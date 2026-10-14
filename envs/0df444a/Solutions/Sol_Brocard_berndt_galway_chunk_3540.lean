-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:57:38.012854+00:00
-- url     : https://prove2.me/submissions/06f96486-b4c6-4406-8647-664888ebfcd5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 636510791 ≤ n < 636690647 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 636512041 1250 636510791 636510857
    0xd0608010b030c060d090219060e030a02010e09070309060f06060905060310030f11030111070b180319090e07020703020306070206060901090c12110307030612080f0c0f0106080d 78
    0x14150404012103507110301401111252075051100c0140c4409030030611a04842041c01001d41c1406030090041c003041c0c02b00f078400e030301a45071200541d03081000c220038940705980782e5003244c1e55604180d01402402400414081c034007807094035a00d2081e8840c0e01a1343e119503403211800d0f5140d007084002e00058510311410302e1103003020000150441e1914141c581b141040c85440c43ca854002401c456060482e170314015800103004d81005050100310798401c50503a400d040714807444011542d207004503000e1881203050800c0340e231100d5028100d403030018012080d0000c0d2628240c54001e440d01030a21040740a8440c680c041580300d4000301d40d0ba4403561000e007181e00280e01cbc00c3d00c10b41c06801030407004020f21588182c0c07115031060710300070711100d83c1d0501452680c0f0300b00844024121003195108405003141e002c0c90350000ba00307090441d0780e42c00540d0703201512030481d1442581401e02e00c0c0188820340d803802c82c000480c0d4001250011401d010707a12010300d8441e800e6080c4440015080c0c0360b85c20 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 636513291 1250 636512041 636512053
    0x1090c090b010f030614061e0408071d040c090e010905060103050d020d05270a120b041b0305120d06080601031b06030b0f0108040303110c0303010305120a08160210060b0d0608010b03 80
    0x11410000041d1482100723003c0c0e25400c10101001d044101d0748140c212126a8015050070f01007000c0c4800c12404000c842c0c41034544514103600c0d00901000329014100038030f615800e425052500035000b0720740c89a0410180c0304c10b540d40f454041c0d0b07100e4030743c045800540a5150390b01c5015005405466500350b0600175580c0c0d00c560b400b48440c03c40640b1480541c40b01510b04040b0780c007940c1c214050443c0703105e00180c0160f428941021003003108080c6694004141c6100180b0000c1d001040480702d64032611030080d01c0f54003190b50200500000d030066002807084000000a008141200083d00f05840b54603c1540d601c2e854200e040c0c9044100a40d0000c4140c00d400507203503c0380d030406522600030720300010044000e00208140798441e42920305243d102000500500c4024411030120710202a00d840c94a85080005411500e00403d04075003044d001e051585100d00a005a216107400c100d400c1100030380381e6403050310070b420040006030001c0c0380400104070000144940031101314002c0c000c0c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 636514541 1250 636513291 636513329
    0x907031811060d060602010207110307050310020c0a050d05071103010b09270f010902091e010e132f01020708030f090604153c05030901090c090b010f0306 68
    0x114054014150741084040294443d900c006205200203040164005645c440c00c0c0c1c05c1034480030b960750a40d584240c2000b0020012a80c1c0042c080050000c2035802503100e00c021510765050080442000d4181c1c0500102010a2948107004018803840340810300d20300344039407081c50301f01e4245020068108030524080361080c40c103e00c2101d80105101c80d403c1c013a4841461603800c10884103400b01c020b80d1281c1c5c00004626140c588030343e000c0c1081c00d0002c2415a0824010300001c418070645105002000114001580c50f42c0d0344444241c00030740300e1001c0480615008813107000011100032075044d08405074115032010859800f01d41c800c600850030b00000c014400e00a6000c1c0e42c0040d482101000006601c599540310782090081546844002c01c45070b0000030f003185840c01c2c02c00b00546404008603008085058544641d0f1400d191140c0c8903507584c160b40c6d0040400640181080c0c07546e0300e001032200d10700d822018001c60701f80c0e24040d941001c94801d905813030690146081c3e88000040c440c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 636515791 1250 636514541 636514553
    0x20a090e1e0f0a0207020406031511161101090b031f0e070e010e03070e2409091506040617010c120b1c082b0605010c120c080d11070209070318 63
    0x55003240c038103c8010b1030b02a181d400501160255442143e4115130604034200c20308141c40752100c078102c0d03d90761030b00c0c000e0b1029200c518849810350080c50747c6030142c1002c45a034440d02406010300084103420f50b4a040240e507070069050444503d500c01c40440c4004145000c6a5129500400305600c5200070f41c00c44400640305274040741c030110341611811500040c642c003031202a6004c0c40d50780c40300304c5078803050702102c840c0c0c02c005880b924060480c81f402e22880840025440e041c0d00c003018000e04040e01d507140014054803440d800040013603080b240c40d107001101035002c14282892a200d811001d8205201501610300d003901701c940c002840c1240368403450b11440c680160a115100c1149031040201e12580c0c056002d414200180007805a100c1c0700a615228000c050300d02402c0c0030b42c96141c155124107a081c0010030090820030ba40c400360041241a07025111b400b000d9240038442071b00004940c440700d070400842607100d03a6090010a000c2ca01030710406000041d020080c4180a105480f28 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 636517041 1250 636515791 636515821
    0xf070506190332060f0307180f110307110c090126030403062a08011520010e03070302071a071e060c0c021906120915020a090e1e 57
    0x1000c043c258001950b000403003607407140d50008040c101429103a04003001400f210303c21011140d406584241400d10450108040d088410003030f00c038000c100e0f9001100184054800342c19150308401010040c401019003008413107004d80c4040341119840d004540421813859020f2040b0701c0242140c0c1c41d41508a524124110400085c41048900d09075407940c80c502269501103260020b0010021040944090462a4451030101b850000307403950600c8211107041e903050043c501404151200c02940c9407010441080c41c14050008114868400c1411512644002011801800344a90119010303a00348010302103890011840f0f400d2044680c0e5428908580401100050803140700020000c0c003103000d86480c042d180d6503418072410700c910501103c091119030240c1c0b081c0000c0018405158020350a98100c80c0d104400b00e108105130800c0c002ca101c0702100a00380d0380c0002a500d02454101003000d04881e01181000520f82c0c0d24244903a040c13800500304100108030038041a82d442c021108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 636518291 1250 636517041 636517061
    0x1106070801061d130605030708030a0f080a1b120606051809040f081303110402030618060f0315090f0d0503060603041e05070608060a0e04141e0f0705061903 69
    0x2800c02c4448040001004c4040f043d01381c0c0802921100140051701341400910001c2904100450401000d000d0162803485410030300010441c0820014a210301070782c01c2a407002200c25604000c00340c8500008000c0200e50205901d460b052030700010700c03540b194007168911600c007010340034016110000c224003418054000e5450561403250340002c6010003005060425121403910903051943c40c0840910100210940c03049106200304070340c40c0c4039114044184249054144d84a95030007001402603510703981445d8043c441e500d414203c00b050a8000c80c081d9400c9d404503030742031460701042c070303954182034840c0400070307005101003002c90501c00090740c0c00910410300100756550401c032058036203103401b006950725030000038204084c68021070303081e0f0048001e4802c5080e003804c2071030128103090080c00050000341e0007101c00982d00e406003c4165403400c1c3d0b1070908a81c611402040f680e403000c44000360f00d42e0140742070001b0303945855000c0310384002d0b141c9000030001c90040801d600822260300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 636519541 1250 636518291 636518327
    0xa060212220b0c0d030506040207030819020f0705031b03130b1e0a0305040b0c09030c150c03070507030b010b1207051b0f031809010b0f0a0201090b010f06110607080106 74
    0x35010403541d0b40103000e0809140804010320951040220040640b00041e01c00740c0124410005a008241d200100c0390f40041140c030201200301284041c01c0007849051080448000040368403000c1100100c003c09e0500c00c410601c00183c01200d0700306440c2d2081c3d142e05880040c440801f0000c000c10f000c007610b002e845002090401400041d507051407540a001240002596030301004100481d5010050300061085802810400040b0129a54900d080a4039100b0215410350080b0101108101d03007003040e10340700352600c8003494a4255920010343c0402c680300070f02e00d000440e1000c0d00e4815205060046907a80b4501e40b203140050f40c50790300444502d100c0068405c07030b168041e1800c10814600082c45002035644804450301e889015420b0100d41d0b01c01d142c2400100300065040064450b0800e810b01442e40d5500c0d114016070043c0030803a0001d00740d82100c0000a01c00900f001070004483c015252403040c1d4503044405520b58038212980c5011844200041c0403d0b07100302078000c0c030000168 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 636520791 1250 636519541 636519607
    0x612050f3c070f0206070c02030c04020c03040f030f032007050d020325051903110402090a08060405070e0705120114030a060204141207080c06070c12110a060212 71
    0x50341c28941c40300c04880c0e44001c50859403070f110a8990401040340e120b8618500001c421000b640041d460704020a0490710503074002c20f10315054042070080741c00800c100314a040081e40da0f450300940c150000c1c02d054006c035030040580c40e410020030305203c01d5452020040c0c003080341428104005900403013070a070380501c5100d0810031080b901c014005452400000420a01440e2408000302c2041c040392004511411900c00c10004040840700b0395400c008a4000d40c41303940200c040b503082c1006138010f05d024803940d8288030603c00c022800b01c007900c415000400069541c3c04040e01c4603c0703408000c030307460901c1c00c00401400e0b400c10343d4624103401c001c082c0c440c610415191401a0382003070304020a040d1540d4044c400b80d2800c008084604510100a07040c00d0345000031043d1582c4915a06070701440e80001c1e101d04004202c245040500100b54040c04034048a082000420300f41c000090b024001240021501c140000b0304101d0b030500c2d4035021480d103007025450301405508110b00d01c54002102d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 636522041 1250 636520791 636520891
    0x100e0c07120201090605090c061b0c030a0c06020d05031e0702010b040212010f05010c0b16050d0c08040b010f0b1606021b061006090b04050418020301060612050f 71
    0x204501c0e4800459650002c50840d4450410404032000a010603000d0b0307001d000c1420b43c2c0c2d25084299001d11150005900d10740700700402d610704041c51001119414000d4440705d40800c030284503d00c05480059003105c480d03000840381502c0070701c0103441d1000d5124014000521460890780362036031244031480041004d01031000414240d81007018400306624406c001408000d60300711001c40185000d1074070201445580d12000c42c0004094580003150180d03500846a960007074040b207112080b00d20003000340e0000308100400c003002c1034074101e0301164030030300000d10b103c01c0f0f1101d0400c4c0d44103a001240791904201042404408070402154816000d0003201d502c1d089101c0c0c505080e070103040251800b80b8104140002c440800d8004a0900c41c0071743d000c1c020204603100380c40a40d0425580041c40301e21200c0b248641e5a81903800940c95800c0c80304c0807402a030b1046400d51601440f090a00c82c6803180341c4520202c80003100c50301e00c0307070240c20701c4859802521008941d109034003441c50510f0301d000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 636523291 1250 636522041 636522053
    0x506060d09060b2d0303070201080f070c0b15030d0e06180f03060f1b0403050d0e010c050d02010f0c02033a1109090703090c03290109150e100e0c07 65
    0x1000b00e60103800448113200c030311a036591030b1000c21004030091031501d4007582c0060044400035111203014030303108002440f02400ba001c0c42c90001e412406009151a081e00782c421f42c40c0305c084109000340100c00090440c1405003180b4143c0781e000911150400703218500d244462101c0661043e03000c408140c44030003d860502105004103101d94040c000c40c54070039903000710000e400c91010760399001004104040380001c01d90644121643c54840312030302d82c0d0b000407100e403c240003014009014403084c2c03e0820360154080c1d0683c0b010b0210a100c90090f41b00141c2e00c90103200c024001c14240254800010107000e550b61401c3e01907442541040c6203248295412a00740340307003c1d605900002a0458a441c001005551080305071400384860343c2140d46007003840e1070301d21000300001c03400a00c00070200c004d41c0416034000f0304040088215a034500100c8080c0c0f0030484584541d105000c2c000c1688000030480ca44900c0c03070101003480b0325140ca550341b05508030050400e11108800c6c068280001c81c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 636524541 1250 636523291 636523309
    0x50d0b010e07051e031608010f0605090d021801050a06050a02120d020f041d010504090f0b15100933110313270c17060a0b03041a01090506060d09060b 66
    0x280300c0ca245e859203021014242c0c00d4a2806051013030000d0440104800f10000c4c4484c0140e40c0e030761520341c0c1c454500402140220128400095002c46007014800d00001e000407043e0490310304071801124965103034005c1d2800d01c20350310301e900145c014a02c0d0300c0e040c50940005095034140020010b18100d00711407484483d030003d80204e904600610070402c2d180314800541405000100c03010007a100180c2d6480055040d03405004221200c0d02c40014045c0c040c4010305c0c100680c002d40031210038585a080280002c1060240c2421000d5200d80c0321810a111300c400e84841000032004c002c44031110006130f5007400100401c01c82071008003d882100c442e07145182004000008101040139829403852800d541003a0240d4180792403c046400550760200603000c090900e502c41c01070030344170f5401241c040c5810b900000a0000000140010000c2000800f499001c0a0000c81c620f642c03110415425540291013999104005101c801000c000680c01064058810600014204411008a41c00036 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 636525791 1250 636524541 636524587
    0x40308030403050d0b0315150d1e2306060d050a0615060f0c24110c06090714030d0518031b040e150406050603030c12030709050d0b010e0705 62
    0x40012131840c440c440280100e0030b6210048015101c0141c81e0041d007100c00200403c00c40c031709066560b10110765100c02c5170b0406029003000c00b24040d2500c0034000c00d04031644c03000c1114010305800d000004800c0700702882021054010241c01e032034890780108840c8406c200c9040d1032502034903010400040d11031280b00c02d10031040300194603007460080c003e0064180c0c040602c1c00c1c4582100904009441e0914210380b00080c800f450445007081c001031070041c01c40258808220030001641d14804200083d414803e000c108104c82509444c0c501d03201d02e40c15039060040e0942d01100100d00e5182c024000380c194490641034105c8080f001ea00000d1900b4400704200288040801e40740c100c03400d0500500160010f100d0041071308907104500440d10707040040014010a654002150030783d5424011941e0070321030b000859105800112107481a07070b2041d03841d240811000e180c0060301e0b040100c210420355822038121b81140e80390128208451500406c03c0081240401001030041d6024000e00801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 636527041 1250 636525791 636525797
    0x115060c0f030f1808011d0607270905010e06041b020d051602030d0c0201080c12060f06040b04030803160801060813050f1e010509010513030309060b040e010b04051803040317040308030403 83
    0x80c0c0854417121000b02100d403007041c8d04541c1c20000d1664210074510103e510300201c024590111104401d0023890360740003614168240301c0001010490b00a0042c00360b54200c408206408030f0a42218002170710580040240e006051000344441c0140042c0103400705000d03411034000704c0c503070010b403d01c3c0c03440f42d185c00490441c3d110b440955034010f003007039440083d441e202480e00c00d49502c410f2100c000205620300c0751544003400e800030745848058070300508020000a403501d444e46400e191b01d03001100c1020b01e08020b01c4014040320300ca6401d9034100c8000703454000c216201e1002c180801058000305807038034454016202c02c60b800420404040301c06000c5210031110000364a2425a040900701d00b00036810601800410701c03000c42034041259040c2400580380c0c400b480c100000d0084084060390003031418180400b1484190488801003004407020461076030f0700c807080d0704250442c1000d00a143d100b03110500004620709004420740c989600300c982440e643c0e80d2000741e582c2c002c813021000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 636528291 1250 636527041 636527051
    0x609210203070515150d02192705040201050f030406110d020d0608010605090c1c020304120e0a03030909110c0f010e1c021b1c03020115060c0f030f180801 68
    0x248001404008100710410f41c04204e1030801c003c1600d0059102e0000c503106082e1003200a04640e2980d180c1b134481600d041d01c1c1c0c186156102c200102540b4600c001a00c0c0000401000c0140241480380c1d41c8542d40c140c682900380081c640180c01c480c1c100400c200c841642e079005014096070310030082c1004444000004d80d80d40c240800752030580e1915031102801340e0410406120550700c14510550058661550545a200d0b4070b005404040403107040f05e000b244000244001c3c05841c2030242a190a00d454008802035090300b80000a06a484080d0004e51410b1007484401d81c180c021884015196071514182052400790f2410840780780d03500c40d4160342d01d241c4004111000d101d0032602d1006441c401c0a60401034070065111843c172011548403080f155008625940d469040c2095840045410000042e10b490041c0c001d012080304c03411815000c14001450501c1407034040e84580d442894140e641c483c5980956039010454030040030301086861505a0100400314000201812400860 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 636529541 1250 636528291 636528293
    0x5070302120c03100e15041524030e0607020a080c01060503060a090c1203050d0b040e1005010311040903050d020705011d1b0d0b15010e040204030510110a0c060921020307 75
    0x2004d03040d50209800540060401201c0d0103c40410020f1110568001c10213804c034036100300484115412600e5102c200d0b680c0600410310900b207070b00046203da102080f121503c43d80780c950718102100c06400582c842d10143c40041e102c01d000d411840318150001c210342d03880e02c001a050060494a20582d40d5540c1000001d000003448054018041104004001d56103174a004049200308540140c000b92140c01d011150b80310f6900040590000750141d070145050580c40300082c100038070080d10b22800002c20402a4031301841307296052549610b880b0314000c0483d4403071002e500460004e13a110755171460140005128842c14002e0314003841c002d0300e0182c4403442e1180415102c002c0117800745051008890010304000e00b1290469851019145400550f1004803895049420f03070a8029001242c00400c10100051030040c510380c42d90240b1900b80c4058020400d4028403080c5000101000c0400c40071520b244e10601c03d480c01501c4038020304403480076a47c1c6a00b12011400011307400010740384 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 636530791 1250 636529541 636529561
    0xf15110913020c030a05070515010915080105070c02041a0603100f0608010b09060706061a0a031a060304120e03190b0a0b060307051b0609070e09010203010f0905070302120c03 77
    0x214281c03140c0404608042054100a540303000742030000e410710400103032440a00c101003007104ca111140c1c102c2e80c1d98540e158001d200140c482c20355082425009400f01141030032040c05881d21582050340d480301c66000703507020040a80302c0700d1414100c00320140070354619a2075103001948140c490070240c0c422107140451614410a40754089410408041e0061114408580c03c07140410000c5400ca9200c1d15503003419001440540d00150041e40651401a041340d5030030003414000070b0b907480411011201d0a50001140446950300c1e038400f8007080060002903140e10000140079140c039080a10800c0d031804030f03144c903581c1c1e22409030120851140740100314194003545d51080d0019070500c0207102c1c04c8082059400b0203414607045c031201240451841d5010600c40d645400c624040b42c4175401c04105468984d601c9018215030701d5090800198600c1741402128100e4a0b038a01c07120003d845e020941008120203041c04040603020000c030480000080c01c030b03601541091090b1039603810201480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 636532041 1250 636530791 636530809
    0x9060f101101090804170c010c240c08060a080a0b2205100207060e030c12031b070f05060c070c05010f0504080a030215070c030e1c0c06020105090610080a0f151109 72
    0x20602c91f80301d900382d2441641c0c480c040e0340209034000403c80d0032814400541c0241c0c549000300e250024940000c2041e41c5900c01d44080c001d090560300d51140f40d4880741f50300c0c2c4032041078a002c0e000003014808a4903c003040d040c0000e40640b2a038200c80c40d06e803507527145800c00c404c0e2094107000c9a0045510750500002e4842d450055900030f00540ca004026054180c441a0161081d4039103040440003400725489450300b00c1c4e0303102c25624a2a501d00c1c180c6008940312035582000d85c0c05101b09400503074102d902404071419584c010007000c0e03149140c43d00448030079040090f0b01c0304001050000207400365003007180309402c4d4800d0f00030b404c101d0410366102419502c020b2246082004998a0001003500000e1900ea603101c1659000032805c002c13500c0303107414030140000030820a0b00000c00a0008d5066004500505290701540c2054465003400311041e0400d00030410180c000c0307a075803070020f03003c00c1c86400d0741803180d6a82c1007601d0040038544211540d4048a584400300010210444d00d000910 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 636533291 1250 636532041 636532079
    0x50f060726250f0b04050c060c100c03050c04030b100302040903121a0d060506040e15070206060607080a0309050a020301050a0c09050312092b031d09060f101101090804 74
    0x2480781c08500300d072283c0c200c02000c148060400307203049021800303124007800051340c4c0120251440d90b5075000c0c1009280d86030b01465800503182d20707191012940901c00d024460060142050b014109400c40d1503043c91054080e00350501e0080031100000143c607640600c900f41e074000e40328a085d6005408980d01a01e800c5a55504903030386c550305031401c9a40321020722a805070800d200084540c0c4080200d0014003003942030308224840c50940c0036511084036010781c42224582d00343c0f64103454410a00c02da0740034403240102060024403074911020702c29070204250500907800c0b14100207040c1c012170b0850b0012342da050002a03ca10442000a401902c21002401c2c10f800030440249000444030150045103103103441640e0800f0328601c01d01c0d91181400c3c2036004403003e40403011007803801a0041c040300a500000801740280554146850a1110300c1080050204860740f030440341000b29000d0801c9a14061140e480b0703040c905d0f01400d1290150051041d5003c50340d450900c540e0848108038104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 636534541 1250 636533291 636533347
    0xc061e030b06030a02070c030c080115090e070b030406090c080c0301060e0f13080d1415010509180c0708030f01061418090601030e0105090a0c0807050f060726 70
    0x1001400c03070340b0380c038040f264080742070391005803601c005151604036514141d0000d42040e03200b1030b0109041c8819800006c9038042c3c0a440c0c074070140d4481050041d00d002c600715000940040c82c080115081e01d6005583c814400c54000036664103650750300d030310b02c0603035089507000d94090104131400c0e003024072850015088481c1c0b4440b0914181c4080302072402c004144d0808080d0350300a800402c0b21100a0b1155040141c0060045140c0b007884420107000454010000018044248256502950842c0c2c0148030140944102200030600c40884407406415000c0f840020000c482c00f10300307030390041c0d4052084010084180c3d4034011004199910007401c0c4990345004028075165110310105a4407251020388040c89140d0359000160000e0a000e4000030055081008112a40d40702090900ea8644070b0001d03080c415031106d04950b07550f00640281138002c3c6032a80403006d2407901d80060081c0314480c04111605100882c2c80c0813825035100013108c8d016074080342c4942141d42018000250300a004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 636535791 1250 636534541 636534551
    0x100e0705150c0309060f0703080c0301030803042d060609050109060b0a030915050112020306071814040605061317011811010c0c12301101090c061e03 66
    0xc0005510140281c0c0025030040e400075194081041c00d00a541045400030040e60315011441c048020550001d4000c0700003a502600041c0c0303030b100c4d801c144c030f0580b80c000a9041c00c660380d84e0383d00d0489440690025000c001d02d890960a0f042c0c03c4404058013a200703c602080c160703d030040e010103441c0180c000a12660400303005110070b1802c030043e2101d40140d8a0081100c050500380f020380b14090313240d401c81103410680041101c0b0101c2802031030079842607085420380d50390403408880080c420310000c650300c041604100210314502c4a2009480c400910002d403055031840018010781c07207203500d5540440c1c2e401c001c0100c041200c0b42d941c2004880c000034085182d450794104242542c081c001088410395800c018140d0744600904502158042c0c2d0204c449519640510703899506c0042c03c85114180100300c0f1b202980c0c2c070b1140081d0717654000045d2414411980d00341d8084446c403000141d50343d41d503000d400110348400341c10401032030540c5500c10348141603200315040d040e0001c43d401c2458206 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 636537041 1250 636535791 636535799
    0xb0a050411060a09050613030b0711060a0c02340609080309011d19142416120306050406090c020c040e2d0601080604030c02041a030f100e07 62
    0x20407080388a038202116603a5036022515030070344d41440c4a4100c2e070380041740400c511458480302207036541035070301174001458196108042103a180302c84031940341494201c0c001003000d0311903980004144c0c03c018010788008291007410400f140c40a2000900c203941c9030a140c410600f100c80b00280a1f11081c40d2401e5610701306025280d4a100e044140c1d0b040003a00300b507015074000c580d0b035240c10f0020020141035400c580f512041c0b513038052070b0203071320342640c3d580f80c0810842c508030340c0e240c20809207034004c07000c4103076028007485513504200061482000c001c4a0340c800100001070001c0c07401d820f41c500080c2c00e8100000c2c04122011600001c45080c0f0f0960549822a0002400c504044080f600490f0100599140c07a0030450b00ea18070501310f0400082122118000b000410350405084040310190303a40d84111a0351b608003560040d0104e00300850035405410b1540041e8480703484400d00c484203100e00f05c0401c3c9020300320f40c4042450380141400740880e8050b4041c808107014140000c01e805418 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 636538291 1250 636537041 636537053
    0x1f06020d0906050f040305010c02010923151302102a03051b010e0d022103040b0c09041515090f050303091915050706050606030408160302070302060c0a0b0a0504 71
    0x154025070b0203102d00413620400084884049038081e541c840000d0044407206000a400781840600881e101101444c03200e0045030411810060112090001c0140310100d000140c2d002d5800780c8010f5255895078140170240e11165034403006c1800c19502e5801c0701002c02407400c4582c04400703420411510340c012400100b90302005585103117014194804840c291100f19900501146c10041814011003400c070445640120744602440a02400c0080f508041060743c0310341d1001703c5000340f0585543e404601500344000140c1441d003806000042ca00250541d0b182c000708042c0c1c00403085039800700303408805507400100d040090108542d8001030909102c006a02ca0140e00941c0d070207200c0c0f41d2501c4032100c00700031707c0400070200b00940e0444000a104010220340c0544000d0300c020f130070040480daa9007072003800c50348110b401210040c200b04a0856010000d16144d2090f1304512422801002503a21607000307102c0c42c03021600410701002c543c5450121240014000d101191a080420002c604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 636539541 1250 636538291 636538307
    0x90601050703110c0a0609090b0a050d03122318060403090b1c060b0702030d0f0903060911131d160506070c09060605072001120c0909051f06020d 64
    0x40c0c10b0800b607401070f010103c0c2c00d00d84401d11019550020707001e100043c4250b0002d0942054444401060141640700c10a2140d404107070b10686400013510604080424820f81e05070a8480034104c0100c1c092034121803c2d03185a031a0040c5100d181c0d130f15002e0192212030301c6654648911600054a11480c0a8602801c05046840b0b0b0058090001400070a0410a00c00000d4443c1081e101044031580794104202207420411040340240304000d09100098003d03000c5289810103036680e80212811559000c02400900380100e07020340c0c0c03c000014465a8401c0007001c2e0402010f03002507451004481c22842c0c2035030882e4031407190000c804054070311001070080015a8403e0724010356418191403e24601d030481e0340701c0b82c5003901d40070010804a5000d0000d0042c14011100c1203620841c130782001c80c0303004017000b00c035020511344091800e44a1003600090704aa0700d0f4100a41907580d2030b400041940c1c8211400341010910345011841101c50b0400440034200303a1004020458a1001c041c250740 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636540791 1250 636539541 636539543
    0xc02030c0114130f0e182805010f0c180501022a030609070302030105011409151302071b08010c050733050a0b10090909050109080304120e0906010507 66
    0x480c41c602510b00d030100d421501c2c9440e901da800c0b00c0300c5584003041d10035200d503800f5031328070708410002040c56903a0300c584117408400d1600c0601014590131355a0b00d0300b50203000c8a02400315016040030003081c03080c418a61800ea0903040400c9031280104010714061003621b4401404082000500603640e0006a8007040c0c4000c642103504610410326447c821410040c4455152150070100618001c0119102c0116403003a80244641d980729010480c1c6110016550b0b90400341c60800140c02c508461715002015802510094204807101042000c0e030780014005c1c0d03031103c1003481d0041500001c40c0b1001c010460312000301f1100c1d5241000801c948980742c1c0c007400c80c414908a02c15001a103400c1100d1641d03949421406007010107075442c024000464004107141d00d03041ca5140c03241422284e00205d60345955a404005041c03410740781c02890411401e8030310790741c0c0e20722440020389008000d600850090301c01c800e5008441800410021002400300d012354140000d10105980104c280d41d001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636542041 1250 636540791 636540797
    0x2040b040302150d0203100e090105010608191b09080c0f0907050c011e0b011701051c050115121e0308040b060609150301050a06260709080f1c0c02030c01 68
    0x110751000c400c204501518500c0840d180c0300000b1f110300a0040c603000021030b014850210300c183e072002012400ca503401d10130100802d186000003018411b1020084e81c02d010211000100c511030b080146808804104040c000720b0f40e04070041c4481001001143c4842c802211251000c415102c0410328048002d05054184080418131015041080d04007401c55031035801114841c03a0404034141c09401562401c5020400c8d658241c4000104c11222606071400540b202400100803480405d400a200b02d007aa595541c81c1d41503440e5803a03410a4070700030303c05001c0301d00c442002c5040038032082a0403000001c0c2c9c518854003800001e504244c0340ca40c0a40c20444400703169a0360710200f8503a01c00c82c000c4076841f0800010700d00a0840fa000a14103035001920b150200907151402500c4600581354150009200c0707541440c1c2c3c00318036074800799000c011032400d036034500d0b564071140d46803421803584101203401100e0340e2800314542c400b16125420300340c5002c098030b001c181c0110b600c0383c2c8440a82c0f410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636543291 1250 636542041 636542059
    0x20f120d0209060f130f090b0f0613210506010e010f06030c03090203010510090e0a080f090a050a060503070810030812060319050f060a090302060106181503150902040b040302 77
    0x7260f90300d03026181010b02c1042d075655a82a50103e01c2440c0c8550700440c01001da01701c00c0414a6030080c429500c09010241001451645180410403140c0082001200c0e0344c0c2e8410001c607c565a401503117040b0302c00d0000c080808119460802d06000058012125400061004001108902c0c120304111a02070a001604c0030340f4a0048003d040070743c130003942540c2050244445035115083c003c08992000c241000704120041400e03440b0310980c003018100c054180410001d104403c0002c00003110010800c500ba142d840010400d962070b680d11010202c1c40200030030903600d421010701d60b44041074074100d0010500319601d41482c2d0082000740600c407500c120015910341c40c100a802c6194649418901c003800d0545012a61000a0350f100e1109005220100d29110440d020342009187d064001c0c1c402a801c0010807a01c404c80e600da240c04200c0640b0000a4002d100b01ca072400d4245076075404221032070683e03540c2600002d2a13006d1046103104101c200b1005101ca002d44040e20350440d07030350305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636544541 1250 636543291 636543307
    0x120c01060b040b090109060509010c020f0d0b090d0e01090609032406080d020f070f031407150509040e0a20060f130510030506130c0203070b0403020607020f120d02 72
    0x4014411034200003140740c1c000802242d90351045003d0200380c03400b641c0340740e9403a480310300403103031401070081f100e02040e02c03040c2d4140140f034030450305007030004040c004050f00b0b84030340c41d503021202096130705007a590000d000041413160710419041c0404003c0c20f080840703601d801300003010300f04903200152420341000890310040f1040c01c040c080d4804401c1040c0305c0b294072090b800da1140000c4d000f1102610074001a850141c3d000300d02c4504440f0703810f55444500e0703e141c488a41d840c0c040c0840c00d10501480002092400e40d0181e5508042280e40d50a51110448020b00c0202c641c2c4115601840d03002c0b0000f180050b00d4102448542311079402d649440c004084003050307680c05060202c01128102280380c021052001010740d04880044400910300100c40d40c066080318400d85100382c11082e080700c4810712071710540104421010b0f42c81240d00c2c01444c0c0d20780901c2e10f00144d5003140141c20210a00c503600c0e604210070320505035108050241001c8030060f5a0040c4541008054450380104d4600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636545791 1250 636544541 636544543
    0x714070b01050909160314070801150312090b040b040e070309110103020a1b0501050a0b010503040519080904090b090601060f1d1801061101051803120408090d0f051e120c 75
    0x20b180e40741408124105c0d038aa281117000035003116500d0f5258030a9200000d000501401031407445110203100942050543e180c0031240506400b60f1000d0251816000425118110040c4000c03d40200c2071a1541e0505c400b01400440142029080604002da044081001c000001207142400d003401640c48180c080185c41c540c1c84402c1d000c4002e0043c54240041c000117402c9a0301c41d800919003004039241810041d90300d40002d80d0302901c9648030090b00d1a1130914144c800861038040c00740c0d02d0529507241c0000b4142e071641001100d4006940b42840b00e004010421140075200e2401c0081e00c2058a407801445415000401c4400e401c03801040c1c0b1090301c44141d090300740d201040726400135603118400a412141340b10b00984845d840c4c00005400300140e4866480b0700c84041001d107180003038a100c01d030001100944103071200c40040012180e1951000240004136100760b110350711000d41410520300f4524100b01c0d1000703030312034014442030a41c408079a04140540009a0b503481d00022042c503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636547041 1250 636545791 636545803
    0x1260604060b04121401150605030c1c0b04060b0a0509060f04080111030405070b03010e0f060112180b062403150a061713120c02030a020312030714070b01050909 71
    0x28a1035982c002004145100a9407610210501030b0980c0f084d031610b413000084c200c403030781c5003d44175200c040702c01403100034400c90040d600f14802249a40c10030301c0380080070081502d01d49034180181d503140300c60383c2107040901a190082800340fa205052445c814006421803180090349803207100e0000d10040030701280e909660103810b204008000c842d0703010b5641ea80031b40c01a0340503a685d20441000051540030301c0101d80c10f0310051510303454a9100c0140300c01701190003400c0b450522103440401800c102c4c0b1813081c4c2d08200c43c403070204480c5c2800c500b020b070902031000e4509402a0b0064150107540f4402c060244844001e0035001d965a40c0c0f11034107031324640c015480560740032118402c0042d0b9258081c109441010300184030007001c1d1103160700041011030044004008803000a01400600d000c1c2007011580c1d8005030507140340c042d0503070000b820402c0541c500c00078684084280207504e0751002c0d070884041d1000c0d511a107003104988600800c000144559032040c074120000420b220001d2280d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636548291 1250 636547041 636547049
    0x7051005010b09193501240b04061e02150405060a0c05030103021e032517032a030d2a0f1b02010c0b0406060e1e060f01050408060106020304140126060406 68
    0x3044401c0c000c2d00c00c04451411f0142d0701e40035800e5082c010900c4509030044070100c4619468031914546910004c0078405050700500c020741c089d40c2c640d140d144021044140c40b071449800079114518001c3c07221b104503000e407880b01c010400144010720047c2c5a455006542e8544403000c032030306040e40c43c006864201543d060486d1105ca2036401d14942c125502c0b10320590307110740e025000140d0303601d0f0600d507a40155650350021035448110031004981904240100f200050305507460f007060040c1800548040c65011008802030b078600c00507030211441c3d0f0007601f0080380782c0082ca41c0f072804c1c4014150216000000e0901e6228031801c0216805502d21800403a403001228080d1710701810200c008281c0b910170070070701809000c0040e60f00000d001c5030104d886030b500781c8a0002d41b80d20040c030104250401d003080c1401000c00c0f0110340080108200343c000c110aa0041d5511401c203441d0400041200c99624107110620000b02903140c0412003d81400001c500d521758103580300c40005016141542c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636549541 1250 636548291 636548293
    0xa05210d020705071e050f100c0609060b06070311010b121b030a060920040e0307030e030f03031305120708030105040209010e1005040f0b090102030f07051005010b091935 75
    0x3d808401042803064460407158221064548500c00c00144003550085020354000620349d1003600d4005401540710714100d6000d5100000c10301e40c1c02010174100c0e806600f00f030340424101040c072000d04009004070901c03541d00f036480a0b006421000c4040e50b8031120260004a0b040340c40401e582c83d1000c2142c0341120b03811003014450700d00b090522800070001b0542206114080142c446d129050034040d0210b44c2c030b424401145804070355241103400342411920142d142c080d4000d400e075485003c2000e14021160300381c0d01e4280c84101d1074854901541c410008456007800d0040c8000325080c0e0b015281111800d403070159455518100403a6072004400640343d1041c5051052000264441c0142080d10708070810400440d80740d0b84800828090f0105c56801a401084501a070f46884006400140c1c891000c03109900c1600e40120242c40098002906e401d070f001c1048030306842c02d08826101d04a0200380300039410300b0400040440c1d45242e509001c0510054504c09960080c180203071404841c1030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636550791 1250 636549541 636549569
    0x91b030c2b020c100b030709150e0108060609010e0f040209090c04050709060e04090804410103052202010e190b0301090608071809081603020a05210d02070507 70
    0x1c141c00300290000e110500349881141041c3d0790300303840c03803041400085004000305200ca1404011902502002e160b40c1d2040e46d042a00040c04030407425107a02130004080a03280f2440e02d07905000950070305905c4595a44540c0080c0051083c1d04480c041d0400d8050381c103401c0f00c0e070702c03a041f007803528040241442d04a40b6000070050707103c0c0c1c0014201c007035801a54504101802032000c10068921019000d054581e04000801c10041510180410016007820004ca0700081002c0c0314030b0202004649602d20040103242c200c6503a15119140d48142c0344901c0031186180d04c0004a2001007040c00241070041c5002c014800782d07203c44e241e2448024080c5038915458071190102120740081c80b82e10100e500b00b840c007182d00100480d0810545410100340c0851000b000002d0300540f0709150240c5004604000c84032010b60003040300d8165074020f8000b00300505142c80d00b50b1074040100d080040d402001d40c905522465102d0032108110f051400150b210602414400c0c240301180d44030a288a11030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636552041 1250 636550791 636550867
    0x9040513080306271303030612030210051302030307060506030705010801150804061b0c1101021507032004092405010909110c0d02060f01080102091f0923091b030c 72
    0x40f820041041e8481d47d41849010b030340754400114040000740041c0541c11030f00c09641d60a0a6500c40d0390b0009101000030f03100c0240380c010034190b51140f1030984810780c881042041d503040810000340102001e00c1c15154940c90103610710707030340c04003035841804011003d4040307400c3c8102a0405141604000011040ca020310f0b10050095103081e6030031a50b842880c3d5100c103056002280390400c4480110001010395281039040340105240c80081341c1c3c101b0301c124111404100100078001801542e040081c02880001e400f00c0545814882c21141c0d5030024024045643d00000000c02c03141103d1012884038103000002030785000c8c448503454140708a00c0314010303280e130004900e0701880e4841049400b50762681541c900b0f0780305202d250754202000742e01042e1400654103000f100b1002620700012010780343d01051700702d05420080000744400348214044180b50030050701d40c201800584100079040e0b004101c00f080c3c00000c191280c25500462190310216000303501c130028100c440c10081c062058 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636553291 1250 636552041 636552061
    0xe120309030106090509060f090304090c0504090f09170f0d020703030b090a06051e03032101260a03050306060f0f03190b01020a0b07030608010f020904051308030627 73
    0x2204440c148250309020300000e49032094403a050048540c00c1c05041c1594a14a403600440301c0074060140714403040100041041145c816244800031300d07610325640d42e01d000707121001e0350400b0401440c081d141620302030009184102e241d52103421301e07541c940c95803410715040030742e80030301c0701e0020318540005942c83c105649175000b5504000111703040c0c0f4140e00c031201e04104489003070013900d4015078050441000401641b10585d055400141282c0c60301500807554280126006030250501000c032006010040c59813910184000c0c11001806210529032031565890f603138204007506102e000400b0440da40c5034502256a12a994224155540d0301004200e52542c002c4401c0442c812403404410f0008089000b07070480004160700400d14044030380c80744259080090229414503660ba000002e80c04c0d020300a100440400c4100140c0742c500500c01d21080c2c0710024010540c402c1c9140c0003c00041800c02a0ba400031b0707003500c102c4120652074401c47d03460f05411000c8224641050200207204803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636554541 1250 636553291 636553297
    0xc010e0303070206010608040b040f060902040f090b0105060a0912020409050708151303020d080603010e0a030801150f0207182007050708031602010309050c1503010617070507060b010e1203 83
    0x4055007240d40c4c036a40e80c85c0407545100241c8000740715003010341c041008200071015200c0c07201d00400001606240740c0e40081c049411025020901c0740d201e0800405002f02806854010141940d1581c5065440d0380e00420104045c05030401482910b404c01043d0f40703959001c1d0424a500204456045803108103269651641c1c101420704c50915900046940d9007030384507281090780c1074000b400144c0704c126050b200d0841c014001905590384800180e03100c030b01002284a11802615004600e50400b41d171011000c0c2401c1000c0300b40040c100c0c000c00c0380d07a4009000d031304950000c66030100300d0701030f0b40c41c120180140322101c1000804000c0c40c04051141c40c3c0041031094811003c54902c41d56402c0f5490f2207000300a141d03618003a1804401c0055406a004002818801e10603510540e5814002501c0308070f9020a00b90440e01c04401032004a0308203014103444209d403446e0f100c2503e07141e0301c001c11510a0b80e01c01092507440c0d9160740c6250b405a10845070040000b0808610062a11149642c84d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636555791 1250 636554541 636554551
    0x40e07051504210b01180902060d02091c0203120703120510140f1011010e15070909090f02010f030f0501150f051815070501050c040306050c0c1506060c010e0303 71
    0x219102c10f181c030700092101c461420300c0d40d000c01e400c0100d07840c024035100c9402084440110040c1c450201400503030320a4002c04a4520070721005841e05810014400005000c2e4a510100b8441c0400030000d81d4001808a030854005d01109648956615046841140c09192040301a0074041401503d900b43c480b00c0040e0f40301062103401d203e01160030401c0d15001c54980a412619034440414030078400c41b00414652040340c004124421001c45c814500074000080302805c800b07400a07c071005600c000b05c0c0c00103100620042c408070340103844021a000581707900034140181c1a810305210341c0641c00903018074007240c3c001c200e55a5500503e084c00c283c0044402d00140c03c58040c02d40309405901620780b1000c80d01e0040300c8151020f0180901154144003015210006200040c00904c007409610303c103908a4202c0c0d6103c900d140b4010064031400b80c028409000280300c81150084009170015111805d029800381d15151217010448921078203c24422550030300841c03110000c00000214000c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636557041 1250 636555791 636555809
    0x5010515090609040c061112160b090a051005040c030605070c3302070219060e040c0f022d0a0302010515010306030203100e0102210f01060e030c040e07051504 70
    0x82d55070541000300005048900402e580d020300e609102592040c000700c4180135006040b51250801c8514001d42d5410200c0007407001c0c2c1c0c028a80008205000303e03255081242d40340280340311403442e52625218010313a602e0800c0240d4410000f0107001d2080d081074015900200300700500c2c10500300040c50385030001000d6826200807040a00c0e2050b48044000704407401c620000610421482d8410180d0702000050340d00c4a8114148107224100c000c0070001492192100c80e00d0140300b01c1400240c4801d045094244604a6103c600c241c0e00452001500540c0e841d01081c100e80c40e203100c40c1d840c0b050b408004a0340c45035a030314108160701507000300e0082c5c000415055040a10788011010340b01c19000081d016008203030b0500f80e031006900320f0701d4002c2c68600003500345203400c1208540c04030a0306c07040201c250000103211700100541d20013405030503140341001045a0580110780d903500465142801117581e40e007200140074052000c0c60180c0b60050940140005049401c03180360480d00500c018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636558291 1250 636557041 636557059
    0xc031112090d0509030a150609020f18010201061d13080a0314090705060f030727170625030f050a02191110021c06080f240609060d05010515 62
    0x409030044082c0d03944c1010041c02032804c40c01c2581c840000c1541c048002c0e80345c54803041c011074400c0540c001340851500307a5441d9a00d42d815083d040c2c0c05c1c0401212501d066901d0142d040c002c00c403a01021509910000d901c0d0011911400c80581e46c40d0703010720002d001d42102003804450f00703900d40c20002c411740c44c09c00700c210390351504510991900c009101e510303071025040000c0e000c0d19110f6005940c1c0207a0f2030504042d112515042c240e0380e100b509a08000f5801c610600384000e8001c282088509584c280080840d45814080783c425100088904c02294450726504a060345c400d40040d01d030302c4c132003880c2480030b804c0020082d00039420400c008900380307401c0c100f0054540c1c8a0081c000c0100c00220050a60b280c2d5a5402c1000790b00803400065052140700461480c2c5c1350b540600c01c0141070000c01030070078100c01e68242d41010440c0c215486154041504950825910401d81d42c10600807a1944000e4075440e002401c032000341c6e00b0007001e40d4280f0003046681e03c1001411074010038180e070b1000d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636559541 1250 636558291 636558313
    0x109061409130201200705090108010c020601050f0415120c060c0519030309050a121e0509120102041205030301050301050c09181f1e1e090c03111209 66
    0x2100c2a00c0014041e00206898002482e400518010034a15801070500c0c8003244c00c0c5841c490803088090084040d2540119000c00c0305040040d00f1a00400021000300041101808020740b515810301c0364030300c900e484c1d064028456031242c0c800e40c40032458510447d00c00c1d0755404c41c204020340c2c01e40150307030030300c2c0342100003440f54014400780d840541e1100260440c965000c180e0309540100c140d0139410150b0310210f00001490400000103000d02521100c00c251000c00c400610a070705c041c00b549400240c6074109150190008140c4d5070122044445156003070055294500a018650151812245e018282000c0c08008002141664401c0e40280300a507284000d8900c00d1041380308080e08103c4105681c0410080780d07003841c0c2c02420407560080200700d610b150904021264110015448108030342151280b4812550801001d074001903100401b9213084041c6800c405221701d000b09901e4102443c0100d100380d10000142031031000d101d03101d00d001e0010101c0007008032503030031440c40b079162221 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636560791 1250 636559541 636559559
    0x30a12051306120c05030402130e120409050906101409091002040303090317030f060609010903241401030308040b0c1e0307030b0f0a26010c030e060106030608060105040b01020f0a030305010906 85
    0x38880c64000e080700c49e01030b41404070000103020403507404400780600100e02d001503440d40000c01c001c0c14510310104241c2000581c06061000103021100c0185d802c030420000180841030045418a04481c010038035910303c100181411802d44e41c9450703c3d480040c000c0101900280c5c1c01040da400ba8186044d00c2d0110400442e061100792050224002800000f4a051a0008c01454000010314046d900d0541e296901c452003010902107615004e256030361415000a648106c460300c440c40c220b04000d0354550349014202c088090300103042800d40c600000c1c00710b400705007212060801d45a200c81906140c003280c80c2c2642041d075501c00040d04007140c8072210701d00002d1048181d88000d084060203447d0100c0308514208903140f20405203003100b5450381440003842070305400029900d001c10044041c21a240c00e01c0d02c16040a0103241c40c7c404280074407040054201d065450990300042c02000303d46c0103034a89441d481d840840c42c49246a0942090303890780006041725000102404a50f440d00020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636562041 1250 636560791 636560797
    0xb10050603060424060504150302040506161e0c0e130c050103021c020d06030501140f0a050606040e1005040b120615010908030a030623030a12051306120c05 69
    0x4580c044000d00106003180f0b882d602c80340100224281a1001c20f0480302c5100021200d50711540c0400e00200e41080808915000d030746003810249000c5181504040004007503005510341001c40b81d80040110f030400040204042034046440408825401689085108120b0b5409030744068520540800c4608250003038401d0910b5108440c48029418031300110000d400c45403a056041099100e641c801e503045200515503111103410120b0f5960440c1841800e4a089140540c806505d030010041d094014000f06504544000804146c0780c0319540040c990b0301417a0094402e11a0351410306c940c1c0c41600060204444007620f043c44a9800c02041002c0400e0038500055140c02410014035100503107146103105080505200d0302c0780307458024251842e00300050540100e5603915081c844590080c2c00044070000241d070f000303990410701012039100e50080000a0100f0800604800d0050140080e42c410100a41088240541e103040003061080f0b8040c40c12080303460110100c46c9a8030075021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636563291 1250 636562041 636562049
    0x13050f0322122a0b070501061208030f04020d080a1101140c070b0603120c031e0f0f072d020111060705270a061d030c13090204090c120b10 61
    0x22000b8910040e440e1140480c0400202c040580405044402400b00518441d400382400302d12050301d0b80d13a246002401c40b03090b500700c135407150200c0036043c001401c440116070340103403581070141079a21584042281003000031001025827901184d200316940c0d1110029031100300c40d4000384403c00c00d80c001e9681e003c400b07032040301300700c0c1c0104150b4010989080f045c03604200302030300310307440448030540408081e008403251240b542c200103000e6000040030b440c0310074220701c144002841e10b40d5000560085205030100808440307400300300e00b000e001c0c110205140c40f06286000c0080e015240e00710f00601c0b019031404038041140c081d6240204503001501030f00c00c00079a101d1a15114420300c0d1442c40c003400055068032a503687d120210991102d21007880182115220070070703031a41125545003000e4540d15150700a42c405070b920f126550301d488456401d08009d8000161304412070000c02c000d040f443c1c001030f11008824000090b040990110200040c0c0035107001c02150b02c3d0080483c130250302c5885 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636564541 1250 636563291 636563309
    0x40e040605060d051c090b0a09060f0504050a14030a0b040605100e0c0306010c14030403030e09010821300a0b030708070308030c1c0b100f1713050f0322 67
    0x13540c2d03184e000805e1101e0244089904104d003480b55601e034191721691110402d940003883c0404108841f9410414505104001e414030500302810040410003051681c031400c8184860b04482c0401903d06000103040242c2003010039285141074240303100940415110522041d84a05000900404070743c1c0c114018a542140b02d45140c0700c4c00011030f40f1100042066421460580d43c801c030603a0100000c00c000c5102e900c654404125a038100140741205078480c02e42500700b81c8d01910420b4190306031020a01e5450407641d00d0354214118007200744551100351029050011454440c4c4500804851191070038200911a45800c40c085c1034407603807544110780f034640c8812024030010f51240c01442d40f01b04260b031400c0c00e2202800f40179009120314010722440355560000c0404506202001071000002400c044956007050b00c1c0040c400350a50f2001b140c12942c41d000700d0450707068030202c000c03440c0e001021a080384810040380e6440390b11640c01104200c1c20290140350300c68202d003d01040726150703e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636565791 1250 636564541 636564553
    0x20a08030a150e13060b060412060e100c02101d03030a1a040c030507020708012003130b1014040b0a06030b0a0509161202090901050d0609050102040e040605060d05 72
    0x764410003801d15034403000350006400380080b921031401c0124910640240340002c600036520300700f0108484005504d90f000708410072061181981c0c0c6942c004051303601000020325118011215801d10481112001d083c5042c0f004540c0c845500050201d61700c101d0040400c00079240c107801d00300113400254600c203070350018400610900b0440c0c1c418001401d105081c580e041508a000904403540041000c1c042640c4105112245a041007a6005001e04100820020f00e0244481e00140e20503000d800e808003000002820407066083c40007016644061000d500d4181600184510780d410b00601a80d05540c81903000c1618050040c0e441d00c20002d01050721803414280114090710520f01b1041d0400b0558000091640f103104c06139100741e1110000a07410450400001d00d10b81c05000d25803ca18010310074104680c2c2c4031340540c1e0458201303c1e680f5040302481d15100c00a0301e000440500706510215000403882d800d1720410303115030321501c030400040d43c1c1c101c10440c2403c100c1c0c0b8013901d164006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636567041 1250 636565791 636565801
    0x819020102150709030807081911060a09030c05120c190c090908090306010e090f03130501080403020f0f0616050a0e041d01110c010c0c0b060405040809191401020a0803 74
    0xa040c42d41c00c00101c0c81c00401480e16500c5410091344003490848118000041e075240340000d114944072200b41c2480c0c0180501081d44803103076110340182c2075494665441410703504040c000c1280c100e849500800760345060381396506040280e0099900a107107801420382d0110064004c944c0300c042141d00c0721400f80194100090b070001045288030841d0308580400a9290507502000000e0003841400180c00191601145480c02c21000b0125241c45a105003c840d80c050365030340c8c0800a40c1c00030b18018070303d030b5220705040345890740343c26000007507000310a410420040c0229000f4891492800e201a60185041c002c980510600740712000151484904c20715601d00b03908030b415088c036000a282d110820f604052400c51b00c05242c145038900e000140b401c0400300a01808003410100e040104404000791500850000c0c0200396901c910780e10400a020014444180c45015802402c0480000000344041007010b03900c4c0141d0300046018010102e0039880081c00843c0c0300da0110f4114215112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636568291 1250 636567041 636567073
    0xb03060c0a05161a011a0f160501020f0403050705010f05040339080106210209070c0503250b010807150e0a051512250e03150903040819020102 63
    0x1221100300f030480703029403040100d281c0e0b20f03401e440c1005110036600340d94034240781c802c0e024201600b001c404060501c0098039601300c082c1034491490b0f19070744035502a182454000d00904c900194404c101d10003040c00300500c500081c03a9015030f1002c0e00d444501400b03100c0301703030780d540642e21000340207042d090300122013081d16040b42e040350086140b1500f54101029207425080302c0300c0d0040300e402d07136460104120700e40481802c1d00c6c400c04404224400a031032500816008103000b4418000d2200701c030204030400c0300800c102d0b00c0d0705a10f40441d621101c0b841e80d540380300f41c800c00b00a84166039a02c001207042c00020818004648020399410450701d2103a0f000c0d55418002000d955001c07003036541c00112a01e880d0281040e150800001aa80300320308100c07469910405080c0d00403400b184041b04968121b400035021404082e420319800f101c1c8180d0000f07181c144240703800c0e401e40f1560f4040c85040f900000181040da01408241da030b0300b12011aa5104089860f48040c0c0160310400c5103684c8006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636569541 1250 636568291 636568297
    0xb040303020f06042a0302040c110c04141b1e0414030d08162105090d0e0105040e061f02010b01020c041e0203040c0b0c1b0f0a091508100507030b03060c0a05 69
    0x4070180f000175655580e4002034111080d60850601140c46182c00760255982404040d0b81e00e441240c040100300861080350008041c000e040c50360b01d15560b41c074518800d2600d03050303070081c4c030362407a204001c42202c5075200e05680040c400c000d14400c011003800120328010450840c809655500d5410650356040258111102c4010010900811200da10180750381b0840404c181004e84401040c10300344460700c94a8155401100d000b046914040f108441e80e10004880c100c42d044078124803aa1103010009100d440100030006000c0225046602c101340c040d000544921800d030203444030700c0c10903020300050300e05045501310146514000e041d10b05010740c0c059901300380254070001801c0d80380c45914405611684c2c08101c8c0e40e02c0704000310104190452400c0300060161000321100c0901c2c80890700904850165008607915040f01802c00c0110309000c1c8010080d06007103a8500c109854000010304c016120ba0000030700b401780c10795041c00d00041d46801a400b90102c00d20b000b50000080318190 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636570791 1250 636569541 636569603
    0xc0f08090d030522050d0801080715030b01170a05071b080403060504080702120705131404110f0402041d0903070503070f06110d020d0b0a290708040b040303020f0604 73
    0x5442254011148811350031350b20440c0324000404101003c01c1002c0c1035104140e100400a500989041c44100c13908a01055410410f04010a46200820058680c11351003c2c0103500d0740301000c10800495455004035009d801d43c0d4851019842915030740281050310f0345005001c0700820031007000024416807029074030078000d010603828058540c0c000b8900c282580d00c842d100d54800c010502007490000d0380303d200202e4929080049544c51380304481c4e01c0100400140408101200e0040c00e0b40f80d038607034000d402e84004c00455441d910707041c1141d06c1c50180c250065039009000700103060f0450020807074020070b801100950038807450b555085d00001c03140c2c900301c0e405510740814465191500c0007401d12504404c1c4050b8907128204100310444010f0741c0498031803d07046204020f40f200ba003d48000c50123100c0581030916000328443e59051040003401019540d0010b000500d110f8141c0180068901ca5400d6410401d80200702c1541ca4000b40e4000d041d8403041052041c001310032060190b248 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636572041 1250 636570791 636570811
    0x20c0c10030b0105120a020408031209152e2d080a05070515091e04050906070801060522081f020307120c0219030905030717030d111308010c0f08090d0305 68
    0x8c5610780d0103240c01c64019120014020300c0f00300c244641c4002c18808001c0c083c0746d03070310075024500d00407c0e00720050320020b6a02e51401b2481e03038110354a00150540c1c601070014042940601751011b12540341034480c2d601115001166604041000c600214602c01c1c43c1c1c0c4c10100820703081c0c0c2414100113a07a0782000c03202d280150100007015042d218042e6124060740c030b1b200c1c031082c0c0c00d646105100a03910300404030810340e0049010041104d800034080b60540364a854460384402c100700d0b03c14010442e08820449003288000c0c001000e610000301e40401c940c420301400c21070900c08141500340d000541c0d400012810070b481e0b042c1100d04580c4101e440c1e2066104032403000c8551004601a440300fa04c054001420504090240b81000c004030401400030f00700e85000040c4e43c101a98490041005601c507083e1505c00b010140e500440035035129514866007000010755545c440350080c0703007104180010503a0307000c2c07140150303003d011100e101e0103003a4080c0c0494000d48108400508001b050040c4c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636573291 1250 636572041 636572047
    0x80d0209010c1a0109060e0906070f03091a1605040b0a140d0504061d0c0f040c140a08040c0b0a0c12030204120507170613110310020c0c10030b0105120a02 68
    0x482d60034070241c3d07a0428092041110f03541006141020f80da01a0080400b4007181810311003012000540701d54000400d01d0100c0e000b05070300300220043c080e03109015040d008850b40116048122504850290001c90326001400c0341050044c1d82a0140d40301e940c0d4a91800c4c0001d18030b0902560640c0049070080301098604200c0c42c640408841007a90700342e4002d40d5442c569404403220090400800e0009030050107919000c80000b01c00c03960003100c6138001c03600c50f14642c5c1140e00035990449a1282400069203618088000500d583c10403201601c080444000c00102c0c00a842e08444800d10705545041c120f09541d118600956011a6000101642040005248900c8252181e8654480c1c40503003001c40c5440b1007030f0081129081d110300c0f950803003410f0001c00030400d8610f000241c0d12418094100c00190000703800d010340c8100440070b203070000494004026011030900d007200d10071120540a208040c004508459003403448602080f410066103005107242240e0b5548000e050307402600d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636574541 1250 636573291 636573293
    0x207080d0503062407111e040207050a08041203090501090509060918010c0c0c0906050105120714071a130221010204080a0b010f141e011e02061909080d0209010c 71
    0x240c0284001480311350107001042c0c820801003925000100840e0440c0d24a0a5030104841c1140d80514003000a2142c1da0001e8094200b00d4140800744000c0d8010b01c1154450b036030f0b00360a0140d4102c28004500003144d1031000b00d0550b008509280981d10060601e07011036590006018404001400680703c8090040400c404030700240950002c0442a54800801c00b01501d4403803803000860b04251240f9007004000c0c4030a0368400107a44420600c0041d070300858907503403030545c1c07074440c918501c840d0b142e0001000000c0c4a00502103420b840045100d040c116503905610341000a907408000750f018111000306840e44118041101054444400051400b603613400703114a00320a201040303403450780c201c004110915446030b400c0c008003e03c003c80d00c040f00c044070000c0c1c0d484940380b10003008001020264035051b44500e030041d003080103050f460707401499040b4020f5900c020072540c0c40c100c240b595603001072854817030285031600c0750300400c140d003040000e0340c00201940140c014141001802aa540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636575791 1250 636574541 636574579
    0x150c04050a08012a2c0114040e0c0a050c06010e04020a08010b09070315180e0c030604050d05071703040c0e060d0b010302091803070308071d01050a0c03110f030909070207080d050306 80
    0x1408040b10314040c90b03a91180040050811f620140445c1107500040c001044050b41d074811a0b41c0c8800c080380d00603134410030118151181d00030140f07400014411500046071003d412220f15000b140221441000155255000c1d400e0320f40b1a5079854108102d0804512254040e810540c0c01210403105455074644884004000b844101240d0b0300a80d140c107107220200708207110181660005401400c040e250a8581ca40d8815040e031041040000011f4090284059204c000c0e4140b080c619450307a4908080c1881d2800d450710f40101c0c2c0303903004040c3c081402c502d0460081c8070b40c1e540c03101030071109a2843d000c0010241000f020003841e14001c45003490f41c048103000504046203c0d40f140c00380e03400d01460082ca01c14044032880c5c1c40714009074010f542d40e81c21a0594040a40701e2030301200400712860100c4482d13030501c0b9884c100d44969510010386290100150903203050644030040250380d4000c08030703a175070028031810100303800000c40c182006100d14000e66000b10081c081e001c01598a561032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636577041 1250 636575791 636575837
    0xd18091107060b030606060403120504150c03030b0303031b030a02040803030403021b0f2101110d06032a2c0f070e010c080a11150c04050a08012a 64
    0x140a900d240081c020041090030300c00d610300241d00703030010280b03454202c01094032480340780005020940c50000300304080b0720070401c40d070241821208008071100185406850749284c540102d010078108100c410003420000283c4e0310032a12171400840060b844000c100c2c0caa0300192400350150b408006c04100500108011801075200380e000340054008150569100103a000a403441400040c603a005180e8400b110001e040c03001454aa010012007041c1600600020343d0203c86690301007114190695154060011a4010106c0041c82d19142c6d50401c20001e0110441d00b50482c076240038000e00a410400410003006440c6d000004400010500012441110903090381060702c020008800c0d802650107003c00740a00304003041108617511341139039005508072501000588100c0b00f1007624100415640034294024000042c14851010301c9140d1040c02121b00030340c201500040c50400511030b0b840700c4280c0710700c0d8060b00428448603e03d020440901c101c10800c114100ea070382010b1114030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636578291 1250 636577041 636577061
    0x9151012032f06090102030c070204021b1204060e0328170c010504060c1b02191205061006090b041214010c0201050a0f06081e031b0102041e080d1809 66
    0x102e000ca880d160000c40ca0020000d00e10300045e4010b00a000c41d240081c01982c00b444e40c1214051785030604146a00044400320704905840d20803441c51036142c050010003002070307030142d03514100d001c103c01040c1030765803241e0300c01440c00d101090740c000340c0500c04800a6020a00c102e9020101c501c05e250360360219003001d0b10b00c8072582d40d984d0a010030020b440c07143c0355400981d41083d00c0f00c2043c061004d4100b40041c24041d00031010a1000310b17640e1909940310010303260b21520104c0c28a01c905140f9070300d05044a20350307960352103084045030b220b004200c0402101c079a41034044c40c2504040f48941c403001c03010340880710a4442c1038440c1401c202801950750f803107196070000aa501d4004458001c1d10308008080c12068a01101440982c0700801d0035403803941c001005034442074030b501e005131543c8206006903050480000c144a0301c1d2206400070821103a0010300c0000c02c0204c1500b0b4030031700c940d5100c0c190042c0e0110034203d1542d07010f40701c60f449942d03000c1811410309a448840303030f080e1410390031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636579541 1250 636578291 636578357
    0x507110a1202070f23220e160b0409020a0519021f051b09150301030c0303090602073b1302150a08010e0a020d060b030915101203 57
    0x5042818150704110320f80040000c15500000d41d8640442c43c05180c290060040410004d02c0d0004183e8481c4110440c82d9910550b50943c0980c02254620042c0b84081501519000c0c0380507840c0074074002104201610070190001345414509400e41c1c1c001c0d03110041321018080c2c00d0042e00000f040e034400100780b4819030303000341200c2070402a00202e400d0080d8002e0010520785030074000301d85400f028229110b0301400807642d450b0b480b04000b41c0400740141a20014010001c004400c00000c06041011170340319440746800c40361120402e0361140c03114000c070308800a41c0c00f01c1d502140c10b0074410380c0340e2110740c480c0400c0101002e200c0c0075101904490300c10303044078a00e00000840c00d00b22440b201441400c07200c2400c0a00075080240a00c00612a03400851509001705d0451000c0350b048540507000043c0030062a66030340818141600200d83c01d148a020303141000c0b50340007800307400c2442481d205065544c420704095008d44600300d12001a81000ba640d1030326401140442207546050500301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636580791 1250 636579541 636579563
    0x106050628030c02120715020c0a0302060702281b060203040f0b0c07060c0c09150e0a05040209190603140303060f12120d0b0621010f0311040507110a 66
    0x7049610a00c03544114020589889003c4001940c04504091403403800c001c0305a8946850800c0d004215000030350006041c4001200d020f0201d0008444030707450b20035026070300c0940c0d409800341c0e243c80780301d4201d44404a0000c6600c060418041c0282e8003d07100f400741d11000c680d080b400745151a81d03a003102c2d003d80d04c00201488101000003503900101131f0000700610f442000810b003034840f071840c407071030042c0045071000d082081480322140e0050b04030080d04100841114009840d48000c3e4440d00b00403108000c0440c050581c031b03010300c80c0700e160050034003e0280c581143c0b03d401c4500c4d10f803201407120b0350381002000140c846014021860400001075441e030412a08000425090804140c0b25080c540902150400d010030190001001400c520392101c0101c480500a0000c84040643c1700c0b10001d00c3c020401003814080f42485060688042544c0e01e50050315140c2a044c0006805040140a5040d152806402c642c2e8000d80e1860600d100481020040b07142101c2c0000c22113042d1000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636582041 1250 636580791 636580837
    0x1b080d110d0b030f03090a3c090b04020313141c080609060307030b0f0406090b0a02070c0801060b070206130911071505071d0123090f0402040b091201060506 69
    0x10480d0301d1000d2140c4c0040c0d45001d0580c8005804449244161143c0c107011044a202640d0341a440043e00b40e4074088241e440140d4580440b1745c0d0700d02d07001e020600c0b440d02141c1b28080c03e041c8203072403084945040e0209030381001d4403480c41d2030429030301c0050a0311a03001e01401d08040c46204580480032074071110001d0814004010702420000c0100c3d002c0d40c414141000410350740d100c0107030007a11804030150780d5192418040c02810510001515941c150401d002c01514035a000b80400b900541c00c6108290b15051007d09070b03110b600c0380d039503992418402200507203003080062880840718508003100c50341c0c402d880b500751421211600607000d03001c1900303c00c1c04100e070f0018014241c40030082146142040c0064035402c8000d100c03000200300c928150f00e160f40102484070f045a90000700c07201c26041c048402e04035034809170819000d00d6451248031401d080074002c2e1025208215642400c00e0a04018007500c0304050b40e050440c3c1d901ca03400020f6603200c810080590843d100c44500e007000d01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636583291 1250 636582041 636582043
    0x14070203100e0d08181e2112071d0f01121109030f030405010903080a051c050105040c020a02060a050306220506010e010c15020a0302120a0e0d1b080d110d0b03 70
    0x41075018007500c8050001d02c1a0004511510398100c21a0440003146e0040c071654038000c5408200da050b0b0700022240120401d803030001d4122417901079450340b1160354010044403511b00240888030607030f1282c00c07a0100e0346408181084050781c1032520024552a564008040e5001049541523160000401d08401d08083c860851185d66040c01540340c24640f40000300002c0013407001400b02e11020541408483c8150200c41d428120b030300c85200c20b1108808030b500100000e00c01caa10443c50107480d164468000300c1c002106580003000c69041800310f12080e2000c0e440201035070303404650340101c2c04160502403241240103e20318070014603403510380009000811078440c1ca0b41031149911107800010558102840002d00424000d6260b0345100010340107070050032801444c1410540070003a10701ca041d804140070104403404c40f840c480c66594103844090203050600080c5117924080000b223032401c0c0050481303250180d40001e0b030700c1c00c0ca4045055500084070000700c10341c5410800d10300c1d00d8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636584541 1250 636583291 636583307
    0x2150c0105010b281403090c2701050d0303091205030403030605043b01060305030706110a1b1b0e0f090105090a02130e0610061e14070203100e0d 64
    0x203d10703458034152074030413150640c2c1e00c1c00e10120840800d84010b014880d12628040005540e000c02d066282d042240300261106040b9100034014011080c50003542d0512011503e082d170310000c1887c501d64204802c2c403003011129141a010b0644500300c550000c0c0031060f11403040200c996845491f400c02e03190060645225070300491186051001c2011000940395140080860003030b054081c14003089000c0d25810f24021580d0060351030f00c1000424847c010005220551198208004162034201242598083d2988102c000741504003400484180b80350244110350044552215504000d80c1140414031583c0000c0b0f481d149400920000f089103000b49a04050504000d0010340380103280c45644418488000e44200c1d103490400303204040c15404800c07014554000e9440620780101d5040c040e482600c110000940000c4d240140e840c0803120f45881d20707105a0701c458214620300003009542d080000c0507030b40740c0102403c00480340d0107885844890302c01c040161403004221305c03004d4070103130f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636585791 1250 636584541 636584549
    0x20616200a03081f060e011d03121c200309210d0f11090105090604031505090d080106050f030910151a040521070329130b010b031302150c010501 64
    0x12113018000d0101580080c18041100c00c01e01c0d180001107101c0100d0761103641c2c1c007030229401d0301928080700c1049113082d004011410b0b240e9000789141382040d108000300c801d8651043c040d062202e02c40d4003402c503044010b42d004400c243c111a9128044980c6200000c50300703e07100b1408034000b42d1041407515034000d44a081110341000c0107840007401c0e1161a9100c3c0c3c840d000e0406c180020910710030760703071542910040c5400089a401408880c2041070081c50291051b0300a44030b02c0c01d03003480c43c1e40b040d00c0c141c0c144c4020fa40c40504103000f002c1007010680015213401e0311030080741c0c0d400041c052144645182010881d042c140100d1408400d03142941c4900500311440908010610550303c41c09019016400b400340d2001400075001c884904010389034200030513561003420311030707054120900c0e032450213018500f01d1103850b1217203c4000307021044842d000307100048520040000b505c404001d144d2003088000b007a65050080c0d070000d00e01d904d0b1599020b95003000466859140c00091003007a002d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636587041 1250 636585791 636585841
    0xe03010c0e10050408030408030a14030c07121b0507050a060905030705060a110a0f0c050f01080406050a0e0d1d010c051b13020318010b01020616200a0308 68
    0x800050030081c1012910501c01d4010320450710380c00c601c140302d00104c070001d01c1e404083d00d8685440b0080300d500e0741d1140043c030001501564100c0610b140c158210b034012801011410b261210342d0303948018141903a480300013032100030f028440031510703007101c0782803082c0c880c10240948a040c04100000e101d1980c00c504100301420206214a440c00660340d03003507234011908662a0290741c4803c6480341084a13110600d070050512010400c50301c840711005052140582d80e940c1074541c020310401060342200c250008070190041004201c0742e51200360040c805003004600c400050140510380b101070080f040000324148a04030200740d517901284400300007464901010074040c3c84942d9903040740a00900003411405034031005a40340c281c2034980b9100814155284d00c0d1810480c1000c40345c0f8200303070782e02e9424602030010540c40810307001d00ca1100c854855180c40c0e0b103810111404182550a03c60340e144090b0118103aa004000c1500550310a40e540c500700c0c600004608000012082043d10b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636588291 1250 636587041 636587051
    0x70e18070e0d05010603060c050403050d0806060702210102041e08071212020712060219021f0c03020c0109060902030d0903030f35010501170903032a030a0c0e0301 72
    0x191580c0111040d072400c504440301e442d28401420070700e005002ca81d20061005191500c800d9000381c201016208990140040e910074402400007031300c60700821211154068010405400185400b02e154020302010401082009042c0c000321400c80e44260407403003083c40c90310614642d08039102c03161405040c1400107000464900140e00104042044008108139009003207490340920030030400e0000c0c010b0540003d2404d5050808200a50200a02d0b2907802a4440c217100e01c05d00016454030380d5080e00d07600040c803501c0200d03084020b11010b0600020107400300070407881001c090148a0600d4003a40c40001c0300040380c8105450320741580111014400d09001c10400b01c0e07000090b00b0900048cc0c1480078501030400c01000704c00c40c0350b03804c019035a03140103081446c10409141c20341c1604c4080c0c840744656920701c0b40140103110106d41c64006580200001611101303800c0c091000b000c843c4c2180e08031502c1c2010102404d410464400038816559250a1081644100e02903c8440150000c01c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636589541 1250 636588291 636588301
    0x30509130b041a0d0303020a110105070f08090c150d09060504080c0c03060f1302011b0f110307030f0602090609130509010b0409030522090f020c0c01020309090106030506010c0605070e18 82
    0x2130065440b41024082c1030f0701040c07002c0890701407000340c490020b410b8020041841c2a0b10064410600c0c0c80b0417400281c911000208114000200d02c024440c000304520415000c80c9448911903102454a0801544840c1c402d000a50300340681405180b05981c42074803014540802842d018500100d0761196001c4018043c03042142c0c0c80c00d582000c0500c9401c07098110600042e40d43d02011801502845040080708050000701e100c03021005209900602480c107204041540c2c1d030809000213080101c60090800000b000d40c0c0c0240b07a2002d000d41075030f0500c1115030000e180e80c5034508003c48c519403030f6410824007090a01c42c002a2542c1290108040919074034020400d001c3c4035005507403004580702c40080010100e40d00c800400e82144140410f40d1140f035005d01a42140c11000454400c0d82c0c00940a90b00100aa820205000d0401e50b1242c0c80c010080f0098280a4100303818000c1c02e1a018000c503c1d140030345032240354a43c0382e1040e000711030380900103041030700714140664201d8102444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636590791 1250 636589541 636589549
    0xf120218010312030902210c010f0e220f05180f070f0e04060b1002030705190f0b1003020415080642030601032103110a0309030509130b041a 62
    0xc01c903d041d81303000606000784d4408a128001511044009403c038442d907000388000c0000c4000700c8507020381e03e44080040c2d005013680c028441c00c034405c5d03018003091981e07035684040d04d15082c0c1843c07070820045a204c07181e010100807550240c4d07041c0c04010a00c6501a84143c007000003001038401d8100030044203191601c2d2040ba80000d009625201802c1c5003c02c09011298000a4861000502880f605120340710080c0d682d6100300d00440d0540901e2066500f182d058083c138420046c1c1001300e0007441c00e556941d85101000c0208049074035000b0300000f0001d61168420f100c0450401842e024089060001c03040ca00003006051848545030810050900c40d05040d0007071400c064040c0760384128100c1380b01d5440380c1d8003d000c82600351180200001c24080c0c403035511000080411070b00c4441c08101c038070407001d4400394004040800003c00118050078400c0d4800840180079181041c103003c05000001d4040c444000d580080603141c00c1c160b030392071405215024465800340704020000103420045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636592041 1250 636590791 636590813
    0x10050f03010306020a030f1401170703021e011b0b0a0b0402070c0612240e0f090a030f0c05031206010306050607050604020d060b06070b010305010c0c2402040f1202180103 75
    0x80019801080002401b800303034216010300400c0200a0042101079040e203110030000b4410300401ca0000701c0c1c0f03000600c1020803a00142d030740240c00f080405e52035048048100072504050380c1080b00d096190000c69003520750040399581304130510141424a1440001584e2500c121288154410064140080c29855810b8103c030482e0030002409521340b010000100000d004d82042c01c2013800c000800300030303550f400c0d000381ea208240c100790b0f45d21007105007680a031045034142c840c4d5104443e21000b0902800e051403c4400c41d2402802000b8265203660441d001058201340748500001070241e1b035a094042c04000d0081a1020340c00e015458880c95038400c405400070780204a03149082c0207100c0ea94211407421100a404075030f42e0ba0035850f120ba40d800d800d00c002c2e00c05519000c0301042180c03050941440300c981040c001208000800d4690301001d6180003a80c8242c0e60800000407200001030a41000306451505803070ad0030381c20700500284159401900030495900801840080c40645035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636593291 1250 636592041 636592043
    0x10e04050703020f0414090108070b04032d080c06060306090a060209210d0e150315010c0c06030c17040c0605030411180a0b031c11010b040504050c10050f030103 71
    0x80454151601c0710181e00a1081c0300f04e40801c20720004010940540044004151500550709246180c1c7c0c1c800c8a103403a242280200316014004110400110b1741506050444082001420302c402c00d151081541c89018800211040d40b0003148142140d00203004107544003100781c0241c90585002c0700d6113a00c45c0032a81004010399404130700e224158599017142c0da980d070b2086403c1d440b5030020b502050b6950b02400c01d40780019414280140702030902c003c12892101e60010b0300c60458031f62601c0015003854910340141000900700a84022a0610040100800507910300080c00b0304540002071002a80c8488258141078074014800021b07040040c0c0700845480d0310b007003900c81e1241e1828003a003c0760403c020747c3c41401240c900e8041240c0d00c49207409082da000d0108080c014030001d054a900705d201d55900303110071010400c580f15011700305408180041100000d1224045070014040380c009503026500d590140c15421030074104010242c00044036818260704041403c0f100d18418801408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636594541 1250 636593291 636593299
    0xc03011a0d03020a020315040b0a060522090f1b06030203040f0314040801050a020a09080d090e0a200a0e010c0b070f09170a1203020c031e04030209130302010b010e010e 74
    0x40c0076050510a00480d44510350003811340746600007155401c0c890070b90658040c1c418001c0440414000c1d1a5403089104490010384501221209580141c04180c0e51450b000d2166444801420009800740c0407548544d00c14080041d80c2182c034145401c0382621500000f050510400510000c80e10f6403460082c9aa0b06240c2101001821031031420030340101d03440891550709140900060007219005012909640d5880e030300350700d6441419933510308045880c64089025a4002d000c0c0310340b0468020b038032040005022407401040480718031051000503846a4900700030481b4400f15601c0380d0703d8000c080003441c2c10003506090382c45101c85018080d101c4420300020720300810b8010b000d400c14a00034040c050b00f44200140841106459204032401252141300449080220324001d1090751000e50080e4021070030b00101400d041c55140c41101444d0342c07074006110000059541eaa46135202d05c040e00d80c5142c00c1816450064290f131244100d05060006050304c25480c0d9034401c0000303028203000c035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636595791 1250 636594541 636594559
    0x50c1c051005060f030105090610121113090b0f01080402150a0e0901120512190c080c0102030702070603050115080f061f35010302150f1b0c03011a 65
    0x4045428907802a400703640c201e9004180b0080c03d0700c2ca10f0103035048950603150400d82e40d40304801c01c2a070492424010010a02c010120032450700c0b107900c00a8420040303006036140488400c1c2207004091703580d0040f80f81517144c840c1001d0901304140d8800c0ea800703080c281450a4146640020aa00805280907048460100d038949906102e060442503000c009084541c0d1561540c1d00810141500c1c4010b540d0f5201d48201030b201c51003004211001006411003c0071003012100c4103c1c0c03a2000d058066078500003d01419041000a2000b0340c01030f14990024883c62b0b00d07058000d02030f034505134000008202000040031519400810595020006200d0201d041d076070000001c0f0103a580b04010310049106008030310660360403407600701c02079400e0300d4a410605030701c25000398a0140b5521840c09a40d1002c01040182441c11640040b00b012070611400e080314400205829000a0307000a00044484034600d0852400e01004040810a42c000e206100f0722481e030140c0308485003c010300400c248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636597041 1250 636595791 636595801
    0xa0c090c030e01020a02032709131109060f0103110d14070813050304050108180d050c010e0a050c010f110d0309150c08041b170d020105010501081005010c031e090801050c1c05 77
    0x192048c0840300700103000e0312090030860f01100060909550840f01c0c1602d40c041003000d40b603d014880d105100080c51090455140001100580000e5916043c40042801315600606c13084c050200401c59064000340149000c00307005044500183c1042d08580d60103862601141001c411242960800e090842e42034503155240840c1001c100302c2050719004140d1410455035001c00100a08207905000303200e20180346904c151035a85a00c80140a9441240030b2030f400e50048921101c8102c550402030207010440901d1420900d00340c00020002c0d544100620401c00c80305107240c010341405000700865100a10003400041000d00080c12a0000d500d80b428519003502060000c1d009110f803440c0e40c00540c2c0d00c6590b075000c0c8048588059424080045202d5100711441d078460041070a0b00e50410b40780c0344c01503a114007003000136002c01140c8002e41e43e480e4032409a50015080c00c0da60b81481c076180c207840c035003103036005050f8440000e801c100401404124944d0303401440c5183c00002175a46070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636598291 1250 636597041 636597097
    0x12120a17040b0a05190c0809071406091309020a1401020d030c12050946080409020c071a0d15080d03180b0c040e01060e1c02030a0c090c030e01020a0203 67
    0x6805c0c400e161030a01c600c50102d15804a1b41a000752040001c4a0099440e41620411060804800b07070700400c041c03101c1c0c07400b403500400128600c1070f00d41d0009441e00072074010030099040c54200303010f907074803800c05100c0c2941d04000088040701036180c00c104285040200400b0520002c00c1b612034903890350702140a448090100103044040c01c41551120804003a0303c1b4051031190500c881c0c008541d034404140701c0302c282034040d442e43e40607182c54903103414601440c0007500880741a0800d1b1194030000b01d42c031040000394a900c40b4913055055142c44c42010b030301d004e0750a100201014012200d004100d0807c0000e200c40703559420f0f09003c240f103222030810000340c0203404000340507421071070141300e00c601500008009681c00d1b448024016a207a00065513420000759441c2e0b0403240745030015000b030b8002400c0c4070743c3c60300c000c045d00c2088415490b0132501200941000c0b6000d591140407100040e014415000c10b118940000e5081c1900c610b0080c1d128014404a1420b2139025560010687d407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636599541 1250 636598291 636598321
    0x40b0f1807060e040f090b1317040303092409060e060f0d05190c090b0714060403030e070609030b180f03070515090a0c1412120a17040b0a05 62
    0x1120408036000d40381d40300001003501c0d0f8290070042c00b91380750503800b040700c1c030681c01000146030708040300c0c40141d2204641042210201c1c2001d0301c4040031708080050507034849008000441c040d642d003c03421810500c0da80071480c203401110202032946180001e4031030b00240301c2401c4481c582844400482e291000c501144610170f804003c42c070300010604100329860740101c0c080d140c22042e90410640d00401a0308a40c1003031849004902400020802c5d10302d5031006101f118070920b50b003104a081c80000c03a25181042c1c80440220392144425894180e0402002000341620300c2c14000d1940b56440300f0f400450080c0c030514204c00400d11608400c501003280a014140aa0459680c1c00d0b150030f1658583c2d6107065081c01d0200341e48042120880f00194004581d500104070365146c520300036032180682102000c1c160419910003031703131000003018000c1003009a181140c042d52290100b90003049004180e10a10000c0110824080070480d4850115030020600400044e5915183c1344451002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636600791 1250 636599541 636599581
    0x902090d05060405011d16090515030d0306030b0c0703090e1f030f060c140a0c05010b031902031e0d03180b010b0c01050108011a0607021c08030f0f040b0f 68
    0x2c4180c2042c4000c00c081507000d2450060349451003440c1900c0411100e898440390484510855000b500502007a0780560015403c00c10340f40c80140b05400310404281404042c5038600086079440f00b04000707001602d0282c507403052600d40140d1408103950b401501c003031030354040c030040142514005030740d002c1c20700c0d5003019043d1144010444a036680c40e06506103107800ca0300701c500074100f5040b01d01c40c0f80165030969810b2a280c812904000c40c0d00c6003214080d90000c8142c40c90340d01e8400d280070b20b44050140060903154420703080910074003401814503100e540101c0c81002800c0303400390582114003052203800d241c182d180100e20340e040803090702c0400c982c540c4007070aa10542000065030305145001840100002c00c000d0017141e0740c66075428200d4a80c0300100b220740f9a00c50b204c2c0118504103006100240c80207050310110204052805c1c1d41c007200078021140d007500081031254199100707201c50740c011304c135201403940d42c600b941c4c3d02210920054103501d00c20350041d0110320301180080d4050000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636602041 1250 636600791 636600793
    0x130e04021c0f050c03010507090312031b031a0307052b0b07110f1507030e030c061e010801050103110607061b270b19090801090308060a0605130902090d05 68
    0x1840d401e00780000a0b40070358038126154421420040064201800382d00d2040000e44c03202c11040f481d6484540d0001c02c010b00c1d01d02007596420007000b010f4000c080c20143c4a1069600280e2007040c10355560000d4440032134a4441da1140c001004180d9803040b11a203103c2d90750825500500c080c5400315902c030074540d0014200c2c1040c0c820002100e501212540d4030800c03c1d0200c03400956202801904c40542010b814981c0c4495000a4401c5020b6000900b1041c0da0104580c605003c16030a1400d220b020348841c0d0103145a40e82c641640c08441c24680c3c05440100c4c02000903515554595000b00c0c4e00f40040e07030041c00040343d410280800380e03010104c0a1401d00034903009042d2940014016450000c44003000403c011104c5094840400914203603105040d00ca40f170501d960f60000d100c0400350031403404202443c100420f00e240280034034525940303c0d459044450611000f003106c40b40d0b880d0806010072500740700b444810707107e0f48a40710884140490041e40c40c1c1ca040d02041901c0000b9a000d401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636603291 1250 636602041 636602089
    0x17070203070b0a03050712051003061d06040b04020306090303070507030e130513020907141206030f12070c140f0d2f1026060d020909060714130e0402 66
    0x2103901604100d102c6c90301035070303640b14000b40c1405440807210b05540313020168804c5441440001c030130703500c00440d114410103694002c0b808048424070b04075044904844582c3c00c1c400340f004500702044940e42205600300514114540351034010480e000316580a0704100003803410780c40e91380301e0850484010f0602402840b0505e40001206917071080c01208a0140c040c0c1d00c001060544114409150481079680951a00320080f0000703400800240c40c0e60303498000d4071103251080400704601e10000c0715241049803290705e82d05103e101c00909034411000c0c5400017031141700e507684280d0000b00c0d000046804041d40ca1180c1400385403540090982018402400c1180340001c8048468042d5290115510b9040d0340e00300c20101ea22103810f603280064254440b448003111522030130f0f510303840310020300100c1985d15250002188504142c0715510ba41d0415818040c019074401c0300074600c90304400c441803410045500c5003160f44518031408140c0081d100201b000c40d0b6803040a940700001c00006168 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636604541 1250 636603291 636603307
    0x105010c110a0314011a060301050f120c21010b091003030309030215090705090604091112030708030f010501030b012f0708010f0c1b05060103020f060918150402040317070203070b 79
    0x8001c10480c6c07841548640c403078880304206d2900c0d004603030507164068100d81c0d09200200a03c00d003210715a0b41401980a040302410094950008810325420004c0305248210801c0015a00316030b414405a8000d41040080011002418041c201281d601d461f001660300c00c00d040407828070f010000000300c201182c0c0c06104184c0c80c0000e401080d14400c440c00c06007501c5900400c82124101c210090500c482030880627540e140200d1190300000003c0c2c1585d10f8801c03560b4501d007442d402240d0107214402e051005001659040c880e80c545900b081c286403051498441072450044000c64001040c00349110b0394144010b0300703201150081201d0002804000c1144002c4006484841e803c0c40020310611111082240c1030b90100c2c0d80150001d0141445908540910110341c0c42e24400d42d40041d0304001c01496915221800340d2281d1481c900100f060074291301070707007000030003804a030305c00ca00604c000d0003c5903906042d0030340110008142603542c1201c1c80464148510f507884039000780000704174030b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636605791 1250 636604541 636604543
    0xb040201030209033306030d1b2901050405061e12070b181f080a0b0d11150f180109050d050105010e0a0c0c060c140d140a050105010c110a0314 63
    0xd80d0b40c15220a00039511008030001204045c0200d9046a0591008200100e0781d409812411000c003000400b002c0d10000c4c64548040131941d454410a100640380c0305526050300042c121745c0500002c860510132424500002004c0000c01c6520300414109442903100c503a031001c0c8601408900f00f419504140e40c1c40c1000c050307680010341d58242c001c050004000540c07410109010302d002449043d16041104414221608000184003007041c0b80d580c089000350383c0ea1a1041c22055205407100301c103020426007885901c89c001d844070f1513008030030f04c1010016a4000f0680320644000420f038405804401c0c0101e40c002080d0340f2045d00014030b40703010814081d040d00482d0680d00c000848540c2c90311815040000c0f43d250051400005058417442c10004116811811207803000c1d01d0a400c2041d02c001d942000ca5000140c40050240d80c3c45407420030385458030b051035000410640c03c00842d0326020001e08490041d180c014041140698648015600c0007466006190000c214100b824001c140031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636607041 1250 636605791 636605833
    0xf1e040501120f150f091410050705090906210d080c130e1f080f06220201050d0228080906010810020d06080111120c04120b04020103020903 62
    0x5140110300300000030440311008a4818030b0181d000d01c8000190340c0c907440754200744901041c01045a03841e10148020650b403400b13801402c80c042c2920800c1c03480e2204041c0c0c074280d81d2860000300c05041604125010b50001d003a02c064600a90fa081000d41d9401d0000d40d02c10a030340c01c24000c0e040030300f540c400f0301d002c009042d80c55542e041d1124003240d00d8020400b48032b4026100044543d100509082c0300302c0c10040d40f81c607044001c00050b00103e000c5201124460421900541941d5100c0c170b50031041c01104105054018000f004159003100c80c4000864091150346400ba050000015031000419000e60495000c2c3c0645000c116801c0e80880c6400d419602814075080001c5090010645150010941761304030f80600c030003400b640d41c45844560183d04200f200003c80c0f5542c8000050700c1500703000d4803a44000028100365030724815000079200d002c0c02307030001122182c140410700c001c0d02c120003440c0219801c4603c0c4002c5681d43e10049010344503405880350180582042000c4c5110003000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636608291 1250 636607041 636607099
    0x14192f07120206060f010c0201021903021b06040807031218180b03390a241106040303092108070e030c0d081e033408070e0f 55
    0x864204040c1d4541283d5561054507215440118041000c0306503000310510000c046c13041c015100d801c0c4907230800e503080800f844001c1d070158004000311640031004640c8040081c0c0d049501c1030404d07040415895580c02c45000050140d40d000721040f014a01a000425600c0e151060001026403035581e8488802c20081000e8802801d0020410341e9180c0403401c0015032020307001030500c0d0345000f04801c03515010011a400d10300070750712280c0c600d616101002e50280100c030403107034801d218040ca03000b2719a424000140400400305144640c110020504079082034061601282446841c01d101c40c2c14440c000c00303200980003950086105a4205440600c40e207030300e03120034003400501c500b45034441c4445d6041551002030301c8000d00002d45250042c11020310410a51008201070391101c07a06644191003034100301c40602080c1c108034040c4020240b9044d01c1c440c1d0428024058040a03019043c007030550720500044c0382e4515000e445500158105a03401040019020b900104940203641d44c221 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636609541 1250 636608291 636608303
    0x403060b0405070504051807050c010f2306012715080601020d0311040320061b0d0c080d05190c09050f090c07080f04031a010914192f07 60
    0xb000071280c0d8020415076084800281000141d880d0ba00102482d4050080c9088107011080c01700c000100d009204496401191600000354440c002e03102090090280e0a0071106050b404d040008990344583d541c4903081c05180d541841101d00400c1759240c50310303600a51003140948031b02030352903035101e100340b401002c080e0240c601c4080c1c914011400e964400040000682c01000204005801104003c0f070010168400c10665141000080c906501980da010422138920f00300c4103903400280240840c0120a040c041004e400ca0754600303045024218a9551050f95100020821a04000e0568950440030400c00c43c840d40000060200c446278051140242082404c521a90802c1040e03e800b4902d59041c40d8140119070341c0741840c681c408140b4a1204030180000000134114098241c0c800c40070460090393340d030411000c401154000c1d008251815000d5050243d110b200031411565483e02c08004154070a20868a04000d00741601490f203c0d104d4840640d66900c0510140c02102d200704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636610791 1250 636609541 636609551
    0xb06070614070806010e060d0f0e0102030f1302240903070608090c0d0c0519090501030825020a061101020f0c1b0a0807051c060e0a0c1a030a020d0b060403060b04 71
    0x30710300300c0700d140e021504e6901080c00034081a03100d141003000b0b00030000c140d01c03000c1444001840d80200361010b0b480c151f200f50f90003105101241d43c0e4411081c1d8403d9501c2c105815181e4245c00180078840d0a6006c00c0482c0e4418100c4500444198201d95420034054200e034021540e03114010300c500d00465103511140921000c8400c02c0c600006040322541c1c0001060784410304110030002000c046822441941d407000d0360018546016001e140d00850103200001c1d112001c9190200341050290311485050103038010750b00050341d0300401070302500c0482c6032011201d031400180c00c1c02445082d104484448001c144c018001c64002007421900c0a0340d15114080c035051801d02007141883d0040b01400d421808048c805400c120315940e041882e078482000507070307019850707410072540820702019650b00607441582c2400443c51140c00141055440001004401d05512425000c0a0442c00e100c0b80c0000c0c90880b4070403250008620210010015981c4075964904040108a50446140150304007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636612041 1250 636610791 636610801
    0x20c0a0204110403031d27070e01030608100507140d1b090e01090902010c0605070e01090b090a091a0a0e0a0f020306060a0c0204110a0309020310050405030f0a030b06070614 76
    0xb9080c0c6080320f42c142c0710301d6003000b0344603002e03006481d1403086030342c001c0c6034070451a25880704034170102184645540d12a145061615008143c0c091107461141810309054042018000000340440c0780c211070740380000c560b121f580088614a0b6081341d200c1c0107120200b0322241d03c44441d44550300c85420b0445251442a100302c0c140c950399040d2042040342c0c525080100a0001d40303810602c0c84610514211441c41025550300045130400e80b80c1c06c0004010000d6041c880d42c001c00b00d0f80113010701401d440e04001104000503000c0000380140e0000940391403031100660b00180815074625001400f03840e60580751865030b0001c45046814580007410041c014103404018801c80e1701444003c0d2a4074500807540304141c90340075010034104d0b0002d9980c0d03c1140c401005030050b00c407504140d50049003040c4580100f52500740b51012060f46186080b05103c00200d0003c1212294a9020015a10340c0c5440342c09030020300d150f0036415002100020303500104400c80c0e1000c0948409503000c00d0182d118 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636613291 1250 636612041 636612071
    0x4110d0c020712020d0f050304090614040f0e1908071211123f01240207081915020301030506040c060806090f150a0305034315020c0a0204 61
    0x21043c4081e4000e40714901500104400f007000740841801081120b00c1d1070f50303071900b450455a480d8002c0704540401c049443c400d21701400396412042e00a0801c2c410003915880d499168070700d41c03400e908003910b102e94107402c211041d010346040a42012002681c6401000702034400711090b0002c60b168060201034490009a11054030403840300058031000030204401a5102c0e01c80840c42452284c01845010b0440ac07000b03800300b4082e000760b16405850240011150001701a03104155040d0f40007a102882290320003d004100d004400d400100c0b0098a0f04105d102039004050168200380004004028040000b481d1380c082c81c401d411081d02c0580d540d0049400c05c50688000b984502103a001c24419190f10400c2034003c1c801c480346040c2c03800200001a0807441d10380c4100c6043d0004511001c02004480c581384031550041034544403411139040701e2400742101030350300c080075615a44281c240526850310146001070142c0c02c6560381c41071480e0320b03580e00001c0b00403445903040007068003501d02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636614541 1250 636613291 636613319
    0x1b0307080a0b0406240506031e0403031a10120f09120e09010b0423130c020705030706030510170c04110702120d020a02040509151915030c05040b04110d0c0207 70
    0x306517a01c80c10340d2410501044880e170300c0075000070000410050559080d540310b12400340554401e450015000004807200003806a516100354850700620008410071500401141243c02c18004001081c02101d00f944c401007402500240984904100386a44540c1000caa004140402c40701c5040b03070b81c2d03500f034569000d224074050101c006800c11950b408a1160001e40c5011510040c03c0dd121f0506a404110885103010b8141c40180d10442c0204441d080520031307800505000e2030b041c09949001e4641c0c03209886144605140c0d884400c00610301c03104280280c0701c0c01c6600030810322411031511080074603134000074011780c42980c60101a00304d01500103610791050489401504141440d41c08000003000c00519010711402005070022420380080f4813a07204040000030f501d0000d450650441c00c64052162585d440c000c2104107101040181c50900e0469008440101c0e03145801804140a80b0010820800c0800301240c0d408480940d5000041407850310b030b0071035105032f64500c2846000c034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636615791 1250 636614541 636614591
    0x602070f080a0f08030601140f0a030e0a03020a1b0906060309060b09010e01091a041107050609070b04031205090d0804080d140d090206040806040f020a06111b0307080a0b0406 77
    0x30b4983d8000014403c2d07000380d50300102c14100746180c422007040300903855004a500d0030012000141054a594140c401d850403810090018502e0341c0964dd4069074030350f621507016001004100a03070581c1c509284008026112a84050080c1a580c0001402800c40c8500c00c81c0d0795801e0444440c55820f01d9083c903412540803001c00b012076443e240d502801402014030b00040d03800f206980423010384541c01001c0c030382403e00359a2507881843e800d1160a00d00040c2c010580c940103450204224070341c00d0140c4040c0d9400c41d43e82145200301ca14283ca4910500d00003d030044d45440303442081c814071501800443d92040159401440868000c440e5030b16811210b8007044d80178403151031440101d510902070241301605940c5410b44070340070302c1d15280044504a070302a02c00d42c01d01d002c604102e00304030014145801c00c11103000c407504840e51290326001540e255000d03010552496503500700400802450080d0036103030030841d181000c00e01c1030703000c03281582d0f058107110b5000d00b40a20040c000e8504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636617041 1250 636615791 636615803
    0x11031b060f0106111e1e0703140604030905060f042115020a0206150102070b0d02030a1b0e010c0201140c011505030705030a0b0709051507110105090117090312010602070f080a 77
    0x528084441102d0507210850204424406c028040c980007401d412294404411030004042ca640b035460080050050044200c00c80d030030000501c40026080110301f400d40384111280398652086040a01190286a0010344081b25074048503400110702d8040d4076010b4000c070074682e0000000c03082d04003603214070b0000300010b0340a1000a058021a2100000e81d400148142c40d0550343d251031038401030b08803004908042d80c3c00010b11540304000e10030104084050309550752546200500540b510440d98900c034188480c50b44900c3c02c580c0b04003992010741e840040070f00c0e101c440c14807590b4001c0c0880080140212180c400228441c500000c4072001c0b210001d00614420696035200b0b00307104400b900580a22111300408074180d5039502d00184103005603025140c0701c40142c01c001944802c50200c1c40d041c814100207215040e64400112103181c0041d80800303180da110b14032481d103540b14a00c80303d139502d0001000464030507404104402200e66041070f20343d41507180d0603015190852104000d201c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636618291 1250 636617041 636617053
    0xc090501080c0403050706050a110106050f060c0f06010801020a08061e0d03020f030d0b040f112505031602101103030f07020f160501030c0e030c0111031b060f010611 73
    0x4940c80341c03030000d602c03144200d10380307060a50302c0d07640c0ca18000c10794000c03801050000c9043d00c400e40d03101c1c012842090b90702c802401294600008180300c40340c4148100e0245c40d0000303d181e50380d2801c0103024041d00c4010300b2a072803503a4a000d424000d4104200380c00015841c10085815845c00076003021002804134609048400d1070380801145031b46418085042d80501d600e259501d4101344050201541841780109012003208108030842c0c150014410085e443c003900003e00c048c0b00c3c03080d184030800031004a032001c00c41e180c02504241c83c8030801001803000080d07113a030441d07803000c864103100d1099030000080b00060609031040d01302c41001000b0b603882400041c0c4808030b40c005e0250042005c0c015101c61345c3c500e420542c05d108100a200d110b00f010110300f00b04030b50741441800b031144140e24251401c51942d400282d1555500c9640310f04001d480f07881c0000d02c40b410700480b40404500322030035030784040603050076450361421140384030fa010b958030002600354050307580130380a8140d580151003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636619541 1250 636618291 636618299
    0x203010611031903180b1303030e031c0b03030405060f12060a030f0204090303061508100b0a1e052206020714030c150d0e070801050901060b0a03020a031407030b03010b01030c09 78
    0x80680840254006101c5d070305d0a004079125599041c01070004804054134180f150030041e0075240c0b90524108150300401c4603075100c54200d49040003164a400001c650003a42ca00000d02d540100e4001a40c800700000c0d01a03c1100f009004180c140340c2031100e603089513501020800f44203014880682100d0701c00c0c01d08401860640d000c801094803906000501d60f4a40f449c03103070300800c948082e03008529120b0500055a20038034010000f01120764180e1700e07200354404024000c28000c401c40e00c803c03039040c0c1d401c0b68031030058043e0345460050f01c41600074517114404507420540d0314490440540242d0801007200e0103c00c083d1010400050000c00c911070744075050007640c012a18480220300020710080c6000b00247c020300b4146420880100346150410b2100e03800c50b00050f1220401e071713150890070001035080d54181e0360812440d090040e1110140f220030740c041c00101696515501944c010401025056440004207150070780c000c000d80c0c00c1d06030040d0308a49980b092000400c601c1e0400300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636620791 1250 636619541 636619547
    0x81207121103070609030e09060f01050405040e10020a02030a0905090420010c02150405030705061614010f020d0509060708090304050d02120106080c13090c1a0c0a050102030106110319 81
    0x200a00c401c0459183c10b8264036001c003150350b200021070020700e01900780d01103450010041c9402440484480155400c07400002e03040d0700c1180f050500903921001500002c2400b80804034503a40c409205543d00d45410000a40b241c0c440b40550b0301181c0c444001203181d007041a01071788a1030b440304030f058506140306c000300d041902241c0c0b020f04008092803008010307241d10180240f000e030b80f0b40b103080c0c0302c505100030035040100c55001a40500e0040c060402510b14510301c00c00456000a0410200d8101a402c11301428104445a081a000040c6840c200f00583d21881c403600b204c005940c0c043e151240100c0707060070151814412030f40140401d108526102d89401500d51004044020001c034040c15103003541d042e41d0002c10103030812800c0d0b420500b04461007a401148007002003014039070326940d00329161654015021802d020154150500c55540100c5680d900614201e410610a500d40340c1d020354002d02500000071520401080a41c1c800026505620036040034050b20110355030040f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636622041 1250 636620791 636620807
    0x5041505070602130906091404080a0806150f041404090f14070f090e060619120807140624011706060702130b09071b2312030108120712 60
    0x26900590f081110b50340f6400540f010900810a9420120740c091509207900d0407104040c000e81c0c0d905451038200000510752074211181701d0b819041c40c0000d43c541344040f550250201c03103402074902c40000d07550584042c3d2005441203403440c800d600741c0256084140f05c01c0c0c510900c00140302d02e40b00c4040c540080d2201080d03003080912a011544d0b92562400a18036a0f040b84d40004075140e6150a10032483c0d03001c0c000c49a00000c195030715036502401809500c004159840384081c0c000140c2c0403502048540801c4403030f00d84e004403210038910341401100c2d40f504001c0c1c4940712040240048000d8041c540c0403e414080d00503190345c10300d00c00028a80b4004c5000a0040e9408803040101e00f00690b01e40b2070b100c0204085800014800d1014010301250100c040d2402051000c1001c2e20918010348183d80c11046510011036003d1007440c030342090080e0b00501c100e44c0c2d0f6000300d03404050410101400366040354906011030b40500140d03002d684091182d03803005004017081002c4210128051500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636623291 1250 636622041 636622043
    0xc020405072a11060406031a2e020319080709060f17061c08030703050106050403080f160c12050c100207120f060507030f05150f01120b0a06020c010f0504150507 71
    0x94030000c0f904003c0001d0a0350f002c1d801c030001103940c80704400d1b803c005500c6160301581080d11003140c050584046001c290551405d40c041d0788822071038030003849100388180d070314a00420b004071748401000003000d07041e428102c41c041e0010b901c0450000e1364a1040c1409122050a03443c3c0c4640c0000b0841e800064960080c609500001c8001034480001e10188601c8521806440c59036142c1c20500801010b50b601a48a401004018403007400814407050881e0b4094502c402c2840d0303200080d40701b0100b1410400c82c054030100035034034000354892040700c41c244503e10500903140e89850000c200090410300d03d541c0d00c016800f01c6410b00410111001880116016030790078030744a8290b41c0c801c0103480003203480d000025201c1a1071200407006010342500014030450601440b401c03080490404120b40300842d0420401d1015651203c82a6004850200002d0400c80ea1240c40b100c0c080e503110f201da10007900040780310350507442c154070600540702550038402d00400840c9490104030390703e82240b40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636624541 1250 636623291 636623303
    0x7032d0212010c110604020f06031509040b09010608011107060c1b0309050f04091101030b01050403061a031212010e0703060801140106020706050903060f0a0608030304030c020405072a 81
    0x10801503601c1c0019240008034440010440e1691880020031206650151200a9000b00d00b400016500c54036140c03811082524072544983d502012000424610071009400005440030300003480880340b61580f103906640c00034009159070b0a502c9080700d01c9140c88541c0e4030014000d000004856400440340324456141003580e00b000b00070f241c0c004419402044001c0340c440a410805420440644080315804507010080c07100301d43c82d0b078095040800d41813030406940b009448507a03030090040d80c0c080c5811010411404c0081c401d50701c113420074040211f11901c100b40321002008442c00850740c01c0056a9004003299282c40e0002c0c581220180901051584450000c01e00040c00d00c228030860f100494145842e5160080c0a410910150008800c21204001100711a203001a04540010580301050155551000490010702e150340000c0c006010010070720080c117a00000d40700c2e80c00d00071a0204070702d445040c0140c900015080c0f16000c807400b81d410b84201c140004802010701c42c0102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636625791 1250 636624541 636624623
    0xf060f0301121416030c0e010b0d3c0b1918290a05030105071b0503040b0c0307060e032b1401080f0709051312050f07140f0703 56
    0x3c0c51505007800014011880c15404d5820400d001141001c080201200c01c0043c140e541401491000c2d4410305001e1009540c60790405d06024441c1e04101c01d18541e000420706903003100f2008110180050108102c2c56410802c41755107030b1901c480e4005908440072180e950035031500c50881c0840c650346616004465581100c00c0a2841c1040328072854905031410000869141c01003004400c2c0581019009038506820880d410340c0051449205081c480c00811201e503541c42c0c010b165205541051101c101d010850071699200040503210380e41c03250f0401d10203c0c101040c00d0341e503402000b03220380010070303c0140101d070300024010400410307102c084040f90707071b400800e140301c1095001e91002e041035004991008580700240490b00241403c58420b020f6800c2a82195111024802c00a40990724449003500824010b40c00c840458600058490701c9003824100303500211b0158015480c280601406085404004520141920f61083d00c003207001440142d04800341a09102c010003c040c00f0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636627041 1250 636625791 636625823
    0xf0207090f020901020f1204120f05100501061d01021f0b15030615120c0906120906061c03080121050708010e0f12040302010815120109020f060f030112 67
    0x9006026020741034100142e0349200d480d0009141150f00c954451464114010910070b400301801120100c4143d0302d06030000c2002c03030400c02d103413180f85070008041e0300c12518242000310301c940000e412242c182e210152040410001c95010002a40c24280140c00c041ea4441d20301c1d02c10002e2040ca240504000220317400580c000c9074003017100c00c40703141c51100044100050791a1502910300d00c051680d0525080c02e251407000c0340c400802502d8074044510120700b00d10310342c075600160748104049805010560a10000c401e40394070b41651500e004014030290701550394ad0340501252200d03419030780c0803d660300c2c2c16107480c120505a5260201c0400900500b400f0507801c00040f4083c2c607861000144140921f1112460300b000d0b03618101e0541c100000c107403568072820065804982c0c0a0a24100c04e542e60041015001d078811986a070140300146500ba1418055001107000c2d403080d11041000103080040102e00d0003200c61047c00440c1c10070041c40410190f40d0f650720444c2c811800950210320f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636628291 1250 636627041 636627059
    0xc06011514090f36010e0c0a08012306070c08070501030614090402030c09071e08070e040506240315030d0c060b0607120e01080f010f03060e010e0304030b0906011215150b0408300a0f0207 82
    0x706c0100ed0b0741c08503810360305110510050120000904003403c0800c0782c14030705406140d00200c14603a841c880c3d060f001c00181503450502400400c98002001a03803107240500000d403000e640b410481240c241f11641280407a4080c1c41d001d80224142c2d29051481400101000003420008180c250855829903e0076604608200d00c1c4140e402c1d51000f0a440f0f280800039003058a0031160410320ae03501000729841c2503908900c2c4101290b8200501007070740c05c03e01000c110f0a100782200181544c030354244e501426940107614a9990a00f40d0341c1c072581d6141c204041c03001e00c500b80140c4611900301e01082002400980c01440c40d04c6900300049040000605007600310740007035109542d1001202d007040310202d01801600c0c09440115040703507034078806842c0c880d0b4001d480c0d014103031104d50344d000b041d01c0410300b031a1010080007148003203581c458a8103034030394507001c1c4140e1036100c83c6200780c80d9401c105c240c0110210000b95140940b8103040e684041144c3c00c0003040c0c0761109500543c0008210700071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636629541 1250 636628291 636628297
    0x80313062a0c03080d06180912050a090b0307050703030c081605092e090e0405060c070203010e0a0305180a1503020f0c06011514090f36010e0c0a08012306 68
    0x418005d001449070725206020308031070584003d03010300b140303441d84010008109605c4901d044182c0d1801940311010242d058411030302641208107200008420061a29440030043c06214841c1e9400c0c45012041c1c076095400c444180c402500c40b6162804000c61140310742c001c0c0c50042c03030050891f0890380b00034079100701010205508490500780c0031880d44c9002d0300014114014200c250302e11515180948445484501c0941102d1340400001010000d540d0250000f07800111010155040e00c2c12a240c00342103640a104100300d0100f8043d40c80c00d842c500b0306000401c89010310002c10b0209180f0804400941c0403070180401500b0510050090040400100d4041e148166025964030136080c8098098820302c41481c0301c0040400140c040f640303800d21101c100c031505503a4109401d41c020220054094040075219a16107c01c88000c3e02c80e562450031130484941c903541a94546801c0304010a6200308051100440c189500400c107003c10150140b5682180e94061801d9040360000200198 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636630791 1250 636629541 636629557
    0x6031e010f0e0f0c090d0f0203010f0504020f040b060301090504140a080901030f0c0509010f05040503010908030f0a0b01020604080309150a09032705120109060501080313062a0c0308 80
    0x442075410520604060701142d41d0803540c09450624030f468841403045851003007200c140c0c040c44042da243d00800000500d0088181e90040084c440c000f00c02680300002c004c12a426413040028554203111402c0030320030324170340c0c0c0700140130355265a0a01c440c080c05040f01400440d050b0030180c0c6811030b0b28406100809800d4803503421035039110b84403030004080c1c940304e28032681003500d04001001101c3d0080100d80c0d10003400c2c00d04500c0145903440a603024011036012076010f509281b6400104035890006600c40c030260f640401980d21003c036444101c0746444034140c0968024008100403a503400050341e807105910301100d4580f4400e60914032031860503211130030055120551081003513040f04003034115a051a20540138440401c003081100d0b6007601c5001e004e0f0040302c4582101c0c980c01c2d00856007058100c1424850f07542e545c0311081c0c0d0380e840a04103510040707040304081800d61180f010811312040e400589803460000c149880d0a500c420300c1c040707070a0020a000040000c2d51040501000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636632041 1250 636630791 636630809
    0x40b120a0804090b0414060d030315060509010909020f12150d0803071706011b1506032102030403021305180a0803010501091220060c0a050a060f05060f06031e01 71
    0x103d1600f40ca1100b91504980361501c82d5040002c0c01240441c4e10034210751103c42140e0009410a032801e0960060590030007808036121048004240b16030090018000c400080c0e880103081c076669802403089000c4d0052a01840c80200080c50011003501c1241c1c0d0089402d84000751284241000504080c1341204100e032444030100800c941039030050140d0410710841c4408400c60724101000034542d22480303140035501c440411400c0240f0480c0048d01500a0903a102004995240e040c007017141c820f80503d80100d40c0301030060301d0702d251002c820340d0210395015103001200b0004400348409050300030180c802040d040810890340c0c160801440c85118000c0340c10590365410100018825841500a07800000c01042c0c20300001c2d8210102425020b8032440170f020303141301e030340001d59a0310408003500d94900c2403500380008d0250118015189034802d15041241c41043c0c1d044d5000e680c411110240c1c40014a180c02040341840750003161302c01b4003110404202c210004000c20800c000303804c441c40d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636633291 1250 636632041 636632047
    0x20309010504150c0c030819182604290a090e0a020405011d0307031203050a0b010c020f090709050d1401050c0705030a0311120a1a010e0a0302040b120a08 68
    0x2444002c2989442200000e41e05020f81c4094a601800120005c00c0084c06c00c030600000070180b59000d5000c80340340d03c1b6918240200e02040e02c0c9007040b110f00d2007042e02c075070880740940700c0841514140840d05181170b48100342481d00e480e04184008019030903000d01c2c0106010041c5602074640007d00d800e03219500c1c0e040b41c007801c140202584e2200142000601481040305000d580e0f003100f001c125134a01072031480c03540003101d00030a061040f2648000c24000858900e10b0318160150019031040424400803c94541a4001103482c10300c03158002e5000040031141d8085814050421580a0070605207411515075680104020540c40001600c0c0c9004042088507801001e026989d045146004406d04081032a1076280d124400c0610b1601459541e1001c506880b00703241c03d0b074201c0385800402a20030301e003400d8039101500380944014076032a8000c00044603076000e0030700300d074900b08003815406506046a0a20006002c991010341d40202d10102504010004102030f0711010f20815071740c0d072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636634541 1250 636633291 636633293
    0x20070e0c071112280b01031401150501081602150106051209010b090f0a0e1905011803082e063c0c0f151a0303030420060d020309010504 60
    0x84580e80c2d248074821980710b41d000224480004410314180c081c12400e04c0c54aa01d0440382c4480e940480000f40000c1141c00008240000c400340c0c02c5c04c3c0c60101d4000e100304903128040011020480c02400e001c640e00c0c0c000300e84640c0c030210f00b81d1840f5081c2d0044481045035411079551358003090303102c803000600000c2c0e2905140c03209540c0c41c2d01306900b103000f4402c14001308002140c0440092680008680c0d52002030041d002d190403048901c15444269591a241c007003a007012030005103400d81c2c540d0f09010343d100c04c000c420107590015540640d9038a0164903a4112041da0008103900c0a048641884000c1c04514039841040d005100d55240c1054404110440c0042e800202c1c41407200c0207000a0030030b45244001d0115007120b0f5051800a40300740382494140400c400c901c0024141d01c5420030012040c2c0b1150f0700c0f0386000700900326120340341140081010b42d24031084900401e482d81811035441e86a2400002e8130a450303000300b41c141000015020b94040303130402c030344e0940305039142c10a000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636635791 1250 636634541 636634553
    0x902091810080706020601140f0d060c050d0b06070f030503100810090309080d050403033005040b180c0d081c0f050105060a0206070806060c01020c06040b1620070e0c07 74
    0x40f0041103540040c0c6829890704c00e8052079680950f00342c1d07008200070300583d2159541c0e2403030700b0340d8070341d00c0b0350100000d0310068401881500206190b01040e0716241100c910f134501f40e0240c0d441550f202c560149020f459680449040e080a070006044054410020510b50800e20101d0031122021000190740c0b00340e4107009161540756400003002c0d030440318601020729032050449069031b800d418922420b5944016085018640c80440100581800c42c1d8666000541c0c000c1d60085d40150581081070b2030301d00440c41d034000e54a0940c2c08592011044907880d080019185009a019080d043d04024200c2e24650740c41040040c4070080700d5403242ca40354000d48a101e0340340034003c01d03a103c5c0e0403c4100c1101960f28007002d441c40051048410000d040c9641d0f40c42207403c944c900c007009644a0700b00341810782e40d038001510201c6030799140100040d030029000030001310070402136031103105000800d40c081c0c580b601041d02c0000980103004000c603444d1520310f165809003031000c2d4080d90b9096941000c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636637041 1250 636635791 636635803
    0x41104141309050303070c050717031206040203060a050909010e01020c060103030305070503100303050c0703051c020601140a0b0f070804060917120d021305030d030c090b090a090209181008 83
    0x203074107091514401001040b80081a06d9102c07155080c02c8044015a003006460180344d5400310440c000300324044540170101201410820003109010b07031075a1900801c00050380811145107400240c00b040400c02d84c41c1201a00d5007084480000044c09042c14040c1d0f801c1e648035480100d2164080c0c2c00420406605218541d44151540b40030f40c1941800f000d070480020292001070100301c4041141004000248401c0300150707402021220340c14008034215106111040c1044058021440001038100c00040807103540400240010f5210b1f041880d42d203c00c0e00302014030030304d9410500c1544d00180c4640004e001802081d11001c0c481d521302443d003400e2103100e5100071860b070801c1c1c6003a03840440388401d030350110081741d1025840c0c50115078402003068071544110b5042c890341c80094400c1d505a40301d103001c619940e407966042da8492030316100911030982500e4103c03104550070406044654003412200030020210824401100c502c00ba01c404181c0f00c000045021a1040085000030004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636638291 1250 636637041 636637069
    0x11070e100905060108160e191404060f060c1a04051c0302090102070303081305061509010b160605041a07030c0e33071407051003090f060b04110414 65
    0x18440d510f480c0c00004c082d480082c204e040344080c0c0007170101d440350091203084039450340500303100310f4103080c038001c10001d1445110309540e10000c405080300c13504007805100c050310f01d044201c04c5054a0520b007164814030104083c4c41400049400c940400c10600c20a40100d001d0740080c202d0040800342c0450580c4130000b0300c000d140c410491005941d80118215088a8050a1080da05d0361407045032505400383d460010b000340940010003c555019004d07411545000351461401e903a00c6034620301c1d941c8030b4402180c13510360804600034001240d54105c96813092040d03001c00704804600b0414103540c0c3d000d0795513001003615491101070580d807026240c18140d404980425089442c0742400c2ca03c0c0d10390030b400d401024102e0f060b00e0b42844014003101d40c6280d01000b55441d81ca4400a115140ca1050140510940d842c00ea00c1c84050700c40d0044440c11904404905209007580e41c4110080032014035068100751200524524446000080c000400b14103230400e4240001508201042130704242e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636639541 1250 636638291 636638309
    0xa02070b03040f0609020a1208040815010501021e100219020c0915010302090f0307060f08060103020f090d0c03140706080f10060c0c03060504140d030e03030a0b0111070e10 76
    0x2000003141040c807001d56284e800c9100000c00c0a0320340080b0316401410b030032207038007041d41844050070049460001c1003250588025100d2083d03d011408a1584007846a180168070280c8101c480c3d80d00d100d02011320002000c00c9074800708400d444c1c44182d810a00c0f42d40843c803c4218048000b0b82c061207407200d10340b03083303900e0903080c078010007102d00c0400d20344d040504142e070114000d00503490350300c040c24100364000d0132070b80190780da184014020a2603020b0000082c140c04c3c003180882d40030340261106050301c0c9801c40c0c200b40300b580a000f1580c070070348420f54210210900010104240740384203003444441c0c20291035000d042820140140031701070900b14000024508100111131454054015104c151401d81064860f03410160402c2c1216080605100d242c80c042c401040351000c103113a800c84104058138440d5070005420745c01c44080d40c4a103d084d170010000640849220b03444141c108405040078a02c205005040d1071400f045500800d44003000c44060006100d840d40141d401003075210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 636640791 1250 636639541 636639547
    0x9080607050403060b01022a01030b060c060414031903090f14060901060f080304050405070903171b030910050306040906020f0d110c030a03091e050a020a090b1804080f07080a02070b 80
    0x1008d8824514a26031a20382c3d040c0046407007510307038481c0d00300c83e00e41c910050072680c0718042081c006881d81c80a59044a4000045010364110071000c0180ca5940315098440071082034042010f0b0003415503a0002c50340d04002d90035410000d2200d0072107001340c845c104001c001c80d1a009801a0850f116a001206041385c02d10303040144c1c010010880e02682c4e0300303890109850701d456005440c800210b400003820340350042a40b141040d0020b0141504030302c405004420020380d00314140c0c0742d00c11200d066411030b41c1e4000400b5524024001035400c03000103000003c0108841c1c40e03071400c0360843c0703400e062040000521012040301e240034600300c491055004038600f41103200c4440d42c9109200e0709406044d124070141040c0800800000301c809084400401d840100346400b40c0c40e0a59003600f24460203e01d100403441c2545031080800e42800540b042c0c1c07002240c451040d4040c0ba008004441000040101700e825200400103449000d210365010303510f542c00c03903001908140040e0400381ca90382e018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 636642041 1250 636640791 636640813
    0x23030c060408070902160c0902130905221e200a060906030510030206030f07030e01051e27060a050703110726040f03060605030d021c09080607050403060b0102 70
    0x4940803048441044c0016a50300424014510b209109840601142a00070700050f42c604e40340c00070404a980e140c00804110348455038001250b4040e07070080d84074400d8900142c92520625000b8510303a0048a050450b0004583c1c1080401d4012100321206540d014a01200110184040e8807104003103810700040c4c3d040c91001040c48106203e903004240d164000320318944151072030b20014540280003d60741780f03000350180f605000c0540394080080e1425984442085c8184546402108001e00c05903200c07811150034012001d0140680c1501d0f0010104040001c040a1189100c24182c02c06000c8030304d01b00c090710080f034000030b20720f8040c035040ca8110b10b0f01800d210704460040703a025140340d400360b60207038000c01080344140a6040d001d80c00500801d2103518048100100c5e0b01c1010180726075501c0358141504c6a0f20341010001503480107604c0f80b82800107038501c403458030301450301401c05a581d00c1b00c1403508100365880340220300c00103002d200f4030540380110001c0b4138082c002803850b0714074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 636643291 1250 636642041 636642043
    0x6090b030d080714090a0f0e10080c190506030f01031a060a0501141201091e11030a020304051f05060f10120c050c0106032d08071b23030c060408 64
    0x80108000c3c2008101d203101000c18404005482d04e5000c0644540749071030b180c5620303907107030b9010b4040d241c9803c040c240040c4050452311492015a12030344098210008080203000f501d5050134013400280c45202004100c0703860700707000f40d40301d014458041006545075003800e40c00b9015140305c5600104456082040c036171038030200082140d03800c0ca442940000c1d07114960700c5500480b40b60160f141100c0300002801c10139500041c500807003071003410401c032000c0703165501200c2e10820000d02034002031000070a40b4249601543d4005e000b542030b10044040039050700d07a102100c444814071141c1e20f106004003824a403c42ca018201c0c26200e10070010050030010301100c0040d03810311070113a180c40c40380b80107e104000707841d895020030313000303000f03075a100c1c50018910744102244081c020418400310a82001c0260f41042081e04420b440c0d2414446460345030310706003004d000c035621209171540081e4000e0084201284082090b26252004030180201400c0852000c240c2d0b10500c8240414001c0b030b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 636644541 1250 636643291 636643307
    0xd052a0a050a0c05010e0f0606060c1b0105130306090c0b0c06160323190203070918140708090f0705130b0307030206130e060102210904110d06090b030d 67
    0x903440c1031060301d80090000480f01c0024840c3d00501c10350801070030a00d100c6000800c42c40801c140026110665102400c1c0302d69802a60340350034503a0701c4681d000c1d00402041b0841e601e21a03040c0341c84d901d000b100c00070524006005910485903d0307524091041404800300d0450060192810f50138a024520400617030394450103044402c5040b8400525a0304078040d62040680c568252899500207085610320300c0503a50403152500c84007000800c819209041d032080700d00c500c40316202c0003003a90428000700c540071203070f40b40f14061030342d03c10308480740f44e201c0d07030000e841041641c0c0c5140b194904040d03820306040e0084500301080c3e1124034203000c55900c10062401c030b0f4040030800250f110222000030f103032142ea64000f0703402920005001c480014403004403c2954505002c03032900e52908230049945174a000301c164a040e21801030380010074900f60080451000090010881c0000c1da8450b03101030784400980f100265980d407040180c0c1c0114001d040004900f140030307150358450140c011340046 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 636645791 1250 636644541 636644557
    0xd0c03060b07020f0d0213020901081621020c03130810110405061c0c032c03070605190c0201060503070906030c0b09011e120501080309130b0f060d052a 67
    0x1604800c040c03690786401c0d217441000b0350002e0080d0800c1c0381c0750144000035808144030760300260800740091040700070f900703040b20b10200e80d546600b160000000107201d402100800d40081d240c00700b01070501c0a01c20005044280301d8004500c16a03032511003851324013440b980c00030400c14280070000300701c040000107030f0302110b00070354149903120b080115680d005074103000074502079450044100403480d815480241c583c42076036418200ca81c205100c240001d5800ca5480c0380c154800c200440c00546150484c540101101e0080a180e02c0194030381d4049d07540b032a142c3c0c00140e5450004101e1454100009030040c00b501c0c3c01003100303a0071519250300454690080d092846000104824164850316481d82401861215240b0180f4841c03801406170780703880c061a000380c2c00c0000105202001108035070302028000d003102c49240030342088502808c5650070312039103c642600ba44440d5100c3c040100301a06020a0000d4240303444490501d01e0380342c846601c0d001202800710700c1c0c001e60220f003c40c0e40c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 636647041 1250 636645791 636645799
    0x10f14100915090f08010b120a0b062205040b0906010b0a09030f0201090e130b0105060c1c0e0d030203070512071211030405040f05091203160e0d0203120d0c03060b0702 74
    0x40b08580c0161000511680440c48012002500046000040d800202e0383c0344200c030810244203081400b56aa1000d41401070107400052000c11018903006c00420803030f4200600d0030845040141c0913904440c01100d094413218503040c02c011032400107000301c2d8054030400c44c1d030034100000c2850007802c0d01454000100709203d000758002c01e6a015044074030091408c4c21000001d40381002e8012121391504c241240c003a44488008111464403605403200c001d03025009003188511a081042030140f400c4459051080c00c04140b081d544409400044403402500207586c0d82d8180d00d0114030b08079031f8040141e11000140910310015107103848269011503245820a000f43d4905600f509510032580140d80c440e180a032141c035800d21a800591242c0c0c1e0501c00da41c0b01c0c4c01540c010b1401480112007021503110310110f4071180034001c10000c0e109800151918000744007175400701c1c0c58111011105609400d01180f5070084041a00540c000b01c145450140002d82c0703130201c8e1600601600300001c0c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 636648291 1250 636647041 636647069
    0x7110708070509100b031306150509130f05030a0f09090b03031909090504121205010b0d020a0c0501360201120b01020f0d12231506070506010f141009 66
    0x9071000c298000025001d502090b40e580d04141c4414109440e8000c0204c0b00c2350304003900070329040740c1d5512000031510701030118001a03940285213070b0003544000f0201d40f581d09040320742020038810000781980c1c200644407034001d0b040c0500064028500352344810925810400b0070402514040b0a8030105020044404081e0307901100a0b200f65401c0d400a1b20744914040c108014400b0006801618110f151590209001061066401d8860034011a007980300b00b04010700011016900410800803546416442006c281c2c0d05c0600750750503843c80385400c00181269020000401c44e920b69210b0043d100460388021503070002c1c05e4910803c00c26690302d0381c0c03468425040d03402400000d84c242070900c10395088940004001e0300b41d504410004480e0f500e440b5889801104844c0c1120841d4008503502c901d90ba03454210300c1c03090740b00441c1213400070002d1180300c0005104101c03840c06005074403e0f28010038108195036601b00e5003521f07010701c9620300c07440c200c1e40d080e000f8802c1c50958000e40c180d140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 636649541 1250 636648291 636648301
    0xf110a0c080c06090d0f020c0a0303110102070c170613030c260304061407020703110618060708071a1303030e070522050c041a180409060507110708070509 68
    0x40c080c0a00c41c030b1a04a03010b02410030469520120320380d00701a13080d8881d1001500080c00499440040060454001c840c501061011038007580749407050042c0c0000241c0b4002e2965114041c49110364860244d444070a903042c104400248400c5a210000881d1090b251140d51002040552f012a02526580710754140180208032811441d100ca040540090754a051a1400030010401d00004101d819000c1002ca560b20780302050040403031380c101c2d207444103d401110800c910b5a000d5001c000c3c00c0d603042c0c083c0b00c01b5502e882014090b19802101c1085c1c4600f954200710302d03155402230a0041320a00c0c00c0800104003540c1e843c14101607014a000034581c1d1843c40340f01c0c81c3c40f10607000300390f003d03001445100700d41000806020130b1010000f000e100710f8840d807202900a000e28043c1b13081090350b201d00509081102c0c4080c000f0643c0745030300080c4031600400410111240004107941103502d8408010040f0340041100440b21003800007400800d10b400600750b210b112502800b4030440881e80810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 636650791 1250 636649541 636649553
    0x308031905010b0c0d0f020a201c03080c091809010e06150301061208070b0a060915060f08011503020f0d15061e0504090e010e1f0f110a0c 61
    0x425401611001c10140d6103440802c69a5003141500c08002d00c50b013107880d10302034443c000c4c1902020680e0024040710199a40d014800890400c1e411058280b255107840141c0d5031004d0364048042e102e4104c5c07501031407400d005000c070200401c000340500c42048060b03d81e07220403030000c40c4401040310075078070360f02c81000d0203014207541c101100c5584074280501420a6043c40c64203ca82c10440003081440d50316400701e008a50f50100180c10b03031109002140202c3d1000c840f203070303005282d000c0c00121151210b109108507950481d000c8040d5640c2c02d0207001c0ca58001c82c0381c40119142d41054003031903142c0b120320401006100d02c403104058000c607401552141e60810b131480170050100901607034240407000106000d80713114a6001600320440031030841c044100e201d001c44960b075180340c40d060415840340050041010f6030f045c41d42d40c80503040480d40d81170082c0b10207071800e4a00e004040038010a11300503030b9139184030061034500e040c3d40381810729801c60480d4038a1861303007040074080619003410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 636652041 1250 636650791 636650821
    0x2060402120a02090c190309050a0609031701060804030e0f130c03111c0c110604060c091d06120d05031501050f040905010810050105030a0321020c07081b030601030803 74
    0x940001e001e40c2480340208410019003000c0c6e141002c10b942d510f00c1e146045090321510307080030302a070f0400450307100400c507160441c01d401802070501000240d5444080c00007014241e204100041540d418801016400316115504036400c64144026084200014020034485103003482100d0f640c8900980280c0a07030400741046240c442d4503a1244000c3c100c202010701c4c405a52240d86107000540c039007c1e405101d0319184a10040020030050b5039a54849004109000500c0180850040002120301d000c8481903108550511440c1d0241842400d200912011802c040c5881d00041e48031221233500c035098a40c0111005900300b04c40032070000580d5a88103161450f0f00c00e29000074081042c0c80c031600418122400e103000c4480c00900200488200c0300c082c000c07164950014041200802d101d02c0500c410002d07001007022110507542450012a8400003250041d5005a0010000c006007880400c00380306064a40c0500c500c3c8210010791a420140002803020034048045461a0704803090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 636653291 1250 636652041 636652043
    0x10305041104020c07170a0812130b04060207030e010503090d050904180309030507050a030f0303020901034d030601080a180807111009050f010509041103091002090102060402120a 79
    0x308554540300400c1550305d82180e401050700c45d0030814443d2828010010f0080481908817031000d0400c1403048441000031000340c01c41d0074954449010301e002c21942c2120602a41c400c2a005035514510b20300a04032011300404035041c40b80900030010308800104410002c0d00052810568808080000400400300240901d1000b5494440c0b107040540000015090ba03000300b00316840715945400308681d030354180c08002c208030704030301800000a0082e005011591014100420342c00300e8032801c1101c00c4000048402d24001100241d18080d0103d82202400350502c1001d4031306aa41141d52a800c1c400904524104030415001500d030720410f9200c45407605103035401e110f100360715081030546034016a00a66244080781001d11962806a00c0703066903030002e8469000117440c140c1084100ba044403100f5041c03000410401c61581d0b02c500c130b029900091084655102d0030003105880c03401001c0c9034170201a51040119280e60380c0c00103411030384503504903220003000e1500150302d400c141c84000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 636654541 1250 636653291 636653299
    0x230c010f0201090b0a05190b0a060318061a040608030906120c04030c06031406010f0c1b0506030109091103062a0d0c121b0c02060f190201020909060d110103050411 72
    0x2402079402e000c2c0c0025010388041d200c50403511034840400000c6801d000180350380312704e40714030800c4070324043c1d0081d82c104d80003074490100400481e16403000752142d98480418901101000c030003d07140c40e104103000303806060011410900d24801245085c40351001102111501d000010402d903c003100b143d001d035502011942c2d090390340e01c1020b00548181994850041c902c10000703a41c95200340070424000c03d035030780d644415078001d840d052107100300540142c03240160b000000c1810f840d608000d60003403c40c00c1d00000d44071074508141d0055515840d032288a900300703005002040300c1800300311855404181c1d41011021001036044d00511030f4071142e40080b400c041c0c0d031000e1181c01850202d60903503d08410f0009868880c1c0c02a0303a01d0103500a400403519054443e005410110050002652007101480c0381804001b1061810900d415060005030340004400a003401c040d024030f5000501602d020004850035075401d00302c860130481090406a5a60010b018085070398115040200098 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 636655791 1250 636654541 636654563
    0xa020418020f190206090715081906171014040b0f0c090a09051006050408072903010e011409040f02040c03060509011404050c090102060105060a03020403051207230c010f020109 78
    0x54000307910f07085d00319406101c0340142540001c01e1950040c1c906d40f1401b840c0c0c7c40050a54a803074500502100340c07100c01c0c42c1e20350350324004a1546181c1e0b00301c007824a8202700409500c4a85141c0d5400c2d41c03000c0201c4500341c03141034240000140185d140742e0b002501220101141d556480720414103002d155061a0301403e4440c1c005241071007076200346d010328000c2c050119255101c140545141c130a91064202650200004102e90200d00002c240751a40c04900321082c10340203400340b80d890f002030b009891810705941c010049040b1000c1101b040b94426200303500e007413805031508402c401d030394103001cae01a540380c500020b00a4420341c440c0000c0c000082c060012540c5034802022244100342d480d6018604d080081610800400c00303640a0010590041c00e10ba03080c841840440e0704405845401d240c2c085c000800021024001c0d4400e015412840f035807180d645007800c0340310380b040c61a00800003141d007990012101c00420202034680d002e0800c51600d41180c070080340100082c010141c86070701c040e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 636657041 1250 636655791 636655837
    0x9010b06040b030609060d030f140d020406090512011a0108130203100605100c050703030c051507020d0e0d0c1a071e020f090903030412031409150a020418020f 70
    0x1180146009413000d07501402159101014401080c190641c0500411525002010361500c266000c07480314420500f69814014102c43c504181c1e0003035007142010408a8905014078201100d070b08210080307040091083c04411038942030451a82c00b98641000100c8000400840016a040009560160880b0320000004100c0e40090056000d0540300b096006080300c1c05d0391141c58000d030620741040203060041e00d5944c0c15207884612600c100c82e2405600b4040790804c41401c8098802d0032103401a120410074000d000707114007a601b031103a00c130700000d800540215044000203021744400b01c1341504442e00c010340001c1e8034000c00b1402481c9154800c03100015030b800c00c049805980c800d0711116034079880750042208441b802c4514507256442400041c0101d00041403101da55286030500040f4030f404503046810003c021070340a1900ea00044141d291850080d00c4540d010224007011400c0c14105542ca41088581c0001c0002c00341c0c011071030f40d0082c0158400c44010359a850340d00800300c235403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 636658291 1250 636657041 636657059
    0x7120c0501060518060d03030e0303040302060603070b0408150606190504030b010f1d04081225030b031207111903050106090209131d030f3f09010b0604 67
    0x240011a429420302c07200086a04045815901d1140998201d182139501d2505212554043c084140d08240d10341250000c000d605200660003940654050100c62030305505061520f81554003000040c2805c2004000c07a91021900000440d1420000000c540300d6000041c100d0144854010f081548090f5112845801c40020800c42c1d1013920714054580e65090306503203d5505120703509026209080328242e91044030703481540544650340b240d080800300d0760002500042120942c8aa1100100d0034610704d1403c001c054202034186000d0100304209804291946003910b03031071002620104050040091a11010b40d0800b000b03414400ca13105030356200e528000c2036100603100d5518104d0003003030200c0b850086030300b1260b014040c90140c031060b07812880104100568022400000c54078a00384c0714051000b80f0100b40c4102c401900c0d0307241c0d000c41110b01000040c0d040c82c411008244290361054401060f26109008000e101940e60380301c4045000d071035104c43c402d0340000d000401107154a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 636659541 1250 636658291 636658307
    0x5060408010f06151b15050a020a02190507120c0b0c010c170705031b091002010c030f0b090f0c0d11070b0c09012001020c01090c0603050601050f03070e0103020712 72
    0xb1122400e000e02c940c0c51008000c68001c0741e000d03400255200c1c4403414803054100c40500c2003441420156083c40c11407680c5030480b43c0903911709010b103400085408801e941004401480c0c1407111101e800c1e5a1182e513590f596182d540b107100d0200c08120b10507418000b8002180d0000c0c8424410541d0326010340c1ca040c6d0081940c000b0301030206070342c6007000e00704030b0070440c0c0903100300f1050721154510744907080340c19160090304c007801108038801c00c500407442d102d8802c4680b0b403169507000030910002d450743c040d05403480002d048000700e1030010034041c1a560f2884540c0c000381e44011441003034440303006101080c0718845850b040715007400f0040710240c40703c1004200c01070248488180c0c80e22141c48100e020f00c514859940041c402118407484011f002c05803144501440700010700d03080c0c09103201400e6940712001070743d460500100406c00b180d011b014450f03220109103032803840e18020030940c00c074600011300002d08001c49503100c0700003640254120307641a600520350088041003a140204444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 636660791 1250 636659541 636659561
    0x91715060f031e0d0c12081503010f1d0c011b110d15150803030a0c021f0207021008010b0a0302030a09080309062a0715090f05060f090a0209040605100506040801 71
    0x220072504600d204c58419900d0240c0140d01052105403a803912908580c100805820040b180c82800d01446283d503091145c1038101c1041c18020420096029252910001604c0149a80d03000a90420b04aa0740140030701c401c1300c180004102c4480541c00e200d860f01c0000c00e0030300e41140f0407001f00c00500070750504251040034010300500c40c0102c010940c1401d68103e21600820b0340c030034404a0030840007900a03440c0420540304035883d048440d08a4685600c0030740e041c04119600044510660602c0e1a01c0c618020303203400c0c0002c040d490b01e01106598400e44000c2c030101940071020072421f1460340c105485594100504503202d0602e00f1490340c44440555004280d00d000035540407850440351440c0d00300d6030208071b005040c2520758448002c0b110980d80002603003603603420703480e0000b092031000c0c0207075a010308000c09103403900325a80842c00340040d22201c0268046411440103a03a1010020340c042d40c0190081056203648510000b280501d41140d5844032000c5000b24062005610807000d40c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 636662041 1250 636660791 636660793
    0x21c051b030c0304380c12030a0e0106080606060301120809030a060b041a0a060c060612030e0102070806011a0703021c03151a030406051f0603060501091715060f031e 73
    0x11410b160b4502c07107040c0161704000301d06415910b40c07030040c00d80001c4e2807071001c25400c0d104041446440741545a0044420244d007550703502d0601a9941c007449218080c104480051a0601345a0300061150105214940441a02506102c200400441540c0500a015084400d80c0f00c1c1e0346465000351581282e56802513103482201d02c1e00d03103001000c05c8450600600b81d80032031410020100d500241420040e1a125100c02c00042c21741188424008541c0c06980c650f1580310b082d800080c00c02c415030303001022650094005001002e2803a003010781a8400d804510b642d00c045160030b0b800d041054544014000c0d00845c44c900c0c09805801001803030054990125000703445600c002c016945000e40108261000e00014000070115400300d5003010ba400b2104d0480380440c64104805403054201070000303502c0341300400665810081c0c500240c0b08440c0050710864402c40c40030303650341c117070403c014402060704003107031a54964403489101d001c00901501c00004100039030107a44069100e1801c16 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 636663291 1250 636662041 636662069
    0x4030b0708150901030311070503150406050f0108070519080a0c090e0a050a020603070c0b090312010906050d0605071407081308031c090812180d021c051b030c0304 72
    0x21a20045020b440780c40c0042280c40d150f4210746040320701180c41071240443e40b14158020829a40030400041e50413110103280c425032500e883c2460551700060326122207104540d00600000d0070100780f400c10f450742680d21800c0319044500104072700145500054050082260306014804444000400d071016044184503410021020b035550b6002c00d40064655080010030348010700e0030200854008207903181050181d038083e25022511031043d00c2c40481ea5100007030303402c5c64004000d6641d00608012004011082c03425001c16612180c000c4014216607a4000081d022409040c095103a0740c2e05a0345181c50b1407030b501c2c28210561080c0d9500142c00714501000072044030000c01c03110540040c0c02200410081800705001600701c44904890815080c41110b000ca02810303409489407400000d0200c8144210346020304190301c1c11442c3d402c640084007001d41c441102218a00d04034624580380e9507502c5400c8540f01080112200c2d10258000050f085554050000c041d01c191240c420110030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 636664541 1250 636663291 636663301
    0x90c11120405011d1302041502010c021f0c12020a0203070212010203060d0f1502070606060f17070e12010e03070b0c030402031207061d061902120a020310080304030b0708 75
    0xd464000d038400c40d40000e81c80701d0000b00ca4140a840c054040c00040c00c2d40c503580c041d0101c804142d07002174001c0c4811083e061401c50009509016151201c2c200d80003400103951181800c0001c46134200c0c3c0f01c0e1700c840c1c68401c982e5441e44100603000c00d605290000b1500c035141450004e403a0343c4141410380c41a090f0850307030725031003106100b16805400b0003041030819403100e40c1e071140c41078140c40d020b4078141e85184c821019094680028901d462080b180005d8290402c030f0302500005940700701c04104141441c660b0402c0c0301902480b40c000c50507042c0b40da00010100001990801003400005003035003403103a241304548001014141403440350f45400d1495640022441c031074041154065859444030710f0f01217045004400614420380900c001103412801c0108101c0b0714410344020087e2030f407104040080c0c082c2071020559043c00014025807034a102c0140250500c1b4000c1c03d0022442e41c000081036440d41080d61100082009000303403a104c55032800e041900400c110307010300200b103500c0d00141b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 636665791 1250 636664541 636664573
    0x140307022d0f070810060e312d050a1506080304081b33070b100501090801110d0b030304050a0312021c17220b060f0108090714010207090c11 62
    0x1074152a0705032260101c0f40e84010211440310301c0924211842e0080702124a10716881c0b240c0345009900a41d400d80c1c0c4038034240c403010a103050751100a80407041e4a9192800104081903214800303410cd030703400c0c00305038004d50403030f000f80081d51151100381300004001400d41c03001301c1c0130400c0203140c0c2200a0031141000074407074a14015058900004084c0480d003d51050384803c40300c0409007210340034101305e89135031025800001500c2010038003802d0300c000c02c030661303200f0948405401240001d01030801500782d5200da41c06503110142440380c40d0610880c4603202001610700400004004000e070341d41e01e041c0054001d2101c100c440040c05042c402c58030840d00b1442401070400e8a41c1c1d0440703010f0041c0b110868110001c0c041d1610742c202040c894090300c1e8079550a0314114041e1200c1085401d2500070000c1641030b40003841e05001e01d4400300400100c01140100444110341090800080a200102d0030281c00b0340141c0c45961a100c1a005c00c2a40190944400040403086408811840c0c1c002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 636667041 1250 636665791 636665801
    0x1412010c02030409020d0212040602090f012303040204090b0f040b0705030f01030b092e180507050d0609061406010e03150112021c030f140307022d0f070810 69
    0x202680c41000200004043c950040440f207000308401820501c01051101d01e10601b550b003034ae1890380108a80d040703481e00c8291040030081c00d00303204541c2c240d4004c0d110800c0c840c12011030385180c0044001030a548607900041c025035401000381245142c400d4208941000a40f401d45035120240700248206014804590080950f0120401d542c0c2c0b03142c3d100f800841d0014514041c60003981030380c00c001159005079028500101280b071034040d0f00f0ba42400111281c54490071040101c005914004c210302203050f009a440917101120485071504203040500160b805c024039461030b02c8024146201e030314560345c1c09140240e036100c0091450108050b0b54094818110b04640f6a02c1d004200b039400b0320344070310720f44c0e48040c2c00201c0c00040e440d04d201d020201d64005602103800344500d020b01a900c10f1a051200441c4103685056040003040259646055940d1740c4003070548070259403606880340d0840c0700e140d05081c202c401090090400301d884003214407400741d080c4034020f00895904940c0c061 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 636668291 1250 636667041 636667061
    0x31409030702090a09060e12030a110405130c0912120311070c091d0303091b0a030309090b220f0b030d23070b0f070e0405010302090f040c0906141201 66
    0x3c2a44140c540c0d14820009000c80d00046804a580d10042080c805c000d100d00c44492207182c026a4891400314032103420f584900c103280140300c10401c02400103a0b0f81c01e801c0844031003e10f00010308009805015141880c060b000183c101800c07140c18070411510085084031900281d40030700c101c282220b01107020703005203c0000e0800001c0030042c0604079850b44180f0705000244000c2d200c8008100e40d00c1e0a580c4241c82c0061580c001170391139103072007000b4181000c48104c01d0310396101d8117113951002080051a40034241e41c60783c8603a0200010b42c0c8102c203080e0784400d04121a002100300715054802043e802140d01c1005007800d180c0300103850003090b0480d4071079154032030b0091140d800604256500311001050042c42c030901243c004280705100d540d200d504058036107440790030180c0e0b0282865000e81034480c440e0742850b0050005032101103071079400400081c054010780c2c9440c03030b00c2150004950400b4642c0c614208000412000700492180e030014181c1e00000d19107015002c507420307196081c0d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 636669541 1250 636668291 636668299
    0xa0f140306042a09051002070302100315031703061011030a0c06090c1d061f080702070504020f1201090b0d0825030f260a2a031409030702 61
    0x1002075001d007410382003807a0304030400b542900f01c03441d440d03802000840f940401e400050804481844a4200401e140f014a09540000c06a05296500007082110301c14103140402d81c98007070300d503292105109103074065580310aa00e00d12402d01c0844620070f070811507606104441c89104d2200f04c074004d010002c80200c907000a03619103400007a0940701500500d600300c82a81d624141d40c070109002c00b5225016102031b02d41f1082081c41c1a10b02d01c46110040e000030302c01c405884c0f0035412504540b51104c190003441c01c10050340c1d03843c6201a401c01020b0f40c01103070001e00000302d03880c0d101525001010300c0d03049840499466600e03000040700300c03024090443c0e00304940c0d2600a01064159001d042842007141491210440c640c41c0301d04450003141301100852408048045101d4025003100e01c407500c03500a1001401402101402101c0080d1840c680c2c3c9558450403c414440b0f01c80081c0c04071001c200c1c2400305e0504103030040007000002c04605004a0714004921205c1d40841200e441c160010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 636670791 1250 636669541 636669547
    0x50402010504120807170415050f0d0b03190b06130b03030d240905041e0201080402100203041e051804030801031e020d140607020106030f0f03110f01020a0f14 70
    0x100715846000409003540c44e090300b8450000011203c1001615051000258640381e80c0351818015250610315241414018184501001c494201d4161a6540e034120350100d0410b000c0408682055481d040859a0780c0000728100c01340b103802440e442c043c040a407050311828044548100c00c480401e003400d5071641040004845c8110309070404103180034040f1619004803002d841c4144646455480284080c0c0c40e030b0104001e00c6207121442c3c80400b0f40c80345100401303400d640002d102110080c002840743c461000e02e94a00c03813080003a02e019007060726003400380755001441c044844e2118070071f25129140b61040e0502c2c4038030344040c0b94091a8180c54400c026401c0da0703101103181c0380a101100ca00b01c0011100c40241e60307450a041c203070314014801503d02c03441d031820550070914000d240700150b81c102032040001a000d50041c5d04e00580060511449040d58607040359a15405141da080c1ca00c261003402c0c100001c19401400c440805444038100b95000240680c0c0f1059260640b0b030381c04d0024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 636672041 1250 636670791 636670799
    0x31611010207082512030c05190f030f050f070b040c0501020f1e010f1e0501080c030718090b161101050c030c1c020f071b12022112120a050402010504 66
    0x58284034406000024680341070340e0311017100210b0084002c03001d0340012110305110b070074040d042c0540d4600c0b0100a0b0210201d20035078071000359400c211800102048001c40f40c1c00001c1c0d01c601c0543e40c1111003a1503c640d02c5403117050540e008041908e094419800640c0300050b03a60001860060a12480700a0070180400340384103c0410801d00c00b0703620a540318000031003040340714401c5d06501415103249120582041080744100d4030142c0202e52540c5c8081526440d079a0002034034030448600703161115070030720128040310140490710001000c1201b0300d81401122100e02c100401718034842d54a4030510704003030100710309841d01a0380141a10ba0300700003040034841c003c2c00605441243c4008110720303c0c440b0705040c0403a800301503c3c05d010303800401c401c800c01c0713151110210100725000c0c485410605180310541c940d400c0c210001c0c40b620b803880c807000f0184403041112280080c0c04040d22080102007000f50021307444500d00c0c0030325414100024400b01e180f0320a20340903940603502d0508150030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 636673291 1250 636672041 636672073
    0x9040f09020319030e03100203090d0f0e0d0314030108060f0c0a0804140102120f0114010305061e0a0b031315090c05040c05041206090b0f0c030406020f0c03161101020708 75
    0x1580e07500703804101042c0704481701928104a41c50501003141c00050343e0b031070926940d50070300d02d440e00c800041100740c0354282d201c22361005400d00c00060888517074841007501e21341a6281e6610b42e04003500d0401c0400001a441c0000c1400b42c070510380050180d81076641d50150425a01c58120b000c00803a030920089804625000b4001085c3c003000e030001868030b4281c2e100d024491208031100c1d0b008960031001440400c500318209034100f002030a00344006c1c24864000f4080c402d800403806410042031207442003590b15010040c0c0202011180c1654034101041400f6804210020030346120700d01e65408150ba40440c411500402d82011518180509020410019000801c8240d041110034400440c40350142103120b05554072403100020507255500d00604c000a00038040506c8503508400c005025000500302c039442980000300503074501a28101e616107000d00f9036040c085220106030311000e48548615800c02d14002c101e20000d5690309001260307200041e019541c0035400c403210705005402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 636674541 1250 636673291 636673333
    0x4080a05070f061802030c0103060608130602040315141003020603270f030c1005070207090b03010612031211030106050a2d020607120b06040501080a1401080309040f090203 76
    0xc811114000990b80580320701c000d0769101c84840002c0300b00001c8901c1145030820002c04509001e0074103001117850100040c0511030700030004200b03940c0b50300740801049a6941260302440d840703503482041c4150062500003d050281515139401301d400003055403101403014490840f980145034514550715450a500c4104054245480d00c030f03011002400610780c10721801d02600d8906d801580c8804043c4101840d124043c0090056145080b0a21071780c2c0d50b011401c03906540d2885000b080c154564000300e4014651680322440000600c03680008042e4020f05c4140e01e05850b03c424011040c6560706108a807100f8800c84021440410400020a008005481038408460b003104030303011020a5610800c180300d0482c81c0103030800c0c41000b803150f801101c102c40c81d001d6403c0410008011502043d81c61245001b414140910000000c01c201c08580004c0380400511442c85200d581d250340b416642d81000d55190721840c2841a10b05182101e441800712141c1c0040050500801c207001e0350640721 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 636675791 1250 636674541 636674543
    0x101d0d051c050f07320a0b1e012105030a0906021c02070909051216030813050723041104050307122102150f07030509150103150b04060308130b0304080a0507 69
    0x50790403c958080d02c05e003055801c410010700070705a46403103440c2c840d00c00d00c8010018482c3c0c041300c11640d00c095070f503000454152042c01c4e03624000d03a484201d07148070748401c4080040080c40001614100103038005031100441d28203408807048000084000c2400100002c81f600060740441e00800114140340c119942450045040e9011912211400340c12603000f455100d4400d02d501c00359408041d40121040e500190024407010000c4032580ca082d1600070034810b041302c01c4144141c100d03043d10031000300559a41d009100f00500b0100800340049904144111880380c0205040050003a90320518000056030000100d54102c02004000e40f00c0f01124800404505c155562112168480303803180d802a1800529000300d803800f440001e06503240102030034410340040c0380154400d0403048085040d640e2202400e030300700300e04402c014001c0c01c2d4528401e0744103040210010910881034000c0a104810110030800f05407500b00ba400a0b10080d180185845810800c1500301c070701c20000340c9002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 636677041 1250 636675791 636675833
    0xf09092f0604030f030e091003080d06150c061506021f090b040b010e060f010f0c050c18010f06050708041404090c240e101d0d051c050f07 61
    0x16440ca080464035640064008442e501c100000000034540c1003c007074005000100d607140098a0003410300003000d500b03440700500881021501010aa041e5000207018010b06402401041020f000050810740e2509042c3c03100e40c54243c61205103540341601c8400d6441c00c0c1c00420400c51400d05254801103410b04486a503565210a800014040d044450040c2d0003121240b85a5040c03800b0ac030024040682828030521000740c000449903040452070000000c00d042c000c00046550916a082240c80e4040d2076005e00013800020b280b1441c211414165840300401709059038a07540240c820b0b12807a080604002c4050008000001c1c007540c242c00788610203040030a10042a40d134000e010035064014545c20200824202010010101700005400c254a0300700450b800c9440400d042c041c10b0f607202801c00c01d9021161003030510010702944400310151002c0410a0305081443e15100c0c41b4400441c220301c4100000d020034451400e40e98030320748a40d01c5034a0180250398900403c45002104888 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 636678291 1250 636677041 636677123
    0xb0304080c07170c0d0c090b030a06060b0a0818070e0a0b0d0c0311030a0c1703070506040318080f032710020f100905030706090503070602130f0909 65
    0x1882205002c50340082c82141114001e604060820f80c0c1030800484129000310341c00c4003050041141200b00300c0454102c2c060004070212920046814070314900c001800d1242401000542411400e0003800c000c109640e50511645079500704c4100c20560303905140c0264040340c01440704005444180390058039805c3c000070740c200c404010400105000c00217890810702031404000340034034071015000c12a000c80141460210540d00c42c0e68000c2140241c00e000840c441d403442101900b0000c036140309400104445403840c282c0380081902c0080f0f03000d24034444910200040e071440018241c004904458042e5003800a560103501003c0c90018203860059201c005181c81a210f07130580b5031141410f03501820042d080c2d412814907220040b1803150b02c0794580041c0b031020840c0807042e03689250380b18030042802c1583c1d051140c6180104000070340300d2480002d10100015040300352000303c80e40c8146083c42a9550503441040f561f0391040600176900c40d009081015045c50400741d01040f25070140c0380 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 636679541 1250 636678291 636678307
    0x114042d030f030608010509060106030f060b0f041706010612090f0210020a0b06100e0d170d0b0a050405091903090b0d050f10120618060207151506090b030408 70
    0xc515019080e0a401140e0450b1644100c1903241c000c16000d000c3d41c600038022400d00e019800d95a0700140308040805540b810401d60025098110b100145000344100f62215004401c1c807083e940709100b401403504501c402105a4003020031640e040b40c0c8151100038004441e0362040b409031010007401c40300c1400d907402e694010303aa40d0265900e01c0003070307030b0041414050724078144038003013806070009105460100d8103030091540140580351001d4242d030401d610f49540d150202d200d103182544c886c803603107001c40e010320010104c0c1e004511030300040310854a12a0b407031081c48101d1303105036840f0b10550460000c1000040d92486181101c5102e40f411401e1680d442c04c400c403090f04610320150301c03643c840003480b01804210b01110381003c2030b41503050780c02d8602074a004004818840003440c0356240d001240a04003c58298098070790003240c1599901308070302d0102858046182024401c924021b550541c0000d11030f001010741c1d1017070f1a00240c2509081030360344943c000410445081d0b03010050b0b41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 636680791 1250 636679541 636679613
    0xb07081e071a0a050603250e090a03030b0108040b01030813030618060b0612010e09100204060f0f08011511010f02130f06050c030904020c10060f0611011404 69
    0x440300d18081d0401c01400326402e00c2e140032451000c3d00700d031085410301050280a079030108803034212044120700010003055041c0e0341c00300c00c0c03003540c00a030301007102d04100002c0c01400720308c00420312320030750b420050308c070944e0300640745a5000d540c0a001300c0ca01b01c0041c40003a022100400d0111004a40941201d9481d65824151800044032907085000c008120003004840d009019076148202d400d28107021031400c08004000c4140f09101c80c8034146800704038003110500110002031034000b0b0035951344d40ca400380606003050b950250340c00a801c017400490214490703007446043e1400c201354031046401c0c2c4001110021b00d050014900c0d55a903080501030701c0802d1009144041e012144603130a41c4ca031519140b04004c041c0e00070380501c001080501c00807080481181c9029078100e0700180c95a00b80c002443c41c0c1051403100c1c1d018245403000100b8602d200d01c22600446585943d8050940f03200303411142130750460300700c01401000f003001040c00101c40c441d5a00311542e1009010244000c00c403054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 636682041 1250 636680791 636680797
    0x20d090f0606081915200c07140301020a021c0203090409050a020907020f03030a180206070302060a0e0307020303030a0c2102180d110d0302070906170709060b07081e 73
    0x1100d04550307902e810400044107002c0010001c0400b110740d80741003011307100d1101c41c8014408091520740d03912281000025440310b00200c0700c80095000761101620b10760256203034164010707241e090f0800c0310b07000a140b4050007203800961866010b1300c104400b001d03c11003090881d0714504150b0005102542403620795200312000070b40503000401300b10620b8010f02c90002009000f5400b1501f00e0406031800140000072290016000740000840501d80800d81d1038400c2c992100a41c00075000419400345980058010b008200e030b00001c0003800c1843c01d103a642d0f0b00c00ca5000940581083c800213900c101e103644000e95084030780c18080d1480324007000c45c84990300b104c483c410300191301240001d18510381e00d41a002900e810344105400f80c426454401c0100b4640c000b00b4421990b182020082510a1000c40002e150400c42070014513101c4600743c204504250b8610602c0c07103200c01c00030341c03282e29000700c00031100240b107140d03d010310030703168001580c1c000400c0e03c5461235803070301c5509203107110801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 636683291 1250 636682041 636682043
    0x83912010e300304021c0309230406171024120611130e060411040603060611010c0f0813080706020406180303090512011812080721020d090f 62
    0x1e40e00561051041d40b00158001d01040e90101105004200c01030b15079124020b075545040c44c01d441075007501d1130111081c02d56904100d07002032000d4460901c481b040008000720200072101401003e403200d14418a0b80c54070070507034550364807043c840e003459070540e80034100c0c4401c1e90512031041031081c04078041d9003055030b01c0790a030038440c220b10740d0a0040a2140c2100079400a1001d490a444555408119204c074043c0b07200c1c0c2241070300442d07415540c2c2d92090b46c4401b03d44020580301c6c1d94a64000d0010b021621811011410980344c403200250b06100c1d0800041240c2c45221061400c90740440311802e008001c403007010206202c4901055103480079101d035a11030080544c2d228106040186070a5103000c0050350001c08103003c1c400690000095400e8440583e2601c1d10505980c03140c0d401f4000e90070701c070b90300068240500c2003444040314400c40191003a03242c62116849135034040301c400d0503801c10003400e200410440f045404143d0010001003582c141e01040400d0151511216003140e0340b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 636684541 1250 636683291 636683323
    0x90616080301081f18020402030601050d0e03030a110c0a03301515090902030a06030206030f070e06030f0708041403031602100c050d0b0301090507083912010e 70
    0x106804a04c203040f02805403408100e4018410300f0710825181d8024040810000e01c225001310005074035034840e10a50b040104082e40a124403800001107a0300d0380d00079107201c0c144a00b014031052b00c95543d101140c207050004402048a403110b910304407000421b00301e041186080d0341c4d0b03981000c5127658100700c540f20390002c0d0004d02e242c06986c46001240310b80d4030071805a403a00d0805903069030031041b824102d8461683c050396a54412001c200205a5604029408280072040c0042030b810240001e1040200e603c400a49071a00010008207000484a40502041000004200d24412582d1030f420500c00c080002c00350030a41400c0e070858000300d481c5026425001d20921086904112a90003414048010440d059013060000c4c22441140180d801c00340c0c66904101e4103403402d41c031802045400c042907d003400d0301c40700c0068a42840b0080301088000203010082c540890f80801d12544910749041d44e03903800740605100c40f035622000a80036955a03003c2c248424a810700c20f05c5d00e0840200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 636685791 1250 636684541 636684553
    0x402090d0303060807060c0218060126010306060509063a050c0a0f0b040603021308010e0d260406090204090b0c07031808251d0405061b09061608030108 67
    0x941341919000503644004100404c405810000d61a9040850341d480e005842403a103558504c00182c1d10a80e08500c1d0500382c0000201c41c4902c400f500d0365250680303114040a104c3c271640c860800240c00400e98440b54001029205080c008a00c1c4118400d0800c0804059521300840090031003800c406020542d01c0c0c2d00100042043c5180c1400040d0103801e1005030b00f89641e0038060164814011030140205250740028000d1440094600010003051b41600a1143c03850402c080c9807500c0d010f0040c0404501c1403d1a038015620039000540003240506951007650380d0390300c6000140040f054243d80140d510705610380805e1800104911604032448642e941d81d8003407500400d1090406400111710855207418050b1003c0840d184510341c1500d0142110210094003038a8100c1c81544001e004070030f01c5940701c2a0304480030881d4801c1c2c0c082d40a86000303540d202d405c0b101041000c0d5021069010402120841e440e140c4042e1036074041c440e01c5070b03c1509059803910307001d40c4281c10009640d8404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 636687041 1250 636685791 636685799
    0xf05010302043801020c06040b1207050a08070f0e030d030c0f0323070504180b0a0527100815161d060a03020c0a06240605040905060402090d030306 65
    0x14001d0b80c0308507840c40302c0060f020207010f0306880c804950b0000014841050001c180c200d0b0301c01c11000d4600c0344001e12071030361690f447ca100b5240b1303440300201c440100d11040000c0c0340280902c0648002c0840760300c40100c9a83c890000719081c1c0b0400c03100b80103114001c0c0f07520b0a151420040d1401822117601c0000d084440200c000d050580201190006c150030014208001400c22411411020348a0b000c2682034540c030390144c903035000c0c5400000d01d8140100c544083d45010307402c40450300d407090714091140d41e158004e000400340790800444004901201c1b910016014640c0d507507226107a09261820980c503107020b04d00340010420003125010003003007440f980012100012401c0100d905000003601c0900101c16588110108035a01c51500469070807400d41c00b0f9011038074008403c1e019240804101c1c5040802001031200603841824044a01342541c0c28100b1020282e9030035440b00d0741403131710300380125020b0a0001d2805402c1a000e0004426603214a081440641d2098901042003820 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 636688291 1250 636687041 636687049
    0xb060412050604030810031a06010c080705070f091a010e010207051002010203010905010905060a060507290906010f050f0d0620030a150302150a09030b010b07051e1515040f05010302 80
    0x1701404030b03811410141c0d41000007401e1803400170240009000c0120140c0d0341c050045e501c00d60441e40c0544034900006203181003180c040384c072109071544284403101c0300ea11000c40d00c0840362003070181100c1c1c144401c0c40110b60740c040d480c1c2e5802c5120501c112542d02c3c1d2140049031050a40122003009030b90044014060304209005003401340c13424007001c12262030000c000030944046449003000b845000120745c014021410f0000440c00c681a060002c0d009520480a80064044408100720302481001050071481c142c0203a003103074001000458014109410800c010100d848120f803126550140088844203055041c442c40c102c501c1915281d00d800a150016118914078400c0f60018800b0300b0300040c1e680c8481d034130401004205581d00c8005020056840c08125000948104020b40000801b40381e40001000e565115005503804903c88403031118004402590020b1281c21008a21601da106444159401719003200032104120154010504550b401e204401046840341d0041c0150f0034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 636689541 1250 636688291 636688307
    0xc0301060f06031b0207180b062106010206011a2206022404080318031c0c0f0306121403130305010207060e0a030e0f15030a051f0e0a0b06041205060403 67
    0x40c980d030212503884d00003900079100c40c1140070306403111031401c801ca07210300b0a90344540c1b1301450181c00a0780d201610084003843c1050800800520b8400744005011544080340550484490000107041718119110400083e002420241040c1280c114804660304c400d421940c001c4c141c6030003418802c01c2001c0c8400a800403441d8445154804405000000d4003020403603038044a102140c000d46d4480000d1142141305000410b82500f1481c074402c0100111a0311001d03190001d0b444e1003d081d80070340d00c00e07400e65145103d805c03d03030300700f10140c00c001c510082c1610740d078050b8000c1500e1508080c0b80c3c20540403129500280c4082c1c2d404a00e0204100f040c0c441d18043d40c05541c0285440403c03550001e0500c9255203409029513042c1c1140d41458560304200f032900c04c0d00b90304060310703450f2a4000400818088501011010b201928602100240c04200050320ba6803e014011942e9401044016089510005411100401c40094a04017921120312520711070009800743d400e060900826403c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 636690647 1106 636689541 636689561
    0x809090c0f030a050118060f140a05120715030605131a030a060203041104200a0c020901032001030c0207030314070f0f0501050901090816050c0301060f0603 69
    0x3e90283c21076811713642da00081e00440e00c030b40ca442d281950168810a41000f6016500344400508a0030a60807600041c0240312000d558101149620106181c82c038110307049080f092001804902407424018003030304d0180b001da42808006901c3d590b07401701b800c40b09a59090b0103000004031103040f00d4210070007410f0750f507140b24904004011b035004076001c6924120340514a0641d2400d8443c415100b980f41c4050886440c142250130b0700ca5000e80800c2040c072113510180d80c016590118041d01851042ca2071100010390390041c006007550f05440c3c076051509010030050100c0c2d001503d60300704d81d01880c20140342060707500300b00801c0c8984140a42049407000c5031105000d1000c101941113481036008112580d540b24041d400c03240600720040c0703084010400c0000804a0424201c0c0441c040c1c4103841d4071480410001e400c44103260f11200c000724100c4402c1000c1601886455802 = true := by decide +kernel

theorem cover : BRFrame.Cov 636510791 636690647 := by
  have h0 := BRFrame.cov_init 636510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 636510791 ≤ n) (h2 : n < 636690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
