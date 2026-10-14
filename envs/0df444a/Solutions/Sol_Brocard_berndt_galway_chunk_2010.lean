-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:26:35.557971+00:00
-- url     : https://prove2.me/submissions/9d7b723a-6c41-4f7c-9103-19f74a88e3ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 361330935 ≤ n < 361510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 361332185 1250 361330935 361330939
    0x409030f09330c050601030606051201021804020c0a08030408070c0506040b07122c091006081b0c03070803011e120f05011b0c0b0f090a080306010c020a0b0a0e060a090311 75
    0xc081d07183d00280041000500a6004510000e40181000308001c610200f00320502016801400170041ca1203e0136480c00c01118100c034010f0b9118a0a00840d041080701c1101410241005c010442400041d0004141180c4500d94112a55403141c0812442d80620300a82400c0c04050003048002070f29840c0341302d150ba5050404c49075050140d919101556180aa0300c200060003840c40e40850030010901600080340f0000d4100043c1419030041c44c0440c000d2107680c40391103060028840400d44002c079051005118141c035551301190901d03107a10b6100383301d0f85101c04440740000c01c44000e50700d46002501d500c82c41482d0207481c3c035110135000c45c40503081aa401e55881901d2502d220711094000b1202410351100c40c007100c82801e140403140c00040c591194455031a00700810b0f0721020030307200c02042d407240700c4540301d0300e0b5600100e4036840c83e0b0704001c2d08040030010200740c0700c041c0005851940001da99021191411105102c400d0090601c10800300c0d68a030010b00000d40e0f5200c0e0410030f4400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 361333435 1250 361332185 361332197
    0xc1107063f06170d0302040515030c0705060c1c060303080a0905070801021c3c0e100e1c05031303110610030b0c0f0a0503090c0409030f0933 62
    0x444500002115000da114030340c508043c5070744210a50741400f4040e5880c5050504500b428900000b164411018501810b00c0d4200000002c603000b0020307040c0c40c100b94000e0201c40d07491030190356011096202c0081c64040d8014111840246e1803240a54015aa0716584081035a240d01c07507410081c040403c0210b8450068031300c0801d401c502440517200c01c205070724a2a40000c09440c8072000c540141100030b4007a078030b883c00e141074915903060041c000047c0510411078010099040002441200306441413401228801c01e420b10190304504515521101070b24001c00c0c2000359680301c111007056080103d4414000140b10402030441440018000d0402d1030080c1c00e1158454201a0101c1d01d82c00c2443c2200c00074401c0c000208903032a070245124000524054640a240d07039a0f026460481d01080700000c00206001c0b01488114110a400b81040c4485003013894043c045629503880c0c00001922440005520491449441400c1001d0310500261407415440c610010000343c0e0380f8410b0001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 361334685 1250 361333435 361333547
    0x504060f1b0b010501140403020609120a060612061116080a0c08032706070819090b0f090c040204060e090402030a0b0115080f0402060306120c040c110706 68
    0x4441400301690b403041d20200210360600001403c10f410414000d01440000c3c407013480180c076010102c1d0a01c5100302c03a11000d80c09503454080c42d0411103d0010605410071800046a6407084400c108807403045409000049800207094110300030b039218070841d440600c04a60225003100d0003002d4514291402624240854856402d1644143d90b614603c05525512202d1032540310502d0700c0105200b4040c008908040000900c910006080d2014580f0b046000c40c52070f0303615910001c05140d12044501031850010b554000c80c1100321600707881030040400356111440c161007102c0696001e80c5910320300b03502c4041401310004000700200c0e09440f03104003410200340410390090090600030065042420f58820080031600040c128000442901c020300005039074800a50398008030907258403000c1030042503414500302c0c4580c500c1d5005072800302000007103075000360602400ea8410781140d850035607881040b101d03050418082040d00544200d40710400c6840c038201240704c44001c017401c801c05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 361335935 1250 361334685 361334717
    0x90604291201061404060b03010806041e020d03020d120e0a06110f0429031e04030306050405130501180201230f0f0405090a06030b15042403140a030504060f 69
    0x500180c0013900c00b0303078012562500500c1c0a002d1040034029130304200c0d095524040d0020340d608000361000b4440c7c0f0002c0001c480030400040d412091640007490040400802e0030b02a45800701b00b0400800105400126100580300f401007154800541c0c00405034450242c43d01c000401808500d9466168200404d800a91240001d403001e082410441424401404040004150007940313508603503009001700908d1701c0850b0317000300d241c0c074050154480329607070303131070210010310613038111541c4a40341c203040c400e86d00060404181c01d284660000c012008845243c001c00020401c0d0080c0000c220340c0e04c0d801e00b0300710401d5846049040510082c108036201e100c404c9541c0180c200c0b400300b202e0206003003010740b402820154120480110800c905411038445204615004081654a0402d20341017032a0707444650122500042002508000d0901d000340300462009a2005403842a115841c104070712101240c41e81d0282d6064a03520f103014500308040d0380c0d0080e402c85c100f00b40440004080d070f0b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 361337185 1250 361335935 361335941
    0x70e03070f03030806090f0702031903020c0105010320120616180b0a0314070e0616020a120209011a090411310914060f0d120e090604291201 62
    0x2543c800c1e01d44075524a804824070140c0000141444454540e0304144000c072070700801111119298002d075404040301c08031084c6c010344980c1a550605600e0302d4000014856140076402200094400d041003254800e41003142881103550b0000035034001401181e5040d01c1c1c003182203001080d0341080605103841c2e180780f00003c1400e502c04945500001100d811030b030b07403510400000048001d440d88550800b481c00800030070b4031ba20000c1c00340d000000d0005450313040310103e460551f40101940d040c5901d502c1e9481c00c1d0b00149a00300d002d5401d030300002c41c4121440401c0040b800b4a401c1c100d040c03000ca1030811014199030038604140410070800d120000c00342482007900052110046161100c00100301c5040c81d00c0f030380c042409030380f03040320311900c0b05082d03c441900101e007180c00380a505003940c0006d1114102d42d000400d211902c0025604c01e036088100352000c240e04a034a44401c0c0c0e2400180002d6907a42d500c2d21406407440c95901c0030506000317091080c02d14028101d0081030400c04012030031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 361338435 1250 361337185 361337189
    0xc09030c1201020307020706091206050718030320062806051206040506010519061202041e030302101e021e0d0b030717070b0703021203040c06030f060806070e03070f 73
    0x1c60b500001004903081e010000b55006140521f000c4001034907025100106001c2c1a000410a0341c0301c0d0301080c51306100711100c00c043d1440c08541c42c051590780c9070203000b600545030911410700c0c080701c40c80040700340402c42512030000300d030b4030741030801c030402c8a80020107403282a0000c86a580780b010542d80c440c2c00c007070700020799010b00030081400c103803c1c154900a016804188190203503010040c60068800c0d0f03c0007284c0d03041c2402c00f2b0301400c443c02040039004680107005074428412110302039544c0c4e10038140480e0b00a4003614079200c0303140085015a92444502d00080c0d08909200e5020070300c1d50300034101101841e056030704d078a100c0310015015a1043e80144030040d101e5082d01c42624051104600074200c1c510150b43c80c42c8590280b5448403524891043e0000c004034001c41850b0003405460580c1942da000d49030f5034909441c0044004060340690070000380781c51800045000a0b00c04c8100340c42c0a0002005550340c1c24000301e418034086204a1781501070920001121003400440e040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 361339685 1250 361338435 361338469
    0x5090c092a0706060e0901110a0f0207030b13030f090b0a080406150905060109170604031b08040303030c0e1903020603070909020d05060f03030a0e0105280c02030f0d080c09030c 78
    0x4c00c0da240c070031402040040680030038503076490714a11810f00b102050403520b05003542e0802c000d141d861420140d040404070f5001905003602c04003000303080340c680201c0400c0c039031107920380c201d1910b415042150a80014011809800020846020700d40d00642e922913000b4811751022407000d0180031000c40d014241c5d4440c2c0041520b40c0140310207503800c41490b01c0139000700e15080c65000310460205607541c0c8003500107018410113142040040d041d0180040085030461400f6039030325601d140080040c107032038040b000010302034459080c0b14680359100a14003100d900d130303040c1d0140c2507800b005005e82c009091036044c011040400240180384d8000707418442d10404c070003c0c0a2402c0001c1c00240619600d8140c0700c5c1e0000c0051103261600084031002040003841e01c0f90700e030890811925210300110410311790b926011454040c42a50111352400040c0c0700b582911160611254400c6c1d44d14a1441e15001040152001548191552020341600f8400804032020a10720b40081056403c14401400b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 361340935 1250 361339685 361339691
    0x41205012f120601140304080c15070804060b0f040906050604060f0503120307030902040e060601020f0d050909101d010f050613060309020d05010c0903050105090c092a0706 76
    0x407850744040c0d500014104500003148250700103000c441124411801010790402980000c910140d03c0f0380300c0c066911044940701c951301d0a1604000c0716642150810b680c0612034511901000c291a0b0300b181d0003091035841c0c91801d41c607030350750b01c42c09030804044854000340c2032401094541d0741c42c094000c0550240400080030705042043c40283d800c2600101c0d0040d6108104205a880000c1d107804440840c4e080162030351a2540120041c00401802940c454280b12418044000c041602801200240c00301c0310b840030601001603c85210780c410701c0110741e00303010075101401d103c0245070340004205804c0e401203465200880c9121021340d012107002c400030780184501520656000c0c042e0004944541c14100300008a025803c01c03130081404258890410004540383c1c0152080341540c0031009028250079803d00804050003071005035415804d0601050f2a60408140450a25405000c403081991200e104078603e40751101c880700000c034840d4a007015015140e014010f031911541c008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 361342185 1250 361340935 361340951
    0xc150403031101051b070c091104150c05070611100501030c061404050a0302042c01020306010e040e120a0207090c0f09050117072102040e0921030105130204120501 72
    0x100002e9804055519681c513207402e10000e41c0fa06148100c4000fa02013055550711118a0f001c204000c007903000c1c0c0242801c04214160726440003000d40309039080072521880d02c0d041260100d600c24026603000e0059000004180040d92040f0b0741c000f5100740c510200d42c04002004000022203400b648160744401424405019032540101d1000c0720501c000c903541d080604100018441c90190b08c002842980e880c043d444400003001c02080c40303d075451242c01c50f1500c1141030740c0e001c0e620403524903001692036000007019103044e221300384040b50040010319601e0604090480240e0001074030405501c180c03180018007811502600c2c450722050358481100da500b50002400f1078940d134001d5410300c004031022000c1c103030301d5144059000007a850240c0101901f00b288112644190029070501800060046581800580454040e150110403035110000d5002c482c015003c0704541002502001c1004200e18030b020883d1000120b0f20a0b8018a8032780c2d074a95101d1001d8500301e007190965118510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 361343435 1250 361342185 361342187
    0x204150b1c0b0303030f0f10030206120403030c2a020409020909010e06011d190e030a08010302120d021e0304090606080a0c02010218060c030408061f120b0604020c0c15040303 77
    0xd00d0105071040e0011350960a0508030082d11510003403204444104c2c4400080351114908800d03802980c010f030006a5440340a0900403990b02d003103d00f500464200225800d000d4419044070341c6c50a43c007100d140e440002c02c28440d0710340780450410b0307078030a480e01001400759888624aa001b203404100015241d94460b100c18203003041640409120400c0154140c550100e960354a40c0c401540381c81c2c07150131090448260000d0103010382d003280622003c6040da0410382c00c030345102d0603a4003c64890000b103c1e055515aa10f4030400924030041e00031400b114014048260704c42600b2500d1000d580c24207407502c68040403544a40d00110024030910180302d05078080d84102e0f60064100d100030b41c603220071482e03d0382d041c0d02118120b9008400c00180040c55600610694000d0704100003070b212142440c5214120212180c0c0d1031644200b40c1c00000035102c0c2a1001075403905500452540c40780e90380004010094200c1c0d00a2000c03030090075404802c0b980c8030407005504815031410142c4403401c6042c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 361344685 1250 361343435 361343441
    0xa1202041512211b0510150801052a031510030b0111060708130201050408070602010c091203020705010809011b021b2b15091104050601030b010801030204150b1c 71
    0x41c848441001c440c03c1c603010350b034880c46545801002c3c049641a4034440e1901e640b50408056985080a15160302d03043c00b03003403a9000178110303005200203000d10740324082c4a01e20b8603a0240d4140c2c401d50741801641554404c6009164020741c05803d0300f202c40030708000f003401504801200700c00a40e5500a4404940e0441cae80c8000c110074041c01007009e86485c480141201c100913000c00c2546803200c001c1002c40e880780046902910030b001c00e4540c1141e85d41c038080d023740f211000c078002080d147c074070108034440807401145c000f0341c16a0080c1000e900e03180040d25001e0024101407600e54881d600010315230049100c44106183d1a070041103209134001e10450219408001c2500c02c07080720b42201e00507980060030300c101d5088a42480104042d900e4590b442c0300f0480380144034541003498403028002003111100304000c042c2e8050026990700c0700114110744000c450903010505000041c000360416600c035201d40c201340000c02104548840ca0001140c0002101c8a06c800c00c240c10900d031001940 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 361345935 1250 361344685 361344713
    0x80d0f111504030306060518010e190305070503071505030c1810080f2410180e040528060e0c0d1103011d060a0b0103060b0a020d0e0f0a1202041512 65
    0x441d01e241040b0400f0014150540c00410080c1045800c1c0c90101032a40c507811982f41c40c180c1074aa00a08942c0c80c0703002511803015100c1c04d440b078010010006642c2c2c000403030750041c003807155840b2869541e45d188000c1c44c0e50410390b08003041101140700f00001d0b880742c6540c1402843e144d04d44200a24100040744a018002000058601d0080030f990440349400314035440a0788c0e0460394800409051740b0704941201805003c0046582e4506002520070b240e003844600543c0a401524107280d0501d000e16074611016946172200e2540ca04d9040201da00d82d03000b02140d0038504252080b07101c0b041c00040c0003084c0003400341da0000900302041500d16007403180849400309640c1c189000c6205045054403900024000d00b4020f480c0c100c0304031395078426405074000d0324944845980b5149156802540d0f049103500420100e10341c1801c1d07510030b14000c0100301c500340d801000c05d0303400d0f410103c003c111805020b40c102d803c07949410f03581c6e0302c00c3c0d0031752070807000b920003501020000405400e082c580d100b00d003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 361347185 1250 361345935 361345937
    0x5031c05060f010e150702040207020405010b0403060e0303040c030308071709010b0406050d050a03050d020d1805010f0b03070612060e010821030709030209040503090306040b01080d0207080d0f11150403030606 92
    0x380c003a43e00c142c035649180b00741c107045e980260f9241c40060001c100039104d07110000b50700c58607101c004595170b164280a40246d0313024140410009180c4d502141d43c0f80300581c0c0c0074161107050141000001d100d0340c0181d9200d075080c0b510035071860850103403e040400954400c2e41c280d45914200301542024801d000007450129880003144905845041d00e80d031031000042c0c100140003071201844d00707480c0c0403a2510002c048080041004003419010154101c580c115101d500303011682c20000c000340540c1c0da1182008001c1d007111480d207081528044200303001c04000d651542c40c005502e000f0100300e207000b4000400604042c840e980400c0c002c58840304140c0407a02000d0080c401d138907501840005c2030700c9d030580d608242074440e410524558003138545655814400c071000c10040010012505040f1546001100c0c0492180c0d10180d84810fa80d00601c00c680d4441143d14452030320800d031034030194110781080302100031004159428841500421600003214000b07000805a240c45007900070481 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 361348435 1250 361347185 361347197
    0x20f0f01051801091e1407090b0411190e01090e01140102120301150e0d1e1202011107022806020d090b0f0a1101020f120414010e031605031c05060f01 66
    0x35a640f410300741030340c4009040604c5c071000308404010300004004007840c410412a00c03000c0d80c90101c58007409451080301e010303a080542c6404d00405680503640c3d03901800889540d0036451140844a1400c400d481d0f034104006510002039104481d50742c603019021041060800340c00110019103003001c0307030242418001c801c0004011190445521040c1a107440c070701402d81c5d107640c03400201442e0001c40301038004681c42038207000f0f00d0b50200c0080300c011f204102c04000d0030582e02c001e90032201c008441c0e40360385000304141401403400c1c2100118030545522801440901c40145001e5a0385030703040b80300035034090200ca41c012500600c1410045c4a4020020300d44010215100315501810040e181403080ea04040c080380402034058408140208010b26100c10380306188003103504056400303075650050410a003400140c103029910300620800001d5250182011440c600c10031465001d03225800b0030720080700d0803030001e240b01d01c4004802c1f0010a29003030140402c00120f246c0c28400d07040c811 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 361349685 1250 361348435 361348451
    0x5060118030b040204110d020307020d260a0e07060c0506090a030903060207140f0304060305100608010b0a09051c110102062e030c0611060c210601020f0f01051801 72
    0x1500c03140394000e03070740c0c0a090102c8549552012070041c00c031110341d00710610404102000001c25580c0614801c040d56400c45c0c61803044e03000152022010311000c1d42c0503452000b41005c0c05e080d8006d0041c0c0081c40340b07800249e250300015005082124070780054001810081c8540d045c01020006940c124042c03102800a518559030003420028051200401c1c480e000314441043c043c40112038001681e0303220584440c0c01003255401c1d2254018052640468900380101340041900e214880c20364010381c40c1c5a42c03503405c0210405541d00011412001c01601400228583d1984200c1300c02c0003a2507030412440719542d2422000312106a0344050442d4040320410020076180c8075000c4064441c44003c0c12211a01001ca0880c0d101c280c002509518400100240066000c4205180040c00905440b06600c850b0041d09003403043d403034144076081d010380b42602c0d5200b43c070482a402401c140111190f442c0c81641460400b0001025105581d64a404000000b2103225485440c40000c80003084000d0f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 361350935 1250 361349685 361349717
    0x3020a0b030f0f04060f050f0a1505030307030e0d150906050a09021f0309140715050408030d020a050d0e0a050705010203090a03061d061801060b090d06090c12030503010306050601 79
    0x4000101503101403c1d070ba00102c0c0501a84ea48108050301d0361b10720600051a240d071025036000015101c141c221450700200ca0032921000c82940c2c203440b801406103151041c42d4404990644003074071203d510100000c2c140000840d0011385821220600c0b40c00b0032078280d41d00f850821143c0c001c1c00140c00c1c5051401d01c20059842c0f440d00400c0940e60000350101181504c1c046000b003245030b070010041100906a0800b00500203503401c102c03001c0e0030943c0c41c08424504c085805001368402e0315825401407090341e5074900290050111880c00d8501917040c1480407060301c0954051800200035034005d21959000d01009010210103810280020352a042070742c00842d910000c0ea200261507241e4038130020038007202c0700b101030400e611604112002404d08641000d8100350720300b00e005980d860700700c0c0050b0000b603003015034456881c01014086612200c0d00c41c031002c0c217013130402100c0300d00f8408000700c1e041d45146411030026020703980da40e45960442c40c0c00f00840d40d015200302e05126842c0c44138041d40f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 361352185 1250 361350935 361350961
    0x1050a15060c06200a03020309100c0c030c17070305090907030203010f300c09061a0403080a0306030524060a120f030e03030301060e0f090106080a0921050403020a0b03 74
    0x581d20403000203107131690f02812070f6020078407480044810400202420700c1d0764940c02450051032801c0541c0c603402c10180c144011584500c0480d030224446680140200340203002e01c40c402c6019003014068801ea18040701041e500030700e02200400c0001c20116503030308000d80c88c160300a155040443c595410001950f408460510402c8981000e090412041181c0082403542440509042c10000d5440f803402240d0b00e4194050000c0d91450130000254404036126100c031003084107043c2500e00b41c09d5440740c0c4119800700001c43d05154542d0b10000000e00e082251000d00341e0a50b80c2c10b42c04815000000310030341030243c00a03225440060341400070103480402d00a140340d00c40720b8804569000c1c6419100c0300089201d1307540c180004800050b006801c42c41924200504a9148021104150800105103070a0040a0009442c0c0c0006110758045a100315401e81c040d001145552180d4107159414100c1030303400c0400108085020411820403403007080190a00c001c10304d007940703024a455401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 361353435 1250 361352185 361352207
    0x1a09010b031c020705060f0304050f0106030201050d0c11250803042402120409050604052401030c120e010b040c020a110607030c050f0a050c030307050c06070507150201050a1506 78
    0x80701500040785003110700800c9414018100a4030303240d242d104101100c0d00392303042210281c0301030040100520122030188a41010390b0750507103405050002c140b1801004040c0b600801d000c2c0444d4050150150b0420402d02202421501c0250360314001080d403000b81d4102507103d22215401400180510322805411001e4078107094621004000c686800b20f25114682001039880000090045002005508010300c10170040c0c4085c002d5496401700865504114010300c003441160b10b1400d00103610980040920310020701e024400d011200006804440c081100500305a40d1410048030600b05402200c8010700240003501071810640c07120310140804407c468812040060329a08242c01185080c10254010b006c4440c0d50416114099491614010030fa0b2144900102001700345400022220001c2d480f8001e4803882000754180700f850707081160112041e000f02c26005c1a0300310070300c15400030b043d0329074004201c900f401c0340420119000100d100f198903002c40c0090101e03a401c81070038a2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 361354685 1250 361353435 361353463
    0x812040b0a240b0c15040c14180a090201050f0f1801110d1b080f030403020c06190e040b1008010e060405040b16110105011203030b030c03120d181a09010b03 69
    0x35481308889082803e000403c501c1c45c0c9071451040c28401400003c0290030107540001c81c41c0c00c0c2181340d0340f0030842034001600c0ca000640d030510001500d08000e50304100c0f0703282c0c81130400324204890a003548000760000c0e4041c00c1c0c80180400e507403168600850385020030076000e0800344c01141c80352414070f07207544072441040f00340308039100c0510585040030505ca2499402030821900c2c0c109240c03a1305129481036405038010301c0b48444038841d034076204044600b40c03164041d12048141d0b2801c2c050729842400c900b1658026940c0001c5081910303000c00c056100982c2c2d03541d001e102e41c10410040c48000000c3e0856005e14a0b10007000001280c1c48649500110162025011601400c800701da4090044507845000c3d404c2000000e00740e801d014442d44024070a8405001d17503c0380e0003c1c103030381d84101c40310303680d1650004003d45400601400103000700d0301c50300004243c5203101c1151041c1d501c081d650491f00ba81c040c4040c040810000a0225000f402c2c1c40c00900c980c5840400003940c1d00d0f8407105c214 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 361355935 1250 361354685 361354687
    0x40b010804031b02130e0f0c0307090b0415030609030906020c0105041703090d050c281a040b04082407021b0d1401052d130812040b0a240b 61
    0x100f020240707940b00c038954981c000c10b0512002c0010301080b025042c0c0d51301140705031180740d24201c66030501141c0c1c440091805001440c001d072800c49200058116042c0d0381b5085a03035550140c0c01818588814005113002d581c020500350b015240007040f05d40241e010404540224004a06c80ea81c0b01085030110790f50032403c00844014205035a08511480224a0380300c0e81141080003004404155480740703060450b8400c0400080b2000c2c5211001c1c10101100030407002c18040c03000000d08800c0080120580003018109601c50072949101c2e44150006a503503417058068081e580d920b050780c544907140c840740a11203800c08400295031012a01003091000a41c3e5462045684401000c2c03110141c001c45d244020414101c01e09000341800c4d640c0c1c10400d0302103c0da01880b82c06041c1c0c001101d0365040302d40900c42e50307154030340031141c4070056040712511401c200301c5081c2207940e800240680d001e5905600103051074401c46c0c089410440782e1140440001401d582c1098004030b05904841c1100e00c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 361357185 1250 361355935 361355957
    0x50d0b010e03061005011d03070312050910090e0c07115103040b0109050a1103040b0609090d050d05090307050a050307062904020702130501120b06040b01080403 71
    0x1a6541c0780c40958054240c8074400800414109503000e103030131a2800e0f2078524904000b0f6a0b103882002031403544540540c03080350b080000442c99403140608035039503c0d0803400c010b1b0740030000e0007812110b507001c4009000c40e5001c4c0201080c1c031002c00d4001044919107450300d030240d600c810310b0003441003461b807180e020f000c0d02d04d0810191018504041e28401b07400d080031041058405120308512400030f01a5840c038581c1100820074804980c041c940110000c0f16513860300701c110000d05001054034a055480b500c1d5501480010f00145000c2d911428801c0d50a1030206c00340000e5040046c8103aa05034811191700d684950481c0890301a01900007021483d6507079185690701e0341c859601d0040052145031060014044080044d2906034130491003808203019000e40450150301c200d068000b00c510404148500b450181c0c0100240d6201401024200300881681c004580003680311500342d44e000b002500c104500c1da0200360340b08404403010410300d81100002410500b00801c0181444081192 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 361358435 1250 361357185 361357187
    0x303170f060a15090e0c07050f060c25170901030b01020c0f0d02010c0816031706010905121e10060b0c0a1707060c0f0e040b030a1203020405042c03030106050d0b01 72
    0x140d03c005c0c0611100c04006410090030030780190303001820a86150080381920300b038003100460840d0040e450001c6040c02c2c4201c1c0b04040041809000e943c1c0400320002d07002030002010440301e5043c07161007802c84ca4880c140307040090155401c03101614110740141c2001046951490502c0201c0c2d07105440710565042c240c40141c403840f556410103480e601c40403480c2032480b80030360143c4501501c01eaa41e0242c0c2200d50407a407050160a940e140d01040301c5032803d100c907040c181425042400f00710221740040e1110260101840000c15248020340c000e500d0030b010b100e000d401000e0003080c64080c046d1070000918500d0391070350803020000f08074424100002052991000c02d441d21950480c80401c030741c9844c3c8030301074602d41c9100303401004a040d030440202d46d858a88103070340011030064041c0c90b03901506e548001003016a031a40350145030b400c0c4000b2030582c62314410a00c0b68403040c61071041c0c60040511a40403620100c400c1b840c9603000708011705c14a94800c1c00c2d100c850080c0700c0d021941610000c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 361359685 1250 361358435 361358447
    0x80303160332040201030b19030b1302061b0601050102032106010908070902130905061804150c121d0d11010b1005030a11360303040303170f060a15 65
    0x100024210078950200074424416448940074074400d072000c0144184010902004c048c1d18150030004800b240030810215441501540d80450090519151030304c00f0390024150360450380d04460410303400307400c540107800c08010071409014240021804c1902911a004a500508644107500f003919404920380364043c42c03d10010b00302d2002a90f866a0701c44001400942298040c0c4d10010080100003520031540d200d5a405104050300410103090850166517486070b010340708a031140508003801048a0700313841400e002c000581d81d04410004055050741c280d03410303115000c8441a00e19900d03c8401000200e41103103000300c0c14803a0381c100c0855065401060b070300550302d4014100c036280030003075540f090086220310307001c2c0c0f41000020024030440581e801080708409030b440b020142d007082e081c0020201c1110142845a2400c00c801c0c400c0442d0540c0c001d6030044000c90541814900d02d0740340e06420030307444218000321804901e403070400074655202e544100c50222015401404025108038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361360935 1250 361359685 361359731
    0x10c050c030f03121605220e0702071d090c270a020c010f0911040e0f0a030c020306011203090330050a2a1b0306090302010906060803031603 62
    0x40607034000e950b4801d2180d840381e0042c5401814504202d0008140040c1da03922050402400e9803064240004802d090080ca020015628803841217580002161803110000078440c803c03075805024014617141f110f80c1812901c1602801000d000c40070001e4204000800c41c10802044903c89444086103529901210000c41d00030400391512042250542040c0c0051031440c805200030480e50042c140d840342200d01ea4030b40107000c502000311002c02880c10b60000b0b505501d2502c16101107060300c002c0341c1d1070300035445412004108031008541c00d51038140192801000c0d0300404000d88002a82c000b0510703410b034040108030600d14440d095030300701c840745203e41c0c22110508140e80011120704c00381c0150000c0028400142c0c0f1642520100d03111003005a40e140320403000820001d10641d40c2c0c40d440000c0c0d200703083e4001150b14000012603880e0192260b02d0b4065000010b910300329040890a0305d00079001148140d02c10030511600003a0380300540807004c82460001141400842000005e90001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361362185 1250 361360935 361360939
    0xf010c170c16050604030f0906020f1005060a0b0d09061b090509130515010e10060c080702010201021c06090b0406080a031206050a090f061a190207030807080d0506030c0f010c050c 79
    0x52003004101340d0030466100340580140c4031a00c2427923945508980d00c261a05019849810181c044080703000c0c660003e80c0c004000500200c00b080d00c1d03c0080b1103540200070b00d0003000d40c84d000c031881880590710644103030007902e60810011410341c04001c0c0407800c140c400c0300d000700c0280340020301842d80707007031442c072460742c004203580e007000f01c0310400881c3d10020300460000a0120001ca82100c0345144c102c400c8910765200c00e258206c0c0c503140e0940503004030b0801d0f030565408121040c0040c0b138820710200c20032642c0380002005030808501e0701c12680c2c00d030040c90140e40360081c248036217940001c483d014507174540b50041c2c081c1d65034039004002c1d01160340681e4016200d04c0d004160071007550414000c00c00d5500042280c95600c2a40c6020422128120f01c07081c00e0030480144544040c4103500250304560040318402035903541c1d0071902d54440c0c041555069004103c9404290041c080c050b04081c0031801001c4205130007001800141c03500c1182d80c14041607008140030813900b480f06040072600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361363435 1250 361362185 361362193
    0x7031403040611181809070e04052d0d171f030b01081f0c1e020313140f01211a0301050a0b0907090b030c09010e040903020f010c170c1605 61
    0x3041d581004c402c1540303840e00c80d13140066001c04407114010120300c1580c110001340344c84c62804910050f003500107002aa4a4080c4034406000d10006202807815030400c00c0d21a2007041005190380d0810720344080307a00411111816a80440b005941440c0e0011f4074045250b1103503000aa24400c038010303940c4010007085016000044401d0080341c1e240c04040206c184a200820341064079045428001c20840803401a6102e03543c04490b1022140e28100140100c81c80d1031950401107040e5100e070349c0080e03074a07421402c95081d14104414030030b005c04028280300e90001d81c0035030040a405103039200000500d5407010013400903041480001e12051002c0c0c02000513040c44000e0364050817010880b01d02861144011030072491103031034010211151405a0f50540d100d005020425510505a450400685040e8054503603210711503450250300c2a0010203101e02401c08103030035151210300134818014001d2404884803100d841042d4000810740456540c1e0400d04500840e4502c0d00d00050401c0c41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361364685 1250 361363435 361363447
    0x4050103050601120e03130b092b0605092b080a150e0a0911060a21110d0606081003020a1205160803090a05120c0108070e122107031403040611 63
    0x94003000800000720078240c241192034541d1440e80706841000752143d0085d0100d1214034030ac503803480c0c8403600381c600d9018868844205468200503140107881e60308030b641044814092485280344d100401ea9007000704180503001c0070380085d00d03840e00202521103258644100080c0c10000181540241041d81c05c80c411900b800c400d060020304003040121003001e071072080c1021a1034a6015188031040944c0c8442c01b040c1440340500d01e001c8102c0c40094010f0710b83c100405042510809401142c24030341000030400c0c40c1400003442c0410140604140b81141d80342800541c503143d40c070b00e003500c46001c14401c541c1818070384cc91828a00c5a0444000591a00e0100f80c1c02c8000c8005c0180d644100c0c1c10180c1c0e07588900070065604000007002c0c800d50b000e02805160355009003055540260141000e00783c03c40da01011682e09850440c440303540703411048201010303241081514003d8505030fa55181010403a940180c83c40c20001d1300301000e15804070000b01003000c2a00081034800c554004141c0b40d503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361365935 1250 361364685 361364711
    0x80601140d0b030d03020301030f0f021306150206100b0706200403051c0203091f090b0f0c0609061e10050402040e15090402030d11120406090f1502030405010305060112 74
    0xd0020b80c0b144a40209200020b0584c801d0098a0699030881002c0440513102d50b154003103c2201c141c2260486c13039842c2040704000081c45158001c004c5000142034075904142c00034103200f0004c041030b01e2501580414010344103510301b41d40c9640d42c02000002c0300d1070062034640507940c062400803803110001502004002c0701241d1401c880300c142e100501d02c1c044104040c0d0f164007451010030341200b106080d01c4001d101c0c6942850b030700403281c2400750151340c481c400040168400002580d01d10710000f0916500101004456130201c5080007821076030600c0290605001080c0c840c40c1400d002c200003046d107048180c61890020701005008558a175564a0540502a0100c51b502100c1c0d5401c0382001481c100140141c0c412940100600b820341107082003551126004030042409100f20001b021585000c0c10041c4040c2406850300b007280381c900a18000c410869030409a548041904046049a0000140d50a0b03070424240803400c0c3c1d4507078004803180c0910507003401c442070602890f00054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361367185 1250 361365935 361365941
    0x30020702040213060207063009080706110c0c090f0f04140d030515030a020d02060f090901080703050c060703020a06050705070821070f090306020d020405100305160806030d080601140d 81
    0xc804548400c03c0a0464a440b911960540c00b2030301c441210301c0c0c0b180408040396901410f412791044d00e001d81001c141d9181d51044410003040c2084003800028036214001c02001f41005c0c400781210025101c0c60701d009101c80400020300b581405414031f9003c2400c02c00074452a07100c86680008440d517682c5002030060113800e003a07407548940c021049101d10be904000c28076002e09a00500000340c4410755500b803040c00e6214858030700007070740103100c0b00c4110303a140500f080c003c0c50808000c0594908504000d0b003080200519988651401c11a9000203500851084040364010070b0000b11a83c42c50f0042d9032a00c91010300400600000a4210046140d004500c48900840761900170710f40d1268002e441205805000c0008144050004c000040f40c3e6002010f9004040c3c0c0094102540d40d070120701300340030412900c0086600e80c0100f1210b41500710410f2844e03000c0c1d00c1d000110f410104082604c940410044008005811002480c2d40c4d006440c0c084020014201141c0c3e0343c51011013017001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361368435 1250 361367185 361367189
    0x6160806010e03031c060801110c0d020613060507020c0607030f18080a06050c070c18240501080403030908130e0c04030507050909010b13090330020702040213060207 73
    0x4a0900408120694030a0090841ca048081c0c011898181c24009000145280c0303800681c4207616984049001da400f030050300082d046528030241c45520182004c2d06090b40305a00c4d800310361040f820041a4040c00c08044055031308000d0000b113607200c2c400c1c22804c0421000e00c181c4c00260015041c03007010f07408143c250807642070b0b5980d0154030070024000500009540b20340d480d2a03101100301303000314030958810740c1c00188540c0e40c0f80c908600c40d80c40784c2c0d204040b540100c201b02189060607a0342555806a150719441d08290f420a007603400c480f41e040e10700c890245c00d04100131500000e040501a0303001d050100c0d003000d01d49480b110040c5290748604160b000c1c03e2035117442d40001c690103105100c260743c16258814041c092550500080c000c0d856801000c110056499090025281c0c95454040c8025110403201003881221800c010b400c0440350b108900e0001c40c0d9502c403140e801d600045007881444090f00259840340d55000250183c0250021f4256061102c1070003e441500024a041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361369685 1250 361368435 361368437
    0x2040e040501050f01180209121219030203040c03030c05150c0c100504020d0b1f0e010504060b0703080601180905150103050c031308070c030501050a05010302120c030c0d11030616 79
    0x4074940e9007812844c00201c0a214520343c05205408076600303031086801601008402900e200480160603510b0b40ca04290381c04180410b07040092007071540348511102c544000c030380e801d00390310310704060759848540c60180c84040c0c1040041d1030b42c0d074104801800f0103910b090800c585031245061031100321259920245060b0901c1c81807921600c0e0340700880c040c60744a907400038030210540d0b07140d486443d119000101030500d00301000440c000142e685038042d00c0607203650040c015566062600340021141c0540007940c4405003030102e040001d81c80061203178000001e18196801c035940741690141340d0780c59003188501c64180310400800404050146c4c5010000b40c0c0d081c80b56468020100c0058481620441000000c0081d508003241002009020341c6100d414103142903a5661241400c50307500303841480c2d217162600c00400540c40c240c1001d419044402c4040c020141c00600060740e01c004e441c0c0300c2d5014210107407c0a042c03200e0b4480846110501909840491400340007410205d01e00400302d0f4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361370935 1250 361369685 361369691
    0x17010b0306070207030c170c0607080d061a220f03030201140601080c03070804020f0405090d1103040f050d05010b061306140f1213050118020922031209050102040e040501 75
    0x2c1e400510005658044031742041e4500340d400c1c10b26104801103421819440d10701d2180c50404183e540702d91004004c2503001d0b030307221a00e40d20b04103500d07019a04590700c500c0d40d80b0b030010741610008000c00121aa28854811907515400c1d649603c820303e4400d0381e102003800306d89180c00105040d0190044041d54041040344c126540e11200191030282084c0c03800c410360001440002c0001c2c5c000d914040d002400100344024041c061710015054408c00c45407140c1355000940b003101015044102c03401e2240040780610300346410400300d003010140ca0300c40c0500c11900c3c0b613100030030703c82c0030340c000c916091002d0241995030b100c95552081c01000c5214003400541201d40c100c40c0c0d91a0002903880003150700c145989042455500070030002c03405400281310005646003c0c0000b1350034440d140000c070701049c443c207030041280100150729000400b51100480d60054080b841c50f4140642c140d02e96042c14401040d04034046454010094000024090340c80004c0100305905589402c51056109500034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361372185 1250 361370935 361370941
    0x105030607050406050a03020f030a020c10050f0601030b0d23070911160204021201060f0e0415062f2d060106260f04062f070c17010b0306 61
    0x41580c4690071034500303000440c18482403181c144240000c03c0f07500c0c81c5240260405184d1068118a5401075a90001081d400112404042e00034003240c0c0c2c00c407103419000c110900d00f803143c4011000004142d6410182e45414850803a83e44103070007109c890b0045031002525486c00e4203039003844240c025071a220720039644001941002401540d4480d140030110a041506c00b2400c00365091000d8000c03a802a024007000740400e840e00c0a80b80246a25034401c401d0310340c00300d00a8000b00c1c021003071754022410301c40000240c10b1990580d108480c400c0c5812200f030b1060000950fa00406094183c03500800e40341d00142c296000604441d09100800c0140d00d41c0c24100c03984440d44a080940001b1070304808010090240203180b041107591070103022848030301c040d1388800350000c02100e81c1998503440c2070078481032050512840089690810b80c0341e00c141c05400f1a550020880e01005d19200da00041c00d03820440d843c50040014000800045451682c2484072030282010358040c40c002d11400d000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361373435 1250 361372185 361372189
    0x6150901030c0605031503030a03050103020406060504030c12020d0c0306051b07031b060b040e0303042603010909060f0507080718051c0c1a031609061407020d15090303050105 77
    0x41a4120303580314079210141c9143c00c900381d520340c000a210000181c420180610191803d000608541e00d055400044540c1544104011121140c000d8410040148000e000240c035999480c810780b42d1807601c0314070514080c4001550b060784100003c0c5090a101400020041c0b03503005035016242a243e04813042c07010b207042402a015048003c0e00049140507120310110f0300b040640d59160080d5000316258103010045029500d0b0042c1d030180360303440001084240080b04511140c6030b01081c0a804820201081100e0035000600640b54210382d510780260800240382c0c00104410704255090100d458500c00180c40c0103000c485040c042411056030070f40e00a584071310346090b103c2c000e1101d100310400340b001100b4081035180840b203006642e0004a04413070016190190040341d140385503620706e0000015180380f40490f00d0790080c090002800e011031604501c03034030349016010003116100c0c04c0303500005100c0c0f944001c000d0b050007150300300141c0031105600032900a5019850911050340d171001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361374685 1250 361373435 361373449
    0x170706050708101e0503030a0e041b0f05030a0f0f09060b0a05090c0a0c1704080f010c020705040504052109010e010e03030406050c0304150c020108060d031e020f0f0615 74
    0x81c80200001c1c1100050294030b80b0b0b0070b40c160241d02d510350300844594417000841c0c91342d8021040700c0041840300c034141c0319078a894000e8482001091603014103107500c6101c0600101400410041400b10200004007014041e50152500009404d0140300c12034101c603204001742034105041d54843c2c00d2040348040c500302400018116100a85506d8560340c5101006000740c00c050100d1b010400501030450201e600f0b00c8030400c60781040e120301c0e503035546061007852601032001280d030141d0b414042580c0e00281c02086510842e070050b01c000c55160303210314001d410031005107180e02e016698000d1198003c1900805080e401c0c0080e03c0780116584c05600646000c10006030175507042d4400c101c240401845003024044c003821403c11281000d403100384003207210040c45280000100511001d60541da400350f055900603e05850b02840c000070798500400151350300c1005098408580c420045c00c0e0710030007031608108550426600d0490502d50066101c1070181c850b0f40f05d00003003140c040c6191603c07407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361375935 1250 361374685 361374691
    0x70305090c010318050303090c0118032409080a080106080603010e030d0c022407031127060d2a03060e04030c030c020604030605040c090e0c0d060603170706050708 72
    0x1000800c000300c142030046000d4a0268105a00c50061469142c0094420005140a50307403800160003c2d10270300000401c06d902000400051012a00003000400d440b58900084840c01c0c0e1b00400001d02050341c0c04000d015200b000503c440d000091200080e81d120442606070381440d03540182c1038403210304243c02e0f034a00121050740b54004001e840350f1900a0f5010492160341030040c1c1c0c00313070004800d083c2e03070703c486a00100c00c0300c91060040217a200d40c144545403106104250312411f0080729030380303516480c00103013000308240c0810100742c01640c1c07001c040e42c0903803429000501040c50300000401900c00204141c1c0500703241c03000c207580703094000d0049400b0350303400f641000c1c0aa592607c0450340e080b0f40b90002e506010341b4015500250710740e40d000b400514000c1c1404900740c00c0502d00b080442e89554801c00100d803504a07005041c6030040382711084180115103c5107030003a1410070500030901580014000241e00d0941a1110715000103001e416000d50420000c56030744c0303c42581d01c00012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361377185 1250 361375935 361375951
    0x280b010f0224060a09020a020303011410081503010e060a020c1207030507170408010207060e0618060c0c100e01151a0409020d0e0d05130501050403021003271a070305 73
    0x30036049440488404460340104000c161300b5006a07200c0c00c00c4101d901a0000b0350060308000014404401d034800c4e01c9006c43d41c00e40d0400050750164500524450019081c410b502c5581812003140d503600b508070a07941d003030110a0b588642007420604000754400d02d0a080c41d1300502c0e42502d00c0350007440a90740e1160b019200c561034000560745007100c00800c0c0c9807140b80070b0024030021803241390901c0074054452060100068580c85540d40a18000d0f0013021609170200751500048001404102a0b410040c1e420005445151010f141c904180751039015010240c501061303402c02840540104044000200c4a1030a55032035090111140210903414044031908000402115115038000d00100c0c0038000c000132446c429003852800c2c41030b980780300c000092010039482104021100300c0300080909080c020b20b41480c641c00b04620801c1c80029505240c4d49420080032001c4c2c00caaa4000a80780d114101a40c4006141540305082580d04d40701c1c480041c040020340c268043e102c0c0c58016200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361378435 1250 361377185 361377223
    0x720100b15040303031a090601171009150f1706070518040f050402032811030a08071407120305090d241b05130608280b010f02 56
    0x6251450024000c1444003a401c44041c01c141005850788401a0001d98440d50300481c40e802030140102c5400ea10700c555034484c6098605003c00c0313a8000ca1100440f500c881d10513041075840c0039103220551096805480c8103401d044003444c2402c041d5440d00b06940700a00104100d6841d243c001211543c2051215055800706000c19000c0d03004a015000104a02c07500701a2141e801011030181c50b0740d4806a41525141c4061004620741030240410070030803064126209403001c480035414010341200601040c0a0691018950310280b00c05004190480700681d55070201d4580485502d070360300503928035802500030206041d1481c00030182501d07010f56402c0c0c00c0c50728000410614503410141120308071070329120040031440f411000445181c5003031000070001005071805d644032001d20120010040e0802c12403096102c484544010b69100340f40c2080381e9950300c83e40d110702000c01c503924401001c0e15003801e95540c00e5034015200c3c45200707070390b01d44610910311001c0c0c4c0c0d85d072816040c100400403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361379685 1250 361378435 361378453
    0x3020c010e0601052101021e0d0609051501050c07080601150e01020c0f130e0607030c020105062707050d09080306030d08040803180304090c0923030a0b130c06080720 73
    0x3070300c007404064003425040014a44030403402c0c4030f03003c2e821201c40341104230300210310100d959000d031003040c0042c060746100340480c0c80c0800384081c901d00c61403040303414458046031007020706804104010241003010200c407401d5848404940c10000b002500400007280803503400b61a51001c03503443c0310b800e0068030001504920108210b4260f4031102400b083c50398a070070125561108000090059125441c00980241c000600a00b514402005c260044030107500300c0441405816410348080c228038000c00072500e030310394115441d01c125000e6000e82070810741c0900900070140002c5020b48012011102d00c4005c0c03400c10b98078580111805042d00405100003801200f2680300a12000c9890050382e25160311150904200c4081944400c0000c044520511010361965196400304149082c2c0c1c0e5000101d0000003640c030301d607000000300b200e0184008240107100c5580e0810056038482400d000d1700e43c03100001000d40c171046464200040380000040380780c1c0f0000c24020030f025000070292104403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361380935 1250 361379685 361379719
    0x7080d03110d06140406060e09010932061c0b07030b010201060506030901020309070b040305030f13030209041a0109091e0c030803010b03070e010306080a02090a110a03020c010e060105 81
    0x10044034500070303030700c601046008524800b40c40b0f401c0281051252014410524200340000c4841c690070210604c59450022500f541d00c900d502411101c0f210408180b000c90b628255442141c90304a64040c1000c101c45800c1403010746801c14481c081c141ca144440c40d204207000204c20b0400e4a020703101b10b45020208079224803c0e040b4004065040c0008540e4503034410106404c1d910071550051565401310910146032000d0001000401601e03003000d0a09045031103180c0c4a11407032003059440e000000c1c0c0000c0d16090400c04070010340c1c00814400341c0d03160a040808110891110801503004d0050011544415a10a040c90107400101441c5078503003002c00c0761030f0304104407001e5a0352502005d0020009600000541c06000309501564070b07400e00000150618185c001164181400e089050164000001d5100720841d01120001d100d61900c0742400010100807014240240c0b00160070117005030144c00410b035211044000300003d103910420b6589130712082c0a1240d0106054900500003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361382185 1250 361380935 361380941
    0x10f0c030e220b040b0130110f0a03050a021c0203040804090207030513050a06171504150501020c09040209010e0411030307060b03060906041e050a020909010b1207080d03 75
    0x20100140c080003400701e61100102600c00b4240100c1c42142e01c5030b02201141c101401200c5070100282001d00c000501c1031001d004039403111300d22000d0342e1070921014a154600d03401c800e41c00709400300d100f680c98141410364004d45d0700580b075030408642002c020880c04041442101d1901400303201003815046903072002d0019601c06001903811100c240302c003040b240800e200600c80244a40c441d5079540d00314804007030880520341d00c114400c1c40101410401141c000d0002450f08035070b118056941d5407200070025600110701c0078150441e103401c1c403070070b20854113002a5055030002d808072088054400e041010024003218001c0d0855600740c01007010900b911600c0d50006d10440180460040c1c038004a0714581040000755010f644841e08544903003000d2001c0b5800c0765689024103050f18198890014040e090805810051813050201052180070302071401c415900408003000e60900828480c060081c0300c1100d881841c035841c60140240000079603000700c801520181c55041905070080e002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361383435 1250 361382185 361382207
    0x503070b070809090a0b12010915050a1b0207080705120a0204020a0207090f02030618071e0903050f01150f080c010e01050d0509070905070201060f030f0311060a020703030b010f0c03 80
    0xc640d070610140503e5941c51140504c50740382da050005103008031200700310764003a200d00490b0050345000c64003804114602200400c0f844021000b142c20b8551000ba0030050202000c50010800800403036129281e0100705181120405000c03101d8280c2c8078010402d0840a4415802140d0f005482110042c05c01d40c0140c41c3c189264010f41d0f02c0f440da5203c8110941740c0c24a00c00401036400403c0019900e440a14622038040f0400048510318100401038040311342c500340c522442d0b8061034014a6184504c0004001c0c2d40e200e415961210419508e0502811404040210041d01c1140c040f030350402a140d0300c401c403500c29004144e0b02a200005460b03410700c111800c0d042040030402402d12000e103006403401507401c03e00030100703149044408000c40307801812410459040c642c00b00500080440e4040603a50445aa85100d0b07100b032a00380d408508040c0201d0090240e01c0400200c141168083d0403c10300903141030000319011801102c54894003016074012500e1486500007081c410111500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361384685 1250 361383435 361383443
    0x1b08060d030e03060403050703031505090402040b04020f0c010207170a09090b03070f1418010b091c0204050f0103050c0607030503070e13151802030408041701090c030b0618010503070b07 82
    0x2c4600b1466020038200380d02140d00b035021903030016401e8200742e45031050080c40c640c21025a0702d030a0422001541a030005040030f0f20903900c596044041e991a80e04031400c0c26008601107940f20140d01200d800707500120f50645424001c08803906002410208407000c11403070350350703003880c041c1071002c0a4001d0415002054040c4565007011440078a40c611941c09005041c80d564a031408040c10024148840707000300340342200d01401048440d1003001990502c0c5c1e0126040c828524100420201070ba4500d400a940103061000b44690101c2174440181603901503001d07681002015010310150348a0303140010001601000043c0a0342e114081c201c960040c0141260725007071680b88440305031119901044401c0011003410070200b11030506907060800e030b05109606500c2c02d52100c82c5103025034802c102c1c0d980078441100304030400a512203030115510a01c9071900589a00340100800f004035071840c010f01c01c0402c02940000c4403229141255401802003810508040c0301c0e20468205a100f19 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361385935 1250 361384685 361384697
    0x5010b0402031b180303030c0c0d0315170111030f0412030b010219020d020307241809021c0906050f130c140d0501020c010e0c090f070315090c02101b08060d03 70
    0x2004c580c0c00b80000d41c00f40c1401c562141d215074103421402d0801180f01a2101494a08510021103509030708804088600300c10f03401e03179444504038505024080b00d000900d8900c074004100010100b0724100c085c0218010000b000580384290001c0d01203600801149008d40d0145008040f0500c5441d21007034454406003030380b18145001d901003440c0100701e8010494500042c000d150048c0300820b50074600080916190706403504081c1d690415500742d0160039101c45e00000e00003c08100b15030300320b0412859900421040c441030500e40c004150030750790400031032180f00128101c006581a09554140c01145520510380380c400076011102d14003005680204900d0f000b000880c1c001e1014120b1110715200119252070381d4492181040c4040d003c161090003490207200c01490140d1145130b00111500f400100b50790110791502e000b400030751003c00ca081c00c01030b2038071030613902084d48000c80c00b1a2905011446001c081c14900c2072001a4200001d43e5160000d4100c2c500502d4020300c05000307041c54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361387185 1250 361385935 361385977
    0x70b060d290603010506272a07020a0b07050607120e0114090708010e030a05030604060504061d06030705030d050f0903070b040806071b020f280305010b0402031b 71
    0x841c10001200e07070001450070031010000c49007400e000d42c82c0d011104842c0d4501d24041640000c59100b02108985a420200c6000545400d0038601c1030300c26410762410281d043c10f185115078816400248100d00402034207000044104030401562101580203019000507582c0762021109082c0b0b1a41e40e0003016100d81c081074016000380300d43c0244d8028009440c0345032500f6007483e032400040340d00454403070b89080c04c0890710b01c4010040c0c0380c40d4150b602d80b4070390300d8a403007002a018000a07006641d009190810000d40c945504d0440320080a50100102d059034a4008042d150812449070b42d1300b580042602d001054402c3d0010f04d1896074200b00300e81052a81800b01e0b1078110160441d0311001c200140c2800b10308401c0122550000301c0d41b42505150040703c518412551040d0002405240c41c49480f660540d03440400388003c0f0150021107a51460400a200c0035074440d2005403015482d102080c500c3d800e050088038441e90510f1703040f000031600f03401c01d0412540090070030034000e0800290 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361388435 1250 361387185 361387223
    0x1052d0a0801020405010923100c05070b030a050901150501050f3a0207051b3f01050402060a081b0304031805100f03050c040b041e0b070b060d 63
    0x120030041c209410005840358200000036050b50079580181e001009101407002510000061219450390182e0380c1900500300d600e41502c01d00300784e0b40b005019015001d17000c1030f0080090051032180d5000402803005880300000795007200d8841a500c0740d1404603990600031540184001c200c1e1031b2540b44100e2034114a8010074642d0307110b42817600c2d0414a8024070300008810503050f50040320000c0303400c6181170b18981c3e4007642c510554070f5030281007071001058001c036912007200d00c07881c6080080102440d00c10602c02c42e040d842d80c50589901030280440d40010000520a251099a014064034640b07103400d5010b403400080103101466506003c80c4080c0480580c1014600442c880d4581d48005800300d10560301c220103d402190003a83c015130744900061744010440c182400b14240098a0340718284510031600c100e4004100901c0e0000d00001c110321100842d244c103070b03c00303c83c0e070a40540ba14180041840341c80006421100c0703900c086000c4d45001c10380e4144091107990610800902080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361389685 1250 361388435 361388449
    0x1406070f08070303050c030c030f0a1d07080f010606090e06030f03040e04020a0e07020a0b06010e0307030f0501050c090607171201090b10110d08060d02030304120c0e01052d 76
    0xc00319016a000314900302010f0b010300440d40c200d01c82506040c1075107000e103007500b100c0c00010120514034800901181c030440c110b520604412140450016000103813801c0ca91b655556071090441a10a401a01862031010700c0b40c00c0030380d4480e03607031850640d14144000500d55406064140d0600900d11001d50116040000f04003c142d400c03000d10a526290042124026059004055108a0008000030554045411248103a0100680310700d6120080100e450a607110500d44d0948103550003c410300003500246002c85100d0b0000340b05503600c600c8840c40502420150036044201030100b540011030907104000340140008034641440200c030321401d0415000e038402d10b0300c0b5544901801540c100031040900e4502c46003804681400b000c1c21481d51001100d444600b08007100c4d0105005581f4140e22221840d00102141c0e221515621161491000c0c444200c540701c1c0341090014210480c0000141298002802130704082142c4001c05901c43c00504040d004000602c5c00c1d107455034a1070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361390935 1250 361389685 361389713
    0x130609020a05040204060f020610120b1504020a0c050118051f0f050a0914010c12020c0304050402070305131d040303110c01050a0b0a06142b0e0303100e0709140607 72
    0x10740c6205051641800107400d000010708102b920303407407005041c89015034010036212a1070740241c50440c0c0342e40300c810078900d000c03440000b180d11900002d002141d02d40d001d100c194049001e500204038132000030044d413002c01d640c600028402e402441400340d5000c000318030500702d0385854801003400c054070840c0030116402101d0841354156140d86802c2030094020809860341c1803800200205241440e01411043c010700107800308035000101c00010708010300c20340d8000d002c003a00554440c0300c10310700030380b2941040c2c41090500c000c026000402500d08400441d1350840f81c400750781e240c3c485450480180200403001b8008807410003c94061000034400e00d48070701c4020000181000d2440d080003061440c070b83c0308404200100e48e404440701c040c00d040310000b804140388000c0003c04c1d00046017021900c081c00040785490144090246c4e44088025882958075124000c402070f20307902c03000607114041d11075000144d40c201c8144269000226544039602c0c00504450504a450381c80910600040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361392185 1250 361390935 361390937
    0xe0c1207170c1e09010909140402010e101205040c0302101707020d0504170c06070b060f0a03030c0303150807060306030b090708030f090a09020301080a051005130609020a0504020406 80
    0x7440740c1d0005503a89100007a00300c084404064074003c140705035402e00059280a80225403070010780402141c2c020694080202004c010911262600c1c072031817880303541c00320350a81c0480d43c0c0f0b0340303030469610b42443e40340c020000a44883c0501400441c030700004140041003120702005048000c00565500051060004090303a40c00c1a4890100600302c111701d80074081809542c00320b8032a5925a40110540c1d043d10b001b200280d0421100c0c0002610345002031440c1604032200145080c28803100c05000b6208040a603140300744180e000041c00a50f000d180300140000745002182400030341300760010b000420703080300745440fa02e455113021410321a181c3c1c0940003286c0d540208108000c2040c866591000300b040c0030f007082914250080343c503440b0f07503e60203840100024240034595113962481c0b0140090b4501103440707603101c00a180d5182c04860381518284600840000114660302801d489440d10107050500020310b0307500d0707102030440004103d901a0348107801044980b1284050300c020115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361393435 1250 361392185 361392197
    0x70e04110d1a0a0c111f0f0216120207050a090513080307020109050610080a12031b17090c0f060a0e03060a0504021504030218090f150a060501050c06010e0c1207 71
    0x140e440c0100da643c03003440340034081c440300c40d21810178000c81c440e81c580844041002082c100000c598000b4913003840c031000c14030302c0480d58a810941906803c052140f140d001c91200841404d41aa0740d00c405200ea9540004180014010346200c0d0300025085100740120750510310980d039602c0420b41080701c00b800180e5507010340c401800402c000f030903002402a041c0c840c07203d050081320750b1910055900035050159110942d05c4452095100081809880c0051344c806106258000c01400b50844664549404c000210309524004268030500460041418101c03000500a000302c2d5000a54503109120303117410009002d8505011036445110800d50005591400b48104008401d00181d100043c040c14001840144c40d00440801541c80b92103003031340113603103081c202403030000d4500c02ea000c00e0007030355401b403a202c60140f9024002c180b480414400036498a004441d0382c003c0c0d50445484e6800341c00100511481c074124a60800a0300070154940321500d400c0004840c0d041e00c0c3d940000d50307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361394685 1250 361393435 361393441
    0xe0303150a0308090103180605070f080901021206010e03010608010f02071a01080303130f0206071b1e0b070507120b0105010f0e0102030306010e030304080a0b100503070e04110d1a 79
    0x508040c0c000e80d502140c1d02034000381107441d000400d00500382032a060513510002c0c1552055940a0815250f9200500307000a1914110081480240e100c84001042c01040403d103c3c10040c000d661081144042c40e9a00d82c2d541d40046844c03003e10461242c241d541c1d80740c0031a15500070f000f44c2160303034a801c4002da5654528a020321411108d038a24a4040040c20010300207801e010042f26003051842151004402950900d440c0e100d400180c003e6000390000341c0e840800c100004500d017848601140c1c40e1141d942d4079014105680c00d0300340c2c0c01c0c1c44221041d0502c840c0001c6000342091a00803000c440c4501e45900154466200404042d41c1030300301000100580c0d82c0c0b2210846a812a500c1d2000e04620b07400d002175070328000646224180040300501083c1034800308140c400070040721007202e40341e0b603c504290741c0001c025506c00c0b035421508407000c44d02e818001408400c8030840948034081d6680c80e15400040003548000342d6000e050a90300c0c80108a0800d000340c04041480004101c1d41 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361395935 1250 361394685 361394701
    0x27010204050f100c080309011107050c040501090b010c021e0a0303051306030218040e0a120306050405060f061b3a110c040b01030213080f071d15030109060e0303 71
    0x82d60603501070300c511002940400c25507400642c440703481c3e0b80004074a0700c0340c03100c0e50341c3c0c0d01404071407001e81211140420314005024000800f04184901a10700b0040d036621985404144c4514051072408a503e40004c02d00604291021011207541036500030a00a480710000d454000c003540140d00080d030120328043c01c594001d1150700140303d1410b046252080710b1400e1040c40200f50b103054803c9545804955114500f400016201075001c1d05000e411003200c0c402900400c0d190103040e000750700e090001050740c248200002440e400051149003001100014000c2c8000c9140d4440d52901400c0c0088085c45010302c00081020041032803107640300100c1301c440c141e28a5548171141001038043c80943c100340c02095001c41040d00303840c080b8000b00044016400b80c418a502e2007015000700718001006540812a502015044c0342581e480aa5410f02c8009030040e05840209095600d000310341c0c5a03480803a4034100420240010410700c06c203858410031100c55002c5400660000010040d0348 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361397185 1250 361395935 361395949
    0x30b010e01060f0806101b0204110d0b0315061207080f030406270b0328020409050f1e10050306040c080105010801020708030a0b0604050901060c030f05030411092701020405 76
    0x619851811344003c0c60040300103081d002840840906100c15444003011807880100c02c83c4039107401a00c18405030341b00388100c00b150780c0910341c0c82d9107403450309280c25614074001c6a01c2c071244c040800030200c6900c5241c100b10450b2140c00c40f8054a1040d05000121040103100d0b2048a0300701c500510788852a0000140c0300e4641712046050390103040c440e500445468400480544010403000d075100d079a10b4400300c03041075000048901903800040b4204072540c6540044c0b090790320141d414803454503000d000800e0305405030340312070f034501038020031460041210f1925076018142c0e01e44d01a1459503400400c0c01d0420956090340d410060010500c000e000034001d01740104483c1e002189032202948031840071380009040c0c01d25450700d414011001e581c0782030588000c0c1c840105000c109503500e002c0608180007000003107001ca07404c0075694030110b0181003542d1080d82c106001c0700c0000040000c000b5000c40040403400b80c5440a90b4500c2031044101c500c4021400780000180e0701d5041408000070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361398435 1250 361397185 361397207
    0x3180d03050f0a090819050d150f060e0a090c02010204030b091c020309030a0803101703130501031a061b19020a15090512030d020a080f0906040b160207030b010e0106 73
    0x200350620090500084207201250942c040b041a0000c6c00384500344200c0e424030400c0b186d10100d074100b0106a40703880c0308030106011217900c02c03801039916580d18000c1e21008014403000380c0c003c46090b400c22030300fa0503030402162044a4400180f905407265148401180c068990071415444003140344610411003c0310003500e03190740000d40c00e1101140000e40e4034964220300611403000803004c41d140c140a000f81001500700000c00521220345112a00d03940d4022000c4103184900108000840f9401380c841c104811041104d0a441d8a840600f405415406021803c51101e10104c003031100c40c4051100c800300118600c40c00d1240c036540e00401404140c1a0810b80d05400d0b01c20000c3c2c0c00981110700d1404592081d19000640e41c28201c0160940c01150b100c43d1220f4000980c3d130395030703a0340312841901c603e00c3e00c1201e94044d100c0c0300059a0702c8100701d81c001c2101c25003101045441000c1c80e1401d0103030310302d441107a0400c0e0b20303a03603003180300764003030340a142c004160f04010700c00d1640049080724 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361399685 1250 361398435 361398451
    0x5100504110d03031b1713050a0206250b091212070309030504080f0303070f023d0e0f0c010f02060103080304020d080a09090b0a0b070803180d03050f 66
    0xa24103054880e4981103881561262244403044281400c050281d00b181a480c12044140c0d0b00b40101810054a02d9401ca03100030350f02c0c40d140300007468002850540400903600400145081d085030b90074092650b2000d440d00c40480c1d20403440007200311841e03c011352010711604c128034017420502c01c11392820b01d1603032204103003140030301500c580140d02c90050340c1d2043c05850081168001802c0c00d071024425600f144a40f40291704640c8070044001000754001d9489564400080312910301c00c90311882c0e0090301e08140003000c200810840300c2c40741c0407a11100449020700a625205d0170807801c903039a500061005130403c16003103855030818840c100c0c4058003804c1511040c0204c00303009484000500005110f028088081400d5403522503d515216511000c040d60354100c09074041d04e81c400500c50004050f0a201c0000d140d800d204c600c44044591616040e07003849038960700e03035943d41c10040461009900280042009110811200030052500e4500040074240304950307441460004bc00c1c82 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361400935 1250 361399685 361399691
    0x90d0507090b1503040f02041e0b01080c0304120e040e010f0f1812121e050603160f090b0609030715030e0105010608010e06042a02060901110a0c050a080706090510 72
    0xb883c41c443c01d004417544181d2010502c921856648001002041140485040343e40340300c14402034041c00e5440702d42948401d03203549146580e6826040000d20040741d00602490002c1e6042144601500b04100080f20090001c00d881e42402c5806007110540c6884921040d00c44994400550181c850480c0034102764001c00c41c2c908191311401401034860151034100040000540341c1000d095100309410170b034144600e60380450340100840a800243c59061080c01031820803400700c1c034054135000c00c031504a11801100d074030304851080100b10390fa14980d04080200005540c0d50340904c0004080c2500209071080d412126100a00300e4400300c51009d0075a143c040140403058100c2c2c2480c0c1116151a00c580c52640e40d400400c2c007418044100107801905042170f040c1280c0807841036045141140d003140c075580da1300d114903403c0e1010ad161080d0324030720400045000e54881c0c9a00200d80703010b8011502e40b1442e590720b035140c55104610544004e41d944104d401004014419031020f125901014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361402185 1250 361400935 361400959
    0xb031e0c09030a02150d06031113051012030e061216050408070311061210080d392a090e121b060f04020420040e040305090d0507090b 59
    0x72035a80d081001e80a40301e20342200c0c485c90200088803c440e400e110590342030083c0c960f2440d20440d20380829403001d12820030000607070000c42c41481810f00c150309019012180c10310f804121909810600010340c200411603015500303640300c7d140100b9042400700080d40e07142c5050031000c002922481d07002001c0160420040000703400010710a401c6d01c0d004a9442060000b00740003030107a100d030400d5000449090420800c400551100010844000d0340c281c9020015054007120700801c044034070313059901010504018500715214805441c40c03250071410041101d17440340242c0b1810a440c80c0c100c00c800041c50301c90746c414011800c001b0240c807c01403100071a2105610b031240450224040b01d100042040001074038941003e500c1c0b440290141c4006003020701000d0170801040b201607006600700214264030b019901c144201d070f1034035101c1e0b540c10700381040040b1444440c003600940410500384229281d175640e0000800c41148240c0003040101c0c07514451805a4207030551480c822032000c042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361403435 1250 361402185 361402189
    0xb030f240f040c06051b0a0b07081b07151104170c0a0305150403020120040f1a070b040203030403170d0c1409041805011503110604060c0602130b031e0c09 68
    0xd080141d42881c20107a4a5030354517030100510000b4000e046c40c143c4241481c000c240113491017114025415962a08001e035100f680003581303908403c5c0344000d00304040060801041c201020526011294000425070310170407070800205401c0b0b60044407240c071894501c140500f00030801442030350801c1e103103400180d1440d284c0310345550925850800c0110b00b100090b00b018400c2d07000040d200c040f0202e2034600c44032040100e942d504140070b0f08410f101c19000210320310f04540341c05100042c0c0c0f840030a1900003203540d0740c1094400988120b03050300c001d10005c07000995692510b042c013907000c0d0740f4603100c00940d0085c1d8181d4641006000c1030281480118072a240e400c03040b5816008251270201e43d04904042075005076840044c0030b0300551070078480105081140c1d4402013201e000d04580f684c140c0c1c800040101600c02e134070401c404200003064200000701d090300a0310b05a20388800c1a13965603980c0f5480003195108540100c010307080390381c0980c402540f50100f643c101e819600301a09110032000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361404685 1250 361403435 361403453
    0x4050906012103090909031403010f080f01020f07150216060b130c0e1908070b03041a0610030e0109061a01020f010501050d33090c060e01120b030f240f04 68
    0xd441c1c85c580c0c0329001710307052602074061007034020001620f240d070b02d41c0d5500300781e5003040060007008a1030296090800000205009880320201502200345c6084001d035291080a443c1d1180c2c03098542e002d1004d80781c0811085d0310f5820744e034011a0049000104101040131072040d8080201d48640751925010503d07a10000b0b03201d032844c00f641c8403000c6080c4a900c00c0c860025039400030390b55104040002ca0894020005140694415132248000c0001d0b103120000c3c99030b003143d00700c0c1c0110140306107040040c403940102d600c404006000280030030700d035121801601c401c0301203900000e800041c0d0300d0080d40d04005c11001c01c801000201f01e654109000a00a0700c1c0280b40580b140e90600e0a00040403040c018542d10440004c2c01e40d6444003c03504100054410b0940a03199841040400140d144c0141001c60600c030701691010400024550280b00030f100c8091016014401d401442000c031200708000084094058000110604040400e00704c0f0306000304440c80000464050100041b409030b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361405935 1250 361404685 361404689
    0x910090c15210b0409020603100f060f0509040c1b05151021050c100e040c030605030a0210020106080d0908011503020117043206010f05060403021e0405090601210309 73
    0x85010941040d40f00c00203014024644020f58001300002c00e009180d46001084000c44100c014503400c00c0daa5200242e03516142ea90074040482c2c4108a0310140e85859030000e0386410190030303e05012540c500c08407000110512049a46038020342902da11501c428601039409650300048090190800004010700f071110810b404000c0c86c0040b0740401c100301409000000707440980306442507001644020441c0c880d403240180100c0c036040e61034202500c240111001c0d09d60180007041010f0b40f03a42440088140d080050085550301c500105d107541d810b01408400c0180d031744c1c03008415410b000c542d5084451003400b403501240482400c10040c0d0304200030710910254000140c943d65a83c1c20b2902420000c14500351140084508543c0c04807051000104000c907280c0440d20541e890744021408100c0c507010382030f03015130180030410040c90803101001182290031405228851341402080944a041e241c08101d500082c006008062140480081c091114510380700481c0540c0c9000d0180c408078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361407185 1250 361405935 361405997
    0x15040f03030507060b1002100e01050f040803040c09020d02040f0807060e0d0503090604091b0c0312020d540b0a0209030f0d031d030409050910090c15 66
    0x802c01c3c20500c5190361012840c0740c1d000e0540e01c0e0920768480002d4550303210180e203081d8180340104407a0900c0f4144038042c81215650b03030601241d22151602c6641c0d8000800450b148989c8180c042404486030000d40070001d029a00561164204900345440d640d080c2c106200340d0703000290401a00b580103448894400b01903544008805050034181d0861041946c000c7e00403800040008141500e64080c04484c034200500d0490480454811a0481030051002c1c00242c44903d074111170b07030340940c01001c0010070018000380d1010000ca8004504405a80b86152810f1034003403c0c180080301403000c14035000d551051080e01394864440c040320f07441c000003e410102440b00040d400c059541c1200c070000c40003811143c8100d81003e0b05552141c041c1c10801c00241080e41c2c84042039805415200d100c1c4041001d103040c03e0408201500500c0700070040e00c0a40300d10f03603125285806521903c0310190042c24500324190500a00f04501102c2030311150400c60384076421015111909500d000c54100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361408435 1250 361407185 361407187
    0x109090911040b180103230a1a1518072a080915030423010e0a0f020301110d020703030c05040b09011d120109060605010507020604031b0b0a030b15040f030305 70
    0x208808500b085544181d0b07410f0f00451a00013105000c404200c44024180b40466040d080907032101903512038508e05030041401c1808848018030102c040c586542c0a4001c5030101240410600000d0018030520440f041c20a222001e12149940c800300c80034042c0c00198291904e03806054801c4968800040040c1102d50085070150799942c1b94010329502d6040040c21035102e0501d418410341405000d00c600b51000803104c2e070983c600c40d06015445100c3c11030702c09800752000d15100e02040c00a82d203c100c5c1c0c07656980c00788030b0000507104050001c1c070314500d400584030500352402504441c045418001448028841040400c3c541000c44a1010003842d094243c0340b500e046421280c0c00c8a040305034000b03045000c80392500c030158403c400031130060300c00344210307569000107444500c030384030000c0d4000c24200014000706604411001d8400103509e03441400c0c555034022003450707400040c1c80340c000030340b40c51301825185804d21801925007010388440f0b203050314000304d080380c60b030342480024240700d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361409685 1250 361408435 361408451
    0x1c030809071703032a0f1305150315010216061110020a0c0317060117040503071208060918071404021308061b0f030f15040c0806010909091104 63
    0x20341400081c0080c0100904204407802c607800c850349039001100c1070003051801d100140d4103009a200d144201545511103240382004c95014a0305a5202003903c0307801441580000449490300c040703c265444480b0350264803403c14413004070031a110390032500d045501c542c03401c0c1d004066041041e0300700e0700a030500072003e1f0101d0a5503820810085e205520051001c280e070342d075542d0098541d0001d544280d0300c014804038490031601101d4000d4925a001441200c80070135042c21b031810094000b405001100e080008580d41c07040240c140500da00001420b62003032003100d051241040303400003c001c0400554403241d0f1022076840d43c1c14400c40109c000e007001d411009444035411610b0050514403fa80015203c8903055030700c18055648400c0300043c0d10202c1c446240794425100c070b500f01141a03505e0b5407034030b10000d00c0c03030390015084011a4050104002e801c3d070722403203a4060524142c4445150345080800941034040340d601510f1500d081c0300c044800505828544102c901c0c0880d0300090102d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361410935 1250 361409685 361409701
    0x1808060f0603160305030c07090e0715020a080a0903020406122a030c0e15031603080304060b04050901051803070507030f080c03030a0501050307052b03030e030d02070605061c0308 79
    0x400581e440801c50f9414880202c1803240c0803000b4001b55004c40e080350001665038035580112440201044020382041c0300078490910040701d0b0340750b124811b104440f03840c0030603250f0903130683c401d000680200307403100400c10031400c20340102ca0040650342d141d20300c00300c0b41b81c4401500040103031084800c00c3e03422405e400e1002e403031b0182a0246d904050240c02050312081201e1502d0f10550701441e0b110b51742c65109407685400036420044402802c0c102c2d011034a03543c4e8030311464001070f01c21200a601d6401c3c000e0141c55a1160b10301c5810080d0001c11542420041c003801000d03031304580740903078004000b07103004504006400c80c03c07290f00800c0c1808240d524240034005004850380896140800414811000e80700c0c0c2155050311011070655490a070755108100303004c00e10340a2501d080c0c196113040d008540361a00c54260160007400c0c00f050700f0088c1042c0d5411a071010701044289580072035030300706001e01d41c40340540c8100c0c10383e0030900081c5140d01350060f04151910081c00c100055001903200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361412185 1250 361410935 361410943
    0x1091b21150303020618060c12070504150e010f0f090e04080d05090a0b090a330f020d05060f090c070302120301060c110306040b060d0201050903030a0309031808060f0603 75
    0x7030100095060030703003a101d02d00291190002d440140901700105031030034181c1d4020a040e401180a1400503141c03406240b45804501e200a00070000e101d0207210010341412418451070b51441d56a4034404590f051400140100000f8001c078003c0085440444500c240c111b0034110a9841751040c07440195118035024955200f402400c00ca10b60502090110450000600c07540e80d42c400c081c110400d90310740e0301d10780c1e03900f281a1b000742c600504001c0703c1c1d002800200000c0455000301400414039a00d506c0010252042444081680c5a0024500607981070b244541c030303040341007150030811841c4034500055910f900500844044100000c2e0042058001c101804496406c004200d803070b983d4500001d04400c02442040c2e400c03252000c4091018540400c00a11950740710807080440d840b288107104441d000d9013070407810b10800304200d0802d0740c0e0402c040c0001c0c1916a90208040605c0c1c940102008101400070300c2d4808510340070b122054002c03908070341c42240202c01001030744d030b07520000c1d1074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361413435 1250 361412185 361412201
    0x4020714070e0f0c03090c04020313170d0b0111150c070b0c040303030f0902010f1110020c010209010e100e060d090210080f13021507020d05070e01091b21 68
    0x12403040c014001942042d50742e206100c0e00c0d1080e80c1c44080d41c2c4071864440f8a100031207101d41d40340c0004041e522245815800703103800462184030b48031103815580e0703003980c003c1c158042710700030000105003803102501a00910341c11540030301c1d01d0081403004101c0c065441181207100b0940140f00000904807030403d100740e401e40d68010030b1700f0307050741400d050007010b43c1c3c068001030b0006400c1903041050081d590007080140b96040e0f40e545255219180d0840710b0380072004601d4282d0096031000d036a0301c0b01c00e00242121000882c00103a0782d0b10034a0024008404110495016251140c4030689098101c2c3e45914041c0c016620141d95002c20100c5030011700c2c2100d0001e600081821483d41000d51111296128603244001101592a045050341e60302d01300d104001e5100c04200300414000314440098580d1910250200380001c6141e580d082c20306125030445100003804900400030f0f40094094281c24281075050200c41c5c14040000405400c0c542c5400140343c1c2100d160280d4007a50395009c090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361414685 1250 361413435 361413473
    0x15030b0919030309050c0d200102010204150915020c030a0b0a0204030807061406091302130906092103050705040603020c0f030a020a0201030b0a080613150c090e100f05040207 77
    0x141040749150140003010b07408019282817103461040e200701d0500c00c4010594a410402c403204518046413024113142c11041c0303007411035408ac0300004440e2508500300f80a4105a00c1d50350303070541052800360f21590300350b5801c0210b500180c0c20035065180801c0510340c86e60000d9074980d039a03035968101406032185900c0240032150000c0c4072401d100c0340358481082c400c40c8184502c0c49445200c03c116054805603810f403076040860711030380f005180c045181d6070b041d0f0806002094003041519214202d035040c8405507a4402030542ea070b102280b0b01201d030000080740741410416401d0000000304240180d009110525a001400d80c031050400c10800004100c00c0341140d42d42e00b1100c4000351203000e0303094202d01103400e041c01d0340700d54a0101030a00590385c4500040c2040d9441110484404031074000c1500c0b0420b046005111100c07590103040c2c207a0b402a00c2d0000164688007021110050081020000f64601740041c003c0950035800e000c1145d40444004d6226030141c00c00806d91940190030031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361415935 1250 361414685 361414723
    0x10f060324150609060813020307050d1e0f020307060507050303240405041b06050f030a150b070506011404022814120105040b0a06050702040f0f0519050a15030b09 72
    0x2c3c0b256800000034064070100d54944205440c1c2c81040010382083d00c40c002c1d45034100072001c8c00107003000c000200c5258044d04082c0910f41909410202665540405403080703054800c01c40d040d41030030015000188140d01d00070340381084a0700c407140c40b400b02070140120304044030b9021404d4202c500d5007a0125800502c1080030b4241442d080c48042d03854001d016940700a10000508036024006840c1c21b0449508030a20316511400520001c01c0742036010703288070600160105044036008003401c17405d441100108032a506000e042120a904024418441c9004000307803c4d00310841c6928130541c1c80342461910724110180c005551402c1144940c2c0c400f0b50002c110002040d0803881101e04980303080d01c003000500000701c288064105a0b0281c0c00104070204a0b00740107040a5000c0504040d01c0c042c0000d0b05100d40d26441c00361242903400101005110a1044100c2407078441c0a42148101008203d071a094107510030780007180d48800303084a1101c10004003481c000b413090314440c02c000200c070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361417185 1250 361415935 361415939
    0x3010c030507031109130b010c080c0106060905120d2a060b090705131202060f0309010b01091401020c090a2406080702010c12020c01060323010f06032415 68
    0x900400c011114040068284090386204104d0001104c0358010085c10068002c024000d885010b000d288803560b0400401c5600240031130782c0040039101410041e0000b0950b546041001440408103400c510303c22903641640400c0c4030720020300c41c024044942082400240800000c0355001c030074121006480040604002c10842c83c1d6001f40c40a0b002124020b03015140d80d0000c071081e00034201022240c043c0540d040c8403030b40080b9100e0883c0c910041256103885410428070040350410313900c4001980d12210480415030304940c0890240c035401915901c402d1110000039034901c91079140034003031050320f00802e1040c80309401408941d1007030285084003408480740c13080d402030700348100000102e850000c900c800340f040c003c4011000440d86c6038061503000c0982c042c002d5118034440350056580301000800519135100e40703051141c1610443c10f4140c01000042d003503800707010302081c07030516050f41400011030040541d04842c042902a41d90803011040302802425440c0b9100187e009080700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361418435 1250 361417185 361417187
    0x1030c090e0a1d01020c06070c0f02041b0e01020c1c020a0918211409030a0516060f030b0d080309150c1b0604210504050a08011d0d1211070203010c 65
    0x403508000005030b10724600c00d100c83c0480c500300d0183d80f0b03405405030090f2021034549486484203405d214000d00180c0c60510a85d070002d42120b1030410303403450a540380e120f14409981c1060f114404e15800b0b0000e00300058403400043c08002018503040076410011a410080d511503030341c240302601e005541088089020901211030700eaa083c0d04444c100300c0c400a0300c0c030950ac044000308a4442d2522405500750005024800d9500003000c03007509481009119230106904120701230301c0d03103200f012408202e030821100510035a50517944509142c184107016010391500c0c000254040d410240260b203e0300e41203003040c05d0521082241100807040000e1001e510071002c002c2044207021f001d5884240100245c3e075844400c2241d02030407502564801d014159014202c03071500003042d01c4d14901e01501c03100005c3c0036003900d422007e29a03651300c54810508503140010091403a0680080c80384400c0200024440c0348228140101e09898070020300315240160166001d0a070b000303000f0f21110707600982c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361419685 1250 361418435 361418441
    0xd020705030d1a010504033c03030c180b0412030905060a03050f0a0501080c040b0a1a030406140603100903031107081908090a0206180a0305030304060606020111040501030c090e0a 79
    0x208640340c3c01c1154100c0d90306600680c225021a6402030390181000d50042e0589a409a03007807500340340100020100780d00e910f016070080340b0148251000100315100c0f5000408c0d0041819542ea15174080c0c43c0c0a01c1f0f403050040540c0c00b2910044401ced001c0004900d4125010850b5601040d040b220200d0445240c82e0160442031051400e651600da5a0b91a4520101980c4080c400e0724203e4002d4410300301681000d41105014400117005509040e54800d040e942a22829100c2d540c142c4000c800c5c8810004a8058102c400c5003200b8042110304025002070784440680d6003640c0641d03660f4141c5c0041500a40002c41c0e19061040300720344800c0c49007000d020540c0a20102405042682c4c6081501c0b405152114015201c8400400203800380fa401c1c40115440244031500260503441c5440d56569030484400281d44180e01454490802e8503042042e00d000340c00c04400e5905049840d00d040c143ea8081d501160000d2170003107590060a941a1090352042d0002103e03a031f0808208001c2c550207030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361420935 1250 361419685 361419701
    0x3030a05040611030406080105042307020a02040e01020a080606070c03150603120206010f0911070f0501020a08071d0d1a04061506050f1902190b0601110c150d020705030d 75
    0x503c550510180700b00056842e842103000711000f00b00900c0041c0714505195220111040c01aa4142c0b00d407072074440146821607040f9a80300044e03100c2680c0b0000c60034140141504102c101000354104819081b018054a00c000d00880c041d01c2c0c08100b410912044e110f10000540c0c00104210041b10074640a801410741070109561000800383c244015030b1000806504a600700214840114240040800500701c900b03604030008074103010740710109030078420590815100d0301c00182d4501001e000076050030303001088141400010b2070314100c440250a51030840b0f050840300d100554840e0319020144c02007220360016204010000c201c10005503620801d00c40184100e001201507a611007120603200d030f601c075148110018001c1141125400d15040c0303a241030340c0151420201d0391420a09025500d19041d20261440c1c4280001947c000660401c45400c1c0f20203451a144000041098148070340c2d0408805030f130008005c9850b6059505488005600c84207403980c8400094149002d04141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361422185 1250 361420935 361420937
    0xa080d06151d120705060c06070e060f0d1503050a1103100b03071505190e0a0501111c020705100305090105072a0204230a0506040b03031e0903030a050406 68
    0x90550000103400780c003101e07242e241d001d003048488031012410310540c0d24507900e4003c8a4801c40c1008036595942d00090202013075064000c05481c07404220091031826171402c454001d2604120900002c0101c1044402e03840901c0e002084114032145040c0c0854807070340c400380c6903003d1603214900b00b00a0903100c10654108170304881e03250900000110407509104410743d41741d0712000c01000f80d01c140b24825811144203041040c05c1a810800c4c0d0000c103203d8541d150006400d41c001c41301da91070702301c10410141100b8a80407004141d110341c1295192151140307000d468155030507080920303200f000200064000644000100130205001401406060b10070103c1e55003044002003400748144020b04140039403450a0b440c42d80700394102c4414410041050b0303040364803100c0c821400506182c0013417011800d02d10080852800f0b090007000c40b40080c0c100c1d8480c40c1012050325103503038000b00303990488003001c050144615022141008070701ca05c01100341c140c0401b0032001175550b0070001500c129089 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361423435 1250 361422185 361422209
    0xb03100935280323040f050d020307050d030915090f02060c01020d05090f12030411040203041101030b0102070605250b04030302042402070b0c0309030a0c05031011070f02030a080d06 80
    0x6002026000e6034680324050000310080803060341c0c405030135403501e034000d03018040604010b80c581c6c5450341803808519085001da03100007044820490204546100c80752980740c20021106142c1d21442105d1600c03c04035040780e207a580755400e10101003600f00840b82e00603c050b5035000d0510a0a001c1c1d000701c02c041c0b8000b854280040c112040c0446c20121403003150014002d0070070680c44000385900040c1041d03580d954018010a0b264690744019405140901081540403401d2000101030310b07580c903c040e04540000e034041203401d400000362250f000307042424040303c203070746148144800c0180070090a544013060a000a141d0140e004106880ca030091111000da0f0706400020000b245074100e4006a004800801110242d2006048403500860540e0f290684082c0024075103913080300305032803480690000304003038542004011200308121000707005034182c400d011036803401481805050b5078503500b1003c08558040c0070103140d445e4061b10150719100010840001860640110902c00302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361424685 1250 361423435 361423507
    0x60606220620121207050c060106082d010306111204060203010905090706050d0504061d16060c0f060506010509090103050c0306070503090c0f060f040303030b03100935 74
    0x1001051000780c889220900c20b24164a116880c01360310320040650042240070311090074140c800703000d058001c00e5240d40d80041410288540394141c45031405200041d0460808640c49080c12a401c80c1100e801c9000000c0300103030540039550900c1402084110f60850008010801109901441c1078602d00c0b40304205c1580c80800460b40c8080e54001c140104d503051120103002401500403d50113842042d011401505290714500c60400d100c00f00103058106000517100710585100c034000624883c07801c0540b40180f49c80302c486504c85500080d05240d01c80000a03410790181003240d1043c0c0001d88044c003070f50b079a070400940755188018428820300841010551003880380c0c0940703000700b003080702804004005200308070100c0040107410b50080d106100c2901b8075403203d0080c000035070282c1c402084446d2048101800c0c808414000344280d0700e440b0005000c1075001121045100d04d102c12074241c1c0c8010f04031102030303542c0c41c60907080c191400a07400b0b4120792141c505014045040c140c04210103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361425935 1250 361424685 361424747
    0x1b020a05010e03040819020d0204090b0a0b09010b0f210705040609060503060906090406060b0a050408010b03030309060c0c0307170408010c140a050a0e030304090b01020f0307050606062206 83
    0x1304c118890122541c1c44410b11002c4541003050a00c159803004201850088141d03010405940c1515000d641d10311941e0304010812100e80641e4040c00b0080b100701c1c00035811300040c00c040740030b200500c04503201c000c40da20f0701092196403981806241d1800b00f101d28901600d000707015501c2400784800080202c08006111805142501d00810005240000aa031001c0074051f0806005009403245038844200103000080d131001002050429591180e5990401c0c01440c290750454200c01c0c0a07500c10010014401e102280c140d401c400d100d0351190307a51104a00880c514015a00b000d0165137040c080c0a0300e0314032400051003200e01402c000d00c924407000005403602d00311484150306502040000155151040c00101100d512030700b40556000d43d08008a844c54020f504512041e079503900140509680400c0300b43c0c021030b4014021490b082c50369503081c0d158403020380b00b5400740c0b902296145420940c0c9200324003c40340d201e1454200341e603a1200030009400e018460007d042c070445800000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361427185 1250 361425935 361425937
    0xb0405060126030403110102150a0515030a0209040219031b0905060d11010e0a0e010902130e070e240720040b0603041b030b01150311091807031b020a05010e03 70
    0x8685800b0185080500d5520341d9010341c05000c00990460184103c5400015001403201d40100441400041e2600d070001c075003401606900559403180d0f2010401100607035501c20300301e9020364107076103900c20554010f0340c0c140c0100c42c41e000102401c11421210500040c4aa40a0200c46c1940400c1c040c0e0b0301c0c1c0782c0900c00c00c0215220080d00c040c0b0b1811490619501418600c61134030320203003090703040c80e644d20f071006070300c040a1304080b803201e8000611034800d08009000b1b5000e00708069604c0a039040c0ba000c00740144210380121130260040c40501094000940e000c0c1e140c000c0c6181840e0b07512031091400a0148005010450f00e40444043c0004681032031702c58580d00038009804989540c075580c4600c14900a80100030007001958000800001d0454110074028101e001d03a295070b1284114014080d01e4001c80d070048117900600440040f42c0d2000512200511640909011f6484480049014119040708031a269070a84030380b07501241c1c0007400710001c034041e10080144100c00e0082d40d0702d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361428435 1250 361427185 361427249
    0xf02060a05060102191401090f0506060415090b18040302030a0306080d09030303050c0904060e01030506011a0405010507060b270630031204080307080a0c08010b0f070b04050601 78
    0x1030340281c02140500348411000c49145006d01075008400c00030200c128255600940211952529101088108202000100e4120f60111828072443c0c0b9242c1c3c680e40c602005200b000c41d001c0d107502d020304181e03c51075810381c80d140790034541541c50716203070078042c1d660f62119107844000784c03400b50001810312001c1030f40c0100300308558030220083c0c51510118060031014240a0402004000c007a0440d681e910602e0014038480348100c0c160340c034604080d03050450503844018602030082e080540c0c0c510134401c0f5000c0d600c003401d280392554440d06000004200f601e1a00d07401681402e130001c0b1a0458144016101a48044001c2d5641d5007106010711400d0b50780407210894101514080c140000c0301410301e400d40100c0849041009400448208071004c1e0740503211403074008107100c0021b9010b5041940300c05566424081400f800100030034807001442126200940440c500d80c2c2030001c1401c4524103a00012520058103050502e1604e440084c400d4460700f05548040041032460f090400d03032 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361429685 1250 361428435 361428437
    0xf090f0916110f030c06100905040305070206223b0103030c02030f06010617060f0a03030e01090b0706060611150411041b1107090209030a1704150f02060a050601 71
    0x5207150400e1090380c294030140c0019032640500029400c2d00a401c02c090a61004108010030341401c0c0100b19002803c65030b044040b40d00c0c100820000800d4009013110882641914950b641d00d5071103400c0c441e26641584050050054006e000401c100014070030752040a070443d4280178828180c00b88150700c0311908242080000600040000ca40202100c2001c0d900290554000c00c0c3c1c40a601800c003207090300810041180b002001c003010806c00446940700070165403464104014000051280c80f062000a0800c544d601e40c00b10f107a4070950303880303006203204d0b00080e4035201c00d8641040981458014800064170581c58042c14110015015480000b5100c50075007584886d203842480900c0b0308040ca0f00162150362840c09030302036182195007016a80c0c1c802d0f9200d03005d03004107403c0000039486404d28074010700c036440c4641e13004103000722030590041007243d42d0411112001c541d4055680f1140d2404028009142c507180c01c4804074001101c158261a011703134581c0070581c110341007524081c3c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361430935 1250 361429685 361429711
    0x5010e0118060b0a12060603030305060a060c0b070302040902040b0715061a390c0603010f0608060f0306070521041119050a0611120c0c13060b0f090f09 67
    0x10010074000e0f4404060804084c0030940140c1d115401e1454541100200700c43c910f0b5a460708105069041c4207c5402c02011034402c0307003c51804000520841400d0380223480c0b03030707000030128007440d0007681210003c02010f00207644440c3d840700e5a002a4121001c10b031140700c100102d02030210458407d04042d2580b6445040d2001c518190324a4103411801d480007000d1010032000d2030000710300b425019180d45800e1000b10b03102ca190040e07803d00c58818002e60180744240014054410360846003000e0b01c1143c9000764455032000d0020341c00341004200741d9010700464081c0005550320200070000318075101d0707005c1c07030006a40c11075004c1104c0c00c64000c0c118820703040d41e09503140303842d642d6195404001840104402d840740c0c0000d484407030b10740c04000898092850b109010105124094404082e10103060070100343d105003a894042e002c3c03c05108140300f41113411169071301d9200c00003400400100700c0d12141c031040500d50b25130020078820f12420025080701d09600d0b1044003103100b001d07012090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361432185 1250 361430935 361430981
    0x901120302250b13180507030e0c061b070306020f0c0706020f10022101080304080d020609060402270a05060a0b0a0c0201120b1c1115030412052505010e01 68
    0x28485801600c105094100381380000100810345500185031290382800014660500c06c41c0901207038900d900f41d1b8160b40128a5052031559014207650360480c41d03014451a0040703113003280d82040095000100300c6840031070342c138003207903045006040c2e07c4a9040c110b82a00c0c0c1c485d07805998031928000c0b003500c41d9200407150808031016070081e200940042078071407005441403a4402c0108402d0b0070004503648040760400c03801343c1c100062085202e2038001b4044034107000243e951140c0300280040d00681801c4507a40323980d042c0c1f8030100c80c20421880207412900b0500300d8403000e41001d8a030144034044041c0c0c0400c01581e91350407200c030740710f882e241c54903100c4071940155140e01d0040034803110700c1e564226600458032002c254045010340c420741c0780c10007400362074a070a9440c1a00751080c040d540b5180f00300c040303841020840350030680101034400396010301c4408560521130b4142401007840010b05100e01c81b940e905000400c00e1098000340501d004511183e030885124218113644116a1068 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361433435 1250 361432185 361432199
    0x20a05240105010c051c0c051b0f01230a02030c061e06010918050c091207030c12021e041d0d0311250204020403020405041407120f12020c090112030225 67
    0x50360010f122070400001c9064540c0305e01c1d0270400030040c14450030020b0800610540740814a0f03018080090804001a07600309a40c0203404403580c100300c03140f40c00052603801c0c680c0208140c403c44c4444000721a01c0b8686405040c21f000f07000da040c0c2c42c8003c0200d01090656010350401001e607540c4221000c200107514000001403d00608000c8204008200400c07507a203d01d06c0080b5000c02d400c00418213903296141460031700c0a00d0b84a5642101c08041c440016662081d84142d50140ca40160303071107050707103000a0300800c118810b0205042c40248201040b401c0410300c500c3c00f07182520100704000705103003414064450904000b8001500c0c00300d4083d0484001c0d001415180058801401c05407654013180480d1000e0b18251001003844000c450b006204001100140500c0c29108071401920f43e00c0655000401ca00180800210b03140040002d10800142c0b0301b424005140526950351185002c03004802070400350014012104800d075440f0704410321143c09012850b08202440c50300358 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361434685 1250 361433435 361433473
    0x5061509090711060709050306150a05190504140711071433041502071503020f0d0903033e0703020f0109060204091b081501020a05240105010c05 64
    0x1c00d000f0302181820707001404010f003a00c00e482c0c0e40c8545680d641000d080625010000700140350310f40e594a000c90144e12052002d100b00c58054038407001c04404060305134698000c80d041160403514003204140c03040e518880302d070300900482d140c03020b400a1041300e0a8460b042c0703000f0035803980b0805200040038100452100928514082e00c26036100d9010032001030003003210800100311070082002d10140305a5200c43da02e59160380014100145022002c01ca070b820196440c100f41a03011a81c150b04400746011149a00003101040080483d00d190182c01400d00260341d4410b9644040004240c1030700d0521240c502426480110b2751044084503070304142c0c412042203007180585040140c071882d09000750321100307119100244e211410b1001000c2103031001e03011380c04500ea0704c1e0046a155904400030a401207035240c80c50000d46031145c0140e240c5008007038004c060380716288080c0800d601030240c0851030000c0c0804810966038801c0115081e000202c8040c00340d0b0812060b170744080ba2203034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361435935 1250 361434685 361434691
    0xd150209040204030c0e06030303090d03150503100603060f090b0f0601020a0b040308060112020a230c101413120c050a080f07030809010c0c02040e071a0408010506150909 75
    0x5440903252080384808038007030b40c100ba40100c4420350f0b9a02c050101d5001010041d0f07004800364020360075454409103490781c503070f0700600c01c606060361054600c05040115040c1c1c0041c0a018003102c0101c0d14ac280120000d04d264401511410b02c0c001080d81d1901c17403402200c410b241c2060382d1104e2900d070f001f500f9942800140a032410361240040380390009100d640441c0c0b0a5000e03455141007403800c2d2002420000040e00c0302c8229900c10800d03d1083c50b0000b03450901c0c803584c0e1010315494050700c3c40d64080381c4246880316459104a1040ca440d80c0307465085040110780b18500c01140351544940301c2c80003c0301c00070061000e0300700440c1520b041d02c94400c404c4043d01541c1207800d851031540f20007909512000c40b4640d480d000040700703030500d90024000c0c0e402554540c000c111605021400518000602000920407504e400c40c00500460412a47c4058400c44200c4e2030101e003e6109000c0300e9100d8800c02d5180e508000000f00240b4155120200d009500c1c4281482d000e040010091a1030b001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361437185 1250 361435935 361435973
    0x10f0503130501050103152f07020109170a0c09050c03010621180b09060405100c03110c033001090e010e0f1608032a191b05040b0d 58
    0x1c10354010a009000d50390003075000385000700040c0300d000d58080a4943c00c4c41d584000d0300704e039031500310440000b0010703e08c82410350001d65240c03403480c40101d43d10078403940f00f0104400c0c078444e0031a91000108a481101748100c04104126581e20705500988004540c0d900552100f480104110741c044c1803490f040c09086141c001c0340e1349040b46000c040300c01d03011403035120855000c200b0081180380002c942e0403000e80030040c2800c0c0317031a6807150f60310203100c00414500ea40f02d804c00103055020703405c098541989583d000d600e9804050a040d0741e0b801c035011901c03842a50006004040b60307000c60f1110702100095015055038285000f01001e08500009904190368130300805450110034818a03004a00e01d030040c102c1090540001c00c2d821445070004407007a0010004100c40c0c0020841009035504020518581ca80000e00940e080040044124040c907285458603010420400c0c032440d0748000c01e8024444c140e8803041444100d96410391070680140d00300380c4410203e510340c0d4840d18040340d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361438435 1250 361437185 361437211
    0x15010807090801021303031106100302041d011b02010c050a0206010b1602060d050613020a020a0605090a140303070813020d0b041e050601030204110a05030112020109090e060604060f05010f0503 85
    0x1440402c60700326442000b01c080c40000f0103805100301507200300300c04c1c4212142c00050555003041c01c001d0350041440e10000b8480c07035450724030705900d002003481261400104002004080100501e0100c1130b094501c100c001546400c59100b181d43c0990141c81100b02141e00604207a0300302240307031010b40d00c42d48201100342100b041e04001a51448000c4c41d021045c0240440c0781d0a085007031041e50a080084609298014001c4005050340000c0311105660000000b14054403401f00752424104203c030050b014a5514410818883d000401140920345d25a240a81d0340d90303520010f509141640c034000c2d44581c80110740740224a046507040d8205024148140f5800c00c00300b5050a18606200300b290240c01080041055240c24403032070a0080081040516180d050540203005110500643c2a03201e8086219400d591058181c0c5025000c3e040f410800741c0d03103241a8035521001151000c0c4114200403001c924840307404c00c15800c503001a19a980d0b028110801503400b500700406d20042e0b4a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361439685 1250 361438435 361438439
    0x3080114060403150c0905030f0c010c060207020409080a0815130504052506080606130b03090a0503120105030d0c080a11031903020c0613050c01110a0506010e0118051501080709 78
    0x11043d07840d800c82e881e5410b0001e0402c1c03034154003910306101b03640214441d800507594075450031804a00c2d00c415132401d2a101c4512801c51800704000d0040d032001075005458896118100090380700109441161621840c00554607451400790500031081c0da980c002620a903c410a211a03400a6030000c3c03244091300c4421600c82c0e002c90201414905200c4652940301081258030f4100e0003031a000941910344902c0c1c0060407200c40c6003c1c2c247d10559400c00e000000081c0c425800b40800440640e00100754bd640342c0741c0303c040b202400003e0183c2440390140c80071450700d0b07034041d400010040d80d0003c8407500b012440c400c103807030b0000031509200c1c05020410541c0c41c19a00c1140c402d542480503280180c032811080700181c03401e1030040c0320310484007440f242c2d440400c900040c1d00b60520400d20f08522008038071102c42d0f0400940140080903803043c0e800100b0200c20400352a4162081c0c0d84580000c180910300100135594141c98030a821284020914030302d501ca10601a03110702503003030800d1929 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361440935 1250 361439685 361439693
    0x21151202130e0706120e0715180905041101080603250e04060e0d08011802070f1b170a11090c090d050c0405100302100f03200c060901020703080114060403 68
    0x580c02c2a11220a600420303000c1c03200c6900403003400c85c024112074040243d01941c400e000c0d0b40d80c1207130081d540501540640c0d03102c0d4034403034207410781c2d45540c06e15009002c1c4d558000300b0015240580c0c0c11142d0000c03103140c608081d4420607c10b40709110003802003061042d820140300382040b140c03c0401062206d82c0c4049084035241103414003551040d0301c0051201603840502c0e00b080303940000041040004001007082c1c90107035031404c0500402110041e074030801460906050300c51400d00038058501116400b001d100080c0031041202c030b40c003122050542d6600c06103910b03207407001c2e80200030341c7d0b200103d138030541018468146d02030791200d070300d51401e08072500040340c4080c058400c0b00c055000c07149003881418940201f0780c0118040c08800317610703030440c2d0000b00d601e8400c1d0158000c1004600162a0040c460b0304014400c2179039041000440c08400b180001c0c036072040d00a03022038490b140220b06c443c1014400c6480854160b81c52a210780d090030340c91241e8055100c96583d0140f002e000210201e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361442185 1250 361440935 361440941
    0x20c09040809060406081f0501050403030f0e10020307022404030605090f0604050307050c0108041a13060c0e01140c06041401020d020a031a0a0612021b0109032115120213 75
    0x1d00700d15140d00540d0307d000c00f088203403240d10703c004114015440c001004a81d80141c2a14180d03a41420b00c40c80c49454001c045603540c42145003a83c0c8a0b50b85d108080200b0380200052840c41e00a03610718120341d44881c0ea180e200b40d0030456800f2989403c200402c04030394542e110a801804102c1550f20014000301d405181800239507003521203400006d00c005c100402008043e03a826001c0c01c00b0010392826072118016160341303c00754511501100009103000000902c00c002c80382d8420340c2040a2049404000c0071080223201c3d00d8007041c034041d00901c14920702c00a403002a04c900c030043c4502d039280e990f101c0c02881c2c40301d031642d01e940d000d21003075800b500d050010703140c40c00f019600011494078121588018035074070000300d40907401042c4103001c0c0503480617a40504440e0580c01503500c1541f90544480c1d186103849d00e08c041d500e402101410994440e400d070614410440c180c10609148109010841e0040c940240c3c00c80c400400070441c0e410804075103102d542c002440718020300c0b4030040142c16 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361443435 1250 361442185 361442189
    0xa031806060f0e0108010b1c1a09030a120b030c01030213030b0109150509070c060b0109030804080d1e0c110d05011a090711070e09010e0d090321020c090408090604 72
    0xb41c00e0b8940041c0110007010380243e00502d40381001380611502c1c000400e060781c07050342401c4030002c11800d100050001c0e1454515031401d0f5192040c185181100342d2507120341180f41900d0014099aa000c403200c803640c010310040c2a0000c000d1710038000c42c440150000c0d40304204640240341a800c00001007061003406500030400040302040f002301d20f1480c038441050035002144034603031013420f1008407940703e0f01d82082903a00910000c1e01c0d580302401610901748aa100500720000000d020a044101141084022005444520580803602400107001c9099242840058021002c600c00701d408490329020300600070b0001051a207582e203516003034901d000c940303140350000d0f00911000380c20401203080d403250f41880c111008005152505442c0e420f01c1c42032492051040c03020400403a000e51100e00350022000403601018103144024009030318500c800e0310303d039a0114a140015840c0400c0312012105a405000020007600421103020000b81040d40c0000c800c0c40110807684440d402440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361444685 1250 361443435 361443449
    0x905030706020a0b010501080f0411010504050d15050106090806070e0f0a081c0908030414060d0603030c03110604170307020a080a0903020a0f0506071e1719090602030a03180606 78
    0x2030107003e6043c0724000140c10b0307104504000118040188100901c41d8082c0c0140c1d005c0381d08003c0c0001078004803681e0003690045540403a100b14090304019810500980b0000c101c0014442c903a41c806d02928003446034800e40c0c0c1e40342c02550000b040c0304d119900c00e80007420020803110401201701c010403d801b0b4142c102c0580d540c801404140394500b0401078260451040ca4900e00b40350500c09840d0326401a48284c1d024000300c001400c40320340e69001030750909142148200510342e924140244032103a680800e174003066582540d00f2004402140c00e62183c4d802c664115074124031410b2030311056000078441000c60140da0300050028048400400340c203803a03070b625410418118010400d1504055021081441d81c0342d204100744e4981130161600a80c0100d003000c2d8901d12801d4030300b1140800341d8018040500d00e2500c0c0c1501084502400d041c854201d0210f100402881c400c1e502d4914501171000560300610a20881511903080040d0039881c0c641c02c031b180d03552a0350310030042da0203980203d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361445935 1250 361444685 361444693
    0x702060a112506172202010c02060f04050a0905040f020d08130303020304090b04021e1606060602030307030f0e060127050a0e010b1522080307030305060108011d0a0c090503070602 79
    0x30451380140b225100000799401009542050103500440c1401c1c103440d100e0303e10120072190107681c000c0044e8444283c0103407815581b00781e02200e6031829480360003031134814526500007103000b1010b0b10805102c4c40e0701c450810315044140d000c01c481e0003400041281d0b81102000b0018102813000144001103210341c000703540700c1d03081aa400050f100d1410b800c1e80030342e1044c0000744010400100820308801c8090311203a94101d0309c0741c02008a480300c02d01511150500c20001500c0780d001004510501036658108401102400540185c0e2040140c1c800c05034004001070180390b40c0e40b810000c14090a0461100100480d200c00007034480880f00340000c2980c801d441802d08034280900e4240380c1c0120713a400f8608a450a001d00c45000740c0d422141414094440550600203c0e400f1034050302c4ca400469483d0401803030000d000d800c00f1503490380060f000700300000c0d80c1c4003002400c4103480c184102a882e20303030303400301802e00914405080a0070040c0c00080041d46803028844e10014140300d901070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361447185 1250 361445935 361445939
    0x9020103050603031e090604080718140903030a0b0609131e0603050d050d0204030212100e07080703080d0204120b010314151305010908030c1803030702060a1125 71
    0x9412100c000b0301c1036000341c02c1009010390005211940380c1800156421154541d003080740421034600458010b000349108011000c104070b604e5203d40149886038010901c9641c0e0f81c507501784130644081c2c1e00c0c03003011381c02030020404161050308406070071440902941e05010a0200180e4582040109920b800d6a43c00c240040e07030014a009034a0500d05070070034810315180daa40c041d9a84038507000781e003c111022440e2041600b0b160101e800a640083c00c80f114623020050704c60701d1b81c0c0c0c031041c12040d103071a00b01030010384031000c241d2404446868020b045030310300c0c1d0f032201c0d2700680c005c080009940e54200030129400c00282c203c1c400440c05464440c0c040d60440c90007184410011074804055844600c00380a0322400d22011a807104030101411540803252920f40e024040b031083c0208803110100c01c05c482601d01d04050004d0340d03c6a1200c0c09042a58018151603201e2101e020b50003031300800c141405540585078000d180c40c0368404607001c682108686598100540c00d1a4038441c040302e41c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361448435 1250 361447185 361447187
    0x10c0615060207140a060f0c02030601030606090f0b031207080d090b0601180e010302010507060e06012912010b030619080a11030d170c160c031202060c160f050a06090201 75
    0x80180a0046695984c0480f0a1140050031445080c41618100968158145440752007080e803c9019640642100c0255840e45071000162135140102d0800ca464a019809070140d117000700d014110025010b0324400301d2403524809a42c5c000001071f1411401049404803c1000c0e01c81c0340412070048481d024903007480400180320190b800d40074620101c1c4602c0c1070240c0c20803a8007042c1101c1d824201a40c0d90402440d00f00d0150020f106202e0180c080c903400080c40e21488041d000b000c40c01c440d00e51000c403001c590300c48094002c940c850302c02584040014880341c0d210b00000c2d90401801844001d1b0030480350303e00307010403c641c0c010f01c045400511100b000c000842c4003518128004a018085800c404480105001690901da4550954100c00b04074034801d0039040b9080703000104c3e52200300c0c110600703118500c0001440219000780f060040968824804136005029200c9401a0b5203000c01018664003014200c00c01034070a10004203000380043c404200b0210f120f0b20440300452181c5040c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361449685 1250 361448435 361448443
    0x1050a050901080309040203040215270102070608060607020f0d060213050607020f040c05091005070215030c04030807110d060905010b04020a020d052208030c010506010507080a0e010c06150602 85
    0x100c000e0149540c0001070010706408419102003510590b40107889503076500004104e40c000035080800c41d0800641e0115490300d2500f60520b1f101c0b064880c0650705034800049940302074604c40c00c0c0001d00303601d0104a00c0e00d4030300b0080c100107000600c1040d10780e00840003c2c0904c101201c08484a581c00038410007200108120040140802c469141c20001141c011610b81c181e80182544030ba41d98003010812140104c060303480d07106001c1c1c1484040c000800020713005501c680300507440384d1001c10b010b101a9040e102200d105000d0b2000e42414186560794280d000d0b042414205c1d0320181c08042c041c02621a220780900308ca01554000c03e200409051003803c4076503201a941c0581c2c010060300c40741c83d400062600081402c0c0c030b40a83c1c1d400311601d04003544c0800d02c000c6003440c0b049101c0012140d0b40000505195600710340208004d840d200c005503418071801d10001d001c0d00d810300000c442d842c01400c0310701e26220181420728280c3c40581d41d0100b101d00200c046c44022260741c0d418484a54104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361450935 1250 361449685 361449689
    0xc0105010504060501120504020a090f0209011b0c0b0a0c0503030c0706150b22050334080601030201030203041b1502161a0306150a0c02040e0d0c080a0e0d060501050a 73
    0x740e803c100090078140000e010340a541c00d80402c098841740454215114214080000e02d10590204802103140100704e000c0d6000c05a881c1c000785044007103072450b080f84981d4603242540310f101514206c0c6041106080e680101c250308d020f04c100c0f120030001085042c4025446400d40a0015030b4404441c50841c04943c5501780f15003824400410521140e440724040714602c1400942e40c50043c060070111001c994441d0b080103030540140ca0107100007e1110708508800c141e84041c09084146c100c11545148400c0c1c40381400c9075200f04010009540254002c60300306002d8800c80c01880d503a400c036501c0c03416550344948c02203130b00903c05400e000c0e41031100c45611450300c0c961000680c900301108014a0052a8800e110000000843c2c4a56990b0a0b032020b50744451200310380380c81103105c01802a003000c40c0264046d03800c00e0409201c62902040c0940c1c0030456803110440800b6903211456580c100b0b00e00d80d0305008400e90781105607561403003544e00c5503200b804042010760500040c800500c040d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361452185 1250 361450935 361450939
    0x1204120f030e100f0f06030b0709051c080711030a05070302130b010206061302090a0f0905011a19020f0a08070c0e040503040e0c0909010e04031409102609030c01050105 74
    0x1209510102c407030049958801000c4014002ca1380340408680c55000307004050340aa6a9464180d002041007182000345210b05551307118064420341d14800c3c0840d0020400c1e004031505040c0141c40c0000707400c200689000c9004100310000c80c071211010a01d0005101c9047d22a0351104004004501c1e00810a11501200b00003c5c05441d01c0800041d6550401a201c148135200600b080711241d5043da05847c04054020513082880e55102000038002e5206e000e40d041c0d030740c1000004070710301f0f01c3ca4158000c2d41d1011500c003032400c812001e0544208170048050811401081900c2c000b105040000340c000c0e50054052650310320720762800c10144082d562240d240e200b021410000401e5000c410303501107030b90041c15218669a840f081010510641030307031540c08500ca07800481e012a1609800788518800d03194012b404e20710074001c480c20f009020703c07540c5c055401c1003140c0b1b24078800d0310ba80e000000002e1199520148070021901070b401c003102c458800340e10208080808640c2401590b0042c101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361453435 1250 361452185 361452191
    0x8160e01021902030a080a120b040504030c020f0307080706030e062d070513031104140c090607050309120f0d08090723030f01020913020313030c02061204120f03 71
    0x8800080d44941002c98041c00445810080d6000d40d20300340080349410742d009a4840e600c0d549000050107003c070070712101c1816490701d20746a01608162184500994043d2100c9007110203580c00c0100d0400c4203040540c140c050b4000002d075051080060308040e0800381c4000c82c01090312000749160050060003520708942c1c007500101284187c07045001050104a5108031694480c02c040d2081d101d0381c0240c09110305079290000c28860703c007419030700d400000c0b6801d12041c400012140e0342d480054403244201c9034100302841c0d0914002d40104000d51044050300d09000180c40041c840014950640001e0340201e94410b500f20420b01c1000e0154005050529903400c01780c0722640d654020b0b0140154074843d07224802d40045484408500b500e0700142280e0106401a0219000c0d4010128141c0144032191189441070454001c1e00c0c451819402106004007040e03d040b140c110300c0c01401d0346c01082c2040f2428990220441d03c030320030b600801400040d0704078030030000c12010495640f4000c040c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361454685 1250 361453435 361453457
    0x304060e040908400f0b030610030c02010f05040c030b070c03140d061e030b010803090f150f030906090d03020c0c010e120d18150207060f0903080a0816 67
    0x24600103413844840069644804508071460350803000240e24030540e071080803002c50320079400404440100344c4596191103510550745602c10800c80c08282c6042d1703840008a4888403d60707100754000f580ca8100c1d44000b0401c2e95a101c1518101c543c1a41c3c00d1380e1b15581e182c018030602403e803116030381108251504031107144050b10000d100060044100400d03060000301310030303001c100340c2162000d4104032003003c62030008501c425171400c000c0e01c000c03a90761019030000100d4100101c20786882000c041e10710040c4031801c5d81040500c4040d00450411141b0900c000548504900041c61044005800924480c03c107000440d180418031074215040600400400c0e026203004584101d40200c00e00f08214865421070004150307103204883c00c0d81c0d512a56060304011039011607203082d0606081c0400c01c000791200c040d4910403240101c0c10b009a03104c0841000306911600c00a08101d210b0700c0c058690f962203030749401c0698040c02203200082c101000b072180320844040e00c0f2049841d07604018000305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361455935 1250 361454685 361454693
    0x20702030f06190213030210080f01050a1a0d020f0a020d020c0405010609030605061305070e19030f1421040810050f01121104020a020105100e04031704150e0304060e0409 75
    0x9180c03c42c0d4008a940101c1c0114000e401448034001035903005100c0c00c0c581c00c515200500302542103501c0408540d425000280a0802c448070000340c0341d041c0020a4200c803c414083c405a1115a0140351075074200916116081205d010701a0340081fa40a00609841d0700c10003454131035600d15272880345181400401105805c130302150308503640200c002c901565510001202c414080281d002860305000c10000325607400009030a5200b02129590303c401c002e141e01400413002400001d02c1c07044030f00c21740d1020480800c50072050704e40746402c03541d8503001194040b103031100e03400700c05080c4480481c0c28840304509002c844481d40d1445d10400c07079403600c0d03641080c0100041c4500448032107a00c6651013072100400c0c00244001e4050825507849081d024002e0080c4403c0301e0b0642040040440401e03640e111301c44070b902a9806a0380c071203584071241c001d04400c10020f04200c55400c0e8402407101d40c8116401403180c4528503074042c6860b0f501c0c0500140818640038001440342e40f80c81c0d1640c3c001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361457185 1250 361455935 361455961
    0x50105030d0e0316090b270a150b0403061416120209010201020d020708070204140411040c0e091005151e070206041212030f090308060d0c090c03020702030f06 70
    0x20304540c5007156082501c00702107400e04c559002d9561151000c0a00410700381001e03001150102c5041c1d03604d11080500d03000c0c4841d0100c4d4420080c54100314500070402c90403660708410b1900e101c0c8010000346d07070341d251640303440c035802948119140c036220707400900d0300000034203101e60000c240e55881c1804c3d03112040080518034a00110031110354086000b50309a4402d6040c1e0300700c54001c0000310350340c40300707130802c00c5403508410000ca204900b012091005811f003812003030300031580810400301c1d9280240410020b003881841c42801c004000100240b20796803c507007940107070509241114264100804e20001030759140560b48202d8040098a102004107003404038808100001c0544520007480000c0e120b20950b84208401c402c15103134542800705910380c0a52911f400c4c0c42c01c0000700100b0b0680001d41c0c2c0028000b401203840c1d10005140b41c2090503800070304a10070907400426546580015040310214040d4100280d80818100c085003000c1102c0c0701020030003030003002c0750b15100c01c0201d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361458435 1250 361457185 361457203
    0xb0f01050a05061e040906030c170a03120e0102091008160509060a03020c07080723010806220b120d081b0a0f123b0c040b0d0512040609080105010503 66
    0x601c40e10480f030300400451241c1924040c01b0300701000c5c4001c43d030b03c2c00d03c181d54104900490110403c044e4410721010000200550501d83c1038403040c07040e8014990810041c4401c0199030580d540030400c00c40540d940c0d0916030a0843c407130301c801455040030b0b05020708003000c1c44900303c2070000c10050b04500d0360f2603d013610a421458900569115040c003403260800300c1c160b000400c2407080440114a02c000c5001848800d02000e5000d0f000e00454030046800c000240c94070340d0004480164a00080c000c03190b1000b420301f01c82804222640b242000c0748203030025001142c0e150b044006000059580180c01e283c20203042c0807007441d0031154204444243c0306454132407040c48003441c2c660703007518020b0000c4041c8041c1180d040241000a10140d2003654040c012b0020221209001c10045440c060000c40f4030061171000f0151141105c09001c000e291340400ca036400a5080030710000030304d08015480d1103183c082401d42e2034901d0309101600146041c1c008508990400d00103100303640380002c0030f0700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361459685 1250 361458435 361458457
    0x109060806120c090a090308090d0906030b06070c0906090b0d080301170703051014060414010e0c070516030519170d1b0e100201151707050d0b0f01050a0506 69
    0x411108184030481c0f0b0001c00caa5020b80007041c01d4200602e03105a5481200c0160007078031165181e0761a00d40e42da44a00035a501080400c030041030901601780300794410581010091f10311450000161601106007019502504089445550500030200a0b0080302242501902d5084002c03110f41c2c0d03203c0003404140507403800f500e144000d4810009080121400950b0080c0568a21525580071100548000e0a14000c0803078958045107007130500b489601c01040403101019600d9003070510030b0b145400c000e03103101400c14041c007003034000c20800c0c800e14200e1071408600c0c0e05810b18501d0483e01f050a0300021103217200c102084070001c86d501841c805840813207001100d90300e0200e909580c0040050341d04801c070030301c41601c50404003078100a011518030000c1320300c1207100460042c120300380e078001c80d00e50001c114440420041800030400d0220464006801d076084079864001051405004000607951580382400b0b004904000101413800f41c2402c1d1901e044840c10100810414421035030500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 361460935 1250 361459685 361459699
    0x11040f09020a0b030709150201021809010e04173606030c040315140403080405060901060602070b0904021b0a17071101080703151d0c03010e0c0a03020403050a0b150109060806 77
    0x86485e445950208054a0b80c00584070503a642804024001e4001017842d228100d080315010313165140c1008a03a0480303840a11002d00c0780d507660348220844001031406c0e426807100380802d03a0750048012a4407114010341c102c09d15424452150242105159004140182c2c0d040007841800080c140c225000c0d690805191540790480d800e9100c000e2541d000b2004a154446003800304250b13200030600d0040d8010021a01251190310220b0300b210322501c40d68009d640302031400c101000001000d003007400c600400041c140f445062403500e210341c0407940400309421805180c800c22090394410303842a003501c0783d10703420040c8559890102c40141003507a41440301100010384903034480d41064003109184518000880da45096035054550f83d9034403019050310034400102c0400c01030083c5da04840c203190402c600c9881d40740504210350f01190068003099002c100100c0400c90030020040402d00c5402c039407240340b5088186400302804440040d04000c20603008010051b4030250316504034008950031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 361462185 1250 361460935 361460941
    0x320c0a051b070b030a050702060610080a0b010509040f0608070605040b0306010c14010e06150d114b01020303041112031c0212070c0519030909020711040f09020a0b03 73
    0x1140391030b9090307101070040607000003000700303050aa8001c01c2c043c00032a0216a81e94880b0002c00c03001c0c40c044c9996000041908000a2a040d0250000c1345d494406051607440d042c4001c001c40d00740c95110200da02d040d610b400301080404410810540180388030701c0c0c1541400cbc20b0400d402e5403444041c0845041010160a160622540000300c107c0902d0002c0208140300010507001d8490500b1141060711010030104a0818103141d402480c040782e20003001c00241c42c1c0f1104010800c0e20070000c0b010041003030103110003010209684581012602c180b1090880c90246d10001503500c0007060604540043c001d102c00110307a00700240d200e520403180400458483d09180d17141d401030182d99040e0601c0110200c3c034219403030340203040e044071502c1429103640d2001c005a5002c400e0400091841d8012490b40742e14000b82e081d0708449602c06c0c6440d01d103c550b2400440d050340c018000664051164074030010309881d0910514000440b40701040c0240740301c540004030780018600c64405070304400400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 361463435 1250 361462185 361462237
    0x70f030818060d09031e14090904030c0c03110f0427020303130902071401140f060105070f1b0920090a05091f0608040f1104320c0a05 59
    0x143c50080c00264400c001c10700203801d005000e010854142d61081c0094502284060311032001d64510080c2851071614104103541401001e41c40140705500f0040c009850000092201202c0c01c000c500583c12058180d8500c000c11010711005e44506205900d00006c0704a05851403220304040e0300098039441d880500e50020908501c10b5880451101182c50030120f04030115a01402046000f0008184aa01c05074051804c035090061400c03504101a0002407405401c8100a80c1c0b0040c185012402c1281c207070384503401522103410440720303423610282d828445101c070b01403e001481d42c04000c2c083c1001c10710b106511485030b8a068441200001000b142680322062410000c08000e000a522071800400f6200700b40850500c0010003080b80e440010f1451280011500031a0450590404c032000355550704e0030701001c801d1850300a500c810103130703e0b8800c0d50744103c45c3c40031a40321030000780210740d0aa21a6003000401c0301414060500c440c0c0c86984d40710341a5080f4021555810761203001c1824 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 361464685 1250 361463435 361463437
    0x12011e1401020f1006061409060304021c020301060303050705010c081014031f060302030d0201021305210a080c0705010921050f190201080c070b15060903060c0a02070f03081806 78
    0x10044082c45114040c0c2c02508051780f005049611642e00c0403545041200e401c1254864801a10340c4108180042400f518042500d03985081400383c0407a1020f1880c1c0c082030a4130020750099001c0b0b0401709240301402028050102d83c139005161a000c80d1415025004010f42240506608061410180070040e1403c0100360140200f242030310345107403202c20b021409000e403404201d0007401001400c00700140140259600b001e218005001500c0c00d04061000080b20720f400f400380307690001c4c00c1c100140310030310624429038090703c030b02c541d54004440070a20f041100e0380224100720b0101c4003000380e40b4900c0d403140c403003250402101410744800d052061a15007000ca003408240201401004c40702d0f07002102c4103445100380c940d50200e84e25021000e0280c011400c014003020078240010340344440011640b00200b400400042c103041040000c6850580100e406825506000649138000c0c1d8040141100810456800d096610305545c1c50300c010b801950354410364581d1441c040071044c2d840c20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 361465935 1250 361464685 361464703
    0x71110050a020705030c0606030d050c151302120d0e0f0105070b1f150f030c021011040f0303110606060a0f050c15190e01020a020304030314070204060b12011e140102 73
    0x404403500e0740604117510341c4402c42070300c500d80b09e40f294519550b403003401a02602c00210350318016042031005080300d802c0201c0010407001d05948061a00c000603030b640c608040300a0850401007080206000025020300c541d150769a1142e092003100401a07a4424116100c1a502030f007a82402d80700c81003a00c1109102403d6011040c400c03060108182c07003104034042c140c000640e038600c0c0300900d01405504456000c61454016004115070b4180303650a504403003209000c0c80c15152030f051341e50110750040802500101d00043e2821000c291082c0100300550300300408031001c0c1c0c0750072826030b00640b5283d1110002c0050080118107101d0801080c0324142c1d08400400034450a444d2001c0080641c401c040520754549107042c245000c0100305100382d4080c1036450300150714003401c50301d043d15807095110303006500903010010400140c55a004d03440050540030900d988825410600e0340014105821412811040340321208010056032550f80480d80340816046e070602c00240100d003084009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 361467185 1250 361465935 361465943
    0x705010c0609020d14010b1c030f1e020705040f052a0d0c050c152a1303140607020a0f1101032316170106050a050d09030801030605071110050a0207 65
    0x14031141d0280001c18108455181c50071008001c7d502c041410000c0170b56900b400031421300f46c2244000002030041068500114917800e160945038611102004590800ca944c80010f8000c2c030010805414580100c0c04c1d20100c103502840107190000409800d0425020440a0a4003000f03c4a0024418508840343c1c01000d040034401d9881030940078040f54881032071044c00f0310810043c0c90302c2c600300c01140380c01645116400d800d09600c10f400d40c3c001050000045030040e80810402c0380820444400c80020b5202d6030032208020034600e25230f41044401040c480035500440220b1001401145a88030b440c0d60080c0444840586003004800400c6415681040246121a00b010000c2c84805d03480c8203903a0101d00040c900c414600c02c5a511400280c0407050120b08801404541d000e4800b421002504c2d1a2203802c26400035101c200b51038180342e0990200e441c800051007442514001c880d400601c0e4102a01e00e00980310215580c0c0301185401040a56160013007240c4000b546c040320903090b00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 361468435 1250 361467185 361467199
    0x906090a09020409200304150e010e0610080d090e160e031b030c101b0201020a02030607170a0209010c06050603030d1e1406061912050a15080c030705010c060902 71
    0x3d03054241c005080400c002c2c1714440031040c01062032501041200d200b150300030780040041c5610744103c0702030a640400c0e28141c2d5260b01c00030441100401001d44601c000c501c40e204201d180421590910f1052000c0d04108211908280001110140d2946e0090100700c5860340003003c06204880c80a1540e03203640c0e140c000d0441c80d5080b0003103445d80300880d00049007615517903100c00d4100072401c00650b00d1803010a51085028059242c100b00c002080741c010b0065556807581907000134101075084850001041030440308289035a000407480b81d000348c4401085160500303c3c80080c00902d98408010302c0e458030746000550546003030085d10f81c0180140c2082c000c14548505400c1003100134402ea89002c2c2c900201280421448000b0394080d0074080c00031031801400101071212003440e8003151040c0410518083d0000c01c0b00d21030039101c0c210511000945080101d844c0ba240009584166080e5104c8810408141c4d804208481114402d0a1000a1040c14600348010b031801d400c010b503004d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 361469685 1250 361468435 361468439
    0x80702010c08120a0b0906010c0212010603050303190e0111070210030b03010e01020a030f06030c0e0703060e10061107050a0b0c190b1902070503070609020103182607080906090a090204 81
    0x541002440c0c043c03408031001780441001142448030340f07601110200e000410012569015003003001d0b04004401c00103001194554980c0c6036640f56034001c1d12846203080c0343c04083c07114000144508044864a02c0090251042070306070826036004004010b403050640740b0100d622070340242e00803405480041d00030711200100c5510a4000d401c40c6aa80d4046030400c1e820714110301e664420102940c0c0e1003c2d15108160070320555080d1000020701d2034080c582d07104004139511808048061140c2903580b00500c00038240b040040c01c2c08aa641580c240307500c4114140700c0c0340d450ba800401514a01e021030b070b450740382c5100c4980c54540090490b0810440ba4010a02032081501e001c0d0700c1408440c250325820720308465940c040b441000c102402c260418440600003c076a90001c2ca035980c0141340225901045402c14180c0c01140c031800c0b950035000114440c0ba003203901c0900c4491082202d00a07081c107426480780d403000e10070035202612850001030104505c2d5502c00d16100613003075510085440340c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 361470935 1250 361469685 361469707
    0x2010f020115060f200a03030b031f0504020f06030714030619030b0f0105030706020706030b061c06090b010c08030406090f1401020a020723010e060c19150c0c080702010c08 76
    0x10002000200c0007610789400c0c040a0405c5108812401c62680010120082d194804a00511210001079414001d5100d03840c0b0300030454211218089020703000181d0342c202032040001070903032203a1075800745605000b0012001c2d049400c081524102d40c50f850341d03039550080060f1003040494240a2007030341c030040101c01d00804c23462062091090b202c20b002d83c0c0c1d0700d5504041e60740d0240e2103000e00590203640300707101043c0f080d001003480442c007901003400c280304043c0041c000a10107020900060b503441081105007203500922010784402c0c242514044141d40350102288030040024001e107840e200f2071020043c02d8840488510782200d100910003a050740414040d500198200006100784034000ca8591790418252a6000084030f201c03045190860041d55074885850442c2c0c1d00210600500e8013048003030100501040030b48500f00100b420a00e401203210920b2204076180c40e107000c000c1400d098001c8600b10341140c0042c0140d40321121440100c0d003a004900c40248041c10228030681e0310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 361472185 1250 361470935 361470947
    0x102040f093216020309040e010c02010b062104050f0303040c0e070e09011413150303140f030f04050313140f03060903030105060f1e0403150501030c0302010f02011506 74
    0x107940c0c1c0301c14002c0341d00c1030307102d0039004030340d0841208040c0030034100810801c246500508490900600540b03003448071500025048818128070b100c40359450701f0b40c100c6040da080c07080c1008004200c071800d04010840c078a40c80c00304400e03846591070b1020403012400b0305c0002c014082010b4bc805044039075928191400a4641e6024401d4244d824445408038500303500aa01011f1420800b034040d070071507882c00c8006188502910b1409410030024032001d80c5504443c050400c1c0a50301011b40610381c0d20310320340145106400d50001201d407405118002c0d0440300c0d0011030b90070040c2d503072080e403441c1c6031810f02c01d04600c5150100c6101290f440000100190801c42c018118041201d242c8549101c013414140c49410031240000c05402c06c10041c00b103860890003510700641401d08040c10f102001c0300f540e040b0a12604124421440410f04000b000a00543d0044a2104003024001d6501d1561031702c0c1c0700007440c08024148801d030f1040401c91303403013580321001049594048411540e5250009418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 361473435 1250 361472185 361472201
    0xe010606050405100e0f0405061f111002091302031b121602030909220f06051017031602060d14060102010b030c0f1c120210150803030f04050102040f09 67
    0x1683c55005640001801511240c482c2172018002ca03030003c550704104001810014200e070341c8100a25580100300c00f02e0f08000303190801c140c4607180070b0080d03403aa1a00c0c1481c0d0070050004240100481081c6440300d890303c021010003140e001d6280c0d2501c124011036030310040c8018072000000b0032018224024200b0403400b440d0006d20011015074188407c0b41c81388541c030000b5410046d288040317522803811b095200e030725280b00c100b00c15003122070707a5030801c100c04004401d80708640c81e00144062101c0c1829a00010418800c00030b00341400803861540381d000b200c810702c0070039407155616030543d20785071f0031947c10060070001002602e0310980103604500f800e81c0d9050042d0701c0c05016034007600700018620300820000f49502803c0001000b0095500f810050005078440d8501190000444050603800e80030741a401820034907004075040c60032141c00301d88044441d81070f10002c0000c22008000c8941281c00c1c0b584100c80782d82d071820428064811a440a030348a8010000018107105690010754 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 361474685 1250 361473435 361473439
    0x512030c1608090a0f0b071101090503010c0203030103060b0f010f0305060d24050c13090e100204080703050d020d080708181915050702033c0904050a1109040b040e010606050405 78
    0x440d41d02c580082424000e18000c6c8003205104200020120345100d07003a8042080502d003041c070007600c03880440c2c00c0d59401035015016a03c04001401040140d014084980c0000d5401c801d8030b1200b400005c1100200090410615542d1000f180d825100d46000703400094000c0480c0749154685100c0803000c941c1c04803d0740006203400c0204088816510440e8909800e801e45011a20706068000c00107011780e040c1d003500ad01c14146000383d41c15140c00544010b00c0703040090b154040c0340d8100141000a803002c0a011500561400c40c004d580007103106800142c00d19091200b035807403036101441c07007414011640040c895900e0880d03403c402c09846580040c45a400b15240020748600d80e01075807010f07100c2f18003603041400303c03016807000801d8030110000303146e0b1003503041d40f008840504040d40c662001f004000002a030200b07282043d000351a080a50000100242220311241119601403245490305c034640740d0300c4444003a600c80c3c101140a0610600800030309075104c0019000b0780c05442524 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 361475935 1250 361474685 361474699
    0x110a0303080703050624130e09010c1209080403110315160e010905060304260706020d0e03091f03060e15032104180e06090d1b0512030c160809 63
    0x64640c1440740e148200c08841d03445d080006d4004d4410b050307080c2c001031184900c800700018001641880341040e140035581810000071000d0010700000c00410060a800c41994100781c0813200081d4a00100c0d01183c0e000322140b500b80e011840000d00b0080230944000e9801038800601c03826040d1020b812692840e65220310b10148498001919a0049441016031088003440000d010407a00303074103c40b100c06100c60b4000a543c40201100755500b001509507581356001c1914146909640b003510b506104c103400440c00c18803420002030354507011000c82c00c441080744854000990003904004081d25003203940c4070072442c0080d4003882e200262662140300740f098080b003044062040340d00d031890101103101c0c10b29190070322506400d601c203000000081e0310b98820b20b0405019060043d42d0040e40c041015000d9a01c0005000302640c141d0140f08060f095844030305800908001540014080400201074030303695000da280c025801000c224413032600c040e02c0203000300711004000b01880340307040f1690 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 361477185 1250 361475935 361475941
    0x120506090c030a030210150b0d0b1806100f180602011401050402070803011710020301330e0108041b0b1c0b0604030222060909060b030c09060d110a030308070305 71
    0x10307661142400f0103009030300031401040321807074903070401608210300505803408203948000c5440c1070750100b060710203200e980701090942d52801c020020804411000424050308180e400075929100c445841428400300350030302c04e4418001c501c4800e0f503a10045040e0305003641d80b00c01038064800ca600001108849800204103440c0500c00e460010390000c100c01d065a0a22a100d24810b008030201511480b03a8002c078818036030240000d60183c0a0003000c01c40c0d1044600695403940d10640c80642103007e00b50024141c00d602010411032500c00740b820ba60710340c455042c89280d1005c101340300d650410b03c11002103090700c05003008150a40f80f0150060a0020400d081001c03555508421903004030b040004102501e0580c410f0441e0b00d008030104419080e05001500440300079901c500ca40c5501c403c5d915003400380c00d1007081100780d820f50182200c0a00100018807243d802040c03503110b019650302900501510300400303648454003a00100601e0344a040143c6505c0c030490340c0200081c242400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 361478435 1250 361477185 361477189
    0x30f042d140a0b0309070302090915160809010605130c031107030203190f0c0b06031c0207050f0306150d050703120315051801051210060b0d0c08010b04030f0606120506090c 76
    0x4c482c031601006000c1c1001d2401d603802c210480340040d2061041c2d200300e030440340c0c000991003600750141004048100d02c00c102c582d4041d001c440014000342d5264903104d001c00168540300d200c1182c4414011001400c06540341e001e400418100070040b9000a0105041007015000001001c1003000225a00c5603011151001c545c0390f1910140328000072250040400010b0f1003c03196500714000900790790f0320100b035810001314100a100702e04c005130b100d84000c0049082080c40a110078800b58040c0c401441c02586c40c1c0030385803e00340c0c041d003d0061100d0280c140b0009125400c042c541c420f2a031491b4108110b4010041e0115a211600105402e44c001603285008a4440345203944c0c882d030071405a00e084100042e03605401e805203018020b900030240b2210880c81040050041a184191107400c620020700c103c03006011030f2010302000794014464400d002068074112a4805282c00c04010701d45018809058035a11452000c81c00028800401101085081c82030500c00200c2e00d0392001142 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 361479685 1250 361478435 361478437
    0x3040f2301110403050c0a141c1416060504060e09060d0503030a0209010806040b100f050c1501080708070506030103200418050d0e060a030203040c03080406021e030f042d140a0b 78
    0x1003074501614600612303d103d0b06040100c40c1640c2240d0039041c0d2001e64070703210f15240c1152002000042c0d0030140340d0b03402044130314015102400b01890180d0500b400c100d030243c9024110150140300f1000c03007002488581d90100b0000c1c40317903404030580f40c4a0a2690b0042c000c2e4112460050102c3c010b040040c0302410a4401c0d1181094000c1c1503400009804c6010b071926000c00b081003041120030480750b0800b901c2004040b03101907100d00c090a29600d4202541e051000c203801c00c1e1a503820254007040166900c4c801d03a0f0540b80c004514008681c0c0d000f4003204031240c2207801c40c1d00300342000003c040d458819145042107031300400540d800f181080100300c6011074060202540084d0034000c3c106050301c03d6026590191003541724882d92928bd880700d141d103400a50007030b801680a04c507408640900007650003000d0a503140207605102911006448034003d41c0a203000c1c41074040b2041010f5044051611000c000aa84404031f0949441d0044003400804a2030703809980700100000b80030000380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 361480935 1250 361479685 361479689
    0x1e121317031005060a0c0b0a0b1018150f020c03010c0203030112020a1a0c161503020f0d050108030409060602150f04020a08010507030c0f0503040f2301110403050c0a 73
    0x580412825000014034403103500054006880024601400306203601c1d00c1c4000d20302000320342c60b8502584420300c1d00700616000281118a01c40c00c040350a01c4a031202d00403007440a0190600703501010045600c8507181c0c0490b400042075030450035010b1502600301c1040b17000f090155098034500d28410713080c14240d42d08251f407100145d20400040000001e0000602c0c6100d100030111420341d607950f802e0300c0c241c609811541000850010f80c01e8000c0d001006054040440010210104c91038560104001c10054115206060700020400e01d0703031140000302c814030f1100d4441003080c2d5031a450390faa603e41050003040300082c50400c0c0802d80900000740381840d4001c4030b80c507502664619001c0d0881c040003a008903040f41e0071450120b900c000c2801081d22560b4aa036002440300c0c86a200142920400c80d60f59092107000c10900010035402c6031101d055a400401e20084c0b00340315000b00d01440c0270482401c5042d40b8162880e110802050010400c40b809242114110841c040400c01d440180e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 361482185 1250 361480935 361480943
    0x110d090608070507081207080f09030403030f030905010504031e1b110301140406020304020405010b0301261c05030103050c040c09140a090608061009051005090c1e1213 74
    0x441003040326510a04140b5400000e500c3c200f0b04241e65580c80c020f02d90402d190380100c0e4502d480401600350390010a0540c4010003106032803880c2461601281c80f441540400740400c907004149a40b074902940210525591150003013000703103443d00b0001c200d0b4840703140c00c0d03402c5070f2049000ca800d244900341c80e181c1003202d00c01e4800480c00c6580c41400e1001e540d4400c0760155211908801c0f600510303402d480c130441c01040056030380c2c50140b04100840710140c1002040314001e0005002c101e50032a01005c404c2d6604c020524a40781e0b440e10b2524009000720840310050180480762207450b4020007841c1200d100e001141e40d1020074a0401064641400c01500000c0c0d000c20104140c48600041e116440c10103050100c12743d0300c48030604256120360f0041c0400350b1100050110004000700804010010110100602d08059454000f06021442603d101340b0841e40484c3d0400000c0b000c440350a000d0000903441d480c0786003810411508901c02000c00e1440f00b1000640c40102c03058a070320351700e40c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 361483435 1250 361482185 361482197
    0x7110f03150612010507091e1503090f02030f0c0103140105060f031e100e0901060501051b1002031f0f030b07080a090f1b061e14130f0303110d 63
    0x521100d840c11030740c0140041e50004208002c18001e040038030aa41c0540e102d56074092040d403c10000001c9880207140041806007a0b83d01006000716445000000040318070740806d00c10340c14104044009481d51b00654940102c0700c40c044032580000e580621a00c0c00c0e00d0901c01e19284840795480403009104058011000304050a882c0301c800e002507500910400c4505096001e9030b03441480360504480340d030340f0000e10117414030100c24400e44c0d00d5800003080c2c0003031100509210000f00180034006072540d884040b0703c01041500d5040c0300b03848290704140411510ba1402c241007038001000301c8442c090011040d0000309e45ea0f4855500740b015290040c40080c61a11510001c491141d8010001d0602560382d4a140e000103200d0402d8020f13203030042554042d8400762000c81010800c5541c400e50a210294146802131880e1034501a01040142840420090308407174200040c821034040d050b40a44003600400c000308000c01c800c050320700903941d64051000d0866120380d02c4010f1003401003c1030b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 361484685 1250 361483435 361483453
    0x1050105070516030803040b0903090d0201050f040306021317030f1909030503070b0702060109060f05090a0212010e0a0c081e0402030712060506090c0f071b0e04050307110f03 77
    0x100030801440001d10030012a0344074a81003c1d507100400c4a0b810440c0c1c2c0e0703400081800240b101038090340350010340038400b03103242c0350400b80012584590020001d05018000c503143c0030101514050382c000b90b800c004190f599000c174140311003001802e805646800c048480c0c120805141c000261108805035035040c2e0329010b4101310040811004950034010400040070200001c1c1c8280f0291078618400c030481c0d01c0d1401c00d00406414070205030041d00000380b4104e000c0007048610441c42c012a142a1011600e6440c0d1100b282c020703108004040c1c0c1d945600c1e0000103040c0c10401c200c14441c507403503102000510b00007601259454425500b03060380950700e21102500b48c0104034059041131008003140c901c696140c2c1c0042000c5240e90b0103980981c0d84808122441c2841104158804c109452451522080d1411308200340035840028160380e9003505122801220b07444620094002e1507078000007481c040c92302c0d6650303a000788008c5551202d07000d40c4030810304001c04a50010800100904100303e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 361485935 1250 361484685 361484687
    0xd080112080306031002040603021b1c0503150d1202010c0302091806041b050a110304081e0c060d0204060318020f0d0302010f140405070f0312030b19140414010806010501 75
    0x1e00060721495140c0201703c0082000c0340c6500c014001024180c038050f88801c00418180b0000c0900300343c0744016002288080101c102029650a04068604101c0d4032038a85c038080c0c8070300075443d16100e81c000003105403200511180740c103490202400ea5000740004447d074030046050780103d02c001038020b99440700e4400030391643c401c007561041001e0310004850401724414128000900d4000c000725500086058880f03900c607500424a4140c00d0046150500d024074041d9100c0f903080241903031052502d8010840c50703091004a00e0303120000c020035110003145910303000a5009200c1d507404030b850840c056250302c46954992514540051400000844100c01e00007007001c0580308900315541c0300380d40302c0c1c035451030700c200c20140824100c2c07180c0520341307840c0c0103151001503007100c0342c1012807200800010f100b0030f9941c12001894600800e072955180c01060898080341d0212041e040701e4100812084150014251400300c00c40b010b0191341441d4154841d1280207002c3d10b5003d40080c0c006000035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 361487185 1250 361485935 361485937
    0x140a0516060512073506040e0102040b160c0e0106051305010e012307060207114b040f2705030409020f09060c01050405060c1801122304050d08011208 66
    0x255010311845c2815004104417200b202c1400c644070758494207803100307100d4181010303c5000f001e078030540001c5140c40e0925050b4a03090051440301201a0540c041c5981040b441b16180b400030002d41d1002200d0b940c607840040d0154014040032194520720440000d050341c85a09460000201a141c40c0d6014907041104904e6046010f050002410104000d100146031840200310345801082c4130040c002e2842c041184030101c7c44031a02155480d0440026001c88044200a407490407417a00840619060305091b0070400324040c480d4828a080382d1842501c000c1e03006170710780058404001b4400c0c807241100845030b40461002900550090105009207140c0d40e0040c00c0e012240140b40d0700308516a80010400d038031032807000c034660351600b00b4081000001c003d200d4102550039511820540e926604009070040e000c0722604000860019501c50340c01e81c3e111711003c0301d140c0811110303004460100c925500050364211020301c1201d10380c1c440d0610582166051b52198031007a186140d86407100c1c1c4507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 361488435 1250 361487185 361487207
    0x2105131b0807060207031203020301030b010b0a0207050909060901150f0e060427060b06040e060402030a140109090308060909210c01050103060b040f0b031009140a051606051207 78
    0x61180340d4080400c1030203040042400528580d4002c044682c01c526080c0342c50200350009906140c0103000510018041d15451415500107001d0359031140701400e000c078a006c0c0c06604c00d1b9003107069082800416400440c02610070703003151000340403c00740c02c034480701c010030740d48600702d40d40f020240180003c88113207a2441c2c214400500200c2c0d80f49a520b0401c90011040d5141c0e03803d0031380606000c080000750701a101c030340d680440303020b402c05150840f82c0540400040485200c1c07070340000000d0542ca40b85d4042c00240102c0722419500390784034003904008000a0300140c0100b000c110004201d494900b150038032840d5140702a0480b07202d64cc0d8980c02514441d414440d02240500850800b20401d124040c02103010b07000101c3e074260749006000440d81c42c1c1d8a101801420480b43c4c0d985501c0008241070b01000d0760100180c0d50302141840307580044440c00015090080c0e981c21014031100150621018001d00d0240403041d917074000c02c0d101445003d1003c000c41c105240080c1c10903000d0980f071b0b04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 361489685 1250 361488435 361488473
    0x12030a0911030606011e14130602061b040902071b08030430060506030f0d09051309030c150209031b01110f0d05090a08030c0d0e030312010513110a210513 68
    0x1c1d034443c0847c002c1c141d042103100346c2d600801c1d10001c210b9a54108156030300840380e0303a12010200849065403400d407080d40036100c003243c0c0004440080107002100c00d01d2100e0360501c20700700503886580181e1290320070320980c4d2402495000742600c140400c020700500c000841c1010b8444038055a4100240c40c3c001d041d2907050189214141e01d1080601c1034540c0301c4c03001e6695415040c2800208401c02c008185c0108042c0d00d0006d81e840001e07040240070000d00e400030842e460001c2c4507149040a440791801107a05401a08000c0d0031b40b4014205410039131400740c0380c00000c0040800074556600841d051603940b41d11600d03882da240e81c000d10050040180103041008000e07162242d0501d141d0010b054118a54040702070341d580103a22400030a11041704902075450580c50b0000e41c0e01595040c019a803181107110000c0602629650054011115030404c6644031001e40c1c002800216a484954801304141400303291032810034841c00740315211114100102e140789440d40000c403024234088403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 361490935 1250 361489685 361489697
    0x40f060e061003021b0c01032318010b040f0905010c030908071509060227090c0a05160204061805100302090a02160215072001050306011112030a0911030606011e 71
    0x40101440402c83c1300704172020100a02003500c541c40014100c078400710302034924019119080c0b4899410300305242c1c01c10500700000d034024503020840c5005000c50155070340d01ca8a40f442118001c0c409401c428102402140204486000d5410a81c00d440340c910006005140800590001989140d8400e072031048462000076118483c0e52010100c1e400315440c0c65010b6200031801c2040025650b6a000c101419110b1000c01d040c1041d408499000b855600020b20101140c1646c090103e00300c40e18056400801c1403060642d10300c032106070b00300844e40d6214524100300028a0f9529401c4004044a9000e801c00c21681e84141c0e07180000c2d0000c4803005090660a000040941d445410181701140840070307142c1c1c1c071444c5140248528401c1844184050140c19004005070b07000400d8032362107142030809040c4030086c1000142040e1801d0302c444000007020040c00a90792496001407121403141c0356450320b00b1181c200f019960802110140d0003d81c2a500c20003c0c8003003a150400e138030b09181021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 361492185 1250 361490935 361490947
    0x61b0a02010b06161e2001020c100e130207030c02060702010c02031204080d0305040224040e0a0b0406050301140103110d050f0d08060d03020a060c0e09070905040f060e06100302 78
    0xc443e0b41c00b100b405070044541460500a00c14918082d064030805842e2a5405882c10364806000400b001c448503903005424840076000c1c0d0092000180c20140180100b82c11600c0b0000036105220a5580074021070304c02c01c15902141c2503200b2500450f405844118500d05564200040d540c0203a20490400a0004032000184c404001350f401084c0c050034240e4490b814203008a20301051840c601042500b44020720001da02c40300c043c503003a01201094072040f04907400b0140e0b42031042d0742c0044400c4d060038003045101d44090b8460880b0450484090080c0d039591000c00d4262040419a007240c01c00b5400108005414492403108051014041d810961200c0d01e6403800e244640c190b02c461a084180c4501681e54001046a070080d801c0314207130100304940d1402503503002c3c51a00102465900e540e43c1c0c2c0080d001c0d40950019003802807070710019242c643c000910407a5540304080c020f03402c00c0091201c800c40e41c0507400590742c0c040e00c000036981d502020491a20f9000608900303141d420850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 361493435 1250 361492185 361492189
    0xa0b010507120908060601090b270d050705090a06081c0e0a0311190b04091a0a1d1501021f0b0301090b090d020a08120601110f01140108061b0a02010b 66
    0x3080b40702050340c0341d1003800c81c9000c0310306041c4040180301c1c60400116500500c41c0c2c84030102078840c074507509429441d085410540c803070503031a54081c10941c4042559460403c00800241d4142035404c2500d184c05581c07512020f04041c1c070068090040c545c2c012002c0e2564a08100003922408607651401540c9110960003040346070500f500203481203c0307421401020340c14075407211605554422815485540342c038481c0d140c2c500603030144811403911450700f0602c1a844c00c20110300030000034110031a09a881175040f02c1c20001c141881c1e10f00e55900006040ca40120030703180307441201030f000b900c02d1211601a00080485036030000032010f9907218600d426441c2445083c1b500381c486e00c5155420300b014400c603882c201004040900715448885108001041a02520700c242100802842c098843c8001070354002210305813600240b10f01800c0b01200b0700150810003a44040703152005450343c0fa0808140c41e07440442d41c00c0b44c8040d100a600f08550940780003480b04044d00d100008030340d030744900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 361494685 1250 361493435 361493453
    0xb010210110c1c1e050f0d0e0d09060905060903010f18150204030c05131e15050102071a0a090801020c1606020c180a06051c0c06080705030a0b010507 66
    0xe80315a0840c004104460400d4042110800540114404004403603e2901c01400c8020514201c0c9840d140040d51405240c0a841681c000701d44100b0308903140d0b02941a05401001442480c030094410554808002400303140224152469680c4982040f03060009104003035102c8103845400d50350342d071503202e440d2045100b505581178441c2c40804449010f804d10701076180d100d071081040a84100b00c100000360901040354200c1d48256039015244074500740300001083c0c4003400341000e21840521074013142050740000b1080401503250805548c1f0340e00120783d0b844640c090380c45050a079901109015041101426005c95a4540340c10200d032540c448600b60f80100c4100ca00d1503201d0008084440800781100020784001e20041c4484480740700043c004810b244558007001090314041354107241c45801c004060000a880c443c1c034101300500300e0301000c080d080280d9000400c0140491118490700955020302800e540e10780c21515461105002400d1058006051250070041c400000d042c0e52 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 361495935 1250 361494685 361494701
    0x12021315060e012c0a0f14090601050d020307020706110304060e04020903010209030d09090f05090c013f1503080304140a0b04030203031603020f1c06090e060108210a030b010210 78
    0xc0116004c016a4105002181c0c03001d41220044206116050107992003010b131910030020308944810303807038a54500586e054854207035840c2b071a60001040101460b0000344520440c0c88641c0c03201610b4056032541a100c0c0103500400000440150341090b81d40f520f174000d065205401000185000010000645003074102c1d0124404581d1070300381001596650b100d94070b0b8802c101074042c0681d10b42544071903116510441b2803030500c1540c10075001c1c0c4035000f0340d036a902030880e800e50707126052129490708440100761340402841c900303141c1d00c941e403a6445a002812070b58015051411a1220390343c459082800d140225090311800d249403010a1001c0610340c000d500a4024541c0d03400c042d14810140780c042115041410300410050500310003103002c40b10032102498441c092005881d4a00019050715800310828a04150640060000118a00e0704a400b80d40490b82c0c81703800c18200f01480300c600c0152002118051148000303481c0070b40c01030210200140305442c1c1550b001c01204049490344 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 361497185 1250 361495935 361495997
    0xf070518150316150c0b1839030304080a0b0408090405070e010e090105030304050409030302040905010305010b0a090b0a091a121c020c03060a110409020412021315060e01 75
    0x20460410000d01410a0101c2c008198640205d603c00952240c10801401824900008440c0070318080c19400502140320481c0b05402c4c019a002680c0391014124003140c50409820348070314003840ca2a06e00007040b03600b00c0b400e24010744251591070300c9000c0304400c01441994051820004c07044540d89510802c1e10a01258a400c03800300c600500051024000c0c80750180290500e0005000541d0f002082e18100d4004503401b15001c9054079088000e4000d5030b0000b15a603041c81c0000c810414190802e0403001816510b440c04650b0307840c0c0850603101e4041b0460340003580074105016840c01500480c10011441903018482d060f03040205524406a00300d25480350880540074000011004031003003031118900c001c1c00368440a1300060f403107040280c24020a180d513008a41854840d560a840c0140030042c411501c5555400c44400002074514089204401c50450003040e1010343c480d2012682e44c60101c03c00c8039050080c07d9402d55031a804c624107114140e0040c5100b806404940f000c82d41003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 361498435 1250 361497185 361497223
    0xd0e010204170a050a0b0a241d07050901031802030604230703020609121c050705010c081510031d0109050c060a0210150e0f090f0705181503 62
    0x140210202890300000904205030f04a0400c00012910000342420400d422210120980d214104417034002c1c108074804042401c505451300e0600300644d900704003252200e42102526a07003030a64941140c0301102d4030f5010070810300031840301d9480b03948800c10354100381c075003400415041d800003440e00d681250200c485584d040d070740e1201402c921180e5a02d06003600d00512010b0704550010f42e4900440d543d0501030444600c520342c0720001040079100203075295140c1c0d164844000402002079000403001d07290366080c0140031147c1842801414480d59800c0c00910070800880100600700400c8030000c0201a00ca00c40314118110380c00c3c0c100060403440d4000511800d661402d2810501040e8515200381d2050040d0a9040e4010420202410245c0d01c005030350040269035175036000c1d00d80c000c006180256810800c80103503024801c0e0040564400710303205010040461651208240900c54109980501c80c0011100c00c01000780c100720341000d000c0707040803d803012916001034111107180802c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 361499685 1250 361498435 361498439
    0xd061203140307020d0c170a0f08010501020a030f030e010f0519060b040b031906180506240d0e070503010e07030b100503030f16020d0506010f0807290d0e010204 71
    0x508850419100820000700342d040d4601010043d454071990141102800390148041c0100b02c00700c5c00d20070400d21241c0c50580c0310b000c01500104a4030340c04400c50080742d014800464a580002112035520b58107555082c0e144413125002c601609502d2618a649d42d21200103c071100b440e8099184143d0386079141c0c3c680038004440b6807007a0340003039011403104a8200018403204200f041202d0f884548035032030200010303509d120f450090109502c4051502001c907844c41d56000e00750487c60140c60100d8502040c0c580350100d401038901c0ca44e8540340142d20800c4040220703001c6800030904800d802c01503c884c030355a5800b090a641c0c05041407884c1d0f420041042c02048010150907820500d07084200d09804e040c4404247d8910581a030081c50300408920207454660031b51541601c141e02500c1d60078019010b140c642e996030000e002e2030f1300509030520302062011000651078115075180c41411a01813520307111320056899840350810511041002000070b01c914020004200c862000059482d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 361500935 1250 361499685 361499687
    0x118022701021e030a0c17040e04021503060d03200f0105040b0c0310120204060306021b061b160305090901230604081f02190215070804170304080d061203 68
    0x4202441c141501044220076010b00b42ea0020507603d600e0080e051034106c0303904500b404420b6010045001a41c99030020780424400c03c601405405a40b09440090300417031000c105869901007203c1d01e42c2c103c2c44c00310069011912503c41041c80036030380c41501c642e4003030f43c0400c0380c240f0394841e00b242c40513034454040c0320421913020425680201658406070860824200030000200c403489290138511a04c0000c5043d5035855000100440d4407201c00c540c1c40350070300800600011520320300c01307040c0904000107c10420301c442d0100c1c58a0440700d61468080020345040444445e010140d00300314084c840c00c00181c41d4801c00e6400380c042c20028114901d864007580e812014954001c0d8000d104c00d02040040c0000003401a0307005003d04c600d40c0e20606600700c03420090161404c444800a040c0a0f1008050b070045032480303405d06143e26590701652600e80035100c100060710002c00303044031400245900e0000c40059034005200e114401c0c500a42104800b058824a4000494403c00302005d00109 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 361502185 1250 361500935 361500943
    0x303030902030d090b030c22090e0c0f011b050a05150a151203030b030a0204020a0e1836010204061e11032710050307090b04030b011802270102 63
    0x1404082c03400020217414182c454a0740c0c00090144100741d0b001240205483e4003c410b01c440d000940403e0402440e9141401000385c510416004800e010b4180002c00901f4000d03000c080d12401070311101d421440a00414403111240c070340550b5035008601c1181c0015409103c0280c034a4003503a0701c002541440d00341c3c602101c0341d0740d040e10400c1800311000c1045124075030a83d0052a098100080c0032030034000403d06000720914020340c000e100260120b8041e4101c4000300b0220010707609008100d0202980300d142d41c41c00d0302c60041d00b20154031203480c401c0c0a11405a103d00c0790441468200300184009400d81e08150030082c0410b03d200c2c01c1c0c88a0019074040c0b0140c0c6881403808403580c0d9496090551644104501448201c003801c2075180045080240140c040b9406000e00301035039100c0c1e0005000d50001e566408c001090002d000801040440c181c60a4139081407041d98030740d00c1d10b4400e0064651070584aa840d640034401203041c103141c103a950100115003101ca0720050b18803c002428 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 361503435 1250 361502185 361502203
    0x605030f031801030b011e0801090e0a020d06050c041701090303180f03140f0409020a1b08030708070c1a040b070c0b01050607030c05060a020706150302100e0a05040204030303090203 80
    0x303564418400340301d030401000800d2078000c02c203080020f20f6440400040b15461105a840010030118024580320b0300c2c0c5c00918a4103c0e016458100010401c4c40c03210b903110001041d029502160960045001c2001e6922071908807021041c49490141c0e0354480740020098240c00103006d96603040b0081c145a0140200f10102c1d1451740060203400c0d256456004848025201508210782070301d40011821119080303601e10107808000b55280c40e6203424900c003961082000c00c000078042030390750340313044541626523644990020340581156222a821611100c0080c081820048180c01c1080403541c0005021404070400140b04403d2920742070000f101e40c000b030808030400180d00a41c00100d40c94044141c1074440448407142c2e600c044d410101c8029811140c00303001380c01600c0600565103d00d030f0043c000c09100d00814481040401c98070000e81d0094440650803602981045d1885407141ca524200304c003000303040030401e075103c0d00803030221380040e001180420fa1324241d0f00c06500e0104079890b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 361504685 1250 361503435 361503463
    0x307050d02091303140c060a0c0807050a051303021203370c0203030c160e060a0e010501030914120715060506040b03041a070f11010527030715060503 66
    0x19600d06560108409020040c4802940c010500780e400803d48a81489280074920800c02c94483c1b62210b005c0e0384458054420100080c5804c06d1b0a403128050003240d44280b5450300c07500c0c101806c0f0b16040d00d00c0c0c0c1c07003030b08440d00455141c4000300050791070010182c2201100340045031108140e22018500145000c501c800042800548142590341e8040c4441100340c6460522001e07202480440e1850040001d6482140100b01d01100c0c0f9082448070b20b0101e0f0140c0300c2080300ca440744402e200c98141d85001c1c50b40c0198800006000360f5000b90841240a48035417404048840a10015801e10614028416641c03c00145040a0000c80c900081103150011010450149800d0004915110b184130704803c0c080044001010320061901c210456a10f0200d290140d1605150042c03030988061011801704203074110004c01c4080512460307124115452030791041d91086401410440e801080301003081c44204985400074044041d522152102e4080c00300c2c0d2982408101810a4031801d0018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 361505935 1250 361504685 361504699
    0x705010b01091a16060203160f0e1305190e1606090b0301050d0305070804030804030611090a05150c030c06071709060103150e03070b0403021603030507120e090108010209030705 78
    0x1002c80d500310032040c8541e02c00140c3c1d8a6983e02c00c020040c145024450300074094500c04003c01150b210a0910400940c646644411008912890580715440c000c00020340001a000c00c0208007001944001d030850b5403002c0244070380070f800740d480e0180c6408804048460300046441c410400c491046d11028141e00e0900c40c03601c60521007100d207540014421035110b052031554850034140a0400ca412407900007038169503494481c10b228130154030a00c42242c00901c2c280420b9069840c0f03400351900098000c001e1076010785440708120625a5280000000d00e00c06c0144401303600041004185000b01113025181d00c5c0b4124a01400c00b504039001094404092020801c070740401043c030605480d4490304d24001c40d112003245030000c040e01c111110031844005852002d0002c0192641d1056209508458209500098481d80380e54039120041c04180d05100c1c04c00010392500c0010124181440c219194100c81000580610001ea000d500c442c0d50000c0c02c2c4202e030409219010251400756402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 361507185 1250 361505935 361505939
    0x3070606050a0f08060f0a06080d0c02090711031207030213170601060f02031909090f02120606180105071a101d0105010e041805161806060804020910050307030303020705010b0109 79
    0x1d540b6172a0041c40e401c3c000f18810006100b0141c40e44c411070182443c070007111889082d01e04058104195440182d2007603d05400088d005031050b00da070344074840f2a038061401c007030403d1a04004030f440541030400b80742c0c0a004c00034041001941758401410040c094a01000c0000320443c20503070182c11600030800000c40d04075104e50000101c909210f840c4801100d200c401c04003c42c1c004990740c008841b035506040460011040d1a00a0049404505030a0b105ca40b11001000b4151041025121101010015000e02d544c007803406068030724018098424000c00f03810600340700c2c03103084680c01d0100b40c404106100100c050500c607070003074100501c1190035505040000e0000c02d10487e5562040c1e803550084900300060a15600c00380303900c08121001003100213001e402c3d49000f401662011001c40130030b80404506405901d084800b1603d031000e290316543c003400034582c0b004102009032400080e0000701520300700003c40c0110b02039900140c840d4260301c1c003d0309448550880504005070741e081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 361508435 1250 361507185 361507199
    0xf0d061401050301120c15080a0e0d09061b0614070f030903170702010e07150e0103060b0a030908070b070206070e03010e0d03150801020c030d0e0a080405040b040b0303070606050a0f 80
    0x2128107403511445c1d00d091041c414501050012242e07002240080c81c4691030f907040e90341080e6898002e003816074090207400000313461680e2b60050208007030001102030400300025406481400c0040c2800d84100040c08001d468000940b950715282c000030505400070800420b0380580150358a1400e4a0140306418403070310000c00020f0055400d07250706a030040400c0c0401c0c002d40c0011100003070a000d680c0c0560342e400d15540d006504407044000300d4400b48100c85950b20074030881080d29038083c00b0f00d04107020b01004600a01e04040d0403900d6900401540011521980c0114030605503907000701444d181000004000840b4548494001d0b810510f10140082c4045502c070b00d20b03545442c5c00984003000c22030a10030381250741d11180701544005020100550048000c003520110304cd010301001d0500c00030a507440801907009042d041082c0000d0040c1d180c0f13a001030310358540c003c00200c0c950301008000383c2140c0c840001154442e5039910108054103100341090000d100c10520030607146e241c044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 361509685 1250 361508435 361508437
    0x16050a0812091804061e0212010b0c0106031406060f12061501030f090506090f16210b07030504050706031107080c150c0408010e0a121d060f0d06140105 67
    0x301805500700114401006032240c403080925450b042c6401c0c0b8041c00c003810b01d400100710301100b0000411a904041d100661140211211300e028000d0600c62a847d02020250642007684d8800b59552500310002c01310751401c104a003c425684040c1c902d508048023008403036440340410304c0c0251007036044a00c501c1000b145003548a80348600142d46891b04d0320041700108200f100c03400c00c061805102c84c091010000d5100c3c46112582d04540502d92091442543d03400c1c101400a0000f07464541407001c82e912601c00a00310130b0018400800c0c0c170f05035840c00781c3c4040458070003002a540b8020007051003010130445000f050740d8203040040101000c0c030f0a10b507100c2c9000180c000303031000490788a40c07e0100101d00b5402d0b4020320346401030030003026013129580705100e6400d4660030300b103600341c02000c0401d000c031440ba8820500c900c17a9529200546001071043e85401c00c0d140504603c800c0c503120710f0020001c220a207a2160b9980b069024100d00300e41c00c0e60010404960a23884201c02640c00c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 361510791 1106 361509685 361509703
    0xa09061e0e160203040b271002120c0a080a110709060f0e09010b0904060c021504021503091f060e012108030606090d0516050a08 57
    0x4005403030214030318010031007403503035860108551030b21505a075640079840c0d0050741d06190b50b82001481503000103102c442c0440403402e541c8682d100d60803490124801c215042191400407150003552466000006a03203144006107002c41c06000300a00704003103a002203501e0f610001d45000901f0100e40c1c0b102811944034188011072841803a000e00003c2c0d418259241481c0c03031070320650280d01800901282c04555864012000644421469521031400340c0c0c404070b5100e1210800901e401c2e1618030309100e020140301408011b0303842403400c4104400c610320164503a02c9101c1e0081c10030850001c12411110010041580300c40d485d0010003c5403502124040d9982c1d0314104151141218010780455100c0482c00c500000d011401641d08900081d000c01d06002e03201003c0381400558580070b8072103034480d0800c0d504080c500c4400c0c0002d80800c1d0351131008503207810310042e0350302140c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 361330935 361510791 := by
  have h0 := BRFrame.cov_init 361330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 361330935 ≤ n) (h2 : n < 361510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
