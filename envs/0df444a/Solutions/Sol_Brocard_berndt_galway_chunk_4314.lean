-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:13:18.745918+00:00
-- url     : https://prove2.me/submissions/ba363015-704e-48d3-a8be-007956490a9f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775719424 ≤ n < 775899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775720674 1250 775719424 775719431
    0x70c1506090f1b030209060904021303030e0102031603081302040504050f010c4d07030b100e040f03360503160902030a0b1e100801080c0111210d 64
    0x482e801d036082e40c03641c00183c10070010f1141038801e201e02ca03074050490f0443c02020146041002c42c0020143d802007841c80601107002c1e0002c004058100c803640010420a0001d1420440f01c960001c00c1075250000107410720005c00f000500701c1001700009040558020001c001c1030406041540c1d031000c80400110175503107064003280d0818000c0051110b07034402e003030903a9011a186481d180070300180000712440d960311040605180262001120944a070345001412010320b14204200718210240a510103020380761802c2c07003203006240d0030b00c1e0307c280c01103500e030001c1e021072400311008007000c402c0c99400c10115002100c44218400c032806402c0520101b002d40540390020140c5819846140d07440c1840c6a41c002c005400040d0007450380300281602c002094240340c00850b41d602000302042c09524ad0200001c1c02c50f2070492090001404d4a10f0441550360416101c10b968207200404181480150b01170711000703200420400706401050309a03005983c0380d00e00d0181140c3c11105c3c400f078403a800c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775721924 1250 775720674 775720691
    0x3010f0908070b180d0509040b0418060b190303030506120f010e060a020a0912060b0a060f080a06050f1c06060e0403090801020901090b0c010e06190609060b0909070c150609 76
    0xc61950f01300c95080140e001e06500c6103031480c243d0b200d074060404690041e07220044140c2590391445103903546403452841a03d5041986000c03c02c40f092144801d11854a8003038010001d0301d607041040649a240c00d0010f01900e441000038002803410300c10440c1449105c1c01c140000c0701c107401c4001d008100c101103603565101c0e140c40d98268055504002c001505001041103d00140c003140310b54140580c100150203001c090104031a80f04640121020404d100d890810460f80040e040b0b50044100c68200400760038100003401000e1a00b020340c0c070800c00240710802d02c094244044003083d1b0700440070407040e903036107111140c00c0000301c1d011703030120750b420000040042c0180212901d9420594400c0300050404520015541009903030011640d43e074007201d0b0785141c04120340c03400f8401201c20703a0741008048803a01c003030b10220740000b650340b424420304104040c40a401e94042c820101c0d0046181e9454406c1240c20340c120300d1014182d80c0c00c0d071300300c1c0d43e1018090303101314191210000181300265 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775723174 1250 775721924 775721941
    0x20d200328060b060d060303020c09011d070807110a0b0a050f01210c21060605062d0c0a030314060d0503030a0515060406032702130b03010f0908070b 66
    0x4501c2804111a6403501c148400040c880e41c02195a800001c0c6464104000520100115a4160801c4002d07134820b015040c0e443c604004003500501e1f000012240101c10300991800120010b00002c040c0080b0a02082c1c905009058030b03601581d02d00b003215481d0f9907a052524103858251108503801345040b010512042c20f008a65059401d0004407440140750208810210480c40380103070391260202c4004145881505c12412400c90300003030352200071410703052030b404072080c9a0000380301e80400c01c14100009003e84600c3c0f60b20800180190782c0200c1c403c2c100205c0d1003180310700c04040c041e09a0301ca04158055110701c2c0040ca02104100013980e50500703000c40250403180152913a0f00610018100d02219001551f020490030f0901c1e441d208807101003041a040740e002080440c1c0c40310242c000400c0d400c070405800c4950f03540040e50b601010b801007103036040c0400c0b42a10b00c0713840c1c19000c0e8954030250099610000c2003081046070104504000c0b21641008008450340c50a1002180981 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775724424 1250 775723174 775723213
    0x60711041d190201050906030103060b0a0902181c0c06020604060b0405100e06040b040c0207034101020405060d020d0e0106080d11010605090f04031b0519020d2003 72
    0x246840148404000704030500c1d52160b071024100e0401108116150468403480091402588030383c0380400e00d20800403c000b102d0400c0c1d04010741e20380c1705100019094442c0ca001002c90343c0141c4001c0c0007110f050340300c52204d54449502a040fa90030820004076240e001400c14820f90003444104100c42000382080f0903a0010740c1c21305c1c81d1210510040c000040c40b40202c90b08494001d00000700700180798086030907168442d90035405600208010801d100c0d03495050703076006003001d03120f400700380c104203140c5c00c43c1400624070600c40021102c90209c03a10250304a50152000415071519142d00a0555000e540007004018481d4101010116018014042c0c84241d8540102814100c0000306007100c40c90b0030212a45900d640302c00c1c00064540b1041c058038099448540800c01b503151605014000340904205001032030150024980130030b40200c0c100b556103034900e52021100419000050090011040c007800d030700c8144030b80c802902c1c044a410038080c0010740555003003494030441101d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775725674 1250 775724424 775724471
    0x6160203041d1905070809100b0a0b030907030c080106182309010b0a08011b020607090506030414100903020105070e0f240d0f060522051506071104 65
    0x8402c03900ca0018104041034100c030781c00f024503562201d01500004200e000e8410554030720700425001810b04c89088400d108104115911140900c240c03110600400c81041013407013420150b000c04004290004010321100f401140c0280201004540310100c1a00a00c1c452154483d140b090210b07041d03141149005030740c1444c40340c0100c1d00f0741c482d88012244003010300607c031176859517854881c40710075521443c1500142c4001e0b40005500c45c01c11560540f02d98000500d841598400c200b0041c4541c0c0c402551000d54030150742c82600c03038845150044451800001102e0f0600544c00c3c1d400000b03085a2011401501941c000d00035921000b000399400011041d0098101314480c006001604000c9132102d1811012440044002181c0c4204005500b010907070344003d5407502003248030035410307000341c1000d0a402c4a420081c5503d50711004651852000b155501c252035400242c2c14811141d0004a80d04024011580e00c1c07c1c503190100da00e080c051841882980b034800000c040035491008070301d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775726924 1250 775725674 775725689
    0x150b040b0a02011514130e0d0c1e0605060a0b030115050c070f060f02070f0f14030c0402130e0a0216060507180801090501050a09082205041404110409021309050319020616020304 78
    0xd82e01e03808601200e284103802c0007a2841e41403002b4000c0307803084010100103054010000006d680c00d040041004c41c5100d6070210803a540240018000400d6221600340100501c2c01c0103039440c0848501d13a420440540d000100361032181600103101c6400052200490140307909681c003092715003040d560308140d0350281c1680501d8068062180c1d0800c40390000d00850000d007260703101800400000c3c01d0368400d04c07224001003120304080000358017110303806400c0710700a601541802e0404a141c001010740700310151002c1d4903203003c9a8512300603110719a038040c01c980e900c508562580c03806c0e80039040d094012165586005e000800203030641c42502040341c0d018420381d18000c5c0c09604098900664035000c1c40300c0c3c080c0c44e80016655500d120740e10409140c500c8941c500d18103810108801c107080840a4082e0381010341c0400180d03503074294030300380000b0180000f43d81c0c105424103501d140105d62001541049090290714440d400080f500d11503210241401803d0b031b43d18004907101d004510403105c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775728174 1250 775726924 775726933
    0x170a080402030d2d0216081c0206010303020a061a03011b0f080f01060c2103061d0f04060c0306030b040c08060714031b160c09150b040b0a02011514130e 67
    0x184412411310003840000740b0441d460602c03400301c07590800b00c83c0d601c1800d843c0e005001d030391440078105154401c04c04050024280562654401a40741c511414001f010701395142c0c40c1c0124a80141400c18980601600030402e0900b00c80320001c03448003641c40302010900e04030003040d00c01d210b02c50043c46a001c41300514107903440d015042d2061054008100d640120380701c07a901e041c4c510600380c0241c1000503039000c21040d240100d10b400b4850010b0001d071040c807a410401465034049a081504564840e40000345404002001c8005013000e4100620107410607092206110461070581c2c1550301560a944150321010001d50b50342844209016007104140001000e002d9a00d880480d00c86042070840d01e0000d0310010603040c2c0c107050504a034403da4502092180041620400321804101a4040d52607410018040220b001d503202d00d103502c600009814003814407e4000d045140b045214202e01552200151041c0d80340740d0520768003c40008100310600b045501503900e40040e050081d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775729424 1250 775728174 775728227
    0x50607020d12271a28060510121e020711030a03270f030f1203020f0f0705010f0615030c0e0906120c0604091401050301021213170a080402030d 63
    0x104018402003405881c2c0701e41c01c03032036036881601d01425070303201c0d158041180d111049102e801c060707908100d45c015010249881c0c0288100c0d141d119074000e0300c086c241002d58200c2e03e06000b006c060326102c0c26240c10031170820f4202d5260082038003e8000e44d4841c02000000050040505a450951450260029545241940300983e010069035022a10481c3d081c1545884110740245903135079a100311114a801d410400c280900c3c210540d03900882403505601c0c004800c8202c41007030180800302580c003640054581d08000b0250b0110042100040c82400220340d14140c49020103400310240d00420308001c91010214030492031404c40350001800390317180d40c0319407061040c200c0e11014410b400c0d129061080c0c50076951600940f0040c80c99040100c1e00807074801c01c1ca0601807060340464000d07070060040071511003070202c101c0d502000121500100d071803d0300345006800c0080301c803015052700005040030515486940d0754410740c02942169809582141c049402d614204100c40403880c6006030f2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775730674 1250 775729424 775729481
    0x111f120f1b08041a070804020906120d0f09120303020405120109080706020a200c0a1d0103030f050f041401080114090604050a0b2709060c0307030216050607020d12 72
    0x82c3e410a028800240b10004441e092200032003007580d41c400411502c1080200314640714015a602102c2a11803040c1a10390045066442c3c80d0f8010410504c43c1d10044455901d1094408000620701c201d400014480103080c05002980240141401041c44000304903020700c0500410008592100f06240303441d2554444c40000d400c2614410100071140700040300d118150b45584205c00d400308090650025882c080010f5881c0540c4083d400352440040c0d0300050248410240c1103075058141100841c915110459051107288080d55138440c0220300401c2810164401282c101c00a0b201c8088a0b40c03196914076003080b64810703030f55006050400282c824142038001e20740015401e840407481c0341980000540d4901c07c1c0100e11600c411881841c024040036040e016080301c1035102910050500d9081c10246120042c291001c2c5500010240b000400f074034245401250001c3c1620a01e040c0400029103601c11449903c0010b40d80c01703888545030b80b1500c2501044810b1014024820200703100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775731924 1250 775730674 775730687
    0xc0e0f160504140d0f2d021813020603010f140402270112090b100614030a0b030a0b0f150105181e120d0206090a0f111f120f1b 56
    0x40540e0005160f103e4100003070b1034140b50208080c406e602c0c1c40b5444154503408854400b0259881443c600540c01603c0982c80d40f01a421101202201081155030b40325121210400d2461009401000000001845184030b1000c1002c1c0e43d49141041c04a4140701d042005a000340845042d08816a40440e4461600344a4100700418181040b1070000b4441e14000100c83ea00181607841d031a040040005c0c2503854030711407001e0605400c00e8080e900c40000c5000d00390000030014411155102e0070305c2d58a6900708500004564800e241032200e24111400003469003003616160030004001341403100359030080c4166090312141c0b24900c0c5038080044100880e94140a6540345166003846c1c15902540b203540b2543c41d00e503490310040c6032020544070000d240480007002ea070110707000003040364009400c00d00c0340381069400a641c01c140c0342d00300d0006090b252182d0107900004d14000015421141c01031341141c4880340c001c204104002182444109907003e010003030301f07049108503114401038007515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775733174 1250 775731924 775731959
    0x60f01150210060609050405060a0303050306150f031302030f12030a0b0109030602041205100605060702060724050105031603050705010f090e0406020306120d0f1b0c0e0f160504 78
    0x204903210790700540142c004480c3c0541161000a901d400c1c00d11080c10103005040d0070481c00d0302d20b450303543e1954800910034040a82550701ca07058204a0b00c0c0000c4580040d039400d0408140c509030303a0706140c41c10b0684401c8000089010b0f015031414601c8412000c54111009140f10103c28507550f21403100c0e0004118104d80241406003c41c2c011000ca0160301c040c0c8082e100c3c0c00d00705001041c641c10550b00d001400f0803000303c2681401414008c075140e180c01e41d11040c1d0705039452a1118083e240402411400b00526100c1010241c808602e03480660003140c12100d040d0b007598461207010103c10003140c07441c04081e0841d803100d0350400165100d49034442c41c03100b4078034100d07030483d40302c20001c04011400c1c4c0b801d4034659008028040d4520789a070f4002c0d140441a0000d164240300d065000d40250000f4061400b40426a850f900075804000b01503504a030303004040c0c10481b80c491500100048090315090302e1004614009119420740300d0a143c103400e21503c65038100340c60060748003844402e40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775734424 1250 775733174 775733177
    0x10903050d030b0906120c042f0a09080f0d1202120f2502071a070510050a06143106030503180901030c0b030403030f0612021305070f030f0603020a0303110f060f0115 73
    0x284140500d580c07410408000a4250540c0c0c0e81d52b81e01201402401c19072030307410641003a0081c200409042000186400340c4d524181081c20f540e0000c0082d820090051030104065090342c5020404801c51801c07110f8801c1c2e5001054a0651686002d01c0c010340556403520030140c0c3c42490700b0311141080500203d08004003904003407401c8050707944c4608000024505608c41030b160814052a9407850240801801002212622220f00d500001d100c103114003825503e0240e603040c05800201c000ba06071034003269046e509100c1303241e507803410b90307078a03070004030045642e0b180d4000b009000e24200903110304881d003007409168250304001e00040d003a8000f510440c203040d0b86041c680030489041c096180148031000400c80040d03094014080c0300d214501c10091441d20782410004220340241891041c00c0c16071070000345003100c0050540040c4100e0700069070201040100104140d8000308000700100c641003503415a2120300340060303480005a07080e88290621100610110002480103513010306607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775735674 1250 775734424 775734461
    0xf030f030f0d060503030a1d010c120504030201030b04020f0306011218030801030b1018020711030304080102031f14040207081210080d050c030315010903050d030b0906120c04 77
    0x1004985107a2040c105030350716840100c1e10b110036010b9072242100504060300610714041c601d0340e00804ca00220012090780510608501d0100d92003015044420382c0d01160014401610f8071020304160003900c000c0b4006400d05100c1c03031041c20320740240d80c001540c00f8056030468407164010342d0582c03000843d4003480d0399910760b000360342c000c2c110118510a00985a332042135041d030915145000c00141402d402800304070082050038107184c0c1d0151200303074240300180c0310031440c0760003060740040c1000580c2c10f10003c500030840307481c190300850290f100040300c0161007009090000c0e00340603d2084105215184840c0d42e41418690010501a071040340050302d00901912408807004080d100c80d059021303010800c0c0142c4a003080200c150500743d0411908108000e40700c2c035901c4c03100424040300c00d21941c5030100d40380d010340805c1c4059581311040d00e21008076003000500615008000e07134454000d0001043d01410903808584e01c603d030b444041c054440080c0300344806010440b144040700c555 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775736924 1250 775735674 775735693
    0x3081819020108220f030909021c0e030405120c01030e15150402070b04050c03061f1a040305100e100e210c0304060206091c050a0c230d0314060d020f03 67
    0x103409406001341845990a00004109030400a080400c1c81e005054000d10401243c11b400008040c205000b903000300e00801c5051003d5021801e46c02107034003941c0c106911100e0f0951041c030100701151991020303a0200a502d100f0440907176a20400b540c00c80d001c3e090100801c862026926000643e803402801c0945001c0442e90b500c0c02c00c80d021a41510f0310340080020f0007140c83c081c06819088555480041035101414030591034030b800c1841404d003001000865881c00444d8801610011038200040d20340032104540703014007801012400c00502c1c0211200303041940c41500c0ba403504009540001d100c021004070b00702808102c01400361414482c1030211034481c500400c0100094000d43e4083c005504050038007525280310781e40c00309404031f290111040c90b15408001e81c0e904105c03d20305620200b1440c140000815024040d02048164984540c10f41a100095841e01d2101e0340d0740c1000300d50a880c5001c403403624140c810b00d51203003170304140e1005480c1503040041d209200409446c0c3c2c581 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775738174 1250 775736924 775736971
    0xc06080a0627050a0213090906091e0b010f0b0a031d06130b010b03040201050702060304060608061003030f0827151302100c1101030c030b09010303081819020108 71
    0x1400b41c0940e40742074181c24042c02d03a20300c900915800c00409801541082c580c040150160b1099024043c80395942e00d6952007842195007000405640200164200c074007009401400704c0d0b001c0741c1c284e40e00e40380170700006038030b000740c80c8442c0886044410a0f800c16020300000c801074480803185c00255203601903040b04882c1c0620006000d6010056020540c8180d454406d01c101c105070300095004509004110140c3d0700402168491503040711625500d80e981d00c1c1c501c004103001d4100300050f00c078000c02c002c078001e20383e4100310035a4000d4840346010910180c0485080c4030480d5a80c0040d082509807001d04501e0b2581c0ea40b003c0041c6068a60303c40c1010480300c403c0e0700850300e402281ca840e110030350960500625000d5050014500342c50421069210700d140c59402609050400d641c079903c0d5501240300f6400142c20600041620880356981c0c100140880000c0d130b080021070408054100c0740c60000244100716203411100000a0109500156035040e0001c00e01212085510554100c61 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775739424 1250 775738174 775738199
    0x4050d030e10090519050604261c0305062d121b01140301061b1401050f060906030f0a0803041a010306091b030f020d03030b1503040b0f040c06080a06 66
    0x2a601699940501482c0c8810044001d401c070345d2040c0d181c140d11000703200d103440d14001c480036209205060341119600f9418400104021488140c581c00341d500c00da581d00c454007a502c5015203842c0d40c140002d40f00c031020840d910803503d180d13010f4071880300000380003c0000804501c11000091915040c55028200e450900c160364003000c2d0464001c008400c23256800c403071103c01031001000010b080d5810210003414000c20707039005070300d0111001050000c00001d80b11002440d80000c1c000d01031414030000f125601d41054510350710030010880080d80500b000185080d1090031a00103100c00081511200340c25400940244d6180c035026801d40795410354000c1031402180300720700c0002d1907a014240708065000900100c4110403c0e024200040f030310803010308c00420f40440b00900040c0079443d06400420190784160381081428070010744101d5520f0103940b107107001b22500042541c4a1882030350411302107070000c0c103061783c0c11414041544100d4015903c410045400905542c644180c0580c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775740674 1250 775739424 775739449
    0x303090204110a0305060a150818010603060e0102130b1905160204060e0910060b07080d06261002040e07051b030706020415093f0807020a1a04050d030e 67
    0x100c1e481e1800d010650901f4800b05c0003d10261039280d1038000207403002400030601804441501c0700c0c001c80302c020701c50203500800c019648203808102080f403582d0300c14080e420800301c15000b42c07803901c070018804107a00308890b2000100240b2040c98620381c441034601d500400d000035401341030081003000688461080b0406884210b811100d50701c1c05205040c0b500100c07031001140c04d400c1c89400c00503001c1a4040d40d91065000d0207050325002c0000400c401441b983d0300202e21003035140c400c0d00390129400100001c070702c2e066064416030060010050140e00c0317584030300480540ba40c800561000e1140014203990710011340c44038200d1644290f40c92540d04444401e480751540010b080000d0151f04049034184090340c20304030900b030b19190082c00304680e1100e058010200c28100e502421b1040da59104287c0c114889410b20700311641072660386500481d400301e000b02a01140400c440060711030920045441c11112480c1c80d040c40180f000c14542d080b0104d081c080c0c50411104160b03681090340c0f06 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775741924 1250 775740674 775740677
    0x1e0206010941250e060717091503011406030c04090615080109050f1f0506160308070516110f03060a09030305070c020a03080f13080d0e0a080a0303090204110a 70
    0x2010240342c5420801090140c4100103800c95241c0c1200d03031030440100484681240d0612111000c0e100003c20200e108400d0010603001960081c2e605084c007000190042400603902061600b11490f49660b06200a016215500300c01900f4180180f4201d0300850780700180141c12801c0c50754900300c0c1c5060301c0240d04280c43c005c0501284084641d800f10301107004041030201401181800b50000f440324801518100004007020015248007031444411001840080c03c8159074107180300c08101e07544201d19088000604400106108170700ca1402d0300d80400c101701c0c001845d024241c2d03651a030301f42503180f025000756400351083d80350b65042c081c1034814400c2c00c801190001c11480d00408941000700706c0300078042c4d00c4034400090f0304e80407141029298400222642d403802d240101c03e550090024090440c410b005010483c00004500c400400c40d60703845900c540d60300710041040301101030052402950000c003c82000c20f200e9004a0000c5001400c00900c8080300400c2465a9008000380c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775743174 1250 775741924 775742021
    0x210030f0203070924050f13030b131e02180402030c1017160206011413090f05060703051e1b04180f0902060a03020d06051504080f0c0108240910061e02060109 70
    0x400e0015033380031b200001d03072a41d00b9040300094590010b4004501c0280e03110160118900140464504020b500391009000382460000000310030000d00740384511546154008040021584000142c40703001851005a0050700c0c0c5682000c800d80c1ca0440c1c400440ca40c00205031f00d021200380060312881c04200d0080a8a8084481600b4040d141800144c0700e402014980010012031a071050000000d08030804001c9406803190080c81040e00291890410314010000340007620201c0020b010300d00020551042c015040d0103101c28048076603011000e0b4010008005141905110340c0c024400000800c00010b2000d89803400b041c5c0a9400c00c0544118200018042c032104200304861040d803450400141200c00740a40002e098a030f0203003600d02c0342c80d1035a000d2500380801c05520200b01c071001c0c040103054506903400300303180030380b5110304404103005a1015845a0350401001d40000e50b5400605040c1d1a003020301c03004110084008051212641134035928090801d0220760044400342c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775744424 1250 775743174 775743211
    0xf0503011805060105060903010e0303150915150a050d09050c03010e0102040f030204110409050408040e06010c0f1e06020c070303021212040210030f0203070924050f13030b 76
    0x60071900001d14428914400a40c0d50300010300c0000d02906581d8107841d201d80707481000300800d003d00401030015840e40000b000300b0000c211303010700000445000300c4140701c13280c6a440802d08210081c0702c0054200940d100619000c034802001001c096005141162820b02100410001c80d003210004441541200603c1c0715a880d090203100d03440443c2074003c503d0103252021180ca01845840001c3c0940e85408403280400310341d1083c0c500602d92070105119601c0c1c545841c1489520500419500946001c08145103501c10284542031580c46020600e6880407a2079480000d5040c0c4250002440d21020b03d800281090029101001c085401800982d00b90f14000c0e0602040342038144125400340920074088206000c3d0320f400a40607544201c03404500034044001d03105103031002103c00d00010900901d558030a550f441100c20480c000b40000700e002c80502c14068225100c9000542c091150500c1401500f0050841a0340d8511003030302070f9940e646499103540c08840d0b000001c151903108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775745674 1250 775744424 775744429
    0x2031507030e01110301030f030509030d08100e0105061218030708040f060c080a110a20280e1003020a03120237060603170409141515040e010f05 64
    0x68105110364503009010003840c1c4102010355010500c0051300f03403802c055508c028580140f00701d0b05002c030003505a900d40701180c40040c280c10310030380344840544400100002d80c0200152054113032132000b0a423501e8480c51080016110307001805c501154802076a0040d00e0034020401804003a104502d450348036840c115038840d5100b081e81c0300b141403100b404040c1c8001001e81c82120001045030401c50100084240c5a80c030b4015121001081c600703a03009512a4008481000400414215626201ea04d60400f01e104440240840030452031401d0ba0b050188003820010a40d2041806c20901c48065894000502c0b40c507543c2d00684418010083d00d40810380e05000903603c80f1200c06100c5d04903001c00001c0101d40000c0380703100c1e00d0068040403488c104019900b0100045410041100b01e4954401d19281c155100c1c0c49860b1903145041d95610300301c212418900d10494101d00c443d0500c400160903c482c2c503d1107864645400340400020a01c01c1040c03101e140a0320110365900071443c101001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775746924 1250 775745674 775745681
    0x310c21050f06010c05030d0c0e04150b03180a060c0503100f030b15010e040c120b150d1815061a0c120a0311160c1508070507020109030203150703 64
    0x58121103080004022110400205807900040280f030250f141d6141800d2890850040300c020b105c4031400c05070604039a55111280e1952803008980800440481001244d804111072103002000c0005100165682c107150036158840d6100ea000c0c0c40c030010b000d96039401242e0304400c6850100e00c003c401d100440c07405165003c043c020070480c50344800e003940c0b100022001c00614003030059204010085199106040d8000e020401a2050107110700c20711001e005000003034900c440c5180352503003000003451302000c149040b041d403503002c0b80b074000c0807200710f0050200c1802d020301550705c045020002074a40d8950f0800038100100002d0300f142041541c0910b034840041c4036103500402e0040d4503c9000100d0003012105003140802d5507084411030a0740601540d03904d00d11b54003404691901091200034078211054416060324041503200e01d8140c1c54007e20aa40d82c0000303448000042d4070720b0003100104a1b8500504024802d156254000f928090b08201e0142607054804184aa003039050300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775748174 1250 775746924 775746977
    0xb0405070e011d180f06010e10030237030b040507050f011d011b05010204050a0b270117090f0c01030501060e01080c2a0d0905310c 58
    0xca0028665241c080400c507040400e9040301040d0381440b010450fa8031494554624804d01c00054607424200e200c07100d03448880034400c0d9aa1104400000f030302c1c0b0029410420240c0c1c0c0d0013040d0039041e681a09901e1400b99400d44080100750b4159503050307a044200303006800039407207210058070902c3d0030301d40603041c11025030105019110420740740d2107681c1c1066485030456800e41d03111b800700d02d883c030040f0784510171350440040c1c03400c40c0c8003024280b12064004205507401901c141a0b01a614043d4409621980b18001000c150100c4443c40d4601c0340c100300c640110301450000529641051840c41485094511403e00d0b4455941000e481c0b80c184421003a00f4000d0030304000c690714218019001c40145072031309041209450010ba40311340d501c81500c0c4280d00c03001c580519920500020b00c140401406500404c1c41081c500e9400c1c0c03480b40c10040180c442c0601200c40803400c3c0c005028202c00035000416034602001000a100302070b03407044100c4000260303990121800c0c0c08040c15500d03c00c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775749424 1250 775748174 775748189
    0xa0c060624181a0702030703061109010e030a2f1f0806090c0a030e01240303080a021e031312120f051b0a0519080109060815010b0c0111070b040507 65
    0x104020003030f040c15110802c1114500720580741c0d5884482c4006810b0850075000241094036040c1d0758400c07520000e0140a00d00005c0e02c4403002d2182e4001010f503110030b04400100400c005655103d17142c2c100070240c2c448202003500201740041e42c000060905640a407603100702000d079418058130583d00240e0a81c0080040d14a02c0d00d03801d000390f0060031482102e441000b416103a44c00313455948070175400020002c2498003810b440710941005c1e200e0001c8144807c4d0001141c24020401800072882145c110410280300407249203a10800c148a07a000107080e1401d40c0701c0046070034003060303d060540e686d004040d91044101b030080d400d4203040f030b19180c440301707a12480c04040140900440102c5408080b04044aa807514140b00044a0070711802c60103605000204241101c1c1070341107442c490580386958420f018150721020503c6c0e8030b039002c0c890050b020040074010442611007500900c00b01c0c409000101e515a80c03030f601111282c1c4254411244c0904280401c014404140112405000e01c1e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775750674 1250 775749424 775749467
    0x5122706070f030f0c0803090706020705031203270105070215010603020a0e0904290a05150d02010806030f011113080f122208010507030c080c0a0c060624 68
    0x50b4449038020b54003800c004080c003038100300c0180203d006034840c10f01c181e80150031644c0c80c80d116122680b51803480c45036401500c20410042158030f00401d0b80508088402c1c03410f03042d0769480d10025003800110740380305130280c0301080d8401d000310203000b050301c202c04030303001001040a21082c000c00034205a1081040600c180842001198880504400c402e0b0840d02040c050301e0301e0421120445039000d12980400240c2e01c0032241c00200842c0b13038420440ea90b01004141d50311051104242d420092296101000100ca4401503002d02c80300d0b50082c03000b40445e29000c1d8520911400c44641c950074055010300852140b041180b00001d51010b4030322100580201c08100d803203507644081820950070803090214500d41d4401c10310142d815076401d100e84180c980381d0303603c0c5440d0080400360713046000a4140800a15454007500030705002e60f2105c4d001c203240c10880c01080b10100b013913110459a4a4503114000380101496480214107114065801c1c10040741400c0500502b83c82a20b800c070038000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775751924 1250 775750674 775750687
    0x50f09010c080d09121b0318081906110403082a0d1d1206180a02100503010501031404020f060703023c010c0903080c032b0e0102120c0705122706 64
    0x200e41003425131613981f50074407100d03105d0007a03c003070406045900030070403038402e10307101d554100350000d40000c28034000c00d400c0209041040c0300322078030b1040e4000940304000800501500405045030340c0400216031030901400800d0481c81828a80600362070000200d2001d000b044040e00030008150100044031050b51240c107507282d440e1145002481102507a01d94009103508013000d100c401c00441e80204001310f001000440038105030030a0040c0c0e07002900d007600700b40d4040b180030744041c00340d45c00902c600e446003256000c015050f4005c2030110f08501070b1003101004040500380e030800c5070a241850040060302004500e1115252281c0c0c0c6185030304003842c602c2c000c0c0c5c0000a00d010340307800a00159a48080c0c5c0c06403031031840344140c1c844442c0c101800e803c0822000d4141007042c24803480c802c0c0041c55034500510700340d005182220644414540c045040f00f80c2247c000c2a00078070400650749405000400003505400409008650620350800200080c0d100c00d0046983c040032103075603003000d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775753174 1250 775751924 775751957
    0x32a0d0c08041e050f0a080307110d02060c030a11161a010f03081e03090106080f150a0504050c0603040f050706140a1107170109020301060801020307050f09010c080d0912 75
    0x2000c4020f03603030781c10343c0e140d010400c3c40f1080c0700c418080f005540454070400203500d03140c4203d0b4070803110040000c1d0048a036030000c3d00007040e0408142d03141d900620b001d40b11245910700f40e0348080c00460f822070742c54076082489012480a0084034545960942c903240c3e0908280007089200f2248807002d03613000300184488400c810b9108252500400312030f84400ca5040300181c40c401c14803100c51018004000c010180d00150019000e591502c802d5070000e0402d0b254107a5141c84084010846044032000600d4080081d844142e0190007a000c6442036240c0301e0210f443e0f030f442070720140c40c00c821160511080c008104215001031105190021030201d00707404090f220301615203424100442c4c929101e0b85d0400811000003c1c000b0070b104240500c0d03d01e91a64002d1411480490095003041000512814103100b528440e05446e200d0503c0c0040c86160006640e0000036201d040c41b0075a0703039010108074044081c06c203040e40b01c84001601c0006041520b190803d61601d08100b05411065074080c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775754424 1250 775753174 775753193
    0x5011103042310140709060f0e04051e0c03040c080606090402060c0a050732010e01120207060c081e24121207031e0c0206032a0d0c0804 60
    0x24849490300c561010106002500b0703c80a004160412820f108058030120207500416010356600e88408104541e106000d40d4600b42c04207010021480c5c81c0700c20b00c0d507820680c005940c0f040c0c44520744240e803600032541102c080c0d07040e1429600d11a0110800c8200035403445500050803100008250914000700000c10b56540104005c4c01090003107900703001d01104020b445084c9901c00c0075a0307242501c1340080e88014817201c6800d080b07111031607515801900c4c040c180d026084d4041c0d59520201460000640c1d4051035001c850b480242c0c200500c4002c01c03058883c070540900381f0790b01d102080c141401c0014107101c480300e41201c041032480910409200b00c00001c0441c04030b079010a041503510b800040c0110011014091141c01010710700041041400020801a882604c40321012814044902c10304180301d40c2c1c03c400b1507107079001c6c1d601514050700070351f034400300e4102c00b5030a400d4240d10081045032024034180e5014000b0408403031141c0c9a009101540583d8030b020b03840d40ca800d4464421030b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775755674 1250 775754424 775754453
    0x241707050d0e0a0b090d110705191e03030e010f0e042301140a060801030c030204020304140102071101090506130e0403050c0d0e0f100540030501110304 67
    0x1444030000394400c000049400540262001005030b41608410381011030b62500100c5000038540a00c20103962000d020303540105c880f840400091160724240020301805921131a841d88150b404000c0c0019040c86140580d100f4101c82440c60705110318615000d0300b042c0c0c3c0010580d041c0201280b61880d070507404a680d4182080c1103034080782c0c10051340d108490300c4034581c40d2503503c096203d0010032a081c0007440c040740c50200751002c1e00d81d035545080407100c1c0c2400380401022010b102c03804001601c3e0540155400c540540320030311240c41a006168226071204034101c07602c1503c461707143c00390b681000319035000b090251069403501000d988500110300150003100400c0138042c0100701418400c6003540c6030f0740c40780009c0750000901990054450314010341042e10580c410702c001100c90801e80d803000e08180341500c4850a000310921044a520200004240d010092240d1040041800a001051445503480d600c0c9603a055040003400d50f600d461000d550954200140300c00511062101d540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775756924 1250 775755674 775755677
    0x15152107030204150e0a080111120901020d051e07030501080a02040e0a0605010e040b090a0b0c0c010e03030129030903190507060f0b1c0503040909050304030c241707 73
    0x41035a4403142074009018a40280b4040c0040f148034102041d004405005c080348222032151009589000d05802c2c1c5014501c0c80e05240801d00c821890000907040c10754000003580d0004d07003094103c0c42407108480c01254048480803002190601c80c0b407841c80400c1e0054124901402a5810800c1e116542c00d02c108001340507640d60790540c1c403008030505c1032802c102d5010005000650b554140c05450b07080c183c07000c1d03810103ca940031840425000824150803688600a01240e036079010211072540c111030b00c03200ad19502ea0007440c45000d400d20096000c0d05030036039618003116160106407a409406141e11469003400c205004c402040041994050b464400510100c0700c205201280d090003640401007a281c203000905207242410b0304806000c02045d509411484070040c48145e4904028101401940007000306000d200100c0e0001818640540c08881ca850381d660785a45001c602503001d41050011103031000c400c0b0108540200c000480f42c58820807085030359141c1802d00001911000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775758174 1250 775756924 775756987
    0x305040b070c0f051002071203050106020d08090c2101060501030b030709110c0f0109020f0904020a1802090d26031b03060406031b050307090603050319030b06031515 73
    0x90030030072039812183d07240d40e111080c4c6100d86140803c510207908450300444440700799110721401c1611a124103812500954024540302c00c409006807040b18000d06854460700400103504155200c2c40103a0001191224800c80403040e500b41d00d900719015908200e040609000510400c1d039400a2040282c2c1e002201c001001c00601c01c0019652050081501f0113002e031403015480d4060651081240764000c1e2000503140c0c000c00704100003170008640c002d52003003022005220040d0007414600c1c00710003207040149040d031182c000540c040988407013100c0c1581070354061030040c5482132030503030300400c17001545007141401400900b800c2c00a441c1c51010f550044000384103940c40d0b400c180003e60301710720b00316003140c208040c2d440b40724000d02480e0b00070311074110700080a00643c46004204d80c0c204001e1800e0166101ea0342d00744401680320001003546610328400242d031580c0007540944010b182107880441c02109002e020300c0a4105400c15241c24403141c81104088842c401d8070061074140314 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775759424 1250 775758174 775758197
    0x91801061211090f0903030423073201020a11031204030b0f15031509121606050106080609040f020d050f0f071505090618030321070305040b07 63
    0x5401014903620005550009102034424040500d00b00c0e2190581660724103690307038910652200112069890184c198410000200480c0940b0001400500b002c0001d0741c0000c10066520f2a10707141c0d030801c00c0c0e06000f05420761456240c1b9a0b007401d400f2401d00350f00d801c0c0c024443c000303174903442000c201500151050301c3e900340710791701030055100d02e60701c1c0c69081d40c03100d4130790400c0719030701404682d620102ea4440000c10000b03004920380c02d00f43c50008004281c0c400b09004440070b9a00d02815080182c400c260794400518011005411704000e43d0380446514010f5003441b0003130740c41c1a4005401e01401d0810300255840e100d0307080d5400768010305c410b00340341302910201d08501c0c10640301408902600705e01944c4050003040100e01c80004500700c0700429291303016a0410101d8800c0c09010403400c00c00c0ca020b078240754020741030001c103606443d520a044c1e1000b290442c2d20200544000b401c001c44ca100d01504090011600681c0700e00d01009145003a50710140c43d2440900728106100746941c10703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775760674 1250 775759424 775759471
    0x7030c05010603020405162c1909050408131e05061b0d26090d080c040801060927230309030f1606110c0405060109090203100512070509 60
    0x2100960340038104004031f180c02e1450591800d9000140000100240800e44030341e0303402007580d14000155000c20200843d10800c0000020359900c102070040c1c3d0350702d0000b900002c3c0c2d1081c80d102e00e001d5203415a0780c01d0050491444410a034005c05d444608400003410010103401c500c0c0107460050361016a50b0000c0340311442c0700c1014915002c014824180c0301d2100c503900030114a185290f00c00710074802101d401d01c40c0034150003240d0600140d4080c0c60316000451146010b40d0300400052426854240c6400c001401c1d80c0840c0c0201c00c0187e1504e00d071641600c581c0c240c2000761a4110448003070200980c1d030301d9469200d0342000850300345034460700c900190010700460f019144010211481c09242c4010300c2d0311003001c01c041d844454002c40d40001e44600a20400d44a40503c03000350007848000400c0000514010f800d8a04000c5035000208035403240703100660007110786040481003585014200a00d40c8030a03150101e69800c40d6000700300c1520f849080c10381088240d1090039079000364155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775761924 1250 775760674 775760681
    0x31203090f06090204150b030a02090a030f0b1b0412060b03030f0408150901090b0403080915010306140a0b01020d0e040b0402030f01030b060603040b06010507140714042007030c0501 80
    0x350201141840d60700800c01c06a0003010014820ba07018489042c035050002c120603454456100410f000704005168128154010550044002d001900700351f00d0f84c50316007001d128100c00b1280d0181801c2441018100303114550030b51041d8a6546103002d041a040d0142000c1103040103140a88420200903141ea041c000d4602c1c140100c0f800586440e40c500c40310343e83c2c03141d090303440407280d02400201e0858981802002a0650080c1b4428a151603030341d012100480c0083c008202c50051880c008207644c80030440900850045002041c040c80d1410484490203001d440f0b070484a14100186e0040d0341c011604078014a01c50070503c05200075240480c02400c0c1055946074014070010401c00c900d191000003605980c000c0c0382105059803004c0c244401e070700c002da03405031010203410b00044e01984130b4401042424450791501d0040310000341c202d4a04a0171b60072400342400c0c200d01130f0310b50381098403583d130a894414400c51503040340101d054a842c4114103000c2c0801162286880c1130000035003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775763174 1250 775761924 775761941
    0x3050403120218090105030114010b0d090f12031508071503060b0a08070f050c070b0901021911120109080a0c080c0316110315160c0506010311090903040b0301031203 73
    0x5001d41d681c0c1c20f0403050003107900381c07100424070a0407900008225800d05100340d1509204103441c8904690038450f1200d041d40081983c80c242c00d844420300d800050256260020305440380d4900900e6000240e40030f415038910285001c92121400020084143d000411600f2186042d01803088920240000c0b4003030441c3d0303000300040d1040043c1e407a0380d040c0d000a409110348010340d50105140c05031101101c85119041c10002107500c440d0003440810095030003401c82c2c6405004a43c200a1142c804490007011044142c44803004001921640c1c01e08003102c41c1000240d8000300101001d40c1c2d1131038400d004164070382d4104140e00380d000c4204030407801102e11a030490801c82e81c45003484a071010301d044001c0c1044908080036010b12803241070000f60140e8182000c040402c603035603400c40c515034403041d0051503800c010300326401c94042130043c030400d800b071400307002008501954681800001040608441e42070360080000b0891900840c095030f064a9002d00c0031050780c3c070340c02c104801038401d04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775764424 1250 775763174 775763207
    0xa030b06220602030f09060306040b131b03180b06010905031605040b04020406050d0c0519051b0c09040f0602040f080616020c220e0d020d0201180f0303050403 70
    0x91a50482507115070a119190311244141020035114041280c5a0061445444d8821070034010764100345015006542c0c4014098400030f014026000080c084140384549506001d079529148881c0b8030150119220198540c102403160382920105a5014210790300d024000c504601d010600c1070b0300c691804001000011b04407840509444032100307102080384229071140d440c00100c40f290342400d00a480489180c0d85401d400c011446600c04054481929400d0400004007c1c1070080851100c80c1c04100d1010b0b0340c2d0340d0702d0350510381c0004d0084032540c0742071649600c02c05103004940d4030704490704e078000d83c0204d86001c80c80162400201a000b0380d0000341000c0311549010030071110005001c0d01c80c146c14111150f4100341650181d8035a9802c90280e9002843e441403604000c000441d03a011407220003600003902da0001c17070f0356030034a81000345010058100605040c2155824080c54a220000941d1501040e849555039184500782c0c1000038107140d12400001c06046c000c0704540c1582440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775765674 1250 775764424 775764427
    0x306080714040e0a140d232502150901021515010c1505070e0306100605043f031107080d2006040302060106180b030103062004090515011e050a030b06 66
    0x100d8170a9290220b5044440c0029410740c20b1240c4c1035050401091000108514240761012842e05030b607000d004030741d89144c0064070244180050721a6120340c0304e040700c031646050301d43c55000002030600725078409110906002c5414480250303c0c0e86c540101051302400d02e42180d5400e440c101c121001d207085941c100a1501c000c2060311500452004046041201a103001c2d035134034103108445007010300620000503400c1c0424811080101c02c013000104d20b1f620b84e0060050405c0031300c1d11506406107121200d60a18034070b40b0401d60840940d0602c0040c0d000500110b5090000003035442201522100401000114140040191002144544400700e050320b50350300c1c0070306003e940c0324020710407003001400d620726110325098500e03018000d5441d084c0c14503117181d281d5211078001c0d21018a078a41840c3d600c800ba9480240c002c00180003d00c0075840100305850700266207040005a000f001d418020081a039a540c2501c2d10f001800844c4941000307510b42600d0b181c01c4005003030204540d40c00a20 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775766924 1250 775765674 775765703
    0x140415030c090203160f120b060f030a0c02010b0303040e130c05030a03020c0f0406060912080c0d020a05010b0103090203030a14040902040b030a0e0a0819120218010306080714040e0a 80
    0x8183e0025445001040750425901c0002c460803036440d0ba2001c040e41c000385101c450740c003038048640c0081c14402d000510560074001001104071481e0f0040e10400d03000c4c5d40d41c08042008d280c0a008040700d621080303000c0d6042614000303c0a0580c10000d1282c1502d0203595850030811820002c0c400c064013000d412162041d40750302c0c0203582d0307450808150744a0038050160300d1300d5240502a80098038400e5454000892400b0a0701070109902001101c2a840500c400180903204100400314240c055005040302c140601f000c03804c45500d00340b15810103043c681e0401c0940c400104031540b04400b4a4007031415070441e0002d40365800740380c215180035400040c1c00604080b42c00c000d54010741e4000002c11950681040c2981e461242d1400246811000d0005400140441280045628003410510482c1000c050440d00300d900815849072230100b44c00041c0c1155a1511583c0d0103814000000c0c20b540382061b960314501c1e074182001ca449541c80d41603030382c0d000c60240f2282c144581d110940400b00d25 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775768174 1250 775766924 775766939
    0x11211010516200a05130209060705030a022112070806030f0316030e0603071704031e05070317090601090c0e030a0305072006181804052104140415030c 67
    0x420400d0b41d85040e48119901c50003600d8280204c01c11680004c2c200480364003001d404501079045004080e81c00141400074030041070b404e00040c032000c2a4ad90250108801c0380c060b02540b403002c0e400d032601120007803202824080d0718001190300801d10b41013032a0740740d5444001a1809620310000d1040b40000710310a030190310300d1140288c00510a880c3d0b0040526400240285400201c4210700042c2540403500d94607100020000d808c54060300d8900040079402c4110151040610292000180c0c00200c1c0014154410360003528151003052104040c180451510f694002c10b016851b00280d46007404e0300d4944c054083d00210710005415148404402d040c090300d1600400360035581e0155500311105808114060b0104907079004041905044c2604080b1074880180400b05800c00150a01029a400140c032111711481c8203000602d10080c0481c00200c1500c030801d1141003c85080c0070611106001807040e00700414192000a940302040c4004c100b0100349a00c05001c0d108041404240c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775769424 1250 775768174 775768193
    0x2a0302010608250302060306060706020c10050901050f01150210060f0f060c0803013605150a050a120611040902180d030c0605090304170f0d0206011211010516 70
    0x540c0e2007003e458420320030401c00c44184281d1800e002c100b00040c1c0f82480189002d002460300418017524031428010a82e0742c42049a01c0748100781226806410032070204840c60082c1580003030301c88002c0c00a4100700c0307114800418180038541d10801205a40740089108000e10244840010401d012103990f5895480551443c0d019005408001c4240402c400780215150240280e10a40c0c1ca851a844c00400d85400c19002044913601204508029500031403078103070103408000300e880001c5605008444455100c1c8914405000d010307884803c201541d6902c0d2000120784000800c203071105036605e0450300600c030461141c1d901c044041000301c2c8001440c1d025060706d12200002043d03800c0b010080107804030000704d0040020b030754564200002041d80c0c200582050728a401c590503e030301c3d0070320804000e020215080c1c1e190321107070b000020f002041100740d02000c0507001604071541404140c50703c0f03a16040c0013400300c80801d43c0b200c0b4540d01c03540840325104040d5000c0524048503140c00c0c03406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775770674 1250 775769424 775769429
    0x11160209091f020a1412070305090106080307030e2803060c03151e081b0901150203160c030b10080615130c0c0b0f1909030f2a03020106 60
    0x50040318005101c4040000c1c82800d650340c0c00e41c1e81a5111101c01000c0041c0d444808000e0400c22800301c034003c1c0701e40b14005040c166840c1801d4003014070f001400141150401407100f01d80340e0410004000f0b040001c400c41d8410740d090314055110854000c0400d440c070140404a1000c03403440303510315070a01a000c0ca00e40960b4860042070100e104030203011405d48481070141e185040c0d404030100001951040000e2200354441000041c40e651a0409420702007054940c8084080d15041003a061a00c0c504050240004d09146590401c0d40c1200958078000c2040352002c0c42c2262031600184812024002c0c021a8054800a1203150203005100c0700c9003544241c02071072203408045181c00e01c0e00c405454213081c001d00346540e4003004c4042e07000030340707145880001480181c00d103550110b0421400e45128040c5103a1803806405e09040ba85480d03004a01c003181c0840c038001030f51000a900c842400b21842051501c10705582d10100800380c18242c01ea02e041c150309012416208140d01900003504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775771924 1250 775770674 775770679
    0x30b0109140f070816021c09080c0924060706050a2a020a0201050a090e13020a12151d15012102150c0c0a03050606151c090204111602 59
    0x495840e42101c1d0041240c054440501207415a40000d842040205c404040401680304a9400f50110401c49891a8056401800081c012001031008590030010200c207404103542c1e080a80c0f034a400100b12410212819248000709011a00c0480c0e4461056480307454210380c04001c42e003405010340b001807940210341e02c0c20080000c159903100301e0011403040c1c0c039503140d000381039031840325401150a0351001a440c4248140801702044c90a4610100351040041d10821118101c0600410100baa095805942000810440400025203e1000f000f00130f407111404514400001c600c40075100d031004000f0190b10422008142892448290504840e000300d43c942c0d0500c20b80c1542202c1200c6a88060f411105480840c1a0b030460030b40201b5207864120241d90500548000140001085500541d00ca0303014030b0500104d071604001c04441c030071b075440c43c641c1b909414105040010f0134003d074200c000da41c0c9400c0c1c0030640d145c507007084d4102e003401d0301c0c9140e48030780e0040c41010b1070280b60350036030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775773174 1250 775771924 775771961
    0x1104120312061d0601020120281b030e06160218060d020906190f0906270b030a060501080f0c040236090109020d05060307030201140a09030b0109 64
    0x8542080510882094484860308118406040c2003820b42d4240e004d804181159030b00e03c1030400c401440f040941c6441c40040a659541c4802543c0d000000758084030b02a5080a91120b81c181c00c3d0000640d0300c0e0200c281d80c05824020003800c0680e08510040583d6410040000d0840300c80074541082c0c140a0380308607070801454101c3e0402140da2003088482c550401c0c0c3d019204000351401d00002136100c08000e240c030389002c070400d000caa400240d66000c0300c030144401e80c0034018100035000c0c41d80a032088014100000010305d08002000c04820500b40b41690380e0300b1a151562402c0c4064407406030070860510031540d6400c11650345500080b0b90164500079041c44210074500380c000c45d000c414a43c8090141e8107000c614040c1992050301c201921003121000080d01501c4402e82c0900a0461040050320b840c406400d82c41990360042070b2512a4010b03642c2800182e0304160a12645a2205071940c0c5a014a0301c0998650765980c102508010202000242d0400307aa0003020403811080e03401d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775774424 1250 775773174 775773197
    0x60609050102011a060d090804120f02010f0c0503030105460e010b1e040909060c030c0e030706030203130c0810060e010e04202707020a0803010b03060411041203 71
    0xc014015400b88085d5002204018008045000d03400440c040c0b401500d0481c60242d6a85c0c0065403040c07000c8040b540b1003445000c0c4810366070012246030f05000355040ca41040711060b5244c8e6124801405854401c5100050801c4034200134580040c1840e11500d403410399181200c00c00b80c803c02d086440c000100030f40c9201140095403048041d04a640d540705e118245aa6182100940e02451551500511090000180e1f0790000e02070703115802e0181c540060003108560005003510f8400c086c580c113120220541544035280011104200c81052400607213030740b10f541d00c0e02d81281c1d007840e015002d101c585802080040380401e4000b1b4246000800300040d03030b40c03000000e18000b024882d41916894440c0000d000c03440c0e00420207503200b952189034804541c0c50000a4012540c521000c2c080401c0441c0401c10407245580d00340c009a05000030709260210f580c0d901d00a1005025407046603201101084980c0c466030000d0142030b00c2c0010007a160350311550f4000c0ca9400b482c0c000d6001074942c4811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775775674 1250 775774424 775774451
    0x33041a07020706080c0d02190e1806010f080601031b1d010e0a0303050a0203041205030901080109020f04170f150a0c0914040c0c0b07050a1101151a0c0106060905010201 74
    0x115070440f0b00940700c0d41c100303541e40c000c2c603000c030340042c114107050079002c0003801104400c0c1c2c60303c0200350102d501d44070110b400d00024018410060307a482c1d03900c85804402d00180d1380c0c11036442c8900c0812440e241280b03940b500c0040300900200c8008100364140d08003800040d9822415802c0c1000d2101e41d07060603140c1c0c0b6001140c041e0411000c2c16044180c0300020b00100e449080109141c503030900459140a950300d00400c10203080440076905a04042400d082c03641e40031001da0f0041c00030707100660600c4907120290640d0300c26442100c12240d0050320b8030101010a12100100c00e26000955141c0c0c404800c6540c09001c0407941031052900e4203074001d500a000e030440200b0781e14140c010350b4541c50448140b10090040742513a405000c541000640001c600a0000d80703d054255100f549801400078041c1c10104504112580b0340d040070340c4c082e1901c200c5441d0760308580e05109200707103429126840701003d100360003541d40c240d42400000311310300742c1200c585012039a0a900030000c03500340055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775776924 1250 775775674 775775683
    0x10909140d0c0312060806011202032119030b190617070816121e0b0411160212070303020106050a0e33040f23010833041a0702 56
    0x40c6800820400d0b8078541c00300340300d01c4e20b4150000c110751001440c284c640140501c6c11f00c090f401a0301c50304030340d0700c2c80d0110b040600c050003900d0740541845002d1000015030001c0f07070194040038406000c0400c510800e880c4070340c2180c80c1510014194031341142d080c5100107113614140c041d10700410098070104945000c4102501e100310b12aa403500040d480c1d43d241c1c4401030003400961402c02c50794502611161002e4842c140349011003620b50640b10b00f008a03ca02650421008281304a103401f90103503100034080c00710307400d07038008658048100a480c03000407440c2114140000d401d1141103808400c0540551100054603412034042180c41c0d6910b848020303280c801c07254810b40141090000c6042003068a8202600c40000d50752410b403d04000400e041310900d180d40003d95845a071607120000720300800e0603002d6101059000c056041c01040c99907501c0c80c12900030203c8100b08052501c0080d84070b0034001910745101401d5900301401c0218180e005000d0103010b140600d008036204a00010707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775778174 1250 775776924 775776943
    0x3021e180115020d020d0c030e03031918030206071106040e0f01180908091e180a0516080f040602040b0f120601030b0f06070c0b0f0d1a090103110d0b01090914 70
    0xa001b04071044005208651080301c1e60801c800f400805181d87c80a07a030188085d040744581c407031115140503c41c000050083c19031110300c14150030040030a10150310341e001142d201c0ca401001c0502400c0b01c50000c01c40070b00c1981d00800d02c500060313040c0b0203000c0003140c4460407107a9007203c1954103000ea28900c4200c40c13510000500c24034080040700d0300c078104202e00340c42c2c410700314100c0c0c900d080c5164082885141400c3d441401e140d04e800401c00c041820f48145030b04007000f00340490144003440c0010b804c184025206030b01e01c00300840000d041007100d8049138040d00503242030071b882d40308690400100d6000543da102290558000140340f1b94030a1003080040f00e40148404005d011043c180b02c40e5901181c3d050f03542005124000c9400b8208200510540801201c00c60b961303402e00890b01d046481c9072203500381c0040c810100c00407a5440541480c1035941003c514a400410100080e01040c0c100c00014441c021300e83c00000c00403180c1c0e02c0704940310300580204080e94200c080003501d803000302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775779424 1250 775778174 775778177
    0xc082b02030301050604092a03020703081b0a08250915080c030604021810230a08010b03130210180b0708030103110d17070c14030703021e180115020d 66
    0x2400200030000094000c601001e1203440100e480a0000000c0301000450440020100e500091054100343d4811075a0743d0154040c13b041c40403400a03800a0302a1040011107010081c2c008081500700101a10b14198104100e40130800b45001400c0604450182d00c81d400c0802c0e21405865022030240129a01c01c0144c1e801c42465950b07031404020080d0840121001014008812041c054441c20200003141c817280d01c800750503402d00050a030003000e4040b40b410300c2c00014070034412030300d81240310755055600c0b01180a4a1342d03546458258152070041010303502034103425140d03804513004103d040c1c050b40c9448541403565240d581d81d05a510900e440100482c2040004001040e440d804c509001c0300020034480020b803203911a002d110000c03050301d08006100082c075004019460803918001c0c000f03020a041009906000030f034640700c0921000e40210586030f88034010840b2450462043c080043c140c1c02042e008104150a180c000d01981c40741c613420000c070100c0580006a40c1140700c14a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775780674 1250 775779424 775779427
    0xc0303051f0b0c0705060c011a031207020d02010e0d03030501090605030d0c0b0601030612050f28020111101d011103010308040603020c0c2d09011805040c082b020303010506 76
    0xd100c20380b0180d51090902d440140102e13100403420307079120307002001044240d4002084400040b41c40b40c801400c807800d0f60344203034001d0300109240c0d1542e0083c1d0b010250112410320400015000684070305a20b48111035002d640e41d10074004040d0154040e038103030b406840007000034513255070030303d0303030710a10700d105e40010880004064000841e101503079a84500c06160200b401603403042215123181100030116417680028038503168454080000017a02c02d03010030070b07800c1d900c40ba0005204440d048040a0b041100c5505e0050a2201c00c100c0100300009214040000c030741d00d0309200300141c00e8154610318035401c020b0b814800802150a49050b280c206400c0e0f480c1900d4818158000c0d88003040c3e0802500407800d0aa0b01542c6d40084d40e003480c60100c5504001c403d101581c201084200b44400e80f049403210014400800790b40c50f64501d43c2c600d12400140c4d0313115401c2415809506070b0001c806c074440c5401d0141003e0b11048820056416072260b07240d07005000c01d0680c0c4a00003401a140c00050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775781924 1250 775780674 775780679
    0x7020111090d110406030602070506011a0403020a0612090b1501020f0111030708280606080609010602030318011b02031b07080a021309061109120a020d02121501060c0303051f 77
    0x4050704000c82d030f20380040001910035a42da64110603038009403400c5c1d40351f03040035004001d82800b0641e041c2210416000d40780c0761505603400906a10103500480040060604d00c07a400100b0650009101e0750b001043e01c401c2d841d040384600e101e2101ea013890350050007074030368040d401d000500910061031207032104a42140e540c54412128040014000d0388240c9820304244000d0610554560b00c08104a00104026040a80c0a0180d5001500050013145d607000108059980442582e4001d0f280898015a581c0a010300300c1c050004841900c00d502d0210050428550b0000000d02d80c06031032501307281d10400e8250742c10391180200d110b000101d4000d195030500500e048441040fa411444c100001c1d00d01d82516800e0407181d01c8124824030003000240c0403440d00d064120000c00201d440010128048c0d5640810510340e50008000c1c05200007100300d58458a00740110000c0c448100702485503580c0d10000200b6195850b042900484c0c94000403a0101382e04050303600001d070380c0e00544114180b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775783174 1250 775781924 775781933
    0x5060105090403090e0c0d0b0d0f0620120604150303020703150e060f0403020c190b1602030f0c04060e040f1209080703060605120312160314040b07020111090d 70
    0xc0c000d000310104009890003141d5918445c08281c003648040c4540c9499001c2c4040180c00c50314014603161041f035002c111400050013090040842c03a600803001b140007011410a203030507241101448000c400003040c3c911040000307020079403041d07000f260188441090100e204042d42418000900160890001400403503c4000b2418484407603107000640d0740800b0707030300b2410f1001c1691078030084c0e6500f100740014581d04002c2d5131042e0204a40c40074040404802000005595100e649802500840d1801225a270300080c40f10042d009400c1e02d00b0041d01c0b042c015110310721f400300c15101da80741210209001e029201c2542c8910303401000d03404140d410303031941c0d051030080c0b4003501c00308504954040f5600c00280f001d1001180302d4040801c206080104100c0000701c15070a412442d40305203e140b2200c5922003400350441102c0c0409441c1804804045000c2d10001d0382a0305e004d00070400f80001c202c4461030540c405c075000d50003041500102800240e06200302d440d42e50380000004043e40128 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775784424 1250 775783174 775783189
    0x180303161209050d0e010203191103040302030d090306050112020109140409020301180302061f1214060408040e090a050606040c0318050718021e092205010f09050405060105 76
    0x581081c07101414803803118000e40d0303010141220180c00212024280c2c60304034080382c1d5840d9003400614148100001e024408030441c46810041021825483d240400c0a00032203010b16005025a8102c40304018060320a18182c402103842c1c0c0d10300400050042500c41070f802110340d0503507500182d146000710381c100304180c0c582802c1e03200750b640e921032006079803d114070b40c60a2881c0d40755181c1c000d135608002e030801c400108010110000040d14507030b20500030704c5800c2900d00705180f41500d035216040400e14503003500894191031041034140804d0281c0c2c48058000c440001154940c9035881082c401d4440342d0b11a002411580700c9000310703545182981042c12025918130b0b000038038400c108561400c12000c02c0e415a403a4006400510110301e080040984540d012603040d0301d446280180283c02c00041499141c1d21440480c807074a56907100f4110345407946e808603800151007000784164004100a01c240f5460246605000030019201c1c0907240c400c2e600000580156071800f03080c00801e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775785674 1250 775784424 775784461
    0x801050108041112010b040f14041b0f0b040f1e05041d07121e03020309010c0812150f040b0108010302040e150c03040b011d16050903150906180303 65
    0x2c403007891140c16129200d08a0b041d1131024182c0000c90460001c0f010f000c112407a40201a066505048600e0540d481c6405100e07007040c0e1040481a400c44110003118040380c46401820842144c00030010302c04c10b05d0005481074030181202610900d40e00c507a500a404000c10715100500f551140c1004140360590100d10340c80020241c0f60303403000c0c140410030f0130040e081d04001d217400d90b04110503080c481505c5050644121404549a58100544002e556401004920b90411450301100701c1000100d100303170b5500407840c0c800d24140d41001031510345400c11700081180243c61f02c000a800c2450240200c504508040e111b01c509a4210740030300c005016a04100040d601c01c2d602c81466030494101c52030700c40c804910b0015100d080c94500042d06100c1a03010605101110004a616041e015140c98010707056143e110051062100706442c0e5002d0171b602c59600d1b0003040002004901540000c600c80d143c0c51040d00c0d0981c4d6503501d20300c42c010984a01d43e1b00e96000703100081000c902222503048 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775786924 1250 775785674 775785683
    0x1140d030201060506070b10051002061501020307020406180510060f0e030705060f070507080a0206030c0c16060c03090504050c0406140f040315050a0507050a03180506010b12090a03080105010804 86
    0x111144c81c2c0000c07170403650100c5412501c840f85c442c10440d07002d030285952005880f0440d0020a02d1440c94402075076031801402184181c00b0500f40e041a6030300800c12604516400790092000c00d94681d800072051070500989214242070400113619482d82d1915401503d8007a120001080c0f009201141d2200c48406000d80601c40c449022446550781c002410342003050b00c60f4203aa40c411442e1850501c0c4c0a0390040c0c8842c0c6c071600000b80142d99600681c3d40c0042c000511544034040028098602414415041021141b410011a0f00d075800391941d80814002c5c4c03a200000d80d03071841440f0880c3e4040711441c80c0c00c4818002132100310301c50300b10506c0a03284004280d0501644119000096001340c1c41101c03050100d805400d0348080e0340c041d05901400e140740c03c004a00d07100034082c05502c2004021410141c0e10100011000000300041d024650841c085415560715412413200540c07040c900202d0b40d44000e0001041c01c00f00207801c0c0d103110b034560744640e92a460300c1c00540c0e1548000d442141c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775788174 1250 775786924 775786931
    0x180b030f071802070b0c0310080106080706050d0b0904050c0f010801150f090b13091103071e030f1802012d050d2a0f0518101404062601140d030201 65
    0x5001ca0304414001c6d00a01910401036504e0034201d0514000407016441a407060f4102041004503c0d000b00b64801100c540b41082c50b9034007a94a0148000d28403d88126800302c406000e00040c07100000f0aa107e5200035101e8040c003004103001504c600303200b4401c1162000d1400c80303582c021481742d180c0b1403640c6246c1c180018240e444001e5000c66400c024040c0403844822101001007114030300584200040d0f1003002c034514241900700034500f00c0206002d41c1e030900d00041441400d442540700d00c1c0d40e604c00500400005c0c01031941c10003032080100041e07001526110b01d55a45004482e24a00600503030b802d00f5002c481c400a06a41582011228083c3c0503601c41c007982010700b011081c95130f11780b40804040001605484003801440202042000700803040c0401c0700c810b5410070749002e2019013140c0805034414a00412101001c940031042c40d000c0001c10005421500814688503210501030890300340741d0704580c110b01480c0d007445503030041c0740c40c030201c201541001d40c0c041440782c1c0a4800030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775789424 1250 775788174 775788187
    0x91b0d0c0c02030a1a0705160f38010506040e0a05060f0603040501200a0e040207050703140a1a040b152817070b0307050a18180b030f071802 62
    0x21307044c21601c03182601d00711191010410411010585581d01c801700782003650400705034081046491503412001840c1200c80d140120600c0f800380b0806500510a41d50002008003200501881c036104402000503580751100200315442c0280c10741c0c050f554100c4861419907203403091200604405040513800c0000c00092000b41d4039000c00541c402c81c06a000403440601d85803121240030485c1c07011a9000b4828800c5444072580810100300079030b41103070056103074100741c10020b007000741036840207083c00c0901e442d180400d0804220394034840c0c05190840e145202c2c00c200b003400113804442c01410500d007a40000ca0b8030317000c00c4240071103130320140004000c038009102e000b51034001014101d40f0605034070300c10080c0308118440801e04644c070501401443c0e1905011101a010103844d034010700001007455080c5510800071021103040020342c1d2006156949410041560949400400c16040402c000c0d40e42c01c00203840710701c0080340310003040410700d00303000360703c011802d02c0a01c00083e8080085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775790674 1250 775789424 775789429
    0x702030102031e0604090209270a0501060303080a0903050706091401090819020f10050c13060e09070e0d080c0f070f081606020c040209010e0301050411091b0d0c0c02 73
    0x756215240404401d00c43c04034001c2d19a0780b84070014212803007a824410180010385600300c0300303a00100c2011080b41c0c0c1105851520000703690f0307113008401174440e80c04903034144038054121000f164065260860903032130741600c02c402d607174000d08040d011500c200944030005009902050100340100c489020800e030a01146003074a01404055070442c10110385100c0b2360020030810300c80c0c040c3d14001400000d500355041911108003980c0b003001e69030780c0c0002404002c025412200c10103641d0380d0b40d90f003a80d21420090b01001018000d40d000c2c0440000040900d402121616120350008099042864081d40d900242e940490a541d0031402007040c010b0182c5420050070015188800c0051480c0d803c1c101d407a8501400302591110516211008011127034001c5a4550700902c00d8401580d610744003801610b02d88a1050469050342c600400c210074007200c0300140460802c100c404101e1510342d6901080100103e04e40c0000b0090100184e416101b1594019014652075081c88108007802d03400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775791924 1250 775790674 775790677
    0xe010905090a0515010318020f0d0203060702010609050c030c181527010216060e010207151106150102101805060c0a080c03070c020d1b1526040f06020702030102 71
    0x10307100541c43d140c07030910070400030350780c1e10300c07514030303081c40d041003000c0300e20b00c52080488995502038083c644c0180c0101480d16803082036418140c0143c1100d0444c206401d000f8024003a61144000340f40c41c001c04980d28401d0001182c3c0203807444140c40381841881b0003000900d0041010b1142e001014103048040703218882c0240100f900b4813154203400c1070100840009044410003c80c1c11900000b5183d801200d908107008180d8400f881c0100741410b41c01e0044c0c0c40c1020b50380100345121041401c11200d268054102480301c031190f020b0b5003068860003034a409031400c5004003400350b0004010085040030742e0340702441e0801201c08403044001d407500d9150a044059900f1081c1c031074001513080b01c086d08a21480e410a8251041514500d0190001010200c2000c4000c0c41490551081c8052280c00300145e821418052f080e081c1c0d4542e00c1c3c150914502c030a11084d000b060b000d03481e06070001d03602882400c5203480b01c24070724101c0d9511340da0720082c40d07800803048840e981e0a020b5100503840920 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775793174 1250 775791924 775791931
    0x60405280605040f0e04031b031110021b0c0603181c0305040c0f08060109050c070c060e330c190c030213051302060a02010204030209090304030212120a0e01090509 72
    0x2c5030140d80b507042c010500002c2e54150041200180034205100000307070301509a0740010b110710070041141c0340e5031604071039100c00850381444d00c0c842c2134a4800d20760a42c0e40100880c1003028905500301d0002010b80d40c41d000501c0c041d0340d01100078000a8802c03030711070b40c08a0f125101d50b0305840300304c070281c0d68244641d0a8514402d0001e60f03180c040004021160050300042c00c0c00d00f80b880225454660301c103940303450501519010a0701c40021500c0d84000308180c4025651251034542035a4440740010300d488209140c05209111810540c0c06245600b84030480b846080c00924080c5110442c014459a004401c10880b61003003840c2551400f0042a465081d0340c810007044121030300e180100040c8460410f01c1c01c01c0c840c44c15050040703918902181d01111a81a02e1349901d0303030400c00381a4024080c9a0010750011095020808203500200041080d00d04c2242e0518002000300d013a2645c54401c1904009111001c114541442c7d006d505881c5101b40145004903c0d1350716900490200141a07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775794424 1250 775793174 775793177
    0xa0b100e0109020408070b07050c06071106070b0403020709090c030b040f02060703020601060801060f0e090606091915020109020a12050304090f0519022a03040f0e091b0604052806 79
    0x114090181240c18046c507030007080c0300c1c410316041428507111345c0d44811005001a220b075200042c01020840201c1c003604120a009218940b03480c1719090060203104111400c800602442e4408070710a00310f48035460380c0a41101483e5000350440c0e41d1019451000380060340c412140804090050340c814008013445c81c4250701425085d407428401507c0d0300410380100d0240802c040300c45100d140e102c40c840d441020b00319840605600c82001281c01c4c0c0c40b82402807900081000041c5202d00400c0c180003040f101c2821485d0440c90703003420201d080b80c286030b0009510250012003041101030040000d44440c1c01641a28034103030362031188104403408860002640d90312002088051020761b21076600c0c1009603a0158902010110042e891030800ea00781c040144101070b03c103040c40c00c20026980640090150009042c0e10341b03c2c029040c4c00101c8074030a040c443c1e204100c048000b0a412100d10391000f030000341c2400c0c2803c0400086030319060311580e45000b0441440c14800b4448140360043c24503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775795674 1250 775794424 775794427
    0x705011107050d08010503030a050307050a140f0717030c03040f03110a0f110a0b0901030e1002162105031618150f020c03210d020a1d01030504050a0b100e010902 71
    0xc0d40000307080d13148141d10003403094205201c020702298011045135808501d5241c1540c0d2841c40900580f00c0c65010701a1440c549030110f0015594103001c8014a150307402201e000d41c40360901d0395400c0062004841c2000301c0f200500100700018007000c2d81181051080c14000981d64140302da0900e041903140c02a50000b060000e40710a0054490388501c803404266030741030395141031401c84040c2c2d10601590318105a91103e80400050781400440303440301c6850801c0d55510080c850244215403030000565595100c2030301d414010803807030408440d4a0a03030311074a08640e6115488004500c00b840c41805210a004203200e0042c20904600c0c09006a00e107020341c90030011100a00055040050605641c031100300d2042d140d60010392184d520001d00e4104008000311402040a030040d015415840d5002003075926090360800d00450307100b5518500140c410624800450543e81e05860280030b54015128100204031501142c0398030094606104e54026a550343e02c0513042e009a0021180310350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775796924 1250 775795674 775795693
    0x12081e0f0609070c0203060f130203060c040f0506130303032a0206010611010b010e06091503090a02040c0c030806090a020408190203100506221418060901050c0906070501110705 78
    0x20710602e0260058038030f00e01544082d1096011959864010342820920400b44c0c1c0041e011000c0e0600c0c2541da1076000e01500c60741c1c284030311440020741240c0104c1180f441d6050b400706175400d007d026590104403002030380c80a0340c910384003500100200385a00a42c0c48040ca51242c03540403400c80c4e41404545a0b000b00040d602d808802448a01c0c00c0b03400c0f4005034102001041c0981e803010791403003131000488249648121210019103070180001109140640100070030180351000f041080600340252014009001c03190001c030760a010540300100401d0340d280100b14607017440002603600424070500180b6050f11454560700e0081c004803002105868502c4a8045090510100704890103511307040c0240d0900000241140500500c10241c0c16010220703012281d0603900500c071003283c035026910321818480e014940042d00040b84044502c1038001240a401051045900c10000500030f0760405500d40c0c20812241c1c0804401c0e0340300d40d00d41900c1d005d8a15104001d048042c0320ba80249803444 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775798174 1250 775796924 775796929
    0x9060d110d1409070308030c16050d020609160b1b0601080d110a0c061202160b040b0f0f070f02031c1b030905100926040f050402040312081e0f06 64
    0x7030440c44182c1c08000041c060105450000514106895003e2031864807584d81300446540d42c01440f0460060302c0e0600e554209101d004210810111803a50960324181d491600950343c0b000c2240000c0442c20b9000000c100210800e0042c0045010042c0c1c000c802c0800b07a000c5a19103003003a0000012508511007008005801c080011100441c00020384410038058554001100c624410304c020301c10440303a52000140141e04441800c101c0c100e901c07507100850305040344c1c9500100c408032040c1312450082000505002140c922031f00d83c1c0f18103019241e465800495039080d0301800702003548014000300f944003801e40d80e0492111400d070400211002d92040155041540714842d6017410714080e2101c002c6130300402c03c2020803200d41e801046000c91850400034510818101d2010840d400d03200d01b259224600007801107c14100c001c0c0303405511801008102e2041d484024008603000d004c55030f81da80504420f48d0300c028407907882040c00420481e60203c3c00c40407651500f524851034200007461 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775799424 1250 775798174 775798181
    0x31207050d0b03010b1008040c03050321070813030e010c0b0906100501090f21060219030c02240c1c061a040b07060b0303220e01240509060d110d 64
    0x40d0b000c800a220f01510380c2c01148440301005003c0040103101000501030148a02007100210f50100440ba07956984c071020800c908400d0604040c105c1c15840032940603445400d41e54000c0703204c1a11000c0c140134550701601d55450344003500341800b0400441c00b01050151211034441e074986da002c2c280c01d01e0a52621032082a207604000d0502c5103040003480070824a504c0001600c0280c418a0400680070001940d00c5511a00041c403045c0000ba100003050a0405c2c11341007545240c9061141c180c0701e0310300b40d07116110b801e4007821590f031201c040303600030f91851402c1c4e800a6290254030720309964107801c1505079548036199a601a11040c4c2040804600030f03800c0d9140710b009442d541414201048000705100b0450080c02207516140c100e8003981d000e0003241c80080c1203108649100b940b180e810752540c55a03100790001b010036040000340c2c100448002000032048201c0d100d8241c102c2d81425076140e00300c007a270707640c000f43d081c0600030b09424503115103007001c112800d50325241c004181000e002d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775800674 1250 775799424 775799441
    0x30c0b0705210a020403120203131a070312090b0405060118020426010605091f08030f0720030d0804060b0a080c0d06140109291011031207050d 63
    0x410508000307114840802c42060a9245502a0107441580b50305680c48040e008036003010301045d0b0034103c2c40c6071a0760004000c01211142155040c0c406aa400086c80307291402d130381849003440304011003000039225044d035040c09980000002140c0041da1240660044102c03022034103036020000600441500728030044009060740e100750302e801d040c0111203d5040184508a40c01182c021400300070700380a40000d4050312018100350f08500d01f07402d01e8807180080c00c4224410b61004400440c0307410f404030854860f80f2500d03407507078508a41c0d0366071038040e04104002d81030342c0800031504840503941841001c65031045550b81215600305402c200040303c0540c0102d520030300641e08200007054021580c0c00c60b19508490658248030b0784e0401d84041c200030700389803580399400400401e02c0030440d400403101140a1000c5018114a01f414404900c0da121660b0750120758078854400035032103260703000d01e070a41240c1640c0c100003010107246a25081503c206000c10300115000030221b8a501c1490310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775801924 1250 775800674 775800677
    0x103111e0f07060504174f050a0b040311120304080106030f0c1e15031d0123040308190603020301020a1e05071505150a0b0d050c041401031a0d030c0b07 67
    0x540510500d041d04000b00c7e1100d412401480c1d540b00045c801c1ca1168040300002100e090700781c0f8590b280e0396058929195020301784c4290003800c8041200c040c240256401d407a4002d0b1007400c0f00700308600700440b490001030b086031540300030803011502c81020300400d00110312420b202a001030389898400c442c180150032100030246025221801c1141510790041101c1500d00c0c00c01c0e203200d0a540850140400d101c0100c89a101c0074040d041d130850540c03000c2d0101c524941350760850b20300300a1100d1281d2080d500980020020008500c0c81c040d0350300940365501002800092040d965400b103401c2e07030000103075500460b0404807510f041469a06610004001d43d160840c5400600d591340058000c001a44044040e80c42c0c00164003255115103c101e40e00c4001d101c800c0307490340c0709166242a886100404807503030821012440f200b2400b0103890940c1e10182c99100070031414001140140030403103c0c22242c0c480700401c000951038807040c2c01d2925000b60707598120100b080c00c160700443c0d0003500150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775803174 1250 775801924 775801927
    0x50409020102061306060f030f0c0905070c060f061a0d06080606012a2301060905220c0504020c0c09150a051014270103111e0f0706050417 61
    0x40141c0e0b0100c0c0d1a50300c10079100c10020030281c1c1c3c3c10110002c1101d604401443e56100f00088141b04114000c4407043e071113480c0000c801307500c401e00071003a91400c1c1d8106001c60b00c0c4910400000e94140c02a4001104100000695a0b074844d03229203402203050700c5080d05d8800140038004258a17010f010042e00041d0300518203418080b00083c1021800c810b01005061012188009400241d22000560390441c50105000601000383c030000c031807807103080303405619140c000950740c2003a00920f40f04900111406155159810040e404440f03805001c9503d00d1541c800424556118070250820308000e0009162042c6031105001104c8009040250981803442c40c2d000640d50321100a41550b074240c48072b0070229401e14081e0b4030402e0b0704149204840003c00e17400b80029407800070b1080c20781490b0240014035101d000550440d80c4903084150480010080303910901080e070862403410540081952428000e40640c03070454000c500111009a10703002400b00b4402a12413202840c5440714065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775804424 1250 775803174 775803191
    0xb181606091806080c0402090a0f030305220f1a19020f1504080409021b0d020a06050c0307080718120b090106170303010e0601030b03030304060e0f01110f1810020a0c0504 75
    0x542e0341c2c07100700c05da90707200d15000103600790181c03204041c02e00144244103191424544a140103080c5400c4210b840c419503154605103130481c030b894400003044400c02c0700c10b80c1d00d560404c02c140c680c110000c400c10b00400e10030010040e1104841070080125003a50740174050340321070f9800780e5051034217240f01c058200c0501d10a00c000f08544000302c5085980b85680184e5a61030300c50f0701050142d681000440600409584038130154012507221162403040204200c0c903074408803001a240030503501c03040011245400952030501905d040c1807842a0f4002c80030b80650303201005030a80e015494100d400d0f62030b0009104080d40d003409018064000c0c00142ca480c002c44e601c6032030740ca0005201c0e819003554450301142d03969010f540304e0700e100d910103401e0701d68a180c5420318001130032601400b515280b2440c800086242e4041c450743c860151040f0030145814075010405c0342d40d8009061004400b015410704010a80d02d40d001c040b04000550090501c025181c01d100124198a500c001d0045003840d129 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775805674 1250 775804424 775804439
    0x1f1a0102071205010b220c05191d060403060e070503010603031205060604180b0f030f0c1509030303280c0f031802130b0f0d0b181606091806 62
    0x1001900e9031418610048040b50a045024224204159400c0154083c006546082c1c030165400d8000c06040107000340540264100c4544c82079002c1d0030302080741442c2034064244200c410f1418603044075102c0840030303080800940360f80c0c0140e000701e0f01c071075880c150700040c5201072005000401045000300070f41d500c0e5440141ca483c0701d070010882030941d5500026015514001581c01400c62092100002c400900f020360041c0b0f00d002d0400d228854072000e4014502d00003510003009403519005d41310280c103182c14480c0c0300c03540c007070040ca10890a10510000b502c1c100040c5214104034107014210924400010304018003a10840c0d81c02c505210000300440d400c2013542007104182c1c40c000600030007205146034901c500142c000e500c800f403202001840d50554201c1900038100f220a1040c113414481041121401004d000b451030030010b0000d0807041022108041480c402025100c004035044503202403016190489008650000c0003484001000104000310340311200c0d041101a050004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775806924 1250 775805674 775805683
    0x50108010b0d1e0f0f1517070302040c05120f0603060f0c0c10020306011d030d0c0302030d050901050106120c08010e060a09020d091703010e01030305090406081f1a0102 74
    0x1d11440705000180314500195581d0220141040012880202c0c0808000080141264420040e00c003420680e02da5240c114501c0758844840030b814010001510b001c1d07182903030342003842c80600c0d64002c800c00040540c48500400b281402c19690700c680d28001c0c120307140b60601c0041c2c4146c5c01c5074150707010001140ca001a04130341058042100458550313510951031410711410000c5d600314014411010581030294000d18064a4243c0f50710709040e040958041c14420041600d541c583c0c00188a007118034020fa4040154500a1050741d01d408104820385040e11401d681508150b0356640041048650103144000550105d18040c005541c0e0070782d0083c00784606004d658032501240c008a110b5a5588800000800b0b92440954880030890300e0000101040c3c4400d480d02d40544810980280903c8126810703108913003000d0310280d0031034500300c65a8001ca6440d64000f03980340408507800070104403400c260301d1040000316507a1142035209080d59039402d00e0760301003540c80400085582c4c0104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775808174 1250 775806924 775806929
    0x2211807150e120a0f0b090a03090306320114010f0806090c0d0c020f070f12030302070c0b0708030915060a050f150f040f0f0e0601050702030a060612061505010801 72
    0x26009641100c00d5001410f1200c03482c991400510030103440c8400c0041c0d030191000f046000d4513140b076455850400242d12010340b8940100014081130003880050010352040200a6680078103491058800002624240b6100c10341103540310401d00412840d0310340b843d1034030b9016007841c0c40b9160300b51824024058044c0a08010720524001e00050000c40f4250240e84519140e03020503c049100c0100c084e4552202e09240e00b80d5001701440814071059036201082140c3d143c0c1c0c0703422503003a40350714110002c3d080000115460f040c94100015421741c50405040d50724001c8004030360700c0c2061070515182552007209805800701c07a0080146603652840c0d85030403102c050300d13805884c0f40901e0005403880d00348400c0f514444800300c0c540d0418400074010f030050b1020901016111074407040b401040d401c0303520a20072100055400078010354803580213400c009102034101e88291110360344140513030b61103070021116405080c140324107005050240d091540f0a014611840d1410304000901020050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775809424 1250 775808174 775808177
    0x70c1104021c02030703020403020a0b040f030b0c28020114090601060f020f0105010905221212140106050306040b0f0d030302090d060c0507021e09060f040221180715 73
    0x300c0c444400c2c000c010414001d1201140d0110358034581103602400a4002c0c0c00309901034a540c560204107150158116400c0d03800b000c640d840f0003480e6544450340e20320010600d50401740207010002c00d009203020107899101500a0101c18203940c40320003400c5074011080450740c209007406000c60031038042100c0e4150741440c03800312903481c4000e80c20b81c5403045000c1d001840d9807030a0000164655540d110034014407202c0c444160170750965640307060703408c0003e6020340505c100c2e03403031010001e02590708000140c0907180d02040820f10b110300403482d844241d01800120f0030001c2000303110b1030b16100d010389070802280c80015065074030700410061186014000e0500d0760000d80200103036596800209401d81c0100d00340b002d200c02c21001441a08203c0c0c0c128020b0801c10074086480004998910200300c025241c20354940c0d0f010100031b2035001d001280c0b81c005508012102400721180c0351030b807441c880080083d610b0b00340b100d040c40b00b40746a400c4401c6160840c1c801400a1380828401e4030030044907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775810674 1250 775809424 775809427
    0x3050727031a06010e060a02070e070912051f021c091b0303050403060f1b080703150e041203020702010504090e151602010b040b1c06270605070c110402 67
    0x15090410400d034015040580762103a010300307110a040045040d207100b00402e9913840384c81c1120300705006c0280070340d100900240e0001a0123203c480c0a088100d94042014540b4001140c1c2e40c3c120750310307906d501100c181da542d0408200f80d40755041e0604101000343c00410218604220f44c4522404040582d403592042e03521030205009000008600c51403074080d8800b003c0119070f170307450040c215a0140c131040fa50141890313001c000d100014411300c192a10303180000302101101c03050444459000038210410f00d50385840c2d008060188a44103006030140041103020b906140c10290f032408040f407034040c101401040710302e0060b6031241c261002c69007034150210b031785440303150010b040c1209100d807610704190780741c00c02076882c880300701c024103040641c0c000700400b001120a1106490345400c810744c100195040c030240c0d01003036252407412075000351000181c010f05018500f500032951192050400c0c000d10054060100500c1107a4200d0b5017410000514180d995550710f6195039614560f00c034550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775811924 1250 775810674 775810727
    0x109020d05010e1b280308040608011805010e0609280c0e0307141302160606030311010c020c0f370f0609090b04140c2502060327030f04090c030507 65
    0x45c001104006941d102502c1d41d11192507210040007603d00b4894814100c4d00e1100000c000031003072241c503059505081c556106c507174440c0c0a000451001038146101d0045540600c014407078084d50344e0009071201c50780814080d401303c0009102110940090744a500b0401c4104020301034420a02154101501d6540c1c0900d48500ca29000b8040d201e40311b09020342044410b001c02ca0b10b5407000d01a40d1090b01c0700143c082c45410128220b1391210b443d075001d81d1164008182d07a10b032040d00440040d50080c42100ea24180c10007542c4140c0080340f50035819106000c84030780d000c3c212004d20014204141003d0440c500e0001d0050681000e4892000c0c00d6585042d0b02c03100c0d41300e503080903101a5a00e00c02c0c01c0380e4100202c0c440d0342544021b000020000c991042e800c0c00140c031040e42d4440c5030b001042a419521408208022038a05051440c010f60104000c00c80154084c0301820741e9919207000140c803149052100401d5a105040c81020503241c402000b44180c0c000c6e901980040c603c000d00c0f40c0b44170 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775813174 1250 775811924 775811989
    0x140301052a04080f0d0908010207020915040f02160b072307060207230f01141b09090a0207030801090501032102010b061803120313140109020d05010e1b 67
    0x10403600081d03414050080f013240300d410001000e400c50107050390f9400b1410b40d550943c600700d000c0c1c0340d4025408040340700880d0202d40003a80c00b00040c48014400501e100c0b4601411040382c1c0042400641c06201001003000c0c01141c400940e4042e01606048840c2c08000701c0d1100000c0000c54070005040303001c9150000c0c0310300c0380e05480d441603005040200c3c8802c2140a0b840170007002c0e0700481180700b0a107400f2041c41060295480c0425100180e0685807200c1c003074090602440c42c003601e1100010701840d005079588445150003490301100060307640d010760900808644058110a00300b031f007000010000a2000030490091502000002145040c6450100c0c00342000c802065446030001c949100c01800744154880241070482c2110780460b0300c00d6070040c043c0021036840301030b03040000f266000b00e032003c07a00034103009100c03000244090309a03001560344414008140d03550ba5644e080c035410000c080154a02600c81c007024200e0035180c807400220100c00300d030300050701140c0c4d0044402c400d9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775814424 1250 775813174 775813177
    0x1103190e04020403140f011b051b01110a08011a07021e030f0d0207090c0912060207020a0b091207300b1e010b190c02030c19140301052a 60
    0x18100a0003599950394904007203500c4020300b1081c5c4018001d040c6500c4800405100e030365200500b0441250815001d0301059a1030707000040b034114041000003c9a100c0c14082c0310f12900420341c04042c80d290000b07018000c081080507041004a869004054540030703a400058844c0c45a0445501c8140e001034600d011541074041c19141c0c244c4038034840305c405050086148002c3d041c840d800ca945140d621141c0d003056859807074003203003c62046041441000107608500640501604d009490a09980d001c40d0f160710f09030780f05001784600420800d85615001c500d07e140c5042c04401801941c3c02c1c0b5041e405049004800a490341c1d81d16019024080c9030000221030b16604032100c0303440fa140c4041e009000510000460540c60b840c0d200100d03465400400313a0300c440b001c4030302441c0c000c50350703a10039180c07d500c01c2003d81c2e03d072140440740092a500d410310152040c11850180d40c50381c0c1b41000c1c906040d014403215910a0341003000300950b0400024524850411101e10780110a201c1c64940505 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775815674 1250 775814424 775814447
    0x121802090115030e0307210504030c0b0315030d0906051b0a0b070e09090d05030a022a0d030b06030c0f070f060203011401080603060417090a030f0b0106110319 70
    0x128244000000748109008600d82e00950291400c2c8078481d0401001600ea2107400b800500c41c1c25410b0304c4840d075800e01141105910344030308106143c1900c1e502c034420901c520fa0301400f2030300000003c010304280010009020820254000d09510041c10170103414a42a4081c100402c14003140d44210800c10f40700007034900441c003007524a1120581030090070b07104101e1f45407021900462114509042280c0310a108080c1d2401800003540c49001c1110b4561015000c038186035000e1020300034900c5035042988610303020103050110080044031003400c181240310302200f030500d0000382c02c0710b0b500c0340c40c2226804068590003c0e9504144c141d014001c0c01814009440c012070922841300704225540190305a55428044810002c007400044602610484029405800400225000542c2c08a26040380441c0001c1b1a0801c64580081214844a68016224800043c42050600858035207950140000d4903103281c1c0d000d400c022031a5a03105620750703403495000d201c100c0030400e441003140005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775816924 1250 775815674 775815679
    0xe010303021902060f0a20060106050d0908041508091e0703020f0409080a050403140d0c0308060a0b0d090b0f090a031101110409021206030c0109300b0906130201121802 74
    0x48400c000d0707070000c080c1d607249040c84a2000030311200021f404000a9024100c81d480d503a07003842e0000810040018005100c02180c00110501c00401c0e0196441440c403900c6206981d500010324161800340e2400c40c41c10b9022201d203e05200f00c0039842404a8a0340940c6d80545215418410050224000b00a0000050914200030034030390714159010000700304580c050090300b2000440c003d5007071b403644162071903080030850592100000a00500c0034030350103d0000c0401403071560340c42044400e5445040540321080e581c0c10101c042020b41400d4a0708010000d41070354071407406980059941c840040003a007402f0070a2101460300b03100350000b40d01208030800c120f0700c0f40e660360303080c50185d0410804040c200c1d07035080000702d45080004071408d080005070f42e0740783d10f5403600002034080c036a00b62404d41241403854121402c3c2d140710540c02501d506c104815420703407516000180c10310070042d00d90340404420841030000348c0c0e8089200600081d41203c00264462401c05101a04100400c000d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775818174 1250 775816924 775816927
    0x506150f0c0d020105090d0302190c02120f0c0a0806090607050c16031a0105041a10050702040e0f0705100915030e0d0e0f01051e0c0309090901150e010303021902060f 73
    0x8110f40c1034110b640558003c0080b1080504042c0b0142c060340115805882c203140400841da4000748200d50403120030740084c00c010003a002c0c050040c0e0030000242d00e04184c680c0402e036600e1702ca05040300d0180082c00b4031000f610090800c0308803151603000c09400340741000800325410020340801e02170f40007080d0140080c01540ca6480ca080790180b040b842d03600598040d02000012207080030b005d404480b21101d204078a05840303c804002017085449114801c0040610480c2d0050316584079170070f03a62903c0001807219556203102a454070030b05800882c081e1400c40d604506803500182c540c01601c03801c000c03c281e24504608210010494240465030920448008460680d009400c407008a5826188400048500001901c0d184a00781412019603000100b80414000f50005006a0100742c0e0540e0703e084a04400a150711030199840c1310a6551100e8405184201c0c1c109130340204103074a95500c1d95855500d0184d11442c520400846d5001003c10942c01c5558a0040381c1a202076034500a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775819424 1250 775818174 775818193
    0x3090f0315140f07030e1c050405040b040b0d11040908070f0c0e091504020609150d05070201050f01061803020915042307050a0908010203040b09100506150f0c 70
    0xc8055200d54068090751030300c0c020b800c003103140041c00c4541c890400d80307800c0c00c3c0d1a102c00000302e00610b0944005680c6000303101403a034184043c0601e81040d0542e541c4c03400c0d00d89041000304012995181c40c16807180380350146e00303c180d484690a20210390382200350303014035007014808180030704155240202551f00014204042010220208101c14050070b000c404154a504851601030010b072941c403103682c07010b9950418580305c07010783c0340e1084c809441c49041451440100ea031443c101e59400a40c2e031030110b41d141d0070055a01c04c00390721204a100038441d500303081880051031103043c0030b8202045014050340d0000c40c0b1042e4090000d560180a01c6104e1400400c005180c019440c2440d100d2420009007002021400c4446400741c02d0703411800342a80c50764002640c00e54803c02004040c05002c40c00015454028800755100b10300400940030f451510485080c1071514140040007601d20344803e1010548450400038410b032452a800c03aa11800205c491a450185401010081c4506040f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 775820674 1250 775819424 775819433
    0x3060b030a0210050d092405060f030606040917130602060f0415050a02070f0b100608040b010e100803180907030e07060503060103020c0f07150212180a03020d03090e0c2503090f03 79
    0x1080f110f6041d40c7e010400d9884050402c0800c20040203490f6040c0e0010340031641c01d103030640c410031041e446002203080400a40d5258102078002c06100d0a100f140201c04204087c0c0502c407c42e40000c3c1c030000121103180030b540d580032007035015038070a040f1a40d540000b01d400c82c0c1641150841ca0700704d40d6080c40000350789441c2e203070000e040340e003090075440036440015401d00822502e07001c4c42e440201031426a003001000040c0102c0100b02c103640704056030000035000004c1c03005014941da11800b40e52810741c40814040360f0000a00044c0c20980380c410048000c010104564064880303c0c901140c3d01d40754900100c02074002c10392156a6806900104800401c0029410040340d8402a1000d90700e061054182c1c0c4401d9041c0403c4460706003000622102408220781a803100d0f4010a028120b40d1070350041900c107400b0b0a82107010a42101051040a1402c66900d038820a02c40016140c409441c0300c1100c441c0c81d0403c01c0d000704400d02e107010304041c05240d501c00034081d14280b084005503282130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 775821924 1250 775820674 775820723
    0xd0b0a050402100c080f180909101d0c360604050109150e0405070b04140906060c070b07060b040504050d030e010228020a08040f03060b030a0210050d09 67
    0x3402c030f118001403440c1080f070601803501e1010440c1c102c3c18540c01c00e07405202c4869070360b001c2c00da44001d44d495152200711580d54014414040d90b540e40041c4a0602910f04000445000000c101d40c90540905840d60845c0c00052503640d4040c240e079841c600c03d10401108402d420400072080700c84062180c071090b51001c4801381071080400312010f20030b60741d03a034014000300c900f1001517040c280c850100501c8080c1c02801c4080e0080e100780202c5400c240d40f6100240745402c250046030314140812100251380c600f040181d03812100840c0c1c410301e042c01d40c00815550b04224401e01c2c24010020440304203109090b482070400d00c2020300700788090f00d428900103407207012a401000c00b0034035054405040e44414829204028070b040d18a80101c02501c0c19641141000301c0710100318410200300310002411600a00014030764992102d05d62402d42c50b200003035540441180340131340d00909486015940b107081c010890f08050400607a030720151007000001d0800400040d08103500324442c04686d088107007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 775823174 1250 775821924 775821931
    0x40e0c040c11070509040c031b0803030709080c09250522081005060f1507060f06080c030303160e060d060b03250e0105220b0a0f0f02030a0e0d0b0a05 66
    0xc0a550311113403604c0c00c000720701031309880c003030400d1080c7c140500029130300b64844581007c049603403255142d42e039140146580d00807202080010707000701041150f094200403030507018108586c001000c2c0752515045600d8048882145983c515040c074005805000d442140c42400d01080a080e400d0f5140d0702d140c080510310710542c815803062100c3c403044e0fa141803140c9401343c4801451012820340103403c008088000d510301c0c15158204026820000c2d240d48900054556041d0300810b01702e03e0400c1d2a41000b04c1340c1c003041e000390020020481c44c44005007655044003424140f1540010040011a0550003100c1c59110500e14296021a0192100e400307144109240300c940c0c010340000705207550042801c40f88081c08524903903603000c041e44c000d07005440e001a00503040d80da003604061040c01000313403c0d070220910540001d036000500b07900a51010098145061000510544203c020740c3c0348200c4082000f0081d00b502d40f0120b07030f07032000480e0940350340007000200c15007003400034240189000e8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 775824424 1250 775823174 775823207
    0x1207020705030d020309040c090b1603030b030f0a1205040315051b04150f03110703170702030909011707090e01021b07060c0b0604150e0403230702040e0c040c 70
    0xc650004642c5070008841d950103840d0340c065030400c500c00341808045d02030340c030501003805007650700840c01d030554202030300c03405550010164581d102403c0140846900c20303091030090300214030a5004100002d00c6e07400c00342e0701c0700c075060345281d4034101200d19000e541c10041c000c0501000580ba07a60b8280c00084c09084032034504000c4170301050118000317100c0d03441100c6501e60806400c020030b030300690068114665078107000c03030ba180d41d001c0050410351040c40114041622050040c01d900c01c1c4072003041c2e02c0100350004500d0030103001d0000320b514005204500d1000840d0b6039442460f9000c1c0001e070000c09040c08140400c081604046003c0c0d00b0521364807240d03da0110303040c15001d0002520b202180c00300c0c0c8403e20402c901c5d44440d0540e81c4014100342c0c100f501c40c4039130602c60321810301020052001c1340c41c8072041d00307091070024804200040031400d92061604044400e0741c0d00f908481806a048400040000c060483d1504280e128800d643d486898901044908c40c0c101490031440142c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 775825674 1250 775824424 775824433
    0x30c1605250f050d0c5406120f0302030c010f230106090b07060b090403170f010311012a050c010f0206311203021e0306130f0e03120702 60
    0x1904103000302c050011202803c00c06014000704254a0005104100c200d406d00f0f005041360f1181400f882c0c417032020b4501111b0510145419500e41d0350340b00c05110980d5100d01d080c08214589200c00248000f000e038040d00b412980007150f0304044c020021115080c2d1b05074000c1c0100d0080c0084040100001009040806081c18090280300c5d150101141601c50039100c29141d54204a10806540c010100803102141d40e0484458556140102d5502c220710030b42e180c03070728542101c0c4102803401d006041c42c400c14400e14011301c0051104035001c1c004801c2841c000041160541c030300d1003680c11a51514606540d2a0790b40400d000c0c0224000c40e500c03d0a888802c050b052280c0100e0390307410221002c5080e0ba084a400b141c42252143d401c122408010708070070f041e5241903d40a00105400b4804800310b0f41c0020540c0380b0401700e6211b0107007002015199400c41c03414201180b003000e9030007148981c80d0741e20225007250075450b500072003000f2403980441c2d4444a18401c9104042419249140507219 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 775826924 1250 775825674 775825679
    0x30b0102030c06040b060604081015150c11040b0d0c030b311403030a020a14090f010e06040801090b15120a0f0c120305070314030c1605250f 62
    0xc1141c1c110b0b814000100720542d103584032980c036640090102c2d81d100a00300300000d0014410040c0c0b24600501d98000a0481e0501c00070004100340c0d903000030034400185180e039001c035402c00303e2000010b411010802e418a60303000007034010103411000da42c3c0956010300140511800c411090240e81c49a0f03d440c01544a0201075001080502c8000040c040c120110010300e80410454488880c420403d074180341e65011211030842d00f0484110b0301103075003c90f8240e00c0b0741c0e20919480b8400c1031407001d07500d891032507804034070000c1003004121705000e0314140980498840d0401c450091074540700070003801c81c4a25010350345030f1040d02e41c0021034400c0405100149072034448041c540c5224401402c20b581d10399126100c02926050a0300c408441000018400b07400302d070500c070303074034800d41d2000e6640100380703070281c052558005181c60701c203000d000b04494614150101c4034258000802c8458000062520901d0450008544401c01145141502c0c40d011b410000300240d403400400c1110542c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 775828174 1250 775826924 775826927
    0x60b011107050111030c010903080f16050d05060f0909010f0f0b031e0102041e0608070206010e06241b120c030901030c02010e0f10060509100b030702071212030b01 72
    0x3032001024000360071800301044a5801a0149070482d1596000d483c14844200c01c0306084a090560580204569000b0441c4014054220719403203240804007590414141800030031900030404800d5285590700f022034172503a00d0000583d6041c8008100301040d18000c24258042c056100c0800809420f000301e65020041900030000c4200d0040e00810700b88039007807a0f800783c0683ca0012105035550804c004107241c202814000c400901030001000200d103810401004034070000c0c2044215003180300144000140c0a81071600044120b40070900c0615070307540b00c00d1080d0518002c1c180c951001502d40792412560344044100300d014403d4412001e485e100c0100d80d80300350195410183c2003004078a0703183d0302941c80303c40175003564400010540e0070140700030302e89001c0801390314455004400c04806002076004d540f01801042d81c0541503420001d03109050c02c0e20700d000328414010081b0018040c2c91080101d0b40041c101d900b0022268002d6051000060601c515808006800d20502c0c0d051b55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 775829424 1250 775828174 775828187
    0xa0821090f09060a030605010f030b06040c091413020409061e03110405220f02091008030d110c030403080c01050708010b180310020c0c04060510050d020f0f070609060b01 75
    0x1044060280c0e14101401d000708040c04400074086584440214004008515244070381c0340601100c83c0d40e000001e080d8102003400c0c560041006210b43d0604052801c4c8981c8003054a00b10b441c400c3c0c031143c00c0c050400015a0110030050809400b510100740000c2d002e805030480b8080360429000b10f1000301c09980ea8603010821400081d100c0c2c01c03c00442e01482c20103034001c075880105440e25200d2680d500352280c81d0b09082d1041907800c1c84152003050b080d40f41040b26660400444403081c00010302d0300b400c15850340200c80405005566034040c1c3c0c081e14100e101107458980ba20000d82e40e4850f140e18082c0d50326003001180710712a42c6082d00042d910343c01003044506891108891341d05011a4840140500405170b8982d500b600680e526001072022a001800180d01040007900c502003540e800c0c0700c211a09544081e101e00c25584003c00c0ca01e03040412110070818410380541c0e9034072602d4501e000b5100e00100200c40000020301c4d00700780070643d0b0109207010301c0f640c0c0c00d21501a1890044811 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 775830674 1250 775829424 775829437
    0x2d15090432070f050c030412030e0a08030c07031410110a1d010914031c0c050c0904030e01081e011512111b0a1a09210a0e0303090a0821 60
    0x441e5010f0064100140940b000c1c1c400c440f0840c00300e9241c10740b218010380c1e80e03543e0f06800300d0108903482400802490300c4054800541110b000071810300051511143e0344820f14400a0956103014004950a40e0144811200004840401e02c01c00c6500100c4000d26030002e09400009031410b46050808800590135829089050756000e182c607041c032250f44116241042e000da0700d4811a1500b1501d43c0002200a80c400c031980c4a402482e4a281490f500303004050350520301c901c44400c20040025005850040b00d400203180080c003d0b561480380c42e0270f01d11965011400e905110303000260187d2480d540352495096640c42d5144a038141894001b6210252080c0340c072050107000d1005803160442040e0102c10020b07040301c9803020709131940d0740c800040c00440b400f01191541000b110060803c50014012000643d152004168401080d80c90044016000801c2442e20601ca000d076002c04c159410b80350010103402d0103540e82e40c040e60f6100709000101040c0d070901c03a030300750300d01110f8002e9404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 775831924 1250 775830674 775830677
    0x180f0c020303061e0135010602010507020f0c030303010e190e0610060813060c050f04080703020a06090608010b09011e020a0c0b090105030412020f12092d1509043207 73
    0x41d20314041c540c0c1d40780340116a80394003802640b0558441090640c410a0023403803150000205030802950007400e003460007044440da68006514a4225203002003203a0445401c0c554200054840200c400e0f5070001080102c2082c03801c0201020307481c4808552a030140c0c110200c2603440035500c0005803418941212410759001d5140c203c0720104a50341c2200244101501d0114075082d4003445020345608250880c07011039001d5481401141041004d10019040e40d060120f0300901e002001000c40d107050184024800c0302061000440e4064480f00c004280403e1548100026040c0003e40e00e1064040584501c0324400001070200360301000c6441042060b5182c514681e15a1502c0b03511901051481045100750040b410511009000301291020030902183c0ea03081c20200300099406d08a540f010851041480d44800c0f0b1b005200c80022410b0941d140c0044803007002c0c0c1224103004203100e60340c0244c1080e61138051000800840620040346901c0d042c440208106a601c10103c00c680260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 775833174 1250 775831924 775831937
    0xa020c0a062309060a110d1d06090309130e030702060406030b0a0b090102030901032a020318030c180a09201f050304201302090306180601180f0c020303061e01 70
    0x40b01c4179016007105100e600c2c5282c01c145482001d01e043d401700d4100030b81c94840501c2d41140154200002d001550b0460045002182010b4884000440170206c0c0e460203000d0654640000c82d42040a006451005400818098480e640c624014010386420b109540c4201d9041c0b1700414007864020a503080024107a00442c00c01c03031240c0040d0b00a0410744c01701421100c001c0740b14908030f12108280c205c400d410b80c0c003654861400302c41800719420340803004e61282e00201c190010781c1d1640c101d1a044000101c0052031030f81c0b900b0010000030801e110340680901e0b80a0b41c0e504104040a18110360800299075001035409041910a0b030f1501a04c412030000d01c08001080200781c982000e0b08000c681c00c14192250b011070000101c034413540c80701c920042c940116500d412860140801940090302e1002d42802508622030a51074080c1401140410541c0340c03401d04800c0c85981c00b10302c40105412003044080c94540b0081d507250002c5911921910a40d80108106c0402c0d046c107016546040c0c4800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 775834424 1250 775833174 775833181
    0x1020325110712020a05030f0c01091d190b030601061e0212090405060a080d0801091a0a150306090905010b030d090e0105041d01090f03091a120a020c0a06230906 71
    0x500d8401d8038042660f000c4090007002c00c3c2554140b0242040c0c12090323000305094049040050000c1440d540000300195241d400380540c40c00103440c01d44d202d034092100d80741c002e00180f80761006008980113582c02d0700c900800400c0d4150080138101e40421402401c00c01c01100701c1e822603981001c0030310300c422200140b0008143d410590407507504050700400214403991104101071074941c0c03e4840000054891004210031505803240304c0500f40c0000030000c00c0001000829099040c621424024501821040d00d0780e611075403180000d014008428810b082c6181880e502820604a1580c428007601e40594032035802080e080c2d04a5458440d4444140e107000d04101c014a9100303140c03500103a40f6206640145d0b002e21074900c11500c5240408a0354919007001420003006030040c107442128554100d1481c3e0600090b1440741c0c09103030a4802c1550f44081c204064051291041c40c5807188203071070b102300704c1d680c1c0200c054800180400816002c14410318552200150784001d45904001d020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 775835674 1250 775834424 775834439
    0x20f04421d040603020607080d050c040806060d0c080f010207050d0e0102101a0409150b01080603210f040f060e030304061b210201270203070e18010203251107 70
    0x1111880010400903811350f594011611341c2e80030040440d0310480001d42100c400205100d4290040c2c12444c015051504240041d6612034001e0701803417003101407c0f03182042001d004840c1c8003416401007601d103900042e00303d4a020b90410203040720343d401510744010700c1510a80c00721082c00390503401012654000f00d2803400500760307040d80c07104510515024080f2900d85004203501a032240407c0030002c01900249030440d42954bc40b141004002c8050000581e400552440c3d01e1a0040007103490f5045490040a14070450381100d4250b84082800103220030a60811011940b41e43c4a942c102a050000c02d9128400d03030282d100400c2030b00120a04003e550301c05441480e1281c1640c5a54298820740b0b2a4000001d000d4480180e460b0f8040f540306046540410300d111281003404010b090407680001c0d11010b080c01002120150080041c0090b01c164001003000720043c0001c42d80c0381000740200003000030608158400212000440c06084e12511921040070150300203015161306280c2c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 775836924 1250 775835674 775835717
    0x302120a1b080a0e16030b0a2c03090d081b06010b0304060203090c12030c070614030c0306220c091d16020a061e150810020f0442 57
    0x3070304408959451300618180b00420241d0b0000d100c602e12052003616515103080031480040080b0310315410900e61100c400b8901e400366681800e106040030100e142c130590a2715502455141540c0400110094404c2c01031a100410700003406040008103034031504843d964544081c0301c2c01116000c10000075010074040d5019613001001c2e001560080c1e03401d580010304030701402d107034114240c20020300c0d443d000c00100260b0000301000d051490189610000381c5645020003041e41105039000000030b03d15030707940c11450f00301e1803620f120040741030351002e56440101008181074010803001c450126040354140a01050b04200c0202140380750758403d50b02c54402450040c01055105602012000031141c2c00b881d029a07502860810203c1808620007064503585801d813104030303041e400240003880740490007000610104601590352030100c090282907100e254048060071800b0060100d0000700c084003038503200f01440080c1d0802c20440e591352032100385c44412a0100e1050720a8442084a481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 775838174 1250 775836924 775836931
    0xd0903030b060705011b020c06070b0411150405010320030a1a033007080f0708070b0f040b060a1508060303120106020f070b0a0e0906030a02040c0302120a1b08 70
    0x503011610310288004600280c01407903003203400380d45032030b07410900a8100003140040e03403142c401004152031880c0881c1d080c1c41142e00103030071514040000360034071a6400404103654000b170220b24416041a20045098205006a9000a003448010404682e407117400c6c1041642c10780078146151180d05440c00103080c0c0001c80f81c1d80e02d2104410f021030f5070342446149a0709007000251400313101c4041c85500c240c040c0840c0c040b0302c5003003404400013140641c800c1d6602e2900c504031160369500d0340d0a014105005180c00241a5103024003000031030008078000900892050820800e00e45a950800440f080a4024410100c11720110911003d10030704006400000140170b42c2d1900450901001200100760400009a40400d01d03400d950342d0108074400040c5000c04405081c00d10144008180c1d410045040d4810841c03940840c4dd2680c090201c1410154000c004110700444150040e0203900520406c9042e50b040c1c0000401503086801019000c3e20314001d003d500c51411402501c6201024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 775839424 1250 775838174 775838177
    0x1f12020f061e030c1b0303071e09090c0c0318081209061201060c1b06020c0405040302010b0a081612021507050f01060e0f07170c0a12050c04030606080303010b0d0903 73
    0xc071540070a404640045011300808036201e070340d540896500040c02d6000181107000c3d42d0041040000c460303403004540d060f04180c4000451081c000180071030340b1002c50f40000c51200c0c50071025112884d040010544d0b00b92280e00c0700c10403990004a890381d0b080307035882a601160056403c82405000ca10000e0034007040040500d030030aaa0121710b4400203030700760444404502d07001c5000c2d05124442c4000d4081004003510702100d18200480251204601500e02d4003e544410101d42098000c1d00700c0d000301103024019070b000320780d60f1f0074965884203130036003082e0f0084448a0104070140052034000001760060300703041c0b85000743e030441096a4401401a01d03d4066040c0050601000707008010003080e45075841a1542043d80510400802c040c00000922142122201c142074104100652205011108079100d04141e03d01f910450040740c0d0302000240f42c0300811484200507c060015a80500c00800001e074841d04c403903030b41b0303c0280680c00785d560b13051204e1056441c1b607070080700000d4440d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 775840674 1250 775839424 775839457
    0x2040e031b0105040302211608041e051009060c0b060f090405101404051f020d0f0204090605010c0f1104151401080901050118150503061f12020f06 65
    0x18048024014401d40d00c0700880c0782d45503001e00043c076504100700d4541568504c6104806804400c8501503403250b800d10503180d061580b030b19014806102d00f82c400a0083c0d46000502c0510035040d40a201c4083c0581842100b400c1b11494460780b1035a070000980b14035407610320301007000d0340f03465074441001001c2d41d600000d1136164039165103c509070a401107100e6401420980e241c4111141600c2074140078642c1c0506440c04c200c04940c00050402210b0b8226200c2c560400c0c1403d1038074082d02c944e26540c0b01103400e240100920780c05a0b4000c2c0200d502d02d2200700112a1030b18011a044000c650f406082006070760401d0011518400c46039200d00c0006000007041070200006c84103480042d88105640804440011850358000602c10351104d220402001250f0500d040b01c100d6880721107030202081c0e80d0300801d013400100c090400700030b03150013000c40340b680ca0900440b903690214a0300703c00c17641c0c0000600003403424083e09110440d0f03a00400c40301702460f032481403141a800004292001c110b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 775841924 1250 775840674 775840687
    0x21213140f0a1b031704030b070507080a080a0e010e0a15060f150504030501050a020703080901110d27110310050613020f120a020903010e060c12040314040608010e09160302040e03 79
    0x10000a0405203d03000e005c4551243e1541c01c0180c50400000c00202c2030200070002c0c00001540303002150703070b1001306041c00303412134459641103c010440d02403501103c0d0701e0074002e21f48160000500308410b520642a01c2d0000d01801942410780f20540b065900c054004c41c01404803900a842814120078203181550500d556500c8803425206d050303c0c04001c1d00d0340041c4400c10305034030414840d8000891002400030160401c001c10300e81c8280303111113110590715001c03808140ca5144900c00b4107140e081c41d403000c03000b00e81080c00c450000520280e03c82c2c07269054a6041c0305560060300c5c0f04100080041c80304d0903100351504040e50081c000144000000c00c0b00c44004501946440c7c0201c00030440140c07208180d9061608454990541c00c0c2d01d503000b0070401450ba420401114002d40240003080c15640b00c500d42950141960107055220640105012139800d901c01c042d1390480b022544020120340780c1c0441c072074850088081d05006424141401d101608081e004514050a0a0708072403070805d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 775843174 1250 775841924 775841933
    0xe06130302240f06060a0c0201030203070302160506071803030c0b061f020c13021318180f02041404050d140405030307030207080705090721021213140f0a1b03 70
    0x481d902c2008001c0d09a5401d00803940b000f28a51580b08405480705c5140020900e000b404403060703240c0003410550000300041c1c0ca1440f0760152448220408109505001c292602c20385030a01181d205001811025105c9030343c0301e0f014042c0d812640c040d2100300020404e40c030703002091200140026080b90f8605442502e4074026a590100d540e042e9018200805441c001c01c28802c00e59041da609840c01404405045815500707004200d0700e03002d1442c214031003403030944d2000d0413131041e11034108540d030b65440040c422050300d20f14015200725000c11081149015000d0210019200602160301800c00e52100500510030588150600d105250500340d03a00700180c55640010f504400581040c44c0421489208108940103000102e0758048241f800000041c07840c000340040148100c804444031003101101e034112203031640b503450900d280389081c42201191070781f0401c086419510700da030280c80c03000c40480c05000c40e281e5103000d000c4602036130300c0740740300303410001e801c0c640d9104207540000024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 775844424 1250 775843174 775843213
    0xb03060f090a050702061015030203040224072d020f010903060c090f0f080309100c1b140a08060604020d0605060a080103050d020304031a190e1f0e06130302 69
    0xd02d02814049494a44101c009040c48009071906104c010452010304c03812210541600008203589801600d82d6154000144100304042c60b9080010b442c003081280913038920001d048a50088601143c0824218a1035421440501c0f0a032031020024501900503d070822018484980503d4841081c507101c1d10380c04e0841d090f0000503800306841c030800700501a41c4149100040440410b0f542840d45045600d545030303c650400540301c0d5405070704411465004594a05900740c01504201030510342c40b14045074910140600414991182e02d81500c1c5c0ca00203405078143e405107130140c042a154541440003a4024411660070b1580301c100202d029110340c0080c0c03000c420740741d031455040c9d495401d03c0350070f01300e568017208115042000180081032448d45030f0b0f16100300d0305c8a03007030155548030800c04002606040500b016400c1c607040341d61600000078110440c0518050340f448014800022504890071920001d5043c1c00c01d40c001802d0841c280c80042609002c0d00503038030402074410341101903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 775845674 1250 775844424 775844431
    0x1c02060c37020a05060a1e08070e0f010c0b10030b09011401050a0b030408070c09092001050a120e0f160321121109060708220f0b03060f09 61
    0x12405403030032080007110201c4400c0040e024401c07030107116030142c2c02060380812280101e6008250008428980754031a06d24490502000c1c1e4404000560700d52000308100f40c151405400126141c1c1e20084a18204440000008058488504041180d5038154005a008180810315480070134000b020070211441580305907140c2c0000140b4840b030007103241c00e500c8103800c00f80c047c0152903028082038001400312504550000000b54403480603140c40384891515030012509103092450702d0041046601c01803600c002122041030601a50400440c0d40d402150f4401d00025150000e510030013569511200210000d50180c2d0304c4d44c0c4819501c2486c0c9032404191500c0b541c02000c0802c180008210100d01d02d11104503100c5010040b414020141d03907041d0300352003444d07a540c144410815604401c5076005031020384005d46404003410f052107140c20040b004000000980540c82c0d440301d0403880c080c2034900d24040c5d01c00d01420211120010342000f001da03038011402c02c0102c8481d6607490340d030512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 775846924 1250 775845674 775845703
    0x120603050303011e1809061b02030d060918060f180804170a0803071116090e15061c08040e010b0403051b091b0f04030c170a021c02060c 60
    0x80d0381d4905a032645882180221140d0410001c00042c003170351200003110303010000300a8010038000158105140185204407c92010f806031080700701e605600800038102c9000030010421005a40710315150596881c0c601c00380c45513408090800000c1c0660740200002c51919900054a00e41501c518480000d00d00090760b540c080482c04101114211009140492061024100c600496549c00d84640000307804031090010441098201d00e90030003070981406a051061500b00b84d5540c602401032114a1246a0030b002c0c2414103124500d00b0b000d40780c011240030b84208034010f0f44903605040c0c0c400e01402103403c01c20400000802c1083c10040c64003034802d00d654a0b036108c1c5107140c032514107216004069460041d040002c103ca0751010480390380000120000c40144d01c44800800301e40c40352802d0300a142d580820f010060042c00a01301058070318000000c0c90780710b441c420b49565142c100000030761210716050a00020380e209684650b1107071000c3e18160906120000003420b20a114000c0c0f80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 775848174 1250 775846924 775846927
    0x30c0803071107061e140c0d080a1404420c08090c01090b03060a12120306060c05030304080a0e1c0224042903040308040b010902120f06011206030503 66
    0x81c2e100602c460750040440d424500215540c400c0004844804508040c0503c003154030317510401c0080504440031a14904156204040240c50250080c1d0f4203413035211100e031802000c60b0404419410041c041d642150000e1000032001880486401101c0b0b1700034002c0c11001d00c0001045010000041041c0c20302d07601040c02245844018002c040007440700d207150380881d8015540d44d80014030320342035980c01c4c02c01c2550f907a503000c040f80d03980107141d012055914000550708203101c0c9100d500381c00c406040e1340074003074666911000c60f1042561900074100c1c0d00200702040005220320000c2c0440c84032800c01c4860b003060480040d102c004240c0c00841c01e192420b141c5800c520300070214152507000180103021000043d031b0466514025030080b113640b60341d070022191501107100d40c0300c0c5941d030400301065076a240c603240003054005e060340c04984840030381c000410791148c0c600a440e6003e00000502d40b840d503031006a1b82d043e2001a04040c14011320b155a1040b00800d80071380400f5501410065 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 775849424 1250 775848174 775848197
    0x15040f02040c080712090507050a09140f090303070e0427030201060e0115030e030d110a0306050904021309240209130b060a050f120f0405060a0504021507030c080307 73
    0x30055a8010290908003c4031404100070030b5005200d07080d841d00000350001d44200e403480c1141c68240365410403584210343e4400081c00780f03103170740140c2e08000c03002c00c0c42000364617103c203400310303101301507a5594160b0401e0000904061150f01c60900d511001400420744c10f89800e12158038401c030994100c46002c106400c141899024007810b4000c2c405507940840962500c0d45030700d42d0310f40d00c0041c4401c1507210001c2c075400030f00070026903544102e12281009200724540503000706a0100d00b002002c2800c0c440300040702c2c0707400e01d012031245401900d807114804589010030700400d0071990440318001c0780c0d0140c079003c911182c070380380800a20404c0180d40b180c4400400c40d006140c41620304c401428002c80159030386981c0d042d00d0000e03180703003400d42d2181d01c2031009403000c2c014012000310300e1072280e04101d04800418986800f682c0a20142c0c3d00f591144080c5a050711011140603421008000c010385ca103090220003030248074000d14007050780c00070307aa07107140450340141c0d101d500162191884 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 775850674 1250 775849424 775849429
    0x504050d1509060e0118120f18120308010e0f040b0601050d090507050a0e133002150106110a0206030a1103010905040203071203020c0f0a030203060a051b0705060604020a0215040f02 80
    0x1000760060704030b06c0c0c40c0c0c1e040b1b4103595040d160aa8040a92042104070020314100e5030184042541143c440402100c000e500c03145e44901c42142a01e090700000d108a0000560b11600200039015101004000600f0754854840a11100002e1701082c1000310410042c203031203416100744000c2a21510103002c00324948820403245070b00395008102144924001d0000c0d00c04403a80442c4410390092800c0b0040c1442a01081c03040402d010100014050840c240d10540d8045542c104c5000c45006403602031340c85880454110920101c0722a0507440302104402500e0014051a07011400d2040810f0003410110b041282d078000382e018000311500d6205000841c41d09010103c00307004c44000040f00c001041d20005d666248500c0428001c1800da1a11103054864940010245402404492650401c101120010b04080f5400d85840705000c0c0242d21844001003203802c5103401a004248640710031b01000001d500900c80c2c1030640c4582d071a6040c520401452892050f4042c01800551104c0da005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 775851924 1250 775850674 775850681
    0xa0c02030607110c10030605090f01060f050306030309012118200d0308090a0602030702060601140f070605060f04110c10051303110a060608070320010504050d1509060e01 75
    0x16802c20b0200c3e800480040c0d1400040f1459103800448074941e4400c5c505605030024403880d00110342003101d14081003072041003c1071181c12244903503a0400300da02c7c03015086480340025117206600d0780003001203215540c45481c5c01025007035a1400458074440a813400003c89200c403000c0d4207402c1d005200341c0140158165503441010100081c0c0349440c1c06200021800e0381840300050501080d00007285007840c040001c940303078a5005400319640e09200b24044d41d41c1104072a054001742c0184900b509011800c8180c54068030061019420030800356200342c081d201c020212038000303a00c0d900409207503589001301000100c1784541d0691f10350b00400c10904119418440c2d42c809410f2201f4445803041d6252000c0d00e4070307054605624a80703684140e079414140d140d800909203a051205c00f241940003c644481242e01c20b0010441e01c901c0b00c103904454423011901607020901c10b1004006604200c07480038001e82c42032500903102c01c071442a2104070703801034500b560000da80301c200b20302440e001d21 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 775853174 1250 775851924 775851931
    0x180106060914030c0a0b031504180b160f3203040b010603060509131109010608071b050303150d0501050a0603141506060a1815140c0d05090a0302060a0c020306 70
    0x20040c1210850b0130340814001c0c04039100d5840907003000030010f411005800c01024000d4002802800f1106000394968103c0a0070707101500c00090107008203140b02c09031025054070007074136100d20801c07500e603881c152010306249180000043c040b40d082411100028822180d40c2c0c09959a1900c0c0c1c100303820120340d01c00050304030405051409005206680d144120b07182d00100747e0306c46407000100f40ca00301844a49080c01703a9000b00d111713000481d5807074110b1203032445401c143d50340c0701c00d0303000c0c02c400300d80040340a4401400e03a030010004582e207000c0e08441807a6268015240056000039a07440360308685044811030303034259a038242403040002e0140740d000100c00400050880c2c041f03a0400030350043c00a0091840b0340070000304240014001d0a81200d10014003480140e01a170b101041c641c00e0100241d5000003c00350810140712440314025a170510204000610303c41a00240940c1c0650103550381d0340d44003e80c03100002c0180d4803040107294401d250390380c1d0b108000e045d105040c070703212016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 775854424 1250 775853174 775853179
    0x8071d0d061410030804030b060d140106050111120702040c05131512140f0a0b03010c050d0c05040e0708040501060b04181b0512040c05210d0e0105040e180106060914 73
    0x152010130128892109440a60380c1003003140d05152035000000743d00001080c802800f588040d1007000000006510090840d0000c4e240c03411903d412904407500c8059000700200035540603c84400941000d40c041091606181060fa150001d0155207440044075a03000c03840140c40f00c101580e01c40e9110031501103603000c8030010721100c00c007d0110080c00c03c0c020110b0050300500c0c40003a0711160160464010b460001d0001c210401c2c1810b001000f580c00503282d00003280c280300090003803078441d004880460300e6a00c0d035041581c40e0903104035490031005c0c000395559900c90001250701c4080c0030081c0018108022041078040c0c2d8001100240c400c0c18104d07083d80e038481c100c0d120140740c00c40101c0b01045d0804400a40a5480b89000e0f49044401c0e003155401c41038005002c503c821440e1000000a4240402c58903181c0203120112a00f80d9a40c085900180c2c044c0020846025020822900101c0601005e0039058848600508403480c542c1f20300005200d0280c2000100201203554100c00030a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 775855674 1250 775854424 775854451
    0x40603020303190e091e130c060207060e06030615071518050d0807050f070312051e0c030402010f0309020d0516050406090213050607142d0303040308071d0d0614 71
    0x1500381c904641e200304086c40b02c15401340c0c0007944001000b140030300c81607030143c050f12805448582c02035a90b1080d01640d00130170f00e1030340c03c010180707012400d0f41d1007014000e1111391115004d070000d070040c0d007001c202201c150060b6011041c0040443c000c182950407032075142903504040d814030138030b480c130492052030900c1002000d01c60510741c090b08441c88400460440c0b60340300384900c4e0031104a8405003240200e03528000a1004c10200b40044000f110428804076081e40ca03090007541440c4400e4900038081031481e110982414025004a0a806d00040900500702c500780c0300e85043c020820704401560401d8031003885a440c0512810b005042455001c43c1020300d00c256449018101c1e0040e140b103141e011550801300030014281e0054101c41c94203a40105030012101c40707240e4140c02c41546500842401d041680c0c0001003035070300c66a016a14011603407103819041c8c500e4025404580405604500381c035500c1d80382d0f0404010240e04c110000501b010b802045810080c0014140140d900756 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 775856924 1250 775855674 775855681
    0x180a090b01080109051509010803040f0f0806070f05160c080f0f0606120a051006050a060e010828020f07060501120507031212050a1b021614040603020303190e09 71
    0xa02800702c50540d4007a810001e899164407044c0c0c0b81840301800c903a584440e20f0000403400040c00300203002224400d511140610343c42c0e88425400b4101360150165640c0000d00250610f40710700c10fa0360100390750b8100280780407002c0c807071592502d4030b0710016603801c16100010040043e0811148e10050300300c5021307100240c080c6500646a80014204030710039104501100c40c0c0e03100900c03480b82810341c407800704c0b030b8400c101c4035205016006034407030148a07450b0b41c00000741580c0284c1c964000e440e0141c0d202e052690f41d08140500410003443c3c03a0500c03400415a10a018555100a0800e1030350b145038540c4694907850b000c0b05845050f00100100a05803140e070002070b0703000070104c0a4035405044400c080c403441304211031441c08518481d25103804c0c00240140300382c1e81d0b2712002c01c0da4902c2019564000c44108181e03583c0c80c904a85100f24406010104a035604480c0e0a101403803000b000402d0850741c980020b85103810014182c26022000402020301503086040701d6405501030f40e401d00d0f04d19 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 775858174 1250 775856924 775856927
    0x7140a030e19030f11210c0102030a0e130603060612150b060f0a1101090b01180605060a1d0a03031e080c031602010902090901050702070801020304050a26180a090b01 73
    0x50701e07100090042e03202000c44400c0080d1500e1308103558a02801c4903013000318486c0c1c124806451180a203500c4e0048070003004103948040201c44468046860f003003004e00390241440294000c01043c3c0740d260355641c10100024219000e45801014030031200c05001100d42000c04e43c0d121036070200e282003480d020407100c1c1030302c4400c1178801003d00b020445885041440c0e043d41c06600b4080e404119504e4105140108054840c1c11816980b10f00c8902d40c664040004440c1185c515000311a4800d83c24403180c802c45204521b00f00c0182c00c150719107181d090241d008112940481d8104a0104d178190807919516440c3c52415607900c0c030a842c080e0031500746100d500e8040c0c84060100d2440b016001c0d0043c200e03a000350004e88030960701406075010b614040200c2c40c0201029502074006000749840059010414003d49018541090190150300070326510f6600c1212861200560300003002040811082c419001c0c0c0079003100321000000c0d01e50190100030040c403a980222040620301501d0444c280d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 775859424 1250 775858174 775858219
    0x140114030f06040206071704090c0e011b1202010905031b013206150703110c0301061404020a090503030406030c080606040e0402040905010f020a031a09071403070507140a030e 77
    0x4d0701510220b80d0745020b414240c0e14181d91050420300d8960024000030041e8090340085401d030219521070b4280c0150350011a954114100001e0404004481c28008501d4041a43c1207545084c00001180a40c1d607445508640120030309941e81c0d0b10300d2055210ba51070030301900c901212452446a28041c40914285a100e0700342704d072615107030031880040c80d9a02c03608103008070214140045500c801e03285c40d0041584040d0341c8403554a01a0400440301820140644020b81c2d003250f14007031005180342c0c14000290082400e07142080f1400703200103585c0e2030910091000c0d00c8180c0d00460b05541c4a20094010b0202500072805801e041104104d0024042c00d903035007107641201c000c580101c403070030300034054510221281000f61000030000321098150b40600c80c1e803150000220b1484406104011190000321a098042070401711103504245203480195444052400c2c03130740c28a0441c0e126454540c0d40e4170614100c42e402a80803009064001491503880d81044a00076110b40103881c044030354 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 775860674 1250 775859424 775859431
    0xf0b0304030503240d2406081f020d0c0810081f0207030e0613030b010512060f07090b0f030f06100905130b1f080c07020609090c070501140114030f06 66
    0x10710744060f00e0003912041c0b00e0702031850050082c45d078500f540c42d0781400400a21944044c2650b00e07003049031461400014002c84040302e030014050030361080003681c05100071683c0d42000c0c00c140d03400c0120301015801c512950600c9212a84c0c0c01c1058903040c0a07d01d2464905c0e006000e440c3c1c80740303000c1c9040c0c0304d42c80000c442004a00e080541c0391002d03441e064400e01c842c000d243d0750284c80070030081540684820500110f13800791580d0300040c2da9032401e10921522100701d82e2000d8101000140151040800141c0c10092514000354444d0b580c9140e841190400051000020400030602c81004030100310340c1e4000404035002d2910840114000c2c0240d2030b0f91107541c1c0198211041041148281e61100f801d00c4405045040d50741c081c1840c4001c00d005241e00300e0003181001c008220817000c0d080aa41b44554042c061a1820201404100100000422800d00100108480b400054080c010b032108658104d91040d12541010b11003141178080c00c00c2c990003a8002c1d410203100c40300c0000e10b241c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 775861924 1250 775860674 775860691
    0x3150e010b0a051b01380609060c101509020f0a0c1505010308181e040e01140c071e03210207060e06090f0d021e0c1905090a09020d11060c01150f0b0304030503 70
    0x25a2012320020510070f0081d0b200b040c106020b02c1349805424502d030780007810304910b84c614501d542034031030244900302d000d00c5d000e81e00d9840b0f051000311340c00f6000c2d040d500303092401400308580c407000030201c903404c2c0c5100341c1048507d118041110b0310418100340345282c4d0b5401c22200509480c21510201c00e54030040aa144d02c951345170400c01040b10002e600030100c01e000790513101c02038a443d421050b80c9038001c0f441140c200c95070120b079400b44c0c20a00c0c2c00c40040b5a140d03075403524450481e50640d103010303040d0a00c0d0310f28541c02c03c50b11000038818400d000b1480d0f445409490b4901c3c013035030340e2402e00f400319149a07082e81001c03821048056005c100c115480141c500440351500c602131034079140140c46000240c000640a00050704814030b4030019080360380846101c00a0ba8843c01d01d0303402d031028440001d40100160412400041c85e0740c94090b1030400280001d400c015021054500750307001c0307408076007000700035407030501c40100f00414540150106000c0760f403640c1081c3da0024180d2000800c03591 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 775863174 1250 775861924 775861927
    0x30c0e010617151203072015070201031503110405010e0c1b012d0b1009090e010f0204091e1107290106050a03150e010b0a051b013806 59
    0x104500122a19081c3e03001d00a0007821000290000260792079000b09419174000e80e040c648000078180c800b1144046030000b0705072640d0b096030400042d115811a060407414583c88810340000d0782d0380340c611940294014000c0b40250040c21b8144000c6400607040070302c6942040040084450042e012650440c6102050400310484000128010000d6810034a46078030074506140910001c02d21070b04c43c0c500e80c0c08041024600280801c40e2458400038a10003080c0c09070002c0001248035030040510060410010850501e58030040301243c2c00341d00715403100b5940c0c8080c0c40403505128403031001948441803c000120200c1c0f9085990f0242c14070017804408109800510811100030f15540500d100c41c800740300c0e50b140c68001c0c020b81c04c012154000289086141c000320480820400201d90424240c0207150742132072003d103d545d1080c0348450601130200070304845000c501011a00c9070202c500009840c840304c205001d481c0203010b0f43c3c150105107414504070000111503200002000c2101c645 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 775864424 1250 775863174 775863181
    0xc060c030f03090c030f010e0607050a02150c0a03140f06091b0c030d0c180b0310051809240703270c060816020c040902040605060a09030c0e010617 65
    0x949507108204024103020008024040041c40015184405450442c2901c0c16606903807031a908a40200b5a45503c80e4040c0012a181c14000d40c000c0c4602255841035410342c40540a50f41001d0a0944852110034800100558441d5041c41000003508410080c3e10b941e04055040301e40303100000d082c45109480c2040460106000d200054641140c0088901d0722510014840707916500400340404969003400c41040d581c80c450860840005102e8004603c0b80c0d06000c2c0c02907503504000c1c01c1d52496007000501090543d034450b5218030344010302c0320405903841e00d02c08880c141051310714914003010b160542a09580408440310f58020210300d000160403c0b22502c00e03403040010302c240a5404c0c264001e071014417070f035840b000044d031341180ca80f448070b44c80308000c3e40442c800008803034006070405c903c006201d24141c0c2100e0b440c0350000741701142160300c0740005501039100482c0c2ca004920300200400402c095200c1044c001c2c010070034241c00d650314011000e00410395a01c6880c07031070840320000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 775865674 1250 775864424 775864447
    0x20a1101050c1009051605090a0c0306120f1103061009020f0d0504050a1a160c021810060201061406191e05040518060312030901060e07030902040c110c06 68
    0x5031048901e8590440703804020256000f802807030780903010344581c0034501c0c43d40f0070b0003000000e4074201c3e080034084402039601d800e043d400410340381c1c40d0682010f4071140c0008404014852010ba003078007495881c0c0039004203148c400c2d4040611004103020740c0202041203090314040c806841110014040035940d04c0c5c0580700c02840788580d041013000146001d003408280100010440c20082c8558030100d0709800702081c080310b84004442c0c9040101001400e811014071800c080301410384058081d03007030784134601d5070511104c0c021150540440b001440030454103509000384001080b000885055001d04940496180d104210030800c030044007401a01000348101c406121012954a500e540c1d1500b00d032005040da4420310505120b003135000c00d221128010f08800901030940200245041d81144210200baa08000c002a4065580e00000903a041c00d88242c40c2c071814280d6000a0743d00f4082c1b041004849140c080d0004000d480c07158841c140b80001349102d981d040827101551690300010300e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 775866924 1250 775865674 775865677
    0x129010507150f0c0c11090609011206060312081b0403021f051303080c15010b070b090a080c070513020a090b0c0f1002090103061a090105070c1d09070b0901020a110105 74
    0x2406101603d0520b9004c02d42d40e00030034030306501c0c1c8900e081502804a240800c0400c3ea0706445c881c1e40030281200402a840403140300c40c1350280b06000c00b0906541d207447d01c042c94a02c102228010034060010401e00381e40c194100801b80c00c07038605441c1002e055401145541503a40302c001504022019101c962034003403030568074010480b0400004113612407908200d0784d0040707180321890344210301d1980c10a1004400d014161000e00c01c1507800c28066440b651000f20020f8480780c514090901281c01040140000300322908070302c1d0040149500d04405c1c040c1010b0340d0420761103c9071042c02440310f1146c0c4100303088200c5080c02c044540301c5d05498421030402c081654110190b1059010070340c84074042d41c0103440f180509803402c104050303407054203840c618450400d01e50030180c1002902015030140000d0b21110707004a0180649a03102c0c0711900c0259a0036401840d80c007501c00070481008410800c00014200f610003450401e1b5002d00082e5031121001c03c02801030002e070140c50301030f9100d00c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 775868174 1250 775866924 775866941
    0x261b010e0f0d05010629120a11030a0b1806012f07031103010b0d02031c050702120319090f06081801050f01030302010b0402190315090e012901050715 66
    0x20000700d020301003850300c81c4c001e024510610314a03150322008441d04d090450241c0040e00c1401d0005440d0807031110200058010080160002c50b80d00d180a400d020f14110145105a0103400c00065400401c0c0030403441e4841030803030103d1030840008025099900175841000140d050302c09a80d07014002080d40141c5070500515445881005000402d02a2210790300c3d8040505038000c0004201403401e02c0710200c0907110103501030f444141613240c40c48412a41014240051034900d00305001746d4001b602a00f00d034446045244e2002c04c01040980b14805405465491030410b0703040356140c4201d100c00d801e0248580024083c0754000120118146000c0b8010002c008008011600e081890348040c0381081c00198019840c2c280b03100c0403410640700325800030f01202180b4140416499089018110b1180c0c09880c11080c02000903240c030450040d00650041c030000400e0300c5030a00840e02c1d0310382600100300d1303c40c648406007180c02d903044402c41d80c0040c0c02c80780c84e1807181220030152001e8082e40303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 775869424 1250 775868174 775868179
    0x1109061b060915130b07140f0a2a021e040b060c07030b0702030a050301050909150405010f0b041a09041e11281401090906261b010e0f 59
    0x28208a90402c1c08035410b280145455140ea00341d86501c20485601c0c3c02118000b8408034080b0b0204140c68002d4010003209648102c0301c610f04100c0404420044c0c010301d039828089140c0c101d5031441038a4a80390030350a4481d4900ca00301295282d000248030b00f1100d441d02105080f410041144d40d215600300050308440030300303003135500c5d5244c0040544d0343c0c01e0f902c01540e80d40d65000101307160074030200031103122449030303034900d801c43c2d0804042240d1000301070b005842e103110b402c40700250016070960303240c4502e006070000100d001d202c1d11352000303070307007000407a98456450110642c00607184c04444011035941590543e100e507845180c10100402e0308074051814525025150003085854940760f0f001600c1a19940c0c0244201100b0310b00e0100a00000c03c41042c0700360042c000d030740c8805556100684149840c1d14003503960310096049913000e4020300c82c00c5030701b803c14040d00d2045080342c09504800c2401403d2110314108105210503a010000b0704015140605102907600d0300c03079609444000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 775870674 1250 775869424 775869433
    0xb060d09110405061f0f0507050123010501030902030604060c111504060f0204140f031e0a05070e1603020f090604090905061b090103020c070e010f0602060a1109061b 73
    0x80d42401444003522a55403840349041c100000d4032800d00c544200c805121665058824401c0c214007030b1040c200c5140654200b00e014000603022407003d021f042e1127002190b19548040e001035010600c0404140c02a038141400c007000a80180c0700046c1d450b62041d000303003002414007031210b000c0703860002c400406015403040601303a000c684122540e0a020354400d00301004801020b00c07442c81a405548941c01030003000644245041c240007646032418a001000e0f5500c10044071100c20050090b18a4084180e0054503414100402000144045c02c84124100c50b01c2c41c02144003540024040c0b1900100f580108a01000104800c00c0c1d40b04444001c014507100c545501d9007500800d01814207580d5071041b000810780303190800b403283c1e40440002d07036024640740202005401950210004080a01c5801000103001d030300110300a01070315030001d505020b41c0c41c0000003460035034003608041d5100e251036218205510480116035000c1c43c16502c6545850a60942940f0742c1d4a030792814640b8002c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 775871924 1250 775870674 775870691
    0xa200703030512150609010509180a09051e0712030c0c03030f170105060f0a020c0913140705010e0f12060c03100905090d0516050f0a03300b060d 64
    0x4200001d0501120b005560f181c2c00d644071111201403c2d844050150040130801008405510030401810345803c090040a0202d104008040d00801c04944460a19540700e450b24100f040038001049801c3c1c107049001c1e508010003001c243c841e01a40b01d40c49030f03111248661130405014240b0003440f40d4210311040c0f06590f503400d019000080030039a2000048181c40205040e004481503241a95400b420031b40c00d1842c41986140c969001c56400d01c01d610034552160342030755640085604c0b54942d8291966642c0807454a02c5c80c1c00440440880550081001882aa640705d00044c00c0c000e001c5840f002d00013918030200d0780146200e0b40702c822074000c4e1010006007550280086000d08201d215201401d40d44210b074100305c442c26a4036410f00c2d0004448007003d00e1241c005001600801e5440741180e10300d5951b90362520410b510101c0320b5800a0751010240740c1c204103410103801c41d5000c079a04804120340240380f03040307110940e86501c0c0d81e12040341d651922928150344c1e031288481e40c00c01c00e145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 775873174 1250 775871924 775871927
    0xa0611070306090c0f05060a0903150e01020f041e03120f03142406070b0c6c04031e02010b0324151302070f05010b030d050a20070303 59
    0x50b145c002c00e000880007240024290130848111140340c2034543e0b611440e642562396005040300700c62383c07205590b0b0700e40c82c1545034400300388000d01c0700e16070b5014560f40d2140340a0368050441051038400100c900c59010810114079400804043e0040034501a009180105420b81c0107040030b4507001216071a003000c02c000b14600200740c1c610048840303d0b03880d501c0c88403010000344d0305c40c08600400c580850008a2200c60b510782c081d0084c5c00381884149648603400684c0300c0c0401e245c00d02c01ca00380c56051940c03c00d43c00d070210940000c3d4110304034070507210140303100c42d80081005500d48800100c0c0f02c0010703090621032154040c02c42c1184840070985582c0490080c0a4a45808410300c41e014041c0d54140141c4002400002c4030b02920600449a40e54162000074501200321650000d4001200c00c16a090354401450301902c07a0304104150882420140c0c2101c007800e01c041e0003548441344261019030800c00399141c40d84079140101359100030f01c0c005800160a504512083d1091110100c01c25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 775874424 1250 775873174 775873193
    0x20705151e010b0309280506043f0f230c060a181e0204180510060b0d0f0e12120705040605040e0c1612090902090a061107030609 57
    0x101e5512049469903211600382000d07200a5a1401c0d940e80414850009070342460a2104049400400d20b10714a44d541c507080c0c1080c101303c3d000c98400080051003e4042015540000c802c181d24040c0e800344000303008203401100c1403140c61030030300680c40100c1d01d185101d011050480080300002c103544a02102a00d8980e401c070f0030340c0a169004880010f540b01c0841d20509400c2080000095000301c0d0035112081090320407202e20719002c00000051025032200e010f011042c403450414513075186010304140707042460080220061506000d8100a005c0010040d180002040500026404503103582e050060820528841389402110440240790311a400a003e00304440503a100303903a5200d40084030148103600401c2c0204000f800f00784031a00c0007003521544603009180c0c282c40d02031081c07141200002c064800322105015201a09030040e4004000c100070041d4440560a180303174000000c684154601928040240d004c060003c0034104100d402d00071034201a08028020160414140f01d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 775875674 1250 775874424 775874461
    0x7050307060b0f300a05060402121606020601030c0e0f061e0a090207210801151715011803110d031407050f3a050c010f06050f040902090a02070515 65
    0x500130034515030400d480114030759000d5544240641400c0d07480303a00300184498500c000c0d100c0ca20403200764111603e0302c05030450243c06181c00a00e0598514500442100301581000710048411024444140c01a40486400180490301e2400451510042c2d517401c0b0595072103164882244200010244103582c0203140342400b800d4441c2603c00241c0112103040c00310003030a030005143c100100840c07140d02d40d8509100045140101050321002c084160000c8283d42000080115850211040d07800040d07650f44c2c0403a105403860b40502e0760b140c200401022980c094040d17800d40494400305441034885c0c20680c1da01210780394a030412410141d81d648000c0700e8524651181d40000c19018440340024a20000d6812504015003891800750b0000c0c64116a4002406018064081c1030760081c050100c1c2c00049440c00a400c9140c01c08010400b461400c03564000c80c9010075140140e02c8a8138040d521a88035140980d940e007251400c10b14182c41d050a80e2030011808040c0545c001d28610004007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 775876924 1250 775875674 775875739
    0x1d041e03090f090b010503010e060d060501060806040f0b010509121203010b030109050108060f04020d0201020f0303070c031d0d03050a020c1507030f17060d050f012a0507050307060b0f 81
    0x4107483c1c074020300407600ea02e054640415001d2004009031a50b0580e0103601640242416012440359500c410503142c0c20f030802404940a80200080d034203003880741d041401d54400c1c0034004610000c0000e0002d10484041c1c0d8010110a0b420201e00c400c10440d00c001c440c40745681680d0303503946940c0100c00b03400a008084070142081c0000540160000b0b88074058a90041101d98503220f640c00c210303e83c0040c5600703c1c103600801c1d2140c6103c08091024502c510601c3e101c200d40e0780030500d03009100c204182c3c054070b020030b20441140d401c5d4a800c11241e12040e4941007099031136481a02c181c0c90841780c00d85207075105100c01007545003090050043e000d00b45c402d8860b00048041c2580a48224a8a00041d138180e099200096101d1030001d4600f4100b0b4011400e0346c9520542450b0242900c120f868003800804034250000c4c4107401181100c2403000360340c6001800c0080075a80c45849101e40070000d0301583c2c446102c05002e03030b10605843d2a010b002403001d46506c0001c0010307c42e28001901004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 775878174 1250 775876924 775876949
    0x8030304052103060402210c0c01061a090621010308070201121811060c0f011a032b0908150601031808071509050303010306060e060a1d041e0309 64
    0x100d42c1100ca0400061401c072a084290031580c90b0802c5c00029044105043d62203121040417550324499401c04e42d00400c0041c503266a5034403142405401c2da68142e11103d03010425a5031400c040d0042810b0313030081101214042d0340c7d0130070301c45e4030002c00740c80c059115082400200000208034401c0002c01c0c0e03030340c800c0e2a1240c0d010f081c2a0f420003101c500d1401f00d5841c0c070700301c1300745400540b0380013010303514400c02410981030601701c044240c40c082942804804c6695140c0c180d8811b00f2400d0740038000c48400310024040c40400d0100c911164201c1000c4528050740c0c01d454104050040c4050009001144220f901148240f200350b007041400781d5119012134905544d02000e4610101c0840c01c5580081c10285041c4169446c20b02d561290405c4092280e950440100059801e100450086004041c00304405080140c080103242e000b80c00c0034418980e406040006105485440505044500780c0c0c3c1e91a59850030700950301c42c03509181d643c450000b06d01c0d440815411810352750039501003407244c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 775879424 1250 775878174 775878193
    0x4030302011b1b020a0b181906020307060509071701150e0601020712020607141f05060108011509030c0b130b04030512160204060e04031d0a0b0f130803030405 70
    0x200a441503080907000000c83d5880042d400c07040d54149400d4040c800b9118118003541d0300410314540d01f00c4055004480c0000000900e036140884885818240c45101401c40c1450440041e580e4820703004010642c2d81c03150009050080203000d400d0041c5205000300110ba005160654000c0a6035907010380b1000805c00041241e48000000d14424070060b0020104541403401e04d140c072181142007241d105d40c0800030710000480405261601d10341c6030000b8088042c500580c07c000700e04030303141c0d102c03007902d882c0c100680b40e07030f000c44071504407210b1020301e610106003200111001c504d2908082d18444c4088000200700000c84011700118001c4050715009076200c40100080d885071b8400613259a024200203684486184014034100d00f0402c0c42d801c0c204015030200b010b032040d560000340860203c0e8104003d0503000f21003507140b628903c0c40c400c08180d0070b400281b9104524014030456850114010f00580c2d40310341241c841351040fa000007400d6540e0f4002e01e50740d42c4202d81c100d8483c014000d02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 775880674 1250 775879424 775879451
    0xe0a27060e010b100c060621140307020a030b04030203091809010e120a030c120f020a320a0212044505070507060f0b09160909020a05070c0b0403030201 67
    0x10a06000001401c546021a0705181110168500176041d1115a42c901000440c0410309081c8a00c2c074a5020003000c024119081c50b10001c2004001c0c024103410400c14080140e40708050001aa40d2246140c02682c030b031800e0492a5022710814079401c141000280c2100f0403c00c45203030700c03922451009104001c1d014500d25102c0f4030324030a200203170100f032000c006218040d800c104c01d0900c140c42c0400303175081220745107800c0d03c850100d6000302075400260000d50700d50210251006800c80302141c00109030142d0803040d24140344000150f03000c00820408030b214030034400d400b19030320110181c0e0740301d0342c88003484030b4409020400c200c031040249000d1610325031001007034101e000e05503000301220020000d41e00c0103044003c0101c020828100a0000010203e219400440d000ca00c40002e110f8050400e02c01d103050b005c1c00e9803100c428105a0100d00d01c0d0300c0070074030041d01c25a100c0544c035010300303c6003920f440c0100d000003002d408503590b0105024400c00040d000710b9000f0780c000c0c000409002c15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 775881924 1250 775880674 775880681
    0xb01050d03120203061c06060801110307020c01080405070b0c03030105120d050d0902190b120603031804021308031b0d050a080f060a08030a03020c011a09010e0a27060e01 75
    0xc00401042c4210b0400c002450306501542e40464060488030610040c0c0b400085000ca0f036140032242195250014468602c09109680c951124400e41602c1c50400740030103540d5014a5122504010040c800242004400d0014a000b000c3c10740c00a42c40f0314948601548a070002d0042500440c4441c40c003860048000640500b42c0103140c030b0b51031908060004d1180545810081a80c001ea0f05408134101091111140c20090070b100c4035541d103030310018004400c40c031005080b003480781d4020f21140a10100c07010381103002c0b01044500603920b00c041071061140c0110381d40300b150a40000710f811842076071810301030841901150152032640404400540c0d0900402d208040050040300000d443e480e50141c0c601c3c0c0011004198128541d0354006d011f15640c051082000000d402080314074840b13009000d403000c80790426502c0b0781001c03041c1f008a2000e0300144a10a030003907101000c50f80701c5425a0044611196100d6400213042c080c1c2035001020f13540c0001140c00d5407500480d400090701c10710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 775883174 1250 775881924 775881949
    0x1020c031504080703020a020306100905060f0a090f1d1501092025050c100804171b01050a060e0604090f0809011709060129041806050d030c0b0105 65
    0x92401d5410703180c80e11811681d41045004405503c2a45110300160750100f0405200302640c6840b100d1090606801d041500c002030440d90140003000402d000760f42c1e807034000005613031501c40c0c00510f40c1c10310350060020f0240280400c0144e4292840100306500c04500a420a0a12000d100d400d9aa03820304c9002c44080b00c1961030b03002a030050b07100c403013140c40c0014401c041030b80c0d075510b04072104180c404040c2460580200c03075075407041603005a075003860769001c4104802c1b4140700b5150704d02074584003400c03003c410440f10b91032000900000c900a404158503030b10180c0c50001c103c24a01504e181c0024050b5001d000e090b003601c2c0000581500d0b0034000c0810071503101040760b00743c0103aa983c8107102c0e00009580c40c14014100e80c0c42c440000800d80340c03486800c40c1c00003040d09504d4151a041d01c15040803105240c150f00386c01c0c41d01140c40d40412581140e800c1070700b85410421065010004090f90341219620030490251403082c0355000c0206001e09000d031380d1050340340c4d80c0da0040200c60038010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 775884424 1250 775883174 775883203
    0x30403050309010804030c02220b040c1b050316030810120809011d1008010504050603070521010f0f0b010f0503010609090504050c041e18020f040507020c03010c030b01020c03 77
    0x4000a0600f540300c3c0102682103842410700c5101c00f0041d9002492601d42d501245103054141164440d10913420b01072080c41100650b001c02484260410041076119a00d5041000e250302480c0081000803c0007110182c000d10b48511018000c1c501d0001d000090039150040300e101d0380100420044a2040e01030015540700c1101c1d807070011f0410055903941608200c66036441007000564245441d861030f8000c0c000c189590741d00040d8140802c000440703101401d11030286d804080c1c1440344d500d9420119224114880c6410002c00e41c0c15442400341c1840c9012454040c201a8404076150303041d004051002400d0700e60312414990200c0840300703400240318040c00101701380c0040100d10483d6005503001405007003620212001d060115043d58045201c1c020101002212000d01750003920400011040902d50b880c62a112a00001d0007651180007142c8601d0380d500107e40018000c00241a52a0010f0001e0094000041c0050001c0c000010110b016002e000040005481c1c04201e11581e003010b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 775885674 1250 775884424 775884427
    0xe030906070b19110909010906030803130819030c111f020c0a0602030705040501110c01050f09060c07180c050306100f02120d15080f0c01033303030305090304030503 73
    0x181c035150701110b000b9144a0f402203640300360501c2002503004031000709004901a507a0780711800213020542a05a111226003480e100040c40002c04201c1100d40100c02c0d048040b0800089003050001441110014110340340e191100314001c9404d07800105001d074854444018820f00000032503140d441d941c914880000803a4504400070b01c2c2c2d94054110603152108803080b00d0307490b5441d00300300ea00588030280862400f1804020a681c410362105140f103504020340701c03000340000060a0341c002c0c800c040b02c0180000c202d81d501c40e00e5420030359441c4070b0b03958100d0f2006540c0f80c40280c0e0158511a0720a006030400e0345900c40d05004030101c9001d2030000c0c1849010b065100c1301200c0c00244c2c1c00e88002180118442c400d0303c203661074042c5c410340204810014007066551607040030280309602903d060341049089901c07081010443c2c4c680301c038080c00d01103003100c040d06a040d880411700f0b031095418400c80700d4203581510005210000c0d6407080e03c08005d06e0b00c82c41c8126581c2c1c059444000d01c0d6500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 775886924 1250 775885674 775885687
    0x103060b10120e0f07140f18160e18070f0c050a0b04080f040608010906150203030403030b130c1701050901030203070320040f0b0321040e2208030a0e030906 69
    0x20b141d01c29000c80300700409840d50b14481c3c052090504420340d02c840b8800110756210a6640f03400c118200c0d401d04110f03403407000800120480c1a5203d00140076161580d000c1c03c107403000034045c09400c003481c50010050178440c0c000000928500e00103454010005101181d00e03000f071f50140320013000f00c0760080b000303150326071040daa07115001d0750081c42112441c80900c40f81420241103070160000c0c0c031268680602640c1442e135217070203c800d20b50106804c8090a00c0b200912500481182c1d0480e800d450045502910b013070110300003009100030084071a04d0880e59240180c0d0000c51600202d01038407084046990310030400a41c54000c1c00007030740c16081400c0400000d060082a0070403801150200c8128050381c900250403181c0203a040c20409407190030310091480c01380f1002600b42c010400354a607040074188808030314007585c004c0c208a05181004250010510031032040c400805040c007038a045064031b444c1180381c00c192501e201c668181000030380000000320035541d42d890080c004504000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 775888174 1250 775886924 775886957
    0x203192f100e1c020a08030c0c1c09030b010e090d08072a03020105090d0e01111006030303230606090f041404210509031c20060103060b10 61
    0x18103030440310315203214990380d101da0100349014006445100c10068010f02115400007200c4200c0700a1140440d080400a08001000355040c0d81e08041c01c640000c2c1c88071401a01070b07140188150360140f143d100c440c00800340b9517004601c0020b480c850800c0625503681d0714524415408244c440180b03541080141f042103500c10701005520407d80c0c40c0070b410304528007400340b20308000c0800d0814086641154041819024050a41c01044030401001001e4151a008007000107481e225810003034118880348c0c030702c0000c205c1d43c6c80055070b0503070401000e5075a150160061000710711884c0101415841081d4042d14841d00a00c1000d0182c1010700d848101e5040250414482952950041d500c0c9a60210790700302a02451203640724240045000305804090769802421400c40742c00c202d010007501b4101e03100400c40d4a02942884403600d00c105010300c0958039030400000c490b0031020611007040c060b09001503594100d078000e140400800c0001414030800d03002d0100054046100314004000d500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 775889424 1250 775888174 775888247
    0x40504050705070c06050904050f070806010503060d08040e04110102120d0f09050307050d02010e070819110607030509040507051216020f0a08070b0f042a0312020319 73
    0xa810b2515914102c510b6440e0b10b500750342e6801c500005180030520700201c0c00c00b0b2050941141800781006250303d004c610043c00800300901c942d04116003c00815030545842c0300a51280d40e01c40c000c0c81d1225201c1000d4070f00107104403001e41e20380c000d1050040407035001080d603200740403200c0710651410302c4000d445406016580890541541d480414001140080c4003074014036119002a14181018078002130039900c8207040c1c2401d540125401300711750840003440044403088100d05540303800c030900302040350549980065810a400107084000c0651100040c2405c50003200c00300702c0c94231140c2c1d085600340a03003500050b480c0c6200e80440c0c035014403400400c04141c46841143d80b2036140038000d03400c00300800c0c0300321aa5500800e5190803c400b120320b00f1b034007202e1034904000354501034071070050440d24807050400c03a0075080d0380c130b184a5480c0d1924601a50700881032220900350040001d41d00e0340428524042007854400e19400140b1039034a85022041c40b0f050488507200d4000b448101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 775890674 1250 775889424 775889431
    0x27150304050723120c0901090203060d02011b051c08010f0f060c050c101d043e070305030106030b030a03055d060d061a120309030c1504050405 63
    0x3c0c4000c0100460195031444c9400030688211400341000d84000c0d805e10a100710182c10004001e070051080040c1910307881748041c14035409180c0394441c035980c00750300040d000148001821a0003503003a224401e000c1d20302401910f4000340d9030190580c3e42c640540c0a400140c1c01248000d0808140c1007105038802e04042410354080c105903807040079400001500300541d4007601012070310a15000c0d03e503072a802160540c605041c3c03003c1c841c2c4250800644164005105020304040054030b82180744920341408003c080f0303088441c1c40e91040b442c2400782054009201b0038000a04060041640e42004640010090f0703041d1070313150619200c05070302e080f9001e06040d02203440000d1501494025900d2151500c80c40c81240400030f1701e140304410034040d03034080c48145912161070050002c151500b40509091a41202c000104101601c40c4550124000d000340c55000350360003d0b0090b80a0084010441841700b00e0803160b40c00200418440071074400032000088138000d2004124a06060b01301651 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 775891924 1250 775890674 775890719
    0x702070312050c0f0709150f1e1809111909020d020915040617010e01120204020f030907080d180b1b0307030906080601140a0c0602271503040507 64
    0x3e0000d0b5250040ca4200100003411182d400030340c042141d0b4855108100f04440602c80c0e4880450500d151900c0030f200078031a036107081d0100703241400620b6072808210050607500b0381c0e08242d00d10b0020740d00c0140801c1d000c2951003c046146004003498003590841069660142d1020742c44c0c03074840120001c2d0002a04030000329000c00140c0c3c1c00e691403e054046106c0f128500c0c03502c440c18400e008011065011090152813141e20040c02410940680241120712034402141118660310118020340181e4042c81c0c06010044140003920001042d1001a41c000004440e02034040d02011030b403400601848801072003241c90b00348803005072003008000d003000480c0f5030300803010b144184518541c0101425800150100800c0c00301540c08107405170001c409190036040c080003107c4c00c156520440c40313030304140880000303c00d080090703503010385403a011030a108210941359207251241c58041805900d204100c10710100003200075000669010320741001c000c0091500749894400d90300c680198108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 775893174 1250 775891924 775891927
    0x1e02010209030d05030f0106300b0a062111120a180f0b0903071a07140c0a1a0c09120a0204020a090e1003030807050d0209041a18070207031205 63
    0x81d06450401007810301c5103007581c500d50b0f00d00d0104400304081c041a0008000c025668208200c0501c00b5251042004205d0700b00c04510815225030b8001800500c00c00b82d00288070b10340c000741803600108500708903c3e4481c800703410180642e00131000c80d58204804041c48000348007413400c0e4040039040b26032015020b00000380701e1488410f445081a401e0f0300440360808000300d442c041109400c211900705d10b9481c025414003505545401005400c0d04216207150321190004001c2d40c81040d08a02c07403034100180030381c0e41c00d80012503a01c55202400035112902c01c03114800c0c2001034180f1003442100ca0f540341d1420010140e04022000200c82030608480c41544d4900c07000d41c1c3c0e00d1004146188c078030f0301d0b0030b07274001d14107040410f51110043c0310000340d4090704400c00120b034101840729803000f00340c40c060f07903640b081540c050004e00134104500c2e0001e00e0440d80c282d50100d081301640b2552811200409450860500900c6c0404101c0d0703a440141c00c40c140402c001550031402c2c20003155942041c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 775894424 1250 775893174 775893187
    0x2030d11101109030706081006080411090108071d0f16050c0f011401060224070c0c0f050301051308180402160c03110a0b0f0a020f060f1f05011e020102 67
    0x15001d031000d464004080b02c4000400b03107018a410007000008000078200300d00c962810400c4008190b00d2071041c1401c0c000d0343d030001001c104904902c400d42c1c0314000c00501c26941c4681d500b0baa034070160b01418000b02c1542503e00040b03ca921003691050790956410f010698403a1920003410b103d2061020512806020a04040f401848612102c03140304d800080c2c002000003560b5403050041e400b20b02075400182003003001001c003804031040003402e4460346403162a01c40c011140048940009413003188680c50100b95030000c0c0d1402d070111182103000780718503110500c0d449181501c6a038014480c5000700072095041141c900c41c3e4407035141c010030060414005900300920882494811981214401000d0040002140341150306a10135a580071081d8105180101c0f10711861071041d100c9100820904941c600c01c000550240d01c00c03c05550407803c100c40200d102c00020340d03c50742c0d446c0f141c1c1d061114880603981180300b100c405940361180c8080b04101400305081c0081d6420840d5000c2021 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 775895674 1250 775894424 775894453
    0x81c050412061e05090a110f0307060302040f08120403030309080405060f210c0901080912070c08060a15090506040e03040602071404020703081f08011a01020c030a02030d11 76
    0xd401c0580185004640425003c2c10b040081641d00345a5015a10b414144030b421080081c8981100d5131000350044580340ba54000303103240003200b05440d0b046c8174802001c10116410740207001150700c00308459170f14036100c1c8903241d200c0c0300c4003038181050203050100b0000300b423003a002075400300d0080f504646400d1321240403a02139803010280c0c1c640e5580c0002d50040645244400d006900280b00041c0481e08100b11180110311541c206a81041000004a01c40c62800d1024180703600019001555610743d40c40d144448640e1482044098040e190009002c24072038098000030981030120314032102d061036000c238010803026110603081552a03403069070f007010810042004d0015900100b0080780352580100c1e003001e4800b0700d9401180103111030000290402d05540d0040710800400f8064450302c41d00d104030311215800024550f00b0701481000e0b0b40c08129941082c45030030380c20b0326484081a0103059440854000094069202c00b8481e081d0a10401050f10b4004022094600c0340107070121 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 775896924 1250 775895674 775895699
    0x10809010c2102040e1e090c090a1e09030201050f071b121b03080619030f02010f12050106030911010320180a0b040609051212030408041203080f0907081c0504 70
    0x6503036440d107503a00c043e880c1c01b400c6041265400b10100004221207644100402c500c02c0c0301074400048035450304d4006038024900c0410400041c4001c004000c4030085050080c061320341910111000d451400c00309440f03a200e40e0300c9100c8000350403031349181c0b40302e00c1c2c0c2c508070311500b02c0c3c1610003040b4201142031040b0f1010b602c542803103030003030390350f071454ac00d00c0340420060030441120f8000300c111001c010030001c0d01c9030031080c0030f0640902b0315643d1903410303400644030204010212801c03140f0700800420303590707050b91110017451b00a5650908440301c18006400b00c90010b50015030410400325202100c9141c14020843c9924843c81510b07640300314000b0910342140c40e0454204041e0105041c00142e03800940c160003440c084840041001c070000e07031140c03a0314980e012015000d40000c0018240150a800c44000340016081c0c00c212810b1410300500c06802034904a102c00b0349000810341d117030000100700d800d9850000150102c2c580d40580d009115894202c41d10a00c281840006045100c40c04c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 775898174 1250 775896924 775896931
    0x40c0605072d150e0c060c1e07051309030201050105060a121d070806010e0901110a0f030b060417060c040609060e03070312020303091002070b0f090a0c090b010809010c2102040e 78
    0x2802140c007035912480b16082c8504a002c0764005c1e1b10903c81425030290010302d10350f400d451585c00d010100301036180c0d00c1c2051240d0b00150f802910f90709540b0491504c0c0c0c0c0c040c20001e8001d500030041070342c8800402020b8840c440030600011140d01c080c1d540340c811640104072080e65076140c0d41940440600e55402e00d20309078000a000d07040f11004110444002d1405544241000020031008010a0301000c460060818413007c01c2042d05e00841414042c0d03007c090a218001d00c0c035a100e542e6141080b0750b01c00a03c2038403485000304000701d40d18032580350658064454075100d01c42060700f0041708607401c0e01d00d4446c0b0307031b8540b1503d080003000c15251441800d900869502941d42d034605a050540b41c000b100050044580c8108841401320740c12001064000c1000130b90101c071a101d03915100d00e003964409024107107011010303000a0442242d806405058420f80352001c25a035407142107800c90380e000c0525800b1134026040303601d1004030218110790b0030314024030040c00c0948500e0f0740da01d80c01080f0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775899280 1106 775898174 775898213
    0x10503040b0a060b0412031808030d020c240103030807050304110409021305070810050d0f060c02030717091807021b01170a05040c0605072d 62
    0x2a000400100312100780d04e9100d80c0c8030454004071010441080300410608400c0c1c1070068038040c1c1d940308480f80400954184104d801c0300780d002c0c0d4802c1c8d0001005d80107508180740c000c110f030065854407881094807840e00d58103501d0094401c48000e00004c00380721061003004002106c0f5a05243d514000b036502040841d501e1010580705412902c2071625136060900304001542d00042c0c6038420341c0300d400d9114080341d40d081400071242e6581400f4106881d2064400c02250207500250205082441200d02d0020300e03454001340704220b510941010100043c2c10300c82454800c100f10704c004c440e4064000304e8204401c029640303004075982c01340920340410f0501da0380d03030140c03114200e402c44d00f182c020b50900d0702d00741410041000325422580301000000200b01607100301b0030b03249450703404503000c0328000d821034400c0c5011001030164403000c01c0f100c4070600001e402c040c80724010b047c1d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 775719424 775899280 := by
  have h0 := BRFrame.cov_init 775719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775719424 ≤ n) (h2 : n < 775899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
