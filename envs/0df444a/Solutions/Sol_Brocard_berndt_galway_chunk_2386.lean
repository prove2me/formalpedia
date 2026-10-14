-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:33:47.699374+00:00
-- url     : https://prove2.me/submissions/06ea6fa9-5aa5-4c4c-ac62-8e6a00f667b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 428956834 ≤ n < 429136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 428958084 1250 428956834 428956849
    0xc0405011707110709020405180f1503070b16030207090c05031602160305011b0c081803030d090614011e0b030603010204030c08060708070801030503040603090314070f111806 77
    0x541014000500840203403a4010420720001d401d417440c0050340d40d400c1c00c1c1088030203d94042003101c01c9810300d041241c000070341c540c3c47e030700096110032680e004103110002900b00f2040d41c02034105810049903820b001c86668401103a41c0d0701175020f4507040ca85421251080c1c80c0e140715624081281040451008104610354161a80061040d292442600b003d04142e06401e42c0c42902e107a074503008084072134016155500c0d62180c00782032034003a20701c107503441103554042c004881c02c0d0203060180c040c0454800384201d501400e00e69204002e07425091030160018000c685144400d100d03003800106a8150310950340c440320f0b4003805c0b40264546024004007072584003c00b8950155002d2000200080304400703441d0141c100640076011510381741da40184401001000d50080000c04401000858800301c102c1e400d881c42854046240200b908080d91010280c04089043c0c450001c2c0b2441806590241074048511074280b4400c2c400c0140100542143c0c184481c040c41c0f400c072000306180c0d00c1c0185 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 428959334 1250 428958084 428958091
    0xe0103060302030f0a171204020f2202070605070e03100c0306050a17010b0307060507030503130f0f03081803091207030506070f0212130303080a0b130605090c04050117 74
    0x94041045a100d90100b030030400310b03004042e8158400003800042000c0740c00502c0d000207500521342d00b00042902d41c203540361009440a0f002d143c19803401d40d0a512150041000e1001164100714850701803140c8034000d6010002c15541d040c9088040381440e0701c41c6403088182d0400038020100320309104c0001c0000c003c0d641081003459550400040e080d10340380c2a000c010422039019002c100d0a8800c0b903400c0d00c0d00d10301c0701440b940007040244000c681010070340300840e40500e04152681d03100b0200d05446c1e0b01c040b07400341191101000740340400030b0f5401004600e610070b540d0100c26458080e44094413803180080c00d581a001400f117500c41c1d0030b003400440e80b080070503004c442500d5900d85034241883e0090b1407000020718200c9000310503540400030544444020914a0701d800c0209800d918200340c03600004041000703a401240c11506260405079002c2c074000c00800d001c12071030310080001d2070f0f0740c4601030081e00407034009404825601d0988003265810303100d0b00e5020540018082076020300a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 428960584 1250 428959334 428959337
    0x702071422061809211707031401030c06020f06012102150f0a09060c030804080f07061a040b1215130506040506060a0803030411040f0b030f01020a14030709060e01 72
    0x450002400b0f403d030b098201d01c101c0803100d00040004643c04c01d061001604400202490540b040360024654403481310503006405070079078242038446ca803040f40901810f2003604140700316000003001b446120280b040485110703800310f40200d0800d400881d2640000d03c982c50700301c1111010301c0c007118030307070743d911043c00348010925100c034080030344110545d81150028240400000c01c04240b066080890038018117414100500d00461640c5e00802c0301500501c01072600ca40491300c2090300c02c0d0041070701c5826034090b00500180c4032201440e503003c1d00d0703078100e10311403814a01640901c0c00c3c00b011005088458402034004082c0c1c2d0200140750b680b01614243c841c101c101d9002c001314009201d098091489200079103b64142081002502c0059800003490b0350820001c3c0800140040340e507460f41030f800c0d5808200030075202d40840050160170102a0076000b090301d400003941040d07004003540e02c1c0c3c44e146c00b4080103c00c800742c410740c00112001c9011420304c250601849011303001d80c0e9040c4105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 428961834 1250 428960584 428960591
    0x23010509180a0506030d0c170d0b10110606060703050405060906070818030d3209030109060b0306090c09010902090d02100507050624090c04030503040e0702071422 72
    0x11421400c0c066100300d402c1c1a10036590ba050001d0345c03609008030b180c1d06a00f45001caa1990035911900000090072031742c0d180d110400900071a0700602904403d0f004400240b1003140c1980f5000e01500d001700700c46070945c0b94010300b00060358611307044d001e5500c10380d0540c0c3c0d020708060070b05051249503409503545580c0f028060041e080011300300c00003040007518500c080c40180c560001410305c1d040c5000d44050511a070340421160050250a9a441c04000e11148000820300f0354210050341c810b0340c50a58155082801c03240a001003600b1059803004140c0c00c4408a98414000f252208607031b10b01e40d6402a242001044050f00540141258001c01001c0304814003081e400200840d070384035a0b03500851700124119042c0082844041d0340300c0c0e60b45040041d029920101a01d4540561000078424810301300805d521005103800d4402031903100089a680e83d440310baa078004070004851b000e0040c03080c0600841c07070319810028071004042c050040210b60040f82c81c4c02001d00003034401d40c03c98995 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 428963084 1250 428961834 428961859
    0x70b070b0405150405160b27010e040c050a0206010803040e19180303060602061008100915020a090825060305070507021e0a080606030309090c07121823010509 70
    0x20318100d0134000d61180e0004d218403040c410100d00c942c00203501400b03014400384000384229211900d10220000c40c400c064a03105140c0005035864007003515180c2c0c0052424070b6a20710580c208005000d9845682c01325070f150380ea140070751662803007a0b00440e0000804070000c600b540740c0c1c8000401c03c0d01c440143c045002400ea842c4400000b80c45841030700080d403502c9040090316010302ca229000718260700b0b0b008500f4180744690f03581e0ba000a2220b09415034072240381c020f00203c1d100301d61015114620035540e80240c1240208651998001c81a05004000c4030440500d686d0048070f005080c060b608022192400c40c058008283c001c00140a0080401420307005941c0c03001100802d0388031030381c00c010003800a001d0206070030190700b103041c580e4440c2d0144207640d03400101baa001104200c0d812103c0da41c0d1203082350950b004400c00200f41030404076855101c1703500036141c064600803144011842c0ca42d40e641030b100b21103108041c0c441c00c074881480a2101c1d4807610082203641c070003510b1640d0401c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 428964334 1250 428963084 428963113
    0x31119110307050f211e0304030c060e150c03040f03050c04060e040f110a050414011802040308040b0310050d030c021507021c06061503020d06120305161a09060402040e070b070b0405 80
    0x81b24410342c070b0b145402c005001e20410030440d070414040e000c180361a0440c618500c0100b55113404103103003c0c04a010200303034032200b4401042260080e00e0310070940b140c000c1d900d01e40303190380d0054544000d12482c142300000c1900178148030418421600044100b00a18040d00e510088110488603a5000064910042582e03243c500944030781c000ba09400b200f80350715260340e25954068034500400c04500400c402c2020407601020b44050799503241c8820b50320f80b03400b03248025001e001e511035500300d540180400181604000d9880005000340c0750142d004003100c04c40c20a6100d04080207500500d10442100c08407541d03c40454030038480c0c000000e149484a181c01c07030b08c10340452b007440000c1d0002220f00c0700344003500a130802414140c1126030b440300503940183c0203000c1c003000c5840850382c044500082c0840381034040710380f0407080507280103820403c11030340d103903001268181c0c095400e1400240c140e000015190084900129116050815542d43e1485809014000b42c52501c544180c00038680b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 428965584 1250 428964334 428964373
    0x30503040609030c021f02010e06012702040503010c0203071e0213050a110408070623041502101503031e0f0c03050405040c08010315060b07031119110307050f21 71
    0x120340c040c0001c004100ca100282550310b1800f101c040ad8120400401c000120f02c10080b120000c04e002030300c4c2c0310029a9280009001c0c60b8070059040d03003800d5540718400e4010000b0400217020f0070444400040503190181101c403081c078001d410204507204903200101030307408950002185000818103800010100c0441d402c107030450000707a0002e080402006401041501051145035007900c00000300c000f40c5203050056114848a0300074003119040d51601c02e2206259040b414902000300e02d00d007941414107c69540412004075000305101441841c960005807135903140c8e035a40020a0301a19030841d071360711040c05d0441c11b01105202c0414a591140908500c0410729580c3d09076540c50345c10650400c044021400350301d185003003402d0003012340030400c441d4005d0701030500d1560001c8a24502d440d0034051405010110b607010181002c10004070b01031403a503c0e04504403a92603403140104000c2480036516141cbc0014041d501040804010a200d0b49504026040e070b014000103181c450380a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 428966834 1250 428965584 428965609
    0xd05130f080a020d020c060a030c05040305010213170a020d03050906040f090230040f020105070b070309020a060215190908030a140106080c2710200604030503040609030c02 76
    0x41000102c0c9006600d0303030400c0b0031159149544010503848140c02c0204005100e0303003243d80205a01c0300005010341d070003401141c0080d580000219034921004040400384a0707240100c40d10000f96000030414900009401103000b03400801e1300101907074a5505031450f41c001401250048801d000005031240c4541241d0024192040c1c003507a070b240d49007513500d4a031a600c41020f80d0b410800c503820100542048003182d001d9841074128040e83e405000603142d600607100000d001103030b460304100c03d06c0e9041c1c200c01c078103034403c2da070083c3e00e00c1d2070700e0341680c84030f0403103e448400541e6507000031054180020642d51001c48403600003000c0780320f03071118a4030381d01c11960115001c2d100c2281018640c0a0024a401007074686800422030900c01d49044051161002c0000283c002e00000d10200c1c080341003920f80318800a204440300345030440054400241448004002d907030421341403001e054049861482103606903507162466860780c4d43c4600500302e000d41a030410103c101200016110405414071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 428968084 1250 428966834 428966843
    0x604061706012607030305090103090b040614070206012904030b0103051f110406051b07060f0801080d02070302060a0e04110d0c020106051309110901092a050d05130f 73
    0x1600d605207920f505a640500c002001040e0b00c6a5041c5210000810318006980d807601d00181c0d11240c1d000121301030851004041e08a001c04020300080244030fa0100503c003034001c441c0b41d0290f480c08000c1c2d803500402d202d0759a0000583c200c0d0216180c0072400390100c5403800900d1801d00d512503c03031000701d5909030002c5031280d00020301c03180f070303d4001d000d038008900240c0d40034445525140400301c4180100d00c24031050003000301c3c10288a41c1da03024984bd001c20180e00b00e40d4281c0e070b580c81c02084003401c50003074004904940008100c158002c6a034000c04901da0b001842d0041c6103500b4003110740c4c00003003400100006007015007125501c0c0c0c085d40c5401100312050540b03686600780701c0700c110f9181d020110196850b00ca010405511285240710702c2135064100029409018100600c0201c41781903003960010103007001080c03d202582c07100d81c1c9015048c200c1003410a050851144149901c0611004540240441d03544a0f000b0f4001c141c0c0075015080c1e825065030145e5074800114589101120b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 428969334 1250 428968084 428968093
    0x16090e010e010e1506041a160c090c0305010f0501080c1308030712050901090504021c1103090f0d050d0218030a150f1a151b0703060b01090501051206040617 69
    0x10101c3d0707050f840f058001c1044d582030403041403000006590352081d0700c101340710500d80c5c61211342c002d1550410380d048822000510104010149031140007065079004038200700341303000070103802948a403107081c3c140e4015907449a44242040015610480014044010060200161500030950000c10401048003030000e545404440c94109072000803601070100300501440000c01581c0c1c000910700444a0540d00180e40d420710001c00001c4882c1c040c540b00c202803d110303146001418800086228034104001e0f03c03000c11350403d5594985019404540c00207105005100c40070009d940103164202d1001c038001002916100801e0406d00c42d242c0540e00c3d504034003200103200600307004002c6542040d10041005000d08551101d0755404110401c1c0a01199001c0840c45500e281c01c0f02c5410260284804109400d40c441a64429040c0412200700d130402201500a5020300b00d8407094850586035182004400a840d42c80048002c005941c4503407503034000504980780141484044d61680041e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 428970584 1250 428969334 428969339
    0xf04020402190903031e1209050f0f030405041107020108040b06040f05041b0b090303040303030e0106030804170c0303030f06040903140a030905070e041e0305070b0a02040503010509010509030316090e010e01 91
    0x1c0c0031040d6441501d0100d01212890b541301030307031008440300404c201040c0083c8c20b1400d4145586000b1440980100d20310901031900c00d4000c000010b00101c0e40101e0b000d100d00241702802e0120380c06003080080c00701c0d91032000f1800154a030307041c040d80541d000e8000503e0038107208014042d039400340d605842e0302982e8940448205030004000020b0000c15403d40c0ca00440c4501080d0b69200300d07c4083c08259036001040082c10003034200034010354200b04000d40b915156007007500141781035581c1c551148a5810810b80c141800b0058038440c2c00c1804540d43c050b0b844005003c05450995011820030008180001d480d000d000058010100756581c000b40290b078078036009103002d419402c4130259224900811002a403040c200c906024032560450141c0340342454107560501440100800000480701040132003c8980e000d001240c00c02c5000748056101c0c2c4642500b01c402c01c0d13034014506d40041002138401e0520880003641031444e494040e000c16500c0d0400c1748250070a8004804884590004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 428971834 1250 428970584 428970587
    0x51803150a0b120d1835190303020c0129030712020306060409151113060503040f0209060d1b050306010617460f02040e0f0402040219090303 62
    0x2d0040c098801d0750b16031022400c3c0b5909a5680000b0000041081001181c1e030740704004442c0e20000604500019800707109401c0c000c50400000d55448440503074814200400e00440000e2208001c00d0740490495400100e4600700c01a52002e6280700c165921040c0800d03926084030701c460450f8101551025407078229008241c106041a840304202c9480c200301c0c4005640d002c52040d030403000c111800180301c10f40c2e29207081c070700d10111a05104c05190402058804013007800a003000d000c280000d002041e100d41041d2005e0001791000b61042036003285000c01401e1484c0741c0ea8205030700401b00988101290b5415613420620a4042c9008544010801503410208846400740c5114244070aa11200b82a840210803004220707041100c0c0044070301c0181450083d51680c500c50940c20082a11041e92038042218104126440c44c145445c450110201140c070070361302554003038210b031304103600e90188101050501400a990195081004004901d102a45001c81200c1d40e220041c4251850a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 428973084 1250 428971834 428971841
    0xc0203030307124a06040b04120f0c020f010504080a0807050f060603030703080403090b12040c29030c0f030f0106030506030102030411120c0301020c010212090706020d051803150a 79
    0x284140c0c0b001440d0740340f0030341c40000d00b4641001108641c8810035004603440c5500c0c204d1840d14000d0942c0602d030240021b000c005092548070b01d005100390150620496030031501348000d5614240010203a50601c3c0041c500105002e080c00c4c0140b402074203182e1244049414850a21011115040002011030400000340b02c003610f14280e42002e0321803840c010700030985900c0340d04002410403100700d00042c1054060944080a02144043c458940c5092901e400d40e000c0300343c4050b03802031f11141c800200f8080180c00c0c0e0450140c02c50040c103440a844418808982001e0080f160541081c04a0381c400b00030311000d90300c1032603515002d00340c551500c01c1c00780031940c01909403402a401041004046a0f05601610742200e0584094182500b10066681800000c805643c1e040d400022224007805054002d040701004013207450a02da00c0d1203045690b1420742e40314079401758005011404031140a1409007580c001c90850707035034189405100080c1131a41c0c400c400020403491009209d0710041510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 428974334 1250 428973084 428973101
    0x402040e1e010f0207030903020d060207060504240b03070605070c050913120203091f05090301050907050f01212c100c0521090f0307060e0d1d0405070c020303030712 73
    0x2d0f0110728240c41ca840c0100601c2c0140400f80c01401380030150410172216504130b80d00b6030703000b41c400c0000741403619100000042d03100304010b07034440c0d656940e40403501a200e4031001e400b000300140f5469180c41c10584064200640a42d0400c400700070029a03500c3d1a03449911407041d0413002c40ba54840f600e0201001e118001c0004119882400b208645440e0704004899940d08007503040003d00c1076000450f60792203040001d9815500700400c0c40181c0400098000035a0411116280c00c44901c000454015080303000360405003000c00c24141c0408c24580c044664a805443c0010740555004442d500000d1000500f00d2664031104041020aa040c82401c440385980c0c43c1403454402e5406003c0c400310030300400c900841000c40042a0f0004081105c0c1418440d100d0a0ba074031800340b401c01e5401424661201e80c0e090180d18101d540c8184911051120440c8000c0303da5a80c202314070070b200007440c1c010050420301079100410303405660108051413107001c903552032092119008000005890305035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 428975584 1250 428974334 428974361
    0x6160b06041b0507030c0227010e090d050906031312050a03050a02070203150a060f0306050f011e060e0604050d0b09120a05070303090804050d050607110c10080402040e1e01 76
    0x44108408443d4070000f11904141c0514015070014054000503807040c104602e458a42520303048201a04000820514100c440760081c00300709658100c5401d4403204001e000340b0000c1c1040155107103e103040005181c0005100d11200f00080c0b03e995050707103007500302c0101c1c0086800801e444000c0c0794103000303099000030503800075824a0a0303079022071b54528880020140508181c0006a111a41a8081801070407a000c1d0003842c180c0d281444001800c055036a1541c02e810a40081605200b0050f21402c1c00e20142c08036101a00d0b109007201e07603807075200c40035601c444204030014841d5070701040c0c0030320b6901807410007188e41003807440030b490900c2c82d031906610403500f44451680150880d0a607103c60380c1609000c07460700200d1924080c0e81c03103150405a413040c2c126240c181031220005600388551810707154444040302c21510b4076070b00e00700c68000c642e00c034031204080e0703551902c148c48450b00a8030152000c95041081c81183e810510804c0c54094911207280c03e481d41c2c81c030240209001c24505 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 428976834 1250 428975584 428975621
    0xc070b070c11090403030b04060909050c060f03010e090f0303040c0806070804120e0103020f12010305070609262410052704021c03090905010e131106160b0604 70
    0x2e60340c1c400302c01c1c0a1038107075208022031000141414026009042c140200800130040720351160179040050072a01c1040c1c0d5103108041004c0b0150410340100e51406002100d40c4d030031a07281a100c0b0a07140002043e48006000341290008604d0040010b507008921441c08902c110342400d803041d00c1c021008010300c04000701203042c00041180804c4451b002c001d40d00c0c081402052420069001e0300c40c6605080d01590300140d20401c030160004010f05a034850400d4888030f82d80d031801101ca400286c000c980150607010a0a2a540d05c4140c0400c4105100c0080d902425080080d003100e40e42d40010b0041c5841c413501c20410940c08249520300a08400c039006000c2e0b8071041c000d01820313546540f003c203540d40781c03c0c0800c003550b51b01d030054849401c1c2d81540c1b40701c2da409494010049040342c80340682d01424513002140345441440582d00c21402d1010780550b0340b0464651186000800c440da80c0c0228003045035140e90030034038900d400c50600070b07000f924590416a0500048840365444c0c002c0c00085d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 428978084 1250 428976834 428976857
    0xb041505031509150d060507140f0f0703200c0f01021f18230705040207051f060815040b0609071e090906090509010b0103060b070b040f0b0c070b07 65
    0x52940d541c02c01e004241c8003405550380b900a201400101c0b400e40700d41c00300360381000b10b0400c902a001107214100d166144110183e0080c419911402100240084084240000e1001030051805012100c0c001d00e002320034400d46010b4007407481c042003d49213a94001d4000d0170098140391401d0b5003440320030310042250407a2040020b88645403003038581d500c181c641044541c0d44640580e081942c98112120507041001c2803044500c00803500c20155090003030003400103040c5010b03c00d4400b02d0760060094000600341c241c0089600842d0550316102d159900c0b400300c0c24a03c200903081303000c01840a0340d09681418200740d407817003c00800741c134801c0c44200200816594810300e00051042c189496030b5180c0d610b18020343d440c40c5a40c000f03012061410200007a0341071781e17820142c068452000200400f0300500d0044099030501d00403510010001c0100c0700010700e41c6209180d000d4050707000c00d45d4454079651001e09884040c0e0b00e8480c000000300300b00050042190000c1d8001c0b04c0d0b410300c07a00c1801c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 428979334 1250 428978084 428978101
    0xa06050a0810091b092a05091c0203010c0f020610030c090c11120901080a06050a0b0d140403031d011517070f0f050a0807030506040308091501031b0e061c0f06060b04150503 76
    0x415039160900070015842c1319400001c2115491027602d0b4000e0003400480c121100040c9a4248010711000511400e0003140354041180c10342d00a40b034104854680c0c8038180030940d40900b044402e84410850000c14144014800713004203184221041105a03492541200040503c4800392243e500d080c038066003000140e0740c0c5880513045481340a03240d41c440317441d99400c81c0140040180105540410b80812040543c143d01500072082c101c0310b20140f203440580c041d1708a40c00136100001d0b84c0d8844400740300c01c4441c41081500343c5500700489604075150007070803401d4085a40008940e145040e010700c01490800c2d40a0045c10200008140052458031929038600c005040a810700c81d0801c00304140b900180700300e40003180052541451542d40c1c1c42d0090a0081a128280f043c0c0e6200d903020a034500c004480500941d401003001903003070690b40400e076102100c01000c68000989544013000910b16019500c0184148100c26440750302d0b111520456013241802d003000c014081041182c00c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 428980584 1250 428979334 428979337
    0xf17091b01140d0e070314060106031404020906040e070909050705011421070e060c060708131a1008060a02130605040b0d0b030f03040e0a06050a0810091b092a05 71
    0x1c14002c50100300411520301c00b45c00d1a01d00c0c0c00141010b1006041d9a030080c1001880c0c504803101654100450101c10000728921041500c000354804a01c10101c0c405241070741001003152900816600b4155860007030720101c0e20589802c9440ea0080d8104011540e0803c0e11501d07403d0118100c103181c400d2b5140e101c0d10b5000401400c910f41c0346000c000c074008501c1350038a115850b20240045030354843c04034095541d00e10494564000905140014400e0180003061664180e4801d17404401032103084010000c030f40700184900e52200002c607001031320810800c8818001c084125005a54807421110740d500c01803a50008000d00c00200070400824101104440c488402d4030300c0002e0001045000a06120b040a02c246e445d00c00860080303940c1200c0c1100500885c000c00c1e080006a5481d418096100307aa842407a44a2b04403401c480d5540c0031603000f14011501c01e0020f074510611076a07a86040003095000f45c440c00b581c3c1c004801c2c0c0950050b0422080312400c6a42030415604081d004049 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 428981834 1250 428980584 428980597
    0x2060a0c0908120f0f12061306120f060b181602010212060d0f060e010f06050405091507030e1c11010e1b060904060306150e07050a0f17091b0114 64
    0x110301d0700103040c4c042e0034444021354410f410414240d03903480b10340c1c41b50200469002d450706841030207040d07030055901005110b80d0b0100c480403c08560300c110951a030304a5081e02c140252005a1a14050841e990f10002080041304400c8440807a504011185d0341d0300000c0046560290382c410410300041c500c13030740070340380e40044100c8840394601014a0300100f03c01001e03400400043c142441898000700c103401c050036041c00c140003009043d6540007004281d980540b007005450f008801034207001840e0b5401150b204150b0705012a115054085a920f498190090341c43d85044a50940e608940e100726940721201040c00240400e00d034810410342c8071124041c1d500c220004085620100ba1100c200340c882039040100200009952803c016001c0c1c01d184d03556000744c0c29103040c04201305924040090150007da614a400d003441440269542c0a00c026a2410300102e48815000c00c20058401c40c454052140034094811503445113400c206007100d01d003814020304c00220900304407400262543d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 428983084 1250 428981834 428981863
    0x608060f041805100b120c0f010305040309030507060203120609071403061201060e0402030d02060405060a1109060a0c0219030812072102040f050a03020609091b070302060a0c0908 79
    0x210440c2e500340880707201c1c0950000070f2050050008036401c034203042c0d1021002da403058076000401d0003040d030840c3c0c840703640140c05039204603d00c691070f04652080e0700599015100703040488605840340c0302c030f034a0419182c3c8a800140d03c005203000410004051683e0000d0050781c201aa6003002c0201030a442ca050b200e00584410210004030a981c1d11201c541c1000903203002040340356100d020310840200119005d07030103031190480441000c1d10000d500c82c03259410201800c0140c899907002005004d45d83e4909000301c405004034039581d6690320090030045a59120360842c2c807040c2c8180090f40d8461b64045401160110080000c10420350485000a03080348820025a451880650b441005002201c4000c060341407107084001c056802401a01c1441c0d500c0c503007059480c0100151262203000083d0880b0040c402c6501c0c904011410a8002844003c400c40e08031844019032496044070b0020380050b84258117006c0700024911400b08003408928184500714180039a10380d0b107841ca04e0070200c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 428984334 1250 428983084 428983091
    0x100509121201180603020f0f03120a020a05070515030112060f2904021804020d021905070b010803040f06030e0c190f09090302120714030a090602012405060918010e010f0608060f04 79
    0x51954148040303c204ac110404041d11644035280083d91780c2080b46040f1303098886c004020640745440304d11140c01145038407942d45944c0c06e00c0141d0f207058001e13403c12201182c540358030314250100380c05a4029411280b812684500c05111890f401c5201070070303054012417041080c101c4052070420b281030603100507100035a6606001d0700030b030000d11030401c41140d005141003101c400341c2e0307101e80280300960165406510a90301d52480b59203c0c4114400d49403598103201040040c14020b821685100440038262844401090701060b00e8843c01003641800403c0c0d180c00744a401e05080b6000301520040c40100405400d82c1d4010350b403007030601c00d424944500070a01e0340400403001141c483e008000300076251a40300500b80600031036494010840075501b4103450440c40a00d100059405200a03104090001e20f0f0109115591344010002ca8100302a100c3d9031509a402d2407501d4002e0030009004403007507150640c410003000701500b29100b000244c00a028844e030300e511681c0c086660884001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 428985584 1250 428984334 428984359
    0x30206070e22020405100302031608070210050708100807050a030b130501090501090218070905040507050c0703050a12020d05120a0905010c020606031608100509121201180603020f 79
    0x96410040340070342041031101c002103988986194001d4000c030340c0c5c241c80d406018400e00740154280d000072500380400e0500240d41c8003220b4400c1c9500c6030004051f0055540303080c1703612440380c151202100c0c2040490f0000d0284000004a19505002480400080c0003cae50030000041c002c0e20385031001904000c13505011554005e050b0b80c240c07088a034080020080040c1c24904a030281c50915400c4e44190400350b034403410565500704040c03180360165a030324038441c10582000004c10025107103204008046c002e010818004001c10006503000c2c000400328000c56240c07041c80c04032504a80003c64000410380302c01c054014068555034043d458440283d035461040280c0140800d000c0074120358240b000c2e1010f2550041130150103000150103903010b1105030102003481d4084c2d44240509540180b4569070340681da0792001d60000460800e4038415103121604060036082080140603144480c0010420300358001000e1040c413000c0c0c50203204a83c90754000809400c0364010890190b140349030304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 428986834 1250 428985584 428985589
    0x12100c0302160312051e040b071e0801030212301303031d091e0405210406081513050406060e180606030309060a11100c03021213030206070e 62
    0x1038803240e842c01d00801c1c51072240c07030038001c02c3c42201a851021651030480810501c1c62084a01039030441040b0b107018842e01d0300d650b010252075004222404020100c25541c001e500d40c0d18150300e40111640e01d10303480b941140104410707a136078800e1800c0540c1c000080b00004d0008202e074541403103203c914811215041d107408035100e1081050750341c010807410001008064121042803010100c41f00e81b845070140700e1007400402141658083c031000050000b0646035035801055680c003900c500140d0b000356200040d000040003c0030049d0070f030480049024081c02d40d1008400740e00c4540b000c81d000c258003084010404140300701c01e01900302601c03140000e05002c000d800c104000d001d1260b0750300b06450b00c542e090140c0c0c906800d45405a0045501088181c500001512206013004088a142c1802150706403840e902140f56a08103004030100810b400400e0721400c40b0984440e240580d03100f101c0070180d10740745401041244030f003c6001c0e17220040381d030001c0c10740d0744050310741480850f03500280300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 428988084 1250 428986834 428986837
    0x301120b090a06020f0d0e06100b07060905010612051c0c060504082b15030b1303021504060f060501081614090307170724030903050702180103020108010512100c0302 73
    0x2000d00304900000d05c410782c03003000c2001880c41c810920401c000d15075010800a440750300640301401690080d031814806001c04c03000070500e0f58031542d4006031000d00d030b0340c41500f0744019038000b400e84c458002004c0140402885440a5140c07200361a40c0e02031003854001d016800400c80c003410855480d800101045811000c680120b1040c080b800e03402e4600309155685100c200c5079140015081007550050200d10030300da10292580301b201d9154503518080703a242a0200c21400303038214030410907040090000c019105018034020032010403003c070381403401410340380c0b140d10060400400034100301d1030300f280c045d0480d6103000a242180390141c05103681d13442406000700440e410f02501c603000400c8203000340300090005010090b141040d035681e40c0b8440c819028026501014042589038002c2d610030303842203403580e00c0790401504000e155008201c00030030745049140050f00c1c030030060080d076810080113030040404407541240341100f628a5074a8044480c0c1074480d40340c48151300c143c000e00940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 428989334 1250 428988084 428988103
    0xf06040b0a091407420306120b0a0515090604050601090506040e100b0a1b150203010801020a140f040302040915020c071e0e060918071401030e030301120b09 69
    0x89090100300f1441d00580c4800c0284981951004c100000d1401500007048900d809009845000120540341c0b8001c904030064541e44ca00709565004089000200400d88a10702d038001c001d411014074100410008944014290080645c28492104405d40c1e03030f40411613000301d040e6800b15040e12800e005030384000c55604407039440790340403401107500b000c98400e60b84240c90140110184555448102d016441000100c1d0001144000403a45c10b00c2e03807421517040c042c400c07440d0a00701001450300c942280c00c280c0098a46940004900380c58a501084d201074514110441501d084400601040f0910652000902668a5010410500619010014112648000640d95541c052a01e90f4940d10300c1d0007007580754080e020300650560010308003401650080103001c080c94032a00e040000400e001054072000e1040c45000500032001030103900002e01c2180e0355042849642400541600e03e021b00a1909078414030041110500001c0d9024070035400600c1a084d5490b1010742506141004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 428990584 1250 428989334 428989343
    0xb0301090b0106210e03040b1305040f0e0d0216171e06072607110f0d0302041a0705060601050f2106180f1f03150c110f06040b0a09 58
    0x800007450b070380c01410226651071102c00e1520054180340000b8105c914021040c10103500511040c00420030400c0106401c1e410400c00f41c031000c0c0d81c0c000050a440001000945840d1603d200009088042150100844040c000b40c007400c5280c0c86d040d00400036920940c804500001906881e62405000d252001c40010440b100741c0742803071044035901c0c1401d542c041d0000c0d80d100d82a051041d0341054801c504518013072080d90300c2c3c80340f060844003006103000111203401002c00e0084088010003070049004c106440140e1039600d041a80c0c4260101c1408031a1901c200b000004000341011981642c0301d00f090815035200c511902030301040380500c5666110b4100c0400740350442c52800d6035000c1c03041d04112240c651040080b041e1403008d401c15035000c0804080c100c040b800d02c1c40d904220041001e0380e000c03401803140d52611001030410242c0310f4500c02d55580c980682001d68468083c0020042c054010003001807006c2c1c45640d00c1074000d2000c1d00d4000e07400c0c04100b1a0702c06402c00390555810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 428991834 1250 428990584 428990603
    0x90d0f050d1404050606100f0804020111060406060e0a09020102031b070506030a0e071a070b1b07080309010f02160809011b060b090603010c3501170c090c0d0b030109 73
    0x1822803058002c0242c406580900c106400260b062400024101d4a024aa40d400c0d4000e070310310005071105400540300f01e040c03050110311030542d06010400188198050140800d0651400002080400c4040c1c0b100504a09102d49070000d40d8000003200c007401c600e119001c40c1011588102402d10140d0f80200d94840c40000500001261030f4004462030f0380b54405030b0b03240c59500c0422100c90703900540e861038030308014413103000812003030705901d94084040d030030702101c142c0b8100301925950b008031000c03114000302000f40801d40b0000d10031540010074010003140b5007040301c1c5400180207a030308402400001c000170b000403580d05c51401040032030f003110810200c01c55285002400391100d402d615002d0501c442c00a500c1c0d2905011700c40745081035072035080140e0b010951490101c00d030709040c01c820134921100468000918130041d80204105810410036403100215203051070040450340c5e00c6064031170107101039214a0b1046a140e4012603200042103040c44002c2805090442030180903400d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 428993084 1250 428991834 428991851
    0x32d09011202160f110409031202030601120c0504060e090402060f0309070503150129031303020109020d060c0f03090b060607061401060206070e0402180411130b0a0906020303090d0f050d 82
    0x10080c84211a45c4269101d0291042282c1444200c49003004081c000918910614404083d113600441c0c0000c1d041c500441d80d121868025815a401000d4400c0042c038002810400150711036803403a414403013224401c0300c906003900090400c0c010043c0c60010040004080740840104020303000c000c0c81c018090700c00f01d0075000e212000b03001c402d01c0b1b0000728590301280001d1a4411880c0040001c43c0b0060460964407502100d85950000c40c00441c20b5650382c69161000d0780c0c2c0d1040031070b2414820a00828882d001d0071000300a038201c2402c01c024542440d10a00025441c0c071441a0b2051040c1c804903100c040d03d040003c0646510b01c20000301d440301d00c00210b001d9030f02188039442004a612142250300384581440120310544408004c08000c10041d0b92a5140c039411109295015032001402d141c1c0c4800185242203403603010840d203a6000402d011316940102ca0030004015500155066142404003207880340562850402005100003641e04100e0080013503810018060400300096075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 428994334 1250 428993084 428993093
    0x708060a1203021605040203061e0411040308041401080705090409030905450a050711070b0702010216050d0233040305071217070503120405032d0901120216 69
    0x4d11012001e048400090750120300b90a06008030382c000c02e000f520004069110020494030a00901ca034582d100362aa1241c003600d884081c0071300095030040f019035540c1c071b107400a01d4404500b10119141132101450801c402c4982040556035040300c00d48010900d40c0d1a8502240c0103400c2e0740095030f0017040300e228a441c0e00d4840c1c0ca0764400c00c1e1540b6070082102e550300118142d07001640c140c504154015000142c0f04005038204036041030700c6041103280034420343c00c0300707080c80055041510000e002180e1601551b83c10011000101c140320094100709041c040450203404440c10080e0185d0a4003410280d0070300802990004c150fa600e03140000c0780d0511044552a611900c02a2128800c4150224403940e14180000c00c655000d2202c00c03604500c01e030a5015504500702c2900d00780024012035101d589010300c810711a074490409950750340d000d0a09135130954543c418200c15070407114004043c0c0f2003002d045401101090801100b50303ca4002c28401911401c01340c140c401b45501181700801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 428995584 1250 428994334 428994343
    0x1c020a0503040c0b030603030a230c030705060109050c192106170d0e120f1002070311011a13200a08012102040207020616110a05010e03060708060a120302 68
    0x390302c1200b1000510344e0b6001e070402903000548015525400c04c100c40c6500c68010451400b044903034043e149101001c00f0300605c81500200c03840044c1e900001150010084240301e82405041c020000308060b04003401041d20601520030b644000000940e081080f10740540c1e100c812196124040001c1e14544480c80005449079115255100c500d2021300352503d903000c00c54030543e1105958002800c4c084108116840051402d00040d40c041e10441e84030290061004820103042c101e00545d4500251800502c10700d10407030800c2d22640341103100451100c8000e08400001d004403100160489000411030080101407483d00c440303409550203600103000b07480a00400e482e5510b586885a9039070400418a481c488012000c082282840000500d0031350b001d0041640050306d403500300448600610070051a60f1400e803404d48100c410361602d031401a403c100940030038607004034040c6185003c0380e900ca402401030f1060280b2840041c10715240c51031220014a081c8040003915002814007a441c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 428996834 1250 428995584 428995591
    0x9051c140a0c060e1b18070e06040b03010f0f06020d080f0a110304062c060606070c030501150f09090506190b0d0828081816061706010905151c020a0503 67
    0x1414172140c03090038a181060068010740e601d066164a0b50f9035160302140c1c0d0610035040b1950200003071001140408c01140914060081001290311300c17401c105500c05503010a074450070455011911404904d68001100381c1c00200300a044201d90301c40822040140c071041150a151620100c10131050003000e1b040008140c100c400d203607040020794016540800c200070011310325648844041607450030094000c180d124000c02e0030880c1952a5a1400d0948421007210300301c2e15410311041c00280c8080712120700604c0740074030800070300140d5919152240001416400141e5020900d080144200c1d00075a0300f00d00c0050150420300e034145410041170f040464914100c0303101d0703110804000d10b80c4074003034030440b402c0d116600280d5661500444810840c5004521801500c01c5110103103036503485200078003c180c5030700c40300d81c13102c5455507001200101160704020038050100804e45a9482031500000e40076842070b1b8500100d035001c1411041c00c01501110751000410780d86d41039200014600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 428998084 1250 428996834 428996863
    0x1c030818160e010e0105150a140301080a231207060e030f1201050f0f06091315050102121e0c0313060806030f070b0a0509010e0a080109051c140a0c060e 67
    0x6240e40c07a1144c4091801090080359081042840a03908034809407000d4070340c0e00c010b031030040062048045101c4864001381c0c07003d403280c1d00c811641004c020307040c603414520f50b02c05070b402150026120f0b0f11550369109109031031040070340058009c00344503094000c2201074241004481e940c04240119000da548510719900310b0403040e10011400b89415296400c0c1d0f403000400080b40c0c0105482000602d912552724030f035021010030788689016529004034843d013441c1d800400e00322172405002905120b00740c1c0075016109000c101780d06906083c1c00fa014114804446a00e0f126080c0d005050b02d50f00c51641c45001210b0072100000d8030a80c4461664802c450a500b41c40d10160843d070440d0381e0718014096114a500b0500144500500c5030340076200f03500341450500301c2407010380040360101d80c05800000959458120706010b10008001810491052105045815411013001407030f10311051408600440002581e04c01c09106144102909420620030822010308410f0f140d55006100b10265 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 428999334 1250 428998084 428998109
    0x3070207080a0c0e060103020715060617090727051609140108070302090d061407030e0a030807211d06060607020901030f06060312020102090307051c03081816 70
    0x220340724080b410b1840b8503030060002403a541044028600741100a20b8075040550a025100204541e0a01011584410000028003a0034440c00801c0e403220b0041031200d134900c110030320201d2a0000303060b0f002c903020001088580f10100303000207220901008459244c038105418801607030400d10b503010324641c0588410f0700190351143e05404250302295580d011035040f0001070365103802a0020700221750004c081c05490880d07170b6160400ca5034035003083c820303010980c001c000b00079416202e65441c4a210b200241b001c001c591750f0041555000401110811a0b105041d2a03032100c06004d4803221584002c060040103819581840360315081e61040b80240710300000706201c1c1c2841c10880d900c803900a416680284e007142c5500c05d00940d000c0c3c003115040d40d42c1c1ca000002ca48501101e00c0380c3d85013070740050380d034909010030503203070070840e8104501c40e286170100540988080c8244111503076050a06000664805d00700d00b40c09641500c1414850045005032115994404503420030b6420b11000030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429000584 1250 428999334 428999339
    0x304110d0302010605190e0708090f10021e12010314011503080909070509010207140a0305070617010503071d04020a03020604090e10020c03040b0309030702061306110c0109060f11060106020303070207 88
    0x400361016144251044c48007110003007492340d885402e82c0c80d4468414021214005882c2d0b400c18034280c403041000025a0b80424848090901c10ba07418a110100c012014144046443c1029200406204c01001c220200c01200e02c3e400c07081d0000c00d1014031002c4c0c0c10300890340e01d00707205416521010b0201d1145286200291840c0d028800b660385d507280680c020003080c0d05001820344440e0341c003207160340e10413a48280000010303c10032180c0d020301807907510441d1500a90888890010040c3c00144c03003a04007000170310851082c0d0140846010490359521103035156800858a4030896420294000100080c04145c2560507002488201941d4003103d40300e4002e20010022800740040840302c940007040104954182100a184c01100300c0061f64500300b45a030024a160748150720580c0720346241002002015001412481c0000c0008041c0482c05655000286640864018241449001c002040301070384202e0464900d0400701c0e0468140703584583e0040e503030350011150130700144981c1802 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429001834 1250 429000584 429000619
    0x30801030b100f05010c140f0102130603050c0a0e0409151b11030304020105031b03150a090207020a05092806140a0e07030b0409050a0c06080c130b0304110d0302010605 74
    0x6540469018030b03d441000c40c10b03d80112504084114152182a060090881c4032007040c00340600040805000694520035410074442000490380404245880e00040001040544084070944c8004c3c0c64010b5043c5083d000060040c04480350240c5a0610800300701e405441d1a80310b03a00214400d2118100d401d4500d03030031103041d281034135005041c6c0c0042c00070500550084015507003040ca00c0c4a41949041003220a2000341c0045880c00e21550840e003030a040c50405420001c0a051030030310039413802c3e609801003a420813881c4520fa01071103500c0c00294121452801030160014440c0c86089a10f1204110344068150390040c51031084540b4000b19491a03c1c030706071000c80381c02c0324080300142d0310724105900a1603007017030603900a521140d105000450511030314003080d00ca038190710003540c01e00354003e110b2440240038840e0800c1c1040580c402082016503076040f80e4030b010800381d42e50780d50302c1c110305c0c1480e01c1c25505400c0084441d03c01c080580640101040e40d070260303000440802914030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429003084 1250 429001834 429001861
    0x21812030408120702040b12030307030c0f0203033c160c0b0a050406090b01150206010602031c0b04090819120203040b040201030b030f06011d09010921110a030801030b 74
    0x1080a00d500c490303440803000030f080340905035050000303000140c07080c20313400855007106201100c070503150070010405ca1626018810013101c05c10625010b501d035025400d01a503030f1f100160000c2609685618010802c000e80c235999400b51842d011400d58100d40401040c40d0f6a40070b86401c041c3c030344948400781455200b01c4071a0903840d001245200541c0390031227244024100070b40242c1d035150320b0780c0782e800c0860000103415000700034a204403540c0e50102c41c80281019410382062046400401c03030003040e051030251500c1c2140c5503100018040039440002801004078178001000282c0104002d042c68009000e180c00910b595110801140d40d003100800883c070048800500b144080d801090255206c4e03070090344904009822a100114680142490306009070b0104c3d001d0190044c024000300c48114406400c408064000d2140d4946540c5560012031400a014030307400b150707001c4011840c130400c03000c070003444000280c45400c942401d000f400000240810f03100c940c500008100304510310310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429004334 1250 429003084 429003089
    0x11d0d0905090c03180a060204060f02010c020105070e040e030d09050c030f0c0d0b0a09020405100f0b040848010e0d020f210102180906010f0504090c030e010218120304 74
    0x80481303103565a1010b4651240d05c002414125074410080e60400240e414401003003d0000d0f40c0f40c3c5004410401c6000742034610403110fa20840e41000180000560403081c80046003004480c00306103003c00240700c51550090315802c24003681840d01c62010700c8004110f0384441c1d50242c090320598034080001a0b655400c809015030807800e44880d0074042250351002d0398021401160100c0d03005103135000941555419505142e081030041c40030020305280412203401000014241804c0502d8854000d4a400901a055400e1074050410301902201c4a0300d0403000e03071705000c890307480b01e144040c0540907511101d00b80d408070707802500040803443d02e03060492a541c0c1c010b01c1c41c0e0070000888140040011480c2890b005c00d61603c54040032060300380040c14401591071407201401080b10100a000f440150075681448620143c000c5099484011038003a070f4401c45010810301030741181180280300b07000d0b9440255102242c4103924241c1606043c018035002c40e96030b0540500079035040c2d02d0f4030803803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429005584 1250 429004334 429004351
    0x130221010b0712140a0f0302190e03010501080f0a0b06010306030c17010b04050108030a1d0a080c210a06050408040302100f0e011805090c09030114160206010521011d0d090509 77
    0xe2203079405d0240b0941e880f0842d61194500942054a0682450030100d0441012400714960018400c9241000d205260052062400a000407401695000c0e203800007441c0142441e4070800000703015074000e0700304000a540c0240783d4124281d540c14681180d0f400102425055424811041c6492400e4000c5074162519000518035010a0090585079034800a90174100d4280e2002c501045655800309a002403070300d00043c20345032a29104100144a45840005070744a102020207008440011a81206070744500d00181c99121400d01c104c0b10300860740000d5000030550f1050013020f80c42180340050004988070003404202030001500c3c03490401c624400d4810030603030200998507040003442e401c02c5c0d030644594074240340000441e0075101d4640310070096400c0c0b0800e0005548112102d03688585a61001e0242941410700152003502540c2c480100d20701a80540c010040080d0f00c0a2500e00f80310500c0c0d800d04180d4864152109052054a80070070b1000d500021541041c3c1c1119100b04940c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429006834 1250 429005584 429005587
    0x90902090f04150e0d031112010b0703020106050d06090b06031f0f06050402130519080d2106030b01050a05030102030108120708040806010806012102130221010b071214 74
    0x8041c203256540e54020410f075008035640e41040b0003441244a55a0500c20407006131480001200020b0103a50a03140362015081007000344c505080540e0095a0558410700c14441d610040341c2012405044030342c02c560762201029406100300111390788022460fa2165900c1d0145503075400416480e038014200d0a40c48518200d24030502e001558003e5420302412440064000e8907080418200d811050300b0403041c480c440341c144254a004810080d51100c1381c15500d01c040d0030700d201c2c3d980f10200700044000b13106003448000c01c3d0b4542c646d000d05e84010801410040640e8034241030154031400c0c4100d902940103c10b000c83c1030b04040c000c0760b06803402240204500e5481d1400c039042e17544a03072400e48028409101c007094054060007101e00070003e26008010035410140b141020160343d02160401c10707400b00750030300140c440c00b0004002159440006850340030700c900c0d01480042a5203500c124007880400440d00d191164050074185020700d0f40141007013102e80c01511070705100c0e032801c46441e10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429008084 1250 429006834 429006841
    0x30f070f0e070f020c33131e030201050901050702060d0504060606031829090606090606121306060918050606040902010c120909060e3903060a1706090709090209 71
    0x8040311901c2d407a100c0c05030310b0b02041303012026a0011021b26a00306003900c80002e100707101420702c1d031001009420314010181d400a607004103072511000b50705c4024103100000c10039881c0384c2c4c0158150744504d90090110f564500d8141003910050408aa0440382c8a2421b03801240c014420b10401110465511000c1013540c2e10343c60310401700382c902d480145d00b40a50941054a101c000c0c0c600c9014140c1c01004008604280b410007904200040a20f4002c2da030074400c020f51583d09101d926041060181d0300d8a00601078203180025000e40e0f00700c600c81e642810b880d034240c50781003462001e00a0140055a0150300c4120070007054500040021740081d4942c41aa008606826000710813400306082145065070b480c02d60781c1c240c1d46a41e01c85046002140c0800100d4010451005540400f601d42c900c40031004200c0b030000b2403100000780c158141c0110000304036454519490300681091001c1c4111598180140c80d40c400007102c10700024014418001913041c500d016001582c0d81c002d015280c0c9a5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429009334 1250 429008084 429008089
    0x319022701170c07081b0f0708010c0509010c060b0a05030d0c1a06090609070c020306040303061d01150c1e0b010f0e0702060a0b010c02040c050306040c11031602030f070f0e070f020c 80
    0x1009480382d81c107031b8071000409129580c3d040002d00c00e80b402500c00b034008640341803107880c21241410000d0081c07100400c03450186a03403001000300f41035400756000404d0402407010828a002070380002d5010f103c4d841680030000d42158105000610a000107801e1101c48a5040814001a0380890700700ea0f040010034100d141c40c81c2d8090f030180841c50301d00b0840d110341d000686403007003e450540120b647c600013441000c0b144030354002424000c100c1c0441039403601c00015031002c00c4445c2c0f4020040305400413410051501c003040312032114820017000112103402c186000000078492284c140d00104800500e800e00611200c0c030a00b09a0060076150b42e8665090000d08507c0c8141410054011001c0005940d24491200d014002e659030582707919042c01404200c40b518803503001448000c4514048e581c000000319a2600d084041c0c5045841081c40440d00d010084810702c8824041c1000200741c008080c940c0000b01c1d2a00440d0400c035031695042640c581c0300c401510f50040e0040c02c0f0011403030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429010584 1250 429009334 429009337
    0x212040e04031403130c120507060305130c08070608070c03020304050d020f0607060c0806030a0209061908060705030402040b040605030c090405030d140a0609110319022701170c0708 80
    0x290007414a40100d040e464440100f561049603420b402000e40b14000e4148020807554401400748048082c00420160301c0b01903940030a80309000415403980300068552003005000159a9400340380300e81d00545403101c5603203074042d901501c00084c4041c8000f4041030722602d4846003407a01500a1031900b400c01080c840c03e008504411390300b142c2d001920314600d031200307401404010b010711400a40d1001030303c0001c01e80800034200f0340c466400480000e0140e41c9003030005800220131174030864882c417001054462440241c0c48480240102020403040d650844002e51003244210b4040051078041d40070031080707500f18050300390980c0c009903100d071242c00e0000c816a00710b40a90f049904014541030100252903004500c000e03801210720500c9401c06040c002c21002d000c5100013032154008032200a0810b0000034095445c01410384846000003840b42e04407164502c0454203c207400100c0391140407030080c0c080300540000c1006216103010f03800c0c4e070704543c00360340e00040070b516005640e12604000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429011834 1250 429010584 429010591
    0x19060909050a0209100302070327060302160b01060906020c0625020a0810060302090c03160507080c060f09150105060a11191112030406080f071803051605010212040e 73
    0x1c2c0e07820000300e20113030344600c01502410501e5402581c0c41d00c207482d004141002410f018440088541a030100c02144c000071481960340c20301e001611208680d42007003180301d950030054102c6035a0800450a660700540035800c6d214540c08a520030b48010302449918428404070400300070001d4060b292444041000c9442980009d01c40304400352070b540c02c6401e10310041c141540b410b42d1080100210f09181840d564010544a140380c114039109000418400401007440c00700300d800039000c000c00401c0000d458400031410201d811600e0282d01c0051492404ea03005103482c41400c580040c07105200c1c04180c180c5501402e02c1d42006215101910070080c04030307019180e40074804a00000c41c030107840e00400740b40030300d480c0c20807001c0c400c003400486140042006a9908108010700250344c00c20801e6070401c2007403840001942d2600d03c00c0ba00ca0700c404e4240b4040328000880041845000128015100d061180180347c0302d03079440041e640c8021000070002c00341c0040c44200305646414004560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429013084 1250 429011834 429011851
    0x6091b151d180108010b100905030a0201140c0d0305010311120703030813080d0219050f040506130803030a09030815130203071403040c14010527010201060503011a1906090905 77
    0xc120b080365541500d001e426004130109a54a5040009524001030080640403290a10181450412001c81d40b12580384030041e043c401c51400c3e080c0b0602c0010100c60f821503080301500c0c03180340c60780401000b0742020b10064030000020b604151071031800d1241482454051001410285d00e10b0760190b1b150701d40200021206000301c80d100c008100707400010321103a4541a001a03540000c80b6141d5500304140f480d180400c002401058902080802290180c4a0480b04262240b00d41d580f00302082c16079805c941081e00000c400e012540441d03411507501e251203600d40030210342c2d5107000c000502000501d80c5e0790000d2010a600315222040e4015034000d0b0041c0b03000890342d03289049081540d07005490403519000010810005601c000c0f07051007d0038800d01c2d10a00c1c0414544030349a01c08010451080d1004c4500c0e14500355078000d600031802490045c1c024001544041e141c4642124804140f0b4040c48900740540b20714041140003806035220760711204503150408075188000d0400500803903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429014334 1250 429013084 429013099
    0x3060a111c020c030403050c091e13060207080403050a02180c161406010e010603060902040e070f02160902220305061303030b060f04080c0a03050c0112020706091b151d 74
    0x50f43c25005000400245010710028031001c0c228509105030171400900061001c5050103c1104035480310080d070360030625918000e81d10040c90708140d0024810128010300304207001500104010b00494031201e9103000321049a800804071051216408040f1a210391962081001800055109440501943c003e81038400c03944402c00455142000a8201d07031b55404c0d95100400c20390740d00d4001c1d80c0c0034210131070342503041c245041aa4501a50064032a00c05d0041510044c01b01d01c1c402c02c084010105d608800d01ca2403a41c03001c200380254020000d411a94a03031140e41088004544446001c403035008004200ca43e07100b03084c081056031100c004404140d2600b031143e106548100103030003920030315404255200c1c5808081c900e01004141c0c0c950141d0100081080400c20100d800c038110542800e008000d8090042880000d100b4030b58018049890541c280c01030004820701d140c60054000c05507032401c0d44402c00345007881484813080340061100a0507803c0c0180b02d11018003189009812034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429015584 1250 429014334 429014347
    0x150903120509031c0912020301140a0606020f1b040902060c010603051e01051023150405010f0c0c051507021002010b09060f130203150607060b03060a111c02 69
    0x115018180340916500064000c1980001480d09011403501c888003408080450905030320068030036400c1344940134043e100c0c21184401c0d502c2c01c0d04810155003850141d035003107241629407440108800d020f1400140704008240c4594100040da2500326100c016a2061040b0141d08010191140220032030f0000c1003404041c041d281d090141c840558415000342010040f16845001d07150700c81e01c5111070a80c141018082080340040c07988098600c0d01070f296000184049600b0460b00c0c404001982110501e0303054401d400181001d0f01c10b0b00d071300340d80d00c203103140e41c0d091301b21520605448060610300e04da44040000c2d16150031100c00d2503007002c0c4e440f800c12200c0c0c1c001072032072036103450040c0142c0d468030702c5440c181c035042d4100380d0310003406c59075800c001501740c0c00304000c0040d0701414030307949030f00002003106007141035030034082d9140c000c08180c1d80e5415882c000018103001c101c030038004c0c46100085103421b2800e019204040d460298200e0624510244981560101c030007003081c0540c1c00c01c032a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429016834 1250 429015584 429015593
    0xd02120f04200105090906210a06060b040e010909060906022215020307060f0e030c1e011a04200d0e0c1c2006180f011404150903 57
    0x20521035014040011000e00c1c1509110b14060b6140c070014800700c1ca0b88501e01116a00001907a02100c4155a003591030340c2e41001042c003910135540c00d0b01d80080c0510030112004400143c0e41c462920981c018003440f9503075140c502050240340035000044030003600500c0049034139840200180e0081502180c7d00010341c40300422a031203000c42d03c450f034440003060f0300307180543d4550740010220145100c03404403806600035280c2c0140d031002001c050300d2754203124071403101e80c01510b200104141565030303900e240441c0560f14000303546140c100c0c042114032002c510806115149151124080c00082c5041d54000c00c0010910b4611540040407000c1800700d82140e03480252480d00c58280000500d984000c01180c03030b101e160048507100c0d84400056040c0d80281c802881021076006c8104101036080c19a0071000ba030040703104940100c0c01080c0c107100500400e4100e226140180c91030b0342000c400300011540f110309450030440c40d0000300710030840344400000500310b840c406c0c0703004802d90b52240d03030313 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429018084 1250 429016834 429016867
    0x2071a040201030c02070b0a23040602030909070903020d03050f0d0c0306050319110609130c030203071403070c0b060a0315050a0b010819020f09060a2a0510020d02 72
    0x2044005100164104000c5580620440d90140d2542c0010104a864500800824030507103102904011100c0301c1d900d401207000c4a44949507006d510711070b4603035403901d00007992604002040d03841100c40002243c0a10302035011241980d801504898601d04543c0307058806038851a0150542d840400c91065080b100b03114141c00d15207241d40c045100352030003040510b0306071400100040c0c40d29007000040000c0070b031036600700c001d6000d40714a600d6200c080002002d4007680084105a94103140c80701904030350540c0218031540c0c1d591200c0c281c0d440302c0c5a000c91140811140e18012403d4802a00c0114803500c1e44564400c4004189100c0d1b07030b0300caa84506001d0381c004d411028880e15081400601c3c6050b02404000c110b0a181104861504240808844000040c04043c00e0b03400a0440680003110044884052001d81465a10504400018029004000c008001181c40304d401d5600e0000e240807803144942140c0200390001503401c031000254041850b5104469080005032442c0300b2400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429019334 1250 429018084 429018113
    0x114061611010906020d1b0305120c0403020312040b0a0e030f0a0804090b01021c080603010f06032006030628051009060f0c0b01260118060f05090c01080405010207 72
    0x52140e0304201c0048009088880d42d0f4108805541007149084809a4080800c5a140c490a2402c0f2008020350400f598248a490a100350100d0040100525580e45074018000c9900c281c00b25440088229087c072880e01035405121480c1c04200070003522035100f0100000300810050650700c442c0218805549001e8400000700c82c0d0300c1c0c01050800803240702e4071810410041c28005040e0003021020403a000d5500e00345501e082c001d112001c1009502c09600140300303800c510800b000301c01e0310307400d0038443c0d035914030fa5043c0400400b052a04690918501741da0040e40c000c1c03c0d10714008d88580e5105107244100c0e01c4048503807184540014165650002c40c01c00b220540c60300d88041e410201c0050284490044202c00d0042c00109080080c0c40c0c1c0c03038140e0440f10b2503020645040442091507540d10700301d130f054001c2503007411a03c2d00880d0400f02d80400c0d19126071800c0122048901d0b804081c2c4100f2507284030990028a00c0340310550142d80700d9584a441079000601d8001c0aa8a01e0070586811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429020584 1250 429019334 429019343
    0x15041a04060e06240306160c110303070309080d170a0207080d1109010f08070203030417130b030907060c0f14192d050d031d030309010b010305011d01140616 69
    0x2000540e0405548018011322800c05d0b030280c078451500014010820044028440c00c0000500001d805c0c00300c59a604011282c008090342d60f109954100289821828044c00c455401040326800881d405000e60340c91601a002e40b00d14039a403901c1a500003900507a0068a810400300b0071448a00024480d000c00e01c00071802843e2180d00010005014521180e8000c00b4081d140013070101d0a500001526803181d88004001c0001700500001d941c0c07400f031038030204903903181560003085400c05000514414006c1e6012a092140c1c0d40340c3c21201458004c2c070113080025007180010228145184a0381e00e490103004071000300c40854045014000607a000b6541c840c1840d602088000d0080b50030f203c424074011210442c0b4002c1d0302d80b1034460b015180307201c084c943e032411146407100d100c007602c0314100402001c4d203480b4034041d15030320701038407418a00d24002882c00c00041904030009a160306102c54178102c210060b03080a800101140507a04040c0d40070350280104180314454206aa107014400c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429021834 1250 429020584 429020611
    0x5091903060b0105040b03060904170a0801090b030c0d39080d08150f03100903030b03061008030415031803030c0311160b18030301060c030215041a04060e06 69
    0x650610a0482e107601c40c2c0c05040020070007003042250401c00c1900e40086040b146142151214907000e90103050010041c800c0301c9010403100141500482d119049541d1080d00780180445a401c0503184c2c1d4100300080d40c800c408544c1342c4c004ca00030b500e00c0403c40c0c40708101100c82100d03142104048140c1a0300e01108120400700c1800b90060600462034854550304049901d0704041e0007001d050020501c07418015022081b5100d5103036002c1100e00d0802044990402071805c0c9414010040e0502c0603100e1300920074800414201e01d4100000c0086803041000b40d8245400c00e80101e501200fc0d0810404060312038140b107030f1441e4408030891906200703850009601864110140540350701103e00d8600384418403540d111601e0200302d42c048182d01c800c01c03642c5a5036003103020a0720480718038a100c052002000103d0f40702d801c45c500c007422901075000c03074104220070180b42d900442e0031a0020300302180e16103c9003800902c140c0e5241c00034030480000c00e0b1b0b903007680c0e50a0724000c41121540b025229 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429023084 1250 429021834 429021839
    0xf18090c0a090f0b030a09060b090a0603020a05030a0321021c020903010b09010b16080c1501060818070e060d050109030f14040b19020f070f1517010312050919 70
    0x20000c0c50b040003840d0081020500030719011030350110340001001c08503003070340311220b400811070b841c1d001106191000305400c0031401c00c03a01c8180140360501003240582c40354280030519140019000781d0065060743d50803000004001301c050080b0702c0c2c02c40014443d4080c81300c1c3c500c0170182c00b82001301c034000074130060b152064041018251980d50308014010750481d80107100711030420045982c0000841a50201c2d02054945003d4620820224490602642940e1804080912121812240d0540c2d486078140c41c3d45021b12400301d16403400700515800401c04000e146c5501600704c1d070003d0000c201402e0401e10f034640c0d900307491510300c8c00c5000881004081c041c258008550701c402040d031102031801c0508260400901d03100d09125903800c0c012240d5a540130f1442000340c03041c55408541684d0300c4070ba0301c402c0e0352050492406a07a17485140703a1000c0040d14400c05506e010180e44131101100b0380d01e1500c803e115006007075080001c11034100102c0c01c1981b100020140e0b00030140c00c0c440000c91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429024334 1250 429023084 429023087
    0xf130812071208100302060f040902040e04051509031603050f07050706030608030403030219022701060e010327140d0207140405060102070306110405150c060a110f18090c0a 76
    0x20700461650b02071000d0758051203401d00e10a40807106880c2d06885140e03460015200390501401154405120107000103008075120f0b80352460321340518800d41c1100e104001041c0d00d405c0502c011648030306a07034414460300b58207820201140c24070f00d00a0410b140303802c500001e204102c1c3d1060701e09840d55800017a080142d01d038540315200042074000040d500340760440d0b13002074842c183c038031074601001c8070701e090003095542e813014070b480110950303610501c3c10400a40b030683c204400d105d007201049008c10041400d500900071309422008001c0a1030908648526010500041e004180d580c40101c814000c14454204220580100c56030001c160b000d2521100c0e0400380000305230780d030149081c0424007603103980010740a42070740c1c1e00c4807012900e120703040307a10340c298000c0f0303800a50b0104290582c4401c520104d0001c01d042403d1100ba80c000743d135002811000c0d10303c081c0204021307d03010440c582c0c000e241c44018025a0040d0b110315614200c80c03000107458144161030840d0004c100140007000035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429025584 1250 429024334 429024353
    0x30309120c020111060106121a101e030204030f0f050a060f09050f1605090c0c06010e0105130c020319020705040606021c0809060c090102010905010c030608210f13081207 75
    0xa42c041d0085c03041d076042000040800720380d44c0104a5054075034014504814110040e0460030300003500070350104000800040000e001c2e90100c041340361402c0c000038402d030f2290080318140c0e03410500e2034900c54413982e504419004400403d503564010200b001c070015000d4051654000084400454803040c84d0400c2403d101c070303895030b65026a0000d03042030500703030f041092003040742c40031110303420242d03144030850040344242c00c0b01c59154000d400011522028002c6414140d403015103400c01d13808142140c1c0c1c012600c0c0c0f0000000980d00500a218101031030855030584814140b05940100e40d4600c0440e099840c243c000341c0c0960801c0042d680f41c25150403120200b041d217460700680b90f040001c940c41e01c3d04070280c01500140000501003006900075086146500d0b400380c020001341690b048011700400007809a501240035801c2904040303801e04202004100386811100d1a011243c21820000d0740301c51520910712090080002e588030040c025030308004d4803403980c20756540d600e01c1c10501e0b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429026834 1250 429025584 429025607
    0x9042915030a02090105010309050a060f0c030506010e0a09020d0e0303010305060108060705030f07080a020f031005150a05040e09120a050304030e01090e1602010e0f07050406050312030c07030309120c0201 90
    0x6540289115009651144804c40c11502d080c00c0001d00c05401c0e00740345040c0b11145101421040c1019100101c1c000d140d8402c440c0468540da0070040d94682800444564454101003940030100001c1407120b000c03980c0c0141030103111140c0001d0321180507006c0c0c9086801c241e00c10745440d0810001080204003e22a9940c1701ea11032401380d203140341000d001d00035054040e1010b4204101c4030001009108641e048540c9072040d01401070700ca1070803c409034002c401c01c4c000c05000700401e10b400396000c02030406961044c05240c45032400d20381448445c1c0340c600340c024694181032282a04240702980c0c1107005105000b0260345a541d40e10701070501800c60219414070604002c452107040041c920003948080e04986094103424005030502230407030151003104074140140c0a09040100e00800000d00c007822680140c4090102d6559001090745440140120079141e40082000807950b0140c10b000740312041c8a0f00300000d481216442d5049104a26414503000ca03100300d1900c010340d038101d1111101d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429028084 1250 429026834 429026839
    0x6080309100c021503131a1506031e04080f070b040c05030607051204030c0c0b0903060a062607080106032f0f06090d150c1206050102030909042915 65
    0x1010b40c1542d011540301410b121105030741000220100d8250511107a60700030058000000880641c5151b0503c04100010b440001c102c00340118204024100f0304162481b801c00c60085c01008150300c0003080d81c4a10040c8101c17070102080100b884000220380c050510f10313015440710800c81c0f0700361410301c400d201c02d604954801da00a8003042003184d4080100d540c0c0b68520b010b00c3c00d107a11545001e8030900140c0b2401886412070040102c1d00400e10006004035040480c00c030341c51520394800e07901c121552809410b1b41c8180d40d4107192100c990800c04004490401011a054240c1d00d0480724212109904101c450281e040580800c0c40800d00c2031100382180812603607203007078400c2e001500201e85803140c980101000f082035540c9659610381c2c20002078100d405508010840c402074001404c80000c00710100722040b682600081d00c900c10001030b920180c004502d040541c500f00580c42d64001c05c1240e104420100010356002c401c860b0101a4080c248524450b0505017514440340604500c0c10b030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429029334 1250 429028084 429028097
    0x7060608070807030816021c06020c0d03061401080c1306030b2b140304030f06020a02062a0d02040b0705010615021b040c020c030d0e040605100c1101120608030910 72
    0x30101d45001c0482c2c0c50829446e03c1040c49000b11320226204000d024030380300e43c03600c80e0070303021091004907001404503208400c1624805c2e20301c1d810a40441e04e00340682071090507052400310745035005107890351700040c601080c24140040b0381718002000280c2e400503000240c442d1407006513400c0156452890000e98442c24010684100d80c1c0380c0c01c0c006d450006450115680c20b82550713520103204a6015540041c03034221190ba031424030501035802000150010700c141d00020382c8070b01c002c00b80c600c0c424404004460000d088014000c9079900321000c211903455080100041800300803008101d41881100045040b0780340143d0b01e0751a140c41c0442c142550400b809400403840300b4100366500c89401c0b900021004100d28040340b81007401c001e02601740c4203160f84120515040b07003c0710720381d820071141800800d44800034483c00059040d808800710740320108000008401001401412806141c1281100c615079042016680c039a0300c000602e0f040040c0281c0e00342000d032a800c220a01904001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429030584 1250 429029334 429029339
    0x120f06090d081e0604090c050402070807020a0902030906040b0907170f060702070609090e0114101a190c05010b0a09060f05061905030a0b0a090c0201050609190b130207060608070807 80
    0x641543c02c001e29240c0715035074907840350302040706500c0058003510380a0011502c1e80c1e07484c540110745a000d04800d9100b03140801000030044024003c41c0d00c030f440204064110340d151603440145098020b003504900e802602d10118084404102c0213072050700b00402802c0e40581c52980d103042010180040d400c541110105000d190340100301003003214903021700040d001021150703190040901506010105003100c080c07044001664504d0344c1900d000307280701c00244440030586011071080c1c400b40c5004403540c851120303c032130050741c01e22840c0b401540003081c0305012400152102c6190f03003101b03840c165200014004051540401d40c0580802d50f00a8039085844000c00303001c03000d01c1500c004020700007002401d085115040020085030142c81c0c241883c1e216415280900f24110720a8015882e1600180380e0b0f1070300e490400c0c0a011100c8091030b6101030500c0b190041c0030852100c0760400c4001c070028505415130320040c58000e000c1e00c0002002414600020b04181e82980701c07281c140d05c0344006 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429031834 1250 429030584 429030631
    0x41e050a09110d080d020316022b0815120610080109020a0b0a1403010308300f1503190203120a020d030203130602070c030201080106030908030105120f06090d08 71
    0x22190301d8004a43c69034425465207800704041c821202c14a400074004000d000b00c6540c0480c943c0982002c07a0241c0d1180c5042150307107544a819501841d5250300c0c075940c1c1c00c039190300401101d82c0041d50401c80540c0000780c5030105001d48141c04410b16154040000c011802d000d5070040809000401c0092000c1e5141e40c00085601c6400e000d81c5003c14400105070507854040d50301000c115802134225900c0e5a5681080c0038150484408942c3c2040c02c43e440d4404c0100c114101d1400e07960b8044880d0107070300c8480c014450107074000e00141d40b421443c0b600c0ea5140e503080090300d5010481085900d03036240c503481854203212035072035030f14001c200c103011910031144c000c6803056440340340b07150041c5c981c2d480c2c03180180c2c4400205400390030944005518411300c2030410400c02600c0c000c1e200c1c201c40366643c2400300d04813584034901520848042c0010303c5185000108841c4400000781142c1c000300c41c9070242c2c0e041607800d8070608070a9109011440c020344d00004480c0d4051000030702c1074078a0400d0050b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429033084 1250 429031834 429031853
    0x60412080d0e0601030302330a0f0612060501090e060f042a03030809010e0c030d0302031b0f0a03050604020a09060305060a090c1d0f031f0902041e050a09 68
    0x4006058050100c0d849004041d01e911a002522810080740d00300c1d40c0d2070a010b510383c2c119550400c8001500f2801242e04882d40e6a401803c440e810302c13007105550350488941c01060510981c1c103006448400c001811010200b190000d140920300029003540360442d01ca0444022a4411aa0360401020090b10003118041d00c2c1e4003c2c2c0040420800f01c0325031000c80750940c070541061452044000d004424103a200222501c603910300b070000c12260302c008100075078a00c440a0001c1c1e15901054030748941e1031094005d15000840003040411428034610b0141c05608018403403c400c4001240c00c048032079040c01102e0300540e042e1811031901d218180000c1c4101c030303540280300a15441780c003c2104c0351200b04100d001000c0c00102040307071202e40c070001050544464000f8111503c080c6d03000d00c051810a034840051a070060080c20442c0101d030000b20003001d4907011802e40399440300c00e8009a11203000700e1070b180c0b40b424064851400052090411184050580425145003480c0700001403280325 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429034334 1250 429033084 429033119
    0x20121803010c0507140c03070b0703030c080c19110105151005040e1b190302040614031e1003081606050a0e0c090604020702130e0712170901050408030c06150604 71
    0x800c04103004040d82a4610b003000001490307415202c0c1c01c0d0b00041d54003109e0081d040c0c0511a030790030322203500d101c141113071042816140d4516595040044424140890b05d96040d91007483c1012504076400700da4036402c40e4011140380d0b0104c035255440040a1030486021440007070341742083e42c281800d101d42e22251400c020111002c0004420078000060b0407c000e5034500c001015400c8407141e0702441c000c0c06074100303100714404140440f0000c0320000290003035030b114103040e0940100c0c510b4002e0520109400150800c40d00b4069030f031000c404038001070001c06814201501c20301d500368032403030910102d48000384901e021900c0c08000c602901408110042d105004031204001038441000080c000d02c205240290f103c0c44000c031030252500c65400401425108009841c1c03490f42c0d6801d042031120403650002c149075006203400e05100400c070003400080d1418035042c2e007443c2d1104c0c0714624540c8050300b010803c0c0e1048040040134000540080307021003007a101641030a144ca40c040a4004425 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429035584 1250 429034334 429034343
    0x61620030a0c0809030d030e010609020405030303061306080a05011e0903020a0308040314040306090209340509090103050c0f04021903020319050126010203070e0120121803010c0507 80
    0x10b4250180050714058a4030400020b00361010340c540301401900402d02c11041076544e50a064000074050154800d5404441c8042c005d0352840d035030b810402c0240e800809540340810b9035034101080ca00d10800000044c9441030000181d46092002401c00070848462907141c2c00d03042c40e1101d00000d40c0402c1c0340e01d01c203505003494012900c40e4503054442c42c55203412400700390400301d4000140300054000020303650095078480752944900240d150314060055101856118a103c50b03403030f5152280d41c40c0702c1d03501c60b49012414400b4900004104ca0000e90054035981d200c1b051115103440c0920094074211000ca40852600c1d009401546806506106030828940d000c0b0005441041c81d4440d0000c034200600204440c0da111450303071100c2a5415060031f1240304216064040100501c02c480c050441c0f521075940c184a10401101c00c6624005004c2600e41040840c07882a081000041500020b0f0046140ca80c011060080120200382050b40d1280e0304210301403400c0b0360420100c45065402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429036834 1250 429035584 429035597
    0xd020111100e01200301140d03031b05030a142401200609060f0c090904021807020d020c010201051933050a0503010207170307030e061620030a 63
    0x49600031400c200400c0316010380d5030304101e400c0c502d0381e0041d8003544c141903030711004051110f020443c0c825240024098080c2850340d4840ba60090b1615000600340580b00340380c0450042520700c64101841400d10f04600032075808020b2041c840c2c81030051702c100780304003c54000e507442c0203008420700104402d407448002480c9940d4886a902c01c2040300b0300f085c031414a0168010103041040d13569041224460080d02800740841c40000c2105135250080080c140c1c4036041004680030003022820140003240d00c40f10150070b14241241203000d0310311400450300682001001c00d04007909290460070709034116450700080100503070010b00310400030068002c4c001640d1042803400d0350030080030002d0048041c08400d01520506007603e4480680e00c040d6420345140b5036402c01d05090780142080181264003201c941c0090034000c001442e4840c1c024580415441040e40b8002d04211090714000d00d0021100080d2651a40024076201c818400e0210280740c0ca0200140940701d0141c0d20804041040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429038084 1250 429036834 429036857
    0xc05061c0e0c0d0506070908121c020418050703050601020c0901090e0a05060f070905010c0b0f040809040f0e060c132c010905090c030c03030702060903070305010623040603020d0201 80
    0x41c01c00204000c450042c0c102c46880480d4107001e41d48540450320f40c8001844900c01042c6218041021641c01d000081090306050140300c25045a0618404034640c081d402e2000203600345039032040c03004400e40300000180509000740000c042d44c00080a03035041d58810048802c403600e4400d052411912404400100e44c045035403418100101040c003e80284955010b002604000043c8140201c00325201d03079000940d544019545626000d0f8040c01c0320070001c0000d2100c1c680d0307c4d54a9030107841800c46911b404034140001e4101c84c0800280e0b2846551034458442c50300e0b040103556081191010034030300b041c502210712040700d00f041c003907500c94a1400f00034400003070f44c0c0d100d100103540000717585480c5583c50f034070301c50001c00c4116041c40040c42020f108074058240401ca0b5010405c0180103580f4000454080c44442d606c20311032507030107114512000000c20001e124460141100720300c0148030700440c000d2000400a42a0318911a92a00b0001c000603071340d182094940d41c0e42801c0100e00c0c0d04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429039334 1250 429038084 429038111
    0xc0f0c0f12150c040e06030a0b0c0d060503030c030409150f050114090901030b0601021903020613050c0307120209100f0510180f082406060c280c05061c 67
    0xb010305610500c604a403100303010701c10f94201c01400542d040861040a6607031b403002016514401404050a01c1d4402c1e008580800d80300801800b0b5440780030f00100d412030b0303100e011134a1076000e084c4400c45504049010b1040507040e00500300710a800c00c0e03212031098104030100c03451100a2081905101c00310b820540000f0040c403e44200b8800140000c00541e501c0c2481042040200d80a50041c002c44007103429030340028200c2425650140d00500841d60b810300b104038030314159082616075101d5200602d82960381005a000504007001030034600080703d01c180001c43d24040c001440c0d40707101d8a014400d603291503e80804650007200d00000c0704c6000c0d003041d0344c0c9030200360340c0d04015100400d001c100c90607441d101d90122121041240c4011000d02c1080280d06503c041040400c01c1d21303000314401c0d00d4640060043d2088a00c01d03100c298400300ea2406c0782c81c04100d041c03507018030303070304800000d000e40444440c0040c00299501d92030810000e260080d034000344004040e135a40c0d01c040c801601c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429040584 1250 429039334 429039343
    0x1006080a05070e220803180d020d080601090b0c010b04062702090127060806062506020417010f0b060415030518010903080906100503121c02070303020c0f0c0f12 71
    0x588601c1e441c11111850b801c0036440340e80101c03003100300b001c0c5042c0c03891281f400020701307034130503141c907a0103014450036403a41154800d40c0600194100442c007507020416400d58001030540c03918680002500103500c00031301060b030b0140d90146100d10901094080090941e56154002c0b0f02180401a0b4890190006035105400030185030b05401c0e00780b020300c5038412640d01d8803041d581d141e107a8034074581d0f4042c1003003c3d61243c060000382e0b000107000c42644209124031480300703440c400c950250901d0345510a14014041e191400300160f9191203c40160799020310654511340010b44000b4030b032034145001c45050001c2d07459071004041e40d51000600c200302c0390524400003906000240034814003420300805413030054031030400c68000c51f004215036504041105007200e0f006000742036081c021204101d5107402000048031040c0e00d02c031502a1107807803440140805882614010788805503108003074904901e125030200ea0340d101e12018500c969440c8000e01d0140402c95540040d030500709189404c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429041834 1250 429040584 429040621
    0x9062106030f030e040b040605030a0f08090303031e0603120906090102010609020c030a090803030106020a0209071b0312050711070b09060f161202060606070308040618051006080a05070e 82
    0xc07005200b407004100755021080340c6040c0c5040381d041c001111008100002c82c2c00c584941c581c1a0301c41554400000d00c006d644000e0b5034041d000d55402d140400c1d021034195407003110560004840d07082070601102c0c0d030500154001d0070a0f00103081194043c0d944813458071a1340c102900c00c035404922202181e201350401005414208010354071120480e94055698011451300f0000c80d0707000da00810740c3c840010982e81280d1540e4002c2541c0c00458080c04000d21002d005c180800c030366551022110800c115101c9080b5208e55280c1540b08903143c654030441e140036003003408000a014036502030640015580c01991001c644050751445402e00054030707407082a00c50100c2c104085800012001206200700466000324001079100b4034640040f40c40740030441c0e0b101e0307001c5010b10080011902c582c000b1548203100d10300c005402c6040151140352540d04250440e001d81c402c880c12990b11100e80180402080d403c0020010300703d01d0f95540e40c0b210b4507030045483d03000d00c420000c0d00c611801c0c5903180c2d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429043084 1250 429041834 429041843
    0x90405190c0207091112010308090d0c0e041101171504150801020c0106050616080f0f1b25050d1106031602060f15040506061b0102190906210603 64
    0x42641203550282d10f03088071380301d08603026103400600c2c80104032800880c3e80c9180c4040f00f0b0b15060f802c594a00702540c105010640c0c01002110805001819080c0c40c070b4041c00501c0b00b042c0007440c061418504c0b030340300000b8050401c2a0410518400400000c88035040400b00500d003500508000214001f4451500c4950748445007100000b100d020641c005d1001d00380d01d40007407003c0c981702c4090004034850585045400307600e40c01c6003804948001c0140034105100b404e26441c10720041c0e00072131a81c02441d44000002481c64000b0086c0d4405c20100441c1580c40c1c0c20f08810348681b0103003001d4010035109150103004960790010800140e005200d42c0208014000741d2139050200c001c03011001c51903a0f170009481f030407012600c07464410061324840da0440c000c0b200044201014000600005054150804c3c2c003404007280c070400103e0500000f004940c00162201d0b0444412183c00315181042424011240d905020050b801404002d5014403a41e02c078882d510b08902c20780080c00990304c00b90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429044334 1250 429043084 429043091
    0xc0604030c11181012050d030b061306051309050705071113090507170601050d0204090201140a050702030615010f050c0703080d0603060e1b01140d050f160806010509040519 76
    0x20a02a071560f1181d01404540000490164682441e54102c2481a40151065200500e4400094403030f03080003001202c00350031742c5e04100b1408540d69a661243c1c0001010a0001c5024a5064014015940242501d141c140030504100c5800380140c411160050b11255280f0003407003d940300c440e18441d0030b0106010400c107155850a00c035844900b10702910124403010324070420450030025070070b41a00c0005201401401c144c1d800c0000030100000c049040c0310b000d80c04d00181400250180c0722407038082c0c6406a0b1084076104041c206400240350040200098140018503603205910551120b201c0c244103070384000b140015031812489610040c0801d80000d050918400b003034210508503882501c06010416000204913142da41c0c0000703441444440715541c840c3d030341c480d202038004d40a200c0308243c58030004c00c0711b01042d5041240e08501d4050342400340020701000d00800c10707101c0607030b00e0f03d03501c2404d02a0000b0418802c0184003840740d92958007040e002c20641c0c0800002e084000f034100b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429045584 1250 429044334 429044359
    0x20703150216120f020d11060c0a0201240501030b060415080c0d05040f0b07020105070e220e1b010516120905030d03050103050c0d0c030611070c17010b0103020c0604030c11 76
    0xc4c4442a200e841d80010f000e80300c9685d4505000d0340c6100107140c04100540b000c0c1e560310b082ca540a070007982d80101150740b00c00600e0310020300001c04461005102d00318444070ad003014001750580790015541c601501c030420080041d40f100b41808a020148c80c5444107507910b48291201d8540607801012061500d031000341b01c200140e0541d4044900c3c0310707400380708040d90f4840040c0d00b09c401c2124224041401090454014070b003035001d511200d00822000c01030341048062030411190180050b000c0e0b580040341c1007440e5840c0c2d07001c0b20400d11003440c5c590f180c0803441020b8130f0f1016858100030081845c41818070203940c01902c20101800001c0d04461403000080305c02400b41c072082c4010390341130203020040d019500300425042c64541d0400c1400c44180d1031669244000d00b60759200001f0301c2010300c1403070000783d98003082000400d402c074144214404105021030864030031591403414180704128210703802d1f0f00400c034607604c00c0c1c1504140300f001401d803d10404c04020800c400350b000c0c2044282 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429046834 1250 429045584 429045587
    0x120424020a0c320f0409020a150804020a0f050d24020d051005090c070809120a0807150b21010f020408030a08160503010509130b010e150102070315021612 68
    0x8040740d030015442c840c6035210380c2c01c071445040e01e105801c1a0401985841c031300381414141c10138981c0c5031002d840c4803502a5240120625041840c40700c000080700354080c0b1041d0320301080300c14040c203000780024502e0380c40c003000a03480c203000a000074114802445e0903020740c2180d40c0c0d10300600f89804019542e4100111500307009200c03c540034082070502020110700c9090282026100e03881c5e02001c50716107001c9454918542d04080c02d520341c4002c52501c40c0c0c2c0c0c401c0040c4420f007080380c400c0701d809844060034540700b80348207170311081c1030f02c201e19040e20390040f0307503880c44070352040b021040300d07000280150045107014000c1c0082c02c020040c00020002410f03000040100442c01c20755840c0107944d10796081e2105101d80464007a8001801400140120701e0507003001074002d07410081d52400d1a0985d0b440201c0994241c0c026074101c0700401c2044112503d00181800c030303940910251055504640e41c0b480030000d231000c410b000590102d02003d00d030000c0840640c0880d0424007104145050b000c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429048084 1250 429046834 429046859
    0xd050f0d05190206060121021306030b03190c0b07051510050406090209300604050303040309080d0f2a06050703060b030c090d0201030b040c080702120424020a0c 71
    0x2a0803400c2051681100701d0b244003041160140b01c0594441c5034010813885001c0040012040040384e040e030811030804810b0f0303941d04002c010025a1004507590a11408141c01c10b040c40c1c00d0341d101c2c060b0301c020800001c0d00c0a01c9140545080c05082500c807142130821030300d4060600a401d110054610500920041c83d611000c1100c00840b418400d240d103425002050303004610702c580c1c0203200e840c801e1854500c1410001111146e103044c62500c0030800050524052080d181610150400070901c41070580c4143ca41d4060907030f084c01003d05501d080d0004040b0340d5000f1684c030400c0445641c0703108a98078104952551a035409850040944608124000748400e031f51030300129140020008562240f142520711401c03510b9482c82c2441e03035040901420b1401000100d0404d9541e110380101035845109910100d11180c2d03911240f803414203800707458425240703885001040144010810307480441da0412000c1c8020080320f03d003204820042e45041200c2000408010f032000c00171510310502d10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429049334 1250 429048084 429048097
    0x30c0c150c0b09070b040302130902030a240903020d031a120f0c09070f03110906120406050106110a0303090c0b12101d0708070c0210230c06060d050f0d05 68
    0x4501900b692a402d20702ca540d00c056105031002e204003444100090701d8002d404a004c3c1d140d1040c04a001101369000070704160300c0d5082190364481c5c42408200e2100d8a0381003d8024042c11020483c40d001510044d540706050303002c0ca01010f440c2c4000c148a801c071000040c0d4000d030301900080341a081c480c9056122038080c003200030b1034482c03a00c420f03000b4a00014018020140c82c2c64a007c20040598214060441c8142800500508000803d0191580030088c01c0a1282980070319807803c151819006848044c2d0000c01001004038003d000c903040411542801c40c2d2609001407031600c1494103580d1115242d222115456010844070310000014003a82e01c01c03070b9820250070300d054940402c40020840d407022084051806000510310501400f903141c0c028405041138120f0340c0d180d60005201d52680308141000469541c0012207005c1c6001c100c510f09013813184800d080c0a4008141555144000c00b1284200e581615020a05c1001d200341c08a1446d401e00313555112050f0364015002d0351160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429050584 1250 429049334 429049343
    0x10050a060e0126100e060f010f1e0302060d1b0903080304120c051614040902030309011b0c23011806080702010f020c1006080f0a030c0c150c 62
    0x1000151016400340316490a5500d1000804400c0c0d0800000380000c0304607900d00c1d402c0c0c02d4401e612030951201080407110300e210303410307002c20311901d0182520f0074079901422130b0380d40b0007262005000b49640b06c0034900c155191070306444900b080c035245c100c0d091046580007940085c40003d1080b88140250040038220140104101c0440118402283c1b041c241d0f01c8080c103d000c0c1840458002003c10050b10190b442a14141e5048482a12000d0030b1110002101d00f1904c0c04140801044015045a00700399008490070426400d103034011944074454918454100842c15079080b40007034640c808105000d801c1000c1f45181c035112002007042c1a0340100a200300c01004648040d558800c2c02c60300c465450100882c0e070303000d24003481a6110240901130000303554880b09855601c007400c2c8060880c80b0302100050021404540035442201d8894000040303d400044985201c0640052405003466062811100c81c042c9401d000c022845a40c02001d500446011501d40781e6900140b00384819024 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429051834 1250 429050584 429050591
    0x1413150905180105102a11190f090e070e04020102032b05180a170c01021305040507020f031909090e0105071e09170a0b01171c080f04050a1410 63
    0x51042940e21419482e200301003541c41603412106c600c1036948400c1390703078810240c82026001d03a00004505220108409a187c9020707071042002231020079040c40100300780c071401c120554401c004a9201e403824002c10407942880303808a001c59100700b080701c61183c2d0081084203124070028069000300d540180c846d0380581807602060174000c58500051080d07018070700174410402c8541d1050b0205040f00d460602980c03081c418814012028001003a6007603c01d0025100c80c0c1c1413000700421202c000d80020704641c000504d03c28010340c000102c03281e41c1400d0310140c00030350010300700b26012096030700305501e481e0500c98801f143c614150030040c012121a10b480c1302010901c804420070395038001898001449140c41002080180200088210f0a80054884e441c242340c46540c0b070580280d10005024071003890903007040300180005864039019965a5282c00d030345407401041d2a401034503980200881102042c10450104480482c1e298046e42d024481d16564000d20b4940400e0785001e0042400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429053084 1250 429051834 429051859
    0x60504031704092d18140a0204330605030c13182702030709020f0708030108060603070902030702060606030702150a060504200301090207050f07080d1413150905180105 74
    0x55500410080c611700c024120b0800144d0349600072009003841c1601220301402c9202d85c00f60710741c1e000d14038120180c2480d000c1c0e07040d045481c007030714070500c00c100170405040d180083c400a94031800300c80d001420b52407960303110260007242c6020f101c007640c0000355845000304c48140640d10354126904841826007607038a11b040d42400d030315182080b01d6000350706400180041c480c516441d80680151a8006806800c15016a9410520742c0c02a040145998080010031050340b50411410003d4402240b06600b14209424041c0d610344019015600c110004000103940c64400c22522100600440041e401da04003c4800c00c001d0000d806541d0145040005581c6807007001c98005205280c0f0641d003603c0c1d0ba05e0903405034003e42003441c00b00c500e405081c4072540c65210420080029284050203445403081c403c0001e07000908040844d04114818442d02440e040c80203041021510160032507000203c0c25401100e1103001904401da00c1110380c811b0320b10413100345070000e050f02c2044e10031009255 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429054334 1250 429053084 429053171
    0x210406061701091203020c0127020f0d050303010e0c1234171b0c0606010e01031a090901020c030f030411010816051e0a0806030d03050106050403170409 67
    0x7011070002a0000312491300b104900b901c41d60080003210a0440002440000c541404070341030b000050128015079001400c105500e06042a80c60070300e03044440d2141e1400075510315469010500c070b118840100d25000841e07000d007001c1290900140108000d03e01d15080803644903410240004605800518490004035503036120403907078044d82503e402d40185400c00e500c2c1000c16006141c120240f03a80c0c445802070707210050140000308110f101600f0741e0319001c0001000710030701d9507040d130400d070902c10156074400c0b411154a40c008070583d02c260302030baa0b50401034068030440821045d1484006000e40d015804600610f005620a02031500241c0d244030045035481e000381d600b6070304000c1c00564046500d018200400040c401d480c400d03c004103105005c5a01034100c03860440102d031403041000003926084c0541d00c0e0700c10880c1002c00080d41032540040c1113015038080144207241e408500c0121410841c01c1e203000340034044e824403840761500c0c2d032090400d001a00c4c001400010802020b00c04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429055584 1250 429054334 429054341
    0x3020d0509030307110a1509061403061e19080a0302070504140c07143c06060d110301050414070803040b0a050a0e102c090c210406061701 61
    0x90300038011804d152481c2c41da06207651000c0201039102d004183d0001c1c000c50b000108240c044042c1c0c45000e4002d14022024050950107000921504410010400c042c0ea5a0796000300c0303403070400c41d801c880d0a242000300342c1d44e581241b2000c0041c0001c1400041004000504406882c4203030709541550755204244419240c440c0b480110a5440e9000102c11843d04070182c00c40901468140c05804208200903040c4003550743c1420300c03c904032040310301c0400d422862140050340e644000f6003c0450b08522600e4910281440348500c1240f0807030414402e0b000d10703038844000000d000b04610304091809000040003440b011803903001e203031000a6495000300944003222004a1003138540011010100c46a0340582c00700b00501c00c480203c80240d0b02c0d0751002550400d184e41703819280d0903021141c25003401c500f00780c04240780851540254281c40300d078a401d0b04030121044440e103d40304c081d0301c0c00c0e9401666000c42c102044c284200f00030b11071070790426000c55401000000b0750a0111248501341c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429056834 1250 429055584 429055597
    0xc0901170c093c0408030a05130c0302010e0a09050a0921081f0e090615040209130203041a0705092103032404060902040e1018020a030b061603020d05 66
    0xa043d109041c404200d00f089042030403040110107510302e150b200d0059092002c0c02e54040c1c40390000402000644402842180e030400782419000f00c40c00000c0d030310514400c000b4003000781040101400d1106a0f00c91280c0e6101506d40d510040c4818580802918004d01002d1819141d400000018840300c1e03800484005100045907034810302c650710b560501c004c1c5c80030008081c0b502040c40c00002040da650802e094098054040a40724508007080c1c80340c141d030011101248560300c104812011903540300c070510701c0800c041c407000d62666154200403100086a45004020000074030400852640c840c005001d21607040355240e01c2109402036811300e0311303496034141c1d8041d03004101289003002c0b000549403580c02c00388009a001404a0041000e40c1c070641e1180308590380214080c0950b454030400e0aa00514038040c2c0c2060ba45400300c45002e01480001d007140c40d640c0007034205112031003038000220f02c0340060702490740c58102014172600c0c080d642c001a8014042c0c1c0620b03da20343d01c01c4044840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429058084 1250 429056834 429056851
    0x5070b0709081005090c0402030403020607080f1603050a152c0c07140703021002030a081b070318030606120209090f0303061002070314060412031107140c0901170c09 73
    0x588000812032030f4001c10015205020310310408001070016600c0b80021071195100317a0140ca420304060748046c0002c04050040110a04810b0411000d000d018107101c4030500d01c2e01d404075a079180c80b03c2e00300c000d0840310343d1680300b51211b01e008101c50800d1055120840209000c406076501258070b00b144440d41551105084401044101c1c0402c643d0499155402c030388405650300e95550361b0000e242c0a04914012002d40c1002c80c0d103450702d5421254590b0f000d480049014000802c40b50002c950344101d0f00300506211040601221741150001110040e640c170000c10007242c0d84400c0c1401c1030350b2000070308902c106074110000d1003d060110361406140710880055040da00c415081048504040d00c001c0d0851103071130000008565070220344054241c2140241055081508000c50f4408030501e0384418103050880c10004000c0305411a85c034640c10000a881022581000d035041590301051107074042e14010000c00c240031113010f5140402c80b04800c0359040480c02043c403200d494111200070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429059334 1250 429058084 429058093
    0x715140c120a120c2312130305070501020309030d0f0209090604021b01091202010605190e0c0c0d0e011d010806060306060f030a06060905220f061505070b070908 71
    0x85101e4500c8000d407144901034206080381d0990086101e0840e204030007544000303605408010800e002c01c400100e6054240f034a154900b5184d1400c00c46816809001400d1800c07000c0707203c06c1498460f00c02d584216a01800941d81c0e03003819100d90344e0342d802491a07950a280341c91008460110103200b00c030240178014203200655610340040000941002128034424208171600c0c01200c0028440e01d107800d8810b07298100c032000b00c4107009084070460b03005540503c101c2038107810700c504508030100c1101c11000401c80190742c3c00c0c100c00458060107407101030500c2128020068a500b0403035501031481d080e40c6000c8106415100000d02d041140c107100d01060003600070a49070304049004651100c03000c2c00300ba1404020b14404a200e500451b0984110707941c540707080c00140d41c4040c07240010a002c440030180030342000085c000040c4c0c2200042c0c449a62002003041c0c1103c5030b04180002d0000c48104404103820f140050503940c07044604858030400800050351440c011800303101910465002403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429060584 1250 429059334 429059353
    0x70803012409180b040f09290105031b0a0306050426030c090105070f0f0f050f060106080f0a090210020d0909020304031e05040308030c04060f020d0206150607050715140c 75
    0x10f8000f010208500c94000f0344904144800c00014090405410f1080f01b411315842400042516401c144842c010f000c2c58441c00100100d660002d00020303482ca2045450301807020180000300230603401e034002441c00b41460200300601c03544075210b8880403c3c2c7c4801c40300d040b810b012802c20510040b40e2090031070400f8003480e5207a503c540054140688681c96884900b4602c2c0c654001078a10650225232503819601144104542070028440d141c0c004402404903505003c0044e000d803000a0042041c0d103400c1c00012851001600088012500038100a01460755030030000d450300b45421400c000308080c00c0c00003a4503482403080b603200d117400d640c500c82d03a450040091400000402030b48810003c043c40040702183d007810080d801014034011255480d0f25000380500148139040c0b1142c15034104502102d503454021601542c8042500c0c11205040c48150010b01c00713000703901f0301620f80d1280150202e5034000d1141c0d126040052030703c5240f20f103081d103211200184101c6943d40e40d0b40d0071402c1c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429061834 1250 429060584 429060629
    0x30507033501060f0306261f150e040507050402030603010f0f0b0f270718060306090c02010903170612060415050c0a0203040306020d021c060302100306141302070803012409 76
    0x1c412a00c2010050303c001a0441e424610b18407189841d90007100d668850b0f0002c841c0d09d03450350400801c5508120a410f290a80710071307849112500c20180120b40000006400d176400b9404181e100c2040402045072280c0c0b04d04800041c101e441c04580500d0b9003221141080c50000b0410f501390000c540c05400c02c92034420210b403441c43c0641101c080c403480100e0b80040c100c408220b040a03080640d00041c2151412003680b00b581d44518a54040d039140c80021808283d0111640000c5041d0704002440340d280d603004600c074025100d40e0000305000381c0040c4030400008a400da10101030b0740707600344207544541590307220502c0f4680e024405a84200710030400540160003603c440e03035144000604041c9007803613501c40100c04060f1244c5156540c4000d00440ca410749500010400520b42080003501b082c040e034100301c0207007000d540b2071107500c1820180705160360110b401c002d80c0940415229650b44804000071049000c00b651342085004504030600c0c03142542004403040c0104414a01c920980c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429063084 1250 429061834 429061889
    0x309080a050c0405150d080f040e190c030b030c010f05041a0304060b010302190e0102071a121b0906130504060815010501080c0a0e030f0d0e0418030507033501060f0306 74
    0x1404048e504041c000007510b05819036a075441a02440c45100d034008a2207442d100b10317000036010781d091614065484500f91000070b400e03080300c442030030081204c45000c0003e43d0035000340c0d400316001c0701004a140d00014108400f03580240d220f418103005001d080c0340154140e004a1116a610482009a2842043c0f01e01646000c03440d040c0140c841c5661154640d00e9803105002000a15000c0061840701c1c0c1c2181780015940803062030040808500052040c0744e042c03007222901445004082900c00407800700c00301040080c04018010451187c1d1444811f0300c54520002c00c0300c2c101c0a0000001d00c95000e290494410004010010b180504c6424280c0c0c1c800302d0503042640500c41c2c803103054580c03a020801c00d07220080079190045601c10810400007921440c4810003007941c0d12402c4100000c2e0000203540e445a41401c1200c0d01905d051412041d8848604d43c3c8180740380311243c0200c60528400c000c5042c2e400603a00c07c2c040301a0000260203865162048204910101a501424004e13850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429064334 1250 429063084 429063097
    0x180f060304022431060e01030c110106030c03120c02010504030807030e1206100623090d0c0b070b130c2c040c051c0305160309080a050c0405150d08 65
    0x1c2840000b000e403c0001c0c00690890300440e0640d00c900c590800c000404034002c4280000b081e60040219818a0002004140a5561141032603100d091055140c0d000301c07400d035200c425480c02001410b650b42003204060030240301c1941c2100c0c9240e41440d20902c25140c0300c00160b01030312070700e14040c69550b030014076600c40d41b01a810030942802030307a850340e201101c00b085500030340c0050046003042c980d4040d10702c20a9009400f80400110980c41d00d0703081c200c4000514940b10b007666118a10f6101040680e1001c42d4018442c102d69580480c140030204054100d0034090540111982e59004c148400c00041e1400034003445003240080001c02010852414103120340c02210813024800300d4440410b41c1d0640d411250044864028003081c01c00e0741039224050982c10002c0c081c2d85a54402411504c12404144104c034920f10441d011325016101d44001083c1100440310031388144d0030410303100d42e520640144150306103c007107a03140410208607800c1070001400b200340040a9541d90310300e0381c080c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429065584 1250 429064334 429064369
    0x1090e03190f050702040203070e0a090605010c0b04050c060c010c03180f0f03030b0a0902030105041a0d0308130c0801050a0c020f10052a0304060c1e1b17180f06030402 74
    0x30444d2000580f5280061802040301d500c4003180c07040450100140c0103c20340010712440c0c50030b001002240c0c1e220000c80e0f0005e800c2030342c02d00c0039110340c00c1c40e90414211018458225000044040b10b13503105510102c0c40010b50380e003c00c00d031100c9081038a807070f9a00560250003940c1415698010541d54000002001d10070304001031025020804a04102141e81c0b040d12a10b6002c001009a41401d00030545041d8419102c0d81c401e10480e00001d1035441c001382d001d81000040f8001541005050840074409900000e91016295651f8055406004200c828118031030404001c204a1400044c6c004410780226000c0c1104003c030390018802848010013030300301d00d1140c000c08441c06068041221007a0b00d51420f0558a00d0142071210603243c060009904002d500c00040e18002e140c1240b40e13600032a285840251560441c1c042142004036410240c14443e180ea2611010130b4404002d000d1418044c000c01c880d20721101c20084088000740301d80f81c00c03010810000d001840e10702001104142e00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429066834 1250 429065584 429065587
    0x15140c09090a060f0b040e06040605010512040f051c030e0c090c0a0c021002060907060516060f09020306070f0e190e06030f0609011508011b0305220b01090e03190f05 73
    0x1680d1303030308014090940c001c00c024400010240241c83c0d011a280b5400303081034505014581c03038480000e000340b1500e40c914034401d10305400f240800c080f0301d4140c1c0c101c0d50003504640c404104a50b44c81000032703445a0020210385030410b02405540c001ca607100c030100e0300801c07000c0d483c0d803242c0b28604590b000102034010001134000e20300c01a50307603200c20084105981d00905280c030700242007030b161001581101060180901c42c404d000300d40400b066290a51007103000c10701105004100b00501f400d881e009501d8081d070304c200090591f021048008030f20166641c4612500780e04144003483e8482e0000c42c0c4101c1402d0b0081c0503042039a40c03450703000000a030031075406050703e01c0000e0074100195030712034487c0d4545440b00b28560f02e290403040502007800c02006029103440b400c1049092a1a240f401d164913040020500b000244045540c800f2110b0440c1503144c280c50311202a0350240182d0317074a43d2900801e807d8502c40002510607852581035000865007095034140c850440d0b044502082010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429068084 1250 429066834 429066839
    0x10c1a0a1d0f071e031212140601020d18030b060307050a0605040504050604020a0c0314040f03081e040e0106210c02010b0a0b0307021515090415140c09090a06 70
    0x1118070200340070304209009060700d000242000c42c1050f659600180803590902504030030702c1c4070384a11008403544030640222080429400b9941074420440c1d4010151030b00d01080360b10880300c09010311581090b820381f803c8600c09030054a603185004000a5100301d4043d007400019010700400f500100006c0841c3d9003566642c00140c1c210f000d94008100286c0e001c0740030820f0b81403d0141d035400541c101c40550070302940000052112050101c090f0402001d05a44032505008030f08940141c030740d10912512664076030800d68250340c820801e40441e20b504c41c140385001554801910107a541c0c045840405910740082100e051401420b00e101004521805690b468250b00c14170000f02c8041d0000300702c00d8000b2080218641d20340e44404d01c590020030812203110f80c00f00740c094003c1d0f000e0f00e108425859824038118003d51031351a0360b0b04080744c1c1041c0414006a80f0314404940b81c42c01c801d000920564143c0c00d44403405076034502190f0300a102000c114038082080c2035000043c0d6200007940341d07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429069334 1250 429068084 429068111
    0x11062406040e090a06060e070c03050d0603080d020c15090a170f070b01080c010801180207030314010914150a051302090d0803100801050f060d020a0e04061a010c1a0a 73
    0x10741e81c3d0411640510340c0c1c102040080d005c0c43c4001c183c6903400304241e20b000b85c0003503c03201c0c2d6590000c040001c005800411400586d000001641e00480c0060719030b031004a0346002544070810980c11449101010ba80d601c0c20b81095074818418200944506171069540305203c075403080c0031004c00201480000444a0404060a2143d001d02e007120300315450440c40c2818104071102403410081d10500500c0300781065168100c0014600c040165501c10070309040b03008100350f885080da9540010000101c41080c0e401204c90000741001341080d5849000f107146103070568800c41e642100003800200200e02d00058001d001104408001d460705600000140d9900329009045400c03443c08001c2c0101d1070510000080a041000001c000e0340c00d020660700b4000d00000d00851184400220314421511131198410061800303022840b800d040a01d03103200030703200b03014201c0726030202502c0c0c00e07041c1e61103180c05001c56900000200310f013294240203041903200040003004940c0d100d588120000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429070584 1250 429069334 429069359
    0x70233100e04060f1a1f050c01020f0a09060f020c0d171611191206021306050304120f05070209040c08190c06080c030109021305100e011106240604 65
    0x5620582e00040d4100070040d0074001c0301c1030049068650340c0980000003080e151134440395082154801005041781c106c1e282115280b0590b1030004040d40080b429100c4591034070080e00c0b8450481d02d0304059903407500070071a04610302442440041c2c0c0702c0102a41c04d42002280040c982d4011a586d64482c03a00328072500c0307185d100240c0980e1034180a50ba1100740035440302c14010705402110746808148600314500b559540c0ba0040700300e01085a18000200310481e07045a10308100104945a0156540c1029000741c000304c0b400c1c0c900b804811842e07100070344a4080d00c440140316840e0f45051480d142c082c441c992400030001c4420789003070000402c00000800c80304594807000428031010405615200b5580700b0554040d6050001304002e00007800b1146042d07a040d5072003145c005072a030b1040b540626207505c05034400c503080307409100802030050348020001c0b005030080e280c401c09144c800007415070b602c01c101e41c4115000b0301d10010f110b820b03604401d85800088001c03c950b0420b51540001c0108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429071834 1250 429070584 429070591
    0x20a0516080c0c09060f04020906070b0709030507080102040303080c03060123070c08160b130f030f050615060405040b040f240609030203060f130c0e070233100e 71
    0x1c4040441e8406010000f00420300f50361070309440940e0903007044008a0f100d440d4040b200380c82540c001c0343c0c9601ca512510140c90040381c10824024517410b01080c064104c120350b0200b56000d00030140003049100c0140211342c11130703601d0f5440c083c899603024440007041c2c0003d051035042040d0400207a101a40381c0e45858036010807241c5040ea61000c61410070315903c502e030700c02ca100303412082c00c101c40340740d8504011046545040342203643e1b2032203080c419a04450b90700703c0c3e4020510300d01c1c003000740055601490030452244c003c40342107441d40c09407980302c40c00102080e03900c540200002d03c1141000e400155080b080030b800861510305544110086c0d40c544007c0d01845000f042d41c1d14190807040c44590010403090500c2000103056401094403000000c00242041c9204804141d50b1541460403001464018070181c079038a80784c901c54150403205449c800c0c01445933840300c2c0030142c4c1c6c0000c0542d03124603003415407407034641c0342c075a01001d040001c1641c40146031481c00055100103100e07000b8030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429073084 1250 429071834 429071843
    0x5070504090c03200327060106120b0d150f2a180b2113110f0a050d03030e0a1103160b070f0618051501080a15020a0516 53
    0x45850810700d08100301c0e403401e4692030803d401c008001d094080c40910755110300001040e16940e0703564000400354800f4440c5040d00c4031444000d6140c03003000010803064142c80083d92000c1c0314850f800909810359050543d41607116160103000800a03409e025000615038210304040380028503c07030700b40110703082e011821403201d0216510030300815400b142c4c0c9405a2460030050500e00d0a00e0f1200f0302c0b2a01c500450060f548001804480c2c9030744900800750501d0400700d2a80ca41c90141380c40040d050322103400301d40205e60b503d00440686030090401c0741f0104050000c1c56150b22300f06c100030304040c8860058042c580c0c2c4481e0030100c14000c0c42140506401503442c0c8075a85010000d15241210000b030048070288160014451901c03000212403240d50080e10b2803e5071922818400000c201d00700e0241c4062810b080e06000700680416010340314001c000003403045a0341c44010540b0381398014801040c9500a040450f04292558040c00040300c5138582a4182104850a00384180404100b9103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429074334 1250 429073084 429073087
    0x906011107080105061002010509190c05040507030b1e24090d0b040c06030c0e060a030e03030109060509090703082706130e07020703080d090317040605090601080a1e0302030706050705 81
    0x2a036810711280000d00d0000c030344009c0100d0320301481103507121440131400d01482440104004180b1914522983c0601001081007210307050000000d40101184000f203401604c5003d16490103442a03e46898086005042043d0b103006030752070044104504001003015000030300240320251030f800d6030511494485c00b90b001c2e0380d0505c0e00341142c2102c2c40341d02c035004041c209000c20480302d170f101102600d84541541d18507190100824250041e0440449620051001000002e450807040d0400700c00c8642c2542c1401d003984840c1c04068891070035010140880c401040b4006101215a03014941040b480204a80c1003042c0000180c2c298800d000400550a0b0514103001d07030003d80c140c03d0340026041c0010410223140d9600c3da0164003905102c82d4180c2c5e03840c40304d501803600030040c11128210580c100c80080c54a0701d0b0000040205039014207071807003414000b042c6001d0010703000070040e400041d240b002816648190b0303030041190100f00d04502084c0030417400a91070b80183e03070043c6103548030603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429075584 1250 429074334 429074341
    0x20a0b0d05040317100b1c0c030b010e040905070b0c1002030c180102010b03070603021b010203090d1e09090b060922051f090f0b0a060305061003020403110906011107080105 76
    0x100440040c003c000d561003c10000d0200c02420005d010046440095241c0d854000c01c5140c4550203c2e00c41a03040c109040c806014201c40d407650012800c0c036000d07255450030301d1307003001400210b4001c200010002d600c032500500c40f403050040035104195602088038500141a0340c60010b90f0825118076041481c017250109180d03040c803a11030008032003032008000108410000a946280c0c0e441078030181503000803a600e400b4000c9064640010f017240095580e402c040a5107580c48900074100c000003800030101400a4441807440ca2712040350ba83d49100003802c10000400611040b09203a511039005c00189255880b09841c040c020309451031940c10a904511104082d01c000401c4011520540000c0b02450345275400d0541c2560f100a00000d2141c00e81c400b01c800610406800300d5200c0d81d0030717a00145032641038120612550054400d000651171340da205500347d020328040240b52050076944070856040003c0d000d940700031b051400310400c074412841e2500380b8440d070300300c6030085e510707103080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429076834 1250 429075584 429075587
    0x62c13050403080c070f03030c0909110c0105010e010602030409020a0315090f0b010e1503090a0f0c03110901030c090f060e0903090307170c09040809150406110106051c020a0b0d050403 81
    0x2450340c840d03014410b13580f400c02e05a0f0b8240c500e2a80050040a044d951751400407018031688a80b030150411034010080c09200703944003ca00d40181d4900c4490750700b0b00001007403284d03443c20464100d41c8a5001903090904101001001c5d401c005554003c05694076103054401418456480040c04004000110381d403291030800f003030301c00501040e030600c08102900c900319103030040102007116594407450345036110080b5003401e200c41d070310015144841c1d038a49102400f1342c841d4004100e82c4681c00070041130103501c05020b00214240310141248142c0038080244503207a4105103840705620038001001764a50000c902c89200603203005046600201d4001c549007020011000600880c2c2141c454180614444503078403c0032180a80c0610710300404a000c000d0008195095040c001f40041c1078194121400e0444e80c00c2446030314002152805200c041100c10b221f020251280176060b82040d032001c03200b01c035030601400c3c0100e80001c8061400140e0100c0440a0f04520b103e4240224150516040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429078084 1250 429076834 429076847
    0xc010e0d1e03060303022d0d02062d0103020d1a010609140301062607031a0406060512151b13090501050612131103061f06020304062c13050403 63
    0x71a050501e040c9051001c603400203404040740120a0811310182c8009100404002202800450500c1107007401c603011a00450304520501c02e0115200840c1e010380000640070340140c40d024003420342135006002504000744280240c2c0d000344005248402c140e80b0040f001c0009a0003800000d07400344080c4519921b00f400c100300400220020300003142040c1c4843c5565280315802400c40700100300030b40990100f0701c016402140c000030710447c81030801c159299504001c03102110b62920700000422145040301c10070304401503040040c9040000d0038800440316001070f0102103240400308a000c41d601c0060f00400007a4419880c0007919407034100540180d41d410781156100d902c00303010482c00282c095a880ea03000700440c01207200603c560401280725941d001c1000d0701405584100904100c4500b5185408014850707164030195850b242282c590290f4090840041c8800c01803030240303008511600c665403281040300110640310b200088400c6100261402c01545920402052540009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429079334 1250 429078084 429078137
    0xd020d020708070e0c09010e030d0504030b06090c0a0315050a090905102702190801020a08090c030c01031d0109121209020d0609110604121b15050c010e0d 68
    0x50003400f2150501d00d8040b04050001c2c45200000400f08034240c06030320403551600c0718000034041d1070880d00420300040959102c2c0c0003d8549036125404100c06092001824bc454022420024102142c8103c220050548080061340ea40602240441d9642e00c010400000340b44200c000184040b0324a0060304000050701200b02c2c00d45001c1402c0781914504c0e40c3c02c1403140003086014010055031001610b003110f00511384481e60320161003c54101015401401c03000d225464403140c03035a40706081c50f03507030b002080a0b54268000e0b003074506040d4017030340140f4409000641c1841181d0800494942160f01d0508150b607245a490400140d15800a00401000c1e02c0013109101074034180d008074602402c000c0004061542d500c0c100c070240500f89040820440e0000c0800d41c0e0b0b0341d52000c00900c081480f2030240c92990821040070240000c15950f241210720003100b46018016580b0291200d4016800e500c0c100c2d502c610000000c074609001c0120101c0050311045840721a400da010b0400e124003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429080584 1250 429079334 429079349
    0x914010509090303190e0102030709090b1e0f0103060806130b100501080403050a03020c0f0c13181212090303063605060103020c1009020103050f01150516050d020d0207 74
    0x401489201d04020040745e900040903c0007407040b86020500ca402041c80002040c40fa510200600000c10b5009180d2002c5864500c001e02001c5408010060058461606403200c00700155010304142054111545944014140000e100740d54110780d904000c001c8410401c2d910588060004102c070444410741c2149508402c0c03d0340b24108000a40750940c050300107410f10001145540032a480390701202c0d80503250310142c0e510740401003080c641d0740201c0c01c4810300c9084c0c40ca584034200031072885020005c59013130b85000844080c50700c52881041034001c0e00d208001c240c0d00d6402c2e0f2a0303201d01a011555200c1d07900002c03064034100341c031011004000c03030b41480c2c41251030041107030b4510800d40e40810100e90b0340001e0161a2400141c0091240c800c2d107407428012081440407945051f80032240c614000c0c0c9052001c0d58411810008600c0309015141c1d80d00d262014031221035100300f001d4943c00c50051601d0084c0b044130746850f840c2000c14611603006034000d020f003038980e6605105250080c5100b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429081834 1250 429080584 429080599
    0x40929070f0203030c0d0e0a061d16150215091516021b190e090f01060608070c06020d0203010803031609080c06090a093801090303110a0b0109140105 66
    0x44a4025200d04c00504001003000d0049815054040d0385d0b40a0200403021104623440040e01d40b800760050902d095071840d1074212000c9034940c4200110746c950750440300c10503100c90541041c0420b0003140c1d0106d0700d007045229400c0580c2075050100c02d40d50160190b04010b120281d00310b0151440750780000c002001c917950410001c182c00790002205503400d00c040e40f049070348203d1080403034021a02c00110404032030012000007842e82003055140e000d8010901500c1c5641400d035049426140c0a204110000d103601c000940514401c1e986040c3c1d00f031103040302501e000c2c0340741c3d243c5013642c00c20303040342440e0b40001042c494211809405c001400300142484885945858017694456110039541030040d58000756018482c2e0f00c2d103103510050314040b0410400c80000e0030040c00f0303c160400b48103545d03403081440214a000c43e6aa051090b00e0141d5030700414608595045882014592103015141700c0d00c140303400010310050095020380f83c03040380001c80098002d0507541800d810b900c0640120381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429083084 1250 429081834 429081857
    0x80f010605060a0c060f0f110a140702060316020a0503040f0e070914060702060c0601060206180304140411071a07140c03250606080a151404060b04092907 68
    0x4000740213808440d0820000901da0118500e0302c005002010b511000d40352a02d40c1108040d800903005d00441240d81e5240c0000703c1c00c0707581c5184103104805003e5808402400000c1e11040841c0c80c4481080f41441a100302c10070704d0303440320f2035908280c02517506040d02e182c0500c10141e0004071540d0240b0716250071072080d803810340b04070203545401030030f6405204001180019034803000112040388401008503500340d030390340600075111003050301d0800910b80b805103103c100f0710300001681c05582d0070045010700008a002000002c1281c3c0c2151021082d00744407e00c08522a184c0c40ea603100e0b0302c200d4500d02d03880c1c906001406a12103000c0c0c070030070150521024100010000984842c0d88090780b01a10740b01040e521101a20103206004050302e0a08101003014240401d840ea5403c1c8110303412100e040300b01c0145019070f459000c0a6910742000c100040110755542c0000c14902000742000030002080c0d200c0308400c0b0940e076881550700d01210034040506e03503000441a805400c80c94030261100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429084334 1250 429083084 429083087
    0x170906070e040c0c1202070b030a06080111030c04060c17030f0a0b030102070503030609040201140d0f050609060d0f02220516030203040515041703040308180601060c2406080f010605060a 82
    0x81007040c0685584421040178151074002c12031740b40941040d118654407803600c0c51007407000c0d0060f4040d07070800d07508020200c038604024205481c010308070071015506040c00c00500319011400640d00740c40c3e29a185000394041142940154080c5028034401011071401403282c009803098144220700a0788108103138000314002109898009a00302c4074014191170b140012200312a685066a0000c0748c00103078458550403990000207245c000302c1007400355903541400c10550003000c5803055003101072181003d000a00f08420181c1341807000300100358050a002d01b0601c1d001c030341c211101c50707241d484060010307000401904443d03d5005180075441c1d8034240c0d503000d8940540140d507420491901c00424100700c1c030001000303402d558940140e51030340380505005140c0d45041d10010100c4103003c8d90503081740130205800c0d0586c0d03400d403102c003502c403c41e546402200c404105200c4a020140403610b0714407181c1e000700801424400e00914496800f822102e0031142d03d035015500c969010400b403903905 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429085584 1250 429084334 429084347
    0x3040605072d030e102102161407030506010501091a03061f02010605031005011a030910050a050a0b04050103170f090405040507030201020f0c0a0504020c031905130f0509040206030403170906070e040c 88
    0x80091b0340c0c02580b038840d0100300d40e00c04c01041c400101040f180107030015919070f0004800041f203014104882559903940010b440440c094022900b01c2e604800440b00c5501c0548000e40e001132000c0d005115803506000007500341c25030303141c0c100c0c0140d4403600c1c204030034602001000403120b28910100501d51400c80300c20000b00c5414080b140d820300200029010000501480800e04221031041c80245031110906000345000c40c4c0800031a032814030324858505051144031b040e80d505c07400740b0300303440e0b09640c81e514203800864400e13103081c108212070030b030b551141d001d1903026910030402413a81e10709601c00a0b083c1090b044481a90317034032281915020741d0360100014120344065400503500c0c103107001340904604c1080e51080c003042d003400030941c2c4903038841c2c028030300b0111140162044a4131060140c10b001280d210321503102c60050041005458010f0046400c9882414101c0c01844a80144407a1600440728100c20313400150800c001160080d902e10f25110040f071b410080c12482c0d84024041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429086834 1250 429085584 429085637
    0x4061d03100e070b0304060204210203120d180f2904030c08040306020c06150a060903061d060103060b01081501081b0d2c03040605072d030e10 63
    0xa058031078500d141d801e4014010f01c4090301d4402e5080e0b5407032400d410303d500658414401d99030030301ca0144000314000e8501c003120003803d038010040d22441840c1e01c00d00c901c54201003800313544541c2d1403414152a26505200b00020780c401c00c0c61840304015418400e8880308040c1020307140400c2c02104101c0b8007209501c1039440769050034445142811401c00f11098080c03030308010309140c03000030380c00760280c2c0c000390710740c8a810032601028886c0c088005002180e0010f10969000c80d01d503090510000da11a003014444030050400c2d0420904203644891501c50280d10917102c484c0d41d080f400d20696440100b1542c4400f501d04140d050308400300000f0f02000c0010207040000311200b450351700b8460884104c545100d5044403d002d64844a02c9400c120034080b0900d2081a0992001c0194280301005403000c5520300d0f240c5504002c0b4680766000d4038400701507001d40f004072072010142d07481e01000407181903a00030386d59041075000040c1071201c60044030701e17038070203010102400d1100d2020354506800b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429088084 1250 429086834 429086863
    0xf060506072627100e0f040e01020415030e150601120b100905090a05060307170a0602070818120d050d06050a030f0506011e050906180c04061d03 64
    0x100c094401e41c807164240003039100c0720103004000f40b007041c01c420103602c850003030018010102040c86004108054030054400710b001145007201c0381e1403180307091021020290006007000c116000d1007031b459030880e8019003005070000c44a040b10600660306100d06860414840c00401e084001e00e1a080641100144614100140340b00080c1c420412038100c41140c2c00081c220350310790241c5401c043e09644181c01380a001e005d41c000000d9000320301c1e004850240b000070300035040349414000a84403c0b20003031482e00483c49442d00c2180090001e00c01080150701a9062985900c0700600540741e841900c04400d00c542100d03424200c041c000410440110121400c0490360b62950408800151105030311495016040310381c00424000000c108100742c5202c0c03000c0c0c9000342e89480c00c0800e40301302d144e290000895030250034440c50500484030391b0002070080204580390200c2a500060000440d50846a80381c00f040801610b81c000c0b00c052020020217480d8000c14200901081c1c1d03803403208101c1038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429089334 1250 429088084 429088103
    0x1020a09120317061f02030307020d03090b071b050d0c020a121a1b0d1d06070c3f0801140105030c0a03090b04080702030c1f081503031b010f06050607 66
    0x62050795500350105000607510300745c400c002c01000010f500c0307802c221240805405010900b0110910078400c2d03403007403903106550130311a481d940c004075488480c4030303007410907800040c01d00d00100380304101100e101000c0c1c3c1d40b0f005081c50030748107018848481d80d0110f500c2580c0603242400041407a0360001600440590390581c950343e12424540b040c2503c0141809008006100340025203142c001260307ca034001e6041401031000401507546000c2140c0c00301c006942140508006010074810070f6030307030110100c0c40070180c007001442c015440c82c500d4000d040c0102e2000030003106030440c100d140140702c0c0c1e016134041145a13000103010380c400100b03240d254903030000380250300034040d9004541d07690b04800b0451070782c0341c0361070000842d40c050201644644200c4080740310300d141c45c2c441c640d102500a000302c5500c0c040c488090300c81ea41b0150a028070201500c1c114803041c0c0b020406011083c1d100f0160000419288440342d08444003441c002581504104042c0483c0e19854115a00707140c2c00031840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429090584 1250 429089334 429089341
    0x509030708010516031b0f030f0c0c1103120406050304030314180f030306010e0103180f1506050907050a08090a0203031603110307030509091f0906030203100b03190c1701020a09120317 81
    0x220300070300327950322403100140c5418a041d91a950007241c00107000e02c6403030700740d4501034038104040e654040441c2c42c5c500755108000c140035032407103040590341291013800c0c04280440706074040d90055108907820300707446c96040c000ca01d0720b41d01000008003506161001d14610304003100001e1100c2c09a004175170600d521001c02c12018008071800c0481d0030781240860142112514008452007545040503c00500740540030480f40362074525075020f42e13040d45480d0724100010105881d0000010a2103505005042001000d610207200070044414030111501c40c8503854500a45820700048001c0400d5109000c00800650850101d80c2d483c5004c80c0c0c00449030341e40f840e15100c209030724042d020066203100e0000070407000a030419019a80f00b01c050341d540d00c41c1400840203c56504030500d50680c814600301c1030a03400c142e0b4000c020382c0196403411180e5191174a040091400000804241e94005a10310020b43d000000030f0203880c5c0b440740900042242d8400034650848d403428800b4814184010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429091834 1250 429090584 429090587
    0xb0d02150c07170601051e030604020111010921110c0622081002041a2d0f13030b070503040b0106030209040e010c02010603050709020408060a0c0509030708010516031b0f 75
    0x109000b002210100480f00f00440c80c10307a00c8100070b1040780e004450203406499403080030120720401303000150040c60155a582c00444000e0701602070941103541c1d5145000200d0031001044807091007403004561100b80c0c0102c000e2503000c6c403441148181d0082881e1203107075510380b011105c40f22224400141c10030106451207503450043d40c40480300d403244404c0502003000613009031040f90450002e0307803140c1c500c14102843c0d610980700c2ca20f03c107600e84d1800c01c1c3c0110442180109422070f5503062420803441d11810761042d8000d5086104041c0c041c50100100035200155a038070040500e0481e05508043c0e44011400106008136414160049804180c5440d260301105002001c8002440106110b00010303000f00008d000580c0c2c5405000008590500c040c000c45003118202d900808042d030f20805440028050410318808010080007510802e50701040800c0113490164000035027418902e00303140d80c1c4103440030354205060615a4102d40d40f00e00b00c3c51144110314a04200354111102c032030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429093084 1250 429091834 429091843
    0x50f12031602180103150f0204153920150c010b090703090c050906130506030c0607050f10110304021c061a09150f0d0305040e010e0403030b0d02150c 66
    0x7601c600e40f40b500001007804041c410240c0f041e05102c3c070820482401010090580c409c43c061007030500c05c1c0700310740c0b2080d9100340340310a082d101d81540150304e000b03c00030001c0c00801a8a40c41e41850150350007005000c0c0c20841041146035050840c0742001079100840c100c4205050510348124001c5913101e8000c1003034015030483c08000f4134095031403922110150013065400403c0d1605100d054021032142000d8048600800004010f4400d0000426010016200081a551300b40c0517a0701c18094681311500600030651248000c3c101c000b2218502c170b864052000c2010000c0b6050803403202c050740301174040f84d410503010b440004144981d00c4085640008c03195008001c6407a29041c0030950701c2d03041c018500c0b190101c44c1030604c2d80340d0b1408840c10b04884103100b5446180044080c8040c601a4031480d58107200f400e246040c6607450740581a2418241d010080090340c0b9070800003099803500c1400e030207a40c221045543c0d5055500403807521440307aa41c05488100c00642501008400c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429094334 1250 429093084 429093109
    0x21040809030303180607110709020c12030a140c040303050912010e0d030506010306050901052b080a180e1006120f02160308070807080703090c0306090b01050f12031602 74
    0x30704481d603034200404070070b081e851008214103440c0a00c0000c100240d2290003250581c48042c0014074142e400c080680c00207500500c03894100744551604155690355043c059440780c84042c0d8002555040d000b1945140ea00040c031400001701e0400040c80001e80000944854410540700107032820007070000d160040101c42c4010480d40b044903144031000368103401c003900c50102039a0a0005a1780ca105020000400b8007543e40d01003242003402c00218804480a0044160040a41010f45007174541114943c001e00740040007584000340310f4141e00e2000409001480d040010034000d1405c516007543c415918007642c0f041150f49090780814034040e400000711301c800000210342e601c81858103034aa1010708102100811400f000051000d4044e41c2e1591042034591141c20b200e41d10910300b00e0080040f0002106d0003240c1e01e82c040b0120b032a510410854030700c200a11681d035418001040382e000c00381b000e000d2140000d250b0340300350b0010110648400b00940c41308524040c04601c00100d1181148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429095584 1250 429094334 429094339
    0x71401021204020a06090b030f0403024905071203020409060b0414151818070f080a27060e030c06040b091506060a030917090f040221040809 62
    0xc140c006903a10126040c5000e00c1c421182c3d0104c80c0c2e51a1010780766080341c1c0c4208102100240700042014207104622a8403070720a10550710f415241d8001d24035016440300368484041a8501110b075125041d0000300021190581c43c0118600303038410080142c443d85100400030154036070303c1c514040c040d405031005003040c000280f18098885142035101c2c0c200e48580320301c060003d2a00659400d0880303105145d90352a502052801c880c00c50141c0901284400b4150002e000500000044604510445c010201d5a0760108120080e005c024074628024000d19801441d0101001041120b85c404270074003603841c03094041c408a81e06180000b0039107401541d119000000d2000d0f80314001041440c803444c0b080000d07500507152640c0c030583d503001003142c9450b5551f402011490724501400030740740042c101d10303021404680c560355065009241048001c0c2d10a00811103014501d000150011003903003d6900b182400904c0108002c0242140000b40d034600c41c42011138180400c29007107136940c0002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429096834 1250 429095584 429095587
    0xb0f130e011811030106080c070f020d0b04050f070b0d0b0301090c06030203090d08010f0e191401050a0603090506070305040f050f0c040509060f0619091109040606110a0807140102 79
    0x11454400c40841e41000d0340b651140c540024010001c40c0daa0949058620540e00c030302c0745a91f000b2002050780c1c0014015100007200c4101c400c010f03917901340144c4215104901c0e841041c00d2a20f401898081d129044401039080740006110641020041c2e416590304c044010507106504408a8010300144034040c150107031143d000303c0d98070b8141e0025030160000c08200c410650b003500c2c0c100c80040c1c00303020306c1940030f2a039403042200000e8003031035680182e54480040d5850388440080c5c01100c00900d04103410810f5040104410314041c0b000354010207940c1418015000166686500d404008044e54103065076140410240a101c10001140e5070740b01c400c0351544a440902e0550703801100740464400e5007810300141400e03c0100799113020311186002070802c1d444250801007403c40c28400e60020000d491000158a042405a02d4040c001c441181c1d0b45da01d201810b101c00c0d24460741002040c0007030b44454040b244400504512020b4110391036540f68809480c0007480c1111035000e071500d0350700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429098084 1250 429096834 429096839
    0xf0a0b040b0406020705030f1f240e060609030a1b1206051b0403110f040209030d0504090510030b0c0a02030706060605030a1b14182101060503070b0f130e01 69
    0x507880c010000d8508503000c42d07540da0b079120101560341503852000c03001d80d08020b0540004e07074195104255071031348400c000b0032071a00b030b14000f41100307000450410504204140821043c5003040303040b0b030410802c1d5013032880d080d043c002280c0e94a0540ca0000c0c03058030007043e801358051410f103058001d884041c0c92000404c0142c10031001a040a507100340031a085003a041c80082c0c3c40c03608441c11aa4801c411606100040381040b1485c1c58100c5500c0d041902044010f010303079021300040e800c04c921515a161103505001c406002c5910050160f840402007650a00202d001c40034001d034800f100d10344684c0e48610b4030408905501607a40000e20b258103014010918940000156202c0e000b070f02000c0181030341511021080d41042000030011406501c00e205d8a1a62000100490380c4040303140500b404040700890f240001140742e40da64542d01c028816072a03031003802190010101107005040740c9081c0081e46a0602c100c400304003200e03100280303070082c15080d81c1500008000404c055100e82d81e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429099334 1250 429098084 429098099
    0x100203040327050a1512060603090c1d0f130209010e0106020d020615060c0c0a03050105070813030219030c0c080f1203010b03060d0201110115171b0f0a0b04 69
    0x1d600e0944500c030001400d41000c2a440d000d0700b900222a8010040e41c1d1892400740d046001144403d00941088207004d106425604140241402070080d41c1e800100d800050500c0070915038540c01809041000c00c5984040524080b6240e4209a007601c400000751640b071451100e00e40401c1000307403c900d19000011300e440c49104414120ba030b80342c080c0c0f07030880d080e020100d0b1039440c00c1b111070341b000401405108150030282c000d440a440341208541c194800500001d011320000d0340708a40036915441000b49040c1c2c17003240a44c210003032440d03003a584000d5644c080d40318040c8042403180f66a80303081f514285841180351001541d0407600c0d41740465141e004a648800013100c24001c0340c4654440b2520a0b80a18112412105445100750864840c1c0c41048148030910400340d0400c141100b00c0301b000c081c280702317141c4203150418100f488145005500c40505140550162554102c02d00d581711000c5028580c1070000005c03500c3c50050100d1000013802280d803030304600c8005001040116180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429100584 1250 429099334 429099347
    0x60b07031809140a1805150c04120b01080c011b0305070204090b04120807050720030708061302031504020f040e030f0c0102090a14030709020a14180901060207050a030f051002030403 80
    0x10440340b138050000c405035901036402e6040c100c40090441c5e100c0300f802c410654050a000b034100e841c1c418802c5c9096924405402c04480314401542c3c9a408400108201141085048100d901c282082402c003081580003115114420b500036041c403000141c42401c551f01c3c4c3c1c0c081e507010f40d800360482040b0304090804680c1d0030311703d0000c580803503003550100c4c040302d018030142e6507000ea01520503420b615030070f1602ea41000d504060706070107100d1410301042c60304d81840060320402024941401d643c000d8010075250400c58004296400048810700000d078841148a07100300c0c03420b41d0042100690001c1c42c51840c800d8030541d0124034400b18420501c030344190014140084115189190035495054010460130032062255250f40402401c202d168440d0700500144c22440c00d081011043e0f800d090700056010320724032007000b00440700042e103501e05840310501501c0c00d48010921107040102086400303401340405424401d0380301c2d079034081080822034071004000e412000d40d1030b81002d1902034643d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 429101834 1250 429100584 429100591
    0x1906020a17010b0406032c0f06010504050c0f0a020703080301090b1e0303070b1003020d030c1a09120c0c030a060501080d110c091e0106081504060b0703180914 70
    0x46009030021660915080711505940400a006103001d191140c254000e00740e036242c0c4111302e07100c00080c0c04901d54080c0c001070141005805001c0402c0d130003056608241c03058101c1d0344140e10700410710803085a01d50540381504500004150344401e82d0406a1070200540d00082c0f00d01d81c00000854815526003000000308401d4036a081e014218002011590154010458042e807041c0100404a803c5858594000103900d403400391240d10303900494100040f07501d055011403074403841030081245085400728000941c5140f21054100b9a40b1103403107200841c2d00c0f0307281c0000030506107601e10040c0080b00b148440242126200d02e000e00e4082d02801c02441880300501840c0210b091650007448852903070000740000c0c2002c205001d0800414100c050136041c000944003100310303078070025a58100d02900d21078545406a290180f580045288110400d9000720b0030501d017040036092801c243d5240542c9410017052945091150500410003580100003541c14084c03c208848800c101c03d600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 429103084 1250 429101834 429101837
    0x3606070201060f09020f03040b040f200108070f2708150106030b060703090b03100905090f06010f060503040206030903160813050f13090503190306170609031801021906020a 76
    0xf081035a070955035089000d28640350704603000c1040046d0001d1242c00e44240c1c020b01c145040d07040d14a481d156540e04849504504180c0d00c00485280d01540c0c01221440d031140051421920750049a04020300c9090b41c50740e0690304e6134500108032001304540a1007009820707140c0880e03821040c130910070180001c0078850300012910744010210203040c100f04403000f003509522002640c500d841e405101c1c44e40001d003101c0c4040a4101c0228410f407072070082034000e0702404014025440181603c0d030801c0f5040e40700034046a0340e80010001242c01c8000d03250300a804544d0350313440740d481d035620a04510404035044504002c1c0c9218004008840d80540345006454281000a9840710305000400b8814485a580300c081c1f00300f10803603412580c000d6000140b046007583c3c101155602040c03d043c80c2e291030000800d85900702400000015031080c1079030900207006115904006020075200e1082a03254a41c0300f00c1d03200d002e141640204407074482910660011101c2d4a45424198001c3d00824520350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 429104334 1250 429103084 429103109
    0x303020d1a12121204061b170105040527190309180b010801090b03010f020406090503011802010e10020a08040b07140f030a0c0c0902160b010b03360607020106 70
    0x1d02c03404001845050025240e00034500e401110a030040c0c0d4080003c0049650580b5505400744017880100c0c0c42d0324011090300e51414060302c1a214040a44c016005240124a404100f00c91070400141048443c0703401c1e58100c030808080c075481820000b03e445105024440c18240ca41099848084030040b601c085031204291000014000c042d10750400746540000e0b01103005205503003280d40100300c040c1c4010000a943d155804440050340c01907800400030030b1029100b00400d0800b8020305084281070705100c00407411950000e041504606141801001c4070010418054020002403118940040f07941d0707200c65454028526030361110b107085600620039400c00061030f0000448040c60007800340a541030208a043c12240403134400c4040d00e01252801c3c00241c01c0025100400405031100310840c0c000c1128101104004410b03404481000303401c10130026184000d8010000c40c004c010000c0c4030304081c000a00000705032000743c1401074054038090004d00c640552200040720000062030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 429105584 1250 429104334 429104359
    0x803070f1407120f020f060c0c070f03020310051b0f0a0906080f04080c03040f0f0906051c0215041d0115020a031d011b050f07050901031208040303020d1a 68
    0x1c841c026110010081030f00c140c42e44450318000c00e41d40f800c080c818411211410a40d030b806c0f502c1c115080d2020800040f0000705014590710510070700000c0d00c0500c5445007114903650201c4d681e0b0b4640303101e0a140645d5140410410100f4500c601e00e0045041c0c0c4440c1c0b940e0b00b8400785102da03840040040003045070b503080002d9013402058903500c50702c02e20242c0c00303a5550f9621f03074805503070000204840d180001c000c003040c0c0c0d0140d0700d103038009040c0504d00102003d0034030050204540c2c40d40c00551054034803100480d0b2003410070782c1150910b54152002c1d140c9d64045450300c400b600664016824030420718200204c22070955024904803084030f0082a501034640c8004c0c3e845002845007e80000c21280e942e501801c50f43c4092400c1c6401894460340844200f12140c00d00f40f4500d0049801c1e402501d20841c2428007002803001400c81243c80401652569850607494400e0000c150b040c0600c0500050074503019905607840c403000920140300200401200b001394010480200344249888500b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 429106834 1250 429105584 429105617
    0x1419030b100f080303060906030c15040513020910180317090f0a121112030708071218120c0f170601150f1407060911040b041b03020a05070803070f 65
    0x10740211030b030a42c084d51454542c07000b40030300d0400003444181c241c8140141e0f40e5503500e641d01d02810035110314200a84590400e0104840ca0040c118403902950050200f88000c0d07840c080d0382c1403210b81d0303820003480300d003171010090009508a50018088003034072815a4681000d0500802060354220350b40011030105104201808449009001640b1800420303c4002045032900d510031000082a04043d000c1c4068124510b41c1300d250111a030510100e8020200700480b242d05200107001d0411180f100000300110300c02010780c7c45280d901e17101c0d4001084c1071107011300d400d82c0500341038000c0301c00c8282c540b400000700c0a510350f6500400e200307800c0001401c4400c6006d00e0740d603001759039135021059014881215a440c00301103e0316804c00800c0100700081c01840741c5501648070301840c0107058103141c200021501c500300101d00550800d070648016040f5101a22420f022509005860f0340c2d011008a4840c0202c1c0002402c40b640002405991a00002c0404100401e507035400c1e50711046000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 429108084 1250 429106834 429106859
    0x2040b1009060c0224120f0c030c0d0e0d050a020d05031005060f0c01090b0703050705070309030303050c0d020c0604060501050d0b070e12010f06050a06030e071419030b10 75
    0x554000800a03031042c880c072803081c0f5031240c68a000825000320300c0896002d1102085030100c0b5400e01040004140d0340d00fa400b44802a4008501c1d100e422075441c10070140706c3d070343c070000b843c00000150004240000302525400301036408141e03011102e60a06d0018040c003103911103159035001d88160540030030150b21540860340704912180c480c0000780c1c0381c5030a212640d0480f400890380074400f40681200d00e00248a290f07103041c0903407034112039810f102102404940003d024101003120130001c0f0404684c20281c0c000441c1c1d410702d80018a0743c0c40d00c014040a01840111f0408240001110441c104d00040c100d400b45008060400259999808205d6032811580f001040c0b82180342c0055049400347c403030702c3c03103480c0d014102c85840e042e920f5007182161504565000619500c0f08284180c1c201000c5450103054641820400c0c00842403d42c1d60f900510310401140c051100c0d281401a2200c1c032850103c007013444503000312030b030700c0f8544210501c0d011103038160000321301080090812003104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 429109334 1250 429108084 429108109
    0x120905010e100615021905030906030a02120609041211010615030603050c040920010909021b011d070e061206010e07140a0c02060a0e090720010509070506130902130302040b 76
    0xc0007804000859003400000460701b413001e44180c0010f1048003080d071640001544504c22500005035100c8894080320300c0c008001e004140a01c0e01c0d603007004001401040c3c0c515118407203003441100c800c0d20f00c1f0001e0151142c0d802800e040c000c00c403c11404a501a0486401d8030700c294160f03600c3c2c50520050008460600c8005081404200c0e10000000104610000c19030410314100710015158031841e0241e9000c00e100d003103d91600c0c401070420030428031030005050045d200050510042d41140e80d950440780c024a0391810440010130030340d940303070145010b80200035401c0d61801e46e9110100752101d1000c07101000030500010b01002c1446003401150801280781d1580c4900e245550240107040c2c02c80001d64041c080030050311561030380d80c0c0c11013912070f003826a2121100f00c05030307284451244400c010034441d681031809200000c980031910304240d80742a5400c9840340340034114125100d0881c0e00401c64244001802c58084020000d010207590090700c01f0300c482840701c400d00c2528000328 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 429110584 1250 429109334 429109337
    0x9010806031b061803060c07021c15020a030b0d06050603061303090b0903010b040912020d081005101b0c06091e17010b03060c07060e0a0b040201120905010e100615 72
    0x1c07809101c0724906200580f80d9241042032100d44c00704108007007894480241c4480004000200c0c0c48411450725103a440c0310115a6400c10000a15690f5032910002c01803030f0400f666900490b41402d914030a13440307180e80d40d800901382e481d80130305403c2180c002c060950303440d4064000d0000103001101803036a0742c10800c0d41a038404c480c0914002046034145c102080040e459500c03030150004030756440c092040c0360b9000da069250482c5038180d0107031404880241c44400e0040d11800c02040c014000b50801c02c0720300c10384841a82d45140d12084412211141c4940d010144800045040c0201c07a448601034400d9516640190b130740796129043c2884016911080c28100441c0c00d0144550352403807400358003100350012880741824000a030500b40210740071482c0c044045407400c02d201079801031081d503401c80c201524041c00262501c0c5090b44005002a0510888050b40701644000764020109250040f008008203185441800d03202c080509100da41c050402c4000704500046810480700c10415 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 429111834 1250 429110584 429110623
    0x30307120b0f120d03060f03050705091b04140f0d021c0c090920120a03030209010e041b0e0105090342100f060801050405101a0901080603 61
    0x1008200c009040c00758280e0350400c002a0804441d41c451070440c00141d110140074000f4114845002022100c82c0c0c0e009041c2d0031540c000400100e40003041241c180d40302520a90748541e10010206114403d0764020f0017610000030b80002c8428480102422000045410170402c0801904001c1945040340c2c010390b001084c07280300070040105024a64046100780741c0c601d030b500eaa80a074403046841d040c00641b03a00c80315480400e10f400c1480795604200c94100c0b40b04c0201c640c211820343d030f107100300d0000a00340b5030b000504499681c0254982e0f20340a00c003c01c00d028410b1401400f80e202000212010041440c05102c4001d56000e18140c40410101400401c102c6290017190010342d0801101c20509120300d102039404040c280c0c4500035081c10040701d080107828241d0007031400d5001548045071156290350184003c50780b1040c4617044610807200071510f6222441c0840301e8a503658032032204460410381464400900201600302e00c2c80c04d80315a015651030405054807003210a9012061000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 429113084 1250 429111834 429111857
    0x504062309131d0109020a0b1303170c070f15210f0e03120f0f010305060604050606120103051f060b121e0403210b01020705011b06060314010c02030307 67
    0x10030b2802d055020140e0748022401030814020750790b142200c44408031160351114a0f000550900c1900700d0000c00c4640c03400c504e004607105941d00d903070046000c01045030040d06240550304084c0010f503203042d000315040e98011541e540b4003440e11030561180758140704807103030790308181d50141c0034003a030030b040342d4942c20703408504200300500410381442c00d03400c8541d881880c12107000082020700101c030030042c025011030400c2100c0d8040b08400400b50010403413030400500c001600400c915030408400e44000c00d154842c500018143d024003076606564120000c000818070000023a00c4074850041080e2881c030301424001e003410703101c41c4d014214105000304202c01e400d031404030740c0b02c3d48560031101d0001c1d84011102a440028800d440550006103034003650004d85802401c4100c490350400c404000810303003080080d4580000d481001d040c4900e81d0050281041f060150040c442da100d40b040001540340d2500c3d0a80d441c052490741ca040d0f1030081d1400e07915000004880c0180138944030f8820628 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 429114334 1250 429113084 429113089
    0x130605090409060603060b1206040c121109040302010f051e011514070b010504051806180708070801050a061a0f0915040b033913050a060504062309 65
    0x2032004109075006a034508204021411601c103c501841c821440440c070190080100003802e801414481603540010080c040003810011700c0c1000c0302d6107a40700c91030402e07441c1451000458812010381e00004001c0c00c1204040d810351050b04a941e810104224944640b00c50042c0947c480f000c0445142c0c0d1000103202c40c04002c0300c134aa60800c0d5280074907000002c104185501c0d000305070700320703a0144840b0041c45030749014000c0641c0000c4070041102c910400508241c0c0c0e9010180121203030901c80c0551004070310702440b008018000c0b00045440099440c64920b008000844510914a00d0310b0008a40c03030004071603203850714410601090520f00001034403d107640c4640c3d40c8960120303c82d4582298000180013030001000c640403456140d162103034a05041c50005070b03021032500740858025586d480280c201c2400200300303001e603984403e03010310713400895852900060303400003200d100042d0782d81d4080000c0054603041e55442d01c82100320400440c901283e4040040001400d01030b000160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 429115584 1250 429114334 429114337
    0x11180604141e0901110a0804060c0c0f06020c0c040203132a150302091305070e030105071d0d050106030c05012303010b09010507170c120403080f03060a030b0703020a1103130605 78
    0x76010f2000003aa03007040c040014841c0c2c2c812040000400c075100200414403110344100c010031606814540c0a0307120640e1440810440c031607000b0200b55003c1031001c5000000c005241151001400840d03076401c2082084041403814101211549681034040f000041104c5030312120070345404075589950700b0400c1b0100c012240707200610416034217000080159541c0714034819a20242c1d40000b6090615070002031641c20480380e180c0c000d82c1010284007001c0c0e07100c0340e11000d0b5484040742c07039403141c2d1040c0007600081c5041805442c1e5828402c01006104884140b00c0c112002600c80c040c40d600d84c0303402d200711410300485d8008400810300c01000f0380780e4000300501003048149030145c82d2200302c0e03036040c1940004c80e121001c8198041181c0c84151400c000c807040700c190380b00001e42040d20b142d8a0340000e202e1290120f00b808800720110313032107488642c4070300007030365010321140c0e41460f007840028000c1d00b04044600014040d41914480c00b040071040b2500301c13a0002038a000b43c0d08080040d5800e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 429116834 1250 429115584 429115591
    0x10b0f090702030c01020a1d0105070210121409010f1d1b122a0105041412071206020304060506011106130c09020c030d06081504060911180604141e 65
    0x30b60008001d1000d103008203100034410740c1101c3d100c020b4000c482c0f1283d90740e00c0049480c03480c1400f2040101401607a204082040c044c1c0781c900c1e11340e1440a9003607000e000f41a25000b01d002c18440001407061000c410b402c001c0b109410030350304000703124014900c0342245008030007200854104840c96200861207101d105400f01c00035200040c80e210b242000c5107481801d803014a80b01c20079100078030540e046400314840958003460611308050600400d6840c1440000800744031700c2b040f01c96440008801c4c0100c90061080020003041c006481c2015806580210b038111003440c60031001030a00c1d0b01400c403881050450500605296440300000034441800540c280c40d064007081c0001241140350000b0301d540340081c000345844441421000d0182c032460b4001603034581046054541c1480049071180e44181c0010300812020003904003000580014808250418484c1c040400311361150040315020b0f480c00e0300d040010691441440c2c4441e24151441144070980903035038030245640e036550540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 429118084 1250 429116834 429116837
    0x5010b18010b0a030b221506210b12030a0c14060f0403180302150c060c030603030702192c10030302120d060f12050d02063c040c0f0503010b0f0907 65
    0x10070320340c42030303a0f01b51031a01c0e117074090529840785190342c100310703500c80500c000702014100903007000f814280700c1144100010345010015076440d00d0b490076a40b0449000e14080814060701e83d40d41176000007e10200c001142600c00c4980021107074044003002070b405204103000c400c10035558a032568121564600c440311000721071030000c1c0c04005a62401041c0e486141d03101100c0369039200d0b24903060f0030124002c2c40303100101030038810484180c901204a454103030f41202c0300c190340b099a183d58018170b2003541042703011031402c0244c100c40070442c1016855200d0016170b0144540c1d5400d05801a43c055400004d006809c8843c0048600111802074800907a4055011406980300c040c009000412540020030003e0b00340c0d5502c0521074207004180b03001104c0c0c8040d2907103182140c00c00341251402550125080202c1911086141c00a41590000c500040c942480c0381010300f405124002180190070801200880025103454144a25581640f018110000c005681030403c03501a4000b4003010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 429119334 1250 429118084 429118099
    0x305120c0909042918010b0603090615061306050730030510090e0124080a02101b0f05010506030a0201090905060406031403120f04030c06051503010905010b18010b0a030b 75
    0x2030921420094080c032178140031038868042d4509229190070358250400f5a4041c03501001030018180012600550124140102509021141d80810258440d000415075446041c06010840641c010020040b25015150000d001442841d40080c07803155800c0c800c15201c444003810011601a400c001c3e40038050b40d02c0b5448071940d4140400640c0c1d8000d028600030303556025a1540071107580f11064507882081d81c0b08418904103400240d40b42006500a8460040000c09910491007000b40c0e0241c040d108188050030401031400e0001c0210b4048200d90b907508201c000b40003420001094400c01f5016568561a14a4086440006c08010f00000e4001e03440b0b40001c001b10310904071256250741d00038010f558482134507004a030100300103040060b9140070982400040303a807040c0c150042d960062b40004054942c1c0188210390b5600c024011f41650811042d94244070341940408240502a208046109400404164000c000340100243c00300d0620401700311510962008206000150040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 429120584 1250 429119334 429119393
    0xb270303070503071b05030304090e0115060206040201020f06070c0f15050f16030207121b0b0709060e060403031b03030b060f0c010b0f100c0f0606030305120c090904 73
    0xa04680c09081c0540d4030350310000c1d0680401980d003c405400c10204013181c0c0406003040e001a03180c0c07082e44201644283c0382d2940c900510b00a501c69503040022584100c5103d13075035078001c3c3d01c51004440a90260140c00250081d840000c83c0c1e03940b14a92540d21746600380321554600c2c4402c00001815107258005513000c4c2070400d002d01c10940103480700c904400140c0f500c0340b2034180c40500452840201401440340600058400c3d0f441c04800b480d81c10000d4000401200919003103c4800c40940801450024442d000ba0015800e40a0f034129a8176109000360341014004184250300c8001c0025100540c41d069070380c2c1350581c0e03142462207454041780115500d000200c00340c000d0a840d00702450005002030f00c01c44248201e1018030010780d100c2402d2503001000840b243c951900102c14480c030301000c08100100500c1404503640d10240400c043d80e22030070010b01541060305485521034941300070841d1043c1e120141c07140d488004040340f0041e5102d5440a180d001103508003c2c0038079103246413 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 429121834 1250 429120584 429120589
    0x1b031d150115020a060c1e0207060503191b0e010917030714031309061404051b0f210604050c0408030324120105060310200306030a021008091203010b27 67
    0x1500e45100b0a5a940040305134501078421b2081c0c031003d030751408d40d40304070b10401121750008181c1ea03000c841c00318441c482e4413842c600350001d015241555a00d00c07000c400c5c420005601300c403800c008075000fa41d5121825446800413075640d00c00741c0e18500c01d5070042c80114001400442d00c480400008029a81040203481c2c0261149203d81c02154400751500d000f03020100320564070a60600782107500f4003003030030812040c0c002d403010f80c0100341030100c00050800f02c0b0300d003c200300c2c4d441c517407045504005007114140c1080c04c0001529600d2045040c0000300701003000003025902541c3c0e207100a140b650f2941900001001500c0042881421205860101c41d1f916907079401c40884400300046802d243c000f04041c1045403104003002c00900e44032450710300c130410082c80c40c0c000c0e038400b9441e5520b03220080040c0c500b419605d002540401c0b92080f00c141c050f4042411030048501c50210f500b2650110b01032410380c00240100c0f84a0340c0305000540300e500c0700c00e203007041c1004480703000152078086401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 429123084 1250 429121834 429121841
    0x1803070305030a12110703140c0714030d08040201050d090303090c03080c0607020106080316060b0d050a211b03140a0302120606070201050304030c061b031d150115020a06 75
    0x8107607401c0d0070210300003c00d960440c80e150200c03103414500b0041d410b003070706130050039004140d070143c10007400250320301681e21240101d5510350440012100e425641d114417146422100c2c41c6203003340120002c0b50855801070b10030038004c90341611741c1402c04440c41e54031f00040040343c2c402d50400d520ba0143ea07011409a4050348055405a0b1382140e480324105203261500704050025805c581c9481c10802ca110300100641c0c0d510050250110b105001600b0213402038081d000751581c0c41248100d619080003400200303415610f03c1a441e0106059111f41c181306030307440c049134200104010100f40070402081c264403509180c428148103040104035003440690750048088240425800185a40b0b5100f40010aa500510450f903003407502c0042d500003080350001410003801e11154414480400246800c0849021050090381d00d000345a070400070003819204420401c00d0843c803800c044110710104100c0c14140c0c0b041701c00755030760740707030800600c0c01403050520750302180103d81d011000206170f0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 429124334 1250 429123084 429123089
    0x30a06230307060c0c09090f02030c0102070602060a020d0e0d210911040c0215040b01050a0b0301120b10080a1a0a02070b010b0c010e070e01030506060d050d0f050d0e01060e0105030a02030c06180307 87
    0x6100c0c4e0012449e2060602d000d4007102540c3c1550f000c1d0030100080d40c0d00042e240d030700890391400035858448000d80030000e440c1600e000503890056a141c580090f9200d9015500140c3d9022a842c2d0100801a5542164983c80300503041c501800404480d030305050300481042030300d62041fa00704158511007500707000c0060350215180b0078000d00401841c03901e04c200d000034003030042d804c03441c652600e88900d507041ca0604008051007480000520300c00d801c00c0384400144072102c00c0e00d169000500d4a0480003610075842c3d074002e000c500c0841c010302c0b413074802c0d07804040c0e20484841c116400c004c0c030703110503400028500d40d0729922503008514038034052102030020051301915001c02d50640c901681043e07001400360f0300604040386881d020402c0001c091442e6220f504105400d1030b2540c1e022680781c4921160b03104400e00301144100d1400e015480f84044400241001c1000d0740c8400416458221458020b545544811161000340c94140000d14440310b0002c0440418100040443d00700030069 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 429125584 1250 429124334 429124343
    0xb0a0e060f0c1605040c110a1101090e010b071b0302031905030f0705150c2106010915050306031e03041802090901030308250c030503040f08030a06230307060c0c0909 73
    0x1013040903042500846402c51494200580d041000340700c0c141d91083c0c0303004060104ca484520f0072082e640030701081000b400c0d000c00c01d58580c0da1290740c80b24043d4040c10003244c04013600d5080c4501d4101d002c6000007940e900034040c000300741c8a0102443c0b40e0440002c180c0b0303207000400140b454820b0200041051078410000f074400d0704101c0351030300c0b0410320082c8607c1c501e0074100003054103500364039050031000030801841c2d0802d858981c0100e03001e003056004200c00c19401c015000302e0540005c05103104072412400c45c3d10819900c144080f04021078041c11503584e00c18041484030311440d13141c0c00081c0070401c00041c02c1105680c0010142da0b4280d009801084554050054150000e800e0410011402550b407444c007200d00c03001850201020405001c200010000c5420003010700038034068642c00444890f12404e00c0c000400042259104141900450360300185100388558050180403c0080c00351006a20f001826030320f80c019401c0c11148100c1007440411294558401e186a07107014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 429126834 1250 429125584 429125623
    0x3070c1a071e09050613050111010908030c030c0d020d0e010b120304170a0203190b0c030402090c0306040f06032001020619020f13090b01081f0303030b240904060b0a0e060f0c 77
    0x4000c005402c0310110000d09442b64107101014000c9480c440441c2d41109a46440568994495800c1c42a40c000e9500460707a8500010303d030114001070b90005204060301000811810240000b004000e0706510810b01c119002848104000c2450903101d828140f070380010b54180300310950001c0e04261141401d103a8100c0c5450255050010700c8800a40c0003600e005c5051031800d00d50000390440c000182159984040040003171303003e40b6207400417602c20580300410301050351030b031501c004600301507d0303001c0c1b801c0c1c4160a00300c1c2541c80082c1d041c0c0200c2e1000046d0f0944c0728411a46070113940444080d4501d803c0400900c8065200c10075480c009114580c400105407500300001050392001800000c564107030b00c2c0b402000060321010f000b044a074982070000e014039400300410403078002d01e130520a0350071814034004d60f0240004010300c6d103030100b142d0411140340c80369040e03505402080e00200000352500040700301800d250000b421486070007803c0f41c0c00c003400143e100d881c21b0004091201103110303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 429128084 1250 429126834 429126839
    0x180506090d090e090c060a121a0f010f051801050903100e0c120c010309060f0603080c0f0706020d0503060a030b160e0a0b0702010c060e0303070c1a071e09050613 71
    0x6000c2d41a001801080c2c0c11000207061819007203540d09003010304d19109440c00907560031800d02442c1c6548000385d2550040c4560404102c2e11402140300c4601e05000d982c0c0307481001c071598401e8034981d5011100d9110242851400c94400c20114951b205c0141407103800c1015560707941d030400c18030804142a0002091102642c00e10b84d06008080d50060b0140b0b184030700f10b5901101c0407810b84a800c80a1070005201081410410060320070354402c10f800c3da00c0c011011040c082800b0040182d040028110f4035900481c00005a58130030703500c980c40050308060350b40510140300e20700458100c030000302944101d0380c480c0c4540510380c8041d01e207564068000788003a8201c51b0480410b040b407401c121a03143c0d81500c0d00d010303003032079226411340241080b107202404020890241c0c01002e2810f02c10341241d46070300e041d10001c0c0500002c400296500d200f0100b82c4050341d9110a540c92155030f07a5910642c0d140b4401c8480c56118803011028401d00c0540e50380030806403a0000a4443c8240800301c0005461 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 429129334 1250 429128084 429128087
    0x102210f0d052e0b0304061e0c030603050c061206010c0311011a1801180e070b0d1d07032319030503161701050613081219170604180506090d 62
    0x3000c416066000415a01001041508030540c0e0303000e47c010501203008203d0240020044002503140b00b1254900110032840315450f030b01c114181c0340700d941120504484d090802070319008080c2e80c1c6039428100400a9120752050080a840350300c00d08240e01a01c9c010f126460035a40d003401400d004a40070400701c1c3c020b02c0d001c01d9039041103400e400c86000550409086410a0101c0e10300c03840020340303804503040308d10b804200100017010000c4246845a00070031001c1c001d031401090502d4240c201d44541d141511001c5480811240d0095440c1000c003441b8850214185802541000368021003d11030b0105070711f41c001080f918480c0d074665a070b82c50f04108405a9030300644903001000050b184080d041001a88094107440c82203605d640c503000d0101008c2c203600502e4001402c24050703507c80c030706511800e8019041c1c1d4a00f4490820103061402011183c450700e00c0c24040c40c14402c4000300d0700c103080c140e00c021040e44100811081c240b045407134035841e141041d60700ccc46040e4401031900c814213 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 429130584 1250 429129334 429129391
    0x50403170d050c07020307210b150a0602030f090103090602040b0c012c0604080705011e1a010e01020c01110c0d0b0a0f0e0706050d14040f110102210f0d05 68
    0x100d5443d0002c1d0030700485401203035490740d05000c2c500d4062021581100d54000c0a01818480c4c1d50001c2070b5030b01464403190300300b500440c410096024514181c40842c01c9400030080c3c60110100062050a21000c000110003030151480c06544450303081001141c2495180010545a130722400046001c00400884d0410124624021f0105030b19526601c1151400440c509030800c3c3c000c0d80050700c4182d5401c107a0f0040250011001907211400c0c4c0d40c00103c0400e80021854a41031801d2000d581c20390001554040d080710015801a000304000045640c040c07103a40d09065096822158000640720100b11102c18140017030350203508950400000c82194084d464070354601d03ca050009000090b040c0f903070b6040d140144018000081501444038900c0d5204000800f0101d5030b0388045e092504103000901c2c500c0f48251651401000d400006500001d03041d4100c4d04030813401a10b100c050402964650011203503c089524104990483c401c0c1d2805520b010300505007201d4a036034036002020b0700d00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 429131834 1250 429130584 429130591
    0xd020a0e0a061119020303130303110607030213051002070509070c060e01090803010308030c160f0318141212030708160807050703030c0315080304090c0309020604030f03050403170d05 81
    0x10441440303d6844154030210702401c06091880d90007004281503c0000c3c21030083e034214010031801031a00000b417650190410341055943c005403007580d200c2100807402d910424403070440290142c0010000c0f400d110b02840d40d8000944191542030791500c001079a22041660200005944140c1c43c00501490703202c1c0d00c028017600002089401003030b40d074550103400144006005004080001180503044c4c00440700c0e09040708a4030041c00800c5d1800a4402d0b644280940008211500342850601065a21070540706a00c5511159080403020012480d610085030001c5004264180100c40400005140a00300c01d858804961405100c40030b581180501c00a003080501801e1000568026007210780ea01c1e098540440c0b0318903001c50940103805a031150250306114640e0000d02c008000c8050001d03201c000005104016405e90b01310143d03545500007130340c0040e082000300005580701c145031464602c6800c140f400c1a64170b454000d50340c011710b8841d106881740001c0030208101a032241c2a032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 429133084 1250 429131834 429131837
    0x170a0f0f020f040e013201060c021201060e01090e01090c0b0309120d0903140f161a040b0a0506030a020f09041a0106020a050c010302040e0a052a0403050606100c0303050a020d020a0e0a06 82
    0x1c00e0300701000c542c20071003410b104d600d05100c00c0740750160039521340c07102501464bc0010028000b0b0341e900c10884060390300c2403041485d05c07450180c0d0140100018011079000c6038028120200701da0800c1900660707640043d25442403446910541562000c80c02d02502d040f008075507000500403400c0c24054410a881003984005401c10041802c481581d04251011580101050100300f0039920346100c08400300480000d407412490100402c000f641d00701581f1800c25060103001c4c2d61110002d140c0d5580507110002e610254405100116041c04100b41c4c0d4060300071000717041e91184c0f507104a01d46800a0300201c0068008540c0f200501c2020411400441001c3ca0214a094503020401d0000d540241c90701d10003549800c04100e9194041540e50010440c50f00380c1400c0036002254000c044e4820310044455005010000d6001d2030180078840c0c1070003403625404d800c4079803541d00701e004110007000d41075820350a104000b12450544041c10840209071520703460070f0008010000404035a610480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 429134334 1250 429133084 429133151
    0x61b03020a080118140903070c0b0306060901120204090e07030c1a0703030c0c0c06030204090b09090307030f03090b130b0f270309041104170a0f0f020f040e01 70
    0x1800c1a401520607044510300c5103488401e410a69188003d402c41c2d05d01c0c0d2010f60015020700001d04030101c000d050042c4240715452016030b072200110303c00e020490f04a90b00c2142030000b500340c0e5010790041100808551401490251600044d1045403480c0610316001d50210005208000d01c1944001c090480c014100700c061200214118981c42031820080400d83ca40300692803440c05025806126a0720454032036066444450090007500644110410141000501c03145810031a1035079001e0140440510320702b400a40307003030b01c402d02c06020304000c140da40d410340d0020806110646000d20b0b4141d0200320304031000e0825100c081e2001e411809581e64140c240030400300b0407502c04411012018250820500d021501c0d41103024601000d500141070110300c059041001c0010015191078210640d924010a801075540d2078220000030f1000e02012404400704074284040010503200410003c0c0a40e450400724045d28465224200c0030f0791980c2200ca404101142e801501c10b0203400d803003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 429135584 1250 429134334 429134347
    0x1713020a03020111031c0203100501030e121608031906080633030709090203070e1509060a0b0c070302031e1e031605060403030b01111c110703061b0302 67
    0x4140c080c1910000381840740040c200901d080044c030a8035007051160360313907031500c0540c01020406076101300d03094805521000008911580a48125160080c03190018403c000710702048000c1940211001d010207030004056000203821000158411002d82d0801103001812141403801e444c3d01d600310501e9604100104400c1da162080341e5200e22204980c51040c00c52a200c44440b0007111082440d014000c2c03040c0403441030520703086055030520a4040384d0844d41e03954541194030809450301551280440603041040c50708652064000c4001001c0142140c0e88078000c008941c4080d00944803a040035008109500e424880e0350520311588400102e03070301c4841c2411307454640288110700c6160121103620310180d42081540d80201021f100c43c02c400c0e00c1414030030b030b9940303080300e0440000342003200308900340d4410450080c00311040001801000380302125408040c220b0001d040400c5a04e00c4458055041003104d01c0c021402401c001492000d8609803245002042851600f0b150040044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 429136690 1106 429135584 429135589
    0xb1e06160f0b090c010804200a090905210d02130308040303320d09030c1e051005040507030b0c0409060605190e09010911070c06171302 60
    0x40001ca550f56440707a6642e503000381600ea0000b0740c08001300300015000001c0700d1400c2d0502040c0400d0340c4112000c15030745260383d80594601e940301c00700c02701400414000300d0b509004900c401d60040c0300303102c9101c001e4030942205190950f4000380075604503011244902c050b65001c003c056071165281001025082001100d8000d00c0007441c0c010204080c1111300640225065116801e05020840c0407006100035001581400310712a80180080c40c1124510021a0f5155103003115001c1410710600c1c05121a031140311003842c000c14000820800240e04e030440c3e502680181ca070380c2d2030340b0b401d1925020b00e61018021b0b60070800c0100306680c10401410007602c0c030b03150b0020301c80300900d42124043c0403040d03401d1308400031034010310110f00d80c0c0d000a802032205120403881d18800d0790381d4400c040005e60205001171641c1081c6a441c001c2c2c41c40316a00290412114803426829800 = true := by decide +kernel

theorem cover : BRFrame.Cov 428956834 429136690 := by
  have h0 := BRFrame.cov_init 428956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 428956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 428956834 ≤ n) (h2 : n < 429136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
