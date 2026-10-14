-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3602
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:35.228981+00:00
-- url     : https://prove2.me/submissions/fca6da1b-5328-4882-99d9-26409e070e8c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 647661870 ≤ n < 647841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 647663120 1250 647661870 647661877
    0xd0c0303060b070c1401050903070803030901050a1e05190e010506030f030406050a080c0f0c01021201050306070903080313020918010c050a0807030902030f0610090e07050f12190305 80
    0x440009040c048003080600e918019158000d600540000c1304a04014200c400007401c81e50081c1008000c0c401d0040385d40d0100032120080000b03202450741c070b0424080310b60959200820010b01507003000354000220381007200100d0401c07001c000000c1e0940760046ca0001c00c0700d00c01c115689840c180401c030042d450041d130003640100c000b20201c50b005440250035a4681c003540c459070001c00d90500658000c10300a00304103a000f070490100d18031b07008204c2c501c02821b4000144003580d42c0e60105c1e140c0b98098000008502502003107008102c40d281c0b80100622a0105010040c259035020000c22110340452501d18051f0b030380105081103903e484c0942107401803010321b40c0f03801d40d82061600001c1078061000c5600c2280195218180e55070b4102040c6d02502e8039600880e018441c95030000c2200c80280089406030044408020b0711624207000320056441c00351003007403580c1002c04100a5a03440d5607030144040c80c16a1030b50700c040d1262005174104158405411b03402206201001d00b010382c0701004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 647664370 1250 647663120 647663123
    0x1090510090302120102090102100b1804035d02180a03030e0306070806090f0702150f010620030726040909021c03142203050d020705060a0504050d02040209030d0c 72
    0x2152b08403442c900c900b0040d108010351840e00320120071140c6444142506886601c9400381c102148900c10b5005c100b503400c1644000b443d01642c491011016a04200070100ca100d02d045042d040b0084401000d00722006081c2e002c198180c0c1d000170900214401d050f814074030f940004004215169a905010b0107416101101600c240120740001e001e00c1c2c015402c25003c0c0034041c241070381c82d503a00303000b01c0a030031405002c00702580f0401c802c500340c00c103001ca80700344071700000e51003040740b5403414030b0141140041508000707520903c4a11110030a01c000280c07a9456003002c0e034294920700074185028045400e0a504004900018000c50720b90496009800c0386d61094404e40400b82c1375440961001014600040c002060700c0c08042d0440c0e6400058081c44000d10422180ea044070407010514204591048400360803400c844254190180131300001404141e4180c3e241c01d07d82c840090071481035008151244080ca0f1944095498a23030642e580404e01504031600c00020100c0500741a416140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 647665620 1250 647664370 647664373
    0x60c030a0e1e0d2309130c03091401020c1b01050403050303040b010f05060a020c0120011a03060907050306041203060306021c0606020c01050708180306010e01080f010b01090510090302120102090102 87
    0x100008128450030310b0313485100c2c1005202e6000c0c04000b5291444c0d600036102d030340d4880c45442c20054004160703c11485260f0250300c0000300c1ea0100d113880036080c41344d010121000e0344184000c4040b0038000c100d0b84e50703091040841140300d490010040e1071307074022900b000d40244804020041003208001c900c0c0d040e1111000e500a000781d49008000071846480c110400681004031580072035401201291a4014804c42000bc10341d40003030083c1c2180c0d4004000030b00325100e4101480c89040070300c131550300018203030050454075043c50082551600094030041080e83e0414906c252580b1030b900800c059944801c0c1595a84001e903070003086503480b5041461054541200016a580005070200b28410182c56290600c22507440ba5035541d045299500c1089082c0b1611000c15a4103004880c0607041c042610209541400009845c0c888483c018060b56032603c03010460311783e04540c4100848804450901000c0d00300c070b100b02d503903120a40c0000c0d00840c404215010002e8107401900c50034000781e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 647666870 1250 647665620 647665633
    0x1204050d020606030102090f21011b11011b0c05030d050c090f0103050106080c07020d020907110f0c01020a02210706030b01110105040f3512010e0603060c030a0e1e 72
    0x50806080381f280c40311250744401c0c1075100301c44904041881c0144459004d10060010004e060310700d0075907078811259004112032003052100190054402428407030040020401000b5200d00100c41034a0180d004060200b60140c11003000f0b410003c1341e08200c2c1c909014007007424000e940c03205a820480e1030a00c83d1018146404041d4030070b02c9064103c0d4a0303030360741980c9501d400f40ea8201c940d00c55141640c0200e1903041d40000b507201c002089010301c0b001e5803440c2104400c00340b03c03420225020a51811604542d02084d426a400515005055012110210442c03180c0d280d8500304a40108505017600a1140001d1940d8140d8000bc003546800e0b01d800004285c01d40401c1d00b280c5086a0045c080c107442501c40002c204034442a080c400400b52000b440e000510403030041c420511103a000c07941e203001481c064001c3c0c454188900408004180030303014102500002d444071002001041c400e0804230004070b0f0700b0416003003502e8507400c001c2550385510840349068010034152200d0503003841040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 647668120 1250 647666870 647666881
    0x3105060a02071415070804060305090f060a021b0d0c0302010c0905060711151606140c0703030b03011e02070b010509060a06080601051e0702040c0f0e010c081204050d0206 75
    0x8100300c8103540c91a502404410b803d207201031041156103014241c0020060091440300c20842d0001d1801c540220b2029403a1403401c2001016a40700803c03103071241d000b030014804d401c0000a15641c0001c00104007584602c0034104002c04001130400d0344007103202c0e078070080103004e40200c0940ca10310b01030750080c440d00203044000c1d40c0086d140e20807103421260400007800802c90321a600c11300c28000a240705142c016419a4500c2504201e0190351420307000c2070040100050b620440c846e0b052807a1f28170b0700518021004d55074500a800002c0c05140d215140e0001955080d030051111030313228514100200f0068400380300a400c540000c81e580c0481c0d1002040c5860101d10785446160b00078207c041250a04404862009000c1c0c20a414010700340490741018603945410030040350541030058a40103280100025030701ea451174102440b509003208184194000009907032000203080c410344002c6603103440202c0b84140654003011032100d13800d02040060125902d10120816800c0b00d4164960 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 647669370 1250 647668120 647668129
    0x3050601121a041119050c120c030c25030219050a060e04050609011a0f040f060302071b0b0d18080a0c050f0601180522060606120e07060c0203033105 66
    0x740d000c176020302411100d4840d8898811001001400c201f1025907490440440600303844d50480b4641040d240c00110b140e8101040400222044030f0214515120b5031200b81801c055400d42400702900810f141c002c01802c0413a0310351100010007000d850b181040d6925503005041c540143c410340e20070350138070b40896520300d032101e4a541620265440c01c0c0340503070142c845116a82c08036091030f21054040c00f00040c0c158203981104001d20290f1805039907810702d850147c4074500b0102d01d0180300340040c0b1050044485282c180d840b410f0b240303003000a170008803410125060700c1403100107104c0e030800503070145103503400040e54034218460411500301c60402c404840d114842401000080030032090842c8503203059401042e00902588002c28102070003001b0034800c00f20102007a101251039001c20440366600000c0701d6100c0e2050007080010318402610b990315200d0030711941041250000c0403200707544c0c09001300c0741084015175001844190062046205582c038011800b17494480060019180c00c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 647670620 1250 647669370 647669377
    0x1b04030c09021c05041101120c120b060c16030c061706040b180f04030e03030c0705120c1309020103060501030b06090121020a08150d0308040303050601121a0411 71
    0x5010a40c00415400c0444090094110b000b94000d21503007442c42000700c05081c03103614040c5015044141044882800241c080c841401c4103020311450710124812680d44801030f910007580c0e59401107240725a190001e44580641b580307080d02030240d010700300d0014030250003603c200ca210702410442560745000c182d40300302d2009113129684110b840090600d00d4a6070005c002140004d00c80b41da000516280f0304088d003802c86045503055212024031040c1600814040424902180214504079036001900d4030703204144030b00d40c06080c80350780c03954170b010050100812000340904402c0301e42e076007408810058014140d069010920307021000c50709501c03e0082005c0b51801401851802e8080001100c400d19020500e20400355512010450303032116000a105c2d80d102680c80d440681014030103e0455505840d00300d105000c00445200001e401090241d40507405081c00242c950701c0c400180d50354503070b01c5092102e0300d1500c000584145503007925207240741e8041d50104400131400c84002414030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 647671870 1250 647670620 647670623
    0x15030207021005130e18010b0f010203040905090f010207050d030e010209060f09040e01020a02010c0206150a031704180e01050a090209060607020607080310330806010302120a051b0403 81
    0x240b141001c050402d02410003000e0a0701c0100d501d45043d40d507070b442003075030413410784051000c40055041055201d070240644980000f04503003000440000e600080c1d6603205074414840c849840f0400a1f201c0b01050011f406480e921310000c0d580e444092500316126050b480c0c0344030100307103010002d2501c444144240d0b180b841c40034003480e10b030a204120310505034003c0300d0519845034a5440c24050a83c0a0003c0c2c500554650004501407034000310190810764000c25800c1d420400420b4031a203075903220141d04c220303600414925408800d94071f60050300e00c641d4101011059a0103c06040d00c1d030300380d0107800b514551400810580d2641c060340c2040d1750b00e516000c0d5210742500c022032284d1070080010040988010082894080c7d19650007403107800c1114000c0c0798039910f800c2008080288211181c202040722800a11280005035142e005401120100200540d941c0019416400381c0c3c1124510500a40b082401d03103445102013000d0a81140d0601d120844518000c0450b400c403401e03501500e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 647673120 1250 647671870 647671879
    0xf080c010e010e190905010503010c1706040203040201110f060f01081c110a0605010306021801080705070609030c061d0705150d0f06032102011406030c090705040f0e011503020702 79
    0x103514800045070221602400700360f001c0144e01c55001008180e140f1180100300700c07032002c6000e43c504801c06084501c102040410700000b084854041c0e601c60505a9000408540050305c9031298001261002c40c0b9004298182c4a04010782e2044940020440d224108000420350315a1f01c5405040c0c481c82060031503c22150040545249180599140090056054229680181c0a4440c81c06803803080c0c0c0180d0f081c56001401e4607019080d0360104040e10800e083c1418070b070424240c001e08511500f100034020300c1e41c401008041600c1110031884041d0001400c1c094000307603840780c481580c184201e0f600c0c00d10481d10001981e0500359904e161015030815803d040082c0c0040002c050401c200c05d0801150369000003200107587c010b164035600c10a11444003107821580c10217421184141d442080c041968410460b05a50001f000303e801001918902315640324a00d069407280119000081c41210040d0017083c4111300902e001d040f16904420311010380c4502c902541280302d1503a019401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 647674370 1250 647673120 647673137
    0x6090b070f060f020a0e0907080105011b0203010209100206070801081906050a0e120c0d0503040803041e052e050c0334120b100503161101090305040f080c01 69
    0x228941c08154403189002d1400031801100c2000201c040743e001c3c0d1500408140318030704240d000c1c101102825031002c45400c0104040d41080000b03004400f80300c5440150501801c4c0307e4007191070070b40643d40100340240c007010303203020116006074480b182124143d0005c3c14510000440c01c1c80043d074402103016241190f04071000c1038031044082c0800800b81400d091300c0740d181c050030351801c2100a4078a1040300c0c406449009000006040c000140c101c041001401e10901002c6804901240d130001d510621101502040d407044c96600011010050300500800c1e4424822038040000711700803105080042c10564040c01c00303d0704464080d42c08141502c403e100140c44880c041c01c5070301000b115100081e107008182c0080c1b80da042c04000c0c01c02d001a290042031084201540118540e10f40d044905024a103084c480041503800002c2141042550001c0c41a51040c06808003103000c140b0107000340146005800e0180440d8042d210348030080c80011000a0040400720b840c01c00e00c40b0596903082d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 647675620 1250 647674370 647674373
    0xb1801030501030314070f020d080403031b050709021c050a0c02010c02030304050a060507120905031c14190204050d0c051203040f12081b0a0213090308180f030f0c0706090b07 77
    0x880e4211b994100d40008452030031901503a180b10144015621500d0416074a9066280c010482e034182c2031039000b01002c152010300000d0021903000c06807900920300580f290103165041c0f000c84102d11540308554a0003050007107111080e0881200c6100342d40090103c1d800d180412640e07848210390240094220050f51800203825030406904013007140f030090804610440e0000403110742d00c60403a201e80c80001d0f80d4000300d005002e0080103404007003081111180c01c40304886024030040c5142401c8260241c43c03880c03455130b41d060350003508020303003409180201c51410198400503401201c1c40b40940442d4600e4411001003140d080d9151700351100c200c145800e52003c640a54101c0031140c125040c006203c60440c0c800d00300d07030841850f00003802020b0890041c000d25038030a20b80c01298030700b0010300c1e101190f0440b42450300710350b400e6090520456081019030601001032400b0380786000000e05000300d01d134650094001c10040130180d59030380380d03680016207118446205542104509100840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 647676870 1250 647675620 647675657
    0x1090314090a0e06180a0504031812030806040e100204080c0f030312040302010b0d061e05070207051908030a08040c0803040501080c0703030b03070f0f0e0f0c070305040f0b18010305010303 83
    0x541220002e410b0785192010fa007032202c840c005c2141c04107191641c0c0c200300424103070b02400e03110110902e295a201514100580a95526119038020381070100c03070804100544c40710742c402c40c0b52041c4c040a95560580490928001c0e41c428451a10144143c60a0200300e2501070112580448004c00035460403071450b11204080c44014020340a5550b1500c1300b000d16156104950365452290000095540a07500140f004503012540c0301c03442d92410003040919a00050504280d40089610b60900c0c50302da00d0480240784603030031843c1d04ac00082862001c06800c00b050074000c51181c40d800d05c10315210303032805e40d8a000d0313441000d0004e44206c0104034003485041c01041c60b580685004514018442c02280c985480d940c4a0540c05030742d502c04022408002498034040c0141d40804801424903039060199800c0241031a8070f0301c0d000280d81020140180101d400421042c40728150050f0f0395101c00d496604010710031020358041549070a45588281305d55410b8990503101d4880440301703401480f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 647678120 1250 647676870 647676899
    0x6060b13030f0f02060d020715050603190c080d03020a110307020d0f1514070e1c0201050c0307170306100305100e100f0e06030c01020706050706020f04090e01090314090a 75
    0x907143c100010ba02880581c030b581004000500301d030200583c1e00c041510b0042018103d01d505038240234a004240b0103103907004100d50443d0300c41c501c04141e64907414280340d03102c01d031283d02000440c45414200c10480750580c02400d1050065156014800d2800c2c18503512413041c2d0500030340c4140041c00b1100041c060001194031280104001c8480c2070720025810112a141c05004503201c0450040220301a4851045440700d18140c50740304800304081c07000d050003444840c2c0207050020103d0160f505110801c20307140301c1c0d500001d8094220001001e0314140b503000380c510b50300401020105d48a003c0c003a003d02806440c40c2040c4100e418078219480c3d00b64203000e0051140412100300015101005041380c0c40070300405034116565040503004c0610b00030b80c0580c11815900040300400400ba08541680c05c07032500716501594844010b02105464462904404141c0c0d203070218507424458154889113115100361100042400381840285550103003d4049901042c80c2505020841d0343d00f000307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 647679370 1250 647678120 647678123
    0x2040e07030b071d03190b01090b0607110f091e0703020712200304230415180b10050a0f03021602040e0304050306070513060509130b0a0b030702070306060b13030f 72
    0x144041d41342c00c2400641483d640018074592010030030400010b000c0301042407401040344a80400c99004450045804c500550f44d01030884607604800c19103540390440b01007800c880c01070911815140c1000070880c41012440c850701e0542903c000110717014068401c440c4d4007900210164203441d0180009c5a026607242201c2207032000d401c2004079210340c10400341024011030a810701c001c00d030b001d0251400c03c80e143d01083c441c904059005600802d207049c031105454030015482100d4002802c080c010300100c1c0740701c40d0003e001e1100442c183d9408000351120720229600d01c1c000c01c52035501101640240e41140c0880c0d403481b0003040040c03405502031407070794480c003080c1c906055446e4000713400e00004031020800705071300264152240503c0f8449902402d1103060003402d00c0c02c0140824440a8441c040d0130105a66211500c0503a503001c01c04e038010000700d5446680c1c1e1400f00c000a460f940640f0045480c41c1c204240442d00303100c400151282840d0140005400e10300d1600d4140c01d481c1307038020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 647680620 1250 647679370 647679407
    0x2010806040b18100501030e0d09031b08030304031e0c02011d01020708011401050a060c030509060d09061a01020d1b1b0807121208130b0c1b070302040e07030b07 71
    0x100010b03480303c004419128403680c1c00300034040d5203040005016100280b140c5c41664009507101c400c0e80b500941007105030390700443c0138007405008034010107130301c1d6981e000f1031002d1002008100c10168084030b4a1481d84580ca090340014525280a40e10000450002800701d00c05050740e4070307058054916101c0c100e80501c119000e040e5104541d03421180350408411101c012107006002504203544900c00800d60303840c000c490b0309000e45008040e8001c041e40b0340d108180004094100c0e20700d41d0002c403900350700070504008041181e9080102d40742d10f40d4009015010b412210310700b480c0a44c0001503070b2045480001c000380d403543e50301003481e4003440f5018010713003030b400300072400314400c1040501404060400340d90001e13650900d9005506400d41c50000c000102042050030003a00c2031011500e50f0102c410700540e180e5240000040c020501c440c05414402c1d8440084030318005821404c40b03009980030026403450607201505e46d41107000103071084a611000c158090710440004005840711380307 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 647681870 1250 647680620 647680639
    0xf050f012d0314070501050c0606010f0309050102160b15030c040203040606270623010e04020d020a180b0f0a08090c060703030e010b0604080d03110d0908030f0f0402010806040b 78
    0xc0c001e02890045030019100c2c1c0d00e12402c02c2d01008000c00011003d0700302400d045061040040070140c0d91480105150b041240408019001c42d029420515500d40e0100003076448428090326502d00c00501d00c01a90404100e03c00f00b4001c415031003603689049005005008090640b1043c000071b9440a401207402c0b60340e60400003207000c49582d0010000079a6108005c124642481c40400d0b154590000050781c0d1194010204010000c244003a0744602800c0c070300e40021940001800078015503400286803400001c6c061241940184003850240350b9000b004000c54680081c458640203081c0302c0e6901680821100d102c1d2400380c290240d1150350f0f0313021581e03c401000041000c54000d08000c4001c240c84800e140000c041c00c0c007510f00030103c1903440070f040a240241c02984c42c42c509252509240e036841c0d842d00004d03c80021102e090080c044140203038243c80c6021050b1394412600d5141c078160341c5000c2031880c071900c60403e001da41c050f9110103440c1c03030741d4040000900400018a60010845 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 647683120 1250 647681870 647681939
    0x20c07120f120f11070e070c0c0801051008011a15030a0b1f12110306010309050319020a0b09010b0901090b061204050c03010c020304030c090513150c030f050f01 71
    0x1d6002d000c80000950340c01c48100104000030f0110491003880d80348540114100344806840041d400341d00c440180740064401c0c1443c02c1c035507540c4060b0340164080b54200401c00103101006000c18003101d20060003004100c0000380100501e210f51240c941c1d11203d49000a503540c110880274580054201c00c00240000c07400b400248040034000420442c10ba80340705101c2020741203c00d41c1e0342c181c911403083c40300580c028000d051500c00105074605040d507071420701052100c10015589041b402603042d400c6031501c054040d5071200c040f001100e42c04080800501c08a4044c02200382c11000908082560f0b428900724a020700f42454406402a40c14000381c40e0048485141500a034052000f03450141050340501d42510b04074400001554010082040003030142c081c20340c111849050005581c0d00c1c1d0340441c586030208580c025240130506034503942105c40a510400002c9a203850400c103c5078102c03041e00aa6200303c58481d1a40400d074010400e4403000d40c808032058031100c0081d800780f02074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 647684370 1250 647683120 647683133
    0xc170c1b07080f061e040210050d0f060803030115020f0604120c0515180f06060d051c080f0114010516020609130212010e060915011202030a0519020c07120f 69
    0x4402040013540036909000484114868201c20030f821496005245c0c40d103600442e2004010110030f400f0404001081c281c0400194407545604800030000d01401d5a203400059594001780100744419041090820403680001060380001020b00b010b000513580b148c90710176030901d10385c1000060016150004c0c00040c410301c05155102d282074500c03240c43c18200c035501003581056401d6502c82d408010300550176200082d032a50701410456225291652600d88182000b14518074032650204030031714400059080a40d852141c883c0300d5400ea080d070f90b500122400e90340700110301400714a0405c030090003031001d1050041d075a400580264038001e410004107002482120440d0f10450307002c200c0b00e42c84040e40d5192801405a0388070341420742400310000c3c0c2d5003100030b09a015601044041501140d00424041d000704012260031522031824001c000c0151400b1104024074600c901da5818521147e4801d4800c8200c1b154001c00c01141021300203019002c40c1e602c04d40d069170000d040030000854 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 647685620 1250 647684370 647684383
    0xf1202010507140a060b040e0307110607021c0b1608040201050a1701061812020105041e1203091d0f280c0f021203040f031b0212010c170c1b0708 64
    0x102c24000d000c801305506001c021942c83e0b1011520a82c00e02c15054040c10707001040c2d0b00b0454000381c1910071010524000340c214800c03a817000b9084040448804c01ca51407005140c0c074000d0152250141507030f280c0e000c220304a11901d681c0380101d107403071002c0342c0954442d10140c8075101039418001044880f144036101c0c1c1c410264421800141440410700c02d030a4901c0f01e0000070403100c20001072560007a4000b0b84035002d0743c010054401140c0c40d030100003841441d8854001c0c600015652103051440c1070003002c000090260140c0c0034034407080600c036800c4020200b88240d104200c00305032178503001e003102021542c01ca180900e06010314800d802144141c410150905040d40b5401d110010300f12010381802c6c1d4440b005102c5840030703c100000328590701c1e1000c0e400360380f40c581450362146108140741008600d51000e0340001102c0d000c5500c0c00d005600c1401100d00f0b03a165014418009405802a84400c80d603054a4100034061000e0324041c1d00007403500024081c3c203481d03403151034484a600d40316 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 647686870 1250 647685620 647685653
    0x50615031501080c15120c25080d0c1706010513170706090501080c07080702060403200109170a12020f03030a02030a060f05010c021908030f04080d020102040f1202010507 75
    0x200a0a0244d442e4580305035900300b00410350b9452402d010005503252110907000b4244104000300003074100700c040c03500d24108010f05041e811210f03210380d5030900c0c2029030080c0124003181807030480c4041c0c05901801001208041d444096005559a600110b60b80d0304001c0c024071076040c0e80d240208000211101c00b543d01c003048002003040c18a081002009140786500841c18040b1000034000c016a0900071100b4058018521030754940452000c90b4172031017aa8005805040c00e421183d2a0164241e1441b0090500342d80306001c40380c8603002c002c031034a4100701c90000b0380d004001c800001494108540800c0b03200e8016240032040c03405419055030b008940001000e0360002c2040030b6003000f440343c40064101c051169003a00d0514001900e12107202c407019106242c106c0d072182038100801e00f20406055200d0580741c80d13400c14907908e1419040742c0903c511070b0140316450300d0054414403d450889a108959690240c902541c000450841d43d50903410008200310001c00315004051080050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 647688120 1250 647686870 647686873
    0xf060e19114b0a0207050a03081e130e06060910170705120a1d0106080102120f06060403021002010f0510050f011d0f01030213031b0b030405061503150108 68
    0x9042d61108001d2030107062004081548045030680444400180840d0845452030110b90f86501e100d1051340b03444c41603444543e2007409100c2c04401c10641c2400b0788001a6118070810303407141d03240510070b514010104000c00f10b0300001b9041107091003103000340c1c0e040324002d4102c0d890506110b01140c081240071491002056111083c056404041c0c1242a8010220b01e001c41c14201c02c5041c0c100c2c42c045c0540910116034460000d0b2824024030350400b274108082900800020781d441c1030070341c00f039006445821003800000b00001c45c0b0f9802120313002d204420040c00a46000d05507403c1080043c2100c4041045669070a19140c880605100d205d014a240f01605400c9603e40800c204c0c0c108502c0d44120f0412249480e09101c0070080100404801c604544841c099080d4a00490080c000c00051005800f1034010020500515004041c2c007100c0140c4003044a64a80c03400441500c0b00347e5008026500000001d07200c0c0700080d0001d0034216000f82603030301351480c00383c070220088030a8100c071840f03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 647689370 1250 647688120 647688157
    0x13030e090a020301031509051b01021e0f0f0102031306200d0f0e0309030a03030b01050f1308011b0c06021b06072706080c07061407080405010f060e1911 67
    0x90000041a0380c0c0100f68025040c413101f400780d0345040d211480194840e0821501e28603146c0f1981c002d2110481b1000000e01120b503120030400e5896031201001e0222189002d144500c4c190b045042c002c0301c1c4101c401c0c01090b42480344555851000740b56030300400c280107800c40c0c4d90104401d550401030015500c0264045441818401d0100c1250a102a004a25801001422a9500d0108400e041b413074250a0000d00c0009540c016945441101c2c0c00130510940002c00c07080d01380b0710b040040280c4210320000c00c041c80000c801140411607100302d960104a401c00b000e000601250018404114070651002e248014000380c58a40340047d50710b04007080f10321b110140100003a105083c03100c4036540515481610f41240075268400c0034121049800000800c002480b54070381110200310880600c800c0d1a14018000070035411050f00c0c21600e03542010030301802c00320b41d4001c2c001a148480e26910a0b40c80320701090105e80143c0522011168840d000d4061008209018200f40890300b10208030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 647690620 1250 647689370 647689373
    0x110613050708060a0c090f0e0412030b030d0309051c02071a0d020d0c02010c0302040f1206110a08040b01050a030822080708011401051203030103030c03231908010501020613030e090a02030103 84
    0x1010420b80c00c00c01581c0b8211f801002402c1066003030980050704980c07004000d2004c5002140074142c042c1d030240c1c040c810017940001c01545540050415030244007954548643d030f04681c00d030b0700041201c54005034048542400403c80c6100c3d001e003280e140e808024505070100c920307202030307070400c03c3c05040b02c41d500c0103a0310900c0d40a008140d01256940741c110715140c14818103900390203980c042c2f61482623440b0140340410609034400c03101c80c5c0d661640a602c411002c0700c002d262050440e0202c4409408400001c0c10b8186460440d0640368494a11030800d01c10f010102110521503071000400840f4100c0028980400c0c8014030182c110500089030400750f01c0340b085010001030f4803250141649050742203017681c010040d00d040d254185045680c090f21800c00319101c62030002c25031a01c04400c9548441010701c000180110029503111402e035000a44040d13615007001d228039400742c1c01400c009081801e03000005001c2501c00e04045200c508442d02050800703404036a05114207500100600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 647691870 1250 647690620 647690627
    0x203121c0c12020d0902040f0b010906180e0402030c090403200304050d0602070804091404151b0509010528020f0706050409020310090f0b040c110613050708060a0c 72
    0x40221510400c00c1c4000c03014020024080c0074003020303141c0351a9000c501c0064603600354100d41000c680042091000d480303019000402004561440c0e400700d0010380002070f13036600403100c545014030354216540c40540b40851110804400501c226030500580240c004555107a0140c40e02640c02583d66402c070b1000d0500154000e441c00843c040143c4c000d000c10007980d41d81c44051201981d0140c00580c440d00141b62894403400b413030f0425256141001c582071861b1031202144e07031040c0d010b07141804804d540240850200d408100d50001d070000f0b040a806459406200103000580040c58102d01e0402585119102d0452501c01c500c4079922001c4880e48a175410405420340142040203032440034a040400b4000740b0030ba1007007450042c1c01100148000400780040001808100310500030680a91640d03c001e01c00c040d4020b10a501e030000d1081503d00c01c80410002e645d05400034940764842c102203814404c1282d6040318580710b600800f0600b01014420b0724015000458003140c07002c0c1e02c1a024 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 647693120 1250 647691870 647691907
    0x40f2301060915082503080c0c15030f06090910020706060e010f0b0a030c02070b04060c1406220f02100c061b0504030f020a0f0b040302180106140c0a020312 69
    0x100c40800000500080750040307020b803280401c14080b0340c06543c17010043c04158009900151003258040b6148200210202d107800e14140b01b2507007050100c00c80c4400d0f070034500041d00e18800e162a12030002c0d2072030810a0400740c028001800715a400b4489040c65030507a4004002201c4640d107c54040080c40511144140981401c004c1380010750300780540c808082c041c0c0c02d03004003016103c8a05036074050080c46414042c081c4007a07020703030f0b40e62180400f50601ea64002c2c212441b200c007800b007070340841c0c0101d82e0724020507048030786107a2060180000c4400c5002d01c041030b41c001d41443c0002c80181c0d10003030018403140c02c548680b41c1105580c20250304840105414031100c02c000e00d84000b101d540081101d007503e074882d40b4410300325000c0c008900c0144840d045000c0242100c5000314240743c4c404068402c80e4400c860902840500e80c00490a0040c20300c542c00100b804010a400e410b124200604005d04003e03084a146a0250300028540000302002e03181141300010205403880707212100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 647694370 1250 647693120 647693141
    0x5060604090201081b0906040b0a0f0311030105011d03030a0818012d0e0d021605010e060f03041703130b060301141b09040f0f06051008040f23010609 66
    0x421281c280c5800203070508100421001054058201500c4110b0380b940a40c0c0d1800b10241c58036844a494001c0d0030801c2d400003d668000c5440b00189181040c0320b801007803044015661100d0460340b8002c01529031b009414001602c125075170a490800d600d0070405802441c0d00c80da5104444d0a001082031040d010070b0b0300f8040d059047c490080c03485100e400d0045410300304d49039180b000805842c0d007038005150640c2c407134219002e0b40f010b01d0071460740020404141d8071016822040c10f035a039001501c01084224015411007000c2c00030420b080e0f407500c00766900501560f02d00612260424001c50164401c0b44d400c02204203a0030740f031003440b14002143e6440b410070b40003007001c80d101600c02540c4038001800300d4604611036500c52481c041003000e9a5480d0780240086c0248410034003603a01910032076690000c20b6140c85800a514500368106081c040311503201d8815580301c81c0c440807100d1801e10415100a070a1400c120005142e065038200703d0a107240001030b900b03040c800014145d9600100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 647695620 1250 647694370 647694379
    0x30b0a2403050711120304082203020f04150b0a110f010207032c040b06090406030302030702180c0a030905031e031f050f09060a0e0f0f0709060c02040f0908040909050606 75
    0x2d054180c1c1c0300003008032845d28050300554407941c680c540106c0078813403540e580360520b81c1800002c40b401030605009003030b03138402c6032000d141551003010b0100312801065044a14038410703004200d592010b100800c904502881c00c600c1100303442c424249040b16400340960946e600040010506500ca81904009840418140040582c4021070703d1a001000e500510460b07694500c41250342e1404121140340c1d42c046c00521a41d5603900703000e902d940140400740d000da055250250f0703c0c031030303100c100c00d2040340008102810301258810841c0100f11503841160944003c109004002104426801ea25210319090076940d02e0031491240c2c415100b200150481c03004071000340000d03542c43e40e40748025082621240301540e50303140090409001940142842c0d0b030380c00d052045e000700040f0304600c20140b03440c0601c0c003500c0b51174048554854600c81c0d10005007080b40300c4070040c070b060341022803082c403113941c0854440150703158005542d10940c4071505140c0e582d07032824200305c414014035509c08000c55 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 647696870 1250 647695620 647695637
    0xb0603030c1606030c020703020d030e1809030d0b0a0815100806150f01111b040f0509010c1701180207031e090602071a070b10081506040b120d030b0a24030507 70
    0x82c0824150f5032b0400d0001c042c49503885910000d51510703408022280342c2040d004034107040140780113071254011020070074010309140c80071b901404c20200c41000c80e442c0c2001444913600c0c81c11500e10240000c0c1020034032a480000024110304204440380c002c2d41c2ca0104000d0400515040050003403103004841d05114521282c02d41c40040442c01b003121483e51241035032800e0000d000500200200c020056a40c1c0c60503041c0301a140c2c055214001e014815254010b045c2d002d4802000990424410a0040c1c0718014034004490780c9d90f005451214400d041007a032559511041d0000c0841191b07030f040000d200140c0801650358104660b1780103003d03106201220400d000071308403441c41880400b070044040c10000c126034400c41030061006010820a0790016441c03040f07001070601050350010310860900c15a40042d1511702d03000102d00303818000400034030888600660240003103021096010300c0814002070385e00002c4601d410300b01250501401002030894000c1c0440b50042d1002040141340d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 647698120 1250 647696870 647696873
    0x414072607081b070c0e13031706010e04060e040c1d0103061d0f06090105070e030c21071202041b1b1e05030c010e03041518030206040e150405090a0b0603030c1606030c020703 77
    0x9124109ca41103511800d0440d40c2d0b0fa070042e5400d004980d0680c0d0410700e031910000c1c1d800664140240518801d007486072050369951005000d80040008804481e40450700420014071140e2243d04055000540080c80c0c2c5003916490f41800d4207100b182a003908940d0400003607801c00c1c800c4a40c80111801c14002ea940c1c0c1d40c1c0400d6568010000700342c05100101e90341c2011217010b80540c2c003071003440e2044032803168640702003517041a90407100301c4c001e6041403568a20340400e4685015040c480e80e8a1440780d81e101188094402d0000f02c1c240c0c2c6aa03d51030140d549074a1501c41905010302440040d583c030794842e0707001404c465139034640c90040e8000307000c180100040150654005121440c3c2001511880040c00e003c903c61503000070751254000800144646440389524440c030b0102c05552102d007540c80510045c0e945c2200c2c81821a044070111400090380500c9a503000715010b01221704140c170041007940303002b01c00c8104110036001c900c000c0006a6042c060200071041e00c0c40a80602880d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 647699370 1250 647698120 647698127
    0x3030f1407020a080705030d020f1803030720180c090901080d170a06050a0f03060e0d080604112502150a120506040207020414072607081b070c0e1303 66
    0x103103001019118001781e0402800f03010020340380340171110030b0215903920280c20800c1040c2d101c81c141c0c05a405031444108400e20b00030040c0c50340c00c0e4100301d440b280804c001c0b42d000362400302e4030000c0c0e50155030303007100c00300c0c848403088107030b02c104075400c40e0941e80c0408100700001ca1005900080c0513600c2202c0e40300c03240f5031100740600013240b5403003810300640f2004038940141515411040d080072503440b000a81c51406900441124001e0310f00304248101740d8030258407000341411510200310038070003007581414554001499280004081d60400e880e08414421490100c010000d05000f0301854101b94035011110b0305411502c8018145014003000008d40800501e40001d10710035550780011301c883c0c90b00d404650506900a00401280b1071004504000d4403080e112600021001030310b03c7c0e407164041540b10301c8650119050368081c5d98480b011184908020100502c00b90300341d040120f44000c0d94050900c5522640d82034030809d0078008120111107000340f4015402c0c000810340804a0b40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 647700620 1250 647699370 647699383
    0x7170103080f090310050424050f0c1602040212011d15010315170f0606030106030c050d06062303010b091e280f06051002100b010c0f03030f140702 65
    0x81c948500307854101c40c00000c3d040000d080329005c0682d08102c10082004083c0803100003041a054a0204d407440006420046800480c1c46003149449400840e65916602c0c0c0a01603005180100261032039099000c00c059800c80d045c041c0010b41e244d001400184042c0b203080328400c105e000c0b030000e540380481403000032115545116041c0369641e40e10000304402200302d0743c05040d8280280a0754511950030075541d51000c0140e002d01d00a040101d9064a81801648200ca820840d800200c0b03040c00300704a04803103038000c11230300c003a9280c1000905038004a00e80b0101c0c480040a42075034000c5106050a44040e280c44071f11900011082004200c00c4002c1404001030b84450b112980d03442c004002d0359050b40c00e2070200b4000d400c132180d040418068104010402c00c4640030b024240c1e9540920644c101c0e000f020380d0244e0040f41048480c40010b6100103001041403404e00c09490264442224000c4581c5054001a440d0036060b0300d09035640c044e09107800102c4071102014a00000025104c14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 647701870 1250 647700620 647700637
    0x816120c0b0d061a0a0207140a0303050c070504060b0712030b0d0f03140319060e010803071b15030e0d0e150a140c060106121104050105071a040b0717010308 69
    0x719402c198001d4540c044805401007085516101d03400480c07036440e9030450541140144a072600110f00c4010100640940342c0000c0e040c3d003032040c25540c0c04d544035001b05200c1d07002403042160004242d50b803406454020900540c0d4580c2d10b40850a181c4034511100c0006400e050402074403030f03d9500d800030340003500c90300300c043c00e00310baa2545070440d09200c01c12a40580c003800030050002c0c1c01503505c0503100d25654072004100382681c2e8100481b51074001d03c00c0141540051129a01080e11810301181c03c40f400e0342121a26034540000d03401c14801c9400e01400640c1d86c011003c1c11070b03002c10044002080324104504210b08810004140903290200706001c0e400200c3d0000380940603951851200e01010a0305071200d60003084141e5a280c244107035800504140c00740c00140d0113610916030700c011840c915515140c00c0c440191441c1e804002c1c12107440c5400140d016060b040c03003824a014034803a5100e8141c504100c0c6008205100da04000d100001000004000081e0540120b0b88c180 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 647703120 1250 647701870 647701889
    0x203060109021c110904050f0910110a050901110307050604060c210f020d090605060423060d0c05100f270509040f0203060705070510090302151f0816120c 68
    0x4c86601101e51400d01407030748034641043c100001d002142c0c0305240e00c0e42c442d41990342101c0c8115030054003941500c502101400d44040c04000074460f1611660050105139010f04000d400003144050492840e84440400d603403135000141030000b0800a4060805c48140790b142c91001c3c040344a9a0480c034501c0ba15110f0303485651040342d076902e00c0d071907010b40711900c045540400c00c041460400c03801400c403c5941f14841c610780409204072084100175172004520070340342c901c000d6849000307006201c012020261a00480090005101c0d540da541034031520a43e40d40d904449510f01c074002e00048184484280301c5084201c82041c10030303c05242c1c40450388101c0300210325484038240952162070480300650980039440400c401e4980110060010030b104000301c9100c122856521021546510001401030700042c40f60710175026081c1005030840c404101c41e0b51550740c080f440e140c0803c1643d104441a401c9017000d1500b001651065600800b16100c01200008490345d03050091507203401610b041c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 647704370 1250 647703120 647703131
    0x6020f0714100b0a060816140a120c08040803040807050304090e0c12061b160606060503090d050316120b041805060f1b071103060a1d010b03070b0919120203060109021c 74
    0x240d610031880c0400c0114807070000c950f50320004e103004128048910540c480039007000071201c0214400d002d0cc034440d641003144642103496950703900720740360700188003070759980300c10320011171501001d2003090a0a034024000341032903041032041c000e802030a020a085d05401c040101b103110700c0001c4a0070010700d1038002c0990741d40c800244400c8140100440038112070b1600101203500ba411030020b5004080381811568000d0110504a03080d20089440d0102e03c0300c044200501350780a2051445403041030b58010502001d241c012404482c0305007008120240c2c803112082c1030007400c1c012950010070358006074502c0d1070305464841050b1035540e2445407160000a030074081c40f030b441070a6413000100a0640760181881d40340c01005c1c011541b21418010090300071609404414840c07078404280160242c8112403801e40c140c1740341d400a1071a641c020440d0f1320003020080c4200c02040151402d10300d59020404d01e40103042c60240140c01500c00e062040000c1c0f0780d5410b0110501b80d0154044a01050f0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 647705620 1250 647704370 647704411
    0x7050903160815011403100b0103090b0906060a05010323100f030506060f06070218060d020901080f0f03070314090a090c021c1b06020f0714100b0a0608 67
    0x41d1062400da45000080c5042000c1003012010038011034100016801040703503621070704450058000495100e9065011b85200c545030307005600180c00c0300d03c050500080804003500d41501140080343d5201c00c6400c40030410045283c01011500641421718041140c10300365010100c0070248004040c0d9510003d000061800d410769400c0c9000c0c0a04600ca1203070350f0360b01d160ad9903a4080c15126544030744010020b084141c1007110607518015002032100c0342504110303e82841c442d102402c62500130740450612001750310b41040060003400d07a40020310101d102940030605004280f5140d8456070402c0090301c001c2544450300c00342070030b00e00a855603601c40a80005000388040c0c0d01c0452a1810003280b841000d070003046044c2402403000e00c0c02801c4294100032101d00d9807860050403014440d00c8240c010481d180d02400c000341000d04134501c5c1000580f40c0303560030b151100040c0213562145e800000303502024045c120340c2e490152901480203051620180522a00810311080001001061503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 647706870 1250 647705620 647705623
    0xc091a040b0c03160c030b060f061b190311010f2d0b090403030e070b031b09040b060301080d090509060a060807020a060e0a0b011d1b04030203060a0222030b07050903 73
    0x1041c13940181c260b003000e844140307401103070400148025528804134400141242c10316015041d09048010400c82c50310043c0d00441ca40c1200a10445445214a8010300343d80040c048640200d00e01a4407032141e1400c80c170050a095556030341140702500d00708070342043d240504800300c14502442000041d50045140c1c03180c4010408803c4450f840020042400103041e05680100c00c40e034080e60070b44111079201c0000d207040d4441610312000160302601001404101c1002400314180000d10101d828404a00043c203150000e030000d00c01904282e030440380407600710024400504003070703590713082900d4480d0004490342c4091081c00c05224450300025030b868801e001a04a0941c44001000341900070610155580c1d4810b10855000e903583c000030640259410090f005030210200e01e1072145d845070701e8040c41040826001c1000300c070900012005030781c284080f5225501d0007000580b285d640403041150100c420081c6110a810034009201051000c11708a901540394106540e0b51812080802d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 647708120 1250 647706870 647706877
    0x30215031e160f0e030c1207050406030b090d030902030a0f020105390c030613080c01060909030e041407030b0307090218030d2d03060909060c091a040b0c03 69
    0x10740300004800c10404180a0084821182051541d400180340140942036a40c032201400343da905500c0710070b00442c103140006a0b100128180410f450351203603224089404c1e103d03182c108440e8002803070304011701e100041068580d00582807505002980154001ca03840754540d00015100e41c1c0407650200669004008844841207000c00210f0003000381d140300e95401c140100d010036040714842c00c072200d203500054200c00101c0000c01410f45610b92940c2a600410782160448400c1d0050024107c1d00100b84207140082c245540301154000b01e5281c010205400d0241c039901ca50314211400000c070280c1c001c0164042c00d41d0030009170b02440800003070710704080e03035100741c040d907000040340100d0001c02001640d00c074000740d040f1000500b6a070300a650b007015904a1840040300101c00040200c200604600000c0031403c001800d036889858150903510401d600340c9107291205200303980150300200f0f51004000410200038406184207007850f092185116a00300c2d510003040f00601000e00740101e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 647709370 1250 647708120 647708161
    0x20d080106172d01030302010b060c0312220318050d081909090e07140916030c09030209042901082e060612061410050a0e06030c0c060a0603021503 65
    0xc3e54a55003100f40200c141c2d0007408100c0055080c08501100d03802e080f030596840c039181d8800345040411020075a07140c080005e16401e00c801404001e01303c0b0f003816003000464103010342e07100e00c0218070303244144071800d6495104a02078002031600001042c8a54165020324050007800c40c50b030841d2074421211001c3d1900280c07034082c80d150042c4101d8400056480803188801d900c3c0d0035914500c0100094941c1c00c8603184c034840d00258485821b20f10950048009901030b080c80d00d0b055459401003400d03440d00b110100c0b802000070070729851000c04455101d9800c91100b58802080d81460146521031100c8008040c0c20307030800d01d02c042c400740248140b0380b805186440400185d0350724800200303221800f1045152262905502081c120f200388802144007074040c200980c00c03104400d0440d03140c1c1c05800305030200190344000c0307074844e83c8a2000754000e070981e4044980340d800c0103400c281800005010050240e280090070001038856840c071605400040007025120b035240d640789800e01120f10752 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 647710620 1250 647709370 647709421
    0x6221701020a030b030c090c0307031e06061d0a05010c170d0b1c1109041110020c1011100e12030a02040e06061602060c0705040e0102040303020d08010617 68
    0x101260841055014040707040041e0360900403d103043c3d007455103800544070925003041255001821440b0800015600581c040c03400003040400000002c0c00803803000a01e205854503400b0401c03081e5400b0118100901d00005c00754600c0500b00001880c02040784a118140a803041100f01400414006140302600a030342d038903510382c9a4082000105031300d1003414800c6c0c0003140d4150070310142c0d54a200c0420303441600301d85c0f03040040040140c00d90008108aa20f492851456249911038250f40140503846800410102225200b001085844040b0080400c5a140c0c6d4918501200088001040e20301400001c3c20300b0640154509180642030040c4420704004280001c7c0c03842c95000304204d07802658030705203d450740030400a4600c42c1c02403e410f45144030402c4409031403e00300a145101501080311040c0c1d59400c0446d0943e2100c400d80c010030b95011030304005054050189024041451070411a20343c10000d01420810030790050641034210000090511800c248001524010098 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 647711870 1250 647710620 647710649
    0xb130507030b07020f070806150d12090609151202030903130305030301050103051b1806130f030b15010507060903090506031911030c070b1902030906010807050607020622 75
    0x4201802d040280da0000040c880c1d04010900e030071340032407000c0903202144c000c1c0c41144c442c01c0c00880108105030440d82e1040605d00c10070001a01b082c1000191011034880714410b614000024185d0445130f40041c0d018921764406c160510380c02043c100030424100d00040c6c036134450b0070714145180596400106070046916001c0203200001001c0d50480d8403d03070342400300e0758503489604140f5081c03d040303000705030041c05480380140050101150b9140040c22260500341c0410144007403884a5000b0903908203889001c0c4203001400840c075500c00750651600c41450030102c0000c215102d0340c07101409050f0ba82d12048201441071280300010200141031507101d0a0900b070b0100304900349100c0b08501482c00f0302d0b0007d65180401030b28410b16004081a080c1920ad88034440c024800510401ca078203000400c070019507449201460084207081d0042100d507041c41c0040385060a80d810080c0b144405000c2800140c0c2c0c3c4d041290015150034425803104059110b80c038400c3ea516801a005059450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 647713120 1250 647711870 647711873
    0x120702090a0e0304060504090f2003090a0507090b1309020a120804150807030b121002220b07120201050f060d023001060509010312050f0c120405090f090a0b13050703 73
    0x1b0010700107940050004101d01d00700c0312a084202d640d43d001c01301c00000c1882568264507100d00103581c0c0001007005541a02800307540c2c0c18104401d40e000480340715a180e80d200712504100100780c01c5560544810024034101e500040d014034000c0c81100c101c2a011070115080001203000c0c0c800415180000c11210307469904042c081020440300c40700068608090a08140303820440752002510032000b4000c0001c0050b050b1010354045d01c0035441c0799154040205480010301000c10042c0f0000045e5901e4a12500d0480e01c00b86000340e028007103a041809001e0402c841300c8016800640032a00000c1035400f510110b0705102c26580441060402100010b1a100843c0060501170944a0003008020f031100104140ca0b2020b00016003030040f462070ba565403e000d00b004001c03102013644a03d04240d20398074801e15115503010b240ca000e1901050410040c00d002e07600035004030035108441060b140002800d0f0361004202e4024145d0320307408021495804002c4994034007680c0120a07100c803103449 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 647714370 1250 647713120 647713127
    0xa081603090b0a050901110604150b040213030f030305010f0f090b010e061804061a09040e0a02090a0207030f03050118051b1b0c01020c01200c04020315040509120702090a0e030406 79
    0xd0259404200c1401f080300206c400403c8862203240d21a0044002801c484101340c02001d12800032900306508001d090340004446000600a42c418024621070340510302d8014243c40b010703440f24107942031040091100803000080503081d25480b81380001c001ca61a801260b090709150002c075007003070000a010215040305484031512280a0b40d00f030100c1c40d030380c0c0c0700140200300b800380070003002c6010b2010260900c0c2540040c8102d0720312008840360103400381c0018481c9041510b501342c078180d000861408254109201e0013131504103040400040d03242800e1100811000c114000900d41c0d10000120036030072406001154140b0010196140c41d508aa8a804900c0ca0800f550b0302d44203404100000d5880012072281060041c4c0d2410b001c1d11050705e40b81c200b5051800340040c81d0140103080303403003070301c2e2403014500c40c0d00c1e042e2110441c00c90304010301c41120000741c440c03801034000b9401c00803d4030b130200840c0e103400d40c107840845a9554049044008000c8070f0303035280c0c04e17000004001408690 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 647715620 1250 647714370 647714377
    0x603120503090f0f07030f150606020303090c040507120207150c0e031009020105120403030902031603120906021b03010b0613150504141e131a030a081603090b0a05 72
    0x201100b2140b00f601e8101d091035880c812a0302d5a0040c2c0c1c40b900301030001880494920341c111b44542020040319900c800460203440c8980c001c100103920100400c6203060040204c0303400401c06403070801c0b190808800081000c841c025030746003095000500d0404020031266011b545c40308522040119440749880140412090410303a03100b40700b030700111203180459105c0e03820940d905849192a011900000186058000307100b40c0c14107a4441c55100503840034440e0301556081e1440c003645840c1545024001d2041001e0343d0401c200060b0024414207800040404905401d86581040030a40500180c00761154140264121401080c801802220260201c042c0c0307090041d03059595105100840e03950103217204000500b07019142641c21820094407401e450340d00500d900300d41c0b018001c04140c0c50080f500110307120f5552407940d040040c0341d42c400302c40503000c1280a0484245240c0f911003503070142401074503203406607003034aa04060040034202c0040c250b030311419072100a01c6801900ea40c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 647716870 1250 647715620 647715631
    0x90a0302010e182a0f0301090e03041a12130308040602090f030a06062409051e04020319110703050405040e0f0d090503160e0a0b011b051b0901050a180603120503 71
    0x9041d105807a40c44c00c0d001030341c1d100c1c80342008980c02c1da0300c1e204607a006002c20b11401141c0e400308000216a0640c013143c052502c8044503281341d9500096042030030a108010079000c400080246007800182c0d02a644e0b5800c03036003015003d85c50b03150341400500179000319420543d0622850a405080100d1508608112407081008000c01c0400086680004c050a19601c0000b10150414040c41c0381c5400e50b0b10020000d241d211380d900c4505401b240880c0d1017a22010459100003c125142010070301883c0c00b044140f10307605081c40304d140d40244c102c0c080d03401500e11a40d140d40817100520010001240090016812600e045000c0b02c0c000c1c00c442076501409029002d0721003403507418610b41140c01c049a41a4041e88055615042404004c0070a481d2040c10019250ba1082c2050300c45a00c04843d1070003000030300f0f480da041c3d1104820f000400105903000e5094240100940d6a869400034200c400c0e0242c1072018403141c5640d90010500c3d80c20003005200f010a000c0c820503031040241d842031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 647718120 1250 647716870 647716921
    0x170f060105090105061204051c1e090f0e0901020c031c1109060f09040e100b0108010515090909010b0d0b18161502010b0607050c15090a0302010e18 65
    0x59032118248140c2882c2406402c1e04a0fa04000c032820108a0b0052164814020170a44001c0341030301e80d03404e03154402c10480700c000450b84d904481c1c0c000c8101200c001d50000c0c60500182c85071034820303105100c01c5ea41c81543c948003051400911407050a4040b542240488415070b0303510501059144005186080000c42c05c0d0b24042568084680407001c0702d08a50001380060b0031300210111a100d55440091415009520749010480d2450300f004100200c6400c84000b103032490444000504e10501603108601c00c9801e4000400b40f07401c4e00381226141c4509031265000e40d582d1a8005000d04208105144c0084110204605121246a44a010740c0726958080b1120a1200d0026079840c5020101e007440310600c030040003002c040c0e650300c4074504518000803804a94107400143c003a0401c850a8504c0d40000460302c030149400f1490041112200d2995400c1c00307882c1e00030071003c20320303404000d0611101c10416262940c408114203400125615081c1240c40c007407903682808003900382c0c1d86400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 647719370 1250 647718120 647718133
    0x806040305040305210702120c030a0606060f02160303050307092102040516082205010e01020c07050d0c060804030c05012d02090d08070602040806010b030115030912110304170f 78
    0x211041300101742c81c04d034500b039680f03040034042c0d02040400460300c8041d100c240704812101110340c409000086906e80258000a5240c0c07408070082d0000810748891000c541161004070817002c003c03100d49081e43e0301071a055481e581c0380001590500d03010b40101d840f980060341c40e1b0750350b045070140d500003040c402c0c0d5050102e40c455104180c0c0b05003940b960000402c03040c0340060b50252885074407982a604482040d003000321325440c1e050031581c0202c0d0382c580507500080c02d500f1180b0100014401024281e900004803035103a2210710720004c1038002e1004105107000450309143c4210806a5880c0d00320008200090a5440b00d07003001c0c05404413a1540906aa108208944c081c0b083d1001c80034052302848a001e2281c1e42c2c421940d02141085902c29401d110100e901c1c501044140e004c0c0c0400c4088030b50b80d5040c811001524100d0300c003020300f0142464031000c0001c0445c80b00010b0021203051200c01143c46444450440c020307604065040741070368071510141a0002210b02000c605d400075100c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 647720620 1250 647719370 647719393
    0x40305010606093005011e090c1a03010303050d09170304020306063a0b01030b04030210050c22031203060e060a0e0f09070806070c0b07020f060a0207020a0806040305040305 76
    0x41414004d45034240701d4200b000c9045143c04001c0d29082c107107200700000986240c0001e843c14a0790030b181009100266602414020042c000001c07501605d00c5d9402aa440c0415100c80c0e94144414000181007040c04125400340301d42d903422480c80e00780d100003030f00c0440410300880b03409904101c805070302c20b10a020110302c207410000c002442a018006c086011041d407a0300021540c080c0741c0001c0d0700b84030300d51104004103c09070040c501031482403108843c203080c64240280350401003440d8050036843e100605c03121624400407034200362184240c00102c40580710341c900e24940c050b80b0180c5500c448540441300d00703506901c06010f85080201d9018075849080c00d01810280c10300852162101c90000300703c2d45c41014822980c0019140c0448848030b44034000a410709800382c41c2c141c00b0402c0c452030078003001001c000281e40b100d03591008050354480d4180e160741d607104c042c0803031084960001d203039410354840c19003520280001030110341c3d943c14640f4001305180e01c039200c00e407800c0c01120034408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 647721870 1250 647720620 647720639
    0x3060c170411040e1608031908130b060f13150f08251a040501030c0318030f022409010b0909030f030a0b030a12030b030706050f1e04030501060609 65
    0x24003079900400d042e40d00e50071102c00d01c0010301c1e542103403503034078070540319600e9110b040c10035414050484100074644901207019805040107400c407520341400000c03801c010742c100010440c2d418403600100d0b51100740c0c4900c008528483d12500c140798000d03280200507400c014480c0c1004003011540311640e0f2046944105d601a501003e00805a0540145d402009070014503089407100d010074400c00c1c1c8e0042c1da95407622a00218099002c280ba2002240c1000b0070743c1c040c403584504200600382030044924000191200028500c0b004041c0400b121030a480a803003081012034283c000900c0300ba000340800681b10350b8002c22900f00c0060342c240512844241000c901d5a03020384e00130300c019810070407181e5130044190002031010605076a119070345070341e6990400804c0c040b64050751018440070881500182555154034280e80698020b00303041044944c070504440a6100c403041094903101603084091410307842c02c0401641260118011040c000d0640c08907003111304948458204a40c0d550481 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 647723120 1250 647721870 647721917
    0x200609072111010521040b0a051909061112100602012702011206060807032d0b060405190f06080c1b070b0a050403060605030601030f12170103060c 65
    0xc4600d0074451044200140701d070301c03a0030710b031440504006040801240100e0791030030300210f000c0c1a05051400340020700c038280321242c4e08510100780038002c91400b00e001b2456641e03030a000200c02551111041c092001d50780c48060300003880c803c496500d590200ea06800c2000540702030742407840c8400c002400c00d00510032101000080030b01001102801c414a8140144020040e03042c00748185c1c140d090080d030703807150701c01030107407512003040608000380000c00301c922014081c03154100c103614400d40d45054090343e120b14544090049010300e401c4010900f80c0c0115400b00390004030105805110349071050018003074402400d00110004d980300011904818141d41c200f500d105d0070415200070702c0030054460f80b120029800c5405481d9985003401180d8040211703c8002131001c2000e2041103501d014540040c4400c0780240b006504646512154481c0707004021300402c60f070b074010004a8041da00380242802400d0b481140e9603901d081134000390070340644400018110082003494001d0f20350f4032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 647724370 1250 647723120 647723159
    0x15051906081912140318010c0c0302071815030b070810060e0609220b10080f0708040507150f0e01031401361d07060804080a20060907 59
    0x7140c07051101e075210f901e2071400480540d000c0000121102109200300d00013140035580f1036159968002e0742509090031181c5010a41007000ba00c82e0340c54010a0b8002002e4007130715003420031015071900c0c0302000c80040c0180120780121481c90740300001440011410390b886003805480e8503055984070603040d20401540c0c00b0b01e0001c544444114807850170510042c0c0721307442c40608035548190043e40321450b04c5904903000c20007103481d400c940b5880d08121200180980c1e080c149245142051718100c84100d000a1002d01044200c2d00001c09000f0301f044050000d00c00001c24000400115030010135803100c1c0403130400400d044040c500d20b154030a1080341030480b6400044501a406d1030a9101d111074880012592080180d40e1141d0301d8400380c8580440d01c1c43c0c600006451740103084407116900a03890001c01c560410101001081c0c1c12084180e44280e0000000d03a030303800b44102c244c4e0110000074805400e80160340701c0d19180c203000505180542404002c54074082c2d44e0301400104408030008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 647725620 1250 647724370 647724403
    0x10515030703020304020402070203030313020f0d081605120c060a060f0803120c0408190b07050309070315020d06030f050105060a0503030a200d0f030b0d020f0d1505190608 76
    0x20700424420b50165400030310040000d0701d4018035400003803030340d002a2001e0529160565081c400c41c07a100c1011105400700ba103a540c0d01d00307829112402c450141c41d03841e031a00301084620508000f0140090b400d60226800b0081c3c4800001880340d9445004444a102451900c400811840300b001d4603038049882c80300040d0f18000f070020040001c40806003441220b010284400705d030074001840070031401c04103c3e00d141000e214609060100d40c40140141003401020800d104c100718002c0f0707000d01501c1c1c00121819110b442c80c0c14401c028400e0140085001d840c080c03000c41003144000c0e0100080d030185000340000d494400c100b15211040d842643d40c99481000b00440f494084c50025840c1c038012440c004000424550590401b00d851030043d00041d1034510000e9083c1d0984918015a00e05a404806402c0c4036030100383d004030b81301c180a2240548851f64420012000450405a00c62070010b20080c01d0441c000003004002d08403043c0700740e04205001c038020500144c40740c4992040384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 647726870 1250 647725620 647725627
    0x90812070807021c06061205100b03070e0711100f0c090e0720060405060f0106090b0a0c11040f0209040c0314010905040f080703090f2903130f0c0806010515 69
    0xa007042080c81e050180d0b0030602c0c1e800c14000005c555140705420050802210100040e4200d02d0001c1c06c03c15184c090100440c5071009030a00d03910005a98400d0380d031019102c4d941502e8100d03081e40c0440c4041c01020240c4a654001140e4000382e41041080e00342c21401446400c10407802514844a2800740c060071152030340c002040288240c2d1031908000800d14907007020301070700641d9410054100c80503100da90140c424000340220640a184c01403c0b6171411180c85ca00b0610b540c0b00e144100302010041100c01d00c034030001e01c0b449501416103a00000c1c0104802e0030b5100000029400c244d10311440340340703040485040c45000340210082000308800b090102da00f0304904200601024105980c09410381c0412400101d03000000c000390b0b40607480d4912001c0c90960142020380e036a40081041000c014041840030b80c4642d591000e42c85000321654907542c448c031241042c140c00c5000500551655198402401341d81017100007622000800e48a090380c13180203000540d070001000c45400710080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 647728120 1250 647726870 647726873
    0x140d120c03081303023021010b07030518011e081807051507031704030c051c05070308041b180605030706021911040515040e010b0a1202150a090812070807 68
    0x10f1006e03a80b001c1aa000110b030760035280c0000c2d401078006804142c00d11072255644019000c1c460001e50052100010750313403914a10382da0040c0399001302046031030300310000003440e206603004d610f00d0140b411540d2006c12085200550041c101b00041d102000c078610002411610303003001040000650720060051505640421484055507001000a4041002000d03000501d82551039900b4083ca00136680d001c540a01410000d0811b0b1400c10788191094031070103068011500282910001605030814408543d2103050030703030301c00c0c8854440010380c2682500105070b001d803d5000c1c42000402e50030400100e030700c030000c4c10b55501c01c40c0a07000141c2e1000c1c103c40d0180c42102d0b241c00499114044022072244118089015541c0036250301c0b102145425024842e400c0034030034110203036031100081c00400c072001c01003010011f003406403030450050640c092081d07403a00306041c6100b1143c9140f440d562100c5a03001085194280a070150034041c020703070603114000325030a4845464001309002d01e000c409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 647729370 1250 647728120 647728153
    0x3190614010809010207230f03070308040f050c0a0b070b0f0403050910120f06030b060d020f12070b0310060f141801021606120b01050301080304140d120c0308130302 73
    0xb4064030f200d6400704020000140300421540c06401049000b03003c0010b45220b160410400588166059006000d600d001c81d03800405035810507041062000014603501301681400403c40d09250404020100060301c5e001c020001d01c0301c039001321080070b0140c803084608110220300791005000502e040c4840702c500e02e00442000030504442c20207421345022105150240c901c10100310300681c2e40c0b960200140481e10701c416500c808101c9200d401310035603600084500c184000003034050312062002001c000f80422184018040c0a48230036103034500f000084a80c1485400380c1d800190035a90b290319150300030001c1c10008400343d41200d0801c14550030417840c454158030700ca811481a0800406400c2150300721002518580c0c0d520350201d030000c1c4c0da51082e56a02a24030741048410030042000c1c00c00482658169054501d0810203032a1840c009100e800c011207000c0c0c40c00c82901031100041d908800c1d0074296038400e8075540d030165074000c3c074200080c03040c04010700984c00c038070184900410b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 647730620 1250 647729370 647729387
    0x60312030f15140d0c06020c13020a080a0e12160203070512031621022104080c040506061c020307030f0e03120702120711190305031204020d0213020319061401 70
    0x10701419508001d01185c4946030700004941c404005a041780c524241281416400001e00c001c0e8a001036252422444004024039401420040b1840c2c1c4c803116424201c5003400050042401c11184503128405c039442c0c04480a14000c04902c41e1151140000b41400c03c81440c031540b80d0190b000c1d50502c0c0080070704404404800704101c81b200307249003691101d511502c0654404e0102ca900400b80d0b910400c40d10140b07020054185034864805001c208608600003e50307010700171050f00c01058580315440072451a000e245810308200d03080c41c0040c0100507069009d0b6224060780d590500c103030a0101c03c803000f112036840402c010b51300100304c0c40b070800300c0031003a40d07801407518130485140f417642c0284030800e50440d16048941c9882100e0309041480c1904182d0405c845140307035404250b03c1c40d40c0c1c647d41da01c9107125542b442d0120000007015541e64804070341c080d0340c025001d0b450314244446c40f90000d50044039403496802d611882c0c1c42a100903441040141c426840360f68060141c6000151910380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 647731870 1250 647730620 647730659
    0x60f0f042303010515030c010c0c08010207080c10060f030803070905030118110a06021c0e130902310b0d050d0c021309110919060312030f15 62
    0x101044002a080a401034095009090076039100031220440109400c0d5280609060034039548603144c00440c0e40d0110b103000d8011800d00f02030301c1c2003800380b8002040803006d03803214120b0351010604d4014015071200826089031440c0aa504200403900900c0c212741c141c1c003d4004102c081c18007800020484801150045050f0030440e440b01e40d6100064251480020170320004010320703080c00c0400060103160a628a000c42d9051a00f84c10400d000796035240c4810a128800844010018002e00940e1505048080039201c150030f82601801903002c3e0a0368a001ca0094000c107020780071000720003880d0109201402d00c055907148140504d80042d003003400030541e100032440308607000101c0401081c2401c60711034950f1840745084d80100003002c4668900003900300d00708290200040c004c0181d154502c0f03000c0300c42c95202d80300d02c580101801c90541c003101d6490329012020050241d0090401014000c6940030301031058060b002c901502d54081c1c805086198029040c0000303441d103501101c110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 647733120 1250 647731870 647731897
    0x906090f0301090c0f080303010305250e040506161d0402030a020d02030f070e030f07051e060a110c0109050625120c030e0915010c17040b04090b030606060f 69
    0xc5000c100040e08480f014a41142d1541051904000c02c030a41001100180724440245003158034644500da2650381610716030240741c20650002c1c0c00c0c000030131209400b82c00100c0307100d801484c107460320b244c2c0c55805036030001c440440044114126845051300c003000c030b42d1008065107403250359028803001c0c0d04003629044135941c0a0001c40020303030031403014512648003511070b800d280c01d01c100e020700300340d4020940c40d01a801094240018103000940300d011680c05035040ca01c1c201100f0b129920301000905003581c45800000c0001d242d644c05400c2000d02c0d88c4850944031614048001502c4103541c0f8401c1d07982009090104034081122020701629031300c5d51141c480c3d03401c011590303410300541030780c03000e4808148035080ca8000d1580c401c2d0381c0c1c8102c2c0010341d00103029050035010b800c21804084146410000c42c0002c074410400720003203400c03020a031680035503215900d07202d800e40c5580082c090180c1003468005400042d10b00041e103103015840240c136441c81c02009554601450348041c0d405500c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 647734370 1250 647733120 647733139
    0x60f09070c060e0c12012301050a030b0606090411072310052e0f0f0b0f0703030b030607030b03060a020f1e0913060e10050f1201092307080111090609 66
    0x155164100705001417528007000103020041c0c00a90044030074405040003013041200018451074607981c0c8254140c035040601342110742e4440740043c0c56031180341c0610303801600344903001c0640894403001d01406c0d4441c9225607085111101040003c000360498410035034460325491120840c55131041c1c3c2c03c0241c0ca840030b0380c100c1c910322240c2c81440010350702291042d070003002040522036220062000d099031154025040b0718280715100c2500462a28290070200003480ca0b040500030360140351040c0d4090240c0b000d40c5043c0e10090000c20020001d0344c0203004250004d1458102403089800c0079081060f281c3c18041c190300c203030200d0100740410134461402040035042903030b5845804010360000381e501040e180e04085440420500c0a0170040c19610b03070260038402c56898003114068041c080e40c07241d910100c408a850b01420881720b01810500282c0501c0c0b40103034903a00b030f1800c4044032400310743c2c00c140d541c00d00d1400c0b42c03420711408000450a0026098902c1c140004020000006040a64 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 647735620 1250 647734370 647734393
    0x240708090f030a3c03050a110309150a05070b010923040c060c0804080303040803160e01020703080d020d06090f05090307050c0907030f18050c0a030803010504240e060f09070c060e 79
    0x4c0d48100d40b14140c0c0401da001c207100c0f180a601003020750b13140f00281c01035414001c80300013040d890030303030f4503002c010340103012030403039421481001038401a5420843e04d091a5945201e00d8005005115882d405400742c964862002d0304140f101c4c80c000d90f8021000700d06c0314640380c8110307540002818115983c5004120003e0800c1042002c0c601440c010914682c0c0d81c00c001f10924080490300f5004000d02041c8001e11403140e0f00880d42a0407641c1001d252903880030a0380701d00000b031080001c1c8009103490700c900840d41c00607680c880f83d1040300e911401c01107900c4641a16590b0300a41c03800500c50351188003444024200f00306000d400072860305001c115400003403010f8054540700340c420b100d20f040448410781448020441c00480134425201d02c480d90b4116100c000b414401405041e004a4456540d03070680f91001e4410414441d2404d821000c1d2a00c41c0140c11000c3d005803252481072a080344d404070306141c06149c15001d296240c680c0c074120041e03035680c4009030001070303c01b200c24051071940c8403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 647736870 1250 647735620 647735723
    0xe1207170d0e0d030c150e0a0609060b010905031e0a1a07020c0916030203130b09071a0306090402010e030114070512090102041202240708090f030a 65
    0xd1045003644068040280030180051890900d00c841078814504001214040781d0840c0742124103903082441c0c603406001da42c0d058800380600c50300c0701c046440340500702c800340000c55100488180c4110700500040c8040001105e01985030b004082c1d040e040031350340b0104115004208000c81124106030350050029850b00c01202c3e03203003c047e60304025103204010840d0f0f4140120821740c1c030308407400015402c142803200d1031000300c15a40410b05034000041150084800e40c10744800e0b0b404861028585080d0902580703611292284814038031050045101c07110400b0300b602d1062402030130701c1106580d56001101e030901c1041a042c0c15540e0707060290240b814240d0064418071080d150390b8bd50380e105c4d40000c100c1600c010002502640706100901003284c2e016031030010f0b1901207644541c01c0e60050340b800c030101075a0509403069440000c07449c04000014000d401001c20480710503130300c100e15405040c0c47d10302c5001c00800a03c420000c0000700c101d51002c00e0320a068018076109207488811018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 647738120 1250 647736870 647736899
    0x100b040f0305010e0a05030301091812051914030609040f0210111b3601080607120506090703180c0b190903050a0b150324090106060e1207 61
    0x841031440248000c0c82440000d0007100300d4500c01600404000009485071350301c0e404107000d085619502c0c4c0019048018503030000f42d0f1843c1d009802e0010a5040d00f1014005500600e0b02c40380415403240c4a40ba8039000f2400c140c0314001034400b4610756a070b01410403044040082049410001201c0ba00000da01c6140b0b280d91050b80c0340c0c03509010b500e02040110703c1c180e0b103821030300360306140051002c00782d84501c200e601100402c500c00401c2c51403010091004010f0162403044544502c0c00001100d020005040380140d11036154400c2c883d14641000f03054030f2080f1040d503023106a5102085929200c0e50080c80180c0160306040e42007107081d600d050042981e0340c000040c01c4408105105158015080c40007a071085080002809181d640d42036160504d050b8090034007000f0f080050781074100140603035240f01c0c004090300d4207075108402000340081070311446400c0000c00302c0001c3c2080414403500060b120291162410514060b0821000304c080495491450107a160000b4080d08560200d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 647739370 1250 647738120 647738129
    0x60106230a03150f08030702240307020d080105150a0e21060604051f0308030415110d0608011a040e010b0904080c010e0a02010c020607050c090115090b130e100b04 72
    0x400c1d40f0304201e120412051080d0042202c0c00d00300c0c10100001351000049400302d41d0f040d039940c802003840803c42c1500d0107240c410402c50100c00002c02a0050b40411a00a024800d0300e45511598a03681449404000c03803c0c130070b2a1020401600c0c04c031600800b16220b840e07000404076203406c00f0559002d941c0c080c074118084596809503040c00468a46070090a0340720355021400300c00503008c400d590002007598840908a42c400001040a111018411018001c0391250070720040440301c03100050f13944211440301041d8039081e40802c00034818060041003400200b061440100f011080100520500111010310365a4641c5441c00d5202d00c11020302c80c6e401026603540310300120800740e0030350355a1101080190010411400141c0c2c000700260011034050f145540c03107811071718100c1d207881c00e6400b9840d4842c5821000003000301c15034002d1070180d14195990b4112958400152206006425400c0b00c0751b14032020902c50404178100700f6911202c041807140103542d443c0e600c01c20a9001d81c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 647740620 1250 647739370 647739377
    0x5030106060201060f15170411030102030112030e0102070501140a030e191205030601090911070512030a0e060103050a02190b0c010204050a1d1602070911041d0108060106230a 77
    0x20204400e0b040000e420000304224805008440c9035840004d11890151f990340215603d0000420700b808940c0c6400d0480b150060002c56403540c44000103400003651000880000d602e2401c00c43c0c25510114251003110010784400b14001c004202c44441a0450a0395008044d500c0007228481d000404c030100242103688003148902ca4507080410044071107801800a00c0003c0043c0881d0344d0340705200804442e906940000e0030051070036000514400c0100c007800921401d03004016803510140114000c00c26140100414000d11060603202c180034400a88150088600c1801500300b0340c81246103007501c0140c1032500707034450540d80704541100e420149183c0d80407405002d98141900d030000a4100d040c0203107000c650410070741840c0100206000c0300c4940707500280031198001c01c030f1385001c0c010802c0309000200c003d01081095401c244030fa40c240115000d0032032600c051401c0800c0c1602e4a800281802c0ea080010a80320300300f9514898500e2140000c0149100d25171174007030100c81140780e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 647741870 1250 647740620 647740631
    0xc070e070801120b16031e06052701050d260a080708151201020409020403080d0b04090308041b0b0a0c0b01060906020a03080603150f040515070f0804050705030106060201 75
    0x24004210700c90507003280500d01c3c401094400800e6110388250350011035000348041e9482108402c80203002d080043c401029400644604c0503041c41c0c10810a03070b2000e0301c400883e0031000b0142590004008004000561745500522183c100701041c0c01200c2d0140700d40713040c2800504414000701007584800311501002052150929a0111400360043d049240c03084440c1083c111500c04103030518409840361400c072500c07203c074840079011f135002008014000c5440b2652800e00c0020341d440362503010b90961034001c0e80344031840c2c14415201c3c03e682664400d0001c0d42c4555035900c0403484811006010081300100280840411000306442d02c0c5a80e143d8001452130b2601170341c44401a004030092180c0c0b01001c1c001380ea40040d42c0f49c4102c0d01864585015125000840d0610070100c0348070320440036540800c1002c503080d0820074082c2d80704104903001c0c981c042900c600c00d4013040c0d4281000480000815800501c940601908180620152100c09588030000703030071540c0365403216015175100e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 647743120 1250 647741870 647741881
    0xb030109050702011b0e0a180c0210020304080a1101020c01050414011505010210020a051917010e190f02091f020705123007060920030616050c070e 65
    0x9000740d07600000b9500081c026041100d282c1c1210401c04606502040075102c1d50a180d580c85450520051010b200c0b0030310840020010500584011064040907210f070b203120800e800c80078800c407480345030003001e01e60034880c0601080320710184140e940c101e159001e210004240c2c2081c814603010303611924400700030506800ca034600b5600b0981366840d4140745004200001c3c1d0b008903000c00316143c40c0c18010f951700040b030015503050254a6400c2c40380315960f1418030043c4d80000c140c00060041c10040d400b140c1e40c0343e21304001150100c410907206110129050794174041d079042403200d40164540907050202550204911900107520301101011100c0d80808e80ca4043c88054003400c42034400c0c110b11a2403102990340c0d808880c211241200111041c50300342003448041107010020000d075180e40d45554141803001c0c00d4203107000d60b941e10700c0064205503141c0c540d1010318055809405445141c2e0740c0c005445500d08502088001d000080005072404d142c1405460094100d0210801e15420074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 647744370 1250 647743120 647743139
    0x60c08011a03071215090908040503160f030f06090501020315090604060b03041b030503040b04060311040501230d060f18051e06010912060b0909010b0d02010c110a0b0301 75
    0x103414141c503500010014820002d52014a1a4030310240ca90049640208140d0000035481c075a0700c008003544c41c04081000300200c81c0020303c12180c0c1203044401400000748045111783c1644603005842500000801c002410895904605400342c640001c00034403680b600b41c00c1e40d00440b0204299a6044203c0c1a03503e4040d0259411a0068600308803490038582148075510019001500c0c2e18900c1110607104020f14210349c000c1c0d5802801e6940b9550f45040480b5182c00c00d0040c0000700b400d082c18001c0c000c0c668805e0303508445e0160344800301c407144d4a14a05080044c50848207040c1e208102c0c44800c84214080c4900601c4a0401154428a00a19000014040d5044c80110350420f0180001c101c2424450742800701c0c1c100c0c0b02041038840740011f840031092603005091005111001d00c0a015096003c2002c01006541101c603a40d503000c001c0d422075062071510340e07101c0c12a401e1705000d94482c0e25003c0505d407103040c24000c2e0162000010b90381e515154001826000e00100500c4008130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 647745620 1250 647744370 647744399
    0x90102031f080a03050f0904020a020a1505060d020628090503010e030708041a07171206090c0a03020f070614071b02030c04020306010216030b090706210203040f060c0801 75
    0x54115580c40e01c94281091640c0355406104080d04108012509886070920242141c0c181c030701c014011503803101c04141c040d440c0c404120040c0c1d8403001e688a000d4155145005081c23080d0b070000d0090107a2442c0b40d003080344175084102510611020003002e80049219980316003c03282c40d90300d036a66054034146c201420340702c41641d44001e07900107101c010009640213040d10103540c1c11908000f01c0b0986c445070500b0702e025102000c3e2030b040340701c0c0340510106100e000070b0160288007909504980d079450280070130104280c8803001d00c040e00300b0004510620a5000d480080181041c05d8901515030700d80006aa00c00142c00151580210900640c1030f0405000042d01d141390b510030204034202d800182d00ca086d04d4182074044c40e000000181140c0c801d001d84000c0d070b8802c54406003450344030301780b080c101c90045440d151700d803140070404507105d4040c01021881c9196079068452090090041030060b400140c01240c001902e07a2002d030014089029a03401c6a4250b664003503203624200d5400500007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 647746870 1250 647745620 647745661
    0x3050606101106060f36060121050a23070305060a0b0711060f07050f06010b0906160f050616090501031e0b0f130203180105060a060c031709010203 65
    0x2100c0a84a0b03109140410350a030b002100303d4281880040f1040030400c20030f5140c48082e4a02d68084880c3c14881c401100b40486100070211a04695500d20042d12140c0c400c03050740031005400440014401c12a801407a80118060404a03490311542c41c000c52001c2070811405030f82c80500100304000f0343c14880e840c0e0000301100c174500d40c6440c140303038101644144c49024203090026140150380d511041e00319508000588040c1da030710724203410451f4880003000e81c07006550182c2c42c000502c440c245000d6810320800140740600d05101c2c00c00f030380392041c10a0b0781191401c040910b281d000c540140720992203541204d50740c3c192002d00840c0107003e02015004103050516010450f448201280c5005c184848180800104e081c00480000d290000080f10190b00120030041c40f44007420742e0300a5401840101d181400300002c0c0100642600c00403100c207500a8841030040160511500c180c205690203810007039040c5907020750b0400e41e9081200c2a050aa400109004c1403000c0d6001001426 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 647748120 1250 647746870 647746877
    0x3091902010c1b170312060609061c09050a05031b0312010b0a1211070312021228290904080406030e0f07030b0f010806040317041b0305060610 63
    0x4601580003900b00740c803160020700000a050004030980c0800705880c4068040b04491500c8402813102040e80c076446140300c40c035207100c100c1c00300c0c0751810004203480b09640c0c001c128504002ea02030b0322050745615207442c500204d40701d11440012071820b00265001f140104d018564030000b1240c0e440268404010188950740200284511600c4907005035041d25420350380c2c1540d0302c40800b000c8440007011144000214504001c0103a4500148001c140291281d101c00040e0f00662889400320b004512036030a500c1421300c0040c1d407034152849001e40415243c11560195045804084102c0d2042002951891034221003405900d1071002e40051036a801c44d50b0094a103410742d179050080c0503034407810b014144c81d035080ba0004642449004c0c5412022011a420251349003452203420500b0703250303054546681c400220388180c021070410321030b075010340310749a030504d5800c817a400c1100d008006541186110740208044240740c0510b0340118040d0340107000b01e0508900300203c0189084030740050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 647749370 1250 647748120 647748163
    0xf030a0615020c031509150903030108160305191a01030803040209060603060f0f0a05040f0501150f08150f03061006020d050406080c03100f0902030106020c041a120709110309 77
    0x41c0c2d07030004100c4400319054a05000c5c039242c40081914015800c54a4402c4c845074a0070462907280000156040310301c003a04803069405205840c0b140803d013400f01908941008816407002611180c100034200e04ca940c04900ca004030100034070040400f13030000c45280718000300b40000e40c07401d1402c80f0b03004401225600d24600b0010009129001b281c54581e01529900c98010100d1750f03114840c2d0028003010b04144001c89c4440c03014001404240101255240703414410941f092084070b100740020840e40390135089451389085c0d03d070700f003203100c04007503200c0400c010004880e1402e03c80da0780150301c9105515140c600f01a8040c2c01d01c20008006420444c044c07008011440c0d200d01110303080b01114030241d559407a09424140152200e41120140c86419440004d22044035070003141202c00c90340c2510102c1c01d26004010030303540030074264100c42a501c1010113461400c4440e441d031001103070041310071080d0707150142425101e40005000002c04080104800c6032024081030000c0809480305140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 647750620 1250 647749370 647749393
    0x1014030103050c0901091a12010b120a02090112080a0e03030f0a0305040b010b030c1b0a0f1a0601210f090c060c03110111070b040f0f0b01090e1c050f0f030a061502 72
    0x7c05d0b80780010b85445151740401c0f5043c3c003038082d8844000c0510162480d01d80c9202c2840c01c554601c3c03041c20880c041d00b84a80000f07a4090350241c0c05400c1c1d9403010034a4905940795804a0b0404002d01c415585800100030010351507900c08020302c0c0c05403003030701c01044da4070303103030038008583c00050b0711000801d503040042040d442c08081c2143c4003420550100060185c81301c124510740252403100520240601040c4400e0244000000c18448030750314000300145d41c0d500c01124203100800c0d84804840740516013144140c0150000120240e030600d0024599640b41c41e0b24082d00d000b54080408108026141c0c0241079210480325441d0b40050020f0109002c411804462803040580c054042010b60b0045802c20407412070025066401041da03c0510304242001196070f0000c0c0310f0344c0c1c03e0501d0551003901000b00403d254041403018078004403881c505040a6405500000340300c43c0c000d104204901d010010a40503500401114000184050030442401c903200821410f40c6c040d5480580c013040e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 647751870 1250 647750620 647750651
    0x108220b1f0b04150507140102040e150109120807060f0609180209010e041407062a0f080913050f09010e120306150906180307060309030e1014030103050c090109 71
    0x207003260b52080c1000c299480c01d003000c51300c50017011b9006000722551082d6036402c0b9015000340003170302c0319041032000c540c490094101d00040c0b05121103020886255040018528004102d10894064800d5a00c1c2801d295510411989002850801c203503444406010a8070648a16050f0007008032031003024a605800040300c80105100c2c0c039403201c4010700090704200c4900c0e09126901041c01c12248503139104c3c0c501a000d0000425210180b4881c40e02d0280005d5803000100d540360b8000707440680d140c2d0240c0382c03501d255000344c9505400a414580e0000700d111144140c0340328803060000c03849241080c0e002a4255143e9001030035a83d400304c0400017074011083c040b40c2e002401110b0940c2004192a4011800d01807a51000d501c03410128100008411000340300011400032401d0380d50940d1075010a408544d000c0c44041d00140c0600307a000568201405a0500c180107414420000028402a00003660003600100e61980100006480604051751107902401c080c16017404030030a41c05248 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 647753120 1250 647751870 647751877
    0x20f0705032a040b0a030303050109052203030b0102031b0a1e2d141b06030c1614010c0c03110d0f054b0304110108220b1f0b 55
    0x8651801c0e0311081c1441c0d0f840d940803000031603000c0d014280d195520b04015005100901c24000e0807400d000c001051080c86800200f4500c280038120700b0040d0749500c080300244003002c10681548000c1181503500100031560404038004400242410801c1e0b1500700700c0c450108881d8500004102c4813540000d816824104c0e48113401d02c0d041103101d0943d83c0c5c4a02102503403001070003039614941e04a404100c041903180302400303011400340c11001c03502d091108900c0304a840b400c2412091041c0145240d43c07108407980103006161107580c14903c00c920f2401c40e1144024040891541a5003904040d0030103e1308100022120240000714941035010303240c90001c8111500b00940020800c1d020000c118402210b411034820450141181d4001c0114042146d8114240500400321106050044804582c800c4da40903c0c1042c01400d01c8005641d0b00202403c62a2400751003900038980c915003250180069004116044460924816400100c0384641c694140b00115400c00d200c0c010005003103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 647754370 1250 647753120 647753173
    0x20c10110a080705070218090f0c010f1803021203120f010501020a1106070c27020310050904080c15160c05060408130f080d031b140d02040312020f070503 68
    0x1001240d40f0a281101d06100d0f200009601626a4101c10b0000582c07100662047c0714002c02c55110a1640090941c0c0e0300a0b00c1c2403d001801d40c5040070b1f50503215060390b94440034020340f00071a081d100e40c00180031041d0700444600c0c943c4045000b100e6083c1314540c00350490100088031b02c13554100f100007919900a040c0281c116800b06904202580f2260120380d1529085101d14040c1c40c1c5400b10518181000c90480005c0c101011440782454030380d01c202c9000d2002842c056032114903000500a04078002042a1050802400005800c40c4144444120200310024540c0311345132180303034103011341c09981c103a00801641d403502c038000900c001072251304141c00041c80e6407038554000e481c684400ca103811809410b0240780c000a002c010000300b90f2200b94641c0c400b80715075001c1640602800310140d001301c0005e10b2161a070310702c00c0c205034010100c40c90301c50000761a0a4403919121a41b407000c505000041e4410320300007003500d10911140018050480c0a01280750102c404054620442d004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 647755620 1250 647754370 647754377
    0xd1a130b060d021804210302270d0c08010203060a09060305030a1103160311070e2217040b0c0d02061b0c0120070b060f01050d050601090513020c10110a 67
    0x811003c1d590b48030007103400f40490b210800000e10702880d00a05001d805941c08000364043c042480c1c00318024020b40700b0f0003060401c90410068100032601103807108645c40358000708501d1042d40402d81c54244c0d0710140a1038000503035241488028071003000e000ea480404003515156003400002e501200725070b62520286021000528850021410351040032000729802002010700c2007015013050b104039021240c5401d0b03e800d0340d620407914002800448080325408181d1040424118001000c2c00c84140100c44443c0b00c1d8203560414035180e0b2007074010110b00d00011a08100c49002004210004c0a00b403000e13000604092000040050f030010340c81020950106400c95a41c80c2513001c660401006920a802881500c91501c1c20303a10100d0251a45071046000903039038100980710414105041c0c0d0380a180c40c4d00d100402004141c0509501e0411929440c0000c00b81c1e216032550002c038103130560046c4c1e2002084601840c00d4101222480c040d403e242d41740c0010f042003000e0b200180110708 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 647756870 1250 647755620 647755639
    0x8131d0907120b151c03031b0801050603070203070506010b04140109080309012a03030c17150907021903090810151205030d0c05040504050f1b0a0507020d1a130b06 72
    0x103c801c84002100c444864004540d404107055044100c01031744825406a28200184400909010b940010112400000c1246000100006c3c00d10000a55001c0080c2c415281805019501d990030031031b00380e104004411011070103220f202551107001c010b00c082420440031062401074025103a000790707050f440c14017804c9040f04440005a51890f01c0c0c0241c140140200d144c190304e8050000d102d103e801d00000340e40003010a1601c00083d14031402404042030200019800c90204101d900c0014002c0701103020b03100400c003090318601142d180701e521030340342c0044190a245480e854842d1100d040f10205003426814804d002e9030035012010f131450350b590340307111100c0c0c4e0400920794800d00c148006203a14021564404070b5000020380103442d030448050007c3c0d100d0f4061900c0109040c1c401c041c41c0c6086a410028540381e400040c03c001c060b03401d08c076041205540015045c200c01c03c00540d200c05032002a45d0300f1903025290b06078094600c1c4205085180079807114502481c00400007402040c210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 647758120 1250 647756870 647756881
    0xc030f2924090406090309080a082b0504030e01030c210e0f0316121e1d12150601020712030c03030618020a0801061103120408131d0907120b 62
    0x40d0305038000620090600803043c10700389800310080403104800d80014085c00408900c1e0f12011910780011034100091504086503010080010030782907803000c02d00012012513061a00060041c248900e0190304c3d9101903964100014041c0c0340c034591000704000c200070b020703100c890400b40300d1801801c500000042d05a13440c0801c47c50000803050b4180c65100116280703911129888403200d2840c4a0110068455070f40a0306484000007030034850680d4407090b851400a9111310305540c808400f00c0e042070f44a40032a400b003881980c070314142000310341000f0301c0c2c3c0c000b41281d4400e15800040a2005014461a20900314030b40e024401004080059040300402407511a401a00c042d0056041c1904030b00909500e0500940c80a580d0302c0109604100008a960180b4004888a0000c0000e1460007079000c103008030010000303000301c40c0800181700400045d0018043c1030003400e44003920072142c0507142110913004030014885442070340004c00c240729400f44440e50300013003070303003e00000e800c3d440d030303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 647759370 1250 647758120 647758171
    0x301210203281e0b0103033209030c1f0f03060b0d02120f04150c12020f03010509100803040902031305011a100903020a0b070f0c030f29 60
    0x11141e5482e00e5549100c020400c0244101030b11006441a810f42058111102c80421400d210000c0500b95002c05401080800e0088481c92844c0490809154000103408843d00c21010b01200c41d04070070f40042a000010308040101d48170981c0111051151413032141035042c880c0c841c45c26060100b1002206000b4402e0203038000c54060480601c1054036032144480550094000a501c001800581404544003014590142d4011a0040072201e802c4103164198006444808103110401c040304010b045101c80620180011407540002e107590703545054104031000c00007a000e0303044d030040c100b4100a1054000216000c0320241840540c803550360384048981c0d0725070780d9402340155080c40c82d03040c0038002000f80071840c01405c40e02030401c418840002c84020f0010b00000390080c1c01c000c4144480000d203000380251a2060b401c1d110074541903511314000b1202a40204c40d400421245201003014182c19044140035038800300e21121401d00c6a10a1074902500b41040860413603030b601c401100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 647760620 1250 647759370 647759383
    0x6030601032c032a07030303020a09030b0f0a0b03030a1e09030206030f040b10050a0317160b06010e01050a0e12160b090a080d0f03020a0306120b09060c0301210203 72
    0x44840c2c80310102820720005940707035030110356031840c40d503605083c1041e0040810360b06644d021100d40200907035030466901360000d602200600e424440c00c84800000a400762012a02c03850b06084180c00c00c2c200412034206881801e001e0501c203404c2400b41a00055100940c102c00c8001400c43e5000c0781c02d882410b03a80c0d0515508043d410420001c100030941c0000410140a180b085e03082c10887e41e22100320101142040c0140b5a01252080081022944500440c121400e88a00c1e0500e04a0f03c0800b0100d0081c2442c02180c1c508011400c02c0304560700b2404039041c02d082070a00901d00541010002c00c0c1c1c3c1039000030300344130305084101504400c03010400080c0303828a240030328180c9515103e4404041e08800000ca114010750305002c6401c41c408640030100410130340310042660030040050300a90018410300c020140c1c5d07418002103039030084000100380d90050004d103c090401c0301d6218240000100400003541d0304100420600907070202e0403050000114084841c3c1e015880000e00303022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 647761870 1250 647760620 647760671
    0x3606090b0103060b010807030c02070302060f040b270103060f12050c040e070305240c0d0f020f0904140903090f0111010c0816021b040f18052a0603060103 68
    0x280c004004020046240e10a4251440c00d8076000060b80c0c0e0900300320242c17a0030080000050b00000420001402d000025000e0307500d226074414200f0762655600603554000e903000002090110003000c1c40041c00c1c40c103000c00148280b0f0705001c42410b1110382007521044d80b1401c00c1c80c16001030a0021f000f01440381b82034401c001482840760800e0740700f1282d50b980c26408195001c5c003409064511041c00f00500300071000214402141d503070341c0c0520003695504251807000340745131500030440280036944018141340442828040d01c4050b564140b00460300c400c611061144548814040345440c004180d60750386c8001c03110b07140110081001220801f07091b0445020b075608202ea20072540707401203c0144601681c40348610b035400c0000040b070356035419042e6024440c001d541c1c0d1407584e0a003508689d88070682100041501c0048013149485590303d030074255015000b110090010340380c00e40c141c280c500982002000340b2400c0500040300c600c80a42494140b41d40e9506e03550840454218120300700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 647763120 1250 647761870 647761883
    0x10b03010f0204050f0d050d0c1e0506160201020a0c0212010b18060405090a0803010509060607051c08060d031202031e09010501030b07050a0f0c080c030d020904360609 74
    0x102240035000c06074103c3e00a00b8032610490310900254100608008021034101006141822046409882000b02e25a00369904201e80c11341a00c1612002d048060f568030a070000d00c1c8500d01200504124809043d04508690040101889556010521461a640403190001c4480b56003c2503801001c0f010785c0b80d0340204007820000c60800403440e0003482014156014081541c07002d0080e91115a00030008040010a00042c401414406041a80305001a00086c9000c0e19510340500e000c54508481ea8096610700e03e41600f107512660305500400709a80f01500c10070103540c083c0082d5401c80b002040e036940840000c0c2c090801c8942c3d68120110000f0403003150400001c2c45003e0310090106450580141d00810010341c442c100301d40c48000c11303685032030320203003100000c8480000c0b094043e610800140b108070848002400180700110b00b5802c01079507051600b041c8000d6a4840c100c000240d800b03880010302103c1076425003251003c9003010382014004924068000b00b15641015010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 647764370 1250 647763120 647763131
    0xf0910090303060807050f06071509060f0207022806440105090f04240c030614030102030106140a2a03170412050f0912030406090b0405090612010b0301 67
    0x80c540c05074400d005482c422000d840000751940d0501c07080d1032601b00d0640d00503d0800c09c0c1d0303000c54000b02c01040c0a50400502241803ca19103429003074500316514003a005500041d150114900b88201d18480d075540e5014000000c6000c50300409003209102d2982800a50844000e4050054800d0040342601244150a400d10040390941109200181d01107103041c03400040340c2c07441c0c0890024814000b000300e180e295511681c91200303509248507480003002ca00030900d010301c40342d8007035242001c0c00395400181040c9400c04642c082080340c1c04981c0240d10410040c80150340c07002c807400d02c02c01c030031081c0703513031242441d50071188640240c1d0b2010308020000020010354940340000e40800e40669034016401341650400c81d03c0f01c0c41550000c0c408030003c500640d00d1030180019003821007c00031404d04010010f804280500301043d848811138100190902c016500200701d940603100042105080604060100d0b04a080c060180c901c01c001c3c02c101100d41040c250030003040c0392005402841f1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 647765620 1250 647764370 647764373
    0x9060615050a0908030306030d210e160905040809040b1507030f11030c06061c05070e01091103160516061506030b04140c2d0703031407080f091009 65
    0x3090b088540071800040111000080c01d00001080e02e01425004010345105130268a0951b00d0540310001440604445110400c0c0748546120f62340260302c080c00901018504418044000441368106542440c41d09050202142d442010744440e0a019280010358154904c00104201c0050b05035001d0650002030a00c100b581c0100d081c1c0c010314461302e81c810724180c401c150907100d00402010031880d511407800606146800391100380340c644060018582800c81e07407500c0c1d08220300c5821803840420502d004120045151155030440b1621050817421030078200c4800992a00c165001c8080103404104100c001003c0100314a5855000c3e0080107a180381c41c40681030065107110765030100b440c0c00c001d4986403d0500814a60781d1080342c1d201c916603035101c108285070b04042007440c84c5015210840e41c0700085040344030303250701d850388000d0340742d680703034540241a6040e101c100b07040344208200307100303070250011012500300031448842c1c0003030703900c00d40c0262410324068007001c0c1d8a0b040000040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 647766870 1250 647765620 647765627
    0xf11010c020d0f020103060b0702100e150c280b010b030603030909070c1205031509041b0815060a1409090a06110702090f070c031d04050c0301261009060615 69
    0xf40aa8800e80781070017801d07520300f0b040801e4059503001030741046080c842c40960300d01c108482422080007c0242c40042d0741005070034039942050a81048036800b18845880c0300d500e1250744942c4149201103a03040340103e5445002d55074041c460b544011101001284290387d0910a032040464003a00b211224a0a407500074000500c15800740c42c5004600316540059103c0d01c00ca81c0b141c54800300e4601d0200004e400d2108180e40144255801d00f1100d8618440080c54206100101302071001403051a035100a007201d508400ba1000d4070806101c0f0081007550307003100c0700c2452030034101e802c0322113540c80309a0203041c0100c801005000c0351420354425034400410018005040c001d450b81d18855450900080007148140c031900041101020680006441003980c0800c1106924800780e01664500c046401d49a05680985c0c6200000c001030110708494030b00c03191065403040700070a954401440481e00d0f2210100810442ca0b2608400e81c01d018070740e0001c80081607640100c80c400c1c0007200004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 647768120 1250 647766870 647766893
    0xe0613031a041a0601050921030a020d0906021b040c180f061409031b030a0c180b0409020a09020c07030206030f06011b03021015090216020301050c070f11010c020d 72
    0x1228001c200601a00a01c01a0f801c02442504180c50351307490f00c8445820130005452407480d1162103c50705802c500c11050600c081c1000310042e40003071107d600d04140203811a9a60380040d001c43d0712081c000a1444410f40007200484000e442c005641d0302c03140d204075407028a0007885940b121000000090f240090150041103d015503200e4404024042c10403410780f140e04a4181e01d5400070b02640002140d500c02c40615050041c216541c04100c2d0791281207020f040d41c0a55030120300d43c10001452a014090402d24001c1100c00308803030200d650000380d860020703000d0352aa0540c08030784e0082da94010090303403000e550000c00c500d0700c03072030000c500d0308188504441c4940011482204450381480700103950391070702d078190050404000c0989511000340610076102c24000307140345001401020901c010491341d20302042801038540e82e40107060942d0300151070180707005000c200c10004206c0c2610035440302c542c000d035060700c40718980c401260808090200a54002c2e441d00c0c2c0b40c01046000e484c507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 647769370 1250 647768120 647768123
    0x17030a1b0c020405071403180c130c08070c0302060f07090807080105190606020a080d0609140a1a280503060f040b09031c05040201090f090c0905030d0e0613031a04 72
    0x1440384da900c10038121040b0100501401040c0710034408030f00001e9035144210140300c03000007220301c0c41414a00041c015001801240185980c500c20b041d507882d4000c101690001380341c1800c251410007a80c000f942d50100600c6980c5940c070003c040349903a0f1252044d40c004054a000f00c5074000d464401c618021f04c0150303155000c078002d550000c1c00368584c07030084c18112083c540182c8240c600d40c0d201c144a0360300114040c00e0150303540700c0100b80c2010901c181700424081a1122000d490310a5002084032600d5181015115000109207943c1d03481086108001541501c483c0d42c426940c1c0041c443e02d50b8640001d82c0c1401206c0410883d648032920243c070880c00b1b005803604c0b075220f440d110b03512841002e210783c074000b00c0919200b140c0c0130300760803540d0040e1040c580805c00c0d55452180c0d03168500160805140c85480b0000302518940c051015005004105c015200059209901814450041082c1c81c001e02c000f0a84200d441c0859846c07000840d040802c0c5498010740810740b074034a1108480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 647770620 1250 647769370 647769379
    0x21501081005180d081302030604121b12140403170715061a180d032601080307141002070305070c140a0302090c0c030c0114010e0417030a1b0c02 64
    0x18044018100d8004206804001030204c150b9408400c441c00c4030014208403020380031042550060701c081120501c03d034004c81546e0300610415030300820400c480b1081c0008440c2c0082c034640032075040c0d5a0300008a000e070501240c011100c0e40860950f00481e440688020b0784800c5503209421490700610019108681c0140003450300005941210b120b4040d6001d031801e107680c5098198849001056484142a851120b50301480001140c1001031101100003c51011420250b0082c07d00000701205903001200341c1503050002076a0b0364012010060142c0310b96800c1e0800c0800f00340441001c11241003402c0d9030301e180c2801c014000b0703408881304490f20328105030001485002081d40c40d5031148000c14601c4440d10f5502003007612440138001c020142c904002214200b00200003c11910f40c1d600004205581000f07504000070b081640300488000862040200081c1507804640c404603034001c3d110b40340e4441e10b07062001404044200c0c081c288a1400d100b000d582c10000c4104400d00c03c6a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 647771870 1250 647770620 647770631
    0x1110304230307080301050d0204020d0f061a070f0b04080405030d08010e0703290118121103030c0a06090c0e0a0e010e120429030c0301060f080403050a030504030215010810 76
    0x41241d5aa07205140018100010601c014080c4c1e25080b90003945a900051000d410102e1080c1c51504039100c04149180859a8603010030910b69420b41c40c5001d0844032040600704507440c2c4840c03c2503204c40c000109010034100018080001c810250303005480b0241c126841150f032004080c0049c0c1e4203002c5e0080e808030701000a50342d540700c0d00500e840f1000400660241100a000d640c400400c2a000c060612101440015100c2d1180e22101e000781062641e503603c0c40e1042c117180c00141c0c9056100b07030083d0000c00c01044058800151003030300e56070203c2d00280d03901d002d003001c0d508480c40740c03c01000502600148400078040782c000a5001c1c0280e0020060f100d003d03d01c035603950701040010750129100303100804c15015101005081801959540d80c1c910701e042d2140c0790607a0003101c0c0c0c0d084100022005005007917100d15802802803050610090798200394070081c165000c1c0039414002c144c1c407080041c007014824004980c2c800d242c070344141700c0355854200d1aa150040c20a10b114850b1a05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 647773120 1250 647771870 647771933
    0x12030207081005040c0b07020d060203101a091810030204020d051602010b010f051806040305010e0f0d05030402130b090906061512010608070207031403190e130e01110304 75
    0xf0b11549002e107038004c0740d8400d02854083c5812864106203002d80c2d00c41d04503007840c07010840c640000c40c41a698a07005002d02c5003842c1b014501c184081410f0701c41c10320144030000c95038039020a50304c003448a132200100d107603078ac9400d1890016041d0300025003140c0003158040f0810916082240110031003444070094404d4030900b2422143c5680c041c5000130040c140c00c3c0c0310240030b07500404201607041100b1349002d420717902140702507011b0b600403556a07550380c02c4812060b42c2805044420f40d8603030040e02e1684100303036004145000107003011340304043c01c050400303503015181e024030f02c88840640000441e150029005881d400e0440c2c00b0303401120b5010081071050032710700848518092002c1751102690030f100040750007501c014512429449044404000f0402003060001883e04004c000c507036401800b000355620005007a452014013110242d8580c681d9191100070512805030301000643c1c080410003e030241c16080155029000c00100b4003051050400320300600610b116000a04503091 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 647774370 1250 647773120 647773153
    0x26070308060303090a1e081203010510080106020c010318051b0a090b01051206010e1c1109071b081c02040905060904020303030a0902030a12120501051012020906041203020708 77
    0x1100c0304180e2040c0340703250034802c42d03607245000c4410b80800c801b0380c141a6120040c480c680115065036080b0302001000411051034101004401d0400610f441086035142c410080c0d51001e450715002d05140d02c3d1824004c0130391314181003071441d42c1c00ca000c41f440b29090314410f0b0903032205200b41c0340c02046200f0012418405500070b08000650694a603032170700c0c0540000e100b01c03900192040d41000070b441e0741820b1560300c1422200114041c00258403800406140102c440d0051113280c03401010980200160b203500300b105500c241b152615181020070b07d91601c4841442800507240740c00001003a40544d011030b9a0203041680c044180400998655008109461104890095041c0d004000244401059800034002c4904c054102d0300d10500315035815203000d07601c1800c9400150603400b142001c1c003080c0030b040c1c0104000d50303030341c1140d10800d040113201d0000090310200c250780014001c0c00c0ba031264811103006015100e0300402045441c60000c3d114003080c49a22141c1c820200c060045206 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 647775620 1250 647774370 647774377
    0x203131401020f0c011403061503010312030606021603032006090709110310170c15071e200d02030304080106030201180b0414031516110a05030f0726070308060303 72
    0x40c16152034450b540302c06e0300f150080d0320003030007542c018000941030890040c3d450301071343c0614480c00300300c1005081c6200c028119003442e401344045611944402000702c100740343c900e0640c1d03094504105111000d10700407045d0b2025400200b402d126010410800280200b160710554619540034401c0b0702880e00001c00e24003064400b080319400c081070801c10304200c2200040c0704d074841005e40c0e05003158900000c07000780c41040300c080207903400100e620800140c1c1c00b45041200b074421083e044400d00b91030340d100c010390a0084400000207410124007503544e100800b24504e60041c1165950345d11400958003030140c1c6e02c412408145e04106032140301c4840c0300600705a0b101c040956003003501d03101300c00181c2e070302c41b4451581501800ea40320006039000c4120502c1081801103003140325020190042040700c44860084944e007010f540170000400200448440003d10200551606060b08201d492040d00500c6090200480e0402d0580e00341d0b45d0b40a00405400307074580c8034003a502ca0702859120311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 647776870 1250 647775620 647775643
    0x60108061f0503060a350f010501030f0b07110a060f090c08160f03170f21090f0c0105070b18030a030506040f4a0606120708120a0203131401020f 64
    0x80b10107001c20310046c0300c00e03c00d00a0036010211003a07000f5000609084600a8005841f03101039075182c04140b080052034143c22041d5850069072007181c01904a17113440205030004c1c061500c81c2c075041c807406196004144c0c0203420a030300c3ca42107543e402090342d4941c1c4006501c005000c0192001030245441e0030300303504aa4014100300c10500741d5800c48041d95200d444161510042805a88481e810405000a01c2041449090300c1c46c10701489141c581090704100007101d50100c3c0700900241d80c02001e0300d5155910003007008441d01c0342124040b1101c00410341c01954400400d00181095050300302034080d550a903400c00c1325180c3c00306040e06403690b03c0104c0c040f0000c44554940364000c1c1c403403840d0740c040845120301c0d280031014500f1005001152a80e5180e0f92110b010302a25290220195000101e0b010060031100e03c0c0c0b00304903440b00c0300d0159090f903004000c600a001c4130f00910886e00c070748400040401d81c85844039120340003440e44d50352460040c032030789000b0701440100058540400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 647778120 1250 647776870 647776919
    0x908040b0f0d0929010b070f0611030f070e030703030807050a0e03030c160e1512011113031a01140607080706051e1e060108061f0503060a 61
    0x260a0060a032240d030300052034021200030411031001400501d03c41c005030075101d001c154600003040180400d4150003801403c0c442000c1000400c1415001e00481d8040b5520811480041c001c905000000300b000c0d40120b00c0c0c882001040040c017603404030071680702d450641c03034003604c03040c100051594031021400010080b864607404079082d5805035014007080a00c2d482c0c4901070703440031804607055812440180010303601a40d591000003600e40307128805008c2210302041d00e0b103004c00c00c104c2c00b001424160360003000c1c41340000740254800e400481318429034000c00f07582c4019071412a441e25003207100560f40d4100301d4180954034006441c070107048a0445180241242e06001000042e50044c10708a0b25860104142d03030000b081405240d21509501c46c04035044410046030200a090061089003110444c204c1004c181542140840c3c00c03074000e1a08543c0c2d0f58520b00461101340282424408400700c401c0545100c0d40d0043c0114420003064411004030ba90792008003c0314010748030f8103d200c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 647779370 1250 647778120 647778127
    0x10501090509070b0a0f032a090807090e0a1101142b020310051009050918070b04061d040b03010e07031101092403140703090201022b080406060803040905060306010602010908 77
    0x2d17511a411044422076194080c0e690750042050308a1190450ba96503230100b00c548400308014003051040d40000c1426213414449003006c4e0b0300032500c2e48000700006043c0c60b48100700d003899911601c1400b810340d000711038890341c2e11414034000010703140010558203041c00354050170074030b42e4250090320302a03a4000b0901e0b0305981820200241a400c40304010b0400410310720008855844880042c01290070718000c05906d501075100e103080c417085e0380180d030084404010422030142d22040b178514201c1900c4440c44070007412000100501031040140c0d42c150f007403e81c1d0801c1d442c40410340100300c900c2040c442d56404542401518030303803110b200340e103446162049044584006080c1405e0309035000d00d00080c0381416071014244040041d1000c0c400269903215900c21942c040007045003220318818800d2002e0150103083c5202041c1c0318400c0c1c1004910008203003081025002000035041c0101502c2d00c554440f1120700042600301e81d058400c0c4a031800000303001c0c1c0103100d140e90702d582013030400b440c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 647780620 1250 647779370 647779397
    0x510030f0f021c06020c070501050a0503160201110703080613060506040501081312020609070f0b030114010c081908010902040303090308071104110a02010c210b010c0203010501090509070b0a 84
    0x240070701400e981000b80b01c035401e014912108001046113105042c0180c440d0191700d2403070301d0a256508007a0500c00c04100361071046422a00781c981c05044940b024281c2591071034224007419484070250030244002c00c102d01007540007407059104400c207452014400c40981021020303076000c1d2281c1500503508001c14012075208400c0d682e03104081c0d161880b0709008559542c00d25065085040005030446001d200d41480b050110100400c4955507100c1c1007418946040e07400e200602c41c061592901c1e0601c4800b81c6d0144034842d01c580e820451458907000094141c0050314400180000010b04100005c50300c4c03074061085e1001d607030301503445005407400d503602c0400b258827444040e00c0709142200241500d5035940140255240c0d801c1a440d15000c10702e60207400e6410319002c1c0c400303020342c1d070b6000e42d06130010135884010102c00300c034041400844840146c40c100076449000c0d4055080000124440e8175a81061303004105900495280c0350303950502c00d03002e00034001d640d000139521500024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 647781870 1250 647780620 647780633
    0x1403060c041205011107120908120a0f0e0901090501050a0902180105031806010902070b09210a05070602040b0a02120a080f040611071a010609080c0603070e0a0314010510030f 77
    0x2090748203c1c0000381c12040000541559046003900315001c80e9220500c1c0526684501041d00502000000b04011019149429424040d011009003000040d014203410325104c0c0d03604510030703240600083c2165840d0002d607005020240980350017a504070800050308852403080702c2c0101030203100000880785400044800740d2000c0c10117203450a0704580d038207414800f40202e80c000e100ca400c0c0180c0e141d1151034450050303900103103201d01e43e07000242c0399a29440c58075070700701c6500c0c1034002055a0303180d41c1100360341c0740c000c080c0042e103507510215000c40e500ca2400c0041c046021035400b22030708484900e0001046201e0103800e10000f500340804542c401d98120760070758100348503000104455203621490030068001c1d110a0743d140d421064003004c5241f40459041c058086460801040d506211400d680c030100800d0403030281c21b00100054025110b41800c101e60200200b00300b800c01e5803801d01d68502e20703500c0d241c0c83c0c0d103520380b80c0810704e82d00c20b40e078485003106e91200c14400d00059645941 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 647783120 1250 647781870 647781899
    0xf060a29190302030406110309210c0a0309031e05460b0a06080c0105130801060618090c09060e01140f120a0b090f2e1403060c04 57
    0x400010340c203008203098000e01d941c0681c04071015580058880c502410628140c554580490321280c01c20014480f030740344003060410034401c15102c3d07002402c00300410011540304401a2141c1400341b18545400c040e07000d081030b0204d900402039402510b000751032510110183c000014a01d500140360b031880c2c6a0070441444140c101c030602c42404100319540d014400368a0345800400b06108800d1600700f06010034001e40200c140c100400100382403035903065844003e8090581070000100780070b403030001601010000b41000c0710090220039921500076140240c3c0b11881e4201c08055100800c0780400ba115511010945030303280c005c45498440242c5a150040141a042203000000511120201c0d00200450520b8400703080d81c0f500803014040702c034540503108000c643e050440b0301d0a2a83e40005041c0c01550011042c41c0035120802d0b0014030b58010144441482d03c6000107200c10381d064420481180d01e08042070160414060030180c41d2030303080b036403e61800028401480302c2403800100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 647784370 1250 647783120 647783189
    0xe1b0313080c0d0503090d020c01050301051309060905010605091501090e07020f010509070501180e04080309030408100f0b0910030b150607080a020106150914011202120f060a 77
    0x680b0318007551042d070b02e03040010f5a200100414000024002080010070101d00914010f10103054060301c01c0000800520040c81114031640c80c43c5007100320a59903038468803030789521103801c001ea050289401800307401c035032250a1040c00140001801240d80300c2c008060340505946541e145802d1402400100b44040d04c858218807030b00c800c0b041042800d1082d10301607442d603001002102e151500050030540581d500c2e00c402e040d41041004130310310910b102c0e03800c180d00c007060b180c49035140001203186000d250301641091103286c0780380140200381c1c1c0c4603c00105030054103124040c508000e0204103002500c0304119012081420004510010b19040d0081400c400c0741a4949032600015101e40200c0c0301903400400008a001c03a0b55024444e91000b4440d840c81d440c4505800303440078000946a1040310800b016200388441903030f00c61042c1c1c51104072101e40c11500c4112a2040d00e030144000c9405540f00c50300038002c200340c1e00d01107103280b044410303401c1c1d1441c49801100c4071b041183c000b48003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 647785620 1250 647784370 647784383
    0xe01140a08070c0b090109152d0b061207120c02061503010f090c08060a11041e0b030a05150a080d030b040e0304171002030415020702031f060e1b0313 66
    0x1a5030700044c980c0050714000d003840800400d05c0d2805090254022002c909603045a600d40204101060010f580c14030f1a44082d628400104840c40c610402608161078034540c0000f001404007190a501e01c04103000740d000d0354982c444100340c0101481120940b10012300541e02c60400903080105156003401540c40107000420800011130301e55003030b01c2990400325026140210140003c2d04200507659204900d010103200c40b01c059a040c020f40d114501401c0e040301c00068120b14461810080310000b03202034031240340e803468800e03035090042c842031700c02504960f4410f1306c201c1507161401e102d4042e1940d64010b4449085c10007805e5005028aa0000d50055107600603c44200c400340041c0c0000e00a04000174001c01c1d108000c01c1c1021075600180009034810300a0002142c03044614800c058610034006989032100e00000f840c00c1c0c3c0c66114030440844044403007600c0011500038401300d481140c041c5100d5110840405040d204244001c0c0c041d400a000151103040107480d40c0004034000d80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 647786870 1250 647785620 647785637
    0x314030402011e0c06240b07030309052b030605030706110114090604030810060c031103120406020415030b0607020607020a0e07031a030c031509030c0a120e01140a0807 74
    0x1140d684075100f0280100810503044111081c00024045c0600d84020319030f1900007503d032141001c4952002d80580c0313803030140102c2c4030400c060103607100074a040d0300f11044071040e500c401c102034400c400c160f603400303034079103c96038101c881c00d00900481068800017006420001e05041d01166481d81c50003000403203640741e541c161101182e0b400320901031400080503001514140c1030284c0290790140c010104150401c008010b07869100c01000e019603494682001c03600e403020801d070701e103005040c03c1c4203c1c958800140320810403240d00034402c903030501d000c072902005010401d80440303807000c9a01e41c10400030030804005207400c0c0002c01603644018442c1d019251108608242a51b0440d04180413030b03034900655001c0c0100d10f10480007000102c0080001c1001080865190b919000c3c0c91400701c45032a0208000c0542070054402c41200c28040b034a9010480c03c00200e0380c803450b03403408003190301c0b09000c481a501ca40c000312101805000e0840c540b8104003002c4403c501d00405900c104035981 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 647788120 1250 647786870 647786897
    0xa0506070f03140a0207050609180f01090f0c05180a030c090213170c092805040c061407030f020a0f0605040b01050f03190c08010608030a02060702010207031403040201 74
    0x244054010140901e5518555180600e40505151164492451a03507000e006168800b50b0004800d8280d401c2923480d25121960900480d03080e544c90813503c0c00c844845010040811110348030305041320041e06044c0b0000318038407441001c03980410080400114200035950204c42440100c3c3c80340340d0060105a00d0316546d0b1503200044145821071500c0540000f0340c640d03304034041c04a005046452902c05401c8100d100080d502c52090784814001c1c204040042e81882d480b049003005040749000022010702421192001001c00321411110541001c00119250740305405841021502c07424141c5030610640701035488541c0110756908500c1025800c01c0010f004441741000f843c480c07900031415051514010001c0141600228001d260007240405c0554002401c002500c44400c146090690a410130300c503183d00c0c43d04131821640c20310301c001030a40b00000007055200c4c0340c0c3d0301b55155900c9041c4124203170710802c0340203000141c0c506c1c403a02096100e0002590440d10504100c801c403c202c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 647789370 1250 647788120 647788129
    0x2315100608132301060906140409020a05060a03090209100e19020c1006090506040c0e0415051e090c16030f03020c01060608070207050a120b1305100b130212070e0a05 73
    0x442d40402c03409030030f880d0030f100342c81400d0062402606607085d041c0481030a11926030000c3c8200503900d403055441d500b0880c155110380e500d01c00a0040501403d54a02003203a0240180c140a10f00720b0041c2c12140c00141d50000c0000c810003034a13146a00c0c4a0319444100000c2c3c0c1e0010690001d241c8141e003085056000032003002005c1c16800e900030045821882c10580c08100ca200902e903034090703030501c0c8400d82d0302a8071a04144841d00c08070b9000400c0d42c0e045c10310801100c0c80d80c20154015007200007000e1407501d80e28072501003220071540c580e165500c03140281c40e107001c1c1d0000707041c07418403928030321001a002700440d100c141100d00d4014180324880400509496081d40040041940e0005102d00d01d541442020041c02041d590003c0751498080c00340e0440680440140c2101d441c0300224102c010306c64800b0603448e030400100ca00c24161418414000c1034442045482120143c117040b1002005001b87d400302072045a9440c040d669a078000d68010100c3d44140c0c0d0310454900340030420783d48 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 647790620 1250 647789370 647789393
    0xa020c0f070323030a0207180609050c07050f030406080a020702011103070b090f0c01091e0e0c0a0201051501020c121f060504150f120609231510060813 67
    0x2148928225480403020f0340040d642c2501200640c0c02c10020b0319000c540002d03a0404803801c0c0350040c5180c0140e030201e40002c10303e94102a40320717402c24043c400360340200070161140c40d004005560450a40c031080700d075648030710300c15036011510803400a401d0721070550142940a0040c14041580d5003485146825680501003c8810000810034000c00900411070001c0c030794030003c020303c08841c1040002c0d01c00c0c0c1043c800c041c65400c840d40c0c005080d10380c50400c0d000410700d420030518581400310200e5000c1d080110742c6001907107440300180f030391049040152105441038001d002440705503421320110003a90240e0110720b01c200d182c0340400d01c42c00110300028034040700d800203100c1e0a00040200351802c1c5142040c3e421043c50b000e10261141d00c1b2004210750403180d81c1c1613050080d10300040517282e400000b821001400041d07405c1800a00403280e1406000002c3e2040d4031540c124221346810150b40405652640410910989004100f42500700d0290f201e400381c5c0c0090781d66890950310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 647791870 1250 647790620 647790623
    0x906020703022a150d0605040903020d020c04051506090a180b030c0306090d050c07120c080c041a040b0316031a0a090521070b04050606190e0a020c0f0703 68
    0xa01066003092800041c1c00740c0d0031510041e000f420b4003029100c002070b64a0701c007a18410010440014407800c0c03000c442c0d00180091201030002c0c00216110705004c0c1d00c424450300080054043c0000c0f04603d4642481358501c502031b5004a41a01c1e41d1003020b03c00d15801004002d40c02203502d49000c14843c0c0c007210340310061252a40301145c00341207213007410f061220040c0c0702d0740030b98020024400880e00105000301d0101c07a521b041038481d150720450740d107004072690010fa46280c0512035103084c0440030418005990200d8103e81648a1070000c0c041191000310b8080c00c0b00002c810290705a14107604082e4009400408984100c90000e07030b2160b43c021964170458603140080451070a18540d540c80d80e5003c48031040030012021680c075a00c2d200c86545a61500440212642d001040000d20540f04031036000301c00c0c0720051400d86821560b40d40159801485011804000301612070480320a03c1600c2161206803059140d54901b58040e40080c94003030700e20f008100486241110070031081d8005e6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 647793120 1250 647791870 647791873
    0x90415080106080a050d0c21200316080906280f0f050421050a0b310f020105190f0e0f030d0804020103270204061706041104090602070302 61
    0x28a001038450845003640c0c000e24250b0013852000c004a100454088080b10107401c1049a9100070b01e05a034001029044041940080030b1030312070095400394954886200d404000c03001d0500c080480c0d9600d01a011000e0220880c9104441c00185414040c02d400300c8080c00c07003030602815486402030111b4000796035540f1490080c044d80c1c40c66214030340000080142c1001c103840300c901d40c4000c103203200d50300511362920109090b130810054450102a040c52700901039400054035840c001c046000280e60400b4480103044082c0d000d00e0140c0b02c0304039401004006004801d0482d1b6860582e6140e18070281c0c144081405640307071640580f0004010004076541e0b140414443c140040c0610348880d032071a00614100d03e20750080e0300e00103103c2420919600304031410790748900c0100c018103254602200c41e254402c448022442580700c880c0b5042e80308580502510342c4822103d41444405800300140341e0080300420041546081190040c02018201040b40715058030343c201640c3c811501200103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 647794370 1250 647793120 647793161
    0x7141c080405120c09060d03081b120a0516090b0a1d0d12090f030b060d0f020604060905011103070507060f050c06010e010302090a060503030a051c2d060e041101050904 74
    0x5d03d005401c49600c000c044400c41d030480d00d03030b46006250160050a800c10b50f001c00e00d12003400c0d21034074156070003402d85206140040c0b60420307012014040c01d84081d200100c800c003c0d00c00c010300800d1385006a401c81d003601400c0c0110000201e030b80c0d4410910300d010300301d102c041602d1651900160070348524060608a41040400b1000601044443d0b020200c410003654007400010346011145800100885980d08200300364244410300c0c03035070001e00952104000400203561f9030461190002c03590242c90b42801100810801d6482c2c0c0700380700006000d42c10081040c000305000d58103042d004c000b18600a428407205003401450460285c10009024542c00010030441c64418140b40e0301c00c80e051801d010480c90076010980d240681100c40040c080045422054860920462941c0000a035400d124600b0000c44010a0601c41300c1c2901c0c600d03020780e0032100c829066009100807200341645c0000310f80d40e01d480320417007294001c040700d04000d002c020b03c09040d52140a00c41d0004110600c240b031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 647795620 1250 647794370 647794393
    0x30406091d010609060507020112090b0910090b18030c030a021b06192006040c05030606010804110d240b01030c020a02030a111206090105040507141c08040512 70
    0x80c040380c80500e108101c0980d4014850198481d14210844105003407440d203c40700380c8010b90302c0c0307410b224a11b10300c81d25102c031100501071180321890281d9031000540300107100c1c1031505410f50f800c0540151080480d54081844202c00c444840310b100110029281402070200c1d150340bc50303225144000040c0c0c440943c20086000700003d401d5600c400300c0b03240345414a0004201f10b55020032140710280b00f01400c44050101c6042e551402e400b40002c11385401d481c15180c0a5140314960103010301130721450001541a5000ea0100c0303000380c0e0840041401e0301d170072804010036401f248104032910f0703102030f01001e102010f47c40c14180d0103c25000100f5480d540500040480c0c40742c070548811544020100701c0581c42c003107040385c10300341c2285a40e4500c805400108008684038541c4000a1280b0020001240e41c190300180c0280c0c499425a42c40356034480f004400400308610359944004072440700d0b0320f9402d8105039002c2a910070341c01c95040503034450004210811000c0000000d400100080301c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 647796870 1250 647795620 647795639
    0x9010504051c0b010b27130c0c0b0609040f1707120f080609100603090c03080c0d1202030717180d020703020301050a020c0c2107030804030501150b090d0c0803040609 73
    0x1340506031140284c1c1c20115443c030b2201c5000c00d81d003400c0c0384000c1050807201643d01c0e2050410f0b1038000403130060001c1c80b080d8800070400241003030181c60482c03a20303010514500e000d00fa41c40c0510f41040200d465241c0c03d880d00904044812000089050104180d45c0010f034a0101c035480810951a1003110b05a01711001c0c0040000610385032040284404010710850250800742c1a902d00e03140c00160741501b0b20b00040c07114a07907000584403010201d112221303070000041030030035000e0315036540052581034550311069000075030b604008030308282a091400c5034140c0111707501c41d80c660705802c4604060350000d41440205503401d001a00154028400c1d4202405002c0d000403406104601d4410824492911405d56415541c030610882c200e1401c1c4100c041101056000c0a005450200303590307180080d0709500c603200c02c40781942085100d00c090300c140b2419204440c020f0050038034120400d400c000c422480301c8000c90300b05483c0b5030007151281c420009800901800e40314082000e04190420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 647798120 1250 647796870 647796893
    0x31a04120c0201050406231b0d0302040e010504051e01080c04112a070308030f0402130e0601031e050102040b0a021608030d1505040e150604020a0c0809010504051c 72
    0x2541803201d210207400040c3d034000c0894084903000d18165071090341e00e610342410542e00c142101c403001c0c0c0200b00a24160709031030111401c22a401308031380307890080300c0094050740520700c00d0190b24540e01d00100f08504154100b140d001501c20030449102c00a481b181072010720a81284025a001a0305941c440c20180b0590800d402d0107240642842c000700c00d801100603e0009102c100700380555800e84c2c5000402100c000b840e4007403006503e0f45024040c58600040c1203409038450324500c1100081c21804c0e00c14005250400d602620082e800c64803500c40941d010751a442000e07440002c0342010038005c0c0f002e0030240528a20f4940e0312503150100a1a255000e2070880181c1c801d8842000f0740b07400001110700c0070030000c101040300304440780c840e210324070710340d001c0c0390010b081c010a00480380e008540700401d01e114801d80b4005890b500300b400220f015542200010500c40003201000c251a40003601c0140b80502d85180383c40d07115030208451003c074824040da0121840c080f04200500301144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 647799370 1250 647798120 647798153
    0x90b15120f10180c020c060313030219050c150c01090f020a0812031501051b0c01021510140a2601180312050405012a02070510051b07031a04 62
    0x31000c41410403d01d200111901070a1444940e070301d6580c1c3d03601c0c9009101c4a1101c0030010403150716803074034200500d800c82d6544001c400600608400e108d0701c0700c409440d502c407142c0040c001c0c03680d14000020b100888900f03281c0f021071100140221035900c1c600740200002d01d807103010403102c5480e051051140c0c040d081e80003131410360400c41004083c00031120549134441542c3c107002e6215400e0f440103031018410a20fa100d04440c2280c90000000c800086030034403c503085e42203c03040200180c0d0039401c0c00c02950049110300f00381c882048034a42c00003003200000401401c0901c074030b9444201b00c14040102681c00c00c203812103141c2e0485c11500784900e00389000c4001d900d4942c4101590000c1030f4805031810550000c6e5030b14086401d100b001d40c000c1c0b801c50708070280352420300944900b249654029101100052103442400301d481e00f885400302000515503201c3c642089103400107446100110004000584113801000010034010f0b030fa10101480e0f182d40020b07550600c0e00b00306698020f02c846 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 647800620 1250 647799370 647799391
    0xb0604060203030f1302040603061a030c091f151112040f051e03060708061c170f1201180b030613080c1e1612050601090b15120f 57
    0x10400c0180d4002c01183d61240003580c05248035518146002c02a5030000d802a4201d8075168000c401c02009610000c0518118445404804a010304040d550680131901e07940120313000300892130340006400038001007001e00b83d01d4030300c0c143c8510100903460302101c1464005200118042c400b0041400580a10302d04602e0040c1707418140400c04a800c0800d00c20f5601400740c000d1b85a021902c03110368882070304401003d480890400e03000c020702c0c0744401e03140d4a20030486282100444811101c035a07454136404088030f4005c0b54031008040954000841c0d001c4403100401c4680e000e8801c0d00440c502070004461580c071f55413089051032040740c072000107a81c00303a400082805114a5040003042e00c00d035228128642e90f05c1c4641d0402d090040c1c0d262071610340103040941543c60340011600102185030003c0d03003200981d8420f0185400c554060001c0c006402010040c84200c202ea0072080352102d014005412a200c170b4480d204456204022114028102c28180030100c0c2e012000130b0341250f6002c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 647801870 1250 647800620 647800627
    0x705011401050d110907030e0a050105040b090a0b06100c020a03140618061605130f080d02010501052209080a02010f0506030714060306131104240e09100506041401030b06 75
    0x2513481c224020310380041880307036200c1400245810701c80d13001014003200c82025284013200528106010700801c2d9012100c134142c11001454070b050004030311101540240b141070158458905100d405a5071034514402c114080072808096100c00c030000c0000c5202c0d00c003250b4400c050403201402c00b07001a00c1411b200745a11100c4186c101c0015020750011511a6400d00c100d05600e81623403d03100d1501c4040007410b0030708001850301010900e2000700c072481020b54854400b1000128201d910074040e141e0700610b80c143c4100503100d24043c0111003070505800186510f00c40d212a6040d8001501c40ca00603910360358170100303c1400c0d011b001e0304001e0540c0101041c504014110024807410a54140503075004400a02c050791008158409003101c0d04003001100032084115580c0c0d80b0078050003034460b40d24044100c40c0024210b8101c51502d003582d9114144000908000c001b90000c1c280000102c0c10071070205159448000800060a0136036505050944400c009401d494003009039030310564091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 647803120 1250 647801870 647801873
    0x30801210b010b0d0f060f060201060b160f14010f0b011106061c110a090b0102061b0306040507020309031b0418080f0c0708120403020906040213030204020903030f0705011401050d 79
    0x2040c100d05682c90405031585032520b0f2413030000201480c81ca0400740c18180080041c0ba00c1684240005a4840358001c0c8807060711100b00003100e200e0083e05d13003903034080e100c80c00000c52506400c9110407403190080c5104c4081d981c0c0007500303448075130740f82c0b031940c643d601038a00d615a0041ca902801c0c04802014100600d05680020f00304850143d0b0310191310140e00401c0c042140102c1ca42401010080910781c401ea261503401c40207100100c2c0130390144c41200045100d01400c4c0c40700c0341800d130165016a16665803002480080c01e0094440801c1d840b09005c101000d43d014010210b108038a8101d2881c80002001040140c900280041d9080100210020003080f05501195138500503001061741d00d485d003e15041c5020415031140e2410b026070915a62080c40210040046a0080317500540940340e440801003244955550003201400040d820001414560045c2042170750081c10342c0c0c2070041ea040a98620b40c440b400440b103603556124080002660f41d141c080c050007003a10a45009440c0c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 647804370 1250 647803120 647803133
    0x5040b01051908070e22050a14041104060605030c071b03060f050a0606171302010c0c060504180c0219020609041508071d15060d020711100e0d0b1806010303080121 72
    0x1907014007166070f911900010b8008d01150465404181000b418000614080c101002d00552070380580748107030306040b40061050710030b009403070013002e07080304c2c0034500916a0f4030f0041892142e840d0200e41000240008003003940e601c50414452151100800c0c41d1920305207aa040383c0c010341122003400100c1078001084c0b50001406940003891000c0c0c601c0701c118500041c1d440e0b281402c401014102c850801240d03050380407015008840c400080441009403000e100001c0d122195840d80041e84800380840d107201c8107695880c241d50014000d0303403400009201040c03e80f10121902201c540d114801008081c4003002800c0041805011080145034200400640950060b0078000d41e00c0d4102404480b55440108850301100c41500440d900c14007881d1072000351508184d0b243c82071103122400c0a809015144005500d8001844030a1003049566070120b03908000d030044100c9400300c01d491500d20020485540614020740310f051966141c55036503038001440d9034010441008030340303040002500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 647805620 1250 647804370 647804419
    0xe0a0b150702091b040b0705100b10080714030c120f060114030405190f110d03231b01021e0c0703030e0112060620030c0705040b01051908070e 63
    0x28111901c45554480308a401d408a28070108024044c800160004504a0348402480010310030300541e114400442e078141c00b1541d0392070039260010b450003d841c40503031080c2d0f0102e502140c02c0c00c0c184151484440c2074409a042192612a2440300099180c044800100e0103a0b0100703101288050618001000802d200011071603002e00010210115007040000c0c450004d00e201e0219210441081500707040f4650392451805446410f00d0540d400010b003007402e0303000c0d90542c1548805101e03080c19940038445c80c5806401110f401c0e81804100b000802c83c004888010220a00168440d20b15416a208102511078031845448003000000780500011520307008580d0503050442c44105040c0c0140c4995081c80302181d8010700e040ca000c80c0b07058004030381541e4045440c00c40b11143c00e400408035a41c0c86009070782142c0b40c3c030004040081d45442d4000d01c8004806251040c10000181d408414041d000400100818009400c05c1b27001a840a0003104d2500e04490f58400f0916800750722440d001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 647806870 1250 647805620 647805623
    0x110102090607230d0e090c09010c0809030f0601090501060305013201050d05041511070b0f06060f03100e06040603081e0f0a02030c060601032307180e0a0b1507 70
    0x20721021810900080710b803506088480303200180c0704d4003001c03920000c0c03d0450341840036101d4914480814103240b421802d644031580103031524086441e29403500645604030f07010355641880350311062580e4540500003a4000d000740d9a0210b40c0c3e504040015050702c0050b0000d03d200d444441c208000d40d540140d40e06202840c103054000e5490501c1c0c01206d107880748c1d5074541c440f00d0402007031104007c010481350041006003042001002c0c9601d00b030701c445100d00c40026188482490203d201e00e016032802c0c903048040280094603049002c0c6518415402c211200d0801004c905810000781d40920b008561110046908201e02800c5545210760780c081c0410031200460900b075081906003904007140d5200030340010b502c2e21401c044000035581c0e0320817050401316000c0d540102e50954040d00414424941c0340d900c500701c42044084079001004020011403c101540b052205100a4100003401411184c8491601864080d07041d500756244110b445003d40d000302d41ca2600111070005490403203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 647808120 1250 647806870 647806883
    0x40b0d0f0218090307061a041b02070605090f04050919150606021915240f0902120112080d05010e010e070f09060f120203071812050d03020a120e0706110102090607 72
    0x220030090011f440c80c4014040d40d50014030703050072a150181c0002d0442c1107250584d003214082074560030112341c24000c150719182c10005102115800749406c1e00415800f201c0700080301c01490850901d4140d14000c05000d4a210445020041c18105180035140240c0501d0008150298034801c2032000c28050400140c1110207118944000228941000010044000b1388184404445a04500301c0e5060b11840110704d0a281d00018007000034000d4950000000300c00e204a42e00e0720070340100c020010801102e000408000c03900703442031036100e15400f0b4a480401c6010940c104041e50003008409402c1c0018000e0340d0b280c4049456000d0404c00039101e00d450a00091440c50030142d6410010b42002440c039400032082081c10756009000111345200c40a0410807180e85840f1070034440390051028015400409891032110301a400421948845140400b41d2020000c0c000d400c9600381c2c084507400d600210410441c440c0e0040448003440b4802c4021890300e040d410008200e88200c1600420701c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 647809370 1250 647808120 647808131
    0x80108071d04063201090c030506100305060d0b01030f0309050607050d18090207050c030616050d0b0a0816140f0108150316080709060e04080711040b0d0f021809030706 74
    0x480c030084840c0c0c14641c0d00c03040307070940c204d41003150242e07555424010071207954070f0704880b811200d100340200d601905019042c0801c5550018045014040050419800400500c60480041c1103401b07000d00035409402c0010410883d407034000c144082039802180300740000c0c1700041c046603010901940d10709443c141001e0310302d1914420424408203074060440c0e07030b1010998105000740403400c2c00d40c1c00011819030704603a46000c1100c2d214040448c1010002d402030021300a4140359510084a0b960024100d07221a0b075101181d601c5d180601075268900d0038140402c0008040c11599080155000c543e03510032402c0c1000000d1010310300a1042c11060384601a8010030744050003000034420508032805c0080e901d4000081d640e803c0361280b050103610b0584c0c00134445058100880c05a80d110803c0d80c50034445440e04c0301c1981c04003440301c0e03020395140c072860041c0e07598000300c0c41082d101e1501111255014010400c4402e241180350141b150854100301803050040110b808855024000288 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 647810620 1250 647809370 647809391
    0x16023309010f020d060546050a12060605011b02010507080c06011205060105060f0a1818090204050906040201090302010f1b1a0a200d11040303080108071d0406 70
    0x50300d420000d10008510000700e4018aa20f160404d45c160b4030151480d0301c107802048002c0c240321030205040305034007010502008001e955130740300603200842000f058141320740b142d0008110041590000031241b01446150082010701d0180b28000c082c242400300e4041e0700b20f0000c1008552000300281080000100581004480401d40d141d02c6110303404c0f10920b43c0c4680b0a000c140b060b04e9401e0303c40307116500c0009400e1400d40d0440d0000c5904511030b5080a100d548140c1d00f101403045041c01c286410a8041407e0040d40c01100d40c0311029500407486e000c2c41d00521085807030142c1844406d070030a01c00c210150740c0100d0030b08112075081c41e1602480c1c0b40d409048a0001c203016091a456016851007018000030240710710316404284464049520388054140845e010744010300c03000110141c84840b18000ac1c40940403183e80f20402003644407201d590528264445d8000300c010803041e0300180080f0000300302d140094510f80242d0b4580341a404170581c66000001d02c020007443d101c018015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 647811870 1250 647810620 647810623
    0x11100603020333090a0512031003060504210e040b3307080a05180402091f0c0501021207090e0c090f062b0b0102010c081b040e16023309 60
    0x20b000c016103c031442501c0c180300e08140d442d02c1464509031203510480100382030021811040701e0103810720781e0f0784101c007a2940d51544c0140c403000b0801d64203501000c1e4007002109611a070400c141c2215904c20020401200421089404010802c0c4c0280c40320741ca03072904c1442c0381604200948400740e021500c40c040c0594200700340305000700102490760115400207803580000180c5940c00941004c1402d488400081c00100c0c0a651411644200c1605c4035241c09400700e900c281c1151001d02c3c1401d840700c100e4a510b403daa00400075000005804c00c01c1142c501e501520788000340c95910f08071052400e06500c1450940111010940714642880c42105d044c0d4440c001ca81e03505400c060082c00e1400920004160041c1007908502080e0511351168250b43c41031240000501c425111514645c40f11160034121802c0c41c42e8018102c1c00410000c20700120000280f44621160714800505045e01d020003802c03c001c91f5448600300100c41c041814009240d6022a0403c01003840c803200c0e5600da0001320b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 647813120 1250 647811870 647811943
    0x10204030c03060203060f1c02152703060a090302031c02040509010801050a050a02040b040b030a09050609061008150103020d05070b0a03090c050916052107111006030203 75
    0x411650703499030004204422038018502c0b07901d08541845a4400c460f040c403c035001c134030300c880100b00204800d0100503d000d2241e100489240c220190800c0e003408929000c0740102e082045c40c05408034021652441d00300926070b40122081401c3c800210260fa01964074000c801511400701d0450181070341003000740e4142d0b40203000092206081e565292100c0c1d00821060302d40140043c00c0c80001504141b4500868046910b07001c030051400d0f240403c00341640e0006082841110349034042003011400420a21303018140320340180246040c04003803103080c00c10b02c0c0d010328003540100c111080306007100c05249044a4054a440d01c419a0b149441410151540c0023041d45072070100c2c0c2c4114007680340d03003c081c1080c8950814518030380c4600030440c01004c11140010b00d250090f007120f1019118002500d01807516500c1c0c00000c1a50110181220104442801c001418210074440190307080000101c8181c130583c0400c103050031034000c00c0d00c86038115081c100b0003600c8011035500382ca001c0c01c013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 647814370 1250 647813120 647813123
    0xf2101051501020c0103060506040506090f030d020f15074d010c0507080409090203030c070e100905040507050402031e0c071703010e010510050c010c0c050105090a0f08090301020403 80
    0x810481c03810400511091045480030350052148529407201d0354042d1040c0c030705a0303400500107402d003441d000801405501488115400074a010710070456030720200f045240d142401c0e0082c18611001c0c010303591030850101402440c0a291900717000e52260481c13212503030180b06203449224092034001c5a0300e155542421201c401400d480e804e400309081140707006503082c005000307011b88107070301408450700c2c000d82c800134080b01400c010811030300c4007a078000d5440700d201400740c0341007030215a902c90400b0100d03440019541d11043c1080030440c0b00b8103112014180c050003c010750704003a103400d9544e100c035000e96070081e0380c00408035203960118107480780001194420300960345819031f00c100300c5400451007100c02c4287c42420164a003400300c1524141c1e141403002c161987c0c600410012502030700e0305d00e1f4083c131001300100c90b20914213004002c4202107e0b11800c0d8884400c2c0340003800c6680c010400401c07500b2003001c0344005081c10380450f680d00d40040d4110b80310100140084d00900c03542e4030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 647815620 1250 647814370 647814373
    0x3170304140a0c0e010b0a0e13060b04031212050c070615120c030204060b0c030d0f14070e0a080606010e010305100b16140a020a031e060f0212150f21 66
    0x2500742c2004032044400d4140c500c00d048031042c5913a070f5942c580450107441d00c100041011a101e400043c14001b0b0806040d1030140350100e10183e80d005039803141e03400364200343c0b81d81c0c012401c040d243e9900b0001080400c01a089c0c1040300303142036240744069024400c0010030303032502c4040c4020340140404165020307010b039040707a034aa8501840c010041d1185840200d00550400c0b20008501d60902c060750480d40e4004040d41ca800108900c04e002032030300b5082d0075400343d90f504020441c00010f0031070341e1046005171940c42051407540c0c104180ca400750303840320307032294007000800007280d1380070702c04142d4500c00703007030125090b190300070051050501340d00080c0d820340d00070603040c41d0390121942000d00341d03005802d40c203000385a120196880f802e0b402c60107504000f40080410000b0284030145130005454400000c3d03580c020743d641030a80305410040d04103284c011500300300c480703143d040c2c0542001d10503a42c5821070700e1b0000800c2080340035010b114801ca0240001d41e10290407240d01c43c1204030801c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 647816870 1250 647815620 647815633
    0x60a030e070803180303030105010c03050a050d02161a0907170703020d03020a031b08040b21010b0c07091a061b010509070608060f01082a070803150108010317030414 73
    0x44806a40e40c01900914242c04d0007030070480110309001c01200c1c180c40e0180c5d100801000580c42c2915545e001030020b00410800f0400041032020358405481700c04014aa1440050540d06181c00407000c50130250305012001c1040c41400e0100040030740403110a902030607c100602c60000381400842d50019420900d41030780882050f60200341a441c0a10076101c004000401030700e0038042450241004000d40000c0000340300c9038142da805400403103154060100303c0005001005403400003070780300c0c5505000220b80038603800c8050003ca0054460400c1c01c00c44490b564440d219407400340350490380507510000d600c40500c0ca242c0c2a00c4c0100c004100240464100303200c00e25903802d12031141c075000900d00000b2811a02c5c242c0508005220140c3d50b400f116203e8802100b0a001c214502980506d031106100c80d051103000041c00207039000e0003520781c40f45044c030307509000b901141190b0b50411500d0401070001030105d00090b58407110740c1c4191500c13a03403640781c0b80c0c059547d064090703c1c0500c9081c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 647818120 1250 647816870 647816879
    0x190b040806100e0c030601030f06230a080c0306011202030f0303361e0f0a0501060e07140409151d060a050907050724060e0f060a060e060a030e07 64
    0x7411a0081d54141c0403080440c1d40c440304440d01c2442916406110754003040030401c03a43c03003900a01100c01c5040030028000c1d0351a02421990b000d401c0c074440c04041d004607a50054606244018020103484010381548030310280003d450b0b201c1401100552041d0945001c15504c0401144050340c0c40001141e0303490402002054074000f002042d09001c090390070000000f4403980d0012841200407d0042c0007441000700710702a0001d55110605180c468022000321100c02000003000c1f860042000040007402e010842092000085c1281c0038403c8003030285415840440846080307400c0001c0001c0c00c00303103070b400b40880703006568440e100e80e52180c0100c10380d000b0044210380c01030104031810140a44d40e001800380d03000c2c040f90640c001c10000e002d080085410a182d541100b580c2107404d1044008800d014404c48900c1c0c0c00009840101104010b030080503817002d00e41102c0c1c1150b4000c0b0140c50144002d24035040000024002c50000c038641c0d40ea40c0c0641c00c40210041d0000a840150b900c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 647819370 1250 647818120 647818123
    0x10905010c0c15060b040b03190c03020d0e01050c0a0c03030e010f02090301050f0403090b0a0905060307090618050901091802150a0207050109030503030a050903070b0f041208070905190b0408 84
    0x189000c2d43c0c660f1011020307210300106445020100e6402400107420980b42071078121790350b00000e0a00d540e600c445501022082d000388215060000c56440068503441d207480342004880d44560741c50704581c50a0113011a0003902d80a81d0a00b01592030b096035005644c0c942103010f407812801d242019802e0541c942652842600500701602059008000740e0756000101c94000e05c0c240c40c05004224664404c1c00342c118100014070242ea16418403082c250b03600d00105880e0350007200c00b0000900713242d10503c40182d005010640902c01715410310f85031410724000407484103061080702e400039620440f140303100012070421442c1a80041141340e900100c03080102540d4004020365005009400000c81c081d80940c2c1d5110949411000950555a90242000081c0070203050b41c0c000340b00034004d48001503210030700700b403003400c0c2d0000041c02402d0500e0268000940203890400788455081005012640325040344100ca00440d19004544061080444102d0061b00524485900054082000c080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 647820620 1250 647819370 647819387
    0xc0c070e180c1f17100e01050a03030503060402030402150a09170706140703212f090904020a0b0403230307173007080f090c0909010905010c 62
    0x318400c1c015050381c91000000e40351098500c41960000c0070444070012055940080740c2c00d030f401803c0000e21000c200300082e110010440b0440c4180392030003014081840f039200c0b800c0c01040181d44030b0344003e0840e0b8020301103000040c2140d00550b8084001415942c07044450700c0650071000680b561081d20362030040505015010300302d41d0400d580d001c410100800909801200c0c200c0d910051400041242c400b155404000203908116030030038400f00402d40108401e4101082e81c0d00041d80b41d40720007840b071762000402018411a0751206488000c0c06400c400c0352141e00040f105d0450503a136a100190502009402c6a54104e102140200402c030720307202112511005100c0f0310042003080c00c210317540d910031014004d0407250704161107005202510301a0103c0454204401c1000d0381411580599140c980f41000680050307030f05111685401c00f00c0fa50304a080b00d4800780441c5440c603072507540c84410600c0745002e4035400b000a18000405e42c40341036030a43c007400901024060b41d8004040c5d84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 647821870 1250 647820620 647820631
    0x71205250905011e060e01091802130617010b040e06042019030e031914040302060a0518090933010305010b0a0b070c0e0702150c03011805060d0b0c0c070e 68
    0x40030031300042841c1d8001c440d0141c2801c416503504185904010b0201007507100e4022100b1015024442401041030a8044d040a04034941d140c9690320001c665000b4140010fa0102c1180c0408000500c01c7c5802032501a40c0490103441c0803070901714003591200c510110341c8004850110125041c862004265081c3c080344000b550240014254028155220310440207000003048459610003040c0340034882c2c4200d00c2950001c0581081d40c1c0303801043c2c00d58002400c9000049000444958605000044201040c000d0b2031058181c84c0050b450b665803080114103000b1054007845500c1c80011098090702c50f500070342d01d02c10555a50b0315049001e02a01000c5611500c114000810042500d03401c0e03a20303498004000e006810702d025888030f95810060700c01d00846c0640031030100f0303010128918900440c0e4001041da625890662910640c0341e950440c80364090500c018402581e40c0c1030914400b6681001081426450740300201031644124105a0380714007404200149051513039a5892185 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 647823120 1250 647821870 647821919
    0x200328050a061a041a12160305100c05031302060d02040906030b01080d0216060e0109121a010f0e1f170a02030c01033c14040507120525090501 63
    0x180543d010803003603810f03040d69981d408114100711406880d0510462505a1800c41620213146010325007064800550b042922283e201404070280e00129210f1074820340014a0402d045041880c540e000780d649640d0040e00c1114046061f45020b2542d0b81185c004000c048010494195607141c443c030701003000d20400480f401542200542c0c1400420b03442d10060002c0c0400c40c41c00d0910b0760980d1901d01d40c08a0b64100140140080f5941c40c2c0c0300d0000c51030700c0c016122000c20840e4454a00b110b01c40c16040304c040f04c46030200030005c0070400c80d50b0b2078012005004042c840f129000c506500308c0303241d5004480403180c400e10381440d0704c0085420313800385000350306540640400c0001542900c4a00c24a141d0b0400c1030024040c0005c00d41500c01c0781030700c1321401c046014880b100d404045d2800c50101c42d2800e0301203420310040107c1004420003c18000d81541d900d40fa03152034103901c1e152041401c1d000422049122843e005400c5168400341504250811070f658684080b00d0f140d00c0f110101015a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 647824370 1250 647823120 647823161
    0x30807030615030e12040303051c060504110705010e0f07061101090204140106080604090b0c0d1d0c0307090606020c09090c0d0c060e0906100509130513200328050a06 73
    0x2141e80002c88040d203030940c69891030f0411241c0055050002b40e0710015105943e4800410143d030b031400f0300031103842c0e1030103100c4c3c0b910400d040007400c40d8214100450310340c1c004007004440d0000842d83c90200c420394102040c0c07845941402c2070261400c1d01d00294003070300d03003041083d0340c281030712401c3c0c10380e52160350310040f0b5510b00050100301d41d0510b9010740704501d0000040c018442e510000c0c80c50078110b0501140b100c2d070101051040d0a87c021801403290880060001c80b03050030028039005001480084c1b107064134000029450f0b505244619014100c88000140d03104410000035410340005043c03014030625a0030041e1341c186803801200001031030303954054500c0c0f4102c0710141c0076032002001034810010a40098034642d105240e100e03000341244012404407007032885014440c91441124100805007490621a0500d0310306062202a0a075000200c5544000070043c0106e00c04160f00041d0040a920104422080d00d01c003c151b44500d42880c1c0c200403007030b00f101c903007075a400130007010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 647825620 1250 647824370 647824393
    0x11b0c0b010b03060112020c2b030c030b0d120c050708070e012c1314030403020414010e07050a03060b1c0b01030608030f0d0902031905100504020904030807030615030e 74
    0x1103e11094910500040240c498a11004180e0b401480e2000303004084440058001c04000b440c40070004071140d078880c80308600a03200d5010f006224084150b8130b42044048100d034005803900c03100e110040c1000c1760a00e07404024500401d000f0550070380240445280d00e503a44400355848415001309110400e80600001e000c4000326100c081c44e0100c05842040d40d58000d401300c1c0b8100008040740c0004840541d084049850a0070300cac2140b1145ca0040d65a6034154010b00c010780b4000c041c07507482940c518004020302500145100d030805010b140860741d9041c148001c07405030a99030840304e10441c000030b1580894008000c207014a200001040c002c540711180194216105803041c00d020350020000c0200315080c010080ca10804400e00003e042c185503000300345405d0b00c005c2c407441092821072494090060400040c124400306e28010700c90707450640e01083c80da0801030002400d0040e4100868520360298110348080c110115901042c001c2c07541000300a000b00e060f010405005030540c6c20b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 647826870 1250 647825620 647825639
    0x1231b0a03020c0f06030f07050d0f0203100608040b070f02030906040806090d05040f060e190620030a0f0e010e120a02090c030f011802090a06121401061b05011b0c0b01 74
    0x801c94040242440d003166503808042d40401f00042c03641041220070003848120391418030812010303414601e4016101e2621044040381300e0490b82048081c804075008000020340701408803a401032040c03404803d6110780d200705a1440c0030b640c00d0558460004107000c0707032174400080d11074802c501d13040c1260304254042c002503034180b1640c0a0200c008107001d07400c0c0310490140110300303440d440207001c0c2040710011307e1004030200e4041d008240081c104030080d58011040000d004084000b031400707186082c0903504040e0000b0404000c404c2404004030b801c80640e07014104161603c54060240407006440c0d05c42071340c45002071072040340300c2d26030030703000ca81100c0c83c2c5407e0700d20909455241031010390034009150600b850068622403480d80801101403161180111030004101c0794541c0c04185c0001c20094080c1d0b0420841c4111140c20304004003c02c5a1000ca80c0510074804001201c84180301d090150160851801c000040e0170703e80700341c11102c1d51009a4039501400341000f4403a990300c800c0001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 647828120 1250 647826870 647826889
    0x14040b090f06040b1f090e0106090510031d07030b09120c07170a170406141804020c010902280501020703030507061a0d0303090b090a0201231b0a03020c 67
    0x54003110309000900c0909142d440300001316001030208145401e10b85641032404003008061001400424080241211004400c0e01515403820044402070900d00440c180c842c030381701c0d00000c06803145001d01288013052080020014010700752017031540c81c1d0a003180032070404d41d44100c051088401440c0d242c0c85680942c0c0c001118103002d00041854007900e06890008821851140d00805000304000740c10b00c044c110340c030210404442e44640c07400c071014118090390340c2a10720113841000808001c24250b0034845128204540068441e086142c91600603c0c0f0f1040c02500070070704164030010f44003003002e010b02000ca1815004016516a001240c440c0607500c0014045082400090005801c40d0480490f40c13402940102c07800e0201c00001d0408201d0605c00c0d00426074440038842030000201b800c951000c16140280b0350000b0950000702130307032110980d10610711510b1880d01c030302200203021502c0401001d548003150018282c0340c1a11020160800c5001d40304140300c5d031000e42005e0000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 647829370 1250 647828120 647828131
    0x1710080a1b120b06090903131707050a0b1903110f03060f0301060b04210b010b0705010f0509030405040b0409050307200901050d0201030e0703170408070f05061905120114040b09 78
    0x3ca125585410052140e4860094a007805a020901c9440c5111041e002807034018142d9a14041043e8a0072501c142006203c0d00682d02a43c1005018090068044200c03521a014586010320759200d03007408800a103e00c40c50442402c0d40055680413640941001e5405141e040710124034211742c10041600320341d45840340c0e00721060300344802c005c04030550410351984604841c9500319110b040d5141140c400098010020941012071000d05100c002d124449880c00209010805410a4402180e403802507220381441191112030300d6090752160b07003007800f070300d5409011640c5608803450f000c180322948004522183c41d02c010018441d1030b12020a5040310005001f0501c03206181c0c0046024048940c4c08280034800c83c14000000f402640c0440109420110741c2074079103080a4406091500f10303400118801c800080c103100e2940c8210403074440e10f489a124441942c40072000307441c00d0168501c1e4840400982c030001030800b01500c400013107100d003190300b0051000a00108045800c00340e52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 647830620 1250 647829370 647829383
    0x1802090c071e0609030305060103090506011401090f0603051e0f0a0e0c030a060203060a05150f0304150603030203090a06020d1e030e0f0c1c031710080a1b12 69
    0xc6204401140000c059940c014050040e040040751034010382442c0050080b1000c80da01d07507201060641c0b40c4544e40c0c01040c2480c00303000c1d07100c19449080d9140010f014404103220508540d10460f0700074080b6078020081100c0030000e079950f0340030290040004490b40b03001c080b11242c4800400702045030b01403142e484c011003e512615a150413000400d103400102d590b40c49200d8212049540812800c415941b0628000d0303030703a05d8190140580e81c4066030005014842118010601d044081c05030b90100401d0418507031a59200d017002003c030300e50384a00c8240c00b450050701105044d03000c0b00034460703241e054502c00c1c0b0a503619001283d4900c10200c05400044040d592400d078180b500410640c0341e2040e10b03000c030304091001c00345800e041003800c866403280c1c030010303510103d414003600262000d01c02c0b030144070b16140280c07805402e400f00c00348624129081750000803080900c0300001d00140c01003c0448846100526050001d05003420314901c0074440c0c440006031010400b08044501c9602c070a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 647831870 1250 647830620 647830639
    0xe0115050f0a2102120313050a140105030f070302161103070e060f0d03020f0706090e0105012a0f0b1303081501120207020310092001030c0813140609030a031802 71
    0x41280300300f111849400ca0b0711800001d40c82900010420251400c00050300c900d155480c40d020400c80010b202e607121075240c06000c200f000c1d140c2c2e04401529400311050000c02d003103560b0b10b8401c40091140e421320180c8450040f5255041c010381c4101261921829800c4602c047d071110a0196035000840d02d46500040d080c4540d082810325410f8400040d00ca401268248404d90b42c40c2424a0001d80081c0005000e06008000362300042c05140d00404080c2040c5244034946070441d40d040725801d1403440b490b44040580e01c00c00c40301c1b416094107140c001e5100704007030420820031141808001000e8000a207a5004206450192000ca02c0d034450161a1041c0a200341c5040c10040c2d00701d03940580e0701d4001c0070300400c1004d0700f038041c0014203032042c0c1c09070503403514110a052158410f44c0c0301034101490040042941508042d0450300301c0d18070546100202001e14110322038504604504a20703009000500846120000141c1580c0c1e04540340cd01a54245001c407803c02d01141002135401000301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 647833120 1250 647831870 647831909
    0x20f0a1e020d080309010e0709060317031906140306090d0f110c0a031110021501090921020d090803120f070c140d0f1e03050603010e0115050f0a 64
    0x215400d07403000e4841040c1d1151601c924185401c100c540b401c040e511008651541141804a04050507010104010304d5003141c41d00300d00c654083e11040d095030000004507481c5160b0700d10072032002c90501ca040c4501c0791aa22080700304040b40b40c206001c0d21800011402c5948041520b0030020400d0b6034104000c41c603010308032840b0f04110101144c2d401000e5290100341c88813a00f40f8041c601a100d2000310040c9002409244c14400980c9411904a80c40b6200700d016200503290440c3c0c1540400700383c18059003040801250341440483d282000d2410211000f030b0003240c1c4d09001c1210b52207800c00c26558070b1a103520782c840ca0030800403c00c0c031800001c03160700201c5101a08464645004121022196034820024852182d0301c102c41d413240001c43d03100395104481010b407800c18900398011248485101d2503040740381581d10181610b8000068254030f00f54080c45052509400a120650181c02c070780300380901d2030140c580601000140d549050401d262424100d4108105152510300135 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 647834370 1250 647833120 647833163
    0xa02190503070c061b0f051611040605280801020408060f182406010c050a1101020102130f1d0403020601031b15020c03070603110f09130219020f0a 65
    0x1410902440103903c2154007046880c8034069081c000c48030144a00510300c070002e40440400111075081000420181c40e2410152414001c4690b1207440c401d8101d031a0400038010b40004c0c1c110741c0d00030b04c6007401c0c00c421940c0003806880b11004100b401707481c0c40d10f40b240542030b44242d0007994050740c00f0502051442c6a040601984020030404502100315a02c0c005030812848110031485103120920740c4040e030703010400f1560044030900300a0715043d081d9884c1503c0e20044034001e0056105103110030340030390003901213541d0900d01420f8846c080c4d455102c2140c0120442c01445410011010030440100245040340c0c0200e42640042c41c15a280d036580100341244085000b2006150740340c000365024114a14901803000303500981941510039040c5480c1802a07885181054240081404155820400c4481b02008030b0748041d9900e401001203040c00440500e041c000030f10000308250b00781140c07c0c1d110a044866403d40d0944880e11040b559603800101c006050300c0c210b2250400c03404034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 647835620 1250 647834370 647834377
    0x18050f15031807030311010506010305060a121704060309030908160e07140304120e090402010504090c09051804030207061106010b030a090f051f02030c0301061b06060906030201080a021905 83
    0x481030b03000e202c10448051442d04280307050f44200d010500d24807100c2c552250070700409a10081c01e1030700300554600707c5c00145040b240703485103003450808541c00343c09101d030740a10117005440540050703a94564500c0e0050041070b421105030001107401c5c03004100c0c900080384600e074280720340c14005040e034184003076001d06600190611003070044a90b801c801606010020314415406451076042d1038504100141c50350708514240c6100b80001b100700b00040c1c0c5c0000a95066502c540340000da0000039800642c0d240c0c0042d007180780d1201c3d02d540c2000000351041480c52050348240c1c05d440a0a07a1a9019600c10740444501c0c5180d800040040c0074001251010b907030710682c01640400d03440c10f10780b0707040b00c0c41c4c040e800306a030316400c42031070483e0112144120403000315541c40110f15524100317207503020350300060040c0410024059802d05a011080051489190700321004001e80d550318a2400004c22003480b040303003c03c2078840080c901d08040c2c4207032201c031703031904074024444084003074115019031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 647836870 1250 647835620 647835631
    0x10201150f05210604080315040203071202090d020319170a0207060507060908120103050714031c0c05030c0106060f2d200307150b180603100c18050f1503 68
    0x21100f2044160050200311080c084c1c5d015801c01c0e640c030304004d40c40c0c0c01c0522200741082d0117280100b050107011680001441060801c030400161111840d40002e074401c501490082d5241c41a0781340340215104111402824902c00c10201e2650040b091a01409000300204000035800440d01000740306c1c0180d0040c44080e10541d00001d41c1b15907907460000d80d410104a02d501c55007407000607c10000108040e00184c0390804d508940b052039007000903a1480320510000c40d030100c1d247c0c04503d06005490100e0582d034420300340c984031520048494000c014904c18000001d00c0100c0120070309014001001d09802100c50500e48002c0035490099044402d0614400300101e5541c181d08180071600100616400400035581c0c0360807504041e83c0280c00c00301ca80d80e80c0c1e0318203a500074141c0c0e180c0c12800ca120110040009084d07031000d000900f040003c0490f402a1070600d254030010310740c081c0c440101851592111107801c1d4851050203c0d1710500e00007150440803e4885c6000826070303d01859111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 647838120 1250 647836870 647836909
    0x240a0f030605040222050301110904020f09120f06100b071113060801020d0609110703080a090f0308090d090b04091509020f070c1508130201022a010201150f05 70
    0x20381e98400303d01241c1c02640c0005000010700c0700d41c00003014022080f4000c06048000303015181f08900e10745003920460304554440e9500240603e000c600c014141d4640391002400e003182e241118031061340792078010645800794082e1000042440070445408000d8404001c1c41d64201034460340c800e12001c07058036801d98062445081d40c40c03001c44a004040c05004082c00150b10703111841d01c110309075412038202c4c0c00d09038284000c0f1401d00e400b00781664900381e01450022016140c20303070b0368002451000c6000d0030241d0f40c58418070501d45c00c80581c0380030f202d03250126010307803400100031500b80e41203008a0301c030391f0020401000340940e0340d00034980c0d520a01858054565a034202d01c0d04991158607603d5800402280b81410b1020056a0b07900621140500100f405e40030030700102109002004400480394400034a4207591081200d005400041c00481e02d40c44000c000105042602030320300c3d801907082090f010380040c160100101201c0e12103645d81c08907801d01e410032640212507444050103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 647839370 1250 647838120 647838131
    0x8010e070c0f02130f0e030c0d0e0a030c0305011406040b0a060e03030c06040506060907020f0c060f0c150603010f0b010c0b041b0f050a14010807031d0714240a0f03 72
    0x540e881844c4503d14038481c000000e040000d02c500394065a241084040c0076400c184882c0c22501404030b0040042d04035480d00c42440606040000c0e1040c9240c0c10240c0407408140c008000c01005522001c0ba0340032071424045550382d450100001c0d80d01c40981550801c034241c504101241c02201c0311120414020141c900740704400800518007a0101c4054610f41e001c0014441e0904207000960381082c2c40e8070150032a12031260615036140ea00040c00c9020b01030000c0e074100b01440000c141c0d0030300c16208c800c0e103107107800a4a8203611114143e416a1195182c06000c0940c02154420382041d844c06860f28410f1011a0b100d6900402000740180d4010303c4062240651065500701071015242d9111003104c01c9090000384180c081007500300da5011040c0c0c0e280150540e8001c0308041c0d0101c194980441d1402c01c1a00702e072410117003a00e00201c42e100d200d00104a200e401d10005e0040c000c19161440651490400600007148000400c48000d204009410300d947c484e00c2ca46403c9400e50030007050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 647840620 1250 647839370 647839373
    0x6130e071d2202040f180308010e1602060f0702011107050d030b06180d06020f040303020f07060206151207030204021314100512042d140c0120070f0905090d08010e070c0f 75
    0x1c01c0c074206d040440000f5058801400035019400c0c0040c5c0200d40d200c4e0301c0d00703800b5141802960303401c3e014103c280b030701607030b2800540c0440c0700350811b00c0c0308000c01f0403d5480f01034901e0300315a01c160012615010034100b5008c0300181c102041603910b0030301c081c40802c10540307508007031000d40c882005082d030300e558080002c13296052002000b40000d5220f41d005140640213001003d0401c1d103242c0007902190802000c0c8112192150040f00c2e40d5401110391b00d030107201e80e4050324900021940000d4005001007401d5114100e9075480300225844407401c208841c0a400c00c01c12521001c40300d01010035402c2c4042c0c0c5e9032240c0c041101c0c1e0304c50b04c2000d40746082a21a00799585454030803a042d018542e015508104100c500122040c20004c040001c03d403407503121001034440365610860312541020401001707405a000c011607401030030313807030207150b809134480d56040d002e00421541c88286115544c4003041e210303c10403040c2d040303c410080140c180e49030f00070101e441041c045400e80b040d0041080c24030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 647841726 1106 647840620 647840651
    0x6240405060d02030d03020d060501210507050c07030501020901141303170f04080c040e0703030509190b0316020601060207060806130e071d2202040f 66
    0x203040d555050120b514142d9846000e5418404e01e0801c00d0030617019402048c02600c0e0a905103c0a901c42006594041100c01482115030386840c0004404180c0e600c840d07000180303450007904d006213500b805481d080c01500b0a480595000420b61415030704401420b0180300070082d082c1c140030009403002030b986094071000d0224040b0b03115907028030705900201c1d00c4a000c260103480e02c0315140c13080241c0d605042c92009004d289498422640030300001104000c482c1d00d030b5200c510b0241986c040c000800141342134a2400408214081240d40405000c1d600c204580c3d20164420b41e000c0f0300007417615030184d000310203641200c0700a201c5291302003421544400d0695142944440785c0d0040c40040409a40041150080100100351800c44c4540c4050014969074440600d441c0c00e2000c480000343c01c4540103c00c1071102c14040103007081d42180351140030742d14000414102e046500d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 647661870 647841726 := by
  have h0 := BRFrame.cov_init 647661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 647661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 647661870 ≤ n) (h2 : n < 647841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
