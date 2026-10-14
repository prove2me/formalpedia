-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2442
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:44.418278+00:00
-- url     : https://prove2.me/submissions/c7033b42-dc8a-4660-bfd3-a300daaa4bbc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439028776 ≤ n < 439208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439030026 1250 439028776 439028809
    0x203070f030b132a0c02060a050702121204030c050609010212030406062103080916051905030d032a09062a0303020406020f030720030a080a03061a1306051602 70
    0xc0e05000c5401340200e9043c014845803880c100300c200589901145c214862408604223101010501d90b0841d65901007409403401107400395400c416039240605401d400c18007044880040c043c101103528100981034035a240c10580c020312080040b482e283c1c01c1540b01400660700c0580300d900106401c8030b0140b40789510030b01c40403081c5000165090041180c000507100d9540741d000241140c003541540881103040c4d4108a880002c01c0d9004c0340100c000d018517511a540500640c1501508a5055808140f0f4800042d00502c03035480516890001582c0d46420580030480c140001e210144c841c03010806110703960f07907140e008003964900302c1c0c191400d1401e0850010b50001014448994144403080c04110180000c50414501e640e0308590300014444c00f82c0803008403440394100e44d804219244202c0e800c02070726030382c4600c41c417802030150050f8041c41e103c202410300200c00002d22401142c00180f440d10b13801c2456401c040c4229820340c440c2c02003006c045036440d004009079850007000d8002404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439031276 1250 439030026 439030061
    0x9120302070f060302030f0c0a1b0f0209010b120a1a180a150806130602190c030f0503010815060121050a1404020607060903090f12050609010203070f030b13 69
    0x81d0010240c0b01c6503660700070b40b04050062040c0080c140c41458500c1e001800c28510030389565105c0c0c0126400d051070204504280c100ba076552040c800441c852282a80c005c0c0c864600b00d0f80c80d113611752414400c20a144030001c400340f001681801942d80300c0700e00052048034800070038002e80c0c0050110054044c2a080b00d07074005080c042041d44902c2858200700c078041504030080c2c40c2603144c0d078903200020485031801c0c00b811039480820503e0703411039000c01c0c0400d05002c040342031240700070084c62005ca02100070038010b1000c0c084540c0100c0541e070480e005a0b000703100803c000b1010000912001d400d050501034980040700d0640303030b9500c07400e000f6201c002d0005014907140c46800c09855010303246420402c2c00801303001c0980c44100c100d032419034202001151000b800d1a040f64203400b03e030f124030400f0103032000c041b9441c1e640da850ba480b598050f0088449548440312414202d200980d44000840c184400c000d01d07450080d00b00800c81e03a4000d25192525914506140c1a1044440c50f00300008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439032526 1250 439031276 439031279
    0xb0a0e07030e0616030e03040902040e19021201060c031101060803090310180318120b010602010c0e03061807030507080703050d0c200d020d080306210309100912030207 74
    0x2541880354464040e040780042c45981480f1100a14004000207013504054660341580f040a1003002250010242c0e480115551961150b40401c0c241007640c02200d6480103000d844040091402a42e24107902c0e00c2c4214280d03403804400b40e810b010003150840c140030981c0d9210a99040038801c1358010450740d000781d5038404d00c220801d410f15501d1040e0354540780c50554142040d5035002e80b09400e441d4141130900307a2910a034500102114540c1c01001c8801110600004200c0b100460364101e51705900248150501c0040c1551b1b4180c1084000760140d002c03500040003c1c00b0240b8403101b41041c98250340c0d8140d100e440c0c4606142098101400680c440034041080100410441014458a28005002c11043d85c0c90500c80910880b4071080c001035a5114196583e8051a20464690050244005180a260980b02900222100c07881082c909080c0d10440c4042c94401d1003015a50018510300701c03405003013041c0030200048a40400002c00e101040d8210301c40b0100e0015402070f0001c04419 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439033776 1250 439032526 439032541
    0x5010530120301060e01090803030f0c04080a05030a030506061801080703020702090a09030e090108030f0f04080f0c04051e1803071b0f0b1804240f0e0906040213050603010b0a0e 78
    0x21765440d040b00c0c1041503c0e00d040003101b10201c01d698100d0f003602110000d41c1c82e40550801c4902451304044510700500d0101010424000014442c00c0c149880501c1703a691004200181e038002c400352840641c2c044046210113602c41c1201b0b550083d030b24240142400b082d0b07004903165010844440806c0e60355810900203143d0011100aa071440840310203006604182d8140d88a02400040840d6842c1c00318800b0b41c00665201520040d0505808492400340c3c2400301603030340c40d40280014007540c0f920000c169840b00080c0c24011a401010500c41c09840e9a025208a15000c1d4100c1c03405000c1405441e0003c0e85182d0580100d1035030b607103007056481c07d0041403a004c00080d4800e0108080410540300303c014450130700041c501c4116400202c441c1000d81c1c081e40075010603000c9600c40c0b240c150202d00e505961200c60261610304a80044642d02c200b0400c0e960b100a48020f03611607905403070901031034500d40017140e00c1139009e0004600124100d0104014541c20b8100c0501152243c0400014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439035026 1250 439033776 439033787
    0x1091707030507170307060e03040315050a05071d092a0a030e0102030609012903090d02010b040b0102190602090a0e06040b010f051c02041703040e0a0501053012030106 74
    0x60411004103c011081c1c9130310095492103010b000800541c3c803a0000c0c06203da051069800030360300301c0c0703a10000c81d8103181010b008004c2142e175510f10701d1409001c1004a03100c1d91a1040d120080745000603d040031804010b2044001040f00c0320405c81078001e0100d207242003205550252016081c19242e8480303007005025942c40c1c140c402e18031303032040c4200101c0350368051045044032540180c40c215490800c2071015154288104900c5120001040c04108040016186940f81180d4000c2040080905c100000e5440b081d81d0301303005900c58000d540c040c03900a0703a929403c1c0e02c22100149440500d40c040f0301c400c80d0039401070018003c04c1040251609240c09100c031000d01c00d01c1c010803890ba00344c9001d080d50040580c0d5411001c0d8400c0380243c01c2000c0c0d41200c01800c00c0f803000a00c801c4c4500113041d943d606c18002d0300e407200d241401090f01003500d4040e071410394000901541d10030924103081100440342c95030000c118020101e100006004c01d0000300000000c8680d41c0f030f81c1358140030300a000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439036276 1250 439035026 439035029
    0x20409060329040b06010203130608011a0414010e1c030c140607080411060706140412050c030906160b0a15080304050904060c03060803030c120a050c0d0b01091707030507 75
    0x1001c502c02400c0d41040c2c00a4200b85074000c1d449000f0140684a28004034a0b40c0105010700200001d50700c0c01140180e004a8040d040f1100d80c04c41c0e4520710045484808240214424040c88541d0000c00408543c040d840c04007503520080d1900c40c80f0490940c0d20005451070300000c4d0003046040f0b48042c1804040c180320403034441c025000703060b41d06081c68004c14580c0001c001405004000881600300e03580c3c801120505038002000b444214000d42c071450300302c0802e480c11035240c460213001e0b200d030b1800748040d111581802c60156051130042414003407a54842182041c3d0240405000d00004443c18402402106130460024041031900e400e03a94922190b00100b65a030b00030f100c02c111a0395445c1560b6440340e03022501003030420386404150058500368022032428000401040034910070140504007603181d5000c3c03d0740310b0301c1c1c0100d194101c0d54192544000214200300c83c0c85803803a9504001c0c281c42061501616440c0d4a4010301c02401d144000d01d441600000020070620804005000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439037526 1250 439036276 439036313
    0x7020a15030b0109032f0301230708040f0b101a09180118090512031f0501090b192d1202091804050a061505030105090703030f11010f0204090603 64
    0x10074507415a100c0014017552203070061040c0c046c0102c400d1101d0100b00341400c95a1340031340240302c1c1c402ca040810310a04a100d2803048a811030a0000f0401032080d05664000d94001c034461a2400c0c40d6142e0900e0030300001c0c8040d081c07841012000440d0200082c1900300c0291403214182c03a0348005082044126245c03e00d810a025010014001030607615000000301c2d455940026550900c3e240c42070401c010152954a010780110421600e91007001d4101014910602c41e18a010340f00e20054809034010301800d15405014040f050305800102000c80703c2e54154280032601c2902d00d11404ac040460f400910b8181d09002d4802c1e05564000c040003101140d51003055041905442c0401e18400034011800e0340701074008086002d2102c2803011450341504034006011000400405864070310061103198020742c41c19001800d18400802d00000380caa0590b9845c8600d001d9190803107c50340c2d80c0480900a550741c20140315010a0741c40200700409101d9000714001f0b01d98182294045103803070800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439038776 1250 439037526 439037537
    0x708120601020c0d031b0c0504050f040b130b01140d02030706090504110405090610090f230d0b0a0b0117010e011d07050a030c03110c0708010c03020f160807020a15030b01 75
    0x140000d0300301c903001648880810700d000d5941b049043c180442400740d0b01803138200b480c010a11107040100300e400343c442c50142d10004c1958540810031528600346c00800b41404021900601ca0390184091101c01e05000400c079101071072568000030700344003660b4403034008200c007210100458107260248540e00700707040f25401e040900c0c007404625080301c014007251040d240b003011440418050040d407400740c12440d8071000c02c641c0300d03070400300700010000503440218a0036143c494140340c0b9041d900841c503480701005a00303031101d0604001400090381007034180020344244a400030841d4404500070071808560b1906940340074032280c1154207051868403110030001c10852919000011a40d00c1d11452a000074102c1e10007201310028040d211045850040000d00004511000030303e0205445011000b0804040601000e80c124851a038401140c903005102080d280504819010120341c01401c07805e21b090016070000d910001690801111044034500c880001d96040c03280344209842030070f15 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439040026 1250 439038776 439038799
    0x3020f01020318100512072f100518010e03071a0105010c08070602040b04090902040c0f1d1206090a050d0801060c141c020703031404030206030105090901020708120601020c 76
    0x1401607003100100f99000f20003519900921078854005c50301a185901d65003801130500080003044028201007202d510161100120076519030134561034155611507000344040344000c0e028101030302d0000d24882c8088200452214410820b00500c5020301d00e5070007665951110b031400c4210b1095406007510014456801400281d0708a100040700c01e07040105c01da2642100d10780107000e841240c00a020926003c1000280481c00341c0040101c144222001d1000311381e294800c54a0b0050b2480b40c2d00051030070b00c028000000c0c08042c0da4644103002d406003268003510b80c0d02d1850004295040442c40e4015070360300083c4802841011400c4440b40f400303881651410400074202e10b203900001e4400c050111340f1031890002000000e11490b00136140c04007207500703400080c1d228a140d10098001ca0010b41c8444194980c00c8100d80903070303a00420b11411342c1d0a100501c01385d0702c8014168040c40d9401c00410021a203004040e025615840106d4100d516007600024240011160010b0240d070f01c1d6141e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439041276 1250 439040026 439040047
    0x201020307020105070f0519060e0d020601050f0310020310030b0f13030f021e030c0d03050c1909090e0109061d1005152e020d05031504020d020d050103020f010203 72
    0xc07144110b40901c0c00c15143d00d0f02e41020094081822001031091255540815420580a401142c0c3c54002e45d02007101200403c1300d181c507202d001203000d0040e00003a0062005240c07080f0b00c0d01c800b5601030211910403012059200882e4416a5000c540e100c1c1c00c0c408004010441c00b240e40d000104080080341400c0181a00e5000443c0c5a0014140004a0341d030480c078910030000d1000300441e4421307504011071444880ca4403940400c0d00000c2c1c0c0d01030700450640d610f0080c09010f005481000705145040d0250b044c207100301ea88000c144e030400c0258280060400311a00400a1013610346000044444052501000b00c03403003080c22a80096000c40c0080c034181d80814003d101354001030b004181a0389034110303580e41c0c5514008190740300c44200302c10501402c41401c0d0504002015401c40013012411030147d90740e025040800d0700203542000012002410070181c2c988080700a440581009500c004942c01d981003108607013211650ba4004006614003206000c000001c20700103145030101742c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439042526 1250 439041276 439041283
    0xf0e18030c0a0b06060c011a0901080d0503011a0f03010602010204080d031802042a02010b030111070b070f0306050d120801060908100515090115121b0809010f020a02150f0103020102 80
    0x60b000f420900605001070300f1911440b04481007009070070020002154404904a840c2a0740c212040c0111000070020070404800509484441c4098507800d007140c2ca8514200e030400c0c1101c442004040d000e10540b007046034a40b000d036020341a81c0c0c00143e140ea0070301000b1741c54a510440540101402e0251000e088440e24088412550301601c0118601c0f18942c1880580c010358001c054000e000b00c800a6226507040d401440e85010032002440078140d00c0c0c070f0720441070040d040041e00d801400004104514001c14801c030801c50b090401142051b035a100043c0002c020324000e860202a00f904072520f150b0201c5002d02500c210b09100c407090381000051582c4104443c1c610500550307070408240e07083c90091045240140c020503101c01581c50702c0030301c44100c540c4900306003c2100b14181c0700414a15010b81e0100a58815a1611540c112001220201d00c0036254440300d5503201c01000c9651140d00050807039810035001040241d16070303106103100b0b07880200107411808103000103000503079010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439043776 1250 439042526 439042543
    0x60108060f07050f0a0201090236060f1e100f0f0f120e0109150c091202011e050c0a0309080d09030c05040203070516050d0e100c02010503100f0e18030c 67
    0x26804c0540390b904681042c0e00602c0175510195020300d415400c030112080518242d8031320039114401031400c0c0c2c50140b0036903c0390340031340e2000c1d407000b003c04444415040500340303040100c0d12201708a8101d010480404c1c007045c210f0131700d240000c6100780311100250b000428030108448a2812244155030000001c218040c016518100c00e61503401c548409842500710004240c0c100d800c1a051215242c5204010003400c0d010b8004505132410008030350508150018000d501030b10344411988542001202c0e00d0140187c00b800d0060620001d0610002040200b4055200c0d40321101c85c0c80c140041c0302e04d00200140010100860602c0c140002910900e102d03003121025a00982c5948414100381c0f038a00820788100f0142a04003927800505c000081d01d440490500d486004088140c88180403040401b20002d5001c02c030070602510055100b20003d40e407007071800320042c5115031210702010050540754002000114000c0c00c5c407110300d22078000040d400d0340d111300542c40c01c0380040009840344c1c5d08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439045026 1250 439043776 439043797
    0xf0b2701021518030301080c010906090303080a020304171204031d031e0703170a0e010801050f12010f1404050601050a150804050307021003150f060c060213030b010305060108060f0705 81
    0x15440490f080c2d800303e08103442540103240680781c403507031502c143c07a5656503c0b900250000e446104001000d500503d010402d5a415541e1400c0c6560b43e03201d00d00c040e500c00b0300121030440d4911181c101140f80c110281c03c2c0c0c81030300c0e018070900e030800d4100100341440950800341d400d020302c0b440d1001640e00080ba403609500c0da5116544040c0b01400042c24a406c40c1c0c0007a1001c05041004011580000c00601e5142c1003900d0700c880102e4540011070300365501740101500400500302250345454110300501c0c1e81c005038800850070303000250012041c0c0d00c58002c0c0002495900060004000c0d0a015403030241c00242d407480c00d101d150104640c91211000d03410014482e80304081824040140111168590080c09803403442c0e580d940001e000f0700030380b8180801e9054004002c00e10b90400d0580d001110001d84d6520240c14080c1c41e80c000950040c070703026104070440c1000000054090710928000c502404c054081989420005030501800419400450400c10708000c0d45a82000c251050601c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439046276 1250 439045026 439045063
    0xe0a0f0f2310200f04090f1503112b020a12020102060417040803180405061e0103020904060305010c080702060702060103020d151d1b01020606030a0611040f0b270102 73
    0x420040b01c5000740b40681841c4440f10300020044821984c12000f0400c60359400c40c200542d040000e2640200c0e0040007000064480e20441000480e0130210320805040c0014502050701441c82081000781a100042c8544000f440c0100d000b0f618081803204000e009050100c00d1281441c0c1c0000e4468000400080c10785940c4002c503411400c10009940c0545240e8007200d98600884054441061800400034440c50070140022114102040e540314125005200d920f0300e107090740015030103508128015a0040e82c1c4450000c041042401903c003090600d480302d154605101d50300a00f41600144500c05541c48600100016180c080c0451480f5410981002c1f6040101010002034644a00309111100540709403010a00c80460114185555101c2040c4064031000042e80c4628040761142d0713240d08080e0003580800e0342038001d007001e0b000c081c003c9464580c89a0041d010003a07590840c0494803008611016130f484100441180d0030014880d40c0584103100700001d548120700c1c24140f00d45003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439047526 1250 439046276 439046291
    0x12241508150406230702160503030a08071d0d06020c0c1f050901140304110307060c05120a050910020607080c0405210715050c0105070302040b0d0e0a0f0f2310 70
    0x307180300641c0d0081811049203c03445c00c085100a5840f425034844500c500c6141d100003c20745800012110502e88544446010780c3e10160160345230408501d00c1c0001103001c0003100340941c2d404e00104a01407050000580f201011a01c051800c50300700c00850080b10720107000b0b2024100380c0d00404181000c0d2a1059640303400c28012181d2030b01802c0c441c40c801101005100401080e000303003c4044101303400301c48003207030340f244200da207980c4100c0701820607040074000094058800c402421002c115040051401d0900ca0100f42040008070254006810000034840d405a1000e60950020707001c08007542020700740b6000a603103580710411001120750450503400504414400c910083c031014962007141620200302174500d9000703002d04400c40d460100080c0341d00340607100380d40c00d40b42800101401c0c0107405d41c1c010010281d071010b40aa601c01c0986420000c0c456a4035044200e1142c010840c0c14040c910302a008544800b0070f00a40d4440b59108a444035400288080302921800001c40c240b03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439048776 1250 439047526 439047551
    0x1020703080322050604050f1c08130b0702060f01060c0305090d0c0e0a02041403011401030f050f012a02060411041107060f050f1f12241508150406 65
    0x141d0543d2610898600c1c81c0e4540001c0c45008600c207407046014009a030702c03800c000031116844061200404800c0203501100035400d502c60079000c1ea000c0b0281ea400390304001542c607405410a0100c2e01000140c0c44481046260303920050014010400ca04100d0702c0c0c0b00c1103076030207041070107000c40d0680a500c40808290900099450f28002040d14045014030707030400320100d4010794050300440104411440d1200000d040520a49551065540245c0500c0e400c60342c0d02181c2401c081c4080e0b07030600c210314131502651000e00c40c2c140813969680c180e0b049461000520313141925071850010564028008100108410105039004503004540c0003507032111210307052020340100200038280c6071400c180c02c1d01c8000c1aa0000d03009000540d01c402d01a6120b0600725620a910301c400d03007107640c12100401c45010390804044002e0700c162a0800c603401018400709501003851041c0680b240c642d04120180507108001102030100c00e00641203210001c21b0311028024040d200902555a41d04d204648 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439050026 1250 439048776 439048801
    0x403080c03070e04060e0106030c05070231060e07110a23030d06030602070c120809010f030b0301150f170c0d02120718050a020301152a0b0f0a050105010207030803 72
    0x83c0c41c4010010407110fa211404110500405d0007403030086898200180d08160180041d5601194020f15034801034060083c03080215125a018036024401842100d880a03c0c40c09014007504010707000d550701e403074a400010051302c019048040141c11032a00440801d120b2000034006445000c582c51078030315900c04592a51140e126400c0d140c605d081c10110401c8401d80040407010b00625a00a11644500c00311032039800498000b840070764208107e0703071594081d1602c2e0440100a060010317140d501c120209003514000f0101140c5003440390f0041c000b5050101186001d0304000040880e12036103102416a5041c030661203510904a9401d042c01315510300c0074000d190391181d02600e02d01e980c0c0f48c001081c07030300303484050601c00c03800c207400580204110320a84e41201d1a036801448540c0200710140d405003052005480380c20022084000100d002c04000c4c103000d44150b81241d02860180581149100041c1511140c2e40c100401000180c0c0d002401d01e00f40d03600060080d03a2500c0340c0410400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439051276 1250 439050026 439050047
    0x4170c06030c211e2707050f0105041217040b030103050c18060a120609320604020a06050d0e06010b070308180a0305031f12050c04090b0a150801090501150605030403080c0307 77
    0x556041c10102c110317025021404c0800c0307943c01d40d0095416100c001c0107480c2c900943c090300c03085404d0141180040b441200c04196040c0d480385000e4503103500c6640402c6d00794404d80054415500c10381c1000d4450905007442010503009003250907240c1002000642d1101c1944510100b04007103080e4002070100715440010401e50102c424840c1e4500c000400c00c2c481c400b41032040404100000c903603136052000c100c103441745600038203001d413a41c00c2c1102580c09800c8045e060980707555503000004048010000c0e180a00340c80070316180c50707036427601d001401d11070000c0160010f5000e00080d00c0310150f000ae902e14000b03070715081c07182d120340d174201c42d070401c2c084404602c6801030b030141c00006480100840d60f50306140102d00f0380c4d07500e5541c5800e100541e200070400600903203520000940301d8800e9440749a08078415521094120f50743e085807170a540008100740c5071659282d461080d0200311000c1e0381d0044c02981001810740c40c1644003d0301102008244205183e800000a62844e1064403002c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439052526 1250 439051276 439051321
    0xa060e0105100e1201051602070e0c071e03020705120a050c011b060c091d0601021f110403111f02030901030c030908030a090b100b04170c06030c211e 66
    0x4134150003c1d403c1c0d002e08002d8a5030741000d2003200303184140510120b000c405070380400a0500c01c507103600c010b0681035404200e058841a46100c240d40c0c0721007901800304200780c001c0c1c0c000d0150608240030000440000801000e2030fa122414103400035801240304504600242030408564801d50a03640c51307045402c00041c1031501d8607448031040c0390441c9011040e02c2c07628900c0107101c0030240b4205d0b41c1180680b06140503920440e9440d0003050b02a0401d0581c080001c0041005000c0681e0f112154100350011240030b02c414500c00190304101d03003411440135102c0455500c9401c2c0b210040c0d140d00c0794540450425482e007000e001185d0094000204603613110140590328542192a60000d02c0ea0040480c0c45525a0010031414041d0003d00d00c15154002403041c074081c58120710780c114025414001c501401144070004d40c03681d0b18400b6601c16980250ba0903a1850101501300804c051080d491090f00d0915040c020301038030b04400e81c443c0c00224038005806444051100c00e058040c1c05520 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439053776 1250 439052526 439052539
    0xc060902010917030d0f092109080d08060f01020111040b09180c130f060207052103041e090c0c12020a08031003170906030c131505030702060a060e0105100e 69
    0x1e03c1220000401001c40889041c0104221809030910304151222880060500c4550842d80c0c509a810003480c444488507904200105941c0e50072000c0c1800c0c4044c607e40c1c0410709000800040e81082e14800d141800248003c001c02c00c15060110014040c502440b1041d60000c616200a034035a0030070180803403001c60a10391140f50000c50558150f2060180c58800c807070b010800201c24008028110a40703c1c1500508601403c003401c0c05040000300a041d2541401010003a0400c0c1d02400100040d244000b00c41e0098459200101c43d1003100d907002e001910b00c5c103c41c2014a503401000c6c42c1c56503a00a80d0564040707058407080340f40c1f03580310401911401c000030a1204407038580440c0700440c0c0c40362140b0806070080d03c166101c14000c00c0c4900c6d40084040001030500e0111a0003000601610b11843d1022900c0e0a00d41c2901c00f102c14220300030901c000300744000e0310f40410405500240580060185130f05003015611000c0061003036601038144004c013140818090f204000140c18040c01c039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439055026 1250 439053776 439053809
    0x50318010906021215030105010b03061c020d0809010206070f090b07020301330e0910020c07030b010612111e0d020f0d0b0a0518040209061206070201200702010c0609020109 76
    0x1000b8240055403114485122170f880301c0b109003010300821b81207e24244125055503135000610a10040e8006190800781c0c991818000590b0303004078080425004031001500d40008000292504801074440c80c140800d40c040f11503200e030b00c0040c10003901c07c1c1d081178544450311840403902624003624003a4000392619007100b64401c8045c01100c1010948400301400c50359030321308511100060f60042016004000543c003182029002050052400c500710385199a0b6034881001c0c2d1002a00194001940049020325850751401000100210308200502d043d415141c102c102c00c41c00316602c0c0628001198500800310543d060300d410070108200c0c0c2d42d641904520301c0000304120342c0e2462181ca40d514010a540c288000000342c040b0140f20000415181c6408004070796200404880e0f12480300c500031140340b541482414015100740c1c0002c240c8200e5001e80c42d0016140c001c100f40304500600501000d0303030340101c0c00b0150355040300000607140c020b070004903010381c1d00390403034100704401000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439056276 1250 439055026 439055047
    0x150c080f120702070b0a0c02120c0d0302010515010305070e100e06040923040b0a0908042d0e0610030209030a0807121d130c02010f0c0309030e0a0605031801090602 72
    0x72501c502003550981e0403850b245c4852003424014140104000f500d481140030050520088411503407603000b0440d54091000c500060050aa112080700103035150801d1011160340303010101d51111090030140b01a142210300141845400b24203e4407580504004081190103641c8200107410040d00c803640e00c544914469000d0712050207030307282d540c8003040740301107091707001c03003280e004d00c0d441a000c990390784646100b907001d448004001d4038201000c01c03000914580b00c0082500d006113140c4209102c143d081701c01842d01c0c0450303116103010200c100401000f99100c61580c0e100384602e084c016103a0007203030003080ca071004800c3c0c028400800003540700180810801141c0040e03609944981300e00440300500056020700c1c00700c40d50015000e4039007144264031a086109030360720303070700c00003c2041c90784100c00142c46104141c140407a50351043c890070305070f03c41d4008661101c00d40ea16070352540381950003417003844001d206114510f0300300ca815440c0340342034010300d121540107081951603210260 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439057526 1250 439056276 439056307
    0xe21010c020309091006080723070303091a04050d0c050a0203100603120203090109170a061b0905220c14031620060406050601050705060f15010801150c080f 69
    0x900703205011004c000ba2075112110030b40d50640b1450354400c41070b6150074006841006041600d11110503441402c2080340b40e40f440600f00e43c034002d941c041501c1805040c841484042529003a9200454a08210105200090030110040b81e850010602e01c160b0030414100420104025850300525010000245ea1604440d05407401b03500761042c28141e0240c181d95070311415501d240800c202010800c4041c1c14200706010090603402590960a00e03595103008544c04040c003849208443d226548000798402c1486024050076035904801013074070408202c1010380c42d200c0d409030544400e01c62401d41e1003181020820724a0580ca907460b42408107541a1656044281100180d60030610180d0203950020001c245600f4101511036500c944c1c86141c080c040090010741840010060100061710801685100d50741074115880c5508103260700e02c26002c620b414050400142e00c0050142401040d02c1c0c404041c541d080150141c0d030b90b85041840c6015080072600c40701404101d850070000004c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439058776 1250 439057526 439057537
    0x31b010e0c0315010e07050d021b060c070b010b0304230309010314010b2218091104050f13031701060305040308090d0e04050a0b0a120b06030d0e21010c0203 69
    0x209644041e8280c1040c10307500e8091140010521803a240100149214090065044000b42c9005407a1410111159050341d0003042c0043d40040142c00d040c84141c000d011841d00144100b403014600107442c3c40b003a8904506024588042078000045400c003c2d00d0301c2e0b00d900e1400380f1500c51090040382c444094498210010b1180402c0c02e1000140c4a03441e0b50a0f018140c3d002c49000c40c1c2040803101e420301100c21824465586000032000108940c2007180e03c061007884400760215201040d031030201484c10b0180740d03041c0118100301c00d100b416200743d19140d03400000e6824000d41c0414906040303c02030100c6090070f6021503440000314240e58550086480317107000b82c40f51126038032148400c0c1e41d2010141c114800103500912032035a0392a003504000d07004050080003040c002001d0f0002a030f45a0681e010030040c8407500c183c1020800910002540800101d01402d5a109400340180c4032951030080c4610034070301800c0c0489041030700032141c000d946194000304040300496502946d02d6000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439060026 1250 439058776 439058801
    0x27030c031106090612060f19080f030703050403120903021f110a020637030c0908070605030106052a0601260c0d020d06050f07111902060c031b01 64
    0x40c4503401072410032604443e15400301805803841c1080e00031aa4031086006401243c1c048400c0e440780b441ea42d542d2a2460410f07404005201e00ca0b0310b004c070071914010001c10b81c040250804d02c0f5003800302c1e4109040d201241e81004003903484814803035040b81c10704ca8a400c000d5100286820101242003640749450070703009252504180b40c1c00c000d14450b034441814030020740c080001c100c2100140d0000f007580c01050803062044681c58010110f0741c50002008001000207591242a1038103154040160401040300c040a005418240600200720388014060388050000000364031841e4111804404c07040c00041211207071006009843c0c5850304420303c2030081c3e5110000c049c610041c482c4003590364108041c001801401ca13600305100801c8580f0341d05aa20130158041ea001240f041d01803280305820325505010b0500d0000300281107001018000e4100e540303d18080c084d007140710200072400980444105844400510455265210310404c942c900090140c080d208000c054215120380c121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439061276 1250 439060026 439060043
    0x50f0f071a070b01030221010207060906050115120b0d02030a060603030305071103030f090309120105041502070503090405090705060414090105030c090406020901050d0504030c05100606090627030c03 88
    0x741074007503501e402000c0c1c001d80003580e1000100010303e0200501c1c19072240220000e02d60300843c0301c00324220780015005440b01e0303484500c0315040080c18801c0c2070140c100031807040000310031340d40010415281500f100268603a65400c03d1070642c1d904a0410031940e0082c11a4051101e502e460340c058540e510003200400e0034440400c02c45801040f10380303c8060750304011070543d5100d850a0610b081c02500c803940c80d01007040310b4801e03621904d20b5802c04a00600020846040c1490071200c0015240780140e500383c810b01c04100054030101c100c0d480101e0807a008074080e00c07000b000c1400d003903041c0c2c00383da800360001400080c54040740940f280310000444e0301d20156a61751081c5a110344910301c0b0395521080240001d030005405034094400e016041c506642000c1c1c91284c0300c0206d81060b00e054002c64540d4603005e0801a04014007044a4103840c0240700c080e191002c00380022040340911801c1c014444c80c81034540901c0b921030311000b85c95181c2d4403001d50307681c101840c114545000a441160 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439062526 1250 439061276 439061309
    0x120302370f030e0a0314040b0c06071706010c022e09080f12070308040c080712051006150f05130905040210051206040b0f030106031202011a0607020d050f0f07 70
    0x1d0181c4200d070003d403490405460361201c00c0da02195440d40d1243c00401c0d004050001040c0c8680700409049412103040003419541450030000c2c02ca1390154001241d4203034000c0400c0200c0e6030000ca0603410310f0781940c0a1751074001312007a4800c07011003a8904401501e65050040f0709540c015040b0b07048404440554040c4040c0c040320303076118107a586044c101c1420070800d05000910610313080d40e019004104810b002516a802d143c1062a1039100502a107001542e60080c894181300d9503c45682c8444100103240c030745082d0640211010031540705120085130446042e40c000d07011990950040d5000148031a00c0d42d5440300200401d50381a0301840382400401f0f00a0b0040044480e5004c1140326104d1036941d2408000251420000c0c0c01d4102c01d1110b588880c58909004000165105600d420b0100c2c005a4000b0b0840301940511040c078607480005030107c1c1c55000483e042e268041d0758900a070011820014034104120500c424103124840d860f0819100210f808010b0ba481105d2014085 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439063776 1250 439062526 439062557
    0x5090c070f051e07030206040605090105040b072906220b03061015180e060406030203060405010b091b04090f02120705130608190905070b1809060102010912030237 72
    0x1510b8900000b501300d80100400d0210a001e0806442f500d0014980903140c5500c03584e03940c1e46900008002c40d90302000201c040344284019110804002c0d00c0500440580f030100e00140c00742071340b0040b04140c455a4030142000b040240c120400c5264054101c4559003440300c5a9026201c1700d10840c22101d04014000403440e20642c0441d400200f074255540d9030758100700241134a894044c20803903006949040020050b10b050180603c40ca01800001582810303400034484108030051000540507029107603000c1c0c8150b0303203080c1ca041d95980c44000400042800c0944000c0c0700d80000580710741004400c000040707500c0401403640440c6105400740c06c0d030791250b05451140d000e1700c900c11310000461001050f0801584040c141138061000c5800d4242c0d03500000c6400c1d130284000780d100101801400c00a17041070010385802c0311084c80200074004107616030f0044461040d02000c2016000181250800b54820080c00710840c01600141d2081003503000c442c00120002d50308010410990f83e000070b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439065026 1250 439063776 439063783
    0x3e24040305010b06090d060c050d0c0206150105090d08030c160506150604030209040330150e04112205010e090d0c08033603120a06050a05090c070f051e 67
    0x994201504000421b0120398031000580307510f45108042000902081e0342d03841c0d25004601e0f01d035840b50050b29007410400d925520b1740c004d03d0202418070608000115650311821001000300f50030802e0140c83c3d80310600d0055582c45070001c40304e010300102012a040c400c0c04152580a0444074500140b00082c51080c080540a2440080c0d8003607034400c00200841c0c045c200c0c94040034042c50340b40900b062071651100c02d0b1482242c2c00843c0310354802030b4a00c1c00201540c0720f40500310b06035040100307241c569601d20340d0620590401c0d010b14880010079200c800c042207c2400c85440761790500c4590785500c05003661007030855410480340300307251a04a01c01d0081454241850304500036a14564900300110415034026021500c92a0021250100003011990800012516502450385e44443d401c20204e0b030f0340c0240c04241000c0c03900710108801c2d82ea4041403c11030b50141c40c140c81d04d90b0381c2814564035010383c510140c2014185603000e000c001000c1020030043d01c0002c10700305d0b03010012555959 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439066276 1250 439065026 439065037
    0x10c0f021920010e0a150906020a0c05010e060c030a02060406050a020a080a0e0705030a0c08070605040e0a11071203090c0f0614090409050304030308043e24040305010b06 75
    0x402080c0e114141402c0c1d80700e818003451040181840c00c05075042078045600031001e81e110450444510303007040d00640d840100c181c010034061006040401d039a0315401c000842510907141400110180130f40682c5403007060790300c100070200a0b80d46030f81250501944485c81110101c0d4400d01d0a00003500703c0c1e420388280c40c000300c00c83da9a88460b6440c003010400504180c201000c103032241c0c00c400200303980c0802c10040b0036446400544202442d15a000d0302e07010241c1c0004090080a001c2400003c014410055010040721030110309161404528502c5200c0c0c0c0c0da014000321202941c04548a4041d0002c20007117225401c800b801965891100c0c0445500e40150030000e03001da0240d0f80007035a0240544450980100b0000b80c41c4d156640d403a280d980264400c60105a01004100510112941181c0004602d408a441a1032035120f01080c0c01400864000d01641036001c4079083c1e1201034100c415100c407120040400026101d05d00c070b898129103c00c603480d6080800421043c20403105030354 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439067526 1250 439066276 439066283
    0x1d070818060402190807060203041508011208072f0307090204050607020904020411031e2d07020c1314010f0311060304151a041409100c11010c0f0219 66
    0x107261034aa082025020100ba0f032001c06242e81c01c1c0110f52404188181c00051180d60000d50782c90b49041941201000c200c2c128005101e40f03040100802d04c42490380d100040d80c0484203955540c1c00345000c91018111390038040c050740c3e00c501041c00410200c00d004910610807000c80e11020b60394050b6070140c0c440d130f011300e54000c58180440001814072804980d0000d10040002c19202d0501510700015001190405a01d03200703452040c421000c10306401d6007041c10b041c0544d606102103200c052060040070002e00741c1082e414001600d107442800007103041d0030000c20400c03181014039414005400e80790001c81103c1002c00c00010000a1501a1812a5031004050061001420400540390401042512580d86003078029480380103030304c00c94940cac0c054403950001c4071124074140802c8400014842400e050300300c1c240401d551000400c480078a0074201e01043c200741d40c0c201105c0e164402c03c850303000e540c01c20001c007200c2900305903500501030490f4219003000450440048c5000354464025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439068776 1250 439067526 439067533
    0x3031b0804033e01180b01180203090c0909150c030109061d060f2214060405040b040b090c0607081803060403050405040c0e13050106080c0f0306191d070818 69
    0x41c0f001e020650352003280403001c400001900c601900c0b092440c00ca85000c100c0c0c00d601ca680043c40040820403000398480c079100c2d0110b0079446c004c90310380e950310003a40d801840780c0741c01c0d400503030141000c000390003500003c1224a031036810200d10070b2085030030038000d041d902130800a0101c0d41c0e82c090300c008504102c82100b1996551030f80b805200d1410751075190180c01c09840c1c0740e4444039525110000150880000c03000031034015444000c050700a01500040c0305a0805d424040890011b01a680d00a60805201520b03038480c1b003440c0745061805901c654210401203200424003a0034000f615601e1480e600248404610004154580000300c070014081581844144030780d013090341c0144c0d403162490419044800300c0c800080c0e080000d150613940c9060321a00180601075100015580004801444a0520458001e03010a5000040036071740a225503000a44480d1402444540140a60840d00c10421119a600c02e0a100c048603110007095860b03010801080341101140322101d5070390041c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439070026 1250 439068776 439068857
    0x191d031c0c0b070207050102100204030203031b010b0319122d051e2701120e0c0d050a050c0607150e070312020d09051801060c03031b080403 62
    0x4403008841050500811040481007000194420031143c0106501c1e001005441d00d0f02000a1400313144054042400740140310410050700c0000c00e0790103c80d002e00740c20403407400c0300d819076005003161031600d641803058911041140707003080380003c03a681c007901c2001c4c00841c8440702520401c0040300d8080621119882542c8010100c0d20410080315461030030900c0c000340304029184240c04142200c00840001600c103400fa011041d084e2000c140b9030800a001c060003500180c0303034202c9800034508080e1a1004104070311400d0000386505d0000038a00e041e8144503051290341c5400d4514100c43c0d0707102c0c81014542e1841c004081d91019940680346d6000c00d0850162000034000f002c0844046214000c804030008004070741c8064502007942c014110107400e03e0008002d55002d905c0f040c000c960641c01c3c030041004800a0b181550403d003444d020002c114a8224018404a480d234031404000c552140c208035400712486010324080d64410140002524041e11040700959400c880d24956141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439071276 1250 439070026 439070053
    0x5040e0c0a0501050c0118150c0e030d030c030908071a130b060d050a020307060216050604050a0603020703051615050906100e06010c0b2e030f0f1502191d03 69
    0x6000d1644445c001007010b603015844100d0b4048061411508004403240612140d101c911401a24010178600100c5600420740840d48880e034160741e603820583c03240e020240c070b00c1c042d422240c80580c0c0310004035500d4040d030500c44200c4200c541024080c5410f070300410700b09201c0c29000c2d184150081a03008550700c880003044092410f101e0211164001e503000180540e50a0012400400701900a00407550400a880325001460b0708402d104060621091050391540c4101300b0699107a03080c0180e44072203505007521580201c41036040c041303003015802010002620481500d0982c8160144540e4868440701902d5690486e900f8000b80c01c150b40030001d0081100c141604100181003108070000291544040404210f6406640c03640444001c50995002545e0004690014010901903425540c41c0e00c002090040c01030008040020391300c09000c2400840f54801c03004c41400c40d40c0348851040c00100381e10303219449000c0b640070340c86000d5400c170305611900c000e44010041c2070390840350f14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439072526 1250 439071276 439071287
    0x501051908180607020a0b06031b190510050702090a1a090402040e030703030501030b090f07060809121209061014120a120801140d120f02100c030605040e0c0a0501 72
    0x50851403040d50310a00010b0400d414014540919120f40c0504554803039418844c9400c41d001c0c010398003a611468051100c04019506820029005c483d00c00d003041c150000440040c0c00750300003da001c0c0d008400ca6072226040001000814420340348401aa510b20010404651070b44241c0042207001a082486e00d1070610f100a0303100b44001c0c00011105203c2042900d0340e02303d680308030086983e840050041c0030011440d1580a14910b0003000440100548151161554800c48003401840d1340400e581c2c0000f070212055004070401660b89070b286202080c1c25050040d120448203004034404181d8040700807813042d0523200c40c1044640d40a0740f00302404507080020002148038020988008002180e070320034014940515a80d5000715410101600d07001b076441e1643d0391040140b0090200021004000007a0000349800c100c20711401c1124240d080c0704440802050310703441c0007400e082c01901644198207a49090350708005095170a90038030340c1e40c420242020340c40800c50104001561045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439073776 1250 439072526 439072531
    0xa0510030e070f08161a031e04080a080a0506061603051c02030103020108090c01020c0f0315100f14060301090902060c0a050604021305040c0509070302040f080102090a0501051908 79
    0x52400140c0301d00742001e1030342062501d400ca1100c10303039084400c0203c0d2808211760f01c03107412001c1c190340d105880d00c0c50031030940f40c00750650030861700c0100000c0d600c1a440e41800e0384250840c51010820304d058580120f456101010a0004c02d1164011400184c140c3c0f203124415040039106a103040e0440721110780041c000701c030031420020b00300243e4030340b9520031030010340800076a9005a103e50441c4005019010300410b100c54582c0412501c0290381e0b40050031092200055941d2500140c1ea100032074200800460040710a0890200303114403076005103e10b00482d82102d5030035403002d40b1100160240e104a0000c548d00c00e10500052042c4441c0358800c42000d031008210a203050240320000e42030070b00446040c1e50b20b4124104220030340c10700c9101c0310904400c0c1c03803040149240030742c0e881c0045c0c191400f030345009100450004081500a904680184c2555141030130040c1d5580300760342c080d50140706660f02071034070700c180080c0c5540210140c41052004683c0741c0042104480101d0329450700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439075026 1250 439073776 439073809
    0x121503031116030507080f0610090203041e0c0503120c060a0b0a0f0f03030806121c200a020a0b1c090819020607081b0909040c0e01060f120501050a05 66
    0x20400608030850105501200443c032840180180e00c1c0380c10401e1f4206988102c0c5142c4681014042094180030a02c000082e6400e071440140c903a00c03242088004211130303001e0806000a8031554805000c0350304003100849038200c1c11608482c14580000c0000e00442813100301d55403124000c108120b190360451a100c610141411b10003a03951414400e41a42d264011440244040d07424014180d100380c0d0a640030030143c0c1e05e0581584021142c0781c1d600071f140e046026140242030917545140c0301d08025491045c40b420321400e940d8081c0c41081e1102a4140101d10540a102c40025420f15400680700c602c07200306212001e44403041c1c00300006d4280f198044669090410468800c04c0300310924a4030b80c3d01d95802400245800ca001402c41800a41205081621031041c0344c12129442e0846000b43c40c21340c7c82c40416212403503c3c02d2030b00100d03004454034078005000818841d603c1171422141741690f81e1905480101b81c000750b82100d0b000c1c00b03910b4200154080c14012403c24001d82d5800c440c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439076276 1250 439075026 439075033
    0xf040b011a0f0d0921020f0d050406080907030c170f01050402030d0f0e030a060606020607030b060a0c030e0d121806080402121c02030901030e03040b030f090a05031602011215030311 80
    0x11165070381c01c072017000c6000c1d018400010301c034001800e5904029440c2c0315500c080050100480240d40980180194420b050412400800048956005212280c01507500040041d40e10340c64101c120800360f02e00001c58618412642001c1003004140151070140e40c02501510321032540fa441202c001000c00f0850043c8071400b41c100c075031510100715116455001d40720000f402400d19000074108140503110314101400e00c07048002aa440d20b048072003000c0c042c20001040d500a20302a01d080850038000c0354842018528101800389484452060510303d507140e039001c0e182e0043c001c469008500800e40014901c0000400504200c01100d22030011807044031040070300e500543d480b800c1491050b0b8016040840d0b096840c0d41c25000d14109541e014014600789424140014901d0100030076182c0d40c0d904000108106480c01d12002225a41003070542e90b413007211101070700e0072140c44d62040b400518940000181140144a4560b940d90080442961603207151030498003103d80d580c2c480703183d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439077526 1250 439076276 439076291
    0xf03060d0506040f17070b0c09040f02130f0b04031104021c02030907030b010503010212061003090506040f03080a0605060712111e07330909050f040b011a0f0d 70
    0x501c01c000652040d032150b41c5404002185152080e80d4410490f48858140010b1140b00c00051508208591200340850110740b952109000540903120345615601003601c001803609a16031a1100002a0b41a088400c00c00a69480082c0001e00c107610014022480300c0c400c00c1514035240d0018132907031808400c041c501522030340d141c60883c0e00a03954007910ba80441010000c001724014032a00401c8110021418410f23211104055107000401907441110074062216031030780203034004580f41f0b812508031030700340c03500d40340c0141c0b4006049816404201c000c4000746809420b0f00032a002d640014002c1c5044c640c05540d80700815a00b45d0804003400180f01c00310448450401440d802c079101c861701c10310051602001e20b400c1894503003290050308240307000b040d1815130596030514036404401041c1011104468100c800200320740013040040d0400d02406101184243c41c94003680c0a914003203000d036660611100348481c8421204903140c418081441031380d80180c00380203000380140000c900c41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439078776 1250 439077526 439077533
    0x307030f06080c01080a05090a02400506100914130f0b0906030304060e1012020a090501020f0f070b07080f071415012402101104290f03060d 62
    0x240c0c29a00140d156a110f071011602c42e40c1d200d25900d0304a511102c0802450614140090f04c8400030b00c8081d0280b00c480316150070710003402e02c50b030001c034800940104443c20384107003504492040340119480c0f00e0800380890070610340b807046a11032000a88800240034503146d0354081030641202101d5100d01020050440039141e03001d4640700c05e405002c001541d54100c002c100c02d0000c090902d0b4002e600a010a0150035000f14512031202c8003110b00c040d606801c2e05040f1100e90141d1720600c8001d00109600e912a60005c40e12000c0d54401d800b50b40120140e84201d5668500c81000f00107a644021810405103484100408016005e556101c1c6094900000321413070f540502c008503002c8914a00302c40001c14207202e04510740d44002c00342c000e40d516040a0040e1400e1220090086030502c1034802c40041c02044003510314540c401003401850340c40c1c1c09044403a01306108240e603141c1c0350258840b40c55a50b029502c0d8007007820303c0c280e003400540143d6024603080281196044102d8142e01c4012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439080026 1250 439078776 439078781
    0x3030f051905210606070201050f0f040f05090a0507021002030a142412060105010e062b06080d0c060c020f0307060905191104051b040605030103050f0d090b0307030f 73
    0x10310788685a80f4801c8042051400c1162429001ca101c0520180709a07555201304603040d043c2c09103440c545610000402110900c509103120101200c0010002a4207810300300035002c0703520440b2480c0c5079a5403103000c4800d8076000c54924005030046902441528055800785d1707000b990384200001d800c0c9039034401b0001c42c907050b0355407114401d600030755500c43ca441d82d0b80f0140c0244156101070900d00c074400010f0340e505041c000c85040c4005000007a400344c40d190252008504030046d103451a904046040c0d2000da007c83c6400303202402e00d07038045003844002800c0d54040595588440f00200c05841c2c44008260f020b00150031409008812103140d0420800b4151443c084e94001031503925501e881482c0122f4070200989400d50300c0800008031f01d02c2c4903107009001066038089103556640f404a040101001440c40d04403601080104200c0c2c0c3c0040074505980c400c1088640e51030721301e0382403507030f40c0c0341070b4405000280d000c0c0c806e00c217441c4ca0307602030b5070000294107000c15200502803c4005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439081276 1250 439080026 439080067
    0x1908031303090b12100b070b0403050702040f050109090b16091412010c0504150e0603010603090c0f17060603060103051e2b081e060d050307080c2401060903030f05 72
    0x40c0740a81c0103000e034850420174002c3c010440000d20b030b03260400c695140f184041e002400501800400710302a010b540741e0390025020f01e00503000c200072540c0c4034480d1600400c40340c070040da40901410300044072009480004030b039025994079001d40942c030b8980c0422600c0d608521080c0c00071000010340c601107100340203200f01c05034581c86454a59081413070016a11007203041110401c4045e8100c0c14907a1500801c5a043d620b00e450081540180750030f000130f00000d6944056440b07140b4080c00a0f9001554020003000700007507050340d07100c0e00d40a0405035592400e020240594010101e01d4180400d641c540e0351a0f0312030001a101c41d020201126010031024040a86402c21442e501855580d40f1145090307100700e0142ca43d244540003140000c801c2c540040c4400d0141003600800c800307100040003130794403490b07112032a541e40b05030101821f80c8450030b01e130441d0000c00c03420803901090080f035210b09058640d01e68071000507510b1501d0868041410003601024800104401400945155034090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439082526 1250 439081276 439081297
    0x111070e01170303010609260d0306060905062503020f12031e1315060515090307061103030604021b060a1a01020c130506030c0d050f1908031303090b 66
    0x900d580741031000303924550400c01c510040c1d04100014820f15402c80000001e688010715514078030824903c040c0186c5503809a6a11984a81000211140e84c5500b2440544a82c0d949078a2401c1d5968140b140900071640c011051109a110303040e40a9062000c4564a60007403044038418489168400d0815400c0803015827407203c000b081002c5a424010154881104484020050300d0302850000308682c1554000301046107040140400101c01e80248004d08001072540e901c40c154262480e0040d403107100294001e0140712400100382e40150b9401d0070300d04500380507500d196901e01c100402540510350134258030598621a0402c01e1041289901c03d000c04d00b800070b0605400b01c0741e81f4602d00707041400c0741154441d95810045071190444000001c0b00000046016146c040006e400c1611a2045c1070308140054806810f0090000d6020140301c511425504c0d1810030014400d5000d0380880c000d40007110420209103c1c400301c4410b58a030320300a24007545466126130032802d16178031070070102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439083776 1250 439082526 439082549
    0x5100c02090a051b07020f010c02030f01181703100b0309010204030804061d0f0a030311010b06210609060a0b0a0309051b150403030c120201020f1b0c190b09011107 72
    0x40348501c0c4ca81c0c08114800c9624100728100b20b410350000718800c0701035081c641000320010010341191410000c200d08050028001d001d000d40340d8555044074008000b050321070b8292091011208400401200c0c000d4032210f549030700c62403c008070003034140d1000d0022a8507660800000000c5000d04c8003030000b41c05030b03070380d91110811086407e00401074000c0d91540f1400e10200312600e207580b20300c035003011a94035081c80b80c1002c041c4080107004000c0418096040f10303002520042201070318004110100d00c03080d80740c102c1c1c0c071998203000360580211081900f003128808117200060301c42004d04460030702c61502007005800e50b0364075418a0820030340c40d500421401614445890036068410310b08183c42408da090a00e1501c2c010900b0100240203007200d4800d248074400c0c0351007034045410f101c85145855650340d085035800480e006041e144104a4080c1a07049013103860b04c9860505c1101d00230040c0c1500b2810401540d00e9544001552030500c00140921410740d5012b1002c04002c14012004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439085026 1250 439083776 439083781
    0x40f0b07021f021023010e0709090e0303180f0d1e021513031707020607091203120f090614060a0812031f080a051c090f05100c02090a05 60
    0x500030040340c1c9816058441e000182410340e0b565000445030040030424802054903880e0041d0f60324032401101c00091016100e00000c1a0078444811f82406038045a03142080696903c514004440b5a503410050300d0b00101701044103071035080340d004c01c0550300b402a01c098410000303e0618020506030340c00046248100149414443d600da5038801110070b0018117a2000581d030100c1031008010184070348254000340d0380c0107040c0304419101a0704c0030850310713230501c3c03d0a51010356152001c5034039200085000c10040380c0342d00c804000c4421268592185051079004111179005401d030f01d06040b40745540e0301d0310000401c3c2c850180c4440c07444400e444100320f007801814030146c01300503003002d80c040d8000c810301c6462810301c204580c3c1c0311031a82000c0d1000601e040300104284d1181c3d10510161080c44484814018085010700d409098114507514150ba0508191452100c920070140400105981049a420509044500c86c00145400d643c600600d500040301408243c40080c5202c4c1d0b60001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439086276 1250 439085026 439085029
    0x212040c0f0501080a0f1b0305090606150a030504060b042a0201091e0812040b160f02071403280309060c08071103011407020a1e0803010e0c040f0b0702 67
    0x103100d001e00301d692540c01d860307418500040c0c40000b0181c1510030741035032004005140341840c0d00aa01d500b91070714181090090041d0006c014007270689010400c3d000e14000b0070030500c0c020080d0a0150f03003500405040008500c01580181030040050326001d44401d1008919034480c0704203020740513080301c110500c41310416280c9001c00007942d0301c410b6a2521040c00301090240f11086890700c854000b801400c0b900b071070951041e016440008145102c01800d200c03c0012492209101f8801220b4415802c2d40030741c0700300d4802c644065010056048510b043c07050302c001f5240c0c2c240c25600a0121b4181d22901c0b031200c0ca04c0c280109003c1600300d42d11303606c90101580310000c50700400123441c2000701280e082e01c803000d80b03214564008009171103002e416503403900c0a400100300d9600d01d4009210070325001034080d4840c00380100444681280340308d00000c1c06001424103100507000306069045030b09024540000d150042d028052600302407200048400100c43e000029064a0307200300c2d20380f41a4070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439087526 1250 439086276 439086293
    0x6050c070b011502032505010c091403060f180f0d08070206010906150c06090c1403010c050f0301031704081606030605100c06021804020304110108060108090a0b1009021204 76
    0x200310310180400c400c120481c3c80d80c0002501d000d2401074912000550729282901000c51100b48000c0495007000e0b800014950001003a4040b03079a24110540c0d440c0800b0109030b1160004c40c0e4406403001e010b000304c0c0010700c2c01c0b62040c0100c840c00003100d031448200b0108a00d81800c0c0c60306000090300c40010400d10310b5042c41034070b005000044081c450349040a0204c8082184c0780c07051410001015000d000748002a005044860b4000c0900c1c0c4000380c403030303d8040103100d00742c0c02c1034000e6080c00506550b16100d0422100030380b403210702e0242581d08541c2c61006502c41c95801e44140c0c441408045500c08092003c20292200d0f0040344526503d08900a025101140c0c0018480c40010b810308915940001d18503580d00e5000c2c00050362101d0007070340d50210030b0320300c15102d1300720b031011040008201058080c0c0c03030910000d8030740724400d40d181001100da00804981103407ca40040c148000003640b40042241c0000416030700c4e0750070580720701592049800015040e00030b040040c007440306002400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439088776 1250 439087526 439087529
    0x30a050612060705070201080403090e07030902030d0e2101061d0603070f08300c010e100203010f0b070816050a0c051203092b030c0b0c0a080c03060301060306050c070b01 75
    0x10405002c2c0d0749000306001e0300c18060900081d050100aa0003e010036114480303ca0107000c8051081c0c5e20b038142010000d0080c84d0b00e51040380284212442036400038052401d99402d49402131000380018100d216281c502064040a00301640d2a0a40800c0400c440c1c1c008004000401d1110300c0d00d440c004081500d81030a980c0103440b60802c095060182110100c0e1740070328401c01e01041a9080088150b140e40342011000700c40308100007095000003c4010f405c8491250700d544200c4480c60b004080346030491200703103e140a551000f010410a074101d04000c2c01e1000c2c00ba00c1c08905100c4200820381c1d035030014a404030746c0c5410a8445d0307410031020f00c0b0088054001501d115a001d044400c205a0301e00c5003540161042c181a00c52605510040782801000c0ca00a042108040300c2c9107009018043c0199044480740000700000b140c46515405462005140d50745018a03a00c9012400320154130140080d038055481309d5011010888e14010240a080002000756482c1d507a400c103e015040c1c107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439090026 1250 439088776 439088809
    0x31701050d02130c0e030d0201020c01241502150114030f0c0f0d080d0f0203090f011404060c120e0c121c140d050c0702040c0309032012030a0506 64
    0x1e6400c60090784030580c40b01110031480400140907070740800b003550b40031503940c915541841081580c0e1a01740d41900030b48408103410f0001d1000c90b1541c0c07084100c40c0d2526100c01900c0c2c0c0b800f0010004110521010003c01c07a260058402505000401114a2000b600295544080354210079a181000c0064240e41c40c540c1c0041c122049102c00002c6016101c001039920132803d50404006000070542214140c00041c20104a084182d211400103504211000c8600c0d009525a4490110701805002c4940704925004060303645e40f81d403807600401500e4150400c0002080080700302d01e04501c80d150201d0410300c01032914117030200c108040c0499003100081e07240c00c04441ca8591894000d011103100d82541010901d4910101000300705008828001c450107060006201c0b003d0700003001404520300940c2e0500950322042d4041e803d8940801c001400500b01c850f000c0004140c288001c07845068400035900030000c9052540c5c2e1f80d80041e911251059070381e0051284618042c0707840b00100d5075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439091276 1250 439090026 439090039
    0x2010906020c130507020c190e070504060f030c03020705010e0f07050a0b0313030c08190e0a030b0a0e0c030706090905010504051009090c12030206091002160f0206090d03170105 78
    0x182c00071075050741c5510180080c641c4c40e14045035400f0f000f88090054410f02400e000040d6030142810740101d002c51017842980c648080108900d54070480c01c031010f850003501c410200c820001c0040700105920701644040503401d00058000920038022180e011002000a102c00340054501c1d508021843c2c2c80305108500c8410b0800a504842e016250310405c55003c44400a201b82800c1e66a80d50000005045007000031b10b000050080c7d0000000190f40d681d240e020300a00c000a00c00e962031103001c00b80142c2c03090b50000f08102000d0f00300f281c1d03400032a0161440c820421000c82e103043d03070942180d8003003581c45d5018003440f905441540d0040c0f900b118180041d04001039000403c40c0700707000341b40c416600c4041820600a405101500070806070003a58664109400e0094844905442d0700740680503036021000b440140307000384c8d5040303240d0001d0741001801a94a49401110403002243c02090034050741d0360319503c00c645980024000c1e220201c0c0458400d03003005a258050700610b100b0007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439092526 1250 439091276 439091293
    0x1140a090b07020f0c1c17030f090a030c020904020a0b1b210412030e0d081908060a0501051c020c0a0213021e030a0e0a21080408120709090207050a0201090602 70
    0x1d0000505e000f05000940707803080c501c1e900c0d55441088502c150809890440180d0f0980500481c0a00462040703000c88044455625034109060700c0d070b948a000980024121401c40026152452007d5042840101582c1800ea80c5484001c1660403a51102c0d0b441c0c10f50910b403401c001d00038004003070110074104500702c1070300d00c0c0010500103000d1805010ba445151480d903404040c090904440144401802045a0f01d032030304d8800078a6100007591680281c005040f5280c2c01d002e01103190007001d008015950007402d1500442d0380350800b141c0b8205071800c0b140381400a541d684014211001100080c1020888a0060088461032510313001011791040262440c00d455402c0070b200c103c035070043d240d581e1b074565072041d00c06010710100804d624001c070740c03440003085480310442700e18246102c0303d0281000031740c1d01030381c050340c080300e010b05040001c20076a42c194440441c240d07804080782c2040a0869200c08802c4201d07002400c1c1210b0b2540020500750540d03130000b00c034038010300e0356200824900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439093776 1250 439092526 439092553
    0x50c0a110a0b0715110412080304021c050d2a060c02070b0307080114010c02090702010b01081e150402040f06020703032003071106090d03120507082701140a090b0702 73
    0x801d80c210310142a1517848600b94a02040e920031a8000c18030003601340403003a12410984e82075413040e2070481c4140900610000d680c050300d8600f071040f941240c050800c2544200041d00c08600d039000c40482c80840554807141c000001100e0881c007800760500003400806404040d2414090350000e0440260038810895810703400105541968071080b000f0511044140042c1c1ea003005c00c05000703502c040704104000d07610382d056000c0c4040c107609070398540181d00c0d0803848500c5100f00e0160039000c65400310001e490542c1468000d02c030369801401c0185031a540780450313550302c40c00d82c1000c2c0068005120400c24143d0100341c0b01c40220700c42c400601e03901000c100c9039680e80b242c1d8100170040b03100003203c0240340c1d032030a091301c04c2e00d980681151014140ca1400401c600841921020701a02d0840498125403158100903c6500d60095001c440740c000b481000c183c2d24250342c0c1c42001c0d904c455100020f4615640344030700425043c6008200c0b08110b1400e03403245c43c0010b181c0070465110b1500d01d51131 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439095026 1250 439093776 439093793
    0x100b070803041e1214040320040b040e0307020d0c05040615080c0301061b0c0b030109020a11010203060102030412150f09030206060904050d2609030a080108010b01120b01050c0a110a0b07 82
    0x454640c20094490f804584051841340a558006170070148600d00342342e00c00012070158291124125030400c000c2c402d00c41000200c40040d120100190300c10300500005041024002107428055046070002541d180001404e070b640700c0d00109030070405414005070568100c0310b920307001080c1c80c00090456040500003040d909030010107404180d101501070060204002506000d000c00c010550b6407076031180e0060020703600c0340303202000182c82850050b45041c01031080c0c0340100b03416405585080d15258424003081d0380700b4800d0b00d24a40f01c200c41060204940314401941d14010804540954942800384c00d110300101030310b01441c00d2030b0401001440101b4624841c05907418004540d081036001040011000f41a4952451389903040c048402e03000409090009241d545c0c140181e0b803224041c03403e9175808640c1d603020503d81c0c991b89102c0c80d031980082c6986141890214141f00100004a2805a110206a610020b903c0c004105401d210301e8240203490b2030444640703070200b2036982840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439096276 1250 439095026 439095053
    0xe01061805091b060909010e0105010216030506060f0310050f010f081f020a17090a05010507110c1e0907230903060c13080604050303151507020405100b070803041e 72
    0x1101601907541c0c40c113640c070700098410150700035002c007110351b07164200410380c900c082c02182c0c054070034052074180c0191021601000c1ea41c0c130001900f400d071502c005008286010304980c41d45401840f140c48695800d6105052142d09000000d24081d41b41c14054114032017541c1004105410111401000c40180201520712465034100107958000032602143c07130b4001c4401009441840c03a042c400250000200001c071140110b008010303075203c1c03000907078a1030050141e50303900740c02401c40b181c0c17546440445020603c3e000300f50b8480c0525442c000808070803007290300c01c020519101c0071b50428022507100b9a12207070001d020a15200c000000a07550f000700500e9005c01d0b2030001440c01d018810300d90004000d0070100c08039030040c04c0915050751a5041155940300c107541d20051007009241100d80100126041030055141403015000d1101402e17008100800d160050306c03000504505800c000d140103400351881e203450b41000d140032034005c40e10030aa02443c0742104464000f0401c00c100084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439097526 1250 439096276 439096303
    0x40605090f040303321f030b13060f091a0912030a1103090f161202012708030d050901090209010b030a0e0a080703030b03070f090b0d060e0106180509 66
    0x1199803030f0314007200500382c48401642140c5400c90402c101d102d504505030142075042441210a0b691002400000c42101004065004014000b000450440030b00c44c0d400280d101000f89131352020351110029681201c180c400015920401c040c1032100c00c1c80c070b03803091003c41c00314402d03142010009a560380d203241d600610150b1000000c61560074a56210314118602548000c0e00ca1070000c20071034590251201c0c0c1541070082420074103502c01a01c00360300030356049a03c070240301030081d001140d900d6a903030314a410500780084d6803403041d140d46683c40024200d1500440d684c1341c1790a08801a50405441d05580c0da050640e260010780d00c0300c01d1241510b0b25014515220703510350004001800c015222200f06004100401042c0000c90000781b8125009840500c01160741c3c0091540e544804d02c140500324003074a41c14015001c6036003005603441c43c001c00c0c400104140c1c0c0c8400007281c6001040c044503039550803040003041603166280750600b0755440c080001c0d151030108075889128001150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439098776 1250 439097526 439097551
    0x7030525110a030203130e09210c1c02150108060a181e0c080c010806060c0f030408060a050108030f041802040b030a05010303080c090f1e031f0b04060509 68
    0x1050648607800c0384480c5101101228140c9119040c0a03441c0d9003e2418900317489144440030816031111845c031802800c0d01801041900001c0c10018007055485100c0105103108100c2e199030504100103040010012304103940762410000c0002e407034030800740384412014140e80c00411083c00003113001d5a0207c0c8940000c5640103c0d56800010241001c0d0000c0401c04107043c02d00080d00000c00005140b841049c000c101e40c0d4440100d10740c1d2342c482d0844180001c8041c000507104c0d09050014002c136a07044400c0f80c014010540c500ba0664100350001040e0f5840f031001c10003001a03e020381401800444050351400d00b03562090700080c420342c024200c802143d06840e111240059040350700a240300750041f6180e04041e060030004d00802c2c80140c0000d200840415501101c060844180010040c4051802c683c55018484d228034540d8014814031540300009015441c180425010031021458401110050107100b10480e41c01c010765501503482c05d030082c495034403480603681d041150624503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439100026 1250 439098776 439098841
    0x105010807020a050a020918120d0b010309121101061d04051603030f0f0203040f030302150105010f0507060f0e03131d07080f060a03050115050310090c0b070f0821070305 75
    0x100c0c4041520103541001c0c0e10527120708100b0324500102402c454107600c00140007101201c4011000e507000084054100380c860101c51444a00404400e44a0b0020100104845944055040640e04a02c0b10174600c40e031102c0402040160500151040c07a2940359083c240300c2c11500e004000c481882c801400f40811020829080b0740200140d9004140d9006008402d5889280003510b4250320310310558441c000c04004106d540c05001d85039076407003896403098104089925801d01403e0304540d5021102c1e0b8850185010000910081040031407849015049034581000e0f19006450907281e44030081010041c4402c45511000264104030486040038489e2070346e00c0040d81c07441440e4801405580391100c09890204848a100200c50341281580c404002c441458000d9a80e5103600400560031680d00b40801c41080002d08a04d0707002d0f524003940e1240d6035481d00e03200d0b801198000f40c038006244041540814010300c103a403000e03040c0341c140a141000c0610008003000034200e0402ca5115040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 439101276 1250 439100026 439100041
    0x20411070318030b061009030507030f1b06080703090807080307030b09010b07052a280509011d04031404080303010302040509031204170d1109031603150c03230105010807020a050a0209 81
    0x1409009235401c801952019640ca1410f000402600e440480325007181d41130038090410303001003007000c4806031b4944280903a41c200c0304500410324240e084403084000c0c0b1141000c40c00c00ca000e18421412500d000400e85503410412998403030503400b010300403100300b102100003500450480c003a220340a1a0040401d01e1302c0f04688480c1404c10f07865003051001d0307101c0d20001c0d002c00c040c07034413150000400c5e049584c588092040d410002d0040a45c51500c0c005484045181c0012840c3e00034000e1070211080041380700c2c111010751041c0d000e898203500100040c400d51800b48203281c0c004149000a41c0744c81c918034500d59100300000c1010b0031a80b030165829207955000c104840f0011002541005511641d41c481d034000d400c000300c0c0390300911030000c260440c0e41801c0d07054000e0729006850440408045803000000c2e000c206400d00415444d400e903502c982e503020441e0a80c280d01038030144683e605000c0010038040c3d0081203034086511050001c000b04d80e0102d0502c10041c0c0644100f500c80cae5074403e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 439102526 1250 439101276 439101287
    0x6120a17091807030506040b030d02060f041109010b1c02090f0d05030c010e071401020a080f03060103060302220c05090a0b0f0f130807060201060f050d0609020411070318030b0610 79
    0x1502c0c0591048100c04104101e40d050b8000c91003180111010407120f440b440516a40b100408041d40242e401302012030b00c2c61142c40304490348180308c3c0d45a040c1000d182808201c41c50820307423014903a03202c00328050412414074030142000b01405003045007409103030f200290703036002c500100501406107000d10034127201052084440300c1e42810000c1c00380c045e01c81070260703a803e414841c03102190080e614841c590362001c075151100f990040c05990a000052030540d015a0002d0466810b041c0c2e02d140010040e11840b203100042210142031401090010440c14152080d03142c40d01c0c1001401c1018220f10703590aa08030081d900c00201040e2609011004844c40d441410742414800d44c010a1161010810000700300540e0f100f030065611071992a0016030070707030703400e40a01d84030700c03a180c00103201c541825110000c405000c0c5c0c00102c1e546001d03802140854842605112181000086600c14541c0242ca0144070004595a40301c966203148c840040117440a0540742c89280d0300071541810343e00c41d6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 439103776 1250 439102526 439102549
    0x60a061521060506041403120315060c160b0406030506031c030908090409060902210a030f17092802130203060d0803010b1801030504110f01180e06120a1709 69
    0xe04415aa607031911b202503200d414016000d4840d11030321f0b0320320048000a100b900e00443e036402e4100450b0f20150200700d203e07045040c61441d03520420050302c6072038012008c81c0000b4040004071075515414980020203982000305070900039405032121807144094450028142490381c40d0000b04240e9034030b04125107100d240d02c0d8591290034006004103002a0b9030105940c10305c01c0300c0d083c143d0800c0301051001c02010b600c51113400c2d0003180d54180800d011340c4150342100c01c00c1c40d000840109119841400b0241624640b03000c0c0d2040c4003412090a0100c0d000c220303c4803449051019210b075900180c280440e021aa4a13a02d4020002ca01030341c40358948034100701e82c410012902e039a140c82460301c1c60f400010401007051103517044203050354085d1052070302851300100941a048034200034006081c5441d80f8150401c003c0040110079002c0340b15200000c0e00902010342160304004040062580459050320741d00e411203d042c0000956078105400c90020240400d81c844a0030000240107800a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 439105026 1250 439103776 439103779
    0x30c0f032003041203150f03110607080d0b0910082109030706032306100807050f04060908070503070b0d05060105040909061d06070c0b0408090d05060a0615210605 72
    0x402407004000b001c5802c14044c0d0a150350402215600d60f01d4801021280e100e50b1000440c2d40c8414804607aaa41800041030340107400d49103060003581c1c8880d403d500807000107511541e42c9449104a140900b802074000303220b5400c441c0c0c106d003005c400c00d0700c1e08400701004000a0500046024185010069502d100302c002c0c1680e1031190b40f000003402034110807450f403551340000c00e4140d04060048050701d0141c40c0150450310b811402040941c5c44083c041c1090f0700344401808120901c0b1a814010000340160303580c1c1d112443e2400691501d00046504007500c2508a0b1500340151110380301512000300c804070010440d600d9620068407580b24036081407041a05007900c54040c406d898000510f101901160001d20464103005551903200545143d1300280d00300403071341e000c61003140701140c110b0f0040c031443c1d01d0048000d00061415032080e000b01c0b6240c001d0810042d1010091148000908114000c44402888004024114050040200e040d420340403041807072001035901c100d018010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 439106276 1250 439105026 439105091
    0x807051b060f131203050307080916140103140a09020112020a2c0409030504150e091303120501031110032a11011406040b03011413050a0503040608070f030c0f03 71
    0x220f03800c00911035401108c2c81801300d91308030301081c0b0081c4001800d000c00d5100d010018a41c900344940e560381c0880407600e041c10940c44848850915003a1820b49000762a4030000140108040c4009400240002128881e1a1061000441068110076801d24656005160300c45489650540460b40300399403078150781291815030100d04140e040001842525405103550000c003910f42d8040310464428040d030798004100c070002c00e82d00c00c07254959524841c4a030420100b1030851025080448070241d2041c3e40c0300322180c2349028541010f400320031020403140b400307000f0155502e0405203040e0b200440d1414400c205400b002c0407510030030002001034182c5000f80b02e4109804681c00f100d5509030f030054484c0380b4091a1043c2c903d8144100d850207003000068150700d903504103150076082c03800c84054813640070304840c110004e5014002000070f000303203480f0a01c144c01e084400400c2490310300003810515151415100a640d040840715480c90124900494186c1c3c554055803000078100403219500103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 439107526 1250 439106276 439106309
    0x807050f011503032703080a0309140102090a1e0b1c0507020f0c101b050a120906200c13020412050f0f011404060f06030f0807051b060f13 61
    0x210b00003440d00c1140e0081c1ea41211032007003c0070340c00451460881c5241c1600b000c0c40204001458000a44113000080c100060b0150150700c0343c41400c158080c4600c4503941c00100320500703140040e5140042c016205501c40316140c1c0d01e2162400308214081c3e5408001d01141d0440001c07c190010315034010b01e00002d201c14244030101035078444403d0440d080900422500b03821600301500c000c0c6030b02d01e80f6901c69441189940700100000c42d8040160307000e0107290384000102c1c0382041c480002c162641d640d104a549001802800600c83c1200c4d4940061a0380f4900210500080c40b1520a04200d580c140e60f4815849000020301c51136000c00c07401094030480000b80040841d469116071180c10545541010241480d0b00729074145001d19100c40e05d40e8007141c04200d081d800702e1119940b24400054407912a15400c10b0516002d1089a05030000a00d490800505001305c040001d0242c0116000c1c0040c000040c0c56401041642c821039000441e254890300003104250000300f054105521445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439108776 1250 439107526 439107551
    0x60d0b03010228200705190302060307090801050109110a0503100e2d06182d0103020f120303070e0a051c0c0f030201050f0a20011a060301050d0807050f01 68
    0xd0761100340d0000300d01201044c441e005101d821804081d82ca81018000c003c1c00c050422100034001c011400c103800000802200507190500198010910f40d00d86030181f501d0040c030107081d00d105030414034800e410406900703507101640e41501c0c00000346040150326503030b81e92010046400c0b940d101c081c2400154080c0481c0d4811102c00c41060b00340401103010030f0342d00d074100c214001c005035001c5400c5240d007144820701c40100489550410f0070014161035a0080c800c800800020b2000c00501c1c41082000420031490100f03411400d07481c0a43e265039110011141140d201e000081c60b0038240b04940c0444d8009030703107250240020b444010b1401401e103c4403800c00c14012000801156120300c0d2013400b288401e2052180d40c100d0342d05a45451518101070704100007078021020400500107001c6010080380826a1000360907042440005001124a140c4401c00d02a40d8162030140030b04000600c443d8031000503c070740140d007007030307602c0c0ea50091454603a2515031041191181c55182113501c20b100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 439110026 1250 439108776 439108837
    0x306010f0608310b01081015060f110307050d0801090e0616090e090109030e0303070519031b26041a16020a121b0e070e041d100c0e060d0b030102 64
    0x180c1d4806011a8214241c00d21f104085030003040108469000c0c5500400c03400f8031941c8140d120003000c0c03414000e03010041801d0f92035a0000c080071907454100c80003501c1070300e07804802d51f401005213000c113010005014200d42e80fa0603014000d003a80803400c60b641040140200c0500d4001c01c1c41408000e090300c0c01091260080401040440000c0d0000d540c8420611b40001aa509250041e018003e980d02482e0302c50301c500f005203000c4003071102c0201420070105004190340040350262030884401410030031104120360284030922000f4000b40014030899218820f8075181c031001501c1182d60301021082000b0341c1c420074900030f600641450300442c4c1d1180c0c00c0c9900c0e454a11652580c882c4d01062400b1000902c206e0050922a0780711000141c40701e4412406618a104064000100c14106020720002803031321900002807507103d024044681661840b403281d4080e01403610814501c02c01000030014400e06085c0c2c5140d0740c4801109040760307420b6040782e07035805000300b824050001107032034000c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 439111276 1250 439110026 439110029
    0x51518160504050307090b011403040302060f0a050115050f0c0102041e0b0f091c060608030c1005040b01180b0a0321030b01091a04080a05010504020306010f0608310b01 74
    0x485010030310304035034101e00507002d8a06998009000e403401d5420026518001e10140c000c150400c010090b0b180342568040340214011030103a4040c0c0a1480e003101c2240ca400c5000d889110541e1500c0010802c448001c0440272803104503182c0181d40d20f81078900b643c07113405104408491948000380004498211401d02d1001c01d00c00701d012110603a40303041d00d0581d40100440d0740c11001d002c0048030302c240f0704102c041560076a240c1c81ca0300e01d0708071a292501160741a80000300b0540c0000f4041450709800c22140b180114108000e112510342552141036040701840b59120581690002c5030300110940c004807010a03014046841e91546c80c00e1000e68030640165000260665611861410307100740151600c2280c11b03115100f0407481c08041e0000c0001100340c0c44240c80c024000840d9a100c18006803021900030400440c8034101030041508103441a403101c0da05080304c0804216454001154652041c80c0ca03500000000107d03c01c4100b01110b200400071002e1103020100c01c00412980860 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 439112526 1250 439111276 439111291
    0x20a0e091312050f040b071a07020607030b0d21020a0f05030d0509160b1e0301121a01180507140a02010606020c03010905030d0b01140d14160c0303051518 68
    0x2c8040c008007042d1024440c40551441d02c0c841040103004488a8a000b000d07020310901c00c552500290046440c20800140c40300c8005800c1b8000380624142d150050b8540d8280c12220f50914120301c0d901d6420811052081c0b400340d070007421000c60218020302c801c42d101608205a21000d82891604c203450764440750901c4502c5281a001c07030140e80000800c840c4804601c6401440c040c01c040c040c42042d04a04620b400b119800c8102c801c540800d0300185d4020a00e40340008030403400c07485d15200108070b40e07100641c18040c00004100d00800d40c200c03016010441c2600180030740f038440d0100d90306003440311304440046001503823407100c076415809078080780e89540c2529001400f0800301426100340d1030000c0c016510500030914103a01c664491507001d01c050400e81901c000d98400045140c2000400001c11940c8100c80f590048400281c1e9901500d119018071224920420140030701c0c0c001103000e07080680e00c070f0000f0346000c2e641e0450341460701d00824104140008184580c0d54000446040c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 439113776 1250 439112526 439112543
    0xe0403030c080736080f0609010c0302090307060c0606050d080306121902011115091b01020619090212060c0405010315081e030d0213031122020a0e0913 67
    0x30340f807a104501280e0480990f031001c454802c0780c42d05554119104070b0b1141945400c00c1c8000038115000c00c03404400240c204060410307072a00c0b00ea9a42140e1207204800300b13050040180001560700032030f40805403030303150070140180e02d0f00c5c0c285a00140090303000550000a044000030601420030003640c03054000b2140b1841d034506441906440c0c2c100d402204c00701d4100403c602e8015801480c945085140c094103c4544801060503100a0641070303d003101945c010146543c807803540f05804035a2040d007800106040c0c1041600c0c1924001c000809040c644d50323604901d011035590100120354191008112155418001002e007035941c4580b10301400301745410140100101c4600a040031500b0a1018100450b1a0607668400c041d20501c0520540010040c0c00808503043c40074000001c0760400248a03e415460a40402594041200c1c805c50130301000300c9250f444c600b100504c0c0d0064140141c3c6501c502603040e910070f4940140030b5030107141c842c20843c200890034200002a4050b2091 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 439115026 1250 439113776 439113781
    0x909090f0d052d0427050106050a080906060a0b071e0818030601210302190c060f1b060c0c0f11010e06030c0702010c02060405040906060509010b090102150a060e0403030c08 76
    0x10715500d800500d1214140003000e02c010401e0903002c0080c1d50003202d032a205545c100004031100002ca4000b42c001c50081240422880c1d08503500c040c000e40d103c1c0c1c07036100402c0705050580008986072003134807605001120010303082c810442035008401c20507040d51000e00c81092245004800780c3c0121018a0240c1c4281c01d2208503450000391305da0484400e00300314904060b4501c005800e40b074100307405505500c00d0645403200b510145403401883ea0141d0031210040c0d00300340b402040d100c00c50140c902040b41260443d460718202040108503180d108900040034858940d00703986540030a4006001440844a4607040c843e032071141d0081020300740c3e5181d1030070290008001303640c00141c4601d200d0042c103002e0a00194020001c1c000c2c4c0c10b0000b41024101665030f000075041c0c641145048600c01d03181c403030801042c123042c003c46024024a0700e6042c00d11102d4030000303613145510040383d000e40c0b4035600400d840007020350298026043c2104003240303e142030704001d0050318051099000113540c0100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 439116276 1250 439115026 439115077
    0x5040c03060303080604090507050d050d18030308061e03030409090c0b0412060c020a150f05070503060d1b03060e0a0c05010503012103020115080a0c05060f0909090f0d05 75
    0x1100c0070b4a906840384051038070b03210148802002000003c0316130703200351180401c0303e903135902c3c0003030301d07584a07100034000d9a00d029070090104c1d00300100410321103550301040c800280c000d03140ca07600c842c05503802c414442e0f0795610842c030001102c01e800d4060000080c0070802c440307241c1028840c2030041d807103105640e07074503c8440c1082c0300c0c611980154004e0003003072600040c83d0380c025102181d001d104030f8480b05000c0d2a003116204400c0002494181c1c3c488901000600e00d005080e44001c207814485e007949840d801203100c0080128005007007403d4818428103404001d407044000d150403440030403200117038038041a035030b100440090341e000c505034000294640c4a0401c0300e058031240b61800c5c21103000a82500c501041c0503004800f507540311070b01900480401d2202400406d0101e005004500b46400c000d400341066400c518045c400c1001554204030a040c22508014015100c0c0641d07a83c4012140e400c0c101403020384a031500600c043c850040ba48800036050790f15101f40100f40f0341d02140d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 439117526 1250 439116276 439116281
    0x1c02040e21040509061c0c17100614010c0204060b0a050705060a05040804050105090f1302210903070b0912041401140a02060604230f1501090e060904060906050f0105040c03 76
    0x800c0300e512880780380006050341041b1b0080c400882c4140c85200c440c0d51103a4559060450b540c1100d03500c3c24075940e090044040401c40c22151080642c0c08101e000c0c242450580d12002c40b1401c6030500494482900c00c545859208000820703280390701c103440e4001500000e10a501410b400c0d02c29104040205407120494400c2d580100c1d4040311b2145171030318010066032690020704d4560380c08103060b00606059220807840701d00c90080a00c0041e500c00c3c620310000310015044910445112000c01001060a0000201c0c0e00650300f10058148030390b282102d03e4646411701c114420200c10105001401c00002140c410b10783d6002d0300c3e81448554440c02010302d030b00400b103000c0c006078485404141c19040130707440018041410a4070004035191220514071240081c0c9840d9070502c8500c04001c01d00c4600c41d521000c4e0102442c024035001c1c98801f4036488404081e2034940f11f0002100441c0c01c0006a6208800c0035901c00c1050103107141410351140d01110901c40d05018904001a40c10301c1b51091 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 439118776 1250 439117526 439117529
    0x170d03051e01050907050f07260a0c0206030a0e030a0c0302010501060c03080f09160618120804090b03010b0409050c0f100f052203230c0604051c02040e2104 69
    0x540103884943c0c030700001c000c1403c1c0003900c1e00040c088108101c3c208501c1d48402405840c0c01010005100a041c075440716080c421200da800b41050309102d06031156902440000d042c54044441c9520b0b91580381800300180322003400454148000517104208030b03000010118058020740003041307140c2e62428161044030a48c280180052541d4000401049101c0e8210360000c83c280300700c600240c4205c1e005141103606400680209800c00f10064200d40400450000b13418101c2901c201032403035503601025030090340200400541c03034403a000c810392825404010b940e0300c0103005025031522824040e403691540c000d06401400d44100c1b0015908020156100c18566552140e06404c4061004c4074903401420380425801e1408010060300b95000071000c010f903008040480f01a18400070343e420240301036120000980184150011556130707982960f003100c8003a2241c01c0200b9905501050700550341360000d501c40c1c070f042d561004660f070004c0e20308400d03070300d0f92036400a10000710040c0500380500e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 439120026 1250 439118776 439118821
    0x10609020f0a0507050a0b0718080705032a09280912031a0901241b020d02011e0203040512010b0904140f060c0901090902030601020604080f04170d0305 67
    0x10400288824843e2005002c068040d0040e00d01041d426500c95040c1d19040d110f1400040001510302100050060703010018910180140003807840d1a020076115502c0364104218401400001024099295850800303020010810203051414012200301450103100502441030700c6001e044440e04548520080b00e600082d807440c0b040c010310b00480c00fa002d0441402c2c4d8a0107078a10010342d035110100010b029009150f045182c00001ca80701e0408403850a100c40c040000c9a0024809842c1c0c0113801e404582d01a12040102ca08900050b5600790300b002400480781c03c250540b00d207882d8003002070016202c084451040110300a0411402c2c1e40c0b0410640d0781c00320f0540081000240030702d000f044000340d000c040e200782ca151454642d08005080350101041c91000071501c2c0c1e03640e402041800904070446c0114114106103000030355964001f00014003c1030000f9a41c40751195040984005068408008519100e03448800d9118a81a8820000f09042002045025074004400f1400118 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 439121276 1250 439120026 439120057
    0x50714010c020123060a03170904020304080a1107030f150204030f03020106080c0a0b091c0b10030c09052703090a1d1302151305040c0203070210090605090d11090f010801060902 78
    0x40d0b84558140808900e010f0f223188508204d0f0750503d80313850015521440c0909000c6480701011030000e4100f00c815504032490fa0041c01051002403001401c4001454204030180445608029920000d201c0ca0700040c00c1c4220b03071071b4001c080640c150400015105035500b41c132101c0fa489018000c0c042402d0080c0c6413203110504ca00b10f0b480c1840d928840041e0b40702203010200300301c941c0361041170140a4a400480c94504003090040c001e11303002200062416040401c417610b40040c1c80b2070681945543c008280002101102c0c00100810a942e94964020820fa0840343ea4603407582c85100c0b0081d00c0d07180c5002500000701a100e00020181500e500580180048d41d215807a6010640c00910141c1890744103100101c1c0c0c944440c41030520302c09898000755901c008600400c00c01129123500c4104000d1400828070149a011003921401c01040d5a003241c0b8100c00e14080c24214a848280794006000100700529031600200090403030311094001c1040300c1c1c550741c11400740d120310488900e181070f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 439122526 1250 439121276 439121279
    0x130801050121020612041a010605030c0d1e0c05090f10020d1202130e01080c09040c06050d0f020307020c0109080d0e0d050c0a08100b0a0f06050714010c020123060a 72
    0x1402c00700d1010560f20042c0790a1520348200f0392921a030710243ca084d243c9042d001b906203170207100705017064050046410000d04524040b0400d0030640b05140b105888540c65400314808e0300380d4209640c0a00c0500c020034041120694001841504941e500038498094280002510308100c113401000300401e034081e141010001c4c02c1a10200c12110740000619802c200940c0f04240502c1c213440900001403120307a10303515202c400c43c6810058000d030380c801c01e400824840000d400e0419042201c0315410b000f81c1713034807850f0004030003410103083c412183d078000801c1000b02940810301c04e110340f6098035003010054884004c01c0c2d03103011800803003021a40e508400c1045241c03420751521543c0c410790448100c031a165011806a2480364002c3d000e0754002580804009240d004500890400340e0f10f503455a843c5c4980340f0701324071483c8503040c01d02c00700207040030078040d0044886524506d114000d02007068080c0009000b4010b092031494040e80d03120718070588c20a4103680a01590b8002e0014886a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 439123776 1250 439122526 439122569
    0x301180c091517010c0f030506092205062a040b03070302030a060506120711010b0312090103060302210123180f0111030a1d150901061a1308010501 65
    0x240050744444804581c110b0b80001d5040e5003140a03202021000b001258a0584010140c60101042005010316060108015158070b68250142d40803580ca194108072080300d1102d1010040648400350117801080d0030464100e00c00c81d1185820602c0000e982d68040f8840c180b020760740920b001c0c824040008001003003041d40701e078001c0c541118900c5000030750039072380b000011a65802445040103811916041080f910b8106552000c110414402402400518400251115100794410800c182c000c12901e1107a48070345e000201441c1c0c0500f1080c50b0794011501026903082802c0c0c01d00c0a503003000d800041e211080c1c62801c2c00b84030070000e40c1d6000c2e160030540c151000032800380100c542c4a03280142070050350900454015240c3d1844091752400e20101100a0780c9030465020034071301b11591284001100001c0320078100d00c1070740c070740000c1c0d4072000b8a0b01c2c013401555008810f600306080c903401001c51802c00404082036130708800c0c003141e17556240050076a1424070841942825001049894 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 439125026 1250 439123776 439123781
    0x10c0309140a121101020c04020414010c0f0f080319020901090501050a0c1209030201021e1203090705030303010e0a0f1e151503060e0a020f0313031e0206060301180c09 74
    0x81a50040100c1a525115000f64500302000d0310305542c1c114119036040b02e65601400f40303c1714402c00f990107618246c200790a280c00503520503801810081850000d200b405010300088241a910207000f600742c0311b86040c050348540043c1c031801600c1c51510f420b03a240480b240b007150002c5070306842d0000e600b031400006440607004090040180302c6860030741d00c000b40e52440c81d80345c154180e1700c54450440c1180002031426131040c8604c400d8030010007400c41d00c5e0b00700150100f05050407003400d035a01e90b10340400307506094403030303008175091312002c070000c240503000000052180302c1402080141050a180d24015210500305041d490140c10354070440c3d8039020b030000c505144141148a82003659030200c0b184080703d0028034000680e450304c040c2700005400c44481d030000c80701a804d6052644040c000101c44c4809400280d02800d12184001058000c41306036603500344204080c1c50900303c03950080d4694004a6045101c0d51030001c61602440030b004034a001d03240c20580710f82c2001c0c14002e08000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 439126276 1250 439125026 439125059
    0x801030f080304140609010c090f0b0f0f1c05061305040c030210030e060408030f0f07120b010909050406202703151303030b041806051009060e0f06010c0309 69
    0x50003132055072510070781030042081c24011802c01c00005040c0342503200040291a150300310446424204408000e550001015074203c4182c008107182e6411641142030f88038480c0c0500e1030b2a502e00d040b400c0306e6601403907001c24800c0e502034a0707126224060b0030000c021280c0454008104041d007000078005070901402d0a0b00d114074034140000d54402c7e015100e842d0002c1101c0403034200e0000000c00c402d151203405100c4e0040c80c0883c9424903070401c41001b41c56a803260f004482115520940640c840e0710549250004001c1e01c8030802071303404c00342800d03809000c0d901600e000b1442344a0890548030780407800c44035104c0c000c00316030040e5550400a17050346040034100350780c03601c074462021400702d2603d0a10750007800d080305030006801903403a000c1e041d0303211400031904c0b60b4501181c0819200510001d0500303e03a0204000945a603254031411303148440e40c11511740d1900d4604003058003071b40c5190700c0380a030380d6081c0000ca49507961300c011181211619070040c0050451141040002030007039601c503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 439127526 1250 439126276 439126283
    0xc040f0612200a0b0309010c0801031a06040212090a0203010b030708070504090c0e070c05150c070f032003130515190e10031b0c02010914041e0207020a060801030f080304 75
    0x1641582c1403000503144040a800482c0c0d4104004180080140248a600468005420000490761568440c050911990b545802074840c4100001d211590b4582c1116104403540c1c00c0c00425082080e0840d98554480c20101e01a610340310100c542d43c2340c0001c507001280c080d0340080555a0500041c407000e80074440b821074088180040209010045200c1c040c82036205540d000309660140c21318500d0264520310b4a1181600700c402d00020300c2d241c00444450b50780200d0301c0d00c0b506015242c00c4500e4005007128004840003a6511049003038040001d0041e54a03505401c0289070302d480c2044100210310148400d100010850200608200040052040c40f9410883d2511422001240e10301c005005094002a0703102c110141100030210a010120300303600d004100f0703801e95400030f00521352a0246e110380841c1d05944c1c5485035103541014508074076841d03160014030301c0070080001942180008a200b01a070890105a080c03040079014106c9400200d4040a890a0740750f00c0020350000c2d01c140c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 439128776 1250 439127526 439127573
    0x12030905010908070602031b1201050405070215040506060312030906040303240603090209070c030e011b08041d06152b150321050909070e030a050c040f0612 69
    0x35000f0403000400307044c0090050f0381c0075030380c1e2402c4000700015a0000910302650441801011007460160014a055890a079000110341e2520001603107422110040000003010800c100300c100040800e0150144030700b0350807180303020369001820042c1c0c0402c6030f590450358403520002d40881e20940100070001760307418141e80390a40106620601c0c2d000c41d041030011917100c4184c070b0b08500b040070409500c41c019140c0344c6070951217a94003d00914458140604114000849a18900f01c00c129007030103a074032662213655556500525420032401c200c0030360b82900d920002070031a04100c143d20140024000e6558549004580d0140c00c0000a030fa03007181072103840700122a40c005520818204c425a03201d4400c50301d02e540f030000d244140c4011800301d012901c45003100380940050641da414401110100d17802d542d4007100311480d82203202d031540d1500c00c0f00311030400c2c00300100e492000004161010700030a010700c041c10b42514042d2040144080002d01d0039808140d03501e011510340d02c540d8680 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 439130026 1250 439128776 439128791
    0x80c040b1c21210207020303160602160f020a1d0c03040809060412020915130f090b160e01140703120608160608150906060d0f02130314010501031203090501 69
    0x80501482114008041040780e00a0660409140101c03d25640a01415445c000325039000c00d8907030180080c06060300003070081620400c0029019241e4014001c1d440e4110401e5600b000c46001d07500b400107901840a00130b02048800090340e0000c640d0080351091403458881d028500c0040c1c0c4000c1042e01e80040900c0182d08664425000340000c0c5090f642d101d0343c1e41101c3c0100601503001030030401d01c000c110b900c03040b8551100c1000b00354614843c0700c0042c81020440f0340101420f580c070300003003c40158004019021403103802c1c42280701700d183e0700c1d820050410710064402006118003200128018040752000074420040405842444d000114445540320b80312031600c03c00c5601c0300c501840048051000350742c40391940b41d0000c0e4030a076070f81504100901081c081c603030240450b4003410b00007840003c0125190020501c1c1d0300d50ba2070843d91803228140c0a6110840384c00101c0c2c100d03809c00d5a100e100e11050285030306a81c1c100000c03108500010005900130b041e2010103c8103035486018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 439131276 1250 439130026 439130063
    0x10b030108030921060f010815070915030906050c0c0706030501051e0103090b01080321011d09030f0f04360c020c0303071104060f080709020f09040213080c040b1c 72
    0x6540c028410301c6d9032401ca550601c04014146200708290105258a2104020007503034003224080890320782460355142c6900041d01100980240c0001400882c1030105118099003031400520703030b04034103000761445143c8038074084081e03a00a12440364440200100ea0a05061100b828411807105040008000b259585c0710500c180090b4010180d90700003041c203048220358001000038141d640000d030038156050510101c901e032180e01c95082841340303400c0040c03070261080084420003138000c00344640343c201150440d40c0a9000e40030f0520f4901240c02a4010901c80f000c078a20740c0203051412004494110520000404c0c0d21030b0b14404602c260028009035440c2030000f0544140580c0c050107001e0718a00611044e80d480f0380c8a41c41c000c1204400700003905000c920b40b0142c8509020141c0d883d015480303ca0164002d8009c2142e00601c0000c291500c120207045200c11144101c0a07500038011400070402110080080950003040c0d603501c9185612142101210561003a591503403101243e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 439132526 1250 439131276 439131283
    0xb0d0b100206060f0d0206041503290102100903050315030c040e030d05070513271109090604020414010809010e1504140a0c090b120f03040905010b030108030921 71
    0x10320340405604004140700c050b06000607411104501510729001d52841c40d400306100303210324890384007518500c8840c2e0b05034a01c07a40085255503481054be010310140c1500440c0c0a0102c40740c0d0b5409441814800418100c16004a101c03c071b4042c3c4804d070540c4ea810180304001085072640c01d03071600070303040d403100301c1e565a01c180000104050021501c03505400720981c1221000340c61501400424421a65103c1c056031069040e10070000703078225407031400c905d0300c1d1110700d944c68081c2e641030800c080d540c4c04000300c001600c202e0004441d502425103031a0240f00032446540140340e036100f41050008519405240815080007610000050f4084450030640c02c0c410920b005500640c1064207000074403055000300e9044a0001c0c000c0c055280d100d50f102c1c1080a01c6200d40910141c4541c00225140d60382803050004407a004207a4405000c00030340251a603025005e8030714908d1400002046040854099906803189100110b103040141c100f00100900d040c44e102c14244441980040c0000050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 439133776 1250 439132526 439132549
    0x30105010902130e010b0702100306180c0825050901020c1c050607080609070305070216140a0b12150a08030703050703110c01020a030e04020c0708060601030b01090602070b0d0b 78
    0x40348010f0300d800c0500000200110654090503003c0e03070540043c0240b07032540c4c04403452a030b0704a80c00c0300b400380007000a074017400c0c15034070240c0015034680d103000d1011042e80020b4200740780c41d07130380020381da940c190010000000b160580242d030001ca11f0401425000304020803600c0d40500450b00483e0740d004c0021071000e040412220902c9642d1420300c20000100500ca030403810900301441c291420801081c951320008010340201510390020802181c000e015842207102c40c540500143e64941e00410181e4500300e150b50b008003101040040c040058105441560030311100480568690351500e9032500080800c070f540c441054040060317010000c00c02040040d11940380c0070b4440c4003070300740035202003090400c0b196503402121211500340ea010503c00103103545814101c40304841c3e1008200240103070a40480703e4801c80c6404200c5140c0011200d201b803030b00766424040100000300443c0d07001c03102e10812000d80d010080c20301c080f100c900043d00c5000088440055030000d600001203090b81c0c2d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 439135026 1250 439133776 439133789
    0xa56071b05070305010b010507030c02040f0905030a1e020c0d08030603010e0f06060907080105090f07030e030403030c0213020f040e0705070c0b071401061229010806010603230a0213030203010501 86
    0xa0803c00c108507084c018415404001d09020303007010302c0f58a010b4014082c4140c005c0c8502d69455280013411126800b02001541020880c0d48035481e624014000854009200444007951031030049010b10001c0c001022240146c04082005038650345d180b582d802c0940015855501e810361449203274410843e800403810058001d04050403c80b080c010700e080090241c0040202030303c0140101d8443c0c4140300e41180c0d42c0000003410350b451200c00c80041100103580e03140d44c000003800106042d80700d440d6840d1540200c603490042038202680f10100c1c4180d102041d500c62007403004010081050f21151761000e507509220380707000c07000d0b559001c0803d007030340040d92000303004110300c401d010220740c0c6880284589402000121b04104c141554406580c40080080c0118181345081c42e0021400442c024a1008980740700c0d61102e072020348800c002d0242c4400030b854100001c00e0b81480244a14098200311001e8125860304d407860303406540200650102c1d480c0440c1d002005172400d104007402810f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 439136276 1250 439135026 439135033
    0x2d01090b150f3009070905010e0123010e220f2a02120a091511120a09080106080715090312050906120a020301060e0613050f030a56071b05 61
    0x406d640d41c400c43e82d0603000040184544801070014030b456914a10005400d20b20780b0181c1824040101c810b40e2039801c0903504035920400e42504501140980c2c40c1401d811041880742c2004a40b030502140c0b600f10030600c0e0b01c0040442d44010006c400c45030000300c400d5105907041e2038070701103c9038080c3c1e21000c0c4c13480005a448070300308500e041207604d191004030b40d8a00800040100074070a507503165902c00d0b031512440006094039041c0d015000303a4004142100081c800c0f0f5aa404400c0d0305c6041c140700310281e900844003500121485074074100243c0e640300091070360b1504003003012100340e00808035041c0c01100400004001103420110b051142090790405a625810494010503803444450450b0040030103001c56508903018000e46803d4541c20790b8100c091001d40e0340003d1810010b9072026040e10440d410040c2e00c0000c1c14898445c043e1400203612203d0002c0311008201e0384484000c1481c040002c403100d03152a00c81c1a002d0300f21400d894240181140300841000074905844222441d90 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 439137526 1250 439136276 439136279
    0x905030301091a010206011412070e0717040c030f170c0706090519090b032803030b2e0519080115020c0105032d01090b150f300907 58
    0x408501a466241010030042e180941c1c3e42c034000707592010180596001c0c0601100100042e40340d18442c02e0320014032108440c68166100d0904109802c00e41d410700001d5440110100100483c4c4212401247c0c03121a0f049010b10710348a400c0f110219040484521442442141190204c14043d105040c102000390210030f00c4d007440605038218660149016508008400081040640c00c24044904901c4046002c515000019046c107489030a500c5204c4d81e841103035401686c01e603081d602c0841c42a2002c0045070020300c200810030210400364112a00b031000c10002410355802c00b45030514a5041c0b2504100f404810703030920144110034030000076459030040102c8421843d41c410421100e0015140c520405000240140f000500c400240841c0c00504240d0500890f04403065032840b0a100b010f03561512401c1e4068800411014410401c40c3c41542c07407021410115031841d0300b00f10f6158581008262403951040300c10064502007118083e5000100304004001407003424000082e00715035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 439138776 1250 439137526 439137539
    0x92a09032a060e030c12030405040e070906061e030c0c020301020301151e080705070309090609050603010e28110913031b11010c150e0c03010c020307081b030d0905030301 75
    0x1407065010100700603a48040082035200891551320503203003a030b01c41e00f40c0d0004003400c500c3c600c1503030300c459001468182c90103050603000c80c0d0b00050701c0000c00c00b8404e0340d689170350031140e02030800e4150721041da072406d0301400d190290740140b83c90300c014240b90018814540009007280c100f6840284101c01c14105c03018003591010080c40542c0c4d100702060000d412080008194000082030441440000500d0206041c001d00b01d070030081c920000c0900038286c40f076084d44003810050312068002e6003003000e1044010740c08030b0000703003004184040b0440c400101d1090b03090007404034400d40b80403050948036445511a54455481108070110039503800020f890010840d01c0d0b40c0784c000d01d400e400e14891200050108103900042e02c030910380310342c3c51550f6080c02500b120486a880780c1d100d2602d90000b0300c503403011a40c8000154210001c22a00540da001030381c4034131580303a000705000000c0120341c08071800030340102541ca5825040302d00740f2584154520840e40e54401c2601c09500c04001041030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 439140026 1250 439138776 439138853
    0xd050a0c020d03030510051f11120c07051f14090f060c0a0209280b210703030801081609090c0e04060b1906021009061808040807092a0903 61
    0x3084140d5900c1c040005090048c03082214208041c0e08120a2040040101404000300c2060001030200290740745080c3c0f10165603000c241c1b040502400700031254030201403480842d80302c04a0242c841c03040d84c0d41044d040d00704c50f52002d115aa8010b0707918101484079151040604a080030143c014450704c0980c4c010021190002000d019845001d6140049031030009002200e445806c61400b14442c0500c40008042ca02d091221424080001c084510303058000200f01e82281d0282d00e42c14802d0b600c98040c561103062400e15918100c89014042210513043d902c905540d50003400c02c40c50880c0c5981d180f59404406550580d010364440316100000d01d00442400d6a4488615025410754a00310011b51500003e08401d4890741d03448000d441809803641045900000204c002980c00b10785190a0301c1c0ba4010b80910400e030311444c880070806030694481d41c20101c3c2c05400480c9600034811108000250400000c3c08000b601800040003c0c000c50800803040d001c40005e0011080104021a2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 439141276 1250 439140026 439140029
    0x609090703030c06020703030f050a020304020114092202040b0408030a020705042711130f0509010b030606060d02090d29190b0301110c06090601060e01020d050a0c020d03030510 78
    0x80d410048041000030340003504902d0b06035019401580780c04107400e040d0b00506030000c41c40b410314105020080c1c610a15401144034034405d0322404078450b440c1842c05414043d50380d030309812600c01c10311200c4004601da103224400c00280f03409480c00d500c0d40680c6103039401a5100194561001c20ba421005406000c0e900c05040c06072010403104040344c0f90a0100044803904061003200f07658004d05100e020560314000c42000b5140002c05041c0c40102c90041c402c2ca0441229646400d01040d45a403040c000c55000d91001802000c861f00c0d408208980c3c0c1d07100f05034483c3c04039030802c0381140c95101d0403001e0130001d0140c1134001300f4a1040980b01c8580e21100c01c0706c1618070002d001c010059102e83d00440c180104804002007032a004c001003401003c9141d50244580c81c0400c00040d03981001801034400d6000c0c84c150b41481c0daa4220541d0300410f506a041c0c00f58200205403160b6501c00c6014240c4410985801c0c9001d084940224070a211658002e0340002e440740200329001107100b08000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 439142526 1250 439141276 439141291
    0xe06010801080f060c03060607050601060810120c1e03140c1e0907030c140301032111060408130b03040b04061a0307050402090105070c09020705100e2e0606080609 72
    0x61800b0b02014098982900a000745d0b521076020020404030f440e800261084250700508607010384d43c54000151100e042142e454183d08a03814001c00c840d501d21711010000c5911802c04910b203410480204d040b11400350700c00049188c07010000000c01c1080104440002d1648080c00c0310341880818400c0c20b001108410010102080c1440c0181e22000d80069102c000d9160009081d070402000700e40d1816a100000d003000c40101c00402404040050180050200d0144c18480662058283c3c0d89500d01385400d03009402410000740450007200c02002000c00407217104078915110014202c5941082d2400d035401514602000100060ba1140c50001403041d6008440e920418001941d24192401020700a0350042030800050740201d00b5100520b5000c0840d1500c9503d071030414009401660701680c20b03105003095807925a410744908112203500002605608802ca19420f18190241001b00080d104401c500c204c41c003900d1080e840a00b240342c0d2803224505181c0104446420040e1010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 439143776 1250 439142526 439142533
    0x318060414100b013f0f1506050f03040507150f02010c0e0a0306111e0703030f020301050604030605060a0b0a0302090103140106050a0f120615022125020a0e0601080108 74
    0x710f002ea801c251510710f050301c80030070412101c0c00c540170382d8858648550400c00c80c450500d00c4018500042e00480078400c0c04600c1002119006047e60100a00301c3c41142e001c2030003000071410200016000b5035010f8007610840c0c4405960703000c400340b007101c0041040300040030b4002041010340e0a024400c010034003440d1803858a0018000240283c82c1884002d003000e585610159149a851040d12220b500768155254009032002280d41c05612160048001a140401500d8401d140b4070a40e41602c0000d0b01e81070034181165510f500400001d004990b0106800d03000082c541c1c500740c01026460110756001d43c40d103018030009025504602800000c0c100c5560060281c29445419100c07143c0c814503194020300c1c02c0c0c1e1002d0f5075080070409141410b50901d000410024400c0c54508010101942218200301701606071511485120504a0349100108040e03160f404040b140d804800100016441d100306c100d90010f02040301d1031380a040f980c000725041203001e6070400405401000c60717101a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 439145026 1250 439143776 439143791
    0x9011b020102120d0e160501020f0102120402010c05030d050a0209040c0201020c0307032601061e0507050a0308060303040b0310030302010c020609030706110d15090c02030a0203040b031806041410 86
    0x1070340b21484441d40c5800c3c0d080c0402c4101c181e0480d0b4000304e4101440d481999103030001204140d001d103526001c1d0a000d880303000c0990001c000c051080f1411912002e06098150302d4980c011101111120019200c40c403041c06400136286070b9215442c010000940c0040c0d60f10603800034802560810301650041d64814003803180144030100440340c0d0650302d490302402d848890042c51400015900c2c48200743d082c07000c00401d185802444074850305000751600c040c0c10008030b4046645101c0c941005100d90441c0d150403000074040c1c0c560640040005045d41c0c1402e898075058246030b042140d0072a00200c05550410900d5020302c22200d40245500c0a0141031401295440e524401c0d040e004014070b90314450a91900144419a41c640101078424000d01c400e000041070800c0b110700a20b400d191806407516203950002003101c200b840d098002c4c500305890300b00569038682009003081041d508001010705413071010312249208a10440144024594103405185000703844942290a41d150814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 439146276 1250 439145026 439145029
    0x31202040e0a02030424020306040605100c0212010e030705013e090a0e0a020304020901060f0c14010f1e0c031a06030a0e0f01090510060303080f150901060509011b02 73
    0x41035038044030a2034003594949a506e803100c3c400c0c0c0801e00340032604c1c101038804132990b8410b8000710b0040710115002d10809849404000000a540110802048001d0160801800c000100c4200303414184000112889000c50082c1554840d907400c4545135550a10740140380182500045800b03200706100f520801281c500740700d039408200c01991003210110314034906540300281107019101c410305844c62810450804006900700b81d074200d204004140003c2000380c1b05900c05c2100049a5541d405503c0d070f5a114504003035142c5a241d900c42d520b4041e5405002d1042c011400006103c00c551102086800c1a400481d401c0542036010542028041c5450f60540409414440f0b003c4036200c0e03a9850304460351000704816210b29805014007000314030780e83c5040d44007051040c01902a10584140311080d00704468507804000c1c0411240d00204149034600541603500c01c4c040c40f1a03402000700340e030010b05c1c00781d000d03444200011400036035000e103540c0c00214084003080c039051790818160181d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 439147526 1250 439146276 439146299
    0x18100e0706050c010b10090806090a080306010f090803070b09070f05010c03111518070501050306090a051e010e01050103230105040b0a05130e010b19061b1a0403120204 74
    0x400c0e01c042080104840c0030181081d48058400040105040300c002c0100c0c4020700004450b1080c0c405a005400010701c00d06004121503001d00d81c070104861440d070703a440040d00c10403003030000c0c2420008140740c0860f8a50081008240482c000d4103088054901052001e14055030343e00689000c0c80780f04000c0006d40d800400b004850359040c01d040d11440400d440003442c05043c901c03160355510010081c4901c4a100a102c1611410202d0075580141c0c2c44030010b5805100c10343d44150001107920000704101e5503544400c1d003040c02074024180003174228802d0150318100303070001140c01c0c00010040140c0d607058030076084403203d000c911a81403000588088103280c8144980341c052902c1d440d41e1b580341d40d2160b0503e0090030b401012920005c040712490002882c003103c94203400d40c80c000c02001140f8002450303406444c3c61600b000e41d101c0c188030702110135002d10803840381c030900415044000968002c118207420003e001010360103240074100148401c44c1c482c55214030510411043c0a80c14048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 439148776 1250 439147526 439147529
    0xa1407020f03120c09090a1a04060522020c0d050a0912020306070806010224010504050f0613020a021606030515040522050304120f0b06220b0d050618100e07 69
    0x803c200c0300d543d07940040c1e4600d00c1041002940103141c0030030041c0b6284154803024501da07084903600b400040c210103201c00c403000ca004140d48407042c0070708911049400d0038807141100d4400e0015041c0307240308010f585000e51241210300450f101040101c81b0350742c0507000000800700c01ea45104690a00d8010a03100c00000d082d0104012140d40081d030300f45d00030400107a244046640a5401c0103c10381c042100c0342003030192500c00e9040c8004529500b07180781e552406071500901040d903491401004400940c401c00141d825801200c0c1e0b00880b82c1501e5903400b000707185548010449141001c12403408070f00c0a9040c030303c928a403074188044100544030a812601006040254140a60a2041c9540125482042042c00031304010f401c10280004180c0c2da1441180118820303290350040090b0700d00c804c00c8040c000c180003902940302c2c9006400c0482c6548001c0d002006e90075441d12554104001241d2048664000c829004403035402040382e4002d11210480402c49001000101c0d5100c8109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 439150026 1250 439148776 439148797
    0x3f0a1404080a17130302010e030705031c110711120109051011040909230a1110030e120c0d0315030b09150703051e07090e09010e060a1407020f03 64
    0x8118142c03003501800300218840b4480b0f40090341840c20905000a900403008114015400c00910b0b00c1c561f0b02c0041907031f06031540300d4040e50620041542804006403802d00c9000807075155020000824507600080005a002d032080c0032a0f18801024000c15403a00014580c05a01d000b000201181002c81c0c0300901050101011910340841f0101d0000c0d801103400c001c40d032a1404e000c21040000c0c5a19031024114640520000310314081095a180c1d002503c0140c988018106192000d20746514520003c141f07609000415802c100c518500c1c00c06014489210008001440c00714000204000001c0b8a0319240c14001c0b1034100d03000070310032011480300a0441c6800f40202d48080780c18030043c81203840741c00807500540703040d4800601800c01a10044e0510790700c801613220b078500d04086a4840e42d00d82e11404000ba18210001e034120360020300041042d541c07603894003610041845102d00405550070040342c04684d103400c9840868000d80708006551005940203d160030120980c1c3c0800300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 439151276 1250 439150026 439150043
    0x60e0906090a1d0102160507050319080d18030206010513021309050703020c03030f01180933060923010608180330101a3f0a1404 57
    0x5640f00504480454110f90042c0e54004100c0109101c41c01064281540c0a00101c1c0d0101d580c41090585680381164895081d1510300884000304030444000c180080e620600050400305184003410310388980070045005030403540c010412440d009a8415900e20244411442e02d1600c80240d0b00c5e61050b8400c104160782ca8800081c440c60113681541c20f58003034001582d0780c81c0f616074001c00904100f4068041c40c190803200b048520b20440c4500d0480b00e07408517410b100c0607101080504042d40c01490718800c1d501907220404d1601ca180a410f0061200301c0300482c016003140c031030130350b540ca600c58a00c071050040001013011a40c0000050b070081c07202010842d100515000c540d0440c803130b20950100c17480000c0c20b41540c0310f668161400c03441850048c00449034442e560700d0300940e01148150301c42010040c40c0d401091000c1c20060414424044018610703084202d9175034050f146805042c0c05010035218102500c242c103610080e404124407408220140452011422040d4050f002814000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 439152526 1250 439151276 439151291
    0xd051e1314010b150d0c080c0d05181209120a0b0c070606120c051008070e131401090504140105190e01093206100303030e031b0106060e0906090a 64
    0x410a5200c1008500013401225030644103110800180c1d10415484c0600ea15041d04a02c01500c9044003a015800d0001e91610305480130320036502600000e4604d442a059500c404c00701803804108501c242c5c208811107589500752441000451820315001542c550460b904034000110ba28461b41d40c482549528161501c60301e00344000180746940182c54150800300d0071030180240320f255801140c0080310040351001c0ea0701400c5455040584610000c00d1190380c00e00150329106001c010f0650249800158550981801e041c0d04c16081e4030076080030b90b588040c0001d01000c039101c039200901540007400141880078900b028030742c20b40d1041504a558484c4030080e10300070f4001540c1160402a41c802c4e84101d90700141121030100040c0d0742e031000301c038a0801000404a85580700b03900c458145400d07103180d601d0a4000d03112288150403640010000350320320240809041c0200c0c4945800040c4080c1400c4015000202c6109802d102e182d0700000c100c40c0c0d130344031180c407640150000c070b0225440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 439153776 1250 439152526 439152563
    0x601031a280306060303020304210f0201080c0702030a0c050312040803030a090c050904111207050108040209070908121c060b1605160b12010b0301030209071d060d051e13 75
    0x550b400041802e0f0514000100b03040c2e0000c00b800079034034a4031490903500c4c2c40602c0b440800c031a40100911001801103808007640c00381c291650300c0f00c1401103240c43d181c001d0b0b00080c1400421345040340c81d420420300900107420f042160300302e480d1040305a0380c134013403d181e5900d60300c1c00700030514081c20303440e24019820405905a010004d0802401c1ca001b103080a14155030019011403400d0f0083c101d01620802c00480001c0030001c591041c0c4038105162950380a010807c0c90060440041c0040e1b603000043c070078001c000034024005078050316604c5103040010399605440036014107040c1400c064090120f0440c09044800351641c4840c84596240e2502c0d0442c14990321200b0300d000700d41c254500141e2a01928000c0c580c100c4810107199960ba211681554071b40420300019400521040c00240740710300941503011581080640101c1d0500000d0020707050f07500c0126180b0b481c64444c000c4c4981040f4540304448941c0c40c551082d240762610701450908014142c0d00540283c00c1a000080030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 439155026 1250 439153776 439153849
    0x17031c3305040e0d0806011e030906020c19060b0108101806031b05030c0303030708070c05030f1615050603032704020c03040e0c070f0f030314040b0601031a 69
    0xc080107001030080c80e502210340713600c0320200f20510011a00800010b8035070341c0300d000c07803568058282000e1050000910f40403402060350820480d2004d070701b04410020fa06080103c05c01c60340724640348440100381ca280080540e2000c4240034180546034050000c181c5141c501c110036100d0348514110342c2c0404850f027901510099002400c40c06660320141403801c02c2c10080300c140c8000340c04803074851340c0b5041419500e120455034100000e880c00081450540702d0360070740203810301520407607040462a00010308071380e00400d0b00010103542001c03184100002c4580d02b102826942d041044189445008641c81c0d100f0501005000c02e6020b14489844041d68400100141c010744111f4803013501d140382c00d55a40c02405200741000b0502c0c0051195402041182c1d446039201040454080890396800021402e44004400340b60722003c0c001c0e02010045200c0f446240141d04005181c203102c2c00150446054091110700102e89503260101d03078803804042181c2204582c00e1f0b41da20300005601440d0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 439156276 1250 439155026 439155029
    0xb04060513060f1b1d0906030709050c09040e0f0c13090606030503030a14070519110d08010306050c25050703080409020712050406020a1b17031c33 65
    0x5480c0c40c2201c20243d040c001e500031540f1000128407031a0b5852032400c2540d08500b05080b140000700b1003c111520340c10080c4030700d5044000a401c40b44648c1d00c5031000b03001c0d5502103420203e8000b000c0784807415498140036a003842040700c0c0140000d1001d103444c043d254104043c182d80507801c03101d10011170415a621070406180c110004124441e00da1900684aa01c00d6500c100480d05081180e04031481c40c444090094449403076070741c60090343c460700742e1030010a003400ca001d0000d9103490f1555200280000700c1540c20b20356806400d58114a400d404640001d00164035410041c81200c0260b00241c2e00700d9404400001d480e5180700e168601a8034040d85a0401400c01b10080740c0043c9440107500605445c034032038903c46140462403401111a40194840c900051384803440c2e550101e03040344520100c010b421100000d059885005034007190342c04d00c619090a42c000141c1380030342c45551414030041c8a8018040c401d2000e490070000d8511b8040110058503500000c4021200c00300300e01910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 439157526 1250 439156276 439156283
    0x507030206160e04090c05090a3c0c0809011103070c0303090212150f090118020405151f091a03041e050d03060303170f190b061602150301030b04060513 67
    0x22940080c50400c06e0170180d4401c49024504410100f040c50000d070140350b00940000d21125103025081c04543d201081000318030792a04401c0401d40602c07000c5000e000c4d1032981c0c07600c82d0f01d507a01f002c2907000c1c02c4410301c00b0014581c000c02d006000940d07038003000481a00c0c1d0180b0300881c46030b02070b00010702c1c0c00d02224540f101920440c00304400c9074003200c1400d03108081d00150003410f9602d81c05043e003a146000c45400300c145580e98103000511b4039074421600415410b09904210000d83d000c1444540310004656041041860741901c40358020079610140c810411580240414180d014006000c054002800d075000501109d0609101c05000303825aa0010100c0300d072861020006001050f060009400084094142003520004200801e0184211100003016a030365481048105001051602c81940c0ca4007064030103075450700c02400700c00b400c3c40d03c0600d0070b540d207204200c64540101c0500d0540482400100041040c800150744c0c0650030020201c0c0f5079607103440041c0c0d02000e005004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 439158776 1250 439157526 439157531
    0xc0203030d0203130b0c071a041e080c0d030e06010308070f290606120a18080409060807080d020304060f05040e15030d02031314060c0a030e0406060507030206160e04 73
    0x4075080c111801e906040c0d078080c5e05a80b180e611841d400400601c5030047c094070710b9046100780541040c602c4842940715000c1e20321104c191302c4144c500c1034061580310082c0c07000c01c400f0801c0c0300f01e900140403810110800303040c1001030744007004420303442d000c0510001e0710b00040070400c90103000e180c0740760350505981311910104410f032080072154020718010a4640348502040010301a0a010046500319440c04080440a5442c0c2c5220b8000c4d003010700d40d66050320120036140c8d000440c1e40c030140001e000500d60100304030b400e00c50840e1525440f5400b01049900560a01c100c9940100407101510200d180007080c24910a500ba6001e104030340c804148800340400b0130113410141084c24020031400c40c2a07510000200238203e0341c034010b42c00740c84554800c00c8820812100c440d4018511141c000d04594204a40075104600f4541903c90550101e8030303414200c115490548a0840603114034108141041b41d51740380295034441c020016140312005204030131070300e4011412092440b1008105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 439160026 1250 439158776 439158781
    0x1504080604060b0a0b070f02030309030a060e160f030813050901080c0315070509060711060304030f020d02070b0a0f09030804060f26040323070b040209071e0c0203030d0203 76
    0x9540d448004a600780d07803079407810848801915000d1111000c907403100f03854500b0809152240103118a0800080382d26200c1004581a0398070305000c00c0e802c242c06100001200c206080d00b42d4101411b0304440d19045010320f40030f100810002c40b013102070f03903001444180c48900302881400013464603006203a004500e0300001070902800035500941714803e0341a2081800e0340c02d6030205483c0d041c0c54540c04680284810813803410484041c20311640030351a0b07941c0c29114400441c01035403003030740c007600000c0007400d41d00162601013101c031692100600c01005168602a6400590f001c1d4100103410040e04840c400c0340c4034454420304010b0340d008808165200d0f540e08000d010440d1496040300420b614041714401c10b100c0783e004020401c1c400940b4040d03a038031395a040352640180c00d84554001900f0b91000a551481c2000d444030034818807180b482030034580100145008014200300400c00c0d240e001e10b5000701240c00c011141d0020342000a00c1e500203200213804c50250031400f11085202108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 439161276 1250 439160026 439160039
    0x60d05011e0f0204210c12121e0f0e0112090305090913020108060405180706031e060f0303080405031201090207110607230a0b0406050726150d06020c011406010c0317061504 76
    0x204031107182050310382d01c272040c13980240d4400360f400b8030700d010000c2113450072949502800340c490a422600d05140c07403403040c1140c91003503044590006054000601c0440c1058a81c20700390001a00003604401d007140e100c01c19800201b40000c01441c01d03002e55210f0020405071401c404c08980200581000d4442498a80c003005004118100585d42c007842c04058405441009100c1c0c0020398054041b040130b0141151001da4600da000f5004403420310003041400350403c001078045010300348402d80540e0341c0030903041c042100a50b40316a14820001080040300040042d10b101c07500c82c9030035010119031584400043d060050080700034000440c10820881040003982c0703e644503180c0c90301c4180c1c1031505052110120482514102004d40c45480441c10103514220700344400707400203003030055100039555610142d070040c7c160550301c2c0e91200300c21800d10a42a1149902903020b107086403000d510380d10f0040100c50103003260340728408004041f515688803007001086a0404910075070b038580d581d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 439162526 1250 439161276 439161293
    0x60617010b011803020d1415010906060f03060605180a1802090307170a031805120a05100b030a0602031b0403140607170609060d05011e0f0204210c12 66
    0x208602c1c00036003002c56002a020f507100825056980240031100d004c6104d40e50305600d0110052a0229886800700007040601180718450107400914004144980380c0f03a40607004214400000c4181810280d041c44030700c4d44502550a10301d415418429881d1030070b00401c003044626000300c0340b81c211406840341fa61640b50002c107500781c1b095084540b0346560350175807800b0403080c100000795a0001024480481e10500d2085400c480341132094035010f0780c0300002620a55181180402504008511750500006000c19118411031403014071010301040f0001c1c0d1120710041d0000c00c000e0b80440810107511010300c60101c110540d900c0c042c0d81d540c0382d00300004802c07200c0007840310a102d003600144050380b10751841f403611061074803405001c1d1120010003580320002012550000e15203e60303100850024011281030350f440b914403a02c0750228056030000c0d100d1801e0601405401003100308450003c0e007400120f42e004655508020036880d1608041c04022a031010158400c421102c005101565 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 439163776 1250 439162526 439162541
    0x9010c0e0f0420040533251401050f040809010f0e0d0606210201050316022113050f06070b04020a08030d0638030a0207080c0a0501180b0402060706061701 68
    0x2150101c00304400c84916a42c1c4080c1001004e024080d450354003602c0c81045406000c1e0461031a560380300d106490b0400000079100303100705540388500c44002303821f1050280b10b0300f038100c41280d00244032803401d9141c0c1200ca104850f05541001010380360b41410f5481000014a1307140300a040020700056420a0b4019101c02d0148134000000ca00c1c0605520310680100318640c0da041c3c59071420341e61990510448401104c00c005c066001c2e180302d0002c00b402c040380400c046240c1446a0781c03070ba10401c1c0c503140c8411098000d0781c09004008a080c41c02d03070300c1000790346140782c1c80380c205544c0d41c3e09c0d8400f0642c00c6040750b110740700c18031010500c0d01c012003a03a00700340300340d411014500f20214400b11030b07001085100070181c0c0381f0516040c0b00002c3c820401005513800504070f90050310f010303184d030341d02d1a00b80c1c007403980c00c8910b401c869600d504110f000e024101040c40352180e01a01c0c00203a4982800000019000034810300c80000c0705000c01078180c113308000c00d8512000d001501c003454203d806071414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 439165026 1250 439163776 439163779
    0x30c0703080f01031a15030a050708010605010504060815060702030d0201060608061806100e21060106050c0303010e090a060c031a150a0c15150303030509010c0e0f04200405 76
    0xd001500000b078440109040300d401120321541030501c0c4a44501000d00601011a289010303514070740241c40030001280103e100c1c100030031031305140c9001c882c2111201d030010380c10840200401c0068990001c0000d03002041002c50640c0000d913400020360760f10540c0c02c02500344c01030348410a0b005406611003c204d411985030044140e90342800c22021800c0c3e00c12030b5102140920118506003071070241000d40008500700703c010140031800048041b01a194a80c22001c181703c0c00e400521003d00686005100c2410315a0a02d44400c203025180d000c140038041050009000007502a001082800701154211104010b001ca40c268000d01030005030340d000680c030301d20102c07000035800c100079a5080f501d0721242c2142091003a0008440d604144402039035080504488410000c0003880b44984039a6100383d4006264503600c0d01a060315401041e2440300c0c1d14000303c1040307454001010b403080c0001200c9404030000e02c940081d004000d01c20030046000c01c003181440c50032a04c60000c2050350310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 439166276 1250 439165026 439165037
    0x10c021e0c0a290406120c090306020c071409040803060d0503040e070801140d03021b011202030f04020913020d080a030e060a0f060503030c1e0304080a0f1104090f020603090f0102030c0703 83
    0x22100c807003100d14404c40c8155000900c6040360603440f50324542c041c045201030b9192201140d40d403500c4440581e003008170390050641028100300100301c0080710b02d048401054600f81d40034a0f15498030b1460f4000182001c0c000c140c2d40048204001080c000c5402034000300003103107503030b0a0a941c001c1480c042402442c2d007441c003ea12044151400307004600d88940e05900410003549a1142c20f1881025071203104d041c805d850341015100000c60000e14450002d0490141640c030340f6004000b404903018207141000f040c80001400541c03207100c01c809400d50041c284503a0794001420440040144000075001c5001c1c03942405403402d496080341401422400042c400180c503107040603100d00c11191130039200e40c4200183d20210000040f83d6115460a006590405980d00c403410706204085008688240c00680404104004118503152003042643c04204500040d0781c0e1041e5078150000203481408048001110101c04200100320b0710a05070013035440341401640343d40e594006d410104c0c04500d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 439167526 1250 439166276 439166339
    0x1406150f0a0b0901050d0e0303040b0708090d0e010c0210031a040c051c09020d0c18052214010e0a02040501080c01050f090103090c14030f010c021e0c0a 67
    0x1400c041008042100240744041c518500310380c1007070070b60000032400d06020f42884181020038083c400c0d014030505600c0515580d262038035010f50b080030300900f0030003440320b00018041980000140382201d2986ca0074040c500e41c40080050324088142d0344000c1d030007400e83c11203a5801368940c000000c1c40c462806422075101000b4100015100000b140708009102400141c8071944021403480d04c40d070303c2040004025015802142051182c40301c00d60f49910000c2041003821002c0b880400020402c850401180c182a400340003100303514000d900c80c0445019110040c003195050070402c10320345800801c4514000441280c9a8803540d8081c0d20852a050000a20940214481143ca041650b40902d0300459080042190308070f995008e04041e910380d034010000d441d04061002901034401e0300303e00d0800040826280145018010500341d041c50040d011b10b54000500c0c030304020040d80e0704881251403081103071901c8c103c042203c1d40316540c0b610009120700310b001c1400b01071103006d4250750703842c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 439168776 1250 439167526 439167529
    0x90d030c05030c070b04020d0210080708060307050a2d06030c02010b0307080705060a030207050d120e01060b18040209060a0c0b011703040501050f090901180c020a1a13140615 77
    0x240812940300404400401000300085d5502d8822644244014403000808070150003044881c5e100440e0100800c40da20103004625802c48031190b4041c60403401403404130305000114a5401c00c0c0e01c079410182800021104071302030a40300c500507403001c1c0300c00c034100c503540c4100c0140a000e020380850055441c252807120a424007007128070039030394446e008151a070300d04000e0140962001d0ba4103410540e0a10151700019824410030a0f82e12950707640d85915140c80c0004821034034140071158842e07241441c10008600040d05039000d44001c940409050450440414064412000758a0b840080000c20043c0b40303030032a80346161980140c01030003050b81c903800c2049100001070781d045000d034030078007003040250310880081074112041182d803405e0044840101d0410700017a0856003003c41400d07101d81c00e881c80c0e80706009aa04803440207117080c1011742c6940c4c0000c2e5008401d60a4080c3e0070000030b0f0201e2418002c82406503000d129540816104864581c9500068802d441c40700200102c1002070f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 439170026 1250 439168776 439168787
    0xc0212030301230a0510021911131a060a03060306050406020d1b020304050d23061902040e01140d02150319020f0a03090302010e0a030504080d2a0602040e090d030c 72
    0x10040040c2c40212130034142020000315800d0026042c007148901c2000f00c0c0e40c015207c92070040c1300c2c80740c12401c040100c100c040180030245410b0400b420742c50a0308411003405c058516000302031055407483c0d6a421350220840140c070316500064080e60030700051108100c1c055000306082250807400300141c48408070604039000c2c4565080005070300c14007060016103081c0c544100c01600c500c680c820b8000d50f4100034030101081d131101588580140341040780f02107a8887c40b0f806008003503011072030079003007561400040c1c0040c014500d0b000316440e444e411300d4440940100d543c0b50010184410802c406100ca10389920403a514146003511801414024545009903680f6440c000f5440f424181644001c80041548600075001c640d00c0c1c809061640c18248001c60049009654180d542ca041801d440e203090183d8010100f0401500b82242080d10250710340c0d400340301d51010050482900d802c242001e4041d580015804402c9038050000740c940014807039040d420302d528107000901e025a0203407038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 439171276 1250 439170026 439170089
    0x2060f160504030b0a062112050a0f05030a0e010e030711041802040f0f0e03091f0203030105060307120c0e031b1e03070e2a04061e0c0212030301 64
    0x1050082c030040c800a030201e4181680144071810008a131640e8094140420084d010f4981d10311030740c0302841081c0039010740f02448a01050400f145401d0f2807100080034140b50031040400c04c48080301080c0c0c041020b410000c240c1417200001d1000c1c52100210580f29440010111100341d260441500142043d0180803c08084114480c00c1c0b9003503a000d110180c1107e032200800140e40b046c01c008648610310490b18440c08940086071201003110074000652000b00c42046000781309500d82e04107d6000086a064410640d111626a101c2c020181e41500d41c0342d000b212060700b411116880302d45c2c8045006c10b400404c1303044507109030440726544c008440e0080314580090020980300c223480e08091084c044410054102c071960303035031800c4152642c4000c1d111664130f0b48050007900c01c555820783c805c0c610742800411451600749041c8003d0050058030050008012451110a00d05401350b500450500e802030140c00c1041801003c0d1600c90b8001d00440c20b0882038501103c02d00407180e2a01c44 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 439172526 1250 439171276 439171321
    0x8090d09091a090103050706140c060a090f050714040f0e120a12051f0803031630060e011a07020f04020702061204050c0d0317060613030302060f 64
    0x20308003400e1480381005440e0302aa20228000882e54150301e64690309022030080d8000c6000d41011801c1070341c01040130344c545140c82000c50302880441c9a41c403000c0391380d43c1c000c4201c2c40c000408820600d4690b500302d0400d2400b429a008419000882003c0b52012200e8824129820000b1405000128040301c00c1103006a0041c0d10045070440c0d5004201c0c001c1600c4002c90a24203450b0215600c0b076800d5480c1103411000d014010503000c00d4191350641d10502400b03d03500a513007507252030312a204c80700084601c00e20401001c0c84007640c40c100e04120301c0c00e080700c01c041b030656005000451040070304024441c03090315555002c0009a0041c0c0d02c6249901040f614211a00e4010240c00700009298260101648039030300300301000041c1c1e00d2200038580034110441c511030526060034510f042034405800140140007030003000c000282d12a00313400c00e40d40e640d00070701110b0300c0d440042080b90042005c10383d18416212000f000b49500041d6440c450100543c10f202c071607464503280369080d1620311414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 439173776 1250 439172526 439172537
    0x20906100c0b060103020c19020a08030306090f04080f03041a07030b1305041406161b0f02040c0c050f1b0d12081902130501031a0a15051603090608090d 67
    0x114001a8066034043c1c000c50145800b500313150072004141e04040100c4007400401510348a03403800c60510051140007401c480307014500b0740c40c0110101d1f03204080142520200c55900001600b04182c14081e52240d111071903ea5869252a10f0602d50311007809004c11400618400098942c80c468001c2d401d03800d07005004200d80004c2c020b5590007500010300101d80c07803210b03000799001111042010a10030200b103010f10941e0928604042d00d205100d50724007c3c00c06500720f082e0003064555111f80401da506031000a54808042c00840b032080c0c04131402003442c043e0284100740c1d084005040a49800c120240405048110080041000035058028075a403c504012443ea6006240c2181c1c0418a08000c078819003c00000704200d80c4002d50340200d01c81ea0102c10308c42075905111b41840d401c0c502520484800c01040010000c032300c1845014410f401800c09058180e01c1102586d04001c207005500c40490240d1070083c00755105401020000343c0e56100144421400040d13003421401d058403071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 439175026 1250 439173776 439173797
    0x60106020c010f110f06012321190804050406350703050d05040f06020a1a09031e030636040f0f030e04050109020c06010b130b0403030c02090610 64
    0x40d54003c00343c80c48041804030204410704e1100045c4080d60780080168050b00256041508000c8002801e012580700c40c42e800d041400320b0740760b411014030321088001800c10302142c0e6488607072901405074000c180e0300800c1c41c6c1000c01c0007208009401a5181140d00303000168a4000c00841d103d00003074140c02da820003c11011600d81941c07145640d410980082e201c445449403103542c5003d81440f600030010314001070400c16400b20044142c040c01e08e0b07101415034043c542e103d2000b480900b10b0008041c1c800c1401003640000c0400c11195a11521021303101c501005e0202070f03d182c1c104580d41401000740400e45d11600260803012403010304c20001c08103200141e4800e502c140540100300301c80040340402c0d41408140c5030942c004445101703aa50852948001c01444180c07001a80642042c0d4010b01444000c0c0c400807900c1030540780307450440b64880c05050208251003140d41d004e0040101d00060110905038440f060303440c664000d86a2080c0740c0c65030428805141d049100050016031180d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 439176276 1250 439175026 439175029
    0x601030219050907020c040b090f0f370e06250504090f02030a0c0206010b04030318091b18032301110d1508061513022514060106020c 59
    0x98000e0721012001c0501ca15252004a91210810307100c0c8070240c3c0c0482283e850618040c000c0c0d032032008083d40c4194079404c240c14095110a005464544158403107000105500e840c00b48000c0344a102c3c03484c071040701240070000000048528001d07404942004c09500846c0e00000f001070151031270304103040c00e030f00d0689001629201d81081d880d003080703030800c00081d00c50b506029041940d00b00960040c1d5908080c2c069208444040e2040c9040d50000340c01000b1104181040c0c800f180d8150801515081c0c6000800a903868a5081805c040b0f1406e441c0fa081e03403503140c0300348462a00300d881e80602900300d100003c6007408541b000500c002c8400500c41c0044120b041500c02c2c00e02c03100004203040b607aa151b03090440e0000074104100c2c0d0307680c2095401c50b01c4030581001c02024207501820550510800144040341484010ac0c00b60082d0b01401480211035411142c1c0800d4480310900308210015039468070030769402095609110021000e25200340c0800c0e4035040ba0080c0d001028601c1d4040e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 439177526 1250 439176276 439176289
    0x302011b020406030b15030a11040906090f050604050f030304020a23090f1009021602040b21030405090105040b0a180b0a08101b080f10031e05010608030c06010302 72
    0x400030450415200141005032110701508001d10312800c560f00307043c603100e1800300041080c010154031a0384800481300101c0c0100403c1c8503102c00035500030943c600d0301c0c10100080c1a50b6032008100d511000540401d005000c105c0074069403003501075032101c5481c426500d60b03e000a94010754006050f1100b000350801c40d82d88105810004001311201c450351000003908004101d032662040c052210400c11041c1c14203948001801c00030500f10700b410201480a00441e03403568000b4082c0d9554030149038180e90703d4962454115200445180d480075892170b0588a030040c2c131485024054000010400386030034019486091005044c051000d4134010488045504102d4444406940c0700500c0e2555180c0c0e58262000c1c0036100c005042005102060000303d402110b291603c075001410212002c544c05215241c00445d503070543c0d08162034840d001c0d1402046540300400c502c800341070384902c0810140c058415140100020446e00342d03100810741e01c9110328100d0840c60b03048100144011701c1c149 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 439178776 1250 439177526 439177547
    0x403080a090c091503050c0d03120209030c030f1b093702040308090306010902070506011a1c0509160b1e040806090a110d02010e06031302030d0e03061609030201 71
    0x1802c0e07507800e46503220081c4088855200d65001106809002482031007000c21808006130300039206030503044400d88004218030600c1c5401962340c0e4000a08041d50f0354200800d0960301402025260b070200a40707002a55001c03402d4020540001c610716807540307890a0803081e407007a0385150f6420b00b42841c900c2e0841512900388d40404c03400201401c0035004105a201400c0550310540c0c0140d0368070101130405103450016848442d000c1c1c0100020b900181d40840d1844c1102e40020750600c83c1000c0c2803100b03105000d12002c0b050310354810018240d40c0c02e440d030003990040600901362810300c3c416108480546150340503c000c0b00004001c0c1c01d80c00e0203034504120420702010456070a00780c4910a19040c0300b019114940d41e5406202d105040c40203000110704540c0003145c002121800650001e4061644240a241f042070040b0000300d02c41d0055049445040e030090644032036407884080549400b2407034a00600910032940001c10010841050000c4003206d91a0420840e1641d0b00468011420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439180026 1250 439178776 439178783
    0xc020d06051b0f07110301020f0415050f030a06050f0f100f090f0602060712200d09021504230a0b0307050408100c1d0901060806030a0212060702060f0403080a09 71
    0x101071200d050b4841400181c2400708200808030743d00c4102c0c1c2001901c011501081ca8400e03441000b405106006900468086549441300d244c1e03500d01205040c2c816002d041340040710320b1000010001e011440c0d912042c20740da81192a01c2542c603004060125108030103901c030340c21581d000150400c0900402c90315000018070f14049102c1902d580f00440003120680c0b0083c0564030510900000c50b070400b00c04000f00d060520b01f00600001e0120824030f207044503404501c01040061100c84020068102c403c5075900500741c0d882052010b038140e00c0f85e611511400d17004401800f20164500300103164a50842d0b4000e00301c040c124100302c04082143c5c400b030581418090200f20020350100144070000307a040d00f852000403a441d040c1c00240620320004400c011208454010f0b00155032540c0103181981c82920304507000d46ea403800440c1c5407101e00030f8042d600000b148019140c407800043c18900c00c401035401d03200716440e00007402100001c01e80d002008540400c00042c61f0000981c00300005500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439181276 1250 439180026 439180051
    0x80117010608010e030d1803080705031009090f030e040b0a050f0402090d030903050d090b0d050406020c070e060a1a0304060f0204030f050604170922020c0d08040507060c020d0605 79
    0x25140582d90843d072115400c0c410541000c61511a50025480f490418019502803100400f240c0ea8000700708001c02000700040c4400400407031600d14610783c684014001043c030410168196041010030100540e404800240843c0c0c045041400c09003d000e1200ca0701811004001e82080108450014a1030645030000e50901641e100707962484011000b060080c0c48040f4047c0c11070600a06211820312440d080c80000c80702003001e4620b10084aa04402e10340c000201c9403618900a03010380b1415103000340c0752095000104415054011250141314112075014403250b40342074070407200ca1280d21140d4440001c5c070004000c58000d0300301c4501c10f540400c006151680b255603040007140503207000e6030158422003c00040160341a8010444c0c00444411030500d070030900080c0c840d034a14a01d8250b01c1722074100321020902d0035015a50404c4401c03040d18103100031040000c100071800c54055480340300341c020000d14036002e04640e12901da0098060078419806407a0f98001d804040d01c2c220315401c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439182526 1250 439181276 439181279
    0x60d09082704090c060804050c060f09010e0a060801030803070e0d03050a03150302150f1308030a0f26060613082401050a09050405031c0b040501150801170106 70
    0x4400c400102182482000e8400c020000050041e0780718801c480300310300461500d4610740104100d070141c07000300d440a2800e80e000741e03910302e44079041084406680c1d410107408102c6c03024449900b4007400000c03000b0b9840e21039191520040000344003c500c599000300d6807481c018404514590011a44030903c0d08007540302184840102d814142118811340000e540030030440034584d031500030742c0c1c4d070b00440394400d032201ca0a680000d205030343c00710356002c0280400a001c421400381d0381c0640759101423918071441810b40d903001150700d0b40e00250781840010682055001d4850180c7c58110100104180c0c03420600e0070f040c00c142e81d8407009403d06a1122083c007080403882c2d420310204019140381d00c058649044107031100312024220700381960b505862540140a0b944410b010a812a14207410210720ba48503803e0460031880340c02c07901c031040b1042c0c84411014000c0c540000c0030011040d1010407591b80d9402031180105400081c0c00300094080b030040010f14404052203000d00750b8000001440c6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439183776 1250 439182526 439182533
    0xa050901050c0708070306110c0d030f0b0303120402010e3f1903083102280810050903270315100b040612020a170103030522050f060d09 60
    0x20703c0c41d40052150340c0220014410040347e40a049091390000503c582490700380010b0503152880c40300110300709a0f0742d00c0e0035408110181c0011a0081002d801e607580d41c6144200d10724180401c03a02030b8085410120409810b041048140030700700b2410a40441c40342155a04480d0304070b140081e034040b03070354038800001e008005000e8101600c1101c0c21404d00481c0030325020b0511b000c0100200c084ca0305402c5c1c803240314004840300302c110940c41c02c1800907082c45031002038020070025100c9054007803071101d0400540c040c0f02c0840309030380051080300c0d5040f00450880c800d80d0411518003c141c4c00030701560a42020742c145242c00040300c03600d040e0000f0340c1503010918051241014040001040040c090f001482c1010380015100d0121018517041c140380014103403c12640c1840221980080e00401c0944a6000704240c9801e001909105503501e007002000380e00900703075010201800c100c0c0700c11400e0351290060100c5201800002d03001b2608000c000700b85d00902c03100742405450740c0440c80007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439185026 1250 439183776 439183783
    0x2116060e10350f01050604060909020306040f0926070c031e080c0c1801030201080402060f0909040f060b090411010c0302010209100507050f060606030f0c07060510090b0d080a050901050c 82
    0x40414030b000c8080e092815026500d44110306a0115000d00010030050001580c02120181681c070790100269980c0c40750f030b000c23034001d060300003290421034944a80392003002508820b424814158054104d189a0080c040010610800300010030908403200c0c100300088446d4402071510b03000c00b101002d00d0b0315039100d20210364040700c40c0c03190341c0d00700c001ca61915180c03418450600b4030740020105034560459001903d980c10143c4040d204440110b600d2485d10203400c211020a030000d0440c1a40303042c10318203512689824032040310350078105a40b00f0080e060464045103d203400400f06101e6003e2a0010340d80003400c1c0300281c045540800c05402d0b1603d481180c80409203450303481e01d42c0d0704001c1c00c0450508407440c407200b4840d040041405120f170faa071000e0304e8000c00c3c003c00d001655255a1891140da115000300100302d5800c0c48204041600f80c4000081216000301c401d0014200000400c10542007042009021a80c1030002d034040901c900f01400810f40c06041081c80c000708106500d28 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439186276 1250 439185026 439185107
    0x100912200a0e010f0f0e010e130507032303091f110703080301050102060f0702100b0121050f090309030307060207020d1b03050705010c0809040b2116060e10 69
    0x10350115201c0100109a00541200000c205403131240300c1700341c20103020000045041c46590711004000f40481c1a0418815410103116440000c0f102c050b0b50b00d1a1059001040244010404003003a0811b0581e82c0d020040b134080ca86c00501091001b0454804100d44040021883d03040000882c2541c180c180708004410145020300030268503585054002498000014840712101c10820240254103400040325110b0f81403400011800c5d508800049409031004403680b03038440c0008079100682015588424040c00101c04042425520882031a941344110001fa98041e032080000401180c640d0707014090b107c1c401003130740500b1541515046804011220395521300d4400030010020003004000c2403008060a08041d180c03054944c44030450b5000350f0300321601641e1031b04540841c6541d240440c0c40070008401c806188281e00c0341640f0350703511188103026201c01d4041c101080107070242c400840c0e0b002004080f0b64108408410449081000c98a030310809a4072a0400589060a80501c00f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439187526 1250 439186276 439186289
    0x5031c021f3905130b0702040f050f0412050901020304090905030d0518010c0e06030c03150402030c07060501090b0619090b0a170f07021b0607060603030e100912200a 73
    0x208101d00140910603042c10140b50903061080c20444031035080950b045000486030005400703500d4102c0c0d8000708014020381c01d1466400d600c4c00c01006180d400c0304044500a500500101107010072102090314540f01d812011800360740300344020440e910b080c1c0c0000090318861001d0700d0520750003051720003e40340c0c2030701d100c1d075400000080070220503024468452079044034541106a07243c088040380e650302c409048095800e80020001e4421108204c0c442c255090180046582b45400c05c80d00829400c050811034460b814a8000500c1025500a101000c4001000246030074000c00581007c3d1134503c00788010300c03501d840005034030708a030f2018225140c00da445891540f640303501c28070800710000b000c1030702035071041e02402206940020800240b81c1032207100c032030030203032a000910f550051410080c00301c0d042c14000b00416600404008406005a51b01180450782c90000e48108110b8001c00c2e45200c1a16407100c0407683d000c540c40c4802034042030700b0461211000104448280030b40012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439188776 1250 439187526 439187591
    0x1f0b0a080703082110030609020301021306021f0203011404090309081005100803180609030c0319030201050f0103150527010c0f020a0506160e1905031c021f 69
    0x12180f01c4c0c414281100c0d1402200700000040ca0420084a0b402c003d50101401d903030b0f80c2c2c1c48204210b4a0960403a070342c1c40ea68607000c1041540d100d000a40d514004611049680708845d40364642d4655802502d06803103c1282490100c407811091200034105050280c0802ca1482000225410248600000b00708582400308107860840c0002c54101e134503900c00051640100810407008070004c0f0801200d40045920b942d90301c5007103001903d0304408803c45549405012000f01103050921200c0140e18801c2c1c0081c00b07503a0700c8a003c41c11100342484003406054507140c1845803400e29a00103503100c0305211058500c00e0000242401c01e00400ca03885105a5546e02c3c0c0d2508190040b80e6441d00100c0b604c011718200c20280c0c3c429480d800060456442c0703000142c04402d09500800c8805a2003601411406040042c41c50b01c03403170f460f401e101e924080e0045111101d400c3d2801080e00314510502e400901c0b000c2c01204031040608072446503081d82d259035401008248210104110f03210002c20100b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439190026 1250 439188776 439188787
    0x161e08031305012702010c140d02010f0e061303031e02030103030f0810050d150207050a0f14070b0316091701090314030103020a120609021f080601021f0b0a08070308 73
    0xb15085582a104a00190700b00d05181c000d000041042c22120b40c3d82860301012500861905020000c29240404454000d8000da07100f071560551001b000c21002100601c030351580028241c0e26200203031a4000e520001090b403d001c00c0c040e412000c8180303040241c060104410810080403030b04281c20480001d030034a2810b800c0785070300802c006e800024041c2103041c658a8040013a6080031098801800b52000e445046040c0c0c04550594190342d400030103840c07015451385000d185048451900300c615620700d125200148900045580550300c5801e43c440ca540c840e81450303400b0502400c1043d04005c04860042100f05414582e07810000e024000803402c51402e150180c0700c42202c90017844541d405000400c056522515040c00f00c1d40344040307282c4414441d0034510050010800c02a402a04001ea404441500d0300380903030b41e9411580d02c4038681c0d02c4002c012a103540e00000d03a200d000021210fa2604405a644452021034004101c0c0c0c601a50300e5016508000180e8001e0301c410f0030205030b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439191276 1250 439190026 439190033
    0x1080c0910080109150b09010c02030304030507030b04170408031b0f0d03061508190e030d021318140105122a2701030303051b03040b04050f03161e080313 68
    0x2200ca1030943c54985c0c01d201400c10408003042d014840c80d09040040c0c00000c1d40c25901c05004580166400c0302c1910743c5c041d1241007461b01c6100030f4a04440c00c41c0c12884108868290f403040d24103588400e005140350003942401881c411100d410408000d004000b25089c80800030402982d1001643d140404c001d8505203060031084107001d9045c003030007600000c0055a108581240403194501c1c003000887c0d000c0744144600d5070050311351072101e1510009003040503842580e0888211030f0251207014081e00141480b0056888040c00340180590070341c018040d900e0110064461030002004443d004d410400d112a1455000c0340900c80c02642a8102c804609105882c08503c03640b6030b58100b0300c10100d41101c10146d105100c050100341d990804100c490301112403132140a089503401e580c40303040508080030220401c0d2000c8409100780c008100ea820004029038074520b0100b800304a610a690b1104030101c40d440e070b00e0030341e03c01c0d0340803c0d0b00000361640050f50180e0800441d07820210310500c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439192526 1250 439191276 439191281
    0x8070908070b0318010212100e012c061314010302040b240307020a150203071218030509040b09012301020304180b0a080609300901080c0910080109 65
    0x8201808a4100d81400d02802d81074004030384e00107007880f80300c0e0450f0003440c07050790080c051400d1000e01200180207214a02d10f1008519041c2da2008003c003696076a078203009450303d105c1850b501243c01c1e107101400400100c800c80c80342d0000d0060280143c802001c020703481107801060441c04600705c160b0040c0203600345441841d4603070f60140c41704000001c020803500d038641c08002403040e80340c0002000076174883c828451058620743c4802d800e40c0710030007402e054020b50030807215400080c80e226400c03040c0ea4003a006e0300f003800140c1203951002e580782d0b0b10129402c0c3c0c02684010b410540782c5520f0790030f589030014801d000700301004a404c40c100f44407100c64501a54510035604640c41440b0502c000d0411156616001c565221300103402119080416075200305940102c10502401c03041015105010442140039030f08841d01000b4031251040929400780e141c07020065031001489034402c00d5029007089904901d42d000c3e800d05000c404000100d00407103014131a0005803074400101f01540030350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439193776 1250 439192526 439192529
    0x409061706070804120e0d0605011e0f090207020a0b0c0607020715020c091e07020105071101022503050d0e03041409312f010923041b080709 62
    0x20303001d0710aa062140006103c50409007025280305040003120941500440300c9009002001d000c4200e034855a0402000804091040c0c0d45800200c180484100614040060030b40341c0d0000c07548215800e0404900c029001070008a82283e4002030116a03034440c18090115030b100c440080c486843e28003802401c101c0f15a10201503a03080070903190320203070081140b03004008140c03061001c0d41e54800c41c0b1403240d4200946042031a00300070031b0015469040d0015480350301c01d501e0b06085003241c40081d40c200d00c83c10010110801c0f02c1071007004e05004401c02d1402840c0a440c146041c501025034020894211202d09001640b0001c0c0800192020442c100403414003150980050b107002c604001e44110f00c02130003402c80c401030303503212401480942605402900201d86182e0189160b440050140314200c00c58003411402e03486914540c411400d120030360303104034252480540600f039480c4042d0200c501e02e56000d07460308520361200400200d1840d0000b02e980c0d440c0c2d102d0910303400252444406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439195026 1250 439193776 439193819
    0x20a030b01081b180d05070302090c09030312060a0305030c0a06050c071e06150e090606060c150402040f020a0509011d0a0b030c0c010e07080f0312011217040906 71
    0x8000300120300c0f415a0207400c0c0e54082c0880e141da9000254500083c911042c0115540140002442401c1c00000244003040d00d10079104521140c90740390910f0000d000d00c42009a060388200700e962400340802a10503000800500301d20011600c84c1e80d031a007541c00250b2503050036031120303480e6030a110b1940170701030300b16001142461410702c3c0c0741c0300d507011802c1090a4201042002205404000c00d540c0b1891411002544144145d0385601c0011b9600380117440c2d80d4494401d40c2c011803000d03e00b180031260840d915a008003c030440c150715003984800c0051081ea231150752294080d06080c3c3e42d0004192101c4641e1740c6c2a40c48220300005081c642e00d2010346001190a82100452515406100000e9072040360b00700752a944c1f4034111844030310a011010009500b003440c03c049030000040d02a0a0710f83c2802642c68485803101004e60700c1c06200c001d001071101800042100c03250a410300307000326010703141e10b800c01c028034900d4008562190b4002080d0a6883e1000c00080c401a860720010340172 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439196276 1250 439195026 439195037
    0xd03120b01030b061b21040503010506040c020c011103040f030602040806070c0503031f030f05061b090f01051c05190e010516051b0703080d05130215030c0903070801020a030b01 78
    0x41100108400b802061022000080c0c500341c0410901d60070003103407009003001782021840f1041b40302c502d441c41c1c01501c6014025804c0c000815100d1070a802580001c0e0407990040c207036646d0403001110700d201c00e90010082c60200300004200d0807043c0f106d4901441c0281c0001d80da6074604a00b903441c1001c001d058100b0480d848120310700080c0c01004694000c20680340c0e0043c1030070b8071300344070404d803d0790343c0002c04803003a0701c1c80b003070030450003103201445006d81490300e444012002e0034003000c0f403050070400e5501048a80c0c4509456000d100544031080b88804440c070107034100e03062482110016038072182c0ca4442d00100a00744c1515004d150490303c0518003e00c003908042012420820402c060380c000e1001c085010103011b0b0781d0710300e50000c41e04e2900403650120307524100318920354014040406114105400180e082100c18112504140d002d080b40002c0c4101c40030804080d00064071401c0880c2007080058119035041094a000c1c142c03071307000145c0e183d85200d0090101c0d10260411414401e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439197526 1250 439196276 439196291
    0x30903090a170a0b0a02040b07050105040b010b1306050f0d0c180501211128080c07020907121506020c093702070c032006191d0d03120b0103 62
    0x21004101503040684c083c0321035509480b61103501e006800795030440421150302003030840500038150802401540079802052850740ca1324451022841506492401054051001c00c03169200d003004110f00a04030594609010320401103400780c84600d500307000014051080c1d0761041c0e0340c9040141c01010300342805c0d00141d10003170210030aa41101101c080180d17a601c070300b0360401e40003000c03503440000114030484002d060442ca0400c0030a0140d5000008001c0d0f0000340070003443e001110078050300205155081d03a560102241e0510019080c00000b60700c0e002840884083c1d03c4600c400780c0754640150104204c0d0409024000c03000074074070200346400c954500d06004e800c049038840b5210851220464903c02c6144002a00c140e90f401860100410705c000b0a1102c005501c00e4000540d1120300040d0b00c1d40d02c100300481c0505501074210f140503000001180e402040142c000314520501091840398001c00169403c40403441500414440c400600207442a48210100c280e000d0800700140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439198776 1250 439197526 439197569
    0x120721080601171f0303020f010b0d110d0615140102100515010c05070b0d0605010e0111071e03050d030c17010803190e03010507030f0b0402160609020d08030903090a 73
    0x9003644288250f41600e500041000303080720340e080366900c8000000110b102c59480c41d00035903640d00d81c035400342c1d46c0d40f0340700105010f85042d2280c60360858100c20300d036803c0c40074481004007901d0303000000c40c0c00560f03480c03011300c4406055811000a05850141c1501c100c000400a410300b11030018902034286004104420184240c110580001080c41c04c1c0041d13520303600d020741ca0b202c210f0704a2456800d000c20a440d00e0b4800f40c20510503100280d80380803603075140b10010f40721135083c114180c006402c01e05c01444030000590400210110b0110744a0005950307840b440d0404100404e18000252038500d66045c03241c100c40300d0041341003240310751a01589460403d644a004260b40d107000304c1411455000c4c0144503881030b00d482003006008000c1030400600c040c00030801d080407041d2540c04c060f01450140b920340700355082c450050780f1491212005540c0d410042904032412a4001709421504010580d444081c1d8458003485d001140c0e41e0350381c0810081c2014042d4800410094241c0da1118032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439200026 1250 439198776 439198787
    0xf050d050303070e01260613050702060f0603030409020c1b030f150604020c0d1e0306060519110706090e0114030a030c021f03021324080405120721080601 68
    0x4100700d0300d00b45801a03040c000407240084d084100c0313011803245560301041313010035003502806407e00f2202900c01460509400e019a80c049601d5405600100001a40082c151494a43c440d0009050700d14241c0c95914a07012030b002424840c0895001001030010181114460321403c02c04170000d007810004540740705d594000c802e2031900340b1152000480c00c240c5031601550042d07840c1c0c50584490f44028240107041c1003a40041703014403152000034001c2540648944020340314580d130b4443c504002450110150031200951508000014105407500102408100c0280036555580b5964a103864a89510142c068200310804a04030403010307582d590000c0c581c520180d06041c404002a603d0002900704c0000030807190f15840200c40801000b903040e4001c115008211010441c074940f54050000c024007503441e0b2a0b00542c1016802d083c40d0b00440c040780e4858421030441e01d0109103401007041c3d0f0b4100900483d410100e002c0080c00e132142e03902c04041ca600c1c091804241ca4078000000800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439201276 1250 439200026 439200031
    0x60506030a020904021303030302070302060f01050a060c0c0b03180705030c0a0306090f0602160b010e0907170c19090506010e30060c09240409050604020904060f0f050d050303 77
    0x18180d001583d1401600c440e015185609224040440c681e036490901602079404074504a005004a60004841038503030420342d81a03880c040c1108500c45e00300b0300207841400d00f04405855a6041050000300380161000840c400d10151607040410b20905180c14a400304507007090b48280c0228043c00c0d019200e03a901758080700d820000c041402400c90610300c0340c0c03016811000d440203000040c038004102c41d640c0a01c400342e110354100b000d83e030ba880042c0340c40f0240a440150040e0000401041481c0b407011107207090785191025152910160b1000811804128610842043e042c080c2000b0f03401440c46115400308080c01d14400c08020340000a0796840e410a400c2d00803912050441300350313a100e82d0224807006122045038150b04000800c841f4503000b0200c03041c442c2060b004003803010100c80c0d41c400790010300e4102c003e0030305041c00c014002400b8001c01d0140c10640c03c0c0074a03011941d4500541c00103250181f040d8400b00d080c1480c0003401450368111a0060404042803c000380d0700204880d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439202526 1250 439201276 439201291
    0x8070b0702150f240d060606021f060f050f0109090501032103020a081602070905010f03020a050d35072004020a0915030605090c0301080114060112111b070807080106050603 76
    0x130003043e90301001072807080c10307104050901840d20101007200ca400003400c2038110748011225454501040440c02aa405406107000c0f4641407001003100d4108a00c3d802c10310034050400014198a4400706001c5030700903402543d130609110b0031507011824080344942c3e2102140703425450315107003207009062000050301a10140e5111149110f0300c5100f403210300003a0a0715481406503503582c6448400100c0c2901003a441484050030024091a1078401c502000d0b0344080c1104481c5082e410800c05843c9120140d21f010342c0c20395203901444a5a030060064a101d0141c1282c00801d041e160b2a8084c0c2e1419100d004a104005524225411080345401c4401c00c0d106290405040b00b0110702820707850380300c03680224244050210248030300b00514162500c180081001c1c0380c0a0311264244002903806a001c20b2441e0448030701e48035960400c10030001d40311245460071250091030601c540754000420340c0d9801080c1e061144030f41c2400801c2c020460034000340201810440018110302c0090f1111 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439203776 1250 439202526 439202581
    0xb061c0b040c080d09030210030504050a0b1f03030c210c0b19050117060c09060301051003200403051e0601260a0803090c041a0d08070b0702150f 64
    0x1001c2001c2d001001014000f41c0013a036402181c051805403d5074403502049104002c4070f00240e102c01c1c4244911881144c000c1300914159480741c980900340a03000c0e201b03140b4408420ba4420444482040403001148039a0340d07400000e030541001d1680c2500c80e8a00010280030300d1055520551040c11410005e40203021500191a48500c241c03102c28160706218146041000019284a80c1e000c1045241c100e0000c0e03400c181d1791907243d00810711480c005107030b20003020700052109046c80ba004401d4807145040000703140b68240700944200e461041885100d8400080c1032040020a20501c070000847e0300301e0b080407a81c0c01e43d0841d21000140210b860070f506040345001503614245d03072440c00e100c4140649800252078188207505900c1110b82c00c0700c0d032080d0810035813a07007050300c1041d1191002e846079011407040c460400a603c16201c200b903520b12070900a0501060b07514441078020301194004003240c103840c0081a041e40d10060001440300b400341c0070000310720200c442d004071040031794250 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439205026 1250 439203776 439203781
    0x50a090f020d091208010806100611010b0306010b0d0b15071118070c12021b04110405180405070b03131b090507080604051602120a030207080a03020301030b061c0b 72
    0x1088002d0251011105040f800e0840d00e005220788a003020b42e2050307865441c039055a8803403209968580003a41d41010210300301000b04055031048101e2030480d0082d500214900f44420002460524280c212080848001070303070084800c010301c1020b440104c04c3c5c6050001c0002c140362000e203402028400303840104c0c3d0b084240307465540c540d000f8031103540e0840c01e03c10354284448024000080014201c80304600000180d50150001a04020040d00c406426280c60000301c2440003402510341c518250800034440480e1304d6a401c20b05261101a2660444051515040c43c3d8984076403a403200c681402e00f003040c0600e03001c101c8820703d03d940e00204901c0036a9104103101076520754a41c041e06915140400703010ba039607409580240914400c070783c24001e0f0303100e1115050100340d80c0c00984000d0307030048115450381d45d803c83c040c0c6035032820380c00d0050070080140c03140384481e07005c1840c000009a0010050040000310f10740740da04140160b944c0d0f40181107008800f00041030380c24015042d00c180100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439206276 1250 439205026 439205051
    0x10806040f06030b1918020d0f0c0f080a020a0e0f011509050d05030d0b10022a030a0309060212041809050115151428050702090112140601050a09 64
    0x102c44011a03100003940b0951a044280190001c900700d105400c407410070000303056003004140074000543e001040d0b03040d803503280c0d03544200074042d40b10111915103a03940e001906800c0940520001c1c04500040c105000301441040450480b80e000034103e24800d4090101a5210301d5a0905490030f80c41440305114034000306176056051a0301083e80250803031550760810202101030000c00382d181c0070910003200380004011800101d040c6000c0141e006141c145001e800960140c0901d071040a4101d42038a54000800e00b082c0d5180b1040d000300e11206010030186504014003d984007801e0482400d040c01d0440101c20b1010101c010f04e0038a8480d818042805020352010440e10402c4480c143c64582da00010910410280442c07004540b080441c015000307a040f040f600c2c861494001160400c0c10811454203480c525107500e0200318062000c0380050300d07002016400b91515041900a4079840d251441039154002c0c0744250542221004000544500d40024290fa12081d00440c2a504545 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439207526 1250 439206276 439206281
    0xc0a090b1804020a030605041503031e030603050a03050a0807020d021e1f05011508090703031112030403050904061e05010509060c070f031a0403020a080702060d0c1e0905010806040f 80
    0x142200c2d402480040c0ea4240306415174010821503e00755010b012030300c00f2102c2d800195590f4880075000c90140304510348294101c01920700f040e01142000a000303500d170344816141c01ca0001c422000309a0004500c440d060b00945500c0d48100c3c18802051342c0300c1041802501c1e000c1f14011104030320110121004400300034001080c001d004002c0035918001000801c602804013031141c440d04030100007148008a12030050503101e00a06801802e280c0e155683c00c5409800c1c2140b0307402980a207140340c04071110110004d6010718000d59076103854150041c204030880b4200d81c008807080b1206040c84d400400f1080001c01240c6003400c009440398050740214180e07100b07848102034117008506002c5088990700c1346501c1501c1c01540e80c810101c1101c0c2c42018140e41c00d5a024015a0026074110001000b04000702540c0d03102178403113410080200d90103815240a41001c4000c0f6002e9040c451345600c1600d1085500250344c5403c0c21071900e40400078006c0344010302000d0142d6210040640d00408a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439208633 1107 439207526 439207567
    0x15050709210c120f020303070b0106030507080f0403030c030e120403110105091e15030a050f0702010c0516060b0d080a11030304030e0108040515010803070b0c0a090b 73
    0x10105880c8041d941d043c04940040f00302c140a001031720140050940c0a1207810300c0100365040c04800b03425100010000350030040038dc4104a1101617460010b50015003505002905106145048018080f15404040144105000100001d4020001300101c0b4011402e00071117003414001144d4a2103405146a0b0049580300c000c20001d0142c0c1c0707213101c0420001c1002c4154020020340d000b46410450304d80c0789050b034900400c580c0c3c004503024181e00000b00d200800c80c0d000c41035005070090140c0301740603460700300f2403007240204001030f80420650382c8024507030004d0f42d090b86426480c641c48509020001420b1075079100c04100e001098900496064854031205082c1100450388110000c009483c14032031401d4500d40d0b0800202000d018010701c2d00034554462490810340c4000310040c02c400c8501108202d9088103a50002c0601300741c4041354001a9250f15000c160002681c2c21f = true := by decide +kernel

theorem cover : BRFrame.Cov 439028776 439208633 := by
  have h0 := BRFrame.cov_init 439028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439028776 ≤ n) (h2 : n < 439208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
