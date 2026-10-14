-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0517
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:12:47.621335+00:00
-- url     : https://prove2.me/submissions/32febdd8-018d-4e7f-9cf0-9d60d7551bce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 92805755 ≤ n < 92985612 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 92807005 1250 92805755 92805763
    0xb031c020703060b060406080121050712021c20030a0602070c081203070801050103020f0c0114011701090b040807050a0c06020a20010f05090109121a09121204110d0302 74
    0x200f03a52403820303c0f1003410f8504040040380c003142c28590703a4640583c03034a0001409421550070400d09402d9044a1a000c16420410074018007008140d80e0550b01540c810043e06030214081580400c40c4100b0007004181804240c22031140b40340b000c004181e084c000001d040c80ca80e080b00504052010035820103003c100500c490540d4a40000c8a0341d444014603070b8001c1d800211010f000144403800144081d500c41e0700079101c11400148140e0910700440e41c0c150a50310160a42c4004410102c0100884040c4c22204a080d2000d50700800c0695625181d030611a8801400a003141100040160030050200054040180c0090423143d010740c0703e0314020b44440b101d80c003e8909582000d0140d20001003e2100100050141c48008a014004800303841036000b070a40e10341844000b02000610505410011071045c0c807818180c00b000c10f0200c56105070b014040d00c09901540b22050500042d120b0400b260181d9001120f6960b0036521490800c10380c1d5405d4401340c0d00500710981101c20135030001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 92808255 1250 92807005 92807009
    0x1203010801020703172e0302041e0f060803070f0309030f110306070815090a0f020409060312020111030403110a080a0c0b061002070306051e07051803060112060b031c0207 75
    0x2a170f4004450317040700d0704420a01000e03500b81030117001c0c0ca21502e08240c2140800b800c100c03081030503d0140c5559400080468080c00c500c140c0e198141c1c0e09800d201043c9201c0c0303800302d4095110400101d03050480080e564060010010701811001c000c2d94107141c0030303d600c03900555001400c603181c182d5503c0c086481a1001c11640c4c00380c8180c0c404030320294003801400f4852400407808401c0b0180a00c10040d10303d4001d4020004c00b1341d51700035a0308000203070009001034014020046201403943c035014809a010100800859252000e003070807580c0420304aa41050705860600c500507109103001c0c1c20a860715800600400c000103100880325000345c000b40f40103009205000c0e480c0d40307206c103003c4240c1c040036641d40182c00c032080600002e252035000750742146180303005401503410b03c20001031409003a00c600700401d80211700c110000707403140c500310070380b410a5024040b19454035041020f410aa14001000035031200081c4e0100e840c1080010103140d0490b4000d800d000c13103942c01a4032900d00e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 92809505 1250 92808255 92808257
    0x30a020d06080d021b100806040b040c020a05060c0a0801051905031606110a330603030c15020a08040f0305070203160f09050c0901030e070b0f0316111507021203010801020703 77
    0x1610310032141c0300c0c1c5c540b0a00059078043c0c00c0105500701d0341c0d800c07201200000e004a031700a540d0009024a03455500c82c250318504039400a0901441d182050380c5401d0008000c04c610101c00c10040b4070300350341320f81c019044500503038400d0044811120007902004554014036050b104030004441e0140c0446110400c4407416219079a41485100d1841d8959800e41d0000d0200d0108a4164828125100d110b800540c40c7c940340f1501c11282008110540f036941d402075000030300b081d4064042c02541c02203000e2035a01c261b0114a042038010380a0130b40000180f000c0c5c070001041190006060041e001c070341080d54010705643c8a44407540141034404814083d00001440c0594007141d044102c3c031802d030007103003400c2c0680c2c1452507030401100548000e56a0f0b80705030207503642c00540340c4400c40241c428000c1c25111f84e5180d03c2c000341c1d4400825012441039042011224414114502c0410944503d2140d2012142c19a6546805a00d01020f10702c145400c0c000c0040001102581903019003411442 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 92810755 1250 92809505 92809513
    0x61a0103050705090d1104061206020306010224040213090b0a050114040207020603040803042609030105060d080901030c05130314120909011e030206030406020c0105100602070308030a020d06080d02 87
    0x82c246085a860050042c02034002c1d014100f040c0205546014811542600500101d011512160401c48c1c810420004840c556000300502520b0b40e01480680364011880d20300d003099018650205010f5031011380043c4c0102c400110300d20016100d0b8003e0001c05420441c01d504c10300b4408416001000244a0040d005481010310111841c0600840c0d04040d0000c0c0303c01d0860f00e0b141c071a0416540b0240048a00540c0300d01482502d5400c008903122511100c80c0705602e504150f0306241c2036034401480d49128220340343d40707140000d0003101903a50443c001c0c070707000400b600c20b03074030a4482d403042c2e1900703580391100e41c0000010022001c403084440c0800105a4100c2081d80f4295449809510440796014441e0801030044804100d50118030607060121090102e9490300412620b40c41130303409452041c0c00003010000c8403801d0151035000360200c400b88841e5403038110021b4441e03110323000003080c0c44e1000021865100e502c0e015958070019403041004415521010507544135901c442010141c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 92812005 1250 92810755 92810761
    0xc090405070c14030f0922060806040b0c0a051c1d0a03030f0c020606010f020309060a030e01050f0402060d0e0c100302071505010506040b0306012c03150603070e090a061a010305 78
    0x7004020b96003402542500c3e241001d1ba201e040140f1082151516010780e5034140012546141600958005056036806000c150806080041040c0802041c1d402100800c104e118440350303021044981e0070f4004182c00b040c400c0d403140c0c4100070341908140c241c0025445041f040100001003410100a4440e03141048010046003042c0c042d5a4034241617009071f081680090101d50042070002c0c80c509a03071043d68a8030101d940001d00f10780114802c01c002982d2030800c4181c4400900c81e01c1d41005844440711458134080c0c1c00030b0100e1141803400300001d40c03240300720307401c1544c1001040e0140c100103110801441106070000c000b5005404155102a00c10a60300b1400220b840350301d06070380000c2c1c00d65241ca824100c2001c10f55001a21407810092a0001c1101c61001c00e4440d0302124450800507148a0195041500e010040001180c101c0468011f00885a80c002404030031038407000b00191080d600c2c4c3c3c02d014288000007901600b0a400c0c03000d19041c10000c1c4400710345e280702c240c80030440740c1c0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 92813255 1250 92812005 92812043
    0x3020f100612020f0105070606080703030905040b0a1404020408030f090405180a03080c0d090c0f080102091c060e0303090d020d05030108031806040503031201030c06080417030c090405070c 83
    0x6040c5102c1c51014802c0000c0e10805400d091290800c840010304295160800c907646e20b200f110100c1d132120141e500400d005104042c3e05c800c01d50001c010803101170282905420001e801d5a46600c0b4041898441d1030740c0d060113864540554000b012107400356a1940324400c1c4e600e1590380414011481107182038009501010095111400f00c0c034101c00510344481103039029942c43d075001c0c1c0101d5030900c00303010360342c0001070701c0c0190b040240c8a2011422131340c5c58003034000e803096010340000307104e0f0340141f00013480c9031101c0c60411003002c1407101482945905003402401004280d0940308603010010800504c0007000a132555250441e9088400260000c0e8085030b10780001c0c0680c09841d00704004801c0707802d480a020540b00c0400030103075441c00b55a02c3c0020b107103900840140d0b0910704418010020711041014620081905092820152405a84001241503c035050741c0801c480440072410f584041001c0d1080c0e10b001a10030401402e000c0c8018000450007182100d6074011007089803031030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 92814505 1250 92813255 92813261
    0x60604060b13030303020d020909070f020708010204061202180301060e01080606060403152c01060602060c0306010e090709050d0606090f090b01090b0f03060f010e070e06040605090607020d03020f10 87
    0x4000404642c01e08900390f90b8100d02a41c0503400c00d0008030780a100030402c544d075012205d40a500306031104040e100c0d9049010381040790030342c04007030700741d20500c02000440c3d0071080218104450450041c1d84904da143e03072044c0c151500c3c14494066190400210743c0043c01c0d0038150607a98070348111902617480c0000c00415110b2400000c0071025001940035001d100f81c0c1003500c2002000544d000900c03105041038150503140c40301c0c10900da4561500304141901803002c0c6411109155a032480c0d0301d0250006044440c4a2010502540c01c00700000c00d082d2041034100041d2030f0040050304098140c0c20040c02810301e0340101c40032903150001040034012039110b00700e9030039401926103e481c1c7c40e01c0c04d110020126802c01a820502c0143d400000355030520841e44501004d900320111941041c0c03140d844990024600c0341401800c2d80c00d200e440d030b00c0c4002d5908031441441c08541c0c1e2510a004909540100346000390051400103800040507004610b80c003030000404216598000e042020700e0507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 92815755 1250 92814505 92814517
    0x7090501080c060c011d06150109120f03050c0106080714060a1d030a0206030a020a030b030706080f1003120c050c01050412020d050f06041406010605032202010e0a08060604060b 78
    0x1d10381c0701030512110b90800074083c04a0400703441c000104c030085400b0703160300e1826007410352400c0d030010740410414142d42114070100d0042841c02c14880350a080c90f504100e840b9034006000b2011410710b0702d042512800440346181134180007032100ca99100025581c1d904a4041c0b07408102689400b0f60701410314a040e101c0f00d0002d43c0e03034202000203c009002c403482240f025182c041c094441083d000da22074030001c0d40140c8440c0001a9543c0d03a5150090844800c03448092003074014180c10000c1c280d010303201c15006020306d4012112078590f80355a80400b8502e81c03006011414040300c42409503041175044003c203004000750362103d000c035401141d907031242d402101c0d400b03402900601c0c090300344101c1300340f0310b1841003084601d8494216141e81c0342250854040380c0412004511070700d129010322403980102800c0c1092415810241c850300300800740d00c0ba0308825807a07420800700030f42e0f215442d4040b0310b03c00541410b20180c0c81d10f10140c0c50301d108030344241c0908d00705500054525050811200f07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 92817005 1250 92815755 92815769
    0x40209030712050a030f083709030c0b0c07050a03030f090b16090501020d12020309010b0909071809080301090509101b021b01050901080a091e0605070305071b06020c0304060e0307090501 82
    0x400303000c0c408c2200010001d1440440749207030111880c10719400540c82810307106402030f100d05d07020395403914010503d0140108602599107050008100082e4006084c4428551504000c9244041444c08000618035114040c3c44500e20509002c0300c80c4a0300c01c0305211400c1541d40e11401a01c410042e40d0b10f00711030569400007047e405e1005940e0b81a580610b030000648800460540e90282c00501240d0003030b00c614480c0d030440b481c10000d401181c60042000c0401d01c000f07200e1001e0985400903907010500c00d0900d041d0f103031400540302041c180324090006074140b40030081c080c990440d80300c06c031641c21503240261240c0120217410410241d002888400305a503070b24588003514004590850000d0700342c0c00c049846000100015011546600c0c1040d148640b00c0103501050400405941025000005240c0340005000d03a4581c8816000c003551074400c3c0c420740c03502d811300e018802807048440c1003005000109010682640c4091600906001107040318a00c40c3c5844164084036002c0c4914a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 92818255 1250 92817005 92817031
    0xa0207151b020706021c090e07180816090c030b09070e030d02030306100e130204031505150d030806010e031629030a15210201030501091109040209030712050a030f08 73
    0x15042000c407410038081e44c246c0e1400e600c89554031001703013603001c1c01650450041803a4030400c450801080c49104028400030004107882e0b00259010608044140a110b00480e1504040c40c0114060b8001c4902ca440240818900e0314104400a288600170302c41c5501c24080d02003400b03200d501c0081502e0045d00e00070310190520082c80003e46012580780040340d000f20840c0d10401790000148060001107004107950780d1510003041e150f40448034010181c6503001280113190080d0b403034a142070011541d06092100b600d407912030060724030305108000c0c41e41c148101d052603190401c0511224040354000d0300584188501c11000c101e05005000c0b0781d02a0b03074000e00c00509a441c0c2d54105512807002c0449207030440c0c0d2201901080490105088900c1c4040683c9001c05c55905108041c0180313050001000030261041d0590784511501110b02d11443c1c011407845190b650500c0100f00500324000b0002c0141a00c0c0ba041e03844807507050040d00070408891080c0d40311400f40000c140300e807800300d01c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 92819505 1250 92818255 92818273
    0xe030f0109020f10031103100602010b010908030d15091d0706020102090303161104050c12010b09010f0c02060c030301060207090b01030b0d02120a05030a0e030c0d020901030305030a0207151b02070602 88
    0x20016006407110104c082684520726600b01d0031b02c000084d401501c9954419147c0c42c03d100b4081d003901c41c0484002d04011543c103081010020220a1b2403000200d0340c000f203034082691600310582102a0020042603150050400341b00da1044503070b241e000c036110242c42c03426a8690040c1c0c202e018511486425810403c50385410b0100340c003100c05070b548114007000402c1405000310307040b03a408507101c040c0c0c1e50b4009040840b04940d0041c140c01030042c44260717032400c01c001d00000d18400a0b0104c400501c00f80100c40c07000c642d56841603484038041181100d44a41c0d50f08002542c03440306125020840341341c0065190594401d000da400c05031b0010b01210306000c255400e10205ca0b47c0c81c076507483d85000c0d10028500090041c0000d00302c40d00281e42c3e072045804410101401d00c06095001482003030104110b40c0180c039049900740c1101c1c0c15041040e10b9945032001c4001a01c42e9001c020400780c070342e5142c0300768560241c0c054044240350340031920220003003010590313841155001d990003680c066150 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 92820755 1250 92819505 92819509
    0x11060c0301030b13060504120315060203040603020d0209180f010b09030604080901110d08150109080c0118030803040503040e1305120a0203130b1b030a21090b070e030f0109020f 78
    0x3029070000d04101425030130600c0e6868003c11204169411286d003042050403890165060283d894025100b100c43c1c04921b15101c80a50b4912440c81000305154010822081044030f84e070550760681406171880c003040f0801c88110020401c2101c87c8400710364158000b25808180409841c80c502001e07000b4029901c2f251515155030b044007401504001e000c1464130f801010501c180103031b1a0035501d881030355040c03003004006112102e207040d6042003807003642000156000102000408000c3c2094000d850b01d08a1140394010146c00c0941282000000d100400100000800459040d407d000000da141c88191111000c0a1034003c1c01980c0400076440b654004280140500041801200e14001045c0d0f50400c100d40d0700c0e800024036030780103c2c0303003550564940c00c1c48524a0094014514000000c08040c01041d03180c00341030035000903d41c0d00400040990b0040c1c3c05550091400c0c107440c030b401d0300700404a05401c40c601d4028001c00482d900c882005004d8a007640b0f0340101680031051520301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 92822005 1250 92820755 92820773
    0x303081b0708070c0b070f050606100801030f032606030601061418010e0301060306020309010f0209011d0105130e04030905060a0f0c02041103041a060a030209060d06150902040611060c030103 84
    0x40c20703a40d136103141200054580f43e040091031030500c0f4071200010091113080480c00d0810040c01e01e80580139440d44000ca091b809900941981ea01c42c4400c07801c1034050804545c0d0043c2560030f11400714800c041c50314000d0480406610402040f170071503020b42c0c1c860304111011f81150b0032481c4c41c8503090148070342003155a404810345031030615080209401500001c1d081d00c01640c015542164000300b44801c001e130a008803250726072002020b510f0108601c0000b004100c44003181030b03406000d0f40c0c6401c076607031241c030445d88605805902104829114021007a402c00e06072805c03400320b002e8030780c00610350525030180d8800b04500e46030281541d2400030156000c80129a040b82d01655035408501d1a40c0120301841c041e6001e400201c040104014018107070304000f503c80c600c03c1d044003034108016503c12080c01c0c2d011106460304100c80a00f8900032004d010300c05505c05401e004681c0c08207805505031f001d40f04544c4a0340e83c0b2001120004030590300e40400345d42022441e20304000500104000c81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 92823255 1250 92822005 92822017
    0x60504061706010c2003010f020f030c03041103030a0801140103050c0904020d06030c0e01051207050f040b0103020c0703151103060a17030c0304061809022106010c0803100303081b0708 81
    0x8140351881a4072a0b0700c508a285c00b00850002d00d4041c0714081d80c040c1000d02c07440d0310b00d654000b01186440c0c10b0340000c85081c0401014801800000400281003008030300a0790055280503044a440c0e50100f00061f092902c03d00410f8840b89024540c541a980b181c0030345400754000d115001d2400e82c20409001c065800515646c0c40c458440718000700240301c4d095500010a0158a51a0154100801c0010303003946104000390a5101001c180001e94030101c4500d81d48504680000d6652000b03001030b0003902815250018070700900b0000424010a05d030340308106034100c2c07401c0080d002e80c0808036842c0e02040c0c410729000b0a103940306104554440c402141c0038ad0308501201d06000c40da000c803901d164000d0b0003110016458520000b690800c2c002c0031005812405415070804425074a09209102c44c401088030f0103401c1030220340390340d01942c06a5082034102e482d0035a20b2170801079802d0303000700c0c0d440100c0000c0d000341300083e8104a140c1032011401d0020b40b14515154051b21303024841c1d0009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 92824505 1250 92823255 92823257
    0xd0605151905040c020319050901121803030c0c05060414011b0909060501050c030a08100b0c150105030c06041703040512010b030c0103061a1b010203040309080706050406170601 78
    0x110348410303081c0d5400015000e203140300c038910340c01503090a09100c00d541c20b841c07080040d58811b119541907200000708048a5400314640306895100b5140101c40040c000fa85e0101030b5407801008407046101d000c805949280031340c5050045c070104d10360071107410b0545c0c8406080350f0409000b1030700003042d0b10340006000c42020001301301c1d9150f0000310340c50801c030315020f0720100301c206800700140c040c0d80c06008000d06007420300c02c3c01c0c003900e40000c9481e031203180900820090918002880f85102c0b02d00e11000c1c0c00046079580e100c99491044e01e645074510031040c1104114200001018a400038454106803c06090182407a1400c864264142511204520240014803000c11507840c1c016072502d444003848008510b08610300b050504210744241d6480c1090304011080c402803c1c02400d14070f0988818210503952000c4204810010026021a440d10b500000500c0203240d40705070385000340c0d80c2c40c00503200c0c002c0c0d0f43d12065a00384124410302c0c0114008181c6485103510081443d68030201c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 92825755 1250 92824505 92824531
    0x30504141603120201020712080a090501020c0c0916050a0f0903050a030804021e060901051c060f0f0e01060f0503090c120f0f0303010f3602030103060b09060d0605 72
    0x6056501400d1100d450682030401da880581001440455a0380510030100d60000b186459110b403140511b00e40300300030980500140c0c40c041407010b513040e03100100031a040030086489990300e4101c152150b0f004419684114980f40c041000341c0d111f0041c002aa802603110703186031001c0e000d801d84403040d01070035403014016959400804618240480c0241510a40e10144a450709204019040d951894052000a011400007040313446182c2110705201c000d00b0142e84810305002d00c01081c40044201d41501803c011000402942d02d041e0341085c0c5e052900b481071019141c04200c0000c0a0034411140080e6030200c08054090080c0c2c0190780207403116007039400056115010a001b4002030303a51611070350080c582c4092020040c001c600b0f0400800000d0f40c6103514000000794800c1c410b009a14002d000c801001e8049194218940300d4440d0340c03444403000c101500b8200d00290424841980c0d8035042000501040c80c145100d60320a1b0401000c2001031140c540f684001030200030b19141078208 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 92827005 1250 92825755 92825783
    0x50a1d06100c0f030e100c0b0601210e0303071103070803040609060b1f03061203020c090a060f0311040f020f030423030c03091507050a060b0f130212010611070303030504 75
    0x441c811801a402d01035121a100142c2c05402d00c481ea0120606c1c0004014040340d0620000e0701000440c0e0304075009103000d4138003440d41c0d00e40c41d070039030281070b1404d07a07070761400034014052480030009c0d40c03080b01c03a5202ea0205c45200c078026901d80c4075010b0002c0219200700000340c005500d07940403995071030181c0310004088001402044400d01210b20468440010a00c00c00f2502e80c035016101c080c1c50181c6154030300300c1181d07070042d548246103507009201c0e44071032000407550350481c0d1041009146a02d1038000d016070700d0400642240c06001107a004500308090202d41210b5402102c109a080070500351455a4079100d44031407070440000a9141030310440c140041501c200041d10341e5840d440055a954101841042032840c01c100c0010030200c0180150030100703a001c140f003a0400c0c2c00020119100ca4080b0004000060354090140e0000e14a0440904040b40d6070181c10b0303007541050030810590702c52009603050300b40300c0842400c0758440b00d0113100080c131039040940c01030311980941549407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 92828255 1250 92827005 92827013
    0x26030706050916051c03050913060308040824070c0309050a0617061002030906031e010312031811060c070b0c0d1d010509010c02010c020a030309050a1d06100c 70
    0x400c10790341090300e6800306003c1c0c000e8034800208480140011551620a440c4145e010005003c03500800340520002141d20700042e20b41414440f04102c2031307401000000d4036444c0245441e0050300803440a44140200c91603100440e002420039480070354040300c6250707245c4800b100d100802600c00c0b010070100303040c0041c4076220466290302808040d1030304121031144803501e0403080b100912061140d10000d6400b0140303500801160035420701660310544d42d0b51104001d03100702c1c02d400546013154114400000902c00305222030b00d8901050b0b5010f02c2044140c0070007041e14054201d01501640980445400a141880003003203032042d00e0095501c8169100428000b503008801e414426411050403401002c0d4061000403405e051400382c85610b0080000090440c001c0c40880d90500014000d90403e580c011040341c0b8820740e00811803004580c40e4a802040c0c07050714401c5900510401001148041075011030080b00040d0100c4141c4503551201000352b03042041880e0000e2100380d0560070041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 92829505 1250 92828255 92828261
    0x11703120c0a120501150f020a021e0d050d0806010e0316050108070207120503070210020d1d150d0c020f0a1505060609060414130203060303071401020c1b090903030126030706 77
    0x3010048900b01c1070003c06c1002a003444000c2004030110340010203880c005940300455162000070004400040c039903e030021402427103103000080c000b0321940d0556400c907640540c105201c1c00e4281e8516081c1c65500c3d05150346c075950459100541d0340c0a04051220354131070118540d000712180704442035039036541d00500482ca031040094480c0e070030000c1c624044d424183d034810108905803000b0410014004070081414604108006501c0c40304800c010031070350703240d142c09213003060982c031903907103905a0030140f0060400034140e20150080c03008d502030002d40440c4800400340c0091f11071007100c52003c5d05034010070005000c194412801c1c04454100d82f600c1024002406041034800c1e418881c190810103140e02c0004e01c4c91007071b401001080307255100841500d00700c0e0b0780f10120a4140c2c03107420301540640a44c402004052040040392805901c40b420403424440007600c105072603480e46002e032516403000340102082c0f0390928030380e601d03405003c9040b9060165007506490500015a03581c0c416 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 92830755 1250 92829505 92829509
    0x30304120305030618070816140a120c050405030a1b0e0c0c070506041d0417031302180402010906261501120b0906010e06070f05010203011703120c0a120501 69
    0x341c8040200300042c01c08188410400804005d103510703510308094005c0c00e49000030503404000f640741c102e00150398060005481d0841d10440305030703202c40720003038000d203440c041500c0e151165045c610b6021803140a441294107640c4c000d40034018100c05034482d10b804250207041455000341e000310004540d80d103084090b0007203155001e070540d02c0740e19614080c60802aa00201c0c4200010802004180e0320a500b0040942c00020f091519558034106400d0000000984840f020000010000c4200c416100b01b400648204c6079490070040d03c040c04404201e0456000380414031280f030900000b402200c0d82d212440d5060181443c011109844052114098548414030101a4000415580c02400c4001d1103070398140e0401016a01000080c10910003030b2031681440741d55400da03412a11100d003141c2a00347c104068108028081c0390160007503000f4400c408000c000180520a00440802181c4512080310355851440d02c401c001d41060b0740c04901e040040c0110020301e0244546136020303143c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 92832005 1250 92830755 92830757
    0x41e020a0e120712170c06010602010e0708120403020906030a1506031205030708071404080a0803040b0c040f03110d02040507090302130c0503010902160503070b060a0f03050c040b0303041203 84
    0x846001d400510007944000b02284a07030341c10500007400140c0713400b40441c104542140c01c0d24074445201d001c620440c480c1c100b01030028010540080760141e0150850400031326803e0440fa01c00b03070355001c12034031007070f02c0186000c0d00d11040000704050300d016103246412550041c103480e000c40030355450450030f0f2804a614070790940c84075000c200340032070201d00c14025012810864034500e04203070010078020005210005000490344001500304000c0300765070103458540202c41c2540d03a5418000c5e0240c100711000c41d43c103410b010000380500c0c0300300c080e0342c00c551040003c2440c003030655440000d168811031b007140c0c201c1d400b10020005a40e4070302403a8000c80194a40307142d03c0b4110700500403c40c4807405050307082800c1840c020021a80001141d04640d41401c00580b1041c0820000d450200c1c5171402815522020410798248200d000322a806603404407481402da5a41d00c85810710340c620762101134216001480148a01e0506400c00070341c194008050b2460640c5410410030180002c0f40194 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 92833255 1250 92832005 92832017
    0x20903060f0610030203072115120b06012f030d050a1b0302031005040b061603020313080114070804030e060a03060303080c030402030d120e07090506100c03020c041e020a 75
    0x110380b07400e0454003141000d070245425403035480c002d032006e01108040d200c070396514060110700240710005588148071003010501417080055480703034848101c2d000c80100781c81c500803180106040c2d60003500707000c039940c104800301e42298601c0600304181840503200650320380002c0240c8442114244a0203100350007545c00001c03d100c400c4004440c115590703200206261042041c0200d24401c0071b1031804491003294041030160788070010034568000c2c00324400391090030882205c10143c0200140100d6645007a0f10201103951b20000b80c2a42c00e00300a601800c5070000202c0c43c424881c03001c250b80b00d8080d082043c0240940c4001c5030195018903502000660307641c0051040652020b049900901078200c0d02d0305504141e00002d49a1801c40450000d0006100858003464000d400401c0c039010f005c400c0c2c03411150707505405d40140034110b825511a0346405401e4007924010104042081e8065004007261a1081d00b4840280301c502101411580700710a0418501014001489080070340c1d41c0710 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 92834505 1250 92833255 92833261
    0xc070801110c370204090b1005100f09090209010c12020d12020910050a1205090607090902070b0f060a05030105010f03170a050f0a120905070f06030e03030a0c03020903060f 76
    0x607007002802040300280c2d10003040a450300b0f03102c0314210903450801c40d003001d000600c6440020020f19940100038015992041001030602d4441211001c50700140d034007904107844548200c44117a41856418003141c0c14140c2403044070032550180041020605141894a02c00e80300c204100340d503000c280005034001401121410740c05404404480241c01c2d0035410708403080300044a11503541002410020086200c1001d0351043d085050a180130f0403041200d41803000c240343c0c443d48203c400380d004c110002c2d4001503201d81c5100300c2e02055004031088203140c9038001c0d0a0415075016141f95030003200b901d0042000c1d80c0078482c060007400c03403242d40e8001c10301e5441d00013451000300000146000d0f0a01880b100950001c0c11206103055101d075240e9104d1000105a4603c42400c0c0c109030207501d446000003c1020000d000c1302611405c0100710710255413131500300d055030a510070354001a0024000710710502d05a80007208010b4440c01e016041c0110140842d1401e141210024a403003105014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 92835755 1250 92834505 92834527
    0x40f0218041707030e0f0303040509010e0403030b09360f0105100503070e0f0c041701020901120501080a0b0915090604031803020f090618240406030201020705060c07080111 76
    0x5040c0251400d040000c0c03d1180c0e60b1009041d02d03039028031040c060843d0f80840040c0741e0742482114041d000c000c04c0703404d4550f1501e1900f000a4070848044020034074100300c0400038540000d185228541c03c1100088180c00e464084010f00c0560960f0f40255200c4029103406c0d82c000c5c840f4610945001d400011107242000075420505803643c4080e009403c405800d20104244003600350740440c0398221101151035160038420305214030b41c0000f050099032004840c009506400030b1124840c01d9807034a00c440d68010000049910a02c942e02043c0e00c02c2444000190f1901110b80d801440311064540c60681040b000100340000c0f00e1250058006104000805801038030911400c02d5000d913140c038071800c1d5800300e01c0801101c048548158070340000204103981e8614660b0324140c0c88003001d01c05040440e000100c07920380e00400e001a442d10700340e140c4035003004c1c4551400c0700d8050303000b010200c1c0f52138103101c4a5441040e4602041c0100c03840410104401d0003206202c00360f080d101c0c1c5e51030410101d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 92837005 1250 92835755 92835773
    0x303062318070c0813120807021e0f04200307080f0c070b0f0919120306050415050103090305070507080a03030c02010b01120c0306032a0503190803040f021804 70
    0x44218a062041c148282c26a11103450220181c1c40709455075912a002c1c50a007905c00154002d45400c2c0800340c0e00c4007007002260143c403405100b0341c1d200311640d1061146110451742c80740099044810716865214502d03081e00711003010201c0b8198100c006900484480d0315500488500000c980c01d042440700c1141302000440d4010100700740641402900e0740e50304c3c102080a840010000e004a001c20802003090104442104c40d604403105d005c051450b0100081544041c0400403e24181c800901d0b82000d00414030240c41e001206420541841c005500030024603105a0800000f40032400000f10b0400c0b03418090100c006c01031001c0c80c000c2c80c0040550b07499000d0501164100702d1502c0c2940d80000c060040544c02c03000106115018110480c0108500ea00103040c0352501b614840400f054141b8091024040306001004691104d062640c0c0791051102e038074000103400f0301c0340013180784d0760051500a88a00c03001d411001b20307900010300005900c410710350345a2061381800f0030058080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 92838255 1250 92837005 92837029
    0x602070201021e07090b120d0e0f030706081f0e070305010305010c0e030a0b04031103181005030603060c0c0a06050f0a0605010e0a0506030406060f03050d02010b03030403081603030623 81
    0x20525502118403c0076840d55480d210328282517445440c0404240c0e00c6aa0111104900c402180c110502440b0700505410340c0c0c0204500426001ca07051032141030100780d840036a01d1a446100c20f0351541d26107900c054410b5490101e111200410104d00750f5a55080320f801500180e4001c6481c0d415824028210b41001006c003081c801c1103c0300341101d45010410318101600461100d82c01c3e59a401c040e01c0d070f030184034a0040c1500001800f400512401c110301180050291412003080d0100311094070503120607100c4551541c8800300007504e1103400340c0100f00080b00fa07400d88140c0072003079988405482082d01c040f10004440710810015400303030b10600009107000d280030b66004018001080115a440c003d00d80a03520000018003071100c16001382c4028040c981c10328131580d690b818140c5e20703500b4050250005509001c03601140d440e0002c190303815280c201003102c1c40c0034403600400c1c900c1c64000360100c0c00c6c55141c810020b81e174a000b0300d04240341c030150070b10b10b0001b191810412212018107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 92839505 1250 92838255 92838283
    0xf0303020105060d020f1e03100603030810060504051005090306010603061d0f0112030e030a0506041b0e07030905100614120f060408130f061d030d210612060207020102 74
    0x440c0030151b940c02203031100401c0c0981c0c072031001102c04003a807402502c508210301d405106000001d5841c4285074803210481c0c0c0a41d584021940310071000c9003081916100340000a081440180a0382c50300700d03c890007200c2c45041251a10345058042800c0c203101b6440740c1d012980e102c0c5c0411aa01c0c05c00b00e03003076007804e0311012000d581c54800f034001c0c01d11006002d401d51960803070000004060280c81040910300d4005c04640c0c4070303042441c2c40e5940d600110f43c2200c2d0001c0146107160b00c52010780411091380c0141002c004a5a100d40c0120003e00c1244421380b1144103000d180c0701d02219510078680035080703c3c1600380d28200d0b40c1060007802103031240c52170070981c441c801c6003640c1400801d52503042070b40700441c07a03a10010301c0d811180038105a00a200f00f18480d070b1000170303001d03000240307010034803281e28034201410b888604064949411400c618085040310340290075008080c500e42421231100070f40000d0b00c07512039010048102c1d041d481283c0a660006041c01950f804001480c4d1903018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 92840755 1250 92839505 92839519
    0x606090f061906030b1e01080712090818041d060609100e09061b0c0c0402090312030a0509010c0c02011b0c0b07030c020906060f0715020904050a020706052208090301150f030302010506 81
    0x41b580c0020501c5038018105402c01145130f00412640c0c846d600301740fa606070400e50043d1618800e80c21130a0600164000c54411031401c641b4051181070b03071144256000302c40c4017400352aa1080117018034078000030300042039000200b1011504030b150031400c50190803000c00800f0b081c5814142440015030081d011200d450b0244050350005200203071004101c0700c01d542c05611424880e012130301d0328411035100c50f8526000300030032018150391b511640c410366003c1c00038007070b0904d680c0e8291074002e590a00a030010b04101d58101c598190031401941607032040150030030303640d82e5480c510307030f07940014608600007661405080198500128000c1e00403000301d0f0800d2900f2100103406001c0d12414a0040800b282d202c0c46803083e4000e079060b248811400740003802686456640d032402540300410495549160001003140e2015221440e060b40503110240201c0044544810356260441d261090f455903d9201c08245000a20200402000e03500c442986181c1113280190940c0c000034021030160030703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 92842005 1250 92840755 92840809
    0x50a050c030f030d1505060f0a1209030807030b010c0b0c0a02060108010c0503040f030306030602030a020712090e070309050f0f06240109060e040b040615020c01020606090f061906030b 81
    0x32001c01201e003450a5213800051604c98081800c1043c2269400b59601000100b428907076481510000c04407040d180c0c0c0c840c0d503103aa20b1700c842c40465000b410b010740001c6000300003a881e140280d128484100050510400040880d036941400301c030101e40c11403080d1004108454000c0c0c04210707507805450f2000003803181c20200c00d4001c107a400020000b40107088071644200503d8042d51058010f5a000201076680385000380d840030281d441641c044546803200d110210081e4401c54158040c1d0380001d00041150b00c0d2800120301400103640182da143c05460025203542c6401c01042020501d1350001c0c020916004403042c90080c034240141c8004245042d1880090703a01180d030700195400303410f1a00d41e00c0b1030000842c009221b5040402d412500c1c002c000315201d107030000301104a003000d608aa058102c1000121307140c000a880840d0080f07010300c0411030712001c824070990300642c05002640013241c981039006540c4402e501100c00709907240854585803d264078990326030740f0b14200c0000011 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 92843255 1250 92842005 92842033
    0xb0307081b0a2102010521070e06090906060309010e03031807060906090b030a02040b07031101060503070e0114060f070305040614031e090c220507090e0f070c060504050a050c03 78
    0x38902c0b1a03001e480c510b1010310380216800384d07041c2e4403490007100301e142407000c0c0440d0078000e00200356034171340c0403609d400204083e52410ba0101c80c50741402402a01003a01d03104140001504054030010403075407191f209142d140401c10145d031140055240303030175400c541e560450341429080e410203c02c20200c1103083c06031a4003e0b0300c0e14103c5060480082c0d483e0343d0114514000e0046e50041406090005074a605055001c00c1450003501c10f070008000305582c400c20141d6450580c4541102540044010804a0110314424805030300244c43c1d24034056461080c2d034031503070200404034080b500c04101400f54541c8010340340000300a4458480c41c6041c1090840501d01d586054419203d00c0072000034180d0740305102007011814090401071400e42081c8450210031321100340105660304e400c0005651611071945c40c01106c12010340b03013080d51200340002004000080421062006013240720001801d1407040c1403007107006001803d8080f00a25040d82011690750040f846a4403030381d8403500038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 92844505 1250 92843255 92843279
    0x304110418080a090e0103030203030912030613020705120f07060e0a11040504060b1309031206030305040501050c012d0f050601090611070806040c060f03060f0e07030b0307081b0a 79
    0x7550040710303694450751031003400c48006a150700281400b01101000004051700040918020107480782074481e5880c0d181c1d5000c0b903600088603169032000d4034a4004448446550080541501920581d07031382e01d02820b60510103030701c45c041c1e13001c01d280001a04010701446100701100a603206018000207036064881805604200c032005110b982e072400490100426544a00d0f8655400b600844540d515800640004c15080c04250042001003601703803a00f0829108400540740d0685500d4105030400c2c00441d20383d040b0550401c1c4640d80c0b0050b2001091103001c00004210b100c2e0301b061780d08070315403001c402520020322401004030301745800e000080e82c000820500391395003460001c036003440c0c200c41076140022039403010000f401010b00344401c2c0182600c405040da05182c9030f014091030407035011022196507119040b41000444c9003130102102034038000760460034601e0b01007410301e844400281445030543c04200d143d80484c400e04d0790a00718000d00300548030304550b45105245800a183c8507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 92845755 1250 92844505 92844551
    0x50103020f09090108010c0314040f0602071509080405150702010915031d0307120f0c080a0302040803120405060c0405030618150108010b15040312080402012303041104 74
    0x625801150074504400030209584542c0c0009024818959443c81560300910451060394002400c1c5544550081003480d0300078069540140d06440724400c0f91200c40013500020412900055018502c0c2c623460200c3c000c1c59000ca015580389661245040d00f0880c0380c0c0500821410001414018030001d030384c004000d2030450714039a044001c3c0100d041e00440c01452400290300d034054034001d0030030110f94004003400040e48118402140c85c1c01008007601c00c2203006100c0e03000600e202c010900090100b03006132010500904004d81031070344668800d030840d004110004440d400341c1c81000b003400000c0040f190000103141d1803518040c10200400d0300e402004040040341d01c070840c0c403140d00c1c11041184440048442c20303025440d503141e5481c140607006014107144503900b4203018941c0c8020703080c11502141d505c603481c81d1200015500503145088024401d034144100504941c0c0100c9620700141c0350002c1d610901c50303a0b803801d0310b410014114003010b41ca000d03502d00440c88069805422441030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 92847005 1250 92845755 92845757
    0xa050309042a030905070b0d02070c06090b030426030403080405060f090c0616062301140a140a0503010515040e07030b04030503040f0819030b041401050d0305130b130608040302070501 81
    0x280d144090070a43d14001c240c0d80a421f5444002444005105803503014040b401d02c100c09915907240d4408049074480e004d03025140d401c0001f0400305000460010503040040b100d030324603c94101c02c40c078162956030821142940802c000e0070070801044818490140c0c8910780501d185200d040c0075449aa8650700e03100301034040c07480019503c142c3c001f070303c01101510790700010034410304074491826500b8801e049400e00420500c02c2c0046040368903680143d108240160890071810f14081122080070303602004607400860705100813509480a028084c424004401003421900380c1d102844102c940395078600906030025a414000240c0351300b00141c00680510b4000e40340c1c1c503603040003540d884038412300400819000502505100c0705107902c1e035250f40c1d2601c042262440000601c01035520001e400464003807241c00502c05441e1035480d101000e4040d180050401004404051038820141c00c01100c41390085040040c9a55110000002d81090302e403088203401c00e079070007035510642030141e24 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 92848255 1250 92847005 92847011
    0x1050a060b0412050c040507020114070f050322150209010912080a05031906030c030606120f06020c0a08040321110303060609040902040c0305070e030c0102070e13050a050309042a03 80
    0x40904ca1300b001998074003840248204164200040e01038020714410307035054080300c4440b00052400d406075901800207080750701c8280c616581d02c4882440b03091402c510482d013200c0401d1004c0450b410915814400380c2c80500140c2c1c40540100142940419500c5004407113280c40b80700000865a4060b04d0441006003800b9441c0e403111041400011079075030744d101403146030803000011301111028a0003264043c090400c1025200d4455015158003104040c06910000b042c800004d40617a00600c070114440e029948003031500c0d03603448110f510a0f03005954200c90b4003441c2c038190302088080480c842850401c00310700c203911080e1545a00000f085c50b0b204110118840b90140c641ea0001301165500a100700030483d500b403400742c000c081c1a643d12001515081030a020b070700780010030327150140c3e0503001490824a40b01001001f010024103660f841c0001e5050540010020040f18800a1040014540791b000b641c2c00d100c07c840d4001c4240300300310380000d842c2c0032640b000303500c4c80c000c031080385008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 92849505 1250 92848255 92848289
    0x11e0506010c021206040c05062109030409060801140601020a02100c08090d030206090d030e15060a091b020d0206040308010e0402030a0c06030605150708121b0406080901050a060b04 80
    0x181e90210000d0000f07504003001c44c01590340c550300829550b01c514030901902440170340381c40030320030280603040e4540c4030400c2c4c5400c2111404c141074a1564840660300850b4501601d9280c0c90f07040c2c480c03581c84a81c80d0b039100e4100029070900000b2641e03202000b0320041200284a0f00010440e0542161680c140040c4000d05014025954121107000e040035080b2003000041d0b02c0c00a54998081b1141c200ca07005212846114611038091102d400e224400106142564852925030401c4c1c0a09240e80c448070300e03040011094114000c0d501e566130b2100e1442207032802004043c0c2041000c204a4046402c4802007100003904400c05505480c00080c410140380d0319440840c2c078003080100045c0c00e812090100003100c1d80d050b001501628070684910f1644501c10580101d24016018003c103090310a0183d424500038803520280e010f200c08801d40c091908140c2c010300180d20940001c40018a00001c00001c2d040034054a900700c0d01000c000c00c109032512000304400e00990103988025400800c074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 92850755 1250 92849505 92849507
    0x715020a090e070c0807030e091f1403011d0c0117010f0303140c070f180203040b07050304020a090507050406110a170a030f060f080105071110090201030e0a0b0402030708011e050601 80
    0x4446450340d10030549903480744c1b9810060802d514045c074151068114030700060405949004001e01007080c3e46150b811203040000d00203900034101903407505903503a0700c14259a00c1004014182c422503038000741c4025091180010302c6444408040103c294240004218506004600c581165018500282602c50103481d40d02e581c45000340420461041480c08666140101102c00c00c40340c1c0904030700060914408604141d001c1100c0242c4039200d20000511114042c0006550051000303107086005625416150203c4000b0b03190780f0700203034000c1030a100540c0c00815400c4844070002c000c1c00081c0b01c0c0d90300c03c11900318240d01001526000310318904110f009800c59801014605c40510032151506c07041e030302c08165881140170070742c00d08002c290510300643d0303030b4103010410901420400980c00300c0080900138001d422410142c1d219101c00d000c20092050741045403103085600860708260041515180d039940010500340d141c040100410b10005c02400c0e4440d0f07a03c01c0108517a0b0b030f0300c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 92852005 1250 92850755 92850767
    0xc01030f0f0f06080f0f03180d08030a0b0a060e0f1509040207050a110109050306010e070c17030411010509010507030806040e0601030807060e0c010c060213080d0201020715020a090e07 81
    0x1e124550070401d100c501d40002e0380101060b94048821140100900e8001c0e5039502c250940b1686290410004580c1d154101c0c40702c0400808082d011220480c0107a80d004090350044581e100690358a17245101c1c0c92800707219082c002e2110340f070400240c840c554005102c00d1105201c09200e01144c03800d9510410802081c0c0d200c08100074000c5444120340e0910030748a40b2445005c40760000700d00c8251020390301034015075060700c0024004000d60303800c00c41c101d040c040000c2c0c41c660511000001c003d00080004411400321101c0c0c1d08540c0d200e04092070500710024030140c5c070724140082480342081c1643d0007001d4445650b010300e88200e40ba2070300380100e401440c118640d80c13118042c40002100340420b2500526407035100c0d400400152480400c200d4940d450100e90500040d030700700c403d0000c1031003034011f04848526000c41705201c0303507240c0d00300b458181241446000f60b5008600302c1d0610070355030b07001c0303101c2c299181c410b61602c2c3c4104001840b49659026910500c840440410b0f40b441c4161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 92853255 1250 92852005 92852021
    0x50603010b100530010501110a02030a0c03021008040302031e0903010f061d040c1814042103020c0a14070f03060603020f030a050d030f1103010f08011d0c01030f 71
    0x54140c450801c40140020400d92101410044e0000000c9100308504580782155403100c0700c00d02041c0e526400c150045900b0092442c030001e00d44a960758142c00340c0d805100480c1d039244105505070b8424510710511000d804240c1149080c041d1030010800400d0b00401141d080c0c0d141c1d40c4003c06c0c1c075001c00111a04038040c1480c00360b05503103010443d00701c100d80c42d1300c85400d4030112459500705908001181c0ba10003811a40100a400f1101c0200000c07142c00c420503c442c0b40258000c61000910f46100c0c1c4041c3d001c80f01994900008909000c15045030000e0351400c40061034150715021100031443e80c1c0e1000403130000d0034910400d800f4082082c0511400e07016103080011000300c0781c0d40f400c20710701900550005901c80e02c18511401000d280008070340e140c160b803007005080c00240c600c1c41500200200c0342c012082e95103035561011002e9004005501910341403820886141c03c0000490854900b00d9401d02c0d43d0f0003070410305001c00d030700003000802d14a0900e0081510440c255414010340000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 92854505 1250 92853255 92853259
    0xc0d1e050709050702190c0302010c0206070f0303091407050a120c03080d0608070f080a17130e0411030d09121a070f02120a0504090b15160b070e13050603010b 70
    0x101c00101c1c40d03a20035081a03000d0004c0e80c0c203d8400d060a00c90100360050308100050000b6100c81c0d040006500600a54594500040802d41007111390380b201c081d00070700c0000440010350345808803800c20481d10303041c104000442d0300a017400c070304040c0817417051910f07401a1307c100201c68421004204c2e00d88201c0300a10f03401032030980c03604540652140546400d0150600307a00034401c0120b0b96100711040f40c03088815107002060030323074103d469804c0c907001d04422240b222502084250801015541414028600211101c40b1881c1c00d003000d2000741c013601d0a40d88680c21051040d035225600015120a907072401d103400304030590a1600413080c144020071103c1d41d0004208010f6500d41058030421031a0345030b002e40707200500c0c014a030b1040340301e241c26010104d00240030500204005034041400400d02401d0300c0d40100e0440f450001c0c54211405082c604481c03041780b1001c0120b200c00c1140c00154904200310701840590004004050008092a00ca40d0b500000307a0256030075003110003e6000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 92855755 1250 92854505 92854513
    0x3030e04090203160f060503070f03410a090506010b0a03060306050403110f0705060414060705010923030c0c0d060921090b07020312070507090203090309040e0c0d1e05 74
    0x2214400512010f0394410b48000c030403a1140015002d01690480b803041302c0c3e030b542d50044d01e204440180d0040c5130040c041c0350b10382111141d033940349000301040c2884e0403c125514482c49041c0c840072203100d00c0200b0002456040403a03580000c0d90008826042d80c076415101030b1210400b20b4110000c1c55143d0016110900700000e00080c1038104c502002410040c01c00e0350703d0322000944e5a680d444180c81074a070480b02c200410400d801090b2055030401c10010101894005161112030940e00c0c106800e40c1c541c511420b0407404580106002522040340030061410111018203054803601c001d2810b601a5889089a0080240e40e9022002d20baa01040b00c03200389000c0c1000c103600c040003283e0b00d00407606c4900041400000c80055070200c65000b001000c4c0f0101440104100c1c7e0000360b0100c1e058803e10340301082c062414000346108080d0500159251080c0400300410b83c4c02044070241250890005074a15488204070848041c6c0c0000408a040d84410480f41d101010404003800c2801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 92857005 1250 92855755 92855773
    0xd0609060302090c13050f0409061506180e040609140109060b0f0111030304060c11060c0d050a060308070209040524010503010b012c010201021b0c0a061803030e04090203 75
    0x18280e001800780e034026035081c03031030766180d020506903841048000004a100d03000c04000314a1310903040c0c0015100900046410202542c0301c81c199082900d074150781f040c54100510207264440c1c03041444e040070300004900c1c03d1030002a90802800940050000c0e80c44020060611100d00200e413800f1007158001c0002544070b041c00d00003012140c0015200700000381c40d602d1150703c101800c860070f01c7d1204c0954038546031561814010000c8041c280203120300240e03e0f42c006441030080c40d00c032b24006410181e0715010901d54200b1510300520b65100b49160100500116800000366000c140c5d056503442004d840f203042251920003100c2040d4200602c0300d43c00780c101d05c0c207520514102ea02c15070003840360140200064568607503c40807603c08642c8a5190703941070aa080a0032000d440600005242203e45054115481400d80b22040c01d98415101d002640c1051424500100303124504407a500781121011808900540700250407c03e40180085035541c2d66881400c0c110783c002d04442c1c0b200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 92858255 1250 92857005 92857019
    0x3140d0917030a0f05070518120f070306060b0414041d0318040e030712080711070f030317090d110c21060a0221090c0d06021903060b070f02060d06 65
    0x3500403180300003040c0c10902106108131180c0950f40c002c0465460711410701000d501000750b2140e002044543c0f00c10a03050094000d001070000481c2c4410360b1000c0c1c5010303411403d010056032456401000300080070002000070340d0900480041d83d0801f1600460300000c2600c55200c1c1800c90381202240b8000091070740031407441e00080650240080e03030b0030310040c254110300ca9124084c00c0c41c040c0c140c2c24100ea00d00c4240384507000032944280e072410300c20b84606962040a2409150b60004954840034100510074581c03c150380d0b0000701c01d00c0002c01c0561501200b10380e114003102c55102c017070202000414803000c2040c0080061480e0180c480c00e4584c40150400c0d190442007071041200e8000c034000704080c00224001c4030040c0314400300004000e0b110000344042210001d0910702c0e03600410030900c0c140d0352070001c2c2c003c44500507140542c0b0790707400180280d1b01c0c4442c00606d106040c6841010480d0040480a50311301a40021100360915994008107c00344103051714440b11a20704480410a9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 92859505 1250 92858255 92858257
    0xe04091209170106030203030d0b03070b0403060f0b120a0303020f1c24060503011412010e0d0e0105040608190e0f100c0302090f040c050904020705070812030403140d0917 75
    0xc4541d05084107141002d18070071800c031041c500001c0d4258008102e0b03000d1054158022801c03d01d000b0b001c5079201503999a51703a8041d040340d0011903900742c0718007480300d1600302030092480109003150310310541446000241c0e82c0d408403081c01000e00d071700403c101840107406815134030310100c0724040301503599081c841c0c82d004002482c9881c0305441007900902d006440c1c01885000d480c5580c0b225441c43c3d0810321500610100c401642c0c2d403264003c0c25443c1c40e02405c0c01041000100c0600030304900b06000b002800b50144c0105050401c40184820442035501c02066a0444039040c2c07504004004c10304c00e18094442d500700104031344550948030701c502500050408800e00011000c0180e809020812030583c0308820311154081da6131035580b0280e2400c0d50203240c82c2581400c000e413818290501143c141e800a8900351003c1d048442c041090a0061140d01d050303440181203a403841c075203a82c0c06840410420500c1a12100215003444881e5840c0e0003008071a40184015210010882c00d2a0a07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 92860755 1250 92859505 92859509
    0x813031407080106150c11060708030a1406010f0818030403080a020610050a060513030c080309011b03081807032f0d08090d02040603080d0203041704150e04091209 72
    0x7441051400100c1c1c06044c0b01e03001c281c50310b0301020711440c01d0085085511100041054580f07440f072500d940c145550302001012403912401d942600da213406a2190102d50342002002c1d911200310702008101e030303400342100310304d45011f040155060312070b071507890440c054031812841a4400006c000c0144401c5a0180c2035082c040c5e8221a1075548403084505520040c4c45100e0b04003440c1c880912815001d50041c001042c1d0f001701c84d2425640d01d84602d500c0500641c4020351603040040c0b100c206503880181000250000222a0044005590004d01090000309030b00c2090005004540d034984091201e44000d5400105030f0000c1c603144d00b8207400700e00102d5001c09402600c8151711445092049154960f10b4110b510035003003800c9803061040c155a1601c1c2207038410794480f0040000340142003e801258409000142c0324a000e01c0c060040c90106507078038016620500c4100941c464040800400d40300510f045600000c100c800725010384404d640040148540e41d13444600030754041580b00c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 92862005 1250 92860755 92860793
    0x813080903010e0313090902091b0c01060b0901110a081912110310080a050a2013021e0f0f0a210c0e18010902070206071202070501090b03070509010c081303 69
    0x1720f255205424000c8490008000350841c0b6028001105c40b01c500750507105a007440300100c1d20b08005603d6041c21a42c40ea00520f2904101094200382540c4c0301d240e03208170044150050402a10304c0d22000350342c1c00b4840032801152420003480f000303548180b00b807410030000254184100346030300e01043c44540044501c0300d902501c0d48000994800e000940e02e22a5800134080c06a014082c0c40301c010360740faa012001800d100b2054044801c0c2c442e200c40303101210481c00010b8540400369502d02540d040c00445111400040c040500303c820040211001109004240d40c2e60309150401030b900480c2c010340240604a440f0346140ca40e038107640100514041a9948010080c0800100406003c42a0180400d042104014440b504203540101a00740c0020031841c144184c80d0780702c42c0c0d01140500c0900060304400c50800c600e5030006400130103001698030160440c0341c0040010210b00403104024104004901035205019900c2c0846014522008a1400381c640342c0c142509040c580d040110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 92863255 1250 92862005 92862037
    0x304061b0c0605090f0a030201020414030705060a0309060b040f1e0e03040302040b1f17090309280801020c1b06040f030b04171305040b09010302010813080903010e03 73
    0x380c030352a1403154462825490715100344000c00c0c1d03110075004200081094500d4400c0100140b80800100301090321b8910030350015946e14200820301809611860950740641d014100600c05503803070b20150345c2110060b140c002118201c60508102601d80c40c7c000d40e07042868902d801c0c4182582c0d03001003012504c1800c2c04030001a404400d00e0880340b040e5202d40e510b0300203010600061506400024084800410395950030501c00e800440c510070101146020503072000c500c0e41007160041600e80e021002802841c20b08a600c1c003c640320b110b01815034810ba20414160b41d29130004441c0b00340291000300d0086407070320385280144c0c5c0e42d0340d8411040c141d01c60030900c0508051400b541141c0540385014100e08030700e80385030b0f10019081405001100c00780d002c000310b80400c13001007000d4015103603400c054100c00c51500d02800112100b0360b91403802000388400600150f42c00c41c0b50b458118030b15640d0440060790509200f140d40c09003010440e403550074098a15403643e40040908503d501c441004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 92864505 1250 92863255 92863271
    0x50f0a0c02010f0c0b0a092609010807050306060d0e010e070b041409060d0b060315070201060617040317070c050a0b1e010f0e0709150816020c0a1404110f030406 71
    0x350384500c90440014428894880094919065501f280203034511645080310700d100000788681c58045500b03402042d402012610121543e440006641c000109080c00f6245042a070003048452003881060900ca82d100d80e8501c4800320258040050031034500c00391000e2603296080382c0190361042c41034031221003c0d024501c905261806031035018040061103c0143c2c0e4081d1f854410f02c60000308007607418040d0101042c0345030040201a803184600750300005145080040c0070f820201001d191003c0d0214a808100c000b80c0c01008041085200031418045550340341d0088642241c1e640004010340603102c50304003048003421482d8002d00201c5c02310083d040b501070700720f0f92802c000d20a400b11803500003c200082e015440a83d9001442031400e843e1301a242c07406a12007501c10b19050001800c80010000e08248440ba00c680c4041c4900c090510040508001503139030840b40501d0025090124510b410340d503c1c0d5020503804504018003d46420b03c0028058143d00704230340544506d0b08028070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 92865755 1250 92864505 92864507
    0x501030302011134080c0f0d080c0901081503030409060905070e061e091c120f0c1e05011103011a0f1c0f020301230f030616050f0a0c02010f 62
    0x307586110320700348014200d00c02140725684e5450b80754802d21401040c07115400340030403034080c001d0001c0e8411000920505c1c1d500d802e82460583e40d050b00c1410020100203000500b4244030444018008c00d2030700e030360030740c54600c040070810720000c05599040c800010001258203642d045502202c1c0201c0c1d080103580e9070480107503110040645c131640d02c4901000a004089803114000c40058580c008490400044d0004681d04200d404070030000e02c1e041c031045004101031640d02090002c0c951410350543c4001080280680d03040d41070007410082034124007540b19201c407541c5080650054002d10200d101810804500d40c000e0140c58030400100c2d00600180d1080c0b02201d489030000d031401850411540340580d08000c3c3c1c2403035030014540b54080054029224000b46010b840c4446003014240d29034803944000c080d45041c070300d005403a94086d10600da980440c0300307948020740300006552140b40010854079403040340300c08100740d0350100300e80310601d03400844880c180e031007a264001c501071a100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 92867005 1250 92865755 92865757
    0x90305010b060901020604030809010f0908030405060618011502011b0e0901080714060904021303200a0305060a02090102070e010605030a05010e1b09130504080304110a0608041214070605010303020111 88
    0xc200f5016a0094000c0ba0009120b02101d642c0003941000014440340d8404104003610150724042da180c80c03002c800d001c1172160510190381c01000c100c6465050480348040c0e1003500c0414407404a071541c415000e0b0408034000c1d040700c2c55089413000d41c1d4090100c0d0351740290034007058052150240c82c1110000c0f961010000301c49080e40d404502001d506800c840400203541d129101c2c90ba0490f8080c016200440d02e0030319100080c41c41902c0e120742c1e647c40e510311202c0005440b548944510110b480800100300086042074008403880805a074445074140140d191138859849034005e00803990001980e5540440170390f00610040c0310a1041781d0343da02020100d03940540c0c003012031509050312440701891240081c00200800b0700250400c51009440e42c0490f0300c102e03820b070340d080f000008104c10844103400b5015010360854a070040c45051031030041440d200104010801c4164a8484611902608500b20781ca604094007959902051030280060b120a1100310b01640c2808101d2140c265210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 92868255 1250 92867005 92867017
    0x61c0e030c060406090f0506090f0c030c060f0a030b0901091b090303020c131116170403030210020c0c1e010e030d050a08040c05150403031106040b0c1c0507090305010b06 75
    0x1d00420482c1c0f01c0d5102c8030010301040408035143e036040c080e118005041840302e94810724168000c0d062103a041c1c814942401e2003110b003207200e5044a00c46800780c0d52240140e40c03d1041198a2580b178003151042500205804005a80e004c00300d000002681c0e4801d41180203000414911138020a801c0c0380140e400090130300000b000b41e0891070b103281a50501c3c0d0300d100c10300390302c42c00003048407104044029070070f501071041c048075112a40c3d0130000f8415400c02001e0400f228800d031500d4503142d03032002034903071000003e8074541a40004070129102d8080000c00c4405c0002080d54203029505288041e4081c020280740e804a0078450140c0344520300400c0d40b1000008a07280c03540741c1426014101c440c007200a004513075140f101100400d00752207c1001d0a1464441e00c1050350b201c7c1142005044140e40d03442034001035214804000000b020f000a0903004844001e00a03100e81c42c051896620315842da03285112030f032500741000310060380140450110f80c01135008110b0040d056051007000d00c500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 92869505 1250 92868255 92868277
    0x30b0103020d0609061b11030a0e010c0501020910050307030e0a0b060d0501021b0303041b1505070f022d010504050915031e030d050109020316050a050702061c0e03 72
    0x1010040015061100340010705074852400010518070035600c0004450b28403088070079441e00c0180c032061440e003010341c02c049a038a00006505000c0711880c01030070f40e4802e400c0c0034100140c10b442e95041180c00d405031000c4200040c070300600305400e080000c005400803a001000242404d807028001c0001041e01c142c40ca400c0f44115009030b8030b0006021142c01034083c1100c0c90341d42041000c041e8141400c6810840350000055507403030516003000949000507800e105c0001c220b14108000c0300c4e5042110b079501c6132003030a00740e484d6122414110018840e044010f50071055140390b00203090106400182c041c032106852000300900c500044a4500842c010300f50010021004601c2000950142000750f4800408880400e40c80c20f07800414160b14644042403a0b04c00f16841e4042d4445010329800350440704c40450940c501014260620030804e0a072105001c0002100c10116215400f11261150080c000e1513807410307003100b051240004890110302c810301e03004c2da500070310f480401210122100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 92870755 1250 92869505 92869523
    0x3020d050604290607050a05030403050d08010f1809060c08011a0408070b03060604180203040b0601030e06070809120a020729031b041d1803090d1104110f0a0f0302030103 75
    0x2c3c032810b10500c4425024602c0e0320010502500c0700041d404c0040c0d860081c0710b100075545035880c0d0302e0501d140040142280041c0082c0320010301041c0b241c3c440003421561034409031042c41031100541c00061403080400b4001c0c034100040000b00603041000a412170f000c0341002c4000b101c90380c1502c03065014074090302c04aa04410000c2040c030742000055030700084001c00c05486e1541d079100404d00480c210051000c580e03000b00c200b100340008901e606501c48000c0c05c0c24071401010b8020720740c0b1002c0080400b03060214040200700130440401c5030380f10b04c4445400300c0da80d5144000003e0741d10040c511820459100c90100c1704401d502c01020004c1003019000785904503211421010388842c119140501070305c4040c40001a00c0c8007111200e0501e420782003005104e410300c89824010b09400c20f0314803c490780104580d0f85a078490307840c01c1062940009800b803c10305200002400381c222541c403a00c04000c041030246241c0da61600800b1002c0158a800004000100056080c1e010900c806040810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 92872005 1250 92870755 92870801
    0x60a09052403030d0504150f060e0103030c0606030b18060a0c0c030f12090f02040509010506060a03020703090b0403030203040e0106091a030c072001030605040218010c020d0f0303020d050604 84
    0x1245551500070000300405407818610008500310403a5401c83e401c2c1c81d0144110125040c64019100700c1310452140c02c021b020003801d20304503a80049040c0300080030000c14101c04014018181c2c04072001e503501222680c503909003d6481260080d040301c45040a004110200d20414103d1044034031103141c03500e441401c06159102960300780d80d0385031170b00c0501040c6c1c1c0c2c40e041081c0d09440341c4c02043e44240085181c1c01400c3c01800112900205524680d0385071006200c45641d49905071511180340e460302503955a07403460110348400c9545d20454010b98040303030100401d500803000d031042c1d8013031102c111fa60743c0e0384410440780038490b0702c2a1398000c050314560141d000b051800456000c0884150313245070007920354407804084040c4d200710703085001c0d414420410390b906000703a81c0141000c80e030540c01e0184140c000001d04411502290520440849a104648600e800b060505800c80f40a01108005060180107035200404086800340351100082c000c0c46e01d0b00c07911018003005044243d141d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 92873255 1250 92872005 92872051
    0x1002210402030a2a0b0a2312010801020711150d09060b0607150b011d0f031e0303040b0606070302030a0f050c0708160608040503030f2508060a0905 65
    0x80500103a8041c000d5110346804200c807010750000304100c442009441184111080130404015046000142d9041098402c001d901c180c4400002a12014800229800f00c0c041e800d144102003404490b103001d44000100c3d41010760180c01c030203010f03181c641241d030f5818040143d081403003400c10398511030034000d003880c0e12841d60180e03400d140300da40300003951516400012120741100b042181c0b018000300f0021a41c01e50340c081c650003000c1c00e081030b42c80d400404500074a141c241c8510b4070b008000199044145590030041c01003102641c4000489510700c05400035182d5000700c07002d940700c910b8003000c109682420801c40748020307016809036003000001e03503044a001c0c0301401d08400b0002c3c00d01030500c0d1395405000e144001c080c51030082034100020700300002600c803541d0281040c030600c0300030000400c50201c102d03580f00d034502d03c001041b5501c802c400105002c1403d246001681e401c1c4002e0007417038000031703894054042180c0c0c18102030341c2c0e50804402e45604403640d03842d00c034034151003242d01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 92874505 1250 92873255 92873317
    0x305030a05270c1207060f0c02131d01140714180a0b04060908010614101202040b09030c040506030d0311040b1318061d1801050c0a021002 61
    0x111504611000d1000a0b44011180d41c4842100b4545900518a00030aa140040710101c0389201c1002a2020303c0c036107030340600341c04200b8210205201040e00100110740e00c0b03071064112031514120400468110380d900c40d0401d0300c0703041e0380c103807540c40c01d52400c86801c03100d26001d204d0840d0340d50385944030740881c440e60001e400510008203c08101c5202c039880ba036900040b10090700207246034a4070b451810000420f119550351190213030340d140513414401d01652034161051411309682034400b81801c564120b0b01c41a0215240121502c0402d0200c0e010442c4c4008020118040f02110704003420801008201c650507101281c1c150b21202d205031000b406030f04200c410307021200400741040d5560b0b0b24a00613a102102c4150b1340d018518080c410304014100d02240d031000580104207003420149400c11f0381411002c000c0d200182c00000a00c0d4406c5000c05d425201e40403030003400582040140c0246680140c12400c0c05030280342482882c000c0317031340f081c4c07a00c41084e58069036104030780c881c54044c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 92875755 1250 92874505 92874511
    0x1b0b07110c090a02031012020d08030910020309150a020a170a0605060c060103030305011203021002090d020d0606030507050f0d02060903010b09070906080c0301061e0203130602030304060b09040305030a05 90
    0x4070300540707000002954581100610450340004050b80e640b501010350203031618103800080c10512481e0074540541c503408040381400d6403103c03145940c0e031508220149032400c001e151843c450300010402012a0b0701284540c44404403020000140d10b90038800410390045c85011400200350b15106c3d0260084255415040100d030305001650300d8444001c20b1095100750000304043c2d0080e13004104040d810b1190703d005010038204540c0d02c0800340d40013503e07104006a0546810303000701b0076444540d9850003004002c0e90090186245000758504038020700001c2c401540c0074003030714100040e6401c100d0300f19000034600800c01000c1550070b90030805103803c102c085581643d601c0500e8500e5403182c18a55006014503120b0749501c03864600001c0000b00b00034040050f0324401d0004020b003d402005030825269200341c0c4200110b0110400c0303185d4001c000321030318846401580080c86075004002580130300c0c000e1805000301c1d50202c082c889000810b8030010005902000003401d0342c0d2080d401550 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 92877005 1250 92875755 92875787
    0x40f0b0f0f040608010606090f090b011d180405010c08010603020a09051e06070c090b04020703050a0f020c030319030506031207080d0204030501050f0f060301091e03021002040e01061b0b07 83
    0x1440c0392104c00140c00c680d456082030000c40c3c80102d05208200340c400381d600c0107080c100320031306c140301c1800700080c0b508400e40b80408180d02d0180d00402d5940e10410101340005000145001d58038290a1850280900a650760b000c07410140011035414441d00894001c0c420a450b00c440b010310344814041c19680001410200540d415802440b0382e441c24000c03c15180501e800460160410410404031540c6002041c8282c0c4108405c1380066000400c2d02c082c1d501500308803c81d0000054160b003408403007a05290705020026036280000720030b00600303540980d03d41e0100403699681040c965203007011040c4141101042c8017188c00281044002c0020158180c805418540e695644500f0b65105841302c0e81803034410401c000c1d04228a040403940b0101c00c03002402041d01903101c0a200d103000b05072a2804500060303060003810700811000750a000040c40465541c2d0b0390701c40442d442c0c2001e00910000804900149090352207040b0900d40b90b6802003174002c026210000c0913036540281c1c0410394 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 92878255 1250 92877005 92877011
    0x10f05060a0e0901030c0e0f040201080a1e1e0e03030c03160203160507031e020d02151317060108070312031815090b01080a03021203040501090c06020c040f0b0f0f04 73
    0x51441d4032102000c0d0300079441980030b000928140140e00a147c0307801010144803d1941e010040907071703840b04c0c0d07198001b085013800040b40030550009202805031801140034050901c1402500003074409491440c0d086c0d0b210040044420700f03035000da1244419511000040e0703041c40402c4240d0882c500081640009004481c60078911254850a1a003039503815034490b00003030b80410a00c4042440803040c4160b2400915a0004a900042d1481008000a4000c00e00040307010a041e242004403208080014100d514031a42c0d4140711300c20303040c603c83c4207055000302c00001a106800040500030b40b94411012032040c403007048128010880c4404002020801622840100f10700c031040003c1c1d45031044000c20750100c2130514050001040c0d201800d140d004c40482d80c007007580400d4050b425241280c0d1640c0e0703520781d814020701400c0030680150a40140041c0000d000341c0000d0214882c103010b581c244040c40e1484c00590845800605c200d811940303c1c1d01802d12442d1074060000c104100601c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 92879505 1250 92878255 92878277
    0x809060c15070305070f030605060711041d011a060c0a0f020a09020a200705030a0807060e0d0903060b0105031302010e12340803070b04080c0a060c03050609010f05060a 74
    0x20060844065407660b0110b903840c41404038859200c0c91849000c0c01c0c1d0300b01407003114030f03003004115544600740c400340003105134100d0001c0a90702c1e904101c0303407124211680058142c0c8008864000e262001d800003150a1244110384142801c0c001ea544c6101c194010708a81c0c9060785030110b80304e100700c0080364001d02c02e013804261051988081e012078021a91011140c0c071001081c800d900360030768070302e600561001400b0425503030005140b04d41160b0001c08291a07003120b28024002c0c100c46a09200d01c2e00a80c10815050756000140d02d085a002d00c8007805050081c60040d00d5510065401402e0301440804040240d40681c0c50700e210500003074050504a541c0100b82400d21140e5040c0500b07105001000400c000461003070020164800e550f4594030364038100ca5280d6900c210320005104c22402c90000303083c0b00b03519003901c2d110b0700404107940d941ca04620303040e00206600034ac1036022074501170210f001400c00351001410788195116401019080004024035a0131005d50141001218404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 92880755 1250 92879505 92879533
    0x90a0e01030809152214090c03070f03020712020610060804080909150a140109081605040c0c170901090e090d03020d0b120307050f030a02060c070204060902071505010807030809060c 80
    0x3e181c940c0d078000c042a0503a5007801c6e4800c84100f142c080d01c500c00c00307200d414031488400d10f40031250001c2050030700035114018280140d01034059503802810090301c228031154240d8000c83e2251003080801150141551203060135295041c054a014110350b40c01d20032083c1c1820700324816508008400301413100b00c40307010b0010703900400c40c0d00180c03a5451f0180499069507048212071014080501c0a440903848114000101903180d20075980305688503043c0c1c1081e10b0040345401c0800740c000405095121100390404025484070402c0c50015803100c1002400d4040e10440030b002e040705801400e421980e4201c100c001c1c0d003044c2d81c810805592451598899510209200302c04100d68001d181c030f17040d40d03052070303400e020709240a04110b4208202e58440980d01043c482c0d800502c00103142d48a02d00b600125006180c035400c48000144005241006e00c20080e01058406100c2001480380b0f0b80c0b50f040c0702ea1249402d02c801040c03400d05104a880a01d0700f90054107042c03018500315a804241512 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 92882005 1250 92880755 92880787
    0x30305101809020406051002063402010212010b09010806040507050408010e0a050f01050f01031424060f0303090f04050603030706180606050103090c0e09120d02090a0e0103080915 79
    0x581e0030419965140c241c811070500f806000000c0c441100c180782d00041407040a0746070b000081c0b14000014541601c02031441c0c5c1044403010f180308001d01e0001b40e80c203c000c0a0f00039032080400c090381c020f5480000484241d640c048600b54041079440d0711081d12003006000203460090004014000f003448041109030f001d2003602c0910125100400b0701100d98107060b820440d002c03000d00315a904160401c1312082e0807844040c11290712800307010308804409002400c2060a440000090b132070b03521942c80c54024008280e02400084400e6105c00c0c4000c4201580c80c07240c0e08100d500014400203440a610701540072580c4103001805483c500009940c68000726120242c05480d044a100f40701c1c07044c41098411000902000e0904206244071601c81c990442d9852003070070708600c5940001030700710381c00340b1094500c4003c1108294549448080c0748021303400010749180150224803002821a48041d8480c2c100c070f1308000c001c1e20b4031030840e080c014508482c01d00c1d50b0420380104601021131074580 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 92883255 1250 92882005 92882039
    0x2040e0312060619050703020309030316032006160306030f0b01031704180509030d06030c0515090901030f0c120b0a0b01030209090a02030907030c03080406090506031303030510 78
    0x480a140d4a2140e0105075480250180955004103000d100124541000035041441000035040094172464a07207402c92a610039a4980380d0940004540f80100c40101070b510b080d102e00c203843d0502c2d044248250f6242084481d44000391581c48040031400c01e100f00003080c100080c4a24001c512107449031111860485050401c80b4801a0f6000400074042d155045210607104160040c0c40c0030b140110101d04070380810b94885e0f4440d9540c011035000c1c0020002c891507405008418009070745c1e28102a0401202840741901600c1d1000f001c0402901140030bda03c00300004007002400e03402c0d500c1e5011020300e005030482d800144d1100c0403030340b8541c41c0800842c86100c3c2d00d01c20050302e4140280d00544000034146414103005115410715561451450341d400024904016120358600c140540360641c240d1002d09869900a8080144404903008006652807601d0307403000150741e03005012140c40102c407840100f40b9400102c0c40003030310a401080e04003071075400b441c82ca25101d10304104150110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 92884505 1250 92883255 92883281
    0x702190503031609030503030604110c1005010312110601120201110f0c03150708130c09060305010b0405060307080304030b04062c07052215030803090d11071d06030a0204 75
    0x1000f0412a00380e4100c00c621034070028030f862071000b4556904c4aa89002c00341c5018420360700d075a0148030030311204041d50341890082c07080741e24070f0220710581c10007040c0a003c152140302e011080c203017946003e00d840c036496240303640040c00700c1da03c5c0c00700d407001049040c0070481c108020045900002c800420a194082418402404e40528000109407920310384165552030116a10300304110290050f1205611018109280100c1c5c007003450b0850030901e241d04156003070707407a00c0004414460158440b1710840390942e01008a500c0f20002c0590b03c103200c1c41404d0300c5a00c104001d10028143c00c9906030098440c3d5000f00f8065510b210034040340745004424030000d462a01d016420b04810000000286010303212822940111101d42c91b08542610a140c0e03240d4548241d289408151001c0c60000c41d0000d52280e281d0600030501c80d00e85500310200c1002500e034440044844402260300b40071036070b51425050100c000582c0c00a100c00340204010b0b03150142540d00009a00c480c0164003d588903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 92885755 1250 92884505 92884507
    0x19060f02040f0806071e0e04060b0309160e0412110313030b04020118140613030204090f0b0703050c070209040302160801020c0d0e030705060903070b0c0309040506041406090702190503 81
    0x600103c14075000000384140708201d4070303c031040710718100010315400c1ca0500b403910321810240301010801a100c04d501c9141c01808c000104a010305000c1000307203c1c00002c040c80021550f940c51840381300d500c1a070b809410240c40f642c415518900880309039100410080035a41443c13580c48031080402c5069000303441c040c0c200803c000071983d001c005014445480742c100c03040c060030308901482d100340e0206914056140000d03034008400c0c040c0103100040d1760052003070040c18007504c0d00d1000e0a03407000c0f0441e0610f59403404580054002e0080c64807a005194a0a0801c84d0b00c0d0200300a00401030030a40650090307107140c1d50196a280d1902000c0c18030b1a00240e40c84410515a44c94810b00c0c0304e1044c2048858565071003190b4000c102802210011075030107440300e1030440001c4c00e1240691000da001140054140020400840a0280d140085070100040e541d280309000550307403404150180c00442800061040c1303040d2000a4001c8450b00c1102c6054111400705503941c9200d6405443c5d50340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 92887005 1250 92885755 92885759
    0x30406030b01050a0806011803140109110d030f0309020402040b1216030c0c02120c03100c020106050f090f07020705030115030605160504030605061c0b07020606040203060319060f02040f 82
    0x6050700503410700500070b00e400c918044406100902a510140280d0304020084101c44103641060107100050350700000b040070200d08218410340205034408046a50021811008500c0e28240d001615200d805032101d411181e0106011401031000850407680150700b8080403481d8500038003d0108450703041043c5a0904104003455981568440d280007003500b0000c41400256025078042c00060341540c44102c20003802d0000c0381003010742c01c0340a42500c1002440010255650040400305d215900208026900caa0030b125107241000c69840d001000400410000c1ba54446526403015192058408017074595000909558185404c15258038810030300740140070b05840388641200c04060b2042800c035007210090610302440c030000c0d00660b03071072000030856140c01e40c0c01c074118480444030404e100c8180c60811409807091b1503003001441000d00160090400d442205d016104c0203005100f0741c0c3c0843c05c0440c0400710b00c081183e4403a11823144100f081c03001c1c00648054600c114194551038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 92888255 1250 92887005 92887007
    0xe030322080a0e04050907140f0402070605161106060603130204090b1f0b04030f03080411210d02010c0e0f1305090109170310050906011e0801090605010504030b0109020a0c06060602030406 83
    0x900061b020300080d410111b006c002121440c01000010342c0c007503031180400703000840003c0003070142a0740034000e0350400c0100702c48000003c02d00341101314a500c48905152141c510107a644c1011140190002e10401c082486009036164056000c2e01c01800420b0f1424070f650344010070903041d1000f02c400c00e05101e192003542102035011014000c1c0355481420546192141c04084011840c05010300050402080610101e4040700f81781d0303003015001061000e200c451102e4a000005110203850260340440c1480610600070f6862410b00303503444c4000e1171202020011014610070020354440309034040681680014003a586c8225510800020946154244200c5898000c000b00204010401c00c21898200d07103100d01d026190240c4140003507580b80340040e03503804080704440380c01220010380c01048503800920181a90f810203014040143e81c0c200641d9140910b00004049001502c0180140303401580505100c403e24a05a40400425118070782218850340113a0010b03040000e05000b55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 92889505 1250 92888255 92888261
    0x15120d0906090e060a051c210e0301090201020736020a27091107020915011119080d02090d05070618031a190f0516030e030322080a0e04 60
    0xf4654240b8000103880c1c410002411100c807406164400d440186012070031030500c12101e03402650207995521107004614820121141e0f43c02007400140c10391a0103c42414180103400605074103070001c0c0b07072550424865140d40c0742121401403c06a8400007000c843d10460390140c44180e400c1c0700140e4800c94130b040240440c0ba144121241d28030340c0300e1060003981141c4c01480441e040d4032000944624400100001803090060107980028110240501c2a402e100400006c03202600d489010b80c0c0c02c0400280c8811140c02e4016040b0f4102c00f0920200740010001c200003188200e0041c030704411a0300180b00f545032200c0644003a80816800c1c00b01c0c07038000420060b06440c09250303000c86441c50340d40d107001400c919640c140c0110302c8000701d418400c1825000e02c500e43d901c801484603079400308d501e0000b000d00300c8105041c81d8800c140104201c0c0239224505180c58608080c40c5595500c000c60320301c04000d0140921107410740800c900100326850f01600e03080c4055039a8001c00302c9190308000079 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 92890755 1250 92889505 92889509
    0x1401241401080106050706020d02040b090301050601030507020c04180812100f051302071b12150509030a0f020c09040b0f1810090303060803181e01020615120d090609 73
    0x41204040d86158181e8100102038111000b030314080341d0b12140c61414501a02908201080050004c140450f032328403c603010308400c400680081050b5694080114240c490945280002d42c0243c0080d60042c140f603002800c2c0329400e140511401c0e003a82e80c0b0900c45a010b13030144505124000180100d046284542c000104a070700486000c680c03e10000603903101e0803112000180d94009881d004001c42c500c0500c185181c440b031030b2008a0744d200d40350400a2203020f07040304d444038040c02140002c8030f10311405001d001288001c40c23700640700c1e000e0b900e0344008402c000135440b401c2e8012049540d800c41c070510031031180203120880c2c00c1440000018201c090310300c10700d90004084e10b90b5002800a4401e4010b10000404108980d044c04c0c00c0d0300a00d2143c1250740540000544001c0c07410000544c40c061050690308010509019031850014204040c1418010380107907000c5049010904810b0440c4078000b412042c0a02482c14000d160125070300444000c0340c1701c00f030100200d035001114900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 92892005 1250 92890755 92890769
    0x30609010e0d03020d1e0b03070503150612070b07060207022b0b1b07050105060f0118030f02010e04020705010c020708210d09080324040b010c020409140124 69
    0x124031400a450340c541d5031000b5960209640821624055013198000f18441d612003151031201051322464040500481c81d403e900a1107a10030016540c01d000403d403190340d00940000006880307010030010103100140d962007241c03140c071308040381101e13400b002006100d1060720010b07a249064414000308902c111a8540500350b001c8055060409a00c032900f807459100820490039514000010071071102030b4400c50300480041042c80400505500c594012142124007040ea035103200011900e0796584050482c0b1355042e1081040002c2d868400a20b03440d02c14142a1000040340e0301180480e00034000c00e4440d82e4403240074142c075680500410010b0220302d03000d0701407020f10f42038044140d46250908401c0610000f0b00c0102c80e02c01c0c0d0f0001001c2c6074407180007541e90501400300042006113031030304030b0155210241d20000d442c10344199000040f06840700741d603044050702008018440d41c403041d0350400d1480d4100f03610784000e1041c0007001c010401844c2e040ca405030302c484020200c070f4102c1c1c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 92893255 1250 92892005 92892011
    0x309061602100327020120010509010b0d03050f070606030803150906040e0304030f0c05030105070906030b18060904030e0a060504030308090703020108062e0801080f01061809020604080d020303040203060901 91
    0x480a4029450b540c071130410960541c0301e84902c0100c80408041084403001e42000100c03204001c4190005402060100d00034001e02c13004000300006419040c030b00038046541042400f884426130006041003600901001500f242d680d100c4900d41d500446140c8408100510440c1e50391819007001070304103800752010003c0c4210f03010b00644d648124040507003c5500722a0b904200001501c12030040c0202400074410303070601400142c17004540d4020407011074200048000941801c07400c8501e070380c1048406407011748604040c000c040310064002d408001ca1545881c000d9107540b0b1400000340368903501c43c1e43d00c0d491802c000740250400361245945d6048503004101507030740144541d0b040712003118100050604200d004d215020903103e47da4040c3e0400c0d49803802c00d03410800050403284a40c00b55400c2c20383e075040d1a4200c80483c000e83d5055102409036000c44400f03030780000302641c80540181d00e80382c0c03240c0d446450605000031240060313000004100840c02d060105e00d0300208400e0080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 92894505 1250 92893255 92893271
    0x1060906030f14162601020d0605030f030702032e0c0909060504050c07110d05010603050a0b010503030a0906050a050c01050907060306080604050304120201030b12060901060f0b0f070503090616021003 88
    0xd07080c4843c00c0e10441035040c140156004a151020701d00172011299000219a54651f190445026101501c50540304c0d01442082c204e81020101c1100d81084d402805460309130380146125407441135801101908501d0031034141042111480f41c114410140c1d100d13210b20914150a580954100e604480d0280f0b00700428070100c0501344059480da01d50010201c214100e41c0c0010a104801c407441c040c0180d03003845070000510a001c00c01400042c040d25203c12141c2e2500309165580c0301300300c180400143e81c8a81080354074810006840c18500350320b0950302c3c01c001101001c0c2510310603900c1d0081500000b10400507960144101c10003000712501411035460651150b940b240224820080c030310350611400421a840382e801844800c0d07000704100c044400341011199070341800c44440c200c40d0f103000d5010802c0303c101040780381140e6001034100d107010988980202c0c0798100345801c0310f2030b100503c0740180541e42e203405480d0b02d80040c01d40030a00c5120b40100b0102c0451a40c24406061a04843c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 92895755 1250 92894505 92894533
    0x231c0b100507020907020c090f010e0f0712150f09050603010e011b03050703110307020a1109090d0c080409020406020604110f090a05060d060e030a080a05060303040501080901060906030f14 83
    0x1640d1409404039028013140d41c0300c0000b41d040900b68007180b0b034024940030400640b1026600b0b11070580722540a840d03043d07910390200f03168114058408001103400700c0c1403400d4004442c0c01c62040003410f40c80580e40340340c1c0c1c5d4a90490400b4583c028401c21030300c40d130801140e824244105005ca8049030002d10512130304402070440902d400d07000380101903d410019030705500a03040b580b041c0000d15002a640e144c8224002c0d21020722040465505001054040c42031401810843c01140c08402410100003541c0d0280c071181460541161511400d010004030400c00b4405800100102e802903c0c2924043c030303144000101104101e807107064010036140c41521111102640810643c000060070345034000003c000d001f900f08000c01540c00c001120392228000700c05070400c2c0841c1d4454020980720004460140c170300840310642c00d5841400100a40d61042e0080382c2c0116140c80009031300b50302c82d4130620603954a0380003598241940e210b801c0410a55080c005500714811000d00952868499 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 92897005 1250 92895755 92895757
    0x30c0a15020a050304032001032007140a0309030c060314071b060501090b011b02060708071a01060806010f020c030604030302090102030f03010f03051c0e01231c0b1005 74
    0x1511110098004880d00441c1c000c100e042ca100d034001c03040f03035100c1e070362450180d08404c1c4a0115041204440c048008594040e004031602441c45108402d281103044038a10000d07084044140da14042c80e104485000c00103010003001d0318003a0741d490030150f0031810030020022880c4e10100800d85814004a004103c0700d00c400d8202c0070034908460b0320b540301001c0e03600404203640042c00480c5004000100c00c805644003180403c001c2e2a80042d40100202031a410300340c02c01c010350480b40410013100001c090000604544c3d00c64403019020551070020a040c241007600800302040c54402400340f03d682007200355800010603c000c0c140d000c040e4001c01d4030740c24042c0008051580100751184180c6c002d00c10380d6a1005095a216200e680d1145440544606440181c42500440341908000d0b4006446407403046401e46034920312034458030045a800b11500030744541308000c22a014100035240006102446000c02e68050000e4030190b000102e41100e48035a1003050a600fa06440380d4100d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 92898255 1250 92897005 92897009
    0x7050432040c03110f04020a0e010207050f0108040b040f0b040506150607020f0d032703020f01030b0603041e02090a150f0f0302060c071a070605100b0d0903090305060c09010e030c0a 80
    0x4400213084003c0c0c2000c01c90741c241041103541d20500108a81103900d074030401c10a05900240c2c211808969140140300b10702c1b00034800d4034002000b12000902003032201c1203803504244203802c0070710030044984030410362440a4034121220340110b03041c01800c3e068004016801001198800e02d44040ea5000589142d1081015030050084809240034140205501500e0720174500b00307540080000e803c40d20ba1540540012480790051034017850726540709200c0c1d008282005003580346180c48a848842c1c805480f85240c004600200d644103006880b001d54203130280d0070003107001c40d02982240741d03030165850640203000400040c0b00104044000c0780c024030700f2170750141d804179a5595480103003400c00001d0b4120081401410002000744810b400007092884d00554040040b511b41d0350b407110014400c1d204481ca4120107100c204c202c8038290f440644230500c6414600001c5980c1e075100b41c00c0c41001c48001800042c0855a10240c2d604400f040102810840c06000341c404d0800000d02040e12034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 92899505 1250 92898255 92898263
    0xc0409080c013b1606030606170114060c0a02030a06050f060904020901090908120103050c0307061805010e010215180d080108060403030c0212160c0b2106010207050432040c03 77
    0x3903110030344540c000d000d8113021200754410403c0356034031000c0c050080c08181c4500350004008501e4942c5400000310414103132116420000c4015000c0000c102c0c0d030740c000c07888001141c05000c40f01c0006a0303040180700c4000b40f040a0103d4589814800307240c50100051649008604034010400103a650110160644024240005502e00030341040900e50007500080030f020314110001000b40200010005c8181c0c60450032105100d0f19124100c859820b00b047c40c3c02c2e550032003641404298024140801d0300c00040c4125402c007505450720f000c90709010f45050700c0340c010328007426200000034003c603013050106082c6401154904601e040e614440100041d0030940e41d0442d00290520901c6044151900d507004c054444004600515060a041504035240017000030300044402400064034100500560300f20901220581010208480208418114041c128020070103980e6489200c40000340b8821500f21800641a01c802004401d000f1241c0c0e00d005908200008000c542544192588 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 92900755 1250 92899505 92899601
    0x313060921170403170c0105100e0f0a020706020a030b040b01030204050d08070c080607080a05070806030d030c0e03030f130819141207120801060810170c0409080c01 73
    0x103202e41c6581d107000f0f50b0402080e20031080428480c1c0ca4040c0007400c5044510b400070801511484c07a41d03c0d5001040c800c4032003410600001420000c2c03e80046680300610010140c508480341d5a844100c1c2d01514512001c039560714062401401c1034420941800380a081c1149000d041200068000401660042510400181010400400440180082941c4402ca070000e00b400c0001a090b004221a4001098a03040000389a039114458150140c800039000e444620300d5031004801402d00040881c0503c08140180e9a580d14208000c0130b203440c07800c4042c0c0d00e82c8484003100502c4011540001d2140d4001540f003020a10031a4102071842c1e80187e03101e072030f514064441400d001e5418504903007241e0209449040c0070b0741d4122458400610741c1c0d051001c0c0c0e02c420b03003076800e003201390748844111107410705c00c1c0030582c40034150350340310040d04007155401d034074030740001d420b580c40300c10205d03840d136000304106100000c00d00920600e48446002e544090070b03140b0901591241c0c504c2a2602000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 92902005 1250 92900755 92900783
    0x6060a1205091005011814040c03020f0103060503070602030714031e130806010e04060c0309050c0607050c03030f0712050702100e0103150902130506030f04021504080313060921 78
    0x4000c1110074032154006201380200e695a0f01e203000d0304120340d21104a540e0800007201e1510102421003441030b80d110908207061401d64003131059040f64112010b040c1030f921100132500d40d90400200c4001c080e1540155903c21040c6881e260036442c0c80c1d0328098075841805482c403c01040e00b030f1024982158902c3c261900e40352210b1340c41600b0b00c0e91082070a40a824008500003a05000f128812030282400b84848104990100e044445001700a040e40c2c001c8003490046140060040000700d0142c41194904000b100010341946e104083c852149000050824200f04842c0c60510840b489402d03c513041081a4000c200100000407120b0108065513808002c142e000381c2c0b209240e16000c20140700c24580300c0e04004000c1d0b20204180c10b0701400c0e0540011a840c203182181d01c901e4030302c1c0d40e80b10f958032958203211060f10102c181004800d8180000303e509441000a0311000b00100c94041c09603180c20700c040d110100580209240030303444225002500c51424118080030750011102010407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 92903255 1250 92902005 92902021
    0x10206091507210213080c09010303030e030904020f0d1b0804060c120e070513020703200322050103050c12040b09030f070501020c06060909070902070201021002041d06060a1205 78
    0x2030703503c071045680c1c0502040034002e003503055805009000d681041d000d81d11a22408104d6030342003c1600303507a1002d0307000c0041c00000c0c0710b03401c4a0a0002d20b48100e0303051440e400d00160a80e0800000307a55904404181404840400d0243c01001405564005140303080840020100301c00200007500c00c40e100d08046400d144180c1d4840c420358901d0070204641100c0500e2161504914852144101000c3c00101100c101c00d108413010180d05440d50304203d89559030709013043da49030341f40c81e050f80018413240c83d0007258148444d032440c00582c9008a144c2c01c1c00005021150050051020755800b84a0003000850602d00582c0090708409088007559407070074920300d07510484103590521080469280104101500600012409602914110382e600020300001c00021694201c0a42c040c80301042011000c3d801031030803170b0040c0305681c6c411000d4001c45040c3e0b4090b90040d42001c0301465055604e0104500450b001802250110318107000480b000300045407250800540b81c0e80d41012590748 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 92904505 1250 92903255 92903267
    0xb0a0e0f0a0b070b07080709051c171e0306060a0302071b090f05090c150307050403240e060f0105010e12070e1b0f040315020904050411010e010206091507 68
    0x41005221960300d607100c80b0809803680140604507644515900450021400341c491284280000e50f50014168a410f003009050040000c28010303030115003580758049440c040e00c501c0381000c010b880940d55040302100c08500c2e101c201003858030907001c0c814040c1076500d103000c80f98126010300d07003d0f0301c5070228200341455012141e641c8000b0003504030001156241c41d0810304481580308010001982e0344c0e9141919503a9040c0043c1c1d010a12415200b200c042c0040a1604130550b80b034107900301a200e66400002d00c8028a0040081314184540010061a40a1503070501400c1000e4003450a042c49600904401030040c14107025030b4102c4203815840e8401c3d18034104412a04840145545140755800441c040e00c1114912400103100804107003000101d40c66685c0085406103050b02d103450354100c010000d03890b04e81c0c00b03800300b010030396550b980d000e0300e801a40100d500e00482290500050710403079014852605542094080103610031010418280720070104880007910b40d2450011650 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 92905755 1250 92904505 92904529
    0x80105040b0402131e120f0807150e030910030b010e090603010e060a02030703180512090103021b100609061a07050313060e0108060103060b0a031d010603050a060b06040b0a0e 77
    0x8135101e046000940e000290940083c1e0346602c0f6031103858940c5407a425402c00d0b0b80024040c0c2810741003110a8002001d1a001b080c20074000d20003100200000d9042c02d050703071440281c0c44a41da102054280c86032412a06411502e101818100110016800043e2000501c640840d00c0381c181c010015a058800790041802c403141c0d4400e03079000345808400c8400a4105540c0240028a081000302c0501030102801604c690000d0060107145d4503406460030a1740200d40c003c0c105074080c408500709234078001c680c12040000768040c040821820390100c2c00c90301103038481403c250a1100811020706c400c00000308014400455554a0803581002c900e1841790b00d40c00f4210100c0c0c0040042c0b0aa44261840c0070240c0907a90342480752101d40c011010b86107107000d060300d1804104075214000f03000e540010045000c01000a0b03880181c14290f5003140c03910380c01501c0301d0700102419800c00500740708410b001d00741115054201b070708055004041d4051400c90000b448110f0b04000c100f1344c1c0e0081c54401e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 92907005 1250 92905755 92905777
    0x2040b0a050a0314070f050d151b0203070312060f06050c011805030304030f03141f0305120406020105090d0e01080c0d0213080c010903021e010c080301080703021f080105040b0402 79
    0xd0340c079581d1904101040740c1c0300105405020310311001c501b001d000020b14040365401814154014a2034640c491391205e43c0c0034500901c0d035509401c00040e40040290341380d05446801a644400d0b103400c0c0a8540d1101644021207685490410b20150050510714000c0d11542d00d40745850380030160b0414014589014600c1107600d2004402041150002c011885148281d0340c0c2407401695020560540300d00030740c0540c041c200c01000614100740002781d10380f030b00120010b40380825940e454460070202c481d001c008e42000001814080d003a0240141900440d0900c000c18085003011001000380e00404000c0d81000391100c0400e039001c950001b65200b400c25100115603e4a107410b450200d030800e482050250b001d80d55040e20740d50f0041c1610001c43e43c015205a503003000d201d0510607640c004140c4941800b11490600002c03501c5000a14043d0200500421007113046004108828100304019401c0380c1004450f000940c1e8003010300350441e90140c80c041403820f0848001006030081d034003926 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 92908255 1250 92907005 92907019
    0x30f0f0903031f0f030501060501121a040c120e0601060e01110604060b0303040b0c030315180105010e150c150f011802090604030506041101030e030f300709060201111602040b0a05 79
    0x1c01841b1041d03100608458098030342d4441c160320b1422171810740702c520307001c0043d2002c601885440303030410750445101100140382c03488501320300d0301c0004111024210030811503840b10006001058000039040e05441003402e01c003807078440c5590401d03904c40000300018405e944409045149450070010b072070140080780d40d040c0d15401c0000f4040c3c0d99800450b45000100c10b851002c0401c0d00703100c032103041c60701600401c05000303a08000c019107103410540010783d0811200c100d0039030148400d50246c040d40e1140310180844928910000302c2c001c8024241d414070041c00310041184650b4119200d84404116a01585822081380002d84c10700450b03001500b036020707240c100400c000200000c5640100c098808000000764a44c403d0b40e40d02980c102855000c2c82004548c4010080007a4141001214903025040c2c2011068040d103d44e000c0e50036501042402d8420b000442c0c0a00800c0b0380543c8086189041c80e6001400c400407401c69880603004560300e08440307260b5183c20740b954000e0321000d4505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 92909505 1250 92908255 92908259
    0x809041b03020c0d030603260f13050a060e130e030910030b100201021303080d0609060305030319020a0801030209041502040f14040c08010e0901021e030f0f0903031f0f 74
    0x90041e5000c0050502c3c64000e000f90104914000d100e000f0980e07821800921846c0200c0e00294400da014507405644100300340302014007200400000c1107500daa441948c41c2507440d2405000c541c1e1a1900090300f48042c1094000700c1c1e0b203800d21410380d2200d640201152070034007000260300318424095203c0d040345c02c090501d601990103820042019030140d945141c00b10000804a0803800f07083c0c0c0821500b02008402c002003002c4001420501c03840300310000c0d11300da0307500000f0221501030740300726170070b800100c10030000760300c072441e0010001c8001000b035241041c5804000e103000c005000080c402d410420120f41440800520000030204e102000c641d5940c540340d602c00254024425560702c0c2c0c5022a0764582810305001c0c551859016407190308007070f400c103031036800c0c01c5a008003000c5056509020880c00c050b014444881e140c00c000000d01d5072400c00c0c044440c80300302e0040c40d0704a202c0c000300c00c0c084181000001c81e603000b558441d0300c0240b444004800503503072030258400710103c8108a00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 92910755 1250 92909505 92909507
    0xc07230d03020c060f06060d1e0e06071b050a020918010905010506030c042009061e040914040b01090b010207050d080a030e060c090105091c0c03050606010e09040809041b 75
    0x600c03d21403060110b503030b80c2d5540100040c2c030030301c01c948494000e142840030038040100d6030042d94125800342500103007601606404e5088407110200c403010b0364410802c1c400c2c40b54000089203100c00880043e60800111b58942c0e9a0700e1104074002402101c10100240703034080780310a00aa20061040280049202410280c2c0078150584409200b405606180c60301c03403a0521598480000100c10080601c50100d111000f0341c02c24150a46c0002081242070103042e0030342d100b01d950208079550942c8031401d158200c011200d94000c1100c507803906200b4400803500d26442e56046404441c0007040f80110398004034140000750380b00c0c03030b00500110545070400c1b0700300380502580080c1e550704101c0b800504c0c01d8156100c900b66001c400303019040008110310b5110700010400900058803290004120b5044105914400c14041d40c0300791a0079001d01c204502400120307000034092902c011418800c9000a04912000c3d0004088480005070340403203465a80003803442000600100a003440c1000c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 92912005 1250 92910755 92910757
    0x9080309070323100b030c060304050105010e010609030803190204080f060108100525031b020a06200d020903070504050903070c06090b0301150e13090c05090c07230d0302 75
    0x10480d0024880e520656035201d030460312aa410b1926001040b4143c8813070508001081c0c825000d5415000d08070710000d503a16000c0085000e42d100c0c00001495602d8820721185121041e04440c04002c281081003000c5030022055035008810320b1405003100d41e5a402c040020301c00c40e4404020341c0103111002044140c0410424100c0c0d0071402038407540301a80b04414111003085454041c8421101da9030402516001c11087c06030a007030400140d12a0303240b220f03603110004880c500380140e01280030b18080001d076020b40306141d005a240039504403498582101107018040e511504181c0c08121550203a504100c0c003c01003001500410240c2070a103441a10780d407044400343c407203441402000481c5442800c0407003c645800ca2501e00b1a400c02200c06480c21b0302c0c1e421101080503120310b0001030303030303501e213105503584684000082c000d1140d281c43c4241d059076605c801d114040c1d1a0803c0090710307074142220310065110420100d4020f0030b204100c9540e801901c40060313841001c202c4440c050b0968 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 92913255 1250 92912005 92912009
    0x605041e0b0406050315090a0501050f04020102150118021804060801051f0302060304030302031905090715020c03030702010f0c06050112060506040b2d09040602040f0f0312050703030908030907 85
    0x900184940c01c54801440b05444140c450f640d090750206142040705105540f5240d08140d991050f9441d842032070311402d0960b0025510381c030784124580180000c41d078040041a00c941c491241046c1590301d005121400400d030070840c0318905800040c0c04080c91106c2d8146e1841c00702c010420081c081d00c800c082c600801c02141e61405800d40445414004100e00c0a40d2045035401005a0300d10354482c2c1e0220040e40000e080810405502441581c41421030b01403144544210401486c0c0c0524120745040b42504400c0510195040b51a510903940c4000c42200c06c01602802c01c0100019190004c68100e01d80d11400340c800c1d46010000709400800d00000710109014100c107114980710070341040200c0e207100032099031250401000385030f0032604598421640c16101003203141142c941000c01c680e202c048408a99090740020240035401018808001400d44418003040190031595580c150300007085c1d0150500401051040805129401c00d5074020741c070242030b58803810489296aa904814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 92914505 1250 92913255 92913311
    0x304140102120c0c040f0902040f0c02012405060307020715050309011a090f0402120a0305070624230a0305010902030c0114090d0c05041e0e0c0d06020904060504 71
    0x302c220039a21119400a039078107140190080c180d01c444010070030000340840440507000d2a1522041d4015941e203114100380d00101c11000b0901d0407541400134212000341005a4217200c0706d801940304049200880401d5640135140c1e29034030b0311244c07404d034038240c410791085090075035030000b04140d03682c07020155000b11641e8000b0f120000c01070211000d844200e040d1943c00c446420f000580c21200b800303000b5046400a480d614144800c20340003420420300000c15000318400140c1801007085034802c2c1c9000e908090f500b10380c0b03814034241024071100d092107061012031203e2014100d8403d50301c4a0014005c00400744001c1c03650301d1900e14003801225a0981c82805070481e8028194010500740760a6171040c60064a0304081074200482c40302c8260090715005140940810240c642e88900050040070550645510301d4068946e82654030f40322154245800c800600580c40e01e490b000c4010444e401000544c039180480e02040040c03c2d41e6114651080c14280c450074100d080d00c18241c030790100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 92915755 1250 92914505 92914513
    0x909070f060212030c0310050a060215060402090303091203210103060e01151206060f090510060507030507120c020315090c03010605060a261e01060305060d060b030a050304140102 79
    0x7403010160b884405002d03590f2000c01042001906a140131401194000c000000250100341c41d100407842d0030034540c00190260380700e0782441d0000307069071300c06030362181d0300702d8056107003000754800b2a4803402031090741d50040445580704803240800340160b030603c1781091009a0030913100e105d1101b199000388070a44000385401b500c2802c0320f006024500d940056800f40b09001841e22500c040419804601030f94442d503540350101c0c1460311a41100014100130101194034206002281c260302040e60062090000030400440040d1300b0105881103150008100d00c48001100001d440c891a82d2100035458014800c81c28404400c03005818050303002041204d003006105000c4c507080b02e00038050706902403002c1c003134411054460f501002d08189588800943c00b9011404292003090680300c241020854541c100004001304001b0b600500040c90103102905100e80411a04401181e014060a840707406d801a10f880422451070041c0e0f00c1400c40b83d5543d5039030b5150703409000380d542c01401801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 92917005 1250 92915755 92915759
    0x7030c050d020a060f090b012c1317070c060e0a09091208010501030b0109050918030d0605040b0d03120504050f0f0309030601061e120912020105070201062102041a0909070f 76
    0x300d40c46002c81036907218070302075030300d07420700c200d07070407980141c040c40e4003020034100d512714401d00c092281d20300a00d5121900c0000d02061f15040709101c245c52001520200140290000f082d50700c1000e42c2152854100540d440091784080341c00d40401e40c004c08002c500342640300d03040198200401800340b0050ba580e0f03c0c5640c070340004600350b6502e040c1c003a00046420106019038500110b026800c04088181200c0b102d1005003001c4c00e54010442c85d1600d0356031181c0400250905002e0107214800c21109441c0e20041c7d1354015081000141e4401f030140d40d030380c0020301004420080c00d006a82c074041140d500d102d00070a00c80d0780b44e022038880341c020b0103941d00002d400c60044001c40c641050702010255282d803203074401c0301d0008021142c60b1103240c480e1080340c080b4141407031113204110107900105407498000700c040e0a4030380641c01640c030818442c2c41002450101a89480c201c3e034111008258401d44007100c5205603014110140d126600e8001c0c00805900000d40f84e0484011240311a1446c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 92918255 1250 92917005 92917031
    0x220309150f090816060e0301020405090f01060f020d0801030f050f100e0f0d0c15110417150402010f0509010e040e0102070215070206040909030c0f080c010b040e03040b07030c050d020a06 82
    0x8412213580741520064000c040c04050f000740c0541c03031580c0c0c2c0603000504255480000840741c01d01601c642034401002d00041c0310460384001d01c0001504a07000810400c03d4506004080c0741051002501c1da0101d002d80d0380c00c00c6024480e0407011018082125000d141921012006001d840d00400203441500e00c1c006541002180c45050402e407502c40a8074140d154681503a0105540c15405005e5501c020b0245540c500304003500160400f030840d20107001074141d001d880c10440801d141e0041512208010041c1c0c1c3c45043c00941e000e941c504030352290500001610321900c1c96501307551150800365166100e00055001c1d004440c0200c0341c5140c034401e01c080c000307958481c0d01d0010350020300c03c22040c002c0c40c0d42c039002541803c2c420702e04180b5a0005407100e0313103c04010202115054000140d104147c1d00074022520a0002218100030422002003800d030740f8480e51140342c0000c00045000000c0c540100401910942c00c1005d440000800c0c1d04001c0d2101d5030807000300d4520b441e284840801d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 92919505 1250 92918255 92918263
    0xa090507060509100201112d03010608040201120e0d030c02010b03060903070c060c0b040b04020f0301090b010f05060a0203030103060f0902060a03020a0201050a0908030a0b1507050601050306070305220309150f0908 94
    0x24288846514507042d011320700d02681d0890741d000e045400b0302c0300e1104081032080c8c50046000b058580e5480c41a07040510004201c0c10b83c01540c85c149504010310019001800310785802c0e11403150a000564080403101607000d04241c90000c0e9041c01400c00b000806503020000700b6070075104103840c0208a07201c0c801503078805922007014245007a018002000258803d0805400900040c1500c84107030340c000009095030141003044030601c1e44903004019448070380840e40080c3c00200c400d00e09000750200700035070b43d010510014050079161707a07014900350610340c80f11f0902d1790050030303842d40d600040801030040c0d801041c030b41e0010361900c0000340c0c02034a0b81c0b040c420050341c0421001d1940d1214043d1001030641b00b02425030051480b4501040310080344020449580b00d10050056907161008050030101d0003400030f4145403d040422040d54103100e03009080140b074042080034016142021285c4c2c0400e03402c84160182e5080710b144d001c07500108c104520404681c0c0760000c2d2510b40f40c07000d886d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 92920755 1250 92919505 92919521
    0x312020303010605300c0706050f0121021804030c0b07090312050c01060f080a0308060f0609010f090b31030201050d0b06070b070306050108070c05150a090507060509100201 76
    0x2c0d0701880030041440d1017100350300781111160450104216607141d07501c3c07221004d440360f04503294005488020060781c2d0080c43d502c049200540d0b59250302d0310200c0201041071680f0501011982c401d0b42c0110341c1c401d01c00d0402d2192014482c0c4440ca054900a0220b0303800d4681a10300000d0980040c104520802e191802d90354401a81e442d003c080403000d840640249510310625500d40c40c02040768400d01c21a00c0c01040390350300401e102c0c041c5080c05444044040c00c5980502e000c1c0c909c1151139100e41e0120740b40c250080ca844919510540300440700507036903030132030280402c0c0050805003e0390100c101c000d00181000302c040c510781c800c20800074101c20620001b40450b0741800011400b44003507003c10024513000e0216880c0175156038408141031002c484003808a03035684000d1000303591002c2855840005400c000442e650182c50303450ba500d05054142035210301c0760001641c5885190000c552140e407003011141c601b0f032600006082c0f60004003805025004143c0704030700c80b030b10500030b1380c2e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 92922005 1250 92920755 92920757
    0x19030c120605031236120312011403070b030403030501050906030604050715030b030304090e120408030706050402150304051507180509040f0b040b0615070206160507050d080403120203030106 84
    0x810000b070344180d04d0160400c4e05401c0c0d0991040c08005c290350302c41e0004c010032845504000c83c1e4500c41e07104010a251012007000202d40c800e00400c0b10110343e40084038103403140e881c41107a03040c002c1c5000918029454100c0140110003000348020160160040c1e8180c81088480407207942d03e042c03d2503034407401105c000d07040d030744114010811740c5005a00d40140318803c0c540400d50102841c042443c1d944590f0140d8040d0303550340142c2d203060200384040f040134004121b0131271500d0725000803260740303014518003d041c9643d0b03080810b01719078603074044038140c15014403001e44030710305030506580315000e03041c10041280c8a140000c410a1092800040050501081c2d0765210309040c1440036041c0010011103040e481d9002000202c0d4001c2139652103103114891114092070004240203c9031103183c1d601071114010b010b088016922076054854010000b00e482c2101d01c0c076828100d140002607400740350000100c041c010140480c0c030005100750b0380280005010344401d81000c030b94910091007440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 92923255 1250 92922005 92922013
    0xf04050a12091d04050105010e040c180207170a020c0f01090e04050a05250902071703060a030b0c250203060c0c0a0516060f1805040e010219030c12060503 68
    0x2800007000c080c1c41c030240301254030785803218a49580302100d081c078641203000007240002c0c0410041020034040c640c0500000c81c1465194149542c400181d02100c2c00b40d41c58090201c00644030a00d03199054582407a0080c0b05c0c00100c100c070a44260302075000801074401030058524030030880c14003a122007107852041c0d40340d14009150120703246907250050f00c102e5142c043d450034030380400d00400014110f410a4280442d0040d044050080b54050760751104ac01d6a0050002001082e82d003060040d0b184e94a00c41656213507180000143c00c100507801c001e148170025814021032803800d801600042c02d030b04810807121550688500d5042d1100e01d0029410390181000594151810006e420031051f20801c035000424103554407800c1071041d595125804403025810050b255011810610420031810118807480065050080c440c0150203400d0141e41c640100c0032101c0d5095044032800603849103000100303000854002c01406000c4c001c0000130b42080350b1040e41c0c503100d10445c000c48100034010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 92924505 1250 92923255 92923273
    0x50a08060409081801270617011a03090c0d0506070216080a030c0203030f033103082206020403060209011106070e090604060806070804051605220216060f050f0405 72
    0x1070840340c1c0340e44403110f041000d0b9082e00d86122021b440600c0703400d0088401e0380c00160801131b00605c0300f42c018166412408088004001c4041d481c0c10f1805241e00c40303990b00e41d680c3c1d40c985a1a2410003090555a00b1a120400340c0090280c085480c50045019600762207404c0d018040c0700540c0181c2c0d000358502d90b00320040b580006801100c504005503c05001d903410503900c604034201a0f00100c8a00c803100742c40d940c90242e99004005203130920b15a84a400301e1003c82924010043c01004001c3c600d09606028411100c0c10301e02c8488860aa100b081596106d4580c030745040139400010269000c41d14a03003c21650754808903203d4410f028980e1500b000b480f0107000c000e0040e02c06084240c02c035a5991010a0305030f018042c4034811308031510380c0307102d03030034071f898440d2624a0504243d4241001a8030520040d41c0c0d0340e03110200401c0b80400000c8402c802420380f07000788206050f03403240c0303a2240440010440d01d40c12035000188801c07000c00140c0d43c3e4110b002d0a920084800424580107a200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 92925755 1250 92924505 92924527
    0x3402070510020114040f05010b01050336070306020c0105010602030903060705071e120e120c0108092b2c04051e071106092d0c0301020307050a0806040908 68
    0x120401503007603072001007460400000c2d15402048280d4059445001c6d01e0000d50612009000d851140407080c86e2a600c0e502e002d90742d000f5614050440c0850300c030741c1203441c00840311000d180030a4401e2004185d519241e82c0b494843c0c02548075034440ca8841d400c100001821500100c255460410068084c040c02c1d035039440200c40c568001d02c021a141c080c14410000010901d040c2007461500c26070602040ba28110f101401002101070440c3c4501c17500b45042501c608041042b504103203003030a161240b51248100795040c80c003071004640741c800103d1141005c1c0303240440c88007a0030b985a291034404a82400c030b4880441281c092200d800c0c8401043c0b0840da05199101c01c0e0320003201c00750100e004016040c0d03020801e2080d9520350000320070704d500302000002802200e80100a000040c8203c00620506900e8240000c1c0d03001d072180903901d000501c050f0f05010b509140304000b4001c5542346170005025040360014a904030000d02e0203c0091090300b41032080300c1070b69400045d0217051201e4801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 92927005 1250 92925755 92925769
    0x705090f0f09100c0504080129061b0d020c011707020303012c0903030a0e030c10090f05120409050702060f0406020a030207050604060b0f1804030309020a080634020705 74
    0x464690b25115100318030008118074803404800340f86603038540b544d80d40b03407200300350941e804040501d860b01800381d05042d46141800b0480844c1205a44894071030a00c1c0c0400f00f0b10190a101d0144540141e2004082e000d90204103080c0c1c241c8240c842100024055080c50f031100340455070003016074400c10044c08202845686101c00b03050700100d0b0709541c40e154103040180d001c2550601c405030b10200910091514901503459102f82407002541000c036081041c80e601c07007001000d0481690b50f01c2c49038052048091031240003d80101c2240d1098103602460040e5074098030030701d018280b4000100310550710102e070450055003145180001920f903615041c00a40c413040740e003400d02d0740c20080140005c4080c03040038440d900030b11000032015441418001a00c554a503074030f200e041c40350b02c011035241a40c043c1c2e070b8009805180004d10242948089180443d1030b4000294074402d640400500301c41034102024032000004841c4402c4200c203140480c03510041c1c45040250b0400b9100b03001d0b6060442c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 92928255 1250 92927005 92927011
    0x105160f080103170c1006060e04090803040803070c05070f090506090106020c0108101d0615040f060c150905010f06080106080a020112021207020a0302061501090902070302150c0c0705090f0f 84
    0x4085189440d02080b51541b40072040550201030940703d00e010001c10344c1100420900d000155020f004000c0d05581e070511511008000a19190001c00071801d0306204030b001c804d140d54400100d5200584403000603a0100e494800c0c10b011030f040c400003c19504080080c2c5049a0b2140c009140d04031041c0c005486121000700401c00710b40e02c1d22000200d00380f4030501008524044411000382d41051014081e000e50021000710ba80a030800041104007000144102291824031340481f00c10058a81402d483e000d080411400d035040c1341c01c1009000040d40f140300d101f00c9520040aca03284e0346030ba900e8207031842d51203034003911b030400350380c24000d5402101c0960f8120500007005107444e80701c0d20300b0751004505840040060b84000050010540c0412030950000401d0002c404050040c0300024000003c03401a0b071071442d0003203102410103000b085000303283c02d03450400300c11501d4200c1030052140c120182d64120b900c0796060002c2c1c5800c1c845025800303441c510801e80d070a5540c11072a24a405006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 92929505 1250 92928255 92928293
    0x270b120a050c120402041a090703150f0f060c0501020f19030e16060302090102010b041805060a020f040311030a020d0b100b090310050615030103060c120b010c060c02100e0105160f080103 82
    0x5211f01c0099595001c012070b00c9060161000900e06a0041289074000c1040d0004440078240303d40610242c850640750784200c1e01c2514001d48546414a0210b0181c0514888281040b60104400184031441450101d004880e55010085812000c8046a68014008043c0a101a10b10041c00051b10a0700141140d01042c0004243d00c02880b01080490f00340011003810607440e03d44004c100032003401840e8210209a01c1541810110708411405d8071503440b004003034000ca08509485500e0030300c40c40c0d52142d00103050303500386c00032410002e400820131982075002c01c030004c4c0c0100b141c41c03904007a0781014402600400c03900e04808001c00081c24040c00c4140c0c450088195589181030f4180194080d40c4901004207019040e5030b00600000b40f4130190074103039401d04980160903644003071254045600003801044040ca001420790410780c0c41d81c038105000781800d0300911848015005280140c510751075003915030262044c2203440e03d6845e101e500000348140c00400c089a00404030038081921 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 92930755 1250 92929505 92929541
    0x20301061e2c030609030c0606100f080a09140c1c0f0b0406090f060e19020108060d06020408010204030309050a0e0705030a0905031603020a0506090c01270b120a050c12040204 77
    0x142c80000b4602001210b000034603a100194100300d5400038854a84c0001c07080d44c040d001e80c03040d1000030b44468543d41c2110100220000015070b040c0980c0c000d40200c82c0c1180000b000d8a80b014412034030b43d10318989650052815014070308403400d0749880c070040c1c0c0d608080e2006000c0c0d901c0e5250161540041e00c2036a50b6030300c400703581020805660100741c00920407480002c3c0459805e00d024103114010300400060480c041c00ca20150b60041c03003607070740070300101c0703c0c688855035505e002c40c02409250440c0d21590300c04200881015003200b080d1054400403200a0326103640c0340030303040e5440b20031540080001c005101007101c40b44241c00a2110300e124a0550307080008012031a25100c0e5148015001603000e030080106025080c48100e070440e4150340505650900d07a800600600707800303119020145402241420317081e54900799100a88408d0380025a03500750300c21824801c542c00d07200801054a44000b240400040200715094244100540c5819aa070b6030200401040001c80d5a0b0420350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 92932005 1250 92930755 92930837
    0x80901020c07181a0f040906091202070509090d0e060a030908070b15040504050c0105131d0403080a05060307090e0102090d26070b060f030f0f01020301061e 69
    0x81c08014050310f001c0382040c424182116000f000e0361a01001c0c101240703144400e40d1000c1d251039085100155007900c01040300c035130500c4c06c00300070110a900640303140c0140c0c0c590144c0613404a580b20450701c0c1200d50042c181c90303e61300f103910344070581070001c0130602c921001e44507404c1c54005029000401d0400140e81d5200c2d445000740c44d40000c50480707014401c3c2042019540f104108240e000005842c00c220b81e1a00c5e50300e542e40c5640d4901c50310f06210740400c0c10229411410b0322f00000c2c00c0320fa21000100501101c00342d95840f81501d040740400d030036400042845000c2e101d99442204000d00038000940780200340310003000c8c52030424610755001c2007d07901716101c940010444074070542c0c000080390807510003071920000e0000302c10710078441041110049621001e40e03e0300038400319500c41e112107000000901d00391600c1d2841d440c6008035045040b50800c1075004d1412101c07a5100c00003d001c00e9198071203c01c05407403607100400d44130020301525880794a9041884187c000100140300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 92933255 1250 92932005 92932027
    0x10504081603020109080109020901060311041a070b0615040302040c110303131401022a070e0717060105030c0a0f020313090b0f0f0603010e04030318030309111f08090102 75
    0x20000c18407000c1c00c081c00100400841d41c0c4000d1400003060320718020401800c3e943c2c006030381c082042c4915000c054607103d00d00c0320346900c50200d4000b460603a641c900400341003452008240c2040c24240e60b000743c0040090080c1c00d00e0030481c401221814416407505046600304401003000c10b040d1420406004501103005004000950007050b20140300c2541d8a4240740445c440903075007554034110790060003070200c500c03554646014900c09401d40d1f03000c00c50f240318480b850108c0c558481c60500c80d80d10103121000d43c000161040b201c0d6140000040c6aa07a41c00644aa1106450b46a400c4104000080ca080d20898120280890910581e0329000141c00d2401122400ba0022920704e41c0d03d100701d401a00e896101e40c3d450170310079201c00d80c03042340c01000a0020b0205100383d10856584100040c101446640011502c0000203151100c1d110701d4200100202054401101c400c10100b1f100070180c0b4104995072040c40400309224000000601c08031506030002e40a01d00300e640034030810001c2c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 92934505 1250 92933255 92933263
    0x703080a090c031a0106030c050d11090315090c01090302010e040b030a080a09090501080106050109120f0f062c030904240621020c030a03021606140a0e03040503061501050408 77
    0x1180200310780c4d840c1a6101c42850640441a88800f05251900641250f02a08001912042800034400061100300b9003092001480f07011201d503490f010300610780c0021a020068207029a00d14012145a011010015100c00342c103801701a0100c1c05900324144503140c217800c540d480c0e440141c1a120460f03083d555440b601d03085043c0304408151000010f000b801494480c050050113584028400741c2d1400f000a0701460a07405013030452181c0514040c140f0601c207000c0030784070303078804154046051170b424800e0007002c0b1a40311016002101d84543d1079107404170400c210400c45032000c0c42c50601d5442c00c00004002d81e4041602256900302c0c400b503500c0e641e00c0d13180000c01d00354452010f4140340d10341c3d45d482003480c602ea420040d84140018030b480380380001501c158501c2c0f03003001640c0d400038400451002e280000018107040c140792042c40c01000c1049030f1406118040014040c540c04105080c2d100e000d81d00605030140c5c0700c0c00001e890760622821800000c48181080c43c038048d02ca544103410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 92935755 1250 92934505 92934509
    0x1106040f1e06090803060f010c0c06050f0417010204031707110f030a06020d0507030b0303280309050a0507080d05160b060105091906020c011e0c0222050a0b0607080703080a090c 78
    0x80001004000450420813441f8510301070901c1c0603009180303503a0715074222143c640602c00400034007003105821a12040102d9015100440c400007150102c01d01080c040d42c0217000c12204141c00400c40021007124000f51aa00c0c1c1c0d0203005602083d10320014050a00003001907240e15115800710107001c140307203100400107101100d0000c5440e1034032620241c103485807401a107000e03a00400c41111350380c003100d0400710120040d903d59600c08222000c1100640302e894000b405601881c84c0c8a8104140051000c085801c03034800c3d140480e50064055559019000024100d80c000311520000117655003002036001c03c05040c11402c0c0040000481e880c803640284943d440100d00c030303041c0141a01000139800111003440c158100c021020600403510342c032034a81c04e05001d0b142071804115522401d81810240c9501c40900044648002c000c028113000e0703680003092850400502d115007052002c0760322554001000d14601100c030b80d01140c0e5043c004124426240e80c07280c00b000007404089201e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 92937005 1250 92935755 92935763
    0x50a0311040b030d14030a140a1505090907030201030b03070f080312010e040807060504030210150f2c07090e070f030c020616110102040b04151106040f1e0609 70
    0x610302414180030884607661000352080c1e01145115000d40c0e4004002a10704c0c0c42c03110002c3c0c80f13490385904070020300f03a15a200c4980081000400410000c5980002160030341c00b00c00c286000c3d030318810700103028400c0d030b040800c1e90040355040c4055400307500508503404001d41112441036031182c0607040c10103075802c0000c1540000503600079803825256800c3c050502d43e2000c282c04d0030180c0e603040700d40c45403a000034030203a10f80300080c00b03160090000c003e9014200d00c0521202d00341110b40000803999002d80058260600c401250440694514140c1800114003402c00750806c420717200a03250008001c1da0401001c484046040707100c0105050181909456008402c22009400760507210485d04203811544030b4410082c50012071940180e031040541042802c0f440786400480c0a481075821950040c0800240010103c4000c0003910850044d03540c1c07031000c64954076503284c0ba500103071000360102c0b5070460a2404207900c0c0710415032110144a8140c142031441e900c000640b28450b000b03131 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 92938255 1250 92937005 92937023
    0x120313030302070501120c09030b190903051b0f0706050c0703060906050609010e040213020d020f031008062a18030d0807080109061a090402040f08100c03060b22050a03 74
    0x13005503004400111500110303c0244205401d105000b00105035920001d0000850350300800c8101c0c03407644035000b05815000c824042035a150a0141079036001c0c101c00720352039070b9860b000c1c000888049510020820b034000580f8070f0798680341c41241d2541200c95012982d003d0341c080000012054401c401c90070f803260001040e9840d208040108840c0141d2018100500940400c0010ba036203d000034804444106d0040e1582078280d1424020b000d03803101c900300010300005018402c110284a90b08031041442200c07a55520340c0b581c142c83d00d600545248450341c851800b044103442242c042c0071801e00101400f40e01c0e044c0080040c0c45c0c1042804640041a920703403e2003910380e4400c03d00c0d80942000c0102340165880d104a00003503003144c40540d1702d440004120102580c1c0c854040301d0061024850043d24243c480040c0f0b9191464014054580c034a440401c1da01240280206000c03151034601c458189080c008a40f8031141c4c4e80c195000c0c0d418010070011915aa52602050146000d02100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 92939505 1250 92938255 92938259
    0x140c0f0a05100b06071a07051c050613091203091106030c1b0309010903061808040602031b06101e0b0d060602100501081905070e160f03150512031303030207 69
    0x106048442d003c140d24061041000741201041e030720580600e4441260700281e0441c1d803580700860389805060140040300c488088010f62003c00c84d082070b401080100c5a0340c141c031410140201c100c40c041c81c00101996080310207814042d01a42c040c8221500810300d80c02005840c0f400a00c0365482201c0182d1144008501784c0d8800002414484405605d80000d500d0a0b034600000b81000410f848010610f58072920400f4140e01000c09406640d9030001c2c800751100c0d100d10b000f039141c0d0440c2e10007412854151030810480c900008810340520210010380540721b0030450f02d883e4190300e502c4c1140319503a40000c0014000200c43c003c0000320610800000e0580c200720b8000e052091404415038030702d081c04018800000c000c00c1440d00386591441180c07550480340b8009042204c10707804490320742c42c04010842ca1244540d20880c114946980b611920000c8180a8007251644070582460850844c0c0a1000e8205101c0444080620310116810031450050f44200003c4540040b4010703000b03e001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 92940755 1250 92939505 92939533
    0x307030504140a030b1f0305070312020d140703080703020705060f0121120c030908030d050403080a0e07030b070302070b100e010e0f06060a030b0d060902030c030706140c0f0a05 78
    0x680c0700c111403c451500400e440c68030b40c42d5000d48007a00d8400010380a4800010346d2400707020401c006c55221060f82c44403650390401d42c451010750002038002d800340241000c1050304c24824074070701e4494444214103203203550324100d0b10a03a00406000c1455400c0186001182040220a1041da0502505036041d1f051091580340762607900c001c0380004007172450300b4000a00d034074580d1512007090701d0521400d088034203040f82c0040d8140d2100086000014080381040341682205204500035100c007501e82e203559002808544880d000c03a4007907048064203000045002c42d102c0d0300603005250250810015840d4698890b5003561403403440340d8100c0040001b80000c0000c0d90040c241c070645030b60180742106401c0d50156004111602c120800141c1d511454003d9000302404240502660788503800362405000601c2d14481c00e9219101e900c4062260b031a0015190083c0c0301c071991021400d0703d840060754500c2d0880c001182d01ca002d000556001c90400b0440400102d000307000800c1261300f2518 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 92942005 1250 92940755 92940779
    0xc0902030705162303090904111c030e0901050d03052b0c03230f040b04060204150c0204150503030403200301021c0608120f0d14010909060e0c0f06070c03050307030504 74
    0x1d84d40d4065041440054120382d64580f8880d4020340151070141c0d02e207205000070314502c03104400c0c02c13030703038440c00c19001e007403580c402c81900d00010280c0e04600c4c01c1e600c7da420041c4a00c0d1802c00100010701c2000030481115410001060010a14440d13500c181d0503004148240c0d20542c0e0400006940c07444070041740d90340a441007a00745400304600b00c42d810711001c91405044000e1018045c86503010101d801c01c51554115801482c0240040c000c1c614284402001138040890a038400e500b0300000300c00b007007940c00c1c0c01021103d00034001c600d0145580e139880740c52440380a504a030380004100e400c0d030b00e4501780024080102e1034420031a22444d507040303800480341582c01400656100b0300e400010219040c2c01c5400e41c0b03502c02d25054442030303101c001201601c501e280b9054042500c1b0000200800290402c902c028440c07103050144113000c502e00ea41d29644a0f2850b0390044400c8005210360400d4401081200c1c0110850205180c5a41340c66155901450007200000c1c80002c0401c03060709154 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 92943255 1250 92942005 92942063
    0x305011815020f040608090c0307170609060903090415030605070801031a061e040e0d0e0109140d06090807050114180303060d11030c1207140108040c090203070516 72
    0x3250440c00d245820302500071030f0055020f50814003006c42d000c80c100308010006110942e5004003210041754558030009641641070b080c126651080001080300d0882c040740d480d2050501c00b00031410420344030108000741c2141890210b8000481c40d01001143d114000c0310f12030342054480c5c20702940346141c05c0c404c10a100511403d46020030080c405203580d2044d00d0184030320300503200c4c1c0c44002e0b2203000900404a40405116a11030101916002c507042502a110310300300f602c880e002640c2e598100381c0b5102210110b550b203c030304000000c00140103076008180d5540540101070500c02a035803040c2c01c40709200701c01c01005481c04d04000f06040f403c2511000c80203898095402c506111000c641140007401000f0084119030309000c201762070400500003045401002030201c1d03c0e040074056198003881c01451401c0d8080ea403442d40d90750246030414065a41310840800b001e00d0402d80000941003d04800300704a400c00000240062030400302d40203900070400c46968600441255640202003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 92944505 1250 92943255 92943293
    0x50102180d0317040218070207140a0302010206060d230604020a0603020405030c0d05030f04180507030e0a03050d061a0a03050f010f1e030209090f0601140604090c020703050118 78
    0xd074107400d0029602055407500381100300c0390810141c50b54400504c05410f89001c200d10841c0c524100400a503000500a04442d00b654000d4482c82141003032000c3c290700c0e4000640564014804210507040400c1c003400c056000c0d0b401d1a80d1001100c02d95000c071951508000d226a0210050000707500c1d240003043d004000600302185081d15003004030313446040c403a0300e503489510040722203001e01078240300f2191a1038481b41c0180c0c2d00d40d1501404010000640c002c03010092a002c0090000b0b07001c3d02c91060405c0581c0020b01400c1240e40e821550b07a4000b0030200750554590070b00054940c035440782103020302c001da0022901e0b001404c00041c100d41d00180844618007900004003c03000300c09080d001a104c00c15025401c00051800304180b9071382c280d2000b900402e40c001000b1a80c42d01003161000701401809032012640d031100300028110403c12544e510030342c01c10003042a00102e9204881090190042e1082c4a903640c9482e402c4074044241c01310b120f00703100b908608006a42003996050181 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 92945755 1250 92944505 92944519
    0x12090c06041a1b010c03020a0e0402090f15070b10090c09050906060a02030c1603290604050702010e0604030809010b041b03090201090b0403111806010c0b13080705010218 75
    0x30b4042d0a2018512006070002e0781800055001681c20b40407540040c40310901c0001e0040380c0320389400400070f510a00000c0c00198825100190524060003110803140005002a0803168070004111440742d06a100e01d0360800200081c0000895619425214440340406140310b6071030310002100742c802003240c500400800380814042503841c51110380d000308d000c0c1c4690b62100b0b9044d60a0b0f2841c492140f00303000b984200650314411290007150b43c070a50317200f40070503c3d1468017001d02000303d0303001d60300022160048000003529402c2c1030340031551021080c40041000c1c1c50140c4a281000d82c113840560005108030300f000802d030801d0050490030f10050781d0401506041c00460440b00c1c0e0744010200401d0f440d95030000c1507a100788030990103440e04c9140c80343d03100c2e560324042c00e0002a2080300b900405241202d1000c1d10440b64105108080686418031240419641d030807440c28000c01c0314888108220803c400300e0498005005900d108500050703030384000c0c03042500c00d02c180d4610301e4801c0714 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 92947005 1250 92945755 92945759
    0x40212281103010608060609090f06010908190302010605060a02101a060c010e010c170109020708041a0c070e19090201110f01060e09070503070e0c07062301090203010b0403030503040f0812090c0604 87
    0x649041059102b0301c007249034401c40c2c4510300100da120207554070a160612034806c10880f00c1d50709800c0090701a119800070041146d1394400e218241c0282c003050000360300000c034403030f50800c4190007483c1403041a84d40010b100300035000040e8aa04140c0d040c8500c1d81d511080e0440c08202481900d002801c2c07410070b02c100107141c42e6904100e0505004c0c0b0800300c0c0c7c0109112081216850985000d05017078400070340040e4140620500380c1d045803810203454450b0150001d00c06508016031409451b04100c07a686003580424000060030507140101d04000c000c082120b001c003810300c00c2c111040d98010000c84e0040ca003c0107128280006040e98215400c0000108941c3e9030000f1640101e49080c0c08009056881500107070707d0340111031015105038202220065100f2102101c2c0c2e400011655844c0c04598031941440c08174002405164a0140b02304820f0010a0107080a90760142c80f8100414004902c0d17034602c2d0054001c2c0b4090700d50408858180040083c2c02c0c4080c00e2030400c01da80450a1034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 92948255 1250 92947005 92947009
    0x50a0b06040b28120606030b060d0c0c150207111e0d0507030c06080f0f151302091503061203070302070303200610060e040212281103010608060609 65
    0x2100e10302c03540801ca2030000703003401c00d04044189921402a25200d02c1010703458944040c00c6004007032540c41002c0e00d044000304401d4003a125107107440d05d010b4a1f9501300007126044100510444210f04107202da1030307214031b0008400b00014200305650708005038940c0558917000d000d49000c0c1503918425080e56490858a40c4c1118029900c03c1c0201c1d003040e0381c0000c1e800c100d8180902c1d500f010f0545903100801040c0301e5005403020340514106500c190650352072000300035500105807600c00001c030305004121168904030b0381c42c3c0d1400d0001c440040c907214441c40002c006d8030700c040b820f4022903004020840b161401d40440000c880384580510f1900080e5036000b0348450081c04004d040c490040b02a81250000e4414181240038500442d81181000c2c11f11602072006445100000f5043c02c0389245541441e0095804400b101c0000100c1505c4e40394821800b0f0110100c8078020100307903514000e52a4850060144100c05c40806039030301e50602c4001403400308014078081c0600c82c2000060503507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 92949505 1250 92948255 92948257
    0x304020906090c04030503070303021b0a030f0302030c040e011410140d050c070b09060402030f0307030903060b03011e0501030308010603050c0d05090111070c080706110304230901060302030a050a0b06 88
    0x45041190580c0142d90fa10310700502900a642004d0a984000310310001003503019401001c1c4003421140b501540009030465580e42c400b200c400400007a645141d4400300f0380a60047c1d0340003040140f5503403c0c207449600401c1c240109920240b1450303070594a41d02d036410b1100b035041c0c454210b0702d040d410f01c0c6030007483c0d1400c5100b00381d04d880105070350700006135202c2c1802c000e03140017941c464540d01c1d503802c15404d86a074607041560182d1081c043c4881c43d81d10000000221540765030b06031503a100c01c602e0364440348010032141d04840e0b0503540340c034060281c40781c0d4444110001c00340d41a0001d01e079415810002c00038130050304207000345841d002c14022059007402c160b0340c082d02051000314903a078450850b00e000d005400501542c010011441e2010002d0390014501591104011590300341d981d504125890403100911400c1a0410070060042e2510340c1d288852942c0b20380750f00490f441c484000b081c40c24030240e1182000070f5001c001d000c00d110ba10301a5980202101500340300f031540d200005555 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 92950755 1250 92949505 92949511
    0xb1603020f0f03040317091e130207031e09121514010b04090b06030c18042409050606030f01061803050d080a0c0c0201020712020a080102070302010c020f0a0c03030c02010512010b09040f0203040209 87
    0x290550a100011040e035800c1c270040b40358804010299100c2d200b6207406403207000c08100b00c0031139003160a08040c419110340403400845400e40c40030345131050070340c8601211002400d0715189503921103d8802903829880750850007050b80e940495500c030f01d03080c400000c840d88009101e105805c00c01c140841d0841c107000b41d55034035041440803a81d450307038000020b00400540710a030303502000103400e0b0201c5820b14001f0000312001000c09024903500d00741041274a1004441c0103010142060040c84824429070b6a20756000350030021151207600e03030300d4041c5010841880c400c0096540d40400c1200c481a008a048040940c107201420b41c1140d80040d4640186004807003594501c095003000307658070407010074000c00840008655030440c50070002d001c1d0849810000240c440c000c40c40540c02c00000708440403980100075904218103641c1c1c2156601034981c002c1e4104102400341d01005441030003801e009002070405250307602401020f110a96910b000d0028000384144100000368884042c2c00340c4c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 92952005 1250 92950755 92950789
    0x41505060906100509040c0525020d1101021906020a1e210603021c05010605010908030d1d150601020f010606120b2b17040b1603020f0f0304031709 65
    0x501450503e01128280a0070700c85e290b1003400c01188000c00e9401c02c005065500202d1b03070801140c4444240145041036440000323400c04a00310320307000490300d4401c840c002c00c01c05205644440e405415101c11400096a0a035440ba90000703403060719540083d01000d4641c0362524419100540d008040c0c0814210f0510700a086901e1100d0381c0c012500340d000002441c0d00074102c0d005c0e2002060b0030148002445021201c0d50300e0724401042a40c0075041000454221400031440c0c0300c40016079030083d00c581002c0c250100b00020462180103c18400e60710b402c01010840c101518000000901d0441030024140683c0d1602909109240d4491a200e90001e40a2000b00392842c24101040100e240300c60b5800400e92140d440440905012000d103c8650103204400b03860941100900c4040c0304074400e896509c8401c120807247d45001d840d00241c4c190180c01a520580c64000303035141404030a03014980c40d508002014001c1040745062061140d40c681587c0d0b041121544c0411195003542008035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 92953255 1250 92952005 92952019
    0x1b03031f231018030803180307080a0f0c06140a200a030b0303070f030206010806060a050603071805060d0b03010e03040e0106141309290306011701150806041505060906 74
    0x114202d8050000c0d0403190008030291440f550f501e0600d20065003080c3c3c0c45d506e10031894040c2d1048420004151031034142c00c103a13040c2c640801e01038240d690300460402e2101740303c407280303e64011401e030f4460050345072244424130b00b55140504c095001c03280030448070070ba040740061a00d90300510720341c01d54038034400a050005005003540d0009203180a02400101782e280102d441c901010f501180c29412250104112030b01c035183d01003040300c0d5081034015141c1000080c000204454400c50f40c007009003007190604241d950705c90000c00c1150340036031003414080d80c980501074181e017801d00c00c098180203580003a50a09043c540849540541032042504010802c103524681000c51804c0b600020030002c040300410765200c0700c04000d4030102e500c4041c41c05d00300c4003281505440610745468110028050135603682070090390400d0f02d089400024841d9620342600148403240c00010000d13205280061015140c00c1c038000917100b007044040441182804240001510360408040e00320504813509 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 92954505 1250 92953255 92953279
    0xf0f0806040c050c031306081806040b0c1603030c120207020307050121020d150e07020d030c021204030609060e0d080112020112050f0a0e030a020705061b03031f23 72
    0x11034003402084024130070b0b800700040100000710107840b00000c0328000e072550445503903150214921030403208a041d450360031a10010b4000b450360700d035030381d0b01c005440c00f078a0910280200030105041c0c108002c4022a54420344800c0341a00207540098200c41d10109502e04081940480d80b100c415105a42c14071040c0d01701d99920382d42c00585c001e54a000600d08545401101c13000c070015140022038815490403100011a2180c645860320748518401e4000f04a1021903e00881c02045500810403c602628000100040d040c2c00180021030203005d0210303204030542001401c80317800702c08031503855200154006072150040c000c00c1c111141501c0f035810303030000d900041e00c000f2403900300f01d00421718000c00c0100340c410b0000c00342d01849503c0c404220150840c00c4003039030b901c220710103140580d01ca20020402454040002c2c20703042d050303980070031118503605c840ca403660300151070b0061240449120004003418202d6018001d00c91702403134845140d04544216520101589207a00401d101d00741 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 92955755 1250 92954505 92954507
    0x30406020f0708030a060501080c070b04050309060c07080d0306060f0806010e0901080a05010c02010b030a17041a041505030c0301050d050c0603130c14100c050c030a120f0f0806040c 80
    0x15102481c644141c9199503404a2411049030780c001c90f2500001d81c648213001ca050352190b48020700c00e40d240d113086445d0580c00c1d100d16041c0341000304101c2d01c5100c10410003106403604805080c08032000001401d0450811340c460f4200480e9141e00020140744c0502080300e10b62100401c09591154101014a0784826004030341105046481a800c4101c0b000001844200042c45002d42401413008200b80c5000720000c80c03e1ba00c1020300c0b1681641b107482e111000c210101c1116403904a5120401e103480c0c3e852700040246014041c406d5902a0085410454000d007480d02c41c42c4c1c403100b460418914a0003a000014600040c0121401008090540010454100085912128000c044c161280b40140b002c3c0c2c0d40425280c0700712740c045c0b41100000303404503900c6540c8a264800402d03115039034080907000c90306e6503030311f2200f900c4620400e100030b40181c4052292580d0700d400307451030212001c003000d00070740165003512594080000e8a620750040d140c0c40070040b50011000c48010a0b00c05907071034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 92957005 1250 92955755 92955757
    0x30d080c0c01110a0e0108010311011202070506010f08240705070615142803020111160303020a02090c0910180308030a060306050117032215020601030b0603012003040602 75
    0x9840d03800e602c0d28403e00c01aa10b224084c1080890301e0750380a400d0300c1624011600c08000703100060107811240b240c2e41e80d640c0141c850003806140c24000508120301c5407510380c94213200b80d201c0d40a244a44e1018000741d1000d001c41c5e2100f441808402c0b20905003285424046900146010704006001c00e00ca0100304154200e18107650001000d03011803034507180720386030301c45000b00021320032200542c0302206c0c0740324403803040003214500c40b1074207240d0b107547c0042d55841030308280034034540030b500158035008100c0c0700c04001941c040d80c0108503c10081c07040c0050442c002e8041e42c110107084c091020079565040740300b04244c0d26403420070009544241100c0310000ca0b900014001c04011042090124055100c2c0c000c0302d00881c0c0502c880d0341c3c2e4001c07504445d1812a004069a00108203001e6031800c440c4544174503013401c0881d2007000d0750b511401c84030007181c00d0306d40c03005030480b00c0104203016180032481d400030b500314002c10450003c0105c2c040c001c56083d002500e00040400042c00340203250b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 92958255 1250 92957005 92957017
    0xa05090d050304170d0207050d0905120604021509031203010602100e0a031808010e100b060408210409020d0b0109050334050306101802030601090b0702030708010f0b0103050105030c030d080c 84
    0x10741d056441c1c11092030301c0c980382c409e4102c102000854645000030f903460070005114840070548042c007096207650f020320060000d411001b100455040020000c1b5480c20002031074101c009070003441d2254101000282802144500a88481e0508038161400035003c20200041581828100301c00041200c642113006007035441610a9440e100c0c090b032801d48040392022407606000b0080080316500c0c0300b00409030040c2d0084010f80d40c0880b028a00214010f42e140000600351060075003413550307600c0d496099920040103420705503251541d1000958100d501c2d0310141c0800c401804400352881441c000020784203103031844084a41d20f03074820150038201c520003d04405425180705192090015050308400d1140350030302d400c91428011700000328400e903809298141e58448605142c0300300050680c1298109a031f0502809000040d103d0703007446540042500780b14040b961202c044000340460b00161300080c00b0350030003852030340705603404110185c00b04810b050458940d201d003c40341c0000d020744 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 92959505 1250 92958255 92958277
    0x71104111c0e010513020a1a1c0615120b04050601020c010302090d02150a180602030304030c02190e090c06030c030406022b06030611070236040b0a05090d05030417 72
    0x60113020b03040907030b202c1d10280e0031b000b40c60503000e03265143e4541a04110000352400340d440f040c0710001d070f14941404c040320400300c80d450201f1443e4a413091411200642c081d02c001040381d0a00800b6100c105026465010800311402c000354134040c2d0010f5154a0110a400e04060740000d000d11203a07520714071404525005841040002da101090b04943d030f10044000000c90803014140359490345d0001040103803000c40c0e014500719112a501075500c44c0041100326400704121448600b54940c40d800c600013424030715424911810b00e504503d040c040382036107440c003c0c3d42c00c0040120401000040329040399011310010794800581e500483c01400c007440605c40c01c1034150030017100c1e241350340041c2d054178000c04041020001000070580984070f402030007034204a2080030b1400d4000000d90020b40d001034402c0107958034418098020b0140d80484044130828021014044032502d0b6104840c0d100502c40f00a00e1111607640024244e804010401050603805c0c603040c03000d11701400250340c040002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 92960755 1250 92959505 92959511
    0x3060111010911030f0a0c03080d020d0e07060e030d020601050f0409081603030b2707021f0204030b01120812040c030204050a020d0b0108010b0a18050a0605071104111c0e01 76
    0x99403909105001d003826030113100344145020200200070100c1c4015081341e10407504001c0038a556034171b481d180c110034164005d00703500340204075800c4030324090211111415806400f0762400c008000d00410444d1481301c0c0203a0040544800b05500060348506540e002c640090b550b210060019010b0504000f008051100116104803019812a1140d1440e48030346c6047c0420310b1b41c0c03420310040e250341b403100804104c2d405030442031150003030b185aa00a03c192056410740d8511f00010041d541c0800052854523500080800c00c1c05406810f0501410010070307080c02030001034a5104042c0240c1502800c0400300401050800c0001000c01d001180d0180c070600c09894480c1c1100000e410001101540c581003000700d500070b40c030843c0791a05844905282e42d081140d261001c60f042541c0140c2d0100f01141c04c14089500e540b80310820f00101030a68499680e000e451400d441030801b0841d420380960700700300c00c11401d0b200707040c16103c01c00703050305128080c2c0b82c00c40b2128015000c0b1001c89103095103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 92962005 1250 92960755 92960771
    0x20d030906020f0a08010306050c091509010215100303140c030304031d03060a0e0118150b01140c070f06050712030b0f0405010801060f080f030318071d0609090a0201090b0306011101 80
    0x103000000717070f81200d0040d03e042003a6982c0030354070200d61040720076040e400070103030a02c6040c0e80a00c0c0c0c040c00c0325000c1841200e5401601d214461607808003610300105a10350b88404000705548460083c02042c144071001d801e0804205800d035507800060401800e01005030b4180f1484400034401040d01d581c02070896806007131589814000740824401e118541d401c0c000c8845c15021500c0240f00d10a81c4012506003407052040d07802d00403c2c0440030340d41001070100c081c4503282d810002505692a858001e81860b83c17810a08407400c1c610790b40a0b038240315050003000080303040381000d4034040d40c881c20049020761041c000611904040c80c101548246040300120f4203100c1540000c00b610140c40c1000d8000d0789580c142550b800510070714003030ba94020000038021010300c04014080c001c288044131111034039401075080d01130452070a4020f0821640800200c3e00e808102d15400c040000081c06030241c06800003002c1c0e06031405280102e120000101d40d699216075044004002e0382c030002c1220381 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 92963255 1250 92962005 92962007
    0x130c090603020f180601052d03090f30090409030207030524150d0212010c030c0903020d2301060806040203010c050903030d09030302091e12030307020d030906020f0a 73
    0x1050502059000d020700c08403c00450a003000c03500b0201d0880c81c0c502c4800d6a58900450b00ca5008000c1c540781482c00e85d0311240400c0c9120111598402590b6200e9100d01e0582040c03854103c0b05001100603512801160210082c501c20807101b0b41c6110740c8200120140400c0c80c030040c0b03e04240c085d041403500c0301210615602103684070a0b64403a00648403070440348420428450625540810120904004180e81000c0f05010402a0780003518806a8242640026044002504603500b090351140c9000340352582c10310600e030710800c850420905c005d06607008078120320100f0a00900302108903400c1c1d000402c0a04294440120303040007030140ea0b803a0ba880980f9801c3c2070324101d00035800c00108192860245041d50380b44038000c0c004508141c8240001001786c12118419000d05070300304420090f64032a0303460083d056041016503d102640e8105100000f400b070552220150000c2c400d00111a5010a6603081500146808501e205207400c0100003482076400f018808000003400302841c03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 92964505 1250 92963255 92963261
    0x10c140712050a022e0c02030c0402030705120a050c0714010b1009061106160c1a161101110d0903020c061902100c05040608041406070503090f0102130b03130c09 71
    0x2403003522044942c12444007651415036078901720b056900c010b09416008284511000718805000400700c40c100107155000c9402caa20035207842c0005a0002002400c41034040a86500103541c02c6003002645081440032181d40039900c2c00501d209a082d803603041d03c45007500405019480101036200207000001c01500944061040602050b440d00e0b90b02116813003c00d8aa1154030003103080d40b800701c0791810854a486c1158002c88101807203241c2c00c0310644071006158420032804000245a0b04500b1000c1c2102d03050b54070103000c5070704141041d10307000c1095050740c07000c50b860540070a84100900e000c0c0c1c100400203403800c0e003042c0d02007180c0300000710700c00d8404a013800365000d03240545429201c200503103004e00b400d90003181c030420081050760f10449009902c180200252100c2d41150480d09041440c00c1c2d80c0748000440c01b00c2404182c2c4c40503c0b81d03a08005070180210704d0f11640d0b00180c4009002c0d481030000100001c07001800c095991a44d40e508a940800039540990b00c4114078402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 92965755 1250 92964505 92964523
    0xc070902130806010305030306010c05030d060b07020909010203040f020402091318060501080a030c1104090204020d090b0c0403150e0307050a060e0d0903081603030e0d0203070212060105010c14071205 88
    0x6500c1d850750300140150011030068107981d00314015510f1540c9560055400000c050400c490b0751104020081c804000d41c4641c1f00500751814960744d03560418010003c02441c050b0040d6402d0340b0406c203010028441943c0c50203510b80c10b0740c01507281ca5806001964151040700031005050a2040103940340c103c0b80355035101244a100c08100590325440b002742d843d4041c440c0103000c1541d03020480007290f80c0365041c04000ea801000400c2d107507500e9000c90183d80291014542c0b194598800c3c00802100e0841c3c140c3c13001d6070351a486c2c2000c2c41c0d41c135000300c0365090b07a0003d20307000e03500c0d0540c8119107002c1c012210100d40000460321811024a810002000843c840c3d180e2401140c00c0403241c01d105a41150499030070140072400c003046500e0040302c02020b10000c500745030391040c070301d0610f0005001420503d501078002d540c450440380184840d00d01b041e195600103401510060140b41e070806100646240c1000c0417840310b032070311380b000380c544034040c0c101c2094581d0140e005000c10a00080c0804 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 92967005 1250 92965755 92965777
    0x50709180b0f240406170d030c030c02100e190c0e130305030402010819060611010617070b0a09030206040b030106030e0f0601060513030c06110d05070302030711060c070902 76
    0x1d4181c1e2410482c1d280040140c0c1c00d0302000d0314500c0c0e07422094541000c04685120300a000003507241d40e4010300c070502c01c1040503802191300320060030358480350948110200c0b800c45050a125a0701c0400d070094403540d610682100a03540d4141003c0c10b010104180e05668008002c25541480c03075040041030701c9442e2080c00c0710080340340300183e2040141040c1d140d510f03501d5140c13241944c68940c01540d40744001810f02c2f44041007880629290300c2d0600600c0024001038a030781690b03440001c101c501750b58498000d030020890302c1a0764102e041c0001058021100101003c1d030705c41303800f1a02110741980660019510590209022510700d0418000314104d4655803010408407414503c901e407500c00d1142205025003025004001481c000c0c1b000b003582c66801504010700b1602ca03900c00300302c0d07075450300309400041c868480d00600d40700c10016640200b2003402c00600f01091650025500e210b0010010035210108100b080b0f181c035a007090380c00ca6103900c020b40d4041038903940303020300940008180304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 92968255 1250 92967005 92967023
    0x1050a091a03071d0c09061b030c060a05010609210b070207030c0b0306010305010501030506150c030d06120b01050d050c010f0c120804060f0605060906030601021e0f0d080c070f05070918 82
    0x8400440369411540c1014024000c0c030b040032035002321543c2880390b4244000c0ba90000308030b0391084130824009180b00d140811000184c40d414140001e04a2166030421020b0b660901a0f4420340d0040182c0c010b111035020150b2596503444910490415035180c0c00113244040b03181000c05c048800c0e101651050358281c1c0e0400440e80e8800044040d10000d4401c560800c2855203d400154000c0c001009062040000c80e807401c0d10303240e0a042110340070740c4030201d100000030320702080184003803180e03006050031282001889029110030351100300c00080181482041c1442000d65409540d4403010250071510743d04060500d0203000d0f02292044604940395403811400c003110308080e105440c15144081e0000f410103070401d05018866001809040c103510980780141c2e4202a46d5484400c91120003010f42602c500b000c154a1401e100c3c62804001d04c4494000c22003d03994082c1a20003080c3c1142c9200ca10091500b0264103200d119084072a100b4240031907041d500b655560201f4056101c6e01c044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 92969505 1250 92968255 92968261
    0x70506070609210c020d0c1205030405120c09070813080309100f061413090b010b071101020613030c0204090804260102030c0405130204090906140f01050a091a03071d 73
    0x10420f000301c000b0704000300b000c2040283c0942800492034801e18880c8007003061040d161590014401c00c000d2003165650700000e01400381e400d100c00540e20040c0000c0050460001710030001e541c0010052100f01040000f20016176640030f0750140303402d07803030301701a666580c6d0400c000c40c0d5489400e88000b45c2c0c0d0540c04c2c0210b0850b6240380b840340c4800c85058441103464a41c00780300b001010455410515010341d180d110720000309481405540c001c00c5918103240e03540e41685000000d0b0984003140a040d50000c90800c03107420030701a08924a260716291200f0b05003843d200180090586040141c01c0c00004a404650034020303190518168190180000d03600e100c03800c9460a034031003141e502d410248144401c000d1810107003d05840d02420980c05400c05495910039012036560170380548116884030384241d2444800315904e42c000c0e00b110981400c1d50305000c0418a503019910400b80903664035102c00704000202034840b0201c10009082e20407080e51104214000d0456540000410003a6408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 92970755 1250 92969505 92969543
    0x9010612140c12060a0b03100e07082104050111100504200d050729070b01060e0405040b0613020922060f12030c0c0302060a090f0f0503061602070506070609 69
    0x28000034070342c1c2c880040c251592a04c4294001c6e2010b075501135014415025601884200b80c010821500c8000c0020700304180760a140034545002580040300c400551110355000c5060700044400303941d000e090440204040501d40c5203464101400c5540075442d000510040004003800d100311b6071000c4441003003d2101c00c04101c002c42d0304141c018440c2c0d004c1d02d01001070049081c0c026602c668000320300507500380039400b00d01503a0301c4050116201300c1d00301c0040c8105900440c02d1090310400380e070100060310b060750b921007007000c0242515125094550051801c0c820b250101c480c0e0714400f40070440c1000326aaa001c586031850940c03c1040c50070030b503010414010041004040341c0031034410101260300d5490503152141801003e85075907a060b400800503803218401418002450340c0c0c1c61000e80c0c9000008881d0142d03070380211400540707022041200d81d9001442a800c200c10048445001500d400305921306081d81d80550b400c500041112014400f03141d0000308502d0256030360307103540e10007c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 92972005 1250 92970755 92970769
    0x601050114070615030203070b09030601090608060a0b041d0703060506030303040308130201020327040b100e090c1b0f010b0906100804030e092a0f0304020909010612140c 75
    0x72003109a04041c058a4041890303a0000c8103000003440900c402d4540f01c1e001b00b0b04140d50740e04102001d84000800762110f040c10040e03640180b0100b00200419401e00c0a000c0e02e42002a014840a584500e1010080d980310760022450b64038451603524500d141c42c400544a018610054070313a0751402000489a00300070088038411603040d561b0591076907420884c001c6d190480a000d034110300c0107000d42d801a801d003140942c25040e1400c0d908070100c602c402044142c9201110302c0340503002d03141c420328141d5002a03100240f008112a610348950300e10606980c14002c0d84110984412040050440e070100818288060702150000f8403e61040300144418144c05940803500408940704620810744641039003070700300d48280f80003041c1040042c002954000191080c8910364064400d285000d031084041d612502d00f42281d2034280503d4104007200d900000780040d0080e84940c0000b00354113020740c8001c010300300c038814010318590b65040c040c50303031100c400056130b4a1080d00400403c0e444c22078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 92973255 1250 92972005 92972027
    0x180b191416021c050a06050402030f0706090b07060207060609090212030f0406110319081f05030604060b2206090e0303040f020103230108010507030c08040c050910050d0b0906010501 80
    0x14000d44440c1d03000798207118a00c0c041044101c1003051100c072030340c0001c1050040c0d440b1640100c4000c038150403d401010f0910070221060504c640c0f180e8810456070f500082060125000c0b0000c2d9500d40b204c070b0805101038403c02d6001000359242120111780c52901d9401400110700a4800c0710016542585441d945d200309803000b42d2240c0148410002203204a60052130038ad1140c064030b0900c050001c542101101c020072030808541003804204400c110300d03550f46816038900850046051420003c6521050040d00c0a0300e143d49840383c00e101510b0320751100e003600c0044070886450f803109000c444000d14050140910750b80c01c0c4000980c103030301c00005607405645c010181c010401003c2d4015002030035007110300a01d14400d1004980c0e00180c0c1d491090081c4801c1d40041810f103400703140101100d5030014040103000101040c803010448103c646010f4400590300140d003030b1500c034040d1078400041e41c011070f4403054060345003003000700c0030715554012800c203011181c9990703e034001035035014120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 92974505 1250 92973255 92973277
    0x90b040311060703050c0f0a031e0c080a2601090b090106020d0804020f04020406120510032a090203072d052b0509030c060105011b03180b1914 63
    0x440306140c245040002000ca0030304c60f080451400b0b4141c8100c0341003161a50b4000310682058100805244c0c0084c3d41d8124408100c0390801c17004198030003c0c20140c101580901070500100e9441c08050040555140c60795500c44411100403074001400300f1a00d09001d092022070405034104080c1c20000d0040b410785055401400600c0c90041c0110707081c00c001481a40e005040d29031810007521035100170405085c6954854114512009440c410303180701a140e02044402d4920400104200c110900b41540b0b043d00c8001d0058015880ca400d22030301900549112880001480b240982118050b12010070f03031032840c0100300c49429a0810002807501c803101066081140b5404801c0c00c10001c9441c64240380700c401c00c80141c1548008864044882c0320a82d40001005290290100100c5005007406d20300710707200f006003000b0003d04e01c29649004051204c0703110407502d180c1c26900150080c09070f40448507180c90401e0746405c0008036420070700c2c0110b1100003100c19000064801c40d1000510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 92975755 1250 92974505 92974523
    0xe03041e1a16050a082a03070f120c06150504051006050f090d05150103050f0a08090409030201180803010f06020a21170c0307030b030f07030201111e0d090b0403 71
    0x903002522540b10300c02c003044480e03014241e20b08001800c002e01030b1030404141013070392002c52101c400000c400701c006800150b15520900c80c06000031782c0703081c502110326030014080c00c5444985d84113131903525201c00018081e40c182640000745095a003840022207404480c04d01042c2c4441d911509614810f0040100041c420044060110714071002040c280b50007038500d184030b40d5161200c5042403050000d40c0c00311107541e8010024090b04000314411001588045c0c042c0c00c02e0b035507070000d01d4441c0d850b803c3d02494035140801c0a0500070351080035030a00b01072481295650901d400d801c558801d01802c2c0e054a03451002054080c8000b580ca5900d951003047d2509120fa0f00645030032618400300d208041100c07014003107042c551900302489c000d800700040305d900c0b42030522014054803641c85540340250701101c042800380303000041c042c04583d02801e08075002d1413840d50301414004403004190f5050011992041184000111a1800d4985079610f031348198903810b0f8a50f8903c0703948001313881c20740 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 92977005 1250 92975755 92975767
    0x20c0105030907030501050a0c020f03040b0702010c021203030411010f030b0604030b0c13180b0603040b06041e180b0c03070519030b0a08031e0405030a060209040e03041e1a 76
    0x1000c0c0c00203680000e810001c82d80400e60781c0c4d440c503003076460440c1d81d100400d880300e10045020f0f80402c240c990580542028505060030716094800601840301d001c1e0401501c0031001d410354981010558084011005407079072890242010410721405154440c0010b0f0007a202d40a41c5104c0d20400c8019400140400c3c6418a5500c4507c81d14002034820001d58104201c1c011060403400f240e43c3c0109481c0b10030368034040f10302c400130040b1101108814000d1004000f040002501d028036281d00c4902201c00007151480c428000743c090042c01e04810510b86400c5100c8140d03801e410340c619845110308900d203800c0c0d440c58603c1810340821382d003c03000300b101844640c4c4c29a0a029024080c103c80345000210a0810720015244007429444021305800001e00c0f803e0f040f0010207074400c81590010014502480e000109071748120040000d041103501040d204580e80e240d4010004060301c06040b00e13116601e030b5800f0350721700780c1002c81031808080c2110001071500e070300c42d80d0440004008055a003002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 92978255 1250 92977005 92977007
    0xa08041a011a03060f0a030b0f091903050a09080111040503060108070608180a0b0c0d0b0d030f03111c050609070f050a1b05060103060e162d0308070501051603020a020c01 75
    0x20f04040c3c01958064114031154013151a4407000e50003c5000309841403c5043c014407100380304401828110082d0444003000e02c8903404280d02c0440d65070700d443e1440d650342c1c0c0c1d5201100d1301501500026225403c0042000390302550001400540d8811001e40300c540c0d984103001690350542c0e104410105070f07003c000a000f1000607820012000d01c500c260b07011056141c1d500800c0307250841d840812203801003844952030303200380325041c80180b09446000c1424280d85000d4151a58480c51400300341d1500c00002041454005491380301ca1120540560600c060512801511080b40d499003d0b44480002a0026114040004210b50380da00e0b15454200448000c8a080145001240110b00d05495010002e401001050b0007540904400114281802100b034102403200c800350f00e9181c1c0c02c140900c1440801030003400d007080b0450469291180f07450449a42c101103510242c00714001007842401e000040d0002c1340300d00c54508091030400070050080c0c0880c081c0f50310b44801a480b21400c0c0d000380d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 92979505 1250 92978255 92978257
    0x110414060702030a0606180506010c03020705150d1503050f0a080306060313080313030f050f030f06031e0705010f03050c0a0f120207030c1104230406110a08041a011a 73
    0x814000f405581e10210191074140a46030598070810040c07448400d001c403044564801d26801140c03d01e040c030580d407001d4038025540d90240c050f2038440c403c5101d0070386084112108880c0341c0100c001082c0300d0303043c00000064549440d0700c01035074140220b10441100420100c7d0305002c150f40486480d0440d00c401040c0b0255400003020581021118440980070a80c1c0704059441842c0c81c036441000c1d40101c0c500140844040403030501441410b11104180843c040180c0c0d5100e240442168007690314000003c0ca040800461141e22000110014031064008101c0c1d0040e0754007a01c0b14540040c803101c085080b220204d400c201c602505001c00e050181c070172880c41403c08a0f41c50030040c03041074000c440741260300508044000c0746c902c0d45510b04110080d221038941001c115010410580001c06145032100c010300d141c81e0403100309001508021030b55015802c2007922040076130300c1e441b0406000d840700074152425180000529140b0340b414465500030b034143c1d41d000c03012242901d08000c104a907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 92980755 1250 92979505 92979517
    0x120201050112060b040605061813021c0b0301060b0a0f08070e010c020d03030b040e0c130203040b0609130b0f07020c0a080c060a090b13031202010506010f050a02011d070911041406 79
    0x80321b9101c410009480d5103410140c43c0f4200400180154104a041008680e03040020840d1301280103012401c4108022600006c1c0c0405020340812242038203030000340181190f801c485c424600c0801c00c02c0c00306900c00e0603001003910940303c02c1150345402100340c07110382850341d40c6400102c002a940c0014142540e61800e80d905c01d09001c51403100040c0001c0580342064240c0c940307a0f00581c42c007410b034608560030380c8440000c00030071850350030251a1801244d1001308064001c0405002140c24003041800144255030403069007402ca08100c499074280341000d6420708010b200303041d0b0151251034204101001c44400e04000c1600141c01d1080c069180c00401500c0244450340c8000100811100001d111140304400242c03001030035032820506a9501e07407034482c1160314040802910744d0301310302e044280e2010750508a440f65130000c002c07070260800280312a0318a0368a41e1559402c00005041e20586a0508086c402c05010300b2500380c1502841c4540031b4429124801001281000001426 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 92982005 1250 92980755 92980759
    0x20703020f040903020f0a0303020d06050901050a03060225030843120905030301090507050c07050d02060c1603020108070302130b0f0f0c0309130608060f060625120201050112060b 79
    0x8200711b10300d0701c00e03080040a0342d0907004a900042d240e040001240310303403c0504421250340005504140100e038030004980401040301d540040c0c5070104103011083c40c400380c00080314001c00351034036180080058409450348030000702505000d110300702d0b04c450708802803aa00e280440e0800c1c5500f02c4813012000c00340044040c000004001040648035000d20b500300b500440c01159a5490300003c1000c8800080040b404c001c401d02840741c01036000301d4000e04840701101e0990400000d400055101c2c0301c2c03958001000c5c0300f1211601c2c40d0340c68044664080700c1c000d0300c94100950300e540c002d905a2007a26071482e0300c01c811800034424419840c02030248882d00c20440c5040c040d03d0310b01c000d01c3d83e00c2030030400720075440841c0d005070314580044100c0d00310b80c05060a01c401440c000324a655000081c08010b07551100400140072a100c690175200310300c000400c11400d00103201808000030140180954420001d0541c158807180140642c60407644030740905081d22605884141c0140303501010b4507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 92983255 1250 92982005 92982013
    0x7090204080a030e04240e09010506030d140409021909151205040f0501141f0b070f0f1203020705300a090b0324030d020c0f0f060f090a06020703020f04090302 70
    0xa040d00c5903541e0064451200c0340da902c2030b21402c07c240d042a4860082003503003503038100401c009503902c011074105d19803e4142407450400d40548400841e6028581002c5803080c4082000e0a8440d03450b0b00c2210004419141c0b1109103803144820500c0110700c1c0000b03004981e031328070400d520400903032040d903105009056500002206545090a4841801040304814405420320210b0440241014039501e1480c0d90102c4042c036107001400203000c2ca11001c0c006400b100c5051040c041c0707003420740214075031050590b00c12451503807002c1c000390041513069449100342c1c40240c1c01040d48011019507040580341d0910344081850301c03488213030320242c0c4903420840400f400080d0a00ca0b0806036008801c4040500004052a0b1110200c0c0a000c00014800e5000c061684030454012038072820380d280642d8201e46582c00c80e00401c03a02c051042800d500540d0000b40000886940d801030b0409180071a034411603156103a800700d0f40c5024901000c0d40c02074801c0244002c1f89401d41c0700c10341d00c5100c0d0041d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 92984505 1250 92983255 92983271
    0x1e030228030807030207080d0c02010c0b060402090406060503011404090816031e08010e0a1506051602090a2a0203030c1c05100501020d0203250f05030301030305090307090204080a030e04 82
    0x500c0941c3c0059000300c015900889083c86284820f02030100100701c140382403108010306030002040030904900c00b230108040d200106000d0b40b500e4040b00c1c50410050000e06c000c6a45480041c129882440f88204059514084242c0361600d80070700d59140b40c124441c24280000c01116110031465050100c0c00c0c07084000b00704039098034802031804044241d441d03003622507141400310b00c4000e070002e22101c510b0b460500203071091721503520400d007034800034500140c445482458484000382c0001d806980103800c0802c11240d5a180e801c0f00212004290070a00b845110350003440c0000c600e0185040035800c01d00014040d5242200038110035071604090344035540f900c41d041c0d400c8034810354010b542416440070901042d40c04115104080340d06100842c0340404603070042c010007081040f4559a500c0e25a010000d000c0e48036600601030b85c20200340ca0f0b41e0f50750b910b000341195000340304c0740c0d009008a800020b41c1000900c00c0d2021622148080c00c01076110740c3d0300304e907405803240b109540682e580c494 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 92985612 1107 92984505 92984513
    0xd0f0501271101051c05090d0c02090109050a0b122a010e01050913140a0606020d0e01111e030903010e01050402010c24151e03022803 59
    0x1640c00e84882c400b03004840c54810300e40707000c3c1050900034119001c001c1540c0040e000b000ba00c0120340308040b0001c403e841d0108a6203020b980100e03540f0040103801c3c4a0b81103039a1080481000060b0501d20342c0008644a8124805000e04d0303101814141841c010010846003912900c40007080c50054080000c01c0f07000c941c2070244c1008404500750096880310300c3c2c00000d01c2d01420091004130080c0324910300448048070910086410310b940002c2c50b6002040300d040c0f007002550b880c00c0000c1c0440056500da8481d00c2011101c4c4a02502108840e0440d002040c0c105030040155a0b103100d00c030101400d60740d848080c0006a403400d1b05010042c1c0c2c0201810308426841050380c0e401c2200d681421150300110880c0c4c200150420045801c0a101c1c4203002d02a1905150054450390911050001c20961408025000340218100d03400d0310304009480e20b140c810014403900015140da039 = true := by decide +kernel

theorem cover : BRFrame.Cov 92805755 92985612 := by
  have h0 := BRFrame.cov_init 92805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 92805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 92805755 ≤ n) (h2 : n < 92985612) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
