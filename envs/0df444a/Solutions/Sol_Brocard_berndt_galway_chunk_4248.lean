-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:09.081986+00:00
-- url     : https://prove2.me/submissions/b46ea48c-18f9-4119-a0f7-4bfb7122f571

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 763848920 ≤ n < 764028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 763850170 1250 763848920 763848931
    0x1502010c0801050d03051c050603060f090703120314010620031608130e040609031b0f26160210020d051818090a030807180b030604241805 61
    0x1c6400c0c0303a01e080204814003802c0c481c1102084000d2000d0340d08241e000030070030800c01c246600851140b5080050500d4190001d0000c0d0f00d1040070400e0055420f4040f03400001e6036000802d040f0000104e00c8107901030000a400300f900c84089400024040340d02c1448401c4100d00200a40c441d10401820256030740034400c084402a401809054005006a401400200707034910100007881d50350200c5d42107a035403c8900f039a5142d01c7e0070b4050200341e0300000004051602c031291840311601034440c50b154038450701e00201000ba550200b081c0d516000c0e900c0c00442c44074200300079694a021100700310424400d002c22402000846014008103001280e1010310351816500c1034204400904c0c0c0f08900000081d0080c0c0045c54523071440c420701d040349442c501c01c11300e074402092002118a001810440020055010422806245412105446000d0080721352a9010355141e03264040043e0042020346030a5007180c02000c8180b4040c0724562407503003114038840c07c007004100d51060200039140e084030b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 763851420 1250 763850170 763850177
    0x2040b0d020705070308072d0503070f061d0a060501060504080319050715021306081b2a071a0f090103050a110d0f050105030a03022808040f1502010c 66
    0x20320149441d90240254901075000c540c040c42c3d69880d030390010b5004d080250b515411140010140c02001c5d4030340d104240c0800d00c0300020441688425072640503814009005245600c10302040c002d00fa000300302c05010f10f00213100c40028103661140c1e1040904001c0718114103020000544c5c1e40a41c1c00d0380c04031103041000d145400426035407140310195807101d54061000a0041c4408240700c0380d03032a102c2c04240c0d800165104c03044100d01c1060078565101c031040081c2c2900304100e200814800086c00f0702d90804d501d032295a8801d903080d01040061400801364604070080108000000d4480202e5400c2e41504009070030444070454640305010366042c40e420300300400000f6510a034403680d401a10740000040507004070440f88500c0d84600c0d22115204d40740c2151800001d0380380b0902740100000c0700104481c01e0301e82d501079110403024090003100c240c4100c0c080004000060405142c6902c080c0c841d42c0c039502d40001c83c1c03413001c4600912010075006005d0010090051052262240d45a207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 763852670 1250 763851420 763851427
    0x50306070503071115090f070b0d020705030d23160504170c0a03030f111506091003060f050109050c121501140f0c061e0a051e0a0b1302040b 62
    0x10419507240c0d1010780b0301010489044160008101c00b03100402c1780381c880302481500d6040c0001c0d01843d28640b820b1403240c1e50030051040012020351001c0303031243c400360030300035848941606086040d03007e40070b03415000a04240e0083c8071010340f80d0b4406403002d85141c007002c80c0e4a840a5158140002c40b6086010460400060110490030300074a40380c0c006000841741508480c0700491940c013400c0e8000c90110b44403100754002e042d0004071503460600f003840242440c60105074050090341010305054001c03400c6501082c2080102803a03503000e5500200c0034000d007052031241c08001c2c44248254240c0300e160002250315034450f08200e0f5100a2102d01d03103045521070b0802c01c40030080501c400340c18007000740140040c0c1c4c010702c005030031040114009a6250318140c6280c500702000140011442060020318001c0900b52098035a00501c01c070100013411351320170030b5108105490040c0d003281d50300018104482d08d0b5841d004184d03034040645401c0031480c000055141a0301590003605680107050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 763853920 1250 763852670 763852681
    0x4030c0323030703021b040b100f0807050a02100e07051c0b0c090f120f19050d050a05071202070e04060c030b041505040e10021902010507020c0a050409020a090f0605041401050306 79
    0x880078006d625001040021403010303201c002400d08003407c1500d40071801c8403800e00d10464000c6001644541142000d07480d10700f40e428000c2d15801812511900c41d40d441100c3c500c1540c0801a180181078040e00134102c91094141d40600790002410072905141404001020302211b1029200c958502810312124a400c0310100440140b442c020b03204988120411402101000c000c990f00b002c00d12401e210090226041032401d0901c560080c0c402c0c40810041c100aa03a80101140c11560300a0403544070b0f05400308040f801d14000764001070304075001c2c1c000d0005008140d031103010726001c03a89041110b07105c800c0520050325501c1c00d1181d03140200b854100101d040035004000c0c1c0c0c0950f4003c1d5840d040900d28180100e8128004c6400c0183e668030050390303899024820b107500031206000903c08852a01c000602010040c0200c1c3d020b2a290050320003151070303516410001c0c095980c018803030300511041180c0100202c0c071031188900d080980070704030100750001ca41c0c1030700d0b00907000e043c00d0381e00e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 763855170 1250 763853920 763853953
    0x1140109060801050409062009030c120c010804030225051804020108010b0a0201061706040b0c1309020a05090406081614060a030c17070f080f09150c04030c032303070302 75
    0x46020030ba1f8070a4846c0442e50103046410034200c40d49001c2040c01e5110300000050500d811445403102d0700800d07191341c0c04201917100080005d0100c03002d28001140b551145812400e00fa0710645002c0c00001c141d0b91424807140003804002aa60140c1c1c00c440c1c2d41c10280810703282c452055901034003107080c440040c07042803d0030b0001d2140c00c245000120b00d055554085081280110f045800550020410b210421a80c440103540148074007da55080400e200c52040d8400124441c1402c4140d001440748840c50041051364503a56004200704900ea9036000e107070352510420501c581d503554107124042000c1583e80400c25003600e0140600d42080e01d8804203070020710f1285c65000a100031403500c02800e54004026600c200c0041d80e8001014000321009040540068024032442c520360301000072480000440525001401c00d450000341c55440b03040b01284116000074100d5080180044280203441c0e426000488003c42c0d100c0d40503115261994403401020401030050300200118040c1c40705 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 763856420 1250 763855170 763855181
    0x3020f0a1203050a200f09280b12061014030f0103050111070312090618050d033615060f14010f091a16030806011107060c0b091c08011401090608010504 67
    0xf202c401d0246010041c500094034988088000904000300c0360088d00b41550115a01000340006968581000000b690f11460400b0040c47ca50141e0001041040c2c01449030314403100000304504140ea59040c24580100803074804d000648481d801c151a0290300c42280040724041905550742c52090030f00e48250f0300181011071000d403401601c901494009500e000c105010243c824801400c0c4002143c20240c1540d03021846404103003040300e0b1300641c1100500e001c02032860840c1980300b002c2018900060700800d4a40d2507416031b481c00b0008a010184003c0c600240c0c0c004540c0d0900c005110001120307216001da01900c00100c121208200c3d03d0442031744c0141d03001c0040340390782c01c001c00d400d500490709480c200d0030350006100400748221542c1102c03840c4c6030f220250300640100d40c2000d0300500442e24032500148003240d03900c006101c4400c244071035802d007048400382202203810b007500102541c1e403c2c0201c400500344400424000d6010f17400384e0080300c2840d00e17148016841c00c13003048001d12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 763857670 1250 763856420 763856437
    0x10510061b110301050c0a030b0f01050d02131a041d0601020a150b03010c030605041d030405010e0d12020705031005010e0c250309061d0f090403020f0a1203050a20 72
    0x4081042c1800c0c0e5400380141445048403d00d071680720311030082c0c0101075803100440075004940202c000355660341d1000441c0c960440100c2d0142c0c0d1345592519621024516078000702a03080513500f4000317031203e0540284200c4000c200c10145034810101e01110180e82660f1542c0036034400c140c900c0004603100c03200300c110010004001203500c04c4101103401d590349010314100080d07961400340b065180612440b040702d150220329010403606414190394074415405818140050050700c0582c0d9520341031071064440c1d0000c1c2078400d10462041c080e5840d4014001c03c0e1190040c06c403030240c180c400341300c1c2c141200c02d1031808a030380740c0711510740c0310301e55015040c2d4a02000142c2d80910441503a5402c540c0031034820340d80e081800740f401c003004191307030710242c842c80c880b5504484000c61580c07440c00d0a0b80343d03007088854100503201c0d07140c160302e485a0421300c10180d0182941c2d4500703001407003060b110010007940303045c807940d900c0810311070841d100300054420307000764034600e030002d004000302500e082c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 763858920 1250 763857670 763857683
    0xa210b071704050a0308090f25030213050105150c0601050f0a090c02060a1803020604080a0e1f080703020403051507030609140a0b040e03040b030c12090a05010510061b 74
    0x50a4070000c448000484080d505039100381d42c05810198800e0400b544480d459000c0c00e00780d500043c1923a103451050702e116a81241c11401c0c5034044aa100088004642c0106541c031640d61078004600501024420240b155040744000300d9110f9410080720400c01c00e0002420640c0c0c00c04003000003c0710349001c540c0d003005804c00c002c500c0707642500c00d2012000464000388806d00d40a048001900e02c0c007940c59081082c140c0043c400690000740040c0c100303a105101c0e03a2240011942226400004040140d0100898176500c08803c400808120054950f41d1181d00954541c0390540c142e208501c001881948442d08480c80385030108a01c41d0061800e14001c03d84959942c105803eaa00c00c0e698000000d5401050207034001c02403181008404c0161030030300540c59110402526030180e8411800d120740008005010741c0d03103000c1210603c590040ba601002e0a006c01c2540c0c2c1c83c00c08070011a083c2d0301c0c100c0071408910032000c41c0d00441d08281d65240b00c40245140310a103880301d298003100c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 763860170 1250 763858920 763858937
    0xb060909280504030e09010b0a0507060b0f030304150216230d052401080a080f13030203010906050a2306010e06090307030b0402130e0c0f0d0f110a210b07 68
    0x1d42401840d024501039502c0300c0c0c001d00b000c402c110810006903c14102d85000300040d40540b42c0120580301880e800c42c000080408218000c10303074800840d14040d80c180000180410680d000303600c41000305005908031180d0010203440046a10550f02680000c25400140318200060203c050402e21001406641d10100281d407840d180881e080600030202003504048140b82c0a0040b90078010702ca0b402c010f00001403252159010780c81807440d01005060002220750005e27172580465801550b02500811801100b4108400107181c15221940c03124184010f90030008034800c041c401d0450103109000c401c1d1100f000640381e80f200380510942102c000d006c0340f000b0b44c2e41404290000e6010310f1901d031651409104101001c2c855488140d400c03031508000e1210b640c0c2c005071004500c0c409032001d0000d000300c5000915550040d0070000c200c948201030318820446042d80500c22840155190314946403034210501d869003c450003030400b000003201c8880441c20101c21940c024800c1d0900400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 763861420 1250 763860170 763860241
    0xc04050901181511211003080706020a030f0209101803061e0c05180f0a0312090603060902090306060904110603040f03080610050a030c051b01060305010b060909 71
    0x1215082007034103561401d000002404a40c4660194030862451300300c0310b920305481c0c0c0c20300546040e0740e03001c0c511100b078024000a507215280c542e018040e6070024009910345080d480c1c12000f945c001280b000000341440710001d0908804e0081d0340c4180c0006041419042c1c28540c00c6030502442c2c10910941b032980100000031a065114900c180403c504942080003400c80c1644282e4514038171034010000100444880c4640f1003c0c0051103800031504280002007003000140b000c10aa0800390445601c0806191895040b4902100300d40027a281031212076a6064114100d00842c240b280d015080031000070058034103440240e87c028850090400821000404141150002c403002c4410340022960031050503000400395500c04801c0f1641108820348960041150044075240c1c0189911280048070943c001c105480d140d203000e006400c507aa28003065503010300f0151200361055440e1160700b10079418607400701da6442401418032400c83d120b91502054106900d441d205025480304014203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 763862670 1250 763861420 763861451
    0x30f03052502030306310f02070b0108160501020601140114040b0a0804170703050922111c0c0c02100201060e07170601020109020102190309030206030a020307110f0c04050901 77
    0x81801c8203500454aa141000a20481400c0a0307000c6800103a611003d02030140c84515011801a00110208070840b407070700f4100107806440002008417144e0350010821220005107805882d80c1030300900ba040769500d00680c1c03619000e020740810100820050031465004402500c460261414043d141650716051019030f9005442e44c0c40c00100940248000d00504030b4880c1c0380038035151000c1d45405000c1e500500b0794464032a00c0750181006c001000d1050303d5069148400c0501840c06116852540607805110780c05107580410b03021004a4110f00307020144a03c0b6080388182c1c40f1941a410144c0030011540030400c1101d0442d0740311200802c22540c1e042c0890f02a8030191110344005107651102425440000d01d51411a89003040c2140541e0380068000d00c901d80050503e02d00c43c140741400c8960444c15040079400c1a0000140013815000b68011032003103004d65a440c0e00101d080c908141c40d100295500b49490380104107003a600e252562000790000c42ca200009820301c0b41c107000c075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 763863920 1250 763862670 763862731
    0xa051618080d0f0818150402040f050a0f0f02180d081b010f0b030303040b071b06020301080607021629040527060402041818170405040b060403030f0305 67
    0x4000303010743d0071600307025070400d1039180c008560084902403440042d044e00c0d52a810902d1003030004441e1800b14056441c1c540c0103600d00000d100043c00f071850019030400142801901421103603207440400381074000b5910076524423101002d4134980b0007221004001c1000c140680c01e0b5a2404100300e01c01285080740040c0680c00107000010820501e40310700c9500b250000d81045000c0d802c100104000030340442031036a4403500500b0150500d00d000400c1c000100d41e00800105074034400400031030306034000128a4410f4459608846c130000c43c0d034811306499038862003a80300808880c4104070032050500c81100ea0164280032107411325581d040010340035941511114a0302a0703000c44901265040c10f00b55600c110291400c0d8581454203211622441508200714022503461140108080b02c00f020900781f0390300200010b5140c03403210490303c8540e100c0c1c407510380310300c3ca0500d03a843c26081110a64045070381540391004411a080b600390050640105500034558958100020100c0c0c14000c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 763865170 1250 763863920 763863943
    0x4180501061508040b0a05180336150706200d0510080703020d02060c071d0618040b041713080c12030906250f0302060a05161808 57
    0x1c01c866141c8400308800d81e44400e040000c02070403c04000100e005202d44a4200c1c0c5081710000d02941d03603603244111110400fa1242141c00001100d000c003c8030314442c0c49480109400c007280c51a0044030000100c00b0408945800ca802d1035580a4140340c0c0c030000d00400380c01200b02203080d48a540903e000074141d00c81c3e10740710003c0032420554200c0c4602c02c40303500a5014103845040c030b041004440e59814548002803203580624098011521f50741c00352507a83d0b4640c0112000305807122842c3c0360000e500e26001c130780740c585440040e00d540b4002e4200071502e0007499428080c3e407500d4594810240313000300b0655045441f0f104850a5546250003008032100302170510b050282400c440c01c0c202200c2801092040021041c07141c1c0003d404030440344040d40480c3d03141c3c1d0340c00e118030070002c0401c3e0f0440180e40010361504038a0511142d034440c0e5180f50300c03d0f82a1501951290400411075a0035030303034100040c0803e61b220707001038000c100c80303a24848900c00760140c4a0b80d0310f07411403910b1351652070b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 763866420 1250 763865170 763865173
    0x190303080705250b090703051b041425090b0a08060d0c03080c070801060b0924071113050f0406050901060306110a1112070312061d1005040216020906041805 69
    0x10f071281889880c4524a030001c1c108030207058660f245803075040e992034070942001500a01c280c8909410354803a031003841c0804503035181c0440c5140401a0345003442c0c20307200e410481c04030105072810aa200e0014007050b5455401520f04140104c00c0464074048020062500320308160301007004204210101030085108a02080d0386035014480241000c44507406801581c0c1015820301000484a0680b944d40405a4044200001c950341524103000c2003d0a040319100020301c031010303c0354a01c011a00040243c1d02240401407400400044540c200e41c0e980a01c401080030800054003908019041540c0200224050b81c40b80c0707400b8125a80c80c002411840e9000601041454100f40e00c10f092a843c2800741090f0f21600f00d0341009403190603c02000c00074507140031280030386190711007001362040031480c07070990b25070021141107900e060314128201e0340913000014207442d00e8000c0703401c6a0300c40711100030802150b03800c1c01350500c00601000d5110b51200c0003c0f00b1640d80c4034504814601400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 763867670 1250 763866420 763866487
    0x190204060503030d0c0905030d08011a1303050c100e060a14220305070503010605150d141305070503030910110a060908030109060e060108130302070312050a080105190303080705 78
    0x17880070304803120a40c04640681c1241c140c440e20150044289411192400603c10500d038010700d07a40001d2003951400202d808100d4408000d00200060340f01ca00c00c1c2c10b0341c0c07803a0303100b89003202036070181d2300340386041c4d4041000c011000ba814400d0750069000f03002d4607000c50905120b0400c5102800c07144030080341d0314483c03200400c00d00c041006030078014001a002040414207000129050f01c02401e0800c1c0751050009a080200c9401d901c402142684129505043d040650500c000380e12907500a590720700c0740210104003407401004032511244014501c01110082c3c10098400f091307840b180d072216020b50102d400101d80f242c090904c030b042c81240c1844e030320740c10030716180e007219150b410201d19510ba00d010060b00340d03080801c3d80e07001a490113030400f07100b02a103422461f01d07003d0381005151480c104550b0001c0b80c1c000c0f002c1c1c58012141e03120300c4160ba8032071080c4107002c8644458040d4031a41c070042007002c24090b2440d55005681840e06070305c0e280701c005200140c041100c400c0d903140501103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 763868920 1250 763867670 763867691
    0xc0a0c0804150320030f1906060e04150f0513060801021b06090a0201080a1815062306071205040b0f0301090b040b0a0302093c0c0c190204060503030d 66
    0x140300340780f607030b42089075043d003005541322440c15607000c01068a18004020f00206038000402401c0c4056500c0400003408641e407151402006140c2c41c1c1e00c000d00690500160007980f1411074910400e455540e0709d444040d41c034020400602c13001c1920314480e40d95541c14041080f010a00007044815521104103000d443c040200c0c0e454040c00801c03820481c1c10642a62005030f13400100c40d60030032910b050128400c40c4c1200104416468100010641034030050030600b60002600008121203130400344c41421050303600e124006040c90f50206601403810000c0400103a002c0b000f02598518501e0050b0410351501e04040c125031050402c401c12140120041154480b01d020f0a16081b105840c14002c003034010010548000c224080240304240034000505444120340b0700080f400c86441480702e075480283d0a40c2d090384808034007500d114030188000303058a001801124840612400102111180c040c005910740c44c0f0700390101e0780140c64440002d6941c0e010800740c00890011030000032103104c1c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 763870170 1250 763868920 763868927
    0x306090c080d110c0d1e0c05040506060a0522050a1d1003050c12120706021305100c1101171503010c18060e040603080703080106080a02040e0c0a0c080415 68
    0x1203000b5810044003a80c40d8507000d001240120482c0e20540f405618a5402d251180700341402d84415042c440c0740704008020b20031007440c600308a94003900c3c200f0090b1211000d10101d449900070305000b0a81c01c020000807104400c048e244014540f100c041080381e03e44d400640c4c410502ea000440301c40c2100b50a1111140130103038960030a417210340c000d031101d00d9962806d440b9009000c0040c811481040c0000180e0390a08c890342c60100009c00c020390396401c500d0b0000c025005074512814400075200003203468182a03683c03040059460b11200030981c0d05980d0406000c4104c000c0c141000b40d03903c02d01c0620701c2c61041c601d00500c0d503025110100c000450505003100ca500000c142008022080702c0c40c44140001c0d1f4205603040b03880c181c2008196940801c010380303810351005044640c0010340c6001e066004079401e0507a09581d507401d0703064891182c0340090303004c1c0b409035180000d1010085007101102a0007042c4100650424815440c41522403103c01c1c0c00641c040c5d0a00b07a0120900050300e07a2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 763871420 1250 763870170 763870183
    0x9050c0d060f0e040807051e0f0f011104180e0a0c05040c0c260c15191a0105030430020c01020f1509030d0c030f060819020f010302040306090c08 64
    0x250140c102c401d103151031003d00f00714101503c042c007602000100341c401d0040c180100d001408680c500c00707481721503840304180d07586640b0045038511b000b988010300300710030107004104045c00f25440785420a400c01030f100c0f4202d103951030040000c03540d07460114554a401c5c40b81414107401491507080303452402040c0410385491607254002c0142818051001880e13500995207801c51420405803c1c04c2c2c0145514458403605404030024410b6040108610700c141b20803d00c94000125400b03254020b1050070303029a1040c0d03020503a64401e0101e560340552082014603809400b41900024092180001c284c65410307603903003503034041031300109500c40580400441a07244800c1c80107210514081c54003940b2081c07107080070364014030610045040120304006903480c458a1000810082c004404060014256100389481ca00c0c280180024200b102040c0c0009505003082054003031106642009a500190030304076060540c00d001c0480070421910420404074807403070362030302c1c0c0e01c3c14005c4440ca0000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 763872670 1250 763871420 763871429
    0x306060e01091803080c0c0703050a0609060c020703051005060f060c0d02011d062a03100e060f010206280207082503090b1c050a020319021305090a0609050c0d06 71
    0x10358081e5000020750f00c405d40075400343d42513000f140c40305c605121b65428581240c1c0301130480d108004088080c411390b44d00c040c4000c0d01ca09801c00044440850903604c2d042c2501c4040d20780d4010b102c00c028a000d858020b9035000304024000030f03449803a10001203482d040440c080d40d4a60181d503803208900e0f02445070304846801010803247c02c50520450340d41e01d040007040503410ba010002c03220b0101030200c00310005c070f00940b60040e031a458020440c007250030052151014224214000c1105400c1c07a0011000520040e80686480e680396001c050641c600514142510080e620101040c0d1425101410746e0301d1003500c0060750307240c00350f40c500101e1711142d0909240e00400b00c0031100080d00326488004039100c140c000781e25940c0072450400301220140880f8501ca090a08022005003194000c40c4135441c503912211204c1ca60035280400c034052581c4000c00049009428011071501000389d43c2e03c541c40940201d100c9031110080002d030380f41551000b4071124041040c180441442c0101c1d0041c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 763873920 1250 763872670 763872701
    0x1d1b09060f120c0f09041d0a050604051504120f1107181109400b10020d02030a05091c060b09011203080a1107050f160e060306010308090a0306060e0109 67
    0x180a84126156840703182c0d04644200d688a4402c1d40038218000910781f068040d41c1a60f102e01042d05015481c0c22040360100c03003d00683c210101712502d141c0d64540a15004608c0c042c2c40e851000054034a0642142c40400b402020036003001c440b00c00b0088400503003410105244000c08031a0f0741c405640c1c4650020710316030070034001c1020315114015080e1030101c0704000d9152111211412007222402c461501c001003042014011407158280c0000d06d460b40c098407486401d48145d8012a11491701c0443d080040c6c10400141c003815200e0703000740a009100a04c0b6102e040e0301055241d150300000e00f0201e903040c1d100c240c10100e80c41d103140414010084450500d000141c00c0d0780060180740000c00e0b520350305903151000300b0003610f0701080d941803a900508480c20201400070003581c07070411110355000040d8040002c511525442e41c510300a0318098010071842c3d00716540c0a226801030412160000c40c00c5034000041046070085200600401d452480c1550422107510f0668800307102d682e028 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 763875170 1250 763873920 763873927
    0x10609060f051903050426071415010e06010e031b10020304150f110a0b0406050903070b010e04030c0b010608010504060e1515130902030604061d1b09060f120c 70
    0x7140c00ba5003440360410102d113070001e0103aa461402224510495100c254501a020039130818a1405002011400d00511424009000e2405146da03030381007440002c2e040d000100c004215001d41180415040401410301c18107041c40280801e2400c462a0048001c0d00e004110817044d0f8145148182003daa5a02c09580303050f04021803c00150408401c0c4802c0080c5020250f040c6481440340c003a02000314429614002c62034200200c00e1a0141d4007a61042d24020100b030002000000310780d403141c2e07c80e5004100760303c0e00c20b1503401c03450010019024009048400000105614a11070180a1a444240555040c0414001100c0f0359801040e00c10414409121010380c1c8a050074280810483d0032540c0320414245004050041158580c05800080000325040403507030069803207034800f03a504009980c0d03143c1c0b5441c044903e1000c030310112207030340c4007181410b04000d40d51040111100380380e031314203500113011441c42d80c888210803042d48001700b5040c00c0404110307010791300b0200781c5154500303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 763876420 1250 763875170 763875187
    0xc0b310210080f160917030901021b03072d060c0c050d0816030315090b1203030f0c0d06030b0c030711210a0c06052d01030b16020a0b010609060f05 65
    0xd8010b009009081c0d180c00340d13188005068803c5c400503020b08000f0708007040e912401c40100d5540d40103001210301601948408d203114460032607028108100050041042e1403501032500c90740004031604800d00c4448000ca01080c0400503a035000904041c0d035001c80e0280b540c18544044515074000724414001c0780e000c600031500710b405803010710f02c014001d0340c0001f00c50320381540205500300c111111829589000a000001d55020340c10103081a82c0700303151643c0e00c0403210f8072440100c0b0701584940c44000426030403035452004d010f0303100b142c40c40021002d8581d00d9a07418142c084846003c0070381c00104001038a41d1040c002002c500d503800040280c0003070100ac1c14201e594040540041c03800110f80c0d40c000d284030349984000719070019010405401c000c103480b085000700d94100b11080c0e240c120102c401001368544c0504803500a00c0c0c10740c80d512201c41c145099202c80a17030008500c1810030500c007140721100c24500801198445048007450f040c8094101c00c5181d150400b804418402d004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 763877670 1250 763876420 763876441
    0x906040210030b0f03010615030e160614040f030819081006050a02241510020307060203040c0312120e210309070b04060f0206160c0b31021008 63
    0x191884482e007408144000d03d0404580c0085201a84680c03560a0490001d4a00b4101c01c0642100505d40e80500803915051809591a00307959030038941204240300411032588500021a0004c0e0f0314210546090b540701ca000000b0612074006962066001641c0d00d205260090180d90030619402d104c146454026141e482d000c0381840b402041c482e000541010145c4203000d5120721040c1d04416030700808510300403809061b002c8a03800191071031108045001c0c6004904030002401d15401145402c90070381c0c40d5400b9410107441250318a4a9520110000341c20303503c52142840b05030344d800034203103142c04030005441e000c81200c2015000a22a428600d424041840303500105407440707076a80d140e502425107002c40fa40c1c4000c40d0200040360108005a00200c1840384d1a4550308a03840d5842c2c841d881030542e00301115102c003081d4607181d00800aa510140d0590200e900b603050300002d46046420903491003c6003004007490312980e81101149800b00d841d81c580c2c1c280d03240910b054580040c159 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 763878920 1250 763877670 763877689
    0x3130905130f02010e1306080a12080f130302071205030307090b1804180210050d0f050708041b05211009030c0f050a021903051915020d0b2709060402 66
    0x44d04000c070111303c0c0e10352521040e0103c2030031403a18604004090342d0f0b15015460b0a45104120b41b01002d4102480310540b10302c81c1c6c1c600454003c00c5020503521124034a5001ca4a050000c80550242d01c03000110b00000c00390518841d8060000340d5641c0c545444000e15000d011382061000000034880a80042d00d2092203501d0030000745c8000031428044138801c0749650b00c009000390311201c40c1c00d4046042d540040a880c1e0303102c3e1000103001807080078001d0400e6482c1161500c001988040008012913844010241d04006820508050717507101c0e400b1448140304180803015051002c9002d2204404c100082202d66013000c03801c100d082c07a20b40d001040082000000ba001c1f1403509409420720005006008107607034010038251583c040200380200845e0f070b910061381c080c0250b000740740502c0b0b1814600300071264070628481c0c10b2001401300900035007000ca400d01c0d1a82d901e12500d041c0f83c46009112509900c10780c0340306201140c0c001030701c2c80310700010002c152a4021100307010040e260460302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 763880170 1250 763878920 763878923
    0x81b0114010909080d050408190503070c03080c12090c01090e0906011e08030331170d0b0406080307050705010f050d0c0c12080414030703050d180503130905130f 71
    0x4200360f48076003801251800b07414091040b4500c0e200912080180d400c000b44004514074210348c8000c4120101171304c20b07000440b410b40115184d1107140002138424948950b102d50180c400c40e040c545400d040c0d00d081182121407a88a900c1251311841c1580c00c00403110040805813205a46440d0aa040c1515034030188200c01c202c03200c1281841d1000014810040940300d00b00c1101c1d101d02c1e04a4003100c408150296480070404140000080c0901c4108041c801c190024000c0340b20b2859110310000a0380303c0c030003051403181c0d02e0085102c0c0d0303520360041c2c000034100c003001182c075242103003402c0b400d200d4a40d01c40e03410f01c0b40c80360f008405980c01030241c03001d01007440000200c5450401050300c1c48400400d004146c01010345d09070720015004a4654055400351402c0b010203032007a00c01c0c0f9920311032413401030080740051041210b569510303000840540c110035022210b850b265a00e10345580c00002110840300b144500038403000c2c007144102503100041e800c04d42d0011006446981086c1d0401a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 763881420 1250 763880170 763880189
    0xd1d0a080f09061207050423030a020111013210050a030609051c0c050d0f0e0f0a03021816020c0a09020c0a0b1f150915110a081b011401 60
    0x803400c071143d89010540d1610f610036901e0307000764030707202e60000e000f075205010340e0324030318503007071192411991074040c03d58010800340042000c0c02d4580c005413125038110391481c4003503496111500803441c1e0300850040411410384058190b2444038000505098002c02041c0c4140c96840100030790360ba0340b05c1c1001225084540000d001e8040c0c1020340c1014030001c2c406071650b62909072821425070244a040003103004006903500e0480c42a021514448100302500000d00c0c02d001d011128502450444081100109544240e03983c03a404a65104628465502541c00c0e0401b0805260022030804504c01d0f054806015440040c400041084d0070320b0040b091107079400300701c1c100041002c105007240290040c904260341e00e841c950900d01640e610003015204040c070702001808007500801c130700309040192182c0800307606000401854a01107464070302000300d01c0c928104000403c3c82413200d030318003450484d40c1c0c4112a1480314075114407191031060342e078546248100c1004070b10100905682d10b044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 763882670 1250 763881420 763881427
    0x6141804020d15020c1207060e060603031b0109020901090213060207060203120c090909071701090f0b0402180903091002061303051b031204031704110603070c0501020d1d0a080f 78
    0x6106000900407030002e0011441610340c94031b200001c0d813000e4010a442048140141009608000c0d00e0b490182d503603640562043c0302c200c07052010f2010030446030406c0d100010300f0b1140d0b600000c012900a034000340070b09a0019941e080d5440d2101c07001e01812860004040043c030b025070095503403080703c503808000104080450950a100003c807080d0700c5009081058909003582190b0302c42c48a03110b826214840ba402c02021a001030041c250519040b1181201e0f940c0991504060703400300400c101e92254003060500b4a00040710001c1e4000c80454004645521082003440a000162a200c400307551000040050200036038040d56280da60610f860790300c0f41990303500c0282e4220300d41da0302619030001040c20102c038005c04402503c01d50280c1d6814a0203c14601081200c99040d00d000e012656064624015810000000e40e0429010300c0d204580c0c181a889080c01ca820401c0e0403807599440d41a80b440340340b61b15450071300004810024002400242ea0b03004914415401d01e42c40b1528040b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 763883920 1250 763882670 763882703
    0x60d0c0608062d01120b09130204110d06080c040908190e030a03030f0f36150509070e09030405091b030403120c030615200106141804020d 61
    0x80c18101000e0f0340790402c0303890803507026070000819040c50103003400074016004a0f98009100c2c0a42c0c0740325200903000d450301c0d45030b00718418000d4072030110581e00691a0b0880400c411346000060507200186000007401e6410001e00038280342011200303920590800d46028003244c5c0034411038030400fa0b43c10550070a03241541c415911003000030b80c1550b240c01090642e4043c0364042c0c12100b28218601c608000c002c914021540441c3c040d01404030307003041a148154050060304203402400d400e02c0e402203003104502e41d54250b250040e050b146152513202e4040c00043c0004019100142c0f80b00e00d070904081c40e01e5280e441c0d403402030344a200e00c100000c02c0461034502d000d0410782070861440500c5d5641c0d26160402406a14407400c41184151800307103580c0c1e445105c1d101c0e14043c0d4001c98040c450007400e088044456a558004150400c20255400301d24036509100340c8008085050064140d8200c1c90104420074940038a1043c1d072008440810005994170209442d40c41d80c451135481004e04407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 763885170 1250 763883920 763883929
    0x80a0f1106070f03090f02040f1a1e010c15050442110715020c070e061e011101090605011404020309030a050c0f060f04230d1101110f030f060d0c060806 67
    0x1c406c010303400c41d19020704800c0006241d0072564207a0201c0d0054070000d4203440c1481341000f40070743e5201403400418400680c0e50310a42815240c0d40c01042c101d5100002d0900311000c44000352012241e800c400c000900c40c0c02c6a0f002c0121200c2c40388a0740e075a2075000d00c10b42145200507a04000c5549607500350401d00f28808005542c40c00d500440e08036948922060020000d50180c0f141d4080c030710804030000340000340d860f00d4038403905000e0100021b1240010101d90300f02c4c0e04900440c18080003102d0411101400d128548a040c0904d00101d51540f41000c90360103400100c41c800d0040e4010000c010400d038000003222208079880c50116514568170340104e040c40b02c1d03228000e0484c0034010a1111a203243d00849008a0007603280c8404a50303030041981c00700454045840b4540c0080154200981c00341c1103a00d2403c150000124602c507000c00030f0601580040e8102c4a01c0b6800b00900c803152411078110b69101c01c045e10b0b81d00a03c402c0791190204000188208800c004107040081d81607140c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 763886420 1250 763885170 763885193
    0xf01260705060a1205100e010806010b09061305121b0118050d0807080c0609010b0f0d11030309060c06010e060109030c0b07150507200610140d080a0f1106070f0309 72
    0x80b42c1820170250070194058144a02c1038803900d041044d9a074000b18505070f01040043c1203800a5200c00c1c5410001024040c0940007041c1d12084158030701800601600c81c1102450804000030240400750381001551305101070014125041001d03000038100d0b00e40d400321408003610700403a00b40141107040e2034101d619103e1014000c05180303000c22103940600300018101d010f905000000e1000c070005c0d1051003c040c2c02424020760120b0450300060200b400400006210040a016249890444c0300401c25a42c081684030741c644c2d0280e001008500740e0f00c4481e1b83c124509190184400d451500d590110a803a030041c1040500700080d58000c0142480028803030810b6030341c05000525042030090550006002140700c00b080b9258944240040800c01b14460b16407010b09986480c18031140c018240d0b11103012503040020101560301080c5107001074070030307034045a460180c608104800140244404441d06007998003040500c4209070308441700c11404842c46ca4005030200715820407084102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 763887670 1250 763886420 763886447
    0x602190602090409120908010903050405060a03060e090a350c01061206052d18010b0a080d0908010204060f260406050a061e0302060f040e0f01260705060a 68
    0x28134281d000420070400d0454045900b030507803100c080c096641e208079409c0e034804142c000c0002d40c01304424402c81c030b000409443c40102ca4a40000c00f292100802980c074181920840366a90080c8541030402038040c10220b210401c12480005003541044210030041c000f2600340385450001c40c07034000d1000d00350f111500030000c0c074078408551102420103000421055a911a42c4440710003441d150302c024100c14403d1003101c10074103c4503900d44140f0303039a128880303107518059503c40b15052030a070780f003e802c0c80c083c1c241600a05091b503418000a0a440101d61024205900520080000640000849d00c450865062901e40308003003085a20944084081000c03101004c48180b009011855105501c40e4814000400a03d91580342da075816803080b100c50b0301c15510012050005040000281074a100102000d9050030389905c080003084008480f105261401c40c00100001e851f001e000c0304a801010b80c4500a9908404031141c0340e100b20300525004900018801c0d010b584188200080e00d0f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 763888920 1250 763887670 763887679
    0xd0c020f070f0f0b090a030b130c14030f0d0c1b0909060f050709081209010e06030711060c0306011e02160b0d0b0328020a09050c0c0115060219060209 66
    0xc50b212400da80d00200a800b60b649071581d810301c0841e80c0135014003160500c040040a0154403031860780c40e6840f031200100b409030400c940c1022000025042c009030301c083c03d039030b15550258a000005252401c0000ca15440300d40d4000520076200c2034001d0344442034246c000e552142d07103008090f0044203190140c0d100f020510b14008a00041c014150710941444020040a016944074078000711084500c0b40070300130041d00040c03071031f001440c8a40000c00c2000b0040c100246262213000000da901d420031525080441e882c0c403244003640509116041c0d200c3d9000d42d0342800c5090240001713110708440b004541004a82d0089103100034002c00c8018100d01c03481642c0003130652502c080c0c41841d005181015000307400d04054018600c0d010230b840740317800302c0c40340c00c0ba010aa104904069070300308014127980054100f01c0c00300720504103009031071140d1411a90140c0d2800c02042450031680001541521100150300600400d940421100a68030810007401c000f200e050410200030f204c2c822036190b10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 763890170 1250 763888920 763888933
    0x4082d0f0d201204210c050c03030f040b0d060512150109051311130e0c12010207030e010c0303202a07060c0218150a080c09060d1505070908070504060b0d0c020f 71
    0x1251b80c80350b030400c0914806c1e02900d40100c150028991b0728040d090400b00105424881401034080712009403082c400025008900190b840c0040352201c00341c04201d241d540c120300c03400c01d08510280b2040c0d00408240d41e041044e0b1900303400c0540301401c2100020040381d040710500e0520f6035040403040d03502c2c08400b4200914544002c0043e80c1e40c0005c0611401080340c0f003004140d0041c18400d880d40c1c9034140d291415801d81d8030004607120a004441201070607952802c0180310801c809400d031916101c2c0210755507621850b400001c1c00d02e0352072140a08811810303004d4041404c0407508008456081c00c001544110030f10010b80b58649030011500c81e840500108244030160403a2884201c80c141da10040c0306454441290b12811200c10080e0000315650215401e401c181c21310180c500e0081150002c4a1201136815098480950b08540091141c4005006000041c051341d0000d0038200c404001c4917150a0380c102d081e01421280d5600c0b19560030b0704151513402400310030192800a420f4548 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 763891420 1250 763890170 763890233
    0x14090913062f03060f0418080414090903090a030201030b041103040503041401090e0402240c0105010317070203061f080a1401050a0504082d0f0d201204 67
    0x31034204005100740042e54520710a2440164000c07280107002c0603100310785160502017404040c00480c03541d04040007090084c440030801e0040034001070f140d04003e01030000046010050180d601402c0c0c0300442d04200f002408580d80c806d02201101c0e42800c020030020348a4000074020700b520448408031050000410040241c00300003041541e601d40444031202d00403000468840380079008201d50840e0305800b09000d45408050343c0039442d80d03101c244c0d00c00c00309041d54040540008024401741e83d12480107004001c12000d0f009166030782002030505244641d00029038810700681407001c0c128003520f1441d82018403410f4500036005180488810f0299413400d46044200147d150500703510388400f04010041d240101401960801e00c0e56042c0072808a5405407004c0e059200c01104603101140c0301c2c142444d0b400782072805110700034240c030b0b029001b604a0540d01c8640750314102c441d6801d5860a54890201580c00c50b055100303210708943e54624100041d02001c540602419420100820 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763892670 1250 763891420 763891451
    0x1103180105090a031a071b1401152303031905071a07050a120911100e0306150306090f28080d0525050d0e0a0206040806010608071409091306 62
    0x9036212000680ba0206da0703d159084400a01689201c07031030031110a03518020031050200340c0320301103445000280100c1d41a0401c892480242d0207004003c18a185d40100c11440c00411036020300160042c42c5041d403015040241031500304005001c1c8400440c50f0300c02d000d110f0941c1c44d00003046e1103007e80942803e00004d406900070285001c005218001914407000d441d00500511950182c903c440040010f410041c0303c94418290b00100000d415040c010b0b0303907080000900402a0743c11040c114a0007005060800c0c00040c03c0c405664810051100300c01c80000303101001c900011054625200c4103801c0d650f03c914001c4003e012060007081c51458007003582d0015014403000c80003071640c8803401030f007002c11002004d40700020a101780b00c00360540c20320b81c0201104500b020242c90340c24945a00152075508a6000070b00075078040d00042c00640e400040f002d80100352810140303410621a25003080b81d00c5040c858038003c14042c001305140c070807c4035000d90402e42c0401c050000b100f0104419 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 763893920 1250 763892670 763892693
    0x230c0d0605090d05041d07030209030115150e15070c09020325020f0d110304030501020408100b01170a09150f2412020f06040e0c030106020d1103180105090a03 70
    0x1200310f400340d040344086290043c1d0031182100d039000d003d03c1c1c1c07034086810f24405e07040000381500c05058003005034070380c1507500b07200d40002900781c02c540000301400c1021b006500d1810b68420b1003400400c0c65296031b00c7d650704101071880485020342d1555807103189400da030080d5403580003003201400441400b18481987c0307151095006a801c403016100718055080340d680c07110900014907504580070485415100741100c03e540c0038982c084a240581c0c960790725007240e016074052449900100041c85914806000b001400403003481d22403d030290544003000e200307002806418030103580e007c1403400c1002080316000d00900007007040002000100d24a4081c02546450b2071111025484203422040315240c640140d5140882d00c200c809469800e004501c07100744942d5a002e0000d12002070103040607960380d48246481011681c1b203501d051006840c109160301040c06005c40c81c1c003984694040081551103041410451040c0d541c005030060f00c803403207a2440c182e0440031580c0c0100034001c3c4000035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 763895170 1250 763893920 763893931
    0xb060f03060f04450308130203030c0d0201090b1510080a090b040f0311030a21020c0a0c08150112030309030908060106090e01050405090a0b150603040606180504230c0d0605 76
    0x1c00c401030104e07004611a0808000401242191000c11200ca803800b8240c50305600c0070382140e14142460400c0391808051580c1d2000503911401080100440d4803441d9412645007000d84090405190002d00c40700b050071060401c004030b240000d4860075168100701080c3e5002104c0c15003606050402d01d4412060030415070104800d140c814411880001c1103852650f01aa5406a022103000444001c2c10341d03d140710030200d4082c05255001842481244d9005200300980d402540c0b52896003400e1064046a01d4030b0b80302e1400042040c15004400c0a081d254945030008100000c2d20381500c19400c6034100c0c4030b8600c503640c0003164054214051038181c2c0c200f0150080e06c2e030b90b141c08120648000b1160510542c110199080014462440454001340c101c001808000310300ca021a6250308200c1d030641e01c5a03140c0074200440613130001d1601d445c400b0784400340450324080c1c440c420020403001c850744189004490504406505219a00c1c000c0c80003084081040b07101d042100250001341c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 763896420 1250 763895170 763895261
    0x2b03090b130b06090405061f09020d09050f0c060307030908270a0909020609040507090b07080706060909111002031c02030a110c0d030518010f050a0b060f03060f04 72
    0x30504503d00007001d41c0c891603100001f440c0d10740d210660320030414600103078201e8021036904003041010781400640841707452030707a00040100850400350300e000c585440c0c160b1660402051080184c80303503811607174441d8850402080b94412131400c010184030310540c8102c920005102d81c540c204202c0c4e8803c031034810454190710f100d520381c41740608555406c400258415410401189035003042d03000341e980120b00b401e01c990110b41d1440342d100668000b41e81192190300010b41082000064440c4002402c0c00050400c42107400341d41d00302080c420421020320500b100200342601c94030070400c030b41c0024103032854041d030429881c8004000c0d420036034118403128100060203c0005004040c0d82c24400d03020001c02d52101c000304164020304000e0a810702016100c2002c120b610000d018010010742e2071000000c039850204090707421075004000300c5109075400c010600058044c0c40c183d030b0300800110b549200d406c1e48200014008d011401100e000307215168620030074030700888070111000c100c540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 763897670 1250 763896420 763896443
    0xc070804061409040c210c1e020a230714060d0f0605031e01141603230403053406020c0717030d0515011e020a05100e0c032b03090b13 59
    0x84203000787c8182c020003034001840c64803062081c50303070581901005401801036540c0195980c4441c09100d00404c0916800c91205004071624a0100000001003500e080e1000f065802c02000404a1048802a003070f100d440341c0c880140030603036503c001c00910004046889080100030000180ca11011102c0655440c2107840700c185122203040b207101c2d44142141159039140200300350002c2c080c20050003420100c0c1c05251a00209088030603002d04c0c06511100e444007003021108a01840c001e070410344492407580b403001040d0100b00e51241d825800880135860342078500a0605e0042140d200342c0308560140717180c1907901070201c02001c5031a50f05d00140103a40d070307003402c2c0081e41c0c4142c401c1900003500706401035451058044a40b541d10700c1303841a100c109a0944441e03203400c09a12103880076503030391212562031003010404240b00704426805000e03052102c895415540c1c003202c0514bd001e00d0042034401e1268803907481000c109c0e0f405100443c9a0800d080f2407130365001f003080112040840b49 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 763898920 1250 763897670 763897727
    0xc010606140403020108012102130b0f10050f2b0b03060901110706230a06060e01020a120302090310090804030218150f270f0c070804061409040c 64
    0x1040b10241c94040e1640f1400c4e0b440d248240007a84400c22410700c1d070052072113080700107a50b101c08081080d0071080d004aa44412b44042220012414180b184107034113283c00801420b4102c000e44100c01031600c81641c0300c407401003107602002d441400e50411829001c0c07403203030305860550088002e03020650031241956900c0b05410300329240c1103160782c903881d414800140000d515410882c0702703045000100d60020380124940100d90016104c80407859240c120030f0045039481401014108801d2000701000311640d182e03614009448141c110030542c0000320392420303840802c800c5401000c0820100510002414455900c0d001070208030b04c912510f04580c0140242c00388103900070b43c1484606201e1003048410400e500ea001800b59411448046849a5481991071000185d000040d89001a0b25040d910107015090083c40b080d020070f401d01c04a40400e20040517602a10f0b91070408040d818400c0d4a0074843c2e0003610281a441801c00c2a008101e9600c2070104031001c844403602000b600d800c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 763900170 1250 763898920 763898957
    0x20307050f0304360c050408011a03121c0c0315031b09050124141c0b150a0809030702090114190b0a0804150914160302011704060e030c010606 63
    0x13000f203510742419022950400b01c5550340300a050302800d0a043e4a025515842d142c256032038002900036058440054080c18102441001d00100c3d9040e2511300d0140811024441c0c0d000da04449007071300d585c03007490881e5240284c0c4100ca49500048a6014442d41e80c07610700070030b41c0421500282c840c0300c20000900900d0358020f003410303105101807544c202014910401002d000a400311404c110518101a8290907102c008001b4860100320f90741a5030f00040012090f20304000065000350310044203141c0511502080c0c51030700c0460b00d0456a03030b0300c13007140b51880d41c01044006944200c628000086040500044400885040e590050806110203070b48140e00c5c2284160003428608200300240b080c40340da07099603c9031080c1000000480a007203044203d403844041251405616094904214801c110004011010661a00080d0300350780c0000d0089591000c5084410321010104007001a40c0e0403003800005240101c03038660841840240c00380540d880342c000800c6049410490300e144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 763901420 1250 763900170 763900229
    0x224091e0f15160c030c080d060e0109241202060a090302100806190305100209040f0207030203040810150905090309190f082103041707060506090f0405070b0901020307050f0304 78
    0x20546c84010a092168031241d8031940108141100c580d600c1e880480c0e44a140c103221406009841c5c40081da0581400310081400c0c40c19142c1a040c4103400000c00c14410710082800380c0d40d81c1601d4950b1940302607281070b101c26905810095000c030821015002c8641d00c00f010b01e1060f28116024070810800803d070150564140c0005011600040092a40907501c2e07002000c0e5400040c00000b0102c600039001c2c0100e820498040b8012380002804000c18281040072070541518144100318010420001150618481c070522440e107842d1000109036080500030340740814009012080050484509042242114028409041da881c2d8020450050014080c50980d00413032a05087e41d808a001a8243c0c00c0184100d0311445030715111071841070900040d0034081d21541010610781003410401c07246000060248180b000e4136000c000104500082102c00c4440002c50301d59141d425000403810351013071f24000b0f001803107a0000c1c048050b00000040045480d109080d828402800302c0f442e10151 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 763902670 1250 763901420 763901423
    0xc020306060907020a0b090601030b0619060c0606090e060601021908090f0a050d05030a02010f09051f020f070308090115050a061803120224091e0f15160c 68
    0x1031003140080c4580c02c00d815116001001401107036441c0403241e4880c2c0052800312030301101a080007004004210707254030f1103500043c0880d1000102041c140703050350521078a1181504000b0360300304a03020b0141550241c1d01034040003105101c603552a00c611076682e001610154014032441d01c43e20192400340719000350983c2d000d040c051900305d040040002441200742c3c121351005110000140f1945c800c05400081071099000e1034542d100414044d00312a408408160341394105500c001c00030320041040100c500300c5080400c1c000380c0790002600240207111050103619070010703441c801c0c550840c2c0102c7c8200c900c1c0e0002d02c040b070f880e1500140021202e01c182030700805045c42c240728140c092030000c0100d003440442c0c04499603498071150798248010b084000941c00440040a00840b03041c3c070f9486030450342d04505850300341071040f25610a030b1038817000f200c4c503100515007882d90f2007440313007184140400702210b81c0e00c1031071041c03042042c0f000e40d02070f6801e101d0604606002070060610400c00ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 763903920 1250 763902670 763902673
    0x3060a0506070204061e0e13030519020c03100605150708040b0c010902030624040c0912173609060d0f06050103080409060905060618150703050d050105010c0203 71
    0x5250205009007908480c030126489074039a83e012070300b078000c8001d0484101038041300051b068903105034210480d01c0901402c0f90301d0160000078002c2504030088903000035000d50304090002d103140d4224203000b406400c0070b0381406110b10300318000f03403a60800c4041d103801f1075000a0828004122910318421940000e0201d001808104182c2c1c4240e070140071076010320000490440300b1384e030010307045c080c0454240206c035040c51940104a02c0d5541508100102034408001c900006036000e040c0d20801d1081948004400481c40c00700300341904d030170140d14080187c1d19104e408591041107034045801000c00001260001404400c2c003140800d0071000b00038000219a032515001e10542c08040d4400743c820241c244040303400144103220340742c000d50066640035106c60a12491100b47c0c2c05541c062039100d810601409010703651a4110781d542d00040d21083c0700842010085607100e04900e01c2b0143c1180d001c13a440c1e0506030401c5c000c1a001c4007003203041040ea0388441c015103c0700d14070710700a50903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 763905170 1250 763903920 763903939
    0xf1b0103061d04020d0f150501060f1d0d0503030c03072312061f02012a0e0d03030e120301140603010308160804050a060c0212010507022a090a0c090602030306 70
    0x44111600002d074026002070f0205005c10100d4580c03030345a030b140401c01c840328103d500f80c200c00c030034842c42528050816441e014500451912000742800100100a81d00e00c512036005210f51341c4048052243c260f012066a844e45810340c090800c0380c02c1207078900c0c082065450301c10300c0c000005000340008070455003071604140c02074140459101e001064507800000841001c1468965044c030b0a4401c50705d030340041400716404486032045403444100081c05054a80c00280c00c540110411140d49416142c0603142c1010b8101240a4603071418400301601998441c0701071896640002c1d8169400280c003024107104820601003544424480601007d006101e024036400100190b000054041c0203494149a280e05c005100702001d54050300c0403407810402c001c01c504201d0383c04051962110000c02035860304c0800a5100c2010060071290038203040012075000807246414402d002c4003a05495503071500381010402040d0314050b000101350348c26000a0160b10000c201c910498000d04203058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 763906420 1250 763905170 763905209
    0xb030610060302030910020c06100e060319021c141c0905010c02010309060c021e010501030f0305031906030b040201080901060f091505090c070b07050406020a1101030e0f1b010306 79
    0x941001d0a05c048600a200280c42c5600310f50020b40070655950000e41080d0500d501d40c2d024042d031030345c040c1c6c0c1000490010401150707000320380301d4801103500302d40c0084001640f0000e100720200c2c2c10030b01160651b044001091145903803040c810301c08e0002c2268141d0040b42442c00c03250090f5900900050044002401154070805c0840101d5106040104203c801e940c1c2d40c905881d88284440010303800340e80c0358482d00c46440c1203c06070a00c40d0000700300650654948003441e001101d806002e004001001c1107600c032800011b00e40b10814044100051500d0b440c1c506000201900c00703034000395044002c1030440307030103214610072a4100090b03144103500d0800c03844083c203000329031311031801b1001c0000521626003e2540c0e1044c480c08118643c0c5803680e00e80002c0505000d81100b0810401380803d01003031f034000400d0750302c140e004441c02c5801c0a1000040f0060301201800c5c0005004015114507001d60001703c0d10742d6508000d0482640020101c011000c8610718440d41030340507605c203910071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 763907670 1250 763906420 763906427
    0x6160b130b15010e040e0c0f0a0f06032406120b0306070c02100c140d1b17030a0e030d090212010e150403031811150a0c020415081e010b03061006 64
    0x986000181032801110b80c42d00d00041c1106d51183c40005c031500b0078802400141303010700b404a8581000c9540c2c007030603070030400f11444001c4d02d8090341046c1035807116034031080c449a103540481181281b45050f0000e0b19044010070190070079200791121400c010710b040381d900c4d001c40c0c41481140203a0341e40b041ca0045030204014101c20404210620580d101c0f840701041c00072410700302c1d07010a01c3c002c05500207440ba004150701070750f40c00d0f071441260791a112070014000740c10741c2c034404030344244850b240e1b1200c1010200800c0000d8000310701c4d1100090001442c0e04582003079042c04d00841d0300110b17520003415464282c850b4001c00541e26001324801409407000c030441d154019002c0d18002a000a000c05107101c1e07000070380402d0760315298041e282180d038070300507504080c083c83ea200c5107410f02d0300c008000b510324000e424000b0710864482264010040c0003500010091412400703e0340440240e07405030503400301d20781306c080081d401d0402071442801e0008440d800784104488401e080c0d454030340c084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 763908920 1250 763907670 763907701
    0x617060a0f0e0102040608010509100315090302071203021f1802010c0602160b010806070f051b0a06020f090301050906040b1f0810020d0e0c030d180506160b130b 71
    0x64000581d41e80641490b10380034406000500322548501940c0d505003c100500810010720701800e016044c282400055002402850188550480450201d0407403505030704207422a0030043d0380b400360f001c810092541c001341c4241c070300399032081c407030340782a070500c011019660034416402c00506030464550055125907001000240500b80060801001e544441417071030620009a41080c40100107100b4444117212083d00000c1358141200ca0780d03821000076119010341c0480c945c1e55000c0303800792208800e0601006614907841102190703907a903003280101c400d07000340c01c5071b60103580b03844000703a0180000203a007401150071400c0a80c031543e602030f10ba40050f01c805001607035003034110340001c2c0f089020001300402e5601e14402684a08144c9141001c17150281e500700c002c0d42c0110407103115510302007410907181e02076150840342c0040d50750500502e448564480b50304100d002840c2102c01c41a04401d00c41584034001c0c07144180c072142c002c1041030082d0750018244841c804042002c255451000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 763910170 1250 763908920 763908941
    0x10309020f0d29180f070b0309010f060603020d060b031b0913020414090a140105060a02280606051905040513021915050a05180406030f080705010617060a 68
    0xb6100c10820602031140c0240a403801c0c0002e0031648000d100100305904013104607041100e00525095070a040031654075080c1c0d02c140150080d000012540d81e00c0290020340d0407180e0840c05010060365504010300940c881403c2c01140c500d010000300707125030508200c074021025861007402c1184081c149403180e41c402c3d80603a60140000b03400003820011800980014500c005085030350201680c144000c0c07043c0200118034075407a0171010100d202c01440014107552082d207000340c0f43c580001c0103902d42410002a000320384009104000402982c660200c2c1107845843c0c10700c15241c0ea0703014080c01c00d40c072270b07580c0000103614002480517040503402154440c845005001c042d14158010485103d0302001e40220000013003810303c03600c01e6480ea20700c1020614945203103048030000d8002d00c0b50082c148000780000c10390070b001104ad0f90315005140615084030052160903140d181400c07860303010040c21102c07542441c000080c100c10024500c81c44c00141000390010756252038141004040c6030b221b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 763911420 1250 763910170 763910183
    0x40903080a110c060705070c0f0315050403111501150206060607030c05150c0c120f121e131a060a05091320150c0d0c080c15060906010309020f0d 64
    0x1a603080918104901400303174016449150b80ca0281c0c0c10b0600941403160410014010005010800540e00d0103c05540000400c0001402d48561030102c810840280910307455104010600303414002600106040380c40c1418070f03d40c1307501601016a140e40e0110780441c0d0090782030100340082400398803414041c42c407035800e840819110b007115640d0301d00213488018040c4008920840c0c400410442514280840404981084210707a00d16903184034400ea034000d00d02c0d90901280c140b14080303c02003c024910300a405d06131508014500c5012681201615510350044603901c0344200f2449242c065800606485c03103850400701441105100030b021030703202c941650110000302d4100c4400d150828030b5030952031048080c3c4400c01c00425045003d4000c11102042680f103100b40005604080210609020f002c0c002a414140304601a50302c2c0407000d402012902e441c120b40d1400010311440017101e4103c3c140d107860004404594442800039000310900b10b80c2145031030b000000c080d55a11511 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 763912670 1250 763911420 763911427
    0x105060f040f060807031518020d09200a09050105010503011203200f0111040e15120d2a0b0403080a0b120c04140f06060a0c021f020c040903080a11 65
    0x20004400402a5806000014950802d004010703605000b03444081f0108152404104e0030180340503c140420380000d40c1e0190f00044400030454160044020079810903501c00c0c03032000c5181c0307184d4042e83c072032001072085081072000315004059110b168160f61040c2d481c01d0460382800c0d00c0b4501000740d244217800b80f000d4040b400f042e01c00c00e42c0d0080441300000c4050312000c0c422901d0380f800e41d05100346090050340144010701c282c9403c11100c0741e01c50b141d0660800c005030084040744048084440d0034840b400303001100d10030f060304440b81c4c520609138000901540241694011032400c41c02030000c00c400018408100424400d048094100524140020302c0c00c5800700015443e544002c41f1101680122001c00607a240512800800c02c1c03202c401d01c078661504846408600f1401050184241d002007000c20320b0b18403481183d559150b014019201501464010b0540e1205010003540103118403a0110141d04040c080d10b454258151202e044a8480c4020507010309819050601000c8050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 763913920 1250 763912670 763912679
    0x31006051b1e010609022b11130305060c040303020a38090106080d020a03050705120d05040212010c050702010804050f011104080606010302040303081303120e030a03050906010e0105060f04 83
    0x51100d92038551440c0c04030503000c482e00b10240e00391600c0da4080d1991520500c01000e690680d240c0e8040c4800c11444001c0759080010310030300013000500c0216070908004030318920514911040c0d181500d0288080f5a0195981c406203034251145000c0140160803a4422800254150280c011904c000842054882c0c110781c010140c100200928160b001004105006101c0401e2058102921007800a8285100724240182d500c1504500003406c2050000c0d4030000c1c0942802813104005400900b10742e02c4a41a9030400038000541e01a032003a04800390b03142c090b07031052182494602154551702d09000075a001503a0150b00203105445600600b8510b0607080d800b88968404400b01164460b120f5080c1110f0501c4c05200801450506104100a20220360003110086d0320080300b1140304242046840c0449140300d20010044a072820b00c1030b448021080030029000c042544d0b03030204855510158820795441e0700781324828084100000610441c10a98001c0079504e0700c10b00c02c50300e01940e8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 763915170 1250 763913920 763913923
    0x18040b0d0204020c0a030909091a0a0b040207081c0501051e04020c06090303010f0b0a02210c0d03051603020306061801050705061003022d04021c02070503040302090903031006051b 79
    0x10b1341003803410f500300408003410550000400c4002c5d1880ca0410419600503985454484d204486240740c1c038516280082c0c92500d481c0c001205040000d070096440f902a441c0011182d0030040c405810341c0d045024210b90b00c56240b180303604035500101001601d00c4099107016064044410b00c42e007007602042003941240301002842c0c014401c501c011a503d61400c4d95010035421550008010a0010030070440740d1540062590b038010517011604c20020b480c2c80383c00320b291181244811450090100c000c6542c1c0d013552005200d034a18481c41584486050000c03000c0348400c440e126400b120034042040d00403d050700070911054181011843c1107000d8880a1400c1d1040300c04c20315050001206004500b0090b80d0245205000718911102c0c2e041c01d10705900300d14840804034081c0b81d01080428441204540c0d80d01d41100e140783c21075980c15141846074403a401400160b005e0805000407a0142d000081260b11860102910000c002e0030a1401c6403142d01c80000c102700c03520f2604025584010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 763916420 1250 763915170 763915177
    0x801140a0f1e021b01112a0d0e18040f1106070201050403080c1f02210405060f070e060a050d180305032805010801290a05010c2306091218040b0d020402 67
    0x310820800d40701c550700c04a030302d066014000c1d0007e00000050b100701c801f450000702c3d406820500d08058150000502c04a0403030158070f040300406512070800e000a010480c440644443c0c09030180420b500000020301240d07214030345009000410401c004c0001c1503968003d007130340300c48902c2a40e2640c1050560402030b4080d14070f450b40714690004681c0001d89855025120f519188480400740c0d00c0c190b2285c03600c4010043c0998440705074a400940710501c19035a103668050014140d64a480042c40001c1c1340360001542600f02c5860003147d4004c0c03c1902080314000396041c0c3e10940307180d0300c1160b0f200041c3d1003a81c15a900c0b4481030640032101c2c0d05409424081e10240000080020151001100704e900200001c82d07a0a440c6e00c034000c00751100e82200c2c064803000e082c4a16803800e40c4c40c01c403112001044925080c0100c01001001c0110041100d0b8010078420044500c51105c4440d020420301ca21400301e401c469903030f030204a840c01c0942050b240c00c0b8008011010700b65164011400380d90 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 763917670 1250 763916420 763916441
    0x150c090d0311060a0501061407021206090a1106070b0106111903030509210a030e12070b040c060f0210180b10050a29070c0801140a0f1e021b01 63
    0x2c181440d45180714000b0099141e010705455028040c41d4580407014101c010403030b481d164003045c001110010f41d1140d41038020b01c1e15500c42200ca0b1494100c41c03e907115081394030200d03800b43d00c1c0c0310140c0c510f24040d8280c4a4040d040600f44601b6464884180c88920124072511035600070040480399010310a507150b64414025107000ca050700e80b90015a0804007407600b102c0024158400c80440d040b1b8001c103903a8030410754100010111310b03454a05161050036a01c050000000185440421006104007030040c1e21650b400e1840c9512040c080c0d515841c0e621412006034804640e4440e90182034011020302c40c4071913140120f01805032105002c0150881ea500d0300141a0340b020409803d21480401c01400407012030180d24982d00d1510890003800b9136100340300f01d00441c4260620a154440d1401400b445008000d962201070806802401c100c030189042442e11141c00b10340c2031325000e0700001006071407003006040c4400708039000035004466400f085006c1c0000b1355441040034401e8a0400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 763918920 1250 763917670 763917677
    0x30302030d0c0219110d0b01090209040b030a1a04030504051009140303090904170f1305011d010804030c0302031b1e07031a061302070308060a05040e150c090d03 71
    0x40d0780c504071000646442c008000300710b61180c03510703110401075845060845035000075150780712240400040d250140105000d419100020000150002c1a074003c0003e45411303a0305004c40075072078040545586442030082c0250420f1034a20140e131071017054103580684641001410700d80c0b20804100b21042c2140c100c000303c1c01e408002d001580c00003890400c3e4100803001145815882408200c0491010304010905100c0011014031030480c40c05450b000d04800f04040d413540d038034480071030a40318940700f070501240036666002103510407500c0074080744d6410f84607941c10340c8403035a08039020b000c100415011400300344080310220110011018915030040d00800640024841d00807490006030303501c49155210100400014001045500c80000000140341150382c4110125500028075074029410340e100007452000c040d00611060301a03042914600c0200d03460342d003440125804481c0c508025484a00410041c0740280c4800d60321041880000d4200040400402c141e05154102103010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 763920170 1250 763918920 763918927
    0xc0405090c0f04091e050903030108030409020c0f0a08040e060402120c160c06030c110a1a0a0204081014060a0303020c1002030c0d0c1218050105070f0213020c0706020604083103030203 81
    0x40b46100d009031b50700301010201035031441d494410003590780d210320320421052710780204080312486000c0c4840402800c80c482070b01c81c030740d401c2c0c40c11400c1e650183c041d00c2e020b0244440840c2d01c0341018400e803410250b4107000400746480b520b03c0c000d401d40014000a0682207115074000004910000700e400802c091f40700440d08420b0790001a00300040740a07510b42d01c2e8450396100020400300103400d060310b05240c0c00310b00542c03a569801c00c06032260f43c100c8070403846004140d40302140c803903200c560b03d00980d03810080303607407103400c200a40e4540c540300240040c1c1c41800c00d05901e01c1d2586072029100d00c640101c1e4909865550700302c2c1400000b01c0b504011a44e407030a040184900c81c8900a83c2989600e08144450212400300092103614050941042030105103041040300440301e01000380e40040900300b00000c8022900c01135401480100018040d0480000360103000151441c0030300da22004150500000c0e440d14246e118141009a0428441803c12420369460350440c3c400386001e64040d559 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 763921420 1250 763920170 763920221
    0xd1b0f0632060303181c0507061103120103060507090e0a0c0f0c0b0f100905100906050406050627060f030f06310e031c050c0405090c0f0409 62
    0x20740715400014026503562001082016039002c400c5884855111110100050544c00425404401c07015414000c0840041007400e000002038104102ca150f90b03a145001d00202441d81e0312070085814951034040d03002c0052001519a401035540100342c0e1500019203030303442c1c0ea80d2003c0c1c441980c50758055a5914080c242c0e00383e0000650768221400e04050f001003884e80d039221074040d4010b10300c880c0d410300ea0010400103040c004000d03009081c000e1013881142010f01d038850042a01d0b110349055589018000100341c241350182c4012140014026800c055030f0284680410f0102d50070410029480c600821240c1e5031600a408286d140c80811500c0e440c181005c10840302c0042d19240c0300383c81e03401e03500944000901111031240d91603c3c01000401d00003245c0000307070030041032141a90001240c1030035200e183c111241680d00107a02d0510258651421400c0107104a0040342d1b004946580016a107800140040c54030b080b02e922030f80c1c81c0c2683d52600c1c60440d41c5e03200052a500340307201035800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 763922670 1250 763921420 763921481
    0x3070605190809030f07060b0603010611150903090409060b06031303110a08031f09050c130e010b0922060e19050c1b1c1e020d1b0f06 59
    0x4581901c50030003001c0c0f81449000c0c00c0e542e0007058403050007443c001800008202c602d4102c0e0260f10006413140ea01ea584071400070700b240c62250911130051017004e6040c0e00c81e4460054540c0180302c104051494004400300340009042c0d442c03410381c0c4203510780300b007400e0750f44032040194440c4611203d410b02820241c640289904040349000300d00e0741c420000540810340d000c080f06e0304004984021080f6800441c0039401030a02603112003490f615203020045e096480c1002400c3c2e007003200703140c0001d007170310740b01414003502c402e00846140807800c0c8200c10450030008000c20174100b01d0040b4290000d101c0c0701641c00e0300c0701500044080c4240d441808456202181808000040c0e46001d04c0286014056811140a01469144011101d81d003c040c20780c014003021285023044942d100c056104514081c1100411481541617400900c600c65109440454107090989443da560300a00c00300206401094507981420354200c0b0030b400c1e006001801c588901c003046800c0540707980c0c0340309804071080c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 763923920 1250 763922670 763922707
    0x907020105180307080405010305040f0c24051317070305010e01020a110a050d052b0504030801120f030807140d090302070609060e1203120709090b120d080603010b03070605 76
    0x2078580f54014021000010741140550b400d650080c600000c59030b545041c01c103001100d0140142031800702c4100807401941904170b0003502100d141d4034490f801d15440040380c1074410304000d41480c642c0381c0000e01c28000d45404020b900b41c0c0150440d88030b2503e0b03031111800c42c0e40010240301c7c1030b940090340d182c2140d0000d0f02d000c500c002d26000340400c4100c580307685866150f00c4d4465010000001000000340100d4241e009982000030080c0040d05510740b2160001c050985095021a050743c00010f580e00b400d100b203006283e40661160a11002d0b80d8050352000b1001d0413501c148100480c2c420396041496000d059030b090030010203c0d5040013410701034140b00403a001b00b400c000d41c13007101f44125074100343e1104a00000740c801c6000b449012041a04500500524003c00d100444c02e1003d03455200000c0c40586041400402100003110f04201c51842c0080310b44440b50040100300ca002e40c0a00704040d8046805000402d0304044000040c0c2001415000b42012550100b80321042d040c001880 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 763925170 1250 763923920 763923961
    0x905010302040e0601080a061a04090b09010b040b090a0e0705090910051c05160e16080708040609052b0207080a02031203090c09010905010501081e0714090907020105 73
    0x8501e40390500f10080700050f0001c00b060b052101c8400483c00844141d8000d500030021000d0315901068201710310804c59215101e03220380c0c142004095042858011003070341c1244d9103c100d0303500d02031400580050796000454100d40c0003468200000d03200b5540310510307108144683c0c40c242d540c036010341004400103000d0300a40040c1100c0740c0c1401a40c80311441190300526942c05207004003558507080380750200c026503c1d101d407001e40d0000140302000c100b0070341c00b0f40040c005228285406501c00c46d40701d5012541400000e04800c0494040381a691000d20514040c000303a4004e6181c08884d546140d031302d503660710980800c1501103400c0503414025174000c1c154803800fa1851000d1034000035583c4610030020500ca0ba07001011401b14102000410300c8413102600b6001d440d0382d18100d40740100024400c6a0101e0903890024484012680758581c2420003000d008085480e007810480f40d00081c941e0480c014003080024024035910180601c1c8600314590001c40d07146401c500f03001c6554150403c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 763926420 1250 763925170 763925177
    0x5040c030501051011070906080601180b01020303060603040609060e06090c0103050103050c2b030513050102031c0e0a0204021c140106080a0f0b04150f1d19110406030903090501 78
    0x1480940e0340e42541344074000e468039040d16440c10410000782040c01592140b140940740400002e9641008140203040343e80005203002115007155802d0190b9607000d02003070060304208009003491408401942e0003a000d0400010f50b0328050f900e2404548145c107d28201e80c3c8607504218070540c007005101441807080c071302400743e5491541c3c0c080c0e1301c100c81c0c052103106e0310b62400c0301d42e403400740344070800c044000f050426004908241000351950b8001002c0b002001003d031400325295000104840f11200a415400101c10720080020018240780710360005038050f003010b800150b6514006000c00c0c002d80d034040700e05550800380c00c10880342040c4081c031481140400400070f403a041441d29a02080c4041e005c0b9101108a400703038028003810800030b13841494921140d900c00c242003c41000d4038040109082125202c41041d644120710b409143c110204040003d0340e543d0079046000d58a0480d5400426100540c00101046401c150000307400079035200404001e01d0380c01107043c0300600080c00e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 763927670 1250 763926420 763926431
    0x307020709111e090303090a182016030513180605011b0b060a033002010b030a02010e0d0605011d01060e09010302040513051617010b09041203090503040306050105040c03 75
    0x40b83d1007104909042e54118800020500706520f885c00c2c4111104002d0041040350425101e8051a800d4405180c246030858075000d03180600600e00c401c87c100084464036200d06094a414140c61143e100a00031020800107210143c043c50b0404d11800240c040340d4882c0c5004c081c80b1003d041103500341c0d8040b13410001c444012042c09a50758081c01d603c242c003e01c200009940e40d0001c1101585668401880c0740b80050007200407403504682544003045c0c0001c02541a40c803802c040742030702e54031020385606400c00c10700400158001d510440c90448080e240e500b08080c1d41d2541300441d0007d9110015511b100403038840540c6580c003002c0e01400403800c2c4106202807031400b085c4003090500000340180e5a03400810909000c2c000f01742d40c04c0d42e00c002110b4110584085200078014240309000b42d50411982813083c650042c0100ca25400000d030202c84560359645540c0d0b1907102c5500c1c81410705640b001c49002250081c00104042c5001c1c0001240c43e5140c2020700c02290183c40140b4101880c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 763928920 1250 763927670 763927687
    0x14030c0304140f07062a021c05010609150e0703050f010b0304021f180806010b030703180804080c0a090203250e13051506070c090c1103030702070911 66
    0x560030340741c0094105a040c044441c1802d9031514000b182d0600e50424440c0c8280000e00c154003802c07040404083c2a20307082407075003406454140c080c59580095004c408090300c0a0b14070100e07100c85070818020300010071510707038940c0031034101d400c0c004907a084526201c209114004120361840e4110509103002c001328500101155003800043c0541b011740320000003c01c0c295658060b0080090008103030b018207100c400500545050b107001c80e26400c005900700b00041701c0c000800c0c003504a070000c0b14228615907804504800501d0584441038140129607030600c042946070000c2d00180c0700b80b0b0004c0206482220402140001b15130010412600400c2000161440305c10f48203170248403880c3c00d400d880324003041a00d062902c0f00741907400019a603d4901c50030b500b03801450003074212580032803142c0040070030b00441d0b1190440140000c20701d520100320540c2940d0121a9459261500d88000c44102c8291411a80182c0e40c2c1e0300140d11401003400031500510442822090704000c282c94420701 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 763930170 1250 763928920 763928941
    0xa020d2307021e19031e0306030510021e0706060e09010608060f04110f01140d14090a0503070f020604170f0c0609010f05030c070f0c03120207062a0602030a09031403 73
    0x10f18048221310581e0302d4044041500605201e0910791402d0319254a020380700000400402040c13000360380703500c524030103018a02202e02c211191490344070030070a100c5a255110560940c40a00219491a51580000f902c402408043e90041c001d4200200b98545000c0c1d0941c1b50000c094030102036840e84e03805010000300c01203013080a10405880d104216a034460044c0e0702203850f980d0100311070074001505451900f06500c032408202d94054001c025403a10b8903056031300c0d0045c010007003140c0e00030424080403503c180b603450030303040c0300800f410318003915078a4507488a42c0107501c11009034025202458210014850b0205a00080c0c4100703041a024400003000b14481c4428001485000800b05101c01d03900307000c071040030303800c00e1903002c1507545460102400c00303a030300c0160345c5200c8c0300810500385031001c20303000201d40342c82c7d580044075844000c5554840c2c0d40001d074001101244540c140005031180042d52240039200d000141c1000f503400c0141a8051407100180e50031000c20401511501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 763931420 1250 763930170 763930183
    0xc170c0102070501051b2a010206090c09010e0c07060c030218090426040306090f0c0b030108030307110f0a050615330f030a06030606090209090a020d2307021e 70
    0x45004080955210291090620358440396008088281e2859106071900b441f881001d0700d942a402c5400945d5451005a140c040020355560b00240c075000421044c2d6440040e181c001d5601110340b45001080e039108011035000b450740c180840d0b004a1603460301c03203210304c600181900079241d030035207498180c0c3c4100f006940c0881509952000d904040c404c1e80b800020391b005158800030403c031410403814105003450714040c0403a48503500c841c0c08140000010103030790403210a07400540c11500d0316041516403030074000c00d800140c0f040d9480900791410800c119007865000741c0182c2402e041100150075000000c4642c0c6001e002c00342040490442c000b00400c0c0584900b0180d21017003004003800350128810707141c0b486103440c00802403110510313065004408403882840104581130741d40b5081c1c0c05a009000080768410920703c001a416801a0010b1085550100c00019002406804d1107214843e58682c442e01200d681f0401800036010810403c201c892044045441c05003480091307035451 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 763932670 1250 763931420 763931437
    0x1020c0904080c25091503200609061207020706031509090302070302030a0309060801170307030e04060f0b0d0b010503061e0d0c12230a1e0c170c010207050105 70
    0x207002919030091101809103001107101224109804d0034100c008003a810000e0058074142d51810f11804601205e6070305031012644d2104140c80080c40804207031090110201030103030461000c004100d483e5884800074071048070300100c051028207000741d009140440d5a007060040c9894407221a054050300580c42c000c1713841e101c101281d07080c45440d0890801a26610080d010b12502c0c46850030580c00001c404280d85240e900e1010580c0e0754071440d00b6440c000c00030898a07400800240001c01e04c20802000360260151020422999034200282c40300b0055001c4032849038042803000c4404914019400c4243d4246041800c40c10004c00141100014450003d020350214240108980f5003140b00404150800e40340c0b01d0050b6540c0c00c0c2000350813660000c8490501c00342d0400c00340050643ea54000011100081000072499904c80d58043c0b48040046c5113412014503510020320000c4405d0080d044880c10f5526084901e417003249041c500b070300c10505540042d24280311590388142a507810300d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 763933920 1250 763932670 763932683
    0x2090a032411042903090a1e030909020901021606020f160b0906030417070303060e0f0103030926060a0902210c0f04230115090f15142701020c0904 65
    0x11890015604010544c540504c0100329000c803c20100318004200e1080f59400380c801e0403040146a8076840602400600050200d07003030640c00c1c80901d0070356001e000584418011214030314006030920b41c1c0c04410b6400b080050303011100a0603002400d00400d5050380868240a80d458200507001107a4020035844038004e0340007100240600c811400070a2015a840c40f15a41d68442420f00501825a50007420840c20000012481855001d1340c042c0c101d03901036460524103414803240e11103104040204a1039070301e4070280d041e1041c0d000e0105500aa4100302e0005280710b0fa8418888054a01c0d40c041c0004400c088207800b201c40042403014050100f29014006004210002002040c039000c020300609000011462204c0c1c950305040e043e54150029a4030448043c070045074400c040b4010707100040c882400401141c2005080700200890604081c154000045440e224507000f081c0d03200c02c0b1205182e56a4900e10000828040c407880a01c0940310030116000855042c100103000203040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 763935170 1250 763933920 763933949
    0xb190e0402180a021207050a0c02041508070b0a11030a020703030f030f0905010c030f20030a1e060603140103050a030e060409180b1e1902090a03241104 67
    0x856480790b201071000040c0610b484154100910f1003002500611104048074028101180e0741500880c00d840c6413002c80c2d6546a00704159074240400f826883c0c0200350b02c41044000402d1440303040c00600041c00c0b544043c2929024581d200a00c0118500000d68068004205500340254041050810b0301e1301400d0620b0410340001c0120014050080f00c0040d00303180411500c02c201040d00000c8189800e80c0d8207000d51455960481c003202c4414042c003060300101017581e40440c080740e018560004801c2c0e000690081481226000084071034058813005a480c0000d000054042c0700b50030075280810020a03da42c15075844654072040740da00501400070100740a5241d64034041101c010f00842202444400040904140f005000f15022591064601d000441c1c8001100b1040f1484010740041040c0c1c2e00e45a0841c038448207442e07800c0881039001c02a0b190141c84074803600e40218800d6002c2500e24003e4046910090040310500481c1801c0c61083c0c61a100807500380c5040c4c0f41a81000da04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 763936420 1250 763935170 763935173
    0x100b0a081803071e020a050402040510260f0117070b0301290f0d0b120a02091005030d0c0506091606030b0d0501090f020a30051504150b190e04 63
    0x155014560300200a100b0141c280c00013101e0445601000b40e2007602c188010684560400090340a0b50250355000b0511040b40510301d40f10f1060a100c1102042090004071448500b502c1c03000b1045503242031036100100100312100030031040c01001d501c0030010700700503428062207411038481841194118841d00c580100c8101981004200d01034541c0f10f804d995103c1a114030502e60411559042c001c2e241c50481036050500c40e03003500c2003a109001a01d0310545650802c000858081c142e01c1c0c00580114021a55413000c204814544010b9296500703140712501c2c25078a450f40c010507140840e0400564618007404d0b184004c02a07e00740d003000700d1544181c0010130411004208060819070804200c0c0d014494181c1c151942c2c40c1c02900d40d4601c01e40c6401c2428034010741c1a212240441c84003604080c2c2c0e500780007008005a1207030080c2c404003041c64480c0c2c2c0c9a1803082d0380c00c1e100b064607083c540700c02d144e540c0b00304140b00d0301c260b4a00c3e0003141c902c111404050450311801145103030b0781000030f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 763937670 1250 763936420 763936423
    0x70c0e0603030d0e01060504321806010305010207140d02061803070c0e0619060e011d04140906010909031b06060b030114010f0503040f11040f0903030203100b0a0818 73
    0x1003c00c1020354080044a000200e124043e007107901c280d0f80540c0ca00720002d6500c962440d42d029461646150a180c040c0360000364407100000148055420003032003013840641c880600c02c0c14000d42c080e50025840302040d0519440200454402a4940c0d1003041903503030f0603170081601d9500c41c0d0004500c0d0721104a6000b400e0961161050003010204000c01c0847c082005048040c0541070035070704440f441101c820700c0c410030806806020007052950b00488420340c4112440403118081042c000400d2003c08007107800d58004920030050b422010007049880c0310104103450040c05842000d0160003225203000d4079402003004044071000242d0201000c2c0215a04214024141086069565a07440603a410002c071010b02d864006026030f2206000b0314402d60569007d240c00140084504015540c1c0880c0341140c00750454000b61a0f0f6186d502030213407803040c0c14100d4043d440260b500e19119044810348411038000c2007120a050020a0038581e00400250744a0ba01c4060160210988100305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 763938920 1250 763937670 763937677
    0xa05041106041e0e0f0a0b150d290a0b0304050705120d110c090105060a140f130f140d0501060302131a240f070605040521070c0e060303 60
    0x190011400280050b142880310341c00c280315041090100c0209407104c012080c200d405460074100c81030b50f140490350315400c980c04071480802c002c180c20241c3c0d040064a85543d003044c01c5800380680e8601c1da0844a00d10302c51404403103031080202c042c644038070000103512000e0601850a05640100008042100802000300035100003012603491400c0e0460650340e40110304050400038141e801d001038542c20008544c00d00c03407030042000c00d0a07820030b000e20016030000c5000301c0800003902e0b882020380054400400140c0305611f010340ea9105400300c1260042000e40c005044030b14900000c204815402203205084203040342e0400c40680303541012070141203a1f0300043c1d44a48501924140b10344940c0c072941c001d090410400124102000400c0300e84000070307880d51050138503c129040d120821100610300e08002d10804c1c1d0804403180c03107220071542c044404a403254005040c0c02c03011401ca0070356490294000040030302d00009030781c46036004c0943d1304c24405c000810030041101940e051068 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 763940170 1250 763938920 763938953
    0x1c0903060f0902011403092112010f050406060215040f0c080319170603070329010b040602250519030b0f04030305060f090f090102091002010603150b03060a0504 71
    0x7070000018820110009100e041c00c100d0219840112407944900c004003903d00c0f03502060040d00f804910070030323680c05d44840e041c84035908500c10003407200385c1c1b01c03136802c03150103004072004c0351400c1802d00c0709104c115000f0350820025940002602c072040a050049181e00652001d10000c00568515007681160102d82010115000114100a8040a804107030a620046603201801801d00b002c01003022141981c056030590800b10f02800401c0b00010003078485130f50700c510090780c15071500718941d213801d0a8006c407070b69500c0000d04000300b6070704014090a1003030b030020001c02c2036846400c0b40c0b02d150052045900448442284e8948210424900c40040d908040c020501c0e140240840351052001c075411004203140002140080c142600b5144445402420b42441510740c2220b072020044001c1c40c2c2040d964081101031941c0e00c1e0b0810000505a56800129000d400d42c078165008a1100d06228446e5280080030819aa0000351132a040300d1090300000c0d0903111801c0181c7d900c2000c951 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 763941420 1250 763940170 763940183
    0x121308070c03030c0308100b0d050613060602030403061d0a03031e11030405100c140c12070b16080c0f0307030924110a0c0222141801090201021c0903 66
    0x5143e0861004407030948655620245039803005c00c11f40c02410b090181c000080c00030300400c185841d503584030300d400c2038000380045040d44c0401c42040c25a5480d8018000680020404004002160080305081002c101401600069140005641d222042000340400d40c90b980c0803096490500207101000c1a222002e10001407a00f01c03c01055109a0f070481d820310074010640d00413130349442508c929402a5488104101e8040507203c15a0011204501c49001f004003d10052000b0070041c8042e80c0305002012292405024200e450100f20036904107105406007049240c02400049505c2904200543d507101c1d01c8020040300144184e94000381005003140b01010b162540b00c0307188140301c171110414020410303001d44240302401160418070210b008290101c0043c0380485520325048911651001d043c9502d0300114182d6400c03850b002e03680b14550301030100c4820540b0320307844092580c2000b8040c2e5034459000039601ea034800030b015040340302000e03c0d040c034a10410900c0001c581040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 763942670 1250 763941420 763941443
    0x60d03200d0905120f1f0204080f0a150e070501050d020909070513210602030721091703040528080d0e0613080405010807260114040212130807 63
    0x8000d0180040ea02586100e9502c2051600051348006140d550000c40325005e008265029021080049005040000c1c080d8083c0008141d0500800176250001f12010060036120034600344003000d60603414454003c2410440340340e080b11070015005003256401c0c64056512084030310f940000b4003914610a40c003031946c0c0203101034940c1c80302c0070f44540c4104221103442d080d80d1f0315141d034480e0b841ca034841080756044810300b0089030580d0302035075210010b82003401d40000b203070000030107800d00701a10451142d5249010380030b01c4100e82460752020300c0103118502c3c50900d41c680b29070b282400c0c0104800c81c4010000840c000480900100c00507038481442a110010701c40a40041d00e508208648035103e00e0001034104c40c03d4064ac800040e8109036042d00e024104801102e04240c020140360a1100c5004802e80001422041000905518003180a5941040301e266202c04140c800d1900c209e0045c850a540340c800310407800c0c0c0141002092001c80141481c2400150042000180c68800c600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 763943920 1250 763942670 763942693
    0x603151505250f0c06210902060708040612060f051c03030e0f0a150209060f09030a15020a0e01031104270e0d23041202040e0330060d0320 61
    0x1d009441034501c5200e90142081d02c0320305c100c4408aa0400e5115038046000701c0549080c203542c071a888a40c0090720319071601180d61100c000d00d502c04d50004000440a25043c00780420034070501c005001c4d07001803409000d162000141d40700b421401001001d4808109400070117020740d114061084110054404d100c074000302043e2208166003094a8a036682500f00e0700b2020300e4401c0300c4410400812440c240b80c1c022003074000540200206a80511800c0ca200d40420b2880308107146a040844025036641c03540c180007840352603c100900d0601d401d0a507940b1a1080180545060b1050315200c251168500c1005281c4c020000740000440e07403410f4001a005100428441c1028580d6194285a65480c01d0040365074822804000300d501d50510041c446150040d03008105d80c2e000400c04030f41c0c1012000000d00b036a0186440d2580e4858504041c00a100c07403204401220414401145491030544045038445072101401001c01a00075148000320400a0311002d060f140c0c0c02c212a00582034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 763945170 1250 763943920 763943933
    0x307230a110106150c02031615111011070201020d08010509010b0f0d1d0d05040513020a12060b18090103050d141c061815170c0310020301060315150525 67
    0xa6030303050f80030340a00c8500807903e40c100c41007541110027800720300400c00e8950300d0480e600400a21280c0f03181c0104104040c1c010a5400341d40c41d40c0c04142c03912540d4084500c0003a10b070201000c1d281e41800b25520040110380e4410f51140d044510740e640c07090b621007a02d11807440c140b280301e44031000e43c0c1c80d001e204510008a040c030048404404030440d0401c1003d000180c520380120320a00d036012501c030806600740300031a00500101c1942d42000640103144000300d030b0503914241c00110384080049562111141c400c01c1c1181445010b43c4c981050b5410354960f5034417100c10b400190180f144100640f20580c65040441d1640d815080c201503070307518100400006803c0c10320402c000785100c02c0c01034000d0001d61140000290201c0720203901c640c03034040e411030720480e280180c00260090342207001080d1010b22400d20228003040005075a9030401501408980d4a140182406009090306212151082c0d2a0400c0540035003403054540d507440800180c072113050b80002d840c6113800070a45003000003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 763946420 1250 763945170 763945187
    0x60706050a050903040b030703150305030309100c14160201050708070516090221090f010c080109151805060a0f120b240108060301020c03030c0307230a11010615 71
    0x10401c0601140d10341620060b5240140c0c065059072207002c00200b904c141c002d90101c4c40c00250b01c000485c0007039498072250b056810496031400107400001c0c202020f101c092058421076445410540d55240ba92038800c5628020b8500c4101094441c11120056a0140d4252003203a540105207694400c110724007162142001d001c5241000c01da8000803038107031282e009403146c01210202e0400340302c00404d14014107c0c80501588401d000340d140c02180e010080c0510940480c49450702c1c00c5a501d002400001c54101d40c043c2e6140506025080c850000a030003030740c3c1c4c150b40d03400f400700d000d8813a0390000e074100e6140d501c51090764488042c0000c0c00a611031010030018003036010607081d940c41c24001d001e1448840070503c41d005142141e04d9013036000d004913580000002d0001410001e104180d68990f50094845901000e4084100190680d02905038001e06030b5031440c07248411b00326031000c0e20354003601c1801c200b40151f904805200e200254002001010a996103108510858201070045070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 763947670 1250 763946420 763946431
    0xc0e01060f1103030402060f030448082d0a1212051504020d0b06030708011502210c0a050714040e120901140712050406030e0d090501110c06070605 65
    0x562601d940c03501c42c0350100039a881075801500886c500320045251040c19072004104440c10380f0071841c400048030100c140198001d0414810010114041c64035200e50401c4e0b146200410742c81c2e040038800c000c00428041100004225421910802d01002d040b4400402c080b05c0040c3c4a0b0108103403d110f6030290200c15101c0640352a01c503000c0d06041ca000360b520407100d641601500000d40c0c05542000e90041807001c03182c10001426044c0000016103941c000e0f100c1d48006903510300107111409201d008008082c52500040414080045502040c2c0d04102d0007061054000b14003480c009400b805075100240e80324007540c5c90240c448211003003491041034890b001d00e1034010528550f210000d00020700404c41880107003011011030044901d5082c107102c041c00c0d920705001060004005941134001c5031095125035440b1414808010300312a101c00d55180f081e40218040c54406401800c46000c0c3c50003031a11600301c06420a10910b030504064800e078001400103250b10030700080ba404035000c0e1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 763948920 1250 763947670 763947677
    0x6180901060f0b0304030f0e130e030703030b060c0604110a08010905101d1207020a0b040f031106070f260c0309031009030212180a03151b05040306090c0e01060f 71
    0x1e84400f0481c03224041207600030042050013040c02040c038051400800b44842c01443c00054620282100051f504c1803055102641e0000c00e48078101601402105411981560102e0030508900e0b034460340d0b40c901801c0a00044c41c02c150008950b207900402e000600420002407005c52014a8500d80d14441014100101c0e41741171804a200d10110912038116000380008100caa40c9a0300b50540f41e91010384100e92001040000140402c0c445014100602d40c10300d024942501d5801c002c0401b4078800c8140388550010003415001a080b55001c604d140d4001d60410840f1003503008800d0121040b0120810055012840714090b10000006103e410016030a0342c03c41200324016206441e91200c00401681109403640403405006e006030450f6107100c401035503044000004203c105007141c1054401b881856030381084800603000c0c044c8031000c04081102c022009884c024501d0240c0c2c0401000691202400c106211601110b5009480b6040c9040c00c1942e41d0a009000030030654100c1c0c010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 763950170 1250 763948920 763948949
    0x2120a051908161202071a011806120f051e0a050c060c030f1602060706140f070203030c0c010219090e011514071505040606050f060c0d05030618090106 67
    0x3501c030b00503041c01140c11107100d0045030500c0c0426a0640b0082640d910002e9080c0402008511021801e125040003d000422654140182d45600c0d200300c40262000780d05004080000b440280101c080098100c050b01d03503205007501d00181446841c1882d400000d4105200c035411900c0460001d42d503500c074204031400a101803003480954011010301a01542090000d900c12024003401000e14003940c4581905160349540046c0d60781c0c001d900242c984994585100e2442200915500d070003520010390a803c8ac94000c81c001d43e40d1100a02440000b40e010680d000064000d4050328160b40b8201c40c0198141d400b000d000f00702503990302c141c5082000200001450310051401c1d40000071181d91800e102c151703590310f400c0305a4080070048401002042070049032058510a5500452090718041107192400d001c12030100c40c181c49251282408101e090607a20b400100030b450001300381800c40e00c0307a5800f0300191554042c1900c0340442d501900401c03807019030661003101580d0003031014104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 763951420 1250 763950170 763950217
    0x50f0a0b010c11040c051306021e01090f1511030112030e0a06090e0606040816050a0803040e0a050408120103030804120e030309120115090603060b03150a0b0102120a05 74
    0x142c0034041e0703201900002801c0c051100e18245504040700e1107200c1d0910038580660440303580450a003544c450401600550303888144015001548840c1080690090000d0400e40d00c450f00305400c144801400c4410125003600c0000040e0040c0380c20f404090141a22580d442822800300081c49108800103110004c41078034a00d80300644a003540c116a440c2510203040a81a004400000d01400e42c4050b00b880700040ca204108610341c45007400000c00b868452400081c002040501d41103050950000d00051281c91040c0c42010360149204001007115103507428889020b21a11307c0c40e801010803a000402416009400340d8010f0b07110710b01d108400610201d04a0300300c120f440f0307082d138107400400c02e00c000c81ca40102c01207060603202000040f2a070300320309401980040d95103c1c18026445000400601c4514454124078000aa000d080c2581c25080c40c101c81000082c2418490b564800c401c8003964800c10687c035100b24039a490654031116800090f0080e049020ba414a05007460704894 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 763952670 1250 763951420 763951427
    0xa020d0c082a030c0a5d03230114010c060609020a170603210c2b140a0e010c050321190e030307030b1206180613030203040504050703020706050f0a0b01 67
    0x140c80c801d541010b4680326440e907078111a646c029000b0000255081c103280100c0800180030000c05c003000c0d180020014102c6103a4140c104d0b965404114000800004100e000d10510845071800f02c2482d000c548000340b442d05400038a65a003084603002d05c0400c2030f22219800c0402512030840d01000d2801e039607940c000f0999100d096034001d51b044181d5144d00c2c031486e51158003804e403e54080d025103019000c40c60b40c80889896003c0045501d035807040c050342c40c090b000700000314080a0008500d1a18141620160100d1036801c820350400401800c100d017400000c1c4165100500c132103241c1189286d10744070026800c1c4081c1ea180403980c1d02444418692159841003102d00c0b0400c1c0051410341c1c0e510f110a8000b4031089042d19080040c0c0c01504010200503c8540d00c516040311030f54885a1100740d03801d00c1c1040007040c0700c8102d02c5103000200800d0b00001654101d0300c0031200403806594407a0110082d002c0d621005150f241080e0030302200441880c40944201c0010b0010044000d0000044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 763953920 1250 763952670 763952723
    0x317040b0708160f210c02031b030405030a110a080105190b0f0306010b0c0304030b090a0303140c041208041509090c1412060102120f0a020d0c082a030c0a 68
    0x203004548900c0800080174024213101e10b9000c203180740a1011000c0706201403d80708460700c0200103802c001800411040b48940006060300c10800460815040a000c81c0c1e80300f55100340900600c005400d0f901096545940500c050705048009000c14241460b000040780300d00030310321040c10700780170b40030360603090080b810b4074145402001094203074030b482c80b01440d5512a000201050208000110214019004203400780d4442001401d400b2440d0030024200c51080c11011140140442407227082206c030790580741502c0128200289041e4146061111881154030071803114882110b1440c0071134000c00001c007100c2484400780703c00c0990788001c440100101a00d8a2140028440895041000c211150f408001030045070030b41ca8030342014000580100d940458800d00000d801c40d0402c0e81882040840d100c07078108040f4195156803180b20074044c5202e0910546000800040340d804000c82c0b81c290b90303400806491346d54030400d00098a64907550820f0350660004a5070150700540c1d161907 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 763955170 1250 763953920 763953961
    0x70e22030f1719050415020a0e2407031103070605151002010204231318060e010b010c0206031b22142103040b030f070815010e010c0317040b0708 64
    0x421030794112a03c0444000c202c0034000b683c0540052221585004280c801000d09000380e4603402c022070143d4007048035040c42c1e4000507103e03280161303003126010f01d03c9003135030760065150030a0381c5200e82c0100c009265015060010b010b85040c00284070b500c06241d440d81744c0c03450303003500d041c04500841c41d811ba0030b03803045214030b5044200140413000a1210001c824000120082842090000c1084890180c0d010109446803281412030360340200101482904203085010000317100e1500720100280050a490501030f000344000000178100300045907581c5480921039482d02e8440c0d0003124007003000c0a8100b6418000b204848006c945038000504200310980010102d0340d050381f02c0c03005404280090324450445100601010800c0d40c500d0b005180f140d08141d81c803014a00e00303254000d008400140ca179188c08080031170f0703880e41e40e40d200d603010503001310a0030800312118841c6000c81d104c4460840000401c0f819809010070441c5a0203c14010500c0f69a18566603c1c0c0c002c0045074440d103903a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 763956420 1250 763955170 763955191
    0x30a11061006140c1204140a120c03031b050a03120f05191d01021606050105061204060b1809030d140f0f13140604050d03090203070e22030f17 63
    0x440d043c4260020004041d9400381070300390364083e12074403655400350304035801c490754508013640095094104410b05100903c1e020b0b072800c84681c071588407040d000c0d216000c003a04000a4040d112010201700e504031914540c490b080341c15036034241c21300401c40f8040703403501c0b11018200b00798001400c41c10302400740543d412580440720f0342201005c41000340340da941034000380f40300720312103101c0e100c000c2c8051720010b551611003848007a041d1900310f00300c50303050704200e10820041c0081c081c15203c1d00d4016901ca5401400010701e242c1280010b0510b6003402a207442c440c501904201c000103000c400340c0b0301416024401c0c82014180442c0c0c000c150802c0398403100070380c7c0b100d000070810080549000e410441609203014151900d8640200c0840340c24060481c0340d10480901080200400500d0f0003610329181c01c01c2003011950021703482d40498442e0003c2c00107200080b0362404d4481502c3c94507041071440d4620340140c546006058841100052004290a200315000081d003100c0d02510840000c203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 763957670 1250 763956420 763956437
    0x90305090f190e040611040b16080d11040e0105060a0519090512010e0c0405010b0a0806040f0203102c420301050a1103012303030a11061006 62
    0x40c1844a00032120340c045601494036060001442800344281e0083d0951485034101c51a00b0304051054400c88460401200c500b000200900c030203202c1560185041140210100b01c2c9508001e1914010503c0480d681c41c40d042c003040702d51907490000c00807244c850640030802ea0740c9030100505030044500c0900030840c104a550b00c0030401325400e0040b10b03c1803d0129503a5181c3c0007080c2c42e13503102540b503126607540e414403060302c40081010786c030642e0044038184103030742c10604c2e007100380e0082e002040b0501284101107000c980c1d45030050903011301c0c041002c5441e4680841e0071b0400c01464864210b61482c4210305004208a2420070034040c0750071003080e1215102c40801c011039266404ea0012140000700030701100440e107590080180e601032100749400c0341c8420400d402c542000e0f110350b0809183c19510790f08210390406490440e40c45800c03003102c002c1c04e08054141400210300259140c040006c0d1960096080010003000000c0311003243c6880d62108040440f040150003600d0200f10100c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 763958920 1250 763957670 763957687
    0xa080708120c010212040f03080603070b09130b030f0c09010f0b0f0c15040602040801111920010f021201050108040b0402060d02090a291207050d060b12040c0801090305 74
    0x101c004042040050000501d0100d01d91644120f5000079141203c42201641d00302082c5540100c2d556040324044000c1c200c0e182c41d1101c00d000a1181070001406588000040080d001041d4001014608080e01740c40000e003100b085691102580a0708030320890300003001117003800a0800c040151031598015071310300034613600001803e41180d15050781c54811004000c20200c03500d02c5d071a009a1181101503190b03800c007699942075407102100007014140a0281d03070b0b40c642d4444100728650f000c509040c0181340003002c0c00a80e6040c00700c5011440c1d03080c41840c42c10411700740c0c020130030564500c120301543d0f62036800454400e04192809451288442c0100f000352034990b005080b190411703140107107495003440102c0c100052541c0f00007e101d104201e0a505003c4100200f4850305209544a190079900024442e030100e01820000800038041100100e1180c0341d403242c00502542c4000d141c6402d102d0481a0711408201d4044030403001c110000240a8014002d0044484c1d051300c03920304140c0301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 763960170 1250 763958920 763958953
    0x11120f090a03291503031b150108060702010c0503150f3f010c170c0d1d0c030102040602250905040f030311090d020913080a020c0a080708 61
    0x14035120307580542400d9000002843c030903850001c12a4111640110071041080740381100c3c4024649111141e004080c244156004800c0710020000c140e02081c03104038503140e452414140c040e800e500e9401c61400840d402500023001446150603070f000b400340d0702c6070780000c0325540000e903a4a00b840010071000b24980c034258240c805230344005030a003928900941e408510f035912170441c40f02c4105581a41c0079002181898110030007124100034040c1c001c60010040c49840e80303128201680e4485c002081503101b601c002c440180c81240d100303104056030020218040b581c0c40410b20100c3c82481058160340c1418000d550423128250054a460011820b080181500c6404c0c80382100c0454900403520b403859110316800340340140401604004945009021607410340c1c6140003600e0103110003a5a96240010080d1241d41a039001c800c036210001e061516502034140103140e0304003c1030003220544d00040703121141608403140801903a44000c0c1d1030300c0f203d26020711401c0b0b811010355803040662 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 763961420 1250 763960170 763960177
    0xa1e1703071101051009061d040b0414030706050a1b1e120e1c09050a0311060d0c0809190c05100507080409140604140106080717010e040311120f 64
    0x240c90600c0c2e058002d0036005242100d80807140f01c90454008102400b4400c0c2c00c0c41990f02419903002040c2d07480c51072403121045a0740c0100010b01001902000804100c40501103c0c040004d6000b1a81c45840c1c900e0700384082d000c115651550b25240c9002c01c8401044001c0c1031045107055102c0201035600103c0c0d095000280c82c200c1402c0c046110011344000c00c107449403c07100103190001c0c0c040e0300150512860440c800120160420030704000900190fa240f2440030101d0b5032040c54a201c0c000340002285850180d100a4440146025002b581e15900a14203502c01c1b0140c0058503c1200b000074200b0000c2c40a8001514003034003404103024a04107540701603000e02d010f0504c1820b02c0707026614034283c0d60058100c808080c0c4c4401d101d5481c00200c088072504800c080394140440850041c3d45103181005101e07000402c480380300440c40d285c0c09003000c85602c0d4a01190b29080d0f42e142c039900d994130b00d81983c6c02c8000030400c032101c1581400110350200078803c88580c1d946800a8808135415541 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 763962670 1250 763961420 763961431
    0x45090303070c060f0b0a090c08070504030302030919030f05010510050d1a091c030b031c0c03031505040e0601080d03140c09031005070216080105060a05061b070303020a1e1703 77
    0x161785000b001c0403039440503105c100411603104046a860001d0100401c0101d0181506091210a000520000741c000c82035551104090380d4094039030503c0c0b0744034400e01986500140074000c20248240074803906411407849640751011103070140703640390240309042080141c00b9285000024500d088407009491494001d07031180c0440e03035840002d1028000c00c2c00035414031000b2a6480340044806d08046c070000d29020410b01408614641c0040003400c101501c450081c03c1660b1a000c034540c22030b100b4000006440e0160080140b0000d41c20342503a034400070b006014043c400c03012040319081c841e000f4000e5040030303a804051071340c40342c401004a90300545071040c0e1501459151407240059071054034451035080c0d004242141001e007402155111580000410764100000c0024503101c11850008481040d26040c1d40c2d85030006030002034080b0b45003240d000d40203000c000400d2542c001383c0201c00e98000c5d02c444000740d040c2043c04005808200c40203140780b40e000b80400c000f008030300286a102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 763963920 1250 763962670 763962701
    0x10909090809031603062004090b0d05030f091311091e1816021518010f0c050a09080c0904060c0c050f0f0f01020f070245090303070c06 60
    0x702d810001904100001c4800d40c3e803070090a40420511505d4092564600410b02c0c0b03068010003a080d805410340301e540181c0f0000c0c0c1c1c40b182007010135210f0340903e4800a401805403030f06c0b0381094445107883e2340020740c07180c440d60b80520010203015192150300030380141c0c1d91030117103400070700402e0000d2030008601824001d1203030014400c03c1e49640520b0303c202020380100d04c2e11442c1055142615500074641c003021540505101584d1103110200c154000b04043c0b543c10600300140c0303500e40500398650000040c0c0e428030040b404075940144c0507094490141d02d418402e40d846e500499558012012119480056403010401051450340000e00e060054a040c20300b843c42603d0311440c288290240e050590320034032558020107002c0c800d41c0d0034081050000c2d032034005011a031756954064000701034403440914510765150200c0c030740110440d00000c0034184400c04504506609520356501da405c0c841005800509440804400c61b4494503807911101003c034259100d800044c500b078010205d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 763965170 1250 763963920 763963927
    0x9040305120103060b10020c0306010608130212060714160303020306180f06010e030309031f0e120a090905040f030c0c05040f0f060608060907080c0f0f130b04050109090908 76
    0x7405851101c6003c0c50203840c020030f03174400483c01c0c0003d404160b0036810840d0807240c0f81d21032541c0d020403000d04494040c5011801da48542c1c030820000e15880702c0003503001040007500c9801c10f2020941d54882c074084d1311030302900f031503040c100c07200c91084c0c40c8000c8840c0000307440340c00060b0003580595040741c00a000d8144085418001e103800c1581981c13020151405241000711075a8000703034902216000fa0f02940c2080310b0f090100c0e40d034007c0c03164000001c030303280f40e460340c02c03400c160303001c0c0141080340e200b00d40211040381c0c80340742c3d20351100078000c0000b0340c2e05c0d002285c21042400b51038040e90303100386c00340c0c030f0940300d601c0444804040d141c08640014050400003050307541d60054a0800000000020311811002c609a00701c801a5004000703100740c0701c0800c4079654403c0c1803a50f01c0038090402d00c000d6a0344840c40a440c0c40303602c214000301c901c08a81c4918620309503000e070a184418644c8948030546880310105603008921072a0700040419030188650b0200380c20800700c0c2c1c0d1054418609 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 763966420 1250 763965170 763965187
    0xe03040f080c030c150f0d020d1407181406090109181d0609070302060f0d09080910030b03101104080724030203090a0206210403120c050c03040509040305 68
    0x3100a507684480002e9200003007003031540c90184688040b00d4411594150000e001c0050070209004003008440e07441d02c00b241284d0a51295012210b0050701c025042081c2a0054a5400c0c862000d84079240041d1000100a80e521074440c5504141c5140c80c0c442c9460a001c01c0c00c010441c2d1015603850304000002c14000f410701412001d00440c07900c8413401280301c10911000a04104810301d450038154049070a104403448003040f9081174a40554001796100e00e03440d10b400c00d502c0b6441404400c5480c02201c14180500c4902400034040304580d008503081620034220f00780d410301a5001d602d900301e6056070a00c601d99074408030b204880d4812540c106a61008010300f40701c019484050a11140d1105440d02500210180b488030304c20700701181182050800c8642e1900d280d10024000c1c0f00015213003512503d8007081d8411402410300302981460179140041c00d1198100303604903298201010030119902800c291001c400d0960300640c01c0501e810700300046d00704040c10a80501404002c0102d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 763967670 1250 763966420 763966439
    0x70e0d0b07051b010209130605100309030c080c060106080901230a150e090d02060c0a0806040219110c011b061d03040305071a040e060d02040f02130e06030307080406030e0304 77
    0x807410f621000580fa084170100b80300300303880c0c0d01d44055051454040d06010f07a0395004c02d404142d11281c40c00190300201480d0070b803400f0703d118102602c40710003c40c145107c0200042e00505952080d90354115607150188641d0980301038010b0b80740500341164032100842c82030190307540e000c800108082801d042c2800440c851f040f49070071820724110300f84100b16811034101308181210103148014046441d060712005564050460071204203c400004500155100e4040d2455107003502e03003504001d0180400503040300440100701e00d0b10f0086e102c00d0003c035070084a0003002c1d400e001e400a0101c1000d44c2e10171004124a00c1c4007900303111a99828540f581041020f0800746208000600c20141813400081c044050071122040b01ca030200402d21801114164094000609035880071042c00c0b20f200040c09402110743c8030f4810752021603010716600c3c4101241e01200d000e03410400c4a41c44510500d6240d10030100040e01a40c8100010400144a80e00410120a0407019070b0306041c0c80d2104070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 763968920 1250 763967670 763967707
    0x100513260d090203070605040b1207120606120b0301060b0f1b070e0901050f13030f0e04050c04091b200c1005120a0507020c040b040b040e030a0206070e0d0b0705 71
    0x41038820365840e442c50441c18100074000c0503180720b091480c02c003450689400400c0c41000300241000301d146000c58140c501582c02c034044141001c406228040d2203800003410b01e150004a880c0b0b103401c2c020454500c0c28103210744001d851040224500c2c002c40f29120410030780c0a205541003200592404505d01c581c240100006000c042003032040a0a19491003401d45030302a00080c040d8410030188007801c0c40d6885e294401d581c0c942801008091b10600588a106070308024a810504060800405040000051040d15861882080640c84001a05100b4940011054041840d80c400780114031440c42490040040840c01c844129540e040403686803110980403101040000c110810081e100c00780303150b0700000c111390401c0645000f2100a54400d680445140203580e1524140099200c54004031010390010348144094116003d21603920b40c804e241844c0180141e101040105200300d1490695400003041901900303c692500080850068541e0051040420190040c00c1080602 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 763970170 1250 763968920 763968937
    0x18160c05011a01121a120a1502220323070306090b04061a010e060a02030c010603050d0215010b041401030207060f0501030c050a030f08030907080703080405010210051326 75
    0x103007000800040013400c42d100404c402c0701440c3c10158284010b0780d943c245c00000d410100e0704d0070310701ea40c0038100b00d090007180e25010340440c211102607188203541e0740050030082404505c10140b011005508241d2451600005201e6800e4100300b070580c14122a8011103004c00d0406c2c0e5003043c3c0d0741c2d070351076081b10084e58040342e02400d600c1c204814402ea501c40c86402644203441d4040007160311000034922030b080d400719480780f8800318140f07000310300c00c0080e01c8030fa030032100c000c028041d00e0307040c500d80d1000500d00240041c400c006594108841d840e5500d812a80400d0344103044c42d0602d4070459680c1c8003031480e1410141c0c20301132040491401d019040f108500c41030001035130750460030180500c0d461500040d01910407500100300003031400300e05001194100303400e00d40b00e4035070038070311820003105500a900c103100d800b40100600c01404020400c8440c260201c455041c101d81d00e5005485c0c04440e07803d04110040d035038030081401d42908603c02010480c001d2046280750030b4240742038004941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 763971420 1250 763970170 763970201
    0x2071a0906070c0905100503210c0a0809031b0d060903031e0902090711120d1404081b1209010c0627110f1c1703010b09090618160c0501 60
    0xc00013813403540300d560380050415040b40070071400e2801103950f440400c013030210f40d1482c100520201440c0d410569810040300d00659610940c0b42c01d0141c001d03000107191034070034055118066a2040050803011740d62030090100d003914440c945829008010649041c1c09154580c884400940c44130b080f404803010640c1c5000440c00d01c28014403202c0e0720000c107000c05101c40d0404003c10380000041207034182ca080b42120769120f601c151110040c11021519244064000e0107010812581d440039040a50b02d8400b80411103100d0032460365640c41c80d04a10300d0b2200100201070704c0e0751107003101d6400e440c02444046091700030101110282000c4094400d14000344500c034001308000d200c1d0f039126840c000c950f08044502d402000a0070100d4540d10954000301041d400c804214505146009141208101d19201d40c0e41d031071024443d80c08921450310900148002440e645094070400c4000802039106d019070b42d07210206290821000503203c4140107070035403808006042401020018002a007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 763972670 1250 763971420 763971443
    0x1140a0302190819090c180e03040608060102061005010804150b0a0b0d0f021c150b03041101110d0f1119060c0e010507050a02150f0a080103031e02071a090607 70
    0xb0b0007109005030304d886180181881c00500120311142d000000340c2e0500c0c10a206401110603040c8014100402c80b00050300000c100094440d07004908035120368001e07002d072101170791224134000c248401806454007186041d404180410710b8500d90f2101c00340b108100180040b030301000100c0c5580d0681c4100081e12000403540d518081500490010304010323081503060650840c0f074640080c60441444550a540c3d1405403502c030880f045607001007042c01c3c18103541e802c181c20035194644002e0304040c04184c03a06116012900c000504482401d110b9a860030b04080046084640c424072603003802c42c600c122140d03103034105c1d10030080c0b0903903910a5000080c1c540c85c40001804009520b0365442c1408820b001c1640400c2c00401e5030302482e5811a0300d664a62524102d0300030714084c1441c80e804200001c81c0285803a078100072164141d0307000b511075580d4440000042e80881900701007030790060f00000020131100d802c0007040d4144140060503c2d00b08000c100204105400c858000d680e0011905c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 763973920 1250 763972670 763972681
    0x7021c020a08030a1b03090f03060204031a04050a02041a220f020f0d02030a11030c13080d020c040e0a0501020c030a0e010e0a1202041d0109061a01140a03021908 71
    0x280741d001c0003000188051414a4a540c1018002c00300380b0341110b420001c589490340070144242180e00151003035120607018243c072818000002d402c0741c04101e82007011010071800209409a4191240c6d41c0000201600403c40d07003400301070299040083c6908081042c860515515034200c42d40300410902d481448109031140e040c1a104071910080ca141d00c1000700442000800c81184c0903042c417000d0160f581d0700c0781000f0100505504007110418030010043c80041a0341d180200b1003410341d4184010362584481e07000e03848840201d25540544c2c40b0310000c4100f8100b80d00203680040c08001590b820140769200c0c03d0030b90b4081003004c1c03181d800005642500c660004040300c0750300f000f80780400482c0c052601180703c16440e8010406c0300d406003200942155101c0e001120100c00324040010240031041d4024040c040020044030aa41045850002034441c40d01c0038540410503035035032815525949030100c00740c1c03041d4001740405408205498000c1c50001081801b10071594900301c1e645041f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 763975170 1250 763973920 763973929
    0x30b030c1f091203080403080903092e03060b0301050d020d02060d0b1008060d03030b041d100b010e1003050903190905130203040c1401020102040801141012120e040207021c02 77
    0x181c0c20051580d52a0704640010179800340705280c0c13095050800c1070b41a12a40002c40ca0b50081c1c1200b5075002c40034107151001070010f03015041404030202c40c02101a0310104041d4203440340d0307000352020798905000410003840e014840081090001d0711800032642c698010500c00c1d405220042e04075503c54080c4c0300c0d141443c8005003c02095440d20742c1a60400e0302c00550005851400039042607103400908a80b55070f03d5100d10070a0f207203288032070040003480000d1901c0b068501011a51986061860cd00340d5004008100d040c506c02418020f11100d1118240c0c02000054201c495511050201412040368900f2800c0c41c8449502c6a024040c9031804100800251003c1d10041c540140140070004503461500800c2c3c1d00b090189074520b60000700100e00a000700c2e4812000d81d03003441402e07501c1c1c100300349045025801c268000c00c0c0c9541c59510b00c01404039000e80050000791103215140c0b80034400c05000030020300040c80075140032880d0f000182152204140c084040c40d000c509001180740 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 763976420 1250 763975170 763975187
    0x90f0b03060a051e0907030b031c030c050a020a08130e0406090620070204472b03140a0509030d020106060c030c0c09020f070309050a0e0106030b030c1f 67
    0x202200d03075101d101c2c803508001c40a400130a00c980d010b03000c0c02c0c021a501c46d001ea00400141c660250403200030600f0980304c1d649200807400c400000c01c0c5040c01c4091030700d224074112102c001d002d4008040094aaa4075148c0302e5100748000303860504803c40215a140017800418001e6004520100b091001c9003032030350444843e61054402c60001c4d801c0c001d0401d5222003918550754040b10002000021680aa150f440700d0200c03001515001100340c214020300f00e904040d0404601c0d1114911128920510020440c5041060034040e074a032070a07001d491007546140c424501c0307403400c0d0010001019080c00142c000d5000351020030b00114117034565041c20060704007a410244000d03ca0180b61610240040c080c8050103001c2020a001e400c00380400300316104014012007408654401c1c07016600e500c01c0c2c000c40800c42c000345c00103600090301d190101c19041696000358902c079841e480c0c8001900240300d05243c060701030283c526095000d5568030040701c034445252108801c2c071200140001c1000d030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 763977670 1250 763976420 763976429
    0x30406020d0612050f0705010e10022803030b030601050a03170c030403060c030c081b0a0c050609060403110609030a05030a0b0909030418062d0806010605040f090c020604080901090f0b03060a 84
    0x606c074220421680e0381c00b107040003106038196401d42125000e41030803410000340c03840b40410321250404080280c211500700b4101d035030080d9010813140b030054080517190700d828410700794808424213007400807500050380b80d4140290503400c00d03d0a9595078099040d904581c1c01611115a6144000112a09400f074518102070328503001d8a5840e2a11800f5211410b03810703002c001d02d002084c034514941c09090760207842d40d040300c120b4609140108100e660f80b80101c0c0d003200011418003010210401c002082400744c0d0050002d50306000344007504403001d0b0002400c012802d601c500780000f10b03888440c0418000d49510000c3c507540c6040c9020f032040012030041c03801c041860b24404224000b0320140105050980d2103c4040d40e105a60909080c000f1035048210103020742b500008050303412000400c201d85000941000b19950380d5000d9085894a201540140c0c10880c0010005041d090050007404414101050380f103440c0c8084002c2610700380c100d1180013070000144030180c90892904030061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 763978920 1250 763977670 763977673
    0x2060a09121a0109020a0f140409181403070b0106230309011a0315010905100510020309090709120f0204110a0806030c0907020d1d13051e1506030406020d0612050f 72
    0x182c26008010010811f1380c07100303000c20110804580c0c5511880c005c8800401c05503c3c2884085030100f001d40159000380c0d4102e4110701110b0942c1c40c618004030a4032449034004050f0035850707103020401c0e00c07400d407507191b18101c10332100401024088c040c4083e5000303180400c00080e030282d80160481131401407905240c825130142000888441d007410f132281c10f4440c80c000c08600c903101d03490301d03400345a0b42e41c0055500c00031a0440700d12032903000000d40300d0400300325104681511011010782d11080c6c2e0b0301074405980c4407801d000010400e5140c51034205407001d040010101d110900041040e00551808800520401c09205051400b009804400c1ca8100d480000310b0a01040295031203103502d03040d4050003505600d1144408020304082c61442c2d000e03141c1c5144c000980030f2900244002c0f2000790f88003040344140c0e402280c840c6402e9204044940c1c449800310401030412415810003401161090f800700840c40b444141c0d070003920000c1064154400446c44d840c030301182049c1e448140e44189 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 763980170 1250 763978920 763978927
    0x5010207050d11120a03050c0705040212040206090f13140a02130e04060b0301090602030402130b01081b04050a0e060109080c0f060c01090f11181302060a09121a010902 74
    0x1d075689450004015a1240b4141c401c1055980402c0314140b40e80007110a50140406413024036030440700420880f2401c409640c0b040c0c2c0c8500c2004203e00807608005444a003080c009030050034a440240340015000f00b10100d50980340000a41c0c5a1492903202c422585410516241502e01c0c1d94a6800c0054410190b06001681c2400c41a04a2920880c1d003225074030008a820300400e07074016030300080042c00034484a161380c14480041d600650b0200c1c0140c00719100f0150342d80c0248241540e21405030f641c0d070403648a842c4000c00380d441c1d0f0b4294495542080000003030380d40c0c55046d01002858003c0316107200703182010000d07040c48520341c401415038000c0d014003800c66441d02084181140201e610b2521a010303245034a00601f00ea000c000c01f018200000340c003e00c480b0801d4039030500070880300003843c0f42030344202c902454019100140041c565010b84401490124003628190006160404050b5a502524070314584040390954551542d1031645800d41852020540508900c8105500e07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 763981420 1250 763980170 763980179
    0xe0d031803180f24110601050103050613020304140c0315060d0609080d0905210d051806010b0d05060108060303070b040c0b0703090e0718170a060c03020702090105010207 75
    0x24900c94088010104540c01e8029007401c44006240d9002e003c1844881c5030340c913161424180a54080c8a0038000c1c0700c8504103d10440d803096555141c42c510000140825074a8400198068000900701d9070380300e05040c003a5880c1c1c1c1c0c41803025501c92401000c0740170403024002440d908112003042c145010b0f4104e1110700240d00300c04141c25070015000e4070030300411189400e00f40d0040080c480014094440001e5040040301507801c0020b49a0040c4141d40c0c07444854004035404903060f174060040d80c24148031030340e40c50000741d02c00f50307000040001201201c000410410300b0f060003604480028800841c040024003060711900307070300c00300a0030218480c2c10444001790f0340c1e0158140c014414180b440000e0100b142020302c2d6401032000c800c007180c607815149805881c0405500a46c03e6500c407640024078091303c40e242c000b0010300217506801c0018107015a40352422141525403100388220301440e40000c45600c50303240030600c150340060f20366249204005004006034800d60440d44250002d11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 763982670 1250 763981420 763981451
    0xe0a030903200306070c0206120f040b0a15060c050c0a1d010506090a090504030903120507060e0c0609010f0215070302120618130309080f0a0b010b1602040b0409060f0e0d03 76
    0x5e81011050a04092100e541c3c40001d020340f164040b0000d007518071000307004000b000080c643d401203125000c1a13400d981d42d5415041118201c800040e1240c02c120007c22083e8024080001c1060044081e41c01070005000807507107641140e801a90071a840b160b02040000c00c8407051400b4000c02c68003903151500c110005010040d05008056102d9503a0020404060041c503070b00c8010346e803241d44640c0405a14802400d039801200013650124249140801301e000e000c5005695610020591400c0440d501c2c01150705410303000c296000e40c415001007609000310f06d200b05204025603a00580e0f2900c284550080000c005842d040c022110480c11660280d021644554001005982c0c108420000d0400701e03152906603008d6a840e003d8242d09684d06c3d0350103e103203000710f4020141a140d59903100000c101c0c40c07082002904580d507841071124010316254102c020041d100030700205c0c0103107145d1501c034225441d2405807284141d0b580208008200248680301c0d6104003410208800e048424964 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 763983920 1250 763982670 763982683
    0x9090818060c1005091014070503040f15020403120807020a0b060609090109050f070207030b13030e131407020a080315061b010c090f080d030e010e0a0309032003 71
    0x3003140d84900c1081040c1d0301ea06081d141401c8241085a100341d210b000300000512040d2000010382c0110104600000d025011b6a5003030100ca441451542e034844400702c0c2c1540000d0411030700d403158204a003010070b00d1200121001c03901000c0040e9520300e1403a200c48903d822078090014400084104206960049400000c2075000f000c00012a0345100c000341c1c0c0380c460410490703070140c8140c0020440c1c0b4016403190f840707186034400d108107a8843c15000c0e40c0e500454030009020184040c000343e88408030a80c3c004c3d41c680300b1706019600400340c3d00081c1c0b068a05800039240c450307075000c003180c941c05900241c0383c0024503800a003a0980c0c0e15141c0107103910004103100038000702d00d50f603140305031501c00c211804900344039140d280007100d0b9a84213028025450a140c0001d04030071004c0b840c0080440b0060440d040c220042165102d4120141e02600900002160075542d40c440a040a1428824800302038820366808d81c6650852401503a000b0544800c2820134072100510112500c0001d1207 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 763985170 1250 763983920 763983937
    0x10f05031302280f0806090a0305132408071b02010c0f0f08040f08060606030f0615190801080f0a0311070f0e090c01170711030d05040c060207090908 66
    0x142601807100d00129041c0c0700d09a840308000410040600c9202004500c01d0090724040c101e01060556520b1030340d681c811082e6035028443d00042d14000002e07014000401c8688010764081580940d580d40801c0c02c2c004a40000e80008102540c070701c0056400460950301501c05c0c10b0078031060f010044c04900b0f108803040c0003410300584003010418064100301c400103035035120740303000402030803031502000c90b03000f520850f1010000103038082100e10010904034890303d07000d41038605582e42c000c210341c55030034060030851700b0082d0140184001100e103c010206882e01c04070000720325a501c20020700c4440c2c141c0c400100c40e04200e80d2140143c4011503040c854942601e132148014404040c00b5080014503071100c1a0340034050300004200d40000043c2d0b12650949058501e810172400041d1a0010034804403c00300c054017002a1034603000304104161520110212410048190f11030801c4a200ba00c4c2074a8040000c1002c101c003e9040141b017026200d241741c00e014805075945c6181c00c81c0505e101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 763986420 1250 763985170 763985191
    0x150e1005250f0f15150612060f08031905030f0606030c1209300a050c15070306031403162301090f05010e071203050a120f0f0507030b0a0b03180a060614010f0503 71
    0xe0000341c07103189420030f4018027141d1155842300ca684085150ba282c0c020b00c044402c03904a0410385034118011400e4903c5260791807981000760742c45100f0040250310040c507800ea42030040c031414008461450300d091240c0d0b020801809034214840d00d4034044120381803805c401405040b401201405150f080c2c4100f05040e00b4442c0d1503584940b615424031036080d245d41d20282c5544100840c856040e040f003800c5a0060000d000c00d94030018890b503c9200d050500340d040c041d220129400110740480c4418a4420b1301c1e5044810441c0c000300908bd14010503050364444091110002400028850302649100340001401e20310314000c106260b0300c9100201406010001c0380c17600f126800741c0071740f850415080008011342419485114014101e182118540c18030708400940102e00910540200b50001021131218034503009949802340d2006100700d9001d02001c1e441950300a0801181408030303c21500032442c6410400e855a1140381d89917910304000fa1804101c4c41c45410604481c0c10901046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 763987670 1250 763986420 763986437
    0x13151a070c0e0c0714070e070512060f0118030605040c060f080f040302160801020304120906050d02090604050d05030c060a092a0f150e1005250f0f151506 68
    0xc1408000d00132080e0181050003001100a41020302090039001e4034003102d45028944c80d41042120140541c1d49188007252542c0046039581c540070818690800701450301c2e403003584145805c00303a420701c9d40e807044030501c0d11507080c03204211034542440c0180000c0c2c5003070644d551450f03500501c3c4100180030388141c1e81c412008901454401d0005003107882d00200010089a035654045000798400c8405590000c0041c5500920b07501c5101a082111469680e8504004104024078000d510202c20107070f12a8080000040980b500303900e280c00759004201854480f14200c13051420420001d00e902c100b2464030b10080d0000300034032080d031444d001a80d601144590054035016074070105800000c503903400780d0800600300619004500f4021425941c50000c03450010a01c14400b01c6041c40e140496401c0c0008030303038001e40554070007400d009480701c40500c403016181d1300c0040401180545110030801a010184241280f03407007408021084108000403110401d0f000103000e03401800304000507903 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 763988920 1250 763987670 763987681
    0x10e09010b06160b0f06010905041d01090c08100902011b051e0f190f030825080403170415020f09030f0604020f060408030306060913151a070c0e 64
    0x941c88240249070180000e5650710700c020f40f0350355002c00711204641d60115400014108402120014001c201c10385448003501d041904100103403495081c50100300e805500b081c602c6150074004d8005040c02030000782c501a0802c0c0c14203061110800c20030004504207402980140d81c40300c58410301c091146d0f9105d0b00f16000b45407090600210300e03012209001042180e0b1519170011507408102c5006108403000745007a0020304882e0302d02044041c1100090364580c2001c40c1c02005502e43c08072541d5170354440001c00340301d5010031315a104096400507400304100300130590480c030000c001010115040c1c18625255890204070a40000040b14243c0c000c40e4079040c1c4081c91041e030b40f00d610010309a9144d480c0030324103140d81b040c0c02c0320183d00c1801d845010a0017802c25804540c02d0f00c0126001d1480c41d540c4405021550784295080f9402508100d0b81e10168101441407100c00034504603014041d9250a84071070303940c1540004249075403010010807000825007a107020803109000c54040d15030380c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 763990170 1250 763988920 763988923
    0xb0f040909170a1110060509131a010303050a02010507090b0a270905040b0f1317041d09011d15060f1012050c03060a03030c050708010c050a090e0906010e09 69
    0xb5510355100e41c0e400480c1810703205401c01001e492500301c032000c41e0303184080d1790780c04070554586101d5650003002580200300c512420100108145006040c401490f04402c2981060101c0036030041d0000b03031000c100141d0503942030251642004651034070381c5485081c0f601103100c1d40b00351100d14080c010f8240092000c42c015480186101341940b0600240580d112b0890003c2e181c100c3c1c04a4245a21000040c0420f140c452070714000c402950580021340701e580d4801c60500194644202902401d100000d105c2c11180084001011800d600d41342c14100031b94050300303440f0708201786224008641c02d904540100082c074043c04c640d45100108003520b500000c0707030302c401e154a508e50300301e040c030101c140f80650010204070003040210000c000c6540c071000001980d00094840b903a0054221104002003449030084d401c1c0d00d802501a030356582c0e907801c401821280300d141c100011880c0480e24400c4590800200c000038011420259100c2c5400140962549014040c4804004030b420118200110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 763991420 1250 763990170 763990193
    0x60909020319110a0e190b0d020d0911010f1e051c020c0105070f0801050a0504050a0b0316050307060c21120c23120f0a181b0b0f040909 60
    0x2c00b00200710320034100e8001e044a40c400e0b030101c0c0106039809000c00c05030130140781400c800c0c0d00903894040060f040000b80e05c01a07100450f4205459001c0c850100302c0c1e00c039807090283c110701c200f86048400310307801d0000d840c200d000d64013803090000c80000d454030580b00080b202d0340d10b0114034020b030303493b4403009124034181d1800021042482c40490205030800c815802180140006c0d1550301410f5900182100ca2040c04d01503150440ea50010421090410380c03c619000f68940401084400c00c3c82c001c030780b030406803082828104900700300402c8581000d012802c00781c511450300941c0602e1544135032008144800450701d400301c40e0f080c0500342c0703403260b160095415038070740b400d106a40c10318000070304680f00302c2e481a0ba820600200d40700140c03004412118090810891060140d035009801d10700c03050003d1039070781840d480d5828100d4800c030302d01040c0010780c400d203109a01c0240f2a450b1241003ca00c1d0414002903208101c0c101c0181c0000040c8c03021540c2c03e51020400c41d0841c03414401c031a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 763992670 1250 763991420 763991461
    0xc0901030917120f010602030d0c2001150b0702030a0f02030a0203100209090a0204150c03090f1d180a240608030c010b0306070c060b0a050a1503050f010609090203 72
    0x100000e50364150721142c0320050403d111028191001603e0b14002000280400e10411015a20800c0076000255007608082c911240030306241044000790b0b0b0304800c50807241c1954800c40e95681e06000441021030f141c5001510000700500c0c105200c0398042651400f0348072000c1c0071041c626a0a00c115a410051040415409401d03038a00b090f50f849103601941109855500c5060301c0381c000ba95464103442602d04540300481801c2c1003501002d41a101203041e200c041d001c01003003003008140c4140b03221540000b402c1455081d8400383e0564007402c4000d0300600000120000c1c40000600121f00281c00490340350003258015666a62011612044ca20200382c12005800c0480000d5079140100c0900b8400004c100244a981509000c00d5200e0200315030500116801045070000714540c0e84c4803042100010300400308050700c500004859400310f901264400041d280e0366030820742e05008036500149a400002d44c03d505042000d000d5044a018401807194003200181c0c504111048164285 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 763993920 1250 763992670 763992683
    0x402040609111207020d080415061e031707080f030a091b08100c0503072a0501050709080601060c020f03030d0e0f0d08090a060e0f1002071e05060c09010309 69
    0x1d815000242c1d08580020545502c14806600003800750b500104d00e0f5a50041c684c0d0380c031117569441e81d48001641654203c4095402d6440300046120f009840e9410508921607044181081c550718049500122503010324201100510564000a0030030741602c0180754254180c0791207030344011000c4002d180d0000040c000250001341c2211000d42c04000e4070a89015206488138004684001e405603102010140006502000090304a61140c064510030360083e102d982c0b0200403070900c516485280010550b4503940d61800d0100d0b440e080b841980050003810040c2031a07601d000009804490030714400380c01050394030300318034059409200303d49079071507803003003c101c10a5200c0540c0d5a542440ca00c11070940700d4001150840c50180c88084c3c410b400c03006c0284070f902a00c0c1e0b100c002a215421021b582c903c100032a10010110611001c00c0e0340300e12000060b00c4103000d050806140c00c040c1c4020920031070300f41803200861f001085460f841003009059079a54130540c40120000c180010f0b014244 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 763995170 1250 763993920 763993931
    0x180b0f0603061311070209091c03232403120319021207120f0216150905030412031b0b061203130618050910060810050603070201020d320402040609 65
    0xc1c0c0591380142441ca40240d486e80c005a4403403105595482c059002891311040441388021128842d412031103003481075981d40b8145200c070b650803078182141503512914a4620031000d070181c200c680101000100118000c007400a9841d200d48a00e200c0540302941030f0280c0c06d200800d4401d03d8044440c40c2c1010110021103280000008007a14106804001240c0c2842d10280380c0400310700035540c0e4250400700d2080e0594003582c4a82e000b030102025401a240c4618115011aa0600182000b4440c441703501c0c5c0300304030031701d801031044c114071410141440b015000000031a02511103181c4c0540252115040c821240000a24501400f2840e5083c08580c0c0000300d11150b20141c401c460300300031341c084500c072501c400800110003021a407220540d01c80381410003113148542d0703000d600194038030180302e1400c0d2114049982c0360f00446039480940e400184d00310120304d40d84610015802e49907203401003400039203002d4030300241410403201c20b1000c81020034295601e0ba0f206a0041c0180b8404114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 763996420 1250 763995170 763995191
    0x302100807021002090f010503040f0602041e1d0c03090a0c080d03110c03090d0c050d0f02011d0310020706021c0b0319050a020103021602090c0301180b0f06030613 72
    0x800d60084078108018040c2c400d114800200c18000c0c0c8809200c02000681c212580000446450f00020300c181ca1116880c0800c0010a0311403000300040d0054454000002400000620300da60700b03603000007420032600090110050000700c0b840d402401c54607501d03580e61210a2003900e804c2c00480050900a001200022001c0000455016004c11906d09020810842c600c4082c10301881c545108907800412400304145441d020400310070f441f0384106401243c492012580030780450508980c1f048000f0742c242d00f0343d030708407200403a407100448802d003103d803824010a480b000142110b401043d00412218100401a0103846020740003031054407000c201c441c0160301a02c04411400d000e40a00031909503000c541c00c0004000c4da401074020100240300d5401103000798003403c1105c038550400b161020040e95078100c1e0602803026204955201c0d4104201c0d03441d00b141c00580c03110f8841c40c3c0000042a601c600b400701552807421500c9a441c1e41e10322003c41c0001401e54062890786251050303051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 763997670 1250 763996420 763996427
    0x612070e01090f09020609090721051503010b0a03080a141210120b071409041e0614030c0603070306240f090e180304080f0f01050601022a0a030210 65
    0x10704807805a03905100741c120070b00e80c80d801c0307a64000010350080c00400002c050390500e8244a50080c2140c0307044400c011168500c007014107050300c5a40111074458080c061080b02501e20102c1c0031908030020006144c0c8000000d800315010312009001540100f85c00701c0b030a000d1000c8851340c4520071a81961120894145401034400b03c4441141800a10340422007032640c2842c4184103522180300503145c0c8980006403000703111151070a03e8030004001444e01e0343c94074014013400480f8031814081d09036400d1424004c1c0c0b8015009000c4480d8050030f4485640d40004540403803010640314903540b611804002c80140c00c0d1500400d001c0080a0076214021042d0010300710342c440b490f99101c8200d05100c0040328031040d18031030018502882800b01d00c94078400052420412038550407a4070b010b0b0b59840302400c060201c0c006041300d070004550440d14000c28000d540d880700c2c00b440580001035020420140b0311028041540001803407201c0482143c6034030381c2600246400070002d9884070701412004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 763998920 1250 763997670 763997699
    0x318050f09072c1f17040c0504020406020a1703100608060d020a080d030e010c050307050d091b03050c0f0904081605060a1d0109050d0c030309080d02040f0b0c15061207 74
    0x7902074500d4489100328645080018030082c101c9a4501c105c05050099410100c400a042520840314210001640369200d2000b413008107250340140030b80c1031701c90801c441402088402d905900d0303410403c002034081600448070507503000e402c16031101c0e2101c40c0800c8060a20700341c002d410048407d40400c06900c0044c40c14180c0a807540e00f07100b20f0100300d84507800c1e641140b0501020860a00c046100e0303034019405044108040400007503408800d4403030001c4400640e90609000104550500900105000c00c40d5031103c15140040180010004502e44c3c0f800100060045107000c14400090300ba1500310044d042c0d0007004035442070070f040c07031850020110084a400c112400e020b050103030400601135440075507000f60113024030040c00817060b6044182070604408042c3d0340d204803400290503030060100381021100c0181c4441c10004001c018a540707810031580b041084c40f181c2c1a807200000c0481c412503162499400540718500410100085031080e0039480c0a04480420a1041c1c500b60 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764000170 1250 763998920 763999007
    0x604151a0415110a0f02120607051e030408030105210a1113150b0f090303071127012619020102120a050f0306031609090318050f0907 59
    0x100b51014418841c1030b2800000702c1a1980d040d0000340302003020542c0386801d940882c1c0003824402d403080c1d000c0c2481d81003c1045621002250740461380c544d483c0e030007000c0080390b046a005000d05d142810346501e1554041481780c103100c1d12912000221419a010176075009098503800ca96610309149031031243c1201a09a00303024075480c82e020881c2c51028001d62109941d04400c0c62001402d003e508200d0b5030000849880384101080401c2c0e00c3c2e20200020000203010340907130640c00c0461010014074a04400786495100589400131508590f0981c0380c80c11580c00e190003100c03610f045920139071143c1c2c54002002090041ca030919058103050804004124801d03400e0360000e005032a01d081846c00b42c00440710005009105030070302140680c0003150454001001c50f2000040f060030815401015003024240c0360710b40b00c00c0403c041e0803500c072490b0740b400c4250410780c0343c1c03c040125140804910060b489031001802180c0528052100e04035009151003402100a40d082c0d6268842c084102c05e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764001420 1250 764000170 764000189
    0x70806040b0f010e010c0204200310080f120d09060903050306030d030e28080703020a050106090204060e0103090c0b130311090903030f090c03010f05070e0a0302090604151a04 77
    0x1034070072840c9881c90b01641500d105849074680b1200c1c91340111000400c0d0f1070202d07002507a032940d00d0407076582091100286206042c00c03a68900d0040381031030401207075034483c05080e44080c40c240c1107228040f0ba502c0ca400410790740140c4030f00601c0d807000042c009a82c005400355251a80140605a002c0b0041d172050740c0580c11101a0354010300b04404980c006242094140c0210301d4000c445640c24846c444000c620440101030000a0f4590031910b6212640c03c801581c0181c040201f040400c1c007601d8001c0100c40401c6042601d454005001d5001c1c032000c5504040e179548941040240010326000501418a022901c9030415410301c265001d960000b43c40f11444c40c01840d00d00d02e0004041481414107c4c0614219150049030000c1c0c0360010340520064001c0842500c0d09880900c2011700b0752500306004616030503d040302502d86244070b1a00380c00b803e2032080520158880c498243d42010b0107030740001e00d00c1c180c01c103030245451450304105a03c0104c180711080004125028009885200c0d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764002670 1250 764001420 764001431
    0x3021603031b06021b0105180606090406090816080d0e061b070f0b0a060311090f070e0f0402210601110a1e05160f060c0804090b0105040e07080604 65
    0x21a1404105092000a0004011000380501061000d049400302c51250b1405400c0910b0728004400d4403a00c002c200344142c3d960300401052030440c90001c00045030308070241641d42040e001040c4402c6000340b01401c00b9480320801c0341000f102200300c07400201503c9078000342128138500382201c1c2d400b481b215014142000d94840c205400414601d0041d0300e8152a81c2c0414401c0c58400d00c150000081940e45c69066420b003800b090006013643e104408031207000582c2e60451524040c041441c014181c010503800d01000721820b90784501c982c000c0b607142004880901c100000504480600b03410540160012618902e582424070003840c00000000e10020161340d16401103403800e0003001c540b00c15a002400c002c0100d2011003244c1e0212400352648000708045440746071030034140f20441840000b0000d230030003554030410b0310714028208a2401c0b203100c1010b500d45040314040c6000c1c0110f21561000c908030140c0c080c0c02110002c0c01c1503540d0350440d00d000c40c801740103140700719101d0303002d50b0924 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764003920 1250 764002670 764002693
    0x20190c0509360a1203021309020301080616080a0518120304060606020a1203020702061201030f020f030d1d0d12120b04090b0a051e011217030709050d2103090302 71
    0x12401c80c1d40010502c01004103215548400c61381040c0711250b041819800c002c030b80b40c8982e0203800b0402404030340344090390b2940f4040c0001e24001004202390800c18045042111055201003c55089402202c0104064481c00800d9006c02074401d58284148200041c0851103001c803800355104174000c490800c0700558034074082c1e8407000e504000600011080604160450199000d07048890018121700d007040c2c01183c44800f0210f0030780090307941819106a0b4021880d24183d440d141560a07000707008505501100981444072007407400707204000788005e5250030f032940b0800750710154000200d614005036900014040c1403190450703001c894200024840c07a4103003802030000c60340c0e01074121030702c03036070780341c18801c003c2070081e00c02e00384071f41c0c008111203c1801c0002c0103400f078444501018003203000c5242c9045040c4041d607800104040500030401103541017203c0404491080d02c01c510440d019241000c0b600b0b40360700440c14110716095910f00401e6140e40800d42c0c451081d0225030b48810300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764005170 1250 764003920 764004001
    0x50609060108060c1b0106090b03010c14190c0501110316080f040b180d0f17060f041d030c0d11011b0f12051620190c0509 54
    0xb4054038040303074401d40c042203a4020442c000c2071550f0300c00e821180400007200a050a445c40c0e03901032070110f03484003450002d0746401c1c4035001703c408240c101540340c070b400710144412601880701040d00000c100c0f00041c5038180944040e590300341d4400000c0044102420302100b040c1c0080d103013051400c0c85841880e000342c1c040c0529074010101c1c641d1080d0340742d40d01d954020034510002c1442e10440081000c04c8082c000400aa01070041e1503102d41504401009004256011404400710801400010b21040ba03e8000e02d00d074060f1001c0d60042000c0302c840204100c00303003014603081840d21001608190302c0074040780030351208102e40e882e86805100e0394015400d0722038402040c032034400480307503010065006683c0b141c030b054102e0410351294446e0012041c00c5480031a80307d50411007005198040c1540240009165201c80500071070001750801c0a90f55541d10a042801c40303c2180d003e0020b000210079003500401d0b00a202e252070785082c1c05100c1da2105e0700d45070031158510701c44015010409 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764006420 1250 764005170 764005183
    0x804030620090907030605031e010b01051e03040501020f12040b011208030601081f030503031f030b040f0f0209040609120801230a0b161502070c030209090f070909050609 75
    0x300480460416641004001842038080c0010b130500d5a00c940c0080d07184c80500c91041010355407060b210142100aa100f401d440d299404141004010401e01c00d2514020054911030f4800c4640c02d91a070b51a483c040e4028811030500003e4500f0100e50302c00c154103c045a94880c0744100c800001d6a41e0702d0448104c22904030100811060003032000481d42c0d4450311009038800c00500e415280c040720115103c101e02e0b101e030070640c0d03690030001c1045401c2d4100d5103038444160208260304006450344d20740742c603400009040100012860b02d5003005102255118050f0250000c0600e14981080e01d0000c0040111740000c444802c5801071516a050203141e0207412108054100700c030f40400c9100401440d06e1064146034020031405001c144009048040c080301902a03803d1601001641032550010304c000758201d52a50040000000143c00394803110300f281c2d0305803003201b4242c844900b000d00348010100501d489104001e400600c1000a0701300c909401c2c0500d007540c90300d40b1a044015110017 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764007670 1250 764006420 764006471
    0x40b0c010f153209040609140d030515090403110a1a04052415010215090a02280b0703120f06061205011508181603060c0305070c170705010908040306 66
    0x12400b9110b0035821300c9218036034480e104060025128182c1c0c0d4484499980c410780d0446241d00516650210940510465401c094070180c00d54120341110300103003940100400c0103081002c140d400304080c4000704400c128442e4880305c5041d48942016860819003803c54050f9034510800b84050a001d00075490f8010091803050007070b406a45505d8201090b5940110755070451190f40d10f8956a150000d006038000c05424024114520070340c01045041881003110341d600c401d084034007081d0b2003091310710038048480a0724881c0d2119240d00313040d140783c664002c010320140c0c108100108006080d0b40300302c1c2078481c56201c1c03000040c6050040c100301c442c24040c18404001c00c41d8010046405142225440019070702c1e01e14403005054696410150b008000c3c5075019440c0e4800d001300201030040740940b0032185400c02c06841c5c4208003d02500ca600d03006040c108107800800088443c460464012640060003400515101d1414402c4c5912510090781e640d45082503420b101c5000d00c0d004000321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764008920 1250 764007670 764007749
    0x20a0f321b220b18130b0718030201030903050c0d09050a0b0a0813020a03021905011205150907091a1b07061211070b07030207020123040b0c010f15 65
    0x48605034244030080424002c850351100c0001304d1080c1880400020342d1080102c0c1c8110907281002e4038000c0f0a091001d00543d05101d0541d00d41000442003078080e0041fa41c0910b00411910710a0900b601d580c4a4009407201501032044620421174000e0f145100304da10548a81d040b103540d0385460b4043d03024403002040010701301c2010a5203420b078000c00e0405140024603425140c1c0d9030380c1c002000c0b0352000204c0e95980004001c01c12003983c102c1d401e99071280884c0c0c801d1007140b03040c854200103004252080307403007503016201007902984202c41d07502c0604aa044884010304000f038075140385820070120055040310304440c0703c3c090000800c0150807980c1b286c4603403c00da4001c101c80e402810321000d41d01918002481310002242e11144580c3c015042e5480050fa58480c03400010000fa1804044030104003612031860803c07048401118101c42000c001c4a4591401c43d0700117001d80034084e4031888080c2014210042402d100160f1021940d0035900300868481104180484168100311900103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764010170 1250 764008920 764008969
    0x7050c030d0b0f0a0e01180506221104090e0c0a0305070b0c0f0303070818120d020f07050a03020607021018080a05090d0c1401020a0f321b 61
    0x200c1007608080b8610200804100070f10302404041103940d00c2c69400303221402506001040001d031040600c0841c050800301c00d214501c3c051010600c62401c0100503001c5200301110010030388003541c0700305480d104448203a65126a07800892000d0b007110003410550b80280d0030003000900c0c100c080381003140da01501070101240761189910703d641000d1211200350249122207c0d14074018402140300d20b009803225051401d0008024510006060840806902ca0316407058400c58850075600c1d800340d1190090382e111a14074041825014105009145100e519050400c25801040c610720400d11a0300f100c8107004a5841034050f43e1062010280100c2e6128940d80421151f00003400c40e50000c0c01d10a180402203800300d101d9180240d8240c0d90313050809424810310502502042d008034003440282203101132a101c501410403140c4004284481c0281e0140d0310300d025022070303100440c44041006030751164550103a12001c50440380880d00307841e902840894075000034181e0149600750181c884 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764011420 1250 764010170 764010187
    0x903070512030d060b03070e060711061812010504140a0308070e1807030617070305070e100b1908060405090309010f0203190201090c050307050619090510110607050c03 74
    0x1d058603202408050004110380c02c00d103110350007503100400c6010452640d0b8900440b008142e041e92501c2c0e903104030010040390010a54000020b0030000c000c5442a58a000d90b8074607100b02400804a00d40005841c0041d080c0c803030065100b02d10030b0b40240d2400003440300354180c803034a41041c020010045034104000c54050f500c509003d04092401521a0581d584d0503815a00c3c400012100640060b80359031080c01082003500246d04942e078010000c1100e035045550ba240c803a03016009408488482c02c00203041c21002d00214001440410080350362030b1070403148100185030002500c0042031020300130a4042c1000d00c03820b0320a00c040006942801250001183c407600c03d07603040011803009103d00c503096100030100302d1000303803c1d400009080800c1d2070400500e52060313010038402c0d046483c080003291031380710032540110505001105955941801600c2150316504a0383d004000c0440321020613806c502007903c01c02503241160381e10307950084100c1c0c1d24810003412101c01c0d00280104c0c1c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764012670 1250 764011420 764011429
    0xd2f0609060f01030c030f020613032003010c02071e0902040803040e01210807030e1c0b1f1715010e180d0e0d03020f030f030f0f06060f2a060702070b09030705 70
    0x7c0e60b0300c0286650f140203140300e00c4041696154106483ca101850b0402c0503400f180804404081c01c00e800074440d0107138140d0040d4a45110b0f10402180d5034240b03d16081c030341ca11413210b20240402c00c01c21500ca40d2620007940d43da800c0782c052001c06851600c00030600e0440d501c0c415200030b201c1c80c2c1c00304201c40300d1ba40d8100560045201203092002c4817510080c80ea87d280841c0040003600c002c00a10900b150400d86405400a41010185209a03e16050180c0002041025588850072042848002c05200c1d840c2489140d00000c140e002d010010829010128034240074800070420968400c21100055848050b140d10079008191015000100303420800c0c410b078140c0b402130064a034240e0005c07000c1825030384001080840742100000b008410300c05404000d03041103142c5204070f0705141c848003107121881100058151001d011400c103440c81c1001c0c000f981c00b02511003808c80c0c003000c03890040c2d03502c050940d140740c090b000300200031558411031416502c401c1c50003801401d042d4030380014007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764013920 1250 764012670 764012693
    0x810050d030c061b081509220804180b0a06081303081b1602030d09080c01200a050a05010b060a140d0207050d09090b10020d2f0609060f01030c03 64
    0x8943c3c45481d50200800328620604501d40d1121a460f035280500c0c0007400740240c100f800391990b114007001c0c0c0502005059003109074056045800c00340159001031300340254107000350b60207110080b145100102d01c600582d00f1502c0100f400351244440d090721290150703810302d4111542c04048807081c4070743c0b0100e0f10884410307400c6019142c41002c11203440c0e80168043e0712101c3c200d00d5590309031040c1c60450404022040140c0a10302d0113a44541c1040c1503d03481e84079180c07519042000c500d43c1c21031004048038414200040713440460b003c3c60041d2a0003a126010642c0594440d4a05045c0d030042e420702c0411140e205105039070f011713140e017490001c190b000e8101503240c0000079406c1c801040010760400c031f86a404004c80d203483d12034501e0030b1000015140012101c501030b0701d840d9100100c103900000e40c0c40001900c0d003412586420200c60020802e403000d52400d01c0108582da908a500c400404d445004007501000d6405581e2018a564400350084c48001e09020304008108085000d84104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764015170 1250 764013920 764013923
    0x13030807141219060305010207150204060504121505010305060601020d3e010204030804090606031109010f020a02032e020c031e120f06040b01110309011103041a0a0810050d030c 78
    0x51070f20314074040c04104a41c0903802c2100d0301da6000600130b00b8810f83d0046001c006050442c15440c1606105004040b4043c501ca41419000c040051408020720005d012a00b442078440402080d1b0303407420400e5446600756142c9001d40030300110520480c0c410441b8411149061614405007450070620700f04010000781c0f51390000d41c0c02c0c50800c0d0000d00c03e0005000441c0911380280d111401e00f103401c421180b00c0c2e4407a030107261500030003c1080b2040390a40c0c24100013420588061803103030509904285006d21f0003903150007480230120910002070640e4649100c03081d5450007090800079404124451401e10500c25842884107008410042e01180f502c414245012824003203400f00501d419501915a52800c0780340004204107410306206000c40b0310002d00c0d00300700c80702c904038401d600c03445003003012410000740103c4214050010021140105064518001410800120001709030003a07408000014640300100700000301d07002803017080d05c2000780820050341095034261950014880c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764016420 1250 764015170 764015191
    0x9040506060f01020f012c0601050102060a020913060b031512061b0f040b1804052a160b10060804050303150d02130507030c05071a06010314130308071412 68
    0x41517076448000e0041c04002c0144041210f0b16103100e076003007414040c0c01c81c00c20560780c0c8420010000da0b81e001517400c0c0c001c1c0d285100180e0301c540c0c11000c20194041c1204010f00c09040080c00500da1904030001d510404841400d002855084001c010b0400c0c1c01e1009500a0f41c80400401c803200e0034071050071400035844171080e14010507206002040e0f04541e00c01c0798003010100303040e1808c1c0144280120805030440302000b0324644644100b0b9003146103c183c024592a030300115202c04c0701c0104640b8818030950001101c1c1816290903100d0180c21500540210a41c80000403520f024603403041c040d55010028500f1541da0b907604440c8004031038000c1e07130300200846260016803207211a032940e114a40c0800300340c48c6001a001380540340caa00300c5400b0028204156000f00c2c060306105522040c08003c1c8171059141c100040700504488080c0f01e40d0402c299043c0b104220b580e441da84032140c441c2d21034410359038a5080a4076051510010001408803c20400000c000d2031858694041d1202c10b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764017670 1250 764016420 764016433
    0x18040b090321250c0b070906021c020c1908100209031005070215040615080715050705010b04020c0703050c01020316060b2d010207050a06090b0708071b060e09040506060f0102 77
    0x200310400030001504010110300706915071320a1080c507203c000d6204005040c0b01c69480d00d0190025562200342d60080500f180c490501c00c4001e20a2143c0010b41000402002d68240d0394009681d0402d554480e0b05201d1041600000008015000381c44804c40001c01426010144000c0d29010b041c009000f50304602a5071b00b109103036052644420702480c0503050010b21100104c2c80c5001c4141c0503000784040d60312001040240160551400c0c50081d101d14045d6211151860320a024005951081d90306c14000f00c1c0704020420b00290341c0003201d0084080f03030400480d0100598491162008400c482540c1000e081c01145168001149955010303007810134030040d4a419928075800c2564041d6a203031745180800481d80d0400104010300002c40700841d8003031911101501110311882540c040c03200104a01050020f2001550131454002100205032848018000d03031540c580e00030a00400c100c848154420300300034001030310450f0300100400498551608001290291180c1c0070704510404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764018920 1250 764017670 764017711
    0x6130302061602130618090c0803070501150e01060816271a09030303072304030602120a05060a140d150606080f190c05070218040b090321 61
    0x1d600601c0000c414400000d2041c800340b0421404070460388400000c039041900074000c001d400c41508040800c400400111040c11349050b03240310050f80e000012900002c1202c106106040d0403603940071071700e00d2a20354a6038a8140f09075200d4420301a010018104a000403c2e404009221502d580030360b050220000c0c1078040d4000500c52140720034000c0c008648001c01c02c81c241800d140e0000c400701c40c4801c0c04e00300404080b81e601e01001b0007940403c048110700081c882403000c000c4180f0700c0300c1030209030350f5510781c10030b00041d51090b0740c0b19801c80b2405000601801c40c5200702401034200400310062545409089590016107081c15640604e821f50400001014020f0b10b040c0c0c07042d502008968140b5096018041110003060301c00e03103070144000c1051030341c08920032945a4650700b00000310040d00c0202101c031030040d0300000750400d40008010912048024000344107601c40c18102e546581c901c4070458803801410001c00091114901e2071099200381807129a00c864014581210070341c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764020170 1250 764018920 764018929
    0x90402070816050d031e0216020307080d08060406031e082101050915060a080c0706020a1707020d21090b280b10210f0e07080d090506130302 62
    0x20034030b1481207018080c4520208072080c0860b00d0040c40d2400c04006051480e40103014011124040503000c40d40095101d82c5480010000104540c010b401c482e071443d1504104e0383e03105240440700000c107025000103080c5141501511065075480078400440f410b0740e68003450580d00c1580308483c00a020b108551189450b9841f00320005180300d001c0c1001d514203828401c60b81405009030305c13a2002641c150289441e040d0460320310325800e1810040b1075503800003056030b6004885000f00718600026221800fa584046100c8001c0000010300c000c0303850300c0760240e03618901c0141c1d00c4045030709079003080513403d00d6101c080e100b09001d0b100410040c0e21699040c16060b8215441142051446000b125004814045c011401030342a410011104000b001034003624a030004082009006c0301280e20b8181101800e52400d0a604070600055240312005000b41c800441d170040c0d144180c0000003140480040d06040c80800ba03100c100c2d9840c104000c2c803406512041c02602c40c00500350000005864 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764021420 1250 764020170 764020177
    0xc010c02090a0f020a021506030c210a0215120721020a03020f0a031e111c2a021203160c05031603171e011403160b030703051e0a020904020708 63
    0x3140e46c0640110360248a40c3c181c092801707451a80294455003801640d42c450b1b8600104803242c00799014802c3c0d420107801d41c0f030503640c41d0f0000c0d0866a481000c1c4015460400508200c905802c89082141d9a046045400d18900f02e0b04450b520006881d0300036140141e8018109000d80f3310f03000d450400c8075202202554042030440000036a00c1c0c51858400a551800e407044a10f90081130001c01c01c00b111000007800b5000784510800c19444d004060742036554021104012200070f03900c1d03d58482e5032010a0319640c00c81c80c0c0090b0144c2d10071200030740b0403001180d1042c117000c41c45140c00f018004040343c9600702903604407031300d1008000d1030031400358020442d903425200b907460143c4822600ba030403031480006800004120303040c00d03d030a40e00080c070441c01d044d02e44417080b61521071a100300281c034003205440283c070045056440480c554040000552043d516030714113214903200c0aa107003070380e4030250031051812903c5402042055095800070110144028005410129541c407030925561 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764022670 1250 764021420 764021437
    0x306030a1415010b071208130b0f0403030608031303061a0a0924150f0509060a0801051c051906020417010b0a0807060207120606030506011805090c010c02090a0f02 72
    0x18004881c022025010302c1c0d40901400b1a42521420081c480d55140140801603900780c040c40600d000040070b07a180c040c6005141030300504c845855007001c00c03c1c003042c400141c0d42600042e00381000403400450001c100c3d00584034995601450307502d035440e00401040030107442e6840005200c69640079a984403182e601038030030210005074000b87c1e45001544c0300c40c00154075608440c450000c110300c04402100b403200d860700c0c1c104941d0245c0880401c44d03007445814a0503a01ca500842d9030703122240e0041c03507141a52020341d00260b801503083c3e0700030b10081c1b044100411503840384e05803021480c0801c00343d00c0c60074491301e0098101921105480b8882501001d81c034581ea5450301c42c5012460701c0400200180f1190000d000c182d1309001000f9142d0345940110400100c2082e080020001107501c000011900700d07043d21351658440c6801608880c00340b00c00c00100303041c07030041140600b010a020710011416101c0250382d2041e50700b44001103e008041c0c154055894054041d010380d140018400d80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764023920 1250 764022670 764022673
    0xc03010f0306020313020433030f031101060504060602070317030928060603030f02100603082203060501090603141b040b0d171308070f14060d060b1e070b0604020306030a14 76
    0x3480240030b19a070700d0442d611050230441d02c102080892a0114801131440c3c0618042980d4805c0d662114094002a481140c119141c0707040010255800b140c81003d5a124061043e5404c1c14180e02507414002911000041d401c040041022a0784c0c1c154003205070300b1203148122420341580c69540445d201d40d441034000c03584064000a50356410b1095100c404980002004102d0450b100c00143c0c1c052898120900f4120b5000a45921211001b0a00550340002c06011f6907842d203078500051300d428030003140c6c0c1c0b190220b22200544c1000c6203014444102e40369240e60019800c1c204030240c8107641000d0340110001030007001003000f0a0030040410100740900780d54000401680c2000f2401c0e500402d080c5c2c101c1da8080c881111000c4409040328029900034607188002c100003842e5126810340b0503440c40c030f03101001445001d49000b42500b0000e0592054901c0500140c0c40802e21490328005e020320f4034140001c01c0c0d8946640610b81120018088a809001c2581d078244003038070320307001d44503207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764025170 1250 764023920 764023961
    0x50901060f0b130302010e0a08031803160803220b0c010e0d0f0c080309031912061208120a060b040b12180a0b1510030902090c03010f03060203130204 66
    0x80c01c01400e11500030b0a000703440da460005041c000c841e12822902000b41002a411030003030711aa1a1032004024150440980b541c9500240f01c0c084042084400e050103802811103141d4425500ca0300e2204032020100a0341c50100008007002d06800d080b03440c0c0c0406010700c200420001100c2001d020b0000f9540c000103004019003c6080c41d20194650041c02c203c00195080c1c0e0b903d5000d5031100b00c165001d6450b50b10703911082260b42c01c0d801070382d20380000380a4403203d007010a50300000302241140180400c001c200e8855841d081007501540300034011500c20045042c4850300f02c0d8206900a00450b40024082c1c1c90b0141030b080c0c0c0e441035000010744000841d262030807c60744c06501d900210245040d2400124520002e501c90400b110301400c0d503504c00e40050307001c1003daa4040358102005143e1081d03100c2d9840c01900a01c80c9000aa006007541d000103041207010408980c1a80d8043c40c03801e40051859031094040c0d44014120108401c60351034032001a1958091395007441c03a4540520407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764026420 1250 764025170 764025179
    0x503191527060605040b030a0311150403080115020319120e030f0a1d010c02090403050702091003260f07050c090f01290d020d180c1503020c100b0d0605090106 70
    0x107a0b00c06030801440350b4504003a60b06c1c2036600040c4824110351500f040840350211441c4903081c8847c41001d001590030101c108020540c0c440d10746030585501c00482400c0750044a03080307940780180503150040031203c040e200503450080d00d040031060218080460340b69100310040741590002d0701c460724081400301d00c641950b48c2001a0b58081d13400f020f20508490036200009000e00c01a100190140c440d500108060510030411580c0d02c0b42c000e41001b2850402003010441c03032401d440241d544100c40c0c19201d403820a424109410074032941c0b1410b0810016180c0d440841e840880119400d02c01e51040d41182e031203814206104440c4c048036068070390b1501c0402540300000501c14201612802e12010141041d0743c00d50b02c1d0040b0300140140c4500c08a4501030013812110500702003030300528058000c0190007401c0c2c100b92800300041601c46411a02e0503010790280207000d0040b608000301c60001c106682c0d119014400000f442c03d45160840d488901c1280d05c02d0b580440d00365141c030303010710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764027670 1250 764026420 764026433
    0x1908070e13062a0f0f02031e0f0f0a120e160e0703150e010323190f05011b120603110928020405030607092303100c0c0203070503191527 60
    0x41c40172803900156140030400600f0741da00440c0181600d03120200410f01401c950ba05100751204040c0c0c92030700320303a10746066001030441912400c0704418942049d184d907a00704c8001c148400c40c60058050359880d14104201c40f4011607000b4003a10070236070b990001054030303d405c00380b1200074141007880ba903403075041d41040e813640e080001101505111551403442c1c0c03807500251a07030b5000c0c0c5102c8000300750451484d080320b114049840282266080036410202031041440104d21407686486403003503030907a180c95205842182c40040c0401001c0714110b0803d0411240d0700f42d0016031449007403003030707000400301014020082c1c04050407503078040703001e000b5810108400c81c0c000c0006d040c621450b525100514100030480c15400c0645040190990001d84080001201100c80070380d05024034480c2d24801080004441020317482407003000380014440c00d02288500780104004c0d80c10000c0351183d00d882c4d04000c445214a840c0c503564001201d551100b49152884801d800305036803500d84036508101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764028776 1106 764027670 764027687
    0x7031202031f1e05090603100c02030a020706030b06030c180406090b15030f0c13050603010e090f16061407021908070e13062a0f 57
    0x1189000c94030300802100441d10120700650386803071012981c05840c41039014401d88940134082414000d0009604c40000380417a60b20410110f00c0740103c41d030041e903040c010307040071030102c80e0030354140218002806940740a014100c0207030009540344c40040d14515000000140e1180e405a120741201c906500041c010040c4035941e01c50480070f00240901c0520070180700d40d5464a000611007030320f00440b00310581c0401a079071001e44030040c4d032026040700006000508000f5041e0b51b01f2004502800300d4201c2c6200e14140300c0d000c1843c1c900b20640e000002d4224450503c0c000030009503200480302c4500e001098a10011101c60683c881d040c806904240342030401409881c0140041040b110410121120696290803c0c5150304040e540c150b0407030410104a0301198607600031103804104c0454070310015040324154031f098401017031300c60045070402011107400c5402c003605 = true := by decide +kernel

theorem cover : BRFrame.Cov 763848920 764028776 := by
  have h0 := BRFrame.cov_init 763848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 763848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 763848920 ≤ n) (h2 : n < 764028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
