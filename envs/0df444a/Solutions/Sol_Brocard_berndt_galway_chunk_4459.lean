-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:41:18.705433+00:00
-- url     : https://prove2.me/submissions/e7040a5b-60f9-4468-9df4-6372c1f8cc2e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801798561 ≤ n < 801978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801799811 1250 801798561 801798589
    0x10509100c151a040b010e100c0501140a090201030e0c1e2422141014030a0b01020609060103080313050102091e030c090105060406030c110f0601080d0e030318 70
    0x10500410f26150030b016020383d041d41c445440740b45444940d002d030750301603a1090f030b100340046c04c6c2c2c01105000400c1512306081c102e8040c3c030b071952181072092600302c0f608030440c826649034000060314051030000604407030205240440350350000d000c1c01c00a6544035940b45401c0d0441c44801e0712810008040355100c4000242c14282d101e00c2c400c0e0401c050008009008400440c00ca501d4030351440b540030401c124554400c90171852b91001e040e04050825100040305a44070741452007182e580b504506409030f10480c1c0380210341c1d5490394138441941c0d0500c50f080c0c1011581004202650541c4c650300414170005d8100c0300c550900e44040401c001003901035030181d08004041010f601011010448010151003595109004000c82d0303015918010301d02c1070680348050103480c18181801810b0380100840f00340e074814001c0500c4a085401001c0041e00000503454001c1e1070030b07514000da180e180100140209003801240c51001882e42c400001391100b10381c102031402446074009002c10761440024070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801801061 1250 801799811 801799853
    0x10f05040b0106110111040b0d02070f0b0117060f0705090a0f0f0311060c06060108060f090c130602072414030f0402010816050d091b0609050a05010509100c 69
    0x30841402050301d0401e0481e101d42d20f6003c20510354024090803680c2084a16954a000340400d000240c07100b40640f1004103c2c5a00616105507601c1c0c004410314210011500202c42c0e50060002030401040410050030040007004281448071714071081c2c450040ca441d04100002c1007945040c2c1e00d44054034010980d42a0301c01600d62603081082203805180000d8540384061800d15140b82841e03c21212010b00e800081d0505854030801112a5907020301415442811441d030300320240e0300d40310407a00862103540c00599891400c0a40240450140d0040065400c01030082201c000b01d519826600b0a03440040d01011040d6282030358100f8080720320101c003100110810918a007620b510303a009a000740c80304202642e800c0f44454100107610141000a1010301481ca1040120b400800a242c03040101180c10400b424000003440480d50100c40006c00c01c410411041c240980340c42c0c0600000c1c6402460028100c011954a00b02100d40c401044260650403051016014901450191400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801802311 1250 801801061 801801071
    0x1106040f09091a070507020f040b22060e01031a0901110c0d08010b1c0b030a17030a140708180a0c09090209100e04030f0c05010612031206060503060d05010f 69
    0xc89001450060002c0b00c44000b450100140d0b14000007050744513045654500b807038203016500f80109a540c0e00708031070b00643c0b00c0d100f070216076030b4003000d4030340902e0391403580f489914200b45c14606549032580815011003000340103001040c1800301945102d0208002e02da1241c84080781343c2c2c010041c008004c44410004150b000c2c1120000c5004040e500fa250b45021440e41c07102c048130388034420782c1d078180503a02000142d000000c180360414103104c0802001c1d0b410700ea40549589807518a00d604070201d000001081082c07040c100c4c40303086207100c08602240b510346080032014002e840060202101c0342008403981121603002c00c100410540c0c0304c0c14030f02e1526a103003180000b520f01403400f240324115140010b190b2100401d061012640d455450142c25201e07a1802d41d640800100407000700000c001d1440e0110740e09024a40c01000d081c22030300141403030b0703087c000d041806020840e440b41b41041c10400030964020261307500842d04075a80c20301440c075882c240d8010400c0191510b8100d00702 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801803561 1250 801802311 801802319
    0x4020f0603252f03090d1a150a0609062c0a080d0e060705280605011d07110c193302190308060f130c0e0f010c1106040f 53
    0x21504280d02da541204001501c0c2d44882c50f24608040380310006039103648203010040d018074200d041c3c0b0035030501528641002550340c07805002007110844030a01004003160405825080c1703880d40c0e4000b00251310f0f040340260708006006000d0031501c1d00c52082c084072583c070300c5621030302c0107400c210403100104241c940503904c0c124252900d50f1422400d0107d0562100200c0c00e00b0000c081717a0520b94130502070104503044501d8800310507145810140b21030049941c06c00051040d01c5264044c1010700c08056200d01602e03645039601c10018804010445624500124220000348820194404803902b04da1041112011580440035600112aa41000c40c1c4114000380114070724009815804901665140320380041c0d0361640c03040501c11030601005104000b003481402c81c03603040302000b011100e0038010007000550384039006007082949a5915000c02d0f0468110705060f0002009542c000c90002c3c3c1b140020705080c08085001c0d0141c003016080009540d00d04040b00c000e040140303503041c5240e0711 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801804811 1250 801803561 801803567
    0x70b090a050409210f0e04020708040b13051309030518040e1219080c0307110102041203110d0813020904110901150906090e06100c080c03120604020304020f060325 72
    0xa940310803080040002c0881a85102e0170104030010001d0704d0f06154945800e003804000d40c0206000c0d2000130003404042500482100106640070790b1150501c0f11070f0401c41000710b460303024641c3d41d60f200d1a1140101c006a0000c0540340c0b030b04c0c1d002d21522201c000c04000f080180c910000c00d11514040d03484480640c1031a0b8000d402ca40d8810b0054080307074450042c0c20b8a8109058502803036039602031001480d8a4852404610310b4202d030000581015501e03018030315164050802200410300340905145071103010001c54560468501d400101410b02d00c030300c081d9021541c10302a00801544000605000c03e10b20310202c0e029004d044000d1660b92841c030300485000828211001504850300041c0c00c80c403c400c001c1c25a9014105000c0c10f0b1190000c100341c044009460780244440c3c440541e000c40c0c41e4001415000700c40c2c5029594402c4030726600c0100c1c540081106100700c1c410300c28000035840e0400d9424003000107031a0316503030b03403543c161440c918404800110340740340e00281c4c80c07000554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801806061 1250 801804811 801804833
    0x10909020a091d0f160201060b07030801061e20011104090c110f2a1801080d050403171b01021606111216031d03090a060c05070b090a050409 62
    0x6400a2000020000c504543c07601402503403140a440c5080001c1340b49590f4480c00b0582c5040640000038920b566100d404021380c005020030307808501d14100412900780c0155990000c0f0301035078010320311f60388400e80203001c0e03151074030041940ca81003810a100c8583c0c00d43c030501c4251000c161468485694644c958040d080400c003610000e004810b001203880310004011108424402c0a000356951460100c010a0501745149031018003100f02d40801d030703d0b1100500b01084403100020314942c1040c0e4094a80810202140e00f001000c0004201060158460765420400050181c0c2d84041c48140081c031049003440340c5086510006103e500340d0000d0002468141c803509091000030810994000301e4020140f041e0204e40c41c501c0004d00110003441070345170b2443d907402c000a1200c65240d50440c01c101d60482d440c180c0e0310002d24406580741500304030004029500d03000100b560311744c4e60700c2d846000e248108102508007090046540d039038100401c0c081d1001500410088481d4113200388080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801807311 1250 801806061 801806069
    0x5061f090b4e1c0c0206030a1409100c02030f19050405030f0609010b0108090d030e0f010e1e0a051b030106090e03030f0108061e06131503050d02160302010e010909020a09 75
    0x40300741924850f003141401c803101500140f076110450700a402d43c0034010203038801003540e03040665030710f904507001d007034641040d0061049000404a400c1c80000c02d00498004d00380e40c1080d5130090140300e0606421a04817030410484590100b4038016000c0c00341c96901031034004560501a40803000e10b000e00011300d43e88200b540000921050707180c170005448202081d500f0380d0142e04107131084181d8901075007203421300c2c0440c001107500b85101100514212542c1540c0c232001c81e04000060805010300350080d401d0620313030402034204900ea1355100355a0301500e440c0043c1d003028204409007103540c203601c200c0081001040c01d000075031521801c0c903100d40c42250f00e00c042660103400407070b80726400902c05114208402d903010300e100203a042c142030b01100034900e0394041100c0c3c4480000c6600c5000e568102c0c003001040c80b54680c00e40c0b401c1030401c86011050001c660255056900000741005000120b940a09040901c2c044c17100040b2410100b80e0025500c0600024450f2142c030b5101d8014401c42d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801808561 1250 801807311 801807313
    0x3030a05060d080d0509070e0112020909190212030f0403061b0c03080106030b060f04060c03021e0c0108130c080601140d0510021605061f090b4e 64
    0x5585403801c1180600c02110003818106062004e40c0c401d01043e80099002038100c03044840103941c072034030100c5020098010116042010080350210b0510200b00c60f04484078001400c601040d81c81400010010408042c2c407800b854808825220801d100300c4264982e1030301e4040d91540c407030405002034001a000d440c1088842003802550368802e02208020395415925081c069107080e0045001c1d01d40ca2221542c0038800300301308540141c200d40208007d00a548900e801903000d42006420400d800c03410148140321001c0b11030010a01290707c440310602420014501d884a0b64030086541829000034a101c0a100f4081240c3e20b000901038104c031800d0000400c1c0b09070720700c10b000394288035580c010f2090380000008100f04409802600b0035001074280d0480c401c101d9101c1c186018019070f8940c01005101006001051521400070054100d8410502119000b10042000d400e0311300140d01d400c0c10490308401d040c03400780c001c200111361b44540100501c540c6000440f21140049078021803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801809811 1250 801808561 801808571
    0xd030c06140618060a0b1b160e1807030303020325030504020310020703140304080702031005040615060e040903121409011d070b0d1104060c06051005061c060b040803030a 75
    0x2480f082d0780c10f4140300e94806040040d400f80b400e2104403003034025286a482101c0a01c0c0c414842c0803041015281280c40221820700700d07482c214044000c0c21010700781000140700829200d014a100062520032030764949001640d0b0790326102da008204514001d801881c1d0f03020a040d401d101c0e4582c2066001d903000300c0030340b0194513481c2c0080b8224031400f24010089520700c26400322a10401e07015581c041d0050f800145080800e40c0001e0811900d10000214240e40c1c100b40403d00c840da1080040b140b280c0b01da905055802c1560107085450b10308003007441541c80f400c1540815100304055150401c00c03540a1080101001d01d0749600300341215110850341c60100811555051408044e215480d1400079040042c00e00014000e15489281e10001c0c0644410305c1c030402041d407a00401c01010b0301d54500f00c014105281040555801400c00c0710351402809041c400c4e0b56a40c4201c498503010782c130707a502000f545404c07141d0281080d43c0c0300401141d4086000900010007000451083c03c80802c1004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801811061 1250 801809811 801809839
    0x103050c0301050f070f081302030d021c0905151308010c021e0a210c0b0709080d020c03030a0c02030a06022b0c0504270e0f160b090d030c061406 64
    0x1310340da04803810800940c41c00e924000c5640071b1507145801500c0d80030103009442164021034030388840c040c41080183d1048501c0c8a0017240d40a0504910f4564a08041c40c140b03048005080180580710313202c102400040c0314030b100280c0255500c014608c940090009201d81b00c00a52201c0c2c0a4080e0603490962000c83d8807040c1c00414551780040c1d12800c903250906104800781d06030041c00c2c4e4039500740104008030f60081500c50361840d200b03485950300c20448a04100720070b41040d007402c884000f55444600d80d0000c0ba6008000d40e200d00c034944c9401202450345000191400b03008080180c0b000b0300c00104142c250110704031000072007225044403452440f02015040c01c803500d03d910640001c20901c001e200c5200040301503007900340080b00c20282d076062a8000740440f04041592021a4000d09101100e49018050007444d020012449031445d0302d03001014185105840b00c40c3d1107880305c280a08201405200560090340c2c0002040103140b901c07801004e0b6071801501d10520651900707180c0c1c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801812311 1250 801811061 801811081
    0x6270c0a230309101401030b18010f050402130510090203090a0c03062c0a020f041d0606150a0507021003020c0307030503040516080a140f0d050301031101030504030212180402030103050c030105 85
    0x1009010042c140c4041d1f032854031007c066403005030541c3c0d00f003285080074403651070090090104002e409000018942804e1041120414030100c0c081b0015003008200107600440000b5282290a45807001d607417036480c03102050410303029901c001c1902c03007815030200070310009a00034124011000e03e62440c203141d04006810005000e2944005940b00000134030050600705507414115801901c04500b03050001054001c03480426a008070f241d0000c02000441c0c5800b21039199601e1031006c00f68a0040c0c240001005441403010290140807038551059505110780d045075581d45080007a203440b81b155280003401c0d80e00c2940d0540b4144a0b40301e00c244081c0b02000380000702c900003402400c0303942c881d03903800c0c1b03640f001c240d00750340c240c06102d00c0e41c03400c1003050103070590006040d62019502e43c15850503803a07840c03003001540c0c101860b00040000098001a214000c50150464280c5618081c1944030140191015480c1c01030300100001041003000075035a100500220001e11140c0c0d5421454 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801813561 1250 801812311 801812321
    0x219020a0507060e06040b1c14011217070b0907140402120406200406020f01060e060609012003130e1f05120c030f030306270c0a23030910 61
    0xa4000c1c2c01c0048200b040d03e00641690018200241505081030b5540c03501d284290451079a00483c1811301049050b8a151841102e00c0044162050030540d4106083c0c0c1b160005101c0c4000c0a502c13000c10030082915011081d11552648500c981100d4a40b51100c161a95480d21a0001040800740007450903d0b140c02031722554030f070000c0149003d41c0c840d2640390280041c41c101846485041703c501034240040c0006202404850300104440359900054500312009036001000a480b0f1030140701d80c5994500071a06107090900c0c001104180c0740c1c0314241001e0442c11000c0d0f00b8440000d211120b5034602a00030704603808442071020584c1c0c0c0a025040340c0d01901010074284680d0f110030711081c6001100303144410030031800c4500a229110200e03140c140d00c4201c4280036880031080045a01d0603100ca201e0404180e40500e00100c90005c00d6040100080c4c290b0102203030104040c0c20041c8100c80c000c0c00151072184400f40f80107501d007440441e910517141200c1600030450b0030340c1080d00c24065 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801814811 1250 801813561 801813563
    0x603171c06080a051218040c03020c0604030e120a020a030305091306030f120f080c1e0d020d1b170a09051606020712021c0c0b030115030c0f020a11030f100219020a 72
    0x850360241b5402c0003000000c3c507c50342418149a800d001c094045002000141d210f18869103d21120780f02e41000c21540a0300440701102592001c056a001038a40510030704c1281e80c0746c2403503915180780700c00081038840030b00310554000b40782500003c07e2140c04800040030314021440341100401501089a0052070b086090020803c414007080840002100501c40120b19060348909400e0200050104d50700001450320480c2e004035002c0c00c018124851a075064860380854843c0303a001550240c200100b04813080d00e8004000300013031014109800c4600b41c198080301307032006085000c130000c040c01f1490240300c00501c00c0c8540071541c0c8a81c0440d1941a54000340507524042d08010314071620032103000125000001082d00140050745600658080e06c080084072150560400005046914010080080109a600c0c030005582c000c40c0079034009410000c0c800005051401203032604590040d03461803445014901c00c0d40c0201f981c00b07808500c01ca03d510000620480504a903181c45e0104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801816061 1250 801814811 801814837
    0x603020d290726130b06210c0a0f120b040f060603050639031f121506050603043f030b0d0b0f0702250501020c01030603171c06080a0512 60
    0xb5608020a174000c0c0c0329544104001c0c0030702c880624846000903142e08001d0091031079444585c00e0700917803824100010140000600c000002850419484800201030300081c010700300714004241407140034039a8020f60754001c2c46c284040c60392454030a5907084100c486900d00c0302049200c89200c601c0014030a40e44c1c0303034480720144000031403150222a84c400b400c10420780d00341b10085480c07000801079005c010042d0003021702d40e1001900b049491502c2101d2918019403406d103090110303680d5002929003040d0002e0307240f0f40340413842045520850488600c8010b03da040710804c80f409543e140e160781440302c0c07640d040c13081d4103014061006014440c0130080c040142540011607003d103422440368090414412688800c90542010701d100c600200c800f980802c8824086c03242d0350f010008040100700a2030200031440c6543c40354a45112031500f0648610800900003d8015040351261410390020000b08421a9200c51107039840d1020300c4101c0b614010030b001c10032540d60150540e01c042c12515 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801817311 1250 801816061 801816091
    0x31b15030e0a021215011a03041103190803060f03030f030f04020114030a09061103061e060405061b010c050a050405040902131d010b040603020d290726 67
    0x182500540894a42800319100345016040944c4d80c110105000c150b0440184c1801129600d55400f5003205810028015502004c0c514490010000300c135442174104c00305008004c41c8900003400d0580400503810000521a01c0806100d00c5000450241c002240c2c0c0241c03000f070110515441c2c0c0105095004441010300002c0e80060300360302141d81c054414900850300180340d0028020640040e11010703c40b5949070500010081548240c0c000d44400c0d5903e10309501d840e400003100302c000302060b0710402d9400d681c80c0106440d1582074a0260400401840d191080c40511200c903c9407010b03480c3e00c0750300346032082d80828001e0080340c460020f1942e91134601410304082c0030140507003034001c070b1300501300d4010012101c54511031b402034424108017000d04065001030712403d484010382054803d40c900a005c0005079100d203400003415600c4000003107414a650145400100a94480c69141c0070820802c02c0d6107a00c1301c030a440044120142043c10034066005038007010080380d60785900c55541d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801818561 1250 801817311 801817349
    0x1120b0a05090a06030c0b0309060f091009140307110a060512010b0c190521090d11040f11071e150e0c03030408150c0703020c06030c070501060f031b 66
    0x1010652040801d080462010745e03d43d180008513500340d0040e015075a0103c00d020100b0018400320307030040c9200d40502c859040034411282c440440718401c2d00f102ea0b80b002403c00700700442c0300c840491b60011065070b071200800d080c0346021300315070448217200344644440440d001340a1820344912035135641d281e0001e43e00300031141341c86900040c100303046441214486070395541844403641041e40315a002e480c0c102c0c18170628010000041d2169a4062418001d0498039250140d1107445076400500f001c903020b250402190051100c102c500e1005424501031001300d101d6100200465441601c8404410190400900180b12861002003542c0740c1c25107402c0c500545038000385480d51060302614050b200c5640042d00d9a8000e50007071039039401c82004500000c0f080714a9940c01608440725924007c0142e4000b5101d1203680c015a00c074200100c0424201e03551001034440e01c940c401300070000d0355251040f8803440d16a034481164440080350004500d03024035590b803001c492056034034410131220 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801819811 1250 801818561 801818569
    0x9011e0c020d06020d0606120e06010302300303070215010f030f03050a05092110230c070b040818030d0e1e060d020c120c07061b050607080601120b0a05 67
    0x701101a60340ea60240704074100a4201e205200c001e124549800c8c0c10308540e5440c203070a5400c20919003c154105800400258943d05507002c0200c1503c904440c1c0300c584820000c010005052040c502031001001700001035030005100e04030070780743c4070405000c0d03a0780344014001b0403d0b40c00000c048282a40c224000070303000e04040d140500c010308200d42071000441c08181803030400d6140380e00508003501052804c240920184400e5942e0301c90a0006c03103694074003e80b5000c802c13010b510006904800184801e00003000743d602d07031035002da80f202d540e04043c2013100d41078010800400944074820034000780e034a4009000c2c41a5507082e1280700645015000300426096072540803a0f29031808061102d542c1e9446008054542d002c1034010703110390500c0201d62400c8092180c40e4442c3d10308212144010713a0000713402088440606d0310040c11303211488010b40724410010014901d1190006110a03e03410500780341c4990020307a10b440d05118607400004c00e8425841c43d0726040341c06103c040c0300b9414 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 801821061 1250 801819811 801819829
    0x90a08212104060903080603030f07170903120307080708010821090301020706021201050f0913020d020904111f1d030a02100c03090911040521070b09011e0c02 70
    0x24080d16951030a24202407050303014001218115401944c900710b140404d80c018141c2c0d030300600c05030001c41c20300c08500010852403081c000060024405c0800000511110600329040010041d042c0e94014590a841c008950001c0d41c411020404050004000a210747c3c0030074101c800300001003159012031580464682b854156984244004100c1813543d03840c240024443d140c4659001a910f044202c00c0c80d41c1854180c001511403e6186001946a0f580520f43c541040d158600d805000c001d40c400a00c180108403030094004450004110510204004580502c1d00644100c40c1500f000b140040301001210010000309620f075100107400c0320314000c44508004040d00325484070b407050300015003900b9074004402c00900c88a20b900c0426601010280040a0300c590a11401910202c1159a4000ca000e65801a464a1881d40340303000d050746a01c1210b01d03444142c40f0300b0390322054130400550181c41050302040e03400001000605462003501c1e0800d07560790362410025616820040100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 801822311 1250 801821061 801821077
    0xc0619021c0c150501050609010513090f0615030b131e090c05011e1b0f02130b030c121504030903060609051006080601350c090a0821 59
    0x803144624404080340c4070014042841c0181e00d540c03800c24410300d48110100f00541d5903051050400c40104001e44544082d1183d849007400c0c6079031952041c81020554851503401140704900301120317603181c44000e40c04001501c10001141050040300d00003039082e10140003400b504407a40c015803007600d40032544222280d11241304403030b854898a10204054918010040d00c004117640e03800c000540c0c0010521264651b2010942d6005424400140c80100303404c0c04100d8041c9008812010000090502c3c44a564010100700148024021220007014014840340c02841a52420005858168001007810078000004c04200303580340c0b10083e410901030030403420b0001c107110100c002807440c003c0b134014240f01040025185000404414a89143da01900c00d1040b40b00c14030441766404048a0f1420100745030082d00402da00502070140514011600000d50860060240718000a0024046028221400207005459064154554804038100d00b1094807000b0000020020003020b00030b52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 801823561 1250 801822311 801822313
    0xb010c030e040e012405090106020a0812071110140105220f14130213110313021f020105010302151306110a021215150a03080f041a07060c020c061902 66
    0x7145c0c2c0240044540241800e6031264282d01402d0200741840d440d102c0c01001248010207064940d9241e81c0d5940c462409a020b903090044000f03603800740103502401c0040038120841e100084488a402e0007850300b80d40e441e0003c0d1825000007034078a00000252100c21044544100d95808268160001c0508200181901d0384862403121145041861075206484455141155403054030401c0100384000c20381495052400b00000c5040c02200d00752036011301100c49100c00400715000150401000180d100c2d20706440b00100c01c42c260381074022038100e03413003680c3c12104501200c0350400b40b80102da040704e20140b200181004514402c007003c119510036102640c500b46801e4000c00c6680c1c5070482040c0c1e01d0b0b40324585442030079207194412540a01c0c06480100354491303180c0003988640032440301501008010540c1210b0b61240c9045400600007400c8a0113403c3c1890841303900c40c0c000d03040503143c0c9807611070a00c04040c0003154442903400001c0695107010082c54152444815002545c011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 801824811 1250 801823561 801823571
    0x6030d0305130b040813060822020312030a060501110705010503060d03090f0b0a110a0308070e060c1504020a0e0103020a05060c0a020a06020327060304060507050c0a060b040b010c030e040e01 84
    0x214000141890045005201c030640c0e0303610403521045044c6c2a54420020410024100905070602000090080000043e0310400703440f140002440e18000401303040f601d42d03000003404040c50389684980110b0303a00b80c0f07500f681c0f41c25a4024584034012840380c503001ca0f400b00300041d1300e032030440d10164030f16109040000e94182c40e50680c2582c0092034001c400b000303200103000000c0b103412812020030004250000c00031001c00b81c0d0024194071014101c0814803008903403042190f51134130305541e0780000031741c00c840d12003921010804000205482c207034080d03c1d001002050300310148080d20b0603a6005840303541ca47d880c2c401401010f9001020701c5070140142e008241c0140d890581c18001411161300031525000b02c4001c0070781d85810900c0a001c850a0b98030340c0500c0d82c40340415280d0241e0403040001c0c4943d14180c0660f841c0c401e200c00c02c46180501d4070100100401c60384178080001c01074904000748040740c0015103d940b040d1030090089a0002001038803440e1540090140d1040300d40045030f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 801826061 1250 801824811 801824813
    0x4090b0a030f0506010e280c05070f0b22030e06090103180507180c02060f060103180311010501060e010206280c030f0b0301050c03160e090f090f01020306030d030513 73
    0x2c0304000181d021245604610010401d2892028415400c407a081d8a034000d10400c2850800c0201c000c8040c07220200d840d803209451185c01441130f190302a40001c00240d403281c00b0f1509600805040303a4120b251525000f5241003c0090343c28907026550645481c07094241e0b000400c5040e81240e10f2460405440d005040881001c0c65445c0801c28480c0c40240070550611020f140c101c05400203202e00d8a140c28000705140e0303400103a10303400c1000c07013450300b0640e11210300403006401c52071390f400441900742c3c503184101980001c0103403485c00c6040080100e079072540300844a9111401000c0d00503404080071405003a110404501c01c1d001c0e1451043c401e0044040c0c40c402e1b0341f141159000441e503600206040140c3e9405040c201c0c4c50102c00810a510302100700e00f87c2c5010180041c406c400543c411700000d07a003e4040b480700d00304003c0c4502003a10f45440700749501182151160100d02501c041500c3c001c1c1c050080e6405050001c002d0702d900304101c0740440042c0703002440081c800340e501e40c182c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 801827311 1250 801826061 801826073
    0xb030d031109100f02010506040b030c04020706060b070b090c04060f030312200d180f0314070204090b15030106140d060b060d1508030708030109050402130510090b03070b04090b0a03 80
    0x1c603516494544d1a9500030300b04001c1c1c21650028034040c0110708156046116640c00b14118030700350411940181c03117900605001005007034039044614141000590001800701d00401244103404480480d800d0a600304140000e0f44c03000c0c462801100f80840d0306000107809010140c0c40000d05801c0021400300c264000c5d000f01c0005c60f1904c03a0020f0000d2820141c0c1424011b440072151500b030101c0c000c88841ea10742064000810003c1e0411140c0c480b50110700454904483c2c64907001042030000080030f0411000b9048191000d0391082c41c06002d155460506004480840f1006014007070640c02c58003e00c610303d03854009c00c455140c2e840b04250626503550025042c00c8800b001e0001d43c400110801400e00000d030b401100c415481801944005044101201d05440f02c40002190329182e03403001c00c002039070300c1040001260a1404018408510806040464a800740b003448114a000d0a0549604147c042c2c81c041d1803040005100c1c0c030701a500400701146018004180c590743c0ca807118 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 801828561 1250 801827311 801827329
    0x706050a0606020d03020403080f03090a052409011802060a091a03010501080c04120807080705012d090809210d05030a060f080a030309170c010b130b030d031109 71
    0x400d459a0307a007418450030380e04000d80f401c554090300302103151505584540400b80600030303072100e00c038078000001003040c281802004800d40d8480115058500128540a199401c049920350010600ba00045c00c4020502510306454042249146016125000d1010303c2d03102c1c12034a070902001c0e0000003440c0341c495810001071240c03885015102d505010005101000140001c022664203000c280042c2c3c0042d201c6e08000c40c3e0010321070740d0b200d250b8500003820b8051018007401c40e500e0304002254140c03000c903241d00c800f0345d5100203a0291000c14130002c11074080d1400030f802c0e14000e202006e01401d0021041c80c450229045200c600c500314581e003881c15614030085000520080140f054880c5140204005041d00400303021115080048003940e484811101034105071701c1d00c94080901030a0483d13880d0105451488076901c40711042000d0103011036400f03603401052119a9102a1a1148100c0c803520400501900c1481d829041c100e02401141c2c08003441c10b00c0401111030540d680c4880 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 801829811 1250 801828561 801828571
    0x90b030411011e09050909150f1026010c020d0f030b190b0c06010501090308070b042d0b0a0228030204180606020f060f161e0302031009090c03060b0105070605 70
    0xe04c80103500708014400e6580024241000c543e00901e0248602e0110407180c1d0360210f102e424190156079428200c406c46465a4401c45c51025058030403506143c25282d0741e20343ea03280f10024000340c0c0341e83e039040380d0794829012140005040442c2c038008851003034103c0010b000005108070420360100e6071038003501c40309506c1520409000034107509200418021036005000034241785d000e0906d035889d508082d22890000030030000007200044c0070001d400d204012107042c03a2010244440c10044078014102c801c02060382e1310b010420004800514a000b22607000c0b80700e1418018070f00c1d0003008042090542620003080c55004e01c408580c80000c0a46440359007508440403440030b16100e03000c0c0c105032100b0032206c5c07170b500440c00300120020340300c0d88603812440c11040d81407003410900d411a03c070821078003040c80c0127244010030340c1c2d020340c0b5030061800f03030a550785034040090b56900c0c00750450b280701c04000c2918106c9038040001c03030043e030310400d04c5080605040d0300d400c0380d40d03440c401180d0044030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 801831061 1250 801829811 801829817
    0x2040c02010903090b0f04030b1806070e13112a011538090f15070b100305150a1d0d02010b0f0604120309030203030a0504080607090b030411011e 64
    0x8403030380c1410343c40004d080080c102e04280516041031003112034031910030b9010203808040c0300c0002c00d2078100f0091100c500000600180c1c3d41905040d500100f40c1245d0192682c40fa40080c002404110420f100310040c82940481c0503203452000407811b500c07030751a078034030500070b07020011800f080c54001c1c00b80e0f5100072008070f0540a020f04007680e100100d00511141c441182002440e94207840c9a60111051160f80b981d41c00c0c2c90741402c00000300e4a100401149800800000042e00211044c2c4090b00350f10744508102d00c115554045d03010403159841c070010b03000d0303803081c010020105840c0303a80725082500c1482c00302d001c555044041d0b44c00d40340c1c00412090b6038800640b4030801d56080c4200c5c612a08200d032400c03040107400c400a0403500a030301510480e0b0303c01903840f40403d402186c0c0c0c0b0000b180c1c043c0030380c1c5e01c9188521000e0010f400900c60010140030701000101414490301d00b8030141c6802a14050454880381ca4805080720340d61405414032110194001e6100043c2012003c2d15010765 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 801832311 1250 801831061 801831071
    0xe090907240f03060302011704020f0406080c122815020408030d0501060207061d04020c0a0c06030605060f04090e071a04321c06150602060601090311130902040c0201 73
    0xc002840514819a002d041515001d81030005030781c040d00e0500066610618940340da181c030300000b180610803440055210340380c541700140501c0c0c0403805d84503404085490003e8200740843c3c4030b4456100d5401240300c0007822114042c0140c1c40c210030500980240c246004401170306441204982c025003110802d03610109025110304464001c250140681c1c0c8050a0143c2c45c100b40581004002c03080c40600788120b40004585443c0d6906850b030f110507403c00c5490f000f01c40d080195090b041e41c007441000034107050b0082242d0070600b0403541c04112040c0000e1500d490007041c00000e08c001104034125000b22080047c0c41540804a086800443c40300150703100c0c5010b600e6000007802740401307522420801032120b200f0f00f08054001c3c1d048001c0d140c0848058400080d50f901000031071006280518040300e900146207032032110001d41e04c0927002c0301c1641e00c6041c01580c409246200c01000c12030901141c40e00ca04282003180041014501e0200781801d042d4001000d036104918843c0050f9559 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 801833561 1250 801832311 801832379
    0x80a0c050a0f0e07091224060e060105070305090a03080702120601030b04060e0a0b0a020d0f062405040f0305011a040e0a030f05040509010b03060405011d0c090d0b0405150c0a0e090907 81
    0x1101c1e0301d00949031f10442003001d98905085221903c900070552418010081912010305014600311012030400401c1c50103d9502d07842c116016400142c0141c1c010510951007900c1d0b110009042410b981c0c00c5200b0300207995617542d80f84080d04003003407071a0035405820004c40003e10200d0f402c80c0610450f140241c1c4490b042e051003000c99121904155030b42c0d00f426020800003042c80c40d514500d041895840700d8410320424261900c1c4150750010074407001b0100004203000043d48400c0484581d8083c000440070584100f02c141e80080a03180950b8118000f2180045d000e82c0c2c00b844984400c1c1000d0f0b051640d50380c00200041e0b0700f41c0c880780112000008000292038107201c0c05000d0505c0094401d81000c11782482c1c100c8500c010079840c01c000d40064082105c0da80c5da21440041640580d113440b89207882c0c5415901d07000032a59182420500001042c15904100195100b03a801e40e0741b000421139410b010080d032810040c0101649000c0e002e000702d040c0c01070b03030403c40050724448a400080001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 801834811 1250 801833561 801833603
    0x150e010b03012a020c03061911030f0a0f0b060d050a0506090705040b0d1128030203280f090c0f0b0a08010e0604110301080a0c050a0f0e070912 63
    0x1411202a11036458481c0a40100c50300f10540d04586502d14010311105510000907850b1280445100764541f0611040000c28900c071750088281814130b440a002484a403000b801981c0003c5e51030b20144400d007800a00042c449034003120100140603c08501d40070044003040c855400f0312603481c411501e900c100f2100303584600078a6006070051314180d0140c905000e00500383d000f540075202c480c1c00001664806142c07030303412080461824034407a6a49802c0c0e1880c00080303c0301690040c8403090788100001d50305002c0d05c01d0324454010220712200040c071554002d02200c90003020000340365941e1a0b514600c81d4184074004403107104104c00b220440c00c040b25034902041590000304094001c000c6c030a0307155402000181111a15007a00181d5152180050040d040c001480006c5290100001649410000b1400d02007401800034003205900d600c1400401c0c0000c1c01141d01684100700100580500845180e0b440344162404100c035a403140c55080340741005c200141d0351190500725080302803030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 801836061 1250 801834811 801834821
    0x3090317210f071206050a180507030501030819051e03100b0a050904110c0d0e130603050a0f0228061214070f09090509070303020c030d021b0d150e01 66
    0xe94402407038441c9014941c25503140001001941000760a004401804031a900a4405854010070141c00242c450f4156404400a905500d00440c100000300e03030307a540603105090590f50095161481c00729101681142e8002c3d400818080004c01c0000c4034840407030720b006000914241160540c3e9040203480ca64030400075800c880804c010130014040c41c503802c40103c0302601c0055030081a500000750f202da403070340076003c081a011700940303040566165121100e9402e80da01291407400550184c0340100881d0303000d0000404540c024200e44003c602214a90708071148014040700001401e02c280407180803144055100d01545450b0034813405400090984444c070104c8d40401c80c00801d550031018150016062500780050228914503042c4290500c0c8060070700b1020520880c08e0100040341c4e00c1c9076510080d801030060039030400f0146030116205003015459070060098044100004142d4683d031440c0743c0d4021208001d0341c0025a40c07961544000300d605000260608000910f1b0742516 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 801837311 1250 801836061 801836107
    0x303020c2e2003150d05010c09030201021c0203180a05190312170a0f0213080a020a060c0b0a020309070905040f11030d0207090b06070c180c03020307091203090317 72
    0x10b000121071180e031002c0c1e40260390b4020454800d100c601340501c40480d81a40042c031002e00300b0350800a8504426030020444030449200386e0894041d0081659117141c2200441c3c44107006030020050407000d020b00c141000c26a80d4000c00d502c034056034410015512046035a01400b0781c0500d44810814040400e0300360f8640365050500c140700c1004c05416401c2e0550007030800000540d19401070400e00b5141d4107592031521050f05000c1d0040c0c032600403903078825200d01c0403031080c0c1e01090007154052203840e04415a580c801d400d1101ea8554281f6640a9000184800468071a4640c005070350310b0301d030044034001da0084048046513409811300000091881c2000303802544080c43c5c1c4601950b002580b075007102c011600010b040340c1d42e00c000503081e200e90300c80549030048e002d801158548003034403640b00d0300104420801c18240c0d00c0ca42581039000c1114820040359081f071081024984045844000d01d10a2402c07441440c0c407507031010040070310350b01841c0e201c03800896410384440944a502d0141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 801838561 1250 801837311 801837341
    0x30f070f140604121e060f0e12090907110a0609080406120b010915030603020603042405060d0305210c1305010309052d100c08060d0507030303020c2e 66
    0x40f50070000500815102c940008201e1826264030000c00380c41c1c581c100c240a40c0c004018440c0b4aa22074100015000c2d0350f03000030355405841d031444100c4024400302c45e102103000c0c00200841e580c680003503840301c84082a1407101c1c0140b015840014913680b049000c0741c0c3c400d42c105078650f4102600140764009214110b00380e2450000b516416130313005114a0200d40d03a9081550180214072012000750040c0d40c0006d4200c440030050004005106c80020709881d1602000c0d2998000d140c0710200707440041e035030b45400002010011020a00c101d0043c411108840800c6201e40c83c0104000c0c0304800c21540c00385802c04c003081c44400c0f620002c4928005090918040c40914040d0716407644035812803108260102c0c20918843e0010b800514015000c00c01c81c0c2628519204a03c40001070a0015171081c00507004100185041c9080c0c940703108640e410400405c009170079a60203600940c0041d140b01d481d80b00303035030f06601c0b0200b50f0001c0c4c5e5000004110640c10703140c2c0c07181061041e2000c0035040004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 801839811 1250 801838561 801838567
    0x19030c12050c070e06061b0c18010b03061c0812040c0f080712140f0c01171e070e0d0c05040e030301150f05040506070b2a18030f070f1406 61
    0x311040020b115090318003054224419071185c0c000220b240c4900b1800c603400c00146849141607840110301107000760401c0d20901000d15034050381c040d9840c424040d540c0c40300002d201041d803904204040042c000e0498901010303030000d9860b070005540010040342038413070080f0100020018514070360703401006212a400b1a9a0500800a4a0320070f58003d40c0c69074212012a00184004170038900c072962410401e8402d620034103100c1a072a44c06491406012070034406c44203910141c1e201c4401c0c4210340c5268061590280e41e0100188407030003074440001c1200e0054001c00d29511108003508482c0704441903060503291000344400e83d1402040c07800940c1041c4010002c20700c02211000d010800342c580a051040303000300a4030f4500072500160740003c030201d15070041044401805018101c1d411b00e4104000b12104008a2008807080c0d20401b51410f1140102d09031080110152a10b00103003030300e910007941208245015920780c01000c00344c10380c4808018040345058a20110101610a40d103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 801841061 1250 801839811 801839827
    0xe0715020712150e07060305091b011d1e0114040e04030503040804081c020c0301090201020c01050711091303110c060306060d1503060204060f030603020a050f0319030c1205 76
    0x52548030a2140882036042c000300d08081101c8000e1a0b0b8040c00c15a808120041a104925030389000c070b800340c040800e1501d03010440507103000540320038980a09100c4a804043c0800440b2034000380d01010092011000001c0e00c1996168501700e07108200e5903649517404c035100c00050841c0410035400160302c0f4104014800034801d15496644543c0600b0300d15a03d44840c5040c0b0110320032039001c0041070088802d41500740c144911360599400d4113030300300c5202ca0395107070406007201c245400c000d0142e885140700194035400381e0b010b0404140119091a6605490b030080386035140c08842c4a00d4945905500c07404050b0840030b02100010300500404001c21078602003a0786110203031200340b10b0800810159020380494102003051b5000340d4031044810355925002c40030350003c0c09808040343d075040e24100c805200b8070034081180e0b0020000d500017854402030058030310180c25100c2e0107010b903904108208869440e03102200d8800e94a22100000701d04209107070103185000070080090400c0314003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 801842311 1250 801841061 801841063
    0x90f030204020a0c0b10030326010501030f0608030c010207021503090a060b0a080f0c130e03180402070c0617070f080609061f03060311030d0207090c0e060c010e071502 74
    0x599506036001641c40c5039426003a40d001300b0600c0001e0160400c24100601c1541d690002c5080744d110361110034444c90003039031401d11103070181c14014500b04804c004104542c400d820070440a81c503200001002603e614040341980e118413030403140c03a90009001ca08605241184007050312009440d8dd00350b0814104d07842c2c40740403220018003115141c1d51207200f030b9550f0103040e40090039241d0495039848111241c594032904070000040c49680d140c0b0071500d0b1803105000300301032001c2c824055480d102003190f80301c41c0c210a011710b00390855424445000001c0d02001c0301c2c40680340988a40c004224089050782c0001c800504403c20808014900302d10f86821480c440d0f001101240c1d80300040d0368007001315640300c00b950040700100d805040700380481901075103ca402c1c0d07800b824220500010203820305565103000c1c050301d401030380214030400104206034003894151605240c00341504461000140060b007254030326a003965502d00e50070300240e070708211070001001c010040c022480c2a4020113 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 801843561 1250 801842311 801842339
    0x61401030b0109060f0306050907020c03160510080901060306020f25030f0809010906020d23070c08030703111305180103170d06240215010b1804020c0a0506070306050109 75
    0xc4c0d0305020101000003030080c003e4011602814010307040012070301c2c2400009550b9260400924002d000340f1824108000184590800b40e80001c4c0c011902e1905607101140e190900402e6814107540e03a110104c0001d1290006240070320304a003609031107603154604101c01c40c01c100c030242422800200c00c0000a500008403a0440300d40c5d0070181c0140e078501c07100c1c80c00b43c00c05050003880103100040c9103075802103507440f043d0100b054600312480320303800c002d0208480d48161b601d1b0b80403e422808030380000750340000030741d401606031501251040c14140007100035040100187e041d070045c2c03030052145041c06a01d01600d4180801e0154486d491500d500c0551580d4020711101d64200056500031503059070010401448003051228045284a4039121440d0000d02190b0060180000f015041d05c42082c07141d050b2070084105518142c003400c02e40d82c0c18122031390440d8000343c00b072180483c44002802401603172070143d40640103d2030048401000c0320451b030401e905105107014184000c1e654a0703c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 801844811 1250 801843561 801843569
    0x708061b090414040b01090e0604020d0b0c0d05090307022d060d0e0a0605090d020a1e0f0515010303120207150504061103090a06110a0f080c0c030d061401030b0109 72
    0x1696070340c1c0350560081400b60201c003016241c00382800081c0800c01c045044210304a41c9205810886944a940600c1d00c1e2402680c001e9400a80310400c400440c1031f14207078581040c0a00605440d11080002d0310b0203647d01141c203035402e9040420360f1010360904503040b1a01540d804110110600022040007120010740842030041c0380c0032401d41b5002d40158020b8803d04110421200c485080385449005004200c0719030f08a07000b01d200090b140c50000580f032022617444aa06000b0040030341e4141c20f00410020151908481c1c071010001046080c4100184210142c0d5911110743c11403c010340681c0410450303081c410310403c015804501c02202d0340f07400051005c800b003103a4a03103080803c058008004444c621030310002c00c0c4102000e00051080d01c031031046c3c00c24452040c05030380c2000d076030080d2002ca101044220a440300404c4c072841841da480600c0c5440d160900142d030f5006072031a00840f003011552a62124148006c3e09074000100020109203002c2c8035000343d0740300003000e00070035121b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 801846061 1250 801844811 801844861
    0x1908070c0f030210110d0b06090d0f02061902150609060a0e040809150d0c0c020d02270a0b0a0806130b070203210105040b0d020f01110c21070806 64
    0xd2070208143c400e0050099030800b10f4000c0c0b00e00c0344c1c41100d05819502080c014103986241c1000c4604030b05094094a1180d0401003010301400400c2c0c607150110650f942c0101ea200c9c000f0450700c3d0306203500c440303008101d01c0303140d000303200c10114146603840f56207029018604c2890700104100265032102106029076a94406036115611540741144180c0152a66103500c01844082100300c10324510160186070407404c0148401200b00105032810502400d0194100c1406403059015040c400c0d0008200c403280b10b0900001c030641808101c0980c01550003000b0ba640701c0d048a042d503d0400c1d600d9024003803140c007800090400d666441030f505002c1400a040d2601c1e680000c105500900c01d90300b005180001044888451058014424009005181c82145400c80481c164100741400c0405c10343d000c0c1862a00d12004401134654242648400ba203a1050091180c2c090311743e9060844515011080d00c542c0d007030440d041e2401c10420b900144041d520a800304a060300240415603450300d8024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 801847311 1250 801846061 801846083
    0x52401030f060f080321060d12050d05040602030115050421051c09090e0c0a0506031306020d0e120f04030b040305311e0513090b07051908070c 63
    0x80ca0300c0002c1e1480f90310409801c6051100010010300100c000d00324016aa0846c211072a07100100b02c000c0b071800d0b41c1c6960041401e07450000080c16481140300301c0d43c040d0500d036003400e07492004070080d200c0883c1e084890a801200402000c0d807038220602c4c03181c00030b00348a8141818449405411905030014071507080910980d981030003400c0c0300e2403c012030407224043c2050303510a070213485110036200740c4503641d00c0c01800c90740300c1001086c178092080c001411115214689820403085810181c80201152004520710002452900c000c00c003d0402c040081000c8401d080340d242000640300d40d081c4580d50400c26a0800c0010100b11000d0760340c8008640f0315900c03142411130302402480d00446040c016804951000326507200c0b07500503402194005441161a0340340b4101300c200300e102c900c2d000302e009401800245041d1480003090002e005000440da0443d440b000150b03201a1070420103d480011351425075030000702d55070823a031040d04215070142401070000f0540342506001500c0c0c0e6850f8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 801848561 1250 801847311 801847331
    0x80c0d09021e0306070e030309090901181a06010e01091a070f050a0c0807120b0a241505071509151505011e0207380405010305240103 59
    0x103544032415640d0080c10014900318129a0400488a10740805101e4821319001480082c444c1c942804030000c0900514100400001030040014002d4000f81c81c65407615070200c00b6580b420281d5a2842c0500c440841c0048000d0111a010350b004e8a09810049003804400c41c1d81d8010404034111030034025000c0074000f503060b04903824011620020040f111b183c494070240f02000503405074a6000b0080040340a5558048565503c024452142200621500d840100e2501c0c2c3e4041d5000c01e28480c042929607108400e00b56400705080182e004400110b41441010b00310380595100040c7d90070418078040340780d00c1e0140844100c04080c8541c0361107005038410031154611031031556a000005110380052860401410322003070180d24009110075403100001c2403100510601098070381c025004190405041c07090b51650a84030fa1a0700c000f11582c100340040c600b12007030070281c0d41a001030b10f407410880014141c3d08064004071708040e889944c036500c0c0c806050900000302090070005804004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 801849811 1250 801848561 801848587
    0x9090516050a0212030c04090b03010e100c020708100606080901050403020a080706090605101502120a0e010c0f08030f0903131401030b03031b011b1e030e03030a0c030f0c080c 77
    0x145014034030384d42d4010007440080303040540640160f48403030006008024240c01854200c0e0011041099241d101d080c844815020550141603410510302c1030316952a20f078a01c8a181c840003088204405a0303a00041140d03a0b0b01040040c0c121200340c00074409800c3c079440088d90740781c4c0d0b13140103046c4520004503181000060f40c00001d6440d4807083c14070103480c02c12110103c410709072180c1440c0c2009800030301e25051002c54124184001158101d05054a4500450f00e020250542034184007551602c3c0020a00c884c0d00644120301c55140a0b90360725290614484403600076202d00490340c07062020f459180c490991030000d45120058000b4a14580c8004030043e00d0400280c13a0140000034082500d405506417843c51050b960000703001816a052403009031a296240000c0001c2c407541d1102540036046d40c156105011616000c1101c070b603400411070171a0f1042e10f0260b080c82d514000c1440150301070103081001014420104044203240c0e5000d002d01100034054020b0b0f101c005200310307402c01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 801851061 1250 801849811 801849823
    0x4050a0204051c031e05040b030a06031403071b051e03030405040e06011d01030213020a140a0809070608160c020406030b0412031104050f0616170a09090516050a02 72
    0x4401450b0740e094403da2000500410300402d000c0e80001c401d2040da0301045102c0e154036219075001c2d070b14076182603e00404d8040c190806092442e10a0b00c8110000100d40e04250066800140201450f40c1d01c900b468000a40c600e80d80b1650120030046c0f00411142c0e49078482500072549001e03a9608240c21100002c0c2984520303040254130600c0c20311606202c1e030000880d01c2c10789000740d5155654100b100c1606d0300c0072109200003580005031420000328540650083c05c040851b034200007901c1050304007100c1442d048021203400041c500c1d010008008020001032008010504180b603040c1007a040e2040d41060840443d42031103403100c1100704648443d4402e0005540104070580542090701d40403910300030001928000a0400301710b48200e010510881c1e0448500401141d03515001c0818412140c01641d900d011410142e40c038800404d00401141d203260b40d0600d8401c1c0e4a081105029040d030a80d40c00030407a152403e000c108400901c000341d41c40703520950410340c0c0c6505200d40203d203055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 801852311 1250 801851061 801851069
    0x182d050a1e0e060c1e0706090209040f050d0311042c0a02090102160807050103050403170c0d0f02090d0b0c04180501050a061112030c0c0105090d08090703030e04050a0204 75
    0x403254450700119416544508001c11a0074180c0d0801d4907520f805082c1809000c203583d2180200d00481108000c90000a00b4094030614000c00c1c1143c2640000b049110308440903103500701c58031a0141004001d00007011041d50030304040050540c03940d80316460780110f00603c18035051201c0c20781201d28210403541c982540d03003a000070070780c900719800701c0107500808412405442007212500014059038404020741d01c10f030000344012458000110081d2902800560611105040d0f14001441607075841d84503100c104a61542d5400750302030041104c40d80b15a03c50140d1040c4041c400556a540820b031b0880e07003054000c03403144c581c000003201a101e1588484c0c0700d80c2e41d03012214050802c07500014100c400840d104402c181c2c0c1ca043c240d8003400450303a00c1c52540c12501401c034581c0d20580155800010084080f03082402d214481030849009480c01d6a1b158011200058804d41c8800c0704c80e0720500341c2001c1c03d503061845d6000b903c3c014685d54014070807038580340050504600c80e410f40d0010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 801853561 1250 801852311 801852341
    0xc23070f060c0f09060f120b031e06100e131a01030b010f0518060d0507081006091a01020303011206090b1302011d030d050c0a0606182d050a 62
    0x610118039010700240101054200865010200f050001e030181c4101400c0300c12640703d00003805a10f10085416004115551403050b58542041c056520104416a41c8858002202ca0030755684400c01c1d2410100401501c1d01c0c4804c01003d000c0c81c86224031040d045001e0103481a12118503142041d019280c5c2c1841d0848110a0400041842190003659048a50f08004180c0003a260028050403882c409042007003904110081000d07424200041c40c00742e0b004405560300141c80786003060501c000c11090034112500caa2080c00b00c2401445804800d01c0101c60390089490100c00203910781c00148100d08822007110312510a1180c2c1d42c220500e101c3d80714044419504d040311004400030200d60041e80001d030701c460702541c21141d078030800d44c01c5000240203200e5100300c202c017160306500442602c00f5030700074100c26000088090092a02406a06c1a00880041049516030859502000d0341003603800e051404020003005c3c1015030040300000c0c101259075503c43c2095030240007401d41103110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 801854811 1250 801853561 801853583
    0x1211104150905060603070c1e020a0f0512010612021c0804030c0311030a03081602010608010609050105100f0503010302040f0902030f0105070306170c0d23030703030f0c2307 77
    0x14084407090000903074142610400040c0c444000340b10182c082140c901d80407428a0300320708042810000d9804030740d4002a15101606a50307400700d4a148080c0d070016400c082001c4051001d840d00309040c074850450400200800b91400c001800302d04880900030b0300130341002030300006500d68140c44400d4140c001b030500342e44990300e1410403400d052610043e105020000420000307441d02040c03080d81150036a480c44810344602c130350002a0703120100980b05640d80d5180000d00800b080c05504014651101e000560b03600d03200500001100c4409103500704002020b01d47c00340c6410600b92811f503501070781c2c000b4401c0d0f002030031b101c0103117010b100295252050800d00c500d01601500550311585160303a050246603500c010700c82e002e4102845005064000100d0a40d440c1000c0c005041004d0152840b10413402e031001001070040e0358540e4048442d000090407006150b05030041d60180411040c0820143c44501001091002440c40700c503900000d034034040a01307524030026108035a0f0040d000b011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 801856061 1250 801854811 801854831
    0x1503030f21012103050f070c030c0e01120b1b070204091101140f070b040804150503040c060504053312061c020612070c0c0b030f0a0501211104 63
    0x407505490140c203100d012500008541110b1100312000c402002e0340c45646040380c81c0d541512150491003d0311078100003449808041052581d10500460040c61300d200c502d414a050030815007c160481000d1004c14039445000400540c400c5501001d5400301c1c00781c0581107502404584100b40010303510500340b950700c40034041d003120405000c030800d0700c401e0050507805407030f00e82a00401890131030b04241842070402060101c0f40d01036026101d80c616031300c0d094a58141c19105a04080c418001500c00300c1080100211840154060000341c24114102803410300015064043c3c81498041e420240209500b60004400707050003104200444640314000711403403912417a070413911a841400700100300c0c2d00c603008421041c0d001300d8000d00100c4c507000341c3d04444016100c0182c1a00104001c034000400459400c003081d801130811004615070b030b814259444640c1e00405800d003241e1920344801089850f80c00f0007101d02d910140d2582445458490801640f00c0a01480064011741007252102c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 801857311 1250 801856061 801856087
    0xa030c021309031d0f1302071103030c1f050610050705071a090f06030c161704030803040620030105100201110d0212070201090b1b2a1b091503030f 65
    0xb00010900c2001030000860241080700000708172041c1c1c2d070844040b039038602014080360000d040b158000e032080341d0351408410200340740d58003c0703901c4115900304d84600006000111001c404000400109000906140d000180d40e00b4651000c0000d00000058084c10440140700c0403000780b02034080e0101d2014805d01c85280350340002c0d4281d02c0f50405d400514024a40403059a014201800103241440628400040c9041c0e440400b507c03036841c50050361101c551000000e0019621506101da1682042d1510000b43c855014048800340c02d240101020072200c201640d0440740c1c100c072800d54440c0100410790040490049c1c0c44001403000446d032500403000d030000c0c642224800084140c958034010308030700701c540c4550018241300d403020102d114000d990072896150b4003441c104503c0c050210345011342584804240c1d4594904164035246519028400303843c800030707030240e0080c400915031b00065242d80c00401005900c050800e80c4030b200e40b03081059441c151000c44a071552030b480c1a03290 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 801858561 1250 801857311 801857327
    0x21192118091a010302031506130909060c08090a021806060909011403120c0d050901030608060717060114070f05070308070c0806010b040501020a02090a020f0706050f01090507020a030c02130903 85
    0x4541c0c42c5000c1c0c07950700b03500c0381c42268802c0c0180e185802c09450400100030080d444400d072010103000c05000402e6522452140b048501e100c1e00c00007070200101400905170240c0200303940103982081680d40c01580342d10408204c11200209d80c1301c0c841e42d0343c0d000100326002d1908165044082c2c000045241c1780045e0301c803a28050101d048034030b2100be0b105000020321891018007240d420898a1240041c0200040d000500d814100030400304d803600d400070b2401000700c460b10002070f0001c180d003111103882d40c041d580021080c640410117a0341402c0c0e42960b4441c2c4840244684181c000400034081c0038820385000c4c69018221b15a102c145080c01d2031100d500d40540301035400b43e840000740b2400c04204850444406801400e2560000d400300510044002d100c601056001c104801030710580c00018591140b1490303001a0350704185101e40c4070581c0503007280003454034010504c9201c0340c00091000c00f007a03062070146818030b254404500500303460407030b030304100741840124002c250708201c0d5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 801859811 1250 801858561 801858581
    0x60906020c030732070e0901020d0c050a0906020c03031e0903070e040b370f0507030e0c0a0501140a030f0203070c05010b0a03030801232119211809 65
    0x4e403030600850101d000290040041c0082d255401a00200310b50760b0310804159104092100060800c801c8440b0314054031080d904040018000040641c038031034102d200707400604240c0c40203103040380e40d41d00800d83e01c1c0b24038031100342000034803d4003003c0565035800715051145d0140070740300e905c2e0b900e5601c0b04024206880442d14031005100081c02400341d003501030b070b0020180c0702c00007401400000e41159000086403544140f9214241c034205092580a401e000d803660b5940090050003012441e414404032000661240005440030400faa03402105e10b440e140030b10030810b68615402000360014000d101b059100c00d4000310401900c035401c40d40c5808218000c1c2c000f07118090b141010088000c88a000c01008600140e0040c00140075984040c2c0341c2884814050b5800d030340304000107490044180a299001068a07031264045030248000d0030000e004078172100c04510642e4441000062039a00403600c4400c4221000d01c0301c0c41404844403c044000c00e1001031a201c0c0540d40c00341c074200316 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 801861061 1250 801859811 801859853
    0x90d061518021306050a180806071409030604021909060e100605280905030a050a0c050a080c0d0627120c030e040902010212030915010f080604060906020c0307 70
    0x10741c4000c049050007168000603405007181011030905800761100d40280306d070a4100000300c010500d026461490660190070b1410080181c1d240100d0003c01c1c1100c02e00c804200c0e09003e101c90903e50b14000b030100c0d041541121900503082c842403480a0319401688200652410705100050103e07110004501131814802104103440d1156800ea0300f510580b1102100940c400400c0b5528003460070380195106003916041440d25500c10009140442440c2d094400c1d40020100070100300c0b40400308002080162811004145480c000a8039208603150380c2b8011100e036010340d002c116a40c0d2100341d0050840c0e5a20340c42c421515030030000070702c984404079a0030301d0903100007041c24050032908802e19815995000d001c1d02030380030700c0003420840c0012819445426082040361b007070711006d103108800c0c00000f08284001c50b154240c4002e410390240d410322007020024819680b010844680c040d41200700405d96819501d04440240f082188502c4c1900011907800d0801c000102e00600242c6042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 801862311 1250 801861061 801861089
    0x80112080c16031b0312030902150403140705101710120303020a030b0a0b0d18120c05010b060406080412020f03190206010f12170c1519090c060302090d0615 69
    0x1013030b081c1e16110b601014141a100c5089030310018461341180581d13602c0588a151107041d01d0100d0225904544c1045034400c070540c01d428003041007003041000824048600300581c004030000074200c1440741803502e4186100780d0000c0c22240c1268028401081d0046000398020410700703004009400052002c03001a041410005141ca800078110090b00e251100311460040d2215982d00144483c01d035028991b001d0640c1ea0020880501c50340c1448641910b8000e000503407450601e085441005502e1301c81c1406110078004035900902c190b520030b61100c40c210448203048001d07840e0100980c4158080d110020f43c0d07440303900e456181d036803060f1503503000c4072402c0c0d0722052144c1a000d03c41c05103540c00031050015001240380607a0904035080200c00c4640b4141005107500c0c100030003074070076416000580c5e080c04580c000ca41c100301c41c68014004100400e00f190b40d2000b144c01c520b44030701010141c0125648203072340d954200c20b07601c6e154082c00401c0841c01c10902c8100110041c031409601070800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 801863561 1250 801862311 801862343
    0x3110301032102240a0f0c02100e0708100e0f031c09060e060108072619020a120b01030c080f070e091525051305040203070e0d050106030b07020d080112080c1603 71
    0x18087ca04038282c440c0c01906041e00c12010a40c01402100f44480d1540307d441400240c441c41170001d0b281ca283d060101107004044280110710704040211051b10680c41049200008440c0801501c56605616408607500206040c8400035010020862074903006920002a510301c1c00944141150b1103440c5400f11102d95501c0c40880e21105a0000d005801981c5440c501d00307150341c0c004240610052800e82125161448100010903603042111076202c038200520500c110181c03658001c04454006021034945440d41a4540c00f45200c0c031030202040c00081500d2000522a1921078a1441d0000c0b04c0e0b4a8140e8406c1c10700303440c0d9011840c0c4501502c1e840a01c461041040f00c015100c16141a442c4510b40303000e00000f54002011102085055200c1c009295908489100f0031801000082006821403d008941c60070282c071030019503104039800207400b07030842d0f20b103030449408900d021840d00709401d20b00c200c0d1061000f100700c24041d40124030885c49403880d022054a008001c00701640c514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 801864811 1250 801863561 801863591
    0x206060f0103143702090103142205100e010b0f0303092407060e010207021306140607080d02070c03030207091e020306031f090303110301032102240a 66
    0x19a460b840c40c004070000d40500880350f404840c0450b0201001c0b04c00e81c0c0c104503003e0442d01074030520f01c3d1a4000540900d9903130306020341c9220700c030481d0b401203860030240c44641e0001e1704840f48214071076540a0302801d12a090044524454156805200701c4010703442450003040030201d6140325400760050403800c1d0500105071007e481014210034020300c1c0409201c5401e5440b0b441c07501030380c0743c1000607800140190203400039440c0000300140c2c03581018070400425012400600584514004080090500c0004804030840007a18181d99603901402e0040741c80c4515500042801c1c000038140342041840607084084078000d5027941d90940d29205c10009454140d600f02d090902e401c14107840b40030a41c0d0045400c01001001c881d0803a43d80c540144044ca0310340851010a56170380c3c1d1482c14181c041c0505071050100c038404034036560441e5112200c083d20b01d80d028020900f2004034094650080140200507504403003d841e00002c21208207a41b1442103994a11841c1000000c03540100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 801866061 1250 801864811 801864821
    0x306010f0306110c06040201050304050a0213020a03050f07091403011d0303011502060903180f0d05010b030115150503040f0c0905071407020904140a08030907141f1412070206060f0103 81
    0x303d51380203444942c8841d00110b81540000d030054515001d1903480000595408140f82030a403240c800240c1c45002d03030640a0129080200b80c903813a09900e0041228440d4440190400d40e0171154400941c0c1c1d5449000c80d0060042d4804140341d0790300d505484503003280c000040c60481d1003034a0300a0001c1c5401c4001c03600c4a80030b4070002226403081c0a04440e0b0070080340500a207020107404007009003001c10011303654503840901961165034900b5a51500d007428054060607540d41c0303010040e0140b6120042540443c500009010032001101142c104561441001c0c8041d8001601c0526581c5501284e802041e05031451004a20400d0010000c080b4100c103a0710060780080c100c0040b590703035440b14181503140420140c4070f4010207183d8000500c00102843c0203034a020700400b0018240000c1c104114400b142c0c0902c21042c1c0740040801000044007405d4500c0f003803070001103240200c1c01508103402124011a083c0e90304104101041c0d0b40012840d204450441e42590b85408010054003215 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 801867311 1250 801866061 801866077
    0x6030b0702030f1e0c011410080c090f090102091f080609040f03110c0307030f0b0a021c240e0406110a020d080c070f0b1803032202010e0306010f030611 67
    0x14052000300c020318106505911140c010b500300c1c524042c01c10760174508450210010034282c400503420700c01558180c0c03000c280640005402080c5092203000018141080284140205080c050004520781003c0d01030310070210001e002140f030310110950f80c003546c0b48603401407400100c585000a40c0d51810100c1c043c000d6401514400b101c0c061900c0485076141041c42e1880c05100e5105d82c00034a4404000c1c640045000381391a544458452400da801c3d2200034051181c410300500585080c5184d4069001841c0c8501800140d030800d502403460b840320600010200324a1100000104e0580074858907105034130541c0200000c840100c0c005135280240a66080142d00c80408000568090100d1640105d541c00c8440e08002d80342d0b6520540303030080b903011900b01c241750f018095101015040000c140078004051170841c607080d10032415401d00c0240b10781c00703280e1400c2e115013035900031031604003820341c086c0c181c1d1410360f165244a51b00c8442d51000704c400d1840c120400362452620001c1d61010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 801868561 1250 801867311 801867337
    0x804031a06060a0c02010e13060e010b0a09050120010603110301150f0b0a09050406090c1205040201080c0f0c060c04060905030303041e0510090f030806010807080712060f0906030b070203 82
    0xb2280924007104c00050119040b41403110003001d01d15284d03a042d10600050085400110b151420f1109500001c1c206030300c560711400e818400400c8040d001200d9105a610038a4600d0601c1c025411042c200080c681680703100c1d500c0e042000c001c0c065201c0c1c101201311000d41c024080c081c420b040110300e800d403512901c541a01b5014040c03048940c100d004010400c110306e494007480c0d8440001504945a40d40190030ba41d94820710f0744001d03a00100c80c03503d01c88410320200300c03a2400b0380002e80003420040a004076080d0002c2c1060104018009694007120b450013221036a01d04140d4080f426030141c0a000045140700e90009041e2130000700b00e80c800c0b94404442d440040c46100926801003440c441118607003c0c00c14059400b201e14852003030355500031a403074130b060421401c000d00040d02c00b40099040188400810044076041a021900500b00e850100d050048010300500140095006200b88070003229000440c40d4940d000742c8180c5c0e000f00d484207500d0710351101c2070360b1302e1140c00011969 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 801869811 1250 801868561 801868567
    0xc1508061c03170a1d0a0210050c061303031b020d11030a210219050706061203080f0402120a03120e0736140a0509010b03030d270804031a0606 63
    0x1948800780e540f65000480c1e9a004a00c04145003a010800c40d00d548015880d079200000780d0b000e45c80e11082d00b031402e42490078854075100c0c01b00034041c0c84403c010501748841030344e101c1c0441098800e500a00c507074075408014002c071045e9114003e4403144601c040800007501c1400c0c022001e00044100c81511344e480e107600602e8480000201f031540c001c50035091003d1b600b4030001e0200c0e0800895240700e60744035035680f59100501c1c600081212200d4100603166601101c2c0580000e40200500c0c0d089207114103002ca160740c84e84001148100315002c0f0100d1070003113108800405400060b003c02d250b022410911150084501e05641d82c2e019201d009000380310000100340e01c482004050f008074030150000c84120300f41c02d1444080e100503207034451245129104000c0020300034440c4940110341c0100034403034000b00b40d0000c3e649006031040e5080540d40c0b45402c40041c0c45241d0300803500c24070951442a188000d0519904a4000b41300681e00040c0b240403480b108656800000e100e800001c1410341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 801871061 1250 801869811 801869837
    0x20f191d040b0307030803040b010e010911090d0c0b0418050603060411150d020313030e040603082b050108010c0953010e0c0105030c160c1508061c03 66
    0x1000d0111645060f070580180d00020001c5403074280103500c1507018107819903c55141003d444480c5005a2003900b800b0f1500000c03024206045084604904c022603600080c05100c0c01c0403002d902c8180d005c588011400200001e5000e80402d80e04401019480704100c0c1d0350300d05c0103040c5c0b00c4104407001440401c84544200007440c0c00c44514680092000304141440944030810089034002c1e41c910801002650380b0004042d032000c070384041c5a0b02550203012151865943d88172501403404a0130210024003004403001075040d9540c0500e401c1804180002c0d40c0d01c46025009200309148980040c401c4c103004603404500c0c00603000088100d040c01c1d202250744250200c91500c48809452030005042007603030b04101004902c03921007910800000301308050910107441d0a0507100d6103414003106004000300610580141d800d034080c0c420b5200e490140d10300d00094000c1c980d400c2842c2201c0a04103002c0310640c4190304900c15801600d2501d81008410142044d150700180e000b4001800440200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 801872311 1250 801871061 801871069
    0x304020919150f15170c0a05070c081f1a1e0a12020901050d0b19020721080702010b030604111203040303030b1e060324030a0506100501210e10020f191d 67
    0x1e04510500d8a2380c1080403503500c464600d01240d1000c241c55004c1c120340307203940591210405048402ca241080600d004110148a400c841040c40d44038204103000421289a01c80104a6150005114641481e141c142d01c03255003024100c140e005040c1d6000109807800d0a00702e100c04507410611080c0e1940e0b0f00c60001c10003150601200d039103a0f800b4481e010000c0c0006004c00c400c042105000100003113040b20040c55220000e004000310b80c1441503c41ca40e40f000704400d600581c1040c0360300d003c101e805011614602e4400100742d01480006000428140d055001c0c0105d02d20481e81803035218460420b031a005022a130311207038000c1e01000458003098909941d4007800700d0444008005045000010b810500310713600661300c5d9003101042000c400986900800a40b100b42008240f004110550b1030200100504007007841c0d50700c01207150b4402c01002168101603664109654038004a8101d2020760081d104954045103141202c103142c9010385169490141c070081d4501c54005000208 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 801873561 1250 801872311 801872317
    0x90105031603020d2d0203072001020c07150224131b120c0515090d030908070603020406080603010c080604021303060c020d020607050304020919150f15170c 69
    0xe40c1403681c01c04c41a0003064050040c1c0d02d101c040c1314075180094440b80c80c9010032403440740c040020a40304108000d84260440a42500d0940c0f042020002c00300d1102c0c00760091052042c0c80c1450b12031460002400c2c011801c20303810b0000c040d401e0750341001c909005641d0703c2d8022081880b20701054400501201c800c01711a05d4894051110b40e040e4512805655203120303419000308131084103460324541486190700703990300107040540f00e0b40d18541c02c828601c6558040d20403030a10611f0401da244c01030501c01c0941001901e440c501f81c40d4869075841016009500c80d10032280450403c03c000f072040e01e410320a03541690450307200d4244564440c41044000d6000b40340c9003102440d82840400440d603540b0518450b101e55030000c1c80d84a20540020340b400350300604a008210003001001700503100d6150560300f00003604003145a020322010380401500b44c04800c0c0d0b080e04140140040c07a42c1080c0264011a4a0301c83c58618050346820220340c1016005074002803402030002140c94000e0760401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 801874811 1250 801873561 801873601
    0x60816080102030c1917010609050a050f0d11010927050a1401050f0d0c23120a060b0d02060a090f0605160210230406080a0e0a0b060a172109010503 65
    0x880f06c0c0d0003011100c050311030300a17044140040d0362200c00f40064205018200040c01c0210b46d003000c00e03858800000c24111b8849402494900b0807100118142d004401200180907207889a0048180080e5842480404000131608003030a001c0070500421070343c8503c903c43d45031401c048085a090200f8030a030711480e0380c016500540003080b60310120303030b1000500f0064940160000180c0d041d44000d402c2c180807040e4514414990440e240303281c4500012188019a0b100e600450340ca110342c00010030410128102940086002a090b021140d01c80580d030181e42c00c09001103421a1030341d6003110785015001d00036060185c0352001c2405868000490100d804061908028070026144000440c010000c66000650000f25090040c00d8000c0e400d076603c0615401304002055400310318583d03c0d068048040c20703846000d808500039868860031600038000a2040f5004c0c0621a0082c0b41c0d40e010411100d010317501080300147c0c0c00002ca9080710120340c0140d69280c00c644802a480104000e4040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 801876061 1250 801874811 801874817
    0x602060603010f0227130c05030105030c010203040503100509010219031b030e0d12020d022106060304020a0302040c0c080307181a0406050334030c0804240b04060816080102030c19 79
    0x712a503d1b0300036800b442200b40f455036249a00d0b545000249440d1001201004d810754005110922507620002820328600190410102c0c0301d071180c20b00c690080c843c204c807540c15134805640340500071760142c000d403070459414800801172441850044049038151200725070130f40c10030a070502116100391031184103d8203010005241c0062003103c00101da10035400ca500303d050703040c02c44880848a4903805d600040c1a10f8403803031450998001200d4172041e010091159079030310651009035200e038854694065000348510341c0c0341402c00020b0141100490000341c0c09500384408541c5042800c40000d034050305040701404c00d41401c40a50b038940000300040c0f10030347c1c038000c03410101d00200c2c1c00c864640c410300c0c503204103e0000c4d03a000703043d82c0c02100e6001c2449108024003000540b84d0f001043c5018100010400300840c0c2000c25010302254500319501504080300402c1840c00440c03002499448815803014190b602c5074a0703420703400100c5064071045000c1c000700c4d00840d1580a554a55043d602d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 801877311 1250 801876061 801876079
    0x1060210230708010303020708030c06160e090129040b070206071a01092712030f0f02070501060e091204090b0604080109050c100201022d130602060603010f0227 71
    0x407001c0003000c0120340e407000140800004105054040c400b050203402d0405c00345244c514071140300c0d81c0e551006401810501c58510280d015a41b09401030107507d500100b00402c03ccd60f5400c144108940e944c0310705060b48003083c40404c0244224000c450480d00000b514901300070720b40e0200082908008030503201c40d040c424001a02045800c0c00d180601a442d000242c00501040203d001c2102c40c00c4c19200511a1425180843c1040e80c080c02c1f010000d01e801300d070b07060504401401038003100b54055074050000c580c0741c08114040d0015003d03640034080141c8075545003880c207552400391203038011070f9000410080c0704020290300103201e00310003d040b6514040e81c594103542101d202e1013044d44c1d25080030b890409186440702c1c0e10702410480d84003e5081c2280842c04140742c488040c0480e0300465480048c825604004080d6000e028a21102208665980e40003035110442110320034030a520382a06020400d059100351600c001d846012400c558048250940e0042c6030104110b512035400313 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 801878561 1250 801877311 801877361
    0x121a0307030f120306080c09090309030f0a120c020114070f0b09030d060f0513180203010e03030a0b01080103121b050d0f11031e030c0d1104060e0901060210 69
    0x40240c03200841c070800d20544914030a06000d4001c40d04200510100360405500300240000065000001c0030200c50917101a21158481c51461090580c0305401d80910003a40322402d0000c6085080c1c1401401002107011550104440000300d000000b4040f41c9881800800060440003500101e03228041f603000c04c50480d11043c800d50021901d1042c00c2d031001030180300600c45030107403d0040c0f40c0b01d4005c0014a0030f104c00107098050703041c061074916075601444404102c0303901d049222950041e000300b0110310491040c9440c0d500c11074074841d5460031720140c040c480d4484c40000d0304903030b0010a0005221220b820440b81c0c01140141d02051032004481c1d140031400501c03881d1410040354413512100320301c0b410302400c1240b07492801d100a800c107004018400108052000c41401d6215440d1303600d0b42c0c0c1990030724542c068221810340081c941000c940302c503094840100b05545058882c90070406819040100c020805d000b01001030f00845840c1c864080c2980201c0c65110f02e0040100840c0c00c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 801879811 1250 801878561 801878563
    0x40e130807020904080d0e0715031a12010504260409020c252303070611100203070504090612051f23070f02030a0206150d050139121a03 60
    0x292420f6078210400100746c1c0c42d20351071384038002a0226090282c45414540703000c03406000c54200b11001416202d5000b030784100b000305048042600300400b4919680386001d084c034000c0c07404481c02c41e00407508260203030b268407210a505010342101702080f880c040c01d000ca250b010390400d102c1c018951180920707051140030552400c4c04094034400841213264680040402e080000c408288601d801c1c120010b5420380300801c0c020306841450a000052200c0c4d19000d80c5440d19250711802d03032500c0801400080d07a4804001c00031107110650600100e41c481551118014041c00010701c550f00107884440910300c03141c5500200c1c3d60b03451000440d0420b01c03d030b5400c4d041c04880e81c00147d07840b80781000710030b0740c001d410a1040d562601c021810940902c002940da0304000e480581c504500048010180d034030340704804001a8420001d005080383e0001403902d014203000d0343c04400380e0110800b2005000f242c0ca0b0129455560f90b011521484e5110f00f00c000d10380c40521007443c0c0320104040801d620 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801881061 1250 801879811 801879829
    0xc030c1b031603180f150e03030c100b010f02100c0e030a03080615090a03151104030b07080711150c130e0f0c03010506030f091e21040e13080702 64
    0xc1c001294150b6030718000b00010715801690300b480c90042403e0002c11005160001500c0114003141c09a102c002000d5425410703980d0415030520000881503207034000803e00c80c0507a0004142800710500d11030054070700560100740c1100503401045814261015a00030501c11101400d054503500d43c29000f00382003083c034000030382c0861590340030f010290030840e12020390015030000300340c100002940050f4190b00170344005040200c1c2c603001d010000a580c0e010414502c01445040c0d40c4079520301c4d1041019804880702404100b250000445c418003485140e0010030900707014041c0080c1c3d00080c4059200d003e0b102c03e00003402485040d0201034440724030703005000c649021003e41d00e001c0320b041040a80003030051054540610040000b915408156904502494040c840c15581e040c0d14500e40520203002d044d50a48000d002103802001050511045456582d003e00314030b16224520700d5407149215900d1807842cbc1e5000640580716031010f8154261140412510705400c540000740500c2c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 801882311 1250 801881061 801881077
    0x190c050a1713120f020c060717180418030e030622030903080705030405031605090604020a17010f051003150510110708060106030b09060a06110309151b060c030c1b03 73
    0x142c00303032004c035070480d010808040702c12400c0701d1a82c50301d078441d600c4100762455417044000c04400031031503403c4a148001c00383c101c1c01c0040d0007000440103108403000707840c0b8000000e40118486000345080c508011504910909000441d1450700b501001c0661004071220b0083d42040160a408000200d640c00100300d0140100c0040d03890b03e04020405060400305246d103240745580c03e81c20441a2075100505502000440d001601d079280542c007511109603480e400c80042c0740c1a00041800110030501b5015590180c9540b41c07241703a8000300341c040f0b85806401991110501c03030208014074100f51104c200c99001c5c03808500000d103500381c4600d84810360700505180d400040044c4a8182d242c0300b088101d800440d01c10314a0304141e000b041c1c3c0c4142c603000308010006030324280c001402041080b205403000c003420300500d4a1180d42011180d42040c0042010807080700c01c524503a8034001459405010b00a80c41413841c7c4640504091651003c900c0441d1050410400b0350007034001c0c40503004070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 801883561 1250 801882311 801882317
    0xc1101031107300804060203070912050106032904022e11060a0903080609060a0b040f0f0f0b030f10030b04080702041413031404050306190c050a171312 67
    0xa2400d91100c4048503c1c06030003541480d203c40d040e41881c1d600a144940198000400582e65220801e0480e00030009070002c620140054000c0300800105500210407607000d1003230b4290920341c2d1040303040c244501100641c603040c0001701040c00341c0b802011110007291080e984921341040d40b1016481980803203224800b0445031952014000018040035034400200c01c0100602c402c240e402030100311014001d14050140380700065180e07201c0640c03074406000c0710b884164a580e03072540c1e050711040032802240f690805401c0300082441606071040280d0b4003412400c4e041d965080840401071200030b00d19040c0d45203805000010030344000d00c2c203008a010f070b68001d55030f038018010700013926030382107c41ea0707110700c21000c012070308440c80f4940d090b690f40761a1a204400140c00c000700e85d806a50000c4e0f6240c01070100344192072010020800021444610074403800b032034010280e90740c2c0100c0e2100808510046c032a0114400804180c1e9071008001210080d111041c0e154400000c210b000c4003008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 801884811 1250 801883561 801883583
    0xc0414010806071b030c031205010b09030f19030c11130b030c100807050903010e06011217030114010509043b06160309140303040c03060501050306070c1101031107 72
    0x554007061040a6200d5600d05108075a507428940c0c02e03640d945054405806c01071602582c1c0100341c07003103c0380c502c0ca200d28a02030040e540c541c007000d8000e5010700a003a12912a1011340b00b035981c00071500c01c0d29890003840107020a0b9940c0c4040d204002505400c544041d04c54114001d20364551302c15041c07000d100000000c488000c1c40500d850265080300f00e80c4160f40f00141550360b00e5000500f254000f0092074040d031a410440c0100f400b5000c0b1004001c2e0600518002054400129003104010380c080d003402541c542d502e016075849884280514280c2402503544d924080d4040d900810740d200b0058000070b4025450b41c10440340c83c40340542080d15401c28036003141e80d000712421160041422401410560410200600c85030300180011070030706440b80034800c02c4c0311102c003a885914440e601941d0f81e030728081c54014515901408111402886e09001041034100043c51622641c103a0f00c0303000594615858001d030080002e015541055212010040d41f62804001b514000d0b20880380c80d41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 801886061 1250 801884811 801884819
    0x6090501030f0216260705011a0d0b010504050c0c06240a050f04051f142b0303110409060b130b0306030d030e0703020a17120405010903140c041401 65
    0x2520700c02c640c1c1c120254014051106138803101e4241800c429440060810214203c201c4401840a00c0150201e01c040108125052104c10f400c00c0c04540c040b160038034000b42000080051106000c0c0c00900700360300d548010f224500340361b44042c3d0005a28031042d814076040032440d500d0034030100c4a480040c03003004028803004152008041e81d49000302c030561030a5040c100810591020b5030745107449546c40e1800b0030901750480030800007040c80400500038903500d45041050301c1e41843c00d0f05001e090070083c40401401d180300a0403105244695039000d400c611786007103000d0802c41c03000ca4000342040000248138500340c0304200c01040c0b00e942041c1c45114000f14115000d04a80c044071480380100304001081e40c0110303900038559000d080c0000e5004414129624040003600003d41150001700041801d40c0c220074488446400141241c98880c40c41e0043d41c043d001e0b500c0f030704c1c3c082502d0072020f01c00610b128000002403d010b408680e00c984c00000020180c4281011784100c1c0544200144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 801887311 1250 801886061 801886067
    0x25020c010e0a05151b15041103060717061f02010b0f0409030f14041d150d020102100e0f0313080607030603020105040504050403030b09090f07050f0a030602030c1306090501 76
    0x9460700008482904800f8038000c04100100c0c43d0300d85040f03a0301c0000500c240c1015480a003492200c3c1c43d10102e504009554000242e2144c0a0381c083d038011450324074189640c640014103038400c0c05241d40703c800d0151442c084000a034805071420385c1c4008080c5005c80f1180000312551070b010082c2e03001264030815a01800030407100d0890060150b41425102c20100c0c1d0090208100000a480d1801019560b110140414000c82d0000d400f4880710000040341e01750b611040314002c0340300710900000400004200800340d0725180d030081c007582200314110000640ca511680b8044012000c0e10701c9070b0301e03101c000f9045a0102031035070164401980148a42502003000980c052072a040030030a950958001078058041c83c814144541d842d00c001504241c4241c02510b010740025200d0005420710641c06500c2e04904403002680d0301c12480005001e1514600000a4200c00b40494128605644174000694001800401d21000410280c071100202d058400d00824455403404d0708141440001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 801888561 1250 801887311 801887327
    0x306032802030d0f0f05040b09010e0a09050c03180307050c150405031e1c0918061e1502010209010c0b06220c0206151008090c04020408160602060f040b25020c01 71
    0x4170070000248014002040c0200c1100c01681c000d08080d0302c880c4000000410205240e00414491810141804542107088020b90300648140c0e0100c1e0b80b60f01500103956a030b014200019007282e01603050307413103030381402c601d105d5400540300602032a0076114004203140c1070f013205d1609840c00180941d0789102d241403241e08440c2000e0607541002c0c8407100d500030004009400750340c00e803c080d802c0c00b02c840d00700c607072050f03000702501d5452811844001850318614000c0d8840c0d41404a00c03200c040c107280f8070610817512210016180c0c040c1e00403640d01e42031071050f8001c01044d00138125604034070202c2c423501e104a00c5142410004110b582d200c8170b0003130401d1805840403101000c0007a502099540d100300d03074984e07101e41d0301d003200031542c03003100c5103240800c841c403616000f41c030018001c180501c0100380310548100510709040040d03030311a022031b96a001100e6210991241c5c6000c5400541a551039a400800c844a141c1041d545100551a1108030341c17608405a8030000078180196040000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 801889811 1250 801888561 801888587
    0x409050303042a0311010c0b070810171f0b03010e0303090f06040c05090a0b060301061d0d2112021b06100305031c02040801090c1a0306032802030d0f 66
    0x450303180001c070f6000300341000f4800d01000781210100c40c10088242d105e610040221508601c8040590800d104082c040c1e010549000e22481d41e140380118014489580c00f440c0810400c1c010096003100030317216100040c2c0c90030209012074807003110740e0181e0740c02d0042120346039000b0061681c905104680707034640031402406d4101a0403072010400030880300354181044440036a40980c3d030f50365905440c4018080c259081d5804400400081490343c0d000c140c5128018600601d144402d1031306003002104000943d00604080d4003a5824401d00c04014201115104034100b00501201c0d45038848242d030048540c921403c1082c054000e4040c400b040f5440e006614880d00d5038645045464058407485442403119004c1281380c1c645109010947c1120f0080c54150020012a0301c14a880c8c60004111321942e084d444030580c080058124100c122402000020f008280d400b58840c010301f1421054030302ca010001e00380d070541026072014884001d4900440c2d458440c10400302d08060900350307450003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 801891061 1250 801889811 801889853
    0x2070f1511190204091104060b0d230619030503070b0a0c03091505060f090a24151b0f0c08060c0906041716030302010507120b0d030804020f040905030304 68
    0x302058106140c4007425802c690190b0740400c1102d040d0601000c500210901c2c9500180340007400259000150060480301d8010701083c011144203036024040c0b0740000303011284d000c00310400301d20145419447e6184405002c02e0742000300da520f031901e5045400900050711210604410000744c601340f031080749036900403400c0c00c10000281d503d5411104143c2c0351a07100b41179451001c0f800694540f181d00c03081d610700410b62000ca142188051004c1e01c40004450350004d00b4024250092020401d0354095609058154030790403042030f8200c0d07603442084819000c40080110000100350a1810380c010309008004040d4181d180520b60fa00c3c1c420010960011004244140806584d500c42282c04940440c4202078402c4403e20207142011242c0c11503901d503a1070750300004205901904080c1c07003030751580c0b030701d6a0980c4c00c0752444090701c0084001590100c040888080001e000d081c090f500640090011a9001414000b08044441e100c4060304e09600c040100010803410881c1420b03108500300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 801892311 1250 801891061 801891073
    0x90e190f0207150b06131d070206010e0a090309090f09030801080606061210050d050a03020706090608160216080a02091b030705070501020903150f070804080a030b0102070f1511 78
    0x184860002c02000100e00f4503003034a8610305011550f54000f0f50f564490601c20940c03410f5907580034110940300740340c80e0009154041c00000c43d00740c00402d2240c12581010b10000300c1d540d076004000000d0008020840502c02c040e40c01040d154220b101d00c031140345150000043e600811f04018061392016403002c0140c0d0302400400c1201e0702c401d03080e560309040c029006111501d40c450400768026094001e40c0c0c1100240c5800014000002070251500f400b903000ea5011507101c10046a600041c1c0c05440b01003048031020403c24201100b503001b08907150b10584100030040c0c10b0b007005824040d031050540703a000703500c000227501d0000081608910f0811040844e402ea800c1d0100703581c000100304a041c000f002c5100800e0202c01e4045605042004064511281c583c0010343c070443c1094816080442103880003c2c481c6001d174420f64020b5801400b45418422954811000740c42140000f80c1103003d83c000001d00495810132940290050405a150b6820a9038000303007000304109888003d50721403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 801893561 1250 801892311 801892313
    0xf11120c0a0b0d0902100503011a190815031203010f060801030203191a090619052514040807090e0a030806010f050705030a0e03010c11120a090e190f0207 68
    0x7208800704984107007402c6501c070302c480c0b461031004204c10440a508007660002c5c2c4811070b81d01000440c16103d06036042041043d141c034100e603990041500c2d191100300206558050980101090b6500402d14801c443e8a01d085001090034560000d40d02100c03540040014040751081794036820240010b4079054140e5895500020303522400b440c00010302085001000c82402001a1401d0800441a2078030545003400c00310643e9505040b03800140b80c5d83c036540106004246030003158016645801c000d40c000040300c0124441b540980c19080a02c030340c41c034008581082d040040d000410034580036016080c60620880291107000040e509190000e82003040041e40060380d036074110388203180024510f6103480701902c03107104003000074019100101d801c54140d0b5100d44440c6550209070024080c4124110080e1202d08440c0711114054022800c40c06142e41c02e5005086510b0a619203854110354071112020001403c2d00c50307003800d08c03400d0660013070030015002e070002625410104520300281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 801894811 1250 801893561 801893569
    0x14010b1905090403090e09030d0c0e130506041d01050105030c0316090c02031c090525030b06061303032d090b030a110c250503030909070c0f11120c 65
    0x401d014a0344038481c040041010715104a24220181c0f43c1502d42c030145041901d0120307502d40040e140e41f90368a0a10004224141c440c49811001c4031018201448020554851401070040182543e400c1a071b648101c1c07601c60441c1c003203e9848402c4400014542d41001d051509000c0000021402a44440c1e8058543c40c042241d040850309000000901e94580c804c0032070841c810f80c4d800481c2c040c1c10f010681c034035030003552009400f10310410845603440b1441064035202d41c40101c0c0c00520001403d020030202c0c007400d01840e40308400901591501d41c003c410541c2105090b00150300040c903541c00400701740c16100c060400b100411107010a5581c00f2140101001d4080c0101020050701101094800c003042e041860902501c226580d03d440c000242d40eaa204550030101c42000c0d50000000b602400d90b0030712038141e0300c010f80038500d44540b00d0103001701458003a11010422545a07580c1002c255040458201c00d44104020800c0b4001c1ca000c000817140d406c60305d1182900040681070696035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 801896061 1250 801894811 801894859
    0x70e12010204050105030402061e041d0901060807060507080d0f0e0d080f04021e040c02060a150e0703200409092315090307140606041d030307050706020d0914010b 72
    0xd03048440668601651100c2d6161242110009072b0100000c07802081c9010b040200c82c0c41200100d018030313600d07a00c210416003a9015032140e20183e0b005a0424001c640c460030013441a60b0140702414a1715810200107002c0f104000d1101740650350b02d80c64295000c505210f04808400c0500d02001a41401d41e100d070030f9400c0c042e0000348506140d002400c0c010040b55140d03001448020820420080d02c0b4070080d4448900722400078002d03203804c4000c2014000780c0000b009913510a89010119516a41e05400600d0710104480001720040c603400c2e040d441140040c40544070840011802c4140e51a10f00a29003840b405018805070b45014600007800c00070340304c0740c00c0c0a5480c8007002d40e15221156403c51141400c0505280301c0c00311450421100090000c0c005d000540302003004074040d20701117012000c9840b401d8115003040000c00c8900344584043c105480c05480018030f05100041410b080700d03010031084854440c00000040c01d04004c0c451031070805003c0c1c03452009410b18020313903603c3c05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 801897311 1250 801896061 801896063
    0x105060319021204050c0109081005220c03020a0e281b0e030f010c050f0d060b040e07110f0c042f0418060506090d03020a0b070e120102040501050304 66
    0x10401000180c8a49018250140d461200c090110b40e210b120803140e03070701503c0844c0c09030b40d103100e4141c6081d0342e9403150411004481c0c60101070850303c0e90501c1c03990082c1902600d0b410288891001c444102e100700307001904690b200e02c0c60542c4c150f1841c8140149170083d80d20100800c280101003140300146202d2000c03140c0f003610040c4444854607028803004000c00309000e500300c0440440a01040e0700501c20717102e0010204d0071501a06281d504407801d032644015603d00050301440b1540f071581412000c1d090709003620b0004036103281c07250003070141d0360840e50140d100303100c84509100b071254109843ca206034043c5409068070078010a001555030145a0005009070f80d99510000c41c24076609038488000b0300c0341800c0b19641d00d030707900e003080c1030704a03001c0c02c0540d04584401030495a2300b842030030700719907025007400d0034249500100030311030169400070390a45c002c1d0704501c3c00080190360031500c07900c0d450303d840d642c882d02a000e20481940c003105400b081e82c8100414003c0d60381100582c0d13441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 801898561 1250 801897311 801897319
    0x910050f0c0d02340512070203031b030d090804241b02040e01050a0209011d0108060d03020a061113050114030c090d0b011d130b0609090c0a1d0106170105 68
    0x83d00c442800007031011304424210344460350789103103034640300c0848010118031401a81141d8004a07442498041803142002c000d6150384200154030f0102110300c084103103003005600b075134200604642d25130251020801d04480100c00060140a6404521003007040320407942c400b00440e401e04540541100d050780d20b1105039041c451403003421540e5a0700589400c003145002032050b4103040c0c00c92800303508962141030215010107414031031140b1403802d040e03004c0d105035508030540c0c64001c20720604071311060003034045006d0b840748000494194010040301c2c09195003c0343e600d04020401e20141e60a44e0001c0381007080014000c04078070b070180143c980180358040c10390369641c038880020b0075100c4103840080c0060010400025140e40d0003e14000808440c040340300e080d0755007058000701c607112820042004403a40301003507080c20071290103680501054100d5504060700d400113a9581d0031039000d0154482003000d001840c03800500980e0042034642411165180351840118812505001e12401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801899811 1250 801898561 801898567
    0x12021f0216080f0d180f1205070519021306030309210210080114060405100e01020f011a2112091504140405010509011d09070503060910050f0c0d02 65
    0x6001032581001c14101d52040d1940e9440d0701e100900040d0307400c184450184103182c0344d041a1000304505504001c1503124a100d0503901c0c031940d860507910311400c0914200f1406101070740008408000e1716015000d40c043c0d03c10000441e00c1000190b03112245c030036255504058041000030b17040329803101035520b41070910a803514030300d03000020400f80b10400b075803215080f1005009503400c000020705850007a280c10409840c0c072003c0c844140310740e10800e03802070401d5000ba00745611840b10050740b02030500c192403407040460f00423402c1d104140c2c000143c440100b0a0f18410345400d4440d03480c3c441e0485006100c04081d4120b09481d40c008811000d94640005600d036016601d0301335281200252034460303510f0f00d85400c041948a000701520b240100d00c2e050011829203002180b441c1211b0844003100580400e12821f54511840988181818030a850000c00c1980e03061083c00d105044000007040101c401c0040002076444c05009691180180c0c018417031000003000c21294500104480965 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801901061 1250 801899811 801899827
    0x40f020a1d090136020613060912170a17010b0c0c0d1a0c07050d03020d1d0c04090c0b04030b0609070c21110109060c1706181305030c0a12021f02 64
    0x411100101002075004000080d407410007044a4071042c182d40701e507030b100d2004070382b1034403040d00044468401030119000040b00c4c21700c07094040010007009010b464800f010000b69040320308142c0c0c0030b801518007810080f42410a4800800c011808041e04407441104040207440f04181c07244085c06000d1800c40e02000108480b10403800c9648480d844003c680d046264054002c00a4004403600c1c400682070001004084050003e00c562040070030014143d00b40c165004c1000500e40c011044400c0500d03035100242d0029801d000e00300450003690340001620b0850300b000410301008144406000d4280c041a000c104d036455866600b882c1c07001c04212083c614441a110344505400829035982042502410001c2507089606400c019448001d981d20700c3c0f52000100c06c1c801c41c0c01c20740000308699550303140f00c021451645c01080202c1c1502c0e811a07d40c46a9041d548000c000c880d841e440304080500700301250084849400d040e1020700200d1010715410f10300c1d0701e0900401e0400c950045807040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801902311 1250 801901061 801901151
    0x11b0303090519031e050a09150e04090602040f0b0a1d01090909030f0f0f02120f070b0708090705040204030f110a1214070816030b040f020a1d0901 65
    0x141515840f40a4000079502c518000300181c006a06410184405003000883d8600420580b00c66500c5600c0b60001e10b8204165072905010401841c41007203141d4462400788e0711a8844c0100f414007d00c40987c3d11800c20300d00c6903245181d948203644842c01000000880c0b03501c1480d806202071184112840c039804400102d4800b0b080d40c01003549149081251030405420001810071800d03107440d403494002c10440141c458203221802080560000e00c0f110802e0600140101100e0700004045410040300f0f49562510300c00403214000468001ca06001c6582c0e42000144020a000c40b010740c681411695401d480c1c5804030700040c4804422101000150396118111019180020032030150008504060750700551101d6100e03c1030207890000315000c917010031b9540042e080c42000f030848516603500c401d10034100a0056609448030191000107981d822a2a0000d01080308001e220411004501c4c450900103400100f0680c500200718452200442d44d031005520512021010711401207802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801903561 1250 801902311 801902323
    0x30c06111b01051f060f081807080a05010e07050f04020c10020c0312161b0314030a09120314060f010909050a05160206091e010b0307080705040b011b03030905 70
    0x210701c1c54007454150000300c000561041e4031a20041d0ba682c04207050002510b12804064090500000d00000d00444054028000320f6042201564a031080070100d0302c2190a103d52034205070300d6034200c012110244042401a241c1e5468072001900c0c089217004005803801c2030301000d09000d59008241104004000c2c000000341e075190001c03c2d507903003070040340150700c0764009501502c00300b500318082141c00074101d160600714030241c2c890700b200004550300084003034040e1408404000d4250419000e0b207043c000618000d072913840c4045036030388980c80c16203400802180c0903002c25252228203010ba54103060709640080040c1d80c4a040110581c00490301c0a0302c1d90004100d40d0308090034002c49004540c41148581c038248941140c180069400702e84548003902d000d40f150303021120110f0b0b8282030040c650070070b4072020000907001044401090400007150304c0802550404402000682418003c80d41c54810918000d03014604c0301e961030f00f10050a4001508255aa00316442004010440c1c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801904811 1250 801903561 801903577
    0x1120809090405030a170603070308090a24030c0f120f150b1b1f020d0902030d171006170417030c04060f0f0e19180e0d0903030c0611 59
    0x20000e0903160500f002d5990754080300044001540c00021804450782c42c0e00094003c25006010340a206d00c0c503100da164a80217a4400c1c2d44c445091000010740c0040300744425a2105107921500c8483c590441c058100c504800d80c01c000c0c0040419002d042c00c0d4840e138422182e20000030001001581e504094006155410081003442115800400e520480401810f082f9003c0208440310f040c90040d0107450307111080c905402002d140e241000c1d03003481e68000e45101e940c03101c400980801c1580010703107042004501c40010130400c40c0032500c40180035454603800004105400c0c1401d02d400802822780700200103a81e11000c1c0d00000c1010004540340e161445000f5005444c0c90b4100b29810f600a54000c3c401d480116081e1900400140c0c05290112032200d000e80f00c2400420105080c0311109483c501080388500912002042109070fa4070300e96400d00c2c184400080101c00c80140902d00070400449000780b1500210400020798056100031015900120108991002240465030b900884103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801906061 1250 801904811 801904819
    0x160c0302101a10030c0c0311120304060c030501092c030c1c0f030b0f06031005060d020903010501050a03120f02120708030702010f050402150c0c18060901080601060801120809 77
    0x118403003100d48860403404407000210f031004020f80c1014401d070220360440c030881010580e4940c1342c0b00401d0043c03c80b86c00c0b60f01e1907415103505104951806041d580111800c403680c5640360519490343c2c0e031503c203007405072070002c81c05c1101c00e0720321500013500381d495034880c000441c0000300d000340c802c0140140c0d040112004100d0b1b441c10214401c000c0010700c4500b5120000b40c18500440241c0d100f070150b502c1726500501988800c13030760381d800e000306648000d051806d0340d5240c840005c1c8a0325440001d20f205244480d0050f1290701d60390400d402d50304181e000901c4ac20314440180040740c020f8900108080140c2080310001030300341c4042e8145001820000d012400c0420181d0131320680c04001c620400c81a80204040450016a00100c44d000e45000c0d4005a10303201707005c0210b840d0001040300f2418942210301014a150024401420345040d2031004000790051000500301900f1882c007402c50340e80a4007a940c10070000404620051003004804101100840b050080c0d0308100d030001d4138003038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801907311 1250 801906061 801906071
    0x10303020307050f07050603040204181a0a290d03021903050d0c0c031409011403040f02040501060518040b0a08010f0c1107030b04020d0206160606080114160c030210 73
    0x414041d489401898040d600c0e4051075841c00d0405501191a4060b42c0004040c01c1c2541caa5409102c01490a100005070f03403004080448042414041408c20a0300701e5211700c211850503025560030343c0c150a40e0340e188900d20f602e040001d00303122078445420103816918071800850b10704080749460781c21507e85980c400740c064036400303069100c070040c100380b00448010302c0101e030031400481c0c122114020180c0003403059000100f00300b001400030480c0800500d40080001002d00d02d403402d5a0085d60f040320b00039280d64108086040a0207854014503c50034207509141e10500c071034a070101c0e01d54455100320b0780e4072940406503454882c0c2c0009015540c008002c2c82084e01c8200d07000784a1070a549001c0303960041140f080c3c000004001e42034a621170407406042d2115424080744881c0c0740d0040ba80410f0074016405001d40645a4400c003500805020841c6450242898215801000345108900703103c0104004603c41d25000200c030081ea103400d48102607242407c0307092102894842403034500b08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801908561 1250 801907311 801907313
    0x180b0c0f1612170408071202070503100609051302130225030203030414030a0504031e050a051f090804030f150c09030507050415060f050708030708271e150103 70
    0x2c58441c1481d48070a807a0014440c9840c00d0810500781c003180c0003003000c00c003040094005112020044401c5201e801103076542c5031682d0001c0d003040c0106c146414501e548030780801c580080c600403150806080d03030800a0b420760300d03001b14814100d4030340a10411900020b14030080c0840b40010700e440d042c120180c210301c8000d40b030000c0d180d03482902c0544038001503020020b00c2881c080102c80c01c010345500c40a2419185075505022484442d1070209519101400781c000306100b07000b00c1c0c0c1114410000b40c10303901c201080d12003503419a91025920686043c000b0030001c0d0005044070140c0b038210320090460546460541e120819910641c80384900f0890300303c2c080f54001c40313044142c038412000d8500d10b079182c800380b00880e0707008264449503040310231080104a009070b640d4600c0d0b843c0c5d0b1410038034008840d01c91000c1640162a2040040c4501040289021081010800d0b2144080b406402032645954170341d507501071000c91010a002da641000641002049800c61007928514001855a92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801909811 1250 801908561 801908573
    0x30203011d010f0506030319032a02070e07020a1401150e010612020310030f15020f09010806061e1c060b04050306090304030302070b07080d150603180b0c0f16 70
    0x541d24074540c25820308805121800c12400b81a118844c050001c5007000b1040c1c040c4006c907030400c1d0707861061664950303a00b50311411104407080d14821242c801c3c2c052400c5000000e14010345603100008a07804007003400a210307404a00c4180d0980c10610f507035505018001c000b801003851340004c0054403443c22000852490b00c0c229141240d5a5484213886440108a450f040c4e20048a0084000e00918000d1001501e8042e900017036034010113000102c0c281440c000e5003242d10424074074060b4000865249c050b980c2c0b241e00f06500c140150f078040c0c2407500c1e03a8000d094004c603038003060390301603c00704543c3c211400410081d4080f04920300c0901c00f035592170f82000096403260190500030702800340003400c941000000c544c201d076456801480c038a4600350051826400032141181c2044040102d043c0505d01805800d8030840c1540c0290703801c514204010b01220300c800441078180150b61032050108540807003655001100000859444020340080d15051080c80302c0905100c0f81c940884c814809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801911061 1250 801909811 801909851
    0x902250b07230c1f060e0c0729090d09081b1201090f0c0603060b0d050c21060f0a0b1b0102040302120601090b06120402010f200328051b0703020301 65
    0x3c0c0c81180e12001c0c12104c1c0c54441924198081d4040502000010031030b800d25800041218078055001c081e40d252131001c10039240c8030a41780340201d1a403100300b400354001050004105c81c0c0040c1c00d1064119180c40e00c40c507120103800d110b4581220301c0048552868440c0d500c3d407100403810030001c115001080c43e241d5002181400c1c2960200c07500d0201140c014080d202e89825115101001400e0208240c1e0200140a00400c1910b0400f400c0c0548890105e40ca02140701610300e6420740301e000d20305138003440920440110807512419950a0801480607006c007203c4900000300c0780b499400100c0702059000e4070580d8402174000e00d0ba42080341c951300b070200d403c2d0f0690f0714002d024408980c0ba142000128012520400000030030030000c10019809068004056201410840d0448030f034035000e40104116012045000d070400100108c0d24440005c00c80088140c405203118210300501c80100140114108801b42841820f0200c1002d00d0420005c802541e004009104118000d011111041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801912311 1250 801911061 801911083
    0x201031e06091b0e1e0a090902013c05040314011d0d090b09041b021f021206150c0102030703060501110619051f0902250b07230c 57
    0x1441c22103403c0802c640d40072442a480425503803080d134800640201300921191600003942c0d200c07030400a13500e684909103400001c1c1101d4070001000300080c0009803419140c0240c02d21035400030019034094030320303a410f08549200d42d032981801645810f5016141c034450b581014203590941410361007100c4054000301c0200041e070108501c28001400e86507551000501050089606088207000b0010901c02030440c0ca1401000403072194002c21032500d0313442d00f500601005800c180360090140c05a01d2000d1402005600114036112154010003580c0f8800f0309010300c43ca0100320b4080c20b6405050584501250001c000c41d81e03428586c0000d00242807912816000c54240003503401540c0f00030036558860b118510f00320044c0c8007201d0310300000309801008204038505e002d203200c4e09040c900c0142d20103840d4150005070791340114070000814440c5140940088603a0030480340c0010740c040c2409400c210b00d401c021107404015020801c1c04039154840d5801000081591440340c400090f90312550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801913561 1250 801912311 801912329
    0x290c0703061407020601180f020703020d030506010c0510181b050306070f08070c021215040b090c10050a051204030509150906160c051c0c140117040201031e06 70
    0x1500101080e44110b00803520840582c001400400131a00403072240840d5001c448400507452110714034103030480e0480314090780103070f100ca01030790f640c69058070a80c1d170048400d003030a1310100f00c0c2e0741c2c544e6511014020510641a1103110310020710700d83c1a17150814a61104900900c50202800c0480802d1184200c610a218160100b49030728018144a140002559101d40b00780d07480c22015a680d41c1a038008a80006201040c403d21000a20100032200d8401c01568402e04281c01c048030592005042540541c04c8400c11920310741d035494201c81c3d1017800c1d040194a030001040300341c5040c010544066048142d020410041540c0400285001c500845141c002042403d654110340d020348188144c120008000c0d5030130703900d581c04c807411046108400741c441c1c05807038102091241e2180d040b504040030b0600300500070400307800c074848040d00702d0ba03d0608001800100080c820000c1c054000901c60684004c5025644640c0100c008400b8480040b02850301d03000310311000340402e11404c202 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801914811 1250 801913561 801913571
    0xc0f06010e0c090111150a0608013207181410020106031707060e0d2a0203030301091107020306072609030901030e21090a060c0c290c070306 62
    0x3040c003840020340550304407464141410f55030001512048128420190785100d51070804500420110841d0302c101d03100b00c0c002c210b0310b01c0c1c544900c0c25a251142c40102106008000240002401180481034080d40038130703a5494944400649001a8031041030220b1001d910010803411841000326100348425200070700345d2074002000320f0803039006005c028850b0030307000d14440012046d076024065071401000000341c0c00c0e001e0f110b031a207081203000d408404520b04403000c3d0034101080319000c15102903003090310724007140d9500280d02d038841401020b1007559540c4004401400010544000131350290071101c09040020014040020107c400d100d82d143c46041c1c28264003100e0b4074240240201c00040d8100703c8080015005030010800040407031103400203216940c0047e540381a03d4003200b40269a803100e61209114001c0016000402803210040802000813001582c1c002100c1041464072410700c00d05054000c035504059080c50400f102042c003050351000419410206e034410001004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801916061 1250 801914811 801914819
    0x2030f0f04020a0504050601030f050112020a08060c040915080a061e060303050d05220b010302090708010803030414070b210106170f06300c040608030d0b0402070204020c0f0601 78
    0x1440122002900003000100800c100c0c2891b4010320340000c0c05060100d42aa104004a0100c130000d030306c124014400c2c001d5203001d40c00e00c4081c68000d170101001030501490700588035182c40c41188507494006580c3c0a90401e01184080a00090200f00041c1c0700400d138103041200240007610112050090000384040b0075000380e1140d24126a07250b10f03114200811040880d0082c03800414151030280c0c50ba5004000f04507840710210700c54403c204c04081541580140f10070031900070b04600c00e1108201c014020840c00105481d400f66000031072048820348a07400500385a580c0d1701c2480201004600301c0300910000038850400c42c03244d00301402581e69954102d501c6160701a000040d001d03040003061200c503850700e10a501c200c02800301d507881d00c00e0182842c2880100180a40141c2c40c91a08602e0f0341024003121160500454042c0200e0f4141403d0b6a240d1190305c0b0321705921951040e079103d10b61259015540c1b400d40060046450f060344003d1640c496410b420250014000c3d800045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801917311 1250 801916061 801916081
    0x1b2b0207091e1b02070b130306020a0c140109030c12020a0b0907090f0501050d081e1902010f110f0d1508010b01020d0228020319260f120c0d0f02030f 66
    0x85510443c950041003140d2422404d50350319400009401003e041072540031012611700d00051103038036059a50142200c2036401d01c1500c9100002400385164145049d0341c021070f500088072000250000140345540d210107105074504480740300020410320342da40c20001492008110b0038101c0380800c0b07003804800c41a064000444030240280da90101c0000d120a01240103880a4044410890315010100f291041c4006180c5c0002440c002c80e410403000d81c04e5415420f015030724041003819014801020f5082d040d580c3d5029000b140d0840d0303100800c4c41c0d46001110b070401d0801e0400c92451000c4c45032030b0448203001e0806100364501611403029011110340c80000c038522489803111907880c00310a800e101c60311140c0d4002781030385c0c10b11500c19a4018031490300d044803443c40c801d01034809800040710650b040100c02c03915070920b211041c85503035550742100d4210344500f0b0070815820126070714141c0c00401402070241c0c842d400c0c3d15248c1d50310f12103503007030f8010f500030450388112800a540703403a0340ea = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801918561 1250 801917311 801917351
    0x10c060c11071a22080303090109060b0619030203060d1a090d18030305090d02130f06051e060a0c0b090303151020070b07081b2b0207091e 61
    0x14510000f010011110543d0704a0424499604a000c0c02450305699100c0c00740f668000381e49100c5141d41d038429880800680c2d208600840b4401d030ba044d400e101e003031122481806d4480020205041d00080020782555400d0f405241c500e9002400300713200d1020340122140d200c01180e00c03030600d02c0383c440d0410816025a640a01000416030106003a074115541250799400c54540290450b050180803401030b6034900c801d0762900d8030040d0020f880d200802c400c00994080da84564010703206c0702840520161281c0c50f00d500c2032810744001e5603030002841c0031600c501c130b03c140c040c0200d113a800901036514004070045005005000c00520540031110400c002c0c000040710f1500070601e09050540e400d440b5a010504404c43c1100307807881c1e107595040c42d1610f58401c00c8100d0f9404000503a0205503004210f00003440f80c0e000e0010510500c824080c20b400c1c02e0211241416040c04d0215180c4a5201304585009400007100500240d000c011110f504910409021203404d0b050182c0d01600c1c500070401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801919811 1250 801918561 801918599
    0x1903020f03013c0e010c1805010f0e030c0607080a110619090302120f0903102f0918180a0201080a27050c1c0b040b06010c060c1107 58
    0x20901c40e002060018203003400c102c0c038980d010b03854003c5110340301c109603104524182c0f080b6800861119044540107009074600c1c1c1c000592914001014007041e42d01207a4803c80c000e17941000700d240c41d00d800005e480d03c02c500c1c0505a00400018203041042a01d8028060030320594480f0494046a2003005031590001c942c40b1241d5504640e01c02000c8100b03030406402c0c1806401507502016800800c0301695010040c04200618009181c00041c1002c000c0040c0d810302103c0104510003034031096145185003421020170000904020841c1074480030106d07404020010308150b40c501c0f1a440c515403650046640d854034110b074402c089644040820b00d02c0c0c445505070349640e9982e071612264401056050170b80c0030050491451400300055801041c4460381c0107800034125a09000c08003c0c02c00c6400300103a40780c00c0c518801c00300086007000440e400c140e00405807079155450400480d40c0d80710140340542aa070a0020343c4210680140c40440501d04070001e55421513106c00c0c101c00d031078150f414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801921061 1250 801919811 801919841
    0xa08071503110d050f010515190507150203101d04030c02040f0b0d06140c13060309110d1a1501171005030d0806041b0507150b1903020f0301 62
    0x3500049040c402c0e4411003480341090001070a0910851840c02103440403030301c0145940701240140403524040480980c14000308062514261020003010324582e440d6900000b404400700725201000142681c4120100c203c0301c046413246441d03009005140614400c80050320b2401200214100d26413038001d00c201d40689a0403045860350b400c0c00004c00d80c501c009151720356610307004a0240d84180c65150198020381002c204130780315080c82082e8420142408614240410121015025414410b0100c50700d80c28001a640001c1c20000c5054402400c0c907548542c091480c4030400c141c8010403c0b0b4010001e44002403550f41c40310348082d203015501500d01080c3c0b1702004604807041843e51903801801c2c4a02c000b40c0b203541c2e10100c0e1601c9480d054841c00305800e001001800e00301032051042c0080300344401e14110f2034521000d441d52240711006444503406101005002d01141c2101c1ca900740302a00780010010403021034504001036000403031190f4030010141c0d07120320b030501070144190f070180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801922311 1250 801921061 801921089
    0x5393415081902091e04020f0a030230040b0a0b040e010e010f020a0e040f0608010c050309061b0f1e041419030c0b0a0c050102040303110d0809070603020c07080610050a0807 76
    0x20000b05c01500e201d12100e5030098080004007905105032018040c018a10748000d81c4485841c84ccc595014003800300c1034007501112100e0701e59420025203070385802130f40224041c0110f4840c030319000d010b0180f2004c1180c0060402032520389003841584046c040307005c3c44008000c032040780340c44a01680718103506040028080d0114507028541540025021050a0f40000f0b1050740c41c24076609580441c8041d034040b0b00c01108006a224041c08220b86c040200000007205005036200e80526014a02c0c00c00c0340200d011500102c614a8424804800d10395410b2140d1543c1d0f441c2da1140325441e50b0458940102040b0b0f42c1580000c1104c540311060302d0b40140304088860901c10300241d25004418a0410014070986a1002c18030078402000618000d40d655040d89030f080360740c54a01a40d140f10070b0100701e08c440400a01280119003001941c0291a0140e599014040c4a92501b00207030411840c50007250309003c445404803a1820860340180d4590007000e9a4145007901c403900d500c0f624002c80204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801923561 1250 801922311 801922339
    0x2100510090b0f18040b09010b0d03120e06042001080103020f0913060e0c0414070806010e1315210503070803070539341508190209 58
    0x580c01032440040b0140c034007030580d41042c00150964000704603401c0030758400010b2006001100c0d95407503200c0050402030000c840c0280c007240c10604583c0c0040c0c02c01c00382d200b034261882c03003d410040401c0b003a0001c83d03215080a040c080e4003002007500780490162103080140e400d50060307040c1d9040ba50000e04100d56902c400043c030400440040ca45600524516a4080014000e10640c01c40f41204030040a64007803002c2448110b0317050355101c1d03005504540070050050361062401d94001c10a00c7c0c0311102c217080d40041007106e4401040410183d050031500124695918040d000321044480800009400758802109840c1c8122014040f50400c0242e0400f240441004680050300d40c9060f40c50102c10429a00701208182c4080b07030700884641d10000d03080310ac8843c40a0b000300a802505d4505006070380881010b03105019081c00603920103842615207040410305000b0040c19a00c0e0300310585d00c0400400d180700c115101c6c881b0340d08070106605285464400c1c0c80200e171001d40341d54855003030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801924811 1250 801923561 801923579
    0x70503031605031204200103140a09061e1517070311010c060e150601210b040f050702060f0109060e070c060e0d0302091e031f1b090602100510 63
    0x60307103070103841e0b91004100602ca543e400b828214030031402485400c1a8003d0b007842c114104031502c06160405041084903000340c8200c001d165040035485500241e00e10041ca05100501a200303400e00044c91103411450141e41c0c2a00181b00111b54000038101d025110300f0140c106841110542c01c89600840040c030001c0c1e03d0701c0201800c100d05040c2500c0c099225030340d8100b562510741c0c808125030046692000d04021074041d1a4110b0403d017082c11580032110f094482e001301000419403202e071510820070b540d80703403948005521014401c061010303251291000e59144025601c140c406080c1c0d00000483c5c9019102d88001d94904401d0610651a0f50a00310781c4140c0e480c10540300c10f03503200c1d20010681800c0080c1110290b240c1c40250311000c098040040910003200030500e0b08a1100c0300149541c1c000c20500a414803040f5070094004804c2d140600400c2004032080700d040b0131200c04818280c000c849a02112202c2e0700b103e0700e0310031006181c000d4aa0035240030401481444060000c450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801926061 1250 801924811 801924847
    0xd0503060112060506130342060306020d05010e01060f0203030708040302150405060a060b090604090507050c0a2d1703061201020f0a0f090803120c07080307110f07050303 75
    0x111a200400c0d442d88800009999620006ca8803201082c5520104100040074a402e8950010080c0e1548440f04890056484800c15481c0b100d26003511090765542c128223030b010001864001c84210344462144418000401e400c4c0141040303450b181000103841e84c8039182560398288290f0185003503464010044d0348400001d8422001c1d400344640705e03080110f20344855889180600020443d0b802e21840d80000c44109400519030150300704aa0006902c0d440101c40468060303c4000030159500f0000300c1d200d000c2c03070ba850515405441c01c038409005a4260040f580d10588001a14400c0d907240c1c0300314010540b0000900780312250203440700020400c000745a103e100503103c211420301094856013207900102040ca40e21001140c200780aa9121000d43c0f4000030505118060382c4c20441020794034014544126000d10000000400f019503820035562900d600840303440d141d040501015200c603a20b5101d03d0352354411101c550840240004a040c201c45010f0087d42c5852403620840b50301c24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801927311 1250 801926061 801926087
    0x1180c1d130803103816110301020f0d0e07050a03020d03110309060c0a1106120c090f0d0f0b09010b060403170c0a0c09050a02120c090f03010c17090d05030601 70
    0x403080140010b0000318071030b01d210391104a111007540d002103075000d502c8501d418180c00c0d10308500a0207014401a00901d21282d11b40e00084000303880d40400b400680603100c0c0241a10300c042e40401e6516000f1780307541291216240c00c0050740c507190303125024480765464910000e98004a100703c0c100105e4054002c00c1120312070442a00c2c90425944042280c5502074100c0c2041030703001d5052001407000e1111f090700301c0c0e0811243e0741d26007080c3d0410203a0300c580103001007030b0903c130004480c0e00310303680c90218403043c441c040c0036600c039981035040090841000325401d0b00cad00400100004c0500708184070b100380c04180113040310b050505584a50348842a07240300040803c104001120031f00e001041403040d07451180c81d0f00411541031030540c4c415148003408403400c0b140144100e040280a01c4012a03103c446240c0c1c16403a00030440000f209803240d03d0306203405520706407075202d80719408064034820a014071029001d640750365505d180d481c1382100945000032818030110b0541e622525070320601c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801928561 1250 801927311 801927331
    0x90405040303060f0b2a0c1207080a080901020607090509070c03090e15100c0201080c072316060e03030304030c02130e0a0605060108040213050901180c1d130803 71
    0x3c203841e440d0400c0a01c00e203070440d0100c000042a80803120010010100c2e00c8002c0d4694405602c544c04515a0b03a403a05100340c0d0703c1407a05100c8002141420005140102080340484911b1301d01810304c010964401c0100c00d006010300e60004031014050881c44003103c40152040c80c140c1c4e221030088a2001ca403080480070024a507000040c81100103421901407600c1c00f4000880304d81020030025403402040100d8140642d616205007d030380c003c48021f52044030146900c0d03944140e85082560400701c1c1c01c052401c004100101081810006504200118602d108501d11915058291840900c08014641c158010800100080d214040c400149031002c0d00c0000c071300c0c400842c0300d02610007498103440143e02840903601404a00c1c05a00c0d003226081c24500300b00d00381900810315600700c10b4403401d90b4540302c1001c140e08510950141c600f0f54158407500c3c048030001d20303090405020354030515006940b208103281d220313006811124003514602e04204a00703252942c8801e000c4c0c10040182504c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801929811 1250 801928561 801928571
    0x501030b031603380a0b120606060f0f0a080105090703022701020102040305030d0203060915010813080409061e0b0f04141503010303120e07081e0118050d080705030408090405040303 80
    0xa00b030500c03911610103204c000c2131856928101500108a5500f0004036109107109401b0700d16020b00400c4003a0080170607591244e50b1214002650844e01c50303003009038600716000070019800d40d41700151134141c5100f144c440c141c03510754050840070790040038460600114080e143e004140e002a0610041d01d006000140c1030560780d8841da403d64212800079480c0c590000108052483e0611202da1302c1280316480003c5854000300080c141c0e80c00900e0059080d5403c580728050000d140c040e980144045402440041d4803030401d00f001ca40c12030040340c1d070520358aa02103490784030481510070740c03209450380508161800700758600801e10100c401b9044050084c01803081101030740210701035402038445c880c10420b1000700c00c3c226428085001e0058103c07920500090742c0105241907489082c180018403406041c140c3c60040c203d800944108081041c0118104100410344400c000042e40700d10525079100c0000340c032107110840e0005c04102c4100703c00e034400d152580c002504a80a4500010303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801931061 1250 801929811 801929873
    0x1b040509070305030318010b1c030e18130b090105070c02060703031401121109010f0b0f04151710050a0603051e01260c0a0e040f080f040501030b031603 67
    0x41190b1050340e0b04c680240003c2d0906d80c42400074080c3d40c030072940545101e070503054450081b840900030068005d00708485000003805130f94510b12912224844481032100b6420b004100070303100180d60404548024502000421041c01841480c0c40b03954a074807843c600b2103a0f039007002110703030154400714207046c0c4d903608480c0a45c150031183c501a10584e81c44100181207800e00d0141291a858a5445040d044006001d070804046451084440328040350f511102c0074010352556000c2e0390440ca4900040c0e4001c662202e50249220a903801107200b601460f883d0304882c2c1401e0292409071b550046c2e01340b802008103030311a0380200e500c000d01d45d0798296a80e181740380c10003200d002a4400c4d2141c101091441d50805610413445a44400c484020007510005001054050150384100f801d81402032000405126000c82d5591320b041c0d000b0b184070361794001c2e103148189940150003894000780c900b050074909410002070112440806000c84031275545545d480100342c2c0c150304003450402d054130101c41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801932311 1250 801931061 801931063
    0x1202040e13031b0b06010809031c1112040f020411040b03070804060212100303021b01020a1b0f091401050a0302030613030e03030a080411060a09060f091a0a0305010501021b040509070305 82
    0x243e45103220711418031141c2441c0000602078070014000c090b450b08204100b5051f209030f0805080c0108060300082100a0341e0f155034500d41c02440400e140a00c4d00306c0c204010801c1145008640d03c0c400c90701008501140c04076032071680144c1c054400714000400c04501d10501030303918130b94002d2107844c001d03180c103d24402015071f040c0c003510a4207030000c540700c3c20300406406100d44640448020865003000c950140001d6503200032001c06004028075500c50b440141c213104001001c0c1942c040f40ca01d625644501c0c0b0401003824000022420380ca2100200f00b43c60541001000c03244c00030000c00b13860f00c81310304034008140342040807800d100c0703a1744000203183c03020b1001d4580026651500030312482c0c01e00305440c8040000901c01e204840800c0725203002d540100c0741000f0350300c80d864070740c0c25008940c0b010340b00c000607a08001c1441680c4101d04694a01300700c001c000303c228039a402d11550340d0743c0005a03a1200607070150203a0883c0800c11003024105540003a5102e04040200c41c442980c0392185 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801933561 1250 801932311 801932357
    0x15011b0507090f020a300c0c022d0f13110301140603100b0c0c0a151b26130308210c031b040504050a0b0a0e06090403030b060903070e06011202040e1303 67
    0x247c0086291a1604c170158074040c400d144110604005040b81c6404500309060040d0610911600c01c299808204850344c035141100319507a1140c0c4800c2200600c1e4410340b8020350403d200d008580b003003072040c00e051401e01400703480c010500d9000d43d110481c10701e00c2c248016008544070076001d1184e42202880b03940c81060710001080a003000e4001d000715244000d0904c008030442151684d01c000c1080c0000d2505214400c0300080e90000345112124005101818850b0846052000d0300c0c105000c400c2c0700c031620040000800d154846211030400d1581030700d4160b02124410b00140d070910004104090f004021101c5540e40c0301d0762850680c41e41c00160440c4da0561344004c6190b0303240d0714110359041000c5072a0160520801144d41850300b40005440880c00174401020191510540c0e1074684800044d507250580040560354510b0311a00154014841102c2243c0094042501c0c0c0c1c42100d4240700310b030140d40000e01d2031300ca10755401c014103507254920841103040006052220032442146006 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801934811 1250 801933561 801933581
    0x11e080a150e15040b1b0301030503090904150903051b060621070302030a0f050f06160c030c05060a05070201060b04030503070b09120304050a06060506090915011b0507090f020a30 79
    0x68102c507007000001c1b081c01ea58404951b2144490800062002c184000161018030104885800c115900c0d4501400420b00e4114030300704141c20b24202408068001c00a04003600580c920079049515442e0200d40e582c034140d90300c540241c40c1002d1144c0c070903441c00e1038080c00a502011a110265030781c2c042440c000b01020f06171640c0302c0001c030341e9003007042c00d01003003c8401d0801d005003100d061946140740001251001c0c0001d200d03100185d030342050301035504400d003550003809a60075840c0c0001d4034806041d003110a84019441c140c3d0101d1076a21031b400b51070540380c000c00190308151040c1d54110075a0742c0034003859024800d043d04140703a1039440c401903204511800c050300c4040042d25103503095071510f410040c03050000380070001c4207884001c07140e0341c8081d100f07030303007001c420070380030050320b450f40b403e4050950344880105400520400180398002c882c510001008031802d00c001540c128001c184d2064001580d240700c15105805040e10403800c22019030201402e00e4442803404102c1d090030030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801936061 1250 801934811 801934823
    0x11101020408070b2701090b031e1305071e05130b09090706020706020d0827120a110706020d1404080a120f03060b0f0a030b0306011e080a150e1504 65
    0x1107484200c81140c80121030480c0720070002d45105c0d008070020784280c03820300500440a03008400a040920851034203d0300900001504040c1d0422030703003101c1f00100580c5c00f40d0b2030b40f1402e24005400301001c044610000c014060080b07400e4208001c021003c100b065850b038600c0d44482c51460700f540c039440103c1c00307084590000c141c02031404c2000f81c2408090751000b030540d080017281d00d0b00c01c3d801848107a070280320207518000c051400005401043d00d0ba00480c070880c4100041a095801d10350000c006a450a490303442c1e1400c4042005686c46e034890044100581249010100d0140140705070307984150340c05801401d2646904d4001c1c604060030b107040c1e81d031020f0f11252a00701c5402031005100d0122a180c14005c20741080c0c00440540300c0c8841c0d00c02c1f44000000c1c00000717107100b1340c820f00160724000c081e14000e503074034005811043c245541260b41e8001031000020001d01c0000c141d0003460344003450f021211520004034001b08403062441415010f064440000c040743d24002c0c03403080744252 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801937311 1250 801936061 801936067
    0x90402130e0f0127020a02030c07060e0307050301200c0f120a1e0c1115030c0a0905030d120506120109300c021311032e14011101020408070b 62
    0x703940c0140400301a030008130002c00300c1e07241208058644450468141d600c40380541d031607100780012407840c07180544406407405a40c50201f00c3c00e50014241c1c03070906080303040701d50301c58940040508a484015502c0c4420001c007240c0e2107106406405801d44402c01020f444408504441c00c03410b00d42440e4180c07400310030010700d20040341d80007450040504025000c0200400008102629403086800c014142903084180404a5510240c9481819401c0d0083c15101d0030030041d80585030f080080d45101052520f100401c1d1802c000500d500c0c3e00d031141c3d07107094207200072a031910020301014150300d8100c4144159544552002d001e41007640d40300360740c0041e00c03854030241c8216042c1806070f002005030081c90303071181140d0b022000180464048400c080c02c07031901e1782d20bc4c4c003c010019030710340d901e100401007040c5507803c03250380d6611070740f85806190b0302c0e200d081c04084100d006009598100700c140c80755001c694482e032003403101e61502c0c000052a00da03d9031503141c41c0030384650003a07187d08400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801938561 1250 801937311 801937321
    0x30204081906090503221a3a0f0b0316030b0702010f020319060501050a0c1103010b0307150201060518131a13050c150a1101060906121b050108010506090402130e 71
    0x5440c42c1d031b009042891141034213100ea03121842052140d401d02c0c2018074071210181618140d01546148052000d1054a420400150103100a41310302e5007502c480c10304d0440398544501307000c1042070342032a0a42e08100c0e4541155181c845080700a00060700b150750303400d141900fa20151005600404000b040d0103280491848450240c41681d004603040020901400400c190002401c40d4030a5000d5046c004000382c5402003401404148a400d50600c2000c00004203458401102c00b00b00c000744d4000e0000e961a40184180c5410501a0000001c1d02c0c0000a080100c941c6072151902e215580e403506600c413a090011040b0740a542d00624a03160004000030050100b10b00d00070313904140d03260403002d41c0b00c40c59680280240705035201840b1010240c40d150990030340c80380000c2c25001108121440e1940a207e06110842c94121418000700c01c4200036004064004400c03510140d5440342c89070b003040700f4410342d900401c0c1741c9900181c01340b040841c81004c9040d454060a10031180340350038602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801939811 1250 801938561 801938617
    0x20403111f030f0b0a0f06080c0901091205100e010b04180c030b07110312060a0b0c0705040f09230c0a0305060601080402180f0109060501030204081906090503 70
    0x120185052040e00d02004414105400d68144404001d0a0400160100743d003061a40948480c1c40380580c400418039021944c4040740c00c00005603002a038408599565007103024420b40324481c00140070805c148801c0040c05030204400030301500c51425101998000703003400054501110f844c500503511030104414031308203881031110303028003018172032000085511a00250700f1603000c060068401200002e80e0240a140b400111041c0902103964848003c00a440114010350b5024801e83c02d0400000780d1103410f2080d222000010005015000d02c1c02d01080000d05420b485a0612903d5611801c0403418951081035070340350a082c1100d458081c800384604105a07600214850055408240f0104000143c403650254007030070516105d440c3c9000142c100b81d4890340c003400d69901c0d6410400940e2115061504031908030740188030407034542c1c00540581c051802440002ea00462a001c2c01d0480074042c1e0305218001c0d1070000c1d40010607140c0b40d06541c00410006081c00c1c8480180d0394101c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801941061 1250 801939811 801939833
    0x110d06020c031b0d0c0c030809010519020307020108130308070e030f030f0d0b010315090b1804050f0d03020414090c09090c031f0e07200106080a03080108210c10020d020403 76
    0x103407a28000d801c5000d00e646e0f5010428407404003600660700415040807507409a0115002d41407002503019507081c4c0c45400039601e900408049001030280408218222900507a02c5040703035164681c801c080e82c0b118400c8401825049802d40e040c49400d0388a0741041c4140000c04500a030820302d01e1751091140b4481003959105c0c03a4039130405203443e012483c0510101380c0201a00c91004010500c00454000190240d06c00c070b06880e00c07a8ac021052004000c0001250500e807911101a18401100001c066049000c2c0e44140404529030101014070341c540540182d6206007081d1030301d0304001c00304001c6040c010080760104001d1400000744030001c000780501c8480012131142c00b9804902b0441c04c0a52403001600c1c04007401011808070b103000c10900c174803a6003680410020015036036079160f4503540711120581540803480040012416031004100040d08407650101102c0d130040d0a0300080303050b40900078070700c86809072982c00b130407404580c0000c0080b05c2041d00003503140d03030a41c240003818076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801942311 1250 801941061 801941083
    0x721030e030606060702010f0311040e041110080619090f0c021e030904230405100c080f04080705070f06020703030306050102010513080c0c0a030b1f03110d06020c031b 74
    0x1d40014204405a1345200c11a804641e0a180c551440c0585000c1070300a00841003034561025800320b0041041818030b05c2c228811801200841c01d00031034882400307181840c201c00308001400d001d002490038203144c802e8040034040c0d44101c42901e60b681d02250116642c41c9040d070b192a4a940c084840c6681c10401c804000700f07036660f92960b44007440003865591007251821801180c441c48c0c2d030642c402c4020310300301c2550100c2c082440380d458a4500240c41d2600c1840d0350209514114840344800d21444940d03119a03014101c10345c04d40c490351911081d6801051048419224035100840c00c1090750400000511558005021817404c620b005410b4075080e41100741107a02d041d04011004003848000190103801006640d030362141015041d0030941102d0005811024203d4000108050380310201d125001c02903c1e00d198206054070030740c5150310340c0f0015040307024140a600d542e103400021040c0c120700c200070042c03034181c0c130f600c0003400c541041602400d110f2994444550650060240310050303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801943561 1250 801942311 801942313
    0xe03070f1a011707180e010221010f030803010b0f070f0c05090c0f03130c05101d0306060105030406020310030f0302030319050702300f071a0c070201030b01020721030e03 75
    0x845004800300e42e9401d183e10514501351101c020182400030144d102c0d0720501401b0000b596079181100380340080302410b03803050120103460000080c1c02c0c1d090400c58816254481c04c41c070700d564a41a840d070181e800c81d9609001c84103040280400140c0c1c82c0218400a51060000e4081c80e480c1104002c1001c500810307000314180c0411512030802c41600440e1b52041c84202c080c03a14400a0500c080940503d8000035004444000c0710044190441a046964211810103005184242c41450b441e50000e4900c0e0b40414024000b141c0010f02d141c0295a10021403904150007640d2074a5001003c46110025400b6800000520201000300309580742c0e8228207030020310640c10030b480e0081d0386505041e406d005072160314417656144040d0515804054040030400c1703803103100c480a01151640448821103c5505042c00c00c403d10001c80004c80c031400005050504000c02900158064596407940078114003c0c07140100d910161700210007051012416009280c051500d405403a0b020b03205c1000e48a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801944811 1250 801943561 801943589
    0xf0501050906070c2a09020405031e0619020715020a1206060813050109060e28050606061c06032102070e041712090a02010905011701090e03070f1a01 66
    0x50a0700f200814110340d502c07188240084211160304100c2090000c0e952a10082980c400101c00c9007d80241054503403c0301942d00240c400d085e42422190701c00340440080c4c203c400003c1c0d07810016040601031020711003001d840c00003660b845c00b030000300f02d0120506041e40840c204603071680c010282c00c000300b10000108401c0d42400405441c1d080c004003818420301c1c048040d801041429003190ba0300c4c0b54008414080210818007103500c0341d0800030745680c074400f091310900e0a00002e034142e0f42c8031034225000d08066213523941484032940c840507400801c000c410348105610105071140d0401140185600c0308000300d00f030481c86807004500d522000319440400e0510041400141c0e40e41c000c3d621456024007a480c0b00c4411165000c0c40c2400d84820350950200700c01d0304004540030f0070040c0f003603031840d5440351100010f55041401454880041100380f0040c09848095440b040c2070715422801c0380c0c00e2011a5503501201c24410104981401c281d902d00940e10030940342c0240035104c2c60303503000b41c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801946061 1250 801944811 801944821
    0x270f0914091b030c031614090f01090b0f100305012405121003201302040b090409030908010c111b09041e0803011706061005040b091c0f0501050906 65
    0x80d88194854800501c06001d500c20b4240e0395003046a03c0c208032003d030070380d038180c9060b840f1140c900015115550005070652aa1002071815080c61840b456074031040d50181c0e400c103410080144807081c0702e242c0010303800c080c5000680c0d0380d081820717034900d5556001c02c0640c100500c81a0b6150a403080c1e8081001c40110010075940020503594507143c6541240740a641d00c45da062a4880a0750000c1c0014601084601403c0784c44480c1c040d90344020341d4040c200c0042ea4410f08100c0c8030310701c00c0550303428040c84540340310f18090300003d25680c0a03140c03442600341c4540c411030860364025403020100380c441a03c040a014284803502d1600c0c10310500e0407005a40d00c010a00b0f9403401000101445100060a004c032071036030301c5050f600e58000f65030540329a120140000e0051071030000429504c10900001e980d442d203081c8003d10340d80c40f980d820f03092515100d00b8903441d40008070511750104032803441c46500400c3c4030f85003804e01d0054400320103080c080e003442821590040d040d00403036000001001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801947311 1250 801946061 801946063
    0x501031130010803031501090f0b03100e0903072001022e090311152e0909030c0212031e030717180f0c030607270f091409 54
    0x6500c00c44120300314903400c0d000001110221061044551400146400100c3c001c0c00000107180303d095042840301e00303581c1090064603292030b54407a5200d04540c0320014030800340304401440d0070070101650000c0e40760311003207020300705801120308401590000c2007210901556200060081c40e410103d44a140600c0700002c0d10b403140c54100c840d81c040c40b01c0c0822a02d14603100744241ca50010300d410422132500c4c3c9802011184004d18900c0ca52042003400c020f10006000064044e01000300c0104405c1d0708135000b2001c003002c40010131214007441e100000c0f060748602403041c0c807612994640c4420001481000b50007481d52895956941c82400121425050002c1400700d810302c0c03140300c5d910b0b075036100000c8540420000c102c81c00c902d205410300c2120700301c0d580000c0d07152000c2015108002c40302d06140d43d883c07800103242c0307a140e88124042240b95000e41021b00b803030b05a030240400d0b001e41c05d00060b40c0200107a0b0090980241082c070030420150148a407000380c0181950111050034000f0b115 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801948561 1250 801947311 801947317
    0x4151b021c110c190e13020406080606010f030b01021e07050405010b130521190c1d1306090210020303011a0f091513030f020301050601050a0206011a0706020403150605010311 77
    0x640200b100d500813103402851118840010800610a894649001005601d10003c01d182c00c038062030408801162001d4007190b4148911410f03541d05014480404088002c0c1c956006e64a040d405150302110141e0705150340221110728020050202c149880184022144140c0c00000d0911041c014080101a945444411101c04641d1542c40c1c0450803040c898126080941c40c0d068440c040c40364040840a860b6000c4140c060300072005125a901041c2081c0d51905144c1c4500003810700020308100b801a60646078917001d25070005c0d220340c540d40845c43c010001720700800584d10110040205c80403914040c001400c51984c51030628000c80906c503180d000700174041d40324112201c3c17036030261720105043e1600c1526000280c0543c99603814202007000203800268003035401c03c0002101c6500601c21200040324a5000b000241e1070144098800d40220124a00b0f80030300304802004101240050405140140c12404500e842c0c0c02c44181110b444e1752069052500f4112032003280700c450b600b6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801949811 1250 801948561 801948583
    0x101d1807050703030f0212040302010c091404020f1b2a010806370f080a2105040302030105041203050f0606191b0c051e030604151b021c11 61
    0xa90b1101e84500e8103501078105030055030511440450244608032000384882e020724080e400070460078030005401c9640c20143c4c0280c84a15016812080346402c16030700401038820031541050800f101d0f0444011451034005e104240350380044e040b07451013200d0202e0305602025600308810408007aa001a100e600e0043c0780c0c0e4411120181c480301145011101890008060007440d001034001d840100300e42e800b02d01400040340d14100021071602c0c8000307440707020107820124120300442d004030344900f054607404d2400100f100034400040143c50902030140981e00c02c0200c1d81c0c201d058001d000701114401402290412000c07400d1240517219002202d0300996540381180c8040b02121055400d800310f030002130b18884800707110300113024002c41c000003515002c540c00da0140001c21446600c0d45800035425500d604100c02140000e01c20b215060f10820088102091140c04410f0104d442030b08021807001603089110101c07050f0f0090424580c0510080c245007100280c030062540e914851056 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801951061 1250 801949811 801949817
    0x1b060c1b15020f070b012402012a05160b0435090102011806050a180c050f1810060f020102070309050d0c0f090e0105150d0b0c0405101d1807 62
    0x5103c0c2c29070540d41040704c9441d5000100902256561040d20400400c40c82c00d03038621003009801c4500c12481800340ca0031010807006130000007611800780c0b110a0240e94420018001c08000e5002d030f2072240014414028040d00e0075964610f85800e00450722440c448045091007880740005112103107030200e01c24101803094195490f600b034900141d0051000160380300b54446080c51050800c00c658100510404000009200c4109020080405114041d00003000711600031800c1c04142080d020200d58403d004140c40480c1803080188880c0b840142c8003480c0d49106050140511502b05005000f9054140b000318a002c1d034540f0001e2030030700540100d500c901141000c02d0309221507500302d0341c003070010800c0040c201540c8a280d10024070044100c90070729400c0c840000c0691811003070400f00c01d180903003228080c1100341d0703c04010715001841800104002c0c0800b00d1283c9401c0c0c6400b04140b4186c5601210720702000c0700c1d0304d4007040f80f0383e0a0711950410290720038a180055015420000600b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801952311 1250 801951061 801951067
    0x1003021e06030414031c09020a06030b0108011211040606030e0609071404050603010e160e0c0310030602031902040801060801050121030f0c05161508090601151b060c1b1502 76
    0x132030328250302c10400c1c0900300141c1144c107080840036542c05149918401c665043d4017070390302c0c0800e03000d5072180811b80e40841d1911004014040f001c1034101d0700c0c10b00c51803559064003030340ca002400310313025034100ca80000c2da659002100c0743c500300006600464014010440c0903d08080ea0068031500c02c03403140542d0f01c070404100544c50940000441c5044003060710682d2030b4541d44000b51452300c3c4075400103281440040759000a4a00c200c030b0083c18030420703403251719003542c0b40d240295101608404000c4c00d01c0312441d4003184170344013510240070004004114545421515401d469040e00684110f40e400c49040000c00c440c41084c5d0b90056141c1400c510142d20101c0c1550424072a190191003801808069101c0c3e803406040d48060714160300c00e501503600a59000ca40c402c0c01250031030f020381d001c41e0051008045802c1c5090420400346044004400c1c039a5914280761081003084840c030341ca65115059981d049078081205c101001d1411141d001c098440b14096005041210150350f400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801953561 1250 801952311 801952343
    0x30804051b0a1e0305010504030810060809060a090f0c03030216050109050d0b09070911040906060e031b030a061506020106050607050304051011010c0c050d170f0604060e1003021e060304 82
    0xa0710f07030f80c0020f64010000300b01ea03282c85d08002e8507102040b5010400c20446607404903019014001090080c1e842100408031503035400151001000c051100b52144000c4000038000a600f8034180c202640c0300e640980407103420340c8120f008440301031304102d05020050300d050080c0c1c2c482c040683e006a80281d4160007540720915294280340c42600101d0f1090308143c2e1040c1d6100203000100f0449900800800460f035075540211010045107810b241d041e00014014208002c0403125050740c0354009081e2080f613100c5a03503103421030711603290400306440065010082143c0a210b510024207043d120f083c903240e510380e100c81e01c0c0d104a008a521603d5010341d03410303a0a1149000c00215038800000b0403201c00d95071800381007800748520840e4540301e20024445441d104400c1d07121410070a0000c0042a1a000c9618440480c02044180c109642d290300003002203060710650b00500d65024a840e0550031760060080c803446215401921044803105880991038440031a035205030001d541e40010016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801954811 1250 801953561 801953609
    0x10606080a0c0e090c120726150d050114010f0308040611010204120b040213110a0e120303010326030708160c0506090d09080c0306180f0604030804051b0a 68
    0x3c21002160065200070812044241c0300000340b01c80801c0c040b4150461b5520002124608000254448104003803940c0c020352040d0300c604141c00582503903c0d2181e103c00304010919840782c0c2c40f0240c400c0d071345414019a2001c1c081403014050002c04405c60406801c50300c0300d00b990f00ca24858042004440d41c442015100c007941910f000c2c010501002e0b40d8205c00f810034140a100079501a403003040c004034040140f503034070700c600c80942c81c5542065041455045090740c01a0b1203c8600b60081101c181c02e51411501744010350182d403044402c00803251182040080031860782d0340a0f10046020003d10001c0340e00119010350084000c82000d040c000b0b008800c40c0d10325203656000300396214010611141b210003050b030284c440c96565547c00c1465640c02480e558080404c809601600001c4c0403a00115107083d0f64079003980f00c44101c810072281c3d0306400d417402c80d00b2602500050020303028481002414440d0007008070a20300c0135401c4242e1080024540c0715103124007031040b88100001451034407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801956061 1250 801954811 801954827
    0x61d070f0216090e010c0201051012051e010522020607022e030f0f0b0d03140f040603090b090f0d0f14030a06140312070605040c0801020c011d010606080a0c 69
    0x1442c418000c80c2e1940d0700441d00103014064209040c95091030094201c152051103901d01c80d0310466a01c03100c19180c180200c612603403032030094440c0d008100c0d400c45100520440010a0500000000760510b4002c3e00c40e400a2401c10030091503001005400025a4a2400351815250100e4408945408a4a00c0610700f52407010382100c44601ea110700d1144c0c0e403da480f80c4c2100c01616814040016128104011108420a016804940c3c1c0d6840310100340300300803800910202c042524540390805014128507003156201c0c50010340c503601c1a5040117610f10b151900994448000c0803901d5103100206d1b01c0d0805001064100030054010400a074032800071030712210542c1d082c48c2d941b81420448480900160b006041d4400010581006d06050028410b4401e000c1198040d041118170f94508010f01005801036507001038003a40491048420301c020407c030b002e55000042c035080c160085003964007880e600d642c2c0310b0f4542001000340300c0e0081009680b154092000007150043c0340400e031a504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801957311 1250 801956061 801956083
    0x5040b0901210f0c0e0d080901030603210318080d09081b071403070303050f0904060b0409051b030910020d0e060c04061103030709291c061d070f02 65
    0x600d4550640020740c0b160342c841805042030345000d1082c4185900b003a101c044200d03099641040c041448040811a00405000000d07414980450f107640e0b43d440741480801c43c0c0402141e00c84c4100d00400c402501485021b000c11100c1110403040c11076a21a2466402064400741c2d0980d1214840c0c0b00f00a10181107c180d070744031170542501205003007201a685c401d0380c0103102c1941c100291800709440d001841801b1070f98955500d03403404480c048200216003081e020650460344a00c030118074418200301920181210000005451522119001944414500d81100d42e982001440242200841c20b8407010b61001d0340544d0f83c080040b00880100341e0011042170b14003074007080c0454400c0300d4004000300d503400d17910411340a0040d900300c0d8a03444169940004100b129408101310031410f0b010100c1a012184440b8040004250204099211242d12201345d540b4a0700781e444140180706000190140607060008800f000020180502c0085d061905008581900d54601b078030810800b0744c01c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801958561 1250 801957311 801957347
    0x1c050d0933140c01020913091112150103030f03050612060615040302120303090d02030a0c2a0608011d0108060403030e0a0609030e04060504140f1b190807020d05040b0901 75
    0x60b40f241d0800d6000f9000481e280e0b00c40d03e4840d42e901c0500c2c086014032030100b9040900c100c80082514204000f064070010071030128080c0340e04070f40741e18216600c0640214021b0b102d2120081004c6001422648000d003c10b00c100381100141101c0140002c540d50b200909540040d21403428504511160040b82d10007903102056181c0340d02103603400301c040c0d0b009000c1b00044030440c000c0b01c2d8003a80c50307018401c0b841c40003600c40990040030a2256406c42101902d5a0b2103143c0d05007900404081b4011030b400c1900403c1c0007400421200405007510070382014802d03007409183d41016142ea88a0300042c1000d0708060721610403510780c901c2400055000340c0e11600811604546241c0030746801d50b100d00d914031031031901c840052981400d0150409102000c0b200e41041d580c0d41d0148100c0080c090a80369900310b8140b80148005007080080001200078035440d84904440b950041c00b240009100c1802c40d00000d0b45002501d42040c01d980c00e459003114040e403a00416001251241e042d01c0d0485c001c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801959811 1250 801958561 801958567
    0x5031b130306110705030c0708070f0e040f02040207050f0705030c0a180f02160b0106080a020909061504152f03070f050c0907030f050105220b1c050d093314 69
    0xc0d800240050444400300300398ac0c802956a250700000c0320840c4254071407208280001000210640e03660400c071403000f000103090482546401c0d140040117100805203511034542800240ba0400c409a4003075001c07205035010f58104030a0007084810041035080c15a282c110201200ea11501519410803600800d040340355802c2c1020301e1190002e10511010400f0718001c1003181c03000d070084645c0c1120280140140d900c0b400207008440c2507180d1074111942c1d05200104114100c841c61507115a081d580c0ca8040000c2c10502c0c034158842c6900380c130f04000801544800402e808400e9481090f08098949100560b0341409810300c01c03c028400d034042e5400701040b07401d1780c160f408404843c0c01104204400d81e250310900540d0310002d000511803c141100502c0740304496005026080c1000d0324001c50301012081104807001d00d1101291140c200000010f0b05941c03100111000380014803a805d10610f060b408000b0030907d074500d8810722140d80e850b00900f2402200e001d80036844040099075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801961061 1250 801959811 801959827
    0x14010203070f030e01021306052109030d050c070201090302060d0608071203120b0a1806172802060f18090c1c020708030a0b030a0b0705031b13030611070503 69
    0x2901c20b50b00000100c2c4c54034010b032050718014401e450388201040c07152034000c0c0c00d01c00b0130389031500003c0e0b40b09410105103029040d4102100300c45405090380000964071200c0015940b000d582c8010900c0c800c051040c092000580c1c2e01c5552881103903015140e90390b5580c20000c03c100a4101900700088a1080441c0050311640c061070600266000356101f005030000301704140142c81410144070b0780030180d10001e010401c920380c3c1c03003103456811080010701160b07900202210601c03d4070401046800440c96009c4004a108002101c0c81d0403406a0140c0d0b17072142d0004000f405031801c0aa040c0c440400d0845420001c542e12002540c4000e008032054580300500c074140b40c2c482002800011b20601895508007418003d8400743c0c0c3d80000450f04554441c10400e00502c250080964584105601c02022802c0c4900300b40c026540d5a54041d03480c5444070700c52500d5401e210000160900802c000c0c00302851000c850000d03290720000c04690b42c200c00e15801b90a0140d2500980180000580b41c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801962311 1250 801961061 801961067
    0x711070324020a0e01050a0c06060b04031a0919150911190509060402160b0a1a0f09040201180b0a05071a070504170a0611030901050c0a020703020d1401020307 70
    0x121500c903090046a80c414a50700c161030a90286920003000300307030505403061040d8003500280802003140d1400802c2070038a40c8440c0241d821a50001c01a400c000400348180300b40042108915486400212042e00b8084009695035150320840920600400c01500400c040d03d0407100c110403070b001d014040341005042942c400c06181501520841ca41ca1b0703c802d640400800d10b40843e0401050103505a480c90b0600010b035022018001d030001c100544880010200b03040a800b98081c1c4900181c501d0713285845400384039065880520960308809d592542e0390300c2d92a8039510503820321700798486a410b0741d82c0d0b40084102d0341200300340364000f1900101041e40700003e402d43e24003a074442d40b09090b01c569140e4064100307854101c0083c80401050040031400c24102072100720020407610b13544e0203074848408845880303120320786201000050100001003409469002420805500e1901c442030350003070365581840c40024001c1071041d11040c01e000514815440e54440034000799624a0841002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801963561 1250 801962311 801962333
    0x90f08030a0f05240f04090b0705070c080a020604061b021f03051807030828091706270a0b0c090a0b0a0504062a05030301080d0c020310020307110703 66
    0x40e4903450728083c0054281c2c3c01c80f5411030025501d403e0412020b62a56043c0b204000c84030344030316006600c0d403d4000009a400359541d100d208241c5d1265100d044514180d5840c1071240e0110300a640554141000759071744004890450f0410308104240c240c40c0c01c041d00050700c0c2860040d601c00050891003040c0041902200c200400b01c0c1d5003013003203950b020600c040c44401050040c03020761080c8018000030f01e80304001e01d07111a444180b0040c0110070300c0c020100c0f0b111001880b00154407460b080103815108111409680480c40240c070031481c000c500014841103144100204209021500e4600c070801e0102030099070b0812400302161030705000034140d0780d0000b11200d004040c125800504982e0483c10b0f920307100b039656900c0d0b142c10324010003203401c0000c0e403c03480d10307028800c0080e491400d9900380e510b1819102d400650740300c0d8540748041d410030b0b4140c0c200000340081d42c0505401a41d02040b00b00c0101c2c651a00141c40c1e40fa82030007111484440d0072210303070921640340301106011861940d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801964811 1250 801963561 801963581
    0xc0203030613050103080d0c05121e090c0d03050d0b03031b0d08090c06031024031a060d050411090405060a0b0f06030a0b01050d150e0c04030b0406090f08030a 70
    0x209500720740c0310b42d40300310840e482448091724000c3d0500c800a110301440e040a40c1044a500d001c60810442c0c02ca100440301e420f5540300301d140358031401e82006580b81030000d0b41c440c0c103813405407000000712008602c02c404000350007000c2010000d003c500001d0306074040e00c0d41860181c200c9444240000039802c0c00803a90302d074225148560004d498180344144011403080e50107002030180100080c0034005075400103032040e4000703e4048004546082000200c1c3c1c0010500c0a186003012084c010280071503840c0c3c0148031401c40031801c44101900c4070011101c01c01550440090150348500744541c905d25520f11a82e8400c03002824841480000900c0f41d029102010741080018982020864401c000d0100150004000c1c00080c0140105500415103840103041052070034990300c441c1002c407012054190000103010009000c040e800c4010140d0001511072054501400d5840d000c400000062004080d5602c440c100c4040280c903055244003a684074403023607141d060040036034003c1c00c0c0c8044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801966061 1250 801964811 801964819
    0x8010b030a03120f090b0f04020a150e061c0c05040e0708130b04020102100c02030a110a02011709030d0c0e0108060a0e070e19090506100809030a0c150c02030306 71
    0x4981214900440c0c240086a8583c566091844112508030081c154040c0114000b540e10062031340442d4801060710310410303410000002a140a2040003185011074020000c807011022500b119a60811048030042804940454450b02805602c81c0c41076045484100f540341404801103401e80c01c480030388295103850641500a68880204580407a01140e80403007d01c0d01050183c042080542c49030782080c0188169403138842d01040c01416914031099280c0180c0c0001019811503a10100d80d4039082030040c05060800d2160700003d28107840c450b40d5080c20907001022400c01d200c01c00403542d00024100f003e000350baa1015002e4000160100503c0c04200403000084141c6443c802c04004e94400844a100d5070322101011203c941101ca10b0343d0700041d440700380003180369811008000a0010a81c04120341c603091082c400070001a5240c08188100350047c442070b6a00401075585064080c079024100d01c0c21030410000d803900c1d0030b00b9141c4003031800c124084100e034040020340c0f048400751 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801967311 1250 801966061 801966071
    0x180e030d0b030a17070314031314032116090b0703110a050f0a1406040210031104050409050109051c0230030915090309060d0236010e040e150711010e06010801 70
    0x4003031041d01780310880352040c0e9125800c9c803203c0010244540e002d8044071150407641000724a030726601444a6500402496580c40410400e2070340c1401c0044040c14100e281014401e1f160640c58145402048001418000e013040464040c000810400e1030386070b00b200444454040d0b001041e40c44a4030644103503041e1403104085443c441002502c40c1c0902d50142c40f59200168008044000301503070305588420690400000407070399503500a00032024010400051081018540b0368074200c2e011148513810106180e0900c2c03d2900407885c180f0280350503500107140031403001030f14800900003100440d420804400d03c205283c000500d507030700940012500c141c40d1280c1e20389070795902500c3c6041da8003410420101c40d010740c158000d4045034100c90200c01d00c1d00c0301100702081d1010043c0c4c1490f210b1030103d090100c60341e8042d50910181200b44c40c10002ca10420000507210f085410040c0b0141c144440407401d001d01c20809902003c580714001c000c00c44000840c41c0d212507080c41500c950750700340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801968561 1250 801967311 801967337
    0x40e1203091b180709050307090b0306010e010e150609060309010e1e0d1206091e05010e0112260d090302070f0803040521010203040309180e030d0b030a170703 70
    0x100c02d0203150040200045021508401c0c0c074030040100508600401480d2000040d80e9282000f0141c080c0101480204061003214185460034005a21070070f2034000c4034004106590744030b05040d030016022200e4940b070500803c0443c00911881e0340550b0092800001c020300c03000306500c043c060381440c8003a90408085420300c41c1102050314402c04840d002122070041982c05850460f42c00c0c4401c07400415800c1d45c4403407000855a81c0b110452040540c00c010010103405441407601500b5207030f00003002541400c0b921020f14030b0001000701a0103034101c0118413041c2d54203048480240040354a66074682040d141c0c00648240d45040b4090310a484002c9050003c00c8002401d85041100441c2410301c0c1000300004216807076811100303481e82e0b1a01102c0000280000c6208601903200c3c0c0003018a41512030180c54071212070446020b1600110517003800010080b94280b082c0d0103c00300d08000c0081c00a81058041d00d4014101410007051100d426000000b80c0107460080d00c481180000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801969811 1250 801968561 801968593
    0x311010809030d0905011103070201050906012411032701090504090b0f07200c0a05061e090604092903060906012106020a021608010603020f0609040e120309 69
    0x10788001c003942d00300384444119110740303501c0710380d07124020700010070040b01521003000c0b00c3e441600c620005035112000c000d00c00d40e080003070318014610384030110881904116554080b0301910031030810402081d103805003d2a04105440d1604010020102d501103013006540a058050f0000b40c0414080b550014031441c00d4412132403100e404c00c48030006680c51880c8101c04d2140100100140080d2280204060030300282071a42c1c0d4101300010500d24440c0030410148a90590100d403203032504210003c0541881c0e1668910004c14030300701d0740c585000c1030002e4005e020350b810800a0601d45000c050414104e0092080c5a401c0c407410114051420700505031a5041119410401d52021004029424105407860818100d136011200308941039910001039a20000c048001070b4040840c100301035052112050003041c1c1400208101303861a4081000940e00c181020310584010503842a0740d165500200c11010710716007a294600c5a400b100040d6400944031220144036034866140c1d8028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801971061 1250 801969811 801969827
    0x14a0d020d12020703290f190b01032003040623070e0f10080405070801150506030c160c030b06060306060d090606152003090904020d110a0609031101 66
    0x90080d00c5030181940944400b00d140c1d100a4030203003140715518001012496514020303540c8040030b03200c0e0b01c4d2000860078a21061001401184000c06291b0501c4501c240c60151031403280315901d000701c0c545280a0050b0002e0545140410b0003116080075244074444000046202d90302c6140b08001d44800707100e2841c08100c0115008401020210100340410700403e428010b40000a202c08040d00d6610042a031800c0e00c2c818480100740404248000c019041c850780001e030105400030000c19500a07a042400601440303141d00582c0000082850151144103c40b031049201c80000c1e00301003280360411810409100c1500c2c1c17a2903a07008105645420012a4014000141914101007408081c0e000a0001a004490040e5101400103a1500e07090540c02c00d940c2c03544643c2009004000382c00cd0303140120265140d030360010050030640307581358141a41c00c1a01699010307000040d919011440003040b201c03061340580d44020004000340c0c0b00c1220020b9a2052014030601c3c0388010041d0340501e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801972311 1250 801971061 801971063
    0x10519080402041e02042102030c090a0609060e01082a0f0f040603030206220f11120d0819180b1801060801020a0f03020c0c150f0d0b0f0d11014a0d 65
    0xa0048911030207036107041c0d522f841d00640070b0100019400d565042c45400c8403043e60000181d852080d004016030203050091f4003085014001d212001c4c4071500030100800c50100181d440741c007940030480c001d0345841d210003800301d001500070090b054480c100030b5900d00044406c10b02c1040210545480700b012841410042c41c0d001c0b4422100e001e02d03944d80e0090700819159190814011036400b81c10b01d008004602e00300f00300d5160000c450800161186014180c0c1844074000d90400100c03140c102e08940c0040c0400d0b41000c142a282d0311003500c1d544044141c000000065800d20401150104040d0f0081c03040b5051038803807a4105060030001d405a010f061551445600040c00340310060800c401040e0341019101500c03440d201c144001503055810402c40c0700821076403030381170001609000280c19489042100e0420203040169101c40b624031800d02c0d102c0c1000101e9440f00034030314840780003a10364941807205072070642e0b00200c0d0604180c40b40e2003214090b050740b600030346203040c9400340c01911 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801973561 1250 801972311 801972313
    0x15050607051209011e0c0203060c2104050f07060e010206060a140d021203070b0609060301090f1e060c020f01150b091512071d010519080402041e0204210203 69
    0x10407100055040250494440b4030305101c0080b000e81c9541c00c41560107641c8140c16151b40c6002d000c0c07401410325110000381702c8400d007501004401211400403422407a103044641803480c861351b075440c1c00c6040031406500640306205410001c44c0c0710b50055801581c9407002c1e8211a0320f0f07621701e410004035407420b1007041c2c009001401c41440905208140106090020b040a007070300304c4400b4020701d181d00904003a82c100300700c80c090100a18004842e250000c200320024413400215842c0c09003174540042c80240b8603943d143c0c900101c4101e1502e21402942c20810401c906410030320701a4444a0340d503281c0010303502c1c180074000100d081e4034415003941c0ac105c501504160401e02030080190703401841c3c500044050003410f03401c0070125200d9104089955600800070180c00f04a011645128406c5050180602c07085480503141103440c8280c2c145841d100c0c2e100e80b42c07400480c0003850005400c1c501403c99074030403a0910f00c9a00144200c490032448071004078665030040409058041c0000d41c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801974811 1250 801973561 801973573
    0x301170d0806120a0b090c010e030109030203032a070f020f030d1e02010609050a06081e060403260702010c0e09040c0308070507080105010312090b16140703151505060705 75
    0x550a00e000c0444903402400200c601e80b520f540c41d080100c0001b242c0b2101e460740240c165081c43d50b801100c030440f442040d4002e010921040d640a5160b010040001c04031010500d00440d201c9513080a0f880400c000e8074006a9501641c141010b8140c655401a4014409168140002d060000d01094810a01e5480500b0110050050f40500c1c90760441c040440d0b4a918004ca16020356201c1c05c0e000348010400010140c0c030300145103041c82c03900400310712003141c0500244544240410303244d0303102d9854507060b00c407c508010003005030f01c000f83da19400f819081c41040081c0d5015030141d10416201e032640c2560a082c0c038100101c40104940040101d110f9000410000ea0048080e204140c40f5109036110151105000c500b111402d030300940301c403d555520741c0c0c040764002ca4001d010304402040146403d4110340b2085194040c040003c0c10300e000718100003136507031081c001c0401032756100da03050050010054441d0090007103030724a117106d03505640d000221440d04404a400c500e5000008d41f00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801976061 1250 801974811 801974821
    0xd1113050405130204060801140c190e01051917130c12081207051201090b010c031103130e180f0d0f0e0607061505031f09170f0301170d08 61
    0x9407501510f0044144a03000e04403006a403107002d072001070940c5600024850320500d00f240d808050180070204d6240301000078480c1103000d211614003920310740c14207591070500040104e030f06220381818042c40c0e401840d100720403d9030000ca11038507009030000055003910f0742c40300f00300c41403444400208040d038914410022841003040c4c40c281640074100e024100704150005e050310304012a580301c001071000a10001c12410811218050000400200a410410030018202d00c56124015003071184403001881942801c204440c00e40c98a041c1c0320540582d40e142a142c01d5000b80d0700c404074400c8480b00c1d00d02c1240005102c041d401c940c2002005034131903103101138400160b41000c11003080206074801d04d2503140d0f80300400180348140c00c00200c0a43c0c2c4003d29106100f40e4100e03078403a810079031001d1070451039130010403000842d03414009003259139032410040d485525134101510181c0818403460030500c0c0740203141200e02c000c02d01d011028440320b40e29100c0e5060348400c00402d0f505800700d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801977311 1250 801976061 801976069
    0xb0402040501122703021c1b030c0501290307050907050f0c07261504050601091a091302090903090a030809010309060e060108011104030c030602030709030f05030d111305 75
    0x4c4070018241c5070321141201c41e00b0b020081c03100d0344d00d81900568420800314810b801e00f841c0c5004c2e5400c2600e04200144285040340320003802d11103002e400c00084c1d0074040c0c18428290312001507000c41c250001074140c1c0161103c182e50420064541c441c1c060001e00096604068403050f10800003503550920380307000c1228110164000102d440380034820000041030404014000c030303d01c8908060029401c9542180e1289840ca0355624401100041e81c00d200000d00d0005425066940c1120081080b155155950112542030000643e00140d07580c180441740708104100c040782402a101141103980e0a255140d0f070703125000034290040b10b00c44082005c104640058076480f401498082003441c01071f1a020195a20410300c00101e822000041001080c01d2140049100342c4e000c955040038a1034480303090304001840060035450700040000d039445e00c58004400034582c84044000b83c01444d0611070341e01e400c05111850030a14104040c5081d030350103016510040384402800101d2402d100c00c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801978417 1106 801977311 801977321
    0xc0a0c05060711090703090506100302031c0804031b0501092f010c0609020a030228092c0c0409150b0904080403031b170a02010b040204050112 63
    0x200000e5814407035118a00044580b0034107545c0d612800e40281c100404000c1890180600704010b01d8100240d00c82620b00a500b101c03403040704910301039184560b5102c2c14bc003150134000060002071040c10452240060342c00402103460f038990f241425a140c040080303500b014000807000941c0320811210503010100c028507100080301d0b4001a001c55410b80c0040c203d5600d81c0d800c4030554507050494070003181e0241c41620503507480400c4081013000e003030300c0d050008a000c3c1300007280400e0340601074202d52542d00444101e041c9800e07000001c1d04c0c0d4505100180284080740c1c0980c0c1d980e11030f603c1101d028a11000390301182c00d8401080324030203504184108070080c00c1c0004601c2d460300f81c4098a80c1070500c1746140d54020040c0350b40b8181e002e0010011007007000310381140300e40e05011b03081e1800355400074030080c2d5464040009901481c054940000d9410003441e01e070035400c3d005 = true := by decide +kernel

theorem cover : BRFrame.Cov 801798561 801978417 := by
  have h0 := BRFrame.cov_init 801798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801798561 ≤ n) (h2 : n < 801978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
