-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:57:08.984986+00:00
-- url     : https://prove2.me/submissions/974d3ffb-4168-4c20-aa71-7be8f7ad7359

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 223381294 ≤ n < 223561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 223382544 1250 223381294 223381349
    0x80115150e091506090405010905182a0303040b0c030a08060409080414011718011103130210020102040b030a06050909070e0606130308070302010e0d0c1a0c120f060a05040902060301 80
    0x981014101f0006503a40b030005038001c01c0e05540039403000001c541450503d05d40000d1203000940a003078038660360320008042c0036051100504854141c0401d01000500c0310401001d080c0801252000e513a80c1d5103420001040c54134001c00c007d2041c2e140914410101d240181a1402d07109010069502d85582ea40160342c41d500341c2c0b00e200717909281e80c4100b0080d040b408908501c03034450b40340244002061410146103d010899103001d0f114040e0740d03010003500e040102c1410000300f500005141649485100103650320450f40c0180b13071a210a01002182064100300b0350040c0c8410141c007065007000e141100e150005440e8034450040400c0018164541440f2140115800700b07409580e04818600603000e000201d42c50101d038041e955484560a0088403012881503101001c0c00c1e0888144080c400b01034000b80000181090900402e4003021300c0360303000343c00750401000343d03111460720340c040081c110381c0340e0031041c080e40c00d14094500588070b100a485c1501c41051000b40141030399403031006103 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 223383794 1250 223382544 223382557
    0x60a0203070c201005031b131a1306050903071e0b07230706140a030e010c030608010608010204030b16020c030a030e090c03042109080115150e091506 66
    0x1a00400180f01c0d40c00010083c0112514007566918803103030700798805554a010031240480351090740d440000302100f04400410030510600746000410762581c076404180865481c2a032200e030740004144000d03043d0602d03008020421460814030345941200420703200d007600e00c120003070320b801c1c0213141c0714100c0012034140180c030700e0b002c0d055121461424548031b5554000340301e40703403c5031112580803001004508041592001d482e2034191300d500c0884a1529806174210004160740c4030f5108440d05020b010b0171345200020780e00460710504140145003141d90550016003140e10401081001900140d001039110005100e0740d0030303a0b980d012041c0e00381004550702650501a18001e08201900708205190015003525580c00d2969020690011484140c9000c0c01d5650b0001806c50030078121202c103844103001c0e01d0f00e0030440395208032071800d60f6048015a510603e460b5003d100240c021140c000014815207411004241000d01003030710f0100c0605580d034180441150340b1080d0b140d01044618 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 223385044 1250 223383794 223383803
    0xb03030a0206010906080a2a17030703020f01020c0a03110a0206030c180103111c0e06010617060402040b12090c0d1505070804021e030c030607020d0f02030408060a0203070c 76
    0x140d44000c040000d4a0310424010f10019a10b80307100441c5807200002e000c1c80c1d180d0b00003040314511010940c40c0d024081c440f10140010302c0321b400c010881605152000d12800309200080d515500340b881c01134145842880c0c0c42c9c42507841071003824203698000400d800100d400d810441c000f04481440c041c1050001c1c2d034040d401020000510000540340710041c50041c0c00080c0b8907100382c01c4880110255200d500966180031401d00c0503840f030105d00100346401101408000a0381546945e615007040426070080700414800128118810611090700d60312070012681149840c0c20214002194082c06800500d070041d12000119541d40400c44080d00c214014039403940203006181410340c00610308001541c0701c1c1803102088501c1d019603410b501581d8003e100d03980b004410306c41c0c01007080c025a2181d030301d481403a4031040c00d03860a11005015542c194007801c04001002c0010700703a0210148080110340c801c110070072910b500421143e401003006440940d0342e071207400c003c0b101980003110241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 223386294 1250 223385044 223385047
    0xe06090a0306050c0910031a0609031603050610050d120503090f0703050102041d070918060902070503071e05030403060b06071202010623030a261207080c0403080910030b0303 77
    0x89404c858405003030000400c80360b000362100700d82800c9060ba03d551598039040655984030111929002016021320800902156000d09418840e188010317002e900a866503041241030206540c6001d100901420059a801c0c20021050351744540342540740007007000300038003c00070035000d900501882213400084030071640302c0d5440b410040d00035840392050b00d503c0b84075101000f84588408090030710415072604d410b404545424000c480e14051303a16000d215943d201c40202c1e07118050710180c0f1089005100546c0c50b00102e00d0007800040c44095515560604c4e110042d000035000000c40301620707400700d4081101d030f100d00045031181c05072081c0102003e03a80300c507502c04540e0543c841c004443c0040140c842c0003c1c164a01c00f0044010a00590984c01003000100456606c106040e04585801e200384021302154403803000580103001340001c07869429091000c26681b2150309504000d89100d45450149035503120105442100030720360042803405200401c21f40a5400448a900f0150569 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 223387544 1250 223386294 223386301
    0x90501090506071701060e03061311030703110301050c09031c0201090f03050a09050103020307020a030305090312040807290a0c11010e071a0901050301060c0611120603010e0105070e06090a030605 86
    0x500300c001400e0b0400004e40c6103000001c0c84138401c244a50204802401070421034442c001142c1000701120000c3c0c82d9480d828941d80c1582d00d04020703600003035020302801c85181c0003031800c150969802620b0f8442c1c554040c000301c15240da0206030150015003400042c1c003281d103490800e9000d0419050082e0001c44643e540c0400c2c9a040707402010807581d940d03a1522201c0d2150010f408a010680740c000059112840711070019009a004940140031101100d0800300c0c0c01c03070b07914201c040c105d4040301e1030390000c6102c504010480c1e494031200d02e1100c02414080d0750038161400c12640061501000c00c1c0c0b10754031851000d00900c00c4540000f00c180081c412002090225942c900140c030071103828030351121504c0c0d08010b04000342e80d021401603484c20f146900e040703000c440340c40d2094415610301d9501c0c81580d0140c118140107001e92441104898070501d0540101400c643c5505081041d1b039040900308802140d0002d20043d0005e402c40d0b546450340c05842c08101c0880c02500020040303858041807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 223388794 1250 223387544 223387547
    0x9030a05030421170f04030206010b071502030127051905130209091b03030702030a0602091c06061a090a0512030706020c0708070503070b120402011724040209090a09050109050607 79
    0xe006202400c61340d81c4401791101d03914448160400c44002c2c005810540042c00450307106001400700038010b2100e110a8105141150103c0e4000e0380101d41e40500382c503148014010010580c04840f440d06801c10035450007100034004d80c090700101d104003d554000044c211400d2551800c855030300544204d03028600402407aa076100080300e855034103414800c841400b441c0c004212960307154003802400330101c0c0d030740d1401d01941000c210503a11404080d1000700400308003030a0350366140242e4011031a1072504030284c2c140800d0454807075400804000d10405500d60810b034204540f010350b60340c10640c28060304c00781140035031140180014000246d0f030314126800034412050781d00d03007030176603031020b81da00105551824a481071081d0104140101d007001503a41003207070390190040c1850b407000c4840c611042c1c9051400c42c0c8010b5208048102c11340011400841c41444082c1502c0131860041804006241c40e0030003000100c24507200c9440000f005001c0d00148503440c0d10404499490908510 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 223390044 1250 223388794 223388807
    0x106030b04230f06030a0809120718020307080a020a020a150f0603060e1b0102102c030318010c050919080d2106120f021503011404060e09030a05030421 67
    0x101e942e81e1010283c0070820528011035240c40c0703164000701781c1c0d01d045031445c1032045410b140107030000d070750048180000d0903180074408444001c503581c10040e500d00d05210064600300001d421a48500d01c103001111085400140b4000c8040e004040810030b103003e60503103000781265034420344070581004000001c10200d13800003081c2d40d5190b01074035003a5402840c5103030a6504914402e0060307014034003409582200b41d01c512540000e802c41c0d043d01510584402e8440d0041d5140d254041c1e00010810181c0604020100c0c54800c031980284600750714040001c0c0175000340180c0354814000b40303080b010103124400c2080000d020200903503252001c450005401d106418912808840801c6191000d0341e49074403540e400c1c0d41040c50102c4e00140940c640450484c260701c1d04903000108800d108800c45019030166008140048001d0101d03c030402c284815180396501c0110701240c101c050020404010064882c09084c03450561740f81d2f6240d01f0f0060300007404180e5010301c48105078400c40c9850740f108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 223391294 1250 223390044 223390051
    0xe0706080c070b040b0406062408060906010504060509060412060605330a0e040912090509040503040e0c0d02070803040209160c020906060c160905100e0106030b0423 73
    0x4903021116900c034000c100302485041c2000b0f105954900015000131000480b40750050b010b4000000c009480b105400b41180000341025100000e030019010584e9009585691007441998514034a0902500281260140340034076800d000b0041000c100c103440700010382c1c006050000c0c0c034201c050001d080110040106010b501c0c000c5011190513100701550001c900702c8078019000f40c52007071083c000b10a00b107030480c081035010050000a41d0750280e9481c001c1703502c0d05020701c104008500c0c94401c094140c2d841c0b5840355000d5810f060400010490100580d03040b1101103070405207075079640c1c0003101320740305036081d0b40700c410300c00701d0f450041c41151005075100d1071098903500c04075210030002540340400b4100c0c0d42d00140e00030340220014240441c2c1907401201c050181030903e00f21010315400c01c181d0000c0c86691038070440040140c05464015150003c141c00c000035170560a14031034021403070341405000c05040d1501200a800e4855501c41c040d2048001000d00b10b004d01c005925400c0340003503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 223392544 1250 223391294 223391297
    0xe0108071704230a03020c09070903060212090c220b010504030f0501020d1514280b09130608060c09010c060f05040201231806070503030c030a0c03090b280e0706 71
    0x780301c0b203c0280750000700c00b800d01342c054000301030306224441000000480145003c0402c18003007400800038009002400340307152070007026545454101e215519240e0303c0e90f070301d9108258804004a002c1c05c02d665410100350707600c00204071401ea00d00107882d544501c1e40010031610300c0184107418004194081c2401000051061191200161a0003800300e00e0303010302d2201100319101034807035162004540d2408e80e1381c010f502c0e40044c030f40415100d48407440c1d4420210345000044000ca94038117100d000c0001d0018920400815090010940d0343d01d5004008103100100000c0c01c000c168042d058900e4221307842201071105c0e034894000c00014181c151012070102d4800011540391002208000020520807030085040c003544003000643c0e820041da1098210384104040c0c00827520501c01544a41043c1085076584d06000343d100c012191405500c90406280c541d0394000101001e4541d030700a4011142070740c80081d0004040c0315114110a20140b4614010304170a1182000ca0790208641c000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 223393794 1250 223392544 223392593
    0x6190b210c03010e0108030306090106030e0a0203011107150908090904030e030118020f01031103070c0611040605090108010f0503070303080910060e16092603040e010b0415030c0e0108071704 84
    0xc86c46982c1e030f24082643c802d584400c4500041c807409110340d011058000c6120304561b02c45d6200c0d00406e085604400c0c0085804c200000c0c3c00c01448420003119002c0f00030501d04110441140e0cc540035030340500d40391903120b06003840205007803500c5072040d9045180014000c00502203a1071b9038122000803007400303c3c05000315100d184101e6000344654151084503001c90f40c959075440500301c1d42440450801c94101c1d60383c0e00d09000400902c4040e001038042510765680d10140b81001421468050f44403507940381702c2030010f01042d1808103c04048035850b06100c1c103191a40c1c46c41509004210b04040c101d0b030700c0c00c1e000190031203c8140841c0540f50803204140c216410081c100d86201003405102c0c60b003240707000c1d04a00c18103030a841d650035188000070750342042e8640201d41c00d546803c0c0c0c040740c10701501140a11180a00c4036091b405242d00b410200980040784c540980103aa010300c0c46414003249000140707a50380184000303186003103906036143d068641407400c0b039001c1e2103400c0d200004054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 223395044 1250 223393794 223393799
    0x50a050d0203010b12010509070801090e070e090309010801051e0d1a070c140102090901210803010e060102011802010f14090d14010b0a05061c1b031406190b210c03010e01 75
    0x40c07408e211030080c5001c0c0d0b2841030507802c1805a4000d8a10074003182d80e107118120f8000f41003400118443d02451084028655501c0380200041001c081130308140c0c4a107069410000184d00f040c0300061001005a8803c5d401e07050034100506000d400c0b0804c1400b0003549410080340b158480121381e071062040c000c41c1402003003441038500300d019042c0388a800110700c2e070060055040b0418500325404054003070964840f02030b82d58240390f8100780d0140421030321360414041c880d03070280540300c800b2513400300c109564260341c3c0000700844c0035502d2950501441d007030359144600003107084640e01c80c4040c0030303100321442510b0b2000c0100d028004c40d0002d5444c0c0421a03085180030240700003100d02c02007284d81400c410301d440405401448a101540701ea0740c0585280c5480f8400c0841c160b0140d41e280000c0c44583d410742401c0200000f400c1038842d0180c2c01500ca4000078142002c001e071445107143c15180c078111442c0203652460501982294600c9000f08401c1a585400960582c1c250b00304021191760b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 223396294 1250 223395044 223395049
    0x50c030d1107060302030a1104030c061b08120604090c0b0901110c030c060a0e04090305030103021e06041a22031e03050906071b08010c0e0a050307030201050a050d0203010b120105 79
    0x158090010092504200400c0243e640300750082c541141c0802e01c0000c481040307031f212001c035902030350084039890902c5004220841e0090a01005003094501e202024211655801130900c00c04901c0001d024202e40401d100361169030014101070341c0300144101c401d171500708190194006181309800920311101d0030b00300700c10106400e40c02c84c2c8054000d00702c00d00d52100708042c0c4d030000840e0348104521030200942d03559560041005940c000e80311142d603941913006100307599600490b43d051001c003000100800791688404c4900f110702800710740c4040b03a51050240710310f1007042c4c2e000002d004890380000800844c00d10300c07802c03a4070580031445440119040000c050f0305001d13020700840c2d018000340040c0d041860050581d5841610300b43c0d11111084140d0710000c216802181041c3c1d0740360311a002d5150800820090000111030940100746050006aa1848940002030400ca00400c00c503580c41d00410640d01000d00c4000c3c19074a175a150360503810325070480341c80d8000c140581c8000040a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 223397544 1250 223396294 223396307
    0x4051605010e091605191d040b0a030206030a1524080405030403020405060a0503010f1a040905120c031215040c0c030e090c04080a1103150601050712031503050c030d 73
    0x940c00079211070b160303913160804007072094040d284020a01c00e04000c421044503985601404282158031280b09094602a01031813001d6a559550700592620304c0b00f410b296030f00038001c42100da045031426580c0d034884902c20702910100e0350300d52204401000c04100d08612501010b00003901e498100740e40c4000000450b50101c1c1520007410179081000f003840981015088654400c02c042c0c030313001640d6614804203003180c01c103903500303e481c698501e158041203201d81c4032803c500c6d004580c10300050845440302903c2d0804564200130b011f0000400301103c2e00309000380d840c0c03101015074a041c036142c124145c01c20607848003403d91040e454100a10365490050b10b2703508815070180e4400c07081d58081c000b801050078000c0d0041e1300c09035082c44001500e850412101056910076040c03046841c80c50802d15142c40d55443c004100e400103141003144990f48541581e01756034014940c050606410b14040c0c005114444800390441200c49010041c40000a2145015803040c0c040ba103405103044402c462130f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 223398794 1250 223397544 223397567
    0x2d0614100e0106140f0307050a031407020312060d2307060801150f0c020901090605040b0a0e130c0806130b07030b06040501120f05010f1a07030927050405160501 71
    0x441c0d0075400620180344503514050b00915500581803070940c0da41c21244154000329400700026a0004e0700c84001035040c02a040449110160f103051030420501c041d4690041c103000e50030301038000b00060201c1c0d903000c00d60f691a82d0000603858444046070191880306090350405101031080b2040050014480c600d99030403664540c2c403403807100c000d164045402c40d90030b4140c0c00c01c05c8000d400d01e00140ea5107181082c02090700c440e000070607510300780034001a29030205440703100340c2c02043d04001c1291390100781e540c401c1c49400300300c010810030720f000d40103141c0c5a00014050302c525010401c481040449a07400e00340100346c00c11030395845980841c03d98280d40401c581183d4203110030041d80d4000d12000c2404241034502040801c254a070400071241d09078001c06248086030802c20900c049564000d0950000203501450140540c502401c0e135240c0d40f043c0c1d2000b11040145031400d949494100d02c0081d801c01c014000350505061440d9603440c1c5800000e04060070300c800184a42c00b500300d0300030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 223400044 1250 223398794 223398809
    0x207030506070207030506060607030210050a1b090509010b032805061305040f14070803180901080d080c090109030501090b070905032116020619020c0906030303042d061410 76
    0x1f140d0787e81100740400e5800c801c000714154400c010f01e1080810344c078000c0d5407003942421800210901241c188592a5900c142c4c1c0d0340a01c4105603040c85079464455882d41541c03500a60b0700d5581d1581c0780843ea41103015070300d0340c0840080c1403003800d03a0365203038000038013901007154010700b503000e148250f41c200e810070390f402002e0101103134081000501605604400b1551003060f2002581e407116828155840710540c501d0f03803d4468240080b42c40d0000071170f40034144c0e50300104816106018054603240c00030303116440710107000c01c00b103032107270301c07904080014550043c02400100c2052401c201148801e50b00c100c04104030000100d40c0f8200051056180d640e00c3e201080807051800000c0c0d06540150015103502d8100c00311140943c44407001040d080c596100c0b07074031001d8012075000f82000c08210486128140b10028050750765400002d032a0840d800c0315124030480d1100c0b000c0d0302c508600d131031000c1c02400d031a25004103000107170788050321401c114103e100c866038034078010320b81d81d100900884030f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 223401294 1250 223400044 223400053
    0x20a03050117100c020c1c06060e0f0103080f36040b010c0209060f12030304150903090b03072007080105090c240906030411011b0803011a0d05010602070305060702070305 75
    0x200d50a42c90f044000c0c030b6541c40c01503800200c0c400022400400480c40c1e00c0322884552a040d03c10400235104080c02045207202090780c5051140030904510010301c0080c111000200c0c0c10210642200700700c6800486482034070a0b50208600918603404800c01c0d03540d10003030800f1a200150409004082d40c2c990140c1d50341e0f50f0f111240d1308200410401416050b0030106040c1038880d1521044001882030954000868a03841c1902d00a4120000c0120402c0704506100c65034000940045100054400200348103032241c0d900c5c28101e80c403892031100700e00d000340e400e048521100004200d090654410100a01c06585c0e041c4405030b58241508003150008030301a01d000088601401003100300404034881480c00301d00d840055550b41060b2001d9a007904142030078182580c0000303a010407010000c80201240d1029283d003140c500051041705c0460307241c440c000181c5040c2c2404c03a0101ca00111080120b0758503003000942d43c104900040300d0521802d4007040050f4000542441241c0d400701c002d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 223402544 1250 223401294 223401313
    0x311010504080a030f02070503070602070c06110a120302090a0b0a090803040b090d02010c050f06150f0d0b060d02030102040b0705060c0415030209120d110706032a0e13020a03050117 80
    0x120005c0c42e14110040440d64207000ca03600050302403000b000d0039400755002684420460a00c2580300195610540034801c42c22180f520710a0003255400c07060303810690503900390510760310a0340a0300c50a0082580602d0024020944856220140103159201d1380c40304940ca8a44540b50358903c2107001d0034100c00d8040c040e80c10546000c034130700c155440c410324000709022070981d01c0d645450f40020341100b4540001e0104881840600111604000c08a8079820f21518400220300344411440380500f01c40c3d11140015001d480b00c84459103590b5018008560300d03a0346102008494200c59011102800740d070340400d00300c02d43c10045c4c40c1a640c10f010081d0091445540a1703009600054241e41c05c542020b1041c40c89080901c0a41d8441d9130517140c50019804005200d030a05d5110741109040c149801004950085282039010510300d280701301da01c2c1d00c102403100b070b1816886d582c002544583e411215001c00d40e0150003034400c2d001e180d01c080c0482d90301c8a2110140f02080c0c906021070ba030044d03121 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 223403794 1250 223402544 223402547
    0x2090906040b040920030c04050708040b07021c0203031e04021806150c010e060108030c0d1b05061608010f05012a06060602010903020f0c010207180e06070c0311010504080a 76
    0xc030011034070003000019401c0c07160340c1d070f102c010380f554a6a07040d4171000c400c002e002e030900380710740d08010340e0072101080b8a28050320080e14650014002801d225540000200024000c0204050f5888440c1d62841c0103214000c0c000d55a510840304207031030111429100301e003001c5100b0a180169801405000311842e12010013001d48002045164400308200e0b00b01c034010344140c010304032103000348004600c51881090303d503d00041030b40807240300e03170042080c14601c0602060010780e00b01c0741d00e070810b01c0120091402d80380c0d801c0c00b0b0740070300140590010310406020031038110700c1c045034a441d08041a070b6266009035401100d0312560b400f0a44500070706900d41a446400c461094005158000d901c1c03180c0c541004031150fa412100160b9500e40303080050540401c401c8403000c1110000f041d80408510000b034441d1000e2182c008110440c207185085401e8941060581d221450102e440d130380303004000107001104c2d400e42a000703e1503002034070381b000708107000c0c103480740d900140c00e6850107a40080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 223405044 1250 223403794 223403801
    0xf0d02121606050a0206101a0715181a040c060e0103022a1b0d0201050309030c0a03030b01120507020705010e130e01140609010305070b130504050f07120209090604 72
    0x141840680584010484105940c905000182c180c070790340d650710b0b843e2804d0003900d005805412014461820041003148498051b104104050380c903100d503844403100d10700802104020400b00324024145030b80c000110307034460800180140204a54400054842003103095041c0030740d0090504a800e0340144030040c0550590b40340320720107242c0149400c500307180000418418001c0407458120400e0620380f083c0c0e08004941440502512041c00200d428001803c60040900000d05219010002407003008081c0107031035080c060354041d25103035480c0d458010021300c100c00d00540410442c021b4403002904038803a10340300b24440e400406034641840010348001030080c01e080d0f44000c1c40c1d04003844411079402605541c0d01c028001140d200082403071240581402000c01b80640c400800403c0858000122001118488080c245e512006040c4450321070b0015005217810604140c2070000484005590318450183d6980b00c0030400c50148120050344240c1e0944e55000b10f071140407840c036203802c0c0e1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 223406294 1250 223405044 223405069
    0xa0e01033314030c010512040c030c0306020901030f05131416060314180703061503060e0a060e011803120f24080c10030e0f0712020307050f0d02 64
    0x30404084900381841c00010031280444010082a0003000c000040701d03410030100e2058214050580513480c840003e2003800b5411442d180201c200003c541840405950f11000d5904021040019900d90034440c000c2e42c0b00202042c00a0b103041d1700203210f40030a10036180202c0c801021854242c840d5114068400040203032001203004410b240c8003480b14202c0542c008049944010272148000040d0308540301004180000060181d0110340740030320045100300960394400c0c0f000614481c404180c0d400021245c00c014400344c038002c070788080d10100148101d05184607080902240f501c05840c2d0382a40d280d10182c4440780c42e030300b030780704c0019000390310300400444c91070f40019100c0044a18001940d8102c11404c1010026100548003440c0c0c10017100d001d0800300340200b040c0c070111000f00303030041328010484040551354898950b1180d0240640b100c1e0000300001c81c1d840c25252042001c1c80060901c2c101d21078890111b0000d55800d100800000c009002000b500c0d40c1c000d203800b402100c000d1030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 223407544 1250 223406294 223406321
    0x402060c0114090709060b040506030c0313050703031e09030c12020414070c120810140d0b013512071b060210050a0e100c051c0509120a0e0103 63
    0x500c02c0b40705500e001076040d486000040014000369240081c42e1080f03032103d0704112500f050400080c8510385903001280d41090005d6a046d941c0d0b6a410b604040c4000c034004028400d015090000007415071002e06001e100070b200d5000313454084d00b44003e0b1400d8500f84070091150480d0a000c111070a144401044540d001030f0002c50103004465881500790003c45000020a100310791402c04d10501e80001e815081860400c0425400d14180c1ca0981410522545540b822511080712094803861102404039030700061300201561181c87e440e401c4000860348030070201c044181001c59505010824000010303c0b005012508980440d0320160f40c4642c1043e070b0303144e400340d15000c3c050754261011070003494958050015000d40ca0007036000c1c0d950292a0780b08050600300413481451011901810614002d000000d07218000c0c20191203501450821560581001500f000c400b031321a000305101f40004000d5664140712007054641a0048011290000d180d21840802550081e801a600c40140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 223408794 1250 223407544 223407551
    0x317090a1707020d0b0f130f02270a1b0207060e091510020601051f170403030e01020a030e07051008010303210204030501020c010e07140415080a030c15050106080402060c01 76
    0x190f00841c0011080c043c04640c201c5000f401c0002000300c0c040a00d8000c001d070318070101d401001e600c0b21540300044030b102030300c145005598000074107000381d00f0702c0645910909240540c075041c4d0001004080c1032400f003145014814124600920100e40882952459101c2c00341c015011007d204005000070629000744980c0002c0d03142c1d81c1c0d203202c0e0a08010b007803540100890360622007400b03134240786403555845200c0d001041d2850360340c10140c01c1c91042007203200110907680d2400d01300d020f8900d1303d410f80010351000038000d4250b17a00d60885920203280c1000c0b205100d55800511581050f0f0b8456940003070225401400000c2c4189000c00c0c2801c04108202201000182c0035801c0780d006610417070381c60390300280c030880509080c02001900142c2e64040d00a6038507040014081c4078008401030702ca03030340c0c0f5403030401d54207404071441d00a010a04102c0d401c00041340f501500752010200296140082d045484d00030300402d0003010306a84a5960301222620b4a50030b0260a0308808a1050b09548 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 223410044 1250 223408794 223408807
    0x30906041a0c120706060605070c05061c0e0a1103070602151b04121a070203090f060c070e100b0301050f130207050d0302190801050d020105090a0f06020a0317090a17 73
    0x60401c915540f440140e0300840d502c0250f40342440c11503c642c0c0c000d80c1030140c1800401c5c08102208520012988280c545542d42c0700c0c0982c61090075140c2c07a6030014014a403d1100e11005c000185024009200346c070001c0041e10300380c0401d50394294910034140107a100c0200040007c05a420701e40c0c120210203054000c641c8980720100580d0000d420031415000017a01c1e540c10b000b0500e17035211018500805002103418008802134482c03003052281030059012880216803030f19070340e041341c41d583c820800f0303180120340301d2030110801d48040d02d4106c1c940c00304003404a02d11181c0411607049840c000c0000740d0719100c0740103110301c3c6040b0791300b644003040e0b013804004086070060000503d507200c039070340069641d0f80c40001c106512030185140c00030405c10f440103001d1038845602c0302c8035440d02401e0190b292014000040c412036100d801c0031890361480345000580580006403d240c1900c252542d00d17487e0031b1104010504501290321144a9102200c030b070010603241c506401c003245800c0c1c1c54514014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 223411294 1250 223410044 223410067
    0x9020a03060c080601030f02070c050402090a030b0a09020907050a170601090b0a09080f01270206040510030504050105060409030203030403081503030f09100306051e0f1e01030e030906041a 83
    0x80c960710302e900104044004000d8650713414071516041008801086003801019202e10440c40e840f070213001e0140342d0000b0400c0c219598984040021688000800340610f0302a01d940003400c00c58504074082c0381800089844240540c00b900d44000c0580d9414140c80d8607400c5151607204050000d505000036040042000c1c003940c001001d504d80c890700d90780c04180c60050340c2da18003140c000c0032408d103900d0b080d00348071801c001503a40c100e50308080c01c5003041e0790f24500004945114030b5002e80c2c0d1003c54028848041c0e50980c014038030584c002d10003041a60ba9200a010940c0d1002c00001d00503041000005c000034026401c40f40c1120050310340c94122066040424174540c0a00b885009120000ca4026410324003442d50341d00c52040707450144441c520b010085091650015074443c050099400d42d01111346840141e145d819000400079004801070018079451005100320a0313000034204480c06c82c404100100311000340c0b5000c1c000b039190500c1d041c113070302c00603030828925050f04108000d00d00702c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 223412544 1250 223411294 223411301
    0x3020f030a150905070f0e030c0303030906011409151c020907050705010e0705030a02010c050c0301061403010e061605090315090d080a0606122f09031504050a0609020a0306 76
    0x150703100d400c006400682e58031101ca50360480d41c001c1d9121814102000400c1d0b604c07050481200e21503007450038034030350000002030034a0f42d0701100e950507110200400200c2000001c10368103d038021512810140591414044002c1040718910b01d100000e0313181c0b203110300302409041300640e1504001400a07049500151107024151600000501d01266040c244002031244041c0204010000c00c00d0500d004086510b918202002a0501a4200782281840001d0195801858004008200c09501d5820000e00b0f0441140c01c240258078100710380c4082100010121301a0f42529850080014601811a8070f0b0303104000d205d4040c058903400b089084180c1c0c1d621406000000f000d0011403001a034018214400180f01020150600c1c0041084c242c00c414202030702000280007040c03d14603410b42c1d502004182d40a43d1003e580c04050b000c444c2e848401601752203504509640414466988140c0100000c0e5805810380e002000c10300001800d95000181052014000b1200555071b604d540c02107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 223413794 1250 223412544 223412551
    0x201031404050319030501030b010b0306060d060609141207090e1009111f0804020603070302121003060b030304030b0c07031e0201020706150602031c021c14070309120c020103020f03 80
    0x180c2e030001c140c00b0101c4c05821800c4003000c8651804100c0ca44c903540300d80d80440e2043c481c40c844507100002041c071070f4907940101d482440501c0d10501c4041c0c0e485034014101c3c109840360704005510302e6490f804610b040c0c1c56004100510500400c0c01c40c0c1411500801070180504000451040c048031050064043c028001004d0056540c49503d0208009010314a040d003240500302035440340400c0c1420f0f400400c5a40c001d901915265100d81d00d82c00294024801c202c0e000d000640c1c100c003082000c0070001402d0701500e00c201c009000d42c9254400f410355a000700e000081c06e00083c5000903080d0810360004d000c219010f490f20b50130080710300000c0900141844030740e400503500042c0c44030920455010f49030807556148880201d0b50b1030188004d440c4c2c000c05c61040c510020340101c0d03000902c0c40c0d4040d01d50303c514000075401141d1403941e41500628090540781210001e010004007054002c0c814120f0080d0004941000c3d0003041c8401c580b1100d0300c900403070500d5400d000307018a0701b41e1400690712 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 223415044 1250 223413794 223413803
    0x4061d06041d04060b030307050d0f020307060603080901022a040e03040915080106080309060703080a150b040303120608030a0f0302041809021f020c01110c15030709061407030503040201031404 85
    0x2a6070030036081080540e1140d00d017150182e4400c01c18174000030300000e040a01c4120a00d480501c41c4080e403c00c030308601c00c0c0c4d0070103030030a0304200307000c000e000301a802088904001d808407505010602c09841e45031055203040c000c901c10079058442141400d8004154005680c000d90380381036180c108400489600820b44027180381018018080c094003485514090070708600110700380444030000076018882c0c514014100484000841c01e00000d5070003011382954046c860002158403100508240e42141c130043e4009120311100035003031407241c4610003c0e101c004001d10b05c1c20800803401e9900c2c4102030501000c042c1d00304000100e100c10030040003030f11810032102040903c03a074010002c1c1c0001c480b00c00c010000d01815111841c540004544156140a09180072080c05c00480341d800d0940d20074003190031282c41071103021146d000d42c004612811b41519000d0001e03803541c10441e124100f5110109a103c4c00b00020000b0a01400203507a20503c145401315182d2010880141035002c10b1b1001c89 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 223416294 1250 223415044 223415099
    0xd0f0e0607080c0105010810090c051314010b0c07050108090304030f1a0103061a091312020c0603040803010905011e06030f0f091a01060e03060411010302070c150e0604061d0604 78
    0x2c4802d2090202c1c944d23646450b1400d0100c070525882e007a800c10030901c9a10b20901c02c0000b1400d01d60501c0d00003501ea41200a60001d003980d42c0d2a1102c0540d101c208615041d000340000460298001c014443c081c100007001541803509656522500c070313148010070b0303071a00744080407920010a084034103400ba510a80e408119050b062204110b550f20302c4081600c01d0001908101108420400c4c01404a802107141a12004a840241d0400006410280e00000008200f10a0100c0c410065049034209081001103070b0fa02c05640c29000d02e143d00c994440c440d500004c10285110313070000100c0f4000340304000340d680c0300054610119080000110f0f908600690540410040c0b50308440c010911801c0080000002400080c1c8034000100001c281d480444012071b5039911903415280155445601c0468060b198140d6241d1046aa511880000d0080315030a00505118059a007200d1082e140c9114204103100c03160000024116141d8005105000015055501ca140507000c2621004d0304d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 223417544 1250 223416294 223416299
    0x5150910061d06010f0e031005150603040807080322050604030e010519080a20072006070605070c06020f18040e06011206060503030324030d0f0e0607080c010501 71
    0xe810390307030203038003114003031100807100304001440440c1c503035002400b440c2c040d9854040751000c5d1380c0d8011303081e641074040c81600940c4000c0111075204600900c5104010910726040c2d10800502c2c0c80210707402400d1110034030411000640c8440515044108480300500400e0100d006000c0c0f005e803010191070503800380c0c090005258105c0b000d920f070b0090a180491a0000f00f019400840f601070b699101004003280006a1400750380d400f115824540035440380c005091852000e9441d08004d4041d1640329a0908400030303100c541c3c1400f942628060706060404080340c4840c001000b000b0302100500a5490209000400510087c40c000d0000018a40c4800741c48049024442ca0454034501130b80c07070200d206440010000b03586045891011007100121303804c0c507210019000e2071303211941510010041c00b45c0380741101059081d0031900340d142e0000c500c0c19070405a0360319000c0291404a500114160115442207232000c0780c24002501c05032508a640c2c1e10105943d01400020034070307075510f9005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 223418794 1250 223417544 223417573
    0x90c04020304240605150f1b070501020d0201050f040b0403050903061602120f0708090a090e100f02070b06100216080a1b03030905060702130507031e02040b16051509 73
    0xf5081c000ba10030300104003a03802c080104910001c07124150a5040c4e0101e5400f144540c0282290b0140b40b404680200c81c5480e080a656140098043c1d00c2c090f0040c41071400d03209105218a80c80340c85040c0c00360f012510b840d00c44144402c0c0c0600103a04010301042244001d440410029004070040c8a401c0703201e10781d000000741840c0038440008410313502004440c01200240c2d0aa4400d6070700548480e55540c0034000092070219190b01026030641404111401090003117100c050719a50341000384a501140e01c8480224801c170341d03000b8121000038002c1580c0b8280b0314402094862a40100d0b0500480c5118140c284101a403103126250311107900c1c2020080140005c40c13032580c0c04241030005c64156500506000100d000705030254101281030b5003559501ca035043d0310380001100800140c1000640200907008800307400903401004109203032583e5052085504031112100b5903410800d10702030014014000100588079445078400d00c2c0841803500e030445000d000c003c0004c00f801c0180204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 223420044 1250 223418794 223418843
    0x6050102030708030a1a22110c100e010605150c07061404030f03020307080406200d0c020904020406260c0103020712080604270611091503090c04020304 67
    0x490464006100000000c0c03100025a90400500350b000304d074805000036481c0302c400c04043d1030743d03000400201c1041c40d600303036026000468021034424808a00d49107226081c0e8070543d40f0364800c550006c41020105a41a0700c14201080e01c400041000c07552080050480001021880910580001d8054406408001d00d070000c10345804c112586c0c9050740b030310110314080c510010386400010300004d4100752080c070889035000da000c5200d030f80300e640701d4400034141c05603410700c4020081c0c544400c440b220030005840c5843c50695943e804070f04138039403c3c062504409007040742c01640391400891709141c5d502040c015003000c8215005c821502c402c2c01841e2200512400e41410310411242020610380c121000442c80c4600700100e6603210600030400401c07910650090804104010214000c56400c03001c00580c0915010f0006003c0c0c200b000c0120310403a01010380c0701c82c5540040441083c0c03070000e11703440404502602d041c491403030b0105060f41d008039005c944040c01c0f48404c410141c1da004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 223421294 1250 223420044 223420049
    0x40e060d0b1f08060421020601030c29040806070909181739060f0711030c0307080405090c2a0a051501050414090615010306030206160606 61
    0x164a030000324540d403100c100d2160041e220000d2190500b00c0d02e1080c1e00400740d000c000b80303101011510603142600700076120303580c2110800955070088054a00d07103440050b072319042c0da81005144038a1441c2c0422520b4229060b45503020520810080c4034000390f250015000801307803034001c1c040d90310300f40100828804180d0042c88a00345001c07420307035000020104280805900030b811480b2200c91021a01542c004c04500c4606503c024040f5100c9640c00100040d407503060040c0780c0100040c807424952112003c88101c26501c0b1440300003010144203041802e40d89e4940d10940e4545804884a00d00b90781c0901001da846e00c8001504001a0a10b070000c1e41d403010892203480d0402174248100180e1901c43c0710158594021003400300014103003800300340c00103a4000d046801d1034400228403007400038240b0405100c0d51074502da61403035810b90714a591254110002801880d540c80c1000020700311331560032410581c0e2900c0100068541d031008050b01088845040c0c1590b801e482e004050b20041d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 223422544 1250 223421294 223421299
    0xb010905180a060b070f02041e1506020601141804020f030f0303100b0a0203030a0c0923030f060105090c070f0b07051806090d030e04141305060f011805090c030d020102040e06 77
    0x80268001048419101c480c1d110360480d000b14110b21a14407409c030007944140c0ca140801e19102894484174541902081110a541c00356035040e079036110b80d41540d8070700103d666002059605068030580c0b024028603030045c401070030800d510400bc008039152113580c00c15804035a00c00001d20040030030401000000700104080a46006501c8400948900006e05100842c40d00c0e6103140c1c600342c0c010b480c040050400d4142d8035084045658440c00c0300e41b8203400340c40c0240991520383c445800d020590b1070603100c0c05005d030721007500d500056044680c442c80d0292040c1840d5081c00000600a11207103000f802a0740e0380548945a4035010b00011564240c003a00c121030402c034020a0f42c030b81c803290010043d01401c2c10340c80c03030855002140292280140c5142e0609101041103500340d09160203515081c001c1c011100503170317036003130044140403401e001d50300c0e1615040b0000c0f01e226849030822070b400441c0300181c801440c130704404a0301e419644d01e660703030250b5001728040c0701029001340c0096200c4003c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 223423794 1250 223422544 223422547
    0x8011e0e0d120b0a030501020a120f050f06010c080c0105040b1807030b0105040c020f01060303020d0909020a17070e09010e090d0216060c0201050f0403030305060405090a03020c040b010905180a060b 87
    0xc04074003900070244490032078807280e12181a24010b68581307030355100564000009659910011800500520003801d9a0282e1032604441c620900d503d40702c3d003441414a50b615190a031540c1c0015986451180d00850390a00100700d079514845003030140502562040c0000740e904c0c282500d000da20791000e03541c4403203603512040d01000481c20000590381100c82c15100090a040d101108900302450320030000c00542c00e020303000042550010311003080c2c40c080c1e907a00021540725203c1909921036150078034001030300c0041c00c4060f0042151201d40200d014181100300c82d2603603021401014003617104084050116003007221900c01481450100c24062010703140d4220364100c04280b8036628051141003011183c0c5000469014204490041d600c0b11a01900c8554a140043c09810304031000740c01941080d000c81c0040400080f0041a994190050051083c1e9a0103000040030070140240c10010b40131000034044e11075410402030400d4014107021907285c200d108506540d50760b804040d18200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 223425044 1250 223423794 223423813
    0x30c320d060c021608060a06150c020f01050d0f05071101021e07030c141b040209031b0a0504091104180b01060c05010b12160608060112051008011e0e 66
    0x80d000c04400c10140d11160008908100403401c0745020301e80490503d4031140c070440130805100008105118800e8a1410301c04161100313142c811a07004080c0d8200410404021034005103406849801001c2c010b141160400007411402001d440c80040078400d0169980284052031b1b900140c0d01d820305d2284070080d40740108018031140304841140311402200000300d001c904240c17103001c0104995030030025201c0402864080b00740c4520000301404100e041c3c48055800d5800c2c03e009940f03800c58004d000e00054111840001190440c20a40540c40103112901068a6982d0b2140d084543c0c02100c0b408802c5c0000801d00c021140c1d0350312224140000c0600c1c0e140003400c80440c50341074402a00c1d00000c40e03104d80c070303282c0d01601c60340e0340c0181d100340080800185580009891080f05a10a001e0781125a407150f0139903400b60103641060000b12025012514000144c000c01c1c0c00803807440205a64540c2da10443d421909140c6544a9503000422174962045840c00703801c064000080203010f0442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 223426294 1250 223425044 223425049
    0x30f08010605161103252c01050907020c03060114040509060c071b2321060a0b030307021504030218070c020d1a040501020a0908010b0f010810030c32 66
    0xa2200740010901c0100a480008170f880920040ca0b81060310382d08440d44030f003d844041c400c12024080c8000d036a118a203100c3e115040190a01913032a54030024100e07d074248000c1c0403094400a1410f81540704842c4208000d450801c0518000d2614401401c2c210b0590020803050f01d030054500c46055100c0c070b090012006810080721070881d0b00c40802105144d044d800ca8a502001c0e500070f1b001e059902c0d0b0900401e0303c0031489801c481804031600000c4400c0e000710700e00c0102c0c010481910960021002500e80f200d20360081c44084001404c603800c011840e40043d0041e140d02c0340740c109000c0042010030440c1003420f091942401c060b040c50051b803810080080c54100c1c0e0344400380c80390907a00c1c00c00c0c0c2403104d100320ad8154200c10003503030b40301c40c80c281c00d0581c040c0d03001411000001e200c01c0300005000f501841502d05180d0b00805504901d25003000440394040c01138032071407013080342c440300000141c8102400e00041503400c80352400601c58401c0c0240460700520341c1802000c5046080a095 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 223427544 1250 223426294 223426327
    0x20a1a100902040e070318060510090b09040f110a0b0f1306020a0f031803020607030f020c01021207060e03090604090b04050f0106051b0c030a060e06060d0507030308060d0f030f08010605 82
    0x12217503d0000381d4040010b5072018168801040544818608000c1c0000c2460780d0743c10f002039030b503200380c1480011900340c10712504000840e00a440407540140010004a0014121a40c604000c1403103c0c0c0740d8440c4801c206940c4049003440c1c20309030004410f140e85da10200b05500502090014255140c1c0a440704035450081d02e0000703003000304441d6a85c04a51040480f103001c1c50300500142e4554403640707405441030308140c48440140c07241498042242d0310005142c1d450780d0082d08141d0805100e507a0f14405000110100405400140145441921850050700060020500105818030a403061008460300030f00780c09843c0b40a0720062040c90b0300001119034201a038020421800d028404940c280403080ca40141e150040d46800c00521000f60810f01081c0229425039a65468120401c10748218144c00240160800f250400100e40903201042c3e10400140c40c0708164140e40c0e850501c800d49452049011408401300b070b0070000d07405100e8501403c42428900e25002400b240c64110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 223428794 1250 223427544 223427551
    0x80a0b12070e0106031e0b0d0807030e010e100923030d0504180606050f0903010902060a0905091303020c0d031412040303050702070303090b0f281d01091203020a1a100902040e 77
    0x1a03a100c07414581180c07240f550b510040307900401c00d01e8a80903245000cc00040032200041e0018000c1004881d491a000b00030030750851481c0c61f03084045150051221200d1844240d1940c6007640c15005002d85e101402442c0d1a0010f594908d50743d04d06228140c00f050034145143c0c2e907104d25256043c4012500181101c440072481c1244580742c4002c040001c0c00740c40c0b00e810094000c40007041d40400f00741c0280303611046d500100c03150311290b03481d05104030749082c0f9544060700680c0b0481400c0705170300300842c4a10342320f8080e10300f0584049910a00380015840415003680b02105102080b0905605100307030b6801c250180b0241c1000c0c1e1031134030001e001c86008e00a200b040d140010301307022207107002022140322803070707003900440d0224012100e22200488401080042541d03560942106106075000b01100d0a05850300d28200b401c00c5c110304071070800c0400440c154400c0c85184d8001c1041c042d890403d05041180fa1103d5140c100d04c2018410f15581c080e0b510311380180814000942100d501952 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 223430044 1250 223428794 223428851
    0x2030601090903021e06010b16051c0908010b0d0b06030312070c0b0106020d080109050910060b0d14040308041502070f0f0c05060c1c09050a1401020d05070503070201080a0b12070e010603 82
    0x310fa4691000305c00c110246007000030224810584417030ba1044bc8024081618500d0340c90f036180d80d03681c0d02130140c00c0c1c1c0c0050119961000721403c586002444503103460303400540243c12a42011542552041840ca007038440b8000b017480080d48004104803803010306d01404451000e009200c11036a03000c3c1a501043c020b4450f22a19030000410320705040280e4031045100100a0095a50706c0f40c240800d5481900c801043c141000c400403802c83e01d90f03420a002c3d0354140e9580080c1ea99648881d684e441400e00102c825540810050000c42e00103201500c01c5405042c0444d030940043c50000b01e0500345504c1280141d20500588076851000306924001a10300c9444c102a03500c2c504044640070401d0300203030341c8508007420128a9074544050403454400a8003102c118119880042d00c4500a4500044c8140d104101210055109540c0d0720342001c0c2c1800040340395a4000000381c2110a448050200390f0b000f0042040705140c1904814014882c0e81000c0000c1c01b4030703407060441d0324244900740e107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 223431294 1250 223430044 223430047
    0x1b0f060406021f0b0a03150608190609030201021c0506130c121a030d08070e042a02070e0a090b0f0408270901060e0306090f030d150302030601090903021e06010b 71
    0x111105801d40081c0b84003480242805d00c00760302d03440e00489918000040316600ca250000200b040000000c20500b901490205035910042e40c0c1c1d0fa060150405250840031550284000204c0390091081104040c4400d1004203807450240140131006244400c0b20a102d400c2905103e6003e4001e00170041031320007240c0100302840e06a920040510840643d55018410b80b210030f00400d6001540f01d00039031441d990302000303258803810801602c610510807500c0640030142d80e000c009065400c0c919050042c0165242180d40d00810148500211031303000b862a124400c001c1000704102842e980310240b01081c2741d941c1003a858201c5503019509a0f03c0c6003807408142c80e0000018492610200c80004022460640c0c565030014038034031040c68a58020b10800022610111001c640000881d1344000110b080904004401e00500740d81c0c1081000c4c0c2040003004005601d06104240c040c04c1c02e1380b004a00f001140c81e000f440e140d890105a804082c09801c00200070703c0209004c0e04580c44620320302d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 223432544 1250 223431294 223431343
    0x50607020402070206040b19020a1101052107032403080f0306010903050a1a01060f08040b100308040803130e15010804020103290f010f0203030a050403111b0f06040602 74
    0x5000384100c10000c0c0d8490000b08000504030101f5008003c2c0a10000c000c0681c41e0280300140da40303aa00c0040280701c280d00b20034880d900e521540103840b41d41e07000c4c40117000728100d400040320300c40000c0d07a040300000d448040301c3e005440c40b54801c110301124090300480d07051a6403a68142409a04449000c1500000c0490290782c8030780c180304e02941c2c100c0d041e1000d440c0369141140340050104090101a82034000014031071780a014403031070521035038036134007002d0740c3d280d0300d811301008002c0c869028010322540c0840810140030150014040540041d5600c095841d448138404401740c5c000241654510104043c0214810601207159002e090803c410340300c620040e4094a1b8000440840351810700c40d42030100c2c05e4000f0242b401d50150b9031454143c00c1d46004659115001410b84096417042010030141c02c00d81d80410b07402030203485c0444000e041400158280f201d8040209070f51512115444000e1612001e00002d1140450f22503103002d240c58000303500c42035824002130203074080000f00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 223433794 1250 223432544 223432549
    0x3020a05060a060e0708060315060a0807180e030a1b05030d0f020a08010b1809040f0c080d0207140a0302010f0c0204020d0207210c170d0501060c120807080105060702 73
    0x48460003903008054900528100c8014070003407140e481030352850203100003c07070f101c980228082802104046c2c05444071200c10320001e188800e016082c240c0010f849640001c48403414005070018040403050210140d041d15134000c1500c1441c07801c00820b81081100c0b00195800049090310354450b05540032a01c8400e04010342140544040c1d09482070404100c4a01c02605030b008242188840e116000281d80700c03c07602c94680100c00d10b042c030500c84000c441125142c00c00d801a0b01c01d21805161541c201242d0703030350f4a0400342d0b03170050503d035101e008044080d94040c04081c004d802ca48100c64071a0300300800041c18200c40b8800030f4188803900c44517100a601c98031403800c11a4000d80150360300c007070301c07201c40c0003e50180c1c4003511030380c140b8003031076002d9881c25413400c031090020703030b600c0b600240306458204207000c050700b0f400041e002c20040c00c0c0059856000342402400e0f641caa2404102460030a5034002c40081d944004224416040020f85c581201240f81516001c0d1403a5454801c10f102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 223435044 1250 223433794 223433803
    0xb01081f032a060c0201110606090117030f16140303040203100f0f0e0c01031a0a0b09120114040b07020102031014040f020705010507030e0f0c0108040809120a02010201061a070602070302 82
    0x608101038048500040391044e04402074030021031007039035403c85420300807950580703e02098480f19803003191480100729450100741a412420b441006992402c180d8420490496120068480b128a107000c00102800165600c1144e200b440002452039850a540000d403500e08600b107204825559910240110019a012240311035000704100300600f44a86040d80d48c0a00600f180c0c0024103082181c80002d10305500401c540e94081c1848289604004580085401140341203030021003805140b034904009014510008100c07424080081c01c1c036041010210000808900540e0b00420038440500100360f950022240c0352100c3c1c00480810100041c0030b0044c1c09031050303c19002003820401d0142c1940041d0040d9900d40701000761030a003c514030380b1200c0308111600705401c80803810400354010445160305c14414900705140c2078610000842000f40d040314088240d010482a504650702441290081c124503941011014140d17441206240305500b030003030847d0b402103044001c0500800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 223436294 1250 223435044 223435103
    0xb030303012d1215050703020c1504051501030602070302061b0d110409090501020301051009050307061d0418060507050301051c0602040e09030a031103060109030809030c0a0602010b01081f03 84
    0x1003860318180b9407401d05500c00841d50300180c100d140b40c85d0229510601130700c2154032080c100030140100043c01100382d1581c0c0e40040c41510140110100004904002c000050103075205420040e00d908250400900d859401003c81d80c80f52003a80d100b00358480c842e0183c03100d42c0303040b041c0810b20a24062980c0d18902507680300b42003007810548a1001c121040d00514103036002603c110b110000800380885240601d845029056002400240826427103030040749070083c646520b0008076403004010804480d8803045206901c014002c90808100c02c600800743c10134818a4501c3c1903506180000c0d002e00422481c01515880503101c002c00c01406030156030041495000921181c504662402c0e120340c0005441000a0720b06501481440d09250a42e406000180e43d6185468216904d0b401194007003c030703140c1e041c0310300011803109a0301c811041025100c5a030010494042c0000007500d884400b811020401820001364981031103d90548422681c0060070b501c0d4150f80e0300d108008124045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 223437544 1250 223436294 223436309
    0x6060f0904090614090f120f030106120b0303040603050118140c1602090f010f090504081c1e02040f120b0402010c0813030b010f0e0709140102010b0604030b0103060b030303012d 78
    0xa508114402d0404076001a400b4858019102a4214a1919022441000c1080c4c80a0b4409d0005000d583e2140d584c0302c1d00e424018500207103a845e000002861504154065800a500d500050014440508200c092550028818894a004071281080200d8000c04074140c514000c0349a0307140e6030066406003022074015000801c6410701c0c0b41d00c411101000d008500e00e01f4590100090911004c4c4140e038443d40d0800401e83c28098800342c919800c80e03c4c000104a52526482030010107000e1070581c5025080b04400142e43d00e1500c903203a4813801d4a50300480202c06061030300030101344119501c80d40280e091a00014800941c540b00d2070b1400740021841d400c3c103101c100401000300c0a01070ba4103031410003081692880daa081030003591701d0101da41c100003601104003041240d804a40580f01401e050001040200c42c030400300703801e9041030b4030a4900c00298401003050100c10b11a042e0701c0203040d4090740c650740c10a0b0031000e804210b1070348410110682507043e54007031107402500000e4050b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 223438794 1250 223437544 223437581
    0xa0f02030601350906070806100c12121a042009040c140f03040b0f0402030a0308060102010e1b040e010e1b041b0f0306091a130b030d090303020606060f09040906 71
    0x604884d40e50b908007200c01074003042103403011580c0d0340380424042c0305020443c1d0b104088030300c042e45c4d00c1e0382f00d400b90301100c1e0500001155010450885000c3c0180340b09800b0f24043d04050300034100802c2d00d506149404a4607161854881e1800c203a00c1161490041074901040b504916001250701da0034965034004070610108091a4013007501c401540100e014074400c1c00300351982401044078039006d0314002e41c16440441510b0000740114442988038a0500000442d0300300c5400c01c600341280342035540481e080c880410180d6103007130b201c0c2e4201842c0e030b04002c208480300ca24190742c2c0d070714400a000401001401c0741501503911074001c1c1d6103103117a04907030f88004a54a1405040d5840d203010303580c0800d085c1800820f2414940c8650701c0182c0c9145400e404413184d403828062441030841043c44402e07150282c140302030700d04110001050000340d440d444154510304000b810000c1c09030a151048000300420304416540c4003c3d580c82d03540481c0d000500400900d007040c000c0c030328180c46007a9a180e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 223440044 1250 223438794 223438801
    0x70c060510090c02150601090b370f2c0108131e060f09080a05090307120f03020f120d0c050717130e040f0f14150a0f0203060135 57
    0x1380494041c80c85100c08200403e03e403034003130041d10000050701034000c202006106250004e20300c20010081484014070703101009159a44100e00010348408102c04201c0c4604181d075032a5118041403802401c901542001001c4800c9080c4c03520030098035141001011408144203d5002d20300c00307805603015100410b001c0e0601d0110761007252a4406441261502d0000c0440c0c00c5540503241c0c8031a032241c03400d8980160081b0a0341c4d01d801080c035450701441b89210100c0c030716003e0441210030502a113400c04503007141e0304c0c1c001d1404001c1111190303150010b0801071040b03840c04040d01ca124070080c9011420707030349060341100d15016140015120502c1d42403910860302006004241d9442a0350440800688071f8401400c201d00035500203042c0d02c0314050810109041c840d03104e08051090132501e05c09010002418900112110180d241e101810140300f0802014450fa108a0508003815421480e010f4000380c490441403100200c805e0503402d40c8249045100c154071052020700e001d0b403c1504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 223441294 1250 223440044 223440047
    0x3160516030206010603110705120f0f130312020708060103120c08130302040f0c0203120c040e010b0c061b1204260702040605030c1e011704050c01021203070c060510090c 75
    0xf20a200d1440480c0c500900308002580b401c3c120780c90240c00000501c01901281240340e01a40b225016200340c503014007007803004081c050010041840120a004202030845c10700742c4c8481c40350a8450b080d54000341c0104020a00850364904403034001301d01500d21070315100c0c140c81c10b0a8254000f070011500048040c1503c8501044500b500d00a0b20208905082078440204440c519000d103000f681c01400b98602c41d40028007003d40c404400c0d0405400c059a45504c01080c80342a0040c60243ca004100116590000c0000f941e00410b0f07521003404004a050641085100d4800200ca100e201310001405000f841050201c59000440b002c4040c102e2003a4503030950740004030101d11131424040c2c00121441e00040d42490310764004c6c00101c46096203072003040b42241d020010790620006080000100c41c0920074039209a00420290a4140c1c0070344c0020700704090001c000165039418000d01014503400107007a804540c2c0b203c00020a5104d543d04403403003010a6101c0c145840c1045581814035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 223442544 1250 223441294 223441303
    0x30f050711100e0c0616050a03260103110d060605030f100f0e03090d060605090103030804050c03010501061220071b06080403020a02040b0d1506150212031605160302 73
    0x45501c5802e42c0d124014901c658001d990b8070051401080d4000c403221403035407174540000c15060000d481e0054103004140e50702c0b0700340407003804d00782c0110301c442820803051400c079800c000f080140c0803030700182581140c1e1100c03040d800e8204154054404001c4031400c0081d951700c03180241000a04442d0400891800d9903518601e0758040114103040c407003800174120160040812006500c4091810401100140074040c8240e0300292a000d4803180c00092546490000f41d000c0c42c003d43e280c00507840d050508928001c0c959620724000d0b03140c00010483e881e480035141c0800c038015080810803050b0040170f01c00a00307006068030f1460340d0001c3c04400b006541d46c0c2c3c0d01841e08140901e800c8482c1d44490545101801300d4014001d83c0181007000f00520300340c0d101c440074200051407600200003d41321032a046107040c0590107450366541d8240564080c1280d4002802014802805100603064403001c4034040903049100e44c500400c04500c80502400039074002c40c0344c120019030315a200d814000d556 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 223443794 1250 223442544 223442567
    0x5060a0b040e07050906220f06060e0d030801091d060c070204052208030c1603021506040209010e060d1b03020a0e100c030f090504020d060f14091501030f0507 70
    0x103510382190b6401d80d9501007403c804403032000303000c6070f4243d13607040c14044a41c00f04101c082d04050340d0840407403042d003280b00345901514808000101d090038202e0281c85010695007280c4201c0c1400c1e07048000a5018020505480c0c0b2014003040d40000e0b0100f10008107001c481520300c40c01540100044104290f01402c070305802124103100070b49400d040c0364405a8040400010b1000084400c00400c007018000c6801130090300c4201d15159011005480b1505450b60440068111a070365003600d40300000466002201140c0841c0740c4960180040e251000f283c90a9008410210b11a082c2407000da20845201e000001b44c0e1068489807a80100294428100b56000c074203035201c5608941130070742703180060403010345480e0070040300c0d9102a5031404030f8030341c40300800c040b494001c00c468130380d4000342201f21000e060103d421030030084100307184002a0003000e0120500040700c085a0f4a1441e995040100001c61002181486004034040c28002492000039824842842141648203044450b03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 223445044 1250 223443794 223443799
    0x316110f10140c0301050d030e060426010f0b060a0c02030304030c030807120201060e040f05010902060a021608060705090108091005010f14220c0207090609021e0406020703030c060905060a0b 84
    0x1a503601c50f000c108260000303000740d9070000801d20150300001d002d856600d280601c020400c42c00c2c07683d6020f031102c0741c28862940076149003142606031400c0345c0c04d0003114070140f00c0c540148404140c00e80420000c0c020817a0600c1045807550251044d520148125406580c104441542454680c100380c5031591101d10129580c41400c0000340031148103110301b000742d030360b00a00c10320701da00c454607a600c40000b00c200568455603218451001603981000800440e903064003d0200c001c003401d10b06907141003e0b0711040c0c0d60303040b110811400d00d502c001201c0300042c00b400e100c3c00c070341c0710002214079040307015290340c0b64546030500200c1c220101c0e084482c200c840804401c032038102c8034824040024a2000701c26010402801c25424080c91504580b404103120720454112903075415072613041c0c6145078000c02d104c1e580060070b1a8940d1803100711100800b100c5404610300b600d4400c00a6440c0c14910001c0c0c208080100e241040050a401160219801030220748a0b41407542603c0300601c0100303070891 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 223446294 1250 223445044 223445081
    0x6040f080109120503041205091201050906100f030c05060a0207080d0507170901080103150f1a030f122505030703022503110d0501020715060303080a020316110f10 72
    0x700744c407650840b4826503001c3e100131070840c80f550040e196504911001580410b0980141c489038030700f44501d6100320380d03890041c420360614091341d159110f02034100d40c005032084c0700b091011918807111041103034000e813500c0d5520740c84403000701e040c01200d401c082c036140110b14000c2e00d907aa100014059040c00340b000c0e064240240c006003e1244107540380a404296002c0c01000420625001d46c10358440c4410045454060002008200d940e40c0a55404400301c5844507003140c20100450349426207c0360041400c1c080384c945554040c010640a1045031000e00101501780000410768403105500030101c9403150224540a504c1d400c40b00000e521140040012480104840d9035030000c1fa900400d01804540e802c10612400303942d550340541d280e40d0200700c0080090401d14410700900103046001940c1421464010490311010308500601c80c010f0043c08445421071403201d01c002514240108400400381c0028140380215045034090300611940041000f610b41245254803009107464 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 223447544 1250 223446294 223446323
    0x6140307090e09070f14091303120c050c010e061e09011515030506030601120204390e010203071a06030a02060408070906080102070506070f0302160305181806010e06040f080109 78
    0x10708010b0108900d05900280860204242034a000106032300c0f50b0080c038182002202e060000c0040c0d4038080b0709900061400610440d4290080c42024030902e8800c0c050000c2d424481e03d6021140c40c07a02165146441503004034040d040250b1102040c50250030003440000c0c0d5407203803a03158880104481c0301003070601e000200281740116625058520344460036200e103c05400307000c010f1840c401004000d40402611310b81d90b03c440c61401442c400f0150385142a01428a030082c511070040c0c1510f4155803091080705c0016020401c0d070b00e950350b4036507004902981ca000000e450700200080103500000009404181c1603000b240750000d55513000d4007404820f170760310103082c00c0707108101001e07249070042808510f40341c0c41248039940420091030054208081c44502110009005400700c0100e1800204101e004d803048165000300700c000c0303410301c40040400301d81070743c50400100a42d040009003541c000d113507a0780e20184c402801d014401d1070040c0e9250909140242001c000c107446058004c0b411 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 223448794 1250 223447544 223447559
    0xb07020a0302030307050703120e070303020709050c04170c10120e03040302130b0d0503042319030b1b030a0603031e022a031009060b040606140307090e09070f 70
    0x200040681c550b0042d8555664a10101c0c3d154024440450400498032a242c41a85403405640803840511003d17029a40c40d6140c0646042c60340e80c0040d0320b150504041055080310002038404a5001c01c6406001c6400c41c407680d800c05c1003000309260300409210712003a41681c0000380500400580204103e0303114030214040e524010743c0b000941c0030700e002808141d4071020307410280101402074075030301e50081c59659150440d040350704952003a11569082d040d00c1002c1c030860801e190400d035924250010344c2403019540c00c4090201404003811400801c09110304c40340380e04140c0c038184070181e03107030304000e510000a0400d600c400d174000307500c075409008400e82e1108035030f00c0c0304642e400030400a500000300400c04422200c495103400f103010f8104e03d1a85017881001140302101d000000c1240030361524070211003425403118061440c0070414021140c001c0a0b4072a03042e48030074201d4482d40c54100440f40318420790000420740d40003105008026000190220540c1c03201961070200c29110f81c070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 223450044 1250 223448794 223448803
    0x71509140106050306060d03030b0d03050d05010f140915040f200901020304030308190203042a0501020304031104090804060f0e01020a1205070309170a050f010e030304021c0b01120b0702 82
    0x162540b51700034101095262074024419060f40744282400724045008030300241484005590580c0400d1001500d0009038080d03218490141005a80e60240c0504104050f040c0043d0410040d002e1800680416075505195604000008000740140311140b5204c2032980078100c1500d205a15110503a1003942c060460f4090f13841c0c2c0c41044e0300940c203051464404441000c40900240707144a0110104c90940d41d4900003148918056680700356400301a100040c0002c90f1140040001c103542035060042da07030301204071801c40c1d41060030010389840040019005045020340200b01c16400100003400381d030803941d40e00c41c4143c81c9d241c80e60f0000d03c00340103989510700e07080010302095070300d0f6107c01c0c80ca020b0000307403401c10b0180c41d00c01c50084d00d0b0307901c0c40c072451001c06170741d03040750b2003080340008001080000300500f500d05c00c02409201c80b0410850740d0380c003001d0b00080c410448002c84241501c0040c4401045e00c2d0480110011540d4030b2007801d0150234124403d41d071100c0c44000069500d8000079 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 223451294 1250 223450044 223450049
    0x21804020d021e042a090e071d1e010206151003020a020f07080705121501050d1506090c110a020a0b03130c080c2809020f071509140106 60
    0xa00c5044080165400c00030143c0c0c1c1d10041000240c2440c207002003603140c500c1410034580c014240202280d0460140210b41c68001c80b0079410403a560000f4007403060a04070f02074100c8042d0500c0090070f200182d0740d100b4108043c200503048080f00303114a91016a00b0b030b00091584082e000c0c2c4445484800840904100030069160045031020080803800d00c680e0080c00c1c1c44580b0310654000b40600c014041c20402c25500c401915800017409200070b180500b40c41d006115107000800203080140c0881c0c1074614140300e018854030700d4a07140340c103024140c0a0320607048084401040b145441d4001403008010202c004800200900503103a40a000080c54180d10f61700103004030f00386840c104800000ba4030003084500003651060703103a000540d03c036100401501000d8040c104076201030701480b0705c0ca000c4580c842149102e00c015440300040b02c101c4642a80c0b449500587c1d188c0480300410384e14880c070f24009202150140702e1240b1946564401340300341d88600c0d03c2c500410300030070540307080e1030160 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 223452544 1250 223451294 223451299
    0x405030726071212020304060504120c031211040503070602150a02040305060604090201121107050f0303060a031502190507030f080601022a030604030f09120305161502130302180402 80
    0x200700e03000102d404518800100f00080c0350079215191012026000d0b0781056600b03e07889510b860600c0b007004101c007107040501381c892074803400c24407503034500409510203d1800c000c690750b582034a50304074600760115400b0b000c001d02140d10a0342d49200c02503480603d001030310800c56148000c80d10a05c02d40c001c417422a5003140081c90f80351105001c00006000400049052004186051080304407074001c4400440f240165182c9400365400c04c2401c0c010100140440e80c0c00c1001000f140350f94204a1005582d0841c1601801c1c0f000700c000034000b449145030011205080d8218a2452540007009003006440b0350354521035031525140540d0040403c2d11040d0141e00444401400200a0040c04a940602040780100c0380544000300c1e06040c825142940000d0001c40c460010b25003000d005801803030342e000444c4030300f071080d140204240650a10070a030201191381c00400e0148500750104044602101195601d500c981c1003a941006c070301c412070140607003118181c04402803010440c03007030f60003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 223453794 1250 223452544 223452547
    0x3020108011e08010f0b1305130b0a0212043f0e0d08070602120907030f0f030c12052d030a02220e1503010e0c060a090506030405030726 60
    0xb0601c0e580c604100d0800a0368a0304418032001603c81c3c02400307030654002040f080068501c004105000354000400e002d442c0c404d0038001401a90b903c2481d081c10398030740124040700780da21080000406407003041005040100340d01d0501052011405020000d11908000560a000d0b00310f02c03140c0075000024201001140701d085032040c28092030500200300401021004400c8055455081c0394020340e10648080b613002c941041c00d88101844039070490280c80c01000541c1c51a51164251a080071000f4072815001011004050160b040c06440e04d03840440c401d283e400004000b40541c010030424820b5800d0780c0c41c81a1040b0907580400002039403d60918516a1441444000796111800c512040c4480c551070100921001c103c00d8040c01e92040d05220034103000c0da00c4032403c115104ca5520076450304000410615000829080c50a8140c0f02d854440c51550001e854486882d802141c02c05000010401044400300042902510402c00c0564030084410a100f00440702850403aa9500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 223455044 1250 223453794 223453799
    0x601020a0605100902040f090b03030c300a0201140c040533040b0d1415091008010e01140709030503030106080916031103010c03150509040f020d080c01150302010801 73
    0x4641d000b6661102c0d05400101c1541c0e6034002c090202e03800b41d44060740380026008184011041d80c0a608040c2004400a40c01d00c0047c8136101e8903685031052612502c10382002a0800c980c0d03851082c2c03598a10820300c075440308403000000c0e0191141204407840c1d0460380c80012503a0b441c40c01550151840078041003103a01c541c0b0107224641300d2000c102840008003002e20101180d0080c02800a0a95540c60a031a180c02d4101041605e01280740302e00c4006400c010012103ca603840c81c8801040d048a1240581c1c4078000844d0105225030801c0520354240b607404c41001c01e054202c01241903062045220641d51031500312003140007400024002c4d0420801040018810071100e50400c0a141c1650100c1000b8140049819131a920841e040298407820302c0051400313100340510401e2504092060048040c118800c0705013034002e46100c7d408450200381800306200c01c0b2803000b84d024042542c0c209050400d41681e41106461020710b60070182c4010300c2a4031440e00700e0449a040e1101c43c0c4590 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 223456294 1250 223455044 223455053
    0x30c01110d05160203071205060604110a0c0f0c0b041a030105010e01050d1407090305100b035b06050303030c07142a03060108150601050403140d03140601020a 70
    0x900000b0203a0f9800607103100741000d40e805200c6400202503031500030034003003281d00e415420610009d00842c0b2982c40c0240e620450792800d0110b480c41800da180501c009403862901c1009805c0c008005000c0a10403440030a80980c1d200c02001a14070308020b044505c4070541c0300502c144003d004107400148000301e24400ca500945c0a007001002010012495800540d5800640310f402c60350305c8000344412104106124007130280d0b000b19401000b040c44044044000b007079440d15a445e0b81000004000314a0120848070880d210481e980501d070100d610790b50a0035942d1115030f200500f0703819010044619044070b05442030030700b150b070058080c2d4115900c000081c42960014201560a1f0b01210f41d060039000b0b09010310b20341183c030580100050b950382220b80da01400a80b240078003d500c10310062140d554000340c14034041c0d12100002c100c1c0d035a01d800403038460059074801002910b403607400e030707840a50116440c14040c00d51360b010414408500c071900c00e912400d4a800d4056082003100c0740221b0b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 223457544 1250 223456294 223456297
    0x120b04030f21051f0b09010323040302010b010e01021902010f030e071e120c05041505060c01050412030608190309051201020903010f06030206092b05010b0a0e0709140a05040906050402030c01110d05 87
    0x49c2003140381c141c140700c3e0841c03101401b403412101140141d5403072035010019a084100c0e0402c0035800e10040030320b0840900c0d205810704034648068184100c881c80100443d120780c102c1d800010702078054a100c20ba540380c074002404444c02d07210241510440022460710902c210021496402000c601e510518100500c001010100d0800300c030700b182003030f01181c1ca8035040300900000c000316000250360702d0a410140110000488810105810320004200301c0ca400030381381c031040b0700342002c4904046192500b601c0d0124181d10003604040741c814075a508100650107802c1001d0203600034840780e940e0703505500c216181800000c3d03001d4030600c00004907007094000305910400c02d82007940c1300b05154000b4418601e00700412145a9100c295054080c245040c000008204140079101642803680000d01001c05602071106006c4900032002c405645481042d801044050700c00c102c0040a400c005014240440301a402032040001a004170b5100d013054081c0c00c0c944001424000e9103150040f98203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 223458794 1250 223457544 223457561
    0x100b03090a0c1805060907020d11011803080f0a0203060d0f02120105100302031903020a0308220c09051003020609011107031403090109120b04030f21051f0b090103 72
    0x55208942618002841c080e0b2040003500b0400c1000032100301ca0305501090f14002021503000d1003103403003803100558001801c0850014241032140c030070000f401c40e55004100552401400b900d9132810041855041505603004101ea2860040d01d80e482c03a43d01020780c8000d840341c03500300c80d07014008004200d4031003560001d107100a180f510103030380c2d4100c0d00b0f0030742c1c0302074503402c41c0c180303c9a00400031460304120000c01c0e00d80e0076091050350322054501070744610100303001400340076032540000c2e85864aa1034400520301d0307001c05011942d101e0304002900380c0150044c4c1162510b0140420076410a604100040301d500420a6140060402c0110751040c15041c48140078420344001000050091418180c040c1e1f5200c0295255041c0800051580300c10303510101c086000d101025001c03c2e03441c1603072940580c040c01c002001d04010307002200c0c0c50180c501090350001418510058524003601b202d07000d000343b0040700c402114140501c02c90100d0510555024030b5007040318100550080d08030010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 223460044 1250 223458794 223458811
    0x30a020d08070501060906090b090906010504020f04080604050c0111010b03060c0d0f0516030c090326070b070f021e100b01020309061201060815030d03090611070606140603100b03 79
    0x702515030f40c4403825a540ea0304030010280d1107070818080d403119441070552601040f181c003640c0b814007400b01500c1d140c060107498040ca40008a01140c010198205c800420f00038040741c2c1c1600e00340c01e0480d118424040c059000603658a19074003a40c0050141f840a650000d01814840e101c90540b10499030052080041d4207489200030003140780700d071040781c2c49141c20740c4004108041d002001000c640100050720184081e0300c1c030030310204074041c00e441541030f48180411203460900044041c0c1d13001c1c07500000c0001001000b0402e6003940000102084820f0703030200c8005d44904841c0344007820450400d00071a9100c484031180c2c002c0f03d40c10140310039006006803840c1580340b4001c102582d010901003041249003c00410046078003000c205da02051540800c0078a0180100003500e030301c1080400702c100364032440c40c08184940c80c0e02004440c9403c4042503500c44072480c1210240070700e840788449420743e00c0c02428803420b000382101d107e441005c59010466041c803200394541e8101514584 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 223461294 1250 223460044 223460047
    0x702031602031c02030706150b03370f060b090f091e010b030106120504080d02070303110c0109050705120c0913050106030602030901050a0902010f050a0e033405030a020d08 76
    0x181e00e0700448843c4031012800c1e60146560700b181e8145a01a2402c44042e1101c0302205c1034100284510041566040044c038103001c03460b0070260b01c003214400003030000303032041c90000c0c28808001d480540c850780141e000244c0c14044181e8849450020340215000e0541014010000d90b032140f0305900c0d13203540207200040703401200303039a001c4a00b1406401d0300a0001c200000005001c0150807034081204521070103400e00051800c0c0d500c9120318080c0b8031200d00850b4000c58040b04040c0660420700713102c2c00c10850262540c4002c4003560181c21480000c3d00d40380501c40d40403c1908181e0041051b1800c140c0042100c000e66100740400048010110714000040441020000c0e500b0b001c0d0000450150030007503281d007846581d403821541c1c0580704445242c0760400080050b40c20907607003500c401590404980703410301c0724001e954460b801c2c078615a040c085c1110504081e1071038400e910713090110540d1915150810703541015401002c2c082c050f850b03848924002c0c010f2400c000040c544910075202c8e079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 223462544 1250 223461294 223461313
    0x7020402160501022809060c031e0320070f0f05190609030801050f150903011d0f070609120f03030e0102161e08030126070902130905070203160203 65
    0x401ca840e15049044070a0f035000540100c0d4440d5402c01c00500303c41c040000710800d4107a8a000e841d4460500c00c001c2448440c06465040c103008008542e03c040701c10310031000000070480c000340103102044904030840da07011f00c0164000500d03410750796141d41c400101c40d02420692100358040716494422507140c82040021241ea0780d0800c1601006846140041800c68071450003804c0107005030807950040400e851500051303901d08030030b044600c0190040e03681c4d648086000c00c3c090b1080440781a02c15181a90b801c003800ca00048644801030f100040d114081d80b111021039808056100741000402021131180104203030000c4800b071984203050000700070b00c00410760b03404ea800c98807207003108201d03030241982030011026107034494030bc01c01c592110902050b569840c082c0410300861600f83e0001142c115141907001400c0713941c08214003198015176550142c4c030003035071010301408070101000000140102c070501845002c0c1070180c0144d4240000c2d03c4150700342c07600101003607a0510488000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 223463794 1250 223462544 223462567
    0x140f032410030e070914060f011b0b010f0905060112020a0207030605010305030c010531050c06130f06020c0a09090c0f090e011401060801031e0b0c0918010b0a0507020402 75
    0x46481030a256100424070718004043c150505203190b110b088014204074402940445442c0481e5214000316a1030b0907003440ba400488412084002018209068014580a102d81c1120f41030480d0842440d02808070380740e1a1b6581911003c0c0c07071040c082080911100c0030320712681c000c1c1c030310801c603032044030381e8580d990b110344050341c0082e8404d540342c2e000002d6808008100703004041c1c2c0300c0d02d10488040e1036203100d01d11000c2c83c2d840d10309607044100800d01d240b08110080c8128601003000070310ba2750300c5e00384d002e07a4485492030701e1045440c07106030100e000800e540040fa100249010042400a41070b16084401d8064511110103c07a14030801c1c4000c03509503448651600a0f10b446100044d04a400d40e00b220300310b49000d08148a1049208010040f6030350280100c2c0c152540b041c4109501403051404d019125603a0a008103040455420007805c00149000b926080004481d45850420307500320348044080280603440c100501000b100c0e058a015800400c81c40b40302520040ca4419080b40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 223465044 1250 223463794 223463809
    0x5010209030a150b010201052202011e0305010e090606030303040303022208010c030605180402150c01091b06110d03020c1006090911090106120b01050405091006140f0324 75
    0x42c11608154241034000141c2014495039000d101c4c280000c0119081c0340044004003602451a030001c0c0c2a40345005013164454030710209150b40c80c141c20b00310480c0f001009005044e090040600501540c00041c140c0940001d40034000c40000c0c0c0614915140c0d52001c03406503000c0140e03813a512142c01516007120701c100c0001780080c10a103000081c03041d4080b07001019617070150301807841540e8503140e81c00031240100142d60001d030f0440b9540601c244110402642e8080e281c901961540b83c440800309000e0940c40d6000012486405600020b4680005a07011580a10003d0156100a48440310f150299001700f125100e40c0080b02c407050340b0040c80070182c40b05e0740c1140c035416465880d0f41c0700300003c05202030b003181e000b103d807503034298180a00200f0075440c0042e240172503600c4014034036207a40244115805000301030140c03442460031b0480c4498804a40c8100400150348000b844566041213042d04d060100307101c501031564403044000c0a07240c2d030010654480c0504680b40c820240e0301c0a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 223466294 1250 223465044 223465063
    0xa0c2d12020f010b030709022d070308061210050402300105070e130504020109050a06030507020f03090d02011101150f0603060e0f180c090a090b060f0901060503040501020903 77
    0x11100c81a410040002820041d60644103451681042c10140050303074003054180c00c1d0f40d0111001610342e00b2060301e5007680c210742044001c440607220f4074140710850503801400c02c6400303511741000d503803075050a000103e041ca141482154000c1c2e1694900718449411903900940010030307030440401a2030103942da0f204c43e0003030900394040015407120000802e0081d0b03580584a8200707007454100c25008181d02c1d101199004800699070b000103401c41e070040b05950701404000e001e28080741d0301da2401400074030040c1c54000151041807081e1000d60b600100f1104c0c0c032403001e010307900300502e56401501c0542d409048140c1d55521046460f0a000401c040c4000409203002100c1c425440c1c00300260803100580c10000c059400700c8104800581d030134800b190052000440c4d66100c0283c1044c050a1807010b030100c2d54440208410f02c50032100607000202d01c940251300440c1a501d500d801c01c0300a858103070340140c001c0082401084100d0180740075645c0a40070341c1c00946002d10040000c0d04160b06070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 223467544 1250 223466294 223466303
    0x50c0409140103050a080a11011a19210303230105011106040b0106050a020109120e0f0402090306040609031205040804091118060a09050a09051501050a0c2d 69
    0x20404011809481c0100c1485072400500300c40a54110b0300c501d6100c2e403210901030079000c00055141401072140114802940c10940200000c0384140d40243c00d08054001540c07066102d102c0d0b45131249030a1010360202c0d5011481844c28100c0e824688501b080000819424503a035088000309003c28508d060a100b0740740c0c52018960360402001421031100822400a0790340107400300000103801c425542d0650b103441c1010394490824880403405072400c948010300c01c2081d2005058041e41082c511a014082126140321008900c405d02049000d05241b084c0d00d071380004089004107800350f1003c1201e901910b460542c8000002c12041543d07002e40f0212031030200002c04000790795603407060005e191354a51000c0d25003084140c0911791541c5005c1d50f50311501001039006c0c0150f010354101801032074040c02ca141c3d8a40e48000240082008949c1c62091003d002c8600003958402c00885a10681d40d032182100034409132500c0004000c194056484421005030743c0002d4070500c01030441c0213120b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 223468794 1250 223467544 223467547
    0x1110c09100303091d040f081603020106090c020f06010b0f0c0d02030301051008070f120219020f0c0f010c030806040906090609050c030c01020c130209060309030d140f0a02090301060306050c 84
    0x11840d0007080410302e580005c043e044030806048540c0c00003501a908a908040c0b0041520320724107002c151482508903401c07160200700001010035804bd007100044500700d14081150307050419082c0d1304c8841031030f4071804c1c58004400521030006064090017118001018140c20044091203051400070010b90791409640044010072952500105028103001c0ca860840b0050030b081502400119a03480200213114907100d92100c0c4804990507035045801c8a0340000c050409020040e46402012a1402c070074092007410368268200550195100b40044c0c1d01d0000e070b107036180c03070031122104040c0c1580c0d482902c1d04c1030040440d5480c021105564010000091009198508149800c5517588a1030080c5c00c9406100104c1c1c0c3c011940e0b000d07108003654140d41c010410500c81c00281301d4104201d9200c81c0100500104403800401b4089040404408000d00c00c00003d080c1242c00d0102c407101e10340c030b24102c00140001c0d400d0300502a600000303800440c1e4603440f40e8490b03095880803140500710110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 223470044 1250 223468794 223468799
    0x1e0601030b010f0b03060103050601030f18031403010e180a02030a061a03070e011206020909040c0303080705030f0112141002030a06090e0309100219030f03052401110c0910 76
    0x10710801490052414800c8032800f5032a00c807808405000c01000c0034181580c400014040b40d000e038010315031410b803141c010069080c0f6009070400d0b0000000041d0002528000141038080c288400c4905032820b90249040b140d490020a15410780d0900d81d8441901400c2c0b000001a01d0400c034542050b4031607180030551031800c00403e040d4828124841d803190303101e4502000300c2c01c0c20040541c1540d40c104003038104030800d418060064400d12003144d400c96005810401445160b00051040d40c1c0301340d07220045030b100c0340e0085070305020a407070030304018a1040041010041c2195080e061a105a091062140740d22010a0529480000e86035500c0d0b000070800621713030a14441d0201404280b501040007801042c10595079010368280c2900030b1a94108850080e402041000013004006a05244100b4240360050030040c03040c0803440441e04101c0440d550446043e00451600305400310041060442d000442d282500c80f03807054007034001c01501c0c41041d00c3e03054103039104040038000300d40c0451 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 223471294 1250 223470044 223470053
    0x4030204091a0f25170a0e070e0603060708010e010605070218070c02010f110a0609020a030c080a060b0f011b08090402040815010608070516060b120d03110901020703141e060103 78
    0x144404d00b540c1d8040907440706031002ca802c42c444030860022180c10702001c0d0307540120349004149140800e601e070b114071000015180417445019100d01300680603620700d0744070ba2106480211017070040300c01d403509103001407000d54421000b8003002c90008001341200740c0c01e01d00b0100000b00c01d5801100107903440915030199600074a14100b107014910300000d005c080c8100b101e890b900c41c104001c01d110f840703100801c25552442006005150010080b0100c01d80d280c004a03a02c0740480d1040780c02c1801c0c80f81c448400e1a0040241280c1071040e11a00d149603440105542d13010981181102c1c1410240516507160701d0b13610151000e00111001006c442c8601610240ca4010580c0300900304400b0408006a15034418160784881c2e218000140890701a490100061b2204580f120b403c4606840000060500094480515080c9071003c018520204e03007840074600c070311851903016070f200e090202300160000c140c031141c21100d60195a0380d481c1d818450020290103600306004d83d48810018030034407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 223472544 1250 223471294 223471321
    0x30f0210021204022d0105030402030f01060b040f080102040f090203070c1b08060a15050d0302101104030b16021b1906020105090f030412030305091e03250804030204091a0f 76
    0x20401c1050151280000b0b80b40202580001c902c03c5e0704003d000300208085440c1000902ca0303502080700203005441d111800070b04240c2041c41140001513040e1000200c0c690117200711001d40b51070700c5040d8010b07800c0c6104040603600240132170b800c003e80040078101280e2268a16040200d030024130f04c2915141040c114503281d8082c2c0780d50005071030320024011202c003404142080310016949401504410b080a07410a0b4200901032075180c10201c1640c031001c8850000e200b6240b085450071100e4a824080d000c94407002008400541d12200f41818000001d041021002100405c0d8243c48501805c0022030882c5940c440c6026070344500500c407007010180b241403554500f0b80c000b5030500e440c10094401d000d11840c0c01405040c2d603000401d00126040c42035607100d20403ca8404071000e480705404d80e8960060544e0141a14446590004050b40c0a00da02003a9001564282007038150f408000081038140b50481e0881582900794506070103880702c551181101e9032402e586450000c8034402403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 223473794 1250 223472544 223472569
    0x801050711010203010e130c09020a21020a021f0605030109060c030e120702090c0c0607090614040b0301030b070c141506010512070807260603070501030504020d030f021002120402 79
    0x340c0d005100606c4196100030b4040e178005c2e5100c0e942c002800c15802c00c2010044140c120211140c0005005643c194026242c2c500c440f01c80c00040c2101d0a40102c2c1d001280154141500140c002205503105810303094000303c4407141051000a007560f440002070f00711a000241141c0d51601e5195404056401d40700b050f40400c1c406000d441003221400c82d10b202d0744a03178800284240070000c045011003071000c2c00e41b0400d0b19040111030240c2007e80c80030380108141e110726000680c4080f03030b0300c04034048802502e08070b03508404010b0540c2d0841da01e5440403000241008104405034220b040032503042e03402042c0d43d82c001c9010741080b002c08040001c0c010f10042016041c0403040008404415000d201d40340e00960740e24284079540c80d0107408071807141c0210001b20088101c040f90b42c003008049c00c6014011241102141c0c8816550750054060380c10894001c0c2d803007a1400c94000101e030007426002e01d10b00361341c4181c90b400b40440c3c0b41e100c1240c000b40d4803448032034000c05c05c100c02c501302403d0b400314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 223475044 1250 223473794 223473827
    0x60f0105090105030607030c17010b070210050408030a05160206071b0902030c070201110f1e0601080604080403080304080d02160213110d0c0c02090c0306090c091c140708010507 78
    0xc9605143c0480c4d51076401070002e004060780c8190000b03230544900794044080c11115160191075a452030240340d01e07009000140e00c00d060f290246c14082d8051012101219440000fa5041c81c8090109503030582180317010f5000c00101403c1e501c0141d6400005002e0300344074481e5000846010b40d030700300c0c920410382c00000344d180c4100b0a10007851001c20a4668450782460a900010100394140e4105124030f50384031418401c4074003e41c42108150b8500819160420031208160ba0b54801309540700c0e4207440140040200700030610210391490021039200780510301c003616041c00802604202c0c1c0c44001303800301c0d856004410170218a040b6040c10092642c1c0001442104078101d048410ba110303071201002910b07510800c40c00d9041c001c6210800403500141540c01f58944001030502d550720460351103105510301c0c2c3c0014400341609058a4485001404c0e1600b40c5c142046210182103c0c0c000903100c0e4482c0c60f941c50750707100c020010300d00030704542c1c40049540d0a2004018001c4114841c8011 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 223476294 1250 223475044 223475059
    0x9080708060103050c2101140702010e0a260c0303010303050406090e0708150409081303033203100302030f0f01051311061e0c0705091602061f080102040305060f0105 73
    0xb012590001d0035175580d82040701c03410101ea02c042d03008200003000d5007120f2020750030250035500c0d04880946140c030601d200e030000d20a4800c1403840a0b140c4198800c020b220031468001ca07201d00c1d40c008801141d21b44030f114401c0c50841810b0030246141c01c00d0b0f0007240080d0002030f05025040c2c0c000f5156009188103164083d242c10525006003800600030420740d0303c4141c0014801703182e03030755803c540a007079080507005580d00020503008800320710074001640401c1c100c6400d41e042c54001024000c410700014403030071400c0150101c80e64a0b0f0f00242c4040e8040c100c625011000d80d400b800140011a24040144a00904400381c5801d48400400c980c01c5508044001e41c0822180c2401500089089860305c1c2d0301c00d464010b072041c44165220301d00c000c020120b210f06074900001450300a4600c200d034101c2140d5a42ca4481c0c008801040e206c00068015501003640c612000001001c8000e100784010011070701d4013416422600264010350b410b074001d200348950020301441c480d025110076103018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 223477544 1250 223476294 223476299
    0xc01020709110306010e0a21140d0c11040b06030a09060b060a02030d050a09330515040903090b030703020a030b0f0d03080403090f030f0b0604050403091215050106090807080601 78
    0x9240c070f03010081a041c14444100b482e40d42554039501088050460720b080a2103082d511005503000d111801e4044900a01c00d014812400d0340008840380740d104a642c6203083c10b00e2540d21100c06020003c05640c10a444004940c503030b0303840c040990b1190340300840c001000348450816000380c881d0340001070300030401040741740e4403941d004c021151060400140881d89441e08000b0030000c050840001c0d01396000340c00d00d14041940000791300b224026134a40ca140d000c90301460074023221070a41f00e030101a103189080010ba400c1c1078116048440c0241450f004443d40c5200c000c050b81d0080321201c0000380d0025141215030381503c100500042e080d04d10f50618440e650103d00354069010001e0144201040060101071141180b28040c000882c69900d015903a07142c0b0011000b40ca25040b80c401c40310400044031401c1503c00d41d807049400d980c0303c00310545480b03000230380d5610040b01074401c400c80251118100d4000d010b0140200029030312140803a2030101c3ca00d08251640d0056201a081071004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 223478794 1250 223477544 223477571
    0x6060d0c0b0a05040801020408010e1b06090d29090d05090d1704030f08090901060c0f080306010309051509060603070b0306060d090203010f09060b0a05130207030512090c01020709 79
    0x840c0903246140000c5503581d64801050790240078984c03018004e9800080c0114248406400a48042c1d00400842e001c031242c1603900d80c41280c020841c00e230005020300816800c1e107440d421080f621805010382c2d20465070300d007191510400440c2c1000c0c0c1c801d0500401d0100241d0100407051600c202458038504180d1400001010585401405002074400d4000b990b0f4500741700044400940c0c3c0401050340d259518a41080302e901300b514400c0c495001d2000018240303000d03840d0031045940c0142500341c0d1a4013a941c1c89030030b410141a030303810556179101d2400060010000768603201da10107030111440c0740c0070303504502d41f1200410f801d000b9044464100301c42403600f03080d40d41100049400301c0d180c0c0b0078106a90010004040d01941c558201003116440c01e01e960700c645111400f50400b4441c030303001030061101703294480c810150080d503c9009184000020b6001d000c03014443c1c5003041c03821110100710f000c071540544d1445aa900038940704030761584c0401c2100020718540d2014008031000c0881c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 223480044 1250 223478794 223478813
    0xf030a0b0703061805220305070b04050c0a08030414010f0801170a020d060203091b130518070e0702010506011d06030601020a0c061d0613051302070807120206060d 72
    0x4008015410150100e04035502940012000e051078804c6110245480071285001d4003040d282c072100324403290104401c4004521100f41465059100c0300d11708113180e07440c2c100b07800c00240292054040e400d010072040d0703541074011005082d880f0044d5142d41c01e0403403124072000055402418031503020001040c09401000c100e0468800c86080f070b04600c494500d41e070a152410030029449034801d1031080070021384ea4040e5000f0030340001162030031080c0082d805a40742c200c0350301941c014030042085550440300d400c05580300e106c1d04a02c2c042080313440e60b5189071456a82020500b80c8540d010018902c0c4c0c2485000d42c07041b402d00e0300d50307019200c0c49110201c1030a8070466600842e0004001b54090b4020030030041c50300d90005401c9809969003c2c010411450001d626030905486c2c20302c021185014002d642480b20556081c0200910344410403140c0c915420f80000c46035020300804020450110142802902400d0440d40500f031166000307080c450010708051040d80c0300c10306c0c100852005071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 223481294 1250 223480044 223480063
    0x504030801051e10120e060126010605030f060f0c0f16050102070b0106110c04141f09110307090902030906150112090c170f21041e050f0f03 62
    0x2120b44045415000300404000f600d03020040e0815248001030b0b510603440030032000040f91340c80b41046a0005440301c652904800c0c483c1845c3c43d03510132000c4c609590416050302090b040103000103070244e40c50010070b0074100000001e0445401c030800300080d02a1340400a07500024880c90203103001c0c002805403900e405981080d680b8208071303912541c1001001d5045135205c54010800c41c00d1b0b90303504c11005105c081c41180f254898000c0c03000d00303c4503040601a0f130104803030480c18225a81d0784c1030405001103c2c0b18141441c9240b40c20000217800030588990813804910115560340c902d0203c1001d40303030000a501043c030b40c40c410801c0101d10500810801d130440c40d0080c0113490485070400403030303460040d00d0038808228940345504040184a40d4450304942c907003210520305940c0513040a4580d0301040100c5a190801c00013483d8045882650b02450b0381c00c2c428550905407a0600d428080c0004040c840d2501800c0000388038525244030f5404410f4021550401183c2090011079110203881 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 223482544 1250 223481294 223481299
    0xa03050f04260d02162603010911040e09012f03040f08040906080f011a010f0f0c0606080c130c170a0608330705030c0d14010902040315050403080105 66
    0x5807240384200c0c40c020031108140c0c1001803c1d500e46101e049080303c105e40c150300440b4003c072486011410058044d0031201082820003015056038a0000d452000e8a444905404185420000810881d4400962034062070802e000000e0000c440d4000c003080d000400c0c0361501c148100304050101c1c69101080f00c1e84140d20403021b1190810515001c556801903801104038076040110120b104040010034030461800500280003048142420100d0342069103100c900240c2801000100c190045502d003140210918100c4160b100315181c60341190f5141d08120002c0d000107100800300e180c901041100d080c04411300b00b0a50140c241301900c118281484171184201040c00141c0000301d96000b0300c010300030b84040e0f81107980c0d0581c0801c008a0883d821070007504140306850048403070740351840d11820003a140d0901e1070f1240c81c1d0007521a044540c8102071152140030002256040d0b00489000745411040983ca039429440c11002c1c590003003403c820074604d000204800309500c20f011a0444809 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 223483794 1250 223482544 223482593
    0x10e060c0a050d090c06030c0207140d0807031403040b060f1203040515041d040317010602060c0f090a030b1021030f09080d05031e090a060e0a170a03050f04 69
    0x40d0b40b4410f014145551010b031403460100300c0040c10540641200c0012032035682502c03480c40d100e0350030f15420301010003100e4005c100c0d803049000242c222002007114500900340740301007401c1d500441b1500c1d40200d81c00c503007540886092115038101044c1c5c2d103014045c2260241e000d0080001116540d0003140b00d01e0348110441c40107120280e0851044a0160404d0130310120360464211040b5030000c8161070403070020340c80c0c501c0000e50382e64a1001034160b5455a015194a494088000c0d650740c01844c9100e11200c0d0402100c40d441e6a07105030301e002984100d200c030002d0316010600c5004a1059400300c07000c3c61800c0020f0100c0303d801206d0458031581420003054808110300b0441d00e8444c07039007003d4228811503030a600d00030303004001f65200701e0440d44151050f40c0c860818140074001a034404c0c64503407140108000090840d00f243c0200109070742220a00b400e251102d8030f400c3d070080d0b4403460340d100001d10740034004da26001c0c0c0780d03001d9091400c441050505a450800035140300b03ca007c1c00151 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 223485044 1250 223483794 223483807
    0x402030f0a110c060a02040f080f0c06030a141302010e24210c0d0b06040b03040311030f04091a030109020102031902070b030a0b0405070216090203060a080303090f010e060c0a05 78
    0x1030442a030f0060f41c0c9034004c031504d9103048600b405c000d6026008640e44032040c51400109481c002501d4007090316004040c0032072041d99400c1c40700381d400141c4408413181c0c0750f200803402d8101c0c10000701c1c403640041070000d54056540c00050001c404c48100c82d8003907000b80d03011500b00100d41c2d20a81c81c202c01468400d50310021210580084800b4200100c401c011070001c1c0051025908064800d00c54070380c0c030800088460004001c1640b25601c140c170401e0800303100180c00300c1e004400b0900200b10360801e50f85013003003013100035103180d120360000311070542d80319441726a440d92034074002c001120030703002000341582a0700017030b64a0007072003005402c804125009450051091010350018000001040d03182e0801e0b21400340074003010b50146004528007000180864800038420540c4080200c0c43c980f4030b03040500581c040d610082205402050b081000038021400b00021403217a01d51102030520703001da0310415400e5500310700b03403503060754494000c0c401c42049407022154440c1c841d0402a6460303e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 223486294 1250 223485044 223485071
    0x80a0e011e08060d0b0108061605030114091317070b060a08070b03070315030308160e0a140307120b01230102060c030405010e0706110d02010e030a0c0515041b050402030f0a 76
    0x2103401d00090402c00c5060000980c1032001803810f000b000b0309c0200040c4004074943c02c0f100c5000034441c5003034441c0144062452818880351264028840e00b20794000001c06441d151003d00f00100e1500c0310b14030008002d800e01400e8010f00360840012980001c000e45003613a003e907150903600882142c0b200000209201c18041d900c0301031b0b000190662601c00d40c2e500c2c200600b009000300d03443d03503c00d841c44003d1840a4440e0441018511000f808110b2460901000c02c0c0e02402500d1090f030944903840c404621102c22044c2885400c1c81444007021039814104071654584640c6100d4170b5811420350100312503a000310313490364440e00c044540c0e80c0346d03550f500f0300e02d014012038028801c05014000000c20859481030000d400420940c045070740c00b44250303a04a0072940411552030035600180482070107a841550740984042c00791080710314610b08404180001d4030305039030485e10204204199103000090101c101c00400003100e0450540c5044c0a80000c6038100500c0b54402660361000c000184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 223487544 1250 223486294 223486309
    0x10c031103060f21031216020a110d051c031b1713060c08161b060c0e030d1806080423030c0d03060305060907030215090f0409080a0e011e0806 63
    0x20a0b58051506601c4d010180385900d076070207100d0864403480c541c000165003551101c0c0058400860fa4000c00400807185ca607240c0301d0450b140d1941d841500c0300c000001191080009508116803190500b21200b40da11020b012079003c109085011811a1400000075803c11611445214400d002c101255580c25000c5a076a001181c0100950b00c2e00362081825a880008203100d00c0f050303020f040c0d100036001c2d4141c2e1340003440c103c811480841e030101c0000007183c64222158840700c40c01c1444285600c0800241001d81807401900003c1c800d200c0101104072481c3d1140043c951801d01c24118103040e15181e00028250400c84461000050010460b072000c2040701d04400b00c603803c0d1100e8940c035090080190141d84010f5a01d84544408103c02c0b0002041e80002c403603009080e01480d055000c0e4100490b009026901e500440d4220000b81c03070b4446005265040348079129080c0d4884500f4009090109100381042c1007141650300c514603104890302d0741c1c50001d1a814800020b641d18030004114 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 223488794 1250 223487544 223487569
    0x10902040c020a0201091a091905090106020a121707050a140301140301060504020a2a02030a060c11070803090d06060906090e07080309060405090c0903060c0408010c031103060f 78
    0x1192421424002050b404a0520352062003641c4909201e696000d4200d062a800c4004078010f40040000c12130b1817508403003069600000007103001e41c0076601d4000554a5400764444000341e04050302140030040e040c454900d083e1082d080050318040d03085d80d80122100010440401e1000c0000d080340035600916046812510f1402969902d40c2c480303604500404407044464000c2d0308284010a030781c5414000e0303425841403039403502030200ca24400c143c41140300344810411200b40349131a80c00f68405000c7c4002c00341c002e201c04201100345d441c00901010309510000015081f1a00c18445404044122402e00c41c089a0106c0e01e07010b0790401d0700041100d64405165149884400141d800e000c2d081380c8211070040d0180d511076980c51401c0394a900c500010594000401c100520485c6030403034110743c000b003030034000a00701195107011910700142a10101c03850000400d0401420070240901d00d2440e000346020b020324403003402c24080d680000741401d4442c0320002040c9a2585440041c1400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 223490044 1250 223488794 223488799
    0x6011406070201020a0c0906060e01140a0810030c0803030f060405041502030a1107050d1806050d020d09050604030309050d0c0507090b03010b101205060618040e010e030a0905031006031a09010902 86
    0x5003a81d502c00f803e0044c00c41c0e21034003010410300c80001071a0341c040c06c0d004c0033503007660519615042080700200d17480940100704540991100e0b4011000c03511200220001d4030360b09004507628288441e0320110450002c050710310480c10441000001186401c1c00008007a2142015072240c0b900c0c00b40c50b001c4e141c404016200303c2c00105e400303800c0c000000381500ca40c1d085921100c8614400c01201040c001140c000c2c000825010411400c5030740042d401840b06c103d81040000c2c04404ca983c81034188a0181c07020340020b03440324008001d1100502001d2100c0e0054107000d6084013160b980c1903103ca0300351140e8030903140c2e524010340942d1001e400080c1c01a00c000e1110400c6c480c4400081e044161402c0c80080e5145000000354076820820200d40704034078800d8414003400b03042410003000d0642940844601e540b00d1003540c0450b00100040c00341c45000d40c840456090800060520344600c0d58440c0a600b0b040c002c1c10401704415404141e400c210301032004050742d6400c80464058025858001d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 223491294 1250 223490044 223490063
    0x303190203041a03101a1608041802090f03061608060d02030d0c05010b03010c091e0504150306050a020f0702010f0203210f070c0b01150c080703050403021206011406070201020a 78
    0x31105500d00011352040c241500c4041809440715040030505510011050202904120324030b000418404248020752180303620b54034154451600c00c01d0180d40301d40500100341c02240700541031400c03c9105140c0c3d90254000c0105103002d10b15440f10b0400094010103000030740300450400d88075040108103664016040b5402501203960007003128402610540301c81d440d100c3c1c03103100c0740307418010740ca084076495450400d01c030305011800510420002200e040080321640000710703500d4034001c8012040300300100302100352441c10325005a802c0186041c40f914410800c4150307400800d802d883c0e0041e020b181c00002600d90450503407851180007020908505c2180e40700100707421090005220700000e182150035034030740310000d44540078050802000c11100400500c180b0003100c640040703040851810b4104e484264843d00d440da444045c1c01d03000514000760500550410b402c12600b81c480b1840141079a40c948060f8203030a60f012500948200c900184c0c036420b58bc0708101e1034920317540040803036 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 223492544 1250 223491294 223491329
    0x1009050a0f110a06140a11011b0201020d0606050702131d010510090b0f0a0e150d0b0a050c03010b03070c0303020d1407090602010204081209040e030a08010603060b030402030319020304 81
    0x4801c0c82e105281d195110f1846814041201ca20036034001003483d510000d4207082a000c0f141c244e070b42c0e20118803800119943c804005640e00800601e4203072850043d0001039440d50052102403d5442076003100d0700388842042040c0c0161140d001c841c0802c1d08602c1c00140751002200c401c1d41000154007038209960800c82841440c480c00c644040c22188450310070010009400d041c00041501c1c40d1081d5030001c030100c004c00991015003105544000c1c6149091030014030304000901d0054a80000d591483c0503004200245000b0721a09801c03035031b04c01e4414110341c50105500318600c001025102044000e103000010940260152a1088803a15041c0b000d607419403026030303080c00c003242d1410000d203150b100041c03014018400c5a043d00c4032880134102c10454414030312074075440502c01030b400c150707a010000403d01040c00a01081982551828019498010020166503d5400a40728100b04106010041e13600004595040542c220020030f90600d440b000d82c290300465200044503440513405 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 223493794 1250 223492544 223492553
    0x7062c0103150b21060607020118150c0c080f030d110d06030602070204140606040e041505100f060e09042307061713050604030c0501021e250201021009050a0f 70
    0x6400c00691490070154080a01801300c410010142c610035041407040195002552041c04a5040c40d04c0010042500c01d6503103004140360300059003808000341c00d07030307180c202004945c195800080980c0c400501d412031100c00c82c26203e2041108074626107603078500c11540f906400c41510904010b400c000c2150741c1d40d0341401000703948101802c038030551030319100b03e6000341000c541900032407018041c0d6017003505000541c1e03c110b502403c00c0d40c040c1800c0070415112030213070060500c80d010a5501c2c50800e0302d00914031945402ca0b40100080c0f14034558644080d865010269034001d0308403942ca801304805036000312204100c00c0d48861140504d07140070400940007905650400c1290400103100d81d14901080c0c01c02e41c00c85002400e6030015800b20300824852400381022500400005180401c60b03440f458001c01101c50490f0494400f180681c441d886910340d9116105401c01c031011f0781f13411980000c0d100c0200c0c1d04030494045c0d03030f0400182030102c02c211140b626584042840d829213090b082 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 223495044 1250 223493794 223493797
    0x405063010021c090b01090e0c0301020a2c0619051b070f0e0903190212070f0c0603051603020a03020d1806150303090501030902061215010207062c0103150b 69
    0x300300f00c501469030280303826115107200320411142c0160826180e6403c00801a0241001d50f0000170b20b03208410882031603503800e100510035107001d9203442c800407400d540580a9001d55401246080f80c0080040c5101c1e141c0404881c040c025452101c04e401203c20b4099503075006176002e60211940074030f441c3c407504000003100c4068404426043c54803550ba41114481079108075040c0398160810300c0034420101c054459404100c1c014015a103e00c0400c22922606402c40304003612900c0d156020401400341098010300a04a1458140418940110b00d6200c0d6020001c0043c10540d000903010790040c8240d050f100c1102c00c0e21000d00c8144030400c1c420641400b5002c050769010300d408901c429070b0049500e65801c41e6459200c0c1c410140ca404010360040030100026600311108100d2440c4004071110842d02c078841403129401c0e00781c1424002840c222440e04142d0504c0707400c2e0101880d00301d11540c100300000e81d1010541c5601c4100004030041d107200000c0c2c40941d1000200401c03c0b000910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 223496294 1250 223495044 223495057
    0x3060803070510050109020405010504031104060302120106051005090d0f0302120a0201050f13150f090f08190503010501021e07150206041703070e0d050708031611040506301002 78
    0x30103004c5640c880d03802508a100707510500740418401c000405c0010b8081041d040703603001c020000180d041e5290045400da030302115000e44565035602040c84185000704850884005510f07080707041418400200c1e0590052940c003034486104040c6480416200304030152217800158101529085030b076001034041c00050754404224481d40c00000d201d01c07c07103410f59900070b170088814044284642031a8004201c0210401d4681d5240c03200130000c81e501100103946c1030300c5203c0065640c031030407011440220420200c0000c1000800041103146ea00061050b0100f8031602d480000542400d022031a040003a4050015603482c146085403407900400e50303d03ca14050b0003100c80303401d19400305001902c0300f12803620210b4030030030981c0024200b000e11126994881d84c2142c2e0429102c0e003850f4503580104817484502d8150412210800c000012300340a07018040c0c50a1015050280c001a42089004440003030302400f081c8100d2110001d00714000b0881441c0181c2d8003c2e803507800c0342e40183d400792 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 223497544 1250 223496294 223496323
    0xc0c09010503030309070e091c0509011704081e19030b09011508070302030c120a022d0a11100c0c022e1103040902030a06030b060102150402060307030608030705 71
    0x81000181038100801220f2040241d000075224150404808850070a00a4940a490b00c41d625100888400301c252000e80340701551203103902e40c030010b8001010106c02104051017a0000800d01c0001201101038610042142c907404c845d6141c03010300d01c101d40c06030702c04c40070b81c004001103900e8040e505a4031081c040201980c0c1401e0070781c1c0b02c61404080021807000300d000100e00384000f0b0b4869100c0e43c05581c000750340ca00d807280b410790100c80b03506540205071284d0b00250350010741c00100c03c8130b4400b00a00100c14291100340814624814000b50051103201018000c040c1400207000da010b120390904e100c0c2480c0d04210552644d00d00901500301d03038078100d001c0c00f0084600c80702c80d4240c03c6802c00504072902c13501181c00d0702c44022107814010f01c14442e014803041c003011501c0c005500103940701f08101c580018165165081c10401e081c0085c11850554204110b880404041c141c0c1244d4490f4041e100140d9a4464243c00c80c0200015441001e081c00003080080c1004000710f91417441c103285 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 223498794 1250 223497544 223497559
    0x302010306060f02061315020307020f16060207031b150801080c0d0b0615040b0a0201090c0f08070303030203040804050904230c01020309040e0f12072001050409090c05060c0c 77
    0x100c00c000d84110f110741c1819409070344000002100071040d00019a00c07240b09000e14840340001c5003a150a9800c01e4a418015803c8040e1030600207808001401070b00e01000d281c403080619007030021b0f48900082c0006400740c030310048a500e00004036940a0014070040a0500b00010951030003011407000b8041c229450180144c0000340c1c3c03804070725440074680c01108070300703140d00c5441c1048134109010300104006c04060000242c3c2c441d0075805415040c1072500003180b04c0e1220b02c0c1c00703d5120101c1c0c001d101d041038206401e10582000007801c000751703a4981801039403620b4030300b04601580503a500495010f51808100010030581100e0949100308540000300e9403000d001240340c441c03280e045480c0c0140d1003030000003014035094225580c003910100946070407065500215040400080703180c40000800034020081041481c10400c1c803031020103010418401c0700300001c107a44598400e01d40d4054450300c801c0305024640006000a0400401c0709950f09004190692645079800c02c0a1007004c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 223500044 1250 223498794 223498799
    0x711030111070c08190c05040b04150824010b09010804060b030627010605031f06030f0b0702120a020601050607060e011d0d09031505040309031a0f0604091709041103010f0302010306 80
    0x488003450064654400d88a490150130705061000800704944001c0c0d102d41c41d1825180b8208030022f210001d082c090b0090014180300300b4000c0021145041550b46402a05004000104000082c0d82125a007481c02003200d403501e0602c7d80161240380100341d410b0041c1000d10003007100c20480160142c0045000c0349050b4400038890742201d1845c415181c03d42c000b1817540e00b01d003496815003540380c100d80100181407038894482130010740700d152045805070b0010080c8102c26804102c10340c00030841a0505180911001c40251540c00c1841007500420000c5000010030085402486c401d25000008000b03001c1c00c5643c0504869040700c50085a000708442d005159100e0295070081d43c0d000a004491103440c0c0082e54010f10005000382d0400200303200100c002a29620780c040c204002c188102454284408902c020304009000107200301c1c070f400000d41c0040c80401074482d0980c0000c00385620780d10f1001c0401d0240c80307070300c01c1c03486010b10000001c100c0c28117400c01401564004e030303010031401383c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 223501294 1250 223500044 223500073
    0x3020a09060201090507090c05120a02040509060d0c060f14120103020a0f03022407120203030901060509090a020108071206060309051203040812040807020d0308060f150711030111070c08 82
    0x208800f2014161b030304440c038240700a0b82a42c00c07140d22800b0030301e89681b810106117190485a0000d4070340a81c91500010200070300e24120000942003c0c040301c00740d1007144166110b102074040d038882c200502c800d04460811845c040ca00e525010009481c2c001d6403442c501c2c00712607c0c4c402c00d020413482103150034804150f07003c0000c00307001038a80c0038002600d44551a8402078011800381c0e03040540c000200004030000d11160350801504400780c0045072a8181142c40c6825500ea03034020074014034403030b410041c03407481c002440c80e02144c0a003003080c226118204200e03002c9910959001200b82012800101c0981c0741d84402041070155007512002040349003201924030003500e02910580b01400300701c1c0302d580c103c001d0b117811038424070280785003030015408500f0b050102c20094010403411000c020a03030070321101704c00780910111000100f004012040034a68041d900d0098481824150805a1601d00350701507001410f1310100306440c0d054a1808141e00d8005000d161618010b02105139580c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 223502544 1250 223501294 223501301
    0x17070b0315040b03190b040c0509190c2703060509010c0f0f0504091d060a1418011e0903090902040b0a1427010e0306060901050918030a03020a09060201 67
    0x25081400c03001c0c10440c9010410000d04001c890071503050003003103862505108070360b0880c2c01003480b40d400c0010034038107814001100c3d0390592200c0d004241010402c406041070003000f003200c3d04800c00004442c40b603210101c6017a81481a40380303c41c880703034080510099141c02c0780c6046901c24082070009940b06200503007a11441c1002201060007011001ca5090081c0101d82240006140c214100350380e40c51440d080d10340303408010146000800d03c0c00d40c111001d0055503807000804000f0300180c4699400708001c5503005181d54040204402c10604010080d00150010901d0030840390038a6240c100f414014001250300301c5c00b1400c010400503000d8140c0c02900c084803804c100e8603080981e404010340c0c800c0c08004074071008090401004440601d03604d84600756003800c0740c0c0e801652042d80d0015180f110780d102501d100e60f0081c001c110f210390b40d05003076a05446041e00e000d406078071082d01c0c50b1442c2d502102051114000801d0b070141e0603a140d8054a158000ca540f90b03582141c0d1600305900700e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 223503794 1250 223502544 223502551
    0x7020f010e0a0b070e0d060f0c090e130b1005060c010e010b0a0305060103020603040c0e040302100606020304050d0807030e0d0605070f090602100507050904110414090f0106031a04050117070b03 85
    0x380800c00c0d000071891801409181da0407540a0080c41b8616482da07140c4040f102003144540c4042d40d1550b150184a038003865042c09000c20120724111402c0c080300c201c0390050006001441c8420040010368400002e202c1d0300e00408014014a840d07030080196035001c2c00261500b00081d6107000c400c0000b0745010503200e001c49400a000e480d007a400c41e000d20546074001007043ea51414503840000e15415095482791243c0e010303a02500c072034000c0740e81d4402030f540694052011540180003c1c40155a0b40404042641c0d1041c101a070300c11851405441081015111036030044480808034240009038102520403000d556a130015449401c0c010b4035818070b240180c0e00180c0c0f00e8045202c48031100d600c1640c0000050400070700b0210040000fa0958506401e03108010f1000305042201c450403100ea080305a008881306081c528040c40030800e5908140704001c1050f0701e9001840300e0303002c007411107038005c600035200780078a68540600080034250310181344000d1003604400070700c0084480c207a901 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 223505044 1250 223503794 223503803
    0x181f0503040b090304230901060801082a04050c040e2503021612030204060201140103080a050a0306030f11091605190504090507080f09010606080609190507020f010e0a 74
    0x3507403603684030079464400c02860300d206803004120106074030003070010015103400c400e8020000c1c85044018080d90b00700603032089051002100040c481c40b18049030b4101e803c9413000c1c0303401c0a41c1c0c0210008507061480d5441d140c02502e002c0c140105848020002e000307403101e80003000c0e2140c45000100311941521032071038002a80240d400200d4511940080c001545680850f1080c00e4003074a5650100480e401c507000402c0d80061308005054080c040d82d80083d412850320350a9601d15158426144240d04e1244204000007404e5100c580c000d500000155410030346071060700341d0900d84a4007005c010004603105900d01c40c001526030141c550b089507095415510b95090030041d24a2680703000f00803001d401441014440401c0f101d41602c1443d03c81c2d00190b6803c1b0342400c10300c5030001c9481c0d02801c6044c840c0d040440503c00c10340c1042c4001d4200005440e5100241e8a100c8401e400b07412041c55071207028100380c05e0100e40d660018949509000d0040200b0050a00d504130a64415030b4a10003403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 223506294 1250 223505044 223505047
    0x1106060102150a15080f160e0705070c0b04090903030f0b01140f0405090c03180d0c170906070501050103110a0f030609060b030610030b0705040e13030311181f05 71
    0x42d2060141c0304141c2c3c1202c900c0d40c0c0890100c0f101c40071000089165045915543d01420041010100130040f034140d2030704050015000354180043c00790031902c000c10440c01c0c0100001c4041c2081039000c014401818076060164a6a0300c540510001e410701034002da0002c0c0c11702d079074541003203003a214041004805840340d0125021240c001c045c0343c0c1044c05c8581421005100014140e100e40106c688070301101500980d882c60400c800781c12071040d4a0044101c1c1e40000400c001c690340006600d81540d03000150a1050210300400e0540382c464078500e0394000d4408180e8200708081500424140c07441804010903560302e15041c4030f00c404841c407075441d151030401c8041002c10407a500c66944070703000d00004102c1e40c4505020030700c1c1440039038940b600800003180402c00d00035501c49454000f001403901c1403400c3d00d03145186428080240105451441c03621070102010700a40c082e16000314040e508a490300022800020403903549152140100e2080c2c0c3c50305c842c45c2c000d00001d00300c61555102d15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 223507544 1250 223506294 223506313
    0x601020303280f06050312070209070e190b071208090a020d0807060e0303190203040f030305070e13141f031b030204050a020a031d0c061c0203010b0304031106060102 73
    0x51800b0361207108407858005034042c0e41c4008501034016051000e0444101040d41440d04043c1440d001250039103500d8000240010700042e61101c4146820000700c0c5014901d101c07012000421015010f140021040700700c80b00059081d1803040580b00940c0501241d080e00040d00100740c8441004640f03820003508060b2502e001840d00d0300111100900602e095030509031540e583d40112a03040020311081c0d4808030400078402c604880003c48000d16000540c00d60901d03680e0b9200c4c0e1403d40c803000341810740703d500040259104907001d0205001c020540b125805541032010300400791202040d6100c3c103c10b0001704829100c00540c00e00d16202d140540901d49552540d04001c80001e64480b6482c1440703800101680d03d80c0140d074000c05a5070b500594495800341d01404444000d4401c20070034240c3c4141410310030004c20f01d005400015620196219000400700101d405030707100c42e89034103101100100328590a540610b20440c1300e9191351092401c44000701d5036401044a2076401a40842c1d0103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 223508794 1250 223507544 223507561
    0xa0c0203061503030d090305121305190213050603150a0501060f09080d110f0d0509360c0d051008190b071202160510051b0d11041502070317030601020303 68
    0x201e41b41c042e28029060210b5018071258002d0251200e030341030030b00304c0d4085042c0314042c40103090940710050b0184005216501240582410300f14501800f070b40d032000680c954409018610100c07200a00c507192502c1c1c10303940f4100401080c0a030000046113490518802e07030144104009440010000384441046440100c919801c0300084078042d008050051107807002c20410395845a05940b2426143c0d0454001e2092200ca810110000180140c10f590f40b00803042c01800b41ca40e00300c01d414861341e95440a80034862240175000542c040c0703080204070f2003002e410140800d40d60074800b034940c2c540d46070f1030400e4018042c132070160010b0080804a40903d00801d420b4100070f5240710054204090010140d001c094034802c26201c680281100080411035841560760000025103503108141001c2c001e40c0c45401104080560030350384122861001c4100d4081e01d0040101d900c510b042c070041900c0013510b440051104495003070b1040e0203c8210000d2070290303449243c041e0300a608640d1510318 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 223510044 1250 223508794 223508801
    0x5070504051f140d0e160302011b03021603050f01060506071211120c031305120a0f06020702030d02070e0c03010e060d0609060203090109030e060c0c060318030a0c0203061503030d 79
    0x400c8020f0201100201c42142c1c1c03500094a1004250300c8000b0b05e00045441d85401c050300d0b945a001e044454410070300060f80c02564011910030714032040c0000c0c42c098030303080c0e1600900310104620801269400010414002051102d03400501e00a00640b40d40d02c3c00c1c4109409400c00c018801180340144e504030307902c0b420f070480c40d0f250500211580400203201006265001800004540d040003074504404a030b8110703004c0040c24103a806241012030048290344034441260000d040c0c1e001c1c0c01c2c400c41800410f806450107560001c0a0740c00c1030803400f03800380d40c0760f001d88a003031002504240080c60b40440740003940c1c100d540001e0002c1040d0341d400b00300441c103000858220b0300c25541e0440040403506505c0030b14440c400342c00c000201041306040140c003c1d0541c900da0b0f17104400c00c11408e84a03480100b01c01340d140b1000c1d9035103912922030454460005501d2030416a00348004100b10440701c3d4031034000444030b8001e0f4150741103510783d802c0a041ea541c1809004e038040d442000040b296000a03407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 223511294 1250 223510044 223510099
    0xe0705030c0f040e18150415020c030904021803060c070c09050c0d0527010501031205090303070506040312060b031302060a1106100518220204090204020a030e010507050405 76
    0x3403001e10b010340721032066181d03d030145c90225401226501d04041200d00300502558070100904000e1149401da030740000001c00d105584a5054012841290f1040300b0810f407810420010000d544521880c0c44ea00200c186c5072750380354480c2c03040750040343d031a040e14812910758030380009000e00102d0410120b040a0440a0701d071241050041200e0b0441c03400f10302c240780c01081c0942d40300001c0b400c0d000900398000c40c6c48001034107507454803004000040c0c1c0042441d858014074102581c4500c6520002810340c000d0f072101030001d024500411080603400300e0f03805404407032a0800c000494841024141c1030004503880e0b800444807110300d00143c500000076010004031841e01d101e02d02e6080c02c0040c1025425100041590485041031050f40381042031404000361010010005140c40b00051b110414407108000d800045142203034159221900852900307074000d00f06540e00c03000030314001c0060442d508041041d51030880451540c1d0320480c201c4045030b0004000002d0941007400c0a00b9240446 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 223512544 1250 223511294 223511317
    0x1506010504030629060f1e0405031006051e0d0201031d01021c050a090201020a0803060102150711070e01080c040509010207021c140d0f0c03030f020c03070c0e0705030c 74
    0x140800000a11280034880d03042100c0da9180c440c55106051460058581d1804248141d6086c00b00c010710410320026a01541901590200711101d03400682c0700512668006940600680383ca07131007545280c0e0000402c0340c80603141e040303035107940000b01c28040c241d81c007049611944200400000d903219801c144000d0074043d24001855820b45921802c83e4081d07032403a0180404403e1600132031866200f080d40c0a440c0c40000c0c03020b520341e940000e4507081c0c010402880c070b02e408070110302e09034400c000071070000c010005103101d58204400701030310440e510f84d000c0c01144103040012440c000e00c582018103c3c0d061600901c282050002000098000100011140d6609201a20140c5c0d6101c0d880b5640702c08a919110580d00c590500880e500f991607012207540e4002c0500780c485a901c0a06000360200a203001e188204091900310060000320320000c5e502030000c2240d03130b20590084014691148115a907c98940d0740301e0301260070780c07012110100495020300001d040311600100506008009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 223513794 1250 223512544 223512547
    0x5070e13080301141906020a0605010b0405061c020c01092001111e010b0301050c040f0f030f02010f0e04090c1d0f040204020a0c080d1505060306030a060b0a0305030c060f0f010815060105 82
    0x100d02d05c030f200c1c0c038403980080016803200552000b804000c0c07144501610085e800c4a00e05414800485c01c0c40c490004621064041002a81603111780c6038140c411141705480244591040d904240242d11b44d070840101d059203c04485a0003980202c8844a1030f40303001006e0942d2002200007010640381c86241079945540725500c0790b955640a104052050324001e04c1c16480c0d80c02d1680050381140786401004412010b0310081c00403540300450180081d6091a00076406800707510101c840f00c10400c13031141c1040c1450029070070030078106085010b035555100d9400b080602c4d80a40c82e0510303025128440d00c0c2483d500480c02604040d002001d14480b503040510291170699550b052582c080e0107003043c12551400c0c4241e1a109900c0d81c8070081004555003411414420000b903260b40843d24018450b40c1c1e1030040d90742c01e4862021441c0110780100560f5101e5800040540d1a0103048503d894651441c60018800040b04007110341622440d000130a4120807021244071507070f8001d403015050160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 223515044 1250 223513794 223513819
    0xd0201120b012006011401050a230403020d03030e010b06090d080306030307080d05060a09060506030a0b1207140907080709030b0a02040e0103050f0105100617061c05070e1308030114 80
    0xa10403c10920380c00c601d005007050344c580070310300340940c0d80300d108681040402c02240484a030b100c40ca200c1031115071311040782c07540040141c007280c6110f581c0c0001e400400780d160b45800c0c10b80640c061261000100002d02c03d2030341e982c080000c0e501c0750754200c680c02003060381a00085840300001d198890303c041c0803246802056210319607260094080e882145480b4010030007141080000c3c00300610455505201150404000810500006289580d100d60720f948016982d902c460030b03162078203042e50a89262a4550342109812100000c00034090368000b40407900d09441640014807515403a80d80709940d6007161344240d2a8800075101a58042c2c0a1001142080300c1608250085210300010015400c542100c41e0035603500070030044151285070010044d144e0044050300d19003400680c2c1100e0340d0703610000100310001141c00400350b640f102c0380000800100107403810030b9488642c3c4e188066076400c100700004440c41c20004014a90500040105402c220494020080000e118004201 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 223516294 1250 223515044 223515077
    0xa0516210602070624050a1401030b010207030b0a060501170105010503010b0703110d08040501050906071d1309031808010519020a110a050318010801051c02012604020a050d0201120b01 81
    0x1150746a080e41045c003c1c40388250300c00d0740028a50001c010940d0f0b01d90006140c111095200020404c909041c180ca400b108039441e07100340449809143c1c40006140142000850000280550300603280802c071820136540b450b4040021450480304160344552960313003841ea151400d81c00c81d542c101c040c40f00c584000006d0070f4040c040059444225681c140c114a81400d005003034603406010107070107170011014010440d50001c03a02070344014041024148058100c081201c11020020800ea114a400138900c10940d01c04a0344610710b01c6a440c282c203d03515840d9041c201c0b230040d94848040c004803a0f5400c810140340d00070340001c00c3d49040101c50701420031113880c00c0c001039a8040710aa00002020000f14103070303103900d14a0840a00e00071880790704000c0030480a5554181d8200f1181d45d206400085a108403000c0768412410004540d05560980c5075000500064604071b220b038290540100d103030b0400c00409590303c0d40581d01c9100c84030b0360303c00100003803075a0006035042007580c0100300c4901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 223517544 1250 223516294 223516301
    0x30403260a0c080f070e0919060902070c060206010b09090a1d0a02010f09030201090e180706020f0606181801060815010e0105010903020619120e0a05162106020706 72
    0x11125140080750758061500c004003d000000d194402d003945100500012035404460226051415104910241c13501183d0600c02000c0749840c0300e40a007400070202c2d41089a0700540b201910079501407585135220581a40ca42c0800d02620220031000d1220217042e1a201c18040d030418445900014030041e18000f40761002100d284c000444d5005a20202c1156800060421810254a0310b82c203101c0c01d542c0001d01140312403099011081c0f19401254088800c000c0e8011314842c25030450f45c10340c0d41c2d414040d48900d25102401c0050040070001041030070f140f4102c08054074480301503002d87d41c401c50f2034a9010700704032440e0010340d6036004c082002c0c1c13820064500310342030308610000c0c1c640c903201024200120507041a4108550359400300016145c3e8001d071441a0031003c1d28101108509600701d4841c0e0f004003000580b542481407004202c0408a010303900c450244043d9400c82c01561003100000400e407145103586810002202683d02d00c0020403401e151007103402620703050043d214002075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 223518794 1250 223517544 223517551
    0x1050309150a1b05270d030507050709060f06180b04061d0307091d03070f08031b04030606030605070903020a05150d1a0a120c0504050601021009081c020403020603040326 75
    0x100704c000605c1c4003409040c015200b010380c00d804200c00c03202001c03030100b040306046842c014184100494000108003003404610060102e41d00200f0240c1c1d99007095440c140d80c68450100400c04aa40003080c1c09101c1140d40300790f820300307803645141c81d1502108550043c08010240b540f180c4501d0b1501d45543c1c2404081d0041c49480e80114560515070f082402d002c0041c20702e40841d0348100701141c00a4010b50401c00c016410000041c1c9981d0b4002c0c0d0490b605d180305104004040f400540842000a154004d0b400c0c1c0380166030800072503559400581d00b0760514000030f540070880c0380d81000707140b502d10100c0d800e145088080754203020b956254001560b8515a030035030350b820a941e4a0320310b810304501800c003d02100c092744115580c0f94840041d101d40c680a45400f030754440b400149164000c1003100402060000200100412070920302aa60001642042044d174052000700d9983c6060003550103032030b00280410b2850725a59400d8071030070342c640c210244035500c9513580c03807142d40741c0c0652520 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 223520044 1250 223518794 223518797
    0x1b050d110120060133110a15020d0e0c03070506030901020409090f0201031116060b12060a0c08280203060307120b0708061c02040b0301020903030a030e0c01050309150a1b 75
    0x10f00d0b50400401c01211a408503092036060b00b400068200000240c80303101c0e081c100350400001d40e90540503120b06058845801a00d001c02c1500c0c224841074540c0d0084c40e0640c1100c10400020f05002c036095225004042c0c800e074107074800d030014415454903c00440c0c000e41c880c0f0005250640d00c031250800e8654400050b0342c00701e541482d410035540c01d8002c00800c21460312400746003004100514001c4120303190040c2003035641e80b00b20740b1981c139060408984402c401c001c5841d1803420307440310000345c00785500f050005900303080865216164907040c045201c108038500350128801c200718000941004100f00e5240c03007507000018910b105074a11041c414061850f40c00da038909110080c0c041c21000c0d00c5640550710910303d81840c1c0303010f80f49140b04503a04640100301805d1010000703019000340350350740e507040c000022069103c540640c003282140780310790291244440305000641d52400100c41c0501d46030004c070400d044035240b006609501004548001420001140ea88250038009010020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 223521294 1250 223520044 223520053
    0xf03030c20222301060c05010b041a1908030912120f07050712021806210d0314060315040309030b0103030e0306060a140f0f040908071b050d110120 65
    0x1c03000300503802a0442d403c8403c2000810f000004210155400144174110400504c280d0040802500307400540c0114030003001448000c034031211481000c3e4610000501c0f40007000b145d200040d4844840f0340c112103540010310709006d0f21100b40a00c030150001122160300a5100c21862041c4000140200c9100340c0303190790302d0300482c1c5082454031180da00021071003c041c41c07030a001641ca038a4481003c41400044216588612000c91810f000c5000014010840444500c1c01c070400081d099024203029507040c4a010010040c4d81084c41003600c20341d4040c0c0100c0c940c011840d68800310181c1080c4203280c102e604650329203404c50714a0003a00210002045400114000d141c100910358029000310b40d6102c0c51481c10040700a10140c2c282054000d00d5100500ea032680e4803503108040102001d003050044a100c1d02e82003585900140d8100c6070278580190160f030700011008031030140c441c0a440360b4104005621801000780c603c0280a040040e2640420360512034030070303a45040b524003070081 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 223522544 1250 223521294 223521349
    0x305030702060f160c060209090103030509030c040b1c02060403120201150605031e060f03010603050106050405070c0b0c1827011a0912030408060103030507020a0f03030c20 76
    0x80c100702c0041c2c41070780e0b1040c107071003880f1070701407040c202e01c42000c418244004108001c0c5091401707030007100c0e0030551200464000000707058104005104400c412026101c4040240003008100c1e5001038107a034100541e60301c1484050841242401c0140c0005d007003501f450340d03a9031a03d507034000c03064100d00140d4442610103881514000b0001c09403580f801c0640c21407a00641c2e12910600303400000344241c04d058040b0b05035464007211b104003040050000e1003560745a05205010702018030075035005038940320000351024494401604116844480c40c01d5940711680e00c101c06800040091600300c000003401c1c2e1080d82c4180c2006a800008085503201d030740300e1140088a004141e00040c80d900c0719200c8244110b580c0400c50b03003a40c10413505030340c1e840c0161003c10f24500454028100e05e00c9420000f009264110340684140da10849650001c03d456500c0d444d44a0310512000b00800c40036101d036070003d00350f13124072700710038900c0710705d003c41c6410344400140c03900726000d000d003101c101c00c207100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 223523794 1250 223522544 223522547
    0x70c0f030b07110a0201030b0a050303120412020c1f020c041d0c04052703040902030c12070302091c0f32010902030c100215010e1e0c220503030703050307 68
    0x260b54450480d0400c1c0f111031440603100ca8032003001c50710090400d941d035035240700300c0e603580100c0c0c0c1e000c1c24015040303d40359001d5910680b00480c0560382602c420300320380d01c00e415003480003812890016010300516004004600291300f10300300e1a076010190701460742c408141361075501c40c54031451039640c15050717000441c04040e42001011214980541c2c100800c002c0c0c6500800c42103400410503100e111a141d0820b8107640c198095500722440c81400081885416804d4001929420080c1c0700c0310002130f150010158100d2150410080c0c120f00c001841a0a1056100c010070000340901c5862542072070690f500c4000308400c2c80740c5990002500390050000062031860f62400380d04e20001c011255094001a40e902d62028410707110f01381c540842d0140034400e0241c80300084107041d0f140720558581224405000040b60200310001550751482515400c4111240c083c02d80308078000d191211044406520f03103c400144408a580706000069513101000100046802a5240c40d26410310210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 223525044 1250 223523794 223523813
    0x5100503210c030f19230a020304050910050328060507030902030f031306030603050303041e060207050a1205120c0d090c03080301090608070f05011d09070804030809030a020c04020f070c0f03 84
    0x5010040180c2801a5807062550380c4514010186c00610300d034a450a0031001c0303146100300d81003990003203410001e1100d035440d58003086042d208210700b961400d24201c1c0c4551040b80320507200d598840e8810a141c00444c056500182c0c12000310b1502058110b1940c02003803800c0c41250201d83c40da4000290b100030b61103059045805090395140c01c1c00f80d036103141c48503583c0740405080903021007110401e160720900408070206040741c0c080d80a5444240600301152501c40c0310a081d01e0a6000e88031681920b84641c1c2140c904403c10000b4016980f0703680160005904100c0c5444a015030303608020010a106405110007903120b034062030f03038960411040c1c600341d92103980242c0742a40640e00c28010f000242c1e5109080c1c130402e103442c235486140c0150704404015042d42042d0020038a10500c1020340e0f0015043e4030542c02601c941d40b65882d900d40580c1d0320303c900c8a041c0d0050300030710099042c0d46407a030010700107540c2c28890a81442d4030754490444802403030780100300382103450b0780402c1000703002403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 223526294 1250 223525044 223525087
    0x10324030b01150504030215091c0309140306040b190f0501090e0102040b030a0504020d20040c02030a090605070203160602071d061008091507020d0305100503210c030f 74
    0x5200600000f02d902d014115010368080244100704100d00410300782102016522818001042c8001100400d0100185c2e1001d1342d01c240c000403000607011a01e03080807200d0a1440d6800b9000301883e64840e03c4150121a018200c0840480341510310080448680146107800b16128400500d0b549002450400ca80c40c40d440480b0b80d90040c001000101400b405495202815071400b1a2582d01d903c00256414032a520042c0600c1e02468001d0308200342c002103019903901501d003044140000d620990352401000c1411001510b440014441c851058010b00315051000c0c044a0002d048a1400c00390403141d5040800143e100a400300a16140e40901000e07502c0c01d0140c5a000b800c110020807248000b114100c0e05002054011880020041116042c91441200f23401550709000354025119581d200300702c40000d00f03000220700c24012070f440c5e40c0100c030300c02401007580d034007280c55444000c0f4581c841031220705401d01c110490031005000824034070644d015650380e070b02d440580b50003401d44200d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 223527544 1250 223526294 223526309
    0x30f15080c0f0603070f02010f02071505180303160302071202060910110d0b0102030d0f020d0605040509060a050c0403061b09060f0c06150308070c1a0f0901030b010324030b01 77
    0x5102d0000392100f0742240c0d003002031031500f40d41c00d074044201030380541400d0108038045440000c1c0403040c04088a268081c0e800c6500c803e1015403100d540e0702c03004455015100a80c0c1e0020808141142c0d40c503000400b00c00c2c0c071824007500b0001c0036240d42c510000304205500c0540c00c1201085000d140a0000841c00741d0344640401c8444a17500c401d0105005082580c030300603549103a000304681c003c20984005041d070309001d0040d007090420300e00203034000401e0b04600a00f412400f08180c074040c000c080c0300b229507200404980ea6a11f91510280c00e0161100da142c5000704008004113469010b84120b08852a203c170385802e13070364100141301c0c201641c00306042044061001030709651090038011344982041c40820311807010020582c02501c142e20017404d1300e1000034610104002d500210701182c844034a41d10190105142040d210700c20400c03003490400c02005031703a80642c003e500c820003906040c580020310b09401200740000c16031300381010121510313272401001001101d290680c0902401d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 223528794 1250 223527544 223527559
    0x1b0b09280803010e0c04090507170105040b090c03070306120803090613051b0a09020a090f080102070201090e0a110703020c0f0a06020c090c191101060f0b0f0307030f15080c 76
    0x58803030710034600040c012041e2195580c4042001c0c801110140c40181081d800b0030032150600b00c002520b000c0b8844080003112044100004281c54240b08000603100083c003803120320f40c0c40d40807180700c5a000802d4001819174680340420000c0f0f5011180500d40e00c1901c070340c2e030b407810004001c600d00040140b50420201c0720380d80d03040008a021800140c1c00c0d840944400c0f1840340700e4001034204001d0b070060032100e031000c035200e0314013640203c10340c003210042203404c1142910b5100c034600340e01c642c10011740403540d41e100030070406000030800c0e903210805980004441c1440e071048030f4554403180c000d81c010384c000c05e0400a98580701844c518807181c1220b2800b15a460000d019480312000c3c0b03d403510410300e201c000f032150341c1081c0c1200c2d5a41454040c3c200042d0840001a040d07800415600fa040e619184010584a014800000135200c03604e00c01d071308114035500d1000041c0d01c0186100f040584074201e402c2034003010300420140031a9144c102100030701308034209162507409100644140708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 223530044 1250 223528794 223528873
    0x30308070201200d020913230a0921020115060f1803030f0c02030c031501030c0801180f02121219020a1a0402010c0b0a062409061b0b09 60
    0x2200011581a18844000503031190b40e451b00007241c5614201e0f600660034280700301d96050058140300c2c400e80c122080412003035902c071046080112448450f0090000404188440325510201c0030580d2211044c030000c20f103515004441c00d1000c0781c550109010540340d0b04911981c5421404640c3c0f82100c1d0b1a10803200c6107103840c000c004200150745413080c003000c0030101003551424841090010809002c59141c03000609100003200310911090b29480d50260011460074018061b5606840396911017090412040e191240000c400b854100d03408141038040540c4200d040c062003c1d072404e4801c141c1e07141c115502076407101d480c8240c0e0003806c46d0003402268001420119000c00c50101c041e4000009503160b1005948a03041c04102074102000201006210400d81c1c22038821b0b14840c1c2c19010440344480000700110302999010b038003080068a060000c20b10034841480e042d05014090000b01c205902c81074021b8000740c1c0c2c0302c0010b400500c034000c1e002d0751903000c900c00c0c002c0102c0400015507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 223531294 1250 223530044 223530101
    0x13051e0108130f0c03060b0307080a02150d1506030c03020c10020f09090f040c1208120403140a0c020f09010b07140c130207170901090306020919030308070201 70
    0x104062864140185500030030b501052a03070241c00101c0c0d00058262000c00c02d814841d03c914000d100c112646410072101c0c480a09020a0800851700980020040310015034200400a01660780b5104201400c0c0810502c1070210f01030480060380b40708084614500f8404010150361924440c20181401002048041a400140c88c6015040a0380050321002007510070b508511540c1d06281e0310003812002d004040b005040350f030b40200c1c81040e510040350358680360841034000030f80300980310340000c4c000540c0240079000400c5d8041d10904e442c40c103070000d0000c4484290031450003400060808255041182010701d81900c031050200e82d400c9081d0b15101400e055441000c80040842007081000c00c1c81e014200288523406600510304000210101d043c9802500801c00035680e0703000240404074102d01442c2200c9103410180e584410fa1425074031100c01a600c0070309219004081e00d12481100c03054207d108020f18400c0da1007051a00f810800242540c05070144060325845802da40c02005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 223532544 1250 223531294 223531339
    0x5010602100209040b0603090607030e0d0503070e0d0b1e09010b0a0501050d0e070e0a1401060e01050702030c0a06050a020607110a03110c0d0501050901060b09030a0204090f171305 79
    0x38401a00c0540d4819041c3c001c140503242c0d403040560003800100c14040380c0c2102042062051a05a800b0803000300f00c2602240e032421000340410208504102258a661203100203041d01d000141040518600c2652643d025075800c80e403001d140c0c1040701500d090714411216582d0005400c00c028041302c60b00e0800104c07140810f2103010305010001600b07291412440e045448001c80407420b44c3c5c3c03540e5603401032400d036001c102c4d0a80c0d2010318012020b00c014580f410031506842c4207903a1400706084240043d121580919402e0b030781441503042d4042e0b695540c0300000c02603d0142d5495441720311840010b4945140a400c2406104003d00114000c01d0300240d1500541d40520344262410b410314805801e20b4407420404d0381041e41d0600d104244041508210700501c13000000b04105d903078505100105000f94084c03140c0c075811006000001d45001d400000b0b90707600400e0b03013034240d003029a648504464001c0703544201481c08a03c03540e40c4504480088010300c42698a4014001c2850248600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 223533794 1250 223532544 223532563
    0xf011506050a090f1203090b211801051e07020703030f1404080a03020c01020c030c01080a0c020f060a050106181d1f08030705010b121b0310050106110f0105010602 72
    0x1080404100d0340300040c803c10b03120000344149000c06407065120a42c0c8455a40c41c4001034000c40e410540000e08c41132204e04680d4918140c41d10382c2c0b900c3d0403100700700e086010058280c028031800440061418076003032242034002d0102c114882e11211281c2014050801d000740300e801550405102000030076002032034071800740890b251a015202401010b1200d0340030359007200d8028841c58000c00101038000a480329140001d8080390f51421005c410540e0342c1c00c010000600082c034100104400c0c070000e400c0000c0c40c0d450b5006a4000660300300d191868a581110701b9098030381c95500400000b90480f01926500170000c10010201c0d0510350343c10f9080004441108075900b02e100081d261041960b00065213a42007001620231941c1c0702c18555480d00300d02401d8070107500e0818007007410310f021b401400d04904031401500c0b0308a480105900021494000c2c01c4c0c060081000100c00c0030000d100f01740c060030704d0b178840340c02c100c9000b014985002801030103020f02c2e0785400018020703281c0003d06c2811 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 223535044 1250 223533794 223533797
    0x503040b04150c02030903100501052407050604030c06180b1303021219120612020607050c060d05040614071b0c0302090906191811010c0c03060e0f011506 68
    0x111a2510b28007070b9a615442c0039a100118a0188201d0382c050f8007200070122031100b2070465030040007204130242102d00a2041c541c0c810302240c4000010707a01f1b1010706813445e4102c81c1c25801d10722691560350420800711030440004d945100d00c00d0400c0481d10884a2030b030180750703241c3c0c00011150340c0c00d207030700364082c180d54030b160b00400d18502010710802c0001c24800c034040c00c0d1510b50b400801000740450301001010003041a05070441413107030051203a081103840c48085036219840726000e0001c25889991300741c42d6401000e07000c00068940e04018010103510400005291815044c18011200d01240b00789810710400148514039901025a06200410b946811000c0d10302c2d241c034108000195100035013000050b810080b840c540440c00a1103a9245800d25012604908c012000c44042c00540c09142a03241065004600d070041140c40181c1c0604041940d0001c41d04c0f244d060798625402240c24039104c00c6042e0800c1c0d8240b201d0009554448024032914032562940d142c031101c0d9008500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 223536294 1250 223535044 223535063
    0x80f03090c030109060506030c03061003030305220c03030e010c02210a1a01060e010207030305030703021b030c010603112403070212030a0608120703080f0703110406020a150b01050304 81
    0x2080030105000300049280d0042c02080502007a103804006000300300c84240c031034000c180c9420050b0070301241c600d109800c050304101a07d030455800717070010040980240144000914482065850b8a40a01c4d02c1030142915010031807075440c0040c60b8a0f1a02c40303150401801010310401038403582c0000c40b0b940050309a220410311040341c0340e0700c2c00d4807072400030741024107100a060f04480c1030f50809061f2512a650750704003284140c01a41e64101510006001a40402c00609520300c65805041c090106580c13000c003618410001c0c1785182c20101d024003030359540318001c10030002400700300070362880c0030348810600da40c400c0120048450591142c0040520000000d0034a034401e201c903001c603114018046444c0c0c08c01d01c2c14040105075500901d0000d00caa8021450000b4444058460300343d4980d4605500d0f43d5180194440c800016102c5001d05880b100c08030000354022000d40302403e100d40c014101e44400c0d08007950040035000d41c0404007440c11703440701010303644101103039800754115000380c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 223537544 1250 223536294 223536301
    0x110a0f0e04030c06020c030f0403020907030c120509072402010b030606030d0305060409081207030c05090607030c03170c0d060f050d02012003120f0a06060e010f090f0801060f060c080f03 82
    0x4d01070310405001d45400c0c000005c0c00000800411701030002e0320300955002d4143d5445c45070a404903080b0349819404520001d038508825541904882d502c030f40607501303a513401a0740d403011504400c140859507031868040c42107114880e5091040d44503280045008280e10b00304800800d8644104114440815458000060003174540d50481640164030840465444400c924010301082e000d42c2d4140011f03080040062404e44144199a481d01c1d0007401c0717a01e40040c03640e00b0764000402400c104c040c880707940d091a0400c034028500354411065080e103e9038601c02c100f024821204550401c12200c680d120061080b511500a4040c0090b4203080c146100300390340d219509601c05400c0c000780c5038071000030304508010501c40034034000c0e421021a4a0700351203500c8510f09550882c002c0c08000340401011040c1580300701011007202010381065003d00d80c4441c042c0e03000058907002451507a4490030b0821408103480c02e5000140440e10380182c15042540d50f0702c0b418810007000c1c0305c10741e0020010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 223538794 1250 223537544 223537553
    0x150d03020c0a090e060a020a050d0507110a121b050d050f1b0d030c030209030a03140c010203011d071805040207030512090106030b010506070302061918110a0f0e04030c 74
    0x400c000c001000b00514810342e95803101001a06507450300d0100c50045c0703008074800400b180282d480302c0d8041c0d16110b0811226440c01c40061100038142810003c0d07416181302c03070000c02d220850340e040c00382c000c4002c01140020041c10380c1d032601f0b030010481d000c194403140200308089030003038100300c80d454000c2c2c1e5140042161411380c0281c010f01d003889040e41d412480d8004e80081c03890344441a60b12b041c00b2120000300c0c158202d010f00c2030a1a0140c10001c0301c040068030030041100905208100c3c01d080c03902410b10f103801c90b08241c100d010410948030031100011907194042d6070203c101c0c035004211900fa102c1d171801c0700c00c0030304c244c5004640116505041601a00555542008960008070946001403890340a003109110030b941403200e110020455062243c202c41d02103030582c00034465601c50481903003850301e8a9500100043e0f46090403080b281c1c03151441c3c401c06009203008602e080c40305080000414841c0c2c440900c01d0980b80041107460740d00c50600c0c0e030080d012700740701100c241d10b07041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 223540044 1250 223538794 223538803
    0x609030a080a02010609050615070204091506030b0906090f0304140a0e0a0b040606020304060905010e18092512110a0e01060c05010f230c040b0f120906150d0302 71
    0x600030401d103030204194544030760540c480300850724034041c10b204540b1148107020603816215510504008100700800c05820660801d102aa100300da031103010141702c6e50031000311889500116424180d00c0280050f00b1410420325802c1102200580104c5c00155011942c85c03150f031284441c0160303041d444040680e0358441d031000500ca0210502d0700c03417403c2200080240b01c4606030620030780c40c2502c0403030300c80d100006850656006031203170600f0604150055661203400400b1543c0943d03100f035410310134400404402d001e1480c1100410104420581002000c00001160f0207404035010007000103540810010300c3c599080b40707504411030041c102046041c1e1880d000001442141d100003d4441d5000c690441000d0240d070007042003036081c003a00402e445247c2d4901065110400010700300b0100300b038126421002c6a040300303141540c0c86028803100c0d041483d07581840e07440800c102e03260300801080ca942c0119050003900803858203207401d15110b6000c410313a0b4054603100c584070702058000c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 223541294 1250 223540044 223540063
    0x21c0501020a0905040e16090e160305071802030c070308270d0212030f1503160f1d0402010f030506030c2e0503070e010e2706030f07050f060903 64
    0x90007035559808001002c2c0205045101c0d06003c0d6150030341840c541e94001c11140d03e42090320008510041c038006080c405001071346c01090050048030300c04801c1080c02108600158428006410342c1340c0350443d5207074244a03c01442250500400070040c03034000c40412501c543e50b150800480d1502d8052607041c407110f0602580e007a4000182103007140420000d03440100c100b1690848142c50038601c2d40d0350f120702080e6020381144040f034000c1035030250502009016684044c0454000c0340b00c0d080007032800c4210381d205208002001a0034001400361403041c0006101c9407007000b011742840c4c0e000810421a11420b68101942c46021034201c1c0d406125600804ca4002d000d502c050880404103131200c00c0540b140c000c64008110221251400356040da841200d0544806044044c00ca0065408803082c807080d03503220103060360032052240c160001030349001503014040031038581401814a0084607800c50302e51503002000800650303131000394074a2100c01c02e69606841e00e915101282c542031500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 223542544 1250 223541294 223541303
    0x9031b1205011d0f03070f020f090106030b040b1c150f06080717010c090b0a02011d1e0c030c040225081909061202070c0503030318100204060903021c 66
    0x36030103000d01500480b6205090011841c84070748440046651941c4901850030240c00a100510208800d0009180501c0c00917064546035a00e03600050080c0100340c101c100441d990b509010f001d070a051107480480300d001c8e00c230300342c08003103c00200d81c0300b80e91050000d081c1610803110024070910340c0c210440c142c05d03440d424403005450705191921070016001c0c40c0b05507031a5420200c40c1c0300301400340c28100039180d1910a01da90421000340c43c0d030340c07000c1e40001c20756403966850030003240b004c3d500d420502c82486c00340c504071007103107540039080000e0740151700194410040780a85680114280e00b600ca401c5500603a140084601d04214034400c074241d10b58040495200c100340a950802010603095001c0720b25069115078405803180c000c58054000015944008240301c00d08990081c05107a0044c1c0030302c02c81a0b40c81000030b1465008a40d0864206140d0302d00541c2c07901b082041c40342e140d000150660405060142c000c040c55654800a072050074249520032a1032143d076000da9401c0e400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 223543794 1250 223542544 223542569
    0x9020301020a02010606080606090d030c03021212070215010b041203090302030a0302070e0f0702060609090102121602011a060702041d07142b0b090106050d0b04050c010503040309031b 81
    0x902ca01a0003442e86208a90100b441d94000922602d0010101e8552900041401b01029441d03141180c0840c1890001c506600c118648002c0910401c00a001b1541420710404014600054001d08003041040d1400803018441c005214214900d01502d080c1d4040020710550719a1508080312042c011390b00294050040310007840038142c0c0800c02d0410340746406050040c94817491162900020210341160041c2c1210300421a6850f01c43c040b1900020030400160400140c103444142d00b900c1540c0e080d491004800d44001016028002d10126400c5c3c101400210501c0d1000302e0014407030440c0081c8156540c5209004003a4038204248001c4000e600f100c02c202d80f00c0c9103065400031b1003c0322030302c43c500c0900c0c01071840000b000d0041c2403c0c0224a464000209641c4a9481c124050188880380d500e0703810100766a200c18801c0844c00e4080c2010b440c95040c5401c0090400e85840c410b6810460100100404290440c4c01f403411660f05c80c0a5981d0b80c5c2e0800140c4000000c0b40d000482551341c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 223545044 1250 223543794 223543807
    0x1120b0102120f041e12020108040c031208070305070507050712050322030309090b01050d0b03030f0c0c0a091404030c110901060509132d0e0102030f09010c0203030613020d0902030102 81
    0x30004c1c20641e28907440c2036110081281c4890520b6500c0d1003003803106030609001d440154450a04150802d100d488104507003501c1ea80c40a1701100c5c410038410008051004100300b03140c1c580241500102d807828000c1c0b400140d62901e50b103542a900800b070784060001c0d020b10401108000b02d40081c246442c2e465103107842c140c80550412134034801900099186c54020030404501e10075000601d005071034641ca058403041d40c0740094841d100036268103000a10241c00c00510ba4002016946800d80280c0900684401000b041075226008035941d10f140030340369004880003085142d002605410203181c00310081c60003c0055034010000380d0042c0d0b000c0c00008555401a0160051850071600003015001281c1002d044440b0702c0405080c00f08240102180c00200d0440411410b00c035031008101c048108a8813400c1ea4030941c1c2c0c005034070000b0350401040c1c09080c071440600006034800346103103061240011300f0443c2405d800c42102c41c5d0000e184580416580c1c408000154090025500e424 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 223546294 1250 223545044 223545067
    0xf0d05040b040b0105092e0b03010602010606090f03020a0308030405010b0409080901030515010504050f010905030703110a08030a2f0616120608120c0a0c030606170a0201120b010212 80
    0xc00e41d0101c0d02d0f010b003040042514542018031500ca408042d1102c44a0081a1070018141c0140d00200140001c20300020a0360500b580c02103000e029140c0004c281a440c00e00018807031042c9522401d14002c80350001e1006a83d540c071414101d0750050200e60f200e8403241080e074010a03101da461a400f40c07400801000b04008840138200c1150b090b00d0421055030380c0c80c010f5a542c410400003d0010320104400c0c441850010030401e0020018074002c401e042d16030000c0303403401c1c4c5650000d48194241140800a030300d454000301c0064102c55000d10304000001d040640302203030f03e209110301c4c00101003e21200c0d5000c00001c0c1220b1400608403091814945240c40381400340034980c0000460f596480107546000c1d01545003122880340080507401e4020f9032000c05d81e040746503400454064080480c01260603038032254095030040200040070381c6425040981c000c002c002900c1240c10001740c100240c2e1b00020702c5070520780c0691001c1281c14031000101e080151b505021302e2040b40115240f034114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 223547544 1250 223546294 223546313
    0x50106020a230d052a03070203010b06040308030705030414011407020610081207031107030c0e1e1513020a09090b010c0804060302090a0911030405160b0406050f0d0504 74
    0x15010340c154070070403074884002c051144803000350344106030301c0032201c0d05070b092240006200d00d40964080e042e03005400300e0b9400141d00e40300a91800355001140c81d1065287c2846000d195050072540c462030700b440c603910048140002800b00080c80004400101886229031100300d88000c50002004034040084904c1d1100e40e0a55150006104620000701003032901c0f450301050768184001404102010622904140d1002c0c10031020800320782d2200c0c1704e07400100003038005140720b400d22240306810504480c1107401700030003c9802965001204d601101540480340d008801202d907241036000c1980410000143d04407000141c2e84006240c00440391f104104d1411344642070000d0003400241030044071640100640a81411020802040394602075802000f900d90054a10043d45a452600c502224103c805043c400c81c1c001007003004210f0705106200a4071208040041118145100820180603034080c074005e20000060084401105000b5611042c40104051145107041d20b01045d94 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 223548794 1250 223547544 223547563
    0x5040b070b2422020d061d0901060e04060f06050907030204050306090a11010c05010b152809090b1903050f190201050d09110d060204080705060c030a05030c0d05010602 74
    0x98400c00803902460000265001d00200007001c18411654241100003c010340d03400a58640340d0030030808407420501d0141c06c00a101c04c4100b0000d000203030103583e81004004001400d181d140080c24440c00c4564441690815049140050b041303940038500c00c01800c1c04d8002aa0100145c0c08001c81c240e8950010401e0355001d506850741750722072801c0da990b180104e401c02000a604810362080d554400c1000b140c5085c0075030000709148841c480821031111547c0500143d40c00e002410030600b0001100f800103c80010311054412254454010303e04041d0f03004034840c680d2181c01301c00c25551800100000d211a4070903070160780307659103080c0c0da9809030394480c400140941303010105408020601801800e806848443c54408035000b0600100f07805181221503044101100201e9140d4060003407400e84942401640c0354140049a8544005039005a00c910030400c48004c42140c00710a90b814840390b8200113803a40c8580080c11100e0040107440c092091608000064056001511031b01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 223550044 1250 223548794 223548811
    0xa020c0627061807060c08161a0108031306110c010302031806011508130c05130e06070f090b0c070e0c090607030306050f04110a11030c16050901080607120c05040b070b 74
    0x211196988003e40704200c40d05005000910180b008d001e44100c02c02c01d194510f40314a003103428080500341712403940d90080c0c10840240d40b0108a0080e81161503881102030301c02818a29454981c0e82c2e5043c1d620000620840d04058010021075003583c003003003120300c2012011050b00d01c01c0d81c584441a0005c241e00b450800081e10101c045800740c1030006220f4000c1e500301d2a8030400038201824450f030f1144200280b810503a80da031120003141c5061014038001c1e4450369440000e45400c90f0f00600040e4590083c00b50040c0030421040d0b4000b00280c0d800454000d0050354409035100c08503e10180525071482c0e4021000080880800d645a44100140e54080741c05907038003030300d038418407049130041001c0c40a51242040600c1841e40210390803403070307002d60302c007128900700c0e0b107100c80f6042000050b1100d08058a401e0140000d26099003001e0241090100911070b501d0941c1001f8482d107101a07130b0890440c0ea81c1e44200c0c03801d220700f0440b00902040e482942d550905c515100040410860300140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 223551294 1250 223550044 223550053
    0x201030c09261b0d060c050d0207080705010506060901210914030a1103041508040213180201091a040e0c1201031208090106050307090b061b03120a020c06270618 71
    0x201c40310076440c50403601c1c203009003210040d01605d82d02c4e6030041080c007500c502485030038016001200a40c0c0000d06859116404554541d040c91a14509440c0d000e800944512418000e40c14140d038040c5546003101c1d1000c0c002055a4040146e00b4010030850134090440c000b40048109074460000c0109111202c0350340d00c01030301c1101c00c0c00d16101d00640c010800840c031030913008101284140395040d000307400201010001c00c030a2040b0400c45180380c0c5110012400d2840311015581c01031402c20080c00b03950743c12010031f42c845070f0703402041c0318602580c062070541c2c102085010300190300b500c0d20490025062011540c590600d409030440c1400e0090000b0391041c002000c00d14103008140440700d014009200386401c2c070300500068000d1070750040d000075042c030400c10003a80d80001001c101c0050406513030390708141152019000c4004004446840c010404070b262002c000500d04e41c02481d5540d10080c03045510044e0030400f03200300554425125007070510090b02d050005400d240d134164405c0740c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 223552544 1250 223551294 223551313
    0xe070c02120c13020d1404060b0a09022d070b0c1b190b07021f050103120503010e190e010f0e07051002070b0f0c030c01052406070201030c0926 63
    0x40c0d49200100a80b074005403c0000c1482c0d0416513005801c50950f6400f000c14110071242105d030402c3c0c012a000e440c820344501c083c0a503810412900c0d00580781020307096160811080068946580c007203500c4130140d071510465120040828269030108d580300c4609080c50525424030362542c0c0110724000c4528018072750800424500140a541c00305040d8411105642d1986642c66411f100070f001070151701500841c0c4030000c000583c884110054004001007550641c02c200e064194061010743c103002041005102e10702000200e00c0c1d0103803e4a2064506500d1044101302405440c00c41414540c00c003e0720303201c2d1881c642c01c22004e103041a0202c84056503500c2c10041e0100d0b1400780c800268102e4401480b40006800042c06912141582c1c43c2c60a42e503407004510395031100f142c0c5400ca0f50b68a05201280c88524504070b48030709810080f0141c0c1c03070380c1400034960f4400d5210090505655042003802c603070240000800400840c500500b81c00382040c412002c401c002121030880380504d8555 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 223553794 1250 223552544 223552579
    0x12010b070b0c07120e01031b0c0c051005040311030a0f0f17161e021f090906031101081305060703090605060307120b1b0f0c0d03050402060a12060e070c02 68
    0x9881d0504d40010050b14a0031010200751160590304200c2070405448080c507004841006040e1401e50905070b80300303404810b1905040d5007610058020a105002c81c41001800c9540602079406582d0440640b00071762a0302d90000b46450b011307460090043d91244a410240040c52010488060042240300e05020144005402c5446502007490781200500c5c0040c010a2501a141c1c0d01440394012300050b8112940014036108004005002411803280704400d490394480401001041e0703144043c00710f01c0c11956021090142c1c003682c01c0c100f140c0d0100190220704020920310f481c1c0d8100081c5c0b1300504055000401a10300004203850050500d40891454100099100100d812002c81400c0318103255a6014010501600c45a4100203000a50380c1651b0b0441c0240a8500105081981c52904514403400c0240340224001810303d40802c00001da124001101c800300d1071440c0024160f484110414020030240e04601c42c1601c03242d04110030b00c0d800180c1c000e01140200d0b0304e040071103900140f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 223555044 1250 223553794 223553797
    0x40e100512010b21010e0a12020f030415050901050d060b0a0912020d060207020111010c02010606080a1401140102070b07050106060e03030307090923070206010603050c040608150612010b070b0c 85
    0x62240c110020b0660705882c13102c5209902003055100c1c1c00495401201151145400365404050b902d4030160214881d0090f01009030616041d101c20155090502e4040f03000c0c0c005607a0000d8006024000610350803613072190048500544801e403040181a0301c036000c03507603550408440c010106008010202d1682503000a0820641d401000140306035041c0d564500a0341000d04224144401c03030200c0e5550090078018242241c5a41d80001503192030700300e000703140400160074410403520b0240181c4c40409810f10316815203803600300d503050107088580100d18101496000117861100410305004110f0190011001c440b0316585415541201004140d02e82c80181e841401044446104102190180d001240034010000005011b400b1003000a03003803a20031140a0010303003042c001401481d03010303c2299042808500e403942800e04010300540001c8000c0c00c000840b070301d2070b40380c0c0420782d0305d0740c0844403d20303601c17480300904c3c1d69110000d258a0308980d030b04590648411b000180381450240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 223556294 1250 223555044 223555061
    0x10507120207210203040b120f010b0702060d0e0f03131401030b01020a03030c0c06050c0703031a0a0519081501081b06030105060904060e0702030c070f050306040b0705040e10051201 80
    0x2590403c01078841040c42e060032452186503001c2d40401d100026100021001030071190740b50340d200001c2c515001c40004e00c04501600500303050a802c3c0403400142c0c035603000791600c1c81e4030004001943c107450400145040d2070131000d08103d00c8001880c00c1011005030301d440456401030036546500780000700540c103139070581c40c2d5240140d11802c0c011010a1090300a0300551500e405e003064218840d03140c2e00b045c0c82080701c8084420b0300000c3ca181c20554903110320b4003a80301c04c0e40540c0990000400040c0c4114852060310b100d118000740d0030030120b203100c000600038815903088503051700325001c81200c945006d21a8107114080c0c048040c49201c443d03080d86080c018010803841c80d50303081000704a02504207181c000e400a669400201d90002d0155840d80544c0d9030344c000b551138030b19614500c0e1030000940c05c48070307000d8400c0c6400c12094a00182c240e800551040318904296076940045900e40a240d01000d15202c0d11018001100c682035416000d85505440d0040c4c005003000c1c1c5c1500b40c480c0c00c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 223557544 1250 223556294 223556303
    0xa14070807081e130303020d170a0b1807030b090907141e0406060509041815050705210109050f090a1202070503030d0b0a17031210030212010507120207 67
    0x1007000d480080c8800e00280061881501c0070303008006880703048003040c0c0041c0501d0184148102d0240141601002030500785002490013021488103482c0c0c00000582c0a4851720496484d040e00b29001d948510a60703407540401c4907856841e02d07025038010046e0541c20b02c554010444d10001c9032410381c000ca080c0040d101603040c1e540070741104200b480348080404c0651401e0a0301e6828442ea1543ca038001c0d00300030150390f511b00d512402e00404000840c0c00204254421103140480180003c2202e41d410000c90303c030000005056440e10802d030340320700c50340204812040d42c45100c4541c1c1d0060070b580d941070314400700707041160340c3e500c40c1a42804081691843c401e130780400e82c440c000660715003440080341ca1030710684200d9540c880201c2d1850f0003480481d0121070b118017100710a403c2c044486070050415a040c00f4048017010403507904ca01c6a200f0849100007000700003002c46070980110002158060003001c840f40100380c046000f44001d8030400d001442c000705040352200c45000b40d03085c16800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 223558794 1250 223557544 223557547
    0xc0518071d06041d180a05150403050f041206050f130f06020d0606030f0b0303480109140c01050a0810170f010b01050f030105060304150e030a140708 66
    0x1261107140e1004003100075444030080201281485003540b400d41580d1030f204030380c29a41006200d5005c0c1340442d2500d024142c1c844041100402d20001c1c5603140c0c003019200d100b081c3d441d9403d080340c1a10903030000c52140003000800081b0030100c0c41594120710f020362400c021b80d03165522000042e60050356034144030310043c19070001013060301c200c1d110043e225076401850003a01c44841000d548480c3d201c080401c3d92840758076010001070141c400f1110007140036626101e213042540e10003c0400b008100a481c804401d03450f58030003000d4240c80c9180380708260003032180440401d0b0280186e10b000321007083c0c0307007032054101403000510ba4207a500140c40301828055100f6040306c00c0f610051201c1c00342c1080b000c0c00a1a040484400d00d80043d46502604804209410480c00d450f510350301e00341006020400c01030b202c0e00c03400689040d0340084588503901e490364104801c4481f8140300d00c80c4000d240c4005440f10380e41c0007008049103d425250007041c2417040c0c6107207419002e6414050700e0b2100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 223560044 1250 223558794 223558817
    0x1350907080111030f06010914060a170a060513020a020d050309010603020306101e0302010806010c02010c1704052706040c0c06050c041a03150f150a02070911090d110f0d0c051807 79
    0x20040302400f03805106161108040301c48202c0d00c331003a402503a071340c040155101402e01c40d60515080c0b51002031100181507190417000c000095403825094084400c015010004c5000488207410050003540c004040320900d09007200c019000130020710452100e04a8500c08640482c0d14140d03403021641c0585400e4044d40e500401900d0008090743c08030304000f6103055541c009607180c1080541d803806681003944584c1000240f20b1000c2204070098050101010400e020720f4141c0101030303002405032000b2541e400c0d01001030321410b0182c5c1008182c58105410001261400c00c003078400c45403400420801c0c008041100c1d04030b8030040d201c0c2c0320f01240000d060310241c100707101014040c440c09400b84c003c4042899400c04260494000b070801600200c0082000503180d0180382c0e82c1c02418044549030807004c40008500e00c920900c000d0420014101079102e03540c80480b071404552010b8528002001c1c41d00d00703049159100d00459106176090000329403480080c043d440d00c86e942903100c078010b100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 223561151 1107 223560044 223560049
    0x120222091a0d050c22020c010b0f0d030903021c0f08030f070908060a150b0a1101180f080c01062301350907080111030f06010914 57
    0x400440c0d514086400850700c413403e030720201d40000500c130030940228456074009201c61409803021401c00710400040d040b50082c00781c100d680443d418200d0f000c116000f030b402c00740680010b00b410420300040c00d107844455031868140c100c0d403500d03811541d1807003504610900d048400d0b41010041c40b40d400e004030650341d00148a400c1c00c02d040750031f0032050b42e5140402000c0b64030b0140c80d45840d00d00480c03000712140161101d02081a0360320b00780d503805083c00e040745140300b560350301e000e01c100151441500e802c0c0905600103503031288480135071074207111500f02041c00f0240d0355840100090040c2c15080b0348840d8100b400d0403001440d0890009000d103040c940d0300d410030b070b515000000d40c941c840c0300340c0641031840640060016102d5200862400001740c012030b116628080000002c0003e0b100031318440c01c0148213040301550b4103401100c550015114448401c0700001c111401032 = true := by decide +kernel

theorem cover : BRFrame.Cov 223381294 223561151 := by
  have h0 := BRFrame.cov_init 223381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 223381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 223381294 ≤ n) (h2 : n < 223561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
