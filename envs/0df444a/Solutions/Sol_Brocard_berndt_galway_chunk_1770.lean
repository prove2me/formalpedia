-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1770
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:36:36.474976+00:00
-- url     : https://prove2.me/submissions/33960100-5349-4588-90a6-8754037476b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 318165467 ≤ n < 318345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 318166717 1250 318165467 318165487
    0x31506100905010807080601260906250507020103060b040905040303110301081207150504050319090302010507020622060e030105060a0b120c0d0213060f090821040909060203060a0605070206 84
    0x2138281d000e030040c9411142125a1521071284049e207000540401e4120010040c0b074010402401ea440710305000c03103c80d00d50304401102e000600b0700c1020006c000c000070b030090969001350005401000c6181c0c1c200d0781c41d41d40351014401464242c80c1200068100055502c014080c28113686c1a2521940984100504c0600060300d40d8002d031011a106102c0003004001a0b441b8440e00e88150b00540103941cac0c80a5801640c901250301075009400d0004240c014400750340e0180c03c0d00c1c8510ba05030f450030b46e5504d02900c14506c0301c5a03080c030002e40c1124454082030140d030103045642d182205500078040e41d101c0604206003c006400b903c42040401d1206104c058001c40d4400d820400d01a681c0d0300e05180c80c04950140c1e407105061981000c02c140c02009155400311550b00c5088951a100040c01e0400c680310b034035096030145c0700114a507440000c1205118903001c9030300800c0c00c1402040000d00340c0c079118020b50000c4510340e10030740090070002500d42c007420480304144d5004161900d4072450030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 318167967 1250 318166717 318166727
    0x3060b0301061d03030a0c03111204030b0405150423062a040e010b04030b07020f060f22060905060108030c191e060608010c020a0809120c031506100905010807 70
    0x20250070820340341015081c03e030703842c00d000070224a0210368424030318002c40d05024240d824035122036002548500c0324003c1460956040d641600e03842200301c001e940396802c04034a40b0419100e810700e50000d100c240300c10410003440c200364021101502c0030902a030b89240c0c5407104000c458401c07240c0807043c09440300c4003851608400c44510b61044604107034448903e080001001d800c40c6000180000d828414440716001ca1a80b01405100400b5030100307091086845000c060300c1d0000c408041e40c0070032040050b070303111500c401d050883c0d460480940341c00d1102c0500b42108064401c0d018403000825221000f0044400c0003200500401020302c0b00502091a641c003644142c4404210140c442d020450202c203100046018480100d851801c006a5508640d0b641c0042c0055521000c010000221030b00c040e130750020000c07a03000c2c03000d0b03074a42c81e51410300241c8550181d06005040240c0c60f4600b007445140d01460041e42c421340510303100c0100380c4111405004841c045400c0a0018040c94410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 318169217 1250 318167967 318167987
    0x5010e0f01090b03090718050c18120a0506060a150203040b0c01110706021306030b0112020306060903010e1c02030301030309180b030106060509010815090708150901030609110103060b030106 84
    0x40c0350036902d066442c0341044198105403548462600114000c000c80401401801d01d1161190b0040045007000000010144a55400502d0085880055221950340c0d0f4141e1400c107804481a5011351320203140450f00c9102c100c400510990f503484011a4150503160020040c26842e00158a0303d41044000101a04100386446c0305e907484080f06000c00d14140041c181c0e6a100703080c0503032202c6001c0c3d0ba0f499005a1900400101490711071140c14580c0e20030015201c81028080059490305c034030b00030803443d01c80c18501f40d4040d0300f030156030041c0d810001004816210b044440040c05e41e240001282c4a11081c40040c00140c1d00d190241318424402c050320700301d20404240083d0181d04140481c2c2941c03101c0d0300200c0070074401b040007041941c101044036440507041c800300010100c80c400044c0420809484401000210070004101c1c81001c1e650f91050700300100010100e60307503440c29034040c1c007460204070b500f0034503121400307070310350190040c41d003078401c04243c0e9820350782001802c460042030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 318170467 1250 318169217 318169219
    0x71206171e030c010c0c060e0f07060c02150307081f030308070806030f0a030f17040c030b10031b090b09150f030a0206040b0408010c2c150d0605090603010605010e0f 73
    0x2040b20035243c450901c103958080c0f425407550800315030030742802c20489550000c40741c3c2d1a000f010f144c0381a2200490000181d03035040c14040c00f1810240013142d06420841c9241e1118280082440b82554202451a10601040e120b5040200b00400100608480342c807009021800440c04a488107000d01905540000090125005401003200c0d0501d4040c3c15003003a400b0500d04620754a080e944180c101c082d074600d210003444141001e07503414040c000c01d844098130400402003c143d2a1a50700c610000846d00715a208015010111011049090314400d50404c0b0b0300c1c2120021307543c180041540d114000b804001c9100209100c18004041c0c1e40144480d80b5015800c81e0500590f96040948068000c0501a50f01c0f182002d1803c5d00711940010b510f0305100c03401c0301622101d03441c001c0c041d95160340780041e0300c50001c02d100401d8400382c40100503e00c1d5880400e0703003c40904c090b4009400c84108690308440b5458030030915080302d41d64029903000402121554009040c00d9402c0c000e600d034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 318171717 1250 318170467 318170473
    0xb030a091106070f020a140d06110c030301061e0305010b03131529060c071503060b0f180405060a03060203060f0607031709060f150d05010203071206171e 68
    0x100c0c400024005a1100b40304544150745041c44c0c10030743c10b2180545015100801d814000002d00200203038101c0c520341402060280c880f06843c80c2c0c0c00c030740000c1e50b113a1140031007200c1d280d50b10760b480a00005010480301c0c01c45c2e521824048440c0f4800d010300d504031900c04000d103141d81c80d1840d14829800c00c200050b903000c0c201e445000051550752160001d504001129982e401d804008860200786d41489807912800c0d080c032181c607002c036000c54044200c0703d042048103609017200d003081d00130f040303540e000c14040440407525a0742c201c0b40000904c2c1a5104110b80481900010100310031141d068441c1600105000307824800101c3d03135801950814401082a903a00e01c0e1040092015400610218005003810701001d4400c0d500740e80141d0890b2462018140604c0c003003c071401c02440040804001040d0740e0945c0380c15403100351a011603560040700955403445c000c00007030310001e81c0d2541c0d45a03240c60071300001030401599040300301699036140034108560040c21a82a613049404040d50140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 318172967 1250 318171717 318171743
    0x6021c1d040b0a1e170c01020606010c030e130504050115060207061103091e01140304021c0f121d0d02092d0411040b0618151213060b0102070b030a09 66
    0x449003620003070704460411481c003100390410f8200554400f05e001c160b41640d001c0ca408004507a000300d501e80d401030003803900480000c024142201c092400c41c1d9110f40120080141d10010204ca800c5a84103c0c043c200070302c101a1040c10044648069125010043e08611b6050106512032605621190400750440e0704003a14040010840c004403d00d4a801c034a90000442d40d80d6006070000c00c1d0401e0b100c03081c5065181c20340205d8020741e265010003540719900307421001042902c403243c0800f00e03000024003002d062034000161501d0781c3e060341082c0c0030100010b850704628000c010340c0c0c20180d01030546601c0741c507072a05842c4e1101d0b0403a01c5200e035071203d9801c4610030404a045a102c1d038004c00c0e01d581204603042c144021503003001d2505018010812941010940f206101443c40502b45c0d240e85801c0170f01c4190109034050000e140011000c01c0c0d0520402c1c4002505103d40140a51010440c1e00d120000680e582c1da99845500d500510900002d203040c100c6032303c002c09040c0103038104c100c07103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 318174217 1250 318172967 318172979
    0xf140613020307020106050423010b040b070b04060e01150501080105030a03140903012901090905060904030c020303090d06051005100f050a0e180708090d02250f06021c1d040b0a 78
    0x285a01a201802704509081041d00c0c0404100019005140c094583c91038103050054503c858410460040c0000074144003240401429921035202c500c41c11000308405140c030300c0e081410307441611450b4006408800045000c3c40c001c070308003010070341c0b54980d44000852100244420342141c64159410b55991a01c44c00c441400030307803d0b00c1c100c0d024034a002c05011100c00500300c50300542140f40b403240381c5401c000c02034072465885508150182000c0c000605940b001910398850032005603000303c059030340700c806c01c0f0003504018082c500000c51404100d8580b030900c11503071224880d08002400c045150581d16004030010302c0099007505d40380340c4900110002c100350501035104e25a035666060100601c1903481012540c12070031000c0075145450700640700039a9001819008002d580046040b80c0003c0d214400400007400ea982443c455165283c034040c3d06c0340070a22500441203079405c0c02e030700101d1150703543c140c0d651483c454201042c110300d4140401031581d03528a070b40141d400e00d4003242d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 318175467 1250 318174217 318174221
    0x1608040c03021818070302061c0902120102070311060403050717040306060e09010e0f0304140120010506010f0201021204122106260618160303030f1406130203070201060504 76
    0x122034000c981100506046164040484c0100003000c00758000c19014801655050111344141e11468020040e1120a01c1d0a42c0200385280009500c40c2c044585000d41000c19000b03024141c0c002d40b00c02c964002d5850b4074035240e54040301e0080000303104112000c0000e1100c0d6521211018a5100750f05058480d6140302c11030b0410741107001e104500b401001034110003405545500109140030f000d0b007501a00c400366070780c0154000c84884032034488211200344d10650f51401d4803964507890a288802d9480800e0080c0300c15175490b4006804080c4610109005000711090391254003032280d200d0780c87e41c8400d9403030b0340d001030a282000a2444064a0400e20000e003c0343d4a0820000140c09072820f00c2550349800d4011546191640e42c0100e410700102c0403940c81d9200280010701c1d100098159800750800c41c001c03c541c0200301041c4404011326070325900c8600510aa49070400550329040540c050b001411143c1d258400102900d421070b401d2950040c42c0c001007103000104416442c0c00010341 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 318176717 1250 318175467 318175489
    0x11060f0d0905060406180210120e0111070c060c080405040f0b060328230a021b0c0a0b04050913050f071811090d1b0f0b03060f01081608040c0302 64
    0x1906030301c030009110500070541b081949081c07426080e1500d4014560100d041c1c4141401c0d83c00500244544480010540b5003052a5078200503000304441d0211103540207654100a105070340c00001148040707a10b030b0140304607183c1c181e00221441d040030319100412000e40070400d01d10708032a807502d240d4691a26000003550088008002c41030307085038144204030b0907030055180300030795504050100408642e10601c1e0a060160101004040e903600c0c554003010317104102c514452083c03001f03442c0b800400081840208050210340b00a0030341e55800540441f405136000b030b1039200c55050080340324004513241203000705100e0015070b543c0070f03c800400c505114907a80401005050f601d034184061009100c1c14081000303084016007031440a4010400010305520003d0404812211400c005c0c0702c64051039005040c0e020042d80310310749070200055141c0040c2d40e00340c00b030009152210215801010120f10a205111060b030a42d2145d20003240d0b1700801410959402c000e10001002507185d075541e0407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 318177967 1250 318176717 318176723
    0xf09010311070f02120606010c02120703080418060b130905280c17090a0b0711060c0a0201140106050a0507060e1203060a0e0415020304140d020c01110a11060f0d09 72
    0x2030b244560741d0061140c00170300c80980010076004441000384981e002200440d080e84c05131521151500008081c51501015030409040360b0b002103000101155408503008211034800703410700c80c481e6161003401e001d000700441282290380f486406c2c003c06410354806644903000c00300c00c548034201e19190242642070301c00d0410b0019250700a07110705907004906040700c05911412440c241ca022031001c2c0c0c862144940003041200c4960200f50400e2042000c450004071004c29901c25007030000008045030300c10f402031005942844548985078900c000c046048641ca519220301e4148000c100721021780c4940002c50340c040c1c1c1d40e008140c3d0076008100b0b00280340d992001d140c0c3d90381030500c204902c03159285d0283c2140000501003100040c041d5400301101c0421a002584948030b03440c01e00c0c0080000c040322891407003070804e810020b907030000e03043d15008000e0320f9075022090301003109921045032179000b070403d509a8903840240d041610042c2120525030050303909104030700b010b81c0d003a82e52a82040e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 318179217 1250 318177967 318177983
    0xf05031c0302070204060b1806030f010512030c0f0610090504050c01050a11010f0902150a050403030e0d061e060b040521070b030705070c06030615080601210f0b04020901050f0901031107 82
    0x151030003542380400010042c102e0703406007145859404ca00585005001c1d03035008102e5100c41000c011410401e48008240007015100c030364039885840b82c0c3d940011540402c0891075640d002541807100c0c85158011501300010b0f1115000c010019141503010b42c400c2420000c08407844001300d54207101d10ba40700d0768124000301d330580c058010015501d118040000100b9001c01014203095000411141201da050504500784141c682c00200c03525404680904503138100748540c1c1c110a80700f10729550400f0000400c00c40550ac40b54440b4481c002c50051907001385128490303070002104101003c4800c1d08580c2103840558540110180d10f03041500c600003c51804038080c02003001e401c0415000e000245403c1240c03900d40200c0948680c1089120b0b4148134959020a103281d20a01403070584201c00b49003c81c10a6101c404c1000925240003800407061501758054150b14090085540c0720005a4655041c40c000d0000704206030f21000003e8181a9600d05034205414400050b2000d07502032290 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 318180467 1250 318179217 318179227
    0x190e0c040c09330905090a050a02090603010801020909071d010e0310150f090c0804030e120304061713020102152208210103020901120609080f030603070f05031c0302070204060b 78
    0xc0d0070f0200d4802529070080c01014241030042d51075507981c4c01d603c0712101d40049010b449481d241c1c0000d1060b5030710350b50410070002c0086040e04054004218100050361714540c150360328107044441c0300400e1a5502c25507240b610b86902503101d80000c00e107010004040e6403201c02c0702800f00701282e2803400b90550301009410308000c440715044110380141824003090109203a441c030000c000c102c000300010706002e5102607044403611f0703694100c81c465072070b0011280e940d502c40c034000e490840001017108005101200241c0000c1001d0541c10300d80350b040c1c00504002805190040050000511580480583d00141d12450b0710440c402000d56005041c03803980d900341d81ca0041b604101d9603408880a5000358010030060b140d2881250440703081443c103550940803490080c0c043c00e04200042e184110114281e20300c40500d00c004c5005240440c203c50501d640e415108107580074501c18941e05801407056020309020500d0000d1641c4041d20300186409443e5000074102da00c9500111100440410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 318181717 1250 318180467 318180539
    0x30c0a03020f10060806070503250e041d030301151b08030f090c0a060e0301020c100605270c03280903021009110f0402071406190e0c040c09 62
    0xf18031060a40032003003d0100c5420107103401c1d51203102900394003c104d00040020200304e82031641c0048602d0b0200c680000c0c2004c924001e054147d003008440c4958580035400c1e4015103014030342c005075841074002d14116803074048a81020031a5000d007506224045001c1d5285103260b20300042d4940c07107401e4403510390400c840700c6226040700030801d40d6264400b140c1c2c0521540c60842d088104d4100386460021142d0700310120340a8003420210300002c0c40b5805c0c03a12000600da81100c01910302c141e0350700d4000040520184107601e070740000501000b02400104200c021202c0c02150f112281c00c55034401060044201c1c50000000301d4000e0340d050b52a80782004150381031000d01a6900d00b4603050001500da034840c40c0d190803100d4003492144080100e8aaa5519a60180c070f4046030055500f641686249400310b468940c1120070701c480c00352500c0081907076003043c400c03c0e5a100b8500c0c0109400024081480700809544400605002c2031280000b8060942004015400166000080710030300d448 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 318182967 1250 318181717 318181723
    0x60f0103090803040515070518130e01020a0c12080606030c0d0603020a0303050c0106051f12142a12010315110a050403051c30090b041b080c0f0102030c0a03020f 71
    0x903281c0008c1207001c0080d5002c840080c003003009000c0d0300b215510b5203941d41407030300d100500c0000408403c550011425001c09500500f0440c40b0340d0143c1d40204283d180420121140311040b80c403140d0000051011649a02c0b50350301815a0540780c0324006603481c1c51741c000900400c0303035030b004800060b40016065054182070094500812066806c01e00c1a56094624214840780c2c16412007000f00c1c9940c411280800743c0c00001d1050220014440d440c140b0310109040c14800e0307400075142510403807003d5034143c601c1d011600300744900540b042481c0d0855039548414150003480c400c105858103820603219418000528002000e5180c50307984a1961034520b017044041c2c005e00f00c2e406110303003231154010340001306c03001405181d00a86207098921803010ba80440020358011300c1603e0480b4500800100d5403100f0700850050080780021080300c2090014401d4138003403800c0c10307000360503450054140485954002801401038074103021613900c0051828030204002e80060740000c1c00e141c1c01050034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 318184217 1250 318182967 318182971
    0x91103041b03030503060609030c04110903060c0a050702011d041103060a080703350a0801260d03020904140c2805121009050403080a050109090b060f0103090803040515 74
    0x180c00300c0c244182c91503c026245000040c05140240000207100c05665414485c90640c8140180304200840502c03900510750f400803070585000e446210080b0703c003050703060291001a01196a420300d48010795004446148901c48012284010285800d0443d52180200d00d4141d81c0c100002d6203c3c540903040062402155000340e03800d420900003072010070a00c0c4540450000510400050342c0e10f0014020480d071005d6003484400d175004548007030207030f0340306200b14100c3c1e07030100324030b1840f01980140001c0d0218912902015500040359400360700c0c000d401030725a1500c014000116188005441070034054219844560783d0383c0010520001c110a1901c000c0c803d6010242140f81d0300704940c040c206d4419440107051b1051000002030a500b00142400042c3c144200280154103041ca0b01600328101910b0f03120606080100109051005124000c80290004140059621001c1c144542c1c8101c0d068181d0405446038201c40225200600440c01903208000800700c100303142085404403000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 318185467 1250 318184217 318184253
    0x14030f090106140306011211130b1e090406090305190207030501060e06060708070c0506070605040605070809030f090406050604030b010801150e0f07020c030d030e071508070c03020709110304 84
    0x3c0f03940440c41d1038500007403880c15100d0101094038034200c6424003001c804642840581d11603040780c59200388080032341007032030203036415500e6485651030300e0380c000740300a84003d80319040800d060005010070619080680c1e554080d0500610301200310310081030b96816079150786c02503840031500b002048400d00c070b11001082658000440303070400381d000580b14803d21801500074007010900c041400310942650b0002c01004004130340c0d903845440c20001400c000c907800d075086460840050b0303402c1d001e04282842402104042c0d4078040301c002d00a9100c0e040580b419030030554402d0049020344803c00184061800b03a803504681d50324040644d429607030510250202250382c0002042842042e081d03854000e07401c180f000e500c1d80e481c048200c1c901040c62082c240c0c14498030004640d0070b500743d40710014007141501500d80040d11860039051000e0f08060801c001100311b800191207510403590010b50707621a10503500f125548030844819204019003002e5524400004c1c041000000710b07925925041c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 318186717 1250 318185467 318185489
    0x1d0a05090c010f0905060301030f1e170a0c0206030103030206010305070603021903052a0a0306270903020a0501051906171f0b0307090e060906040c031214030f090106 73
    0xd4000c000c161580319812006041c400d05400b4501150300603810034020b044041e140684a60352070404c02e8081030760b80b2046d150b810117402c0d82c08800d0301c5d40400060141d04110140c80c030040140c9480d16552003203085008000e0b0101000c3e0060396000000c40c0218002d2340104210b50545c2092404c4c0b0899600940500d8810054600b8020000d21506400c0b00181800a116550129041c0440d186110060a4059518022031204640b2000380c44c0c0300c40d543c0d0b02000499214080500d51584e0400e40040a1052100c000d814030000c1d0070294905100c1c0c4191094202d42d07503201801d481041d40d000c001c1c0a24824130444816240c41000020425040a6402480790382c50301a00c03100e1040c003d01109400800c01220036400d604500985e690243c100c68000e90750700c074104000d000020030b09206018074004542e40c3c1c9400100a4011504451440c60044c51030b0340d920200c02215601006008580e9800140c081c0b940000d14810420391010241d149004507466003121059000070b18048 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 318187967 1250 318186717 318186721
    0xd060b0a091203230904020a0309060c0203040e0402060c030c19060c08010b120a02130605030103020906040b1e0d0b0906070807031104050919180b060d120e01090f1d0a05 75
    0x10313074000c030a00464203032104985490844141010907030321540f0007954000c2c0c00082c9486005600d980140c0106001c0d0004000d25800080c3c12622446644219162040050041000352030310800034020000002d00701d86c0b502c40c0500c1e4107801c001003180501c5160310003100c01014040680070b221016103e03858009010740c10601a46194022400000c3c8480780c604000341d1401420741c122080840c0059010200599402005000380d00c01d0000301d00506a000104807141428061606688001003d50300c025000d10182019a14003c4420307a000c4840354020002c15800c490090040581e030001e0003c6150004016280c244081c1002d402c240c80e095040200406400aa40c1a40c3c0111000c41e034a44442950604030540102c1d5100124500200c030f83c46a900120b400030418490340e10311b810b9a8400080194100d01c0c10405001c981e12121030000355880381040401081d814142021003c0e00c0e1246803c1e201480c1d044002d0074102e100f01e04400841146a050b40090214000d100394 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 318189217 1250 318187967 318187973
    0x7230105101d1909063e030411060d0f0f02190206090613030e0303040f2c01050f0d06050403080702010f06030f121205071d010807020a020609060d060b0a0912 70
    0x480f032000410254a03590f00f00e0303400f00141504500245c0700c80064000311014204104c07200c00030340006480403001281c00120348515203900780c0b4440e41e00045409100103162007400020340c00320704150070b4107581e20880450b021032071151035040f0001c00d40060b200c2400070940e18090044460005c00e5600130780401104810004001e540443d4887c681650340c45a4030702914012034a911165040c0008600490103001d0705c501c00080703917001002d81c9440c1449d00a5400103000a07000d01581e404228014006070400c0c48951030054000741100f04107070b207262202d000300d034000e80301100015050800d0020407a8240903a402c1c000a00c041003040c0392a5607174101c410300e56514000c02d2400c01600382ca14250044044099002d00004140b0a625100380000c081291402c0d101900c2004481e10061551060031080d101e9101c5e030f00242901805602084901c0d0803014100d98803040400060450290b580114001081d1841c0c03d951201002440504840402c0e04440c0442040c4840c40008c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 318190467 1250 318189217 318189241
    0x90e07140f09160306030203030f03090d050f0f130302030a030e03070506040803041a220302010f0302121306020f04030507050f060a1704020a0e04120f020105060607230105101d 78
    0x1c1000700302d855055259000060b001740c942a40702a6140c0800f08028a640f960f500042d84204408001d6450541d0100d405a800b80134488101210135403d1001d12411448080100301100c3c541c00c1b030b50000380d0382c1d41c0060f14010b0300b0380342100000c0303003144c0c076a0303c505003001600082c0200311140c82c103250415500659a01540c410103034003043e02d140c0040d80d014024100e80f681310f020900e206547c0c8844261142050107031104034001041240c401421a11902c241e80316a168444610300c41e03210400400c54214040100740c402700d5081158000444144005100951040001c5e0140b0791400c1d04110301c0c0c08802d00e4050081000b045160100f0742e002132050500300000789496541e0300d80e030000c90f20f005415080b24007205c4620b400c3c07205000296486400001086c0d8039100400300c1003004a007641d0b01a181e0755042041800303c0400181aa1068102e560382e04010b42c0340309209e81d291509465080c0c4810307030407120400d0309002d5200a81501041c076042c244041c09542400c003c0c07020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 318191717 1250 318190467 318190471
    0x608030a0c03050d090b040507080f01140406050702100c020d0806040e03092b0803160c0506070c080d050a0e1605030a021521071112160309090e07140f09 68
    0x1044070008a29031000c1c41d51703018000054200b941c0305030740d03e41480d1040c0d8a03103640c02200c0c1c052040c06101802c0b048140185020250b902d090301c3c459407210f075544070240c10040c0c002410f6004400401030041e181e0300ca11008290240c3c000c100c0030010341c501400360080605844e020b80d0801c0702c62071070180c001044800c04981501e01d4000b0303900c1c08003200d16511142010301000006007012906104050010354000c1d8001880b800f003c0c40362200650f1240f02c4201d009260f0303080340d4001184540103c5940c0001800343c40d042d481c0c080070304da07244215402200d000f070295076078400c0b04020000821842c801c20f141e2090000845003070200003542c0780f0305e058000f07105001240800d8030000507601503d8288900002c10544841902410768a0305000c6440e80002100c1c40d001d841010400503124910040f02c4a94070b00c1d0020440500328020000e640507010302a070480d00045020151141040c0c41d032022016187d00c1e400d05003220303105044420064802c101ea00c6079081c8550750325008507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 318192967 1250 318191717 318191723
    0x92109030706052803020403030311030907060e010c02030a0501140c0f03010504020a0c050d03141e0103170c060108060105031b0102030306130b03010c17070203252409060608030a0c 80
    0x25454041c04100720b00903011251110b52131411442e4260613064140d000b50054a20944003400700c8289020003180601044038110207503809862700700083d90140240d0403800c10706140510880c842900840e140210541088a143e0341d560002060380300c299240c1d0b0b4209000c240b449203041d0040d403403000640010300034240300b90b80c000780301d9480c0c0707020b41e06140180340d105040d103417005170544d0094000c2000d100d901d81c2240740314000403041050300041c40050544401449420b0b4250b865410540d42d0301e00540106610401c0404c0700800200107907802403103c01c6c000c1070998100340c180341c00d00943c41d550014501c5070204121240ea00882506e80c4160140d8080c0c001074001e52559024101d000d080ba03415518001e64020450791090858102425004a00103151038064017240e89118000044140a10007005440740c0d81108030704032101170180250a891040c081a52440600340440c080075450307544986c0c00c1006407d009460041c0381c03d00146080010041000c0d1417103049003001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 318194217 1250 318192967 318192977
    0x30402130b1e130507080901060b0a0f180906030c1508060d020f030703150209040b030604020306040b0c071509031b020109120512040f0f09020306010e0f010302090306092109030706 80
    0x24120589514140c4082c2c0040c080f000d0229040540c4083d022800a071460200ea509000d001710b41c254028003101c0015400703507561209060345070310072a90300c007100803604266a104080010754000d90700610025500480400038080d1900344c0c200c61501c4200100b03014008003508105a1399113060850070401e4069034162542e2004000103801d02445400007010b46c801c0b640950420ba49581c003500d0004401e4504000301280c481c1019500d0707004079002541075001d1400140020036407891240c101a0201c040b60500f0196130703c1c0c02d450f40c4820314450140b551001d04105144e44042d0307882218007950800340500f003064000908042860260341210040c007451041009004c00207100a03a00c1c80007c4c50710b590b01c501151004030b07098403540c00304892250000c583c00741c46108407130040074140c40b611581c0015000f8010361205140c0c5103414584d080c4240b0301181c400348015449200040c010b0800e114403510000a00422000001d0300e20409101d142c8090300c0004001040e1070207400c2c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 318195467 1250 318194217 318194269
    0xc0306090201120509061f14040903200c010806040c230706060b121b0405010e01050c060a050105120c01021f150314010501150e1302130b030402130b 66
    0x43e10f20b0507403500d0080b0305070718000402140c20700110300309015924005004480403203403003104100040c4ca01800034080100d2043c00d0341882d240d03000c21400e0b846414070f6000c44400005c400c2499010901a0006030081444e0411941c1e211715907580c054421075080110202d03003074004044106000841112141d54000703003012480c0302003500c0011754030000500c14a5102c00300590160030000504003455514000f0881d0072030207034042e40103200416841c0b8206840e2030011102c0c014203500c040e042c000200202008008240704151041d25000d0000c560740d490001480780010008035101600e412203400c0d5403640e070b030101c0e0420310032005c061120004199808218010b04403290303200c14a8094410010800c500c2c02440004641440020026030b030361413030142e451000321040407002800001030348203145032200c81201106a41ca8005081441114840c6008010343d0808819110301001700811880e00c0007040f020054025030034002000d807000480c481c1040b00310142c6101c0410b040d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 318196717 1250 318195467 318195469
    0x90e06040c20030405040b010e03120f0d0c0315050301060b040e0604020c03071a1b03040209040c0b0a0c0506060411040e070c05061014030f030322050d110d0c0c03060902 75
    0x81201181500b5400d490560381d42850210b0340c0743d0040c85502e010754104a41c51542c0e41c0a51070700250210041c010740b0421010070f004510780c1d4086034903541541d20610208244000c07a215807503040040c0d03140010140044182c00b01e00503100d52019110781e041420038030551540c1d0040e1011103000c0070b0390301d201d81c071a0000038019015a40d04508144004140c0300b090021100c07079690790380400d03807410300c054450b22001d8078410f403600b13500c11807204104082070050a00412465000f4056001000100d848044980b5194045c440740300000d0700000010301800b00c20300032a50001000c80301000744068400c0d5610317140c040c81c4145640000740728000748080d070140d0942814107a1010940d0321500d403176402400c28404500880c3d80c1405440c01d00015814009070b03c1000308124001142566220f40d000152003048408250300c080d090b00c401d000240c010070068009910b6034445100e0010004244c43c0b41111300c180700380070072500540000202d8100d0911005483d000f49000c5900f00d0300d80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 318197967 1250 318196717 318196727
    0xc0a240203041e180b01020a0b0a020d091415060d081e070c0e0f0708041e0b04080a0e031204121a1303020c1503010e130b010303020d020d090e06040c 66
    0x103070003001006603055104202d20783c81c2c0100000e54503200540c10100b244007083c1811104030411850140e40315540c00c1d404241c884c010241e010502d800094581342c146029801540c2110354102d500c001500c403180d51180080c022903e060744200e4a003c154035107100005c501d078000020251102100007000078100e51401c20240a105441c074200d03940e0b0150345098000c0c071030345100d40070f5106504408640c1000c0e10404140c080c2107c0e45d18903d15840315118480b0b481560020340400b0709800d80384400042c2003c0b04103101d6030043d0495601c1d400746c8100644101c2000c8503641c4030760454100c0420380750000c0c09507010b9421500f0507004001c01031820380000b40b203d56150035008400d80400c50440980b15001060034803030340c2500c940d43c000740140223a448017400388800e0148140014085400c000b0042c660100c0d0300d90b41c811401c00e140d210b030800b0b070318203800035001038000e900110340d802c1d010848041068500e24003444400d10305203d4407000c100251942c0e03c26a25002c070a40740c54407071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 318199217 1250 318197967 318197969
    0x1115041a0c070303061a120606040f0b090307050307050d060e0c09040f020102011a0a0b0c0703140a050d08010e0406020c101b030b0405060901030311010f1a01020c0a24020304 77
    0x88203411180d041a0380e074400940c00c1018210000381c00c04c140890348103020511101895002642c1c0e50500b00c1e14221006d800000518054100e46c0501001070903010004400c0000d2000320f10f100e560307107061810b0504090440e0003860280c1c0c44480304000b5603e4004003010590703006840003405e0220f01e620182016001c000541d40301008038144028080c03840307656421580b00b41c000300003c00d802c48a08140c0480030b0b007402c0d8000e00c0c804003045011800c0f0002c3c40d49865a50603110095100e95a41c10300319100a55410a43c0c000036804080000400c800c1110410508194842e0f616020040c14203100c002e0000b000c0b80e8003c141d03ca4544403c0141400c0c1e1498150240b05070f01030400040c0ca0701400554000000c0c1c100456001142424440e07540101c2c0040e010703855983c00d549040d21702d404140f80b40c81142d0344c1ca1b04c5400724088184070340c05900012010503e07812400344d00082c03501e0b00d00800301e403041d001c811040000211050752201c00308a0b113a5503038105240184164118055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 318200467 1250 318199217 318199253
    0x140d0204030c032405061e0d0b0103061401060903050307151e020c190206120405120f03060a080f060a050c090306010f050108010605120f04020d05030d0504030f111504 74
    0x4a018040700b08249413800145645068040c0e0420000181d60f03032041d203505031a8142c2010703016842c1803028080c1061000c0d00400900310112403105036075101d8090070300b40e006842099071880c1c15142d81d001e030540786004182d1131403c652054107540304d0585910070704800404c4110030041c442030a58203908045c001c818112142d814441541c0d24103406940101c0c2c00c0e440b940104404100d45c0141c900c400b000664000d00710078207101001c00602c41108001d84103640b02e110f2414081800c00c0700c00024214152102c55054a900701542440400d803840e4104e449240c20010380c5c41c40c120800986203070320141c0d00c007001c19140c450b0070320480e8a1040304240d940502400700045038041464030391904403402070f602c1c000c0e12b03a41e44104031114003a0540501128203000c010503071f4801c40340000307038120340020800d00710641150341d00c0b451a44102d5918000c191240200024581c011080f0101d80ca1103040800b0500b0380201007507118694101030240c4039198001140912165802085030b01c81 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 318201717 1250 318200467 318200483
    0x20a03060207110306060103230a060e0403030204030c120807061d030d09020a05090c0714031303110112020f0f1b010c1812110402090d020603130c0906030201140d020403 75
    0x15050810010250a0f05910f034028031442000c64041c0d480303441003040c603422030220b5a0042c141c4010000625034080d1041d004503445480100782040300801d85405944642c034010b07a582e185250a00c0441e4180c0e200c41c0c448084440d00b4004200ba91049030711035035102d0000203c004070709181801c400000d000a4510380b001007520a00903003c3c1d402442c00038002c40d16890350f6980da101700001c00c0000c544100d103105040c4005000500c0346101c40e000d4071300460903641010100c040108031950f89600581d840300c914410310300f4950b0000c40d0000304031030703400066203844400c0e00c0741c4165100c1c50701c03404070051000901c0380e480c2500d0b0114209160180000340326131070040100611001000e01c030700f00200c4000b4000503050382c52140d0300c1b042c40e601140c42d0780d010720550304000007504030400030f5400c000e81407032590040e95000700851040c203007850800c40560cd1802e1441e13281074070307400020030350f81f9008081c40541e803c9820914100c496414890b03464203089400d41c00ba000b158001800c2c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 318202967 1250 318201717 318201727
    0x10050711100c0504150311040f090b0909032719060f0c020a1205100203090a21020c0907051201030311071d0604021b2406010807090e060a030b0f040203010c09140607020a030602 78
    0x1560040800044501d002b40a225400c03a02041100071301040d0303449146988104070050544800d5441018040030103501c2400c3c3c41391400205049041d19049072031090300c52a0248029a0000d03040d04032481203141c0801030081c40e6000c21501511401003003444140400404d040180400c2110048482420150340340d00705042000d0340d231001e20804417103080e4410308201240a10303101c83c640a0003145c0c004c04100d1111024481c01400107094802044410030000c00d5031000040c1040c002c41c401c0c0c0d144c805203810b07030302907e003403100c540c20000680030198a606004d00903411080d41001c011035006076215100c0000da00d0380d081c429607540450044a01101e510025146500c14644030220b01c840ca0f6541e403001190126011603d04010400d8550203100c1c0c2d6008135a110f0313101c0b0300501001d82603a202d81380c000380110120b500c041059440400c0008604080c041c0d440050868200001c20328104400000c50024441a681c007400003c65050150341c2c514944500558100100715628 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 318204217 1250 318202967 318202979
    0xc0c030e150c191a04080f0708040509041b0b0903150606160804030308100302030607030f230907060206010305100c1202030a0524060702040b0310050711100c050415031104 76
    0x1190026104413a01c90013150100c0c0315044c0c56849690b121040c41d01e00290009400250707004800c045d0b0751004107020108140d02c50744a200d00580c01b0720b040088012104458142000c0a900f00c40344080040c0100e0b6400d07140012000440042d08001442540c1c5910100700c40340582c4920108034100c0e00e62100c2844560001001035074000d944610080e035956a044540600910000f5015440304002407041ca10075400244c400002c000c01007803003003072100759a803800e400e00e1295900c0d40300ca50522190f41010054030001308114000343c1010341c074603141c183e114515a582e819002d503d03045c1c603c0e92144912209400d0b0200068119140c0c20301c1c5248a00400c1d0071503560142500400020740d508001e0441a00d10041c004d00603407501000e17a084c8405800d10942140d0540710341a000c0d6035203002801200d1280913165500c800288000424900e00020301000c1000a8031340007120b912540c1c4007040304c1c1a20b54045200c403640c0c1460700110000d0100040385c0529480c04240400c035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 318205467 1250 318204217 318204253
    0x121d1c0803060d02150d0e03030103030c0605040c1e091b020c12070807090b010806030c0603070c0f0b070c051209030601030f0312061403010606090b040e04050a0b010803070201030c0c030e150c 85
    0x1b1121030550401c5810211420039689110a01000e008280b00708807400010311244c02813a40607215240d100c4050b03540e0440ea0411800071009403040c0540d04006001c07030306092041c40304524465410701c0c1c440030101d9001e500c0b44200700c1d145015200404400030180d10820a81c0c0060807090215a004e96803910108010720081042a0005044d440418007501d00055129103280380205418956103407698151108980307450200c45100c01c2c0c0883c200483d501d00d018512910391500c82d50b00384052403601c0341c148840c0c8590051505824006000c69440008188d819a82d0060702d1480b07500050a00384e0b40103402c0303106515080c0c1400300201d40c1400294581c45400d0064000f44003541e03c9500946204285016903e8500f10600c0104000b03201080c0c401e03042030041082d40c010364a00c1d203502443c500c00341c01c440e000e41d100107014011940e05100d0042910780303034039141c0004012680c005100ca4600403400c0d105181c0d103582500d450b41c15a04841e441c211010445000c1c080030350201030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 318206717 1250 318205467 318205477
    0x31003081e0325050903100c0e0d0f050607140414010309080304120f031a1017090105010501090b07020f040c02160810060b090108160c121d1c0803060d0215 69
    0xf180c403103161150412502800581d601000c00501415040340d89408140082000c2c80d16901080031410780c40000382c64a01c9251903040c040c8543c4511f140c3d5074201545802005800d200030400302d00319032140d103064403081e20155100c00c0000203034860f5170307070040700035200c4c0600180002c480002480700708903603002002104895034803074414400030001c00350102e803510820b50b4103540c181420414240742034101740c203044d10301c3e04000d400c0e54110030100540d441c2c1181d506080780e46d43d80040c4050342c1c0017170380300340100003440e5443d203803c2240d0301040d2000804080c0600480d00e4440f40c20940d8000d106040e00301d2080d100c2a41c107a0b41d038002440e07852241c80e000c801042c1c645800400c418803c0c030300b10b40c4004411703101c01c1016141c101d440b04d02d022100700c2c918100030b0076000c2c2000007001080c3c4820030403c19500d40440620070300e2031084920710381c9045d034414030340e04070716900d0148810841d80d0300c0780c6c004010350303287e0b620303007000c1403800701c0c1300320001d40c000507940e083e01c8503645640c080c0c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 318207967 1250 318206717 318206761
    0xe030a08010603020310030f02490c0501051308031c0515032d060c03010501030b09011404020c0307120f0807090609150e0d03020304090c05031003081e03 68
    0x9080e0340d990380310590403031009aa00110b41d01070301c4401d10100b016207280340c03041c91014040e102250511a003100110091162051414281c240b4514010440c482001507204108507600c0400030155039000c1220380e103115844c1801000b00f03040015580b09507800300241306400030b59031364111002c007511012499a854040141c980b07004100c80204104001c03540d00400b500030592040c4481c40d43c01032004c1031813903042c060301d101e42e4051180030038005103005001e44010f103900c1c0d5040000141c01e44040c400d6050090401000411064240b0340290007099015240141d0705c21000c0200d138150f220300c01c4003402029150300c81d406860392242101061101d1a07031045483d454a82c021264110a0f100e03072400140e401a09100701c1080185203c070103016410100340c000ba01002054030581c07886401c1d00960000b1404001900306030290b20714000c0940352040c82c5147c08004034022080c203010191007440040340f101c0800004c030058004619100c050103840c0d01c3c01c2c103032584099061049030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 318209217 1250 318207967 318207977
    0x60b0102010f090b0711100606020a02010f0c0506010504110f031006111203010303050f1215100201060b03010b090103180b1b03010e071d1827070e040f060e030a 71
    0x2080110b11900c91000d0542c2c2c4100f18410a44134124201c03071b41c009805012949010703051a19440c40c42a10405d801454560050521030140e80009000d040018100005020b4422500d10000d600412000d066580884000a14a081e030b14004190700030100102841d1400005102c80318012003a608119041c41d075030354140403000c007285920b0740c0103403400a40c0780c10240010b20000e4000c8028001c5c8200c0c4591aa003003108081c01202000c01c1650242101c02085c048646182070040381a14410f00c140003d220052170003101302801d201c140300300041620b000c1249122684260403506031003038940541d1020a4050900e6111184280c40481c0f0200c170007043c1a410304081e03001e0ba4101c8145580744440c0b40d589050984160301354100700c00c0c261003500d010309415510300c00e50001a0007052940c511520704243c04c40d02003006042c2c82c14100091002c505e0301c13504005801e10960344442c0205035242c480e840c000d8090302c044100100000c1c1440000c00311076800001401c01d80f003039035840d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 318210467 1250 318209217 318209231
    0x2030c0c0f030601032a12060b0901050307030b25091805040305040905060a080304140301050105040b060f0c0c150c160e1305120d060501090b0a0804060515030a060b010201 76
    0x1040800c030210721199030150800b0300100045181002c1394262a004580d0032128107001c003486044003001b54000c180001290605c01c0140f09107849030321701c002003e503681800d03941050300107030b41d4524500c401482000742c0800145c01c00724050310b1850300100340d6502d0300083d2081d0006406951180210495003c0b0300d40180002d40d010301805000d550591141490325040283c5000604001429580c2081601c200098040c10400040c802042064400301164440004060949006901c080c1c841d50500c4400a00d0743e0391041100c104205a054050b80d6113403002303491b41002d040c4280c01c4c0d8050210803140400086800083c131407000c00b9400d070b41c0c04040c000d90070303e10002c40d070062007201c04681000a80301a030607020b080d41107006008590104640f110a1600d942c070401c01d0400b15a12110b0400207940c000781030102800c41407101c2810004a264001c100010003040074040d5038860b0007040c1c84007888519012004800703002c0d1140b11007141000f00c05000e1600301c0340d006600c0d000c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 318211717 1250 318210467 318210469
    0x60e0c070c051003090b0103321b0a09143913050604030c09060e01060e010f140d05040b010503120405062208060411090705031311040c02030c0c 64
    0xc551456074060603079040e00741444103224410401c40980c405160b910807800b400300c0c8008180900852007a41000a40e5289500303c100900041440203082c141c003000801b40304001151b0035007031241c02583e40740c0700420b500000c1d00c14541580107200942c60a4008101d00400d42c1840744aa542c42804200002c2501019202040c201444502030b2480340342d10000d1040c101c00170032428034140411855903441c4c00000740b55074030640c02258034401c502420012038644d809400e0003802500350703c00c12507240841c09071403440d1940106040101042540980a0045101481d694065080e407910386a00803500801000192800d075002c84189000184c00d15001410b9001e60000305105400c091601c814007a15401124a03100b0038441282c0d450b52208030f0803605001005c000000b0801400d140c01c00341840750f001c00c11f060241d0103610400450940000031207400c44d0200d04100f4051025080c4910741e80007000c2825886814507190700b4401d03600001a2985114884c02d071103031103003024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 318212967 1250 318211717 318211741
    0x509151e07030e010f0504150203040306060806040b0424060815160e01030509010f051906050406030c0e1b0a030c0e03070e1b0f0d0603060b0f060405041107020d0303060e 75
    0x440d0042c00900040e204600a5100d948800da0301c0c1541c3c2030580c207054443c1c00c6a241d00c1400000d000060384041010000d100c09030007220001c20b46480540700b2400d25444a41100c0c1008001404210030f411044040051045040a40c0f030407010040001949902b030064480b5015240c940c1e4040080c0046220354221010418514040d92a1004007030646401540504002484055070355a40c003039a4202c1901c03030044522802210300784944082e0068007100884009070403d9019a02d40141400002c1241c4040015207035220780300038843e55680801c040000c44011999101800450100e00b80c0360503030080c1620b42602e032501c0c03503038554840034541e4501561040012940201c030101c0e1203907400d00020020080100c11042c035144046c041c030003556004040307140c0c0313142d40c07050100140462442400c44a900840700c20301070412040c000340c143d00550156174800e40e55643c8402950001b20f0446040a43c080d0440e10740300c0b050b09011740100110700c03c0c61002c68403400000c901d40449 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 318214217 1250 318212967 318212977
    0x60c0c210e040e010e0a0f02031204180e010e16091a1c020a080304061809050907030201110109020a0308090117040f0b10050d06050108010b0303040302090a0c0509151e 74
    0x240d07070340c5100198000401024282000c80750500d0f540c0c3d800d021005202c24400d1650403806400c5208050286106040c54812581b00740600c11f03d09000502030b240f00d1000e40b034030800e0502404148000380100c120700410100584420a20508511130300150f280c64444081f14000d200c00c10440a50070510720040e031040201d50f034004070080b801c50001d1082182d0440050010f4205581c040c0c0320302c2c0c19855548a41c02c00800310710401c0e5800760420a1072425030103040c0481c0140031a0402004e42071b2f5601030360000030f052103040803540d41d000c8025404840880d80040c2550030344c9550b4104140554400e10700f150000e04c580219800e0070240c4070810740640da201101d03a01c0c407060740e200c02803200d070301030800f2803034100c030700d500264598540c1030042107140030784c600241d82c0d403500c1d592608444002d00c419000340c109200801c0035944002c0034aa000c00040e1000c80c071646000d40c102c0d0607105459100d9805440540303190210342c2c20601400b240031001c1c03242c4ac20720b00030b4103c80b280d034090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 318215467 1250 318214217 318214283
    0x905010b1801030204050c040e090c04050a0b060a0c05162603030c12040f0b07020c180618150a06110c0f300708010911240a020a060c0c 60
    0x281c010401410140c0c091540004000d04190401c3e844416007a00a40c040d240c1700b02640c00410a4011454a40b007041d81208a541c1b00704601860000840c0c0c0c4c07406020000d40a000c00800308005101007840140b0580c5046040205200d0f03c1e08020a07145030605142c00d41b809910040141e50400042182d002d00311014440d8148521080410100707400284101d46000e44050444001803070803d030a80100380740e8001d88441c0035070340c3c24001420080318003020352030868024410389413a0b9103c040d900d030310345401508c0980d560368105852480d810608941000c0441000507505601000203010f45012505440c2d44000a408000080c690700e8400b590244a0f5005141110340b0020f407a49818002c0701250581404d01440307030b0522044d940030460b640d4443c01e10303d0800030450302001156038116103a840c2c0d2110790300c100410046000c0d45103581c150008150010a0081020b448860303807281d801d000200d03038a400280f1412100004440c0d02d21030108248111405001042000807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 318216717 1250 318215467 318215509
    0x60f051806010e0943051e0907050a180306021c1a011b02040e010c20030405040902060f0301060315050d15180f050303060910030c030807060e0d02010905010b 70
    0x84c403104000d003005a90494a40d03518034000c640b840340070031203000b0303101a4117180d0321784824640020300405924810304070103070302c01011406c283e03a03440900303058100c081807030100e03203031100c103d000d0b54250b444140c00c400d140e5540304004100f0010b50014656170403105040102d84a44684813019180007861a440880780001c40660303551180c480410b00d28492140401d80200e2900841c1c2103824054244989035101d0001001c0d16030840000100790740b01d40f1101e1007810644140d1510707805070340501445280c8500c199415940d0302e80076100f5a040c900d03d02c40d40c07565119409401800c1d01013101210f80d030750403c0001e0742d2400b0001c150104d600410f440c0c5c18000b04440c50310042c004420350912440f010201000030a6407510240b000c0c0740700b2030096a0b03a0030050104803100d04c00500000098618039020710008100c2c05007507080b00d903c00d41043d2600030342e01d0404041c018055114100388200c0850b580d81d1641500300b00f89090041001b0400c070540756080c401441288014035610503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 318217967 1250 318216717 318216733
    0x30e032103100f1410051b0706090602030427090228140904030809070807030305070624060806030a0f110a241107080105040803010e010806160309060f051806010e09 73
    0x108040c101e000000c0110301c0c6c400e15107001d000f940c0c5502803007401e00e1010b41e4054502841031980002500c401307440a0300096080c1072405034146c90b41c81c0303c2108104409000f50118401c2ca0301600041c035020750040405e02c0c1860f054003040d880b1110482e1840c40909020f10000e0b1100c50f41150390141c103000340c651405075640f624282d50381c1c43d020b000b00703520f4404c031400064070120900151010718401d546083c1d0340e030254102a81a03420380c80814000d00420f91400c1e10000120158204859260410f82c5a43d41e42800007420f02c0e030082d0000d00302040d0f258552082019041d142001e01c80200c80210140e620303450684c0031841381d105210017240040180110302e42c01030402964988001c801c075030807c2d40342c0c400b060a4840c1540d0443d040d0102000500034101d440020360b002d41440740c01044649001080d180726021504055000d25a4404a143c14008550000241468042010322041c1002072001e070328501c50130f80031095400b44900200f0561b9892032a44d008104074001846030b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 318219217 1250 318217967 318217969
    0x10806010f020a020a060210050a330909060e19020a06110f0106080d141e0a0318080406180e160203120906240d030e032103100f14 58
    0x180300741400950961003061030210050360381e040960007800c401c1d030140442401403400d000903504017510043e4010b0615101009809141c1403416450704590036103d0f101c048002010600b140942044103003e040006920501c0a10780120048042910840e0584171440e100c042100c1900400258015040f80b810400c3c54407400301c2c402418860025170f045155403071040d84c01c40e00254000c030025000200c50300070080d00b200c45680382c004804d914500e420800001c4840c80c080c3c003501c06022800200b200b0110350700c01c0d4006046c5d078011908903c4a111340c0e04006000d80c01c0351056400040c0e241440c2d03580c1c005085408811282401c4100c00591104000c1840d9000c010305d44108501c0184080c014019800501d54028204000604400c4c1013091044c5400310b0120302c0c00024106110740001300d502c036a83c001042d280c041c600007000799000c0c0e002038100070b15041204520038000500c00301503030141c1e00844c010b4103403068151559980e00c02c10703100e20a043c03107981c0c1b101031594050042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 318220467 1250 318219217 318219227
    0x109090b0f0f0f090a0902090108150a021606090308010e06060f04051e0a06030b09060402070302030a030507110703080405041a0303040902030405070f0b09010f140706180c0e04050c090601080601 86
    0xa038401000c0751034200320340010421319201190041d01030350b00c49030b4082c294206404501e0140c403916024040d4103c0c088000049403070044d003d00ca0300c3e030b030016403a41e181c00100d030310000d0194006024840318200d0300b001042d0000a0140f6100311840801080e6586046012142110a4120910b0401e0720b040e003042103007024000c01c506040c107411203442c626564122004050400c1e51000100000c12105010356140001c0c401c500941c41040440e0201e03800105491000300c0520380400e050365040c00032103901c0c407080752009a500c80da19011081004481c0984281c7e0402d8070100910b200c0548a40e0a0311000642160503400401c0240031018094005503032040c0584104c030300643e0b03941d150b10f6a008040d40034048800d000f040421352907a0100803808407a03801c0c90800303582c40c800c66a404162140101c0100780c03959404c0d40c02c0685817014854000ca9401c03500304038146544180b542d0000e07008030350442d2035000e12030301041d092811100407405240181e4030340c2e409540360001514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 318221717 1250 318220467 318220489
    0x90a020607081b030301060e04270201091e08010e0a0f0f03050702090c09130b1c1704090209030f0105090a0f0f0c0303030c1101090b04020907090b0412020109090b0f 73
    0x509442c0801c0301c000b402c84550020180060100021580e940c9000801080301c030302d44055600c2281044d0a80d41c600c0300025442d41e800c40c0340811206840d045200682e84d2000303d601034000610302301004e454801401c1064000c0700e45040c000c3c4020402d1306130300c030f0700c403854044010078480381e0b07400e020042200c258001c082244681052854407030f080c0c0000f03880e4941194030300d5446c000050b18184c1801e20a03420445c110101d0024441ca500010000da0309682c6c620710204050000d00307195050081080d0042501c2ca25441402d60710f6403542c20030800703076020361001303402445522000400f40905215441c4070303102036400b130306482490307694000304802481c2d0150b59580d60109600003040c20350038540c00451081d00c0000b854184104054151a02c0500100b0682d15101200011400084450f98072a03811115280389540f01130042c0c8100c0103d4125800700c120205010030b0740c10300115406c1031503001742c80c0c249a25644001800c1560400a8000d41001038201c9551145c1080210b001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 318222967 1250 318221717 318221723
    0x3070b060a09020d1b031e0b0d0b0901091106070c05011d040e070608090a11120a0b0f040606090506031902010e100c020a0509010b0a050c011d0d030b010503090a020607 74
    0x1c880c568400e450b00c2682c0040c200c12603a6542e4081c0e0460103024a0034401d18018603040c10300c40510349589181c660b1003510382c0c0322280750700ca070355060070340e51941c1421088075070001d6012814205240b0710350080c401804204d55804490500f00b200d45000030a480110340e100c00d408106500b01001166401021048017407901444a400706203035880c0e01981c01e0401d08080100707c2c151501c003000f41810360181440045030804401440810101d2030058080901034484091070804039591514091281c60040e240c0358600c000e00c1035091007480d41500850007010148041070b101c00442084800070b48041d0341c10780c0090141c483d054a14140342c03045900504014001000180220340008498000500010956903456045207821540b001c0904000c0d9182c0000b0f60621032030404501c11030150a00344100410b0349183d20000350005c1940080030740002e5000c0c8000380c4442c3c0c3d0ba03a80d05008102203814403540b00f0065100b01d081d64400c00d01032000303110080f01e9409020075070303100c2c0c0c0707090f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 318224217 1250 318222967 318222979
    0xb0a02090d140a0803040602270d062004030f12020606010905010c03020f010f020a03061d0c0d0b0a090203070e1503180708010c02070303120b09060919110301060f020a0503070b06 79
    0x4101041318a0080c6200b02e000e07050143c0c1d00c611000fa400d806602c00c00c0054246001e00a405860f929000000c00b01e150b40700d40d000500c0031114610041c00011401070450483c40090302000f00000006040c03070503486503404135000700c00210141c0c4c8854007124258005810800100031b2584158a080d05842c042c0c01986c0f850302d8070103a1113080d203209a10b603620b0107400040c800f8040c0d605204103402441071191a4640c4844a060024000d1006e003402400c01d002044080b0b0410059101c0600014020003204130b0941c1c501c08800a500300319201c0010a0025101d4805800d0107900071072555400180700340340d995110348400101d080c404040080344281a4041503108003481307407190061098009000307540c03440c038001740940c40d2079120541c04c50a008040c0a261601c05c2d003140c00000844801d1002e039140b601c3c0034000001c5074081036007141050904607800014800560507942503680b00520741690b00c40a0b6602c840c0206d00070500c0d4020800500414a900c0d01e19070005002001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 318225467 1250 318224217 318224233
    0x15050406020706060608071818020307020709060305010f0509030c06010b220b0415020d02190f20040c09030f02120a02030703080a0206060f18060a051c0b0a02090d14 73
    0x983e01c1150115080000804c21a40c2405486604014070741135242c4010040d5100b00d080a8140e264648032904c140702c40354000c0003091860f4001d008542c046e141c0705004111041e036900f015401303400d40b4028034040740e203080081211514080219042301c0805001455540d04c0d0040480703aa40c41214401110007010701180c044414040b032160040c400708640c580c0391230a12505c1403440c28641184002d542c008094030740581c4d00414140800300000554041546142c100301c0140040c1c004000c018a54074007502980401680240d0481031040c0c038100300d035005804082d1214004e9010207042840c1d929038040052401080e8860f40740046015904e8480281c0d0100f440c9ca021030b04115a800030109040c20402e07410480664404002c590241061522102040440540c0072a60000100d4400012030701d03121150028014030000e040c00b495110700081203400328040400840f14065520017007504d0030a0360080e41c034400d0000f024565629a140e40b0100c401d61074140292a034020569 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 318226717 1250 318225467 318225473
    0x3030c170f0a09080f01060e04121833050d05040c0f180b0114030c0a020708030c1f0506011b030201060308121e010e1b19020c0a060507150504060207 66
    0x1015206032a8551512200c07503042142d8a400c204901c2176403081a0324015081040d00000780f601c1d60031941014114191801c00030044400c003d000c0c003109262482e004001800c000c000c10143c000c0440955801e42c46c0c110301121038024840703121540001001409844404070700e139401076400074403e88008030307860354490040e00c0702043d9901c080051501071070074034800e400703d0052442080d004d2030104904216000300c001140000b405941540740003003241c0c032100c0d00801079480504252412291142d60000300c15035110b05030301e1582036500c0c020040c4900e40b40300c0c0c0600360055005841d00400c0d44070034000c0c4890b043c80c040d0260700315901c3e02000400b142509004041e0000d00942e94001407510010101c058805144070314040b004103001080301c0011023100c250402041e002805400f0703041c002404580c090981704680301140511500a29500001d10183d07054050b43d12041403681d9007019503041c01146000703005100e18507090200308521360700c50341d84240704020050600344991 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 318227967 1250 318226717 318226747
    0x5030711070e0103240509102304110a08010e0c0d081204060501050a080c030c0609010311121008060c09090a110c01090b130c0e0601020c030d030b0f0a03030c17 71
    0xa4800c2d40c030317007600c405e48214000303d1038405007030304c0c1c22428240810b0800140e120360350850050000c0d6036641d01c40d00020200c0c0d514030500c40d10f501d81d8070074449c02d0915003400e268120180b050244034401d1108006074024045c0140c0403540141e00c05400079103000c0081c004202d4200c002150303400c20401030b280c2d51103440381041d40554040e540000300b03903060405002e81c41403275070000c0403558407004842605560010307895501c40400d641450b100c1ca01900141d024100540c0ea003003803d140860070503140c10107000340600c90a650381486ca00d644ea1500d60b0341d1500d03c1904c420810805c100015034050501c50260b507085000902c0001e403685042d030300c0b1303002e0342c01050050790540d4441d00c1201c14403045012180d00070707003c14a0700380c0383c1c03e196603a072080c01d041d80700790b00c02c4c40314031800648a80c1c001d010440314030b440602079400f0a030300c4840040007480d4201003644550301801c1420685e00340000c1400c00d42e40c5c191100140703130308a6291003150340f0034600b50b15000d000400410b81810303520307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 318229217 1250 318227967 318227969
    0x513051b18090d02010b090411040f0f0c050306090703090f080304170301091e020301050d171b07080714010906110a060e030d05011211010c0812040c03021f05030711070e01 76
    0x51400f0303190414040307a0082c2565500030110b4490034a0a0601020545d080141e058a40048500182441e45000c801020700380740e01c200740d507191400048a01c0140c2001c02503105410445080095642c1d00500350215514080054200d40c001e034000c41c0003601c0c4100464101c1d000e12507000c0994180000c500762640b00340c1109506d00c0e295210700040c0da003100c4102e6100c0e00c11200550071981814003184480c1c00502c0050710842c500210355451405030003c48104280c50301441b840c8809181030651784182c18800c0d006039115188000406842001c0c40d091000030503925a11600e01e012030488207070190b5540b08a85026020209000400502c01e0981840300c48001d16182c6040703900c21030498030b0580c400d104001101c0140030000b241c0e80000d00e100e520908202d020500c02c0d09221010780524004000301d080d02c1e002740030a011000c600707501281c1c403c40340c190464071043d84140c6a420000d11f1400450001d01c0801c01c00d40c0281b0b0704045040300f22040380c001d0f5584418401980c030007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 318230467 1250 318229217 318229231
    0xf1b02040c090806070215060f0f181605040b07030f020f0604050d090509010b09060a050d0e07050922142b020609070608010e10091b02010513051b18 66
    0xc110100f1003002d003803240c1130b805002c40c0041c1408200000707a2107160340c4000c04051050000024203000c40ea501244c1d803207000d030081c011010002055001840e10314007503516105c00d18280e100f18445900c203204803401d6543c19010641452110396040e9040500121500e040d03000d50782c440350761a4010000c007449240100d00415240c1d04030b113030140c45d48201d50420740c0540c02c0200103100741c1d4260b8049a040b26000e030380c0c89a8401041900f15a00c0c09805100d101a078140300c0c04d180000b40001d2101c0603120100d6800c551500d43c0c4072660a50f550030641070300c0c800c0c880300030400030403a4140100b544130941e01c01d4860050411050140141d110340180c107040105010030000f29504102d000ea005024000a0100600b031085c0913045103c1403080c010910b244800052010071307100d6000004110040c0107201c2104800303054624041f1907032241e4010b40ca4240040c0d0901c45168006000f81e400c100600f26986060300b00c130b07150050300505150032540c100c1d4a80000c1d01d00e41c903600d00c5581 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 318231717 1250 318230467 318230477
    0xf0f0714180a1d0c1c08040e0a0903030b010e090a0c1e0c060b0904050a170409020a05030714040f06052a070f0f03080a050d0f0c03060303080a020a0f1b02040c 70
    0x340182d02041000e18808400f96001c1103424030591155002c620145404450b203000b12030302881c11854920558220000908441007804080c40054000c4500d241c03083e1401d00014100390700444a544100011961240c01c0c1400310301c0584055000c4d410101051911020400d525040d1a115204ea41500310000d1003500c100c0050190600c610341c0c2c5204216500512418030b525007540c1c034000d0800140011400e81d040001c540e07480801c560080c190b0280075502d81d004001c0141642c2c000700c41765000b03c0d46002e1110309142c0b000003190250b4550f413050b544107d0520000726056044003942c0c600101251040349106c0c0303c0c0c1440d00c1da030a02d694000345920b81c288020450480055170145016000c6224180005141681600da01e403215187c2a42c40d9020342580c0c501510354450224141443c041d2902c0d0002da042c0c01c10002d40307000345c0780e2205685401c1d03280d00c124400c018200c400070320a03149540186110b80b03c1100e40c10841005840412030390340010b02190180700e0b00c003012079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 318232967 1250 318231717 318231731
    0x90d170a1715010203030402270106080915010f090207050a0c171905060a0902030a1403090f010512070302070317010605040611010c1d030106080615030f0f0714180a 73
    0x918081e07030b5000b8070096602031880358550020703569010280c0000d00c07504442039020109004c0361f0410301c80c0d1440c104510590f503980e1700040c0001400307580d042814080e1510309190102404202c40c120350b454034038003102c50328001c0c01000075088550200c2d01409003210741d4012a5403481079001802c0c8005044048036850789400c0d2812079090503a410700c0c0c1045020780f01040000c203440c3ea018082c00400b0424941314030000f418007241010040889040c1581c40d4171422002002e003400311400d841c0c64020160789001580da80c014804100041f001000000740214821303009031640c18031030b05107044807081140c83c8400008003600203400050300407404202e220340c00070240d01c80804040082111091492008241c0b000000d16040001c400a507604215103095210b040248014000c1d1907031402c1a0340c801c0d0f036035420b540c9064420b21940b9082c84c01d005001c0303240c0f4100f50803e002080402e1038101d100b00c042d041c1300d06060b0700002c1c60258900506624003020300c9a484454002188 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 318234217 1250 318232967 318232997
    0xa151109061b010e0601060c110f0316060e0a08030d0209040207140307020102010b010311030f1f06030b090109140f040804050d240209030d0c14010615090803030606090d170a 77
    0x140d210071101c136103a52245c001005010341008a114140d6005071941802c007465a0200f000510142c4696070944a03004102d50b01c20052030348002540c043e40e5514400c0f41480007000070040c124001c4c404103801c00c0100244a44e00c940c001c086059000d0005410840b494581d07440b8001701a50062aa41002071058219a4284600c05402c00c0034201046205414980b18030039020043c04003a5120141020840d2000360000c0f805010800c50183c0380e00c55140c4030020040c10b010424540212810400890404c4043c007541074060300c000c2550103250350780450200d02c8800900150b0360503c0810000c151516084c00c08518079024003400c00d00030306109403110044e210f201420b26007070301c10302481c40940d50204480c0b01700da250f850203400240260505510000c24541030340c2c1d030b541c80c001c800103062031380d0b180c1076000740360540310400f2040eaa81d04541d1039210072600f0503400074003040003141a01d02910004022402815002041801c0c1c2502c08020342c85041081301007031a8901c15510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 318235467 1250 318234217 318234221
    0x3160c170a0b0c0f0d023a06050f0619090e0703051617070f0509040c0903050d020105100303050c1c110123040221060c030a05090a151109061b01 64
    0x20110051140e1304c0d0143c2848400707014040c06411490003600021301c4003c4500703e908002002d0854040341181481c0c45000700b05003869900c0301c0101c241801c0c070000741032400c43c40006c3c28110290005242082c49a01c110502c01140421014081c0174200032031641c10100d1070758818420b03038400240c54240440724481740c200c016060700400900fa5140c8032104000101e40360001e6080c24900e4032500407100c10394180c0110b0290b241c029140c20a2038404992261040e41224000c0d402c4d01e40c80e4807001c20403401c2c0c40040700c2c009581e6220f80c000b040080e118800422800385d42034103440380320140012030b424200c80c4d43c0c03035040012603200ba0081040001c0c8078404418001c4040ca44c620420098201c0003000e00a0000c0e1013200d00142454002c0c540c50020a521001c220646206243c82c25903110f00b500103481c054002458140000c2ca082c00c0010003100042e004441040e8240ca10060f81c0040d04810a030b01c5030500d014080c0c0b07140350311190301030f100341050308036116100701e88201403c0c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 318236717 1250 318235467 318235471
    0xb09240402010f08090c040e01051b21070c140109050c0604060806040908040321120b01080a05040c05221104060518030309060f1201080105060303160c170a0b 70
    0x210419090a100050b0380200307000225685a0501d8a816074441c11400e0070800e0040c0c10980080c2081010205500e042d4042840340d040320440000f052042c824102090207541202220281d050b01400d000d0f40c100e0302c410358049454500b00240550994640590800386043c80076569110301d103800c00c102062182d4200036600351045420b00340761100042010101911080c05250307100c2041e402d21080230112000346400c20110441c8070f00d40c0e13111100744c0b9003200303048001034002c64068269070594042d80c0440a0140e48408942d01c4450781e0310018400604101c40c0690480d00009268966144954007a208820003040b02e43c2e80341c1c05a420350b083d401109a82e40c5040205101c240d0b0000d06451510034140c2074000078040d45000b00e440d520803c82c04640c41000030134607003000314040000301101924044288a07990703131385900781d0903207000340c465580c580c00502100b6640b440e840e841c2d1a40600500702444190340d9a82180d0b0b07980003281030b1710203940140345690144281851095 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 318237967 1250 318236717 318236773
    0xf06070602072a211209090501080316020f0a030611090f060703140706020706050114030d03110307230c0309010816090504021c060602100b010c0803061005070b09 72
    0xd00740041919402102d01454050103a400c0300b458a40060741134164800208a54030090020800e14007101c00b61180320b03648900f4034024204030001c0340c0d07c0350210648a494502080d540e14620301582040000b07034040d800030f130f0002130000e0000049126800707200011070917803201540d61010786003403181d44610100c04500400040211800095000d000100c01004800e00707942c84128619061001c1d10441401400b20f5007040c00200e21410300096010b000e40c802c4040b142c0070309880303400380c0aa5482c0079000008c51018000150000e0103132620710407002041c103400b032003403001c0081210507400601c3c08000d1a4404144010b86503041030700990019054458031031003840d01c000c02401c03012603018650045801080b40100004680d02003000d441e400300d01442480d440d1040295107880100c0142a040d04001420481c0c3d401800301000c90343e000020b59285603242402e00c200400500766160801c90200125004a17284034802c03406011a0300242820b140b040105070303000f00d202c1e6004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 318239217 1250 318237967 318238013
    0x3050901140c03061203070803040b060109050d1a0901202223060403020d1101030507030b0a0b07050a0c090609110a0509090604110a0203032e0303030b0f0607060207 73
    0x202002c81a002c040d00c3c0d0000b41214060040c42c035140c1e205085004034080201441c10103c244000c00c4024010f07140308880030b0361101485a030703032030800003a50090316003e13040807160700901c00740001e01320006501c0ac0c0404004900c03e00802d80c602124405150307405070302d9002142c2d0540240c00e56024014802080c1c643e58003882c200401c040242c191030903c14480d40001e40c58060700c0d02c41100b40d078001d640080c0fa804800400d424050803810405410500085c03030700000501041c003d00c179034052108041e0000b502a4100344d550f41c0c081c0d200050585061141c1c404a400040000e040e14003d0710442c0b2001c9402450410704000f62103410a42c0e40b01c00f04140482e116056100c0107986484c1800c44042c442501d5120201d00281074098090b000d8440000ba071018941e00000118025441040020b209403080320002c03c003110340001c52034084d5401d884c1000828403c0e00301e80302d0000000d04249010a0946c0001c0141d4068003040b501160041420810f11120603103444610002000e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 318240467 1250 318239217 318239221
    0xc0d03060302010f0f0c020406030b070225141201110c0d05070201080606030a0605041b090e060102070e0a180f06050603010504080322290709030210050a110106060305090114 77
    0x1070601c010411307040007000300c03202501c0c0845120703010ba5002c0d030390060700070004180c4900300340600c20000c603000c00143c400c1060700a032080b4040b8015044880c9a240c6c06060b03400c040c03107280b803c141c0494996020b5140101560004ca02f0300c11a803150303c030143c2c030035a1000c051051505022282d0f0000042c890b040c040c05000d42d070070484079940510b04984107540c0c1c1e0341e010385c420010708658020a401c54640b03000e504040880506211403203450b902c0d82542142c1d142803a0310b01220898142e401a00443c0d01045003a500c0c95025400103409400811103c1c003d505003d80f080d0604404e50b40807140703049250034084188211038101206900901091510780c440810b244000781090400c900120b001901300485c140c15a1016039026141d504d13004a4140c0d002c010400c103004078903a030700b11140030542842c06081d0b00b104481d03003c1c002d40d00b42004000e05507025000700d0040b206004590304402c948401c20320403074010f030000b03403400507032410162499801c50380303a041208044103030101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 318241717 1250 318240467 318240469
    0x30c190c15090b1605070807170105060f091009110d0c0512041101020f0601030b04110303030906040201180b0a021501090209010e100c0f05030903100b1c1e080c0d03060302 76
    0x402402a00c1d030644440703583d410101c455400640300e51380003524a0049510100e42d900c2c1c0801c010045036000b8540b9007107105020320040c2250000c1c0c609580c45030b914040607016040c5a00000c0d40030900315070040c01c030341e0386072094000c0d034104051030400b0000c00205070030412007602c9081e49810161805c282041c2d64002c040b00c0d04100940301611b58040107020720001c0e8400c00c0001891416002512000d5940b0718003130801c400309a40458815100c80b20740341c5141400010360f88a6189100200312585441d001569040f500d4072038440c2c0e080b105040881c00d0354440d0010401f18010385d00501c186118141c0c0e40003404c106811608480c0d0042284c0c12050380d02c142c1d42020750100300e604d8500c00305000429aa1400c03032000041c10079011180c0c500030301401101074980d0310001c0d000c0d02c002520040031641120403208003a42c0c4001d610003a1910360507640c04c280f00c0135204240040001e00300248602c04210700600855075801c0000d8030328902103091100d0308998243d41010301c20241103034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 318242967 1250 318241717 318241727
    0x304240e0604140708011103011a03070203040311040b040c0206072c01211b09060e0105041e0e0a0608070503030910050d2406031d030a0c0203030c190c15 68
    0x68400707007184440c50030410308214140f002d40003d040c5e501c002c0004e612076101c00d60351a0024132130000e541c101d0490100390307120394404032072240010b5409585058296910100302c040100401c40d00681d9404050704a9115445040180d582c2c41d0000c022038a0103020041051000240a1917003a42503e10b000d45406d030600d00b510b504400b400c1040c001228143e8880c041100d01e06241c100ca401d00c200c01c0b411040190b02000481415900c8001d5641c9441c02a50311409000e0071500040c01040104aa000c1d5045072254202e0804862041140e80e100e648a0040040d030305990034a5681a04010b1203c00f007210700d005060a03405075003090701c400d00207034129043c07518040c00c1c0b010002c0c40340803503542e1794000070702c07400c04130b6100003031080244103164403001600038100400c0c98040f6502514103201c42d00e10700c0881d280021031800e000c0c110121170700d9000140032038061000b807040740c002100500040b90407500400222015400d5418040342e200a070750702482c03002c180d142c2c040c641c02d503220b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 318244217 1250 318242967 318242971
    0xf02090a0b060414010c06090b041b050a0605070807051002040f06110a0b13050a1a0903031b130e040b06040c110606150408010218011805010804020f010c080304240e06 74
    0x28084c80340c403441c00143c506690780c48004107010b1034041c0d00020415100c0701a0b00907405811500c0d803611401001d10801c0030140109980402d11450030440944603400401c26540700d01040360506031655900e038075001504001c08500e41d00400c0605c554a0210000401055985402458040e038540e80301d4840d02d205102070511880540040c00e03030000c00c16101c2d209075000003202c00c400e0450400464541842510136501c8888c3c801207140d100c0c00000b52400f0721100c451905018200d4844000168402544c06610560919002454103241d40342e481c4101c2c015003580d541c619120080000f2984105860400d00c10007140350003060000060b840d501c00401c3c0c1d902620101106034561050107140e001200a600000720712100160810072540490000e803120403600d19084540c41d940022400b5490015103404000b9015140c4801d043c1003401e410f05014107a1b240713580310024194022103068810501c0f01c0b42070201100c903042c0103264080d040c4030411005000c1458651100e82c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 318245467 1250 318244217 318244229
    0x30c030c0d0b0417030a050f1501120c0e04020d020705010b0406121205090607050115060f0f08150301061d07030902090f091f0902150c031e0d06030f02090a0b0604 72
    0x41c01c2c0001e810403000d0520484004091910340341c41e841d0610900e4003502040b5414075421000c403010400b1180385188080c0d04c0817058513078a842d0150b85541030000c0605803c45410400c51884251243d110383c4014580600501c802580d51007d90a0060960340e082d02c090f8012440e0140c00c0022403c07400381c4950196002e4035541c02c1602d00f00b802c0326a401075031080c039400440095807004200707056001c801c0130190310b00480703c2181c0d10001030720184069500c450100f00c2c103025080c07446210365903040d80800c03040e02c03104510b2195008a42100e0103900701c03216540318070b103544000130101c0f00a15031009492a05004601c02c9601040c840c1070041d18a0085a100c10089002c08109200003120b00c1c01e201500310501120082003406843c02d20800c0c1e004100c500c1c50708405030420821280f102d80150021880c1040019a1400e00c13140000d080d40401410b0241d1103005009002c1d0317800460042d503081e070400c5214010400c150801601c246202407800031401504c4d1204e0042c0c40c22200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 318246717 1250 318245467 318245483
    0x30309030f0a11010501090501150c0305090609010c08031608090309100c05010207061b0e0108090601060c21030f0b041b121104240203130b300105030c030c0d 70
    0x209030400340c42c210000303c0110015400c00002094038040e982c082030480f03011113140d04607412080c0781039401c0030351180007800042c010890600c1900b0b10000400d4410300c1071401030344554843d2640c10b059001626144100104403480540040d80100101d801000c4032019504d00800c1c03500183c807242240118009100d40c9005200510501b03505079000c3e550032074414449804001a511103441c503c0101201003504400c820205500c180640361007100d1031002090b20742d003003030402c0d1084006554103c031032584584401151051010403814003840c19200404c19001d61007084050b10a1070091902862422000e52880a011900e403610035507282440c01c1030f1002049030002034603403641500c2c0315040001e0000351080c41600308880c40601d0400040d03a20003041f400720b80b0b0b885210701c0b90100214010f024060355488400034146821a00c3c4000e00c2d85501c6284e01c04400c01ca883c0078801210a403004000300d003402e019076801d551044014000b41d5501c10001242500c0d000e5001e04404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 318247967 1250 318246717 318246727
    0x40603110d0504060c08130221030c2b0e010f080a1811041404211e08090c150d0902060403020603011e0e1005060d090b07020c0909030309030f 63
    0x2000e40d00715100500129000c0c48280f60506182d0050700c11100345000107200040094420608240e8191942d503004103035030140c0054000c118002801a41d40c80300c980010409816510001c21113416039042c44140d508880654144da1100c004c224841c45041c0316208601c42c940e81c1e84440d01224100f00340c24220710725182c000c480c1d8014001c80e90359024000c0740c0c410305800c3c02541c0150389414481211706105000314241c42041005040d20010303c11410110140c207417218805e0101201c0100d480c0050300b070111900c82d42c00580b4554110004908150240300c0c40303820a10250903190005d42c0c244c19490307400c1c2112402c500c11064240a01d03948d5022010031990740b1000c803001950010009504c9507140c03462003107400b042c583c0c0514001e61609000034100301219070300344609201d83e00b003c0142e25060610406901010009100c113641d2a139440c005400008424003a503520750050404074484414060000c1005d050300d42a64010300811529070300010450381840451503400b0348803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 318249217 1250 318247967 318247991
    0x9080601080606132307050c070909050a02121504151a0307091e09030203031f0b0a08070302090a0803030603100e060711030403050f0c0f100c0305090d020a09020c1e03040603 77
    0x4000003044800702841100c00e005801d1f500c0310203070030001250300c02e0324a010b65451040c0c04030b0b582500018000d03000140138401501e070100c104110a150030307081d102e90b030120003445808014116022600b207501c8054900043c2d840780f150002a41c50741c4dc680c92414040c2c400640da46045100d00b54a42c0d845050b88203058000c1d036100451a84651020f00c045e40151601070b41320b030011290a103402c4016003200852040401200044a1544440a1401801b1042100c1014004110306c080c980c0800855000b600c500640c00001d01400c0099900d078145002054105034540c0c085103183e03403c0250000840e6804105642c216095040031106a0034901c4214203500480c0d00140560040007a04040c5420105804e00e8103c1c045444200724624041003255920b06032100b440041c007482804000640540010039030000c00078001d0540f00c6075580001d020210702d0b00b00669580c0c01152409000001b040720342030038041c010358142e0300a548501076a80e8020340c880c030010180c40e034030807040e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 318250467 1250 318249217 318249251
    0x9180a24020a2f120301090c0206130b0703180c0f0f050f0d0f0b100e10060f0c150e1f0204031a040309030f0317070509010f050d06050307060908060108060613 70
    0x1aa83c0c079043d580280402c103900e41142d002442800c03640d604004810311502d201288440c030800e0440412000c10308070b0f484640d842c94004007800c041c141c1c9c803440c10f6074001044100240040c810009502c12074144118a040c2c02d000c5e500c0110b902c254114248010381d103070700840b010210241c0f03892005454030b003011040520000d01c050a0035503000d06200c0b05c41224007010060750400c0e800b401140d100d10011000c001a1489004005010603c004490754422149040c0032409056417001c504407411481c0c0c00c551510002945c2c40d4001028010807201e008009010319404450440c02d0910b11384921103251480300390320543c1c0c0542400101014000c80034400070b150404030144008039940b4000d0028a1100006011001c400c2c0014011a100701c1c02ca034100d42060750782c1113480c2c10480c81610b0396081000401010343d100c0c8808507068504100d9a4001e20350b0382d50b9026240e14042a080c10504180c01525241c1c010004100503521503803440720030900b20000000c1d0b04084669030b580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 318251717 1250 318250467 318250547
    0x12030804110a0f030605012103030c090b18010206090f03030f0a020409050a020c0c0a080c0d0204020708030c0a0f1b030c020f090109020c010f0b0f09180a24020a 71
    0x241c0064031880105011200c0e00c0102d044d28818102000566281d044925024171856a9031426144440c1c4000001c4c0c82038020491f520104d007044014591284d206901c0350704004202401241c825440c4072556034104401c0e50000d18a00180603d8000c3d2042180c59200c0201008580c00b00c50010038031318035186d0304039801850842410040c03800d0211002010f507104443c4661075108001c4041c03201d10308000303214111040c420041490f100f80c4024040015901041030b41c0c040c0e1700384400c0b4003194100d00114441d00350280c0d01541c07180c0541014007903407141408001002140c000e29082248906030b507084854050401508a0402e440000c40700740c007044003d50072400d2100000750007203480e00909911a00300f03009002c9002d00301d4160307044984038002168425140b06925245003000802030b504050000005080742450316540307031038061804821543d000d0b080f00b804000d021040d034501d0761625004d80c154900110400000d0240035a1084596428450b00380d2a9034440b000030118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 318252967 1250 318251717 318251719
    0x130e24010219060906050106050c0a120e030709050618070906120b1207060e1014070305160b07090918021009090f09020f0d15020c0712050a050c0a1203080411 70
    0x10b102d405243c00c001400f00c5160440d48141410300104145004030300f541d00c035520080080c4402480c03903d800301034042d241138076020b00080401c1c03045241c0342804408050152074001090504001040c081c000c0505080765105840c4841440000c0343d028980c902120320500d0500d600141e00344200000301001004568012031140052201c0746001c180b08003201c0d41600d0f807007011800e40c024412004171181302c5000007440703400d90348032108003c0701410f1928000d240c071a040c8014680c00390204030a181c800c2c3c0d8035034081401c00210b01d9008554102500441a05011210311840c0f051195040050000c4c40341c02c4d21100c654000740700300004802054002001d01c900350381641024018020b051069000f5403103461210307114107080c0b0031078840561044c0d00f84510b9006400f000c00075002440d85900303901540034002002a000b400f100040d502480c00350401c0401c0c1c0c1303841d03483d0107040140103004074a442020082001402c3c0f00c1d80034290103041c16092641d075482c00001c40000d000040d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 318254217 1250 318252967 318253003
    0x14030f070509120c0415050f190e04030801030b0705041208070f0501151707032a050a060f020d110c0d05120304060b1003060b07060e0f060705130e240102 68
    0x4080c0243c0028000c81004c4241c5040044449006150311003450501506030001800e05121500d07080ca00e5802004141c0303154a900703102e440d01004080d0840c2075070300750001121000188144102482c1f1290060554100f05160500d81019100c2e42503410b203029004410110740c0c4018046001ea10103031155200f0000c00c11211030111002043c8014007881000c0c00c1001d41e00c0740906c2c2c0000c0c9800989420640d080700e085000c100000b10501900c1e0610040d00807400c0c00a2141c5070080c2001c081c00315074841034181001010002e1034500100355100030081e643e801d141d108440030406141148040c0c81841d994040ca00707081e4507021032007138030800d1004008100000e01c102c551022040c680104d030640d0603422000c804900b84e0707003280074290302c0860401c0341e9170000f041176020400741c058000641c0d000c4007072042440c0c2800d10468049010400014452043c90342c0c402480c40071301025072a0040c20b080c450248500c645010f100084510603240585c00580c0c020040e6150341c1c10560b1030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 318255467 1250 318254217 318254239
    0x8010b13210b040b15031605060717160312140403030209031e06040515010e0c090f030604030e0301060b0721020c06030406060603110a020a0f060b27060114030f070509 74
    0x8441045000c45030411640045d01c40d11000b490b010401848401880c0c09446ca04c40c1007404128140c0e00c03204080780d900b004007a0021004901e2000b034600b0301c1c1d00d1140b41c1414800c60030050320504090400706102454124606140215844420340080d09407900580743c01d684000b0a2403d09c008010750b01901940c15045106c003000100984034501c02c0c4d060302d4020202030161043e211080c020307003405100403400204984000300151021071401000d80c000545100082800c1c030300103a1302a00050700d6000c1e600d0880c2402d0152070010b000e50b00225107040c1254036800c00e1f4100c4154040b42884824160400300c51081120300e0702200018203041e62070400b864400c0c0148014400d10010034108071000070700070500c400b42d541885d000e4000d03020b95111541d9140c808a0310f1007085403402d9441c0450b900365101e2109201213400f000a1240741600c1918450342c1840c8010000fa041003c0c0e440b080242c0c09485c0140c1c1d4020a00c104040125180e810013074070306000b0750070101e41007812480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 318256717 1250 318255467 318255473
    0x7150e0703051e0106051008060a030804080c041a06090f030309031504050721060c140301090c08010b0406090506070f050a06090b0f01060f1d06040602060708010b13210b04 76
    0x39084422403c60441c2d8801009004159400d85015115842e4030152136003c544c50b03036020342c0581d80c0c0540010540d203a0103803aa40c0d0010726410941104410303a11582010340c10742450320074030501e200e84031341c0c0c40d00d000b882e14001415846203c0038035014400c4800340c50941e4a041090720501c100c020156112510500a01550604200c038240c0d824424140b00045546074040c601c00f07044080c2da600702080312291a4840500703c0b00e1050700c20450030305503450310b1040550183d8041c0201c1c02021403c400b0000f4024408101078000c2d201012042004008054100400070704440040d5031480d120003031814407088240b2856006042409500b07100c004002c1282c0c0900c00301072042044c400c0c503846148007070100101c24040c3c000803440103545c02c210b290088101c00709013034801210b161280d503940041012900694850700c0582d000c1c5040c0700240e604001ea0602420804d0310284c181078400a480000002505c03e102207a060029042000c00207142450300580e00410342c140c2c00d04080c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 318257967 1250 318256717 318256723
    0x5040f0201080c07081e070b04030918050606031b07080a080a0615020a0308090a0218040309050d1205070c05040e0a0309080d09050411041a03061c0807150e070305 72
    0x8800ca0024691100145104a40a0650b540c01c2d0300080014200725003105d034007401d440201402c0c10448418020fa4000481655005200b07620a88e1054003aa151407607a01c16451001d07840c0d00c05038100b404115081d2610303c12340740e10480d0b264403004081045040c1c43d0711407141c030f030000c2d11f00f003000100394009582040e441da0182d2000a030800401da910782014a4081444140713400580100d11000042449641c105800c07803c3e010070b81c2c01d894419130004020700d20310600418507501410401080c581c1040400d0018007080d104505280d940360f80e02d8814281014201d802c0c082c0100781c0c0c500f40001841046d02400024100b042402000c0d6180c550f14060410110b0001c2c0c460140401d101c01d001c90307400c81c209201c0d182c0b080c4250401040101405000d408141d14603024000000c50701c000c0c5c5481c0e644401100207484d62803c000c014807030081c00c0b000c1c918000080d007401c62000a840b80007240d01a6801006c6098003444404100000d4409102611041d104000d00842480008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 318259217 1250 318257967 318257993
    0x602010605180903030a05040809041a10080106020706080a06050a06020115081f050a140f04051605130b0d080a0201020d2301031202010b0301020d051801110406120f0504 75
    0x480d000350791450000710b02c4800c1101280c0081c070750307002030020070014101da42005030044d01c170354010790520341c101001c01c0c11034160310b1480407492488a100380d040d00313110030002e0810440389000791440d0f04000010356540400d21641042284100004203001041e904c404082c01c0028140c845070b65552800034042c1807000454440c0780302030701c400030b481d800c00159035101c4044441810101003607a41035000070b090003018446461b458406044d038000c0204041446240356585070030150606040032803400002150108403400340c0501400940d071031041618104201e0000814889a028040740c514450544028a2610003042c10300706136406402502c4d510700b6005040000d454884124514060500600c00740a15113000500c049858a0171a41800f40c650001040b800c075208082404ca03446561007030103403a911070030702c00499010304a20450544400081c03003500c08140708130900744980d2280d14188406441004a070300040d41008600c80120401003005d0710b428144000c0f42020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 318260467 1250 318259217 318259219
    0x12030409110c0f1501090c090e2502010c05070b04022e0e0d0c060c0203120d0c120203090c120c030f0127030c1e0203030304030909151a0904150602010605 68
    0xc081d0102540080040d44c0e621100e80804d004d0b505034a8100f030303d00180041c00c40c42c0c080084814002c6990710203403900c1d82c00741d40002000c000444008000c0303202680351080c16811079041078070001d2450740c40702c15a40d8064102014811584551000802c00c3c50b070401c0070008002a100b41c00c228503000c1e40001000d0b091a00c0d55400e203951441004004101c10f480140780440201051207018400c2114250b180c3c4082d040340d500c190010094400e503003001101615142d100ca070300d1901180d102c1c2d00c0300061401440150b096090035010140c40c0c40348405814041e03002c85529087d40f034030812100c4d40030140903040d5841145107180c014083d00740850038030007001c071000400c50f1501c280303500594019015031f41e088100350349955404041c0c0c220b051030810003c0d8902c083e00036990038402940203078802c2c0c46285003c0d00d00b40b012030540701c030500964441240400100107480040e124080030210345511640d64100f600c5c001802410400c864101c05041d80001207203094056101c1d0081c0d42e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 318261717 1250 318260467 318260473
    0x10201061205031b07050d05011a01210911060f0405030c060c0d0f05040f08100506040506030a02040b121c09050d08180d02090a060e0a0905030912030409110c 70
    0x1d25101c1c203800001003007000410b103500400c0343d44190031444e8002da05412079081600e10599540700010f54400d009a01034610340d544140d142d50312503c40c0f040c4003442d5000e08001c07d05041d007405e140845a50954100d05042c1c0f517a1301e44080095140802d0030300c090082455071074040d208000174103504140034060092042c4884a0818a8028252101398a04030000c18500800c000c003141d0355203621100c1004d1180510011070060402d4042d90040e1505078003d00c07091803000c4021040c0c4d14080d00290180d4030700b100b0f12225440c08642112200e40580b004502c0c42442e10110b00c2d0000e4400f080c0d0118040c1804a141601e03001001c1c0810311229a1681c051548640402444e800c100c80000c0c8081c1d41000121800a9030380c2400105880081c01050209510f801181103404115401d0080b503035620f40c00c0c050618a07641140e0084c405200800040d8015503903140d4074412422103a05c5181c0b004860304a08100f001210064942c62009000c00c03c40102030100d160044d40364006280 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 318262967 1250 318261717 318261719
    0x30c0b0c04030b0603152a0d0203041208010b0d0c1205090604140c0a0509090309101116030c03021c080c060106120b100509151201140105130603020f161101020106 72
    0x4030f00080c0c504c42442221b400e04140351078401d444919558402c03190300041205201c17030085a800c0c10050102000e031501e0240e5645010b01c3e1481c19548141c07036410a0101c0940144440c5510f00140c41a500e10050002041e98076035000b40c44040220060081850501003040709011000c01c0c49402a84151906801e9540601000c2d807120344000c1580d4020416402c100100c7c035264000703c3c1c00c404114166803411304204082141c0c4011412100d01081000c070009030810310801040e44281c1d05001000c18240c10350303444081c4c460003032001900c030325030303a280c0b0184522100d80500d203925032100e211595203001034603c50304d410f401d1058501291048403640c80049507405448040c1600a010f04d1508440030700955260700940780291704248802035910320411104010038510520081444080d1300d1305240010549814000710704004050090b46002c000c00060001602d0050a015880f1031301c880f01091701c0d0055018207280e4144000022090211841a80d0004082030380240314079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 318264217 1250 318262967 318262969
    0x3060a0c090b030103081204060209210610081b041d01060503060a1b080c13031b05040c02030a050309031e0904060503120f0306030c0a0611010501240c030c0b0c04030b06 75
    0xe000900c00071b00240c0e020014543c0c604032060102d5449072056600604003450305020a206817034903d0103c049031803030640d140c0c00304000c000d00d9500c040080446e00c000ba080102c0552149080d80b600b100081420007030740290740e2140c100d0b103030080181910702da0101c51356802d14064801d03441541c0c000c3c010b00020400c0c03004140280910789044811024042451190807903402c04028154890842e0910131701d2007030070102d0703140c500450003048203088a1000589403200d44803145d1105200b00c0c40d1200001c942078002c401d488904075641400398030381c1c0d228901a42903101d45002d100680c6031010400300550500409010051000c0c0c50810507070342c1716414907540300c1c40c0554441d490382c02404440c404101d09001160b003c4009410303214641d140300d0109800044642040f40441e4074861404c180c118240b20300b500400560601c0c1810078056100201c40588000c00c2400b0044181507600916020340000341c441d50f80000d000002d841c0c401900c007a41c0e00540421601101e20708085282 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 318265467 1250 318264217 318264239
    0x4140f030d051003031d010c020a0f08010e0a02100c050a0c0b0d0e010e0613030e0d0b18030a0f0804031707090611010b06030703050910020705030d06060f02120d060503060a0c09 78
    0x41c2c82e490b80b120304c040b48006c0c2d4402c0700400340d10141c1b0304108031008510b0040c0c071240809401003001c10000c40c101c40c2441042070a4030b94141e00c000e5164008402580540c0d51540a1000c4540d9420038100c40451800c040f030800101c01000303002c40f1107806002a0b6015200010016000d81550803c84d00f15880c0400d030a890b1891030011840d4400790100d0b610642c901d40c1c070024644241400088401c0c8600400d107402c41c100024ac0300b42641c81c0422603144803c1a042002210340d1010b1803070706001c140701509031f408401111040020950015041600034125041020000c8540c03c800340b0f8200001010840d40380501da0014900890901d0040c0050240b0442c10000501080c00c554601c08200d00414006100c0070045c8600d0708800740500c41e40c4001c0241a009001440d0703142c80c40c444100a0343c445034010800c0004455446007007a078086034948180c0306400301c4995035502400010b028140c01e4001c0b075494010700c4144815030f1060350000c1e52034040341d19002e544544ea00c0103800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 318266717 1250 318265467 318265469
    0x6032e0e2706070f080a0e01150501080606040b0708030a0b030a0605010312090303022a0d0c0306140601020312040c150206040b1605030a020a0c0b070e1813080304140f030d0510 78
    0x10440c044e00200501c1d001d000d407907510184007030b000a480100e05001e1400c1d00c1c40100c2001d1080501e00d4184050750780f01d9109640a9010340c0c0c4d807490540381840c0c0c985140b0440202408002010000c5940070303000780c100c9200341c10000c041f9107246140741000e60003481e003844100d1780c08800146c1940114001c0005a0803640c25402424000550003c2c1c042c001b16071001814850f0300081407a14107551f900c00030b90825000f400100700050461800401315140d1840c00c4116241501c200300150707030b001088422030544203c180c03000d501c6500c0d0082c019042500041d00310901d04401030700b4103a0010755280b145000703801c00e400380d444002c0c04000070300710561308000142d01040021200d0b05150014142e482d43e61610042e500e116880303030142003105076081000a18601d090307038070600e456003401d12032856001c501d41c0142402080c0542030f01020b14000d290400102c0001c0034000c05c0c6205070400710005090364120600403000503102d50222511003101490309011030003102c10041200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 318267967 1250 318266717 318266731
    0x30406022d0904091b0f080c0105070b060d02040f02030703090b0f060a1509150f2619021b06040c0806040b0a27140c06032e0e2706 58
    0x80c90912440c050101034510a40d05a071040115090340c811170040a01c0c10009204010b0b24181080c20600481c0c2020220103a2a0401030244081d80114a22401c400d4006500300ca88030f404031120710100340500707103800104841603c04410001c0480e0541c0000818500c030316084c0c030546e62081c00d1803c5c0c5880940f0b1481d0000182c040501400c001c140b0305422a071994142400c00b150354082c60503a01d903000001c0070000c2c002c1801e1400d00c039005041c0c1628401e0080b82c0f98003591400d1042a600c07480104141070504081007541804805941110b03c03181f60094040440a040c44425a03600070550b003c07618141c180b440010792800100c0d0850041e80c1c08911400203469502060014083c0200f6090b100650a448641500d2a070780746080c240e482810100c030b54010000c104d50910300c0c1c40500354007910b401c000300415a08400c414901d00405460a01c24810314051220a4010b03da0070811209622070140a1080400107040d0031952400312100c981d078603114030307960301c40b201510a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 318269217 1250 318267967 318268057
    0x302091306120803071701090603020906040c021b060f0301090605090c0a05071506380a0e04090303090803040b040203010b011d0d21050316020102071703100b03040602 74
    0x500d0010301c1490045410107240e01d0910b06c260b8040b41105030340d00e801e902681503c2d0341c03403c0c104214140f40c81740541c001c201f180c08111801e0040006500da030b20741079420044007041442031000d0717a80c035070545801511402806440351707182c3c0c514000901160045a03c01c0d0402e40c0000c4440e002c41040343c0340f002c410b6581e103091401d2681c5804409004410888516444040228504282d81d001d0b04070b00ca005104180c6001e10031504c0e8046550b40c8540c1d08001d0700802c54050800d8000500040280d000c2e940081c410040c0e05040f0b0041c652000b004045030070001c18002488800c0301c074140194001c50007005400c0c190b0b0019100b2050070080c0014005503050701c03800520b00342e400d04070707030502800000032a500085074250450b0003081d801004a80b001c0288995091110302040074a0b40500003185480c1407902c41071156020f00302107240c0c50900100217860240308c00c110390000c0550450842e20390403d860194046e4202690000310110070310b00441081c000b91140c0c081c0300f444040380c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 318270467 1250 318269217 318269249
    0x12230c0a06050f04051f031b09061b060203011e09020a090509060d080d0903080121080a020f06040f0204050702070b0d0b0f0d080307080112030807050307110d0302091306 75
    0x59031150049880e20310f03001c400380800103c07500e50039050040103040c8100002100102680901200d1481c25400300d281c002115840e031050f0004c182e101660002d0034103811070306100040482d082e118bd0001000c85002000000340b0081501d00805082c20b15111901030320707100c2c68180200e00411205400003940000c041210b030408039542c940107080945107080e4100191030b0150140c2c4548903e0f1045943d400b902d809240e444203540b03001d1710888134000b8040300e00042c603158a440b0307848050040907001070a40742c3c00e40200012080c401d960401d55520f881c107414110310514070800e050b805981820006010030788042500801d039424024101c0c1440d90240c5500000d080d81680d0300d0300301d03c1030032020301c0941e51040b07201003803807007801c2107552441d00340001030000b00180d01240e1201c544002403400690000d0302d0a500001c0ca2421030303100d81d1050b00880b01183d1102c10000c4038090105940b01803a803540040131106403c3c3c0700170b2201600421303210101c440610130303034030880003c0d0340c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 318271717 1250 318270467 318270479
    0x1409040504060e0601081b0d080406030e031e030a0501060201140121020603100512190803130213090b01060f021216080d0603110607021f020712230c0a 67
    0x10089070010300481001808914042d000c1e80381c0642038109107090f41c0041c035800c03280880e0540c0b1003980c900690747d0300880c6606646821541c02103001e14801d0545500601c1c0320303280100140c94103452904514030110034a2000301c0203641c000d4610103001803c181c0081180c40c014040d4a4015440200b46081a86080284050004200b011914440003e0b44860150f07036804c01031800703075841700203454407a481d040402c1000b10300303030016a01d1500f04945030460000d1183d8503507401c03034100c144246d49035200d68580003032118500009520031040c12a403001144150700c038207500392141d40030b2a03080e602c80380141c80350f004c40c034000300040e0310212000c0602003041e0068011400b0000303071000f204419503141000b54000786105c2e00a0780d036400c0204240a00605580e40400c0700703951700d51802c1c9003038005c81d0343c0c0b507000f81c1c540d0703418001158150482442040303840d0042850f0026411110b10600c1c00354240019214401032f441403c8000c0710412001144482000b400101400c000c43c1c6004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 318272967 1250 318271717 318271721
    0x20105181c110114090f010504020303040e0a110a030509070911090d14120a080a020403020603060f0111010e0a0203060609060a030b13020402040b0307021605030607110c03030c0c090106140904 85
    0x1003088400060403030141d030240113282d10107218004210880c0307042a085494420002120421340e0705140510015840100c05c48055034511541082140d0b14440400083c000182080c60310210000d04000107980c59030140740607205010503180c0c1c448e66a1402d000341d0300a0050241200e4040240072010710f409100140c0d228890746445149909440c00c0c1400c000c40d8820007c1d1007400080c0c080581c9030301a210035401135000c1800c5081c2411900400c0f61404028a4140591040610841c250303028159940880200d031000344004d413080e00825440f4002100200e000340304000c0840c10f203107002c983c003500c150005403000a50600c6c544455400c5100900315a000784032810590005d03032154001040a40220440c4503580e04104400030303d0080c00420006070540c00480074072642c0e90105290f07070022030b80e140003070b05284416040c0e420010300f07164141e4140f00008040c1e041d1100400d80d03039103044040740d490a4580e40c0740e81c240c1d280040000d20030792814003000066071525041e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 318274217 1250 318272967 318273013
    0x213091a091b0d020306040b01080706020105010f1401230423030604020103021b060405031b1603080c01020f13050901060f0207030b0c07050109150e01060303051e1204060207020102010518 83
    0x10100183d00d202c9402180c10a0b10070703a802c0ea8200c085000600c1032040810602000300b18610003000190725000761030407001700a00541003144140140c80c01d00d60322410b0340e820441500100880c99902c0d000711342c0c00caa0702510500d204200c0b052082c5510340c40d0b000741c03850b00741c5c80500030742440da0725540110000c0d4000c00c0e42d59041003081c01c04070009801080414861885813005643e030b112540c0c000d10300e1441d0b0000700003032170b48009120350303400340c2c450142400c590348102410f444c1c08001030f285000e400382c2e98a00c401003030003144a03030940b880d013101001190800c4d00e0b801601e03600d07880215072915010000e6070240e03006d0441000081e6840c4491984070a54202040c00c1ca86035031b0b03880e420b4078401d10080ea8201c6482a071143c28404034426042c00580b054003c114061940d035010302103029a0511080340000345c052080b131f404034a81100c00360a801601c0388601e21346490104029040103030700f68010f44c81c0000180e905036520203104491401003004001c403104803505d0107209410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 318275467 1250 318274217 318274219
    0x50a0207090f02070f03050a021b061228090b0a0605060f0a030906140a0e06010f1703070602070b0411011b020909010b10030b03160b1c0204030213091a091b 69
    0x3080044c507010036600300e60780c0016486651583c0d0b484801d07001c000d140c0101e5500a0400701e002344c2c41c0f80b10b40d40c0c4030422281c00f2008024040010303520740d07010000c0c280ca58201c41c1c50003207041090207550003c0d64800b0f5001d42c8035030014030341c46d2a100181da0843e845809140d070000020050304c0394600c20030b0050310030001d0601d0017003100c6032980e460704140d5161100138040c80c0c00850500085d20342900841e80d016060000400702c80d80b4003050081c0d070540501c5014074148680403440c0d908074041c0202c6800341d81010382599265000c0c074010841440c100c506813800d071b8450205500b190300c43d803048060f218000c0b840c102200d03c5a004c000d0014406041000d856617148039000b1152506180c000d11400b00e43c50010f0007014038414107044c2a007201c1c9809908040c0c5009010740301c1c03150705480802e1100ca10340700d003082c1600b103e0320080c40386800107548203824140d0390f124070314140c00411809208908103d0207136180c1121030010241695860496001584030b0580c409202d8514117020724 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 318276717 1250 318275467 318275471
    0xd0e01050f0c0d0b1806030f0109030f050d06170a030906031b030b04021611150313030c050a0c15091707380a0311181c0602030a05060f01050a0207090f 67
    0x400400024080f4068191701d4030714138221810440c0c94076080c0601c40e140c04c0010021301c64910f06a50081c20b43e4802203100081c0000490810300c80d90099001c00e01520848a130503001d541c2520340103586922800c011000188d8608011402510034000c0c1c0388040700d185a07440c0000500041600071b41481d0070410342040d803c3c000b4441c415101440384070214081c1d02040402e214202c00d0080e81000403079000f000e0b000410034058000c030882c0e0345000c8290946000c443c07002080c80c01038100b408114000d00750036000500070035011400110810268a10f40703424420a43d2440500116480c0da0783c101c4d06900b00b148104081b20f07003501c6080420b00c166644200b4194a890100f00c0c0400070752210a080d08007207000703500c09802d482035034500340750030144909107081c01401620321a0300e2580c1c280074102c0800005001801c0144281c81c0c264005000c0d074403462f0200401c0020402225468400e0303d641042609030b50240c0210340706c3c007850341d0280900b0f0b420412114041c00800c00c00902c903607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 318277967 1250 318276717 318276731
    0x20703030b030a12020111090904021309080708091c051f020d0f06050907110601090209030a0804060c030e09160c080405030106030b040605010803040e040609030e04060b0d0e01050f0c0d 82
    0x1d5024803c1c001e10302d2140c494122264480d280c020308485100b200d2210003041003000c090380307548442c141d0394415411500c170a0007945455101c805401056001080f0050101c1c0f4602000311003c0500009801074448070140400c0c0f020445400046460180c8180c001c100b0a240c5002e1860441c0c1078081c0025016180241400031041101e04000c1031404950341da000a114518024407034540042e0345107861900d074408900c119480f10010321400c02c150360700060081e00364500380654181680c2041c01240c559946031070162180c4000d0b401100050f0702a6031910b414500051118010040700707020041c00c02c0c000310269124001050183c0d26154244000039141c0d03000d004010186110707550000941c00d1074507048007619410b03003100480da0402d000c103219118881000c503074019000341c80801c420b801d5080c290f0f4000c2044410640090902c03c0208080e91240000d0440c00d042003410466258160b440a0072178406454030910401284003184c0e41444840103006804030510000482d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 318279217 1250 318277967 318277969
    0x9020d0b0604151214010c0e060a1403040c0303170403050306010f1715090a0207260903072d1d07140c0106140609090105040203150409051605030706080a020703030b 73
    0x51180e82d00020145101c6040c5408001c01c000848151032142c2e170090018015400c000391801180306066406a003000c500007060a12400d1410807212107510381d80e640b82003a0502d00407000182c0015004600c0c000e080008a0000f40c00300c5101d1038040d0740745406c40d00c0311f034011181040101c0240d0204000d140c0a010180003281c0b02038005c0071100280c048124108052050f0b83d10700915558800e8410b20100c00400c010032200c4d00311403448a8441e1207500c0120000015000300c00c0516054440c80d040444c03110641d03041d07092840c091440c803900d0940d1164040a800c1c071203006144e201e10705420315007200701180c1802a003200d118101350051100c801407540300c2d508451000d01c41d80e074494400708035001000802034034265040c1c0303103989080514800702e138040390103100d4a40165400000a100307287c10143c1000f00180042c818071240744c407410010f94070703a94041c2030381070075040130790004292400003030b200225007198440250960b9110b039180003c2d005044150145621182ca00c03600e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 318280467 1250 318279217 318279251
    0x2150c09032b030506060f0a030506212503080f030a021b1f05070e0f04020408030412020a0b0c1c051e13060810170a290a09020d0b0604 60
    0x242000800c0b0a074014080030300040c192a0302800b01809642c0c1005000800c6203070030212101c400c51420f0225650b120800070901c0340b04035a240d907100d0001c5024842d81090041201046210018001e0902049c003a070b080001031507034400182103420401842030860401c801640d071001c1060b100501f040b40c20300075100d2800419110081d0b94105c0c407044510b080c1c2c2c86081c0044089a4030040100e4a003d150150010799507020062062307400c0d40c0707018519a02ea8044902404c40042583d49496654190303540000d0241000c911404040d8000f045412074017094a0305001c00b0001042d00c080e04171090b0042c0410b445669040110400107000c4240324440c0000b01c209200c590746940c2c28a81e168090300b01c0c3c4c6030300b01104001444050016040c854926202590003503080b210301141c00413142454028401c0c002030500c1c0d1842009000e060440040c0440781c500700b035446281c0d81d0303842d141c0302c11203120400003940321156214400100e1004020154000d50107000020740c8010f00c520b08007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 318281717 1250 318280467 318280513
    0xa1403070b070f050f010b0105030f100308040602010c030b0f0f100c0b0c0a03050a05010303090b09011707020102031e010f03080705030c0601080619111615020a0e090702150c0903 79
    0x24001460541d4001001001c200717022903d9515030003003100129001c002095444043c2412071110740c0b41d404602064200d1070030300003c40d0f100700019501e0f607480d6400ba010746820f00903c404246442d482c1600c90910140c10b05452500904800c00740c2e4000003008071f000712010081040000c1c840c0d1550011b5140c00459003d0420719100940310410540001c0550308010008062281003400420009411000d94000d81c1c01220a0a0300c4017450001201d010303035a244c000c3d4a90120009101c1000d40640c000c0d4002c6020200769988020030380d10f82060b0074000c0c40b07032148144080b1010400718600e40701500c42c00703104100762490041c0c5480c84501c2c1c06c10a8000383c3d074070342103401441003140300034409000050070840c0034002c0c1003141d580b07250203010790045c4d403070030aa1f102075440400c4813240c444c80d03601d55140c104544034900b10307100801c00400306a440340908400808104c0741400000e07954101004a102420f0a42d5110600b43c025085030103040c2d01841108600e004100700c00031154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 318282967 1250 318281717 318281723
    0x80712140406050109020c06010e07030e030706150b1c110705010527010b06191b0c15090803070f020609040609150f080604060e1c05270a1403070b07 66
    0x218403401c10342815803c881041e480074404500c100420528103e011600d1030455560300e00041c207540d00c440c02a001740222a0458401c0e000014900c0200a9a039218550b6080050492090f03035448284092080c42410b41c01404c03203e80c580300c0129070b15030390031a1000d00100c0d03201d40d0174036002c0d581e1282910810342d60f00300e83c51810030541429152145c42c90700383d50403c1c8000c3c0100050240070614512860440140003e03180041c96000340c0520003075018180100c8440300712701c2e21814240c4e01ca240900032000840200c0c284c002a071b512603000541507401400145162050503079030240f0122441c481260000400c1c0700280650344c40d4480c2200070148090003090010a5014000d8194526000381800d66103111742444040700024565034000d502400004240c0359540080d45400b01425001c6c005404003440e0203841a072100140030006800c0c82003850ba030b80514071184a12038245001504141c100008001100c120100d1418051000d41503e03049500d80c004d81c6c1c401d0384450002c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 318284217 1250 318282967 318283001
    0xa1e02060403060906020d0c031118210a030807050301051012090803010f031b031a0a09050304141906020303070f050903060103050a05061f09050405011d250510080712 74
    0x604e41c003c0e8900031143e0010046c030b41044090030ae04c107802460f00452079141c040d03000444401081e9203460002c079041c81404442d200070940b06060482d901c240c44401140010003080c081140c03140510140e82c10f9030340042c0349158038030084104417540d84d4008442c2d920161120340103400300d0480d000460107071005014008443d03081d4101903942d4007175090a480120040041003021850850421000d030070b105050400716125003080202500c541000602180400a0b000498948482001c0b10226065603401c036290f00202007100247c542d071013550056081040000e040c1c511410007810f801c0040c1c1405810b002090000c6071500c0d42c00d820855881e84621703074100c00c0c0038040001c2a03003c021441443c51905009400516082c910701c18110300e075440e040401c081000a40000c80078405086001c440240e40b00c0c002ca83c2c3e4446014111007200780c41001d44d00d811703021400034081d103501902d0030550140c00d0703c080356000d500a20341410411800d44000c0c0d240c080c1c0c01102c100c0446a885 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 318285467 1250 318284217 318284227
    0x7020d0b150607120503280902010e040c0f0302030c0c0f07030203062503090c0b0a0815030a030e1e090108010c0207060c02011707021221090a1e0206040306090602 72
    0x60410640540c0d00322442076400380b0401000a0740c084602c041d401d424907245e9182c2e12070384100700c0da1002090141c0603100c0c00c581c2401c100f15540d8071049485001b40da0742111851060b05003c1100c1851944100003a2601070b07801880740290000d6820003801c40b0820b15140c0241e0341c0c08d00f084070502d255105030b000001c0c2001946005c1008641103201090038030303a00003e050f0300042c1c00d0000b0903606c0c28543c80d95024014404101c0410004001030041e1540e1384d4103010000341040011034014a440205102c01c62050400140e500180b55160721080c01000704a01001000800c650300d8158940f4541d010404540b2881c100c0d41c000d04464001141481480d04042e0801c00c0e107812600030800e0500c41000940e07800040028003c1d00e1541e800f86a445026080741014034048031685a5000000c11400e8898240000a415910402c1500c05a2129071000e13071a80c00221020702070940b52015000300c25103d0b10500c0c81e6602c0148440c6c0f9081d030382d95590080d030318054000d80302c042e40498 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 318286717 1250 318285467 318285481
    0x18151b010506030f1c0f020715031b050a0207031b05030109030c1101020610060f021e03070c0b03060607022b08030106031d100b040e030f0307090b13031707020d0b 72
    0x304042c4644d0303212001e840d41c0303060b04000301504c590604508082140461400800b94001c5c040c1034040c00b5925144900c3c0d40107108090090113104a070213090002ca101901c240300d10503019a2030038405903000e0090180f41d5101e1034140840e040d400c550502c54180005032039642403140190061081d01d443d10601401d00b00405440400300c0d50505640041d400c1241003110355140006988680c10800111518806c04034600700d111020302d02c00c560550010303640d041d4000007a00c00b0602c02d0042190864503016030603030302d001c00ea4000e43c104100340000001480c140a2100407606c1780001100342c1508031941d46401450389405503034522000005200c0283c1c907000f00b040805541102018400035003038000ea0320411a5a964102e6a407280e1403011962150400e40c0103034031120480c0c1c0c80d07000d21129184603610944158010a40b0b89200040181c000010f85003208010180c140500d861600c507141403049500e442e030450321041100301c00603a1003a1404900a000d030902c0001c3d460600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 318287967 1250 318286717 318286723
    0x10e013b0a081e0a0b13060e1e07061814191211010f0206450105010f08070b03270703030f020111160206040e070e09070518151b01050603 61
    0x35443c608290800c05140c4041181e03503143d2034100e03050151030a10301c1c00301d040440091901c89558452800307004130f110a0300c12101444030015403800256480e85030b0300c2d070041d44d4022003488612071207240c044003006558080c4c038a807408404042c061070b49850520b440030740403456a8003c0d0240d0386900b41038030180200c014080d44000000c0c20032141d00800314502039075903200140398010309109404010703210182c603541003000c07195202c0d02e00c0c040040b80c1011010743c00c8103221a40b01d5864000005549010f2080c50400c540d100c802409420741485104100359200070101200c0040c0f20201d442c0307403012219040c41880c84a405083d641c0d05520340185102401a50101103a040600140f000c2c4d01d01d108980e001104c43c4618492250b540c0b000c00c40300d018560200b15000415010410490b4014510000f540021136080712a0340e41c52000f5141c1d4011211021210140004082164144100041c61318059001d00794201140c0b5201c1180425044a0a00e41039440e2000d01c0440c1c1020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 318289217 1250 318287967 318288013
    0xb04080a02010e121804050103020603240301020c030d14041205070318091e020a05120a39020303070512151e01020c0d081611040504030c02010e013b0a08 68
    0x5c5801f80305035403445c0c001130014000a8a00080d10002d403101300c1203810b032a80368000048021f40255150222018070f2900c84d00704800f00d806050410035403401e1620780c8061303d4030541e488140d0786100b481b00c40d42110035410845089003403100249104010640703e50f5600c00410900d180454406000313180d10412a01960300c0c540030070b0042c007150203100d0b0000b041e42d100a503c50f5892040396603035804035020f40350f00b440603040045000d1080a40101585a00a49071011407150901803c041c004982d81d2108645600016000344003d00c40071001064841d00b000c050503090a82090500000d034a06414480d03181450f50b001d081088603580612080d41849002c440020100c102500e409442d0311440a40501d0070341812010000c205550000951600c07010300304200b58602454040d05071468013034217901003101d4a990024561041c14a58070a080c20744012200c0b0310304c000c0746541030a040410042007085818007189030b48807440040c5c01400c6100040641200443c4044054a10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 318290467 1250 318289217 318289219
    0x5010e0105190506030a02070609020643030509010e13050a0c050306061909170105010918120f0203040305030c0d030c02030a080f040201050c0102180103050a06030b04080a02010e1218 81
    0x30402d04111943c3d61100303596200382e041c1d0000da500c24031460322030020f0039450380080d846500814038000c6846020b01e1004408181521222800c0d41d5140d80c1e226a04688080c2c41804140a422400a840380002d002c6070f600c18141051040b601c000020b45054844485550f0a5624406c2000310341c518004c0c081c1454490400034514141240420b8061103000c09024004402d940d40304d280340d204000007001007044120300084103c2d907191643c081e060030b01c81c03901d0342c41c03c008a48840410500c800c0c092035900c010303060f040b0060707000261459a42468000b0540c001400000040354041c4020414525488041c0c050301c610b488015003101d08a075180c0301150300c1400501d40068020052030703005402454610065662880100c99a1182c14a26807081d4004100080301c40240e034003400d80e006090f2802e00031650740f9612101100d1031448041d2440320320070003080106081800030444121b840c80045414884402058a07180c450030144402150000384800c000c3c00441c80b501c0142d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 318291717 1250 318290467 318290509
    0x815060d0f0513020306070c0201120c180303030f291318050705090702060408030406020c03091c051005150f0402090d0f0311011a0112090c0807030209091207170d05010e0105 77
    0x2340d650002441016801d21004800f507450120b0300e2928042c5110305444030300c0054444006460b03180c01009002c00e100020307070003410103180a1890650800c0c80610141c0c2c09444081211018200151108144c040700703040c03603603407a8081c069410300d211a2031440c052402820030b14038050902000c1403005241f80b0454111109000005001c03000b10f83e000340c0c100c40050380f80d007804088036007584103c01c11031f0b45c800542000c81d482d1030958405d5201ba00e005005456248402c6400c6130290740048030300108441040d6114100e40c41c240281442140018000508012544002c100d03040203440f003d82e15980c0d8003c141c0700301940314803224082d52280c002441210040e40700400c06130700001041c0d05104054031803607072040c440c2d400410510340043e0302115156442054644802c09400305038040c465110018002110024889554500c003183c030b40d1400410344c842c0500b0700040c1a034440480c40401c04451180790b1402082c0c060140c05c0411041c5501d040c08001294150403420805c400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 318292967 1250 318291717 318291737
    0x1204030b0a18020d0606080712141b040f090f08031006050c0714220c020c0621060604030506010e0a05090a02090103080a05070501050c04150815060d0f051302030607 73
    0x40754540b4182c5815410b546080402e0500e02d0044041c001c00c3d04142114840c00400050a12000c64020442400b91000c441c01d10521103d0580341d0111002c5209480c900480142d12030800e5442001010000b440020322f42c0d501d95110702c4000c01035142520810004014828090344454412000b0411400c250b0700e01034584e01074581303400c00c5218803030404a00da802c881c1c0039100e001040000c404a07100b00c041e81e181b1880b0110040c0502c4001ca401480380c12905011802e04c0b404540254195100c0628003000d00c2c1c3c000c0c010701d07100400194014406020010000f002040030a02030504c0500c810507510713000e60300004491005145003402d5000209100150301c0b11000c45041d45d422200c0b0700d80c2c0f00220b41b0103881074829858020b01940c40c0404000300603607000080d0050b64200c10400c40c203008030200c100c03908075098914007003215001e0000041403070008000c0a1201c0040c0c0c02047c0303580d489000e0380480e201211803611042d2880e4400c411807605203c1540d0199440c285410702d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 318294217 1250 318292967 318292991
    0x601120b010e0403030612060905010b01050f271201020a1202042616030b0402130c12020304021306090f060905270304120f0302100b010804030c141204030b0a 70
    0x603a038180304000e901d0901101007802c0c180300f030700090043d022085900020290394900b01d0000c1014403010b8401d035203070105007080385d8410002c813504443e84245081c10101d040f4844503c03500030644011080030003440b941400e0b111100701b0241d0914400005860392000300c009020a9031052401000c148100028000711189103144404142c000350149054055249400e14000c00c000c03041d4161141c00000200300922052002d01c22842039405503a03000390000a6002c0c2c8002d6030203503010030281c050305110940d2545c045c42d0701500080951000540822401e800c032101078210a0010740c07201c24100f002e80c100d016290003049107a608000070700e807098850440e07907002d81c400c201e0004c1c4548142405c0381d007042964080c0c80c401c01503081040c3c142c64039a00d003107100342c0110094026407681622486203440f50004c10300d03042e1a1413000c2c4d030340e48e90112241125050200e80450201070100103100e0104541d1140ca0580d0b400150b0b56811400c000608401c010840c0c44c0c0241452400045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 318295467 1250 318294217 318294233
    0x17060118060c0c24020c060304110108150915121f020a03060b0a03020408240c0306011e08061801030c03110d06141618050111010f110c060112 63
    0x8980507441e1019002d15245010001c61681d0780c800c1042c40c0d42c0009401c09407410038101c2d4184c61350f50302200c4d030400c2c4400621a00d4001141c2c0507110010759101c86030b1079409100e050394451610a4207591100c070150000e80181c1080e60340c0c201110001c00703450a2030030700c07905454901242c1c40c018031a440040c41a030001c117161003a070001a40d000305451304114000d030000c80240c0b000c420019101c86640c08000d0080d00030348601d284d58800c2c80880803090303151803101d845010b40003080c060190360b401201d14281c0e02c094582410440e44008918881c2c1c01005055030030308a99490a0b039a08003c02008807004000e070740c06950000f9080100001400040f00d4812250f002c04e0b05c06c0883d0a00d00010741e8950941c0c030141c0141d08101e00f0364207014a100346644115100021482c8003030b00100102c9400840006020800b20015401e00040d8020302c88a02103510000c004182c2c00c58840c010400d8030b82c0c1d84100041600d0105076100e41c00d000b402401c1c0034108101c0002e140341c01c0da443d1808 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 318296717 1250 318295467 318295469
    0x106020f0a060b01090b1809011d010302040207030c050f0a0c06180e0603011b02010903091a03070c0c0f080c031c020d030e030403081605060108030306010f1b0b0717060118 76
    0x80c1558421043e40c240e406403507054000c022000030b598807503645c6103100320b0b00c03030030b9020152045c441c0c8400404d0712901640d140324100c40681e0f400d07a940e800c41d800d00c4000c0d403080380182d0500000c003c180000030400c001912509415030302a0021a415280005100301290010b100380146c5490b1521000c401c142070b0021500b080c0541c1d20651078030404a0700400c81644042520030008160f00c034525015080000914420350b43c10429556500f465400c0040e06540755040d00010008203560a1040200d0100d95004d5825032800c1a519082c42044600b603520000b0503412645404115140a02c1100d0303040c1618082405807510700d00009486012025142007890b0ba1501d40100095082054602a540c002c11440c6d5480b61208451598141c20030100c070184a101c0010442510200c00c0d28022081070311407034a50706600c3c500703841c50444c03001c1e9040c4012103c11108081012000c03840c1c0900d800d611008520b8521075506500880e0040005061201008924035003141c0d04132070340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 318297967 1250 318296717 318296723
    0x15030f0609140309010c0605061f050c07050103142703030108100b061608030702010e0304060e101106060d0203010e070927050604170d0912020708060f160512040803010603050106020f0a 82
    0x323500c0d82c0e400000340e9100502030b030b1394011041c0f010302c1c5200c181d08480140305090040040b11503640e40ea000450035501e000641c0307548a1060f00108804192058511688c5405d036a054030380c10081402e820310f1504244e0003101c1ca50301c040d12001b429034443c07060461490007600c41a107001e1900350340c1e40c00c800c02c801009210400c00400034501910030b52040c0c0d02c103803c8100f92990346690710001445840007070200d0b40300f40e456005d0200344070700641e0051401d101a102030f01203680d81c0010400349503011401070f601552141c2c90295858002c1c01080c01034480028009007110741490039a00145040c55a15449038143e0100ca003c14400030790740350b125901000032142d410700da1890f00061f00a034050043d0207418030f840e0070108800180d400c08250b8682c0e003210207056440116994440d415500c80452088010100384070403800081c1141044550030911b250103080c40c0150344021007254107680390100803006102d4241d140c001c1600620071480206006480f480c0415202c0c8540a801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 318299217 1250 318297967 318297971
    0xe1206010509070c0629030d0f030f0209130203010e010518010e130210022506090b09030307120305151f0f0216080106030b06010f020a0615030f0609140309010c06 72
    0x41c0a052149142c2c1c0d64191744174600b030081c01e50440d641314501c0140001012841c0120f0418121410002010700700c1030815030310303c441320005210540082100c0d24120076281e8013004214040d4031400c1e1350040109403604016070f00d61500003600159501078112503c194004c0600c0d164040c0b0740d03080c0ea41036a00d0410417180c0354a500c00034000107000d101c0c0007904040c1c03401c1312100f06038010400ea5031141784d80203221100418001c0a9550442c0c5001d030802180000006001d180700b41000340c03d8404010302100c5c81c10360140c41c1c00c42d860350031415000c0000d88034410000d61102e4000d400003e03480c152408159484c1030000e18807804c1c21440b100041005000d42130044603c20002041d007151a5401500b00c039440d21b19040c041d0030540000c0c2e444a180340003056044d441203100302c00f2040035901615280000b070b52900048c0481d24080000d0007485200800412102e00e52180c2c854401d4000241c070569034541a0080c04180d14118090382046c00001c0c8240d030820306199900b5401900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 318300467 1250 318299217 318299221
    0x20a020718090b1f030b010e07030506011e180e01240f09030818060a020109030818060112060605041805060912161401090f0b010b04082119020601060e1206010509 72
    0x15901d899503051744040c0c40150030384000540c084d00010980c1c005d103d5540c00740f00c03965400c4015200350381d14950651780c54110f2000441d0b018070415108000c0800b03e80703003020707890ba1003400007003841007a0044420006194020038a601c074101905c04109a01e041c4400b160b000c550340640000f05c1448050501d50300000c1402c0400d81d02220a400c0c1400103001d50386940c01001c0080c001c150550b41200455005804250030651190240ea00a1140c4004200507030901e0801c50b070085801208070391017502d960b000306140d65a40188a8042802c43c89902101310b113042a91a009001c1c09400c0c01c1d411121658040c201940100e41c00301e2074481100740800004d00d00380d10b00d80da811310780d0f44065180015440030031038034012104409002c0c891106050340c941038105240d00c29403050488540c45044038800c0501d0741d0840b4011100034009403400c008441340e005001046160f07454005800501c014080c564000e4001041d5603406d4620464200d814104980d5031541070090910803c1c3d4000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 318301717 1250 318300467 318300511
    0x50c0a0809160602100608071a160609030203031e070e15040b03040602091503070c0318030b0a1e0c020307020609030c06070501020d0f090503070b060f0301020a020718090b 76
    0x50310000c0308820003a0400c0d0f0703601d600081d00e4040891a60150340d013003038800910004001040c005179410004012100840e09038159a284c2c451a20503c4e090482000d510101d092840f80d601064040d801035540d82c03414402441d40f890000c1560141200a40240b02c0303000e600105040e03084109446440f0401080d038243e42c000d0207150b2010754644000803c0000700940368000e46181c10065072000100a850745014602d40011240040025420708010300032a11600e00b0718400005040950380b00c548070b85601c1000358046601c440810f4480c2d11001140140c1d40c0d001c00e03125000301c0c00700030a140ba804004e4680c8a8140041d02c2400086081005517030184190441319000504003592162680f805c94081c0d0004204403880c40c0c0b4126088805004c1800b1307500f0080d5104016514040c040d0365541005680548144d402000741610202c00352001d20041039072500680080982514015413083d01d40c2c6140c3c525220181845c20910002e04445c0d50b032504040800301c1071892184000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 318302967 1250 318301717 318301723
    0x2030c0108223f0c0503030f041703070c140c060405010513090e0f0c010f080a05090f030f12011d040314070503040e0114040e030a03180b071e03050c0a0809 69
    0x10010402c001d0040e0b0f0040c0b003268161484070507020703018194803c0032110360192103003101320102a020f608100000307501c05203240151584113100e1440e81096a2005105078000c1d0821541080803030881d0004009100c01102d0101201c01340000030804ca8031400085071b12400342d0311a540c1400004106184d800d440c0c1c1080300003812418604000741000803009640e6001c0140800000340242e02e0000165446159200102d03407080e260003c09881d04081c64006240051117240030340185040302c2c80e070714402d000070922000504511034451b1804041c6d80340802069000036010300e03525102e2009000000c901b25403207a0142800c464004160b00d4982440c810500c1c000c2c1940800100800c00341c003455202416070380054204202d1070a0503082c4821500c1c2d000312a180c0d98800d0060030300642c03098001041c82d1688480743c10f050240d960721850110425036003100402c170303150f00401c0448400c80ca40d0342104070918044c411030030300c441c1c10f012511582104404010350400041e181000030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 318304217 1250 318302967 318302993
    0x121e020f0903120910030507090b1b06070e1503160e0d050708030a0e04020702010e0f040f060b04140108041109100305060718080109050303060405060a0305061302030c010822 77
    0xd81034804440d0b01c1d44210070030741d001141d1517104643d40305a906217a403091140c644178440301d8417903100140c1000c8100841d5000350490800d16114800c040036801410321032540500215101c90400340051810002c100e100c10000e0300348180c042c420409281c590012086070350002c2d04200c000060743c03002249040b200501c0c0500b0383e1081040c000355108000000702504030156032440c00400c011010441684213111020b03002425220426041d4548480d1114041034010000541c3c1c0110496030019608a5844a6100740b4080b4082020242100c4024180c40c0246040301c1103161a54902c0b600340403882c20705001c1c81402c40000c1c242e0340c0300d08a14000e59008021074100b449c01030f00c0103040050381c80c0d9107255808800000103201805001d958a800da1141c0510704590f20710701884010040202041d900440d00c48000010803002c0c01210f005415082c204c4880f44081e0050618040341509180c5c1004001402c201810004c074520241c0c00d803900c012007850451500b8940c0352002d075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 318305467 1250 318304217 318304219
    0x608030f04050d1e03050a08070801050102101a0d060f0f06030213021309050a091a070504090b0402091206040c051e0405060d02190e0c040803030106050c070902040b0307121e020f09 80
    0x101d10304d45814182c01201a045000706a80c940c105996941c604854103c0c0a00c00d0341e0160b407002200036920692900080d081340c100a004408001d08100059080d0b01501c0c8250f41050f52095a0b0b51107658034000c45030100c5800c41d052007070901e90b902085220b002ca003007248040e503003c107000502c42000e1810a00034180900240524100712403140014800050210313140c2441d403003c41e50342118060320324428111522800d040c54500503150001d0711080c203403160b11a500b000240c125558040800408200c03a80041100740391034030b0240c1c146030064009510590b11408150004003940d0301210b04540140c0d004280754480b00013003036500c80f2202000350710030102c4404500304032075003811008a0781c01c00d109031780d6030304c548403500b040d44114014800c851304104010f000740ea001e0001071111481c0e020407150076950f200007140403030300903030000002501d0001c01e0000b130661015180501ca51b071000100480112451480d035003c1d81d0842d035248042c0c01140329003070b01101c00306481c00200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 318306717 1250 318305467 318305513
    0xe150d080f130e0709081c020c13090302060901110702060c0102090406090c0e060f070b060a08060a0f0b031b0906010c0206031504050c21060a080d090501030608030f04050d 76
    0x880708040340c5000c0c80e600030480f050340494001940d5070b1040c094a404c940d440c1010700f50b0b081320301d00750030241c103d0b2080900a500c0340c1d01c607081c1c5540b600d403042000314005060024203c101450024286040504400c1450f8101001c0f0a034000c0d80c003048a920ba681241c440387c1d1a0703000c49045000e8000c400f800d651051030803c00041650031900042c8070b0800558640c0ca1603801901001541c1c080c9416440c1d40641c01e1145c00005840010941c0d0405402080140c40036598510307d40f0b802d1040303032450702c1030f0740303e28020032040c41324081d11443e418201c015103014203079144e100086006049680c0e201e00d600d0408200c0c1030340152403800c00550054030003a681e2402e0842a0300c0350300312241c0b1900a902e0200020030105605068420302d07005003804422050303010460104024010300b4440c2e00841c1d2000010340200c0800482c1d9030094107803513207441c0618041c00941181c680364080070349038204004040d540450b4a0440f41031714000caa5050603101c1504145800c281d04003024402d481c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 318307967 1250 318306717 318306727
    0x726180d02010c0801080102070c09020702040902060703020c0117040b0a1e1404020f01080f040f0611030a0b12030301150c0c17060a06080a0b06010e030120040f0e150d080f 76
    0x5075042d0003155080c00a40c8600d010b40e40e0324501e09080b07104101025141041e000c2040c804041c1980082c5165030008102017071050241c3c0018200d903004100840240e44410361001030703560468112080560300701344e403d8003490141c50308000280c00501d000c01090307903000b01588610282c2810310f45c0202c10307601040506c82011201c02d0440f001d54091340f183c0c14611440c1d10301d40c0f10b0004148561007507a02a0444d031600d0750b840100c4201800100e80040d110601100507800c04800f8500c074500c00c2001050f5840500280b10250280b00031600940c0c1080006206030369041640c007204c000d49141c444d41644071030501c860001c02c00e400c9100d9100684010a07070035000001e0140c014140c454040000d9561001780c0703952510501402000300e801c18000403247c1d80103040701e40400c4800b400100d102da420304490880310b0300510b00c4404c1e001c40818240022100c00d40054060803011414030540c4c1041004101da0f505909984c82c0b140b0a42107809007080200304c15506041001c81e151a114 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 318309217 1250 318307967 318307993
    0x30315080d030207030e0603070f110703150212160206072d030c1b0c03031b0609210e030a1e05060108070504230c250501050f072618 59
    0x1a40c0608005c0e0005215213078a86a030b031804c0c2c3c00b184d0146042d0740340c1f0460005801025503032100799200070f4440d4000e6a01c000701103070524440301ca0b50303003070140c00595030b2014000c042a101c4028201080400344161b08002070707a0000b48064200c003842c01d03c10348140903042081d58140034855150714000803a144003200325095048120741000c21340707508460502100c11001003500740c100241102c0c8107600100003081c0260364480c401114000c3c00710f074a404589543c01074450841085030700c0344141e501f8140c140340080151810100601d0b2500c904100b4100090f6682003940d0007800c1d0b10741000340da19000714907c0c1841d80340781e4404151075682d030b9079000b41501c9192520405004030f04109000c0a41c030790b08526408584c0c07800c00000d415444000030158075030002d03c0d25189800c0000d00c1a00ba1110303201003000c00511542c000b04981c03030f0040c0d8403001164050503080c140b10b03482d010041441d09083c6115a1a20004650501595540321100e0000784554500059000724500c007200b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 318310467 1250 318309217 318309221
    0x40e120c0606100c0510020d020c0a03090602010c090e0c0306060c0a0c03050d11030d0902040b060d020403060b06090307062d0c0201090b0306030a080f070203011d12070f030315080d03 81
    0x414042103d41078840c0980c0d0a040d41c04070b500000040144e0040b03d8001c040011a40c041d00442000b1140141000320000166143c40820442078000c6102040b04002c013540c240100700340c055091030074800051508034203041400020f0480410346001000003042d035100d50b015200300d03038151400ca41d00309800b03017041e50f004040c07808183c5a46c000d84035030005690041c228091a055600021454002012440002407102c004200d0344980c803140313080d01590300d010203004510b42c0e0385001603480f4034510b0008101c500362240d07280111801e224003542c0e5036012a02204540c0c40e801c0c04d0810512038560040e564070026550700c0d58560342e5030300107802a4003401300300d0003a1003a01d40c0001340780c40310014040b40c0401c840c0554164400380105000804480182c54a11409882541085103e600180c01d56081d1541d40640c100c582c1122180407004001d501c0820900e04442c500d0843c568846440d03103000d840000e0203068941c0741c090300c0c241c10129140014402102075a030140031100c070040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 318311717 1250 318310467 318310471
    0x41a09060706090c06090b070803010312020f0105070203220501020c0d1703010905180a0c0501180306020f07021305150f06090a2312070512030d0501080a06050f060a05040e120c06 79
    0x80104001041d410000408c403174107aa0000d81c01420760386160364841c0c1d09007004503c601180121100000701d140c3c2405031500550f0340360003843e218485012a00c0985c4d0000903141c84200f101d40381004580d80108000c0c030492000d03903112000002d0b81c01c00411504002c6480603245400100000d514030007680000d00130300004001410207400611081da03200c8001d04080d261a600300410403044d030180c858038000c00405400c450351156241c444008903000402910f0100600050002c2185000003040d4140d241345c4400308114202581c00c621002040000c141c05000441c41c9a10f00d95101e209440000c0e8005001d024041c2d183c1d100b0700a01b06502c42c074100e8036003030401c420100c1c0c6020031603680000824030040030301030326103c02c02015050468640826010030418401e035803006e805030501a02c03540340240714640e00c1d480c0031002c5450081070107000b00502c00c103000140d030ba2543c07d6400c81720100c0b4003043d110f8150898504050110f5409003000c0c00009803808500408682e140c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 318312967 1250 318311717 318311729
    0x5240306130305032502070513050f1602010b130903020d020303070807080c22171207061820010807030b0303190504150c0c08070b12090c280b041a09060706090c 71
    0x401e41107049c002001030750f6040d902000384980080000700710401402e00b1542c3d1000314800407580c0c0101c0c501103000c914000d02c0048172643c544d002c00040c950108003402c1e4511891008620307600e04100020b21880b00544841d04029009012900301441c00701036842941c4903007100301070540c42d40b40340099140c403445400030080d040701e003070101c0e01c5002c2074080c00424032583c030528002e507031b80d40e01000701948a02c0c00f10401c001a00740c40403481c50b0116205000001100c2c100444142c40050408440140341c841014100084414a61008016164200407144d00307072103402c0308854180c030103001d580c20041a2100d00301809100ca40d001c0c440411450103400b88166094590003d5178640340640665902003004010441c09004c1464541e0703440040762060b42d031909051400140e00030810007040f0f08110180c0100c07120505200080c10052821034105460b0526080300c04100c000b811400c4c6240003c040303031203801a107900b022526840d80c059410000001546441215000c09010300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 318314217 1250 318312967 318312979
    0x603021801110a0f060603060c0206091b0a060507051e07060e0402030105060301061107150804030806040c020601090f0b0402191b1a060105090301052403061303050325020705 77
    0x3403031195004565604040440301c0140920755429100c0e04c1c19404c4d0441d0860314070766100e0000000c03a0b102d1207051f01c40ca60700c2d8081d02c0c450500446203440e10682c00c00c0030980128940c2c41c0342041d82c03240d0a035021210305052aa40b215035174204903007000340072580c80c00004c40f201d485c16000c41c808525141520500e03111076940d0b45900c002d000c2240401d00440d50002002c04c014020342d8011501204e80c1e40b80b010858400d170707445080c05e20500b4505228103021a1600381848101900701c009994490004c6d18100010758808000a698080c1131140c102d03520380e5080040c0304444250080e6070301c1c0f20302500c03d645e5960030810801d074020b0704442d58400a002c1c07650700d5101524103882d44040c43c1d000041c2d031300d0b50f115030010701032065030241c101d40c10300034200800006501c0a003d003a10a41045010110440e04000c41d0224540c40d180450b103c0d81000040261460403401c403800320b9038051400c4c0c0e89a941e040e000d60152041d4010002480c1c0003403204444941c0e00003a804280e49060301d0f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 318315467 1250 318314217 318314257
    0x30714060613020c070e040503040812030105090a0203060916090f120201021c02030304150b09190b010c0317040501091b091d0c01030b01090902040801060311031207031116060302 79
    0x50b1104070300942c3c60000d9a500480c5003089605940295103410138003443c01e07280350070740d84c5400616000d0300c22055001e1030301c00b00040120385040e004281d409421000d080d481c520b414000200000790040230004d0f01561000345a920503c902c00c8071001e0641280140021519030100a40301c0d516440120f0051089030400950101901410344612200ba002141151900c4d5104120078105003ea4105190707941300508040c2c4d2882409405a15011400e03280361540003062403d803403e00094a061281000c90f1400196200b4004d106d065210451003c603900c940c68030b035001d4080d00d0000761860007042002c601c044518040720049808a8801301f00d03d0010705400c1c116500b801a900c0001e0300001e844a0b99540031741c005035103103007052400448103611034101c201282c01c15004007aa50390b40d424240100205150342a586800c01c030000e0181c0c002510025070b4a10400c40003e08100030b2103110b01c4078003010401f014185c803ca0401e00d05d00e40c1c0301e480090007500102c810220a00301c0c3c3c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 318316717 1250 318315467 318315499
    0x171b0303090108010b030c070611311403191b0801090b060910050907050a020c1813081204030503070813020a0b13080d0201241401030507020307140606 67
    0x41250451074068407180881ea10f008005881a040101100d00c1d02e001000f148000410a20a4400000980c50b400b40c6904000507011012007025614000011a03034078140368a0360b1054030041190001845045140c1c800b2000c82e02f0314002c600164240c44000181c00700f04842812080c90201c0c8041403410000e03a03800300c503030984991141c041c004011070004503002d070400c107000641c0b0060100790501001e40d175101054a291084030a8000a400401d1203912142d052010b81034280040342d0382d401a00d1220540d11040314013900f140d04100d201a035108c100003900d801d850144000c0ca0350030465150504024100760b0007190800000380c03010000440c44c0740d840300c0840d80305d90098446140039091504c500825405101c1118802003c0c0d0000030701d05004201500d00c440c880e83c000300c1c0e844090228440407401050f07607003103e902030f002c0911a84c039600380e0400009800340b0b8041801d843d210803d13415480b80c42005024114400d05000140d4000900d160154400baa070440042c00ea0030303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 318317967 1250 318316717 318316723
    0x90c12030405010c030c111807031104050a15020a0609030914042c0f0307061406091603020310030206120709080a02091b040f0e0a0b3106171b03 64
    0x7008a0380420813440c00040402e2142c03007107480891069902075084141c080014140c0b04421014104040e0301904011040380e0600a01d018001100c1203142001e0601c00041e0448460b4000c10507980824003681e00314502c01c1000030100c035000441081546021708004107110b1640c00348007101c42146240b401d05007030611a14240c0001040c10310320802200030740901021031501344810798480c071200240d45940c14801404131034071a4500090680015034405807101d00200ba040c070850500b000c000000c0080c0343e0940105006160041c3da0703540c0e590500354810412b8001031740009000c114034220345403981880c0d0140c3c046445292129694000c825580c1c954200001e4001c0403c00c08074807401c20440c214245074503a907120038141170706c540d00c05150840d02c1c0d101e801400c1d524001d001c4045c241c0e1240807005442511201500c080000100004529105010080411400c66420051003640c0000701030146035544103440c0c001c1401c680d40d41e560b450410f10501c405008400400e00e000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 318319217 1250 318317967 318317969
    0x6160801030809010e0a15020c191d0c0d0e0c0a0801050705121b0c100b03030304021f11010e0c0f091005090711010606201f0207030c0b090c120304 65
    0x3902c14a41500301004590100d000e03d007681d0811881e00010a0035124003003000002969a801407003201100e0040106621406e0101024900440000e2010b90114074a000d140003500c100c00409490b250340c9180544940615425034519283d00302c0d03080900810300300d503500705c201e82400c81181c89011103802c8441c00d58001c404201c0400041d2000d8081503141a80645550a030302140300140a06044644c030907001c1c040c15400403100c500300b4909034800c409800c40160025811481c2c103501040410500526030121030004110900d0010302c18003008a2b0704420710000c0c071508c205030700800c1c0c2c4c500d40c010210740314094100721003900d03003050341d6a0f40c03081071105490000b080c5020301b8880b05000c0540f400040040c9000500b9442c8400d02482005201c29900d00741c2100d0407194422401b02103c51800c060b030400c2114507090741012381c031410001040500142d55010515050350b4102c1d103030b9801044620040d081000c1800045541010b41c2804d88070124484001401c41341c4a00c05d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 318320467 1250 318319217 318319223
    0xc0c060c020f0c01030e010209060f04031e03020c061813020c0c04050408071119150f1b140a0b0108030405010807090f06030f0b3d02300c0616080103 66
    0x1050f4038640c4030f503210750400c1c241050040b00040c6403070360190200301103522444a08040510004041003000201d10440f1240711034110361841c0c10105680080d12001c1da01a01441010003040e594045051409035038011900101b0510700c241056a841001c0e411200e0099044e010345809403006042901030a03114982c004c004504d0900750355100c080b01c10070220340383d4001a152211248400080407414042c10000000b6400d803120584010200322008601004212040b204a00401c1d8a900615542680700c500d88034407100c0c2e140c001d843c22409190280c03042d8402d0000081160300440240300f039490a80e01c20340799603a805006d0b138011070b0501c40d50b80c2c42c1103074520801c4860300c6984039081e0100c5280010895072103080001c0c50303000b2800d800c1065000c5068100803044011280720044840510015411140c1c00b1000f075140e810103a551181d2200c01c404407150410700b040c4401e51451200c0c0159251b07a100d100341543e0390b604448440740b4000400309c40e4092801a51518100d9078 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 318321717 1250 318320467 318320473
    0xd030c02090903040807120c120b1303050f0a030e070e0f0417091e0406170316051005010807060e060415050901021c0e1e030c061b010c0c060c020f 65
    0x45603091110300c1500030a82c11031400140004281c900c0c051014000800340748144404085030350a001c0c1c05100154402c09440d0020200f480002d03020002c280c1e4401c21641ca40c010790510750500341d580d8070584503240c4410100090f41c0041940540c000002d14003203504035080203480340d014a10b462003e459007071000243c0c0002500050309501c80a4074108100490303410014060f02007140710900074200386000060f84131104090800740b14813402014008500b81d4021043c08059443c3d2040e030108031502800c113141d0b0300030b10104000880301b440c100c1d6420020740d81c0d0340003400c1e15540540621400100c04a10144d03a2303190460030340d01a038030f4200c200e41120001702d10680700d584c000b40800d030550040c0036841e1103010f042c0a00c52414600760311901c2110046c4410480701d04965110f940b1300b641107060982140e100000d0070080d010342503030003903590b4078002041c50445002081c52030056082c001c40486c01c0303902c05041c5186a00c074000c144006c840b44142a6110081014544103e038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 318322967 1250 318321717 318321737
    0xc0711040603170c070b0d05010303020606012a03021207060212160e010f0e1002070513140403180312230c06040210031e0c2006070327050a02010801050d03 69
    0x920040610944104c11202c0055485000c0460340c0c024203915040603545070010011b054042c0003041e403090702441c10b100d0f021000020301801c20b000c08403407190400d040042800f05402004610003c0c000c4a240f661261054500035010754014040e20700c481e540700010414070500300398802050409526295403815a00b8011103070141c0800c006001c0100f00d002c0906140c81d00c40803803460b01c110344d02804d4202d04200500010f802c0301c900b030214051820415050518501d9409074000d50f151070003056090300f038040340003405040d030000f400030901c1e800300ca9101038104281280629400305454021205020310304181d0003100e126404a40140c800200180ba10492441c10781082c0d060001e480000c0f01083c0a1164014080c41582540e070038503c10700580102000c4c0d048106809000400d01400f400c1588509010b02100103241c0c85e000080c0e00e0860b031140c2c00815640f0000f50881d11010360420b25a5050320400590128039240c1c004966420550501d505981d09512901000703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 318324217 1250 318322967 318323003
    0x14240415120c03051501050405130e031c0509070e1e19023024030316110108060901080d081302030f0706110714041a06030c0711040603 60
    0x6001408404001c01c031144400c20610041032050005040c4107603000544c2e460500007588024150481c2d140c1402000e0104121940d00c4041c0282c0300210303a0710108120085011440c518080c01c00601200812240c8001420140e5440688a14000000c42ea1f41c00ea0710340e15000321101c00d40c0c2a008604031403001c11210080c00001503081046150010800200355205008036005030b028040a103040f0b604480c0700f241d140202183c0072804060361500c5051180c82480f03d030450b141c004400c06803000300045107540a0040d92040d00000c0e6401070010003d18040b0b007409a1200c0040c04079442e0302c00f041e454105060183d0581300920010010042161015a00540d0041030351040c41c400f00d6a040045e102444001c1c481760f02c000050800300e061000103031110801c0f9407204015070149a0420103c10950544840850f09840000d4007907811005c02d0303003c1d020b0904894004100005001c5081e9881d4000c1c1401802444411440d4040340100010740d40f8503c006042800d000c2c0616240b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 318325467 1250 318324217 318324239
    0x2090a150c1109250903080f0405090109020901021915050c1b01090c06030b0d1506030b16080402010f02150705091003050903030a051003050a06020d06060810150513142404 76
    0x101c00a0501c17030303640da903260340f03100096009411404400340046000c2010303003000f424482c050158400258103203041140000e40c1c03040c07070790820440c840c0e800e0218014040c0d03000d03000f06482d54004040c4000e02c7e00d2491090a9800f070b09184450300782c86242c003000054180b0802080e00d502595506c19145005000c501402c10b01c1052075010464100c20800503d150f8410000b01a014401158403451814088070900340148200c02d1104040c1c5003529045c0d00000c183d9200e40e0908180e024402c9840c8e00700d150201c440c92504010040794240f10741c0e9500140544540c800c201d85142d65260100d50440a480003540c070030040b079202780042444031b4100c4d08116406100551040a01380d540e450310b80ca041081c0f00181ca806a0000b400b21000c0d45600942c000303004c07281081e4206041480b10b0607050042c038416030003203c120140e01810948203400315040c0038008000c2c454450b46449080140f6483d045a2902c614900c1510b98105aa803007480c02c4603409203c0740b1802c041c50040c54502c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 318326717 1250 318325467 318325531
    0xe0406090201230a08090a20030c0406120501050601090803092b321c0c08120f13020105030f04030315060513090e0604110d02090403050d060f0506090402090a150c1109 74
    0x582741c003c00400310004d4969101c0d500080015000700e41410031141042821600b02a0a2a0400ca2044024407081c4400400c5844050054a040441d070f480315049076110203182c810501e0500d1100241703001e1001c489910b22034007c0c00c0303140c1e0f03036400071040301c6490a0100ca006089290032010503d8410540111070102d05141428042044c4034503907540b01c82e6620490240d801c600c016002e000b40c1e60f5207a03202607481100c05802c0014480c07241c002a000d0b00006206100001c002000102054405d40007680e041245400719400e00c1d0b01c031400580740d0b41020030340d415207100fa50000542c2e540503000308140031507003001402c400d490716114102c0035001541d049800c4000c900880d0016140c00e89013611690090307a800791520340d02d440c080140d401a81c011114556410400c0c407403555a40103d845e0a0700407280140d03107050240101d070401d0520b42c1704c01c07108038117410b15680003030300308842c500450b03c00e444880c40c1034061401c2280c201d00540741480b842d444240d544401803d000c0e0105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 318327967 1250 318326717 318326719
    0x906122a1c1b03110403020604030b01060207080d08041b0b1303030305090105070e010f02030f0a080402011b03090b0c120301080a02031005010e0115022e06080105010e0406090201230a08090a20 85
    0xb038640346e102c1d004280640e1203035104603044031124004201056050005038081d25414010f80a01c40030044000c0c50f60002402c00341a40484004103888010010315841c014036424003001d496660480c2c2000240d40d0034402170380032070f0500c000203020130418443e003482201d82c0d03100c000314a90107000458080f1846074502c01544401c1000814841520000d0400507207103540e03203101440c041c800140041400c40c0007007581c85d4000304c0c9000203600400b10380706894255a496403138202a0100c07500d0a40c0c52030b14000ca450000002280c01000403d20006c007500a070115009094055401d000304e5000f4440c40b02041d0108005106609400f000c074600d450251040701c003c9a860b25803100c804901e0b0041c4a0001c04614103140400c40c0e0307018800007059042c008010703640c588401c0b00d02c548002000140042c0c0d440c01e06004584c003c0d8030140707100f50b401000000034011a0308003007056001818074004207920000090380280c0003d5003a1030705030b00025040011075000000c03010007042603656 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 318329217 1250 318327967 318328001
    0x20a0b03040f210f05130e130b090d030b0303030108030306010e010302040503010509060402011e0206040204020f041a13090504051c030e300906122a1c1b03 69
    0x45000f15104090040c41010700d982c07944a240703210000070380b1a2040b89603103030034841c00303000651000504081c6407049850b956028102551580c2010110300103240004080140c00000c0c0801150001040980b18000c1d0f1010011601014101a903038082403040c258113902c104002209075203c0c1c0c5085643c6a0181005410f060f11540043c0c01d44404440503110303944540100410b5613844061300c1e8041280c00f607000d101d0101c5c104000c0d120040204040e019540029031010b00401490407500142907510140701e80e403041c80c50060305a4004811000c0307010b91807401049080c0d20340315070307400745500c1001030511559440c422541458003504408c2071590b100c0515620b1070042c00201800998454407041c2500c640807205903000303401c0942c40d41e80005100364006911414102c5110140404103000b1955618040b564540c00203040c1c150700701046186c5403150f2000c1405050070400c001c0401500c407030450990300c11240e2500c01d05d130020740002031100409010b83e00c201c1c048101c000340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 318330467 1250 318329217 318329243
    0x10801240b1602092503020a0e0603041b1e050303120f090a0503220801050105151e0a0309020f010e010e041104091505030f06270f0a060e07050904020a0b0304 70
    0xe40d00c0360221002114695852280700340c40c160400405c103000d81504007141044451035004001071a070480e0f0500500000011a00f8890300d00c2001c3d04a006088500b031540751a00d2600c40300d001c4411034604c00041c1d4840200c0d040c0340102c00d40c1c200d248150460030b06903942d0300e28003089205c050110301d604c0c003d8910759008030344244002c1030301089043d240300f4810a006007450a44507980d0008640b64074040041c48a5a5207070010300034581100e90558581c0240c2040c00c00001040201d045150030001d01138030745c2c0750103401074242d280c021a048088a01158015500f15071105140f6002403207868502695151960000407002b280c600d026003086d88900a0408550a41d2004030310124000c400304110324042115041c0e50107408040c2036a030918450300107410f402d0008010481c401c00f00480300320b26040015111602286084403660041800c054005054100705000d040c003d0f448045124105034880074090b541c054002c000d424a404a81852504083d01c11148450f040b08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 318331717 1250 318330467 318330469
    0x1109011b0b1003021927021e04140a1212170114010906210c0203120f06030d110307081e0d06060e1212300702010b041a1e0a080303010801240b1602 65
    0x441403107000c00423202d85079540d082a00e10050700b403106d04211702c80c5041910032f02050940c044442c814650120010a8001d04010103660340750a0010340300c00c07101880000240710106040c070310100c1c2d03070a0b01c480d00c4160704d80c03000700d4035814483c40d000403a02805200b803140c0400f0350b001c11002181441034078280000710100d010320480c00d450f02c10500001c007051042900c0c040c462003000038418203085007104000c200d056124040c208000d0f1034003e02007031200300f1044010b1030f440282086c0402950320f41c450300040c3c2c02041a4081d00c0300140c10702c0798032902810002401c1d19450b81c0c0d4001400b843c00000958489507200b038091400c013004004441892203010f25001485090f061251016494104802800c60302c2c01e0005a10960800b0b400b0510041c3e0ba4000714031402060b40d02400c44144684486c0d450305a92840e03d0300325400340000641d0075400b202840c180c4281c00300a11012001039450101e8203600d05410b200c0c20075640003042040e1603040105030300c8041522460810351300750 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 318332967 1250 318331717 318331747
    0xc0c03080402310b060304021e040f020301030b180c0310090c0f0602030408060f150607022b0b10080d27060302120601031109011b0b100302192702 65
    0x141d921800328101c4901c464805024000c0c2d01c4c0a40042c0e0b00241149425000070b030340d50b54091003001150301c02c084c03c0c16154689070002080e150152000355500e503503a15080c103940508481d8810344e003016061500146402082c5016403040080c0141068114410500700810312171000301c03900900010300040440000c0c1d03c1000601c1c40303402554940e407800c91b02500f00320000300024100c2e40080c0401c4054209800850034070314080d5841500c5030010f1003c10315903003c0313103800b80d100042e1150002d0700c00c104900c810141841100d0520054903840c0440c200c41038503000c1c4c1d00f801d030000c490f8206600d1040e2014140100d1038811005d090304081c880000010091704164006900080d0000c2c0c10680004503580181003031070700304441c1d002641c1e0120f05010700d0800d00e040101c0c0000a01c2c10a604c46180c451003900142580700c00d041040410300d04010341c0c8800c034080c1580d0303640c0606103501c00082034201e8200600b4481c41c406009012042540c0d1443d06080c015404d1041c02d0886c5550 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 318334217 1250 318332967 318333019
    0x909060b070b070912060b01050903100b030c12060606070507121a1f1503150b090a06020a080415050403050a0b1f030302070e070e030307030302120a0c0c03080402 72
    0xd0301606548841c141840e0120b400014034000900c000c0315010000a0340e820204003c41c0c0d0403a6001421683e0301b030040740c02c4d215a8461917410b206101e04003540c602941d001184c094001c40440d02d560001a09101d50305209180c0c0d8007058100c1d0000a40c1c50034064001c0041c0c07803140f070a6030251500d403682281080e541c84816134208400a044000c90014200e005802940c8100044070182440300c500300c0290303440c000c800c129151010a00c40d818000d03000340341880c0600044c48a80d6480d5500b2040c660813b400769407140c11070000010760303113001185c5091348a0300302e000e10303107028106901c4801c0040c500145808001c010480040469024001000414440c48811400713040032810030301d40c00c284204034440c004585000f0000613400040400440e404802c07003d066958841c4161024040038050319014000000c81004250f8150b0040c0000d01c03461062118580350b561050302105ca4000700e420118211b2140040828040c901c510341c0b0520042142c0110351516091003400c1c142 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 318335467 1250 318334217 318334229
    0x607110607020d1101031a060912030c030711040605010306120602030903040b030f040605011505180d081308012412051c170906041a0a0f060609031104090b0703020a090906 76
    0xb21202841390750f900d4040d031039401d440810700c0300c0c41701c928400141040c440c4000d41c2c3c0c13240961404600050106000351a014803459090700d4440d070180c00c108500c03e136580c0303240d4442c03413510001050542c000e110707107030a035115010411860800351392207500a502c05800e200161005100c00148407907441300a510682c41140b0151040c101458104191241a000203152407031a03100300000710390110039254004041158440310801c80703004687c45145864001d0081c0c040000e00306180c5800000000440d0880e1008015070803c2c0c0d02030760b0303403038202110700c00f14040c0c01c95042104655410f64101031078001d00560380e030b405254401006075000000c030b04000c103900e5100c031641600c0d810b603440c0d0301110640291080d407a00d03507035001301200c810309003402e90041230f80820703000e40f52a4460794a908010404221084d21400003030a002014482161a10700c1c6030940d070342c2ca003064000c0124480e4000d0030f900d0355480d03005042d4042e4001914100401850308400244450a4040c0c080102a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 318336717 1250 318335467 318335483
    0x10207080409050901050412050d0b0310150602011a06090f12060106030e010e10090c0f060e100e131e06090c1115070e0a0b030a0f0b030c0607110607020d 68
    0x1160115a40a0f18802012400300740d240500304008209000e03001d410300400d5250a0ba03498080481c110f0090043c03911881d0184a4204540c07100f09060780818243e01382090b0740d10b4025030785c01040b4281c8501031003103900785946042d804564104840501700c01c603001080d0030540000b11010072151400c02c45201c03001c0d80070b42c1c0108801d40e014812944c5103003035070000344020050700c5009a60f0b01019040d81c0c2c1606c0e602c00004050000542c0410301414200e183d0818080e40e0f01e0000303150303003c400c089a210f281c49542142110380101010281d420003d84030061844820716000c00a000010b0030640110020101517010105441000050010304c0350010b01e140b0040002000da82a80741c5c0d46109500240ca22410119041c4050758849014035020314800d55204c04201100b040e44d010040220000c000c1c094a6181e50f0881d1704c410024400c1005040362200030155108905100345030002010060702c0041980300b21000c102800160003d894004c003035011400369485420250b811035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 318337967 1250 318336717 318336719
    0x11040f1b02070f09060e0415060305031908011502060f190c08190203010305070e13140d110304182403200d0308011e091508011d070b0f0c0102070804 66
    0x800125441c0e8044c03d1148410020141804505041c0110161019181e40146001c841200c410340c5c0000d000f441d17109084e40e489010303899000c805001c0c007140e0200814510400814a8184180b1524010510b035004006603120100e00c01200240504916081c420050f050300c090002d60180d800c0c198ac041c1e40d0803030103240c84003041e4402c4440c0840f40700c0c2540108010000b04070002100d101f0340300c400e03200d0240364580d829020600100040001c1200d08000a549004600807841c0c1e6060b0710b40d03031103032035140c0003900030140c480c8554080c1d0140d04403003001039040164a50f00403540c828004252490100790345601070090440f40c2e000b11200c003094401419040c0701e0968428030340505640d0381c40442c0c01650301410380b9405002c0d41184440c4103040005035100703001e011004008100b000c10001041750000c502c0c244c0740c0c1c000c0c14003643c00e10200e1154041d20007080c00d448014600603252241c1400b092500903440b020a814511000788413600c0481803c0c0700819550344200c2c400c966171 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 318339217 1250 318337967 318337979
    0x1080d0f1b1a0a0525050c2107030e0f180703022203050105060d02130c170a02040f170607050d020712020106090e03130312090f0f0302010e0102060402102001050103050d020c03070311040f1b0207 86
    0x8501a500140c055210340e03103059a16164124000e10305100c00e0b200d98000d80d0751140440003806410480b104090807003040361411c0030545020390640340200001d020303a030303120001c1c0850a0b003000402504655940c4600740c45561603404030424004514290030801034011a403000204244c0303e50444582c001020454070040940c0c040040526100715181c40a940401340d0b100c85005100c00203002c0001000c010b44540c43d4102c4400550007000b5800200a00310024001d01440c09242122490241e817508185000010380754001209009504081c0c1566504080407030b1082d0010700b44141c80c034000c00e541d0840d060b20000f406031103103621040e0f450340c0001844007a0b081c0b1503a0564000c0700500c00943c80d0244001c50920392070600c0709240c0c074000f580c0301040c028404076178075a52900002000700200441d080b01a41c10541c01c50700d508071010105902d80342c0c20300c40108941018010241a82440e030403920041e0304408001540c0605969240003202c0d2840e284401600140400d000f4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 318340467 1250 318339217 318339227
    0xb03090f160f0308030a0f02130e0c09030601051c0b0a05060315040b060d0c18021804050f1b040e0103050c030601080d0f1b1a0a0525050c210703 64
    0x501c0c10848100305414a80300000d4081102400b01900041001000448580158002d00600e43d0304000071903480c2103d42050001d41aa0b015080c600e001120218142101d000251481d0080c02005042142d03e84010031801004081101502c07c0c50464103001045c1c100007110701c035203003240001c130385441c1040807d03080480264001084151110038080843d0303040e1000c55101c0015038801403031030460b040104650180e507200801d46100d20031301812005c11074002c7d00c080344001d4044500c0107058403c2200f610801c035151781089260368000398411601031901181e40c0d607013043c41403905845050f50542003400340c005071456840040d9020403418104152801410184c01070082003049960041c081c04190380e05000f00210748901d400c00745a64030014161562012407144510b54402022948020482e08131640b2071410700041d1050b041d02d42414194410b2000030800c03c0c03805901920039402c0358002020500c14404044400d401d46030113107419503089000b240c0c03241c1044c940100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 318341717 1250 318340467 318340483
    0x10804022106090c100c030804050f1c110a08030f0a02090307030305090f18181f0903020d0806010906030e0c10050903010b0411030601032304060915330b03090f 71
    0x801840780300780742c80300b4680c00320543c10111f038140303003001c9980c440c3d00f1700c2e5150048086500c0c0c0a4000c08498001d11030380c000590312409001c0d260740c501d451404941e15101d40300c3c10b034090a00300301080000d1519a2024000b680441d0b501d400505100d03c90300400d02d002e00980045010580c0019107042038507003400140c45180e0100c440364280c204450000380891400f400140ca004401c251070b5008035420702212400d82d428a049182008075010340c0000b900c400301068001d07010361048120500c3c86041240c0c4240410b85070540d40900e4408100d008001f10844100d1900401600c900303595604500044002525a5481e0301c8842070004c143c00c60300300496541c480c2d440c0145201480c4104001d913a40301c00d007400e000810701402d644104030080b040360320340c8420881908020030801c4079809550614080c0c6900050540d982c074020003150748200c2c96440354654150000e103503071400009004048121405c40406070f503126010019500180c0381c2c1c03002c07900302d0444020882001c0180392 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 318342967 1250 318341717 318341719
    0x903120d060f0e060f0103180602030f0f012c0402010509120105060901080109240b0a0f1d010b310e010e09030313080d0938010501020c010804022106090c 68
    0x107080c500307004001071400e070f0b010517019044c1034030b40f041018401417020b0903501e01604140d080d95240342c00001c0c40000700040b40c040004554010000c20105c00d021050440a80c19a0000940c0751a12402207040e00c1c000344101c0c1041020884101c4030307141c07a4440c000c0b00c00201c002251604021080081030b000503000015241c0c507140030100421011183d43c00e80918070000c0d83e00c621403405038034000c0c0004505030f0f50010240e000c00a44460110400822208002c802500ca514420b0900f00c85010a10070912454028480c000c58004c1401d5051107170204804040c1c00e900a2170104800025564001703800c1100040041185403502d4520301d600900034005546185006020065000e0403020050404d520209034410031140319408000b03c2ca03004040c0301c544a80301c00041071722189143c0101e44c0e00500102d080b002d683c400401c42d041e107105070058200d0500341d20044417104001401a0386c0301031a100340f1818600b001e601401030b240044041c11841c070701040c106240002904142e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 318344217 1250 318342967 318342989
    0xd0f02010b0618040207060e0604120c0c030209130506070f02070f0305060705130902190315080601090c1704050127030816020c030f2404170903120d060f 68
    0x41c0d0103a580034110f43d180e0b5200c814910512610304045030003801500e000400051400c1e1b80a050440c001135040d10403441010416520561640b084078107041603a801047c0c0e00c8a03845c11710052030b040112a520151100d8081140328045e01c80354584070041e502c080206a64039035006000f41d0512841000d40800c00d00f048041d49150b0304c19503a400300416841c2004000f00e0f881c0700d00c00b404800e031001003601590070740d250102540034281c5115082281030102c0d140c183c8010926074500100c5e03003190049800b41c8000d03861300b07103c20042c0034000c5a400030050343d0700d0301103069a00100814041c1c0d016800010700000d0102407200c40070481e9499000c407040000c00745001950200800792b120800031002d000d4541e4011040e0305c0c10b074032650080d130706000e8400100e1a46000280d6481e16404201e04c02800124203820801c0d40c60003600d000d011580c420040b07040309a0060001d1513140000360485034200141c1c2040c0a4075041940707107840301511000d081080c14013000a06000c0c1407a009a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 318345323 1106 318344217 318344231
    0x12030801050108090616030b040e0a0f02280303050901090b1204020a1706060f010e0a0609090f021611040209120f0f0f06072106080d0f0201 62
    0x5180c000303480040011399005002607490f000711022011640310b81220281100075090403066540c005d5115186108803180805c050445180142180150f00206104000c26040d020100c00d10908030109491b501c080d03115213400440b640340c20216940d000c90001070b641d41c03095612040d92a0804901c42c0ea103c040528654840c2c2e1089562980c12910707070520f40c001040da006580c2940d8400000161641090000c5031100c8105040c4140303009500c8001408000150708000c00041d090709080100f1413442c06002ca211124600c05d50400513401070107600b10740c0f000e00152485442d40c0a01c11141c85543c1200c0040c0c0b00540b008400004071030802e5580c601041c85001540315203441d100c4011404645c1d01c4e4410788a401900d556224190201e40302000c802818060705400120385102a0b0244079000060403e100503055044120802074030300500e0034003d500b03690500300c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 318165467 318345323 := by
  have h0 := BRFrame.cov_init 318165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 318165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 318165467 ≤ n) (h2 : n < 318345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
