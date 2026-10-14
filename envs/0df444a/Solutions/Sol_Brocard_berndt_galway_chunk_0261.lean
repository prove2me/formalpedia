-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:48:50.419455+00:00
-- url     : https://prove2.me/submissions/f5a5a91c-28bb-4b23-a11c-28bfe5f95679

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46762594 ≤ n < 46942450 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46763844 1250 46762594 46762609
    0xd0515150f0103141b0403050d17150f090618070201020d0605090c071b08030304030206161e051e07050a02091b03150f04050f010303020c0604030206041e0f030f02 72
    0x80341c100360503c05411000d2100c3d83c04c542d0044401d000301c50a60841c10300d80001402180e00180240c01511583d800c1d01d60800b0012089129145048100c1d03030340c00006040040c6504451500400400c01180d500e00309280f031180c00c510002c01c9054000c1005002c40a000c008807403141c01030350041080180412540030703105c041c180071209052a4a0b04426500c41c078000c5d0400500100701c0441102c0c0c001e803103200d030b590103000d00704107495891615003000b0796680e4003920701c44131400c4d00d01e9841c00700314440c0c5a59040d080c8410f804180e2007070b2146003220705802000c0c000740139408162200032000502d00081140d04e01c282d01800a05200b8010080440700090500144a445001c0d80300152282411650300c02c450a41d94154030750100d0124640500b200f03945030b04140341109015016150103400b5040381c1c4668201c800148400d8203001840c015444000c0d006002030009108a20f0004010b807034591110380044207099680b03801c12401d80b1154010f61741c0240da4190581036040801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46765094 1250 46763844 46763869
    0xc0616090602120d110418090c05040e030a031109030d11010501060e0a090c170408070209090d1407140a03110d020a0c05010c020f040509012703050403020d051515 72
    0x380c41c00d042c0180f61440e55100310380445a4040c1e035002c03440a000030300e0064a010b004103071501c0401d00480810100105512a0306607420321240800003030314a01801a00d0000390000080c50406120a005a0203000a8a081040800b0078048010991030400940c0000c0945036500c00100c05912442421030b041a0448010440080310354260364403080041012a03030401d5002684c8606220101d50b0010b02c1c01c420a90a280c4106210a00083e580941000c074000c441d65801c5407034044d400341d42c84004402c1c04000c42c2c46040842e0040300100040c019407030045103072409020040310740b181402c40c0300c0c03c210086101111140a403840070011607000c640d00380018a810307070f00b90f119078507800380c984140e03410002000c8400c1c0454031118013401c41d4510107003003440b442c141080e405020700800c071850b0600e0b082c0c4010003120550052001405240c15445103481c09080d502400042d9411400c00d54541c452030014034888401c08025501c203440f0712016048001d0000d080100c14503500303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46766344 1250 46765094 46765097
    0x40c05090103150e011a070b0115030b031b13020d0f0c1704030207171507120f02121b041d071704050d230c0a0204060e0f010303030507050c06160906 66
    0xa90003800440100601c3d45d0641e2203518280c14900c0340c0341c0b81c06046102e603080081c00b00c240c40000041440c54402156410b5a568800748020101a02856903a00b051445103210031495040c650090400c0b0f001455501070310803000d0300c2c0c8680c3c0d10030481641c10a1554242a036a2003041030303141548170740340709440450082814802d0a05440c000d644444038014040070420100c10302c1a905c50801500300d5115000403164064505014042c01104000103206900c50601c042c1e500714407a02e200f20f5401000c0440e840b251500c440078003145030001070b42c507600304880c200000300d00e03d0195041c81c00482c080c0c0340c0003180c0d45415000101409140c0064442c0c451181c1e082c04001100070629000300001860a11241c030024181c00241400e20702003010f810000103030340707034035004003003a907203c003600a03603051000683e201040c0d6011802210540140084a0010b00019100e600081c0c1c200300145032040c241104581d141d4100750302039030004280c00b80301615680b40317a0480c07101401410a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46767594 1250 46766344 46766381
    0x103031106130201030225030806030f120319060308030f04020f0a030f140c21010b0105040605120601021203010b0a031d070608090708010501060809010623060901090302040c05090103 81
    0x6603911082c0ca40c50000070706154001c50000042103403000540d880340f171758840d030b1400030889003000340c81d0740c0094450600038014200c05040000e00084c5041c4203045002802d0700c1d41e643d4140000c5640c040341340d48124103440b0207002001c41d43c0c0d500603601407058240170b030b20315040c00e01c1004078080001383c5650143d22550750400110b2081d40302d03080f5003900309240c12101d40d0091541420820b01c20016075002007007134080c00c10106007001844c134074040321008010761101e40f4015506400345219460006608105501081d110302c1c1c40c95411400c1070044400c10070480901d0700c0039401c00d030000b54114401141c90000c580c1c0c140100407215503520002d0700c44000804400740c83c0d501358060b000c24044d595012403105034040050000400d0400001c0042d540c440b0b5000302002010b983d10340c0c00e0b600b440f0001c11080f100507020720409c04e0340103114540014240610030550010f0f6502030501460180020140e2194002c1001c403c1140d0346079030390ba41c15140090100c3e5103903d004604000b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46768844 1250 46767594 46767601
    0x7080705030106060807200d02010c020601080a080f210130030518030723010f081003030f02100609020307090902030f07052203050a030806030105090c090606070204140103031106 79
    0x1084400e95401c090319203000307d00c00000f80180581810300d00c2c00f01700c03284a0100340364007060b4103502001b81e42d1500c0e07081d50141d990302c1e407042d07980320310f0a0f0f0003812441080150f040200d483d000145001e021030070106d0b55840c105002441d180c402640301e034004000c2c840e00e96864448030243c1040c0cd810030140900c200c1103d0704d000700b41d0b004104412550381441c003c217408a0741e007003000c800106111004c9600c020000e95a840740007030107070100f40c0815240b40040288034011b0008901c540c203410308090903035145440c2280c44208169000065010790b01407228541454006ea05c003a0003070180240e964140b446004003280079550019462520501c1485458400c080040d41c12480d40d1800d40d0304c4501041c100d500d040608126070071020724a10380041040f4001c00c00c544540d0013501c0e030507801d9a8400506003038550454400301c842d0400382c03012880745006c1e00c4940e08a0805045103090820a9000c641110400c0498668112008004104056000c55000802d402442c0944a5403c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46770094 1250 46768844 46768847
    0xe0f07120507090918080f090f090702060f150315100504060605160516080703230309040e0c060c031308010207050a030c0314120610050306030705060304060e010e0708070503010606 80
    0x20f180d01030306100c03d40703a40207007510201002c5a201690780294a0583e109003040041c5074590162120900926800300c580c2c28034034190301228883d03040c0d13070043e022a41d1034421684000034020508000340009105403561500c040201c00100c3c1d21402c12200d10742400c01d40f01d150f100703003507200911032400e055090261962200580d03003e0005901d030f09100724104d1400b50306242a010340d03091608414070002444107c0000e0320803ca038060b00144111290010880304182051456041d1551007000041c2150405501c6100d0001000c0141c5071898003044c005107259202c0c1c0c501201a42c004985034134032240d490051402040c20b80021450000c00f0358485485543c20200a401d01000c1700d01c203820304ac000c0440754821081c4001c07146d590f403107518020340b07103d4041c1c442c50700444141400080d02d0703010b042280d003d508007d004040c42468001040441e81c00103100301e404907143c46038100c80b00400d010300003c80342e143c4084c0480600b0003415034501030b1f1b00e0384a58860381c10980e081049a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46771344 1250 46770094 46770107
    0x901060b0a050711030609031b121803150a0b030105090c090106050a020a060908040303020c010e09011401020f010e1c05120f0403030b1201020301051302040503030f030405070e0f07120507 83
    0x90300c0d0a000351500c1950818080440305680040d81500429081004580000c8024109d00c80c1441c0440000110500656074a1800701d00c04000c1c1a42000440900d12849481203030300c410040407a0f111103103a40300500d600780103076982d03400d050b114440002107160a0080c103912040c02c0001f42500d000b65030000301004010310481050140020740049541d1091028a80c0d094001c1818050000d40d4a80101d142c0d0003848107400500980306c0400a44d0b1060a0301da401300c0000307101c15416401c102c0c08001c140081c980d654150b1103942c2c944220540c081c014100c68490000c06003e80140780c080b0b40c4070000045204d0420000200144040c0c0407103103603401c0d000300b03480404c0100b03943c0e03134902540206181d14140394019003400d00c80c1e0300058150000c50503240306803030014440d4110b0540c203003079001c1ca01520341d04d5081402070f1241ca06c0040d02a40c0e00a01178021500d00564034062522000d406035000c2551705803640401401300e4002400001c07842100c501041b00740b50205004004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46772594 1250 46771344 46771357
    0x403030902120d0507140c10030b03070e09010605030d0206090709091104050f0105041a06040306050a060b030702060108010b060301050f09060316090905010b0319060e01110406020c03060901060b 86
    0x60580e100100415510380c40800495100160221240b048004101130840d8110b0036003112000d4491141d10b01400010504e00c8403201d014000448941000380290040c200700c4c4030381509031254001c00501401241032260060414400000301a401c18061601f043c1c9808001d01c00e651100d014000c25410004208049900101c4000343e540c1440c9000d100288810384600d500078240701c20b1148a10000c01114104d8200300c8013002992282030f55040346a001020351a44a40c0034001000440d125801081d80304030081d4002a109840f40c03003d82c01c641050b200000164481030040c0b01681d4248108110420b044404500310b6140000285403052040341050041c004400861200c0d281040080c4c0e1035110680c030405d1180d210501640100521034041c1c40c65805c1558820342d5040100d03142c1106a45541032000720001c503103481e005002e80050702030180d0740c2c03a044039110b030010344003520142580e40d003d440e9600440b07040610784240508a40320f03503450820304100a481040840d0007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46773844 1250 46772594 46772597
    0x7080912060717040204090f080d050601020c030a0b180a050303041a060a090c1107060c05060604050403052203051906140907050d03030e070b07120509030c010c060e150a0c030506090403 82
    0x60943e41e0f1700c0481c01412104100500c00020110580308002c50310000c0c080603030603001c0401059132004012a59074400c0300c8050f070507400065840002c201010901d59100001c81800d01d80341d0036128509180400400058a0a400c04001e100c1040703a20080001c05c102880031900550901d540044d0200d0914816103008568640100c04590f000d80c448114120010059600203a0385100160030091200c00407a03050040d540024520310341403141c580642c2d05642c17010b00780002240907103490300d502c03541c4e001441c10240c40000065404c00c403503100c854440c20340c2007000c9054034041f41904c1f82901450300d2901154100312380e140000608504464044815080f00c01d00c60409030010000101090b02da030058003000302e074548084008000544c480d605244d802c2000f1074084800c1c2c003a03100e4565050b08505421880d9610138a03900b407086000303040004e0342ca0203503041a0314100c1e9244104c240525150100200444c0d1485070150b560201e050901172032a00380005184810010301c003c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46775094 1250 46773844 46773887
    0x9090507021609060612180215120a0f0b060c0c060f04090203010e06010f020f070608060109090c020106060905010c0803040204020309030f0f090901060306061b0512070809120607 79
    0x304124420018035042503800c0050440301c0303454014520280070039024000205800c00c11090181841d4031400005071000281008511450350800c4440b605018000c0f40455050108602e40202c00725414003850412200140789640c0c4201c010594100d400140e105040030f000801003d44003081201440034200e5415988a55680003804140100d801c03500e9042c0c401b000104060358800d60302805101c090300c50381d040700c8680c082280d0f16071510b4032400700f82d0414501006014010318015811800c14106107501c1c0e51200d0b8260102c6903180030110060707446001c204800307900f006441e00505020701e031808000500e91540110b9100c041c000a000b25400400a10031000c1030082e00c9030504200d82d110741c0c030003090200c6902c1c0c0d0083c401040c41451501c00000e03949000b13103d1342c0b08540c10303525903d003180061501d8109194403420701782c0c1c0b03a000e048841442040480c4c000d1014034820001180c03110700190600590041c0c0d185403c3c1203a000d50b040c40310403604082043e0301401c6941c0c114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46776344 1250 46775094 46775101
    0x12070e030d080a0f0f0e1e030a030e03071202010b090f07090e09010e19060e0303100603020a020c040507050408101802060703021203010e0105190e06060d0b060a0c0b16090905 77
    0x248020505003100001142c5891881086190ba03504140d401080c001d040f00c11300d003000940707c140950110181207469008001c00c41700300c1e0003600000c0c065803400e01603d00740b840d2600c80440f59a0110742ca4401030355550390402440c506140d04980050718100034900f64a0301d0b00c0c01604c40714581c0180c9030545105d400081402c0000d401038000940e0807001d0342c0c428040880802500748940c0d200b21101420004c03800b16024000080e60311032106203468504541c83d0843c290001d40c00050030318214058400c12441540304c45c001d1034081c84c440d0390381079603c03807824640504041a40300008140b84c00e00c1d0904003800d0040c5181c0201e1070f0102d07011030b6520181e00e01a0714100c407442c031288440c04007100005040340f180b08028101c940c00d4544201150803605245c4051700e460142d03002e1440d8060100b0140e041c100091300782404c503550001012030060780003030b1041c0c104000d013200180317416503044100540380d50100c3d0015400ca00c01c0c50b0070804202c0c05002c1071600e000311f104061f920b4000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46777594 1250 46776344 46776361
    0x70c0c0b0d0b0307080307080414010e030a0302030306030c010201140126010e0a02040f090c06050c0304030206040b0304140703151104090f0903030605060901052217010212070e030d08 81
    0x2410003030810400c01a9244400c8120401a040c0b01c40e4032032007406020000220500048200c800c00351740308102070b1034070b4100400b89085440c00381c41d150400c00810f59031121902c00300a4010701e503000b03400071520380c0307094401c042ca019160501c2504690518520603c00c4400d080f4441c1514080515171420740016a040c00c988881c014079a0010740c01c0c480000800782020810620751402501c06001c640804125502511050400200f03c03062006040110a12441c060440d05807504166443c05a4980004920360442d030802c2038404000018041002030081043c80311002441c0034002091854643c1c0c000c10410f0700c0c05011141e15002c060068410800490f009048052010007052a00d034203a40300410028a08902281ca4520081001e00d4000b0594004940581d2480d1512203400080700302c480d088482c0803100f41200c60040754442090301c0d90342e04903025000041c0c540c00560000713100d000c0080c2038207050040741c00e40381d40c0d5a20040764000b0081c5840c01c0c10340080d141d8803403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46778844 1250 46777594 46777613
    0x3030b0901030b090c060f1207030e070801020405040e070806070503070c020d030f02121603110307060c080907050406030b0c13030c080f060a2703020a06050109051608040b070c 78
    0x564440c844038000720400800c03040c240d00482540c41110010a24001444420302c641c0d40840f031001c006112109031214004060307580110a8070b000320f10159014145403810b001a0020482a5004501032100e070030144211814080040000e284503890420204e854400180800041020000000e94058003c4040e01d1002d0360181060f080340045080081000408558070380050290003200071521201da01501c0e12040b501174a611044007565061b10070089070190690140014441840441d10621664041d2781080e02c800c507061a0079010141498503581001d80710382e01d4444d00303001082d9a01c0c0d1499000f07480341603203a61810500744440c041c4d2820f40c1700410114a009020994071404251025003602e8070341221803a841d030202c47c2c0c041e0340c860b00030b10300c1940d03034002c0c0b44005e0101d0568003403019009006071000b003c1e140d2110402c8e034200341c2000e580c513074a603418032a18401c03c81443e03001566915115545060540e03d01c001d4800103880142000008408101030144000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46780094 1250 46778844 46778861
    0x20d030302120a0501030615060905010c240204060207060207030b0a0203150306010b130602070513020f120112020907080f010e0601030209040f0e010605030601030507030602030703020d020a0207030b07051606090303 95
    0x2e5441801e01e0001d00d03d0b8040c000900049130303014201002504000d80c1d2083e41c2c000e60f030a5454050184d401d110044604607005001074503560020f08143d4001d60080c4800005c01d58603040c05642c650404c2c20180c940841c0f0380c0084210740c84407108101003101c903018150880c04a440148e0781e5210b07a2000701c4030b1a81c1114141c0d250141000000350038464600400a5469818600c0c9040d6a100000c0e0303260a400e204087c0c010102000e20140040ea9a0090001588030b0000390b0401c0f000036103219406400f40c03c101c0101c60100c5051065241070b0801542c40940c07890040d8651402d61719481000304184207105010347d00a01003046a0302039019200701d0000500100208202c00d000000075060303981d000e401343d518000c0081424240401c50b0b5069030b4020b002082e540b0718640d68603000b0b610082880081503802d201010f020915400148860a01c41e8018103010b400c500b41001c5810021304104c0c00d002c000c0001041c800808048980540d8010760001403d070000d00f002e901500115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46781344 1250 46780094 46780117
    0xf050d050a1a1f03021e0c060411100503040803040206190f0801090204080d0e0307230a06020a03080f040c0e07080a060509150d08070b0108031206010201020909040609150e0c190e04020d030302 85
    0x49400c7c5141c00703000425610a42c0140740102038080b400d0284811354a8203881140043e000308002400314840c840110f4000f032001c0c0540c0d15000f080381807000500400b0700908005030107a01c0c0c0030401c503800541c16001d0003191104501d402c2c41e007c001c41d6902103482a030424013264008002d1182d0381480080018904500d15a019000711440018104202040d45118150b864004140e2900c0080c2030401d0a80c50344600e82c158a40043e841091140240212800741d42c080d00841c200f0f16040d4401d000c3d0321140c44032650740c180307078001c002171ba00c1c5500118050f444410420a14000d03c11400d04c80b800d090b44e5078503800803a17042030030743c0d4810044041e00000c045400040d90900c000300400c0c00d0329484284040a41340c0e080128280e100b40040258031248500100d004038009501c1a181c0c0ca100f4040d054401034032840070f9041da01104c4404005410420b521410b60429400605504043d001003040701814981c000060150142c0040e0007009844046410140654110380b01003c21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46782594 1250 46781344 46781347
    0x10e0d0e010314010f0509040f06090303050703051302060f070c0f030804031a070507110d0f0303060501020c010e09071b1a071b0c03030f050d050a1a1f03021e 70
    0x1145000e05485000d00800707000a141c444030105084000126038107880001d040c0500d054078100c00c20001c10f4000d80f00f50f0f5120100110380d0001a002c0c45881c8405110b0344011400c2e1809103409012100020681c25484c072209113034000513998030003140c100491850102c0c0e1503800c40c2c108021f21100302c1d0010314210400041c08010b06c01c1d660080c108480c0304416a9941c0b21484401d080582c2c2d003a039441c404540305110100001c4c482d8075260581c8000540340c072003c4600b580780d40084609144051300401ea84202c1032100c0c0d40d0500000368442400c1c00c1441c1c034408600c0104a142c4001002e07081080f1010454201c0742c070307003c070700341c804260846400c0000c0c0d40c2090074918558019a4504046104039103402540382909220246080c0c011100d68015840e40d1001d451242058040c4002c0103001c0107401c0c40d0044a02c180c90084408613000120380540818403211080f40a40c91403164400303910010340300b6082130017180040498500584c5824020001c9950103404607848501e0040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46783844 1250 46782594 46782613
    0x3070b01080606090c042106110d0f05102105010902060a03020307230a0f03020f0706091106030621070509011401020c0f010c060b24031506031e09010e 67
    0x70924041c80c1e003212200c243e45c40b41c9241002910880c0b2441107041440002004c080031035a0314035003100d0080300081440c4c0720401c0c1040e056030214031092041580d400d50001390307000300e02c9010343c02038003010f204200a00b400004075221208007241c0703488070700849104040242c20340041d0185540507011907180c2e030b901c80b4060007a40040b9400e07000214000c40c1400c2d0711608042880000340e100070101d18001415600303c401401c164040814182c00b0000390121502d03800c010400c140c0034207800034064209242160380720000c242914461002401800b0a5943d00d0011020007514240384000c01c9100100c000e0034241103602555020100500009061540340d401d070340c011100340d0a981042044404000e0b02d010301c81880b034005880c49090000140310742c1e20841c03c0c14002000d9030107031a5180703020039000701080b0070150700c01e0f004418045d151b01e10100f42048010708a907500e00390714103605040d100c0040701540c030008107503102c0800c48450081d88201d9440d0b10381c82c10ba40700d001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46785094 1250 46783844 46783859
    0x221030f071506050607150e0610050405060f09060607030306030510020307110a0c1e050301090311070605030402090c0711030f01060f05010c0c0e071202041203090b030603060403050c03070b01 85
    0xc0003048240d801501a0400e50902ca1451040c4404e0780c2c1c00600da5420075425445400d20040500843d2103200d030b82d0505032216050801c01c842c42610003150070719103d814031013804142e4202422030b07800380503c5030608210b50740303ca080703641c040c00540300507443d00c805042c11006401c050b0700c080d203d800b03402c001109144a90300194402c202c561604030f0390807080004950764510405024050705102d0400340f03c1812055286800089144007005802c3c0e100c1c0300190850310f5101084000c100082c3c9200c00002c400d0012070002c215030b0800c03909602c4c00d900400ca6507240284011541400080c840c02008100f01c40c1c00c118a501038100c80d92440b07140305c1a8002c103440d00684803e8030914074006040e41c0303d1040900e050754045c070880300407480c0c60040d101c0700c0b5010780501c003400780c504480711030090980f01801c0146041d8114520b11009420301514110f07454100c6a5216000c008000c01506c000502ca50040c0d414900540c2e41c0080144032030450003034170001000421244000140310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46786344 1250 46785094 46785097
    0xa0c05100203100f060c03140a021203010f0303020607050307021009030309060e060f0603160e15060a03050f060a03200a051504080f0d02060408130b0406021609180221030f 76
    0xf54036205002c0e440584034a01510509070031b2400500250340c0d900904900b240c60005800b80814900494500c0418013402e001c041d00243c10141c07421102c220b0400070705a041000743c0d000085410000d1850600d160700a456181c03001e102c0d0401c58542a44000305442517000f1000c071504072108208003820000c205403505015500c031000c100802002c01c4a80c1b070041280c0da02100010b00c070089041c50705031003810f60440100141d0210382c91441000454403007800404014015583c00240340c1703810307803c041500c48050049805180c10301d10a100051044c200d03030b001039181d004145802c80e11900003445007503641c9c011a4200d61401c01c108682030501018000740c6803900240c88d01b60048848540e515510030105100590003000845e020400000003440409070511040907050748a6170709182e82c1c1d0250b0302a40043e401380300c0ba15520190380c84c0b110042c102e9614180a00303440428030244544402030043e208a400860404001e4a0118520b1311082c00c00d00f80c0303031140c52005112095 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46787594 1250 46786344 46786349
    0x200a02010305012c06030304050d1203060b0a050a110a120306300b0c0d05040311060906040506150f030115030b0c0a0210090303020c0a0b07020d020606060a0c0510020310 75
    0x4a41000004940c484d007002c00a1082c50a582c910300d0480c075200841150658090102509408100004502c1e83c5032100801900d50013148100001c0740b09480080854110364003c01d4080c40900611031080c0c1e001080302d01c29845c92801c842000c1c101c48840b130401d14840401056101d1840180f5000c0d5010382000c41100c55107100c50101e0148002041410b04076020f5102200e8880c114620005a05c203003000d41001640011070b0a28208145400841e90300351016000302c0c01c40c248401482034104102e50307002080201130700c0a410107a03102c2c0d5030f903a8040c1c4906000c0ca9204010003c50310392807000d01c4101c6005000344507844403c40d81c0c0d56441c015001c1a2110a00d2000041c451101c0000b110040c2d00d1960041c030803a820014904010002c0101c11010190208440040403c0812003090001d0058254420324140100043c0c07400c401c1400a1065401800402c8030070703910041038441440d450306168400c0c1c00c07145001307420308810190380e542c07003480072040c4105102521105400d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46788844 1250 46787594 46787597
    0x2071b090606030f0b03070e0705040e01320112050601110102040f080705150f071106030a0b01110109020306040f14062d09060a110f04060201050402040f0b03061303200a0201 77
    0x88907983d0422005c1e1841d2011003a00369011800c1004002c0b40c80c440e84d5480020741ca00207090a483e131050209241c0280e0104110300440c45103010200400329200071581c0384499150640c4a0f21000605035001e104080c5482c29070340d4000031b1091740a003203c6c0710110304000086581d152125002140b94009028401581c0300340c610200c1c0900380f0b0101054800e5034101d0746400c00380d0382226202d050740b000c41e0465003100c0c4107840c44510789840c000f030b40c0101010b540104410005c01c00041c428250100c400d0300d40d0303050000b001e025032004998550003940107101c22488200c01d052000c6442e000c0040c90045e031059408010b480030780041c10307440d2646c075084015041c0c08412001c40c07950200303844100352504001c011410b4800759070303c01c00c2c044214040302030a00081501e020b0983d0000d900c0070015035162410030045180a2068040b2000c80000070030003010100082a590100100010004581142c240c2c06060207034040c1142d404c007045907070900c14403402441c0e88504a0160403070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46790094 1250 46788844 46788851
    0xb1605060c1e0a020109020a0b1801090513050903121e01050a1503020702030c0306011404050a09110105070809030106060c0210021b01050a1206060c17040602030d02071b09060603 79
    0x868110340744044542c00a510400c925201c0c0003916409416808100c800c0159903a4646d11030040c0c40d000800001840302c0100552a0407018444000c40280c0300204da0401c00e00b80024440c0c0c3e0380f1003203101d00c1d03610b100f040021a55103030001d161842c407413080c2c0310358418248810052803500501001001c00e0b203007020a4981e984e1241440142c1c05c160140042c00f8130044c03080b403071684c4203601409102d030001341100e1440c426100883d0502d0070a030130880314110000c00420481c2080d004440e0080c041c82002c0194010945804061006148540c1e04020300014544140a240001d0b18510403005000700800c84c0e640c100540104508481240143c030021a03d5448900105403500c804203241407254105c01000011105a03000403100c8040c041008528810350820f446010003800c01a00d41039030404146c10500d013081c845085002c1a81c50402062005543c08810b031020007040800240c0c0750192413810221118511303c695441c880c07611400a04606603800c40403c4829684081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46791344 1250 46790094 46790101
    0x40314010204030c0b07030206160c0b070518030c1f051309050a0f05060a140a090608070303030e030f07060f0603080a080709051c080a0306081606090b0909040605040602040b160506 80
    0x380354030f011b009030260146c1c00c1040002c1105c40d1151031018001003c0c40c0210703d500d0706a0714078002c54000e99050002510215031042d030074200c011420101c060850051201e840c0000c00500c6452401c1ca0b490000d824210450481c640100309a4285900515003000c940da2580408001171030704030391001702e5600b012842071071540340d885000c0c0101c00144c09034407204d080c01d08413507040c020b1800315034126002c0074001420f16010701c20480500000e4001e0700701c0303500e03504006003688c8120381000071640040042400c812148d4045600b050b501c01004182085d04031074100041401d0341c00903200403000a01110143d9014100500c50300560320be4046203034881041c0032a27640d18078600920148241d034000d004c00c1260020302219043c51030081549030311505080e043c81c003420800d0a5240004406200c00d0f500002d468002d04103c1c040300b0300f4426914000b658920021b44050041d43d6214045001d00c4019012607024002d03804005548111009a0403420060313000d06460034081c00011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46792594 1250 46791344 46791359
    0x6010f03020906090d050313081c0f0206010e09031b01090212010c0203160203100603080d05070e0f010f02010b0907050c0f030f03040b070c1a04110102010905100b06040314010204030c 81
    0x2560390151000d0060f50414407000d09100b070010034800166414441405440e104071031580b00c03d8017908020018001340b03d00c0e5003910102c0e84036521404c06001d8410740918096030f0004d12141185c070888a4074400761a4026500d0840c4101400c1400415010608a218040540082d003003184291808010303000e50402c41c0303080328640c540190041e08200510104c2440f80d000d00e5042d02d0004040e0380741750061480c0702d8100d0344541d104550300c0f000413860744aa02a50b126896100606042c1011143c410b0000981084180790b950b50502021032070a00240340f00b5482082400c07000307055130303106007820040580b01d40c0003500e00340014450b420249411a1012003600c50112040d0000ca08548031541c1f801101c101c000c1640c42082840d21655011400405000c41004203880071040203080509082a0b60405481d100b4191f80c1440140310009030f00140c0d512481030100c800241d0812a400010b440744116840a0301d2480e0384507840f503104c0310660041048910030a44100200d644055 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46793844 1250 46792594 46792597
    0xa0302040e060f010801060e0a0b03040b010501020f0d09060804080705070b040f0b130302210a080703030c0807080402040f0b031e01051012080304020d0516060807020f06241806010f0302 82
    0xd0f600c0c00034410300c0c0100111401990b0a4200c0d08008060380c20284c1c071014142c3c4241c00480c0d0a641d1007400000410107541c05204000070751312240040e000340060701384060510290761140004100305140020180000001a0f9a0b13035603020094030748a907a144002180c0341c2041c06000e1302c5440f03208002800003040c00450302c8455565400390042451074003045030600031030000c1d141e00701081c190308034801c0052010900943c03140848a40782c41c6603081c0103044038115a803460500c41a14240014590008145548250b040b074000c141401c40424000c081c00001400325050300c690305a00d131141030024036103450240c440d002000140da940100c0290200da41c441d51000c1685800c8401c081150340004640c85800503003c142c9407107650b6079251404280700f4040034520743ca50818003109074000e0047d500000d243c4000c21414000741c420b01d407900c5010349038807055401e402e9070302e2842d170003014030600040c001405e14001108140c0e00c03c034040c40454100d03000902c1c032030050340708902a10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46795094 1250 46793844 46793869
    0x108070305070b09010c0503070308190203061c05010b150c010e06010b0a05090105041805150103110a0309060e03030702030d05061f0e03070b0c070302150708032205030a0302040e06 80
    0x1d00804281c3d16200030355a65074411000c09040201000441010400810040410354820341e00c400d001d207090040000c441520070603103041107004005100095840340f0940d00c0c3c4180300004044201520f00d00907005001c20380003190015880140d40808190300d901400c003131aa010024010061102d5080e600e0760307800d029a03403440100303000000c01144180003a26603460107050482c41c01d615140082c05400f0030401c90003900d0785139400c101c683c4070005c0840c8072440e4282414030009407440141c040310b0059044001c10581d8401c102801c4c0405a04034800032074090b8142c0f0360701d00380404020f48a0780448002000c1d10b080c2170124480c2c0c01d0a50760072000200c0417080d00c1451120301d00031145840040e1707101d0350502c40c00402180e40c018500c024490680c401b00200245440c1d44184411000440050240104140110b10128034081c1c220307a40700c040d003101803c190707071942c3c00100345c281010300152403844049040c064840d0194020400d403401c91110075040da5816082164980e150b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46796344 1250 46795094 46795103
    0x50f03030702190804031b051c080901260405010207140a0804030303020a0512010801060503070603090819110303070c021f140307200d030522080702150703110601080703 75
    0xd245800c810f04803903490003440b900c00c1c03c0c9070b45040ea90f61a01c2c91030040041403030000c05042d400c2000b4600c0c25558000045194044008242c07000303450344408c0307000d04801107050156007200c050380c10101118100c0e40c0d5030751116488031400c1a0400e039000b074100d4001111040d0b05078000c8108400000f0f28144442e42c40403019161a0955404030040d4002d000404140042400018401001a20818041e000d104000140e252419080624049841d44040207040c6800e00c40b0300842c443c0b000b1200303811a00c0c03005080141d8040c5013100c0d00d004019110303100340030200a02c95030340d902c081c204032564001c44481ca0721030501c84408502114a00c90080415250400010f01c0220304028640c00b500a08010503d03445401c0d90340f48030840341088107181c2c4c1000010074440c40d01881250341064003004040d2542d080c0080d01056080303851000317003640c140840d0900455844a07003031012001c443c83c28940311381c4180341c050034070544000308103141d000c1c1d00000315004400099050403139400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46797594 1250 46796344 46796353
    0xa0b030408090a030204051e16020303010b070809030712050d051603121b050403050d0e01090303080604060f0e151f140705010504050d0914010c06050a060312030603050f03030702 79
    0x4030740d107245050703011016142d0002c0d00000000f0140c0d41703510a40d445008100c14010580302c8640c500c00d0f020b038008261540b40601d03081a101d8035a800010f690669201845503582c07500141840030380c601a012005038580300d14072001c200308405500c003501c1c3e140f06108a403e00c0a15800c00e40701e5000e00801e0244810441d608103000c203108d007042c07100410a42600280fa482280c0200b040880303400004400700307a00050800401c0010450031115119518019201d2081100020001e680d9444007400300312400000c54100d41c0c0b0369101400034408468603108813580ca07480c0d00c5410604945203959880c1d07c042c0d80c402c0e4200500031468003100c17042d0040b5241060801518818207500b2108040b203070a20600b00000c1d030911405001d2405000148a40c0d42007180c01440400740c1c1c3c00805584901c0307600505181d0b0031100341240d080e4890b4020505584c0c588010000301080c1c3c0c4003400c41300440403881c0c0816096484034064900400c261182280d81c1ca482035500d1200b6200500141c1c030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46798844 1250 46797594 46797601
    0x1090201050a0e040608030d09050708060106090302100302090a0312020d0306050a090c030605030d022112070f03180c090612020604030204020702010c0503040602011401060c030e12010207020613030606050a0b03 93
    0x420000f00c1010080200700103841629403480070300e19040030340c01075100c0d59a01008010f01604105013030041c030046d0000d001d40d40c1800c03030041414000c0d100c024001c0c1040006100c07401d0003601500c864110140c03100304425aa410101d0441c400c2001c0e00000d40102c03503100030100e20902822003030b00c1d400b40100340c142d4505210301c40140b00245614040580d64040800c07269014407803010802c1d465030003000d140005000061038485c0c60b0b401999007000170014034880070740381d40c0c00690002da80e0070030f10181010441c040d800b03000a070210f080f8403c0441e03001001c010100e080c1074242c42c40303c80100310740e079100c442c50240a0f20028002c6c0d0701441c18042040180b4142d0001c2080c14410b02d030028452003107a8070751707180d50010340020015035140e941104486032851111801011203203030000056900e030310061300708101505a903025060030361104520740d000350100d034161540501040c0c1c3e908409034a00348011103600049541b20300301840050345140c0144200192017078045014030b580c030b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46800094 1250 46798844 46798847
    0x8010506010f0f0c08040311090c030403020d050711100809250314121b0c04090f260409061404090302120307030b060a0206060301050a0204081e010e2b0201090201050a 74
    0x35120f00b4104100800301d41031000085c01d100190004503c02c1d80c2c6c00208056a104202060000401035100c04105004000c041b81c0d0005903550345000900305940c3d6030b503171400c040030759404e0301c812547c105040603581c0c03606981c001c510310b104440c480300b607d070400904140149032903000c010401e01307809a0b803000d001081d562006403880030100c00c200c4085011801d48401e03607401c1070260807110a641c60202c808000f06000704210101c0c100c4003000700c88071540d2086018250b21070050124184c0706115144040c109010450100f0604030294656581d240c2e07100162195001e14504071b921640f141c2610b06203401402c94031917140c2c000d00440d4000110001c071541008090900305a220713140e0789007607102e0000800e1600340e90340c0504002c1c13030071000341401d5940c05001b8080d080e104101c100000e0001013407243e40300315030029028101801800c65809401521440000c90017008158103004028403440405035040210710803001c0d1079018203134222061f0b0107010340070500c20000c4045030b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46801344 1250 46800094 46800107
    0xb0a06050a030611120c07031202030408180a0b0d0b0414090a08220e01030203010b010e100c0503090a0e060a0f03080a030b01020118080a14070c0522050c040504050108010506010f 79
    0x182441d1130442d04200100e208082248070a50300840801c5000904106050f80032141403941000c140d400c0d485d5003002d64400d451442051190b110917001c10720704800c50b66943d20404020021803420700e8031440400341c03d10081510103a407920880c641074004000d000e000300440d2083e980341004cbc1c4101195078903201142c0e8070411401030110849030581002420307250720b070809042502030819030341d8190701c140760031034440510860503c80404860f1031251303160b1034902c01e06101ea16015050702c10510340b092540c00385148455008000d800045204144d0010080c0324120464034404c6151f50b448600c50200600e0201400b07101d410072202480d40d01a40200800950610000a10003403200c038140c0c1c00130b40c510302240c05030310004141c030125034458001c40c0e05004101c035203031070143c880c3d4030010602c0c0207208241c0182c000207551100c42d01804031004404171281401c1c082e51900010084690b4014060144118a003400115010310140f240ca80700701010707111031820342e80408007070b60030303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46802594 1250 46801344 46801361
    0x60608060f010507020a032a0806101401020705060c010903020d0c031b0c09020a090f0504020c070e0406060f08030c010f020301080a020d06020409140610030e060a090f060212040b0a06050a0306 85
    0x2c100d0400003001411000494107241e0700941078400000280740701e1140368040c9c0e0b100782403030352118090024400c500458003049509505011020f0b491080060b82080c42580c00076038801c00100c0c4e1000c00702410341045032407901c29401e0f51030a40041d0400c0c0c0d060072401201800080d04208060081d401c2007460f407034414014400140c00c150740d5454a0140c0c1e004c868944001203811404009000c8291414000781a003110300b913052041880c0e6599585c7c1c003a03c1400105c42c0214042014804130381e002502806242500d001d65980316003003141e0ba540120424411907180a5407809004054405e5030f040e680e09201a004120040d000c01812998145043d02e901d9800c000000e50309a003031141c5d00d000c51503661f9010152804004120403501c60010078010b0500b400d1103412103440202e00164040c255840c0064070142ca4102035204a03036408005168070310009404038200b0003030b0300380c80c808c41c440c500c10203041c0ea90000391420368200340728032504013403101d405200044503038011405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46803844 1250 46802594 46802599
    0xb070b01121e030309050c030316110607080f07050705090c07020d1a0a0b18100509090c10080f06040905030a05090612010f170601060203160501020903070e010801060608060f01050702 81
    0x42d0300c08401c0b4869000005002140480d030f4442c1c10904000050011f0341c60039000710081c505101c190f4a503100021000e01d4018108010140d0000a594840c0c0503202d410350011065074a80c0442e103508009580b05000503140c40c03094200000319494004020f601c210b4080390340605042140e804c4c02422210102c04448895640304507248160b03081d540c142c4038464003600468081654824000142a03807071a40c041151500200014078060f03040c180100c400648108030035945035210345040c44005c1034890742c0004694440202150711181d101d00900c881c0c0110f01e80c035207a80c01000116810880d00030a0390f041884191080c0303024030040c0188a1020b041d280c0f4007521441c20b480c2d91ba000f42c0150000d11075010041c410b030707003010140a0a01e451003005000795410284040e642c0d01514050311007403251801c0c2541009000e4058034990701d406401c481c0d40545480d01d80302c056100340150745040d0301e0084002045442103801c5806508068091307841001004011103456002e088181d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46805094 1250 46803844 46803863
    0xa0302030703051815030a0e06040f030806130e01020301050a050102011b03020307090302030601030515100608010e0a060e07021c02010c08040605040602040807060c0201030b0f10120b030a05030909010b070b0112 93
    0x800076100c6200004410404030301c80381c0d403447d24561240884000d40d640700c0955000804000000d08803031580020540c15081c8071a840d0b0300c0d00300248a2603402610320020508000c9054000f01c015005581031700e1040782c880e407296480302e004900300c695020590782d40002124003a48820300036801541c110900f4604542042d4030303178010a1408200782d20448156009280e1090015007410314281c01000c41c00c6851700c02450050f00401d5001f043c000c1a54460f4004041803151119510190003008411900d1903640341010010b034031040080c0b180591456002c3c60710958501c18803c049081105841e082c0c101c1d01c4584a680081c000184100d6215a0801c004a1fa150040141c0c40080a240d0303076150000189100040c251544012220b00882503460300210983c0e81050b0040086000e1a040054411840480c40940902c82030503805006402040307090003004002420404400da80c1c040c0035903607030b014603d407074450b150001d03080c8403081006200ca0581d144c141e4810074082c4c00d001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46806344 1250 46805094 46805137
    0xa020f010f0503240d0b0613050108030406030e01232703160203010902060408100b03010603020f04050712112706042106050f01030b0a06050105090402131e0609080a030203070305 79
    0x509000117040041d04c183c0300004c2042900d1500020a05e03205001d00720500403949007125840d540d0040b40075a609064807410400c200041c254048214420780c2000154400400e0101c2c0c101c1c2c070010740d030144a1400042500542c0b4072001113020055420360020761030510703d640c8114440007803a10881c0d142d500c48592801694030000904041e08146000d460008c4017801c180b412200340425803802039050480030400350740c5900c000ba0017010261004282641c0b8100704484056003007a0710140c4518140c088041480541c0250a6505c60241d40115141145030011070741d1460400300b0354085001c100a000c10780828140700000c80800c06000c10311200ca55400090b0b802c2111524405201c8800401c181b0182c11141c030b800c4030b01c0020800103a410b100c0001c0482c07080d4418240036540001e199902460008440001030106020100308a200c15084040c0c619071485107100103500c010000c0b4040b0f1010410160f02a8160025807404006a60949083d0070100c181c400c10232418260 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46807594 1250 46806344 46806349
    0x4110d0e1e010203100602070303020a06180c0603020c0c0405010f050f0303070c06030b150307020c1507241b090e0c0d0203041505070903080708090616050a020f010f050324 76
    0x4080241c9103000140e101d24201c0e41c140389460841c0d02420455011074010070100e070b0080b410b008008d1b0012004644645900125a0042da00cc1d00c000c01c7c01c900c80c8400944d143c3e0560141007541454010344603c02081e00401060360b41c2805034022440200c80c0810440c038041d241005440000760075a4100340d840e444200950905900200100741c50310720f07103443c914160854a8085064040d207505609140034000c2d9502420f0150b03074052007040d040c1c5091030000c1000e41c1e2100b40e20074415104155011108802401c0f000c0c000d03c002401c2c0300740c04484480b070070a000003128a03917413140319180c940381030300c0c1351454081c000c0051400200040d41d40c0e05a50700046228902030b21001b8825401000d80e170045900080c014810001c0312403062000500d100d085401154000e0303806512030000c0360004105100e080c010001c08054150640c00300710740810341c440154022a280c01590317147e1001174603516640910000001c40c2000044c4041010845071911411460080075020080c4400f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46808844 1250 46807594 46807633
    0x503010f27060e030408010606140a02060a0b0406090c02011d0c0d030810050d051e12041e0504020703090807090501050d150905030c0109060605060702061b030f0d0203070e04110d0e 80
    0x315aa07516058240009c035000070b04482d840980b21085440c07d900c06400940b9918058040c12290303844002185081c0e0b590b410002c0640480e8500b01b04082040d000603009249660400c101c1406428140e00802c0e00031034413410011000d030110507081119a0201c0d201e2070b0045c0140820440e4030340c04182d030b407640d503401d1501500c1070008198030066422002c0a590410b00303405403d5014498420300e440549003564101c5041640001100d4000c00c04901d84490581216802601c0800d4a10030315600c4100721040710040002c0d200308a440704601002e60b00c00f40182900208402c940c08006441c08541c80c00350a0070482c001101d28280da5002d045a101d0716001406030b44035000001400348901c1180005c000848103586040310690200d03500d405100e0109030f52016224529200c0c010520454005400a59816507200301e8842c0650081d007040d528000090030800d1008060b04140c420036010354000e000c4d041c00c20f0514103203180640b4104a807801c913070041110b40c40c5d08025100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46810094 1250 46808844 46808849
    0xc0503070c0e090a03021c021c02070f0f06020c0f040905011a0102070806090a03081801110a0306050405040f060f02120a02040911070b070503100305030705070503010f27060e0304 79
    0x181400429464140400302e0701c0d1025000c04050740083d0030782400603400248080a02d102c0e001108042c640350041641403560000c80d0303c2c0d283c548003120b4621640c1c0880e01a0580d075080e12000c5046c1e44800400d90600f80c14021310f03015a1100c01d48000a10302180c62445811000b8008900b04c0380c141d076294291415408241803400d0040ea203035219680511000b0050010400189100d28200b4000340e43d515180d40c000d8180400b00011450516033402e041d810040c03040000e000484094100070402d90020070b440c0000ba1402901007094074040c01014015074100c000e800004041d500c035007008111104400313100b960300704404407441107401c011510440f040e1000607200c5180403401002d494001000210f83e500811030a800101c0d00c9092507003200341ca00d001d41c1c40c1d0356002d51411a4854030b41026006100102c0c00c00204100000c40c0f0b41500c0040c3c009000c41d04403030007400150740d40300c0d00600ea10b4081d22707116a9954440d40c04101c0350703030203080046003e411089a15007950300c03a4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46811344 1250 46810094 46810103
    0x30c041203030f0e031806130e01030f051204120210020313060309020312030708070315120501020a020f030c1203061c0c060f0e01080109090c051f0e0d02030304030209070c050307 79
    0x41c00b0301d0840f400c0a21444a05207010740180d441c242c1e0781d91144400549250344c091007a85d004c40c024a55880c00038000001d0000c901060143e941c403400c1c075540102c4058012100b40c4106c0c00c11241d91404c00d41540d00712001180807651150300c1781d0802141c0c0c254041c2c50710440c40280201c01c203110942c41c603a001801d0540740059030f141540141402c02401d0b41459503181d00c01c1051140c0c6503802109540c0c002124640050321800c024a41d01211419504c2041c22140b000d808006210041d40109030401c5581c080341d40105103104a5500e82c000c040d98540e80d608030202d000b404050030401540d001c10020514008280074250906003400405401e1b90300000c1944240000ca03000380c0c0c80c2b20103503200e0030203298030341905c00024426201409030003c400c0d10340403507208211010414501500340103144081c441581c6e80c232140010f60a03d4850001480e40381d4001c5203041c0019003d00c13003500074014502d080e06540a110340c009000d44420100300b940e400203404544240064040e1074400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46812594 1250 46811344 46811351
    0x603030e010c05151f150c02010804050a02030303041109060108040b01061d0a123e030109020405070305060f0f1807020a05070f03030306060305100303031d03391002030c04120303 79
    0x10032170101071060150000c020038107501c0c40c0c0d8640250000b12003504e03d0307030910340f000055981e4030f09541040343c602c42c004d40500c0040244010000d8200744042c06e90b00075039001301c0b00d690b4500112a051420364002d030204a4540c01401402c0c4504020300e000203030102d150740c40b03803946c8011030004007040e80040c0202c0c03030200e03000f420018072804603a060340d1180c070100f240022551007440507202152446445c018000d560001c2c540f401c2d0400001e40d40c00030b104006c589060007010b8054001241c0d02031041505204140c514500503000c00020000a0603240444540c06900e180242000c0c1101c1d0541c842c0015a00000c2e001b000a04080c10303c0044807442c0625602e400380a0b299103401c030800349814a400c0143ca4414044c90200301d039014500030600c649410703228500e203175100281d10102c4c0000602d0741c84110b41141c400114500c1e05c440b08520b400c0780482e8080307102c11034800410079000389202d42561203082c0c01658020651826072883c041e6184c0c80a1004060020700700c4c0403944 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46813844 1250 46812594 46812631
    0x301090c150f051e090d0f0308010503070f08030304080304020a08030f04090f0515042708040e0702010c020307030e01120207050c03011b050904021606060f090b040603030e010c0515 80
    0x18014040c000ca6011401e0444c101860111070300300144c48003c00d200d0740c20001c180480e0b03990700d44030018840d50704030308441e031014842d08005104440900950f03029107e804000201040c11100c0d11048820900141d4103540301c40d070301c1d824580d001400990b8050106140030943c00c8007440140040a507a16401c1e50b03c620b40080355096900400540516514110411030460030f44000c803060007000302c5d00040d081914820b00c1c4015089140420302600e2a1200c0d0706c01c2020001c0200160384402d00c41c025182d0b5035400880c00e0703442c84540320006800034040c4c900028020a000c1c10b4210301418100c00d076030840400384089801401041e42e0039484000c40c08414202882141e01e0f440000440348141a02c180300503049220388a882030249600080340064540b040804807000d552140d07081c40055600c1d810780091401038002c0c0c10019113030401a090300e2505101f0f40c0d0849070b158581d8a1941255001524010b00d0043c041e40c20780215010f1030052100e030a02c0922030440c28503001c80220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46815094 1250 46813844 46813847
    0x5210606030c010507150609020307030b010210050106140d02041206020a1107060f0e030c1e19050a0b07030e040c020610090e0601090c050408060f0a11120a02090301090c15 76
    0x140c1441e00a030401144040c0b603980c05011503060030b4119085285032864a03010744000c141ca58070400610344080140400b181d85900f0003e42540240d08803100340001948082c102d503020711840d004106820242000511494007a2052040d41000141025030303605150f58810702d4880c00301d9203943d0014800480540240754980300044050040c15070900b000d001030891001c218904040c00300340da07808101581c00f0441c00000344005810b00682290648203203114242260103030f0b20034210100380600c88019184032204a1340028062241c003460520004510703480240d084e4100308a0308081c2d841034840f40103508110105074020800c81c549011404c1c0e107644c903500000324081c14488405491300001520300d040d200851000101504000007e40b03280c4650f138481d016074060304c4200000952600c3c6010300c21014100180311003488481000704a2080c002007166811642c404070b0343c15112903006d0424400c0150000030603007502d4641c2210b00d041584805180320141da800d5807001d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46816344 1250 46815094 46815103
    0xe040210020303040302150a09051c0306080a050c040b060906120f01090903050327070b03010608060a030f06050415020d06080c04090b0f070c14100e30040521 70
    0x40c509440030354103505043e076000307490f111203c0708541c41e101d640740480c3e01e50380d645d800302d40c006601404031040c1c0c0d14404c50040c0c1091701c080088000ca442d1050001e0f201d2340200340b010300c950307001000e0185940c070a41044010000d01e40080c0d044101880003c01e00e80303554006000100c2e08008000681c68602410700004030160032001c0c0c017505081207000040c0d000000d580c0c010001240010351201d4131408203500182c00c152654035840f4010002851854100003075060f1030056071561043c1c1d45800a1080300d004034070005241780880e019000204590b64801c0d0380161045a4607000307544048042010f9030054050044003555400c02080010b004010510000c001682d00748131140460301c0301840076000400d54100001041c2c00160140e20034084112059400307260000d00c69941c98000c3e5071159000f00e840309642c540340041881c5080000d1007000340340c00a03464052207481846205169050b0f01030060100801d21001c140e0359504800300040f40c60310424411400c5030820306600e030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46817594 1250 46816344 46816369
    0x409110c06101a0915030408040303080c07030c03120f02040b040509011d070c06020f0304030305011806030b060d0206040b070501020307270b0a020c21011109090105150409060e0402 80
    0x410910b0641002501e850400114000e240003c0880d180c500b0007011890401ca00e00d40034460000c00401c000410903100007a00549000e0364501d08959a00954441e140c410f409000c0e0109400c122114002846944104600600f514010407030880e060b0f0f10f18182c0c1c126410060311407401203000e0000e0f0a101700c1840c0100907961001c01200c100200204030000040d05000401581031002020303c00950111040e800025202569900c0d190500030700400c420f008802c0c000c019000c0000480025000300810f59401c4150780c400c0c0c1e00c4110803c18080010345017243c10540a1000180410706000604030081c0074900141c2c0e0391a140c10014407000300c4107048250480482030b4500300d160000e000350181c41c80f60040741e588500c01a010703881e00f10708205040d40544500321320031a0741d44049a00810b50007150090000fa52403100400060080c080c0c20b036007010512004010b5464080f00c100b03040399262000c24075040d00ca13a040030a039212908011a1a00e010301408214141469481038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46818844 1250 46817594 46817611
    0x602010b010315033801150518090603150c090118080706030207020f0306070e010e0609011b0303020705070b180d0209040609080405040603140106120c031202030409110c06 76
    0x802c08215580f150004040d0101030101300e81c016442e03445024590b00c80d920380340c40000040718003642e8050301501e84003d008001e044800107045802c440d000c2c07025517400c1c60325a08849134031002d850a04c03140607001018581e061080711a02030081c609800c1450040a51100c020382d035550440000d402da00a0361408248994901b40c00c00450401055100c251aa6484d0159445080b4000503113400c5051001c10703414081d1b082070010081e0010109480c98000ba02c1c0c5c460045c0c0d10740200022805104055404110030401402c0d40007092101d08040702d1007810010300b0503400392101458889540c0040100c003000142c41400140304d001e100d044003004880c001c82c2c0f8410381d800305400d502e0181c4020082c6455001c1c605c2004540c1d010b0b14082e09018100b0050355a0b83d040c03907440c0380c0d52451054059440c0c02000314140c0c04200d9603d20864220b0300c4601181d1869030b444026111b0040e000d0b003140000c1c0000b09203410343c0d006800305c001620b00200e441d149012101e0307003043c0c400390070760a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46820094 1250 46818844 46818851
    0x30207020a0806062d060406120c050c03041a120907060801050402270a0801230a05010305280b0f04061b09050f0307050301050406020301080607020303011214011b02070602010b0103 80
    0x55031791207001d13482d541c424402c03440e8030440f5401210180d0340c0c40724030400e80c40701022030042041da9210080d0741403058900b0b400c0c848100c9401c010b683c070313114400d81c0d00d015070000c22061180c82503070303001050301c6554a0866032030204091010f40814800f9110307880503400a082c10400c45a11885450151000321000c61410300f40e40d038010748454410805140309414400d0610b8940d030383d1310742c40c8010140e04009001b4135a41d003088041d458000341c400d1052402400124404c40c8052054078140c990110090004200d05070300301078241e2018500b8200160070801d20f2000646582006000e00980c1c52400760604041c513000d01914219005071010f0003001c2440c84c0c40a510202101c02c8030700030380317000d0040b540b034202013801d00c40c450700541c4d0150300300340c20701c01000125030065040301c0642003a50000c0d00c40c24800c980302e10080c820519120302c0014058003060141d000c40000690340b400008034079092062488a207a810881d03580981c100e48401c01c030302c540a005207601880b0918040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 46821344 1250 46820094 46820101
    0x2070801150302040c17090c0114070803010b07020d06020a020607081302010206010303051303170901022407030b0f0d060504020f042c031c0c1206050d020d060b060a030207020a0806 80
    0x103110352907103848003900c280d40300c1701200d1120b80540c003050204580074020f00104c0c82c080100540d0381101207441d60000e0a01c0019000100c03081c4192813103035602101c09459640307010440e0282d40c100700350981e80580f00c100160009074141c03009040c0100d254024014910301f19501420009000b800c0c4a61900741050450050380d01198150540c0d81c103041043d103071112503035401603078017940e0070007080e40420b0b0090200c044040d070003400c03daa20907822642c01c0307010500026004840c02c00d0b00c0b140e42c41c3c01004550091301a4108280b005c002400d10440710711008001030980110b80c0c1c1c1903503a1507844091100f5414003100100c01014140c80602c040355501c030750b8100480d4500b24442c016000c0e400100301c010420b00896118840c59088048103000f14000307107004242c08030341d020100f1219509545011818002c00048500c0101170805d001080e800748110842030140440d00b031a42c13403001010a42d620b8016142c03607c00c1e03950040e1520032520500804500d16000240c40b40e01c000c041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 46822594 1250 46821344 46821371
    0x105070903051509030c070f08070504020a080a05040201020c060d050402010306050913080906210f010602010501180207020a091104170303090c060a020a02060301031a1b160201050d090506040302070801 89
    0xc1c003000c11080d0083d200e035a644000701801c50250200030b041c14004c1d100e0000352204500b030000191000c8201703441b1299503a1080004a20030f0851240111f882680090500b000b640c0c4242d51090040c01900c1c41160020000b03000c6602410700c90340c4540d55a030a00040d940e140c0319a1001d040c2c19601e520f00d908080d8100007102d040304400030a8500000395030141a2568002d071490040520340b00451303120120003200380c0c03071000c8508041c1001103000005960b4414083c003412100800043d03103110340f50080d1100070f5444404140e0308600a0000050300380803901c180d220000140d100e490b00e940c02e1401d018100d840740410501c16a20a105220441402085900034510220f41c6c03942d50312090340f02682005880c3c4800fa5214038040000001d0020042e00344070200c0701c0d0302c0381e14001d0b80e415940154480c6c210522820b00c4006000c00040300200c01020403942e8014100a81040e2000401c20700b942c401d480211350503003040041c0000c140c0c04000c1e0034080c00d40c183c02400b500c0c141045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 46823844 1250 46822594 46822603
    0x3031201090c110c061308121b0a0f02060a0c05160603060611100e070b03090307060507020a0f121101062402030304170f040806101502030702130f060b07050a05010507090305 77
    0xb0844c0301d010000b40b450803400a40c10020000c000b0b25040d20291040046a10f030030360007891101c40301c05509c211090880c074010500b10301165110303140f951070385100d4003403113808d40040041505000a269694011610800c5241d00030301122441e0035900c3d05102005003a50240c2e48550207001580300d01246d241030115051001000791100090580c0d584810760385000c0e11070b40726460b01c2800000740515480f0101c01404c449000c2d420600003074480410481e1744101400000d803900c07030100b1503003002a51600382140d24155529044007405448070f811821100a944400c1d07840c264000e504c0d0500d40d28422400b41407040d4000b6504615003500c640d964a986462800000703940010032000c4001c04e0703015580038201200c1181c0b482c9c40c0c50a604d60311070485000703180e0002855071070355610f01c1c070000c01c9a001039405030601880d44242859034001d40400000000c41030380350070b404280b603003c400c042c1c00414001c000508200d0f82505115085400c007404402c10450162000c1c000b01d000042d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 46825094 1250 46823844 46823863
    0x20d0906062d0b070303090f0308010603050f01150e0307080708060f0a060503060c07151a03010b060a0e010302030603120c074506090518060a02070c030201110c03031201090c11 78
    0x72034940d62004d06180c12401850300c3c0400034140e4481c0c05124040c03640c00724809050303c666460030042d9444548298820034000d101c0c20704122000740316501120300c90034070402a408041d0445040a0300e03080800d0800ca402d400c140e20307550142c01049034004403089800c3c0c00c8130b0721060400c40030342401c1c0400d0325010010500549145c00051034001c12440810a4064108018040100080e000d429000354032440d81c46510035800d000200405183c1031088549921300c1e03032581070361042110300540c040e41004000e103505008180b440060400e0348002001c036100b100d00500700c140d0800e500111181c5a25401c000b10600040f48108100202144071031440741c1c440038117030380301e10980e5454064910340d0002c900715400c150030f10000062a102140300680440240c403d95910003c6081c02c030f01600401a00304250000c040026501a8003105003040b400c85c00d8610000da4803010910f5a40980814903c3c0c40000d80104010107047c8030740241988540391910109010710103e170340d2015440f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 46826344 1250 46825094 46825109
    0x40209030703030c050f03030703020307170c0315030111070f050f0c0a03080304140706020d0909180b06030307051501061106060d06020309030c120306010206010b030127020d0906062d 81
    0x1800d1318003d0000401c1125080000f81d811a03980b86007200c4000d001e504156205408200780121080e107140c40c264909215a80302d0980a080d03940d80da87c0c00440103000e0310415015584c5202c5c0c211711100010050000358002c4100c0c40740000b4910b4500e240542c41602d050300d075041844085201d80e03841d10308000f120b8024000d1520380d2204d0503c80104919450b41100034411040009003841e008503120301c03101e0560700d54100d040e41d0f400091081e641d40306010b104840030300b29010009901e030801030750000400f404590500c1400d80c0d400e40380800340c1e9541c60780705c2a4403004010076603201002c241403000040141c152401e001c000b090120600540040c001034010000031007000c81001070303400c1042000c08880c0610000283d0000c90340c41540c4160050040c64008250190b071003040b24121405201d13001e110594034616101265610401c0a8039a40c08124091086095018100e5881d014001c00103009140894118001d40a9070580e480512078104c20b030001c0c0103d0b100c260440d92003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 46827594 1250 46826344 46826357
    0x160f080c0d15050708060102060115020622020907051206060403030503040f02011b150b011404090509030409021206030c01030506010c020d0203240109050105030a020f0d06090c2304020903070303 86
    0x14074007514803820149240c41100c0c035043c100903040d40e010800a024420a17000c2d117000d82d0300c9072892141810080480c1d00944e0000011488070b20001c689621402c0704c5584620031022a5400603030741d84401c1c0c0c0d601300091400705681801c51003101c0116080a01114140c1c40c1a203580d81c0507185000045c03010300b40c0c208a034980c0c410f69020b00503d01c605e520414640941c81c0d4a490003203c07070800900c03c901c1c1546040c02034801d95029500e000c501e00d1a11040604091030014820f002d403c005001c4031440c00203100014aa45550020701a0600e038084c1d400380900d00700045c1850603000c1407840b030401d0b08140a002d00740c1d0b00075003107440035038040d500c10712004258004240341280d150030b800c0d0301c1d0135030489150f0803d1800c10b2441c1038514101042c04543d90303d804041e55110b120101a5114440100a41031888d01c052058481c510800c000b20340300c2c46a40320051034000a0b400070301e000f26207185241c00c010b8841101040c0c402c0c1140c00314104100c0001013607542e9000d02009091081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 46828844 1250 46827594 46827619
    0x170303010e04032105010801150503010603080417070503120c06090a03140901021903020102041508010b0f03060d0204090302031c020c0705090601020a060609060608010806070f080714040305160f080c 88
    0xc078803c524200000d02805d10041d60364848a030f000b459403110401d03030380e0b600c0140840c1c46d1070306004040840740c0002c3c0c00e41c00e190400c01420410a0751840b4000184101c03800006e65803001c0c01130701d410302c2c51298584d44440d0304851540c10040c1c02004d1100e16041902075000103500401c00f4580c0d2501d0420746510384400000603864061560704800d008540d2101ea5420140e0540050040d1028445e00a000341c4c54000d094900003c01c0c002e6080381c4009005000c9040c4169000c1c550105004141504240494000c1030440349006410b9005810004407407885505488100b1966001c40808601c0d01c0560500e250b151306081c080c81d44118100c4011501c0c2c3d0b0b1003080101c5034a5044501003100b1541c80d124034000308898825030b000f0075181c800000b03000c01c010072541e20401a5807903000c010107079520700712a00c1000424560038820490305c00c5119507001009000918130134001408a0b09a01e86400d45008290b400f0301000300348003209000140340401c200815030000c1e01d00c00d08552 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 46830094 1250 46828844 46828877
    0x6040312060b03010e010f050109060509040510120b0106090b130905100308030c04030302070b0c15270606090a0e0d030c120f0b0f010206070e0f120313170303010e0403 74
    0x1180b648461504080400041041c41c60f040d860340c103d40500c070380c15600594400040d00d101d002440380601003103040c400900642802e0b04544e9000f10350055034840161a9424422141d5000409884055140c0014080c080e08107940c07502500e00400d102c1d0621109007001c91401010740907203204251240086004c90620300301070005907a02040e002e0b03c03480c2c001c141c004241c01901c400c0d00103102d07402000580880000485e034203000640058100008006940d4004c507402404030054121901700e500d44118180207a40740082c03004014103c281001e40030810300e420701405400300301e072810480e41703d161400143c50f24400c0c00c60070086169800740e441560610102d03920b80701d50604111102d0400700f0700c1ea1103210799910803517441c6018076406004903aa10012134088d804680d40b0202c442c0b0f0b40c0317001000040c044031f009002580b0324a80007903450071900420440718200d0600c04007485134503151003020b42c0301c01c0240002e40c255032600c10140081c0c0c80c00742c0007a082c40014283c658044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 46831344 1250 46830094 46830101
    0x120206090309040e120c100b0103020301060504031407031b1d010503031b19060c17040206090402070609020d061d0d05190c0b150f0906100302090310090f030306090b0306040312 78
    0x5040d100e1416241d400341400a51924541f0b441c0d440000c1c50f14104069035030180c401c1c2c9058424990700d00d0300f0b00f425030381c410001c03016034010103080788140071000000859102c662110b1030006881812502d01d04580c400c502909411050340088010740140060b45000040d01d1004103040300c9203200d146542c0384142041445003d0b1f0350005901c403900800d07c0502d8000340c0745001a955518440c0001c079040820a0800f550000d500c98070130820f816461070a0780180208034080c0d02c000486050f1a40002e15a461003107003299116243d0014240070901c0b181d00706000700458025102d00480c24038002c1203440380320007401c2c1e45014a1480c0c80100d1058100b0a006907020f0700c2c1112138240340008020858000c103200c2d1040020094807081d600384014101d000c1c200140c00800074264a80058002c0e41208204540610601c006110394016502942e00240d00170710710711038101154100101621410b4002c111000d00700300154500d918001150303503000307805250484034118020b6548014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 46832594 1250 46831344 46831363
    0x1060902041d100f030506100b18090a020f070b070e03030a0c0f110618150a09090c0e090a02030106030c0c02010c141204090b0406060e031e0111030a020304120206090309040e 77
    0x840051400802049000580030f401905c800d0340850b00c07690344000840c1e551041c42c041214494ae01449140207060102d96640c0010007140c0260801c02c10341107440081e0083c0006642d40a950710a02045540000280c0f4080c00150095880d0030560780c40500102443c0000810f101d040413078901c14000c2d4414400411000140060f64841846c032003d062940e540d00d600b4401d402000f560541d03414640221030200f40b190315180d01252900411300700500d40140304009002e0005c04600782c69403180c0f580c62003500c50b1000161a541004001402c640a00d400c04060000c10502e50000d40c3c1c1040320310b0640e43d8001c0c0300901d11650007064900313101600c000344000c01004500440c001100f0341181544010a40e0104107660b600d0008503008030004031050340542002244002c030410528103081da00c941980042880d0080040c01300e107550040715400b00c0c1f141e0200500c01002850a0fa0342034501c41440200b56a0800034030b0241c17244603001c3d600344915a11b54a0305031020041c09030100c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 46833844 1250 46832594 46832609
    0x1020c0423010503031c0e010e0706120b010512010e04151518110307050c070b07120e100504090c030e0f07080f0607090311010e03070906050301060902041d10 70
    0x101e80c046803506a400007020096201c1c8601e03034000454982000803d079180482e5502c490928808240d128800800314641c004a00355200d070a80302c1c3c408010407080000340000d07640c0032602c0d01a151010104e4003448401410090200603d200425034520b0150554030100259019074a5625001c14844c50004e24884082c1c03e04010407140503007604100100e0710030320b10090045010151042c11160111610703080285d05001150081e8802c402500d00b4560303003000c80e04016212950028550003e90301114181c295a06e51a88c00b5800071905036840c4040d50194441d10010401908601443c00b40704007040e41e86a01e200114445e400c0041c00880400135906522541464203407115800d02940b4402c1c800d610101c40d00900005070944640f00b0759842c9001182555500c0c1649994580d401381080303036503402c0080b503690901006000303020380700001544900c0d00c0241800e40d40310340d1041060300d1040c407080045d190b0200202e845140342c20440070040c2e83d81c594040c0c0c80d213010b400080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 46835094 1250 46833844 46833851
    0x90307210509060f070b090c030f0f070306051806090105150609100e040f0905010e06090601060206040f0312020c0d030b1903020405060a030b07030e1603030e04090606150504090b03060705160201020c04 89
    0x401f0800b00310360360840419001c2d25850341070351452035520103c00740003000030760140c2410400f0408551010f90001d03070305864282d0350300f6002800342c07510105540c0d91304243d5540090140001e1102044d20705030301d05a40123828081c02100190314104400070b84400c2c040c03034000c080b510340e54551049907000c00035002040300e9515420080d008150b41c680c81742c40e5108031001300340700e1580014500e040b50003d034010451a503481d9211440302054100840501190500c0c091042850b40003506040c0442001408034010444004082c0c034a240a105c0c011815000103a000c18500e010700c109403a01501d01144a4071a6000301c1c244280b02d500250060000720107102d81103625801441c03071102c0d03240c2255a2842000d5142003d100700e4131008011500880c81503800b070401c1d030030160f0880c0c054030000645545d20b415003a08503000c411200000b50340010240b0840c42d1078860044d0a1005600030324a608e05138001500600c210f940700f8600381c5480b0b4080d811603100f00030000102c50080e0090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 46836344 1250 46835094 46835101
    0xe07090603050d030203090a140312070e090601051c050c07020406060504090605030706050403020907090302030d050706061d1f0305010f14090606130f14090307210509060f070b 78
    0x148081c0c002101d040c010b01007140320fa2031190080d00d01405c4050b005d07000d00a0a5904d80c008a080428400300c5404140803000980c100c1d48010341c400c00550310f682d41c80c042008200001418001c0c0100e0600c8000c0c06204d1045208104118000c50340000c00101600c4498000050340203841000754882d05001c1e01044d081e500501406c00c94800d640107101e0346407503904160b240d1540e4003031540000c81c10322042001d85858001c036a04011305040202c0c0c050745030307000f003070900c0382103c41a0086040002e102e0104011440b4030b80050201910142c42141c600410f045050006820300c95800c00340c00e421042d401c00d01e04080c00856001000b000705526981400e40948500c0c0480f04020fa01b990014801c40c201090f40351051000608544c0307007070703504004280108000514028115650b211891b040ba00c1c0c009114020030700f0000560321514a0b00c1c0100000c15101c2004001d000c4a444134008960083d00703031010000c00300d44a40d00e899440e001c02e0080c0c0180076002d484c14003441d051 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 46837594 1250 46836344 46836359
    0x91c0909060312120605100503040213050406020306011b0c15140c01050103120206090a170708030a0f0c090e060d14010213050306070e010512090114040b07020106060816030c030e07 80
    0x30b841920580d850300340135510042d80480864001d0301c101030f0844401c02980540798807603c01103500038801003010310750252004402c001c6a10803542140c0d9598001306204503580c020b40114002d4003030508844440c0360755035904c04444054480c0403520b2118001c08079155010ba110209100e0102400340d449100c00c000082c0640002c0c0300594100003443e00764002e1074404608544100c10320002442111301980d64002d0116030b88810301d0310050300f885080700080c9050003c501440b84001c020a00f0b44000c02c0a07400c40d154100c009041c420b2455040014108010448c1d034452400c40310b0b5108040c1c2c80c03c049800024010f000219035200041100d1106410f0801d00140e54040d000c07107512f031361100015150414000b6115010501c10b00c25445165404948103a00180081c004101548000c8180110500a4404440140a000410542590901c1070320014945450049114104181c1d000d07802907203030000d0020140c841d24402c0e00c0d02d010303402203401c6a0708102250300c0d49507640701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 46838844 1250 46837594 46837613
    0xb0402070213020d0908030403090e0703090812060301110706050f060306040f03030203040f060e1609020c030f0d060902120f07030c080c0702010212040b0a120c0525080409050603010f05091c09090603 88
    0x455071040251004204cd80e0702c00c0c410700208a070300051040c9010a042000c0701d050500801040e030541d00c881c40d091222103900098070708540b041c800850f543c00d0a00a40101d006e004000034000c2d84440104800700301a01ca483ca150b07509820010ba4a03101c81c201441c0c45409640058045403c1c1724034000b0b4404002070f103042782c04441c1c000b22001520f40b010481a4801c107004042035910500040003452100c030000c040c9075500250024803540e940d45420700340c0c0c114105200000900a0800846020b403200080d4040141d103010024500c4030540078008400150800c1d10315200440c0241c11a4020000c25281d051a004115112a602c4814224a50040c0350600004040700300c00e0072054800e0280320040040e64480504200034040d068032003821255105c034142040c2401310000c1000c1600800242c401d0102c04541c5140100c141429198003110050102c1e00d01400c1014025000c030300660301d0070300d644070b4071400d03900e100e012201d1001703a40100107031616120000040191881 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 46840094 1250 46838844 46838849
    0x271203020d030504120e1305012903010302030d0804050f120c0c0901050904060903051902030d060e04020904080a0c1401050105090f160e010507150501090b0402070213020d090803040309 82
    0x6003241d48040e03a5100c22401d03034500b80d4004050008054142c1c819a004036100000c04001401800b04c45041c0e01c196815500d0030390040e03803440c04081b0750414503403540c81c0c111070400d48841c5013450f5501d942d0109a451810005120420a000001c90200078044c0250b00c0041c0707011080395081240642c8034070181e4402e154200480c4140d40b8140300d14100480300342d040b510002c05403aa80d94a68407000083e124980040301004400c02040361a004941245441c111556000b035494040542505041b074140e900884090760312201040300607074030003646d41d0380720754800d0205131034029104054441c910850350080100c001840070013004001580700074103d0351300311844070564403481c0d10000502c20036150b41c00003070400600484014041e002a2083c120189130880c81c0842c1512042d0000b1403000140b00c0e0f4648072801041182d2460040d4421b10204903801c610309035041c1d0020341140104120384840d1a0049551191030f50554080030546400c144a107682c2e14151a0043c4168000d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 46841344 1250 46840094 46840097
    0xc1e05060c0d12060b0d0f02040f0b0301030501050703140712020d1107020a12021011120d020a02070501030c020c0d02030c0d08250b01140a08030d06050a0503011b271203 75
    0x282d850b0074043c1043c0106801c4854028156180000080409014041980c5402e041540030040026007042d0942401c00030724486420544030b5040d40360050a545002e8042e50400d400c2520440c03440c4106e01149030040e046003008030b601462010909d01900622400c05080c0345001108003203000b20300300a258182c8210360b9040e03c03544600b00141c0c1d5490005000e500007003095900704886005007114080b50b115002101c0000d40c4c054403920030b0b079005a440c1d018154000ca0074516081c0c0400c14200070745003d0030140714111000500940e1000c5d09402c55100d44c240141000540d10140441ca0010300050012450000c0f03078140b0b07006c3d81d0701c44695407074540840715104480f066005c1d03148101c0c42e4410384480d000e918220005200d002c05041c81544580403800c00200380100700b0040c00c494500050110384245030001f0040807020583c4041e000f40d05005600980b02042000350784003009a003010300c48025110801c1e2504145e0100115054540d0b11011401100e140800c801c0b040c400e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 46842594 1250 46841344 46841357
    0x1061101110703090302060c0106051c150c020c010f030608060403050a020d03060303080402040c02011b081005010c05030712020a0602071109010b090906091807030b220c1e05060c0d 80
    0x2000c078200c15100d981400b03800950780e01028401885c1403001809030414039000420350030b03220300016410185180140508048403401081088131485a400096445003010004001d5442001c2c0d1241d1007038100e070f410001a500840c0308c180c041d07071080014000c00011103400380740a1030701030b116510074a901800361040d2550410202c1c0b10340504401e41c4e901d55242c14080e120f580c2413002130490384031001c01790b54a554034252a4403007020b0351181d02115645031a8241041d00801030311400e540c0126041051855405002c02d40000490f04403e40c88600910383c1840f046040303044c0080101c00401c05030001840005000c2c0c0d51081c62101e0380701300c80703010703060b640d0700d021020300d1003582c0105412407106400605540340c840c902030b40c04003214050100150503100c0303a03814400b10350011a2030060000c14070022104c85105d0310204c031424205010000e001e919540d501e8103140c030071040b000b400c0d0342a085800b07180a0111008000280040391200200340da61a00c40344000c0305100010075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 46843844 1250 46842594 46842611
    0x70623091603150908030f1008190b100b0301060305160306080d080c1c0501090606020f070e1e09031c0b011d0d0503070b01030b06180105060a110601061101 69
    0x11556030100e01a80c04903021a074503640d2a44401081c04504818083d83c0309504e00c04030740780130001c41c80f609000782c0414082c0340c40d81c5c0d20007000740c40b50402003d0358001002c18500808500001030f070380303821600030301a40c0e80b4441c00700214030064001160a802c0400000340c00381c0c00d81c1042e4094001c058170340d8622404204100e04031111441150b40c50380c01188080d036800c0c040c11040343c000410b00c401d070f4500841c845c41a4041c0c02000c65500c071990341e03035004105410903880b03244e0250241e0302c05080708441e04030701e4559404903401190120a90a00403c0a4072191000c482d84c500440080000e585005245a912504140690f140c110360400091015212a00c82c445d52000140c648144070034465500600440c9400001a08101c0102c0850089801000504466886400c4400842d811850424080040a07061500508145220000c0b810803103003818155101550111f0301d880310482c003203070748051441da1046140981400460300c55404000c211149404900902080780e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 46845094 1250 46843844 46843861
    0xf03040c050f0114031503030a020a150902210a0f08040503210f0a11151e010e04060b06070204050708091e06070e12030a050711040b0307150203070623 67
    0xb0b80200403400290070040100b9a00101000b454000c00030309496070100140401080c611380c4460580d40140c0c0c807043c0d040042000510f901114582d4080c0d00388100d29542c3d011501c0701d900001c40303910300381e4440079150b00c2d25001c210340006a900403940d8071100c65941040c60583e48540a03030342c041d000da06007600b90340c03401c003c0101c11644000348861818141d400c240003140c102e4400c2e0400c0007501da000000f010010004034030000c1e11804038800302e0800404c0b248820f420000308032040448c18004100113030003a8801544260452404a02c3c0c080c1000001d071284500000207610a2415090020482d4030442c07840c8504000000c84403261140440c6940300c5000c60840c04103540a2000034200c42d20035004503410a50203050520449403c22074282143c108405807000203501041207014404a036104514560b1b0a89080182266200100703403a24164012248400d4a850101e0003141c400c004980c81203402c9001000299080c0e1001c40703010200e0750801c030a04502902054402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 46846344 1250 46845094 46845109
    0x190305070e09090705120d0f08010312050904020708030907050103110c0a021002031314011e08040201080403050c010204030606051306060c170d0204080f0f030405010c021905060f03040c05 83
    0x102069103910030442407880030880e20020003025607200b4001c1d102d0024103a02c940031505041514071020340703031070554907000610304107040c903a0700c081000c103c1c01000895800d03001c49a1050007894140c3d6603020050100d00648142e0a0043c2000302c000204801c040c00881c2130420341da030990b0305000e80519a104030074140100c0701c50118940000c0f070604014644002c0e8081e0110040c0140c0e13081c0100221580c80c04403c03544503002444142074196559079005043d41d105e503c8d0221116070145452000a100707590040c0000e0503c1122808181414060010b0719030101c03042000395562600c80c40c100010708401d2103154098141c0d1400382d4912003040c00380c2d03000d859181d500e940145030035803586000c1030700d80c582c0c02c5050001040040590501c42c0010800f03801460000c082420702035400a20385070840d80c402289403c184020301c410780c0d00c0403035031035078680440b004c0d105612240c186114a802da50701256000000141c04080342000704040c41c8140e00601e44201259618801d00055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 46847594 1250 46846344 46846351
    0x30a090305280801092c07050303030c0403050c03070b0304080d1d0106081e0d080a1107030c0209060301060f05060c010b061801170f0c1c0c110708030f04050607020d0f0602190305 79
    0x7044c0f06c080e003480796010720119511040c0c1501d8210340030395aa0300d000c00d0540d801503403444c0d074074480014180107004082115184285080d070007008207602d440d44d840000d0102174030082407200c001403414591078403500000000801c0b4140301c10540e4017030072458001c01d1140305102c5a030148a10004245d0340109110024140b0040034000038080da010441e000030004050420303441d034901008c00c2c01107801c000b034a55103101c0e8981e41011540c2e4010000348000040406100360f04000c0244048844100c44604549081d54003e40340c0960001d254050155030310543d401034808540817030000d40d540f0040383d1040c4203880300140100f010146032040801103c5d00000c50394a04003140c00204c0000c000d001a4007241505000d0040100c0702909a40c1444101d5000410b00002c0140303100060003800004d0048400440ca800d82c0e04041480034040c5110701d5104841c08926141952161181e40204d01e52003021070b00e1b4550245880c01c000d4100c2203a5103440100e04030f03555400c8ac02841072500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 46848844 1250 46847594 46847621
    0x90e0102070c06081902030a0203060a080a030e100507140309010e2710030204090309060e01091d060303120a1b0903020102030d0f0b10031d06010b030a09030528080109 74
    0x2c02ca03041c00e0f010350303442d040504074070307080f04c8403115540e0035810900c05107006294150026960741081710400c5400b000b01e40bc94a4682c20840300400041c0e0400245505020150740b4410484c0c1c1070081601d081c0500381c400342001005c3e007213480040701c012004140074603090700e88c100001d4401c8284112504180d080080d50f11a060f00910390780d1480d005240e100742990821207281f616903020030f0580f01e07840002c07000308050380030501445401015582069400303280035080d1500c0c0c40e07034120700c4414030000c038010800884080f88940d202403048820990b01012561882d040130f5144000409200c200030500d004595102000740f8410703c020000c03250140e00440c00d0041c2080d4510092840c071740c407140700c2d640d60340703a00d1540d403118603c1c0046d0341055100010401c21400341d5040c49481c01541c500c1315049180144064540c2900b505e40114003c42c0014180c00d84c1d00d07069401e8401c0c00d0554000c030844020543c841140921421150552640c3e01c8a50380d9075a52410190380c0707001883c46 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 46850094 1250 46848844 46848863
    0x1e040308030106231206030c06130905040f0c03051b012606040b09010609060809070303050406140c010501030807230c060702010203040f09060e070503040b04020405130c0f090e010207 81
    0x4290300c100044141c0040440c130300d5100d02e80c40c0d1182c03081a4020711021000d0280d076401c0160902d814841c100c0c03d91015220580307001c1080074282a0040a801004d945603641c2001c0f405101c510741150020a9010003c0442607480e07003011a91801e4440102c180305840e00054090340d44541d041141030010b02080c05945100c0e003101d40541d560050516811564400d41e281140c1e40d42e1010500801894480115890510030004d0201800405000e01540103800030400a0b5112003124119401c0d407601180481c00505007401070302c144000c4124940c00c040000c02030012060041107203e10907240300d031078810002868100000e400307410b00119046401d02142c141091001802800d1051040da0b15280c2c40d24000100d8141036080090481d640308014070008200b22001c603044200d030700303100307045103065654203400040041c030080c0156251404143c18070300c00303000f0302880355000074044021a1a103202c0c80d5030500500c103d220044c2000301c0780303801324410700c200e0f10220707041407200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 46851344 1250 46850094 46850099
    0x903020307030e010e090403050901030c0207081c1205010303030f0f0c02070e090a08030901060503010e0a0b040303110705031605161a0f0405030d030c0e0a14040f0e030d021e0403080301 82
    0x2075442d540000383d401d0502001709104d150130340c0c815510301d10aa12a44580d0746449004000508480220342d2820540d03020358018040401d00090811034112480106003002e9900300040340c1d03040d410340074203810340e08040c0003004040e09a00000c1644202801c20001510182448002c2d5041e0b081f80748050782102000b401550100c810a580c8103400604580349004580e64651103a40100d560300a0359545006c11b0011b80741c28040d1010140240004000d4151107440c0c0c49442c48016100800b80355642c0c055600740100c0000391a05541c0013016291100d81a284400481d00ca5642c22101c074064406600c08142003540301c901a2941007035031480c000e1240000c440c096004d01c1c2c61004d81001888000f032590f40801c0764115a0f0015a004170720781c00341d0301c000742103036620444240c89001089405c1c40340a5510201049802781101c02107000b034036504201d4001c15401c0112420ba02002138010900061900148001c0c40780d403001745003c072151706941106020b1800024880074080004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 46852594 1250 46851344 46851347
    0x4080a0b130209370e070b07080f090d12081008030c030702090c070f05070305010c1706330403020f04020c0303070c1406010f03060e010b0a0b07061d0312010801090302030703 77
    0x84014210807036244d101220901c400308100300c490000c8150100c0d8503907550030304122017070004200800454050078140691030741c0321760550250b03002c420305081000c01c00003880d944861000200035006141060060000d100c01018078104580c12038542c405039100082c0c9210000445101c40e4102000d14144030465003005121030000c0d142d0388140078140820030201e1082d9200658082c0300e8001413600030704d5440d14030b003907409100a4000784015040d0a140d20f4007990719050b440402203c40358004610b291001d0842d4441d40e0400c0d1041d61010700440300109404014800e9a000301c0d00c1d0584120448204400e0b80700f203054a0043d50000d1000c1145940900c41440f030b0180b040390002d2124400005862034400260320503d02041554410000d00496202c2c41540c0c12448000b486091030000218001040c0e0b03101d006c00445000801c002807012680c0260b1080d039600d104406000704a20146940350441c05540c94044d800e0400068801c20512903271701c10740d6140d0069410407445490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 46853844 1250 46852594 46852621
    0xf01020c0d02060d020a0302030702060c040e011203020109051006140904080d18050a06020304030809010506030a080c0c220605010f0e060f040b0706050708010609120803090106030804080a0b130209 87
    0x1c02c03030b003003107051040c200241e42c1e900142051000c1613a0060312480d080340300a1520202400342400110100b0050043d5420414001e0545400090040030022640390490040640c0300b00900b5601682c440c405c04410306c3d800070340c1254082c01e41c10a12180712010084407240c244da00078210308040001180440300e0384c100d0500c0d007000ea44501c00c031484a482c0e0a08107e50008204e035425400004c0004254100b4141c41e0880d50641c02004949010f0b000700f6238503118040050894800803404410b9101e040001d140348a102421810f0184460000e05508500030030385000c1690070242e02003025442904400741c1c0c50320030f60fa0f001d1502500c00c288001540718143c5000700450801001c00d04990306001802914458440001e052601e003400405120040e008981080300042c0c08010180e90350018040c0c154010882c59a42d0300d451010a0041040d44d000600d059400700740068100004500346c2c0c8501d002c2c00003030b43c1d141c1c0c1c0c1642c0404c0c048030194009620041b02d501081740d2001c0b0300c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 46855094 1250 46853844 46853869
    0x2010c09050d1106030108070306050a05090d0e0301021b06090f0606090703090206160f05010501060206061503090c0a08100609051603051302130608120f040e100906030c060e0f01020c 81
    0x916148a8583c030020a00c240d100341c01540107540b10340030402c104a17040c4140c540c001001d580c1008103081403c0b542d9110401d4100480804c03a6202080c0b8031544d01790b0496841c00d030064165080d03403600c41703802621420b007201c0c2d054841c050b14030b5881d2641000708a441c8148401800105140c4d6480c1d4103030000c081180c0180d80110003030201ca0706040d260095000b1060080040200910740d03031600a0075580c2c144c00480854225000b40310b110b8540702e024418a468980c24941c480d40c540303051614014422100d660710085541c4002901c050100e20503040010805040c41541d8441c0289410b40348251000104114400501081b1070700c0780d4402601705000d00704440403aa07164000a4000200e0311464044070341d0345004204060b400c0245490304030000544034102146008413138254007403440b64900d007240131000221030240903a01403001e061890720030460181c890074120700da144036026580101d900d4204901c590720345140c65074409001680140031164842061080104440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 46856344 1250 46855094 46855103
    0x152a02010e0d0516062106030209071b02150a081602030405120f060103060f0608070b160c030f0f03030b091b181c020108060a030b0406020306150d050f0702010c09050d 74
    0x9056442c0601d0609220061001e42d5550424030121090007540c0801b052140c0780741840d086080006031201800710754400c20300c3c00e02d0107000c003100e051080c440c0e41c000402035203c6415510304103000842d10160040d210141e9601075643e64180b4074107500c602c040e080340c001d030f807042c4401c00070303407505150007500f0720404403c1d40e0381c00c0c000d040d0311440e100003a00201d803229140c0445444407a15486000018240130f4002c00f4018070b04410b5856901c6286503601400910240c508140310015a50500456101c000003907118002c5c100030b020a1200701044002a0420504140600d01600d40c41d000343e08148810001c05480011000580d00004d20302241c2544c0108201055640300400700310810340c00d00e0801502910720005000900042031244199448101840403c003008002580306520040c010394070b45a000000d8816040100401314045000130f20700c115180c190030a40c041c030070300111600c0a482d0f2400c140d00365420314083c9400103800704030410030342ca400c3d8003900a00340030307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 46857594 1250 46856344 46856353
    0x703020408060403080711070501080406020703051909050a0b190c0201090503030d140a05070c080310050a090b03060f060303071b0504050f010e010807050a06030213152a02010e0d05 80
    0x269a50300c1c0c1010b10494013a404a0b02a00821902c40e80090700e41d10180400000781041c1410840041c14440001e44050841a40800d89004050241c0d08840c000b2503200040b0b8075400141d031006080c8040e500a0902800c0922000a400c42800042c3d600f03d1216201e00c10081035005401c071203c5140c060181d04000b810701000a80e510248003c081c0540e2480b0041824808071841c4801548090034866003a450a01000000d580c004c9503c40345035845003135503070f50381c50365088201504044d4001c5540194005000150032600d6400b85200b076005500f07494450b9a114141c120038007045a207076415800c20004c9400060b013103168008092a03405480c002d03c2d8441010808444049450102902002c00144a200005071440740101801001464600d04040115120312401c0c40f41c039017403540105402d91080002c81004001c3c18021010308051100d0382c0c0010040c120040b841b0701c90507a80101990400e01145038040000e4041e11000307582039020041c003074041c40d0880c2c02e071400d00a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 46858844 1250 46857594 46857599
    0x20a0c11030a150b0f03061005150409050109020c010b030a0c050d0303110f03040c0b040f03060b130e01021809010b0406080702190c0315021e0310030606151806020a060507030204 79
    0x10b65003ca0041070340031240068007008243c00d00c00b09050040c241c40c400d41c414030170011385420b01e108000a856044e1882608417080000304900d40c02035400c41c01c601c0707050000200d40310003a503010b01140c0794003000900500d0455018542c403820102c130041c00340b000a040500c90f605245000e03540b0342e4442d04e400a075000451002c0c411980104018090b00d00000080c4828400c000800c1ea0190600701801e629007417030078010784540f81c51440014000350310340c280b11510f5603039851005110788001005101c107642058103d8000c1d44100c0343c070020f0191a403050381041c2880d0b0820760580e8070354101d803403400b03003001d0702552504402420b8004600c202ca400300d20303c40801c0f00428a081c030403035450b0421411480c000e0b200e88542d86000031319a2042c05501210040100e524003150110301d501640ea8452030b445800505e101e40000e8501810400001500201a580c42c00c602c0d44664410030201c0381c9502c40881c098181c42080016400101500045609680f165401004a0a0040c0340c1395 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 46860094 1250 46858844 46858853
    0x1e030b01120e0f160503070f0e060420360a090509011107050303010f09020712081b040b0306030601090902060304120302190809010c02030307021f270c060201020a0c11030a 76
    0xb40310130381104614100319040090b030504000180150041a6100301d00c07500740200c00e4400702c0d0040c201c2e0f106d030761588a004c8052100840d940728445c44001c54503943e0784020440d0851140002004140c181019440340011940c0b4090400c51040105050345c1180b070036580070060b20b4040d15400f00340d544c82400c0d40d90100b16900406a0342d01c100081d5803070b0b41c5010312104135030046601c5013030340e54010400400008c7c51210040f0343d40205040091003500c40c8a1181c81010303c001040300d890400203808141c1c10046000f8500c0382804800312030383caa0700c403814481510718440300250441c00900101e800508070484c14281c0031894a070040c01c10b001485500007880c18000c100c40451190018088100300a00980351040f590303000a529508203410b00954840c400c03d040e54001401c280310b5059021349400c40306c0b40f0b403118403410140014500000d01c1c90161078004445c80f00003610300045650040c000d4030f03140c14854a0310142004251229684a030603682d070f0a40c1805540360540c0000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 46861344 1250 46860094 46860103
    0x809030c0a120305060f010c061d030a11010612020a150e040c03050a1a1c020d05011a010807030c02070b07030e030105090303060117010312030905100c1e030b01120e0f 74
    0x840c0910100c800800b14100c0143c111807001e40400e000b500d1041881c0e80c0f59811240c0d0541c160340c02440065543d400c0c00b4284078900f60208800213902000903900c11113984542d0101c450300458000300310882e40d0b08100d040494042400075009aa0004104000340184c26601d2032a200c60174202c08200c80d101c005404c07600f003040e40f003001c0f80e0b80e0010b00884020f2071213003c940781020b45100d0051402c10f000546c04840441781070704141884034200b070031911500e080c0c110035a407181c0240115505c91440d62420b0307002c5003509002a59800001d42c805101e800341c00c0a46189030090220981072003000c0300035501c61001036040c055a003020400c3ca44091241074400c0d84108050364880c148403000616003640002d0040c5c8030401040188040340090030741000c00c0c1c00303a050010300e201d1240380c040d04060004928030303000f501d40801d0390710480d0031042107500d0042c0105048008204003c0941c03c0f110300c0120180001c400312282c52841e80c0c668040400313000c60394100c4009014041540c7d240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 46862594 1250 46861344 46861363
    0x7110a050604110303090102100b010905040509030d110f0306012303070801060201180305030a0c1b030207050108060418020d03020f0d05190e0d06020f13121a06030d0809030c 77
    0x450340700c0000c0005018001c0d1800b014880304a018624200a03080001c0d503620002e40844c002540e1444180ca550380244501e400500014005002c1e510301200e009071a5003010140122a5041c07003644180300e8158002c0300e0b82d25800d80782c040d0540e00d51000441c0c1d20b608030300d0780d201d00502118000e07045c0c0c2c4c0504041c5115030740d11f6481401d81d41c1031960003425216510034900390000c070014103200007a0880d0542c0c4e0311810009000605940d000341c01c4070910030318648010b00d50301c07040c40b000c18580c0c0410100103594086c5ca84107540e0329024280001c44601c45c4030448103114102c0c2000052900302e20131907c040c00b910480d16001d4105114a0030120304c0d0000b01c0214000140e80014072111000944011000303051513006202ca103c0807403045040000300421141d40058070301e030015100f409503804440d0140c00c46032015112040b164050a0002054034000c001050b05090304a514210302d101b001c01030098113500b41481400d0311036003c041c203802e1982c0030a11411070b40ca00d0402400c10b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 46863844 1250 46862594 46862603
    0x420040f09050a021f09090e1c050c0606010c0b06010c050f010c030608070e090d050d06030605040c05010315140609030c09070c0c060206090a02100c050a060b040b010903020f060307110a 82
    0x1815042c4d02c1080520030701001801c04175281e000e0081c0015030000d0414040740c2c05e112002c2100d003064803000d8245058100c01804055000b100c440c80e8030b82c080042d05c6284008070807209a0b840341d8005581c440e4070400000d00f103203121800140b455200343d1b0300903403007403140d012034200504050505013901c0803c2070000000f99510380400240c8000c0286900030540301000300c501c3d00b0b01da0009a16110307150580c0084c4040040e142014280650100300210b410100030426130502e4686902a4005d601c40c050001c0d0428440e10340000030a00e95604950340350a507400ca2800780010b000d041d410603120b8035890300505100815907210200900e10800d503030340d1041d050b8091031503c2406003d0640183c0300b103510000801c0313840d034000110041d006030126811540503002c9901282c045400c4080144103000d0680c83d482003010540207005d464208907002c1c45184811801140ca03014180b0021f50312120039100c04025081a00041d0307007100345440d100c000d441e0094030f501e2070f0400340c900848 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 46865094 1250 46863844 46863853
    0xb1903110406050607080d050709030f0b1006050a0f1202040503030c100c2a06020c1f0605060906030109020f0712020a0309090903020606150d06080102041403060420040f0905 77
    0x315450988158000f400f0125040c909040007074481070018040c4164640740180d684c0089084240035024281c010360740035088141d46c1039180352000f00c0b943d0607035400b00407101e4000040f404038003035810354a440740141d0700c19a240ca14a80220341c013900c111640c24025500300408529501c1c18002810a03c60403001080c9074040d0001160443e50a4461101000074001200300c4503401c80d100d00502c000f6182034071844900d1381c20f0800007841242d1b80348d4a41d10800b100c102000030804100c0541d4080c07050100201e40d50f800a00c00c2901c500e11006902c07000801c014000c0c0c0c60294040d081000050103074608181c0b560340d601d4a0b071030305500c01d08003503484659074108140d480710004002e0150880103201070416039501a650700d4000d409030f07115449580341c4c503816424031829207818203030b03100302400382550315200300d8000c1d8410b01558a039191000905030301400c0002e1028021035000030403070300e07401010514022001003007482d9684070751100c141094185136400307180100350240b806403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 46866344 1250 46865094 46865123
    0x40c05070512030903030109050a1116020f0a06050a050d02040801020c060411040605091306090c2d0e01030f0501020708030411030607110316110d0318090b030703060b1903 76
    0x10310302500b0b02d411100210b001c0081007034074500030040d0390442d021400045611340b208a444000b034190b020f81800a001d01007411106a04035200f0400c41c07500a1720f480e0281034400040c000701c0c11060040c5400f1a400304804141c4521500c014510020030b41001810719460b0a40306007039030f01c0006890001d82c869030503c0207000d0900c01002d600c1c00f00b1070f010072000e0320b001c0c082014128014400040c480740002c1c264148800d41d04084403e23640a81c002d0002c5072120950520070243c004001c9001030b00ca0607080710f0780095800d8509855070114601d1181c0c1c615a03400c80d4104034940300300d03010b5400740700e000700080e00c140286000b11710903510901166100d500340340c84d0a000600c0c4000700440052203a9255402000b00c40c1c1c074540d141c540a01d15241c07030074480c0d030704c3e88030040f00b84e080184458280285940098520700c0141102c0140c9074007540c501d001d900317075009014400da060308000c2003000000c1603580324400d8030b00090800e0025108003028400c41003065401902c0826550842 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 46867594 1250 46866344 46866353
    0x203100506090a0e0a03080a1410060f090302150c03040e0702031902010c080601080a09020a080c03070e041104020a030f020c1c02280c050306041506050d02030318010e040c0507 78
    0x42d198007001001c010412070440e094030554480a2140c05800c2c0f040010104031051221f0708081c48041c0f100c116000c05092014500d420a20180310310400606100b410204141c81900020101c0380c00504c2d56100000103040007460340d01000720b00550348004c0100160f55000352030094032502880d0044d43e10b61005868002580c2c02c281d18640c116454200e00c85c080c540c0008a0b503410120030718142942c0d654924880c6c1c01410020f4000e544824051000a03c48800059810b00910180e060b03505155881018199824080e240201080710500180105091a5002d0005490b143ca0041a8104124948012a03001c0200e00440783c010500d903460024482560800142c124402014240240c00c04480f024440007207001c4e003084003900f090705120300c40808101610000f025112507040c50700c0c080550a42c1160644000f60034600d0000b441e01d04103032100100c0350094059441c1810880000a04041e01c00401d4148a84040e544a840e2140c2c403402506954545400303544241c50b003030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 46868844 1250 46867594 46867609
    0x6060608010603020301080607080604020f0d09061d1504020307030209011e060503060a09090809060a17060a0e06060c120c0106090b04050c071401111201090c1409011b0203100506 79
    0x180043c140100300404c007075000000d02c260311403c0380c50f00440f070383c0350000050040e1054a5504d040c40c140820480041032440d4410300450303220301420803819440a41c140c200c1008161140401e40112241c510f890381c0b034060341d552007880142134840311034803036000812000c0207802000014006107540c3d15880705210034100601018103003d41075180840003c2d00e8112240564602c140e210300344803003040b4066040e181000002400c840c0c8482c4c40182c01401c3c0c072010b00300310713104804540201c1c00c42e0410b54601e02c20394043d2540302d17045540303510034080564011045c10166208070105040320072009409040c041d0407540020890307604c0c0140c1801560049104203118510781401c0c44120081c00d41281d0a01c1d5000c0c0d500004081003500075801869031032045144a000000c41800408c5600b071118140c500c211400c00004041510443c0d1211241001040c40482041500c1d0030b5030040007100801002030440d13100112050340880c0c10310030b40340c0c10814103035180c4003031007243d103010003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 46870094 1250 46868844 46868849
    0x9060504060f06270f1d100b03100203130609050d0201140906060d03090b1603090618031103070b19020c10050301060e06041e03020301051b0301090203150901030606060801 76
    0x30188003c0f81030480300003c0c5541c003500c1d4245503850307500c022891241a088030407540310008040010125100e1010016104c00e5481c809902400d00c54001d50343c0d152260211703440024008101d03c11250200c1e0340254009841d40400c0382c07001ca004030000f0b10702c0c0144000184075201405401110040190a5400082c1600071203407a04003049840716000a846601c2001218852000d000314101500d040b0607a0300f0603d050720000030140c2c01144048611441d90784039035500818580e441904a0b170b08500030002088203110701c00100040380002d00f108401c51401400d0764221030340ca03a01100c80d1380c4130305080b50040031180040c4000540500c200328a842c0c064035660b2410903240c600400a101c1401a0800c2c88100c404c110440e442d001f0039038020340002104080300f181106001307010750000c1d10040344031b5070920000422900103e20290004c5c508415424207507428820304002075000203104010754400461207a0440c0e5031242180d00035030107000d001551a0401e04001c01070360058 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 46871344 1250 46870094 46870121
    0xa03030e070b180a0f06020304061403010803090111010f0204030f06060b04051005030a1401030302061614040b070812190c05090603070c030e130e16060203030112060f0906050406 79
    0xc6010004903008004a54054183c0706803104203800c4000003410003000c039002100c180140d02000f2070942e40000c018800d40e952503d540700c1c041000c08241076984030900034504036400600c4100015409052113103240601c0200108094840e50083e40c00c81c3c000e644144c0d0038849a43c1d00030240f0019111b6000a8154003036203a03d443d0402001c60004c4640e00e00c240104540000000c03250311403940120380300940c0d0b03c3e03030f40002d59403410300940d11002965901040b6440841d0754200501511040002c604006c1003103090600c4c014082d0b119401c4424240c0700840e0407c4414001c2d8000c640b07585c0301d00712081c1c824500054402180d0111043c18004206104080091221a0b542d50042e00d0f881011442c4c10f103101c48292408454003032803e684990020b032400403603a02100c00d500b000c40002e18440c116480700043e5405170424038098451040541c10800050021241580a413544a8001e0b94041004012101041c0868408036012b803802d42d0707a2010702082102c5405002d1203804038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 46872594 1250 46871344 46871353
    0x9070e0c0703121b0c0c030b180c0f100f1b0302070303080109020f0d0203060303070f03030204090b0102031c0b031c050304031b020907050c120705060609130803070c030306080f0a03030e 82
    0x11600e030240d0100c8400005042c401078445c10810800e558079041c000c0c0d42d201c242031900d8104001c55040145803000d8052150044200d9480307a800d1920800c680040f004007841040a01032401740ea8228801f020403082119640540a001c0e800013448003403288a0350041a200e03141d824003d18800040c0c02241c600c0b0700401c0300d4299104824161408800d00e03d000580c2c1c2d07215000043d10b14460200c00602c8080c0b4815142d09054156000d00100c0760b5100c4c0500410800000484c0c9910403130b560200b00c4020311240804004e03881d0300c00b01504401404440a0010002111242141d42e422200009a0020811040550100d001441c04c1500d000700128130085500084800b2801000341d000c000b404150017030396104c1005201c5504420f03100039541d60032107003811615032070101c40c141e00501d00c2c080420120030b4400d40318000396403ca0303042402c507140c018003100e0600011300700707074201a2100c50114031040140061100c1d46800c0c1300801d200c40680c031b400303410303a440303481c1003103080c1c12 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 46873844 1250 46872594 46872611
    0xc040c05040b0702100905030a1103070f05010c1211060a020418020703170c040b040b04050f030307020603070e010e040f0b090106030b060d110403060203070206010314030301030f0b09070e0c070312 87
    0x1504143c650f225070407103140200d1204694201e03440c01c080d034800f6501d84902c00246040c02035401000c16448010b4040d9040151201031600c125101881007a0000d00c1110300704000c10010121880204010301d00814003e200400c5140381034416034a40741342a40c002002c000d050a400c0305489200a620f005500306415501c2c003030701e11055403008443c00b000900026072100f031180101c80c05010030b0390f001a169600c0c0d02e514440c0c0d8000380500385c0540c40e000b001c14a03900c0c00205031541070780c0c02031200340386540b002000c881140d090045181407101100002240d0b50380da00074003c0c21521200c0000e0071010400070842c05403010303448441818178011348101d2a80b1813030308803800c0041c0000d000c115a0008520b05403140314591014015238400310a020400e0303408038601c3e0487e8010b200440b601c440c0b200d03c094882c4003c3c44000c1004189040b01000205110b101c15408421030043d6190559140340213040c0308000c8400100010700007608404041e00105c100c07001c9864500104480e95 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 46875094 1250 46873844 46873859
    0x212100518010302010503190e03070c05061e0f12040308060306060109050604141302160521040620010504060b010207080627070810020304020a05040e06010b0d06080604050c040c0504 81
    0x31043c00064100b10300080021a0b2121007450494280e00d407207410003240d00040f12540d00c90300840c00480316907400c5400001d07a4030746442607a80c02c088800008401407043c20700c1d510658400078000c1d0b0f5195003802031a000d50441200d0714401e5000ba00d9000c464038045c400c1505002008140606201c080c14040c480c0d600d51340161001c1e5285141d9490811240000040d403130301401410140d8940001401d090740b0700c1d080b08050090f80300b00115500c2c01c1415103042c20094600060b03940c8104c052004105042c8200c00c6140b00c0401002d940a80140d02d030507041c25100100c4090b6007460319030000300001e580c10000f4200811081024080034141880e00d54083d080d03030002c03844620004070602010650078001880103006c0f4a0846586191198840c2d000c1e4004803030a0f4854001200c1c0001d01e4101401000707034001080740985001c2c1c1c24200240069004400400000c940e200b0021a00d00b6003084942d016a000781d000f00904d000c48010001512001a038036410444244401c12444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 46876344 1250 46875094 46875139
    0x703091a0a0f0609050f070f020a02031204030308010503030304050a0308060402070209041b05180a0911090108061603020702030a0615080d08090d090302180405030f030a050a0b120a03140d02121005 87
    0x5101c62030904110888c0304800c074a4481240c1000c0d500d400760a5010311034410302d100074000c90b4400d0303c0b00718490ba80e031801c040c0c982c001147e02400c3c1d50810394038400000c8c8542290355003d80020801424055039402144200c0f00c215400c44011140e140240ca808010f6a0440014002141c00030700801208030300b5090300c1806000d210101c0d440d50703840801c11890601102c1001400351004909694032105c84da5541803c1c0c0c0e0141514003103801d0303000d400e4441d0081340c4250380c0150084c8a480100d60390040117000a0700448100d200da54404140e4800501140c8881c9006649400190030201042e40c1030038072a001d02c2c0c003480032640d0100010b894410b03107400148600c030401001d580d103900303155085104070100c000c4072240c000b00f0400f400f0115417055006085100040000015242c2845100760903805900c072258040e10302d43c0006071081030243c0c0703140b030210301d03403030030f002100080c2426070b000b24065007501e002c640b00300100301d165000d842c00101001c85040341408503401c68400d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 46877594 1250 46876344 46876351
    0x50c030105010903060506030c03030a08180604020105180a08032233140d270c0b070305040902040305060613050103030c030f030905072601140703091a0a0f0609050f 73
    0xa515080012088d80e0140a810326440024041d40c4c1d4881740004014043c0200700e66240180500c10514001800700189051140d681a15101e29100500c102c01100311040381e21103074440c2c1415004148100c0c00e002070b10000060340e4a96402c421500b03015480d0007040e401143c4c1c0c000605006d000320242c01000e50307620001c407110035100290551811500407100d2100b02c03000b400000780f150b0b08424a64044035050458400c021584404650700d4210f80312241006403594102510070b0000305100d00040c40c18078440d00b002c61800788c0c3d510580060340c00c954015038843c0c1140c0c04009160500059000c0f50203840c0004000c15030440c3d40291800c0385180b805410420760303031004a4480c0c0a60300c00c101c01c541000803100602d68904c030003c201b082c00100c818805030110021070314040140214001c030002001211050b03582ea0b00110010305180b0741c1614044040841c40c10080940c2d41d90f14010401c4410125111204800080949006501105610303103468104208503150a181da40c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 46878844 1250 46877594 46877603
    0x10b0105070c210f050714090708041202030c01060306020a08070513060302090d02120f0c032a030703120801050a0501050702030c0f04020c03040e160207030206120703020409090510050c030105010903 88
    0x200283c43c0c2e1000c030782c02089042c01804c0405084001d424850b000404c0310440d0085100000c01401c07020500510300c10a485110204a481021034006450614088005481c0d0320490303091910600c101400d5030f425502c00d5403041d90000b40984c98036401144103500c59441d003041498a00c140c030407801d404e60548110800c1503400304907010260b890762001940079400400c80b01080d550840303c10380300c168200239003840c2c0c4249006024a1f09020400400a010300c0000c803403d40c21207541c01e00c0600913800f1555050058803800700000d584010035030740e04006540c649640b503040c9020301c00b0382c1c41a40c100c5418400103004040c01a5000501c0312801030301076620060030143c080c04130b0040d0103502485041400701140205415126414041c81041891b400c00c4016000040907616400240001303034100d2010895440a9490380300c00c1038111b029440c00600d03090b611a840c038119500700004076519004088100b400c1c2d0802c0c0101e91b0003440c0c0388449451540b400e400600801040d02c001407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 46880094 1250 46878844 46878869
    0x819090f06050f04030606090c020105060411090f030102070803070804031101050f07030e07030209070201020a0e090f1b070209070801090c0f021903020c15040f060507080f0912070801020c010b0105070c 89
    0xd6601c00c83d02070b10001c41e8050400d209040e101d09136031020b0000f4000040040d80380800007100c5240ca0b006a429200310049007502d0011f202e000d120140b4010100c403038056400300304038000221250015803046440b9500c2d084142001e00c0c00400d4020b140700e091802d0382c10541441610005040000d40041d92400d00151441044c105a4240840743d4800380d40614550100081640c040d002041076502c21394070003000d007a02108114a10106031030290100c0d4607600028940c00e4541512480e00ca040703c4d1039030814419500081c052081142c0342e80c00640c0a41c01041b40e14070034040d4003850059030602e0040000304140007075440990a8412400400c80316002d018140203100c400050308000d40b030f8084248084070550340d5a4014811140569410315000400c584280305480b20298041350880c50601c0c401d40c0b01407541c0010304410341c030041c00411010116804c100001c02440202c00240e1a00002c11040307003126804407125042c08000c11134a000201010340d040306480c603520120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 46881344 1250 46880094 46880107
    0x19080301150e0d0302030c0709060803042d0f0608090a051c0c05060a021e040b0f0304140307140705120312100f170d170a090314070819090f0605 64
    0x8940050b041e0744000d0300010440000414154044010002a04c420301110700490b590600380044420a11a48800750021300050140400c03014a080c0d8801d09e0b6030301d468074060b55002e41c005000745580103030024020034804100340c58100c580702d58011002c1014203003e81c5980c0b20f0035240c43c10f028100c407224000d41074800039980164000134170103070040c045038558a880350201d00254403080d071007040c2a0094145140101d6401e0458080e1020200070505081c2c00c0104021540c00107802100c0800502098070b5120700200042d0403541c0c0181e41c0301c418501e645686500300034158001500450440c0d104010207440003040b51f80502014170050b4041d507400c00780107880d11035078000c20746c050145c2e540040d0368162400c0b68a1880b00540c1034903400c0c00c80503801e603200d0540f07511010b4085000300c000b56007a5075940c070684195011f41011004040040301c003000c02c1d031112201302d80c04800481e0079210b11200f89141c1407901081c2c107120345090704080180101c403215200d40d808118002410703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 46882594 1250 46881344 46881347
    0x120702120403050106030c0b041a090d060e03090a08010b1c02041d07060210020a08070e0d12090806060d0809060c120a0809010b0d0210030c05040321021908030115 72
    0x510459002110115101e0340c80e49480c0740a08030324030007950110f16032000400c000b0039140803507046844200040100e0441584c80d1111904460036480e07004940d0300e880e602040239405041c1c5059820405940e640c0c4a200803c00500456080040968075203626070080f82c80d0a400030b030642c654000c0e0030f17842140078400180605200d0111901c498025401240c500100290003015610b59809582001c84410006401c9001d544050000242aa008140c000d8003400036070004030030250030740002da400c0da100c8401c2009000c010000081d90700c5000c1012031030a0014a400013021260481e60788010b441d1110940540d40071548039410000d48441b014008200146142e0994010940c84429040001c0c2c4411002c480c000b28650910b01542441c1ca000004222401e0b402043d80c41d0500c0e031030408600a00002c0c0151050103010840407001c1035009094101c44604100d03041458181c0210007402c3c0236981660b43c0d081c0180c10f40b1180040e02c100d06680c150741c407400403d5030203410b4410 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 46883844 1250 46882594 46882603
    0x41d09150a2d0203011d04170c01021306091403060f040618060c020a0303050f04050a031d1906030b0117010b030703110705010501090608030a02030d020a02030f04090501031203050c120702 83
    0x540001c2d2100034804041c61a8a600070354100e03034003143e141d0014445200d00d07550710441110000c1c04040c038849000e48408005000d403404041132400182011000454200040442e40040004c075801a904000002c0100747d8524002402da011b8234072810610308181c8410030107000102002c2d213031865200007840c0c401071b80340340b07071b410100511a50308402d0303010307440350741c2010b06600007402d200c0041c82d20784c1846041d902455100c40140384010302d0b33490071201080b0381806140d480030014011019a5202922440e40340300c21014085100d14025000e000c03540643d40003070501034005110f603008001110181d04444210441951342da035000c50440082071402400090f1030004611310083c00015444541070340c190840401c0985c1d02d508000799240a0131110f40016803042007440308001094000e4501012240112814650185400310140d0001e4101940e03180e41c0c2e07001041030080c4485c0f08001080e9a08080150742019020f042143c4a483c0602c03c81d40e0340e44c004a0500c620811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 46885094 1250 46883844 46883891
    0x90609150706060509160e010804020a05101101051e07030207080d020d0509060a0b060f1315020604050c040b06180d021c02030c030303090c011b0206041d09150a 71
    0x11000755038250910b05900100b465000f0140a00d01c01d030001220800840400206480b00c1e4a40b0509502c401c0011210040000c00c1240c00100070003002071aa114008094007400c20354442c0c5034180e5000f4115030031280000c000301800d60640440c101034030303942106507800c848246005a81e40c062402c1c20034a5204000003000c04602c00100480b5015940e405a400313030014030117444680d15401c03515019034050380381c0e075030740088200528081c080da0400113020752074a640017060529500c00215074541c1000f005000960014010441001800d000d44000914203c404110340b81049000c2a00d500844403503c0c0050000034641803a0340d188103070a091a6070043c2017283d800301c0c0d11402c2c1e1421520301c0c8228020710401c451141645030100980b40b00d22111002000c80d1240e1400454086100d0b036803d4440980c60010700002d03868190050029168511281c0d4880702c0741c0d40e0300c0b116544020f100d032505802032103142d0007401d441103003180c01525a02c00810303034549410880408a9586 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 46886344 1250 46885094 46885129
    0x70c0b0703051e180103050105010207090905010608030a020607080f070e040c021905030406030e01060b0f070309081002040611030c0d080c0d0603061413080423040c1d060a05090609 80
    0x81c00003144040100011318400d0004902e0000d445120b00040d82524000e01407203016800200d004d10016030560700c401103840c0108004101581e44804103400c6501a841d10070060704010104076a0540001d001c0c1c4d0049d024883c019807528040400070711458000c00326074030454840c0c0b5441803052080080e001030107400e0003014500a290301d0029a294410312075040440c1c20040030b0000000184200000c80d07603900c00040c900804401c54408550181e1012001d0140c4201b020901071000c1103101c40390302200314016661818001b010300044002d20b826040ca0b8010080c0005110700132078512003a80290a01a1158507904650016405a00100044e207450800c0000c14000107420988400343c0c0403030b40c01e032540c031010341040021800c400044c01001c005c210030044080414000408040241c500c0f120080815000a0036076403190802800250420100361440c0d03100444c0c1c3d484144c0442c1e025280200900e00a001401041c0d0010311400010940b1100703a1075285c15100c00743d112 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 46887594 1250 46886344 46886377
    0x3071709060f010803040506031603060308030a09020f09010b071b1502060a0605010801030515040203030403060504080304060e0f0a1b0905010f0905100f2105062406070c0b070305 79
    0x32441141e99400e0403a180e40c40744045100004101c2004021130f42982c002a00c12803542d41c0b01c0c0c0da03100b000b81c502c0da5104101540c031100007000ca40908040e5000d07203800000802c01d80701900411415403400d6200c14415000344004002c03240d1000210b440c81644003080d41a2480c0e1003081a0080d09a641314440d607112041088645541c04920303180310b401158410000c8a031a41c00444031040e003400020701c01d50050310305d10010b264180c0a83c1e44644001c086134645503c035035800c0c003502d50558040700c000700040280b004010341401201074500c0480700074a020380c07040700ba156031503a46050103010b2440c1d6040b9400306c800e484880e031003e8192810b040c00740e075070340b40000e0f00c80858500c40c1e001d001c0c0c03408010582e0740e509103220100701c42d50244400b140c40d00380380000a0000010000d409100760351656640014002d00c07010b882450080e0111581c00754940c0720b0141c6140300300705184103090400611780050f008822502c02e8680340200141c488046180075a11480f90380c0d0f000d6030f1001c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 46888844 1250 46887594 46887601
    0x10801020903060907030203030307200a080c0f0c01080a020903010902040513120503010b04030605060d020a3c0b0306030a060504050d11160e07140d32010506030717 73
    0x40540003800900310680884581c0d6455418854440c1100d010003507160304104003055141d44540050f40c82d9841d80d030080900d0034441da2800c2d203000700301c1030f00325240e074400314030403203d64414008031380c1d60400b0070064007461500100007454504010048c103601980407a059030750745c409620004809901810410a03414405031166501340c0786141161410109101024a01d209000381c9048172801004a07060606507511030000d000c004041c16085a070007194000982e40700038411001300203910300c6140c0000c10442c105e1940410000031001400095050800780c508036240703100f00e60003440415100e0301d4190009007080414840a040300341410b00340810701002042583e24045903445200c841c0580902c01525000c003d00322000d10410070604101c14602e51401950088041c0361410b039484680c1c443c03003020340082541000c115074034140803c03040d03184c0d010443c940b08540d0520380c198010143c00326098005016480c0a66804004100700703e009030740c00130112004140b80800c030324 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 46890094 1250 46888844 46888859
    0xb032a0d1b1215020702040e06040b04030206010f030203150a110d020c060f04050a0201080601140a0801050301050108120301120c03020406090f14070f0c02031c110d0201050708040f020409080301 86
    0x40c103004001d441036040340c00001c2c5400452201d41038581d4010529001d07841c408018200940061006030380058440c01c1c5403c0303001040c0300c240d10951042048800509007810002d01c1c003070050300545001c5c0c147c3c5000780050380d40000d00c0410101406d00c0c1d441940c0d1a803028078040d010001031000303441c00220b2510081003054000d84100a40071007190742a6a03155251000460300340c40c054010740000201402651054031881c1e800201030602d40b08a00c3ca080310f51144d6070140d0b940c9000600514014401c3d0b26003801000c1c0100604402082e98a040e030120250740d11041c0300342d015003804d80c10b620381048080d03001c4e58000e51300204104540c03941c81c5d5403070014200804204050320302c0d1410602d15141c0031a40e0354018925682c070b070b0030b05841c400d405a031034501c0984280e030f0501c90002046070364001c50300090250781c0d1980d1000102a8012071440c90020991012010f40e4102010002090f500821442d8401c5e00542c00d20711405160020900510315003602800b0322600100110f03845 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 46891344 1250 46890094 46890113
    0xd060806160f02010902090a020a0309080a02070806092e0605031204030209060103110901140c0706020d021614010f051b07060e031b0405061306080703060c030b032a0d 74
    0x70400ca441d1082c0c03410540c0d03000c0342214503901000303501600541c0419103440b090342c081c2100070150300303001459654035144c1ca41c1e590807e200010042c0d0201c0710500080d9818070a0542004c0d40301c2c0104410b604920800d462400c541703403a400002a0b00c50312034040a25604010004d000c080c0680e40d000765001920242980a404164084c080030070109405501c80d118104000010b111454140554070004455110f0460560311074440c05014009644106001400081101e0340043c500c2c0c8050210280c102041424070208842e6140b4017007180c20510600000c80c02024640881100c0600070242e4550042084ac000609800794680b00403540c0000c003442501c4044d1601210544244101070740c07900c1101c941ca1180c90262258109030600e60001c0307400640003028441001c40707041014041766035641c1308042c46d9000800070400d01500d07128a0b0120072607843c05002070b041d1100800e6803880111412000004266503401218004101503c402c081c020402800d200150600e10030a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 46892594 1250 46891344 46891381
    0xb010e06010507030e12011d01090201020606100903020108101707140301090302070902070602070503030703061d010608072003041806090501030b040308090109020a0308070b090619020d060806 85
    0x21004500040340e41580110240c54040d90b069548003650b0303aa200c18031103030740288014803000f50340705c1e0440e11030124400100c01d074000320031700005400111070000924000d0064042402081086840540c8a070720141c41030950344c080c03c1095081d12001c0020310039219a81c403c00a241c100c94806141d81e4001c5802d10031a92200344c0511042039000406081b1161000001c015900c984400c11500c515a0003519403980a90001410b20210b901c0e0b040c01c0d5407045901c400080d40e03c48061002003000c0219403440480d81030382001540c10071070040c107409000741400f028000c0d50011380c242c8220000c4008040c40c140c0040d0380d117840e03079862501d002c94031807004510814100030000c916025130744250760482e50005d2010300d0715100c6840075280380342c000d846040155240c840410250715100200001076214102071071f916410741c140700c140030320041d000f01c0e2190001c8042c00300d84d50300024110589101c840005a031100d000341c0c12402001c1c650301003545802007500b00800114160180d00c2e6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 46893844 1250 46892594 46892609
    0x90e0c07030905100507061d030c070801050106080f0402010c020310020409060303090504021e030711010203010f090b03150105010f11060903030603120f030403030c0e0a030b220f020906031501030b01 88
    0x160300d0326181001084040301041c440010400e01003580841d201e50481d81e001c48c1c032268892210960803c103142140e0040c045c82205602c4102c041200c14824440c681c01082c044c0b070a000305082082070480790071070140000c4d040185180005041d0341d0284000300103040b4410085585550303507861130000d410f02e44000ea0109648560010b035034101402210950301254098070034005122840d1080c07608050003003000c020803070340712000740403007407000394040c06c02d01d81d80f20021441c01c0010402c1d1806c03204842d029070042c58401d07400781005421213064a000f401c10585000121100302d40e084c0c6041e00f42021446480b0611a6404c0040001c50148105070141d44400f10000d800020b41d01c600039025030003003020070014010034030907400310880344020f140ca081300c100342000080e0380986a40042e514030b0409c80510441c885104840701d51800401c001000040c8192a42a20300d400018081d0180f101c2d1000600303555014030644404e0712002c1a403e4055842e820301c014000824041d558 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 46895094 1250 46893844 46893857
    0x4061415150309061f0e010b031902131a070203160303080606070f080d140907090605010c05030304020d060603080415020c0a05030a060c02100f0b031014010e07090e0c0703 76
    0x100301e0079218045030b00c1044440b00420203521441712640c01c08980b520542628120f041010861643d2005042d0091506050f09500c0c3e00306074000c6a08080900b107110b041c148104140011030315650400b81c100c4d0002c07009011a41844c007920340d960300c07648a0080d850300903000142c40352401c252248d13041d64001d50b03510b20150303502d506000b2140b08105029040301c0001c0300c04400502a0307030061210704d00c0358402050700400e20403100c805030b400b641e0403101c0e0f410108041c022046103104020080109107026403d401807501e41d182c8920020300080c1c0102c80c0b041600080c884550001002581d124245682e034aa03102a810920424008200300500446050403d98503284012005441008025141d0000c1c1c41e500c000080080c05144001d42c0542e00214034040d2440c4504196800075020209004003040101030411100507001c0102501d84a4221000090f480e24541136031000d40380140b040e1a640b07016500b41015900c0960025521030030481f0001300c1001414070705209442d0700 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 46896344 1250 46895094 46895119
    0xb041205030c0304110303071202010903020607050301060906030b0402070c0312090b07020609010f11070b070c0f121e020303040303050403050c0108010806060409030e0a080102030906010f14060304061415 90
    0x100c42510040d901c09034002001e0000c6004580301c60707860241c030388000f01242d2910905a890f4400400150b80c4100584d5481e80c2080906030144241070744443c0c140b800f40c0c41c540c10400050010710040c001c8104050340c5070380080c80ca4440e98122040b25420008030340a0b00ea8a01e403c40582040c02b0000000500e140390024807140580d00b6125400c0e4001c20060400490030011203801c00d103444490200560440c07485c2d9070030404c3c0040005848103150340e035a103404030b08081ca41c491071544000000382c82414100690603400302d0b480301840d481340100d020b01c030489481c850001c401e1000030f540b6000006e0000201a00180180202c9102d60140c4055400c0b4200540300c040c4248211800e03a045070b0005401c52901d40d1158441520a08020710b038042b10070046540607145821452550794004140312103401c040114900400b075010118070240c0c1808203c8030030b8141184901e001c0c40012020070b007040b0030381c0c100c40c030740701d50400c40c140ca02c1c60b00d0895258844c2400e92864001c1002007001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 46897594 1250 46896344 46896347
    0x304080a06151410121506050408153607080a030905040b010e0f120102040314010b0d0312051008030705070905070203040608010b1b0f060a05010b0a170901020c0a0b0412 75
    0x1104610000c0c04a1040f48013800c0540300b200310008440d030b80642e82d00b080c1d1000020054a50301400403550b501c0d07103440c10105542c0c03034154041800320000842100b000031144070305100d081260700c522000d1080c11000d40002c082c14450450484070340c0281400030840b04000034000d034035103000c0e580c1c40300200d41d600180407c0b0b4050040c903a00081e03502c0c0500302507090145642c0000e2401400b000640d6000b02c0865089030402d41084070034550700c000703880800d0024040c41e20000011030302d4075945166139501400d6550040c82e4020000e45410000c0c0861512800c800b00414550058a696020b2845c185490311414010328032542d00d04000300e0086440002550103440443c4c4948143d0b0b424404481a0307900315580d0112084d08468144455113814415201e100140100900380d07070818000500582e881600070203940f200901c1259643c9501603407902008640191000040d2110140c4a0180c4100b140d420000c0c0f080340c28110412070607224061107580250b5000c40000c140000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 46898844 1250 46897594 46897619
    0x3100506030d113007110909010e0a0b0a0603120c061103060105040b0c030c01020403030504090e03030613020306030a0206030c040e060405040201050919030c0f03060c110304090e0304080a0615 85
    0x20f50900c20740c01400022038883c013450440c0b2206013050704101c40c0280074020360280354409a0708442c085c540445090301820000c49150b003250190f0028410320364100400c40d80c500c1845405800710f540b100c08210707000040d502c00300103942c00118044000b440c046016014041c05041154003071b00c1e100580002826803000c2c3c03070259005940c1c0901e00744c0303014500306040c1c00c0241001c205e40000c0001c410b01101c00d1000300000d5102e0b8807a039880e02d02d480c01d03000031909100d50301002c130740081081200c19901c2c1c1400c484402c10215006860362215408280780580201d0003d40142d0b0002c02d020403800e5080140040301c0703d2001d041c0860f90344c0c5040c4400e0320016200240072480a02295200b450606107a0040c0b0b0001e190710009075039651a90414841c00742e0040c01280d1aa04082c414808a801002c900c0355860030007120020404854943e60300c15403050500e056511041001403203c107004039001000c07035608580c118001c03801d200c4010702106400c6120071030151b10000f0842034000d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46900094 1250 46898844 46898867
    0x905061807080112020604080d09050102120c0a031407050d02010b0f0f0a050d170415030e03070f0204021c0f05070f08010b0d05150d05010b040b010311030103020d0503070203100506030d 82
    0x5540b4200d40e441c00440c600c41000c242c3c0300704c0c1c0c807640500011a07080000c010000300e44035982c1c3c46130f2031704e4907100000e82083d0482c0201c1c80c4c541e00c108038a074480000083d201103c2a81440c0101e07030400d418001c0d10b4039000340b540c0104180940368a4207681c40e1305400100d4525400c41e004141c042c005010446003502c8034502c1d9800100720481005546040c28454001c540103030015001901c88200f07820150303106800c2205010f10310035074040555418801c0c440e8030702503100114a407507800d8440d0546900c0155000748100c0d00002e80070f1842c0c0c425480040542c982260512a44281c45090400707014100d600f0000076000f280521a80c900c14500103040720781c898134145c076001068025001602c4000c06a406175541001e880a150301c5002407070020601a03c000a0802c1c8200c1c204415502c80c504118101800e00304410b103036100100440341100d0341101c40c14191105860507601314000c1080280d4103000b824441e5103484182e4100621854041702991101043c0701c40a031140044807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46901344 1250 46900094 46900097
    0x6060b0c070306090309210c0b0c100903050d0c050c100c14180a1d0c090a0506030604060905010e0103030f020d120504020f040c050901181a0304031103040905061807 73
    0x80d01c0400108242d03500c020141400703441c110481d10b850b8012607000d904034402c108480952441030070240003000301400090300501c2c129130320f490800f1118950359030b1800c450302c60075550361140b03000301401001160110304002e00d00b4000e001d168240074010760440c0d481c0790355a024003050040031040303a2080390b8295200c1d44901880b40d1aa87d100411608070300c101c501c1d003099200c503010349503840341441e000418001100840b507449040d075120a5140c0900075007500f09044c44070401076030300c542e4100141d445c1035070151f4927642e80340b0004002c2c002da503100b005c00500d040004115000182c0e00b96040e240203880d0307103c1c0600003140480c0d84030320715107104000500d008111540c100700340d04200d82040c0011302805101902c0800035040300c00c490310903004100c0000b5540074650300211b44204ca5003120445c4881d0030b1805243c1140200e00c000ca6070510070000001408250203003420441c1c0c2c100907000c49840307a8407960302c44000c01e41500c3d003e2282e52031fa40b10480144001201c1d52264101d07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46902594 1250 46901344 46901353
    0x60e070503210703140c010207060c030c020705061b01060b030c0a020708030a08010302060703032009040c0503010e0109050702100c0906032702060d09051516020307031e090302030d0c06060b0c 85
    0xb20f403400c03a031a00d40050503074205d100c04c21042181da00300340090300e92140241c40010301895038100140441d100d9100c010150340101200700308698583c0241d58840c801c10031008404004040030078010050381d0031603184a00c1c003109018480c88850090301e407d0005808949000d5280c0e07080c0c0d50743c2c2c00f95520380307000101103400601c0182842d401a0182600c24140420001900e000340d220030340d85d80600c186014008691b281c0a03191900418030941c415082851465041003c132030940704050040189407074540000c140d045100300201160842d203210100036150360000014900100c5106080000b81400c4001c1200d90800c05089035104426410742105242079080c06415002400015612651554018041803041c005100181c0c10300744680e0709403803ea240c030317400c81001101200031940203111030307000203400090701d202421a00c0036859488484440071601c188150304025014018480100d680c650007400742c01045114071400c0c0301d2951101812185801900e602c000c842e0720 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46903844 1250 46902594 46902607
    0x30108060402011b050307060b040b1005090904140a030201020406090504050c0702010e01051308010906050708040302060406091110020606040b100e1903050601031a070e0d0b06030a060e07050321 86
    0x4500e201000604100118100101601c07283e00310740020030181d8005858009c5a03c3e9440c00f071090700e180c40f03003c4918813400920100d00030207500a0403400760280100700c0110b001c2c040c00d041c42e007443d1103c4070100e52100c1614a8024040c0d0030512828012454482020449140c98025103106101000c0c0450800155400440d051560340c20040e040c00010095102064010503040002d071079803000100d01c84410740703410011240c00030410f8040092480601c030000340d02007001d50304a034100f2004540c88120f81001c0302541841147d103544803000421800074960007203030407445410120b07410401502800180004600420041000504492950202c610703089502c4032860701c16440b603010f13040d1250f5032a458000c007a00144c500d0308441d8541072418440b503021503840010392902c2c590442c8030101203540700d00b840400405c280843d60004800c1c0d01e00b085265801600706500348240c7c8031080c0440c0e102c0c00c403070143d01d019028522800d80240140600482003e1011140da0701c0e10300c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46905094 1250 46903844 46903847
    0x906030803040f151803091203050304020915030607110609070503031b010204030f0507030507060521130c0e16021b0105210406050f0a0b0a090b061608070605010b03010806040201 79
    0x101c04404803031800790f20255050100c40d81c0b041e45244d00c514400d00541130f000b0304002c1c00b201420f90050207039042340121440000e85c402d007a66009a410360305401580c40b00d0740d904840e90340c446401d40e014410760301040b82e00341e80085801c41100c003002c00ea0300d4684803800d60645440d46400303501e40683c0100403000e82c0c480c80c4102c04185082c17500005040036280d54074404052a528019103241c0c0c0b00480031f2052003000c0c002c02d00204624281689802008040d00002040c0c8001005000c1ba50324000303286801c40700d43c2008801d03801249120820b44031303058903200b0307803003a2500c04405603203940000d4038074000108181e521211400700500461100011981c9606c000c81e040c4403600002d8888107442e40d17090340306d4011441184007040c10f01c0e085c000b4469000700101254080c90030f0144480396030301d5258000007603994182c00458280d5503080807400354412040c400581e4190a0900400e0000a0300a40344152141d82e06000c0359a840e202e11003103000078060028a40c00034400b040041d03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46906344 1250 46905094 46905113
    0x60108040b150d050102030a0c0801080d0e0a030206070506010602010f02070201091401200d021603020d020f150409020306030d0801032d0605160e01020601080307060506062b06090603080304 84
    0x9200b000400000405260100d544800c4491088806a40110034004075030031034010480440043e01d49040a50b152064207541c0e8098640756205010314803082450540390800e5040c003468020700300d10b40d1542a45401030742c64109114110055180c6101199416004c0c002c035059280c050350703101c260905186010400b1400b201d00b4174180001d46d8001038030300805502501c002c1d000e0a001d0030200351f4000011f424041c08140301000c80c0030703480040c80140c0e944088464007603010348002c0c1687c0c42e80d00100b140301300c8011840351400008200001c450040c0e400851244c1c1094090701c0102c000c6441c1070321108400c0c04004c5c02c440701071440c2e050f00540b00d44002030002c04009a10305101558444408a42007510901c082c26a0074071070291441e00700c0f0740761902980030301c002c0c030041d8501905d4948038000c3c00310007010280c0b01e60201c0d49036540c001c2a981c0718021a034080e0448405110607002e40c0e050855840e801c94201000055080150310814040f41e8014018a01c2d40d990340e9682d0707054 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46907594 1250 46906344 46906351
    0x1206060301050a05060d0b1804060c090e2e180f05130201080a020d1406010e01080c03070c0807020a06050702120a0201120b03101406011805030304090209121006030c0509060108040b 80
    0x6c2a622203482c91183c1d80c04448021944510100b0101e50415040070020380f103111817600c0c00d10400920400046895903c4540d0108282c0c14002d1000d455584030286103000408010500e00103640205014810300641680f040f000076040103021750010740d150030b41e10215452000c80484d2850680554065202a540042480801032a040200c810101150044070014081d140382d2010843d580d40c000700d581c41c1104007404c00e102c2501d40705c5884246444014900000c014404481d101041011015180040c2c2e008190250300c42d1149002000c40d00561001d078803030100c080c0c040b00e2030b100220b5445820741c5c045e5507055244c601200c003203010b001050032894041c4110700400c00001210702c20920701246040318600d413070400308001040488241c041140901d08640200721035500003013180c0c00c8a028490142e1100258070020300041c40d1502840d5080c01103c070401d010410a42c0000d003a00c1c4221450a5215101c07001c0c01406041104d88074040758025000c0b40100d003180a02962 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46908844 1250 46907594 46907617
    0x90f06051f0306020d0e0105090a03030b0111060901020a0207151209030908060906150a0f1a0f030108011e02040608070c02060c0f0a0605060d02030304032607081206060301050a0506 80
    0x1d40031000801d414403910380e00907114554003080141c1c501e800c6010301902c00101c2c5000340014100008603a4496920001c0101807683d241047e410a0340240c01c4900306e00314036002d88440c1d1400c454114041e41c00014000018016100c010900c18400003110251721040d0b0303680b2b0000e000072001a4001e0412503825020301c0065100020401401c101d00c42c800c4580201500c0142003045842d0300100c80e210b0350740d20902200300207000b4100100d0041c0f04440000e0442c507416542454502614899000d41038480b40f4000700102c0d04400540004c0300d9020103984103850702c3c41103441c0b641280914060361300000d440c0340114100a00c20442486070600040c4170f14645100c26075100d00c1c1440c41041c041607600309a2903c0203021186c4a102d60020701910390881140c010360000c0c2e101e21940c040148000042c644840383d202d00703c00d1443c0c032070002e0305926540385c000b424580131640200101404040c80c1200045460801009803812100040e209210040c14001000030903003014000c0407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46910094 1250 46908844 46908871
    0x210a080a09080c0102130501031802040b150c1c0f0905040c020c1002100f090308010b0c010b0d0f061a030615060702060a09180b06090d03110a050d02010609090f0605 73
    0xc40c41042c010001c041107600016a2420071022074400b075142540100d042c140b402070ba4110103400c0c0c81c00c1e440d58075812200016050f0481001502c181c980c159202045003021407480cac0101c0d0000349584102d081c0303c882119012055201b00d881070449001c9100048540c030b000c22090501c3d030411107048115005035558110030a010424a41d260298100183c1c07040000611411041c411100092101e07041801610030644019166000602c68a90781c908002140300400d6000e5014070301ca1000100722008081e03490420703464940884009503840d81c540443c50310544002503640e0000140680580030b1540c0d10366110340101c8008001c19000101001905c00607074a290003402c000d010358036130706203076030904a00d8412034140c401e03544503141c5407040312400740e610701040d0383c2032210498040712107103214602102c1c6d40e005440c0b01c940c140304540112080040120f0303080c1040b43c07580e0003080003da0b6400c0c080155036914070081c05011078030b039141021400c240c0100b540107018410302e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46911344 1250 46910094 46910111
    0x80403050705010519060906080d0804020a09090302330103030f11070b0304110a03080405090a06210210090b0403020d08190f02060606030103240b060c0102070203210a080a 76
    0x5801d54004035007403902c02604503800c810800c058407442004c1c101082c402c001003270070122800e0740c0303003803540420050115176800a011540d901c0ca500000e012032a0041c070820400345030103541c8464440c440015241d00c40c08410014401c00c455034000c201e40d450026490340fa549003034450b00042c901807001c0110109410710f21090800016009140c0058001d59034034040c104000c0341280d20101e244102c1d00c800041010079000c0c0c054600b5107004456a05017500d448214500030f01050788191401c181075411400c075980c42994810009000303542d100544c2400090881d03002602d80100c2014074820b10040c409403c03c10b044005241c0720700799080c40d0524443e6218000044891000009200040304c0842954103100035900322205498882c110f506503515545148400c0080c1340010078010f41042d01f004140e00b0600c8070810141c40d81d9501d00c1c030024480e001c0d40c0401e000343e0007880390f2129600300314800c1400c0c06c105107010030320a0920803440300407184607001034403080599031602c0d00b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46912594 1250 46911344 46911353
    0x30c11100f0e0f0a0b0a02190f0203040504050408030f0901110417070e0c07140105010501050a030e0114070306050a0b03090307030f02010b100504060e33040b030f0f0a0e0d0804030507 81
    0x4906494050801130400324440d15298040c0500142414a21030044c0700544030302c0c1e03024454242910003410096130155030950204d01c0d40c021944880d6000c1c2c200701c00d00c018006004000c0d07000d4400c0154250721903a0b07580f2800d00740e0f0b40094101051039010082042049031510400b03503100d82450548100c16520341c0318800648081c0daa8406100340003911104005a081c809804c54203010300a000941c5490000b8000e402045940014107403030300300410780140c0c29404417440194850280100d070511000080041010740105030080c0c04101010407521821003d80340321701a2200194a0080f00380d03011500c0e14060003642e419592502d160032102d50b00c1c1c10860040d00e6099070780c50b885a151060040006a07110120342c0a220030015070807500215144942012040e0309401c04d41c81201c2c5071000c00d51050360301003002c120011007400140030f952000c0c1c0780a812034205215158652855000484040c1e02035400281c0c800360515201c24094480c01341d0260080c00c0203030400d40d407502d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46913844 1250 46912594 46912603
    0x807030605281208090310090f12030f11090f030c1507150609020706060e0f0103030315050a080708010501150912060b04020d0e0d020a0515060406080d050406030c11100f0e 76
    0x2244c25900114100300c00b410100b007101207140c92000c0034032083c907107034445c0000c0d5104200090b1590310300010880e0024083d0f0021443c00003003400c100150410801801803607008048400e21440400d4040001480c0c002050241d0000c000c114031101162154802c40c540d00042e801c44990740b0394980400648500d1040400500c6001c80169440c0c00310b10301081206c03183d40107080e075400e0310014400b200c0400b060386419240d050900290151050302e0380550204141c0c085580041000c00c0403403e03040114044040784e0082d002400741d6600c0321104007225150482680004d2200303a000c000040f1000d42c5020510300500d00040c0c0000c0050100f4247c0e840001c1410760907403503075111581e010003080880020780e007030702c05400c41e00115500c1c1900c6d01d01c5404c0c4841c4004103500401c050b959a548400c0c0203080300710032610129079904c005040b50304203109000101e8036050301c00403501e0090300b4041030b58803290b001d0500d0024001100000f0901c54503000161503030b604191016150803c0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46915094 1250 46913844 46913879
    0xc0303030507080c0703080f060604050312090907050c030a0e01033e21040203010e0d020607080c040b0406081003081605011b0206240907030b01080703060528 70
    0x154007142a01d84290054680140507140291a070401c200342404294403643c0c0d16001980c0c0404031000d9242c2a00045480c01150081036060040d822400000b0340c0680c02400c96610503540d004c0b8550740c881c0c0036112170203000303405000b0790410404e04c00e01d244299036507550700505050004905e1000c4194000000980316070800c0c00084003a4050012400742e0a101c0340130802400500d410300c0684e074000d500e500445510404103003140818110b550030b4101e00c03000302c299022a5800300795200001d540d87d80903100040811100404991150040701c200c500744c03942003040700c2c641840d041040300c10080041050014030307040c400c003200283d4a00010314040d110040a5100c80d462803d01508440040440c49420f07201e103c103450f0780d19004156580c0c00040b42e80308030311101e415031020440c6d40b070090317205600400b0b5404114000307801d039100403c009020380e80d0141940c1c82c42016411180b150094580c407800805040b200c101c074121201001074003a140c4c4010392036407044116428480e22 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46916344 1250 46915094 46915097
    0x190305060c0901021006060509060c010e0f0d08010e01050f01050c01020d0504050706030f050f130203030c010e10050603031201030615080a080901081e0403030207140609070612230604090c0303 85
    0x604010b150b9041082c04007403d043d200401021745010700c050014807950440c00e024550225801e548200298030945400200806591509815044140e120070104a00f100030424900c00424000020034440303060ba1f001802e071a1744080030740010350307158014000c0c18a2642d001c1110307207055207450060030300a030f20a0300100803841c200040601565120141e40794598582800c120b0300031418194680c00143c04407044070400e880c1e0001ca401c51284000301000e07982888440c0d0401880010031002179505000d0401541d1208d004241e101d2180306121150703500e031000140081403c5a000ba4040542205685125903445484c0303424200c5091069503800c0e004102c0c00300b556003042c1d101c2d0780516158125003140f000611505402c40019102a00f055030103d00d200820880303000601894088a044802740c0c0740021000d50b03249014001c00d40003032412141e041c401303140340c0681400c103d005034050004d07102c0f03c01c40510340c00f4024825a0703c00c0d102d0755942d001c07a0701640080b01440c001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46917594 1250 46916344 46916347
    0x21010906271a04090c180b010e0d02040213030b0412050a05030406051012080c0f0c0109030303020703050409021612030203060109030609170f040e0c090f09071101050117061006020c190305060c 85
    0x40c41416506205400c40510300c260a115201f003c50b80e103d850210306e540e048400141250090002c50002e010f405a2030090b04004c02e00402804240807541e881148141d861008459401340c04443e140640d000c0800490410304c08280081d5440d0400369001305103800780e03003001c0d9881c600e0051074818150b06644540002500312969801131080000d00c01d61003008212040c0c854000038454003461201808150b404a000001c15120300c0445000380b015000554941074442c0e150f04a6071082c6204503031010640d80c2c4120740c58068000d4074030592058690b40b2800d80707541c0f00c19000c0e14000d0002c4918801c5000b9598010003080b000c3c00c01c6680d101c80c0c0942701c5003405000043c1d480c0c0a048032444400501070b03081c490303a40040940d258102a500110940c0340c0480949000c0c1859000c1e264039420200041440341285007050b00483c14001142e0085d151504042104c8501d8018100141c22100045155050021000006010307081c1c06804065032030700c0d01d034280101a148501031300c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46918844 1250 46917594 46917599
    0x10060b22120308100b030106031e05040b0a090201051c020a1b020a0b0a030e010e010515010908060103030e0d0b280c08010e0a0221010906271a04090c 66
    0x1140301110032100224203080919400c100d14191405880100181000848000201c1c0c0c00007030300c407060061080c184aaa00c0f0b584821014024100040d0400040c14800c480244a0521406100d001c0c580011745000180c58120350300000e030512900690522104220074115205200001600d07401080d0f8010b072203804660000f0521031060b08400c040c00712008031400540e503408134240440d941401b20036038800300c0580541c041d002502014465500e49084591001019005244140902200c0258500c2c24034015a044083c40c0075034041c65100c24010f02c0000e0145080403150342c801040021041e80568401000300b00c126181c450140441c4140c035200c0c1d40540c80c11002010002040c4003500d50b0100040c92400e05105002c0c0b18002e207408218248080c0d41240c1030b03030741d48988803c4491000001d40e80ea600c003c0c443c101c0c0c00c62a054002804160f00c85040f011103400030724840003504503e410401070b00040f818003070f084482c4410180c090340c4901c94508043e00c01c070322031041b851 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46920094 1250 46918844 46918867
    0x60d14010b030712020310120f060f1112150a1409011401080714040b070b2d0a0b04060b0d09050c01030b0d03080a021b030c070902041505030910060b 66
    0x40181e0200320348610600901208a8001140294500021000603140c2c0c1d1071003268004026661b00c001801c400350640c02d0b06000f1038290401c4154082e10060045a400c9107468045a41b0408003400d04002400001860006095007507001428880c0b601c00d203e00c0d1070005003500920754080c080c58000c6003000c041505107215000d005103000e1482038121605540081c1103c00b00401c001c04200c0a92404c03c0b000014005907800b8000101885888100750715001c95510015151304444907003103003070201e00b041502c034010202c01d606031401c002922403040307070070150400050b003d42c0103441c1c2102240c1e000148011f000e4141000700081030701000703410014200400002098105410040d032708080f07032034038420480700943c185007004055440d201150001d0150740c3d1400306141d03602d4140c2c00a518000081c002e582d902c001a198003542c4c2d906d840040388110711860044503444d02c220101d83e4040e0740a958440885405d440780c02c0402003d030401c4a48a401540c102d40000c9a16030840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46921344 1250 46920094 46920131
    0x60b040602061b041401090e1003050105060909071a0409020f030f06011e0e010c0506010608011e0f0504050402030c040e07140406030206180607050111030610020625030b060d 77
    0x5050702114105019650404000e03813259000380c1a00c00d00b060b441100d40d900c600e0041d001401c200c21401c8980c2003100181e00715050300e20080d00c40b5800d05002c01c64901d45082c80e2401160140e0040c44d0152030403807096a0f450300303d40e0115042c903091000045c1d02090380001e207600c1541444141d40d13440c103140c4c400003140c0082d0001d0704020b803251908802051084003080920900e0a2074121405010f0040382c407803140d440020118003552000003200c0b40c005540505132120203554002d072000c01c00501c854000b00b40314141c8003c0e401e010400c11428541c2c00150071a0000d01a14504150b0901182c26200400980d80e03041c0e200c27217410003002d014000c503501c0408085500340685451500041e1607030180d624034904040c14101c03580c1c000c1d80c03020f046411080c2d124000340038440610086d000c0d55001200c1c5180502c65180f154115140301140d41c03441614031940100e040c0c440d02c0d00c0c030f954800955001800340740d42c1e50740040440e51054080c140d220300104010802002102c08502d6a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46922594 1250 46921344 46921351
    0x8070203030610080604090609050109050706181202010c020303070b0118020a0c061805120406170421050f040f050a05010c05071205160803030703060503061303030f0b04060b04060206 81
    0x119002401400341543c0c5620918500100ca03282c2842141c41d8400028001e0101d080024900c1c1d14211004082003419045614031900030010b48404070f41d6500d0907580c8110003903d101180107056818409801c1a584182e031807401032500011441740c66020a2640d401044103440b1500e5440040211811400d209000c0303041200c030640c2804003208010302000200c60005201c00c2e1581a0602c40b0303190620034655583e0090102c80b1146d50241c800001d80c1d210b4003c800002d03107d4142c2400700c580404545000c0d0758030010007000141122121107213401c606a62404110741080800c601c0302486004d88041c2100d0006841d0207480c0400300261807520f40e2005040c07000c07420040f0042840414294202d030803d4804d850103a80d6440c2041c01c01c00001d074168501d402c0c3c00004503c1190001c044e510551150718100042c40e101c1d410150385039402c84078441100582802000080e10907048204400c8841c40080394a8501500140640d0115000f0000c4900c0200d402c01c195075040008640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46923844 1250 46922594 46922597
    0x70302040c021509070f0e0a0f022808040f0602070f0230011b0c0c030503120106030e0705030c060903030d061401090603020301140f01050c070f08011508030904050601090e09010c0807 81
    0x951801140c801b03c88080e2095420142d480f9001502d403007010b0f00503404c940d010880444d0384201100c0351403000d0030000182c0c1d00382900700300ca02401c075004051440c011500304000000341809035695001a5100b65811a50269840701d4540140c40e40d11080b58900207551f10318051402e10014000c07095000c852540e0581e0500104940f10604410f0004600318075203032802440d00c8900b82a01d1036101680010710f18403002070181403031010142c4190603600144d030305003c081c40d44885107545109600405034103811103810711581c0c5c5000001007880a40c0078060b42d0604944001c0241100d01943c000f808000c1c158115401660b03011810b00054036140c1421800d55040c00a2500060100908107005880030758940c10140e0082050303a049981e5601210840e9407034240c1c410030720001d44103e8200d5030030b10b0422480390315004d11100c1550b02003002035050082c00803c1102400014040754140505c40ca404200e4084c40e44100e0b20030300c1034100201d80c01031001c000400c29007000345043c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46925094 1250 46923844 46923853
    0xc08010f05040c0312110d09060905060c12090f0301050a05070305100621020d0516030c050a02030f16050a2009010501050306190801020d06180923070302040c021509 73
    0x400101240103403c00d5a400024440b41160401802d030b800c09140500c41045200300c01541c200690b1200c441c10944009984031301380c480c6d03201c0512410707009240344400613810669806c00c6620591024102d5030400400c040109102540402e08450003641c902c18240e07140c0003000055900b60103042e0304411440151080d640c5031400081070042c0000d5034440803e080e0500c50482c10543c1c054400070840410100f0403410b02d040b0414504145d01d40003c08242401c0c14007964501480a5a020f1500d0342c000c0e525040b0360005909156004d144c4611240e0b20400d00c0344003280d4200840e00d1510b1040301486645440c85003882070540740c103c03140e17200700c01c00d000501140e648002a260030010030b40750f03010410410061982241c2007030300301c00700541c4040745c2180184c034582c10100071541c1c01c20700c1c1d0911034080038407941034480e0607070302400003d09000940031152a928107001a86000010f940f5038588990005054400741c058050040c1d020f490403184420a1001d000e42101c80f00c4000d2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46926344 1250 46925094 46925101
    0x50913060305060f061e03031903091104050108030a0c0c080307240501180e011410030309080309010203160807020409080909160212090a0b030a0501031202060103150504110405040c08010f05 84
    0x1002c0906c0020703464401700d440f83c20240d49840c10815034540c0c582603005203250700c401c00001001420940c201f030759102c002c1603420a442c2814415103060f1603131000a94070745080001c0c141c07034808107090126841d9900303840000d1000b100340044c3c071001d4407a0841c15191480080c21300e81c110280c0e00050120740c80c0400410445072a00005440030100c00340100d45407005540040c010b010484c5010140219030341000010000b002100301030720311030b031140740f450360f111201260b50b0b01503c8030300c6000d60700c200400d0000100c030072a601601480340645629000e15540428242c8180441c2101c0c040804a43c0030340c0d520302440b0031640000801e003600d24014800740300941c1c40405d40207130790400c2c000281c02449900c1c0c401619003c4e0540000843d03407824132894490042c0403d10099480b401394039003e40a43d4404540d05040320f0300291401c2c0301040004500008001c0504110b0f070308104003815401c135403104e0081d030344194043e070840c1e00e200c0c1c60420300c14255440000200f051901c4c14080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46927594 1250 46926344 46926349
    0x6050c0601050409030c021005041505040e06120f070605030411010c0b04240501030b070306080a080a050a1707021e2d0a0206030a1a100c12050913060305060f06 71
    0x35a04441085801141c0300040741001d840312140940d010350003480000511201c0750f003100c01001141c034042d0403071483d0308210354120303a24020f600640e0540c11208000c2211886c05000140c107405100080d1591101d0742081c2500d0a44643d000718040760002c0b0801c4103000c0b46030000d141d00d400a0801d240d80b181c59540d2403000d20001400208036807202d50381106022074405401c1d00c10503c0041c200419610303802c10700300151301200c07000002410a00c01107981c4201152064889910101d030070f0800c100140c060b151070304200c2101703081094025035000c8584104010a004004c90707000303803d00d02800c841c42c080709041d088105503903500c030031082184542020301e0708080906460004a0840300d1003c503034201510f800e07002e5881880841800f1044030341e54050f805d0021241d8109019948210902070300800c03603020000860b40100d07200e00401e030088014466000c003460124508107d00300003c00170708000303160368052641c80d0400c3c130800c4001c204090b004548249903030681c0c40d06800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46928844 1250 46927594 46927603
    0xa030b010807080915070e030304030b01090e01060b04030f02010e150a030501091512050304050a030812150108060d061409010c08060307290f07060e0d0c0506010909080d060602030301050a06050c 86
    0x1545244011910002541b041c411102c915040c035000342130700c3da104e5490500c600f6040c000c2c010280d8a40c60258820709108051107084100c80d0000155800d05e0300c0d40e21a03036000c610444d030a0b07040c00b60b1014042120350701c0f5a48048010f40b1489240c2d10703804449030060468205800c20001c25180105001c0ba5004100a0300103c2d1158105800400b0040ca445402c500940e4043e81e0401d0700b42c40044100702c9004050001a030300e040790000d007551140d10342d6061603900d030100c034040b17900741000c0340c003d05001c1800c18046020f040702291261490f08080c55100d01160b1000712652f680d85054100369000942d0380c0c000340c0480042801ca030038045182c085d410300155204c8d2494080c0210418070514105582c41d00220440182d100c15a60a0910103440582002112402806c601c1100b55021f403540a503000d400a0041a0710303801c2180060040810302400d456030f05040c0000a1030154901403280a003596502440c0c0b20b525160038030032503a0250f0404410b010090206401d0102d0024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46930094 1250 46928844 46928863
    0xb0f030c100c14030c0d03020f0304150e06040308150102010605060d0c1b1109090d0801140f1c0506010b0a05070b071b06060e010504020405030703020f060f0a030b0108070809 77
    0x11000e1030511640e00e0141c400440521004043c03010381401d550b01e104010024081d0040030b0020380300000041348080381244136039440301908500138400300d03001c65403030b41c81558001801a8001010104001200e1402c1b0048800b1030024042e18104810300c0700c511041c5003080020300081c46804d0900380010040e001307104550320300d69910340b20307168020300c61220503100305a002e81c2032108594500344250b543c1048117401d070240c2c40040c04075100700d50004032080380d851550384001181c2d0901184c440d0196020440540c000e080b210385241580d60100c070b1140141908800459149080c9495810540140c2c0048521780382071240c614080d80004c200c41d00c2e65030002d003540b201e99a0240c00d440a96015035002c000ca0803071341d669070030404258030941c01cdc5c940328440b59540ea0790b1101000164801c5018060b0160004902000141040001190440001400c0c3c6092443d4801d040115800800321070000a0b1124103c1c0c0c1b65507006880e030340c0c019034686010341789803421072403040c2e5510001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46931344 1250 46930094 46930099
    0x106120915061e0302030c0f030102091203070b180607030b04020d0c080609010905130807020d080307020f07090513060203060f090405100f09020603071803050d0f180602061b040306021c0b0f030c 86
    0x60460350b2382d40e03038298111221640000c007050b90003011542c0302552508041d00858112041130003107040000c3c4103802c07009c0340075032100801141d9261304044000c0e02003001c1c0b59411503000e0220601004160080b0843c0b03100c141d4460b40c0300c0c030f80101040004941030f4400050345e854a014409910307a0b8000381c1c0403103a040320803182d451601d80302003280740c100c4440180c664a0080240310704244d010900e01c201c80200800c8880c55500c0d02000c2c021110306071038442c400c00c51512440700140c0315401455200000601070354040345043c01041e100c4208881c101c0e55a00060320b10000200584100980302c10380034020005008940e0201c0d0071844080d290703209004c101c14824010420f85140301015550003001d45101c0e0008500280c0000810481400070034817100040c4058900c401c3c0050440d00142c5c0104010b807644071f42c0c08800c4100c5034100b00014801c100110100d01e040c0003d040c140c800c5501000a8000300002e2b0b0101e5100801803442002000381d08005517a001610084084d002c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46932594 1250 46931344 46931359
    0x7020319111210050a0b01020f07050907121805010c020601090b180c07020409030801050a08030f0301030b130c031101080c07020a050f04140103060624080106120915061e0302030c 79
    0x3030403002403500c3d054090080c5140d062000b00302e130b41c0d0900d800c0400103840030780845d1800000b03d0841a01e80e90580036080e00050984009100d8070700c506004421740c48130404c0041d0ba640010720a0400c80761a4030b0079603490703446604001c070141d4100300c1c1c5401400784200400a504d500c00000f0003078001c2c00701324002d480c1d8030404138941c090314000312081c1c282d00174010041c490051401400407007003403180c0c92140c5040e2400242c1440088201c591032010f40d00158035580c00d51b9076510f800c52001d072105a0000d101068036000035200c14040d00a075004a0144038488003003030006103076850062420a40703883c01e205103401602d03180030b480140ca4045698800450000d00800c00074200c24001c80c000b200c042000005000250f40140c050f0755045512803427946450301407080300300141d40c000000480d4000100306441c0701e007450802c211543e41d004280c015550304c4403501301c21101a1540d4007070399400108181ca0701c056010a1494924604040842c615000240c940440e017145034000c086 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46933844 1250 46932594 46932619
    0x41208090607050d020d050f0a0c0903020102060a020a030902031e011503030e04111e030a110304050318060706061502010b040c0c1115070309031104050f04021c0b0a020702031911 79
    0x25985c050f5845100b0804040009180420450442c0301056074006001803600c000444036912480f0036074240c03078041c0c004091980321031501c0c1d002988010712103000c15603100290342c01690280148000d250303145841c000245840d80b6000d0844184040c0184c1c004c08003003081000a40114150041c0001128001290344280c0c078202c1162140da0900341c103649a00b01c140401c03485020142d40a401542402c1050b203e60781e020480c68803090710f015005a00501900802410340001c01c0b00d0700001900e45824a071559451000b51030942e041001c482c0d1083d5a2550801e82c24419036031482021101802802c2034418050000c42e120350f4040c2000042800369540e9885152510f82402448190b0303655400060500a00c0310500b80001c44001d030442c118400c44e071825011344d5002d8903c0240d510f60a454a50820204510b000c00754615803c40c08410004141d4500105108503000080541e540034a0f10405040c154044042c070031280380c00410070040b901004000150641c01e441050700c201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46935094 1250 46933844 46933867
    0x1709150c0307032406020f0d05040b070302010b03010207080403110f1509030708030712021005101502010b0a03050d090503070308181302030c04060e090609060418020904080304120809060705 84
    0x341c1d8003041d00c13035010902c549018181040140342161003560035603400c42c9801c80b807507445a00103024100020810700c0107110000a12001b00030a511a0000007402d00c0050301086c01c0e60403049054403030800110f810810702440940040ba100c104030f030040007a0102c0d50028100380e0810504150314500030440e031001d41c604100d4417000c3d1000303101300c0740c54215a145c05101c0f90f203002d90702001409803801c5650b14412500915024038410b81c00b08040500b032840c100c400e044036000301d80842d901d503a1304040988880c5105805140a50701401d94050406070161140f44543d01c114020b600c010420030215420109540f20f1004028001203686c094600044a0381400060301404c00d10010a1042c000d003007000500c11030340182c0728900549481d5040003040d00040344c1540d005654400000d0081c50951b00c02403d1010710b09131320308041640d80114200313a02c1110201c420b18000070500041c00900740780c0054554492a12540524051220036120400038208078140032000c2626a07002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46936344 1250 46935094 46935101
    0xa030206070f0201140a0504031403010312231303030801060e24071202010e0709020702010816110109060f1107050d050703021f050601031406030307030c0c0f061709150c030703 78
    0x21703074403865400918140002c3e600c0050409a4040f00070455038580388981442c010103581c100c0703403c0301043e109202030b0042039403000c414014440c0140072020f0700b800c440d10480d0291003403404500d070212080b82540b801418064043e04650148001102c040e1507983d122503270550000c40b0029240c0c1c0c3d880c82041000558010014020068a4502e1040c000958154070420100c8594421120043c1c1d40d00c1640049108451019000420490002e5034020300d1a031016100b464070700d0301060100350514602c2c2150461241103e00607106c2c0480f2001d200c2a001c0e035040011420001ca00d417095641c3d07115030302d410b50120082801400b08254060500030300492a500301c58401003000d100392090050020002150034602081c50a440f4039007012840ba165403250704040e00440c502041600c0c20b54001404002c11988920150400315240440351614401000d041d200c0026401000481c96111800103161b840e03694007024031071100740182400e42d82c12030719050741c0940da0b4071050400c9001c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46937594 1250 46936344 46936361
    0x9020c0c030d02160608061e0d0206180108010504050105060a0f0507050d0f110a03050a1d030102070503120108010203060604090b060705060907170316060b010504120b0105040605030a030206070f0201 88
    0x10b0082d80719410100380c0109102036210f44595254000316125401039400301425203521b80c11500c00c0c1e031040000c504481c02c44021000080c02407014181c581d002541360307400500100c5540c0c0c4000c0004000d540c110f010180982000c4809000340d60410300400c080e0b010341c0d03901000b080300c540c00d080b443d140998219407d03550803206503400f0140b600000f5140850180985000429203403141d513130210041a021400c44d0325030346943c60f000c1104001c458807450b5410050b04122595810800c503502480200342c03243c401c03405141c4590880313844405441741680040050303401081081081c2d0b544c2c804850a8036a01200000c5d12040725000c18118001c9100041c600d10440c03042c0000b0f480005041400ca031a1502025000d5802d09a07403a01d82c060500002d80418008965900003403094102c003001940c185080c82c00c050799030758a480a04000e810998400341c03420010320644c01d044c001d86019185c1903006140c2003405940082d50307040300401910403c0351148030045128403e400100f074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46938844 1250 46937594 46937599
    0x31103040f110a1805161b0b09030c06010305010b010216060903030f03020409050703060e06010c0b0c071b0905060406060306080615041b080907140306010902030403120501032102070f09020c0c 85
    0x350801d940d2180080009440804030000c105568030030880c880e43c4483c20810b0358444c1f5003c005050350321a556203402802c050805e0009000140302800f0400c02d05008500400001c620f802e003103400a400c00c2c880880c42c22030058102024003d01d500300c0072500444e645807030903060b41d001400e4210000d0140c0d0300109416400c280a016180c0c0d410b400c04400d94400c0f410300b040a80322a0015181c4a000040c01400d507003c03000003803940b4150360050702503107004030711924000b004101e4106980c0d600350480c200055455040c0080d80c141b92107400080e2406080400500741003600c59540c40300001c01d1143c1403480100509015101c1d508440d0f0141d0500e0a00030803240819006090310200300c0e1603204031b1003000e400040c22508460700f800c1c06000a8082c203130690030250b100010303610040054042c4506000000d00c040c029100f450700035400783d0032495800f05403a085c0b00486180f2420a421584400c40501c071504000c1d80c80c50490310441c400685d246c0000c482d650400e90600c0441d503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46940094 1250 46938844 46938869
    0x7020a03050a02090601032c120301060c03080106020601060914150301080d0816090312020f1e06090c210a080f0c060a0504030c030507020f13020a031103040f110a 72
    0xc00c105001524994180c0300311840049950344100442c01c480a1050b2592004034a080c540524030000b481c03c40310030000c40c1034401c9079003241c1b00707024154401c1c2e01900009904107114810316600c0b0032107e001d03060314070281545500d811002056903400340900c0380f46000b042e1400c4040e6480c680a0b03820f0201c0c822000e0340b65039540f43c815449452104081c0301050301c403030004031810038542200d0541e10795520b0b099200350031a01c3d8041d410499001803001d52003441c01510448134100007040c400b00380c4202d890888241480c0c1c20f07003481c0b0003600c0b100880d840380e00004120783c1c403088207215036184200342c0310038148814989454084c4400c4081c1ca88140021115a460007003c01451100d4900c411500030707880c2e25030210100c80d800c580141c00a1540c511080005c0d200d540100101ca00040904803056010030010744076526205001e038585500042904941c1d4040c02000c40102c071035004107080d4641520356041100c0b2100d001080c103522400403680319a0342c41c4410b405442843c800e407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46941344 1250 46940094 46940099
    0x9051305010f0b010e03010b0306011e0308030405032107081803040f15030c050c0d05070602040b03090109030807020a050c0405040c21060f02090f0409050304080a0f02040605030303100605090607020a 88
    0x72000700005543c3c940040e0f90310354080d049040500075056400e0001e0000e05280e860000103444501401102d1580100c000c180040851154800340d070049009001842d0303184000c07240c1114140c107000040d0b2080c00300d102040081a045000c959001d9010740e045840d1400c203c0425045100b190096250b0080020001c104800c2e140400e001090240e10100105d0030303e1101511a4050300316003081036840086420a618030501c0901441ca00c40c41000d410907840707103254030b09030300110b44000e0161f40d0740d29100c05040c1d0001791580c00042074006840001d41e685c5400751502c0c1590259800b80da11500880c00304000f60104034024403850100030f40856103410b41c5041d250110205403001c81c14984030b010b50428a00c01c40f844190000c00445001d80440140030107090900801e613a107020034400043e051401340803030b50402d80704200c8c02180280178410481100c810f604418000d43c828810040a452510400810740e01e41d03040c01c03a160500c01c000902d1610403020001e401c080c0c0f01000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46942450 1106 46941344 46941371
    0xc0d0e040204050d060f0510080309120a0b01060203071b050a050d0501091e05072418080304150201200f0a0306030204020408060702120309070905130501 68
    0x2500b440c0d52040011500c40352101c0c00e58406450309400f96401d002072162690200344414500562424440c100d80d0300d0080503072090180d80460085048070350704020981109900c900c103107080d0740e181d0b000251a500158011545c000d4581a010300341e8042e28015400c0d910050050340031145040b0800070301e2071580c00b0a0302d495603126449404038410141c00703101e00c0036140d160041400e0030304d00140351a18640c4101e5102c011750308018290100c01e00344048602c0f0a240115001403421000d845011555000c074107a88400036001a41111080580701c11503ca50002c01804401207a10b19007240d1450350311002403c2000380e9070340c0742d0b01c01001d440c41f00014940017a00c02d4036070707000c070302240d00a4112654503404102000081030303040192889100c6502405811800d005a01998680c00e134044c1d404060f8840000440051031014906401500300e0001d00a00400128 = true := by decide +kernel

theorem cover : BRFrame.Cov 46762594 46942450 := by
  have h0 := BRFrame.cov_init 46762594
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46762594 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46762594 ≤ n) (h2 : n < 46942450) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
