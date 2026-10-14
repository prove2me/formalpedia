-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2148
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:47:59.862559+00:00
-- url     : https://prove2.me/submissions/67a13a31-c64a-431f-8ee3-a2d71345b4bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 386151079 ≤ n < 386330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 386152329 1250 386151079 386151089
    0x90108100c0807020c09090c1201050a050106210b06131707060306270f090b01140604060e060304140106080c04060b040b070807060f022a07050109060c03020c10030b28 74
    0x18441b071341e0b11b0380385040c0342c10a0462150351001c08288420031010040d80810300414407072a0030300c1243c3c0c80d17039005d070380100d8084085076a8914081a2580c900317426401242070303020091100746400c0d0000c5890406111715001039041281d41c092002814408100303000042203141070911000f8a81407808070b800880b001e40380c201900140034004a5900b591001c0c40d00c18844504000f1140541071000c480c0e4024014400848403483d8003062900d41a010b5900f01d5009a075040c8035508020103021301904050412107030714040d43d008000c202030030f003d1070b006009482e0050984140c10303010401510f58990160b0380240741080b060208144000271940d826400150f0035684141c0d070b2070070130300070320722404104682c600c0822103103100030380321202024604080c6040b204501502c80d800e51240c0041c0310b4603003c101003240401415008202d2000028040d006072444c4d042d080c0045001e942d852541d50703000994801204589241019908018009404500c0300001440365843e158460500507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 386153579 1250 386152329 386152339
    0x3040c2904141507030c021516080f0c0a0b1e0915060d12020a0b012102010e0105040e0f07021e0a020d140307110a091a060d0b090108100c0807020c 65
    0x902e00e401c0d00c800e000300801410004143c0d50310000c1c0d04000f480a000307100203d1007018070305111119074513050182c034565280080a4102030f83e469486207000e40c8180305842004409000b020b210480500660380c1050052400c00c04902d080c00094400307801c2c0350120050003601206200c0520b20014004400b840b4160855202e61200130006040201c446801414022080d05260a182d8080703510310503180f2030010ac800c41e0341c8078021603106460082c0340400b03014907549078001540c400e20400030040c00c1070420920702501c0c2c0c0c2c031490465000311603d07000032101c0014031044907410403042c580c01c07090b042c0c4580b0041c0007204d400d44485510201901c12001c046050050100006401e0380d115047c0c0c0491f40e0300c40d024900441c0700140742cac00be144140f100c43c1d80003e4100300f40c028405543c6800300c0c2e01c00d010005508000d415081070810340d02084d80e40d17903e0076294880d144168007030706508000b00f05581080700c0c050150b91107259202c0c10400308406200b851900020f2001004000700c030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 386154829 1250 386153579 386153609
    0x91503050c0d111e09160806060f072010020c18011a030403140d05070e011103090d051603201c120e06040b040e060a061709100203040c2904 62
    0x3d00300e1803030000300c81e6540040782ca8107111444507102c1c04919594815150680141e41c0c05007006528000e0400681c102c480420585000840d00b10050cc40880200b4180c04c500c0144004a0705a0100311202c001603400301c8500360f05803500103810000c0f00c003054500300303066060500b100d155135161002411003d0000c4045810180110f001c602c42d5282d0103074241d11101c43c0b1300b4250207000103070380c1000403424100c030743e05a9501c01c25030003601e01030200044d450410064144410509803610680b102d00494141d030000e41d07a260400b070001d60007070180c801421402e00c04c48480700880c0202c144103664101a900c3c0e08400e0450791300c0c0b44d0fa004141d862126040b4603083c0c500c41c824140e042c1e840400080c0100f140c042e240003400c1a10f440c5c6510380c92654031b100900005101174020040402d6039103800c0c81e0081111280140c0c044100410303185201c0c904201d040c1681c00c1a01e044400a81d40d401c01d10003541266024940750203a000c0060302400646c503031903010f100d540600c490200c1d03848 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 386156079 1250 386154829 386154859
    0x6190b0708071a0711060c0301120302070302040903020105061c02010804230a21021b10020a05070f05040b18070e0a0e0f040c0e0c0a03090309091503050c0d11 70
    0x10707098950640c0c02c85000407006030091418010140f080342d089021032105040d00d1030044e80010b9481c418040390a209185074202112040250005002201140f14001c40400143c0350f9000d2258458071035000410305081071030400c40c902420701340d103415202d00c2104405c050703a032120303440f40c002d031304554007104105a840d4a107031801c56010742c12086e40300d101c03c50810000c002612140c8017640d000304100202d1206412a1a102d512070400c480b84140c00b1065214584030500280e07014107401110401c4929503175080c100002c42d4064580c03072f040101d08208504090040c2c0c150342030200d492504514907441079a1803190064940030401c02518444803480d15000900009804001e503c00c80c40e00d8800301a40380d061084908850300c0031341c12070006d6007944259015004911594074541092644c00e0200c0040c02500c0c400e030104411040c0020395910507108071000040b62181d140941c03130031403c0403881d04d03208500307281c0141d000c4c1e0a1000402d02600840040c00000c0314004060300600c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 386157329 1250 386156079 386156093
    0x13f03110d0c0201020f0106050915010207081207060c1b030e13110c0c0a030503041e05040f0212160e0f0d0605070f08070e0a3503070b06190b07 64
    0x408400c40107100d42400044040d8220709001d8903603200343d00b1500d1030680803a015003a600c140c402c860b0000c0c11800842d40340a04a942c4600104041c41200c0b44141d0303801541e460045d90708140f0b1000300c0c0c0015800f042c003030075001d009448074142c18000e01510116285412130b90710100090100030100707180c0300c40c40d540c004070801071106904c0c05000040e08489100c0c0076501540c401001841101c00b900010f0801013000411690031070080c42c14980b510040245284503a80440350009528401140c01d5480d0f10607843c14039403140300180c03540580b440350801d811024110010091a0300200000c950348549212040b01c000e864030346a540941010400ea900c1700c02d4020321650600f010014840d40c400040e031100c1501c1e6440060549540c1c03003c0e40d402c42c00f0070b54940c2010f00701c88140b10200740d404d182c0c04e102c1c5000180420072104403134031603401128807030005007036000066204140421144c5442d04a08219001480d00c06070b90000c05082105104d510b4480c0c0000c5221018031001e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 386158579 1250 386157329 386157347
    0x2070b0f06060a050a210203090d031803080f0c07021c0203010c090b030601050a03060e010b130902091f020c030a050105010807050f061b0a210801060f02070504050c090d0b013f03 79
    0x940c1b08203544030308140c0300c00c5464100d207003200720020380b411084401c240c0d0048109000d80d034158a0301c0800c0d8654000810f26035200400002c00c0300340811071000141ca841803c1e00c43c1980d0041842c04060881c0f04042c25251081801d008000040b20181b1003611990116500580c003401c11503600e486061042e4050115640314400c1401c04100000e40c003449500102403a0482082c60084540c8a1401008034000c0c0703151740743c10110b030390420244440c0c0f40c4c05070401c2241600481d00c06000103c0040c0c03070522483c5045031980d4640c0010403140d04200491000761030304540800b000340d483c00201c3c20501818100740081c02042c0b4484810035801d0003c0f262141d0040c0601c40c1a40000810400d0380c1c030016280800502d0071400020140e22828001a03403810b203a0250040302d02d031000704005004c02402a16541c0d2003003101030640e981c0d084070701c0b0f10988600740700a95503140140189010b041003142450f40ea40c00040d8041c05500d0540031000e000364001c0c55818a200c1c0e00302140c1c040c01d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 386159829 1250 386158579 386158637
    0x150907140c030304120f230f071b090b01021f06050307060201020a021209130b0105090d06090203010b010807091a09150c0601230d05010b0402070b0f06060a050a 71
    0x100000d110708070310802100075849540164003030a035640c08124203c41801e2640d903902e0000d242290503902c00d03444517681003009080304408034144000f440c82d8451550006404036000c4652070002d8070401c0010242100800e180803041060005010002c1d445030b6104006054054100c50065807080b03056024102411016040311951522040007038001d40c0104c42540162148502d512501f0180300c0454901c0c0d0f8020301754114117596058403201800001074154180002441078604075110000030b0f11041d0300894022900c5080b40c01070500b1a071003801c0c0c1604000300481001041600b101803542221205600c425010011242d555214050851200e42c403212601f5115000400040030b8000c05031503106984250b6a50a50b11429020742c00d080d59840074010380d4407141d46440c0c0e8000c040c0c1e900500c00421107022410004007281e00c0390000301e640c0c840311424409001c610207109507004e030090700d950380751010b01580a0002d0081c040000308000048920399083e074246141082110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 386161079 1250 386159829 386159867
    0x7031107080f0607022808070302010f020f09040e01090b040803041b0f03150933050103060618020304030206040b04051e010c0e030c0607020910080604050a021206150907 75
    0x440402c107060b4980e50240c918500504c900740ea16940302e01070240c030000a034041c0c201000b02c88626074a106441d04000000c0e815550385090340182c80c8214002482c41d000dd08854564501031201040f00f203d0302c003500107405038540700001c400144041019500f054005405903101c2d038891901e001c0900c1120034150030364841000c00a620107640710a80280c9118280d4501d41203401210003085035070a08003d0481c51060481420710404401c00c0110b0090108603c100c05c0a11260001512403c0c0d1080358140d5481e4010001001c2e82400c0340c000a190300d80640c80d501f400d0714000e544103c09031001e804003030124085030411004100ca00c10080d2141c00303417460441e80c812143c0c000c0c94134002450200c1d49541000c682ea02d000310b0b03000f0340c2c818001c104509011194003400700c80c103002000c0445945a4650202d0410000c1003c6445288540c000b844100418030500904600c2c030402481240d00c10000d2185a071031110044c5250328080e2000c280301e55411900703c170713050017400780d041c110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 386162329 1250 386161079 386161093
    0x50402030703060f0f051e010b0f1312170a050d0b0d02090406062d14061605010e0705040212040303051f0806010312050a0203030f07090b0d0b090108030c030703110708 74
    0xd44550300b007031305c01c910900f508000540e0b0300103051100b440c0c4100981700c02d144134001809181101405414401140401c107030034484104180000e0b9103442d00001e541d000080c0c00c00301004002d40e04e6911111820801c14108030010901818500580e41c82042d020340340c4403078441c00c0d01c81c90010002035800411080e064109414004000d204138061454041c080d500400c0c4401d015100109440311a10002d0324001d00d004114002c94000380c10041d405002000350310340214501c5601c128550288000003130900c0e041c19070a1400f00701d0f07070081e07008034010300102d43d051411181c1550f2080d010308000c01c0d180d440002030310325100c2001c03010580305004800424034010028655058a02c40e202d00141014803400a8400e401703035a000c5030043c1d100301700007484034140c824a550041380300e0130802440350f215000000140c001c042107560081c5d40340821803213443d088007814010581d401c0079600d000440241079480348600300c005424001e0360350b203114908004010620040070f040c4103448370 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 386163579 1250 386162329 386162351
    0x50a021c05030405060601091a07060b0d1b0e04030e1207030b010b0d0518030403140f060408030a0f09030206010b07030905090c031602300d0c0504091103010308090405040203070306 80
    0x9603030010f480a5442c4d202d06030010301203500900300e60703080c0d4a04030030710414000311700300c40c1290b640002c1c0300b200c2803501ca0540d0800c5868103101c10301c1140c410f103400d00c0c0d000300d81c513560000c050655100c110a211284280710119400c0304402130700351810f40c0e03031100303003110b041a2501e4117556030b00060007210310500000d141160f6901410460303503111420f0100d03032648040c0b00c0785007074411095100d642081008000140e4004030701040300e60040c0a45210410322a081c504002044600782c07100480042000801e00481c403600c1d80c1081605c400300005049601c000350342c0d03441401180b9420304005546014580501502001400300904001d002c0c54031940303c01c050b07002502e070040100c8200c00c404d1141030011800d00e40c1442c1100c5905d1810b85040096001d42803480c0b0900300d4003004003e9406030000c54024a100b81d0700c01d80340c09a840745080c900408070380035040c2c081804076080c00140000b4043d48100e941c81d00c411113020030262540c2c000241000003d43c402440c1034035101101709 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 386164829 1250 386163579 386163587
    0xf0b100914040501030812091c051902030a09180207020d05010605180c070b04061d01090c050d0b0112020109080706020a021f05030406090c0909050a050d03020f0a050a021c 76
    0x1041d1200802954410040c0a0900040e82c000313000003480000280100c000403a241c501c0c2644c04020101100c1844d00702e0a40303c01043e0703c203580300c8002100040c0b00c0701882002c0c1e08040c4118039074030095152440c0307900000c2c0b1494413070081c9650400307145102d020350001c980603200798640007407440805c200c451074030034000c0525119080c065460041f0001d4403008280c070641c03007007240284484c9003040c66036400300c000c2c070b009004507031582d0b840260118a0038010300300581c4104000000030550711300d00b0050f05031503c07944410b01c030b07040c500050340c0000c036980e4400341100e16242c00940c03c0301d41c2d0710048e1440d08164108214920643c240007680d42e070300084230341e0b006000b512070b0300d0360f40194060700200c80c0c44a090b2802041040000c01e0002d142580031a46c100d00440c1e03d901d4894031240c4140036141d014800ba1400d0b0b000c6950b801c00d001080c400881c020b080c6080c2180380c0510b614140710725015118428042c010041950341d011402030050300b8070910440e00300100f900384408054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 386166079 1250 386164829 386164847
    0x7032406170c0403020105070605090a150b18270c091f150c03120906020a090608150a170102071b03110909060a0902040e03180306280f0b10 62
    0x407001c44401e0104032a034034100121416242c043e034403203150100301d07180ca42c080c0c034001d04103c00a1050304135260218030880b101e8510500d550801065003261802005000c241864110310310049402c18000700b61520011460943c100c000742015000804010f0340c105401030650340d070042190410819100708100c4088080d4070840070561541e501d5000e01c49000c16914200381c040b82d800790303041e0007003400b6403145840503008103000304000426981d40d00a9822800c800c030b020034a0700e5414005a904852103907880212100b8000500003aa0009410707141c0d64440d100c00c0803e01700e08040420000c1d011035140c20340250342a003400000e10760304c50030702c180303813100b600c900c1000c28800700d640c6400825140640003100041240341c1b20072140c580200114001203910698030691010750000c144050114003ca03811214900403c032010716050501c0100100a1802c0407440440541c1d01030300204240c2c24003180c00a504912151044010451007a00d80e5002001000c44003c05510802107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 386167329 1250 386166079 386166107
    0x1181d0f0d181a0c0d090501090614070b06030307050109050c0906060a020c1201022205010305130503030f06010c06051618050102071401050f070b041205040501020607032406 77
    0x1908030310003284040301c20407118512081240c1c03402c1410403040d5111100c03684540c811141c41e03850714041640c0030746422211000345c4041460a41c00f0086581c000030000028000c0e42840007c3c500507280e503074154852000d000b4440f05400c0c022520b591401c1050721281940080200300026090415603078564000290500c503007460780c00109182450340c01c5e00e00031015600200451082941006640d103910710314004559400e10000313040c0c5040c0a1048600d0301c00202480c3c0ca581007400040c1074500042c03842c0c02240d002240d400001d5000000c980c2c0c030103004030100c031131600c40200481d58100c1c100e101130100c50426050001903140380e000c01360054051740f11080000c011490010701240c507807180d03e0161308129010090a1050f01940156000514049140220a104804154010100c2a142101e0b0308081004001318440005440c50b094103241e81004c0c50030000035918003005201d1410561605124501243c0c218400100da004808800c5c822584802d4005d06000140080f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 386168579 1250 386167329 386167333
    0xc070f05071401030c0c030e032401140f0102030d050a020d020c0d03050f070c0b0604021e031024050c0109050d0c051c020703082809030201080604050f01181d0f 71
    0x7070b10955600a10401d05404125120081070311000d84060703625184221550350140a0060140301a036603141ca1200e01864902160f070a0b941481c0c1c1070940c0709140c1c401c46001e640e201001c4881d50380c0010690f41080e015403004100c5584003900c80c4064014081425581400450f40000c1d40c9400f042d001405113003076504000c0c569078052440071860044d0b8040d030100ea030500301000840c40b02440d855002c0000b41c0007600c3c168020281002c2c10030b000200608404003c4180802c814481040900829011117008420342c480d200e40070200d50b41041c0f01040c00f0000644012101003900058842c9800c10291918181288005000120b40c50310403111805241c2c140d0040c561115030404400300183c2c01010340905590350110079600050300810640460300034481000c0040c845a034047c030390f079614400d40d64a50710024011000141031144901e041604000f180d04a007200300f4111070a401800c45d400b00d030840030000825000091030002d044040b02d01000e0300001603e11010a02141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 386169829 1250 386168579 386168609
    0x30105030d140409020c01021303050f16030503090d050a060f1d060906041b0e0702070614091f2105040c1a0703030b0a15030e071e0e0c070f0507 64
    0x100031141101c8009005807406003d00050103807907665405012110300d180001450942500301b2280108019881196554025460b44007040c1060004070700754003c080789500c0d9181160369a645034040c0000d5503000703241a803000d000303202c1d042041e40b0403183c01402c2002034035000180704000d00200f0070024100c140360303582c1410003c400105a40700b1501000900f1907904c6a990b10101c5078900800b180c02101744103004203056200509040c042e120540080603c5490907001030840c000e22161030000e03803000c7c409000d01d034a885540060803640c0c00340c404c94480303442d0707000c1d41c2001d4001020b02281c030029040240c46003466010354082e900030504040c0d01c0d50341d10031b40003480500c09092240098144032442c00280a6001140d80650040c2960001501c80c4950011b0450f41040440041c0d1a00301030070b880042841824058020f690640c03800780c0514407043e858041034450008441210310006104041d40f0040c1c401d2650b210041c01e05040480c2807590340c42d032881c090301c1400e1344000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 386171079 1250 386169829 386169853
    0xc0e040303050702121c1109060c0304030203010513020f0f01020715090f080604030c110f06070f0204150503030f0c0c030a140601121a0702070302040c110613021807030b040603060203010503 84
    0x8068030f03a12801c42500c20030100c601000c046c05801412820302c00e001040c4811710702035440c18040d22100a010009544461450042500799039024140c040440d40700503044c405078a4610f0582e0110405507200d16075008680d0040b450151154840710315090b400c0c440d07080250703021494408440000102030141900c680f125a00c88105440003000300d101c102010b40000c140051010b040e01009000c0a08681c4030380c081501688030103001c841110080c0b06841c1107150500c1120130410300c0380c10241c2c0207414100403aa491158540d8001004070100d10403080030000c118250b0412405000c1d0f9541e0040c6107415a400310b0360907006800380c02110b001091500c1c5204d200c4207465000381c01042d030394101c00310300f903181000503244a0850164460120140e2210300034140c9403081035a0780d2038410f0354012414144540507207000504607504c4084030260791900140140100e15540015240c0c07111402a4001c1c1008024280c0007401e00d01c0c000180845503000e141203860a81c00c3d86c200c00655 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 386172329 1250 386171079 386171113
    0x15021203011d0a0509150a021201030308010920090f0310091101021b0d020402070204140f0109060b04051003180f120e030619050c040302061306030b22090c0e040303050702 76
    0x1241c105c1400e50282c0176881901c40e082400d56041801014014900040c0c169030541c03900b401d820a0300491008401004103017402e00c070303618095040728400380d102d1150002181d12440b0704424540f00c1d560700c00b20700301c541d41c2c00d00010325039807020241007080b680c0713303c0e0201000c8500c1d000503000d4000c0e1500030303114a540600c4600b03102001840130b856818103a08000094100d06c13026600319984185010a644200002900481200d031501845c0e40c505624230040d02c0d00c580000e00f8182041c082003000c2d4a44941c4181202180d05003c640c80011901f450b84000f2010005404041c002101c4c2040c4480c600503010080410341c0c540d4180341044003810303a00c000075100401000106440c111504002d0380c004c907000406050203030720b099542e03000a0202d402003640e12040881e402c02c1085459010f2203000b800000070358408410620003013a605544031015600090f09450b0040c2c038040165001c4210090290b00c0314001250410f8100280144411501c11000d4071418900c0e4081d5815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 386173579 1250 386172329 386172331
    0xd09060b0a0f0e07030f0f09020418020306180c030604030f02060f040803040b0c0c010f0f0b010f0518040f051e010605030112110f0d0f060507081015021203011d0a05 73
    0x52505452041e850300f0000c02c03083c2001030803401059510101603400c1d84460007020f83c07406103010003003141c080a004110494005d01c4103946268185041d01740161004580190301c01c0d40d0040255901113210105400d1a100d043d445e1307894003a0030104010560803000508100b030081e422a5900d41d01c1c030348209808003003078502521302c09040c0002000105448002944071a030b0790107640c1050001c40610b400e40702c8100d00d4650301038403141d400a03820302903c1139000f00c04091800140084c42e600c0701403c3c0f4480d00e944070501519403004079101d0b8032141c0008603001940f140400051924591400c000d840703100b203200d901c11f071502c00020000d2143d800d4a05a903a03002582034000e200b5955441c8981c0c074028029003001c031130080200741d9607031883c0b08007149008941c141880c0701145442801c48000800500510007910b0034806110303d45d01c031210544002c980c0d800000031054a060303182105803881c12040c1c0600100214003200780c01003404000300d003010a0300040d2201801d10050f500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 386174829 1250 386173579 386173589
    0x31209060f010b18030105070905090a2d060302190e07030e03030a0b0a08031222150b0d0b1914041104051008010203070503060a1e03081b01020d09060b0a 68
    0x807410040c070a849620000b441030350308407403000400100f030001080c203503a0300310f0350640840c00e41e410400003420103c01040d03000019200801c000d00d240035103449020380f030660308592302d09601c1040004179402c0d8011009181c0051a17020510030700c0403a0b117407644090040c460740341c0745039021406c603500a02401c50501410006141980e440c6007a0400901380441c0701e5902c010084000076200f44103000034101c0401e074100c00e04107858414500e1064000c8207048040140d0301c0c1120b0004125012070301540990801b0006c0340002c240c00008000c7c80040501030401400e042c10b010348194003a41c82e40d0190040d400c1480000e034034007d8020342c0c21040302e0180c106020704c0b00d5003520349441d901c401d83c041c00c4400042e030010b4841d10303c0b0742240c0003107031000041a8008180010b518217842603000a08400341020040c00031402e04001203520351000404000303000c1520906a000784c1e2103d0300c1686070000864036a40810380440c06051098810350300e5900d01039060445007810f007071480c241c40d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 386176079 1250 386174829 386174851
    0x10060e010e090612100e01151a040b030a0e06191824060b070b0901110906180f03010e100605010c0b040b070c020604030f020307080706270801060803120906 69
    0x50f40300c3c0b06100c1d221120509560b0640074021040c1c00d207040c107200d034030030110f4007100016070605413a0b000304494a198125040e201d02e00c20800301c0ca041c3d0700c400c5505903280c0c0040035403203807901c5d0040d00c040c18043c0d04003603007801100d0030409040b4500c00510340c4515107000c01d0203401d004030294001082c42031400b13411092201c3c1002010501c00300e550000034070f250030000c0c0c0940d0766480708400d40c21061301110310200c0e000074000c0900003402100c020350326480225291400100004001c0d2240c0601810004045001c110301503407582594800410050300134070800301d07412012501c3d04031040310920358501c3c00310040b40ca548124401155250321121b2404103031200e48940d9400300008001004100f41c02d00f440005848501c0600015885607030412508000340c41058185400c40d040385805610401d01044010342c41076581caa64010f2058500d802110010003902010075070300183d82c1907092102c00215510000000e03c0074007040355004c0307030710745500150766218201903036002425 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 386177329 1250 386176079 386176081
    0x8060621121305061b06100513050403090b03010f03032d080408070204090b01031103010e030306010f050903030301032103060302030a0204020a032406030c050316110304030b10060e010e09 83
    0x25140c140100b425011828961400c03683d240c0009040b60b004400c508045441810320b10ba0b040020000b55421a00039601802c0c0c85051801040450104460500240b5203c070081801e050103210303154050300c10740c0b11035a44c0350303140c040e000306810f4988002c1f00050134520035020320808821071085402014800144588006142103c200c0d00151040d01c034404100705c6134005a4031072042659261003100c045132a5031445c1015511030b07401507811400783e410401c0809442c500401101d80c0617200b420b0605040707485000c202c58a01401c0300302034141c0300010000c0148070310b9600c0d038125200d9042c210b20412411540032820360304548402901a07000c0040d50005250a4016100c43c424500d40000c454640c1200300360415a17600e20389403000f04c000303c144850f80e0300d4000c030007030b91142d810718074950305091003204d610b9420640307101c0821a4101100c00040000e10840b4015a0403425100c00c3e4100b0400e80420190544100e0000c5548223071014001d50066a029914100040400c002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 386178579 1250 386177329 386177353
    0x161406070819111b0906220903200d081602030409090b01050f10140d0902040f0c090f03020d12031b091e030302060f0c0d0e2401030b011512050108060621 68
    0x814000c00d00c900b4a01a80541a0b69250341c0c074450b816003a400f2b6510b44079001e400621a407801e620f94500300881c1d41000a0b01c0f0682c5401c8040300ea04a074030500790402c3d81e9141901241503008580010b1840c84c20580000b040c090031301c007000e040e140d003140c403103954540100400c00e9081c2d00003046400b1690104c2d0070300250071060054074548440c05008030350b6104d05e03400a022a17400c0280b84490340e03600c00500c84007680c02414240946986480d07020150b0941d00010f10943d844540113089843da0324503001c401e4847c1d084207a10b054100d5080c034500401d850b0250800c0024002c2326a007904c481c084000c2540342030750140890f9090740250070380d61185040403081403001414002d40403001c124102007855a40314214010b140c22024003548062074003507000031060740c030700301da50703140ba460050003c502195615411103c50710f88815004034442007e40d00300402112400d145031a20b400060600b0380800e019100b56421260b0101880600031128103008149000f01000d60010b615110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 386179829 1250 386178579 386178589
    0x1806020d1704240e0606060310030206070f1e0b060301110412050703050f010f0605190605130e010303050d0c03061511030f0406020f161406070819111b0906 69
    0x24000e4065481a000f405424203407418a11032102c0060a0340d84e984022542e580c400c0c08001d420030012610340e490341c1010f200289205445001c043d11601c0e00140d9242003000d41140e00b50610790001e1551080880305656503103c40c00684180e5058160b5070000742140b8043c425080c4c9034042480607402c00f0f0070503401203901d0200c500203d5681c40b8038000072000c034000b04280010003c0c072400205001c42c0180f42c140541e0066444076000b00325103085003074048a402d280c20141e07a1149025900ca00654a08202a580c20303401a40c916010718000720525034000010000200c1e259070501075004803000c203c003180c7c070a224001d40690240e801c0b400e014442c4034160300040c80d101c100e0381440b05040c3c0a4044e0307881684404003590004100c107010310300a0000c000340e1258070084004452501014070b004500310b90010f031198a0001f0720f4010420140c080e51a40e044540c0d0010010300e804202070440581200310b4000742c86071030005507180c421450103501462018012a480352140b0060007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 386181079 1250 386179829 386179831
    0x17040e0103080903010902040e01020c0714030a03080702120d02090f010c0c031104020904052a1903020f0c010507020607110118060203060301090b3606070e030c040c1806020d17 78
    0x1a6040d52510521409650f2394080c4c40300900e1003400040c2d4030680d41d0003051500c10300358481a801c50411400ea85d0640d8007007210100c654050400f82001c0e80c40407801c0b414510588910100c0050120b034080381ca0406601402c1c8521007564525414070a010054500031000345004100f0304000409100103108500d540d180c0c440007401c050f040004a00014094a8080b01c21482c0a9080d51100300f1503452181003810701040340c2c15261810888074110081940400480400c0c52b03000180241e4240d810012200130414101c002c00c80c5090580d0f00030740b81c2406a52802c0003901481c4000f030f0040c0103200740180d50306a000c15580b180c005959050294000604082d4955610613400d00800c410603015480742024084c140364000030000d2614100ba913604400d8a25804049103000321600082c840740c100c0014101001061032000000c2d1a1000b001000c13a042420003112400850b000502c03803515600c5104101c2406440d21400c981d101c020140c03880010b2f10800c8a01e004034081000f007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 386182329 1250 386181079 386181097
    0x20d05031314010b1309020307090c09140a030c1d0a020a05040509061306080a140106060c031209140102040302150a0509210d0503150108061018050a1217040e010308 73
    0x404c0805a80d000255022201113140a146403121640403c51070140040b6028018a5a00b0041c1100100f4010060241c6000f414401c81c00d40c180854142d0307800504400440c0e1141d00d1640300d503202c0381d0380c51071800300540d80c1002c405501e0220723501e50700b2030003503400b510241d5070360b142498909810440390050142026400402410902c5d00100250098030701501280300100710f240e15903e44403402e141c565030181c0a69141103c00c1c46a580d005429102440c1c00d8600b07400d05080320070355080100f43c0020003d019070200303181e6440e00f00d810740242c01224022100b041d41c10821f01d01d00c60262003020308450008404002c000c80030b00d050440d00c5a42d00e0214480210020704aa40c649040f41c100240c00c0490404410403100c00e442c81110304401c0f6003860210410304020000c91000c611019907502440b404100804200b06449440002481e0044c0401c044c6544c9060002c01602c610000b52060070f44c40001c1c41c9103c0f95102180e0407200c440410505580c40d50700c031400260490f040e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 386183579 1250 386182329 386182331
    0x19032a050a110f0307050d0e0a0311040e01090501050621060a020708040b0f1c1415120a121707050406030b0609090f0105040c02010b011d0a05091303020d0503131401 73
    0x24410b4040c1c801c2015085040040c0c0c0116510092404d0040c5048120408a800c0040c00203e0300040d841c0d100c0c181080303a6000c0e0440707000080d010005805020081c022040642c80d0405c0300c0d0500c00150801c078040d880a0302c80247c030001240381444c00004002c00042c1c141e20001c0031a107817000c95401842418042e0405030b08203521822001d10a92207501659001c8502242107404640c040700a0142ea8003044820040d200d20401d80c1c1803c218001e041c000c0c405051107640c0c45641703501c00c1d11002c009915090b16444c2100b490034400c01c1c100052108006850084110122408840c801c1c0c040c2009407107443c02c092600c9030460140091300c00060f0458410700108203603803200e4ad1941c2c0540188015600c5943c103000074001101c071a03294000071681000125038459812458018109124086c400210035101000c152030700c92503402107400c41103c01c01c2100151206450303400403480795081d200f0340a082181201c99000c141c40789040c408100f641c1000003008880c2c0a0000310031040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 386184829 1250 386183579 386183597
    0x2d150105090a0b0d05070f1e050427050903030601140a02120a020a050d02060709030609080405060408060a0605031209061308060c071401020a050f0705010e0319032a050a 75
    0x2003082989190301c1048001400b181ca0181800c0354017811b03500860514111b0141140d402000304003003003004960006042da00000d0501c81d101c0c004443c09400d01070700700301d072010392052071524811820345018240c1c0d00e4280482c50003400801201d000d40030503510300501d0364075181c1d500c44e03c1d802600c80070150710806121219488000b0007803c42100c00e90084c19025005c0e060a41c103002524104201f1508882c0c09c101003547c1241ca41303030030b0700d0f044580019941c440b460304000c64440d0b030300710944c0700001060004404074002401885009942d600b882000c2d503810601d507440544654000303d01c80c1c05d0004403d54245207015244070910a010003901665409032103007811400d031100300a164000039480d060154642e00c144424800c00001c528240c081800203245026554030340030400400120300d410302c1402d401c10303118034452006480d52800c3c8001011164601110700b03001090401c011300446074240c43c0403a2641e607400b1020490b002900f0012102036101d580d0841c20700c40503035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 386186079 1250 386184829 386184847
    0x120f0904050a090227010b0a020312131704050f010c060f060f050a08060f0714070b011d0a02031603051b0d0507200c040527062d150105 60
    0x1004980c00b0303669180000680c1c0d421030040c0545201c01040075028242d111180394804410441e680c0c1c1100d164840c0c540c0c50751000c1900328114480e104441148515103818041040140c01c682d5507410304c10103e8440400420901200e1409184585503002c0300303201014459502850002105512400000805245168030703c82110300940144440da0f9611809024509019501740e028005400080c40107242680880f0a24000101400e041181d80c0d041003a400e0701d003100740c0d420541c0c007801c490515a12140071509410003140801042d410000c0854420b0b40c683c800c481c068041040078503e03036054072400340c014282c0a00246045110f003850940c4030040e40c0060301d4501c00002000c1028200024020032480d41c000905e001d5003e004081c1c280300b0400280c1260909050b0380c0030401e41d07103144c3e0300c059809014042d4801040d1107040b50b40c50369070214901e84100300d54403401541043c5060551030101d40103202d20015a540700108980404040b524101e0443c1490201d1a009141d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 386187329 1250 386186079 386186081
    0x5030610031e0f0b04091e0c08060a0e071205030a1d120322080d11070f060c03030c03110f03040602040b0c0a0b1b04090e101a09060d0203120f0904 65
    0x1d62500340b142c0e070303425041000ba081d030003040e8401d24101c0d01130140c802d007601c0e0746442e110030130a00720004420040c040c08002d40341d1000c1c4014030b0884251802403410824820244c00c940c0c40046c16400780d008040782c14213142c0c04403100c02d50040004c50070107a01040c280e800c0d0360000104000c0e20090034640e0000c6d40e46003c43c09040040d8070246840b03d1034000042e010795035003010141d61001d604014060b40000062a102100907881c1a404903228240107500f88031098120b00d0000308136801c00709210390807030b50069240e1311035078081001c0d80c0c0328a000c8080b1b80065029052120003040f0903c5400591405960000e000702070041c506580e422400c0c400349d000400d4507809802c03401c1d1004c140498405100c1d40202c559140801c032810014100507540726a00550a05643e00d510100e5400700800901301050007800c2c0820034078001464402d8a48e5124903064402d40090000801e18200740020080c016800760007081201c007024500d04041c0c001031000424414148002c210340c1d911 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 386188579 1250 386187329 386187371
    0x307030609050c280c0b1302090411031510050d0203010209090406060807080601050f012703061508012003041514071d0906011b06050c031f03030503061003 69
    0x510040300b40e94020104030102d4125502d500d00d8641c500050007004c4181d000403190720f5203540a14a4416a520101c070021295941c0c040690418034103020003080280064038a10401c100324111420b480044200b000c0070f02e02280d501c50b140403d270500300306c2c0d41048042c030000144002c0000d0700300942c5a02040f920703c01164281d80f00b030340300c1904110240042c410500a007060101525440d8144004501041151401241000159105a441c2c42980303e80ba114110300356a2500580d652030030000050460121a40f160300c0507010005003c1105128000c1030180c0106c5807129041d0f100915801c5410091040e140d06200c0e1694007a840c0841c410402c6c00c1c08401e40a040c5800c25060042481c055101d010b4141c0f121020103078410395075542c640760300c0761007441e1000760407114078400501241e401c10700400407820a0248402600d00b071025502c40c9800c3d240c050812040c1054035200011148406801b2480c02c00110f030881c10030304281b00f03500306a420302081c030030303441000d2842d8808 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 386189829 1250 386188579 386188591
    0x16080c01090501050c0712020708030a0518040c020a12020f060a09050f0607032301060804230a08030108011401151413060807031a06120a0906151401020a0b0c030703060905 76
    0x6d08442048684140913000c098944002d000c524180822542c4d00c0c4100d1280009000000c6155040541084d804201c0d50b400a001440703800b0f4048000b943d600341800c421607002015158281c01c041c400a010202c2461000003001d01c3e441d0041d6907001003003400b100b660240070303030381a4102101c82089900e00903d050b81e00081c0d6560890701b040c8820500d114500389801c210f80c01000441e60210340541c01503000300b003242e0390b0410f480000070303022820107a4948a00407129035009014950002e0750489000000030702030340c1c000e41c02400052009005426018544802d0103000501c40d80d00381451f5803400300018548007125818004002460b8406000601e24100b089043e80d8540990641c001200d0442d2107071221040000d0f54900900360000d50b00c1102d40e00103840800681c10180500c1d0300400c04019400006441e04810682805102071209080b01d840d51107500c00038522036020b800803040c031503e40781c03c01101440da0018180f1000c154460710041680300c240d1255500540c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 386191079 1250 386189829 386189851
    0x203011508060705030c030403050c07050a12140705150c0f070905090c090921040e0a06030b070206100e04020d171801030605090714040e0106120f0216080c0109050105 74
    0x3032401c454140742400040071207007040802c0c410b024011141c035007500c2d0055414200203855100c09c107012440d10a40780e11103944022407680c001110841021590b0069001e9071030646182021428980c1d940c00034442d80b500a01c1c1d604007203401c07800440182040304c005505850a048040803002d141644075000f501040c2c0d5140144160310004006c005c8803c8003d031502d1140d450030400d0252203001d255281107002800c1515055110f0103602110050000201e5800076828010a40301c006c12035400301301e4400c58840c0101c0c0c17000d400010109d101300041117080400c0d60410404040003079001d00100e800035030b80511000001c0705003d14124440c40990440c0e250b0400e01d130710500d0742e8146031601d41450310b0103409024175120b0340e080c2d0342e2001c2e03a03003884810b40440b0066035000b841140d106120482000c000810348c15032180200b10700b45400d50341405010155807824080344124242c3d9081010380e00d15131000201e00030003420043c0d290134000034001115407651800e55400b1a60700c2d200c1c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 386192329 1250 386191079 386191121
    0x304050114070e13110d020705070f050904080405040b04060e040b061905060f03070c081b0d05030c2a0a03020c10021515060f040e060f10200307020301 67
    0x29a040e0140705034064201e140c10380d50724400001150101c00d04400c2d408415440703513400c15a00512804540f0282c0460208554900c03031420701c1507c90f807050040c0280c16882e030400080d10702d80450914000d0b0780060030b691030b052610041000405003040541c0d0001d44940001a1030080464102e00c02c5010301c0c00c0110301c1c07070302d5401c1052a07042c1d2020711504580682c0c09000c02c0d280c074000e4890741e120341078900c2d6503510703041030540d0001c8940078024100c1400113514100c080010b08010143c0c80d2201c2201c0c58548000e900303841a0208403a004815031050040d01c40f588403e000000600240b0054a058080c9040170320b800c090041000b034025900c41c400c020014141014881c509065500c0a012002207904448040301700107824200000d2034540038070819a6600210740040421001740c50b030790b0760b42d000c0081100c01304841c000d205503100d094603055428140b10004086c0819902c220840ca0980d82e9a070403011524102c00480c170090280c072005031070034031030110004d0b112041c0c000c1c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 386193579 1250 386192329 386192351
    0xa0207052e0b091303034101050901031113060b040b0a020601120b0402010c05121803100606050904021c061d0901021303022101150914040f060509100203040501 71
    0x2a240002642c07030180c40c0c0c003010070500c1c080c000d074492281503040c600840e0b4102c0c0c0820079216884000140c00c0801400502510010b6075080450054038147d916410240c1c1c0e20310800000340002d210207408586d0018020100380703040c5240c03d186e01d054034000a4529210a00c070b00311a04150800e04040c540040c0c00c161440c1c04202c02401840060403060440710580c0d999140c109014100a040c40003c1c071901c810420144100d5945080001000b511100c10f513002f010541c407162003841c028010024030803404500ba00070364080d12280d8a4252902c800d50f818003009500c038140000041c2c41010500c0204c46880c01000c005080b1030a030050501c10041c1480c402c00030160180700503a204004c0c060741c18010007490021282c04507105c80c2c1540401460001c03400064007041002e51801a1170308032288801e4185007a215081410000440401c0c1c0711000306106030b03400f428440800310414000354864001c150311105c40c0d0300343c86c150000c03c40042c040e07810943d02210603075110070001c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 386194829 1250 386193579 386193581
    0x601090f0b09042105040b0f030105010912020306150616080415090f0302041814150c0c0303011406090d030206060f0a0312030b010e1c1203060501080a0207052e 71
    0x2000401201c240b503003070510703a8481100c0c2c01a1912800d400c0d8000352442c1c0f0b018014000e0b034004048020425a544100d03001c030210715882405800e01040d8102c40c0403803500541e07101090071a50190040819407a4120004000c46014200560100b800c010170413401c0c45203948401030030301c6031960315102e50402011481c0c07a268600f5035001c0100387c040c01c20025406000b00702c11030b40c068034002401c4440c0d07212822000c40440001c2c041910760912000d40c4040001e4045036107400b00080f811036200c06910354014401c0d8022560582e10600061114081030046600503200061a16141010b1500030500d03513410240c00340c015802c0001084011f00f032021113000940002c5880031003241c00d59603504031465403070388040700b015a00c411980840e40030340021507030080024010000c00d145140f82d0300d0308140b402030464000c045c01c0e46009542c4c1c02806003009550050b16400f40542e108599000290003000043d180e0f8803410326200704030008641c8400b907085a0500003003441c811802480 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 386196079 1250 386194829 386194841
    0xa03030507060c0e13020c01020405061204140d020309040b0d060903020610050f0114070312020c030c160302031c12021b1516050c01061d0f0907031a180601090f 71
    0x4c0c001c1d6100c8410036a9695494400c0c441d034401c81c0146c650814041e4030307009008a0b00030a400440020301d0004420940340d42c0e40c801ca200300180300e89034024542c1203841e440308400d88000341e8401c0c0213803400c1d46446e070414440305102800c950030a280c50388504041e1461480705401580009041c0004001000700100c040e0006480c04c0e2140780304030000030600d21001030161000440451442d08040c856440c203500481c00700c20654490f031101c0e105039125409103e500c515441841e00b0004410180c4802c032003142e030014064000403008074220082c9d51812038407132040000d01c50f151051030f1128030162058902c00034521750640c008c00b00c25443c15100840d01c0e58448070410800c00650000e07640510028ae0b2407130034ce40c6030620f4040007809000355800010b000c00c96041c6c4071741507080c042e1500c1d1003580003080548050b03e45070f031080c1d02c81d040c40c0809000250006a14840c1c3c50388502e40d81e4100c0c0710b8001030145a90401032107030921500307800c03080b4050307210842c0705980745d8140240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 386197329 1250 386196079 386196101
    0x302070b071701090c02031309050603010b040b060f160503160b01081b0402090a24090e07080103032006092a010917010207150621150b0f0a0303050706 67
    0x40c2c0040c10003800c901c103501d001480f8071200d440d20b420143c401e042c424419107540d00c071600b0440c3c84460711040715001400089407194017135072810749240c8140c6050302070141c0404000e80240e15016a4802c40540c0e54000b000c01081c40036075051700c7c00001c0d0200000c0c071160080f106c41c460f5407074481c58007d40c03040040c1d00a9107240c2c040c00702864501c2200540c01c14030b0000311030040c0ea85c1444030109020410942c41030301030750040541e24507070081c0034a40ca0100541940d8031402142c44040e41d03845024142d42810016643d00010300009002d59215030b8188615600004007940f00c8562a2904404903942000e980040107041c00840000304903040c1c00b842841403486454411000815000b0079200340d101c2020445c0d1040b5000c1401e40c1126056900030091440a0380c41c0071100019010a00c41d01c3c145841c20030051811110444180305115403000d4a51a0444101d1440b07024080d102015a07000c0f00032881c41205680d8010365900441c840e4130b407591102e01c03c2c03c100049501c401e102c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 386198579 1250 386197329 386197337
    0x3120306090f04020114040806010f0b0a09060507060f0207050a14030918060402071e03090801022a282d0b0a0f022803060b0405130b100302070b07 65
    0x5120341503450361440d650082281100c811695614001203e82d501b4003042c090421200080100c1d00c8180892841d040c0d41d001240707520501c1d52950500c00078440c0d0f03860000041c241e008144aa98401c02c000e01c1c803280215004a0000d0381005040200d074441c0d10b0480306c0d940410069010048640240940d15140d04055400d0400d40b001103401560319551641c400140390000811030f590340e605882d402a00f124450101500c0791017440700100c05164140c0120311203007400625800305000321050b55615042208450f4845400e0450159a03000a00403d000d000c2e00300c0070f40380c0050407010f40c900c50710f08550705d0301c030081c109056142d840c41602c0d6810720761f9040312007101c0c000c4e81c43c1c5103456522120f0f40c001070342c8944245c8002d00e400d900c010760039400016441c0340611001805c041c0c00c015101c0c5481041d1f00c4000c2901214002d00c2200445a82408100200c0c54402604100502c0794000407442c0288000042d0091034500a0349000c00c0c0d020030000d040c41100280c5650000305820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 386199829 1250 386198579 386198581
    0x312030601121506030902030f0604121e02030f030a090f1506091a09071808030901080106021903030b0f06040b0d0c0c0f06020306011110060801110f0f36031203 71
    0x70648600144c0203920038151980c0300c0000b1504c080016010351441e403819036006050524145602c981c010079140b000841d103614503805041203404861020f041ca4009500e4589401030a6080d50401003010802c960f980c150324020a240600d2200201d00c01c09081c01d19280e029280011107403aa081003c0a0349400600404421804c10420508408a4420300c4940d9903220484c1c01c000c21505038a421105030710001100c0600002800503030100340c84101d400d82e2540c00481e5a414854850080061040114000300307000e540040d110130000341000700302d29404004a03929a00c258040ca1000900007100b80207024980b003580000750b054a0074210301c0c26551144034a011090a000e07008980c00804185107a0152500a070036960400648d81c642c144040c0d0301d4002c2c211881b5011842d401c0c08041031a509908085078211440c51040a09003050301d28045404d401c00a5503032a180850300d45400365007150400702d620700002a103201e015480380c2051600f0510b8000f144640150240 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 386201079 1250 386199829 386199851
    0x206010f1a0708090a0b1b0625080619060e0414070c14010207020411031801050c220506030112031d0904020d11060d06080c0a060807110c031203060112 67
    0x6044402c2160814101034942e00c5000005d00d4403c99540300032030194001070310400b680000c06408803408919410b44181d5a44c840c0d1001c0d081034200d0030002070603143d03600e05030221b015450aa810030800b40685905101c2c86a04404e11035494006d1030102d0846407036111149454001e2055252140a10314028200300102814800e00c84034004d194070105100e01d1540502541650031858004000307005000303807614518102d60003039402889096017501a1410b40105000d4240102004501107103400000318500001151007180d525545108420000d41540ca04000c0d6001e00380502034043c041c01e8500e000303403035203c200d4204500070780b40b04100d100c00da84600302e4540c003e4041e0341b01da812006900e014000c0c00c040181c100d0344000041400322503560907a00c002e017620420021206004808002c00c020401c0900c00d00002400d4030001550452060741803041e00300180d002c484440d050b4200007402c004e00c0028240b802c00c0040b04200183d80e12240c80010006038180c2080341203681c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 386202329 1250 386201079 386201129
    0x718150206060d0311060408030708060409050318061209160602060c1e07022806020319030b030712081c18061802120a03080115020a03080717070206010f 68
    0x41c0003d1207050b0520b805000e1502508130991246034840945459140a21380581c10303800c02e03142d450010740381c000040c2c0141440d104600740d0a070400000c60030700001f140143c184076904a50960041c0c41409003000000d0220021805214504050300d004803210b200f041c4d56007915406a0300f154050014022040001e01c11503014048034890b44480700704401c1920710500c100000250002c03481030003207100007400010110011a68582102d25070707500d0404030f1340e1f40203440c038a46050b60118021000c0034001c0c1d003c0c00f150f06018040e18001990b54a005402060800b0283d4540320000b0b122001d40306128158501200204c404020b10b032061807800e552104070710401010941da81d00d4001000c0040801c1c0100c455006101c004207903071a581a58031800390311000c0f00814540c1c00042070305040c00f114185112110750041c5460385094408072a02030300549000140207100000040601461000c603214180e80d40040249504d00540c0e10420601503000c0c0c400d42209440814400c912 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 386203579 1250 386202329 386202331
    0x3090d0305160c1707051507110d0203040521070b0901180311120304050a0308040513060302010816090308121f050102121e0a020709050a0504150504030e090718150206 74
    0x4c8003068580000184514160b8030500e00041c20358445d926000c5c8044448550082c4900201e50341c100b48890700344130141e554440811400090380041c0024800f906102c429110400c0c000e6030341e1450402e030340032210309101e0103400c10004048009042500f9580251407500078091054280300802d00e0342d102c82c403001840705607444c440e04510a658581c10401c2055402900c401449280c855641e40743c003407200d500501c0782c00d00440d42407825080d100c46e03501c641c004680e0103844006965541e1304820031580307046201d05040c445039441c04030100c0c4400015040260200300c0c00300c66400c020495100c4502180c0c0f2107054440e2805013440079927800719003902603c54000ba002e888140041c07801d00003a16001c03d80200c41c2d00410b43c101e4055000600004403040c0c1c1d04200030586903001e448007515011503024050408451000b201031545901555000340030b49400c0c01d070a071075040020600f8600795030407030020b1221480c044080b000c0701e00b440000d26107441c0c81100e101d01610701079140c540c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 386204829 1250 386203579 386203583
    0x109140105010c022e090504111e0a0306080d030e0609010623150d1d06150d050102070b011503060506180d0503040902040303091a0909060907030b040203090d0305160c 74
    0x184c20030302003180710203840740000c043c8005c408258502d044c20100030400d10351441b50502c03032400c0101d4a114084840308480c2ea04454a40c170800201c03407180382d01c0c1d09034443e02c13060042650f5040002540c0c003060111010101140d6804904550900485da141c01c1c001f400c1d61603030b40d00d454010001038000c1c0307000d40e42c5c5140380c0e02c508191014102c00039007815181d03209140104c0c400141d0150000c1c42d640a29400a4000f003a00c01302d03038142022982d2028100d42050307840700d842013445003a1a0900f020950a84210000745c60304003190342d4200f100034203a000726148110908031701009a058000c8e80080c2405550340b9080030340303000300d0111085061040c5401140d00c88030900510070140110750180c07143c24010f41d030b15035807450010480c8580b4030400d40000c0e0000c500c49900000513084a22950000f480d030603d0307403144410080140703000340059003450b58503680c020540e100c5001540c443d51501010b0325200180c1c6001a09590300246440310020030100c04e40c0700d503074204000c5852a6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 386206079 1250 386204829 386204839
    0x408060a112704020405030a06020c06010f0f03150b0d03110d1b02041a090c04080c27090319080a05180a0f0317090a120207080d0309020d0b0f0109140105010c02 71
    0xb602040454020710458102c40d8050082101c0c140c280005900201840d00003003003201c070310781c5c0c0c0d42000154440c0140607030080040401810800b1508081500f40058000040040e0480c5a00d00203040d00c0c0511030101c0110b60340303082c02c10b04001d090000404501150509080744828803048228205c02030000031310a0b6503c2d0a10405050052200c607682100a0590302490801c00340360250b64106204400040c400ea0b4000181400c00e075082c9000202003044100e010000307d003516040e00c40c0145114602d1109010400005036400d4411883c4022070f2101c0f16181400458082913590041c940c020003c442c80c042e0380780003000503210140b160004542c7d0440603280c60111280001d440c1100c500440d841c0500c10b0110b800700e91403014921030408040a0216604140c2e160030452041040c1138101a54003070005000c0d4100201d01ca2004080590a04055a62032207041051303c0b928a0007101c41c00600450f1124400d0070340516925038074107081d40c502000280820b41c040b100a01072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 386207329 1250 386206079 386206147
    0x4050f040e100923010209090a02090d0c060f2d050a020a0213060501080603010e0d031505090405030306030d031103270105090c1008040c1a0c030408060a11 69
    0x401c2090001c0c10806030a18018007603d141400c1003d8031102451a81c680b180c024000c40e00000014400c90300c6400c00600300942c01d5031b50085e400020b410150750260022024105a000a00407944400c05000d207034072a000c290b28880740091010100c0344085c1c129854405041e45030100c085400c580d80e42d81450444d60382c48034000c00300d00f030001a220007500103846a0303900c3e1001146408c03500a0f610280d0700d9840943d1054205801d9071100b000c6408950080c503000c03000503200c1c1d0405483c5002c0344034030107041d0390380d42c0204032650000c82e029034098202100307000007403400f80110300300c070b88003031909011020002421580e40e2001a050b0100c0c0121020091031b0001c00b0301c00440a84c40d8000200031784d251926489803207801c07984038079124034904421400c0f806e0041d1080c0d40507907040a02c0b031907954103100000740350401c0e13200c80c10710344141440003a1050504000800143c04814090302c1c4506000e9994006d5885d155824850280240109201f0400b10704407005c0b03400031000c1c50089 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 386208579 1250 386207329 386207351
    0xb160302030d0c020102070b070f0e040c02010618060501110f030319110a0207030b1018050402060702060408010608100c05090d020f03010f021e03040f0b1e01060c030306060504050f04 81
    0x80d611495501800d0b00303040500c0c0d443d00c0c1d0307010740c06040c909003d604244020303660040c0c1110705004010000e0040346d03d54420300c0440c24039921500a19005000000f1915142d002d201030002e01d004a260380152640d0040c001542e0101348960203442040041003144200311641c0d4a07400000d003102031036081480e030034020a00c590828030100114144182e520fa61409001351200c040e80000e480c00d0344c03108080b071036107004000d82e0011210414040d0320008000700030311003e0700000e403041c1c0e07200310140160700250380c44000400c01022400f00000d481450500020b04040514003110b00452807d03207111185074000c801c80d41d07400c008a401044900c0240300051484100000c01d0f0740540c0707845035426100c0c29550080081c40b60103200000200352544082c3c0c8a03100499000f805207001402000c005109503032100d030064407814407000c60b0403494102d40140c000c240d01c8103000a0f4200c18480900d909445690050f03e40b61030490300d02030030600070882491800e1030450083d40d13101c44043d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 386209829 1250 386208579 386208583
    0x190b040b0406180305030907050f0109030602030a0603060e0f0f160510020a0c081e030a050906161505010311010206220c0b030c091807080a0203091e1b01090b160302 73
    0x8926100500c801c0070805950138010302d00d8100b02d5004849128144003c50640b40c006020303110400142e41c0d01131a5425540c40304003a4001070319156219860b8400440041c51034041e64803504035203401400c0c5610301d200414600030f00c0385490580c6411803071036001034240c41703040230054840c160380103451201c181d0f038101e113000d6200340c0213048100c2070640816a10004140740d2004c0c2003a030344400e88070382a425a0b0b41c903442810401000310720200060001c60802c00054007501501d1040c0c1c3c451106d00c3e4031100c64407105403048003040c59581006104100c0004480c8114540a100802e070380c0c034002d0b124801c5091102d010f03415800351044150100050321003224040c1c45445039068507401c180e4250300068000300c10462040a0700010360900d6640101078500c9081c1c81c1c1d81c0d030001c54a44100e940700a5002402c0e42d00907005608080c41054814043c820b10b0101540c010034500300942e150260b05a0018006410030035030080c1002503845980a54040c07424008100300400800d1a0a038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 386211079 1250 386209829 386209841
    0x90f0e07121b030e15151201060303051201090203060d0303021806040311150711010507020f0301151701020c1209030309190e01060306060206070f180e09190b040b0406 74
    0x100c07030740c1c241410b554601104400365954100652024440380710b030b40358000c0c1c1318040342e01e4803024580144000780b69000311200c0d0111010300038110344000c4842c124030342e080d213a85070016008510009070704111144906180e07801050150b00450860a149002514640624a01504058021070302805407401517501c175000080060400c0c1d5282d42d6491329a40401072a01c1c000e1040c07681400309000d00040074106e8000c2988154000102a1000019250750b002400180d80229246044440303544092140102c000529a200c2c216a8a480d03410303658901150140749090340103108407442c070740c00081c2090811444001c195154000803002c01c0c0b840c010448030f260f000044480c1070314000d5160703060405950001500c0071700c60f070700c500b416401c0da050341c81030000691282d0700080d4224403809610003104180e2511099800f685810303240450100d0f0080d6214000c00c50500940c00410017815945580102c0d401d10ac40c0519114551801802400500101006800242004503503030200c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 386212329 1250 386211079 386211107
    0x81c03180510050903070b0a0c021608010e0124030201030b15070305071421030a0f020310050a05180f131a090606040e1911060424090f0e07 62
    0x2494020340c4a00308569600da0580c0812100380c0740001080ca5040003000700c601e140e4004840c100180c44a01d00303000100300314501f440850190301c42041c2c03098680d80f0518018070300b40c1d0020440e0040c1c0c496160071100300800e03640100ba20340100d00203220a184850b01282e409080c0044c0c5e4208920109007441250042951700c0310300040d80004041c1c006001d40421030181043d04940200400310f281c1c0c500650b240c140d281040c2002070000310250740d00940e0300030003c00e00400c0c622901c2d1440d03004d036001500d42a48146090609019038103140413041c0046c4000c441c0400004510351903d080f40b14003802000701c1440c090001104d84940741c9045034003a510020b080c012100768000c01200c21800c0d0780c048618014480801c40b140303051b00072410300001140180c00b10802c2d0f00807613140e46201c410216000881240d2418a998490780600010040309c11109411701da10b9555000519544804d4002c2c4505107030203122154003443c41c2800e1314100420402c075a02c82202c140d40c04003401c180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 386213579 1250 386212329 386212361
    0x30501080f0a05060c0c10061509090603020307120510060f1404050c030601030c05041d010e0114280e0c0c070609060e04090c031e0c060f17130b1e0f01081c03 70
    0x30000e25088009c6c0a0360001c15140d40e0181d50a4403462100280c40b030174413001c3d5060380701050a0208515240888010b5481349040314264258244c4540a544e0309a21414115141100400540c5101052500c04200442e010483d91611142c16070080c00080c03c01030400d03949117030710100c49020303208036800340c0911079080380c0351103100c034110000c40c2e002d019038550000740d00000503016050704070801081070000c021a2605040c01c241c0b0312010340c941301d400c103503460700440050800c054188880c00703220003200c2140e881a112041d02c0c60020158015410444245410484107078048101215880b04480200c2c010380340b401e0031083e440d055007000d029066a05903048a042e0038001039004180700d000d61428159480d0416900d4640442d00100450310f581c4030911800b03100f0b0300081e44441056940003e40361162580340038240f003202c601d14010360045441100308030010300d81ea4024400401c0341e01540c1040d000985964640e900c0044161030150003144c410b0081d00050030800b04040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 386214829 1250 386213579 386213591
    0x60a09031202150f061c02010f14040b1206030606030a020d0b1b030c09130c050a030914010e16291b0f01230705091c080a030501080f0a05060c0c10 65
    0x40b083e107601d001034400d9071084050090700c8a1b05a42c2000c4020300b190161601054907501c060300f6104d0070310315600030320201d00c204000301300801100c0142010075411034010845150030011301d841c1a1002d0600c07440fa501044040d401031799000e00c241c2d0501c0d0701c1100c1d04c080c1c0c0c50382d0000450400c0701b0740c12441d030348c4400300400800c010002c000d44020b0a081b1500804180404018000c403111b0149120015904106218105001ea0840108a0302c140d840c0e605054034001300c0d80c00c4510b000c8030380321980c1003404061451002410f602024013940345984c0e0754407030150100d5681034050300288200110100b560648217100da990845000400416640d070003a0f1440d1181c0200038910004802000c0158072029100ea0b001403948190451f4036410b2800e0f4803d420010407020203e015030b600c003c440040c0d400105070b08040c0c90094019140400c0f00e5060005880c2059050081c0f042e0944c46a0102e2000c01d00000d08940c0000e81c3e100141d540d0001c1c03100081c10a00da46401d001ca0f141404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 386216079 1250 386214829 386214841
    0x611100207200a03050309190317030718060207050f040b04052503020903030409090203030408011e06060503131227090b2d06070b1f05060a0903120215 67
    0x400c92036000700880c103180303200180d0b0608001d54403003503010284c4194070034806500c1c0c03800c09810740601035949042d844651075072131341c8045003100040c8100c2e102d068080180311601c0c3d00801d02615406118034000181ca040c404025500c5007180314080c40348468000c43c40d62900c2c0c2c0c1d40003d80b200c82c00341051105d45840c0901d801440a10002c4071807084061003d15280fa1103032007601c4010b68003c01a515013440c1c102070030064002001c09903407601041100145900c000d1159140351140c0d40c0d041070742101d08031856000c5a8840d403224061120400800c205030f03074100710150b00207a00079061092100070b084111407a00702816100c900b400b0b90207800b04168034248244040b600351070424817607071000d0780900c0292540c000c510b201c51900d0a10482108054025a0a01e8100989032a0620410303071504951001c0580c0c3c1003d4040c0c10841342c1c11040002d103205405000280d84032454240b5800000301004940e101c00307043c49a00400c3c413400d603032090040ca150084288042c681c0ca0406c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 386217329 1250 386216079 386216093
    0x20703090501080a02040e0115090f080a020337111503040b0a112b0c11300d060b03090f0c0108010b0d020315130f0f06030506010611100207 62
    0xd8003803540880c5a19000031200d00141c02110300b5100510700b403810a910301004410b18020500c61030f401d110b032815010503003c00340c501100040c40ea40008100004190041c542440c030b5403802a807200482071001c0800300c200300785128044440d440645808031031030030143c500341700c80041c0651004104074840103454010000d140214021860010591070300c2d80c3e544100d400d4a0b103040900e04c001c0c44444040c2020030b09201c0d41c90000202210000a002c641d0f8088501804154000c680822031000c2d44500410000e43c640c2800c4920011064100c2030301e044003200206607071a203410009a00c42e04828581024000307003641c144040d228100010440d07198840e66020280510980c1510501c641c82405c0042c12581040d008510702452907004201a510003001070341c1c06034800a5190300364841c0c10345084600000c07000042c00c40c00d00241c3c0d105076005186958086420180e003400460808982c0604451190810284131007100e42460309242c61402d00900651021602c17805002c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 386218579 1250 386217329 386217347
    0xc07110603190f021e0703050d09080c010c031109040b0a0801060b03010509070c1109040201030e0706030c1103070c062a0f0c0803031608093a0906050306090c0706020703 75
    0xb841060020582c030040700400c85c0908089441941c024848800012030104000c0480e54001c2c1b906600c1c049190a072541601d101042c01c60351440002042682c1d21020300c078400c0350103484e240c14030201c000500c60441c0780c01940e0780c1d030f4461543d07140f0200e0160b42c0c2034081002890307988000e100040c1c3e40c164060841c2c0003407003024040c0849100064200344a1040e8802850384031400310080b032000e00a01c070741881e0082c0200e040c5a0f0303035a4044510706040014070300500d2a80e80c0410744000031907004100c5c400554125902d03134001d00c001c40002c3e40320702d402020b035a040d141c0302c00402d003640d541c1143d040c01c0c5a400c1e1800320b541030300c0d40280803070040700000703003806140c164100c3c560740c82c01240e0b40d22007120a14409468201326008040c0304d4040d01d6005400b0340120b071003402e403000e0020410350b503411324401c805104491050060980b0320340608840c01c18240314082d103160a4020f040d0b844001c00031441a5039440000d00f0408420050755003031070700710808544541c5980303005804000c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 386219829 1250 386218579 386218621
    0x10e07050415080d2a12030b010e030a0b100e0405030a03110f0304020f04060512150105060408060403080603211314030d0e0d050a0c0f09050c030c07110603 69
    0x10a08000c8034120880c5564401103800f080020208a02112403c440c4045801103800c00058007540c16105045003008220340b50780601d401540c0042d07100c0c070241c01c03200301c03010450501c4000405000c240d607000c165060344e00d41040c030420841d40c8420032829a95000d4004581e0070800d4000c1c482848800006021201c5142d00e0030080c0d0194600d11441c039005842041c0d50501341080010b0060400d803241c560700c103101400114100342c407100018203116801000c180d840d03110020700707801c1c0c403000c190841c0100011389015140034200340d10b0940380c2d14020000360070b104680020900c103880030440130428101040c110610384400d95811300c01644420113440c05078010203400303c0d81400c90042050005001001082842c1d0750b110240d0f41d00c50210381490340a18030503400c41c007140c3c0601c5043c007030074407901030541c500e0b081031000301c0301c4100c503040001e40c24513000c100000d20814501701d0303800c600c2402d0b0b500e4407a08070345001a50100c2440030250416004030512540c03072410310f111440d042e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 386221079 1250 386219829 386219831
    0x1e040312080103200a03020103090c03080a050909060d0f08160b040b04030e0922030e0a03060b0a0b0a050403020f13060305061801090203061609030b0103050307030f02030703020703150905010e070504 88
    0x100f520400b80082c10035042c2d0790305c00d155080c100010740c043d0340503c02c024070030404510281e81ea91114000d80e001809044081800014480080c1c9006404e50b68030010445041e841c10126841d0074414080c0750b24020050070300003501001d01144041d105004075841040d59400f45000c0c9401a8110820b40e8120f0200758100b100342c800780351140c0854410ba0030f200c2d4880400401d003040100c3d00c0c11080c003e5090190700140c0388200c1c1c80c5c55003880041d40c010200405d14190351024022004403562000d8000901800401c0f00d05900c10101c0f021a41c04480032078820004134001402c07074600c54041e100280c54a07000100700540420340a10500c1040102c168101184c0c44650a940341158002e60503080301000030202c01000821281c83c10071840c0ca414500d491b540d61250580d020f800540c1d203544041201810954006601007861003070740b0145050110f40e54010b5520b0200e4040202400151452442d05103415031040015940210090060081000003182c40364124000e0300e0040b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 386222329 1250 386221079 386221103
    0x70803040b060a08010c26160503100b160b130b060d08090d03030b010801060f050d0f020c100203040c0f05031905030c101a03060c0a0c03021006061d1002031e040312080103 76
    0x340462020f2007500c81c105412823020b00100101c55071f40c001461a07501c0140c0c224049081d80b0890081c00d6110031076030031a100404075040038a58034100402c4500640b5031402c4200001c0d810b0b540842c2c2050086d0b031942c040c44000c2c5400b6426000f1081c00d25008429a4110018113030715420083daa207000b82c0303c880340e0b81d07258802102c00d12001d40700c000108408100110394420700754452042405e044030018105050306200ba824000090f440d01440e070b8011040c00140003c50300d100009281a128600d2200c4c0f50001003070715056107165a0100401d0040c01605002c3d003402120b02c0081e42c3c03019a0810107000c21180c005101c200460310110000030801d030b00034180040c20500803034661400c241420641c03036044401502d0180d04404501a1341d00b840d8000070b540c0285005070219071900720307942d85010706000c83d0880d1500c04501c201ca00e40001c1e2080394010044444481c44400c0b0001505c0b03000024030100d2090380e200805019008092041d0140e211024505072446140c0000038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 386223579 1250 386222329 386222387
    0x50c1305041101080603191b0602070612021c020a03240608090604050a121803060501050f03070308180105040810020406120501030201091203020f0d090503010e03070803040b060a08010c 82
    0x1040c4c100321041c680560066030300ca42404e030642e20000740700e0710608450090b00a1074140d0343d1090019801000540e01610301848255082a0310b1002c8101c0c1e490114203040e10a140781c0150f400c51075000c11025400a8441c4c1824881d41012103001c0701a82c180040710703400c5800c00030640139481800300083e031101c003180600b032003c40c48a0090b40c22000810000529445207000710f4260b10070b90f0180600c01205680301a500703a40d6500035801043c0018141d8540342c00c0c04000006005107602c00d420025042c00060411010740d40b8000700b40c80c40c1d0700d00520383e40060301c161150b40c0000400b48602c903000103100700d041e00100255203007543d4040d6403405410441064030700a01000340804c0401c0e60a101d0b0030200220f081805001e4812550b030b030b4800c055003a0400c441c0c03c0340c160000b40c1b0034038140454102402410030340c141c06802941f802072a41c558410901020700010800b8910f64045001c903601d100003c40a490070b40c00800c00700a0401011306665400c83d0141d030048000700440721 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 386224829 1250 386223579 386223587
    0xc0f1b03120304020402030c0d180209070c0b01061d0604170c19090f091401060509070f08151906020106030b0c21040302010219120e0304060c0807050c1305041101 72
    0x8941c4400060718290389841d0f08010181d0801045404442010b02c140542604240a00c401552030280c9400d21010b5900601200b80401001c2505000c1c14401890002e8102c82082d41154141e2500000d030000f00c2c0000d01c0101c0819501c50341c04030000c10003103400414030a4000c154841e4030101c2d4a0450342c00c0c1446505030f1113642e0b5000c050078440080202564540002050701c005c20740c005035000e103c0d80c850042c3c0101d80d8481125a550b40018407260a218029a4114180d07043c041e81340600050010200e49004060820183c074134403440c0001e80314501d003182480d003503058600001c2e840d49030090003041e4a1105032480c01000d00420301224542080341c5501c810701400a48242003c0b100700701c00800a4021000c5650070000140c8045200304000e078040103581c1c0740c0c50216a00380c10a41940c000e00c0155160f40c00800082000e1500041c011040c9640545c1d080c2d01c61040741080c0342450364a040035604012400c50446c1942c000380d001c1c80c4124400c202d035072003000b00c1c070004503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 386226079 1250 386224829 386224843
    0x72301090203030414060d0504080909010603052a3006010e01080103020904020f04050a09030206060a0602070323030a0504150e210109021002030703080108160510050c0f1b03 77
    0x10b50150010801445920030800c0381d810118005080913244c864114900d008542045030155943d07a40800c6145161030030383d8590707004014502e414815828880200504494070356a1050021100101d01900b040c00300d00741c07450303040c00c40d4100210080d0911110540200c0c0c0c26543c03401d011800c0000c41a42c081d911505000c003060b915400541e00307540c02c3c0000504054426a4884000f0300d5200007599203002c0c0030700c251038840d0040703220841071030041c0c907180700606000e108a210202c2488000d9000400e4400c8030317000b28850112046822150b45801c0448054140074080050380e0480c13260004001c2003110101400306640c00c820200895400c80c04480b2540e00120018403041c04080041c00101031600300d5000103a000001e900040c4c0e8410310521001c05030b0400701c0c0c00d00516801c20151401461300c03e000d40451404030000100030789240c05001d20602da8034503040501841001695004040c100848100b800040705265a69420014540007404000c080318071605000ca03180c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 386227329 1250 386226079 386226083
    0x1110d090518100311010c0f1101031103090604080717122e170708060f010303091a030601050a0302161a07052511100804060609060303050315030f0307230109 70
    0x8081421945d541c2681a011024103040010a00450000c210006040034415110f00121820b402c00140090140c0300d1444003a146084c040c001c21009200100c0d100d03034003d91101c8402d80c0c401c440c0c902010488148404030005900204110740c281600b40070707031030080c0d800f01e14a04805058061058028039284450846036040390390420820003940480701021010205440c907003a01e48541e1844d0030f0341190120b516050b00780c010024180c0260cc6500039000b41002494a00f000c8020b440c41e40c40041d007840d04001c070004001c3c100600c203606031350985c0c1614020042c04049803d0203003c24413007419811160ba10400440d50f04d60158040b6207000840c40440c0c01e44118641d07002540b03095805064403503050f210301000701c56403142003140c3d490f5480c2d02c03140780c182894203204003282c1c01074000c5c90706a0324201090001c07030303044000d03030780e1044400601030110009800480d0500000c2c0b0312441d010310000c101c00b0300300480c00300e9024610380c400c0c100c0d1818644501005090714010400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 386228579 1250 386227329 386227351
    0x7140c0409120e0604090207030e09060105040807060806131a030f03031e09280c06020703080d020309011b030b030c04061d040c0503060a0207060b0d0b1501110d090518 74
    0x1842c0e0309140524242e2080748030042250382002c1e43c03101110203036400b005045001482180000d00e03c0c4c43c3c10004e89800002c28078102c1c1c01c160409021030f076074213070078080c10040c803103c0c0c0c00042031680c40803804910f00100b4001401449480d19050504600159003144607024221590100180000680313101d04411408480540702d1005000c40b8850060039800c0c460080344a008401d001a40101c465201080c1d1010310f0b541550404a10000c019044070003150400142000811040c0c0166208040003c800603540c0c0c4814100b1401420451080852000703500071206840350161b100026001d015000d5903800e02409003008200c91040c040c500742c44170340c8094403112a950803000c3e91f0251081000804903901d03480024506201154920b202580029031441000004c0c091858544070645910382c882100341d07184011020010011101d401000e2803001150f0b125640b00100640314109640d00c138120721000030304046c0a030003914002c3c51a1203003049a0008113a0301d500c58800054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 386229829 1250 386228579 386228603
    0x206040612020715141e0a18021801060906021507030e0c0405090714030f0307030e0315040b0103021806101412010906050a0b04030819270806011512020f0f07140c0409 74
    0x6107a0080c000e512329488a440785500c098010303250908070701c480311154503050220f50300d0000700500c0c0b08290b400c020301319007000444001e01900740c02600e40004084c2404a1b09581154000c0c2c07a10312140c0c4069409410503041c0900b01c60007045420a0b00c041290022030f070483d180070305035280119551007070280c2c402c00079a00030038814a404845120010242c0b801810599807600616070280c5041c1e80098004004104510f410954002411079030843d034041ea29000300002e09515180d00e041090203501c034100034030060402c2c1102c8903d55106014829561104000001042d01d4028103004d030504440204080c4218016901200e9002c4040e51902c0388592446c0071040c0402130f000203216081c04041c0070300440440040d4500381000c00000d510346001020b6103040c4060344404c603078907c400001111645d0004602000c0482c9174805a03490b0041d035003030708103031040295801d2500f6000c20f051040102d01d610020120b07881d0030445900e1a0b00c0c60070082140c40a80d401054800014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 386231079 1250 386229829 386229841
    0x80c0d020d0507060906081005100806031609020d0f02070f08090f06030c07150b01170c0d02040b0d0606030209061801021002130e01080a0206040612020715141e 71
    0x10414949091016090305190300c19650707201d18000306504004041080d0b10406d01c20a1307800303490681c1c0302095582941d0502d00c0d08001c074043e05403034040341041004000004800f510300b04000c850324400210556843e640d5444e4081c02034005000d070b41e1005d03003007810030700100c8074500030b44114a80015040d0700da046a5039a0602c0e640c0b105000d207405c18003400100c080380c0d4400000d14032a88103415003aa1b00d06075860104a03180007005000001c1d0700c0c201c14920340343d03845410310034a03030100d0b040188142c8801c000c2510602801d1121113101d4000030f00401e0f0004200060711201c203000c41d081c800151111020f4060340690740d49641c00440610030171010500c0400d18000951041c0159441581480094416a4051b038600c1c505a50050350800c10748050780d140c0d0780107001900c0904440340e503990015180d0b125908c201c404120704078940c0e20602903907504840200b0f902844440c94148501800006885005491410b031014180003c4064800308842c450340d101411030a50181c0c2c41d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 386232329 1250 386231079 386231089
    0x1d0c0333090c0402030403030501061b08031b1b160f060206070f120504030504180b030d0e37090c0f031e02070516080d0c060b120a03110610080c 64
    0x80030340c44648036846041d269510f0342c3c4000c40c06240030f654080340540c181007010b845402d41e4841481c00f000c12420a501080000055a80202c400840518242901c03d8213441c51b0150030f8440b00c808040a066800840b8001400d240041303010015601583d51200100c040500340c0c405c44000d41c01820000e250359100c4c14041e020110745041008640310720aa0b424101e0700221800c801284001409001c40d28809100130100e102c800401e02440e541000441d4131740203118039003000d0102c504009000d070b949494518030307803020030196140c00c454010380d101c014100b500d0311103581081c440008540c00103540203030305e0441600d444070007c00300c016004600414002d580004000f10700001c0c24844c01142c00100307240d80c041c4c0001c0c6650030710002445141001b036800b048a40d40300c0a21001c2d410380008032401102c0d041600001c1039180400820300900f81007602070010b0103420391000426820240e100d010781566000c4600603615811110700801d164040c880aa41c44149416018648 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 386233579 1250 386232329 386232331
    0x18060103050604112806020111090109090e1c020102070b0105040b030c01080c130b12060a1a0304020f1c0605280e01060b21070305010f0512011d0c0333 67
    0x4c0036100741c422002490440c1d1200c51550001d59020010035010015a5824000c0300e0040242201d440d2422a6a50029004803030507c07540e00000d8440c40724420403e010303c032203102c1d01c030511070b421144480910020b0007075105100865900c00d0080020805003081e1040c1401030344003400814540329214010350342c03d040100744020003807041181c0c42d24a46840151401010b1150015403146007920606c40b0951004102c20302036160950f04100d0001540000c515030001e05003940d603641c030b5038008980040c03080014542c014a1201c1030000280d812500c00010038094001040140c40302d16042d006190303004400d00108182602000c1d007010254001e142c40103401c03000040c000e5540c103800c030141d000045566440c1c010411104500c0042069485e806406031604022030343c1400307121907030395526024090103220084405600c080e404d40c00442c40003038403070000f40060400803280d540c8150003c04580a0700500314031140608600b085054120304036070a5500107020303100c5e01c030f81402e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 386234829 1250 386233579 386233613
    0xb041a0f01050d0f0c150903060f0e030a1103040e042405070509190510030504150509151909060606140906121e090d03060602150604150803040e18060103050604 71
    0x41080c0d00015074400007909107006c041940c8072100b00d00d18500780360f4101c6140c0c3c05a885400d00f450100f0f00c4180d00030084070319001c02e0f41000b40c03050700c040000741e203180290b03084030352001141002d100600c9084414810046003440c0000408201102c03000e055480940301d94000ca2018440c00d0801d1405c5405600e525a840c030440321f01651710360014011020400b0440c005c242e552082c001884842c0301c607a8403680d04240c003800305040514089503030380a180d0b0f5427600141440c2c0840c050288006031503101c1259042c06101c4c44c280c604001000344002e1040d9804204c40c07a50004e103440910302554207802e80240f090f42404454407418451010040c0402d03641950000c00004810050303180c540215030341401000f25244020000e0b00b1156150855400d66000010841c0c00807910103440781d11a10030758003c100482c480301c085640780440e0b04030700308602000c140404c0150f64544298450740c0400400700f42c0d402000e403016210b0303000b80006401a0402000600850491060765003c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 386236079 1250 386234829 386234843
    0x91d0a110105030a0e0601030f0501050609010e010306020304032d0216061202030702010e0d03020403050705010c0506181006060206040204050c042102060f0a0f080603011b030f090b041a0f01050d0f 87
    0x117100d0211860529109070011a400354800074400c0c03d1080910545034440700540e03030701003e94142512482403010500c4010304940d0000009000c152090311803c00340d04145184100d1040c400e005c0f402100d02028261005104d02d00814801c401030301d582d901260200e44400000030102c000440280d03000525000566481b805140e581c03030010040c2c00c186031107aa80050710395040d4540076040110b5540b1450400600300f0401000c80ca02140458100d0f0030341903401c0485020700905814514500180324965180880010b513254000c030313505225038401c0300c5c02c00036035680b0213005160b07002e50700a007184407460718121080e0311403140724501084c8c0000d02460810141c02401038807640902e0181c400140c3d4403000da14035a0708401d00e180c1180e8101c00a000108244e03825410900301103080038201900c1d044034410502003984601e082c1038002030401410300d0182000800801c10b51250051900b504001642001070f44001c64140e41009200a40004003901c17003142141d41400151801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 386237329 1250 386236079 386236091
    0xc02040914061e06010503061f02010917070b0a0204030c030f0f0204020d0b01030c0e031b130f0b0a06091505091903030905040b01180308130f091d0a110105030a 71
    0x10240c100071403442409051000c411105003003110781d00340f8001418041c107100050060010703581e00c0b03428020f10350041078034440d00c0d00c00b0103130220301402c0403240c080c0c0803800c40010000c4080300403000300542030064107000b45640304c07940c8034400c92065100281082100c08424000922401d110703000c2d0b10f0140510b0041005503800107030480e800780c842004543da0702c01d039003001c1d075815014103003e1000a0820020000c900000709072501000c403101e503d09a0407001c004d840d591072050f003060038903110b5801c008030845150000028040407800b01c2c8100809440016082c0c07160b0b003800281c03891104801c050040d14841900c081e00074540c800e50101d085052007155644101050b001580070340d54020125107410305000c2150800039000e41000f4544d640100040710103a90242140d9010f1a02d5a658003c0303d001c101c0c1c1400f0341c2140d42030001081000803102a40d811404100c80802ca130420f040e104d43c002144e5460840c040142004c010b9007070707040d1a43c0660003550380210700420201c2c0c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 386238579 1250 386237329 386237363
    0x406051b010612121d04151a0702030712030c080901030204090e070e010603020c07050d0501181109010e01032a050d0506010f15200c04110903011b0c020409 69
    0xe4440035080360301c5043c50703034039454180100040c940c3c0300414203003003030080c0c40c03d50032829000344140d0901a020340c0e01c60070303d0a1300404070500d0400900030b510f210300e0090341014059842e0b61000009a10921400c3c2c8007117030071082c5548040005a00d0b49442c3c990035070f580c2c0c455a00e0303000fa09a00d41415801e2100040c3c00015024a0640f14095800341c40d9041c03c0103e100d015240c1a0002d2040520602101040110000e031420540d0021201c60143c1c1c1c4051170280d0140000300c000300c0800c104900c451040042d0030b41400896032045446880c56a00d9492405482909200150240c141003186017031880c2e2803044081c11122120035485a02e4030f5002140601442c000300700e88071b034011801040f2950442c0c401402034099958090021000d80394000d01d20980195543c040860b6071008240f5100e0400003109440c0b009881409458111113034107044d07030411074050f4000d500300084182c840c0740c8201140301828098682000303100f00c0c0e40a020007000b86110880352280c031008039141d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 386239829 1250 386238579 386238581
    0x315070e01030605060d0207150e0705040203061c0c03050c09060d0204051f06050406020601080c0a1a0712030509010e0d2003040e0f0402101814180a050604150503030406051b01 78
    0x5059a22410260b80c401052030070900e035270a90360901c4107042c0b40c000d080d1900703040440c040b4201c80045a0250300c036110342001a81c003003403400b8000340ca480d11136000b10070004502ca070703030040301e000f501550700410f0701c9401e01040302411100d8592040380f420a090040c5086d5101980007002600009400402d80300240485000703030f084100403c00100e0100426503042180304d02401c4000301600c20b03941c20801140c0d0880c801d00960160f061245824400c2940c09020355903015040402e4403407a507403200c03001d0f0040c401a00d401c0700303950828001c51489e900015200a4140340b543e00c000d0310317030102145030920034100480c410250104000001b00585690101c41c010202540200c0f45814184108403d910241800c1c1050040600e09861000008030240c1c00301d0b14509500c110300b85410000985125080d5030038400c10902400b48501019160700443c407072103013502c041025111240920740448118861607038160300401042c803c2a200318040c001d005550303070076a4030030f00e98211464 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 386241079 1250 386239829 386239837
    0x1d04030e030f100b010c02030d0f050f0d020301090b010318031b060e15060108040c060c0f02060c06011e05060409020d020408072405042d080703060e0601050315070e0103060506 78
    0x22030140e0100c034880c008003529100341342d01d00c00c00f401d184040e0101035000c280c841c840f0200f03040c1840848101200624001c00440f40c100d100001c05070380d0380f22036011601c0250409c0c058a000b5500c2e014000c0c065500904c5450350140710f11a80070f5600d1000c2d5412035101c183c0458014000c034161040b03200041c1740f402580000c102d0b0728003810b00e15403041405407104800614131030421190724244008240810801c80a0b02c000345040101e07251141891810b50510300002500650001000e03801c042c40422418181e40c00700c0300000700316035a2105078803640400c0c007070194003040412003009910700c55401030950140c09030015007010380d960642e6051816980c0502d030060142c07503c004c00715403901c0c002c118412840c1015410103003006030b01819030103c80204c00310450031100404010200030f12403070040480d0011161030035180d00e03112015000c0000c107503140c2d124490011a041c41c020410f08000075000c020354041e5075501004454060107903a24606142d034403c030105403900c40c04020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 386242329 1250 386241079 386241103
    0x150a090e0d05131403070b0c0f1c0504060c020f1804060c0302071e02040906020301090c020f010218010c0c091d0c031605040906020d060f0617011d04030e03 69
    0x18400900d4a9031a04104410040c1400c120042101d40c2080340c040780e845007600d02e190f8030182280b10311404603103851100e400400464001042c108242440011003440c280c400009031101c00b12081c010f071481c0500e1780c0415010400074070050241d80e11540000c0c5616000078082081e010b91180403031b520300c4580c6d12091303044c0304100400041c06018000e61000c03000c546000c519100b03030f68507084210440c0c0c5a08100c1c044c5d004c5000c6055540d150050040580c00040031075480d69a07510010060144540d0306026001f01d203228503001708184295603007650800d0309c54400d014a2401124520f1f0001c204603030190f09001c01083c96a60381c490090000d0100040340b0040201003a580c2c5070030710b100a8180309030b02c00c505d40090403904548013400c4620584001c01d981a0510305100680185420100c68614201c80041c095020301241c6088502e15110b18072140920210100b403000240186071440700034904590525005240c1d00d98020f0003441d1162504140900181c01c054100c244 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 386243579 1250 386242329 386242331
    0xa080d090c0b12040f0807120810060518090711010204030c0509010b031302010809030c01090c1a03101401051c1409010612060c020c030a0602030403030c0509031005150a09 76
    0x800c010800240e102102425a50b08010708111200300c01d0440200c00074401000000000608000c0188180c162101158003031115001b240303103903400034142e0300c0444084030b0a9526440000d0305034061000c440040407103016075580588544148552074501610079010020380a1000e802c4600c284058805103102d1000080c1c1c05103001d04000c4501c4041e007000c22048010002d0042c0c28071000740302c0455540c2030074165415941c05001340d0031401110300c2c1c20540d5080c01034030420441451801000d8403a03140020100b40d0740703190354030300d1070004840080010b0b200d61400d0011980b400c20071100d03100145019441d00308001c0c000c03140b030043c110002d50340c1900d8002d81c50445500380b4409a000ea401c1008200c6035251908440d52025944070180482da0746200460700980700f486003070001480078003102c41c10145458408005d61080301c007603000034138105e030a0200c10300c40e0045422a62006000309408000e0800100007020090b01405540600340d00804103034845442c904020400454 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 386244829 1250 386243579 386243591
    0x13020405012d181d0118020304050d121d01290a050f04020403140d080901140601030c0e03011b0206010e0103020612090307051207141c110a080d 64
    0x2002401a000b80c400301d500060586510b0030b41d110000480e01404050341c94294030b8021861020040109150086540c802c01c007110264240c52241e00541200c18071102d0780c00d41c0c0d24042d4020102d000a60300200640c1007000d8a01c2d100344101c110f9900b500c8012400180e8100d0001e41003101d4000d0b402003070311a5100e1000141260300704501c1c0700c8000c0651603840581c25240002051060f040c05113600c82d00c580d0b90740c0c031143c1e200d070f5050b503014640c170108070b454044248109941d05d80b00c820300c641c001260032001403404007060003410540d0010300c4603000740f600ca000065020303140003d4042c0410441c2640c2041e10782e401d0103885680000f4a03101d0803c51121440207092180582201e000e0320780c3c2600400058a40c4021980d110841040e00b0100303440d0209901d00314030506402402922810403200300707145050000b0502c10340703e070401c0c000010390300401903210b044405690100c0da0040340b520213450302aa01c1ea44204001106845d071004855803041e0307a54000d001c440103c0d035940c07a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 386246079 1250 386244829 386244839
    0xc09010321030e03040902070f02090702010203061203040501051e07050a0b01051008011202150d060f09050609131e1b090c14040b0d090206030a0b03010501051e040911130204 77
    0x70101e6070880700c038035091020981c1208600c1e900e100e00d108502d02c0d01d500162050620030311580c4080200e074000c10a582c80e04000c00700902035001524004d1090007101005d00c1d505a001086801f101c0c01a1241c90411180c00400e1413000b003680a11800d9400401502001803002d106083c00c00e441004810b10550404041c0804211501303101000e10001c240180580740f00d1030206040564101c80b07543c2c8101803111241024010100c032074490f2400c1070f002003480c0c903400c02c500d419a040340c00c04111940d00e002c20003001d041d0603100c2c4070403480b0901c400c6c030101d82c013500c011002c50b90713074140c4400e081c1c0541d0380c1d64285c000b1a038512248860205061003140c0950090707103050003181c5400410000c10300251442e9118900c03541160f040005041c400310321058022041c1a13800a01700da03280d241540b40e540103071000380011886546440e0021620340760015201035190860460045004a9001400010708107003e0640e8510b04000c810109070741c803041418841040503001588940ca09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 386247329 1250 386246079 386246123
    0x6020310140a06020a081605070806090c09060108060411091c0c0618120c0b0a0e040605061e18090709033003020a09051903020a0e01080a0b04050c090103 68
    0x114240300d100d01d0b00400c0030061580c2c00224002c2d0140c0100380c203566101c22219100911403c08030040c01405422000202c2c00400710782c1130f1050f00490161590b9403d88001c214413414100c2d070380b80c041035124001c60000d0038139034440300704022903801c2d45107000c0204002601072141508505506444416000c0c01c00c15a1280d035001000b10b803c2c03c0030080218540d9203041d84285c050059a6680041501c041c020400c442a00903c00c405001e5551100c0c1c60001740160440c1030043d010b24100b8a0005060804100300c8400007242c104070401011031203000b000740c1d4400054100c0c1001c1d080400c070072965481250502035001a15560342c01890340c5001c04c614a1407034850b40031903218200307222072881c0c1001d0a4651501c036180040e50313082d4640040e10380e0b054541080d074210843c01c003030a4001031004c03140d4040d2030080f513a5020769941d0780d10301c0c400c05400f40541c800326042200342100140140708001d422030700c00c005650b1110213070b801017945080241d1065842110340e400d0304806d0020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 386248579 1250 386247329 386247359
    0x40f02040b0f1303120e030f07050105091201090503040f03170c1c181806080a0206071236080309030a030f1709160f03050a020d0204020706020310 65
    0x4001095003000d142088040c05400340c440c100001c04000104620b8080d41000303010041c41d888030400680d0040030800070b080442e410200d50103481000c004400d2010000f078040c04a0b10169a011300e02100c800c1400710489075841040e030703a903403503600d403070001030007440079002801c1406ea2002c19245907080c20b85450641c1c0040c42401b000401540040c1100031802c15051404109045200160b0b1380080f41c3d480c0403d800703824090120540070910a00820100800c1c035030036641400182d80742c13010b0300d403220b018200095011307404001c0440014403282001080704200e0804031b03026a15041c00084500140c08040c0c1c840c03010105124a22911190307100103002c2000c02181071452190100f56240c5c60380001400384650242c1d00c0359241d03c03a00da040302000441406409078109020202e640c2c40c1c2c003000f4410840d0240c0c10109209248154040880350018011f040703504d101d40a000b2020110b99090fa0481d0302044820b01007035603800250f001e41180101700810503d407519188038000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 386249829 1250 386248579 386248601
    0x612030e0901120803060f1201050601020607090501081305190819030b0d141f0203150d0b0a020307090521070608010f0302040b181602060a27020312041404 69
    0x6840801880f81031804034241c1495540f10001035039a4807420001036800c1000681c80c2c0d4400e503001c00b440b45100040d046140520403c1c0c08889080e1200380d800c0e100d640300c50182c41d0004181d1300001d2554030a17065a00c0349140580c00b61040140075840c1001c1d034a2080f6010360b40041300040c0e50b220000d0340c44184a0380904c41c60700b000b803040d0210019117513841169000c0d03c0302d80215584203c00b102446603c0c0c9041152a07080c2090303c0700c00740500650000c4a03502004c1240103040e003c2824089460b0040d2903114803403000c69900d81c1556802500040c2622003001002c55001c80c1d40d8031107100d0030500c4580d2a400304040030001c0046450080742da082001002110300041145c90060302c55102900c3d0704540210b0202d612901044c141c61180c96917052410039401400102c0d5180241041c1c0c03007a09500360351280e0f886144910503075001c080311030300d280d00c0409108000f0896001c250b100074402002c4d28818800c01e074100400f50400c1d0421540314046005c0d610113403419200d60100c202d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 386251079 1250 386249829 386249839
    0x30f0b011503140105040209040e0601060e040614030d05182205090d0509100201022515020c030d110909091c020f0a0809060c010603080703030f0b0f1908010612030e 73
    0x14440f2048190811062007014091a0003003991a850740d102d40100c0c07100742142044410941c0c0d5482e004008245403480d15000e20f25096010071502400081c588a01070080c0050501c9000000100e0301a80401c0200c0d05141102d2204540e60342c0d507003100715400c1110400c5424052070f005142048840181500303480c0d610503540b800407140c101e0162220007104880d005d5070b100c050b070b40a0380603108881c42c1c51b1542003460044041008526044941c1c039002c0c2c0d840c841500310144c00c80c403c904c254840901c480c2e00c1440000c9156085400c8041c019580002e100d00b0414400c0c0442d181c0803095031000d100e41c00000700301040740015031400c1c03060726452000f020004008d03888503454490190000c0c00e030382e0700003c03000c0b80c45c2c8a20040f1940e028124000300a041d90b2030400a12036040700c0b004400082c00e100000d000242c941c0106400020010951085015004100030040000c4400010380707481103040022000800c0c45003600402444000b0504c0851510f8000d1042d0b42c1044024411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 386252329 1250 386251079 386251091
    0x1b183f0302070303121e14070c0c050415080d020604061b170c070503160203070501030b09060d05010e150114010f08070c060603140a031403060105070b04020a030f0b011503 76
    0x1081d80007980c4000c40340c040c100044800071016142000d800640c6900303100d0039090743e5062400485600040d82c0d059140c3c0c03000d0702c40c0c0301e0540c12180e0540d1414090b00c030045500e424841440c0c180c0c4110007000310005103002443d41c6848081c100507070151100c001d038004004100a000e82d501540c0a200c508103a00084515041c1002c0d080c0a03e89201c02154207001d07001440d1848400100c0760115000030840c3e844001e00801281d13001502c1c0c00c124081c0c09664800240d5502034010895803040040030000f00b0317a944024441d103032400d41d405035425902c0381ca23601c220203020320010900641003414600706605000040d00c029080e1260307070341000345511018094a0b80300448941142451810742c4c0000d0050030305c070018007403d4102a00008c0301b011054040d40b0009450301da921301c01d484d9110b8140084103001032900044441602040c420042075001610030101c81c1e0b801440100301c0003e5a881c0d0700daa82004e0790f42d03c1c04aa070703051610010b010a40d4a5800c894805a20303140038050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 386253579 1250 386252329 386252333
    0x50c100507050f032e0305011803120507020c0a080d1b030c0323120a0b0f09010501030b010c05011b0215130206070203010f050a05191b183f 62
    0x1640719500598210070400b00101c2e000305c9022682901e503030071079600d0344082c0f07491a40069003d0541c1c40202c480350318091244034201c4980b81590300b42905501d074a504140c00403800030103840000c150782e046004103003070085180d0f510102d14000e05107010080c4030b59480404058281034480d044540041c070750944c171340d001990040a60000650614103091640d2140b0101c0b203007031100c40d0503c0b070380c1c1002281401e64070088841580c85200e4074030052255084a034144002d404014114a8100201100601c02540650049424408103260080b01e40304036441b034900719100707642c0c0184c3c03548040c102183c016604004604c3c80700d001c16404601414141c5100300350b103802c0d48009008041c04500c0c082591303400c2d4000b0b07074044240700051003203142401141000300000c0320a03552520307900d0441c002d0072503980f00c0c0306010b800840340c01440000028050f121345c2d1102c2c41b10742140e13504a501140380d5100103440d540c24030b4001c1c030540204040000300d582c1c401c040b09460210407803620302140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 386254829 1250 386253579 386253587
    0xa0f091406061902030f0705011a0f03120901020c0607060905071e090506060c060709080601060201020c0c090a0e070b0304230d0804020402090301061e15090b0a0c0c0303050c100507 80
    0x505020345a804025074540f0b04002c0c0e080d8045d809510b400444003007500c0d000c2c02410341191052292009008020800c0141002943c2e4080e81005816900000710340c4c000c681054014160307908140111144094204c0004800da8045102111096222028441044420008003014240306020019000b202e517440330015401072040301c0c010354460012503207545841048507001003038002525440c2c03500344c1010340303402458401c00d0300a10a0a0001400502c18820f603002d0340e5510340580103038a0503c080000170340e009080405015a40d0b44004000380080082c4001003003801000c0e40c491600c0e0070400c02540000c4141d20310300d4001b099408081c2c9000c5001500c180c42402d111509440b00d002103402401445c518640540c6040030200c0c80c202c07281d0500b0320444289080072919620741410310851545030265601003407400e01c040c800c0c8d19445024201c442d40d0341c51b00020b146036a8558000c20f0381c2649c0f041d1301080300002da1640a08052001910440030504280300f181000da500030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 386256079 1250 386254829 386254837
    0xe01110f24130206071e08390c09100b03010305100b01210207060e030f0c0c0604050f0904051524010804020906041830030902030601170c0a0f09140606 67
    0x3014000d0710021503200c9240748404242003900072040c0c41d100c81d103882c0e8211001c040100a0016103000091140803140c0000000c02318801c40009048000032000500c0b0640101910b06034101101d0f960104499800b4009580207600071f1006094148d1941383c008101c403014001581000090380c1c500308014404102e1b00d282c4501d41b08010398070000d506110008201e555903080660100040140c40e4000020190180d91a0301068a40035850300082002c24480c40c483d441e0800144a01c4143e903103486148a130b4014001c80035070f89140542e140c0303803441c014212211143d01101c03a0031049101695404001c540d4030a00300f542d154200b54001591554005021a103c0c07521410080d407141c406244d0b8041740c40d0b01071028051480b0600c8007602c80c405d9002540041c1c104035500302c07082c078407034040c2600f81c54000e0040c1c500b59081c905d40d20f4035807240003140107551180c0a40500652a41017000001b84665a0b401d020541002e00300710613502d2103d08039038014402e03410b0000c55a901c100711 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 386257329 1250 386256079 386256083
    0x17011b0c0f0b0a02130b091905090403030905160305010603171314060714150f15041121070207060302120114190e06130603030e01110f2413020607 65
    0x41030665800e0f01c030314041e114150056505510103080003408074a61009031421040441e490300d20841c40901d0560304030114170a4941c009100004100807a000c5d600446190740120b09484800c21880310100d180311841d8070407541603558100420500186031441c1000c659214011031400d201565140010205070242c2c4003251940440105941d48410842e07424660103071030000c092a490190540b030350100f10740110130054a07400560710000e88200144240c0441e126008540c540d4424840148003481c19071140c0c1000704011000107a29407046442140c65604c030340040d00d441003009040000c198895010316005200b40b103a95080210b4042c15030303841800c3c40c414000c00304c00081d03150040a4202c0c400224890012400c2c40310882214401d100540708000c0e41401d1802c0c0c501102d800340310140015041c1200c0340070540c4902079049240c40300e0011a80b000131040d40880c1060044070941564860805590714010703649074000703500101001180c15104043e4011404901c601000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 386258579 1250 386257329 386257343
    0x3030403030c050c07090608010b0303120a09020420091306080a0822170d0207061205040507080706031d0115150201020f0a0302090111120405130617011b0c0f 70
    0x442c50515110708103494814403010103e5455540c0c0e03021500040842e400b510745039500700099803102e424000119011142c491520724642d40d00c040100c40100105c0c5422a40305841c3c40880035404416001403040307010f4021216640c4400780200082684d040001b91840ca00301001000100d0001c60035480c01500020b081e0340d00c2c43c00d100d00501e10428441c03192080715505001041340340140042440d8002030004844004c0e0454806907520341141c400d620004004084800840c036880e00100d802a100300d088900e030300c1c3c88502d103a0030103180c2d400000010b540d5000741c40d0307428480344807583c0d0340107410004c02084001850600704c7e40028000c1d42c120b08001c0b4160141c3c2c1d4402d5040303662080943d1405911000d42d120010044d500030050385000905060b02c0300d00b040c401259003182494003414861816250900780803100d1614544443d045a581000040801c66400c246e000f21214100004482d445a840224a00d03030400704d040400510041010000740d8071200e90810a401a035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 386259829 1250 386258579 386258591
    0x61c0206070204060608010302130204142b06022205030a03050c190305030a060e07230f1b07120512072108070801051014070305091203040603050f090303040303 71
    0x80340c114810040020742040c9040700006516502ca083d0034160f0b80b0031a43c00d540c9407684c21403081030307020314017440d02e15141c02180c800c0c503031401840ba01c0c5200d03030b40b511040001401a402006490f0480c000342d401c0c680000f00204610000300303030040c40b5554420400c02042c10324003c00c2c6c0c0ca02901400500740f080000780c60015030810024020b10b000c00b40e088a08003622454003c0ca607410654000c01554106140841c0341c0101c821640c3c402d040c01c0c0c1c0ca4000c0d81d450880d460380d005e0241071003407030709620401002c01c042503a280140302c0103071198078010301c601c00c0a00640c544005940184560340032080303443d000403c045122001070a04010807a00c60619091203c8210000c02000d0461404003100740c11b400d4028071200d111307000e55150800315aa039901403040d030003e10092000080c0002c4107014410143c18043d0600c607000789002402c03c000e00010948101d2601d81204032984045001c11032140d05000d0141e000949001402150401c10092592404081c1c0001c09040d1564 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 386261079 1250 386259829 386259833
    0xc06110a15020f0c0703030504140a05030606090612010c0302090a05040b01052d04080c0103140c0702011107080106061101110708070b090c040213031b0605070b09030f040b21061c 79
    0x180035982c490300c1c0d44d0300303803003000d680c91074041d00c036600c03600c5401d001c10556802c044040c902401c04008940015020b0145551a941049038055006101541c00b502184030911080f400340f0070500ea411454a005070349a89000800254014130382c011032089003003082c80e08a599018064800c545001c030301c54165032485000100c2114081c104d6486410380101d070001d510000000e228034545401c2e2020030048440803407440380503804840c2d41c0742901d8200184001540300c0c1d030015a1480b800c0d0113a0307030055110028907081d00d50701c1d8004400a0340d882030403d4001e0b000c1c42020a0002d02c00c0109141c00c0c0c0c2d80d503402140703004541000d429130500b800010300580003448019000c0400910440d42c1d5101000d040c2c501c00014007040c3c40240403a1000040e2980c900d04d0301d8240c0c1c001d900c2e054100009580c6864540c036000304401140d01042c01026409400e040280c07014202c03400c4001c1d01e0b4945460800122442a025600c602e98001c090140a854500e240e184811100c03401da1207080581c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 386262329 1250 386261079 386261107
    0x15091c0f1103032e1a0f090a0b03011a0405030c0f01020109050a031e0206190c0c0b012402010b0a031401060e1302011b0305040905130b040c06110a1502 67
    0x503880d041114080001000590140351240014100c1c98440259540c5001c01c0e04480c0c5030001c2c06035401c10805c804580711142144405802c0f00141c1c42e903098904a015008524094a15400a108144088018024200d140700502d00005110040b64103082c034100001e955007400300341440c001c401001c007240b966407003034000014058102045a0801c0c01903d801080a803503020324a0140000f682280e60340e91003c19140d0287e0080030548042190380c443c21001172003074000030003c1c44040c084441c00034a48182c1140241840d0035400300704080c07078200740c00b2980760303000c400210791428100f0242c1ea907803403840720f0540303070441e4422212138010441180145002e8101407242403420302045040a1800c202e40d503014400c0c0e980c890415075210501103400c4d450000240826024031081c403641c80c0e51340c005607110148868000240740e280d12546240d0906541c256500c090790322040c0425030b04034418110350003108009100c007004a0b252226426151a4080d03e4103030005040c2e00d01e0b01032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 386263579 1250 386262329 386262347
    0xf0306090218010f0e010c0b0603150928030c0611040f030501021e0403020109031b0302090408090906241b010c0f030f0b09070c060e0f15091c0f 64
    0x121000c5640b50061481d04076081807a1450600003851410001da40074071070440c640314010180c450041810550f03071000c0f641c9000424058061050f40c403401c104541808499000346100c50190a031303950400c9149060400c6a518460010041041400040d500844024046400c8080091050903403014044039110700e90144000804801c00801030140650040950810082c18020194500004002c540c0520310002c0d001c541e000201300040703003070440001c071030980740084080b48036165400030f24100e40980e000c0d40c0c2c500c03000ca4403a80c01d04002107129000501210703010300c0300c031101e44800b060003501d15a00508403000f12703820306a161340407101c00400c1c608100078001483d0582c8000c0509481c14840c074002400d28020b40c200341900d2051812803940500b100241c0d07968400f040c0c540c0c244080301150a2035481c8441e0008000074801d0780302052418001d41604a4a180a0a5001c5c40982070b01c089812103526945820384403041d0a82011490504003103100c0303a43c40c00d41d10101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 386264829 1250 386263579 386263589
    0x30b0402070c030b0a0f0c050a02061b0a120204050402030a0f0e0615060d18031701120f0803070c1a06030c0303120601030504020109030b07030228020a1502070f0507150f0f0f0306 79
    0x407c00202451180c0c1140c044e05403242903a00715003055844d101c00b12000710f004104a00102c10412220102511a510ba1425402c00c01e40161400b40c0d107001207012131b8003c8612041c3c06da5220511180044c0b18000c214600741010010309182c1071440c4e00c0b0501d040b040e40058450800040c1c41000c241694000c284d21030580004142070703102c0b5040c058001c464010920481c0c036044400420040322140303d441040781c00a01030309040002e9611040990b02c050204c10a001d06030124400103181d207040c540344564062104130107410302000745460b260041d4581f610a810a00604080003401440e1a82c020024600403803a502c070b030700050b11140b04c250806880031006404000106400d5001011464007001c914440361504000040038004a2200880140c11500d41c200101c0c0c10380c0111030014030f88074801860080325039541443c2d80c032110002c80340c0380c0008004101218103a55840c404052078101aa41c54450302e07002050740000b140044140120b0000038050b6a1190340002c020b4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 386266079 1250 386264829 386264831
    0x10060309032c03030304120806010908030d0225050a06050603070e0c1e0a03020403202110020703170606030903030115020a080a0c15020a050d050a11030103030f030b0402070c030b0a0f 81
    0x4141b50a000d04c2540410564001040d0b070740700070550f594800c01c40035084541010240d404c0c505251100000b81d0f0040f0603990520039000d880c26038610055401034800c61040c4001e0656007150300c0c04000f0f4440080145100341c03c1200308100050b80059030583c0070030501c10082c2d0304c3d00040c2c0e120540782c0f000f000580c4600d002084120301290198014030543e40142a00c00d00d01302c00c0a4034000e00c4900e400c0c001e4000d00c01e00c0100b90400000c0e600720140d50100070550701d880e155410040101e810001003680000c0364900418a600a0b846040340c00c1041520a03e2039407605803070280c2d880c4010701c82c0482000c1849c0b078500c2c5183c4240440b0364071075071054200b50b654180000040c10006171400950380c8c0b1890401c5001d120b43d15100300c920803000ca4482c241001c00501146000b442c0050620000c262241c200c064011003910055010f107100e602c56281000c09030800404682c0702c0d0071618081d46c410000d03240440c5d0b0400a110440758440c00640617a42c0b40b040c584050404d0101c1d005102e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 386267329 1250 386266079 386266081
    0x9031506030611070c0812180102120a02160f080a02061c140105090f090714030c1002010c0206150a270501090221150d031e0810060309032c030303 65
    0x54032280300140345085c01a1030701419079481d446540e480c0d010005e40a2a1000b01b0441c0703401488142c04184a9040c050050301d842001a400d82a001c1c1c0c07012800000503000801403010b40d007110410b25020740034040c801d019103400c02141c2d603561540300f040a4451103002c14a0640824501c4080c000c0304a40c0d482445460307080c080304800080203006d082c2c4241024000500c83e51304102105206900200041070390744e1030000e98030322110380400c1d040c0d0180101d858440d415210800720400819040e4000910204580c030700a040c07200c040d084610155502450025980d140329240341130303c10148042920062424445851240c8041c10440403800c203400066101c0303c80d80940072400074507178113417254044d004c0c2d5180060412030314250500903146103039006091000d00500260300c1303801c211005e01c201410050700e1102d01c0340301c00d00040c0301030308201e100030340d00d0401002410582004c1c4003880720707031742d000c3c203004000561501c1e01c60700c0050441c003081060b00b16840003800a0140c0e81e403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 386268579 1250 386267329 386267351
    0x2120d240801060501030f140402090604090506040c150516060209120114010306150509010e07050702060301030605041e08120615130306150f09050403020c1e091501090315060306 79
    0x1a00341d510075940420310300000008441c07020b001d604d211000b4080341d15005c0c9e54560030000080d4002e00001c6c0c00c07a6032446d180700058410082a402079001e41000c45800e45004040d800c49400362240104001d000d02103c082403149080418a4503809500541c651410740c002c504061980c1d102c1e401a90b0810721100360f0019909003603816079000740c40c18081c0c41c0414034001541d160a100301034001418400411080b4241810aa0030994500d041442c01e4619000542290000e800940d9869a210140710801c1041c00c1c1510040040b8400d41084100300c0d100c0c100c240c010406428207032025000000e8117551060f800c01c201c550404034142e00c2e00c0d85011101800c00b40d42c0030480d03d0500e0414001a1103a40a400c0310480d024207103450346075400d01801d200500300245c001c8040d84600102a142c60340c1c2c4c0e003480310402e82021469030b0004080c10801c014904054620000d5140080901d49240d1780301000000b926080b1065918400301d43c8400c1c00204201c0d031028010318a85504088 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 386269829 1250 386268579 386268581
    0x303030207150b0112020c102d093302030a0204060306080c0307031205091003090318030b01050d080c10020306120c09011701020706060602030a0f02120d240801 71
    0x2000d0350207442c1c02c164104440d606201200c00380e80d901c0f4003045c892020490401c01e0f940092268081a00580f03d1022051880c10191414050001c0d0040150020380b03100f010b81c80005100700380c030000240692501d92703c0b401d44103446503c5102d151600d510341111110b607070b01a000301c5034240c13030340855407440c1140c101380003908070703015070000a800c160000800700f000103140d203036002000700504a003602d56901da03400b0010901c803010503c0788c00e0109181d60365821007008100c01045c1c0b0007091068580c60014000001180e04045070340604500380080380c018081d280c1941e005071245212840310b402c0c8803e46000d61300d14100e09110f02c3c4001c103044c00c0547c02440c050041500d61400f00328960005940b52640040c0854000e081c20f00100a03507805080e0f040151070080000514003031180d2500000d96102d900064007503807000481030311466110385000403079049480509940c03070704400001e44512403042600b409c41c0c1c66600708103440307610340c01070301020031f0b91000c0384221559060014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 386271079 1250 386269829 386269837
    0x509300c010315030b07050c070b0a031a0402160b07140706060608090708120703030e010e210c0604060506010908070f08160510110705061c05010605090619170103030302 75
    0x2400030342403040f071803466994500c0e844240c95100c0e0390f129480d43c83c41c504442e075400450b9141c84070302c50710600080e0308181d8001000141c0d03481d6000f08a403030307500340400d0f200186580c901c1c2c01113204200480d2a80310b00c0740d00303100d842e0b403000c0e01c0600340d1618201200e429622700010811700300005044010044660300040849074213131200c21207a6160f240c0240c03599418420a1825086183e00e5290400c2410041002501ca810001014203055001c20300312a03100c1c021a6079030b4444a034560311341d42d0080c0c0604054900303410321880c280060980d03139100c00300030707100611540e200e1010504a030f00512561010341407510071502c0440d9509091849160f0798840c2d20514068030305062050011080e103c810345001030700b0b0820419001c0000c40d08800483d5010509000703411011899070703509001407014a9542007114140180b9000c0700048400c1070b40400280641001600b0f910f44801d4151494404070745080c0c48001c880e1071003910b46801041c1c4201d5101003400c0040b04050b0554060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 386272329 1250 386271079 386271103
    0xc0a02040609020a120c172403010c020d0e0f09040b0103110f010903021908030d060611060609071d0303030c0a18060801090f0e010c020706021c050930 67
    0x180801c41ea280e040b40104c3c420440312000003200004010241e1040d500928000708280c50035001e241c1c9070881d211350395503050721104000d030407455643c40d1112030000a200c3d40c10b4102c5c001c011811210700302943e540c140b0314001c0c081c000d095401034603a0740c9050080c4011a00500301520781d00c0c080c40c0c00d07014414240011240340507000260011403d04040d04002104180c540445031800d54007040704005c2c2c52041d1000c1640348000200e43d8101c18406482c030020601c03404680603040030130291000c00201d007406050f83c0940d0401c80703203964100a0310341008080c1448500c01d130040000742d8180030060b4400b90984400010b200005070500010310103412555074284640805804d00a07406040e44a003400042001006200c4004e0789d81c440c000e40d0702500400202d0164a0000c103003500c08445c01923000d80c210f014104071071070b0140300e442400c800700301c444c44401503e010068494003914210a00507860f00c035040a008040c030f4020454844507012070741843d4445800c0383d036540007824038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 386273579 1250 386272329 386272331
    0xb18070f0302090a0e06121606020d0512070f1205070c020a08011802010f020a0c0e0f0f0c07030507060609020d0501090612050606042304030203070c05090115080603070b0c0a0204 79
    0x16214a500c01e10950310f44003001410120070324030300315043e03419140c0a030440d6845100b034480c0104200301041002c8a1603c155400e14160b0b02d407170800390818100c0e000d10004c0c04403c001d0b407807080e45c042c84c07070b11b03805903142c104100f5405620404540d10028802c034031070385d540b802080c080c01c0e9400000618185100303d48214030340b0789640031142650748907004840d090419904000042d0b0140880c83d1100302c0c1417045a260301c500e929401c0796066140d1180c070300c00c0e806805000c00c2020440b94a5403164002c43c03650018100014080c00034444d20001070204600468044100102c68000348003c1ca200c00b0700390f4882644c03c3c1c2090040030300384208000e59150450026801c559280c00a902079000005054a99128802c0c00098901c40341508500a40c0304120444030314261042409103001c0e900a5445074a41d1030290002d10380c2e600000d10030815040108100a58440382da06000c1e1546408101c0307131100c04c04071749011021341024030015804502e090342c600740020600643c03402110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 386274829 1250 386273579 386273597
    0x18071a0d0f0c0f0f110d09050f06090109030f080d140603010f0b0303040605030a06080601030b040b0f01051003020d0e060c07020306061005030c0c030c0109140105150907120b1807 79
    0x5140200c480e001c0a010206503c48456041c0600a8030003451081c0c050a204100040c0308100301e041c042481a54804203841410078816070800e00000c404403501550107c1c0b400e800100068124103140c0f10040c9149410218101001100b80603511047c1ca01441480740382c0300c8480750144401c0c01c03903800d030080d840c043d0f0b210340b0300d201740c041d96000160180140d450706050000407034240d0302c000c0076110056102d82c400240c0c22000c011543c001c0d401052410002e0070241303000c10352444041d02c102c00c8100d401006100c16a100c1c22100b90240d52410016960846070105001401c141c035802c00031030250908004032029040000c164580c401c80c1510321741c0d03803078501708a440d000c40104540012801e0000520030f0b01801c2c02010300d40000c80880b81441d100f1412a030075107103d5181110760740b0b8049070442c10b1400c24000c0b00e400c40810515202c030180c141d4007098000c1c80086c98001085090301c0344905141c400d60040314000405080c400c1c00100c2c85100072103155090710076800290081d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 386276079 1250 386274829 386274851
    0x2030607030504170903010e070b0a1701050108011401170f0621071e0305100f0f0c021f061208030f010501050a1b060f0f0b0103050c07020918071a0d 66
    0x840b41c184626404244501e0035035503d10f030383d881038000751300107905507580d00760802c40200200710030300043c000c01d08816a6541c000c1c00c002c02520b00e0350008440300802100500c4603a8025000d02d064038400d103605040c4030968070040350128081d4100c40340380e90103035092049009034480041c0c811001952202500e80741118045882207a01d44000b41da608017500601525400c0304800341803084403840181d500d52642c0f511402c1c230303071541d02e24543c02da0f5406100c2d910000c507020b084070600000c00100140c010455000e9101c000554088002c2e02920f031800030350b4581a807125004d003c4900211102d40424500922254415100c440e1500701c050000102c6611800460303c000e8119568403a1040784000c082507900070485048030403680302c8030b03054a044100c0c4030f0070700c40c1c03518407001003500011480050304462014001c903400c09400c104e04000f42e2600d009290300503195480001031600c260040354108040342d00242c1a011000c0081d03c40c0040c002c01070080c141c80c2c0d541c100210701c03840c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 386277329 1250 386276079 386276081
    0x31005041a10020a021c020102010905031210060305010605120c040b07050a02120a05030d050a0f1a010e0319110a09050c0304110613030305160203010f020d0f15170c040203040f0203060703 83
    0x44ea20007940118207403440e44a2000e002d40c514003561060002040c20b404580d95681980c01c6122130340150f609120403c00d00c3c01c8039144110040c9043e041c208030550402000410911038000d14001d0000b8020200e018840928100c0700103010b035411050b154000780c54081d0303c541c1c80074001d034440d14009107034400da0040810790000d141c1c1d1000c010f510700701c4c0f03200510f03002d045d0003072180044641d80c1c01c00c514010b242e03010b2030350f06e100c00c0320180024110020015003580310b4038281074040da01103000b90120882c07207400d001d04180c200103ca40e0405480d80059100001a00007080041c204400d01c025a15a07601550103280705242d41c50a40e0070107014082e03540038542a590001403800d1040010a029600a00032101c0181c03140b1a50f10440c0c0109003034030000c1d46541607403a40029460302c4524544951012841908414080b021805c50102042c808a0048600500c241c404804689030b0802c216006c201001c0d10035900c0b807400c0d0900500702540100280d01070f0281c0c20000d0392407482 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 386278579 1250 386277329 386277343
    0xc0c080115080d0f11010f140402101806050708070204150e0c030f0f0405010b0a0b0301080706020a05070501050f12012705240303130305012012010506031005041a1002 74
    0x100ea513021301d042d80c581412503a0800401c8100c1c80383d503803642103181c04820f0b07001e03502d1404420702565806050034410b020a4940070001442081046041003150b460520b0760001118042c0c134000380ca441003810440100c1c030688000039401450440e41c80c3d500740110703404d4011078501c550303241400c0d5a4640903070003501c8102c80d00c84030701e40d4a07800244101144540140c02c90f005000000301d9003c1503020038446402a0072000e10200003200402170700c601001640090181e5201800003184607941300ca5a0340340600070a810300602041050513170096105480300c0740c6240000381c0d52540e40b900c0961981d03115400d003000500b010044403c0902007401224040d21581d1004501e00d5524410a1079500c1d44508583d03040c0010080c001081205030b801c84040d41c0a9000021580318684040c800c2c54241854404c402c40284130b40b001508801884504441003620a20795940d254a500d0b640649190441c59005241900040d60071120a0032610a0501a03030801040807050b08142d0751654 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 386279829 1250 386278579 386278603
    0x50108010b010903083a05090c151b0f030706060305060a11030a0f02160c1401140f03090309061810030203150f45010e01090207030c0c08011508 64
    0x203003084102d01d60083d0114080c100100b10390910030310a4034180c846c1c401d401d0444282d00458a800500c6a407690a000b50004203100b02c56802804c3c800b5043c0085078003803204000c070000440e01c00c0d101c800200340101140368009000f03496549101e841e104c0700800541c0800d031080d12581c030006000792901c8c4160036440343e0f050012421750307480001101c00b07800000c00c00407105400388152003034089111029403001c0d1184a0301002c10381001401c0340d4540c0d1041f0141e041010241071500640e541c0c07001c49800005480d1460380d6540e03a044a80d03d14071503003808541041e40014801c0b0700c00c0061100c49900c1c003040f5115090307104804c00c11000e80c001036071400140c11025443d429a49091160440c4a01c00603103010880110075172410b80c50802d800d4000c585155504007031070611001100e180081c21640c0540500d54101030040c1c0040005014101070181d0000d12641458010105102c1d03131540142c4070250701d038031014264003038200c0d12481d900c4000801d5000c00c00c0000031418203a110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 386281079 1250 386279829 386279843
    0xb0d0c0e090c0703030b100908011a22060509070503160306080c0d0213050c0c1c1709030712110f07080307030324080a030e0105090d0305090a0b030109050108010b010903 75
    0x510340a41001940c3d01541046080c1950391261004585400040d0071840320144c0702c01024a28240489003980d014040743c0b101d04858003072020309603961411800c144c44101001c0040340c0504d401084c001c0541d030300320b65401030300e9408020100d070b440b200030341c031502d099180c1e60103002c1c008800790207550b0140508030842d000036855800c903040c6040700700d12080c0003c060400c61500b09140300e040b24001d44407442c11000c0051101e0652908000c0842c04034a07000c0428010002c2180c01008407150303c1480c42c60070301e02c402242c206030041043d50400e40e0081c60015403049a0b5201500005510071042c0b01ca014404c24124114008150502100c59900245180c503140e0b6038120010900010f10050355003208094000940060783c5080c050031440c2c004004c85001810b01400d01c1c050f00e94400e040080030054032100792924440000516807505140792103003000c400044000310300d40c0106040070008000010545a030f80c000d40e0480d8022002044000500001111252507600014000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 386282329 1250 386281079 386281081
    0x1050a05060f0d050d0f2106030201110a03050706090f140604030212040602070b03060a0312030e0c06030606070303050a020d0e07030b100308040b0f04030c2624060303130b0d0c0e09 80
    0x25400b8150090038040d4520380b54803821304110019403404803419250187e5680c03181c0510031541c0201010710724a102c00028a850082c0c1e40d0018051b21072200020602034440900c0e504005c0099070060440758840c130400480494940003603a00c090032030382500140305000700240c0a000f01d0049406940080e8098024542869000c18840d40041d180e650000d01400000000c1644a551002e01c507507903560208100c44400030061400084240c80c1c1c1c0309042c10801d024107035032003400b2120120341c03506010400c1e90715026860700901a035030300722260300d00f45101a0040031020504600741e0748207240c0c400641e16030300d45070550a0002d000c01032015104100a0000d101c800e005881c540f605048564a8a500e0340d4490150f0907080d80015200701e03044054036009490304a4251a142403400100322001c55429850b4840031070880d0384558560381c10200e04c944d00c0600c2161410448282058000d0750350720165106c41d8483e43c02218094904101000241e2003514a561801c0e40201070181c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 386283579 1250 386282329 386282353
    0x14070827100e0d14070801060509060a090b1503090c04050a051003241b08091609091704060c0b0c0304030815241c0908040b090a0801050a05060f0d05 66
    0x80e4003481082c940c1e0040032408490001201c641d210304130808500d002d04582d514205280303094030045d40180388607810120030040c030703a11a900c40c07004441e04c00c0030101d514000880814048850750b4400d00080100004014000c0350005410380c0f80e0000703036801c000956500d48502c080701c00c1601e403041301013410b80d0104003150420742d0620103803544400c102c0c500c15211928030102d84160b043c03c031a07205403540049400d070b0040c2555901a111001824064602c245034450f0200c0e80d00500a160ba9030340004000d02243c004210344804003048001d56680d1034140c0545540011f0b1000c6840c0701440740000d400380300c0c80c8141d9000c2ca0307040c0c840b1450380c0c4661101c50f424100d14070314690402e05c04540c22003030100040f000f44c040108801869a10010f4004001034004102100e11103c0d080007581030020301c520040701c040b5104500c0d03481d195804400000d10107102ca03406162158240428000303985d031a940214001d1600f143c240191144950501007c0c503810705000d801c50704844c2801e06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 386284829 1250 386283579 386283587
    0x6030e07051c0f030215150a12030f030e010b04020c010b1009030507031e0510090203190c0b0f04030203150717010303050316031b021e030c030d020a1407082710 71
    0x11070078801c1c010780300c2056083c1c1052041c4502203c291120302e61400c1003001f58103281000201600784482d07070f807d6200aa49004c0c094040344100354003051781d1500150070b246029031000c100b0710f0780208103655840170084594060002010701e5231040f18031f0510004018000e102290450ba80080580691032a6071100540200001e12850648940301d01480c001003091210a18444255000241c441d00c940180340c500440c00e094451000b9680c0d208a010031071000c5218111461088030503910704103e50b50b079005008640c8025054442c4841c0c50b4060444180c03524401e5a5542da010302004003500c9007510000c00307210107008a0b104101054010f9039104220807031800c42c2c1401703d010041c0039074100c0d580f1114100c481c016000703007180400180d0440c40701c254080c61840218207228559080a499100b04012240e8082c0d00080400c11a03000d0180407502124105203642c03100340e1410410b4166100c440140b054000c00441c4000000110013524440d00024080b09400124140e060b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 386286079 1250 386284829 386284853
    0x709062c0a0305030307020628090f06060b0318120703120e1603050f01050108060f040510060b1b010e03030a200703020a0b1005221506030e07051c 65
    0x10a10080446100032030740321032600074000d6120f40010345e074030f1610b035400a08003100a840c100d001086c2ea840013200c9900c42d4200e1701181c000040010b01c3c01411719003140210170300d510040c032a500b4080c0014240d4903120180d44607840c034440000c42c16032800700d0380c0d0325000d000e0701440c041c02042c44500f01291248007007100e064000c0000041c4059020600d030f18141141e000c3c192814032800040c010060180110302c001b80100000707010325418051219240e0100610700e41091805e28009070500030100581c8a0b0088982d504000f030039140c4a5008540e4480d01903c0348203080600e00c50301d002d00520a02c180020380303038060350440d16904100d902900c00d105140d00c1c507260a000d00039100c4550001000540c1c420380061028807541d01c0d059801c40d0004008003040c1d500307443d040265458015200c1055408140c8902a24000203403100040060302810300d00c5078500803000c00c02c0d1790558880c2c400f00da05042201d0a26a4503010403030969003640c0e01e01d14928918042e0717800030342d2084401e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 386287329 1250 386286079 386286137
    0x20a0608040818040f09050d030f0504080906070318090c0e2e02010b040f02040501090b03090a0f30080c0906071101020102040503030307031b050a0c1b0519030b070906 74
    0x45500204010a00140c804803038007601c054029943e04001c0caa02741c031a84014240b5240c0900440c40d0a0b190400c042c000e00d100a40618400074040707082501c80d03008498030503c44204085c07919226910358008000040034034000c82c100701c4c2103400502d8000d40c102c40aa42d00f040110b028000c3c40111004c0090b48000c040a41d07485808040065849008008400b8550100140c49a20b84000145100380562040c000d0309003c0003800f43c141c03400702d8800130b525004101c01c101d0060078540403101002c0750780d2140703540c010448440c200360442922100240243d41e42c00650f600d8100701d1045030320400158a0380a01e04000000000c1c5811201090444050000600300350365200480e05590040b0382d0900081d82c0d400010129916100080c0a29044d501d00030b82000c140b0880a440c40f4404400a403211030690b141c0400000105820700160802030680702030520001c00c5140021400e010803500b800c00388002541d100c1c40740e1501022203400b560b0745601c1c6a4042c0149864210980b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 386288579 1250 386287329 386287331
    0x5010309120e21060613060602150c1323010504081518061006030c14070201051821010506030a0c03081803030a0c060c020111030105060c0a1202060103020a060804081804 75
    0x30f0211485000d2031000c80c2954040030b00340f00c0c0380007010030246085c00f60311840410b280c0802401000d60004401c162031407040600446910344207140403c902030101054507032111804080b810440700000680101c0540d1401030801c1000b10042da1203002c1d80c000e6440e2a40800441c0416078001e40c002138204035541035401070307c0310504105084c0b80d002c0724043d040c1c41084104100701c3d60b05200d000c1400340c0502c0c120002c140031400c440340d14419002d01034100280030440401141042c0c0c8441c00086004103000980388041d50b03c218041c001c0d55003c0707455440d00380094180e040200d405e9620507803000e84001c2581c1103648003007190300300107660081c0400d05075488140e61001c0004080309099601c0313203500a141c0d4034150040d120303604d45080031641040c030803400c40d0007a90140d07419543c04803140f6807206030b084d440c14a0012074100140000004042c000e540c2074000c1000c9043c0e0740283c2d00c90400580314a0203940c0c0c2c8605690091121313031308100f01d0003045540005500c1e02240148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 386289829 1250 386288579 386288599
    0x90624090607020a150207080a1505090f0105040b180c0d020126270c1f0e0a09090605010b0705190f050f06180109051e03090603091605010309120e 65
    0x108401d2400c80c0c01c5405802400c1783c02d992455010004070004000801c0100882082a0354440c080300c11240c40c0114191190042061408103101070020788215030000c01580c0b8060419800c51706c0c058895984a01c040b00074010007120200e150b40c00e5500c05400c150890115a00440300c444d90340c130070051a250050000c000a0a10400384c50142c0b20188a024510114030304485841844001011203588591074001098880052190344440b81420b0b0700c400b0101080d00350b502c400e0b440c180960106280c0c40200d212803c40d406549164010310b403c202c076a0300c51240d00540e125056000c5d0803680f108640300d85550010b00c040003054480c0d09454030288960351864640100310341d030905250080c108001c902c840310880c0f850f84240c1b400003401484000e0b00d13000e4952800321141c2004228258010116240070012103200348406048a6504d00d4400c2e165a10343d5451405807a041c1030201d0000303910340c0319000360000a50044520580d410310180c2c2036494441c003941c8950804483d003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 386291079 1250 386289829 386289833
    0x3060510080a0c0f08040201080603160b031603020412110a03060219031b0905040e030c12041503050417070204061809050f030406020607080a0207051b090624090607 73
    0x80d4410104403107440d01009810b00441e448155070b90a0a22020000d5042018511a40c00b100c01c0d80c101d502030034901c0054407164003107030500e0082c0805400d0308659102c00181400d09100561107140c0f0551790348084141c1c02421800e0384158820310507040f4036a40c038280414955038441d020158000c00d980701d02507803a510b0304260381112180b21008090703244400c80658050080000d25071210039203150030b0070500d001070410b100500980340035940d90004031945440810441e8804616081251014a0341c449032092551150040d4628003105204400d21540a401400d00030350341300c903a0700b02089140c1c1104016411407001a80c0c000c0c1c0300c0d040058a10070203100c440c10700b1903001011802604034108036292089104a0160a41c400c000c1007011560100d00b45810041915240f80c40b41c0b250202800a8020b80c503015015000742e075810800d0407210021002c0c80d5609440c40103880daa6101003041c40c1c210401c0b54105201140c04c103620313600002c801031414103c028907141c06c0805076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 386292329 1250 386291079 386291089
    0x702030f160c0303120f0606021b0301020c011805100c050304021e0d0b091204030809012709020307172502100504050d020c150d20070c0f1203170403030605 69
    0x2540700b903004c80d020017410441e0710344c0c41c0100300040c9181c4500b484818903020b8029a90f0b213010000c44464039401c0d0808403503550079011116074421102c0240701e1080050186000300701d288008407031511403598015000f04045c000c2d03107020343c40e0b501d03450308558484c0c081c00000041c0c10010600e00d544280a05c655980302620550700c10b020b1003d00c2e150b85084007045142148083e1b1401040300305003c1000002c8842c03080380c0890b00700f860b10b00031402d100801e488806c00340c03455210480715040000300f09071110b07a020354402d001c0caa0b12400518040c2e5541c480240301070303030309034030715400c00c004208802540e00350081d010049104440c40061441070b4541211800d880071500d40e00308507003c1c0c0301c8a50400c000320b900f078001c544a0b0b21040e075a120403840d82c0300d4204020202515601080d0005508080c40d039101c1031000300d119a1903c00b40b510382d94050460141e8242c0d1400b050010402400c0500c1c00c51003582c1c140c84024500f0810059485c108500400441c109900c6840110745030300c071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 386293579 1250 386292329 386292353
    0x807090312090f05060c030d0b040605030a03030b010216080c040507050f040803070614060d0f03050f0309010c080f01150305060303070c0605041514090f030a061d0f060702030f16 79
    0x242d51031540e5103081030a0780100740c00030f6020a12a030001c0c000601c0d042008011904000c907213140014601d964a0003280c0544101d5014960500424680d5800d2540540048e05508026802e1311803512401940e94080c0e03006002d034a40701e60140800b032000d4181680495001009800c015060084988090040741d015030041482500301141d0b0408000075030281c01003a800141c56140f035441c100000c90184400d003034019000c0000c0084110625010318101c407010400c1c025465917a01c0d04009841c041c0c5682160f41001445c4c60000410040303035400d01130306803000000d60f6641030000080c103c003c0d02d005440d10368180010094400011503152084c002441c0c1612810f480d9032400411841c00202c07d0520b03004c0c0014241c24011340c02d640c0d012200da00c1c02c11241420441080c4001c28680540d24500805940c03804180d07940ea030303c044ca030031041a0481011039021400c054142c07520782e2019214207000da4005c0c00181e45038074600c0040c044040040c10103d9601ca020b480700446804 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 386294829 1250 386293579 386293613
    0x213030b01140a0f0605270418140d0503070e03070f0f0e180703080f070c0b0310090e1c0528030f09051b0f031e010e1c08070903 57
    0x440c0d1003080101d0305010a5100044c602d6121049007186030a80180580c403488090001d21000039002250410a10915040f642000f8100300407418800c0c031032507580311130f8030410f4070307200448007001c20303a40c1001486440a03130f01640c0310750640e04c4a14041c4c1c0c10701d550019840d81070162020100d1840700c1081644014411040e0160840e0724020114118040c042c1440315401d0307004040000103e800104201102e41c84088680e07114100f1001d21903500922170014240300c08404005070304810f200146000d464030290341c6070004d54840d4884122a2006448a41034000340250540907103000009050071104d810100d181c48198503105840da00e914403000100051049121b15807503140c811010b208001c4102084012101e0721020358179401c00582000b414500560175106403159001020394480c00390032a402c185031a0b4030940b04003100da400c03540302d42c81c0020300100e82c0400242801c45640d40d28003060064000d070811156040c0041007034042c0300341c070700c0c000000900c0a404080d07402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 386296079 1250 386294829 386294849
    0x60b0310270f050f1b040b07060b06070317010501020318120703080a260601081906120f0605060904080a080604020712081905010b040e040507030237030b01090213030b01 75
    0x442d10580c00740c0e04420103488580d0307610698041701440140e201c04c88060724035408207070391204490b00d06a40a0300d2500240e58000700c001c10841e0402d90030004ca01c515140384074556140741c2e02c6000480e40c80c01001464070040d4011442107c40f0b080402c22840051102c00c00d60759080e480340c48203c4c07107600082030480051146c006074560303040250500b20342d458001c000b4216a00700b0f800000c02c0c8090140c40c440231860020b452040f284000d80c4084000c14520401c018640e1150428140005011406480751824100051414501110010301c00d40d4000501410058140800c41d4010002860aa08941d082281002003507a68807040880200c0d9582c07090285000400c036200e529031a9801505a4182401030190404000aa800351051005c0d600200d50b41c40c204903291007215407000e50400b0741d5040c0c000041c1c00120b12014004012209030001c1054507001145042041c40050501d01100005015400d019001808401803401180c0c4407262282c41d00b5807100020b0307000825079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 386297329 1250 386296079 386296081
    0xf06130602220f140f010c030e0117010906060801140d0b07050909010f080f0f07150905040228020f121614011e02031003020603040c1d0406060b0310270f05 69
    0x3404101d41c40d03200710041900c1d00070280140000187c0055203980d402410b00039050410b0080d64414001d04824520070f011414503540c1d201c0401000f00114015030001440c3c4400100e20003100e01e110945512001d0081d096641c070540300c0a402980140440c010040c0420080902da903a01b1500c82c041c00049055010140ca84290580b41801c10b100c2d0f40010342003491400c1140c400454444c0868030000701440c0115421070742114841502e40000b64043d10114144a01d90300f201101c550307140c0c1d2083c21171f01c4588d0140d4140c1c0c1e40c40181510004503801050101020084079028100016440c0181c03004507071a90f60300c0c15101c1c0707048aa91074681d07486501e540d240c1c0c00f10720705402400f02418114650f040c41165a8496042400003174050803000006c02c003000080f031020002003480f54103804103900d520321040c8485000b50780075104982445004201011024100e13400360402c901d02c0da80700e900e000ca280c00c5183c1041c04034050208210b04c4020081942d009940b00c812118800240c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 386298579 1250 386297329 386297339
    0xc0f01020c100b2409040605180702012d020d0623090a140f091f09020f0402180d030e03190b010f0e04030305040c090e030703020f06130602220f 64
    0x200d404080f110351180012000d40c1e44800c2452010f640c2c01081c02c0503440c2c0d10070000d4046005058241e1080341c011b4102e4040180a6903540340c01805490380c0d50080c0070011000e40c001d120175a41b10702c00c1043d50004000e00f040440036600810310045400c50100d0740315502c0c042220510503c01d1024065145006111000d180c500d19090340000408810400902000700e00681c0d041c0c000c000460b1030640501080290703200b0000031201d19004409100740c101d4020700f001c090202903d0803400740550260b070381100e00e49802a03070180c43c2980e070903d9813011090104091b0029a080580520040e5400183d01e07403006d01c0341c84020b2060300703a0039460f0810b41c40d08225046050b804516035500780340c000d200c60b48040b0002c540103a014580030500742c4440c140041c5141c61390b805846040e00c0c101e003117800601c0c044050a00b15000e40c0a840da10958080202d4503040e0413240d02c000b51421025010000b403696002d40034240800e070030003811401c6601017030400c1340540c000c200e051f2420071007001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 386299829 1250 386298579 386298581
    0x20d030b030714040e07030b04210f08040303051512010e07050402130b0d02041508090c0102210c210c1603030905150705010c08071b0203060c0c0f01020c10 69
    0x60400001d50042a510b45040348060b40f00401d210018819a2200c8050214440c10003c0d44040e40d080701880c0d2490400d407a04400c0d0061411001420044400c180001075002e1f6080a801d50000d8407040381d01c1d503556908500800000300340303c80099016203000c5480d01c545558145030300100e8000a4884010885e117403401c4140d5122601c10b0340104900e04001484290090490700c945403c10380759030302641e600000c0e004681190004407255200172452031341c000b1849010301c84010542d05000080401262100100e6000400300c10a9030a5491084015001060300c006001c058901600c403660480c52a109212420380b404100400e141d40e08500920404040903040000410f010386160740c003916404080c46920f20400e035250940e103040b22110202c4540541c804000c001043c540d010181c5070700c074182c0703c25001411040286a0701c40981d140519099001401424540d4403006e0005260340310040d191614003eaa010860090007400a4a0040c2180f009007040340f005500e0300c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 386301079 1250 386299829 386299841
    0xe10060509011503050705070f0f02040c0e030a170f0c0604021224060f060316201504030912030c1b050d060c020c030706080402041523011806020d03 66
    0x26204070482030040105000c0c90702508600c1d03000f800c0c08070341507440c01d80948040c0103020000c2c000b6000310341000d0400a207140007084092084804000103040306104440c103246441c4240d426070301100c7c0060120b00f9641030091034203083c988080c41c1c40d4040c4821349094000440c440020391040c0140000c40c5001d0702c114410092020003403030202000383d500681322000d1404004000d80507008200d80f81c45004410700c0b851400307030404ea541e052031907250344405046000c14001410312072540c45102c00c6800004101c624210003071482d00101802c840c0c00290141c0110140920306400058003001e81c950700f00030034003e440d0088402c075181820202e03080f42d440f81e0a10551290710a10041c0d81d0345580c00307040b41d003241c0c0010383c40704486070a91602c2c00030780d01158184120100014180c0d0b101040c2071042e4400c1e41c082c0198a020700080c034441c20140590540d13446286000c0b4152207101d20580c4880005140121140041402d0803c0d046500e03000034005030001c45002d000c86030580544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 386302329 1250 386301079 386301089
    0x30d092901170105040b070f0e040501060806040f060807180b09091c0905150a020a0b090c0f0603060906010c06020d061202010e09010803030c0c010f0606090608100323100e1006 78
    0x3805240b41690303c4655009004121f00c09202ea0038031031440f0f00f4480c00507000c50442c013400400403961100320151040c02d003110791511440c1071814808284440b80114021101d00b48000c3c01d0751418840c00000b410b0b14240301c20040c5540b0005141e059648d401c0c9036000321040c46c017030030191000c40c40d20701003803011603840f00a01255a808004c1a101d03d60885103260341100d41c130b9190b200d660f0b0100d00303008800c03602410512000382400a440d10205036000b003440b0885070629400440c5040c040c16000480d1501e500c03101440c0040d9055002d240347c08801c0d8800e290052a03c030304000100c0c2181e0b1a0381042e1002c02c7e00c3e006860031075811140c0c1030380700c0c0011660154907624180c000c598a00c0001c0400901210100c2c100079940400d41107481c03502155001405001d848079070007815003c442c0700e0742000401003008030b50442d4058869400392034000c060000b502c11203440c1310000c2d03514050030304c1c600e104411035520b951131180b0076004075400c02070241c01309100b044410420b072a0700303800c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 386303579 1250 386302329 386302331
    0x20c031902280201050a110a0c0f05041416090807060921050601140a1205150c1207030c0c05060f16020f030304140c0d0507081c02030d0929011701 65
    0x14520b01502405540b40800d41c2483c0c01551181e189404580c1e08920300f03804945032103070360314503003c10070b50140090655019030701711150181d0705e50411041e903140c04106c0c0c0c0300c09100c80100b000821400c0024201110a08040c0c400b2035442c9511407800e21541d112100140c1c11000904c1032000c80b11025044081c400752121008416495154a0b20018400e1020600c10001c1f104600d071141004500140034403005400d42d02d0342401c095440758902d000c41602800d4580c00100045ca4501c182c40365416003040070300840c0c1d513503031003503004000b010000002e10108a500400299040142502c12000310490b05000d003055000300b402141d14003030a07001d40d0080e149207c003500700042900c2d07009800c868400003400c00101c15034141b8410001c1250490040505c1c0c80c10b0110000781c0c0e03002c4890240c2198000645000750103004000c0b41440b0005800400a03043c001c11141c028030301071400fa20840142c2141c0c220101000381c1482d08120759070703114000401800390609100c2a0168035400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 386304829 1250 386303579 386303623
    0x170c0a030803060d0606051908060a0e060c090409300228020d05060405060411030a0c0e1503030409090515070c0b0a140f22030f050904020c031902 65
    0xa6503094034007000300b0081c0608058005002400501d0f080300001f044094006031070004071000401c1c2448140c02042c5440c803a84000c183c60b01154852962076080c280042c010a8170b80856140166002c00d00072030b4410b454010180103d8000540c403c500d03080200c042ca520002c08041a4003803002c102c080055402007200710340182c10039100d011032008042040380c070b044158400600194915180a801886803804100c200b1900040080c040d502801284103003c2e245020191390310130000004107840c0e40d0040c1000031041c205900303601f00301580c180c0300740d0749050008249190080d5114650705500d51608a0900405018901e00765a02d0019542c1c1860b01c11400303000785c840300100601d25440d000004002c0c0525070700c0461088840c0d00300a40c0c3d030038203070169580e00c0c80980741802e06005011307108000b000e03080c2401d120729a1507150b8a001094150054a1541140132142e8015408018580789460f080c001400d210001c010348441f00240c1082c005e103044286113070200130342e0b9000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 386306079 1250 386304829 386304833
    0x20a0314070f050a03020d0204030606090b090a09030207060507140f0d0f1d0f060d0c0302190c0506062b05030406090608090309040b060904020d060e0601051321050601170c0a03 78
    0xa00710b1310340c59001d0a000d40ea501c015039005000384255030001c1c0c827217440c0c8040459680699040b41808140440703041b5425103035850315204403900088018050382c400e66041100d980184083d25065001c0c082c90400c1c5440921401c2c00d000d618401d01203550405109004996000b0b008422116580c5c50b002c0030540b003101008404400d207140341fa10651050750f007410280d880904031010040500d6007032001104140c0302402940080750350784580c4110094041a0300c3c403444085c00400c0d008002400d1503120313807061180040301084009156261a40c800070f42c0042151900e00503442500215560307031400900400301c54082d04040c0400c060304051202c04071000040e03031000c05088500180500245001607440d04c642402c40d40c011b400880e4072403000c03a20b079002c4000c40e050a243c4e05902d5030b803003004607a80d00c20314001e03548640701701109101c10544801e6016480110030300a51403400651205890410240c0c820380c4e200300042444400001c042c00a0450007801b550300b281268256 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 386307329 1250 386306079 386306087
    0x1305011a1e07051e030322020d02040509010b040c020c0405160206010b0a02100603061d06101208040504110a1805060f1c0e0307050c190501140c01020a0314070f 71
    0x6040d8158540780c0460a00c042c031200f0711010f100b003080e802508115403c619255a2a900221101034080205105040710003485691008003154010103070846020720754200002800c0107800c82150359681c1c98004020703103ca20558221040c99002070901d88120001c200c03d66000034001e00110032914000006650001501030555003c2c0340b031a034844010420481c901b50703180d210030b10494200840013090110030f510484048540c07100031504505900308890f510641a0b41c5800b0004d29041c08000003042001174101e144d12895000346082ea0306e00004080e58010101212442e00c0012103248891704100c031001481d9015012007160303403800001406500600c00c4401d070209000078211328451760507410411400c01c819080000c10b602e5018a03a80e0b400c041d070126800d11071104a82071500c0c041100034190b000d0380c0e01201c1c241d8200310044414040d004092980074100340030300001440c0a002914148403140d90000741c6c0ca500000100032510003420400c144401d2541c008003c40e80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 386308579 1250 386307329 386307367
    0x7050906120a0b1006030509010c0819111206031009080d0b040e0a03020d02010c08090304120f08030a0f0b0d02010e09090a05010501030b01090b120c0910051305011a 73
    0x10440301250030354000d103115420900361900041055210341c04101c140740d45054542c0c2070745c1803030b43d081210f6035900c2c030f40e9400c076102c2c0b405c0580400c0313490780025428040044195500b410420010442e50b0f080b18403006590000f0054000d03160701ea80c02c00200b800e04010344e80722081c0991081c00f8910003501d824104e4492811010640c80e00c801000d50940c0342c58100c007030720502d42ca00300d41020300d103802e0094580044042c00d000550801d280121500d101b25a03090180031014061803900c1e00d42228511114211241240c0d01850305840303202007080440a1881005d06030320218440f501c55000904a0705000304003803141c3c6200c480f50000d42da02564000c207a2000b6200100320b40c9032000007a29181c0d04c0500106150300b8200084200010018854102d51802c8010b0206889500801a400005c0c01d403d801c01c3d0300c050408040c62601ca023400303400010070b500a851003911400403500090b2500381e24000076850341d00410080418801c402a0303456100d8046042040c60440d020b40066 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 386309829 1250 386308579 386308591
    0x809032506271a0412030e030c04060303080609091207031e0503040f020d020a05040c0c0218010501020303041e0804061d01030e0709020c031909031106030c0a050a0e090109021308070509 82
    0x2103418003e0340c0205180304490240200006409907544545002000c812000d441c4900a0040c82020f0380715042c240102c1e401d803070303164542080560740d80c0e080c05401c42006003041250720a00080c0b41001c80c9100007461800e0003a661601e07001e40e03040b1410154901d1021000c00c00508004102c04159510065002680d0458022500015900002d0500dc00c0da07049503600501d44442d00c00b9058010b00140480d80c401d0f545100c2c21034140d00141038100f000d104050140c0c00c100000741c0062480a243c0c3d04019461100750460300b015151000c41d5041a0000e80224240320404251101c8002c40a0310f544000d02c0d062008030f1001d14034a4540c0340c00e11600b103c407500800c1c072185a00d401e0003601c0700458144103c210550f030b103640080c6044100d100990b8404140b5440d9155810400c0c01c4032304c0f07960182e0340c0c1441c080c65600704440d180c0c4070742c103910104101d0144810f03241d500c01040900a0a00b440e016807109007004440b03c2c6030742903a100503403035403103000100725079121140303101d40c00f00d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 386311079 1250 386309829 386309849
    0x80c04050d080c070504062c0708070f020a051e06061009140112092306090d200106080304051309050d1b0b0a021c02070c03080903250627 61
    0x125060707143e45000b900e034000c40c0c1d01038100a4049400c088448241500c02103c109144081c404544405502d02040e1101c60000351800002a40640942004503051a10340304892000a00d52120b40c01c1c107c1ca60100801c80c0c0c5c01c4a540301c5000300c00c00006405c03010440d5400e0780400f503070740c02414000d028842d601400743d66810300005c980c0200c42408800f180204140b20124507807411881a6400101c89502c2c3c14bc099006682880d001410030301c0f51050800a00ca0642c81102c181c40341e07140341203c840c40c80007031003404e10415000e006180c0144280c5006503103030782c180ba041085c078501c2c1c4046000020f2511645101240001441d0310742400b007400c061039010002480b420f68400f1001014101107484000e0004540e01640207110b0210750b6548914548851041e040580c800c80e000902085451042840801c2503040180654000102140d000d1000f848018607078010382020110a080b40700c80401403e07401100286480c0000818102840c6c1281c144282002241c040d005603d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 386312329 1250 386311079 386311087
    0x8010e09060f09010e060114090903181e0612010611160317091207140619120209030106060207050310061505070f02060705010c030f0e07140a1a030106080c04050d08 73
    0x24100a500240c45800007400740c030055a1194043c103101c000502303000380107000e11030004001070008015640f1000341143c0c109441500e03202008002d0402080f864914084060b00d400166207010040254100c241d9003201158034180001c1c1c0384d44c2c0741030521410754104d4141b14001152454000c41502c1d480840d4000f10b4480504510407805004200c035040341d0719010903180020b0001e510003c031003070b6109070b151402e100814418240581c10b9080481d000c141143e01c0c003980075940844510200c4400142440300180000742541e070650b0101c805a04402028807440c00c00388802c0003002c51a00081c003045180030491411008103004100800001050781020000080129070041d600100445e848400740c1c100b060003401d805580c81c0210b490017101d5074001040b03009000c0e60000500c050701040b464000c040302e04001030a41c1590001c007446001c21034885400d4880c440c11440d580d01501e079818807501404a60000d031003800000c0080c04100016581c80e503a0701342c0d150348061402e840d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 386313579 1250 386312329 386312341
    0x120b06030609340e0c04030c06021c030e010b0a120b0105090c0301030f03141207030c020c030715170106050a14091507240b0102010f0e030f0f0f160308010e09060f 72
    0x10100f4580000346200031001c01d00880c40d124030060700036130f800781402003030850b6107401c145d90b03503c000b8141624101c143e050000600740290f01c0410040918070001c41c0c0c0740180000600281c2d4a80c0140b0f8090b94025501e20500c500340503400c1c050b02c0280c0340c8000034280503122080c00d0205102c01000c0c60643e004000405104100f2030248041c00301185844070b881e0402c11000b85412900400068945143c40030f45074800248006039401c094040c01146040c0988071951840c002e507800140468440c0440100c441c190440e4020442d6136200303a200d0758400001000c3c1c1e040118410404d600500205500e5a50520514040b10105405954400c3e01c0d19046c0c80e41c83c0c2400c50003030052441e08580100d1280c90700b042d50094400d038020026070095070900700860300540c0e010410b550042c0010080800003030020303c0f21404049009041c00112800112140e202c10a02001350629090130820190000745c62400750642c628011081c2c40c00d182510b135207410043c8000c1240800e4008941c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 386314829 1250 386313579 386313673
    0xf01050c010221090303270c030a06090302060c03042111030d060807050409030503162c01080a0e25081905120a090b0d06120b06030609 60
    0x5142040c0d000964403074401c22428a03001002ca07078100c1807548400002040d261000c0203c9205034600301d0070900f946e01860781e004003200c0c0c00c00e040c0b4030352181d00c11a0b00507a80400c400801a80b04800204104070145002410914040c00040d2074010510134080010654031b580403241403000d520b03589070240108100c500c0720044402024a000000c0d11000380b40315900141d00b510b0010b021100c0090b502c2c800e1100710b13840000b014000940a2004c2810380004040031603040c210782c40e1551041c10307094a2080e84511203071404e84019558900f0182d070f543c00000042d400325240108106034000d41e43c91544800000c044078080059205070605020800c00010000d011041d08660884001010366403030714189040c2550340b8455499151088041601206c03007002c450381e6100403007440c0c03070603e601540020041845070358441c1b0002c2101c059074007201125600501c5040c140307060004c18507080c018060120921034010420075025980188030320394010091242101e40003004100302c0d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 386316079 1250 386314829 386314837
    0x305190501031115030613151d0106030c021c031e0204060c03030e060127140a0b01031508122217070801061d1503100f24050f0105 58
    0x494480c680300011061110a42000000e08000d403030300414162000d4030340255001c100c822540c004800004081c904015030004400d5020075090320078125160211001007101071041e2035249105440108041356150264182c110241e00103003644042585258808403a88149070051503191f2400000a50090840c580c8481c3d01070700031500c9549480005004039444401540068100084250500e6001c180c9e0360403a0ba480140c4c4415196000e00c0c03406240066400300480d0b5501c8070140c900c2143c9401141c0304581c0761000142000c0d20784005011200540c080380c2101c0c0b20310100b40030002000501c504d00d44910a48580c59480b0009400c0142e02108002c1008200321580050a0403498000c0455800c401003a521121f8403108194200c0d80180f18030361814000040c1e0072100500d01d10b20a40040c2c1480a005e00d003203050021034980384d40b008030509c031280c2c1c034070491100c14180d1007190284522081c130015000545200c0c0c0800790001e0013268403603008034400c00e0307050b07015400711 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 386317329 1250 386316079 386316121
    0xa0203061e04031d12010f0b01050412141c020c1f080105010503100b04092c030316050c0d08060306090c0f0f01090f090905010501061407121107091b050405060a0305 73
    0x85e043c1c0001e2854590b010713048a1110744119800c00755459540c4d8010815a0280d400390303d9007031380104503a03c0380841d416008400101c140160b80114142c4c00ca612801110b10400350010302e0351711190700c10310510244400b40140600545164854250b17844525141118000d28220740c0f00e49550000c4001c80045a00142490000240001d40604180c1144166036603c030264150407411045009581140111550030398004100040b010b036941c0c0581c5900789a0b61a10604025030050700c00c3c6418007092032500466514410400c0d00d2404200b81380d803010b90500078152061a200100f001d402c03a184c2414421a41820001d4141e441580c07000c00a2481546d0700032040d5945143e1402418440802c0e1025400c2c080046912400b8002400c80a03512031589498141c00d0b884410141911182281c108110320140345038560b010000c0002419140c0000148400183c032480c6040d40c0d900458018004280300c108543d41d102c50a40b03e405010303090202d210381c0c503028001c405241007031071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 386318579 1250 386317329 386317339
    0xd110a1206060503011a01091509090903030209030f0c0d030507020612010f030c0f0608010909053c07052d04060b09030624060a020a05010e0a0203061e04031d 70
    0x41041c050180c00c03100446905800804c64a010b082c014081d001403101d0042c0400c045131000c101010704000c0800e9070f803050f4075011442c5612020b1050942d00d65680a50010382c01281400a40c40d0034001000c1a0001400130440c240c004008a680c40303d00c188082c050200104490003035449001c200c800000d00f00392001c01b2580c40c0c4540c0c903250303699800f068603039040ba020041002599035421600b520b14039151520660304c1c080003400540b420403400c490714001c030215451242100c0262103010070b00810141c1ca812441104c91a0620030700100020380d0f0302c112020845510303806210b200840c01840e031008110b02d110320100800100102181d0428500240060505516806000b114804809650441e04c40329400b00500400d110501824400006064403510309500240624080317801602c1d0000d4560716061300310342c0c2461090701c00d900704840031411803906010f480d40c0804201c0400e0300c070381101300d890a0203000080004050204502c1040b01c8015003c04420641c00000c6c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 386319829 1250 386318579 386318609
    0xc0609010507020708070e06090910060326090f0108040515040503091005120601050d0906060b0c070b1c0515030d0207060305101217090603010b04080c0f0d110a 71
    0x80c000c2034111000d800500408402003a592004102c0c0d4003200c80070900c000068907804104200280054807030103a5118500500d1440c004030302030f01c00158010300c00f01c4098801c441c000c000c00d841079442400c0764038041141d0902551031080780e150950f003c6c41c140f81c0c595518600b6500c1c00c1c00e00c246054102d515030042004200c00000100018203099a400c100382890150a8a407801114041484014248002045944039401406620705100004a071041080d15400101c0e01140c00180c3c0340303d000100343d00010400c000900041200d4000326152501c1205850a4001030250208030355440e140440c011100d032482802c0c0e800c10083c2640d2205260110195a0303040c51310401001c2402d00001072030201102c000303402241d0024224007000609590b904500d0000c4143c40070346064280481d012548450740598060010550502d680700e0403c410340d480c10410703e11180c8a410880145505034544006070845190300400d0b1003000070010b40060165040c9800252900c4801c1d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 386321079 1250 386319829 386319841
    0xf0624030403030f0204030f0f23030d0c050c060109050c12010e090d020c0d08130b0a121121040c050402030717100f03081303050a03030903030b0a03020a051003020c06 74
    0x2200940c02144030391010400740842d5900441a40114030000c0c0000c0642c41220740070600c102c02421040740b007000991440c0c1002d200c0c3c60440b032060202604030740c1c000710750b000142079144148160440603040c054205000400300664444050241801c2e5644490106000c6001c032010b558503101035106c452010b6848450208003070b60110b50b0003003103128880d210190140045910580707041c0140224040002e15214200705600ca00c80c5012031010f6514002043c10301000600508a819a030b2140d81e24031203440788042c3d4052410f5070031141d00812404039042d503480581990300321400300f600081d5550341014a84c031001303684200e801c10b00000402105650011100e40b038184a2610705049899100406481f591103010b01030035040f90ba4014004600b00390301600700d441c20103030201001a240d540d00340c10454801411408242c50312200e00030542c02d4000c81c480d0701e00942f03c9480a038915000140005158419240149101c25a00280901c41d03012982c0001d207000407100c1341e051003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 386322329 1250 386321079 386321149
    0x9120f0509090c270109061b0203060f0405060702120a0e060d05010f0f06140a05220e160804170306010201090803010e10080a080a03110403050a061a01020a0b0f06 72
    0x2c802c0d88420001c00030b48500b40c2100c0310845400b422061b9166855a0309210096130405001040d801c1c9500101e0000001a0340400c41c99100c4c00c054801e5030201d04103803034000d240510240845040d5080f040c0c1c0b6001c001d41e01c100740c52082d0300a18104800007204808a407091080e2110340e000c140c00c00001062400c0801d00c0d120881d64180400441242d90384412201080f15406002006a04005c0711400d030b442500541b44010b030550742420050a4015a071210704501c0d40680c540903021410030860f40901844144060568109885645866543c03a440b0254031007014805030030200128070142d10035400890007540c80300a2a549503103c04c88034a41070000c80b00315401e4a0503250119000030b0100e59502896171203401181007101e07201094024010b902d105400074036043c40000080380c0d0801449204500859000074014104000c07405514581403503c1c1c1503510038080c01002034011442e856016400409011480d00c80750001403a2580004010700c0e45850b01c1072265400144d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 386323579 1250 386322329 386322337
    0xf1201050f160f02032709040b060f0108012610060f091503021507031224151d03031905040905060a0510031d06070c02030f0109120f0509090c 63
    0x80d16602200100e4400411200d42000303004000040e00240201c0400c44032425000c2081c0e1200031b8566400d40044012071000b1108440c1a41c0c02c5250605200345c40c10148941c2c03400000c20f1800750b009604000305c000f69609101000b00c03210400b4644000d80000900420183d1703d2070880500c1155520f8903e0b200c400c005003d005070403440c0208140c08050305a21400031203501500c2d00030036402554201c95280c21140b001e40c14032071004102c0030020941e00c2030407640c14649102d1440c09c42d9410b0116440e599035080814400c00130310801c0c25640c0c100311010012003103240c1d041c00d07111804010070304600030120000c90070782c00302090802480d0404064002e0b40c82d1000c0c02c00c2541d4541e810003016403420310600c0d03005040d1f5801c0b0398299100760041001d1102d01041c0006200b030a03150507203417080c21505100051942000b26046142c00d00162400c41c082500078040403d40e03031980c15481203990007032010f20881344203201c1000d0141d03069840711480109810164030302462909000e80c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 386324829 1250 386323579 386323591
    0xc0a0c0f05040f060e0c0f0403240c020c090c0d06030803040303060612020a0905010807031404080c0f010e0d0e0d050703030201050f0a1407050d060e0c0a02010e060708060f1201050f 80
    0x403c0100350070a41045200741c00c101c8400c00e000c1c81494540445c603110b9075100d464484200d0400300404030108249018070900040c007440f44a511f0000065400b0441e00400510011504075420402d4140eaa0444094205074a035002e5603035141903a03004402400b6035803000384151004405c2005040c1c055122038100c0d00e10f03880c0c040d13424502900c03110882c881c074a41315002c103501003000e10865204804842c1e01116600f40003c80d4039030312001d0100110203c03411101d008000408031280d640900100d525038040c1ea00038030812403100c032416114080c2d0501d07101000b003020b0220b040b03076440c0d291304042290040c2c16102d00300d86900b0000e000c0e01d001c56400d00704541e030070f01140000e00148204040d40140c0c0d05100351540714494116800c0c0e214401d402c000c1a1236042c041902c8460244a074001c0700c0103041c590781e6149503c1c0183c29910314014141240c0c020380204070615800000c9190302482c100c40081c8000c1d2904001048603200c9034200545620304000c0008501502d01d91030b0041c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 386326079 1250 386324829 386324831
    0xc01050a0e01180503030c0d0212090a031d010519020109150c020706170a0e0f070b09030c04110a030207080f04140a05030d0909050c12090a06050a06030c0303050c0a0c0f0504 77
    0xf280a02500760b0180700c0d100003004e0798400c20005003283da508018205541d03130413101500d088124125408800070503601d000258208a104408040c0c0011034810030f111400700c0c0110400305100040c159000b140342c4440410003410b84402098401c0d84104d140e9039000c90400d41d03101e0340000160040200c40814405446420b0780414068002c005980212075034070684404c540e1500340c0035000c4c1039003110840062051003860500d400041c0404805482c581c0c01c1140c403501481c0400d8a000c0d900c3c0c0c0d075980614901101300c0160b401f600304441d98070259040250790303440d07076142035001c80c810700102482401000c00c01042c2c4542888510303ea0a40480d4109010b54640b81007580740d010450010b0041903c540341000344600700d40100d41e01c400d0b000d0943d400d002400e00880240351040f44c0c0307043d40b42c1005c071341001044003d108060f0030809003401080114119500c03010511518080034061090208414070f418034200800c00c1038035840300c00b54002c035545100c44880360034103000c0ca601c69 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 386327329 1250 386326079 386326091
    0x70305040e07050304120c0c0f1d0a1107020d1e06020901030b1e040e030d240b16081812030a172e1a0a0e03060603150c0c01050a0e01 59
    0x283c8228181c0b03004039000724002d1440302d500752041e100c01415070030465010301c042c480000e03000a149902c00050090100910038240b5415503144613040042030b6000c49460301c900c0348807080300c540c01e07164843da06803a0101e07402c40c14107001c41c1c07003800c1b90710001c02071044940400400000c3d8000c0c100418080c1c0342403000d84419010865614202000303001c0340030060b00c0708512868150442c0001301c40031821783c1d140151f030508000c162a80c80d90281c11142560580c0b02036040350340350b010020b1106012050030310103507161183c05201050409000c0400100d28034181100e4074042c02c1d6003650003402409150f444882c00c1e502c1c0e810072103114020520b045241e1024100100f20140b00399071010715001442408039095090300350042d46052149504003010a51910001403003501680012901d52a40c519000c010046e00103070354440c0c001d8100006002041d10001800190741000891901d590796621400740c403203000d48982c00c50a5800c100600104461030b601a10303a20003804024814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 386328579 1250 386327329 386327341
    0x5010815090d0c0b070c0611030907060f08010303050a050405130e0d0e030304300506190e031b0f0106030b0411030604030207150c0f03050306210706050c0a0503070305040e 76
    0x11608861801030203d00e0003902d040004043d1035190b80e014042c1c1c20501d0140d01c4036250501214104441640c00150000601c04e1f21141000301c18010611464803280d200c07007411009006001c180b0004090102c080f640b40e44050190080d640513103809450003028217583c2404101510181030f18008c9070107080d6030f110780c091140e800205048409401945410300d061464031100c20b0100301c60b05074000c14000e0413030ba418081650b590190088000700042d00345420149500d0b201c1955100c0355030b00d07004401d4080c500100903548502511208a41c1c000010301d15103040c510b0394207240c00203501e880d02c04003c03c03140114840c0540d000d648405010368905c010705a40e16070a4401401503445180c0030403e280240c200c010802d942854000d462451b2f0b41d4455100c21ba42500440101d80f01108100107030511a0070941c24600d0740c050780d0150b61000c0251a20b0b92018003c1e030040140005210a40d170b030301001a21007482d400705c1103079611019070800500720340060080038580500c0d4004621 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 386329829 1250 386328579 386328583
    0x30c121006091b0c0507121407060203090901050d02011815080a02120c03100b0313150c0e0d02011824020c18150901030b071701180e100501081509 65
    0x82da864803e80e00d07020070005940d0503130f92800c0000c01201e040c440d81c1c0012404e403440e094118035032482845244062601030081a040100d0758001004650007805403461561350a451581180c0d420b84e074854800783c00d400101d45100b41303400340e05244040f40d1000206075400109410a8051b1542e901ca601c1d25030190b0f41040e44101901025200c0004020403180000e0070025a0020749500c0110b003c9940e0350800c8180e50011202c031580d03603111002d0ba03801d10038103401c1608101c41d22102081061b01e1040c001d024006010100e0340560000c0c17090508590146408105240b82d107400d20300d505554980080d14440090310140b02060041c04003041c080c000150f00800d51001803041101080205e91710821060041c000540490384c00d04158441d221003c44074045d42c0218075041441c0761801000d40041e03038088820a1a00361704004001c010210a101000b0121400380440c98003070b1907101c17502c2c0032229103288002c24506400059100c0001881e03440040d03600092a00343e543c0c864601e9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 386330935 1106 386329829 386329841
    0xc11011113140904120c0804120201091508010b21190e0a08040510090e07090608070809030a180803071511030103050d0e030c12100609 60
    0x1000c82561540c2001401946841282c0c602c00e600104001ca540240040c105800c403208030101c0920130a0740303980f41c075001000d0301d440310303103e01e0401113804032140124041307500c20b8400507013408540319110391282240c4401e101a807810035810001c4d405920b45150b60052403000a02516803201900e01510360f8480f030f00c03428101d105100b0b0480b21103502c038a0080d441601c006000070180383c11a000c1c0e03017040e40d990820400341002aa040110781e00078070a500e0030807042150343ca070301103070319001c603090b56403041e0031502c030614103a821000a582c81c074902d8000b000741c001c417030703010301b031220038404044059a401540e941105421900030f900c044072444181d0b11030200f424070a001e04200c11110900980c603651441c1d8600343d440d03c44024400a0003102000104030741da090211950000c0d002d001140d0000f0542103e0f510b43d94034100000311946070800105001c62988100 = true := by decide +kernel

theorem cover : BRFrame.Cov 386151079 386330935 := by
  have h0 := BRFrame.cov_init 386151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 386151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 386151079 ≤ n) (h2 : n < 386330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
