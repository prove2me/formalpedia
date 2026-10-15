-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:27.346975+00:00
-- url     : https://prove2.me/submissions/f3e892fa-e95f-4152-a9cb-fddbb11a37f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 747661870 ≤ n < 747841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 747663120 1250 747661870 747661883
    0xc080d0b210f03162301021303020102010605150708030622060303090b03041e1401020a0201061805011a0309120d0507030b09010b0f0309070302030a030816020d050711031501090603060b060405010804 88
    0x80c10f080c00350720045c0001e80c3c03040c4007660010860f480c00f0200a450001100d00c00d8000b00f0086a0300c2061181411818107140b4044a05100c0f01021070240c900540d48018014000f84034100ea4104940c15582c0407200200060707580e5034284105a0004070ba80d002d80541c40c06941149060760790103030506c11080c0c0e06d00c0c604540301e140d00104485c0302d101c3c070100490000255116060804c0c000e00900715441164815004c50548222412440c81101c0c181d405041000c00100b080d5030141c002c0d07600150551026200b5410b454011003542c002514110b00500b4010444d402c0c0b0441c02002d45151402580c40380c0030807801007120416000817940004540b0403910713100d981da008001d08103181940040c0d0540541440b0a0400da030029030f880c03241818080b074007240c051154041703958050b46448a0003055041001a01003884840f202c484c441d4001c04641051040d0b00b040c41c3c0c612070030b0b440203608a403540400d00801c005806103070100d403415036410741040d1070074000800d0414041c2c00074100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 747664370 1250 747663120 747663143
    0x6090909020a181d0c0418020306070f11120307030c02120a0e0d0602030a090314090a050d150f0c0e01020c090103031b05010612060c0f0c080d0b210f0316 68
    0x200300c00d50700003241640c40707141e40c04c0655100481d26038480c0f4140301524811407400199581c980c440a0800c1f1000b80c01070024001d81d80e4070ba10a46481c141c45041005100090a000c420100c00f0041c0710304079204403074a13079240c0c240b0141c0030342a1208801070744190f401140304ca02c402c50042c4d0075154405c0f01840c007402d03141595030110380c803c0460b060241860f4000820040d4190b640c0e0841d0794000d21aa407030303912428001c80c000066005070358206034000d818000c1008186007052110901a00400308104072100200d81d0b14203ca545640140c0115280d00000942c40d80101c200c0141820a001030008841c1c91400114080c1c01404000c06002c2448621713404180c10f6031341e4021041d40030000f041502c1c1c5030900c400c40c0100040040720351600b0a114060ba0b40d01c82d400c0e50030740c6081c540b0742881e0f202040e5100400303074210320a07810305c140c1d68404010256650817058105000b400d0741140c1c00009000400303003403610910160100e688108500148449002501724116801c40c90301902c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 747665620 1250 747664370 747664409
    0x1409061f170604020108060d050a060b01140a02010e190b0a050916090209090a0c08241e090a020c0d11150f1510020c0415050d03050406090909020a 65
    0x40c6035200c1e04410300e41c0101500d818520346000441034040c5000740c90f402d0103070352800704011480d150100d0040c17060300700b001d2034400201c09d42c00050f507160b814104009401c40307140e08825a50072003001000180e4451701e5030f0350701c040c090010040070020304900c2c10340d0310005d484800307203850080d01400c03015595500040c080e21091180b085000c45080a1000480e60303410381101a40001004620860138032021940300c0401c0d1154490a0069460326007880e540c403104144001020902e20100b024442d00203507050340c0d551440107401d511058070b114802c4502050080d0544d0042030340a84501c100540c0034241070004407002b042000d0714001440c0c01c480000c0d90300b080340508100c0f44c9000c581060080d403118000001d441598000c1c508140c0c4118501080484480076000c1d001680122800c809181030039005462038416140b044c116481d03450002c2130403800c01c03560039400214081814015158041294402415034843c1400362604640025020040911501031000740d484403400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 747666870 1250 747665620 747665671
    0x23090a08030403110c0102010c3501060c05010f020c0a0b0a0609020414180402100e0409020604080f060f0c0405090421051305041103010b09030f1b0103140906 70
    0x44195032180340d503500d03070900d494040c1511600700324003802c0340104880000039510510941c2d004040703030395443d40410328000d4902130038000d4681a126001c56a0051040c071080002a20300030116541c6204540900b4108942100c5183c944115400e00401039000e807505c000401e1010307640c00900c5a0b01c19202c0c401d10070018020740d030145544900100303002403419000400c3e413000000c141d0b14048040c180c60038512101c10111002940b084808104a6220340b043c11041d11b2107101800c0041c4004079a00041d54030340181d80280c0d459030000c01001076070307002405941d1f00309004c1d04082007641800c2006520502075802120302a0904d04000341c180840440c02806840724440d054100301c10790040200f1642c003040061040c0c500d1003030300061505041c070880d00c10380440c00c411401c42c0d0908112403541d030b2001840d180e05200c0c0d00c5d0b00343c040d100203019034401c2085402c1559041d13805000050141ca040d1011120044c00031010800c0402e030200300b05a202c00601c0b44000c0d00341c03d072415007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 747668120 1250 747666870 747666883
    0x4b07140118080606100305070807120204030203060c041d371e06270b06090a091b080f13051c020609060109090203030d0f140c0d060602012309 63
    0x20000c2592110001400c014081015130003014251002c00030300004140c25801d407002036400900040b0864000399030039206010040c1c0c60702e4202c00140c50321369a500000c0c0b07010403d4801040d40f1074000b1b420080d0640640e03080c03010407a542c01d5984185082610406a22100720410001c468400d01c46010401c0010a086858a86900c208903503070664803940040d9080c00c0320a0b1904d842c06101091003908405109036803212004d200101c600b9025000c0082c00c40c0030001d540001050024001c0d4bd96440c9082001c4c0108034030015210b0300f40c625140042c0340c565100e100340183c401c14041d8098030008140e81c40088a001c000c0f03a03288518001e441d040004070705107a820500300d1a06555580816590b0164600d1000c56809980740c000540c216107180c1e5000307625501c200300090f4042819000309082600030000001d500d05250a44054800b08461214034038400060030189600d00c0d20810000c0c2245100030058000100d401c0f082ea034200152040a00c0e800344002040140c040105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 747669370 1250 747668120 747668147
    0x30a1e020a050d03170619060c150606110d090e0403111f020c10050126070f030305040315111e040302030a03230703020a11034b071401 60
    0xe241d6008210700b0000c1000b94101c1743d00c4500490760020a0b07280ca0808403600c46441c00203c0120b280d40390030420f64004c400f0380e00c1100c8010980b412100c3e00145882a103008000caa220003244020790303040071782400d0356540e00d0024050580014091410815000c43c0e129504d401c2c01c2060b4500782c02c007180b80c440110045450110380300c1c0d0f003505400345900a45080440e19040b2009041c864001005a40c2709000e001410342e540390902420304060803c1d0344500054106680d4000d84900c225802d48506400c1a400300300009402c00800400121807104100035800070812100301101c180c0551244140e402205040342881e01038001101d000c540003558002c0c11100b11501d1854050000e454151490021080c42d811030300c031111001045030041685540603282c4581c59540d5906082c400020720703501886445001004003079214003381070004082c50f0604030340b01c095041c10b4071904040c3c1079aa200d02c1c0a103038444600300024000c0c26209903090324164250100e00485100c400c0683c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 747670620 1250 747669370 747669379
    0x60d020316090b030601230a0807030b01150201020c07050f040e03030a051005060c10022107030509161a180607080a0311090907030c0504090e06090c030a1e020a05 72
    0x440400810076504220454003010018418801000d00b010f86800b0244145400304042d0168001340e05c411b00101d01c81030300010000310f000f070b403911105458405950011160742c91603400601c00324250160508c2864aa40f0095103003203600c80c1900d48400307040c81082c0c00f9501c0e1140300c0706165070b190400390110448100300d903120b01d000134640003c0c3c9010380d000c0c848040460340104050a0101c01c56010308041001030071415002c4071a00000d5016000221815401e180100c0c00c910320404a90700400a5a83c041428240171841d40c0c10031050218148820040700340420240d1500b018031459828080305040d26035010b51a1010100c002d01c5080d944580001001c500700516400a002c20380c3c010f81c0c08000e102791869903c0c01d584511524640d015051000051405112390020a221621440c00070308042e03a4420103407d5805501051850b2340004007041440c510411000d07000c3d60088004183d4042d164a03100e8852100500031410000441440001d5440d0211848000e00d4042e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 747671870 1250 747670620 747670633
    0x120403050a08150d11150d091205120415060f170c09060a17030c0105010b040f050d0308040b090f030d0c0e2428030204140d020f01030902030c0904050c101d0108060d0203 75
    0x6403103500501602004503200c40f52a03643c49d030003511420540704506000c158058060700c561300c1e03100c0040c03d452a51912503844410118086501c0d120200c001c00700da04045242807110400389051000a262040c0103100100410456a40e458100800c4074952045001c1d02d43c084030505046208208108030a5800c142c00080d02c0d41091009004507507510160b00d68076600c41007000561741c069003010700044c291801040200301c1e0207840b6604020108200d079002998100c14900b160015001c1840096960050320b001b2504a000500892402c50748140d0680308402c2140d000203c0c0d400d01000410089554520004040c0998001028522400e000c10380c518138014081e5200740107000118048150711521030503e58500309013541c0c0144004200391818004600030a12064143e81c18410301c042e8000301c0d10340d0784041d4082da00490240c42100c5c0c01e00140f09041c0c907900034400802c5104580c10400e548150100440103000740fa1101c4a611003c0004102c40701c0d480c0301079414050314 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 747673120 1250 747671870 747671887
    0xa06140c011103010f0b031b0a0c0506070e030f03090603390a0905010309020f100c17030106090608070f0e060408031c0c0309020f040b06120403050a08150d1115 71
    0xc401441c100c0c0c64805145e1380007070f100c580685560005844445181043c0d010494000190801501e66100d0034a4034140d1a201c0da1a003600d0a1401d80e0401e003c43e4107040041042c1c2014003502d0080940d480041d880c1c0010350f004a40544001000c0302070301c0e000742464103098050507060b043c000c14030402c0c0e0780141e0b5040000070303c29804001080b0110f113500500081c69402401181e00303580d0000e21524840d5201420f005090410303418810422034107001e0030001990308110351003039500c8001155201c0d030500710040d14281c656045402801201c0040056a607840764201c1d0220000e031500003003d91980000c140c107070240d60008001400045080d2020b10b03000385608000030320948040c031400b034a515041d4200c9904050180d00f0040c0c06866000f6402c054004d001c082a000e0070302450102042e42c1d51050b074070141d03000c40c0018000501e4140107544150301035001407540d00030b8021030104000049010080c404000c2c002c0210421400041e0340c2c0c1d00d00010034224554a1170740c0c0c1e0101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 747674370 1250 747673120 747673151
    0x1614130209030d020607020c09060612180a05010609050903030129090d06050601030606080c04140a0510090609140f10110304081509030304030912060b030307111e0a06140c01 77
    0x44600c03c1c014410a40c41181515009c030a1b2805814058040c519040c01c5034900510b2348001050580302549803140082a503900300040d48455000f080002412402e200b15102500c00c0504040300c03035403060005014081c0b000c062240300302c1d00c1d14602840288242c5480c07040c0d01070f2a548aa002e120403910300117004850700311922510090380c04001190f1500015501c0003003e540710760300c3d128144000d00c04200800f40312100041e0040c1840030307882d40d40d40011449808414042c00045541104124144c2c1003404c02c00640845100c240c54440d40d0408aa00310801c0500b8038480c0060700c40410380a40106884560360b241c400660396a140c841c0710b12903031441380b4100f24040c0a44540092510b441c04400d580c061603041d82d0307071111145450300c076071689901c1000c1621042c3e5217010340c1c200c030b03078041000740700e110710410412181e1072841c001c00010214602d2000d0b03203c05c0075001c0e03030019640c80c101201600c40c64108404550320206441205011320240302c0c9440d803801c0041000c0c0c292 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 747675620 1250 747674370 747674383
    0x28030b1008012402010b060c011b0f051c150b0301080d0201020c07090507050f03070905090603010b0906100c060920061204020616080a0c051614130209030d02 70
    0x805403102464010311040c201c400039001d12440c00b111010322151000502c1901820340340121902c00030405252130130000d865580301c1016042c60369904d8500007540801c14440c101800c1181c03e04502000c84900f002d489440392460001da03402c0c07003021442404100d64010651030070440951050207844022642e205c1c0c4c000c0c020300e5480c0c0304400f025544103105000326451014903a003d401c42c0e03850710201e5809800040c02c03007000e210b400e000c0001151103c0015500c140380c9a0344038800d1500c2c090601142181c0988824000c2c0d042200b4a800340e1510b04030143c000304241c1d561080d10900075000c03940071054042c020245402c056441c000e000519000b040e000c480201c40240f84000b001c2046078510a150380581a0560f80d400200580361607000341c12000114001111001c000d03039504071595100c0440500803a06180c518414490108141885160810203800c4441c0c1020000c6a141080c481c10307502c118a5060400c4545d0002e030180d80c80c01102a041340c05080d540b000194480c03a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 747676870 1250 747675620 747675641
    0x16080403051207200327040204210201140c0a031d030a0602031e01080604060e010906180507171f020421110a0617131b030b0a061a2803 60
    0x113040140f0302050b10010017100e080d0000c8210041d25040b402c1399151508035410081540285d092000140981d54002c041c01c0340040c20351130322551089880050409403424002000d40641407003041040d8500180f03074007001d501410440086050141c00346d0203a0b0844880d15014017075400071208100f620340146000c1c641420108061042019100c0400d4209205030002940700c0300c00324020503180d41c458800c02130b9600c001f0403051480d899007015180802c1801d500402803010070414441d040c420703038000d0140784400580d01152240000d2303807105203250b022041482c0c0486c1000549107581101c0c01030101c0c5aa2140840014030b000211080107031045e86c0e01040906d00b0301c0c0502d090103024003565045d88500c1000c2101c0500100120402014200040058640d02000c28811186103c06200307500d501d4400c02e003185081356410001810f0050160304020042c401c2e0010b88038809204440c0c207510783e0312230b286100e002400960410028020340180b003103594000c1c0c0d168005541e2203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 747678120 1250 747676870 747676907
    0x9171c0509030c1c0302043b060307090c0905041a011e090303050a0c050f0606040b0402160209040302070f15031107020f010e0411030a1401060816080403051207 71
    0x19550992219200d1040c2c03403c00c4019005000c154040d480c0e0744c43c50b00c0c2d4180113440c0050405443c7d480c000700e00012074032644201c440700c2c406d801c4400200c100e510140d02d00c80c002c15409040c243c0110342d96400500681c054140c40e50310b4001510710681d44407004200042041c0700c20800b100e0100c0302c0441c1d031180c0394009485e003021043c060301075a0903071041c13481d0381d41e035102001e2442e28119205d0700900e0341da00402c41100c000b180031410410180919468802c040e041c0d90510004000442e07011400d101d01031401801189601807400c0c081140060b01500c08254643d01c6240880c00c05485401c03010980c40468004180841030780d80310b142c0c0400b583c44c204400c21450403002c03030b03502400c10000d5001e40781071200c00c00e55206000100003070758050000310300c01e405c2d900f80030169001102c070804032594810f11441d1100505000070f0052030340b4100408a82020429140d003c0b01c070041c0d041c10f0100b410042020184240200c40840c4280c40403803565060142000384510b0081c5441901d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 747679370 1250 747678120 747678131
    0x40b0f0f01030c060305070302041509060815062703060a050601090e0c1e0d0905030d0f0e0304211e0b0f070f030e03071a04060e0102070b040609171c 66
    0x62991008400c0c1070b0380c2c101c0c600c0c0e00e002d480c00344128081d00c2c00900036410582c080c440000c248007041e0f114a90b00e4540e480324901d40c1e007800d01c0103051002c010403000e003001d1807000c860025200c1000721104070400c0302c103c07403080080303901d04280030203409200794151060b0300800800300f6580e4407480c0a0f5500341d84101c0059601c0d2040481c4101c1a0382c404000b18040100b2081d800a988580c80740310360340c0034440e00700010f015440084418035002542c0c0c076000001c0000030355200d840b40d1f08210170000c0c41000568406040c40d5a04c1c017440c0121550360f04070501c003007821089004003285480d4050445645031803000e010344568206040204d039480c902d030300440c0040c0d0f1034107450381c807944180e680d604030040507603401c6000d0300394603c7c005118081004110082407030f041080c142252001000006410145070600444460a12120083c0d1062007003100041500d8070542c2c20540104010544180c01e0070702d49400740e000b03010b54903450360004051104488c2050261440314500c1ca04202 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 747680620 1250 747679370 747679381
    0x70b0f072a2106050108030a0201180f02060313020604090f0e1c05070206070501050a020910020c0f060f0910020c0109050d02030c120f0a030201021b0c0d060b1206040b0f 75
    0x114034800c80400c034558005048248002c1a048035040691080450b0700850400700b80c40d80c1040795001e81040809030400154000915024051178030050411008078950304c07026213805d0341c04464840c0c000d200301d20010105d2180481b1082c1010100c3e001013005550f5565002000001d03d14111a0841641061100c4505490100c1e200c0d41440245ca07a00183c40c04082c070441c1c442e84521404ca030302c440140000d4000c0340d424496140301e1301030800010380e12200c460800014001d4444200c013150b0000340c4040c41511000d00d07802410740300b5070b14141c0760301820064298034094004800d0308902040c0903000c480c0d80c001042c0180000070389400d9a565107070070038070480100326280650564042d440c00f2038941402084400001e4460040c0d0307020f070440d0307568a4285040004c0a40040c1c1d0003240748107c29501192500303139040c0040c0141540c4004002007410b0350010400500241d43d20300c0031440d1611140d8081c812281a0801d0314110f18141c940000185c8082d03032135056407080d1500068 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 747681870 1250 747680620 747680663
    0xf0807030c0509091c0c0506090d020616051917070206040b010504020408031209031e04061206121101090b0d1e02090618031c03021209030913020903070b0f07 70
    0x140105914005000170000356289912074580b0f12850904010f2801c0c00310b00824000d000c3c1c1401498018003800000051a00080c80e0072009000480310321030b9400d40c8000141c118080304d49450a041004020f0101e29400b510303c10701a00030583c010011104100e070040d0b0118aa0740700d1442004d43c0215a62030f042070200b24015401600c100e94800c121a9021052404041c1da0100c5071604907494004040401403244000d5141e1503132040011400307010351070308440e8030084500c82c25401c101c418580707901c800310341c111158050700690a00d4003182540c2d2144464001801041c034240d41e948400a144e00000d043e441000e80080c101c0804214155119000315201100300521007801c08000101c00c0342c131948007010656044c031030104113a05d0010101445022f14410f0349005803508a03009070030300c0800e401494101580c000700007004660b681c90203030700300306443c100380161070b04010742c00300e49021400d400060584001041050300c3e0b0710301100030010184135a03014020700040100d8030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 747683120 1250 747681870 747681889
    0x3031806020f031204060207050d08250804030e0a090e0d1806050f160b070e1e06190509030313081c1e0e120f0c010c26040f0807030c05 60
    0x9034503e4200b082151145080e4007259078001d030003a20010310b050516074880e498031082d040c40801140e401001c01c0651280900b41e20014440d50218010080300c00d1001084494000c1005080c00100d038004825501c0c2c0103c03c0016004ea02020802d9603403000e500c0703070b42d501d03100151000981511a41004040e4191072078007190311039280d090034625400b074000c1c500e40146c079402c00895102528a0b0204d00c0f90b0001c0b03030048445840d03481d110640401030007040040e02c0c02641000724607007024011a03c0307000c2140c15082820b0071f01c1054144444013100c0030311440c644540e142c400440c101d4110000b01c090001298000411501c00c181101e403010300040d41c0c0241400800c0c0035015150a1944108041d10004011724050201058400014012140821658560780d01c181c01e0070400c5001000040d0801d002403c00b480703000840d54444488000e605800c0220a04800f111a00412400c0969000e4540400e019290517141d030410396071600c2c24482940d0207680c2e101c0c002818140904030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 747684370 1250 747683120 747683143
    0xf01260705060a050d02040306020406140c060c03061c12020f071a070303090204140114011106040f110d050a06050c18040b060f0d050a1d031207021203010303180602 73
    0x340210500d01000c025a6401c964000c0d030601408208a140808a5100800c041c600c20325005031541d040480040c01d0f00c0960f07142a61100081003940f280650028090740d115504001c0035a0301d0381c0300c801240c0740c03a03501e07585944c001c030048958004224042684010025a503400c1710100380e035012100d980c4258a00c07420340e500c4400203000c1280900b07140144003803030203420082180c031341b168045811622080b10f1090402d00306c10041c8466010842d20180c850000d00c1e00100f9412142d40a0752500c5010700001c203403000000e890400c100b845000742e20580c0008040200c003080500b0800d80310003e04004894042c81e100000e8000200c1c10240c0310b1808001081d040a62041014000103009810050380c0c0480d0034401440302c00d0901004141080c10104089510b0502e060010181c0701c42140002c2101c44200c800780c060080041610784001d00c00340244244e490350768080c1e00b0f00720a010041b140500004c00442071607081180c1c058200f0706d02081d00a03895070341908a03124240c1584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 747685620 1250 747684370 747684373
    0x917071113020313030509030102370806031b0a0f08100e0a0b1807090c030603020a05030307020d120c050d0e1e0108152701030308070c0f120e04050f0126 68
    0x1104c007091065014001d4400701500061502e074004030b1800c0c03000c1042698000c42c1000401c60b60038120300a100102c43c3c1583e060640940c240900000d445000b002e04214141210a5040c01e181e070303030200164010701d0281000c511440c2c0b80e10750741e03880f201c00700000601075051092941c0349800004803818070b95004454150701e03840d103180c410042c0c0d0346542824071502c145100030890040c28410704c01c07804003a0310001040751562041c0082c0b0307071441d03000e107101e50030911000000d0385600480e00b58a560200c0b9001010251800a4603519054500680310740329081c10307110200e8200010980341c1c00d0440300312001108044500d000c00000052035800520210003081341c4114009030510702c100010107032124403c00c0c00240c44807030445d0014140d031013142001081411f40101c07640750090b215103000780c1e01c4401510369000100f50314500501240d0b01900401d0118801c1200c51280c40d00180248441c1c2016140741c40c443e4400e00407194140c55a00c90f0110345554009420100c505000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 747686870 1250 747685620 747685651
    0x30f101a07030807020114070f02100e0307030f090801110403020f0f030c041a090406061a0a0f051c1d0d0e0a050d030905090f0109060b0a02060a09170711130203 71
    0x107400f21811000500740e2000d542d01c8140103424030081801c01c81c49800039031707030795940e000715420000d16010114250941d6589000d8080e07015410110480320159003509103a03521640d032210031110b01400da8031540055180414400403d0841c07002407044900846180c1d031030306101020800030441e50060182c0c59031206044051505264202d03101100100100c1c240d1502c0e14070109404500449049070210380d540c1d41444200320b8444403c58415007000c105041841c02100035000b01c0d100f003400c105024002c200100c802d58004001d03046520132140c1407201c4000703085013408103000180611814058001d110700b07010321500c0c0c2650164001050b040d555403829050040804907600d00b030b0f04000b820b0001040c4c0f41c81c0d040e0054020700600c4601c0300103600d85601c81c2c040300e1498011a10001c2d0410101e20314980c001a80d9401c408080f000080540c8503240c8040c02c081c00e50701203403080002040c500284560b520007009400010341e9501d6598104085400480c4021141207000f10241c0d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 747688120 1250 747686870 747686873
    0x2011b05090906041803320a03090501021e0c0c1c1509060203071d150304060b010c05101e020c120a0513030b0402100207030b0109020f070602030f101a07 68
    0x2d01d00ca90401c001901c009000720790f0071400350540d012160f090b07000c60144802c0f901803410320101c43c40d03102403001a6850a401d0081442090312602091a0401d03032036441072814001d0a50444801d91030381010f006184000304500002c0d40c2020840500c035005211050a10f030420b19000d542c0b0031450340c0e4a645000040d07840101040d410502c510300140d03154240c2001460610045000fa0441e48401a40c1728944c3c5140100ca0118a1220f01803c0c80d80a082c040043c3ca00561b50040e0b4806008604035001d2001200d124200d100050700b28030904c5100701014607554400003001105c1c111b4020344c002e0582000d0280d03c124a46a552680401070760041d1036005005841100ea207443e19903d85443d80e0b107258045c10154100303035003002c1c11314180070440c5418480078000c2940d500107484024031719101c5125000c3c0500c61080c0b0035400150800854814008848685510410464881c207240c0c0c58440131060031207040840051603c404280e0b1411240c0d1002c031400d80041451500c0460b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 747689370 1250 747688120 747688129
    0x1603140615070606061106070201090b070f0e150301060e09012306070b16090905060108180705031e0c0d0503030a02090103020c0d1e030e060c0a02070e0f0702011b0509 74
    0x128510041c070380c2040c041000012294001e0100a00c0e6641d541112042454003042c1402c2d4040c100000307582c90600b11800284400b01e45545c04040ea0903c4510180250301c02e86103008401040c0d0350221000707810100704004600a03505982a60b07035003901c0c080404080c488038000c2801030300c1040c010003c1c51000d42d031601c200a662000e01030001030030b02402c2c2d0780c1c400e524041900d03590540c8540d1030300d10914035403058540009200c178030410301c1303d403c0110010304070010260800c044800d81485040d070040d420042c25009041c06411030300050b002c918a00b05810100300c8510450140401d455076a2400380074466810790000083c41c61510394008690083d80a01d02c81410b2540900030240d03521400e01180751036000545429820607131801e80c0001c2c03c440503000741d0030716150501e2403c180f0400030302c03580e2140004e0501e0ba65046000e10a07468002c1c0c0740d106021550502080000c010000444c207800b0317a00300d4009004011004506100f040554490200051070900034001240760 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 747690620 1250 747689370 747689389
    0x80301030b0c040e0109090b280b040204080a0606030b090a150e0705040f0f05010f14060306150703110d090b0a0503100801020f121f0b21010e16031406 67
    0x10850b003400d01d800c2d551941500c000314240e105a004981d100e6408003440b01b0043c003a58860310708602420140300204504501412080008500f80d42d1410ba001480c0c4513541114090100001100c2c80c802003403800402512403800f0803140071501c41c010810080300050a1a03107154846141031b0442040d83e1000c008000c1030480c00d005204d6280300141d5910342d4411003d04161500e0003242800700072580000340c40041e80405410190a030003000382e0021202812080341d01120308598035102c00c00054900f03a80348001c141031050008800003096040030402d100c000c512000e989260800c00002e8404810511800d07107240020480b030b40c40b07244100c008541c0000c0120440850b50380340c80301142203030400200802a4000084e4410880e074409004030380c40000c100082645032034221200510b081c4070310403000308040c003180b404043d4007400d141c214080d4400d02e104070f007580e49400c2c0900000b010303107240c080041040c48550116109000d1503002030002078088543c2e0304c403042800034885 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 747691870 1250 747690620 747690631
    0x1c0c05042c0114072016090f09210807030c090306230106021608070503070515071e030311070f080318010e010c03060509070c0f1112010e0f0a080301030b 68
    0x1507944401c3e290707620003040e8082c0541c040e6070310390005d1641d01c42da85001e45480c1d402c00e00e4940c0030b00300d800558490840b0642c29902d01046c086200703c0c0d15882c0c5d002500c07000c400100a81c03c01c50707055800300c50011100c010b031100c9558051040e140c0c00b0040e0201e9144100e0500014020801840800d0584d0084000c0c02e0b040f10400b220290541454600400d0a810100040e040004680000d0301c2210403a4041c1c07161401a24146240000103582c03603110f0710480e805840400a5954800c0924040d1464540c00074544448500d1030009454004004201113020030b140440341442462030400341e0750501e90048495000346802d450300f80d001c0e0001060b8500e5032120318801040c01900303002c0c08908401083c00031508548000002e0182c5009810190048411600b00070a840d44000c8500c0595000f080c802a891a1030401d004658000e5002c1d9801c00c2541d45141c8440304c05600c00c0140354444000e03034103c1c850707204c0000d031100400c88002d005034005000510120380403040168029 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 747693120 1250 747691870 747691873
    0x40507081b092d0406080c0a09051f1202090c0f0a030f23010f080f07120303150803120903040f0603230c040911190c050c1c0c05042c 59
    0x2400c0b003500c00100035030700c60f407a044490305500800689003094040d400c040c00480015025003201040810202c801d44d202d400c103080d46032001b08007509880c2a90034030706000081c1d6000b5150700c03007c0820444825140413409203850100084e188400360702561000e4401150092421030f8080c0c045002e004c40c000504809a079030005042d02d40a4020505141d0903c6901260a9807400d40e038507594103c1d40c4c1c40310302c0304d8100115000540002240010039a00300400c030611422207803d0031801412000c0c0c1a09a980c400303c0b000c18642c07000030261030814205030200c2c4841d40c90f802d002d42c0303d01035482100e00c001c0199006100442c001d03005051940004080301c14031150b40051150300180c19522041c4400000a0038403160146002c0c1411300b110396000e81c1d180c2205401116038110002054000700071050340c00904100090203801540080100a0041c00e09500004c2c0503103805200200c4030700030f82040015240c140b5000b030314410225814000900217640140301c0300c142e29410030460b075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 747694370 1250 747693120 747693139
    0xf0c07090c0f0e0a09060f0806090c0901032d06020c010c0c08190c0501090605070f11120c1509010203060307061b140313060e01080a05040b012304020711040507081b09 74
    0x5c0190724030075100200726080c90b441c6d22610740318480c0d062201c080c0c03070f41c244e54121840409958a0b07030f0000504503035001070b4084540203c1d6a00e030440322840401040041805065002070014903000307446140300c0a4000c00c4001c3c40b12205450240d02000021705488003844009070a03a0380c02039030300300d000340380c104100844059030360745084568480040b02d02d250740308280704080d6446031a1046030861800c0004407002180007181d62003035003c85450202c0c00c0000c181080d00c0c81848101c0034500c660704d03180c00c07c0c148450014041d42040301c0e094004d105404000500a01c5203c0b016004008030f5074105a482403a25260610160340b56000c0306032004000103940c2e02420013812000f01110b5442140c4005440300040c4456800b0b4502c20b40e143c100403e200c04113407400e60301811a03103a2b091440e04103910051812400501220044d8018400300d58502030000030030b40a6034545040f241005543c1d51244162811282a145450590203070baa4420440202d03400070418603038010054a41d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 747695620 1250 747694370 747694379
    0xa150b0607023303090601180e030309010c0806031605100507020306070302040e060a21030e040c08040c290a0201020d0606171b0a12060302060f0c07090c0f0e0a 71
    0x10100340309034000d18007030074001d040414600900d842c0304546160141c104c0c61420042d0880e60380321010300a2507403014503285000000300d0b0703942c8000c42c50404001a030381c80c1c2c50310b003900328002e01d0b075035203884045801240010080d10340800e00300c1c42d9001c5811034040c00f901f0403042c0040051107010b605c003404020028031000d47e800f0010315100b620650360150780c0d141000020010303c42c02406150052030034a1003840103209071101d0810710300a03410309000940d141d00741203d20030b02c1d194902341c001c0d01c0c03d00e105904580c0a0720303ea103d2800b07a035485008070343d1452000304010a0b001000c48480d2070509400400804000a05c600601c62001505000480e51024210b40d03072640803401003440b40c0301d4000b09804910303841da40801d40482070808811400c510101602c980402d0b1020820014850840700030b465100c140599005001c840e12196680d803010161303400043c02c241c1c244a03103c80054005040e00074880380c40300b25901e50030600d081c0b2006454103000048403d9011072042004034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 747696870 1250 747695620 747695629
    0x2030c1b0f04050405061504090c050f13020d0f110304240f05070c0501180b060f060706020414011b030f050a11010c0f090807050a05101e0e10020a150b060702 70
    0x3400350340644003801d41030a0141072480c80c0c99401c0787d5980503c0c105080e143c0800d12002d6184110b410030740daa200084803980c000703000e51f0000c55240016610100f40a800345a0079400411a00a002c0c000c2040d241030031036569030ba01003124004d10005078900050702e501100040c000084e4854200801d0b840c00895400c0d0590307038201d074544002149030700c2074403d02c4030901a44140c0e000300741180240d008980c84c0d030890880001d203568010142c406020f080b5850390f00c03ca407902c0390090f00031500c480d25a410202c00b105504a407134005099180013542c82c00c01c3d1885248580d6040e00c42820b084c0e400c10040d03a0a402c600b1200742440508140070550940c207000d08d00310070010ba030b102c0081e0062054050301040103030700490610f80c072804062000e41c8400340c451090b11700884040b03201501601b4211fa0703d969103921410b806610106a20803a604080e80000b9000100c0b048446074051020407a41c0e64a202c00192600000702c156a4004009a00c401140c0001510091404440d0780124 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 747698120 1250 747696870 747696881
    0x90102100c03051611060105040c0e0a0e04170301121e02040c0c02040c18030602090a150801150c0317090c120303150402040302130c350702030c1b0f04 67
    0x600031a40f10420001e241101d840b96641c94030442c00c204814001d07110501d980c5c1e160502410b40515a03070070b001d8400034052418021070500090036001080d1b1142e0a6240d035800680b02220f110b03680340700f807509000038402a28160391214051101084082d00d840d603034801159244004268200160070242e12280912400b240c6e00d500c4091500302c02e40305100031607a01c10702d010304110a9400c0401c0b00b00e200050340c01225000007000d41c035110700b100010303a210819408644215100303410f10394556003000c205030403240303c0c40c15039442e40f1880b0001d0303c10344500000140041d0000c944200c0c500a901003113600b00240104442d85c2201c00e401141084503aa6452640f0f988007004000f0000d20541c009101c03d8010b480540c1010b00d542c0c0071544031000c07040c02445190300d4445842d03e240c03081c002031018101560340e480c551100c441c00228050003002d901964000803100190300940000100d40109804034010030403001c0c00158a030802c0080c240003035008030625042143c55840e0300a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 747699370 1250 747698120 747698141
    0x15040203040f02090903041d0a020c0d0915030b060d0504170307020a02130b030a0b09011503081b06010f0b0f0f0703090f08070501021b040e0a05070501020114010506040b09010210 79
    0x10382d00c8010441c01007280300c041c020b0800404d0380c000c10041c4050904002e410070910f40c0245501c000762243c400607406070080e1341d6183c404bc46850402903940d0323808a9454122441d0704401c0d0580c542c8084100c2c02e40c0e058626064100e0810441500c02002d02d51205601c10700607030380c650805004202014896105940300030059220351303245415490a0002000800a500c1d000c00038484510701081c0c84e01030712840070b0010403030b00000580000c001e40111121602a07101488001d40764904524160072540394884100380024807150b4440d0000b5205040c1c500d410a40c500030762400d03448031980c0c0e0000d90001842c0c00240003a210850040e0050000540f1039154009030505000d05000c485603954440d10701903120083c00c0096980220707640680e0001c141d03018020780d0b981004103002d0082011a052644100c100c40d00c103020001c226841034850981c000c0c000b060070b56501c404114428003540d1b91000041004114800301c5400400c1701000c1801034600002c1c1145031f000403111820305 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 747700620 1250 747699370 747699383
    0x50601181104260115090e01020c0a1e0b190c084c140607080909041a040f0312020424030612062705060402010e0f040c18060e09040b1504020304 64
    0x11b0002e01d03142d00071882001d802c04021410b210423601803950720040040003601203000e04e090320b070340b00c04e031025406c0c001500f1500381101818403214014902000341c150612051078906190310652081c5456801409811095140311030544c1d04082c0b1145005101c855a600c2038030b402e01c2e1540034851342c00c1c0060500809a951a15041d050320080003036503101c602c1220104407890000b00100c0564003904400c1e0380c502c1c4280c0d02e901c2d0000381c000c0c01407001541781440104020030802600c0140841622942e01c002040d0710802c0710000342d0080b409441c2014604c5e007100c00d00c59050b60540241c20400d450040341043e84d6088400b01c3c011241e00585a0b0f42e21800d54006a00c9454420401400c000c09070b15001c0f41c0946829403101d40c0500000d04201004150f080703a5a5004c02c5400e1800c00200100803011016401034040a0340041c14400201001000505070307000c1c440c20960740c04050710a050700c0d0b9540d03481d10f2510b0030040541407604a1600407002540f10361002d11300c207521030311 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 747701870 1250 747700620 747700661
    0x806061207082a090a0806010e0a0207051f050402010314010609030201030e1510061106010302060706021303021504060e0a0e040b0a0603050a03052a100c02030708070506011811042601 81
    0x30705c001e0544503000007510740d001000402210a4610000340d0000020500585039110b070300e4110704040c85138039525a6440c0c95004107000c010140c2c0a180624800d8074200112202102904a905400d219500100790460000c01c0554065005103801080403003d858030b54039050722051444c00f042e60b40010b0112007060604c6042c2c1c1148044800341a210020700d074540c5550300013a1144600740b00140019000314507944003603652112200511f13801042c40e008070024084c40c50b190b800c24400d14000030b01e02c501c0c5612070305005d440641541c2440c18a851643d442e500c8108146c1000343c2480c07100c944da02c80c008046002070101198040c07284d0f49a955480344c103450202c0038482082d041490040002e8041c40c034003400a80802184070031400480c0d0701c482010181d0a50146100c0544003000008000c0104400403036005d0680e962580203a6102e180c0d2066001100c0414101800c20302d01008107005407100f684154100e94440c400045a15120030b005500755050000c070340c030f10300030ba0301c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 747703120 1250 747701870 747701887
    0x101a1f080f0105061b01020702041d0c01080f070509011701091b020f071406120108160806040c270c0e130207030212030619060f0806061207082a 64
    0xc1032a030003940c0c00d00280e045506000c0001e9091044020755200840b10b8411042456400c0d015160025001003080014103081101404806c5800c41c08208038001c841e0310302160b40c0208100c0c0d000b9601e00361014519030751810282c0b407542c408940b05041c0a03443d40010f42182c101000c2a001e044042c00101ea1004c030b404541c400000c1003e070036400e42d00300209000c9280c0001440c40101e40a80301d0003030440e25a00082051449440f001c0918108140000304040c01e0006a03610390442c00440204841c1d60350b011552924030694004150806500c010440c140919800c11a040442c40c08461a41c662074a0306049031103030304002012449680050307030f651070890494805408000825451f0501c1c994009440f609124418220801c01001186081d01c445c490000c46420180312030b08920340703855002e0600080c2d10010300000e6103400c0061094149501558101c0c580e010342102396440d4040295125000101110a480502c030004052030000408428010a038140c8240c0d076078528 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 747704370 1250 747703120 747703127
    0x609050601090b0102030a12200c0f0309060301180f0e0609070b0a210f061e0f0506040909060e03130305060f070e010807030902090c030126101a1f 65
    0x164480403840789010f03002e50550360044102d80c504074451414100007200c041a41e401466804c050f0b80b1600d07205d83c42601e1032003440004040064000301241d41c0700440142856a912130f41e060907411035003c1c80100012240340010030541105c8403070200d40e03804485886004ca414505201c10154080d41c188a00c02038148007400150440c1b500c41d03840e09450010280c000380845c0500c0710401c07810440480c20a81c558803880414188210a01c072113030703032568101c0900c1d683d410528051000e0110000b2060740903040b510032101c1c0600fa05007401e2030409514010404000260780058448044110781d940030f00080c10780a60101580c040b20b42181052881c100c0300030044410790311a40d0a1001140d00b059801c5140c200c246400c54080e95141e0048004d40040d010007500003200341c0903c440b8420300b0010358181e549484402c119680c580091000207040c01400001e2a00240380514900b10941c03c03038400c1f001050b088103031290200010500352102003e8030b00a00324840035103030602c4d60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 747705620 1250 747704370 747704383
    0x402040506010f0e0139030809010b0a050f01051b0d17100306110705060a05190b100e0a05060d050405010e0d3203070801030c0909050304030f08120103060905 70
    0x2003c0c60030003445100c4500141516a004800505200000d032030040642c0c0c1307100d50321041c90200342814883c040c08410b201d8043c03044407011400b0403004c01c0041d46a0405101d01400c0c0340000746001c3c0c42174a00802d00004c0103e0150180c104801004112401c0e2100d038600b40075119104010301081c03516140050404009401e44c86000300c0b6030041c003040ea03d519001c0019a5040180041c14140c900c580d0815849007400040190140000b000501103c560080d4461020500c0010300160701500d003108480141c0c2046601c25020090380d03596030301c1385083c130300c500784054070040c00e5a03116030005c1d4454100300c058601440d00d030b00800082260a0003140e5100001d84000d01c9c0c040d6404402800701202c207840409000008000b99016081c4603110020802204d60000e9690500c0c810040824109000645d11190864000a8a03810740d1113507d403641d8101b0055824070f419655014103207401244141d0702004181700a480302c500c0704060a0007180f0a860000d141d556516049d400d040e03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 747706870 1250 747705620 747705631
    0xc060605030f0d0f0c030e040e01060e1317120414190b01080c0406052409060307020a02030f03040b0d0e010209031f050609160f0c05062e360c050304020405 69
    0x126288858002500521080300041e0200c1f00881c42754070382080e442c010100750303000d4410040107405100c0d9560024160400c5507000f030765001a2070000c864241090701c916a80c07240c2000310100082c0200e2184003080104d071601c0720035190b019002c1982c5200d21040e8860994079000c0600042085102c100002480e81809407018030001c5d00d0000041c26003c1480c3c1149134920304461782d03010307000e440000c070790b80007800911003910b900304403000039920441a0b000f2800703449220240c8105250010949048805468404e49000403980c20309001d0a00001781100c1590284180c00c140d59007031040030117121030440e0f080e0541100c1c031401802c0e02c1c800ba01550180250106004000c801c45001c1c0e142c0c03550310b003481c04000000920403203620b6409800a4a64041c04007400401c042e0700180855501880d03015441d030250807050024018007921a5881c508208100812800848101e401e11070241464107600c01c440c0402c3d1109442020200c0c8000810001c104400c42c070380343c4201381c5c104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 747708120 1250 747706870 747706877
    0x7050307030804180b0409080304050c041e092f09071b0209180a03020f1612023303060a09020304030801050402130b190314090d0c060605030f0d0f 65
    0x201d1542d2200d400512607070181020341e4409041c40300d80d0080743d0300200000800504100180b40d100d0804000c650001d903000c65803030107100c001c020285414020380490060644100382e0a8901e50341000c01400c182d041203e140e0070000140b40d02035848400c2500c0020100f527180c00a4015400304050781070006d2540b02403140c040c08403205840c0c0d100d50190041d605542d015400d8680320114002c200071080f80d48060310a83c2caa800405601141c07114440d5040c0c01110035122019100e860110200d0003042c4060b164958070070090710302001c030b4150340c01c2070403405141c2541680e0000140782c490401941d01403400000d1145609140e51a4030003030107803840443c11070410395402401040184030301ca21407500403031a041141b00101d072400040202d00000355981c00709500d20400d00ca448021800801d18143d5044180c03010381c8900340c802c140b5200a003440003003580044e11000c2d581802980c1d040d5503600003041a890030444409200010402405e9034454040020f01c0032404c00d0581040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 747709370 1250 747708120 747708133
    0x20c0105041211310b0627011b060501082b14090d05010b0406080a0503031b0d1d0d0e010507030516080f040f080102040312050a020a14010608070503 66
    0x1070040211140d18200e511595180c6030349940f01c0000d00815290700c150700500c0561480004200c0c44444110740c4c41d081400c00d01030f00301080100421402a400f04c1d0a90315441d0082e0b02010740341482d0741401030341c1414a5288900d40d103424006061f80004200c41159031400180308000c020460b14030f00e80d150010391405440c50081090646502c00850f034203000f030140c242005050188265916208040c02e808040c8000f41450380c040c04d0740459103030041c2d2601c03a0105010501142c401007050b000310003145180c0b07401c900305262116201c00f492840a0a101c80e503c1c4440074006d500342c000c0c041a0603003080d04e0002000d130501808641c0d000071b00104910010190742c00c2000d6480d21501400d00b140c81306000d00c83d49200c51040b43c0010315180700092607000f5480840040e2058684444483c3d12803600d441c601c074200d10031400040e00300c40c882000148039901c104010100c10340d00d0f205480d80318149940395007031001032080c5012a651103880600150b102003100c1001041c0880c000c049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 747710620 1250 747709370 747709379
    0x3071401091208040c0e0a02220b1c06031b090b0108090705190b0f0406021506030a0f050109051f240905090f0f07030606120b0a20130303020c010504 66
    0xb03500c0004010310705010b000d80003d030600c044a084440240040808920700b41340a4811748000e60000c00081390f280340c1451b00c02c00c802d2034402c0c0107080ea13a500300700c1840e001298a15001d2901444010003205845850103c00501340034801c0b03d0604241014101d80d80c00c140710001030b01c16400202c1d040010b5482000259400012401e0444405550350300128081d85085030b2071854680000300c9001c40050440300403c880c0c0011b10480325158240c0d02610015609004141c070300303680096160b4040700348240442c02596844e11010f1140c800004c00303041070380e00d4604281c4416a1a40d12404201034000b402c1030074000d0030052051120410b070314102500401c40035810a0040d20700c001d40d01c10006990550401107803584085802c02c80e1041d06004058968602d480c1c00112002c0307043c0080000e0050100701c94070002d6500240c03010b0030380c0d660b009940003855180d20140c000c05a00c000c21034035140303c100820208034001c4841c00e4040c110b04010b4580980e01c1445e0741040801c000400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 747711870 1250 747710620 747710633
    0x903050d051e01050405060315090604050f0706050a0509060903061905060d030c11180c091504050603040231020d05070c02030312040f0b090a050708010b150f0f07050307140109 78
    0x83c19980c01321000202c030b403517000c040b82c6005445841d070315040305d15030140700228a00040441c411442a800c4621466003a0041900c5020501c40d85c0c01258085c002450500e00610241440ba9400350a207800c1c9a41400080c0c80c051040e907041b440f90f18109420601c00c2c0c00da018040c2d00003400d40f100c1054100703a5900030840a0403010103041e030f03880e40f142b41f152a510440c8041900401110748141800d0080a00901c6d911486045105a40b61000e01d80c6c40408502910211140105000d04580c1c5a13024400300000800289481c10f260360142d009081056900303240042d5400700040e1100014101d080488501800300c07003d22802004040c0140c0d0000100c400c225641e040ea0507807503c9600c1c0009100d401084001c00800901c0b080150030342c0002650103101d4090380c11219070715501c0845500700d8160341171070358004000380900c0304002810303070090140a4030350035010300e452038081803154a23801a0b1011070343c84c0c00000b052400d02c00e03664036004892164000810140031503130f40b0715 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 747713120 1250 747711870 747711931
    0x13030b0609061017100308030c0301081009030c030c02150c070f080a020f120c03011806180305090d03050409020406110f19020d15140a110928090903050d05 69
    0x6007000444c8000900c102c40300c00c1c1e20350021a031103081580c503420400400b4045030401d0040280351320507601d00304000081d50294103949074140e01c6480c00d407600c5840459a0036505502641c01a201c614001c8003070803403030020710344000c0c00c034042c1c000203041100070015103041e80d000c0c903001e034070031070544c005666000d03012007070034404613010243e04000300c8825003803200b1074000c140d055103400050f1800d42c2d0a0000c100210380700e044c0030020501c90b5603501100400051001d400500f06000031030580c148111403c22281c02410201c1c1804c4d83e0b001c010041c2d90058016200142d503003034582d40b01840030084d8400054410b07010b02800903440070581756400c940b11002e4401c05c40ca440c604e061180e966203061020904800034040e1045040641010300400e40d0b252054501c0c01303011208111030101a00d601c0c20000b450866100000e01c0950401c51450240d034010b0342d40c0300f10000b950f100b01e101e00c004091103078441945540c084400c0b20f0803240c0080203a40444030a02d0f071b03d201c4000b032a10341d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 747714370 1250 747713120 747713147
    0x61002030c15071101150302150a0c02100c0615030b010807060e011409060a03061e053003070c0e130206190525060e0115140613030b06090610 63
    0x461541d50703940c07804651082c0d0500c02c11115500e414115000c02c0d850b86d188006407030003681d03005441440101003000d40c1c481d103034001002890010380031005251000031030301514054070b840150700d081529548110b5900175000030f08640a00c00400810214091003401810008081c05c9418074099000c0c0c000c6100016003070400ca00308421211040301d200c1502c6c0d240e40082c0045c5d0315609040000b800a1409000320301c19807032408100c0301d69200040c6180b050302c0c8040c00e22a4140da00b0440c03000022804150194012041450402c141c18104060003030a401124041d6081d850040401c0300000c0152016040c01c41081e51200583c0710700c0d04950144060301d11440c60078180c000c0440e040c0c010310341940d850402c1d6040368204412070710400032889004020070802811508103541c225100c208030040e0300005410200003030319144032803603902040a0722491030491001554046d0524940089844000180900c0602d003080c11000e42e10210640783c0b603907840f41058001c2c00d14180f44c00c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 747715620 1250 747714370 747714403
    0x14060306090c0d06030b0a020a020c04020f120a09050a030c0c1d01060c110307080a0b0a14180304030221061e150a091a03060703060e0103021c02100305061002030c 72
    0x280b4408040d900c2d4000c038000e607001b102094840c01c1200c0000040d51000604034010303c182c0110160918061080b42c2e450081c05000038948503a060341c00e523a5180c000c01e03401100740e9640b4958003181c800d0103081e01580c460760300c1592114040c6002c80f8005015084025182d800d40a001044081d9504080c107641c441c1c101400c06901ea45001000286040c00309a0940154800050140c4001a9840d00c96100d524000b405503501455582204c40d0081c040c0d44c5480313401d01007206060080c000044203000003050b02e01e0180c403038000c101400d8040030540d60f2141864110082c0107400d100d625000942260000e60440e9a00002d20800c0c801402d01c213904c12407a030414080340d441070500401010114000e000d400301012060f2452080c80048034003030f0261500084030f86109104010981351114084c9110b40d003540c0038410400001400c090003000800814405640c0701201c814800245590100301071824500340561813600080c14000d540c802e20580312403102c0400c040038240000803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 747716870 1250 747715620 747715627
    0x5060a03320106030f0213030201030b0a12030801051002010902030d0f1803120305071e051c050a060501020f0a0c090e07030f0b0a05070c110f010909140114060306090c 74
    0x100940a0601803040140034440601c807024501044000564100e940a441c2001400c29403242d000c142e1055404506182076075100500066006c0e921000a00401400024949840b1500c540f8005110b20003500454200001080076242c800320210f4110314900c000d004501960f408295500c0d21440c142c0e0a0001006140b00800c0c805c2140c49036040f19110705a588036642c2c00c00e0480b48000b103a011000908007800501500c0c00365845d40c481006403031400c000d003159408200d80079000010070380c010450080d81d111044665000d5075000f204102c000003543c81ca02000a0310b80306207400c1030502a080401d02001168118040b00101c9804c0ba07070126031096044035490410b81d01e5040142181d0042c8109c1052050400c07426204600070782d020442600c0d103220a848601294200900b5201d0b002c100c402c072410b20900c1110300300410f040c05048542c07181549000c0d2511500140348080c0395a004010040308101c1c42c030034030b40082d1601d528500780b0364041040c048006040c18401781000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 747718120 1250 747716870 747716891
    0x3120604150306090c0f060f1107090603050c1e1c1403070c0311061314120106081f110301030b04080708120106020c0103050118090203010e0706030605180105060a03 73
    0x5030019032040c84020100d030002030b100e10388040103204200055400d4180c2400200d592050131140340207882e22625645019840008200c5110b02d10601200c6140161480000d0ba035070746002d80e00240d0702c00c501401c48407040c9003e103c00500000f951031030440c61081100f416884500b0f8030107103401c8000315924800c2144c18102c0325603608030506400e506c030000302c0b0001d0081110030701099030f1089551088149182d2704101c001c3c0543d030740c000e44860109408100610b800e51311881c0c1400c01600c24081082241d0509084035030305d41c0544015001000b511010700484020b03611103096034041003040c0d0380c3c0f800084c021070205000040400140c0008074003405068410f98814540c41a13606a41302107401c901109000b00384213400141c412a80b91942d298000d005460690b2483d0001b03500b0b0404055000700680f00300f0005076055580c501310703d140b5100922120004d8a020f881c0414070625103420701800c0001c241c08681d0038001d100041c8900d54a420480d170402e8454030b00419500c0c0710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 747719370 1250 747718120 747718129
    0x70906091a301303050a030513020d03020f190f020103020a05040315020a0e010804050c0f0d0f0515010512060c09150c1c0c02030c0909070e010611100905031206 71
    0x34100e29080b920400c11901490030864081e00124050b10b030400c0c4a1a125100b00c00203482d0385000003400b00e0320a1010501c403500c01d0340060782c002d5503500c0c2c2c8501c03083c2d6500400d26041c01c2c004180c005030004014916007800070090444121024000b0400744051a100d05280300c1103154001d0401d500014800e02c83c920400c01d03136020303680140615400f41c2c0100041002540308035003490110305000010f1445601031407a1622650308140a0161240d44900b04054032000040c001e501249074414031000c140010313030160203684a100280101c074111800c140d202c0c40c0503803005101d04941c624187c0c402d000407500d1900020203054940c0c4800c07415000a08a40300e0103050560700102242c0080513650025264100010701c1450b40b00c41400c0580c2210210100319000c1c0d00b5034400c900080e0207040020f0400d40c07000304441510b6003135485070604510341800380c2c000400030315000381518074900d0038440304000d070084000030404140181d545a45034082d524018000c2c1603410300290081d00ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747720620 1250 747719370 747719377
    0xc0201020903030c030a03050105060909150a1706040b09030f04180b0612040b01051e0d020f041b0f0206041109060f0303040801060e06090745030b070906091a 70
    0x81c29030362144031103c4c2142e07603074001c24602000a8109000018203040c640204c0702810f00141c00b1103e51b5681c2804405031901101c045e60708003e0060001404d850811b20b0b5001000c3c4103800303040300341800d0810403101c0c14054a00c1c181134004000d2074103a100c1000845044808082813074804840d41c84000000b0008418143e4220400103900c900c0014810304261007107104440c001b071141d880d03100b44041d00120400e03062401d05103d6150005e89044174292240c1480108548030780402c00e00450140c8c1c0280300d0384401443d041d4007035002203410035508100d94003a40300070704040c54181c80341c014070bd0703008143d54010311040340414156100d0035548810703032001508407645d6650782d0486500074800303482628188022180811694035049100d540540d06a9458283d001454824203152210244103d81031503170881c10707065180c2c4a65000d00d001040da001d200c80107851740c10281d04030704000b8220f0041000e03601c1c05100303080d0024800c07403c0c9c2d0400310b840105e50f4040d003030007800d510 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747721870 1250 747720620 747720637
    0x6021c1106010303050a031b020c06161b03020a090507120c17041112070b03061504030c0905011401020a2102121b0f0a0503270d14010509070e0a0c020102 68
    0x10790000402450341003130007403c441d195036808000c884019121035801400048040005030441c120b80c00d07803454894060a21540a810580c011b0740003070352141d440040303000c0c00740000c0007034003c100b06601e0303e100484000d0100513024000740c6000740e0300a080400301164075818959400596500c00d2055142408044c4483d08490541c200f504040000103040c908251080d6146c914900c0546c00101d050b10890f211040740351304546a0130108030b41440f0701c50040b40044000c1c40b0001c04690100d4002c4010242841c00007415410251543d080241010100e03065500c603006601c00181107105038084008030022001044202e802c00302d08000c41c0d04130500d6441d10204411080d01c1440d0040564400e00c0011220707a6031540078059151f04420902034110341041c82444ad90b12030350302d4150940a004c0340441c1040850100142e84180320302800e81c2c03000d4036100d468220b118244207683e002041d50009040192a00b901a00c12510040000d152a0f1301c0f11602666103000350103455058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747723120 1250 747721870 747721873
    0x506030705070f050601030b0907030c0902090105090319060f0902030a0605061c140f24070306090608010203151504050613030f03350651030106021c11 67
    0x401d00f504000d9555803081c00241c07039107003900d00400c5021000040d83c004481e8403000348100e03d494101010000d4208110090620508001e40c0000303136418801d80e0200c54240280c40006000b41c10000100c1d0348224404242c00c4c41e015854016940000d0b040c0c1c881580480e001c6856075514022031040512042c9814011041448a00070000c00088000c81602090300310303000405d0400c1240c0e600c02c146046580a00c0103c215002040440d03408a6032050f070798280031410039664001c80084680c2a0710401c0c451f5408002d0142d04c00304540840d11403c011100c0540840d21041d810845200b01d2082921a180000e03055180c182202882d00040d074003c64820800440d40c10301a040754400311580c81c05034440824080f183e496000304600404041c99406d51a41c1c44105201814011400750340783e02a090440c0c6100710707100c81601c080601140c05040d100d2218402801030040c01403110140d21009000501c80164009111510240701011140e03e80e000002c0c180c5e140002c450003180f45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747724370 1250 747723120 747723143
    0x100e06030a020a03050a0b0a030f0f020d1208100807060c03090305190201080702060709030210020a150209150304110f06280908190201080a0f0e0a021c0c050603070507 74
    0x24401c0d9000e40b80c501c00f140c81c140115524902c4813000c85405000310342c0d1000041c1e50030b001099644407950391880c130488034003d02d445140c000403824606030b501103444c90b160b100b142034017543c01498281c001c8a088561401c00f400c1a000c0d41d01d5211900808082059003034240052600c030300d154500031500b00040d02e000c00000d05861500d50918542030303010504510206110328400100c4a1050450341e032616007003810741e82048140340c01203445000b11b1180c0b045241c0482e0f041103004007050310103003005075125401c4081c441020b00141c0b00300c2c0c05040600c100004940100c46030850342d0b000711403c800c5840c10500044860250001d180e1107011211f052403424080c034030305040c802045446428400da924011960b44410030060074240c5070082880340019401807041cae80d00404809008102e180101745040202c0d004080d003101c1a40c40b9140c0c1c0410b508101101d070440d08040d9004400b1004261941c80d40300ca8103100b0240203400000000343c08a02c03500554440c1030703214469040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747725620 1250 747724370 747724381
    0x611011d0d03110708090d060908160b01090603080d02090604080d03050114060a0f1409030a0305070c08060105010c0f0510061d0903031b0c2404030206011e05100e0603 74
    0xa41d0740e04001c000012a18107404101e05039003400a0354440f035030190040d071070701d200441072014100c00d00c8000c446164031000003200154a04d4040c00c0400410780c1d003110b80f003456003042010700f8010380c41068102d10307101c400d01c0451130040480320a52440c081c0540c0e40d80c0c6034008910244119403041c1c8a83c0280d1240c06082a4160440c030704913181003420031011203603041004140c0c07155150f8071020504554400c3d1995008191000501c12010000d0703042040240100c2d040140b00b6400301d00181000840308104036482c000c410103070003480c0041c0013a604150020b0441f0500340c0c1c0c0034201d0044001080c040150801c518007140030000c2c0107005841d6183e0031408201684a40026007890150004100940c00401d03a4480c00c80c401c540d520b00130181300c060740298444c58260202e4001e03030b0103d106480c0d4405145003000040355211030f042c90035041c0241003a4040e0010381d8041d0a010215003826802d40e1088180c80c400c59401420001c2c4d41130075954560b95841c4903401c40030200401c407 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747726870 1250 747725620 747725623
    0x4020f0406060f260609060f040f020702031002031003021207180207021c080d0e100c201c11010f0c051801081b09060f070507030204060617010611011d 67
    0x2410f151a201e1000394003203941505000031080008100c0c0714891400200350349400442544c1100e800351181940c89034100c003040507124a019041c203002c0d0001403a50447c101000b602481100701c000071070560420103914400030004d488042d220307102400e800402d51806001c000000c1c00195164040b644061802d08041d4000000580c0b0445002e200c1034800328800001c0e9581710b50196075246444524451000201000e42d40d41d221072280400da08845000c5101e5041100126115002d403030041d401d440401c6a00d40e008500f10f608100c210b0589502c07001c41150307078400c1c01d0230b113a40e00540b001d1035540140030300705c080c074281c9040001c1c035030382c2603000401001c20084148960181c0c900480065504a0050f50320b0b000b20201911800e024103480d03009410341c0da000411891070811155201010b50308040402c0d106604201000c00451a0904c25078008040700c0c00c0130301030030b49100800b03912104144504c406201c05505041041d440c2036020b400038610803886560000c80308032410f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747728120 1250 747726870 747726887
    0x30c150709061806080c120405031308160e07121a0306010f291215040f0c02031804151d060a2403140408070302012703030504020f040606 61
    0x200d020410710744020500d00d10402d48903440c10014140600041d1500301c0445d000180100407200d1001e040c0124841c1103a8082c0081c0500d01860046840340da402d00c078810100c031640d20039041755110405161140d200d410840c812260444d900201c15990140203031044500140c40701540e0b8540360340c0c0d62410840900c09424010142c08440e00d603030b29100d0034042e201140c0a825401e41c0c001c4206102ca14a4600311681e68000f20007103420108018200100f00c00e054070500e00e00320030f003020006142014840c000c0d00340c0a000050000040054001c0e44034803e80d66003000c0c01141c0c0c60710744110385490304600c02031400b0000c446001075686901c0015003441070f204031101117401000c1101c0b0700c1d0443d10b00d8181c861501d1401407845c4490b440c00e1500343c1011007501890b03128220303015a15044402244224058148155140643c0c41c000f400c540f0303402041c10020082040c1034034071910b00d025256080ba0b0606000805403500e0000400082100000ea41d200c1d0504038080b82084d40001c04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747729370 1250 747728120 747728131
    0x30309030c1202030d1a1818031b15010f050105071a0705070b010812030c071547060d0615110f0c030604060f0b0d0803160314041103030c15 62
    0x800900d80c11000c40100286e101d0700b400e03805020100c0300c801445020910725003003092041013151800346454030600355041aa8500301101094001e408800f1081c841c04419410410300081c40c0c0d810200b801c81c01003035902a041c100300010500e0710070400303103815034049500c00c4546212146800700c5e0040481d800501c04860f040717180800094000c82c002070321070900c3e071031003c9541107541d076150003081908101820f8514400c403600008070000148500d403034040c1002c49003450720824160501614030252100a00c03081340d4116904954072682201d807035108201c8a05a42d1750461782000e0286c080340c2c100006041844000d880c4643d003125602440358400c01c280c07014400001c1d0440d0321103880034000c80d050341000d400100003134000d6000e400a031642c0c4500195041b00b010110710000e1030400304454001c1c0000c1407080d000d02d408082042d6048a1405001c3c0081642020418200c05400100a446a10140803440d034084c4241e6001422000460701602d09500e000350328248141c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747730620 1250 747729370 747729397
    0xf090d0b07030b0a0e01030f080d06080709051510180b1b010b03030a0c0b04021809010c0305060f060f031005130501050a0603020906071101091505120a0c0c030309030c120203 77
    0x783d00e4030f20b0804026030802c07200f1060305000182e20359110008500c1c00e20031304030f400050401003205c0c101c010344220380c080c00c03203503004010b801c3c10609203c08880014000307a0104001c180950442d503510b0007031136000750091400080b44e4405c802c403540300c16001d401144040c4004031b5454101500c180a82e9031506904009200142000003815102e00c2404c0c104400601c0501c0c4210200303085140c1d49400600c054001390309041c8400c0000c0540c582914041d046075142c00c400343e02254140113454000c0030840313501c0490713030010b800a01d50f44150038013040e420308044001019001d46e41d4841004220250286800e00e009001541c01003c007400350030321500c850035020552502c2442a64031481020b8843e0386040519218400b40301c4414480701d042004030080070440980390181550b5a2a90b80c5455486104a103108040520b008204845103883c010480d840d0310340c4001103502141d050300b80050760300001e080032a10030700e82010203800c0c694041c0d0114851a4004000e0081c0c1c2407120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747731870 1250 747730620 747730631
    0x101e060f0303050703051326070501090510120b06070507090e0102090603010e06030a02040c030605010e030606010f050c010b18091e0c06090609031c02151b0f090d0b0703 75
    0x40c40c4200321905000c041c00280040c480040000d029070b0050429545000c4013900595a42803510802c592019048861070058610040d43c19010401140078020900303095a000703041c0030203c0d00340300800e000002042509201da102e6602690300c130030362101e406802d5554481640c1042e9070b50f5841d0703201d819003142c40d0000100a0b882304cc803d56910000040c050342c55a441c0c803541d0020342c80c0203446d071a450300540c20700200507a284d00c64007841a0312518040f804510309000076112106121440313002e504000308110345a030340302642c900820b80c01d00388103072541440052580141070103102d85802c042880c660020800500b8604d505c41c104020440e01d11101089a080c000e081c640000200d643c011049540b041c58500c1c054002da4002800310350900c011035000a15205507c040c0e1281141184000304485a0500242030b4840404b0030304a56410300e01400f05174030344005404450400080340b0020101c005c82d0407160f610000038541083e14117039052441e05144c0a40f00400800e140c01c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747733120 1250 747731870 747731879
    0x80c0d030b0906040209031504060618020c0a0b0403140d02030a0f09030903080d0b041b090b030403020a0b060a031a190e030409021317070905062d03101e06 69
    0x2400340c1c0c4074400c4040e06003109901e0316000e100c0650040c614103581800380904031070b00d0010000c01c15102e50301034500412070503d0000c1d11501e0f405081410490349004000405012400080302010541d101848495603590781c2001c41c0e9a0b4440700911801c00e00009050800000d9a000f070b40c00790460704000c114000c03081b0301c5081102d001010050120b68244e0342000442c920f40082c0100d080305103804120031096100140498109483d020310a2428000d40044154041360347c034050030403070088920314113081e00c0195035103500180060000c1c14460005245464403404a0000c50707010140b0080f10324400310200b05880c04031000c01d405105680b00001070446070023011000c51103d0003441c90300341007982c2480654805030f45052071240b213078000036215040c0d55000f58200041d501030900f540c10860007105403280a0301d2030b40b003041100c03000d514040f40710084651850382102804e07141c0000e00040303400d01c4110f40c200d0403510f203401070105031000100303000854401100b5007000f01d1030300c1d1b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747734370 1250 747733120 747733127
    0x705040902010e1509030a0c0819020a09021c0f0c140f0a0503181504050c01050325120c0c0b0c0c061305010603211d0f041d0109080c0d 60
    0x654000307400281d40c20103d10302c9040424045090311046032015141070208404245480321a040807180f91041940c100081d503c10710924090682030a1101d0400c6a5500000c24030b520601822001660005515a11030b400c0350b40284c144079100e009221802200d4103040c020308154480c08007007000007100452405503071003101d043c10440782201e0f0420740040700880f000d4000070321422035144000351484040a080100c0d170040b8456085102e0319103040d01c0d10908081c000c100e8981401424814080c851803010317104c00008040034207042a10785900402c80e01062541c03a111002c914000b602440140e01c448080401c5018002e07c840944031800c2c000c91a02c00e8840c0e10800d6008080440d8958042008083c107260050001091840e2241c403603582c50052044190040d603c140000e039072403600079120000d816603101081004001e0080403660181d14109428480c40c0c2d0303507001070100003031a09190156181500208515091882c12843c26408641e0410340c501ca0b400005854910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747735620 1250 747734370 747734381
    0x120c030103200306150a0302030613030f02030412060c0c1a1e0c0a18081501060e06070f03052109010f05060321131d0114030d020615120601030b09070504 68
    0x501070000c104a0f80c0703420500e008800c2c40207805c0c1e0b00142c100307800800340c1d07003c000490041ea03045401d002000a0b0b841d0242492000c8010716056420602c410801c02c1ca00d0340e980e141e0107030800f00c00f2800c00710321001141c185a42110040c0703c4003442000c0c10f50069200341e900c1c403504031480039042c04200c546031109021400c950f02c1c498981c1c1000054102071180c04403c0b0702c403100002004240c0d1f19040d016080034000d007002c550594420004005407a4002d032852464001070f6510b0740740642c1d5131500d8003000c544002c0a0b09004001038915400d841980c140c200c014041c140b12881c3d4104007007002d001c1c0c9003c114603600141030802044e101d00e004104400e040d0362146e10814030864141b03440b1069080750b0400c0c54025403206e40012584103030000c038015510b441c01544410b40c185100440044034003943c590180d48a050480080740e000038110740c00541070601c070b00740050090002560b880391854001d0242c052400000108944064400c0c01041408281ea8880e52200288400c0302c1d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747736870 1250 747735620 747735683
    0x130509010801060e010314031c0c08060904020d061a0312040503010606050c070303030c0c06020c0c09010b21040615030506150301020901080a1a03010c121a09010b0a0203120c030103 80
    0x2c003003000400009104955544680700c40009827400c00d40c0c5001c0440140c00b1003035102c40c8843e190002256240c1c0d108001c2d80e0300c108100e6588049007080d4000c1009010500f00c01414183d5924603184110b66009401c44c0c5104000d007203c00302c60360007142804542051152038040d60900b01c001c24480e010b10265103c1910070750042031524a1910100c001d4004810410107000031403d102020804c035000070144103502100409081411006200e09100142d101d24503608090050928019034548901c0000740480380000054489052240040c802e82040c4d001105510000004221000c11032901c03441e05030b10341c40100d01034101071509078071400007540d0028058400003580030035558407241003900030890710520005103102017400c45020300f0741c010204588004a50001100703008032030181c10280308002c00b020259000c108041c0060003035801d4070502061030090544204240c402c0990500540200f5003440047e28485030b05c01e010544003140c00c0d4144e032180e0040d201d81d507040380703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747738120 1250 747736870 747736889
    0x819151803050a03020f0f040e0f271501091b05090d0807110d03110c04021218030c150604060b03130204020c0c04090602031e040308010e0a06090213050901080106 72
    0x203410356034100c8056110032505800e0503800c0c042c0d04040083c81d030140081480071003049a0b03a42c10a00c6900b038800004202105020b108810000b02c03c6032007080c10003260034100c0c0302c80d40005050301e050030116070012801d010900800002181d502d0b0b0f801c816403c038800315180545120300001182c207413043c09049900070000159210010340900020080940100d2481000c110b0032030014060a500303e07010380004001c0100503800320000e00825040050440781185441d4041d40090200b0f07000400050034000c11050300d451320102881103030034a490440c04da41c103184014060354208001600d0b068001c515000e402701c0c42c921310b2001c89011f0b24201c024a203c8400d10f0382080080d40c4007010f41401402150511400c0d03403034074042d9445092143c1c0c000340c0c076407602c41103816140c0f1000c0e141d8050700c403001041c0004650080d03a400e044d1030040314002c100c2d030340d400540d8000d4030f1a940000011b03480000d00218220946940405a4a0032203503501030741d030703112030b00340c00e0b20303034600516051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747739370 1250 747738120 747738161
    0x620030907140a0b030708181b010f170a2003010914060904051c050409020a030f050610050703032a0c020414150105070c0306060f0e010614071407081915 68
    0x6e4020311191341d02c0405840e240013151424400c1a04280707901070071400500100308008070b95030300701002180e1803030325151083d80641d00c070352001e020b194003501703080300759686100204800500100750300c40783c240c3c40d1485035256940c60b0702c00d00a101d0743c45802c03890035204000c1140c83c17802c020040e00407031b000002003c40caa2088100080720104900d80014444100400642030a0600141400c111103031000948940e03103410784010f0307030300051240384900103014000200381d402100740e41549030185070000d1034040d40600b814601c010040329038629100310100400181d840402070b14854030944080c0151019082c3d044511784041c0e448422400141146a0b029441000904149070041034100304086e82c9032030340300172070b40b99400140091111000034020605010740d51801072007685020202c0040e6028074401070b000c1e400e0001c00c0e5802d00125001a4042000548050f05810301a81c80c00044454180c1040074807884c22221441004d200d0799409070315110b10340707044601c59640b886 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747740620 1250 747739370 747739381
    0x501050a0513140735030a171902030408071203051510090b03011e0b0a0509041109040e0c0a0e041e03110f0d08010e060d0620030907140a0b03 63
    0x11000c2c0340c036800c0003032060020001d010055a11000000302001280030000c0c0e401100e8000300205d04d0a10f85100d500400000015a5002407109001c1c0d14a40c2c0040a5844850101c0714500c6183d502400071800402440306010a18000b4144a445031030703221101c401d040402e0b020344600310b80d030100700e640480c0000414104603410721264081403401031082503d9a9021040780c1080c0c210003c40842600c0c4c00d09520b4900030610090a88142e01c2410850403000c0106544207c036195800340e6141d0603602003803594641a0341408c1c50007403050202074090105195559201142280320300065140094820100300f0350074081c68001421000300c0030300041d116035007040403100720108450307600c25902c90300c01400884040071004c40980840d85544000601980041e00302114040340c1405102c4503a031280070041506511200206400c0c0807803903a80056094011160150300c0000100042c160f40450600203580101c0381148450702240c5c18070070305042601801e0120340c41000841c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747741870 1250 747740620 747740633
    0x7080a1505011e0e0a1104030b01080d050c030f07030e101d06040501050f0c0304080601030807060c0e0108060f060c071d0a0b0d06050604060f060f030b04290a050414040501050a0513 80
    0x154011183c00000ca032203140410003074056071299005032014000c25005000e0104140f0500344ca8006ccca00c0d01c10300300001c4122030381c1c1303a02c210404d0503444e100000d50402058000c01c0d016015001c0103140e040e890418000103400c05000001d09100304000c400c0005003490880c080c0c505541c3e060307441909207902039015890301e502a01e0000da181c48207100000b440c041c01c0020320302a510521400b925802c032450b00c8426550200c0300c0c1400c0c032a8803070300c10a10303903807042e1899407044007110b16502d040780450110f0039a10801400744240c0c0034095010070210072081c5079221a01004403000b8003683c461906034215032901c42c182e64402c200c6d124440110302c17039404c0190001c0004200191440d81c60900350400740c555442540411220041c460a5580500c541040400103840c144450b10400e02c04282c118081c03c40d00103400c1482200700e81c5074a0706501000501b030040c1007046206110706141d000c0103003c44007100e45608003000124000c0e80d40c0280c40c000e01080062460700700c46035039680c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747743120 1250 747741870 747741899
    0x4060905090a0905030a1d060702090610200313080703050a0201050708040509010909140601030309050d05030f0d02121003031e050c0d110c1203030708060307080a1505011e 76
    0xb50006440301c21403008940c092008210441040d00e906003128000495081c2d00840c2c4410140b160000340f0004016854051103203034401021114410f49074528032065078000d0191143c0481d41040344420031800d031000008058917208510030301c00741a41c0c0c00342c0d00c2d07035024580030003000c3c3d4000741031400055000d00d01614006202e4103109081c00d8581700814640b4500368440b004031078a48940406024249205043d0200d01d240501215815500c0c054400880780c466503000da01c0c1e40e1600e20a00001340181c9590003107c403e4145d540041c3d900d80f1340a5002041c9407c290301440d40800c4138549500048011030788d054071a64810740644c94022207a0305a4440303601400400c11030000e0650701800600140002074071242e041041660406141004000c00c00307001e50026075000c00c10210020940e94414090714101c1d4440c1d5070880400e040620a5124140900c2005040000c10408540b0f140d04800c00314006c01c4941e90300e203802d148086040000003140501200305114110b445080e1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747744370 1250 747743120 747743131
    0x203040c12020d060c0804021503090a2d0c080d02150106050a032c0607090e150103060e091f0207080d0e19050f010e060f070c0f06090302060703110406090509 70
    0x10f40c16240e5042c0ca074030054403030040d80036000821800401045143c208103a01c0c030300d4021b105160035032074001c904660315070000b60040d000e0510040b5481d0030388030600f241d00c042a51680c44041e090340928242c032034048107001f004800e0083d641c000e040b075880081d0030528890072051142c2d20f40d1900740d003920244d0140341030b101055201c03940311901d0b0072440a01050030541030314400c40135062031038590030304c08090b04110800100c41400c104003607104c0350454100c0d00000506550841d04401600100100d82c003501d10311280f8010007020034404140e0010900c0c03414038004a501218040c10124850450020701c0c082c0213100386213507081158032220b000041c0c00d040b20201030030590303103041c0300c04004421601d9500500024040c03403020b006e1031746004040d4000713002e9400c0038100c400030340c54020440303401c000402c2418414400c090500c0f41005401000030084100c90b410007d4480004480303801c00f10b070a0402d013000700084c2208403030840b0510354170240e40d5401c000800c224854054035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747745620 1250 747744370 747744379
    0x31b010f02120f0a0914030a090e01151407140f0d0c0308131704090c0318030e130f09060b040c02060103021003020901110d050408160b04030204020f0c070311130203040c1202 77
    0x817407001030583c4a000f900820780c070000b103490320f0710040024a0034003030383c01030600c2c2d02003480104190768527070f09400008107040c24246166904a0303080803040c0070b11103018210126000c2d0b0460000e00109503c0d55081010042c2ca0350243c042d00f0954415003c0c24000b070024100c0c0c070000d0130034043d8205a101040c412009c9500c2c0d00c802207407680103a04150020400c2550304c00040c01e02641610030381c2d12100c42640f052101030243e03240903107400c9920f0482c2d8040c0c103200c021b010400c88a54031030b803100700c9803a50800500d45c071801c00e070707005081d2000d581e40200d14103101d5842c21400010218100c0b90300030708132641c002d000344088000c0d4115041c404d0501c030a0010040801506125203020706a103a40c070b040e101da150485c1c0d540341c8000080c2c031980d2241014018882811090221401c0d640c050b100980d8800c4000c550307520911810900e48110702551102204000b808000d2294440003103d55000b9a909072000341e0407071100303a80040c000701000c90100f06040312040b402c0c440c94002403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747746870 1250 747745620 747745631
    0x150e030a02090702030c0d020c0310150b0409050a140f06100e3a050c060a0c150603030f0e0d020f010207080d02070905010f0b030609060f03031b010f02120f0a 70
    0x2408109602c0054942d940035801c0443d0b019046802040040100611840100300729040c09003c2602c0f009820300c020718070383d100c1c0e41c00b2800b8420228494000c000d500b003141d0392a035031422200300410095074148906800c0000741046414010942c9020f11040070306503041d40c0303900c0d04026160070900040024414000e40030b0308540c1d2014034201040414200000c088000c00d0000c034032a010391444000c0300d0903400c0c41c010116400080050b500101913400c559100c1034000b064810800c100d1000b00301c5000b290110b0009555134110008807442510345200c0b00070f0054090701c0c170310412042c00382c0028013a805907015241100c080000444107005480300700d510b1380250f5041c0b07085405020f01581c05220304100d804618820744d801041d000c13903000980c0c1e041c0041d10382103200103800319105420000120700700e580c0380700d0b40c0301491600508503070395510522030503e0880102920310b00305501c0c0c404503410940950003140c20020003003212190503542d544c3c030b0343c6040f00050000d40d80181c2e42d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747748120 1250 747746870 747746873
    0x406120e0c04060e09010f0e030409090305040f08010f0507020601050d08030a110c0f06070c120e130f090203060a051320030303070306050f0409050606061e0a0503010f0807150e030a 80
    0x144150b001501324130a50420310b1410f008042c0c00d45800580309901213152010f500382d188404400d0b58161450100c000c601d20401c3d080c111810b00454001481c081042303d400140c1802c154414524200c0080c803d01240e5070358075040c1e0321250240b14a641042c96030300c141002517465801903a102e08a120002001c2148500070000c07034215404207401a44050340c8911030130410442c0640c000074529040301c40322065a107034200d0701c0c02c0704080c00034003d01c040402c0c6507544a500345000700840c000100405080e17401c05101504840134240d019004034008036072081d4050203803901c100f80944c104450608030f80e03191030454405c2a034000c4070800d04610b240c15950180700542c050000c079a400301d0554200400c000401e002583c03079512480c03074040c0e200000b40001c91515801132084800710307119460300a00003961102c200030400c802c00000341c0b81c5195508007000d507041c1c50350b244100c0e01468a5425059403000d09018a86110804901c0b0321745452142900e5014642d010b000d03210001100d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747749370 1250 747748120 747748129
    0x1020c01120f0518100b0612180a0c2d0614160609030e0d050d030c0e0603011d09070305070b1e0703030c2a0b0406090b07050405150406120e0c 63
    0x1d0301c01300004a05559000800e08041001c03d00055500c01c081000809038000a101e0b0310440142800c0303c000c00c0000303862418506683e5041c0c003488019a1f004281c00c1c94424220a2680658500440c007402c00500c40140c4065168060301000103d903030550410405903042c00040d00300320b408060403c034604190010000e4605901e00c03510010800c0c01c0ca5281c0036114084204e502800707044000c03951f4022801c0001d4440d10140035040000340d214422100b00c0340c0608070f4164640040340000001190052901e45c0300c44c01c80c440c040d21180e0b03107406003219142e8005100150580c2d000031814440c40304800014500c040081403403141a4031166501815604400002d034007003581c80c0007aa503800d0300030088074015086020f07840d58400c820351002c2445542620084c18505c00440040c080100c182d000b10716007604601d901e2202d14015034010115070250140301e000d01208003007841007881e80005e80c2c003550300546918891404402480d070080001e0b401485182c41741440e034140944a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747750620 1250 747749370 747749381
    0x120e0d02042703020f0111070308040b190c0509031e100b01180603090611030603120711091303090614090402070204090804180b030c030715030f0c0906021b01020c01120f 75
    0x10a03009403040b00085c3c0003c43c01c403200c4445500d01c0c2c076002c200c172000180c2e0160322507a0155001600d0401925050545012007022107402c3c04002d140c103e03681642c0e40c10502508075210200d0855100800500000c010f00c00d100180045980c00002d4500744080c980d0025460f6480614008120000b002c0b000540106c140d8001c2000c00d940700035080a2040c01d024032642c0e01080804186141400d4012a5035868145232202500c10007080480410000074502044114018440c243d01d0401c042410710b041c1c96000c0860120780b40050008509000ba220020048000c41c030960505480d4000e0201030350007907404076030007130355002104009038400b805030003d049a282c0301c620703c41c8903840102c21a80c4020a19200341c0c01042c00300c49540e000a2032206a4680c2441070283c0480c200050380940303440007a8050716401e0000540f02d8a60201d50340b4100d44917030703003103038140364200c0e90300b00c5400c0e0413404a0f40182c00c00440d5100b554040d18a05203440100c03003000410b203145403a18011941c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747751870 1250 747750620 747750623
    0x170c1603060e0c090c1602030106031b06080708070905040506030a0b09035a0c0624010c0209102615010b040302040906090203030a0309120e0d020427 66
    0xd60b141024089140c040080d400300840546800c61681055500340380240101000c059007440c1c04080d1404548007074004071700443e8031000c490450f0052411030005031600740601c20000e40c40070009954684160a200c1c0550100d0b190401e189081a0510001d800c0062042c0d40611643d1314010000389010b0304030f48a4081c1d200510303107030007940c1804500c00c0341c008001300f12810541c120402e1000030181c2050b01f40310951044c15041c20b0403c8002c205e4684415000078a0000b044903041c07a5404034107030b031041c4100d610501840320203500385450b07250007420140c0011342441102c40142042c000d06908040309402c3c4804265950141d4010720724030700c000080721000745001001031001040219052401e0340381481d00340d81840038102d82c60140b440060311031625100300001707000c650b5010011640d006003d0700d94800350318002034080d1112220803907451a118200710304880c4100c22a071404032009042401229590f000c201c040d1582004d6500901240740f01418010045030309040943d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747753120 1250 747751870 747751883
    0x230303010e1f0b0a0201291810210b010902030c0307110c03030a0903050f060108251203021f02030606040b180916030c021603081c020f0c0613170c1603 67
    0x900b0132640d110301f0816400b0081a031252400c0e02900a41e10050b440e968400c10920704809565106001c401441c0264042d035108461410303101c00d14150041100314240c060f804552090f6660b4070500124072085900c0341c10203409001041d440c910403401404800d1643c2d04035000725070285e0009043d40d01009141000c604600010030410405102014103030031900090480c3c5d40c500001c4944440821010000e00d89a046485044045200c000310180065200051001a45e0324000e1750355601401c010a104c0c107888000d407810451402281c1c40f5800c083d14160400f480d140b00e14109400c0200441c46800600ca01e401072611900c0310789125100010030f02c48103461840300030f000c4429610340f52007190801006500000580c034140801c5923800030040d562807013510071307046094685940460400307000103418035801599501030301c0c0c12180e0703406031219a1100c1d000d1218152040701e0052107070040b203500100450040700a003001244543c182c400c2c003c0f980310780b0104581160401c4424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747754370 1250 747753120 747753131
    0x50616050111070503040e0709260f010b0105041e080105070c21090b09060c070801050105010e190905040c030602030906040c051206040209090304080a230303010e1f0b0a0201 77
    0x140030090103280c400c2010026210f282184680b10b0340c0c1c0b00d02c1113005440c455644180071030081c0d8410f031480d80050410042e100c00c2403004021240d02070280c510b074441c0707510400405022082d0184519401080e05856071461300349426012002ea03880015480f549451403200010394860a0203460b12400302982c0b85143c4100c2854040c24461b40703035882c1e40320a8581e840010b0440e80004c404d5083e00c0d950742010b0740b100c01e040c0015103240304035845c000703c40c0996000000c61401c15045a03050300c0c02622403000903516401031290200040030b44004070050001c0c10020200d05600c0781b504207000360030b00c072210340d102d031100030a07039001740c0b0031a00c5607001500304010300200584400c050802260b00c81c0400007007004e143c0d680e02d405071010780f2031038024010072400030080088030000c110a8080c0e0311880d0003070807c55000c040700181c03480d10034582d5404400101022007282c0c140c41200e039250300c0503112020a820760090180c12483d600c0403901d004502800e03100c01078911131000c1c0d8004142c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747755620 1250 747754370 747754373
    0x71a0a0206071b020103050c0d1d07090207030e120102160f0209010b0309060601110304050a030507030b090102030606041205070e0f0a0c020705010507020111160806040516060522050616 82
    0x1030410002d000408000440d80701c040e0301c803d00d4040000c415024a8007140d15240c108440040380310700e41482010a00c0c1641060b40d032050b0001c401803030031081084e62a40b603038401400381641b03d8a00c0c010002201700350701840070701e8990b41158040501e00001418407240e00d039040f109041c400015262101d008202c6001c6107840701d02680588050804c543c1542080d0622035a21100030740442d041c050340d000c0380140a40204141e9008040086c0042c059a40c0c070700f07005480e54543d0101303030746881d030000014070a04030500840e0f01880001d13205a107018941031405002120400c0308403550300030b0a0f0006215101d44481500800804004075401d04042c1050307402c403041006500e0640d08801e8080140760703009030030354003000d4080c00e20b1402d0700e1180da820750600541d840a4401043c50940101eaa13450005100740b040c2c0c410301c211080c2a52984880c031003005180724000000e9030070440800b208200c1615800039081040c0200d024a0b210000500345402a020b126412500a9200380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747756870 1250 747755620 747755623
    0x2040e1609060504210501051315020c0705010f090b0a081501180603020d020c010204060f1101060b040314011503060e0c041401091e140f010506090d0b0603071a0a02 73
    0x1008000541007142945240140103802c500440c420155500300c00c4604450072551121036a09581c1e00c03034001c0281c1e242112000d45074440c80c0c101900c80007002c9410343c0c0c6840c1c0c0d52084480300702e41140100385903490300700116001080d104542d07082210001c0000b42c3d149000c80a058128816154032101e841c255007076001081104c002a410041209581c02d120320760401e249094880501e40565910348031022100a441003828510705d640c40000c0005002d035015400c4039000c1220340ea001c00351000070002c01c0c241d032440e0003610001c502c1080f0400c00a80c2c080c401a1002c2c625000124054500215091034012542d1050b5400c54036250304100300c807020b0003580003014044a00b00100d04541d9014084003005001d100c05c0c0300c0d0707603c0b45801d04840c81daa80d8036952200300e0b000d02c45c00700d1901c078080309000165082c54290007840008500c0d071828800380c17044048082c00d507821180d07198903000740120003e084103416004508010a01c00c414024103d01115802026580c55901c039034000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747758120 1250 747756870 747756901
    0x16050c090703050f07110c12010917280c06150821031306200702040f0203130609020103060f24030203041e170c060f061e0103051003050102040e 64
    0x1c0d010107143c5400c01242424840096401c0482890130b80340d20314003640140d16200c8103001d12a80620344100f00380140320f05403c01d04030a4842c0c468415070f0f00100d160f0f11110b0081d0160310309411401c035000040401c40c6240340215141500c0d0407a0020320a840d040101c511201c0700b00b8a0a0079072505100180080040c00c0e80301c40e0780301c021051072190412136402804003502408014003010040807d00041741c000c0c0d01415481c210207800d00001c000400c02c41d50041d88100d029a05080130074884082c0d610a40e84509465500c410f2040d000c0d0340c64400410601d5001c80c10705a9030071002c549c680766882102c0c0984151169150030400b040341c1c102062526548582c101b6004008100002c1c90b216844900104464584204490145801820b00301100904424924081000e841190000400740e029900361400002152514004d01c4100c81e49250301034692140500f048a45502c01ea21256000000b101c441524135100d588503402d9911550250035020342800910040513001041d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747759370 1250 747758120 747758131
    0x702010f0e010e0111120406090311030303071209050a140c04060801090c0b1b01020a12290d0f12020f060c070f0b09100c0203180103020414090c16050c09 68
    0x8200c01e0348180001c002c0030321640401d040011808903044a00410071080d80500d40c81403406454076142c483c001c0414401d1b01c0181c07459807600c1d50007613840c10007004a07809450503036913a2002c5580440076034007415040404503201e12955144030082110340700c1003401e400000c00606070900910041009442c50358021107420f914018110700040d8103d041e5200704c03490f0140705a02e031202c106c10b2400c604c20342c1a961807254000150703210706643c1b14a1030258140260010003104d040f45c55a0060000e200785c00350400c4005029401007460440301540d6298400c800035402c02d2483c1d07984c004100c10803203052002d6408001d00316481e5006102c002c2d402400c90064074102115601c1c0c01d15140c40000001d8540810031002c070322200c03801e1000c0e4192105500f000d102a468000009669906c11356400950b24500b03c9040061740c0300c1e00843e001c864401c08503079450603556040120809003d0710103070b4100420070043c40c030760801000245145008101504010a03031400303014028100405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747760620 1250 747759370 747759377
    0xc060606020d0320030703110d0e030703030e0c1003021606230108150406271412180402090402070c0b0702041416080405030903030d0524130b0a050a06050702010f 72
    0x9402c40803403e44c0c1c16603501c0080c03450086541250030f801c00685200c0c80d09511700c5581841640d0f441f992000000f8454180300b07507000c004d00820140e9464440100c00903882e884104207400e540501d1194002d88051040d400d0003042ea14a55683c020403126502c6a03805002d03481c1c2c100d49d0010025105960040121801601c04280301181d05004044028001403680746d403050300070503078124003014110350242a8034200008045c1e061907050740381c1c0c80c03220001ca84520305044200d2a20002076942a150010130100000a00e00410010f50840d1a103241c04c254240007403000b148000031607100515450041035503640c0c083c01480103641074000340030554110303101840840c51103941c1d00c0c031000480d498402280c1e101c51801c6030541c4262110140c0c036100100352205d10204039841640180c3e414850f910f22044e0440e400000d180211500340e500c900020610b206031402030b080661404402442d20b00301903180e1000171882c2180d5040740b000107001041c03480441d604030740d09800100b200e04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747761870 1250 747760620 747760661
    0x90f0e0d14030c0f03070203091009050307050405151009080106141c03020f1b0301050f01030512030702071805070e090f061302070b040308060a0b0a051204030c060606020d03 77
    0x14005010340041400c007814001001000681110950742680e61520784860819500e06150800a50780d4110b404424400c0d43e0020141c501e69010b13a0031401200c0001d4003030312409240c0400c12006000092581141c0e49c0c000794041416901c1e0017800445101c103440d0001102d08000c0b4035800c41d4995006196042d43c03145818000e40d4516a200d17140510741e0300c1c0000e045600d03141c100e00342090418014928410800c402441c0d00c82c2c141c20000f04034080d002040309075507010344100c52140030304c0050415000b1a940c0c0d12508280c03c0155404481c0d030044411080c0d40d4500c0b2814074000104507003c1907910742c103100007650300880e02442180300b2a416000b0341044000e40c00100c001601c1580f00f000318246100c082e00f41074043c1e8004507040aa041003034502801d0142400c2d40441d1114410001c0c078502042050703c14084d1589150300c0d91700c0d2410600b4019070380c4100134000d00180c06118036001490001220b502400300a000345902034240b003060000e028054420b500c4130811050b0540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747763120 1250 747761870 747761893
    0x20901020309120c03061504110414060a11030c0102070605060d12110c04020d06050f09040812041416080f031602040c090f0f05090a050103020d1b0f090f0e 69
    0x82d12030440d41103508098507403118003118903200d540030015405000d08800c02c2040c3d00000001508690103460620026426148040f410710550090300d0003030384400403064180c18801d001d00200d882c5410400651810310b0403091a6030855220100c09071b400142020410040740655a040f1000b961404014190f40c2c1e0360b4840900500c142000b004090a00500840d000f0844440882c5000e8000c550390812018001d0140205002c0d480c098900400740f01074606180c08407a101b2070300007000504126400807022a1340d5005001901c031880034111400041c00c05001c015152400380030b2941c1050300c0d010341d01d402d01d0402004404160018409010301207400c400010100368115170001e031002487e02c040d501c0c2d0505800c80910707144444c00100d9106203102e0b005080d1001103032822070b9030f500c8001000980b41c003404002d410480d81c0710140c00240c0810308403e007011800741e294104036110708100d85912100d510101c041c64070348491045424080c8118440300366590050001450403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747764370 1250 747763120 747763123
    0xe06040b0a14040b0f250e121f02030406090b0f0a0506013009051e07050603280f0e0706140c061906051c061d1f0e0a0b1902090102 58
    0x313042485c415860380010f01d10089a08043c1c4110b0403a2169840c062214900180a25403042403180a114005901c2040040004401c0c2500744800c3c0401c1c0c00081800440002c2c2d08050b20403110360381c59820400000341104801d501c0780302020030300d0081d444c00c00701c01c109880300600304c54184113092a51291041a1191180355015009214ac2000701c00c0c01984008001142c400b9000340a8013081011000c41000c000000101c0d2804549130f00e0346070303030400100d072000b5038400c0b5064444012202d214001c1006075440040503040001780d0700301001a00c0300303842500440380001d030031545c3e09000c8190400d58000c0c0a0940f00d440d5400c2200e0001c05581e184005444541c60b03020041007558014044e0b0401030140030040c00c900e13908040c10242140716007050104441031410006401c483d0035200600091554802c402040343d1200746481c60810003207007110788181515403080e0940c10404200820391184220502c100f04e10b882140d032500c1a003100c818003001c07801004050010b0380e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747765620 1250 747764370 747764393
    0xd050c011401060e011b020d06150b0c0a0b0a020d060f1d09030301120503040801020a050415050a08060616050604110108070503070815011106150f060a020a0f060e06040b0a1404 78
    0x7801e10001c52801d480c48100c604c096020008d5000c40540b01c00410000503070807061a42d4040c82a40d4000c9407990300403411030280030004c040035408000d0160100d80b419442c00e400c0b2294080051600d08020740060640b4480d400c185403500c0d0340b100802c00c803030700341c00350812110904056004074140802c803641c4038441803042c0d18400007c0e54040341030010620480b0014100d40c4000c542e124107043d4040d180b07400030301c6184058114128042443e0b800745081704c4000046991340403040e5107ca003003100a403c440c600404111072282d0500020b0f1003041028047c03401100040d11440102000405e500c034020308541c01c20001b0300622140b6600910110f8201c00d00304071b002c070f036031041c41c0040340c49050400f00850320303201c0c031802d01202c0c140d4509100c941100560711040c0070361010302442402d01c64050102c005a004041040100300343d108030103c0d061007451701095001c0d85a2902d4036142041d28150f40d10b210b030b4410320a003501c0e80d200700801001074890b001140c1c5499160301540344c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747766870 1250 747765620 747765647
    0xc061215030c060307021522060f0f06061110180308090313120b060a081e150108060711010605010e091f080d1701080319110d050c01140106 62
    0x18451200460155424402c45100b9940a02034503203030b14003070784025641c0f112112140d00080b41c1d2004507112245d01c00c004900c0058400ea40d2803901c1850b0f80d1180204140b00c84400341c903949000820160130240035900060186a40e05500303500d4001c01c5e01d0609014be000846000e2030071880441800006550004454050501c09850b0b03031000c80d06400c611510441c02819150071401013003803a041c0084200250003400c004e220395481400b40030710314805005482d00755010f414202d1002c03c9030b56004001d12802d00c203440303405482c400380100700c12081e005440c50380c0194082208180d8070501c1c01200710200303802801001e15190004c0c0c14042940701c8540688003042c002003054102c07101c038001d4404103429016901da42d800ca041d8603000702054280020300d04401d01e42440d8004100d46040c1d4440a015503c0c0040d0144a4560100556118000d0009007111440000002d000c440b015520301d442d06980c5041c40f54401d421505621462003220003030790014440300358003210491011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747768120 1250 747766870 747766891
    0x2011401052d06030a050103060e1513030507020d08090312040e060904110909031801021c0e030a0b0115140a020d0e240d0c081905040311031b0c0612 66
    0x9107a01c2203594082000c0e202c4280c100000005004a582490340030314101e0740104800c100c1c1d0495214680e40f9001082003400350070f0228804078284811280e80b086145209060091a00a16074003050303600c24002020380d81c40001140340c1019040078803a2095400f001c00d926441d06007408500192124090200c6009500207400207041003000e105008640c100140307221410301e03103511101d03a0796000c0e0041d004000600c0032404a00c0d4000a8000b6203208610b14601d041c1d42785410490302e04040c0095180c3c10310611160340003090020315464060180c0c2e6001d254400c0402d500074002c52401100110410300030005454581c0e404102285202e02a140800441a241000400c00d10344170000010703c078134200a103144010944020103456501c0d6606000c18009510160344202c01207078464a80142e580200308002c086501c140d0b8010301c6400c10f0b50300720303494181c041d01d16000814000024010302c020960301c01c3c0c040110120502c2c003204c4240c0b805501c1015038180c00700c045c1030025034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747769370 1250 747768120 747768169
    0xb130f06141207060e0d0f11040c03060503100f1d0c010e0105120a110409060b040518070206071419080402031204080a02040218060f1c11093d0201140105 68
    0x56171152041a0781c107400200e03180e02c0074907504019410307005d0745520510680c5000b0241c05c1e283e0003409030204482c0d00502800460b9030f03f10018000d0020b25048803030b159640c21804103601d1010f07110042501c1a40d00030540800c031301c0009003203142c0c0c24030320905100f828000340400104000c40f080c1d02580720030010031002075414040702c80c0d00440c0c0080c05a0341c00c044000c601d40d8480c001030012540210b41444c480140442011402601500c000005800c13440c002038110b8021070007481e0100380744000500e089007100008083d001e00e08074400005200000740001c0d441c3c10800da07171100041041e03c51400d480e100c00303a943c07400b070034100900a40d004100f1140103034a405c101c0f810414041c00c1c00f03070341d41c0700d42444580d541c0c020b0007841a580700e0004c0c0c4410204842c41103e191520100c1010702e0010640708001c0d0307010704011179510003100e02500c82d141404414032101040200c07940c04030030400f0003402909603440401240000d071440401002159511101c40742003101d040c0c001c282 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747770620 1250 747769370 747769397
    0xf0a1a030415050609130f020405010602030a120c0f08100806010906090f0e0c01140f16051002040315050c0d0c020d1b0b0406020703270f14130b130f0614120706 71
    0x1206860014023941c840d141038000540240c0200041180014556507400a415896031100c1140d801d807040c400000c101d0401013000b0750085000903044100201e121015a80d104035980c68654240c000b4103440e920b4031000c010300104ea0090703542c8c00300d403180180502030110b61601c0d80c0720180c0d8019410449280380d4030710311440540840e10468078030f0000707941e2604890b000c80c01502ca281e0b0301721258840c80d24000d071568030510a55041d0382e40800280e2646c0e0405158001809001d040000c101604104072526101180b080c1502004150003810f0014000d610252041030310903682682c05000440d03131800140e43d101d11660090780408016222291810300722000c10001003004c07a0061021943c949601d05032180c50116081d03c126075155544840800b21001c06e403080c820741000540a0340401c0780c1240d00103885980380500440b103007240d1b04420303c0503110030343c500d01d6100c1e96407a0244410341000017030b205080c80c25124030348042c070415981c0343d4600c8284591010085055600d54 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747771870 1250 747770620 747770633
    0x20f0105030612070e04030905150306060306040e19020f060405010912050c03120702040c050a020c040903020c06130e01090b01210603080f191d0f0a1a03041505060913 74
    0x74054110310301142c0f10b071502d541042d1741a00081c0e405402081c070480380050f15240503011920600d207003182403030440c0c40d041e0500811b070304040c1115902584402030482c0d040717003c014044c075031592007003800100b101e070b401400302082041029501502080000b8001640c0141040b411514243c204001d030010324280542800401228031b607140c010060002140c41810317000d801168000c80e001c000742d04c2825802c1e1348038440c1591180c09a0442722031340700c030342c030713180c0d200e80d070018006e0060300c0490071344200140381035003c1864a4590b0280e00001c0c4188005100f82901611800000704180fa00050028040e19a529005c20704034241c403e0710040112030381c00c95402560f00910440e02d8412610400e850b030740141c03540042161000c0d070406085481426032403440852a050440d050155100384014561300310780f40764012140003800640404186e48000080c040c1350106500c904261030700c81215840030107801c0c0c1040c1444107004490341c6406c24207402120032820300d03c80c441c1514045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747773120 1250 747771870 747771889
    0xa020702100504090b0603040f0210020a060501061d0402090102060c0c03070204050a0203040b060d02010503012c04030504030b1b2a06090606040c0809060417070f060204090f09020f01050306 84
    0x207400050380d50301a403a45421101800944001c2c0d9010300c1082c00c480300384103c0740012500035160003460a2602e015090030210019403103da481980c1c490401600d0345020340c1c000780d200c0000591403c1c80700d0103030800d0700e0000514440845065181042e0303607000035a0f81e40c028044800600c0f0000781c0f85180070007007080358141c1d540544240010718190340548000d40003200c0540d0300008240c00102d580c03810035242c15607140c1c140c4406086034205482140c10b401d00401122410301e00c69102044400101c001034403c900c681e8980e41c3d941c1c110714000000100c041e14034040c07030070a401e1580e04107e2983c00e5800030303540f103904201c0103280f007040005a190b240a80111070700461060000c1860b022802520421091354280f040720f0740351008841d45002190a8041500324070080340015146603001403040c81000f40d49800d0110a85076404000310801080300e40c1980000d00300030310b10460061220704092100f04200211054001c186007090700003c642c1000400800a0659031321124007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747774370 1250 747773120 747773123
    0x3050f151c06091a090703060209120601080c1f0203071e0b070809010506030307030215040201020705090a060812030c07150f0e0c04110702010c1101050d1109010306081b06030a0207 80
    0x2200301001c1034145a001054a00020f40d20425007038969001e14610b68500d5008200c54001081180c1c61a169640203411030740050741e00c00d04183d0301d10341080c800c00079507010303120300800303003044450382410800300803203400030340b0030328040d114004545640103c141c0d000d190b00310758090382a18400e010803103c0d8040c0c050082c4488400c8003840324540c0d02507550b900c203283e498000c00c0700d43c0f140800c15649000f201d000500603403100c0255a420300051802540013441801100d070b10070780301d10000f03020500446400030015a00c6504208840d0200408584a58408150307861810000c24540c014825514080c0010320981076988140c490b5500142c0ca4029100e4204984900f0714411a151421040090302c41c40c10000001d0f100380c07200e4216070300e95505841c1c003c4010442c4c3c2e1440c3d00c0e94111030000f4103002040c1b0022440b41c90ba400749021541142141a9072803041c40300150446840350041080caa03c0348400085d01c01840041601000d0200e0b085074a0703984480019000c1d00c201c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747775620 1250 747774370 747774409
    0x60f02071502160b03012601090f1202011b05161a070c03090537080604080316090e190204033c080d020702031501061e03050f15 57
    0x1501d0307407264049203603545500602e203040841555a120001140400e0094607020107646159890f607003170b501190103c88042400125506280703440746070031401a08010f03240403202d00c031a080701c82d0b42031080380c03483d84d900541003402d4850094001d10502a0003035517800b00c030300403000c6001c0c4500801c08880c15000c0741c201d2181c7d072402820003000142c82c1b141c21800b04440c214041814907090884502d105458250902e00c0071840344c0c01d004a1140c0c0d244a0006880e110000c0350b105d4042c00440e00c035600a25010b40d0b60300741081980c401e03191100c43d0f402084940901440300c0c0d46408032494000c1c800614042d080320515480000030f100300d500003081048040c43c1c401800e00c07441d01c04e04800800b50600d00c108a004903458981c40c4400c1801002508100140b401082c52039024214860000e4102d03141035030f4141940113551000c3e0483d2002c201854000c0020404012001c0c2440c9074901e000d000f00d0800c0100800d000300003500c0385514007490050b840e11a03c0e60326102070020040d51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747776870 1250 747775620 747775649
    0x1f060815040f051018181211030f03010f0b0307020a08131d0103140f0c2b050106051002030a020a060c020f0601031a1509070e01030609060311100305010609060f0207 73
    0xe04c031342072a203244a205012980f03401c800c10b95882c00d1080c45411303a1941d2070300c5c000304981e0380c410041030304d052088021301483c00190154401c0400141000c0040c54a44940d25414080304c61030300c0c0c0c01940f00c0d4680c01e0702041001200d550114640c01c44030303407118071603440b2901400e4900004009030081b14148030320034500701c102403c10513041e040300e01401c510070204c1c454045c0303d40c990081403403960080c0c0c045e0509075061b0820303105d20711080034a14510b003c524058440001a01011601174403669100e5a0a001c14035001307c0030442d509543c0000c0d032400034a00300103502d480076448040d00d2503540f9640b104d03c440c024000f540b421380715401954429a141c0c648006845038284200b006844840c0020384011841c0c5903d100b0344000410178000c5039681403044484c2d018142400e410141c65010016071505140141800b451283c0c50b030a0668003041c00340102c00d001d82102c101054105401005113540002ea182c0543e413a078580141000c40781c480a0b41f07041040e50101081b4400232 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747778120 1250 747776870 747776881
    0x30b030f240f0603032b0e15150f060706060b19140906030f0a090203031318090b01151b0f121103191806081f060815040f05 55
    0x5900070030000801596040303050b00c4480202050040460340b407901a401044080020f080040c145040700b114002441102a25030101030242e038440282c00074680d100e00790340ca0050b21303c107020551246610702030314403a00c4071800103559220150072490003007200240d032409010003600003202410507031803150b0f5129650b400700d04400409510590001e0312401d0b002c2451102c04003155451500204443e09607210302074503c19459014202800066881803c480140c41c240050070306004401c0302851504c1c94465004288240c0c1c1500400080c90a0f00300000900c42c1507405054810a0072541c001005d2100155592603d96559081c0d488003045176004000340c0085134915075125466000d11003034444030903180c08544050560940c0c105200000e43e5104903d8001c840f10590720f0503229202c0c6800c0e002c0340f004143e400500004111000700a80c013564420940405010304044411142c84d0150082c09484090480500d0000801c1040420790b80c541004003200f9800004010b1400c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747779370 1250 747778120 747778153
    0x130c050702100305060906120c030a2d02030703033b0a0501020c031b0d0602030a02030a06060903151a1815030a050606060d200d0b040c020d030b030f 66
    0xe001244a00d11044441008034480e01900c2c0c0180b4003d0001000354a4100402420002004002c1100c4c4601d05d800d00082d942005201103450207544610b00c00d0035481d007038074180e4404205014581194a8903500103072000920320301103070b8040c0f41a0441200c0c20408084800070103070f07144030010000c0601c1114000064000001d400c0c201c56030f00401d5614001640c503014422070315a415042414980c3e5040782c40d00304447e002c43c00801401603540315559010403a002503443c9000181d006c0200101d201081c07113010080e01240c109841c109182d55680203c180c0c903440410304054035052540c0c07268440c1c00c0f101030340e0075000b001461b94400100c904402550203d6018011091055003040c031030902003850f4002c10b03082000343c50035985240512003e0b40c40510481d00b07490b501c0b80c48040503c80d410714041c5284003084c00c00e623200500c0c0a81000d9500b0001b030a0701c0b4510b0003404c0b50b070b0f1680004141c4031441742401c01040da44d0326200003a003411501211181140a13141c00590342d1241c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747780620 1250 747779370 747779377
    0x1020a03050114241603030f0e0604120e04110a0206040512040f0b03090307050105100e060109060801170a140a2108010612060801090b041202012009130c05 69
    0x425035081103140c0e42c0d001070501000e2442815600030300c22070400202c400541c0802c000015881c030440380340038081300c503240c9010341c0c01409074002541c0d01040000d5070094000d0103c507050310001001d06003000e0316030905104450f20100113005905401380099200c0c1d0308406400008468443c1d1207040c1540040d40703a0070219001c031003900078480c03103069201d40d8030103450949410015160006092803a910020340c03018200c400720307110600034440012001d00509106480d04680c0d00d0301d9514090590300d010344043c0035141442140441402043c2d4888200c0c0c0c1150407000c01e155034802400801c1e0f040c20a140f40c05003510405d040900e024410000d811402284500e18040642122044480d01c1d00c5d0a1990080060896401080050306c40c1202d40102900b1460001d6019910f5007141c3c21502038860880b403001d840f10422040c000b26401c01c04004103240000d00004008008034410284480982c14582c80003255050150305d1b080318080451440d09000c02c054800308130050260341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747781870 1250 747780620 747780637
    0x70b03010306091a071b021809031903020a020a11010c02040c0f02240604090309080601062606240708041707061106010e131e03020d181703090a03050102 68
    0x3404d04e44440c10505030008680c403c41482c4d17070740d150120040381310b80c1c80c000c103166081e41d005481454801d00b0100c60059507000d0401d110040d5036606065059440180b11044c40c00c0601d48103001580ca41034000c18501c0b1803580c400c0502031081c1045005945c2624020406900140351420055900d500804104074140ca140c0031541103280f0a8052141c561020040e0300d03071070034284007090303007414550011030000c0d02c00e0404c500400e4440c0714451520000b6804400041d8025001c4400c00600343c0754005c8001031072200001520b4020080b070259182134a60760701014016039107044449010084d590a241d1200c0059903541e990f054001c0f449991a15640301402114800102d00d4054004042d800c0940005005141c1c601840c901d41c070040101501603001c4421000f10004100140c01300380e01a002030448290304050070300034505144038110405210021804508030000204410b046036184003071018021203200f441c50440c01001e280a0b0041c0545074040704012040d0040d143c80c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747783120 1250 747781870 747781883
    0x20105010509090d170a18080904050f010e0f0402031204091b03091208131212050c160f021f020304170304050a2904230a0308160302070b0301030609 66
    0x3d0b140d0190060700c40c601c154113a800b20b00751500c1d42000038040080c03564410700c065000140781c00401580b04814281c094105c651803000107003c40e191a0910075140c0140080c0458400c81d0704081109203103040c00f81011903800000c000040840d80e041100e46501110a8120341d115655214080042e103c400302400721100c07070061508a01c4d1013072244041c8140c01c00c010b86225040303014140e4866a000d8a4586010808540840458421051903000440a580302c03054200209520821240050328400c2010340800107003850b01e440800e40c001050300007002a0070501c403440090f0340300c6418102140c0303142c04180782240040e0080050021901d1007100f040500003041c0300d0548070b215900801d58031001e1610184803080c098071000320086241c5594581004000e00880c00e10380190b03002100350007610304100c0c020340c20391004c0d0301184001c1d2a14150341b81507980e2402d6900603018402812000516070700c06052003008244000d051170316407507940b035846c3d04280000d4030903c8000c1d21032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747784370 1250 747783120 747783139
    0x30605010b0307052a1b031c02071406070b010b0309160f060c0206071403031501021506060906070614040b130c0e0925080c0d110f01050d020a0201050105 68
    0x200d81507401100c0c401d00a681c1c030a8503104000482001d0300f100d81c882020704121481c0c1203a0040030070060314008119608003900711040003001c042c0303004094107903035001e01d4031540400c2d030f4250002411000d56060b0000e98840503071240109070719025150f00500804240c030300001c1d405581d1401103014880000584c0d8610040341441d15080d001481900304140a40e48100301c03162190200c0748406100a000c0f0b40390060341c1d1500600300800c103002c0820b80d00300205209100c1340c50ba020012058081c005040350490b81c10710030300020380045c0f2490144900058400d0f4660301d142c100c0d004280d00410410400c2c00b2150b01034072500045a0480c0e0351186680401c07100c290814000c0b040c00d6000901c404068207041302b0f21000000a052901035114884d80034503000c1e00c07880071401a0b0001c41482c00601c0c80c0500d0f061400280800c030600034910701d4130030700200d042d107513450980c0380302947c88418884200004031907a00c10b41a1403919644041107203050942e042d00205d04848007180e101c0700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747785620 1250 747784370 747784379
    0x619020c070320150711150d05160903050c19030c0e01030c0b0408060a09020a091409101503080a0e0604060e120106182003010303080403090905070509190f0f03060501 74
    0x2604030945110344c0b03c40400c0c4010000034607030240d607080094014103a02812052a2501499a0080d10f10244a651540204460440c01907082e039451192440c0071030003035185031074841d00c85600b41c0300c1c0d601401480301d110245420000301e40005680c040c0300c141070a07a6505140e03e00c03c100780812906040900310009003c1c000c0343c251002e03559140c000c4c040503120b44403841c0081580032003c980000c00c1c4a0001064030302403048507188558059058064502000c1c0c0c2c1d418604102c0d1203134140351a0402c04988010071010141c103403580901056a507003a240e0040e600490322605030755003d0400103001c11495031007d0400707a03041080c0c41a14194000c90740103805d03120a0701407a04440411001a0304a0034641c006440302e401c21010000444100344003208a035000f40c10940100742d2040c20300c800c041d0b00010003c01041c0640c0100060b00302400000c040340b0602000d54450120720b0000141907800400c46c80003007000740021000c040d90307510040000d0180340f0060b601035140030300006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747786870 1250 747785620 747785629
    0x6021c0903080316110607020106030506061c08161506051815012003070501052505070b091f0b030c03030304350304060203010f080f0619020c070320 66
    0x40580b40e11070307000303419507880310711505254110322080000c01c04600c559a0381d200c402d10200d80219001d5001085140c21420301a25294001d40714078041d0606401500e640c80314102c00b22095540301412a6560020a010780318143c160000600101d8200d43c90207410441c9a21520807500165800d25000c030b03480b02d0b0311032140300c212050136826542c030200030042e62050301ba4114016420381450402c00103450309618540010f0401c4881e83e640703c00b07003e40d8103c480903907580400d0900b0301607d032410340c072002411402101c030001c00c0c0c0d19515003c01d03403551051100d40307101180300440e202d400444488510250030003107d024024001c45e24076004e241004003c503031096401203c04400281c0712004281d04d8902e0601104a40342d42490300e02070301ca174040c025801a030080a01503140e5042c5445124007c40540c0059001e50026008082420000c02d406510180042903046040006044000607101e01051001c00c2d0059110210030421406103070b81c00010344001c1c20090b01002030030310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747788120 1250 747786870 747786887
    0x7030b01090e1006180306090b180a08181804151505010e060d0b0a0b041a090d030c0c0b0a1106060901060203120c07020d0503090f30031306021c 64
    0x50404141c43e801c1406454001c10000c0031940d44088030110580d42d0b500d868044402170030003240c8503440042405040f0751890340745986181410040e10804201c0d660b0003505200d801000c180c120b4142c056086d207a0340340380143c0c05240d8503200c5c00c0d80702d207018580340d600d034940140c0b605400c2d4a455840c0c10580030031281030381900c0068403101640d12500040002642101c40c010350700075102e8542045c542c440c00418001017108008035901d6502f442504240401010860f1520359414070804266642d494003a00080307405003007060403800307241000f41c102c07640b81e041140c0110002465000c61a80304403e0b50b00c0100f4031003941ea01d0b4840c40d0400902c3c0800f88074903401a071080c0301c410038508188481e40c0d04034840c0d85215140c0401580850b1072070351603180c1580d0641010036112994180306035042000c2d00c08848004803e01e40140001c1c82d01c3c081c202c04a80145814810120200e02300704039400760004400048805666140007591100505500361205c40304000340501c1074003c1480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747789370 1250 747788120 747788131
    0x9080c03031605090a0b070501091e0c0603200306040603050f0d081f0302120c0a151e08221b050a080606150a020c0a170c011403040303050601051207030b01090e 71
    0x2281202440d006d45468aa00507040036106550703a003e45100181c40c0c1c030703040a9903c034000c0f11107004022a081103208107206a01075000d040c140520a400b1f940810b582c4942032080c0030550b900d07600c2c0d1901080082070303581c00051840c840e1014424003460000380d4401c0309210340e41c49560a0380e440e51098402d00901d54603d644d40c0400340148018945a2154060b96407014219002251504001250f040607680103003d844003c008c2010f005078003041c48010106501c002c10404908a14000c019120092400118102d82803c1006003004c0806002213a508019151148007400603008040e1043d80308070383c41020038020000d2143c10114400740b203000700070804090302c143c9030700c64844c591000a41030218000e517044050190344051840001c0c00039036100380448003107480200c0c500303411146d405042c4040b401d92400b1000d058000ca82c1d01680c10314000c1900d45441c00140e520303000b158000800703081c072482049481c07540742d031012a0340c820907030b07a48855940e1540300109074039041e100e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747790620 1250 747789370 747789379
    0x50c070b2706070605091903080103020a0603020c1b0411030f010e0f09030f1305030313150e060d0b0a2c070f17220605060a17030d0f09080c0303160509 67
    0x80f0034041845a072103075900c46046800e031810b401400458514003601d040085001c600000700520035405c044803507801404650408500e45400c51890342e03569802149840701e03400c600c0c5078108280e00c942d04900c4902c0090741d8955100e04110300421a41d8070f090154440302d400840014103000b400308880c0c3d000e123840001452034a103844007141c0259104544000d2404195440080e441e28100001d16400c0c619503650480c86081003220000c4c001c8414004c002c0100035808031b01240d85034412140c040000104c000381c491038100100b05140c610317034401e18002c201604440c038a01c81110400842c0c543e000c84120196a822005a80c5051408482000a180840f640440b007112001443c3c11002c03030b10041c040c542c84003102040b4010080f1084492a0b201d009201c41070805502c64000380c00d24842c5a0903907180e0100c071642e070b4000c510300410900d440b101003110a103031507840901c05541203e0303990760360041e140c1d1090303403540140e502c45401c03d4440e5620741014030450648110391002030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747791870 1250 747790620 747790627
    0x20f0a0b0f04080c0f01360602010c08010608100501051305040203250201110405220e1e0703050a032d0302071e0b010b0d02091309020a0e16030507050c070b2706 71
    0xc0700307d1014212001c240740743c00314000310021150300b0368a030000401103a4004142041c950310010300c000f078180e1040d010b01256805105412079841200c105494081c03070540c0d110b04841000d10300c1d4a4040d4001e40e00300e0310000a12040040c104d600c0c2d2884c44410040361200c22203800128203c0b103083d01c00186d090700c1400244090f20b00854120403809400001c4200707a01d0f1010b0070300803a0701c420316207609981f102c0140a8003d0941c000d01c1109001e50002e8a1100e02d10f0704c0d00b030b4840d0724912000f03040040110740043c000050a0781c200605c0c40c00019040b441030420f2001d0000e41c0320a0007030760030380402011040045848000154240e0740140c1c010380302e07403809243d0062a00031054410b4079a0302440025000e4507441403100040404050100381141035005000d040d021640041701c1e062810401c021b020b20550424100d404e14034907000881e5510541304446501407001040903c2c002c18400041c01c80b5004007500748840c11100c0c040c0020380e00c00b02007034140500207031240c0050050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747793120 1250 747791870 747791897
    0x110604061a0406090b0a0506040e0a0914120a030609050402010c0809060d0e060a0b060f03060f0f101d04021c0510080f0120040e04020f0a0b0f04080c0f01 68
    0x5801101e0340d00031004100c80d040720044001000d4900380d4015006280d51950180764a107000003116000f4041070700c4043c6028202603102154007401042036040381e854000714000c100030945544003005001054031400c02c3d816041d05243d03407100d0b091200203424400040f170840c036103100d414041c80c1e050311044803600d80d660741c00100740c105030f605680c007c0d030520100c99503851074015061407031300f1480581210314002da007030021500030828480c0a50703824410070307400e1441c9208480e00503034200ca900c5a4000d8040004800a00ca0350541d03400900b6909403200b482d410000140520002000e40d039076210000c41800124040d481d141403e40322003e041c54814000d50703000641015090a003901d2980e1030310701c55454481c00e440c1c08041690346071112848100040b65010070808481c04240c42e1901c0d05801d089240c50240000c1e01c00c0e03403e0602041c0f1640d503031990b14010800007044540321072059800c05100c1c2c2080c456415540104029400146801403a00c030014030161201031803c2440c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747794370 1250 747793120 747793133
    0x609020405070f02210c0f0f06072309061b060423030403061d07030c08240609131202161502070b0715050c030718030b060d020d0b1e07110604 63
    0x10010300e03a9905c0f01045109105030050007020f25900000c0e0081084c43e4518850518180005106804000324401d600b02c0603414102461054145019496141d041c4c0f0000151140700e06800c20440c0c5441c84002124064040b0704240f02c0c1e405603159040c11941c2c100c0061007400d0300c000f64541600200030500009050780c1c4900c218a2801c40c1173340001501c00106031070280740e50801d40e1443c512040822080000b0030410401c0402d51111040c5a0140071141c0d503c520040c251900c20882003000034551081c0205ca548504c2e0081101d6640d81010107000c0d489469098542500c0e00c87e50304085040070528180d03da0000aa90040410724544061810103030803440d01103d1001102501000e121941e0041074000d44a000030165a400c2c02d80000d041c0711844a200300b1003442d428000c0001c0344160b41c401d640a030041c0d400000710041480001c4030103020440c000c0c09a09058103100903201c81c2140400681990345441015448008060ba42c4200c050801c680b607510a1000500040c81d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747795620 1250 747794370 747794413
    0x60e130507080304030303060e15030714030c0d060608010b1f030504020d0b0408030604060623180a121b0305070303050912030309060403030b04090215130b070609020405070f02 78
    0x140d030a4031420380e150001d0900b180e110b540f0035400261140c10030302c140e1144484442e002030180d43d8200328003030100c010a894400e60700c102044c0d6100c41c0040c00503a2000c6c02002c0c9101c0008004203a500030070314089008041601841007150720700759100d161414540b86144601c4402201c3c070500820000c011000f03040000e2049801c14140706000f00061417840c6d040d4096445400389548910384002400101c66082c4d10100070051800380d61260034840715180b001d90988509215a00e154402c0c1042d40d40c0c000704030107a000000c09000007006041e00c810160b140c0c1c803400075040c41040e40d401d81240c0c400039000190030b030340010000304000780c0031b07100600c4041000760450303898000d054a001e085400441c2e600019411040810080592500c5641343e100030880f4208003021554000c03811a02c060340302c11424041c0081e1220305c02c0384441ca58002418400303050780d80e8980c2450044082c0c419804124000e5040801240900c0e0054100d6601080340d80c0c02060320208403418280d4100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747796870 1250 747795620 747795623
    0x9051813050d03021e0a080a3b0c12030d0c0210050103030c0b0a020c030d110c0610030303050109060302010c081305122508030313060204091802100201060e13 70
    0x1150010340100148080c0b0a45007146182d480068440441401079030754400d039912040c240d10340400ca00142c582e04248050380002d152400092044100014900c40c194000500d01044075880c41c88041d4940c60031740040c0010201003651103500324103050185160151842c007101d60410300250400240c00e6210880802c51fa204540c60700c104c2c10b44440c2101d070281c00590006481458a10a104003a0720003500082c18200440c03074038044ea000d42d03840740070b050640c140042e1190902120384c02000d040d0b0f0b500c02010780a882d09401c12138207014140300c1d1440200c0101e8207200000601454500c2070004481d010384921391010540d650314441a40003c5403c40350b10b00092012070251074107014030340c0c02d1080b00b0003480001c0741aa1121f280b0520aa140300140070310b80c4040c0003070400841525000750240c0d0184c906442a450b003040a030085820144502d45040811024040700c00d04030b001c080d00a40d0b01842000c1800004c90a0701c040780101c001c00c982c0c44000c1103680700c45852189074103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747798120 1250 747796870 747796891
    0x1b0c1f02183001090618020f10021903050d15061103040b030106050313060c0e010e06041208031b220e040f0b0a11040b0c0606180a0f0b0301090309060906090518 71
    0x4940d980d1131130100c1b03c06510240c0c0c040c05441e081411030070010391213601c15000311049140d000b1201d500075900d02d0300324000384800409040401c100b60046060311811581c0d42d905210344000c41440300c49c1c1198903c42d100014259045e4401145000710481c1e05540301181401c0c596828454244c40c0b952000e005c1c469000c807482c03250b0000c01c40342d200c0c400c400440e03a0f036a50280c1c84000c2c0010100720703400020340c0c81100200800c0021102c1000880b0101e6444940c882c1c403903880d0b41c250701c9514000380940181d2040002d00f0388000d1400c056581074178145040204800e92035080343d005909044a0040120364460180e60104078800c07022a4010528500410082e0041e50220b28540240d0310411500c2004685030320500c1c814000b00da4001402d03070341100c1c1d11415840741c1c01052005450296081c0d5540458500c02455400c10086d40002400074054010303186001016002d0703e105000024a411401040c2284a0900203040750b030000c12400000b44000e900c002d580c0405052001e01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747799370 1250 747798120 747798131
    0x4110a0801020d0608060612030405040f020705100c20060a091b080a06050a0b0a0303031a0907110624360411091b0c1f02183001 57
    0x1000030900041000c090b030340002140552a1280c5a4605800900010300c10b91400320411004100001510125a0110750128460203030340060700c024800d2100203009030180a6000b4880c4c11a5042000008840d507030300885a8a00c440c103e20300302d14155050a00c1d00300c14086010761480740c2003814a940249517003074810b20400c6038002c91103a20380c40a801c580088148105110440c4202030303010075401028060080070710000b030190149404000d06141c0d40c0c500990070071500c0c0b1642143c0d614040c1c4080e445042040e009800440040c698070030030701c10a0300258141c1e06c22440701c0c14649400141782e50384490b070310810034141460b4441007040f108122500540b42404200300401d032488000303c2e0b19034241800c114071003c40d281c807100d00542c020418040c54480c11204034103003098144030300f40c0b5415813202c81c03800c2c4080080601c52070900c41d505050048941d60003030120214080c240c24400c0900c00600c228403411300e10076a40c038427a1154001c41d2a08280e52000301aa0b003d000040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747800620 1250 747799370 747799379
    0x440a0819020301081005010803070f030c03030e01020a080f15011b0213050a1509060b0d1e0509030a0e010915080403020f0712060605061204140a05370b04110a 70
    0x100d030800d84c008031442e4800c50b4115a851070510510b40900b200c0710156161035080e48544100c0d20803100c0040404c04082c2c0c41d107003814465031004040d4100f000095588444500307008000b00015280f00800f90300d4000400d041040c80c4640c00301081c0103840d8403040800070040c10b000c10340994030998201c00101500500c0c1c00e0548104c40c0b080461140015070080a1840f050b00f0078105d03001095814908442030000da0600400e40d0016146850081100300a400210000c01804110b4402013414134060002201c0084017401c03140c510b0f662422014800b01004550700501c0e44160042e00d2405804001014881e030f902d664800d009004a91a41520b14555480c210803a0302c820b0340d07800030422110802c46140210300003007400b240d2032401c107400c031140400044000f0f44000d001c40c40110b2880c0c503410b000d100c0301841d260010181c64200070501d80d82c4049088040071034050079915107140c1181c3c1c1d000c01c400f00e081600f006c1000c00c65030300c6071755114a070703220945865800f103c034443c0041c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747801870 1250 747800620 747800671
    0x2040204091416050904050406090f05010605040b040c0c0602070c030512090414010e0a0b0325080c0d0b0c090109150302120a06050f061303440a08 65
    0x14510014001041402c0300e00520000340d01900070964071084207180904541c0c444213035010b07060111000203480c1c842e1302d820700003022031100041c203400d124903c000a21606500000c01c40e9010769052014582c1e0384100011203a040c103a003000f21700300c646c8c03a10103d203e03513010307118141c40b41d1244060191240c48a03132a11492065000c11a54000b41011050405020700350940801c083c518506505010174148000c1c4020595900c041c2d83c0d00b0103001d240e8082040360b859060060340740c4c0180400c09501590500d0714041c0382214401e001c034400700ca00703158000301c0206400c044c102c0d14a1f1102c613038009050384040445410402404004503c0b10040781e00d48403489000d4034016940d000301c2e02c00b04982c480090841c0040761600c01d080090b511288140f1f81c118004070703a4155280c0003407003459003d10580d080501030981c0000f844005000c00204202401c116441a0b415a1050300d0f104e01e80d0b00c040d400c44509000c1c00c7c4000b54000b0b0081c0c0d592604507a0800f030100b400010807090b00b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747803120 1250 747801870 747801877
    0x9110412140f0304090c1b1e1e03030b06040f030b090325060509010b03061b0f040f031406071d010509030d0306150207050303040e09030c030a080601031109100e0d020402 75
    0x80401e0f040041c0c20000a103442c801c101c06a100c0b801d10b41c101d281440107400c507200c0c15100241011b0b0496002540100304000b10301201c03a407110781403403100e1900c0d00c518000c00c130300501200480e2801044804600c5c0c05020344048503007003100084018115510302411000c09004650948020301c124560140201814460760140480071a1198500e04114041d07030000b03810801982d00d080d00c6052151000318160380e100d0102c103181c0c0403c5a6290360f8000e94801c1d0343c06603540303100c04100800e24a03104070140086a010b43c01c449062001c0c82d101c240c951006070f81c0c010114020b1075200e91080d180c0c5c6502d03510800141401828414508003007800c05644a21520000e59960002d00c07d400014121043c0e80c180c6d03100a200590a10003c250f076403113540101ca00c58039414000540d403180800440307400038959002d49807140300000c07000d006030b1401e94009003c82e0500041e2401d1242c140c003600c8820000800e0803a551040c0041a640c240c100c984494001c40c40c613a1a0002d41c40e10f0008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747804370 1250 747803120 747803143
    0x2206081623120a0b06040b09070f0305060a08120d061707060c02010e1c0606080109030e06220602010f0c031a01082e0302030f06060306040b1306091104060911041214 73
    0x1c00081c60201c04210403582480c7d4182d200d88800750a0040e80c40e4488189a12040d05050008154652800158005a655114003000d200701802c29000e888000090810084940011f200c10b5032160140120302810022031804d6034000901006880e20404180701c40500606084608102070f0011990707581e0140d01c2c010404204036182c1040000b84d00c0f03914000e04607880200a03540055070028190f6501c9182d40d840b595010804614190180c0c10700741c07a4410b041c2012120b280d03074a070080d0180128005942c0d240346800503c4552501034054018080081d08425030b594084030019244e038140030b8809011005844820001150440c0d0801004481400102011403844c0304040c584940340750441c01907005807051008541f80002c200b60480d5200041000a0b81d0300001e1110143c247c5130080c05032410080c102c0c0510404140e507041078401680c00380016510303403140b4810b0340c501d8229421010000c110401c021824000072103007040c4180c103c510700c4441000903d1501200201c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747805620 1250 747804370 747804383
    0x50906040201020d0e0d030e1201021605153601020408030702040501050a1202090702030d090812092a0a030c060e0a060e0603070e2206081623120a 65
    0x2880250760f01002004040061460a00b203035407080d00118220f282039450040c2440328a070213010407681c0d103a00030f004041aa600864585110b0140d4801d6150f950400740c0701c40c010310400c0110030f01c201302118415652080b8403908a10000c40e8800042c00415007010300300c22100d01081013110a0005000a00900b0015511640301d40100001c80b02d042c0c1c0140c4c4100707170110040021200300520090140d404456200481d5100f02c0f09078114880c22100352442e514121135101000740040160411114861a5040ba581c52080301c950312a00c00041d91040c5940d5414007954141c041c8008510450180008007820354941d5112040701741600584c0224004405465090a00a0002d401081d070341c90b00102d0840428041030340c070311014084200700b2842c080e0782c80c0541c441d000800e15244800088106003004404100c00030701c2c050040321210302642e00810840e21b0a031585c0300a691a0104044910151210010410910b076008a8000307180c2c550307410317094509009089a00c0e0007000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747806870 1250 747805620 747805633
    0x2070c030c06110309030604020411120717090607080f06041404141501030804050906061b0a060615090e2206050108210a0804020f1306080d020a05150a0f0509 70
    0x4028061184911030310f0720580c0180001c00d0ba5aa000401c40e07005a01030390001a09507685c1c11207040782c401d00159109012450091040c1c0701da00540340d47d40c404050780820b801d503d1f05801c2da0344401d82550943c0004504a001c9400c80c0250032a66030020002480010f4898801c030305154071006c115400d45070030030010610030088030300380b2101c02daa5a0703032001000d545d819076813081040d0045006483c0201c41c0440061880d48501e41103601d080040903200038801c2989081a44d125034a040480d240c41c14170000040782d8a03854400340140009803511902c0340d040ca40c0814410400624010840c405416117103070030050004000c10150082d41d01080660514064501d4000c3c00f881107041049140c0310080304115260564002d405240307003000c42034130795000040008004501240d413081c6030a0081009210960104044444590036a0310319000e130305040e0b803910a8000080c160390410141100303e2040c081c1b899903c114464800a820b103015000383c012035400f11080c24190340a039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747808120 1250 747806870 747806879
    0x90210200a0321060506030703020c070e010b09040f11120406140c2104021e010e10020a1502040807031511040f0305100e0d11013b010509030f0c0102070c030c 70
    0x4031040f07081d04822a0902040785085c002c1421848004e001b0820150b011594041c1414180f050030002d14801c2403422607540c656000000680c4040402d80c070035890044a0445074106000e1450030a08850019040844420b944401d81b44014001c40311203955003040040d0000392895103015105400e9105e4a0f4000c0d0090b05640500b03090560030715958002c1000011703a644142c2d41d400c440b00121044820750b80030f0042e25594441484c0780c2e03015030020302c0c15040b0713540010700b211001d014a80301a000703801d68600c8000c031303c11401400f00302d422102040c8041641510041c00c00541c0d1540007600e03400340c024080c40c5800c1a00040d450070b070000010403c0c083c0410810b40301452403502042030320100c030300c0703075940d10703010741c2e0a2040c40103200180400940c298040c0090020810411201b0105403100d8580080c003450003541c54002002c0c1c4c000303601e4051081d43d2068102400030f43c0b402d010311000f80300c00c6d0003002501a0540d020000000050003c40038000194464400b07509102d081 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747809370 1250 747808120 747808157
    0x21509091b070f1406040b1b07110402090d0606031a16080a38010f0207060207030f0c090912031d121e0a080a0b04090210200a03 57
    0x180c88a0003007035900c5032500342151003008603120180d10101c0820400c00e240303410f150501e480301000c5914052402004280151007000710b03c60744170b180c091420501002500b2600e070041070800b0f00a4907484d1000349030381c2003e5004012005004009407005003069a40e0320588005820460f00d002114052804081c00381e81d801c0d40041e080800c0c517044000b031040043c0403400062035181c1d182e441d00d1a0b146d81c1821400480b58444402c041e10b40e02d000d040640c0d0b4400c00c04010010b00103100008030050040c8041009001d0310700c541c0c0901800362446c1c03142031f600c02e800c4809860b0042003660002d03612481d0703c0f90700707400391044404104103070141e00098211010132901d001c0251900c3c03c000d04025001ca564003001e04441c071229180d4078100c2090304940d40d0f41c1507032000100000b48165596800071816031140b108103d0501c466180c51080c0400c0d074092807002500f0405e074021304005036018614400b20820112941985042861f100901c0e05807007400a40114418080140d0b54151 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747810620 1250 747809370 747809389
    0xc0313060207051c47010b03010e1f090f0e010605011803170702060309060f070504150e0312031f0f08060c0a0306050306010f081509060106030c020703021509 70
    0x84500101307000869070700c00c28441d540301c00101544510445c0b81600113000100310040b040310190700107a104141001180c81004078102c211020740c21000144042d901c0085a05031b482e010f039415882d4580c00600c0d002180f44580c0c111800d81c0c20344000c81c0c441c10b9031044c0120f100395210042224150041018216195900403c1c10098071602007880c0720301c0c0e102000c040300d50010202c008241000e2101c0014010460b00a6001c40b000003441511000050030134000d0b00f141c03100c49a9030310b540030141c0f10340c8110f10443c030b9610080074180315054000c050346001c40c0f902070240e4503101c155121803000781e13204440030615800d80d541000107110324452903001420b002d0181c941190f08003426070ba52800c00402c0c841b074a40c0006002c81c0c02500c00d420500060001070111040d1396100c01c0143c05420050007141314034851a40c0844003400c54151050162030000050704807a420548210043d0200e5000b1005520030b14000000584034000c400c558a82c40300d80041c2c96a4000080181496 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747811870 1250 747810620 747810629
    0x1113090605090c060f090117040602030906090a02130504030e04060603060f05241e0415030c0305040b040212150c090f01080c030a020304061407020d020708010e0c0d080c0313060207 80
    0x10f0200410800301d0700c0d6001141d139040c1c1d94400c41900d9181050040b226100303003800018148480344140001c104a07030b00514024030b06c40c0140c0c2e04071794441902ca03984202001e0040d502189120101680e60030070b5000f50742041c0289808084407140b0004034003030b2042a441000005d075500b0040101d041007a0031900540402c980518054414400c0b080890750000340303581c0307041c42c00902c01058508079001910624092190399448135502d0400340d00c1d0414080d00c48000c80c1c00c0450b12401d06109220782e40c4280d900c8650418581c40325020b02ca24a0005101d50a0520509958910041050840510800044642e503603154151018460f52908400c1c03d00e042c803aa4605010175142c0704821340c0d1307106095481c010307140e69842c1804000b4104050040d5201c402e480b0500603610b038041103140c040510740c8c08070755000da0341d03000013400c03545880c000b03c07169082000b001940c1d10f00704c60381205007409900305606000c02950610f041d07502040101c0c2000410900c108070003074060048030000c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747813120 1250 747811870 747811873
    0x815040519080d110922110c102012040c06050307080f150a03030e011106130f110a0f03050601060206190b0109080d030603050f0607021207111309060509 68
    0x50300650341e242c500d00071540300c203842c2a16a201c0850168240e000e40d0b0441c07074010b02c0c550305041a8800303180c001c006040300d54042410211340c0078094000c44110748980d034000c40100b6100c03458516080051130507400207020800a0031401c2403588002002c0c20003e2015001034600d402e103403078822907030981c941c403039001d00c40140104900d55810491841d03110000440300710ba0f6540701d00ba605030a40c10b205130b031a40061000d4022040c9a440103041280881c2a00c84003a982c0e003400c280781d1742d49000c4400300c15658211540c0c43c0014040b1903030140321841600e22800da020f0303040000f40001e1103a000910040ca01030000c00c140041041030500500d014005003803076003041007800030fa0b0602c00c1154021103466002d034010b80e0740302f190300000030000c076000e0310a014229440140541883d00c401d803480c2c840c078007207090503503030128505025250039001454440d1203a1510080c9400590007910040400c1844440a44030078100750004294448002505013842c6002c1d4100c40c2d0207800201c56 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747814370 1250 747813120 747813163
    0x140f1005070f1103070506041110030b1020061501080709230d12080a0b0f0f010c0804270c030b0a0303050c0c04020708070c06230a050408150405 64
    0x1040d4008071480c2c640140ca18056000b804294000d84c6503209000000304144100c50802c02848183d2054078071007007007101e003040322008c0401d0480590303080c0c1070740a90143d4120603a81c201170055500356038514a003000301d00301c04c034400d280b98104401100c48a200f400740c02d44000466038021b4640303a00c0305603800c104220500b89803545c10316801031007103d0f1110003203000103d402c0ea00c100c501101158045403626416806000c002c01d04a001d849840d186410500078040628100d0310052103100064589400c400e60b0b5001150b01c902040e500b030300c400e10104800f0034141321241c000003070528007107000161100c011010a0850f0140320f004010107152162802e190355800303a07444200ca4040c90f0042e02d401c4030000d15402d00714010300301030340f1a200052003401c211240c0d014200440c05456512040d036641e030426107881042c00e001c4045800da00302140042001c14010b400303c00568a03041e82080d413030b2601d0524190303c001220709405c128200b00001c00008100306100c03107098a1240e8607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747815620 1250 747814370 747814381
    0x160c09020702032e0b04110307020a0318031a0c0408030a0f17010b07020904110406060c06051501140a090b0d050a052d090c06030c0d0b010903150c0c140f1005 70
    0x40c00a02c4d403040b01d04450f250111034006940d26000420124010b0381c2107543c07400c050038069943c10300d2140072404a10f29a84040e68a00002c01120031250425210440008101803070000d036a002044c009915100f8000442c6205040018051003245c80c1c44011030b5008520000d040d1920600c25401104c15040041c8181000c01091f0740d809a03043d100081c80e5241c0e0f152407540c0e108050703851908145418000203200d5031103810b01407418011a800c1110351507407400d02c0070901100f640c45002c6004818a490342c4424040249440c04041c6040700d103180c0ca42d04404666806090500d804d0764445040c40300d100d100c1d1041d290001000101c2d002d0708031601248410901030200000319850280c0700040310440d050050000d0604010700181d600d01d03142c454403049030090006034003107a290013442d040e154000c80c10311090307070380110008407402c1c1041c018902802d110747c0ca1104024020040000180460141c50b404200410241c0104609100d400b80741c910340d10480594641408140103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747816870 1250 747815620 747815683
    0x304060801091b03020d110313020906030606010c030f3f0c0f051c020a03020309151005100e03061008100204050603010e072001060f1712160c0902070203 68
    0x10843c0c062400c02588414000c00540000c0c9100386502d003a1020000801500c5540180c400c01100d20855114925444070001e1694445007110400d001c512418407040129000d06030640a285280c90078081e01c0e41a02002d405c070340080d02030304080581c28415403180b080c02145204089522103010888c1e240c88010080032000c01312000d901f48400010311001080490400c2e87c0d90340900f210955846d81400d0000700203500c2224541c016018462a8440320000c0b01c0700036004001d00d4010f91100d45c1403030104040e0010707610b0301038113100085860500c203490070b10816115503440c00c04081094508018542800904211003100c075104010038082070391b504095a0540c0e01c1c4090340c0c1540d54a01c0d809591060171011401c0c101c4c0e0800c03183c280e040005401c50010b591301244c0c5c0303480441d5540030800d41841700c000703a080f0b41c0d04030192400110002202420080303054842030808e00d042c948030000c000341a500706402d515000108039007581803c110060001208940315040e480020f225070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747818120 1250 747816870 747816911
    0x301020c1b011209050703021207030c05060a0c290133090b070804090f020309060612120c010515150403030c0501020f19090509060d0209060a030c0305030406080109 73
    0x80741c00c0409042008160303446080c5a2125041d0124100440046070500c1640c07440c032131104034071a003450718148040c08404a0014212940072020040c030f07d09110410070726400003e15041040042c01c0d2903000f0400d62010008800f0318098188062041034104001881b0140c124003010b0702c84410704e05074401c80702460382c201001107503403411000100c18200ea18041c940d000200d87ca402184420900034084018801c84150380c030104100f980e003103003480070307070104a9044400e41c1200001035001d040441c0d000a0344001c840503203650001058208600341c1002c01c4020050395100708200300007007800d12002c1e80d201d0454019585a03001c04403219a4416404002c0c00c2101c8076840c0300401909405903034040c104824540d484d8405142c3e542d00003c940380141c0c0c00500149000100303400c01c07404507402494050518810700d1615000e00100c22405052186c122013542c10020101d504908100051445500a59543d078075144c00101905810f0708004805898100a0188005134141c207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747819370 1250 747818120 747818143
    0x170c070b0c03040306051602100902060d1806020307050a1206030224040b04062604080301091104050303121f12060513020d060507020d03020c0601062d031a0301020c 73
    0x29990785007a402506800c50095a00082840d410f18003403000304040341500e4407003841c1660071118041d00c5400d8041c1603031143c40010307400a10801881c84101001d8100044070b620480725034001500594418040f6403040f035140f0b001410208440e840c0c6076020355030340b00301c2e4201c4500740324050030350300090340d24848800c02e8200d0642030700c1300346000c4100b1820b44000b010764003551030701d55980f5070014145011484500c03c2030761005032402e01c82008200d41c0c070301642e0007003106400c61b0b080042d4034008000a820004811078180300028075954104024100301002441034040c1d401c059149000322001e0286226100e54028014403100070405140f040540d0003140101e05600c540d8059004000d2202000c3e40000d5066504428000343d6001140161056404c407a001850a84114100d01407103030b008686412400040081900c114116005541040707003520000044414821007040e4001c80440403030346500392461114019503000b05011740640c025442c2040071002c45403221640c170341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 747820620 1250 747819370 747819389
    0x6050414240a0807060504050109091b0f02030c190b1605030c03040c0305030706240315050601020102090a0e0f180d1d1201020c1b090a050a02070206040e04170c07 72
    0x600302e0b6241e410074002060594180c402980d2240c40061060b84140200d9001c102488400140401c01d4070440b42c542403290283c1192400600d802c64840c0310603140b10045100c01c0c040b42ea10307140c05201480702c0c1c0da0790006149201c103091910b58049a80184011352054a04d0029401c1c1900207048a40c0062204a500c0c3c0e00c1d41c071451f06001a501980020341544400305002c410400141d2288003100401c14140c0704031032084015031304031029408014200c070040511031068913019081a5041801400054146801c95001c00c0f8840100d911201c4696000818487d6810501714101c1d04496004200e0351450198003c03240e0300c440c000d407881d04003d0760019401c42e40044c501504e0690f01d008044140420100c080e83d8080c3d00005030325400340c041e085010900074607081140b080100080e010100035550380080d50001c010040800190580801880006036220f0005002400490f41120324a081504041e44811180c641001034036a0802885040d5000010362001302c40c11100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 747821870 1250 747820620 747820681
    0x60305120313150227060d0f18240c0905130e011104080105060907020607050c03041e061b111c1520190f0e1306050414 53
    0xc0c1105002c014080090b00803030315003101c800121025001030011180085e941022400003020844007500b07035a28040d40802c04100c4100c02c2c50060f082000c44000e5954000354a02890184800d00c0903250360031a140a120ba40908405103401580215034096500400009849250251034000f032406094030a540300b441600c407079060343c0c2101182105220090040107082170503141c59030440e0003005001d508000003e011414901d1600380306941a50050019468500781920b181d44404607029843c0010800030440c3c680d0714032808c001e20102c4015a16a602c0e161009046c0d9406030040b0b8031030900c40800e100802c42c001e4426402a004a0741c0642801500a0b514042400718100824a11480041c500707550595480251421036504054403070079284040840d45c3d10400840e8100c0810028403031070b5040c4a44500104242241800c2c84541401c0340000ca4041402090005c4580c54070070030301941c00d260240100b074180401c0401494101000e2042000b1495040c4020142c3c07142c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 747823120 1250 747821870 747821881
    0x9092c0703021305060609042403150b06070803040b04032006010e09030c070308161703103804030803090106150306120803070e0a0e0f060d020d0312021911100603051203 75
    0xd000527031801802017601144a0362440c0100121007483c1d000c1c400103150001d10710041c1010401c0300c8100358008905807441da1599150680c560b070140065040202741034030850201c02c042c180c003107444000303401044250b03d4200511220700e00144011090f400a02c4007031102d003030000d842016030f980a08015181c1c00b268008030301e440300680000d80507180080646041c4001c1400450080019241d500c4501740c503420540101c4440301070350b00908000c100741d007035240c5080001000f42c840c420001c40c603150f6a0b441c4e400007604151601c8103565961582000369000522140c1188c25050805100e0f036407414181d8044da02c1c16010190200e07100100088482e44502d581c402d84000c020300319003007d0740710819000241c104480d00030390300c003041c1d01040d09880c1002c20003541a42c0109120780808041d84c04559907040318100042c074503001d00540d80544203890302003240903019a02c100103d2181c840d560b25008100c0940c000491816805001150000c02d40c007062603042011a640c07501c85 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 747824370 1250 747823120 747823151
    0xf05010e0111010b060d1406030105040c0909081b0f011409070b0d150305070603061a030703020d0902090a09050625050307090b03070c0b0f010609092c070302130506060904 76
    0x481013913503445800012602c1c400b064950050301a2154007120025681d5440301381404c030b030f03001d0314068069808007808101c5600035412000c181403150310704034102491000c507482c481c907142c0c08609540c0c0161204002a07002440340341d440e140d040d001c044040c2030400c0340329148d00c02c5010700784203660b00054200044220340c02942d00740c1694205034100300c0e03990602d541c5a0300a030145100003824400c000904401240710341d461803210341c0c4402c1c41e5880e041001d500942c400d5448248132074540110b440542d80d00c50406106d40d00b80e09011034601098604141401001000e00c0c1810f0f0305903600c403002500e81c0b0100d03a569411410810f542c0d0b03d038110282c460400903440803550b08400010082d0701070380541c04003071080c8588c2100540d07840d00d94105c44000801d000d00c40004840c014100010b409a030020410307004030701c0c1c1c800641d8500720701c0d0911011150003d41042d0340007620400c214144440b41204124250388108445e05213400003c10510840c840c082c441d540362030601d00c035840d5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 747825620 1250 747824370 747824381
    0x31707030c0210050309100510060503040203100e030c07120b04060b0111030f1306030209090a0c1b0c081204060c02010e040e03030a050106090f0303141806030a0203040c0f05010e011101 82
    0x10001e080d0f01e0020001caa00408650003150a44c08500920780c00541c0e0302c1d05801158040d002c120796086080342003400480712900010303c01e0f070b0705204004414098000b20f2040480400e6883c002e03654030031146030341c00e241c0360b00b540c00259800c2d041144240400c400d0092207802903801800030802440d0760004030340e01c1c05403d60700b000c140400161b0202c02c0301540c00400f8800100004051034903907a26082e4101e000d0305801c150403030704400010b000e6401c00c0c3c0c8181d41c8603509007459860342101141e00782e41c840d0714000498807080b420009201002d410005961000103400c03060f8940307410454000c018800c807810003418030510750f0161003141d880303420064800f04a10203c076100d241a02100c0050715080c400c41000c2000808081041c3c1d003401c40303000661340c01d80c40340500d40005084804c0c0d1359200007404000712140c6042010b490303039202d000310f0048048810158490400341007004401e2102e520444c070244945100300a140d0b005100411030a00c2420f160844168400720719000d0b04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 747826870 1250 747825620 747825623
    0x1c05031b01020a080f16140c03040605040906170d0c0203031215100906020705090a0f0501030309090f02040f09050907080d11060a380a09020309010c0801031707030c 73
    0x1405169400c2100c0055015101d40240c6699180c615160141181c41020041d908100d10050310031124013080d00036501500e0345120741c3e40f010300d0240c030b4041c09420f5400c075800c41da0000304002001c1007120001e003e180b020703141c8010309041d11541c0305d1392240e88200313482690042c0301b003c2c4000d80541d90107000b940c3c100c1101e41c6003880c5504e07008990350f42030751000b840f080c861100c505450344040c0c0305003c02400e841e21900101080350030303c01000003d40005090a003a0754661020b200c0310400e50143c207009500c607860b040c20309424249041c0503141c18101c035410442c810b01081120200e10101142103e808600000b0f5640742c42c00a5030034544950407608003407098a6000080035448466201209822801c0c0d038120f4841c4800c00056980d281424066401e0258010503080340c180e04140220504004c5403802c0f4914401107445841f40e64043c1407030741d5000c0200880c9190030301032420b9952240c544a4103e604543e582c00e01d0000540091022400c0400c07450304040c001ca1425811a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 747828120 1250 747826870 747826897
    0x60303070f0317360c190b07080301360908090d030f020c1f050313150c1b020a06080c0702220c0207061e140a18060e1c0503 55
    0x740741c40852035011502040c010070000d2009140b00802c050301d8203060300c0b42000413018060184c000c00400c403102015500000b5442c40c403a000145203e502c000403c2000c0c0301e50700c3d040c3c0300d624210090b11902c4500c103040200c80e0710314041281c5404d200ba0300b41c508006904c0001800c01460801002c00d008505480741c04c01c016103292030174150012034403e000d9500b9401c95494548000c20300520100c2c1107114450028121008130f030041c0a034000d58ad100107180031040b0b80c1c541a03100c00c00c0081d00003690641e8641d40b0307030080c002640c2c8080004d80c2a41e401000d06400072099011802c0d8241504c14401000030034400300301d00c00400030032145080c0d002001c0c012405502041c4a00c08030b80901c0381c45d03547d4900401040710900118680b0100c80710361b1100d14101ca21003a45d0040380c0d80b00103240c000c00002268486039903100d070010302002e00465a0780c007a80c40c1454040005004142c0000381070040e880c0102420741d1714030441100c00e030074550f81c40803032a289190091650041c0380408808 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 747829370 1250 747828120 747828167
    0x20f1f090602160b010f05030c0405180607180e0705030f0a060b0f131502100b190e1f0b042601020f031909020607020d0201090807080a03030b09060303070f03 70
    0x50640d2011107107102030013003e094415903601e0000c44074070080c501c00d1a4241d000800b02140c070b854164480b0341e04c06c03224030382d03c1c040341c1d420342146040180484041c0089020034200040c444400c10841014012540101100d410a14030241440c04020505254680c401d800102c1d6a1061b0304100010a64800d142e91035202d20705140146030403801d0800c280088600b400a00c1c0c0c0300c410072039080d600b865005000481c00d0110418040c04078451660f81040d6008044101d02d25400e070840300034499005030b021941806408407018a41d84060303440003c071701182c280042e00092084030216000807080c0c0003007440036080c040000210f84d8046800e944085615001404904015403080503c02016800c225402c003290040703410075240130b50400010704c100030050a020329000304043c01410400303461907480030002d180040c035400c15485900144080b2041580500441500c8401218210224500b0401280d647d00559001a191a0744242c0c0002414041c0e0401c403e500d54500050f1b01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 747830620 1250 747829370 747829387
    0x70213200c07081b240906030f04110904171b010213082b0e0d0c14040c020c0904030c15020705030421030c080a030608030c010c0f020f1f090602 64
    0x2c0714462445a800c9501903d05058100802209000c14414000741030040b0045d8440c60384000f1690100340840040b003c1114140300e43e1040081c0d0302c501c40406401c5441d18080c0f40188050141242413405075803c1024000001c1640088001120071042c01136200d03020b15925000c80024800c3c0d0803815440090603060001a1400c1030782500c1c440c504a8400301c02002d603c11007003456442030b01400c841d414081c0492441002c003280003410090100100c40d1560b00c44103000441a4003400c4c4144405480b04694180390090f800d12a0480c0054907070484142c002c6514444000c000504201c168250101003007036182440b2540349400d041192600102d10301181e0307984c460301402d4030554030b403519140e100c0e0014040704036032039041d51000041c040a5030342c03442a8002441f2502415152840440c4524080020709400346411001003111848081d0241113211800070103421034000b9043c0911940300018000200842041010032551503008076030000d2001d0f080090405000160064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 747831870 1250 747830620 747830623
    0x72f0414010501200706030b042d0f060302091605040e0403020a05160503030a031104080109030e1f020d0f17070c210c02040f061d011a070213200c 65
    0x14180c03034003a03c80c4050703103050216001303440c02040481901684607000602c0f140b48690071407c0030140140012848803072821007003a60340110070550b080c050110711403444041140c01402140c601c54542044240e007160041074410000404100d0a0102ca40c0ca0324207061080044030000c003503c0c0e11007001800d151034000d4844003011300544162040b000401480c06c0d2105003402150303402030045207410344624041e8045d200040c85800004000e12000903003003000c0c042d000e4554426540d40a4031441c3d081081710b015000480c40c02c87c0380e81922003e5902c0d400098040b06c1d03900a04254190888449003101d044100c410400304c0c805034031090041c1d441c0c2040b541c1e10264071032504005024450080354030070b4086110404005030b131004405000d03003000d500540d03521007404d801140103038a60035240d0b01c0200309400082c400c01101c004201250080c10901110708140c0e840b9444c0c1950740c0c000039202d100462010780030303a07600c54500140548604801c041c180c184904282c42d18100250f09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 747833120 1250 747831870 747831911
    0x6161202070329130c03050102042903041a042f01081608070f1103190908060112061a13060609080303040203030a081914061005072f04 60
    0x40f5210001c180260716481c4996000403000ea5441005002940d40c0014400c482ca113641d070150b075400c0e050503000c008240b003800100003030003030402c0b009032109a580300c0b03010741021072a24a071014418400c0c4000110901e40031a0040c1b010040c1e010680c5a1b070802890210544060b82c0b4503404070b00103400c41000030f04040b6000c1000340c0f114101581d6450082c04801c1d944100140002c000c20300207411240203242c10502d10000e40740c40c0385002560718003a45554001e09880c16184072500310f4004032588004128050245003000e070005500d40801404001c0c040203004118548a0150b9610380e10f9509e200365070f010340107144410b28030b0800070840090030740f0b01490303000030003044011841480004c1184d000f254040e0041d440c200014504440903c03001d8900a400c041103d8458252207560050050001c0d50116902c0c160505c03c007003090003002807071110203001e011b0040d40702040344c0000f40303d12007011544d11103c44e4154040308940210903903130260f1103441e06004002081c081c101d103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 747834370 1250 747833120 747833123
    0x40203100606080106080609090d080901020909041a010b0c073f0212150f060d0c15020d0c030e0d030203040f0f140117040618080f03071404080c061612020703 70
    0x8200303158480d44140070810104850109c119400207102150580c410307204035600004440c001030401c0342e1200024941c2d1030540c0c05803078070383c0b10002d00c00951010401040c0104200908580703030602c14899079807181014071031050410111104212000090742c0c9549121020505000d0529000c540c50a0052442c200c1607003c0c3d403540240401090001910190030038a04c1c40d4041560f58540208011071801171009401040c07016208002542030200c80c000381c4543d0580402001d02520001d260101c0480803c040001c07008900003c40e40081001041303c07010303103044080e910381e41000d03880c40c41154064250000707150304c0000c02d0f00391070031070f8400c1d500c60342480300721402503500450f9481440c000c02075504002001090025049074806510494609003010021800b9103a41000e03401142c4842d03842c0c04000304101c1000d0b44400041f91500c481014507080c02d0030f1410040d40c5004c0901164002c100008001034031860060252801650011404e8182c40042100940700c2055100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 747835620 1250 747834370 747834377
    0x70c0302010b010206131401020706020f180405040f0f0516090903020709050606040509190c050301030b0f010e0a0e010b0a09020a092c0402010e190f08061e040203100606080106 78
    0x707040b05561002c509a0b00031400780e800b81040d2417880e11040c100003500420122590b50800c80305d0006442030000c1d0142010b5111602c1d2101c0c1e6607500e8820404110203a24840c0d89400f0803c4009080107240301613607908801c100c01500e42515040780b411549051100013103090301c0c0d0000d00f52040d41c20064041d84aa802c1d110000c4d5581f4410050f610182c1c0c2c110341c03240d4140030078080c41c02c141011503880940118100c0d241500402e9a6048529040c0038200042c80000180181f00000c0003040c5c10800300c00c002c0b08075600d005081c128081014250a60107911035502c004601002d41104c421400700030024a13003507a888200701d00030741c070000c41440415251000010502500040e511b0400021060382844580543c8035000119000308201d050100d5000d022507252941110080b12007240f004510700c141c1490002e0b40700701b85e29032040c0c506901500411056038811181d580b50a5001c001d0491251118400641411009688654000c0c6089400140e25600c0b00e107850403590b140c2c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 747836870 1250 747835620 747835631
    0xf23060109060201180201030e340608041a10080f10140411040209060d0e10050112050c2e0201020d18030203031303031514040e070303170a14070c030201 68
    0x80b003a070980f0140030107019040017504208016500a400c09051001c1031030035a01d40c801650f000c00584410045008160102c1c030010150a07800580d140000d0f00b81c6080413611458283e94601d40054007138030000d003040811001c80c4060032503400340000b801100c819903c44081d4a1400f41c2c4d502810440400418100000c40d8521810101c0c007600442d0400b000d06281d034032040c00d01c0069804584c0f8180c0100080085080511540c891080c50f0064a4080d00605031380305140c00c1a00c2043e08051014000750301034000168001030000e0030300c101580c0090302c8946200d2090b4082455001c0d00b80780320704402140d00c8041e4190300034001d00c10319030006c10040d050170081d1015032208410080141e4002c0001c6984800c11002c000c0308244030346404648020300c480c004016854a0b400904400120040b0364018a4140101403070304030080c009064003490b54800030a83e1070b9061800d09004010380100f01c3c41d1149800c84070454a005d44030802905024200030590006840d007980103500e840d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 747838120 1250 747836870 747836879
    0xe032a071202040c0807140c0724030c050a0903060b030c0907020d02060c03010501080a0506040b0a15090b090d030809010e0a0f12030516050a021e0307140601030302060a0f23060109 80
    0x81000e17a0203048250b55446038041e0f101d03014500caa000c3c034100200ca12829500080704812121000d183d408003030414003480c200340b0b4016056584081c82c0e00706200c4240018030b404c0d580032614608682e041140440c815498401107410420509800c54021050108000d0307400d40000c1c0d070600c41c2a06070300300c590030340e00c1c0c40c00400540002c0c017a2a0008007120040f4080d142190071494200341c004100040310208040021242c0079180e000c1654910011281c3c0c0c003d0390041103c00090150521103490301c030b1041c000030a1032204520007014081002d011800701ca100354800781d5000c0340103007103449090345810102c1844803030300000c941c010b41c03488003a04643d110f80a500d0090034204100100862051002e6030103420020b462801c44c4210030001361906441803000300c0c51030b0100083c550310805420005081c0782000c1600700b90381d00034001000000d40c0001c80b140c0c08880700341d0008064100d070b150280a8483e55004400d4801607c0801010806030420980140d00076291146040e039074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 747839370 1250 747838120 747838127
    0x210213150503360d0f020102091f180308030a0b03011e0c02030906040e0a060807080a030804170c010c0f020c0d0803040503071b06030c030e032a071202040c 69
    0x85014240c009941440400c1024100412440180c0e01c040c5055a542d500c032800400498074414500b1502c4e44503070082000c45030032040402c124a268030095142242200225428441e070010000151440d02988600c1610034424814220142c442e0030480701e64034105401607400070380744085450720b010542c071640d01d01407203220350700c242e00c102c440d100c144d40c04595001041c00100c6e0106501081110080d25915403005102802d60010200114100034015004494007030300010301e254000b07001440035000c0020584501e036890b10708069150760740d00c0c1000302c11440e01b02c08952501c0110b9480000c00040d0011040c4009990f10028500b401d07003c101d98402c0d04000172500880d8030f00c0c001010400c40d80080d075025004004036850000b0642c0c8604140b00c01440034051201c0e03e190030301800798140148a529030030b42c80c085c4484542241050785034880c41c18440858041c0c0741280d0b420030410340c00e8141e034036411015149160754a5810391855848181d040340700703601d01305016020600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 747840620 1250 747839370 747839399
    0xb01020d0801182c0a17282003270f0105180303070b01180207080409090f020a14090901110a0f0c050d0c1505010b0910210213 56
    0x407089001d412841194005034010500030070740404042c80d420074111003003254000304443d880d90f5030050005d0304441c20200c1c1c1d007109821040c40803c030300304064109800074200701454078400004d005400c19460000703031071880103110740c004404003501080d600c011010000e002c441e07850144182105403020252036101004013840c3d940211841c3c00d841e02c030b501c10405024490030900f560081084132800203455a00118001c5640e0204480180085c118800e441200e08019500c01d600305021555600c9d540d0080c3c0c092aa0303070542c1e41141d101400b0410410600035900600003503980e0343c440f483d0000c1c483c10303206043e00441d8484049100308005104402c4415103480b011420102480c004490f4a00910011804c001481c040c07840403400030b01203110154407544981503105494600480e8040321040e0303078070b000c918000c010055008400201d58880c0001c981c4031300c10180406050700c880d200780a6040d2403001014040201100b035038002d20140000f007a0000c0030682d00c00902c2107059 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 747841726 1106 747840620 747840629
    0x5040302070b0f040306052511070803040f03020402031e0a050609130f03080c0c1902030f0d0525080a020c040b010201150b0f09090a0b01020d0801 65
    0x54040005000030482c03165140e00300560500c5102043c059031001805082d1180c2c000b40141d145100c0148140300e038541004001b0901c00002418481490107000482c0b00e20701c0082141d000020559085a922a0700e14441600716800d01c000781d080541040b0090080042e0080d908201500492098241080004880c946103082000b1000043d110300707211124400110302060b000c0c01c18003002d68041c245220152540c00c001c072450322900100c0325680c01098140d00d101d103080a00c40f441c05000f281214104001c0004081d142c8600c00c0040011400c100f040c000141c8400132000081d165040704203130174000580b0b80e03d205030322403040c98005822501c00b080403450700e4421104000700a10003002888094203c0000c3e424441c007039081c01325030114a62a84520850854041078005022007002e810800c0070000601001185c0d00d0150069038523039410f440c401c0900328102c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 747661870 747841726 := by
  have h0 := BRFrame.cov_init 747661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 747661870 ≤ n) (h2 : n < 747841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
