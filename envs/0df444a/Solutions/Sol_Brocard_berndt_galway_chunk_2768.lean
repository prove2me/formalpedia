-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2768
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:41:05.093036+00:00
-- url     : https://prove2.me/submissions/2856d9e2-84b0-42a1-b69b-55e2cf04d100

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 497661870 ≤ n < 497841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 497663120 1250 497661870 497661949
    0x1061403010e06011e031401090504020f0d1e0506040c170d030506010201090c1404050604020405060d020306060d0e0312011d040311070e0c04170f03072907050423 72
    0x199041c01c0c0d5104501100c0c1c040e00a070701991f0724110710360016071307995460700101c0d803069800942c09152000010b4580c680f034029007070054080d1008100030a2056030301d0700c3c0c1094855007140d0b203800c00d80c104410320265040d6280101034a242118005001da62a181c459030340407505014581d42e031000c80d034141d10035440424115071081c0780502503902d480c584090881c6006441e840b56040000150071400d0500079130302104e4000d0302081c20100301071040030194000801d00354103c0303020311200383d8a0ba15805403800e4194000301940c4d80e07080782103c1300481c0f02c05802841c042c95201402c0204e203000f941000350300070340514014400b6040181410f040090503402560540c00002c10701410480000003803080796903240e41c0904440610528a40303607010401391030000d030414007002d00810398101c0b4510804141804100a01550411410034800190781100000b600400d080c409280b0003111506001800740c0d600c0d1407140e940000808103014841469045030618100c02c0c551710481241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 497664370 1250 497663120 497663147
    0x6020f03030c04151b080c0606040902030c060901050d0501030b0103030f021b0d0807050d09080c04090519050f060f0f01120c031407050904120e1912020a0e040c03050601061403010e0601 82
    0x30622200c0c0b946c1410803d40d00120403004440c011800800d42a2405216840010f6806006800001098020083c440d003100300f1007070611034104112100c00245200380c2e030103984034903101c4089504604000303141500710042c080666220000013076102d02c5419191000c0b40c01110012440c800b545003030b0342e15002d070550040a80c80344860502036150800711010aa490120403640d4903e480010003068070071943d000351094002e5a5804001c251044045191f1400742084400001c00044070b84d1170244100e441c003403c0030515080c00001c107204078019004289030550f1880c685c180f5203a0003c0344150f840000c20206003c05108071071141800030100030074000700850380c0740c607160400d04140c1c0350620700d12000421958103200a890030322510742080c086030340b002511905041000d032a103189610145c0c0d108045950010390042031807489880b440c0b150100c000b540f45980307407a034601709060304140248600600500e0b28041858203a074116403801c45050210340303071000140d803001c0314283c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 497665620 1250 497664370 497664407
    0x4051302120f06090106060503060907140304030305011d04030206070c0309090e15010f12060e070e040320070503030a080a060302090711060105061804022a0706020f03030c0415 78
    0x180c1d4054140124106403003a03065016620342e82d5421002600701c4105010341004210244041002c07810100c80c00c950001c1d503801c00000e52108001900640e8100712800c40c0000e49840050094140401140d0f031900000540c4110505080c1d4002c2d4446400600340420000a01e00c001300f07040c4629140001421900c5040000e1a008805c8548030410100d8a811000f8903000010b4444020405003040b6214451101001d0301190340d22006402c0801110400307204946020034011903503106240a02c1c402c1d04c9481102d64031150500d2900725220030340c1c889402080c410801614044102d5010351042d2820711125079603404640300034000b5070400b030b40001c030441c100501950440401c0d0b6581240f24102e80590b0b80e10420086070380700c2c042d00041540038888423404103040075005443c6c801c24051404411000c00c0488030100007034102c9c20b03031156000d40804c00034036406110014102c0400405140766252100d00d00384940305c2c5200749505040380240400c50107126099810b514401e418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 497666870 1250 497665620 497665639
    0x1d10020f03012c0a0608191e0302070906060c02040b0904030914060d05070203031008070f0501030f0f050c130905040f020906030f0f0607030507050c0d080c0412140610030803010504051302 83
    0x1144140141401d024522442c840c0c22401e50050381f07140700c01d076003140d8800c003040914030184204003050780002c2d500701c05610803071002055400d010300998000d050f65580e0140c002c0c1880c0100410303101059003080c0604018030034040480e078420032000641e41c41148000000b912034003c00d50350300c1070701400304240d40740109021785641d0200003140240b03401c622040d00035454000194440303074240f24103546502102d00400c129400381c0c03c07400c4440500000000c0790b2035490442c1083c1c510441d2001d4a0010014441d00341e6500b111030f4802a001150741040703d031619660316a001001c012003c1d01c15040c0e2400501199020030203100140c60240544608440c03908100b0b80c0c2d100b0035920880400d003041c0020362650310503c113950074503c00c03d00510b00c0b01c548650030f455210015046070014242000041a03c0001d45080c00e0840d1081d0015043c89083c4d070226802d10501074070b141030f44200101d00b0404a400081905e0544d07104540c00901500d5100460042c18080d5200035003150844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 497668120 1250 497666870 497666881
    0x5100506150c0d18061b06063c08120d06030203030403060902040c0c080d2a0c0b0a1e1a0d0b06010e01050c071e091d10020f03012c 58
    0x4500400d440c0f085446030a41d400c0f11800c640880e42981c01840b00140c2d07110a03802e199040c3e035a0040266004401c001107039a2101714140d660110152480d6000b49507c01000e62078103061003003500a8503e10f510041c943c01c0c529110f448622081138105112408641894103041c0303580640300031030780142103d6640d59a8541400078012081051b44118601041c1c6840940600d059418081c2c1c083c800b10f2600d4140c5990304d00078030004502c44440c001300344402441c241001c4c012450100c60740c55018280782c043c03600300f284403c018182d0700100d0901030855010901d0414154406c000700901298504001c6007408d00d0007440c0007559440200da0409806104c1aa01c081c0d001d8070080c3d89400a14400c2d030015901e82c80f500030b8000e0b440d4055030081060259843c09206c0409038a903d445402e66142d4000b01900c1d488070100030748008030401901024030402080b005540b81d045c0035030038010903004443d040d020512480d100c00040702400000400208080f1005c944028004040c50804 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 497669370 1250 497668120 497668123
    0x2062a0601031e0816060603080c0a02040e1b060c03160606030201020f070e0105040c051204030225030b0103060f0207050d021c080606070f05190f03170405100506150c 74
    0xc1c0710948403c61084241e02c02c03080620780010078250040f114900d040c45031001d01070640100b1009695a80e03170b80c1800300001d0ba05500803c2048030140081c00c540b055401004100c070001100c079039480d03010800b142524024020343e03d1440804a4203191101d1091002504520928855080c0d0b40b441820344030070005650b1189040e02d00030307400c60b0460115400c1065507081640180f0840b80d084a0041050b403800740c2151100d1081807402c682810360560903165a000269001c401681040944a9210000c41181c00313000320701100b60f500030703440e40d00c5450f50790006000c00b812a07034031200722140c140c03416011642c82c01e90000c1200c200262402002b5201d078a80344400500c03820b6061051b4285104a94050144a0083c869450310303406540301500300d18440c504032990300507860046010350084540c10303c4140034140c0320301100201c0c83c009000d02c030400d03600c10380f0303c101d00240030204000080074001e0740b40d40c0358009601d031507040010342a010b15405c0429007081c00540d043c8805070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 497670620 1250 497669370 497669383
    0x7091d0f030706050a02130b0c01090519052107020904240903110304050a050409030e130b09160215070e0d0c09050105060405060f070606091103090c03010c020a02062a 74
    0x900c400c1005403100c20905c0c06a1144c12110480708102000c10f001803031aaa0090249240200000459072080c3e0f880f5803c24023183c1c01408800d058001d1001404000e0140000303c3c01c0ea21131b2a0b80b14842024088854010b00c1400703070291030903100003420084403032703005400409516035003946100c200e42088042c00407507104400007045c0c40084c0d01d041c1000810341b42500c40c000d0103e4040c074144400e0200501000c041a001c0143c075000701192a103c00d000d00300c1481c1010310109680c41d00c5018010660800340c2041000d000000401c0b8003280e01240d410b0f0b00341241401e5004580361000b0444002c110714000541c8240313581d02c00400c0210003021041120300001003402543c0c1c0e10f10030003a06000718800c141c1c001d442080068060404a0000c1102c1442420300041d16601c07001c455084031845000600c40600000501c00066400c220304041d02c2070880081c080740d1900f8400940700d00003080f0090150101250500361031f40b181e0424190b0a4243c10b880a5031780c00c0015035651440f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 497671870 1250 497670620 497670623
    0x601030f020d0c26060118020f040f0b041e0b030f10051203090a0e06010206160201020d0f0b131b0c1403030a150f030302031606020702151e040807091d0f0307 70
    0x6a1003c0c850f400a0005c40e03114100c40100300c2da000c43c41c08103244c85000e0751298081d116a0f01c030400000c0b90652200d12084050201c401e5103607100e03814103941c003101c801b00740300d1407200301a003030f004102440009003102e501010b00e00c9074000039102d40a840790480c441d07801c2681d2000d800941c0c1046c66400001502440304201c0e6400d01c4242d03160031743c5003500c406550329401600138200141c1c0541e140c5204031034000c0c0c0c81c4001490300c1c14088502080303e041c2d08290360050385504036010917181c00900d449582903009000c1140003060b1800c51080e15000d401041400320f4820490244140d00d10070381e441c000480103403943ca02e09100244014824201c000d11503c8980c80041480c1c00341081d4081a81e0303045d0002c500d8200f0250b50001d101500700c00844086400f004000300688a101c1455044428040b5090310f9446010305e211414483c0403206003d48000d0100b000680030000704402114202c460009040410140107081000d59894200311403003510681049298000300601010703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 497673120 1250 497671870 497671919
    0x15050616060603110f010824010c241d0a020909030706020f120c0703020607030b0a0b120726040b0a090b04051b0103062306040f0b0d0c0c0201020601030f020d0c 71
    0x1710038100040d50b00007815500c801c1c8002014580030390780b4080300c00c41000024141007414105400d503690041c56400700004003010fa014210100b2484001d0061030309000b10301c4030810300145070b82d00031542c03035030440000b03407052001380007160290100344211b86c009038010313000703554628202403241c2140e8000300c2200d400034a0840002ca0b01790800c409d46181503419805401c868071100c43c110301034501c00c1c81585d4403290340900010307114200700050103044079400409a00785043c02001d03101c460100b5500726601a099a94500c2801101d510303948158030000e4170407035840c4e482880d0000c20003891300829005085d404c0c8000d00c00c0006031000c0902c8940d841d40c5c0c00c6680700004406854481c45001940641d942030354600a451102d80039400e03501a220a0606a40f6140000c12011603032000141a80004243c2003c05040c0920030310500641040940703241280d0001755144414400500b22202500c610720456840c4046000031075000903020380b12945440c5450880c10a042c60b81551 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 497674370 1250 497673120 497673139
    0x110d02071b0803030c040306020c15090a0204060e072f1f1a0a0e180d0e0901050d0c05011808060106080708090601061d0d02090103081c1505061606060311 68
    0x614400004a900c10000c1c170540d40e0400b803541c1c1e20080079400001da1a0410b0003a400400c0c0c0100400568520032002240140034412543c0188421104141c02010351560424200900d0b02d8200381c480500d100015004940b04100000407907003032220506414945c01002860702d20031445508080744034002d90300822000c96a6100b43c0104a10f01c40840c2d00b0007200f000c100100d0481c0e003546075200b2008081081441200f064031420450082c0c850000b26204d491110050b0030000001c5000d803000b6240e0825054644d158090300c1d403d1403180d941040082000b90024503d40440310b0002c203d540c040310b401d56150300d4042e16208044403c90001030100c0005036014000084483c1280e13002c1e218841c030b10448c000041406000b4011560f0044203400c481e00060f1110b6041c0360080d400390dc0c0700342d207038043c41c80840160f885120055820909060380c1c650f4101d41131000c142150740441d03460795120440c544a90b4500b030b44003070140449190003800400e02c108d045103540481e0701180c10109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 497675620 1250 497674370 497674379
    0xe0403050a17040215070302150405100e010203060603060f01090b0f03061215010b030a021210091404031b150e1b0103020f030604180c090903180b0d110d02071b 71
    0x300380d800f00c034040d5008001e070395180c4854049800405010b4007034130603100c2c1c11440f03001e047c0070000259001c4540390301102d0142c41c480214410b014845c800c46000754650308041d00003590601002d0802c502c200c5002180c0c0609a000c1c1c800c1c1e50042180c90880c5d5103070003d2040740113040d081141d146000d80f01181c0001e942d2040801c00c1c059003042c1c00c40d482d503142d007498a0403206420081043d000540e08010a44041c000c0c070303000e14460710301d5070905042a402c2c160360406807600301d140100f594403a06d062000294000841c101940d184510070040701910303060a00303040c076940700c2d0300d88002d01d4119286045007000c295182003110903d1448080c5a0141c0110308900c034000000140083c11302c0415281c2c54140c11825000b2002a503030380d41e100c0aa1994925080380303611038889140d03100f00c00c00800d900b040c030350a05c5140d103486005289117007981d8070351644134242304440c1160380c54407e401502e00030000e40708045603665086454660034a442c410b0240c0840c480d04003000030200c0000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 497676870 1250 497675620 497675657
    0x3110d1b2d140c0a0b0307080a020d0e0304031b0807090207080712020a05120a02030a050d090209070207061d0d03030c090f06020c0306011a19030b031605040c030603051b0a0e0403050a 81
    0x4103d81e4117035101031031965032600450754200068045501590200103501c40c0c076410703000d5075030b22450320301c003071503a403441c5280035001c40d60f548810746c9998540c0e141c20032040b000400c070003040700c0c1c11132000b603640d01c100c0ca0720343d5142c40b0740d12000344010008903d1228542c0e0007d00b507003c1c3d80c886c408079502005a4101c0420f540078401c140070050740200000320b03003a44100c000e000e141c56a4500400c050341640c0c006828108119038020060740520750030051550f102100c0d199808440ca50761301c4d00c2240ba00401c41e00c4907485405001c7c0364459101390b424502c0389562a000f400341002610080d070300c54800a4070350071200031051107842641c0012403c082e1a442d503541c0201c540c81101d16040540d0703110000240000300c000145580c2d180ba082c1240c40c103021454201002c1c1d010881000d0038002000f007118070300c11110041501d454414800503c0000d400440040140100e0911541000c0041c2071004070b500034200f000b425100b80420550040007a1129110756150a12001303948201d41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 497678120 1250 497676870 497676889
    0x1203030c14090409050307060f0209090a02070b010504093f02030405281d0105010f02010e10020c010f0207061b020d090b0a030b030a03110d1b2d140c 66
    0x40e007800080080e02c0480c5000d5005501d110b1103030040e00c0c2407420a44610003100d6020b1807069001d0b03000078004201d440d001204a900000520046043c50300e1515080c80302031050040ea80038680c0c03110a4810b01084020943d56242c2e04519000354041048250b01b41c0000f40d5000c07180d0b800322910b42d03148240040281e03001d695000d02800020340c05002601910581e0b0500c8179500b00d80240c007c60608041c15196040011550440c509545424001000484116180004c6914109007842001804901c5421450030b6040c0946c42d6a104000f060062100d18101000740d480060032008000e03035900000c803c1c2d030300710055184a00707003620309903101c0b11200c0001000170740c0f0000030b001450951016008040b084c3c6030000d6001001000720341b40c8407640400342c02188860722a810300780d40400c0070441c1040c0500c3d04150261400800c210302d0030a103130740201000c00c4203008280c801e056010300d84142c904c0540e0040c01c0c8440d030414442d454901c031422017090203240c030700c003c00d400c003660503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 497679370 1250 497678120 497678147
    0x801050c0720010e060301031212050f16090512010b150717250b0a0f02180411070b07270e0a0203090111040902040f050306010b0a051e041203030c 65
    0x80c41c0d04000754282d06081d0024030115505100d08040b0b0102c2540f11607016501a61281201a080e8900407401030403c000040f0303414a994204810842032501030019150080c55401c0520790701141d4a400f80d69090700c0e9000203411a403060600a0041015007003c00c14040039640001001d40301c0350f403080309224013070000d80b40307840f881559405088480010440b01c2068081d82c1403d20b6665890408603d0b184010345841801d80180902502d0380e110f09100f445410b0801c41c0340800c0031502001d1254a65905031066603620300c460309221007103003141c0c54180e00140306406450014005801d480450003400b1030800c1c0104040740018000d0301e41c800344c488040211130340d41d0b81d08491601a6200602183e11552100d0410054011040140000c0e10f00741c2ca0143c0c40f1802c12980901403160381d400071303120754001001002760444420443d09904020310b0300340c3e960450309808207903503403c0d450003445002c0c0c0020002904000c6280314a03130345200359400d0040e072940c260100d0310640c88196 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 497680620 1250 497679370 497679383
    0x60f0503030414060a05120103060e0c03151302150a0309032703020f1804030f02010e01060b04092a030212010909020901090c031e0203010501090806090627010906060801050c07 78
    0x20400f10b510300100a88810342d500e1400314a04000f4001703103104d00070280e0046400a855154060303100c081445164000c84e020340050400c5140ca03200c0055080c0c0207403c42c88286d910504240035134440c412520842606440969a90004041c004001380b0f11a00305400091540c84007440c03480c50b404d1120580c203412107c04007400c2c00c54080202440500d00c045521034078241680d00030b0031400c80742911641c040d071150f02070107092060181c290381c00d0304039101c82640742009c2072080c2d0400006486c20b0751200080054031a004402107c800d0480481c040e0602000c040704500b22a45500200180280b90000155a0340d070740300d2030015604001300080d80041d0200051245071155409140214610301e0086a000140041c1114411341401e6a0010380c1c2c0010042c40341e0350b08858035400031300840b0010101031522041c01d0341c59400191505842d40d82c0100d09813010303a16180b40b41a2010010020003410700b03103207400f00007040c1901c02c004c0075500f01400105030000b09400c0d41c06440e003215 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 497681870 1250 497680620 497680649
    0x6100506030f2419030312151701020912060601030606140a0c020f040f091b0b120405010b1809010b01110d050f0f0304150b06190c150e01060f05030304 67
    0x255124079803446100000c0c0c090f201160101c1d03144d40c3d40c00c3c084622400c510707144003010303046050040c4030f102c40740040d00c0150700b0180620f44407944040190121207258400030030340c20440c0c048901900c542040c89610408419030122500d4002c6010360250900341c8041212654030041921801750000000c90305040502c488170480b03024104880b081840240392401c050242000641141c3d6241820045903039203854880030481d00e2606440260080c0302c1650f261890702e00048494802c0740381030480d041c00d00011608201003500300c01a00c18006081c1205c0501c0b018103520f81800803101011558205440444154061411208003564580c044e185011582c00143e840b50302420720798402610070001c80c000402402d0142d8061441201c0f000000d80c00030080c4015900004101441034800b00000741640c1c02d80b414102d40c007081030400c4c038510041030605440c00034296a40b405a1801c000741e650081e0b90640c000800e50300d0b1a280c0d81c01e90f0f0385a2007455981d00490060070701000101d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 497683120 1250 497681870 497681881
    0x402011b030c050f010605180f010621050a0b03100905030a050c1501140a0b040506030a110c0109050c030f070513051305030a0f080c270d08040806100506030f 70
    0x9805516080d40603051615a550490f51298503041803807410207140e035500c6800b80403078604611981c002142c1400c0422103402c00107201100c1d4030044c0b0840003401030307421b1503860014901e000700c2080c24001400f08228600060b03a140038100d159009131207400f9503084203007900a04d2082451158221004509084030900d058035103500441d04040340f03100d000308140d0307040e2004165a020f00300744e51110724840c841000740110000682c01c410b030040c07002d0105121907200d410503268002c94200000c0b449902010f80406a0300c00e01000d0090395003024220014401d000443e0706941100794119400607040c07481e002c0d00e901881c010715900950741c42c03290042c01100d0708241d411600c2c0010142082c0402c0e0384480c650380c460103007074000c0350f8802c100090007608007140b01da1100d85400141d1402050002c031140381c01c0b000c1d403800356443c0c454010140e80e455001940d107902d980704541e0340d40d071034543c0501503036107400301e500172400e0780c1e814808601414010140c074001c1c0b428130503400340ba032982c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 497684370 1250 497683120 497683157
    0x60c020406091806021809040f0b010e070e0d060905060709051e0906060d0605191a1804050408130e0114010309032307060603061e0b030309210609030a17040201 71
    0x80106c0c4000f14070000c0e02869a07860402c40c0b4016886200d48130f1110016203094120090141d011042d481a039008000410360000f90007004e15004403403610301c481140c58a10010f1011000150103031060170204181640c00c11801170580303108880301c407a818034000c10140c2840b0110502c44e00800514003184080c00d1540103498062103602000c11304a4841c80860480c800120400c0e601c8048000208851a200c04142c101c01d03600d200310624000e90701148094041102400c01e00548e80c5d100000c09009024080d900800400181032905075529150304010480038010508070a400700c5440d8030640c064401d81d003410768580c441481c4010812319100c520b000c2810345d504207130010051440000e060344036400c003444c82a0740001b2400c01003000310601c8000c0c0c12448108501d070084804443d41c0001c191140755608842e91104101440d400b02019080300031b6001c3d4511601c814005e00d58000f002400303a90700150746201c80c000a4000d910f00064050350041d021484000030010303c00711 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 497685620 1250 497684370 497684377
    0x1b080709080304080a1b0503030c03130806071407060f050109090b0a0504110d031101050a020c0609060603070b09030a02041a010f0e0d0305030a0209100f171501031d07060c02040609180602 83
    0x8521b41e010a100c1e584501190031940820720440c80c80e0000103844425100b5241c2c02805449102c0c0182130a180451010302802d000791041c1c40c81040200e0000304000e11038104401031a103044080c002944e4628541001e0300401d803080300c03510402c5000405c0c4090038819188543c0d0840c800028800c0e0000502403490030b010001e808001c040503002c4024942401828020103803240c00580d0f41a0b14030016003090000b41100c010b03904910144191580c0000c1e129003910048000c282d0742d502114000303132900b055610003d4202c0d0510306904045001c000948031507000a803964400d140f00100219041003406000355441134000c1d20300380c0401e1041000c1c642c000b00c0607000628040c808030000b0203408100300703a400003e002c55130a5407041d5014024a82c0c4040c540303038407506c0f41880004005d0742c0b100a69104e041590b1001010b5115452020600c0c0440b03801c410307200d0060f2076403001002702c042c41c0000c0e8000c3e07003029000601d0003003510030a84940c0301a501030704030f540c031603560700003070750 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 497686870 1250 497685620 497685653
    0x5091e0102161214010b0315090f060c070c0506040b120c041205061b12062b140105100602030d0b551205011b080709080304080a 57
    0xc5451448800c50461010b0038019040e0710660f03c0a4403a90700d08500800c04012404546034180740104031903440c00a0500c5286441c449014420750f513a01d51645060203d071b80240c041d01c20f02051040500c4502d0080007503d0240341010003c50b160b20504c4118400ca100d9000129820080c403180a014401d11079040109001450f18140d51400740c0c1042101807802910306070850700c00c5c4907039150101d400640314001c4042c01414081c0d014070380741c45200c004040c5809004540a110410001d00084c00794800034040d101ca402100c5007000f1049007460b0000350019031170400856201002d06064000b03e80c8280d0045140c2640464100041c0c50044401c58202d801c031400310302050780700711603031023055075102c2a41e102e0441d6020554030007010000c41d6401e060740c5181c0341040d25202003404181c0d280001c18101c81f00035450140d00401e440140c40b012040340740c205107001c0303901080e9203000b102c2c81e56440d0201c94881d4078031a00d0348560b2162a2850b845504214001450b1081221402 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 497688120 1250 497686870 497686873
    0xb040606090c170703051308070c0510090f0f03020a090f0f0204090c140301030b010b03071407060605090901141f360b0a0e04060b180901060605091e0102 68
    0x6589080001c1601d100c1403003076000c500594041082001500300d601d61010003450140900d09100501580c19440d140d0047c118500c0081c0c01c0d800d0164540d4082c004100240400500304103920008044030620701651002201c101000101c02100542c2881500e400800041d001440c0400a41c0109071222901b0480c58849071404113074450341c40500010f01a408000c0f4141d400550010024203c203404411030040034001400805d580040c0d6a055507450010342e6505d4540b104241e6000005c01220202c1220001d960760030040b00e900580b080346e806440d4454203454075421075090b00d040b288500d1110031928001002084c102520060405070302080d4888942c4403080f8030901980782290303407074820651280055400312188150002c0c6c00003001080740090010004e801200544035106019120380089014002190702551128000500480812071107207100034410324102c0b1091455441c1103000034809020790210b85030100010f220403108060250054564a601140141103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 497689370 1250 497688120 497688131
    0xa0203060606030a1b050406020c0a0b07030e0109090501091a37030203070f0e071404120314030709090509030c070506030405010231090b030307060522030804061b0c0b0406 76
    0x20081005c1c4100c0154260b52041e5560b403c0c400040d20f489041034405000e04450041003200416000c01c4e5041180c2c107181101c1d0040040004035040800c0b81c100701881c52410b800080c1c400586c2d400320707010001861080b0811a02d000400c03420f00f00022000f04099000000710740c2d03450704d10341801e081e101500c0180991648035000301e0f14000080d044034076038840b800c809200500c0c00e200f078160f01207124074200070640450078807810240a03504c03480e4090981601c1880c105409040500100c40c291940c0070b0710b03860032200003040d00a1621401842320314bc1804140e00c07480100407294603d80e140000d02c00c0d00e2515041c800e06170700080060314255400c0c0651041c0141c1181c0319044280001240c0001490703103005220440c46c0d661100329458a05813980c003803910080107840000b50042c0d4002040c2e503802c00340c9061045290009019450010381140401da005080f01e40921b01500701041844031003042c1e0400780701030442d40e13400326242c4006080040c50004040b86d1040c4120404a0f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 497690620 1250 497689370 497689391
    0x1d0906040f1b0302121006050f250605040309051e0f030c0301020408071401051323040e0114100303020303011503060e0403082e1a0403021315080a0203060606030a 72
    0x201c034100d5003542c50010740c0001d600e40c1e00e051285021500006801c111000340d91030710300c0150003031040000081080c4000f1409005007140341002180f142c418803940e00d103401103131802100420084400301c1c04a41c0700e502c0401c0c14186103c0303407a00a641000c0e4503020280306000c0003a15800403840d80d40c10b20a40440030102c0e2400c6c00500300615003000107198003414613491110444e2100f000d1410420300b0312407044400800104101201d1807604200c1c180780440b65003040c1495565215030f041030401100070416030301503000204a40d0f5188450400c1c0c1c4468000b91258580303480080d005034410301c0140520000030845a5042041e81000100c070740d600c0f01c131070301d103041d084506601180c050030803c510848480141c4041c1000c008011285200101c50800b48071707240e000c0c03016002030360604564004083c208440c0519001401c0c401481d1300808110081d01400303020000c004d0900d0800500c407000026501003066008018150940d40c140601085402c0140b54a1803161508100358 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 497691870 1250 497690620 497690651
    0x15090b030a0c240503220203030903010603121107080d0302030c041a0a0e0d021f050f0d090204061d040206090609120a05070f06080604051e010807061d0906040f 71
    0x80200110b52040c44803d0503072100040d5151101000024030208004101e6510b11000010902c0c50350b07044200c0600d0b4071400428036501400c0c00c095059842c028020040c440684021020751b041c40d5034165807043c080c130926807245030911925105a028003034120029000350055984401c54400a03814641d90b07034154401a00da954100e00e0624000407107120300c0358480c6590315903006c103407046044041c441e40820740b003600030400c2a1070a14040034002c0325600c550211044c1d40408000d0079140c00d404001c0c80010302c60008101c1c070461071b000300024175a840031440483d2050304441c4204a039501c0d02441032580c0113030541c96100404018100807a0b844104c102e4582e46500c008116200880c80c0051400c0011340110035102e1252104011503988403807600c3c1e0200c0b041d5404122600c50b0000640002c007200c80000d0000c07141400401c01c82030018845046605980d1101111524200d01c080c00c50b2070703175091b9038106d401a00007503014100790300400d92038140309a000032030070507500045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 497693120 1250 497691870 497691893
    0x31a0a18060b2409041a030a3f0e0307180c09080708100e0a06060611010f050705090d14031626070311160605071515090b030a 56
    0x12034019580340106a890b0810301145203144400f000e40c0c20040e10b0310181c4002a0041d9002d03248215106c61780c1d45240015050b0580724074070f0280464000708802d00d84200c2001c0141500088404140c04604a803035440d030078000d100a02c041000301a8059180484040c03aa91211640510803a0000130381c003030460600d000c02d80708107003001482c02c4800c2c80080c15500c2c25403086405a212007818000301d80080395055900140940c0001ca02e40003004050501034008406807a02d071038140d0014489400002e14491b81203020000c0040200305001c04040f12420360300100052001d02c01c00d946030811440102d52a405680588410004c0e00012851903121014500d102085c4249580c00c002c0010684000e502c03180100c21090203c8505160450040760006810844103805011200e1000e20040740c1d41248040c0c2206003a4032101c01815540c0160012501000c2c0d2007140001110144145001d400d0f00455040b40180743c00c0e200d00107003d0350741e88540c0c54000c8000c01c1d800107680c07113681c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 497694370 1250 497693120 497693123
    0xf02030a0308061f050d0b0f0406080d022404020f030f12190e03100510082506030902330c100e07030f021306120614060307031a0a18 59
    0x40b04080c0c50600705100c12424805910040070b101c0344400b02c2190b4011007034a502d10080c17003000624021900008030625030101c180340d009481c21002084e0b0800c0841d20382e500030a20b80031554400f04486030710790041c4071101d22604085070200454014506036000d140084d1004044424917040c20981c0e5003840c040742004070b01e040000400490003c68441904400d035198107140c4101404000441c1d240c10301c5402d11004680c2d908001b03484010b6408072240904811011200305d0b00314800001203603900340307a83d920f1440c074101c00014034910074060b00d00e05a6006e0300102d1003041903100920300e41c0b2094002c8600501300840e4440d14040c1c4400791128034070f010700410f00380b4400d05043c003c990f14410103400c140c00c8403500344045100d060100c0020b66064500d0a48002c11910420082079160007500840c500e00480d070091206a400c01d05042e60600b802d06001c0c1c450104241da540801d00c000be00500d400710b1091510041194141e0340040190f4010814000c1450001d41308540d6400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 497695620 1250 497694370 497694377
    0x903050f161202030c070905061f0815060703020316060e0d0507170c0706140f030c030604060b0405010c02090a0b090405070612091104020a0903171206030316020d0f02030a03 77
    0x34034400748070b500721080180c0480c60026624060007000b080d6181c100c9401003448881e02c50b0082007042d104e0503c01c860282c2d4845030441c0c2505103840044c2402410780703074400c010081c481c1020092400c0411154100d604dc0c00651502e4200218184a14003145040d1081070340d4511900740300030140300c0700d45040c0d100e5850f207035982c01c20324100c1844403201e070b510360744031405000c031314170b1802c001030707400300756401c5041c10300c080c44540b103801c0c00034841c0d41e40c440c110003004410f0099518415001d140101000c0b40c082c0031164484181c0381d607a00aa1180d64001040076010b070000d41000980c0b140c002d6081d03e804110b440900020a92843d81a00e040f2195400174104010071617200030340000c010090041844041e4040d21840705510006120354410755000880c444000d005804c803400940d485024040d820384125418035480c0c000b10901000945e1310b1000078168074001c0304860405140d9840448a110309400384050007684030000c0341c070144211354480140c0da0800900005510039034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 497696870 1250 497695620 497695657
    0x905060a020a05060a0504020f1338100f030e070b0f0903070e0105030606120c0301110a0e06040f03060b13020c030a1e0c060c030b15130509040b04060903050f 70
    0xf0308603190000c02001656158680001d010041e518012183e40700c0350102c0d400d056120b4000311070300052030300d592125022141d20911402201c411000c6400c085081035060b100700103000305102400c0c00303103030014001800302d15000c10f205011b5445070358208a28012519481c1c1c1b2601c5c118117540c8200402a000d520200f24002c042c9010010741000c0e0501c0301407114254580303004255100e4014044510403103003201400c40703a0904200c200c151000003002800f841c00c0d806001c0310254415409000003440b1440386050700d080500c05c4130200d9400051107100f061454840100500c0007121542c1c1c05140d5928142e000d1003d40080d080000385800070b55540c0407080320140002942c1031f03103013003901000480458030580250006d82055080200480c055100580460081c01c050000b254002c10020582d142d0740f0541002e814100d102c2d101803042c01b9207900800041c400c0c104d600400310242000010001203650b00b12120242c82820400d00708400c2e072002d412140c1046075815101c88080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 497698120 1250 497696870 497696873
    0xf14040c090b1815300a1d06070c03030e071202060705010b060a1d0a050303120a110a03140a09120f03020904020f03042f010e0d02040501030b0109060f061e0905060a020a 75
    0x2c1c4034445d1181512140450111841d050641c8055401010256025582d0750007030702010001c00110401000d080c1643c00614015a02070102d200c249030980021f460710003d001c0141e00042d61b00c2c1035640384150030a054100d42e00300300243d441800c0846103175495054080d00c6454160180c8041101a116100d052048407641025005ea81c10224443c80480d001000241c4000c4100e0710344280004c650805541d4424801002e0703c1c0ca42d40b410410030300000c07481c0503640d050740614181003050180724040d4070b40c8041d0304181c4503240009071907140062141c912181c014001002d1a0540c1e050140c00c005007003000a00b240c0059100c290748050000030801041203100401030302140d510885a502c600c5400c0c032800401145250905010010703004510680da005c42c1444d6031a03005000b0302003507840c3d24183d807004000b8031407690004e081ca0b01c04100e00340b100a002060768519a601c00c04c524004d511801e41280301d000c0030060140c40300740856592070781001050580032300d0300200400b010a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 497699370 1250 497698120 497698147
    0xe0307060e07030b060d1103070603020a09140108070c0c0f031202100c08060402092b0308010b0406022e240e0f27010203010f14040c090b1815 63
    0x40140310300c00741c0c010b2802032000400503060684c01100035141390740b201d001450171444003002111034070390510135141b001980a500d50018550800c0076a240c1c0041551116030035112006a00c8c1103000c948900000f0384114800c1032a503007103e004070f18100e00c2c203949160241d100c29203900103580c0521000c1d80040781130b404011040c20076900c44c004200307d0060620040034103401402d00791156030005000006582d4420b0320304111311300c80d441400100303d0003410300d43c1d060312140b0407004100c01d6000014503000c00420350741101da40785c0240141c00c6004540024a2659070309c0e5101c554458040c03440c641d8154800d03e02d80c4418100d50200d50b01d042c481200840350f45500550119444a0400010070780200b4119005064400003050900034000e072032110041c151901c1e60300e98404800001c003190300080803402c5400243c915150301550100340010ba803555100c120200700b4111081010005120040a29014180c0c01030002c101680001d48554852080c1081108002c00c0030b030f040111 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 497700620 1250 497699370 497699381
    0x1c0b010e0702030c0c1c0c1e0b0307050f03040c03330b0102071e03140601091109030604020d0203070b07150e0102070302070b0a05120a0e0d0305061c080705010e030706 74
    0x2100d0004508000441103d26a41e4030010300c00346c082ca16204007400385c40250444440b00d542e00c0203401c2c079019140d0700385000c0d2000940031123000d0091100000b03103010321801142e0103800103a4500b40b4100e0845800e038100e030720207001218400c01103c00000844c0d180403100107a00324948409040b1801914003d520080340c1c950704d0b29892400d62449520307a000600342c0d0844414401c40022001c010a441d40308a903683e0010380074410244044038074950214541e03060707a140040c02c010f80680d0095a0328280134032080306406a00841c045005485c2051600210a1009040b6008241c0340c1990504030380018200700c075804424001034412400a0084664850220000314288840b03501e009540340258880e904900c400020b60f4401c5511500403a140c00140c070789846054180380c0303000002030565440c1e045c0d1034040d212101e00c041d4464000e66004243c000c003d174484031281d880701c45071400301c50001c4801480030008640040c0c000c0c040d12002d02c0c4100d019544a042c0c2e400c0000c00d584 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 497701870 1250 497700620 497700631
    0x1c030507032c090c041703040e0705040b09041805100207061407021e010609020f0319060b030c0a032306090a050106021203090a0203010504111302090d0303020304021c0b010e 77
    0x40d070b224061203109108003445040c6100c221840d040d591103e82142c84244100d4103d802d8000c080d00711040007040000c028400c40e03440c030400e210a6030b15910106c3d10760155004050706400c082040850503d0590814295181c3c9950b4085541e0101d5403030a2402d4240d440014801d07402140c0700d81803000c03a02c034540c0e640079008100d9113580707403c0300002c0d04c84985070300c207401e0401c121505505840013503100402403c401142195980121060769042e5001218076125030700603070700c581035142524000d240488101500e8281940c5414240704041c0e00172041c0142010342d25100741e4058420401e8040c49040a00d1440c072082c203110b0140051500c1c0203014907212400e1900400c0001c0c0e000a221400324074400340b840e200c0e114801340710b050141407003019506609001c2884140000601492000042141c540c0506c40464503540d0990007048050f81e80302d90034000040c080790298009640c0544010207031098000003852080b0303041c400070001d8540280b400b0051040d0107840c140242c014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 497703120 1250 497701870 497701907
    0xb0105120601032a031506110705060c1006090207030201200a0c030903210305130b0f15101106070507121107081015060f08040b061c03050703 63
    0x2620160010321a0040506114105640c5071071416540c03294040d0075400e0240b582580c1129689241c0c02001380961104402900455500c00140140200c07403034401d900045019011061804080000300d0300300f0a03007014140100d1a400072199441d2251401802e14203400503140e0301d01c0d04000382150548954901e0802c500015070001200040a50380b86c0352461422400060700340c80c007268a860194402490b00c01c41c26100d03201c01c000d81d0703c1d0b0100ba56040d5800c11069440304100b8030011400c41c03000e4244103403000810010108111301030703408076011007802c51048506001c2808190110f4651000a038074450700c882a140030310060ba040502440c2c000c0c204406c649a070920f410502901c0020300c06101414102d117442800302000034104441558281d524690700030001c1c062050304c000c0c40700840e02c1d001c83c07451300941800180000e1039489034642e96039a41c0300c400f80a4050441503102c0703c881043e00c0308907050510320b50064801d0b40d856403918800e1078090080c5001a9420000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 497704370 1250 497703120 497703127
    0x60306110901120f110307030c08100b04030332030403080c040302130b0d060c1d0d051e0a080a0e040e0a02060a0518040923011505040207061b120b0105 67
    0x40d0b80c0d001d015040482843c003800030b601d01d0281d903840c004020100c46800f210001104015040360958059400400c15403501c190964806036014001c02c854020f2400920313007444240040381c40384160003000c0c404188400c4003002110356984401d0071000014942507000400c0104245e030200f80c0302d81040d00c5411441c101425540010200314401c03242088140d5a008482c00b42e581d54501503000c581c012604000d80c072031030580100400c66100101124a0030060901003c2c1809030a03c544290041d0180c000d01c1c252000784003032094240240559840380782d100341c01203410a4010800c50710b207902d84404410039101030000f60351041e4142051500054100409030300d40c0c400b140c4107010f103860b0150390341791940c034921490310003000e2072900a8903000030002041142e8450a1800b0909420800c1003500c2d10006403c0e61444902e002c0c42d49100101084a41081d0f0080c0c10b1207445141d000c00c2c0100400b1128941c2140c8001010001e4040303401c901c03100005118004900c2001c0c646a882c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 497705620 1250 497704370 497704387
    0x9250504051804081b010204080f060c0a030504020105040f090b0f0d0c03110a08010608010207022107060503131a07030f06060522080f030c150610080406020c030403030306030611 79
    0x10301107000b001e01c034500c2c40400140400142c0405c89002c00b40c000420910482084400340c005e4009024060561080d220384e04411080001c2e003d100c0d000c41c40310340e450203102000480181074080d1049052010600c80481c0710019080c801002c0c0c0300c0402d000661500040400080440b50030390f10b0b02907085516800003241051040f2001e80e508060031008451030311010524a20281e1700208243d40b078020040b4001506400a040140c000c8420760801110111380b40000ca42400c0e540c40aa48400300803c10240034102959004010907005070340c1c4100ca4581008200c104103080840464020800100c650584140c81046403101002c200150500c2c1019150b031044c602a040002e82d40c101d41e980081c1c1c1c4003040400b90188109070740740452045d2203160360b0b40181c64003981314022000c60840480d60f224109220b52001414100360062050040c2c807014800b03803040d50b43c1c6070204507100c0040d408000030001103109513000205180345042c114100c6120004c1a01401020400d00e00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 497706870 1250 497705620 497705629
    0x60c0f0319110307060e07090e030304050d030212011a1c09020901080115090902040f020c031305031903120605030f0c0102011406010801051507020a06030615030504080a0507050c0925050405 84
    0x1c2c0c603d503000e85c0019000701c12443c02850b1481039030041d082c044c01c3c181c048081c00030220103140a14030520032a007120141d10001d0b001d80c01003060400311070f20940e00402c084402d0140c007482c4038198808452a1004040d296800c0c089150100d0920a80f90941e01046040829209004000c254000c0000141c8000800c142c0300d214803d1100c2e954070b0318500d000b59a11540442c40c0355100ca0011580c4e410b00080c09038a9401c0703a80e40007801e04101c00c0028890402207040c00c058030807440c10010305806039a0030f031503c29020f601a0f0200b0307958500490b081d141080200580f1001500405070f10400000081c299229620301000c2140090107100c2603136081441241034a204032002c1541c00c030307801880b50040c094008080d6004500120015501ea0140e0001080d0340c24414802c1310844407000a9003556000d490041c00450204806142d0701c0c8200c000d0148144107609440d14031030f2560014170070010036205035030100042c0c0c6850005503011180b110f9205010700f006402c4c54035000018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 497708120 1250 497706870 497706877
    0x5090907170f01184109070e0a09080301150302090d030302031906050d080a0c06060605070210020c030604080f090901030b0a060f140103021b031c050705120411060c0f03191103 78
    0x4400035a809103004051a001c1d403050304034500081607030014030b01801b180303540d54103e01c542c1c0c00090095000c50740601d4240034440403550801d800c10b240da443e00790700319400c0c1081c800c50400c040d424400c0e01da4550704c242a00185a009542c090780341c0c1420b00c403030021125010b1007007074245c1c68040c040050340c5070f5400ca036114940110025844220707540c410fa0713420640450050a141c034015020656a800c9400360006600958400d041215606026a62800c4150841364154482c00c00240040c02076001080108202100c0c14180340d40356020510b040d07801e800440c0c030402c402042084c00405841010018180c543d4004180707031812000d03071005800d0300320301030406400040000b203643c3c0b003000e1000b04096010803603a46280c0502500d507100e8242c44280c6d609400c000c04a101d080c4104240d410055605005001a0322381c2d5895541255028801c00d030061414404a001000c05108039402c2d85c80d40c401440d5284501180890301d41840f50121040c01115640e11a007500d000094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 497709370 1250 497708120 497708171
    0x100507182403110310060801050108070806240d061706040213110403020a030b09010f0c051b1908071b060530090708071505090907170f0118 62
    0x28240d00c0820701c1800c8024040d01c500100702c044000040c0f1008039260200d910403207a032540e03401181d0f62100c00448099a041c0c1b108400911003070013154184c13521002040340b032100c80444841500d0b980344030b4141c0303810243d0380401e4240e0321001002003a540c80400c009141c900000703040c403860305078000740d6840e01c015404208503980c1d61052100e04106e1040b1405103030000c04011b141560303071070b00001039101101c7c12083ca50900d00b02c140300355003901800e007400f1059150141000442d42420711030111803034140d40c8a01c0307800d41804005d03070340300c40e10410703075000e400d180f0b0341c0ea03550b820035820210000036007941d02c3d4681e1204009099000c0203696040006600c1d5403c0150030030384d102c0b140b5a143c0b88400701415079406200c107070300c8001086411100c400e415540da42c1d5440100303d0344026032180c0d07100070402c10840b112461805000b003d903c070021341803000c817584c01d010002032065011182d5816481c1e1080051040110b034214000403070407148000c0c400000800600900080340d40b80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 497710620 1250 497709370 497709419
    0x405010f050f0706050a02031906150c03090e0c03012303070611010e0d050a1107050603180f0109030c0303060503010c09090c05091f0906020a0b0408130810050718 72
    0xb214040100940b04403202039030080414800f604140c1003c20003588141c600340131000001c07140f4100c580d00350040a003210104001c07401e4505900c4803e1b513200c40710b06011002c0040820020400f92500c5891038020a11070610b10340301d6040c20350740c44160403070305070003480d01350f02500c40381003030f500042c0351410340d5807600d0314440658202e1220383c0580301500c04440c0500400c0c0500094a9010015140c485903036540e03a010150340890007a00d450301806059007040007040001d6000040d81c40040e84010744030300701d0700b454200000351070071540c4800c1c0450004d000d00b003121042c198580120809008110000c200710000c2c4040075110300c01c1c03482000740580c0c1301c10306e070040c0d140280292b4220030000350480c014402200c144800c20482650300b140880d50301d01c0085491440090b2205480d64425aa6491605c0b907454040c660303005402000e0142d1011031022449040c140440c00c10795087e840c0100f0107080650019100d00040d0410032141d01034002d080103a07822071080b14508166252 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 497711870 1250 497710620 497710627
    0xe0d0b010506091c03020c19030c1a12010e060315070c030c11030d0e030111070b070513170d020d0e0a1202150f1b0606010519090e010b0a0801050301020405010f05 72
    0x80401e043c07a80f000c10400c008500c20048801741a00842c0c0d17a114408105c07850f0207030803948100303a005642c0e2800040c110b03501004060095005081c80307282603a00c62260780d42485064856544101c000341c004c9800143e0038404d004641c2001c00c880c0d1041460303c1501d103028900050003d011200706c0d100581088903000038901030003100c41c2c03601c8d03c446000e0141c81340904a850090301011200000d140a0740c6403580304240c00d4507240c00d8a15940d0b10107410840c0d61280d031130454094125105040c500040789000041700c4003c4004002c20801010260104100c1102d000e8201603594142c0700c2446450300d007a800d50340e02d00030800107842c0c00f0111807601e092240049200c40d26013403803032081d0090004181a1621500002d4040c240380b161034031845880f030742c81a94403010b042c3c542c107000c56410b101ca007070a0315110401c06410304c4c041c40c045102642d254003414000c2c01c01c0e4000410f5640016010017015800309401d80502000e41c029840c0a02c4c10000030000341103010350340200302020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 497713120 1250 497711870 497711887
    0x506071e1b0b0705071502040501020a140c090a050412020a03142d1216080f1315151e060302030601090306090b01141e04020d090b15010e0d0b010506 66
    0x12000c0141a041480c034202d603d00140007503c00e50081c1010764482e03001c0d124442155415008650503a58103a001e48900d8400c0e0781c0312000d0884a09130b015040c003801f803035500f55440b030754882e41c4500d10122001c201800c0a0070036802110030784604900719040445d011001c243c101d0708000d6070000707004002e6502d680200e1a03451003080582c40710700005400b0800c41d018090440a070800405c4d0302c44092440d120071300d1101a5000d044a10008200d49800240380803000300c501d41d51080e41d00903c070791070b003a059441540401066486264485d41c070340c82d242038202c1c00640c060160031000140c441e034481c0c43ca00725081c00160311501f0301b056000070000301d050744200b02c464021039101806104401c81c619010709640001d02400c03e1000c0c0078440c1c0040c5142034101d2400701c4040c840f0502410b8071603010f1102a500c4001001c440a460780c0c6408000bc06501019110b0f01e402801c18111500580c00101074a5008880c02e10802550b483c08020440c84480305046503400c40710b260b500e600d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 497714370 1250 497713120 497713157
    0x4091703070e0306010f03030f090e04060b180a15060c0b1602160914060411121b0f04090b06120109090f0b0702010b0f0121360506071e 60
    0x701c2d0582d80c05028080000070490740c20722075142524071a8442d0000d0020540c0c04881c01c5009115a00b04145498041004144168400c1c459800042c004149030345560800480c0c200094822a940c140d0f503041c01c070040600c164480000d00054981310750b0380c1046032580404600c1c05448050384812031000c9000e043c0c0200120000808401529101e05a40300c2e9031400622100030203000a039031010010300d4500c0c1070f00c119407003070200c080000e060000c0a251803400500c01090035404043c011801e080480d0404041e000801d0b0b1203000c56a61030030070850400751400c0140842c0522000c0c494948040c1d00d111111b419210071840000c0c1030b4038241040001d24401e540c02410f0b5040384414000041c0c1d042d081096200010b6440c6940c8010800044a031407549001d580200c1c0042e040740780300c00003582c00884c0742106405000c1011036035001028140d110b074002d4403005481405030b2500b041070600c0900c1c0d010515041140c41c01c0280c001400400070440b15080030048071003041b840d8440c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 497715620 1250 497714370 497714387
    0x1e19110307030c03030f030f0b151b0601121505010f0314030f1303050d0e030d0e0109030203030a020f0706110c010c03120e06100f08191e080702010e0409170307 71
    0x2003001c00d0140099490174054202901140e5100009080100042d24156030b4010127950440c054019981004a460b1124154111030318240d5400e91174011202030210800650b070192a181c01c1c0d95244848510345800101e51104803142820b050030010088945e0aa032444110380c0c21081034602d2040d030861007030540c071a4103400100e124012542110016a80c14003805486c414412188043d03820441500e0028000110992603841421445c0c8610701c24070210345014010b0400311001782c0c8a074000303425900401c81d214016809a080d0004840e010003021004100c2d9023070101c540c0042d034405030f4407030b40982c180328140200144030908062041d001e0b2807844035030702c0081001840c000202611282c00380c030f22243c0a2900407002c1018812082c0380011543e042c802801e110024101d900010a4044019500740c10345a041461921201021040340d91248050b035a4071200ea100262103401c0100070107000340c0c900384210000440030020403c04040a0010303a031280d40c4c05208075035036075 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 497716870 1250 497715620 497715623
    0x50c07171c0203160c0e0f060906010f0315030b0703050c03070e011d0405090c01020705101b21080601091d040b0a0e120c10090c140a0312021e1911030703 68
    0x4404200c1130504c030211070240300755941e50480c060962618000c5a10b800c0054030380a0f84900d442001c100c04d58007407104070380b490700c3c2c41c00c0115808680080380c0d89103507510340c400d5038042c035008204038080d0b52502c1202d03403140c3d0f106005801d40c20701050040600f81450308182c144059064500c002c07650320b108003504e2040040c024801450305804d59620b900c4403044c0b180c003501c01c076200450903181490700c107202c14800c0e5440d144595a4458003201c201c0e0416410740d011142011860000700c441a803d03042c074140c80e1a03946032401c0140004000e04890351154054080040074038031041c400700615138100d6040103442141e40c680203142e40041008031a07855441c803e000043d21910709203001382c91704185910a5400520300c0c100b41d2004d44100c4e41c0001c01c12079404905001040c80801800750881c4050240380d2010340302d580d4011200c1d4401d1120b40541e02c410039900017512140315031140c1c1e04807600034000c3e5001c4680350030120602000c00904448102d644c01c0d0168030b0800c172020085 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 497718120 1250 497716870 497716897
    0x8010b030411060301240942020d11150403081512010f050a050103170c0c030114090c030a11040e0c0607081210081209030309030a03050c07171c0203 66
    0x2540c2d143c14103400080742c0d20801e09111005540313029007a010f10030f0b40040320144500f042106034803413030400f2141241480b600100030182034004264040e0000b59a0070a060f400804ad034085e00b070005400e05401d032280310203942c04840442c0b8011081c6040d02d80060341410820b0880c0c0704e009568540b2030fa40203900350041c0c060404425901e80c1500501c0e84605c400808000035180c0d110300505480f401d000140130144030038034000001c5003400c0100142404441650b00c0d919a1800003070035160001841c01344203842c5014490b5494042c0075585146608800402000d200340c3e449840391310005a0703041c450790b0365009001002505010b24101c65a004050580e103000b10b190000b5203410203d03502074080310100028a005008003002d0003540d64100003000c82d0b50806082c05015444580281d070940010301141c1e031652410820700401c0d0344a03849c1c1e2502c481d452100245451141e030300126409111425903c2443c070f01003803040705c0700116403242228180130307030040e451841845030f10f0200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 497719370 1250 497718120 497718127
    0xb0f130809010c0218070e03070503070303260408040611010e101107050f0f160f03080306010306050402210c0403200604030b0c0a021c1d030106090e0a021003090308010b03041106 79
    0x4400c80c00c41c6206d24071946945c0040e400e08014035543c0c1c41213010f55a003541c0903140500102c4d000d1203c01d20540e03401c0710031000c2c82c2c0100302281940007003a2030449540340d0216052183c1ea82014103540d50111b00f2000300310340520b00600641e1510f07400380c5c8202c0103030341e41d03c0715280300644000c6410464106c1e04a905d0554601c0c4295940c024410950001c2d000d21540d09105100707036148401210420001c03984441e0650702e0744080d6500c06400f080c10f00d9584d42c000a480c4c6c81d24009046800e05420210742000d801040342c480d030b81e40040940300022000c00040c00002c0343c115071b0746052090b00c401e07e0655107610021540074402d5070409402000f40100300203451091308024291540140d0944840d2601c150703044150b90303070101180000c5000030032203820050000c03240001000f00240003294066843c45c40f1400c468010f5440c25158201d48060415400d104071910740304070b4589001c000344074079501c00509058044c00340c900800740000208007404894210001e901c003004003038959 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497720620 1250 497719370 497719399
    0x40212010b0316030b0702060106050703030c0201090c03050c04060e09191401090f1101050a0504050103090302070b27060c12030403020a170301080f1b060c03130603020301030b0f130809010c02 85
    0x9214558131040324002c08850010b400f0790b01c0403807242d040742d000f5220b590030701180e81d4050f4003820303480d82c0040c119982c0b07501940c0441c02618100d4000c0d40100043d21010300004203100030b64545802a0640440703540922084000c0040e20070110085240c2e400c07070000320351801071980016031060203850342c00c149140c0c0500101002087c0c505100303481190783c083c00c40d40152140e0050103155000b181050204222950094201e50701003480f900c16504255262a1005001e410503412003c3c000c0644204c651001c0c0350040c0b4050601048407440e080501d600311007982d500c000d50900c0c1d0f00c1c95002c4046400c041c0204a0040c07220780c003402c5040500525109200d1981092040c2c5d5114815071101500805000c00c40c20340e29400706012281c0c1c0c8107103005101349940205194202032104000c100c1001704202e841c500a00403030754000da9203514506001401c0100940410350003017001c0144100ca00c4e0942c603400f04c0c0e55000c83c40d40d483d50719081c016560003449032400f07900203014451420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497721870 1250 497720620 497720653
    0x9050d05011404211803021512040303061401030b130207260a120513020111120f131703041a0f0a0315080a24021603090317030f040212010b03 63
    0x205032007000e58444e60007120024003190a5420180c0484888243e59000c1c005818008106140e40c1802c1d07040c03529100c0d15049900101c5000c840c2a000684c3e280340030f102c50072040c4d500d0081510b0900e01030141d4030103400081c2c8488585240308210780c0d8001180d504103c0c0246548803948404e18817007104c1d60070300c40c7c645000da110420000001e584180040b556446502c5250300405e50000c03041803d1a00781d0041d00c0c13000c019881200a07101c5c080904103482d00e10001848036610224800c0e0321410400100c00503184281c0003107441c0c2c03000150704002a4800019902111403070310080941151004010101d445048100c0c40000000034080d100309030107401c4550140c250a682c01c250341d0781d8030031072034440203401401845500364600311207020250401f101c2800c1c44030340c401460041260015240100e104404501080c89800100140800a80d0307040030ba488441e00c4500d18a0541843c2c2402400140000e203d03075188202c5452800f403d520440140c030000c2e0848600c000e0408820 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497723120 1250 497721870 497721893
    0x30d0906060e0f131509031709030a17060a0909050625020c04021b15100e011a130803030109200a36090e0607030b0109050d05011404 59
    0x180d4459051400005122000700055482070300351807a442056140e142800d00460030742c1134252842042d035480c0c0c0e1105040751240c510040e02c07a458521140c4140c01d4013080c0c20390000c260040640003031014180b0580c1003201001e07a000c45550ba1074250b42d0303c0b00082c0c0c800b02e407908202c030005d1038580041c0401030001780c01800f4002c0b070920b0305a011080101407003445182c801410042c0c100808082d010b08040c0c0150a412005c0d1844003095040c0c1da003040e14041c40c41604803a04a007900030f02404000104403000038100000d04003d0640c1080c0a84d46103014021040800c6000059904420002e44182d04007501c4401d0076642c3c1c95031346840c101c0280001c0001040d110444840081c400600c007004c075140341d002a01d6005900c626200e05105488009481c600b1000c1305240c07180006c942049400d01501e402580000c284415030200c501d461402072441081c145485845181e80e82c1018540702114421160501035165078a812800f50501410400103042c04405201c200702890048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497724370 1250 497723120 497723123
    0x1209010b030c130218040203071e030509120c1e060618040203060402091305030f0a090501030507091e09060312020105060d0c030b0c19080f060f060f0c0708030d09 72
    0xe010a80d960001c064849140400140e448503068401e11441d10301d07a0007070000c80741d03280749004828410002241c1079a000300c440d18001510341d2001800142d140000310b4095500b4582003101d840d1090405a4856900303100c00d207a407c0114516403121800c0040040d10380d044c4e862040e8420b4030040c00307075a0300800e49490344524030100590310900c0381500107a12641e00203000700499200c81d02442409180a02030b10001b002c5040b0403008110100300404403072006642c040c0d030303030049050003c0c45e0b07940513044a07040609003000c0c040840c2e405404801a14100f0915141f01480341c00c42d0a10107006a020f100320600f00403001060014081d9181c13900c00c03da4000b803180b43e0b100c0c1c007006084a81c0800041810403d000c0501c040b0719442285580312040424040c9004804444250f2003c4104801400210000104a002060b0140a030382201d0b050303030910604842c5000043e4580241700095102c15004107000804030380421411000f840e00318140d0359502502c075064009003811040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497725620 1250 497724370 497724373
    0x504080f0703020f070911121803030702030a0905090f0f0712060b0c011103090d0c030302040911130f060e011b141b030a020d06090201170a0c02060c03040f030c030507081209 77
    0x1300005d1b4a6004e01503003074410341d0361555524241c0340d49659049141d0113408440b80180c892120849440100700650140845800030354681100c02c038010103008054221324010340240c000d00c00708910b640201a0172000908185845950b030b07400403501031441101303e031700071030410000198070454040102410203100b0005d1004800e140b220620794407050b030341c221040d40003004001c0040e04c0390074845021403007441d02510706950b4606840640d0741c050b03017511b2042c81c001071b52140c40c5a610313070072001050a07046612070740303260180c060808035014a00d1814461407290b460298a904c1e1207240115522601590030501c100310300683d40c0401e40c00a030f81c48a20301005800070300e0001965035025500911802c10014241e032568007034900d90030700300d040c058418001640c2c0100e00b505284614144c0000240d10880c2c40c4000385400000b80400284c0d5a08200b804041420066200c02e403d82509100748070501500c0d08941324400d2003c05400c00c0c501007000c000c105000c55419004004940 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497726870 1250 497725620 497725633
    0x30709030b0a0c0c0314040306060b181e01110312011502250303051c0e16050a1a0c030c0d020c0f090609180109020d050102071e05060a0504080f0703020f 68
    0x604100310f42d400040c0c3d0000c10303d0b05031341c800024421100a0154008001c0041c1401c0d625034441e81910000d400259100c040030500781098a203120800051450455499240c51101d40740c1d01c07110207410300302a0400ca46d480218210303000400403146a18100c05a00c0c26a681d1384070400111510550560010b0181d401c20108080b0009402c444210a003594045090320710340e0180d03129409038170601000314043e140200341144d240b10300303034000038108050940b900d0304540502c0151081c1c2c00183c4154107107035051282500c01c0c1c10080c00e203116901c6041e80c078550392485501d1800340c60700305011842094090550103a01149070200c0700400c0d6001c03c2440381050030004c01c104222121b40d001800c0c1c3d4001950085a0242e00320000c107507500004a90015801007015184000c005a99603034001554a080210206800b4038907004403074007042c1c04555584081e1142c1c400b60a58904030b40340c0f00403805004c40380342202d00300865030b0740701d035610310340340c90045e480e9803203000001d100b8010b51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497728120 1250 497726870 497726881
    0xb030f150a15030b01091203020c090702010e0304030f020a050a0303030b030d11150726010311190608070e09130302010e030306060426030a0915020c0d02130e0102030709030b 77
    0x785115007a1803410b000a039002d034910368124010304c0b01c075808504101c091140040c0c00c003144595090300d81d00a9004e4000c03481440e080c000c0d00d004c0900543d007160b15001c241c40c0048004001d54094941c4884400044206400020804405500b0160b4011440d0b0300c000105a019400000310010940540359070412424056401d9071201c20001026008030070070300040440c807a491640550b1508240c09040c40001d00f0583d600d025603200590301548200510a21030950188540030300101c59000210b000d02c40c01c484105d49511800060168000110f5944d50040f880c0e00000701c0d024000500b00c1c5010380303560351540400c0f0700680144d480c1804110100c10041308136481507202a0000d45420724000c401d00904080703501204881d01004400d800b0703903209000070003108295075507c45030075040c50f0b220390042d00c1a0a203001998001d2410a8094945000141500381c0403130ba400800032081107603c014003000f1140c00b5095200008000d4520740042040702520300440341c1b802e091751407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497729370 1250 497728120 497728129
    0x6011b1704081504121b020405091606030212010e0411090a140a1b0306270902040515030d020304080d0807050c0a05030d0c211d03040f1502150703150b030f15 70
    0x124441030920344899080311b805400c060f00440d8220440c1400c40310f11400207120304503048900e42040d40002c2d000904100354440c032914042c0540300c81d40d5848650301302955141002e0054015190040d00d845000944034081a800700b00300b00500600304c0040d180a480001c010036403100240c0c0810552004004210f11138410f09042e6840038030558180c01518040b2403049a504140e04603c5460f4282c1e04016222400713203500aa80c201ea4a4512900003c00c15080125441540c42150b02c02d0008003e00d0000003205000d0780da590a12a1170380d120f42d42c0c1110140b10b0310041c88024844e840c07145040140000040819032075982041103184003a140880c0d00c0c41c041002c88000784181c0c51180354640c00c3e44d1003004503c404025800c040c0307500007030079800d54101f94003482c011aa02c080c00c06c0803555058803120070032482c2c4007400344010201c000301400c00d4050151020940d40301d42509804102c2c0c000b52000d061b14130750b200d440c2e103801e07142c200090714200d99026116803800c400791007a050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497730620 1250 497729370 497729387
    0x1030c0f080106030b0301090f060509120a05030f071e091403030c15130c080304140402070803040f0503130f050a08030406080403180b07030309050606011b170408150412 75
    0x25107640d002000d0f440c3c42c0044001c4c0014000c00d90707065580c4e020b80e0001400e01c0000c1508148500c901117014038281c107440c0e0811040c038405130071007001045441d0000e644081200d07070000d00c2c440101c8558a90301000c84900301240740a60a400d42052448650f6030021855001c60b12081a00c054107012035042c1900c9004124440155920008802040c4041c00b10340380c1d402441c11030450030035000c544038190020925880344100390000642481641c00e0a00101141c00050720294a03180055950300c10034400104050b29850751081c0c00420001c0c284101c88054404001c100211a155042035030703000c5041c0b044600c100d03d03098000807220008001d0320b007110f42907140c1d020700740d0352902c0949402d0b007480f071240c0484120740c0c0d02107010440c4c0405080000d000f40e6001071450340c2d030300d40240340c101c2c05840c0d9414400004400c00c2c00d0720b0240e40404200354003800040041d1200d02a5820b18000d0340c001102d5809201e40001e056400b00a00c244114011782c98441403072980c90007601c0169 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497731870 1250 497730620 497730647
    0x910050709080a230106170105090610170a0b0c0909060d05120a0e130c020c092503021c0e070b0c19020607020d23010b060a0c08160b010501030c 64
    0x4200204140c00b140c49030741c42c131000340c2d115014401d03c0000d60f009242110700c141c0080e40400084480d60898050900c103090f8010307002030080109062020308078691003e14400c05111003c802503084020300c05000c00040150b010f510082a8180344078075070410b4005241c468004c40301c5900250040c60b241120340d030500d401c0700103003204a603c10f44000441c0d00000c41d01c024010184401234131030302c0d403083ca1001420740c40c2001403110000a0000e00b000034800b00b6a01c20318005041c000114003802c6180e903c1608403100f49010b50345803d043d07010b80a132502035204542001d15021542c00e054012011a5840342d013540c0e0f00079111401c400d124003610500f10b02561201000b100d0f17880341d1030200300c01d0340e000505950409005500180b0101159074003119811280c600e0100304601d02813203050941a01c000034002d03200304d100865041d0056940550400c1801c030144000d001160080b030303500f40355600b40d21441d07100d2410a072440010a11070b05002a28210680003030600c41c0e43e0f1900c04a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497733120 1250 497731870 497731873
    0x914030a1106030612060901050f07030e15100909060b15030c0306010e15190801080307020d08070201030b060304030507030f0e0f0d03092303070902040b0d02070f0605091005070908 80
    0x82071201c05200c900d420040c11300340c0248000320003141c24001046024405e000300e00000c90300303241000702520204030141c0402d06042c20586404244c0c2c80102d50b421000c41e1440361215039035603e00011240180642c003003207000d45010b44000034082d850304031050340c40c0c00b95100c0004038020607032101144011503140c0c440c020b091000c074085600c00d14409291050048c161182d085009147c0200c0b5840092104030090080c00b0040300c80d0f4001540e44d004185e02c04c09503003051034507004218001441800100441000074501c0116030081d4800f141005026000704d450740f800f85400b500d02c0c1e103d09010707000300f01c914400404c1c0b948035020240c0e412402900741c59442400e00709010080c0020201202844045075010900203210580350700541441d80840c804001c000f005e050400499412112240c4c0c01004140144421101100c4244010840041e9035804a0601d00c02c0783c000004000c00460130101400101240003500d0021803140410070009505d0300d000950344600319200300d0415 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497734370 1250 497733120 497733143
    0x210801030f0f020f06030c03071830060c050d0b0618040b0102010b1c020114040305060609070525060f0605130207050c090106020a0302061e0a0f1503030914030a 71
    0x10b6100a02c99000318400703045020501c03030b100001501604221000b4108140100821446544c4600a80c110503046014054070508045070041c4410a403980d4004508054400d0f50700340140b0040d0360036050b00144e041000380c1d6854001403d03a40010700d10000d0500b0420b803904503240c400d08564003600480b07140712028803101d0600c00904192600c0c8d906555903400c1096240d202da83c2038146820481d01c050b508946d91f48005410900c2070341804103654803d000600000e04009282174003c4400c503000401e40d13440300030889403441610440c401510b008000003a0034800d40520b154014031a190620815030003c0c0c5101c101c40c03862080c160710070b4212000f000740c11080c0c0d0080482130301039415989444224404134803504801c0c1d11800069020181355004d041d818131040b508098242c0e8018924820180036030300001340601210101c40d03603050400d078220b01e1035100c0c078407a003540ca00e49549503950b82009403c0141503c10082069968a0000700c103203000f0a1008600c0d51200c1c0c031010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497735620 1250 497734370 497734373
    0x320705030318030a0c0b04020f0a0b0301090c050c1e030c0d200102090102070302042f0a1116051903120e01110d021002030901090f0609020f1503130c12210801030f 72
    0x30150187c0140d8128007900e0004034282c4900076440d000c1c1c085e21b0041603503035241c002040119064080010304102050140010706007000c1000540f00003105409500f0b4041c09032918158400c68101d41c08610400102d02c80f66500080d40c5150200e101c03001184c00031241040a00b030380b08100d03002e401138002c58814001490603503c01d101745801080d1002048440e803801c4544c0c14668220a00c041c107021590381e000f59884104919a14012005040c0e01c0c07a0400c100d402150603402503d204010400d036210b0000d0070641420001c0d508098203403003945a4840203030443c0e0000c2d50540c0041d010360070340d02d0b50303242c00507081141413002d5004207242c0c0001c151940003900b001d40803400b55500d0300c1c01280400e5480e8808804c041c0071303030300014034500d26204200a120ba242c9143d07000706080540583d1106000341646c4d401084000e031f80390070f4540c500e09503480c0c1c4074580240c603170030b84040300da20103204400caa881e010003400c1002900f07144000009a5008100b48001858400c09886c1e0300c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497736870 1250 497735620 497735633
    0xb04020406050607081b030c030406031b031b08130803040303091b0605120a02130602060117060c0a0e01030f0e10050a02090901031203020c0a03050d0b010c03320705030318030a0c 79
    0xc043c01b035034003079a0411003504409800c41c1c0c4550301010020751150b50642c0c1490113180e0452068525043c02c100300d039005c0b0b0100320320180202090051003400d90018108960f04486105401e40c4100096a2840c041c68040e005114055007941e02076421440410020036110800b81600e140d92030b980d08000080d0300006188000a04a43d03600c2c1d000e20480c114101d05480c26009081540c02a0407198100303100c42c2c0032901410800d002c07940c4004107200a006440c2c007203c0346454180360445c0e000341f100303005801514240c05144001c51038604c01040300b0501140d11918142080380c01d009076118030409005034065611003aa00040c06001000094850200030404041506001d818080803036212400d000c0008000d40100700000b4450764280140e10a8050840c82400e181e4040c1d215910001e0100780c408074142502c20380c20388590f59520707140403401e000346004503181c0c1c0c1d030b80f81c1448d2454682c1c000f911780b406248804400c0203048003001c07040e00d1454003140c2ea186010015601d828 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497738120 1250 497736870 497736907
    0x606010804081615050a0c1407030e100302130803090f030f070509040302120309010c0318120e03010e030c101404110103050709170c01110a030c020603041a040b0402040605060708 79
    0x111004c000440c180c413410421801050322890754011700181554101d40081e100410342d6060b81c43c80d00701001500300203030304504804010714050392a032440c4e450001c000c4d402481107404001e802007400350005081e902c004002c251000043d18881500c4046030281075a88840c07244100b1660400076082c00700e03080208030303264424024070440b942e0008001e060074040c0e0094030244216511b44510350070117501400b401c103443d050800030306025042c0740c9400b0217888900b0250000c010034201240440d81d825085141e148502030140c0c0e542c1c141c01e00105650b90120400ca880755401c101030490010f142d215040d1180350011442d0307031403420071401180108001810481802680100030560032000c00034954580c030b030a0000c0240f400000005412340010102e83d0209500082c44c900000380c2c0b00341d080b43c0050f030644602d5100e840314a17124201c141c004400d0807420507100c0421091000785448603000714000c0c3d90401c242c036100c10a00080b4071607041e000c1c1420714204841185003080c0c0701c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497739370 1250 497738120 497738123
    0xa0c0f09020906121f0f06090b04080d030f1d03040512030304050604060c09091113091b0c0203030c031c0e0a11060a02010b030706120f0b10080a090c09060806060108040816 76
    0x552070200d01345401101795030a65003140c0d81454446a0a001c459002151200544000b0300080c0c02c09251643e200d0ba110f102582100c2019203030011000355a159400a0124075800d420808042e1001d84030241d0f00e800602c61940f01e11200c05205803103243c08002c907402990840060329045d40c4949603100074101c04074040080010100f0000b5550096200340d04c880c8003066038040c1e458a0380e00c0003040c908030030780101181501d0404da080980001900600040d40182021b00034402203000180c150b010707100c1110010b01000405640c0441d0340d104035400b030b004501d002c0100c0000b072900d640c0c0d03c4503100402081c07910083c0c600d0a56180240103440751322103610001c521803400030301090418183d58460000300d02e400b01e80480210b41800744d0001c154420744100308070481100069171492040c0406c10600540d140850900c05a68011401581d000002c1c0540301c2c0d60385007058000c015511600c44d00b80a03450216440c0d42c40391010380e0080e41c2203140725007403001c034071080300728130500312030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497740620 1250 497739370 497739391
    0x70e01020631080f07030309030e010f0f180f0603021b060c0909150d0501051501030504020303090103110f070510061211300f060c03091c110a0c0f0902090612 70
    0x450307483c07135420100400f102480390380c0101d180140f07850050100408010701905200d01401c02000032648014108000c088920f0000307209010307031003008003007070072030300046003141102c00302003205a010740041000405510145960814001186480311001d54610b1000740041080b0009403404200680d04055000708a003c6080203030009032100000203422207450b5181e0041003101d6030b1000329103040c00802c1c04c0902540c581640040d45074414a920320b418140e80b21042c880e00403d81c800d4030000c41001c001c082c0d440708107003852035856926101c885195405c0c5400442d4888004058175012588a42900d060946a0040040306041c1101d1000c1149100786e2011000c0c1040701b4911401030010054184100c0e10884103080140081480d001d503031003041402441c1c0c90000d024100d04400c506a41000c5080507001c0b9031008003a482c00c10b003403203050020b1090142101040040b00d1141d001040120b64400c0c0c124140d0041d0f840c1c2ea90702010074001d07206400d581d809466400081042d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497741870 1250 497740620 497740627
    0xe010b04151407060b0f040209090a1515050d0c1d010e032a040501052706010201090b181c14070f140a050111030c22030605070e0102063108 62
    0x4100c0302c183c100300b1007a0394541c1c0316040305404e4100401103020360903040c2e4040d46040d81c03c001242e014031006e014a07a55581d160885a101050743c03012101414000c540b000b150158070070014901d4000500c10107034186054840c60845018020f44c0c82c10880380301b503210308501c5500041d607588040544494150080032801c61440309910070b0894a00c1052405200e580340742010b00c800c4420580006001c3e6001040e0b41450b10a25041142c46007800e24440ca040e5440c440100d01403c0351550007003000d403000d000d01c4002008101d100c00b19007000c604494418660107490103842e5580700350b40740440e40300e03691411580c0050009244403802000500240002980d801d4844108409480440d411130030300401000028000d44440c030001c410601e0131401c00000d4081103102e0741111048000c00181d00d0042d4482c0403941c0d2005540140741003005207003250000d04012000e080c040c0c014000c0038000395100c9410f600042d0b604580d1940800e038071070a0b6000844001c003100c8240c40e030b190b090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497743120 1250 497741870 497741897
    0x150d0e010501061d060903071211090408030702060f010303080705180603040f03090b1201050402090f131a0306040c031403043201031a0114131e0e010b0415 69
    0xd000703080c001d10165403148a13051000700f10029a250201649100d0041000320080607640011082c003943c4c036154885d00522413528203000d07a065034088c1250025050000c12051008450246101e0103a03602901c0c810360b220703215460520005d000007404a0210004509100d128202030141a19012505880c4000f1000000d800e03400880b41110900b0310f181d030360300415611282081c01441c0781a0131b070b81060b15940c4d0b90402400d0500403240560303404100c10109980740c48603040c1101002d0f1880881040824210f000ba11001c0c1108010010a25403d211810700140652041c6d8100d026603400c0380c15540d0702ea94013845c1900900b001d01c014440401d40c0340a04500200130038035510a030701ea645202014050740c0102c80d001038107147c9004c1c0902d10284440140540d15542441c00d10b00f00c2500040c0201d2a000790342c0c903040381d5107912038081030001d034007070500f00036482d898a210034269071501c442d005c0410034055100440ca05000c100300b0201c03a55442d0709455480d081000035516030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497744370 1250 497743120 497743123
    0x1908030702071d070f09081009020d02061b072111010c0c0f03051606051909092301270c170c0a0315050312250305180906150d0e 57
    0x103041c4143c00620744001e105020350071804c0b5031042d84003030804280407842c0c65451034403180c03c1c4407c0d01d0815140c014031030441d03885088110145900a140e140c0f2507240318640400b501c7c58180400b0319108c4e2510109024604c0494100d441c4210f50488139043c02580d1102c8141800c3c0320510306200380788400c20002240c1068001c003401c403600c9250707416441c41c20f001c1e14005602e1662040003481d12418442d02d81d200d400c1b55440141c407184440c420b030030b00d00700b00c591050a500010b070710f5241541d010030380f102d41405278240b0840d003541101940d0300c501d6600e0304843c1d0744682c800d00b00386990340500c0e06622030300900180b0425042240080340105110a0000400c0759223154448000a0047d102c64040c81a042c00c13144188403009200e0400000c0781d52041400103030a001c01c0d01003206240d804880701c02115038203002e0b400d0042a5528074001d08590040d00890200c42c071a03800a04883c289580c80740d108680c010848298a00e1082c00d0b81140d0b44010702d480c4020380c8502858052000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497745620 1250 497744370 497744399
    0x11103040f0b070614060d1209150201060e15060316140a050903060702121c0209030f010203102108090d05060f01171b010e190803070b010503190803070207 69
    0x2070889039982d240940e240010845400340300d03145070405d4650512000c0d1b107d00c25400080b41c3d00000f154110740c0301c800c096a612009512440300ba45180349a880e0b550342c1034018000706c41c1c00703400004042c0c0710850300a80141551201319044082400040d5040d8848402e455501c20681442c1c100e0410410b540300040e40200c0070100800c40000e100c0b006414200041c41d401502440079000d2604d140b100e442c114130441d0000d98482d1100c10009045182640c103ca518500c02003c07210b0300d07442c00c04c2103400f03504111303404000c0c0610a41c000800b8000011030040342403202802e20340410081c0c1d2982c80d25048541c030540c204280c0300705013000070410000580100e400c0c0c58401d2107585041d480c05403200140c80c0344003140d003003c45921202c0c070344034552507844102400c10300850001400400c0e200710541d01c4100c80345908541c009091040400101003407805448070300b40326030701c403000c1c5070341d880a1001d13501118202d002600c01040c01d01014580000143c415188a06c0da102d01820342500d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497746870 1250 497745620 497745629
    0x609010c0b0a0504121112030601030e0f010603030e03070b0a050706020909130c0504020913050c0913050627070e06091011010510080601031202120309060a0c110c011103040f 77
    0x242e450060000b480711000000302e254103249046e1643c10f1b0100b50240d20b03040f4440c1c14428101010020485c00e0380030ba042000d41294402c22194001c5000c0d1401d806866684015004901c051400c2c0c041410041000e41c00d550700104418502900701c4011509039018400540b841542031000032481c0c0c0e505005a80205440000d03020684080e0416440c203500d6079001c036101d503204103c1d038102e5880305080da540480c0c9081c0300158a60f550080c10101e44032300408550301a40c118070071003100c5155400390b80100c5040d074110440c41c8807654020a04081050b18140b202804800500d08034401c610301e40202c0d4020301240e00384a583c1010441e07603c1c03440c08003804201901e91408105100744204d682c802d81002d06981c2a6142500840d11900180005010001d8a810a0a980c1c1c02002800c2c5183c903036104840d0380e49031000e0341c00d4030b488050755003200807800d000071000075901c6260040003010f040c82c0504500c042c4400151200555050350000a02040c080002d04c901980107480081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497748120 1250 497746870 497746891
    0x118060b0a140a291813202808150a0b03151908030d0f090b0c160f2a0b2505070b1e0c1b01030b031c0f0509030c0609010c0b 55
    0x1036014404111ba4841304910310200c02c1c0c5041c030700600c0000d506421801c81c0211214550f03541c0044112400e5818041030085d40d0040c43c0700d80c0055140e8420400391060481500041110100c1010041141c0c103500c42c2e001031040070700c0030a15804e4003443d108150600148000019a20a02d0145010038a6848841c3e2a04013080c4950b0702c405038080c000b0f2413080020304029409580d41d54151070b400c05080c442d1800408100c07030320a501d100300040d903015001200c03000072880e54034000c40c14070b5181190190034a03402586440c24204100c104040e10740041c610b9003418100c0105092241c600c004660081102c0700c0101c0201d0001d103c840081c00240d0601070340e40320310030038083c04111030b00d0000c0080401003106c003c41c00004075000318201c03645200c420043d404040100c003d803070f8001c41c00c3c1d41800390288942c00b0407044d003654154684c4c03e844403186000301200c15a064002d4009180d016004802002c00c81e150030720051610140506168440342a213458259000c0300c1200d040e000d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497749370 1250 497748120 497748157
    0x300608100902060708070215030a0204030204060b0c070314030708070506150d05030901031d01150510020304030f02060702040e060f040302070509010501020a020108090118060b0a140a29 82
    0x104018042440190318421091200c210254040340080c802c4140141403581c0100c0d00c03008566074151102081540a1b482e16202c0c20b04904420081d409840102e1041c4d2a006001038455010b40c2540c0c12189010043e064035469a121015810121040003140340010007190303000031041e50180c0030b1140030360010039103840d00da180100440c4419041c00d102d142030106010001d00b0000842c0c00d030300003e20300070841c030304805d80e80d2090a2038402190399950030310106407148440444a5022954110b59045903c0019003081e48c40303104500000c0c100fa4021991603001d420b01c0c000810095202030000100d01e921046004c1c2094005d1ba001805000c5100500040c15410000440036200488003c4000c3d454100081c0d40e5512aa1000381804800000200d103017800b0342c0203401d140c0d20210b050b00d010350139242c02d4000701100d820701841500011030115a40782c6011503052045406000301089500f802041c1000384081c101900d200c0305904213818480038010040d213000300c2c01c0c28401b2135 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497750620 1250 497749370 497749379
    0x12010209030105072c03010f09121403010f0b03060d0b010e1e100603050a09062412260d140a0e060702190305070c0617010806040b073006 61
    0xf5100301a011804010102003101410b80c408a0104d098643e04200034800007414808207024007408203103580320502c2c2802850a1000945010b1603507070880d41c45026907840c2d00382005880c0020300807203c400e9a070308000d010381c0c20500000d641111004081010040040d03407060000a02600b1500324a100702c02442080800d0203540c624580300a1004d403002e2074a010107545800d403511a0000301601c400c049801569645d0bc10100260410000d0005035141c0700d001c4a0951890301e03503a0700fa642c0003800584800c1c4c03a807490325a50360118940000c414100000020400c0044e141428900300b081030700300e8107011303214042803c0422070104203103240c6021010100d0704100c4001c00d075500800c08024000b540403508404e031035104c1c00c0c4e0402d84100c9040c01c440c1c41c042c7c444003d040360021400840c2081d0003005042c1d0f03500b8182c4419500ea0f890b021301540324981528000c0ca00a069004580501e0188689010000203418240c9009140c1c2c0015000c00010700e801d8800581c1c0e800d003d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497751870 1250 497750620 497750623
    0xa0c0615030203060c090d02091503010c180504020c060f0705161a0c16290a09020a050d110411120a050906060d0b0a0f0608030705010e07061403040209070302091201020903 76
    0x251703c00c2c5c26911407800e0801d00000700b060880e00403030087c4500c14140004082000d050283d0310044005030007040714090303042d4090589007610041e121a8040c0c00000109403409008860784107e90402a24564540b0341200c200c000c006810001070200900c01a49403c40c0c10080c11a601e0240007168651001ca010f81001600003034004010007208026040d0a40c001009100f1001e601c2088802c1400351413032403405000c1a914034141010784041403200192190300550761650088440e0090342c0d83e280308002d28500a1900104007180a510700c00c428a440d521801808550318550303490088000000550303580100c071545e420300e5644050250450040004075400902034980f070702c084d01a80c0791203812030310003030142444940340c500c20000c4041c2ca0f0401c100600105084a031282105c0c98101c1c0a030000340401c440902c14498002081ea2242d0710104824030b20049243c99a1a1f9809001010070028a4501415001c00c6248800c1d1078422050700003401501c00180c4903c0c60340c0c1090f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497753120 1250 497751870 497751883
    0x7060810030f0308040204110a030501030c08010e0709050a090c150e090106021e070302030601182d0c020c030322080c21010b090703020309010506010915050a0c0615030203 76
    0x200d410804058184000342c0d0318500407109036098180380c1c415640e0b80c0300003009002d401c6481c00050102207400c40c0200e41580009058a1190100300480c0751210201c41c2210b2120543c0340040d8840e200c10450b10785140e0043c0d810031040400481c0d18a07a075160100803c560b503210308680c0c0c070790a55511940303510800700341d0881400c0742c2c041025450b00360025911004544580403000a01c0940040c3d2075080240c500219800307801c2e1280c170340e520500d60141d40881c8140c8281c0c20304100b01c41c1d824420008c05100c00728000d2643c02201c0c1002032490b40282004211401580f1403800d80e050b042d40c01700b015144041150240c01c1400241a1500b16a80e51640c88502941c0c46480001002da032110402c2c3c8400612548032400305075080c7d9454050034030400601d0304030742c0e42c01c03d00c450654075400440c03048403c00028801da4030749100440e020010381c070035643e08681c06c070720301d01640f4814001040c070340c240c030b01e080c0c0008e1090751034940443d0004628901050002c5008008500303007031254 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497754370 1250 497753120 497753131
    0x4091e0308092410092d0b060d1d1501050907080603120919081609020f030f040215040b0307090608151e220506060315061c0e0a03090f0b0706020f040302060c070608 73
    0xe0016210101c04142340340681400c0c080050f40354030721100c40c0700070194480d5440b482401158012205e114061003540d90038020140204101c1e0005032100340201415402400042e00814030301600680503841504000400b561015580206500d820940358103140a00441d41c043c20700305002c10032404408040380d020765052030050100740d04244103075003a01d50029512240710b4095032507200080c00c03080001c42c1031066a101086c081017080400014511851968035081841900c0324016901508100e82c02c2020302203502441c09182012400001c1200ca0203106236840801ca0000a0500b489420603540800401000e01800c403118003480d42c101c0d01c2a04c0c10b51450030000f07000c21802810100f5a4081c4400040300b10b0300a003441c4c00341e1081c41002d842000144c0c8a80c0c50700d5140c039003441060f03001601d40907022503500c0c56100068222104503040300d00d42005699100041d400c00c803100c3c001c059080c8000030250b140c240c0103110542c407040217440c0c03160030200d020785402806000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497755620 1250 497754370 497754461
    0xc18050316050607020d05150406050a021c1104090e0a1a01060507080705072601050601030b0f0112062d0602070f0306050604091e030809241009 64
    0x818004022a454104080e0340041c3c842d03a84c0c803444c0d400415031600d400c020080c114426101d281c2080400c800c00940994854203040c09152103c200d654282d0160300603110350510444010445146a98400c400a00302c01000c1d90400e0b5503103e000c0c044a00000d40008540c1040f0811f500700105400c0d1090030501c0c2c16030312082035061110082042c000c800b0001d15280002900c1400d00004000c0c0c44001d20320410142d071581c11650301450f4006a0f0340301a1050760810700442d035203600034083d030703161510040d209080034840c003801111841703101243d801100d5602c0a0104101d840301c41f2086449144a524400060840082c4007200c0050780c00502150842070040c4004041900d42ca0202c80e04003e01080a40303c00000800515a03d00c004101e0440980820b00301820350102e40c0080e800f949a1070103d680d13444000342c0300c0f404900004400450704c1c20f0741d5820000c041a041d0400b01001c1d01180964480440e4400c60700314003102c2c00398034404038803625003a80c04011450300203585103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497756870 1250 497755620 497755633
    0x109060e0a061a1b0118060e0a0203060a0906020903030f030405070602070b0a050c0f010e3712020f030310140d03020d050a0507081303020102280204021b010c180503 73
    0x40c00c030f04040c4280c507401d500b007400001c0c4804001c20400911252000741030020001000d544c0d08051000c1c41c012001c4600a09201c03051480d56130208211580f20740240192005940380d81c141401802e803d4811507805900303001806454a040000c0d005015000702c069070b0300c1c00c0608010b450030003580e00601c00c5612294041c050310461009032425220715061094458000b1158181444d4115410400c51741c41c11a402e80f001c400010f00c6c00d42811258512200d07549024981aa40704500320b40200310b0800d20b4032180000c0303100f1172101d102c804a2050f00d2074080010245821940309a44100210f80310040c10300c1000a00d0a070b400003405c00b180c60460340f051036500030f034640c05044a80018040d0101da94000a80204101c50000ea0700060700d43c0d03126640e45215441c007203540411390041c864241c4050b0442d8610030810034840d251700089500c0e4600c1d90801000e584010340c1110f201c003694040c40c5040809009400c0a1200c40e2101240d050070560604500201c43d40703d03d1007640201e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497758120 1250 497756870 497756879
    0x30512070c051225050423010b090a14060705030a03060915030218071107120b0702030f0d0b0103021c0209040e0105072c181801091709010e090109060e0a06 69
    0xa42c0d8150440074001c5000491080ea03101103015a01e64011754019080404071552040030110780481012030350107141032070340c942c0c0305d141181c0100c801090b00301c0020307a014400281601c41c1120340300f2004100c60b1030700074196180350454004010260202e40c85a8003841200094024602000d00c5580c0f9020038901c0c6400140d0944140c405a0025001c3c410119504611035024042101099000c4803003499858054407804110018240d904600074000300e000300d840407084446c000b1030303560702d0350030000342c820010001d0203507614143c1410341c00c010025002031080190840001074610047e102c0c0750880500c002da031008842600140d141c042040400742d08903251150b040545501890f442554250000c41c04164401e11075201a02c02e24a461849090150502c600ca00000e5070b10284088403c9a09895080320002e00707620400288920010000025060070441407425586444504000c10240e940a0300003056140e114031040c4540d091501c2110303004072009004112140c40d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497759370 1250 497758120 497758123
    0xe100806060607062406020309092202060f0d0603153603050c030c071d0405030301090b03160e370e0a0c09090c0b0a080604020a0207030512070c0512 66
    0x21104020700d0139940e844001d41405008401c295004401da49544a941d16041d020b9569005112000d210346050000038004802c41150b00c0c10240750640d084180030100e03030030803a443c1c108000c4901181d1080c08103012089081c007c42004500911240d0011040481c00c1c50940d0000d404000d42d48941c45215500d09040503145031401d00d03079044100383e5100c9854210341d039220715003502069200100d034504c0182000b061180403520b00c1d006a440c0c1041c11224a212000111006802a0800d00c010013800c88507401c00c1d441120700800380c03400c00d10a1108044800541d402031106044104104009507103469500d040d0b0744501e20002d171000c2c00341605e020594283c1c103c108840d40d05c0d0718a030b0800704010030405201c9030307100d508003c84903200c0d001c070401429070f1041982c280c03a1840c0c0010750100210200d0750310382d00030b0340c41e00d10950b503036014840650722480f0390604600c100000000810320a1102511424503c2c040550307641841c1040070fa81c1d011900018802e00c104841c20801400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497760620 1250 497759370 497759377
    0x11070f1d090c100c0c0308130609080d031d030d0501031704050f0418020d0b04030318020d02010f050c0703030203040510181a0f07150c0305151203040306060e1008060606 75
    0xa044610b83c000003a0700300c080343c4041c1d203030070010025002d001c404000c020801d005021500501002000b10381e03600c40049504d24681d1040b0841d6401c840f00600340c0034441d82000d61203048030145400e07510942181580b07160300400000080c03913602c00040c81041203ca108004004102c0c00c21801c003400d05001942076240340b41d01901c41c6541d0b0342403486c1d0024040300460302a400511011103004941041e4800303010440e0100d00180c5068071001c0e00320000880c5554031a006013100002508a0f401520200580e20908051010a1204070b08000342000341c0c0c00914031907806151075034980701c10b000d0035502040c0200d0030b02010022104006402100e400210b451300c800c40c512403019140c0041c02442419048140610009180b4007840f02c200141c80304103202034030400ca901410402141110016100741c403e268249400c40402d2a01080c01203000c0304d00d805403480c150703130780d5501c0c41200c015611001a502c08201044094056080c450000302052401340107940f42c0000082c02c00d21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497761870 1250 497760620 497760643
    0x1a040b1011010e030406020a120f17040c0317070218090a240c050a080a0603050318010e040204080c24030f04030509090702030306040e010902030705010f11070f1d09 73
    0x202585600324101c2094201d80e5602001c401500e68032911404001e40340c81140340c06032080c13a180648410b01078421100c04c40310602e10340d03860550b0718009004030b80550021b0004d81c2d02414241c401300c041142400c0b5503004103410384a80d9a9a0342c144107200ca4210500c640c41c09040c0c4000801050070b4001c200c80e03000c2540403807040380c00240c0055405902a5071414420307000d2400d00f44e40700b140d4100000b807000402d2901d90b0803d980d1801000001d8403400d01004166401c144441d9241c202c12417035035500c04005060200150641c04003060803600700741e0003400c0a91000c40402541e09002c8815000c55602100c0b04859107a411004012440b000d0041c0100c04181c2e8001810b040c40303203003564101c1400820b012080d050043e0002d40c0c90b0000e440b19445280b4104801c0c01c608414824049600c0d805006001c00b58504001941c0e001c071060f00f020184910302504544400c018041400a001c0b24401c00420605090207400003d03900703135000c0304460710003040c0168032100040841d07448 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497763120 1250 497761870 497761877
    0xf0509040f06090c08031c110307020a0204020d1e050105090705030f040b070e040f0b0f03070e010e0a0b0a03031d0a0e06102a1b120305090301090b09011a040b10 71
    0x20516020110131030a511108942c00f01041c0c81110a5140c0108004520225010701050081c807003403c4043c03105688800261f131100c0780600041c00c180e0054903890704008800514264400c8400c0002c4003030105d0b50301c00c156601c1c014480b41c40c1c044d00d07468000e04035203002070840c582580c52841200d0040d0000c1d180c401240001510b6510810f0824030b00d81024005000400e011881c1c400500b450304c00c990301c030700700540e501d071220708000070302d002100d906250210a5074a05170004580800141c841d00c0065210342e000405919800c2d003200041d031003035461010300350244003601c200c43d4003546614841d0030109420070441c030f80358061540242003101e50031400c21f114001903400d03080c80b00c818000d01240c0c00c072402c642031f41520b040c44860b0240c203094000d8107204519290105081c003410405013501e03503810000c070384110054065000080c4c00041c00c422141c8a1640010301110102c07942d0703444003414101d520035066807160001099034203221003c00d010010b8041c400148415080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497764370 1250 497763120 497763131
    0xc1a0301180605100c02040b1c3206010f0b04030c14040e071d09060403090e0903090618010e0909120903030403020910150206160f05070209100f0509040f06 69
    0x20030641c00341008083c01400125910303418100904014243d0304180c0c446c62038a95440028180740c0d000051901400e007404400f10420342c0e40d420240f00c101c40d216000c140110f84602000c5200b0712440d12005030000038a440d41c5060038615280d0b95a8000f00800c203c140030400c000f07003041c00e221055480b204c3c1c408030b019081d0000701e801442d480a07030804a21801c0c03800501141092103045840b001e1158500541d030700c001481d552810705440040c00950860300401c02c9401824145070070586030380540c0c0c40d10040c2c4001921a4200c0b840c034154010088203140c0c251341c0c20400090108109560451031494881c140e19200d60b49407800f255003420001d80e10342d03590380c140115000b841e40100801c001d81030a50f00800c2d500614050701200e04014010f28071081c2c00065110f02c5404440e040741c0c0700400480d001c030360540041c1160000d0081c00d1004800581d180c2110728415012081c400c00d1143c90b0551554142e4111b60105d4040d031841e00a200104403200c84490f000f90300715501040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497765620 1250 497764370 497764409
    0x303160503070f150b01110c2709010c111902010806040605150d150e011503020708030a200708071e02030717010c1706090a020f0d090c1a0301 63
    0x21845641d0b0000d0000f600388201d42e04010440032101d01101a03690204002c01c1c015005403818460200307038010790361082c0c061440c185401c8045d242111b07400f114600314a40e9102a03c0700c161303810f035000105651500e00549055a00c4107281c0b0300d20f0300a000805048094440b903020a400c0c402c00a8100310130280082c170f00c2d84807504008000c0101506440710f14080405440e1650403025441c40140e09051402d1600c0e40041c000406944034001d508180c4e0740382012030b080040c102d40d25641410f0302801070070b001c101e000e40954803031a618440422285406900d10340100172803090001160300622103140821082c00940b60b20030380c0885020400300d0a03a001a02c2c02400481c001d601d48107080010440b030103100300110581c14004001d02c56201c803440300740d540340190426448003181103800142c451409a4426800c440c01d900c00601d441e1444030078071550790090255001c541d4940f444403080218031001c002c02440b501d0080358011090202070701c3c03a44410b2060b0040507009444240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497766870 1250 497765620 497765623
    0xc011e03150b0a030504021e060f090301090b1302030601050111071a0409061d09030405010e090403030e06090a0201090f0b071b09060f03060509060705160f050d2c03031605 76
    0x4020b81046001d054071010003030b8004021384030898040380940040c0b4400340740ca41003000282c0e1720440080540d0b06180361030604281c00d40145a000b9419901d40790302d640452192101c0038042c0c0c0c0c000c0e000c03403110501401032526006041e8000c1341000308208803501441c0c0d0100c0c06070199a2610008040310001d04140d6860f40160b41000d10720b245820720009214851400d4030b0080c8803800d8444a60b81d0741c45191940b40d00580c894980860180042e801c59450b10700c0010b40c4c401d119040000e40d0100460515286c089d0031180b6080320382c0440143e400b590303040302c0382c074000b05070a0040006c01424070305410098000c0820060134200703200e60040069041d415034002800074410304100882d03680380345040d00012031105803409864080841e142e91804141d540c41211141c490300d1504c800d00c204140504241102600e1034901140010002001030241c02d4010149a07503259900d119080401d0085440ca06140124810409207503070a0300c010040d45c4d001a141c3c10042c050058900f84103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497768120 1250 497766870 497766911
    0x4090f060e0120040509010608040303022206030e010204050319022103090103060803090108011a12160305090d0926031c061202151e03090c030c011e03 67
    0x30046410301180440d800c2055010742040d203040020504003800c0302100341c1c400d105900910781c01c48510b1006204143c0a0b40c84243c220f03100c1c2c03070010318200219030605108401408111440030710a00700b00f1000b5414081c20440da40d41c03400071131529180100003a55000200b1022a41222083c0c6007001e41d95080049844800d02c0321000e0b5400b2a40d0b00b0072603c030790000110700d0211f440c00501049550000050b04c5c4061010b8645000390f07424448082d0311041c0b1036981c3e980742003007000780728080055141194040e8800d403036a602000e01e6043c007e02580c1c00100840816030080301100009a848904181103038806800c4104c0c904640171003111703a03900c040c1c3c80c1e40c80b480001052112181c1d180c00c00c00c0c9019810f2020480076490300351b10b01c41710494581c080c0d800b58803c0d148600c075507003141c01050608054107040301c000c03215602c2501d154000726011030f8150040c003078410f4682418403030303030b1210407003441c000031000c0c00881c202014914440354070702099643e0003c60100200703800003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497769370 1250 497768120 497768123
    0x130e0a060b0d050d030905150f18070b0f030121050a151d031c0c021b0301060816030b10121103150c0d063510090f0210081504090f 58
    0x241c400b00811320002030080c08280104544c5841100b003034007080e546c80f000b40350103a24000110605034032a00e000e85a03440c0410003104036800381c08030024030a16140300902140500d281c54a48941c5403500c0411180c42c400b121500107003000c4085c0b00000c10100d03450301101d6211000510354148245580b00912841c00d00c43d42044440b218180c9942c0c0000140c0205c466038507030007118142200300d07407050303840e41c0c0704000159002c0c0d480c4410703a0b204003100f100300744805800060308a03070714600a40f84c08030740d450310070308080a140d00b40144007c106074503611068505000328400d1400944030000c40c02c102d405000b144140f904917000f540e06100380c0203059150244018103052011105920368440719010f1192440c251001510b02c0121041c10140c410b888074852520176440c1216030404144400c91003140164244505030318058411442c0c0c96001e0440c60076440164814000c41104031410076091050080800402164a11400c10a590150740125145c2c5083c41c3c0702c0021800034a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497770620 1250 497769370 497769373
    0x50a0c060609020405040e0d020706051b0d03150801051009050c1315020c0103060305030a08090f07180605090f150d0503030f07030b09040f03030c0c020315010302130e0a060b0d05 79
    0x2920741c2c054000e8420365104640c10068501c0500c48640e54100003030b15a0702682042408110441c01100980404a44842007400f02c02c414000769091114005103080820360388c482c2c00d0002000c5c203510802411a40b0002c02590500800409905201c0d00c030f450006a100c3c0c001645400707100040c6d495090409080708051900c4842c80300c850503844100c3c200601c0395204d0815150711a0081c441101d400c240507510301f41e120303001110305180042c031000b820320584980b0285004c04010040041800c4600011418045107100043d40c807030ba0300103440b8030b4052301070003020303101220b640c0d8202c4540b00b03c01c0c5514402e10701113000c41c0310394003000c0d01c10f001c00300800012800d800800c0d0f110711080c3ea07080204014500c2003181c83e80056401812030f201409080c070011780650300c40c000a00c1c1c2424169501d90256001a1800303080503002c00231284000d00400031410100031303420395075400d241d060140001907031000c2c2d0f448010039405015503403980030340340c3c0030780f0f0300200013a4450b003000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497771870 1250 497770620 497770631
    0x1208121b030f040201030509070608010b0d15060e01030f020a1e090807031109100602030f0a170405031317120f040515040e061503042004050a0b0312120601050a0c06 73
    0x101c0310b044603001110107a000c81d003042c0001302c5071100802c0840555a180c1c48003545a401c0262880850300020480e1162960f41c0702d030b4002400503c1d50046c0103229582d1044403214a040006055443c000724102d403481c014850340f111260002c10000b20681c0885810b14440c0340d1500c1103542001ca64010520350084e61000b1041c480e8566211407400e00a40b140c101c00d4407501404907003030b002d502c01d500041c0c03c180304102c24000ca210040500210a1078610780d29112090403101c101e1094504460603800001c4598160603100504401010b14002c101c140c080c5112105403540e48041e1801c3c0c64101c0041c0b03580d06441c1c00f805031000780001814114680f0400c420070190307684103004000101c00c81c040040d65500d05075031100a0007050400c100e007076880e00c0d40e9106d54030b00301d1314040003401450311081c41d00340c68a00c151f500c503054900000c00d140c15240d051508014400c2d01040c2131040400c4481a4050b03401d1400c2e80014080ca041035031200744010864130054030200040c0f9450504 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497773120 1250 497771870 497771881
    0x9060c02070303020c030a05030301030308090f150402100306030c05060f1209011d01152106090507291e0c030f0306040b0105090a0e150904060e071208121b03 70
    0x580380e0a9034031a40890b01d0a074417550805581d400f030000020510b9204000510000b84207009035a0845d001c1c000315124004130031442802c1040c1c2d10f19906640c0d000b0420807065140c0b07902000c61661043c1003c21505095840d504000c1c50503000d8107010701c1c1e00080e0101500e82402c201d403191209404104100c0c00c045d0f168902070300340e00f001c40c0304420011500041e0700300d044c03050b502c4c20442c00030700e200340c14035100c86a03022a401e43e02c4405100b054105400216615005030307440725216102518109041145050b00005070504070100107210505410401000c002250282c1d45e2040c1c11490030025000201c8803481002d4401c00b090101040758048801020301440c014001128240204251400115404e0252500c065801407141c041080040081c100858110380000b500d0a0092044800310744903e000f40c03011190959640810f110082c4288001400f6000540c20003051032266102d28086029441c81e001c102240e242c049400c91540340351038481003040c24200d98492401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497774370 1250 497773120 497773123
    0x711150c12070501141003060c11030d060e0106051e03060d1203090b01050d080d05070201022101030210020d0504030b07090e0f06010207081c03110702041b02011503110603060409060c02 82
    0x1c260101ca0560070402640848541780885034032410000d030006c0300032072964031864081c101410386d000500c400350307110751082c000620044c9406110b82c5e4020940d18a406101000d080d8140c1c807040c1000b8050084e9901c1d852554010002202c2c81c00103103803640c440600113204500514402000740c2c03100085c42d4032040e0103400c1180418065408040a46cbe070f900240070000c240c0110003440701e0410014402280c5080d840b813a00084684001400c04203491190010091900445c41e012304400c00104114505000000b4500025101800240c07004100141c42402503000041c4014142e1000644161241c00b88400802c0d0b04600b180e180d007420b004c001340354a01a01c0e0301d8010301401501040c0c501e4001203c000155118041010100c0c40b07a000302c0050407054106201618200000e0300942e486009403442280a17254080002f9640d0401070300711248510720b403110815480041000c154040c64101d008c46040d40d03450340d6941c840303000500400070a0001441940380000c0c900640d5030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497775620 1250 497774370 497774377
    0x2030f03070308090f07060e010807020c0405070e0f0604050105030103080711031b01170405030301180b0301020f09031522022e120504050d2303130c0b0711150c12 72
    0x180405584004561802e40c981b0b0380210300030480803503030000950030f040d48901d020651201907481600d8135140288001020f81d40180e45410010b002030281c104c00e86010a040255400c044410600d031600c0c00002811a0205210141082d6400b00d007410074482e40613016980850020b068501c50b201c090514060482c00e290f8960014a080d1204521f2140f1501d0b180c0c000c80d005801141543c2c6003203286180c0400d280308190307150340c440c2c40c0b05a080d2001d0021303007503810700110495103800140b024075103032a1a00e07444855030b45902c403c2c01101e4500c580c2d414813280310180100d48400070390001c640c65040c211500c0701c09c041c0c030004101c590308200b810010a19000c0d03640a805114003644082a031f98190703006096504941d401445290065405030002c2c42c40020001c00c45649072104009604200c90311018280f06450304400c2000d0f825100d005403000c80402800d00e4250388440e00f0003011740b038049002e0601744032985aa0720001d0251380c2d43d6070000c1d045650203003095003080003942 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497776870 1250 497775620 497775631
    0x2d030f0f0f2003010506010e0907140c0f0f120d090812040c03030f0c03080f101205070923040b10120309140423130b090a020a0f2102030f03070308 65
    0x70b400d0030110080307180600410f402030005944079800c4203182c00c00c00c0140d52000c1d2042c002e11500d482000761070304408014001034014940941050442c1ca66181c1c02d00c0410b0b4481542a0031102070201c58460751415649489924800000c00200c02d242400942c442c0300d80748800c645d0190208001c10960603e2001035911036035400000242c81107040d03400140c0010020b0215049100040e45c00302011822a0300003040340900c51580e81d03441d44c140012107640e030180e601e41c01804003408500090700841105200501344c1030300040403400d610605580141000340650b00d10380c0400c100d4813241401c07901500e039540d803540040784c691401601400241c896034480c1d030a00712a0040038034051140f8509003c8100e820654020040303580156418001c000a8420600d00c800e4800314241e401c200b44503406101c0203151340d0400b0b004112480805603c14640380f07102c40c00600c030b006a9000c0c2040c840032140301c45001340000d0310000f4282948001101c0075484041100000e03d80c0c4007050b18000c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497778120 1250 497776870 497776913
    0xa0203040b030a09050c0118051e0904030f0206100b04091806020406050702130203011a0c1203010923090c040f0603080a032f070b090115060503012d030f0f0f 70
    0x102d1003006607005400c804036070808c801744050821860402031010102942d034296031080038820b000000f010710805440075000100790380314110341e2640420060350400003003130740441c010f403812007408202d10580c0070f000c00e0076032a8000916120f4080c56007080380d075407110b015900e0307076144d0030001c1041d08059000e80c840c1140708480f5601d1909032086905880c007140340509648203494400c41c1640c001100441184140341102d43c2e400e40041c00b07103028100704000031841d8012080d000204c0c580317440d81c1c6583c1201a50602c102490300090008141320b080d240401d0105400c58024000c0c491548054803522000031f0b0000e9440e80740d4000c1a506070f01c0c030303c4030380d2003105c00010344099141a440751310040740820029003c64000c00e60190b001413082c001007840081e03100c000c034420301d450b0b000401250000c401400051180030035030880030210401072881036600407030b90080381010301c406400c1c800c0e030101c202c007805646500c480c1c0d040c2c0c01547e10141c508981c40d20301000c2d92841d603102c420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497779370 1250 497778120 497778133
    0xc03060703230118060b1e03090a15060611010213060e031f1401080d0503060f0f04020d0b13090c0b1b0f0c0310020c030306120c0a03060b04050a0618020a0203040b030a0905 76
    0x1a1b200f100640f138021811044195005405080c105032660000d032076010725214441d402000100c20407001d9008900004000c200c403460000090801c1c40204028065030740184010700c12420f6080c0350b00d04941380e518003002404150400700e0700f043c3c045920300c680a08007032010704545100790010080351700d4440c7c03c0c4a041e07030b1320b144980d00e8000c1c1d1903944000850800c007044062500c0a00d0045005000f002003c4403d00726001600b01d030300403202c44041c1c07034641c200a0303040d1030008041c10b440000d00a090140c601c4540c1c5800b03001030f4a015200c1d410314007140e00c03800301440c440d07038108501c1400110b0b00c03a40c43c0e055106076110741a06000b40b2900c10b00c1c544401440c00ca0080d1060240b00034011400c640307850301041040030a21180c1800380c45285182c545a60f00d1465000096004400004c1c20741c00030304c107000684d08001e00d1403aa041c1814400c210032030140240f101050958440180c40c3c050713101d030403811841107500201d40403202100380010143c103540b106104904c50400c0750301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497780620 1250 497779370 497779379
    0x609050d05070c06080601140703121427160e010810020a09090203042d1106120612070306060f150306061202090621010806090c0306070323011806 65
    0x7420301c600c0c2c0000340003c00d103110800c09a8000c0c000b0b29041001410070702d140a166100c421441c0d00503003800e80004038402c02c4a05019043d1054125144446500c140586000b25000c4103500d01c404030044d40c0c0300d580181d1002c103038080c082007500c16000c2c100360840d142d85121880c03542d4000c1c003596406028450654980d440e5510880d00c003a119501e40c1e400c030310b01d030100480003504020000c3c0d540400b020324800c0e00d000c3c02ca01c030546e41c1080610810003280941001107191100c0c1e0703645070081c074040000190205600d90b181c0d80c080c60899001c0c3c1c0754108950154100780441e03000030076650514a0124030010380d108048141d0f01d21010320021890410411000da400e14402c42021444c0390b07031f440d04c3c0400c1c590028201c40e140504858681030f4030b9110b50b115210381994290407201c8000040c890007005002164100c0c414034000d12094060700006510780c580506a0310502d43d5441c0468042c448a42e400c811080308091504059030b074030240e00180100c11907204c0e00307461030070f2004107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497781870 1250 497780620 497780627
    0x80a0f050306010e01031a030d030204090b011d100504081009020f0105090a032310020d1d060a090c05091302010206060117040b07140d060f06030504201c0609050d 72
    0xe02c2148140e461602c0014800015001013402012100480b6124060751940e0384040181a540389800d41d00141d03920700d4250300c042181c2c41960b04e2410040005408280e21410780b0507840480030440e03900c41000300c1c080d429904d5226036480403d85003d0082e0350602d0701e680398881e0450500a0b294003803032800341001102c261050800c4d1540c85000c0442c140f010419600c8000818241100003280001d400c122081c504410310341500526070700080d030800300c444540680c08501d00071115082e40e038204000740b2512031000902c0c40c070899aa071070f40b07074003401400d003010401086c011300003080a0400142940361400d60b0362059002d44116408507581d5480b910b80c0501c201e0598150302040e4581d56151004180c028203144100826010039540c01d0042c40000c2c81454080741c0005003d9240696480c05100c0c503a0160742070500d80810000400d000082c0d507001e50403a50321045600d101c00d000580c549401c402c2065090302242401e100f089040c0e4440b4540a009100b05c41d0b400243c0d440c00c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497783120 1250 497781870 497781877
    0x602070e0105310f1425090e041704141f09030206090a030209010e09121206100908070b0702030120091c08070f0b09010c051b1009080a0f05 62
    0x141a4000a01a03c00307115040c2e118804090410b103804518410007000a5059070009240d07400101285014441154201d88103000c07501801c00711880302c0c900e10317140500018031034410b070b0500261003000101040880000c4005440308005102d46035034442c40020040c9000c000c01601408488172003892403c21608000030100042d56038418103030030f40e4280134950f0040c4903143d401400b4040d020006985100c2c0c668080e01d00488aa811071501c83e0f8050719014585140e000c48500400c0050080d59111300c3d0030307601c203205845140c40c84000c07600c222030010660b445100f140c0906400407542940900042c40898002c80082c800e1110611100d00ba15200c000d03030261a0808101c00300c05810403041c03054041c0406011074620300510303100c8201503403081c0002c03580f910045400c80104030310560300035080300490001300440070211001500303074420079420300400907403a203041d440103008000b10a03210000007820300440c0841d00e07103090180c00c5032581801080c01e0084030303070a0078810400e5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497784370 1250 497783120 497783149
    0xb09070515180111030415050904020c061605040501020c10020a050d050406030b040501050604170a0804030b10080f0a0b091e0102090301142404020d051503010506010f0203040e0603070f0602070e0105 88
    0x24525040c44d0075647d4001c6040b4000e20010304c0390a0041c08550341e81da20190580c00c0c0007a0103400140b40003150f400518204280c0f04062290901061015990000d0030100c484d40566000b10059032070031040c3d140130036144004190f84201c1005184481e0b0200150088a1843d00c082c8662a4011300b00025a0401d001d0243c00c4207044c002005050b07020b20082c0c1900c1ea5150131380340074420b00d4035004040d038080e03001a10340084100501c105801c01102000041c4a500045c0c000c0b8850007100940390a10301c90094541300c200030100c0d00402e018080c0d108035030071401623a201210060140c034040d4001c1e0b0710480c8254603220468020030f0711845041d200d055000c00c03c5044081040b80303048801118000b058001c2ea0038071010b24900082e2003058094201542c00790460303800d02e801c06080d00e02c0249914100401280076003a401d4001041c0d40954441c07020452260340c0c0e44000c0384c40c0c81d049a0141707186103003540002039a503402240010a4079403901214185a032688144091070b14030b00380 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497785620 1250 497784370 497784373
    0x1614010603170703030914070e0c030103020d060b030102090315011d010803250f15050a060b0f030a090b0c04080708010204050a0b130f15110c010c0b09070515180111 73
    0x1a0002c2468248000d2810034800d040c0080c0003943d81c2c84050341c800a84011300b640f0b40c04100709121180d0501d80c1260700c209984000ca181d98110f601041400c249004010401611485490543d580a4050724a89440941121203452485005100c850028401e0341c5c0e041c40c14040041105450009181c1a507002c18011850034002910600c8041d044102050000e0b40c20300c0702c2c0001810425100f0b0483d80140c9050045401200306903084400c00f41580506a14140040040300d00d02d40075074841120140c0c030551a5a15a200b5101501c554040145909004000c219940710105c02810684201c0c604456426440b035408500700e2146006959001e41d0000c000c201c19006000100050002c003400105e086039210401c058000309500003811902030001c84a88841d441060083c2c03464104004010300440180043c3c00760001c2e0360054084411900015809181002000010007001d03012800301c4034040445110380e000761608001c1d000301800c100c0b21641c8106441102100b0090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497786870 1250 497785620 497785643
    0xa020d03050307090305101d1501090b12251502150406290103110304020d02210a050313060e01021b0409020a120302070b070b0105100c081614010603 66
    0x21810707240c94000a00400c1040303102c66010000031001d00408412200014001c101d59181800700d520000440751070310110350014032540c3d240f4240031000e80c111149418001021003000300450032600b50130403031401500c140ea4800810000d1a0701c10071042950076003102e80305440c0c03c0c000a00c40a10b00302840143d015001d01e0010006010b1155003141c032075440020007207000145145007038000162000f034503008409640d4156054060a01c42007078030a20325266241503800960040111440640140d61628540742003a03600c4421100c030103429800c039004003040340b41c0300ea80c96001c0440d460700070210b01c03800078845001d86414a00460140c000d044641445561000440710300101603a0080d200d003000400340c1c40b09803c4001422901e03680f40c201d440039003000303880c2c40419400317000896401c0002001041a655000c4d05444084460401d016500842151020082000909612000184980107c4007149041c0082e4881e58450000b0380700d01d0822801c80d03249100c054000d20300178 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497788120 1250 497786870 497786873
    0x180e040c0b0c030307051c1404050706050f0d0209040e060411030111070506190b0d03091d10120503040302041b09080f2d0609070e09010207030c1b15090509090a020d 73
    0x61b00980700301d400c01140302d40b01003103540341001036884010b24641215a080280003d0080078443e103000b61801d41031051038100e540c03a5280141c4910102503132200d50201d00f150306641c443c1c11403118610b240c2c2c216601401c09003045030031442c074842514401c0d841c188480b0010a002000e0750300b400e4000001d030007241e0f41c116035014001d15680da840000e81d40c89000b07004a03542c981020203941c2c042d9644010b024248600b0458000920480e641e0102d800c030200001042c0e010765210036111614401c114000761803074118903600490300002e42c0941040380da280036400950706100200c903141d0755070105568401c0c4041d06c03421000300d210025004502a80410508681880c40720301c492064168210900400d440c00c1c900155144411504814420400c0c0601504a80d0f000040038008628103c050350b005010b07601d4400b80113086444400c42031121045248800e0f000b4554200d01100800b0086001031803030426011b100c1c45900d82e040415015400028828811a400f401001211005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497789370 1250 497788120 497788127
    0x391e0a1121130308040803120114030d110c04061202040f0507050f0a02070504020a02210c100b120a06050717011406071e1208060108070f0807180e040c0b0c030307 72
    0x14a4902e0030b290b02803000030005410000400c000e122081c0a143c82c0e64240300000c0720ba07101130703200548c40a01280b9603900d558004ca0706030840642c0d030420741c4901c0d0400350703850304100801040691092070b094000070307201003600c1000142407003141c0402160354030300140b0b002c5400a540c168000380c2d0600c103840b400301444005140d408928011914030594510000f0181e902800030580141c0100b40844842d8407410003a0340c0d0240514a50390822003902c51b880d9584001c030007081401c03500c41002d0007280e2680152015401054000d072618460542801400350a080c3d6000c40000c1600e84003030b507034002d201c8101c3c2c10ba8080c0040c1c0402060342c2410404135800a0800343e40d000d0303102d6032400b0020406140301014034892417095400400c440006400014014089814030100340304001071503a010800c0000701d5a503040202c101d440c0c0d00b01c2100c4022180d03091030480900c818020a140744800d0b040c6114500c00c440742d142d00f58a600d040c0c100c500401c0710110940d030040c0301044200b4007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497790620 1250 497789370 497789377
    0x30e01021305041109090a09110646110c0d0f0b07050405130e060c070807060e07081e060702011104030308042d0b391e0a1121 56
    0x140b040020b04001509000600451b07069510800a030f036144070107420845001400f41010b501203e0045c10820700000c11640200e00502d003034442850101c910203190052115041c1b0500307000c0d1030b0250101000c0c4050091480c1c40700154a501c10701c2d085030030514100f40501440355001b02e030791103040c030240e64010084102400d2002800001d000202e240d0b140c1d00c443c0411b5501e000e40c0410f07004141c0707070403904211024154462070041000205c011a10303800c01c44080c240e01100c00100e8140c5008254100f80480d001402e80f80a0000044880704641d0750403200d411a00381078034096110803070305030308130317070b00c1c2e4455002c00d030707001e10041021a00602d070f10b60f80300b8011000940203401c80712183c40720380310141c51010038824103c4504188040340e00416400391070684904040c28401d00c0c445622040c02000e100641c1c01c21002107044002d0700280d50030a4100c0404007003076220450450807a420601089002507248400407a04902c0042e181c4001d0001c0001440541c60546010315190b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497791870 1250 497790620 497790641
    0x801090b100302071716030e04090206071212021306030605030d020a08130b13061704020a1502030c070303170a051611010b10050a1101022118010903080403030e0102130504 76
    0x1c00600f00c20309000507182c01007001b6440708990308002c81443c030b00900307600d40884e9640c1c0103a1030203183e04010784520b022a03120a8101c20320008070001c84070212800481e01c001850304500214140c10204008088a025550b0b00e48050007401d8684040c10b40c2e40c046071940e0001030b8014252000451800d42c000c0407480b405420006400d51039048005180d8400310000c0000c000c1400c0c20130041c0d9004110544007050803140c0c0b80c1d60b042a4000172444855801944441048881e420f08143c1c000c008036516002841c054524042c0d4070b01f4003418040c8203085146454064000041c9141d60714410710707129031803c070403405030b20484420480d0803002c9002a1240ca6603252070f07030704130742d926007800403c0e0b800d850f82c6d010b581d20f84614008055181004513400c0c04d07030052003d0300407090030103102040e101c80c5986a41055860a00e20300d802c42c0b03241c2c2c02071495440c04040ca814582c3c400b100302e108a0094405001c000c91041d400c07400c034440c90304805528010100c0503c880e28042e0410359440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497793120 1250 497791870 497791883
    0xf120d0e0a0f082a0a0303060506071101080a090605040b040c060224060607020306091c0201020c060c0a050910020703060507080402031b03010f020a031a0405060603010b070f060f0c0801090b10030207 88
    0x40c041d5482d500741203840700d1309680950000a04000b0564507000c0d5401802c025603143e4184541a41c1d05092074418003041d5051140090019214003515031018034000c3d08100c083c8001e0400c0d040210400d9001d40707041e140301011040210b00e540c0000f813030f90b007040281039210082c0781908000807030f164030150075075a02078010009400981d408014290060400d03c001d4031603e00f606d6400041c0006100003e01964018020681e10b0280440d05580c0841a050155900c1c04c6040d400c440503c16800d03190307807200e00d40d000b82d9200d80e40083c013141928400d0b0410401ca40301c150040e60303040004c45000b0743c1644a4209052419010000c0440c081b01c060008603640709415112801d80c5c21031002c20000a98031440b8100b0501882c10244106005540400c00c600341900420344500c4140122500ea000010700481044480f0501c401c0c0590007450800101c020030f10300d80301074140c2981c01c10009407004000f141100c1c61380305041c0042001400703007518800b903440582c06900120801c1d00c45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497794370 1250 497793120 497793157
    0x112020307090e010e0610121401060b1201080c062b1d0f06010e0114120a0204090f1a0606030112050102070b0906061e0607020d050f120d0e0a0f08 65
    0xc0402900070310300e0f0a0f00a0b00042020701c0c0134440d251501c20010301400050350617003401c010340000800368140050f007103640c0c5482d03034401c0100c050160041e54042d4055200000d41d03034580300c2200a0043c180d514a100384c50142e44c040d410090140524201c404903980c02000c45803548140084c2d005c0401410803002c5203000b07500c01c5030300c2e0003403a0341600069600203031481d02a00c9020b0003e94003422112500388025410f04180b001c40441440b0b2081c025111640104c400c413804003c10740403207034010014410b00304145840c050f003801e40e6070b0840e501790f080780c1e85415202c9081101c510403800a070149065a03c0c2a0312200c500e1407421003550b0555080114101042420000a100b032140c1c2c0000d0109081c410148800400790719001c8100328100c0840d2401903440004503814150100c501028a207454104641000e450f450128824451078005207040381d00d01c800381802d00c0d1988801c01902c03041d001010740304e1002000007400c2541d911003a0f400500c4c040c000e059503040000e0405003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497795620 1250 497794370 497794379
    0x504051f090606081b010215040f0c12030e0909010c0c03052104080a0e121f0204150e0a051008040204092d1506050904170c12040806100e0112020307 66
    0x2103c005401c0a40c0076000541103220a89100c1d01c9280349500c00c0c4000d0134900e042540c1400c00c490301810003420fa071001850001409207004201d00903104451210f08143d51b2807034003405170944d2a2a007805201c400c800906101c074184101001c81e1510b85034a940001035990841d400d41c01038000952400104050001d4801d4100055200e244034281c502d58520f04502d004c0c0000c20003032201d034403400f402000590858800f09005214002c2c9020501c07085030010b110f00040d0050381c200c50351b0035010b0080c000807250304c0800850214401d551100703e20741c4801c14040022581380490020840382c1c400300e001400d0591180000e82d0164092440c1c55208035045450b04034592840c40403500e02c485400d09001480d912408008141e0008004462401011075289140284068086410740001118100d4054102c0d51000000420b851150304540450241900f01e4041c64003148500e0f40001e19000c03600c40071006072020550300c14150ba28000d1005040c2c8607950049806000c2c0010008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497796870 1250 497795620 497795633
    0xd080f2e090509010614060d0c030b040c020c0f03010e1e07050a0b1b03040509041209031b0603150b03010b0703031418060610050306010f2706080a0504051f09 70
    0x28090101c10788046410f00b040b14840e801e440154104072012003900c00c3c1c0a1480e03403120304448031a003d603c0b0105841501d0907040d8004e040c05c460264003d400d104400c0032036a408500c1000c800700803952001e800040406040c200d4224005074040c0e54003001d0340a1411801e0405040e9040038001160b01072500d5002040c030042e002d07030007000c44c06c80c0443c0c400d10704003421841d0700041d440c00c0002d40c1800d180c03034009103d600700640090a04410300c40c0c0381d408039220700440e0001d550031034081519000c8240203102545100c0c800d8000292a14481e030440003004c0d03140b1070444164000c600c1c15a42017011a10055000440440c01d1603078445c2d501c04d0090007007030018842d103404502c0d0448401c402200604204009142c02c5c440c0c03d140e541700c2c803842d40060503250440820f02c2c0116101010000070380d000251440c001451145010f13140040c03844444501055031810360302d090850722910341030000d038bc1d01a600102603802628015811100c10386090841c50000c100c081062075260325080d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497798120 1250 497796870 497796961
    0x702031c081b0403021207050108090307030813151a120303010302030607260718091407050f2a0c010915030207080d05250c08180d150204080d080f 65
    0x10115401042d1f0420583d0780218a032503004805c20b018500d4540d9690b0000c1400030000c00c0000240d48041c07030b100c203004180c100314040c055034107020482401011190b00c1d801000854540c80343d40d03114903140390080003100360390481c0d034050020010360300c440d44240c1d601403020401c8900422542288904002c4a00d102c0780503800c1516080c0103150012032210b280d8045420101085041c04000f00d10904110031036603024000780f4001d42c0ba1041ca60031070306103218110250001c1c0c41040070205404404920b5110f02c400c1d01400c5428024250005551411043c81501188040d041c41d0b8001a07000303400403e40030b03200700360b15490000d00580071821100c0684800144004030300700321103190300c4140070f41e144840d01d04200b4030448070350796012410310401e041e0340b139100242c4096408644032014000d8074075a001004a000782028010040250003070300c11050b1704c0c810002c20503080d80c0140c10050080090112942107566039020b0310900025129180c24407281c03500015051410b11f4151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497799370 1250 497798120 497798149
    0xc1204030810050405044809061a0301090b0414150103050f1b09060405100c06050a06120605040c0f0f0911040609061407020a09020702031c081b040302 67
    0x603049681045030300b40403180c0700c0b074000902641c5400e0900c004150002e8180e950107480b030003030008805680c0d840744e8202803959031460322006505907803000701010500100940b0214001000031070342e510030441d8a0741003c00e001c4407010080006002c80c04e00364005031200c0d0409400410180705000345051103001c00c4a0030380000b6209444241c556034140200c6410881c00503840d80b40d03082002d80000c0e202c480c038004020205000502c0c00081e101c09041c2c40092030004c044070090f1040c041c004c0d02c1c4da1912102114001c1c504000506040711b58810502640c1d003000c16199403440c03030782d0f0b048010500548240d071030202c1c64400041180440703103841e0103002524a15a9014a4065140140c0d01890900c9009120500040c8080c81d401152441280c1c44c1307150400074a1a4000094118803490781c0c042e4024040300b9022800c840650002c0600c0e51003074084400d04103a5141c0c44801d400c48500c40c0f0300040000011a212226042810f0f80022210070b03000d01c1c05949900042108507500d14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497800620 1250 497799370 497799377
    0xf05011d0619120e1e0115091b020304030309301101030e060603030a05031905090309010f030921020f01020c0a0b090a0f080a030207140609010609090203150c120403 73
    0x4041d0a40d406418964240d00c1c030704041c803980780c64070130850300e54502d0904501410207424254090500942145c0e0400300b21094601080351140628000703820101c8420b110420445443e44e8014800002c640803240c0555420496606204060388890070506201c0c00400c0800c5440450000184074407152521840c40c144400074104005029074003420000c101e03d81000003040400d44000c81107078082350303285c070300190340ea0345020b660f82160107411400c0c1d03001031a1100b00020b504d030000043c1381010007625012403070070541c80120107460107514020718029586265542c28619190f10304406c0e0f440f401601d1441e0a0045003d00726000004104001d42c8812819010300c8920300b2901e0b04071460202400182209885501444403408030041441c08002594000f45100364140d80750385a00424601e280c00c40da002165503100c003910120401d518010002544242900c41e4104103030340035018003070180071507030715100e5108001c0000300a07400c104002c21620700060740607440346110b0745 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497801870 1250 497800620 497800657
    0x5030f0a0203130501050a33050904030201091217010906120609030e18040b0907080a0807020406030c080303150a060e24221e1203110f100b06040f05011d06 69
    0x740d100d503c1c2c620401c0c40c1140320290134038000948e00030b0281703030054540903954024607403a1858224014040c080c0060027103c003180030b034004594056071152286003400f039214203e90f00d03412070100711007031849680c8801d03a441c0c0c803107000915181c108030380d814080e090440c42040c00402050207980c50400c031142c02c6400c41c00308410442c0c80e40e06640c0104c01a801028150304003400159a44481c81002e0042200480c7d603408560350794001e40c0107107074018001141c00390385900650b40e980050300c040210a01c242d441000c13a00b0302040c1381c4111016039940d0281300d04a03806116040c20709640c6034400c084520172011208140760001c0021101802c040030000c1105410004014500d4100c0c4c1400012051313800450800b840c0380364266222100f602c0c248000c81e01d802d49001d84900e0a50f07016000b8005960395480000c250708260a1140c2c4042c8113055200013013182d284070364092414659510641401076520952003044003200e1504c0c21100e6484910000e175140c0c002441c3c2480030341461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497803120 1250 497801870 497801891
    0x91e030b101e030b0601110705030109030e030606010c1203020d15120302061b180f0d0b070201060506090907050c03160b060109120f1101120203040606060207050105030f0a0203130501050a 83
    0xa180329030030b015401d10702d503242c0c00c0d540c90008800c0050195810418142c8050340d10035007d0180c03e0003004020005c1024045c03030301d0060550b00d0307207244940c8a4085c5200181d484e5000e2400031450541c011036411032071900c13090540003900302c0074080289136a0b4050106580d20740d202c0540140444119509450400d80b400a01c1c0c400c00500303800c500ea441c9803110140c000c0c1d035001e0b22413102e684080030801b2a03608002ca03280b61100741d03120343d1001c02d101d00d0300c00b40001d0022042c0501411b03070092051544980501c060344c0b0075001d1503a08168408002800c0c0c900c03841c090202e0702c81c001c0c19249071000103818220032903420317030064400f0700c4040140401507030416002c4004041c01d101002900d0303030546415200400d903600280080100200c040106ea200d01c1c84804d80070744281045451b41014140000213062500a0b0000351288104c04211507010b0303010340c0d03c02c0099280a05183d0344001e884d20203908080e1900d100a02c190340e901c00001d00a0007281d03c2003826030310004650400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497804370 1250 497803120 497803139
    0x316030b0717010605070f0209101e080606130608030304150513031b0201141c06120203061303020309040c020d092102010810030203010203010e01090b0a06091e030b10 74
    0x98441d20510103074141d4030300e4009072104080c0c111001810410307183e441030b080801c1c421400c400000e6214244000b04003d499071104c110040e039065203010003220104900000801c1c45030300421829502000010f2194544200c40078a0003600d04004246296140e085602d5904165421940c02d59481c80c4841044018818a5444008200003000300002ca403000751603072108105800005955441074010341e40100034141118503825840d40c0e0381c441c0010085101c11003000002c15940c1080310001d0080300c040801070049400030040c04040d200e0b41c1140c1001c0d1180f000c110194013040c400030000356a14410312204001c01e802a00302c111030040014820001900464114152507a600701d1400d00c001c2c1c5410310603420b003808001034030713502d00c0700092031201d9000035031660000001260320744c00340007628126003580009214900f000e20801c00040c500c0d00a4400007403032903100b0010560081c00b5100ea10310b060001c940116100e4641d0411214125103100d2400d0300800100156460f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497805620 1250 497804370 497804393
    0xe01111207020705100f1103031003051b0a150915081806010b0d020a0c12030c080708040b0402090604240524040501030c12020409060501120c0801050618031603 71
    0x854030181810b10700f40300c00612004032030385d848410050198480e0028501a9040559140c0508204c9440740b4101000d940a08054002101c1c1c0c1d00400700031410511401d00420380c030201c000c207031003001d42c1050300c90342c104100450803030308004449500280000c0100c00300b00c0d5102f078a644d140980e25240b20700b070701602100d00207085107134462801000446a44415a84206000d40015075548040d40007110005211b0300c015100340f81c0303e5010b104031609680010581e00d00d0380c490354450303610f59000303843c1190704840182c010364801b00010014a009a056588800c00800006204c0302418a020020100b4409400d808c012071a05105510340645458044224807110b001c1c0160503c031000352500841c81924149034443d5030580e0f405018000b000c0700c01c012540110344560b91190850080c10b003078819a4081210003061052501c1c1900601c802850f01d9202c1c84a103134602014042c01d584030304204030444003805001016650140044070802c1048000c40c1100c0381142450030340c041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497806870 1250 497805620 497805631
    0x230f0304120e010804081803030301082d0d0f1709070602010e0a020604090c020a120e0f010509010518060405030723030102030906011404090606150e010203040b1602040e011112 78
    0x8006018519a84c40000c1c594400c1d8800d02513900e1f4030ba52800840e04180d001c41c3c1d640e1502010002040c07420000600040d5411500d0f444192000004001c400200000c98044d00756008055040d01c40360240b0f04801d41c0010500d843d01d00c0800d2460304024142056031400803d0300038541c2000255424040c05424840e00700281072046c001da40000d240c2d100b18407a01410a41b10344d4178200c51402032020000302c80e0070503100200c0315912600244070b48042d03000700d80b2a01c1d20402c80141035201d08191804050107844252420000100c110410401451526031021042001080783c0d24244540c030000c28500072240c1c240510900b078100d800d0310000000d40241e10610802031200f6000450074115000d03d2a80d00c0541040710110700a086281c030040c0c0814241400098407601c0200000c14043c016512094001006001261280b045109110845005015482400c21b40d105140d090904c002c0c8009800250f80b12518252035085400500741c01c004200403c542d0314940b8480d44c8074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497808120 1250 497806870 497806877
    0x70513120c050301181509060c0207031205090105070311010609320907031214070b07120507020705040f060801050a0204030213110d02160209090708100203060907230f030412 77
    0x4811007a0348a001030881103000e040041b00348440c5800701c169070710400103641c200c6028000850100b0010303540705000d10040300c041000c0110340c81070350702c210190740b61800161f40340c0303141440301d03281100e0181c81c2d641e61804030b5503510000149000036128900625844501d1610550001c0840e01c2d1822070401c417404680c0c9041d003c000b041503012808405880c2c0c41440c910034070015000840b0202042ca011103158980043d4103014050703031100d082d22500113551080c103e00d00075510401520f6003510034601503808210144100d281c15004100c203440d5186001030156550020182036500580758000020760014050084d8148040b85800c4607110900601004604950f00c4001c0d1103170f11105e000503580402c1d59424800d1b1040e0b40512541c000301507284e1414900511034407040b8511502e0441e00c11101b1104040666000b40d03807180e1070042c8602140c1e034403c0003c0d40c0070a15038007a61115218210900a80300d4014041c102e4151041241900e9290a10707104034490102c51009050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497809370 1250 497808120 497808131
    0xb0d060509010b0a290d020d09020a050f100f020c0406032a0b0906090a05060c010506040b101e05071406010501020118080d09020a050406030303150f0501020304030b070513120c050301 81
    0x810303000b14240000c1c0185d0060150180d14040c2c0d8001c07140100301d0100f4181d400058400480030031604070b03a0f4407500031290340c0725150f42c1c2c0c8104036500070b42c003001c3c2d60004030b00d200f003900043c041d025010100343d8034015142c03c8505040050200da0301c68104440201c002c1c06156404102c03659414015030320188662461420400358040a02580d0b0005129400c0000e1284540e00c605000c200105005043e0548861140034024042e22045500c540118039245843c1541c0c94004404251004507454948030000c481c00f000c458511106010f4051080810041340002e003042c44100c154054035000e80455410800028291503021540c0f0f5010070500d0421000714001e10700301c0d25048800400064800324034400305c1da2980c15640411742c407915022001081c15010b4010303e0724401300d030030385001180e2141c0c0c003400100742a0040f0340c0160b0040c0720500000b0911045940c1052403410304500301200042620410f09141e00b000d80b014508000210401c20751400c00b1000d4101200203200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497810620 1250 497809370 497809379
    0x2506021e0d0c051c020a0219060c27060e040b090f090601050405040b0a050403170c220e070c11091e070806010203160809030a1b06080402060d0f0b0d060509010b0a 72
    0x61040301301c4200002c0e1070340021500794150003040034503688030b0380c900f00500509040c02c01100130002e1618500108185010600d0b0340343c04850350000b2042031000c8000002d05060044401d920060803a64000340d542c4141c610941d603140600c0d00c940c5442d0500c00e62441d181143e2170032301806902541c0078504100502001030400b12495520040d49a4002040c0c0d44504088030440300350300440414030480002d00010340143e000400c10801c80181410103009050900304140c4e040d4444c040c1c82c204010b0100703110303031f100702c1c04010802d010f54802a0a1b090710710008088010940742c0c0d00e80501101c89821260101c61300d4907034030841034103280c4028074118001035100d20030040310100c4610040680360404c10080c0507141c103220043c00311920500540b80000c0281c2c4400d00f4526020180320300000c54a2103072426511aa601a00040c1005034031000ca030f0180481142d01070340c0c01d1b100e411070006511100310031070780c05000b00b4010500d410b22450300c5013100c5e504004035000d64400030f000e00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497811870 1250 497810620 497810647
    0x40504050105042630040503040609062309060c070f09050f15010e0a030501021206152104020d060c0e0a050a05090417090a1202152506021e0d0c05 65
    0x41c0b1724040d14607a1200304104522803042051900c0c0034642e010000420700c01481000800750080d00c2040c0c88014956440300002d480805a600700f41c0e15050b803840c880e255807403039107020740842c00004d0100d905110b0740442560808401c0d8214010030100410208403c00c0d80e4003805412140c00000c0e0032550800d0f0081003103103405142654103011070046075a2107602c0700a40c078001150050700031511004205200d03090003400b03450140c0715050f540448034404004508545490613001c4010600d203001205e401d14031080188180c1c0c0c00801d021102000c41c0c200d0191154803883c5584400d03005d40c5071420001c0300700380e5401031409600c582800b40a01e480350007900d90066041901c040d42010380c03034090b00581c4548030b00e40750400b4039407600052031240744001149045c402c8403003000340d0703801c810400c00c0c83c0102585044440c42d5008550107868002c40d8001c0f406015500151500c1054400801102480c400e02d41e9801d0000502040100d0039100380c3d0400300003442c01c1440c1103400303074640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497813120 1250 497811870 497811877
    0x30f1b0f030c150a1a0d0516030f050f0105220302010609090b0a050f1303120209120a031706090a0b0103090507060c05010b090411060318120c010c0206280b0405040501050426 77
    0x180654900c1d00d005090000821610030b07110700003019066122740b2440c22020300c61500c1001ca40340e20a40ca0059540c1606000b280c0c03289500050344594158001240f4042d202d54038402e03010740d540c5034400700e00c42c9104e01800460034010f403ca6410b82c149040785008940c401484503194001000603c500003a00111090a981d0540307006401e0f545c002d01d4882c002d00c14044869440100351003640032003000802c207403004a000342c80d04441c03000c64400360030301c2c500216415580250b1100000381d071010540d000e401d031400185400101d1500c41c0e0340305482c04143c0d400420100d0001c1c5124001c0000c2400b40701582d0209a6500e10b050509a6506e610303148400b41c010301c1264080001030702542036001401030402248215410ac2500300301001c0e89a11114040c4941e50a00101005040c00050000e0242d0001e030015611102c030355494a20b9030340f022242110907910b55956162340d6885e4080c4038016401440001603d003083c4c5098403081140c840714489100c0210602c204a1907000140c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497814370 1250 497813120 497813171
    0x60f0909061407020c01080c160f0302010f1104051201020711012102040603392f070f0e0c090603100302060c011b02030f1b0f030c150a 60
    0x200da8040503107001e001620111100400c0c1d41d0040c000c01141c15800503c40420362020b88034901c10352991106188107105405000c050010041010400681600d40c10312441d4040d00c00061810351480494040d20740100780d50302d8420300450140000e1401c41c644074070014801000b1481d111855035228581c6a62200d5181400261901d8500b01d1120104001e0004124241150f680d600d80f40060000c204d03604918444581006e001492000e1003203891966400740321140e0405e1200400c201c501c1b014002c0680008040c2d0794120401c1d030603000f030804800c00c001019008203410300100c8545151a68805100ca04504042c8001c440e1800101c1d05020416514242d41c2c0d56507184202c80e0401e25800250041d0b0000345c00885144103510502c155682c016042c0031803d002c40b00ac076581d001c0c00701d06071910002080012134524600e19191801e5910b94207a50f00622055241c07402c5400c1056403008c107810042c19040c6804045c00c03c1d540c4500b1300241080141c4038988500e481c034100511 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497815620 1250 497814370 497814389
    0x114040621081c05070914311d0d03140414150a1a0901080d03020c010e0328052106130e0309012613080702060304080307020c010201060f 61
    0x420107020b1503004a42e418040d50441403a075100211044004100840314a4001200c03540003003202d180d10301c0d500b04802401030041030000c0b8110a44807504402c16464520403240100000c0c0702c0c1c1c59170090b1444203014940c00103d6802c1108924180010701001000309882c251515981036269285190020f401100800c000f8009070b00c2d031481d10001094441d00415920f081002240035500f08180721544400342c41d81d550081780c14440346050a01448446402c081968180544241d010701319840d4180300105800c03907071200007811640301e00c9010320120041c00b2005007030034078400140704074562860103d20341000b00c03080d61040307240000c1c410011210240841c030310740d0360b03501488141500782e40c08118015444900715582d512104895002c40da68002c5c1c0c003500041c0e180510400280b070a43c03d0360381e80c0c810042112000707034008111a910000c3c82804003603143c2c3d101a5100300e12510106a80c0e0a01200c0030389030180c507600d041d04681c1006c0007400003c4a070114030342206c11000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497816870 1250 497815620 497815679
    0x71a030417030a0e0c0123091f031d120d020a031517010b01390b04030c020414061f0207050612161b0308060105120f01140406 56
    0xe00564050981c103040340514a012081c0315641c0410350090400351a09001c071860241140010f50fa00100212120001e019081c0d4110349091001c0080940b110001c184e48074048480d000c142800c0d484490540010342c2e610908440c90060080000ca40740788080240071100316070010601a1052440d29010f982d004aa80c0d6407035406500000500401c0800c5c2d401c0413520340241340b0701c1100e40718540ca07180d800c0c00c08a203010350150040204a040c4542694003510183c039510f000b01c05901108050310340f104032248041064070345214002ca2080c0d0791701400c1d1006004201c140e860317541c00201000c0400b418811151f0725660500c00180f640d080c0703a031400b140c11b0026407c0c248039512003600408d0000b032503440210015400c0e4442c80d07031030f2544d00405074044000c0310f4401c5021440b15003d041d081e4044046030196103056230240c01458a603251004401c0046002c80c0103980703150312040c1600061100c8014070700c54803a8601c05640030400c01e4034044c2d14280148074540409041c05081 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497818120 1250 497816870 497816873
    0x61f0906081509070f183c0b010503011e08120c1b0f01110118150f060b04180605060c060906070e0303040314070b0c060108190f03050a1701140909071a0304 69
    0x1501f20418100d62031100c40800c80840301101080d400c9000040d0820032140790010711000640f040b1240b0719010303560517085030700301805030501640d410840c54100028110005001004018070910240103000c211303284d111a02c80c0c41d2809841d0f100c1c0e40c00e01c94490030110159140c0c202c491190a00904e0035903c0040701c0e03503004c0d004101c00c62010070b0700042c0c80541018040e10250b04105010f030500204070803010900458110b4190f801110b20310b40c002c00080269100c2c040c003080200e2000038000403083da85000080155104984a00341508134100700310405109011280d880f95181c149600640c5a02c000680ca038492400010100a0f1860b8600c2d05034a0821501300507002100c001c6039158a0800e0340c1d41d03685d0007442858220311803007a001400310407400e0b00400f45507002e02d440240b00c40740d99050311207400411000b420401e25a03c0d09540720f45540c2c0d454003c195140140c00310345540010b10241202c0200345003100c2e48030020400c80003000e6004060701e1020f02820649a0700c59 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497819370 1250 497818120 497818169
    0x6020615090402130c050c1005040203072c010f08010b0f010917190515150d03030f0b03010906201314120313061b05061f0906081509070f 61
    0xc81301102c031058074255407828500e0700880103040540c1d00310b0454450392800b070050800c0d100d00f107030000e415030400030f0b0400100072001c454584034584000800007117500c0500c11406104240c0c040100540120000c0000b00c4084c0300e40c410b250400da1700c0c0b803c40c100c04000030300304208038810321520584142d40c920340b0000600101c000394036186082040f00c02d280c14515610140c0c1031000f058404c03480080f03000c0500b40b8101001503c005070500e40d8950003918180d0050800d81c0380220000d40342c1410001654007885a0442d0702e00c10000040c40c08001e40d0510700c01e01240c074140d01c0004042004011031030f03c5003031002c01c0f80c072125000d03103401040c503003c245401e510803885019031001294450700341c2d000031805401d5910310340d10b850720b0b5690b0104000712111000b001034520780240002c6010440134001440e0360181c926581c0d04c515943d428118220b9134954881c07445030700842856041c1c00000d00c0c0340d41e044100c0000400860b070030b0058104424910748240c000c400513586910214001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 497820620 1250 497819370 497819389
    0x90307030b0415050f19020901030e06090a140f150a02070f080703020c0411090f01020705100504050f0d05062e0312030b0405072307061e0606020615090402 69
    0x180322001c41d9003810700d454619085107080c11111051030400d00040d01091010001d903104054464400c0c0311015002d141800940c001100f1504251b1a40310400840004021190040a40300001d206101c250700f4541912104410520b60035001030000300100c40d0b00184440090031400b0000301c46846405200c0c00910402c1c400270901180544210705020112001d02400c90203502034880e24055002000121404000c0c0c04d03000d09024002038145040030f0700548041201801280d48139a00c440000f1001614640481c0004200050500c05818560031008a106094a001058035016078441d42ca500c8000d005402d115524907006039061a2110070302405036265900d01c6402d80c07282490b040110340c03131b500a00442d0030041c4460150415101c0d8503c9070700aa550341c0a8400300100740d20340b007040c40845400c00c0030280800000b25556110316601d4014030510100803200003404902a11007030390140c010b6400c071104000d0040c0394000000c498142c00c5a0550480c2e5031880050120fa4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 497821870 1250 497820620 497820623
    0x10608100b1c0c020d02010b01090518040213051006030e0a03051b120f07110a15050706020702030f060414010507020613210206100801090c05010e0307171606050c0a030509030703 79
    0x80c100f1586911054004c14141005038a0364001c0c88581031490056503908014452250440c01554a01605020b140a02500107100a200541c0340c0005071a2500365501507440b0380911744042c0d01042100d40520469000e01d84110151088070b00c2910040c1103801410703810048420011340c403160008045c48018000d0300e5003144a504e0f1fa6940402d25100e8201520031030301c80068130703264419483c2c804c0403182114141007040e50f2004c0038510861f882d82100c1021503045809000450060364240485200c80b41a000284106d1074181821085226641c82d064000d0b4504030602c2080c0b917001c81d046034082c0c0503181c00306010354103141ca044600d018140d00410041c4061603081004d80c0400c81768000c000603101d00409030381342c002c054200c810f0250028503252402104108a50040701c00d24035040c801070658000e5541c070038800b180d40b90a481041c0b981c3e0400440013903000404042c2d200685842d1404905280264081a91b1012034450150910101169000c595682005480301a6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 497823120 1250 497821870 497821927
    0x3190218090a0f0b01090e1f0b031612050607180311060d0e010605040c0509010c06180c03050d121b080c1b100f020304020d060f060e040812010608100b 67
    0x95041d4101138510890a00610f9201c40c1040a14003c0c0302000661107000140c200d540000d5030034008107000184a10001a0b0b007600034051040384003c1d020380794800802c141d0b59282070350303c1a80b5041e410080002d00c0e10091148490082e03a4002449001a0540342c0c4101c0f00740d21442c244002418030701627034010030f03c0700d4280707120451145d0048d004002101c400351000d11003401d583e0401e440c107000304804940064240c040340d1010801e150450b40f070313190040c0da00c2e546c07400c910303207071140d60406540050300d01d80d1048629141c07ea0303004c41c00301e13801c0d6407298080180c4c03000c1e50b0803510300700030312001c900c00c0214600209030a442030404840c9010502981009800344003099992940702e050340c4a4001b92a024207548100d07000d00031648116030003007070122944540c1d80c5160080101644a401903a90360101041c9417030248521409a400386003400e455104c00c00e650164203c058100d1410022004144141d0102101d4218166a41c44c0e03040d41c1c46000d80d47e20b100840301e024802c0f4019 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 497824370 1250 497823120 497823143
    0x30b04150b1003090b0c092202070204060b0a140f161703130209010b0c0303060d03090f14120f0717010e1b0a080d020a02060d1b050903190218090a 65
    0x625015400413100500c01ca103618000d582c0e1489003551400f4580f060364000301d0403c00b000310940f0542c3e15003d440d91007040103082c560b43d900403404441983d00010086140015480c8a844d080100e203071800e20100300701c610700402e0000e441000c0c0501c03c400074146145450540400c10702c04d55500308002d0368201e00352a490003100c8007022481e00e0200b80e010341d401a0010508411030400c846a43c15400e00540c619295a001c2c400380c1010301400b9000c0000400300403541c100c501030728800626010107810b0092140d2010460401003c20a1324025030101c0904211000c01007040e208990001c14036400c4d41e8074100626000d000b42004120250150b01a825000c802088c00791162820030b441c5044656242c0c802e15603288a01c040540c056070005244100520b03188000f0a01148101c0021410300510703001c24a02d95205e6912101140010880812909041220b00c003e0022030074400171030398403500030415030313040618040f482e0b544040000320066400c0110170361840e80809500c2c203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 497825620 1250 497824370 497824399
    0x103080a0305270d09120503042d090510060309050c040c0311030903071e05060c031e15040c0f05030c030c1c09120e010203220f0602010e010e07030b04150b 69
    0x445000d200ca0040208805d043c02040300d40a01104100007075101006518040c2170656400c0700798010303054a1020328404030203604180c10010010b00800d0030072008165810303e040c0464120509421090401d444e28101401080c40000d4200c1403201c1620300194142480304102d001d0281e1030440c41106900200f44024244000000c0035214000c44c41a00c0b1000c604045011080c81c108028241d40c0c00720703001c10540380c00c05c0b00554000b0310081840d800701e00c1c140e42e0304805e4902200c100c0782480c08a803002c891400c080c01100030400052070071744907020003081c0141542c04094001500306002100040000c400301c42190a40b800e01d100741902c0d02044461b540260100c103408860070342c0c01c055041e40703581c060728002c01a540160055810403140304800c500003044140790301c94001426500240e06500e42c882080500100e60002c0f4a41e407000d1038540c2900c0c04190044103e500c286420000700710061203443c0c00591214010702c0b03140c4220610005880101c40039503224594585000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 497826870 1250 497825620 497825623
    0x4080304030506010909170906070c0905060102070b0a090b03040206120408030415060e0c090a030b0106123902010e030307030203040b06010c0809061b0703290103080a030527 77
    0xc00c803485a400c03103026a8031541e40e1010b494070200000c00c051100c503e02011410a0000341041c04e03005040e19003082c01c0350f16000f40204c40e9a01901c040341e5140309001007564103104c0e4001400407110302e549840580f50f0700612043e401d208804400e40048046421583c6402c100e543e4101e8105551959003000d090404036a88180d0701102c403244242d1140200100b24050344003215055440d0543e981d90362100040c00d0780c017118005600c01900500440004d003843c20aa019150b03c2d52880b08280780866541e04442005040c040d070032101310346e502d0800703000e00c90402a107602907801e000440c0b40700000ba8050301d42e010101d625408003000300040360342d0503030141d4850b6018210107030540d102c0c0001943e00c40044800600342c54020404604107080001c0145504500102e0409a403400d041c0654100301072500b0031030351040c9184000c0000c881a14144469a101410190040d4034555032240d01c0e105101c2d101080c10f0b200c00c006002c40d9201c2058030899120090142d010701d9410801c00d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 497828120 1250 497826870 497826877
    0x501060206071806050306040b0409021008011503050f011505040306020429091516020a09230f06010c11091f09060f170304080d02012c0604032102040803 68
    0xb1000508984076008088101c240c83c0303000c0b034a068807501d1031501e4240074803018214104546400c15119018000180c0314064940700e18519903a9121955041c034106d080518880308071130b02010f041409000b6140c4a5480e100d0440715100403075480641c8045040d41c00f0701869102600c03862000c9000242a10000e007200b0074800101020701e04980c3c001c840068500800c0300d4a038120995030140400003078070500400800c5040c2c0c4104025040ca0b0f4005085000c3c550000b90100c5d0702c4e107a00340c0c0d44802b58900d554050600c4000d003a03c92070181c03100f08401e03200a08090400c00c100701c82405000389113039014490003000d015131890b450080b03c88500c008803030f04000724180a010700003421441d6071040000380e510350b15141c0110761401201c0d0f025003482603101a030380e0004210000324074808108050301040d080d000403400400074041c4440c81d00045002d4100308170a070080001241011079296445035050401242c0189010103491918807070b07000102030385100041c04148030a002000c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 497829370 1250 497828120 497828131
    0x8071404090f1b09050a0b040e070c0c1a0909010f0608070e0d0b010806040201020706032009120105070c17030c1b01090b01081b0607030c0231061d0c03070c020102100501060206 78
    0x200301405617602c2c5016401c8c0304521960400d8184100811400340c401c0d11000019401a00e00c0f89450703031644611403400c14101c84400201000160100d140d060001c911401491589049012036140c0f0202505c020301c010a40410413203088950801d503900e244490120b02c1e04139560140725038503068500d84d528801c1d10f0a901501c202d076030004002d031281c0102c0304074115603002c0e40d2500650714001121500003201c6550b20005400d20080c0e110800d1103038511410140e034852040764001e00308005116984d44010621510800800000345241c03400c40d403210a446120604441e07a94041c2c0d801400030381001051035001c9000000d8401c0c00081c1101a48186035000b24164407480c1000000d1082039001000315040400703500140c98410b03000000500a5400800810300c40000e507101000c401410030b6a4941d560b0b0240010003441d004180c4070b500b070420654842c10326076801087c1c0d000042641c1d0400154034424401c5920074400b0007a4000107410a00065849840c06525040704540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 497830620 1250 497829370 497829379
    0x100b040f08010e070302031f090503030906040c09020405010801060809030c0a05030c10060f050105070812040602190f141e070c05030c1525050f010c08071404090f1b0905 75
    0x40c4000300f8001141810440364020010140740c030600100349a0b504000000c4441680e0350840c8601160003070001398442c18880300a0034182c5081d00d004401910356410400880d4030501042c0040e0760040f200d00e043da42542010390940d90340e24002c5141d8403030144c04542038043e00c0200010050000082c010100c0014150b070030403101032441900b194040e101c0c0d04040e107410319041181d54081d50041c003406005200c01417820101c1203a8030b8000380d00b51022585030b9400180b104002c4408542083c0c103140c0b9260540c6002c600687c01000c1040003004000a040c001a40d01007042c0c2c0320703115510b0522001111a05c41c1c516061891204000f4400c842c041c3c01407007252061032900c0d0303409194060303250b0034041c100701382c2e04422600c0f910352509060305c01c0715000b00b80021500030400140c05509076400425004880d10f002085280c01030701010901074244100c0007200504026a420744018071000124241c2c1145c044025000100c0d909000844035281d07103c03c1d43d8009001d0042d55429203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 497831870 1250 497830620 497830631
    0x60c030f0c0507060b061b0607090b040b180a12110a171009030212220b0a0c0605060604030f120201060518042406150815010e0603100b040f0801 64
    0x448040a8072168428400003800c104020800501c10f60300c00d64000c81c0285c80a8140075055a0042e1038074540d0002a43d640c1c0900d0420000540c4030070b0010240100308030f02424580743c0806410140100c058502070341c151030380b502c10180c0303581181d100141038100c10b4505c1d1040504000300c210004415040c041c0300700c05400310708242842c98840d0b60100440083c054501c5200b428070042190480480031809a00d040e500044050005043d28003442d5040341810038aa6081d107403140c80c03990002c0e14080050002c005120342201001900d61b80240b0301080302c0c1e40701e03c0000c41600c40d94100402c1c030f20303a800c2e440f001d0040420110601418a4000b00400da1b110000c001d101004402190300414156000800040d090f20070281c80104078804c1d1740c12035480e0b10360b14065a544ae000040c0c40203c8a03c0c0c8402941d2246139190031065040402181031101000200012040e9842c61700402c0004085152001419000402040540855a160f541301c1c22003041c40402481007980c29801c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 497833120 1250 497831870 497831891
    0xa200c01140c0705100b181504021206031006030809010c1406010f05031207020d080d0e06071e05090a030611040f0605030103110915041806090c0f08060118150b07060c03 75
    0x52184101b0302000805091400c2c011056014080400610480b580c280c0c110045045444034000303024000714452501c02c151030101d00b0715240a01101c600001c0900b000c4d410000708102c0e01c115a00388401b8640361910301d10030709019075081c1380c0c2400c661a902c41e0303400001c0e500f030307002c0350050a544088085d10300741621629070000d18050310340c0103940b00d00c010f030070b800006801d04000d0101c4a501180868086001d000710380c14035000300c030f001c0c01166201071880d5402010600400c11540e05007440c0e03082c00024004519001424040100f83c555071b00c040703041c903e0f800c0054070000e008051500da500c544442008140750000c0c4400c450010f07003680c04101c07500d024441c0c2c5101d171800380d007085d5100541404200c054041c0f29000000341c0440d40548000c00c059020f001e012a0013909030142c5103241c00c1301005800d41030380c80540c40360031420060240500007250b054050003410004200d640350003400321800c01c47ca03400f0740c0c2d0000000907060100b0429400080340b043c0b60f602e0801000125 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 497834370 1250 497833120 497833153
    0x61503061605160c0e150307080706080f040303140a090309090207030c0308060a0f08010e070519062616030b0f1333030b0a200c01140c0705 62
    0x3000791100105005110600d66160f101d03450070a03180c01030b412a000150303103148a041c440000c0e520301c2c0100012100c0f018050404000c601c00510300c0c000144000c0c3d1034820020400600030b800c59800280f00170109050504c2500958001140c81d05109020300f0240d20b01c800612440c80200d02040d52a0000500360380c95100b91808035815440c1c24400c820380c0d0368115041800102516840240104042050310b08a4158009000101e00000c2d40d5505031240518000e80b0342e02c114450b030303000307620f86206c410400f1462084400c130b810b01c2d000c1d1040300d482a066403c40c2c84110700c02042064200103018000000360301149515031400c000707055402080c09104004004140c1d0400e1505d950355002e14403580c05207800908482c0303119008107480c00d40351008040c0d50745c00c080c0318084000900c24452901c83e007540042d0302040801c103c0d100080c00004103102004000202d06001c91407804208080d048503200052454900c0441d1402408140b04d58000c3c3d002620188603015030060389143c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 497835620 1250 497834370 497834401
    0xc1a18040504080d0903030f060b0d06140f060a020c031002030f0612030301061803050f0604020a330e030703120906030509121315020105061f0815060c06150306 71
    0x100802418030341181c412131800540b084220440406564200d0740174034200303603c42e000c0034080160300c56035240d201c04000015540150050103003030712201110030080ea2092000e00182c4003d44009032a4034480000f40d0420301100c0c0c125816005510701d0b07442c05c00700c65009520950001280c3c1d03200d40c07503d2085c0721203200c010401c2501680100010b0003410b0045200c160b8600c640600c050040b5183e43d00c0038240409624030780320300d030f0121040c441186821103180e0080e28a148034902c00d541d103c080a0322210f03448281c0a0b4003482000074854907481803c0c17050301c0760300140403120100c3d80d07403034030840c80005020a01d0008602d01004a0a175209008850143c11090024600b10250400030129507100d05080c0c54038840d880c2c00058841d8010407d0b2807002d84503000000e103403409400307000000021140c80340889102510510075160404151031700050940748d002c003c00303004004122944a560313081c4001d48241c5c41009041140c809501c000100c05400755600d03921035034000b500c0281c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 497836870 1250 497835620 497835623
    0x41e0f171b0d050a0501020c0f0d0e06090612040b04060506011716090f08251d190929091209040f050f0601030b09070e04090c1a18040504 61
    0x1c0003500c820340c41d8a0315205920310000010000004020581c0c2d0340352030314030042401c95141c0d40129090840040074010f25000c00d0096010f0481c0b4144407100502050607585c041d482071002040300760103030700d07100300356580c11440000720300003414642007668810741c0440d0111103480c204000640e080d44640c5480080b4801c0d00c00000485e01d85485036079024801c0600d5800700121104001441c00601c00502d00610b0040003416002100380b54241c14510038138003020408850090411606100c04415001845007006424082c0c88010303105200d404802c0c02070950f141442c03190400c0c42007400c0c180e01a4464580b907441905040c03084142040011104000150004080510802c098400405030440c2c003c000241e440c3c0035600310812240c1c00c3e2103042951058500700a040d5805200c1c600f80c006044a07003c80c0c078035000e0310040c451041090064081e584459160041050300e12190002d13054140b100a440340320b02c1443c080030f0300305130000d454139020b031401840349060070b00c2642e008a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 497838120 1250 497836870 497836873
    0x3090506070f05040b092701030309080d14091f02010b09010e060307050120060f0121080a0c0303020c03040b0a080f010f06212d0614011103041e0f17 66
    0x1e0301d0440380d04a150803000340709410909424060007459514542c038040118203900c18041c7d5411410010a050300c56000300880f50f000c10404a001500038038980319a0759401c121690b50755103140459a080d0940503460010002d00c0d81c007403086a010f4000c030003d82c1081ea600e44840e0307030314a18100b907000b0950b40d89405800900051016500c141d0f94a00300c2502007034015003280884103514680102102c03550100024000180960307090500480003403111000034592841c0c56442e46003052103202c13040ca044c40754035040f0a04040c0250107035500345411105407911180c0d1454140c03030039801085810000b86641e0001080144441c0101e41618019004000e0090401e4425140321440c10310036108020f000c170100b500030040d4041c00c112071961000341076075405000007103c0c40a000b103015504c02c50a0003030500032180c995440701940b05091a0079481c156030b180780307a1304512840e0007801303d14903650025840800d21138100e50803699031003501511196140c020010040c400316402d0b00c81d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 497839370 1250 497838120 497838127
    0xb09010b0a0f21172502011d1201090b0601030b030a0f030e281404020a350f0915090c130e1009051e0d08150a0603090506070f05 57
    0x2001c005001c900c16411070040000c589014a8803008221394840c119558001c1d00092a800d40c0d0800002141c82c6040501443d8015206540060616040f85440743e8200d05424040280b0391383d408110543c510001000308036480c0346080c100d480140031034903d40070074201880c07490350782000240e40c1e00365504030b100c4000c2c0b160700b95400c49120102c0142a81d0004c0354650340309180e90180017151071040d0901c03009010a2805040c039a5880349442c4141c401c6205101512069802221030084560000c040e400c0504076030469603250390151184201e50281ca0042000601e48440124016110442114203030707140e01c1c10a85c040b10f4120307860b801e02d0300f00e009030f50084e0418105020b030f460307001200030480075154445185040c1d010700c000040251030b90300304824814144003264801c01700b00e00340808071800c41c9400341e581c084e200001c01005001e10006010142413040c4c0c0311031482c010303d240e6810740c1d2040c1c01009411400f0087e11107018400200b06414010000c6d040e03084015190341d4103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 497840620 1250 497839370 497839379
    0xc081e0606040b28020105240d03030b12030301030506150904110f0312031005130212281a01121506180f06050c0d0507110d06180b09010b0a0f 63
    0x465802c015003804a000304100d1003401140700b0311320b80e000b0809983c0001203e24041e1020000101d2440403108100d04071a180b240689940c4411601560141804070f10f81e04648041200e005c00b185982d0201d01000c400841040b0020881c940100300882c41c05600d402024200001088160303001080310b81d00d80c810307691a050242d4041050b00006041d1240e404445109241580c07048030904a0300d10840d100b4015071520f503042c2d510302070504108500b0041700344011080c10320701614020b80795000320504500d01e007000e144c03410b012580b04003e200304901c640388034407004038601c20b075400316400007c1170a00340a180725110b02c03007000114805070589000425542c2d04c1159030941040c408032040803031000401140ca0f402481d090303580a07501d002080c1c203942400e860b1030110042210410001020842c0ca101200d4100d00485802c0340000b00c900d49540201041211880d4a00c401b5256000b03000744561207030b116440341402804022110010485103180e0350141a10100c0010700911 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 497841726 1106 497840620 497840639
    0x1060906090b0a091d03070b01170303040201140c160803070c050a123002010e0c0a03020105071205090a0305011a01171602030d0c081e060604 63
    0x4582d191900080d800748062081c501110f496800c886040003004818444070010402203e40d14042c83c501040388141c248604d01409051215410002e6000f0040b6446203074140d45100100340801045850f94001c4041c1c030580b482514501c8159604090b0440c0241c1000f2001b1901c1d643c6034502071004004941005004840380242005440c9a10050f0b8008aa2010074031003081d250720b0000341e800a010003d01070480c040500c1458094042d405a020348150400b0784806900005c14001419440e1000a00080041141802040c8141d042c2411060f40d0301c5c01e036251030308400c0011107000701604181c556035584c0065251101880244d003071625028242401e03145280c8009180801000b030030000603116500c0700050302e61003801141c0e0360000a0108200040341d41304000c00202048810610a089414407010002c00c0410140e01c5940c0040049103854100090503 = true := by decide +kernel

theorem cover : BRFrame.Cov 497661870 497841726 := by
  have h0 := BRFrame.cov_init 497661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 497661870 ≤ n) (h2 : n < 497841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
