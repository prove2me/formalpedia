-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:30.679318+00:00
-- url     : https://prove2.me/submissions/f32edadf-a251-4595-a553-ea37638e3acc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 724640287 ≤ n < 724820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 724641537 1250 724640287 724640291
    0xf080a0c1106090105040b0c0f07080a060b10051e16050102041802031b070f021f1706240d0213030c1409060402160204050112110a0e0f1302090103060906 68
    0x151054200709082d01c3c080d480c140c42c2c00b070801d8184000f940b03c1e1703002038520b840548a03035014000004020b0000002411060001e403d0a2200c0d05105098840108001d4000c80c41048020842584202502d0f00c85101424071400495036812140c0c1900400908200000b1440012810000154010301c2210304100d070710440e5042c0361586204a000c110b81c078420100300886032051f6070403042c00400007280300d00100d9403603403856000300c1c00340100310060300702d00200c01c1100541c45410055044601d04400c82c1d410b00b615100002c00c40d03180060600400300a24084005400f45804d006d4514800c2d00c440115112849506107031500e0b07085110658542c4909040410211040071900003407078030141001310240c8445c010f10000751300031241d82c201c01809500c0100142d03918041d08d030003082c4041c410200108681403952080041010a43c0f0035040484100f18952000c0075085e0310407240403540c2103070f03598803a001244064000307000354440c0440001104105080e800440014010f00c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 724642787 1250 724641537 724641563
    0x1a010609051504050306070c08040f030303140a0c051c14040309030c1a07120c0b040501050a110310030f0305040902070c09060617010e0a060503070305010f0b0108041109040f080a0c 80
    0x10b00c209a02c02c6005075905030f08501c0c0040c610074043c00c541c6a1b03840c070940c1c80387e1400c5e40d00c4200510f8030701c16400840c00a0340f580c002903e81c8551a07112508620004410050680210760140c05071180c4030b03000f002d070107110500265a40329079100203441307108140c0a0411b0b00e82840d0045c2505c910380411240c1c00d074500c102180004030754008181d040c2c40349144500e070040e580c440788101941030b505001007100e2300300300500041144c2d82c0d1341d019510901c0089001d00340841450151492103880801406040c000c00c8502d0241000c442e04590b001902e112000340c1c0360404603190700c100d822552489000003140c42c00c00001040342c0d01101c4005108009140d21600c0490f1440700408048464141a40060052541a4010740e03040041e00800046c100d503108003282c2803804640c8150f486075906e249a00740c5904070700613110b602d8000d10b0b05070483d25155036048034030b080c0001e0081c0142c401000050800010135001c240301e54020030785c15155020800000c0000c41c00c00b00460300f07080d0103d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 724644037 1250 724642787 724642819
    0x3050c12090c24040605030a06120302011b0c0201090e0402030304080d0906020d0504050d0311011b120c0c0f060203070219050a02010905041109040510051002031e190c1a01060905 79
    0x11a50f140d89851202084c5410b01d40031084800e900017800d00b000300ca603140c01c005440b00c001280e4500f858441e030000318580c0b14000c40c0303000f0031000c03d01c940f05015004201500503a0b001140348181c48056000415507100c0d0b002007490750240307410404081c0307d503150b07041c0304c07541091040007124915400c403028240341100441d42d0f4021841001c0c0c001d10444400c10000e8002da0b0038500221001000060088542c01071700e9500b01c2110a100228800540e282d00300c42c021f014080a840d0b250505003401c044980c2c0b68103250409050183c58a5070100204003082e109006243e200147d00c2c0440441c020071741012501c40100d104120b001c1a8600740006007810103000d86588080c4016559090405000920000c3c180091803030420359604440031900d80d64034140300300d0001d4154019500c440060040002030b0028003a900da201200740044540180d0b0701100d22240140da18220381c20045500d40ba410030f203841082c04c01c943d2190b40020803905d034030850201c02c41e08200c80d15115546505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724645287 1250 724644037 724644079
    0x30f0c14010813030311030a021b0318100e1f02010c02120a030c050705030408071806241206290c06060d020a03061e141603050c12090c 60
    0x54403140842c0140001808000707400301c0e070318106406410040b4188074640b034108180d61003100d1138288203078003066692191402d5540c1418244405004528110032100c0700054007041c141100d22900100c0030307031400284160fa131410b0481c400b40c140b03920100c00e195104100082e541d0803800541c0b808800400e4a880051326403d03119030003030124648a1151400c401814424100074284102040340d00005081040180010441c00f030107003103024141030b0400c01070341c0551400c12038242098418848400700a5800303110422914140440c01c2e00c040f0285e40c84030090007201c40942c900000001c503040701c02c6119036407080140007841da00c410401428001c3c050703000f051000d50301500006a541c10721041c1000c0b080d0005052005050f62651601e080e0f59a40748254111581e102c84402340c45500c1c000c40301d00c040c3d041d001001e140740c60341d100d4030072041070740070001096140c42c0458642580c41c0100c030421000081ea6070507901c0c16134200ca07541c00d0601e00c006d00403500344640d89103034600703c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 724646537 1250 724645287 724645319
    0x9011101020a120c090e0a0e06280f06050409050a0b0c2814030a06031e1e062306150301050a030f02011b12020f0601050f1c0c030f0c 59
    0x7515401c80c1d0800e0f24030010010959070b0810001d1180700c02e03003c80c00442d40390100344142400e11003c140e03180c14000c014101100904039030940b00543c01900000010f83c0000d0ba421844100000355140050408030040d10280e03004680003450202c0d85014080c002c1131a441d018010185644941c0750200000c0311441040540040e00c11030b44484102001c0715030b0031a0707408420f0b2500c0019214442e00b110700503403043d038031644c0b116500d890400800c5906030140004910614203101e50307e50039110001c03601f0310304000d1f23107081043c19407480c204103040d48154039841c103164401c03045e989800e6000c1440d1605803401c0384503070851a52640c0b1126100120703810b9a00103040e01800c285142da608528481010040741070219a104000000750710741c80c0740b046c3d00d00840707000251441c45080a0f04200482903c40308a4110380c0050001b91912412040200ca05031030701c2181d8880014036030006582a0401059550038910020600111100046141d8002d1243c0c80c1000d41d1030402070100061 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 724647787 1250 724646537 724646557
    0x801060206130212160b04060e03010219081003050d12060504020702060406180317070605060334090608240103110108040f0b01090f0b04050c0706110c070b0901110102 74
    0x5000d03001001418038180100490388a0b8046801c00321040c00200b21003965600006c00ca40b0000c2010050340350b00000a402c030329010360007140360a10900c4908031a6040301c41c001c080c001c101002c1707445600c0c5105171400864014017681e800e05070300c010042c510b10030300c00d0740413805003050008583c502e003d1085a0000d94000d101500c0c0510701001583c0c62070031014219002e2001d00c10000218407558020711802d010514000e948035160301c3d0071002c943c40a0480d9020394050552004480f064026403150324014105c1c50240c1c4a0641039501e01d42160741145542d10704207500041c0041000491030111a070543c22100d101d403200c2c0000254030400d12010b006280c2d07884a80203a540a4007455030080d014020401c20702c25542c03180150341030280c0c0000c0c800c40e0383c1d1050000b003003604d1007220032107a001c8505000b6424a4440b1104501a0043c0641140d41d80c02c42120207400110440351070300f055409940410fa6180b2840000d034000c042c02902041c580e10792a00100d00600c00c48040001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 724649037 1250 724647787 724647811
    0xe0c03060f0702070308041512050f04110d05100506010f0819021c05100314030408030921070311040c080106020a030e060c010204121e0201020a11150a020604030801060206 76
    0x295110214070080c0c00a0100015070041c210040085030800d4010300180000c90b400c15610b20606100601d02c3c070794901000c500b00c1c41c2c40c0c00d2210f0a007494203c150080e8003d602e4100c4943d48900141a411220f1002081e40c4140025441040855089203124400981741c5003c0d80d0a01d0000f9580c41c0402c0710442c044902040318074465074481c1c1d016002001c400264503506090744280c4804450083d034006100f150004010010084225191030700840088082c40c00d00b0b162598160f5a401151101c6210b41500c1e502d0955105542401d4440c0111820440780c1c003d0b544e01342843c10f0500310101314062030030019140007081c009d0000c00c0c12980e880c0d001301040056034400b2144280c4400155a200f0010000300885070024006000945210022840c180c1110710780181c0d41003401100358521501003c0d080c004d81e03000f040d051542c0e5001114024045a0070303000405102c05600300304100007021604002203540020114400c9110351100c4a50366203840090340e590f001141c2d4562005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 724650287 1250 724649037 724649041
    0x411030307120f120c0e0406150f03020f0909040c1e05010905120a0b01061d1f08250c030e010908030d0e030405091305060f0c03010e06180901050a0e0c0306 69
    0x910400c9070b0074031070301240351500f220120340e013020098540c600c1c41a030004800612440880c901231203101b00400e8010251400341c2402c19018112649040ca010103060380421300048140200d0212603011000400e890400d1800c8d02c0c0104039a0310a000f0b58502030b4025654503005d1324503000d50419598140c5a122105140000b044000b08403410103010b00d0081b2140306000074840308540f07000e0045519102c00c2000c0154001004001504286118600d071610380c0c1c4254202c00624420000a460b080324a6a210310a901c48405c100c51600d0904400a51100c0401c1d4880d1035030b0151403183c0e4582c007591417501c0045800c200c1500960300107800801124464500990003606156043c03002d07039041c95038410000d0441001182c003811805584014034040020a1000d5980059000c40c1c0c64201c1c1441c1c002a800d40c001402101c590503401d40200f0410b6981901c03882c500290740b8030305022031030f203001c07441d01030070050354154501803c0c4040c01c2040310010a46860804010740240016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 724651537 1250 724650287 724650323
    0x5091203101412100506030c060414040504051213030b06060c15060f18090607050c071a0f070312111606051e070302030906010b03010621180b0411030307 68
    0x2d044504a0790b0b4883c00000300f60070600703014008905a00d014450004451802505044c103042d2184070b8a48240404c020501809500b081002642d0f44103079000501c43c0d585280c550f00d00000c180a41460540119110a050114500c0d1f0419284103041004860300c0e43e5080c025603000c0c902180c01d440d04030b00c40a5014002c041341d2194001d0b0014501900c0c480740d00080780c82c464400110102c000c03041c000708000368001b04181a00001c0c580380c41840c0005444546444040c6402062114402c44d14010000d54843c0c0a0306e48142185013010307640c81c0030b03241c06840c0f400c0012980c1c5046003400203190b090001c807000c0e6aa03d44c1100b01da07841c1501c03680d60380001448010a804000c2130130a8419200c0270040601e030b0302c01c0d08551070040e906d0030089606880d0200507800400d41d40d40400050112a0b44008220040f80402c0f01b50007800b0200c1d40c2103070180890b05403010790840401040e0081c40054400f1034000c6019040e14820086207009241d03e134401d00341c0281a4807000d103162400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 724652787 1250 724651537 724651559
    0xe0607080d1a061215040c0201140702071203230301140a060206091f06120807140a11100e0621090703031b1104050f0a05090703031e03020417010509120310 69
    0x1029005e413600c0045181d0b5040000c040720f0b083e94540340181c1d916080400c0440900c10030f9604004e80d40004d01519103000e40101640c4c10804000701042610a1511002c44213654940040f400c507401894030b80d0f0310385a01500590760300d03452610900c51944001007403800854254020b00305000900001c41082c92182108140708418030062540c0d4500001d0924003020300c440c401703220f10300496880304c141c00c040003000c0c3c610714008000e0b00501101c40015030080c00f10ba4101e031040c3c6918011342d01085080d00d510f00041206500144006003100030100460030442d0400d000509203002030321500e056030b41c0c5844500000f00461407580c103020f40488100c284c003160510034815940e030740c400000414141d6a0079a01d02d06440307104024451210140d01810368000403c00003088042d2941e00c00a202c00a10300310800301c00b0345a1a4003010f14400d4048801401c60340d09005500818920396500074041116603482c02d001305428001c9402d185c004480c061604203032400b00035130600c01740e42e0b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 724654037 1250 724652787 724652791
    0x8010b1602190528050103050603010f060608061201021e0708072f0f01020d030f060308160506010f0303090303081e09060708060d02030604120e0607080d1a0612 71
    0x184144004403a0801a40d8a409802039002424503081e005440e150a01c400c010003500840400200d10042d0b21140b4600002141150404d1801081c95201d40d40032900500700d0301040d86005081850200e80c064108000c01e02620303040d1103074104111804560340c206d00401c13910005180c0b8101822040d1180c074006044c00c940550121490105150b071001d2281d00414080f42d00c00c030200240e048008004034270340324104801d45040f0f98805d4a940000d40355000d131440c3d0414036646070400b802c0ca00081d03009501442e440006155142c017000e910300d00c0022210802c031001e01c100c03800400c1e81c0710312442260460341d040d00e580d004607045640a80702464010114005c0020041c1340c4440344400c0303000d190045241101034400c034180410010924140107201c18052002c81070f002e0700603200020441c0c2c0c002c1d04032002203c020349044040780c0102c1c000e039850f540071002266803020b0050003002410303000c2d0841d03420004c1098080e502040022041e114a6004c40c062106120103881062815 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 724655287 1250 724654037 724654057
    0x801031202120a1d0d0302031c02041a0309060709030209011710020d090b0703022106030f061603050114010807051c0204140102100902030706050f1c092108010b 71
    0x990800d10190341c440c92600b041004030002285800744a01d48101c2c81c00701d4000c1c07602901c5c41001e68a4549020759a403140c40c4440001c661100c0b2150036041041d41550040c19580044110324140440800760035041640e07200d06500400f004158014050049401160390240465130701d40c0c41e1005004400245002d0b0301c0e40341c00740c04604500030300b1a200a11848450840c0050f00c001c281c1084000c030503004000c0024144104078511034040c118090360410300542e030311410281da605001c6402d0030403082c10044140715400c2407010b0b41e620700c00e40c00d04400f0755603001c01c100d03039841021000100c64020030f5400300d100c25004c240c1c141d00c140002c00080e1420303090540400591842401242e211342d005412351003854980c202c407580d040c48101590408100d00781700c00341880d00040d1325011035104101c14003800040400441103e02e00b9159003001c030a0b8248031503c01c3c000c0050280100240844d40c424003218452a1070748044103141442503181d458880d03030f17801d102d03026030b00741e000b10500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 724656537 1250 724655287 724655293
    0x5040f0f08120a031b121422030519031d0a030507020f03010e060403030c320a1b0b0106030b090f070807050f07150e030408030307030213032f0406060801031202 71
    0x18081050009812007402c61704d0740c8103000000f42d4000300003201d505c070a00c281040304242c140701d000c603501c52200c550742c1040325801c40c10343c0c544e141c180c82c18803480340a61001140c00b00c1c440e40054141d840f00c070807058105488600b0411240c00c1e80d84500300110b0041c00b0407000d00080740981401940300e6440e982c0030340000790f00c0d01c500108524145080300d084001030345844804410641c0281c08041880003001040c004540414010520820910078074490b02c001158611500d81720b45040d1121000d000d02800070030a5500b44901445400d016120100342002c903425010700380241070900c10031000b0620002d64a90560480d0648009412182001403c0c00003c01c0244030000525001e1301c5090b6502507114020200002d50718040d004c5003264100b403104116040020007102e034880ba182c540140e0b6684040e0704405c80088a410292502100d18210188210910b00a9030544115000305250440d40b8007044140c9169001e100002890304004100240c044492560040d210f8019 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 724657787 1250 724656537 724656551
    0x40902090f030109050105090705010c0b0105040f140a020a08130f020f04020c160503060601020f0303041202101b030510080a080705010b0916180e0601200d05040f0f08120a03 77
    0x1a013514181032080e00c00d079640d1400c1c00406041045804024142800c1109c0f0a1a4a40314054041c00501c01d00f401507864111100c480c2c40181c1c010080b10303d10042ca64030908018030404025040380020201155016001c2581d5112070840d01c45010360200e000005600540d0a010b940c0070b20030400d54200d40c0074800c01e03541c01028002c0c52407080040d02e0002c1640d180900b0540f5020000e81710a055400a10a89110101c08400c407a031183d00002c3c0c5158480740040102d1074003403080c0c900790350113141440400c1500c4401c0800315681400e0794047c41191626400031840d01d080384503203d580c0e88145228000102c0c0c1e10040c11790309015000015003c0c92640202e1402c44c0200c03803030701c413a034040ca641118694200c0c0344001f03414400c42a80c42d0f0035007444114401e042000d80300606122040c0110320301c1030800b8403c812044004070075221704901044c030241c4282c015000f072648220403920b02180386003414a02804a90800c00108240207030390410554551100f40c1d450109a10744030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 724659037 1250 724657787 724657789
    0xf180a06020d20070b1f031a18010e0d030c05070f050d08152103091207080c0102120315270103061b021213090f05040314040605040902090f 62
    0x8050640704000907000700f024402d2400c22698003054185095901105010000c08150b0700348001c0e038400c103040d607880b03162400017000000c0038901d540020003a0440107000d06514002c40b00355801084104149030f032000c2903001c01800d940ca80e243c2c0301d5032940a032000c0540075100781c03c29265420f107428068076102c120740300c51020a002480c10307100c075800040030808141e480306002d9400007100310401801e03410540010200000704103103803008050744140901122003401184c00310320009203c0480b14611003c40d036122407207446264014040e0072131048046d40045161000350044d000745a186984001440120500703030381c101c54002c140107854081c41181d005940c00c64400e00100504650301d149032400175103645ca034103000e00c0312801c1101c0200c40e0700005c1e41451400307a081d441b40c543c00401c540350181d10060340003080590400c001d40e004210765070b204070300a60081d5205400000d10010601d150b200d2440b42100150041000f00a0b5184647c05007071240d0f4020012500028850 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 724660287 1250 724659037 724659041
    0x1507030204320d030903150605060a080a1109031e190501060918022d03030a0305100e1b0904060302060c01021c0e1e0f01140106170f180a06 62
    0x1c00d201548010721100400c0e440851182c0b880118103c3e004807032100d10ba600205803140741e1000505001c034400000c09050000d4001c0d1024000c050311540d01c40800f420000c14081c4182c8012000f14a00303030f480000403410104407454080054000c2201006440d4101d40d200d644003c1c1c0c04860003100c0b44030074008961001c51803030a00943c0040fa04c2404c00c588203044a428004050410304003020030760040c0c0b90a007101110703800d40c80c0c00441c00da0f0104141040b1031101003116915010000d824104a50180c2c4003500526040000c1950162101040e41000f0801d962400d01a500c0802448040b038140b0024604d4803409040411101d550b035010944540028100301da85940100f060f0001c85413110300b0007030f01100c1100c207000991526014070788500001c000308000e0550b501032840001c4d000c01404150382c044500030004140440c1c1040800f80c1d0a0082d0000a5092115050300c001c210308404d000c0c115102c07555405403101c1c43c08d8100d5482c00b07001420320b4010701410b2008a50710b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 724661537 1250 724660287 724660319
    0x4112203051903110a03170928050c180f09031306120b0a0303050f0a050405031006050120060f04050a2010080f0a0b06040e07030f0509010903021507030204 69
    0x42059800d010b02d1403401800a442c40384078009168418400d080110303902159041020585d4400c4451607214079805a0604803c0c045a502180c0a442c45542c88a00c0e00c1942d04000d0007501030340d02c000340000800007541c00d000e080e44681c07006600815240e1103603034411034000011408880c40e1510102400c29100499030040c0080717080c49404044803041341c02101c80d030020444a08500700d0650b50b01810364042c50440503025040480c00300c0245010b08200c6014160003001ca503e02c01d51081c03801c0240c103040c02001e001600c022004c02409203460b4401c1450418800900b80f83c0e503c40e900c040c48910700410540342480342180761000b140c041c42c800c440d4124140c0049098120000501210f403c02d0400c0b802040b9819041080ca861021035070354100307a03000004a1070000b000c3c00031310140a075800c2480b60301c03410000d0024a90b010b0b40598080003440005204c43e90b6201041c074201c0e40c400c00090b0240e04540541c4540c8581c050445038499824103005040984580e0815448000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 724662787 1250 724661537 724661563
    0x7060302070b010902162103180b0a0c050904090b1e010b0f0703031103091b1002211e1e0405030606040510090e0f0f0129030a02100c110411220305 65
    0x1841f207051203c2d9140c01113050444da03821600004040307d60321061400300040107480c00340d5843e80410300c0144520212000d408000b03000780294003090404602c07a038070a07681d8240c1e00c18034003180c1c65108a500d07080f038104d446250800e42811504055000320f5030111408804040e030b50050149040d880c04007640c09a1441001000400740005070f406c24500c407511101e100e54242030402c409180e00040b40c1c180455a4810328030910956450110035014014981c3c80c0a1007800034040107201c3c1002402c0cad803022002c881c0004504c100c4581120784500c1c011190150824000105c2d07505254014a80020a0703116811016a5500e902e00c12103940e000d103400e0701d40100012200c404130421001c2c00a03c03140000704910210038604001c80300248002c130351094030303041e800c1807165814820108030f070b5000f414400d2002c84416004048100c0b91004035030741c0900904075042401c2c58825404240f45c82e00700549030441d2011080307100001142c0b80c02900c0325001001c80020b605000307034a00014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 724664037 1250 724662787 724662833
    0x20d060306050a0c0e030a170d090b1f0f0509040c090e011a1e01200105070809100509060601120608070602031327020703110a08090307060302070b01090216 69
    0x800c00200c200382c40748050103004000d0300701001000c1c3d61b408606464065401803140304c482c59100c1e071141d0a0f004055a404103c0d1a040d82c103c107001402183c207100d03001c032030100d42d07082d08800207401c19220540903120842089100910090a01d00c110302d40142c0900d08100e51555100808000d540b0407080342802a5181c92410018006940c0404842c03e0b04488400050008803118581c480344034030524100580c0c6a000d101079000d1442143d203245000000344510b240920300642110015160140b061007800e0403008400c000b80f00c2c403801620385001402e0240c48110044408c03c03410f46000505554030f030400220345108010400040403250060354640306040400d2035140003540c81514070b0881c0031036400036884800b01007060716036211070042c0c80e06440e040c101c50220607c0c04030390340b9205001e5041c00b802000c0020303111002d000c23000c0303070700c400d0300c2d58070442c01d9004804000305030160140051000800c60303005800d054006c10510420540b01b0344802003414045208846240303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 724665287 1250 724664037 724664041
    0x17090a020a140f01140d1d0a0303060e091c0f02010209030f0105010e0105030f0d03050a0e060f090f150a0c03020708040b03060f1008040b040309081002040905070c0222020d06030605 80
    0x70070720101d0322440110074200001910004035035008544141c071046d014140d940d00c410121070001a03c8111030035407403000ca58001115180140060456004541d6500c42802c00620700c0940041c03100d5100b0306014100c0d981c00e40080c0182c56002001b000001555020f00450810340c400b0041d00d180111448008261545030a40500ba618411381102d07010b81c201c0c0d20108102c03840061000c0c070401072482d00003440e58660f1010001005440e0314209540920801c1c010503051103040c0c0342c0204060f40030307944080e211038846540c400e1110b041030512090100011042d840795441b007101c601503420b01515000e02d590360145160f2240e0000c0e0411540441170281e64140300380320601148050f100a40c1ca4a41503502920078040207200500b000184400601054444d88007000242415401c69108000703016900d80a5049400303100405450840000d400d035108015401c0c1c1c181d0060b1001c071071542402c902c00c901e0b4120410403603196800300040b0402e142c03103124420041d405460002014 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 724666537 1250 724665287 724665289
    0x1a0d0c090b131806030210121821020c0f0603040215040e01170129030106030c080d0810050603060d050f061501032003011202030c0d03091d0717090a020a14 69
    0x3c0d12910010560383d81c9001002d000503260002c5041c6452850b08044407804000c11012001d0101c4002c0e41200203a0440b80d8004c0080c0c07451045104030b80c0a00504c110080030f40708a03030317420310b83c410140c0c402c1c46c0b14102d512509004000319041400608506800412031140d043c00d07030700903030004d110035088600406c40310340c0c0e01100e900084128002485480400700c82201c48562801c442c20341c03404c00b8695070104c0da0742503108030001c40c6e120780e01e00c011507640d903101e540711028550030340c0111300c0b4900060a5040f04901c07140640d040148a1811901d400003801840140e841003140d06100e1001c111607042d42c1001010f1040c07221040c035800c035004034400102941d4003241d100e020143ca050b5003c3c3d00741e2055041c0c2e415102d041031140f1420f00301e80000f0303141a0092059540098030080244d0615911160100688088600c03c00e01891015045100b0f030070b08880b000300240b28844e11611002c480c184064001c101a4100c03a0702c000c242d0000f40b02c480a0303500010000345c040c1d08003021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 724667787 1250 724666537 724666559
    0x4050d390b130809310c1805060a082d0709152003040b03040c0305010605010c0b0a0b2205090105070504030317060a0e011701061a0d0c090b13 63
    0x10040c140c1d260002c290580740d40c0c50f10035016202c0014424a8100c0c00c2009460494240700410a514413a0803803003481090320701c000f0001039503207a0000d041034041c001c1004842c02c43c81c08641000d171040c4d181541c500001c480a66010301480c10b85c40192000c901c103a0032035440c40401080e41d044000341f606090102401340c0c50703180c0c4112158a40c60030818405600b0095070401c44144866443c1d502c1302075518a800d41c071850308040c0340100c02000344070512170942c501c002503030b02c581c008004003900c40c001540da0800304400200300c8000072002480b4049590803550030914060443d6411008040382005e070701050506014031207555404020351303030000340907441d000200350401c140380c0750031030314002d061000c4508480450040480494000e44607038840c64000c0c07071040c107031325440d58441113446c40102c2120610041503007016030104444410090740c1844441c3d50015526040030700c0300c00000750111400000a00c2004100000c40900d10002400c41c20420054600324a041101c8a13031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 724669037 1250 724667787 724667791
    0x304030c1d01060206130501020408100603050c3703120c110a060f05031005040e030a140301060813050f0d120e03040303270b18040c0804050d390b 65
    0x41c181c00c1e1400401c01942c0104856400c0081d0744206400020749050403030191249603c060281c1c42105203864449240c0c0e40000241d0344150180c4004071500c20401000c109036241c0280807460380344c9049407030f030222016401d450058a080f00c544507a40c0e200e80300c80362000038481000c1001010b11008103d80a0800040b100003150801262420684001c10794420b01c200d01040c46800000325100c01301a0b0705040040200800074072050141034030803600e0350000301001c40401c0001a5060b207194580d0b00b03403030581c0c1e1544d8030000640d03035030b040401403524900810740340741c041c680303004104d59014841040109420703255042081b80003150309080f1051031686201d81d030414070060000941c880305070103110114100128100450208400c200c41c030340c0c1d00145c020000001c0c085e2a4030051440d010002a0071541003101040800c0c003610700d69022603000b002500301b00f881c1c0d640356010307100084014030389868900f83c13000c80540340c00c405a012054194014400b044802c00c100c83c2081131a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 724670287 1250 724669037 724669079
    0x1806020306040e0d02031801031506020d140c03091507050114093c1e1507050304020a15030b06040801060f05100c1707060c110610080601180e0304030c 67
    0x84141d07500c2c4d009440b03016109030b0800d03610400c11500c619a01c240c200902c154044900b020f40c040c2d8444001e96142000e90020020030554030890141c008942d055500c8080c0d8a4055460f000c0070b0010001c0b894403032140303844000001d11241011580074850040e080465101c1a455400c152851500d44040c640070380004a4070060803100d4211041c10180181400c02050500c003a1a45612030911198921103403100c407000241c90605100004c1c003404015480e0700c0c5010076252840d044802e0311040318080d4000b4206041080078095400340002c14561910340015858901c10020300a030380190304c12460741e911480203200f0040d07992205802041c08403031124a04803000c001501d1082e62136805000203580700c10744010342c2040f5044070030042e440207040060060500c40500751401030aa402c8151190070002800c10803030350000c0d010383d00343e4001080f00740c1c0b908807030341c1034225444900301c61a42c86841d038228441c0200040c001071445600c0b125189418080f1610407003200b041a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 724671537 1250 724670287 724670293
    0x2c010b04020a02070e090a020d150f05070804032a1a07050a0c121407230c03120309010209061216030209090a0902150c011e0504241806020306040e 65
    0x14a40b0303400040c958102d0310803590203041583c5e90403601c2d01b002c90401c80650000780b0b4200e00810840c0c0314807034000c0d111000e0020001e10300d0320000007040380c5c42201ca03c00490214800f10780424020441c00003128110950041c01c0d14441080c03510040a01c1c10469850103103580300c20005200d050308561086c1545002d80c00d00074038260003800da081c0908050104500310a540c2c001b9846452885c880d00c281d04031290392480c29141201c0102c02025602a000c81c40e110034031801100401c848048410060081103203111090110070b49034009051032445650811070848240c540740701521300a11070b40c0584040c0e151040c041c0001c82c1034800d05000705481041a00f20326034900110f50703001a82c900e0001558542440801d1101031001040003440101080c1d03003001903070540201410084140c41d600c0701c0e0b041091000c0546005480007003500c400f070042f880b1b02d5a03a0041040c068001c02101084160741d001c0d400c03009a4070801c0c182c64881d000010082c160525000f0795480791205002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 724672787 1250 724671537 724671547
    0x20709020c0c100c0506070c1b081b01020c090403020a05150c0412260d0b04180222020a030f0b060c070620010608010c02011b080103080d2c010b0402 66
    0x740a031625072030b5103450b110340002c00c0e038031102910a807540084a948002255014103102102400403102408102d80050503081d400c516118450f80713410449085100404001c00001100000c4a100d1400241144610382810045964104402d4000c1e070080d00a40031010280c2055400e12281885020101e16414180025a00d84208403411240742503003600c540c03e407074600103582c0c4154195180245075045070440c0050b00321001400e12440a09040280841c40c600740010780303040004021a91100c4050300c1c4c05030410040c0d140002c0d02c0c4110151b0006a60005a4200d0f0002480d03c0002a81e690726410a02c843d0712910f900304804881080c00c2100107124140d4400d81400380b1010459080c170b0740c9260880d041d2503480603240a00c004c1c00403a48441b1203500825012144070015800e005030488034203c018503403651180d45550b81c045a038250b446031510340c1d004030712805989550701304480031503400708400c9a04040c12a158461140c021001d03a0039114800a5244110710400c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 724674037 1250 724672787 724672807
    0x506031509070e0a110c150a14011a12041506052e0908010e0c0f0d1a06035214060d1103010303140304020906040905280302070902 58
    0x40031001c5428001200000e540e038020313104080c00750a80901d10341440030650301640c0da0040782d800d1071500310005049280c0d0f0346945480640c1d0800c9440b05861900c000107220400914284c0941800d2940e805850802100441c0e6018031045600b501c40b0740364102400c1e540b00b514080ca90041c41c00302c6883c0c9180d00414002a001c585001000e01e0b501040d80c90403a05500845c01100106101402081225040000c1d00d4480d140070000911600702c40107421000e103001d1a0300107040d40c0042c40b04083c0710b280005000d0008014040e654035101304c00070140b203210300c021491071030364202c241c02070b0401c07030b01206c080201d0408542c01c001380140811700c000b80158000c29401c50749141201182981d8420200b0070510a0035100016142840100050448004002c50403244240c1d16800903800140c004100c500007590f0080d403020f910804228581380c10340107080400d004109540460040388100c2000b032400c2d031000c44203d5803152048043c103030140700c000000c01080c502946041e000034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 724675287 1250 724674037 724674043
    0x403110618010507050a05030c0a0506010504090c03121b081207020c09070c0c0302060403030801050306010801060b03011a0d0c080702100b0d0206070305040801020309060412030c0c021516060506031509 89
    0xe881d0604018021400d01c1c18000200800e5050541260039030390b6400920340000d440c0c9602d141c0590f458480c40f40001100d041c18441d421101d50408840e829050840d0303249911600c0255010b81080340030008401100c00424040d220390784189403407a5104032260040c5124031008218000359001200c920180380c5a081e0029840003940c940f00c080074001d03181c0030038200031503007000c2e400850100300842007640060700c0d41c1c1680d20807012030306140c0c0ea0301011403d0714428003c240e071180c002d000400040c1c841f5800800e14043d1038540703074244134002518004403081c41290200041065050200c416014480301c0000101000b052040b080040e000c90050502040024016003000a0407028144581c0a40300a00380e200000d40d03880c2410034500d5500c0d442620305890348814052811007042c000d101d00305503c2c6860315a154000c1041d020800c8400140c8080203203030340104442d201461a032000d01d100d1511a070700014040c20000d05161800031044c0041a030b0003c248144407081c4000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 724676537 1250 724675287 724675327
    0x3111507031e18021c060504050303060109080715050a051c0603020f120312060402070516180212070e01020c0a06030603110319060e0c0d11120303011a090d02031204031106 76
    0x140d0b2803210f0050050403404c44505e59120143c50f071450001444104140030004601441099807504602d584643d61a621000740b0700c6000381d8150703021070f291012400b60020b0040c402040c28000c1c146407012003c804c030746103155000c0341c0d210380c0c1e210306008500e0001107003c00306505070b40700c06101c0c9466000325502d104070000120f61540c0200083c2940d41ca5404a40030a0f1b486015560400c1c4031001c0c150b901816030003141000a080818440600b05501c00d644c031f88180b03454003e21540744d0143c160b8003049281c82d901d0450040a41041d2140c03a02800480200708550300014014a107081201006241601c014461b40220050600c003040300003c800d1000e030010700c00101e581c1044416403902d6000f0b0005500700036903008183c01d000c21032008422583c410744050482c2981015403c0e201e00c0b00340246204150000b1100c1c4028810740701500c1e0002010f0580044100d1a0b00085d18040c0390b00302c03514255400280600410848421944e290401590b030341e0b0074808100c00400d0301941c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 724677787 1250 724676537 724676539
    0x10b1305060d0204050a0b0c07060507120809120f18040e07052e03020a0210141b0d020c0a1e080304030507050a150c031a090403111507031e1802 64
    0x30108003010200580e07070403135006100041643c4511a1f035880405141c0d000b922045a1a0280807000140d4a00800440309190b0b4018174009018002e0641581c1c3d00ba0013514100d142d1103a1603146440c81400300041035554175801025441e05080000d01861581540c90340c0e014505205401d2460440000c150054500440340b42c46049202c01d003001e542c00a143d040f42880e15000000590207802d940107080307041c016170a8504001407402400c040d160b070f080e09194940103c1d4005100880c007400790140e403040840c942c42c80c0c8007a1011300c909a800a2280b21103e821030004001000207801c09032014103101229081c015056803100796090000501c060140580010782200300001807207554140fa9000000f1404030f90510341e0702e8003c150748081900801d10301000e01d42609007820071a90740450041003080349941d6960115690140251950124419402802d000f8900076400d0791040d901c1d030381e001448808000034100703603030584082c0400003403503d2003034601049190051801a50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 724679037 1250 724677787 724677799
    0x1504030c091e020a0f080c1201050609010509060d05060909070b0f09120a0303050109050a0905100e01270b0a0209010f03200706051e0106080a0e0703022106010b1305 73
    0x1045582d0107948001d02c4010842c0b407002030f01c00000d030341145884800718040d40d6421138913641c94900700801d2140c001c1001148014400421881c40e00b1b0000301188070041c0340040c02e00441c1c90206017150481e14881e4102600e400c1000454100b42550990010010300104049480e100000b802c911540d451881a078400086045140e01e50400c15184150848121051303281c4e80e040050040500f80507500e030303c81c103040111704107020500070408120341020103880c0d1044203049020040601c00905042035403294040c800c0300d10b840d00d42000c1d001d8550203140c01038030f00d450a0003810301c1c0201340300b64080c4140b20100e141e90b4004002428210f0a040000e00038115140c03004032070130014240509101c00090000400c10140c000900640c01c1c11401200340b440c9250340c6c0c80c070302d10900426001a200900242e03480001d604019200e14084007510707070b229101e40200d041d241c481855490442c078040304426510a0802000340108450f100c030718100000c040c2c0c5c0c03045804191242e688605 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 724680287 1250 724679037 724679051
    0x60c0301170c27011401050909151c050d020105040c05131401080f0c150f0310080307110f030d02030409150801020313030807140702092203050301051504030c09 71
    0x20401c01210000002810680300d07001903e800501e5108010120b4004100c0c4400080e200ea000c40c000c0b03050352016110541804121030501c60160401407140070840f0f030448002000c0c4e00da14180c2800140d0000c0c922a0784800c44c2492850409503403240d9085a00d803a04120102c0d00c40c146000686108468070700d42c02240c2301007400a0710041920320800350229000244801002510071031044c0b881d0103880d14182440c0070008241c20306403030843d5240341041540a980040340045502032841c1c8500d42595403503105003469600800e0307040303951055480c04600c0c14a0131000c01c000141040b8000e1028030420340c0020740b68007c03885114030b810340310014408162031000c0407402508610000f15142c0c640fa15103400ca0f10f1103058141c022178441d10208034868801c401400784a11144001450301c15a41d00380052101c00509074294a269401c511110001d460790f00d0041c2c0e4040d5490315100d50501040003c07c1d0030300c66120715842c208002c1000062802403440b0200c03041c80d4030008040f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 724681537 1250 724680287 724680329
    0xc09020d0f0507030b1305010b03010e0613050408040e010b09010906120b0904050a12080c03161403070804051002072d02030618010c03050c07020d030e040f1d060c0301 74
    0x2901e0340c402100c401c24207240401582c40d07850380c4000501002114500d0001c0d4803020440112002030185500f00d400c100018054102101000d50304131f807001d003030303d000501d07000400f100b01d0b0000e880803030320824000b808100d0509046081805050b508240f18505141e400000e040c8020611500007801200e90a0300c41c2400d951b03101381c1c01d401014000310300524203443c1c0070740c60300f102c01011030300c0d43c003a4000c0ca002d82d40700307403d00c0d84650a100c510926548907410500e031081d0101ca824010000d01030002180c0c08032b40b9005d107000307480a440d40c28103400c282c9040e5050001e945460500540305015207004250100850400103400c03241e904034001c0501641054010741c07560280d003610441c024440c1c6000c0038800342c00c1c40c0b84248000c200c0400c1c0c000d811001d40c2d000360f45000340268284003641c00751802e21810748196101e42002684c50718800e000c14295140f00944c00555039486589046c40062a55103d4500721548040c1100340707403c010707507105400306009104c0e0b80107603801003442e2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 724682787 1250 724681537 724681541
    0x1209030c0f120d08160801120809190801020304140c0d02010c02060d1d061b0a031a04062c01050105120424020c16060504090b03010216050102031e040c09020d 70
    0x1d034000d42c25034585854100c0040c0c150442650420010118200070049180c82001102d060780c00c0e81c0044180107240e900e075041203400900c50ad9038426441c1c0c0e40b102104408140c8500100940d10000d40c03a8134203801c0102c05807191021481032900030400d43c02c56556400c031150401c41d82401c082004c0117040c00030580c03074000c1c001d81070b94091512256030004505c00d000c9518242c0b1310800c4034225035030f01c50105500c10301052045180d04050213041c035080d00940160b42e070300c4d000010010140351a44002425140c0c00d03800070306145c5849243c6180080c03d41641c807100e950100c411141075141000081c01c9110700c44c40d00000040b40030110307080100c601105100003101a0450301b581002000580007984524070b4102c2e540f1511400202c0d0380d520804010488804d9207c0c40e0416180051190292a0301420242e141d50301b0480d24607512000311030040c80a000ba000181c0b64501440404040c02550b03000d0042050503100304000105a0441e15040d14003459000d03031960b000c1d51314000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 724684037 1250 724682787 724682809
    0x50c0103200412140d02120a02010f0518010614090106030e1c1d010e090403030507030b150a08071b06271101030c0512060f06070f0305030601021209030c0f 69
    0x2a400d0000540020024800094401c0d03072030298130440703150f8107000c035000d545d001d003c50b080015030807013890591800c2a92000d052600c81d50f00003c12081500c0215000303c3d84100c68002c0c035011101c0450954910074400c550151861b00104960210701134000f98100205200b654200741e00e481d10b80080b40b40500180f40480c01c43c42c000e20000c0001b02e8003418026861059640302d00c1e5210700521690310030a8007034a045c5025000c80201c2e100d9490480c040c1a00900ca00d081c1a205c01e458011510307406042401040e1422000351640791403140204a1000035007001e0402c030904000d1044000c800c003080c880c2e40c0d80050001b600c01500c2089056a07522401c03000c0080f103650a104040c82071110b0003444402003641e00700411140984291454012004403944071600d040005840e400c000600f0381c5c1d0f10200078200c5080c60019030350012208a80c95080b0001013020050244a580400c410000c40107100c0319641406001c002080da280c1c848409144580055141d02141e9203c1e852454 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 724685287 1250 724684037 724684091
    0x20703080c07030c060e1e180603120408060402040501140907080423010e0609010203101809080a0f0206010609051807140f04031e0521090a030b0402120109050c0103 73
    0x1e804c40d40c3d65540900b03110030b00c092042c05440301d41c050340d80000d00c41d03484a0020400610344c11030303903c20391640960114024581c5800d88501c111581e00300500304080d00007002401c0060030103183c2441400180c90041c0c2c003031690111030000303c1505694800d1403e51004062a00d04070320b9a8604200c0c0702e4800c1160142d90001c4011410542e000e4103410a07011660301104a80098840342c030054201c0c401160221803140304003805000002c9007280c1039100031005d8202003200d803a903848003641a401034100c94089160f84141c820841e80511103e4014100d40c2020750407689024003150f81750300340e10b8041600030701d01c10003d410070740241c0201040080c00c1c01803584440a103003107218a640130340004d40d0042101002340c0c540007070b01c0c22440d1b942d940c400c0140c104101c24040b070207000c0c8504e81c040c4108400600111a0b81d8940451440086004082220300e0381031600500941034040002114140d0525510700d011400001d1003d040c41e40078a8000707204804c40c0303681107126000c41010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 724686537 1250 724685287 724685303
    0x614070803040b041a0c21090718060b0a0309171806091809030c0f0c0d060905100f020a080901020c0c0915030f0c0f03070312030f090b070c0b07020c01020703080c0703 74
    0x1001040c4108401f034422100c1d41301c01c0400b5144803e002070b228040459031410251f000010900080007444214500c20000c40c0380450750688800e00c01949400c0480034000003565101202c003404400004104015405c203090761410748820907a8501d004440015809050001500803203500d07580a0084404610301e1190a2410070a45890312640000e542d03070160b210b01007209074407030004074441d003807148020206050b03043c10780e55540282400800a94484c050f05064446500660007019000e105e0007a005943c1d0304d005002908503400503002d6003050b8414050342c4058800020301c0c9011031011200c808242d500c49400d00740036079081040c5501802001d0400003000b00c0000c240503818401c0319a00c45200c81c3d07200785984c1c2d151503c0003411049a000c02c2156050117070b8440c5041200019002c56600d00589801018110131350b0060009101c084102050181c04501a50041c42e6840504a40c0681e900005d541d80018040900440e00c00500e856002d0002c004150046501040d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 724687787 1250 724686537 724686541
    0x3040e13021804120f0507120201020f160303060918020d020f060a03140112080703140d0903080a050105090c120604020c010903021e010c17040314030a060614070803040b041a 77
    0x66400ba01005440071074156074a0304140030307014066041548802e0a035651b050910f83c3e01d4581038065a80d11805c3c0c4290355080104007140b41d00500140700c102c01403101c054100c9001e140050444082e98041c242244c139151412140e0805100801c0003560104c4204640010741d0000900754038040d034820754410310004007109940e805401442400288400c0c4402907a0385806051282414950040080d0020406d82e00060702428822a420840c400035508003042403091200301da00d14281540821015010040c1044c801e00440c2d01405043c0c1c0d6540c01410103014201c0c590003140c140840c240c01d44000515540c44660541e442c002000000380103203555404c0107515a101d400c0c0d1a40c05202d4450700342907400d0305010380500c440107550380d800d0034a01101844090a00a0001c500b001510442002d103e50190080c40c0185c507034120005005c1d2070008042c12000f202c29a0038424002844000d0120303d10105a0780c2c019040741d4200e1f5141d685103440e03c40070301e880301112080505681 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 724689037 1250 724687787 724687819
    0x516181e0612060e0a1220070905160903110618130204050a14010509040507020309120c13060f060e120f03030411030303060a0b0d29010f09060203040e1302 69
    0x1409406a07030144008011081501444c030b611001c000300090682c40702e00f0600310196104a45010750401c20f1001d40d400c0340d044141c40303401c0c0b1810340d01c000607054440043c801c15890021200c8031560b40e42c02c252021320720710717910903001704941781170940b00d0000400c00712072040070520304603400304000b000016a2020340c402c220094206015080c02458690307400700e6107210b6660202070400c4144c41d00c6003854800c0c0300700f0001c0c00c0008c0407042140000d001103106503c03040a410800d0300400054180c00310740a060020140b81c000328071a0349400d200003080f503282110306a00076070b561490070716142840c400110f011000c0c2c25000c0f141038424440e984a12038401f00180d8000c0d4894901440380c01440f0301051781e01d00064920952281c01c996080140c1d1664100521a0101014010504002c4500c02c0b40041030309a21007000e501512092898030745c2d001c00214148201810303c60b001c10b003403240082d42c0e40610b000700c00d026080752002c1241d000c01208801b91240e030042015007080c49142c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 724690287 1250 724689037 724689059
    0x315110409090c061d0906040608010f0501030501112704060515040806070e09070f0315140306010b0703080703020703020a0c0602161a0d1805010606020a0516181e06 73
    0x481c0643d680c000605002c00c180c2d2103031780c0f4080351034068648412030800c0d04040180101c4040c2040342d01c5a0769007000604002d007030081601880ba00c4000148942c90750520509461901c0c4000010500c10410420002641e446100000701003642c19120720350300802003001021640c02c030f81c4c1c1c004001d80f414542c41c2c66400091082c0c2e40396100340c8200b81c0320901c0030380b51003900150321303a444115040041e482c0340c480c24103075004030300e24030f00440d030588150f08034448590b46400c50448160740401803011407c08104041c018803140a82500d40650f54500606417074000c0c04200815800203807000c00d1520802140c130f410344e0498128180642c1d200d2004c0e40e580300600c00c0640202c803c020001d0510700142c00720f28040400c0c0b04140c50561044c00ca000103009041c030701c13012407c80c41d1056020031000d20512000e0b10300380e00209250a42d40c103110380380660b06c40e108050044e403140280041070b01d03034116035890200c0c0c43c1d0100f442045441d100503070303403a802c442817400d074904540010118000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 724691537 1250 724690287 724690301
    0xb1003050f070f0603050709120c0306020f0702010323041b0e0c2802030904181a0f090105012102010c0516090b0103090203120306120d05070b011508010315110409 72
    0x183e000a000d950346000960589001719041d001040c0d02140030800c1440d13840d520f15240303200300c02c1030007a55100d660300e100f207811066007903030040c0003c2200411542c05200385000e55440084980e140f10302145011000100104020203801c1e542c07440e101070380012100240034142d2400c0300000da140401c0b0600030342d00440c0c88000514920380c05100c0d20007110718409203070040381d4091407504404905103c0074015900c00c01c02d02e82103055a1402107035560318140403401410800c407550303007400e40300b5981c84840500201c0d102e03407501004104080000d51941d0001e03050001102d00d2190500058680905c2d2134000703000d5008500c0d58400b07076442c030107072001556040d107802c02403141c1240045003101c0d60b113040250150301c4803121094034a0713050065030b88000000c00c030303018410380e250780103052420170300d05030000c2140070605404100c3e444071103501409013144130f40b000140da98001400c12006101c0604006084081c0c035034582c04981000c1000d42680c8519a603d560791501d8100034092 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 724692787 1250 724691537 724691549
    0x903150212060603040b07032c0609011514040513080d0c0807031104050f03031605061e040f0210050904060303230406020a110a0306140a15050d0b1003050f07 70
    0x880c0300015220b2400f8030035240110b4118040c201640d031138080c150700900007440c03416010200b0002d2102800358150100202842e00700181100d4205100c03401d007900d8440503001c1c0545005001030101120042061000711001c5502042544418040720f45001401301c010703120920014a03e0f0700f400054122003076298803a074030205d955450741001c50450718801c2ea00381d00c1b4002001b041100d4585400c1c0a00450801819a032918241190649010300540b100322038a410907403c02c03100e0148004c0c01020f040141d4031500803072500d640d40c2c0f54808103542d002486482000f1f9108040f92150007a100140805041003140c151a8100600119206001040b039010030001804000c0e03d0720096504582c1036800405242980ba80c0c0e851a03042d61000d0103810046291001000c219240280d60400480d1a2860024204410034900360348100c503184142c1c51400d60100f00540f01c0360644c1c542d1603081168441142ca0740141411603054640c4003403d10310070410f0034180500c000c5261012680 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 724694037 1250 724692787 724692817
    0x1e02030c0a171009091403030414010501060f05090112060e1302091003020d020127060e010f110d0e0303090d11030609010c39050706030b090c0f070309031502 70
    0x200884122020300b1084071001a840b42c0c90341d041218103807507085919034034841c00181e01003111800d01d56245810032142a43c01e0540809015998142071240e0b901411061400944600712460b015009106140d00360b410030402064000c0700f02036960040010300303640464444141080e0703c1c1402450030040f400d034403681221003c00c51181d81010510308a9a01505418035003000c0d03001910782c0058105400204103480074180c500841810006c0c02900300360311590310a401d0a80010202c1150040f54000d1198401d6020103010f400a0407080001c407503d05a80840e0f0349402003401d501030f840900c0d0f00706c040c0310701d42c1d020098411200b001d03c0e4015001c940443d612050001d00340c41c2c1040420003c40c81030039000b01c4141c03000d001c040c0c10a100001460b8800030324015100120503901c000d580383d8100b003100b404501c0d418080c09520704021983c449150400145c1d802091150b0710541540ca50700003a40c000300341c010240d000056400c041c2051030081505144000780d0f20104014070585 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 724695287 1250 724694037 724694057
    0x8090109060905090c0f07080a0c03090602010c020c040e0703020607050705090f070c020103090201030b03061608090f061815130c090908030a0e0f030a020708011d0a061e02030c0a 79
    0x30b0b1080303a0220072a0801001192981c41d10654142e41c1d03170040014045141040003004e021035a03100c02030401600a55449205000c0780c2001460159150400d8046906010409120302c1d80012031030369014045800003561034100c841c0514006445d48025040b14010070007805001004c07a02100700c41c001d0f60864865a50b240c090400e400d000c65261011510078641c03030015510035840001b0740352043c140041d81c6d00b48000000c3c64500c0c2240e01105044203882a40213950303000308810f4000d20150f0080c030982c0303843d007901ca07100c2c0384c028101d00f121409444000c4100200b00f100895640643d844c400050030403194044c4040030030701043d0382c0d01407001c130006951483c51041c01c2031075401c5070f809420764a07000e82210281c5109000301c01940f046c9500031140703102c00d00c0182421f4140d5001865500e280050b103509517001e08008500700349500d120204503400c08103544440b150b01c20b6001419a4881d40c05020344003865484a050a2002c002c0103840c1c0c20440060010785140d07100c00d100c0d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 724696537 1250 724695287 724695299
    0x309150d15030f0f0c0509040b04030e120d050d200c07080a080a12090c080114180a030c1511041e031709040902060a03320f06030c03010908090109 65
    0x40c01ca2000501100d0844080400318401d00294507411784100504031000786d881000841072070084d036068445800c1d0600f0300080503002060404510741c00d0354013401c4a180c00c0441521683c4c0c0410346070501c100020340001d0110b1562051341d61110000c10f41c5078696040099074129008902080c11a2140360340106e007004000075550041c651021020745800ca204801710707011007103004551180707901c0741e192400180d01d41c0601c0c130140004000000c0c818801814400c0c400c40b000c0c000c507803c410440b00215a691010400300d82030b5401d0700f8040c3d162803c41c500b03034616800038039403668800e24080320500001c800c0c0c0001c108844001c40111381829a4040d00314080740c40e8480141005215100301030020154000b61121805c020400202c1c844542c01161440d404425050006a59220140c0c0c002d44004402240440c210240c02140420002a810354080c00b8110047d0ba0001900240460f5820048210850006002440060210301d40b42003180c201d0035860f40411034a400104031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 724697787 1250 724696537 724696571
    0x1020d051b120109020a110d12060e01050904031b0c1202010f0509090103020f061e09031204061704141006030308090a0c050d03260402040f050c1b0309150d 69
    0x380d074402c40e0184443d920b00380f20440254442c0200c4001d0080c46080d40300d40643c00c1c01090703810980c1c6c0e01e941c0c0390313600030714031b0300c02111181e0304500410340d117001c0103102d0794131440031155006902d070420300e4024004522207001200361500040020103d4a0082190104074094800c40c52003071300c030a4503070054101d040d502e90082c0325041d13800211440040015181012000030f03240030182295180c07150b1103034185000029003c04d10101100003420018500b0200308542142188203c014200f07820500010844c48002d50b2004603080c0840124052010003003090400300080000c031000840c0d4103882e000545000e02c03003a80130411500000385100b001142500baa40e60110582e198030741070070100804600c41e0002034003002443e41c2420650004118002e03140010b07044100901e140910401003552003032082c2891543c140303020703c511655010280c0700b5001a40c000140785030072440210b4558001c82080d1a030240d146014071a40c2e1040000a029048250905000c0c0c91090380c060340c3c13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 724699037 1250 724697787 724697797
    0x7020f0622180c171f081608031641071a0f0c0f0706110f0a2f090a020901082512060f0905092406011b020301020d051b 53
    0x208243c08911046825460f4099520400f15201e1340340c07070039680410500048050301b081c100c59210381002e0031b1001c005181c1c00001d0a25600851400034643d61081300c9000d0040001e1503c2c410000110001c020a125403081701d10500900c0d48001c1451411040c4400114401307449018145000c549680420803660120b4000401c051030909400d4012000758886400d00840e40038007402810038400c188064001400d0940d20f0740b8150440268060401c084c440d800a0158490359411000402c0017200e42103581160301e11640164000101d0304c5188491004d0903400308244081111549403a03001c0d1268003801e0788c40c41b91907951000302401043c1c0c80f02000c14003104590303003c07000314070848440c0d060f000810f81c0410125955030301c000c00300c00c00303400c01c61030186c51300100042e9034001c004400c4d030000d00240c0d00c805400701003000e0340304081c0980981e0402c58030101015513413a108100c680c0241d40a0001c540d9060361500c1c980081100395250070900003003221241500b001d00b001d8503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 724700287 1250 724699037 724699061
    0x2001020d1a18040c060c05010603050a03090305070f081b1215011a0c03030a0902180705040e060f1008091f0902010f0224060d05060a1b030606020307020f062218 71
    0x4400d60b405d00d40107941d806681401120550340303480700407000400c2800200542e80c42621414111030843c9059818424203801503c035650702801e0400400710001440e100002e070036600305c82640398000c0400c101442a0000d20424401c2c03d11000701d5420744203115048541101101c00045c9050b10094002d104006030916541e00a00c00300d02200810350260408a1009108483c5401120b503802e008c0c1c6070413588a4041240841e0070021400e080301c0c441d602c8103084450100d200307000e41c000340414007409080402c015020340003410701182041130381c03040961041c0c50b0301c0090b0a0b1401c01c4c040d20020004a00042050100900c1725000060844c0381d00e954800b1035840035030741103a00e50382400c01040c50707074049040f40340d400120320240401405880c860001181d4144542c0d03403450485440c1503124105850300800300a0983c2c0401610f03101a030440d00d1400d650400d400003482400788111003141507016070b0307400300e10300031702d0103284215a400c000c0100d0030700c1108844811240801c50721 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 724701537 1250 724700287 724700303
    0xf0a06150e0a11041a03070e04110706090c080102040801020d0605060f04030b06010512070c0314030c0714010b060f0c19020a03020d0212031305031501062001020d1a1804 75
    0x440e40b44845600003010703286004100c94101075a4940708a90340f2900c581d510000400002070105e2564007850741e400c2840151000d00100001ca0582e0b0000e11400f00043c0c9000e680300c4e900020407441142e240010111000255190b64403411014000e52010350398191052401e5800625800c100e0142c0784104902d4103418200b92450700c5261801900800250400200300300c1c89444140d044038603401044956911514000b080c40c0181c500d0744608400303d07403040d0500030000e01c0300340c003000c88107c16401460492514048000f46001d0298140c00c1544590b000c2028800c6000c840c0c0a0555100f000044070312074001a10024461840c0a1002e034200040f24000d02c0941440d020b8035030910710140066440011429020341590455465068003002c1e81038100300a00d01040400402d80a40300f03401c5180d494108003402184880f02450141000e803850030300b1444003036040d0340200d4a01ca42c00c2c898074900c48902000700d042c080c0c01500c5010000c84140c01e54000301c40c2d044c131642c1c1c0a052 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 724702787 1250 724701537 724701541
    0x1805160207030813030b0a141b03180c060c0312010b03040213020711090a0507030b040203192406120e0c0924040207080901080601111b0604080f0a06150e 68
    0x1a00f8040e03440261110300d00c3c0e840f407030300000242102c007145120b0b0000d9200019640e520f0041c1c03d0400c0800b42c05101603c90b000020f50380012020112034211028110019480282c240c1490400105400ca90350102c404600d407070149001000a1480803400c84403400e4582c0c0f2000e4440040c00203640c060340009054103001e8139000f00313034014a80603000d1a0702c03260b048440300004010078811505640410f468030309002440743c150042c0010f0020444043d4114503107403003400c5010a03001c2c0d595041039110320a5441070300801c038200b0101143c250b20300d45002c0d241c14000d0300428400750301e1100a07181034004102180c011a444195481c003c05a200588960800c0e4070720034028031b0040c00d40103400c8040360392992144002d1421a10503404a40c039141c400d00050154000180b20340d0610060044141d09054003280d042c0c5060644c1c92465401117022000c41c103940140d402038651403041006044407824002022458540700e4001031010b44001680b01d80040200d00c0780101641c00000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 724704037 1250 724702787 724702793
    0x9080c060906070207090f0b04180209062d01030b03030f030403080105060304200a05040c030902040b040605130e1509150601180605031b030c04031b05060d0b0103090c180516020703 80
    0x4002100203003c080841c0c48c10b400c60016040f02d940d0001d101c1d01d1401c800d0ba0100718204840381c15400a801c48828a08840d245c203a942400c64551a038901c2c1905c030403d115031a80203070701440d0400e1015080741d480360700c18445810141e10030303174081e008100030000000d590f207466400c07a07120f26441005c2c0410840f03d81a40e0901a845000031070740540550ba011a413501d0310301c944e8521456680e404502c441e128010710088031400305407980920f040503c1130245485030b0700c0c1c1c080b030005d03218400a40d010542c0601410154a2550351244005c02c0c01409800f20000a0201e0f610703441d4000900142c85400054501101c401c004050459003100200401801680596401210340900892540e190300d11242540c2c0201d44902100e1400b0800344240700490390810301a100c05d01011510f00d04100000d6080d000c1c00c005031000c0c0e40c507000d01d880140d2103500404075495124880b941e402d504c1d80c0c80e044049c400b4040c00400e0f41c0c5002e0014081d00800500042003400503000750030280d003591 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 724705287 1250 724704037 724704041
    0x2011b060905100f05060303070201020a150b060d0b1003050907150c170a090b0906041401030b03070906080d0201090b0f25030603060b010809070b0c0c0409080c06090607020709 78
    0x44410380d0129621001e08000c6402440401c0c0d10802c00d020025a52180300611401c49101801c1c1d107000f54400d000501c0140d80001d0034002e2140c00240e20350031112803058101c007030300841c4120b80e0424008503c005850351030b07820400e080c0004407400002c03105144400c80c100c540032508140c0d141d0103001d0411800b94032140350041c03a210303460404408001510340920604c00e10a000304403030000680b0052466001d62800d010381090b91610b031902e150303200003030514002d90050f500840c44004407141e103607009500208400b500030f410394110a90b9201114018445481201c18034001d08402040d40c600c10320803130000c80d42c440355800c0c4940b03c4458440340034000410200c010f4002c0d215800c401d0700c0300c085503d00243c40744d81c007190541c25481c0110543d0702e140003060600038003405000d040345002c20f058080d00d0701200301d107841e01040d543e82031401c1c0102103001d400a240815010074031901780018082c2074220b08c116103240c2c640404440c0e03100d00031500080144c1040e00c0c1400b078030290f5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 724706537 1250 724705287 724705337
    0xd0b1e090c0901020c1203120c0a0c03030209120a060b03120c030f030406091e0c0f0305030d091502040915120209070f050909150a06031a040e0709052707030201 71
    0x1031040b290700f0791708580861a42e00941107045035640c00403d0340d440100049860f10350001c010031405040414995010f884144491801802e05401180b0001c05440300300f40c10b080101c2aa04032601c040050030800c0c011b011710610140640100d12400755030808407412030b0314100d90440110320703044403420410020742000c1c004440603910ba000b6000882c00d039000c800c00385c05104062400d105024601001c01003000d51102003182e200c1c071410404200c1c080180d030141100e00002040100081c43c2594585c1e50031151908910702c042030114060701c80d0b900c50202540340340c22100c03d180c0c0780d03640e0088003440c01c0002988482d07803500050465100304000115500e20342000c1d402c0c0707110100003e40803241151020351840350510070f11034070f2030500c4140c802446035040401c081c0c8402e50240e056040081899405241c0798020340e8159041000728000070034201c0030400030390400502502c12001c89030036031541650040701002042714080703030440859030f0584466130010b041c0c8071020154407034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 724707787 1250 724706537 724706539
    0x70c080708040b03090f1c090e0718090b12010204120f03030e0a03030504030e010c1e020607061404030f0810090e010b04060b03161b031110020d0b1e090c09 69
    0x100b0b010000d003d0000310041d50248250030050144032481e014400c0c580381d100b00914080b203041c5c00700d5081440d08450200d090310042011070010307030344100054800f000038038112103c544030001c0c0020404070780c1d03011101d0204110b8203006c2091141c1a000d0907030040b070117010003544500c4000e0001a5040140d07070f0b0443d10034280070601c11007043d551420f26079004419400b190320f500c01c00007010360020211350304d4a802d00f00f070001400c1c0d54580714a01c25400303090031940408000d41030150b41d1400c06441c0316590001d4103000782c02c283e50b20386114000c2550120042110003014020440c0180745c607501ca600840c208450071850030380e015000e002d9890200c2c1e40c5558902d8076a0483d00c0e98001c42c0094103070101e40b240d8a040080e540079061100040010400c0100300560401510b1240182c0409800d850551201e0035043c102c5e078140303070981c2161409a1320000c1c07a4900c0a03903d4106500b0190f00711140e215122410092030420303e1000c0140d544001a038000076003d040342c002400c02d8a04c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 724709037 1250 724707787 724707803
    0x302030d0324090b04180b040201111213061701080303070e0d080d05010303080a060b0f07020616030e090a0c051b07081b030c03010b01120507020a0c1706070305070c0807 75
    0x2c2e05100d180d40c0501e500328142464a07040b01e00c1442c100340c000e00d90a00d60500c0d0f8540080304540b61660090f401400090420200f00101421b041c820441d501c5051070340c4150946c1d03200c40b460074000d41c084900c20b100c08030321000050b9076409204114607048865000c055441d69a0382c8100300d80310b0905005140e4040f01140304040410b550700050702200d1078014001445504504000d4400c1e8001082c4905103400c01d0740a10003098401e054a0903200c91050f107075102c1d41c00f440080d255000d8601030141c02c00d980e403d0a4241944510310ba015024259070500700c5456841400003a503006075a00d601290082000030b50080012190382603944005003600c0e110784d12000c50509103100d0b03000b452000961603413602d0740e42c6028001c1d5806514214003c21a009860001070842d1003815002c1101945d18000203a000d80240b10482c400745d4031082200401d620303415049140b0415060b628484e109840004041d94043e1085c1d50255031280c8400745d2003d03c03139480310602d81c402001110a92 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 724710287 1250 724709037 724709081
    0xe0912041e1205030307080a0b130b1309050a120302130e040512040f06030f0207230a0b040605071209080301092301090905120a08060409050102071b0914010302030d03 74
    0x41800301c58840040c3c414000742d540e0f401c0c0407000a004003409403146c02c030545450301c2c1c01019036402445081d020b0081030080750310180c1000040c1c403005401c58014040d81407110301d804100c008034442207424861041c2c004a09031218044049000d800c00510801c0c028140c01e004524001c00c000c0d902600ca44100d0f40e6021141200307460302e0308558448400300b41c54803024007a198043c094494074a030b0b408001c508040f0541c03100301a4084584a05612082e9401d4015404005200d04070203103410042c481d03000d00f414900701c0014882100e0450005410051203001c02d002e5000300c40c0301a40040035542142d0900c169074004000390305e0842c411002e244010310300c1000342c845542c02015603882c00500c1c0e44080c1480d50806821440780c200c0c51208006200d0b1040e00209400c0c0c01810941d4000b840045900d045402881020b0000e0480e49043c20b81d80c10410951448500fa10121101404200242c10042110140a000081d410380111601c001c690740320303078010907540764503484203d404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 724711537 1250 724710287 724710299
    0x26060603060114071208100605030c0409091509260a1d0402160b07080f0c03010b0708091306080c010309030e060304020f0a0905160c05030a0c2301060e0912041e 71
    0x905c8115015401061820782040444241000600c0080c81c0c40e082c45031442c50602c18460b8644218064600420340d01d082c11008d01c85402d4980e002201038010410040c1c41a0800e05c0d0000108200038200c01240094542c4180c16030307042e40c0d981d40094440c6004001716a03c50454040d00940c49908035500b4820807041204c1030245806103030050b4140d049a0038a2040145010401070400756003c0101e800c2c401141c0c0c106003264111004400c1142d111603051604802600c40c0c806059444500b07150000b0309121994030a07003c841602c01128103279440c071401036064034801140500810210f055008182c2040c00055601610042444240c00c2c81c060000c0c0e6026440d811440409580307604100f40f29918542078506102141492090340d000303035880b19603d1040344480010000708034100070402c03100f100042c041d09080001400d0120300810024000e00d103611071078040c0100b81c004180c2c41c0c1804070301d010714008068525440c003400c07c0c81300902200994900860314044200000728 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 724712787 1250 724711537 724711553
    0x3061e020f092e20030306180a06030804090b0a05030c030d0302070f060c1106070c0f030c0c081b091f1e0b0a03060302090609060a23102606060306011407 68
    0x1c01156482c0d6200440e584900c00c0c0c140e14281c0d0a0b8485503104105000281e0381c1e0b44501100281015084410b40e940c9e0302c180400f5080700e0340024850100400e010400751120340000e0034411007600c644010960f104100b559800c09140300d01c8d01900101d0130800c003588250000e0040c4d50041c10341c148041075603a80c40c3c017100e5150000354000b40458941c084001410b10000303403c070b015450415500c5100740c66665120400000c001d0502540103802c80401c61000311120080c1060b2040d00d070814405400c040d61628907803090740c4540314640000b031082640b1928401c0c0c1106c103115003c6040d09109040701c000344602e141c94410400c800380020380c840e10780018014281d90ba903020078603d1842c41400f4070301101404e8584502d08106c208900e90f195014028120340381610141c1010f403000c03c20040c00a080005244c21206601c0000485078002c01d9443e440001d508100705404c03e43c2203010300c40101528a03aa01990401c013107030322580714440c5490082031038000c140c5020260742c1d8980d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 724714037 1250 724712787 724712869
    0xf010507080c280c03092702030703090506010305030a0f021501170a05061e07031e1508030408030316090b040302220203130b0703020f091c0c03061e020f09 69
    0x10004a0703d031405004c050f40515500010301c83c401c2e02c07d441c0f900d002c2c881d10f10307000d848200780b0031641d0220001c0c480a109401514100b80c00400341e40c05543c607418020307225404585800d000c62035070001400c4041c07000811a05101c040401c001c00303a400d000500f05080d16030301c41c901c0d0798400c1c18044004078500b800b42c00c0c02410440411441c5440e0401901481a0010a00820301d031402c2d18035401c21088003c5401407000c1e0010005007600c03e42485010200310740c008040f207100124001c1481c400000081d03004000c100140c809299003040700700c442d00540d028000420000703003c1000103041a0400e422030f2282042000c2740c00450000540c1260421200072170004050b01c06c000600c003007604407503002502d5250651501000d00b80601c6a44140c0c0740403801011000c100e168080d068400d02103825900100c0c0023003041d640d080c01da000c0c1c6814a440c0051419100034070200f14454401c6895112030051040d050a6483c002c0000340400d4840c01412182980203010412003031071703c401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 724715287 1250 724714037 724714117
    0xf0201020f1615110a03030504021f110c03010b01120207030207050d080a090f0614030901020906070b0103110306072709020c070f0e0c03011a120a0b030f010507080c 73
    0x404800c0c0340c001030b040c0c220450fa0420f81400101c0d04400401d41010484a0038940c060401103016156817000c2211641450501003a03401e0400034000a19800000d8200d022400170440b542400900101400c0700c4000c6240d902203510401340c0007456442e40c010303043d0300340030f80144c6514a40d502c0104103003202d501e0040b11288000200081c1a64001c2480b01c040c3c83c0c04500b6820b003504155015120f8111400e08000c0d0f401c0102c001219030360250101c801c1d000d40901415103842c114a0201000c40d000c0c04200c1c2c6504801c0c2d0520500c0c200021031521510003695440d03060102c1d445e40300d490240c0794101024418602101280c004014002404402d08120041009902d008400c440a00341c83c2c0200c85d050000100b0320040e00c81c20019213041d2595200410900d03108450300072400d100d90b000132605d9210300f00c00c019810046a2000d4050401078041d18094403040059a003294400c68148011425039004a40315031400006000702e2518980401001c4010f21241454465031903152 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 724716537 1250 724715287 724715323
    0x40305090901151d28090911031207052a0d0503130503122b0510090c020f07090506010c060518010b0a140f04110c0c0102010c09060c0f0201020f 64
    0x403902940c00042e0b030b802644c541000800500c00300c80001d8491402c01d80030350544c0c030300d0f05800b40039240d0080890700600001904004904051600c0803031a0244044240b10b4011546c2c8100240749110444941d50b50000c00740204417040b21618840080360002e030700300411007000e89072a80d12030003107498503903001c0c030000c5444184e01c0300125280501c98112034000d1b0403056040c0e550340080300c1581c5440100b0400210000042c071241400c0f030580b44144c0d4107190810040c418a48040341980040c0d07403d041042c06400f032110002c0e42d49114503001c1000d26881b4a00130080958158005074100805152604c00d03075181d5110441518400e0f1100c56009681c121402d030594401d125101a1410035a042a8028a800414160302e100080030344e018141c000c062500964a5034003410500800000041d10366091580c074581d1075410800b150301640c070300009240594041d404620854526a0307072141044000e603110829101241000ca05512842c910090045801e00410505180120740c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 724717787 1250 724716537 724716569
    0x150604020304080c1b0405070311091215010314070603020f120a020c15090c10091e0306061404200409090f3810060c0f0510140109150e040305090901 66
    0x8010403a400070b0a541c0c227141c5003070000101c242a1000780e4010b07201c111907003036204040549440c1404460440b258442428400120800804a00c20340c0c48508800440c0c03500c2c0c2d150b801c240e080344110714404118510500801a540004450140e0b018220000141c180340400c41010f03e003103201d00d0f1600140c1e50910801640b40400c0080d031100784000c9602c0041200c02d080c01421019141c0034201908105007059064006d20030052001190301c22001c201c200da41e44002c107500c1c2c0500000314130850414485c01c0c41c1450381102c007480c0e804199070a03860249015a01801040381031070032600111a5480c14002c200420f22541e0030700941090040c42c2040c070300c2201c00c0301d462880840c1651002800340179141601e07025007810340d1124240302c3d080e2126410100070a00100100401034429002a8645540160041d01c503c0b404106c0d0001666281c3c58400155081030703641d440c001809410401440a0b0410b050f40c005010741000c0c3e00c1c002e04840400e4a40000740c02030369208001e410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 724719037 1250 724717787 724717789
    0x90d14070b120a060501051603020f15010e06010804171e16031b050d0e01120e0f011a1521010e06130203100501051b0708010b01020f150604020304080c1b 68
    0xc051603020f040103600b0404a403e040020381240030b0000282c1042c0404404501018001c00007140c03040301c3e1608441403090224903c2c00320010901540001c0c0304100f01055495024003640d5001d01d5126203086c8401d00b05408510032504041007401c0e00f00040c26603d58400102001800c040d83c2552440720441c0c05030a0251081c4100c00d21a030803401458556404160081082d4540700b81901e03142062440280c0126000c81501c0301e0255114507103482c803a98080c0020748401d1035501075009116016446241e80110300d040480c054103c200c458104411100810041c0030f4009411807511055190240c078444020007601b028044000b42c50900c16186481c50b101800035103034402c1580b46107414a20f90010701d07030500c01d4605100740820240c00004810b80d500d2040600e04044802060f654000380d40a003c0d0340100e0f40c00342c040e11401c00c09500340410302c82c44802860a032034070141c51310000e010080d8402041500c445d142440004c2601400f0b000102e441082900c1c8003c40003c508 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724720287 1250 724719037 724719067
    0x10201615080105150405030d0804021009030c2d031a0c030c1803010e03160c060c03050a051305040c0c150203060a03060b03010b0d0f15020f090d14070b 67
    0x240003029519400400248415400a4100e05444096854119030140100316240c94091a008564140500103682d003816030b214207038511650088030350300969628600280d078041f24600000d043c60310700c0d040600540c481141d04540084500c90050030740148414a6441e0522580007101d1507041d42d9051410000104e801c145c004000042c1c2d2803450504400501c1d6501c601e21004500c103402010000040c0c1e429841042c07100c08050a41c1d40c0c0300100201803e1651911208445042c00038202040d054442c940078200b043d4581c0340d1901d07090300003409445540140310f01c0c000010305040701081613200d0b070003011b80c01c1866440c0c0959800c0185050302031103152114545e24648184100251551101e40c0d00b4101ca4104c01e002420030f6803400400d0160610075603242c4c200c600c8441013400c000c00384501c9142d0500414035000c0000e13402c0c11010580c403a10745000d512010034400c1d4840c5151482485620a00c5201c0910050b0448c00220342807101c42da1100d00038150100320742240904c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724721537 1250 724720287 724720289
    0xa120c0c05040c0f0f2a031101090218104208150d0c060c02090702010c020606130905070905060f04061a030603100e0c130b0f102016 59
    0x8642c18092112081001001c00c54a0200c050030400210102e44406001d45015000900500c01310040c04c4030580310441c01083c1254103c1c0010003071a03201084100600c10b05502641c02082c1c000d0201c0c9916280c0d120030b501401c4c007000b80c6202003002503c12050603803840c0c005c010310001414a80c1502a0b200c607042091254a154600c50b0f6000d1740c5641c1c4519941d078070405249211541103040000b040c040402e01000808a880c940f10102c2c2280e0007092030041d00c0d108039a1700c4401d90b103000040303003602c804c040d0030b0740581d10501c081640d43c038000204407884000a400010700106607294546010429480f080c0050303035450600c00f4a00309207800c0702c2100785c01d03039091008074500b168480f03c18040c08180801000c001c0b0101e8480d980c14082090500c5a03d002848100c494040d12070f00c49003103401c0a4411001045106d561041c03a01404900040092000020300b59003014811b0707080350b02c0240c1c810401e680c012000f041c1e02c81e9115801c4442800024840950300003111142e64000d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724722787 1250 724721537 724721539
    0x11b03030b1e031507020c04060306020712180e0417130503190b150a080706050901080114010507060504080d0e06060a0f050a03110105120a020c1b1509030a120c0c05 73
    0x600410501c546001400740e20b0300350b2100580e201303656101c90480c03c0c514803002ca075500c02c0c20800008144009a0003400c0700d5401031081c10303405611318209840d0f184045079000d010405007a02001b000300c2980d0b040364468001e4103441e0005c07901864004803a403141d03160402000e44004140004e04003005100c58410480041031945003094940c42c005103002008800090380051285085480740d04010380100305500c2100c142c141c4414002c3c105401074443e0900260140d000020400074002a01506c0d48044c0c60b00f52078070889489100140070010810303030321124200414541ca4009100b0f540140c1c400b24050209420081c081000d001040d900c0304848440b0004180126910074550070203da5000f80094000070000300141c2d10b03030185661120303010350f03001c0400440c8070068005003601c24642003641d400c00e4400242c18803031003140d04201d41081c907407440704c015000c1c5200140810100101261043d4049507900315000703400b4401c410008041070a0030b000c025500f6000009000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724724037 1250 724722787 724722829
    0x91c0206090a0228060f080901020a05090402031807180b0604080d051b0624091603021303140115060809060402272703160f02011b03030b 61
    0x1004040030350b0356890302401900c11988000c80481e210030404240b1800550b06034013202680c0c0da03038006008400b580408001040447d8001074403400d042c42107558002403900c40e5818180301070240700007904020014034180406c40200070152004002031001014034101c0c401e2215040c10301c1c80182c90051001c10b01640040c001408075550120300c05c582d00c030b06858603035202c8101c03500040045802d05000e000c140110002d20030306081c0c00084440761600b4ac1c0d4042ca0000c0d18400b88412048120b0f81030400560854415019903c00c0e00205110050301d204034203004c0e00e9440e164400d0b600e0740b1003000c036a07640f2200f14401400080a06006104034105030702c01380f07000110075072980d0340204020f110314210740c43c10721300029220b400e851041002d4074a190619000051076885250740901002c0281030000092248100104942c45011041401100c0400d20f0342c48403c92001d1a2040741880f00314084181e00d104110352103042c0600950b00496154081420301490f03140f900c44411402c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724725287 1250 724724037 724724041
    0x60102030c122d0a0318211707020c0f030c030105010e0105040e03040f050603220510050c04080a020613030506101e0608040b0403031e0618060f0303050f0f03091c0206 74
    0x418030200313990004041c2e00b0701041c40030018031060f0100700d013810f00034035498055541d451080100203560410a1081e25981c5607140d003100c10554003241110b02d403006a00c00101c0428504240182070036820f03003d401c41c0d0300700d090352002a0039140c098000c504400c035507038010042e92826020301c9045d4201503015610340f50601002000340e043c14011b041c090100003010600a58030aa2481088a110403011151925074a041078075441d0790000d100c070281c10320340410300c80b604802c101d4080f11690b01c010321010f00e055090007640c0c1c02c078000381140c0104203c0000003207501440340602c1002403400107400b5904020712041516000000940181da410100b806907d4100010716006904044048540d5417603140440c05810540403400100000044c220040c140c00d81148090b50862451512042d254051410403074603a44940d030403044081d0b00c01c00120b03000d44000d2001c2c040c42c0040525084041001c607009034030980e031641c601e901c00080144040c00c6203122080030342451004d0f002d28 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724726537 1250 724725287 724725367
    0x1060509010c11060d090302151f170304080d020f281e050f100609050403141c15030204050a0c0e040c020c040e0c100c02090f060102030c12 62
    0x81030003003000070141c50600c09001038540c0c4d00c500340c403030400c90b800e030522501e08146002074403450f101001546042150700030400c0300d00e944a0780d40203135104012a00385985007181c4401d04007941400029507002c00c10011402c40341c20301484c1c1078801c1c280c0042c800d10807169022071800f10100d51281140600407200240c152005140c4e108298000107402800c40000071003d680b03110200c4028031078072400311028001c01c0d010541905800425108105903641c825111042c2c5104550043c0010708040642d000c01c0c02007405000141c000200040000000a0108048030703510f8041721a01c5c002d91902300110310345030280540c003a50f0100c00b8046c9d240b20203405400a045040107074440e03902c815a2070f4000380b080188418034140100140940c030307007151302941c41d441c103400c0d014014031466008505403409509009030850b0301600c001c1c1c4a80e0303100045071809001410302c5045000800c61006070a0041110141203007078506c0240e0b4840950080210390300c3e01c2150612089041c0c0070300d10607 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724727787 1250 724726537 724726547
    0x11091e090f15040b040e01060602010606032703050c16240219060b01030902040203040c080115030533100f05030d02150a0b120303010905010902091c03020c060a050c060106050901 79
    0xc81c030090f03d01003000214000040d015107000d280c0a4440e62912900003901076054010300106c0b42c054070104603111070803041c03481c0408064030b620000103000070300340000b0703100d5001007040244440507503078084501e140141200100398010352040004048040c0032110b034050140d0f55054034001051a044003010b01e91b2401d42c040009044140d40d0701848949900a411001e0031541c000c20440d664030b00307032038406540c0c000c600815070380b58030340001449080b001301140303001e0342d4200004007507841044e01c80c64000d00340800220800c1804039000c0c24201c12162449005040505954044500307014107080140410b904c8a440380d44404020302980d41c01103244041c4510380d15803c00c440d503c490a6101400107a004c1541204800443c0d00324000044041c5068070354003c1c091040d42da0b541801800c0c0d01070b0b0f410182e070020103100005140c10344055280030452107801910440300c61400024800d0b0000b8021601084000901400f140000e004540c00342c601c0e03040003800d04c42282d0000301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724729037 1250 724727787 724727821
    0x20c01170424020d050a060b0f0301180603021806010e010311040506070c080f100e0106031113060b031503160b040b0d09050d03020403151b0311091e090f 68
    0x142007507860034a25110a445001418000040c2c0540d070b00d005900601c0c0040c0300860710610a00d1038a00702180b024540400c40b030360106040f400504507420a8a444c4e41150b0460030903000b20b80d1a10300000503103454420b80910484030344149118136205001501e102401103030301d41050f1510401503030700d842d90700988094440a0742c03241e89594051030a4124245d840d00321448502c155140440d2450001035850685400102e091000200f01e40780c0c2c500f40c5207540001040d8000840c1920502d080112820551b0303010b00c10081031541d83c0c0c50000e9050740c025148d0300c0c1a03680c40042303e4010709081010078100c503542e403012003d5034908a5603000368042c83c002c1c8030350390500251800505c805500601d03046c41e0003030300342c3e41400f0044070060000e5001e8031085a07250071343c02c1c5451a403d094420204010012520340c8510340c050301c0105c0c014259505040c5508006020243c52a00d5602c1081c1d400c050b00781264481405890400c034503038000900d21f8500341c0d030a1080207050f40c0b01c2d0070442 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724730287 1250 724729037 724729043
    0xf070503070311120124020105090a17070b0c090a0b0304020d020103021605070f0603060501030b0a060323090d0305090d0f03050c04080303250201060f140604051002030406020c011704 81
    0x200e8140003145000988100da44c80200c1070746140011a02c29481c520005460341652031540c03042d0341c00c050a9007a03c0c421201216907805c001442001b0402d041c0b504842038204601251501995035078a0080c1c02c0203807408a0101008140320f41d040c04c1414a10b0060200c100030fa9041d031600754001900101c0c12100241015004a40c0349403c0c482c001506904c2a8801e090b44c0380305072980a20022a071051264200290030500001100e5000e4407aa501090016014844207814a070042e0301401800701e06003a0340e0a2101d02581121004e0321f50b82c0036080b024080c244c00b416150300281550303070282c24401260040c07045590919002030718000103044500300450159140080c8840074091540410001d0000004209204a1a00c6100c60b044400d0100c0c80403445035000886c2262240d00450368140e144003000c0c80051840d0041004203070000708414170309070b2a480402d00b5214004403d2000d81c0c0f0101d07013400804d4060003041141d007000c0c41c00345031980220f14003102a2201070005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724731537 1250 724730287 724730291
    0x30908070e0a0b0f090403020c0f010806010c03030e1f150603180b06040f05040b092e0209060706020703081b09090f070c050d091e0b030c0f300f0705030703 69
    0xf41070241c8602d07842d6921410010030401c4d1034941030801944271807035488814401c407907140b04007083e58011340b030160050006039030f5066140201d07503098005011041102d4014461101800000700000000c3c0300e003442d4079000032030703a401c0cac81500c08008400358100300b081c1410010126281c051003c41c45100c650001c61400c01c40d1224004140104030b481c03071004180d410f0030100300500c000020294007980390081110f154265001c0301e594290341c0ca11144180128083e619202e01d00e9a4003d401e580030700911041c5800883d5441c0c504907030050f0003c5001c60a054100f091120362004074402030080c0520903440c000251000801c203210090601c039449071400302042c444c1c0d118810101c1482d0b80180bc50b900d5218080028040001e1407003841100041201c84034060079109011000f200ca0f08414941161908110010207412000183d03074000c070140b0005a041c1107100c5144100c040007080801c0f8401503800d40301204031b0080c444a0190b5119091266880e800003c42e44c3c018041d07e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724732787 1250 724731537 724731551
    0x50c0403031e0e01231308062a071b0f240c0602032a090a090e0a0314120109140c0a09090213030b09060906090a030e0f04021b0703030908070e0a 64
    0x11681c155175000c509900e000442c42e009a600008081801d0f030703158108560f06551003103080d00c281188240b4814a111892074502200314480d00909070b102d108501c04407400c403036003103510004030740750740680184e2122000400803c0d2105400e04008440c0503c0d150700541d4a201c050080d07011840d00600f040e60000000f22a0700040b00358906040d58039414280b4200c12100858890b04895400c0d4400c0c0c0b1175003000160b8030728600c6950007658040700a4529031065071003e4884140141c1729112072001045417403082c58203200458046d08a8007c006a00e040c00070003080d004400400c80424801c04002c103040e250b4000304d0b01012038451940250381c50260610141d11403800e58030040003423081a060200c6000e0100d030261084000e50126621680c0345000315a403a0300b4144050082000c2d20368410441c01e03d4081100520f0006e0005132600580080601001550040c2c0d10210b812111046c41011740c400007440040c0840d100070099141010441d80d028074028041000c1a5030303400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724734037 1250 724732787 724732817
    0x30705030c2809080705010804080d09080c061510120c030b0414061801030c030b090115080c010806040e0d0e1c0302100501050411030106030b0f04050c0403031e0e01 73
    0x8211104580308803448100300d41d070b40014000008600000c00e0204074503080c08100e4150000d134900407188160b43c2c001e4113031200e80f1542c6603a4072000700e02803101d48604100e0041014030004120040f4030a0082c020f0f45070610f40d0100b022820f070041340c0f04440585c038010115500044040d02c0c01a4043e0014240b148024254020700803030001680050504c092042c01492140040f403003402d0564880001c03ea14201444840d1400d010082c103401141005101003801c82580c540e0103820030000060882400e02e0390380503003a040e44440ea2a40c03140e1101681564884155600034005603020301c0303c0888114601d0f2030b240c2d100107040402140240006080d03603860000c0b587d440145020700582d628a08000b9100e8840303608d500440c80c1460700000700d80c20188244446220340560460440c0d082140c00c4000d0304800180ca81c0c00381350041c13042c490b65907505c5035a006481121299940302d14500e009400c070544e0b030b40c00e000340c0482340c46544031442c1c1040c080c0801440c00d19041c21003116401c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724735287 1250 724734037 724734061
    0x60a080720060c0a170709030b0403020a0b150f010e0901230411040e15030604030507061509021902010204230d0b09010f06080a0c0512010e0109050303041109090303070503 76
    0x1019080c0d05104a0b81407040c198041d070002d1803c0181075444850703481c0602c800910341001502c640b4001124070f5410808110403904a07034001d0710030310542c4c42035405074581001440c03040d514081c0396007a9410701300052400810220060f04282466124059010300040c01c0d81014495041c4500d03000a040c115880f82003080b940c0b90000620401919001c4246000749130490b010b40c4807101c6a072000724109501000b80d05806032401030040034113135035035a4202c40c5038000b2001120f04d80e0301c0b2003814900d2030306103044a02a050310a801600c440020300280b80740b100814407001503920400c003c0c0210b4042e042d400040092034200310400342c3c400e80c0407412810405c6006070184d4042d20070b005079403a04ad00081c45100d14807006204458032541070a0f200c1c04e00c104000e2115076031680401507420400f851001c0861820000245417074401c0143c1d003540c6616500311442d0b00004104001c01100052407454070200756140807081c540035081275a1303840081e1918050040110002d01c240440c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724736537 1250 724735287 724735337
    0x20a170a081602030c03060c19031b020105040b0606160f230703170f09041e0e0c190e0c03060a0302040603030f2304140609060a1d060a0807 62
    0xc0705419a803922031149044051185035802c92281c09040340190080c070700095442d000380f2410061515000340800012200b010040b2500c041c1030701c03207040c0d0030420003a0011120080c8039030004079151405180100480d04000e10480c85041d0520004400f082a46904d554075603111204450000e014180b0184507800d002c11003000c4000b101400c4a265004652007013101d200c1c070045c510b001d54000c084501e90040201e5054182400d020380b014500d0300741c20028120b01f000700140e40c0c00e544c540040064841c84e074095411030744986007a400c0d604102461159074400642d14500e49810000c42090802020f030110f2520f1901001003122070b0385651800008680c0104100310060b034a14000d08081c05804514000c1004042400485403205010b0700302f0b007841500f024980350030840440c25050840001e15002071060050916a460304030007040c083c062030b25840148004010f51005060f00220f40a000d0502403005034451034002c0341082c2c1101890034100204d403417814088440d8220 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724737787 1250 724736537 724736543
    0x80f031c15030f0302100c05120601182603040302150f0d02040e041b081915050a060f06140301030314091035010312111615020a020a170a 61
    0x8078680082007041203e40c000205100b038080d00c1e001c040381c481420440e15070007102d4011400c1000601201c0718054001d1341d101c0c0050500c02e562a086440c540c0000c2101d03081004035000c60b21990b51940504c000803000702030f00500842c90b143c11540410042500204240701054022a8101c5091030b803405844458807100070441d01c65035916544024180195000d9821003028880f030400c1702c2c13002d0b522905031400c8100608000800b0946000001c00001040d5602d4200c5007140f501012580075550049501c000086580350601c60f0b8039180300c0702a4000002c0c401340c0d62001803d06011004d9034116505410020071034001e201c03440d201403140c0101d82e030f030000382180580f9100740c100014158260805503490484a2207482c03041d10711121b074440c41241200d174001000015010520030800010034a401c1d9401050001e04602c2d000695a0703065000c55a071409020039010a214100310b003d2510040c442c604180e00441d1801c034050141c407d1555054400518903027040001d243c0781c581c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724739037 1250 724737787 724737821
    0x3011a070822030602070b010e01060e150a02010f06170c030615061305100c0c05060901080f04081201030b090115050108060f0a1a0706050f0702060f07030902060a1107080f031c 78
    0x1107d19000d104840240240c1c04115140400800c56a1068070049201d2002802c0041c6070705840920003410f40040750004210341d01e81000301e003425240d005400051544011010700060342c41012410310289020660090744614200010011900484141081e040d1241c4e9560034041c948501c100c82e40c0d42002d600060410903481d40d140d07021a4a0b07550070f0150b0240e8261f02d8581b000c1000074895800124006603001d004a40f91502c01190302c2d0f0480c1c46050000e1500100c28000022280c007644156840d0104e48104541008213004826180c05403e10301e0410509050018142001c0507041901548002e5600265a11100301340005420000746100e16402c0b07051504286070f1048100300d5041d030801c000701c0c07410200040c2e40c0707000b104d190300500341d980c4d40e240b0b444d040c4140044c0040200340d2144210300140e10b0310401000b08903c00d0707940c0150141540c0c0307507500c0c3c031020790311500540d400283c0a4121a001100380c40e0742c103a035007011310301c06401400e003540900a0f50785c0248143c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724740287 1250 724739037 724739047
    0xe0127050a020d240e0a0b192c03090114030601090e0112030e060c060612100f241a07050f0106090c020f1212131703011a070822030602 60
    0x1000f90036000c0c2040c10880c2030081e00144c003224200035a01041d0f004611940013258400001d4030711401e16501030541007400e42d00e600d0208610095070307800c4141c0c01114192050ba0030803003440fa060550f038490f401c1c00442ca020602400240030400c014403131000e402002c00424004e80c40303450500c0040070210b40c8040e5950310f8032801c0c4001c40441a084010861511104400342401d8042e2401004140302900e02aa1510240021504240140803030307070150b51a2030a8558041c41415003503204080c0c0054000700d8a0a0160310412103020b040c101100460100880340c07000e90800408108407240a0311901c00d40740062401e00210404032040d401c140b40070840c80e5040e40080780d40312040d0b007190b0510303402c90f40468550a545041a49020b4104441c00f00300c00c0c1c1720f02c6c00e41c00884040002a80c52a2910b43c81d450002e2200c01d591084130001c01003201140d8140d20924050f00380c24014a0010700b50707035500085c0316941401c0190011103048a00c04500700410a0085810500940d030350703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724741537 1250 724740287 724740293
    0x290705010c0315060801030c05100c060c020703110301020903061f050a1202151204020f15130e06040b180405011409060106030c0801120201030905030d110d0e0127050a020d 76
    0x40c0c040150700f24801c41d0b42c81c40010ba90f0b841602403504072030f0441140d00c030250400080c410411400c007260000d00406062243c0007801901c02c01c10500001d60103041210704600d0080388032500e181071a40309070300501c540c0d9410380d0046003035a0003240248080c2c0d20101342c01e0060f01c2801701644550381c485036a10300000c0118100c021500a28400c540f005801101484d000082d80180c2c056100144915800500142001d074017034200c218000b0b040c0d24030740160300394900321940114412051440300c082c0400100498400e030070380000d400c880500c403d040710800310f041e03031400000c08a4101082e20105050180c20350000401c005c0411280d4241d140c0704031425900c3c4020310841c0c000900e00a0000d00792031155842505840fa428400d000c40b91080e00114050034400d40c01740c807a404100401c4640842078440e001307100c1c180e041c1c0700761151030384c01c4004100c07862141d0100076039051040000c01070840ea103003d441c0d9144068038210200c02d50030054513091400c4070080d00b041c1000150024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724742787 1250 724741537 724741541
    0x270a0503101a01050c0613060609050a09150e0d0e0a08010524100f0c03170a0e0c090609010506070f170306031605010206010b2b050601021204290705010c03 69
    0x9600c1100768180b581002d03000111594426040788060a400841c08510f045210420140d51140503100110f003182d1a444440221501540c802c0511035562410000308001404ca0190100082c2002c2100c1c0b10381d60030060322040381000090070061040381c0e0030019640c01950401425003000208218030b0410107003018401050800380c120740305403c17581030528049807200003290310360380c80100c0e000c200c030402c1d41c42c1d61201d28210b0030301c81c2c1860f00009184881e03e410b0710400e44030001180002c81c0505644c1030000c3c82900324015030040041000d140c0703138000150f04503081500d17041d070307aa5642d0500398401c900218008201c80850501303a60020503210142d409a8822001d68003e0750014980200aa0052080a0158110b00010481c000030840070702504a010800508400b03041d001e4580903124040040250382c2d550010301c280b5507810049050b0081440c040540360178108103608001450b2103811855042141c045280602c0507101903e400c954000c00a01c8420760180010b40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724744037 1250 724742787 724742801
    0xb04060314010905070c062a081816031403070602073f11160f0305010e1b040917070b012102090f0c07170301050102060a02270a050310 60
    0x10368041e00c20004074111440740300b910b020300450748030a44c031110305035102000741500b040c000c00c802035402280400d440c0d8075011403400030304076581e0840c00d14125410a00d1218141c0790852143c1c4030402c00c0140c0c1e40007a400c501070341c2d00603c20740b070541304a24013146584145100185240c0c00071401c00c04000034007100c6105030b8941083c00c00185040307807804012200400c584840710080320f1b4086140c0303005d801d5006500968005880b568105042d254800400d1039002030407030844220b0400c244a07081c03191385c0300002202c014010030404059001c0002e40307281611803045980c2c007410010000c20901c007001d4500401821901c40c1003500f01480c07092001d1081c030385c8904009600024080c0305a0416481c0b540c02050780b900e54940c2d8031400044038005001c809100d4040000e28042856200c0300404900b840e400c140d035075030510000a040140107802144894018800140301c035682140400e2070001d02408007030003540e284009440d520503940708607014029825913001044550304004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724745287 1250 724744037 724744061
    0x3040c0f080a0c05040c05070605060f120a050c040501080709052703090907080c1c180b10050102070e2a0a1205101508070e092502012a090b040603 65
    0x303c6042d542c20034001582c14010120740010402c00241d0b000a4650344240c2e040070010340780b42e4241000d9000700d5841c1c1c2c401070000150707a11007109942000410460380282d00c2050314103001c3c0354507101201c2d503148058000c00c000c140e00c500c001015403451108501811451603800502000030891603070320b9501005005028042d4200000c003c18003808126009240c01c1503c41d1402c0742e10042007090018001c42d000204d91940e8900085020300c011141002d030060a003400c1c142816800b80e0a44d820039032290b030554108200800c0b002c080344124541c081407003402c03d910f00e28490103065011803131b9141811b071404080b0300b80300620f60181451203850302038442001184c0380c80c1c1c0e9405e84c0000c18400c3c10075186005008040951064403802e80041d0f450901100880541707000654000d000c4860524000105050441d010500c049032141451580000c01250404081c01d94000c618040c041c281d6000c00e80e8000d00203840f0708803000042c040581096204e5840d110000c0180009000705 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724746537 1250 724745287 724745303
    0x5060708131d090708070b070f050d09051c080a0507050c1906020d030213140a0902070f0210030509070302010e030a050109050609160803040e0a021207030b01020d02011a0603040c0f080a 82
    0x10380d0054000858a060350400c0d402001101c1c9807d900550b1079000400868206108500b02c200141081040a541c5042510350140d1141001d05002502814031a013801c030a04000d50a0003045030b070001c440824030181b400550700c101318207120307141a07501c17980d5079044807035403003501c01e500c1d1310062000554882d60b00751103800d40c0c800400c40c1a40070301e40c2c03507100000e6407100c00c10204c1c9901140705642040508020310040d6a4a5200700301e07008903005035140b051001c400402c40c42e110581d14010025418200154200080550ba42e0751071408024140310028003541c00a55041014882e10742e030000090110300f0540c60003030b49614040e600c0b406d5912034410210f28801d00081da80080d074460100440c01d16260090510703c8000c094241c0c1043d0354204000100810700198162180c3c000351004109038000c00002850114003080f140110b926003030302d07100907240001801c009030034111801d903229216820240000d070002d602a00004e00c040300e00080b03605000c110983d50358024844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724747787 1250 724746537 724746541
    0x1210f0605131413020901151403070f090e0c0304060b030712051b010206091209040921090b09060906030406021306080709060203040e01091e0e161d0105060708131d 73
    0x443e042004480900135440040680140b0445008c42c0100c403010400d03242c0307204210340742100444141e10590f0887c00141c0e40100c0005001d070801c42c42401412080703400442860185100081408060f01c0200110b4a60201c0708159608000d09805000f404103207184000151030709035520780b0302440d11003900e03120341281001580003040d400e20a820143c080c0180000700000400f25510903031480341d016079500c1038100491480400c080240c01c040b11810100052040050010552940100295402081040310a46410060b00c14a85060303800a4a0f03407100c2c42e115000c0d00501000e5061900e800b0b200061641c0e210f01058002d4095484410f2070b141c681c80100d8881c440c40c0540310800d48010010000300c682548400510078501c2c0561a15441c00d022130016513104040d60a0164071071403400717185508252414001784450a440030004d00040d94401400c0014440e032845a040801d805041c02041c0c0d040700e5001c0c0d010714140b44c000b034032280030140da01512205009202c000c440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724749037 1250 724747787 724747801
    0xe0a02060d320f0901140c0a080603060402010212071106030f100905090309090702030d0c050409060501090305060c09220c030b0301150512010e01111801210f06051314 74
    0xd00d03121440c07181d905401903568400c010340840303202804d80c83c0c0c15075852052106840200442c0307030064100200e0141e5500c50300c00010101e0b400686000c6c030913000300040c400180c3e00000c4900c60580d80c0404141c40d0b4802c1e00700822880d14211681da0424000801c2000c072682d55458144603908140445400944810071841180c0003100c1581d07203944104a14606460206407541d480a001e10449144c13401da00c0c0b030b0303409542c10000344034082000446c06024000c0c59010350070190200b1310300102510700d50b844e081d41ea0710020b08000002c0c0030009684a85490300501c2490b00c941803141821050001e0020100400b4211803e600285c681552142c8514040c09031806e1064100d4040c83d029040204010f030310303241d00712240301c50f40d41e03007114081241082c000d0322441814400c1c950703283d003d692020300f0380c080091052410084900c8001c2d09003201c4042c6407040942c0403000080d00c001c812111401003507203070881c9034401058a0400034500c01d81e0031038181c4c46030440030b1100c9030300c9950b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724750287 1250 724749037 724749101
    0x110a050109140a080d0b1203071103010e030a02120a110714040f060b0a08090c040e06100b0a050a050a0513032301060b090d021c08030907270e0a02060d 67
    0x10004c1000034100005a101300441c1c004684c400c4e002403100c0a4480d034003e141c4e07c0c50703025050031500c204464501e00441d1400b80704181007017100b00d000d103181c1208118002e407261241c03481086600c2c004128190340d107104810307450645d10b41c1001c80b05029215440e40301c0500788070214601c0f59081c880304180c1081e01e4010031045804040e481803c1c616800e005840c5030304018102c080500ca54890921141d40b5400703030a60f00070903000030300345030304241b0182c0c40c0e4603101d03030890000c1000400c641d0404543c003d040b540c05022920740f5503210b00c1055000c403014812f03000c1c01c8500720030310030010082c41082003422038400340c030b030140051860752038620703a007070f1641849a661140401c0c00003140d41d00f01841c05c0b46040f07100038201499071241c2110320b0403004440c00103803082da0b008030030400355000400400d000f6026901c0b090400da500381441166541028486154486d2035400310251084108049440303154010078089c4c5a403180402c0c40024600d50200e640505c205030349504100c4a20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724751537 1250 724750287 724750303
    0x90105090c010507030c050a0813180b0d1e020d030e09070306080d14040b0a0807020f0604020d111210020c070b0c070608060303160f020a14130c110a05010914 70
    0x60f1140303410460b55440039584569071541c151414000c000180340003610740c0d002000b10640c0c00350712030016810005603c1031840680b081c1050035140a1410b0066540c07140d041100301c1c0d0200740d2030709411346256108000145040003c0d040f000169101e0101500030082d0306182400791040c580541c0c400c0340450545410b846000d402c1d801c00c0c10f412038000d214110300d11018010080051800340d94038030500d2140d011280305000100c0e44014081115814420222a81140e100034003070b80c1059000111350310300c9500014080c0c00400e0030351915440340c0c120301414000d403030150781104034242c880e24065445884d410b40d06008100700070641400d030000f0b8411482141c002807142500300303c016603e6000260005915120a102c4601600141141c0760300b143d102c2d0000e440d01e42c110f88140001003140303400c209040e04189a1400450316642e550340f44501000070045000c0100e41402d854240403410070700f02c0e034007544003402c0910505401c01703001d840c0300d031410001c160345600c007440e120150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724752787 1250 724751537 724751539
    0x7050a0f03020f09031219050f04180e010f0c020f0703031b08040b0301090603060f140610030e0109080403020306010f0b0f180a141e01020c0111070b04080303090105090c 75
    0x82464080341148680d0160502440816075036142c0410400002d14003c0c600b05d81840217000000c207540e412640102d180822001402c140c0d08203004039500780e446005a009048090411840f07403000c022583e0400000814048020024104110003000250115020020151041d8040c2c0428900005420011a50160348030200500c1c070076000c00c4100040d00c001c0d03034130190034080462088a03640c000c40c0206540400040c05c189545400425182d276074449654280c5001090b050300143c201803a507026004035481c00c0e520072486802d50080141030020b203109e601e890300c01d400f040103690040056038001c500f00c55082e80e23600700c004850007580c0110f8400301010b03c4411200440000a807000044050302042c45410083c00b00d0905400b0394040c071030b1410080c01000c0c003410202500603d0a040207900007201c0c01140020b542c8010502109042005150007401140414054480504001030360990341d51b036511185a5260019135501c807840d440c05001c0344400a000501d09c2034900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724754037 1250 724752787 724752797
    0x2011d0d060911040e0f011505010c0b28020a140c0c01081003050111030403030b03011506050c0c09070c051006120b0c1603020715021204090507141c0507050a 70
    0xa06954050181c550b0030070842e014140325080307050319960380c0194151843d40754014640706040310201130a4508031071080052000c10841880aa68006141015550000b01041090729100c91000808006c029440041e030080b80c0281440f00042d0010144803400d542ca00705061a0040c1c5411148030302200c9800c00e0340442e120903425400b80342110352040e00095a8850507689031030702c0e4207641d106002010010000020031081582610480b21401026002000410ba003403032002c0040e400c50040e00d00f07001000c039600040080c100030030650404050100810390030060350142c20002d00c000200c80754000c4038041040c5c40c0f05480b40c03408481010b10003e40b8a012030b180e4120010018100c40d400650401c2404080b0b401c035188616064440d5008107400741c605000702c00c50000303015a100c00c40d00310303400c4030f0104c212500a64065440051000174031340c569034826140340d0b41450380101621404100d0f540c12010441c6c20349100005c0310307420700c0155503481045410341300358421000818 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724755287 1250 724754037 724754059
    0x7060249060f1415162f010e030106231516110409120908010606050406080c09010e21010c050c030d0b0f060d06030c05040203010303120905150406050402011d 70
    0x3d100c00c203682401601030b140c4aa101d0100940700135a91110701c520400152180010041103400c2000080003a03403d2100304039124200c0758000c042043d8407030b460410040e21800341c910348d0203600205c000c002490041c000070090004c01520002d20900303140c42100c06010308005074a01104030707040c81100080c10304013800f0f240d0340c881c081c1e9410f91326542c120b55170740d103c000051036822148801c9001611650510f0b80351081140c2034503000d400102c2000b000380000c00c001d6401040e13240d0002110401a40ca072441c0c400121040c0c81d226001ca544046005000d062a40000c91081074108205d002804102074131441950700f40720340c6102d607550354410401050555540da010001c0d01400500301c0e07058103032030800580140c100c080100c1a941c2d54507401c004100920051034001c080565041d810343d032468030041c1210030100801c2c104140c4682006040000600000b00c115246c1011031055013842c0c18460010001154220301107922010080c00388458070034000b408000c02407455581e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724756537 1250 724755287 724755299
    0x61e09011206111b100606021f1b050408101802011209020405150306010e0103050a02131e0605030c0102070311060c0f01050f220807060249060f 64
    0x400c0740340ca0156151070f41c2e82940300c0319600c040e00800401c103e00300340c00500e200381c150690400d10a4085200c0851504100300003194002c60810440b07400c0c2c44480d800d0042806040c0c0241540d46107035160f4a04900d41803c00340d0300f000240096880f2903003103c420f415119070f41c00441c0c0c41d00c0e1b103a0038030303056a00303aa10066101320080d0b400301e0320841d004100c44159502007016207109655441d8809203234101011981010082d2900400006441142e0381d40b441c0c503280c0d1942044c40019008451840103901d5240103900070504601206481e800f40f86980d0028a0080c40700780a030a01c40d024a42420b0040d41c130024090b0300303880c2c1043c05000c85162142c00c0100030340c0300b041b0030b20850040342411300030b042c820700c25107205500341c0803646080c0c075202c421f40c10070301042a1500c1c0320000020034100464601c01c00d641d501503220a006948410200340d0100790f00c480c1a210880c2c640c260480c2030300040c100a07070310001d000e0b1112409030520310710310311040c0e4031640511400380f01c3c006010401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724757787 1250 724756537 724756559
    0x207060e09070522050f0a050f01080c1213061406210a0206040e16020d0503061e1207090f1a0d021507060209090105040b0d0204050c0c0a0b061e0901 66
    0x10b200b90030094540318843c1c4145180410b030a0f140d1000c1804c3d001e04003d641056550300320140c10480e20841050b003440d001170694070102408074108104d441c00a14a250202c045511400b400d001039081464480f607483e104441c482403c80e60340b400c0c511402c010302202d101c1039000c1d5200600e507014940035808008405000c410000010344286012440561981c500138030140003000307031a0142e4940101025090343d2101034032401c40d400342e18040d05c041c2e0700c401565045001280c8840b08800d91407403c4032501c141ca8080e9a10211800b148402c0d0600050404210740403070005012402ca01011101100c544800301042d29204101c450014602000340c01d01c0c0700d200800c4201110f070f200460a0b6030340c01a1004448c0c0c90340c00241c42c0e4280c94000211b50061070708a4081c810b48102d900401e61117016076000901031912807000c55141c041c1c6004fc2c8041011080480704031050a080c01845c0700b00c260381d6180103d1000d001d010a01b511504a07405807080a416801503918248a03811 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724759037 1250 724757787 724757791
    0x6010807030f0612140f06011e0b1b06070f210f110c06010b03240a15090306060b0922180b190b10030f020c01060608160207060e09 58
    0x20180d440d503a407044650ba030703c1010090f00d01c1c550b0310f2015a000f86060207050a0200003d5015407040802094803440091150305450142016041c842d207007181c1198207540a0f0400395804201092420502c80c200791240341c0460160110b031101d4a640130296802d038100d07200070000859451103003001e12000c46d504030f0a60225000011035256021004044820442400d15215030008408100c0c0108100f41c0b80509400ca40c454554242207203007085400f51309034034881140700c2d0f5044400380d60300c10040500500c8084020020030028850080200f0707040d000c00c4800a15083c03000c100049001e09403042080c014003250820301d098480400280542c40d084003907161900b00c040c81a420808920321098844e00103469603080088048042c0e408440ca690303002494401d503150f0390b030303183d900c1c030044070b4440e042c0025140309680c40100039100b51004841f032036090000006442c0d034484da8061240591240180a107004250200d8603541c003403048070005100d2041b960810310700788075166 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724760287 1250 724759037 724759051
    0x5100303021c18031211070b0304120e031002040504060b09030d051b0f1e061e0a06091103090d0804030509100c02031015090212011203090b0f03010603180b060108 72
    0x200341c00f529000c80d20182c030481e0300200e03404100f010403905080d810404450030800742001600203181044440010307804010400b910181c00d03085c3c0c05228030300910802058103400b4041c0c488602e5003040c032a000c1e41c000d12520340141d29218000502040d0041a1400800020090a40c08954440c12110f0741c02c80501c80d25614042408041c60350401c101030b02070303421450003502090814001090004071071801204681e04244200941c0003c042c2c094209594010581810750306d401e000600104072603001120303018a003085d201117950101c030141d0b00c2003620204a070040500c040703044a044400b07680c010b01103101031064100384c0c6009050200b9456991900c0034084081e034000918101000ca5818200e03640d40c88203400071421030811101400340c1c1c20b015840c0c084503600a19983d0300500c100e0b02c4034150000e04804041c41241c07d880207118842000c1e8440060000304210303035101f8403c4030042494003064400401c8800d0540030841e40080541c11503550703001c01503425403c010007003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724761537 1250 724760287 724760297
    0x60403090b0702300a0b1f051008101701020c070f052d060304030c0204050907120b09030c03041806050405040803070c140f01060501120912052b02070605100303021c 73
    0x2400d1aa130800010fa42c0c20701a80300000c007410105601c0559081d104042d04c0c4d070000d42d120600060725100700c85020102e003860450096030780c840b8000e5004890350041c07165848440f040329450801500540007a001c0c0c041a104455690070303506074481b180744034558104c686030118042401400d0710715024003030700b03040d02c01c940d860031030000d4143d5104039812804a01210001420342c20584503080d40158084000c3c0101803c1c4011020045200c0000414081c800c40000307450700002d10540341c685801d07400310794640361500442a070411050551075041450030600044074546030080c140102c0d0440006880c6480b1110200c5861024440680703508030b1000f041c0450074401c0081c403070b58001c040000179116041c440010080351a0321042c0310340d49d00b4101c0801c041031804c01545103801a40c21b0081d982c0c0154541c07040e040f410655101891140500c5e22055042160001c0c081d05d840b6440411840d515140d01c6c204800b283d0001a00590040d40303003009040180c61160000e02c054280307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724762787 1250 724761537 724761619
    0x9011205010b030a080421110d06060305060c03040b15130b031f05070e0402180103150b0304050304090b0118030b0a0e0601090c110d2717060403090b0702 68
    0x460b04e001c44d5460f0841d024640045c04000038585000005020340c241d88141c00412169103a6181c0d0090000c2214420b4800e0940a41004400d521410007190f101c81510401c3c501150708000541044800703075802c0c803e103400074007440218400c0c1c181d210030090031400a20786c480040d03c010100301c00240d406103d185810041c1400f207030600c1001145045000c612881c02d80ca00030b04030038480401c503010754018000b050b506591301c40b07583c41c9041c1c2880c000500c08041d00f00d003041c6600a501c071030348054001003031000b0300c2004001482510020b0303a041c0004400d4800454910400c031a08541c003101c80c0d42c050000030503003c091500701490302404150048152003c41c180002a800340c823945541e44c004005040c4c2080351081c0c0c1e41141c401030840c801c1c141d00e015000c0300c031f100f042040416070210415102d07241d0380314403405003403080403607a0f40703c02c0b40000380d0740c800b000d54050380807860452000034074140107004c4031042540681210040e41169210356003440521780207611200400384 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724764037 1250 724762787 724762789
    0xc030f0203150f07121404050c030c060f090402160b040c06020d08090604152d050f0c04030605060d06020d0507140c0c1e0d03080f06040c08060d020d060e030a02010f0b09011205010b 80
    0x200725001e18008c1c0040e0007800c0c000c038101403030000144061402008188a0748c5280794205003034980c000f40661b005a03884440b0802e0314020300702444014602481e1f4410b110034000501c4501058a4440c0c003141c0307603603003013560035030324035804403203070180c50b80440002800204291903041400500c4c80010401000307405950294078800859000c003542e40d5010104240740d1402043d8102021000c24002406c090344c000f0f056218500010b0074064454011800381e0702c0d400920319115401100440d01c2d040c1031114900644415169800050b10450140d4010305848040307a180d1031280d0001c0c05030010060610269021480701c21020000110410805807121842e60750514801c0c1c0c3c03410f40f40d18010881c580340390400380c40d560089280098081101ea04810540d41090382210b44403010186840080c044400b070b418010900d0f400c2010816507818000082c1c5000d0340150000d2189000c0e2411020440d02864290303903101c420070340100040f0f01c101c104011624000c0d000400d505400388 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724765287 1250 724764037 724764071
    0x9011a160c08010903140c030a110307020a0902040602010b011d0d1407060509120f0c0402310911180f011103040b04030c0819060203130c030f0203150f0712 69
    0x60700403592039441e940013000701988121035801c1041070101050030900b00708007065590240c00382c0d187c20300ca10403040414401c1d08100392000268024810091580c031501d0034000303504580300d41300140d0700b03200303510210750302901140a000229210004820581c0001c210710905842c0056a007031000003041d03041030405001e10f00142c007150701c07130681d608012002c0c00701200c180d4840750340031341000f07000018070900031401c3c4500682c110307409a203580701c0c080011243e113043d0104411107981e944185e0040b100287c4450102d0b1788201e8208400892a043d00d0f481e07104a02c0c01c80c2c40395140d01071102841c5084070b644000b1220600d0901f061030086c1407440d02d07541c000c1d04280307040c0c10003007010001c03c002c640008000d0726080e4003800c1ca079540310780303c10049000d58000071f0000360044006040d070648640740c500e001d03410005080d10503a0300c0c2060350120800c003805902a026010410b03100b11001c000d01405000008480e107403a40d03503510100c608000c511001e615403501c0f80c03800204e0506017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724766537 1250 724765287 724765289
    0xb01170c0705160f06050f04081b040f0e0a1514010320040e1c0e0402040906090e0a0203060406111b1c02011509020c0114042009011a160c 61
    0x500d08a980c0d4105418028a01036052208501e500c9040d4800d110000c0180285001c03541d543c104a030715100005240801030140d40c200202c42d2103010348555061003016a100c00a5000350350400516006803510008c0d5605400c1600c01d5030b01c1030b204000003034a10f4001c0245607905140000d80311291091214014200b81c0c0f094501c8140175a1003081e0b01c0d519a043c1c0c4c8400022a000c00040d918141910303260404000c1c0d035080c5002c504000a101402a0403180d84400d00602c11591142c0355a0108018046070080c040d9807031801030046580000041d940e1400364009000f07060541c0e4a40d43c0102510501d444001c100307030300b402001c541030a8240d41e1400c1e1110600901401480c0115004120242101c00021a8140242d009800844520b08015161031400144c4c0c0d499076002000d01411014408040d0716007100f040005104004100a407007842141d070365540a60500304010b0114028000c8000c0c0b52544400714282c00342101c005c0140004501c10500014901c0c0c03500300f883c0207a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724767787 1250 724766537 724766551
    0x140304090e0d030f09030e04051017030a02070510020c060f04080d0e01110601051e010c080c030c1b0604091e0c0503180f030f0328021306020a150b0117 67
    0x704402d41c140c51034150140f100c0a1860040401c00c1c81c1e00c6860003005145400c0c8140d0003169600003242484259502240c050420b102c140f640120b16117100035030b17a6102d0540c1c440107000b507960224180ca003850340380c240507401e44e0040c0781c010407401c00c100c1c0c0c81d40711007051040300204000c00204000f0a02101128440503192148003904200000d4400002603500004540220005008507034407a992520a60400120817070700061a00c01a80d40b800303103042c05880c2d8a408180058501c90002c000c08800700f10509590384040c5010003450802651000c241d48050180018805000268000d0491583c00500d518841ca40c0201c00401c48120b0007140d80000c00001c1080081007c0010f00c030816101180140350b0100c0042680345c40303010f000600c5038841d10010218010128a040240c650302c0e4000c83c000200022640100003988100c0003100342000c0004000b8030103001003a00c0c011140c02c00303e4460605030840c0ca0304014900c0d10f464906000003483d02270710303501d400102c803031146071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724769037 1250 724767787 724767793
    0xf04080c0717032a06070e0d02060304050d0f0c03090501030504030e090709030308092103180d05070203011506210f06090f050606070818010c17030f010b03070507140304090e 77
    0x2503181c1c0078000c0800d50403200a44c1d020192890b40001c4000180c25030700c00c01d00d24003042c02000031800902a07101581010354455408000d21040c8400401c600c282c45803191204040b19500c11815075031402481c00141c00703d00950130800c40c6500075000150301500c40e2405040a1a04a000a144100a94481000400c1c1920a208142c2c1108006402025501c01044110311005a40010340704280c13010101d000d01000bc00e4603483d0b03034200030409030805026521143c40100006080307030400700c4d080c0c0c401e60070080c1702442c50f06869004800c0d030780a50394a011600c503040e06403c0e03018142903803038650341c3d880f04c0b8062081034910410001e0300c2007c402240b061002144082030307030300207840c080c07140b0b070200204c0000805030303011606840c890000c1004590780b1800140c0e240c40f0450b102621620a15103916115150300006611641f03184246c0409070740c03901141021030104456000101d0800c01501c00804c8203801125807110003282105c0c0b43c1911048260282d070300713102c942940b48d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724770287 1250 724769037 724769047
    0x7120216080105330f060408010c1112130506031905100f0e070206220507031a151c080c070b0a020d020312160203070501090c060908060f04080c071703 67
    0xc291482c910751501c01840350200f0305910074148100c40350151600c0c0c0e01c1002da5403122011170b12511b081d00c0092003454020003c2044258014180308580d2803090001c1c001e0700000a02d0200070415100422085200c444030320341040d0038440c06074000303032020807000703114800c81210b01d640b802800d11404909014034000c616205442c89031159940040040c48004d03800c05c100715500251541d40200b1000a03100700c0c0b035042c06c52050b48807880201400f1401501004020301030103170b5042143d50850000800780b9074800f018100e01d0007164500d20360140c05c0202441c000498103c0c2c1000c1b45009180b1300d0301d000d4030454064038161181d800307494145004621301d082d00d50144660f014205a0b03001951503c1c5089015a075264402851034880308050704074204994420002e032803a250307000703001300624507141c2425010100720307104000000b50010b10202e20084089a5103025041e004c0c03200d242510f45541c0c8100680010003003039110710417440001070507816101482883c882e82e2015564407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724771537 1250 724770287 724770301
    0xf11030309190812030c0901052206051b0606090f091e0c01180f21080307080405060601090803070f031806081501030b030a0201031a04090b0a060e040807120216080105 74
    0x8540d040f1581421340b01c00b03004000000c0c0c01c0b2411210305d05d90900e40180d440c24915800c52001a26504001044150a0001c149a50840024502541200449003003a0020041e0a580d1003040342c001350000040000300e860408114492604030b0065000e07920307c1482c1740102c511100d0740d000142584d0388105215001541c100c2254103500003612940c4030b90905001c68080b030442c851044410351000d440003007000c0500301c4583d216150344480019175a0411820003440c041050340d05403010f010b1072010460035801110f000e8216120758000d5820080380780c503000845030100405400f8007400b6812001090080000c1c00f001e009140ca903101142030211031004204400c50105060614225445c074095800107800d0071100d0b424031700891045040e0940069a81c07020064642250402225408011000c40114460000302d402081403603030300c0e500b00309600f00c01d65015003d10020800007021441c682007480c140c1c0054012510704502e1201d544041602c254400019039540301d09100030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724772787 1250 724771537 724771543
    0xc0619020c0703030c0f080a0e01020f031e131502061006210906060b030a0e060903130e0403170408120f010812090d0f0605011e030f110303091908 65
    0x1004411180440c201510465080e503125900d00020701400001101d031410006c20038140300307009610507095501e481c0100c1e806008150740602e420f000d401046411071038910000140e645488042120201544081c00f03100c3c0782e0361000b016048007003070f042008a61051144420007008140d80c0c004c003c0341c9040c55603241411070a4019804010200000300c2d40703041c4680d100c0c0301c0c0180701d103000a180c3c051483e00d03500400c01e940c480550210003004000ca00c54103980800060300c40c8405a9075680c0c1d40e440800e031248109164071002e0785044c0b00c00d00080c004e2102403644940701c0c0c1440c410848403400d142415040407601191010b4000883c000c103c100c5c81501034219920314441807895040060303c5491715031140f05000d101401182c401c20981e1000c6084401035000306040d4108030260610f4805000c09005000055454100090070744401260220841e0382084081d034880340d0564450005207424407660340d052100f0f1042d480c080d5599282440c8429014140c5244907140c070074001c0c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724774037 1250 724772787 724772821
    0x1404080a110604080301030809131d0708280305040e0a06030c05010c02012a0218040302060702071a0a030b04051006110f0c0f18090709110a0e010f12020c06 69
    0x40c07150800800d10000030240300a07241920f500c1092142c5448090001c171740d40400e410001403905041c0007102c080c1e80d401d117083d440c041b2845810781344441d45034280d490b0b80d50000d00480981c10401c0b016038011043e0111100162071007031410340d18280d40c901e03000070400c10075210829140e42d80c4008104001e035103a0401c0c02400c0c2824207044083c02c0fa00060050000c4005858003030a071560314851841c2c1141c500039210b5401050061420b006840030314a4070001c45007103001d4403444c404201c0d034074000201281101c18003001880507030414aa03406140e004810a181403607166034810303405940314002e007441940c000381035103d4103290030002040d0741d20806054007036800c0f803640c6010141c00481c0c0d17050b4609054070400001008000810b04010034503080c103460010540a21080c02d10100d44002115a028400e00082c49070003e17000e203520510b0b2500e00807460710140c141040d40140400c0b502da030000d0508221a80012070850300341e0b808900a0032080d0444402c0100c1c00155101d000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724775287 1250 724774037 724774067
    0x50a0b0703020a0503120a1a090613060518040204050717070c0312050103080d050a060f0533040f050102031303060e07030c1d1003170711030a140c1e010c03031404080a 74
    0x2d00d62302c203c04007103001007001415150103190541804c09110b03001e50094030081c64054400c0b0b501001c03800001070760100a139000c9105900304404a80c0d042d204103584d080d44005c1c0c408203809a200c07080180c8045640c20400c40a001c2c100540304284107280c07140320f00840c021800e0980d1280034a94113401c490000f841c96400501d0b200b020312503207030036003c582c040d82c0301561104020540c0c003404810358a54804d01c100042c8a8960500c845c046a0340500225100c601082c0c180a80711801681c0307030b015203001c0f14102c41e03540c0010404295103403c00310a00d03a01500f41d849558407503c1c2d603000c8107155040a40520100070305020b000d015459107a44c01078401c95140c80440c1140d840d0489219410030340c500d03d400c0864035009000c1d83c801c6000380180010100e0310032184518058003014220001400c00b80914170082d021400c000152030507200c1210003c120039a6010015074055007400c0c0e040d020140c1c2c609201c40c500013529980d0740128018141c2d69156551000c00802e90a0410045 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724776537 1250 724775287 724775321
    0xb12090708060105151c060f06031b03020d1410061709070b0708040f030c170604050a170708030f0105040b0d030504091d0105130615050a0b0703020a0503120a 70
    0x200120701c40401c040d030540d00100c0d142558002544401c0312580955940310038001e951480c0081c1040c1c05501100480c3d2031000362241e15a0741e10029401c4545012481f100d04038980c030388003030705440b941c0141a03407059101c00243c0181824000b48070302c1402c072606a00b55503c980300b402400c1d004141d02c882da40e81c072110120701c3d2400b01c7c11252241e0451181204800c80800d0f41420001c00d038040d00c01074070b2008108003400c5c0c0d1382e05100365490020711400d10460580700c15071105080101e009440341e0740005c01040314501c255a42c072044030160142c1000ba01c0144090000036150200460041c2400444004254104403c020858500d090388a21510f460560100020340000075a802c4074024480016060012801068501c110880c4007500e03518120410108924015450038642d01400c03041008103800f14003c0442e20071405590b5101e40d034a102000301411100007804400d12902c151480f8520f01d650f0070380b55802c15900e40c14100c07005410800c9100d0184203050a02c00b03070743c040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724777787 1250 724776537 724776539
    0x1090525050402180303070c0501090f0506090f010306171c020304032d0c030302030327071802070807030f11010c050a11010902061912110f13050a0b120907 69
    0x106204151148078a5001d03a8010807010f140948600b101c2504000103415a540c4d9086407a0881204016020700c902003040d200000c10000c0441c640081500c50260140b442c090f5040200301d01c4541d00c0d43c20b07a04143d196840400c540c0381200d805010360424400400380c05411a9a104103040c44120b90001c542c820321080010403410240041451180c20440b402d44440c0340c160305a0303012164001d880c4440b01480041003550005c000c51240c501420821500c4004841c1410b8a0340c48000105556200035400c1c44811007012240800d40d40c81c2400605c0c0040ca542c460105c0e1b04105800d8000c0740c5a2041d0044240d04000e00f10242c1c03c554001b00120301d050000075000f4003c81c3c4d450010480d1225401b04c06100035880341030700c55002043c0c580c0390800c2d1040c00c2d4410000095100c00201541180307080103026015074440d41c00400c050a06003200c0ca40001c2c001d402c030480c0d0740e814484a2800182c00e40b40c0c41d080d8030142c11b00ca032426a440c5191101da0b280d00b50007030140c000303a03802500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724779037 1250 724777787 724777843
    0x906060a0804080a030e0706050a0210050105010e0f01020a02041506080906040b010e220605150109030b0a020304170406080406180506160306081006061b080a1b0f05010905 76
    0x3844a50059121800320b44500303040301c0850080ca440000c07451b661080004c013050603508034001d403920810580c00c8030b0020b00c110034030703105403942841a01d0106840b0420003001707183c40319600c00004010720482c0e1032200075800040c203485100d804015200e40f007003070030f001c41d80e4440d0481e64400940b81c001c203541e0401e0b87d100e40030101c05101c0c1e01801c0138040c000c03890960010304601c41c91940112001c00c0031444c0c3c1803501c020b00007594442c2e00041d0420900302154000c070801c070100c82c1c01040c814101e030f039840b41c0c0c54080d5100500c111001040500c03688103440d4140050000b8100130740d1003d505150501e00308007254001440900010b401aa43c0b500103500010140ea01c12021081528581d6040000b40e019040c9900b1032407450281c00100002d40c900d07135000305d04551096507400b2945d011102c241980d600c0712900602020010808502c1ea00d000d5841141c040c450030940d010781c000303546c442812801110000312241d03515860048203110041204100614012403204a800c074034003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724780287 1250 724779037 724779047
    0x301150504202b0e011b0207030f11010203040503120405031b06191806031a10170621150f070905010e0a032414070f120605040c0e0906060a 62
    0x1c1180405800078118400c4031006103a040c84014801c03030b20920000d19408410390107440f03034142401c0708003000918146c3c51480000d1520449400c210707400f01c40c0b44c0c5600c0711140d40c0f40307440c03645040d80b20130000001d45840400c110800c0b10b101c240c01030b8450342000100340c2050f109020b207241e08100401854960f940d1030003100c0400c0b20179510f058581305110425101034040030340d0070072401c0543d0070000700181c068014020312424508240c248400c110200070500719502a03c030700240040b1000e0300804e13400c6440d65000b500003400700d00440014404040d5024850301140041c0d080f0110414050021411454000d120000810200c4c50000d2001340340810300d100350342c10420351044182d2035442d4410a0300286130405000e10301c0c1240c880300d03945180c000c060380c218614038040d41c4c0808011901701050050401d5075800f119900102022902090401519521240e0f1400001015941d84c4039804800040351502c15640b5450000c2080454008040c01d01841b000c01c803240003243c1c4070f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724781537 1250 724780287 724780297
    0x30a020a05091e0a02120f07051e0403020a03120f03090b130c030203061e0f040209010509072105070e0f030d23041202040c02011e0509010209030115050420 69
    0x5848080c0160794070b1a5800014141e42802c90f09481848140100001c843c0c0051004440384500c1040030748510b01801c02d220021610b060005d40140b190580003140040031846010700c1c407070180c0c00c298603900000c0720700007240c1c4212078902101c82d201c0308564204e90310f102030a81d60705040101d15030585491580300002421120030011605030728003006001d018403809550042d048401c1c40c9804103200c41c11642a009404000d825100010710000810502600c1682c1c0541900e001da44de00c01442821100075108509000350002901080703c3d10f2400d0070005002640c0102c0c1504161202510917460ba03613450707000c1e03000034a00108a0b02c0000f0f00c3c00002034180381c20700c60701e0074803884844010380100c0b4189030364900290000786100d41c0c0da200d012550003241d04200d00004140d050703080b0390318200341200301c0301790000002425101d94041603200c1c10100c0050300e0b100030746d40000d084845c0070101e805102c03a0000b00340580d0400b4803030b074010b01c1d4000c0f006024454921150301503034014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724782787 1250 724781537 724781539
    0xa0b0306031b0a0807030b0a050612100906020f130e0604020a1704050a021003140606041202150417030423060d0b060403290a1802060d110301031a06030a020a05 71
    0x10011507019210b80c3c514400401d5480d00381c07030030b05c2c1d1240f8120400d01070950b04841c8880c10400400c180385130603c040442c1071034502c001c0003a018240c20305c00103007000f88019140507a0074004550007031450402400080210a000403450341040ca80d10350100014011038000c0d4410700860b160b41d6081050303e4074559081403400f1450f9654600146410300d1094000c1d0001e903000d010200d072a40641204e00110340d041d04c60481c90307403520244429070140c2e208495200c01e03510038090140c00c0030100c8500c0b019150b0405442d2a4483d50783d2020b044202e001812547e10000e0100103461545c01c41c915154103c400d00c0402c80c802c44001041c50090100003d06143e0711303503a210560750b548049070003c56000c1046001844421084030300c4806031140c03845050340c83d4000400004082c800c910451050000d205600c4066800f440340740d81010301c80300100b5584030065803503141048007a5000710320031000d680ca8119034040820003030a02500007402030303212010040041c0e541c0007a20080c1d0320 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724784037 1250 724782787 724782823
    0x1150e010806060c0a1b0b1305010e01030608010501080d080c040f03140102041a0d180519050c0a09091511030103060f2a0f1b020f0105041d060a0b030603 68
    0x50b400b00085251240704c5011800e48929072068041001d03d1852081050f0100c81900095076108a0404a4410155041407106409900388410360146441c1480900185000142146c840013086e0858000f80c02413100c960000e581548510340c424250781d80603640e560b2203410180752940c01c020026080c0402800c1840c4a04401c860441c02d40c1954014440102c607800c2082c441080086142e0052105031b0103542820a0480043d441200c400b40199200c0003c0c0500365600052150040d10903034126202d002e0640607501c81d9994054400c040d0944480003d400042c0f85403690032418060660602141086090800821000d0540781181d4001c40d001c15856130700151080200203903180f00101007059018110207040910880240c0006034840d111800144c10040e525185d00c1500a40700a100304614801410400079913503c020040c100203050944814400c0400403217202c004500d408200300f000554a00b1240c40da0082404002c1a40345041c0040880c0d01e886000e01d81c107080304 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724785287 1250 724784037 724784041
    0x203090a05010513151205070309020a050d03120209041431150506041811011d06030402060c07080d0302070c050103380a0626090d0809070504110d0501150e0108 71
    0x20b0b000b155a04004411000100001c2c0723803000f4007030024180450180d00031100360402050504000c0406c080325901507c07484250031044500c08081e41c440020b590300103890310082d40b401072001c0c40c824001d5080d00918886401c0120004903c58140c42501c140c08942c0701401010032070000b00807250115010000ca519585d031400314020f8070740594680b41440c1216a00fa0906c0391001c038028484100740c0e00d00146040702500e05014085c541000b5900040400209005203400002849102c03103a1090b00d022036550500c55040401100ba00000700b03030000b94020410890a900c06c010300400d080405c24180c42a40340c46034141d40c0300c00800700c01c2950107481c02b8000c0e0201d507103206401c010002d030b000c141c6130240140700c00e2003e080f400b5140604106407400b420b0005c03000e4411401000107000c2a600e1110403507c00d10081e060b40c440d400780c600c001c291038917140a0f0162140e44c150340c02d65074841d51b0499208880f4140e005030700c1d5004030894051007640c481260b01918209280c050034503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724786537 1250 724785287 724785329
    0x4090b040f020d0804030b041208060307060e130e0a1707120507050f0f010209090f060d0206030a0204080703080a1209030509060903071701060302101701090f18030203090a05010513 80
    0x11480f400050415000802c00104000000b1742c1584204e10a01c0c84582c040d421140541d54118140c4203150300d0340000c1c230240403c0344100c007034125261004202c219640b8014000b082201c034a402030818035000f140f031100620400b2040542d200c944d031104103207007180f141c4079942c11000812182e02000320024811051020400030341035200800ca09407034100550002480c001d500c0307148e94501a8606500044582d4003a1400b580b00d82005080c10b0b06c2c2c00c460341c0c00c20425078001802035000d0344e801e00011035844002c100708800386101e82502d40e641c020040004d040001d56090285005007484030010010740c0c008281d491318001951455143c01d080c400003030406049030010040d04951444010342c0c00e00c1500700714101d0303000f0b68110511301c108210484103640301283d850040d00254004004098465200318a0301d4440000042d040c140100c418003403440820058005074808200c01c00c0c0c80c9094001c0ca0020302c400d081c55460704071100b00040da8000c0910030105902003043e080151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724787787 1250 724786537 724786549
    0x11526090c0a0e01090b040902030606060a020708060c070317060a05100509040510150504080c0f0d0b0f0703050114031c020109080c1b09270f03070501050f0604090b040f02 76
    0x1407140e008101101c199254010340d070040a0911820601d01d04140503441e150825100c1e021006d90060050019079440c0780a00006a2121552104510441c003000980c00030910079103004001d09000315968501034140102190300b81d0b6101900c2256000500503190780300301c0d4010848005650034620b028207a24140d03590b01038180c035260090304001c01c014445101e0250503003540c0c031300700d180000780c0310456013240d00d0300490159900d141e0088403441041d140c108152695414010b08680030107103d0b56070303500d14003001c9d9030311403011400105000681da01401114007400300364200d11004220704002a0b5116501450b00803609050b200000201d03100703400181c10a038020740c0d402c0d503a0060344441d6580c2c041d03003400c409240801c10010415860072485460260346010740160400d5545404400745102a1007200510310800d0b010030b551480501c0a400c00398003844c0000381915000c3eaa84e402c1c10001410380c0d22861904600c00000303072800213410341050700a020898148000d20126003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724789037 1250 724787787 724787803
    0x1502251a0705252409050111070308070305060619050a0809010b01050403022106010305070305061b070209060301060810020c012a110c0a09050a0b0d08031605070b0403020601152609 80
    0x140011544003c44c90000c0c5541040e848240308074020010072101020b40c04c514003600c50020002419140440c104601c03e40000d80c1041d00281030605d00001c1d981c5c000415150703154010081600494080341c4a40c100b80466403090081c0002d0041110f9000000c0140c8214003000b0302c00d54500e54114520b0310078800121382240c0c440f04554855071681000c0e0f50780c4826100440d0540326540c00100d03d10500d9045c0c01c000081c10710b07094108280c0790308001c0e02030b50013020590159a01c00c400034440200704104040340c107441d0001a40c07008801c1d20b042c00d50b01a504201c0c07482e016040d4442c115144182c01d480300c0382240c50f05103e026180c0301d126052144000c03060f68042c20701c01d00845c244000364400381c0aa404003c00300002030020050000750780c148c90780a050101c0c1071002502030311078030546d11050082131602a20b044c03541e0b6641e060415040d1401e5005a020300014046440b040d05540b0300e072009810031104103200c004048221002c65010010303000110408a0901d240c100000c132 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724790287 1250 724789037 724789073
    0x61416050f0c03060108010b010f0f0e030d031506020c060708030402210601170d0c08030702150c0405030609120d09030c02100e0a121502251a070525 66
    0x1c0000000e10041556184200c0e9850721030b00904000040311a014810b8039242e03071068480f6034003818045019034503000d10070100bd0a000c2c0c801320b00e10b4907a4041c0135002019109450010300611030322903024002103150042425540004a104425541c1c40243e644180d03210441e5030752992a4030115002280c2c4240501810725180e402d070031240408a5003905a8416400300040c00b806031841c160344040c030702e035801c022030101c4504501203405000259400a4180101c07000c0110000c1030400440e001c4171802046100407d06202c2843c0034041e8980109042c0c3c000c03c3c0c480111601d009040c419007000342c2e0f901d0b230b40d0040c8204040c0100807810030140c0052101c0d8420303004407400b82c5501042a251445007180b520045002e200500c43c0350a483d80080c1d00313000e807400002c0c60fa4000d601c00100364501c0b82c41c14034808110300e21b0300014503155114007640070900447c0e50401210f0140a03100106000081c0a040c075210403203e0155421441c1c0c03075444400b6015070a180c01801d00c00c1d0464 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724791537 1250 724790287 724790293
    0x1803040603020705011b080703050408090303071b05180f040c05120a0b0705040b0f2a0a03030b060315090402130c03150801060e07080c040e01030f060b090106141605 73
    0x1400c507805a01030328515000750000e12003075154242c86a01d4141c40c01e2107402103890b2901082115100e0343c01035602500c10b03010107251064510000f85950031074881110005018550b024440c03014514510092030b041e141e1340c211101c640324005020750010f18007040d4040200009051054420310100281805070061042d440c0c000081a164038445500b13503503104080c8003044100388240102c86c110703000803940d1418140c10844c90341c40360380090102e0920111115845141c0030303050700c2c07520000c0d180200910000300540f40c090140c0e04a44012441020309208008400044c15460301f400e40c0101c40008680d6200e2002500105100c1600035040d0b01c1c0040800540d50035034003041c86203902c80300451100d50756040d110b090790341d58000d22101017220004180f0190013031720314940068a144e011824641c40702c03d00c2402d65000d1740300b92204000341407480c043c4074041c440c0c10104081522040425814241c0c041c0ca482c800001850701810005100820792405075110400c2a900c2802d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724792787 1250 724791537 724791539
    0x71b02041a0f01020d02060c0d060f06030501030c080c030c01122408070e060609011b0f050715030e0a021905040f0b0910150e041b0206070f02070b0909180304 70
    0x1000786810140140d01c0c0079000d05010303000d41e0344c0001200241c49050317500900c042c0e5200c805400d91504500401100d00e51115400310701d0b03002c0f8a403d100540310315030303001071258511b0030206403642c2c0c23a901400058020100ca0002ca4a010501c1003002070b00f030074080540519400c924004181c01188000d1001e041010200700c01c00075070500d401c45030642e0468499a80b03818855000d010103403548e45d40181c081100b8050b40d40509684499600008140c00581210340c86520300050765060442d007542043c0410700c440e00d4903d18114045029180c10040d0109081741d9079541c0c150540068441c2c1c54000e9404c0b07404041c9220440035100103007051190450707440010018000071030055106802510004046c0752503004524200d4401100341c0714099050354007901e1010910140341e070401d8542104203440355000e045480c581005a000b854680b400001c01824503101503400021900151401c120502c50b2034141e0710b4054048805031855103410070800e9941c0e9004251001c03500002c60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724794037 1250 724792787 724792811
    0x40605132705060f010518040e0a03020f01060e090318120a0b0a060504090213110d180b0115090603020904020c010603030504030b06060901050d0b033c15071b0204 72
    0x1240210841003420b00540c0c40b104100164000c1a03102e0f40e001400902c10241c0313002841488222080001d48001014541d514145003056915041a00543d20004076a11603038802d10820b0018009400d0071551400d000c01e4064480c400c04042c0c040c01c0300748400c083c1090352250341010a64510008690b40700c8014034203002040d40c01c60344048414580800004c00b410715000d54042d4903070050510414400d808600e20081c9400c0300211041c95051040d04501011841500700400c013400e500c0c04444214a40207041c2c9905070082203410303080800310340e0100e40107441407040c0d40150034090703211890343c1c0c00b0900900411a66001030b600b0801c0000070300d608030b0000c20a1342d000d480744c8201581c40700b0a100302c621419104900284042041c1c18014985078458021840018152000700803284414001c07107481e8880c0001c2c0e042400e21031074100700000345a01c00c404000001d84440c10318121148010140100350704c00303001011084203194900f0320b00c400e1540303134010020080004641 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724795287 1250 724794037 724794089
    0x13050f0d030c030e030f0f0d230a0b0d08031b22050901060504060c08031801060312030c02010e07050d0507030501020a0f110102070c06110703080d02031e0c04060513 73
    0x500840804d241c0103103590381c0f0a02108507406192407034400ca1070552420340c4d4540e5a406000c074005055540c0000b01c4c604c0d262030000280d0b0485d0b0017480300c00c42c01c01d0000c140031a0b8820104502c240c1443e42c007840021682b4080c1c941c410b078034443c00340c0c41031218001040c203445400e01c10003151044030308041d2442c40344884c99090380d2099511280c240e0702c495003540c1d1480f41c2d00405011801d00041d00001600e008011035106004440d0100c0d50b60385440010f00f5611207800448800d854401808a955450b10400a040040d44001d01c0130f64500314400344c95034002e01400d40910b00d0180300c641030000402442c4011507000f00215a11010504d0003040e00c568541207200017101441d204240c00c105000356a9441d0304090003031201c916004094459400211500009000e40c15002000c9449040070f4510b100500102507505d1800c1c0c8a00711007a094152220402c030740c0d800c180244450100191000d40d103d9081141e61030031307039008298040d8400d60002640c40c1c264066000030203070702c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724796537 1250 724795287 724795301
    0x2030a050f09070b0318010c1715090a020c01110c010507201506150c060114030607020a03050f090406060e15160807080d020a081f05010813050f0d03 66
    0x8510200803545444a84408115040c0c0c0c2030410759110034010301080440000841d04801c0800c3e2000b5203100521140c1e096480d04010000410703e44031006075854041d00101e5030144000340c1d946001c2e082280000c0715424040c01d1000d0b0540e000c01d400211032000d50040001c082d40211241d01c520704441c030f0714040c0800b282c001002400c03140700444034125069420008d885410081e103900302c02c1e00400100000c006002550003108029801088140140108400051340010300020340c10400e203808010561402c81d802039005804102c080e030790108a40c8de6060781494110b580381c6280b4440c0c4428000d2020450f841858070a0003d14603800c24110040700d40d003650440400394850321a808540100031150070128128002c01c0c0000310b9444c010a54184030f100511b041c162205000b07800c82c0c0003280c81e80081000c410500c10058020301034510070b420011156071842e82810002051010040d0001c000f01100403c07180400c0300030701040c03451414620072a040c000302058000d028000c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724797787 1250 724796537 724796551
    0x181c0f050d0302030408030f06030a0212010605190503031c02071e05010e1606050901021501060908070b0c0c01050d021903020d06060801050901030b0717010803040e0f2a070f05010203 81
    0x40380a2002928003d0007680d108540042d11a4216a207295001c0654180107111550601980c1c80307540c0180e4840c0095200d54001c1d00c00040c8641c02c04060000f980b6446c00c180503040720603032040050b40d1f800401c6404500701112002d90b00342480351070a01034001c9500c0100b040b0002d0f54140c00e541d250702902d0a02600071340083c041c04028010494850b400c0040306508400408400d00120380164020300c5000b1042c4103ca506012494610601603002e820501c0042e00348907041009801c200316101c0500320948045103480c001407909603550402c002040d05005011451200c0850701e40d050707915400c03400f0801c505003059072800070029448000300e0500c141c900100070401d1031051042505a9030050002c2c40c01c0d9007035403207009003104010002002c028207450041014a0700500c9a4000e00c020001144c42d42c0c2083e03e01074542c400103110080300f46a15040164044881c030502400d03010710245003402000d040c421503881e2003110f40c080d2030700020341207001c104001540158840d1403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724799037 1250 724797787 724797793
    0x19120909020903060708060102101a030705030d020606040504030504120b06120706020601050415031208040317070c03140c1204030614010b0307030b04060e011215050903181c0f05 79
    0x500d410894080b405959415a05075104500058003280a00041500010b05004a401c4032242602c2401650300c2070711b075240281e142d443c00b005a42000c100e56070142104402401084a40d020020740e40c200080100f4401e94803500450140b600403400c54014000320a03000303d000c0024140019402c10940d03081b8041c41c141c500f4403c12640c0441d500055840c07a0b4050b2803164600404c00015141a148940c5110b0302403e002002414022409850701c000b0780301c40100d40303020b00313020b0b0200418800140000301050100122241c0c4280784050395941810021074082c2d412103001242e0007400e900794410310400d04800d44d1407581d00b000d4800c0300c1c4102018000d17101e01402d1726007120828400c10701610300a0011840e094081e8220081d016000b8100080c442c1d511040044404400e9002900302031901000201307109907680151034a084400003440709040c001582035130381c801c8000c07074402c40e074013021801c005507625206200e002200c10111268503c40c0d040c0320f82c11103151801140c181c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724800287 1250 724799037 724799039
    0xd1101050702041d1b101d060c0d0314040b0f090f01051026030a0503130f12020607020a03080117030d050405030c0d08100909150e071406120711191209 67
    0x184554002d14078603002d41800f10b000c11408069640c201004032010301f000525421444c00d445020143c860800101c005010b0440640006404c880781105941069541141004080b40e00c01904640020341141088115558900186c1c24001801030070381046d4280001d010a91003a03072210b0b0199891b4030241200846521403512020004464980f1550010320003030b403500b4004d20146a100d14944042588a0040d075901160054002ca0449003120f1416100046540c100045036002c4090b00041c80c0c417440c60340340600340300c0701485501050b0842d0004400c21000c2030003516000085604144105d00705441c2480c3c42e07400c0100c00b6125880380c410050315141c816803005004070f8452100520240c1045094409810442400d4a001c0805440700889041901c558040c0c1d0540c04d0103013048500b4200311088811300c841169200340e50078001c503900130031100400e0b81c124100e4144034220780320888185080030603e1640c50f181100301c209100a0ac006c800e200300c038462941d50345034105 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724801537 1250 724800287 724800313
    0xc03010609050712140a090309180213090213031e291b04090902151602040605030309030309040f0e030a08041505090307120216090603050114060d1101050702041d 72
    0x46292503100c02101c4009400702c1e5140395194004201c05002740b4048150503200c4113610207100344540340240d256400285110b45180003c0f080000d8020420b0542c40d000c00039590850140d082d01001d4140c4003205200d0803031400c1e20300d030360711003551080d000f001240411000307032140210f90728407501e5085c0039000603032180101007201600b104bc800e0710a007803908000300b18009040c0c1c517508a80003101c0c26581221000150050150200c2080d43c0e800ca010342407050005981c0303241d1042e40280d0003481038980564001c0156000c1c214107803800114818507030411400344c40c0804a0309594000010407606055000b40c1c558402da000780505046405c000b2040c80488104403045031072034000b4001d51000804108207501040d215104a91490200c4261a0128043c60340034000302640c83c0e00070020000d080c087c07880c2010402100b48803d14280021070400c4d07129413001032031082e96a0700c040c4184c3c00b031400c0d2404075402801c20402051611031a030050b01c414130340f80d262482002d01240313407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724802787 1250 724801537 724801541
    0x1b0c0905070f020604081606110a03320a0b0402030118200301091a030105090c0103111206060f25030e092e0909060b01200c01050a020c03010609050712 67
    0xb104290740c010000c0d6030725070700d545403186c21168074220075500a041ca107010803043d0150b48600c0058070b56040e030741c1c0e054040c050121101e000302340c0c0040f000c200c4102b50002800d2303030648200100081d40209581c0c2c0240420040010842055001d48003100120702c40325182480494603491060801014107050341d100e00c80c4c039a51803800c4065408000500a40c09581c00014800e000c503112100ca45540030002402c1d0340c42200d202c030041e07000a40c00c0d04e039581d150213421030150303003c41751b80d01e003106e0001c50305007805000701000d010b600c0018070710545c000704004540034500106c1c080c1149011280b0000322140244100b40c1c0040d041d0024001e051408400c0d145c007070718400c642036204900354640c0b001c0c1d03062562100142840745000000b5a40485e00500c4040b520421000038910310407000501b0104200381200000b03080c5805440a0080010b00b50850040900340281c886403144000c030b1912002030b104a4065003000c81c00140d20541c0d800103070140035a91240c000081c146101c8000f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724804037 1250 724802787 724802807
    0x17070501270c18090c08160911070212120406030b04050903030f1f0e04051c180b0f040504140711010e1507020a1407061b0503070b06011b0c090507 65
    0x210890b042c010805101c50519a000054002e0b01c08183d01c085611a50b402c00b0031035010300110380103a00e2940f00807043c14082005004454801c0100e540c983d0405502801043d800a00a03441c000d840400c440040002c0d0740454118112150390300d0302e4100040140c000c45207010f000f00d0406003c103080c9480401a00d11030640e82c0034100040d520741c0001044019002d00410030324555000109118203040c52803449203028074000c00003d030401c3e2400a440f9900f521140401c0b000f4401c9041e102152038100084800d50140b40342c80312003812180f0400e02c140da00c4a50701500c2e01c4074040380d2446441403580f06083e285c8407070710b00740400340c0302034281c42c00140141c0300ca4000358140c0c14017081303410303c07150480490f104880c1e800c1c0140d074a07080d4800341a101110103a0115a040003503a5005101962a415542d1103583c48a46540d805640c1c0c09040d1000b0f01117010300c030000303c02da442100400c503844462440000d10354030318101004d0100301c9000303191441e810500040d2441d40107862110b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724805287 1250 724804037 724804043
    0x30207031e0201031127150a080412020c010c031d0d0510050f0105130f0209030a03270608010303030c0e03070909050709021206010c080705010203160206070c050c06071707050127 79
    0x41c1c00340300740c0c42c1484440400d1b020340c0c6501c1094120729419001542001c0d10045485071500d099a08080c201340f9888801010f41320308552011903204000c0c2d92180e40d20001039894240245824070130305004806c0b0925034113464000c9204041c142c2400000202c414840152250400007030716403450514551701d09004180d00610301e041d000080341030952243d54140e00c0210014103201e03601c0c0010341415205541500024440030805000201020301c0c403e204003414001d102c910700e00326000d40035084c140720207424103580303081203000b460155843c1b0a0450000b4169510350303403140004e400a008030401036485204034040400c60f81d080f40300303e0704902030f08412910300780e40e09001121191042c5e001214404c07003d01500300019024009540181d540d03880c0d401881c1e030385860007480d040d402400101040241004034000c40c5000c20444440c440030f4a0342c40e92900d41e0f0a0144441c0d4200d0007400070031000164400500c072040d40900c01003a040c007180603c140300501800150285050f000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724806537 1250 724805287 724805317
    0x130603050d0509011e0f05130806130b07030606170403110715140405280f0902030a050a0b280803030c0408011805100903030b040510030318061704030207031e02010311 74
    0x4540c041d000350048c05d00b029014040d0041ca42d2140000c508080d020744880380290044c00f0090304011221110700e600c402d031032800b08001860004002d040e5040a00d44075104140e5502050a240c41b807483c1e042e1400206040742d4040e6030340c070100c0d840350641d135100701c3c0044d0440350613041381d17a0403200711004c5030401049c080c481c0030724840602c6c01d01c10910200110b03036000d200010300d1220b0704181800034076107060010384a14060800c08140c0c1c00c01428070607400c1c502111106583e94551800141c1c40c9405075403030300c0b41d03046107103507007120055040a84144004000c000710528500c00034420307030704244000d0150104101e0302031241d54940f5001802500841350040b030080036a0f01003d100c901a24000ca00d800d40c8501007004c95406850b2007001003103442082c001d0541003079800d0301c009000504e50075001e1a101c2c0c001c0014102004881c510306554020805140c401c020782809180c1100010341480c1240c07110b00d050304441d240c1240802d04007480c50040f101000e00340c0715103405119203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724807787 1250 724806537 724806557
    0xc05010207030203100203090712030f14040501170c0921010e0a0309090f15030f05070501050f04050103020702030f1507142b06230901080c010e130603050d0509011e 73
    0x80c400203908024070043e03040c42800000a2030401407001200e2b002e0085d2211400240200d80c0104040c40d0010071801c841d904000030090740c0d0b40300040c4e2070507050003040c403211600c0b80c400100091081d060880e40c0410944001601c0e400c003011317103104881990b4003c11804541500c00c2e9280da601c68005408903044180401483c500d82c1c010b114411110840080e1400c2d10215035017116200e90029110204903058100c20028100051030181c8001d080407800c04c542012041d607284602d010709410036802080d510b0454404005080940d00d1100507511249901d000c107590301e9808684e444000f0302c2d61250312106d0b00c032610480e00c07148200300500004c0303d0104c1d00c541071a0382d26031809004030b03555a070014084d050250b00aa002d100c0d04000c03040328128004200d400070b410703008405107400001d2600507a030f800001c10043d04000356180050202c01281c094001c02541e4409401802541a6000d1a0342d00c40014922100d00340c036402c0c144940160151610750314010164049600580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724809037 1250 724807787 724807813
    0x6040503070b0406060321081008030409090201050f04120309090504031704031b050c15160201080621010b011e02060f0a061d0103020a06050a02060c0306040b1c0c05010207030203 79
    0x4201a84507015807001704100d5aa60313100420b0050301a800d001110701075411000e40756100b040f0b1600302000710744850750113040648094680c81103200d050340ca50780d10324180c000c590188050380c0d50200d449100c035443d1903039520a0410090a4202100007403041704001c100e061043c07058901860305640e41004803903044400c40415180a00154280003d07002c50301001521441c01d001130511480180603011805030500c83d485640d141d0040840c00140a660410360521000d0300d00a6024a0b002c84181c403a100400d01c2c0101e0441d00e11402c0320135114444000c0815001564120b1081e40d80fa001600b21007414201c2412000e403250050b002000800c134080c4122060365046200c0c524009181503948200a009178800840d0840704011000108158541045443c00801850910034038150260304000c0d00c8000003085e940c102a8040701207240e41e122540981d0880e000038101c8440040d188050080c0e0a141c0d0004942100a036030010825501c017280600032258094010511418410703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724810287 1250 724809037 724809053
    0x813080d020307050f03090f07050f01021c0306150306051003020705060a090314041d07080403020613060f05010e041b08070e0408070204110a0315050108011502010b0a060e120604050307 82
    0x140000c1d04204d400e12846000504c00ba0003980961801c400030b0812451201d44207040030120ba000350f104e10402076001d20281d0b004100e194030417000c00c04520f10b11001100a0740180500e404c00703541c61303007902e010b015803030b40503444041030b10821524000040c048080441c00c0c2d118114006200d85c2012002c21910242504011003c0b40b1a062096207003131140700c294103541180d44103980140c652004003030f200700d4803522136411603d00d1400740980e2806850103955101e0141c0880c0301c00c1001800c0500717101c0310350310501102240e1202404596940c3e18256840d02c0141d600ba02e000c52824210000c0c00d010b610440d04a600341d10280c40540d280412210b030301e92008000b0740e01140c0801205c0010781d00c5100c2c441e9500100c050a986460308440028110785400306009442c0c18102c0e4240142e03a00700702c54034116003a032020703c8260442d2072030407409840060311140c0c11820500c00824070329041001d46414400c140c500001d1014200e032225640c80d4191405001e40d0402c0142d140824050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724811537 1250 724810287 724810291
    0x71a091509030a02061c1d07030311030f121501020c010f050a210603031205010e18010e0d02031801030203010b0301030f2f011d0f01050c07051f0813080d0203 70
    0x4040d43c0c503c0e82c0540100741150700c0346240f410480e8801131031000c03000caa4400c1346800c100042e0340e0620403c0c1444007694a4080e8040903040c40f00c0300807942e800c64410000c03a80d0200085962503100e50208502d80d000c03500580b00004aa072403000301c0300d01c951002803503d001d030f80c0c140c4d54640c0d0044620410380d00c40c1e11140ba144208a0810100030300401d485a01106d058100c501c0010890f02d181002003052145800c00803d15080c900100068002500076075003058021562444110159030002d005020946c0e5803c03607801085c181e02c0e00d1580220283c03002d0112046103610395281840114101d04c824011a084950300b800140045003a1010200f20141700d03c02000102da040302c40c0640c1c0f40b00e4000154041034200b01d00c05415680201c002000142d40e5110b1803a030201d080024041c400b0111441f41003180200384504614030411141d001050068018503511a840103180381c80b0020503070200c08540c66a004c00c00745001c003c10421340c1908108160704209840a44002039800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724812787 1250 724811537 724811539
    0xe010209040e2404122613120c0519020301020418020720030606011404121401050108030f0f0d0f020d0f050a0e0d0e03120309071a091509 61
    0x10921540c012919103108105036010400014202c80642040958120307510a003000041c0083c6010300000500780100032440c0d98007030a2034a1464040b141c50411104c88074010440340c0b40c024207101070b00038030392590184140540c04589000341401c8003610340c04203e43d0001c109034008541d0302402000e03404510740c1103100400140c0b8060f5940c03070580d50918088502d08a0950000d0403104204507014110a600510441c06600d90b010320300003902c2d00c20003840c0358140400c81c8204014540ca510840340580a02d600405c0d8610f118241600c030380c850a0101800c07580703402d0000c00e4454002094841d8035214402580ca003091180402c91640c0003150001c4055840754042c01d90403405002400c1c481c0d220650005550451541c0801a01c0003d018091a281f40c501846c0700480c1c080f03000d84810169080540394141201c000c82d28048096403040c144202c00710030710400d15408a540400c07150141d4615590b0201c6a40d801c1c11449414035280e0300c010f81c074804201d0b8131040c1d0094206000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724814037 1250 724812787 724812791
    0x70204141b2d0d092019150c1403040315150521061801180507050415030c030809011710050d03120c031b05030c030c0f07050d030606030c0f120e01 65
    0x6000d008040c182e03201c2d1a0115844010302c20034020205c410710303c1e60b002d01070840f0403607000c1090300c502070000c80d03c5004001c481c41c807480b044643e4501403441880890f501c251860011340d071074100543c50360040c0c00101d403101c1e00d1402c0410312aa0318010034402c43c04650103084118603080401c08141c2100b41c5802c000c0c1c80c180c0041c0d01402d000c0c4083c0d4455503e580f88004100c114502207802c4501c0314000703c00c071021061800f004210002072000136030300156000211080480880105c4c400c030b0f40d02c0103110450003d408810400d4210203001d00c43d0003a210801d8040c2101d200d10304424040342c44080009048404002034a040c1982d101014040c0c03c0c522908880f00d5451004e440c0c0540c0304601081d200e500c074074914458101c0c20813030b203110741c540b107411824031100c442c0d404c0c44094441400b240d00031502003040600d01d402c0761840d9a200080328906244405c02801800443c401c11000c28500040c80c04980c1c00340c400108480315a98801e920301d032480481038010800807a010340259 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724815287 1250 724814037 724814047
    0x6030606080603030a0f0c0c1e09200c010b1507021c0809010311042c09070e131410050f0a06050d03030f060803160c081c030203060303070204141b2d 66
    0x8239030b407400300302800d081c4120f6007121501c1c016040c82c4442580c00b440703030301e494104020740d40d600c2c040540c52a2881000c040b55100220b0541c0790151540e00c0610350300080880501941c0002e6000030640640300365481d0101b0000901044104060310001800f11a0200007001817584aa0700001000202c1c80c5110b007403035200c600e00c40c030b084a4032543d2410390403051042007001d0207004840f54807451050040c1500d80c105030550750040e001619640840d04d410601d201000b1410340440d0540c0101802c8500744598248407401404068039100070002d21f0b41d003c507000c079459025a02c04d0311009414020071803042c3d9411802020f903400c00c070600c01d035145400f003442c113024801030101e030503184004410f1140d6820701d6000740e0301e50f51142c00240d1000d0382911650194294a10b4a4115401d00507160390380c2c803001c64214460139000942c0a45000405249030001c203510501403020181d1000079181c00440c011658403031603515102100b01e4800321080ca1040d90718035100b080a003202a4206 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724816537 1250 724815287 724815293
    0x812030c0a03090c180f0506030d081009050c0703030b0102070b031801060f0b09040605100917010b060f0c0f0a021e04020919032a0902030c130f06030606080603030a0f0c 75
    0x1055217030040054862100ca80041c003032414007500707201401c0103200b085241403640001b90303541d42120103c41804140000601303c032000000c100020034210a00788402d281046104c0c80c00c1c2e12800c4100c022a141400007003a035440055900240c440000240d07141d0340752180420310950180b000d400c500d40d00c074074001c1406005c582d6407400a2014050060b1919000c40420059035900e822580c0208490f228404010754460098001c40301d90340c4114442454503500a8050404080110f402c8280001c094441401c2c0f0002060440000d00c161035401c00040510f6448121902d4003a611142c9611001e007001d12010380d0180e03807e0002c2c40180740c004004003103220b4918040106d20045004c00d02007080c401c3d809941100380c42c0340c0c52020300c0007071801240c07c0007032014002c280d038141d4040001140341c034814048519200c0b40443c002019565410054030b520710303a000e084006414940c000a2090150100c5400307920000c02545c1028005d100444c2c605038401d40a9003002003030f54180d004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724817787 1250 724816537 724816553
    0xb0a09020d0f03050d110903060a0908040f080c100f02060718120605041a070c03050a1431050117060301140103141c051602030f030a17010812030c0a0309 68
    0x2c180320f92142900d442040d4907880440e130300307420061b07904001000b185809a0340400c03440d50104802c04001140d0380399003031110395409036400c014100c82603440c0c0418084c0f80014883e01e1000119070b40d400d803002550040382d1040d100072140740540d00c02d00204d113155014207034580f01100c0055000d0301c800d075070380314060341d81891403415035800b550b8200340300c10b00c60f02d01d885032081000b406c002c0301c250402140041403c0880d04024081110215a5852180c800d0321485007505648481c86d031500d0700031035048000e98450710034020070000000080c2c4204003070380c2c0d40d10407290140c54070a0301b8810244103580820300240043d90655880b001d222103210365004050185009681c90100d0341d288581706e0346051111b9a0320301c00e03942c00350030b041e00142d4400d003140d01c071254081240310001007510100380707001d8050030602158080480d0703d1021540c0a4121050505402107807070186e6690000359031130f041102400761840f40100006625661054010300620000b49000202841e180c1c0b15528 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724819037 1250 724817787 724817813
    0x307031e180f14100b030d0905011b050312010e06040c020c030c040f0204051f02060703060f14011103180a0e01030c03170d092901051c1401020a0f080903070b0a09020d 74
    0x56941d03a80f4041740c24101009865030150b0507082c020484c0341071500191003400e060f00003582180001050004000c0c05200740c805075245500b1074149961500310041d00d021046601900561030a04502d25032403000594442414010b40501064443c90051101400b5040c00c00d1901c5602000005a6503c2e4104a000b943c3c481608030118034544501c02400c3c900c0c041c1c044000c160030802c05002240490f004402150410320081c000b01c40c0007401038074980302e1109942c5490201155905942d4502d4040c4495100100d5200003800e03111310003185041800c0c0405480e0003024041400010520807500400030584900a402c00c500c1145100035145c204200700c4030301c6824000da99426680c012219000180c21445260031760515000c11050104074812511703908420f0008024050b0381c040200102c1c08640084d90340e0213203000094081e00c0e0304414900003a03a8840003401086000c01920481c6502041016454640a00c00070143c101040166440045100c0c000e00045031214141b07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 724820143 1106 724819037 724819063
    0x12080717281404080306030c0916050304140d1701080c030a03080a0902120c010e0d0b01030303090221011410030201091a0c030307031e180f14 63
    0x1c0d100c0c100c082c006141d407010510090200c440000c6100d003506030200c1d40c0da101c5a4003841030103001141c00c54028404900c2200d4a03510400c029a04140255090035140038403c052a0502180015000220344904645c611000000b8400790061290700301030140114600c0c04130341c4486144e0001401c1120440020380d418000d13a01c05282240c0240040c600c00c440c403201c90740d4801801c5042c9004c9501d03034102c1400c603c2c00e41c442e9081d80f81e002c054100d40341d1956805401401a901049078041d141c640300c0b000041040300f10040c41c450100c004904c0040d141e441071a0501c0290000340290301c4a0405e00250360442410b400302d030320418903203100d81c0740c00e8045ea5480c05003c115004cd8000042800607941d415044401c2901c603203c52200e5981d400f024500440b104a68003503142680e90f10f441012075121880d805a0358042c442807450f101c0003401c61420700080f07a604ca = true := by decide +kernel

theorem cover : BRFrame.Cov 724640287 724820143 := by
  have h0 := BRFrame.cov_init 724640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 724640287 ≤ n) (h2 : n < 724820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
