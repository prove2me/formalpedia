-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:25.800707+00:00
-- url     : https://prove2.me/submissions/2d03f07d-e1a3-4a0b-abdd-c741567d398e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439568345 ≤ n < 439748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439569595 1250 439568345 439568357
    0xb03060402091b040e0601110303090a020103150f091a031f0c050c0d02010608060604110d0921030f050618070320040801150608040503040b070201021203040b04030906020f0d 77
    0x1503000c000003900b540a00840a14001013800f0404940403d0710384d0151200740c9079500708001100103070f5aa48800c0392491701580217441c40d600154003d4005480c0140d5010911400548980318001502943d41c00810110740340d50040306100e410310a045c000307a006030050b102d40f03042c0708150b103515040070103002801b540e50043d95171814400c00940c0d010070501c20035941480740f0007034000e0180441d8000e0040c030f8000c3d5404100c407031920384a000b44103501c0203480c3d82403600007040b110044c02d00c00c0080e100820000d001c040c901048440d0910304e01000e4400080403c49048035004075100103040600600007104031101b261010418250b004607946800720f210701025409010002030901c0c0040f0a48000c500411710f500190800ca446c80c00071b0100e0b20405540325002c844e00001502c0c0900b03140c100b04030600a60011100607c2d1550041c0100e031802c2e14000c0420106600c211001c1d600410170f24140420103038000100d03401000036200400300d07009182c032801e4940a40d14011801d001e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439570845 1250 439569595 439569601
    0x40305090117070804050f0c0a031410140109111806030411130204081c090326040306090210030c0e1909050709050109090e0705090705070b0c18040b0306040209 71
    0x8420a103151500b0201c010741c0055041040f03014100240c140d03803c844e00d000340c01d01190301000003c1c072044d6180c4001c01440c5e00d03c0c0747d501c58031851060806145110701039958541668825401b41b2400c2006070302c1240710303642c5001120710480702c10b16816045007108001001048aa0600c450300d41203080703078603503942d0f1a14036103964808000031406410507400200c4125141055001e0012204010141c601c0b802040d46520540e2421002c00340c041070004c4011301c0812080c0c4100d0300204900c520300421170301d04201f604603a80083d0f00480d80d05440e008082e0071070030040c590220020072405c003440641c1c401d4101a000400c6051000c1c01143c00c07144400b104440711403210002c2108030002c11003410034074002019142580a154086031400d0300020351b0203094801c1024048400003e0710702542002c0030021007400281c600e2082041c140048000300d9003240c500c9004803e210096543c403885410910071110409507660305c103070300d40280d80301c0e9510003040403079109504550028450b9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439572095 1250 439570845 439570847
    0x9050108060d02090708090c010e1023030903040501110a02011e05070f0b0703151208031021030810080703140f070609080c040603150f020d0c03051b0a080403050901 73
    0x2e18581c01a521001a005000105800050a500400117101500c82103030489006480e40c00310b03102104d400c50300e000301c040416481101c44480c50b140110864885d03000e07481504440d600182c91064050b040003070300700560b41c4c10901c505801100400034001c0d402194001a1200c2050840d121117035060780303800c86600d40302d58221071046074010212648200030f0f0070b00c1d4012040468070400130a00c2c0104220000f0000f800c50350440303040480c418582d00c03680e6101d01e450f80010300400b0003021f040a001c18070341008660215503482000e03103106140d07414280100070000290000c4003864042d0014070607040d0108248003600c0e08130400c911100040f02c407151078424425020300c40d81c0111000031803400e510030440c500b29914182220359040e4501d08200444029102c0205115400ca44a03405490f46030042c2030070000c458001814020382141110540d4441c401e62000240d55404018034000b21484000d8446440d440c080e040c000d80400c06448100e0141010b4144840454203158a13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439573345 1250 439572095 439572109
    0x51f08161101020a0e0f06122a070b100f05030a0201030207050c1809060a110d05060f0402130801060801021809041e0c030506090d1409010306031406061008070905010806 75
    0x482001d000865684000090003402e00408403450340c41031016602014861810b002500c000c0789607802ca080894440d030f00310192804290240078a440e80701c0904516210b9400301070020240100440700442ca4040e070710000903540781e0080c0120500041d001e120740d40b0005840500183e080c200145d4401603802c04c030b4540098500304c103911031002d4001d4400c0945d0f0311501405624140f04503075485e2107180072075050301d14110304901c010380c0912002e166150903402040d0410343c060028502d1450403000325060380e0210580000304c00044808115960742482850010041c8400850a2944c030712040e408821341024054400c10f00b50740410306003d03201501c0ca84040300e00c071340e0240c1d25069160244090540d4807084e500e60042400080c524500031070344104c40c540e5a590358a140c9801c1e0a010003640003950614101669907001000185141c6180d81810407148014405460300c07008110540c001c1c04549030070899620184420a0f420603110020b440c000d0802c04110307580d800208140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439574595 1250 439573345 439573367
    0x30906050c1203070905151602040f0f050f01081912030c0908031c1103090c0405150306040c08070b0703020304150c0515071b050a0822060504051f0816 67
    0x3500c00000744500713550400c0900c021180199000c00003aa26520707071505a000b1a9002d01c0709035541c0d404000180340561240201c418090310005402d000911541c0481d0011103034010050030580040c00100410402c0704160102580305015400d5140c0c2c0340c042114510074504140364a0304c0d0032002e03082c0220398201c081c0204100712900c4030102c00c140200fa581ea1902219480e10303080b17406409041680840c0c0c494203aa0004004804400c81440000c1600a104200341402e441d0060300f03e950900403035002c0d6024110a1141034184040c240c1861019030200c40894801c00907000000e4003c01a14122004e00d012032404a2608400b0f55541998183c010200d01518000034400d0040c0e04002d4003035042541c4103800d410440846000c1c070010448007404641c441501140018400d800422620720b8a0807600c0403001c0080d080e241a0109401002c08a20080b4080c030490400300e658400080704a042d844080015001c0980a20310250442d5580c50900c14128440703070082d034405c0c1c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439575845 1250 439574595 439574623
    0x190602070c0e070c060501060305040305090d021c0b1017071517010801020c0f030c0703020f060705070f031506050f0108040f140c0f04020403080a050705070e0106110606010c030906050c 82
    0x8840c3c40c081100503d410100002140d0701c518140002c11414407a05c45c141c811681602e41c1c6280c80c2c0c4101c200841201104d501320780c85500d41a100c0c0c010440460301300b6103244100038211141c20004040020101641c0051207900345800b2191512400011988102c0716000c084881c1f040703101e101162014100210449000ca441d0000243e600d41503004003844041101034500340030243e81c1841e1203218001c10300d101980544810f1000d441d1204000e403101000a00b054540002982c85a081183c903034004c20100c00084c000700103108400104402c03c07140107104200e424107140004482c194000d2446041040000002e42007090000104205503000100a01800d1814841550313070308406a40a00034152514201d0b403a003414025a02038980c0310031403900f844014142101c55401121064500e8070070807000255006203260801c2c041c04059903203134054001e110304030303150080103040d4070b0400824901c1103000c284c1c060007080c151141454081d40c1d52404115041c070b8805c094003080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439577095 1250 439575845 439575869
    0xb030709090c050403260d1d0106060f020714100507020f09010906050111070e070507050a0b09010617030909010504050703020705012309031c0f0f09061409190602070c 74
    0x40c85543d004030241044038811140c0710146181c200d902c248051070b8a402e803130b56a0040c050700c05c1c200748030b0f004080b9880c00076a800c65982d641548031400c5d51383d50f6001c2e001242071800803040c420b50520a0b0806172545500803a1420020700c00301c0d4105c828482c030181000030211701c040071940d610000310710049009040d9080b07940c407140c0e140020a5180b164038081080100100d062060201d06202141e100071209034450f40d65503000c0d109a840103c0488150003411b9100000a000d80c1030b51703006603c0240002443d43c00d00b034072540d005540050f8402c107540f0030f001e2413100b659188242410343d4400e460202e40c9485501041d4081d009681b002040795080003c04a0641c7c405040122a102e080010701c0f21a107a506016450340301380c14040d03d100f000328006400d00301c1250800301c8003203082640050482602440441152100c000465003e6103598400074424040c54207107401a00a0020b0441c8940c0301c12403000c00080803d000b44071540104100d800e025050050000500140040b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439578345 1250 439577095 439577111
    0x60507050d0f050108010506031f200c030a020d03062411010c17060a030309060c020604030614060a140a0e0604020903030c10180c03030c0c0f09021c05060105040b03070909 76
    0xd64040c0c20f09005211007036280038001425071030006807003258041d0401480303460150010002029186681410b00c80d00e207884014510709401c0300c01031840400d100051a114241c03030000034100983d80c0446000c2500342801480014011088124085a035003000c1c10181030382c0030b040d43e68002d0300c0c1c00d6240b154a010306040e00740360400380c042808007055003032900a546403c00c0119420860102400092580300c0074071113180548030603007950f0b000401c200e042c10ba40c0c2c0e48003c07c3d03582100303403544566503600900ca004d040044c41e51002d172504c0d990382e00c1000c00c814003041c4144498032864000001450105000da1a00e5044541907040036017035a075141416500540c0d140341c20540c152009203030107181d544000b0000360039070080ea0300c840c81060311881d40d00c0468192400c1601138682600703c800000c3c005858a92180c02400d807154096160a003038075427800c4a44141e5244d0304035609110801416a0741714044405981c184d10010f6200c2e11004d030100c9060065400402301300740b4202d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439579595 1250 439578345 439578371
    0xc0b16020a0602043503120702030c03181003050417090a030c0e070801080a03200c090906060301270201050c0f0a0605060a150c021002251a0a0c060507050d 69
    0x440f5100020522411512428092815107000c008a105d610b903400600c12038158207803094525402c0056481141d09191036800401e046601c0502203010020b20300d000d6400b10b0a15001c03401c03240c82176060811040c54940c65002c45030404030924560110b0025208039581d0784c0d040c610010f9500200f601800d10f458540070000203034143c607068003240c00e2000005100c000060034002140e410790310480c41d202c14551032401d000200545c4030726030140200b0064517481c0d04040c00c0c81010b55034020a0346003840380c14903003100c00e180040000100210843e40500c0804040303000b082da4203182882e035411105196504041c1089008031490040150000c240412600550300409045035001c080a564030a80c1015181c081c000c400410b0401c402d800151070700d41d200c140031010b54010766000003029090544022400601c000c0c1210001909022409030781da404902c000910070203900e07090302408040c0c42d85000300310040926803250006890f5901c50801e48411001d4014140011084105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439580845 1250 439579595 439579619
    0x30f01050928030e0402091503071e020f0613141507090f050f01030b03030c0703081c05010b03010306110d020a0309031205150f030106030203030a02030d0c0c0b16020a060204 77
    0x810302101001c2a15540301061141c02c10301c410980c5510344a8841c0b07104018480a900725011140e44401041c1e20802c441c035201c0e0040d8490407050340c2c1c180748629803000210b109410341c2060411940305044015254000295090300100c251411031000543c500c0c08400d400700d8040314006a003d00c5204a0b914a00729036898050300307080d01c4002c406a120151a05250820300c01e055005209420b0010907500942c06071904090280aa926000c80c0815007450b2071101c4d4400c80c2c0250000590b41141c540f8011400c101c0d640d120000e021235490404246c040380010300015040365512001920010907800c00c4030130f20402c0c1d000030342d100c52440c1400740003082c058800760003040c1512203010103131005d4498039101d0165502c113401c241c480d08040c40240c8400000381a01596035510100241c0e80810143c011400d0650040d642c6104001c01030080d6007541c20400140030100c030750140010605401c1c0e03075024401c5140c2c1350b60264060412071811a4040c80030304103a100145c00b14146040003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439582095 1250 439580845 439580863
    0x3311103030c03070b18150601200607050904050a0606200a0605100524030114040207150506100305011a0a0c020a032d020a0e060307030804080105010914090604030e030f010509 78
    0x48404c400c44040a10301074582c0c1c540701f021480301940314009040da42c00740030310510260320f0448040341c07001410380c62840c016042e99800c0c081240840c2601161410b401180d03030003a030301d034010702042c0e10b0004064a03100800b8082c0340b20210f004040c003907640c001c00041030526003150b0f040c8140e0401c0481c082800c8500e0041714040d00c0307004401d584d42c1b0210600408110700c1841c916103143c5c07810400d00041d0f00c0310b5407011340c029020040c1c1c1010400d0310944070300e24840d11b540058141040e10800120700c508112140030700d400e001c010020665282600150034254000b9965038048080e0225410340c00039000a621452507100802840846203015101518220302120911050500d80e000a580c0c030034001d40c8010907040034040c208112041c0b03500314001600711080a0703140c1d40c0380d01e00c940058020220903903450004004a0040b0b000c2e11005031039044c140801ca0401001164483e88000c10190074080d4800c2c0200c003a4500300141410302a000b4001c00c443d040012917a502c0d00044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439583345 1250 439582095 439582111
    0x30209040b01030516080a09050f011b081e0402040b0d030c0b0601111c03020906070602070b060d02180c04051c0b0906010608010e130c06030203311103030c03070b 72
    0xc0c102030855402031180e0385c016240040a52801c201e00030003126183c1d0010a07a4621607280c40310200020010040403480984d8540041840040d03000c0500c0020080228070701041304240a00c440800009144c080060014451030b42c150344a0001c40c01404030240341d15001804401c0d02c10600d40d2184004104500c60003503c00580c4580c0300444400350011807041c00e0790000c0c019201c0e0f42c040388075031218140480c1400b40c20b184c80100010b42c03071742056906680d41500018240d041100904403107502003c1250120b040c0d01e0650042102214200c4c01044461110404a00c102d042801518010000140000455080030b0700e08041c50075915011200f01c00288045212100046070f4076060b6902980e900c04984c0c6030020000c071002018040440b1543c4107890714000c94200d415460180000b44c8000d60f43c0d0402c950b903001692803080420040c1401c090101038622044030080501c180c12902c00c01e600c0092400090461082c0e02040c00e0034400080c13200c04105090071a64030407908 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439584595 1250 439583345 439583351
    0xa0f08100e010605131a040e10030609082805030c1303150b0a08030f092b080c0c120318030c1f080903090604120305120106050d150e0417070803040303020904 70
    0x41c407a00368502901d0750b9000d0342c1b800d01c28007007030110b68603c0359265484451001c00c1981c443c0d50752210360441c1d45a010548410a001800c034003c106600f6014802c5007030a0f035488240c0b03688103030040041c04090420440908001440b549210300a04000042c5412800901c207410b0070400c104000c0003035403111070052807280d90000b00d10001005807114a5014042e15203007505040401c41c10741c1e842c03182c4c944031030358565003904604414070b684000a0f10800d0311681e02d68240c0d07030980c98510242e51240c4a804c0c010003406064101005460b942c1b000050001c45000448002900309a2002e070b90503008034425040700c0c00010820681e0200701d64503181d5502036141c04525907204d05c504082c09030041000c00c400c1007565807e036070310740f030050192921509021902001d214600340a0b404100007070310201c1d00120359607051140c0c005500c60032403440350071450007001d2000c0a800a2000d02400308031114200402444000c848419a2110407503550307207041d02e0080d00941101100354003c0346 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439585845 1250 439584595 439584599
    0xf060c0a17092718030d020a080a1b09150504092f03150d1e0f060c020c0a0b031f0306090c1202090406110c0307030801031203020a0f08100e01060513 66
    0x1000d081d40d00704010303d1091503000365100c002c03e02605101400f025064481080f4144800b50944040d1150391300a43d070390501c5061940c4e000041c0d07a1008034064013000c02d42c0c070503906144c014800d0011210281099100c040034200255441d0045500c0790840c0d80c10800244a01c12503401c81007210f00514800302d6500030030f1a40c01a990000303c17105005600859050a040c3c0303403078008601c400e44103000c2c0d61001d14044c0210080b107002c3c00011900c0c44c881c0f5040004103c0c407801741641000b4030b03200400d20003114400140346d5001501c00c100c001400000407504c0c0c41341e194000c001109440812956150f0789242410040191860a640090f1001e00206241d20000008403096400a00c101c00d1600c07143c454078001c240c0d00300500d4440c2402c01080c80301c80401c0c40600412800b070388074881b5540c9541400344005903852050402c0520401059000076040041c4030580d500390314100d0460381d100000c00c0203a00c0a504202081c42005000180c480e03440320040444c4e840b07060000000c0c076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439587095 1250 439585845 439585879
    0x30f051b0a140d0c20040c03051009110906090d08030c0d050106020c010f03152105060a090b010e04050c15180121020702040b040203040302010507020d0504050f060c0a1709 76
    0x10207480414400104d01940c44004a02e480c4079085034007440124007105070800a0000c3c080352519801c4030046a19001000349071040c4090b10401030410311020320125008202000051048014040c07040d0804640c042c4c4648540007210407a9911100d40c964034181010082d0850f0090382d40c18640d90b04040001ca51a4400b02d1030600f4410103856109080754504000d50141c8505100410480d2742d500000519401c0c4140c05142c90fa0b03980010760021002e818190304040008184501c0c26050425480001d0030329100f9070b044540a403003000300c0d904d9034904142005400310f8070750703032207510082d0030f16031b4901301c200074041c403240c00c14a000424201e00041d54502d654000b0110f445041c103800450308000c6400130070140f0300c01040091404d81c12000030f0102c4c0c1046c2d4054005039500c00402440c40d4040045480d040e20360308255050514210001c4c80680d51002210b000c0e600106014054100412100c20340c2c07541300c1c028840c00804050700400d00c1e04045055482600c2400b5000325403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439588345 1250 439587095 439587103
    0x18050309030d09062c1021020306060403020d020102070909030815030c03060408090d0f060e01060509092a0915190612020a0203040806040507050922030f051b0a14 72
    0x9800320b854054482600300b004000f0100394108055040172540452126a5500e00440560400030303200c04041042c4010141c1c8124003080100301801c0c4104180f01141d0703250001e0310304699040743c1c2002c1e1f12550b480100d06100869004640305810820070318200746d04081c420780315401d4000c00e2402c0806402c00c00d5611040c40500540642240002c46c010900342001040964809801c010076425241d84800841904034407e8030700a660f010700103414031003030003100700a0008442d40d0b016418500d00c055242d840402c582d004103288200740c0c40645c0381d08031001e040d1040003003800303040e807602e07001189210385044800c52155001040d1070079001841400035090343c3d545e42d242d202000030240402d000b907200882c004c00350b2006200000780c5202c20414036226501c0307000900880d52516003480f12892000e001c003048850a042000c0f58880410f41240d8015007500e051810000d08074029121440760212070810708901e001500800e0341d0000390040014864205148000d401009054403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439589595 1250 439588345 439588349
    0x11030105010c06050711150f0a05250c020612060a0e07020a0308040503040e0108070e0c0a080c0706140702010c08060f0d080f0d02030f2d0c07050118050309030d09 72
    0x1003400c0080b242d02003a0141d10050f0b00c8081414864442091314074414075205402400b856880360842c1000b90b04000c844030395070003000c40c190902040c1013010001c04140d40b00802d00b000d9280c0201d6002d045441500c1c0701d5003898000e420300c0e5603801040303484070003001d044500900a607000a40050400051801180704400d40c1e4046c01c0d0704455550304407403003e0064400e51740c9100a200c0499141162407405000740341060081007894074103019146620700042600100c0c0e0350910142d601541c00803640caa0004804003401c1e680d040c0c6140000c004d1203000030540c44040c1b036400f0007104540551207103444110340c0c0c890044550b01d010811032502ea0105595070480701c285a50000280c1c0c03280038242c0f8116482d801d44c10424484030b920f049030012520489102e00031390600130040d50300c01941542c00e804403c162034001c001031400046210150040c01d460800140c08000e001c0c0030350000030000302d030009e03400d01d0f16078030300301140c4c0d030f801c0320ba5800e1090240c40b004051130341c000e06100003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439590845 1250 439589595 439589597
    0xd05010b0a1d090a031b03120f0e060f04030504090507112a060403050d0c050307050118032d050a02030906030406092109090207020f04051003060614060f070206130b04091103010501 80
    0x100f104400806d810304c0c0c010080c0102c05000000c10f640000302154014440c0851079013074006408841c80000314509403014054804241e40141400003107544102280c00755600408041600e4550300c104031030802c441a4000098084c41c2e42014030401c0880f50004015075611001d444081c02104000e1903101c3d03071100411542c4043c00415040e4001c4103540341190083e01a2401c190072901c5241c2900c510544045004c00c3c2e40cda61400c2540000000360145011000c06180703051034400310440c08558009403061100c0464031100305882001216442000500074036120b08040c507010000e0010303070b00c0407501c15041c54901032000d01c1c04580a2070307046565581004441c81d2108950003503020b8202640c01a1507903503907403042d0300c41d030040310700031500030400806840c59414170b9001c94406030004071041ca00000d100c82e06545020580e12510440b80344030359200f10500c00504280315058092015001c24640000e601000300098021600840c0e4140003140d41c92501c200644800d0054034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439592095 1250 439590845 439590857
    0x71d010201060f2102130509060c0304080702040506030c030a11040c020127020118080a11040213180e0f070609060302130611010b0603090307032c0d05010b0a1d090a03 74
    0x20075802921044c5881384c1e0040151420640030384c01040c030300c19100e0307074071307400e1903207039814040554820020700e54002481d411a42c20750038035554900c200e02c558003002c0d00c265140c00c040780c41c0780e4090080c02c1c01500002c0442d011850646080118001c1d0600001c0c030640c5441c111107a400e0040c010b0744076440034100c0b407070215140c0c01080064400800c0050b410040411450000042680800c8018100324401080160030a00d4004102115014007078003850050082c0c1c000801074a0800040e20900300e5081c0030b0700325a41481c4018285080c100c14035129407103540111a0b00491450259020381e502c4010540e241c402c00d0302a13100d0880d40b030481062110080114510501214039041138580c0003091512203040002c081d03810540748113444d80c0000030354000f0542c220402030030106081c0c00d51141104100f0200c6024120700c02c40c1802800321090a6041000a40c0900b044100050001030800d03114070741e160007061f811220240010b00036003c29840e100000c1d0001b40340754540e80318 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439593345 1250 439592095 439592099
    0xc09050f1f03020c030d0f0c091a16050304030b09100c0503160e0a0608070314040c06050a09030f0c03021203130302060c16031406060d030f050307090e071d010201060f 74
    0x2041c415010800c18001c0550030b1003400b0b5034030300c10300041c10080c9008201146078180b55018008980c0c10b00d4280e000e0044200c02001514100d451144401d9180c1003001d46810103200c1c0e0752080030303188074001d065000c0080c000c0200440d89244034000c4100004444020f11842244003c03180d00c4610480840c102740001400b40807034104509185030203161800b1507114050201d40ca0102c1da800043c040f91021041090540c1d1502c511201000c441d82400141c0c1002d49070200c07054424040c050820a000035811070307941c007601003040119440300d4030300b15048841c10700c0b6028407003078041203128503407000c81494140000400c0c1d850a54007180c10042092540d82000340d1a8009924603106005007922001580300307080042000714090f41502002c1d4403540842ca0810070004d1425210314408401c000110340c0c0910340707036104844c3d400e2084c0c2c0c1c0c2d21020810307a11004598003084030b09600c54100aa00d541c895001c40402c01c4c1207030034000d04030740e0794016803c1c3c81081c040c6a041200086003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439594595 1250 439593345 439593379
    0x305010501151e050705010f0506040b030114060f01050f0f070b0f07020c01080907080d090801060509010b0301090905010f020a11010b040506150714030301080729041203020f100c09050f 82
    0x198103e0029080c6036213451110f40da01c0303081d590110011403600b81d41d03c0400c4181d04007401807500c1517000b20000c021001c002c1100c1242d01c00003510746401660001103074074441e4040e40c02c03140100114058242c0302c407980310b401d4460f5806400111401c03030050000c100803001d200b00660084540341c01400700301155000440b1024002080400284950400000c466505014070001e0241c16925035078000e0a0a203042d0a458090b0300c018000d001d1140100020105003082e01e06460940402184201c41380c00e00701e0140c00d100c0c032140f803010310001d421008507811601c03039030303401103204003e1100100940030441110000c4a40c136400031804141e06100c1e0035404014144a442070715003c1000907145441c0c3d2442d0426000110140e005190502c90b990300c10729a4080400318200c02e80702c5618000c150319142c09144120311392074078105854800c260007484a0380c500720b203d0088820113450110b050000d020344001c0c809c0401c0a040d00031805080665504003210b90140418018515610b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439595845 1250 439594595 439594637
    0x403151a06091801090b09090703030203031305030f0a08011d060a0b1b120c12040b0a0e0301140f100602011826040306020301031202061e1509040c030501050115 71
    0x50b003183c0c88194002410303440341d030214007070707001e030000b04d40c0001d242c0004414070800c0d0130b0240c41032150340d01c40da07402c100003540041202d0380f1241d101803046803c0aa40740c490b10394010b041d100a003034100401c0b461091a4442c0f01c0d1412140014450194203031450444190940c00382c0e400354006098080c10302c440d02c00c01c001440d003506050031140780700306001002810848100201d07105100c0010f8030880809040009002e440705035980d161a041c038003010241c0768460405427000740101e003008a0710301e0340c00313510000324101034803041c140c1d514203020f0004003480b0407902c1500b000c100e034070003140c1244148144055444040703180700c0030b80001c3c0c88036105000704260020003c26908103183c0c0110164000e08000d5100e81c0025032a9411351500b1049c00600781c44500031584110b041140d00801c4546512010f41c070030a050f00c0c19100c1c000d2101a51000342c201a030032601600c20302c0b0030000e0b800420380c11240502c0080149076220000d00c80d800d0150045040080c1000c41d854902418402e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439597095 1250 439595845 439595857
    0xe04030e0a0603093507060209090906100323010c030603212109020337080304030c0507230a0522020c0307140a1103030a0c0b09100e030403151a06 65
    0x5519245205c068080801030340d01102c81107440039004544180c0f03070f0030044400d58001c22004003030482440c0c01500c002042c2c2c4a0720000d44400c185607000200b00b9403e41c0318800c00b00c9030100901c62a1900d00019020304402e1200f180c01c010b41c8044410b19141020b0500c00500280d42c0340758280c85603042c505e040000503005130600d07603591184600182d504024200000360400c1c1c0349802c61000c0c075040c101200c1ea0304d4007070864005140c0e101c00022034030340c1180d600030b134541419907180803541003c2d45041c0322500030b03103148421506200312074100442403002450003100d410303001c0c6855400780b03c01075030414040106542d9070342c591144c852103600940a84e50040c0222402c0c150700d5268102105d40c3d040c440d5400380c000030007140a101140c804c0b5028048241c1c011803405030015001401540c090502421811807100480e00c040001d101c0c00d404145050b00602064088203100b5171280e0041c4011262490011114242d407081c80c040c070342059040502a0300c44034614824040c05500c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439598345 1250 439597095 439597163
    0xb0d0509120705100501080a02010c0308150301060f030c211e1502030f100311010f02070e07020601170601030c0302040905031303230f06070e03070e04030e0a060309 73
    0x100e1010501c1d00e5140e40501032090040703001380599006520550100c680c11f81020306150007494201004d43d030403540031a42d140d450726002c011551000d07424081c0441e030114981d415401c1c40000140907051065401c10350f40510100d40a06546200c482036040d106868091031542c28003c03000454070408140c0e80344928840d0400202e1000d550b2007101d80142c2010343e600e65404824001130b1000030003065030080340c020300f010076513045840d40c1540707400c1c9041c0c181c104042600d4540c18207109000101c01030183c03101844103814030b850047c2d01c4a00074020704140b03104043d1000c08200c40021482d0403660000f82a0759840c0c00c6409001c054001c00a0a0b100c1e8881001400f41802d91115001c0055000d121107078031800c480f00c0c0120000c1100c1c200c040180c1e00515a0403041c00000c256150080e00a08185c90150b075036101080c01c184803640400301849401e800c010905400401c94804080c0c2140c1400889031a858154200d9640d544050000c081071602c480701035502e420b803c100000c0c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439599595 1250 439598345 439598353
    0x9120307260f0d05040309060f021005090304080609031b15060103231305061005130b0109031506090c0f02030a1d0307080313050402030402030a2402030f1b03010b0d0509 75
    0x28030742d41080c2944a002d10b1500c580d41c910130030003890341c04a0300c00090411441c082c50965a10a402552680004802281c0603983c0021400c0b400d0208101c400030421901507441c40c0c0f07494464142c5a400100222040064542440d024802c0110341c0c0402c0c0c0644880845158680c100110014038036124070f05541d1344034410f195440e410a242d0188541c040800c035500d07030a91484d1580c06c1140c050900410045180702c18062a5210440c41d01c00c2c1d11140000500b4908180040f101c1d034806500180c8010500082042c8100007078001030161001200b09210f030010182c01101d1000b445443e0200581007844041605440303208041150306000d40c910318003c2140e0f0009003060103036801003041d64000100c4848404000c168030f001800125811401d528041c1c0200361600c1e0f4541e0010700c18008041030502c00c000300c4102020b1010306640c210740764030b020038145180040503100c4c211001074003404011400e02010450307044c0d90a0500c106e0422440032004000303858003400740346190007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439600845 1250 439599595 439599607
    0xf030303020d291807020309040b060409180501061a160311030f0c07050d05070b0a2a060b101d01050d140709060302040605040605030c130b0912030726 67
    0x20b6000c2042d0140300c8200030b0f211851005004002030380daa007010345564200382c1c1e020480078907008020b4a00e20701013600c02050107c05440012814842c42d040450418640389003024a00212100c80f561644204001c01c007140e12540342c4e02c07804c01d5181e15000028420410348000b8408210300e0f01c101171085c10302401d007821841c8102c0c1180c01000c004461000040344407009001c00f041140010101034852148120968403695281e061034000c002400400150407940207200d0008008a003907020510800000080996400100d00d5502902c03000c0c10240140c90a00d030504410f101140380380c41e2100c0c0030400900140ca0700c000e880d101c6060001c01e0240d0791040075203020b4000d04600301d1407822142e02e0805000307001c005140d0845410140705000a00c603081d0801c040b18207454890601584984d1008440c2419102e114407403000c82060103c00941c400d0b4600c09000310560807182c1c411014080b800190b0b80c2d01500201400d0070500180c030014a428041c44981412404042d00349000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439602095 1250 439600845 439600871
    0xc040923070203090f01090b0a18092301141f03021b060a05010b040303121104090e0d033e07050a0f0209010b030108250f0902041a040f030303020d 65
    0xa01150791001582001800e03c0079454041c1d800140200d0900308607003c14104450190700307001d0f01d60010309005607004c43e404116500c41903c030040142142c10b03c124420450409442032800d010b440448003010004107407901c3e82c29a5010071203003d80700c000100610b0803150740706401c0040f010f050560820185020150041e0003102c291030800040502d4103041c0c5c4108111a4164005c5107500c6084c4814400079a100102507000307040101301060020310102600038510940d8001c2c2802440e1440c406055080481c0c5040d0340c040c01e844c2084030009008283d0724080c060645079408080c1c0e091030b00224455501070454200c500040a428801207699461801c0241d40b0143c0704544c03101501740440c0f13840ad00d641c0c050400f01503501c2c10355140240d0039940300c0c2400e60b400092038590a803c000700d0403900c2103100038810b503006c0c1001c443d0b4401002d0001c0d070007402568061101d80040d48007140098080303030201e031158040030803201d145132403c0f0000d4005507800c40515448000c0e204043d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439603345 1250 439602095 439602161
    0x50d15051003090209150d06050a1d0f0105090d0e04052703030f130b16020a05060a0e1006120b0a0e01020a1e09080d0f21091a0c0409 59
    0x20715525140010b421481380100001020001c1c0205d101410b070140d880020307116982c0c0c1d0769039144d0101020a01d51518200400600080f020281d40034560144100c03103c100080d58510b003c81c1400200881d0710f42d40d40c1140c445103011403c0010591200c41c070040c0381000d0780580da10a00514103003240e8012800b0300660701d5003d010300641d590012040c484c0c10603076071481d5904042002000004410103a07119050101c0083c8110b0000e800281c10308ac0c0180244408106d15510906580ea24034088143d03800419105d8101d031541d02c01c0c501c01d960303100041d204e1a000d035429103004101d080601c0d6290300244030020300c4412190745a818480400c13009001904a44c3d6043e1140b21402440c4a00301c003007200c03503540500c10172050345400c01c071010001c101480317050b40c80c0c900048601d035003034019240c009105080301c1d508141c1040c0760420074440d038440281e2600c901504110643d00c1084d0810004c0d06841850000608100c200080f0030705038040518002c0044180b170340c8440022450300a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439604595 1250 439603345 439603369
    0xd1101140c0613030206070f170a090506090615030c091b0c07060c1205091003020d141003110108090601061b14011d07030803060909010209220f020406050d1505 71
    0xf03540c1d030180e4640f003010f80502c1030341ea0207050b6107000c41c014011034038010101091440c242003c0d0080e000400d654451a07089050340b41c1d04402252814200a8480d5507159411210500036500310f1805080500c0c003c01c40005000c40240034441070386942802c0203101422080003074460309e0400c85c40f44449018404a001041c0c21b0302c0d080040c240c9800c100403012030311401a400c102c401c1000d00b213113940300c88400d50417854915005844d2001c0e0400b44004202100d6442411280041003100c40c941d07804554040d240f0030718044029a00351001503440c01c00c240d81c1c07075000380c006c0c2c401403121502c21450700700c811f01e504440c40c900c44103d48600300c6503407515801c00c81c00d9450340220040f14200420003612210481c0c0200091450354070340301407500021300390f00d01c034500210100301001025019110007032001071072278450b190100d444010743d4107034454002c4c1c0d450501e0340e4000e021502d4402e850440380151036031890102c900413008001c0c000d5103900e064001040d4008915a2034143c04c6041c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439605845 1250 439604595 439604611
    0x6070201051f0803120a0626151009090302212205010c0204020d020702062808010608010b071401020c010c1202070f150b06070f020108060d1101140c06 67
    0x150900b0b02c008603402d000800415003075580034a140410415000204840c403a903200429010182c0301e1b20210300c040e02590b88441e1000780002c42c19003000354910303100840040503404945100c460300740480c941a40880b180c1c00c155090003800c001803003140d007101d00d00506c01c1c03040c0c0c2e0b03404104c88021121000c0b50041c803107034513002046542805400790b100018031101403032004845480e02c0c00003024100d0100e0024011134010940082c0e0b040142c0588550030750041041d0b44400105074080310354882d18074041006440c1d1140805580e00452046050794200da50300000e5078200b040b8401c00380d010300d904480c0322885030f0303808031524428409401040c0803100040303501c0100402c02044469965a00e400481c81000040005643d100110200e02d034000030400d00ca0580b90880d100428080025641002c0001907080800c204412015502b6100740c940c04040c1c1c6038071007407150b01010324a0042c804005407425050543c01142015070a0702881001c074031b0840300b60002400c10a007640d07056 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439607095 1250 439605845 439605851
    0x2100e012006070f21140703050c040302060304110a0305060603070b0f0406030b0604030f030f12091703130501140a1407080a0209062209060f0515180306070201 71
    0x484540c1d000c0c0301c020924128880c0340c4900c280501d00e054803160064000c10500820140d895811401407680c070b120368603a01c821040c08118607513140701404010181100204014001654842c0640b21b00c030301500045200504150a50342401003507400908151081114003902188540e034800c0c0b050045c504ca000508100d05180040c5403428003103410240c188402400328400e05100f00080d1421500e403840c010404035810f0006c10b0741842140c0020f03055a00f0030600d042070517044034500d461040990b6506107200d1150302c0c0788003210f01c07080008001612000050700803003955405950031110900c22003440d10156500e071401c64803103080348900f090b02c81c004c0117030072100b0341700c4c0d0141c3c2419040c10740d49900e0441c200a02c10700000b0003031500e10754080b85420403a2550001e541f403001c54414000180340381c032450b40d00c80042510a2080a60821001040d0005c10300403150890380050258104a40703004000c0380550403003519440c40440001c0000c810782e4003004241c2c01848070b60000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439608345 1250 439607095 439607117
    0x50604180f02010801060c0503030a1505030d170106030b060a03050a06080d0206011a0307090e0c0d060b09030c01110a0b04051908070309060206011203032a20010902060403020d0f0210 81
    0x241c04c2c0007059121105109030625858007044001c000c6035809050500c00044058103002d2128400065420280e0544507070030043e10103c0c1c2180c6072148010389441c1c0041c19a90301d4008a090725007002160303421840900048070954085d40200d50001000c50001c9840e64070380a0484c90048100b55610042e84620010065002c0c0ba0100c0d0107401d01c2610303103603d1403500c1c01001d0302c440d0140c4038900900c50310034001aa08a030f19029100842c409100a214503680c0b910180000d800c00105603201340614000c42991b50f0113070303481e4a403902e40b0101034154018252100200355400810a45807401017000100714030101c0151106450320070440d8507112039442c200240142c4c280d0308840c040d913104100502040c21030055040c1d4156051401048130002c0108040080d100103091000b80070000c1d500d1403650750000341000d5000c48080041361400c0c0901541c41c00d80f10042006074000d201044244054107043c403144034007078051941c0d0700702c00884c0e03400300341503014800800000907180b03411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439609595 1250 439608345 439608347
    0x31011040e010e0105300a120e0a0807180f02072d0206030a091109070503011a030f070f02070b030109090212030a14090f15071b0602030706050604180f0201 69
    0x950701421183c40b5440c255814403001c949005800a800070400f0304500b003861200c0517912841160912100c15281c8005061070160010701d900d0b446040840c0600640b00d405007401180c50045884003001408100d01d0407011202034512010b02d90016074403002215071001090006040b858894135900c5003045e801ca04111350b0310309549000d03001020400d03002025030f881d1016250054441c3d0130003d0366081518180354070130804081c030390300004001e0070000740d40d401001450482d040c3c142c0103400401580750f4426580b2003100c01c011403084880114600700c1c4611050030110000780111514a0b48892106005400c04d80c0149495501c2d24918401c6040404a4050034207074500294100111100041c020440c0128680000f80e00424a6441d5688021100345401380141164400003c250001d031a664004081502c0c9030609400000c0d2000750354208900b29440c40d0b000d1410011165511000b402d0040c2c083d40c1e115403620b40b100104054910034000142c0b240c00034210000c19840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439610845 1250 439609595 439609619
    0xf0d0507050102070510080705030c04031a0f0a200309030c100e01140105010c020f04060f08030c0d0e01050d020307051b01150618050906030a080309030c210403080903101104 77
    0x210500844070355000c0a06c2c2c41d04103400c0340c1c102055003442901d07aa80c4038515005409a6403001c5c084402480c400d20601e01c1004100740a0940301445040644c2c4100158041d40e011140d14140c0300b01d04209441007412090107190090007490582c0d00d040420380f00a071a00045003500c2c0e03121a6200420450482d0904c50700c50050400c0c40415901e6250200203441c0504607040a40111004030701d02c86140d45a03442540680300540d400c80c0e8032178403154403695035080385d1440c171150303ca0480c01c1c0840900441003140e000b60140d5985141c0f14001604030b02035040a0f060405124051050b185042042440c9001d521300b440000078803c0c050070010110a504c80d4041802d0003c2c1c030030442c18450250010304162030303042c0c50700d62103610380c1004070340703492130002028044030b5001c8140041180040002c18810128004503550900034907000b0301c001c031000f0010741c9a02400c010810005020304050590544012300781c50301e808080d40851f040d1501d03242d00780d880d1400020280b00b4482c2c08a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439612095 1250 439610845 439610849
    0x5091605030706200a02030111041e0b0901050f090405011502010c030c0906030c0507021e150309030a030504050c220e030c070509281a100206070e0f0d050705010207 73
    0x100144041458180b0141015100c8500f0205150802541c0f0030280000c011174509268044c00810240d0303000e6050f900150403a0003510720b1905c1045a085101141c408050282c0b00000d008034540800d80d8010b584550004020f42003a64041c040029281d0f51849aa4000c0c01c0b411042401d00250410083c01c64103103042d65000d040c90b1401c203000e0703654000d0b01c2c0801d443c01d0341000140d11004401c1500c080c051b40700c00030b61100300715088000000e0a24907240b0380343c00960790100c502031282d41081c59404119410300050740248480050a4071903004176400601500a607000c110001010500c04612800d540361844048811201110700314802c501006620300c02440c06c2000c50500f05443e143c2900c1003038480c40584001c01d1079610510050b94207035003541003681c9081c21500c0d610019090809462000da48418666444c904001070301d4103800413140d003c3d240d541c1c0d0311001170380c07500403480c074580e04080c259003503041d2500e4482c0c10b041e2190181c8001e1420034178000c002403800b1056 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439613345 1250 439612095 439612099
    0x112020d0b0f04140106050904060e16020106060206010806220b07020f1c0912033006060c02010e150906070804030b010b0a050d0203280b040507030e0c04021c05091605 74
    0x14140541e5040083c1518610f00e041641d648c02c0304001005496103401c100c0800d10010203105e017401481c8100006480240c00074880c60359070783d2003603898140c00d209001c1d0035040000009c0d03a01c002d00442c458125003a611034540403030161900890000708540c0c101c050380c03050200d904940c0b401c000700805240942c0b00300485070400d0b00000d00da9501031003051001c049180e08a800c050095100d0600d0f203441c029480d40d840c015440421070021840c0280c029580b0700030020030418032500340d84000f590180c440610000f50070040c0003500714a08440e0103044028403445550b0b42d651801414a03e005018041c0c9650941c1059a804e443c181d03c0000d2041c020012641c0807500002030f00d480e031206000040e2a07a48004101c1c1c0c00018111195106404da000842e60715003d951144400304010b40303007040103543c0c0f41400c0d01120004500e50300705900c115400c003600d01d09a0014001a01084107074240340003517600031420303074005031034a03031440c2c020549004640c40681c020500812013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439614595 1250 439613345 439613351
    0x1e011d060f0114030c121903120f060b0a0509030a02041e050105060703020c0108070e03060f0103030e04060f0b0c0a080d0e06071407030e120d0504060e0406081203060112020d0b0f04 80
    0x1c80700000e50383d40e074900711480c0694180a80007242d100d040c00110340a102c40c1c1140c1c00c0c1f003880c51800429051655803948045494007035018038003001c40c0b0a01007a00c03191184546012142e060650b9180c018140c41545807048454040050720b903030090301d10310f80280ca0090342501c4821400000d845c1c05170040c0307000b00005c2c81120003007035000860300301814007820140003903110300f13100300c17000760440c58500c0e00b6205081c240449120703807a00d00c0381200e001e0341c1d4034944021880708010968000d40300d03001c8038103031044042c020000d07008001c00d042e10503042201e43da5803207a907522410b50014000f4200d0140c0d0b90400700100503040c80400e03480522481c00c08651020042200158025034001604000e0513000c00b040c9070f101e042c003000441002004698541601d060014000d40c014055900080c0300340400601c03a09080c0151000e9a00400150952420340b141038140341d000104600d04101d61001e007001c1910681c0700400fa0380a04001c00700b5a01c595000384092a800741d1078181c003d5217 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439615845 1250 439614595 439614629
    0x1e04050a080109020901090e0a050102041509090e0a14030d180c05060310030b04061e0b01300c03110d0e0615030615030c1009030210020703051e011d060f01 69
    0x1a80817000c1d419a001b0307a40000341701c00400420b07413524510b20001092580b0001e00464144002040500c122541d9928130b5043c58562128506a902814807038925601940c5405c002480300801c06144a40c0740044a003469240c20002054511000d60005082000c038039032800d11540000801c080c0c00c00769201461802e2422007500c0b058828030000c0c1488540d08085800c10090ba000307080b542109107040c400c038404a01e10301c2c0080c0340709554140030800e00c00c0300d070841051409100e00030f10100040711240030b50085503000a016284002010550346400d24080ca18181c805031249102c4101d00241d0300c03405280580c80d00a001d40600441c0920f103540140b1036600107421036011141d14200c0c58485218004a841c104e0f51030601c5600c083c584000d480c11585c407000755001c90307000f00c1d4003192801c1010f034183c0c0c568002e8040500a9003007808900105074441042d51442e11481000081540150001180252003040d5010f0250003034014010114600c43c5d01c03a0150501c41040d0300444 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439617095 1250 439615845 439615849
    0x3031709010e07140a0e0114030606120a030507051504050303160c08161502040b0c010f090b0f1806010b0406020c1008070f030212160f09120f0203031e04050a08010902 74
    0x490b0710310503a20100e0300213419044136140d4000c0b0400400e042040d00c25103585620030006035030b43d03c40c90140244030300701c0050b02c81d2400403070507842901c0300350180c00b6105032130310308a40c1e030b6000840039501445402222440481c002803520f200710b0080000e50340780e09141170031000c9400640c9400c42081511501c45001c501c105080b1541160300b5011021404041c3ca00000040343c1071480780c0c2641d1000c107000600080c568014a01e6140710402000180003800c11581250720400b0f000c0c00c00007204002a811035840c200c40c2d900100101140c11071440c03030000152515009030080f205650000c54100405a010441c010b07224204944011070480c8003000202081c00060155007004442152000750318000d038129074410304050350302d03000d51900d0000c01c002000b914281200040301c1c0c00303104644a214181e800f060750b02440d00310245c0038131a02c0300610300444140a0b6450b02040080c003503008042003c6001e0f030550f08008a403a1480c040401140e801560b000151590400c1c005500607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439618345 1250 439617095 439617103
    0x140703030215041a240102060f0615070605040c090e1c05031012080301030308011d0103030e1c03020a0209070c03120e0a020a090506040b0a1805060111010603031709010e 75
    0x3000582e001078140c1e941d81408203c481c0e1440e8405400030b0400244881c0c10040d140304c02001c00031010203080c0148460049070ba42c0811203021004405003004204103207441001c1d01c0d800380c01d62488600b00101a200c200031604182c5045035800c082260800c42c404103402403480e201306c241c0240280700807402034042d080220350200d500b0400000005000d40303841880742c4000c2d103400c0e407812a012110b0301c0c1803180c41c1e000380010303008601c1705e0000107018500020300c90550400f01d2009085640b81d0baa081d602d1a41040007264030905107914503806800b01c98006000c18000c1c0e00400c0306030b02c64018008803d00c007804403000c20014012560200c0d8000c104514144d00120000940d208021502400c0c260000d800942c840442c46001a59030f042e03400007809814116000c20034200304c00c1c05c1120240c010700c210503039a101c0c1a14048414091b5200b15480181810140c103003002401050782181c28075002100411748503085c5e1108410042e100303a600c00c1000d8000c12580a0304161580d803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439619595 1250 439618345 439618363
    0x40b04020103240305070e060f0109031202011d0d0e040b06040303140912030415030911040207020103090b160e0319080714150a0b03010504020f120a0c121407030302 73
    0x40c15101c0700d03001511040107180d00c0c0f000d4076141901c80300944034170308a030f01c41215110b091201520324000c116103241c841c02122a0303140c16180d05801a1550742c81f28456000c50b25243c00f955640c181c16100d2018114032081500340f00001350100303924440006d03040b200c40e400301c03a0060345480016452501d400c4100d43c04d903505410404289100380341c20f12500d100f55900c00d608034100d1107802e1621000000940165048070054404104018104404844c034001000e0641c80403141c2030300c0e01c2d080c243d004cc8849401850041420600d07a1100310f1600c0003901c00303d45038800051301c125a25801000041c0c842d00442c0500003001591100c6000102205005041100001ba0304401c1146640140d903068450900f9071341e080d240807102e0040c12404840040da00c50406103103002614042c0304079445554000d0560000c0703403a0b442403000070002484112010f204170b40f0b00c031010030a1200810010903003410b01e005800d4807403401000c0c4149030b100d98101644408000e0000035000b0902e011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439620845 1250 439619595 439619597
    0xe01060f140303041701060503071d011406071202030903070b03010f1a07060f0c14340212030306041103070c06020904090f03020c1005040e060409080909100518040b040201 76
    0x4072403160900001d06610960f0310a0f11254a00c040646407000107411030000c035003084040d100c080799100b0304001150700c041800480c50308210018020207007080005410300b01c0190005060140316503904046101d1240d02034050790010403a03011501c1c08100040107410a080c0441c2035515111910201030320740d01408603045002e501d0380c0210708010064840e0160455410700c01d03c900784030520014034a5400f60000a80c00031142c049840409045521150710130301c101624000441c0da002c0e0030b0584c00c01d140c1c4001d02124206025030303901a400000944030300042c543c2c9042000420044030500d0220300010481801040307103070303a0003000c055606500320b90302580d1250f01400040c010b2030462001000041c0440e141c030700341980091062941d0200b43d030154000c0c0c3d80f080059030280114895441c6020780da00008803d81007540208a040d44070b40d1800381088020400110f8140085550045464010008000e0340c80d0410692001001c05650045542041d84400182c40c00013000a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439622095 1250 439620845 439620869
    0x106080d0e0906061c05010515090d0f050f100608011802090127020315090a06050a051903051c0f090317070f0204110c0c030d09060c150f0207060e01060f 68
    0x10f0003e441e030900b102c1249020700c03000d2001d54000e001807001818280592401501846000c8922983c004201c410a1800414200c040103150f41c0354071581d03150803411a0036000b14580c06401c40300402c40840e0040400c000440c6150910704090f0840d00c141000e03800c040403000e403080142c2c4544480d24191201d0850312140c100d40000300d0381d401c004904004541c40d200104000040c512070102c0306980000710f8400c140d58a0724070300d8a094455600426500070317141c9500700810315002e15148502505000c07110f040d02e81e40d031035650500711100202808001400056500940c1c40304003050855054203029025070304503296826491300c90000910030440004048083c8001104120b02255000340240322020002144030407a0700304140241c5540700b14000441280341c0801c442e4180310403540c1d948040c52910364220307840360b18142c040d2050640140e41200d43c04182c010b1303140043c4521405a41e030038191a00c0d20031100034486411a40c0d1500501f44004031a103200742e0100c8000d910340d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439623345 1250 439622095 439622101
    0xb031606050c010603021c0203060a0e030a0e01020114150117070e13021207053f04080c01230903090a0302190b031815010b0d0c030b18090106080d0e09 67
    0x2e4010a042e410181d07004026508024034010150141d0020b01e20a03000e0f14016102c40e0703c800306564010000c1c0070160400d0202c0c004051003620318000481c0148008030304110f2502200305400c40590b05040400d04092074000036580000c40c8604107010708030701340142c1c80d103000e0003004640d682e42403502c5800002842150007010b601519001d1901d0342000c8600d0a20281c05081c59020124200c100940b42988103889440010128054111003801c919a03030708031249401d40b00c1005008841c446818041420090024410200030008035080e5546845003103a40003240300300180202a1540b08200741515521494440c0c000c5a5040c0c1c1d510032000b219055590011103190440c0c19444070110410019043c1040d0410000300c03914291103060200701400c460305a8240a61700d01407108001d040714201d250350040d002c00882c0d03d40024460721120020380220060b1500c00101c1c42da01c014060f000400f07100324001088107900078803510300301d50b102621060070244c0041c0309030820400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439624595 1250 439623345 439623367
    0x8060f09032203080d0e12090d0213150801051906081905071a0d0c09060f050304060b04060b0c0d09080d08090f06040f120503010311271302040b03160605 68
    0x2e0300051540484119218008051190700130803040c4a401d40912503140c6281658400300200c6961200203892032508151036002c2c480000074246169400c5c682e51907000791b00710741d0468284003616008001141a00b000422015030120320400768aa036442e01200304040040007503410144400d20700c4402c1c6544541c00e0090a0010f1a800301c0048010310f80d00c1c2c8400a8107800400004088881c100583c881c2d1000403540c0300800c0c02030502280300440540d0445001b280510340c441d101d0b00000c111944a000440c0c15110180e2116007000004104550700138400e02003000100c40c40d00d1b0a008107481d01074006d5a4040c01a000b40a220401c00031403110001813021000107900c460403690181482d1a2144000d804005c050b0340340c0c140d02600c42085407107141100d0403241c2103030f07800e10962245003c001641070031829202030407076400100c5000f04856040b07540324000f1a10b1076102031007140107000c04d480386015158402d030405141c5c800001c03640341c0c1c2d0009a450342c0c50082d84074140068 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439625845 1250 439624595 439624657
    0xb0a030b041104120f1203060f0e0403080106050c030c070e0708090f12180a030803010e0114030d030c050c0703030306050a0e0f0c0a1803060203072703030311130b0408060f0903 78
    0x32020304446078041d1b04c2d000403500340d007000c3e0848000c041c0506140c5da0307561842c074040030159001800038a10800400803284240050129906a481600d1800f0390408945150040e01d52003041400404000c00210a40003d40d043d8003106a9000d84060b09462034504d4452000045d00c7c2031505012420f0b44900742404c584500c1414085c08400d0b5141d200e083c0760100303810034840da000c0c09503120008504000590240030031214094010240502150016009840c55100c0301003000024840202a25800c1041000039030090b1400501c070340c03c0509000f5000010f420800400c0d21840c18007500340d02d6044070b40c5d44400f1044c12152030307005103c004c8401030a01c0354200f41d030034040d00010050009540c02540154025115070400071441e40d004a80c0004000711000d100c040308404102282c0603030460346480404290152038044801b4200b450301c1401c5e040f410302040042028007555000b004544e4000280b182c1c1600f136481c1c40145181d407803007120a100c0d841c80205801d00c0e2a0000d140d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439627095 1250 439625845 439625873
    0x320090d150f06081e210a030920010306091a0d0512031906090614040e01020409061728110607020402071203050c0f25020a0b0a030b04110412 63
    0x810074000f00343c0e00d0258683d00e544075914182d25003e07030804004030407000101d04220031400c1c140d44110008810042c500d503042411180d0615488128800000e0108100b80200b0001e550a1b8100d0f00c180000060031240c440d00181c80492034404c03460710000364806106800c000403540120050755074600305040c15980140740031020004800c1c0401c0000c1c0301d1803c0005440600300f04155a0384074008000e4541622484560005401c000c01d110706250b0081da0108034024009403810b0350310b00b141d404540441d480417034883e40744540044681014841c04034500718007204a1500ca500362000303491803651420007464140301200511407915401300745d03000c01ea0010400c41d10b45c03545060408402c0550b40801d00001d03d04400114143d00305000c0c1c450051400c810541810301e0051003c0c0f0910f800103080c0401854264018011394400804030041c242d003004c61603ca45280201509491070921a14451420b080081c41e020b141c00047c0e608030742e00041b80700c0c940e4425007800031040500d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439628345 1250 439627095 439627121
    0x303040503010e07061805100c060b1203070c151e0c0506010b03010503150702030a030207170a11060a02040501020d080718090c09120816210320090d15 67
    0x2c40f000700e00b16100452103004491480e1180d0142d4190300410302c0611030359000c0c0b258010503185810200d54401c2031500007261146000150318017010740020f11015a1005203005903000151364820042041222001008041c48840c000e9840d4100500590240b04103a43d91190400441e00d40034480e280c110140d9800074103440c90381d41c580084001c01d610902410380242710303c018100150080307484151107181d10f03601440c01d0641b4028202c1c065400804240c071040b070850300b40c44c409810300c001042581001c0d01c03404405283e40c1c16107410090024504040c42c2e106000401c46a600414001e03008000c0d46005e00890303840c2e40090b1b400d00c1c015101032001c0c00304404081b074192a80c1c2d000b20002403064075031070307240c40c0d07501480510540941070042c000441400029490400b50400300d84040c402c80102d04062019090038605211012240c00040d88400f500a00a80c07840f600da984980ba001c00030780b802c040c10000c600251207411008101c298504404415521607a20034224076001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439629595 1250 439628345 439628351
    0xc0504030b1b040f1e05010e01170a02070804090b03010518070306110f030a0b01020c060a0c081308030703080f0f0105030a030e040b040c02070305100216111c0303090b010902030705090906030304050301 89
    0x83d041c0346105c0000c510118140074006690103c3e45600551107046c0c000b405130740d185001c8402c4142c0c080c4416018003244255502031081c100040c0d01c96010340094202d0a100013030f6014103c6c10142525005880b1258207024070000301100403000c2003c800340c0f5008507002c20140b0070a44007203200d120b241c3d12021380110110600c00461080c0d0400c5050340030076821514a01d1107902001454803500306001c002c10f6a042041c40000c002101500c0d1002a48030030a01d0142d5940041d41581e1005800701d0005412004002c000301c030031085560042ea1200341d40709a903041030046595100c020501070140301003800000301c85d40d07594201c844000cd0240003802400303030341000039590302007034001102c3c3d0340680590506100d0842c4240c580000030009aa07004100d00d484100f40680010300c80d540244c64008101a14000260a900c2040c4265400242c1074501d08002360304c050706030030400100f8010000d1140316648034041d13618090044034501195201d02000a2a501c90342d4003c5070503500b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439630845 1250 439629595 439629599
    0x3060f0a031101030e03270f03011104030c080307170310150c060b090c1903020403060510030b0601020a02060d0c091d090f0c1c1a09030306040c0504030b1b040f 71
    0xc45421002a962030a0300e06004003041070724029282d0081030311210ba90002460800107202d03100100b009007c07030180c03480c0c0ca82410000802c3c00c0d1905e410038509200000502001040b424003007402c0184000006141401c1c920360701d61844200f1224001a00c074030100200d030741640b90100910003080805024141c0785000c80001e004e120800000f541e81d10310f80903140649040152401d4071440070000b03543d180c0b040c0030300b13a407042c44800040380c4200341e424040800090341901c5054069025422a9441e00e0b18500e810801c1510007800e040c1113410007101d000c0182c545100351102210781c2d030000710702c0c0f0042400880304612240d03c507600700c003115811440508a4156400e00400141081e619090790100308140d8030048101c1c10764002d8080c15070b000440084209407032040e44901d07811210514180e404d88210030b000d488110142c0c03c0003062200c4c3d0b1415110303c3c0c0c01c0c00c14a0820a04081c915120f828040c0e000a00c0341d081e0071205044441035440b1b0b1400c0740d001d0812064100306150f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439632095 1250 439630845 439630853
    0x50a0e0a020c010c0e03070f030b011a0c010908190c020924041802040501170d08060103180c15030603050a0807060e06090601051801080c01120204170309041503020105070803060f0a03 81
    0x280005c0e01500038012424089400929540b0600540b5040040c1103026442c00310198001d608101482c2d181c20410721000703880c40001c3c0a45040c19000e00e07800d035150400181001403800e15008032100303000f0614010001a1601d0f03080d658400116107021050001c1580e01c840d04000c0c42e03a40a502c00d142c401540c15000e0702805804c1c149000361000c1040340c0c0c80c0c1002c805c0588179044005039690128038030b40c1c40640b107041000c5d4866010315000c41c209404c00000501820410000c881e01e00580341c0900c450310301084292250341542c0f404ac0b040368a541c86582e1198074820300501a90f90005003507044c800550807102d217107440041112180d1600050303c640750b10b002e000e07152203685040d0050800c40002c006c517506890846001c4c002c011080710066a2400300e4047c8080e10540a010002e1700b07549a407200d4860039502c5c8040d43d904c58080302004221041e80d4141c41030b0301c0d003000c5c0600250740e000d82036030000e13980a0221562a11140f000660500b5041403840e03000c1401c400c048104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439633345 1250 439632095 439632107
    0x60f0f0406050d21170a02090f1c05120a0507110622090609110301050409110a0b0a021207031e03060819120f1b150203180f010204050a0e0a020c010c 66
    0xf80c00c21105407041284c400c02c40f0b0f0f0560392000352285071100001b05402c0d1406500a02100d98010300100c0409081c002041c00c030503010300f00802d80201d0b4003004041c054240310329450340344058200d030b140414002c0003608a00a0f804040c210f100e915590034519204c4000700c17490342a0350342c94003c036554003500904602c4102d019141201c0c3c01c01e0000a1865042c1c0500701c00c42140d03450003411a07003000c0500c0002c104802d01591100c162541c00c840c06c0c1c8803041014082c0901442c900e0381d841c2a003102901e02040360b14140c10000c800c1041d440400d0303002d1074500c9030604214114140c148000340490103400320780c00042c0d035401200040c0840d0381010341440400c521410488140c01448001034841707000810725100460f18500b0014514070346199a60308061007004942e90344142c0301e060b04100d800488841150360f05000319900303181002c1100c3c0061054040095203030500780f2020400550700c902c903602c80d0305100400701e048425035030140c4400d041060000c0260020047c402011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439634595 1250 439633345 439633373
    0x7110c040203150a06080105150309010b0d0b060f0306190b0d06110a09050f1003020c1204140a0b0406050904051009090c061b0b1506190c0614060f0f0406050d 70
    0x480e41303e02c080096454012410b0034101d82c0c009110358114015151040031903813000346030700125507a0321170f400e06e00d070340d081100217449003e102600d0483c0f07812070a109045041c0615188aa4800c104000c000d82100e0f440981d02c000140000ca61040c2507070201c3d11003542480c004101302d0415003145803220492000d04100c911503914441c00c10380d07402c01d01503402000d1126941154040c00116410340c000d4000f4100c607840201124170100300007901e00301e20340141c0c22024031440c00020403e641e260100300000034050311181030707140a14000c80601030b03215a50300c0d10300851f140d100180d651036a00380c1000052194100900c40741c40b492a1810303c1e03007401e000c1c22000c140d802400000e4650550100407425521003074401441d2501194002408c401501141e40808100510300e000305401442c004202180c2d180d42881007514030f80711050700c088a4444100144000808c0310341d540b1614032204040069400103120300c0c1120228000d08400d4201070340000c0f44020600030000c0007048100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439635845 1250 439634595 439634599
    0x9020a08160906150305190e010e1023040519060c030507020c0d2d050601082404120207090203010602030c150105010206040201050d0603060606030f05130b07110c04020315 76
    0x1c0c050384405000301125854012014240780c86440e20310850700036030120360025039481c1020b5030100c09495510544001c41c900c40c20340d944550704048448801c02c030128040c0240f0b60b00340401110a07006280c40035030f804400b03040b000140007080c24000d00f4081c501d003031440114403a503801e08600389a000740c00c803030102d000041d00d0040010145880841e81d003003501001003050443d6a5183c1314400c80030106101800110304500400007a0942003a40307440c4684100003030841585805d5a06d400c2524014500004640101d1610860743c051b401d855401a400805040c4511444404a02c1c08030941c1052403018400400031130055000030262051500e2007040741e2141d002c81c40440280402881100d0159208001203401580200301400811041440015580c6c0c1c1e1380c0c0f1550103481895002002003540c4080c01c16540c00f25004655008030381251203030000545559503501c10200410380020010300c110315110040301806070522485d4014019034032418000000e4000309081070580e4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439637095 1250 439635845 439635883
    0x160e190b030f090d140a14040b0a02060405070e04150c3c02012928030201080c1207080601021501030b070f090602030f07020105090d060b0a1d0a0e0109020a08 70
    0x200c1e190701c1034482d142210080d0544c5401e0035511001503a002058000da03a10240090201140444270385010708150b50031603000303144508290804e1404e043d500d4110f24403c4103450304000108281c90ac03d0091095104400104001079240031500d4401c030390311034511204c030f42020a8200a8800e074003d41c075a13060b0140c6182c19030800c3e007a82225030070514100354034250340d0030011603001d08441d2201040060a10040000420440d0a10b0f1640e5419051100d9800c1420300039540d00440080d03001c1891503005140ca140303400d04c01c94582c0020f004208003e40c400000d2205d900c2804440c501c0f600801c07001946507101d241010502200710791040c009980b04805d140300314402d00c40c850450f15650040d62a06200d15481c03801c0d03a002c10000c0c1e05000041106680603100c0e01c1102480500440001a15000c0c0344100300e483c02040c2d005107514000e0000446c00c0e000440005900601c8011001035524514034003180036045100029621421950000a0207140407440058400c00c883d118 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439638345 1250 439637095 439637113
    0x60d02090a090b160c06050402010203090303030a0606180803090d020a050d200402040501080c070c03151b0e060f0c01140103050d020d2f070f090b010305160e190b030f09 75
    0x28144c0384606000c01000444801c1102c01182059004681090040c41503a00d4040a500403a20350b034016591000c0c041e50758002002207942c0241d14000301414580c08507089031600724120ba0b43d00a00c0603462042031505019070031940c039025203000822000e81128804180b81c28940401020035929034551500c102c4010041d01d0240700711015a00b050315201c00d141c50b40300940d002c58010a0086901742008a804000318440301950075811000c0c07280407481003080c1480c5215407030044c4104051004d408891621079032200295010360550038074098607501d10340c11180c09060500300001890380d91500100c103202c400f05a0000070119a02181e100340e50300b84046942c0d014162a0300f0b25101c204d01c02584004c403c40f284003500b1128406c8451158031034028064242e1f065010004075640d074018001503580601442e9400000e02e980c510401c00071140103800300100b40132091054400b0140c1c1211007050707258000240c219100360310f8880c9080d04000c205164150341da10310310700c109940c07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439639595 1250 439638345 439638361
    0xc0806191a19030203160e070c030c05010204090b1903030e01030c090312020309090c040b03070c02010c0b0709080d020c030c0411130f1a0703020c0603060301060329090d090e060d02090a090b 84
    0x3044044030412000da287c9607582c610101da0154004c00c00310200020b9222050100300c0c00d002600c042c0c220301c0710016250051208000070303044111241507400c10f608400b040841e40002c03a00c051800c0c00c0c240410207000401044403080342d241c000812000c000822440712590001c0a0950754000740e0740da1b61141c68610402c403507030081c2c3c868003200820810003d0701c80391080080340b004500c1070500d00d0b0b9807078050b9100207044608460483c00151403a204118007038040010030070503100c50019000000c2001c2c0400e84407003c160700540119214070301900c0341c0d0b030f4242c00c550400303007200c0700d5002050b00e41244a49500d0706215048a81b402c182c00000c00c00b000c0801c8030301c0325a00d0f80081c00001d020100b4003446810040505606540c0d5160001c0410054503280c0b0020500008900840081c508040035031100a440300303c5070b900c07144031201400d81040700c401c182c5070100c0000001d90307113040002e0b03855501c402c0f00940100f85c1e2018013005550940016041c2403280001036015076030000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 439640845 1250 439639595 439639633
    0x30f0603070305122802100b101b031713021503090a02040906062d0f0b040b030c1308010b1005090a0e100b13030c0806191a19030203 59
    0x4090710607000b40e012942d00d0003004008022040304280760b134080b0f104210060030031760400590100583c21840882002000a01c54000008422100700c000395810840061401c070400e00c1c0c084002d00c442c3d0600091502414400742e441c0c00d5000340340300b6071038019080740c0e0010108208078000c0010004406440030a0303c1a00d1207980600000c145e0071801c2e03001c01024000c006000d840b8107540d2030012900780031125100c0d000200804502010350401515003158418650080c19140c1d4494814440b640a400880302222403c6040c07940740c1e11020020541c0d40f0507000030350041b109511001038140d2040d0009900241c0450707510360031340b0030728500b5281481000103450b4003411154091001951540219030045140a03d03000442d45401429035140c0c41001010071f48028550100308019880035a10301428060015145a00b858101d44212075241c42e140b07540340d5103920500700040400900d40c00498401010040100600003111405800030300042c3e000740a5810606e042c000490 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 439642095 1250 439640845 439640849
    0x106091410120902010c02030d0e19050609130e01090308011e05010806060d091e051c080606220314010e0708070501080921130e0f0a0509120f030f060307 68
    0x51107005407001a00382c6000200107080049060118034038150015031420000d000e910500c60721003140700e0140b03c0400c0070703400c000000c04500c64070201d014001b9403142000d94100034400d40384281c000004000000143c42000a09026503280103115024580c1c025440d504031189004820001040c5a500020b009034074000e950109282c0f9020031401d00701000181494036080d00c00081c1c00240c2d0340c400501c01103502c2e131005901800d0508409109050140c0c545844d4100054449071400b440043e00c240f4008000d01d1040300089409030341400201c00000704032a440484500c800c0e22850035682c2c0c9140707020704040942c64548401c4140200142c0c5100303990000004088841c03030000110f07080d50006000030600e00914840c3c0034404103001c0c00401d1744e0011002c980d00c1d5603000c446481010402e81c4040c0c5a0b40d100d100703000c1e0b451180681700d50400e400c45030100d590f03034500e00c9036490060f1148220600170b40000d1036400080341c032400b81d03004046035000c103102516140201035441c6024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 439643345 1250 439642095 439642097
    0x140903070c151709010510060207150c0204023603120706090c052205100b0306150408101415010203121009020a0206042d06020903010f050106091410 66
    0x49809015000142c494400c04402600d044086400064191800107900390349078400b6a46400900c4070f4984100544c2015010302d1000303001340da08d080001c40b041d41c401041441800702c00200742c2d040d92a20f804441c0e8600c14000642c0c440c2c0c03003d40380520044071190404241e12802864603000e440c0200f508a245122050380c41d040c6940c40d227600e401040c85190444444001d2840014030741c440c1c4c5a102010343e144080780d00b42c2aa410804826240000c002d100e586803804401d12500c08104160b80d044201900e04c60103001d5480300c004400d110325000907006100d05200400b0106a54006004101403d03844491035181c00361800c0c8941704000e40d42c1c2c056013003403211141807018481041d610064035645040095941d810724000c9a000d43d1514005800590803c400d2287c0030740f0b0448401020544901031a1030180303c5080e0300c0c403642004104a400280c10411550250001c1030114008001007059503500d8030040c0c8040340501c04d007844140115401412441c4c80902103c201c036407 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 439644595 1250 439643345 439643363
    0x40e0c0103050c04091404210804030e030f01050a060f0f051c03301404080f07081218061602190828140906090d0f0b0a14090307 57
    0x912401900500002040b0511111040c0800540d05179103000707541145070098020801ca051506226450680516044104140c0014811469540111250b501c242c041c038040c1000c404850002c0e05100010124140390349c200b030180030340509542c0c0b11404441c14544820540f035038440142800d02d034a4464143c0c00b090140c4060010b80c82c040c0080324042c400d24040281c1d00c20900e041c2c091034941c640c9903100300103147c0d14a0400081e1f2042c000c074000d008040d00014541683d410603140b0900701081c04600300410300204100406040d940d80b621000c02100444c607010010940c48a660034410404c0e1080c0404500b41080c030091401041001d58058401d80c104200c5070f01d43c1520004044480f00c0c020800c10500d100d0f07402c02c1c80013098030600c10340b0720229050001041c8491041f0300c0c203800c03102080400040d6560004890191f4401c0c2d8000f81d51840900340a44a04140c400207428185070208100e2550740c0b0740e00641c800e115606140c5c1c44c60721130000c0c956507802591001848022 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 439645845 1250 439644595 439644613
    0x51215010303051b0109050a1104180312062105010b06031b0306011110060509010b0c1f0b060412020a0b070812040206091903020a0503150a0f060909030f080105040e 73
    0x1205070018001419040203080c9207811541284d070031a100240d094445400160604040000c0c01911440994040350144150403402c2840d1401402d042001820301107030300d0070104c0d00401d82d0008001048400300d5000182052080107000d0414210b04036803551a00b800c80e07446240840559010f83e540441d880c07076100100414641d2540f000d1704081c1804890410003101c1d801c00c00c00c45030b030002840000b064a52800d0140a0400d0040e0000a80360030700f40071142c05c1400c0011814803502e10107407180380d554107451901d03004201c61103502c2c0d080346001401064403041c001c43c17007907028402d40700d0b005001c0e039074864601c842c00380c140000d10088040008d80440260050f0041d04603000820181ca001c003031200040000680181c0c03000c030381d07418210400a5160401076403000781800d41c05054003200031500803020000080c11030401030380d00c0c400030706045da80d640030101800c1203180400c51150141805071179800228030031800500c17148004107590401d03020b500f1039507504c40c0050000c1702c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 439647095 1250 439645845 439645847
    0xe030304060207030e0a0915170c0103020d110318070b0403030e0907021e01060302150702060901080c070c0311091b0d18020a0b0c0f0c09040209040203010f06060504051215010303 79
    0x150018909404001764008041d446a8484482100410307080e200003c0520162401104250f8254400c104184d00c4252320030710f8000208424030f06003001d2800680c0e51083c40840d03c0280090140354480c43d40c04000c102603a510320414915640d0f00004454295a803841e580d0020b1040d404020f000550f00380101102d800c0070740c810341d04810240159a514a0352801602c02000700005405481c0c1d1501302c2042941008500c07c04002c1844007154034001c0309801280303852203580ca855041000480010780400c201c0c10a03294026400100d82c012184e50f4102000d2550000411900c1517200c00d003c42d01c0414a541264a400d000e40b2040341007542850b4902d0091640183d168250602419000300503900c40d21007a01501504200c580c80d80380c000c103024949030042428030616803004550043c20340d100312110781d105034112452100380e03030b541c800f0034094403403440c12074182030400101185560f00034028100b0b584041d1142140355445400032565800c1c0344581d00c80400003480140082 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439648345 1250 439647095 439647097
    0x3020c121f020706183e06070507080f01021201050306071d040b030f010204060905060f03060904081b0c03060a02070c0909060905161d071209062309100e0303040602 73
    0x500c0c01140300248101c803080303a00c4040d0030070310f10440da01603400d14080c01c942c100e03801c0020350780501290030070180207580040100710306e400c1000b80326583c08608d8408010080069030003422000c81130321804c0b000105030b03d010390411340402654601400002c1514140081d405210300c006940c0c001c0c00d03a44551f00e9504001130004015005510382034041c000740c07810884410b1100c2c0d14400186e4503444d2040c020180296508a2481600200211180028100c3c25240c110b10102c40e580e81580382e034900061144102103d908014080c048007042c810000b05900e800c0d11030980c16501c040d034a400c10300080b1f100c0d41c40000e140c0943e1000030b0040c50740d181c0c0103690982c4605000103110485031149460130f61505000703c98292446014056154185030f0812945500356101050f800c041201070000350038a000b8034110341c0e540080806000c00740e04240e0300c5220b44481604d01140c6005042c1c5d1140c011141c608441c0304900c650b4040310110310620242c40d01c568080c50840e2a80c2d614a006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 439649595 1250 439648345 439648357
    0x7062a0524090613051917040b070b060f031209040f0e030c07090c09090e03211b161b0b0406120e060708180f011118010e0105030606070206040b03010303020c121f02 73
    0x4500c02c82c000d158030b8847c5010040c00500b10010348180c49450b1440c1c01d03140084020b006e2401500c24000040031a18002034441801c0f601c4218981c1b07034101200481c0041c11030b00c41980350780d0300380794100c00e0b00200440244019020b000a44034010b0301c40030007000381d505080700d103400120611410404690190b0000759156200303c2664a0f00c0f40040c0754120303020f154061141141c9500080c882c0410400b1400f20300b580d52520418100019000c030040c40003d6a0380280150340403a10b84208400313841200c101a0050040151301c07652a0003008011011240512080a2500c81414918400000d02a00c5440346555010090f031343c4619161500841c083c00395214131919501d10301441003070040e03004507a00700c42000d4481510203401900240e121404034184a25000750310b40300c0c1d0b8040101c1e40c0c44a03081d210159222100d10101d03a142c03003180d000300d10784400400040f04055000c01c42c0c00d41180c084401c4610389111520040e112500f0500c0c1c201e206e0300450b01d0030500942500a004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 439650845 1250 439649595 439649603
    0xb061603090e070807020f160e190f020903160503032a0a03030c081e150102030f0c06011a0a08130f0203011404030207062a05240906130519 62
    0x5940e4940e4a00d10348040c1d407400f000ca00c0210030400c00c0c0d50f040002c080040492002015240300030015084400324900407254925030003400290341803691586181040903d0f801040b0340d20640a89400a40180c5811803290040542042d81c0f000d00003a0042919002406036140c003602c28004500407000d40300f281c0c2290091341540c0c403201d40502a10400601949003c111b105c0500300c0148070641c01060451004128543c00112000030401d041e40880c09020700483c041344140141d20311700404070040255080018481040600800c569040750b851380c4543e0b101d81f4801d080c025090140301520340001c1c0140d8002543e411403200ba42c0c004034082d943c41d500c1d01a20ba0013207429640a21212110a16603100b444200b40e410451200242190f00c0c049922140500c1c600c00761a81c0600640d200003c0b80305aa003d00105000e81343d041070024030040c0783d00700c01102e41e008680c81246c0207406406000001440c00c400c1030031500301590310501410300001001011400a03c1c4030009032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 439652095 1250 439650845 439650857
    0x30207030225050a12030905090c0d0e0f030705030405030d050702101b2114031003020d080c0303010807140405040b060910080303090f010e010b09070c060b03030d060e09010b061603 80
    0x30f0692960751103e009000d84c9040c09090380010f04000d4241602a401180260040020400303020300d2442660300010801c47d0203d51544018085850019050003444407408001200310401000000504c02c581050b41075a56205a410060343c07207028514011350046122010040010300c04c1180940f9690307280e5004400301c1686e00da00511840c1400b00f021100085c107000f090701c50f0030196580c041012181c0303503031a600e030032540e00c0001c201d2032000a000d4840904600c0c200040134043d510a03086900c00c4940380c1da515406c03107a480d4860301c2030740c1c1050200081d129460030320303001c2c0714400c0750050342c48161611a5400e00c580c140c0020308400c0b6541000c0740100313501c04180010360292aa14009011a140f01b400e031a08440000042c80b0081c0e26100b1716001a440d03030a050350340480281428080000641000030107021510039065040c040004c2080c0c1100d6168000320503a10040600901540c407080b40d5422984968800c1c2d030712860034480038006094006d00013003000e2280c5048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 439653345 1250 439652095 439652099
    0x5010512071a0d060b030f0a480906080901090503030115020f0d0504060e0f0d02040914060f040b070e1e060f0f0c061303081603060b071202010606030207030225 71
    0x12034204c85a5400540c803811001050001000382c09504075040003544800308a040c8001441810103003030038842d0406407851690210070152050102800742c1080e0404101c80038603454010118600b500030400490303200300115540c0c410500c24050131079030040085166900f0819034800e041c13040c0b54194118482d40c5041183d41d5400d01c11410b071400161038281c1c80707609007032020340407070480302c07005016030346030f00e50100c1381c0d602c1641c0c1440140c2c0507640040d610001e810b1026911502c1e0031440094030030201802941000c4401680c07096002d07200340c0306907841c2d07000c00315600c00b28501c080c3c1d4460b4404103500500540108000c03814103004200518000010040766910b0304003024001e01407202280e03840401000b41b005aa00845001e03802ca4030307444030303580504614000362480c568800000e0810441c076000e54000740c041c181da071496030f454490500c0c068400c141ca41c40b402e0015400c1c81000103941d4082d00070744800c02e41c1600504101c050680003454100000c052680400e0030141d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 439654595 1250 439653345 439653367
    0x301061706070e062a010b12030f0d0617100f09030819061505040f050307120f050c04020706050601020f0615040218060f070515040818031c050d05010512071a 70
    0x12171081d4152030042001e40c580d801c062030840704c00510083c050b50400003030004074a0044210f495668050300580d071103002c40361050000304003c1d0403c8100030620316034680f80b01c2e400030760356510310304041d0140513030709410854200b60b5003060741c014003160034100400d200c0d00c0c198005540c07144c080d080008500340d94070410320101c00003000342e6010840c000b034284441d408180348280030384800c0d0700034005107181114914101c074070140d02a1032484401d02d14010418140031403c2c00103002001036482d01e5076818001d005040550340d090142c070408803822142140443d2041c40f03181d40590f501c03520044c8100788000b070740c081551054684910b00300d13a042662034001500640124500e1035481c0c1d441071070000d207888522884140490021010440000c01c00c0c1c08031803500d010507011404840719800403e160256100310001004002c2c4681c20702264898050280b61a4120090166907030310414010503c07024201d8680640000509010b01d240c40800c0c845003410300340300f403403a080501c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 439655845 1250 439654595 439654627
    0x1207080f03150a15090e28090204020a270311150904060e04031d06030a0c183015090212030d23280f020313020301061706070e06 57
    0x441c2c18030340d891400750f01d20f94402c0100e400f800f4082c086000d14141900e47c1140319424002c03130751601f03010b407107410090049500042d0035035501038029522589155000b030412040c0c030081d040802e4080845801c2d611750021030b5412260040e92003803052410600740600e444081c6c0420903003c3e01000a40650b0701e40380308480080c2040320009005080c02d02c0c00501c241035540c8405451204900344242c03981e41c0c0d00460380c0007010000002481c840710181654207500400c00002104000000081d0020140d41408801403480420401d09400003290780714404542d00081c01a904c0d403402c0a0b4050859449021390f00e000920001c20f03200c02c1c00e20780f8915441458002107650319810034001809000d5003000c1b1107501824611000d00e000361613001502c0003e03e003403005940000d15654000071a600c100c00e000d0f0024030035036492900082100e038010344a00d0480c069841c0550000d8000009000c0303411510ba2003018222649413100100c0d003035190f180c00e0651180081190176501c82d41c81c9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 439657095 1250 439655845 439655849
    0x10c0209130f0c061106010303021504020d2001030e010606020c0420040b0d0f09030c1203021e04050307091413030207120f050c150a0503130f0b091207080f03150a 72
    0x15410b03a0a0400b0401000b41544a65402c02540600010310001e900450002d106502806041d640c075520dd00020b45000030061001c4c1c80360507016042c0e0000c0d0880584180c00001c2a2020f01c10580c88902c3c0d1822203c1c02c1c400c142c0140c1016083c2c0704186026084101e400c1d281003909e00b006110464030703048030703070099115481c0305400144490340c0b031141d0b028100ca5484c032030008001181d0103450151445c00705140c020030340317002004403004682c0030398140c49295040b003105003c103400015107409150f000340200d51080c4102c02001031050182e018058800c2d8036203900904a071035121540684594000084055000b074800118174401c0b01811440c00c0303401a0f000200e180741504019040000c4440c1c4940501100e8040034a441a01c004036400000c03079140c01c070364a03901c0c0318502054020707483c0d00500000305171a40c1c1041c803602000c450700030454481518420f50106000075880c0c8581c002c010701c80c10302440345e121050f80c560095540b00715140c5a2103201d011100001e94240310b69 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 439658345 1250 439657095 439657103
    0x702091306050c090f010509012307061a0a12030207050d03080114030607050a051305090a0603031701050f0d02041d061e040c05210f01050a0e0309010c0209130f 71
    0x226608200340181401125000b1400c030070f12900e000400b4011841140704a186039060143c009800b4490b030b4410700b10240c00c0340c40c1c00324020b046a2061482c1c2d003164001c2d04192810f07818010342d81c0c2c0701e20f40c8500600c44014001d000d480031510700b4004031078101d8007440550a40c054580006856106c002804425a01c00e68601d0744640c180f07072090307103d14551b4007014080d41c03060080184490300642100c0c0c101019083c4079484210720082c200844400fa00f2254100b50704200744000341c1090b8115109892081c0c581e00c04820b108a0a86c141c10b200b4890f890b4000c8015141e81400d080c4404141c1107103001800100c0d224079180b5011150800c800d602100c1c9900080030005480f01000006104400045115996082644840781d004656020300c0744101106010398500280e58242d146110817039200340e030065842d81c00703040c0c000d000c02c842889059080c0a400031a450010007105c0380c2e124161900300302426940c0901010810040444400030000380d6600d01090440f010102c18a120f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 439659595 1250 439658345 439658371
    0x10602010b010f05030f060108090a060e150609040503400807050a0b040b0f0c0f03030103050c1c0605060406050d0b06040c080f0114010c02040203090a0b0903030c040e090102070209 80
    0x90302000600f0b0040401c1d2040c10490300b80180540f4001041e00c00750400001d2030b0980080c1c40348150075050580c0030b4001400d09243c0140641c00c1a03000c0344111a21950032052042c0e035030341e1710500c960b0b01e0317085a004085400400180304145465400e10884c0003450a00f117580170038100074602003103164400520500e06e490410000790100700301140180500f075850180b0585060f0400c0c82c54043c41c014841c0e010004900140b200000d035081e90040d8561000f154000e0151406050300c2c0d6000b130105503010b01444451640d1400c10f51741909907092016000c3c40410040d850389002804003501c41d9a019403141c0f00013170319590315161005c941c2d005030a140c407641091000c1008403501211090300b8085070404009107542c80101e41411100ca00c08248120505440122100d08a036040294400d2000c020b2008080000806040c0c00b80304140c10f003031070340360100348644e01d0004581171003034040100000d0062006c81910180c2049003580007504080c01c0750700003402458110785580080c45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 439660845 1250 439659595 439659611
    0x3070f080c0105090d090315020d06030305040e0a02070807321f1a060c0a020d0602090f0415092a02060708100e0f0c0c0604030206012c01170708030301060201 70
    0x5400e01c0b400ea008a48000106440401c045001d4906c544600c00500300f0740002200b458109442c1d0121511003c03040010000315869150140003038105014050a104220001808081c030510848a026030000885810201c00380d0b21000703c00d5040d60146001c0000076550f8251b010600c101002c2d8200304005040c418888803100d4401c2c41214404075401c60504460104104405210420900060360510759680b09015924500b00445400a420410060500c0280b02e20740d4060b0102d010f08503005d9945800e810104815601900081c6d410600f080742c0c01c21811809600c8502004821100c80203080d14a86810440160494071078000d07030404020800581d03481400c040d44070201e014200da9850400742464400300c1e00400820220040303c1c080303220216650262410080750908841b039902d043d2030300035201d82080c03051703842e0409408003508059a2003240c2140141c0841c1c00081c050f840c1460003014840c0040c000c40d20740c000c9480208840c00180700071800b804c02d0360008542a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 439662095 1250 439660845 439660867
    0x30609140f060a14040b130c0b0a050a0f170a020a0909050a0b1005120a050c0c1902010912050a0609031e09150504061b0816030c020411040614070503070f08 69
    0x40d000d800841021100d100c100300004441d810200d070003403000c1079104106017680c80e0a0f19a00101e2700400e42251012922030742032a4480014603181d4a40e5803048d503054401c40003520042000022661026103400004006449a40c0075241032026864694809541ea9400000301c0394155410b010240d101c151a581c2428080c050008084039803520038502120241c0c441d45d5004041c0c146007003991202c000c2004c4508031425607807045030080035525821400c04450a43c461801805c0340414442000020100c203d03500100d1040e0304140904070b009180e940306e200070001201e044003480b80700f40017500014101000e444549031540c65009090f0700349425100e1a40b001881ca07401c00404010500c01560f01038501d00c0350400d106c44a034984000d504d09490140250072031582e0741505044464240360b440711910035254002d07101040f48a07080f18014105100d1805002c020540001031286500c0d00d007030080141c103006070141d138240303004c0340d03030382144450f40002c00d407410100410035510f10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 439663345 1250 439662095 439662101
    0x13020712050405010813030201110c030d0c03060503030a050903011d0d020f06060f091b030a020d1503050d0f0e21010b090103050c06090109031e150501030804030609140f060a 77
    0x140d0328244039007064580400200648801000d4160903401e452503401054001d40000c038403159000355458031a4552003a1039070f82e41203500c4900d607079410125000f516a010344a03070700986c0c5024000d5850300c0d9030384034107407642e034007170303000c0076003540da2000b03409440100c0394249180444500003416241403030711002498519003180c1900e5542002042c000c080d81c960400c0c00110038161551203c41d0b64902040701c0c00d0103c856805d11800c1c0001c100802445964002c18683c010741c4000c021a80071100c54900410340360000070205e0784a40f040103002030251900c1c454980c3d4074504180e80c1010b42c40450400c0d030041e003d0203c8507901e800858400f030030a00131242c0c50803003603510080039803450f101c1e40d642e8201944440c2c0a0040021360a0390799100d01150405036800c2461900c0d244900e02000c004000c400009690001124040c004d1001e058003400741283d400c412307920304081c110b0b01d401005000d03000040307800c880e6486400e0751720310b0280403c101111000000c0c020b10b2800140e43d03415 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 439664595 1250 439663345 439663373
    0x231303061506051606090303090f060606032301030803061201020409060f23040216021e0906100504061209060e0610050303070201051b032502031c05030420130207 72
    0x20f0003000d1014102514201c942c034a55036801150102d41500641400c0e0700500c20711001409540200c10018184030341500010100c0e40c45070340c10050540c0181044c042904c40d0f0030002803c1600c030004101040860000d0741e0007140041044000100310b1042d642207900c40e9111401c815201d103410401c1c0301d1180e005e08004d280c44242003164145649514884507541060584141d6001ca20859074109424200144903805003400d03147c290242d0903003640d0008800b0562250301d0304000034856080a62070042c9a04103900c1d01c9041a04106090702e9040302150060325556070758400d038021500e1b5000d04460000c0c1d40010344110306012440d040c0e000e2080d080540070380d20402c03007800182d03480707411109a900d000610006260424814500707622680310034001080700038400f09603070613030f424500280030710840481d003601405082503203484040b441106d020840030701c001004150703001100d20070a400d42031408d02c0403034400c1c00a03002c4109a24180c07025580410050308000e01c50300030b824 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 439665845 1250 439664595 439664597
    0x31707030b0d052a030c10021f1b050901080708060114070b10170705040504080903010e03040e0609010f0e13120f0306090902060703051b010c05031905010501231303061506 76
    0x304c80d00b1000400e0351224600151402824803a40340c41c2c070984280580c40b00303034044404898030403490021b0075000d002103401c406111a1010824128140101d0484000d407006858103a02e55641e04415100b125004042606002c0c41141064007411110014074905104030998505401d0100078480764070000d4001da01c00a640c0c00c5107480956002034510202c0c1d03400c42c1c000c81c456480d0302d000401c41c01940d500035003542c20215800c40a81004c8050026034110380c07007c4445664072020812101001e20501c4403401c5552070502641d000b9410780342d48010000d52038801c1031a184d032403404448404101e000003400290300405c0701c81e03050080c50014202c0e15020b21042100740c0014900e4826000002d00b4002d0003d0031003161000d0b42d01d410b01d42800e2000810420032101d5016000740d10482d040c214402017900b00002808440c404c480c140ca8043c0c1d1740304060a19441500d120b000c022407a2031540c14288501c2603011000c4521601442c418600421404000015000340840e5600464 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 439667095 1250 439665845 439665913
    0x1308160503060a1e020c01060e100b161109040501231b0715020703030b040e06040302120d060e090c10090b090d3219031707030b0d05 59
    0x1003550700240043e00000400c800046008514030200c0c00d1080319000c40115a0010031001d20505e81036111104071200c0320891030756599007500c10447c020080c0682d402d640390501031514032040d440c070345d42040b500c1703003100125640100000901c0034004440480c0c3d00d030346071a82604100c2100c928441c9204014982180c00d080c803074014102c007081100ca04c84000700c0410b440090005090130507010106055046681d540e0604004000e020400440c41c0074608168000c07510003000602d851040b605503016003901c100e003846c1d07120203a0107000c40340d200503100c40000c11070b500c038104040d005141001c01446030444420500c20700400c2059400d080c04917004007003000700c0c0d00c40c0484085d80c000b25110f420841551034104103049014500380c0710364650440503c0507030104002035000b08011411903001401c1d55003000300004103448004c00040b20008050040d50a4500c1e058010100e03080c080f801c140380c0c002160030b078090000151019030190fa20011110309003000e119002004007124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 439668345 1250 439667095 439667099
    0x9160912020a030b0615040e06030d09150c02061c0506270f0a09080d0504020a05060a0e0405180f1c020c09042a0b040302280b0a090308130816 63
    0x90b080c518912028007000308850000e9503e0f0744009091104042c5030700034948603038a81e00d0075400c1034403c5a1142c000c0c070503120458410fa0080c0b4100b011105069981042010581d130211744420010300300300e800070404d00800a18803071180c090241e151401d60006001d01d0102d042180e02254036070070301c060084840f000300c1007a0109100c968000c0c1c03001e8034901581c6a68030034a005104100000e8a010004241d582c12411350350400c2d03000b0342c021907054000a4031201000700910032692420049000481c00196038280303030b00500e600043c000b4010b80031454a4010505001d01c07485d442c0c0072600805400104404401c03008401110584000c0c417010300c2001c0460817940740940060529805407000100d040c0610711102050308190119502190344e442850880350054002248646003ca4405494900d0002e4900702003c1c48003500c2162850a4003184a59000038006410007405c000044003007904000100905034031170301b83c400340c513191400003401c1c0000c21940c088012006101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 439669595 1250 439668345 439668349
    0x503030c0307020f01151d1017120d150806041a09210a0914370f03110f090a0209041503060515060a0203071205090916091202 56
    0xa89a0040200661039640d48400006034540580c00558207040c0d82400890f0703100c2440e03035070150100da0040561300d515007540a0000760004040314128400d0742c01d00010041c0400c0580c1101d1702582c940165071900c001d24184100c507a001203280711400b900c601401c940074104811003001442d007040607007001d04207543d40c0c05903200c3c81122031280020400108031001001d00501c0d0061100d84c00e00b5a8954020f94281d034580c10a1080b0720120310720003030001e030740390400d00b100c25400402820310400060405040c41c21501d6425218408025110029684c013240d2007180003400c038480c584c050300c1c2c0c030b10b01d0560404110590700e207000d001902c0d040d580680310b40441541241d502c110140e2940645800701d001050548211221541007040c0003041c41401ea0140c0d002e00c3c10003400701d1010b100310042c0009803280c40103c10044c1d10030000000850305800c2d00d500711403c149802d52402d41d542000480c0b80409503001e00080d80e801e807040c0c00f810b402026000040200038610300d055201600 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 439670845 1250 439669595 439669597
    0xa0f170a03020307060b0406210506070c41062401050711040b0d060b03011b080106230705010f05060306012d05030d11070501050316050a021c02030706050c070503 72
    0x40c000d00e81078803145181b045a40310f810180c050900d0803040d80306400c425070202480d04003920292203500440000c24039692159500c1c0e1823060304001d000d003484051001000d1850b1210049000001c4141c0c6007440408681041c0b51442068400502484c20b091208042c010300003c1c50204078a40000541d0701c0340d0300401501c1c00e950300602c005035500c0c41c0a0101d4054880c1c0302c03900c0e41c4000b906000c4420400c06070300408914600b41c00030480c0b0360320346088240e0600482c0d00d03140881c3c41c0900401400d40305101c10143c140506903090408244128981500e8100403c200e4907079460380104013507014184140f43e0721000440040c03459500d4090040c034120040840c092098160016900440c2c00e0399040000800028040f906815400362004040c0c00d40304007802da41d4007403d040010203602c00d20a49000d4007031000180d141c000144800d44480e400022840c044d07001e461520780c07405403139600602d40ea1140e6005903a9440c024500b81c02221402068042e1200040c0030180c04a1030000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 439672095 1250 439670845 439670857
    0xa0b011d060d0b161707030f11070305220e0c040518010608060d050309060315090a0624020c03070807090f06030503040614040e010801020403060c0503040b150f0a0f170a030203 78
    0x608507121000c600013003111241c1829031407040c2c0001d00300a0007200c5915511902c1080780f452805c11020b90080c500074001d01c01c118001c0c0c0010424820180313044200c0602c0307904111a585066090b603030307416001003501000c032071420b01d880c17000c40c1c10059030400190103200708c01c0c0701e40070040b00d6041074006400302002811280c0a5895128010704000c810011280b070040020011134481c40c0c1035419100c1d41c400b00040c140119082c402064038840075001d410103488560019041514401c0540b00481c0c0071a01544114491641c5803191074400780b2030709010303200400144c25154108038080d401e8807000f5010040c040c1c44d101040000c43c0010013a102a2401483c01e003d606c01800c1e94200c281c0250380149820316002d100009410700150b00400489200e0042484070560840c000d0340e031800b0844000e001d602901000920707148840d44ca00404c03440040004900d001c021001c03810001c101d41220301d41d1a1040030500c0b003800c640e4009006142e22900410f101800c0e9500291640204 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 439673345 1250 439672095 439672111
    0x110303072a1b0906061119150f090201080106140d090516080a03080a05150d0305040b0c060105040e160902030601051905120121140a0b011d060d0b 65
    0x14020721460008600442615503820001000242180000d01007010000c0d11803041c6031460b2410000701c050090035905030030260761003d03142d007031f200030b08219956040003401c41ea2861410000207107110b06200b441480c0310810400601040e140c4005051440c0c103804c070905002c05403185500f019451412540320100005d4081101c526500e8080c0c60080002c1d1a125a40f1480002050304040003441400d014041e0340c6100080d110414a1000c50f070064858281c20031200c0090344144c140405035801803403007480d111b842d040d564242c610098011494140c6550803a0004100381c0c40d00b0301501401100c0b038406401554200e005441340440035100d15484660003100182d0a80c1c00350041c0c4111034454100014002c04d9100014201e5100d148009006a0100c001142c000710007168560494110710607d80901760549612080c001e050184441a01c640c48a03600061010100f007802000c1041c0c00b400c2008001c03070031801000c401400c00e4000c10000c200d11005c41c03400d11889070010b103c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 439674595 1250 439673345 439673387
    0x100302061809041506060e010915090b270901060503040308090106050d060603120e030304050103020c010b0d23011802010815040c020f0c0a030206070209071701030305030711030307 80
    0x541c0070900890200d00450380c807040709400c2205010780c1520440c0940c102c0c0342c04100041d12800706441d414080a0068001560b420302400034516200d01465100d503107081100c02d65503114850b00b541e42c411000010105000c40e2180302011000f5054011244111500c0c5001c3d818540010030501008201808016104011030a5421300391b0112028287c0076040c0e4101c0c40090810102030071b44d5100484200d21011000001170307110b0441c5a03111b806c01009149020315040046002c1e402542c15041075550300c03c0b8031405a516212182c1115200e4a41c0403502d100890070401c0da290801203003002641040d5801d0107022502c004503900c0b581c242080708541d00c908940c1c01390301109480280e0041d1902030131003c0c00d500081c03440f0708480d08100700c0300b07080c21040038410420311038400290031440034400c0000501d45a200d1503400719452800c0c0b1828094072120392402a002c1e88160040780001050002c00c3c0e610000c101002c4806800a52840c28400001807120070402602149500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 439675845 1250 439674595 439674607
    0x10e12031314060103061d011503020112020c061801060e1315020910120e03040305060a0509031c0203100b0715090602090310060e0a0e0d1407020a0b12060910030206 73
    0x124040140b010045240807035800b0f60316890103400a00c04100b4194100b0506000c04a130080d05010301166802107040011003d403840c0e00540d070840d040005440059001c0c050a460351008000e100d109040e02224a0950f01c0511221421154260444e04119240c030040001d01920301000c513880c140c0c0000d2200403003d50000410007809218603003030b4084c3c140c03a10205419408219401c0007581da0307504001c1030110300b414542d41d10652000174656000007002818010281d4412540150a0000c0c1c07031500c1c206482d0030030300240c21554888090f5000c001d000030401c5482c041e8000d0240304101902e032040c1780e150309100c00a000e5800803c0758451190304100200754054904a050103012103e03200030000d02c07000078000760b006003070360080b51000003000c4c00030300e008184007280e50202524080360007900403103400340c90300010b2a0700803042184100503190281201c004123800d415081d04c8200502010006640240c842c500c294054814014501803020441c002c07603038111113981e920340f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 439677095 1250 439675845 439675853
    0x1507020a03020a0b09030d080915090a08130f0f031112070e090109031103030f060d0305210a0c09081c09091d1e060c0c10050108010e010e120313 64
    0x46503400003500f012480d000002d0940184d0064640300b2022002d440d02034003120002c40e50f1000840349030a0561041868080c520f172019845508500c02c80e09454441d2103d0305c0f00fa11a9011000742ca0b50342d62101c00c104880309800c1c003003102400e04410103110041c5151500f4180e001c4180740316206941c2c0c60034200d040c08003082110014200820504514036003451040c1c002c00540c84160040b03010403c006400b40f401000f12449801d16100c1c40300513455003400d2214a52a9020486c1886001c2000004508401410303005521010940304d2280c80c050410006484080107000d0034450b55280c2803140c99008030340d504942410342d10038480c0d4240c4040c12512081954009112280381125070587c0bc81c080140424002803030045807108180214a2030703100c00482420082034102101141c1240c84107001805280d546408480381a0840b9a501003141c400ba401008280c0d91345e464440c56403001c2c002d414019030b1050282022a2029844103900e01c03005102c2ca91030511011060200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 439678345 1250 439677095 439677109
    0x103080409021c1b02010e01060e130f080c060a1802030d23070b01050a17060a0c0c1a060a09060605030c0c07030f080a140c0c091005030d120c03020306150702 70
    0x43c3c0148601030016101241c008440032200214000042d42407181d58894a20705004044c02c5842c00002e05000da6501039410b04106152423048604000300400080442d0240c00500080d280d110060300046c240844c4c500c0031a4041c03c5035202d404240002600940e6012480306140011800c0020803181d0b070404603451101d40c0072005c1d50b03241021a4a00a00c502f0800c0c0310b050f00c40903229400500c2e103440c0c40c3e078034200081f150992164405000600c10144030342007450b0440d400e0800c00c140c000c0542d01c60b1084280305c9070102800083e0000c010691500c10036210080c980100204100c42c24504010680e01c801040301c40301e68400101c00d120100c0401102d4000c40d00300e104003c0952491074110342c243c1c440140540012807101d04008000d03042e07070481d8250035580004100e48400704007400f02423240104080d118004400c0c001907203440500c2004a140044d079601400d40d0040001e00c0c08688600003190105071051080201c0c2d030b2240c8402e80c145000303000f0700544a03c0144006508 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 439679595 1250 439678345 439678387
    0x30f1f1202210313080c1903030309021507060b040b040e0712080c03120a0b030106051f0e04060f090e300d02040f031104090809010c05010e030a170906010308040902 73
    0x2d103c0043c1141030100000f4651040d203141d00b040e204058418002c104100c110115204c0b060610420b040000034040d40c4030607016480036000702560001500c000e152a0404081540c54031740307401c1840844e14081c840c2c42d01c0900100c4007000313840310751103d09654088038001d12082e040079102100a100c0305078180c4049401d0007045940c1c0384220001202a180c06441100c10305090110840540c90180a48800d4440117845204164644540c01c0100341d10410303c401481a10103903046d442e1a103000700c0c0082c0000b0030020303000c0b519103103080b4101c5030010f5203c003294100300c4400c0392070740c0c1c02055400303c1c041d0390307090041e1440c900d1081030562081c0e03441460024070002c0c0014284a14030591803c0300d010710300000b850801d44007488141c4201c00c0008090300020030961105600880314118010300604c00015502039070070702c40e40756500c580100b0022038220304504d2412140ea480f03085e80003000c40080d003402c1d45140c1d14680e0314055400740100d55a004a03012181420751188412 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 439680845 1250 439679595 439679659
    0x30115020c0607140708060f04080a0509030a030509210c09190c0e0a09140c030717102d1242140103020f0406030206030f1f1202 57
    0x3d594520303494903c410b0070201d03503050041d0040303c0000074040008a01c0c24822100c21980c101c06503103690381e520b0140e10008586050000602405c40300c0d880800075440c80c1031007501c03960340e00c00420082202401d5040300c86d903100a115040081000d601044154407018280d401c5207907900c03000c400c0c85000001131410603005140480c401090783d842120610409030585643c1d03542610b985c02c40d0140c0702902e0150482c0d00810000c1074140e850540110781c0301882e46044031a80300786011484010400307580e4403850600101c03050100e0176050150108e000c190800e005940007035410404400c5280344200840507055070040c4040c0079514030655840c03030140c4003038a25041c0d844000c1c448841a010070254400340415882d070055160301c1480003400084011480c244e296074200400c03088090303250398010703448003000030041e01c482000d1401030722140c519000500c1c162900d40c503069050b101c10300e0b503600d0503042040050150001c060310160180c68010008000043c10742255074460b100907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 439682095 1250 439680845 439680847
    0x20901020c13020d05060616030f090f06020c030c0301020c1b15030c0307030b0103020c0c12210715061802070f05121201050f092d01090b090906010b030115020c06 72
    0x16860b2000d40c0241200e10050304100511340700d881c01c0c441da5000d0342c140101c00c00b26000c08480800d010b901a041c0245403482d00c614550381342c6001849242c0c140c0c0c030a0001d644013456003482860188a14924110180c00860400d112807001c43d98841007005612290440714080c1e111076115009040c004900e55400c259507420408d2200c940c6520885030030000070b14120542225620a000302c902400016000f419249106000c10103160104080c4009503c1344866856503080002c0d400144d061000004549030a0b403030604041030560900454110381c07030903100344203d441415003080c0d07003019150010f0b01d80100b480c000441c00d00122016020340b01d900e6001d100c0071010402004e47c14a0b6000304801d590740e030028003440c11000c200c0f09600c1044040065030420383c0e0030710080b50581400003208a0b000310004020b9030a020b8200f40175a03515103111200d141003002c441604036041d4402010b19614203240ca441c0c500060294005000c5000300e440304880c070800c46280410001400e03d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 439683345 1250 439682095 439682119
    0x405210705160905060d0506070f02030913060602070b0c06161701080601062a110310140105010906021b01050c01060e0f0a0612050d030c030905030a0206040605060d15020901020c 79
    0x2100d101c0070510403209403138244400100f5a0070036644d141040ca07404002011241c0740c94605461403400448440c04512007070180700703030655912004110400d142c5d00009207076030131b01d5802801c090a6070803500e1660810813103040300754000902c0ca0390090035209041c11400707003034004550861290300a240030050000020a5032180070413202e04035080c43d2550f0780c00d031500604031000844c03000018040161100701b08000304008038080f607011003004050b03400e41882c0d03101c6802207450170b1140d80b0f5031104980c0184015600f280300c03103018024a00082c181d4401040b145a010691030024504200300400c041504001c03d400c4803000e05151070710040103180c492401105a2003c540211205080030000103507a20341c0300e8500c1c00d85400030003070003c4a42d03002081c0d014003d810304003410103070340d407401d1800300c6c40c288080c04590107960b01a01c02401d0a040841c02d950001c0c107202d10400301b005409000a602d0303644c00081d08840480075031583d80c0140142d0030100c0300c003c4030340c01c2500e101c20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 439684595 1250 439683345 439683373
    0x160e061c1a15071b06020604050d08040b1603060801020f070c060e03122d0a0906030612030305041a040c18020a05030612010e01150608060303030405210705 69
    0x8209114102008011251082810140d24860504225003000b0646038581140882500505805001d80140c5041c1624000040b00d800b00e81d610140c0182c001d4000c3c4810031000b841400c1924541e8641010541800c2d198800e0882c1e0182c0a00b0740030b0050740c01741c9400c42c0603400c0307200280074280003107440704c2d01000131302c2c155405444122100345810202042c03060080340204608100500107040980d0710000d420741c0743c2c0c03040d840282d24050542c26444079100301c21702c0c0c20880c034030520416212100404007a1a03440303d0b030020400d01d410198240620040b001914816580601d0301007815165401c005481c07001400d47d10704c0560202c401c12050001030310b0032034100e40070350385000551040b103114107080b4006c14141000080d41000480c9244c9071074600514050b120354000103101d13102070b40c41400c4a030030080e00d0750b0840031150104116600081c1c1c140c4d001d141980038500d18a041c2c2e98551701da100101071401c034884804501446071080328152980f80383d000c000c40e0720713402c0c031428 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 439685845 1250 439684595 439684627
    0x9120309020a091406060c0a080d090312090302060601050a1e0504230108010b09041b030516051c0e07030506070c110123090d08040b0c07050d0b160e06 67
    0xa00768002d4801d40000103190041c3d11820482c91160030300a0706545030081001041d84c007840300c0f20660300c18103003e00046031a40700100502c5510913030010b030202080c60064640c15207980170003c4607140100c00c3e0040381d000302d00700754015401d2804079540e00d035244050302d00705c2c1044420340441d543c50f21a60410b60b0090010002d41c0d101c00b614100919100f0502c490540e0030300d20740b500048040004000700c81569002d00401c1e000280085002d404541c113004c400c0350400301038030009481d80b040c0183c450000e5903200155580d0f14003240f600551184420ba0698040103000704c1c196140321070845410706000040280d94410162452420300000c010101c1070503a800755070b1240d81e840e18206035801001c260803071a6540c0d000c1c040c0c0320610180340e001a04011002a00640c800c0078240c001080c10300140060031941035a540c0b03654103484464a400f2035504041d00405c0c3c1c081208c40811410806550312000d4000700d81d10b008e010600440700740740f4066031603402400101d500421854041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 439687095 1250 439685845 439685861
    0x2003010f060e0a0f030f0201030f1a0f04060b1e04030807062c1e0c0307060309060b060a0519020109080316081005060d050a060f0b130e010e0c030604091203 69
    0x164440303007200311003010000b6030f00d8644101016002001e030700f04000750416080e10b5100740141400158810103d400c44180c030000281c24040c11411445180c403450400301c09800c0e848280c404100042c02c02000150138441e030100c49540c40d5400e40140d0406036104220f50203035a0091030300b500d4807124940312020780030208400c2e44007401c2c08401e440c040260640d81c441c007000b9000034020f01a0603030101448902d030301c03c0c2000714000c410150b10303251410400c03440102401d96000407100010301344842102c8040d00c0451285008011074132060340d128095030703000004100e01e080131107484403082c4d0040c1511707030005052120100402481d0451070700305100341142e544504071039903101c3e64819250070640c040c555002c103080c0004610440198030040d44204010800220191102c58042e81c2009a6210880d803640000e045110303c440c0103c504020700781c1074010324455041903282ea4820f80001c1c01d52134080c0b03001c400951140d48640003c5501600324641e05076000d03000c18020302504101c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 439688345 1250 439687095 439687097
    0x2040908040315180818030618070b090108011820031e0f0c07020f03030c01020a020d030504081e0d05150406140f0f0d0b090d140a0c03032003010f06 66
    0x80026481c8071400e0045007240d50600891084c0c2400b20303503e0b80c1071600311003040724002c000c4001d00c907400e4030304101d0b003806201800485200840000080c606c2c00402e6040f170020640203025414440c0d82240c805410343c0d05660a21082003200c2c4010001400b002c1020b010304881c401143c6820a1400c0040d40a1314000010000d244c941031440501400c05488203840d031410500000c214101000142180300d100030241000d2041c9040000e2441d0040409800146d41c0010855001c2e43c0400c8603c0c0e0f02e620a0070305114510b059180d08501d07029a1584c14128080c01120f02c5190190908803041c02130502020001d81c180f44100400003c580c00030903008601c1c010010070203d00b0162144010b02c1c00900000d2404101400c2c0409100c0c5242d401c3e81040400d038003040090b0340c4015142c4902d040074012300004c0007801006103800c50b10142030822030300c10000d920501d540240c0003039400781c250074040350900b4658201400036000102d081c070fa00c6d1000c80003080d1540d10b05444001c40d111 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 439689595 1250 439688345 439688363
    0x19080a02010819050f270a0201030b0303120c0d0b10120c12020a0207080c0d0c0909020d0b0a0c020606060901050315031603060915021204030e010516030f110609070e040c03020409080403 82
    0x1d1b00c10390140c5c06a03074110800d040c1d11541400380158401d401103d00d225000d010382e13040044580340030107a01e506480c1c0952401d0017040319007030094607101d00d2901560885045600c01c00e144030142500ca0a040d02442054584441210082c0245000c40840c42211002c42d900c0308911002500c8000e5405401414014620391420300e1030100a100c141135000303c683c5010500c0e00320940004c01c2014001c0380c0114051003158089a01d03c01d144d0300c925010b13070002c150001c09100090502100030222032151300c0500c151081a40d100c010f0703135800000420541c11a40c0f080300028900010100020010106080c0c040200101c03908007102c401d205d40d103000501c81d9040800000c1e40141020040c0c480d05941c00100401d1045044031440d0806041640c41d00111019542800340100425000729020302c0e420903a090b4014018100844003002428803800c18688071910341040703100c0c0d000004030050116040c0003190304001e00850340104100410059880c0120080c0c0240c801640e07a044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 439690845 1250 439689595 439689631
    0x1140603061c0503090a180f0e1f060e0708010e091902090402030106150c0b0a05090c1306030c092901051918031202121305010309140105100519080a02010819050f 72
    0x180d000c2c1909d02c05070b82e4081c0542c5580c0f0454000740c20161400c400050fa00c4507000941031154180c06400703003205135140c14482d810040141040300c00904201c1003a44403d001d0480c40c030329442015400c036811924680d180d00c0d540002800341079160007044000907521426941207400016981c8128410300440020759103c00c1204100c0d2070895840003a600998502c140602c1c04101c0985040140b000c0011010f4032502c0b800488a02900864005940e81c03101e034100c000314242d48000300140c1107e00204805410000b0b2481c0244c4049846c4014503040c04c08400e401000d010b0041501e000302892035640d01d007000c5102c1d445001c4d99031301501a4814001e0307403030341d141c0c00c44403501e02c400000041140f6020046009001d042c00548a00d002185000c1c500303402070007060f0082902000c14546581020b0800105003c040004c600d040c28400080010105c085040c00890750242480d4507da136031520740e960845840d040740e03010340d840c1804108413076400446650096003806071544a0384 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 439692095 1250 439690845 439690871
    0x806090d0c050613031e0509090a090c05060a0e04020315100503040804030813030f030c0605180601050f04022101240509040908040f03050601140603061c0503090a18 73
    0x70702018030180040e00902c000a00c80550722189030f4181d03120385400c0607410482600c00ca950030b010901ca00014400042c403500501c0c002408940015507010b041003005050f0350b84040e0794100d4800d1500401010030b104113850300071404800140c2d1b020b80255070740e00d032901d83c40c000071880c1c0e50524400e00b0405041d602880c42001900d10544c0e101071100e28040c02d5448101c2c06070031502c0f85a41010001601100056080000d031745602c2c407a4444400025041c6004000d452000b0802c000c00b1103080b001d5a05281c0000703480741169000e0302c0d1080e0381041e00022a01070710540c101500d8400d0700004404c0c5800e59600b945040760415154030350400780c01e0321200d5071350164880c45c0b40011014084110540303425071000f03081e24400d00f40c041c41d0585d260622460211145c1c0103035040d801640040081105034903000071780e42c80c101c802a01c0c40c6406400540310b0706190303018440c201c1c070040000701003160420484040100003016001c22035a144106804110a806421201401d003100f0322846 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 439693345 1250 439692095 439692107
    0xe03040302181015020f0c060903191502030c0307020601140915010c021f0201110a020d0f050c1b030d0206090705010e040204090219020d090b07080f130806090d 71
    0x541d034018221008000903110b50381d180e280240c01a003600495590026031046840c900468200690700984180940d075890700c0e08000303640a8880c040c240400440900c3d55000c41c40e0b0b5641e15401c3c00004409143d401c0c072406101d4100ae2070180a40b00100380f103044007154000d0340c400c0707600d5400c0f188107030380f10300b420f50200c5407050b02030703410205090100303112000c1c424540605070010324003044050642d400050f1240f2009080da0680c0300800c1901206c50380c280111203041e80c0603c0d01324a40300c03e44034000e68840c4c1e003051000c00c0222041032244124495400c507001050408115207500d07180b2070410143d03d1912100610a10620403040240b81c004600c0a04c83d418083c00344c61854174250040d80c0481100803a03940c0316500b0800410301a10700e02c0503064510310040c6010454040040c0a0b240c91031020312401400192402004916001000c4a40d800c0d0703c10140341c1c5030111800c200f2800c1c06403840a511031480c185011844240000f0918800c94240040b1550031241e00700903140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 439694595 1250 439693345 439693349
    0x7020a030503191e05010504060605090307031202120c010c17060a0e0712090506090706020601031e08090405280605010c061a1002160e062101020d090c0503010e0304 73
    0x40380c024400100109031041c00503c2e02020b0150104081c030070500920345013500131032903142190391500140074a060620901d0054009801d121b031400d50342000103540c034070079480020a000110400b04058070720901440284030340f01200d0039140c4c004512518040c1c40d541001c1000921400c4d49046852002400c95004001c0900003a00a030706004031601415801881b8605000101c05240205c800354454403134428000d8021344203504214144608217803465000c4d0045503c03a40051002ca10700144007806c09220008600114820345017000c01c1e4020306440942c0140f0f000c041000368100c0300d4030001d611030354110301c0d00b0b507902a58408089800e98052503001a01c00004080041c0c180c3c0e200b4132040b219a04400010004000080c240d81e40500002006812001440030701c6200c07101e402c0050705110000c80c40e42d10308000421107030189050103014590501c840c8050071071007941214082ca0325450b0520214513103080c58000b410740c5201301da00940c40d10400500014002c020380741 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 439695845 1250 439694595 439694597
    0x100311131401170d2609160305010501081b0604091808040303020f0d030c0e01080a09080f19050712450803090609090a0e01050a090302100507141c0e0307020907020a03 74
    0x21294171800c880c01d92404004100c4d55881c459405840805903180d04150020341c4510004138244d07044c007494509000321101011500f04c0c1940c0707640c94079665a002e40e07080c1e0324050700015a645d1500e82d28822001490406040910b00140201c01d1643c08640c162a01d0b0b6410100c84a24591180460031107003080320401c001086616403800b69841109141d4011a40d2580892013040d00e03120b40c403486d40500c0000044a500080c031110014500d00c450700341080301c0c207020381445003584841da800308040310b41c4020420301d006817000a80c401140044107440244000d100e0380c0e160041c210f461219000f450043d801040340000301944000101c400502c40070340414105080e40040c806009000b0700300d00022611916441e03800c00d007d1041c00c5c0700c0c00541101040488950401901700308402400c00001810030081010a5801100c540800002102030b15510007181412804084140d03101c0c1c407070b884c01c4c030710b05080e42040000500340b0070b40200e9203241d1603250140142c0ea18001030000070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 439697095 1250 439695845 439695887
    0x3052401200a080d14010e042102190308011e15030e1903081506090127082b0206090a080f0c010f050a05100311131401170d 55
    0x28403200407100c801a0400c180021140b00c80e00c2666042c001e81c100c181c214203100c0e82c46107180078401c41d0340380842c01081308082c0702c181802c19071101114000c507406012041c02c40100e04105882c0308100003850101c0d001c020b0843c6039118600100110020f204802d4880d00c0200c42618100c4580a0041258490408115905604041540546140000c10910b806102c0d80204000408091403071114440e1b92210201e141c64480000400071622460340148000d2103103903900e0f41c00601000c0c1c1101c0c0a40c141c42150f10030340ba14000701115811040300d5001e49081ca00000080a81c100310400c3c22020f41c1541d0b002c003030801c0744d03983c4c4120f41c1169540d000a41d810045034079400100341800e05040c92502c1c100311b00036081e003034803000c00d42c81242603176030002c001030104c02d4816640c0040c24407265103101484c5440c1c0d0001401540202ba105201c1c104c40614843e030250b0004000000b0003031240070702d60352000111100c2c0a0300988200380d0041d4080030380300b203215080b40481000b07800554 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 439698345 1250 439697095 439697117
    0x31b0512011b032a0c02090907090f090201020a03030b1212070b09161a0f03010b07120203041202270f0f0708040f060507110f0703030e09100308030903091003052401 73
    0x1ca90342d900149401130a0003880c4044c1009a1642d07890340e4460345990f402041d04a00c0c01003003070202c0e4100c07121410140d140c11000b10041c3c1c1d02080071030403242c0503e400720703488045a0010b44000c1a41088141901c5082d240c03001c10350030000a0610350b4000d41591400da40c4140b200c1e9107444074001040c104d244c2a910911200407481c0840455113044849141030000360140d00549510070780100c1000c1c0000300c5e8440802c503095940b41801d24480c8040d60505140581003a88907074a008001d104d1011040b00c08440c44007541049140b020310800c00c403007401c0081c50401c00d154141c5003a20381d0085203001a2041e40108202409168490480b110704407a9880f84002400c010780740100300620000c0241614908100d03e001403a40107016042045c0355141c0504040d007500e0009000d29040000c204451001c181080c0403a40c01000e0f1903569071358240054154461401d00c80d601c03120480b1100811549680824400c0300d10040f861540ca00102e000340703980c0b04c0e03030b000107000440c50146 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 439699595 1250 439698345 439698401
    0x604030c030213140a0e0c0409050601090b060706180201110706020601060323070908100e06060105090d050d0519110d120b09161b0309031b0512011b03 67
    0x10b6800380d04809000190078030641c0d844480d00c041c140e8800880645a044410441106008a0401c40c0c000c0b1410403603c403907070352090b850b0032052007008c37074070b6036600c1c01d0848503100e501c1244c1035030b07030301041c100422a40c903004c48000d40742ca1101680050900c0c002541c906c2d6000983e0320682c0e80310f030002c2203140c4c40c10508602070404804002d09a00d0358444980381030325841c00150080c10315841c4d0a00c1c207800d051441d0328003100e0200d420034450030101c10402c0d0a9012840c1034008000b8602135903210030180100329010f4510600038400d110701501c40080a03032000140c0701c1034006550003a1f101c049141c0807281030140203041d28042d088242c002840c503000ba0006004100424400b1460700e0301080010b0344403004581c2100d03900ca0448404440c1030b0700c1b440903109940803908000c5000c10603140101060b605020003080c40c40c6100b10f413189100e001102030000c1800401d990500d1141c8003219000c0c0c038083d040c18045110100805940ca40a80945e410308400050460880b40c070b1003007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 439700845 1250 439699595 439699609
    0x2070611120a0e03160303020c1903080912030a0f02010f1a010c0204110a0302092e0f0318060f050a020a050d0902120d0c03020606030d0f05090f040c020706020c0604030c0302 77
    0x206090600c800c210f07001074551814014240140c820301c0c031980c00e0a155080190402c0c0154140300d206075082d0044800740c030b120490381001d0304d40000303404e601c461850010444007545421001e10b14070001c500302c4855035000351006c41105007035000348164502007420a0540300100b120583c0c030001d942a401140d44035041c40d03c901d03400200b0110b050f125101c0380d5a55580020142d20020b600040c122a0500f0606240182309544130500c0100072041116620f440d5000d01c144010444500701001c4140c1c4242c01c075080762041d40a410220303401629103c0d0061451003100003400f4141070000701140458400ea80c404c003140e484041c0303400340c40400c450040c40301078000c0380d104000f506108240340e010070284540c2440c2c3d0300c52050000e81820045c3c41c1c0440107102c1c40c481ea1003680d500507204d5000300032aa040c6241d08146481c0d02c500b00000c0c081c000d6408019412074504541c5045465000620004403500d507000c2e940011085400d110301d9104502000d80502d10000d0100b0050902d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 439702095 1250 439700845 439700857
    0x606090e040c050a061d0f01090b03070e041803110c03060a021b010f02031f14040903020f0607120b010c0206070209040503071505061e10081816060207061112 70
    0x1e02d0b40c0950f61501c00040413020326030001000a464452424104110050101e01040080710800201c1c907000000902c080c11900920300081c1000c40403c0100f0b00403c158131507581c000b40305001c81c401c5404017088400003c401a00080c0380750114100c1c0190226008090590280c05130941c0d550b00300400010350701c189100c2400c07040c01071003080004400c1c410b0030200381000c040565241030100000c08806800c66002c82040100c82d02041a21401e140b043c240200660b800b2030640440c0c201a420030f400349058510600443c020411981e40c05444c143c525111028108103220240c4011110b02c6c0d40d8a90007034018504102e40030140c6408046c080d4054411022a803a04900307540f40480480d9040700c2c1c0d0703c141d44503002e10402e0318091650000d41200c18600300c0b40c0401c940001070300c41601700807079401d00030b0940202d91340750004121000c00e01502c804941da1051000035504c14081c0902c00e00006009045001c20a2449880b58010710319860000340520f2041c103103035411a40c002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 439703345 1250 439702095 439702103
    0xf030c0806090c0c100b010e031f1107080703030b03010c03090c03021207080304060509131a24070b04120c0305040b130302130f05151e1903050618010606090e04 71
    0x103000204c1c101200700b1007001c100c00e0300b1401082c48011702c1e00241200e03404d840110b2098100c02c52030050700c1030711401d695015804040c040303450848680c0001483c410b0280c0580001c0000540c00b00741130309078000c41104003080e4000c00001c211581c04908991080d000101030010241c02000503180c601c0c003540c5402c1154003910f0595941c0d0441a00c2d5034007651180000c5030000c20044803a00c0c202068943c0b41075010350500400c8410f072604001550000c035040d2240000e82e0007061000c0b420114040c260045903a00d5a0310140c900340a460317510103c1e000c94000850f000c409031000d20500d103100780369030725442e002d05050a024044032035800043c4880c2c1c0c007010306400000035aa42c10400341070a156240d00140d01c804401c5d80c002a500010204991200b400c400080580c8820042d000501d845003000c040d040440c00c00524810314001e0030244400f41e02c4004000c0c8400410b80a002c0e200e80f0903583c08855803001c2e46c0307003a10440d109a0740414000c040c1000314010b8002c0003a4407600c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 439704595 1250 439703345 439703347
    0x140315270403090e0f060a0303050d060506030112060f0c020303070809010b09011203030b0415121509110108070206062d030a1407080a020603060f0a03060f0c0f030c0806090c 77
    0x240c03a80c65298501210254001288410104a20003400009640281c400c0951006500d460000700f03c2c200101e10000701081400a50440038016a6000101405d8002c210035900d5a5a59550301d00b006010380981c4c0349450252002c1003003025104008440005401444c2103503119103095031070900040140c0f106540351086c141c2107644100d103281c0640f0326020034613400c1800303007001002c030750200c000a4012845d118504034420303001c06102d8115600c803500c030860741a151030b055800d4115481c00301030b40d0b07003400054400c00c1071a1030301401004003a600e603d600c1d582e0b10b400b241d0b10758098a11540004203006000002c01c0800989010f6001d80700540d16503000203c0842c0c44d01009060580f51001800d806d400b40351424019034000300548001400792100640002e00e40d440094640c034800c1c81c110644401a84070408043c00071038128108210354000314046070064030004208000081424081c158a1401b92040000f02201c690315030705241e41c0c0c0801d01c168101d002e40480e1001c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 439705845 1250 439704595 439704649
    0x3030f06061c020c0102300a05150d06020d151a03040c0b0a1d0a0305120a031805010b1c050d1d040216050f0d0203030a050402010c0f05010c140315 65
    0x42c0e60004010740000c0c0400140e4950f5210352800101d60504200c01e05003841c0c2d01c5403056158a241407d811050b00c00f40000d02d42c543c4d0340c4540614401e07044650b08035800400c0b400c00e0119682c0500501c04c011207003403182c43d602e84051b020644441c003036854420007a10000d40900002d002556002e8071410390382c00004e480f403401c00041e80000e2070081c0080c020f1194100c1c0341a024070800100401650b143c0005401c56803001c0e110001c02c4022261100c0118000701d10300d110b0f03044003000781010341604200d80e1441c2042c2d401381ca52003040358007900d115100410700214070548000c205420102404481741841001c56006840d80080555810300c030640001035500d501c002c02040d410000c140c0c0a0701800c0c91f001e4100040c40840d80600c1e04208441005580c02104880e44011030800c00142c0c0e659610069071550182c03d40500102c0c4480311502c02c0040551000300d80c3c08a903152400109682016005e0900c4221402a40c401005c2406010341c201004e418030451688034403460145 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 439707095 1250 439705845 439705897
    0xf0f02150702120118060b0f1005032208090103050a110d020702150a020a030f020708070303050909060f01020705060906070209040501091b080a020d03030906050f07030e03030f0606 80
    0x111012031100d80110001410821842c091810641c40000c2000074071000000c40b440059022500c00d01800e111349a58400d8000d64400505001c1408014849103020b1986507000b405c0f5001101d40340359513200c112103030404000c402136511000741e010151519105102004501428001e0a030601c4c19403100c450518032901c4c18003404240d11203da0040e140c2d02c003401000701507601c0300780c87d68070944100803070f00e49140c0c046420141140c040c01d004401c440705050403403800003194000691802035900c08410190702000811604804861301d411640f11401007081a2508400141c00742c0d0001d4000c000c1424220301500015000414103820000c0d1500401c00f03569041b18200c03856592070304207104001c24503c00d8555103001c820f07014645403e00c0c80c800c0c0c0d03c040782d1002034450300380e402607442058429004004042e5210303030180103500f0290310009005400799202c1003c64108101420700110000c10382e4820054440d0428068481205214503907001141e6003003c1500032a10461031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 439708345 1250 439707095 439707109
    0x110301050a0f0c0e0a03020906060d02030c0d11130603050c04050a0801050f071b0206030a111602010e0d03021b24040609150c030f2003031911070f0f02 67
    0x166024100200d0040b1880341c81008942d003000451090200144028900d51103240071002900c0d815100d581043d2031310700025500e4041c0b20705078925240000104000315507180003800c40e0328110341c82440b45100b80800120980100d040718154181e15420412030540f29070486030700b10b0f40700e020722450561204041104041300d0340103c02540e4444081c000440c1c3e00170802070303202c2e105e4a00740b000c0c6010b20480c0320022002801c064810078011000c0307070001d0480c1d44104203038540308120300c0d640c41080007100c248c0414a001030340802c110b06a040310310b00f42030003010140b82d41a400351404801060714003d60300800504940c100450b13a00c442140e8a6501e44402801d5410741c103181c44500c0d1101c020001d20543c1c020310014201c1c6050389441e1508401009000b036418207012000441c110001c03030fa003101020001018074070039603a41d44403a2000c40254000d04110341c0580d141c184486401040c3c4810602c44840010700b040390b00c020461002004000b2071003440d100d1040d0500c0e400040762 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 439709595 1250 439708345 439708351
    0x1060e190b0c1507030b0307120215120901050705030903040e04080c0f072309010b0703032406080a06030218040503040305011a010318080409020c010b03010e030a110a0206030601030911030105 85
    0xc540c0c0302070088500703c00a21803c6500c00e01a140038009940d02c000032a0f2a607682d44a82494064001d81640442d65404400b115810a20003850340b5103106c40a140c0d0b4400c4240e401e89000d520b04000f24070054400e00c1181c0c4100c5140004614203860068041c0003414001e000391074072a000d0085030003d80c4103009100c80c02024034000c0c2861313402d0182600d89941c84903204c1e81d4441c1c031200154115207540502904580c2c90104440e1940c0113030070300768040e0114023901018400034050300008141440b000000b60f07651560b40107129a01c0d040e020b000ca41060102035031090a020301e2021040d04002020fa04c6446803003502c0c1050390300c1c1e40700d0382520340c4e0b1450400456811020ba815a59043c4908180300782d6420001000c1810303520b40b140781c0d21940c0070b070702c200d180c0000700324a940009400014898030301034000c010305113410b0100c0b91685c00c5106c4920000301c000141c00c139040c90004041204940041c504d1b4510b4803036000650040030600c0d0201c0780100c074180288110355080c401e0f548 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 439710845 1250 439709595 439709617
    0x220e0115050f03330d1713030c0602010f0501030f080a050d090302011d160b0309070512010917130e0a060e0708100f121e051e01110301060e190b 64
    0x48980610b03d101240310210941d441d4a529101142c4c1c100c0c2c0e603501a0311085290424407500384105030100c64006c61141031388401e426610040c0000400644496440440d01d16500030070014080b003122800b641c00c00e21002d8030b0102c00740100070108400900401200415042051030121014560001d40d202c00700240d016035940d038005140000400384162070503000c5000b074030f001c40641104408410150048803d00900403000904c065010800d031030103014018400d240701400020a2400307020f02c80b030308580d24002011140c0704003274600700356048164050040d485035414505d00c107104c800300038800b550707668842d04d0005200424101c082d0040c0b18035076401c03003289468120842d0000349680f100701070450b0710030108801c090521142d401c0c103500c15100d8000300c401e481c0c1080c8682c400c7c0e00c003922034002d14028034030305082604902e010000f00f00090004100101c1605600d000c00d10400000c14500f00340350310189401c644c0300b80d20078215510344409944a920306041c0d6040441c00c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 439712095 1250 439710845 439710871
    0xc040b0f0a0e0702010b01170a050c1c15120c060e1804030e010e030c030a08090d050d090306060b030402090a050a0e030d14010806010501140708041802220e0115050f03 74
    0x200051354203003e24044001c0a0900c400110386a5910180004005003080d10081d61400402c101004c1c4404071a506001080c925507407e52250713918000340446440d1023071b5100700b4500055680b640c03080c5000d0464115840d03140061034810155803045150700c6150f44891041d425034071300d002c1c9002c90ba0148bc0031f5607641d001059400300240c101c5120120b02c0b48641d00c20b40600e859580c000405407011a41300c0d28083e242c40d10300000c2016450b1140c40101203000781c0500d0150303280d120580d0012030340200c4c4144085940c610008100d4070050f28007a4220707200344d0009080d41c0c19038020b2900b010300e998002400501c0c00082c107056030401e00c40000d000c0e0f21411000030095a0811aa01400040010b842554035040c0040c0110540b4203040081e001c0110f034403021702c281e00b02030714000c00049078040800702c1c1c0300036040004e41c4007200b1803814120210550803c200451040d10640720440210500c0340d081c14642c03406082885180c40411504000c2d4504a5246902460241551900740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 439713345 1250 439712095 439712101
    0x706080402271503010b0a1d0703020415080402180a0b0a0e010806040f02130e061902190513080102160212030f070204020a0309050a0b0a0615020c040b0f0a0e 70
    0x24090030b0700c507074640d000044140e0054881c604000180c100043d5551501c5698080002ca409015030408550340000010000a00740054a812450482d10070200360034541d1950000e508074041e50080000c0300e040d40704000c00e400d00990b166500540028545048114012420291140d01705e9200360040d8803039201e51364a00b060301544e000b429409150840e158105080d081d40c0c1d032401440940540d403186c1580003952035001300304059802182d000d00601e912610502c5c0d03903100940b007240001400c40030f144641c0c00f1a200f5039a10034a040c8442d08014200d4030100c805810480120364000c01c007040010f08a00c003440285a9807894520030003d50390743d03004200c850480c24109500d10b810810101d15508a050103c500b16907040300c0058a0301c806200803401040030750002031483c450410b014003840802d11b04039104d00103202040c02001d450f04280000c0d8501e4104010141e0f02c650f00c01d15140c5082e420240103064040e0004004814140000300341182d545e2080020349008028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 439714595 1250 439713345 439713349
    0x120311040e0403030b1f1b0201030213121b0621021b0a11010f08010909050a120816020f0d051e0f0a120204051315080609070609120b04140f0706080402 67
    0x1d50005506c01030304c0c002c0d000c0b02009016000c9800c0d008801d0851310b441c0d1000c402c5a0090341030b80d201c40d00e0490740d0a04561220700184003004029810b40340210703040f0000c05040039891410058421590700d80004020b6699454010201c030622080c49a80a0204106541c05004c02000f0141c01e0401000c1030550340c1800340ea046060000b4904002c4040b200c0c842c2d540c1c0007008281192a4103200052203495400d01600305440000c0c001c10501960240e0031015512000c01c0f80600e16182d18070b01d08100a040a80c2e41302020f518502041d00103546010045020b00d02800b410010714121074030503c0c3c3c3d101400e146602034881080c0100002c10014241c40e40104034164441c0d01e1b4400b1403406092000181c0c50700c1c444c0021101a0351558001140000311101d070500404c5a8412104c40382001381d11142c8800450241200155030994001003143d5003620000c00d0303a40000640100d0785460f02c1d88031112400552207a024441e0100d8200d200f041003041000a0116580d5409541400c2c81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 439715845 1250 439714595 439714609
    0xd021e0118030b1807031502040e0a0608060a1107170c0d020102040807050d020d051209040e1c0c0507030b0702061006050304121b0c150207080a120311040e0403030b 73
    0x305218400d15000c000b031000880c911002c6412903168a002c20b001240703540e105140614580000345000e112840e6415265800d40143c016078011100c103071340b01d940e001410021100c140c403424903250301c034401050180105030f200c80c80101301003692621b09101c42c0c50719400045400130f2080c64810001d8801a000340502c0f02e968516002e100a41c906031038001130581d0380c0c83c50b008442c411040402c2100171591900300c42e2142d9076001c41515480e90340740002f15110b41010218030300403418404100c4034007070b01084c2c215100555141e544800107060404507000c60740c800084807140b03c0c1c1c82020000c244e00307440603882401e1590044c080c91500062141c0c66007001d5010b1010300000340107100c0001c1180540c02c1c0301d01c12a26080d00c49510206559040107203032440079011000504010801d501180d4000710f6a01c80c40c0c080b49c0550380d031a9541652092a20f0006c2c1581c1d01280c0c0916000384603800081916690250050801d600c506003145481c50540b81200030940d230340b54590f5036050410b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 439717095 1250 439715845 439715867
    0x120c1407050f0c0a03050a080d020c0d0815060a0c0821040b0604060f05030316050c0406121109070c060f06090509060601020d02030a0203120912040b0c012a05090d021e01 75
    0xa0340400c0445e14554469503604d102c00b500512000002c55600e11100750744d03040d01c1c40204081c00300c8940e68890000a40b03140c81c180d503050407c910901c040007090505400310b8030a445140e41d002080601038895080a030000e18210402620034078070801111000304050b401203018159541003802e0031020402198550745c4100302e034140c40300c1c00300302c15a00170013552441100310344000000c0c4190700c0d019007040c012040c0c080d401481e103500801d00480c00070920408912400d114411001c0f980104482820304503061130020b0b41d580040b0002600c141c03c01020782f00d6010012034110744440701e2506880040b180c01350f403580310208004580d03904014501400740d1600207589440c0088500a480780306084113440c08003490740c045100c2001c20804810f858140803070a907121525800c024056078451251041c00c0e60802c1e0f4001d4215490448a5440e82c0d0102e002e00014078000d00c0584098124a0f4199030100908400401684580c91a10005048541551f5040b41c4040000d0000c030500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 439718345 1250 439717095 439717099
    0x14040902070b0f061f050a030e0106060e03152a0705030307111908271002030a0906020105090a0b0426091c020a060311040f0f24120c1407050f0c 64
    0x90080300d6000176810700e46040c022480c2c509141d81710350b00d01040d0301500318072940c0c00456180200c00244254880310440c80c0e03407001c6058545016810746440d40500e03050300d003035107440c0c04600401c0c1401c0318002d0140c6840042e031009130400c0c0c46520380c0340c117640080741c01002040d04800304000311003003800500c08411090340700c007810081548401c6c00d10b000e248400b901007112030b000030b8100082400c41d0040120f000308032110f801c10444009413a034200f481c88101103603074101c0110340c0b5801030060030f105c3c07958040140f4009a40c0c0c0c4542c4a0300e44042c106464656410781d07031240340d51203011254015981417640c0c959841e50341e002d002480028914081c0203201d060708031801a0340380740c9200d00f111000e14010800c01d01e4401920124821a40042202480c0450000d0301d844c60b010b800c2c0c01c941c0d24221000b01c04602e0003036103800081c110290341c001a08044a00f8248000364014400181e41c2d242c032184000754141d5102195003c62415540d030f50003405626480740c0100b02d00c285c40001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439719595 1250 439718345 439718359
    0x110102120a0b0a0306020711090906070e040c050d0f0603170f03011203020106080a0506010306051003020d140c10050c0105071b080918040303150608070f14040902070b0f06 76
    0x40840c950518000141c071941c840c9407200107580a507a10080141c002d160810003c6640f40f07101d1412018000903600c1c1c0600990b051000240d0181011a42600c00d41140c2c892048800d0740004010040201c2240c44040c48030600621819170002d04c80e02c44000c03c5200005450f90941c10040d03000074a500c03444002d0700040050010345103c84013582d044482c20010405180c0316841c05a000d081c240e04098030500c200c0908101703104000a13030a04890045400b000340e9218202c800003501440c3c000a504950b8401d03004000070b588492a03141e0105a41c280c90100045400160360782c100c502c0120b00041010841c10101c40c03003841203503044605410a822002d0920006584140c071407240034104071000310703040b03c00362030340008484d01d06002140a442e901e000d18000d0000c00c82001480c60651001001003115802160f4131405951151541c3c03212040c1d040e4200c0f08045841c694100543d418000001c0009880c0003806506224418050072490b24a10000054400406051040704 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439720845 1250 439719595 439719607
    0x803070305011a220801020313110906091303212304020a0e0c090a0e0108011a0105091002120c0f1c05040e0a0b0915010e030105060f061605060c0703110102 69
    0x401d9004581301e030a00c544c00080ca00c604e07810100f2140200d43d200c020300c2d500000820429440890040500318854010070f48502d00c0301040c80031507007089071383c6604004448013060400c0c5505114102041c440d203001030341150b000045080040303900d00a82106511000b1511b41401c204d1458941c149240f411545649080d40000f110714021b80f08034405040c0d541c0c0454803d2102004581c0000e002a10304149182d1350401900c0d00a800d02c5020015460950100210f00e21180c01c1c100f4903005039101e50408000e0410841e60300c0c45d01308043c082d03100b0500d41074886518880544042c500c003401621070a1a60b0428030306060f8510660740c00e100d03240d440a204603800109071410f4a012640084540c4d03503581506000f401c880301040d070301500e00402c0008400e1488c8099100081c00c2c1da908146071908800d00d420b0f16001d07902660701040a011408190412002401e42552416419040e4405a890312410078900790341c14103e0020000c0c0c01c4e000c0c103030803aa82d002c40c402c0e10802149410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439722095 1250 439720845 439720889
    0x7030b0601021b090a090302030c0a0309030605010509070c060b040612050109111002070905180a24021e070204090f05060403020c0a1d04030e03120318060103120503060a0e04080307030501 83
    0xc80c000e210417412a13540a4940c103141c400c0040d00e00b80e40c00c5400726100107000d818003070320b003c1d00c0c0c0c8811038007a410240045042e04010640310b020f0078268480c80010503c568442d00a4000c00080703c0d003199031000001401410100c6010780e290040e00001800f07503547c00c0c2107e100d001c0c80c3ca03541c010880384818400c0b42e9030014a01c801c03207808407800203964481c00e948010080007150300550601c84c0c0e190042c14040c081d1200000d0f0049262621115240384170804142c3c040d40c2a0b031140741c3d803c07924014481c1000001040f0141c401080080c11600d55519021100007446081d1640e9020382c0c2080205a01003101e00301e000001c44421011a2604408140140b4981003040208801a012404060043c441c11800b42d03001000c1c0c030040307548001d0700102500122580d000340802c0500c407216101c0f0100c0d155058a0f00002440f201600008082d55a507002410f0310f034001040d1000050200b2141c04981d010718850790400e641ca003411200101039034810380043c411a001c4441c040821 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439723345 1250 439722095 439722109
    0x60609060f15121404031e03060602030d05100f030b0412030b0f010c03020a2306010f0302101d060f0c061e070c14010509010b130c12020f0c07030b0601021b 69
    0x18186494000f44001c814012032001e041c05103106102d024400042c44205a04a00080c3c50985440c030342d10b0b10103400b0f041c1201603400d2031140c0c001517001082031000d80c42a0307402c0180c0c000003090440c10796980c0d6410502c40258140d206944241940b818441000048014890345155602d400d00190760302000050055405400321410300c10a0170f0300604050080c0441c40c40e903900109100062628100901003803100c41c001807017180512000400d50311000348009066030b03006843e030110501f08980580347c203840d840e842c428100380c0b03075a180c01c2560b811005040401d50800f59549030303100181c01c540b4004000d403804804103a08245200000d107402c0300558441010302e0120b40c01512800c0000041c00c502c118100194201410060540707015005615500c2054444900d400039400007a070445011030205e40024031805241030a41e140c41d005410749004110000c0e01d881c50005c1460b207885065801101c00c0d00c42c80040043c150703014800d6814019840d0300720702984011200144034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439724595 1250 439723345 439723379
    0x3030209091b1602040f240602030705060103030e1906020c09070e0f040f0e030309011b050c07050904020a1512230f0a0b100c0b10050d0611090d060609060f 69
    0x5501c03141c0c4a40f000f50768464000f4080c003075500000300024003104c0d070408604031081041025414101d5030005049100100f19265241c21401505040e4255a4111000040303a440b540e0300051110001c0c1c1004008000000100100d400070308aa804440620a06080c0141040f080c017158114030440d5072100c42c00c84002800c11640003410014400c458070040040d4441c2441a1001200700103d5050550250f0000d42c540d800528521940c0001111688940e5250400e1a000b51100b0013150400c80e050f6504184018a060003554403905442d100100c20940c1c03034002401403001000c445030314440c007000c50b021140302c403181d4003c105001c0006240034002d007540102c1000014800300050744042c00441000b04140c0550031078410082901078066030070f42d0f000c00b045000c1100484018204404c132032001d0001c40c002c0c586d03500c0d088010300258840344200c6c1010403941d100b036601d40c103022803118800c440010721981005452421a41160000752231018050b40502c00e12017020100380d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439725845 1250 439724595 439724617
    0x114060609183d05040b030a0b190c031509022b0f14011a040f1202030f01020c16080102030f01030215070f0b0601030b0a0308030711071203030209091b 67
    0x11a501d48000105082c8094040e0304660205003a25020000c0150f450b82c40800021100107141a115401c000c2183c0881c070308254146c5c0902c0c0d00c4000580b440b01442d5118070440b0200220341d090401d1002940c05107c50507000a07a00e4070140b003200300c103a00031005481115411828003510b443c131b45c0c60200d100c6158984401c081004001c50700480c2d0800048034903c8031060040325003500c68982c07101400c1c055103103109000a80c40d036161540800369000c499111240c0541c0c1854040300c0c690500e00c01d88240d0701405124043c1210403003d0009005100c0e00c2c0000744070307000f020003001c5c6009515810031503203a4010002d011101d8403040030281983c0d0103c6895600c04140da112402612036140700403c1a0707243d140c00021700208122042c031418080e01c090000851032010040b2903400c0740001130040000f032002c02e42c1e180c440c80315a8a61001c5000700c99072a84c480110402841240c0e1084000980020750310800c3e050009006810600f08a00304101d1a1021700300a10340c010f21907510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439727095 1250 439725845 439725889
    0x7110a0b27030319110a020a030f0809070b07140f0601050a080111030a111e070201112d1005011707170d1b0602030703060305011104120206031509090114060609 71
    0xd132002c07982c0080206149500b40d190b4494807910041c0d220144e04005801158650340007a080d13500035030352148550810009030544074100742203e001504481c100396140d43c1401c01804651034200310141d1180c03d01802007083e50300d00341c10404c00706c81641110034141d0414648a0948800c0001d4903088410003601103030704207140d040c3e11500d0080b14000c420418005e900341c490181d0750340080480d01c0c002e80e500c522240440d035120b44c2c0c8003003243c103808212105640d01c003a00302180e0340740591080c0341410344850417152003400301a80c400381c1154802207008100b131242c580041103d10000c01000e280158441c098040380c98603400000d1401c000e0044c045030303501083c44606440212540e00c49002c5460b42404500180200154003044403030350302e407036480c1608000c0002a50b0446040c42d0308603040180c640d091103810b4001826116844040350000c0e880b55903942c040b2845141403000026100302d02d43c2c0700302030078400900140d0007503000f008031503400d8542150700034046152400704 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439728345 1250 439727095 439727131
    0x90d050c120d09032d0b06031603120305060a0f0306020301090f0b1e0105070b0f0411010315050f0d020303041706160e010c0c05100909051005090103020907110a0b270303 75
    0x1c40031148407001603000030600305c800400003144035450107540141e0842d03480c0b038542070a06a0041c0c190101078040070b03c060054100903c2600040d6204002801042c071090b55004d01d41441e0030b45d504115042900480140b02503021403181c1d01c010f5420b031405109026441c0003290607440c118181c0c1821000d140c404100590054046035a8a58007041d205440d18004001e40b21000040d0b1b01100c840f084204011081d600c00d025001101e03a0300401d001186291000b000a00f825098a440d004030303100100c0b002680d000d10250000385248001c0e6561003030f03103c80090800c0b01c000d1421220b10103504c1c03041d444590005d50b50094407000e084c1200020090b041c4105443c2540d0301c00350340404182c00360141254400880800c44581038403d002c03545070744007180c0030b19917075001d00d076000801600100050300d800030000d900b140140c02c284003550b40c103103801410400740440c1030340c020340c40f1414803034040d43c50400000c02c1c00303100400c00207071034000150940f02e102c05050314022003414004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439729595 1250 439728345 439728383
    0x90c0e13110f070f021e010e0111070b09150c0717120301051c2001020d1b0305130f06030516110a080a0e120f0105010b040b0f0a05090d050c120d0903 66
    0x6105040381c2c0042c05c09485050840d0480303140506071b46158006111440d40f05015402815050034121500f400351803814100a070700700250b006903004643c429450021040b016103014020003190078058043c055032401e20f1104100594031f018045400d600a10004902d00043c1041d80e040d504100c40315103c003c240801204040007541000d0080f104000e08506406900c40911000f81000e800355498a84105410386158413252960b118084020f00c810340000e101c0c600034090301106000102855480b00404110b001454000d0400b007a510014030084a110101c41d0302090600d103480407407100c2c5107042e1a00c1d81e40c2c00400424410021070b407550b865010391400c0c1d05030007024011740020040344100f9942e030301345211100a40e5191000204850f0304640c00c590075a001d41e9002d528040042d04440560707408144500208942480b80c1c2a2079901c9141180c5c2e030343e02960003401988802010040c100900e541c40810741c0d401001c0407036002d0b400001e00004c80340c108906009205080035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439730845 1250 439729595 439729613
    0x106110705100314131b03020904020607020d1b050301060b0c03120a0b03010c02030d0b010e031f02090d060b1002010c0e1e030f0d090b070f110406090c0e13110f07 72
    0x4c0c2c401e260000c2c0c070030080d00101c1d038140c0c1e95410340166405035032801110365242040b602e034000a900321080304000b4000d030400c1001003603400d201409100c0407680d0760b141c440000006e4070b0078a50740390b00b010003001145003d0140001400342202c20514000901d4150b0b5960b10031080d010481640d81c50004a604000d0b03480b0403100030000d802032101d891881d00003520782e03110031041902c052600011007495441140c9483c0ea1003000b6008040e2049684103108101c039001e814030b50055000c0007000510b407241c0002002151041d6030120351600f0f640c040100610000c8940301c11a850000601c0c3c145920041c40c0713000381d0040d1550b521410311070030445503201b80c02c0c1c14960148164805030140c8000003a0f0b0f20017480aa6681d020080c2c0c81e0303040d043d55845100d40281015a40d03021900101d00f41405080d038410006100080d41c50303940b000c100641e0840725440f00803800d4007400b035001d0704040c012003280346000c1008214900c0e84600d908024000d03c0910a401080445c8c000c0810900304 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439732095 1250 439730845 439730861
    0x303021510092c03040905011d070c1e030f0816081506040b0a05070c08190308130b10150e060a111504050303041502161214190801061107051003 64
    0x11507120210800500c10543d20385c03080c8034403190b541c5000000030b8248130300b16150801001e080541c5089441e1180201d600c5548c600050b64000c40006c160784201007944416652640310f80ca030407080742d00180f03020300b450100422001101e800491440056980904081ea20114926911804a03d0309001c00d03414062900101001240000c1c1d0940ba40d400401a018a910500c507c0e404181c4540e1402d032288403900c7d0340804011800c08950009004480d4150310400c1d50b003184c88841407903101d43e0a110001c0d82c10001c12001e400f0f050240711a0041050161081c504149040340748480120fa03003807289404032402c205100703207043c008070341c14084401030301c52160031070885042a0428507101d034800c3c0e6045446610000c40f001440209000340c07900503e180760602441ca166071120b011419510130307510100a0503862001200551002078400701c0000d980c28102018000390241c01100182c0180d000c1c0300e0851a81207c0503400120103050300c4007901c010682040030841900600301d98 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439733345 1250 439732095 439732151
    0x109030311152a0403080301030b0414031b0f0c0a0e090f0313050f010e010507060c050405041418060603120906090a080a0c05190317070602070c030302151009 70
    0x1c81401100408001200718907050f00400100960941022440764031035440b0003002e0040600040005c203164008a507030240c0203044807020845174030300b080d043d507009124941b40801e181c0ba0000b00440204481d110a070540401004a04815030008a641a503031181062020078800040c00014041c4a412a030030911030440e500c800482503001c3c404a020300510f0701a103128032900c081c4d0343c414144038207204410784405103021402d448510103031001241c02e00901c001048001103a40300c42c4111030207001c5065a2040320700700441c5841018691809c070043e254071180921942e5980403a050149103441a40b0a41d10f21202c0e0203e002e901900640c16804211700c5400110101c01007062a291407048075503010160710307001001400310041500c1c02d0327108800001840042d46000b01d4201100034202303c513080c402d00346c1d1054161b81c0606012100080702040801c101501005800380d001c0030f41c0075002407840c1001009040d01020b229280d4001d4480c51441108541e07095205e200302c1e04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439734595 1250 439733345 439733383
    0x1f08190f0f080d050a061a090109051c0c050f03030f0318030a0306080c091015050403290f13030f0c020406090b1e0a0501030c090915060e0f0109030311 67
    0x1d40c100095a07801030140c100d4100d040000050001e0583d01c03500095031403404195007200441c14040c41c3c0303508028142c3c1d061004120004c220365070340c80c1c10801e03240e8040651422424152924813002003441d4412401100303161544491503a012064900101c0b03034000c181d840b0396680141401c0c004410b070081156000c0000c070041416410b4100000344c880000895404039030390024813090340f01c203c824220f03240d000c204c01d0015103541140302d070901c031036440d0090038144c0702d844400e44401c070340c09650203140440b020700c04850691810b060307109004545401007440c14001c910101c0041080003400c0012011b40f61801351f0048034400e401350b03005030080044039102d04185000745101c81c95507120307510300d02003122484c1209907045400000035002214203498003005401034501c151000c41031101310b601c0856040e681d840743c41100030b030b03683d50140c80c05e24016000e00010f2203608618041da00b140d41125903a41c00a8072402100d40c14503044d902640d01d003c40504000b030114010040d542 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439735845 1250 439734595 439734623
    0x3070203060714160b06042703180504020c010e06060307030c12080d091104110c030d0e120c070e0c070b06120118061a030a0b07080703060902030108061f08190f 71
    0x143c030074220b06c201e00548040041a0000c0c03103030084030103172142444498a4100f030720400244904a02d6002c4e40340304a03182034464481c40017400341c0c0c000ba6002e49160390740c0e112440181000701f00c0b8a800100030750181000c0750468803001d80009150160b281c2040c01c02590104010071442140e070b00981000b420000d0300c0440c94034002e1b00740090421032045003049452003c0c0180e42c002c503035440700540e00031481c0844140f0341801904404017200c09500903043c40c00720251015001340070307908030342d80500461801d2102560200001604083e0f04040520000e00064140d0541035003205084400f4000b0203040020240036010b1060880a0f00421401c618104540e41d0000c65185401a503030b541105008824103541c0c86101c840602120181c0021403441401003190355088007241c9004100c15484004440690b8000e901408540e07008404001400214041d40f440100345601c903d50980d20781644c041c4d486002e44000d01c400d20f40d00c000903040112403038044030115808564040c001c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439737095 1250 439735845 439735853
    0x50415030e0709050601210902030307080c0610120b15120a020405180712031103041d130302100b0d0605010b04051005031b030721020414030307020306071416 70
    0x1c40907032071880031803103880c90102c1c00c070038903002c0c0920801061f5030760684068039980106001c412220014501e41d60303181c0d043e015842c10b100420b07802d400303000394598603e41d45c2241450703c44014803090700c01d00c94038010700004045440c80180560444120714054582200d16040b5181d0740d4409a40040f0221001c1d46040d008152016403c3c0221404c000c40e50ba00741241d403048402d015400c0654019807000d1000c503140c801340b507010a01900d010391901208800c40c900c1c60340142c00c80c1c0701c1c43d80700303111060759600048240da51000312a201480640125540a5910900c0381842c1d6801078548658011507250843c040341601d810a00c24440c0b56940c03000d00041e40e01c98090f50b0301070a40340f0510380701c10340580d0440780100c410404044000713100b440c4041039a003000d05990200130310030030799a4490000c0381c1d60310072803146940b0042c0d4913450411100a16807803011180c0c0650420311448001d0b0b03801292080c1d10110a0606100f2124454443d00440c840c0c101c10180c4501d408403400300740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439738345 1250 439737095 439737101
    0x8160c05100e160e040809100203040902030f0a11070f111302160309170304050f040f02120613140a020c0c060c0d1205060d02040b0105040f030b0f0109050105091605041503 76
    0xc501c06143c01003c907510b03200d1314050500211409440c0400403c991030303590030b00c1246038590f101c09105a90801c2c1d04c4150b120140d034020340e58001141c1140040c03208084c414821906091000700711a4a00390442d503d1181c00d4020042c09041003400c240c034503281ea12099418041586521411550781d8001a04208a155044010740014400800c041030a0991440741143e030002c0754000c1d41828900300404c24103003c0401100e410540b5940010304c460a107001a21440c41c1702c0740f001800703107006e000707100a22200700354102e05103040202c4038000c4000b42e100540c0208440b0009660344078000185880c1c050707030460031900000c0004034020400d001041c0405031810ba50b0f07030000e600780300c81c0d07000080c1c89081c1c80355076004a64240a6006161035403050841d020181821828160380f50707035000d41c0605590080da03555102c1d108100c560709424007440c0c00741c0f0405400300b01550400c1d01041040000815860f20018801d9140410300c0c00f80041d50000c00d0220041c01c18600700350001806 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439739595 1250 439738345 439738363
    0x24080303100807050307090b040207080313150c0c030c23070f06050f0306091e010803040303030f0e0a021c06060b0703021e0c0105090a0306060605070209010608160c05100e 76
    0xa070090035402040040000c109441203401c002c00074808181410094001000c16441c026802582000400001801c20b0060340c0329840303146540c00c5541080c140052080800c010690406141145003440180c00110900e01030b41c040c54004901c9101c5e1400d42c101e044e0805540300c0ca0344001003414a140c40000e040e00560303184c40642c010301640d0f808180d545004603103494250321014400190f56041503a40541c2c40030312503d20384411683c03442030003840c003007e8022407500d4000150030b2040c0743d058015400358205400c0304218030070351000e14948030700f41080001e11500134140040361240003094101e1003d604000f042100a541c1c1500300019845203c0c12405405100506074060f100003421130520400403004c1c042c20034400b80112119444407030703c03503441301c860400480428503520404000c1c1156440303940da503035401c1c01000125001640410100400841004000d28210203a80c1882520b400c105403000030302d151460504d0070501c4483c0043d86000c204030150703440081d074400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439740845 1250 439739595 439739611
    0xd020304030f0206010321020c100f0e06043519020a27020322061d031e070206070b130c090b010212180306040303051509160324080303 60
    0x4680a00d000c040c3c0c3c44044c24400640f4940c054040941c0316154070407001d0301d0300980c1c13050b00c032a400d031803002a141c05021012032000911000740520680d40100860480c3ca804a4002e41014507058003a10b1000d01846c50701000b4001c640c00ca4808034050303a192803003c00c9078041d1402c9200c450b00e12106240c07840810307441441d26204c0007031005030350b1104403031400d100944a89080e8481c00c401d400b07540302030003140d54001a4961402d80803e80c501000d2604c1c414080440c610803082000b03083c04452000380a1340e81c008100003101e22280d01000c00c0038210800c9c549440720720500010342030b40100c2034003404400d10302c4c04011400d42c906403248085842a0351603072810f0f460701801340840e10151040ea000da8480c0c0d40b00a03524040e80007422540300040d888500440a07400400d040c040c6c01c0e60110301007612103081c4a0b00500585c0c40c91002602510305075082c0c0742c25081030030f41c2e009040c001814150344100d04008245590f0800c41c2c0820034442400850341d992094540c0c070741c41164801c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439742095 1250 439740845 439740857
    0x1303060b100804050307170c0304060314061f2708010c11011a09062403040c090903091404090602030106020c040f090b0117030d06031a060108041e06020c030d02030403 74
    0xc240700d0148450038080c1342c00c0302c010f50605550741e4440e018845141001170030307104140301344540201c04100a0000d441c003580d0105048039042c00741c003d2100068401c611440003144e00010100803400c191100c5005403074141201d0100640515200700c0e90341040c1c031511051000800d03035180540003514034115a43d1006070351000d004142d0b088511590070b1950183c070749107417020700e86848604150000c000524620000083c81d82541517800251180d0b100451302004100a014100400310001c3c480c9040034000f00f02c890b54020480300081c041c0f002c640704106054205502d45910005c1050751015046542e0b584400029685030010244a8415400d00340c910358002220302407200c445038450b1201c80035074200a04103101302d07080325455905200c2440f0140345600103010310001180180362800c9000b441c0c2e4948580310000409180c1030000c60b0040c080001d001020f0f001c0c0f060061400b02603407002625140d0041e228804456420748404035003200d030750707840d640190702440c4261206 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439743345 1250 439742095 439742119
    0x512060108011503091b061e050415030911150405120c0a09050c070512120f150411040306050a0b1801030308060d110603040c031e020a1a1303060b 65
    0x112140042401022441c003043d2161861842c0203030401c0c200d051003007020b40a0146044620b0030071070007552045000500c036190304492915040c4130f444602d070344c51030104d1406080590641140a28482c1d400070103649410710000d010402c1101e1080d00c4c1c0090110205035003040c2d100c4601d4010380642d03807107110f1000c00c241c0411000645860740000141c9255280f40c80d150f02c43c0020003000b090088000c0041018000040041c020412041103114000f0b0b141c2241c03524220141200400070391114158400388401d00c16042800400300608079800725102c0a0342078201094002d076440200b840703050000f40310200b0702e150403880741e25070300340e40c80c514140740e00da82113425140a102c081c000c03542d0040410150704205000c3d104030ae001d199039811000e01c0d000403c000d43d104544c240e07500910048180208400d108003140d8401880b40d0710311541055400040c00f5545502c5a96240700c3c03011004220403200b1420350310007418404215024580e02d0420502410503013540c1071066441c6044 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439744595 1250 439743345 439743347
    0x1b12090706030f0c210b030609010906050a0b030604110a17010f110901080f09010207080c0f0714030c010c06060504180b0603150a05090f0f01060f21030503190c05120601 75
    0x5030703850000b0b5541c2d142d0342900034941d0303140305c40c005141003d0041c1c4c0380d429404060306c00b040207a01800c0c615000240c4000603080c003104842018003224401400c2c4601800ba41c0c0d0b000031481e0300b16421811030382ca0180401c00042c1000c4a56101030b0310700090101020698106600a200d94405441c003400400d6170341c1c0c0300198620443c83c01c0e50204100744003040c0d07400700c1901081c0c2d012400c0c4000500d02074858840c08860b0b00010300f03120391544045991524103405120080c002c2001c0f040c41c01c000e1089100280d120522100014108103d1018141c00d00050390480001068060403c11101140e1030440d401c1e1408030724162001409070340425400e00b0001207045000888000143c1c0300d4840d510750f2000740801802000162003100c440d42e0449038148900c414818280b00000723403c40c504039804442e010554404120300901000009100805410710250b141e85490b00555a40d1410b0220810841084411700e14038508240413414540180c01041032a0760181d140c0301c1b907628500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439745845 1250 439744595 439744601
    0x2130921020f071508091212010302010e04050709050402071e030c0b0f070e040b03031e190203120624040305030a141629040602090a1205061b12090706030f 69
    0x4a03041d103045403d07201c01a040c5c8030f8141250450609402d6500810400445078261741116000f03e09541004004100b15a0002507810708000f09481c00d1040c1d160101010f01066200d1040500442d000100708080001100d8180d45001e0307505540280403000d0704000703208401d035600440d10b4080040200d440c41d0307800080140b18a44666072880700300040824031010305a40d8840d942c02d40310903c4100d452405860800a2690301c40da44030b5158004e00344900d0b01c0351010854001590810000b4500200e20710840642c804010348400000d86111104907400488034814011441c3e0701080110400038040001c14191110b0343c0c9401c240860a05c50010074072525102c0f0240340b54192000000800e6002c00c1081c6561120807581c1802030104c000c05050001c41341152025030000b00406646814034421b006004a5a0142c044030307a1a0755030f0b42d0315140541030b82081c2c0701da1014184800029001c49207500c88020368105581814a010341d6030b1038140c001c500c0420300303090710340d07666441c00e03c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439747095 1250 439745845 439745849
    0x16061112060d0305040e0a0c0f0302070c030b090718020a02010515010c022206062706170c0d1404050c27060a09060f0303030f14010302130921020f07 66
    0x10140d1201d480d000200161203200c448101c00703015080c44001524035510000900c22070024a0101759220402d100418000d4041807000615206201d02c501244030a0800019258000003400190b2140d100342490035040e940185041703107000b800140743d603802e90050890480250000d21641d120311300c4082c1401018060280024000350050700940340800610070300443c0100000800c0c0d070f41c852014251000c0b5002803000c28002c502c18a07400300d00c0b280380c64502c0031001c40d80143c11b0034404018507030110350803411003140858000c02c1400c050301c011202c0700d2045134800c01c003000c0544854220140110f030240c9090107441e00300300c0107050000c2280755000c00c40b1502d030201c40c0720345407034440c80300041c25280d08110948004100801544905405041c500488599407880c625008003590452881410303842c0c140a0603034440d4800214282c1942e904841110743c0c0c0354924541c0c001481c84034409001c1d08008000c9504010001e4923042026615501756800030780d04103606652000c140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439748201 1106 439747095 439747117
    0x70309050f0a020a08060601050901050a030b03070f030b100513020703020109140312090106050607020108090a060510060e03060c0417150106030606030b0118061211160611 76
    0xd0700044c008148030002040d0620700000001c00301c7c0140c0380303514140b050100e4040003c0380260403812250798060708980d2902c3d9600030500380d140d8103100a41d20750000c080403400f071212405001007518405881541c0c0d080524160f080294030082d0254119541c4451002c00140d0384030340501c003805408000d5032908905801d10701c0c5120042c20700c402d42c2c1c2c50710394200100e40b00d01c41a0352942d40c09080032081d540e500f2440a04014075414020081e62519082100000d1489002029140259a90300fa5908100140b560781c88069800c9144a5014042041101c0b41c0103000b04000070b88400f50b441c2410909107010301c03600d081c0c020002090711a0004e1020030340c0340c4038120b000d403000d180c816152000307070f01c1002640115000c0c21080044890242c08180752a42003c3c004120043e082e603590382d1814040c108a9561940880303e050400113212110840c0342c1c15030300c01c00c0c0c0d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 439568345 439748201 := by
  have h0 := BRFrame.cov_init 439568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439568345 ≤ n) (h2 : n < 439748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
