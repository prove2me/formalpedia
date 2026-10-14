-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:22:23.78027+00:00
-- url     : https://prove2.me/submissions/6da18473-fe17-4626-90db-4bdb64dab284

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 97841726 ≤ n < 98021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 97842976 1250 97841726 97841729
    0x405091c0e010c02010509030c0312040801060e1605030a060503030403030804050c04061a16060e010207050d0302070b07080c0c0708060702070501021902210109060f05092b0908060a06030c 83
    0xa10340320101d69105400640001d9a00394003904020000c0380c40900394034200511400c18070300404a506180901c1c0b00c0e4074082d401401600e00c5542403c600040c1040621811402019107102d100310740002104200c0e8150802080310240036111880001c15840500081c4040d50103039032084070f11715150800301c0c0380200021806000380d181800c1008a00340054a0080d0006800d40003540d50308030131f021440031581e071003010704a130349040131140d4dc029055005008507803140c2c0c1543c3d03003000c5940c1d05038124000c251015111003c3c050000e24120300c43d040242c2c0c0104040381d40303424504080143d502d0142c464010003602d43c0070409000303500d601040311800030032003407004142c103490101b051411004142e0000740980360301d09680386c0f90410300303d04480c1b0140000080090940c40d0800801500002e00010307503562a000106044520114403010034003c1d2142450b10342195914001c44004044200010011900300c04560480244250f6002c0c01b83c040021540c6401d40c1840d00284003a03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 97844226 1250 97842976 97843033
    0xc060507020d020c040515150409060e010b03040b1308162d0818030d0309060c03051303110c12070e0a020a2703060204030b0f010f06021002031005040509 68
    0x30303400300b09a569001070032980c8840265000714490303d40c1d001688032882c00c4070440d5403280341400c00090001540014008a604142c0c05000e115512003104440c09028003441140751420400140426021031845400504106000300906aa5104d14074103401c034000f1580100c0d4881d98050910280100010032403010110360310060785460300c41c50341285c1c9001c0c010613100011a1181a05800c0d000c0300101c014040c0c191030740d81d032607600d0040003002d00070011503140e46000c1c41003d440d48280300c2c0610608040340c40e501d8000c1035031400d031000300c415000950148244008602551a021040408201c0c0f400c0103103125400c1001c990078040c2c00408030804144140040540507500003d82c6014965416000005940c4040817103020a01c9070800303030841c0c0c000a0700100b001300c4a0030952049100d04d03a140302503621403100c3c1d501d412040c4035080044c0d010030280580140654000e42d0412038019640780c0ea26511000701d0203640007120b481e071042d000143c00300e2422102d030b214031001000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 97845476 1250 97844226 97844233
    0x6020706060e150103091109130b0708070903150603021903030908061e10030c1d090705060a050a050c070e06032416020a1704081501150305041e030c06050702 70
    0x6000f0751800701111294180d41c10542c85d0550103040c0880f01003694409034000d13060001514060b5010502031080030011a070030314403400040c43c09841480200d00483c0e0719552103d00d140345486420886e4424114240019596040000141c1c0d807101d0f22174a410030712440700d240c9451806c0c003030a0b03401c1c01d0307018040359040030080004a014280a402040709520341840c4c0a45800303034420034000842e0402465a608803201081007240401342c0441303c4000300d03550099a8401a440d078850308540301c1c482d004001400034513420360180d406001480380502c0e1981c00c256060490a20300603080e803192106240c07110070320019003820b0040c001043c0440c4c10246000c2c0c0001403028072030380c00610007414044112310080c1182d1081c80f1484046411100e448030110360051140115441403160b5103041c4510600c000d803001c5413a42242c100c032a03901c42155855406142900a0040203000710341c82044043c0000d42c010700303100400e036507034002d0740c40300c178800e0851030840100c8101071305078000e551 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 97846726 1250 97845476 97845481
    0xe0610171204030b0910020a090f05010f022a0301020f03060a12050703020126070228030801180b120d0e060301180f0e07030b1609060519050904020706020706060e 72
    0x100401d040b50216a841000302d51640d0f0307802c3d05c5508104c0c0c2c540410035030600010300d84481c41e40c420794042c1a5125040030740c0d403840c1e898005480c2060b00e810a01c0140e041080e0b94030b41060044241240741e0b82400301101140b070f42200090881e801144400c0030000c010061100071305001c82d00001510220690070709122040d16000e5403810a44402410007000002a90b0020201048914001100f541c1109641410100a51120521004030b0070121000f210171840840041c0904611034041d00c44a6181e420601e050b040c110014048461180d251202040706441d008200400154100080e104120038454000e100f0520030000342d22510080c00140200e410031508603009050866002460600d08000c18024120504503c0c0c503e0041460000900c040380020030707c50440548051103d848007403055903080e145008260004401f03021414162091410b40358191515050880c10010140d0004050741e22403d8110f4006070046090400c0120328080d1001070408100ea6480c2071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 97847976 1250 97846726 97846753
    0xe040c0b0405061207021203090102031506091809030f12010602061509060d020d150902010e0306150d080d110702100201050403020c0123030a0b032103011502010e061017 75
    0x1d002d0701c900300c485400c0c04d5001c180300341c0c0204020207440294510240d1245484404107000750012a2030000440c10507910090618095041b10030030000101a00c240402944588510032001841d283e56440208509803000c198074000d0030800002c145031400031340c10810002d0a004c4050142880d000020310f6108041e0b441607180d560000c41941c40007082e003080c0c000281500111180603000030302c00c6800da0003c11082c0c214064050003170300c60008030b010b0001071550b40c5008907080719070303840c09018552840c502407000c2905940034040c1c0302d05200300a48a00120f0b155820380d1070311003e0008008003181061284043c64808600003002285007503100070f5150310300019840d0411100c0040f00004500030203144c4000c00184001584034649810310b0320051880700380315031107449244801c0b11003060440342c1c2d101d494100507c0900396440c08107102c500c202c20040000c1555240d00c0c04e18440081040140e214800100d411460305261800700c090f08110310a4205454000030311400b010b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 97849226 1250 97847976 97847989
    0x705120306150a0531060c0503070f0807050f0a1202010e1b0111010905010515091005010c02010c02300c0307031403070b010f08060c030402010c03030f0b0303040e040c0b0405 77
    0x10300900702d50b001c0d070300d501000007110386201d1100c280d031a05801680098084017441c00c4280c8480d0580070301403e59171a524241c411002422006025a0041004100113000d60782c41d58401d51140d1442030a1004554403203080540c1c002c21350409500009242041c04403601409031102454002040b0034442d801405880e000400b041d0400604100c107820320907481030100e0b581511140b8001c00099600e03240480c060142900d03420100c00364011301c041d20b40b8200e0035450007612600d441e0f0786c6040c6884015a0000c4d0814030a0b41030010306201c2c00e0140c6c1b1124146d9072850804c104000c2a100c221404480c4418104402c0c002036114403100b40305030b1400581c5c202902d800c00341c000031002c40340d0941c40c614032912000500c145801000040c03c012000d2400050700d14a100340c1e040b503554408680160700040350081d000135210086800400d0090340040c020100b0340c100801d41c4401c5c4000329203507902c56841050f4030400e96042205001c00240b200020b000210f001d1880c1c54a0480010725 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 97850476 1250 97849226 97849249
    0x1407090e0a32060f060f030703030e0a0902032a1e1315111005040309030201050318030a0e041b0c0b0c090a090903110601050114070809150705120306 66
    0xd41094500d6100300300c810b031848100320710b1052000c00d0318404110880d2141d40642ea52003a083c13a0b0b002050f403034940b0031400e415808000c0c0040035140d203940c408032a40003c00400031740101c100e01c804075843c0c1590004500c031b0703030200c140072401448105520b074151050307181d40d529a2105118407082400e03596520002d280079018010340703400c105500e84040258662059a485081500c0341d00401e80103c6280818038070a03098031803814005413601c041d030300c00b182e0040c00110700328810320040d80038401030340e08210351511041d00620581117035031659000344000800318028241004162515000380e0401c104c914548410f64500004050114031480c1c40082c00d5150701d0001604d1040c1050903149140002008405c09603511508040203002014003500056272051030307500c07010390005d5000d0480c1ca06175101c40001ca0500a52102a04500004c452600c0100480846c80d902c24910450800554003010340ea00000d00e485480c01070717141c0105c00140400d004004031980c54000051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 97851726 1250 97850476 97850483
    0x8040507052404060305090601060311090909011404030201021b0f07050d03120501121401021303020f0102010e0102070605061009030510091e0c0e060109230f0d1407090e0a 76
    0x240d99415a1409040754540d08120007440100071500144d000e601da0015401010b103c0242c4500b640c85a04c200c1c00d0300c3c0d0020070340d82000e42c10010400503040c40c030300341e5900c14198400010000590a01083c0c044400d6506034010b139000300e03802444045041c1414030303a007c1301d801003c030400760341a810784030352481c070509100302c040110a40615000c1c0c4e240088a02d2061000c001d2980c4070f170203d03128002103e80c150741010180e900286280014821100c0040d00c03005180c00c00ba103140d00b041081da00b007a907060304554035000c146600000c00d001a188480c4921408241d5203014005d200429414054200c00c0101480e01000841c0c1c0101e02590b628501d41c40100302401c850400f00c003071017108030f60b801600800c0f410744d109102d00c51950304240c4044c0b9240f146551a20001101e4100082c023035848241c061211141841942e084078014a28000e84544400324031200003901c1c20f419850b055890401c8401d2580c000c56003840741e10003500081030104800703240090103d948030500d01008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 97852976 1250 97851726 97851739
    0x60604030b250306030c1206180f17090102061504021b032805030109020702040605090f100509071b050f01020a180603050f0105090702011d03040e0612030a14040321020c010804050705 81
    0x7d100b03020043e009a08030144503851000d0041070303441d0810b41c510815009964200b82c45d468a00003800c03030400c50b42c015070140d005010070740b5510445034090402240c155400f40c2e08001d1301001c0f03440e1440c80c0d0b414401c010080c0d170301e4091120003920114183d00c00d4082c004104012840041c0d00b02c03040d41e064985030040103031103140a07c046002401107401c80da40c0040f07214104448011a100700a104130070351a8000c3c42d50b076a4800b84a20800c0507610040032a00040e80050203000c0c0c059a46051070040e030440b91003940780b003c02800c983c0f20500301c10000d41401243d1406920803010b0760000c0c0b00e03918040219180464001c40b031403806028140c4201c1500e400310b4541c910075088000800c47e00c00105880201c10071110396294402d104801300c00d0300700340000c0c50510702686c4400c400c14110003e545040207080e02103070075100b01e0703040300c0351b1440612011000c90710303445200000701c01942464440b00340101006e0310300030250000c2d03410007074100b08100c001100840c5450403134000755903a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 97854226 1250 97852976 97853009
    0x7140907050f030c070b010308090418020609040b03071208030f010609180c050c011a040b01141204020a0305030703180b09100f021f1d1212060604030b250306030c 72
    0x25410b04d03119001c00605080071690011051092050060800392000c81d02041703150b44d88440084200c1c3c510b40040d50003c42407107400e002d410039400c8520b0f8000c005046d1414545c44801c4c2841640b88854191001000401004040603102481e1030140c940f90518901c1d00d4540b5100b29035000da082c940d0010f007034980720030f20070850156040d100c2d50f0a08a00901059000c2c042240c007042c08000601d2259044c000c02070752079401980c6500d021014801c0691070141c0c0284100c3c801c003405003049821150320750000003c1a0180042c0c05164400c0d0f0f0340b00c5044c0482491442036050642106443d0706041003500c40c03e68580c1d0401c01c03000e4207401d09030494110144160308102d9503403d404101c50601c142110203000c2a40101e80d02e002880440e5034441400442035503c0043c1314281c4a0094108007030100c0c41599002143e0003000100440d05c1c090f1207942d4442d81000540308075030390107a55414804880203890f1001480b00c05851b0030000c20f85152141c6012901a00c10031118042e034850 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 97855476 1250 97854226 97854241
    0x50f240702040204270b060a051602060c030304060213061b120306080d0903290f15130509010b030c0604031106040506040e0a0c2f0f0f07140907050f03 67
    0x1510024501480c07101c120704038900d4038800c0e0514105c1500c004a1404c415a8031518094066801480c066078031301d0300700001c072138819142142c4084166401101400403d107601030420046106900c601ca001d40c5849882909400078101d035000101131082040c00d0001c7c03d250750f0f2044401d40c3d0050700c1040c5c0c00c41c80e214298000c050542003c0d13079902503602146002500143d80070b044902c650800406c03007402241480039255405c501c5182c41241c40042100103a1410b2141c0c5c04c078100035020b0301144c81440001d841d0340340c00e4a0248070140ca800030040c1d011070a104070b2001c41c0c0c0a030060701400042d400002c4c02449907010080401441800c603842903180c003c00d49015040c060300069a07a074449242e038441100456981100d43c2c146803201c00890311842e00c1e01d41c3c0002d800d4090381e99160011040a003881103001034103080c0b02d1080050341d004030030003214215000f00800f410384241448511081c075254040354030300075407a00091003015907003d002c58101a04490380704d6287c2c0ca903041c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 97856726 1250 97855476 97855481
    0x10050f0304060603050f0f070f0b0a0c140a030e03190809010c05010e161503090c050114070c0b03070e0102010506090601030e030c1b010e040e0604020114091207050f24070204 77
    0x130009415486440d40f046199040050f2440110010714100d6034203e43d02c43c41c081d03101640340181841c0000500500a206008182c030102c10381c45442000f0984080c02080351800e0003913003083d80020800703c00b091aa060511850002e1800b46402c0400700c1426281c04001d4490724850030b04028444101e2020300500b0b500140d0408001400c0c0d40d5120001341000b01540d2546c02061030120310303181061404d44c020b100f900c4249620002c0300025078500001900c907400c0005420111341d5080040c2d20018206101100181c40d0340a40c050b04c0e802c11b824010511009801200e041d07a140100344503140e61819400750b48140c0910700416603285801d807c50940c007500d45001058403410b9022048148146030140d9094030a070703504c9408581880030001561036004415403103400c0344001c6405948552050303025046509a1203260101c0000842e2210030810b41741c02a1303400030f44051103030340f900d40e4131400d0700c440172520403480d1410107090048030b0401c00a00400d14400240c020115200c54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 97857976 1250 97856726 97856729
    0x20a0f03062102120313030821040b01060305100b07031d010201141521010203012102130c05090d0b10290a030908071202060907060504050f04060e19050610050f03040606 75
    0x80c400b144886584e4680585039401c60f00c0145148240039074400840210240014451504078101000c0c85c0d103045023b44c01002c0113000c00141009050010800140d03182c000e00c08030380701e0382d0b4072020040c0041e41800c9004041c845181164100750071002c4510400728590380000b0391b4000c010140c0003900c0001c0750440304071808810628140c080c4c04c040d907010340c0954101c40d116410900780d50110b2940d0300c0b00303116080c402944440500c9005d10341408c3c0307600c030b0380b0b422100d030030081d1510006000086800000b1442200c800003100c04000d01840b46294003801400102c2103040000303280502a50345100f40850b0200c0104e01040c101170303107031294010510703164000c511a41d847d0140e0904680a00e11608104c0c058404d42000c11141d18000038803204480c55a90b5090400d41404208100031320003240b001d41c400c0c0c441101055a1400711101c0340a07440394031014044211003050241030754401000240310303814110222403000d07000350071608200f41c40b80803261b80ea522447e1440017480c05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 97859226 1250 97857976 97857997
    0x141303051305040c1110050c1804060f0f14030105100608191d010c080601020d0f05090a0806090715020703020f011704080a0311090d02010806060d020a0f030621021203 74
    0x10104d00c0034a82e0380000720400341014a1050f1801c06003042e6401041c0c075000e0b0b5040c05121020403118510000400d50a00c1c085801000492050750300c0740151040304042c6c000318007513081d80d5020040c16256176220301c1e03120404d070000e008915000c0802c459030503e521401c0244811900000d44403034507a000c0c0343c0101c0c00704004000e100e01c20b00030200c0b0340c05060908034142d840e140200f030650740207140035403162034164018030f6081001d20003150f03225004603848040c04428000041c0c80c0c0e840c0c078110000380a60100a0040b03103880c6000d03c0c0b81c8103240d441103a005903804941e4510660100314002541c2c0c055440251040c00f60380100d6105c3c1605900102070385402d0b05100c10030800f24010501c0c1410b558080c01100c0840003a00070a10070f04a5860f4080d402ca41c01000550041182e243e001c0e6000308031b18240100503290400745e1380801e1444000941c00701c00c1084032a05031140d4805440803200c0b20003400740b071044040c4a20b12210010344075404411400d5100c1004000320b91040c400c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 97860476 1250 97859226 97859231
    0x80c060f0310080d170717010302060d0605090405030d23070f0c050a030c020108070327050f06130c090528060b0c0102030f0f0603060a050a06030605070804030314130305130504 78
    0xc801c000107000180c107001341100b41e80445e003c100340520414800205000400c002c5109900e19800c21086500c4140b1024620b5203898002855558040c9160300c91400382028564569244118808507040d03050102d0b0405c05040c0700400704c40c0600c1c40140d1207181c07401c020303512410402040e1501d8140c3c3d9001802c610980c59007004066000ea141101c1c94400c1c4c88a540a0301d4200b400e4084e41c0d5002e40b070002a5400c103c041070208600b0280400c110b00440594007042c9640b0251801c104080340c404090001c603081c05070400c80c0b03a403e80b00083c105540c08112a04203805500e6220040c1695204040b0418402c0d0582d01e4050740715038002e10b880e00e2000e540b40003d44030180030790000c4071220030007013140c0001010400b0480700d4605c18400240030b4066982d80c12541001800050300e60b022061f40c0d8040840050300620503a4003030341c410b03140c9070760520303051800806036000001c01c2c00342d0004120a1161002c5110303019515564141080d030344607130349042000705550040d48041e510a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 97861726 1250 97860476 97860493
    0xa0303050a0206070207120602031509012303030a050403110310050114040f0e030403030f030e0604140d020c0f010f02011112040c06050c0607120b0a03050f07080c060f031008 77
    0x6820034000c20500545400741d80541c0c0e82d850f4142c0e100d0f045841040111381507545c609001490701d900459110724610104606800184041546100241c2001066030030031000c44c10928004d001400848008400441c9405c40c40e00b03000f05a80200c1c0f00040102c440d03000c03ca06071707a8090041e1528410302c0b0741c0030841c944c4d541c0050342032003440d04941405503141443c600c41c002c3e600d0041c4030030300c0c0050000318580351075a07030102c0700d00d0303910b800c00d00030146c0d84c2a204144540501001c0d015500810341c60304409042c0e6003090a0403460b0f2000401d560001d82400380c00d88070041000d05068007401e1408200d12035500903802751122407903604101400051122024094070020741c0914010741107550095204c4005540c0e52162684070b0206909c002d0010740c80920070615607076030312800080421014100700c0800c00c0b01681d5001200e40b50800d10003505030304420003a0308000d00f8188010318900c001350700403501603c01d6a02822500000200040240c6008403000300103040c41401c0f00c0100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 97862976 1250 97861726 97861733
    0x30903100b010e01020303040f030f09080109120806012d020a0b100f0503030307090e0709030f03080604111606020702040608190b010617060f12160e0f040b0703020a020c0a03 77
    0x90005000703282c0418502c11401650b540700000792031099a00801400d550805503d065408291028405041026010b4041907a050030300811240900c03512000102ca4003803200030308a0040100f07030f9410030851141d0a030180000108503001c0030b030303400103018101e89100702c201c2c1888412900035110041c0c503c1031140740040d444100044405081c203000289484004042e00ca2000f42c0300c9400103140f5507414070100520400c800c0c1c010300581411080d0039503c0d960a0b0b1074250301e00d03098000c41d50070020004075040500603c001400021680b0380f400b031a0600c2c8011214550304040c00d40f0703602007410000c544440e803215000e009490201c03503410041d0000d80d10038913000c050480b0f0f81039075000001421805140f0711a000c8503020700381c0410395076581c10b00c4401c0007403003035440e40b0200403119000c0d1454280700c0e088030400d0006d001c09803035007808a04085000d01504500800c402e0300204030202d5101603059400c0109480d026035944003546040380b4000c142e0304030940c002034000000080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 97864226 1250 97862976 97862981
    0x80604061e090c0c12111608010212070201110d02030a0209090c071101090510080702010609110a0216060203030609040501060306022a060403050412030203120a06030c080102030c070b06010203090310 88
    0x125140c1050610920983c488110385000d80884028034000001014aa03490700a03002000080508130464005003440300000449009592011400b65400103030582c0b45204041c5103a4003110740e0000303005c0c00d099400b8200d01031040255000300d013a80440402c41e843d03070940440c0d000d500d0080002541d400d101d44025099030002c50100c4080d07001c8232600e00f1650040c0030960480340001d14403500c600c04844260382c1060001d001c80115561050045018a81441400411031036001d1040d01c3d01c0c2402c4000e4038054551014080b16150740c6000c1165941c004201c03644054140d07950440c68549140c154003424464000402c2c3d14004242d0907220750ac0c41001c0c47d1240071000400e002410155500c0d502e8080c1602c1c00380004604100c240104112454040e1480740f0900c1201d1800041c08203508808400340c83c0003800306e840d001c0400c14080403259803005441e000d0000c62641c00c5c1081d40c41640d20071840f00812004184000401c168000e00c16221616005015241d024042c004440c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 97865476 1250 97864226 97864229
    0x102030108060f1314011b020c01090905090d0f18032609030703060e070e04120206090d02030405041e05040b040c060e06250c12050601050409050c01080604061e 71
    0xe0724401c080029448071492410180924841004004003c0703980d1a00d200d0921010400c5020790340311840740036070910b540301c56010054994080d21560714440c000509640284c0d00c4007045500340401e001d1511804507800304103020703034149003404026040c1c0944490312500c03201c0743c1c480c80040001050001c841c94845004115021821090780321000c4440d140c0181d103101ca8141d808210180000755060b40f00d210300c2140c841c01c4440065440c61150800300d000c4400705c46007007080c1c4101e41000d404124580d0420310407809800071a00842c4003c0d601c0c01a403207142d210740e443d83c0d10300f00354104288500fa8081100c980c01d020610702410003100450b401d5a00312024042c10400050b510f02c100c442c0340d4080e17802808035242c40900c100c480d041e2480e1000041c4c264005103100750018109107100001040010311010300b11000e406c005081640580c8600d0040c2d05000640300054804980038003004000d0038481e0058540c1340215004080e5900300d1840d016141d401c14a4000014180e2320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 97866726 1250 97865476 97865489
    0x2010608011815090305040b0a02010204080f0102030105091f1a090f0f01020a080c070f06020609070e15090403020f032a0c210f0a080307030b121b0114070501020301 73
    0x11482080c1d000c400e0b0028040c4001805902d8040548140d41a4581100c45902d0007850114202922180503c5080d0312400c090009030b94006010014030000b8006104841c1d4441c000f14195807511001c200d08407002404142841d140c9440490b6882842d000c0300c0103020201240c4951014580300032000c1d600c202043c034450b0505500341101c40c9814000480c0050060340940301844060395551010b41006802c3c0b034480c010b1440210301311880c00c101d8001402960b008000a0600c0c20b0701500384240c940091500807058004c010240c41806402c00300c2c072400b0341c0c403d1141c0e0380e41d0030103c0c10500c0168031420315010000c2c1c400700d20614a140303400541c4190500c80500ca240089140c1d4505180d003040350000241ca01050081024800a51007008a942510110302e4103918890911600410071117034200c000c024400301c2c540c14031030010320108c2034440c603100f11607031035141795188410013103108020382441c9801803d9102d44180507008810903140c0b51680d499207429400703500240520f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 97867976 1250 97866726 97866731
    0xc07080307090e060907050f0a0c1401060f0902040b12070e091503010e0c030a060207020a0b030106120b0904030206160e030a0b04060b012303071b05010902010e010201090b011e05060a0201060801 86
    0xd600f5161201640b80206c00d80d469881c60a24034014146081c1c01c028030f414240024002e401e004509040c0c00c00d0192800e581c00050030b01c1c14030a140f440d0b07684607004100080d105100510220803418100c1d010700e00a40c640609507603402c0421a401c1c04c0d86c84d90950070a500409101d030142d1104842130360114201c00074041c7c0c2c030075404856a04d06081c04e0300799140d0b128002c54008980f0503070043c20600c0c000384c011542551180b8806400358000e91082c40003922030700800c2c0c586883c1e48921003050b82c0031500e4090a04080d14020743d90003025004449101444404541003400b556101d0700115000d401c0d94000d400c0f6082c061000442220140c584d10706062003241507602c00d00340d6424090702e9002980351160b0308404002a900010070140600c610441540d04c2c0c0403d04144003c03103407207070001140c0c400880c400105003c8a081949055a040903034400c00102a0700c081415101080e640c603072003104030042080310428076441103410800c0010f5092690f03034103400050a90b4080c0009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 97869226 1250 97867976 97867981
    0x507020c010912031808060603160608041b08070801020309010c020708100c090512010c18060504090f06030f1a06060f12130c120510110306090c07080307090e 70
    0x1661103689400c049400074000c52414451015140302442080c1d0082c6040c039043c00c0c9040d02485022459000071209600c154100840c1c0e00d0100100301607540307031800c128140341c03a02c10040e00c458006400288682604e209101012800c1c41c5910010558001191802507451444500075030081e18618400d50820300d0110502c0e000081100880d00c80900404003240c0300c0029074014075205550303c0c200b120088000945aa40a4000f01c1080a82d40000b44e0868442d0008e42000031001003200e149541007401c202c1150800103440448460410200d4000f5001a15a0041c0256040140b1070402440c20800b071102000c861500d040300d41e005010780f0340310a800c01006002d0020501601c410412880401d401c0321201e09400c584401104080700c07802e5500c900354040c540e08001050010943d0f0a0140031042054001034010001d040200301c00102401c120b6100040419000d00482000302d6500d8018004072441d4070b40246030725441e414401c40c01041124288034906000a20001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 97870476 1250 97869226 97869241
    0x1302041104060c08160615090f0c05041811070c03050609010203090a020f010e0a1503390c0c09060f0b09010906140f040b030105121204090b040b060705070905 70
    0x4a03019950036803203039a00f2100c41d6039103aa295020690050000300710341403c0d030008695001c0c2014030440307a00c002034000c0c1004007500850700922810704503a804d0020605181c0d8110003114165003101041004d0800404c20b5100544661111000b042c1070024004c030501c083c0d4100e400690b8400c409a903519141c85150138241e00050b102c6a0003038004040d17801c0145420030064101c040e06041a4501e0362444000801d40940750340030f01c1414041d80d071511800c030f40c075210710b030380d20300c2c0166540641c6000038013180941004450000340714071800b540381812034007911080c460740303074450409021036407903259074409840d05105c6c0000111090078041111a94181691110401a51001500d074903280049404000c1451000a402c8040003981d2040d0f141400400103082000b2a080d52545094188803001c02008250210b0f034101c00c0c082900952890102c44c00c030b0344161804106c20b40000000360045c50940c0945903c5000040c45400300100450301c002103070060b003c20032240d81c4016 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 97871726 1250 97870476 97870511
    0x70f030201200606010804020f04020a020a05010b010c030e04020304110d060e06011203080402091b0a0e0a0b07030c0b0a1e0e0d091404050a1b02060f06100e0409020102010f05130204 80
    0x7101404140c10a40c0013036565442040c3c4c05034040c0c002480340e21a01c0c0400085804c80e805000004010f8103c1c0c0200401d02c042400b600220300401c0c40d14441d004880e44004024542c10100d80d13104980000c00f003400d0082503038203810150700080904103501021719015006145c2a0112034039030007058000a001e01e441c005100005405403205052642c0315400c10264100c0102070b0900c0c04083c0340508484198000980605c010070b4640f500490380610030445000c100d44c1c80084c00c80740401c00000081d500542d5580d5070b41e032110381c020494943d0241540509192455012142e00d0038a0303080a060280c1c1100c441d2a003114186c841245505204680b6901c0c2800780040703107101d803082084941069403115522006072007000507000386401007031a1456820141c0c0c0010781c082c006100c01100b9a0120311f0300300e8012070740c0f0320280140c0d0002400c604000703040c10f40700c1c1c3d0303071040e0490659000390403004d1414800d000400c010b1900c1440d1114410300c41000303038040e5181c802011011000072 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 97872976 1250 97871726 97871777
    0x2210708010303120605060a1101060f120b0c180607030c020d0803181b12070b0d0b120d080106140c010504030201020a11030421150c0509010e010201150b0d0e070f030201 75
    0x47d10541c80c2480000c003e40f81e01c0402e0b8118200c1d9980e075034001400c0380340707074048201a00d1240c0c200c2e04034030b000341071030160840080c0140b00c10180801c0203c9800c1f82c00041100b18242c2501c085459003030a041c20f641142d0b40036000f0350050401200003003005860b030001c6200d504a4040e250b6840d400c0c03d642540c402d081d1566071107500800c0b981d40914906010007040168610701219130094441e09243e1082d0002c2101180464a6004d488000e1414540f00c071003441402c0300a2080701520f00300101041410b1040c4c40c14420021040580301102804513420944584001d03c51070403e860024002d501401c00c10300051100d4100c00e00b0020040200e07802c440418605500ca2910409190060700d81c6d1082102e0a40c00b20408040410003401750101e16011510b5250b255030316640050212005410200e046900d8510310791410300d55415020190b82410702d14a450f51403490000d402041140a20f0025110b04071001880c4182e0620030b1041e2072003a61054521840c0b0801c04500c0c0805 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 97874226 1250 97872976 97872979
    0xb0a2f0606011709061801020d020c030a0e060f071e120207090612020102151005030a080706110f0703080603030d0603051e01060b040b0c03090607030806011403130602210708010303120605 83
    0x5401003406d0000c203030b0710b141445400100051411902041d008126031114417003146581001c56480311140c2c00401000401c14280c1e1a42d02c1c01d11401b800f03410754850070000603c4102c901060312030910a09041001c1c407580001c1640a4100485020b07580d500702e0b1140d00e10060900348040365035400d65281c10b0308a03606030010304c11400703d0300340300c0c010b10320080c00b041d90805004400101ca55081140541c0f06003e80e50722696090503007007542c1910b42100c0c1e882d040084c10040b0142d4207035210212000c2c1030705850f01c2449915200002411480b070b45485101ca42e06010010051207004103005140e031710103c5004a501c014450143d0984a03284600340b000d02c0b05020810243d010040142110003c10081d01d10704100200010000e4100c03074001c0c1c0000b074001081018070351b04601075540030440703040054214681090400c404061026005000319004290300b21811030f070f0001d2242054456030746004034604001c0003400a4002d01c001c4d000117000002d2a6415100b034070902003038820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 97875476 1250 97874226 97874233
    0xf030f0f09010b010c0b0901201306081311041d0304050a12020303070b0702070503010c030b0405070212031609030609060207030219210512070503010f0e010b0a2f0606011709 77
    0x30361b04c4555403110003d081803070654803140f8098400b010b5500307114000b80f82981d62915101c90307440055034101c1e560441c609012030740741804cd110000c1441c61070125408518080d0884900010030060b006260400454594010545500501c0030002d407041e0344056500503503080d41c40c2071030944081e0062000e034268108208140100c0c01c0b41202c01c0d40076250340125a40c1613611804203084403c03100d01280000c0d070342d401090961410303005140e0020030038030060240701c0c86405000940d00c00500b40180c1321517491105002940286140b000a5810a41c20007501c025424134070041c0d407020800b10010301079800d0390180340450300d40380b0340600d40001d009503545c181d480d0b499407030707104410086090050600183e100c0e140b080090340e1060005d60307185511383d40740c451103c0d088040780d002700c1e4084a014006109012590040e200c012500e0f190410543d201403204184240030101d07040020f445000d2103004420002541c217001d80404ea0b1030300c400c41501014601e201200f681c03507050542 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 97876726 1250 97875476 97875497
    0x91b0d08180607150203060907021f0506030f0106080313170a08030c0903011506020c0301110306040506010513270e0a02010c03050c0d0e03060c0405090118020f030f0f09010b01 78
    0x540504101480081c0544103600d040655280c41c10b06480803052825082e40000800619003410901e403500b002490000300015500c00c0c50b040400303038403800300d800d05a030350303030001500c41ea8104000d903140b140790b030001c21005850b003003e19182e505c10b44542107284400384001489960303c00d021001040810040c0c504445107a03140540d40d4800340070701030300410900015046aa0070321030300c2c0c1e02e60403802002c140306140020113800d00302112850b0b44683d1500513040c0100e40c0d800f0859512003801c03035000a4542c1d8900043c0e8040c010550040c80303114408078089801103140040103c1c050740011110041c0540c0485801078403001031560704940c01500740c000055000f250000304480c0300b4203050b820142c880b54524500486c3d0303818240001c0c110403c4100904003132111a030850b4241005034905401c01000c18807003c018400e590740e4411580088004100903410340320007600510a035a964107204140f0704e20740c001070360034501c0001148013050015405200c0ca45044106854403141070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 97877976 1250 97876726 97876747
    0x1141b07080a231e1006060f2a05070f06030b1c0620030709210209070f11060c07120305041101030f0207060603050f0607020606060f0a02030c06091b0d08 68
    0x901c0d180320070960b04c607140e40e0100d02c0c6801d1980c40132442c61100213241541d8083ca401041da140c80c3e2081c8280a02d01428090442d400300c120f1907400078188800545213400010070015411520f0043c1c80d50041d0a00854941c030b205626004445084c2c0d014003240c00c0c0102000b800980d02e141880700100c01801600000b007840c3c20051100b10750740c030828513044485aa110040d4000c4803003000080e800481030000c0b2000700a031012200c4158010410104c081d400b08128001c090400c00030300c0103400c101c83c0e40070b100c0c142e03911081090009949003402c080140f034003aa000050112580c0c41c0b8003103458000d520904c40c40d88030741d07003010400d0400c500040054000b44a00307d101d4072400e40070020f040c040b81581c02100c00440c45500105850988890072a0070800e0182140c02190007580a000c1c5507601d100035129004000c980081c0c1d100030030310303080c0e10310311541e1f00000150040c2010043c04070800b0072071824031020a40c3e00d4107149030500070003040510340c15005102d520705004140d4031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 97879226 1250 97877976 97878023
    0x905210a08070e04090f0506061302070507050906130f06050909150a1e090507030c0f080604060203100503250b0f03010315060b0f030604060b040506031501141b07080a 74
    0x40f1000608005000c04d1030341c0b9a503d90031403040e01520b05500135402e000840c00c100300700b081031620040045003018981ea903050349400c1184120380c80340a0300d00c003185a9a80b03e103114090704032400310802017903115052480c06000a4442c103489001211700044001c0804100c00c0c50b00006a098840715550b051015002001183c1038081c9116a0303010002e41010360380b0445803c1c0b0701480040c41810f25516083c0c40140882d04103403580c208000c010407540724000303040c9812961080e4056103961b6003c0304c40002d840e907680155818801c0c50010090104803070503c0c0260303500494000c82c8103480348440e00e00c1d803192800303030107646030200010030100b01025962086d90124907400305a0a617035407008505900402d42d0703603005160020a22102d0b152500c05e10b00240000709440b41490300d040b0003d070542c0001810036104001100c131403d032a13845801046031842c0d0240c111038803180c1038600e1079000200b541c08070f00180301e00e4001160158001441c140c0711580103d005400b0304c17440241101c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 97880476 1250 97879226 97879247
    0x1b031103070c080f0d0b120c01050301030602180402030a0207060b040b010c03110f060907060f0e010f030f090506010b090f03011103190e01020d0c080604050c16080d0905210a0807 79
    0x6103604144440f130312002500300104100141c01e400420990300c09810004082d2035420003203080e60020750103060036604282960304481e040640161106101d5410040d24500b240802d54814400070070002c1c401e4950340540b80080c001e11003041a08400014802103440000c0c0d0140030940d040d06201c0003034412000152000c0030340c03090743c0045021544440ca003035030030b4541c080103800582d400e2003000e0780000803011010083c90240ba04c2e200c0c0070300181c0000c210340d42c46800c05440381041c404c9100c264102c0100a58450f08131101580e44d40c00d251040d8001048032440783e40b031000040310382d24050092400c1c00409403099459610b4200e1a5090818405403c450700364031094001c03c45031080c4040d1056640d1828040342e8030b0510350004200d00700c01807005202d207140c8004c0c010352022810556182c0001045403c03140102810898118044d900f0084609030a2400382410002c01142070000009030740103240c005400e160f4581e4030350054489070307030000d42360800003640107100d82100e0a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 97881726 1250 97880476 97880483
    0xe19050f010c0602043b0c0f070b010b03100b040308092107080a0b0901020309100209131d12040303020a02270a0c0207050a1d040221011b031103070c 66
    0x1801110b9981c491080c1d82181e84000050814456105d41d1000607240240541141c0c021421003c0d0302c04091442c0401c005d040c060301008040350210b01c04900703001301c6205640003800c1a034250b030f541208400395401191416a80400c44000080e600055020b450959a0081400d401c1c11802d100b4008000040c040d001160144403540c8503e49900f4005640900483c07405440c5605450404000040026040940d180c0c410820410b0030f003400b24108511003a9100050781d44d810303020008100d24840050741029a180103440031081c108103d0020b6000d916038160384142141c0030035200390b0700441c4009030141c0c11800f0241d00500d450007038034a040c50119402244100104502420765400b140c0044580303640d0b10a4480450301081600d0003031078101c030140b443c1d03030400020505a03d030050b00c032980494501e0109007195504010b51000c102034071098408041000c41d50740c00b80103000c6403082280428248111602c0c400d000340b140d0001105586442d42c2c607a010100c800d081c014500b40d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 97882976 1250 97881726 97881737
    0xd020c04050c1b010605040b010806030619020409150819050d050d020412080702011205060f0108040c080d051e0412150603080f0a020601120201140c0a020a0303050a0e19050f01 78
    0x2c0d10901072201007000d98181900001044c0b410102031004031004080c8c11418002c08004002c06a900001c42d15407000d01103d5103e4480140f0302c408000c2d0040e0340200303200070b040072003d6164482c0500c0840860b00c501d81150900c0302d04825602c2442c00c8050040d005070000c200d0b0705c5400303014000901900176002001131500c4d07034a001c01e04080c89200b5040303640940000e800310540d0307404000506c903003940140070030503403c010f000154181d441c10555818003140000082c01d1040251007030005000940949201503400d800003006584001c0b030301c1c2c442d5a800c48844510b18109000e480c00e0b1007141c003824400340784c04c0d1542410150982c0d0000101921800e001c400a440c001c00340000d00d1060b0320503621804481c10181c10f082c4141c000f154004070056840e409030303a000c03010003000140d070b0030040c1d80c0c2c03c52002c9684c1004210782001e500118909000402c16038030400412640481d942d8001d031800e41e030002c01c51a890b8060b0b0045081e000d6034000c0c4a54a00101030b90308442050410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 97884226 1250 97882976 97882987
    0x3010c031e021227190204050603010b1c0609050604030804021017010504021b0a030e040b09060d0b0601180605040e010501020604020d03080a021209070f05060703050301030b0c160605060a080d020c04050c 90
    0x2172400d448081c0082400071004100d00850030507006554001204900901c80943c0403808504002d034411491094101740b107c40d80c0500a50307174440500c10780c014054036854a45030401408090068500301d0080544461108040388254041e41d01007808101001542e4603250030000031f50412070007a50010700311014651101c100f042800c2459110361200c01041240c1400c0004881d070803044103026410f8481002055601c0700300303180d00e00742e22410324809900c400004a9040078080030411440c03504800128002d030700900940103c91103040141c2c0301d81c4c0c0303075001241c5030902035500070b401000400900c000030b03001c0d0550f030742e0202440c1001410300484d23928880952009407000882038125020a0010300c001d03004110240c103043d178065151030a207590061151005100c0503000320a80004201965814000c96040c1190804000052009070800c2401040103907484c500c0745c2401d48000600300404928a1005d41c110340282c05044c0310b00c8148006408020703c42e1303800700000c101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 97885476 1250 97884226 97884301
    0x7140a0201050405010e0a020f1318030e0423070815150705010c050f0f030406020904020712031a10050903030405030d020a050601091e0c0e03010c031e0212 69
    0x141954000036030010469040c1070401c10f007181d00c4803215202c03030f0300402900009a103c50b458100c0d000c2c2c05036002d5404519104c0e0303040041031380c44803020003034030055808024507500c2500e416071004110360810810202114200c1c11100142544078041074a0002035400e90080c201c9650100d080d241005005602d000000d00703400300303501b40103c0508040b44590038403c0c00d00c00c0d62458169810007a14140386055803e141c3d00a600300c04501500000000d0708100c07454054504404016006546a40d214075151444c860003050345c000082c94211803035079030302c4040443d50f2521405407100007a81e1680e0012213480c0d000c0c0040d683c25200030800060191800c115001c0c070b50000364007400300f14a0a281007403c0c0b0006034040314100b030400d2081c0d4110004417884956008004a0024001a04200560f0020400100c0f80d5041d480c01c100c107003400350160003200320600b046400c680940f407015042d40c101c0c080c441d0040070f041c040d2400030748800035a840e10041c0c58105202078414684000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 97886726 1250 97885476 97885517
    0x801090e1c090305061605070210020c100e04140f07030e1906021c06060e040209030a0606151709060402040c051c150b0715020904020409020f030f0f1e07 68
    0x9001c00080d904030000c00c18883c0c02d2002640280e24018540c11040c0d0000e4014a207001d02240a4400d0544540c1e0200140c02081940005003000c0c00c101c0d50051201000340071031a400345040e000c4c030304184418951001405100c1d01c100140c889501040d201c62000700d00a2a0b482c82c0305d031062184000da0038250301e8240c100b82c8498070401c000b40c2d07610030601c0300c0ca160441b01496408864280310f0203000da65000015a0503044003a01c0060311500c41400091038540c04031405894a45068408149400781d01a4544065070f00c0c0c4403800c640141e10381003a04011300301d032307840002d402c00e002090062074141c0180e085080d091404134248000307164403080303035200f0040c01c02010b643d448050000d680d01401c000700518a500a00d4180316280d1510843c0d0b0101d006040241540001c00e410a56035560545002d040300e02000c5440301118503440140e68401c2d61441050102500041c94440c0498141886264146004000512040d1000b07000c03140150103981440a100003601e407100220 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 97887976 1250 97886726 97886773
    0x702030105042a180f0621120e130203060102070803281b1218030305040509010509010b0a1409040c2007060f050306040e010e0d08060303030105010801090e 69
    0x89807094540d65500d16100b414903a14010004001c01d014010000000705240500a00c2540c0801080b40179090710454010100da070415410384901e80c0d800814203c0030700c01500c4141c400c106914040d61400d0003914854082c4a816074841001010051000039075005984c110303030103004a600094860744414210b4201c44842c500702018540341c600c1d40c3c0e014151944140816041c075448a0301070031400350250042d00b002400c0360302900452481d4a100d1103000d8011007044c5000601d4940b42d1500030602e900511415115404000007c101440e1450080f8100c2c0c0010003401d1414021400944400e4158504d192050b4030910000311562154019140101d80c280e881c0d807801201300344100c28480c0043d03080f820550000405006140c1c00240e420120380803410202e407203546030f20009020b0960003c0e543c8565017030216410701c42000043c91004806140c450049580d50382003403560b240024860180010400401002814100d40c0610001000f40042c0c41d808004052141c54200c0032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 97889226 1250 97887976 97887983
    0x902090310240603020a0e01050315120a05060a0c0509100306120b0702010c0314060409140f0c0102120a0503060108040206090909071d011203050f1e0a0f030209100311070203010504 80
    0x11140e4540b400b65200090001030000d03402c0440c1008052000201107440c001c00c02814404000003040140d04040d000c0804440000e0000154820520005440c1c03c0a1882150b5034440d14001ca901d108890003005000220340d41d9040c1801c101c803040117a0100303000225001e0640e42c4101007000e80811404040d8503000700302001036401d051400900b141d01c1041148205840c040700c19a21000040c1aa40c01c4181201c01282008560400280c0101200b054192074800c00600314201d036000314042100044c00d800b0f5814689008001d407900703101d00405c08002800c100700080066010b0742c41076030001e0025010ba418100700001151581c40161228001540316100030081d04400724514100d0110030746003c100c0e0351404070443c02c11100c5450081c140b2401140030f40c1046403450507642241d00040686903107403800040c03030400e503100516aa0014400d0440c06020314024000c44081c104094541e0618000d0100214000d045a0410303c44103902042284050f1341d09015045c0118003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 97890476 1250 97889226 97889261
    0x4170d06060302181008010b0315190501080105010503010b0d051306140a0c090b04050609030a020a030b01050312070515060103020d060b04260304120f0c08060624040902090310 78
    0x280340f04d4a900007821956020701c100140ca290400c0320303074083e81190454121a4031070340c032600d401c1c0c4d10440c0d50300c4850040b42c00c6406044200c81d00c3c241c8603240c1046070300a80740c0c50305591300c80004440b544824010082c41040030002007841d40e0b00c0c0d03441140d00c0b000c10080459292004d03a202e4064680038091382d07464000d01c00c03d000c0c2e42006440340050200080c108124124a801a03229441c0500e1003120312612000c1410394840d18140001170140c0d50003007002c0d40d416124608120310280c02e0140d180a4418500c101e540e00000000b220342c00780d00700380101030b8565010754820080d40c00921884c101a001d12100310b013080540168006051003504994540d418a041c0f005171881000014031440d19021b00002803000100488040d01d80b02c3d01c14400e2031425051234074664217404001045402c410781d00141c0c0e010f0105170305004903011a400f07960100c0c414203c0c0306040c0302460024080b41d0400c030405c45c5141c2d41e402040104406000d6426500443c0039020445003581d000c24141034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 97891726 1250 97890476 97890487
    0x20705121c030e0a11040605060c0f150f0a090c0e0a20040605070f17030a0b03060f1510020718091203020a0504061101020d0501150207051804170d06060302 69
    0x21215a0300700310041c85490200900c0b1107094502e543ca15042c0005410000506181e4900740c0b100c1c1c02120281501400d10782d6109106e1305241d035500210030717501005004101c01c8404164041e00d1550142d00340c050444541d8503846e4515009007504401201e00d0b0070301c207500050090081d40c1c520f12640d40c0c00c400083c0009000554040301c807101254032882c020401060140c0c5810030269908a40c0042840d107054006107004250b0405101c0c0c030070800003000c410450b1542c1c82d900035075004407084d42911429203c1ca155940440300541d000066040c59064075080b5003058680c0c07400081191044030007042c2d482a80420203d116080107841036110030742503060094003c14130504c4111881d08615103208420001e103180100d0180e04104030320032144088220782501035494042815070204a656950102c603200c040e020304038800980241d07180043d461815180902d442079001107c030310a41d03540d5841c00b0b00f11104119000c207120080c4203002d1495176520070b00024181c1c139180103a03500b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 97892976 1250 97891726 97891753
    0x90106090c0c0f0602130305030c281109060d0605010806070816120b060c060907140f060d0f090c06050a080c03091f0b03030d0b040e121902070512 65
    0x180c0700114118148002c610a00c00001c501c80020380000740c20010040e202e4886441484409403168400b0b07010f440701088410b604500480c80614080012005010025061126010304200400080c00c102210700c90408941821040729522900042a0302c17495920f5075104801c68800f038220703c601e940410b0421a480c0c0d009041907400c20900c0f444000803101d81da2000308445d9400f90701030544c980b0762441d03170055101c5d003041c1c50311000b00009682d62890a10103480d502c0302d042c41416102c2040500101541c10621b21074000b0420213401c80c0e2034680c03044a410301510240b01080c02007650350000d50041545002041d02071302c0b4030342d9110b564a070346040040201202804e40600c27034804109024606000081e040e42c00c4003441e500b50b1783d0a800038908401050354101c925014040007079101410300d00c50b4800c2240010441c0d04015284012042e16034401004028507400c0c1e0381002102c4615490044280e203040c500c1c411508490b0f03c82e4041015240303072142c5110240c0c01448000d212 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 97894226 1250 97892976 97892981
    0x2071b0b030f0411150406050c160b12060a0807030507060e03031204030c0c18020703110c01020307350a030e0a030207090e07080a0503070b0a1103060405130b09010609 74
    0x28182800401c0c25810289400c0007501e9001d80700a100741300841c1e21104980341c6504089001c1410b1541c10340796a0b403244041d044c0e0b4001d06240009000300b90142c042000c0c2440024203490302e01c9a141d040240011500d0903528000d003080707900040a120024415508001d10340203948114043c01203589464405007071400d41c07c04103803181c0c10520520011403206268990302caa0549404c010641903401d010a1906e01c079046103500304010740703202103d049250000c0c261648281c0d503190f0030840c41c46465440c3c07800c4000541c0103030400c10140020509054000f403a4031000c403d0b80fa4001d81e00e001c1303048094555a01042c07100340204012030100c1c1c05200d640c0440742c0040240c141c0c0c45069800a44a2180d0b0043c101659a60440725420389800c01404001d412840c1c1180d0a50a042c10941e5403a0041c0208980343c000c180002602180c40780035120b10f030150300c910340341951100820400900780041555540100040046020032440c082940c05100a8000081c1541c02c0c100344105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 97895476 1250 97894226 97894229
    0x20403031803020906040902040914061b120601111905010603150905120a0e0a0f05031606090b1b0d170c070321060503030703050a02070e060f040e1002071b 69
    0x105090302080001d42c13604545242e20290403a00001d03100424030001340100303581c64019001c54890713000c0140715040024290f00645055030140c0c100c801031244462240705500a4806036008440400c0301d5501814100c0351000341e110a442460340b84542d554040301d5840c034180d4983e0746071136040040c04043c00d000c0c0000b0700c0184050003044038a450312540c4101a0300c04121100002806071070080c40b42500200c0c0c044d0080c410010f007617582040c1c00310f2900a002d0640300c0c1c0192903200c00481d0701038100c00212303959500c4202c5403519115510b091074100100c00810300c5030046d400030b4107040502509801040c0c6458040c5c0754107802c15400c05104005203e8515010304118850110340c22440d1005181c5999190041001c11090684050503243e0302c0f094040c03002242500030190400d01a01c81c51361294201e82c009a601c000e0201c0c0c516095400c2d81d000f80c2c481502c0801414145c00c10100c0d120180c00b00c4844aa042443c0802c030790249500340c6420400a056089001c0084034050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 97896726 1250 97895476 97895507
    0x6060f120c01080406020903010c0e18060d0803040312061707060f21110307050703020609010c0504050907030e030a03020d1503080415020c061206040c170c0a020c06040902040303 79
    0x803118000300c0c010354414448080328140315011000030200034141d0111100002c0c050028041d40070050400341123044143c006d50b00c6001d884a003180100b9200030799601c0b03a54007c0c011807030348005840380c47c842c0c1d0020744241d040004c0001c1c482d800c0b2051380240c0700240703050190102080521710070300b410006130743c00000401c015a4200c50b413240d80241011780540d1112018048050481c08420007004803a00005000e100401001103140d0401301074095076009409642c425076640b030640c0d003200c004074a81c0001c42c1e0300703110034803041c140007140c90750000c52400d0004084d0081c8401d0b9203143c105480c07020000303800041c05c10a000840c018800e140d046031030307000c40c0c281c11540c0709043e40c01107006440000c4c5070040704800c180d108001d44100b001c0c0103000b15079215084001002c1c5400215234450080341406810503a03d8450301110500e2040021003000a86441d0340e41d101540c44a440d07841180f090201003003181d5a40380c002c01c0107146150006a855186160103460b0104406010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 97897976 1250 97896726 97896739
    0x120f0513110d15020c0309100f081f030305070501020706090b09070f05060301060c080f1c1103072007050a0f0603050601050304050a030c080706050f0603061807030611040e040506060f 81
    0x400586140c407030500f0781c00640405a00d07001c5040c1c15514500130107040c03c0d80540d500c0384190300380360441030212106400360765140c096074489022141464402c0c16040a90042c6c030030800220b80302c1c8001d03018451050340050b1408025881d090280e43d01c80405850702c0c0010400e02240b00c02c2080741000411040c040a99007031324120025209010511034241401034100d482c104014400c1c00b207480c044144c9407125120003010180710316415040070700c0a0305a00c0d010f401201c40314407406a0344180032964603c10b0300030598514801d0b81842d0a4840aa48204400032910790b0341c529110020f01810f0078a915101e242c141c00070156400600340b10b060103420014000410000b203441c250711501401c00da142003400d85800c84023072041c094042d00c1c8a14040901000200046105d03004403821011140e181c0ca0300084082d411207403412074444da07130100c0c2c020000180380e81c002400c1c640b0804049403c1590310300c43c17120401c204503011220360304004104046446c0c1001c0d50060842c003a41d86 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 97899226 1250 97897976 97897999
    0x2010603050a0f020301140114040b010816030b060d060905090613050d030509100f0903090602070506090f04140403050d060b040506040303051b0d180506090303030601120f051311 79
    0x1050b8954034a128064081c401090700f00c0c2c1591025080240080d1440f8100b41296039505003081017501e412a04a20603820103901500540c8a0011540030310300440080f00c1c0c040f140c250030750042150b40300850704074105001d440c00c41101885600c0090828010110307152138071124040c20200014440848005079010070300115000189481d01e800860030700041c0c0346c07140301d100e43c0342c00d8404544041650405210a0b000c0a050b00700907802482038071081022a00d0300c2080c1d0300d0f90140d0181b1b6030800818042a01c0c1c03450302c0507400c001c01c00f01500008034191030710403030703641c6102c1142c065010800c0010048042c8109110702d000510510050504041c10640024054800c41c440a82000004070301301d02c9441c14141c0c0710000c00e089170100e42c00c41c5421800a0846010380703c0202c1c0d6003480420009141c10401c3c00c40d01c00d048000c01943c60350703840e81c0040d1407107070081c2c4c17425101d2940d03035a401d1510100d038802c0c03a015000308020808100101d2500240c174490404905004180340d001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97900476 1250 97899226 97899233
    0x18092a04030f020108090322031b0501020c010302070609050d050c0607030b1003051503070602071502061e310204060801020702090103060b0f03061005030705100806060f0d090311010b0102010603 86
    0x2c9040a50342440d010050351103003124180b55010341c886071306062510701c20320091000d04009000440c1d10415101e00009100d07203500701c10710701034420140560001d0036805817640c032a50082c18028031520f00020840b4558480340e02e04000c12680d81d011460000300a050000c0c00c01c085a48080585018012076001e900071440343c03860070351700a0526490340007007400016010007902071490054111101030355218402540c4542c648150b108200030380414200881c03000c98104c0c414a0780402030303e02488460100565000001c107108480007a0b004010625402140501c0c0e0054007600142225241801004221160380c1c1c0403c2c1c01d684104520f600585482042034112904181d0000e40c101d80200441d298400394480d066144c064070003080601901450751342d00303440381542100c0500d502e507001e00440e60381ea0b103100300209000c4000211280703029401800d030074103040106130400703625529903c140c0b040c0d42011800300b8004000000071700401d200d4900303940c0b0248000c1c00390034590340303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97901726 1250 97900476 97900493
    0x605030a030e010c0602070b15010807260408090603010605090102010b060304030e0f0310090609050105090d0503040602090a0f06020a030210060f0e09031308070303020c010302040b0f18092a0403 86
    0xa00b505015800322408240601c6038103844001e5000070b103125652500c41099070712858081e00e442d020444090118240341e1141610b4603601d034140b0005198040c1c045503040401200400488a1000412441803030340c03a8403010314003d007141d80351507481d03040210000e420745004071515402840e0174420400440d61003054408808801d55240c0b40c141d6070b01012a0411404d040355903559814080400100809030b40301003030460040008107c80d0300c82c0c0c07070581d44030b00010700038038005041800414089001c0380d0041c421a5070003000d611aa03a0f40300f1000340149410f910500140c0c011551050600d42c060004a507003403a21601002040d04140410008189a0164044001007180001c0c400750007001241c1c1c001910b4000208c8556071011019640c1e0003c0c00100c005014000207110654003038007c0c0d03130075100c14140003818440382040c1c010458109101342c1c04074040080c0045495124070706030034000e80504180007001c0d4001d06d000404d07250717a504011641e140803c010008180c810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97902976 1250 97901726 97901747
    0x1060b0f0a1209020301021602090a020405090408210109020406030507141608041805010f140a0504090201020a0f0506150a05060d020a0c0804080c15090325030503040e0108010605030a03 82
    0x50524000b0114000410b4000f00740c00c00c07000f9003662000600c03050001000b0100ca81043c400c231503c2210350743e41c4178013038281c0c0180e11480e90400c02d101d01040000c1c41a402400c4081410340302104070b203060f1250700742d004500b80d100c482c8a42e40040d0900482e0351602542d03a01c241e890601c3c803100c0803181c5a0380010f00c40c060070701c4d00340c40c4038618500070011110215001084d074000700e51040e981c00060303607008000c01c1c41249074440b0f42e44400600c0c3c40d0809110a11408014000742d00b0070b2400003888040c02ea92074049045008110709800001c40d07081c1c80035402d030b000f01e00501c00c07443d0001c0158000c60008801d10300c2020180410040d5036135040c1219044030700382c1405a2903428410050368002c1c0000c2c0014542e801c003160202d0407810005280800c0c035412190030407512092021204140304405166416400020714103141c4100400401010781e01041800101e59580e1101820354105802ca08410030540e4010040d000e0240550f03006400201d018180946059901800c1941003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97904226 1250 97902976 97902997
    0xa08070c030e13060504060807050a05030d08010312140a0f081305030409020c011b02030702030c04050603100c020f01060f0f080d1b0f0204020301060c0c0f080a02091003050f070801060b0f 83
    0x50141000c4203d15500b142009120141c82804400c1c2c40c0c1380140c0d181e07502c0e406158095803c5010004070b52500144001040ca00da4548800c1a401c5031620312900e4040d4400314107004020516178050600b8030014007a1045a07a2580402c9441100c0100044006842d07000c100000000681c007040d00032080354100c4807a140c005035035200d191240380c054034402001c4003444da4008a480f1f0742940200041807124030803411b0f10b40ca61425020402200d500740e900a401d540032181828490f58268003120400d0405c1c0125900240307054262800e44e0143c1c1c20440d200b041a0004000c4064030300d880c500600016405031092010740c0c4030042002c198015240e0790800110040001c0c890380b0b12652604980143c0255602e41c0c540602529a40c1004000c641c00e580c500e6000130000c1c008110321064440060182904610710b808101c403021001c5d01190441c1d80080c40000000d41c1042000b416501c150080e04400d460244218212026036000030b1441c4010445504c1d4000008201c442c00d403070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97905476 1250 97904226 97904239
    0xc10020304050705030d0c0311060403050405011809110403030e0d050a020d0c090504032d0f03020a0522050126070522090213050a12140f010c050a08070c030e 70
    0x841c1d04005103050010303400640c242c080d40300540180f0303074050282c06c400d5000fa103e8040c0580c40c07010042c1c3e240c40464000c2d00040081c0320900403036104961220052500018070f400007911594403c1c21140030110250401800003810805c1541040002080e90b10858024107080c84d241c4809490303440a000017480745503101c003032604000b6000e0045010f011079100400c01071031b003407030301910646c2118070b44040c800041400d010403101c2c1e4400c200d02d14145035101410944072050903800b94000c030b070480040c0070040c8000083c2405122200610300c51404d81c40302860f02d00310024042112903170707158241503403e0609804002280021a401c40a90300d8007550320082d00c9554054030040c08400c40d40e01c907840303000083c018401d4001e002d10f07442c80502e05e00315030390342c1007005000d0485102c0c18040107400410100443c01c044980381c0002200c0d0f06645220285448183c01c4400d02490b0030007280d4045480b6480f1076000c005c5c50341c84852410640d200307000c00c1d10040c000c07a210b02c036803d20528 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97906726 1250 97905476 97905481
    0xd0e1503060913030908060703090c0b0702031002030901020912030a0320030403051803030d090c050109140d020102120313110418061104090e07090e010216060b0303040b030a090506070201020c100203 88
    0x500c10340c06040200502406c7e80c8150610000003409051250000c0e078103040c1c0c50001003084407849013112083c5a00600820b641d001a00001c00690401402e44115550038804414240c690281e080320780c01d0b80b90043c7d1b50390303900d030300c0040c04940e030801ca08080d804072600c0d0b1088850b03404085a40103900342c01c1127501c8800c4c400c800030008000c3c0c10300e242c040c040440d822400581940103082510b03c00c40b150701d51280c66200460b610351261042443c0103d00c1600b07000b4070b041c007210381c44440d4010310598400503003101001c072030741d40151100c00304006400038950500c403100e5540c540d80c440480381440b001c4058020f500e04480500c03400b40c5002d9888083c2c421007a20001220000c02200300c0c180324001c11211410746840c0507100c0d00300d04038100450b94500035010304c03c903550300301940d00c0f03080300d41c01c00d46440b070080440325001034041c07004100100300201510051441841004404180c20405d490f00314107145021b0000720a680c0140704100d400100441d00382600080900010707100d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97907976 1250 97906726 97906733
    0x3050409091e111206060d030809030702090403080708060307030803190f0507050a020f1516020111040e090c010c0c120606090f05090d080103020102070e09010b030d0e1503060913 79
    0x1040d8640c400d107090115210620820103481002400003d08950003960b01081c4031065032910003c444880d4450544462480002d0003918030030741244250003103d081502941c0450800402920141c001c2040c02c0100004540d01000b1107502038810b50280c0005841d5a60f521304c6400050414805811104801000ca02040e80060f26800b0084030510181c108064007038101d0f800701c2c4400340107024000300301c1401c28000408411130901d030a54001c1c2c640d40d880d28407e0144401046c1c60465407504554800c0d0f00740c0b08054000360451050500c003d0518806052800c0c02c400c40050502007a0b00c0ca00c030220344070520400480e8407503d00380c0d0100030350745030410043c10b50b03400c802e070f0443ca04030700181840902e5002920554070a01114100540021b0960f2180d00074440203005900c5120180101042002010780180400d4008607003480d00000090034101e0f0069003000242200881032a07600c2c100f051003c0c01500341180c1c510350304191003c03c50600004081c800398481290810041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97909226 1250 97907976 97907993
    0x12050a0210060609050312090a09020906070503070b06120114060105090102150a0501050a080a0503040b1c1d011a0a0510140d02040e0a05221103030d140906040305040909 75
    0x8401c82400c001c8581c4441029003848138901899010348a5042c0c01c0158144002c100e843c2d40c14014894803110785442e40140295200c200c0003034000100f88000000694100003804855214490038251480c12a041c40740d2000c80036042c4d03102c0d80c103010400090080284480b03400240170310b48156148075880050345000082d041d00d5a241e680c2908000d1320313208551050741681c004a540c1003003159100b00c00b0f1341c1c0701813192001c1c0c0390360030800c802c100c80800c01380100750856002040c1070300505180c802c08100c621003202d41414041c071188944041d00c0a10403a444940300d14440303044940d03100042441494a0f000e903a00403d04a021584014042c1603003e1955030301c1d0809598a91f0382107a0003002e90441d1080c0540c1084110100c1c0a1007440d0207800e00c40d4104440c5c4c1f100300c1c4140080208000c980c0c83e01603480d1803c036402a15541c5080c00100410401c1c3c400115191901e0042d840c2080c0c0028003031429a006602804000ba0780f1100f190110f802208000c10000c499040a800c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97910476 1250 97909226 97909243
    0x819020d030e0109050d05030d0b100801120201090306020a02030304021305010807061808010e1006080703030c06020310032a0906062001020c01021303050c03010632040c0e0a080a12050a02 83
    0x10701c25200b1071b404082000001c006d02da03a80c4180b40500140c2003410030702400315a80c1d080341c2c0103d00e015005003c1030100f2108500003a0052400e403500c0c59494803400101d070b010031080d10058100008010075810700c1844440040c042101c00c02c015803401200c142c0300d840c24003c20081041e1100300c0c0c203e2415150380750002c0d00460000300029218000c5550792940700c1254120000e00705070b40046d000b240411104200c2e40c02d0380f00c803c0c07600c103141d41d00300003540014182841d00b04151408404200a00d118040c0d8036501e51806900044429801d131120449500001c2514140041800741c136134090101c680ca00060802c032441c810000004034068043d24021a031150303c08a449012840b255078140708490040701517400c219480010301d800c1e514107000350170411404980c0c044e815003440040c1d054030803d000c0d003c1c03680401d4400103406c2d42d4a4018580001d03609007412002c0341f03403401e02d08009201c0d13030008201c9040281d50301003141080061500600c00003040d4100303201d00a101005c4c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97911726 1250 97910476 97910479
    0xf0103170703180e06030607030501080d050c0f0d091403010603110103023a0c1b0215040b030c031501110c19050303120a0c090f0b0706090c0b040819020d030e010905 73
    0xf83e403685900402801090848000d8801e12841010905080c0a032291074180e5070788502401e0b11300c0050000396680d51041c00c0144141c800c0700c000f10b42001e011b02c950000030940d0707600c00d03c2d0716180050514102d42200440c41c4079074901001000000c4107094010703440c8400b8280962a481800c1ca134001102c14100d40c0c1d8082030480300b0318807290084041840e8842e10110b820406003401a1048408034815850000c060405000b08005850b0000d000741c00d800755545810b20381626a01348a041e90400d880c610f4000201000384060f41c200c8043e4401c2a030001c1c030700414000e0800030226a20f0516265160040244a5086880300708a04140b40506005802c0780d99440c0021015842d000c402c42d00c034440a85801024502c4034458917124049808110402c8506800d128404840d80d00c011803c898040c0c1e01c4450000060081e08520000d102c0038003226103551074806018105204c03a0307464804821003003c1031005a81d0709108400c0d8640502d403811110b6403801c0145c5514039640c2100307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97912976 1250 97911726 97911767
    0x903050f03040302040c0c1e080409020c070801060504020f1b150103030c06060501030b010e0105180d0f0c050102011118030c12011d07050a0326040f09050f0103170703 74
    0x340900c5000001001280d100b03035010409581c1c180e078200e41e54050351100506058482d4188841f0140c4139001d03000060165503400e02d020341c1c4100e51012a8801c0a25030340c2a0004c0c01c0400c00c81c20284076010007820190790640c0307084140c0c803d040007441404030111080c04039000700c0030324a9040006034603225850007010003a584a06016044040b00241240c00500301500811a54070a010700305641c0030603154500c00e1100140191041e400154040c24206500b00000c44140e4804090400ca0390192404070035105a904105894516036000b6a06580c10514444003d000714030450345c0c4045107001030302000f520800000c0c10000b148021076801030303d4a200c01c81c07540341940200c4c0e1407100200459030808a015445d91070b41200c2c4103035544120410030400104004031001000b54041200b210f10030305111a05840355007040d0850118888003c0e41844001821300c0361070341000c0d08481c0c1e6111589190760386810b03106104515031104a020404d1001c150141b4541102c0c8801940403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97914226 1250 97912976 97912993
    0x10090303060509130309060c03020f07060509030601060e0306151f050418050f0708090703171b030c120a050409050c0706051303021c05091f02010f140109090201090305 74
    0x10040c01403409114801c00c400c83c0450301103c039003040f0100407607258a40c030000d18176041c0151442170070784100303806600580c0b1008030004401c0c00780d50b010744130f10346a26881d80c0d14102030502d0240705802c428240315422080c41c01a540005402d43c1c0400302e0301602c48075010104c00b0510201080d006000400010b072010191a40c0100180007a2500c2c81004ad0408602c0c0c140300e000c0c0c2c4d40c19249500d03540301490211782254800d03900340da0700c03100d01e6049400d002d90741e95804449001070040e1584030a80490024441c0362212210f4944490110086090403c0d02400b551074011084800030401c40c00244061007901a005640044c02c007031508200d01e142c410750941e9a07500204045030b00614020011340400080f407080c03540513806600420b5641107030100d40403841b001e41124018441c0901c0364800c00d07900c2d0060122200454814800c10f90019080070f400d4a59181807880c1e02d03414500c001d001c0000b003000c02c03411240c040c14003003680a40c40c00140d4403e4025000580300d0f01400c8039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97915476 1250 97914226 97914233
    0x20105010519030206030a0e0111040e04020901092a0915050d0c0203160602090406090515030c030f030f030c0f04030b040c14060405060304170301080c0f0406080d0f021009 76
    0x1a40c12284240c1c2c2101034080701c0500d9003039811090000950186041c030209041450742ea0000100c0703082e8500005002140110506142e04190b006059440b4030b003003040218103250340c032103004194540c4103112503500c0f0120203254002e076103082440c1895020341da480d685c2c826800c94000700041203000134444003100005042d51301c5030501900e45400d00d01440b03c0d0074400800c81d40d42401d10f0b2040a401e4902e565030402a41c40039140a90050303d4810200e1007120134425a170081e04407032401d600c00100c260505042055040d401c034403981010740b80c42d41234500482100d55000943c4c200b1a49c0e551040328420381802081200301c0d10380b102040200030046203a012502a0f40a14510714000f40d580d07000d800120017107000d80c0c1d0092811701080080c1d00b421005190000d21841c80d260340380e00210041003a80c6c1099200c05111313030000840c15814117200300cac82000940192000e0202c0c50500c01003640d02c0b4030305107000d01044803140460080034424410304030341b00343c240c030140008186800d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97916726 1250 97915476 97915481
    0x3010902150a03060f0501091701020c010c030203040b06150306040b120d05070311010209010c0605041e0c14010201020f040302090c07050607030203010504111c050c09030f0a051227011e0201 84
    0x2c0c11000ca0310f05940410402800c19202e021500f05075103c203444c504000c3c031039180c400011403c611564080c0080d00e500c0500b0b008081c0000c01d036a400603101d1600b4102034094000c040c011600404440e03c0040c14101c007107003142c1c0d012409580101e000403140c008501d03040d6803500d02010302d024441f8814440e17540300e401001064041c2c3d8031054440c4011082031300300d11030100d40b140480d41c0402d07140c1c00666207410443e80f00e401030003611543c4107500b001c0043c414030038000310703100a820501808540c0704405404045002840210304103407480b8403c001d20300c901d0101903c00c40303510340001c4607002c0c100700b103501c0e103a41b11055410302d080040014004e1740081c0513141c8192b0410900081c90b440ca102600c030402c140504190300c1580240c9070320000c043c054000d08010030100126511600c040050050780c640e001e00070082c41540341016810849075020440c0114001c100c1043c82d03060b2080c001408101501c88208201140d90050b124689030000951450207000340c510340c2c0c1501076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97917976 1250 97916726 97916737
    0x307030807080c070f0b03011802090301020712030f0204030c030206030604110a0e1005160b0613142e0b0c010f2a050c030a08130605010803040603060b130902090301090215 76
    0x40e049628194480410342034010550241c070321500700c18001080300c2a40600d980501c03040271400140781c0000390b400300342603a020f088192280c1d05e01c040f006510b19818882d80c0098062000110b00b0903056945d003410804862001130b02c2048088046001c9582d564000c115881000031150342c0d5001c41c503005042c41c2e4540113040d102e607001044c4000b000d8003400450b01420140b8590428414440d607422406d107001a200c0380d0480d01515018442c4900b44c4162503810501d08100443c0d0302d089075076643d0f86104a8145482c644443d5002296902501d8060003910f0205240d1503c3d100e03015051070040c00110b0100f001503040c60604542c0c04921600150740c00490b400c82040d10b8034011301510756214242071102981e00411003c011503115401050300504400700c2d10505022a0311440c06954080c1c01c1001c0c1c40d0030000d81006080e4151107210001d0040c400c4083c2005600c050f003130300044292040d005207603000500e940c030320b036000e40c0503800d901d900901d120fa5070f401c500140510b0782c014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97919226 1250 97917976 97917997
    0x12120f0105030a11060a180f030615030f0206160602120403030c0c0305030a0e071a19020f0a110d0605040804050316080604030f021c0c120305150103020306030703080708 75
    0x5a000890241400310380292282d4000c0b401481d00e603240c1c0b0900c01e503544078080d1042000305801164040100301d6600000802c000d050441a480c1182000360440b0717070000c030010407a21404800c0000521055405030500c0c0c04407112521170301c0a400c100c0b0b00390b0400720001c226a2000480308a4500201141b600641c0686d404104004815038141d4240c02c92400140c0452428400980406d074281c0101002c0d146900944245a649850990408080740b00e050000c004c003248400240c19100d140f1410640715200405820311b9005ca501e880d1010824082e00005229588040c1515006504014142c3c480c03c1007110303180601b4034504903040b50207403e119000e41801407100310440e160200036121100054809500e5a55090f980b8039829840d5000303501030b500c11040c0114801480d8810440252901e0000c0c80341858401c0040703044a107000b09240c0340c94240803005c88840403156602d41e0a080040e41c0382c85010000340f0301046540700031b18944d0000380040c1000030703e4024001e00ca1230b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97920476 1250 97919226 97919251
    0x8120a09060e0a0902090102030408030c0a120c0c0e060604080307120306060c0b0609060d05062508011805091c12050a0b03060a0504060b0a0b070201020607030e0a060e1212 76
    0x31201e204a03401c810618000780c0c001c003001420f200450f00d56000308000303138050040f02c2c900303030781c850106040d60401012840c4070380147e40040705100692080524482d12440c00044e00c0c011555000b0408400c1d00a810300d0b01074040c0007480c142c490100b140c02030040d000c00c4a86418aa28040340e52083c1480070000090030010002001805090341400c51070740810750512a0781c506003440718000008000941c0300d01c500206001045040c402c0303c0c0126903982c0910302c040d520810342104580051482010462000010800003210784083c41c02c01d203600c2404542e0b5214402c040342740040b030241000d1009103818036684001e07041910099100d04425040c8229501c081c0400111081990300540641100000880b0341c20a58407055026105100000c0c1050031000411020342498100c800b6219001440400795a010014194011803a14042c0320107010480c03c00c0d103610305540000d00c49030b10b0721b042c808481d10512440720800c0303d850006407140580d900e4002c02140655070100400e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97921726 1250 97920476 97920479
    0xc16050306090a0f060b04060e011505071a090c06030705090103060801060b03060d1403030a0c030b0d030e0f04060806070804140304050306060607050c0a0b03060307050a05031203090708120a09 85
    0x5020501d948150701d00006044010090786900440380301c0c010f0111100c0e503803001268002c3da501d100399000b90520b100c02128075818449114800100c1000140a200e018010640041c4018601c6600d4181001b040c1549850360303544a031410040c1d4032040e2740101d0101c10440c5495011014206a0100743d809002d0380d555450002e00700c880a00426000350030400000d020360030605451411076126400f850a841c0c0c10b0741e0400c1c2590000e458452100307032111555402c141d0b150054111414007200c4c3d1000401d400c0c3d502a1144000c20301c0c01c1c0c06441c60102d8030070781c0d94030f6611540090402a0a4980c1464420801000c10740c08403001c4801c8211480c048406200010580d820340d44050010203490300c03070004018054100352000c4401d44281c280d8051542c03200079441008281c500e08080e107a00303142d0101400d01c074458020b075005d040c0d40c0b5000c0005039800101d01d00c65203003c2400315500c1c0c469055084c1020343d560440011403090030034900c100c030440d000a102c0c25003117641d50710b0071b039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97922976 1250 97921726 97921729
    0x1e0c150901110309070303030c111902010f1106010e06010309020a0e07110304140405041e03212310080a0b01060f1106060f03071a07020a050102010204030203060a0203060a0b0c1605 80
    0x83c0000d41c0d401303440764000c0d142071000902070350040d009180507007000f0440c0c09061569600c0d021a100545050b5640b04922a04650b0401c4a0003480007030340c1040000c0c800c441502c01d80c3c900d0140301e00712540f10340e48007194803a40240e03c07101d103035500070b0700400d80a0b03103900c40d000040805550081c0000c1e500c0110910030034011040c1e40560352640051810f0000140c01c100c09400301070000d0380c5001c41820000c0301da241404984c0a441c2c441d85401980c03d1007118500b198503900455405043d090036000e519411b0412022044032064500e80d23602030303c4012040801543c5600480ea02d0b1084001400610068800301c2e4102c030010303a504092082c945000f11601d00c07250806072141c3d800074010402e10324001072050300e40c10019084651007965035490402181e01082c1a4221100000321071040d81800c00c442c00103460203000941ca040d1859002c130313a40750001064003801a50200100790b40795900880e000003451000304041d120980c1e0740c20540c40c0d002d00d0b40302618058601d200090035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97924226 1250 97922976 97923011
    0x703050613020d060b0a09020301140103110f0406140d06060507120c0b06010c2105040807050306040f03080405010603020301050a0e011a030d11070f06021609111e0c150901 76
    0x2500d50203060703190050388960340c030340c003804c05e0036516070303001e0601c10000c12842c9052018500070464144a01010358000c00094122940302000d0380c84c1840400c03c120300084408101e80c100c44a07071070003020191000c00170a401d402040541943c02c0e040c41c9000400552100c083c006031801350040461302d11283c3c1d01034407040b40c2e0300300c024180c1d14520000382d16503010f031a034082018080c02c0703a0000040105441104001032821480c0400c6012505228a000c10000903000d044e056006058508298032684085008030341e00400b04032458000404201082d04030380c00450b40078009024074200301202c1001f41202094860b065171800060303008000381d01400980c20740000e4083e10085c8909001241c0404055040a5262045120000e20640d100100c00c004100b035502402ca4600344000e0303140c1d000d00380e60040340890b05060002e00c01e82000000c4401c442c0c01c00c542d9419044000d143d18143e4080c080c0030a140d40609803080d46018290500540b2441c0640000c002d141d2140d02d00140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97925476 1250 97924226 97924261
    0x207090b10030b01020f010501030506071701140d0302031624050f0601080a02040f0e070809063c150a050301060602060c0703031d100c050a0f0311040b0c07030506 72
    0x901032030448510740c1003030003684690300b625010700c16100403052400249003540c1c400e9001300c40c0c6a201c0b2040003601c540c8400c1450840110b940d0160995151024507002e40340c2600c0030a10a442c81c42000d003c041c0200700701c8401c01106108a4500046401d01c1300418071180c1b02c4c070340760300f000001c640e0042c14244126442150750490207100e0381c0f568401141d00c00c0008103036000195081001107070701d01c0075041882c02460341c151401103618003a4001800c0e03003405000000c031603000e9005d0000c0f9185006514030688800d072125466403008421040521080f580305040681c070070002c0c0001c00a072040c400b003000f40240c1c0c08550140c0d594041c58200c41c85417181d80c00507005000440d4051040b0f40003007121902070b203008100800510400c62403000900c6400009a114210940444649008504042100781051818254280c4026020720100d10781c003020140d032440b0b181c0c002c2000c54141e03400391142c5000c0a032640a114062550350025010a99840c86090000380704840340000c40750 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97926726 1250 97925476 97925479
    0xe01080c0609030a060c050c0a0c1401050316050307120507080601020c030606100c0609021002061015091e1502280c030b092e0506030601051005180409030806010207090b 75
    0x8181310890703c0303800013840e810b1146020044108078401c4412410409951154041c4619844d40c0d03107400c01102508400b48103c9041c010244100080590516040031002d0800e08004ae9a603450540865103203280b00c1c4001e1140f0700c0d010501c11000d904c113a91503c140030a0b001c99036a1040c16007016642c82003151115400a2891088900244210060550b0922861011814842c9540040e164844014010f40140d2040c001c000380407042c0c46800c0b00034a083c640944001c1c0000038002c1c00d4025900904254191094814804a100e412030000030280c4c0d15010862505010b802521545038203441080e80e801c1c45a040305a039158801d2080603a8409c1080700d09074610307640c0016201004180d1446400390314500400c0c0810918414072811011030817000d0345803400740724002c44d40c010307004a000c1d80c00a030060206840303002c00381040030400e082103a2541e101694040c200c49038580c45c10703001400d010018041581201c40c40740201d070f0913000c0d1841c960300d03442030500306d0f401101c10320b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97927976 1250 97926726 97926733
    0x20c040603050303060d050a0203030307020c090c0c0309010c300f02010501050d0f0503120a0516080f150a2606090307050c0108040201050d18020406150504090c0207030506010e01080c060903 84
    0x1350702c03880c2c05c10703c40d80060710030070540d41008d58540009040d50400c840b60000b40e040b1000844441c03510f404516800700e40c1c551094141004101c03119607a00520350700c1030501100e041003005000d001c90b80780d015044000c44650a02c1101d190300501807032014440004030b04400c0e2200d0043d07006000d051b060314009080c4031003090580d2120b40610200d83c1007510140000c00034040003841c800340b49031080d91032160100305810b281031201d15848003008070030f041104801c1444655100c65820b1600081c6490301c1941800307076039000654400c82d90344900f45500c0c03082d503c0d448518100440d90007142c0322600741e4802d80e40d50b892094403841045001085500002d1101c00b581d802910f14503002401071400318142100d0000b40022212200c545009903080004c200b411440c15000f218050305e195004a4545001140003034614052805100442901c0300900e10f00d0314820070a5200558100c000c403007031540d6402c0004030410081c05048030303a0260300140030641c00c01000300d41403008040c009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97929226 1250 97927976 97927981
    0x10e0a030c020f04020f0310030c09020c0a0213021306020114011a0304060e030915131509180f051e0c030106051206010309080c01150e060306010506030c07060f0c020c040603050303 80
    0xb0040b159103403c406962059013031080004141c8000c01542c45114401659180c0c54214280f900305088680d018298aa00411070507803004004104014005c0c1e064800400c03a1280054003006400303520003120036580d808000084295054000a29040901000c60314507622041c1802e0303801003007a9030422102080011500003403d5a0140480c101da020a40e800c0c001003a00003681281004c810340380c1d080010802d40c41c11a8000078130300081c402405c004409281098019108045512030000c030f10150000c9043d02105541000300a044010030030040381c540361001117a1108802184403100085400041c000b02c41c074401c8034142c4800d500c50070b0400030301290700f50042038000d2017203041540ba11181070020300168080c020054035880082210600d28035002d092a0450380042070310b1901c40c0a00449440200e00c450556100703861650340e035580d4446001e894854480002d00d410b10b01520143d0507507040e40721901240f0554252415044003500300000e17106203005c041e006070403c102 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97930476 1250 97929226 97929229
    0x30106051210050a0608040210030506090601050c010b0301051e01060302071a0603190311010b010507020d080903031605010b04050610090e07090f03080c0d020304060206011a0706090311010e0a030c02 88
    0x511542c00034424165500c031a8498000c600d01d85459031002c804036695105000c11442c0c01c026a038002d00c960300e4100414580100002c41d03a1801070009410700200240d600000306080d00840b0302c220001e8024031084c1420140b23140214103031038030030400b20604000412203038424001c40380304e560010b04c180300c40103c1046008a4000c041e24641c1d2601c80e02032500c5554848010708050b0501a403145d4554401440905003510701503064641040350400940d001a0ba50504c030034107941e0404003a83d1030b19200004240f5504c50740700c0326240f11420368511000c01205400207107404006803014880d1b5110704050214000e040340b148000b103812044144518000800b00d1a4400d01520309010b90f40d5031007a4018081d00c1e0780e041039940c2c102c005090700e02d950040110000014181c401503151501c0c00e4170094507100107000d092500d040910758007820079100c100f40e40d81180c1101c010411902d00e1b00c0d018190780c0f85011081c50550030700f00ca60308400c0d408074040080f00d4258680c0401c414880d0b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97931726 1250 97930476 97930507
    0x114090415030b04050c0f0312030c0d021201082a011704110d0f2303070305090109150201090c050402030108030a0e03010f0c0206040506060a0308180102010b03010c020a030305060603010605 84
    0x70406207200414060010108075241c003018003403801000680f180c40c0500701442640741450410301e020358442040740400c00001e90441b54003000c1c1c5c0d4030b01030300c40c00c100c00c100029100d401081d2603109105000401c1d580d80200d0400402c04929425040c05c65400e19034020714010304003403502040403240404001c0c030f8510860383d8864890280c50448060307143c001115000121403d503860080003518604101414086014400100c40f8400000c1910460a0b98901c10240028100100030078510a541d019112450140603040c40d0820307034000600c4000e008004102068034000054030f000070b01d0f410725200322030603506400041c51422034a480d050711303c00031804030780750190760320034074070205c21400d105281040300c0940c0601f00c0c9051a041007481c0c0540540071602c2407508040800003d4001d400703d0350040152131110040f00c41c40b00c0142d00400080071301d00d82650a0010280203542d0101c2d810040714800d440810481d1508000d1020394002401440302083c0d04018000c0034401c1207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97932976 1250 97931726 97931741
    0x2120f070c030210090302040f060503060c0c070b030109020d05060f01050d020a0203041802210c070f081204110a06031505010503060604080304240804030c110411030f070e01140904 80
    0x1264448001d5a8940c003182d01080d2141c1601c000450900003403085244c280940b401c4174074801e80038040f1500b0070000a440707480180143d0800c00d00007445100d00f010502801c1e0017050400c40c0e070b54603580d4402c10f81010394000d0382050000c0d842e00d0000303035462505c000241e100c02c04c183e50b01c608040c0e02080c01802544495541015403206210014020010003800c03900580c4554025898140c140c0d803c00d29903203800700f21080c00f03208030b040001c500c60000548001a4000c00801660314050920310580d00c07484e144900780c1c0f02d01000304821301c0003001d100c5806010540308460200d03500d160031401c541d002c55860024a504210400a561081d4055a0000d82c001c200c2494284e4420069155034002d5008142207c0c0f60511f8000e400c4080c00180440a9142041e822030310b0165030003403481c101c04d400200340019255068050380c84582c85170891074545d8100315034078140414001030302001142ca02c4001390b104c21040742e0f5944a041041c042030301005501d82401d0340d4104110142012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97934226 1250 97932976 97932983
    0xe0705040e010e011b03060515030a02091c0b01150c0203120c01060b0403031101050703060302180405010b1003060503061f0603021c05042604050a17010e16090c02120f07 75
    0x2038107500180f8000138824080c00074a00010b091180d50300c010041c064541d80da200c40d2040a4551007240310f2051501129072221030040d00503620f0b050203000414100e881d80b000d1040b10740a46407142040006042c00d03041e90804d0f1a14881c0f1a0b4840f01114913842040001390542c00403681201d0348440ca401a0080c9039000b400416501e85558a48007541c000c1c0d8415400904c5d40200000c41c2030703081c49216088046407400b44542030035600440c051301031214100c540c0150103c00107040c0002944408003803603004058000b44810703814001c000d8440c1d40a440e00c2030203500040350340d41c0103010703c007040c0c15120a411000c135440d12205170020741103180c04600b500d00240b019101d00300c0b9031007a18030903842080c54608a640301000800141c5000110794000702e4204005e2069a50714402c40084425018800d00d800c0c04e80284a4098400012030700b50620441c0c4c146115811480c03c03e209480103840d00304000e2024241c1281e40300380d004a08407841c00c0c00c00460f625002c0020040c40c00901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97935476 1250 97934226 97934231
    0x70203010e0f1524270903070303110711100c020d0822030302030915070212150907031e030309051501140a0509070305190903120f0e0705040e01 64
    0x4101c94505010008140c02280c0e00220100d041001c80119007580120614001e40c5911035034034603032031040303403500341c12489913100e40c03000c454120407240c054510516024007951542040c108043d600c2e00900030072000f02e4140000c0708004002740c400d80380d801e50044841c2c200f500f8800b09011640d05864205002c02400180c4440561501c0200c4e070006403082103020394a1610a0140301d2000e84402e045c200c0f00c00300e503001c0010036030020a031402c80f40d0072540418040c00034a4914040c0c41404e500035007040021195505142002c21030348403044154030000100d07550014540d45a0b091400014803020f08001080110f0750180f07088446684070b818005200d0940d522031500c1c00c3d1911521102d102541c40061081c040d290600d01da0015042d58400758036400c01e80010500d25006250f0f80805a844000400210503451142140c003200503040014115a040007803402c0b21b00b160290460b410010201905805445a5800f810880c40584080c0e420203003000090840301c0d030012015034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97936726 1250 97935476 97935491
    0xf220501020c100506060a020601090b030703140a050606010c08030a0207020d060509010606021e0705090915040305070c1409070806040b0301060803030417131205191103010e03030c09010507020301 87
    0x108248000c054084150006001c510360724283d00c01034030402400c90380298024001460010703000645607054601101c00465101010400310b45083c0d41640081c0001000303909106034a1404204100401d002d1000d44005a03609801901c401e03001007170040540c5420400940840a00d9001d003070402d100400c01d074041d030310f2901c070581541c5040d5480c100c40e03591058100300c1e01e5010020300402c45aa0300c900d6480000240d411a105c0041c2c0c07040c80c1c014510400040c80c0070005010150850165003c0100a82801e0400030815000084226014092640042070801142000b003400040040001c0d0266580c100101c465903030140600b070b00982caa00038031607680da003070040740050b040c24001141c8a1400c0e040005c0c1800640c091004400001c1110251604c0e48501d07080a0365660311240503100f02c0ea14215281142c0d034403030b801985545980f4241040542c186842540700c00314020321000d060068415100c1c07000351803a21070108200040b10070f65000308040e1040e43d00090000038103e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97937976 1250 97936726 97936733
    0x190206040306021b01061703160816050304060e010201021215010c02100f0314060a260303182e0e0c040513031b050a02011419090603060b030f22 64
    0x90300084014484c0c8582031208080d1904244101c000404c00d80309440d00442086000e02d48904c5110017190030b4141c00c03070781001400301da48100c0f0090498000001c01c1840b02d170919030327281d80241c0100710014442003060304a41d8414020341d04da05a803617840c0c3d68192111101c00c2c64840c400032040d81402100c11a680140e59104c9000120710980d8803100300b5100b01700002411660780a98140700000503409015080d15440010b10036201001100080b2100c0b1000501582c0700000410b03041e44000410001450900280d040c46080700c5012a400b09048151000305058020143c10050200804600c2161115082404212610f000b030300c2810003080b01203000c0c1c840850304071b0714a0001248880c1050760008650021122000701c0340c0c0ba0658503900c0e2600c4184090f0064104800c149548589000e00011150b000a00030b5481c0b06011030030740042c00132041c501c80d083c0480d10305a00041d000040d001281c1c0706043d20a040780143c0d071340100155040744044d03080001c5205403030700300000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97939226 1250 97937976 97937981
    0xd0926100c050c010606030e0a030804020d080409150801020c100f14010e1f0608010614090909101a13020a09050d0b0a1b0c021e03100203041112190206040306 70
    0x60000c1c81d982c0a50760480b41091909644140e8001d804151405e60b01140c1810003060b540c50741039151811052640380d030b00006c0c1c00709141c84009007144000040c00244003000d5031184e44114455040c0580c00340c0d8542420313082740640d00d210520764104031038008201903140e10048a0b4841e800d000555141040c0c14102c2021098118030b940310103010034408003881c81d0038a10200312902820060150038140024100c1e041885040c00b48009040310a0445500c1030540b0345404020703002c0740315440e040005c6a40c61020b015940f411a24100002820b040c00c0c00c03031b068a0b09405082011000010325562000b50701c10303c001d40412042d0341c000718555640300344031102c060250928440b2410860000300440303550b80100d080e49181d0b00340b51750f111500501c0480115070116840c003403603004000e83d042e54180c1c4c40e5040d681405212213086401d281a800780d40980e024014410703110349030b641407200441c0d032454042c00795441584415405400d0061306c4445901c05440c03d800c1580c0c0c2e580c0c5106 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97940476 1250 97939226 97939241
    0x10f030b1f0513050d15090303090f08191b020609030304030b090a150501150c0204090c0602010f06090b03070b130e0a02070201020c01022a010203070b0a020c0d092610 74
    0xb0000624408900700840078540a88001c0381c1c0e95050904554501041c0d07141658160340c81520b500406050500903444062000c0c2c11105980c002009483c01103450f40c001c44060303450307200c0f07207000b4100a84203c8051220200298030b04e1040145502042030b103401c51580c1c19418030042001200090140400d580100c1a40d40208080f6240340340000007000103600781c0014a00e40700040040c08108400040c030b640d40380c01c00882000f52400850003800c0c9a0f2806064011020340c0028a0ba07815400280040c0c540c00c000c014103915070070b4500035180c1c5c0304801c59059120205c20702400d4401d0703004008400321803001d80561030340c84c410000018000c961001a01e5070114840c007d558040c00b50a161308824805820005000350203203041104250340d45804612079185000f82c1d9000300110349143d82c000d128484c941c07070f1011140000c0e501641a822850181602c1007141c0e83c0586150420b6070b00c101540c003142140c070705e0f074103041020b18403001182e44505a00c0c8542d842c96841500d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97941726 1250 97940476 97940539
    0xb2b0c0908070b1309051909030e15030c070b10030606121a280b030a060603050111070b040201030b0103090b0a050702010c050f09090411060c010506030c0609010f030b 74
    0x4545840c1c194440d092000380da010098021041042c8800591000c0750707542542c0e100340c0d0006050f26a04106072800b0703039102c6d10000c020728203480d04040c160000e059040c100030450b070800c0304038035240c540c1005010a90314a0a600b03001c0c0310030f1001511301032216034401003034010001200d13926140c8105031115644203010210140071a0000e20a2903400184407080c05a0344214a040c004140601e07030104100c400420036038110000c00d117690640108454100c010100c501e02e09540c1413107001007029200444031796181c0217480441c5120802529101504565280582c0c0e0741e94005602412107900200d04169803503007800c0009414a402d81e0045040c180001124600a60040c0c212241c0842010511134203010740812025104116600e030002914041203507112454800c0c5400c0c02400b946a000780e000c210740042e0307081540124411036046084a41d00c902d90f40a000715440780c101c1e17250002d800e4105051100340241c00425004001034018075100502c0076484009500c001c1002 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97942976 1250 97941726 97941737
    0xa2003030a030b0f09042102010e07060908160806070c0507150c0b010f050a09020f0f04170d082e050405100303090f08031c3c05010b2b0c 61
    0x49050b061500c1045410001074034080c11901b096121207448582c0c40884e19501100943d6400c0c00740e200b07401030791690b400d400844500c562541c0000e0400c8032a4010079501c0d2090402e110000303005a11203100300d604041c062b10007510759080c00c442d603031400b1000751400c0c4140c2c1d03400640380c10140c504203030703003001951407020350026807414480e288810790003038481c21070089091005541c0c80400c2002c81d600140300603511043c0d00c0039040607001d0109540305140010a00150342c1c012159550442d80901082c0c0d103072248180c42c15101060241c4079000041d02d000103a08401c0c0300c0714880c512000c0300034808603900780d64400190540d0401c40c1c220150f0343c400d2000f001019044001c060143c8000c02141070040d0402c204a0741d00d00a814041d0f218007203030074038400d852072603600c24941181404030300100003210010b102414102d000c0e80d40c0d440c856104c0694807810703a622031a410b03102c1e400360301c43c500710311861046840c088036020907082c51185c068045003060329120311040b9180a0b145c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97944226 1250 97942976 97942991
    0x120c06060b0a03050f0f060f0418020307120507080313060e0105160c09060905092508060405030a080c0c10020906090a0e0a0b010c030203070215040b0d051602010606020a2003030a03 80
    0x105c4021001e0700c488180030014050040c4c5a8908131030f0881c0c2c20041d1400a036000c2c14110382e103462090840b010b074050082401c00f003803c0c503020058058181c06601107518203941d41000540c1c0f8481d0841d0781901c04100007081c000c1d64441c58070a4200d041c145015400c101c520b000860402080c0401194501c040d1a01040103500a02580b80101041c0c4400c02c41450403041c070075140c0322940000002d500848040010300106403605c640a0a035140449032603203018034110b80d40c6c3c0e2080c1d440b403001c505107400080a640c0c01034100d50315585081d004e0280e0100a0078070380065040040c001c0d6020005011441107601c510001600030007100703056850b00d0070801c2c034240c1140c10180c1154100701241c07110b42c020a400008440b800c0d035041d100c00d40038000740741d66551507014917084120034000000726034802c640580c120714003680128400344c50b102d48031031050382280d445100b19409a00030512003c0460750f03540350010070030580c51030b0107404902100080d056030300030180c070b02c0402e81d942c20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97945476 1250 97944226 97944241
    0x40201170f040c0b040e040822080a0c0504051510050f0a0519260601050712030c02070e06030a0b0606041e030b072a050a0501050a09050f010603120c06060b0a0305 72
    0x75010000e06030300203264a800d046c80c44095500c0d00003880038085500010b910550804501e0002c944030103807130300c00c0c00c245484400300c6446080e600e8007a50001c003a4000401c65213080e03c42c440c0105480c02d419114050300030140a201c500034520141407140900c24211940318136401000b144000d695099650008020700000280030091550200124001020200e140610b180c00705280c1c000c3e0341001e280e981c0307001241c503803098440050100c88924402030107603405070000d0b83d040009070296110103840e0b600c0000010412905c60f0761503403001c2101d2000c86c404041140d003080c0041d225915252711500405101980b80000094204a1401c1042440f040c2d010b5180c0010013440c1451300e00c1e0003246e00ba080c2203085403e000194001000040800104102044186911000900c045d1514480c40002803181d280243c540b4024403904215610040c440c15059070381c010421100c00910060850781070141502c101c80c04c90b542d01c8003084502040c0c019000c04a9590340c0800d40345000503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97946726 1250 97945476 97945493
    0x610030302100b012304050a03031119030807030e0a050607020303090f06060604030201081320010f1404030b040305161101030606170a020d0609020f0d050907120209040201170f04 79
    0x1c1c454a50b00307240000d0700c92582c0c2e02030743d0a5410f2101120070300d1810104408a40c80d4461607000da54012500381c0000300700758000c030070000ca4201103030644825500b141e1fa940100301490740004d000030342d404000f895480c0030b41e1006e08a80c1e100001c90b1100d010b40d40d02c01e4600742080d10301c0c0c005a8008000c205c01c040c0100305901610356104050409400d11502040d440e0043d40002070505c40541c0000310180c01e02c00b0410301040d000181c0e03820303500300380002a00b40082072002c03034006413050f061000643d001c2c034807525540c45030004903440c040c039503180d600c91428090400c808010301000945280d080303914045a0050154000c0c00082107104005002c43e11950702990a20000f0101e40101c0d420402d249680158200800359a8400303402d80100140440e80004c1c40300c80c804280d4000035806480603000d507082c0c45600700710b01d8907030116030f03561204180b04011207590300c14030800040c10041c40a80c2c0162040c1044031032890800403200b51070782c04562401c20804a00c080106009001d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97947976 1250 97946726 97946743
    0xc240207122d03030c03050c0a08040215070203030a090905060d0b070e0303040f0b0309010501050108011a0c0c0901120312050c090603040f020d0b040606051e010305060d050610030302 81
    0x1800184480c0d85044000380d604603103004090407000050a42240181d030b400c080c100800e81406804481c510345180103002042402d00d2940068034100c001910151900c0442d11b882d00300e41c54080321552036a082141102e403031a10b0030b400220510041b401030b01c040025181c0c0840d2601c0d003401c400c1c24030640c0f40845100a00c00c601c0346e00403030758480101301324060080d0013880601c3d065022524000110b45035200355444004417802c6500c0c001022410078016502403541a0000d10059030303601c1c01100c0104003805110307800c42c2000b00b070403104031814000f05182d040c003805807140003041000140b81c02400341c0c00f82c1c8601401e09048c0c010540d00c031664140c440d040c000c0401140c01d203040d07810b109018403c401801203000101150500c005e40217616012903008010841c5410305180068986a080e0742c203c0700d1600706103001c0741c140703801c901c604286000c7c01410f40c01010a41c0045019190142c0080d8220034170a410070040384091107503a110b644122802012545545002840d04108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97949226 1250 97947976 97948049
    0x4030909050a0501060e21031611060306031c0306031e050f0a111207090e0706020d03060518060402090d121101060e0114060c0d020c0a0b0c0c1302070c 67
    0x30a401485029004405911a14400d580300b441a1442d12180d06014005411251032884042040321010300203442c0f6003009c1c0c1c86642c0101c0740010380c4080c44042c7c0003d07100a54150405500c40b00f4070340d02000348a092102e580343c0412402e59a8503811148409900c2580208080000050074807100308203501401c2c142600400748214640c6949009407616802a0320803a4031b507021001d0b01c2d40410106000d84034417134080007040360a120050740c2c0c0380640300b0f00000d03014655040414902038403c010840b04082d003021406050071403003107010381e80289102d034010340c00c1c001c034819600c401d440628242d1250015144100f0781c01400342510805800000381c80c0c0c18500c00b07010780c0d000c1c02101411100c0d8040615845000d20740041e41310302404090614a210340304d40b83c0545540003800c004064419501d900d0625180c082d4001a13200300f03003042540d41c0c07003618200c40c41d0410b01a000045914500018145a0b02d80d40c0c402d0b01c1c40300d0741e1140800003444403041070301802d00551202e56920 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97950476 1250 97949226 97949231
    0x6030e0a200111030310050f010f0207090b040f020c01090b10180e0a0503130e130816050c060403080d060806040201140d02070c061e030b2b020904030909050a 70
    0x16076128400996107196060318003040000016080c1d0060400d014400500c50a503602c81c50500c002d8080600759114280c03103082403041c1c21030954014644040309a43c3e541c0a403014a01701448200901010040c8903081b9558610a08002c00188058030418020781d0000c1020056400c1006080360040c200506149800b00f007041405550b10f801083c00701265804580540c44a00d4941801036002c03000d019400005206a084480140705000f134820180c000102d54480001c0d010030300400b02401440c40c41708200c1c000084c00703660f1540700340c1e030311403003c0f18100b001040101e00c1c0c070b030040e80c01121640c002003410f4920308981c0c05450050007050004081d64a00340d00020711340803080180444d01d07900040c1112a0035916011241d07090b40000003045c1960780c602c0000d003121000000c0c03891034460740100700d003494801d0081002040004000c0c4000070005408410758100784d44205036030040c12101400183c41e404961445203010f500c58100c0b042c580003003a0300340e89004045403043c51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97951726 1250 97950476 97950493
    0xa0b0a050a0c030b0609090405030405090c1201091b030e07080d020705040e0a02010c03050f09061207020c0a0e061009031205070212030c0a1403090414061206090c010c0512070302010606030e 84
    0x449030415642c0c280402c40d1402c4031f40d00c940c103142c2e08510480c0c00c02030f0081100c0c010002c06200d600010130000d418651400f41300c0e0307600d07402d003011950f0403c03e804050031800f6007924118420341003140c0c003054600a0741e05c0c00d07070307220801843c04617281003001c0982c0002e10704101919240c0705070039001c42008040c180c4110241e00080c401d810458004040c81004105820000b089606075054840090161540c82980038103001d5000b01c102c861400601c50070010700b0f03040c01d0007041c800c01c0f18603d10745001241c60b450104444200e0001c0b1640400c414604000080703240d0680000c0c401450b51101a500d0980d80180100c01c40c44032048030b800c0e80200a0f850138108000748040d09141c0001100c02180103001849007544202a0015403260400820701200c002c902251070003035008444442104403c5042c040d220b0500704e4688500f03803c0003100140c03071750140034441c400d24822800c1d0380305420801c0c0300082b02c1c0c018170810340050f0355400d000c2c003496806103d182d018400800003400082c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97952976 1250 97951726 97951729
    0x506040b0d0b0a0c0903050307030504030b1515090105070807120801060c0b061005070204050a1d1605090402030102070203060f100608160c0c05040c12050c04150807020a0b0a050a0c030b 82
    0xa003000303003400360040e6540003400c004a1141c031707160000c1c650010543e0b540340042c0c01c0003055508240000d48001d41c0a4010071030424001c8544282160054555080c0016007600e4070b0321600100c112905104042220100003007044c4001e0580c50310512640c41c400120070341c000c1942c2016040078040c05030300914000072800c00c1a21590080040301c94629000107900300302e5540c06208030094209040805000c0c80340010303045241480c000080b06401800e4600c207843c0c0e03400906a107003035a4078945030180580c1c11701311412540680003500251400c03800703a0100b440c02000b11a8010071b080d004d020301900004541e1100000d004901d09a0482e05010032104d0140e41e0f207440c40018040b1000240080001c400c056500425006008102a4500c01800b41c0f214100c00b2001136094501000602174140d00000c0d54169007940601904400c0710b0709040d110140050001410751140400d040d000501e14000c80e071181103c0c00022807a82400391440040c1c4420350804014541050b8181c56107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97954226 1250 97952976 97952993
    0x12030506090424020f030601020615010c08090406030f05060711060402011b14120903010f090c0605070f12030f0c0f02120703180602151005060412031b0302010506040b0d 75
    0x43d400000070343d0300301c103d4507148050a160100c3e46201e14008140070301200c0800707014502c245c0081e001da500340c0c2c3e40d451f501c00c4c0e150030405100d0f02150f01e6526400120700c1081c068194160301810019401e503da454801804041c1d00c0e084400d588420100300100b5440f000d402da0b01c1503d04010000c90409500282400703140d61103503081c502076425500240300e1140810190412007400fa16491180c3c02c0d6610b2803940910070541c040d60a11402500f01c40c0d85111702000c0e05d40007408900d0031401c09408a0b030640c030080d0700741c40121300100c4540214a1441d894820820252400205410401c1008e000c2c4d508110844040c007491903144c44032690081400c540007500010318660b00c20315440d0036503201c424215624000700c0f0840010038541d40006004030880184280310585a4600a40b00080038260240070740102c0148401c002203103e0142e10300c0814402d00740300c05505419850348000c14003101c801d0340140c4d161801d2200c2c0c0c0c1400e00c242003011b0029102c81c1c1d12030706a0384a141c107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97955476 1250 97954226 97954231
    0x60106081e240108041505060d060f020904050109051b1b0f0a0203071e0315090503070c031e020f0f010309020d050604030801061e0806011b0b041203050609 69
    0x2880a00000511000c8180005446150826940c07500d542440c250303000901d4407034014000e41c0420582c2024456000700c44a52045601c01041030258000d031485c00d01800b8058842500240c000c580700e00001c00b94010140c07d020f242d400162504148001c200c152081a44005e1145241109010b42a901c0c005005400304c0e08500b1107544200c6040098440d0082040c4440305d402000c00c5440d08640201c0d01000c003500803400c23520300342d0b02c0c1c071001528400310102080044400750f008200060228040910490342d400c80042c0c3c60442d62100d50860340102c2c0216440b81c42203c0030300405c0412011122140c85001e040001814554041045080300c1303c20144140c00c508050300641e0301c26002841c48560284c8081c11960302e5107000d031b070b0703500042e281140496038800020845034071401c10040001591040300f048213a5405013590000e00c00b8104a0402c894078147c40c50a400d801050041d403441500820748030b1506040c107540405c8200014403c1604100c07d05c8000da598045094 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97956726 1250 97955476 97955489
    0x90102012007200406030b1611150a15080c01030f0203071b020301020403020406121a040b010513060503010c051b01020a0507021002010e01050c030402040e06040209160201090503040803040807090b030601 90
    0x1c0e1003c41000030496440c0070107240d61150030810044100654480548c1c050014504c0d080b10b03c16064000b5a000304a1380c021032250b911102010607001aa43c0704550483c0b05041c1c00156403c01c0e04176500c02100c90740150605074008003001d021964035118212085000078170460541c14140001072541c0c0c405500c440c1c3c000c2c00c501d650800d555080d4100c3d001554000c108112941c0c0d507a204003d107410b129015032315015030380c5603940410010002d581c401c507072003481d01c0c1c2c03182e092408008030490201400b07465560f5411001c40c458609125110030f80200351603070754a41007803107080f480d00302a01124205590060040040d4150000b0640c1c11440c0d048171b141c030000b815902c0c200c1c018030a0603d80c10681d0300780424000f05082c40f07001140554001c5d60148011241c100640b9a00c80040c1c5009401c60315510005908042e0001d803001c011219100104480d20161915455904203801590780b0b5007001a0400003c0010800707103005020801d07082c490300038078200080c0c46010521401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97957976 1250 97956726 97956743
    0x10b0f0a050c011418070b0702040504150905030d0606031a121002030f010e01080604150b0f0603010b210106050d200705010f0c02010e0c0d030903080f090102012007 73
    0x5000c6074010029140452051030003000070300040d94506094030010740c1d14542c0c4600119210b20011004103003101514030200f0514074040c000c1e401d000003003d0080c800d50f4058285042c89030007032418001c1c0c0c40e107680181c006644078080c1c0c000b803804985041d40f01d031040c9860f012903614071a144400d8044240801c03240e01d2074050380501c5150800e440d140300c044102d0b10000820501c0000303180100e050702c40c00300380c8841036a201c0d01e0140e82d0b004140d82c06458480c0d1440081c0e0702512035008420804c0380a054400c070300d00700c1400b24029400a8210600f8088081081c030b000c14000f58805100c1c001c1752114407000d51600130007511510501c61503000b416203581c80100c85c005070702494410103031010492903440015041c1340d070003825817800902d4158203060b1403400b46441405611088400140030b09106d011140c1081900c8411038400c60030320900344000000b040016014254600f440c15403035039144000c100090866031040103a028134103044030075a0301480e03502c1c180d490850b40f00400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97959226 1250 97957976 97957987
    0x10b0a140907021606030204080c0604080a11041512020301051f06030c1817011a13050406060503010507050703020c0d390801150e0115051608070b06100305010b0f 72
    0x4905102034031254005480c40e044c00080c1090b450340c024008c0f962014292591002e0480401c407640c86240b04d206182c2d448401103a01060400345c20300c0321000c0080000819045095112003050328503071103c6042e82c00b03034500c00c09504080c01001d903c141002c151804105903806e805905520b0350090808040d81e4503100c202e0f440c0581940032078007103442100c2c20569914000f6052254441d421034145500782031503030b03109003210200241c0c1c4070002132142e800c0e1003030440c0c441c000300401082558000d85410000a454400307200380c2c3d02484003a69000c0c2d541c96641006440c1600100845d401541c8140e185008282036100054140801c65202581040381020f11110b408541074581080800c0d01d40020746100158418000320040340c0c0201c802c40e503103003403180d07400388244140a014409003881040c801e12860043c80040b0607030152101e0003410362144000c682080304100c0d14842c042040c070034603261075248503001c480140380a00c0150b050901c204220701071303c0d64202c04104003150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97960476 1250 97959226 97959241
    0x20d050a030f1d010c080613021804090819080c120406150b04080c0603090a03030903021e0102040504060504020a20030c1507030e03040b160f0501020307030e010b0a1409 75
    0xc1802d90042140707007070000a000001450f210b980d1144815180d40ca00036041d001203004081e51803050030014441800c03010308141c100041d500c90300c0d40560020f42104110003540c0c503442082082402801803035150040034801c0c505011a118610090200585c00c022110820b0300c1218040e051030038880303100392143d24008001c2d00044501c440f0b074501510001c12100e8182e005082101d4000d030443c0d40b10f040030424041a84000d55059160340c11003080800030a01a40004020b01c0c40f0748104d4044e003101008000c0390008503116600648d4001030100502d1605018030809020204d900314034005500e0006052201041000302c3e12134401c0c140c025410b8002d0040d507088003084400d448030060112901c80c6104802c4451601092911000e08403088001003610140c440d50605289041c122241210300f1048501085491540107501240000c0742030020754041d02458601251a0200c407944609551107901540c2c040c0840741810442d004112012880c1800c043c2c2d4802061b4440a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97961726 1250 97960476 97960481
    0xb100317070c1a07061407080105010f0c080a171305010506040606081b0f0c030904051e0a0f021902010209130b0a05090402060c01090c03050709020315010e0d02030106180e030406020d050a03 84
    0xa44c0580540e14020340d018502c240700305201e109680710f45d1070b131080b6a01d82006446e202c001c0b001281c0020741d141140c0300040c01d2003005144030841814486d40c0000840fa648200d20707000c8a041544200d15130301030041100034041e0740c1d0848011582407200500701079008020040090104242e04c040c3c2c204a10b1080d00541100c209152540841e41e644810901c059503030740c8134400b0395014615100000b0508610306442c41540440c401c41040d444e220f800c1d01201030040f2854092406500b0041c10f1440040041d42c1810f606041d00096118200c1d0020411080540c0c0003010b800f6007040075080c410342c1c03100d0122060340d00c21208240e1540322400860406e000d02206020290300e8114188144040c814000e8201c1707225004035070b209900c0c3d40d6200243d000555080c9a0400400070842e2158010340c03440030f50103c06480344c0f4400036250000303425a0559401603480458205205901805900448410201e01d90046145c6854004029900c4d0030805142c0200030020401c00810343c4a40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97962976 1250 97961726 97961737
    0x4020f0d05010c2307051e0f03040303030c0206070305102306070614070c030207260604030e1302190507021c1505060d02031c03090b100317070c1a 65
    0x34003c210f081c01e40070001c0c008620b00c00d2020301a80f0340f81c00b0158030000c0d102c212090198010003070518a400c8160341803070061040600e818034010240c00c5804030170204003a0005500a0750f01140019005030040d003414405000b0400f098207100030000843c031401a10740881c0c07e0b02c0f218003054124000305005d07500300e030050703554400700c0002c1d0f00c4284030311030304a9040b1002c8504909400d8940b03200580d44000320b100c0040250300141c4040010318010210380a416605070014600110b41600710b5040c502d0032a800c402081c4400b5401c2030341c1c2400204481d4004a800d0118078010f2100c46824200100d405c00f00700300500020103e0454a9070440c0b00c1d203066002104402da40c2c00d61401000384a611900d0030304c02481e110010781d00c1e00e0182c3d0701c20758198005e800f40992052400020415402c1d14098809050f19468001d001921421010b444ac6c0611400310940c1400c2d403801c00c0030000300030700e82d229981081c40488003143c3d00311034900403680071080d508030008000340f81e040140140d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97964226 1250 97962976 97962983
    0x4050f0414010b0901030507081213030f060908031303031a0102150c070c030302061501030b0609042703020a02120102071e0c0b0d0510080d02030915120c040e100e04020f0d 76
    0x404c800042007000c00510002501c240c6400d0340c100a660b4000d0100314043c1c030f00e0309210301029003070400c041121150304803076050080c44086859400c54403060056071040d00d03041040204c5065000a240d40341c45030b0386c0902c0c42c44e00e070401d2607030640000075526440c0001c40f40d90745601c140131a440001080444550710750140244d443c8643d2070070b01039100c00041328652010031100961103044d6101c0d100b01c0d05080402002c0c06d0030a413848003400001d100750861001500200501c81254bc0d0107004c201c51624803e50045c1016806841807200105ca0000340800380d81c010301024001902500303e000300c41c0f03250105107202e41124240300303400d80034561003044d0001000a0307480c4501c405401080c401d00c13101e66030307001080c0d0b10f0504540e100103c100f10310041e00148041c03801031410701c2c0d8600300e2070041e0600e5803c1050901c000740300b002003622501d2007000c00140400080c582000c0640d40400c5e0440c410100740d10b0a0503a4080c01c8004000a20400d6101c20140c815507440071403201e403580 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97965476 1250 97964226 97964239
    0x1f0b030a030c05060c040605071119091a06030405031e090415080c0f060a0c020609060309010b120d200a141608010608100b1201050403020604060b04050f0414010b 72
    0x6031030901905040040209480c180100f900041703114081500311411100f00365101d40c9080840d447d20002d4404070207000e903208805120003c800c1256250300c401600e0401c0d0001008a83c2c68031020180e010503500394040c1b4130034000c0101254000c0107540b04080032120751024500303c1e040070b89252142c00c130316641c0280791001c80c1d0f0502000204a40960f80480c0c2107031408641c440c10811030007800d40300964014002c001909505106a19540c0480e2019068a041c0300300100040c05541084601400c0c60707546005090983c034111944131940318104000d400804c443d01401012040510400032505409445a40465000700300c441440b94020041a00d8003100103480c030f03114800442c540c082c500039500f000c0b54003001131042000302e54800000f01440c80705e05088001a0038040d0306241d0218041c464044d52500c01c1c01418400e03803107540070307001a1074a45080d0045850000006001b24a8082000020245003d01d00d0300a900040102002c0410419460140043c034a03015002403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97966726 1250 97965476 97965493
    0x50d081309021903380103061d0709050603100b09060c011506110f070e070201060506030901060608010b0307021510080a03050705060f0c04030807060f2309030c1f0b03 74
    0x2071070f91046031070540b4507541070244101c034480c5007001c00000d80200d41660140d6a41c03043c0501c010300c03004454030042c180401c0d0035a440044012160070703035040c0030414001408000c078040c4d1007250b0b4009448120f615600f581003265000b8052175607401400b030511800a5017840543e2400e094500040300900284030031005002400c1500f0b00b6880340401081641031070680a03071011410036030750100b010092119515003042c00d003103038401a0154065560b1040c000c111510390400840c441c86c03845001180302868840014980c000c16401920303000010b10500a10b150701196200b4040c0c6182486a50354582d90030320f810030141c50b80184034910683c1058001c154019002d820000d015a080d40c40c1a90356180d0381c0440b0b5011581a140000100006d100007000d4101500b0300d01e0140c100001c1e200c0140c0c0d80102126640f509501c044200c001e14211480101511282d0010180010b541054040b0385030f140d40b003109005000003040074810f80a00c0c0751341079200010481e030040440301c440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97967976 1250 97966726 97966747
    0x903120e12041d0105040e0a0605061f08070815010e090403031104060c03030e07030b060613030b010e0603010b12030306060705030915030402010206100b070b04060209040e16060306050d08130902 86
    0xc600d429900e18244040f40c00014a501e041c7c1316003180410a41e003c1c00c090607680d503501004042c004c10b4a50b2140c02510350b105414454900c201c2951160740f100c0c02907050519014041c1c0b400180b6074a171048010103400401d990100f0040d204060070307a201c0c41561618502a0040c02d40d0000d0050740902c086400116241c2c0b100403658101e0003034404011b5401c01c10101521a8040d02014000d64a940d0225580741841e000030f08100982c0060010010348a03603d2104442d004e0344041e00300c1c1d10038414081c0d545002e00c2404003d002c100c13940c2c02100a0007640c0c903182d00004001c60320a050100700d04082c04400d00c00ca0304201c00c0144101e81c0404100704010b52a0400d0b90264014462000000c9000c45054120420340c1c01c1d0300c55041c1010041e680d4100c00d0980207000b02d0b0510303000e10400840340c07900d0003210030319142400540101410480104a4610140d11480426040807001c20490312030400503000150095491555a0f03100c1d800c4406c459072076406980400c0c40007542c0c1a94 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97969226 1250 97967976 97967999
    0x160602071a0c1507032f1b06090a1401050403091a130308040f080d140901050705150105090a1a1504050a030b040b1303050a03150b040303031508010903120e1204 71
    0xa4000d42c40800948100099198016001d06c0221088004100030440050f201001802d80d00188010004a0410020354141401c50a603150b0507180d00641c8001c042140c1c20b0380c2211800118002003015240540707008041d441c00b071040030b4378100b1640003c11800e000604940404c41c1000c074415142c1d2b6245040602a0f2140c4a285428481e9a00110b014200401d4604d204001c07683c0700320409107500d00004155004440700ca06022040100e44006001805a018040c0b0f4014515a031903140000f40704080c5c0c0010000e109440c41e11248c020380048000781d4854001e0281c80d4144041b866a8055007148076580100754015040b03400003007080b1503c101c0170712a80c425107844c5090784179140928401164804001d01040044c883c02c5900d601c26807100e000c0c0160400c101c825995149445809548035800c1030300003940b500e4480304002d00b081010310040408200800c078100d00c0c4c0c0c03001094100405045044d203500c4020300008403104005840d1070040c0036029a0341c3c0d541d50f5222649 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97970476 1250 97969226 97969231
    0x13020102240a0b0604060f0f030213080f0d0504150c060e01020c0307030e0105030c030103030c0614070c020a051801030b18070f0513050f0c130806040305090102160602071a0c15 78
    0x14203d04250b030100050400740f0948040b07500035110002c11380c0c000103050b80c60760b01800400c0c08242c0d0900c51603181a00040300d1800401188000d007c0c4908206442c80c14282c0e590024024014100b00c1040103002e410120000b0442e1440c0881c01e8803031300d00e0558042c108d40c151001c3c440d8008500710355000c82c08070027481c0d042d12039214012100e190000540d40c0c5d000890390b0129001c07042c00104046806841c150010502c541000503020b8095454645c01413025203003030f80003d546005800031420060504409081300301c803581d842005a018400c03000005000040c01c3c401214003041241d500c035500092002c200300d05843e0700765122490b10381c7d41c401500c41e07184210070b05600c0c517200d00d60034404c09001d22020410600c07076680c2c4001d0000694001d54956442c8292080c0000e00e50100303114403800303248250341e03040c0d940b813546000900c0c2c0f01441c2a2100740641080007000640c0c0c0000d80304085410120445601001c1720f441034100303000b0307450030072403600441c5484c854510344210400d1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97971726 1250 97970476 97970491
    0x110601090b18070512070c02030d09180603020d120203040905091f1416090905010b0903061602190c03080c0609070602070305030904020c03040b07120f030e061302010224 75
    0x581400c6007032014080e0419110b983c00300390104004200000c0c1c03031006503807148503400e00349004c60036580400e00e40f460131b280400005030f40f510140714024000b21510901841d000e02031040354259000504c40380c0c40b5010040003804035507884501c4900034001d48004000b1120304206518000b42a95158290400412410b64904804115480722442460b070707041aa403004052698034901c001e1000e05201c400c0c0030502040140018058009000f580d010741584900700d51075980c10700a05d494542d0141a41c8100030189150b000c8880d0f00240080d03d400900961500503801810b0080001025801c042c2120301c0003c2e40303036506800062054040c0850804840304260303a807000f280c540105000090442d08100601141c0c1d203482e80103002000301c1c2d0750590380740c0799961002c0e8080350300c01c03001101e5180c903120142e04030540011b5034041405080c02c0c00e2020b5600c0f480c0c03880c1c4400d40108002802a16210b0307460569208010410205d01a00e01d00305004550400d0001401030803200034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97972976 1250 97971726 97971739
    0x140607110c010f0c02191a04150509090a05060f0d0b0702160b0904020304060605030106150908060c040902071110090509090c0306010608090102070f0c0504150b03010510110601090b 80
    0x50301c6544160a000040d0b1040c1c0d6605500031407503801c10554a44130552144460000000410010047c6c40800580750700b000e40c035542c60f841d04a0880a1850b50024075042c010240071000706510380d10380032a03004031642c5001030035584000000b0a52000c80b01c000341c02006a4405501304503502030114054161a0211082c5403d0f035016406412120301407048a01010300125090b0b0500ea00a0745d00540306510200d401c54440c00800d01311a00c40e0710041c500f800070940c034a2419007001744800a0080ca078040d1250f4a400c0811034110301c9a80328800d41d00794001002c200f8400c440c440d0200d0440001c0040e00700140003e00100070310400d00401d48241781c0e80c0c0c040745d5404000a403c0b801c4070405805080e95030301c4c1510a850a460041000d04555002c00010000842280c402c400492150b5440050035007044240b01c05c40f89640c8050111104089081c04952081c40540e03045403811141d00e01540289001140e00308040b643c24031f1207101d00c5c00007041c1c207a0075801a0b2040c81c4140c840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97974226 1250 97972976 97972993
    0x70306150e120105060f0d060605040e06100609121202240108070e010e040b060a0b07210309020d06021e030a060806070203030f070c08270a0902070507090914060711 73
    0x228201c4c0c0b802d40c1d50300d610075400380880c940c50030508030a1000c5070003000002a41640d400215003a114000541189900810300f0071001200f10581c560141001d498034040850409150300c4440414a80c09800d00300a22103a070300d918030821044080704010903094450ba41c008406044040082c02805018003603100042040041291041c0c101c4604c2c0d01c9074142e540780d0361508004010090100c0b0303000f121400012138000c84e0300000300340d003034440d008164403264096015130f0070181102071402010b09228459016039a510340901c629500040016620305904080410340313030742c640c00422070400101c20840140c6075540a50100ea64010a5902075a1500c604a07122700c000c803100b05c2e0310001d4001164074140b04451701725240b48903140080c608031040b80703514a50b03105242c0c0145254040300320b68a4a060000d011801001c041c14154140f880644d1015202d030f410b400f5124001d651400600c003444001c0c01103208031140f031001c1d1542c80c105008000c01d85440d550381d0300043d00c641c202 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97975476 1250 97974226 97974259
    0xb0102030705031206150f0903060106090e0609070219060e0105070503040c0308072f040c0905030a1b0f0e070f0e0a0302061b01020406030c02070b130e070306150e 72
    0x40341c0c00c0c40c0d4460095032402c01c0e0300003005035070000540100c1d00540f1072440800d241c444c0b000104510541d40c0e5119031208001400c0525068050704a101003050302c0c0010014909144250781c0c001002b01e91028a6541d000c10880c54010200c0c58280d114106800480030303c060355110300d50010020001f445a6a60003006858510003598010204580c0d02401c001151407180607003201072203032101e000d40c02422503803540a01c40c11050354010042c59810b0403c03d240c5842082e00062450600d540c1691901c4000382d140c0740045030241080f2804100c4184202203a02c401016099400c05603200c2074a4200200a544040721030401241080204900e1103000d40d900b2003d00f00300400ba8628141142d0901c8000c0c0c001801c000c0741d00040c00503e08032400c0130f00107400a0035040d41c0000f14920001e40081c500840c0e58409003010b04200030100480c50500212300c183d4041c08401d81075512910400c9005292650203101001d08450383c0341100c6d0f601181c0711081034000c4401c040c055040d01d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97976726 1250 97975476 97975483
    0xa08010209060417100204090f0b0a0b16020102010b10081006020c0a050d32070b120103030c02030304031218091b1d04050a0902271b0f1c0b0102 64
    0x214160740a0b40030300c030400000d5408154030341400904c4096459841c80342c04c88409a81160b0041186561100d1001c908010141b2030b02c860000211510702c001c0d80380075106032203131280c8143d400041c00603010050959000b5088401c01100150031902130100c5818010003070701050703500c03090080f07980000080b120300c0041c1c014003c0347d00030894181185420108400244101000c55041e203204a40790342c18250802c6250301d00d800002c0000400044400c0380b070030044caa400c681c681030760074081c071141c10031002410380c15030fa494200b4403032300344481c000a40781d03015982c80180701c0b0008458662202e1303801601200c00c61041485c10038015298000c050985640002c1d01403d4480b240541311441d204404416443c5e00b4401c0c0400d4190303580022030241c90080b02c0c06140709462340c0c0560118204482c0c1ea010440c041220030070490a82481e2040090014200304500483c5099482d16080c03a4421250081d032580040d039a03e241c689440e45a0b07a8004030b441d4181343c5003484d550100d50010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97977976 1250 97976726 97976737
    0x10e2703130509041e14010203090c040e010c0c080a0c0212011a09071d01051903020c0c010309050a06090201050909040302061009151211090702031206031204060c02010c200a080102 80
    0x241e0f0718443c080341403011010b245c04280040d505510361041800d2a504d0a01c015030284150304040d007501100708007031106840c00320843d103180da031600340a03048203a80203038030700c4042c4da21095580d900c0c0140c01c4100d030502610700000e588001440103020340c80d1015070240040400d10b000030f2074105d40314020000460421140c0c1004038260485004000d0b150448030509108141403003410190048a1a40480344025121010941c0044c200008140030086ea032800042403805100c00302c03a80da0344545070301740460000e118035255144001103a0040050320046600500240041d19003820004c1d030307404042d520701c001c1003d0700001251852881c000c0302c0c104145002d017008610f1800040201150070740c1ca0a03a2054420740144800340e0322905094000d501c00e074011615206078203540005440f014100611941c04a4103d00c1c0f00e1241d6815141240c0441c10b105104000c0c0b03000680c0c407000c1032040180012254405040c04010040c43d402400000703440365003083d5181c5001d40d08070f2044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97979226 1250 97977976 97977983
    0x506031b010c05011401090c0212130b03070909141e04021e01050904020307110d09030b0601050a1101060303050a0311071e02030708010c02010207110102030909010e270313050904 79
    0x4200c8010950080d416500414071903c000039132070505412548008001fa08844503a64640d40241852541003210019040364005071900d000d01200c02d104450120b071140d0207060f030000c000180120b0142c1580030050041100501c40c074215880310501b1900304882e03020742c4285000c0f00013402c5442c1044144500c0c0d015094044909202002210281c0c40c0402141001010400705055448600185005600ca1307100c89240c08c0541c82c8440c10601040d0182c000c0103c1c07000d040012500c0301c40c40c6174015200b801c00700c0d0394400d81e1500311405401d456007c010396003414800800c0545c080001d11411031281c1c0d00300409031150f504030440c1d00c903106010381041c101091441c17140e8040e0181034540d51004003115140c80c2d40b1039500782518062070340d210150b5030100d443c0c0180b02c827440458500007000d2028502e041c4103100003031014107041c040d00c0c8064841c03200054140b0107103080c41c0305903441c00288a000168041005517a98080e54090005000404002072903040040c03c03140101c0d070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97980476 1250 97979226 97979263
    0x609030703120b0918010902180601030e120403030e0d0501180302060c0c07030209060f0d1b0b040e0703050403030f150f08011107060e03070f050c01030501081c0e030a0c0f09050603 80
    0x8617421005945a070610264120355038507501c6000503aa0001e03600603410304189110000e01c0d05a0002d412554900441103440c0c010301c040c8604615400300300e40070380b0750505200d803821603a0400f050340c05070b000100800035031074074040c10760035130541710310140706442542101e03080e40e12001c00c00001e00480701900c2c0e0a80c8030b45810300040c984500c18592215020302030860802407600000e04003025100186c44900100002e9070900450149207005041d07140340040c5018500101d140d01c001c03004010904166407071021504042c0309401070b42c01fa84c0840c80034060f040e108810864642858400d00030b611a4002d070001c0d20344818040d08281901001140e4100320303040d21a1400f400c00c181d00390700c2c0f0340000c000c9100020305185404201d1030081005002e00d480c3c41001404070703401a0840115076005400c2103290081c95070221440c5907482c54080f9217031421300040380c90102881c0d4000e0030060104008110511810302e445d084034140c5000f031140d40ca90500b40b644940c0841b160000a20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97981726 1250 97980476 97980481
    0x406050d02030417120901060801090309050d030c08210108010b06032703070f060b0901050f06070501110c030a091a180d0b2805061809030c0609030703120b09 70
    0x58196000c0c0d54804c0c00703134800340403000003a43d40c0102d590201c1072000c1c6160001041c0003012600b4402d031400b5000d8503000300002c00068070054100369070f510410b0f101d40408400c1c4010580b2910000401030751003034681d5151181c01121030244886050301c10101c40b803e070700000704950140200f031007008018080c1d40c0780d51950071900f9130105522240ca262950380054004d0300007410001403001034055254a04400c4862402d40300f40d4a00b42000391140e0583d030010700c92543c440c0c4900a10800c00c440c55507030341c204c03480e202e805012044295810341c0004034032064189030100003480200343c0b540d40c200003603072144030700b920303000c40d41c2d8015103540340902c4550810344036080703983c1507843d0050203010840002d581315152040101d80c203543d004480c1d60b1000c0900c3c80c009079a2004a4041d1060260780707408408907140f44002c940c0b143c48044250080343c021078060007102d481201100a0b00c060b071812a404595170340c01b9640031000146280c0120260108622a07028180b80c002d0800540d84c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97982976 1250 97981726 97981747
    0xd14030c0901020f15060f0d122106080703230606010503220303090c12080304080d0b030d050c120c0307060b0f03100b09011514250f17040605 63
    0x581008141034158442d04080c6041030408021501e12030300b02c600302172103615100042c0991440c10084c2c0342d01030780c5203031607080010354410b0080110050500d00310a0110000740c13004500c2450101141c0f00601d401400715421a01050041c00e80e4000c40c1c054041c81e8616082c42c16050f030010f1a0950768002c003000c9100780d8800c0d0000c5800008155529040c0c000b041040c6e10090b81c07101e01240803983d203450320300802440d2603a403001041036244007100e058581d102d03e032141c400100b0080440e64000789007041c410f4070ba44107068115019045520010b003400d00a041c2c1d0307200100c207008501c80d0340482d0000202d2001201d000d40781204c003031401c216075a9224000f51146001c6e047d44107181e4100110291410010110161400e4901041007140b0b101401038040c41a000482c281d100c400000e003070181c22a5814202942e0420265a00e81d01c0c80b206c000c0480b503000d000d18040074060303a54801e00403034614801c09103000c0c2124003484200703024240418400c80c41008041203040c0002c07002c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97984226 1250 97982976 97983001
    0x20f16021c11120c0603070804080417030903060105040c0f0804060213150e030318010809011b0315090b010f1202090a030602070303141603020703031508010c1101050106080c0315040903030605030d1403 89
    0x709e4824a403841c20f0940b202501c40d50a8518000c41e102588081203070070306450200b0106005000544003001846a1070780c0091804040c88110340c10b021480e40820100310f0b0a41c100e604103800031300c1d060090303510b400c8226611030366981c40c800001d4400840f00b5182c80e0120840d200241c2c1d071140c00c1c000d0200c4034019640703d4002007041c0c441c1e559505407800b0040094200b06c82451072030b83d0002e08d42c0104c1a1103903071003005810412996203404041d42141e608405002840d048504002c54460801c1d6402e2010384507601c00141c2010b5461070000c100959500a0004c661003078409110001c49010035274000c18003100e00340503102034016a0003e140c0a540200003860085c074001c2404000290700c50340001c07060307202c0e0030280c0d511407001c241c0e26071000503000440031100092000b5407505400500502c0301400740c0300e400c030700040440c060742192030b6210f0b0141400752052101d64064103010700100348500c11940a8044c5021884400d44205079205107048411196402c50321208811001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97985476 1250 97984226 97984231
    0x709170d0e040e060117070e010b0d050402060708040e01050a12030f03020d020903060108070603060e150103110409180b010801020a02030d0903020111040b0408070603020f16021c11120c06030708 86
    0x100b095403410795100c256814005980600307021440a03101e408880715281c83e00645921076200d04217120010f210031140802190703020103d51b03078003203100d031181d0001903980d120b51a001071026000044c0020010001c0030301c58105e130310448030f40680d29034a1400a04031113070980b0040c009249039200b0078000d8003036400b9203801d045d504401410480480d000c03916101007a00203020950000b441004a40c1d850701910b4054404c0001d150100e003403040340d0206003d0494801418951140301e240e0400201d43c05490040248070000c0c0200c01d540050b040015003e45000d0340c004041c0800840c02d0a01402100d003150f200794025480c1808810440000f03062090045045540711001d0302858681e00c400b61011b0805451201c0d80e0742d10744a062481c184c030940c054401e01d4010300c280e807034010b0107005944600c0c43c941441003008a0310300c000762900980907482e0541c19204040d6106022483c0c0440034202d00948051502e410052011541c6400711690310b94009410000682170a104044040c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97986726 1250 97985476 97985479
    0x409050615071a0a060504060603050402030609010204081c1815271e0509042a060804060c020708030307020d020610030f0f030302120f040605060d02030318030708070e0709170d0e 79
    0x64a06c1c1c94400040650b001c941c0319000181e1038500b48000d6140c14410345401a45440c0218602850415543d484011001841090be032003d034550350024051180304035880651440c511405450300206040105030120b0200080c6035003038008190103c40b403003030a00c4c02d102050320420624040d002100d901d10308802c0514030050143c0010b90307443c0c0f6222180240e00c9052502040c0740401281803003c080502c0c800d00d141900002006070a410440541d001a042007022644240315001a4540500d0380e110030154807001080240e1035a0125038840c40c822203600303542141c2c0303900c1c0601c0040a62400080e040800000ca0440001c035611020304995201c0c0c100503050041c060032800d10702c4000c84000c00140d4003001080100b22140c1310759035110404941c03d001030620394000c01e58a024136425104070850700070041056503000c01c480c05c0100600c2044440300f91300d41200440340401584d0001c00f0407a250000305202003035411019451a018000340311640d81b0f003604640e02d030360340780186 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97987976 1250 97986726 97986731
    0xa0807050f0604080a1218031a0403020a050604080405040f0203190e1207060b090601050c0c040213030503030c0a0206070c03020c0402070c0b0d06030c120b0610020f030409050615071a0a 82
    0x5a0118203120742c1d21701c00c1c01a0080c0219038280c0c2c0e0090850904040d00c580c42a003906014000a0740c1040110748001c24110024101c1e681c52034160303e060902c89001d000c5202d20070401040000c000300400941d031050302c2c01c3c0070b010a007001c030700c041e40015110001560310040c40d03a0b040c240503510807100b0a07944012101c24040d25244460903074000c54080d1031040d1030b16505011400d16a01c840d42243d000c0c80d200c3d142000004843d40c0310360400b4038062241e42c00050b1031003031110004042c805140c122040c2d0381e0301d0805090600c540c0e44183c59140160082d0f0000030301c1a4080d2000c48007142e00b40c2c01400210f800c01c42000000d51081d54221754040c4294000310301207940c2e0001d405007901010000500d181141050742049030380e076002c0503a2404814405001a20702c404052300b08500740e50040b00208113400c140e060124203000aa102e10002c0b5001501034142c6e000a80101000c1e82d00c16001c0c6903010314901300f0b10490201600140d403910503200ca010201940552140320301600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97989226 1250 97987976 97987979
    0xa0b0a02031c0209010201060e0c0304030e27040501062c0705040906090c020f0c0a0e1302060c100525270b120112020901051311270a0807050f0604 65
    0x703102d0054216000d00020303603800b00f58060956024820100680002643d00f001868040c541030414800140014100400e0f41d12404468450f110505500400d0303000d039403c0c00c4102801242c02000031201a5180d41c2007280005035401601c029098070a240c00f49200c0842503031510000d0030b00003a01180412004120000d4450380b42c6c0b2a89010700441000850f03c81215100240f51a00b0050801c0081d0041c0050031065078450006808a804116800d686a516002e0107415102c0500006c3d400000000d41c801503903502146007090352201312000c20507074542c80e08040101920713111810340410100580c50740980109007803046910034221012040702100103803080c0440581c041204181c0100d501c0d080d91041c1c24415001d40304400150710500303180c0e00010354122040c030490380510043e00c1035144907002d50b0444040301c11915003060b80c41300f44240142c02c290100d048910704140d03100c1d03045401d01c0c004100d0011900068010920ba40c10070040241e1040b90014881c0c0c0040304000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97990476 1250 97989226 97989247
    0x80103080307170c04030318060503070309030207030c090603021516020402070f050f010203070318050304030303051b040f050f0315011707081b1c050a060b0402090d150b0409020a0b0a0203 83
    0x15081c2c821390780051a151214650324002e420045680d204449181440d5410b0013015131101c02d880d40b1007254a40800c0086d41d0b400e00340e003000c20a40000d000c04520200108100142d0340188040728802d841200030005e1100c2011840d00400c075514401c3c0b1501808800035203041c0d00644031050045070f040314161400e650b51031800303055000b40c2c02c00f82d4000c01000f600681501c80d41ca180d207000750703070070041880b41da0b54076840c1d00c500e010082c01c0c145d0b16408110303081d03502452461503e999400381c80d40c0f1a19101d144041c40000c1c80307071503c41e6440c0340e008151800e01080d00103050045800345000c1b48d003804181b40c6102041540c3c07031002c0c803c4a00008011a0802c6079a01c08003090003c04c41f101040300600000c010080540c800b88414017030300200003040011200801d50708130034001254060500050081c2c403030000d07070359440140e59104009024402811408040c2950b41c20030103840d4400920080d00c85485000c1d61001d0001340801440d0710030001040c000019105492a109487c803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97991726 1250 97990476 97990517
    0x1605010c0b01060311091008040b01050109030201080a0f1e02090901050103090818040f020d0b030601050102070b07060f02091f120e070303080c09041503051002280e1012140106080103080307 84
    0x21847c00281c0b00300d041c0410b2144c0c1440d030318007418081c6000d4858a0031030700043d10300704020340b01101c10b40d40d558096400e906c040d8404003116520b801108114810032110a010350898501140315101d00000080c06602a10030b429055512a4200781000d54200c0300800d94005440500d41007500c402049009100d01d01c01003184669400b000a508400714050500c0c0c010705030440c1e0b0540d4448141400280d86460984006d56444800072801030040030145019001351030900c9c0d0031900e641c13601400c4000e103139250200030000c1d90354041d21454500e10344050b0b41d81c1e0b0701a001103030008181440828400c00110703501c40c6103902c0c81450107403254007050803030300f12130520f50300c0c1c14444c03c0c1801001420320407a40c460b54204820740c28099018a200742c089841c1a50000c009002851071206d41d000d07280c40314901c0d000510100d1823150400018003030303401d41418058035529200e0282e803d000f00700b007414107940071907840712250303821540c980b489584042d00b072400b0722001e000c003041c04c0490407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97992976 1250 97991726 97991749
    0x50f040605030d05040e0c09010e0d0609020904080307030e07060f0c02210105070f0309052a040e160506040f0e07050c0106060c020f061e031e091605010c0b0106031109 74
    0x603030342c03281d42c3c5d071605002030030300c040240c140d8130384010401c40a40035a81c4010340350301c4008110fa41008000c000d01c0c0030f50060130141300c0290001400c604000c01e01120b08041d502c21444c60301c080c492617160301d0b01c15440396042d00030754001c01d108403101c420051247c0c00100c95948041e2942c025081e540304003084290903c044804103a45400400c6802680007060120303108550078280021006030380e9040d207444204c140040300b0403c0b00700f18940d40741440d101d8071080780007401c100011008010041e80700c050b802250600c1c84030903000051a401e141c000c4808441c81e0080e010710450420b5107158114030041c040f0410004180070040c500007081c0300d0000102110b1301c1c2d4071080c10340c1c0d01c180071049112040c00303403003840d00380500d0054111004107070401d440700c2d0002541e80e80d50102940b80078804080040084264507003003042d003640000380510f03841806c000702c40d201c6554000444504035410401420148040300402042e4040d0308408500c5050841741ea04140d20040814043c1400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97994226 1250 97992976 97993003
    0x1e0e010209030c0a1206050a0f0e0106030506060a0b030a20160203010c051804050408160c1409101e090c080708060f03030714160b030103210801050f04060503 70
    0x500700886160801441d4020102540c08a030302030b20300104e24100740c4002c400580311640301c1000481c03001c82580040c0c00001110700c10000b2524550031103000700494003081310913109150104034107141c00d441e607100700c2e00e00d03140080c916610001c1d0304025000c00140c09040c150251100d800368000500944004c0485043c61001a19180105030a450349d803420710080c440b007089844d80c18000d030803401881220039a4049220703240c0345080e1030180705410f40e00c100311100c9810f600400814290610440d503000101c030541c0c2200c0e80400c2103810b000c0d105241313042e00044040102044a20740c49415000150b010740c1c5076a0b442d411042544e110507500070000780c0342820020b11070740081c0c00f2500140d00303540848000c81e01c840442d0f0381e03101c0c0c2d100150030032401d640680034040d003c11404114503108003550560680c0c0c0c0c03500c011560402c0c0012506003126100c00079108480006128441c44181c1d00d000e03250746807030140240708080c1c1203401c0c0c01a4803810049455103080014038041d210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97995476 1250 97994226 97994231
    0x90507080610090203040c030f0201140d060e0a050702031b07030b10090c0309080307180302041523010c08091f0206060f0409020f09180d050703030e06040210031e0e01 74
    0x402142c03030420420141c03c0500e401e4410b00610010a103c41040ba00f0b5a9008040001400003400141c5110030103007002c0342c90f10b100184580c031001954010340c0403203015280c4014161154408907081c1d8408503042c80040c1d0007032003848055805440014001c2070407030156089551280c41c0c001000344215510307101007504000c1004100a188900204983c091030200305040040e034641d400d80c4000ba00c80000c0168400c00c1d0900d50034840500c0b8005d582c001c100700075207101d680b00100160501e12403191203100102254007102e0344987c0146203088165a0428001882c1e56000c03550303009001c0d09600501445101400d01020601c440c02c0180715400610b224a0180c003085240c0c150340e00018029405c020324040141c88200c1d8030008002d00316100b510030b9550048100842c2d0354a402d10b001d0b8400c0413a180c82d40d54111008180701c07030080c0d074240f1400d0700c03082c4251fa60b0501070303400030b4004020314001200c0500c1b035489001d246500214218200da1000414016100e008552480701c0e503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97996726 1250 97995476 97995481
    0x613030f1b060e01020a06020c19140c0a0b0d090f0b0702060615211308030f1504050405060a0906021902030c100c020303011802090a0b21280905070806 67
    0xc0a062450005002d40c2c0b0305034040b1080d11000030b4940c801083c000f003c054011503050f8460300288049003200c03401d114201040405410036405000b0841060480c5019451041c0428240403071118103554400d4200d900c0c001012642500402206205a4110b91a80141000902a145403a014821541c014141030500d00100440401120408005150308100310480010001440c00c00c914040c0300008c442d07030b60070040700d1000071821070040c20b140c000410440400c06c0c1070101802000c2000f0003100c400540002e000071500195000342041d8804000102000c00303640201140a10400c00541130007549003604503143c26120803c1e015801c046003064403400d007000452024013000006011064600401a4a03448103004800704510403801d00040e00071070790100e500240001d4501c04206a8915040700309400140000c0c0c0c1c8a440c0da18070112210160b11030794001c050001c408101d0342070703032048070303142400140049005a898880b40c0020a900344241402000300101802191 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97997976 1250 97996726 97996763
    0xa0503040f02180f01090e0d14040f0608100b071707030e100201060501030b0d0218071110020406110115060c1b0b070209160503010b1c09060e2103060613030f 70
    0x104c0141c0107019580d00c2d00003020000c00c0300055001e51188a4104445100250f81d85a00c0d0fa102c1d60300410501c104512001400c10307401800c103841607171546904120f994884080308114452003074080c0c4041c100946038161805400c00a2000382d200e41860031180c80010042140d082800080202503551058100110b5800d8040d600042104a603004510304040d8009040e9140e01c2c00882501c540c0c420011b20058000c8244605040b644012514a0351441c08480b019602c607006510002d402d1101201007488140148000003d0003904481094100401140c003011070b02c0042d24491644202a1500703541100c407140a054810b01c03256980a00e0700511003007880107400c0004400d2055414401c96a02c007081e02c0c19074000c40307000340e501c00e81200038041c541158028401024600000b120400080f070f8840c5500d545400c099a88000c103080c1d0b0000b03194400100301a80038000c000185840c90704000811100c5041c2c0d00b004003068584c0c96004032414250000c0303c04c500703141044030f143c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97999226 1250 97997976 97998001
    0x702030c070e06270403050304031404030c050109050123160b010e0a0e030a0f030b011e170a0b0f0d020102070803070807050c090121050f1501031a09030a0503040f0218 74
    0x60141d045501a50440c0d04c161801951100600203403c00c01c0100c0807408251059451500701808100c1164440e500c90502010358204d0307106103804109003d400164035405032010580840c414024a10811050308186030203034003507002080300111120380800001d40351100316010700444c1003600f000b40b03000031400c003c032817006040300070700c0d4024422080c03491f60005582c24031000320716011550311420401070301c0d28100e00d82c94034040300c96180070b250001ea02400c0b4041d20385951501d12181e4035082050f03400c484500091301d410904000000c001da00301030107008109403040c8110795422b9070704d40e5444d0440d008480101c1d044100020600240101000303588251501218048240d5150802c0c1c1603610b1003200700c880c03c1c03510811001c402e000040c44203d004c3c44c0312134169640d40300705180c030208203002404111040814442c0403140c281d14860180c0c884c100700d1004611702805441c0680b11500010000c0f07501d4001e6805135001038035601001a50031030511b442940d5400c050038603070782 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98000476 1250 97999226 97999249
    0x15040807020123180f01020309060f09011209050f10150e1306060e100504060627030804140108010e0405030702090405010e19020f0102060601210905120405100e06040e0702030c070e06 81
    0x115070051180c00040c1d030b9044212003140410b42116330780c407007030640140c0340d0084607003030410001c0ca002500014020041801980b110a0000b580c541080001c0d00408950b03c0c14070705104141401e030f0a10514410580507500070382d0f402000a200c10720717941c8200035541d20b81c01001c1c0c101c0070b010074864120110f0b4040f201805003181c00f0b014103400c10318000c1020b4224290f080700d404030070600501c1c0b00f40d005081d00c05550400d03100b03035507141c0ba80380c400521129048102e00049141c4000510785800000c2c0d6400707140d0100145160030500e400300001c81e4800750003175641e9503076221001003820040042e0340181010b4905d030700600b001c1e070040000c01160306e03d4150641d0000002c110950b039008440f0440440b41c40790920940c45d690745008000e040500004042d4464203401c42e940c0d10388240a082142c4e4200c0d00e080391040f60140445807014021860750f00641c00f840180320041040006607400f0043d441103a04041d50410514902004d59000ea20030429040c01d10080c0d003040c8410a4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98001726 1250 98000476 98000479
    0xf050f060a0c080a0207020f0a09060609050303090a06050c10050403080a1b0917030d0906050108010e03070b0c0901030b031501060801080a200a0e010803040815040807020123180f 79
    0x1c02c100c0001c20140038000018880325400381c5c0040d19030115510428500d11446000d00000d0405445501c17a400030700090040b0700101d80c80c5e2200080c3d520340002102d003e8800900712400301131034680c0c180c03420f0304401c02c1b00ca8540202039480c030f141c0c480e500c6010300c00c1d1b010760364108240c20058140070898110140000b890405803182c01c41058100030608121549218810000c844414400307045010b07525403281c416081c5000201800307220303001141618000002003020100c1c00d2520760f520310450f00010710301000c440003e000711002c03170301404083c08181400300300e00740c00f000020300301700010300c1c050f0103810440300601070564040e44180c09801e8000040c1801c10f625100c41c98a080080c042d00c6240038a072010a0075615024207080003400c05803404c01c80365840d4082076031a038203d07028403846031040e490b80da0052100801161b000f00c1d084400940380107600d400450f402031001040c4283c0301c1c241c080188040c0703d0f01000340640f141d2403904d107034464501000c200c1da060300160081d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98002976 1250 98001726 98001731
    0x11100804060b09070e0d050106090204060507020f010806010c060509150415050f150415081f0b06070c0302100212030a0c02120c0619110a050702091e010b0f070f050f060a 75
    0x1c110240c10502e0380808040c200c44600c00c046d040c0ca40540503150341c0c0c000c004400e001040c001011600040900307802442204c81c260f040741da0000464210300111030041c002642050080085140c5c0d601c00c0d40c00210000944000c8014941049041e12050728100c40d034031b44401429070300020500c906a0010040030350a4141d0070548580070f615801800c85505c1039540d010f01c0207401d08040101d0000305506000c0d10008000e0030100000c910300d0414000c90241845030025403440c1c0340707040302e842c42e40c0300005480d1181540c0078406081c040a4110b415442850308044050030383d0406544144001503010074690340118000342808222a6101340c042018811102c10034400306640360b2141403110b0340c4400d02210302010307000d0564580d107426000d1000411444455103d0010000580240c4491900d40c83d41c105210440c000101a400c000245070014001001c03000000c00c060109054641c0c00c04006171600a90041404c1003100c042c0d1040c8a503091000e402d218a0b81c2c0100084e404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98004226 1250 98002976 98002981
    0x1031802061b07030209010b0c070f05101b151e05040b07032301180b0f0f010f02120d0203013308100e0906071d0102030706020711100804060b09 64
    0x104a40d03006581ea00c0011003000140d0b941c0c4840d041050380020f5800812181595030f49070f1031821a54003001c01a0440c0c0158140420b80c200d24012a000f00d80002c0c0001c01c0d8210781c80130440301f0b0f0301484221402030201c0302d08600845c90119242884d4a141c50000503886c1480e04e44080c44030b21680b50500c2581404208004105004101035000c0100d08000c0758406241c407000c09420800c070341000689007800008688011204a0201040c1c0f003c8801c00c1a0404d01003044450181c01001d203a1002900c1020021940b08000701c0011020380e004940085502c00f081500d03a0708202090344071070798040010808107649070385848012400e1400d11003000103880115036401031650000e01400102804141e031405481144d40c0103050801c034003107060800710b601a4880310182c0b0400c001a030b083d42c2c0219440420200040e50400c160000e52800c10590b88010207074000c05c0080e40c00f1001c4204401182d203d1085111160190740e40f2850140b03480d181034000c48402e5108940542c000108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98005476 1250 98004226 98004229
    0x6091d0703110406030203060114010306170607031a060406170a050106120b060f030702030d0c050310140d060c0c170304020d020607020f1207080601090c020601120c08070b03040201031802 83
    0x208003090302d4010312201030900c0b40601280103040580d20003501407243d2000021100d0041441e150100f030300f6030301072101d03503034900e003070003040e50b034850004220b0b000000820110b034040c0d40003045900c5011101c02000c0340c2480011a83d0f00594052004640102407680340721000e5400b060307011440620401c160350505d2401881c000c0170007010340b896641c40400030126501d200039500080110b030034a41e50303407400c01c80080d240d4210f4504580c4450600410024480c01441a01e00ca003030000c0805c640c03507160010380c0e101103140050094124407c1c1c0600804101c55004e41340030503800b03071104001c40d01c440c6400c0603c003c50500301c0c07103400418400e0000603030b144010303070900c1d54048131b0703503501c580d110300008041000da003d007241d11450103c2c44030404d5201003504001c0700c100b10281e9240faa600e941c48415603103800024001a0810001400f40c90000317044402e00da40208445d085c110307150402c2c20b10700140c0360030034000d10350044100811507074940103002c01c10804508090710014103a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98006726 1250 98005476 98005483
    0x61202060d0609060303030f0e0105010b0a18030804120b0709140609032415011b02120a0b0a0f1109010c02040c03090611030106030e031201290c0106091d 68
    0x920906000030700080e10745031a00410041e040710701c4100402d41d600d203409002421428543e0310307094201042241400818031601d8101d48008d40042d1404640b540c01301d40b154040c040c100c00e003210703588000c0046030400b009880501781d42c0310303603020040389810a5100064001c1654080108204040c00080300a8594402008007500c0b4142c03612b011000181c200a0301c1c203500c854480241916801d803203620b20055004806003074007070180c080018011101c16807004031103114103420080c000010b06140d03085903000140c1c4005c2d68ac2102c450b64a50383c1e0040c059400003401e80d25880d03518441c50052040c28241c0b400c2154840c40c18080f400003138649003d012020f4415075560035040306d004c0c000d0300b21100f07480d40000d0403c48481d080c03840c800719030028051200003d2502500b00001d14000003144c0580c91608034100c06c0e070786080504240000c540c1540c43c0030401c204080c2c1680c45506004c2c00e184002000045070190420100c0d508485090700d6401342103d220720021022540031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98007976 1250 98006726 98006759
    0x120307080310050d050705040e01020405010c020d0f1b091803020604030f03021908240303070f030309231c1403060315010e0f13080910120c0c0506090106 68
    0x50140ca03125034410b94907841d41415540f1154014241c00c4072081042404900601903440c00c817410021500c010129600f00d00550103021b005c90f200f40101009858401c10301c840261042644088031101640c031140c0c51280a02000d0b40c1100c107010901a0302c03c24040d0b110b00c0c40000280c00001690ba0310300030364403500a000a810711071600584951a80700ea012107040388281c2241504030076944c1c000038000502218127051803100d5890010701803002e03640303600300c410008000354100070321510307180ca00c00f203181000c13428155a5002030000440e00301500c01c50303c0302120b5905c15180c2d40781042c1d090403009d02801d114075540b200503010303264228005150518211034003640303c1c1c3e00c5101080ca009410390248400c110410000100c000e0881c51041c85800240300e02d2415403034050800c1c4100308443c3c00105060024029101c03030303090140c0041c01107540c134500300a4002c001d00d9040c01301c9460580500000701509601810300034100421a00648190020040785240204190382c00c000c0c5e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98009226 1250 98007976 98007983
    0x5030615071103061806010b0412031101180b07080a0506060a0e12060f09070b040602030922050a02250b060f010507050d050d0e01020306090109050c0c0a050a050c120307 75
    0x450300c14140140ca0b2200704180b800581120842d0030035070102a12400700d40400c403814480d000004c01c810601c001a14111005040c070720441a400e40c1d07003074036020710f0307100340354401e641e40d0031b940034054200010038410900965080f941d604080b80010540c03180140304034441c41c1000d0600426850f403c0c1254495080f61070161410340303401c000035a0302030108191490b0b600c07881041c07024007000c1241c40d5014200303580890b10701da83d4a90244450307020b50712550f00540c009000c210668140b0ba05041c81048500400d501c0c0c2c04805001030302100e800b9100e004445602003a000c1c1034050281031440a94242d28003e0000d1845507105220fa44004007014003400e4044c410a00713690140c800d403005c0e9036110003500c0c0b44a807101d4004007240c2002c40c0342c030150750070035541c010324413030604c03c41e8000ea901400407081c2d030b800c0030400c20140402803c1c906403d2420040c21016503014400340c09510b00c150046c0501458074202146410000c0d81841d100d00294050489500c42c00003c6520081d803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98010476 1250 98009226 98009269
    0x1140d09020603041a010e010b18010909020705010603030f090f0b0d0e0613030f030203040809042f0d050906090601170106030c06020607080108071511071a070c06050306 75
    0x4096960009001031440094000802009000810040000480441c00041d2104600303a0341d41050103003034507003841007241c080b038100b00c2c60318002c0306a83c0d41c54240b40181000303242a50b031800000220780c0901000da5290f55500800d00403d40d120010f140100e000d0315080300b0441c01d0401200d0ba406140c86244101301000810444001a6401540c0b000c50f2910540e5424504048000210400620200c000540d40714400800c0e500910940b40169044002c0e14144083d040a100040440f516105142e950784c40e0401c0d94140342400c10024050f506a0154595510822000076198003902c006a40e0300a00d040112079900001c41da030440d40008903e001d01404003542d039004145a81014046c04000c0070040350702600001c1043c010303e903d6403502c0c1e0720303a41c03010616200d010703900132016a41c4200140400280c4548002050040d0103c03e488a03aa036a1561000c92450f0b021035202c4041c002c030750b1000f07201d800019000208490b0404c2c91551078800f001400c0b8001498000d01c0c01c07038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98011726 1250 98010476 98010487
    0x706020c0624040906090204110301030b060316050d0f0b07050406020f07030209041e150209210c011202120f090f060108030306061c0c08100501030b030c10050f0a0e01030513020114 80
    0xc05c2c1c0c2102001d0f03600030b07104224410f6814410a11036009000a0300c40d00249404102d0500b800201400103500c041d00c4922403a0500c401c000c0c008030241d0003234a000e00c00c4640000418440b080240c090740c000e4440584c1c7c4d0780390a07030203401c0842e40c000119942d00032036001c001507104d0010f0b0300e07402640607801d004c1e515018020036040010012018180f6164041028100b132010381c020319000600311a0343c1e0301c00a2002c024a4410900c04d2000001d800002d0b102d4142c0d40614802d41c003603210400090b0803d0300083c3c42410900c02121040015003110003402450481072040d0f0b01c03076640c2d180c05081598184100c0c540e41344009814140221030018622007103500108240d55014807241d800c2c0070800c7c140e10010036809045e25103140c24900b0100004a0750b009205029000b28042e000d0120b120880b4100301701c0c1d207002038140e014088100714a00111030003070010305406081e52514420741caa02070004086403801450a940e00c540c41c840200540e800c030b01c500e104a24004130031690341 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98012976 1250 98011726 98011733
    0x180a0c1415120a0501230616141c0906020303070509010509060c0c010e0414180c031c081605070609051c1707020601031a0a09080706020c06240409 65
    0x10440c8120009441d002140c018010702c26915080d01510302c40006015590700e601d09503e604555840100007400c813101c55001034248040038202401c0c0d04000d60080d1100d0f52180c1111490200001205420881511940c4543c40607030030808016407402068040c03d200c070207540d03844054100310603c01c01113a49c40d0756070720038011141000c0004e804203031550f50075101150b6421005075294003040c5094501d541d0390a0505c85d120380e98100030750540300c41c0c840032041e19212007050300080c50740c0a01e054407503554600304a803502681e1000159030030400c0e176180042a8a00180c1030540d00c000604080040c0795021054901158200e0310004200c000e074039045180104400309078400c1007900042410711500107441d100401a482c00c2d113041d40d40da02108a0726203400b400010300000c0381401a201c1c145a42400325804505400300083d0039405072661881d0740c1000034111202da40006850b40c0526050100a40010107100c1c0302202400381c54007100c0d1680c11900b803500407a0745214810a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98014226 1250 98012976 98012989
    0xd0f02071413060803091002010c050f0d0e0604051b270612070b04090b0a0501140313081c0c09060e060d181101140717070201020307050d08180a0c14 66
    0x2040b05040d0200701d00b6642d82c40f07490f10780d00b1040b400b0f0300c0b8a0b80280001812170040c01a0000318005030390301403a08130a04000e50302c64010315074a4400d0707669032595403218842007223014001c501610050440b1400703003000c00550b8001100590041d401c42414221000000000049080141c1403e103040d40c0d600e00451041500c0c108188124814800300081c0301c0c0f0b54000500030386900d60014044880142e06202080c21a88125800510344100005100c80701d170000d950020741d80c07840000d8421040d1200210794020b03882d0100440d0100c010300e20950160700c41c03102c64020345c0c02d0022480d40740100282484400c00e000301e000b443e00068814061040b580300d4402000c4034105501020840c1c24a1000c51015100c0c1c140030a43c0fa10412880078207036426540f4265001c114014216000310020040b90854141203043d40b01c14040781d400240144850858200705664101d200c1c03400c18640841e1106940e946011904101001c0703010a4251b030800c2e040d150440040c001c840c0c3c80c7d00c00b007400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98015476 1250 98014226 98014249
    0x302040f1e15023d060b0a0305042102010609140f06040522050f01051b030112020a0e040b040605220b070c08030103050109050c01080c0a03090302030405040e06090d0f020714 77
    0x111007402015500481d80982013070340d422148441c80b400b03440115440f040485440d8020018004004d01c4480e050174420b4110315802845100ca01034070f28044030310071440e0449101d001002d07075110394042c080c40314944101240e80c2c60306002d5049a091880081080841c050a0a40240e88540006d442002819400402c102800d608200102120704042d0b441d22240c103500b680550070070000c50050010502c124100e4280c1d600c0880c9542d2030902c090201340e0408008a80284404900040464084884610990151230110a00c0c503240c94440d0844100500071a0885004150b03914007503c04d00500041c40e50103070002c14a9203c04d070056a88117042ca1004144110010005c800c100040d049001c01520400c126031004180700700544880f40c084411700d4407403100b849100e08061003604421042402401a20f1a0513281e601007000e452000300000c0c0c1c2907101209000380c61408101444ac01161407400c1c600394000034030029103c044c54840c003840404165404886555400c68181 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98016726 1250 98015476 98015503
    0x815060703031d1009060510030201090e090a1403030402040b041e0f0b0406150f171603060b130303170705220b0a0e030c030d0207090c0e03010204060302040f1e1502 73
    0x14a84440c110045016205d042d0088880c1800c001c04102c2042c0300f051804166a81615030030b840d5420890a1040c0001c02006500c82c0d00c625045c10010032030351601460300d151500051940c0c1d10f4a401444156010720401038050ba181c442e80007902800c181070070b0001112904003180c1906003407944806480703204007082c0e206240810000b42011203040588280941741c89015406011030400d0703d40e507546044c124030b54a03440d000200342004c49103400c12080031a09000071442e07152121140c4036088100c40d60340d0003110720824001e040d0804a2101d403090800c000b041d55280084000705039014003111603403580d0b4610401594041400e203400054031142803034540303d1442800c0200054010040c0c40d00900640760380140500b00801d111400c925280c0003445000e142905c1d4a0082040070041800c205045d0541541d50f42c0030700051005146035640903031101d0030440d0840c02c03e4510340c03002006c25050803002d609002c03141c004504503048049035550403000c0c003109a0800c804081d0a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98017976 1250 98016726 98016733
    0x12010e04023c1503070309151a06030405030721030e06150d051f0506090108060402030615010c0f06020316080712051308130305010b0f01120902180103080301060815060703031d 78
    0x380311a4143e000c031f4043c5000f81c3c0c11003006410201e541c0116141d615a01d8003802c03000b0307448049414854021074019124104aa1820182d0b4403940c43d144c1e00034030020900144101c00a21281d4540110b03028041e40d44080c0826040ca801e100c2414070559140a014105e0788401800784242404030241030b8040c000c15002c40b10000c809540140070817945d403489002804d0010540190004845205a5000d03000b0320103922101c600e8a0003811009800e810001112070f0030b00060107490607c10032900c1a0740c003503101d007000e14010f0b5802d0807882c50801001154404c119060768084403145403100c80e80700000d03442c1c5400006591410035214050030400b00081c010030040b4500ca00881100d002d40003c0042e48420010403014060466506000881d1b802000c0360380c85e01544110b1151384002e10f2250411403d400150a4a03001d81c02a64000d41c04001000800c0c2c01c001c0159000180c418130303d10980401002409600411314080d080550318002d41100301c0750002c09100c0b18003044202c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98019226 1250 98017976 98017981
    0x4060201050105030d0903030e0f06270a0801050c030708040606091e0501061407062c1510061403060a03080c030a0207050609060712020312010e04023c1503 69
    0x1034064003003846140c1c040c0c17003545020400305228290b480d00f40d80d859602c83c08007003055810050251095005e99a00082c100309841400340e0f0038043c4003005810300403810301c1c0307100d0a08005c02e04410b9400069030340d0502c410032000341e550034100d030b900030b41c1811b044116131101d0031f000300104a20b41000081e03d18044486000b4018502d810342044820081808603a807540e8003118840140e8110322011601409608005203164012800764030307040c2c600780c112824150000f19030400346191402c680e0425492050741d5003040f004291300c00581d00e0054001441c1030030042c0703045625140c543d040b04003c008101c1c555251a114401907810020709900c2e40344004c0050b4070303076002843c00d00140c42170302c0c0001058100070007034842402004003070508214094a0b902280401e0031030740401c5000400126090324158100307240a4500081000a60b00c0d04d403050004008085039450003900051040c840035591603c1501c040c01801d1101c1404107450300041303071182031440c0780d107914001c3c003108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98020476 1250 98019226 98019239
    0x807090302090c0301180e0d030f0207021c1a0103031209030e0d0c080c09060d0602030c040f090b04060b1201152d0305010501110604021e030604030806012015061504 73
    0xc0e42c10303036980e080d5403010300e200d0030540811180041000c41f40c9400a1480340e80c0140a030348100307881030000c1c4000d46019a550300080b12440d0304040301c195a1000e2021b0018418001c2204010100816141c0030650440c0c4014088425120045107025260014501058803881000c074203600c0250081c0203a10881c07821191018103409040f015101c0d0203074620407450304807103550203407801411000c5034032803a48805029500041c44022001410800081e032501f0a078440740091004081c0081c05413600c1c01000181d810903440031591001c2030103c01c400d40309500f0301d0f40c11101692501505590a00740c1904c0361401c0e00c8801e13180f942c0960b0200b4a14090f1a280b400c1083d050760100010f0b1b80b24001520444074007070401031540c6c865000078005040c1503001240c1c0e8021103070400c1c494612000000c1c980002124202c0000f04002c041c01059604030031045075201041c10074190906c40101d04560710407081c0840c600503856800808c2c01c913103c0101d0054000310b4075040641c3c681c0c4814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98021582 1106 98020476 98020501
    0xb030415060503030c07080105010603090b0f15130b03160807031410020c010c030501090509030f1e030f040c082113080610030b0109050c0703080709030209 69
    0x1c101003503d075001c102515182100800410b850350410485900f52407060b8000e909160a0005004c0020180360007282d20180c110426001d40c0d881c5040c8030406880c883d42705411050b01000b903030400030190010085080709808a68030288000107034a280c04030b030710903000140c102c0d02090000503910703840c0702040d490741d800704c881420740e031000da40481e4081842c09d021a9503e10000c40709070b4050003003e0041c01101d030301700400d00c2c0c6007c3d0241c5a21404114150b070f80c0e000181c480c41d000c030790705415403c03400740380700c0540f01e240c01000440109800d0b54240e0701d0196000d80040d80f0080021003041e00d400301038001c19501c607034401c6244650040c00007030510820014012900a5080007054800e40b8440341001440f49113040070f401880040e04021000b900b0102081800102401141c0c0707203903858078154003155a640c2c021207007030000307400c0250b101444200b404988640c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 97841726 98021582 := by
  have h0 := BRFrame.cov_init 97841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 97841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 97841726 ≤ n) (h2 : n < 98021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
