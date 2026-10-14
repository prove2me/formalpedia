-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1804
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:44:32.109875+00:00
-- url     : https://prove2.me/submissions/9da7868d-dc64-4912-bf44-3b006cce5dd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 324280575 ≤ n < 324460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 324281825 1250 324280575 324280631
    0x4021905190312230f0d0f05060102100903050304140307080c151006172a130501020c1f1205090609060609060a0303080c040906031202060a11091003 66
    0x2600a000b03001e51212021a4090f1508025050382c0c50139203040c80f0700051001403010f8000210b55450818110b0088070b8840d18440c0382004078003005442c0e000100010341d00076005109200c1c0b5014030442c140315802c1c01a81540307030541140d03030307568a0880c55181d40c1d14011050000f0f100440024201c82c01401c0040e210350094810681c04504030144083c2c010080c1e42d00c0303800781404002c1e01d0b030404480d0071140c1c184000000c4a5960348602d81c01ca14080f4100b810f03482002580042c1d4544e00d00282c1081c2c030110700044003655030341004aa8910303c01d450079500c40410040384a840400e03015500c81d507842c0c2d081c103800241c3e0a051410865000304c038101e00517000a070400076244401e0010560190b01110f0b01140c50030070030086a200e03505d40c0001400c0c020050013098041c6d140c201500c00600c0195006e114080d200e1428403a41c06190b1a001e000d442480d02003001c1900601880f400c0004036000c050910500d0b0301006440080d46000c4014507a940d00c40e0b94021030a4001e1003010849 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 324283075 1250 324281825 324281869
    0x70210090c081c03110310060f03060314070504050f060105031f120c1d04031b170708120c04060c0602030a14100f0501020f0d080711010504051506041404021905 71
    0x15520084d0070f60301d101070340c0d1480440810030810390903950021401910700f1403034040c64018900c0429002481540c001800c0f440c40102024002c01001482d142030b0741c02540c00344500c3d207400d000440310071b0007502c0742408a407007403001959001800d8070091030028120072285c0a20b5440310440880c494981c01030302c080f01c06010500c80e200c1074241941c1344500750141628a85025200100300314140c00d598190b0407400c00c44e060911003481b014512130395850340341613901d500314034007100254012010100140f642c000003c1600345031030162001c5400300c2d2260000506030341d80309002540300804c04500955940384103201100082d15591280d44090352090306141818034103241d03c03013958080f42c1190f00c0409042c454490100b10803210304914101324040e521072500c191003e41120310f041f0b5466207410100802c3c018001114400070041144045181d140c100501041d6082c89409807211500c14000c00c0060400c0301c02c00420361005031290313040d40c0d150000601d0342200c0700421b5001c1c041d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 324284325 1250 324283075 324283123
    0x30f043203090a0e06091504090203010e0105070305090a110603190e0109030912031e0e09070806091003021012020408011404020f0913030e01020111030f1e070210090c08 75
    0x7003c1e0390303000242c80000700219040c0340c0030b800144c00a200510300103225a106c1c00c0014607440759004440d4407a8010000d014000c00c501c3c00c9c0d4000d10040320490002810a408543d0410001c107501108a8010f40c0100c410822807050041e194009007441c605d02c04840c4840c41c031613100780b28a00c0055081c40004c030342e03a001c506000b0840669500215403200311194a040025000601400c46d103c486c0742d070324804151010107840200c006401290062210001c03c01180e9010482510505049496440726220304801c00c0640e0b80274000290080c401641c589240c90182d10300d085180710241c409444d081d00da04a560a48451115409101d06920288001c501d01105069142c01040c1e0f4195514948003040c4195090040b202805101a048a0708a40d034805c1d08070312120603010711281c2d0303681081c0e0319145a5141c101c400720b682d00b440c2815203506039603070742200e07000d040545c0c01030521841050844005040d40032088a07110400b035000900403109001e00c009a0075801c0740d032000d4070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 324285575 1250 324284325 324284329
    0x207081213060f02040b1c0213180e12030708041b060309030806030d23041d090c0102010c08270a03050405030712020901062a060203010911030f04320309 68
    0x3c410016024200c1e0041c4001e019603041501958400960309044401d44921090160002c1c40743e014103c40d080c01d82c0c0004562040200c4900683d0585080104a0000401c03111610303480541c1641415410410204030010300c1401000d40250064140541c1601043c0445c030120110b0751002e03020940319050001459000710049900601c1600600030442d500d0000608542003420111000c2c03d2141da80313203003000010142d030050f040803440b400a030404152107901180080fa4501c049200707080d030360306042d48103000e804032400903605e0300000303919201420458a1915494000c2d46d40a42e103600c40d030707001c0030010082e8050090b00c4031035507181818189410007855400c5103514102a0a105006840e00703c00d82e41112401c3c41c00103034010001d00344601da213441001c02c0c40207601c5610b0007800e200581c3d005504a074140c02d03003001484044110305299001c200c40500c040e00e400000035002c190013460004440080c540c3e120365100c49800c1241541a4440c0020504c0e0320120f4000418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 324286825 1250 324285575 324285581
    0xa121d0d0216050303040614040b03070504030204051f05220f0b010f211d030711010914030601141801060c050c060319150b0f0304021e0a0603020708121306 69
    0xc040b000210030703025041001095881c8100d00c2803804004202c4000f026000c0f02c842500c0150688680c1c4980d01d04090100503e280c00500003640300d145000082148001800e09081d59028100380010b04a4a440304108440341c0040c0342126079881004103901254081c40b401c00000400d6100080c0c0d040f40c40c00040038101c2290704103051000c000c840910310910260300e144c461880e40c4000c100580003151408507030300c1ea1900c40c600c611010861904124502ca00070b5840d05003a0380e610a070395030700c80029071100000b403030068041d04940e0042c800c41c0c004040a140b202000741110400407454000142c1001e401d911580c001016013101c4800c210b8140080c1009080c00c0b0740450442c105503004e04017089100290b184525522032200c20300c860244100030007800c0f030440107900c0d890011401c0d045a40100c604900c13404074200c000b142c003007500c02c0c4803800780000740c82000b00c0c5081030000d400950205000340c50620b002d111001c60b8881ea00a600c0c07191000e00c4507a0284149403030100d046e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 324288075 1250 324286825 324286843
    0xc050d03060602030f0a0c0f050f01050a020301062114010b210402060d0c0e030601080f010f060e0f1005030118110102150c0904023117030a121d0d02 66
    0x105400c1075010401d03035500000740c82a804240032401e603203d0405130241d0b8400c0c0058401048402d1445594003403141c0810340900b041c258000038031007a591b400d030070701c00ca1000740504000720389480c0000c1c030030456648141c40e00c030002800000e00c610128034104c0300504264860a01ea020014002c00c099100c0800303110303407114001101c0f41d50309280d80007c0b8640100d0b00c610905580e0f03518400329040c844c918500d0f4048019040e10001d5840e06926074883c2842c8410110641c200303600d01071807542520449040303a40001c040101500c80d00d00d5508020300207403801250305088030010405035130032302c10050b40300b0f00c0c4003003000e141e081403030250b03401c0e00c401440c0e81c10344d080607607041e140c02240352450ba401180110884d96805144001400a006043c0c2c0001401c10794400d501d20188805540380085d1965250407915a5032401001e09100100d0302c10035607500144031015140e80208149031070824607510105922400e0110340e00c2064089108408950040c400c1ea020281c062101080e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 324289325 1250 324288075 324288077
    0x82a2508042409090e0c12010c030b0f06040b0f19020a02012a030818010603060902030c0a0b0d0b040908120103060f02040b030f102102130e0a03111204060c050d 71
    0x41d652042c40b0016119010501c10200425240c6000c04201c40c4c040c4000d07118054000c000000c00d0045020483c02032510b4125900400d1900880309610b1400410307441c00e655000300f40518160420100d0300303083d04036502c0d012456074140640031040b081603c803c00d8220081c1e0007010022460700004080c24801c0386000410310b50401c0341000742115440762054503800d4100800b154903048910640f17000104070a05c0700d940303001804020000582c1140311914005c80446441c90444401c2141c0e44105109860808008004d84d0260a80e69006455076a90007040090000e00741d4854031031551020001000f40f00ca48801030040054900c5400744100305030b0811418032741414803101c0ca51101a1421200e207180c180090003441d80b408210018000c94280d00c030400743c01203010004008140812442981008000e0442c011280700d800b000300010801444034901b1070318140ca4850110502e184140103401040a4101000c6c0040c0018003082d5140381d09070205d828144d080000c2208840 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 324290575 1250 324289325 324289379
    0xa0b0112030314060d06090302070b0f040e0601050c0604031b060f02030f01140d061503021908121204030c020a08031c0617150a090204060e07082a250804 68
    0x951721543d1311001d82c00d5001e0b1001800d40b046080070703481e00090742c2c06801c2070100011000310b04240c4801800482d1240c0954210b10f449410054405004105010b800380c6c1c401070000e00030910440c4005084600d10003064405020742d201c01c006d803101100000c1007550000280b01880e04004070050040c2212101c0080c02000c9400140002d46d088001400450311034440540e02c49500409400859008080780300c5103024006413561109541700740c11050181440c5002c9049407030742141c3d14010200350001c0c15079030301c1d0340655030f60943c100c00341e0700140040c2d404160414200001d080200340300d84401000d282c0950980706071501c642002c01720b07514200041c4009040020520030319001010100c18590307841c64504002e0078220300103540107003003050000e210045241442d018800a40d598160381e41c0380d0884d480000790b40c1c40400c40d030700f600101d105e894040c90741c061b10384060400044451145d111030b12424840c0d4091f000d417141c0b040000c2c2003000c80c19103003551004c850740305030b10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 324291825 1250 324290575 324290581
    0xf060907080c0318100f2906040312030209181909084f080a1709060706090c0f08060702100c0909021204060b040b090c0c0a0b0112030314 61
    0xb40d404007420740c1d00c148210610b0508103010602007106419020f180802c5254040319500003e440821860b500c402e00014646e4400840c2520b0411352180c060301c0d492801e80345980c2c109401440e000004100340d824020004969541d200c18809003810700002d0840d42810003246020140b1211583c0036245480b040b00f000804e40c0050b120b08806c0c64186a0b881a8503004080a41c400c007900840616098280242407041d12020b0020042034030080a45090320350f00307200d541e500030603000740c80060129100c11100c00300e40000c05490002500240c00c12489903215815603001c1074048851101c440340500120842c41c03506401022102c0003011709042142e806510b03102840340894038643c681414001d0b072801214000000d25580b41d0455503807402840c0d048400700140c6045528504020381c94905281a00030100b40e5600105080e080d9150800441d5907a4000c104140050154164082c0855400051240205003600d5038000c2c2540c14a0010112101600d03d40702c1e5142c00018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 324293075 1250 324291825 324291841
    0x180f15011b120504051008101202090a09060e01020d021c090c14010201110a0c11060f040b071b180506030a0b0604050411130207030809150f0709030b0f06090708 71
    0x180c1c0c850690410a00304810302050b10032901c0340705603000640c22250464070034883c1a840300b11140700303032152006000c40c640c4a0502d2820000c003088040c3d80300c0e054030041481c4888550060030064498070000820700103e04d842030aa8002c07ea001daa42c1d1b90214a550b44000001001c882e80700c11079404110546003030343d500c02100014010140c90001040800487d07900035405003400950642d0320580f107400110004111a4242d08219102e40da54102c810721814020140e07100c4a805000c0da904040c1800b02d2a003683d040154240c030918038085012a6040740f514103000501240e13860700007882000b0106800307640000c0c2685000ea88107103142c01c0801c0c0c0c404103d641019007120041510703100c60070890030140c82100020390041c0c04621100510820754014a4414404d8917081c9056807460522074031103000c8a810801e0103000000a0305c12034040d4a803903804405070031301b01045034603521141e0381c0c00b1007204c0300110101c0f00b0043c0603480c030303086400b141d2007a0141751003011407401e420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 324294325 1250 324293075 324293117
    0x120506040b09010207050613020f01081909050c0a080607080903040501080a0c031b050903010f021c090807050d090f090b03100c09080f0105010f05120d0e180f1501 72
    0x102401101c035103808104804801e404440da41600320f0102e03561800c0882070b2001c203024884040348582c1c600c0f01040345a501842616215039a1523051310708070402c1030000409000c1d1420300700c1e410f0080e2905140240c0d2182252405801c25800070038451900002c06803402e50090105100c0d940103100030412070380d2000c6503560086000d98040307107a031514441030700641220040c610b5003c01001c20842d6581d8070002420a420088000703000d5008407100003401c0f8403820f82c249100780f07440011140704807640c0d001380240612580d034480c506240c81d203c0074140003841e080740f800143d01820402c808030500c0003107030180c100500c0030031402c00d06600199881d440e540d00c1c144846d0f100c0d1071100c0c070076014105aa0091240ca42900d103030b40b00c0000300a000b05824003800050985503140071806007044280521000c1140000304a1441099010781d000c00400d4803082c2d0008014010360448c150340c0d5105401007143d20010b83c0c00f414407a0090100c0c8040c0d00c600343c1005a8081d00c441030199400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 324295575 1250 324294325 324294331
    0xf0a0f0602090604030605090105192009190e09010624180b0f030a154403090901060e010c0b130813080d090e190b0a0605040807120506 60
    0x1120060b501d40448000c1281030003680c3c0050951441c100820000e894190007140c8200128861050107032407402c02c400880700d5002c0c002c0b11701803d44200a140d008420004c14000c10001c11034001d60f01c02c1840c3c100d140c506600710249510804040c03002c0c00509008060103060420044403900f482c15440422005c141e080f40d00c2000082d80d4403a0745481c9086910b0058859503d10395541d60309203528102c40c0c2e10540395845d025240595494903407103102d484000759118460310f0180d8101035003250000c086d0203400c0e104030680d000d0365a40700c03000036444101100c581201540d101c510b01010401c128005034044000e2141034000142d442ea070200704c900541c1c7d8405001150b43c1c8070041d00c582d40e07494180e4014042d06c030009102c02d0840d60905d000302290382c500c04442d20541c90744001c07500ba041c1c0e4070440e071030440c001000c101041c0360031015410078a5400000114900507400043e00700a881c0d000c00d0102e8400101440302c00002c2c001100a414008541c891502684d90392941d258001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 324296825 1250 324295575 324295583
    0xf0403050a0e0a0b0f130b03090c10170403090617010509060d03020f060a050103051009150b030f072408010b0f0702030703060f1b03090c03140307060213080f0a0f 72
    0x2a102c039103181e5480542c0700c00038144070303c10940c441030614103040721135001c40302042e100820740c000021228800800c40e0301c9015100302408985100c1d9090207058400010844180b000441c038075195030f18500340c101d103d0707030080e5035091030503140c01c0d40541401c1260b200c030240640014014003664440480c2640c1003203081d980a06003a62500703080703040c030740d0702d07054086140260740a00804c244030382c01640c140c03030246065581902216103101c0072101035110003488608520001600040264054156014003805503010000509a0700b414490540c1000d15410390340c401802c8190550214892500da030390411403425414511401c00901482c40300d0915038400282040031501d00b0321080000710f90000043c0309a54805c6520b5002d40074820744200301885c0d02c4060b90381903229000b103911564020700c000c4002811a261105100d05403080041944001c2040100041491005100041500004030b42141c2801c0100b030501c29101c0c0d0b940401d070700850fa0300f80414262000042240c1d40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 324298075 1250 324296825 324296837
    0x60307021c120e0d110d0c0305070c122003010b0f060703110609100f0c0e120f0f07050a05030f120c070302040603060c030f11040605030a02090a08150f0403050a 71
    0xd50100701c030700b4440c80d000c103210107003814140e1052141c00610414040940d840b905030458190145555a545181c07690b80003500c1720b8028004a801100201403881c043e100289006490302040f100b5000d09410403220f841c1d46e0241c2400e400c545e404450707103102e8214020301c0000c1c4120700242c070308807851051a00ca203c1c0000c2d48001c1500036a100811a40904180c0d04140781c0b803040641c840b4030a44084c480c050034000303c103140003030380d00c510f18000000ea1a400e441740003000c248001000300c0c3c500030107a48140321003410045002c10856101402c2640200a001e0904040c00800c4400d5031085029a00c280106a100c04001c90300c1d588c869107008100741c07034140c4880c120345030460652000e9007141c601000442485180e810040c4541d05644042c00f0551049201208948440e0f087c0c010800701032006000840c4604000d64101240e200050306080c0344e84002444084940d0014485078002d00cc10000c1d1130380c02000503480344220718001c000780b4013518050841e01c2040400010022 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 324299325 1250 324298075 324298123
    0x405060d021204050a06051b1b010609050a020c0f19030807020a120504140d021323150a14010c140f070602010510050303160222020f0306010e06030702 67
    0xa40c180e50303a101c4408000d820350f0515081140c1c82c0d07100b915007554058103082c0002c4034200c50a07020170f51224050301592400108041c01007a00d01e410030074600b655282c140004104845d4001c0600645031301c0310040c5d40340920410b561402d4240e21400c90306401203d5030301e90001d04000301031209a054146000d16644001c0b04a0800c540f519000f000300c10480320310010315a00901605c25a00050094030941c8004030810007180d054144c002d5000d682c0840d000c0c49078030150440c8400020010900b0807030740003202088100740003280c00d03008074030799290000c5c880c0c80e28100c050300800310794108200c11454580020500888140b000e00340c40f8a02e080c2d0360f200c80342088148024506d400070b95103a01e441d250f00174040c0000351145181e48181e1400440c56150100407a0041001201b142802050079404e20a40f40d030003010909500c00d0840384000400c86074001864024000300905c0c2e5030b480d001c000542101c00c20011140695000d008001d80d0640024549020030640c1c180c2408141e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 324300575 1250 324299325 324299347
    0x7030804020d0b070c02010f0c0c0303030c0e0618010e0d0c0911040e0702010f060f06021011070f0c050301110f1e090a081506091e07020a2103110f040506 68
    0x80020900901c9403900d4400c1241c0158407844070b0205e070340300f40e0314280c010007040d400322046002183c001d8075440040c501040024080c0e44203448001d401d0600789068180e03c00050910b40100100a04a541e0020450315641c2c0c400380c0240f46031011544002040c002d070720f5003071250700380c0d008000000d0354500d0303ca952810a24181c4000780040f40c5184058606104000d000c2c00a0b0403c0322a820300303098002c607219074014109800e585440d130003081e03a059140c00103006400078040c00700c1001820070680f40401c0300d03410b120f05114010145440801c0c6007000381401c4404c1c8400c01c40116200b8000c0701405400d1108544c01d2441d11001c10100642c0300b1069011803207031641d901d80c0401e00c40d4000a6051010403115616a650000b0030496607580f4240600002d081711366840701648441d00300010721b4000f8159801c6180f41c81282d00c1100280e44010304404000e01e61b100d00010101206d2414ad80350103600e10340360b40300e04001e061218010260070075028078001c15228540111758035001c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 324301825 1250 324300575 324300589
    0x7020703060903050f040303231c181a10091107020d02030114011409010b0c0c0111030c120c010b0a050109150c0b040602090114090307120516080102040f050102060108030703080402 80
    0x11108060551b43d03559902d183c0585145c01203118030b40c4031890080c1000c029080082610101d00600404481e0140454910310003050217103050b1941e02c2c0b0201e420008039904d60a081c254480465880d0f21070300b400703c61420350800991121440c1410038400381003151001040c0c070312459043d110110030354802d2001901401c1c1d5061580d42c0f114041c0000101030366400003501c0c203110156101107280c1d0701da4544420501c80c0a0780d03a6000e6000c4402a145035204003403400402c1008400e4901f0590040403050611249601120048801040c010b2112000f84104400c6200c1242e00c407031014600701c000313080b1003240d114003001010041419044d2030300480000203200c1d400310303150075940341c58508480290032000a580c00150900e10540c0701480103c00c440340c0280080c02001190b1405550010141c2062001c0365030340640c0510003d502041c07040000a800e01500240e180d41c10203a1405900368a40c0c0003604660110004110b4108003200722a030594040c074107040303640e403030703001281c15 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 324303075 1250 324301825 324301837
    0x714120319020304060f0503060a171207060c0305010605070b07140d020c060106020d0c050712020409060903090e0a200903030408060a0b042019020726060109050702070306090305 79
    0x11007804407660800c442d404801081a900c0f02d0f202d000e040184410200c8050100700d4802d5000151242d0911081e0406a0f00d03c4d9841095411117541180701050078100ba000744004981040d142d02014010541501809000d000c45141c254200303200740c0c540081414019040d030090001204881800940d1f500403660b01c0d0400e42e906559414041e4105541d54400b480344030010b010302c0c0250044684201d0381c0c2815503802234020305280b41864030480702c1100d10036040740d001c1e94420b50302c3c000031041d000d500c401c5402600c4a03411107280112150301002e00a0400b00801c0c0f0300f1043d04180040603055040b110400c4091988400403100413902d50710450700309001c948940f100700301e240b180c1c0d500072846003941034a051101c0c62419080300442c06403481501c000c120305004208490041545901a65000c0e10490304040e07a5154040020214a60301e5880c041e4058161810020301f0003d00c0e004150f8030b1002c00251520038402505d442c85400000c05840d00d9034542c40a041c030800c143c0f02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 324304325 1250 324303075 324303097
    0x6210f0703031806030e030f032701050603390a09021c11280e0405070309051e12280f120506060307031508070801090308010807141203 60
    0x505503450b810301800c901c60a40d0102000c0e00c0b825000308486200e40a19480d07510404005d60824030b101e210056107030401440007403405540040121000f203411b61110a10003031400014407030070108141420262168810142200015a403900540840395800c04600241c480a2465811180050f080c444c459001003940e42c00819101100340c0c245030311103021030f07911038100040c181c0b041d00e03218240240b114004e030600d40d500c80c1c82d00340f0051030028200b9840c51300d0040784060380e03440000d045802c2554540000303a56491024104035007002069200588521400103030307550b0050382d940d01d8071191464881c264011440c079588a640715241000340610b05105400c2c000036110040100b4600070a0340000f440324640c1c008549020300c24540640b002801e084d103145d80b5088268040d107404207001c100504081c000042c2400284500d001402c4800c0c00071070741884030b041c005c0c16813006800c08042c580244c0d01c20440700034280818421008280c4e1600c0210354544850703401d5014140b9220 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 324305575 1250 324304325 324304333
    0xc091306030f0602270603010b0306010e040614010f090305030a050a050d05070806010e061e0a020705090112210503040201030b061911060a0e190203010b0d081305040506210f 77
    0x3c108081d00640001d411180101c04804000318280034092540602c003500440308100500c000c1a018009540c05441030511031300d0001c22001040444100d0b07400b82e480c040d4401e90100c40c1c0c2d85c0c82030454010200d20f1900c9000d1500b542c07141c944911500ca01c140610174000b0f00c2d03070f01140c080e4040e51140c100390070003049140341c00d00000d0082c440440b002c5000401c000040e860900c0c1400035929140d146000380345803004600041044c9034408802c8a083d0301c078156000520340d03212004103010700b900408907003207500c442c540f180540c0911843c0048031482001424185507005040d82d078050340910300422074a841d0b00200e4442c6c800c0000c02500103080707070b080344c00303003031b040707149481030080001c1295020ba40d4800380c40212003045109403081e4101402003024250303840c0c0d10b089024001000060303445100000200d0449210004440360240821445866400001c021000300f40a075001d01c040e1a00700c00003803400c44081c080b4480080410114509030311708000c05101d584c0d4031801c13a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 324306825 1250 324305575 324305603
    0x317041d0a111602040506010804030e09070504080d0509090702191511071202101a01180f0e07020d020d080a1e1a210706051e0f04050310050c09130603 67
    0x307049000620f0320982c0103e0400d00810055440f88094038822901565103040e554088400c01c42c3c0700b030000d4207180c1000420b1002160112060004d0030100032242c0390301e40d03200514018000b880c0801000d09045d5080342200b055045441c41d801c480c03091380409000511800304502000401611a00e100d07099004903150003004a441c019100c1c00304540c0856080404a11801c000c2e503e84048030180250f40c41000b07100755002c2d012503811048880d01c1c0440315a2034907140c0b98030005a0348844280b006a20500c820f00d40c05000c440c4425540f84050009440f100402801030704000d000c8002266980000b060380309012588400da01c00703203a8061107000352003400c00580c2403400907050301c02c1c424896107036000e2a07003000c1d16910b4501d030409001158500315007601d03d9040101c22540c0e254008441000e03070500003008101c06581e2204158569040005141c68004401180041285041c06100c0111314903825202d2a000854040444403900340301c05014005550000780000c5c1d04140c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 324308075 1250 324306825 324306847
    0x150c071b05040b0a08030915070f0c150306230609030601030b010906080f1c021504030f0305090f071503020408032107050403030c0602071a0405070317041d0a11 71
    0x15510441d1412581808050032060070840040214494400c0b03a0b402001070010a0400e81264180c0d02c54200400741006503d40304c40a059081b0f40041320500c0710703003005202048401c80440c068098500d03041160a05020103415410300c4400051928102c040e09440c1503558402128250302018060710655650380c500b500e2110400e001b20040281031250100b114040040c2d401010305690005080c01d8900504544440d000c60f2031060841c026070740220140b88020494038002c2d0b1007552042003001e0700410003030880b000680000358a400c0130641e9400445c001407941c05907000c044d4003040c0c021080c1c070f0a034000d102d698821682c80c00089260082000f06440e540d0742d83d2100a08001d50360744445c4e0440d15407069000c014041181e05596401051280c1e014010181c82000000c1281030720009450720144100d0381114603a106460a0040042d0404d100b180c0d403641140b45800c05003480c00101100c402d0091038600503441d2000140c09903800d0700100c1d440c140105d01d841d0748030360200d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 324309325 1250 324308075 324308123
    0xb0103020415080f01050f0a0903080c03040606050a0803190e09060f190906170304030201020d141605030a0207090c0c0609170c0313050d0201050405042d0f0605030303040203150c07 80
    0x15108041084910015180c001072740200340000f6416590321819503500c0061000d03580024005452080c0d40b11800300309038503a1407a103005440c80070000c6440f180c01d01003c4010060311040582045201c081c14026901d641c60b000350041001c61b035090b0481e200d040481c1e030085450f451800b2182040b840040c1d400240c1e030001c026500146056040721089200035503482c401c0388002070041c6d0010f059004880e1086e24180e07100000c00d030249240c03202074540301491000d180002c0d107958000248400c807007070301008060002d201000051124041d01c50014007610050b8001a16042c0c680c442e210802407049220f460040415580d59210000b9165a03940c9401c680c000c1502035030034440205030b070f180600400d850709034140e559130325150824003030201500702c1c40c070313800b503c006e01d06005642d010041401081d1852520720004000e690501d50909990844c4d001c180250810403c1c040580c80214482d40201c804104d0354240c1d448031044a41c3d5881a40ca010f00b1100007080740000380c4d56403030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 324310575 1250 324309325 324309331
    0x30a0c05070504020403170c030c030a030c03150f05060c030d05070507170c030307030209180a0e1e0a03032d140601030c09030219271103040b0103020415080f0105 72
    0x408461041d0344440500c4120320032804046c0c05821807080001195180c07800602d85121000e050740d047c0003007071018502c0c40c0c0040f900c4002281d00e852140344a154940328100b17507a0348500318114a2440c1441e10450340d030190007103500030580015040f0545808200b161402000728400308901d140841c0010a41d0700701c504102d807002e10001c85454081000f105640d00e4264400c059440d58603800019402035008000b12a0080c01040c801401c40100f480184e200344182480455502a070303d0005082461107511080c40b0900306107682c0745643c0c0000d0300c4d8081c43c2c1c1400d0001b045039890224100703101d200c0b205010100311910303101c0007010b030540054814694905a482c2140c641e64015801e9a07102d51190000444070403041001d4500300840030265050140040e81640c2c135a1051140110241207400850880c8004802c101041c1e12400460401200907541141825502d8100802041c40f001c1d100b0354840c162140c0d90464001d111000744410001c54889130b0740c2011a0780604021 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 324311825 1250 324310575 324310583
    0x5161a0a0513051f0e0d1e0518090c0f04080d0f0306050105120a110a0306211e110d0308040203010606090f0e19021b01051003020f10020f030a0c 64
    0x4100480d1150000a0b0050311aa901c032026080103140c00140c03440b40b055414030560565220042c603007490000b40220041184659140b1303989085000101001c024801d41c2c5c601040b0082043d0910392a464040102e4107504441081d095180c56940c103080c3e0150100800c60300000080018962500017100d035a194282e45501568072a20a8103a084502504c10140071800c20015110701e4904906c01c41e500000c0a90009a900c071415106455900039484140c0829500e0106014030304002081d8503454200000a07500031074039036100704104204420314484074068101c2c10003004a003041812070f045002c0d01c01404141c0c00d04006207608001e4800364040e501c0c051010810b02e104205000584003003075105002149090360004042c40020804403445800c505c49007001e64042c00100308030980003210003540c80b1005021421140003511400003051160003c00050315508a440351008040f0f4045201704150401a420001031540d0038201e80000200f28404030f82200701a0740184c00303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 324313075 1250 324311825 324311831
    0xb030f01050604060c03180806010f0509091605011d0603331c0204090c030602041a091318140601080c0f06030a0c05070501020c0105070e041b05161a0a 67
    0x390300e0510402d03210318018080043e1741c40703581ca408a4007944002520100607180080710f03035601d4200c54281030080e0808402c05d4902602001185030003109240c00024500c0035004400c200501c0b1202d1412a10865041c80b481410001120482c0040c001d030841c00540b03d940e41c2d260070510f1b805012141a064a01012900b21002c601003a41412400303001010b891070b00e0200c00096400f14280d07801c5012644240c071098500005080101c03008000c40c480d804c0941c490341080030009101000310b83d510400c52007400030b000c86a489420f8400d042541280000d040e0301607140c41a10084185005071800c4203445110300e100d800000c01f80d048502c1c15081e11075101e0017500f000742e0560118205540030300d050010540c100b00030780c4aa21200218280b0514203605660382a007644c0028024031000e035511420031011a401424003a4111001c0746c04014016503402400d500c440d040a0500c100b103000701d1180c9000300b2500c0319402c01a0071224078210286105407482c03180b02c04aa921061900b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 324314325 1250 324313075 324313079
    0x1110200304050a02010503060301020c190c05031203010618052709010c0c060b1c06020301030618080d0b04061706010810090b0f19020403050a140d05090103091505010b030f01 77
    0x220241500d009036807140c068001465241c0044500b81c2000d0900d9515540c20082580b0280082002d116155502c1c40040b118006900389135942c0703011035011500940152031542503030080e26044a040d901d00b81428400c4419141000d44201c80710b400080d0480400d15050320310990203d0604009051810080090380e81c003030056003a600703100008004584c07408100d1001614981080444520141120020f1f51001c50803440b040030041e4150391403a40080103109010382c90041c00181e1040c801155100021565500124803a11074400009640d0310001010742d56150012401000b45035854400b2010148410343c844400784281030312445001c19100b01644a800745c0d12038103400c0028003d0603a1440c40304c1820002c001d2182d00040003d0200303005401c003034030140000e5409100148950042450290070300c0e41405052252a4801004490716540c0101200c01496080c6400701c0d5014862400000100881c174541c031b407160501001003080c00f0030301d01a501c100c00c0015285101d907 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 324315575 1250 324314325 324314381
    0x70b03182410140307140607020901120b090c0f09040c080313080f06060307210c0906090f0e0709091a04052a0102030301052209080d14010f151110 65
    0x110f0000c00076501500702c0002041648094061908007100252a00e860000145c2c00903d507100240c1203030580418003c80e00f01400310840f080b95000050030002e0521000d2039001460402c101d800c4184610042d40c002020000305007589401400c400e8116a101c1007030324084680d010303050003981028801c030407504188100018520f0300880015010301003c03410100390482101d00702c802e08215010510403c000140c408540c0c030000c3c4651480007429031b0824140c1d0701600c24803280c03429034605041102d00c2111020882c0000c0b04c205150020301000a0302d046d0800e119200d2094581030001e00401061040100e186241254111038010342420340950203400d2486819545005900a0005201a00b40150301c00176040809030180092601c54044006503000c82c40708440c107035004511840140c02d1030040c02003920720140490007540c10040f24101c58540c900c070741d08480b60b43d0318041c2c2d04a0701074641e8140014800c0c0c10f498240080007512000741c20140c10100c954a2007200301e242403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 324316825 1250 324315575 324315599
    0x3051b2106120d031e06140105030405120703020a151a09060310050a020901090e0c22181505060f25020907030e2b03050403050d2408070b03182410 65
    0x3d6461f110002a01041080046480b0f03000104200d500e4031640500e00c4260445501070058248683d0042c40614006c1c036142e4960341580e090300d002a8101071075282c1c00360320084800c000b044c00745c8900d0416651580003d1402e40da1007034101d01c0078a0702c070600140a1840c0c000307001001c02a00c801054540d6040c00107007260044501ca81c66403c144203c642840c0440c924001e82c1800c0790b6880b181170b483d41c0c13022405c080360000314042c03550341d11040070b45162a00c0703100c801084100c404130305181092000c215280700d0002c6240b2040308007044c0380300440c1500e031048007498024012085518000001134010301c1c040c2c12521b1188100e01c80c0c441e00a4110b0203628000b011003c1d03c42d4103000403039054000e40b0014108405005050041c5401540b541c402c02070700c2c41c0d030b568140503412000004480700c00c0c00d9030403100d156001f41d0707000d00c02d28560078112303500603001000449104c03c01040890401868121f5201480c001c00603140c400c0040d1205140505040c0e807003103000a40e00e84000c6d0312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 324318075 1250 324316825 324316829
    0x3020c0606060306060f0a092402010b030303090703141e0601090e060c0a03181b050a0902040608160e090411030609010b09010501052803051b2106120d031e06 70
    0x10140b4208100340906240074060901f090f2a0700700140c105444248201189807226020340707009141d40048803e066090203021046d0005401442c91400e040b9078080d202c03c11800f000e04500462070740090444400c100d200c40c3c215486110445c240c3c00011540d480724030078415080f11a040c00700060458030081007550090704103103922890038580070300c2035019002c0a22042d0390a030181951601003640d03070b1440203241828441d49800907007400100b0207802c9440d0000c040c41481484241f0209402c1f12205800ca04c02400c11a00c10504020850b086040790781411740007940c0c603082c40200607003941280c90300c0c0701c210107843e031669442c6903081c203c8520700740740c07079218200600401c11035008400402000420455151180c2c009005141c4203041f03103a1004e00295540007000658404801d007001c011494030398007480c01034481c00051a802c000d81c01d1181402481e00404c01d1942d8107207580c05000000345c141d5800c025102c0340603005002603038210041da408076048640f40703c101e01c10001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 324319325 1250 324318075 324318079
    0xa080d11070f141302180405060103141006090b070510151716061e0806042a020d080c03010b0a030239010b0901090510120b010503120307081302010513030303020c0606060306 77
    0x110721040b007c00000c0c2002a041c14141650b4440c049094016800d9039441071400400f01c0284510300f040090103140715038804001c9680c00d02084000603000714011b40c42110007040401c8440c42c000050342c10540e81d902203900541c00421103d211880031030307400c6a0105852070228640d03a18041a0b0320a42200c0030345103503a0148c00f22203c07085c020001c194002501800004a0042c2c44510781c201e0500e803000d4104080302e40b004000034a60400920000c5400e038500840241003403540c4040b1804103015011240c0008a9252181407190b4152014145146402c002812281c54040c1400181e08040c14903142c81c882e1500400340140103210702c9420150691109270310b0808041d0007014042d100c1c4401d01089180040d90a80545035484600e002c0d441448007545410105854040c00700c00444041d10140700b00028160004280d81e4010310380000d1a56410062004880910808401c03400688650402105040d81039006e03042c40e58042d02111480d0f100c540402c042404200e8000e9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 324320575 1250 324319325 324319357
    0x1a0c070201050702151308010203010e07020d02152d1f1404050a020c06090f06090703030e0d020102011e1d010212060d0602040803070b090c0a080d11070f141302 71
    0x202c010301740440000081e510081415042580580345003c0c1d544296002c11a169004401881180407038014941c00800c180020400500c2c0c402d0040c1d15050030000b80078103450050001182030040d003c00360b4803c40401ca80002d2440020b0000d4810842a0750103000b0b01d105050241420b44001903030401e0350140300c400000c41c00c8040820014101c01400407603190380078072a200100320b080100314060001c1c00c001e0900729400005941c40c00ba00106506001d920083c001c1010031b401c000f80b0646c2207403c2e154135000080900050703000d080140e40c6502c84524500905031500d0844c1d001164030019010001c0c0c005070005a00c03030a030f0040d0310f54903400c0000f24002c07580340c1c500780100c2001c0c0b42c41350030003500f09607a503031505e425604a11400d031200701e81c2c40100442c240043c803040914503811280c2420341418100140c0d074440d404c2d2110818003a0821007208203600400020700102607105e18a01603c0d1940314040140c0030840b64940902181e6800c400c4185090003520440c48405400c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 324321825 1250 324320575 324320587
    0x90c0105030c2503052d09011421060102120304110d05100f090b011e1a0705071d24010c0f021905030c01030209010e06251a0c07020105 60
    0x100030341c0304a443c0001c8541041080d003843e10489241491540a51201c0ea02da0400310900981d0400520b03100216240300911071101c1d00255081d240301c3c031001e03e0680c82030a40790b2000c501c20b10603500c0c3d40003100d0501500c01c3c0ca175000160003a2080d10b0a0342901d505118003017000c0c20502041d83d0041c203d4031041c0d20321210313040244c0e091040c1801101112804050070721101c04664104d00302c040c2403601c5207460340034010394901300c60042c00c89000326983e28100c1c07003090b500c02e28030b40a901c0e405024103a2628503401e14000391100d03142c11206036003005585101031550700340d8828100031360308500e5002030200300d11802050304020300f0f842c620a10755003840c01122815a000c0040b540c0b159802003450141c0c0f00c04070107007840f0461088206132182003904052400780441089410980100f0040e0b00d1a42d11407152082240d0954a0350348402107941e450300004042c6040144003021065800207100128050f40c943c51010a1059201e454010311311509214030040607001c16410085 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 324323075 1250 324321825 324321841
    0x6080c030307031b08071403180a0e06010e0a05180417031b07020a0905070804060f0e0c0405040c1203051803010516110c0a0605040801050c03061807020f030a030603030305090c010503 81
    0x413030301c0d0648110f120900c1d1200d05c0c1d0705c418903442000211102d5910124118046561806204d07288a104480620101c3c3c5071100342c42c0c0212004000f64104680142c0b401c1c0765032510540d0001425004004200005100c0b00c00c542d121401c48080d1104600c0400100f02884010100d90181039000c2560f11240505488007070243d0125800700c0c0c004101400c00140d11046104050140d41c0c0340c0c0d0742402c903040a007807040a440300f0040c0740c134540e460180171901c0003200143d20300150300c0c161000700311a511401c154410041c1c07503110014440c04820190101a406030041544e407075000c0b61042907400043c10b16088400843e43c81b80c40c000c4070300f440c0d00d642e4015145980e5110f0f2880c211041c0c0200d550100d01004895400318011480c081802e000c1043c1c2805096400082481e40c0c81c25480c02c0400114428242c520110883c0c41c410003080400b80309000221900000d803080b256502604034008000307201c103200580004c0d21307100104640c0d49000c111440102c0b41651400d09607284d01e8a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 324324325 1250 324323075 324323117
    0xf1f020f040320100c0506100f0603110d020a02011d060412112508070e151c0804060905040e0a050a02010503060414250809030409051902070606080c03030703 70
    0x8040100442d09880b50042c0d0f1490413041000025903248910142140392036841c00402170540b801d0b4281f00e0800380981d801e1040300c803048412615011513401014030070441d10f4401c601580000e00d000068181009405410020040030440c85000c040070f813280510745c5900702a41d004041d02c02c510f02030f81e00c11340728004007000e00036540191444d100c20144c10b25500f94280c441e03c0d00025540c0401c01101d0000e008501c01441800805209480d0558070560004040001d2900c1015080e140096000d40418039909190340141420b90f074a45415016003414054814203100e00d041136248510507001060005602e68814024280b040c865401501c003604001c09058010f951007651000c2948021111401480703580c14440d2052514840000d400324052001818040000103202c110b00c03000044130110354500f0000141174071945022042800c071495408042400440c126007400200e90201044856050072204170341054014582c49014130308000d000304014000110110380e8100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 324325575 1250 324324325 324324353
    0x7030803060604080d030b2701030b09210403050706090503030a030b03102c0a12261e10050d06091416080708060f01060e010c050f1f020f0403 63
    0x50070302d8202601c0c1ca490a10b0300c107100700444002a142d000340c00aa017016044c220700104c0e4601c5045c0c5406107003232011034521042c03000900c1e400741080003c000b940c0c1031090090f600c0c001414042c800d40442c280d1880340c1c120b4001030f1014001d000000400034018030702a4110344028016509100c44001c003680208818031a1a425001d03026002400081c6407141c0000c100b401c11080c8000f40c02c861071682022114402e03500c86600c41d80304080030134400c1c03a038140701000e00d1038200d968600c03400c414480b0360b01c3c00101c01c0c0203400c10780c180150001c00082c2074400f4819841d1441070355403100003201da0201148207003034111500000080110303400e9001500706d9401150050442e28458464924104003503c48200c3e125148406000721361341840650f0040100c14020061401c18200880b00610184030351000d1140c201119611a4012100190059040016140d44803210322040b62610700c0e090107001d80b1840c02112180c01c484038030a030f83c050030310b0b190f075141494159503402c3c0c102c010b04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 324326825 1250 324325575 324325579
    0xf01120204060902030a0204090609020906040e0709080a0c0303021005010b090613030203071413060510030b0d05060f15270403050d050c04090e010504050d030b0f060c0c0108090d020703080306 85
    0x50b68045616800c60004501640342a000180e4070751500c80c0000484016400c034144050041024060542da50300944d015600060185a00340d05d47c00b800780d86808440c3d020b40d0a80c0a000709800512445149540840c1e0098090f2064031405486417800c90b0300034001ca20264405211000f02402d00c00098090b500c0142c01c04280c1985076000a843c00019900441650400c030800c0320403400c010002401c2e071642d1907800d0220b0313030502c40043c0c03d13100e00516440426036990361408943d514401e40b2046960031109440c43d170f0504007410f080443c400c031f8a2030285859040500240c0c01c4ca0340303001920401060b0070304205803040c020b09003c1500078109404014091104042600079485100d0003003c01d240c00641c0c0e00c1ca00b100d21000c4d59805c50703000c4510b0b4505000c20010401c0072030001c5e03010034146000101c060202d07000603240400d01840d90382014001c2129124094002150045540300342c0740c518003982c8100c44140e94100c5100904016045130900b080018030602c0916041000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 324328075 1250 324326825 324326831
    0x32a0e0303070510020c1504030507080d06120b0411010c03020601030b1e100f05010e130f18030c050c10140903010f0c0305070327080d0905060106180b030f01120204 73
    0x183d1945803500c0c034100b1301011500d078002004208550700304025140e03540d2100d0b0811041c0392a85019141d03026401c805040301c18009009400504240d10200c080d010151791918003e00034140402c07d42c00031a41202e007288400442d0300c00d5802144602002c60345903009010980c21960340303c0058801070030b403540201d40c140c8000785000346038041c0740c030540c1c80004102140745050039103001c6600300d50002d4140f14000031000d81c0d94581006406a0200d04040829412001004180141425501a007a040300310304181c0c101607201008260036030107481140e80300100e110800610b40341404d0200e01040d0b445003214040524034015001c8900010000240b240380c1c00e0401c02900c140a10390000a581d0f88200401540c052060b401006c02507600d800d20401b000c0c001c65105500031501800e2880301203100c004401c5a504040c00483e808000c0e03814a5a5030f20000e0103000381003213000d1145407005404a58503101000303881c8111105440f01069900c1c0c8110402540b842050981c4c01c140c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 324329325 1250 324328075 324328087
    0x200d06030212030a080705040509130c05130902030601090c0f080a0e160e07020615010e0f0a030c06090b070224070606080c13060e07032d060303032a0e0303 69
    0x1559400000c1e541c1d01d000040d50795404a65401850805e0084c40b000900006020a10090b100d8003040d0754021500ca20b00100c140361400d2a011040b1030754403403a440f200800b1a9490000160001103480f403017601103a0659813200042d00a4916920007100001c08005107005558403410803203030088500900007503014041c4040c1802c0c144881c00c0f03203117180480a010000407900c110074640c4100d251000d400c81d030504014214148902891050400003005403ca450303076500d507002524400c00600d0311060713981e02e04e400094040e0920440000c40c01c0c8450010303141c9a89000c5400e4590f00a0140c0b417581040c2403a8007500e0308012855440500c2480b04500040c9c562041401401002d0000c5c0b400d21a1a41000010030078424125140e50810100308800d4608889058203c032160030041003135180359074041c14501d8090406400305418010351480c045007039100100ba28002d1b502801450301502200284002c1c4208400120301094480f040e05e6100c1d6501c800d0100005050303c1c80c1036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 324330575 1250 324329325 324329329
    0x818010515090106031a150d022a150c07060e161401050c0a11030a1a01060e040203130201030e030c0d03060e090f3c0c0a09200d060302 60
    0x440407500c000088000d20300000303941c5080c012881c0105031a107010712400c0310001400c1903003540c04004030f00590048a109144156203010b507008a407141c20115250700d0f5044114480d440d4038400043c0b030300d0a2808000b001e00b0003160f5400011030f4212840d4603626420800009640300039420f0301e91035540c143d655610f200074070400c071540107011140842c0030f04102248a0700d030641e1038910f041c000d007004418100840802d052a802d41c1141c0c0c260010341c1d403400030070b09002e02c008005061490000c2001005110012900c0c1600d10603501d03000031402601c1840128801500c0203070200b0401420303c00103600ca41c1064402860480a4900f000710292216140280034607111003c203803100c9040c0f12490040c040254408440f03c010020300c1028031141c6d40f075903500702c1c1b01504400c0c0c1c44100301e075801030b151007820b00e0642e803030003019080da0710907048d511707089050341d46c40c400e1100e04000100d081007405800984000c0307402d2403c1480c00203200c010141c0c040b03203c858046480e00000000342e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 324331825 1250 324330575 324330581
    0xe04060303080406110301080d0806030703021503151c020f18180c0d0209041209030f0303020c210319060b030a02071703010e16030f0c020c01030c030908030403081801 74
    0xc41c440e031a80703442420300f03141400a440000a032690707412010b000400507080001401e02d07490a1030f0030032088507213407800840c1c1044225040030f0341128050070610307400c141c440e00952180c45038001c0d600891010204000644848201c12488402d00c0c03182c2e8400b43c505a404020f541134020003d620102081030650400e54040718a60314001c075038127016414900500c0b07074000c001001c6a003000141c43d940d000551400380600301401404d04507020340c0080740610600c01c007840c0c101c01c2c2c40001441c507150080196001d150408568040c282004205015400301403221242029000d41503949001800c0c0c505403141d096101d103245c6491000034100d90080046000c2e0b2400d00c1c01586e2121942804d41c0c1d4850301e5040035004901c01c000402083d41c8004c540340d0000750404a0070812907066400720050000c80541d0341c00e40386040c6502c02515000134a0712003060707080e2000c0c40440042d0000b035045692522002e01010800c0001030000f80c403e8861541c8485c050081c68507002c01c0300401da00b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 324333075 1250 324331825 324331829
    0xc010819050711210409150305121b03090d08090a170c01090b0309031e07080d05010302190305251a12060906130e0f0f06010e010f050603160e0406 65
    0x11812104810f48030410030b205602c8000c00703520f0a0198030b602c00c510302c00d5522691180c903038010383e0341010721003080c0c0040711040190703080811a204401401010103c503401100f0411240d44107000c3c00d10404d2011040d11640080109400019031250300c502c05030f03501448080e9400a00b0f0780d00400c010169010b0b07420449084001407414540040014104103000e40011724402000c2c400c211043e50000116226403038803030040111700386143e510201c4c50003000b00c01450f00ca400300d0b26554110176503120728100c9000300c800800d08045101c00c4112948c541c000035200d500840e107008607588043c14100c005c809a80c0d1100d0b501c0e941c038240700101d0303c41046000505807000480400c3c0b400b84070000c54210310101d4020b1104e00f00440045e44c144481d04904812a0b11101d003d001170805004115080480c07100380c48a11003c80c6107192160401d0003200c400000200021984441a0601d5429220064826071950305c40c400d01c441a000360f012250200403030344032240301c1c1d0303183c502903140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 324334325 1250 324333075 324333077
    0x105070f03110a05061806060a1809020a15020114060604091a030609060a06090c09180e0d05040806090318060d020d06090506040e060702120c0f010e062202030c0108190507 76
    0x8175508090f4002c03078048012544960641e0300c06400e0100035502c14203000d0484201800801c070b05945007003d2400341001003806944505a010000f03407014590015a403212805d900810003003144030b0725800325003000d980c01134204d402480140464182030b80039110031046075100c1d40d0140d00b8940001d1030203008a4040358a600020700f8800003040a0041c80080c02a2042c1840504c81c00c43d0000e2001c1002d20508061508810410303a8012455000c80d0050070200190389941a003540e0181244c0d1140c0f0500d40c0c180315180000b40003580c0442a120014080c026403103580c0c0e07a032400c0202580100c410000c1540d400c0081ca00c000c101403051000034091854041940e1078402c0800048540104100c542030b0132a80401980301c0d40403505401022002d8a841e03102c1c0304003040545043c0c2c5a02c0482050343c0782120000148900082451041c030f2a030804101003100c0d0f071405d40da20035002d040250181d210b0348108129600076110709074003441180800c1c080e030340e60425000c1030320001d0314440 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 324335575 1250 324334325 324334333
    0x31005041407080705060a200d080601120e030702060304080d050702061b07120810030c0905041704060806010516050124170303041101050c0a1401050a0b0105070f03110a05 76
    0x9106582031040c80000c0c0041400303402064036010100d01c0c0e622910700e11f20104006604061017965905410300d6115403540c0890b01c5510062801404c200c0c0c080c1e9886010540382e41c24442c1c242280d0080d0000503031010085c50030101e07180c4c203100c5540c2014200b124002402e02070400d603d641c51040b64450400ba034001c00075030a0480c410f08211602101e03013180e03000d0401c009008120f0300340080c01c020909103840781903561104603070102c0792415003004242c3e21768240e0004d90300855030041c0c0d009a000d0030786080043e03524810b50300180700780d104890104280c0000988258044e030090706800c51207400c04030002e56181e4849007100c40e205600343c040e1111030300001103101c00d040044007502084101e0040c900f1300c500307003503640e020040006001c0842d02080d01c07001c1e4800c60039155007824101c1101c0700c0200a240000c59041075076003564640d071030f110028007200014040c1b1140658182c441900d81622500c4590200e1501c050603020321901c40301034085100204198a4040e000d403002d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 324336825 1250 324335575 324335603
    0xa12050c1203070c050f0609090c09030109061508070e13020d020d120e0a0503191703091e011104050d050703121d090601020d0c0c050409060c08090a0308130203100504 74
    0x6136080181038001e68084c484072109902076494150031a402c210b01143e8861440ea5081000301c80c600c2002c079071036010750038140301c04e08200380c5170001300d81040c403601084403080e00c510300e0075030310105413107031070413442001c404200ea020300c3d28031180010380042c2c0100d0191055402086250600341ca04903682c03511481c0c0001829840110000c0c0c4120440b111030280c0d281c08000b0380e80b2140c10b9041031940700d15182c40c1d000c00c00c0002c0880b40d40c100170035007952240f5148020a8032040e020305109403e4004e11014403541d40e042c0b02e542c00b07400324090814240b500301400c2c400941e640d4601103560f441a61008000305840c8907010b500d0040c20354810b0b01c10034541d104290b40b00c0a42e40c3e03840c0076081c0103040c840241c2e0085041801c5043c1490403c40901060410446c2c13260940c2c0055007041c60f03c000c00d070510003036401c5030440040c40e49546055499032141c2d1a618010004040c0000e0416401700742c2442941c600c03802c40302c1c00181151100c4418a550401701c0d001980d003180c00000038104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 324338075 1250 324336825 324336833
    0x406030b0108061f06050f13060807080108060106021905010b03011a282c0903031b030609071407050313030203240c030604060335090a12050c120307 66
    0x5404c0d031000000c00c5500b141e100d06031025450390030900a45040c40f00c041400e4600d01040f609403000c042200e80ca07281847d40d0340300e010f001024252801c100280c2501e00108000100042da1412140c03643d0050056200b118201d281c1c003140c02c03104849654956410174129a0240500116103c2c5c040d0300b0200015030500b0850400d1b00d00d28440548032a80b1401c0d2400e503550404241200d060300c80140d0b0409522000b00f0000c0f442900321400d003105c00082c070051981c000080e40c81040c280e1005007142112201008035400121b030001d81c42a808000215424490070310780340141a40300c002c0341042c51660710b03d401c6130400c0e4003031160104103810030019850100490048045121108403400030050085803840c1001000055803070300002c0032501c0c989507513100400450704860b1040c2c1030142c0780d8004d1880149203001100d00781d0b1030412750000080500440702804001400030a403d842c02c40d43c072486603240e14040e10716001d09010030302280c0b1020f0041c4a8907a90b440030b95540d104e203181c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 324339325 1250 324338075 324338083
    0x1914091801060f1704020420030403050c01050606040509060112060f080303090c0105030c0a0318021806010e0a140103050910020a020f010c020304050d020f03011b0905010e09101502010b0406030b0108 88
    0x103001d800b04414130071210351003111148620381150301a5808605043c2101c1083e81c00c0e00407804800740c044001040005159002001c0c2c0105416040248000d40f607500400c03180e80100d0044035400f900360804105258020081c0070803080125001184c010f0303403030440d45500680f56100f440a500000100500031009204000d00d42030242425415800c0000b0483c00c24003840d819034041c0b503a9103c610340c81e03a901014410100d5070007003440d0780f9540d43d210360000d020015a1140d0200e400c010f0406000c2c6000c8147c001604c0c0000e41c85d00a5064510044000d0003001d04166014060308180c122030007407900060007103400b03603002415034114a02d142c50844141d07440820454100344002d004641d144000084051340403031300c00c9a2580300900007401041008040d201c6814100409110701d6000444041100e009884600140c81e100c0b00f0300c1008031007111180c0442d9280030382801040f50703a84020303019000508c0001240341c0e00c83d0114045980c0d40d00300b6212621140b00400007118108 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 324340575 1250 324339325 324339347
    0x1e0614010f0302090109060b03070c031701090221060609040c110a0f050d0201200903011427070b030c03090a0b071205090102070302070e060f04050406061406191409180106 76
    0x100200000e0342380202c42071031400701800701c90030000300c1c46200060510801c2c0490b0750710314100c088139055a540500e00020350112404001c1c02c01561600c1210404c0101e84511603000642400e140409a4007013100034a8115800c0050144407000101701020820806500b248900c60314035114100e801c1140c60314400307456800c110f81c18480c854894541030302c42080c2c2030001808040e140d206c1c01c03000901420300c840060001d0f00c0c0789000c00505900104000c11200031000c0c01c8600400750b0400c10303440d0040c6008074040300d50f0800100f680349803060021a44010448c1c182c450840d6150350307000f400c010a0f505040090526402050282c0481c8200ca4000903d40000c40c500643c07907074047e4507104035119250b254005180020b10a440c0c180c03e0a441c008000d00800181c078052914100400c86406480150300b03400001e2901e508011089034007216000420003121101c24030b04070381c800f104e150454050401030214009949132541c0402c1e01040b4044000e940f903041c0100145104214 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 324341825 1250 324340575 324340589
    0x109050109020916090506131e0302040b18010b03220302010506030601090e1e0c030304090e0d0c1707081c0504051605060409181205041d041e0614010f03020901 71
    0x1418480705001d801822081c111031082c0c40054581184040481c80319107075900118524200312003058282740703000885000d90344212010042103011005216807614002c005c4401450385070011300c60100c0c5800696030040041d2075040782810170b8010721548190208085000d40c0d1908107204581c50705114080c058030342c03410204011154915819502c81c40c45a2a00503002203049000e0030388402e0040034040c5802074101d994030340d61141c81900078800e05803042010700900301902da0140c402d10100e0105604605818030340d5044c243e1040d00ca41c4110760848030000100620b000c5c040d01c2030240d061070320f81290001410714050a00a0400300140c14694095450388018840740d6103a40c1690705a824012000409000714a10120300203680c90300940515040030202000c00d52000051050382c010006440c41600011105120b82401b624010000d1a5000398085041142459880480d01841000ca5485103a442c010340c40c51007a00f10000364a4199018070550034803c00c1c10b8010140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 324343075 1250 324341825 324341851
    0x901020c1603300e011106010609050a0e060f270a02030103061404170901030626190825060905060604111801030b0d060c120b0d02010206010b09060c01090501090209 73
    0x2043c502c01da450509005440284030782c0c2418025070f40d109002d00c44180b24404203d510790f50b1514405031003001c0d24426544100208800802c400c20511601e1340640c5004d0086801103003000e00f0410203144513801c03c01e6602c541d80381d00c2c000500500004e40207040c140d4006981c1d50550400106540c0762803038503809100c040052000050344004c07020003840603c46c860740c44112400040380588400c1c0d005190032020759090042160180800140c0b081c0058203c64140921044841c044070102c1c4d40640650414000e900c0f81c002440c02c0380070801e800401d02c4001508640d140c1003181c0c100a41900c0952107070017009035604041c882c0c120003000380404181000d80307003801c00311210b00b050070140c10161690103a100340d1711403490700460365a01002c1400980d110010080c5502c0c0195100c1001071f0800006110078201030000c1019a034044c0d0150215a003801a01146648000462038108104020104070340f070b420311429a1440c412000483c20040d40e004109410102810440100c16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 324344325 1250 324343075 324343133
    0x1018020a050d0b0c0309070810050604060806040c030210030b040f0c1b080d0b06070212010b040c110d0e030705060f120606090a17160323010c0e04050901020c1603 72
    0xf02098040c2d0006401c40c50990329514601038504040107984012071901c1001404090307d480c50700103d1041308143c07410030200d942d401c00c1903540c544c1548c0280040011035018000750030056242d0880c21480d0402255050030000450708688071480e583c1c14051360340c003c121900303610100e45044801500041d4103a100d45031209a05803040714101c0c03a96a07a034903542c44040c2c413a001900c410300e070001d120107541405980d29502030301c80070301e105108619010000c603800d40111484011964004020b040d24036a44034180e0b40340c9101664264907104160380010559120002001d000785400545600c0317484085079100f610001030315a511400b000d10103480c55803a8090f000d03003180c80040ca0780c0b08915050301c0301c5045c0f0611405018400389102004424451a85069640d502d0070300c3d114100d816510003140d080f601c2c91400f0000143e41080c1e07542c0140f500340c01258006070417000062520b480081c40030700d40007024601c00c100000d0710004100340b040c84103440303404100c4241520311410f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 324345575 1250 324344325 324344333
    0xc030e0325050a0f1202010c0c0201031505150d05060a050f151c0518011a0f1c050d0f090e060402070f0b0c04090c0e1c03021018020a050d 61
    0x1c0240d030380540c00803000c640c5806801005840308071070980c10100343c5000d8000c44c02c2201004103409030584507600c1d401540580184148500c0c00e09510644d100c502540880e8011005054401041c401c5800d0740b54000c81c00f42d68135411202440d91010300e03e036444107210152010b80d02c005000c07070701c940a402801c11160322050002c92020204a456140e200740e40400c030031031806803404035488030803212400c482140141d48002d0144e100340b40c802c100341400444640c2030780c460070001c41d500002a600f06903079091007000744071440001401c00c03007a001c12300131111842e2200f0f40142e801c0d50041d840800d181c0d030440702c2a508103e50785424140c0038107201405a40f64400b400c0180181d5000500c4024400101081a9401c0d403040e00245941000b00b042c4000c0e030001d0040003011807402034520a0170f4081c808030504600d001c1d00d404044100c0280900080714455400c2e0290300800c100c2c2c0550b10198420950401181c40c4025100780d0280148140804039400040c001c10315084040045 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 324346825 1250 324345575 324345577
    0xf0c061206080c0a030f2a0f23040209060c03210f040c0e190e0d0810120f0807050307030f1707021009020a0f03060501030611040e070302180907050901030c030e03 72
    0x1c1d0750080c02d40780c071003071552a0150a41306500c17044001c0b45480d0f820900c008043c3c4000c0403c4948d0320a00358030060712403003040644851800c0726403d0b036010780001100390510360090040808010045401d110300d650700241541d0103c000210507900c41882d0001c01c400702d800c443c0e04007003045402030707103860155101d0701d20425900480384d6500214001603d03182410188041840c500f030824440c0d0b0031001100c0341c3c0d03201850041004a034207000020790b4611000c000008135181320582c6080c400b4103031101d4006100084043c0c944000c10032001d40820310400007070140920a66a02c82100100d1400400c004094000c6e0152002280c090269556002544400000d2002c00010f80c41c841703480092120300b00c0d680015550000000000140f01107540042d040b2070003028180929003038030f415102544a0b40c0210f045410b000c0b008600078034425405001c040d12040304091004520a000804250049445000107500050f0010065070315000d680c40d00c00080c1024020000e0000540742c80b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 324348075 1250 324346825 324346829
    0x45a090209030d0c0f0c0806240f01050d020706060b04150302030c0307110c12010f0605060c0307031b2f030f19020d0b010f1706090d0305040f0c061206080c0a 70
    0x304003240340d40c50b045c440f04102100d03285500c2000e611101c0c4d03030f541c15141c4030541100c5449a248095408507611a807280c00500740e104020705400b900d240070b40066030150041c038140b0b00902e80c00d010f103000184203441040c0103840200e105daa00c43c7d1a1001c40c046509104207083c1c100b50062040c0035601e1a29003c0d65001502030a0843c180034402c541e140c90316101100041d0302c20181084072096000640c00035244000803e814018151100305001c0184141001500540c1c4208103a4011a100300960361881004981c0032141110030380b43c0c4020f0900340d10080d180c040811041c600f482081c140d040c4003c01c0203038042d01c0e82d2010b0f00600fa8852482d0b40c0c0b9006504104042c041c00c55071034407861418035512910310140303943c4865091507040118015892410700d00509400d06000005000e4841c0b0450744c010444081454012806040003510032507581d140ca500302d200095689500741c000e08175540e541083c04811202050990300d03030f079001e070b036082c0c21503484241d0b152252001041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 324349325 1250 324348075 324348077
    0x901090e160e01030807082106030c0307051302030601180602010b0f04140106030b030c042f04180b0d050d0f180803160201020c09010b0915045a090209030d 69
    0x85c0360007887c2010340340340c0b00700c0701441281078000d076032001d01983e0300d555680100c3c01642194090f8503804141580d403020380c0610341d40200a000f904540801300d8006640c0101d040c50800082e50300800700c00c01001032347d04410302603511200781510904ac154951410f62604580a008030030805904090b00281809204101070320340c0d8640d140d50718100f0100f0f03444100a042000a4a440c1f00710b4100c3e0003028121120108507410140c00c5d00f40068182d42c2a00c0316080e450342030700c0c0c920701601c5c010418440b81c01e410100000600c40444e00901840099811941380c982c0030008883d0f0080407581ca0200400910301071007800d11030600d0000c291050340c40d808410310011100c074001031b032034103520801031a0b201c00501c0022810403641009400003020946a075024200440c00c00c00880c0910b0041049050b04c0002c44408000303244070300080d1804404ca002d2086004070112602440030111111648201034550700e1101071480c00c1f903005001c2c8580842c24400b0500000341c6980700d00701108 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 324350575 1250 324349325 324349327
    0x6140a0605120a11040816050402120a0e0c13020a021606120908090402040308041d04170a0c2f0a03020109030212010b06070f02120607050a0513050901090e160e010308 74
    0x2400140346135010301a181100d440c038503260b07a60707103070116035480000d184400034690700c550002c0d04e82024009c0d0f40c4c0c0d40d4a040036485030341d034130010440000c1039155030044562158001d08807241c0c03104428801c6880c101080503950340c0141030080e280c411180d800f03200500d0016402c122a950240006410321071080010070031415501b004a010300480c000c0e55032180c4001000810002002c0c0100102d03001ca80c03200348010340c5042d0040a0b00d10403038000d044402d41c0e4050503651900350300142880d080c1400d1400c5019159156210740500c144811f4071079903443d50a805001c0743c2c07266a61680a012034488880e24190b82c0024510700305484000d01610780008003120340b00c400e4001c0e19201c0d038083e01860b100e91582c102400b000c199228281d00403050303440d0b00c0d641e422003c94542c0c41507a454440c46c3c50b02011000844640c2d01148011501203002c02002c6159910355030701c2c0e0f00806040002044030f0090002c01410001042c4811242507181d14041110450303403580a81140d802000d02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 324351825 1250 324350575 324350581
    0x9070903020303031603020403200a0e0f161e021f1a060a0203040b07050601050f0904020109060f05041e03050f06012301030f0f0501082404080a030b090a06140a060512 74
    0x54010740600d030070017488218200035a641038201507190444020301100c0003c80bd503a0f40c1051981740d0f20686642c01d11b590070600045a01c0c00c9074040e9544555180b40483e4406100303072020485003403843d40c140043e0000346c40c0e0011104449540080c0040cac0f860b00300828414619540900f40912030784a004002c040b9440725858000e10550740100320101d080c41c0e940c4c266207401ca4a8280034050a8450b0421900e140002e05001854620540d810f0f15030280460410f4419500a0a01600c060400c9000c01022600078603040e510704c1103c22041040480a0030b41c40c0407810b00c804425540d00c0c0d94098401000b101400480d1450320641c2c50049003080142c1c400128080e240012145070305500307140f104441002e860380042e0480c1c00e000e05494401c8615075403500c2d03c0c144071965525000010000c240815401c800903c00c0d102207082c0052181c0445020a0000b002100e20384a40e540d112400c02074100504001200301c0007c4911607002c9007042070207000d500a081521003c0c01e140000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 324353075 1250 324351825 324351827
    0x601090c090e04080a080c1804050606040b0d02030612010b030601140a0b0a1d150715021303150b090403080c0d150b0438031302130506090709030203030316 69
    0x308010309007040c04240b032890715052800e9241d016000420010328500000355030b181c000c4003a504502038010b01c80c1081d0319031204020240001520003903102d80c04020000714101301800400030300891500240c1c5034644ac400f00007541c554114054056410720520303c40301d41d800308a071410f5514900c548000b180c1c13020003003900ca0700580c2060310043ca0000b01d1201042e041000601c41c180c418103517107a041d0303607182440161280003503540d421a100344800f00002e030004442c0501c00340e050000600301680c400414100c1b601641c400d8a605103002c602c0007009060340910b1008a006a41480481c00c0555009240000c003d100020400000c104d1700068483c1d074018580f07a5003e2100030700e1b0203444910310380442c0d125100d01c6d03d0f120382c00c00c1d81c20488071032000d0b591401d030303050501c020505540001c100460b0780020000012a40e1030040640107a41c0d00d8608808101169400586071400300103000705c10300c020f45010203004942038200016038000044a50200c21000c421101d1012034078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 324354325 1250 324353075 324353087
    0x509040c0e0f01030c020714030a0b15011d031902010203070f0c32061309050103030810080c0306151203030a02030406060f03030c060209012a0302120a020601090c 72
    0x4294420305040608002641c080c0c070051070700301c045840307540d030302c1c01c160054049078002d0b4118000740c0c000c0c00e41040030810748030a201e4400400343c181d98000c10b0907035841c0742003401102c00b501d2402c3c110414250381e5901040000000d6926000d0716601141000069600c000d14031890340640101c8900e001164801d02c2034450705c5038480303c0381d1004456807803c4c2c1310140c103d014a2440061100f014001c641403e03611400b004109140a0341d03551044060040c90351202d680049100c0c2a80780c0001c8124440c4902802507002e035a9070b007c0c13414400c910700e6000072180d2195485a1000e602d8440d030740d4010624980107112910746248448a100c0030800d0013050b5041d0340303054000401088010011030700158441c5129040c100056a15070942080c4424a4000580024654507224000416035402803412440504003444a05c11040303100c5a007203041c5144918410680d0400300c10160104183d200c0d0341c030012012030400a4080b8020b60703600c070511580a502c0c4d140c100d08000140141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 324355575 1250 324354325 324354337
    0x303010e1e070206091c0c020603070903051e0114010b030601030e0c03010221060117131b0312090602031804090f02060309160e060901031407090c090806060a0b120705 74
    0x140001e220b881d2900019456000441da1030600c5d001d20121240c051140d00001c8203a556540c8408030301100a8081c400c15400080c0160b040c000884030110108104200c1200b60300c40480f56242241038046410f0700b5964103c0c0b01000c40b016540c018412070f6031803801c0e01ea04c0b5031300780303400140d52408038044c0f480d2030741c0c05120755099440043d450035110888502101e410140240c000001d0702d43c4001151a140d82050402a8011920100340100300c80213440341c1c040d01a1100b42c000104200e00c50001040c194021a0401c1c0c810340c0744c0c190309412090120040000c2c0c0003550410541c021555407800030122414480c07683e0303c0c9042d0400c94490304e045101500549042d13140c1c64174442d40c5903298880c0c11009480e031102c240005040b808001c480f03100b42c2014010100d40e074070350b585036200341031000146d01c254040c6210104a0703c80030310036030f00361240c19903030120340510f001081c900305000900564040c0000748414018901c000c0c040f1500d0302401d0746c2c1402141d45040088030f03680982 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 324356825 1250 324355575 324355621
    0xf03030e0907120e0106240c0f050a021005070203101b140d02030a150f0303020a0828021b010320072d061413030f090909080409050c0c0303010e 64
    0x13184440102c5415407000f0107480e03250001c610101d2804a80c410002c54032490000090662842400041d80308c5c4240c050b010b00c07500450304a4140c51340042c0100082502d0340001820100d541c005610b02002094580f403114102041000d0315581c41c4c00600c50118001d50502c0070f065603111821041c0d50413a001301003102800c54403420865a40c0d809480103440d81d4040030b5080300045181241d6038224001c5950640081401a10a40d00c4680941200004008200c959019020070b4681400e02c41c840d841180d024103031441c6158044c90011550180d081c1c1014a0180411024411200240102407540039141d440e030740d0502d8902d102c1507402141c22152900e032040280d03000001881ca58010303209100600040e40000c0403a40d0741c40d01180d090381c11129442c0c480002c01d01550120305e41026500d400b25016407900d152034140d60948200700c58480c0c000804210b40744c3c051140541150091001c1e0f89054900540655240010b0003510000c035002d0000c20b000341464502c040c06200c80c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 324358075 1250 324356825 324356831
    0x2003070306050c1e040e010e13020904050a02040608010b150f0418060305070905060d02040c03061e05040507050705070b0306220e0d18090b04021612090f03030e090712 74
    0x8058440c0f0350081e544404041c00704240490414205100743c80a8a00e0b03084d010083d43c1c40c000070b4800c001400743c01c03264000141c0303c0d01c07000760b03d45083c1c192066004a0003004112403e1040c40200c1d101c5511400150349083d82c5840d8607503580c840201e460ba044181e0310b882d13401c86003a61010748183d5201c65111340454141007051082a0005030441e405041580c244564500d545015030300f003103070b244e54014510b042e01401490207074800d402e03480301d51800040458490300e40654010307060041c200b60a03002c41d82085146040d00410340e000c0084d107885401c1071140e9a41da680d41c0c03d51700030720706260340c00f00000e149a00c400802c000109100c8411029400b600000c1c4001001518426640c0703000d400300d4a10154000c042c640000085842031026292818500b5402042e408103603e5009800300070340001030705182a4400307500d01034501e0501e40200c425024102d072039558001082078075540070401c040b035040210000c00903003c3e141c1030070b1580c2d031000071641e002060311042c9220385 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 324359325 1250 324358075 324358081
    0x9050603030409150e090606010e060711060409090b130f0b040609080a0c03020c03070b04050d0f0812010815070c17071a150d020604030609030908030d020307080a0207200307030605 80
    0x200c0198080445d5100c001d8006a51548060340e601c8150441d005804220101da1407111810b0450080c6001d80c010302d06c591070001c1c960300280c0a07610560110210340e0300c490a40c070030b109030701442940094145880550320106655002840441d0182c007522909540300000c0c20b000c5580c000b210b29030713030003074109036a505600005030520f8581d04096005110b040468812810001155001d42d20002a203e0525140200308400b41c0840c005c2118030085100e4420001009180500b004070344080d031a8074230750b042c4801c26242c00710804092510340503030024400f0640e04100603040c0c8e40c3e0070000e07030300350110429240d06070392141d80c40003030085030400741c1c181d4031802e40d00445000340c4448240c41645c1035030b0000c120340011075a4002e58000c4040004100064965010000503446400c003205050364500c041800d503041602885501500042084211648200c80e0307a4000740340d420440c00c0544580301c0150500300300ca40c5801d0135104c1048054140d40030444c0d42d006552011062185103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 324360575 1250 324359325 324359351
    0x9030715020a030501051017071101020c030405040b010903170a0504080a0c140a26010b06040806070e040912210c0915020609030315010c08030a1e110409050603030409 74
    0x58800030b00100000e1914001007035a01e80f403281c03001d90040e195034074840b010418464407031074480585140c0074000004803900310b0020178009054000c0d0144051034a40c0e25240910055894180c03001c2d040002140040c40040d580034045180e0080300c2441c9502d07288048025901c41c0b24580104c1214441d48059100300310031040810182d4410311220f00d4440c40440901c48428600e00901c698544002165a213806c1000c03425003c0d074a01f10000b180031508840405c1e895841074111001d16042003040140154120740e00516100003510300f044428055110201003142d02041141000301d50300c441c0c120000500b05111883c22169010091801e0f0346202400303000240c45200c101840006c1c1d80f0000b2030002c113a051141031110081c520b1940c60645a0b40041c00c40e6242d641400100c801000100d00020061751090600201c000b8a140c03d070360b0420003c0118103454030180d4105070712103c0520b01c000c15203040361004c060203e400e454450000e81180500d8026610652500027048419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 324361825 1250 324360575 324360577
    0x8062d130606050a060507141507050c070e1501050a090b0c0109141203040f140a060614041b1b060527010912051b1002040f0b0309150903071502 64
    0x40c03440340d50100800350340c49080c04010402449030002044050200790085506041c00181e000c81c0d050aa035030301c0355006c038440940001950504001900814540341400c4100200000342807116020985481d0031110b0001080e00e0ba43c0e0103042141c04110700d60b009000d409258043d04d52a014036860300e10080006009204c030400584092060903044801c03440049500c200b00e46000500078903555940e2107080007880604d0003110020300000640c0b540070f00922004021600c60080441e030b8a00d006001040f040b03410715500e100c0e61510404151915501d0203880754034060f400c01b504d100c035421202a0a8407240400500214244010840f0410088201c40009511010030b1015100715040680c22140c114100500c41c0e242e021802a01900072000350619902684001c0c080c014420503141c00c00120410581c01282c020030288040d0528080b004060100300c040380c0d003140f402c910880d540d614101c1190366844812408500114028001c4449068102130b47e900c20b900c0b5a0a0b0b5002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 324363075 1250 324361825 324361861
    0x3010c020102130b040b09060a1709010b01170708041101030905011a010207061403060d170712020d2d02011b090603060f05010807080903090a030c1505030108062d 72
    0x2d603d0443c0c00310742001c545003920f0507142514401403c121101c000c0c000d00f07500418001c002d12410310b80d00d00e07042d050008030900c00d04462002148000e420000507084814200d603034062403c070f10041000d0a41e01407035042e40581c000c5840340e403030107000006038020000000e000d44694201a50405810021003102000e02c03402c2c0d0031121f025546035001c031031043e09441640000c200c00c00c04038240749008852030443c580100f076010001c4d4600c01d2909032a5000030421a1034038810511080244d0f014000d0060708815030800143c0781100c68402c000c1c40054000300c100e940c0c4581c007420b2a0b00d2007540944c0980c00e0000d501c8040f003100e0200504441c1e024403440c8002802c01c00081400c1c40c0300090181100c2061b1a05015034031803003410b481250006008444a10003801403554039039450a10700c0c01140644403403c40c0b00e0030081c0321007001c40e40a118400b440390420041004010005116500901030001e000b18012020b01d80e10b424a100017924100042d400d05001c460b6603a2402030030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 324364325 1250 324363075 324363097
    0x110d0212010501020303060a0614120108010906050c0f040e090a020a1707080a080a030b010c2001020606030102070c052403010b090f0d0210030b030f1504050d080f0109020a0e03010c020102 83
    0x400d5a0380c44004990300d1004035145500300a009a080000f180035208190031040c402d10581c0c2001086085a00380f2030007648000010380d12041b0300c1040c05144d104442d00101000a924500104003040900910441c41101102144440007621908083c0440141182e009000c0c0c0070503940e070342011401034008601c2c91007900682000280c01000014410244d039800690301e0b00700110400e09400400040155074144103c00c1d250400281401e204028414640403030302c171740502c40c00002864200300030f1a080c0260710401003040400d0740001c500b4112402165119015400b141c119000121841200015410003000109111585e10060320401806071070303140200c0c055108200c0001ea650310083d40007034109001d480e40c10301c04d030086052507001a0803030b07240310041011145000038002c440c4007030b80119801d110030088240445441500140782c40005418803022881d4110010302c43e00f000e0b680d00094170640c02c0e000d0200340703014000081c000c02c994681100701071702039404001c50720 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 324365575 1250 324364325 324364357
    0x1020705010c080c13060509010c05010e0706120501031a07022a0f01170c0c1623031203340e03060a0c020703060b0a0b0a09050406050d12030f110d02 66
    0x4c2c0480c1144040d20000f404c03050f00d24801620b40042901d40340d016076120382c10400c031590480d000c128240140140800b5a070001d080041c40e00300002c28403004060050720050408004102140c20301040c590005512022006980c072208070682c900740c4003180c0301501e51035200c1d221030008070103404a005c1750401d41d00d01d044201c40380300450b90520000f000701034000045000c20342c10329841000d0100828401d045480c00001120310040725941c6a208000d000c540b10715200c2c1004102c05182002c400c01d8005042c000a04c01286800d400014000c1e070254183d514000103c201c2c2c401030201d1001352030754442066040b001c0041c980451014400c1c040d108500104120307041a10903072003120810740c09405003070f045070740d20340107005100030307840e80014006008507060711403400500f100380503510303a1204949040c09000658010358066486151104440d10108104c02111035201c1c8c1c0901e00016141c803a0580030f4020482061240441440800c80c68004400c0d5801804505c8103480d0403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 324366825 1250 324365575 324365581
    0x3032109170304200102060406051504152303060703180b15040e030c070314100e0d120218090a140109020703090e0903192c010e0307051509010302040801020705010c08 74
    0x1a130f0003080d007420382d18016401800001c0100f091644003603000007203400a08440880d01000038242c84800d4001c444504081004122150b56888a452180e12840c850b0740303911500c1000a8079890002c0609091684031005c8018009201225541981e40849061207906014011200300d0b083c0e0f8580ca4011450140c034000a202c1c004141c030001c00c2c2500091050a0840d52082e01440c586c400c000b005104a050b2031401d0780380ca01132035500042100051520241c01c1a0040c40c0030700510b4516001c510400c0301d403c401040d000f805040d0002610048807540b0341c103403101d00510225403080c82400c203035800451119016001450703000d009079a1a9405a1154001c0c0d06520080d111002c16030b10400000c000c0c0714040014541d07018090600e9400e0070030407100c621540c805640c4000410f01b1000c540c000c19a04030030a040c1e00c28007038000301410380c10036003c590003441c00700b008842c4050110700300a26a2007501202d0181c01150b0081d52102c1c000c2c0f40c554007805080061001143c050000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 324368075 1250 324366825 324366863
    0x2010c0305060609040c030f02030109140f04050c0d080714010506040b0604120b2a1b161403030d06030c03140a080304110d0218010602060601050403032109170304 72
    0xc0d070303806080018040781c900386004c41040018014a03a1003810b1503115082091403121034805103000300002c00c000704101d0203400b01103818201c0103001500c0d01582000380804140e000800304076820b800d41c0c030b00c81d9014083c00c001030f4070700a00100a2800c40c440100010020042d000716004817000d890500c8845000c5042140501440c000d1030251900c400d18940442d10000c2c095810080c81c4640302403403002e000303007180302c00360107415201c503032800107030301480004148045901703500c1c20303009401424503007603000d560080716101e80ca40f500c84211000e000c59030305000f00c55229415203810084070b42c4d00d04d000741c1441c5191000755803060584803401c0c00300c40702003880d800495004a03054519a207aa0350315103100180584143c0220380814408010703114040c0340403c0003c894110842036142440c000c0c5030080080c100750401006100410010350002d15686d441184030081d01c00a203030b00c02d0a0401048500806000107070364820180304d440c031100046000b14003d8403030101079001100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 324369325 1250 324368075 324368081
    0x70908100606020a0209101205031c09051f0608010e0a05010c02150106120b09040503090a05030c0a0315021e1e0a09150e030d02010b010905090f18010e0a030302030702010c03 77
    0x420320340584c0240e0442070042c0391124a0b00e80c8510240c0d040044603446650448111307810726800c40b600e50000424000680812540c0c800700100b002061250500b1a507071191612124500e065504404068543e00e1004641113000500400c600802005070101c004503540c0700c03c1107042d100d0354609207070b0550300f51000c20021614884c0e212590071907440e044040f183c1d9184140b00715010f9648054010640e1758004066014078084c4000750f0321040c008080002081159101741d103c3c1e808010342d081d040e21034203500c00c201d0b80c22000314000c840210380c551010748a207506400300070010406400f00011068040d22555400352011901c9440d001c5801035203110301d51044001c03030030b039120800c018127180060740010704140c50071a2503050544003291410b405c40c1d0514025035140c00000083d5684200004001c0c81d045030799411505190850280180c07000e0210140a10108078801c01800c09401600c0e041c2d0b002070454440303101e5410001c00940095079114019402c0c8401c44003541c2c4240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 324370575 1250 324369325 324369329
    0xf1002071e0f05091308030c0a08150a05040207020604080a03020f0d052802010b0904230c060304080a0c0b0106050d2f0913050103050606150307050405091306050709081006 76
    0x41070300c2c650703810007040000c4080d009000103418403014022400141651010718050031484482503220140c0301000341c4107100040610001e0415800d1201281da100c101ca542228002d540040e926040e07070020070903500c190b8009280e03520070b0341050820941e0000e407910342c80d41d003031065501510b0103034030031213081c0700301e0022081d8071180181000c0125200030107280411064000042c8520204020030800f410444058680c8081c0d01500005000402051411081801c000c0d19008105c440042c0700c900000e48003928411020a8143c0d480d4040e070307100711203183c215214204c1136a60b4480248154408003002110034240301d2103010540c0b5843c030825003a02d000300030040c409503100030f1040030707006921503079444040e040c080391201c0c0951195602860003403000e0034051400303c1c20720501030f620118000801000300204114554440b0a0b2000d44104032003102e550f8660005980e44c40c2d000c1000500030034902020b22280c40c0e0002c41034401c9814520503103244c004050b00c01400c6512134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 324371825 1250 324370575 324370589
    0x1e01081e06060d0906052a25060605030f030304020301140106020c09220f140d080a0b15120a05090d090b032502030403030212040b040b090f1002071e 66
    0x250011421900d0224083d008a51000a00007500343c9280c507202c099680c1030316a190050701d4504207500001a085051030808140c061003450b10800c1c0d40792420b80c01484144442c01030848101c0410400b040c0c00040050600408881030441547e06c22520303544142d404905ca1340c40c22a46041614180e900d160403603486401801e00b136200c94042c0044d00e03800400b81c0d07000d0130601c18040c4850441c00700c0d940b5050f005100010980e440e92400b041c4040300d0291782e041b030380d010040300d4240701c3c1e014045c140c1c00f09500401140c51180c660100b485000c8000745010703804e40c08038040e110316541e145150311a8460040c10300094603118400c45d00c405403036203035100083c945481070040000900046812419a400000410b41c0d14041c201c02003540c1c4c010400142c0fc0007604000f856030420010f400a4a4810821301c2d003460140e107241d040c0318501c40d04005c0350707010402166595529684020001c0c0280480d904c40b035a041000f911800716000d01c1048040b480e503a030020203040c040c181c083d5200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 324373075 1250 324371825 324371881
    0x40509070920031906091a090c0f071244151c02060a0504170303010f05040c0302090d05070f061e08040804032001090824151e0108 58
    0x43c030790b11011105644810820b07076519541d002841e040f59100c0c2181f0f403044002c900150716040803c00c4150100a80700d0509014203012800c1c11a08440860385c07520fa000c503500c01000b0080c841622140c6040210010044400240c0789083e01c0400e105000c013030400724414030030714841441c06900002a105100c1150f610f2140343d1145c186050003207000c01d002402c00421a00990000f4075035842040d5503400214041400c0099020480e81c07203001040d880301031808c660400304610800103039441018401ca4030303800c01000b064043e80c1110801c02e00a0003405040002e8180280c5d40c003014843c48004200440c40004c0d038510850048124074840c007400002800300074800c403546007003d80709071050b010420000002541c04400407450b40c01007018211844101c0b07001508640d0030f03601441c002e80290301c404002e04c040e040c4039002c0440c00402e803135803900c035140e00c44800c04900000a820807260303001e043c5072800c02044c0c000c82c00d40981e151b0310319a6802c0300d00304500303850f00a89040585 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 324374325 1250 324373075 324373081
    0x20a020703060f0f0603050115060908060f1806040f020f0a230a0509041a0c030c0a11120d0b040c050f04120303090b0a14160e04020304020a030204050907092003 71
    0x4281e4000748800c0380800f102003051003040c2118011141c1a6000b100c86a546050004403078041c02d12000040440d4105120001c0c41c018900d920b0701c80c000c1c04c01e41034403a1840001d1000c030b9039515914104078000101c2e905441c1914000045c00c0b1180e00c00e078800da80100b0520f0781890007141003419203800110449402100c6042c54602c01c0d80409032503070142000c5c10109580d121307a58158411401003442610700204400040d4800c6000751507045949410010803001042010442c1e04642c0a0b01d41281c0c02c010949000b4108891035600b031119110026500281040f650094000d082080320704216100d0600700544841c4901034202126000c1803200700901b08604000342102400b03420f020417040a59660042200c0080320301000c030039aa44407424003e0b003d01c071080e0307000c048591820310069100740b01074404014110700c54030883d0000300240444d2203502c0018021a8058020b01207070416010803038480b49140a0310050502c0c0c1800200d024a08402c0c1c1c5218030505040945103031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 324375575 1250 324374325 324374333
    0x30302121618120f05011103040b0a0e061e130b07090905060618010f0203120a05160c05060612240106021018060b0f122409122d0a0f03020a020703 65
    0x1103e0a00036a400c1d5a1f5091007440c0707005250085203e1751189000306003e140042d440d1049032460f0491b003d13258045030422001401d00740c01020b0407200040a180c1942d500700380e10b250b12462000040c15011003030b060282441d0014480d030190303004144140031581d42d62040c0146405503c17494000030a412a0440065008004901c20070700c2600c1030ba417500001c44224502d820060f0b804d010300940c0c50040040344d5a8201040c3e1905410340b82881080d12180c446907903804002e49400d214000041440030551010052031890074200741c860100f880e9100e401069120f003d21902000d4000d0a1310024002014480c58400d042c00070f50b14241c003542c54441a006101c90380125800001d240107050a590314043d0108918000b40000c0c48440103c0c600c00100e0b5801d4245a10f8196011050000c045004200f4191641482c140982c480301d9541d004c048002e1498094441c04518503009081d100001000307000a00103901c840400c01b610290443c200d00c2140960001038002c0300080c0f0000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 324376825 1250 324375575 324375593
    0x3020904080d06060207030309080d080609090a02150a090509040b04110609040e071a0408070b070501110c070e010522110904020a0801090f06050d03050703030212161812 75
    0xe401003000a090210040242080351169000b40c800340e4003105007081007503071088481e000703482c024024110b41345080c24050002580a00100c0c4948150b400240c0410f030304100e40541943c004002d12a0001007007540c4009502066001c000600050404076450400c0208940501d911928030301c3d140e965504c4002d2000080e4050680c414030410102000c0d0741c0314000d5441070901840980b900c0b9180c210241d0510024440c900440b45041c042000032010118880040742e040750441c5a0b140c00610f001401400580c1003400c02070f02c0845c00384001d000000f0804141d400f00c0303030850302d82e036268000c0047c0350311001c6252482d80030000240020303108507002200b0080601402a091001840000342131382c00003111540081c0c0740d02c1c0100310140d65402007540c0c1c0d01c0804402c10009082401050604507620000b5041c4003001031000101442941160322481a40c40c100e80305051100031074825001c29517622001500904245090100d040c450204540801a410350002c00e16a246107113 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 324378075 1250 324376825 324376831
    0x61e2c06040f261b0f0a0b060d02090f10050316140310050c130911090d0c080a030302030105090f0105010e0d050a060608011e1a011d100302030a0b0f0a030209 70
    0x90f40144400010740d10b940500152070702006031a48684490183c00043c0b2100c0c0f807043c0022007a13000c100100610703000071a6205290703401c04c01d0383eaa9a560480894075081210400a400420700c104200300d21404404041c024440105030211095030341c010076580e03044030030491140d160150000c010052034940e04103498440601519411443e101d20581181e404451450107c0d2001803041030303035284684414087c01c00c40c0010024036407a4011001c4601581003028055540d042844c4240302100c07803036200400c415803c90323501814614008000c0c3d042031080c68054448000403132003003400c00710084c0c140c80741a0344000c80902c02c5820040e006444440585082c041d402c42100802c0c59800b0b031030042d02301c0d500041400140503212810f000701000d00300e01418900f036405682c4250409001c254002c003440d092150585240d6078820f107060021159a00034a000e01c41400640c141c1c01840c4a84489401000303100d141100384101d0820054650390b014003012418001460000380e0150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 324379325 1250 324378075 324378083
    0x5150315030d120c02070b07260705010f05010b071502210a0506101806051b0d0f030b0d0203070b160c0e04023a061e2c06040f 56
    0xa01298240e0100c1d0a2445415401d8001400010300c0740c0d10000b54060907901d600c0c01e10041101e42e20301801d54040c0e000e0510014071131034503801d41c1e8134460b40d2007074a00c2c00c003ca41c00000b50b6821241c540f0b01d0081c500003205051403400c040c000140f0140d0384056130400c9400243d5441c004130301c52007078002944505100709820269070400c807110407020045030b01c140410240040c0501300b040400c210102e4114040302041603500c0d81c09101038002a80800316a51802d182c0d0321410004401c02203050200e04020032486560302810296601507806058418286c40c20000740200105000d00c0002740d01000c0d401d0f40c41414108801c041083c001d1240c10030861000040f02c80039a212564a082e55002060074603101c02404194030b130024030001d0700021007d40c0304007080a4031041a24120301220044c95814444040c41400641c2c2c0000307a9000d000d0100302c903102c841461050041c54825092080d00e0818090420074082c10711130354000312154001443e0b1591143c0d5089003d50342100115 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 324380575 1250 324379325 324379351
    0x1080c01270b0d050c030402010c06050c09220c021204050607140601030302030706050606070221070b03091b0319021c210f090308190e0303030907050316051503 71
    0x20320851141d10300c003070190210a01195864081142080c140d03280a400681c4000c401c000340b00050ba08070a850580541c425004183c0f9941d5010125580c011400c106030080040280e1310032800b880035001c004d0f0250440200420f00348004100c2ea10041c035070284980b50380803c0207201c50314201c001703415598469000080750201a0a0050410303000b070748114056131010400508000e803034001d440d40f004003510f4947c00c1c00c016800044c0350094500c991680003580c3c040c0c2c100400c0e41402000e014212100030aa620305013030109940e0f944e5190140d04900003603c0e12914189000320f40c0d4a0182812901c107950a1540e400302310160440602d15000ca40041c202d0b100001d04201c5141c1d1070314240d2404500c01124441d000c1c240080301da02003000c001c4251020720001e103c01d02500c00c060000500829580c81c401c2069480d00b0550800980c18400031007004081c580004660040d203100750203581d0014403401181650411a00520b940007104008500761090b02c40051075120390306100795 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 324381825 1250 324380575 324380627
    0xb092d0c060a0509010818030f09130e071502060c0f250b040606151d03071706040201020d11030a0c06020913090b0105100c0605090109140105090d050301080c01 71
    0x8280303900500c0b092001c1000070032040e0781d968000040350b50000205440c5491a60038a0b503c81d01c9200d00803c0700040d0300c2c0401c0740301c0640c448a0704c0707001c1d5402940d020000812030029044e40c030101803180300310241c0e03210f040c11036880c40418040d014800440c5818240800003600390716940240242468070034420f11305000e413030302003c0c0c10889140152030f0840603041908004040e900190000b00800c040c0c511910500782d80032a1a100400c60b101c50501c050301144c0010b428095a9882000360071070486011003541c1d00421076a0250b0300c01d8085500460344054155400c0c4041c09000c01c2036007083c40200341050040e40a0010303544076a000500d07005c40c000000352a04441640003180c1651140360a0400001030640d03800b6040445102c1da0000170f0220041c48603010541c0108040e85980108192120940010b00c0b41ca501c00a19406032840c0b03407881d4000d00c812903082c40f09120f0004001070307250141c82200d0580d07420102030141c2c03034007800056131010340130503406201098180360 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 324383075 1250 324381825 324381829
    0xf0409110603041208181b010306051e030d020d0207030f06060e091014060d080f0403060c050a080105040b1305090c0307090608010b091512030f07030c0b092d0c 71
    0x82d032240d4450383c0280c08401d860080101045401856500c07005032041c0e04441d442000a8207160080b44070587c036840c0000440100c4c0030305840e03800b5540048020754a050400400000c42c2c140080580480744609a40c1c00c04a99814a00c03107102c2c01358001400c1400840c03441700e01055010300a00f404503925030b684103807504052044a407402c81e6002407242500405040c010710316490302c2000c402c441414180006a00c008103000003d001050000d100710610581006a900941d08003900b04075400b4000405000759124502c1031000842560000c12646880c2c0700340503c818001d4002d060410b400d070f5515000380400340c4014442c0c410b00300d13052042e40d4108480805012002030201d1031610b03102190f400c4d0788201c40312601c07450740d170004c02081510594546070b2108088914113000460566150709610030303403c002003c000700250348002c0c140c00c0101c401142c1c0c80303540303850100e555882d5403640790840046003002c030045191100745c0c803d80342e00030050151840c0081d50580304601c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 324384325 1250 324383075 324383077
    0x102120403030c11070305061609050303070302010c08091504120c14030d0e0c030c010f2a2d12021504060f0605060705030d11210a050601030b0f04091106 68
    0x1030100e00003900e80342042d0a00d5400304c515130000c42000c0c001e0200d142544d948986030b40d001840d40185072503e402d03101e90648145451001004041d082e00d554101c64103000740030388136540081c0c0208980201141d104035002480d51402040300a5180702d0703444541c0c401c152901050981306c10400042c00c03090201d10085990307554403450100a6030b41c2c522000400090f501008204c5407183c00680b80c6c00040d490220b10036052050900e0720695000481c10103440b0000280c880c0201c0601b00200529110f1000c503c106c102802079150403a9007000814000403901e8402908031300003210341c4c149000070110744912045000b240140c1d0300e200440b042c0014142c808a400766091350b01c600c01100b42540360f102d130801512054035010300c1c2181c50344506030b6030b2081140f121201a610002d08c01c506c00e40c18185c1e07020013040044040d080203c0780000398418015a103000c031891600f8003090456010380300300340c4e48070301c0078020604e01d03098841040001c1001420a81d101e44e031440380b004841d03031450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 324385575 1250 324384325 324384331
    0x30f0b1002011409010b0901030236010501090f03080d1a030139051b0c0a061d010302040f05040f02040b0a0504150c020d06020c0c12010e060604090b04030c05010212 73
    0x40c0c00015405120002141c483e040646048032591516042460588818640c03d040d250140c45140218000c500d421035241540e0b1072889001c00c0c4001f10400100381c60750118100d6600b641c4551a05440700390081d00794040f403000801000c1c04001c580e003140150381256120240380903070304205440900109096031280c10480300307843d10108400203408149175079124100d524a205410405018002810302c2c4200780801c915a14002c10110b003504042000961000c000f5042c285010b94500c00a0231000c00340880d100000420034038100554840d1090302c0807242e00295050710729180005110040c030922150002d259000c100105400044d20010b142d220304994407996103a03d841c031140c0c408103a035107440d0100100c503159400540d5601d0000800c4c540c11100041c0d80d0081d19500317500d80450071128503080748884504d4030728008194485506000e42c107060320740a80d80d5008001c121840c810000340840c0800d0007080209100e4441040c1c4507100e44001441c060801071100e031115021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 324386825 1250 324385575 324385577
    0x150f02120405011d12100e03030c160510110702180f01050d0503040f030809130216231c1b0f110303040b03010306020d3b03130b1206120d030f0b10 65
    0x140c4601c0804004a05c507d401c170f0311090024504604200140700340d1441a89807031444c54504e5802c10080c00002c1c8280844038900303803410084007000100c0130039070f6001540c3c241e120702c00001205082c0502055117500c00c1022100f401890717070928041101405080c48107403201d1200740700102c0c00300c0d203080b103240103503020700704d51074565901c002082623a03c11985c0100c90240113100d001d205a01309994230700720503030040b9294034900100322280103026400e580d009092040c10b00c8412a20b061588500712041c003503541040b20420b0019001c0c0aa400b540010901345001d140b00000c40d445a1042c540c0c60401000c0e0303480c050707840d032680302641c1007a042950a16400109200011701d28030401c2c005415820701c3c1d026908415040d040005049040d5540360001c030201440d0f03841c01402107818000c043c40e2413040f645c0e11020600c5040e04048903c0f285881c040d0017241d05480c00148001011a890005001c8084420002c0740a0304101a04110705a2a903513a82c1d03080d03483c48407a040010349 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 324388075 1250 324386825 324386833
    0xa0302120a0506150705070603021b010c0810060e0303030c0a0e102601030305120a0209040e01050402030706021c120f06061115090c011409040501150f02120405011d12 74
    0x1031800c02c011442210319101280e013007003044c08001280400c0341d030304035482824016103611940741001900415240e465000b54a4183d402c42c5c0c181e04002414000ca07009101080403175142d420903a034070070301d0700009a80340d4800c2c00020030400014000b003280603134503d84000c040c081040840d001c1c101a859200105050741540640010804040200c90f03c00204e05803465266440c045c0552103281110b640d940c3d14803002400e05030503070701194409207000d0410480508170040a1b802000142c038101d200c0d000f407030000035180d40300041d58502c0911901300d02d0842080031070161401d00c03010002130001d9442d401030f000403905074420726004044549441075421b60f5040c903d410415008200410480c600c0280040600b0009030381c8040d48007030031f10351a4800341200c1c008050080360a051343c0181000e0000c59140700201001c0a81c1c4520b49a0021070405004181d032213618180640c65082d6061000704207a601c10380d00a00c0c0f80c1102e0003010203d107851030201e84c0c0200c400d00d0042150348 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 324389325 1250 324388075 324388081
    0x1b0706030e0303070f1209052e090206160f021507060e1b19050d06020702120c0603040b060d0f050c010e030309090601031d0d0c0b09010c0c080a0302120a05 69
    0x14041c0a12040461480701651552505920140402c141800941c082212003154140e680740c255100d00d12a540010444a450255418000400b6005041000fa044020321804014032403405021400303a401450b140c20500c2d0008050102030441206840c042400b0340c1d07920140c2c4a60481504c001c1042000560342c02640c207100043d928060b0b0501d01c02e611001c038400f4024801030900d152030070200c8860780c12003464903c030340a46170325811840d400310840c0b800900300209540200036040c400c0e91005482e080c2050b01a465200702034a00d90440d07010400140011480c00f4141d61280000701849080343c0a42c58051a82610060803581179200303a0f9402400d603004500d00a484404800a510785181000840d012410150005051644503c11540201c03402c0780e000101c10062401caa0074544001c0006088a40c41d01051b60601485e0b0003041030014180144114005c0760f03140d94040d009969100f01c0c250703126500c01010190300b440051020302c051181207000d02c00d024004a0241 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 324390575 1250 324389325 324389327
    0xe18090a02010e100c02120111030910050f010b04181803080a0b24030702010e0a030f08010b093f0109020f04151a04210303110c0c090c1b0706 63
    0x9081481013403040b540700791101607955100503551449941960005032001141c3d03c06c070301401e19003200c500030001c04010010000800202c0845524007610f0621558443e15103903840340d4401c1c000d00801c482d0403c000d005800b102110800782c0101e16200144068441101e24a080e00b144000c600003003007071051010700300711402001c03900401240c900140d0800130400c2d03818181008071400404901000044545000394482c1b41800c04d80c20640e190070105e07203401804800d04058500116041e41c00200320f60312400c0544441c040701402c110f5002c100100b401102f40300018a05900a4220047c0e40241c1c0d81d040d0055603080c02c080011076694500d00c108044005000080d900483c41d260b0109080c09008031710200700d03101035108400c42c3c0b0303501d580000c05114540021490b545944244003a00141c0030903000701c540299000c1000c1e40070200c103844c4a2149424914140d80440c1501d000c0f0314103c1c801039044030a407206945400c07000c200070100c2d07104155181202d034001d00c004115607 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 324391825 1250 324390575 324390587
    0xb1216030506030312060d0b0907030b0109090c06050304050a14030408060a0b01020a1b05060724090213020f0909090f0f0a020102060f0a14090c0f030c0904030e18090a0201 76
    0x41250806000518100700800d51301d0050b6501d02d4842c0f451800828000d8950403290201c658114402121034540403015603950301892001b141c01c85d400100004610301984100217501e64043c1260030003603d4540e08540c282c01c0540b09030b4160041c004110001404a01c5c0240d000c800007001c0e42c1c40d54508400f041c20403500400b802d00a0b07042c0081804540c0c0d020a1000407164441d00b0608012540c9001c00440b161913080186c0004002940e58248041018000d21004054000300c6481c5900c0e84108252051520f00a401000303101c21408405241c0e000340c8000c201d01e485449c00d2984440010340b1070fa40c142c0b445605500458205613080009010032040c1c01d4524009120b0000141d0000b50381d58401018489844442e10115149541c643c10090540e48248030f040b0b65420101310309c685801400f81d1061084024124400321803c000c5605070314124000c0c40c0200325a9603841c241e440c0390f2218000355000ca5003041c0c602044180701d00e441e0040000400520310a004c620000d015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 324393075 1250 324391825 324391861
    0x503090d060e071217030403050c01090501020d0c0c02011719060b090a050604030804090b060d09051507031a040515090901050601080606041511010b10050702030d05161101090b12 79
    0x1c014800c50340c1c0c021414174403000d200510420407260345c3c1c2e551810111954002c40340c4d06062542041160000e1050540281000341904002007015044185054500b84a4540000e003c209108450b642c900e9a070080c0d2680300d01c601c0030001883c4542511102218400d4103c1d440110000c41c01d04854140207400710003612040c1d807190320306815074075900070030300851046a502d16203e030b11208664a8200a0b5208050390782070a22501c0141c0c90310640b035401000610075407203a800000381c4510700c6401601d40d24200c02e400340060300040c009000150000418444500401040f80302c01d5444540d261031060301c44000001d05814424001000c000d4060181031013000240400e0003c2d07aa070400b01c0c683d203a400d0511180c0045a0f03040c66015000380c01503180d20809441298400f66004401060000c0c821429260501ca62107400c0d82e0602440c0c0407503c1e850000c5513410001085207031001c0c2050814103005104d5540d86001c01810f5100c00310062070030590005218502c2c0503c0b0400c0c0c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 324394325 1250 324393075 324393089
    0x12040c0503062203050714010203061815010e0a0f1509060c033203070507030e09040b04121101060f06030c0e061e070507062d08060103090503090d060e07 68
    0x38a0410640043d00303c00000403244010707107100d01d000101401030701207407022a40300d070241d074405501030071190003904100c66003405400102c5810318200c088003110303403007040d6400a41030f1941c0a40011140400c00071005500010f00f1074007c0340c0388424031a45d134020a000d03820760984001803407000b88903c110b0f500070014031505e40144000250420501201c401d01802050391540703880c0312403070b241b8241c00030452a03142d00109011034264001300801c80c45000380c4440d070320840402c05000c0a40300403038010344000e2080001c07400146140b4400c03608090f030341c176085550703074010300c0301d41c2c00c4034000d0384101c04010348502c1c10494a81c141c000c4d1103240b0020b091450020303a88101095491042500c1014001c81c60045651044407210603244069000012903914a498140c040c00010b403803518450b20050382d0034290383d00d01f003400b2207a485c0051603a803410344c1c0c0c907540e0064010b008590400c54050000b408403d40c2ca0b1503c4074851802d500882000c80d0440d298034007681481f1507500020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 324395575 1250 324394325 324394333
    0x90f051f030f080c030d0903020c030c010e0a150513240f0e0121050903120906071706010c020904150609061a070c0302090c090a06030506102312040c0503 68
    0x400c000b105420102034004000c0c80d40c0e030f0701500b451400d52080115484005281001290500d680040c0c9981c04c2034095003215018a030203801582e43c151042c41c4254841a40e0310140449207038500035045030b001c641001c500f00340c001a00c4419508090300100040c017940500c0b0318200c100c4040c1800c200a441c10b00ca140e0015296004040d201610070285c1480190f5052000000744010300c44040190b00004001c42d0070700c02c00c00343d00ca90105211103078070807100300440c0e50740710041103d90091b0a95111016400c4050443c120070240c0180101c1c14000302007220030150b180d001006108510624040030b410f45031030050350482d0030980040f030b03140345808024040c928402c610040a0030300c003000720752550b45918003c2d04a02e0742d07801c02508400490280f08441d2415400381900769000c80350030241d241c440d04100d08907041250703560f9010710380c8140d0150903070081d25501410210280d49480e003040024082145601042008144005280801003072003242041d0030082d1074228090 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 324396825 1250 324395575 324395579
    0x90309060f05030a11090301020d1e150303080402130c050705010c09080d1b05010608030d18080304031b20280620071d0603010c1b050304090f051f 65
    0x411a00004000a4140c0d85e41d40064560041d030340150303031104030b0050080d5075551070f13041c40b403000d000c5801260780510320407d0002001c0c0990f01945914064100f109040d6624580781103441100190050b03030001a01c1c221410011500c1c0202140f00003036032100c0c1d40e079051714505503084412181c124810089010424040c1c00790100d6022960101d0b80307400c03401a56404012020305100b408024000e61070000001825413021010702082c00c81040c1c1081540c9800309840d9444402c000b000300307860020400600040e004024042c04403018021246c03500200b0b641e40103506580c2a43e4030040184405203141310700e0020600c46900344600006c0b90380c0e1103080149014140349005903010b01001c1c0da00c1c3c000e80900c0b0078003000c200071080120358009a5604190f00c0070003004a1902000e0048800034805040501400c0303001209640c1c2c0d240710342102c1c4402d40e24241080d0044900740020880010115028044d02c100c2400c0d16500080c0d904041c091403440c00401310742e0480a0041001c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 324398075 1250 324396825 324396827
    0x10903050601182301080f071505071b030c05120307020604030305220e0a0606020c010e01031104030b0f010509090613031d090406061701020c190206070b0a090309060f 74
    0x1c0e41e044400d0080b492240d407040c840b9140203405110018094180880100d11003050312954036030494451500782c41c40d01c17a8003a03444d0344a050303500461401220b900b514004242c4124000e114882c041d01a0468452015500008801080d402aa40c50415107000d00c85850300c80381889694210740300541c90040954081100360040e440042c00340300c0f001c1207281500c1c42c401d10319180401c01042014410f9201c5d120480040019107009144618001c008120b1600010380b190303006205858101100d072005004401401c2c407a000036600040c00d110000004071102180340c049c007224007603c4030940c145010b00082c040c004001048a9204405100300b00442d5102e00703006a425141c4101002c11250500220340c00b20344102d500440c1c800c2c100818000d5a40c00841511522460000b41306666000c25003030340100c011160041d045400800303242000b80040004c00c52000e84141c2c200b09803600da4221030f600480314200c0150700c4a05a0f420198840c42d0703a00604a1402c4c66148040d80000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 324399325 1250 324398075 324398083
    0xe01020705090c040302060a020d122a02030d1d15010b0409090501150602010209041407021f0605040c050c30090102010e060702030a0e060309031c020d0204060305090c01090305 78
    0x105040c011a1414045070100b01d100d4200c4e000755030040c101d1340e0384d98a0518000d554090704101207000582c00c902981e000f81040c000ca0320310010311341181d400317000d030990b8a0080000300e07142c64080d803008004105240c0d581d0300803440a240e0962200d1440240d9a0f400b81c201a409010001540901401844900c2040d0140e4040d0340e01001c001807a501d01d4502a4018400c800e90b508030410510350006d07090358150002c0080c204250303070500210300015140c4030b2144050b01c81601603000011201401100784d490104d000000f0740d804605151358401180440714030341c06010000f100061141a180d00c1000410495004500c0e400408240e0001054003e83d5600d002e0003080c50000301d118190780b003500300d0640600301d00300350349041c1403606000c1c1d504c3d0f01944628012074807100c00c00e4004c0c600942540e10034130400014510f4048102503200c010032030341d81044003055080c4800c0890700c80302e2014001924490314009034a04040c41072920f003d842c00700c054100900c001c3e0902c0000c00c045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 324400575 1250 324399325 324399329
    0xc18010b030117070b04030c1404050408030636010302192909030d120617060a0b0d12020d030506040c14090418050312130503070b0c04080f0114070e010207 69
    0x907404121015560f42501e0038200c0690200f514100041800300c10f110019102100701c800712008004204010402d00087c3c0741d080340c01810b0001d06200040582c01c01142e0480c4d806280c030805101001c4d0442028281d5101c03000204ca4030310340d00010300860501c11000c030038182c068602001c04c06e240c103240383c00035400703034001048000e40c407882920400007080c25100c0034040202940e140c42c1d40c2d894001c0c00480000c88404e4840c2c1482c20001d135042c0b135113401d0744400e17031008040c0c41c40d641d0380042c0d40044e061800d541a00004400c1002001c150b40744007803c2c100d04039901078040404440401001c0d00c030701820240c403451424140c0c060b144c1d00945c17020303035982c01504204d03207030704070b42c07000400514952030701e00d0382582d020150404000011000300700349101800107072816120084411000303038031858000c2083d48100110004070340480c09480d401401e0710412484c0c00d850300d4203a820300f642c1680130101a910b94066440141a03c2c00480e8004402d19014000481d4240001c0d900c903228 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 324401825 1250 324400575 324400589
    0x180c022109060705010f050919030210020705030408030f07020108010e0f06091b0403150e01060b040b09060904023c04061817060a06240e03011d0c18010b0301 70
    0x50741041d5500c82d00241c40d0310b280c0000c020800c0c1e040120011000e000c007101c5103901c074040c4000342100050b04401c0e108107180c1507030090030600045039032040294000d40c41500d86120600000485400030002061850340342440716844114510015203401c1042c4c024480a2442c0c03420000b11806014245901440459140c08107440e8801c102d290800314450410034000c00041c084203001c80d1046114910041040410044c006550f000e4201c4040c0d000d5400010000c1000700680d42600d03003e010001001442580b0341001000010700b26070180c07031910601c1016000b0b08440d501d4002945040c100c80460120700c240c5070003441c4405101c0c0c0c2c0038010501074039188030388055050740e03074003c0641841004440f131041359001c01580e0f080200d80600125041110218600c0303400403801811100401d00201c448600c044165044d035850b06650b50159a2400100039441590300040302244400c4050065020140d040c0004203108010100b20090b84600401a252580b0212030465802c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 324403075 1250 324401825 324401827
    0x606041203030506011e050c0f030307050702011218030e100306080c1c23070909110105070602130f09060605070507090b030f0a03080f0a09020108061e0307180c0221 73
    0x350310051b40c2d030100e800c1240b2000c1101e1125207030000c3e080360081200455041c12901d070500d10380451596403004641003000200c05010354401940184d01d5003078901d0709a80081540c6010903086c1c41012102c4c0e0303060300000c52114a10425007402c034441140d803d061308e028407001c1c0c241444c40e84d8820085103124001c8a00010140001b01ca0b142c28014840d4080380b452103040c055a181d42046400d130794004058056580000380c1c142d5035214400324980c0c425504070504044500658446c0c1081c1d009a40c1d1a4003044042e103603000400c02c5501501e4541303100102c03070303040c0a041e0040b641c80d60010030134007004001d00008520f00041d0f0310100c8403000c2000c1400865107011905000c000500c1540700c4c031800c00c05408260700a1013903480f600340c1021005841c0d417001c05800949208480290100341e18001050700343c10501d850f1400380d41d81240030f074030011030500424030306000703507210b862500d03698181c40740c801d451805003c0510301184001e1130b54801164410503484410141c1c040807103c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 324404325 1250 324403075 324403081
    0x605121902010e040f0204080c0405060118030b270115050312040509060114030c040801151206050702031b1015150e18040501090c0503120f090402070503190806060412030305 77
    0xd2250405040351706040c009640300d80d51820010703641d40303008910034841d90030900055400e500c614555501c86140d002c0091210b442e68441c0045140e0107040007681104151100303d01d0a03a0701c0940f06040d40103400090750003181c0100701030300e901c241c000380d20036000b07651641c1514010506803029070320300702c92101701a254600140c0c0e4020690b01d40e1803484030040100008482090040c05c01c403501c1000074802d04540f4044010094542d0003900070b1100c14042c2031000c2005680542c0d0720079103d0044a2a10303e0070a0940d1004517007c03003009060340000710403400f8030540d0107040d202d418100c107841481402d001000400100200c4030350b00300030303000c41c000380305595138030002c400705448850010303042c105414403c1c045c002042041c3c4a48840d2003002450b400c000a8529000c401d02480a0401340c0000c0001c2e07840d44545143e41e881030f0240410804960b00740018019040b6400380d030030055070180000707802c004004003c14881c090620080102181520859034296070528002645030b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 324405575 1250 324404325 324404329
    0xe1b011812140706020327010c0506091608060c19020a06020f07060e0a08030a0b03210909010603020f0306010e01030e010e28050726010c030605121902010e 69
    0x84100d41c84194510804588101405458000104056002e02c10750315925102c1e40142c0c1e4a104070004a0001d5242030000f120b82020441405590300051401c0c6018694a440d8a46896015656203d40c0c5c1c001c0d6542200c50200380800c040203000300d0014007040c1c81c0c03007841a030081c02682110302d03505044025502d0707010310a01400304440e80c481001c546a0520351480e00c141d80110368103c0c0c05510b01442c0c440324250006956031220b03401241589950703120b00e41071010740131440200d0b41510550812950841261620383c14190820303603015200d0032800204282000181c1c0a40d091501c1000106110b01d01e1100f1294445c41c20300f0200761a000110040700204810200b40071254680200100352040c04144295500c034070441b665200d506900e650010304480b913000400e9a481000200702c03502c0780040b404600803d00000750015042c104844e800c0d00c000a00c0040000d03582d50045c40b01d8a4540b001440303c100210003001311046051903000c40081101002c0c0c140400c2d5a42c0c0b00042e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 324406825 1250 324405575 324405617
    0x1c02013e070c0b1602010e06120c160f0f05060c03041203182001020d030221060301020c03041e060c030e011206090903170a0b0102060f100504110307030e1b01 70
    0x180102044559180420040010b500a1202041b0700080c000520102d6034030b4407400340d03281d86a10b0030401000ba103e140c0425160341c0f01410485904403480300401c080b89140c4002001c4600801d0282c000c03048900d04541842402880c03800550f0043c01800007241c1c00c0042104d150016003000141d541320303115101444801e0983c0281030080c0c0012404060321204c0302d0f04c0b941c2c03500307030211806406aa0000c1c0d0036400b50100301076501ca024800500340307160060405400c040060001031416448280d11400e580c00380d000fa0b00550044034001d100382a080344440c0080c2006e181c9002a40305541d401451040040e040e10304024600344070244140e6107900c180b00038402c400040003c9800c514014021640c0b0314641a2012402c2c0001a0124158011002c0515059024204a5451182140724400003520450f0344000d19540400c860700c8500c0741103030504c01700c44401e0701c0c3e03e40104000c080da00c0001260580b9000743c1655008004440760010425409080890300700d00405072549007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 324408075 1250 324406825 324406829
    0x17070309081b07080106121709040203010f060e031518070e01140310020c0c09100801050a02040509072d0201111614061e091c02013e070c 61
    0x19140c00090032280c021880c41d14428001c030b000c810b5886031580ca403801402c0360410700c103001c0242c102d400d2080004070004041004840040c15a0741450000000708080f600241c00208044c040782c2014006103400c40c00b1100104422002080041118201c10000741d502038450849120b00c2e0304000990101401141e002d0000e40e11001c0c515039640225405032548041414003902079040724002d403e00ea40215680d6501030340c014a90888040184110180020407040f04080c01d05801f06002200303005250190f540c00c00003588440c10901000b1801e040600308109000f0034145072031200c0141c10003448924041040900300c49440381003a4050640e5100d034210030700c3e000602c1e618041c0c800001007019030141c0d05044e011a02c90038015511903094032106c80d0310920b45007025220f1802c00740180c1c07020040e81501c4040604020300500120442c0484001d40d4480803140250b80d0003070884090881242015981e02c03510410300310321002410010b44407100b000030305c1d0083c484451410f01c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 324409325 1250 324408075 324408083
    0x4021309030e19090c0c17130909050a03030c1107050402090607140a030e030303040b190b0d0b07110a080f030408040e011d0a050c0910120c05072117070309 69
    0x983c0c80c06a05008100440c0c501540c8080b610381507118200b28850070120036603d5100021202e29410100601d1158105500210880c04480e0000c224081c041c01020451407250005007074001c018a0094181c88040d44681d0030031044002608a01000151400403200300303660040c0d650a425010a580317108400d0090310f4101c45588100890074009031030302c0c1403800b9650b140b034075001355010940c4030f10043c1c40184c240c410f40c60120b2184146440004c107244074030403000420f0030700040416100c0c035000c1429150220070400b042030721034000584203005070548019121441c100c1d5105032050045074120f03403441c3d50100c0010100300f541d404460242030b0303c0c0140c5410f503950302654180810050540319840808a02081c2c1a00c4140a005d00031b0042e42d60480c00d1400301805e01a01c0384800e900101040305020304150b0507a40d40c032408a0303e10f800e07a15650b9546103800d269a003489100101184d030000c80d0b101c000442d601c02e200c804808601201c800e00f94076054402c40103400e0460020b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 324410575 1250 324409325 324409339
    0xe06092220090405011203080103060c0c0c0b0c060a060f03110d05070b030a0b060403021804051002030118060b0a0906080910180308100503030301060f11250b0304021309030e 77
    0x1800403680078020b040000811641448140c2c1c03640300345100c081032600c0c010040b840c2c4000500006096130414007150400345415040300b1000c2d19514a10801507002844400740010450000a8140240f60340301116030414043d05160500d0030940104521014242c40b0300c8001003842e079a1070b0120701d0302c80c0b5040f83c2201d110b1038070342c450804142c0c81542c040000310300d045021540b50410200b80e500700c0e500201140e64040c1501002c0e0805500100100c50034013810140f1690722986201941c041d003065130403580f480041080d40340890b0455006903203107160902c00c002c10164407665100c2660303110f152020343c0d61030f64080286800f0003c6021086603003000c040c10500f46120015686003400f90390b41072402d03102c00a02144c4809503001d0aa016002040184007180c001c0150901c0f1040ca40740450451042030287c900344005110111600a4182c0c60040381100055054001d0041e414405295041ca42d0010380070100b8444c21500c1d1a0f220fa010a0a05025222a9404180180c0300e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 324411825 1250 324410575 324410621
    0x302031f0b13020a0909050402030d0305061f0305091203150f060706050112020f1009060323040b010303020d1b03140c010c03140c090f130b030f0d0e060922 69
    0x40b5001e5004104a0380005001c200005070700c0590f4002c241c02650060058040c008881004801624006001540280b0021401c0c1c2280d00c01a1025603a8003195a000030035003055422030342040540b2104415603901441400815403003555800043d04e07088540085032480f940103d440390243c0a80030349850303d4031000203044511000203801e164800c035461301c1c2421400003008540c41034101c425001410403c82441058000da00034104c24880c040700118001105c4904040c61208550440d8102d9290004108164042014034500c50050a00f424150300d8804040402d9100c0b07000601000103000990a00b00d030b03600f007181c0d01c0ea504140240b00030400844050068000c64036088409841311001030351080c240c10544101c2100100118051030300c103000c2040c0c0c80b048800346a50341d9640c0c00c024207903a50820004c005411040090528a01701010107452000356005050160324100f1038020541e4072502c49442c03d19070480181e00481c02c0110362401814005008a42c0e41c42d02054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 324413075 1250 324411825 324411859
    0xb1807021528140a0f0f09031709060f070503100b03010806041202060c07080f0409060816050301050103020117041506081f02040e040209070e03060f010e09070302031f0b 75
    0x10b114036400805000a040e0360748121284221400440c01c0d000740c0b407880003ca000501c2d071345c0000c160300d291039101145c030b00c01d00000750040302e4003c1c0c8100d000c5603c1d2a001c407110803030301c405180e000b06800c1c084c10303807454090305001001d20000c1c509010000e001000401c04501c08a411018000c1402e42c6905c96854403c81a62814180d0302a9142481e0701d4a481d1190b2002504074866590030750180c0c01c1c00810f07500c8490941090110400726102400081155400c0b446014000c20861004241c20821404407a40542c1c1c04d4000d03a0190341004010300160740c01000c1c4d02401080241d40c603e00360364030b0411103084d10200c00340940c0e03d0b061400002d44801e0026010b0100321082222005070312030410040120310951003501c664007052400a40545400390300c05500102e281003c81c0312081000009040043c00ca4046602080b00c00051104a85a51446511825810045c0106400d54002940d903004100d2140c03003030361810798200401e250540110321408070150a40031850f5a03959 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 324414325 1250 324413075 324413101
    0x150c06010e06121b0f0f0d050304050108011d01030b090c04060b0301050109080303010e010b07033b060c060a0b031e010203090606060a12022b050709090b18070215 72
    0x44803403080800741c40c2060b4103038000c070320120300d22440560161031903900d805010003036585005e0554407503640d00078a041340d01e840003042d05d403521560155035210308040000d031040c481a0000c0c016861008080d10440c0400c146042c15281c200b041703140c559030f51910042c50322080c01c82454106040a030001805071101d4055816030740240c03180800755444002040d030b28002441480c1c1c1c41c049800040000d10f07003801c011705605c1e0003850314088209030300d01240b05044a520410b100000c0c0c851007094106c0034688802050301c822141d96160501034070700d0641d690405071107840002e98480c46843c003603501700080402014520040780c0f5901c003d483d01030003500129803000e034500460700000c4440c074109044441405103074880b89411110082003600a4002c0011408203022401c12505e80603484030000c01e61401d03007070004c20319262030040201003501660041100c41c0c1801c01500c86603890412002c0c000c1c104192001070360b990100202d142c00c40400081905144030400e000151039880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 324415575 1250 324414325 324414331
    0xc030f0305040606210b060d0c14041b05041406071a060619020a1203050c1603021203090f010c09051e06070206070f060b01141b010608030d090215040b0405150c06010e 74
    0x515209207031355480038450702010078a0014141042609c3c140b116100c4098408050341001c0d000280990072140c0e002e00c01911441c0410220742c003c01c0c2000144503034030440001d0300b802d0b11401d0501c0310595036581030b0001480d90904400c010000140c0c01d40301d4200307450895403403402c2d8440c103840180000c1d4503034880740d82c1075072101014040704a840d8001c1c0252030150900058681c50b10b0f461007040e2a2052034840120214080e0840b158140300324a0061805080040050410200500001030071150880481024480d2601c820809640c2e9031a002c1405425140c8005003140c603040019000d224038900298001004a80b441c14025004c4060450610980c02007007100300400054519414501c45001009001c0000c400140c8a4504600c000b090440010071034540b2102100e007150041c0300000d281c16952400503042d46090384510840343d03000007171145800d040031011540791180d40501c90203003011011109452500e2000c6a48419108082d10440e58450000e0b8405034416 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 324416825 1250 324415575 324415583
    0x1203090c14090103080c07050307030812101a0c010e01050703060f080a0b060f040b03070b031b04141c0f080403020a0617060915031b01020d0c030f030504060621 71
    0x225001c0394004014408041180c0c004098903196032869079102e9407540700c0c0740001b1041c05403840010f101d0700d08100c8070029500c20741c00107440c0c145411a03240c000f80e00070683e02e1041e04c850000c10102d511000c00c500003400d10390040d82e0f00c4003071401302c2d40034003130b81d0200c0c2045611384010020840d81c50340c002400c3e248000d00e803032200e80d901c0604503601d20012401400c1c00071752402003902c41c64100554008030601510100d1305001007170000382030001651000004410000800241581c1074581200d0450a4101c00341420306005058003901484801140100030420401003020440c650303455401d94080750781c0504041a15209420350443d220490040c80321041c08601a40108120842c24040998030092035035250200010020003600160212080d1590407a1544051100c040c3d06059001d9117040104a48002072a008010310350f02c007000054148003002a50003030300200c502c3c1080ca00400c403500c0e24245100100f000f540410450381224510340840401003040d0310200b801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 324418075 1250 324416825 324416843
    0xe060402310605070312050a0f021c0b010219060207050f06010311090c04050d110a1805010e07051204200a0e07030c05160201032003040b0115020a080d0203090a120309 74
    0xa501c80a55450081c104c000340840e05140c0030140c000e92681c80030380c0c4403d1000d0301140e1808000c21240403a401300c00002d2403000c1112003400310341c0ca40e000d000000c407028401051040314a035212010075407022002000b040d0000303828014030a040261050342039101c3c0651b843c5594903e40a00c600b00e116210f20b00508506001410246841c000e0303a0454030080e024078000780d40c680d41c880f480140c8030b808580c82141900c001c6140c01d0751409080000e0040100000c2039418003021311018800240001c08000d81004845556110418030540060b80120701c9810500c0e410306c1c060400d00c480d0b84064212041c0f07000011200c80a5069901868490324100003850014004075110700c181140070910500e0386c480000154400c0c0d00000b00c14420041600c2a01203840203001c43c1d81c0240c8003520ba44c60254018007030381510003541c801e01d441c503000400c09080e00d55074550381f40c081c201e00d00c02a1a404000030744d100e18180008640c030f560050384000e410b900150098010540c1c0c150550701c480c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 324419325 1250 324418075 324418079
    0x71715091f111c090b1e0c041512090803101401020c060412080d090f02030f03030906070c0f06050a06091d100c05190206060907030212010e06040231 66
    0x480c4030301c54414611081880c030340f890610142d10340240800c4481803a41d9034080210201c2d040040307490165400303a01d88801000c2603a4500350506029002d0010781404100800540d0f0280100b4814100e150078a08001a5030041c10001010403110181c1009030010401002c0000c4081d49816510740d0240a4551103207000126503070b4040b011050f820800400c070a1140704404448021060f10170784125107000312aa00e10f0054480d01ca400300e8894210031000021458240201103072081000000e505600c0c0988055594600151200c03040c810854040c41c240900d00e0240c0d401c81d50820020301c000d040c03080e003000c0180031710701c40e1130700c21490040c168407401c1044a0b480103000d000c000130910070319031102c2d4000901c12031207140181321081181d494070800714103000c3d01c81c0f1126000b40043d4540b0b803003070000559000741100101071042143c148001c3e20710480f10b043d11142041d105140d9103c00108000303110b4a086100204400a10390381d80c90000c10541617005007180000500315 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 324420575 1250 324419325 324419383
    0x915090c010f0e0a05280848040b090708041b050a17032a06010b0301080312040212100e0c0a06021203070c0804030f02010e1207171509 60
    0x80c8290600c613881481d5041c200680d01d0180c0880311601d1420003002c0100080c182a0003c1090303076400320f074444e000001004402101010000d494054645044080d40595480790034026440501c81c0c10102c0940860314860300c555008102d500809842000e483c02c11308400b400c08181182e040320f5044a18840c540f403412840d4150040301d0024110a034071505205001c0306907618459102102c0c4002c1c0032038074100a041b45102c80b0003c80c040640c822191024000e030400b00142c00120b000c00c002c02c010020f1100c004200c412240e580c040d2a122a1694800203003645441e02c1044031920400017450440e20311030307018914241084003240d10081090050148030001841010050f03080311070741c400d4181c1c100008642c0482d0900d421a8544502c0c2d0b14407a550304190801d5481e9080740301d4000455810925002ca240307011a6600102070340192601d03650314260040c60410b015050a0100071002000510405003506403013118a00d03000f03c29551b50620161070659084000324000281 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 324421825 1250 324420575 324420587
    0x50102011b0804020d0f030801030311070b0a05070c170f060603061006080c07080a0504050102160b030601050904090203010e0a022107060c0206070b01150e0306060a0501080915090c010f 82
    0x41c5401e0003001840341041400342c03034144004100380d030024a01001d86000902c4039610380b482c14400e4549a9155041d0b0800422585d01a0201003a0341c2c46100b0030b002c100849030503200201c40510301035585000b1450184892215540803d28007585100c101041400c04104d1402c2d0701081d604844260b0754640800d42d88440c1500c20f040d501603924000c0c4401841200c1803980410041d00380c51034002141e4551620342d00820300c0800142c4045030910040da0f0500075008c0c000004007201c0c0c0d50b141002003a044510000d41914140540002c081c1111386458101a404640040080090f008002507040e1501480d9008038441d00443c0c400c4100038211081c01c3d000042d584000b440424209101a2a0000000030981e070000040c00f00030009908000694040d168215004c0c80c06036050002520040c440e007225071007500001c0800c5081d89840d41c1311030441c2d0302440c04034015240c0d00b203000e0030910b400703280301d04520030482000261840003071a020740d039500303a0300c0341e400b218844030071191 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 324423075 1250 324421825 324421841
    0x14010302070b0a11160309140306060108070806040603020312040312090b0405041a0910030b010b070305030604090305210417030f041515060e09010f06090b0c070f06030b0a05010201 80
    0x180300300d0004500c1020031941300c20049014440071914010b0054081e01443e420002c1c1200000c00180040c8090322550b6501001c100f070640c020001418480001703407010400a081c0010401980c0004040380c1e6a038018a00550700076059540407040581810295405070009913a120000c0c812042e150303101d0400f1324102e582c440380403824181883c081001802a4040780b0354111000c10226206560314903451307000d4a16602d0794080c152451402000c04a01607000d0f02038000140310340004a608901100c2e0310520403a400640c0032500c2ca41075a15000c2c0c503110005141d240000c184266901c403c520740964050703982a8843c9890350044c082038842100d06800110b00c1c4004a800502c0030103400003041604800802c2c02d90900803182d1510f40d855010340300148924040403030034101000e8042c05042c52100441c4001c1c24501c0180a541d02da01c5500250b68000170f00a5041d41c06114050150005800c1012266521034004003c4c1c444041d0007132068405a000103403560052242d0380c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 324424325 1250 324423075 324423083
    0x1620150d0b010c05100905010906020d050a0b01030b03210f07080a0206091c0503060f040c02101a18070201060f0b031609030b01060e0a05030601080312071b150f0f061401030207 78
    0x1a171781854041601808620a048980d5922038070302c0000140107001400100591203c005031074900080d401c1705a50360215130906142c0703008182145c60310041000340242d00f5a181c401135440882034801c110f4829000d4890420101041e11010010120000c04600c0321030f81c00c0384e01640f102004c035038843d03c0c445100000e41d50001245225207000d0000b655100000404108513190001c2c0441c0643d50071000b000c1c010b0f0041a4880301d44c082c14400c102d90480c1039481041c0100c000c00114052101516101c203881504400003507450b0300c00d410103805006600ca00300d00e134560b12610541a5042030383c10108841042c400085207910400c003250450307030425168185a460017200751084181e00ba82e158000c0007a01c40441c0c2a141006018020002c01d00210f6941d504140301c5040048041c00000c100403c0d2183c9181040e200c0a203055803d804c18400c0300441b0051214000030000c0d4100da16104d0b0404c610804003071103562002085845428942d800407103084011402c074480e125000f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 324425575 1250 324424325 324424333
    0x2120304080a171903051e1303031d0a0c06270e06060405060f070606050a061409010c050105040f140114010b0f0408070b040302030709021620150d0b010c05 69
    0x203004614044492068401d0380a40300b4039182c4a6100c82014070700200240c0042a100c0b1b0078040032900e00c80c0b02c20070302c0070201480b034020305040720503070760074060315101408050b2500c108170072004000109014a401810440702035441c0c0d031401c8015242c5c1407184c1008140008842070001041c11244079810100e4110514401e00303000ca00c2c2c02c0107501401c5541c020106120124494484100401a074006000b03d1500d80b0500d14014054075895009180603c4040300700300002500141c00c542114402c1003c1d030303112600000102c0b9021f140d40b101801b50341c00c04040c002402100001c0031030300d40c01030b41c0409004c58480740d05400d80300b1191311014a11407040040044147d503001070003400c00500311451825681b424070610b003203010740000c1564080043e04004525080203000010054080c0560034005840303564070202c20a2030004d004d500c040f16641e00305642210324103003505401003220f408007003081085661078020507030009400b1b01e0012054a00c4d800780d24200789255203c8010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 324426825 1250 324425575 324425593
    0x11107050a03031118191e050307060509010f0305040326070e0619110307080309030d0b010903020901140d062405030c1c0c0801020d02090906040506131d06130212030408 75
    0x401207000d940c0a4001700d00d100340e400890343d800c06a000c60b9100a010901c7c0300030742e003414105030a00390198007100600404201c0340c1e00f1039030480004c07480500e45040008541e40d40c0c2c24256490511140003c2008140c04c21120040d8866600c45005041a68a80705001c000c076051007038909c501118642001a01101c1c3c160841c424121400079070405810349061100c1a5501d041541040ea1100482e82002c0f54800065202e07100b03c640415003460504c107410301d5500414600c2c00b040c0201c18070841c2d5115440344035151640c03030041c220b9101c4001c020380e808030303181c119103c1600900a030408254140008140c60001200c0554804c0208484000104800d940a603802510b07001c88070660104800501c80c007082c805050b125243d050096a60210081004490b000080c0454441c1c1c2c03501d4180003013911a55110f51450158902c00103207400c40107c0c46017004029800d501c80b0344642020807000f0100c40c0e41904903075200383e4040900b02340c010ba045c0e459000e07901075858076a01c08444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 324428075 1250 324426825 324426829
    0xb010305010b091c02032e140c030408120a020307030612080a0f090e01081e0d0f0e0a0506070602040f053a020907020706020f120f03040302011107050a03031118 71
    0x2c180032050f59001c0c10707031800c4c8242c0c0c046800d02d0401901020016500b800320383c50340310000010520010100400c0002c0300001040b600b6494000c0d0031402d03d0403000c000541005424000c071b640c1512456020f0741203180508803031300030750f104580c4840020f045c40e200140030000035181451b80c95011078680d0610480d030400300c5045841040f210b04005045500180844201c1000c601810b9400302070f0200c01481100e5880008102000090503404038102a840ca0350100a528102006207003c1001c0059080050300304142e035001160f20903000248601049001e50040003168a1020a542e980303513900700300806003114070081900c5010351030301441101009148a00e00c040840c40352a40a4085d40200e20031060450380b07100940d00c10740d0301307001d41a01081201101d10301040203142040e140d1580c00d5440c010250300484003500031011404150003034100a90320320840000303d803505021706040e03590f024214419000f183c50001143d4201d07003078004413000e05040c0c071440050b40c140982 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 324429325 1250 324428075 324428089
    0x109080a110d080f0d09051501080a0f24050a0e03071e02032802040509060c0906070816050a120516020f040f0c1107050901030c03031d0604030c03060b010305010b09 73
    0x20044820310804c001c039800340e034044806031980034070b550800209404d0382e20740b40c1c1c542241d41c0c000c0c030042500c41004020100300010b00030000b55100d244031100503064907002051031801c0643e03114403c1c019101c0c426006160b4003662080181400600c8550104403105440744641d031005040300c003290095801c0840144c2d01a00c0c03103440070701240d076a845d1190007040b600c0740c2c1220380000941100681c20651074180502508801c24401030012410249000045440780d10000f0780030b0040401d0074014007040340e007600c000480d0304030390480410141c600640ca0b0703c280b55040700c4080c00c0f2416600414440c600f65002c03407a40100780303101000c0d15001c211982000040c0c296025803648417030018800c45004010071074800d0f440300c0c030080035044200c9017845842d8001ca400349041d100100b003c2000f41c120481200e0701424054000e58100140e1014008021405a082803000900008200000007950100c0c3d000f54003c102e03904048004605542007841510b008490510411005141541e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 324430575 1250 324429325 324429349
    0x206010e040507030812040201030b0906011d060403050d1e020f0606040e0f070e090f06090d0c0302071e0303030b010206090703120c0c1706010b120106030903050c1006050109080a11 80
    0x24102c820043e541c4da41d541169005101b10725080d55190140000c55806000721480100c084a480c4401d01e08040000c040483d22070075007200703442c040c0307215043c0e4881c402183c01942e000400e171140c0c0c3c01000300c007408080b0215410a4940c012858400040344007248041c182c1820002601c09074030307060100406441441007203811409041002c128040c02005414000c003080b84160303d003460301000250509800e000070510b0703500210200007003900c000c54035006160b00c50804249009880c28200c0c50004660840900c0601d000380c1021192100c40170101101d2203a41c05000d50003025004a0320303014103a40615240c1d100c20380903c00a82c006103c1c1c0a18031507271403c001e10003116181c43c0e103420207d500100d08441e03a8031002442074000c1c00010701420106149130300d0300c050018000340311001446100105603032644040201413056084030410120f00c4111410b0300c0344107070030344010704140c407034580814141c540018122202041e2200d0107600101c0f9422000c295000707106105641c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 324431825 1250 324430575 324430583
    0xd02010306090216050f011a190e0112020f0130240311030c130506030709050f1f0b040b09030a05030406080f150d0204020c0f0d020c011e0206010e04 66
    0x41d890104070075240788040c0c90540356480d1000455112410028117118202c44009440e0b4102008d5440c0400d112424041c94401035400301d4205400c41014040003143d6006546070200c4c2100000d000c0030040c110918240c0201c0b4464200350b1400b0042d51030800d611031554214010144c0001d4a00300743c0e000490b028440034011941c0380310401c00012000342402c21500c1c50b02400010f1060000140604c01c2a010550007001c59030700c2900010100d00b9403406034081c0c00d843e800001c0d0603440c1442076100070000e5100030b221604061050448502d001c585001d54489500351040191400000d2101140d103801c0b0518506824085140c060b0741c001085c00b0b030144901c00074500060320070001003006201c140d4034070302107003007070504030050980140494018501c5442440103696031405011004c0d64101c1d00140c2d641403015183d0305144040452402c0e82c0101c0103007103100c1307401007002940d8a400340d07034510780c2c402130b1070881105040c4240356000582c0000018410204000e074110380017802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 324433075 1250 324431825 324431831
    0x806011107090e070801050a0e0c120a02090a020c210a0c03020a051510090e030904020304020d0f2103020309030d0509030f0d150b211b070501090506100e060d020103 73
    0x102e005103410f403601c0034100c0500790320803c01006031038002e104143c0c000031011003e00004d076141007856518a07180100903c5155045059100c9070400c000d04800243e014006800720302d010746000c4000d4021417245101c50085420f0300c0d14032907216841884c5403130b40e4408541410021a0101c0307900c1c0c080c003402c03020b501c9042d4035400864802c01000e240303045220082d4105213058001d03130b81c03410700c140d0241130002d08103040c0801c50780001c41952080704059900603181d030345600000c0c0c64800782c24406007108000c5038030282070000e20254415006400c0b200700708074090701c2200b10200e10044569082c0b9400a0002031501092a0003079134016109800722420103041d4003203100702e980200d041401d0907681b100c0954903e50310b518203100411200060302e040c586056400244501090340000043e001c000c009440c10401350350404c02d00b18203000f0b076074031500340c3c2c80c100b4020034542034107850364460000060500480c40640c50140d40c200c003d50b0140b0344426041c4185450700c024200d042c161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 324434325 1250 324433075 324433079
    0x303051807180c090b12040606090c02010e0d020c220209100c0201170403120c050f04080c0a0b045012030f0406140408031909080307030806011107 65
    0x41100e80007811144a9501d542a41c480881003164140a058800d02910b50420480d60309003174151026140d94012010b42e6070b4551500000a140d2500031000d190320b460040f5814640c15801801c1900d02c201c120360384440c00308c1c016680c1e6080c1004007a400a0140c0e255010340310041c0724032100080e41c9101508151015000981c0703545401c050100080746400c1c84019980d2009007141c8404003011001c4007401e0903280100100fa642000e110465200e00c0095081c031b1017002141c0458044100b8540c0342d0340c071440141d890703c5503640d02c54032400e9484030214880c82400100c0e412207810005116000039041046210301d4607922004240c2e005100c80720804074006024035554480c0260900c6450105404000d6124004c1c144503000350300a210903404024140100d506803505401c107004801c08140c0d4a0503070703100c1d0fa005240c49010200b0900c60703207407000069041490389610b8120105850305069940c9000303041014000a04107000318156501500808540510610941d001070b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 324435575 1250 324434325 324434371
    0x301020d0207080c160b070b04050c0a12060605031c11030405041d15060a090b0a0906090203070f02030906030c030a090c14030c011b030f020a050105090106031e020a03030305 77
    0x40c000320003d4500c410001a034651056080c40200744901400528142050401c040386585015958006003550440700200d010300604010350018800010007051a4a0b102c4e11406101400d02c2011a041c0b42001030200f542d19001c12020245ca1515000c9440203076040011150090070360342c140c003140001c20000c10305803030314054004504014004041920f00d855140707454000d84500425001005c0b4040c0800caa40745100356080f00c140b4000442d000840d40001500e1405030b50040e15641e10704080080c160301da80c3c014500c2801c41d40ca8030706031400b4880059840380310b010f141551082041001403444400030002e16046000d0150008192445599180c00c449081d004101d15400c1c203e21250145010007414101040a1a12518554200303404802c1071280307a40040900129102c01c0b010300e4402c000000d009600840240b04074241021024020a01c5000540d13001c94540490400100d5030110030641990141035140d84918546048004210180000304aa4a08402c034a056 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 324436825 1250 324435575 324435577
    0x20703090f1d0a050601080f1902160516030c061206031212050106170a0b03010902060a090e0a020a050a121803050d050907031a0403030b0411130806240301020d02 72
    0x54194080002c0950010b210481c12204004200f82203079401c0408100700759900c0754440d0b4211080000a9020b504c424043c02010170081d81d842e100d035480852100c45010b6103d1144a115000c0c00c19a8022400341e0500a03040703080e0702014000500800b806c110840c8198071141c1500284480022001d489a4a035510142006204d0340003482070034480052340c625204060041c401820a8100d506046940c596816401440c00500300d0341c0c3d2480800c0c42c1c500f034220980450740100a0760752610440300150507a038041c0681488040403000143e80e103e440c1c42222410041602c0701d90a10082c4c210490300052010b40c940b681c5a02c0d414152082180025403002d10b42c071a031141900c440310082624105c440041c0102103d5020b59410000300d03008007a00f0b0244502041c0110032680ca604043d000b525610400c1a01b0500d01119242c01c2100d00303024045254861002d81c440654406516940301c109607100c114001003c5801c51b5800b0f10524544000035000c0d0000d418200304e49040e20072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 324438075 1250 324436825 324436829
    0x31005032817070501021e09011b02030a020613180506061213020301050106020312090d051603030e0d0806011704021c0f12020a020a1d0604110d0e0c0103180503090103020703090f 79
    0x40d0fa9001f08160a84103121020f402c0115040c5d01480c1c00e01d6401800202020800841e51089030708021010007503480038000d6400c42a005001c441d6103404442284403480864406e6030f0003900441c18026013031000d8042c1601480c401441e06044c000003101820080901500900324400c4416481c00162400c0c06024000c0400750059a2500c9115984180344040203020a2140c6c03c51003040e41d03402d8111042d2803c60171001040035022100d80b80c103a0080850315060f207001e05c00d01018080199001365035030f100b0002070ba139003000d4144180407000c0086094500a500204400ac83c80b2000d01d52802816a0f5005444405019500751110110f13440324140d07110043c0c00c148450401e5040115040d0024545000806081288500071f4841c0d010301403c500c1c402c0303442d140000000308200042e03a0a510001a00304034000d0707902d01c1643c1d901c00103c0c3d224046410188016030250b4449440c515041c0c00c000a18540406200110002c0d400203108406001202001040d444111944140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 324439325 1250 324438075 324438083
    0x30b18010f06140105071205090d0606090b0103180b0406020d09061b0206090a110609010e030f0d031a030a1104060e04030c1b05030a110a081203100503281707 70
    0x40e1281c2801d0919048903e0482080c1c1848400c121900001da41000700c508111180d1070700c03035211404100002ca4000303042a018248500740500810440c5103988640c0541d20262001c111004101200303000281e4030b2040a0080468003000a0128885070000d20800140110010780201c2582d5050b085940c11504445007180600d94a00e04680400010b5001401d100c0105200f200e03036514400c5116803014014081c05002c50100c0301030740510f200c03c0581800505448000740440e40180e510103018190b080042d0a107030380d4208880c41e0b0f541d03440b808200070340a020f904607075450302861061150082c0d03800c40e03501e01c40007600b009400900d500451003035603501c3c041ca0041c24440102015109807103200706d001c0108001d580c0e8001182e40e01d81d130341b000714410203040c0140051038242440d03222621600500c00250a88203918000b18803646150607841d156944420a055490306140701c03881038080ea0b801111681001a0008004075104404074030b44001281076101c0d0399040150216 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 324440575 1250 324439325 324439331
    0x31214090414060a061713080d02040b0a0e0f030309010c020d020907020304030b06030c0f010804030309050304090e0f0708030715090203150a1a0f10090504020318070608040309030b18010f 83
    0x91504c2e0040602c1c0050820b842c02041200000300405801310025000030241c280320960f04040104003015242582d1003810215110b40d0303160080340d416403028444400241d50f181c1303110510300c0c040d03601c650f044a014005500f010300d060010354090b6500181680d000002c1803001300140e43d40400d0031f03c0b400b26580656107440c03841ca02501c6071440500b041b031281e0480c8003016004d0702d4a8480b112400008d01e4402801c0c2c8550406a00a110a15019040340000280404d030710034660803851804401d102250810340300392074000d882c0c04050280800903007007040000c0108070005d6514060751011840042e450000342c1c0024600312100c010040840c58100400c0038000041c4101809030b0601071f001c041419042000039030080000309442e204850031005414810320948800d001744c039025004550301e08103e020000c8040510646087d584605103010881030b11403280320b4051130b45502c41169041c11540c400228400042480302e0445240c00082a69076090040c0c00f215a0509400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 324441825 1250 324440575 324440581
    0x2061906091b080a091a04020f0d050f1509030a0c031103040602011d03070302060c0a1211070c080d080103110d0b100302030d09030308060603100e0f0a0c0801031214090414 76
    0x1070580c200c01446074800a2174250f100000c540341d1072a07403050000c680820f1195548901c000342140042c40304064218514269140400000282c1d15010040c0942141c1640d45280701100342c1940440d05200903402c140800c9103c3ca002e0304403c18150303c42d051110011403400b621a01d950440d60002c00140c0d100c28403001880102a00e0400248004015501d410300075100690780b034801414a1050150008500b11080d10515602c0e26030056048184081c560121207852940c210038001c0d40c819589580c001003080e00003c07140e07826070141e1142e03d8540c1c84d680791032103400500c058464100410513001c4001426140c0400e00c81d504000c0d18000090550040c90302c4c000c0f024021205010010b2002c0c00480c0e0001d80080e030105080305d13029620f0340d54034069003802c0e40c203500c0f0f89801100001800106107440300c1080c4968541c20041190082100d4104e5400d482840013070524404824030303003403042c40703041c100f00c3c410003480146150041c154045421500340020740c00f00d2030484001c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 324443075 1250 324441825 324441827
    0x20c09190b0f01020c012a05010501090c05030403020604080702130e0d030b100e060c0c031e16030c060305180d110606030a0b0c0304170f0405090709030302061906091b 74
    0x5812070302802a2007003002c040e46940082e50745c1000c0d00ea65030510072a0700c18450000500c0c20545210300034a40b002044100070714096000c1d042c00c2c064a001036007029003003404140b084040e24032858042e80140050745a030b88810300c40354007204013030317800061b400f2102d0700442c00c07801100558140341c4000e050300e04006a00030100c0d909641080e03c11074046981001941d80032140041c004000c48500d03585d040f01440b520b2809407034001d02d5405001300d40340b502c2c10881c500001800ca01084094a0800c1260a0780240b14000c5020060005c030b80c228050000354030a6000e298040040000a451242c1e06400e140c5400c40c02e4402500188451100005400040c02001d03040740d0180c1c010202840c0950311411142e42c000d2891980000104c005814001c0c445096594005825283c41d51038044e14801d045540c0b060203030502414030345012440b0b180c40341c0005070071250194040c004503155503541740c4100700b0703140409404540310b41d004101441d1522891740c2106038400341030701303032422044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 324444325 1250 324443075 324443081
    0x109030c12020a031d0d0c120201080108070506030c0c0a02030708060a200403030e01090e070309020414150405100f08010f0e0607090e0a110714100c1707020c0919 72
    0x1030360408540101d807540b0002078001c60b00480e2017030034413450000e040e6a100862035005c2c101c0005806651030301e1002410760300164095600314000e03614907e00344e0b00e50140e01e80d1840380740b14540d000311082000a510080c1031020300090900d00090301c0401000b6000285000701c640c205c45e04507000801840b94100c464411082480100c0c1d018242299401010f000c55000b24030020f824001c071454085c1c01607120b02d102d44081d00198101008500306900f001740188000710040703005501d1312100030f0004c2c1650300021b00c03c0c460709003525904036408080c80050113001e000c4c1c0740408101031010491468540600f009024031100014009513032540150a850085480719502d401c08400e001e006a404014802a10802100c0040c02e03280e05040c4402002e124035025407582c0041000800c00c40b1070301440080042c3c1d07008441c0b2500248064204a0702c0800009000c41d02550200003045c98040c0201c0c0e102406005848118403540d011a000c0030b0300b241c00b40440c240291008030b60301c0c1184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 324445575 1250 324444325 324444353
    0x310050f030a020d14011401060e18040f11041803021606080405060103030c05031b010b030d020106050a180f0c020f240a0b0a08010c03020921070506070f02030109030c 74
    0x24010106100107801040d5480981c1c040a080c03020102a402d030099000d412071f540c550b09810030100d5543e59802c004140c407481c01c200510850340b4081200d0034100300c0c00e516004640103098000c5c1a070340c80d5600041122011030321a0040d8880e503070200a07160110504403994002d4014000c4000b40718980d017011003103a007004c1d06002c071410900020030800101075055a90505100d124046503041851550184000703808441074140740780d61f400981908101d0f030311602501144c4c0f001e0000700040e400e807102402020703042204100d041002907140405006501c103a604d00040c46050541c00704281c03031440c1444005640300000c1c1c00d000348002c0007061214544211900300445e091003070342140d5100035262141054503500160403640d2000240f1004269a00003000180200d02000e4040c0d00b0582540d480342d10160003c2003004691040620240314074030142c00d2030342c107020070081c654021003001e40d80d000c2400704040c0161001d2040103900c81c0a80c43c1d4100190941c54184140c2c4c1c180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 324446825 1250 324445575 324445579
    0x41502070503070f1716061409090c0405010f03050c1912020a090f0e0106080a0b0103140702071d0c0706050705040b07081e120114030f0109080406020d2a020a0b0310050f 75
    0x8030140ca4000340107080c060007540c2043c0b9200c0c0741c5000c14002300700c00d8011540040d90110742c84e01480107505090004004482e82078071010540c0740360f444103404545003102d04030b036640c4040280240c03440280d2461000c070411418003102c030508407101d40301283c100441030340100c1d813498004c2c00304110720b0311160b000341504204400c4940c10907500424008025010310746158541262042130380c00b030f4111031030051455120081c3c078509024025075942040c85a4020b20440221405c041c0342540703645442004015a81ca1500c88995112401004006c02010170000b05003c00b040c0124180000c00322140071b011042d0b22003506010429080700c911079440c2d210781041019000039001462004d04542c240035140003e04250350201c1d05100e55210010440e502c1d002c42c180c100302d090703006030054914035804c58120984542c01900c4640140030038400c02d21010a40703d9400301c08500c541d05503440985005185540c0d410521440d03007082e2107a084d5140001e40c24003090900c00008601c003041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 324448075 1250 324446825 324446833
    0x5041106130612110313030801050f060f070501320a0501140f06091002031201082a040207150504120504050f09090a05030309250605041502070503070f17 68
    0x118801407011200e51107040b040c04100300314603a85200c2540003103c0714901030030f41692440c040d074821400d800c0c03000044000c03c0c030b2240041207605001a00840404014011070301c0d040700c0d00b03400c4c03080750880c1504a50b1f0f9920303a0b42ca18500800740203000004621640508400c0900d16036500b040c0a00030454142d80345451b004104510712040c881270111405d55880c0b52841e000c0e004607209100d80e922140d0440d4040c0d0b42c03076684590010041c11410b07200022102c07580d81b110790180d26252802505a4810810040c60a200c41260380d600c3d440d070401400140741000c95560b1519001c212040c02e201503580e8402c20003400303042640e80302030315034603c1c00c0c600d02410071000a6142214000e098050340c1e20000203000450200400481190050112512440c01a04203581c036050b82d6520b44001010b00007801500d8001c228003000c1d01c10701d842e900c0c1081d0800e1000d4400d80b03296240311045108024001030991402c1c04090003030026104081210343c18590088800e000c000b40c405010340c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 324449325 1250 324448075 324448087
    0xf0807020d0822060c111209090601110106030507090501170f19050a06060305160e0c0301120f0209040605101a180a08010f0c1704030c29010905041106 67
    0x1d403105015502101003d2600d9080021800300003400e204408020121460048420191600b14440008800800781181c0c0d1b00480b64039059a64007907000040d400c184002c0114500d580207244039005240e03160000a0b4540d6240c40305883c3c40e05d260f20040d880c03582c0310014807100700b00002e00300300a070304e0100402c51050f44425a82e504d0481a502030000c40c50040d1510030001c042c8101d00c0b040350002018005207440b42401c503111421041c100004029440d0001803213022986424450440e030303040c41d41107030b00c2c10f1000301000b26007401c11110204580700e00b1006990703091034140113500a4100040c9481c007032201440d00c070310035007007080364508241c10344d80b40f003c8440481c0e0121100e90003a07041103000c280401c0e81d403440740c4c100c0806542000190b440042c80c56002c84024102503507500140840744580340300382039040d24064006030444a2000c04102e899400c3e5070301d11120015500c0030b0b2005460707a00441000c3e0001e401e0036488200b804144020341e00788040b4044106d54480c6429 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 324450575 1250 324449325 324449327
    0x4060f120c081f0803070c09230a020904020d0c090503010528020901030605120102031e061c050f010207030e0f030d0818070b1914030106020304030f0c150f0807020d 73
    0x50802004181002c42d03500d4142242000700004d1914004494480c1b00758a0f081900c1070303e901a4a903c186000c0c440c40b074000010b003d0070701155444181c0c0d05c0315100e284c12040654008509076800c941c0030001c800398000184610800440c06650300400981031404050170f491000d0302c0400345203030b8030302c886001c1c11450403500714403461144016030700e000a00c01a0060034540d031002e60f021101c9040100f01000c19001075106001090010f039880081a90781042c604040c7c3d2066004902145540190690601c01a655038051001c54203016550b1a0702e50981c0d1092070704070300146034852804041e0402c3c1e000d207140c45104030080c0c18910f6900d10001c110643c002e091555409800c841c00c0c0d41c06005200d1840641180b07070583e035441291403180310103041e40800c0440014814070461405c0c11141055134180d840c1c40c1e0145113803500e1174540c019049407026080d41c01890440e000030305102004843d018580032620781c21900b40c01620b0180c03256600030708600c107642141d44003982c0a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 324451825 1250 324450575 324450587
    0x5271e0a0b0333060c0d032a030203040c030804080c130207030206040b040305040909110f0301060302130c0302130f031202010e071701021e030a0606090506040501050c0f010204060f120c 82
    0x212450080c101c04100f6a03183ea40742c1c091904480c0c64100100203068a5480004106002440f5036501c0c14000d2030078120448506501d42d6280001d506010681c40902921a400564109000c0d64400c16140d88a4071040c01030f6000f0743c400404c1d60305c1409064064100440804000c059128086040c90410b8130003070f40300c40000300024103500450740003c0030507004205072000382005038001c00c090070840c0380040c903024414980f14410000e10b000800f4a14050149000b9294007400340d82480030102c8540c0080c1c0081180c04c030a0580030300c5165004111408101c004264100c981c0390201c1c5981048000815601c20700411641001180c20b40d0382d20000e110801c17101c103100c0840d42c0c1c168101c110b40c0240100000c3c044440900894050f84003411005503001c0c04011000700303e22a0344200980b840625481281d4100605001c10441c0d0360054001c0d240f0446d19005540500100240301800c9078800c2e0817202c081034030802c00c071500340c1d402b804400c07007581e40c06000c00c007405030b124006c0c002e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 324453075 1250 324451825 324451861
    0x50324040c0e01321309051009050603030a140c1e010203040215041208091815030606180105040504020402041a07150501080606090402061605030d0e070605271e0a0b03 74
    0x450000070340140b8005e4841c0945008000c40d032800c0029007001441028a0b010070708c500e0400e40d050201285203460080300719007680070592039010004070818107101c22a0009038202d4110b00540000f4900403c014890400354641c0000040c0d680c5854810000d07504c0c8000c0c1c4541c0120020700c01400128011240a00f41c076401071a030070703295608540024000512136800180c9082190300340700c9405881d4011a407400000c50694040b0354440050003002c4c1014095900254040e100420950605510803900f060014001600c0c0c40e03200c500160204c002080385244100700003407101d00b0f200c0120465062400b00000511055140541c45035580101414540c802e00d40d5030042000c56a03140d0499410000c2030011f00c1003c601030a00b10b40f41c0d084611600c03410790074814040303d10240850900290380090301da00341040c1810022859458dc01035441a40658110000070702d030ba81c0702c1c040ba40b504104001010b00c00386c610140720002e14194032010010b1414030a014040c10129001d403d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 324454325 1250 324453075 324453167
    0x121201030b010f08030d15030c03050c0f27040507051f0909090c05040c030b1504080f060412050309030409180201021b010e0f041d0c0307080c01050324040c0e01 71
    0xf20071f40603481c01c48141440f40d10060400150b500e00100308031003c1030982581804954a401441901091144203046480f5604a4000443c109030b00b09800d407019a41090142048412203921400410fa60004407501c0d00220b410300002e1080c00d5078414800c5e0f0143c52440010b1005800c0c5036a03030303850203900b4002d15126580322040042617600c0307540301030360b003a034001e001c0705038401c8103015180194401d0159402c54000c083c00030380d038000001695800b495012075160014145c03200101c1d0550005008038600e80000c000020f1885000d02a1420074400c00c22070703100b0641c0c14800039142102040c00310351841020384180a946c1e8000c00c000052403400d45203103855080c0b910025000307091801083c0810303501c2c5140a80c80000002d0f20000403203090f0211440984c0b2200e459640d401000320160004004200041500c1c6018034841850003000031400b951503480d00009041c3c0300b15510003000581e11500d10302d2b003036070312050400c080e40ca60480e49082c40e500000c0000c200000304001c107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 324455575 1250 324454325 324454331
    0xe0112021e0f1302250c05060a11010203091b010201092406030204090c0e1e1306021204050d1409060403020d0201140406030f1b050306040509121201030b010f08030d 73
    0x711154a5120a084829100500f01c4490541c41d03043c10000790845e410724020440500076165038000501d8071a1031568001c0c800101c001d15000411000d58007403a210303020420301c80003c00406000340042c50040c0d1505014000c030342d00c0000351900000c03540000d10304581c1020ba440000c544800315516603002811900b060101c150004507014110755840250014501103602c0b05214190140d1001e580d200c103100c0c001e03502c80180101040f410302e004c404503500c3e8600400e204071452a1200101032180e00050304000e08a01e1607030b42207604071425203494210400d1001e0f090f502904503901d0b4119000424182803840000c248940501c4c000280101104c150042c10742e0b01469507090803000000500da550303070322814001c02401c2400e801e01803285c00e0102c840f00c4021800d04a601c180203a0ba241400d41c1d9418040201030b0001400a811501507001d082803020b0801d00241250f25100d40c1400c12545945003400f1500030507809401c0607400c41006008411002c03086030030400c44c404002c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 324456825 1250 324455575 324455629
    0x90a0218041e0507020f070617070c03050d181509030807050301062001060e070f1806080a1e05010b180307030c031203021303060608010b0d150c020a0503130e011202 73
    0x5ea2400030001d2000f00c080c40341c0d001c0020040c1d07100c10000801c040c0c00c0b01401c40c2c0d46030200140d411383d07190403000780420b40a11800c5d101240b948d0040e0300b5001e0008904d94a000703192182d034001412070001101d15500c0c1c1c001c1c4418550450107007900b10074107152480c507641c980303800208524000a020042014003c03454946010250410300242400d43c5410005003010b00c8090481104c0b007222030042008120b0001803128580400c1044440300d1312618034641e1441009002400d40350f0034401c0050b0b59058680d03d0101500c1054046e08180040c20355812622068034108003104070010b00c41d81c8000c0c02480001d04403004581201d1b0301c40084801d285003941c09801900070442040182c3c880680c0c000b0901c00c003034110b5812122903000810820008500b84429090316810107465804240d10b4032000b80200e520101102c1601c1c41a03800c400b010780c0e070b550f0035903110141801c0e5448268405110790705404e4000c034014072078600e00389100107540d40811100b4841d05070600c6502800d00d19 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 324458075 1250 324456825 324456827
    0x90b03030c030a02070e0109020315010318050a0813140d0b060a0312020709110a090612320c0c0a0b1e04050703060c1b060209010e090a0218041e0507 66
    0xa07900c41140d5403040d00d0321128584002551000e00d44509500e900c0709400015001c0f8091003142e008440382c040c4085841803400065000c0c00d1004460804068024902001314000f8480203013141d10480751150385525600100300361014030307040300300184980e140520b1030b139aa03440400303d01c1c0e0340301496000c1503840500040e00c4c030009a0001d00400004081d0030003855011615200f030360b40c861020400d920860b01c21144071b010307102080011420440050024a00401d0001c14072002c7c0c1d0000b140725490030300d40d0400d07654003000001851040b81c80d458561038805500d964070007030b1401024180320a24000035910305103284042d000799880400304030011601c3c8000c500a644102c410050380c00c180c64865520006840250380d000c1c60700c000e4500191150f900c0420040c1250422043c204c042c0e240e40c402540302e034408a040c024204c04140b602d450341c01c0381070310446a00da40140c8a080707581186030444540e1181c90f10540c0f0702560341c266044d406004007880aa6030800003801da6038440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 324459325 1250 324458075 324458077
    0x7120c03053313020909070f08010b0f040207050a08030604021902032a0c010809150403020f010b0109061e020a020418020a150207061809020f03011409010f090b0303 73
    0x251090186280c000072408000108041c10b820110450030340045a9107025900c001c01d544800d10f90240620704400361800c0320b411034200c07600800743c4125a0780e40725404048452940702001070b9460314040b0b030b01441c004014856814003034609500d4421070b56140c0783c0352000c0c20802440800c020000c580203481d19070550303c0655810518804c3d8500c190710296403504280c0250541074001c2c0b0201020010740100c00c9541a000d40c001c14100000c400107540d0448002c10146040c4a400d01081144407100410780c003450190300944000c005c03201065082d11503040781d150600122240400265600086400020310041402c980903090000101d0510031402000303540503040911a20341c414015144907040786c400c98803003035a141d480b0101203010f10001c2c81e17040540c00610040040e0760080581540f5544105427107a006911020454100d801a1001070040070000c130040c0980a13494441d08a101d00031919440f01c7d40c03400a0f40b070001603050144c8185203413114604d040c40d0310100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 324460431 1106 324459325 324459329
    0x8060909010c0f1407061518020c101d011a1201050606070201052d0a121503031412011211122a0d0c08060105040c0207120c 55
    0x164040d10384c1095035462150000c8100265000903500740310b10013000303a980400980d890300f02142a190540400480c4103158810803a000e111000061103400e4208040400305002c8000200504116001025100e6560030301061008183e00d8064030100d82400356141c40101161510a500740d40080c0e4040307401000402801016511800060610b20081029000c0002207008826504c1610420840b400fe00228148a10030343c008040001781c61080030a05c2840b800c48407040400c14140310080520454880741074000c11040f064500c1c0c08035650b604d2640f036a50301030440d10941190011552410644900d502d285010101c450001207990002c001e60502c14107188484801f00001e01c0004003a03c0c0c42440c150f840a08564880e81b0600c8001906454049818504081a0819403141d401c0c101074881c6070b5400074206c0116200c1c40ca098190b0030450a2820301c0401e00c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 324280575 324460431 := by
  have h0 := BRFrame.cov_init 324280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 324280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 324280575 ≤ n) (h2 : n < 324460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
