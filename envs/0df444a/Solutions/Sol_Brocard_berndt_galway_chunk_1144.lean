-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:26:15.394441+00:00
-- url     : https://prove2.me/submissions/e3a252ce-b36c-4ef8-a7c3-46b7e9164958

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205575539 ≤ n < 205755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205576789 1250 205575539 205575547
    0x90501021210030c06020c100813050706030608010b060901020c0904030309080d020c06161b030212070b090d021b040203180717010e0303040b060904020d1704050a09050f04240e03 79
    0x2a09421a4132150441c508560082e4540340094652100c11700440c200e03820080d501e41c0c0c9141604a14042003100241075002c3d44100107602ca8040d0449800d0b160601d0003404903801741e80c28002d07140a4011600e00591007003204141c241441400190814041d14011400711140d44034154154841c507900b0b21450350009114000351018007400350000b0640c0c0c4c05c402e0003400748200030700d4600c02c41b100c5440002c022071910300700343c003c200c2c42c00d4080f50743c00e1864440e00b1030b00300035580403021540c42c81d040c001da020507002244007260711034102c0d83c4055075959461020060000a40008029017803041200c00d40b8880070204224010003091514480100200442d005a0a41d0161250342481c0d42c418010701c000a2004450158440700035200c210941d5603e000040d0400c420500290410b269141c80806030014031006100f500c0d0283c4081041c590b64600800444004030b0314140d407180c40001040022f01c05280702c040d00020110f070352400300d008098400031212101094815644002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205578039 1250 205576789 205576793
    0xa05030904060918020405070c0b0a0c2003041a0c03130918080315060913060312050327030405060f030f010807030c0e09010f140604050f090307030309050102121003 73
    0x1005a0025142c03403c0103000700c40724040b445810121400c0c0080c071603a1030b500003d413514032803400c00c00190b4002c04d00c410503041210300740000b4620006143c00203122402500c0049048041d1100721301c043c50015440c2500e00503a0140320074142c0c60040c649182001110104801003025106413040c1c15044035140c0e262030030181c210f03684411541d01c810040d0000c0b0010409907001c0d41c1d0320410031844111310310503a2002603050301c04d01c420581c0c010380041d4004c0e895081070f840441500e00c40c603950102c03414100c0c81521035010413907600c80c1c00107070340100c6480341404065644505503094100d0f03003000c1d100c00c00a4100d0f005040e001d02000f46c044100500c9907514000c4600401400010b40034950070f6803102400a20a80201c03030341001c044020a0306840254000c1d8a00d6084c85070401c16103803090200356428009841c6140716a05241c04550390200b03040707030680034038404d40007149486103590302076028040409003951076560038020701d07510f40803213250310f482010300c11440000c1030300394 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205579289 1250 205578039 205578041
    0xb0d14010b010206090703020f1c2301051303230c010b0406051005040b130e13050c0301050114010c03050408010501240c050a0206090d0212010209010912020306040b180a05030904 79
    0x780c0078941154481428442207980109640b01640c1d010751b0790400c60340f00f0b107000c102c2210f1080000340758000540185c009000e1140700700c0f40500d064040f8402d2480600c0446c1d400d031038099494824621102000c0c1c00040d002d9a03030428180042d20036481c2c5040e0204d000702d510b03002542d0320022a5100c1c07680103c2481d1502c5a24050b000884121400c0042c0020040060003103000b107a03009180052181e44001d04140250010b00c2c0801c3e03c2501c601d40400e03aa2081d6000e043c007111980b003002ca11a84502e0f06016403410f8a00702c11442c10803025582c01120803444c552b805805104003000301188100b02801214080c00203140e4001e0b1425401004003c01445445040300308450280c0c400005400410900510340e0103c5001d0344a20347d10300000c3c1ba202400400a42c047c0e140c0c2502c1ea2807110640160a403100d0076200d42a00542e1482092804101c03002c1c02541504024000790010700600d41540d0030600054200c4181d0103020b85042c94040003400c1500c16900201d407091443c505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205580539 1250 205579289 205579301
    0xf070c140c10020f070e2203030b0405010e0f07030b040e0a0f050f0d05030a1104080d0906080a2304050c030601060509091005011d12011503020a0b160311010b0d1401 73
    0x10368801811350400c00c501458540e18039009880441410304042000803210740e0101c07950340011482d041e100748046c54047d00814150302ea9602540c141000050061400241c052054540e056682590f944e006c800714003c0c0510000294860f40e201c2040c190844104107000c0c04522803003044414152a00b0044d14000450003041c0c2180e1080b1080745415034403c041e25044580e410f008134085003440ca04040a02940d04401118414490000e8400d9401a4804201c45041c0c444010036150825010140c0301d60311010560190343d00444690100798031441580b040c0150b0030740340d02400b0180041c1c03d0200070b91103d0001400454110380303600d46003001079041501202c0f010f05c0c103450607001a021403404003810303c800358060a180015190301c0d101c03800d400350301c90003007180b140503400d00c4180200c60300041c0c6c0141440c1b000842d003002c607002210b041c0120f4210300304c642461541d00b111072000041180d080c0b5521420001c01503250101c0b100300e03c501c111f0802c44611a450401c60850728 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205581789 1250 205580539 205580569
    0xf0501080606182701020d0501060f2705040e030408190b0c070507080124050409030c02060c0708062409010e01050103090c0b03090a03091a030f070c140c 68
    0x440c14000c070743c1c0c2e695000e0b007000586965070445a03a915420f03074038030b18001c0020340c04c4c05500b00341d00140c07600198010403400c5e021890401540c0d80f912000c0703a0000015045001150020415441051010f480c48100c4603010442103030b01e980300e030003183c142c90701c3d0130065550380c1c804501409045014032101004060801c803040001c030783c2c1d89031102d1140d0050310301079080a0000710101808020b100180c060450725000b0f008001300c0241001c0c04020640c0919008811080003242038541405400e45032034060341c0324004000e864007088400d61003201d4100780d601c02d070f40340040d401005201003840740ca00d00f0503040c02249004a5400e01c1d050714024544038500d080d006010081c0c0c1d01d03582c641520020f1030000b42200451900b1000c40328250080104201c02004200514900150340305141d407180e07807515a1540c0d507aa9480000042d5803414a0781c0b0380c14000103180001900080354040c55a00d440100c246490300c404070744607980c1124400380c0d0040510540b489c2001120516805 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205583039 1250 205581789 205581793
    0x60105010206010911030420030a0b090706051306181203120e060f07081f030807020102071e060e0604030b240307060c060518030307030203040b06060f0904200d0f050108 75
    0x140703885c0c2070303500314840200000c0c41303407001d07924240742545e40492a00d60000d0143c21a02c090910742000018544103d4005070b8511500300b000c158280300b4801c0d1110443c044e0f4400303c03c5400c006007582e040610041ca05040c1c043d900d80000d03d110b411241550040c02a01c4000821100c00d801c0015140c0070481c0101c661b01140070300c8200c0e1141001141d100c206854840c94944401e807036415245030082c10000140411031012041c0025500200344940c401d1b022a8005940d074844401282ba0703921540b40000e075520b400b001f1560107a00b01c042c0c1c9103001040c0518240e00c0381e032034491030301080e10036141c0301040b208008070708a4540b030090b02c500000c500421415280020040081d00014002803543da140e0f0041482c0c028001c624a455038002e0098030744914140e080180290402c41d42078400191030404201e50b82408802c445846103108000c51910400074203000140c03c02d05038407000088024604401356020401400040320715100c0401d9481d40e442c03400c81510010303041145a5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205584289 1250 205583039 205583051
    0x603010312020a0206270a050306130201110d02100c03090f1202030f0c030a030c020106050a03061d0a0311011a010507030f14030c13050a0b1c18030306031a040b01180207140601050102060109 84
    0xb42d0b030008ac0712580701e00f83c02e085041c8400caa100484454003003e40704600317071190a11080300d250300811501035012844030200070341900d25030114151209513402a03d84800348240d100480d150303010520240600d401101d20300012007504400383d920804455000d60004600c03803d02651500605110005c13900c020b1000c0390800f000250101e0152000400d916562040e413002d0324030501c0c00910f0710071034a00740c4004440d24100a085440705039014035595203400d005108509413107484454420040e5a482d040c034410380c0e8180c0d05c5009a441010902100c04034081865139014003c0d403054a03600801c3d83c648008642e20030801d6141d4000c9449020031185c10b00c000009041030320400c0803103022440c02503c40610020080404070301c1340c14041a0610284281601504114201c92090031003481d0100c1c104d0300f0700c7c8096010340300101601a840010840407201006001c01305251407001840d0001c82d503660444000401d40400c183d402603001000310b0b40e0180803250040c00496414000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205585539 1250 205584289 205584299
    0xc0b0709320d05071701060e100f0b0a030906091b0602010b030a021c05070e0103110306060f010809120310030b0601050705030f0a031d0a021e0603010312020a0206270a 74
    0x1a07550448626802105002044814407000f0402480103101c0381024000a080000c0701d140178054a000314010303641c0000105d58201c42220800f401c6030030b02c2021404c03c0b41003031504840c950007440c1c0d0a04041d1112500001f0443e18030413468141c0c401c0c0658203090713200c140c2c1c1702d03400303041c507803012055915008443d02242c80c0880c09c0780d41c841c0d04a480c001c4010680074403070484a14080c02030000d21450740d010680700806410749040e64001c23980c09058500c96070416079528002c5907999041038103904070b5000c0794094042d003a000b407042d809481c1810111103404040e0b40084507059200302c40842c0800a0081d0003c01d40e8001c202860030600d8400c05485450380c07889049032258030190002442401c10340f0982c881150079441d4101d86841502d03076000c09940780400c1c101070b03100e4101a40403110350950454950301d922009401e80741036030718640320003403c4403003030740c0c40c80650285190750f000503540c14008101480c03a803c1083c0e05040101e0044400400f864440c5018408a440505c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205586789 1250 205585539 205585619
    0x6051e09061c12020606011404120605040533010e01060206042a09020a08151c050c0907090311010507020619090b0a090305190b04080304030c0b0709 66
    0xd07001c0c90940d101c0c81070504000c44003482c0b0074020400350200f10346003a181e51070390303012807228010132099848000714020480c901340244668490340009058421611000500b103412065000380214160755060f0505202000915491020403a200103041c1d40d400340c0c0945840c0d282e0141500d6103040e040356042c990003a40d10040944003400801c191070740386012504405103411034403008005200c42c16a20808a8083e422516240000c0f0f03501d140000c0d03d40c0881455080302090040c81800004074045c0d86000300c03c0c4280041d03800c1d01508286155a44821aa080c02180700d607030ba00031000e1942c02c0050011070300f00310306070402c00308100907009a61a402506c560000e001c0500070682141c1e581a600809940d1140850800200d0705101c4640c102400c0341c04c9a00510680d0b00d521141d8034100c82403800644000c00307005a150200c0e010490240185a02c103100381440304042d66240c44512401c04111880300004500e08414030a1501c12081c070140c00e6071811400c060502074070fa52038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205588039 1250 205586789 205586791
    0x1150503010308070807230d030c0801050d0602040909030e030d08010e0403030209010c02210705030303060310090302071701051909020a03030f0507020402070b011a07030e010f03060503010f06051e09 88
    0x540f01d4500030034013005021800040301d003401d40c051051b242034001c0b6010030f10000380c0425032800600a0906113008a40a4021010905078030754031900c3d82d030b0a080030025584040a4180c41142d03003480081681c032054440c8061280c029100e035124084441c0070585090400c0c229013040010500c0108070f542e41d080b184c9034001c0d03810b060160301c514507100121101c0041000c040e5000034a00c400740c444006692024120101c801c0541e0303041034440c02810354910040c1c80d0160194000c20070a50546010360040742c3d00f512070f1043e150815035420b80b910414801507100d002c50f0355904203200c120711b4003c0848960000d00c9a061010704003030340004641460520012b000e002500e41c2d81441c49100b2821508900c2d4000e204545642e1142040070152100340501100024055114220307506000d054626880e03060740c0e007810b040306180045a0703144400704517005041d103c040101d90343d9003e000d01c6600b1401c2c0c9c0b40010303c20b03140904110b0001704030b5500c59040300d00c4000c40e605a80782c04501c0e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205589289 1250 205588039 205588043
    0x5090c011e050d0b04021606050a1e021b100605031501061704060e0d03020c0f03030112060222030809030c0603100e04050c1809060c030c0d0504031413030308011505030103 76
    0x5030388502a542c00c3c0b50251440000e003a82c480c0c0700090320185c01070f5082e0b240143c81d01a8104008135034918100704202c810a10540d0b002c925500320580c07101c20981c004082c0c80d8422a00404010500c2c8000340c0b07414141c518011510313407104010320903810104501c00700c80b8540940090076514000001c2c0031400c0b440c8280011200b81d800060034044140c0064402c910030508960740d01d545840014029000355a13100640d0040c5070381031414081c000700b40c905075034224075140008846a550380c07009500030b41d0213801d117100300d06200003c8544c2c2240000107600410043c5d030741d40d900400709070070251042c044074801c66080c0144a0580404000c000540b42c810050041c01d464a09000d45002c4010780450f9011003460b0480313000c43e044242c864002e101c0c441c200d4080740c8030704860301c5450204648401e241a003d01c01115080c0c03070b64219035041802810312050b9030400c146000380e10392240d07200010880301a403040040681c0072800900504080210003002003004000074080d204c18840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205590539 1250 205589289 205589297
    0x5070e0114070c05030d030212090c37061d0a1401030f11130f06020a0b0402011b02031006080d1e030213090608100e010e0c2205090105090c011e 64
    0x10b810070040b0340071003080a040c0080c100e030f8000000580045c0690b1040c580300940e000c5e91004511401c1000403400c1c02d061005003d948107072949440300c2d5074201408103058841b0100c4e0403c40300f840c201d2106001612403071b40c0761403400f010055400314072002c1e201064000c2804810420540e1411190420480404d29001c0790480402407030201030004079110520306000000c49203400c03019100ea510445101391403c80d50250b0b03c1c0b600780c1e02e07207500d080c000d4408400707100000c0044d882205141545552040c07100b541001c1900860305c1e0074020100720f4000307581c4c0d00003405240001c0011000c0f844091501c103010035164a8040e42160b4074030515024190041030106520000300c080030041c103001c00d41080340a58400000750f48403071080d181c81ea8036282030792901803070a06000320801080302038003c205050142043c81041c101ca00d01803c0011090104061600c030940103050050802c0000070640c2d080006210381000114503030380381840994030500e1082c044003140350f1002001414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205591789 1250 205590539 205590547
    0xa0b060907122406023007051c03150503210c030c0c040f0b3007030609020a0602031c020d060509010e2512020c0a0204050f0a05070e0114 61
    0x4800d035407070080b00ca61101e915050080300c0301ca4503800403c014684001e98243d00019986a00c02e90b1604900c2d0780501e0416000c140b85d100c00600c40e00905113000b0000010b0340f810301c140d10f0720707420003400c0618060940140f5a14039002980b40c01a40c81c0d65090904807906a07181c0000240c0d2920030b44a610b031040e000700c8414030750502d684183d601201d101c0d001d8a988040d4400c0d01034960b02d201220a00ca14600b187d8034152642520424507500d001030f040310703142c1501c0c88440d00508525103444580c525254001908072000303111180080d84902c9021403d1001c6104119018040c0e810603011548140f09480c0b03030554a5078111481c3d000c0b0600160740c0c2d2000c1c40c0c42d85c054010754004c50b402840ca9000001d042041b01a85071240980301c80c440009048640030701501242054420005220343c07a01105198059005140d50302000048410840c10340e4007003000c0c0d52085410341401001c034000c2004e0200c0c0d40c040d4580c043d169250490054003240c0001e00700a02043c2401a414000700d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205593039 1250 205591789 205591801
    0x702040b0316060801080607020115170c06040b12010b07080403030c03140f0325020c1c0506040f150e0601030b2d0105010905030c1c050a080424020a0b0609 69
    0x1201e0441d41c008801c0c82d0194268942030081c0a0400038419400725124050010f800781d44188181214811500781385001a4508101082010380501c20030405006454a071003082d80c95800810041c40c844030710380d445040740704e10001c4124059020114240e4200000c0c000989120111410f8a605007440403d1b180d20b4281200c001e144256010340b02003002035502d00e810b040c0f601451040c1c1181a40d0b050b440084056500c000031200070803030143e07004141599451034610740019495549807000c010380c0002d030300d6191401009a0382980c01042d030380003a0080c0030980c0f070004c200700705850052080000d40100940d48110510000d811001101d011443d02030400c8400b0401c80b5080821240b0000c0d507900e91100c90000781304650100e14160310008490402144402d02c00c0e00040606001501d420800300800400c0042114035024841070fa50003d02a00042c2000d441201281b01c2c018081d0503000880d4103011010100703550001c50220001002050030351707400790058a40e0001522380c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205594289 1250 205593039 205593043
    0xc19060e0c30030d020d06050f0f01020a0b1503030d09020f091306090305070f0605010509090a0809060307031e050613060803180f120c090a0c091e0306050c07060c030b01050702040b03 81
    0x240b200f50356241c000a00d4840e9131b51176400480a44000310b441a0345401100100301d4848000b507181350240e0480c0c810000825150b4400c540d000c2548001010851902000a82180e0041030280006551400c1180035410f0082001c42c042300140c40211203800d0082c25a5503211240303100500041d03c0300d5845003054171541c159403480e40c5c0404241d82c0300f0082d1608001800d800d0007640d0041c0144400510340e0b680020b180740e45960032422107440c06040300c050003095440107041c0d40a15480d4501103014800903c0d00f02410780d25103a001402e420604200034008030710100b006d01083c02e0110600100301d0200c00c444400c03a2440744003141c00d042d4808a003142c022400c0040c0d00100e00702013050550004140c0c1c011030001101c0c000d54580d01e1490310011034044079250b0000492001c428800001c020001048203040c881e00301c3c9245989580fa001030304e404540e010380c59940402d0110400023540545141c003000c034101440b8017110400000e18900078140081d2045448644007512a142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205595539 1250 205594289 205594297
    0x90903020309060f031e06010e01030902180108030307030c050a0e010302070309050a06030c081f051207180204180b060d02090f0a0b070209100e07050c19060e0c3003 73
    0x1c0d03c240e48801010305001350b250000c032000522071907180b814217188221140e030a8400d01c4161140c2511130076560044004001000c400c0380c022204010000b41a6801e00c0154001d00c4050000c4d0303940e00e404800281941d54400c80c24082c00310600400a42e19000900070903440c400386001a214101400d00711100449580030580100c486c0002181003941500030610f1200d803900d130b00089860b071182031940071159004591101d1f584070740c244030b24030b0f2507006a44c0c07000c4e807181140c10a82d00c511310b1408001e10031080189007940040c0400c03440030131102d403000b01800e022041011800a00c046613240c440c843e83d820082c1d03070000380070003180d82d800703060300c90780601070558001c042c0c441d44920080e80c40764206034454050100080c11800407003840c5006d03110032444d001302e19100c840c1301341c035150070030904080140110140102501410051030100d103015603800720320740200b484242d00704180c41015601580080312136000002001c0f540002803030341e0b501040c8856140050044c15802 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205596789 1250 205595539 205595557
    0x41d06030102090d030807022a01210204080d110d0e0108060102070e040807110a060c0803040206070f0b0106030c030e0a020f041b0302030f01060e010e0d1713031401090c0909030203 80
    0x3c18926031300515a02c0220144500c065400301c0300801c40303140403503002400c220018101101c0c0e0f190018000c0d40701d000821040801d164542186000d01c000c00f40c2644c00c5904616041d510184003091007a40c46044810481c0501d00030b0121030b05082c1008003000c1801c810300703051082d020081086c42e4401c0099000918100300c4440707031400e00d45860151340d400f4070015102c2072141e140107203e40c500b21240000b120015120801d9290b0f0569542005400042c800d0f80d200c401032103060007040362080c3d440c034801d22034030486c2115810200c2c0a811507040050600800d868000c4030020040009a480340c425012104014030244000014000c0c142d081d111403001000245504995901500a1070080c1e1100700426030341d0303803503120845400c0d4000708801e00294000d90851006d041500a04803d40d0107a841d281c00d0070980492401ca652164441184d50001c0103c2001440240c03540c0603441d0000c00028885000e140d1900300949005028402400303694410303c40c02c140c020402c50b21605 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205598039 1250 205596789 205596799
    0x30c1b0615050103020c10050c1c090506071d0f040f020408030301090e06070e130b0a08161e0e090c0a06030b041506090b090a17070812041d0603010209 67
    0x148261415101412032546201605070001101049a60090081d500c0203c108001401070b0180310f581c11003d04005003650118880400080100450221444071034a01c01e0002007007031f08103807500f2807522800628150803c0304074650891480d4046007010743d050022a40e211408201e44009401040824032400788544005070004070150b001c000355048420a81c000c00844210824880d111003084500000060103501d4005c030b20714080004805002c0c0305000000c900360007102280307081e2410341015445a0080d000844900381c0454184d0150244860b501c4102c03d4040d00074010600c00d008a40616000c080010000c120401c04461102c900070310b9005440d5465a001e0002c0040d00301050086050034004062a00903c01da01c007110032996410340e600d07103032543d500b030309801c1207008680c0080c4501d1700241c1d82400a001d1103840d2140703005040c0c064507003940185400d5004d00d81c000d40500a2100308500c0b0641205415000b80b900561040f650705c070000070f8020322518021039806 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205599289 1250 205598039 205598087
    0xa0501082e090605040201021908030f0c070b010608010f0f0b030601140d050c0901030f0209030705060a050903070b0c0f070303080708040309030f0f050705030307080906090a030c0b0c0607170403030c 88
    0x211200c1d821040c01749000383c00b600d43c0000d26280342042e03506542c02c00b40c55190100b000c6003082922030740080d409044000d900e410100c2c1a650141c28000a030310000010390020014003841040c02c03040801465900f000004241c0380c1220260b0301e000051016040c40b5012041d0310011a151040b1002d501c03465100b0001458103050010071a0418908240040d1402c0328007007109081c1c4c803c49011440040040101c1032905c0100031080d44050100c104200c024010034643e40c80410107400a04a680b10040c0c88880b0004010f20b8022031010ba85290b0b40001c00400200ea08111843c0e00050b242c0742c80f203102e82c2c1714103041d584142140c0c00140700407000b080c40014001c80520603010688a042070f28186680d071000c26a41e40034400c07020308081d0007000304c107640d0b280c0b10000b4141400302819144048c0d580e907e0707511810300c043e40211102200007038903000504081c0000e5a110509040c10b51028908803028039901c41c00820080038540d80302c20090301e042c0035808040341c00081940011103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205600539 1250 205599289 205599293
    0x120c0f0403020a0b030411060a082a0a0309060b04020a0906080604090b0106020a020901090e030d0e07090c0513050105040e01050f01091a0c01052208030718031a0a0501082e09 77
    0x482d51007103c00392a1f040c0348500161281c074020342201c0403228150789000c45070b1900342100c649440c104900c64110400c8140c05d02c000326091010f042e00c5902520002020820740c140041a2003440010500c164030420081d0f01040c2c00c84101d4060f200c491030009400c0d624440820010202d010000c3d1086600400000382c480c0e0004088031010320036030b078001d09666070700341c501d0642d0003074151140c01e40c10502901c445100316038000401d0740c0c203050465140540c0d9190440807a0340700701002002490004402541d142030442d0780c03000300b8003880d01c149000c0ca00303240c8040800d01030190500c00c000880c0494090780c8078552890241c9500c28290401c0e02030b001420000c1d41c05543c2d403c20340c1d42080c00054910501d414201c0e03460704488690218100244d817498250b17480100900d05100100000c40c0c0008240500c40010750321a80082d500310078407500c5094a440014280c2d04c1c420700b0900103002d81c000110b1071346400394000c2c00c40450700380540045a18000300d840d000d01c4240c98201001c01f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205601789 1250 205600539 205600559
    0x3060e0109020a030e0f190303020403020a060804021e0f012105190c03061d090f0d18080a170307020a0204020d140f040803070e0109030228060203120c0f0403020a 72
    0x4120120f60f281000340c3d5161454541c1c0742c40700040d00c00e60700e030451a91001001d20300942c2098051281c5001490306450754002104d81c4607a8016030009200e2808010460901800c0e0b0070700403200e0a8000116428400056910860314041604108152128001d140140100701c1d500d40705405040c8181d00d000d6134981c140e074042400d0707004c403142450440084513010b4411041511003981d004820520445244100008080c110340010311440e42c0a40c081c0c20144a1403c41210079a681c1d4100b80c8501d80d81c101500c4560031410203600049560f2000a50322a000c030400162140059242da4552205900b01058004081d411a0001510a49402265105101c01c0892202e01540c40c0c842c6000a4a080e404940060011000f000070038429030103106844240350052400d080100d44a45c04214843c940001c1403020700110100540022100416200501040c2c402181800c8403c8845002b00001800310305100000142c0c0510030700090040b1001783d90080c00301c111301907586100c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205603039 1250 205601789 205601797
    0xb070c230c011407020112150302030303150a05040c0210110d11091c021503040501110f031017100f020702030d0c06060b0f0a030c030f240803042403060e010902 71
    0x1d80000d00348410f003862501c0c2c02c42502d140d02d4042e1b4590f2903c01810301c00c5001408840404c141001c5404000001664200029071041100341d0a0000035068442071144105441d00014402c030700700032070003a51700c6d40002c0b184800e4070340d11404240c403202d012044d14944210361118035040c3c140030724030a8040c030075002000051020ba412200f540f040440d0702c10031482202c4000d50044000002c42035800e80300d070140d50014000d4000142c0b040b4212543e00d803a40c00034200303950880d004405c0080402d0400050002440c0b200403410703160f106148003075100c480c0940100c2850780d440c460001035204503416076001e00ea026040b600764802615003d0811011110125180e03030030040b02207419041c800a44100083c207801d4076091016040040c0c002c0c22100350070008040e583c2501c40100b11603030098000c2d10b03200016941c400140030102004900146d0880c10160344104020001415203140c1000684030040e0001d45079100120118044d060580c000d0307000e950080004241c42c0d6103a4018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205604289 1250 205603039 205603063
    0x20307030210060f0528030b09061302060919030f1a070518061c050a0501080c030606130b0303040b04090b04050a0905060a020a050c0a051005130b070c23 68
    0x407080141c0100118042d1022400b403100200c0880e44c0412080c204500ca160000381c01c1c0703115040441041803c0012291158003e0341c0e170f041d040c010301411140a1040941210f03200007400740e11210307a004503003284540c41940e030246250943e107840c0002481400e80140da0301086e0319003811000d080640d072071400f00354901d0402c41c000011840a501403c121009010514049103c0001d004100407450308007400c01712040040320441d0f4900c40d028810a440340403c40000601c5504108006203426203034240c1c01d0295200005011903039646a149280040c50b42002003000c00308040401d045000b5607000b02c1d1588008140400e555015800003090040e055a041000395141500704040d500b0700300c8003510503004400480c0010145800409900c0b085040c418a03110341041440d142030400c842c15a059003080c0e070895030215a5004494002d134070740c03075094100312050f00da88032403071805401182400311140f110000c0192542820925160000c5900139250080040300c1d110403650130a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205605539 1250 205604289 205604293
    0x7031e0213361d0a11010305070306170d0909110412020105040b0a030b03060708040317060102032506150506040b180604030308040b01080304182301081b030d0e0105090f030d0203070302 82
    0x243e120040300014445564a400c403440205002c01030005500400002d0401d00801d038031031802191405204801d0840d051301000107103442040610300501c0c9500e26009180f4040c00c0c8560f03500c5400c0340c14103440c107a4860643d030603140c2d111440180c8071481907501403007030040d000c80c1c0d0070a2642c00d039200b000498015001e54445658000c400c948040003250000d0100d215965615841c65003606066840f00042c01240d180c00400183d0030614580340e803d4110445006407510100041d83c00788440340701c8000080c0c202e65003450000f5100740101d00a284c44480c001c101d540780152562900040c0710006414165119140d0030000e1940c442114140c5004074000000900c66200100300c608944500b11030f40100c0020b0300e207420141c0240541c2420702c0e443c1000c40c00d00c2d4030101d00d10b14000d0540d0344c010640201c030880c418821202500c0454844c0c1c100010480c000b94000781c2c426650142464842c3d65606003400240d50754400d180040c0d058880d804000c00c80580005c010402e550198007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205606789 1250 205605539 205605581
    0x4050c03010e2d040606030c1e050301050c0f030703061d010303020d080906060409110301020a020706090f050102030a0c0305160b0a0e0a050703020d140607031e021336 74
    0x404180c038040e03c540c090710783c3c208128140c2240e02c400c1c8515504948503543c0800e040d039480d1514951b02e0303620f030001e201e00000c069004c512280b00180e5113006004c00d070002e101d5840c040a030b0841c41d0041c4141801000000400191258400e91104010701180208551b4035460f518076054002405d0100318007620914049840480c01005824811002500200300c0c80e0740d8001440060200c0000440c0d03100c250101f401b000340d0f03080c006400c0342d40b8690b0060001c50300e02240105000501c2d8030010740aa41c405045c0000c1e64080100e9507091001c1c00c1c42082c6d4516841c0c1255584140d03401000090211031010080040400c00240203d0f0f031544180081c10040c540309480709005000100164001c81c02040141013480849000a0082400d061100b150b155601d05010007298800c002940d03600b518042c0080280751110442f66a4038114101078660091510743c070000c0c011009801081000d0210720704102c0000140740c3c402c80c65203d100001d9000d14005018091070070b81607410252 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205608039 1250 205606789 205606801
    0x50d0c020c120c0d140f030d020a02060601110a0303050c0910171b070f081c06050306100b03150303040f030c05120c030318040b0d05030702030106090b0a06050c0c04050c03010e 78
    0x16040c02e403600004c01d50341132206542e4441800c1c0c881c214419041e80030b4049200382155092018010341180804c001da0f941c40400700007410010010840703810b01c00e02ea907016440c014005000d09841e50305050005071501d41016001d40b174040e031450141d201c40c403e4002c00b00c07a1f510003500c0c50b81981c1801d04d01c003151503c0e0b9a2204070f20002c29401407880c03041c0000c0c00171400c10211480035500a112441c82e004000a145604d000841d4451424544420080045047c20001c0720785c41140c0301d40401800b030400c2c281080310b100c06407044800300724180040c02c0c242d0303050080790000d212071034801040aa5a180c044480b40d8603200361403056442c28064540c0b210702241d00c00381c81c0401000366181c5110b484c6111040040f50091940040e034842c01c048040d20340001c0120b4850040000319220071b000e02c109070940c0c92a803c00800c0c181400c1d6490702396110007845109807501401c2058079a0001442c10f80741c107100b000e40c141e22071b09200601c0300c0e800526000b0340c103940c4c0c04281040259148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205609289 1250 205608039 205608043
    0x2030d06061d0112090b1003140102071a0615180102060a0209030303070507060207050a0f1e050c060a02010f05010b13060e0102120903100e03180a030b0105010f050d0c020c12 77
    0x4902001e1240d11010b042e403040d0711a0035000c10048020754005003800041e10380340c040c510211805071650315890024428009060a00006100c0c402d00a52034002da03039a444d0140b030ba4280e802ca0070060300c0d5012481c0703030b560b0a480c0c03034200044045090b125402001d13000f000b4202090000d0141c0200400b01f87d00261070f00803110110790140046140d41c5816a048074a5482544d0544000d035080c0071726030000d90103012030b640d014040c40300070a001d201400e0603802c1c200100c8094035140d4a895070311001a001081500310200b08940313141c1c58000d80c030801d07405400d001c0340701d0032200d00d00800464561900e00c0a00018901d240c00300d0308581d112082507030b0742503030301c408540542e0011a031003481740c500b000100f4081101405881282c14008130440a917800b03c1e101300c0291304085094005180e08005949401f441140e1000c01d03070340b941e00c4100c1207100c1800780604002c44419030450140c011400c0303174010003120404019104034090003d4031503946146161181c021150420210300d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205610539 1250 205609289 205609307
    0x1903020604030b0903040306020a0306060f0503090604020616060207060c0908030715050402011e09051201060e0105210d020705010f030b03100e071d010f060903031b051c02030d0606 80
    0x20252900745082d055448000d5400b000624402041c0f00400010000600070f0019102400c401e440200e10301c1c2c02c049021300380e902058056010044140b0400020401c000b90f01f82e040b6030147c8030603585d014205010801416880c5018103842e000280b40010031105030301041c045511a03561340c030702684134960b00e0748903c1810f41c05040e910f41442c452180c0c0c40e450b0300403600503105040c444401045440d041494110403078043c808100311032010030903801d2035425903103680c400718020080a41031030242c40702000c060082c140100e100384000448800c0440c83d45500d140400b003112415042108000d540b00854000c00340002c04107010f00c0b000b01e0080c0600482020020080c1c007803003401803581001440e152041440e50712480100084480d0005d181e0001d4400c00c024003200c0398102000c6000c00d0009601500804c250030b403003000881d52248032040048400f55803e43c20584e0341c140705191803810b40ba0a83c220400c8000c0f050703d15000002001d001b0280307102801f5450340c82c0011b584580f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205611789 1250 205610539 205610543
    0x5060a0801210f0b090c0303040b070f02060705010905101103010f152a1e0803010614040e0c12070315090e010e1015080a0312021602030f06061903 65
    0x414000103104000203900d1182c21111441034102609500d82c45504100320030460940707088060606020000c0000d100c042c007106c000703800a500d007602e0b204226149100310580500f12034002c0000004564802040303c5d11240c0000c0240940e0720141007142e2100500c080c00d00c8524580f40c50789443d42502c0094070304a844142c6050030503032030030030038038503005405111100f00407400600700b00c0710414414107d01940320442d0044200103514001307904085c80c80401500348daa00030a440000d800c941140d042d14018a0200a00001d03480c641100d40113640000741ca603030100040000701011035000d054110440403040f040ca803034804050f021580c00341d010103402c49035110b060103480c800b5040071101d03000b500000200032034007402072414041040c5015042c80d448a141c00c100c0350300c581440018000c054060a499026643c020f00104000c0000c0c026807a0046449200d0b142810380f42d520040c0c000e030640d244540b8000005858110449809105144e0301040302c2005004d42881400d480e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205613039 1250 205611789 205611797
    0x9010608060618030a0501050108010606140403051902010507120302130b1207050903030c06090309030f0304151b05030711040c03110906131a1201050103020702030c1003020d06030503040504050105060a 89
    0x440310f09050300203120a0280c1d660944620f00420000804c02d115650013000c1400000a203182000f42c01010586d00880030004102c06110601c0890303404900c000e480100b04c456070b80d018602d0701c0161058003462601500c1440135040408243c1d806030020310f5085003003201380c6940c94132980b0044090007003c003c1d080720707214940069140750183c00101009480102180d090800d104405413605a040b035091120303800100300382556083c200499440442814055410641014107404110380014045070401580b814140340c072880034103200302c241c3c1d00101601d548042500782254103c1d0380c050b11601940c80c01c96407803a050710900c11001d07014000e0b4521032605803440100041604004207103001d070080b0050000b0b50703014100380c6501d80745400c0c0e1482e8446044868a6003184416071207141270600401001d00141e41c041070030b0f6411035040b40d1101001840003012030090044c03140030100689040004030502078000090030071180100c4050080c0d82c0c1310801d101e06030143d41c00000100d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205614289 1250 205613039 205613047
    0xc020a060510150201090b070314070f0c0c150f02060115261303020c01030908160309051207030501230c0a030b0607080d150305030315040204050d11090106080606 72
    0x24095070801c5030002c1d401e21002e1074950300d0b08141d10188007808440701c0580e540b0b0402001300041c01e00e80c541c0c003280c2c609040207401500000305200034002440001008005208241d166009a0344440456049007100080a031902d1203c1c501022840304100458080401c62407054170000b1402e061301d458002100303038000359010503210702c200c25890341c11160054031001e84000a0101c1584240070500c1034070000304a42c1006410144214180d50415007040300b0180450361610440e0300ca03c412181c0e0550900580c00c0480f079100c1a90092917000000c5207502840810008000c400d90780180000c001d50b6014104044500c82c101480b403000e25101c40014806400c240090080440c082c107000c1b896500020000d04a130b44503030401c50b01d002e40814400007001c418404c040300e034140801c5000010b070440e110680d480c00018682e5106d092503014115040d107594040d20300030b12014140c001126154600304d1981c2016202440c080d030f10b11000059024401c3c03524901600015200d1894 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205615539 1250 205614289 205614293
    0x5010227040e10020903070b03040503031015020c010c02030f070b0c010f1b0c0318030c09050705031311120a080d0b030318131811040b0402071a13080406020601060e040c020a 77
    0x13035040000615858041e0340c40c00580712074013000540c13250b40304001455480c94821607010310a00076030410000c000070710f000d0060702a00021940b440b11005d0800c4000c2c00007610010b80340206044d501101c600401e140010101c0d044000b03022503284400007805505580d00203401100c00b60074041540600521980100c140031f01c203d08a103a0003882d001c80100031480d0881682d0003140d0007110b01300e00c1c03140e003004161003c0c815107800c0f02d400e01c0c00c145107092044010043c8414550081e00350001c41d20203448680e82c2d11044910030b480d002c241c0c1c862008a050130002a085251031411050925600c80c201c3c1c5404021030302e06000ba101811048500003081c48920942d0413004c52a5585d10500c00030402c001c448020b01f51840703518400601405c41041c48103803003802c000640583c0c014090140040d6400100196088a9200d000710a40d071314104401d505008003405041250700040c0896040d6002c6030b51410b0794141c2d10b41001d280280b50a2004903410780740940e0040e0411310200340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205616789 1250 205615539 205615541
    0x3b0c06030a020c0601080604031b080a030e030c0717010b040506010c1b050402030406020a031401260712050703030201150515030a0e0f010e011a0a050d03050705010227040e10 77
    0x904407a05000050400a1a02100e8600b2030203030007110559124008200c1010303488019250019075402d020b0104d0035040d680d6106500566201409140d02c44400580000003001550074210441d011550603a0307039880d50070b0b045080700c50124860750902981411504040c06100d00035901a034880d03a0640558a40c401c0e203804642d811005a4460480050700340d441d4009940907a006000040e500c1c010b03028085d040341d804081c022019925000100700700040c0710820811207481c000c0340001108408561070505141c0e8120715241c2d40810440d1092103030000d0b10b841500c1c401e4008001022000c14046243d00107403042562040002c890b80300e07101e0f2050091604058641e00109240c0d103149150b50421104104030400c40e9500c10200100c20024058081401c905145202c1c1d003030103c10204191617028000c050051804000302d43c1018800d504440740030780c22400031921543e41c4070201c6080d032028100c84000041c2c40d0a0b5203242e00c7c243c032445591500c00002400703001d248540c240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205618039 1250 205616789 205616791
    0x70209010e0c0705012c0c030304150314010f05090c0c060402010e040b090f100e16050a0c0b01030605060f0316050906210106050a080f120d0b043b0c0603 68
    0x40650b0800740482000a0307000d004461000140b51412003040000340c401042d0468460040140356020054401171920080700319800e503621119103c1d483e034101c00d015805000c8800080840001400001a051848181041c1503c07001c40e80c489480c3c4a43c0c01a00705401000c0600c078654004001040043d8010200304007403400180010414490440c005014a0030403180402c10152080400c422800605200fa028020b030140c03a050605240c005060358684000e91003083c4040000c5501010f40200103031900181e001118034030319030310fa24022002d01400d45582e03001e4110842115003501d008120302804402d5629042c40c030602d0310080004100c009410250040d08550315180a03400c0c02e646815072010f000c00114405141809000550755990300007041904140021096400c0108000341407502424000e5154600b14103d88020088581d00725485440d243e002100c200d894039441da80810035440c040c1d9911690300e0185800540c1c40000f400c03a422000c07a0303441038070f46038003d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205619289 1250 205618039 205618051
    0x605060304170d0e030a120c2109060617010b030706170f0411060f07051c0f05031f090b0103060e1003031b05010e070e06030a15021606060605071502070209010e 71
    0x1058841c04070801c1030039544200201c6000a030b410314801a50117090180123010703e014503004100d030407860590019400c045088213900354071108007209001061308074501900c0070304000d80c81c484007440d00342e00a0480b800702e40d0080c080d00c003000840d5030042d020500801442811a22a507980101c41f40480e80014422200160207032100103041d00ca0f00081e00c103170648000d410b03559400754140f1910f05180d102c4c8001000e900403800c42d40556000c0c0440703030600e5460811540705d80b80c0200c8500e105104584403140031800007070008010142c1e0700440c5190600780ca0801000303440b001841d000560032070b0b807001d128038003500800000b80301e502020380186502c1c4422040d11251741d505800c1d194144845d12003940952004d10844008072010741d00007000314002c20800e00d41da070b54032280040315400905013a0b400304884401d07a000c00300301245103038000c008012903900e4001c09882904100001c0e80c5201011900e1140340c01c080c800c54484907001816002ca90380707884034904885c4402045c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205620539 1250 205619289 205619291
    0x105060a140307120f0605010e01180806161806020c0112020706020c0a0b070206090703060c1101090c0824060409080d0906061d1b1e030f060102010605060304170d 72
    0x25a04074030707180020b50b019450320b07a984403182c041c0390401000e5400c0a50401003203440e03c1002c000983c1c000c007900000120a09215960004880fa490603134140c40d0701070322490142070208450041c121800441404880d1141d06010280c1924506030034014001d00c409640402a0030f0107030340c007681308480a55962440503213850400e980d200c3c01c0e030708406c82c00801c50307001100c21803c020982c000b00350b00100d14402800c452400d5003205580c0d1006200250109981b00d01401a00e03208030440703428194640024804800c0910f00030300f214074a0310a100c8a8041d003142507000000703400b100480011001007480071f540300e450800006000070700007142e996004200e95103114141e40500038146004100000350580b50400c142035010071003483c0034160a00300200040c1004c020035030350389004144d908680300d0320102540030702d060a040a03841d40b15804410810110f01001089100d100d0070b90003403041a680300e052040501003990008c00b034401c014042c00c100308031140500b003030b4031f103441c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205621789 1250 205620539 205620557
    0x7021819050903040f0f090501061704061805031215030d050d0e0c0a0602070503070902030405060f06040216050f0d08100b30180c1507020d0c12030201061a030105060a 74
    0xd0880c0c076018070b0350116800011b02d1100700441201c91050074010700950031306c4c102840381c030f490741d6940c0075005200134031450341c4005c0c0704400c0c050896009451544201101d03a20b00c1140c01d16801603004446072005180c03090304042c400d0801043c6c560071101e940c7c075241c2c14800d81c000340070f016000403200e491301489020008100740d60391001a0000b0101d03a00a0710410307003054141414182c40d50003c00e00140104144070004000164031680b00403c078001c2e0b00301d51140400180a40f16944280751551a2080700505005000ca2000e00341c408c40d604072210704042c000c3c260340b502e6040b40e48070401030215804201064010009101000c203240503030012080302d14054a02480184440d2903040e01501040b01170483ca5102b48401902c01004001c40f058203070015101c00d14482e40346201d064003282c0f05e000c5488a504148103a0703400f50420f01d101d80c85e20b84d07401d001c640d0b030501600158200740000440c1c4120009031100403d501e5082071441c2e080400340700c1d00d075110254590170441110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205623039 1250 205621789 205621799
    0x6040b030a033617010c0c110d0b010b131401091e09060b1909031101030b150f0c1501030f0209090a05100605030c040e060601030e0f060106050702181905090304 71
    0x281003254102c0540c103951403404e21307408118003000c452113600607030b1405910002e8503401407042e05815500504244043c00d020011411030000c03a0001003001000a0000c2004070242d000350002207981551060307016620702c2c4444201d8940045d46002c6540303450140001d040c0ca101090595504460400681e40da503d41442190400c1e0304ca21400d40001c0b86d8041021400c2142c40c01c8030f10325103403d0314101d066441c0d400c070414200c680b050506645c2c900040080c2c5400ba10094409809810036854501d248003081065015240000050003464060038480c4900c130b8007203068a42010000401424660030301a07840e80c00f40c006c81c0305114008003280050000c000c11780d48040790000c0886c08a140801303240c40e0803200c0341954032403800c01400c0680c01c5000200643d01400c24a008100014945005410002080145042402100004640540c002004010840c42501c800250750b010032045507422409a075813119410420a044680300480d1304000e801040c0641a01d00e40341e0f0791 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205624289 1250 205623039 205623107
    0x1207020607260a030c0c0b1609030f0812060a08031e0c030c150c072105121f0e0c120402280518061c0813090f0506040b030a03 56
    0xe45002c00c40100006001100f082d414011a0290003c03800c04490540e0541d48a2880510041c00d40d894503549007040c4448620802c0442c0c000e50300328207000d2661311141424001544810040d001c00380301000071a6aa0505580200449202a01450404000d001c0d0304002e0426401c0d20b9985201c2408108040340040c0300419650024000a1905024501e5100c4000c00020900c5c1c69109050010b0700100750101111548590403401e60b001d80c0d5420031098429004520145910410450800200c148441d540720b2080480445e803202e401d43d2003103200b801d03041c125103100c4120b10a01c07076050343e2800f5004441d000703440103000d0412440a603180c0314180350045003052003554000c00412490405603840000492140c0d5000020318080c8042080d5425411000104600c8913030258180419403043d10603800590405564099403034031941e02510300748114400c0d02c0d00d4035001c035640e4941403065064100780500600101d90060320203440a051125090800800c441c003040e020340c00e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205625539 1250 205624289 205624343
    0x3040603090c170606030105160f0c0804092f041d071e1d0a060212030709080601060e040c080f0c090a080607030510120c03080a1707050d0e1207020607 67
    0x3c50020310682c5030030030030542518000784c00100760b00401100104a541c0c801c0345146103083c00d00300716980301d030149045c62003403084d540010f44442c5810045030210109021554200c00311401980b90000b040c1c00c01405441188034030704203e201404000c0c6551030308074621390700c81883c1c00e02e48088824120311510036414950300d100002c020b0701194100c40d1024040c07280c0010b00b600c1b217041071400e211001e1341d54400d4a10068642e000840010440c0c0e100f00094000761151209440d4907595a00000e0400700d40205628416800c0c10304005010340b043c01000d2158101621440352525280c000300070650066804903007140d44110045441107003040594028401d50754006060326103540c0f40c190441c040d40001c0c00000b4003012500101e4042c4045509481d00034905965600c140c050980d034203a444526143c0f000400410448030940013030240140c4004403100f07000529108040740c0e252656081d9881c0c884c0818030041c1d000d81410700143c054948100c00842350044414240b90440d84 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205626789 1250 205625539 205625579
    0x4020a060e133305030d0e090a0504050316060911031507120905060c090f150d020f04120f0506010b09011b0317010f05131404020d05120f0301090e0f03040603090c 72
    0x411460104514181080043c0c41c1b09000d180903040920707034100103142048042c20019100742c4036408203060003424004c80740104c01c0328541440d0407019103400e001501d54081c0c140c0c0c1a11110301c0759007660030080f5018080d90461a60f0f14420384c0c1d000029102e0004013031480304841c2d83c1d0b00b010000030394108405c1e0300031002d1091050f1200222000c0144c10201c001032a0701804511103a031a14082b14416146025803146025072a8070f8518040c4840303005a510030740012409017050b10921000c004100411809141600d015a0703c810b52101c2c0c510035405510b002034002592520361410f01a0b01003956440303071905603880b0140e8082e90998180a8005402207482850308029a10b0440160981c180e0000310a00c51041e08a04020118400900207406441c3d100151002c003c0e0a011a408011b8082c840310b4464070a40c61000d070350b403c00d004008500f8601902594030070000920b509581c90360100452409041c81d1084010380100c0c0710071114002004000b00c0d65114450396141c03100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205628039 1250 205626789 205626881
    0xc09181023150a021f0902040c03020307030b0910060507060908040e100509040215031b2101050411270603070507060506040b011b020d02060a050304020a060e13 71
    0x1c021001c10600c2e07061011460201442000710f003143ca500403422007000e2a8201a032910f0a22820f50358002d40700c0007200070360042c54034500001c0f841d0107034065402401940d8081095640e81420300c140b00c4c5c01611a141c0108040404005ca54418001070130918403504d00416018070942d1400415009504840301a031801b40800a81ca43d816158400034901202e60001506158000c5080c0c044982a501403030400040004c0610050700040080c212040b04a03d69960309601c402110224032400c8510000460000203518034040c010b00308440c2c000c5070903502c0c1c1a07081c2110b1940c6a074404000050441812120036907907110800b0f1071158030305899441d0340c2c2c4040d10341801121402050300d8031480c9071030060a40c0e07907486900005182d1100103c107058248600024414480420000b54800f600140030003805034024003842c029803003070b18010031058450809554100900080d160420799405060b0072410040e0012640d21015503c81841c10340c00301c0d581d01c00c407840c51103d18900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205629289 1250 205628039 205628099
    0x1203090d0c051314060105030403110601031112030c120c07030b040f06240b0d090b0a2f030c070212030a080103051020030406060e0f07080c091810 65
    0x2d030820040c5840d00c2d5016280c03c11904000548a04118501800f42c0d0304200010002401701405100070490684103101110780b0356942c0d203407000150541c4403005005000d01d130041091413400000f0341343d074031802e0000791520401d501028110f98014102c40001489901d50002c0800c104040b9140510300958040e640e03514281041415030342c001c5c124004c910300d0758482c0c8042510501840c000d9400c2e045c0469030710091111120081c16001c1c034090200420301040c400d070071000b50f1040003480307030600410307420304001c0c101c6801640301d445401e10080401c10014003082c56170001007a10341d00c024004450403808265141c519000480100040b4402d00014028272604100074940d020b4a14410300407800507002c04030078612021101c000c000404004501044400d80018010740202000c07001035181450303206001b00010745240001c180e507035003c149038040c0403084408190000d00005a003824904c4406007003180113083c02401c2c001c001001c0b9101c0d1408002c1c0107076140c581060849 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205630539 1250 205629289 205629299
    0x30207120f021b1f051b0102130b030106270b0a12140903070605090f0a0309090b0108060607080a03140a090201030608030c060103030503070203070618051b09061203090d0c 76
    0x14100c050820106111000280402e05582d82c0c0075080209000c00040c43d6480703480b913400e031080d0040140341030708800c1e04442c2c110507510550140c043c0c03040303101c10301e0103069131503076107041d40c0c0710030300410780050030900c43c0e1020b40e549044074148101c0308288441c01c56943c0c00102c540c940020400100150141e41c0014499440e0b02440ba10880c054403001c00318201600710503507030b100c0c000000f0401919403000072042e010900c440700200405805035010721159180c014401c02c3d041c040d0091151412031007598a52007a412148207800c007a004e50f141001c0c948130f01c0c003a81c108201ca00101a22443c1d003041c100f00f00703020035005036108039010500c3c0c14940f00142c140ea0040d041120140d20611065860f540c0014005046030740600304a40d60b5107038000300702c0c114820884098980c600f4245d2030710480031b1120840742c409000304151030121402c003442d00c8048903442c40881c2e00103000000325400b0314100c1ca480d850506410b084030300e40070101c404036029145608090f20754180d1a0801c002c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205631789 1250 205630539 205630543
    0x306060f0915030718080d0c021201061205060c090a030602180a061214040215130f03080301091109150a0504030b010305010f0e060c041509050303130906050402040e010e0403030207120f02 83
    0x2000c10074501088045c03d007840306555480c080c3c00400303810490340b00d41c0032040d034580d01ca0000441c9003e00091180903202c010119101c1d07503084044603244034010001d01d003411094240ca05a0b88000c00030300040b495911510041e40000c10440003c400640c464001699120643c10080c80603417100f1107643d4080c031a110842d0924901c40000609950400c0016030301c90581200340480c426640d0389130b501c1c01c0d1028441002c0e81e00714524082203403d0110a02c05900c0140d4100da011140030311102c0c0d44080c140c03103d402030366400e54104000c480d401c0081c00504c005010040e007a482c2590610359203865070412208281c0c0300b603d0595480d80d51100d5100c2034002d181000c80c581006043c141002c420540c6a40f155200e000317107102c11030031240308903442070002030700400000703003260703200e00c201c4000f8200725180b8403030401e09902e4068001820705160003900c0445020001d031707030f10726841c0200724091080000c1c4200c04060342044440001201c00c100e10420005030b5a40803402c80c03810101034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205633039 1250 205631789 205631807
    0x60e06281e020a1103010c0905090a020421050105130308040f08221a0a0c11130507030203060f120a1b08150115170601030903030f0204140f0d080306060f09150307 72
    0x74080d0341444403400c03040f41c018909004a850654ac2211995190220b00d4020300030307a0411250041d50f1400c4001c00d0b007000c80c140135100d008800030081910f610700220b402018000d001030118120100040c0800c1c2c0d40108000c2d2640500c00d19031401d00b4410302c2c20321380f003500750900760000c140e480244441c3c20070509031002106402c000d1480d018001c2006030040c01140e0000b0711014040c1e141508945400041c03c2c0e120709814010700180c02c14290250107908200d075568000e000600c50002c481c64a5803404c15080c1c003031006405100e6060325000d50b4200400f07040305000d02e03100000611600100a040c001c001000da80b00f0055040c20700f0000541a2041da55040007607603400c441103d80c2c542e0310703540c1000d024200019003501a18080d00030300b100352401d40549101250004003000002d0481d052800201c1c1c0d11540300c801902002840da01d04038010b80914010310028005042201c010590225410340840c10003082130005550b03030f100e21a09160320749010003881186900403c02d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205634289 1250 205633039 205633073
    0x60f06121401170a020607060b030606011d01110c09010801091401050c04090207110a0905151e010804080c0115050f030d0e060306040f050405030301060e06281e020a 73
    0x5111000d9041a40050194103014008506403c002c02880c44007042140b40c816560250036252a01d910b8140354000301b851240090190050000054956120300c05c0030024401800c50101600406001182c0703a240c0050b100c0e0040c4960951404150345000c00980203100348800401e00310604c0c6881e900d00c002d9200000084e070304100a20480803200c005990560f05a510f0040e19504c0768109001c0d40d60751008110381000d24541c011a9001c80358004903c60b00b90910380d182800c1e143c02c103000651b200c0300c24010746402c00d822003224940c462201c0c0c0760014041d611075400c00041000e2182141c01d18001680c641c0d844140811a40c28076a06550510204070f0290500b03100c0c80d8800340110070840e8515204600000000da500da845034803a2641c400812000c00251030b00c0d14100740d0301c1c1e0080c090316002c80c85c00c2e5411225031420070200c4040245d020310584100540e405445080204100844140702e4009001000718182071807000804d009513004105805007401d08a005503082600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205635539 1250 205634289 205634291
    0x1203011e060c050706050f09060705010e010e07050f21030c01050a180203032d0c030702310f0209090412120e031b0a0506130309050603041104020a12060f0612 70
    0x40c100210f10081241d0084030414108143c0d646000c0e07400c60641d100c0c005101f6800940450750006105055003e0030280d19140020080503581100136070340c0e2000c41c46a60b80c080300b0031114042c03504204000b004122554030071a4901003817202d521b400d41e0001c801c0300110380c2d0744030708011135032101e0300802c0c888405e131594134603800d02c2a0300442d4591042c1105002031801c10840e18594480000540b489546850b42c800d0310307205d0072600c5588980c80f511003a8420780140310b2808542000c150a48111584400c10042d801d5502c081840902440c643c41114694248214052074645801403407007980f142c422151940e40c586d401601980416030580f4951b850f02440014910000040707a007080c5005222000040840c1c0c00185000c02440c00200540035000900c03403280c2c3c0c8203100e500c02d28480c0c0c41d500034a54541040c001c06002c103c50182140106154031080c0341080e0740201240440c0703140c2000344240b51112501510081d03800700346c201681d42c0d010010654040d80981b5401c0c29184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205636789 1250 205635539 205635557
    0x19110f0a111b0f0907140406090602010e0d0e13061d04031101050f151201090b1b09030d0503040213110c010b040207020d080a020a0515060f0f0904060e1203011e06 72
    0x3003102c2502648005014090804c00304500c940181e409140381305050405964a5448541c0100900f0740e9104010256003880c4981003810004210748550f89200d0351040e0b189180142007040702601448d903441a5507441c003012410701c0602820a07003c2c1c0104043c1c00b032508003894003d001146103864451140d14000910100c03494800a1641144015031070510194000340000c41516041c0800b844135071030301070410100142c0c0e0240e2481800f40c54107400c80d5801042c0c0d000100d10036000c04550541108030504415030083d4007035034019001a203403260400c1d860001c0400c4075442011b4880580010540c0c40c1d0401c001d004862403040191410341c103100140d4041804520100801015070502080001c00e00303108000000c0005c0e004005c0b2003802c803a80311110040c00b000d4801e00d0080101d9410b52803030341800c400640514101034050075244d03646456480080c24800317001d08280c00380b44014950905114003039030280c603090341c40c0c45e81310501d6468245050704690101d428071031100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205638039 1250 205636789 205636843
    0x5011e020a0804060b150c01090606061704060510120b0405010c0507080702090a1506110606151603091d010509090a0503180301060e040809030d020619110f0a11 71
    0x61070150f089903224002007085a5a4400291a24090400c01d4954200400c030401041e80541040c5015401080100002501d8a4040300d940d000c5c001c0c11040c110401d8046070000d1b503141c0c0300f60f03804a6105500d40010b44c540c2078000038084807500a9810310017420601090203000c0c410710000d000d281c02c045240c001c282d5501c10040c0600c8102030710501f46213000506600762a080300050109400d07008480d9a200c16000d0320b4590025091022071140000142c41400d04910441c1c0c280c801000441c1030014500994096105041b0100c04001135440005641c0701360650468045005e85070b094210340c1004180240d820008150702d0345a80300b011a00045813002c0101ca10210407003400b2110301d5444000300c1d01426090b8848400c0302c0c4488108030034015401c0c05413485070011005d407042d04c4030000040ba951801902d082001d0141210641c10020440d80500300341030f507084010303040424449101d1410303000600713408041181140c1c40e4507401c40031303c041e08254400035565103d2410403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205639289 1250 205638039 205638047
    0xb090609100b010f110c06070c030c12031e09050402040b090103050c0f0f070f0206070b040b060a05032e05070302090a09050f0708090109020306070e010f03061d0414060405011e020a 80
    0x1408440e405d0104142801c3c1c8250410301c0f02015000c400f804d80f6660b00c01d28900711001031450701c01035074500050350700480d5403010021294840c9806d0758034884c4c4008484450714417113541e2603451060041e414000921034440703001900090403105695510354145030005030590700010071075a00201d04000080075030302e0100507545da907026000c2452b1280c5031403030326100076044284060340c400004074040e802c01c120112070398412803040d200c214031a01c4400c10b0120f030000c2805200d5140c0c2100d245180e41c000d056154002900801c002004180c40070350416044035010344130000000d400040310f10482c10801100001450301236802c00003460b00042a0013040b8018060300c1c2080b5840001c0f0b100118250410910a5001016110340d41000310000d0140300f03001080f24042640c06020004460084c482c500c00c0301e103c41e01a10746c2c000c0b0080082607100000f071088401031945413004440ba001008000d00c9940302c2d00002444c050000c1030038000c18422856031410741d0041113405151544 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 205640539 1250 205639289 205639307
    0x70b0c07090209011404080a0c14151804090609020102150415050c07080a020a03030f090b04020405060307080f060601171612021e03010e0a060b190c0b090609100b01 73
    0x107540070050b1a0006500102c1d520800991174056060000c10046402c40c008111310b8483c5104150321001141d5402501e020400c009050583c490701a81100c04440810001003039001c4443d01c6500c4140c002d04000380803200008401e6411503030782c41010045580421400b140303040c40030052031a40c5080c1c0d0321010041000c6000d80ca99507141d0010030304800445094400e00d643c4900969150b452003180250344051003c0b0980000303090051741002c00e48644034847c0e5143d0884481c401a50340c5409000190a005c1d007215013603c106480000e110400344000001241c40303002402950a280d00010700500b4030011080548080310184a0005c5c4034400c2107001c0562070400d96038120392008030b00000d004928040548d01215101c8441c8110103400941c1600c0715102c00071040d440320794854040300e410340983c0d804681c1c00c01214401d49014040706108076014a0b00140c0d0039131680d1500602101a280f0380f00c5640440140300b2206024048032142d41c010520400a04240c440002e1005e00d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 205641789 1250 205640539 205640549
    0xf010201140a0c021e0c10030e0a02010c170c07030605060915091015050a170f040201140405100314090f030406050c03120106090303020d0212040905060d05010518070b0c07 76
    0x1c0c3d0307948000c40c4070f4000c0c031240700070100007489502c0040e9806141900c9107003801c0c0c49481140100140c03c00a4013a21402814216420050000e030010303a0055440c0c0d08091400d0b07510724040c200e404040c4003010001c0c08018080c030064030400b4a14a0408141c4101802441c424124003003000024003000b0b8a4903140345023101c143d403440c2c8501e0b80004092150340c0156050403c210401c26a540e000310040500407019075610440010080181010a070151900d01c65902c20401050156100d030b026116a030010803881803809549500003110f0040d213800500129444604151141d100a4035859020514a0181c96010300d1460a15241d2050303000d000d060202c04185100d90304e10803c107940300d2043c05c25000e4840c3d40c50303403805000c04a16101c00c81c0140305905c01c20740300c1ba20124600c0307240038180d10080d041c0303030030200c100015180040031190007056000468020038002d004d803034000c41caa00d00010389880b40c0f01c0442d080280540088841f814100310800130500001810000c5070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 205643039 1250 205641789 205641791
    0x531090f081c14010512010608030a0807051c0f0f0c020c060c01060305120c060c0a050423061b0f010903270b0706061d0c09090919110f010201140a 65
    0xd5158040b00b6455840602505260328169044038000501000c03981607030400c846150b00620b1aa9a581c26070fa82c6015030340b0a50000e004500c130580c002e21070190041c050342000d5080180300011407114448600600d0400307a159040021114100c0c8511004007000803030034040450b404802a6aa991100f00b80f4041c1c00300080c20041100c081d40580007465005084c1c411007560035088081c0e83d0849035400489000301e00201c2d0458003841308546010450307844040c202031a201c1d48818a0f0303043d00704940c2070106280001000da842100400003c021024041d8210001c2d40f07040d0702e080311421554a1aa1411102e0000b19400c8400c12040c4401d00404d04910a13640d41006003080b220351005036443c201041c0f08080041a03000314040c0e4a803607080300179840403076a0030300c20f0384001c0c1e5141e03039001d03000c1203041d413030303003400425281e108480e0412220480b0024212050503800d00704240d4020000c04217030f054a1800d50401075044000b48000c3c03000b146114402e14880001a044868071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 205644289 1250 205643039 205643047
    0x90605180f0f0301020d0b10090609060507060f110309010c020706090e0c090d0b090114071b0c0f06030903020708030703200a02130b0103150b04060e06040531090f08 73
    0x40c0d42c9401e0340161052000d03000b55141d101c2e454054015200c42c400b10b900c07030718880e500d40102a100f10343c070204a86441da613070f08140d4548a010303140780c0d021131000d4404940b2002c140c1400e0fa12350041300d408501c1106515130724508520ac0b6400c584881d50074608542120600f005038592000003203055a00001107042d0355112040304010911901000ca5007210007540094103102c000b0350018030800b40c08000307202c0d000e04401d8500d00041c0440b150408210785445569178452101c90710015140300f4240c0103084c46d26040c40c050411025401000000c1e11040d01d081019030503c4540020044200110b05081050703801070301e00c2a5994041c000041c2e4103460b54040c01e002c202d840c0181c1d030003401036520440c2180e0040e010b0490700400303601003030800b03185807907440c0c101d01404129188041030354105810070300112018442d04814070707072024040c040403405503a01c000e00c9203078903140302e000c82903c40020881d1080e42002a8001c24075440e05805202040c110f001c491031060780301045030f0762 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 205645539 1250 205644289 205644319
    0x402120417090d1124032205010c05040e010e07050d0903121a0a170607140f220605070f0605101d040b1803040308090a0b130639050a02060307020d09060518 69
    0x803508007d0780a003003907080070746c110700007508a002401034650120000085a896400d80081441c00740e03201030014001300240140c07c20580e228900e007030b00ca0301d0f1100700b90800c5210441611055a590364a010861a0000b02c0d407609144a030b0044c10761040440c00620140da60341d8485900034851000c0c00b0030311200119a0b88c0000803242800d42c034008a68039030310510303161410003000b030380340c101d80100c40900030400902420954a91a43c00020020501866619200580005410403482a14000c00854400011900120b480380c2d01c0c08540717064641401c004030b001d040a00913100078034203000030348044c48000c400c540507250000c807016030301c4038035202145003071020350701044c001ca0000c1410101d589000071042c2c2101e0b0b069582401d2919904030711074203440c03900401c0c0070040c0042000e8220740d05880d510310070140510103403160b0640e183c0110f2036643c012500354006030061600701113510303000034084000c0c3c4400d24206007042c20100589803108126942644145505442c46507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 205646789 1250 205645539 205645591
    0xd020a02010c0b131515060306030b150604090f05040203070905130f0305040e09210306010c2003010c02160f0e150d05070902090f0402120417090d112403 68
    0x1e00a0361000348241c1045c2c0d6448450001c1c400100d51548840d101e8000140e00780c444d00a080640360000704400710b80e240d0415034802c0d00118281d40d508803009201c00074001d00648580403000c1517865022030b452034180f04050a02c400c5800415900340b402050100403108031203910740d0340303522503000216164a401d00b9280d901980c0d000007000511882041101300c00461006200c0c9245090b42020082e419001449030104442c807600040c201c4002e80c000c0303034a800c40040042c1450a40300c600c494048003003030075a501d8110f6000542d000880c01c9201c01d41c40c4880d10014110404601702c00d034104548660020300140840c022003c00b89012021641c0d64641912015404001c0f9408035546220784030107034200882d80c900c11a1a41e0030342c14541000d0088031116022406481501d41e20740e501c14030742d016030900d48641500c080c88858511b4691048245c1d24038000d60340d00c050511000308002c03500214062105003d8500e00201c1c410303201100940340c01103441d290f2820030740780241001e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 205648039 1250 205646789 205646821
    0x1b030309050a030e0111060702030d020d0902040903090f0909170a0e0904030801080d0c0210030c1803050610050f10270e0a0b010c0312110705010515030d020a02010c0b 74
    0x19019005800c80b00c010507802a240442c900c0e401c0e00c1d5500158600b07004140c807058100c4402c40540c008000940c01e5441540c010020117008510000c2d4106803034001c07a04a503d00c10084022500c0340000703014404180406800400105005018466003591840402e41c070580075602d1008001c40d030710300b8503801110031784150000a4500720b228901420001c0900e10280701c0d000742030140e0100e0414440c80f80380511080345d006420000004e0307500604500400300d40c802002041258090082408a2002480010741c0500005d21480c10045103d40d071a174101e0380a00d00c201190200440103031112059480480c040f03080000400352049118480607061042140031601403407804545d4070031040481d8001d00d040700f07040003905001401900c08040ca1080500402c5140d2544d1454059540181890501e5942a9418010141c1da91400d60b42c054600802241002c5c0c9901e6842c101007085090350202840207007603200e0710350000380010b4564500903104203136076400100d00c044260402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 205649289 1250 205648039 205648043
    0x17280602030a091b141e0303160b0a061202040e01020d0e0114090304030203060a0213050a090e010c14040303080406021210140613090c0309060e0318040c1b030309 72
    0x40d5500c0c581002510018104903004990340320490300c0501c040072814081302c041d40d45a00c04c103254182120104103148409800d00c004450300c418142200351024005011200c10209541803240300c14170300344a030404000c103408600d42c50b1040402c0589004011000340d079406070b40c00550001103410250184c42410f00e01030380f2070700b010085180407805521562685040c00494510b036101c0c90011078592060f844041d5040e8040d0b004a00861265801840080020300940c40c00c0c60f607800c003103105900345501021180741c2ea80d90340d9002441c28026054084810302d805200403100400e411105c4c003407804060100a645000038040048aa040361080e4014600c03c80306c5291101000c40e244010f0301400501c0544070b00604810b003406030036104814000702e5030204140c01c2c10081c070300500e14500c0600800d80c031007144c0000704500d803280ca0388000c1d1f40c0015503aa50080072943c407106a5100c00e2a00850ac3c014a400c03410354011280030b081e0100102c040701404003802c040740079007940900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 205650539 1250 205649289 205649291
    0xb240d0201092105010f05010e07081003020d03050a0210110a11070b030108010204050a0e060d060908090a08100b0a0e07051303170a0f0203032403010905010f15172806 74
    0x240e0201120000404a03060300c034000900201c80c06c14080401d640080c4a400d0824880d8402b051100d4000c00c64140d000401c001d00d81500d554030340000c1d44510b8114400d401061b0b0015003551032690522a03a000040f0201d0b06011984e11040603906521a0300c4030b0300c04011115800311070b0480d050084400900b01d9003001502d03035841d202014001e5005104851081988000000300410000002c5200d1240145400c1040005445a4000c3d21205108503094041000f800f07680e0340e900c040d0040a82012001050007246080100d811100300c00c0045204503240350342005101c61198040c4e52104540c6080d5442d00702c0200764202354241604002e20396880c0d00c1c1c0071a40700d40400c01030048600c2d2a510403400d00c07002c3c1016601ca1000343c030350038201c03115201a803407103592804040c00f070080701500009001a06869860849100030007820701d040d211480104468070070b071074000182440c45250310091341c450300680d40d00c8030f44481844c0d80511b048401d0041074100700c0085825900588 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 205651789 1250 205650539 205650569
    0x90213080109110a080d17070504080d080114010c05030d150803040b0a0e06070f2010020c0a0501170a050705090a0306020d06150e01030209040e07080a0b240d020109 73
    0x3601110305407040025602134400c07010300140b0501c00086070300741904d075900c071035032030036000011420f05210040c288410f01c0700800000a8208040001d240c60051507902d0380803239414001e01c1903254032583ca800381001442c09021000c0f82000c0f0458172907020090b000101e83c02100303070f120003682c8590f005c0700b038900001c2800a6201c46150083c0030007243c1c0d1752280850085a02000003501600340c01a041a1b500401c1030b00145603c903251006451a0031743d01c0b10003400c1b40c005802002040c2480005812102c41981941800e181030b070080c0809007002d072580c106075901007000140081114414545850118010900500442d00072a4001e48607070040c80d12420804044d501006010014600e0035000090400030402c000000c1c0c1c80b19621200c40305c00d44c80045007e500560859584036a551502000000007080803c1c01041484042c04440502c2e06010340342d000c00524030008403105440300343c5480481811104400c1045903c82020082400100c1d0750000c0b681107244040040c1c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 205653039 1250 205651789 205651793
    0xa08060f090f0a0b0301061224051302030c100806100c05030301172103060f0103020408012c0615010f02100f02040f060306030f0b1b18040b0108060307090213080109 73
    0x505424461003c56105016440d07500c1e003854200c5600d0300c14188001c0b032032603803400050041b50756800c0085c50780441c48040885e17031502e6011a001568601500c6050b40c3e945c2086003014046003681c01c008503010401c10482d60750241480000801052043d0700f24041014910300030f0014180042c1c0000c2100c2e00d0b0368460a000c8a0a010314540318110320a0500b00081a25581582a8034410305400c2504689507142070140c03014000b00b10505264082c08042003030302c401d02c01d00c4140034900300b00f0001040030f04510111041d14081d8040349800200070401c2c1480324902c01d0301114000c3c60f00041c0422860000c90501d1036503c1c40c2031354141008107a034540042a001f03001590142c001d00c0011655551003074003145c8041c400181412130141c0504041010001c0855002400d0001c800b0003054a466201a681c046401c1088650b84188440c41d00e003020720401100340c00a0821050f0b0b802c0000001e651200c6501c915240b1680005910380310420141c240740c014610b441c028000700c8254 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 205654289 1250 205653039 205653061
    0x40e04020a170303070806030a0c030b0603074e020915040e0c0a1d010e0703140903030718030b0a0f020d15031209051c03020a0804030b06030708030f0a08060f09 71
    0x42e80c984000921b540d000c11954a030219a004541d640b0008015016107995100a41d0400040025134140144480001d2500444100c201d002c04408075110300e010124136610540003025070900702c240c01c10035590080ba170019480f0540181c041302c2e150301d240d44c0c4560109140391611480c9401604200c007045200f800000c07821940d0320103c0c0d0070f070030950b00d40b1420600140541816090a99542d004002d000c0007480a2500542c8500d0003244181d40201030b8149540300766038584940c0e0000041004642d484050308181501c91072105072100c1c5151199500014042c3c80d0404241e0303511a81c50011045504403000c0300c40b801c0c028055060a0004000e096000b84401d50301800c5202030311854500c2078160300309841c00104154009066001440025907081800700c00358032404194901180708440500011072054032007000c1464600c2c00e150512f0400d80c400000b5600a000e0200000d011801b40c0d98210034514202a04da0740d10b00020380c94000c84c0b100c886d04013810000f407249000720 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 205655539 1250 205654289 205654291
    0x1806081b04034205060103110c0d030e0a0506041a160c060c030e061302010206090312010b030403170a02070201030e0105060f0607081b0d0207080a021f030209030d031e0203040206040e04020a170303 87
    0x341c0b0100310210760080b1078006032051046489c08d030780040d41c02c810003038080d504c03120f030a00078031040303c1607400c450b5a014601041610255041075040383e041c3c08515040d0302c5a644032000c07803189003002200480190402c4120580103203510303154110854014030a40c4000d030714a0ba030404035112420315883c84130b00c550106000340d0041c0a9000052100c078800402c0b25035070004002d81d440c00741e19040c02c04600b50000380084082010760041c82e000300c0e410b01c500500030348200c44016500e03175a6200250440c0d0310f80904500c1a41000e00b0440c0ca40e8a100c420900e042c000c0e6070265a890241ca4401c1c480d01c40e00d0f160034841852651451005000001c0c00d03400c5203140e4080f145859210328000d540d61008241c000d50242c1c2071821303841c0c8a410011a41d4101425041c00343c01e10001600003814070541300b180c01c0c001781c0c0d108030710118681c40748061400d41845040461950030716401041c0da91145001d814842c032800d01c007103001c548820100400600f0289420b0a0008001139819104c5e88 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 205656789 1250 205655539 205655551
    0x50109030908100207020303090f1201020a0215090f070e0c0d051017072d0819020316140f01090b22050603190b011806081b04034205 59
    0x800c01c820503d402c0740d544200c078526038000b0000c6041022070420031403d48010321701d40d40c00a4402c111440c070030130240041c040300341d1540c018018101e0075200f03821203508018003140f00303070b407105030b003090030010116101d400d0701c4074016a440e11703640d00c40c0240d03481e00c10301c040c2c0c030360b8545407400300400d804101e181c6900303692112075541156046401056980c2146014a55184500103d0700c0c014040e2280003110b038599000c50002c6641d9902c00303540c00d00291b5240381c85107030040070304c510843c5014021641c28101004c11400c00074100000038a500050b2004240603c000000712900c0b82e0003040c0c50310041a0701c2c0300003a9541000c0011180d08145001d2030080c40900c02004905460008142d0b845010026a0708100380c0075a1900c0c2c014142000f40541844000c04030300007107828082000024200c0d40e1070300551401d040071890381d14808800781413034030312003440240300140321140c122005c200d202c0b4085d0018000828610400c1442c00e1060b1b41b4200701c00c1d01c00c04628880e8010a00c203117 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 205658039 1250 205656789 205656793
    0x5040b0409080414041107050c041d1203090703050d120b0114091e04050106030b130b011e050f160209070c11100201060b070803160f0903120c050109030908 69
    0x182261003480181d034034848004129031410311003400104030140301800300482c0203101144080700c58562100c56031002c43c00742e896810403501d041241c00d0a008011301c02011040d46942d0300324182d520303074607420015071609040038004046840481c007000719030082c540040a0b110000002900030701565255024002e4040c249580020b00350b000b4054944d0600a03002d0241c6000105001c01c6442950540c21201107201c20fa048035403601d80c0e200c2c440c0a46060f49000621000d90010081d4241e22070a03401e58080c1450350004840c1da006d1080182e1812021202070410041401030315903000300c2d1303c111300d084804a0300801c1c900014500801c454000d440240b15070311450022200c030043c4280161404111031034550090510b8118010001690b20000843c1c1751035005091307459000c11070555000c0b10200902c40007000c55404040d5000050030720f802ca25503607030b001401902c401d00c400303407003101c1c03401d14110128000e043c4510b0095005000300641001460302802c2e080290254003428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 205659289 1250 205658039 205658051
    0x5060108010c090f1401030c020f06241f0305060d0501180605010b13140102070308041e06020d020c010c020a080a1202060c16060903032316171b190203040504 70
    0x4540d0108200d400e85c0c402c014a00c40d0301c41e180f001980a03200107050ba03021482803031108101550180807541c096002480741a1f03a400d6021000301481c864411001d10485a141107e8541c0101c1d01c54040d10030f0b8142030100ba20340c3d4200010b6914051030f030300507241d942409a040b403e11241940b00342903030300c0f0b0042041180d88401c0403441034000c0304000e115440c1996401d02541503c818650160001441150103c2d41c82c0c1d80d0310340d4a504190700c4401241d2849160701070030132459060b4005080076100500c00c01c020000300a6a400082c00c520303060001d04100201991218501c2d071b00a800751404440c009101d038581071402802000403800140200300103d068107920b034045401c021100810509034021a485140c020080c2c2c01c5c0840034155103101c036601c64514580d480c4070003030f07044c59641d200707190044c86410030061400d40d400420540540c1390000c2b00c85071200c1c54010015140025012020525454541c481e1031400441002c41d08005e4461507800001002610030a0703c0a00070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 205660539 1250 205659289 205659299
    0x9020706110313030e04022116051603050306040609050702030a0e0103051302060d02040e16020c040b06040b0706060317040f05060403170a0909020403060501091820060705060108010c09 82
    0x8980010f540320004603040750401408288207132880b036003400006200510300104d207913044c0b01041d000070b10b43c80118600420040070802d001020010100c060030014030740503184ad104501418461001018483d0200210b49591295400b01020b08a8244208941c2c140390002940d2600101a020001551408a01000d504c64020a0b0007500340c503015041c2e8541039070820290b500b1800381041710300ea080c000011542c050101c1d15000740c040c0c8010a00e0141141e000070f0504903695149401076040540c14521502e0f0402180e040716605070b0010f480300001e281400141100707900140013608000d20030001f0f120f070000108101c0300d040c180c0f00a425600e10034001d031030140c1d10016140d4920f580002002003101d60080108103c2460403034100c40d00c4180880480c0c01980040d240360f0f945d9001404100810310501e10301c0e0070003003207800d8441450b0b60350381210540889403103020344000d645000d498030b40c14103031111940d0000c1078401640c0c58460f00c1d402089541c8582002500c00c03440050b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 205661789 1250 205660539 205660571
    0x40b12060a050906040906090209160212040f03030e010e0307091e0911090601020718090b06010302070c050f030307080403060b09011e06030c17040302011b02070b0d11040302060409020706 83
    0x4841c400f4010014035a01d860400c8010140310307800b950060f84452a00c001030360f071449100e200e04c42e240c4e25100100840b450003031030113190a001d032480741c100b000240803080c00300201d6400c40c0c1d07040c645407119140441c0102c2d0b0105011820743e41501c04d2100208100c41107400410400d1240c1d00031210781e2007181042401d44d01034000240000d280411001a01d040c071120082e80000d06004592840381d0b1210004950304000c001d072180d01d5a548407820170010082c40a40e0000b2007442c1c150704108042c5c58403a91100f4600c038581c0701d020884582c1c60143c50501c20b0307405290300519655240d0b943d90605501030301082e0161440707000950000b00d0780142e43e10344d00480f20340b01040300d80c4d44c1341070007821f40091881c04419428042d07000340042d1440340000300c5511562090380041049001d1400c000300c807400e0b682c001025900038003414450480c0000580d08400c4004c07102244d4100360b007204c80708510a0b40c00107900101c001601061102080d001403005a01c2030741e081240041802e40c01c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 205663039 1250 205661789 205661809
    0xe1015082d010e0d030e1603080904091a07090608060603071805031608122107030b040905010207030e030309130209043215130902121603140f21090402040b1206 71
    0x381f0b14003181005001066510380542009140540001411000d0383c0b03840d0104120040503040c0b0b81c10035810014055400085440100441d05002c0c0c02420b00c240011303a175010090030282005125810721504041c1c0c03001d107038028407000c3c0c10794660000030394500ca0010030b1409480001c0c482e41203004201d40341d42c81110309a0900302c2480030301468010000002110148c080c400f09520b940e04001c80d99500c6c861901014800c40005a4640042c42c010700144814644603101e83c00901081846c2d0f107c4c1294a8520442e1100c01079a907480400014000d11120482d6580c404100b6485407100c041062a01d0641a03110364000c000e035a00000507e022a030082d0a40d0810440303800a1075a01054200c0783c00b00740300400f01d00c40d1241c601d19480c81d01100043c480c18802020340c0800034012000105007481e500d50002e4180c1200c0000c025a4030326240750300304500c0c02d0346140c40401903244419500010b000030001d661342c40c2d07582c444080c10340100c00010b5074001c3c10320110310945080042c103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 205664289 1250 205663039 205663063
    0x321020a030f021c170a0501080c0402071703100e0c030c0f0c010b121b03030c06060d08070807060209040e010207210908010e1015082d010e0d030e 65
    0xd06510415580440308016a5001d56003544103602c1c07180f40000d810a030030461080300750f0361110b2201e10100800c00005014142c1d0150500c0c0c08010300485001189004800c64203031005030780c5940d5490020174002003038068525407007003c000c1c0a0f000244e04104e004440070100921840d8850310400600c91005868a0715001d41c02c0242d205113501900c09489201480c03000003c07040c09a001103408003101c403040d401b994001500b0b618254100c01403603401e01038141e00850901e052129440c1e51290042d00482c03040d0b13103c880041c200706140e811109000d0f0710521040e115565443c00a01a4024068117481030b070403c1050340850905209689415800051216806200c18100046122103401142c00c002c0100340c0850001001d0060554115015004044584108507070b0300403590100c031001e5008208032420000c0c9400000c4503c3c014610004d01d1982609401040081c1070410840f8a40d55007004600b0303c29400214058411201c261400d015044407010080e844801166403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 205665539 1250 205664289 205664293
    0xe06010b041203120c020c01021b010804020d260903070b0307050315030c0a03080403050705010c2310090501050402030d11030a050f040f0b03041e330c09032102 71
    0x100b00860028200742c0700c4120702030b0400c400c0d01c2514051010a41303170300040070350250740b040c00e19901550741041301102e4907c0d000700140030441c0400000b00a0040540061321071083c3d0701496092144030606d0794000390030300001c0645a12010442842d035004078a21b648030780900d0304000742d4011006c044920810b800d41d982072955491200516043e0400b48440f5018070030103000100742d4450403031b09030182d4001c50308141c84c3d03407039480d0491414407560071082c10050768404290000300100d000180b14a008010f9100c40880041000d01c1c00340c500030100100d40c2044492401d21070103602040c0603070b0007074081c0d402402c2c61400555112200c41e0500760164000c02103900318031f2180c00079191038050811964034140c2d40f0300d8899500042600b1a1410050000c140020000208144032044140e40c40c40c031200d08468407500310708040c00c02910220a0300003408103001c800094076a482003800d4900f042040703d0044000d0904100740001c450700840340c404a00c1081c0c4c541000c00790a074650380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 205666789 1250 205665539 205665547
    0x40501081f080609010207060608120a1b0614091005160f050c03070308010f060c020901030314070c03031d0102010e06420103110702091803070c0e0405010e06010b 72
    0x10903803103801c5100c4216030a003003080010400140500005000e003901e0400540c545444d42401021210341da8402d04040d4072009140265a5003d400d0303c03001c2e41181005500c040d041e0070150500703020070030018409440c240c20750000c00c03252024a4005d4001208892200b94000207080444000341c4155002d070f14542d542070f100602c071703a4103050707414907500e4a28104400e490b049440c5400c802ca08401160303c550061100441e42d914030001083da600e006e5950851a8020440320401800040c080101c540e030141c00c5221280122002aa40aa203803082d059032401c00400c00c10320640d0780a1100707019094034407198070500444003481e941074003a01481d1981b590f154841000069401107081641d503c2d80b814080407000e901c2d10b8101c1c0b815402030010420001811901c4c00b00461001007414881d9401503211084003079480200c41c0200d03581003600c0c495540c40c50060820041001d0369441d400325994a00c030801074084c0780300301d0091102c1c0c103540704030b10b803505030074080c4d140400010300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 205668039 1250 205666789 205666801
    0x8010515041707031208041a060f1002010609050c040302131d240109020304080315030c10030207060605030105040f11040b0a0b0702010906050a0e01140409060e091204050108 77
    0x8850415000032100c14a425514400000c51180045a150564000b0342042050040b150098000d02104e890154294905a03441600b01407600d0350540d0780c042200d0002d01240c540407846280c0800050441030140401c2000a0117060180100b0301e18a0800e004a0100c490312801c1d034040e01d41c0200703901d0003441c400e10200010b107002c0c01e400e258603003c03c1c90440403a505105a41c0003034060b04851816410000c41092207640c1a80f04011141c030400030080400c0d101c0050300c1c1c1040c4039600b02210021500c002070300d45500d034040f10307a12054010f14410060342640c0208102441040c007800070b107a0b50001c142c03ca8038121406420f50000c00340001c009501940d20f01c040840042002032142000720100d42050190380180e5900040002c644040d981c121081000401040c030f0542c0c40c02215a600528018900700101c1c180250038281c1225400d82400b0303a0080c040d801c000300445551341c0d542031032000003542c1040e46401100c9240c5004580c0c8000c440684506844e00011a2105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 205669289 1250 205668039 205668049
    0x313051018031206050607080a02070e0705120709180605040513050c01051b0a0b04050f0726011e02030403230406110a0b0423190303020c071206020a030501090b01080105 75
    0x1d5183c0407050b9516a40401c442e42c0e80000f4200190080c21001d848004090000e841c240c2c80383c000d1780c0040e20344410084d13180d070b00004450040e0302c440302c1c400c0203403102081652050380940116000264031810041d800c0721652200302100d804640501c11511154015407080b906084054150b40003030201042c1da5029078014010108910f04940020080590b001c0c1409261807080b00c0103049501030000b0302008000705200e18000a01a010080c9860401100b030340e55a011082d1003045032103210003458080d400000031410b44241d5114104101503003500960080300c2c120081a08060310001c5807611400400311500d021074000d2815003007450984155034030342d00c2d4041a100303a40c0084001a540000103014901c070300200715410b00840528920703145224882161a0302961041c8400d04c560b10805144d2074040c20010b0f079880c801c0e0150350818106030803000015440305164030800c21f40781c0c020134040c04699400c028690f01c0304214030503201c2c2c1704181d80c009040f10005104920345 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 205670539 1250 205669289 205669307
    0x5090118050d050a051918141806030f070f0e010608070918020c01020c10060503010e0712020402090904031e0816030f020c07060e0906030309101211031305101803 72
    0x38500b0102d0900306281600c0c807400c0c0141104100140114541840e4030f070742c410031f03400500900408030700144402004200c51403551412480c1c0424403002103031280c2c03070510003101104000800c2d16180340d142d0b00030040f00003462003902085041640000343c910311950f045030046803180d0b02c8a041d50700d00303801444120f00c00c004102e00e0b41c0d400c000f00507400c042440103240c88001080034260490305d0384e2041044503025403281c1d0083c0d041c0044021146000302d513560649036240300e0401415610f002160090040d2a440354000700c00f40180b0050640160300018404940c00d410181003554600844483c0c40540701e585940203000c40e401001d1340640c11100200c054001c004bc100804002c1c01483e092803070f440000421041c0c010b61255060a05115500440940056180c45180f0740420304000110482c1c404200e40300382200300d0905a50071440d041503120224540b41e052143c403080e884540d491007101c1502c1040200c41d500c0840b13002e01480c00200b0180284012640d803410749098007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 205671789 1250 205670539 205670557
    0x120706090507050a090c0e01020c01090918120c1101031b0e030a05010c031e060f032003030d0f140c040b07060f0c0f02061e010b0a1106040605090118050d05 69
    0x500d2070100f02501c82000100003400d90700b40200341007040b40f80207000408807201c2c071411504042c1445600c0d0340c211000000310307140d813007002411039151010fa05007000d000030000d082d004445014101c0e554004240540940203801d040409030002300190200c0305c1054800740a0801e04000d0b60350b15006041020390b4010103800e9a05803400d07030b6030b5036003140c00c03181038075000c20764406035105484404607154107401e00c101010400e00c2e0914240f039248480c2403200410780c44401102d44084840f0061842490402508407512000d00319901c901034642c0c8000408018513040c210107041c20000101e90061516030116071a150514103818015444941c05540880d10380c0c40c84400c140c650711481c012000d4980e68101d03119442032009007091003f8085c1d040000528001e0b048019030340c3e80d0346045a85a6035060b6507400c5180c0140d5040060940702c3d03056010b00c804102c14050141c10013841010228000c00c2401000c0c0071a031403824070700750054007641c00440d096140c1c502038801400021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 205673039 1250 205671789 205671793
    0xa1404120f0203010914010e070603020f0f0306010504031a0402120303040f0303020306030312040804320d060906020a0305010503071a09060c01060302030a150606050301080a0308060a090e0c0f031207060905 91
    0x80e90701d4603426403a1031b003065114290b80d5a074090303082c540d20505c660f0018007840d28080d4a0140311600300300329405480f0b4003201340074000004c80c00c0e40c6c3c040c50440c0c0096030300140486100d19103202000c000a0304440690041900d114034a0018101000b01c1b4415984001d44641c51031207900c0481c0290401418a82c15200420650000d005000000c07171040d8400e44d00540d071030f420a04040011001048014282000c802c005201c92003026603030b03c5c6010040d0f4504690f0030503800c180e00500381c00000039020510000d0b020317041c1507160300454160ba00c10b0301100e815a6a603088074041041c0d80b055081c6101091203d1445c91401c40010110030700a040081001926900005d0405200300c0b821074030603086c00c0d03240c1140369440c00b44000600382e6092290466140c500141d4940304a000010204001940040c2242d91482080d04c090040544200803543c0000340b260781c1e0303020040c9801e1007201911416032003440e000600340400084589400d040490f42d03071743c040180c4400c0100700e400d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 205674289 1250 205673039 205673051
    0x200a0b070503071101090e1f0b0f0702040e0303010506120a0b0a0b030708061f11070810020d111312030e090c1207020a0506160c080703050a1404120f020301 69
    0x901000009040454000c0000c0c50f5501441d140c4000f1410f5020062410b001c807402040080300203000e42e90340c3c4028081015107c0d03c0d02035403282c42d80c0401d500090324125002c500f00401000300070181c032480c0d200341c0d000c2050249600c86140e0701e000901c1501c2d40b1a5040000901c41d032225801260081c2821001180b0304100300000341c1920560740012004542c0401002a00d680c020b00b01608420f00b9140c9225244c0c0140640c0f10f030300140002c1d80305228480c40369404104007001248028032121040d1030810914a41d61800327540a010341c1d180103424000080b604000000440740002100c0501d06a001d107407040c001c00c81030b5002070a07018000f03014039402c00e684645400b213100720120455207641c0c1039a821602402a000761445007150310140d5a01e0004500044894200245005068048100400440d6801441d00008000f9600442e9200800d034014001d0300003102c0944420404541c1110022070750300a80c402c509403d501000d08001150920f0004001d00c1d0015001083d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 205675539 1250 205674289 205674299
    0x905030705060f0708150a030f020d0204061e140604053c100e01080c16140303010f06110705040906020d0e0f0f010b0109140a0f03150c0c200a 63
    0x2400e034121008004550710508100d00fa40d44a4504d071b501840002d440344d445106000420f400c98100d000003825840100149030a558440002c4000e0070790080c0180003c544800428010000c02000d460304102d401e1000b280c5c035100321401c40b404400c060142070a0628041c10400240d40320072085d001c10038005e1070404282c0b603004803540d0303842d04840300c0a0b2680c01081404246101113014104000000b203079510700e42c0c0e100c5c6901d81c000c0d861100c0a038440201e407004400d000401e01c0020410101941a07003580c80010024504131350580f13001c1c500c01d80ea64042502c0d460740390304c0d0840307240d00014418000c41c5095030020f101c07640116401801c114188001004a031002070911205e41d00c0760100c2e0079100e100704000c041241080d8028403101208400280c840d40250207a850300710050112108141c4400c84500010319000aa031154959641010a028400c490820800c2400c03c4201c000c294010088004985d48c006018014041d0409030070442d0700800700d480e0f600c03690070341c80012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 205676789 1250 205675539 205675543
    0xa020705030a0e0f010807051204020604270507021203040b0433111602091e040309091505100503060d06060b0c060a1404021201090203070f1d010e06040905030705 72
    0x3001c0815615200409043d4100f0001ca1007403105820741008280e00400c880554060291014081c0d003c501c010542c480b0310001e040e500842c2c0018150a06c031500605021074203140001d0404c14004003003005881d001d1080749c8902c030311002c440d0358140c10004540010b030210788d0194080d0248800c481c10121500c095541c9910f600784644191030462140d182e42d405a2043c0300d90900e041080300d01d40b9804507019a03c0864000020303106c0d0341c401c0001910a0300003009c144450b21b588249a0492030549009040c1141318050003a680f80f51280030541190058480d5040d07620040c00f201a048a02800b00c0e5950300040038150880b14019130f01d0006500e03805010080c01d01100515155400740304a5481c00d0f0004291000443c01c04030780d80b1900311640c00d410b030820740689200481d00c42c04882207002d011400b800a4251140600c001034800e0203200270700c01d43c0c0200b00c3e0180207000000d08416400c1081c0981d54040d00e28101013a01403415074070844206120b501038a04201090319a24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 205678039 1250 205676789 205676797
    0xd0615060c02130b0307090903120f060f0f03170d140106120b040908160206040f0b0703030b040c0f110724030b030703080301030b1b03090c0f01030e150a02070503 72
    0x24089000384407400210725001100c0d00c0205101003040040c80c1d004400655a00081c2c0314591500740c0c0c80d60a001854495181c1403505c0c456010207105031411404101d005101c14821100c1c01c400811011403001c0501045108503030300404680c9010341c0344000b03008030780d11407070b1142d00c0a0740d281051100d511018660900074045519007544d40b41000d5000c0d0103540e9078000756072140e890558100000b540d0402078480c2c81c008034800180b91140da00c0810441d20030343d0414440041450302c00212000d48070f004020740c922035a420301c1a44502400d110a0300c00040016020845190746405141e02c80d8402c003001100b404c0c111001c16951b0304039800d03a5422040082c04000c20100044401a007501601f4030301d0360250300500005140d620344410a00041c003005220420748008039141003003107003080d0079080c683c0c0c0e1420340d40e09003003051039554004140d00303038052040010385d00d01d150301a2281701091020200500010f02e01c18601c40e9504200901800c24161301348082d02c0070a400708058 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 205679289 1250 205678039 205678049
    0x1903021c0e010b0a0503010c050717130906090c030b0603060d02060d090f0507080d02060703020913060803120105040b0604051c05010504141c05040605160209150108130c050d0615 79
    0x1c0c600f0000c40034003084035440d4012501980c1040760044c00c0a5001c1c04941c240d6410034003070b0302050740c829041001880b40784c0398117480e44407182010803003012981c004001c070342081358200a0740d04280c80940990b103030500c072103038031000c2400090300505041d040300c4140d0f880201454604180d0308501c00441d0000d1905640c9032216215400821404002900281403a24020304200a141400030351310f000c005e04003000c1680115450405884d9031001c880c182001400a0010035251300d01176589403c440d00f00c04010b0b0b1040d000148900380f038070030540c1526024011070300e41401c24080c041c3d103418503c202401d64940c0e4245001080c420300c03540307018901c0b40c5c000d100c55a25001030b80d072400444060801181440404440302d00b6005411201241c0d07103402d0654942c20102d1164014030030007a0301940240c0940200200c640002e0510b00399035000341c980b10a15212100d00c11034075181a540205100070701c40c401c0c05a454250701450503e0b21a24010070240014407080d00c0350040c039800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 205680539 1250 205679289 205679291
    0x301050a020c0613051c021513060b01030e070b0a2c21060103020d020d0501050f061203071a061201020408010b040b18010506090d0512130b1903021c0e01 68
    0x10b0441001e0280704a581000050007a4140c03e0010f440f4103499001010340641c07120580b40c002c00701c40e4001d0217070a1554034501810f025502e0255821840c40c0000f8108031005850501c101036158000d104607640c4030701c0b900050483e9802e000130132090364402c104101c14002030540e207008840914000c54500b0619071403842182c0401ca06100c1c101d00300b2802881581455501c500c0c500200141d01411a038040700d0140024a00f400403d54494038030700068425402d02c010040304498450342a8091131080e55403030a40004000e940d0389a0054401c018103605005500c405002e9200681d19040171004005842030112400034a08a92155114000c1c5945540001803949414803484440130740988070300360410200250640c881c44140502c900c11080484d8203441a224441c5140190303138004102c501265046a40940b5074000a01d0b949120000c00f00c04100f48070080140c520201c00c000c10f40211040080b801d501a4000b43d0201219003100000140d011926000d880c80040303190380 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 205681789 1250 205680539 205680547
    0x30c0e040501090c0906080103170a0c050d08070e0d08030a150506120702010b0f030606041e02070506090f01020403050d050703020a0c0b07020f370905070207061e2c0301050a02 78
    0x14000d812032500742d100b8014413464500405c00f040d403644110381400026204180e466012f400c040d02d50050b02000981584a0740800c40502034010358414001d004d0381e25107001030380003a0304010310000b940b0710003040e40b001170005c100b80e0700c0c03213400c4074404035040c151a204160315140070415681154281c580551100814845410380a1044c400205400e4480c10480c1900c04007081d61958094591b178003556640064082840090072682c0c640300c202031080d950781106081c0140d946d44140c0d00c5003514000e0040100d201d1f00b051081301d046076400005408502c6d0100f1055a9a4100b200250154002ca4440d04006900d007400e50300901004985503071a11000e0062042e6401410151400342d05451030410300704184030110340000900856844503404107910344800080d09501c40300c00f850806090200280c1c0100c2d084007990f80a43d01c2c441e02842d1008141d26040f0a055030a021a11105903852b0420740b110000c2401910010201c0c190080d42012a085800131201300c2481c40d800701d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 205683039 1250 205681789 205681811
    0xc1507050f0303132f0907270303141306180909080a020606040603030e040f1d010c08160801030201050904090510020405010906030e030409150308030901020d2901030c0e04050109 79
    0x64142d081950011501100864441017180005080ca8030203500c035240d4903001a440d244074110111403540e2070162001a40d11358110010a032030341d80030880204403407448040c00390b6041d40940f5404000014544201813030450251503418100d14047c0001d9001440401c0c5440c4034000d46642a01c0307021007907603c0c2c0c5084d00080c00d080c000341c450b61259080443c20000700340e01094001100e0001c1328005001001040714800420f40019000a0315a00403030560300c0b21303011340c0488813807400d030303124602d40c2e03510703880d01c25401d018007020781c1d002c43c008400600155200700082c00711030384060400260041c594031200d240c0101c00c440b244005070005030900c2a540c0c0807011100620190409100442ca1007461940b00e01842c06034042160740d50312240e07403050000280c80b00854208031099074a05010390030601070f500c4034441019441c10310215002020680c4048010002c50342a28148400c1444c011409402e0060850003003001c01c05c5031040310f64551080600a2014003c0003030414602 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 205684289 1250 205683039 205683053
    0xc030a020a06141003030e030705040906140c030919080c0604050f0c1206010e0a090c090507030b060c0606041a0307060903060c0513030321020703120b030c1507050f030313 76
    0x1150403e4000d4400d081c4005100d84640020650b41e0606282515815038004a890118241c1c40158042d081858100900100c0d82c000fa03000000100c4074042c82c0d88641c0e03845a988410340e40440c1550040b0414904050408004607103c2d118159440c0b40012806109140c440107031400c1e5070503000b4200300540100200030812191000b612002c0340d00e101503a0f1103032140014410700610002c85000200e502117a90300c050507099000181d924000e88035a00f041c01850222543c5c40441c0c80c007c0c07107020b11b20f00002602c0720205010010510303941c40909120141150b190601410342d050300391109566828030400001e0301c255901c3c4c4030060300e141000c0098882d01c81c86001445000c208603d03d040c28409454240c80d003500b44590341d4106003a044080010b1040030461840c404540c1c10b040540c0032029800110002d00c3c1031100da40841c04058076281c1a44505900c0905030702c150507220702000150642c107001700143c9007a4420f01c800b036815507104a40031411140504111300401c150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 205685539 1250 205684289 205684301
    0x507050906180315090a06090206070203070f0609320414090307022d0907050705010c05030117010c09061d060a0e030f150609091e031801020a08070f080c030a020a06 73
    0x30130041c60845051548040d91a0001504094407a41d122003011003503482d41c07012036040b164003804803101c2d540e40f0900d1071040c420502503500040e550000008540c61801140d804650540b95540044100d1102100c10103220305915504691140c05001000601d4921036201c0d05140000d169030b00e40e80c1c8100b2640040c041c00c40c808021008103c4008500c412200b14840c40b800d4402201503120030500b07a07054068800002d0071907081c03a00304050503501c00003860480b4003900c20044000b90081195023030f01c410301d07054000164400410002c45215110414080f201100c0040c1d245a107000400c6495000e001514007042a43c00661540d0804011010711804000d0141196198007480c00d46880c1020304a5441030040b10b020a210b8042807121456400200c844610b81c0b10f8038440c1161290481001c1d0130109a011b0020007855002050007048681c2c085c0e04a0301e808015034038041410720340c410645254000f401aa035400d00d00b00010800c040300c2d0b4000300548200c500d0406c081d182 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 205686789 1250 205685539 205685563
    0x706050408190b010e040f06020738070e01120905030703090807060e060a110a030804050d0e01080123130b0a06090506070312110d020301031a011805070509061803 72
    0xc510041c10080f600b142d1085042d03c0e0a2240001d042d283c44c10040c2844180c1203001d48040e01c00501d800801046542c040d120b21004400340309041030102261590b40514140900344070354050016031828450f0307041036000d00050402c481d0740d411820030441100d50203202183d40e9072000a051080c03503000051000100314100080480605001008240c03590350301ca440e01a4002041a140c3d2a0007201021000018401103032001c2e680c03170030020440f0340192070030340d42da0140a040f601107034030640d0706468001044c1c41d1004140d10b00300383c03140c007550b211242401440b4204240b801036543c0039070324007060454090100340503101d0b604002c10141942d000a0034010910b10401c500e80310041901d02c4603030903052030f007108400550000044d00401060328803102d0000340c00301c2c011301a0b40c05181030342d002d100511400005440695138a85080c01002d20b40d0329002201c0c40704600d20b40140344c0c08030300b520b803c0e410641c00e0408a0555040301403c4c0007034005420541d609030a04101c0004194 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 205688039 1250 205686789 205686823
    0x5040b06070507030602090103110c100e0c180a230108010f050f010303081312120f0507090e07090b0d06060e0409030806040c030e0604030306030b0f092a030706050408 74
    0x201c05039141c66980380b1038407000b8080303600444c2e1601c8684c0640e1140c19941d5440c0b00341941d40f1041000c403515480c603c0d00c9640920300d41083c21854002c00940d4280c855005080c1101c442d0141c000003624070801003c0d40c3c660340d107504203182220403442800d05800f0181004040075410401c0840c00c0d0740100301c110200c28503210401c88041d250f0f0040c0d0b070440f5054249100151140952101c800d45400009030440345100f100d0b40940d40c1c07016020650300d01c22202000000d1141e031a44c0140c5405a4500c4001103100e00140704607408240600d80204240c00c0c00c501c0b15544042d0580150000c88a900840356242003c225491f00040800c440d500111410060b03c1100d83d805484400c010782000e00945c1e440820b1f161040c041d5100f03010703102c01c000880d81c80c0c0c03400385001400f400c4c080c0800c48200f0081c501043d64086100d1220b401244d54001806c0700010701c0070001c500481e00c004403040c03620808611000d42c6c405008400c00ba042c02e985840c0e0340c038140071540b4a4a40c102d00c0786030729a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 205689289 1250 205688039 205688047
    0xb190f0302120a05151905040803011406041202060a05270909010c021e0106030501090b0603010c080906060607020f06030702010c03060b0903102c0d0210020a1209020307090f020405040b06 83
    0x203540410400c403c50800c001750340e820340300c10136000c00941c0300d0328000001c00d1425060005014034440036504031074070060580c4200070f224080c45064001c0e44180d010840c01100340d8001864980007510551070140b4002e41424100b02c00c4002c001074000010f900c400b00385500c00c502d404c040c5034265211148000034801c049128070001d640f01003c02d190811a1840da00c4030440c0403007174000b01c0042d03401100070311800c107442c10302414110301a24010310941ca40440103413294011a90340d4801d50800c40a02020f64900041c01a26031105034220303441005060088002d0352010040e40c090000da60001034690050503000e0229904d81e00951080c04040c0551411580c00141c80358900406030404204040020801c18281c8040c01d4048020001d40c5140ca01c444c45c001504400340380303940e003161100048141c81008a2060104101c001410400b10340007294031900010360b0980702500300c0301095070b00e0116804a9145c286c03c086101c2e000901002240340902696104138800c40d0b1040c0380c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 205690539 1250 205689289 205689293
    0x5040f06060e0f130c0206150a0509040b0c0d0603030f02070918020103020c01020405040c02030a0201050105060307080114130c02031206060901021f02040b04060504030501051e0105040b190f0302120a 88
    0x2c1c500c40d14519206081040c0900025111890440303410742e45580c062009820301c1c0000394440703d00301d03a268880046550403040d20314020040c1012104007401a11058481d038030b0301c50b03018100411900c1426001c10000450b450307184103200080d0700940d126440c1d080d85040081c1003861a611140c040b42c2404008119180a1180400355660900300144d07582000115103001e400740740d101d81d500a1400ca0702810468021004200f008400da00801c11aa00c071130030410f950106982e0f60000503808001441030181303821030700403151402000407403100c05031558001900c074110007120058101051040300400c441880b260402c0c01161018180790340400000d43c5c52600680c02d40e00c0ca80121070b0309003150034a40c1200d02400308031001581d40c5403107003806072013580148421900c540ca40800224a269510400080d204d031040070515964a00020040603040b224a00e9603c1224114500c1a0b610403600b001c0007840c0b091020b0f40c0451540c0100010007111441e000b80b650481216500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 205691789 1250 205690539 205690547
    0x30b010b0309011506210c02031b0a0c080c0a0b040e01090905010f050c040f082b0c120201140a020304050705100905060301080a03020c031903030c0903050312090d02390607080405040f0606 83
    0x40c00025160004c14650080211142f030640c0807070000d800301000c440040b41440000c81d0003a00050250f0f2a50300281e43d41d0909685d44c443c1d841001ea80b400088018001070749580c0000c11a41e0080001150580f805001c2e00704640c000e580e0100c02c1c2c4c1c0b0000e807c101100341c0c07041100080280101074040c0100c0205100f1841c0301c2c0c0e040c000340030307072095465064a90180000c800160380082c00d0002c50500400080d00803d549250a40d040e04601e00192002c0f419001700d13403040e40e01c000a000024035000920400c4543c0500305010b01c50700390004121034960340003650007000441c00804400281c0d003000f07824105404805800b9402045002d4681c003d4000c03948903095041c80d000070b031040c08403c100c900c81745a8000420758000001c0d20413500e10403104841c010b0f000d0300c1c1502c118115111081e41c0c1c510f07441401510010000c1050074128080b400b0745007441e4500d1140460202c0c00c2d00014009038880c41d0b08548041e800b050511142c106072059aa4030104d80000700441410701e80003034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 205693039 1250 205691789 205691797
    0x6062104031b051f06030b010803070c0e0114090a020904180b0c0f030412050904050f091c02070e0a0906090302031e0f0f1620031501030b010b0309011506210c0203 72
    0x2144e141a0303041c03141d080c48164050402036410602c0300ea200e5031200643c544951080009841010b070100c008900b0a10102ca124100ea07200460380400400380d40900c4855100103103d94075090f4244480f100c9500c5034040c501800508070001d481e1900549410421080c002d00b140a0340c1d20203200310402d14640004036600650460000c1c001c040e60020120303014800e01098603006400c1005100450110780103581c052403001d004e0f0342d4000d4110101d2003545202060150040e03201c824100240d42d4007488a9400c149089000f184105440e142c82083c0c03800a101140140d00000344601c0d9000440a907058a0000007030062900e1004030802c0e08a004180300440c11440c0000e40d112101c20005002003485d900070070042403012080ca0b224541c110509982d4044c0c00fa000c0d54507100f00e515200c142c1a284d0104011152386d003812241e580580008041102565a44203a04c2405000d643c000d0001d190a0340c854002ca03805032405501108811146403400742007451880129030044151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 205694289 1250 205693039 205693063
    0x1a0405010c050a050a0b06030f120d1508030a090816060f0e0d0f080901030f0b0603040b070507170a12091a28020706050618070806062104031b05 64
    0x1e201844100e0030400c0c00c0c90361032a001452440f5404039502007140b08000f581c410701c8124141c820b15084060a0794071002e0502098201c0e6000b004825a0b0400c01d600060001818404a214054490601c0f6145031701c250240e0020480c074040401046108024110f1640c003c00c980a601620300b04c00030300383d082c07110780003400c3c0400380c03500114907100c806513030020341d03008004c09155120303074205040c260780610f0080740000c1c01c000c401c031107401c10740c0110304050002602d02444d42c0d64035266144003100180c521410400304010b142e011481840d85803040d020078100180d5030300d169440180444091502189229003803a0242e00424545540d00381030a101003001c07182d554a0150420100b1000300310b82c0d80400c602c0341c075441c000d440d55004d868001e00c2940d04000c7c0f42c5800e410400c1c034100355405003c83c10100b5000a503003e1180a103a0303000714020b00b046062004a02c65400300498202100d804008500100302c00c3c16846140e500f44404000313583d5290200c26294580c507a125048a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 205695539 1250 205694289 205694297
    0xa05030a03230c030304140d0e06030a020c150a05060406170319021e01020d051f09090f02040513020a06030509030d020705120f0715020909010e040606030c1404061a040501 76
    0x400000c03061841164507040d8840142c90741d0f85420f292080d0348842d1f9610513142445031004609881e4004c8014900c02140240342606594900030918080e5004a1000c546406a0081410b0f0f07c0c0c1001d00850051102001c0441d05181c810b040c00111251030380810480042d0b55030354690a0004400c850908104030b0b040c806040d4030450a03441c100e02185080304011220f40b11844100042d4054010084407201c244015166450101066400b44059000d40b1802e00c208011280d580d501c03200c025885400f00a840c240540c0010301103843c121000c0d10406800946a0118a44a02010080c20050508000070f0400514042d528056085c141c8400c987c000750403400e1001c100004402144040301d1790b5500c102d0054240f65a4200000848652000d5a00800005424026034054400c007038980c0295030b02c2c0c044140709481010f80282d500603030319a008000320340704505640140207411118844403c8810900040b143c16900a00b088201c820000302f8140035101110121102460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 205696789 1250 205695539 205695587
    0x607110301110c0a060b030a02060405010f021204090e1c0801050d031806091503020c032b151503180201050a140a0e040c050901080105090c1e090a05030a03 69
    0x408a40102142400200001c2d00410048041d00700019800c480e2803203400140b2285a10ba0140340d520703a011b078130081d403003801032000f4030055220341c0c0016030386c50503481122100d5407d500404801c0e0b2058009400c00c07034540c4801042007008000491480c140506800400084400020010b80041c001c50f441943d10700c407904103140c0b050780c41c545103900310001301914695480015051020358440d9915030340700205800580c5000c0c0c030986030700345200406189402d40b10ba1000c900030940d01070300d01014202514080406030180b0500100035113860320080d8040c00c01484020400601035400201401d240790303801d154580f500c01d10590380c0d0a00f8920b80300c4245c07070300543e0460b50680e00c282c0c400c0700100f41100031a500071050090900107403810403200d11551411112031007a206003d000c07a040764010042c070f003000322001750312181100d0340604022075544601d114581e51f03070075074035500c1002c01c610003d441c0880c204001868110002c1000d030400c1d0740e02600d1410040c40404090030f02113 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 205698039 1250 205696789 205696823
    0xa0e010209090a0605030f0f03030415020d0f050609010f0f09200a0f0f080f0711010b040c030203060a0504090f0314131706011505040b070c03170301140607020607 72
    0x1405680364100002c2164000c0d140c001200f00040041d0700c9418803078400c100000d0350600000c5003000700e00341410095032440d9621340b40c2c03035604090702040f400b0a950030032150442140c944502c042551a004010416040c0041000341c03a00c0c040c0c10085040c4007000b000c02030100c90301d12540841d00516070106000d905160613441c290404074902c22103000001d01b07080b025612804031041c60510352607100126403801e2003100c00c280100e03140e400c07440d48680403500d43c0c0d0242e01d100140400c088000720302c80a400000c9400d131016030f8440380101e9008814010a40340429402010748820b403400c10580180f80c0320118882d01c4440083c0034131035603a2001c03100d09840404c5034021012949101d4bc440c0d40c0d0219140d081490355050b411ba80265000030400c071407880c24418841e1810358a06080904182c418205580190070440e03c91414102c004001940b000000c1c0103a041d01c0c0d10309403a50314040c0701100206148c5541d038801c0360b08000910059a6400c169403200d60070100c032480e500001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 205699289 1250 205698039 205698041
    0x30c020d022a1503040309080c060405041a030f0d1409150d140f0106080a0501050f0f060d0f0504150b09070c11120d020d0206130f1b0b07020f06120a0e01 68
    0x455140382e0445104010365403014210f80040d03004510030343d28101405e41d241c00c801d850305d6031625000d170700c6a020401003240d40b41942041a0f50380d65551185005001070000a10b0001e0078003031a109600494154003000d60000c200400b04001521028540002d510004043c40c0030600c001852540100b4030601e54102580552080840c952000b5036500300310702c80e0808040240700300000144944002103542540b401680d0403079a014140c540740c880d0301c800b00072025184820250f040a400d11640388003103821b003e90b201c039a1402100081a003403d091450047c80d04a82c4004414102800b11102d912010402580040c0740d140142006015241414401c0c07001006198000c1941d581300c0d40701140451002e56044054003101c241000e0200241d0311454115002070a81030f5035000080030940c00030a440c00c10f40f0482c078068420070b12082120200450740c00005805102103a02d2045040001d202e411000b4211411401c0070314a0007544001e2000400c00e00d0841e07101d950341d0800e141c4c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 205700539 1250 205699289 205699363
    0xe1f2003040602030c0717190c0c06030506150711120d12150b03090105010e0604061d0604060312020609010f05060d060b03010e010f0e06162015070c03030c020d02 72
    0x40100a16054051402d036164940c11210102c00000b50b1190400d003124024980400c01c283e0080ac03c0c2140351074038006030000c18005041d00d4010b50700b00140020f82c00a00010940140b146500981d40304c009028411040031150200507036034440c00744030102907040b4100d0341c15014068401b00d003402ca40d0140a1901b9842c0d481514982004810b2010400064100070b050f902c0c28414001e1a83d2801304100036680ca40c0302c0c413049204416000f542d1806440c84840d070001016101103a0255203586541c1a0306510000d000141c0141c0180301008000b03014105003240c0d8410180001d040c8100050f929a038046402400c15580e18952281e6850030f4000c2d007140640349000700300d9440342e03504020150508550540050207200000f8440001080340b040340501a540c074603d14210075413515008200065141409100791060070144500da011000d200b9949561120001ea0451801401391110b0024050640d00f2514512402c1d55002035880e207c9040101c45041d0412006c20303014160740 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 205701789 1250 205700539 205700543
    0x206041a090603090309040507020705011704110a0f0905060102010510051c2a050a0b1c1509020a0305090a170711030105010803040e0a060501050d0e010e1f2003040602030c07 77
    0x1002004104c001d450100c0507000c0600240d0307084c00143c0c1e802e80100e803a800140641da0108440b02e14201a20008500c41540039215200e0000784070822800070f044941568410091032060a5042c00501d50900840707402c02020300081c042030800710602c0c0300d07461281c01054048d180c5010242e0348070382c0e8003280e40000c03900003848004183d041c480614652101d120041f0b846000c60304c2c0000d82d4207092024070121003c8030300e5681040c2504802c100e0040741c1a034016052503c030a085010b0011401c29240100030020006a03500c80144015055920080507010b09070000b41c14030707020071f21520510010100029207295600704a02d040b0080795170240020341c1662800340007080c0c001c0008000c005a40c4400307042d18a65581083c004103448031401031500249041c0407005044805810204140c207001c4004600b255101c12410300d0a00095500ca0051002c1c032b22081c03010030148101c1001920a04030003643c2e40340210030600394031016000030b01041e030000025100c08107500030398001d16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 205703039 1250 205701789 205701799
    0x90603010b07060b12010b150c0c0d0c03080a18080616050a05070b040b0105090c0a02030906070804050d200402070b13060e0601090525020a110f2206120206041a09 72
    0x40903c040c5c840c02080e041140c14041c040a004201c5034040304029101c56043c21001440c14401d00804e2000c0f0444d000012a8160341d01e503004000100850054844072490b9524500c1c0c2d0704c0707802640b03000038000e40d1040f92a03400100034007901d09038103103600e5203003161410100d9540064031002c81e074501c500c2038058000300d140c5050000b045803508450703040318401c8a144640d5140ca240070500c52040000d4140036038020010004070b420600051301106000303007149804c140e981c40101d170f4401a0400116541d8007901c80581401c1e00c040301e40d55890380d05030340c00c508000306551150324140021780310440072880c0f05041c43c104807058000144801e0b80100783c601950351051000c024200984080f03d5403262154034081c0214074160301c0000350303440da004080088058643e0202c001e4641105174000c030802d41c404a003900c0f07100c01c1c01d00d44641c00d00110400004e0940c403c08440c415007282140e05a412600000769840c40d003a90240d50020703a050f1000015002441e0381846003028041e08a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 205704289 1250 205703039 205703059
    0xe04150b040906030219060f08040c030b2d0c0f13031707030f140910030f15080c03060103170d0b0301140a0b15040b1c09050303010614090603010b07060b 68
    0x400e04030740081040780d10035560540910100c2e61002c1204c81b20303004103000200d5804407011070350f10031005190858064111208016103948a0401502040f200c10104d0503243c402000046c400c0d49040e00348003c1d04001c1001c500300521000c82034410a910b180e092040401c0c2d00c020081c1c07e105c110000d5600c62100c80003e02c4100c800342e0a604085802d0340403402c98052011074a0246214040c0440c0d40c485891030309480e035041000d14200303091b202041540d40c1d22483d000c948940f0030380241913640c0551010441c40c0c513010a05d000d80a10803a0b010340c101c8001000000d01d0100f1500f074102c440728103162102c7e52003030408010030580d04065810360030408035110342d424038a001405a0410b600501c44054114240024007490000804110700100b10070002952110082c043c104001c0d84c0c81e61102502c1d25507a0140c032035400c4151000d40002004000a039045111410003d00b0103041c6410415a07800140c6103000511405810000018030441040f00a602017990880020002c0d481 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 205705539 1250 205704289 205704299
    0x15180b060d0b011701080d0c051005090304090606093803040c031202010c0e120a020303220e04050d0f03020d021303031409030a02040b03030903100c0813030e04150b04 74
    0x240c42c9681c0c189010604092121011000c0c144d0035034140c3da01c5000919800c01501021110701c905c0b41802e40e510f010f20781c2c100203024039501985010f60f0400006507111814204e01c01c007240d040c0c0d80700009002440c2020011580451841818110070082c2d100e0100c100030040b0042110250806034000300c0042000304103c107a51800040d01d0080c807045d14140e0000b103003030703088070423121200c40890451441c01c842864a001c0100040c410b03e81560036148855020038695045020011041900794164002180b4001000b4004125803041c01c0705501b400c0d16010740790f82d881e40c000402c100c1101140824903001c1c1d01101c0160680201c110354820025005200c94202800300710000313959207070300003c01403454040e114000f800038040c14000025608000c0101801c02400da0980014001c171000781c0d40604c0703c034041129003d400305665659034001400840c004114400c140038020303900021a0744030510440c100b6040d98005803818040d0004030140c55564880f274500000000c0c0861 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 205706789 1250 205705539 205705541
    0x60103020607020d0b100614040305031602040b0607060e0616140a05040e0117010c0302090a0b0c0106090c05070b01050d030c1b17150a0603050c1026160315180b060d 73
    0x204444059540c001e488c00c4603101d0040c2da104520011380940e2013804410021480100e1104800d40300400c0020388032418000315066410002c002c0c0c890036039608101c1140d0780b0a001042d170007071a10340034150b4600b01c14800740141000062443d0501030129030070441a000c0d00c100e902a151000d80c0003070a6030341321102024072140c0109894a0350030002d044a05038044c1c0240d44401000502511001d41001041180750300300003440001e03907489100020704d0300c00501c1030400c1500b10707a88140d51040b4a0400d00c00b0b82c241a800039021b181e09401d5840440e5111500e00111a4441da0403032200c00c0701081489401d80c140c02000e010b00759402c0d84181c0b000d00103110b5068144203103035035100f41d0350715030303058100c1d8050b11010380290032183d05141a864080d60303808542d14a82800c0031040707007544ca0f10403294101049100845205010b2061030307122480c0e44200b0b00c0d06454280f0141c48140c900c52860010303480f0b204540788400b00304040414040c1c100e1a09020054885501c500003400780c18 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 205708039 1250 205706789 205706821
    0x2060103080a2d031a06042912270c060304051c030f0b04021608160f060506040b040b0307060f050c0a050c0108090a031b03030b06070b010e070c0203060103020607020d0b 75
    0x311740b03030900034110040b079800c1e4014044d90040c1a42d0815240c500156580d41071101c50b00f090602880e07001500b01c030403102a2660b4462440040c0c0f00303203001540c040012224448040b00800410000b0000e0500000d498008640540340303180c90351105d1401030314015501410300803111300c040074020f602d64558064000300d04161030a0003442003650600080717120310f03081004907807141d0380c140010036001d00060502d6a0009140000c0f0b00c810744500c001e401182d44200e9175161102c017846170914281c0076079101610201e43c108000c04100780000e982c4c858602c110010310105844a0040300e001c0c4e07095950100c60354040c0c03190780c2400c0c035002d0b466955800a0501050707890340803804140000400000084d1f0540318150504581207180c040c89200440c11030815448103440136064880d0070141100500c02ca980705004e506191440c40307107100080c6020700700500d409c010301c0581c1d40001c070076045980640b209035481000d40045004185c7e040700243c050b0080e502030004905070f0203144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 205709289 1250 205708039 205708127
    0x201050405071406030406050c19051207090b0702091b0c0a02040e060907090b0d020a090506011706100c02030109060501060f0f0c11040e0c03070605071b050102060103080a 76
    0x30300d0b50243ca07001601c50a0745000c003502d400c400144001000111a507000740d800006604079903040c40780110700c2048240100400c0360020340e0200c0d580300705400d202030700ba8002c11a42007040c3c6650404004032a0780c000c140d4068441c0407840c000c107084089480c14803880c0070328095450b40d902c210320a0280d482c000c1000481c0140c0c680614860154000300350b40d40a81c1c01000034042540c07500304214080c0c1840c1c800300d0f0380107107407120f0b0324016641c840401006202d00707200404c0c5450701e031001500c6e8066550300b1101801405040250310b0f03803214942404150a810501111906800401d0061035800002090302c1e18000021641d1a00094480a91a07030360b602c1c04103582d054601261404000340e03000300488010319841041d45420740006203040d10900442d404c840101002924004142e441140452400541c0c41e05024103a401d2150820a010344000c2d03042c0360400003035640742d0500c4060000c0101185c92404180710701a9000030b8116a9000801e150562510403100ca0703030325881c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 205710539 1250 205709289 205709293
    0x31d03041e0b040501080c0d1e2405010e1002120408030702100311070b0c0702040c030213090209060a080c070602030c040504050604050601020a03080907030506150406050d0c0618050301020a0201050405 89
    0x1c0c4550550110f5066642c103a403580d5181d121224002c21a40194403150751142e214440040110307402030326160301041c21140440c1413010408000e03500e07441e2075007150650407921801c4c803060742c01090444404e03909441a80b034442d65a01e04a043c400c04c045080ca40740c1c00010005034096002000e00324250085595030041c0101c01410380448040e0516586904000e00401001c01e8038418456488008480d9440ca444101d41c0001d0407a4400041c0e440460380c04601081c01078082940040034166241c0210300e480c5020001484c14000d080b00e401c1080280c0c0c0010741032211800588410a510110070b640700d0400144132a9150028003596000307901c3c010010b078891030280a034178052941038002c1e220722002070710300311844080100712160f244209200000029810010284200e060505a1200f00d040204120903a0003a50195218404a149030390101d0038483c0c6500407074540742882903610303403640c10706a503a106e00c1d4000c5070b040d440800d146024a4041d00918811345c41030382 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 205711789 1250 205710539 205710599
    0xa030e0303040308040210050906130609080a03080406050903040f0b030105010f05040b0304060903200615062b140a05061201020c0a11060d0903110609010b090601031d0304 76
    0x16805580340000c5601a00055003400420b0150402030410000100f1914200d441c1c03604c0e040105000341d010b031030300c01008000410b00300000e0f0f1380001d090000d004188044c060b90003403a2002040c1184c041c0c40a482c480c0d450000c250181020021540201030b00154841c94036600c2c030003030300700b500240706144c0803e040c002c4200402e48076004660a030b50094446e2411034807151610001004004011800d1003094400c4140c15003098010f07011000703c200007017200d40b07042e0030b4165201d860410140d000780e0051282d082e03ca40700d0801030380e264240180035108001c000c00c3c0940070b4926040c00d450002c202c8410301000401070f40185100720b00a5840d04e0051211541d028201e205031040200c0c1030304010b04038000a0184034000990b858000e040d00d003803a240c81200411200540e80880105201400503010520306100941e4400c0040c0020000141014041400050011b140d241003698070b200c040c8000340c1e40d003c0047c107201820304503601c0b103454420107140c1003c901e02c00208402040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 205713039 1250 205711789 205711811
    0x90c03160c031407020f06130f050306090a1704030b0403030606080711030316030605040c0c05060f0907030f0503121609140a0504051914041e02030a1211060405030a03 74
    0x1034950302000360300d980c42e841c107400f00440c900040d81042e03408070303409400138114160a6903403c000d0072400380c1d10202e442c3d0042c641a0118203a040680c0168025003181d401c201d0098804a01c1810741900300550101286000d83e039440c0503c2190002002c1c2c3c05002d06000a155040e44520196012510f912110740c607607031416504000700e039094114035401080050401581c0c020b181e0686100e13400c020030840d40301c0c40003c00341e554007015038001400901c6242c091050812205400803160440d42001e403c2c54405640ca810160001800000b81d0040c10420001d0070011a0b4020b5010741000c20181015407200b052429035180c0e40c2d000900703005d4041034000030410000d00103000103001450140c1b80030140009448000c5c460f010440040306010244009070041c0003070522500107035200f0b85490b1a1400780d10580c0d0f01d80c01c0c6840203090048005803400034154042d190000b42200105425202c1121603900410b8070421501a0742d041c4410880004007400c00d000c01341d00e0a101103a035032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 205714289 1250 205713039 205713047
    0x9051b0108100b0a0210060305010905061b0412020609030a03030c0210060807151704080d050a0e06060409060e070f0503100e120c0114070c0b07020106061205090c090c0316 76
    0x142c40344071254600380010000207a621004003521000c9006548001406001860455410780e00c169050794541c0224410080e090080541c00b02660814201d402210440702080d4001c40c05000d020116042c0854159a94082543d59032000242203800112070761400402030081c8442e000054401c00c0081d419000e070346d002d18820390348803000a180d440d18115101d480e039882400c1d11400d00c00c0610305024010461070000c0e11032130203410480c1e80e450000c0b4960f000c480000f03000c0d8640524146003041882c0300800c0b055000b0074100c1b404200035078079043c018010702094200061a21400000290b40c5055102c900101c0300c089043d1901295440c1060061b1241d4004100c400d030041881050319a41c0e11015000d00c14010000003440c145280940303441c01c000341c40c0361010884d82e89859007004454541c4070b500445070303c001d1141c0ba00d04400039004100042e00100466254000a0a0740d88100003260303486800400a98103814800e000e41d03e81d50007602c88404e580300040c0341181e0180a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 205715539 1250 205714289 205714291
    0x602041814070503131b0902040b040e0903190c031106010801060608060307060c03050a12020f0424050d0b060c100519090305070f08120c04050109080c091b0c0109051b0108 76
    0x446103076106007001c161b0751811503d0007400c89a11003540000040360b214110300c064405410400900d0f9641d0303043c01c4e580140c03564010818140c0d80d01c10424440507101800e0000c8804c0894200500f04410a00c0c003642d1000c94003002e40c00300d00c41c4000002e417100301508028112500c0d0f440d401c10907150341050581b01c03907542c0103540101e0b8092000c04002482a4001c024960705440c140000041885580e01660f00a1030003041c05000400d06006c1030718200c8080000d2103d0046c0b50300494940b207801f510034090740c3c021400e410b94508500120b074681904407450b03104680c00b582c44030103a9601c0c42c40113103003c0d20310b0503c514401c45c05c200c9800e000d104141c1642d81607100e5608042c00c41c2d48800380840181000c480ca400e050000c41c801208810383d0a00030348000c06059256070402c0d000421b1030590ba0310025055100d4170583c2982c0e200c140403103401000b1546104034401c1d2080000d002031141004c0c0c03a00c65032906007880144100032480090968190a4903005089500011600d0b410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 205716789 1250 205715539 205715551
    0x1e091a192c03032a07030501090b0a140a0b0d0204050c030406110304031d01090504050f0109111206040209010c050d0c050d1403131b08100b04020a0c0f0602041814070503 75
    0x40100001d880219021a481421030b07044507124103c04c0844d041e480c00c2c11003da2003124030341c0d142c1c00d01b901084440c81c0b245034031030004030702040100c00c00300319070150103005024447c50315610004000c054440d440d842d0030454001e40700b4001400d04000c084000d900440d01600d041c4c0c80c007400c10381d0822200c01143d01954050707841e6044400c18070490584526030040702d81c10700411600000706c680faa0302941d1700c04c41d002d8040d24034a42c50010207500341c030402c01c0381110364002000280740801c411050300e50005000e540041c0c441c480840141c980e1081460094450710510311060305061b44024200425803007442551048503c1e02c0c0f00342d820781031004900d818190b0034400160110708040c0c401c210940204602481c00c000c12140c00400003040d005007500e40c000582e43e404001240c0134820000b082680d0861905000b0740d40180051660a4010007110380034441d001841800d406a030090318007000d4440544040981c03400c028414040540e01050031500040c09403400303542602e02c0f4075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 205718039 1250 205716789 205716793
    0x203031006030b1e0a03060f02071202010c0c0b0c210a0c03020405090601050304110901080c010908061509090c090a0b030c0a050105030c160b09010209011e091a192c03 74
    0x5095012010301d400e098401c00e8109411700f00c0080403032000d0007000036061613082d00681e04d240d20300707219203d050500c403e4015603051241c222041359200215141a0750001291095616481d0850b442d5108021030b14100300b8031603525590000c030280c541c5001e400071020410205000340c0c0260300b0f03801a4031656610003001d0b4000745d015400380d0025076002c0d10803100000311045020000d0802c807030a0308403134419480301ca01c2908a5170402040c0c03004d0b00c003030030040801f803901d10000c1500301c0c140070405016100203800701e48042000c100d240c0c107048005006040510308040c031000100441103900b4481d00c00d648955004e42006c4d82007105848040c0e50300c1d0300e569101d800b0f00d06294071a100000c081c0000203001c102080d0846a502e015519860025948101680005103480324108000440403100910304004640100012013120440d141400c00016030442003029801000c140f407101c580c040d0000b014069008900d50301e00541020700742c00e1710f182008103a4a6942e2005519091307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 205719289 1250 205718039 205718059
    0x22a060906041709060d050703021b06040f0f02120703050a03081614091201140a0e0706051204060e032208280f0c030503072904030305060a0906060203031006030b 72
    0x640704460040610650191016140c0000280d00900301d503000c90752300e000681c2c081600c0f18000d0b0b15034040111034882400078541d40c01e048c0c43d440d40d20f0b04c3ca52001481550030242403c1151159000c0140b00d640d800b080d5402c0544d40d080043c0c468040b07e0301280050f06000c0003c040485100e4050721100d03890356000328503108203440c03a00b51390240c0c07423096100e0382104502092000074040c800000c04070f8000712000741002001c1c0c0702a03a0000228400c0c0c0c2e00542818001d00e40d001040d109400a40c0020301c4141e01e0b1401d05900a01403040090854040080c40c403084a4210608500360f454070b1601d800b11a42e6424004d8440c9541c501942080300000410806089101140080180548824050b09c403140e61414a8000703150b004650035003000c43e0000901a01a0001d000f601c4074040c401219000800301840c40e8a0040000f414541d8400100c2c02030740720115882d01800030244100130154482030069540d8008403441e01808540200202e0aa03100740240400d01c0340262100c42a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205720539 1250 205719289 205719323
    0x11118090a0608030417071a0703030504060f020706021308210705011d0d1206060c0b070c0803070c0501050c04030b010e130507061e0915050c01022a06090604 70
    0x1032400c01511680245440d91000326140200740300500040c480340b0304c900c000d02c140410040c1007a0481d0301400840c0300f03000743e80314100400c104036120640d1610f40044c542d038642c41d00390014040943c00320070207032000c19547c04100d11a0f0041482401540208201540e642c0e07034686e54401c0400c20305482c4024003030100064442401911030780e80f042c0d00203c4d02000070380005a030101c0c81c40614506601645043d41102d4000c072030701d100d514514030288010342c1403282c0500311043d2007800034039207101341000030b548512440c000d45d034560303101402581c0c034280f0ba0001080801d11400a035459464000800c1014484008450849038816210322070381c0c0c130380380c0d00e10314164000b0070311011000015071100c000b4500f40626005022140c803454641c1907a8603060290310060490302c0144096803005010480803c2c4100c411420700d40340c00c5688901000b11240640034a11040c0002e8000f10034010700074491508803c07580c00704c8001c44001d5901c1000c0d5545e41e500948026019040d14004049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205721789 1250 205720539 205720549
    0xe0610021018060c02150a020412021c0510060f05300a0b0106050424140f0405040e072d050906010c1505160302181003110714011118 59
    0x10a007400b4a0300c0504a0300b0ba03114401601c8a450100c2c0060f00301122940c2d501e031410b00b03000c5e00000d080104505160408020000120442c100a0f10560503a46140c0700200c40007010b410469001042e42d000280209403d07000d0071890166a03406216681d001c5800e05001d00303200881d15204e4080041d5100d84025201d401024210a2000740201c11241000c180d1203002c42c0d009141b9030b515103940e1842c1158444000c0d401c0c0350204074910141d148208400d0340b1400000003c0c50b0521266a52180c8540002c01072155034809600141059501801b84201195003000c6600d01c81c0f0010f0541d6828440340b034103441c60f04090100f0419514280300f0383c04c0100e0075030341c0301006041c0035000464548800c1c00c1c0c070020840d41c0c0c400302c0c2c690081042e10030701003001c084906424242942000040114402058810f03035105019481c510500111540b1a07080400c646050041040c1d4482d51f40c01c3c081c0c080b4510013009880b0b0f40c04c194104201018400449100d481c00b00068206071004104001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205723039 1250 205721789 205721801
    0x604060908090901060e030d0e030c130b0a0308070c0807060c0f06060b070f02010207050102031e030604020729061905040b0d0602130e06100206012c07090e06100210 73
    0x5180d00700c052100c5105903c03004503003406001552142040d030720035002058580502a03c0d06010000c814842c078445850000782c5100c0d0b03010031140c032050030040c80c403c40002e1000c0800e00354004d500040c000700303001484004000e10750007031107414003c64540895654030500c901c03035040028022030301c040105641c10810301005101e07420200340d5550f2500542e0721350b0041c00301a584100c40c5801c0204540e0100203140050101b8000345041c03080403502d00040115000d48036546580000000301640d88942c101c0c1c0011f50f0140040302100c18030110450f40c9003003824a0000c400e84000855010324020b9590451800c0d800e00354010242011700740405002004101ea40102e01c100d05800005c005002038003103042d00d0000e840315540f4059489680860182100d40158244c4400740c0c881c41e8046282410b40c1c07600d0f804680c0c4451269a280d08a40f080d002104000c1c0d83c4606002c0002d911030382030000c07034038000c007a8102034a40800308010b05d0034410106e005a41314001c0b40074a90740c2d9410078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205724289 1250 205723039 205723043
    0x6140d15020d02040e09010c1d100e0907020307051501050609012604050606011b02030a020f010c1401050a0b0102011b1d04090b010e07080f1302060c03130503010f0c0206040609 78
    0x3500740000903540b542030740c00a4100900e0381c1512800c0041d940424403480822502614101c0b10460781c004160890100c14135800d40115500030306449001d004000c00111140b0150900780c2c240341c00302c8025144d070811700c01281d0310300a803110181c2c1c114078901121306a407001040c09251640903801507803d4101440b4000a00c00207030b261100002c080e9060760b2050380282c01500031450110b00050150760000078a124170340441d61600c0150b2400a4508040d0340c1c19126050510402001618030402d450304c0109503d08a4400380303004c80d07040d00030300e0040800003014001e0301e8807200168240ca2040b0f000406a8050b01840c0071090b2244014512000d03d400390000040d51110100d4162041083c1c1500c0c449481307001040b03044c1031a15020343c0522a460604924104070300c035a030844401415403454010800003500940d40d58100b2180130140010499603100d0164142c007003001400d202d064400e520b400003825a6050720300450750701e249590301074509540c456135004000d00d208401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205725539 1250 205724289 205724291
    0x90e0105040c17040c030308101d04080f0c0c09010609030b04060c09150206040b070c050d050c0c0d030201050f010b030705040b160209191a0a060e030a06110d06140d15 74
    0x350f4a1058002c0522030b01942c016810850a5030440c00c000d0911440641000182189007100300300784071140c1d0050311401c20451100b5025180c0d403c180d0014001d01031101c04111000071380364000c0e00c0c001580b1164100590b1185c0403aa43e94030706555503c4103200180c41d4006e001c0029002a178198410001400e01c2d041102c001e035103c800e0050403040072400e420140e440746090100380b0648000c11603000900c0d103441401d01855503a181d032a00e20403c80c00c401e004010030442c0588806000b01c00710200040c2550780503004600f0001c0c06014181c80501d9141141d00000c1440104401220b00c6228184c8400d450613242c2084451182d12000c242c0c51040003400b47c01c40180d4400f18418090000041b001d41c08030124070b9264101e560090f43c1800c07410b8449070043c019120a0400e008031801c60812120020302d00c004a170801045900003045c041c901108100d40b189908090058803e81c40e03004c1124645a050f4810391140240380c4950111041c480003001810440301804004041d0308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205726789 1250 205725539 205725557
    0x12050a14040f0905091c0f09120606030210030905191505160906030218011d15031806150d080d050c0d0b030102070b06040e01020f070f02010f090e0105040c 69
    0x2a401e40140c1c2158003040c00c1c000d41040762407000c0c01034a070132200c00c00c040d0028007a2940d03001148007160b1605018010318061459413213000b00582801000841544082c0c14010714040c00100654002203110b42e03601240450706500ca48180d1080030b5000006020446d9090748024081da4000d00444281e40241b82022050350a0300510307002d0040c950600da1076114002c000f4010400f03d070454020140305002ca40100e4404048050f6040001e0811404c00c4105a030304400203501e42600c142c210090350380c00d03070400c1c0403100298841c0d40364409100603a412a900a03450705800d542804250100788a80402407900d60120448144100051486c0246001000e010b481c01114031a0900b2408110310a4589160089060300f88044000b181703080341e00d5460b040c9038103024040900032a0f54005000b6600003d60480ba038129034241281d8440300149003040141e141240201e0000301c0703103500c040d02c0a000d1a907940a807100e051040e40e86a0900f002d001c010101e25606a08001c1d50362 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205728039 1250 205726789 205726817
    0xc080306030f010905150106050f030408090604031e1205090f090c07021905090105220b01021014100512030307031e0c050c12030702030702010c0204111201080c01080412050a 77
    0x1200344d4186510035006003c0421080c001c41e4002c0c18141d20403c184541002808208020a402c41754001c0c0d100902e2070300c401e600c0010481c10f02442c0c10003800040249880000940c41604000c038451040e09103c2503040000e90480d150301234011443e401072451169482d00b480c080d44e0142e8031410810071182414155000210656000c84e03484807074401011042c841402c1034600d20340500300a61310202c03c2c02e41c00c44030056000c1108080d1482e030340d0b01c01c90030100b07a1090040702200f10241105105100d90a00c0c1352802950a445020791500108000100c1d0b041c207001d9020101c41d0507015600719600da45c429005000c00c4108015445035501c2c600451155521601b81060102e550389600d9100b290846440c2c0302d031004a0704a80c80f400c0c010480410340c004111080254280f0f80482920010b102040140c412560b0f01c0640040101c4c0701240e1442c01028581221304100c1101d0b44180810015500e95400751000742034064800b000b1031a2501a100a1150341085e16101e40000561 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205729289 1250 205728039 205728041
    0x20d060e070305010911030a0507020709110a02010e010c090e0c22090c1d010e03120a08040203280f02060c060f1608010803040e04030504080715030c0f0c080306030f01 74
    0x15000000c500440c4400d02894030b41c0742c46403e0161144034003c10041440907510b0440340030040200950310303100c070b00040d034440c801c0c04014002c18240ca4103001000b4040f0006610380c025148000040d0f180c1111070f05000c905010b0244c1540d40c40e16840e01480c1448a16140d52000522049842908000d20b50f500c4111400d2a030441c603006102000517810005010180c904141420007045070021902260481e00c4800360400102401c00c0ca54401e4041d0100c1d0906c4111072200303000850200f4100c0c03c10303401038a01ca214602c22819074000c4d110140d82210300c44e0096544179500341d0466803800c000b81c0b0802884550b10300040400d400d0003e120000d0785801c0c401c603640c15032225044140706205035100c4032802c0b1140b0f03c0c24989540d6051140b001c1d528016407141c446241c41400c00300e401d05002c2d0086030060b099506c1070310f000c1a2222010300815400c3d400f09000249003030304407200c84c0d100d051410301405960355401c04041d12602c5a100c541c00281c8015814041e0300c105074031098007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205730539 1250 205729289 205729301
    0x30c050f0f040329010501110a020a12050606100f180b160c05030109020915060403050d0f080714070311010e0304030b01140a03031209170c16051e0f0301020d 70
    0x365620582e03685040d0701d004480b402010700103000d10200d10f01254041500b401c102419600203281c00c400303907052084a01e160030303004400650016103443c400315140202d0113510440e640900c040b00c13840d440f48010310100c02d60720300740000010a48003c2e92081c601c50017075100e802c414503451485054a50140c03000342e500c6402007240701010318040b401088007810f980401098100c00070400031a8980200b5580e007002050543d0107105030b64440b41e1075890005542c09140c0144c21540039501401000d80488820300340780b004201c43c0300001e83c000f8810403010000c8681a2041403c0c040341e9074055030503030201034100c01d1554848808500340e002c1040a04000c500a00d04a283c0754900038100700305500503a80c0a0003109009001d10102c1e400401d04141c00c5002c1b140040d4416031814600c201d004c486000c0000303038100044010011000083c1c1a040004152070114000d50f00c070104001065402d5800008424802002d081da161116912485d49000b0b40007601c1c002074807400d0300403244 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205731789 1250 205730539 205730557
    0xb0307020c010809010b030307020d06060815070201152106060305060a020901030e070e0f0c04030209070503040b061807050c1204080d091401140d09060c03050a0c0e0a06030c050f 79
    0x400710580e41c1c160340c1d21000f110f80140303d030740007000414a8400425224032880a010b03015540030035408040201c1130f072114004007041000e882e88031050b51140b004280040d140140107600f00720340c1c1c1c42c00070300200c002d83c00c6841000a410781c02c2d4407040685000c056412040d03817000c0d601c14000000c1a82031002a1003030a0003000181d51f004a84005002c1325590356070381c0f00079070050360140140d0312840720094012400646180c1250340342c01200d0f40a01c595080250401005004e1101450700400590701580c131501005495a07508030501a60f01e0303203030400c2807034122400e000c10001030040c001822041d0b08601a80c0f40c0144110b47c0800c1507001c1d90282580b54171840202030b54a81c415004400303001d028050f03500c40c0355003800080c00d01e812000e032400c0c1c640001840c0900700103c0d0b84041b80c942d520042c03e00c0b600a5456016000308002c540c80f00700c2d40d040c4070b01031260920070144070307100803c003e015010460802204074000c00050b94503c00340701041041c105151107040180011132 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205733039 1250 205731789 205731793
    0x2011803110a080601030b1f0b0d141807030212150f0106030e06010b030105130915140702030705030708030604060b031609060e01020318010224061e06030a150b030702 74
    0x7a800b03214520a8030f5100c141c40c1e8011800510003d90f002d0b481940008504d000008000c05108003903110125580c001d003100d400000e0b0780b10300c4441c1e41e0441140d9003c20b0000c1100c0340c1c0e404261a1004600342440c24050300200030600041c949444090315421558017254042520240a0106007105492a100710300e10b030f400401080b945030240481c49070303141006e000107524144001025020602480d0310412a14a0450170444250702c91082140c00041100d000d004001843d0014826800028902d0700f03030000041100b400001110001503002c0001c51a0113815111580e280e04042c10080e07110f0780b80c01c0005000e40c1010041c40c010241800c0c030800081c044040940074801d16800003040c021b9014001740c59a03000f109842001c803030541410400010706004038240070066003030114a99070001ca00c0382c258604c001c12485480705480b840e51001a0722491201c442e551008558064800c0002401c0c01d03032140c0007280300d031500d5006c05606585642e41e0889941040b20004016 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205734289 1250 205733039 205733063
    0x111c0b03100917070b1302031f1a011103040504090c08010e0d08060108010501080a09061515110604022805060a08090d08040804150e0310020304020315010e0a050402011803 76
    0x8881103100442000c441c01c0030a504d0110707a0b5075200c0705c0c0e61000300300d0344109000550f40000d548003441082a09140051184802500c140d805001440310842e51003145401e503410785580d5004442144c200c02c0420011410289000204005030100030030884000310b40840006d01107909000382500000420081d1014009000c0c008110a40c0240214104010b540041060fa6040030070070307070071014155020407400f0003410440f001e000d47c440e400f140c0030381d1100c001901816421907055900038036034850101340840000140e03901002c0c0c0740a5402080c0d04840c1401b00f80c11070398001d8590300c1c1c0c415407465996030030004040f50810344480000c580c40306c04000a1003000e0144006080c5181042101170410703440d1074070103008501074009902c05200c1d403490319038041d01d104461000024102d03a04103038620303038034000f039001900d04038060711668009484111328041c08a06940140d0401d8485a07115070004010304070160050381880f0809000304911004981444003540c003441c1200d100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205735539 1250 205734289 205734293
    0xa020409240b09040303020705150c0c010c0207240909090818030307050a060b0f03030708130b07081c090f050a05120f070b06061b1b04111c0b031009 66
    0x95801c04400440c09140c080300644550700c02d65407641068162400580b204428a09607280a034011442c00065844104100304600c02c0c03401014081da036400244410080c00710103903640d520038000d0080c403840b40301c00c400c020b02403141c411010300003601e854502e1580e50681c0c1000c907140c81d1802d071074035000028034a5801441e0340343c901d42940282d00444c039115003521a19240c0201d410003c000c103803524850748582c0c0e20300340326000d8108000d042c7d07607440c1c20620b007103000341d40a5005040203e85021001500c80504429140b03401d810840840c07920103182c0a001c0e082d59650b08000704c1c15030350104c0c000420794641c3d450310a113100c0c03070040c8030485142c2403441c038044510840348c529070000c1100b003100e22110300c00c2d1188543d0015000c8015210140090303903601540c540c04803e10311000301100010b5000521010203040503010001c90361680c0c05000540d50a20210a00000100f040141060700c41445803840c131441c1c64000b52843c500700000382050754903111500b403da220000f00c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205736789 1250 205735539 205735583
    0x13021908060f06090d150f0e0f0c0306040b070f021e0a03080f010609090218040908190203040b04140a1509050310020711060307020312070c050f0106030c120201020a020409 76
    0x300b0a0b0031140c080c20800ea000c009104405040c400500500f5071200700401c0c84c4443c2c00c455088852080144824011181d0042da80c0640540362040c511990550130400e04002c03a229008907008100c010243d52008000d44009480f607190504510032125412000640440011282c1056002408603040b050400608011010300303900c01010b45000100142034001982200320384a034100580c9803110020340100f41602402c003140c00c103061001002c20811400018206104030700c203180ca00d240c040c07400700e035a4022400740140d140c101700b2090000001a400001030140010f1000c00c28640ba07003240c084410000d01420042140b0183c14041e900d41400158005411080210b0520b00da41c0c5500b11039145a0701024001c0200101107440a40f0a104645d81c050555000070300c40d040ca00d0004040140a41040d608c900641110400b010018000c03042229003098a0054003800c09088421300e1004a000324150b05c42c1c0c003480d0340140c46501810752206d008807480543c0302c039004c1801c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205738039 1250 205736789 205736809
    0x9211011031e0f15060d050109060812040b07020d02031c020d0e030a05070504020a020313080c10030b1e0a0e1005090108120f07020d08030411010201291302190806 72
    0x321080ca03080d01002001041c07050f03419802419407030006150071440d07011405a1060400484e8418101400414100600d4000e602251041300c121080020a80880c0000e402180600300e103107802004018098500020100b040c580020190744800781100580003004603031103c100051780040c4d16001c2017903040000c3d00f80c02402074000d42000c20341d5542d541d0700c034840b038025180319660205070100e41c94403c001f0340f07d280010003020040b260f1200110755950403010505171080f0150040380314111f2107130040441c0c044024051110105078100f000d0100803099860036040363b03800c0301c0014220b149100d420300030741c03c00c460500d8890422040c0f1003041170581024400b50310000440f544101c40b9412600c2514400100d151980d565100041071400580b01c05008188044240b00c14000d07050360202078950260003c218117026140c80100010031845c04030101507208030455142d00707040c2c0c0440b224040c100001490701850441c80210070410441d02d0b80020002010403030b1a0400035408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205739289 1250 205738039 205738081
    0x4060e0f04140f0a0803070e06160213091e0201140a0305090601060c0c1e1503050a05011406071e020a120c060c11010f120509030904110921101103 65
    0xa031a0340403500140135503032008100b004000c0f004c0040000d01080c0300ba0f803075024014000f403c0d5a82c4218451031031b51304100d00c0d00e0580c41000610f283c10a600c0c4203100c0c00d8141d5030b0045003d004610000c0d546410041000001d0781481000c030589142c009001004040302c000301d0300c1c0000c503424030455940c03070b080050b088101070120408000b4080b4002488040c111041d280300c80a01441014071406204110741c4807008240b0018140095150940c0109200c0d08103154200f200f41c0c2da41d241c02e0b201c030111301c8800e40c000c1420806800456801c1a284060100255240422610f84c1c1d0100d0102c6c1c03d030390711601c80803410818041c100300100d0f031074400901480c50b01e0058401c46840c5c9442200c0c074107800e6130500c40081c03140e903000c07400f840300c0c0c4820080303403c0304108514000380825241d50100701e080e1700c180e10b0070382d41c450f00c180c20344241e440309034000d07001c130107009c4915920b003942d007001194400036441044846445204180034000300f681983c0c069948a080640c0300000c004000f0140d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205740539 1250 205739289 205739293
    0x110a080106121407080307080a090506030703060e150f01050702061303060209120d1209030e120304050301060f08060c0304080c010e0705130507021b06070c150f05070b010303050904060e0f0414 85
    0x7040b40690000c147c66a00b508441a80c1e991070404506845441e0300d0703480b0f20b40105010ac100b06c000b94040d88140120303410714902000a07a545036241500d4211001460791011559014036095407085015060040c4040c0010f40f80c07828074240e1080050056000321111a000201c05415042100411845000b00d0380242222200c2d00d02c041c0440c00d0344407612813080e03034469024040c1880703080c1e003602100000d00300d8010204c403c2c02c00c07a107a51003402918060b6007440e10000c0c2d041c1c0307084d0340300040b501803101411041d101d1004604060340301a0056070260000e00501216071420f11405022516840080901e10310f031009205689184501011141d4504400c10101540200b410b200a12407900101c8422594000081143c02503580203003486028103000b0500c217400f10107007582080640ca500d82e038030840e01803c452503c0b4a46004001c041c08000400c00030380603001a000c1e8400080c004180b8a41780d07412040c100400b01c84030000030a540d8107200610074161380a580b40041100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205741789 1250 205740539 205740553
    0x1f1418010b01080f041502070b09010b0a0f03020904080f0403020312120109050408090f01050d0f0e07080703240f1107170310031506030b04050f06090613110a0801061214 75
    0x400341804004c010000f03003c001c0079040c103c04000d41941100c4000354081c1c0c48105c1d90800d407014034001c010480c00c1c1e0703000c3c44000d074010440c107101d80342c0030b0101c03640104080c40030398980e6280300188d0003509804051000600022005030f4040c0a00e00e0380300300c050115500c900b42d5800ca105504410390148117000d203024284400700b004d10040311104a800e460840f032151101004807514401c142984881901d010b944144602030340d00045202c03888102150b0f507007a168142e85881d80c01a200052402c50201c1c00d064014104c0c0c441404c000006100c0060055150381e4001c068400320302e04030304c0c1010001441002c1149a2800c7d0200980607007144c1e0a5241c01400031300c500e041404080c10160150496103000c24080d0011405990310020741181c504103171900c00da40c1c80036103040d20034034054103000130039a040000e80240704510f42e8110381029502519410442c0d00c095000541041c0c02c0040440c07000000d0064034014010429031011000580c104441d50111004490300141c120300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205743039 1250 205741789 205741801
    0x506060703050d020a1715010e09060901121104020d02030910140105011409122109010e1309050d0807031401030206041a040305010903021f050601021f1418010b0108 73
    0x40103840c605000c00c3c0f001a5181e40c008015501c03036101400700c1c2c9040c0703445c0c020400521840e8a400082d03030030030789a41c804031a00c0720820038203080407615903801251000040003061280c61014080c540500b2403542480003c0d40450240da002c0e550420445400005009032108100600024100d01120411100d840c403042c0e0303107080340107114080c10005030352132440041d0100d40c200d889045009156244001c43c454000b51a2051803500710308409803038a003a00314000b000103c41041c1016074607441041c80860030003035501c0d03142d441c120035196205100b000248082003468a018801d80b01d004242c03801b004002c00b40da08442c81a0404141c4000420058450105950580d4650710780c00f100010f0410f45030446024030b0703101500b1076082418500a054010a095140403c80751209005808418812041d2002541c1140c0141c0c441e417452600454a024011000b401e030080c003003082e07011401c44504144c4250b985070244002c189920300140300074410603007010401c1c01c01310054a020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205744289 1250 205743039 205743047
    0x326040b040809012703030e011809020d1e0504050d051804050a021e040302010e04021c0504020301021603021510081b06070b0a0219080108030a1115040f05010506060703 75
    0x41d0008200c070300089524046130780903031a95110812000f0248800524400e401c612041040c481940818140c100f940e150754031818400341041c40d001c005d910b406103022071900003903008508070121955124100d40ca4224048281e0314840e40510740440c8a0a10b801d040e810042e00303406610912030100401c0c0e061107000984502c040b1411a070002d5107984644500e03029108100d44c001100500341c80a192001c061070150040d40d0007a40d95000150108003400128403034070201c2d030011041c0c0302c10300d00d55017500c1d00655401440034001508154008107414214480410100c01681025030b0008203402c9061039258072000c0130310841d410500d020080c40d190008601044103801c0708070a03911180d10303030700b0407500d20903030040c004541c600c2c00e002100004d4001d00007200001c8190094550310707070300c2107403e1b6050751008806945070502d44103040c0c403080b0030140f4517007050048401d56204c5440900119100d140280c000b40320300c00742d61a0080c2101c0e07004004503c40c000a00c40b99010070383c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205745539 1250 205744289 205744291
    0x1020606030d0305101508011401050405130914060a0b09160f050a0201060e160e04091221020307051306140f030a0b09070e0102010b03070b07080f0c0a0326040b 71
    0x1e5400d00140503100c412001844c038030a42c0140c0c200380c14500c0340081b400d910a015a0480380c10102581c2800c0c128030044804d441644a0704c0e5000f42c144850500802560b03000e4a5024442c0031860202c10700c18600d141003c808481c0c041c40240c0d038201c280341d40c1c20040c2166a0200f0750b900c503d05038044140024050070000143d01d400c000d00418211030860003540250040d101c0414211146c2c03502070049000400185200300010391030740280180c0d82031500842c1c0c0200d503c5112490030708007941040364a85a0144d0300303001c0b800030b0840b0564190312440110700800351591560b56456140300d50441c640d9856000e802004082c0c203890002074141800d40d40d640b901c0f42e080a0352070b00c070395402c44080c02e070419007141e100c10b5010602180b86d4110103444621107080e0003d1150004d15002c040c0c07141558442e0000303c0c80c04211101c00240100002e004001e900c5000c01d080441c11619a0725201c144442100814000300003103010f0151410300c10080c5680900303400c0d8900d0656600300c13100d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205746789 1250 205745539 205745563
    0x705030301031707140c12010905070e07090f08070609081212040825021318290a050105150a020a030c020a120305071104151a16051b0102060603 64
    0x1201800014104140e442240c0444c0e4022440c1d201a040b200840c2d503c034041c0c0c4420f540300b5920901c511030300f01818018100c1d01a000b001616405207080b0714008040f0009003498104905810041195882121200090200500180281400c04070701400400d404c0d00108040c0c1d01c600c0088a40402040c01c0340c1c5160401520b28000d13407100d10300b11056000d80503c1007155080306155001d80203500307407000516802140d0070718400ca501c032101d208888030b45144000c441e00c04110314010600c1c030042007014588d02c0503511600700000760500f4400ca000c1d00da009480b92920b00400c0a0301e46107203900c3d1696103003203401c1e03d4144041c4010350307101440c0d03000600b0301a2503400b607000d541c3d803080010001c0c003403000340c0740c0f40f4690303850002c1c065030181c203080301c4100d0740341001902d030305183c400c81c20710f54680c1148034000c42c1441c8000e6101180c0d9000d0b01081c0d0800c020075005083c01c0c80d14120b06d43c0c4184004c1003d6502c00581402001c410450b041c1194061406c004140d40d0025000440d05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205748039 1250 205746789 205746803
    0x60204092307120908030f04060506040b0d022202040e01060207060807120f2903010513050706110330130209010909050a080a05090a080f07150e10030f0b0105070503030103 76
    0x182c51812141c044c18180b4009804401c000c000c00c11198200744425120320300c200301c200302654901c410001214451071204d50010342c002020001230410803040b01610825a048555001e9801403200c281d90103908007034003c64608004004854041180a001e03000034107244d460740c900140014091250350340d010501a80b24004131001000a078003000c0100c1030310b480001340c403510f141c110b03034030100344403000340a90f10f410000754080b41c01c5a0079150302c41d8480094082d0519003c1c0844440090100c02401404104600d03040407003500c030300500d41402401d0046105031200f4690b15460070051200502800c440c020b00c0c0141d9603902ea05054940707000c000038a800d00c0381000c03841c1c00c0490400a0103c4400101c130308440d47c1010240040d25411100d0303484043e200c0c14490f880d05400c080c41c0d0302c036500205080c80b44c44000302c4409480360192900104010070320000602805003946803002280c0d032210310604c0030216000341000058203091544c900482c41e6600b80d900d00c01480041c16003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205749289 1250 205748039 205748057
    0x1b1d0402060c06010f0617040b0c0304150e0706030c030c020606130e010603060204050405070207062f16060305220b10030209040c08010506120309040b03030c01020403060204092307 80
    0x1541e5038001d070340148210b50308690041d0b85582042403060428080d42001c030305500c05003114007841840480c400c50b44015807948540303038021a90350b1908080e1003102d0400e00542907025070b42c0f00c3d216030700406444800918030140b03051070180c12220358003070102c20075040402c4090815000201c0c10380289003510b07011107041000c0039803801172000030020a130b0741d401d206000013071110350b4000d072007580e004907810082c0340c0301d080c0b090360f1707800203072045901180f039018034200c10042c4511f10001144400b070401000c50f89080c1c00600f895281c140b802d05401c001c0c1814400d0701c0e4117100d1503030310868071040040010170448152181d9030410000505403000c1800213a003005014115038002d40e4003805510040c140f0b440c0030080100a0b0150515a40c44c10f0005041d5142c0b00c404a06941c41034400f80d440d101c4a0010f000141440780c0d1055014402041168109002440280002d502980c401a240d82c01d0104075000e4440910b80001d4800001c11000c82495005900b1508050315040079540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205750539 1250 205749289 205749293
    0x1b030c020928020405130606080a0504050705040f1a0102010b130e0f0106032301050c040524030901061406030c1c0b100305012603030601110a050303070c1b1d04 71
    0x240203200807240d20460b442c440c01030b81c01d00d016005801602c6044440142402e01e4920002c21600b061203010000380c002c1000c9800c5100c527070b000a4015009030141e400c500d440300f01003000c0c2c680d420302c48410541d032a00d0544180c645952241d65801092009000340c0000000040010700c4c45060740c288165207035204007010301d041080c0072010100740004d0008580c2ca0500081c1c00c29242040e03541015003d4040b2940c1006201c1d4502c00d50020303a185091078100014080200003000c09070a000d4928020301c001804810061841001e03d00008900b060401000303119690814010a004440500c140002c4a09240076640110400a0150324901c00780841d40c01418400d025030781c11507255049150107076419004941031320000c0050012000c491403120031141135507045000c150304144046180ad44c81600c5101410f03c807101200e181e040c0e60303200e9908540c41030b206c06000c104541c000d0810090010580f0b02c00300f4203122030a15240c40c1c0f080b52440c2c50800032145028061590020b01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205751789 1250 205750539 205750561
    0xe0c0a09080a21050901090311040e100501090b1c0605040201260708010e060d1205040b1b0105090a051009080f031005030c04110405040203040f0f060c1b030c0209 72
    0x3401c1820031158008414180600b00640820b603010b142143c070394180182034040c00c200c40ea00c01c810381d41c100d00680380d80ca070288501d801803404d43d0b100703403030720200b008103e020401401d201905040005603949492001401c0704c90358034030b03640541c454501c494468be80113001d00041542000f4041807560703c0e4801201c01030211411021121046c4960026000801e022076115244584503202982d03250311020181c0e80d4111000ca81c000c2d103812035080025200b040c800c80300d0a071410310760f040940710003c540841d00f068240b0700c0200c0c089605408c1400c0700b401465040240000a800c002130203844458031244c41e18540c0003100d46074492941082440002c590350721404d80c070526100c0c00d0950b15500021614440d103442440b4203440035901346002d02c604040c6e400701000740c41c5010724002c1031101941000704240c600d03c0540030310501103114002c0d01c00045128050001c0e0007405c2c0703c030180c0412030088070b4030039403818495280c000035000070101c41394940487d43c010b131640da4550009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205753039 1250 205751789 205751807
    0x20d0206040f0218090f060f010e060d080405031002090a06050a2705100e0405151e040e031303061a060306011b050d23030f010e0a1116030314010e0c0a 67
    0x4c18184001c0e81001109100418155201c2c0c0c100700548650340ca03041032494480a080c068110120210800b09080e0301e0680c5030714001c107200b01080d90816681e46c1c0000c2c10540b01c0e5006044d00c1c0d4000442e08003501c0c100f0303200e40180080c0d087c130718200b000c0070f031005099680c5d4107070001d03181c140200b1100c11850322034000002028000c2c4a101d150700c940d20020443d0050181060040c1e0074903000ca041070211003220488194050449103145564400041060381981140b6030450b5440721100030203d004d000400c131800300e2082c0b41280900c0c52400404441180520b55001420000c05000b280d69050880750442e1003442d00c20310381505c0c0b0150300642a00404004c15a10802c1e44058003541c000000102040b900000e960000440303807101e14291004454404500761184c006200030810170030080d4100d43c40030000601683c0d4a509445aa800740c00f0001c58404114100d404160341400313041200b01085003842c0555142c03420400d048040685a494034070300118144038010b110320904 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205754289 1250 205753039 205753069
    0xf020f01090305070b0f0115030903110d03061e0501020c010e2e020d1d090705070b0103080405120a03080109020a0509030601090f0b0901030506010501080403050403210f020d0206040f02 82
    0x2007180c1c0ca4103107009001544002012103220403d000007031180f1582d6505107040307400b000c200c9040c60411680032801000c40e02022401d00c84031201541c80d040041141c240c24000980340028080e08000c0001005103109000001d0801814020300040c0d034040340c030039103801083c01c101d2003200d0b2007000030b407244100c132001c0c103123103040318907031807000440160348140850050f000d83c2c0e012542405e0407038201c046400c013684507103140c44400c0c119003410b0069680c8604c81d450046d00380f00882c1d03074814014000380c5c801e40c0c05c040049070500c024a00422000c9c3c0b49440000203108100d010b540c00b800f50441440f8542260b9030200b800c000650080d4200d80400e03c008081d52840d60719002894010078804280709640381c50060001ca250a0490110b410307207820500a1603182c6c0303488011a156032000744110300700101400000001842d038074041980c1d022043c25600c0c0c0c0d409504000b041d113000c062603d800c550240304081036180d000b00d41c50b038100d504025485411800c50002c40d075041071048007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205755395 1106 205754289 205754291
    0x120c0e0709050d0f0f12050a021516080907170109050601090203130809131415011d090615030c030f2401120b04050c070b010815070f020f01 62
    0x2058029500c2501c9131603030f00c03481b079444500c400704030006180824004030f1200300d55034040c41180400804443c80a0a92030410b42d949c1d00e041800c0540010301420702c012409281050203070102800c11502003008a45003021118000c1c0042e8100340c82e2070044100128511946008132800b1745100c2a002c48980c0d507545403490f080d40018071030359001242d800010002007043c001c81000541d5a40104510f14001311101424115000031a0400480a01c00e42005e544058051003424041d54507070010f5440d54080b4841000c41461800314003000300c20001d01d00e603108011840340001e0404245a600c030004944007030f00d58202000346058200b02048140d52044070030300b071070b0703044044c0205d5030308515400301302150021b4680d000050000101d1605101001042c240104080c000602e030107001d400240f052000b02030036900410090803903050410b482042034140c00c03810070380 = true := by decide +kernel

theorem cover : BRFrame.Cov 205575539 205755395 := by
  have h0 := BRFrame.cov_init 205575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205575539 ≤ n) (h2 : n < 205755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
