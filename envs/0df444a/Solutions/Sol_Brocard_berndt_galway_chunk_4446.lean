-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:05.506834+00:00
-- url     : https://prove2.me/submissions/4bf12bea-77e3-4f5c-957b-aab02e920919

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 799460431 ≤ n < 799640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 799461681 1250 799460431 799460461
    0xf020d0212250e0c2113020406092c16271b21060923010e060907030902130501090606020703081209100e07140616030305 54
    0x3500000018012015484003050032800d0360a64120404541942807050520b00c0ca20310643c0c0900d0395801c0801c41c0015690300401c0483c0150720460b414004400003031843c00c40494071009020302c409410002c505e040d000b4040103200d03020f410b100c003415501940d50000103010401901c6c8a40034001407104c402032140e14203a0b000b14041c000303031a82d40c0309051f100354186a41940310030316102030104851568403622000c5403500c01a040c1c0d100d1903000035185101c140106403c9021011034600c40c1d042a40542c4001e0040c1003c08039942540311885102003545088030007a40c0010001400700c008000d00003a8440401c0361210600c3e01c54107415801030503101c0001e50400d00000c0840d082c8407281e00098125194040c00304143c5540e40b008030384600c940d0100504082041014411018007101c886801030000801e0340c0e200c55031811408211070310301c1e03504441500300100420901d400995107012065041c2c40061500e4580070f0340b8024004074800080a041d81c0e400402c200c0141018a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 799462931 1250 799461681 799461683
    0x71a0f13080d0507062307051608030112060c0c052e050f1501030e03030c0a09050d030e03010f1103060d080c1b09250e131119080c04030f020d 63
    0x684521086000b4000d0282e4064141079070424108800c0303804040c81001d032444465451900705810f0348a8a40403646a4002c040000018050300500360101712042c0040d402001ea15212040022552912806a070124501e0009201c0007892000c003080012542c1c2031222540c20300c0c0614040c004800c1c01d08500e5542603c0c00e05403501c4100400120403160b403a0140c0081849581004e10300401101918965900b5100e60340081c4049100f2800c007901902e0701c40001c0c24490215515840071030041d111400c0309400107805904107074843d003401c0c858550043c132401802e01c042c1d1501d0b4102641840060b2105002e03401140c410400d0240c4c0c1420f541086103080192110320340b03620181c400e01840c00e80814800c50030000451a00d03400704c80040300841c40c40207442116900c1d0741003900c0d01810030030060b8104c140c07800d2003610103441d4440c01140001064013142c4030b07404010000b404030a030180040500611009200600a14a040e00d044a030700c07540300c58902d03c080c404a54480c0c211300d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 799464181 1250 799462931 799462933
    0xd0815150409090302100f020d140601051c060509070f120516360e060d020102250810060e0907030c0902090312070f020102060a0908040905060607020a080609071a0f1308 75
    0x1f840801c070407002d070000c05138004500401d0055108100041c1341800c02550120301140081082c9408445e416101c0c00220561100c00104541d5030004203407030103c00c0320404000741040214401090308410350712090141e0280400c05803800d81040c04a020f01e5a054000380807414056860101c0b00304450f280d2601c00015080a0443c5896031800000c902d00800385041c1d2490005031060410140510050b40c05a0040880c9003064014225490200500300105500e00801081c0354000b081080407040c0048000241d040c6032010340b0351070324000703812019560000030302000070071100303082c00054818600c40140c1ea91078510000b4540407100000d48412003020a05500307111a00e00d402800500030307000e40b4403035502c55800204880c10351030000d0404209001c2070018003280c2c3d111174ad0100d4082d242e249030905640004e040d2004a9102c40096071043d0200600864288084002803018501450010782c1242603542d090166141041d0468800f2503040b8481c3c4c16255120f005205000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 799465431 1250 799464181 799464191
    0x30b04051c0f0e040b03060103020910092a08041a0a020424020606060f070b0c0d09060b0a0501051c0b0103060b0c010e06070e030607030504050f0d081515040909030210 74
    0x240506052054802c1c0b00c0841c03102c01800f034450810340900c490325600207024000f1607003540d0800c616540c002d44403014407059060301007403100e60382c0b0441c45107589e02d2800c1c002c5203102c50a90490340e80560081c40c20890040c0500c000260090003611152007201c0303008110ba6120851040203014a6200d00503565010002856644501d41c5040005007268203485203903460070180511441507050091140301d040000c600860090001c0d1604054107100041ca05241ca003e45c0781503900144040d40c2640d520b50a545123842c01c109501c000788828202242051120001d4481082c1100c04120702c45484080c03e540c40d0b1720a41c002e801a1540001c1541c40f980d00091a81c000c0a202203002682d00c038850204090a010703841294040400070000c00640d5a80c140403000381c10081d10031960340c4565090311807000802c0c00f40399108401955099250314050490000f070240d50358040d4001d00600e600442c0d225a03041c126401d5400401d004180801c0d03520302244ac2c41c0c500002900d2052800e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 799466681 1250 799465431 799465483
    0x6110a0e2b03030908131707080708120f070c0b1801020d0f1107030c12060510050a03030e190b070c1406070b090312151003060e0a0b241c15030b0405 66
    0x46c0c411f40f100003040c41c003103480761030300c070b00710580e90342c0362070142d20401c0e4001107110b149a41d201e0000c000e810602c154013410309150342d50f05006104a40c102410840001c100740d81c02c0004406080740d414003d10090040800c1c6e0f083c05004030b4082c1c981c0c0d4040240203002c4021030282000082e0045501c4044071a105503103d50700c0000210b004011105541002c01054030400312603070320410f840d001010507425525559080e506071014070500d5400405114803846104100340c07000c4010b01250035500d60351841e901d0040b4560803103401c202c10301071075000704043d56141c6070f00342c1d402594400d609940607115481e010345140181c4d1404a07182a011003000109010324024130020141902e080003030222100064003640d0190003011480d100e610000303400440d0315082034182c4140034250a14400c494590840c2000c000c114011703a112001580e00c03400c1703030404941c1c0080805030000b0064030b01c107100d038001c03c04164400601a001284045001c1c440e00b4030006e000081122040740d2102c1d00303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 799467931 1250 799466681 799466699
    0x70503061309140303100e040209060909151005040c03050f0a05330f0d030828060e040209132f1306210b1306110a0e2b0303090813 58
    0x1241c14500d000201b0000007100c14001c09a58042d9900a207156483c2d52000c00348618180d005180040920030742007850a1026240c050600440101160f1180e1605120910040e140250203180c00c15192030200546070890086068001c00782844c003043c140c0305d5100001c8210b4100c0e1078400c40e01c6000e5035044111007103951448500a00350b410300800d40a003010001c64800310140540880c00c0b02c0002908614009000d5040700d0301d06600703c48845250401008413100c0c0d412141205006030144015860420406a881183c0c007042e803c10720710644d00d2032000f00c201c0e200c40d14592202150b01d11358040700d200a61858402a00075800342d18007418501c081c3c1407a20034503d451765096032040c040d0340c4040c4080041900095001090385401081c0b040309170482009035202c0359960010102c1103070070801010b0452a41d41c0b140251580da8040054a000661020010440500002d03075040390850300d20310b9462700b505000a043c60181002282407140008401e07200c18643c83c04519110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 799469181 1250 799467931 799467937
    0x9100f0f0f231017070309050d12060f0e10090203090a1b03020d150c030e03040e0c07080c06070e0a1202330a1803050a020d060603050627060705030613091403 70
    0x2d100c2c1550090b00c03045002c3c0d084131403420002d402504174640d008003080c050020000c42c070352b04200000302c81da583c1c01c511796031411a41040c46840c20721000d0100781e80345e80c039106c00a084109030861540c102811050f69485082600916007000c000c080c50303c10004070000781c01581c001d00400008040303854403804c81015944a801c68528155107290042c2c42841020710f10005080218a4107041c09064080428000c1c42d110a2803400c02044c40016410000340000702103041c0101441d0030040f001510111202004030b0003036081100c10854018480c00c48400741c2c2d0140c0d41440c080020031342030040104211843c1c02200580f07585a50854040c200516008006580f404504201c1c203007241004100d62102130410391043e05018058601482040b200070b00c00c2800169580d0350341d40d00c40c00c11808403040f0b00e41d0340c0303030340d91001d01140b07a1004111440b00d0200504011301d0501c001808500028112a00400b407076807500043c1c100c2a4400729089810100090b58078002600c2181e4ac2d074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 799470431 1250 799469181 799469207
    0x1152c090c07060e07180f1b0320030c0f031909111e18060d121701051023071a270703031d09100f0f0f2310 48
    0x11316040f1382c1200702d88046014025108409031050400e041145550042e010704400fa0405a66898950307500c0354100110400e08a02c0d5100070940d100585031b01508140303900b510b42d40440040003042b0030b421181c02151540000c071000951030351505008003440b03250802041418a241508103810b2000c0040324400e00345045076942c0c6000045d15108040d5882c4129403a00320b003d400062540c104401c2c481540201c01502c80c3c5544002a11600725070449a04450046880f46801d05880d01d034009e070482c05407030203032102e40c2e00c07110b10300000700701740d61000c008046c41c00c0c41d019481a00b07010310101d4a01a8011030010300c9a081c50f98040704402d0143c3d0758000440e001e400b2081000da007109000903022905024040551954070705039141005c2c03503030b4a4002c2c05c00103105022651590f0720580240e4058441e03410113030902d249a074507407107590042d042200e42600d0400c46160402c0001e0b06841c030407442004142021903c4594107201c00c3c0613140c0c411001311442400660080011801c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 799471681 1250 799470431 799470443
    0xc122808251115041205090d060c0c021905010201050c0721090b040902180a0806130c050904060c110606030712020315011e09020f04050f130c03020901030501152c090c07 75
    0xb0240c117403401e035054841d1000c0650400703501c449810119640e5406041c4c820b40a04041031402c40035070001e0044882c0b070180058000c02c010090042d13507030910440d54442c50240d070883c80c2c00d40b2030711030300c5a05028a1400c1d82c004200c0305400c0e4013a101d2003c1e00700511400d80c21171740343d9448001c00030294010020200c07542c0030000d0180310b0341c03600c0a900c1049070302c500c020b02103545541c0ca04101030b0002d000142c582040d0000009201e0311003c01e42c5100b0750040b2000551903148070300003030800220b118182a6507119009201c4030b0355010445134100c5409040f90880845140b01080c100414503004003442c01010000107041d8808400740184481c00017441c0c03103605e49825500c012406070802c0840e4500081c00284002d09000081608080d07004190641200001000806031201e01951200194022500081650b058000c441c05400710294551074000030010041c076a01d000701078441054458115410500d8000b80c0c0d058100001605c0c0c0d103198940b9058103020765001880407204 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 799472931 1250 799471681 799471703
    0x280203120609010303051c0209030d050d1503080a120e010e01090b090d02030d180b0408130b040305060c1303050a030f17090604080c12280825111504 66
    0xa1490030b4040e441c141c0b80d050311004e00f0b100c60a441044481c101c6501e141c0300a60801955001c1d60301048410704052442d9102540d805245403400d050760061007007411551014282070000600f40c60580f403204c06c00d840c004044c0c01c101c17960340c0e018200140c2001030702c1d441c10100580d0a401904840c40060290445c030340a070700ca03c10003a650b50425500b00e4010b070018480c41146140750b4000b1112254580c01d0b00040f0a50798a40c0389070108142c0307048a01300c0000649124010040008a00604550202d00d0030145141c13961900c544008001030808540080d02c0300708507820a0b9103501454005040f500c1e626003034a0701815405010f0101c2c0080340040701400080191610f03141d00c5041003801402c0903485695030108182c120390301c50f41d25401981c01c0c0300002d81801024206036090a0300404d454643d148050000c840d84588080400200c0000c120440c0f00c1c1c075480c4034140750480e41440d40e1807100c2204942c103101c0c40c41d002d01140144031262440034828000e80740254090b0b1143c0c12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 799474181 1250 799472931 799472941
    0xb040203150403080106031a04020c1609060b2a0304080703061407300c0c061d0607050d020f18010305280f060801050106090311101428020312 63
    0x94800d03000c48000f00003450308001404260300c03030340242052044401c00c10102074404000101a6040b400d40080c16500c028491103030309070f1196901c40148000c0e0003c00c541d9042c6540d0f0701c1c0720300c24030301c40140300c481d80280d070364007101607a00d02d85402d0100300540c0d45864640c0b1041d0344584042c842681d000c1c1c20004907049080075004002c0c007420290300c1d440007800c051000c1c1100303210140c0211010140c0355a07180b444034003a00a041e4078a15a40e1420790401c49032030300e8002c0b640c1c08410126142c40b0a9140c1c3d001141c000b8910b50043d04a080c2261200390402c5540060312500c81da1455810b0f000c00d450344640f4550004005049003601c0030b0001e07954580c01c030b056944101d00380c00b0082d0140314881207622503d6001d20201c9020900102d8460b40342d600c054291003080e07016000060b1001c1041052004e4030b01c4005200c1d00c05c50b0311282031000303040000c220350f40380395980302e200c003000400d07034034501300c0340d0500c00c505641c4240c01d001c05030600f0b80a074494105089440d82d020038840010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 799475431 1250 799474181 799474213
    0xe060106141207030e010b19030b0901020f030106110718020403030314090c0d0204151410030c0203030114011b320d0f2703140307110906010e0901030b040203 70
    0x890000801d03002d00c40301c0d42c4621084015001014009003955a54401d8180700c0c2c64aa0000c0c1c07001c069181c00340781c201d00d54a030051030b080d80201031682c1c0c1c0e4814440c0f05103014120003102d04413031307041c9880c9200202c01041c160400b01d456001d04142c1101000fa80c803980526009001101e000b6101000200da81c2d621200f01544111041800c1741c1000c50201d201d440d00440c0c0c1d1000f68009003000451a203000b0f0710b0701a010040e00240354000031040b04050524110390b0700c686140d03042ca824801c400f4000d50203542e900040c0240020840f900550030001d911030300000c0920b440c1c002000720700707580384e0a007101030003680d00d07034043d0901e4064103900809088200c0c007a00790088100030040480b05010440e240082c402c0904104078192003520745503c05a82200d03900044085040b10140ca1864280d031120f02000c180c3c00c25420a01c4010081080030f240c001c0d00d040305541428042d610300307004a1f940d40c2c2c1d9110b1103a00c644018000700c14400810303100c0d44107a00c26021503880b04926078603c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 799476681 1250 799475431 799475437
    0x10020d020a1205040305010f1b0513030f0305190f022109090429071719050712020c0313092a02070314100c0f020307060209030a05010e06010614 64
    0x460141c1d0214801c0030015401102065034080285070407400d02c0d480340d8075182910140e950807075401e0345030782d014002c100030b1001d43d219035809818590324118200c0001b1900c041c0300d12000e03024680e44d170f19500a041c0580d00f142c0004201400c82e1151000c1110b000e040c421a000da04001032003038464046007203030100c4000780403a03c100845400d0030502d104000d0708290080c001c40f00b151381c04140070340001041003c07170405110b01010780442c0c500000004c102121010b207400e4044104003d01c0060810751101e5400c03040006004245030f0b81d104030584000210341544410305200107420201000d010010b4141546841d401850302a51010000169065040d4560f1480a288400b0000505c40041446241440e005460a1959a448030400d20300c3d45213114050340c016401e842038580191140314903020140c2040d10300507981c030000035624021050000c1c0704d943c2c0054003c015079410428600c100754844000d0085240a0b414162200400c1c4140f0340450904d0042107904d050b41000d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 799477931 1250 799476681 799476703
    0x30501080304052215030311030405010c03030b01110613291f121103010e12030a021614151003080d02070f020a0801021e070507030b1b030103111002 66
    0x214142400c1108005500308040346001131400348590000000c0810700664440341c000070041d1403001d00c0d6003406451030040170040400382c0c000b0001440305a0300144000ea01c550140b0300000c80c1c05081707005840c0c07500300703e40d80d18103440382c901000191158154032040c3d503032003442000ca0044c4034454200c85c0070754185401700400c1a1308002040d40039825882d84440c0c0041410300303a110b54072085241c0382244940181e42d074104c40c0400c1003550070300f4000e40c00c4180c541401040b00d00700020002c50a80806403d500d08103800048500c40c0ca0414003c9060490b004500c40154801c50030400c1c0d507030740c4040d20b80f49100341d401000520054041c1461400c881c1c004200714505140b03c0c014500941c0b254100301c0743d100b42c480d402000350319001c00b901d01410803580016a9460b6290703a058406a10341c250710405d560400c40b420001d01c01103840c80441e80e102c0d80c80c0445d03440d0410080102c032204203071403031a10404800001070140b2603003c172021507030984544a440d1440300003240c4034400d4101d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 799479181 1250 799477931 799477933
    0xa180b0105070f0b090a0c0b0304171206040b0f120d09060c0309290304051006080102160809041404110103051005011e05040503070815060609100e0114040303030e0d03050108 77
    0x41c00d80105110344e003010b0740f00031a00c040e1116000556103040c03200c00039400c54140600084108002c005c0e4001c0c0041c03001d9020300e44a82400c1d24804c3c03040c030185000344110301554480312403e8203600c0c1d601d0168507458000b40140e110b04174004915a4462416075140c0000390159400940e0602581c1e00113401c81e01550b4071003880d0b0408168080c042604e022445928110700741c40303001900e10102441c00382c0e100d08082d080e220601541c0b4015505581c01014031a4810003105140c2c020b51420421240d90111f2038035101d0506a00180041c0381c800352070034149014800300701c00c0107001101804180d1090301c0410840d10307000c164482c800c4160003943c1c00b24000c02e0041310301108402003035410003002c0c03401c5482d164071480030908000f0b40303600445095100b80e48a5000d4089112140c0d4001003d070b805508003108500020749090540130303560300b4041103000c0031000da44282c40e050b120f000449446542d4655a240040080c0416075000800c4d005074803501c01c01d94800d006150480c1c80f103030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 799480431 1250 799479181 799479203
    0xe150a0510050a0207031e05060906090a03120204120f120509060a0302070c18021c05043302071a0901051015050c0f0309030d03060503100507030b0a180b010507 71
    0x481c295000e0340203030030510541c4122007001000850402040c010805013060780000e500207840c2a0385015405041c5030115040f00d0300300304078a0b00005e60002e240e501441c15261407289081c0c88402841290040d8040101c5201c0c10401d1060b043c041c50134451045240300c00d00100b4031011079041c040c2c80c84d01c5a2103c020885112124440c6d0050f080e21f0b405043d0307806078240d60b009004404191207600415031b90700890b07400d014410809807a00340f08000310f0180035516250351180c1c0d00e102e541c1165035120000c60140041102c4451848901c4011000119a105041c0c1050000d81c4001401031105108210005051950600a06000e403090a0318507018a0030001d05485001d89444580208141804004080070b030030480d071020381c2c54120107581d941e03644c0014036080a0000300003030300385030405108001640b00050900e030610750281d0001440d880d2440120082c1429043c91540200b04050205100d00f020660396403e00b07080208204140c5404010344482c0035500024004107041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 799481681 1250 799480431 799480459
    0x8070302150a0c02011d0301140604060f0810020f120a020702120c0919090803180c1804030509040902060703090f1d0c181206161e0e0a0f0e150a05 65
    0x25501b03003081e54800489241d650701003980441d0846401c9280d0340303607407408902070003510304192240402801d1075103d1101050305200c5001ea0310311140400c10035050303000078400c83c810100803d40c0c1b500007201d00c0c2c4c00201c0c20428401c10187d0041a42a840358000c103c450600420018a00300600741c054642400c59603a03a4901178513011100100c01616120b403000000a410207000710301c54036868055008802c00080e0a030724160020b04014000e0455109402034040a006035590095152500607a95541000400c01401000f58020340100e000300da41000c05030004203440603919062103100c1a1030303441e600140001100c07900d42200e00c02c0c4c48089005140382c000184001300c80b01c040989d24044e103402150720070302241c60040d100e030841018802c0c034220343c5070100c1442c50343d03240400881c000004584d0745030511a03120000e01261750405a01c0b5280e1510030401080e2030204241d0300c2d591000340003200c1a04603001284134140c407086101501d030542c074803010f640340903040c01194501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 799482931 1250 799481681 799481687
    0x12080306032a1323040b0609040206070803100e13171c02070204110c0304080c011d010e0f0405070f08060406121205090a06030903111c0c020411030108070302150a0c0201 75
    0x20b5064010707401e0761200c010b6101d102d0408410040703000132a400c0a014034207410a240c1441000d000301e4400d9840c80148000750381c906050301c0226410214481e980e0f2031b44c26030301c0420203041e802441d03507292031820041c040d841c95103100d61250040c0002003445100041d8108248602002210b011050b00d00043d000000d40d8094644030740b0142000406504042c101c0c2c0b0250007001e0b010000798400602400b00c00810700201a502c1c17001c1c2400781d02000700c1105000d12803090b06c10790b810003081c0d4002003a15a6109034010345280702074010889400d046078010310040030700f000c0d13030080b5840c02c001c10401d0505214503022240000307040402c03241c40d82c3e688402c80518190150400100703110200f440d80c1c2d0a00c074500244015180001c20524034034002d454078046003401c2207950403640c03c01c0250081c1030f0030100c0201c02840c1c5902a403031203100140080c40303480b8905240c0f000210010403200740000ba4801034070b0003202d21810190b607100c000e0031244205030a490000f41ca110a030001540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 799484181 1250 799482931 799482949
    0x307030e03120a06081212010b032a030105010f1701140126160503040b011505070f0501062111101b0303091b06020303010b0901050412080306032a 65
    0x10108040c0c03890710328200529101e2203000e5601e141900e6a41c1301c204030f068810020301c0750b6510300c1c0d0081801e282a207a00c01c21322120501c0780e52070074100080010790700d0785203200c280001158452610300c2c2802d11401c10007a40c2090051901082810001800c664020088a0b0f44611805078800b600e83c01c01d44030400d90050700c400b0702c0c103101110200030100842e01042c81e150340c94010a242041ca4000b1013a1101c1940302c2009051100030001e01000c1944500018150303006000140c0c0a501250300c08c03649480703640006090305100383e5010f000c07c6410741005007111090720341005001c01712040c04455800a140c000d220102c01c80b000801801c4c04858001001424200120780c5e80c1d000b0004080c1600c00c40c01140065544c035030702c40400c001d200d02c11140d1100700a081d440c06003040d0010790380e84418000c0e10400c0d000441c406405072f10403002c6901a02040e50425a0882103117081c40458000b9115a8428050001c20103040d4100d050446584040800780c00c0610b4594000d0204200c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 799485431 1250 799484181 799484201
    0x2090916110a03022413020405060105040b0409050f09061909030504150305090706020318012703080417061005010e03101b0e04020705032b090803150d0305030703 72
    0x4841d06510041c010300c80310550740d00940191000195250700e07134807400c00000b90201344410072414030805101101c032a800040e416500011035448400050383c0302d0150368040d1140c5003000030b000c41c1c007054940115000d4028032050342802e1310b61074105038661004681800c000c401e00a1914003090f040e4101d000c180d4041d00b400c0c1c1c5401e0310f42c514009903003c00d1301c0060106c1c2d12a0700780321541104104107402455107102560a01170120552003031441c4103094030b81008038982c054030640c0004c960032270003003e1154840114594a140c00d06194000348a250741c1d440e0001c0701e01100d1800412150b00c900c0002610b08400342c00c0800641d920340540e403065825200700004102444040e11440c210640c12440314078207088400001818402076202c480d006500512490700000c7c0d002054501005100b010423000e1030000401100044900d69101e6080e410400c429040c0410100203502803245480f040711202e0741d02062144540b1030b0b12008000a20400000c1d001c144240d00c54100c00e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 799486681 1250 799485431 799485437
    0xd03120c03150909020619050d0f06210b0c1b1e061005090a090f0f050105060a0902040b040501031d01140103140a050c01030b040b0409050c0a1a04030609060f18021302090916 77
    0x40484d840c270b140226040d00716003004090b03031804103004a2882c41e68526080c01e0411160a44000f107a82d001c0b68000d000d41200c8420748046003d075862444079440c403801080c24811141803040d407042886900c04510007288076409600040b070f014076002440d8209461000c0d002035180e440f0f0400d00300c010f0000100a84101400ca6260800a584035140d0310b41c2034020000441ca03070074000108449850f40e98481c0c11014030400080003440000e801381e80440b0000d00300018003080f0054500d00403409a010001c05510b04512407001203040071101e03058a00034005200b403c0c130740c200142c1d0303502d001c18009051580540c003046520346c1b080e080071610300005040442d0040341328003c50240d03100342c0c208a45030303004460b0221803810818602802001010a0003507001078100d2030580704d10075400068100d03500c3c6c2c0700900501a040e08414000c0703014800c2000004204011040d49004035002240b14a07640c1100307840c0b02503035001fa80d0300c40000a0103440d003900c61015805008190954003014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 799487931 1250 799486681 799486687
    0xb0f1809090c0d2a050f01030b0108040f0c0b0a020d0f0e03060a0c12020d020c0c0d120f02070b04120203070501080709121e030807080a1a0d03120c0315090902061905 73
    0xa0307001303100103000d404007040e03602081d5428a810003074050390950029042503e0b010302d00f8010b80e4007065494100342c0210a0302c80b5040d640c2420120010260080080404c000070380c1c0000d15800900404085040d90710f05d44201c403691822074240c80003c00540e40f65021001040000000c1d50041010740014100340b14054041849141603800500d44601460780c040b500c100c0b40c0034180802c09005100329980401e082a903503540b448a021f6550010070814442d48000c03602c2d008000d41c2c3c000e0661705401d952a90307a680c0b262800c0c03000c01041203000780114030001a19500481e0840e000300764688500c2c40e00c034140020680b040380400c4080e207441102c18460301481c0310361524400f010380240d4840300a854542009464100c4c058030210342130340307412802d5680000104a10906407404c40e0088101c0085050840e041c42541446c013030f669107050b84541410343c256101e807031608481070a5112043e500c042d100201c80c00c4003000b81d0000300c200243c46003070303646100c1d0304982c144a060043c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 799489181 1250 799487931 799487963
    0x3040311070f0605070b060a08030703081b040f03120804030f0c02130c09051e2412010e06031506030a03030917070303020409110922060b0f1809090c0d 67
    0x706905640c081000b0450008110703050203500c0c00c035a80c7c0b081d4160340f01c10f10540340010140c2c4e02d00c99031002504201c00b0001207516090003410070032600709c08440081e00d0b1911001940858600d5100458001010320b580031000e9000c1c41240344240e4040d15030a00e690420b420a5540d00d652100032032303101661400c98a81d002d16482000c0880d041742c2e5030b081d02c0509000c240030441036058406001c800c0102981c1e02980d8814111103020f540300c60814801e00b400400888403030080d40050310303100702100c00105a40c551224080c3c0b05280c120f0880c3c0450b44803050000c4055026a40d058150f0018071107040403900035004801e03a00d104203040646a01300c48038644250700312035011800240c00040030405120b150043e6840d203900c8500c030624010800340000c0700f8101e40d03410389102e080c0038444120302007490350110000b4021a5002640e40e030451418400542c010002420380c0320b0b00301c2d09124641000030005104000d01c100408202320210f041102c8400c400c2c40866085044020f000c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 799490431 1250 799489181 799489199
    0x1106070e09130609080306040605180a1a0907020d030b0621251107050406050f120c1c060c1713151107060c0815090a27030206060105040b0304031107 66
    0x10000b40140304180d00c1c0e081601c2048240c9e80c096000a1142c01c140d9214910303801054212a008003a980c000075001000e48011740d0340c154000420f0f43d100600208000045030080340329450000c69503800c114940c070b03050400c8468010000d2003500c100242c0c0706814403840440d00c140d0425a030524100190b05000d55144004d000000c4007800150b24a2082418003000c03c18100907004c1264144001c50819012400110010280a124040e0030303032130b88410070090107141e200c81405858130002c1e0f0385a0240003a400c8040030111042850504040c04891060000d1641213031100341201541d146d00c646003c0b00e245418050722000b10814180e200038215101c1c00785207a500682c015101c2401e41000c5089030b252000f0501808040f508014410480c0c0d02c201901040c00c130388051a940311411420010141920841020b1541c03880c1428841800c0411041c1603103c3c0c0e0860f041b86d40d03800011141c130b010750310409141c1c030310601c080f40c0064000d880d4005440d005d00202c41302c6c155150303808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 799491681 1250 799490431 799490441
    0x3240b09150c071d010f031a060a090c032a0212071e0c0e0a060b0f0a050c030d0b0306100b0a050c251404090c03030f180b09011106070e091306 63
    0x440f6030700f84c500c0d080c1904050b807985440c01403602c805030166641c603540303402c45500c1d41e00c0700600b550313031b0058009001381c1e45110f0f0080c05045da008003000340404071a0007400901c00ca1901c810421540081c23101082c0c6840c906180340070722540904600440c00c41d0102d980e401080013100d9600821920b07a641c15080c1024030039030340c090000c011409107002c50b136008d00134002d400400740c181071101c14000205883c1c11606050801c0c40804e41c0c3c5d0510010803292806035036001101400006042d01c05140641c0203440201402c83c191400d50b16132030b80108070000e00c0d00c12030b071903460b003030007107402d424060000b42030091440307825281d011900340f0461042030740303d1004080d1481c04940c01e10401900043c0c902070b54200b51420446030b606900e03104000c40161200030f00300072880c032010b0303000f6201d0031800e921418060090241d4544801034080d80741c000f072100500103213520324104902c01c00000e8240c0582840d40742d8201b09040c0d4028050000d0303006041204401c400110500026070a02c0b41d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 799492931 1250 799491681 799491689
    0xd0207090b0d030f170c03150d0b04030509131109041b0c060203130206031602060603010c1b0302011104171606120b03010b0d1b06020c01090905070e060a03240b09150c07 75
    0x6215030303d203054501201c40c10092342c4040d01403810311094500081e1364184461b00030303800d4209103444494050000d4601d1666941d404000f90070714080441c4070000902a20400310100d40a100704038a00d19452a1401032401c5840020760008088003c81c4266004540000c0303506000d0035049059004a103c0c3e0744141c4480c096001050060302d0410381c1413000681000b4124004d00105071103140091541c1e020f02e41c03251041c1031010545040600075446040340494060780c05455999900c1000070a01007054410580e0160107001c04001030603180c1c0c2c1054500d2030700c503403981030310481c0200f004001202040e5007540d603440000015a841440308003941d4400c25001c05c0491310b81d6415241840a41e00280c00d641c00415410302984e04905c142c002c1d00d80d240300004081d0340c1c2140c03c0314051440791800360000e10002d05500306d5641500604040300700451541d1002c0c071441a01031601c04148100407071070724140454070340343c03400e040b084150000f5081024104800000c0050a01c07147c1d40c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 799494181 1250 799492931 799492951
    0x20904110103060f05010917010b09071707030507090308090a08060c07060608030304050303072604030801060f1103160615080c01080a0b0306060f1206090d0207090b0d030f17 77
    0x344041466030705024100140801d03000d0030418514100018041100361300031110b21070240e04944c000c41100f5030051021400042040714141003000010784a0b9840501c2e00141031301c400f0000d0074040c000d01506011300810355400c1e080c949103464602c4590071009055030b000404520006544108100260103601d0004405907580300c1c41c6482000c03580740f40d201d090243c0060003000040b500103c02c3d294001101d04001124105c0c49140014089610041416a0600170709100900d0b6001c0c4007203059a10b1522842842600c01a043d00e4215014520041c103501c200401c05841c5030310038151080500c11000800c035030000c0c84c289610300c1e0326904030200c20b82c421403448146680c806051900300551004c10004966a80046a01ca400041190307010710640d241e8848591105401d940041c0503020a60b100c0341424803005843d1a05031090100500c030724000403030381181e80d128107500124010204e140700016039a040c0c80c3c412410360303142c1c00e10901924003101000700f6980d01d8810842c4503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 799495431 1250 799494181 799494203
    0x131802071208090c030c0a06030207020d081908060d0506270a0f11060f0d0207020a0b03070c030f0e030307060b01050f0706020c07090e0d030504020f04140105132a02010603020904 79
    0xb40d010b241101900c82e852007a40f05200d880da0760b4980600c47d01c01d88603145005680c0d10640c0c00410009256032800801134980000c00c22070484050401e1024080681e54490302511060f081182d060b003103602c00340080d000b280100724280540d0002000c815050901800689001c5071141d0034806151420355001c0420500d4900f00001440030404072001290514205112042a40300501648160180c210350003c2c10300c0655440419640040c0401318240f81c1d64580504010300240c400503080340814112100064202e018210008610350003a0086003845450344400d0083c111516005051200400104010040b514000d00400d07000c0c0d200981e50b4031aa0480714078040d1360b41d10050381c0901c0d010181d00d00000209400280444500c1c0129803a00e0750b000003032600c544281810b80c014034001c0390110030080501507038102c5c0c3d01250902c0d5403510560307581003078a400c038403500360464048003036180942620124141180c4907100024150340c4030360108040c0c40b02a00c1c1038070011568 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 799496681 1250 799495431 799495441
    0x121f090c020a0b0901051918020418300305041a07090815070f03090c170106080c060906071b050d031d010c0507050f01050f2d131802071208 62
    0x42c151035030b01310341e4039030003082a4648240c840c80d96910909101c02c0a64460140c4400748402c403080d050016001042001091115030000c1c115041c070045c111141c4500c2d64041a00d41540107101454250100c0020b41341e0310000011002010b0081084600700c112103024040c0c13802010761640f0403102922507040e00b90030032070540d01d4620300b180505004480c1c0ec0400c0052075222204001c1c650b220709010592500c03a00d403c0726042015049418a000b0700d80030048401c1f0150040409c45145506a481208059042c4959442401c0019401440c100150b10010f034542030160200d24074502d0003051103407110002420109180b00070f800040710000780c8100340350240000c0c0000c2009082c001c40c80001681c0311501c400003485220f00c5124007801540e10742e4010001c407410703982c0c510740d46a81d440076034050300d140039010110100c1c240556030034003084802c2802161740181003460b00758400f52821040c540400140c0304d00c8008540c0071b1094600084461081544072806074031503901610740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 799497931 1250 799496681 799496693
    0x14030403030c02131503031202090409050102190203030f060904170a02010f06080607140a050c0a080301080d0810050904080f1206010e010309151a060d02120606121f090c020a 77
    0x50002070200452910559170601402100e0b050212945424800900101b882101c4001d0050040458200d410003115504208065006250304543d2590300032111210781c008130317a42d010458002c480b0100300c401152071494001d201c00d601038441d0060b800c80c06c925401e15038441d040003001c280036070b448a4442050030300344c0c02110b000c0c2004ca401404680b0b0410300c0240000f491440042c980c00000500400c01c500c0380d011036110342004411299480c3d510b10308250164801d10546105016035880407400c070f8401c0b80800d000d0f003208105040380e40d041204010100d40041c0085810303d07010480000f480b10010302400040024404010051070000000340c4246840c0c000c1c2da0415103410311320400514400151032040c0755040700081e000c0c540202040b5804002c11a09520070350215400100482c00e40060019a003817042841081c1c61704400d00200c0d025460501110815000001e06843c100f100880c4c2981a4140d1a42c2d903d0b90340c2e41520125400c041107440103030400304d00e0b0307414400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 799499181 1250 799497931 799497949
    0x918150611011109090a0515030a0302070905060415151209080904050906070c0f081b280b07120b0616020306090d081801090c141e0a1214030403030c02 67
    0x95200030140c9400100800217134a0503008210402080d900d10215407401010040b2110981016046840f03624203030801039034500d007074440d0960880c24480028044e0070305009022810301c1c03000400341102c2c1400c0c0ca00040e80744d81501c40041050303948154008520074003611004601a4240941c0ca41c0c13003d081c0400d551000b001000241e0090080c04a0305510152842c0b100e90882c0040c1c18000351440d1190b4903110324084c168131010003541d884100b040104614000780700904903050000c0584041c01c0400c19a03a002619444009000481c4140a90b2140750140c0240d200090010b01c40000030f80144c00c44089145d05641d4140003c0840c2810845a40c020422a004002c5038003040c10041100000400c840c40c050418116406255805d40001d20b1031640130783d000c0320f040d03210030210280c80c2059100c148070780303081041c4020104a4204140c1c48402c0a4060f502c1c56040034802010500c9100045845441c41100408024018000340000e94840c0e524180012603038010400152 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 799500431 1250 799499181 799499201
    0xa120212280807141803060c03090607020a031d0301091b2c0403050702030f010e0a1a070206011a0c2a060f03061509040c21060501091815061101 64
    0x840320b40140464950400c40b2075181d80b00942e2036640d290348542001c1405941031490680501c1140140042c070b010003400b035441211510100c43e82e42d03448080403640c03007a28030009070210300c6c855828103440b1690400c9072080c1102400120303000e030084c1d944000082d070592602248180b500d0090000d00c040b24810941a900c0d8803c0d800389480102c555083d110020700000d06104000030507500310b4400340192504e4440d444020000203020141e081e03104c2080403012145101004a440520209400b02c540508070b1a8014415030313013454095021101d00081c40d02002d4018050080040d108120840c031080c29403580031840340310000681c01d41122018910b202d884280280c0800040c408192135029104542c203401d60007120241014500c00e204000c0d410a0505d000d07425919000241c1d24000d003002034a06841d820040e04030b50881b0310f00d000741030004404c91800c2200110001c8041d4450301c080070000754041e010241d40011041e41c1d48004003240d025403038950310000a1003003410340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 799501681 1250 799500431 799500437
    0xa140a0603111201090b09010b1507030c02090408040b1c0c0e09040b070c0819080f061522121202060c030c0d0920040f0e0a12021228 59
    0x1560070360341e404556284140c41c1c58020340381032551400c9000309400000b000d581003c01c1e0750550801840480c041c0c24004007481c01180f42ca9080c56152038104102c40609030155140411003616a08204604101410640e0000e0040c00b0118072480d010b030042c107c0e14030404d41056594a081c00860940300081150b00612147c01c08000290f05c510134410751259024140d1101c07980c65550039240c4a0f444a40038020107404208003c1d504c2d00000729171342c4100c058903040f00c140d03603070842000e1500007110042e0300a10361041442045440101030722501e60000005441414004000c403050b111603408480b0140360310a902043c850b070f90451103940000d51010300f821745031079004a804c601c8080e0004407401d200003900c1001c146541c1c445201564826050200040808040d245242130343c00602d20840c40e05281650b40d01c403c3c42001c10005010010348805140d540307c0c8080d080c0d01125620a60103280036400c25402c802004042644058401c100f60301d02241e144240e82031262005424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 799502931 1250 799501681 799501691
    0x180a210905030c0a06050a020f0d050306030c090405100c030b0405090a140a0c0b03070201020c0109110f180610110d050304120513270510030212030f300a140a 70
    0xb500c40c13005900c10f0fa045410503e039600400001285424030715900b00c3c031240a4880b4400c030301c50f8024021402040100d0803079015980d49020452040710659008000d03a2148462101e20909074100039150b074410b0400007032030a41c1c8800b081c10b80703504039a40c41003a0410309441c0c080001404800300c500340408010b084981159455030080215800750190440c0007100048201d40b007501100c8100c804000207026190462814840131061030000300e04c246000c100d80246801c0103601d04050f400b07800e00588440c5c460405003d144282035051404010441c1c048d2610082c0401c4004050300c1182e440c50790301e00d45410800c40710381c911460901000400c0103600e40400c15056000169101c41007c4031032a0000c0b52080c0f500107850342c0c0c3c040d15a0509040002e46a2010701c50030880340243d0780e41e40000f8800381d815403070b882100d80c100034210b0103000d070811000811941901b0042e001f4245d485884002c035010480700c0e42210008403490701c60011440000d070260307006402c14100181400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 799504181 1250 799502931 799502953
    0x1201091811041d030d06050a050105120a1a03030c1b010302090d0311010e1923100b040605040915060504060f09090507050910090e06060603180a21090503 68
    0x1403900400a51144166207803000d1012048035900b0604683d01e1480440c1c0e61003c40f98050360181c02140309241c8522102100000c155000d0030489940f0203408200900c82d5481000d484010501e01010042c035929800f908401502c00b0001025424010401841003070b1151510071b4465501d5180305040500502050040e9210f04040241840c2c3c507082a121401c10940b5030350061450b0104a0082d03c41c0e40700c3c4542495400c0358503001c1c107004460210601900710180c65a4103084120307445258840240d140041034079510000070942d00800124480e641c2c0d000240031713240c3e0403070140c4502d80400015007040d00c142c40382000501042d5020700c040381c50300e8003400d014030707a0f44205404603860b550554100310081c4100000303484000d16440282c144007003103d058100502920920900e8042d4030600d400e80020304034403034a001881289103680340126003c50700e006000d03a400074851010040c0015803032040f00b104d002c0e01d4200c3c04042007074215000b041001c2c0c40c0c0c0824004e400501d500c00d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 799505431 1250 799504181 799504193
    0xb0a0b031f050f24030112050c12120309031e121003030e0f06040510050a021608122203060f060902090d0b06221d011517030d0212010918 61
    0x824690f0880710141091250004440002c4124131182010140000049105424456007101c80d0b0702031710413500c4c003c4140e01817100340c074002e2030011034980c000101f61b0b80303500d607c1c8000e60388484450244c038103140a07180b6101a40800150581154001084a044a25501e203816500c040706c01c0301400001d2540c0c41c098481e0a405140c1802141d021000910396140d51045500608014084031100400704000519035001114000c0050041e140b2041116482075400410380380b0b40310281800e42c01307880c90040b0319800ba0043da00510640390301082d0500079081010011402400e02040350300c45250913100301c6141d50051034000d4414031140e651926a0a403012219038880c0c940e58044d15140c0c002005812240d40e4400f55241003282803c400c03600d40c128144c940d01c0c1c4c0c1800d222a408a0f6196401e990625880303180c1880d0402e4204100f01100000724a40717102d020a4078507040b00650020140c1c1c0c089500e4800400e030000c0100310391843c42c801c060a903600f43d400901c811615681e21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 799506681 1250 799505431 799505449
    0x10b0405060618010e06131203180f0b03181b010201230a2c010b040501120f060906270c0e07050d0b031c020a1202030f0a120b0a0b031f05 61
    0x3d6070400c60004003001c110344407002203400d000c007001140b0034407076a02c000d000403007800400100c00150002148990000d920f20280054030080040426014200307980301ca52600000c014901098020b0203180ba40c11081c003c0d0030112101c00d4a56244d0304940001900350b4411004400545015494464800c0391181045070002d03182d002c0800c1004456507a40b12140015807240b195204001d8100c17510107056200401290b015101808660303690038940010740d4503003401900141c60141c050001a02c2075002400040c131511000620903011380d0000f46004e2103c0054000703941c5050144140500690080000c04240ca07080c025460207045c000d00c140a0890785200075a100c1806040d1560b09020111910240c541c2d04c102c2a0f4460384000e40d55514501300b40e83c840702c50b04c1c801c8249c0348080101c5040c0700b161010185041e400000403208405900403500d105640d4414044441e980c5c034200ca401000e80784011505d03401cac8a00350310040309080100480700801d00e0700c100314949404207c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 799507931 1250 799506681 799506727
    0x908070602030f1e130e0606040b1b07030b0112060e06070504031212020a1d0a03030e010c0f0b16020d02010203010302150f1e0c0c040b1e180405010b04050606 70
    0x300700c0e161007216203010070140d0341a07894261984081051688090b175541900304441d41015990f8507a00e4110603c101445036001c0c07a0260f0030308006000ca411940000340d00c0e0a4125011556007940d41c0d00c6d05003400c50203803c403061050604c400502030240e80e0203a0710560a9030405407000307080c480c0380506548600d100091554203008503505c0440e01503103142c110201c04840c19580d0303844a0344010109002140c15512800c41d0501c0b4001e5801c05d04032140a699058036031107001d080c624010f4851105c6440100c03001c0c2c170000b96a40c0001c07440c81d0070f20701800b00100c0e83c24a000c414200641022150421141168414001003002da51038511054551a01043c01c0d0350f1101042c0062500d403084000c91440c06c2e80c1c071410b0301c030720b42d40c03400040080140d2941030314416610ba1040000751928160155409914020385044100c0e1007031882ca80c40e80300600e40d035806500b071020704405017012a400d513001c0c0d545012191940c00e00e40540c80e809181110002d01d0110b41c1c0821130403003101e59030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 799509181 1250 799507931 799507957
    0x120806011d0f01270603020703030c03230a061208130e0f040210050c1e100b0a210b0703051b090607031808010e0102030a061a030a02031e010303030903090807060203 73
    0x1104c4800d4440b402c1031071225651542141d0000d4903558007602070b5203ca10228002450060302103400c910901c5a0408881030910304c044030000011110720784d05020300036240440d41c8001c000f0340084c40c20200c502c40c0e1300c10806d59441d51950b00b8a1000c88890b5030022801c0c0140804105840210540e0349500c0396048501c0c4604081e204400ca4a60041c855401d0140c420090040c0c1100c00e03d100c40d0702c015507090304a071000e40b12407500c042500c2c0090302258000422031000c1c0704c00000c81920035210081007040e240c1c00751030340d155040441400c0d0381c107101084d5a1400c5c00300030220303003c6100c241d810340c04000340740039480f4021640034459500042c040108985081c0350403212288202c00911414000b071000c0c06400440038002d41c000c0d5080c284252404000080d005141c00d2001c0f4a40c4020a1f5141140e541490f403d000e03620007000340c07d1030144110303c001928200800c4074043c43c0031f990001404031840c540600000d03e180c011a903a03502200d01004410743c000125825001b00710 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 799510431 1250 799509181 799509197
    0x6230307230421050d0201020a0905060c0c0a030f0b090a030f08040303201b0a030c0b1302091005030c0315150d02040906151e05060a0c120806011d0f01 67
    0x7210084a900841d086203441041a0b00c41d88090285050036a2880b4002d0b01507852070030750707131000364200d103e40d03007102c2c01080180008006078980070029010080e41001503405071509040003c000240350382048074015004100790b01409180c1102c15841003441c4000d01c0710342d0054070050b2951165001d007100700265803000a04140c1f003500010724241ca18103030445204134655010b0040e8000b01e00d00e08800130b01d00c01d402c035101da0018264602135019255240c4d03c03180b940381c052070850000d0803416030680d0000400c0060700c6200285201d0012540b032000c0ac2420413041609260701030743c0c214402e5006c0380d113a000403108017101da034000c444100040980f4140740f01160800d0004140030794054904251401404000d070085100301d507500b81100043d070b45030800c0c3d01102c00702900040b201d000b030072002e000d130341440c600802c008249428881c03840324051307079030011103410010080c0c0054108002d0061035600b0590b00202034240c0394100c8816486036000c0b540050150043ca410004a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 799511681 1250 799510431 799510487
    0x608070207091812080a0b0409170a02190c05010824040c03090602130905010501020604030203040303051606020d0e0601090218210313080d050c060601030504020402090a06230307 79
    0x1d40d4428805561001c02c401c00580c811401411300181100c01078070b07580c101f4002c01d50914281c8a041c0f840303030744030403160964113081d0b04244443d0803803901c420551003400c24001210442c011004c4e402441400c002000310f043c000018495040601203c00c250071640d0380d484041520064060100310944000500d2140c40b0811000b0b423400c40000b0b400c5602c0000e642d144000110130181c10348171007401c1404503907629401280d0720700d030403074010f80160410321041c07001a00c910010050400340c0210310b040301d0000d880341d5003280e008209010141d50341e032010f800014010301841e401000011001c500707007808440c00345040041c400489108401c95804030040860402c40a6a103240c03000440ea00e407410440880c000d8812405180001e1048585044200b0300c91411a403030f108a0324040c284a403254001540a000041d008a030321039001d000c0107c4984a88640d84010001d60350b0305809219103600f200c01c40b82e10665807500c00601041001007071030300115a071801c005103003030841c43c0044f1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 799512931 1250 799511681 799511711
    0xa230f06160311010b010206070c030c020a050603090109260403080d0207140601031e030c260d020d05011203020d1b0204020a050a030e0c090610091a0304030207060807020709 77
    0x1041205403002072000c0100d001e242c2d000141d024203500c0a80204520f0030114016652040c080390044000384255a95500280c440d90040882034405401020b900d40c54000080840d002207919400e541e5440481d1001d2129540400340a244268082c01c0e02001802c183d4016220350700024240250004540000e0303c601c0e41250859a048480d9843d20704045d422140c5526003032005a501032034182c2184890a40194481c141c184c1c1130300c545450401035a506a06900030b0118101c49030003070743c40c00e40100103410003400300520005006aa42d07155191000403039106800c1a4060307070f4031034100000130340c00180f040c040c07900e107052021160916009240034600d1241000713401c6400450000120740d000f2001c3d1106441c0ca403028044c0c40c01c100e131240d69610302108129400b008040c041a00341c00c00c41202d070718010403440c05840c41034840c140c4103841c850803118220111000402c00ac1415814007003600a03080c0780c9401070345030034180c43c001d41e07421031070080d011015616104c030050700d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 799514181 1250 799512931 799512937
    0x30061315060f1208040f060c0512040b030f09010b130b03150f04061d010c0e01140304202e09061106190209030f15060406030b0c07022b020a230f06 65
    0x6111708810746c0f2034591000400c55154000308464a01c5085200340504110005232405c2e1801d0222075800c0d50f8800d0708400c5030b030710080c1081225550791b0501d1800703500c075160400f00c00d106c02140414646104d4040c0b61910004590a245101641d0b081c40b84450080440315001038102c4004105160a45c02c107581c0c070603010030b01081c07962034903543c071040982106903414110001d0300c0d42e002e190f2410a110040c0d1008441c01080061424103141c031480840da0b11200c0610301404a0408041496205080c1d204007034020f40654104006180c049901c103100340050001460b001c48841c00c4420b42daa03076080064403945d00b280c040521459010001d0341595010303c00242120003caa040e20f5094861146400c085000740b03604001920701d060600400c812245d02040b2100141d6540c00d2000caa81c1112000326071003856a001000a00d081d0f00c1819403a52443c500071200048030301c100312001c5a42c2e41f1440740d04103105001840307c0d19082c1e4010a1000607220715880c04411000074032144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 799515431 1250 799514181 799514189
    0x30905030f0309120a020f010606050403030e0d082502040c0521130b0c120105030304060c0f170403050d1205101401030f05010803040f080303010530061315060f120804 74
    0x41d0000c184045d0b065800100860440003050007082000c0c0c5440d411542442240000b40108180c003101c00a9410141043d219490040403aa820311401007540220303d0241c0c0c42c0200003600e891107480661074148a1015070341c07202d003800c0d441c0102108042007006c0745040d02c1030171590300304005090709038051901011a80d010f80c01100500d48940c29010a0b0456080d0001d5620100c00104081c103000080320180c603050344804009400c00ea5640e105802a07032402c0350381103102d00d1601080145100548060362199018202003240c0c0310004003020361240d4101c44207070400e42807041c1200f84844910580b01c03410450940c00380300f00010380c003030801d002c04001c04a28003800000d41c4640480580190f13a110301e0301d46810750791004180e940f0301082c09101d03800101c2d5440140c01c1c0c1052503a98104d01c04c425444032a041c0101c889a041070000c803403076107002d00401114010880402c0c0752180b51510242c00308507540c04e00c0c07001d8840c0c0341a40100000304081c01c00801c00d00c041e03003040d20010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 799516681 1250 799515431 799515463
    0x22d04150804052e15051228080f0d1e0501060e0d12050310090204030302160e160e01020c091003021813030c0212060f010510030905030f0309 63
    0x34400c1444010412441210295000d0084c0c01e5046034000e005600442030403544195030b071000701c1d400322030740040c040010500700322111148002a1078403a0004c6801480c00a00900300c1480940d0342103090b1900d25004092403000070f41c85000040643e829107030b02c2c4001d00b030407075110500b15542000070000300020a1641c06070280344040301106030030050503a070507541d50150f081a25403e10400d0101e400c00100180000c02c8030038140d5216001039076020143e040560a60342d620307001c840403640660000c3d00160041c40014880051000644008292010a102485c40c0100780d00d081c10030f422240c8410001d8600701020240c1c1300300124010f41000a000000034103010740a44e00800d0706105c102c0c0034100b2800c0c01c40c076006801c25554892210051802a80c00740741d9800c450300a15502e040380d1011007520b401560174400c202c518401d041c41c00e00113459504010420003030326102e00d904410181489190f0700091004800e80e240c500119a039141c498460340c0c082814020401d400d40b0710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 799517931 1250 799516681 799516709
    0x10051c06181d01380603010b1801050408190201180f090f05060a170109150504030e030601421701050f1027080309040f022d04 56
    0x701c07640d60006854400c1d071122844045910280c103402e035012a404000c5850302d030028145030001000e40c0e8200d04418006402c0f40003070b0b202c00140b8030707002a044206c40035000305469100070400001c101c03c1a81c00d081c814103041c5800d485a07900c08800c41031480181051401004690064009419070300c0c0c1a030388565802e40383c040820100c2c005218110b10f450030001000c54880f4640714031070090301e000c1d001c0c200c220306000044240c3c50305e02200030f02070b44d0780c3d20b41e1030041052086507080c2c0c0090340d040841c141c00c0a040090200b04036031083c0b882074000c4c0f07004002d52000d070301801800100e0f01e103d010145115060110100e49a492200205a00c0c1041d001d900b075800115641ca100030140c00420b43c0c0d0700c803400d00030040d6203101c5e00c0d81c1001001d110241481e0003211035804444200e03074081da2941d0300d0300b07040e420500c81ea03000d000142c1c00030940951610b0940150420005942000c5042c040c40c0c0c00754022100c0b10f14404c0e0540c0200185080105042d60100d0300502010341012003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 799519181 1250 799517931 799517969
    0x13020d4107090b03070b0703180e060906031f0f0e0106270c050a03021c06080303060a08060f0a0e0703050a0803250e01050c0a2f10051c06 61
    0x2414100c420154034640100394020071005603612070980c00102c003500518015042c40e070716a026910915003a07060040901d4181c182074480710400026088585003125142003c40c103101380c00501910700352194000c00755110001905078a09002d04d402070b98003189900c40114424020b28640100b0300081d4245080410801840d8080c2c001d0100b1050b50340c1040c1000d0444c440407a600e15100c400029420401c07400c14920907000750201c1070244e00354282070f0394110b2184d8121005039008031207c0d0404800c01003e03141001c0c0603001000d003400070784a00c0c9818143c40941100041400a0203a40e42c1401c58800c1020040c1c1c501070340d4003030207c4c1c8811040e424071403540e400888000c0c00c801c4005c46404008201034111190709000d588415501c0d40c403000066890390091080e481d164800e9401070000314501054071119201c0510883c2010f448494540258080c04090b0500942100352141c44856210007114182d008400304070314440d13402d02d1038130003410007640701070410407441031200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 799520431 1250 799519181 799519283
    0xa120807121a030c100c15110a0201050106080c310e0f042603040201031a0d0303050f06330409020307020f100605060417010608030f0d0513020d 64
    0x40703482c10045003161208007184041124000b6210f0f41000042c030b410a9100008000d840300c02108028004042095542c12001c0c03615600020321041c0103130744440c010082113030850710407600421070b4441c2c0c031701d00080e0741e0304000c01c02418040d0700071054400281c0e009040f204488840a40070b080320f40b24003402c0840d2420000c04080d60700f9609260080b11002400e140301e020301a2602e2020141130656595400560051040d80d030415202c40d00001036a9803036440b0500103104500ca5180003907a4200110b00030200c850060131640076110701c030f803960081e410400c2d04070f803940400c050500e6448080302d100d00b5203000d682d02c5403c2490010042c401c5598010078252402c0402ca400c503003c0000c1180b03c8001d0740c645204098016004202c00d100c84983c120002d034030608803000114189139904491884c643c0a180000c0b651305001c9070700a40c0d0011400f410340c100c0640c19401038102c40c950001183c82a48190042c01406217083c501c4041d1101048030114192451001d210011448844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 799521681 1250 799520431 799520471
    0xe0303160501111b0f0718180b0a06090b191a130f030219050603070f05040503060a090c091b0804060b0a0303030c0201060506030c040b0f04090501030516080a12080712 74
    0x10410b140280c1e64070350000300d4002205801c5130705020300d005038207840070712000062003100c65000114003006844004140c0314103105028048ac000c000580714a4080341d0300440e928248040e00ca019040a800000c2840d091640b00b5110690300000c9411071100e0020920306c0380c403001d041d58285124000640240501d828002c4900958501d43c4004e01244000444025030080341c0d4021014400700707403003a20a075003d6422070b8039030511030f140c1921080001d00e4248100c440b51007842d210802801005409680349008002d103410900ca43e0a440c001d43c40d41c0014412181d0401103d140010240715a681117105009005824202c00b15142c0c10020040c00380001e03810301542c20100300003820b08201c1c00300c0c0e208007400ca41c103900707003420003540c43d140d0f50244211200000050101203032150361446405d00940c03054004111030011480f40784144851070748944a00c0e0071124a10010603501d440302100d009041c0303401e441a948006095070f0701c00e00150240340d8070340307490035074140540d6441030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 799522931 1250 799521681 799521727
    0x6130e0703060f0e0a1101050f041403070e0f060607021507060903020d09030203030904050a02120c0403020a120b0604050403021914060c030403050a080a23070e010e030316050111 79
    0x512030a03141c3c801402c01d6078a015260b241590180c050b002c0829080e0001c800008014940b241c42c000c40d0800c804826000f541218003100744c0c0140b007070150f20341000036000a0204109185807450315400f0748107031440003003281d40100c0c1c0000d0300340110b6035030403080c80900c083c0d40e11060b1141c540d401c01400a05040408401601c556003000b0040d500034014542202da00800a514200202c414880030b010080c00d40030005400f030202401d03048004804503c218088030b9401e440703d2948c0104091503c595019034224114265880041207101c0c072801c3d806102541d0101d842d03140c0d4a001c92410f0041c074030303035540e44602c130140408002d6155401110801c1820480e041a111410807411901c81074800601150381044140d103400c0c010011240c2c450551680007544a81b070800c401130f0a0b0010441049481000b401c11051640040540c821150f080c80c0c264078458580340882d42e81d00c00e21041c0d2a00001c440058010001300b50810140030141441c41074844c001078044606403040302c29 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 799524181 1250 799522931 799522943
    0x30325030e19061124041502030f0a09020a03080a090305010b09010e180a390302031905031b0d02060915070e0102150f01080f01090b070806130e0703 66
    0x50101060301c2c01502e0214500000c148041d0114a000015111181d0303000041186000c4e1111240780305101140841c400c842d845841e00d280c1c80e0501d0700ca40c0c44005250a1900c15105100b4010109001c6c040164051a0340d980042e10b00d007180005070006c41150320041541c0c0c0e000810390035096108443c602142c0c800c000910138400c4030810070021450900640441e000084005500e01399403001c580d05421184098070f16226032503c40d01080394510703034001101c604040560b82c507004c81c0c190044130a0500030f054101300742907500081c1c07282e010280301e074582a02000c107181030180a004a56034440c00c008504004580c00c0701580c1c40d505042283c0d005400740a0000d0034a80740424800c0c03d001c81502d020a03151748050341030b602088994503513030451207030342544102c0b1000404218005c0c0c074150381d82e00701985040f54a600c1c01600900d0050720b80d040061000c0002c41820320b0b03d8010300c050401d541c059541c4008074522042440c142074580b820815110003c88004c00e814054a00842c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 799525431 1250 799524181 799524197
    0xa06051c020906042301060c200d060f020c2b1403040204050c0403080c1c231608040e0a06170a02040c020f1506090f07050f03040203032503 62
    0x620346024289601806074100c0303012000603039245402c0d070001801040588a0311040c1405508480303100009800440100d010f403660001032150151301300110504c10300018401144050200d120b444000c00002d02c807607110326001802c0290358041d03a195510810840c3e00c645218814030300203480503010b103800508981404100c0354401c07224003981802c3c2d00522495038481c0d50a01008200080001c403018401740804400240c100c4010491014000002c180d10151050031a50b520506071503c42406074010004009246c0c8030340c8010601d41c1201626103c0034041c0c4895040e002d0a03600030041075000030046400c40107000124020a442d41c001c000c05521381c81400304541520b05120000d0740a04140300051a05412030305c4003034210300c15034a0b801c1405c940d003894000600101c0744004102c03000c1143e64181720000503444090b55260514905041c50702428a00c01c0300c241d030015901c0000001c00f50348040007140c00c1c0138130414110b410800256000c0c503035880b2241086001440c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 799526681 1250 799525431 799525459
    0x11808090907020f0304060c0c05060a080402030115050d020402070204060f1502070602032505070e01171902180411181611070b070609230f030a081512060a0605 71
    0x640040b426504d400114601b40c00d00300255008213800c03030212046407800394003103000e4907100041d00748420903455031101820309104160945020320b034560881e8200c01030800c201d6031908402a501a010b8034010b03900d094900118000e02190303003007281d149814020006902000c8100c0ca44002030070340c00c0e10141520340c402240c0342e12940b40701c040442c0c0b2980911840d008051040d540c0644141c0480c0c5145968110301044403000342d010b00e6140404044100040c0f40520070020b03a07007161080740302041003e038009002d0f580c0001c1d08025020502c000101004021a00d40c0f507088402014500c48000400059070200d030200c07491000d140e06d0500344030490703020381c400c0800c0058410180c45010b081400d150714580040c02c0a4805588400c11200400d00516460410206080c0e901c030074444012822071030607070b004285140c294410080d01d029164003404150f04060b5440c0c1e4010859101000140c040f441c80d41184414000c65061241ca981c513039010742e041300da080d542480742c00c0c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 799527931 1250 799526681 799526683
    0x3020913020a080706050d051e0a06090605091b0309150c1e0a141c0608010e06010f2102010c12270303052d030403030504030914060a030e01180809090702 68
    0x140c0c0c40f03840301180c0180a101c487d04416007000b40e010000d50880701907810f20800f0300d211110107948202d00036554170310138004801d15002e24400350006581140d042e041854412101c0004016030320030b1280c010010441841e018410034400c80504481c0b0081403d004068046607402800c2da9014450200e280d52003143e8180300351540c12410352200d490804041070040310781d910048250a030030520074103400a4002501ca000701a0081ca000001c1003460b074240d117071074004103800c0301e150183d000c1010000c0801c3d00c91a030900d0018840c80000020003440140c80724622910020004990906005c5480d5031102010000c1c0c01081e000d090039152841101604401074000640001c13420000c8a8400402010004408001c6407441d0450700060848201c5074005540c22030029403107a0502c814503a00210010280034441c05421320070f203041303000400c0ea20030002ca00041c5600e4040311007800000b0f6010b104601c420032041c0c06a900946094210707a800700c4100e0703116038140c501052240384 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 799529181 1250 799527931 799527943
    0xc013306030504080306010f030b130204090509010501080a0f020105091518010f0e150d051905010f15030b040e031801030e06010e04080d061d1608040206040b09040603020913020a08 80
    0x2401c00f0f00c1c9442d46d2100401117507469001000f0009140d124003490019480e085c50a13280310f070343c440b0016112810181d04100380d82c806404214640c1c10305005008903000807504014207036114454921403651880141c03440c0c0030b0b90348025030003081c1c0702c1440d640c0b5203c1d400801c1150141700041a85d061030800644088103803c0300c035000640303c18020080c500b4104203034440c01c411500d0742420511004c07a030806440c003c0700d80912503009a031051a61200c18010f90f409020180713905d0111034246203524040c0314265603108201034544c1d400280b03d480d140d2004070a10f010b42e05807a542e41490100112180368140b845000900d0000280703080c0101244840c162001c00d10091413030340b599181e40d200f50b040400c016110680d6400d000607854440780152030b42c1070040400041c6840c1181030071240b00c4110406034203105c412410080181d46480844068600da082d18030303160f880400c0800d006122542000b50040421000e200600b21130803810042584216403803084a521021030f5910340c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 799530431 1250 799529181 799529183
    0x29040c090b03150a0b0c010b030609070e16120e011a01051303290108010b2e05031003020a0b2230050d09090c02070b030109020c013306030504 63
    0x51000c0c404103140a010043c56016070030010481c83c4441d032a001d441c04c4541c00080348190b140e551342e1100d031080c101440b9083d44041076034041c100300b91502400c900c40da003004108001c0000036038540200c503400784001d00703c0780d0782400c0108051003825900900070005090142c1c0c02c8a16245107041c0c541c40784c2c3c1154101e9884000e0032012a1842c0c1c3c490000c841482c187c00da07000101023210610030400414103000f020107000104045003254140072041d1042540b000c0b004082c00300d40780c402c117119240b004021210b850140d589a17903100240301544403640000358040700f0301c03e000448500c85e43c054203c00d403a200d4540340c0051910340512184400e842524554280041802054618417442c85007940441c44941e0300d2140b80d545690601c0d41499017900815503201e400c1c004200707a0311034030f02080d145000510f0079609181c42e1844c1030205100d03101555400040c2c54643c10029000310b685501c1c5d04100d103071100c0140070554807014804802070306c4c4000302c1c100020102d02c640a454022 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 799531681 1250 799530431 799530449
    0xa020f07021528081b120403050c01090b0105030d05090d0b0a090803041a0f010515090d05010c02030318072102030715020d030b0f2229040c09 63
    0x9015500744030000c030325007403a100700c0750003885044402400d103c1d400f950142d18400202200b8001c0501800b2010041d005005503000a209903e030740200f507045514a940680e8100b0b4140d036580b504848510030100040221350808000000f044443c03241141a0f910403402c2e18032040112600312403034050b500c0d03000d5000400804420102740b01c1c03400707150802e001d0306012540d400b191b2248080c82c1e2080d01c0849201c1888a400c1044049007400d2a41001d1640400d004c254501400180100c44040c6007140001c00041d06c4100b940e201c0701d0584c0c0e02d90748070000f071040000206010f51250000c956501c4000c07041065442441008a0808182c9041003182d20050200340c480c4442400e50790303c22a014850028041060010541d1071040c08907694010040f60784030050080a0300c0300081403034011102c002895040d41d4801c40000260010440c400407828114400000900101c9062203032460385500071744808000401003155021041d94140814100c400040f50300b54001d2060b5000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 799532931 1250 799531681 799531687
    0x60510090f1a190212070c0602061e15040e0f0a0c094a071403010203040506060f030304030b190c022d030f0d0204082407081b030f0a050a020f 63
    0x1039001015001ca04544620496510480004841700b40c0ea005040c00c1c0c1d40307140313019020400168100714032940311010400034006000d14003e0b950a015000d032066036400c00030010013280741c9076a44a4070410050744d00b101d9907801044406070700ea8003561420b6640119081021414900b54021513030311403140d2045210840e50344401601444010344d0700c03101540307401141d01c1c800c1c040100c1d804103182c1107805400305a2130b01d800e0300001c402c1303889218003c0e4010300411011640c0481c81a52018080d1b40062001003d840024154411600010712000e41c05050014070340c44601c081c400c200b06050100069640d007803069a9450351001c0180fa0000445400c0c42600380c1c01d0940d84040e8085802c9906259410a034584141c000300d00c5a150164003141c1004924010000e031101d08060800c40c0d440810010f68a00b2151801006031043c0314003500030807440b40304001421401071121750015102d0502c5002510404015036071265840c0c1040b01007125491584202c86c101c0c0d03065201545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 799534181 1250 799532931 799532947
    0xc08030106031806052e0b09040b0103140108060f07111e1f1a060703020601031e140d1205060109050927030c010e070e0105060904060510090f1a 64
    0x1000c0c00110f00212524040458441c00107005401001c0c0a5005502c241850b250400383d254041a01d44403806811902c84200b00b0042e1004411203600f5041500d01151414032400141d003d072000003c90340310003c0c8080002055440824918040d012100c200b801a0305c039903400325600200260302c81816080001d1201d420002c4101c1d488544003100c3c00d4914000e01340e250b0300c10106482845021140c0c98224010b4244001860450b800c001111602c0c10144c1c1a2002940c6600500000f041081034032110800c00c1708543c21004025800360650201880d81107040707448800e49041c1e1b002184580000701c480840b180115449404c06a607103911b0686000100050500041c241c20354103405161210000000d80d1458a900c1c1e02103401550307905007015042c1e003115240c1c48400550740104405100c0300c070107100c03a641150011503c590b00c41d41c107080010000c024942c8007541c480c04040300103550b2a040403410044840c0072000e0101d16540354a03201d5a10060310040300b841c00200300c401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 799535431 1250 799534181 799534187
    0x2070e0a140c0a0201090219050901050d030806010c080903010504060902120106051e010513030b18030a080115030b090a360f0c1208041815030624030602070308070c08030106 77
    0x420f024001d480007150002d4103401003061f03420340340500c202c0c4110324a01800780d03080101401d03004240994031403041d0352a80c3c40041003120090510380c1040305c2004007d0920110605880014a00030020089810289807000003020b1000c4120300522110304c040d00307064010f110f10421120080c040c4400e04007020384c88101d000001c04054103000060003042044280d071603660024500c0340d4082c64032414952000030300714030080790501c040d6208000306c40354268090740f0541129100c2c408503001400e060426005031641030115038010205c001040708580c15904900940580c0c1c0051400d8404059051188d010341154194108914468410f001400c0c1d5840a031516014003607002d040c549400428454107014542503a0380c40300450309000003509802c004403402c411100800c00b51503034901c42c0f00030740c51901c0064116039a9041e110908021503650b0b442804000c0b444445003901c03490002c00030341010805500007040f050002f244e682c0202178080165800956031b0341560318221b802c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 799536681 1250 799535431 799535437
    0x405060103330e0a410a091b18020906160c0f080a0309050d03020a0219050a0605041815170a060203071d0f0a17190302070e0a140c 58
    0x200260100910300040d940900f2000d035004000140000c1800d01d074503100c021456100202c074a1030104000311440312012064458200714448545165503640ca200200d4000c0840d19000f80a81d2104012091000c40c1c04540d43d00f5511100c240300301088086500e4012801241e5030990448005c00500040686424404004501c0786d980707424101d0700e8400200810410303a1002d069607210020301e00415802101c45000760101f940c0012410b031040c0c40c000d54400512401030302903c0507640c5005c41702c0315022000054403010340402e003450382d1610b009180d64071078461008019040e610843c40700c90103024550100202c003084070300d00c1e0306040c3d03c008071902c00c8081090610850f0050030001e41c51740085c1d40b16080a0700c854051405403142e4021035420010014815000103008188690703515640700d0685030203150240c04041d0100100d4580b440042149903465942c60300c0c40c041541c0083d034902610688114000151038109443c015a0004219080d05515a400040030f00a0940c05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 799537931 1250 799536681 799536761
    0x6030b0609040c080f1303050a030e010f0c02070501031b02030301061b0506010e01170609120a0201110c0601031b0f090c05070b0a0e1513020f0a0317090405060103 72
    0x5540c68a4052400034040b691038818400104d0001d4003042403c1e400c00c50341c558003403000395100380108041d0368010010b202e60410002490b6030380321812407075042544100c101c1c102c0903400b08101685240c01070b50300e501511407140020305051440c1d8046c607201d0030cd980313507170300e42d030021421a42070100c1603419041100050018030502d04242021400c01c020740c50003481140309da0081d0754180700e0b004000c4088422a138045a02c1134080c0941c0c0baa001400100d005180380c001034403148144412409450604440e04420101050181604501040d1141224822242c40754000308104480c11068210722858ad0503028600c01044249840e400041d42e5864038a42546044070075a40c20b032484800341e82c00100725540b00c00c00c08003440108200c910b500f130030564010b940c0c0352101d1040101c03245400700a01a0500007800d0030310352502068180695404016410103248450841d1210303004080281e219608140100f035642d4001c1c428203451030750041102c40d1343c00740e19400010026410003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 799539181 1250 799537931 799537939
    0x21041202090c120c070218070923030a050105070306080a030804030f030b041b0207050627060f0c01050403020d0504031223070812010b13061b1a060102210406030b 72
    0x10741810f40d0800000d0b9204400955a4580310003860040c444814203140101c10f04480c00c10a02036080d80144404040703448144610300c0c11042d254002703c84c250300080c020f03014802d4182010802406402541c400e622668082103903030741d5003054540d034041c0048040d000c1015100458003092048801034441201340c00d022442c030081a001c20110707003014052b40b030000e0a203040b0f074407407aa05201c0c0700010602140c2c4a420300746880140d16404a03030031020090215005a800300680701c04083e1055414440119520f41c24a0200f00d03000e440c00300d5084005020b1107055405c800d00990541d070640c2c3e0040b004000c0c0b440c9001c411b90381f845a14511500006084442c804d0304110f9100a000c1300d8130849074039449900e20b201203000d05006030032100d26010103008599012880310110000c441003803420249e02c0459845c41400c03840c1d50074002e000d02c0000030f01000150b060880071801140282c2c2107800c1800d64403c040d018424020220160002c20402041040d00c41d8000c4690210020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799540431 1250 799539181 799539187
    0x7020612101706070f0201020901050f280c1e111309080c03070c0b030114090411090c03070e0d02032d0f07060909090308061e030109030221041202090c 67
    0x30100400350304007540c4101160b03c0036040104540d44011004900400c9000a5003484c4200001a0040c01040300c3d000c0485404140a220403c0c01c004040e141703102244001a58110a03070000c0440003510015181d80246489811300c24500d44a41c0b26402d40108151070b0105c1804204800810300010001106840c0d003000002300c1c96400090482e10742110080da034400340ca103440c8444043c15802116039400030307c0108400220303454001020300e03003240d50100c40d9440d8a4266085142c410909030040c2c882800c101f1600d190307030002c501443c500c1d2903a0031000c66143c01c0042189400c48001d4054000c443e080705542d203a1404c000c486000500d41030790180b0010580343c90500310381000b089950202070704000003500190301e08054005124144161481624041c0684030b000d0000c40c040c0b84400c0341709503a0340e000810b4040700b00c4018000d00845400307081c02985c2d10b05500700107480800401c099860458003c045408503026601e81e2640c80400d502003242003a0018090015a00c0070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799541681 1250 799540431 799540439
    0x10207060c03021b15012c01060e150315040f110c01020901090b210703111b060109090b0c0c03090603180d08010b030612010e03130513020702061210 66
    0x24040c51250904903a40107807190701030412070781c4146120070007600940002d12010281c101c817003600340c15200c201000905520444060034805510081c403d07036406089000410303007039070010743c00d084010120b501100802e024099503009100580e140b0103241c2142080d40f60034205504544d00140f007805002800c03d001c4222002e040e4044401005c55941c001201c851560300013100401814a07040e04171301345101001034007a084404000c008040b42c0d504001032030340d41710380c000c680c884104903909629040100d0443d03d56032400410f00b021030207140c0001c18080804c0c8203018409420001200c2e2548a140304900b440c3e00c812005005400100a815116115440154041d812105401328500e0400070007906000e1554450403c00c02e10f4401045081c01c144c040d80d800800c1140c1c15510000c1005483d4010100140c82e8039803404081281104403080b140003030126142540c00d05c1400c1144926107007240314214000391b01080a02203034286034102180c103607005095091500300a80c403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799542931 1250 799541681 799541693
    0x151c03020c0301020f09030601080a0b150a050a0b1201090b0d060f090f120f0f0801090c0926010b030a0314070809030a0f060b01020c0901180f050709060212130506030603010207 78
    0x405c1c5020309904a0000725601c031420100a01c500502546018000a801642e1144445840507004000c1c06215400f4078155940d181d508000400340240420403031591104488000d07000106d0041d600301d80340000055565041c0600900f40e40010700d4440a50714a035a030100801010000841003550749540c1e800207810446a90140c84c01002c1d40e8070340740c04040340248060754035070039182040104d043d03640302e13a40c2200320203065550000f0080307800701480350704a451840a9209490b000016024100380d080400c1062242c07141e624000d002040c1d12505065a4040640300200003411001442e5403506402020304041c80c441e0600a24088030400040e1070190414029134080710704101000801006200780d402052080c000f514207070058500003a5586414400c000f81c04102070341d20442017a5540c45400030360308418003041a41000500240010800e00401c00503214038808580c2d500511400c0d501d81202c61078881030704604202c10b004803138101400540d01990240120400251 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799544181 1250 799542931 799542937
    0x60403050f07080703030e0906010215040819020f07033008070314040b06060a050d05010314070501050408060a150305030d200c0705040b031c090e151c03020c030102 73
    0x40188001e00090031a140d1041c00c2c601c05600c00c0c0741c03580c0500800c00010750040c9401142c603034121045613841d51040011303030820303441d100307072b003072194101d504100801540d8000350080c0f25409105100300c900047c010f980c1c910100c44203010135407000102700b000545003021241e1200c03440b03c401f43c1071621228001c0700c00203002c5172900881c58020400c0310b03160f410711078082000c10441031480b080c1015140d0351002c0700003905150084500080d00303582c99006104442500c10f8800d4100001e69584c01c254031072480c64620300c0c015000d0808001003a42c814410f48060b82c034000050006900c8080d4111300400840c4940c1c03040c0f50034080300002085085c0080d0880c01c43c024000304030188074001e04141c0c0341c070703c0500b00240c81d01448580680040054140160b4000740c4000507080281000607103410210840e000c601d11002007000125a0700c100d160b001ca03514a0398102142c1c80702c220031094014403c0521b40c10178898611450a43c4803c8407480c0101d009005a41d50301502c200401d0980e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799545431 1250 799544181 799544183
    0x40f03020f0604080a030b0a05010e0904030e19050901050d0503040e070216091407110307032313080c01020a1a06010314090a0c080105060a17070b0a0804060b010809030a0c05010b060403 82
    0x1000411240c05c400d41501652445035801c83e140141641064000b030700b9040c0820029004003030603c005810180641d44e07017030600000804620000302c0c14000c00c030743c4521a018003030081c0300c61400014030f400c02e0000c0004990380400510306141c2440c802140240004054104511880c4421103040c9106440d020142654120118440140c0405010004000b0304847c08004400003d4500b00b4404010b5503c503d91520b010114442d48014000300b4000340311010441c5140084c0b80c10a08007049994400c90340303690141c6044a016000582e150f80b0310240183c81d88401002801c01c6c0f800d03112005a1258050400290b4110165200c184140044401004560007542d01c4418000c41038003c0000b8540f4400070301c0107103042e4010608442d035030b104104e00015100c00400c0c01220500c1a0070140440c0200c0702d031103054a0100404040c81640d090310b03031602d881c3c0840d205510a001417807260210304000d500e002c001903c200c0b407011001e00141c405550305c3c40d000c841a59a0700c0104021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799546681 1250 799545431 799545443
    0x2070518090f06040209160e04020d0203070f05030103020f040506031509072603040b0a05161505010503010c0f20011d070b0a020a02040f1418011a0306040f03020f0604 74
    0x1031401d03111103481c0210024074184658419010480182ea0300c0c0c0110780c3c0710006900d52151070400802c1610380c20703c003645607503201f8000308070b200381c05003240c0c060340c810452507444c0a0701520300541035416220070301010303411180340e600034512810103400058218101404a0f42841000b0004136182d41e004e0f50740c154070307800500081020a0481035004c2040c1080940749000d4080c0840e803a580c3d12483c402c1e1020440003050442c5440e0040007a90a400f00c032400804002c010b0745000280b821300c07000d2504007685040004a0341d42014803544401000075202c070215800c12000c1602d0803400149001c80d041170010040354243c80c2030141446584428260b4000d0f098030501040c181103540d000b0030341d0b551007440483c00c61640040c40d201c9040d01958009484416001e01d8009050310b880d40c03011100b846800e2000d2071146d841001c5108410750000c02c040084000c2c10b04d00c0c21003001d2280e602d5803184000c180030901076203218165500c00e0045580b5901d841e01910f0401d24111425644 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799547931 1250 799546681 799546729
    0x70b280c24140a0b01050a0206010302090403090503030d06090f0c0225080d08041101020c011d0a0306060608150307291201030f1b0b191205162a0f03020705 69
    0x881082c010304c01100d1007401c107141040c0ca10310f40290f03614814030010344036629100205060600400d11040a040c02400f0340b50b80c2c0f03c0442641020300614410b50015910b01181c1c0960920640308103074860034660301821404410445241080040111070314050b04100f800003650b03102003010149072651a21080d5140c42c0c1410466981c41d60a20120b040d5001603214019981c0e010361184114450303007400035603001c000c80200b40b0811003034200410140c40d11602180040d080010944190b00c009482262020060141521030303040f4440c0420354581d00c4400000d42e042ca00d0b541501e064003003045802e005404078503001410f0207901c10385880700865200001e100041e44030000241e51050071408503460324141c2c2c3e81070302c14141401d0055100340c41d0700e41a240701d032840e0854413548000611440c288103194200c00d4048201ea0008100340030f0a58115420300c285254a00c001d80c1000c21807154552510396140e240480d0440450003018004101655200e81d4007003079026000035409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799549181 1250 799547931 799547941
    0x3120201111801142a03090a0e04022d01030b0303090d061d2406030312090601090c02062a0d02040303030617030705060c09010201060305070b280c2414 67
    0x452552010340050210300c0810401012941d20614203048003505c4400d84010882c1a40460840c0211851268801680400020031704440642c2500a900845a001800d00700b1012581101c4005c036111807a4440c0100a0007150f000c1d0344070703910002e07010b01920703c2c221070308001949490303455408441a41c1c0e0360700f841a580044400d11160041800000d11001c0c0c0200070740d10f15100488022500000100300180054605000ba6254150a2001c003081030030007500284d180d2100f4081c051501d1b15000741001600d20026000380241c21511822030480101c003019540354034444400e01c2401420402004001200c2c40140b000798004d940024003d03003040080010851584000c804230b40c001d02c08070000ca83c011a0880e0400500050550b4908407980141d02404c1c42c1e50024206004544c8000b85d501107010040800403544000074455410210101c01d000c0d11080402c00020005414440002c1900c0803400a40940d01c0c04103106150307a44142c0b040d106040c041c2c110302106001400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799550431 1250 799549181 799549187
    0x2190f29040b160804030503031003200109260f010e01060b0910030f06090204061d19061d0604061d09130b1306020f030106140901050403120201111801 67
    0x11008204031219240c10300e4001450761901811000180d0f4a0745000c1d00c01c108510b070380c203c41c025580709046e00e8480c5041000c1c10b510310098030090b5058081d61410041040d1103400e8540c149205841d28501c00b030a24103140c1c45017a4030b0311080c1c440030088040420b110381c20042824a8400fa9002090901326100c5160a503407090313011403501c40c420700400c802c0d551040048107028070309140009991850301449400b91000b07502040703000d480000e0104806038400c2c40517400302000e4028181d504024418068441d548110106010b01e00420030b000092080e80001e00350104054110000c80d001d000040305a4002da0041012800c03220825241d50240e1681001c42d101c11105440c46203080020210700001a0310028041504580003504000030300c1d030b00d506040d070001c604545801c24244050b155074028054400415402815104407244490485042d500180d465904080c43c42e0b503407400c1c1010051109003903540b1804220941800103015140a810000102e51510062030002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799551681 1250 799550431 799550489
    0x1203040c0311010f0503011e090c020714060a0507081b1204050301051806190609061d0a0c020318010e0306040302010c1710051014071104050702030306030a02190f 72
    0x1041c1880042c2105221984c3c021046d03070704484c4450302c0c0e1180344600d507040325190105908400031440c50207450403c42540051007a06503524101081c1050844608112041c0a0495a0b01c009001001480b000401160103007040ed411001d02d00c018a4000b8180c0381024102100c50008103c0414104001e2909001d0395401102415800220505024065032103c82c01040301e11494070110200d4501206640000002c100d001c004121058480d1006c0f000d480300d12910350b081313a20000c08214140454410a42a8102b80e0021403415450007924004410f0f580c0d445418041d43c80040a110b07141442020b200320700c258000130305205030250182c002000c007010807014040c01e808000321052428404030554004442c46058054440d5084500031780b001e2803151941000310b041020444440800b41442d001100c00340a142e803080000c03a560b000c00c6610381d5055102d421400c0144c103190302160b424030003240c40b40d9049074540c6561164000e060f441025031140369124003404514841d05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799552931 1250 799551681 799551713
    0x30c020a3f03020d11120c031902060919080702060a08220c0b0d0e0703140606090c030a0506060903010c02030705010b0d03020d050f04090e010504020a060513171203040c03 76
    0x7410200d50142c500039640d10030000c0e860240f0402c8501506650343c10480d002203c4003903180140d0381d880c00300507907440381c008603040c402550383c4070004001e02d40003180c00c1c2c0c40384248000a0030f0094841500001c0b10341d02c0241901d6000f4100300c0751000d40c07914070040429401c1500d9008013810000140e00441c41c803000515aa040084c800304000b0f6054641340044691000030640c5070340c02888001c00230920180e82c01458410b01a00000700071700187d0300c1804584c00020b540035903441c0024001022001c81e01c0b0400d0324404c20008410f8a41c0c0c0d48441e800060141c04039090152100c0805d085601804a00b07016030700c00b18090080002c00d00880a24020a4801103407170f40d815507029564005004240090000100c0c040c01c89140b07500c2a01e004091340e034030500903411440c00f454003c0c42e0617a410782c0141045c88001c0381d441d000c0c5c4121111100c2d42c0c0b2001110600e0035142000501250b018041d4034003413040004814007080c00510b0085001d10703003207130a0515521740720040c0300394007030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799554181 1250 799552931 799553039
    0x6031a060a171504020604090509100f0519021308070f081006030809130b060a120b040506060d0e030702090c041502121b0316053304030c020a 63
    0x5401c1202c01240502800490f80c215000ba51114400581980541e03000300e134407540341804218865400051100044d21621010442c0b145242c0c84281928401c890101c0030f2402c82c100c9a580003040e41c010304c001010320202c0f4040c02d464000190410602c0d9008850501150070144040b510034001c840c10583e40500c01c05c4003d1a641e1026060b018051155100304d0f1301040502d0703071803100e40014080482c000d010583c0c0d00a880c0c8050054040a220340d03540c240780c40b4844d18a81082c3c0304250240400411060501e0418414071703000d0f20442035000158082403010701d005071104420503010305820b0b01d08a440c2da0070103c45001741041c404801045501c00030000311181d146804943c4183d030540c52000c4603840d115000d9142d8031900c10310440350640072004109000703005c14041c2c1c0d0300d020590101c1e1801d5201503e00c1100c04000f9450100080c103001060000e801076a00c1e44020b880034000740c5400c0d40da0302e40d20344490b0601211020001c421041c1c00c03807820b4020384150304508906 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799555431 1250 799554181 799554209
    0x6110418230603030c010f0c0e040e100c1110090b0f0f01140d02031b0a0f050915030c030f15011205031204080c0727050408190306031a060a 62
    0x481c11009500c119001c4401c001c0c2010045011503c041c002c4460030000c01c0c0080c06070ba051000c543c1c00820f800004940050701800c4004010700d414002c6003454000c250003091401110011007006043c2c80b90600300703001080441344039403c0d00388004540c00500e60700c00160b0300890709001d005994001c0031024414844820031400300d0070405801c3c191982d8034107885004d12104c000c20024030346030307a0207940f501c210900c01e00d02210103819803851510070b403820602565194403e044030051343c05200c0e170141002000401103102c0020452105c50000d007110310420492000c00c1c1801c4c481c41d010402600010100c41d00e000505004c580180790008403050448003030389840752240603542140c0160016107000c00c00703200c2c1c44003e4402c4500381c68152481d0a43e5503103458810910f2044003014504080212202c03101c41c0e214152045030442c5402c2d1030800d000c2c4400d2407031048002e0a205040e030b1800c0c0800860100340300c10030f00e4a02a4040380d85070401c081008100a06a44080311070301c480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799556681 1250 799555431 799555451
    0x14010509030406110705060403060e010c05160201030f0b1c031403070c1101020c06030c0d06081b10020a201f02190c030209070c020117010302090c07020d06110418 72
    0x811034048030304500c4d00080c2030500e0030809082036401c2c1d0105034089400700d80881072088991081c0790a061100080040701c0d00342400351224040c0b0341d2002d0303450030181c2c000300255000c3d070403a5030b03030100c09480012140e5040d0005410201105c42814204581c3c0c6062020590011f8a00146c50341c0408500d00314540b80e01c00030b20507040300d08010001b8500321521401640208130445074035900501480d268070341900c0d154000d80020324400d01c0700e410050300007250040881c41d00990203d440b060043c09005000707020303280582a6400085116448109010504804641e1501d0090b41003107440700003040100b190509403241054000b81422000707444a6400241c141c0900e040c3c0321901c0f191014900785540b81038020352020390020803680400600c542e110b400d40c20614400d0302c8808014191000452150707009000080d0000c80c5040428450150b400203441c1c414401002035404c001507503600419184035480b0103036940000b1030103001405d20308200600008250703a00300b001c2c0e142 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799557931 1250 799556681 799556683
    0x81b1f060509160201021b240415020f0d090c0906080303060d060f0e0f03041a1603080411280504020f090603070c02090709050120060a05092814010509 67
    0x3e060302c40b90a40610885503014000e4055641c1c0789030306c0d81d00f10a01503e1404080d02c03518a10320484c0c0301281c1104080c024246031500d1400349400a5004800c0c40984006000070340c400054000044000d006140750007007070b405484040d80c858004103261518085244041e2102c3e500f1404442c0c0003401080340e5901e41d0b08400001c10303040b890104aa165100341c0398020120003c0c9079441303000311222948840c400200400c01c40341840315040c1000c3c0794101a510034014030303682d210003070041b005000103e8030400c60307035070824000c0f0104600c85609200040d80720411038272101d05074200c080142d511038650b4841400514040e2020361074010f1080f1400017512860740d0b894403900300800400c5585106900110f0b00a0b8050090607190900d100081c0c4545c00038880d26002440b0b28078003a141c03484858102e40d205007100000d207000c1c1c54914541d07000e0a4000c2544c2d22601c036002e64590580c81c403041403980d80214428410034403140c1d051000d02e581700c010840c0d80f683e06000030300040c03201c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799559181 1250 799557931 799557949
    0x40e06061606090c051c1b180b150d0b09060916031d0a0804140402090a14040f051501030e0708070b030702122a010c020613081b1f0605 60
    0xa030002d0009000c84051415505409450f0007003030b04943c12425911310b001c038540441c0c131480d00503003030b000d86410803141d9041e404145009500c0401241c203500408076207136400400300c51400a2400000c0c440c5011002d40355003042c0100300b145922092100302e2824800b400a8000f1010340ea41c001c0752401d41012030244285500a20400d80d54102c0808902015441e824001214109a80d0580b07034500b401c10341b5030454060324165400801c40c0e440186441c1c822550480b6029150081c05460240c820170380041040381d1603000b5443d4507031036031503020501c9154400c9118079111a80d80754190700040446604d91404c01e0140e000300e20a0141d400001015000c60340303076070784856407036071005012410310000750b91a0240d0700010a010003041c03040351041802901c040071412050202000c102e09952450304034a02581090000c50544404e032003060907403a014040341441c06105e2814000301c903566910407015034015980303a24110f00307884455840112081c0003417004070b041600080480d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799560431 1250 799559181 799559183
    0x5120d0504150c0f03171e150105091504060f080103020f040c180303020724171305060c030403080f151027030c061103032712040e060616 61
    0x24901c040510703c2c880c0c02d5038519103500c001c40c403240780c0c401e1a01800045101e0b07001312080303001000084240c11645c65040e084003c00e02d0014540d1503400f1646c400b21741c00900315040000c2000401240d484003205041001543c25501d90f1b03a41c0351600c0201041071800b007090401612a00410140c0d0769214a403150b004120340008150950040507030300318816066031503403014155130002c18990007080800480e003010002d03421410400200c83e140303c104003161808a5000350105001c0c0b0100380c0321650000c150384c64281100341648510380703401012540d0300f21083c4000104000c01d9804851190000d4001c0007070020703410b00c0003209803090250390400d406604610b080b6a602c92107042482b0450301c00d003001e103481844440f210404807c040c001560544114100080c04502c25032580254a024402860540e00e07261012042da501000050200355a00070240c0c0d1008403c1c8824a065154400f080c0d5545140107204001c6200040240c0e120b103a0600c9024084024044411925 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799561681 1250 799560431 799560449
    0x60414040b0414010f0906051f0807050f04140415080312130b0c070204270314070803090d030c03050112020d330b0409051218030102070c05120d0504 66
    0x2100e481c0c0d000c2802400050082016503d820000103600d0924081c40d00c195521000284034603510b480c28000c401d0b041c401503000410070940f603040d092344590010758021a130751614900c0d18801030b02519103074001e80c000030311100070320301d0f040c05a2038144261540718907591180c1c01d1180c50503641523101d000d02090010308050290001d010b07038283c14441c407030307080e8071a441c0c110380d0800303003250b0302c0c10340029400f2400f4a02d801030420010740342520100b1452445000d04820120f25a8112684800003187c04a1240180700990015400002440c807803219034004054480c0052001400d0340e0390101102c7c01e0601d400d0061104400000c01d440d034003601a00c4031490131046152418022241c1c1d1022070100342c0c03a079445050b802042e101d8602c1702e480380034107200050072942080304449900c070004205a00c580b20141000f18010040d003002a8031a170a540c00d1002400441d0980e404800d0880d584c2c400906d051186181c050800a0304400e58001402000b5002034080e000744503500410081c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799562931 1250 799561681 799561691
    0xa0b03040816051009111f2304080c0102101b03021606050c04061206080c0d1b030503070c1707090e030408010614033304021203210606041404 63
    0x104000c0420007403283e61100407601500a49050b032402040954030031a0103d0015000320340f1032400d02c0e0030b42400c00d842c00303c1a03105e968080043c0c0740c008220440c07000c034080c004480000b4240704d074058002003851101600854a0420009041c5a050391443d40c1942c81c2c007031444914005000070681d07045d5030341001a91f51400c1400c0941c0c00660210042286040104210384240d01401500444400703840b075220000e501d190640a940300790240e00415030020a00209918280780a20301c00d500450007110007000c0b6081032a103c804c542c00981c0c05610001d11401000811040c443c000c02c0894000e0380300d07044a040d4503480d01218880d01e444682c42d9080280e483c20284100d03070080403224000c204059540ca66640a1045210114070034011055244422820402451609103298889400200b00464405103c01d0701400c00c3ea0030403040c042c08001c6e200108020305d4100315504821245118034208500b070a03d0041449000b0320092100308649c4030f490b0341d0301000d000c0031100810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799564181 1250 799562931 799562947
    0x70507080405210d1106010b0901081b0c0307060b100f0c0b18151009020304030c1520070203160501140318030f0a0305010e010f0b0c010605130c02010b0a0b030408 72
    0x32808244040c891090003094600e1038141e03044440c042d17010004800f81e82c5c0c140e90b6038035411007500030b440a15000c1044000011080c000c0c284080d0001886584840c1c10207180d10328041c40c50300b000800322045c0e5966594005c072443c0510490818000c07501d4200c00381c840c0c00d030005058084040c401002c42282001041d403490241d124880820152400c9a0441481299600e0860400e503001c4c1640c010b041008101c0503818001c032032065400d0f031a4548030302c4507030b45c501603119208281141c80c580d483d03504080c0c2248004030f08040c4413030711860a440c0c501074010182480f00101450206400b025001c01c496600822480d00024558814a0702ca960f0500c43c0710508031900e610344014040010014540860f4602a11004c1c01030394040000d80c2c2c0320241c2c80d950000a000e0280c50103401034081149010036801404440540b000201d8841d903518041100c00b0b0a89140700c00303198070703040c0d00510194240b16442120004443c4000c20526224140105100141c00035100d4100054461 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799565431 1250 799564181 799564219
    0x50904061103090d09090207031403100e042d02091323031207031413030e130b0f090f04020607031103040b270f040c0c080d05090105070507080405 65
    0x1407241e403035108141e98a280c524012602c8a0702c4000050100e0440350011803e40700ca4401d455602c0d604da00d41d008105050007520006800080c40008818081207012803165441490f403401140318040c080310341800800317003041154030105c002d220380703103270901d5803000da47d40141090b0486101c0d44080b502940c01d040004004c00d8280c24803106000d24050180290000801000260707015006501581c58810084080c1d440c59070504440d00b0b010320110300280495044000d8030341c800e040001800008a0100d0960103583d00c0b00c80f240c9654000b488030074240400e80c0c00f46200c08455078512403034090705040c00d5400c040e1019000d40320109064082500900b40b504038404031404030f1b070b280c0756110f05070788299001c104140780400c0c14807154a45014010b04005a920000781990391038800e1000340070042030b03804150b00c100284802c130300000c540203800504084009000101d01c03450038040040c00d68401900360001c210381049900c0200d212503003a40d01750f40080743c0100c40b02886061350 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799566681 1250 799565431 799565441
    0x15040c09090f0213030c05040c020a11060a09170609010c0201060513150e0c0304020f0a0506190306120501091b030c1e0e0c19140d0b0307090e0f160b0405090406 71
    0x4400c9840c0043d40c0803043c01b41c80800d490440d04211010700110100721400c03a21200840c070020000f1200700601300440c50f181e400750650300803a107040d11056039142c8090b01110800c082da0250713a0009418015540c0080c040c1001c2d91120740000e200f81860031021070b014400c1c03450411096959003140311002d105e03d80c07060000380b141c030842c04c400d81050440380c1c40380d603c2901c0484c4603001c980300a440d2030905890100807504004c04050502101048403400c3d050200110700800d41e0b41c1c080407800f50030845205400500400002504205914188008400600b6154400d83c40743c02d04100142055101805981c0e0034102040a00203540d00002841599048000038030f41d41403c2012860452000d40108a4401740450f0314440e6400e00340c03841c428038048140e101508000990703503180340b0382091505200260480e01c11907a0b60344208112160020400080d810035441c40301082030411070a125400310f0308465081a19262052505c0d11441c07003101d000f0004000001d090100c142c0c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799567931 1250 799566681 799566697
    0x40203030702030a0305040f14130e01090b070f02060a14130507080a0b0f180c0402090f0a090624170a18080d060608160e030a0f05030315040c09090f02 67
    0x1301d44100e1610725000e42603420a00034200d1124011500140700d01c0b030203040061200700a0106025003140d5880b402c0540390322080c801c410740d2220403480000da01d01c00410b10680c52940c0da843c02005400000381800000762083e84428181b1008490f010540301206401c44001250391080280f00e01d0881e040110030341c000640303800358522032070620903520500c5c2d01c50301b109004541c45546405401c1c011140103e072081885c1e010200740d1880d42400e074005c01e0091001401420515013110000350480c0b90768004800703180d15404100030009041611402910800c400300c90b01174041a40189265809600b0079000d20305000031803a40b032241d51020400c005031540c1400d0481c400e0504103055481170000e034204501d0300c0320014915216282c0030b40640092204050b59041780c1030100d5072040348040059050040500c500e0010300040400103280d4131030130145459150000304d00032002c0544d1003c501032410304000b80c41c559409010b440696980030780c0002c0070345052000320001d000300340c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799569181 1250 799567931 799567933
    0x10503100b180a120b0f1302130e0c01020f030f071a04050106031104060f05090411030a030e150a02030d0c20101a03030307030b1503070f08010e091504020303070203 73
    0x2da8040380031200040459680d8291002c10880c0c0c3e6800c004502d00121180250070988480046051000d1056205400200c01400a15034212680000d154145c603036a0381030f040c603542d00950100110600060104070403d002503c41458102840c83d2280300d4050b0084001c003000070300b04200500100c904070803200c0e030035601041e45060300c2c0450081005020546031b40520b0b80000d030080c40c00d4002c0c0015a1941c141c0305801c98a00803e0095a00010788120307030262001c682015aa02e080100b00141800303039440410842c0044207201e840c25100d11118140e903410404161843e03000000c5130030482051000040e40c0e030545004854081c00c4c07524980b0174120f004140c8400c0c15001510201000911608001700c10165182704461510500c481e80c16420030b00000c0d07682030180d4042c10714800050006d1483e204220580400d581c01124107002140300302c3c48080b00c403a405414180501045600da6000d4185060034a5880c2034444494000e182400001411500c0610945403803d901134 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799570431 1250 799569181 799569187
    0x507060507080a050a0510450e0a1101050a230703020f0304031703041a13120e0303040515040f08070e09070f0311060c0703080315010914010503100b 66
    0x5070005005030b8041d40c05052440c10700c004104c0300c9030345106060140242d40d600b96407031031415546d45100c20603140c4051141140a0314540e41c1e8121034601c145c03441504154160580440c4030500c21102010300360103295016072030141c0041c1051419140010003400d240e601c600110108864072588084d45a146401d510303011024110b104010305000c9120342c0a030b4a0915207040291b17941d014074480501030040c0d11004451407103034a0011a0050f00540045080c0c00030300300d960b110250255040c0c9a0215201c4a000910008000b17512074245245042071020382e4003400650380c2d01890041c2c520a01c4041c0c407100c0e5507003190049500900380640c10518036a940d50400d42c0b40d288034803a0115810301e600c000f440c0721a0101d050025130780c250f414084028110344a4a681c80342c603505442d0444030411110100090820046000703512501c2050740d0f034548110320111404404c0da609050001c15a024454a00b800c007000500800c2880c1098403036440081c404a214031661220b000e0403400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799571681 1250 799570431 799570441
    0x50109061121040c0e04030212070305040e0a141b04180b010306080f0601090506060f0706050103020310021309090f081305400e0d0801050906030a02090a050705070605 74
    0x18040d141a01856940d11202400000080c0c1d0010b02150010224a8082c1c010311000552000e61030700036021344119000d0110314618010154030858060340407070320106007040544c50301040035034450000da005200d100352000b24a00c00c42c401500742001c2c25003a289090700406144103480051000d812156080003155175441700905014166500203410020046119140051080619524480140860781c0381c03091400041c4009490582d102100b040300c2030380302040300040e150060240c9070008aa502d1441010b00c4c040802d0010b14040b4014884040c40c2c2c2e051002a104440100d500403402001391b10741580d00115000000704104404112400d110034010104070a071002a03420708082d02099103c103204c41c020344494910321098148010042c03403101510340c00d0301030240000c00c0c1d8801c4c44030dc0c6420b00d00c2c0300c241c4000045045c40108a1490018502d03a04100141d025140c6614150049920218010304c1488415115400b1400c224811422100300e2a00f100080225081c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799572931 1250 799571681 799571711
    0x120709060503010515060d0207061404030201021b1606050702040f02030915090610050f011806020c010e0a03080a181208030403021b03061b0c010f05011505040b0901050705010906 79
    0x40c50103000d0282d0320b08000a28640c0000a880244d02ca008080c9410645040d203020301039841100105d445a131034178100c00300700c0400382401d40918400c0d0005030300d55201011603000c424a4060450326a8030201c00c403e6894042400201600e80910b041c681e40e15180c000700707003e841400c4460401e80c0c800010041d483c1400700d1804440000328148075282c0e2900640343d5540c80003902c1c69100e40e445607504000038a001130311582c070f111060422203503801c520342065034013805d02d07804240980c0000e151000d0303a60340301c0a4811a0b0760100c443c00c035198150740b01d188140c05484082c5c0d042c002c11005503105036001c072400b20020310b0b2443c0300882600c1c4900d8000301c2a00305890482c050f1040d000942035240308021002003448002e0001e100d543e0315481c409a40c03000c202500708941004009030b00340444203016000701d0318002540403c10f54500f000c400e440420982c029004c0120500047c840d0080715011550b01c00310074a0010740750080e90415600410b0304c1300005020a01d420300701140030207 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799574181 1250 799572931 799572941
    0x604050c0102070b04051815040903080912131e0b0d0603230a0605060f040e010c080c030114042706150f120210020319270e0a0b120709 60
    0x100030b90070360301e40320b82d41c2c2551643c1e0b00480c0690740d4002c000354505480400d0b40e140c15a4407420b000a690f00344030209011a08603451172105400040218040040c41c150400c011844400c0b8141c82901d0300e503074555150001401d9000e1459280840d001c0c20b49000b55034039842c0b014181c8001d0321540ca21a070341d0380c0340052041e40710449900224084105d40503800c800c0b0091201041750161540600369940e40d07009010007002c040e440000c6030b60340601901d91b40300707803200a0650400025000c1c03c40c5000b5280702d800070110300ca04081080140704071400c0c0350500c001040161000310314800c0800720f0200140440d007000c1300410004c200c1c0420b01c91150401405082d5524417009050345414100b55201054002d081440d815155141c005040081130200500c0c0c0b00e00c1964100140e16007800f245003904001c190001d08004603000796600a24800008212026204038032240f03000090040400010103030000540e071070b250b0030119101d098804409a8441080c2d40d0541c1d1a042c0e582e005103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799575431 1250 799574181 799574203
    0x3080408070f06030915090203032109010609020702011218021e01030e1207030503130c08070305100b09010b07140304150212070206030f0a09050d030203040b091c0c03050c060405 79
    0x3284803100043c52074040d22501c1251504070000d2061b80010174031000181600150172030705403004002d42103003888610041d010a461070a54160f0720300340444c8050a6508036009110561301c10403801c0f0042c0c3e003080ca00303031282c0d01c1068080760640200e100c3d000c0102e148000a034102041c0300b8003010046080c080b62003660400d890810190301490380b1130355a40150180c41da42a1420041e410103c0e018002441e0f115014605100c1d14610b0703680d030807090134015130014402d540035100c14010011306001c1c02c0e540041001c3c04011011083c40090003404041c030544d8941e07140001e10748180300c042d103003125100c4500b4080f20360307640d41d900d0b080c039020002d030145200500444d40300f400d500702c50100b2103c81540050000741141c4611340c110110100251001603c999100c040600041c003c2c440c0240b06c180d41e0320010385a14190800b4244507200900070402c07904049a400780034249014284052402440c01c13050040c083e1805443da4800d40d0b15070845407044404010421100262007401d030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799576681 1250 799575431 799575449
    0x60e1314041109162a120c2a0302120a0b070e010f02061005120a0606030302010f060e060307090506040e070b0702311a220b0628090308040807 63
    0x2507502c10041300d15090000072150001002410100003484240d0001e20161aa0581c880c40b044419030b81c591080400480910102d035660840400780640b100c5a07501c1d0300c0c0783c440003151980201c0c030102400704e00d23404002d2041c000d202443c0b01d0700e041000590f440c59401040d4101509004e40302400030040c85e86c0c80341c0000c040518004000f440441c82d1401440d101200d05c2d552420801003100e000a6a00341380f0003807203000038440100c1c2c500d00903480114000e03000004c4ea960b04104041c16104290007003451061000c080c4420b586001400c0d904640c000040010107498071400280034040e41d980141c013511031800b0114000200500a0011600c00c8900603036560410342200d20765010441c0c044030343c4c400090070342001d1036a90016070216118240300b81081c005040003e03640501518484a80f50000284010300f211512800b4200c0d10100e40aa04102030101d030700d000800c1080c69400c0e01142d403c440408140207400703c0021310742c4031403560780720b0780c4440302143e903031020381b085441e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799577931 1250 799576681 799576699
    0x121f05030c130903050c061008120c060a0915021305030f010c1d01140c060415110a0c0c0f031208060d0b13111512060406060e13140411 60
    0x440d00d0000340550500c503024180a8880b94401c0d821801804041c0f4207900740002046492039658051100074401e40c4610310b8426a84d0810f82c01501c0c1550040d040b01e0859410420ad44009200140440e0b0009098401040c1c6000d00e103440b10f030030b5841c60030704512240003060210010584056050949030185c2c00c5800100d9036003c01826074040e444e602010584000c24840401a4150311100180040c1003400b900c0a42d80c86502c0e9030703480144102a0f60b000304040c08200203800c541c800c000c4000e140c00b40304030f9028442480d43c0c5e02c6083d40e00400e1203040100072040022101c7c00300010135407a891030203500d960742000200c20b010000c0f59400101c01600150003450030780c2c0f42c505c0268001e060301110755541c00005004024440b000d56041800250707103401c075512110022a00742d100c0031015283c01e14a1402c80c3c14440c042d1859120b00c0c240b44040c00f01940c090241c0c4070341d600407181002c004058000704402000d001c00440b28204250040000380013640c910014402c1081d140808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799579181 1250 799577931 799577939
    0x190c1205091e09060909011e051609060206012606070513080a0804030f1e0809030708190303020a090f0b0918160513050a12060606050a05120c121f 65
    0x246542c40741000c1c1c0e440704480f004190503040c4150000d500082c00d000005000100c15503010012a6400c541800e05032508200800302d515402c100c440c1070410300307084c141141445000382d1a60014011081054801c030128050816a4101094018002e60942e452402c01c00c50042856101200740c140e662000e82d000680b1990029210460a41013a034040c2840d0840d40c1c0d04140300c640404c00e0300c3c100c003405042050340c0703581440011694840c40b049613981c0240e0082c58145902c541c0804000d412510a1440745401d110050ba541941032400603074664400c0400e540e0800941c011441c44500c0c0b490114500b6544401403c840c3e0041f256138601400482d140000c117034040f14180301d03001e052211010703604d000c0c4000e000302c070aa290200760182c1d1910045004c200a0346c0c0049070007003111219006011440c81084090840c030700c0c04a240400010001d07140f8400c40d103a0b0204000c01e140080c002c82100d0047d9910f49107088038802c070a003889459010328400d51042e1410107506254005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799580431 1250 799579181 799579219
    0x1204050f07060c1a06010507060c1d0301060e1506070c1206270b06060c0f0c040c0905010c030f020709020703030b040c031802060706110a081008060c190c120509 71
    0x810004c0d80205070b402c0c2c280c01e20001c2c241203600076000c0d03410b129040c000e020008a80380114480c2d2030550b61403440341503a013068007109003544862a03010b44d15140040c01400303c25100194400c1104d11100001040407003c24450711501001410358585030780081095903900030a0000076010b00418003800300c01551030540c0440303441c140b0507034a102e50b1002002076070000c3c0707850303000c0310040c201420801c1468419040c000341114034851070700201000340d1149424412600786010038a00401c0c840d08040c0081c11100d4900d0000e004d0000b94003981c80e13081e20800441d0081c10816005540315181403802601030140321400c1407099082c200151784041c403910843c1a404400c00501c0c070410080c1d000e1000d07640c024001500e00c0c43d01e44800c4e50f034010160004195003200d07641c0c0c6140b51325103000551152200c0d82c105150942095052004000d00c03c42503030011203244401c12905401500c003174900c0c0c15180740c014101038268000010140e000400b40c06124000d136003664076180902014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799581681 1250 799580431 799580447
    0x120206090d0f0e03010b030d050901110102090d0b0c0d3b070b07290103051612020112090c06050a0314160305040302070e0c03070e10080612031204050f0706 69
    0x1002402e64242503946602c54016a05046805000020300f444044003080c2440c049043c0b030804100c00003414001c03568413642c0b030500d0710740741c4000318144900c00001540018400e50301404602c6e01c003020070714419a001c103c48400141000401c040c040d090030511600304041540d4041004400716140c480d14030005403500035800b00080c0c4122400d1078240000383d080118181c440d10300340001650811810b19001300300180240e2003044a600d9403034040c1c9000001000d851604501210400c050b03101210f503244e2440d07090922514811403091110001c0a42c0e500c0038000c0d1107480c0c000110729400100a0500903010f540c107102c0042e58543c1480c0700c01c030913205400e610b40c01034100ea02c82c0348642d00881d0480d1180c41070b07402c120395503074101034100d00584500c0c038a0213000041c400c44a800c004c030700d84040020b640295450460400103030102400402841c02400158035898100c1d40600449401154212081117241081d080041d0758503202c0e980c42400d48034850012940ca4015404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799582931 1250 799581681 799581703
    0x412120305060a0b0c0f010203090601031b030b0402210a0b0f1803040b0f09190e13031d041806021e070507090f02040314010e0c0121091a010312020609 67
    0x10000151600d6040804c036402040c0d46441805203056904440d9420f00055008042c8800209219411420106480030b2820b1100b00b03c4059840e0401c00030384280b5019520940446d4030700c0602e800d880c4001000f9128500031401402081254010401064041401070032507000e451070b10754a40451a2480ca000d200ba41c01d40c0c1c0c000d0004110308c3c86094000d08030100700c1d012190074420040d01260012152031200590010301d8607050061000000c0c44952200c0011040e1401c040c064a0250000c003880e981e200312411600c0a000041d259034002c100c0407005441a00312105441c24248029000807101001040b00b01000321a012661020344403210707000009080410f1034002048010180e140f80340c00d4943e0203000c0007011407188a1040031841c02c10001150800100c814141440000c03c2100d040c4a108140c80441c0801c0b01a80301d05510203090000e4555260f04000000d01040d01c800340202c000740001008003c1c000400040719005502103601d15240d0341c01e09612040c041c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799584181 1250 799582931 799582939
    0xf1a0c0c03090405090109060c0906080c0a052a16081c020606090403030612080712030c0504140d0606030503090312030c07020f0f03070905070e04020702030606041d0102041212030506 81
    0x80b404410307250642c02a44c21002400000401d45c40c039a440c002901e00b000c12036400b181c02070000f0000eaa402400b166406580104102d1808030040400b922501800382c2c91005401c00f91000c114030250100700340c40303101703a4004607103a589031212403085090307030380c027a10509010f100084007410201c1d01058840c2121a006458603545100c2800020300005205608050701c41e100018080092001460080d0140860341e81c3c94040c1d003040454800900610400c05107490f4491850a9001d400d0f0b400313032f0300d0410390341703460044a20000307440d450091400307802d492400c40c0000400038004010622400c080d01a1882c409205559900750b000484510002801c200110700041c40e1141194808030340080c41d40712072030100c0c40031074900125070b04000c41d0f841d512010310000c950050000801c1e020100c40662070040c259020980f074400180c5085c0c0031b00e4607a108105000c1301115038401c41c40c1c00000840d00d85994208050f00740003442c10030744403003010060b400c859911034013440b445440050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799585431 1250 799584181 799584187
    0x20912120301290304230d0c06200d020a0305090718110c010e100b1c1106071a041109150f040b0a0e040b06061c0213030f1a0c0c03 58
    0x78841d211040d040700410040e0f46002d00c4603420441240001e58042c600800c5410316240000107040c607428282503417000650700400903000c481c3d60215100007440c4e4410400321b41c0324580c4d807070421061000d07a0260454880802c18482d80032442c3d015100e0145a550180800e840e030740c188940721300e0207020b40100c030265025002614251500b2005a48108090452a00800550007821a504407a24060640142c0c00404418195025000a05504803684810701c0c1400d4031580c4002410103000b4241e0701841504501640c400e0700752060b039078000b62201d84c5050000000404400100c404462081031910031106605040c0c2e80340b131051340c52419499445c4c1c4490204402c100c0c1d20801594400d85622520a20b9154440703200000d0035070264080e80e81c100392400043d1540010310440c003484040c050070780c43da140a09540640001c0c4100142d4401c080d44103005011560b400140c0840d00c120213040401200303280c480304409140c0b4005c4099124400d040e8818402d81041c1203c41c0d0040c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799586681 1250 799585431 799585439
    0x30c0712120504080c01110a12151e09060603090f020616020616020a090b060313050a06110c0d0923041b030c0206090303090a030e03150a020912120301 67
    0x31603000000001141052124507101070020307000c0d903000302c5040790030010215059003100c1d4240141d9801070308002d84103060003854403000309801606008000c5a0740c03102100c00301020707034920300c102030440c3d803202c10900d18814285480250b207070b00c581401c107441c2000c0011303414030910030702c2c000d02c4c8d01c041c0080b0004041c0d000c21480f41c007c0544902c07440841107984006a449000606c1511420005210544102d0040103a8614168451161103003856149061a41c5003022a0751020fa8120140303521a2507050551411203c980001c201c6454408402c0300c464851002d010038042ca402110000d040046088030b000712140f0860003a0410b456100100802e490722000a042001d407001801c611143c5a40d0401301c0e046507444086590303001d0072003d40340d040c03040d242c0c00070500300107601c0c0d820405a030301d03510399040401808000c1c503e0554803a6940602c14000110342014800381c2504003d41450020351100f2121445007184401060001401050b01c4172620610b98006003968030f4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799587931 1250 799586681 799586693
    0x308090f06010504051f06030c02010b0303040b040b1303081326070303050a05070516080c011d060f090d0614180c0d06020712080601120504121d0a120c0902030c07 72
    0x41d207082c0750251b00e030900850f18602d002012000303100540e0003003606d61000d00040e086641d10520300b40240c000b00402d1001510407001c0718210744131000d00c0b690f5144810200729458115402c0280070107400119640a4220b2203a80c000751030350b0800e81c444207103aa407600450b0600b401020103032504544010004039005030098000d5100c6424a03c1c5400200d80d101801c001002000c5016161080402d000240d4100901300d11030b0428280b000c00000c54000808160000c032000510a05c40000d858180110407401c0c0d5800354400313805109c04280ba13145c804094030010102007091800000002d081d075020340c10344d203028a24070000d025540d184c0f100b44201c4100300c01e42540c40e141c0070000d140020792201d1860400912540c0c4012150804400060030a9060101d00b0309103814036041c440483c440c0c281300f0b660b90341c25050000801e40084000c0c01e1411880403046d0340001c2c64400020502010311040220910507805000c055848590010403400103513030340781c2105001e124042c00150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799589181 1250 799587931 799587941
    0x8090c01030c021920030303060a1202030a20010314070e191203080a050901020a0e0d0303061e140901030c0303120207050709090212010b09060f2b0308090f06010504 73
    0x501841138a11450300c0048008104c94901811640000d44501d411158003803107000044002c0114095899820000005449c031030507400349484110400c0340400456900f003100c10f80c440e42c03000080d0074954010140b4006500d07086200d40c0800d0a0090000323003440c003441d0052088034561079605411454600740a00c0201d028600d60342c5040804010403058000a42c040d1300d50700c2643d40c01c02c60304d0614035032743c1511030140c100c034641e038014010800502d82012040d079a0300810340302810300d58824203045010340030b56400000500080100061202c49904818054540c040c80c001c0c941c0310040240032007003a0034403001c1e003e8500c041e01400024070441069452203001d490240c14110701780c0764103041410507801007442c240d545c481a030850404120a12000c98904020400c0340d0429000c80c038010b00092590340b040b0598074503040c4641c0d07202901271100d00c064820404605451103000c1d0310034400b0000354042210480000e141c8a0009500b08650b03001001808103a4649000e00000e05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799590431 1250 799589181 799589201
    0x40e0c093a022209170a020703061109040e0d0315050f220501081b030615150f0c150121062c07060f0201020408190302030f0f0304110108090c0103 65
    0x2100c90228002458040c15210f1880b02d0820f00028a0348920b01d4201808040d256500030300203000e114605905401084042c1141d030010004515030b0344d1003508107607912031094000e0f841b41c9484030040115400081f4994854081d45003081003a0b542010340701501079510600c0c4e8020b41c07a410000c0c081c100081440403041e103003c070b281451400d40c981e140c1607038026048002e180c0c0c40f01006000281d5800203204070b01609402800250400180050725040c2c81003850707006255180e001801091900300301d510203140c01514989903240070049a44818000e5603010141140c0303800803400c002120a1402507545181a01d031405800781e4440c009800c00e84201d003810000340303007003d143d00041144629141c03c900060004642030460162541c18211910421688180010b122880c000180c49100000d102e40d00700000f080391a0417491445480150304d071904011422824108200026500881c411301a14910384c5522004407400c9004a541c2280d650120044c100254003c0d40440404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799591681 1250 799590431 799590439
    0x18240309021804050d0807020606010806030f07180c031e050a020409021803060c0405030c0120030f07140a02092404020c100f05161103040e0c093a02 66
    0x281580340c0020b00500950004145010342c1c01e003c000402c00184403e040c2030501e8200719601e8144124000d54400c002008030b418040103801042881d0b500308110310303900324644111000c0c240c407100407000a030000600450001d0070301401c602401c0c02801200d440c0c0c03817210b800a07818104040c00001078a0040c2c00002d01c107508000102c0c0300030060006102e6480030640401511071a5818103180c004010990b03480071106000501650fa40030400c10031b5400c09103404034059510017a0946c03588071796035002c1c10324070000a0b90800c1c0404007024020341c0d40100900010190300b11043c54640100b008001c0d806a0f1b41c0c13001501e003038040f541c9a044145141510704009401a01050490348400b0000c0360b00e900a81006001030014050780c018003001c910f0502c081d00381010900030681482070f0602c180108070101d550b03540d00410989004000020860384c80b8282007030307101c0169000110550042d51410070211841c14041c0e82c0c84e18461003038543c654036001c014194060500c42240482e40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799592931 1250 799591681 799591691
    0x10e0a080a08250507050d0309050606040b0105090409030f02070911120c07020d11130e120c0f1b04110306031b010212040e010e060109060806010c02041e050106182403 74
    0x21443c0c1ca1880898081c565210385560308444c1c2007503440c080a4205e031104240c1080307a200d000803404a40950086000d98010401c0b910003030040c1e5060081e80306081e001032802031803800307065100f480c4d10440040e40c0c080d00c0b11992103840e018281d83c0101f10034905503604111401c04055418500c69000300c88030f40180c200341040e40055088a040181131b00d82e0304030500000d90924040074810302d40800e60504001e000002c0c448161a41e0000600c42c0110f400806d101c034462005228883ccd2416001c81601c0c6e0101c1030342030f00e40c2c0c001c0540d40c0700c500131442c040c42c105142d0364000840740188001030003040051034001c03d60300040d9005000b1811401842e520fa5941802c0f100648042d190055204400750704180e80380ca004507004040030304000c241e0104200907a0000400f6800c541e00b80b07440309400c0c00c203002160282002c080e10260a880306840e5185004841c2e0099043c3c840390790796074a1004040d42d40c1140540700d4020020701c901c0074813502005030010b00401048010906011070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799594181 1250 799592931 799592971
    0x2091b16020f040f0509060717010b09010e0307030303020d11160b0403120c02031801090b030106050c011407050c10060602151b22090c0516031709030c010e0a080a08 73
    0x544428072400c203c015119000e00500303580600810348d1001881c50000749515907440c0a108051043c46049507a03000010041e140c1d900c6440005018600076040303807130869503480c1c0140207510208218034814500b41190b981a0a582c00721044121312031000303070003000b043d140e1070040e01c80038000b14244240201a1517001c0300e0b03030264801130880c54000e5600e032120441414856566200c1c1c040c10000d030000184003010444054074190fa4184c0b91443d02c42919807005401080c2c0a40c401480c00038a0f02003242c030307562140061040ea1342d4401900d0500710124080c4c01980c020f8085c90002d41c003c0102c40301320304a00d1250660212500000f8030880003484c4001c01254000780c1000c580b452104088100d00c401c2d001c082c03004004c03074001004400c081d02c3c8010701500030042490340155084141d0030134944950452540e0452003000464036007800c0c40c0540c6d03264411050503180e035007000c44003054214086600f001c05500400d001c1d241155021040740d012200400343c901540d800903d0030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799595431 1250 799594181 799594189
    0x501050c041503020a120c0c031205100e090f030d0f1b090501210603082709011406120a0b0a081504060e07080d050403110d030c06020d0b0402130302091b16020f 71
    0x80781ca29603188c13144e20300c2c218100189030300c0309507500b203e0180c02c1506002074212801c20850840b0102c05030a140b50f216450844e04049481107c92110320000c0b503900c00d078420a501c00600092817610811034500f5410100b5a2103000d401008081600c03d0000c000c0c1c1c0d4020170903214030304814440031203440c20110588041300c08580040e2001440803402c1c50404030221000942401d9000e060304841980c2030014503802e030b05006000c00141c035019000496110b010660316050012290b070b07940303480c1c2054410028240c106080c5e02c03039803c0c0400062081c03004107401080390161040040c4603516511290042c000d050702e01034140c0304c4c042e4000b80c0007209204070001042c0c00d69680365224a142007a2004c3c4d803081c4c22003807140f1607000e010000a50401d0460000d0b69101c0320142e110b0b00302040c0c5500078100a001079400c41d00000300311900740c0120003a1000d4900c2218802600d44036080485640d8080da280658520003c00039031500382412a03648030407034401410004a290160042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799596681 1250 799595431 799595441
    0x121508061506040f1a0712020105150a1d130b0103060f140f0a1a03032a03070201050403060917070602090f01020303060d061a040213030501050c041503020a12 70
    0x451025003280090000c4a104104904035902045a141d4142070829200007040f03140c80c030030810783e0799060040390f0010808000341d5440e50340042d03401c03090151080c0b01078040e0008541e40d0001c40880c426680c0c20f840d094440340141d80030740f904c10400021f081444003100034050450b01440721800012000544000e413213030b010b1441500d01150915010311b0101c141c42d0041148900d94580c58100107800501c141110340c003400c00d00c004030f000d40189804202601312484100c1d0503020014204908a50008190501c550711003440801d2080018200d81c0b6401081e41c02030014008200420116200f03402601c0f206000e4041484c030f580101b9001c110552014804503015a00072a0110441c50120300c3d10f40c440740c013030000c0c40c69894510005201c03c28110b100900341540c5004030b0b40784540d10030000980b0708025004542d0303100040003034414040ea0b0f00c02205d83d982040001116100a942940c0448259810408650f00e21407000d070701a4005000300c80c1000070000507080c0101881c010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799597931 1250 799596681 799596689
    0xa08040501021912050a1b05030a09171c05131515260703110409170f041503090201090504090614010e07020c01020a0221070b0d150503010c0c031215 66
    0x58a041010342d03003041d000b600d500404c0f581c012440c00400303030b80142882c459124807142c2c51400c0303641d9131b4ad21b0308000b0082007444800b5142d5036030300060801d4030a060005000b400c01d503040c6482010f120034003000951314101c40c07001d155041c00700717082c0014086244440000070287c1d0081414903000a00f00e818048030381c050418000a19104d1015a606810901c0442e070244003030f21101c1e00b1910751440c2c2d90090140eaa0007507070b0b200005410710100c0154143c5917880002c9660b40c9054801c03141500750058010161016000751a80c22258001d00c82e221000c3d034180c41e034030301d8a403070642000010416100c0a8031940d840e054403100c0102e100030054040c041c414034006031420002070003498040d80c1070140e815580800c20103405640c80c1d055180c000c00942501e0114401902d828500704401d036071003510003040205408805104581221300010702d50441d42c1400346d95002014280c400030300303151011401e080c0c1c21001003881807010850b60b807601280031a407241d41003600c401910090b84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799599181 1250 799597931 799597937
    0x4170702062701030b01020f06061507080313030306081609150510020f0f07140d020105091002031e09280b04030b060306150a170a1a1f0b0a080405010219 68
    0x2c000968051051802e80d000a00c01401d107817400c5104640d031400c0c0541403d10480c0c6000502995180302e0080350025540304101c07035100d0030860100c0701c290091201c11401f107400c00c1000301e810300001440300d449109500320303408814a4041c44400411018034110151480300a000c98140c031002c002ca00d65070f0941e40100702c909090601136003030080101070301034940c206147c20803210000c51920101c0300d60840d142803024032070b440103840c01d00c1840100d5070000c40c180c080079800d580100203414600780e0501003540039100243c81c02424400c01c1441503120943c102070820010b00804125810400051642101500c0e503400b2a0160025401240d0040f604410000d1505080c41056045440044a2000c0c0d0029a0001d54540c84c0c03400b81e4a010714002004a00781282001001e4609400403240080490380ba06142004001240d0b8106500032450766000c8500ca9243d0f01c804a5190200c2c042c100040350108889a1074042c0c01070f41c0641d001d100f61143c62031154100394500310303203031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799600431 1250 799599181 799599247
    0x3111005011409100f0311040b04140f06040c121a03030c0115080a020604120303020424020c0910091505090708101a040605070201050705011b03140417070206 70
    0x10400c5428005014400c0b0061340130007003210603c888030340c0e41074076882402504a40b000402045c01070940f215110b50003414500c20204c0ca070300d80a6054014404100f803403090742d4404d42807109503100c400e40d800000310008010151b00d000c3d0b40c06030100c0115144003400c64451100003030715503040b01c064056203965513500c0103904d0a4000c000c2c0010503220b0040e0030f244c151900051000d00441c465085500ca50307091180030980300303a0444028001c41207c00c9840b035461541c030344510002c11404009846020503907601031500314000c5100d071683c013201003103060501d00d0140182c0031207907011403950800b007404a095a910400944103400543c4e030307806185449019064028260350255214006462041e081440c843c0c084030261075560074140c0c0e4409a6100488040c0307d42d26010b0140d5103000c02c1d0340d01004181e184801710103600d940500c10100b840303106400300d540548008120f112181c5080203000c0241d4041c01c041c80c0010109030802411000c40c0d00d55140001024031103030780b05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799601681 1250 799600431 799600469
    0x506090d020f0f060c130e24040b0906102105060405130507031b15080f071412130c08060103020a0f0b0a0309150204060909110f070311100501 63
    0x100074000381816118010100119840241500c4040103001341075900f10025207071202000f00445540240400708000740b1038a0710494030303000044048141d5009090601020f23040340b07414003074108a660000c00d82001307519910f0400043c12610340e04641841030789c1c0d044554248071020305a64003003207501c01040c20300e401030402c01150001410410008940104407000c134030001884000d480d40102c07500a035461021603524241956030064251801c0312003009002d0394031040743e82c020658188140c003e6282c4000903288407402088001d040c0744140515107414404c2c99000d0380020f101d04140035104c1480c0c071004100d4000d0b400c1000e140d81320038010011420036000d1480144031400036090b00c14100102c60710f00d44500301a80041507150145541031000c8880401e00003400f00000315500d5030740702400351030140d040c49400345252070022201c0e2002c0b0705200300c40c43d007214001040d24061140e60241c03400c03403034080c1040141c8141c0c200c0915880c8a845601c2c084c006011a4074914204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799602931 1250 799601681 799601683
    0xc02030d0807020a06051f03050a031403070e22181e15240602010f0e1504120e090f0405011b090512160e090d02150a05130506090d02 59
    0x1410110100301c0620108824a503000c90000078091384481d000c1855250200304060005030070500c00003001441d0000000c02c0320008292a00c04d210b03031a0590f8042d043d5501c46060300048501e4000b044241c10f50350a1450314401c402010f01403a91070702120640051030104442e0b03581d00c40f40039055001d00e10020311000e002c1c0344130b0101a010001c40403800e15078608465020440303c0c2c2030301684500c030022807108a441c075003402c00d8920031038115550380c48100a010706071815802c100c10f85490f21402c074014000c036151400c0c401e82411100c682d2100e07a40e0440b11286181c02004014101803400380650750185414080c084031100806070b4149030030030900712000c04c1c7c040362042c240880d80140d66a00001e01c2c0c0202c401c101c807108050030120100030b04111000e09596030050241002144c00540401c3c49401217098204898030f440008400380e0b0341d0b819510b0b980c0c24821800000a0101040790003145d03000c08008240d0403403066a07500d80e031034588107581e4819141c011041414801354 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799604181 1250 799602931 799602943
    0xf020307020c011d0105120405251e0b07240204060f0e12070e07020a02060d1a0118050d0629090a0212010b030604061e0e0106030b01020c040f0b0d030c0203 69
    0x2c20480100344c1c400900060711520500303110603039a00701d810008051003001d200b8512502a4a1108044000c07002d452000e14201c501545a914200da1515001e034000942d003030003603540d1000900e152075441e44031801040e000c1c0442401c40c903655407010401e41d1050019100034215902d0300145000125009000c2a00441e8118061420743d490300350744890004902c02180c8003628603001c19192400d0803402e00c490f10201a4001e20001800c00051180d80d005000c0c02100780e0301c107040d00100b4401190604410725102c070702100d034048140200c0c078001c400724031402c1c4251800101140d40384040c400f0000b080001c035443e8885404403886a08112000540c804104503045141803900141202c41c90320600800b140e00c00048001003c030b860b60392001c0c02a1000320009282e03d200342c00109034080a80c020440400c0082d0700005040340a4028035010802c160081c002c010202014072008041c0da11100d0701d00740d00d078207581c2941d44419040402260003559100d00041c0c2d54014149440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799605431 1250 799604181 799604207
    0x30804030f122f010f0204033c1704050a06051306050f04062609030c0d03090b040f06061a0c012009062d030603010b090103050c130f020307020c01 65
    0x800040e000c144031000f190009003020841680690111454002801003110200c1c030415540300203000700034081082c240c131440361041e140d95116006090740c100d01041050300410b000c1d021400a01000620300d00b200034030080c800c1c907a40d0400e642c44c000241007082c25440703040070410000f4200c03003580324103c42d1000303890745003052803910b07951121072400d911652283c1410080ca50030740f560344011001442e111020030740115520703803c0445c0e5140d101d60000304007240602ca00310b081c41d0350303d00034055030300070310340148a204e2150f640d07840d0300098924968040710100d0750b403a4086860708044240040c5003c68140542c0c40d445044410b07800c4641c1030100c880c03d03253303440100880c9070f01482201c9810000740c4244c0e0302c6800e095019a0100401d00c0700c094422069007500702144515409035105020850080c40002d003e0410311411403000e010250240d003044000094600300008546180c040780b090010700301d20481c2400007260801e0b22801c006130880380b27101860350317405440c0307003452 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799606681 1250 799605431 799605437
    0x17091c020f03060903030a1a060a0f0206070309020a060c030509120706090b040f26010603060902090c091f020703050a05030d060f1202100c050d0e130b0105030a0213030804030f12 79
    0x2a00b0b10303021311a0b880c08010080b0044c9a218100c8090304021804428500740001d007a268507850300da00060a0150081079500042c8988000030b0b100511074000e20440720b40184c0302214a0381420170031038100340300349020b030b060105c200300c1c0c0c5200340c462010000989e1494030113019802d00707001c8000c119000c107074406c04400c2d81c180070501c01400405101c800700d9186c00c0315514114018070111500c034090f10f40702c103800e51070100b0000c140640d40c2c01200b42c151084580320f550780c0d01d0114005c8140207002c2c074603810001090700c000500c80f0b261340a801c12615801201e40d441c1d56540d0f914900300c054a0200c480c0c1c3c002080c40241d042441c0100c2000d0301c45800d283c0601ca080950540070080d01000182c8180e9101c2010b500940c02410f0200f40f00d500b181c2038a903900506040070b09000c61011040740240030b4051000712218103480707002000c01c1c0c165a0140317140c41d84400e2380f01a4100c10b40080245001e0b140c0080000e0800009200039881030510000078581402c2407902c03480300300240424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799607931 1250 799606681 799606693
    0xd022103061c08030903031b04080a121b081206060403020108040f210f090504051e190e2a090115020708010606120509120717091c020f03 61
    0x440048001920762050064070346070107446a44441c124041e4040c00c014004410000c18882203d002000a6128900c45001c1504c49600d45000840354499403003180d40c5070304002100d20024810034131741ca01c00f00c643d01d00240c026041d00300c1c10400200c0d10104490713030600001c001580d007128842180d40150700f15200c40c00d0a280d6000601403075001000200410990a0413000700039600361007018001030640c61480545002d440600300c2c1611840e10000325054602c0000c481c0341500503e40b1030254110b020fa5560304480d0862028100a408042c0803000c81008101d020744911944c10b940354103030020041c900d200000b1980c0101c1d44140400c000c00d801142d110a91107042e900c13411154020824449480c00c00403c0742492143d800003122542040000691182d100101d64440251010100104e48850201030b5842c0ca030300e800070449940912200e400b0401a0010705032068100321114034004120001641034410030b410505a104904c1120041d402c01c0b003d5007a41a00503402408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799609181 1250 799607931 799607983
    0x90a05100302151201090603050f34080316020901150507081606050103050f01110c060615070507090f0507020105130b0618040b070e011404030210050f0304050d02 72
    0x11034680d503400040d00034800280f03007401c400020300481e0401c1e040007850300c5440d6182c001c8880034101c00e03c03040d40c1e2886502c0b042108a00b020030304540c0501b00c854000381400341c05040e0241215082d04030181c02c2103018001404000500041c6805008a480c006c00d81002d0310400003030b080c0603040a041c1c41c13486458441d085e6004000c54400d681c00048198880320814804c0c0155034504100603c1181410000810004002100103412046031f00a0003180e160b803180098034000e030101401150300980103e02ca90504420015010b081500410301d8080191100c510301491075100c0144141d840034100451b000d58890303e6003000140c4001e00660400d45846425940062405404000d0600c00305141e60b6505180301c610110040c200d9015251600341040e03400000c81e88200450500c0343d021005601c01d40010300e1045110742d600381014116000e100c0640f1859060b0001d10000300120750040d003070b50003d50301c01c42c451401412000e0001c0d40c02424a501108850145010180400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799610431 1250 799609181 799609201
    0x1210e0d02030a0c060522050705040c050901080f0603070b042904030809090a021b01051006020c010c03121d03090a093e0a0207061407080a08070e031902090a05 71
    0x4c01e69604002d0114294540b5944040010601100e4550000d0581e41d0b41007005004161001203520031181000407000d500019122032180400030780c0043d101c100025001464415070b11340018001d800c070340800380c55103401145c60388980c101804075201c44001c00a1402c0070000048500301d54070b04582481d00d90390360b03001c0b9406040f45061262005000140c0240420b9065442403494010f01d0301c10407801c1d00c442030003007005a074000e16004c61100e000c0f4442e8000076403a10040300c10fa5074005030110548040f507400101a040782801a2140c44480e00c0100c844c5403221111011b00240d07541f8000d503020030415030307480e0307000034400c40c10121904a24103940803158034145103090314418022611403410303040d07000c003210804a0b071400701d07440444aa00203482c0080d03413100c0c0c4540514040802600d8068044c0c04070007810b41c507041100e0b01840784900080394008040741004044860080700280c18032030340028030f04100742d0b01008030055240c180d54064211041d21401c1089050cd45444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799611681 1250 799610431 799610447
    0x200a031d100e04050406091b1e030503030622060b09010320030a0e0304030215041a03011a090f0901180b0a03150b0303120f060103050c161101210e0d02030a 69
    0x114440c0703544c0e00000d02401016000781e1070b503640c0003000e041030f04242c1401e801262000e0060a03d201c004041e603844000090340302c0c00503607401500541c251f0346c0324810842c0b41d44e0b000f608159801d40d00c84040400b040d407801180c01401148040c2500c81c04d0f03a0f000142100c560200e00218100750b6103040f2410181d580440740c00076562240402c1190786681c0c403070724512a5a00007900844541040407a60070800040c00c01e41c0c400100c55409038884180d400c0f4140000c0c001c0d10030028808402d0902503803820300926040d4030181442000301e004900090021009070700010103040c2c102880c2144000c94440c403101346500b12405403140b81035407a1009101540d00e0034003080c82ea5450903001603a810801d841880c0001d8090048034a05003005641000080e641907001c241090040340c19004490f0960312a40320750a14a54004034a1b15403e40201031303620381d80d05000009041280c0441d85608100709140c0342c0340302098a5000030429031400003482809001c64000380f00c080b1800d0703444544 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799612931 1250 799611681 799611707
    0x15071d01080606040e0903030103050f060103051b041e0f050a090b0610090e04060207050d0804150b040b032a0a060807030e0102130305010510060e03030a200a031d10 73
    0x440d212540d2030324041143ca118a4000c2240382410310b0030013009000020042d81601c0c894015507008180b440c20396540c0740310270f000c0180302e50008150340c070715204004050003030748200420101d400c1915901c2d0306130802102440086994a0303518103620145140141c5070007000044040081d000a074a5400754524050b1015228071010700b81001800d1142102c103010308140002601a41001c2c03030204020b602580040b5668022400142181400380c0c040501c9250003081c2d501c1c480c0a10715011004002c0c28803183d40c00f9980300303070385420b5450800c00034000c02c4c81d404400c00c08145444000140110305031119200301d407031440c140482a8810101038100d43d0b5401d003c80d2440400c15010f0190044a00800c0c940e4080040003040c0034054020328014000c0e031545828a0b501c0b04400c580514a422a95406510030041407445c244100c1c401d070078041d0000590300300544208000e0741003941617002034001602a101c3c13490040030620205881c0b0a04a81c49410b010990b035000d05100000c280c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799614181 1250 799612931 799612937
    0x70b041b0807050f1c0506010b04060815090703180506011d09011a0904050705061603120b03120705120d06211a0405150a0c110316020d030908030a0215071d01 70
    0x4040424417425420203a40c5901600782c0e584e56845041c4031180e604140700303100020b030703240011072054804804944d8100c100640711150075a1090425005440e158011445003140e01d070045010841c00d02c4824041e04411185041c00b40340c3e00600c40030032001400e03d25080e403404a103c03030440724404408031021780503604040305e50380d282040f81c1415043e41c4940c0c0c00c000c0000302c03078103581944445950414400c3c0c48a94140c09524030b504225103074600d1058250f8000c4d84640c0d4801c001038080d040c0343e8420300c202e6040c00d020304070483e240e800c0000d2030201552034081c1804100d84644400300381910094540300180c1181d240e903100d20742101f4070307c1c02410000c404901030203c2440800050104c50954160900f0080616001010740c01c1e00400040d220b8180c1000c42c020201c120750070203814509031803070074480d0f400f00025003c24040032414441304000c0011204000c0c03000d45400042c9402820a035849013603140340b0000e00402c2d100800001107480f503c0000304200e0258040d600b0301e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799615431 1250 799614181 799614199
    0x809370b04081b0d061406040507020606090c13091a010201060501021609020310051008011a07020d0803090a0f0602030106081e18010b06040f0810021c090305070b041b0807050f 78
    0x101082d0101158100038000a0800c08030a9440468070382d80740c080c1f00141c0d0100025a03c807041241c0b140000d5540075405510305000c241604031a1015080246c0001c80340c5ea19030343c0d1180c41c08115441441e58444802050b6280e103059a02880b41c03400400082c0041e12244280030207000b0443c1c0a4040c0f0200da580c0803000c20b60950074041c048024090107402d040b0499401c1c9000b4142001c2441020f140102c21321070341309064040800e9803444c96010b8010000004150350740401c42d0801060342c40d2600c900d40803803011840074401c1c2e01815000f003000581c0da50509000900b4403100400c0482c5112540e80c014151403108078000d60b005405024400180084514150140030ba00c21810344c000c0f8082130100351581000d003214212071100c0308603421002084100000e07801004540503007110341c868401c0911615410071500184070307143c9a4035180055940c40303405103090742d0031b0300d2894a030f4030301c4508902a8085080980800c0c0004d106442c50103002659505250b08200e0180c903441c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799616681 1250 799615431 799615483
    0xa09080d0c183f0f0602030402100311070803130506070503090d210515061c1d0a1202030403050625020a020f04020f0f0406030506100f0c0809370b0408 67
    0x15143e85145501c4500c02e504000d0904288002c0d400135101030f032041901d448284601c0740079110b44840106000d00b258181f5031252640401900020034035620520440c41c940001103003031100a11a801a4a03015100c0c100040c480b40f4000030178048000f80f000000644040d2200188096080060365a020515503203101c0303240091001c4005068020380c010950400070038150b020314449440d804c03010003003400182468000b50045444038141904003c480001080501820001000540c0100e0707103001d80e00d0344c4691520200711026140f41021660a4060045030106010582c41c1c5100034002e000c0b10717400103070800b60841340710b91240c0da0018803011051071420555010701c13503c041d801d886503a1140d02070083d103001c07a815031141c0e001100080c20030f4003402d1039400090141c3d581d40380ca0032065552030042e40c03005078010703401001c0c044414910701941605c440c4400b940c0d248080c21b60348046003503074040440d40250002c1c0d40240000d029402d00007610b100d0414200b40460469010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799617931 1250 799616681 799616789
    0x61a120a2d0e1b100201051003080702061903091202030a080f150d060608061b04030b0a0b060304030c02010e0103020a142d07030815090a09080d0c18 66
    0x280c0c2410200e000e0b815410b00b03c0e1500010000b09100199450b605940f0500c4c401c0b422204102c0d1300c803111070000401440810740100140c040c0c42c0c0b0103000c0701e00c1c00002c02924401c0e41c4a84801b40c000980300d803031010410411140100d542605400114284584000060090000202010501c00344c40000901c0c100108001d240c001d440030705010001d06e018105a07015002c02d01825500f40700b40f40208000780c0c03100d883d0355031200718802c50505044c11540d5007092040080c041618407500c4442c000c1c002ea85170f0004501a61294945041c0c0588910014054484006585041c54410701c504e102282c0c0020522100c40309000c0a80d50704c0d658440e4a1085c586c010a81004a0030407120b0800c1350811803008012050103a105c0c441380b076440d00740c2050121400195103030019615404510b40e11629040b020341d051003245140c1c2440e00780c442140c101c507405101400020204106214100503d03030402d005041061400100084a21124040800111040390088000344000c0d800d500c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799619181 1250 799617931 799617941
    0xe0a050a060f061106130f0308060a0b04120302010e060c070f02120706200703020f040f060510021f0b030c060f0c07090209040e010501050108010603020d061a120a2d 73
    0x441c05200e41c0301d29004000c900713425401000c9100c0d503804584085903042415841e43d41c000c0000c0e42a5486584c11600d502e009444180c001d0014480803684a40540c0a040902030401503002010a41c0c28000d00303480d6008541c07a6603400071f0741802145d002c0345003114101c035004528060003c40510200c0c2040300c4825000e079060280c014007086a560010b0801a0714841c1d0034220042808055259118012480000c1d0700419801c90f544542c240303600310401a40c41c1080004075543c0d9100801d04001451240100582191103100a0380c40c001a41c203d02500030b51003004100310940100c0d0b43d4981c40714009110b03d0b4085059600f0100c4a011120320030300e110240e0307600944c0c42503244047d401201e510b030302c0f80703041c44c0120075070001c144a10342c101e6205a580d005a81d01c1c10f14180d000754080c21203141080d440d00400300d180c1c00056021802c90000001181d6142c07040344451803410806420f00c1d000c0344c1055000303d0101c1249092480c801d02d200c019200452203141c0d9400201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799620431 1250 799619181 799619189
    0x60522061b02011704110909030307050a030f0e010c032003130f050a0c03061b020607021e011d0d0e060a0903121b030206100f0501080c210c071b0e0a050a06 69
    0x4604c220412042002c20012107442c041c007030fa00311907035440b10038229843c1d000403640040094000d0044030681842508940e02d84c11342c402002036031144010340c150a540040c0708180100e074540c595002c0c50b100140c074802c42d81100c0383c030441c1103007000c03a00a504d4100320900506410500c1990702d090003000d001001c00184c3c08103144107411790324030307220016100511503000b4100003035480c0b00c50380d40003140c528032501c90340d40070300090810f990502038030812094011003a59600c0d40c0aa11664402e0700041900850384000d00482d40400001410100c03100081c0d4010f1806016000c002904025048141ca51000c061004145002d104440d0942081440068115007000307003c01d06401140d02c030f0240c0701040d0003542107038071115013005e825500d03c140d9001810000000d80008a000c006c6c100840c0300c40c0300c410442c4122a5810701c941403e48260340000c600017000010002405031045a0904180042c005649001410b050002d001460380e905d43e501c0f480040d110f40c403283e000c0e034050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799621681 1250 799620431 799620467
    0x17010605060309010614010e01023d02090f040b061615051e0901060f06080a06082509050c041806240201050907050f060a120501060522061b0201 64
    0x183c68548542d5019004500c140741e00d0b010b4940742c0e201254494082e24820480603001040d20600801c4000304105483d00a001030152285d8003004142142211540c101250140561550356510803c0051032403030780f510317106a14200c04586192600320550302d1142540b4070400c0503031030f01c1c00c041c113413000700d108854005484c0408008403034070f00e480040e00c4541003a0408007143da9a050300b50807100d0034046c021000b106680700f040018130030b040031580031850200110b160395652800915251218450080702c10032032007140900a607101c5100010040b121051040b810700d0360042007144200c1c01000101c040000304030501e8490f0b038103c58010f01c40007220341f140c1c90540d580480e840c0c0c50222610019400c1201240902c1800602d140c142c4000034071031030382c0c60f0f50b110401116501c81d4100c0e0f070610100180f850400e07211032107020f0003082141c40340d55451000e80940c181c3c11040d0740d40a402d8212500c0140021540500018010016000012050103050006a41c10b54000e01e411140d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799622931 1250 799621681 799621687
    0x50703080d02070606231518060d020310080609151302010215041b090509030909181903301503050115080616120b0a03050a050114100506041701060506 67
    0x1616060440740701d1130b9601080b420406241e80000c01007200c00d114031a04148038240820890140040b14486260074000c000512b03000b510a41300c0d0590700115a00000c029041c40e081107080c03014047c1507400390352080500310080204404440d140b001802c03154400035075105100459008101c0c188054984a0b03000c81310380391500e09101030118040955014070b02c1382c03c000440005502030395009001d0840030f1400c00c25018140b00110b180100300098200301e1080710104800c0500140182c0440c0001085414106080240c0a410344c0302c903002010078510604080342c010554240701c0b10fa6a1400441c244a5402031b0066807449600003030318035443d2900180c180942100081d007200e1094054903096030315220b1003094102c0c5018001c0100e08450345030410321390650700c0000c1d900700040c2200e8407591680c45203440e11840b010102d40c0e907952003c4848907418034040090340080c04e1a12031190a00744004140d181c0518400c1c80240785400200e022212400c1d000600500030151580e51 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799624181 1250 799622931 799622939
    0x230c0a060605040b01050901020c0409030e181e01030f170417072c010e27030a020c0a05060409050c041203050409050a0c05030408090a17010b011b050703080d02070606 74
    0x1801140b041c580b19920740078083e0b1072540a43c00791070030540141c000c0c0c1100810403050201510a40c00d049042040e55040b00f4210742d6582c1c1c0035071500c0c801c1031001c007007403501d0003002c2e000c400440b01500c802e40030580104005010f10004100c956433022403c1d141c00d4040c00c41480d0343c041c0b90840e83c03e0f5030076000d00c03c05810340011500e045818000b03160542c007540f01401204000250007008244031114014080340c9004040710f070b0062035910095606058031540401d410300e001845119a81000490584582c2d04002d101d0780c0d0002113903884c41c01b031302c0e007000500c2038820351282c001041d1710341000030400c00c81d0304203490060150200590003010079142c010142d500c18000c0012051808020484079a5a88a00d2541684680342c05155441d292201c801503001600751981c84500341e080441c5130140c010310071483c2a082030011440d501c41c2c100140415070700fa6100c4030307070684601d0580e01045001410b682242e4008149944d105034080c5020040d00c503009001d0902800e04500003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799625431 1250 799624181 799624193
    0x1a0324060301121a070206060111030d150915180f02091c021203130302060c0a020301060f050406090b100324061707030203090a080a0e1e040501050907230c0a 70
    0x908110310413180d00c13074022a1120340a41000c400e991080c0180d000900080d40341d40103c9155589840103000c9900303011030000001e09580002143c0158002c07070610410082c2600e00400d1190701d00ca005418406050540300204803604138210b02d0300c0c0f61070303400e810b400c41580d034100c9802c000041d081c0d00190041c502450403492803080e04034011711115811002c0070f0004410343c1c0381e9607480404980d41e02c1c915001c002032900704a10321082c50140c40c00002c01650244105801004100d440e0704da018908401c220864400394040c2e20542e04000c0105120782c3c03848581c102c8584a410009039000c1282d10f01c0160400e540404d600c51100c484010860641095802c51800c8000080184560701c0c10b408805a0006032072002c0d05501403d0080700064034807015080d051003d1402d00c01e2002c075440040c40718151081420140c3d804181e200030941043d0140c50f01615040d0341410f0f940c01c003820010513040c46003007410500001d540d4549600000f14003110a800c0c044411108001d180e42003030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799626681 1250 799625431 799625459
    0x5040b04030812091b06070c0b130f0605070b061e030709050910060b090d03030e07030f02090717010b030c1c02030a060503070501050d020f04050d03050703091a0324060301 76
    0x111003c0103030a0001201480300140b4010042170b40c01c00d42010707034804014081e003500a00c00480e081203049801045c620114000303000105156210794007d01d2920a135010340e40700300e0b00030f1020000c00304400c002180007148015088030081d60b440c00c00b12003100c9000f11203426440c2e6541e05005005000401d001541c00aa000d1440c4009945560705840d031010119060b0f441104001103081c0301088844c0b07010081c06101c035000381808a1040c1c0300300ea90b00c0c01c02500d1b41040b200c141884e1589000e46c01c24100e603075031000141c20302d00700d245290040c03400814070511601c1c1b810b02001000580d0700c00c00200307507100482c2000c440d540d65440041144065041180c0031100d9910303020000410f03280c001011012950180c6070185403219006669000c1e41c0444100e64100c2020400010580c0f9004800d007079440c0290744064440c0c045150045c03480e202d80c1c0c040074121a101850780d50040b2840e0442e80c00440c001d81e01900300100c40580070fa010034614625900c410040000910300c02e1944807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799627931 1250 799626681 799626697
    0x70b040b09060403090311240c0f0705010e060d0902030a0f0204140403050f0901020f07032105041a0a1b0507050310020c062e06120b0301090b0f060105040b040308 72
    0x2100241e501e014440c1c1d035440701194060006103500c10304001042c8601c0710302c0d8070400c010707025000011000d00070b03c0044c28403d0a401d69884005541d040200c1d0502c001124200600c0160041c1803800c2d0000300110000200c1302d128150010b441c01e2001d40390b600c10654281d002c2e080e10540c000500b020b03420f400b81c1141c140d001e0340c201000c001c400c02c07400914a10481d40350300e4142c2800c00c2c4650368072071500804041415403242d003c00b03484082e0100003c0000b18407034029803292000088001910819030041c007070900c141403009009600004960707116089610311800c2c0c8403201018111080542c5c0040420080001c007145414000701140020544105400711604007801c646280e04a100701049110643c00c85e601250419000d41090036110043e21080c9505180d40710f00040380d00c1c5580d006130b000c80d4000c020b102074850030b40642c40054800b140200100100d50315140e0385903000030304400d410600607000540d1680180b0a54018140814035603850b50b03100d28040145510a40c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799629181 1250 799627931 799627943
    0x6060203090f06070213051005032a030f10090809040f15062105060301021c0204050301050705040e2a0f040311150406050a210b0111060907180b0303070b04 69
    0x3601c030342c0c28100941151307607503640588444540085100403800901020389100603420392001e001500b5a4100810300c081c8010081e000c03801c901d42d5000d10551942070b16054065008504000400040850203071035500110b0380c0840d495030f192920140c248a00d0584d50b0348035190010100d0080c101c2c0d4096580e49400c842080040c42c0c94990035580b05d000d01d40445440c0c03d0403080c2071111021504440d406c4a030260001d82007d514458a0200403e6041c110b40340310360200d4100f22500d001d01a00d5000103035410420315140c200459000ac4040c0144200c07140000c8041011601c18280b0841e03100c0080201129100c0c0b0b49135801ca05980e21604c8240d40401009200003864a008040c403142c01071400201c0c0d240900e005130a99071604111447c4041c000b081000500c5041032804032407180511140000e04c402d004070000d4400209003004064a600c808204400c2c03040c00185142a034012002c10009041150700c10310213031000000054050001050003810020001449070083e48035031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799630431 1250 799629181 799629199
    0xc020a0b0108030f070623040b390c0c060c0703150209060912010b040618050906060108240d050303100603022d0d06180e1c140d0606020309 62
    0x10110f0f030340e8007600d2204140d190b0f0400c120000580607a20040b50100051a030b5000c0c01c4201d51030501580046805130344461210007007080761512031401d202c40d541c031544141740e888481c0c40250403002c003449450803000400070b84980519401c01c2580702c403900080819a0741c114402e1072603101c180c140f00454105400b040d450601007914006d860007000702400302414007110030100629083c01c040c1e0052255030341c40f1030459648450064038003900000c0040041041d402c4141e03400c8400042040209400c580b060003901da81c050b10051300006507405c0360718990850348940c0601d0a10352600e60f401050382c62040701300000400990320480305041803540c980ea030741006500364491034080c60401c00b00c0245028030082244200320059104041341800c0c4060b01030810112809500302c00d80d00c5085030400705c000c1045000f5010013039048800703405042e4507503500080c880501081881440002c03902c2c0000029410305488014200c0c0005201b4241d40c0c0001a40300d0f44500115406441c0c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799631681 1250 799630431 799630439
    0x102100506030309010807091a0403030906081b0d02040e270f10020d020d020c07050328060f1e0b19030503030a2703052106010f0c11040c020a0b01 65
    0x91203503620900c4041d01441c5481078040046910520007000740c0103000c0c1c80d207408a04d8119105a00d51b647c000032020545d210708504000d0220021640316800700300c030000c10001e04012200a10031103890b0080910b0303c0d40746200780c000190090350080d642d040e00403403c00915842c082d880000c2c490070080d44071800b8101012840d00c444000b0912100c96001c2a00b01d0f03030030074040d801400581c90b034810050905a40c02c90761000c0e0703402034000c0f290583c04400244014a01402564214100ea00c194044604850340045104603c0d00015000316900c1d100040140d509410010f80c00f00c81c40d522070b00b03040d0901102c100902070408400c0c014182812152040344980b980d20040d40d0f0400025821982c503551724901803c01104140f40c030507821406440661895001407d64a100e501e070207848049284c0701c900c0100e0807580441003108110180a51660000082c01400283d494414003002c2c0301d0803c516040c511201c1c10350804d00d0108980b5126501084145002c0e01c14994026182d0b81c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799632931 1250 799631681 799631713
    0x160602031806041211070e011d10050d1403070f1b05010302030f04141c02011d0d090e0a020c0303040b01090c03051b0a140c0f071a0301120807050d0e0102 68
    0x1040300e0060019010100d044c64403801640106000c4030a04100d410302ca450728095024071600303078440b440c0e030005800c1c0304a82200303a6511503405403006060fa0642e40c074000c0040c060460702c0c50068940c40c0700c081070414186080c001c0f2046160004a041c1400301140313019001038603a4440d403071007000604000f160320740c0b00f030003107a00690320314807096032540356520f910f40d00020180c00c98096210301c0f151201d95500c4107065420140b400d8000045a1403501190340c4c004d010383ca14030156402040c0c43c2174200e600f000320482030703810305940010142c0d1124400c100a02c15511b600e02c05100c0441000f040103060802c031030680e00e0b01c007014440b005100c5004d03001c4e03403030139101c600c1a600c6e800005070180e034507803000e0880d031300c00c514011003a615071a411551590020308421041d0b0800a8000e0700b898040045d40020310741444604c0c002f000c40000818103000600469038500e910540340b2041c0030014054400b159001380a41e814103410000190200d290391110501500926243e00b084600c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799634181 1250 799632931 799632943
    0x13080705011706180c0702090f150312030a1815020316170105010302180a140f2b06020f0c0d090902040807050d021908150c04051309081606020318 65
    0x240141401c914034208500302013a5100c018a0002031003410b0040f84056510500140c0c005c4d83c101403d8045400d0140302c0d14071721400400034078061f074000d2100c1039821240d04100c1c0d61011140d0f40000d4400902c04a60b10035111024010300846140c0410740d0303a8540d41d60085020f6240800c02400c0703403020b0038040e00c15542c90701c00c504050b44008010407065009800424031240d0321810200450a80c00004940d00d600ea046144014078031803049025007010150740017141411141c0182c0007105400034440318074143c0416030310b0b4244120040070420350f0b40603600c200c12a908031545840c400e009940c0d8925103080399000203040580c00088000f0b061003150159041c0c080a4203905060005004400003076030740032a000860152a1120520003100e00406000c51001501c02100342d002d2005600308094202002d000003001304110955550100c0740c10b084113810003007008651070a0900c058000c2c00e8030851400001801340d810006150700640c441c40520486980c02c40ca692070480d5142 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799635431 1250 799634181 799634191
    0x6010e19050703024b071202070f06120621020402070804090212010e060a120f05100515011409010e0105130503030d1d010c0207090c05130807050117 66
    0x52100304550044000340e041558001d4060070f0251900000c103150300000d000400c0500c55021100d0f09116105c141c00510400034450003111824090b030400016101d07210b0040001c0c805c016506500080d103000380b01100c02441992165a000da41c0d07002c01400004044c0030002006203403010101c3c940201c0c004209200e010900103900c101469401d110096000d0b11064174413072014840040c690300306000501d42403048030415105035141c0050040900d81c098075442c400c1e500960244041e502143c040d88429401080340c51005040d42400c1c4c0c00c0c60030750090f030080c0d9801e04041010f128400980310320059001e82e140c0303010f045031010180d003038040c0b0140035000605d94441460306c0e42c4920040c0503264503020030105581d58410009203076620030b042400d4107030b48580c84114030362010445000b11001503002486000c1910100948902941c09841805666541c906050710311803030a0f101010303004009400000c0d12410000d588608510969001505200e40340c0c451a0f400303072005000b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799636681 1250 799635431 799635451
    0xb070f081f030807080903152a070210090510020a0512031e04050a150e0c044a030f09012102070f051e03031f0302060f0a0206010e 58
    0x240c950a01d025000388803455aa890100155000b0000c80c05aa008001407445400c0e01542c0302c407030005060420100c0d1004020307079141ea00811151404040f408103640580d103030340001d220099540c1ca0800d0007070407070107500078012248203820365070400d03041000e40d0401c0300d1074811910500c104130b07550103011100900582102813510580c00842c8040c0d83c102021a030440811440340262018540c000c0302d050b100f50f07110710305080038040c0200344150350b2402c00400b400b00d0f00ca1920a00d03511446030224038011a900c41170005001a1208041209620480f0010a81300004c3c4004009403040042803070100c0c441240c1c51241c5400011101d54a001c12107043c10951b90800550f0380030091015500c1c500d6000c001c41428500c184002e091241c400c40c040384c0b50044034144640b40200c01002121001214480b01d901c500001042e25400302c8845200c2812280c0b40425613107441541d40000e401020116428182d01c80100c09402d07022200d07400c440290780e8804d04000922001d490045207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799637931 1250 799636681 799636697
    0x7051002031209031e09010806040b093c150f010f18030b0a0e07090c020c0f18090318010f0c081e0a022112011806051503040b070f 58
    0x3042d074142c00560748506144140c07400c004409070440e44440b0350140c0c8580c03c2e800000c041c11a507801020b45504000152020484407100c280072a842c0328020b0010822400c1c400824031404140c0709010f4040c1e0440c005100381440013102d4401070840c15203502a00021a18200800b41412000702882c540140e4800042c0d42c25242c0640711490141c150481075100800c022002c540800d00450107080d400100145a5140c544028100212604454121410003200740b418a83c0081d98407800002103800e48000e009400010b48118800d00c1c090341d005080104100841d81c0204c040e11a41009007081d9010b04400d5004544460714480ca840c0070900811070a0080751403200603040d400c0600181c0844050a868800b0554024500c1440140d10200e01c0702c2c0d450540011344072182410004585c10115218065004040f05024000c54449a2900b819124005030050700c01400301400000304c5500c82c403003108103a40115020b4a00708c00d0f06000c1218581306000c00002e41e041e990320012 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799639181 1250 799637931 799637947
    0x2090603010b0f09030109120e240c3301090c12050405160b0408121903150e0a05040209070c03120b121204170a0f03081b07060504050705100203 64
    0x4003c2e0020007560462440502540c2410f4500b40304410070720780500e103503165262103528010a145060313041c15019540090244a0100e80310f4483d5041c0501d2a4921f61698078040c00350b460300e8080c01008926145454041c03030142d0709000c01051a82451080c00d138203a0b00c403012101611407066114001a55040c0303240c04401050f4071003078029105605450382c000c40c18003074000086164000845c250b45c001000c0160341010003200d100c0c0a4569041c0f03040c200181c071710004007001d984100c2c0600d900e60010300400300d002880c20f4050203010044003032a08108425200a090488080340141c4e00d01003c01d010f5030103008140306207641a81c0342d07a0b00d040c0c0c140f5400050306a1848e000d07000f54084480b01c3e510300e03003804000403402503480226151440c0070403684101b1908a0f9451294000342101d2020480004c49100f1039901401c01c2c201c903440310b0785082d0b4481c806c0408854240030224044d0204000d40d0003550049024100711001d16450341d00f0041003070b00304030300c210240e0300c10094a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 799640287 1106 799639181 799639199
    0x3020c1002070303170703021308010f152916030c06060e010501050f03070509090a09030e090c070f0f02031c020712030f08180f03040e01090209060301 67
    0x12418510f5500c0c0076160382100326800140500d08800280340c5402501183c1c41d4072030b40030381155444c0d03680078064001c1c1031468903403100c2d9007040100c441504003280000e00f07a50b80c81c942d00e12042800140c80090007038285000248160501055100201c040c20003450b10b0301075151600141c03440c0c50420100c407081d420500f00c0da0680c07001840140d900a068680f400f2032440c0b05550ba8032491010745890003805c01d540e80c486042010402200b90701d400451884d031080d210751480c0741400701040031141c0121660f111108083c4900c001088481c0d4005010a000301114070010110740c001c60f09100e03503c40040c2d01c01c51754807500c089040e03040003407030024202035410041e1241107940c0209145a1680d40708200f012500104120b244101c03003c44a50a01d8000c40e2400740c02074400c0340d00d0b0b4125108140340c0304a00d000001d1041075a0003140c60507c1d000703240500c0d507800c0020790 = true := by decide +kernel

theorem cover : BRFrame.Cov 799460431 799640287 := by
  have h0 := BRFrame.cov_init 799460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 799460431 ≤ n) (h2 : n < 799640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
