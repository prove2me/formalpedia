-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:47:48.848974+00:00
-- url     : https://prove2.me/submissions/d8083ffd-58b8-4adc-a98e-711e2212f10f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 565467625 ≤ n < 565647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 565468875 1250 565467625 565467647
    0x1090c02010e070e19090605070806040c17131106040902040609060806060337090c0b0f040e2814060f0a12051203070215130c05010305090111040f0501 67
    0x102c2d0b488183c0622155030403113078560380a003c1c02d00380a00c034206101c010018211488000d400a07140605202500394402c812a1291030191014828201c03800c2d01180c52040d00c0d405007080e01c90740b0010172080c1012141c0347c031a0364050b4603d500703040c02036000130b44150b20a034080c03101183d00080c03c1140c25000480c1c04c000704014101561189010780c0401c6451200601d8102201030880744441703103600c1503500842c12090400052901120000d40000500c21581c003601c885602c07250004103070303541c2c50860307444c460194007003400c203490140c4044820101406802c020b403140040b03070280c10386421003103c0c2410b03000c4011941010940c211040014041c180d18080c80d00100031210075200e5041110482d40c524292912a1900b401e01c542040d0f4450158481c8040000a0001045d800207403100350503101d40c043c0416490b1241280640c0a038020014640b505250003008a58042c1c0e01c101d5004568000100ea5a80c80ea03000313a80680c0541c00411707500600050910403035910a80c0010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 565470125 1250 565468875 565468901
    0xc071203021315090315060518090d0f020a2f040c0228061b11011b030911040e060106020c010c05250b070507060305070201020909040212010204030b01090c0201 71
    0x22914220342c0b4503000342030b09401003c00c1c050f0f10464852846116a1480b40199003010010007803165011348103003e0300c1d99115152069000a200001c020b011a8406000d080e1a00042900f00c1d040c05c829245000f451000d402540110440400420051956aa80d008001c110300c6415484503040040400824030301d940520715101004a10741d070001020500030f06424848a8071800724030034806041445000140480d00b8440030354000f240d81c83c0b2582038421683c07130716200c122166480600f2603081000c01c4054140315140e550f12a4003e42c05602224028501604283c452502040039100d00300d20700c011035444080108170141d81804003045d0f0084c2442c000c010002d0940780e1903a0741d0b81c11500b1140388403503078a40b001d0142095543c8001841d83d00115904e40d0070380d091040c3c84543d076101c0c260100f41441c0004500520600c00c5482c500c1004218005548568003030101c44400e495410351259820031011000c030300d182031440d000306211100802d50f80000d1200900355002480104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 565471375 1250 565470125 565470127
    0x20604030804081b010e030918070e06090f040e06040203010e0a03080a0c05040302100507061103040f26131401180905071b0503070c0e09030d05060d06050c07120302 73
    0xd0780310076595001038004098580782c0400c80548541c540c1450b81c900c07295841c001c031350f404811002c400340140003000c84031084680321244111407942d404503012000910b090400707110030300d407000c05001c8140015184008502c410404942110032012051003290b00820800c011442c0c24000c1240c08092070f4080c103442d1030301c0d940160600001a00402e881d075140e901840c9480c4c802c0e021307a1b000796001020700d1032640002401805950040340181c0d00c050501d048002d00740c40e034000304d034001c0d94000603010301485540c65011080d4400042e003282e1884055050255401e074002800c290340d140d8444a51003490203c1d9140c08139480c0440310306000c0b180840c00903104000c5d006004132200400e01150715076a440e82101c030000010031400081624241c0c020500200101401860b1311803480d9402e559215040581500c00c00c0311042099030040083c680701e5400e03500003540005001d050781000d00c0c22503035480300380c1d481180c9503050840041010760070f0000624078080400100c2c02c0071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 565472625 1250 565471375 565471381
    0x40506010f050708280810050f06090f0301060e0901060801050912032403070b0a180e160302090a171219080903130f060210050603211c05160206 64
    0x549140034289025200c1135000c1400c11054140140307514803109100e0046881c0721580801600c0090152990903020000e1080400c0904080341591101d2900410700703402c025982d0100017902a865248942554030341c5c0380081e000046100d400e000e007410400104a060900c51403d00b190801002d0765005d44c8100010740c8190b140c54120b035009865040c0b5829038000c1c1005040010740c0c034900041c0c0501c00c0c10b0000031200c900c0009080100c0060f0b503401440d070040070300c496113520316009500c510750b9150b01040308014000b80200c160344007410054202030f440400142080410703880800a810201c0c41103004c12414019548500082d00413a41072400c2c42c91a05982c1c0300e185a0351050100c0c0002090000d02c0c104103407007003042c080103000c124544503000d42442240390710414001d03104402401c0f00a41d0b56000e00b501c40c200c083d00400890031030801c4000282000990022640010810001e025050340552408054000c01c082981e0814181080c0c3d40383d0140e180c601150001024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 565473875 1250 565472625 565472627
    0x60103020a0b070218040326090706111f0501061403040b04030e220c020606060c03030f07090312020304030c09020304030806010311041d040212150703020703020a020a030f02040506010f 82
    0x75410554041282141d214012480841c1c0354144007061281d075002036000300f00805502994000009040034003509110401180302c1d4076415068030150300e42d03000444280b28a52282c01040c8a9003070700c8088503091000503941d015160800c0710b114804c00d448400502c01103800201d8030203105040200d0703e00d180f6150321200030103607000d00014104421082c10612a0ba201c56030701d2032011800c1c4000703103075441c03250381c2400400749907040754054000d403030001e50700e441d15200b6030301c10200550207149107640d10440003002c200b0040808090024921021000c40c040b9031000212402d19001140c2d1103003503040a44200342240e0181105600420411001070b070700410082d0003903c00c0c2408122039103050302c4c8034000e0180b03410041034103034840c25450031444080000c0b400303103000b911310385c5100944002c155251140f6903a1084080c030072402042c046c1d482075008003086402481a19840395269001030382400043e80b0030354000c0e020b03041190661030700f445042d812507001d08201203c0c0500d010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 565475125 1250 565473875 565473889
    0x61e020c150103150e01140a0507080903131a0f1c05010510140304060e010c0518040204061b1a070309050114060121020409061e1509030825060e0d0206010302 70
    0x50704c0b144c1c885a8408a400094002808440010400500324a09200d00f4402040c0850340c0d800010008804581000d00100071101c0f6000303804140d2440c241015540c01a4804000c046804d40700c0412a052800344481c0180404450302e2406004c1443c8049240303003503c0381a00400d20899144210200170354100c4101010250303c0e1035200d869544074100300008204c541201204c0354203242d124110b45a2140050080d440f416400e141a10b42501c1400704138003e900a08011548140f02c03400780315000b01104002a10684851a10b074101c40c062440c039143c1610101c2c0402d85901d0008104202030180d40c1c2d440c00c1d1115000a503250040c0001c10207c0d407015000a1481c810b012281b8228141e012203024080000c03080c040640d031244617412200700303110640c400d48500d00c0042400325861100c0200d41b62107644903040036003945c40c0e00003280c1c40091340300c184810004692403045040c06840c0d040c41c2c0101c2001811500075402d550408046042c0e641c1150415001400141e07a054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 565476375 1250 565475125 565475153
    0xf030703081807030c0501120603020d11122508010912030c02070302090411040b0d0b060f010507050d020706022e090f02132a1b061e020c150103 64
    0x71508081c5501d4100d03240d594103030710200800b0a400340b01400b1041c0451200018215071081e6114001c0f207070720810900807a070250000a40c4084243c81d82e4020405001a030142008024107100b0304055004985280c1040ca104c07819205103001c0c00c000d040d4a28030700207001801c4110003409825015a283d0018901140c1e0b08414140ea841512100314804c000b060059580900b01d2440d034100303400c01c1c80310700d111030490601c560700f44035840440e410504d0201c0e411a5020051a9054a803101080011581d9885507410004140b000d4400304800f00443e02c1c203010950090041d40b400e000000b404e06103100400d4070b0490586000030104c03c00318040a400d01c58010300007c0c580c540d807500c1b141d00d9074180d5000e5804035064141032000505a0300090340d85105440301200d80700100c034000300040030317062000c021a0f8580038501008101003000318039580f080e000041e204600f540091903014200350f4a040c0290b0105003008035080c1049413903051100540d80c4030656142d07a80d4140161186 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 565477625 1250 565476375 565476377
    0x30a061d0f010b0703020a121229100507030c020f040903031407050324120105010e011d0601050301050618030304080114010f03050303161716030c0e13020c03071b170f030703 77
    0xa000b40d04074049c401c40514004014884040c44000c16800401480360b0030542d0720450440ca60b1041342080c40d050107030321403111150b10b1f070301d060140d10346042c0e030340c0300c3d0324041640c00c00220141c8500d545d40d113209055280d882500c0014076a605000035003071b4008000e01c05001e1103400c00622440d1100d0200343c0603800d14000d01c4100034401c1c200031694410042011200c9036003800300101e03908508190881c141c550410901403a1120100c0c1064070007030681c0c80300e020a2007040180510704044005241c4e46110300f10301905a845900802d02d140d10a03441039840341d660302d50342e0303443e042000481030041c00800c0e04000068250340b5803588901c00070705850f04021041c146c80716070030300940c400000100dc102920f800d84c038180c0300c4901420400500240024905903031040d605015041e00c3c08018405050b07542e05800003103400009501403c03040790300e88000c0c04900c0c00110702e07189040011600d44200e180c417503d480a0f081401511350f11410a0f60003c114040b000c0b0340000a0307401041d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 565478875 1250 565477625 565477643
    0x220b091014060d0504140d050f162a1406030907060f020f010c0203040e160f03021308070320060f0d2a020601081009020d08030a061d0f010b0703020a 66
    0x960700c005030403032207060082000a8140b10802c0305000424401c14111083c050036140d46240551048030144201041104400d2003401001d00312559040b0920016104501a410b8914080000448000c103031410343d4a240305030b24184002d4140c02c10400c01003000703944981c1582442180307551100c4440c02180c003041080e011200201d0700c20070a00041914210080103885158a8025102e0340700d4000c40b108031300b2440c0030945040c80f480c0c041101d480c0700d40d6029468011004100c1c007941c8425a590b0804042090115004d40c1c203111610041d03210300c0001901100900840014007000100107104041c24005c00c0e000070004000ca84040d410094005850071408442004144c01c2c01d21190401c00780c09640c003100758002030a02d0603140940201c1e40c50714070307030214101a1000003100941040060b80d04000113000301024680103600e11764040b410f00d0702c8080e5202e030102d1100c1040060306480b024800034010001c1c0795805441c08600c16803521610380c502075aa21940e00c001082c900f2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 565480125 1250 565478875 565478909
    0xb0409050a020702060c100b330f12161b06020c1f020d0605120a03030e0c12031c11040b07140f0102070c0e090a17040302220b0910 58
    0x1042c0d07040303a001542c02081c40d03442e4a03100e00510340d9405006022021030340703001d42c803407404d14248100450340a1300e00d00008000809000b102c0381c0c2c2d8400c3d0311094001400b400800c041c243c1001c090305264004451040280c80e00b01c40e85404408903c2e0140c00303102e64494050180340310f020143c2c0002e0b800110241c1d84070000500245403407251101032040c5030450940380703d10104d0390000c1810844041050201c1c0313031a542001500303c1131140d03092140d8004216200001c3c001e400c1306880901d0402030f2417607e01c0d810041081681060200308540e04001071640000340c200080406000b21180300304500c141d0005010903a1050380600e52407520085104000c102d1f000c490780101b14080429076070307a95520002103000c0d4203c0d00d030441e0342204005010400100d140380040c4101d000c5001003880b0455030b150708401034040450001c81030300c1080b000c8056152407001d003d546001d20700e00e1000e1005102c2c1c0100303e031241c030320003031080402d0700c10f100c118051700e040003060724200303804070701090303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 565481375 1250 565480125 565480141
    0xd08091207090f1a19061206031704030309060908061503010b18101d070309020a0806070203031b0304032c13020310060f05040e04020a080a0c140a0b040905 69
    0x1810390741c00310b004981054404a6440026005104003070315502140b031822505004004d0505015000b40160721550a000c2260610031000981c403130000e1900000d140742c982d165401307081c0c6200320208020100140800030142e10107441c00c0200198a00301003443d0808200340e49540c8081c101c07940a100b89003400596a9080d88262419200207003500d5100344002e074110078820084600d4034050b02e03a107000180300d640380c401840d100c0480c0502071002d98ae441c0010f400400030761200342d810002c20301d4041085002000203034040c072000e800441d102e18002c5c0440d01049130f100c0300c40b141c43c01c050041c800043e4108044041c00d01c41e1011118450b1010030101c1f60401162104513407060341c456603480903110030750055024182200c0079101e081c1d11054182d6204803a180e038680015000c10040101640c406c0340d29400520080401100950b20847c003441d182c1072000c00d56102050650801105001c0c003580a19180103986a0622500e0600c21511500a0b441480740c01d075200c200140f450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 565482625 1250 565481375 565481383
    0x71803030503072c0a06021b0613210b060f010c0f030311160c08030717030a0207080d02030f1513050903040911030901060501030603120309050c0901060f08060d080912 74
    0x41013030608040f1401d403a130100301c85444105009540034411940020400c18408216a0f0900000b110b412265540c1e1a080c0300c0d1540c040303041c00e1860481b2030700110380007000000040350790120300154030a6072081e00f40f0740e40b65540981401d01c291001018604241d800040d2030030300c0c2e900070000320307420342450030305801a10380103207a42040032001684050f10302001106020160280220518003526821400d950b80725060000e405005c101c9103c020fa1106c001c019540600001005410809075554540b00e42c1c0011080303050154001c0104500000407002055000315040045c404242d03900001c03a984034103601c0d040308065221000145003001c100f08860040c00c407000204500702c9207190b800c032950410f40740c040d099400c004000034290b01c01d0045000b1740ea000341e1060804c0301589425402002684001c40c1e02c0c1c050000d844001e60b0311408c145000b08016114226201c840130320003040660300810507803140700000c1c00310000c1f0b52080151070307600100388e80104403680103c00c15450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 565483875 1250 565482625 565482647
    0x6070c0209150306010f090e120405060f1210180506150a0c0f0507030312050907051c0204050f1006051303030e030f0a0638010f0e03030c0106080607180303050307 72
    0x5880341c0d400020301b0b500d0a86034002101d02c5100304001039074240744a541c84000d080304620140b8014003003400303a440d0401c010003803415404580391900e40260380ca031030f00500c2210203a20421002d08200142450900da0700d449800c0300408010524200c00001e40798800c2d0a00390744500c2c8041046480503008080840505030800465840c08486150442d0799108138001200040c0d44003da21010070203502801c1d000d0681c3d08081c00c80941084140a021400c50704000c292020354601100581c85074844d0701e01036407030036403c8001e070f16040202603480001644040100724041100300142c4030b00300122801c0d00d60501e0000c0e08810800300107131521101d0200c8010078050320700c1c80001c0090a40c060b0741310400c0c0e4500f1840c9800108821980d485621500e149807481c091241c10280d88243c507860420107440c00c0c03450014103140b0109240d03403c1004007190303c1c0c1d560380d0103014601017040300310741c042c0b07040c50302c41031004140d41d504c145d24400d480000c0a0040100208030f00501940740a45 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 565485125 1250 565483875 565483879
    0x61308090f090906070216080703170f030412020106060c081206010203250c12020d030e120f06100504090203030f070519051e03030c040e130605090d080906070c020915 74
    0x445414041c85490322150156140e0016118800c102c0350007d554001d004101c441110190440da4550f07202c40d804540300c80c5101003601010480301c011002e0b02c00c09140194054000751440c1172a00303c0117400c640369500f10500b4401690081c600180244c0300320384030241c800d401c09645445000060745940034200b40e80007442071180d0301c40c8a820b000c00311611010b000f0fa00d4000701c141d40340e415803441840340001a4202604031201800700380203480d440c40d01c0c1c80103070000c1c5c03020700000d070001d00b80743c56202e0300745190300100f00303000b255003c0c006041c01410013184c00304401c803116400aa0b0328425100e002c07002280c0030400b0000e00800b4026941c410248203061602d001403440c007980c0310310401700d0300068a40220394a0420190010951348980384075031409241c141001c1804c03040b100002c00e04a900590343c401080040c0c11030051500551b5a0f1000b42040500e4100203044988020231040360780d417140e4204513002d507012203600784441c4c0644d10300c441c1da101e102850316009580303c3c07029 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 565486375 1250 565485125 565485139
    0x30309040926070b01090b0d0303020a02070b0a090815100e070309020d0b010e160f0c051c09230310110d11030108010b03031201050f01050c0d050405040b03061308090f 74
    0x5410405080028180783e40f0854410046a0301c4004c2c9504488052111a400c02e24105517080000d0090b4002c20640c0390350300440720019030381d0b11800303500d03800350400704001004c1c4c130001c000c058010010100031484000c1c4955691a10080d031200c40305d0030b4414000501300c4c1c44081070040b400b0764000c0c0340a64019001e9a0900b201d801c1000c41c420080c0314000c200b10f1180005040864003404c40c0c5101c4603641c0c0c0d0309510141c020380c06ca5a41128210645041c00b600344100c00d899013016000442031426250075095918224811600c52075450800141c8500c2c2030840540b9903000c03601075400b41d401c070303000221030f224400081d1290180d44095081c161604a0309040e0202150155040380ca007000280b0081100005054484c000e03c0d1207402c945400d40011300507890601d1259950300f01c185806402c1800a0111500d06080c0c840e0150128500240500003070429000700b011181c002d500034122800c1010300701000c41c0364460060f1121102117440100c903918070018900e0998001c0c00743c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 565487625 1250 565486375 565486433
    0x11060c0318011a10170411130e06070e01020303010807150908010c020f010605060c1c0228170406081302010203040b21060306010501301119020c0303090409 69
    0x3d02d260f9070311502548600c051008070070190f0320508400250f4445500c0c001c4c8117407100c0d510907842002085181d0b901900038500d60700141c51500c030f5000c0444413400201a18284158080c001d40d4503484070904640040006015002001504030308607520503030540302110410004846901564011036101d5081c41c1e080c68407180d0025920315481c0d0b08030000c00c0255500d500700310315442403800c01c400c3c50300400e81d00340e1062041c0817600780d80740716170046d00c0342c101c04528082e4190019174840706a10070344401c00c40034072220404401035140442d9030280303400e0030100302804103100201003603c0041031051070784c1164401c1c016034008040d507805450701c0703880303924801c0b6040840c140c0494040b42840c000039054500003604604842c4181c503440380b4840c0000030140080780c02c100700214482c040c901c0e01d02d81481e503c10342c14040061000c980d1507000549902000184201c1c99000710340c00360100260b1a40c010007220f8400c031044600290002043c540307074442c4101845030b542210804091 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 565488875 1250 565487625 565487651
    0x305030a06180c0f03020c072c2a07150915050c0408060c041a0f04030c0902180901052110050129070b010b0309030903060403110d11060c031801 64
    0x110b11100f0783d111440c40980401d4110300b28016021500c9855010004c00c006c0d0403c8031030640380940b2541280d8141d12300744000d14410800030703100c039481d07050403a014003041d00700311185100e90120600918135140907138031400808128410b0484120303175109010300811100d01d80900640420a1080c006403902e5200d030300c215003080c41183d181e80100c0c0c0000d01c40700d0309001144c091300c0b21203900740b0544c0550042c0303481c1504550512841c0290801000c408601020000703030051544090160b40da00c80f001308500c0f242111012140151501c10061105548400300d804004d025070042070054440000d155140194020049542c2d624080010400300c043e9141030220b000f560f401c1d43c980022848041509115401e406024880054014007050303030307904011a00119070004403410075440300e0019040800c151412004606402040040c18200b405000c0600e6424104000c5610403d9403076a21400010681c0d55856400070018084c603042040d049460140c040003009030300400d20b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 565490125 1250 565488875 565488881
    0x41406160b16020c210a0c350a06050601020102121509010605030705030a0903052107180b09060703020f070b03273022120f0305030a0618 61
    0x142d003011400071a2104025500004070f07802c0e030b4203016040e224100c52581e401d01488803003410403001805034a40c0f44c0085a04070203103074050040c080207050b554140081c2c1405565884501400206403400f0040c242d140208903000a80c0d0489008100790703840d000101d00911603101001542c0781d2920074800d080c021400c0c540102c40007590000305c0c990300d400040c0c1c0c01d1f01044a10000042c0d0810019440216a411042d80b091182c204142000140190001d00d2110030000084c81e541d0402003060311039010252440c1144040c494260407410000340800074843c2d041c0d030501401000131031104040c0308103c000d80c0c070001141910840390f254031a001d00d903070040d2105c07000d003917941c015203e52452844009181030403a03001040b65502c0ba04006980f41da031003035020300c4041084090001c030700b881001041c02c1800d00d2844088005440c0b08041e21200a4010104510001c141400000e0001803010240740d01818481d8680e91030702400c41c050040c5400800401440c9076043d000c11201350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 565491375 1250 565490125 565490131
    0x1504090c0801200304030e010210060801020c010f0c02120f040801060e0702011a1f0309080c0f190506061905042912060a09060b030d170705030c041406160b 69
    0x74009002c4a0002080c00b201100300c2540c21045103810000300703001a000720611744a50006006603110540304460301000c480c1760380e01c1112540d40005840c0c1d0b00340000e1041c2001c101d800c860402020842050096864941500513521a00c1c00136030002594040000d840052109500911613107071142c86420400c00141e50000c095800d200043e986001052014071480a0181c81c40ca212048007280608c80742402c01540b0502d682c1d00c002401040200c4000e000e1698404003c10803000880310b0140340145010500c450304030a52450320018201180309604130a04480c910468440200c19103980a001d90001381d20500e0100003654013101d03100550034048005180384030600c009010300c190b00c010b03007912038680d03040200020041240b0794000440b1501070000000e14a440b04003291070810095903100105101c40780c1040c6071503541072070a0f800340240c40c0881c01d60810300c03d455440e000d170b401040d01c800104052a002601c80406561800101400784c1721034540324200610443d03000d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 565492625 1250 565491375 565491389
    0x90b010b0301120b0403120f1b08010b12090f010609060918050c041107061a040507020706050702010521040b151507020f0a05060301080312011406121504090c 70
    0x11000285000340441a28100c40350580c0d1544020540c0d502d0001001d0018021414001040c11121042c0a18801c90b00310700c003a000002a2160502141403503011900c08030810480340e100140540c41c040c1b4107852801e031114800503040c2c0c5402001d14107103030642c9415503c0d0342c40c103d00003130700810503005001103031101078040026148008030701c00e0380341c8552005041ca50000981d521603080a41c8000c90103068000b019081c804203035901f80a4a1980320740074000040c504901400e440d00d80300385600108640010003d07986843c1c40070f8582d020711980a814880082a0101c07244031304001c1c07514081384d005050f003203807034985091040c451003622055047c1c2c220360f10b40312403401c10040a102c000390480c100c40c10310a065081101050880c00703103980068040600107030703940711400914040c05944000e1502c0341d6070a40b118052580c140e11000300442c0c100009a000d0701d4102c00c03221210300d030f210324042d2552800b5041400b802c10340101a0020301e8826500c00b8001d04001c80d5050301c801e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565493875 1250 565492625 565492643
    0xd1103121306110604110604081014060301090b04030807050d0f0920060f0c120712020c030c01080402010503041704090917251406100503160807090e16060309 70
    0x440c002150f155407180001585907000e0404030780032400c200c120320348900008188514082d200d00d05079060900320003400d001c00381c841d40034a088109003060076030312038029030007000402600d4503140b190800240001e424801c190008c039242500c1030080341c280c902054070500484800c143e646005001c1204142e034000e40b4118030304800c40b13800d5070000480e18018041401c000030140314000907400700400741c5c041d110711005d400710403a41c58081d102c40760103940321034120039802c4406802d22902924442c465000300f29106410380c2c002c14001d421a0702072070311584030307a11403411300c20b00100040035800031200840c3c0040c006106422a0b210503209030300010760101075502d880083c1c028007440c403100e80e40e0003411030b51183e18550242c18090280301041c030018001d060032400e00ca010b0743d15041040c01e4010a02aa0404115135000c4440d03261004030381c0d40c41c01a081d03032a50514001c400c40c140c1ca4038a1f604203480100500d40303a0135a80215054040e030b8582c0054020200e41d5411551405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 565495125 1250 565493875 565493879
    0x906070c030207060e030102091009180e0a0809181602010c140d02090d0b0f2d07030c030b061603090b0a0c03080a06170c0a050303090f0d11031213 65
    0xc403a5052084555040d0010907596003032060944a01c0800d01e102c5402d90340c24003216800c0e50701d51300010f007400c041d0744aa4484904018089880f14001c1c60103003081424410602903084c400986005810380002e00300380c40307214400014446114440c0301000340b01c903803070a200060b180d28241c000b0100554008001c800c0030008140e941007041d28800409010600c00304803140c1d9075800400c483c1030020040040481144c0d100030581105582e20b0422451032010010184159882540405030111060b103040c2c116042200c40c142008044070105900d5020528150340203400c41c9124400041101e6143e0801040c0001c3d242d41c07080040c0c2c0012010780d00003c1c4d0030b031550201c0b43e105510740d5505600d0a850348040c2e070b00c110041e240394051a591400080c3d013100d500711340b2005068a038050084807141c40200310490f281030f00150311070303002040307c1407265940d245500104074003560700421540c0c0f18240b0f401c4148480301c4894141c001c0600c0c8500c00320380178000741150300680304036295041d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 565496375 1250 565495125 565495127
    0xb0306040506250c0f05030f0406020703150614010e04331502030f0703020316141002090d0f02030717280b0a18140c0f190303050d140f090607 63
    0x83e542424400106404501030303808115580002e100d078502810482c1c0c98421040f00ba62000d9009030701c01c10050700020400e00400c11030103a04c4220900c880020301856082c10940001d20840e0071103141848034040701c1094545494001d445503042c50540746e28102900540f8840090030821404803082c07500e40c6c045900342c0101d55040a80e0703003e90040d03081c410f08400c4101c1d01c2d8000101681584018484591440b04556000604501c40c00340e05081030b990442c0315151851101072000000d0041c0304000c440d0705d401781180d581d0fa4020640c818400450700201e410301c031641d00201e088606015503050106030008107405008154800311070741c203100c001350804410034a000180392520100104000d403107682c114100110720001d4120383d07500e8039070303420b4280010389414000d40e07000ba42542030180780084404000e040c0c10b03211941c0d00300080c400c011a90441c0d0200400b402004110030340c5001990380a41c4410000782075451a500740504a0390428000f2a080301c0c1c036100d0fa0002840d66 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 565497625 1250 565496375 565496431
    0x60605060304030f20012d0507080a0b18070905130506030a080304061805070f0b09100f020321010e070c03170601020a02150a090501091410030b0306040506 69
    0x2e1501951022810b1207407580884074140c0010f14a1090342c1c03014503501c00090288218189030341d060500c8203041840c0c00080c1d070905003c0346500e40d403074905020440c405412000050f80614041070000e00c6030f10f0300d80000c443e44800385840c40c8500c928030802c03010581005500301555011501d1984501600342450b080d03070000c8501c1d40c0c06800010740b80b000111450091070f0090311441c000b049240c100b42d48484050905841519580d0050030704116078400d0070700010160070040f03807084c98030305c018002c94000910001c80104002809c141035000c1e03403092060302e03c8446240341e96082ca05182503800c800d40400c0c05256409407601d00070501c424024007038440f40f264142c4826185e098100c4128040d00c800604060540c041ca081d03031001680c42d06c03440c4071200002407080d40c8400c0c04290023088650141c0007141840120001070040c03800c502c0100d8240407044502d02c4441291b51012006824006030154040c861141070004101c8003040705c81c4540030b11828480c030010340010540413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 565498875 1250 565497625 565497631
    0x8060108160f05010309020f040903030f060f0303020a12020312041424060d02011e0302030a0b01090f1a0712020606330708370309030e0f040e1006030606050603 71
    0x180050b441000b05500a400050050f030005203203001c9012010046420745e1010041200000d60f81c1141c182c10310500e108290241208400c5030b0991415903401959400c1c00c000301403c984036400403545400d00c200308843c809001e10f068904223091611b0802c4404420000207a164050543c03038000300351665406010722449501c02800e00d458040500507030000343c00080c0d04020200c01c1c4501c2e0781e0100d0602c1400a4803c1d1341c0143e0328903081c00080111880301d9801c50400c072250304108000764507000b02c1401d9880002081406000c41c00105441381304041d80100a0b910121108400c240c022504901c0b41c6810b503003814011400030072542da2000c2e403d900302c8069150f049940d40c000a00d0740a002018481c07407030790340b0309807942e100351092004411200e0841d000b80401c0c0c400c00303421301d00c115101c00c6450900740a02070041d03601034145d51054034546e0280c040e100081c681c641c0c40d900b113030100070180c07400d55504c4420348a9000103040b41e8002684c07614100748002a00c0d0612300704681c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 565500125 1250 565498875 565498889
    0xd0b060405030d0f1e05070f1103120d0e030a1403071701090501030308090105220507030c0b0c07120b0604050924070e18010509130b010e0a0f09030e01050a0201020d0203010806010816 81
    0x8582547c507565031100145070a015948003214600d501e0268a0421000c04e1408600da40f030780c3c03500e040b10004810380e0820108e00c2e80a41040c04100442c5800c00740112501c882510019100d90f105a0200c42442d40c8204000c15030346200c0000807425a1a840382e410303240640d484040a940300e4102600303a89055840882c034500c00200e84a1030022603210307060f071912a409480c2c88a0381c0e92608070000140750006c8550003000104101e4000e820480580104000b4824481c4002c90703445030b40714100003c2c2618010b039290400070784050070502c035a5200c904503620100340901c840440c035100c03103002ca407141c0104050140120003440c04e40c608000440c0c1d02c10b44400560308020500140060150040d066081040609000654030301c00b0640a0007884400d07002c689000c001c401c040d152641107101a442c41c001c062800f00b50700c038210702650b000a0a206d035582e621850300300d00a02c1005806d0300074520210000c51843e001003450340c102e50140b01102c1c00404a4620500550402d209542e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 565501375 1250 565500125 565500127
    0x140108060f0f060a02010f0e07150f14090a09021b06130b0117031e0706060b0702090a050402120f0f0c10050313021c060b0a0801020a02030d0b060405030d0f1e05 71
    0xb810324a0141d0044c100d07002144004075502810a0078441a00ca031011240555001003209106100070111091216500361a1403c8140100640070b0000c001007494040ca1403c000350a2089488224090004011202045503583da001a106100b00845074003582c1500503407011420078110070002d82e406603040f00581989911f03203200e40032102900c071604e40300e9010600c10070b08109403419400c4032000c1000b00c1c850307842901c5e00d0b01d64101c5186030018a40ca04003404a100941c0312159010740c0640e40510018040c0c0351400020071070100804040ca00344281c2031404d200003400718052001d51015011144964030010070444000c18100c1c4120004405200003440c00341e4074404901c4c41030001d4103600142c511841080c1c441400b40d442664140d80307480b0214482e0401160220061145074021400c101d019a0000d403a1700c1004007020346141c030b448868140781d45200803a401404001c049030051a103401c800b501c1c0005d01590300020414224501284501a901402a82c14941d49117 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 565502625 1250 565501375 565501399
    0x606150e04240806070f0311040e04030c02191d070c030c1511040608070f0806450f04020a0302060706150905100906050901090207051501140108060f 66
    0x310004001a04004040c8010b05468419a091441415014003899006003109213000364001e4140c1d50a02248000c1614141002505490483c181c8051700d15109003c4d519880e6802d0440d10004000c1003c1d40c400414020401b408240845403001c0303030480f58214010143c1c0c4040c0c40010300040781e014001c600300900020019104481c40e503c441d200b0440041246081d05008080742c86882200c0070f90f100000f0107109071034120b840300340d01042d01e1400c4040f8250140000785000c1025210a00585441408143c8001c03e031f003880c5103403079006d80b0b03008441080d032907100c030580f1011030184500503034907021a0203604112030b003034412500944201c8a40385107901340443c50b4400d501c20360384180da0380c2003445243c107031aa1240c01072072400e60200d501d042403001c000f4405403541c0710354403091400104014980341c1c000058119a1602001600c50006042060401d90820b040c0300700a4080ca001003001c016541280806817020790702e02c04d103030b507070081407042d800758008030507904c03c1d01c1d0698 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 565503875 1250 565502625 565502629
    0x3090804210b07030204030c0e10060e06370c11010c0201030f050f0f0a092f190e060d08070b1512060906070302270307050a0603090606150e 62
    0x3100d0094440751914051001c055268a0748592083e1100030029400050410a00c83d41184da90040d200300b104a40c2c1b207060080c88010351108501c01c80d401d0112a0381008d41c0c03565000180d48550b18442c4c1c105a488200f0f0200c501034030703944080c3d6800c0a615401d80c50380349100342c03180a80141c0c004548501e81c0340c504010359181e40e0400c000ca04042d144c44840101c10103d014407405400a02020310b01414200b2801c101400002c0020b42c40e00e24004039400440c402041c941120300f0b18998540303180750710003070000c2078018201c6a550800354160754020b0450111394040d0403556014036146140d00e402d41000960300301041c0180c0f01801c140541004140c200280070f412988070501e1140413214400070501d0600c48660783c1c000745e0407010030040324280c140a25503006000d450218030b40340000ba0b034100d125006002000d9030700e2110780b441d101034900b04154400703024010481c0381495038031070004000c3d146000c000c480e5541000c20018450340f400340b520340d422a00791141c095808821003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 565505125 1250 565503875 565503899
    0x180803071202120d020f07020d0b090609120a03050907050d0c092d021b060a0e010b0405061c05030c01110901020d02120f2206110f0c010206070c08090a180c03090804 73
    0x6d015001c40104100702001a81c40300011000d4070722030240904540fa0181c035480c10454000c0900001d0f4000040355110014034500300c910804990030002101e844000b0907030b181c0910394100d16044000e0701d0801017440300c024984011110b60311400d00070400c40a18800d442001c2c406e49002c481c0da40500024003405607005045000d202c030800910307001d0120f0466141c003c0c2a1082241c0c0e503070351001001046e500f0b00908156600548051100d8200700d00400c840518098240c5081411a81007004000050084903d81c800c2c1c10024007c0324000c03014005190300c4652810702500c19040e40011031070000ca0840d1100000b0740845040c040020306402490380030f01c42e40985046c1c01c0a1582c51136505003102c60140000340d840344580c4d0981c1c1e180a241c01c1940d0900102a404079200c00707034580c0d00080040d0b110311203182608583c0060f103082181c6006030985180e00080860002c18000020420707100c40858124083c004080445001d0f0200c0d10b54800107021440b08010034024158848 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 565506375 1250 565505125 565505137
    0x7021509010f21090c090c03060302091b0c0f0d0f0807080c090103180507050a1d01030f03170f0604150e18150406020309060a0c0816180803071202120d02 68
    0x1910a20140300c50982c0c0d0f00840d000c05008581e14450010280248041403140400c0c064480c00d0412a0340d05540010341010401080a034408292150072601c041ca00b46c207032180240c03480200c0d400a00d840440390b440309d50481d4a1000103101c0034107000000d1143d29050302402894845d1101500c905050044036440340c020541410f483c2c1440109a9032082c4a100e100750140010b80203ca08007810003c1c501803581c0300700440741c01c05560813105805400e005044079403160140003200c9451030182d504d8500303482070525403030780141080003403d00d035841140324030406c035804c01c5142514807841e190300303003d8080c282d0010350850000d0f50040d03010412350b444102441c22100b0b2131003034518041d00144101e40c00c496994010040c400004001c001d1250004007070a07040c44022a01d500042400900030170707404807081400c81c503041ca20b002e026504400c0711407450381d001503519a2003142d907a50001104850400c901c13084030201c2031000c2548005402c034a40224541501c4039a04006034201d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 565507625 1250 565506375 565506407
    0x91f020c1815030f0708010501090612021305040c0504020412020301050f010807030305131e15050301031a1b0a110f060103020603010302060c030903070f06180605040b0f0910020307021509010f 85
    0x1285031503842c04c010005100140358400c00460b856040ca9100002d0b00c0300e6500144911319142c1c100c400581c0c45200c0044403014824000409071741d0303800d02c803080d00440d601c00d0b07411510010340452000041d240c0760542034000da000384000c0c0c582e07a0380c403040d0901c00d103d8078030150040301c2d050001a00c1071000f40003080c0d030590f034078007078940f034082c000200000300c40007884071410508200000c0001114034902e11025041c103074115031441e00c903202070104046801e1000c955800004840301c1d00f9400e601004000d4501942d05d52441000140202440c074400c1540d03449510011400d180c000a0258180d03540035240d1820341c6d11715800c0c0540390b008041240c002d40024000081c541c0c4003041a08010500c502c88604924a010409041d0102c2203640d52200784c00380300c3c1402040d0b0064101c8086070b08842500f0307a20405038518030300320b005030891f150f401003d194010707248590010181510900880d40c0c0b0406503080d404a44041c07048c81d01045c08035485044040202e401103400c6400d860038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 565508875 1250 565507625 565507633
    0xf0f010b0d0b0d050f0606270708091606120f05040825060504051e0d08041104060803030a150608190506011707020604060507030e0a0f030203091f020c181503 70
    0x290341c0c403142081da038a000c1d083c0d1a8002420448503181c030701c5101024668101d00ca228108c5a000e4111488800074000e1050206410108402c0ca40c02c20034502c00031044d1aa0058807900c800c00280754402103181080501e00340011900c0301c1384140b29030f50187d94028000740c6005a072040b040f8000d07840d002071441c6010006038a001041c940d0250303d11076846403000d48443c004551080f404034980f888104a17a40c040c0400400490704100e43c10b800c50703000340607a10340c410442c0c0054060046a004001180400b000b404950b110b16007107a61040352001c0404509600c8443c11281890200c0e0551401083e80c0c19042115681c2d9010075006101072404100303801c0c0190304042c140909035040341c0141e003d40c040000740102445000d421035041e10b41880f200610408055840e09641c901600040130034a62408141c000c000301c418056025103041c00c48148004d0404038a01d5a0300b103840540185003000040e4500241000504447c6010040740b54030741ca200c0c01c55004440d00950b8141c07007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 565510125 1250 565508875 565508899
    0x304021903051f050c03040506060d05010f020d020309010b0409020a290f0315010206102c0405150a02040609120507091506090e060d03081504060e0f0f010b0d0b 71
    0x30034003000c000e03d031100180021520b00625030b0800c0359030042009400260900a000011704041389260300090100e400d00d4201406050075801041e4910700542d40910000f880c0b0a804891b80182d84500d07500002040f030141d81c0740502061302c2c11703c02c0003580414042e0081c00b0030102860810062040000740c0141ca4006c24940c140700d034040e40c1503148000c008001c10010034410b80800e400600300388050040c4e401d05900400b00c0050318011140a0a00340100380e00340c00918010b022000380405449c91203050508050b03495443c40400b1940130142c090020b20510074034000c0754101c82841e510048960300e0301250501ca807005c1e11045403d4050300100003017040c000d00540c14007400107400c450042e8030b016405005600c1680c40b082d05c2d9a40101005116034460015460894060600354104d40e44c42c2d010081030241442040d5015240540c0807a14010010990b4401c4942d1070000086484980040082000034490030a10060420001e8a070054580001d88680c80182800c0d211700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 565511375 1250 565510125 565510133
    0x91f05012d0b0a03020702040f0e12070204230402280515090406060918050112020d0302070e0115080c16020f041503050307020315100501030b0d08071a0106090b0304021903 76
    0x40d210360300120019801040301b02c1545800d102d41280007180000c1009222040d840e89a20360010f000102c84071100811100b0954550380c00400e42c2e03141400e400711015080900d10002d071103040e10b050b0b00030501c412042a5068003400101c3c0e90081e045a1182c15518103010401020344840c2d1956640c030050109101d00d403182d00600e0f0181006485036408242000240e103110000e10b8441100f00e41490010003680c0760300c880300c114603134041d1032041564005040a80c80d01581c1d51100e1030004000000049070141240040c603026a5587d4201203912200e06903480c60083c580142d00e09110104908014602040c0e6100300c3c0703001510101d0302100b4ac0e03160700380601c42903000f43e841e0313003000400c403046180c2802800d490504003000b0705e007641000170701c84d2600c8015020b118141545c42514080540c3e80416982980303034003c0c05a950749405240c0b844501010700c820004061481c0008280c860103050110156100640c19a0440d91642c080107024602d150420121401141c4084041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 565512625 1250 565511375 565511377
    0x3040c08010f090203120901080c03040611030106031506170a2c30030f0403030b040207060c0e030c01050a050d090c08030703020606010c0803061017091f05012d0b 72
    0x104803100b0000e0a01c00c1c0f8010305045c48240080034203d00030070000d14405c0c0c0c1c2c20140d0300740c012827806403050f2aa6120702c0c00d1002007071301c81c1e0310714104800400001209541074001a881d00502c2d00c0c112170090f940d580a884601b030100c816000c43c2c0c0310000255400f02164844101142d01d980400009101d940360401e140315804d200e031f111900300c052008510340040c1c05c0c546241001c4d0318502d480112041c0801c00e14000680725000128000c40403030141031090704030140440f0020f000310b58906081ca00b40c0010b0151980050108a056055512a16021070379900081068450510740340842c00c00301e40c03503400000300f04840c580da01001c002007003600c1c440d040030300756103002180d881c612824064038040004101c2810010701764640301c00540907400b5a0340200302503030120b4101180728000d46898140040d803020b0341b800b403030800020040004400403000300300300c2403000c01d0f009400110f065071070034050090b1040307500046064200e07810040700140c100b0900e40c04172054490310341d5091 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 565513875 1250 565512625 565512641
    0x3030f07060f06090c201b01051b061005030c0906090705130f030308100801060f09020a200303010f0504090b160507140309280302010f0e090a0c02010c2303040c0801 73
    0x824854001130160543c1600381c65015600c0c5c010030b00c07e10390b00b1207000720301070783c4004504000000c2406030190550b4290007103000700c140c06440c00d900e0b01d81ca60782d0700030040303104440c408d00c1905556660b0b401d0a119450045001401d0202d003075541140643d51540206001001e0807803c1c0e90005200400380d076404041c61084e95a403150b400c1010903103580c2c9202d03070800350702079140c0035041010721468000102207d1002c800941c48454018060700ca0400c0101c0a8202c100046500d0b1040e0002000842c10303203000c0814624020303142d409000880704103d80050440140c8004144000c8003d247c2175001d90042c07900500e40359607540c40c100644200040c408035540003084948003854424039540450032940351401180d0700d90440100303103106600c0b0107070502040f025901c008510540305081150030141c990002410a0100d100050121050030b4006503e8802c1351a03006210702c60034910844100e04654070340c08103901c5540c551b44050710850305000004000280080e003800358106c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 565515125 1250 565513875 565513877
    0x301050c0c0706080c0702090a020405030f15090c01051e040803130e061c170904020a110705220218040906050601090b1e0306130e060103060b03030f07060f06090c 72
    0x62140c4040420602d0101140c015106001c01c10040104114500b0192003103550100c0741e103035490315410b2442c0000e00c42c40c1c2005425000d80b80fa2903070344030700c00101c00102900850f20000d40d03580b502c00d250380780c40d04170a9460004034100070200401d400302400712440b0b80301d41e8207580350075541d540b064a0b56104800e80195000c0319070040011803150481d01d41e00440569251011403910b4031561011950100c0061030540399403280c0c0c1d220010b25040d1200c03079002600455403541c1088000c1d003201c136008640c14040c030034180c0104860a107152a0740d4545070801089074051010001c45002c3c2d000b480d804451043c1c2c00c4030080d040d55540c010b181425008600024150070001c000420701501500310791806641004091100408850400751344800511065140d031545000903901143e106c0e1442a20340c141341d01c510708040f000ca105812680b0441c4204904035080040c581c82e40074020a1411a070350500480c400f00d0020340208842d05080500040c156442d409084100c8801d0b44c0090 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 565516375 1250 565515125 565515127
    0x60f070c020d172113020d0b04050109050712060608070506120a02090402030408030106111b19120503030601091205030d0c03150e0106030e0c0f06090a0b0c060a0c0302070302061b04050301050c 85
    0x1444813a160000b958000b002e540c03400c104d405050300403840e2102144d20003000d182c100400501805020740c8003446a6910600361780c001550f81c030410744100710394042070b0b64461800c80700099041c03001a4903001c5400140000f824820b080d01d244500d0f0340003e0010640b9034080100c00026a281d200440c0b19502c1aa44d00d0380701d50504c900100704107548020341110350301104400c06482c01c2c050140108080845400803080444402402400280c0d881200d041550000c410200708000c000b40d1301c191000e0382c0c0c04801e25942d01c21545108440303000940070307402c200941c103100503a50300a8900407000d82000f040c10203c441ca0f0b5280c01c22180c0c4411200d40002005225640c2c2c94003400011004004c014403501401c07030002184090754668091107280001448021615080c841d4001042d000800300d44070146041d42d50b0315803400301c031340384a02c5203048518100d850187c820f07944416011b1307004098035924520400c00e4022000c00101c80241c052100284594003400f506200750312801382c0e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 565517625 1250 565516375 565516417
    0x50c0d1404020114030903091c050c1903060b0a17071811030105040506180406050103020a0611101509090c170708030a120f0914060f070c020d17 64
    0x240100c624194915030961018030a10000d030b039002d1910203030741c41d044010b00c1d0b994a680000c5803840c030070318085640014200700728402029401144440660150060300c0b40c20980608101d0000b0203850960120007410100340003149059004565450000d02807200c131584a0b5803800308420000e2a410265025200a111448211700b954500c04800d1380d003407101eaa462800301d081804140140c03409143d64100050b00c0b940d80158003c0e0704c01c104004410903040604000c0d000d06401d0105034000c010101c0006980c0340b0503003028040c403200501909508407403800200c050200d4803082141c104003c800420105260301c0341c20122846203411400f420b190a860640703814000c1d014034016002a0010440403001008407055108585010011400d2868014004210700c04a80325054903020780728007004045030342a03061681a1044900c1c0350f4540c0c0b030a00030004100e0742100020200c109080040c2401c2e0038003100a441000180f034001d1504d4101504ca0708444107925599120000c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 565518875 1250 565517625 565517647
    0x1509010c03381c050615090c0a0804020f0405070f02071403070b07030912030305041a15010e040908030708011701060f0b03150d03030f06060918090510050c 69
    0x1074510250154040c0e21102c606a15801072181ca65140281c40d01001180303219003a40d41d000605295108003851100082282c100155212411241138510103142c1410641d1850441d8200c1d04c205200403400340b070011001c9040f1040d00700604120b03008040d80301b5124143c1d40d40d008052003844c3c103030340d021036000d4210b00082c5802c00e20342c00080f60b4007a280a00c074054801181c41c00655070009003a40d43c640742d505c0d0490790303400f107a8042200091100004c004156051b00002d0042703001d0041a44407080316002c0c8002210306507040c207400d0039425050801540140c14001031f0010045c030009413451f240e1101d1030b80c0c1d4001c485440025a03048014000e40003146010407554902c0802005110b06110721040301a1180c000c0e14001003004c40010000c020002d24150b89800c050685401014246000342c0503101d0507000214040c1000c1c000b040c07140c451007032070003194900c1540c0c4442503001d80c1c2c203a0051204080903525402003550580304040b96000d107d000310401242c1c1a40c2e00a2006 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 565520125 1250 565518875 565518881
    0x50c01060e06060301090b0d080408030901271809051c02060f0417090a03050102160606051539030301030209180a23010908130b04061e021509010c03 66
    0x8292207000100090042944560381940d040da81011000609040c880000039690107809a004108410006000c59083c00100180000150030b03264030060b2800c00d42c0340414901c2c2c10014a4011240f460108402c081a1144500c031204860000560003000c3d15180d003020441060b0320320240c0c0c101003089920394101700c41d5520201c1a2030094050810341d0f01e40301c0c13461520f40d03140d050a10221384100d490703540050000c021503011008565a001d07030006944102414030003600c40f2842d00d41e0001c0c440c28441d1407086070311480b00003540740c460010980710001491600820b01701c081c50b492400c0c0c1c00c480e90202030100d00518000c58030307585588100a11044020310407010050445240703202110009610a14039a12447c1d0030303034102e910055003941038600900c110301582010b00e118180074100e0000c100070b031043c04580c241952030385002c003011701c218480e410008140006120300c6e02480c0c9204800d031152403040d034030080c00350101c0c44202070060365034a140d655507906290200790544 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 565521375 1250 565520125 565520129
    0xf0408190309062a1202060901020a0f03021305060703110d0f0e010e01111002070302010e03040609051e0429041418120f070b13080d0921050c0106 65
    0x1110021400d0300039900103254011512544007803204400c0001003601c0a14580103500c100440f55842d80c015a0405a10b030064440d8150054003a040c0400c22450b81030086401003003403611403894000301424110029071051003800e4500001440114180c0eaa0400502041d4000c4c1d0300c501240041029550400104409070310500651a0303504540641000301c080c078046090814841d9609070f03000513541110710025400d1180035901140038242207a501a20200740203a00800040c400d40300b075281c0d40d100324000e040101d504048200400e107800680d5111540d240d01c44102608001c0000c5003c1d94007422014a40d148007481024944c41c40c416001c0b000c42c41244d0038081c40c0d1055610150101025241e45940d00404070f50b54584882001502c1d042c0c6648003200b9030704c1e0242080a601900406070490b0750303031a001b02048071050350844c203004641d04003054a28084403186203100402c6142d03000c45d1801c2d00c0704501c1c2060b89003407954407a0030720300b9111180e40e0303440100603d084644136 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 565522625 1250 565521375 565521403
    0x109051510030213020a020c040f1d0127050f100207060b091603020d0e0a0516080303091009020a0308070605090105180604060f1407050a0201050a02090310050403140f0408 76
    0x207000c10405a07866030b000c400d0f000a03a040059481110080403401d20506004044d006800e2010380850402c05901495082006000340801036680307007402c50a841305400500a45c80703d00d8481c01c008082803a0080346240700d030045400c0d001950b21860b00b09680c07143d039490550360101c1c000d803d00c070b0070780070b0182010811298800d0601d003102c0c5040510000400c001d0402d540400c42408003002a84038411488900089411688191620717903a509412000c14551200c1e5200010720035000006990040f4a00000f0309404d040d07030200300b4002d00002c00d081e030707004201c004004046007030000200000c6004120100321440d1800306142580e6014000041401d034010114020210218a40fa0000e6010740007180c091400070f0007101031b105603003000c941101e0610500c0382d40c40e00080100101070141e002408a50740e42d607045000c81c000d8440d425019000a00e625074203100d00d43c04582d1052190805456285d03c070f484d1041150400c8081c0043c00e41e0003d070512060101b044801e240c8011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 565523875 1250 565522625 565522651
    0x6220c03050d0e011b0f080f040f180e1905070e010b03270a1e06020406021b0103060e01030f170f1b01050403051207030207050a0c03033b060c01090515 67
    0x810018901700388a208054082d00681081604101c584802c603002509844165034803251181f0310921410a54403402000380301c00c9503d80c00300303100d40c05007543c0803c02c003015000b48284c2c05001031250248a1003191507000d491000f0035901041030307205000e000b44039040c9440e450803920b03000c0302c40ba2180c82855040c0d40c9a0440c1c243c0080054210800c6520800c03810360304040a101850342400c078500248418000b04000c14404d80c0000d16208844101d1010b1604400c154019401c0314907a02455034038005800060020920044118120610400714031004611205607650036070400d0711042c0008000103501c007100e100220b46d1070480442c00000300a242859900a42a40310b003a03040c0c0349084810001a41c21402075042d16205074011050720002c0b811890525800203090008401040111180070b2001351140c0d60b20b12107a102d03100003030980202c480c6a007854010301150319030141c0e08010788000184207010b41c10303080380702e0001041892101103079006070344002025105802c40d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 565525125 1250 565523875 565523897
    0x1080f041101120b09010b1e0a02060c250506191b11030d140609071e0302250c03141f0504060b210601090c0206220c03050d0e01 57
    0x4200c404101c0202401d10403007491482000901820071a56840e500200110002a0900e6070750b00410701d12107000c885106d25601094400058015441011b00582c000c43c0040c0c00641c4c00c40040c4070300b42c0c521426114041c609000c1c1800d070704c040e82c0100c400e40c21400a22643c0e0400160341d0140840c00c08003441805091642d00022070301029844040101c1281142c0920109200b241d00b105120102807140c14030014074945212410707030350039018003501c100113410544105045010101d0020000320071002e800022400307500110985070303040380d070b80f80001c0b208494541c003150ba00748608a0101c01c28a0360070300103a2540c1c50050001c40380c1142101d50b4640341c00d0209804507100c111400a020785039420200300800c090780440f60081c0c90f44080304c0c0501c1056140c81c0d883c44201003110916a00d17642d0140a994035110007c015078002808034050741281020425007901d100801d840482003a11541001c6005600a4809822400792042030750b6000044c0d485041003802d194014039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 565526375 1250 565525125 565525133
    0x204050913120207080a0f020411120712050108190206041508090601090902090a09030212070503121f0e1b03040f050106061407120905060d0f05181903030e010207030c0201080f04 79
    0x1140c01040100f140300b0101107c0300f10358455000c0904801e44490075901d85400103400c0c0d0046009075540f001040b51419000131407011401031605944001c8090301a40e0340320348400201e4a001002268424030900c004200500106e170041212010366a0740d60701e50600031213060030702c030043c0c0122841c241810800350250711100c41050b000340b407003c00091600c0c07403410105c1c1441c80c12181c0044c10000017405205105000020b0701400303150e03600a840c40d444000d091002080741900351000c41504480401c030b58010400c0380d5920802c0303040f40b410001001403ea100560084038203d8518041c80390b11801c1c4182446441c02621041c01c18030780c07400124041d0692401203004c02006140c6013180c01d03054600c0350340d00c20005c0c1000f400c800d4552500f2814070000d00032035171841140510380030010342da01d0306108440500e8907041d00946416100421521660b01d1880c0c026401e141d1100c4a506100c2d40c00d04c000e14a41d40641c6c0c50903803486042c800100071280142421450701145400d1202103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 565527625 1250 565526375 565526383
    0x2070c0501050a12060e0f1812070201020a02040204030b100b03011d181203011a0f12100b1204031b03090e07120e0102030718030b0105060d020405091312020708 71
    0x540d4090030843d44071009014116680303c000c00800d880581803034400038000061396034250140ba0314014850465481902074911002e00c065290940d50054040740f480e20000b40040803c0c50041c03050f1400c00c81d80ea004030341680c1c03040d40300315403405c0140300f0800e0301c044040a07140600f074602070280c655458800702c400c01070007600c005486031228102040250070420000081030300080c040e83d4440041110009180e00309115035020642101d4074202001c4400040b0b0f502d034035031601c8241c1441e82980311080c041c2401051541b030441001c902180c2164408041c002c45250b1058803122071070946401400344440303440d0003a42d4040c0c2142800041d80101140040e01e540c035800800e01e07a0342c0282121540e103100800721800345000d003031211060044d0000c5200d01441c2c6c449501440c001e13a1400300e50800d501c8054042c1c00d4010043c04585001001056002e80051015060030340b184002508100c0c00d550041d58008040b901a042100d0089488200d01150024080d441c0c540a9003a8803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 565528875 1250 565527625 565527629
    0x5010c0f05030a0531021e0102070b030a18050d091202091801021b0124051305090a060609020c2e0e15040b190504030906050d0603080a0302070c0902070c 68
    0x2c11070311240050300398280c41090816100d10240c4c491840f0000d900c6800c8500c90002082c2c0c002e24401f01405001503041d00c5505003280103030b004040c0c4503d806080b00140d003003d13000c0c00a032500c0c0d244a0754402c0d46100d00e03d201d03074014000303003000c4014054040e200442652245c07090308038000010015030349144a1540c0315030119201c01689154a441900910905070084003d06640c407110341a1441507004401442100c0e0344c40c00c5a02e00c2070680c0d0400c0344288a240d5102008401c0e40059403056006503407c00b0700501140c40280040e91802c09507003694004186056011450841600042080b00c080d01c0e190741e0695034440c1e0000020701c0e0003581400510140e515031b0880d80c500700080003147c0c0e10000d40314180b03115007410b00d420f080c2c290050354103d401c996900b080c4080001c00784549801940d068130340e500c0407407801d00d040d10325410001c2c150800e15610600000400d4070340004101030140c0e580c006941d500e82e4600402d0098098012454451052100c0350005500300c00c1d25003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 565530125 1250 565528875 565528891
    0x1006120c0905010507061401060504050901080c0f06160c0902030a05060d02030d2735030d0504030c150b0a140a05010c080c0a080406110102030709032a08060405010c0f0503 76
    0x140d145c4490034032101178060300c05000c1c0c094002e600001010756004010b0015142c0031604125580d07610b080303440d904c90610546a91000c200c0c920301002e45000401405423117206030f031114071000503865038925401c0e56400500203a070004200201112148540c55128900b25482103440041da00829582c0142c010302a09104190f04c0715820f440101c185a0300e0030240e030521501d2145c8841c6080245030450b40c1204038400a5460700d01c0b0602400c050f0704e000f00d00c4038011410216040c004d903014000207070050701030214074040322010840d0b0700480f04010182120202c1c440c041c03041404036905840e40000c5140d0483d00092001c0c0d51024000310071504240380111103e105400d160803188104148000a8442c17045034500700820708000e8811181246c42c0d040c1111103072800c15080c2d100448110300054110802440000c402c00300100d6080c8120f21408039101d602c6004225012054000c10010740c415010802000001d0041d140402c003240f03005440c1c010320800182850002801c0e81c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 565531375 1250 565530125 565530127
    0x14060f0c0d0b04060b0702010822110117071d03070305150601030b06070606051903050d11010e03070302161508010b0306040f020708071103010209030a020f12061006120c09050105 79
    0x10720101000d410000c1c038080c004008000c9140c1d625000003d83c0c0c44a5800c9010500328800900d000030340c080401c1c0c1c002c03031802246040c4a44d581c1c818610041c44481a41881066072030300071400078081c07100e4890480e13900c605c401c91403214100401c80341d40132003c6209034000f600900c001100820381e55060018045039001c3c80c0c40714070041e40902003a00d030440d00101e000c1162024003103542c014031300f243c1040e9500441d41100c02d1150800e440140805400740e400803452a5005200707607144a0b0f42c440c941e00000781c510341c0c0400349086a1111206500607800408002000507800b8200d900810942491071241009a4009484007405203c0c40710141e80102c009500c6840d9500200d2031480c0c0120219a00e40b9186405d4069401040040c0c1c8c41c416260354400c501c1c141407007140e42c540c20080003400001c1c0280c1c00c00c2106e0900107102500500003580040c0300200c1000054051300d50401c002c040d1900b0007070000c4c024103c500314141154140181d404c1c02c6030300440500180c52081c80d01c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 565532625 1250 565531375 565531387
    0xa0323060603123f100905040309120c0504020f18030a02030c19050402270a140f130507080103031106011a033d08060903030105040504150c05030414060f0c 69
    0x1401d02204112031206070301c00c01c1d42d01207180313200701228620410100c0d007020329180c1c50320891310840d0011900200804c070b502d402480000c01640c0e40c170004501c20300580c5116030f20b07840458141d8102e281c803503502e800d011510311341c3c080742400080c4800c01c00703500400c1150340d40e4001954803402084103d000d0440c0346109007112002a442401030100540190340d6981d4428112014001001c42d017210601486400070031031524620940403100c1f0300210b0f1400a01c110104000c1c8840d90201a60000a0b84041000004a4058a0701caa1034a440c4c07090a907146041c060b01680f0f41c1180c81c3c0b400d403c0750340140100e9140c1c0038003407480d02910310a96240c0d40c4002010018400b400740740c20f00b4144241102445200c0d0500e108505510f08503640c0d5440d0b0b4404e4915542c410035038008445400a10041c041424642d0056510600550a84503c005000d5980c4102d0f2464841100090000010071060041711350350040c1e00110000101158504a50078804080002e861746420301700020b01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 565533875 1250 565532625 565532677
    0x11503111f0e0f01020d091e051513050a1a0315030102121008070b0f09030c1201150b0f0306010c11100203090405010815150a032306060312 62
    0x4000000007a40c404200d10041d64006440101d500302503502c00d00606500442c9540701041ca682c1e45120394980742d20700781c1482e140c051100c69010703a00101d8882d41c4000903c503554030a5401a81081e0118590341d036074888400101c0f04060340001e80180e00c05402048440403480303140940c03910601d14291251200a000d00714641200f40751030b855800843c48412600d0f410360028090072600325000342c1582d590380456141c0080d8800d10b95141014004c2c0300e0161301e40d10003003640080040680b668184981c000407406850002600400d0795561350260300c45250400810181c036500604d241006030412100946100040c04c1e6410040080d03c030004000c0703d00705003140300c10000d01d850fa2084580600035a250040020a132080b400c0100000b01c0901c003042041c4e0345102802c91131041c0e40c0c3d10b1085209501903140440e00f0100b00c1c0d00000c00720f184d00e011880518000075140c2d20307000c61810954500480508000d00caa0031001d4680303c550000c5007100c10329020b06c100c0302462659880 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 565535125 1250 565533875 565533889
    0x90127050327040e0c0105220902190e010c0c0302010f09180c0206060a0e0402060c071d0a0b0109050f0d020d050328030c0e0d05011b2001150311 64
    0x45040900548060207002c12807440303505603482c41c000e4038208041c07050741240981d6808040007484c0030500803c404020781703600100c4181c3d942d0b143c0c140c2c0682a5555881c400480c2d2103152011030355078014070154442c90344020480c01d4200d0918210b510320585486410310f0312814800203040c0803d8003411059240030382c91002c01407030701d07c40340030300041200c2e512030103004450080340040c010940011801c0c0b500c00400b1054680141030300149a40c0d503030900016038040c44600546204148000400000c01800c0459040d1070b8400d103c0b25082440170383c0709846003111124180108100144100e032500854121151001c5400c010162102e00200307031404055000500350780030009442868214440c01e0002210200042010400c0044011002c44030b50a040c040040c0154084140170314240c800020034078058000050102c0a03080e6106101c03d4a0030080c010400c00e034001005580c2d000111940c9406482c004d1101c0010701c0400d81c1d40c0b00c0c460000400c520010b81d010013050b145c1c10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 565536375 1250 565535125 565535137
    0x70f0521011d0f100e0703030507020d0b090705010f03051501030c0c0615030c05060403050a020112180308040302010c022b11060c040504150b070204240f0e0901270503 74
    0x2902c0c4019a030b5a14150315a01c59500c598000d2060030416150300e8403d114138010750806501800d409415946c0444041e404030303005992001414121070081404003401c41e010b15941b000514406140c400054100d8201e000ca490034107103080b0420001441001001416070001d1800003801300c120178043c0c5941c0c1d900c80e0094003040c0f03080c5400d130441000c544920180c90041140310000e42c0d9035403c000d4280310702d0000804e80c1d00542d0207080103501070603100d0304c085c0348400c0100d84100703184001c40703801c1c010000135030004121009200c1410340a03c244c0c0c080d8600761024011181c44050703504a000c101440e0404500002078909164601c1189524402c07c03948064404030b081820030012150000e000389803003249401007246180d49018001d000b2503907511390b01c0d030811002e0340802c001008491401c05890b041c81c0f803000000c25a100366800507010703000903202481d0601c031500c1420340e00109528156850200b80d56075000400b000d01c0100704160480b0b02e407944132454002d04502440b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 565537625 1250 565536375 565536401
    0x8070c030e12030a11010b19030b0402130f09110405013506010609061209111306030503030903071e1e0c0902040914090a081b030712050309070f052101 67
    0x204007513035443d030301c0b400e0300c0b180901041c000d00c14000311008001611154102c40325580b48608420000500f00c501030503401030004018529003003000b001c0d0400d944074000310002c0a42d489103070408000c807500f003201202805580070401503060040041419000d0b004212101201c0403980034440620034010708038a80900c191802560350b628040d2222040380500d4010074000e1004c2c0049520500c500c41050360001e070049130445440d000c0c0039400003038180110b440c070348035000800800c80420007540101e8900000716612411030a0400880750440580c2004203104c20001020a894151016001000c038000741c080b941e01d89810b41114200d0b40c85803c5490000c0350000d02758182d0351100c207800541600340a40d50b9600c036071070f070340340c040c0e003500105001030910000740b0440c110050864041c859004582c03078000c0d0b544402c1002500f464107100081c200004100341d00505014940083c03904031480410300d41004000350310020060000c100c0a482d008a0000103002500314034254008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 565538875 1250 565537625 565537627
    0x616120c0801360b0f0a06020d1b08160302161511060402090609100f0311010f020f070b16080d0504020a0f030b060d21021606140708030406151e0608070c030e1203 72
    0x587c90f8069120b4500049480208000c81c41c55051000c0b0051051444d5600241584c070300540403907038001104400106808600c981100a174000c000f00d84040003400555142c41c5082c5c1038104024803410310b2142ca001c2c0c82d000700c402d010060720b60000454001c90308481c0103079140d0354000c0d100c248288561010010743c002d0000082030010303500203814081e00c2a03031980d8000310180e0060ba50783c40c0b1040c0e0b41009501c02c0d58100004624900a03040341484202d00079500142074491902c00d422840404803441c2d0740d01e05000c11450085120760050404a002052880ca191101141658006c0c4400d015440d449a05410003004508000458040700c441403012180f40300d0007950f9000303814020307504540354500800c00034000d00e00322040c01c038100340807032805c106540c9480941e04040d20403100203486401da84050900d1290050103099000d8099549014400c03440801181c41e03401002441903020600c44001d40c0100d04030800c54041c20070401d00728000011440d010070440d82c650403800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565540125 1250 565538875 565538879
    0x15060414040c0e07030902030a02010c03030e1605040b0906030607030f0b1e0103050a0e0307170909070f02061005010c12090b0a020c01020c060c0616120c0801360b0f0a 74
    0x310b518216054501d141407150859986071002e4044508805004e5490341c040440c0c00300640c490804481114420300e00401c1e60b241391100d0a1519805914030401000300d164184242c0c1420310901d49103c100701c4414082d030600d00042501c07103001400080c20140ca0756195403501e141600b2400403c0d40162501c4031084000c1c0a2580b41200707a0360740740c000f0b0304250101d800b04100d40034418614030404040e5191040c0740e95080d211003030b211841c805031711082c410801c1a136030724001d051286440d038407850381003c010400241030041c01445d94018400d0b00300280050399104e041080500d0f84030b0351803082d888411134240c4102c0c14035030144079031020008018a4a650101d055641c1040c280c0032940548074200400c0410b00078401990301603488003001890b100766000460005405d00e0a0800c403451064100c202510301d880480d10109084fd00104003480b588081d968501c294540200b0082a40440500340032840c0d0400d000243e8039140032a6841d07441552400300c9150052905031800c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565541375 1250 565540125 565540133
    0x120c170a0306091a1c02040609091406010e0705030402060d0b03060a0b151804050714030c03010303110a110105090316090c09060203120106030908040e0f090606060c1506041404 78
    0x31045020f440c030300c2c1c0e0800980ca503002e082c5100e080000a40145a0b0b0b40110400e800520704500c50001a1303803041d1104000503c18020b4410481e085004220fa802012038214107241ba1610691044005400100402c488641c0c0142643c1c1c015030b048403211340d985060500140601711181681c1d60500488052018100887c0d10050074610195a400c1c1300d01d00054203071045006940c10751f05247c0601407200040d140aa0040b9408441d50a09a680075180080081903820880e80854441d50002c018018113800000c4a14502046d90082c08d09940c585d503503451f04452242d00034107210000c0780000f50b0343d50038005042c4201d40d0313110318610180d8400c40000509101101c19001c500303400404500184088221480b0010180007014164a0b0040403801480724010980e000304c414040800e00742c00e980e03181d5000702070381d1905a0070b504084482c030703041100c06045103124000820003106d0661021451500000350111074440a65415002c41d010b04944070341c41810039001c41c2040200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565542625 1250 565541375 565541381
    0xb030705071a090111070c14060f040e15040507020a20040f06090c03090f080d110f090405010b0c1e0304030c15081f030609060b09070908120403120c170a03 69
    0x903d8201c0020300c0301142d1143d02034054420100d000d041c3c8402075030240896210140288404e11001c5c040300d107002031114032200b4580240d0000c41011074000300307101e02909801030f54081d001007241c00308402d0411210103517482488410040ca50324000d281c0c050b002c0d0308010b4016000700090400c1c0000f00b0318112000090100d4002c94860328501302c101c5118610034440d2403500d650042d40070580c43c105450310500e5410211001500c6c603141d8680095010b01c101c060540798003a8100f1540ba850700c1410001910070507080142d00c00342c240b142c1811100000b07240042c141d503810401c154241c035180344034210b115030740014014501806002034040481500b0b101c5100c01d542d2081d42540314a0389010300916010300183c0000340f0076005001003802c40d44542c98081c425800028040f000380040390880c0006c580903804140d1600c01002400400e1141404003c502c0210529150446d81d600f0b100c1c2c40f07084920820498040101001c0004500d405961000000160350b140c031128100180a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565543875 1250 565542625 565542631
    0xa0609030b0c03090601030f0501060515090f18060607050f06011530050a0207021e03010b03030c0303040b0403110a06050a0f020910080601030f0504050f0c0108100b030705071a 78
    0x100120103001039000c0110b1400d4900551020b000340885074650780b40c031a1800f02602055546550b20080040d403640c3e521420840e10180030300d0140c40d40e841100b046427100b91011407030b015410145020035010322400100d0382c020b208480702038494459091142c54002140c1c850082c512404002143e50050500c4440c1c0500b040eaa40600d43c0c14418002080450390341411b510aa407031802850000025030485036002a0b01c000c01814100c1607000140886480c00d00f030010040900c1d041456400c0a0241040d0094250020340c070780040500d46603940d2100820261604c903510001c581003511aa8911044090311001c07580002540e041050040400703a802103400c610307103000d08680f259240240c40d076520b001040c03451041c0100f141a510040024039103170406581e124403407191001e5118440c0664018030040280b0302da40c03046e0b40d2800c000303030205506000184d020071502408038651030085e01d10110307403180c403a21400d100340c0d06401504402004010018400c0031100d0760411103c1c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565545125 1250 565543875 565543883
    0x50c030c030c0f2109150f21010b04061e0c02090c0901031505011d0105091521010302060d021e071a070302041518080105100e011a0301090e010b0a060903 68
    0x1650071040b804280c00040da2150012408809105c02405440d0050425404243d240240c82ca0948103000701d80d0382d070f4000b8401c1841d1084040030680b40c4085190421301609400c0c8081d4585414500090181c41c0340d40ba400d0818001e180d40719001e244200242100c00c1d5001d4410016400c000b010014990490040540024134250012902d42d4400c120002150011b8488101e03560296001c000b80d00c103080100d03814024200150140ea450f5a02108510f020251141c0e1316842d02c2010a60240304840a400c0800203400040c405070f43c4603001c98900c0303180700c0c6005a66030001807a421640301c065020003000c0c4000f25841040c0308202d1440c80d10b01c48000f0303944405558000e400d0741240118000c0361000094481c1c21103c0c240aa1000d141c045c0e4040e0784100c1141ea6519243d0941d036007103070f0850000d40000720412005010040c114050003042e450821a90722407070249481d40014403c1c1d80340140c640c1005034001d0001c0d4010302c50060040c2c0038485050319100c004d00007503c40c2c44121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565546375 1250 565545125 565545133
    0xb0418090809040c271404020306030114070203120a091101120609090803060f01020f1e0a120504051c0209040b040f1208150613060e12010e01051015080403050c030c030c0f 76
    0xe520115955000146d40c09800d00c00031014010003400000d400042c241500b540d81c2c4c1c0b2102c045c405925903501d1017607450794001c5544020308030440c18420700241c40c42540354103240380c800014085500180b0703000c0c400c0c40c1c50b4010401980d1407401501c0726910019070b01c1d00d4140310500f4000130400462041d2401d5a000d2005e609103001241d684c0c100794003032040c5810ad1024000c1d815011420b1080000c024012152065600d444045e02640c00380c4c04080403c8000a0802c041c4c14013284030301021840b00011196800320f600443c101450082c030041c204012840010201708031500140e44040d0040b0041400100345e020103004c440d010741d0418010100480a400f0600d820011185004540c0e03c5d80940d0514040090300c1820a900506510498105181078142400d01c03c40043d02461030010556041c42d042c01c03040380c505034100040b60711000c07008010040d004100720f50000d0703051400968840302000400e00b14000c01c15844114040010381803000000010031821109001c0e05903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565547625 1250 565546375 565546427
    0x1b060204050a0b09151c150806090a0317071e0c03020c2b03050f0c070e0604062304061e05210d030507020118030c06060b0418090809040c 61
    0x206802188244c5034040304240c00382032400001c3c0c0241c1407280300780102d000c0c0c4071002c03980402500c20510701607405410301a82088107810411510340c0207000d20010303054801c00c03924018680112043c95401d10f154800100352814070604101003011082030b80d07044040903041c1c000f800d140d00c1c1001a00148070320006101585001e40004801070f85171b894002d03030700c6030880c100180d21341503003002d4040c04802e100035200410b6500003030000c4035108d40503002d42403c004501c9030311300014180500662916100b805441100210049641801004100f01520520020700540090b070490852002a070651403040200410282e050f20003c4480000300d03910010007041d0b00403030010301e007140c1e842010260078840c041e40c41640c0040f001e1002140301a50024a0300240040da00202c000404071380050052000f14402c1c07a0140510140451502d843c0ca8580c80c5109041d40d030001815954008000c100040300f4100c0317111000c040c00601801d010244050080f1101c0c1a80481d220b81504103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565548875 1250 565547625 565547639
    0x80f0a05090c150702040e07150302090f01030510180b01110102071109071421070801030228090e0c030d02010203010f1701020d060312030c03061d071b060204050a 72
    0x80c080c81100400001c1c05030784401e00410140c07200e42c0310a01240c0004201e0000503858601440b54551600002418003626001304001c030340058181e010105071042c000c8011a540f01c104805103403100340b80100c0c45840e4840400c40101c12039011555403880201066200c04c51a0820302e078004090300d801d42c3c000100c03c0060700340c1c494424010156100c140c5151560300d006600b0941003442e07464101050380d40d0416042c015072182840000c50b03001055260f204810704504103038460700c18030b00b151440d455540810907144c61000000c051045411002c0d03061442c10700814004c1c04c4620701840340114000307078181c641191000030381c06801501240f82c080c500500860341203544002c0d41c2400903140c201c41130705020303400c150110315540070414011f0196540c0520405540281f222100e00f400281014041328030943d40c2d03030141420030034200f18488550070403298064070b01d414030b007085c0ea41034011205114284406604400c0d01c1200d902403058540c041c0080c1d03002511598800c58481031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565550125 1250 565548875 565548881
    0x613182a030c0e1b0c0709050c1c1a04020d060503060915070503040816060c032d02030402010203040e090303060301050f13060b0a050a0e040b01051206071815080f0a 73
    0x3002d81200006041001185880c40c86142d01080414621007150700314200802198042280185554006101401200254881c06d50408070b0a003080345007000d000e00350191080c0410845000b82d6480e03001074a03030304c20a9054641c0440080c002c6699100480c1408010401c602400340240300d00000180500d1000540180720f2910940402580e528180d084520f030b80000d0080751582400d2100205055149804484003440307003801090300c01159400804690461095030b03030006043c103412141940d4885512054140c0c41d8015913207a643d800180d29510881e840201030046080400c0788001022016500030b2404500031302007030b2104c104925410405403036102003040e10304481c000042d003681c4100c01d496806820b01010654030f00c0065880384159020a1696044400300410042811a1907014002c11100c42c80310005a03c82150f0340e00d07000303008509020004070342070007610b8034414100c001e04e80038500c01c12698015200900f0400c4c00d68015124042c4d000104040d0702d1180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565551375 1250 565550125 565550129
    0xb0f0d0c080609040b06060f030a02090906190311060f040f1502010209220f0203090f01150e040f1a040303020c010b0102070506030a020d020f1306090602150613182a 73
    0x2804540d403521a40c454031400302006d001c1961100f020000a003842183c100510b203c0c0700019001078595100c0400e100449200414041c4942030303401c00c0313039001c281c0d419150090320703001b00b642a194000c0601080c0320b48912240740c049090041800200c0c1e046104012040c0c0da01281c1c000014044004160300340d004070040151702c00a0000d90f03405002d8461075640300440340c8480424070107030032401c034012a8400e43e0001e5185e0441c04120320480802d0150085020200b111090143d15051010a800d00080c2c4002d190030049010b030401d0009512520201044814203035101341024038000c0d0081d40726065060065080281c0f4040c7c960001c10100b04585020388490b10356510902448000c1d40400f1505104943c20301c12442d003240044068103043c0c082c0f4918a11841c10141e014180b241c4079405902158094415082180300210541d43c00040a0303800003501408145248041c10001302e8115041050341c071076a081c0070043d44400101c1e41120101550004040c00a8030224254 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565552625 1250 565551375 565551379
    0x40503070501030e0a0c03050c0117041a07170a1a0d05060a020f04170f010e030a090303260f040c170a02091003021c05010b090618100b0f0d0c0806 65
    0x224010030442d406900068204400d950907501e28401303507582c0c12540e0f03042e42c00a542640c0700d514880c0b56540c1205817040340e41d050100e0b060003494913540c0c0d8802484031034a0005a4003213074011419840c01122019111b80150000000301c1c0b8002c21408018010440002d1007075812058002c0e80e4102501d03246111600308001e400c140e9111001d001c040d6200e0100c0008070f540c01c00000603a83d000660701c04084042c0c0010302105903800004500f1340b02203100e500680c1d0000c1080c0a4170680260b200b004583d494146000740303484502d150590140032410a00c0d203d0040fa00704080e0240700100544500e102d0140c02d440951200740c1c0000ba8641003401714910341c0488940301c090f2610428031a40495040e00f213040e0651030b64041999075900c0040549040c950720322a2040003001e00070141c2ca400180e801e00d91a10384407000038004c0220181c04030100d0550004940c6200e8003800050203420380c001196515651030800700100e41c040038036074403000d14003082001d80d04e2050142070f000c0e03480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565553875 1250 565552625 565552633
    0xc0806190c0c1a060f060a0305060906040b010903030f18151e120b032e060e0705040b0a03110a2003130308030705090405041a0906070503150a03140109020a0605040503 74
    0x25000b08080040001c0c4c0015801a001e420745289661214010400580300303a4021400b81040c07018000309540c05052140720b00d051900615076660700800391001c494161811158410804500365404408075802409054200c003000c40d004100400c2e001480b24965242d00341c042c0c0388802c0404000d113485008000600b400c2c070400d07a15045e40c0281c600c100c001001d45014102991803000ca000241040120485520a600301040d5852140400402c17502d1481d8a403841d144000030700502c00c50140071001d00d0b021603410403c42c46580700040150b21000c600d5030f107492860b00600340c1402e018044481030a004028050303d4000310071342e4491451501c900d6a80f40c110b0741e0300025900b005140d0b60070800184200302c0d11703545600999002e60300480400d2111034003182e40c0e044038080205010842c2e408903082c40145944442200e90104e00094060f00c1050706000140090b003240d0310152000090001c0d4486412041d4416900d0910886241218581c1d821040d580750165124441d41500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565555125 1250 565553875 565553903
    0x7030c0228060f03021209160b03011406160f2102030921030c100906060501020606010e010e040b060d0203070f1b0b0703090f0606230a030f0c0806190c0c 68
    0x1018020080c481401c504000d030070b2034010700346d030f00c0e00742003c44d0b41c95183d90041014109190340d07113800b80d0240c414000111314560510809082207180040e88502034100001d00022000790301c403648008503449008034250300780b94113100e00d01c20700d1103441180c080c03481a29216854000030460f2009000600100800200d0b14032032040d07041c1c0c604400d140c0e07000820000105000038030480cc12105c0d1742000107040020750400c02c040380d0149c3c2025040d03502c40018000301e682c1050321580a07003000d281c800c1000666501250140c031402e640d103a00024045801e1485040b903070040c5115102c1681c0790004520450703011a840c11940c0070040d0399030100540500424685803003540c0c054000e080110710b200d0142d0780d1410105000344161095546c41d641401a1100c0b00500c00c01101055254031070403854800041c0f80d119a440000d0142c40001c0700030041084603002c000c01010440c06468240c0390810070102c2d408140132403c00b52502d44041d143e4014090b0b25000e10081d00f084242140e14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565556375 1250 565555125 565555127
    0xa030c0b030901150801060f05180f0901061203021c0c0b160201110a0302190509011b110d05071a12180f070803070b15030a0b0a0b0607030c022806 65
    0x9400940040307040c0d501c900d0010114131140c5004401806140000030304e543c40c010608a1001103504850b20500000b035036512600c840d131000342d411441d00840801143c03079940459004040c17960000440e040301e07504440a041d004a445210f840d003d4044e50081807519904854003031030220010074003124074020504180725518681c21960090000241d80d08414100d01c41e00d4121f0501100004d4000941000e0b08011010603101c1401034240182400c41140003e41a0583d501701c000c100583c070300c00c5000307118010100703032440c502c09800c6502a402c1030030070f0780e1101740d0f034040d180b038020540040700c0f03d001c119012112964a441c18840254696551086000ca1280001385040c40f03a140c61640c00e410510210000740107010056a5684003413074000e8100000520ba070390030350001c0d03215080c2501c1c007140c80201c45511003107204480e52003c05409c001e1680c1102d540e005140403411500305900801010502402202e0100e854040c6404d45032600603100f501111403a80c60360104112 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565557625 1250 565556375 565556377
    0x120417010b1810240f11060a0213030b0106030207020319020f040e1e03031005011d0f2407020901121109090f12130f03030912020d050f1005060a030c0b 67
    0x1821550f07005036490f0340348071420391002c01120140325014480c840109850304102020520186810a42e0b800441c503403106840b410b00910722442d1980009003980221001200d103005568003442500745540c494800400175000000300300d00038806c1c1d8200b40f000740203c101d40c114140e4001e081007452005041440080c0403e03000044a900c035000c0c880340e6044145201240d030604020086849180030b8000500c0080240d10140c10b0040e030445018440500124030b212174030782603130030b119424410800b20f4030f4014108600000080c1c4103022007480200c034001081c2c254000c0b41c00303000c3c0b6601c44132000001e10012038000c00c1034a441d241541c95051038111954840c40c4107054072000b010240d00e035410400c45101c0c510701000c000070292081003102c2c0400010b0540f614030144140d00310743d00038040360660b00a64040c4c0300c071510f522045640b1104448075040c0d114082d02c0300d41d16144d5181c0c1d540c490500244c2000d500f04400140d080c10a154030b0030031240c21107558607030303a440d00f10040e181e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565558875 1250 565557625 565557631
    0x9020714061b2b090210030905030f0c070e09070303080f01051309050304080318041b08191e050709300203010906021209070603110d02090111120417010b18 69
    0x16020078030b03034841065066000c0f2018581d104600216008009104020f949030410450405044ca0030148030302195000050b19080c04070044402e0b82c400308160150b1a1000503402411140180300800c01a09070100703c2c4411a40f181d11190345a031a5407000c840300c0030090007003035000010380d500c0c1003080e402c9401600306140a40103403481c1949a0100d1400c55100b4440510b00d0340d03150180d1542c03820140b140308014110306411fa26482d0f0709210007064060013805140c0b92012603a83d03408070504c15031142d039801813805200d183e0110310307030f14120140000b00d411001040846034002402040703d141007001d041500d8101600b140c0040c02c061a1140e039410070b980640d82c900303410380000c1c1c41d440200f02c0707881e00700302c00c80742c51401c4a181481d00c0d1168026008250030212002e001ca14400705640c4100d03051240561241046001252061001480014503100300101200302c0402003000f4019111300031045070703c0c14804800a0301369144400e03126040306500d40241da9420021443c0e0360 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565560125 1250 565558875 565558897
    0x4060b1201060b0702031212040f051204090537021e040e01181a0d08070506010b04140f0607020f0d15050a0e0607020a0308070c080409020714061b 65
    0x14020803409940c01c54629420141007888002441c4c815454100040052040300c41c80d51031400340b0042542041007009003000341301d545001c0b001020400d06026004000303901d03504a42c1c0322580c3d060060b02800d000d071507261440101c000d24040c2600400807400300c8482e0455071200d11f801312440c0c4002980b2002c1515100131500c0001804030300380340d00801c02458034010000c1217505008a07040c08041c0600d03070100c41071424540c00c850341c000c0d80c1030a02242048800d0311185245090412951246100081c154003503100040f40c800402c0025105640080c031182c00040c00345000d008039050101049544410706200740b400629149000001c4901c000e0412800307080543d0b0344020b061100c55040b030300700da00c580070045003001d88e204031000e2400c0d00b40201014241910302035183c0e0031322000134041000510004007140c0c0120380240d103466010641c40d5035260350b61440c400075040507004a030b25100c1406860001c1c1c0e40003c1c0d0901462203002020411b91205052440c030350700c4030010103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565561375 1250 565560125 565560139
    0x20304060c0e15031f090606080c030106080103120e06030703060611030a05070605070306030f06050103060f0621031107030b06030705012a110429040203100e1003050703080714011404060b 83
    0xa0170b04030607161040000d240003000070606a0901c0400f8090384e4000b86032160088080c4010858242e010805604403a04190100c52807240d05074121102d081e070941240e007254001050011040e070540c1f0200840701e066a070070402000740000b01f0b8a912595503c50700256003404160003040b0103510664004081c1c1c100000c58580e00d80d284007891104550071781700c2c10369440041080c041c642c050040c034021070001c100141410200c00ca0800a4806003191b6140d00340c0e0f5103030f42014040d1004038588e219920031256003c7d0b5915200c1d2904504403805402406548000505540030383e40f00ca1160b002c1501510003000804816020300c207401e0342c2503480c169464884910703915248180c1c2c036841e0b0483e90341224400d586130f130008140040f90245004500c100f0421000f4140c0c0404503054401e8464810101d8450f0384d20882019050781006c3c0c2607003d02030000003049194002400c40d03078401ca01407152005445000e5081b61180c00765501c118001c040010001a216400741d101c01200130800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565562625 1250 565561375 565561411
    0xd0203221703070c1401090b07170d09061a01052b091103190b1504020720100207030309031202011d0d110105010807030b06060c10020304060c0e1503 66
    0xa035805011004501c0050300300158010500007001c4605000e8242c02d120501c002e841540000d1643c81c21b403084444120012a183e0304012640220a1081c98441e02c45074032003100c854000d0051148803021501680b40102011251000034a0624000c00586030581443c0480f0004118818174806040c0306501031808003c035080203100f28115940036201c18010250340c2800d040c42c0c4012060b00e181c200b203082815800045007003131050f5100244c812a003032109000c8001c81e011b0301803a400101020040001072440c80082e034460810081c1c201c0d043c1e10030f200702040a98989142c0d002c00383c00100704030340900108480012a1081c00f109100005400b250b02d840c004100310301501c1d10800340c101d0a04d103c1220341c001d905408940170180200915454201443d030b43c1c2002d403000410840c46030001031880e54501c4140d4130025110001e6402d21440c890303c2100070740c02207504985452a040301a00120f110f0010301d403c6640c0a0480d008490f0170004442e001d0300000c000040031040e4a2003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565563875 1250 565562625 565562639
    0x405091207030305010617040c0b0a050c0a08180a0e060409020612090109020f010908300705030306090a0c0804020d05010e011107060609150b0c01020d091103010e0d020322 76
    0x7042294041d070750019082d4100740307004007041810b544c48582298018103000128498540380e40450302c3e801032540c1c0d5841209420380d0203004403158243c1c50b003c2c5100400c02e214041c40140f50842c0d04d80849081d4a4604c02000b00d4034040c1d020340601d48420800140c440c5c10141e0040c00031500040030103050860400444165075421160886c4d6651608030360011030600030310300c000d4280e007400e000c1d04190400c441140c3c3d44160207190240e050ba00c2044070100c454044401201810440c03401d95582d086040c99030f07899206958450007803005800092100303865101d0681806502c2da103191a075100c075000c105411907402c03425140e035541c070019800c010809116072007141c0f03024003196444082c242802c81c110b458075800105042e080464199a5480c5000250292202003081540780d1503001c100c40e009000340954151031078a44081c0c0014049410385078010b83d241107000340708003940780c855991240c0d080c00460016074018407480252152010704550b144c0d060000f40c40d6200e0340d540e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565565125 1250 565563875 565563877
    0x1030b0c040305030403120909020f0705152e080304081f110d1d160303020c06181909110306030c0f060906090402130e04030809070303020a0b0a0f0c02030c21040504050912 76
    0x100001d040741000334102e040090a02042542415411501c5020302d8550140700002590501c21407006035024031441d199814440010040c01c040400c032500c6a07290140682d60f090a200c16514810118018a602119601801ca00203c51300340c0700d818005000000350180c00c9280c04841d01f450181c441e0a001c480410211905c0064554540ea18034a907060190801d40742c0c51610780560420082c41c910b00a01840c01d01c035404041c4c600d10704d5160308a0100c410703a52160402800310b400c110f9103409458556000d14003440342142074071456060181000001c0c41e94400560b0000c200703005a00a07450500041d114801c0b020300b0141c85c00504501a1150310200e4000c03010104400090100b40346d40485144d500c03804040040c0304140c00d54901030b6460025100041484085a00040d0b205002c0e0b00400280110210107200540030000003a44036007200c001501e20780701d801410a982d100e070100311044c43c0100c4c03c03060701d401d0504007030201410000f41003007a141b144054091248030184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565566375 1250 565565125 565565137
    0x1b0d020601180506100503070c050d081b070c0b032a13120503030615090d1a221b0b0301140f0114030a2c030301030b0c04030503040312090902 63
    0x1a01900c4507604008a8003416811404102002c0b4078010802c400c58440004c91480944e540c2400b076207135580d00100f1a085035140c4001800f600608881014080d0440308207402003040a800109445c210404212280108803002d0803042022204202d0b040e503050045400405c1e0035a0291005400c002001000c9103c6000b4842030030000740e000d24005281b0369000107001d51402852600381503480709585c0340000340410b8440d0004188052011051404440d120407002e09140b40b80405818800b030702009146400d0074030040d10000034072485091450011200000740380f0300d2a1007407610340304141d00c1c031103c600e41030f4030104001284855086000e035000340080c1d40c00c030100398205c00070b020000d1a0304000c1e906201d05800c0c0c0740300242c80ca40680b07501441c40300002132500403d00c803200c0c0800810440101c070900400c49102290000320095051728003503c0800700c40d85407001825a584100d2001614a4105120a10000d42d080ca2150b880c602d8614010855035140d00f10041264402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565567625 1250 565566375 565566377
    0xd021011070303090504060f03150c0302071401050f0901061208090607140303090d020d050f070c0504180c080f030703051b06240d0b060d0503040b0d020c070b1c021b0d 74
    0x84c1c01308008170301d400e0041c0000342c0400c01a07550302c0e503d160781e41611a150341002241e695220400b5844c03440c0300f503041e07440c0c50f074101c030300900080404c01e0070314000e040545140440403c1c00c000680c10402c140207074011140103010a0341ca6624686442c40a600703d01040b590208c02006a03c1c0403c00c21401d5134038a0281c00e01440e82c0b424500ca026182151002c20682590000300e44070f40000d81100a840340d060041d14440da9a00c100d107402054501c4a4110a511a250a15020020a004d40c000d80c1040c0310fa001d6602c1603444210f19035503403400c0001c42c1c03a5135008024560000e84503070060404800394500364280300c80c110250038101441240d2010041440520000e00201c0f1803142601c02641610f04980c4580e1a4546c0094194018141d038020000381d0184010032030100200c13801045a08215500c3d60b84004180000c2d42c1b00c60719046442c8100603001c00d6002580003150314000c4d1404000e02056400303281803001e500040b003180d40c0120034461a103220541804501c41203205 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565568875 1250 565567625 565567637
    0x604060c06020d0f1407020706020c040915090503040f080f0631120305010608160e06091827030304030815091015020106050d150b0d1118060d021011070303 69
    0x440c0030000400480103060761b08552007080100901500403c0704054100c0075500840c40000b141400d11080e24038006d02a001032425000c48144000400a04181c4001c4044200c0c210754680c41c6a58079052703901d000d11030342c0105021891034141c825003002d07259100030703684500c041d040080300c100c1864010184c03100c454850b503c0341807aa041c4100d0340500118203100035a814101099410f6000b08503018040c05402000390195030748000c00e541502d08014118400d8080d00802c0c0308100b00f069401c4c50364850b940d00c40d40904101c00c01505c40454240e070066066903600c0d1000c41c0c0d0050058103903d03842d100300e4658021512054001031041c6811009158080d00d000c810040a0030310030030b60300c00c6924000d000d02039655040d040c0c00c1d00c60f0300040218140040300c40080002c150810425a00c00380d02010441002090a004440c1000c200c2c5c0401e0030080c0404507070f80c080000c0304c0040c0e1200801311100b0040c60403d00760201c01095180407441120741d02c80091411003950015004240 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565570125 1250 565568875 565568891
    0x180902030a0b0f0c030403020c01080c0c03040b13060801081b04110703050307080f070c0219050424050306012d05060a09050901050f0d2607080a1d0604060c06020d0f 73
    0x420102c640c02020030034500c5d1942c42d06460094481c00742c070f48050304022070f4001091344805120f081d1012340c401e85c3c0c1503d6030349940b400404029171240a5890000000720000201c1c280200e6a05040f501d1a401038004d8400c94403080628003150700545520070365035032004c1400d80e4680042d040c0c80c2e100c4c1e01e51681d13a09010307601801c688802007000345040040810844143d0b40310000707400d03260307058400702c1844003800180c100c03030145074001e00c0c1c105290000a0180c18000812070384a07083c40d00810300d40c03588079024180c65400901403010500c044c2d1280403140d141514902600840b0180c07000c10454031080040e0456125025150024411701030511a0703191007440c250051608030b450142821011300803401c0da50701c940300545811050480617a02101d41b4014082c441902190659140c4039460140120740ac4159500000b03101c07603200d0b403000380100714001c03c4c03c84000c005038242403400c80d044a40030703608542114020303000c0c040740c10340312007600070300c0c0c1300250024011400407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565571375 1250 565570125 565570141
    0x4050909150a090308060307080c01050901020c04151701180221071e05091302040b030f0f01051503010c090506160b0a09050609030a0509010f110616020d020115180902030a0b 77
    0x45c2000d44a03a210f604961000c000080703000170500c040c107a083c02c040703443d510761100603400c2c402000d1420f07401a043c401664001c407000b1190500b035416a00c050104805e0600e24a82280c000c20640f0403030650304183c180c050300c0c1040003d104002d000346402000750814201074140201ca52000d0064900a0b1004540c0a034440524001d0807043d100003c461902c403000090b007420501010f8003440d5984000c03030458a06004414510400000b281c40300c1090b460414001c0c030040702c0b4510071031407a030559000f61506028010794210166a40c5131558180f06c20410940c5c0407400c28074600041040c0403000400021103a03100c2e5030a0380c400030f800b80b220f08185040035401002803649030001c00c0301c18219030304042a035118a6082c40c000740c2c0c4840305002a2190703125020001303214031a9004000d0242c941c407404240a58a079400d5a00c00b01008009900765400d540d1429038040c41d000d000d12078a1180001c2c407207401180301d00442e1030303001034010034204a96550705440144015003084410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565572625 1250 565571375 565571387
    0x22206030c05180613031a04061a0f1201020c100e12040f090902040b15090f0105040b0a0813120c110108060612090109051b0a051504050909150a0903 66
    0x5034195042007407403c5a6140000c1c0303059040b0701c841d407107540301146514050300102030b4600510b030b02a00c00141400d00c076801404444040720200c440394104406041c40c00840341c0da9003e4100094001d18803035a15804000d0418004c6050401d02e43d824080c0c407444a50802c1601e50358a0380000018290006c40344841c04c1070a401c40c1d440750340004000400c804544846608100c5048010008a2144520008000d0015442c3c603c0d4049014908010800040130041054080440301740c6511208100103640f54082c621440c0c1081b4400d012441c0898042c2441d13660141ca0320090034032001182c0d480c0014800001511800190407903586410440c6803071501e4201403090030240050316000000075098400c0001e801485000800440c0071907c1c2504030620342ea40c040c040c2c840e82e00701014031a000512888005100b00006200000c103810260203c440d07505a420300300386803e08040c1030003503c41001d00046000d1041d46620218121404180c50003100c0310318000c1801c1110303013002028 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565573875 1250 565572625 565572641
    0xa0e0d210c0806060c0a061a090a0606020c0d030c0203070306050106081b042309010801020915070506010923073c12090f0c030b0c120705070602220603 67
    0xc80740740803000480d807900815025409a4110703100d80d5942c0301c94820508290900d90018001c60604600d00195190348425990310136040e2602c400590790f100d0240c0503144076206200140e00081d02e980c0c00c0c0d082c01203035522814040c0c01c1c0035a00640c56408a494020298011360f601540e50006125490340074040c250011040051114080300326040701405208512800340c0352103690414141010350340c0541c1c50140b0700100918590740c2e45251040c040d40c40070421511400c50041d0755660707084a00d043e900e00c030b42c10070024081070b820504800d00401590140250300381410301c00c00300a10501005504c100308903500c9070845051401006c0c2c480700c01030170288030030301e0341596980c001c6000840b100b005480d5260080e0302c103030f501c4659401031880240290101c6190b01444007071060f0100d50000300d07840340070345800d25901c101c0302501078010f40500d180840740d80004540c2e0244500b010300b4030a401020018548003090004003111004070703002e100c1450813031030b081068039014422844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565575125 1250 565573875 565573937
    0x1201030828090e071b0c030b0c04031709010e120a021503070c1209090207030c0c121a04020f2d031209120c0621060406150302030a0e0d 60
    0x9129144498064a402c6890042c92071126049000030900d601c55840c010b16140030f40b061551200042c00c0c003c050508501007550000b086c82d02082410002e20b04035000c50f900311070b024041600d624001c98603680b0a01c480d40c100030703003d0420b509c0c913a5030102c000c240700b840303600800c000d40d5144140306000c8030b0b51290b0002030300c060042080160f0042d4141842d0340e07001003040046400a442511882a6038204064292010a170b4500700340d0041001902079024041e1604c00030b5440d1041e014079264600d00a01c0704102c2120b9080030590340181c4c94000c0c0c40205030030788007000b0001140c455100d041c50800d40a04201000342c80e02c03e004801e0214100507805440b1080b41035880041c60702c0303400f4a83d4002c42c100c0c010944020014814041c0c440002040c00d40c0d1070140a007160080040010000d854003151004201c2c81d00e801c0c4104000c403580c152401c4000c145041e000d80094000030103e0414640340d00014291038406c0c011600030310440d4580c8080300e248240014590034040184407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565576375 1250 565575125 565575187
    0x180e07060804030305040228140604030305070f0f021903060e0f0c010e130504031e050c0c09040303090507061d010314041b08030c06010512150c030a0212010308 71
    0x803184640c40800c840c2d0043e0141808605900c6520201d00d031048101e10540703a412009a07101c0440c0d80030010082101c483d42e0030180250218001c2000b1445544001400b255042001c000054802e00300500304da406418140036048858001c20b16030846150718035107442689200b841002842d02ca08007030003015100421907044c00d01c50956444845051060500400b11000c0b1020b07030711640d1801c10502183c0d07080c03009051914020307180c0000c42d42901250b510a4083c214045c1c4100305558024810b04000c2c00840c0384002444181d030b5020b00194101a1625007000200b08100300314001807005a0300c480b0040e0842100100104000a81904060515280c8000c0b0080988041e40103508840f000f070030f20404044140c84050310b03500c44503040c0000300345800300d00c2c0c2c042145c904a80c0f0a541c071000c03500b4401b002646a24009009261f00c0600d03074003240e1125100c00c090340d4800940e0308014541a0000c0c1d00d06d0395140c099000712442400020000311218961b00704c150800042070b002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565577625 1250 565576375 565576379
    0x12181201291203120105180717191d06100e0411040209100e0117040b1315060b03040c0f05060d020f1b0609070b09130e0c0a180e07 58
    0x320364503509051494031080781042095036680c424441181015042c42160f035103103101c504a0603025424440c1621920402100202003000102e040d849046030f559410100c2e0801040e2618490016003404601d013641d0b0222a0b49100610400e056660180e80c6003401a0034410750314501032005112a0046040f8281005141c44016000c0e42080c2d10018804094403c00d01140007400b0380105a94030400442440726219003200403000740790402e0345e13054548181e0f40440e0442580640f4002c010080c54800240220117a070f10100b180c0340f1504000d03c14035850003810058504940001092120000030304c010001b0b82c0100f4001020010800340d0f085140c0b074000b61241c01001003a0882070780016041103820040340c11a03030480d20032200149441c1e1140c02a41c0d403083c04580344401403043c24004140e100020064414032030000380035220806202031020040c008605c007048061181c00700c180a9035450b017000402800b100c905182034107405800803425921541940d540c01d070000f81c0300b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565578875 1250 565577625 565577651
    0x220b0f0a05120c0418060506031204030b1008060c12011502060105100e030304091d010b09010605070312020a02030a02070e0c1b10050c190306080c1212181201 70
    0xd280c1110000c88102c8400b0702d08141c0b940c1400c0c2c0300440f440c0c0c01440d0400302d8001407a082065461503028180402640ea035030014580d43d03241001d83c8075075400e41888100001110100071503400082102c80d40d1a00f6030700c820340c6250400a0707408501851000c1001c00250708a040e2040c018000c42900701610000680003030746038203042c007409016880c1a00038529031805108503401140002d01202e5540d03a550600800400e046845046d450704908088074400740d05004801c80400000e03c14801e0380d2900c0010b96850744240b02c21803d00c000700350110080040f51001d420001072907005582c1d50103004c07400a051000c590040808401000e09010b04281644180c0d0701c003402c207140a0a000390b0001905250003000b01c0d600030b00034103103000c000c1103145d9440a0a03107040003000c0740c280010f40714419801c1c1c0b059405606015402581c1c44015454070030305090f683c040080c1912089000c2115a9440703520441d41c150032a4071422100703106080060703000c0c951101d401c00030081c0410840e4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565580125 1250 565578875 565578889
    0x5010e0303072d0f0f030914210a0c0f0614070c06050f0408030a030906050a18060c0314180d030e0d1101020405040c09031505011a0c070302220b0f 65
    0x40c111540900b100314011070242c030402c085681e80c1d0030201c2030613007450b00d1400c0b40d0b041100490440000329426000605c10030024215030321000000d00381c0307403100c00700b09083c0c00034081c08007143c00f03503c00c0e0b0030110045030070503803260003901540c800300404a0514001900c40700e1110201030962108100c0d0342c020803401807880d41503821a282c0140c0c0c0342d1414440510764001c0c0c3d04a1041800f0014110600740d405d648203010141c850f01043c440790b0f076000c021008940c0314114610720a04200d103820b0000344d02c0da10164141e030b194180025284618200131100d21000c1b01d803000c203009541507400d0200404c100d000c02c03006284c42d0900040032044801a10b4040342da0424040c08011140da2b00290020740641c0c2c0641000343c07080081c1a16000014800c0740c09102c00d031807540c80c03035542d104036820602079941650340d400f544030342c0442d9100c021110b13540b00a1800586002d000400310040c2e172580070713500071010360350390340120b0b461070741c1c0607a04882d50010158400c1c20003414815240d10752032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565581375 1250 565580125 565580153
    0x3020f03060403090e0c070209011d010f06050d021e0f040e090a020d0803100b0a02100f05010609050108100f090506010305070e092707090e0d090b030105041109030d020705010e030307 81
    0x141000d00368852055860300c50151447c001c0d480b001c07040000c10454800050b141898107140e0364841c0d42c0c0d98071003640c03051003000c3c014000082ea04000d20b00380f0900b90b0b0000d11200c0035050854041c45407c9954000c80d8201060380c42d60800001401c0024101c1810a40c0d0400355403030240803446440c2c0e00107000c00e406202d0003400d540000c4002120508100c0c2d020300200891000075580741040b000007519060b040c0365509182d8500b480079082140d003845054107a501640f40c007400c00e0304140042d9900b0200824641550000d6100819024503a05205004040f11880851b203410040d00250a07a44010000e80401040d07180e05075036907680f4454030340c010030760f5590b00d010b001362500750301ea100d655901d02060a118010002070300194030342c0071180980410f070503228005010030307084a0f80101441003840c60ba6040c07006100c0da2a055200c038007003010198900e440d081001011a0405214105035000750f00501d000304010750304120300c03040c42c103400c07406507140450554400071012608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565582625 1250 565581375 565581389
    0x72105100912080f01031e05060403020d020d1701170f0307080a17070903020153090a11040e0105100f080d0c06020a03060803130609090e100506010207051903020f0306040309 77
    0x28000d6411f40301c4100f509180c01d9401c00160798591509060203940c0b03540802e518001407041044080d40b903071099901200034200400c2d030a0042e4a8a1711000440002d203050501c103000da02e05d4041c0810080004281d2075110b03100d4a5180c8296150142c13808060746103082c00d94807048104510180c0c07100401050301d509003082c3d0180d180921901e6540c0f00d448180802028071140c41103e02188891001c24556031001146040c03040c4044038a105281a0380c4100f890b8041c0c1d04201c00075604003030101e41d0b408060000512400c0c034500460a603402aa4030640c201da080d0350502141e0100740f21034010389503810083c03402c078818040c010b0020850300f0300a40b038207034042401c0310143c1c442c0d0800b800034100d401c101c0361203411014584107400403600c12800450200d4400052941b541c0c004c100007d0001d8000e40301c03941c943c00e001d501034040148114114051400b0105155907240851f5403030010501381c2c60b80d0507007148180244103803042c0d030759031180d44481c08202c002544108190192002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565583875 1250 565582625 565582643
    0x6061b0204090813080303011802040501090b0c15070c0201120e190204111210080105040305091e100504030b0a0204030b0415021c0209180108072105100912080f0103 73
    0x1600f010f6003140110b4030100c80416201c00c00084000002010314141c4403000c0344003600321111800201203100b103115482c08508841010007860940e0400303040301c1c42e0a00c0c1a6260034245401640a441040f2901c50205034100029400c0d0350344800d07030201c02c0c2d0200000700002c600c920649960b5068400000202800004c246011502e6640045812a0101c41c1d4991681004810001300d01c2049416011084407004005a01801401120301071034040d16903610b8107002105104039035404860b90290f424210314094019212041084030070f0b03555a0310f00c0d84407030a626207007004140c05404d42c0c00b40380c0103100038004100c640201316000780e030106010164201050490010340161000c0e2140810304940451018400360000c3c2010352040710012002d246035005c041e1100c10a005800c0140d00000d000d00110b00d40049112030f4229400320054140c3e180e64400d450800300110b0040703031b40d85950b102c100b0800111900d1f4030003511418282000d180c59216000d0840313052002804480c0c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565585125 1250 565583875 565583891
    0x7060e0d020105090409030c02120a0209011a070c0605131a0307050a0c0605040606030b09010c0f031a13090b011a0f0307030b0409060506031c0203070b10050a170106061b0204 77
    0x80100c04aa10010001c5d00070702c072508071410080c00910a0600990081c03e01ca40c40c85101030010a802c0e4903a82d00400504140c1d00b800045507101c04800e10082050b102001000042401744c400c0c1c1005104640e501684c66845903001948461507038050341510490044c007071107052459050381d51080d81c80c500300343c40d041502e200301d07a225881c2002030a8140f4010921003071110603044081564080c070310111064a421031100e003203c441c0008040041c95404035812258840d420082c11688500e104007a810288800a458030101006804440c1d036035456001c10800705051040c014101c0300c90f02c91091103030283c081c080d07108880c004a40241c00000041c9014000c0d44004180d940180c8101300031081762034060020081901d025209128400015030b100e21414040074007038820760301443c01c1540036076401a1019026108850b9045200c0300490240c0325426880c0080180201c480c0b1031000740100282100c00325000641041520001c0300400b0709101c100009495041e940095030349 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565586375 1250 565585125 565585127
    0x807050d03020111031003170432060a0201090c0911190516080901020616050d0203100909030f08010f0e0403050a020a0503040f050a050604050a030f140d0906020f07060e0d0201 78
    0x402d400d6545620782c0000310600c11100598486c80c41564450701007210403100c0c03e460851103000741c0c42250300d0301e603640d04c590001009030825224801d00c1c4031b0100b80d05030700d910000385907500101503020050f03558002c00b100340110400620010060300c90200314407e040c4001210794032583c40d14108043c5408003040c40700d84a031045807015945480441c0b210903c915000d445c9501c8034102034018440e9101040c504210022204420340e11070b180c66180103600b0804002030b4000a010064107001d11000140740301c498051440118401c2da9452684280c40c00003078560141a0400b20000c1c458610500060807118251900280c060400036182e55100300300320714003580300200401c0c80c0000b080c002540314a0060360700686008880f11480c15031608180010b900603440b41d141e010000d14801c001041d010281c2c0401c03c3e0041200ba40b5402c41c01071030b40d1624040c9002100000c1c8144003c10103194140140d94816850102030260189410f000504401c40302050310b21642519003048216 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565587625 1250 565586375 565586381
    0x30c060c0d0914033301141306050a18090812011809021c050c0a0e100b160b060319050604020909060405070312091e080105060a0810110c030d1d070807050d030201 72
    0xc170410030302400403580c5810165540c801070249242c0540440d03289920b900015008031416101c02401032070b0460302e40100340c00440b10600a5011007640c03110034402040600b40201501c00c2d490307c03503195552409100b55960883c0c2c40c40151000d1500d010702e40141c1e00d1451303016a00c00200d00c0d6000d48821400c1160500f01360780441a0310a100351030009500c0c0396003000d1481040107000d4132007010307600c22a211701c900c80d649500c1c001a02d14885080001c0e1080501900004040c04580390036400c040d100c498442014000d403603640c013003804c000031881e01c2e40800c1d0f0300c000700314083c018509007541c41c5540c804843c000145009440381d050700b2503901c20221200100303000000c6c2074108600840302051a11280105403440d400d110002d425820500d248401301d8010701c3c020300c2e400c01040d0310140107208802c500040c020042008171b54400081003d0306101c9042000020006a04512a01c0c06903c01d1000d50054002d00e00c1000b070034802203031800440700207841e41c084c48140e80c40d0813401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565588875 1250 565587625 565587703
    0x1302240d05041707060b0a150c060207050c03071202030c0a231f0c050d05130303050f04120302150114060403060e0115061701050a14040b030c060c0d091403 69
    0x190f02c4003040060901c0102d4221140b145000d49501d80100e8443c1d201c03410000304c810710303074002c65500007811000448a500400c20507014205a401500070f52002a0805c84143e100c1555400c00c08040400d40c6002d2021210000b012030b080705c2e81503e00603540c454425144403400441c80303801388040d150345a901c4041100c5440103800d000c6c94106c544d0117014400040d40c02d0300d040c8a02c001c4052031501400480b9803103c0203442002c10585181d400b1070342944850211000d0303c00c10b01c000a801080382418246d103500c01e4004c1d20344419401ca00088804050348901062808018a0b20564480707000301c42c01c1e41e8000d44c0119000f5011003025002d440420700c15030080954200003d086540100006503000b504d4220050b281d0740c40003049800c1a80e400390021080d2a00701035012407601e0b901c01000315001a0942e04052207036000500160046e501d0b19056070012001051980d174030448040c058540040d107140420804808a0f40c4d486841803414601010844208080c95840b04001c007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565590125 1250 565588875 565588913
    0x140301060f030b0f042d020306031e19030f110c220914060115050c07050906031501030b0a060618060c170d0f05131212020c0102031302240d0504 64
    0x100c118003070307611b00c0710107824003000b10851514003009080c6c0c48840d000b100d0041d00011300404048a0710715601c1501c20410200d00702510618403582d4101d1103055444c00d4a50007502c2c0c401000203403500161555071440050207458100030344540ca287d447c0c2c0c3e00346112214020f9404004001000294000c0003145e50290141c00c043e20000da003070307000080260603105041d6045101a40c0c44c1070903a12801846402c0c0441d81040d20706000504042450383d0b44402d00408807041e000c1c2c0350005020704ac900b0381098844001c144204030100c01307203005240060080d4078200f5141502a10181c1000d030f0340340030740720403c8001807440d81030001c2e03001850b85844101104079952015500301c20700404180060b84103176404c0200062138072201c2d140914070b0325080040ba800303101010b88200d50040b880020504041e609004151501c5e2092025512802548c40000c0d00c010769401000790002d01d102e41300021072440c6540c079048a03000d4050702e01d05007002c403000c43c07591100d15042214029180c0390350 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565591375 1250 565590125 565590131
    0x60518041a12060705031f0b1902060702120f033112091d250c0215030106021903050405090c07200a050613090606020303010303140301060f030b0f04 66
    0x15108032142400d9400d88a000c59034003801500100e210b5440f0315013100c00d00b000c50414400135480000880c140d11a030345074410101e002d1900c99581c0c8555400c5000c03034942c2c031400b003010100c101e41c04101007a000211030009044c0e0784000030368480240b19441842e26a09008004201841d40c0500c100e013074642c2d03503501d001141c100507a48041c01c11045000b624184401500c21604500070104101074804034040b036800c080d540902c04003203103070250403c040e0b0040610742d5003114400600700000d60b0f1480c0d40e9401c1d2081180100301d40440151302c604185401000100301d01900088c1c1c0c3c1c12400d22011400409032250b0400b601d9500580d44001c2c1c108603c00100500c0b00b141c5801465000c0c400c54804a4101d070004800100020400b05036400c480500703010300040c07402c100a85034199131428034210403a203591804042d15030f25804400507034404401030040541003034048000e25543c00c00c49096615144d8000c103034081900ea060141555078042c0e582e1510350200e04d15014401400034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565592625 1250 565591375 565591391
    0xe0c0d080c150c03090111071a06030a020a080d0816080610171e1f090f060f060e0114070203150c12072001060305030307080c070b01090b13050405060106051804 71
    0x2184190310895489400c0d510b0040c0c500c0e1001f980d0380c1600c050f00c1e0403103940c603444020981080c04019014001e1589440b8642058005a1321501e5640c003401401c4098032035503015000141c01c06d00041c0c403480c0c075020b40078a0f142c3d0781648000443c0d440302044071030707400e01c2c4a081703c2a25500c0c00c00386245002440213040050040305008036002408035000d11011702d40c0c811040e200c41401038101c02e01080312202040007442c025410a4803861445280010190b40d10500b680c0c1c05803003644aa00860301003100c446a80d0380202e054203081010442c003519044295001035110715851800708026121840461801c2d440310041c0d074840c0e4200c1030303060000c1c24140c0d40078001045474100682414010024030074541810301513101100d50010055003540ca6028060301c0350000101401c009040610003480072458200741a40240340042d40043c0d100d0b0340a06000300f03c150510040101801c020601c0002000005e04030304544240c540a40c680944a51803100559114043b662290403c80a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565593875 1250 565592625 565592641
    0xa030b070914010e010816021906060e0c031302040504030e03101b0f0212030711030d05060f060304020108040215040504060315050a0c0f0e012a060e0c0d080c15 71
    0x11120598034002c0c001400020720b1401100c50842c118a142e001640324030106014041c48020001c030701c0020300650b4404941c40600d1240c05181c040c1c180e450315240c00082018401c40c0c00e189411620340d45590b031039894008a220004a945c2d000203004990303850029040c540309605990302114000c0903101110b90940384040640b8881301480703843c001c88942d18240074040c03404806500d01c1078000e003110703044091001032540c20040074541440040721041d16840c109100401c0b80403402c0b000020142000000c4c40880b4140d046d00e207020b04e0041060001503a00035010951090303040f071302c0060903504c2c1134002103107000310343c401d40d04141891804403c01810607010007000492200400083da90440c4400a03501442c02c040003254245e460346400741c0c0b00301c6099055140c181000b00e000a801895541d400c2e907500484280480b00d00744000400680d030040b021a1041040180540c924100024003401d14201d40184400400102400c5080d000e0040c0804813070300001500b040e10305011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565595125 1250 565593875 565593887
    0x30213020306210c09060a09110d06080d0530090a050c0901030209160302070b07050c0c0a0305101d0109080a18080d1d030a061b031e0b0a030b07 64
    0x41040c4100c40300e440f16102907009a51000219200800070400540c0c000207120200c2ca000e81110f0300a0103c02d00418400d100b401400400400503800e00d41da031810030104401c44485c3d03081780d101900301088140340300b0313400710594014180f00740d140c40300c0400e0030303203024420f218690a0b11404910101003200d40b58010400325002070194040e40e0780c251441007001284202404001d600c0102d6002281010390304401b007284111041c21300510300101a2074045042d60201d80c00000078500083d030104522003440105d0b1010000e40c0e51001d95030440ea1040c5e26101009205103c19079035500541c0c21481094110620021400007003140800c241441c141603400884280c0204244810b407141c40f0081498960844420034098044c0000b1200205e0b60254450411030800d007015103003000540c5c0030300014006a110700c1c1c000400050302500340b0300d400510f2241900741460045031025044080100c200384480d20500080c404100b88002040802940c05c058071039160f010401030f2940d0000b0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565596375 1250 565595125 565595131
    0xc0d0803090c011b06020a050f1314190b092b0b0c0c060f15100c060f0b06041806120b010906090b06071103013209010b21070302130203 60
    0x20181c48942c034401c0300641e640340591203036905801050000401141295006e42521802850701c2840c01d800034072011059007054802903210f03800404100001e030325904514030202819102e54211030110903a44519031040c0c4a2112512000160340c0c000f83c4e0f55981540548214404102511601004c0e243c1e0000ca02e19044800315129400b184000010744196604000040010030a503a902150007000c0d0308080c044805500c0c00500041055540c1c03020310a1201e0246d546c500b81e00780a0030800103031807100404048a51400203580300c20b171515012076040c1c80d4003a00c140c944806858445004103625801551711050000700c60f010440001a558102c42d40310030140012611150850206d070201c030200b580c000030405c0301c0400904102103600448400400020754480102907801440068541c0c1d680304104030444000c0c1890b16158854020001c0d5008000e044030b044c000c03403102107141209a1796110503080c040103800c0d00300b15503005503078080c0040282c607007100490f6010f50400d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565597625 1250 565596375 565596391
    0x8010e011d0312040809060403023c0d1424040309090203011412150c0c0106360b030d0306030204180c18140f0402090c040302030d050c0c0d0803 64
    0x1841c2804103011002090b10320f4103403441c0006840703441d00d540f04441c40d07000103603071508480300307004c0040940d40d007a484000b2801ca500c0210083c10108414510381c00416078001d00c1100c2c0100060f04903191036072031440340d560141d0500c48034420420360610304100107002011160804c0002c4c010105245c03c070500a034480d0300c07280005130b02c0300d817150180e01090060040e042e6403a20152000c1c9031100517002030050303003001d13586156121802d0082c1584122410032040c1000142052226070034810307140103054401800c2106039034600c20300d116000140151000324000b0562020003421a40035149401005080b0390142c0903a1a01402514061009130f104526003c2c2e1107002c0c001c43c1e00d400c504583e00920009025051500d0413108030351410000c000140e8840300084286036080039603003c0c0d14003440c030800310318207803040202d5550001e00b40b03c4508824001000161000994540e40d88071a017020383d100d0b070100700200d2800295450455010403401d203035a0034082c4c46800ac600036220 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565598875 1250 565597625 565597661
    0x3120c0507300f02120d020d03020901120c2a110607021206070807080906060a170a050a060e010c050a02060c090d0f0b160518040203040c03081c1406130506010908010e01 75
    0x110b1154940c80e1ba2921940c1005604948941c0d06094071a030300402e05640141171407250300c080440b14100300c9981030500c0c8041030012403074440e08500442501000700107130792442da440001d43e60b0a1004000718407002e006a1b00892101c0442d07480802d0710030707445007460440f40d00e8501980020204c40055850340702007410759020444d41900815507034424007000d0a0803017507a01d840072100140104958550240c090f070040800024000d010403990715000c0c0c0000b02c4d10040070600c05007190603103921401401410401199202c0d004690359600c089613082c1c240d02c1e25900300100740390121300b110041030108541d009100700141c818445011b0030705160045900403090000f62401c0c41b8000c880030058880d0681549540b500740c00030340e4050705c1102c100c200d01c0d56a80c1d500066811411030001030f8001c0c020511784501c000d204410080c040d481484045040400208001128002d40c0c07480040d26640010010390003541404000e04450000b003100a101184c16402412560710611040c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565600125 1250 565598875 565598899
    0x506070804030f05090f090a0e0f0c030f0a0210030b030109060e01050f0105041814010b0619141809060307080d0f020f0a03170a060302150403120c0507300f02 70
    0x8800c1d400c0c1c0e003106030702408061074801c4002c10047c406800500f80c204864569900c8401d002e030a1107500f081c455000e00429002031040109070030b02c003001c00c43d420541d015400040250740d801100d0303044103105007000070b0310840780b002090241072000d802520752424030107505041c1c5015404648103454524841400e85d80324400c00091f01c0c1804005d06018110800b017001103444119407038a00303c58003000061051200010500940089884c000f03c420380606440900d41c215880f034009c03442411410b03262a415000390300155410010090140e031000740020400d4a00304401d8000d031069200b201c0c0d52000660000300b44161803001c00c3c005000b1000a48042e01002070903404141c0c2c540c440c0c15980c0c07000900114883c00c0201700d01400d03038a9850020142c0c4a0071404400b2000410500c2c1c1d0784d905505044449d26241c0c1003030f50401c090703da2402e000c5440820311105907807003e141e0102c000c807030b460f65840c000f20fa1000c0c0042c0700902c010b140c0411030100a03815200e4429612012800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565601375 1250 565600125 565600127
    0x20f0306060112110d060e07090902040b2b0501090203090c090603102a0302070308072f070f1206061721070f0615091a09130506070804030f 62
    0x300d01a100580410a11003500b980c080150f0010034a0b00c8145440c5801c0000e0321065905036a803030b505c0300c044070380000140310340194803000001c081d02c0051800d52816280c101748840304e200702c2e18140324080e081c0b80105a0441e1400d02c9011580801c0401c3c0000c0d6180c0003007000070342c426503403800b440c4140c4a9030400c41c107054400b2441400020b01402e507018640342c5040160401c016001c2c207006e10b03c1e21480d04d0482955128a44508682c0c0058032140340c0c3ca0043d0001d030020f0180e0090000500111025680790540d6440840e00c80030700080004a0300c480910340110383d04660365550809001180c0c0f1200500c3d244c1209004090511501b95508070317175804141c8801c61909103401c0300d20740e01000c0d0120492010003080072203a0a00e84000b035102c0c3c4501d030040120490710181c9844900c00740185008000c03010b403c0600b020848080202c804446c0010703001241402079110344001002c0c0300780040c83d07020007601b110641e916403a00d86030082410008032021000f0030001040400b0706 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565602625 1250 565601375 565601383
    0x40e0c0108010b030c0f03010e04050705011b1b09020403060f0b090f0103120909020705030c160b0703080a090804062307080d0b0d20120d02060f130506040f020f03 72
    0x506041c0c481540340d90900c420f0040961005001c024066402c011a40c02410018000c41c020040210350007024149481e180d420211654000390400c14040303140314019a00408640e0070a5004100c400c1d8002181102c0c0072048550348411000d81c4007040010074003c481d004410070b51480d100400008148000700b041070030040d0b9044045804480048c0700044082d841003043c0100b50a0602c0710301e98809040307082c0ea00415046915400100310b104c580c00080004c0180c0302e402c44100301030300b4141620049140101d080160411150001003071600f44560f0001c01c1003500440000d80d1282c0711880035203250134450320311542250b032960134100b4660500940740000c0d8400c000d90314000155000742e01078013001d20a40d074880e031501a064002020a092024500001903400008401004c00c11500b07480d0340094981d02c0d0024207030402401e6020076480d92085000703118202a444034441e82d0b0547c100000010680d00c60042440103020782900d40c8c0b1400d5208a072143c0e03060080034145511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565603875 1250 565602625 565602643
    0x1101060801050f04141f020d0b090610030c030b030f0604051203011206090305090414060f030c0d0f0302070f0b190c0b16170c03060f0a0807050609130c0e040e 70
    0x81d07a1a0300c1c0100c0d0001e040051201c07084000c1800311b84000c5800d41c6003180c10382d003400b1101d121130342c00590720b150f010582c00b40d100e801c101100e03500071601d415404510580100008107080603a142c40d45c0b0212406035011820b2401d01400310303964841004025960b5400548055903075104031204006280421400ca0b07060391640c4e103011040b000701d03a80e04e0020341a80300044050140034091014141c94a110342e02c0100c036040c00e6140c15042180911081441c58108540290403612007480b09460b641100a40130f580700c4107896050703803181000c03401c041d80d540081014048030080018005080000b03445101003480b41220684200007040d6807031200c80c0e81c0100b141490b80300003001a00d140d03104028964040c01c149400d001c040b640103450705011a22032981b000e01000348020340c1050005030156910541d81c003c109801d0002c1d00d65946542d01c5514071901e800202c00801d615001900e9800c13110280d07090092030340c81140030b09002d902551041c001c40c9400c103100c1c13800d0400209401c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565605125 1250 565603875 565603891
    0x70f03200d0c0c0b0a09060306081b060a031806062123030c190b0105010903021c050a2108101a0c030c1c090503010c080a0b1f110106080105 62
    0x304000840304250b80540d41c0e118180c8070488640c4001030711000042c010f2581349030035a01d0348902400c14001504980e982c0d04000401d50100c03e1b40c1d1035401110108807034400742200d800e921032103800c80c1100500101c114842c040e00c8911050002c01600b81c01520580300e4021000044840c0401e210440e11169400600500d000d01e42011341d01148541e200003030170903030003030300e10b069624034005180c44404501000f50702c2d0019810b03020700c6001603540f030140c6024070f041c00046185400140e0104007004102180b03803488000c540c1004000c2000c1482c0343c0c0c0c004000c0d6500607048544040a800031004c11000c07582d050001001841480d0210007a0f4441200208200c05082d00d000701c41c1d00440003107600e0348000c100c00c031104e0804121864800401030041311310091038000040c0392460980c0b15601030303130409841880c1c00343c12814655218010010025a544442d00041c260b0102070141020700a2104055010a5408068080e8940052000b880b2803075445000030300302c60702210202 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565606375 1250 565605125 565605133
    0x703080601030e011b090807090c050a081315091505190c1704050601083901050d09060501080f0a0506010501050915030c0d060603020306090a05060a0803070f0320 72
    0x300558000d43c400400c1515141c00003482d60404c0b0101e00301c58100038a55000300f002c56100f040041c070708001c0789001d4a0050070a0200710100c81c00a0903078051209810b040c800c00d400010304040c90041d418100d281c02a410741a1660b0130600301000344041003041e80c40004071814203616a00d01d00905019280e54160800c218100703005080090240300c110108008900760307204d00b1300000c4d45446014034011000f80015500d00f607291480c20b2050f807140381c0b5a0f070040d400e100320254010300300e44e85d000300e01c440140c0c0701c90311100480b168440c10b1500c012051400d4000e409009840d40300e54141c03060001114110f04005482035620303075403154014116881031740103114075441200a0314880780003070801003000325602d25007581c41d00211420700700407101154000403400c586c010b1400508842c10110310b90305021001c00d9802070002d21854810b41c440d0081a83e42e2110507000f03000303101440c01e9903190090341c60032110300c002d04181500000c016282201d0160680d01d541210108854024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565607625 1250 565606375 565606381
    0x140607051918090c02010605060c060106080106080c0f181906020606150930010b1c03020c1014180901090c0909050a02090d0f0b070f050f09190303090e070203070308 73
    0xc0406041308201c06030465480340340c0080c9503222500600348294000340030707180d59070500714014900c20050f4008420015018103010951445c00c0071079081400941d0000c2d950503101c90404080a003800c501900030541c0602d88440702018001c0341c040d100240d0984203251103000c00c00c5190720044140003a01b0900308010300d511b01d80803203540c40030801c038040354420130f905044020006032007032035124040e5104d021048040c50000300c1246402c803840344150b00c4001544000b5a640011511540a0b048405030038041e04e0050641c5420307610749051060381c941c500c40540300b0035201540e6441c01403260000100d201026401140030307003002603403000c01246c50181e010740138204c05441260041d0b8204045d103c01d03210320040c0c00c0c10318041d50a90245206031b01c2c060850b6540148000204622079620899842e4800304031205100b51400300c1d41c8904040380060120b40f40c0c200a0b40310f0304120310740001090b41144081044407014000c03030b02566501c00099803688605900140004d00c80000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565608875 1250 565607625 565607639
    0x20102032a0d1a040501030f03090b12010e0709030b090c04060803040b0f0a170112020f04050f060609151603020706030e070504051806040302010209190f05010c140607051918 77
    0xc0f08040c3c03a1441e40b07080014241000c60204d40007a0001e0341c2d1451035840e854140341d04011441d00500c00414801d140c0008519040d000440c18061402900d0000011600703c034071519178a0080c42c3c209200244600b17018042c1c5070317100050b01076039003e2818001c0020f1750480110a460032240f40f480201d151441302c9000034416031019800c1424440d10b100384051400388034550074081c00254207031100c000c2e810300402401a40310f4504520960402c0c00b0480c0c0646041c08040c0c0107d01503401d180c4034200e100004040b000003803a20a0154004603c01412803944484e4004641c000c0d000c0c1c501064841c0821015594090707050445a4040402081b9a08255000690001000941c110401c2c1803070343c00d905061040c2c4043d00180e40100c1e12401c54079050007240c0054440010082d50700349011605034411006201d005d0502580031420b0040c804403080540c2c2809020065400701e00d0614009000341e04020170000200c018124070010ba14090407134052400180c9203200e80240c0303030006c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565610125 1250 565608875 565608881
    0x3041a03061315050411031611030d1a0f120c060a030207080c0d0905040c0206040228030b04150b1e03120d050109050c0906070305070c15020102032a0d 67
    0xc80c5581003002e03112038460451140c071501404005030030020201d90302d00400c00080d140324144030034090f0401c10610206241c41c404014481c0c086040503003a805d551100c19045019500b80c0d58400c0b824058550b0340c0c0071000314074403502081220b00009030884d24040c001010040041080103031b2080444040310300d04079002d40300014151030b015150034000d941c1c01805410202d80c89180364058804201060b0f085040e0001401c0240c13003c0088400c0000000c0d510803002d80040d009410820301c504003a210140d8041d001c842940070340c92500ea40b072418041c000f00454083d550101c4841c00010222194002c03001c2048008204001c81b10000c4e0404942e21001c0202582c1131040c2e003650140c4140c914090809402030b0303000060742d0f61600300c1c4001a104d0040228690070b104000109081d030314441518401501850f1075910b4152a19040755600781c2500a4002c280d461f00b1441074896054008610451000700b84441b4121450540303131540459401e1000d44400501c50745146450b00c1c0c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565611375 1250 565610125 565610131
    0x2304060b1c09080714010b0a0501030e0a030c0204060302120604050c060703080105010e040e06010f031103030408120c0709020d05060102010c021c03020711040c02070e1006050403020907020c1f0e010203041a03 92
    0x9481c061400031613035502d180c14220402d0328440ca94585200040a00c0e1408c4814010107082c01c050143c056200401600d0b40001d4000505000d01a02204190f4686a20400c050759010346041281c9042961980d07641c08210b6048886119000c10450542000c03004c0c0d03901b480c2d140c1c48002950b42001c005645040c8411a25500319541d03001e01c038500d050420189008011040e11481802e04505001803071454404000e400781c1d10030841001050750005a242c0400608000c441c2c5900c02200c03890b0030240140e1050003806c0c008034815070300501070350001d40585000d8008014107032828000340d844442150340070284494643d21414424001d8006201c450703c540c00c0801e847c4d41d0800041c040320290445840140e00c4450103000e0505450009600404070307a20901d000c41c6400d078010460302c42da000c000d004e01c990001117001c1d18000c000380c03510b40c040104414443c0540c05102207640282c11500c8000030110b0011440650000c400c98055441e00c124090828401c0c2000c40039036840a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565612625 1250 565611375 565611383
    0x909070503070e13051f1d071b150612120f020309030a1101020609030408060a09080c0a20040207083901051009180204090c2304060b1c09 61
    0x112242c20243d803404010090b0f00d01c08480042caa0030845000b01b0340d01e1041c0400c0c441c2c511032200070302003921307038030301503040410f4001d51342d002ca0f0384000c41121450400454080d40c001c0d8440250700b0407604d03e0150307160403141c540030001c7c543c0e80c6048042d92114010050b01240c04400c4d000901c9100d4802009144150f0040301d150885060120380f90040003601035989144007001851a0f69050090a41103018134000750701709400d01404588030138010785a24842ca50340e142000800c82d4000c2a04e050000c12816500501c480f400c0c8404403130100c101f00e07014040a034000c01c205190034030a440c401501320309203a007040000d66154001040d221000400c418601c10300d1043c6031085020503c1c40b01d440400410141130414030320f89110301d960840c001c81400c0c404100e80c0500b107901145030765501100c000c143c2e1815810888071315641500241c1d020301ca128055607920100e1000404054030940b010005c8964075059003c16001d03c41444554000700703035035279a9012541d000a0003280c09 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565613875 1250 565612625 565612637
    0x130204031a07260a0e010c08013302010b18100306020f0d0501120b130b0f07090b0307020a02122b050408030a03050f060d15110c0a08091302090907050307 68
    0x24406826407140400600c002c04030381810412000c44c903000300800c1040720783c02444051103a21016108010501602c104401c0e0303100000c0c081d20140040188440100d07000c5590040d41c0744000380a480400041c9004070341f05060082c05003007001d612131040420f0602090100d09696075800a5400002e20200320742e0248409000c40400c0d119260081280600f4407591207014549001e40c000000c061118046401e1501400728007032101150340140e648004031440d0350380d84810341d00030701c0f16000424107440120420990940004800060500071144000043c542210003030750f0b904903000a10a1654560915540355400a003001a241c61802c0140c03c0903120440c25240d90007210105d030010f40c13208103005820f02980055034114406582003e40c445503034841d2501c2082c82d1540c04001641d03000a200402400d6068408000710082074824070f0340542071600f20754003d142e481c3d00c11105040c004400e10194802c40d5051003001c0d00a42e03099a41c104d05131240d4000501c07038010b01c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565615125 1250 565613875 565613897
    0x10603050106180b0a0f0c0210020703021203071208040501020c0f100e033405061003020f010f0e0f1206010306020309071e030204021317070f061716020f0a11130204031a07 76
    0xd49d8450071010011035038000c2c6081840d5004100808007180c040e204246c10400c90200404d104d4074aa0341e1070b49117820071605507100c13442e2490091295040800c050301034004030700b182e54030100b819070003503501500c01c1c070120100c800340d5500e03803047c100e265207099444d405500710181302c95445219200d1068002901d5075541c0c0b603241c28014105d420640c0c00b551818107008510f009803010308180700a07e0101c4c0d400c2d00d10400039140b28a21007103148540c1c40070b4003083d09031b510070261291050400c001d070340155a4070314081001e9007041c4e5180600e40500311011541c1c3c0c1d0103003068403c2c020041e0500b40202e00c0d5809010080d8021510340c403100891000c0402c46492040100c036410800f14014030006180440e40e00201040380c00580c00c00080345500420340c1340400303459400031403c203002c14500243d02e60130b03480c000a1b6540440b850040501007000d010004001d038000303139000e940118150014100301d4049114600005001c030036080e1484070036001e1210040d80c059071908000745c1500e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565616375 1250 565615125 565615129
    0x50a1101032310031a0603010f0b010507031d060703020a020906100918060b0f0c010e0601050604052209050604060b0105030f04061d030c07030201030612122303010603050106180b0a0f0c02 83
    0x11040b8161702e544444c021050003c6800c00344140183d1101c43c4004020f40028900004c00c2440b50039809010040108690981285180040752a050000307000070355803045031078065140c4400c03850603481820382c240002e4560415482c07880f00b4039803560354212080c2c2092169203186108249240d02166205000305070094448010400501103400043d11655900310741343c2503d40a000d900e000d0303041400104410b8403440103407001d40b64120b54603003600c2d0345030b81c005424144410700d540d071040c20480f10720113000004c00d03035038021750041e00c1c02e00c04665528015190b501c01511480c103051540d00025012540d5580300400c107004103202407a021001ca0442e6246801080c4401865040082c04000315a01882010004c0040841c041200318039502c444030140e130050b003100144042407580400105888214031482c0400d00305440d1256181d910040c0245401d000740c1002c980e00321060004000e9500c0e218048698000140e80750201c411811100040f0b5400b1882c10b102551002c00016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565617625 1250 565616375 565616393
    0x2090a0b04060311031605130b010c020a06030501080f0303010b19170103120e0306060f0f061215040b010c15180c0b0306100f050304170d09050a110103231003 70
    0x42d80078070b00650032204c07003408060a06c002c240a210071510006010840c0d40c58442a41720628071030400000c11440900058840c902410700003540320042080100d041901540210b0684801c0401c0351220841c65540b1075581c802030050f05800c0200b8001821000130b55922262460114545007880707400303c21400e80894400e0b0001c03510f10301e0503a044100315034012040540c1d114118000c1c030399403c1c0f40d00401d00002030f0809450040c1898000c403840e9803640000c480301e05e446030084220528203100490641086003007024850f90510b000c025556208200100c8a69007001041705207180301021140140100701114840d20758215214010591824681d0000c2400310309655491030704e501003191552007030b10088244005c500c084003400d50300809980c1e001364420800c600071003030b000c2d0b041e015005082c0c00c080058107180111080290104111280920464030b20303400c0682e0070011f60030307640321403404640ca11041500c2024000780148a80c1c01c000d68585c48031145459031584000d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565618875 1250 565617625 565617629
    0x30c120308130809100c05010f090c0512010608030313030806040b060d050a0f1e110445150605090607020d15090c060206070f050d022101082406030a02090a0b0406 72
    0x206c0c40028138841841001c1c016044036900214041003d1909a030f281d504500d118080c80c1e01a18449401300d00c0481c09600410143c19a04101c0351030303140c50384070350b040b03110346080881c0002c40d400c011a120b41400e00800d41c040d04014170030350800b0005017a140042a009184480c0151101003094000e4028424042c00c08000040c90403183e0290480e03109407070100600c4c0a00140402c81041569415003400824203000a586082080b809000c065000f03c06000c0d90b010300b00076085c1c43c03224050b680c0302c849005401607101c2c60701551813005a4007801108007098200b8000c1010740010b00d4214407130303140648a840c81e40340c0002c2c8045a04110389209400700e851010742c0300c082c41166010030480d81e00049502d0810f4446140040043c103030700401428000003500864039079030810b02e240e1402041030300c0010125035580e607001c2d601d6442001c5080303000b41e20400e03031284120a0284c0310542c4144c034042c3c02041181d034980e0920621542c0188107915240d954884280b042c0e555000d1040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565620125 1250 565618875 565618877
    0x302010e03010b15040816030f0b090f06071709010b0105180d080c01050f0109020a020703060513050d0302190203132705010e010509151012060b030a06030c12030813080910 76
    0x14540d400c06c980359144c20a001c0303501d00844c02012080000500814841c0c0c170042c1e0000c810303072007074940c80304032071800580d500683d0160180c50100a09140d0162600c01500303c02c603c000303c16120746c4003c5080b20100d0325002d0005504000d8003030207034602007a20595000c0034040026070666601c03080f0320350300142007194459440c0d41c03c0c051240c46100c6007030302410102c0d40851070481c4850f000fa540e001a48001002c00751944000f0300f0500c00003802c2041c00b90010706032100e501c0340050050095114070444000444030752006d41d50b15100100352140c0c4042d61068213074181c10031162110815520044107020941c0d040d00111050305401414001c1005e0162040c6950400c6c003000030501d00107216000910f0111225002a610401c1851030100141400d0448042480143c2d0180c02d10342c00043c1c00d5500081401600b81280d8002c1c01124080c0850420b41034480d0310800c0103400240700980028100c01c00701c7e0000002c0502c40c020342c3e00c100d60303c0c2c0c0b900304480082940c140c48810480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565621375 1250 565620125 565620127
    0x51c050a060f0501080f0f19020d0c0921060b03032a010b0d050c0904020f0a030b090f0303040507090e160b0d0609060605040e130b04080a0908160302010e03010b15 72
    0xc4602c010041c10301c090702c02400d111a4501c1d008a035550f44603c02410b140c81030016801241d0100e048018070002e0800500095540e44d540728901d401500241c03890348005130310301800203108204228908900420017400102c0303070300c8070717210480903103012107800c0d61600040091490f1302c181207043c010b500c804c107006a0b21208490b0842c9003100c02021a9034012680442c0307a10000b00045885c3e420400d04445003180c80c0c0380c07030000c142221803000b94150020548403000c014000001c00390361140c2d1884003140e00210740c07202516100d000656000304a80c1c8001006c3c402c84515401140c40410085c045641c00c112004071040d21640365841140349100000304442c50304568011074000d803070364641c18040249010700c01001403080d07200c3e20510401b42c402241d900d03424440401c92803a007100c0303056403600341406c140610b40e000100f044003060140100142420000c01d403966914001c0c4400c0c18840e1442c1c0040d500751110104480d419561400140400d5644c1e0841003141d840c100d1501e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565622625 1250 565621375 565621379
    0xf12070608060105071101050c07050a180b060702031903050702090c0a3f060806041109180d05211603180206030c070503070501060608070909050610051c050a06 71
    0x78164080262020341040b004002c00800b061103a44c2d101210b80007841c1960340d43c0000c048880c1400483e0704041d40c0b014030b1000001d44508200708081d03004402c2d0403b00201c0d4408010000c0902c6141c00c001c2d09074100c01e1214040e414224100c00303401d402820524038013440340e03000504010003120707c0e00c01d451001c0f41d0307002280d500c510168010403606030700000c5800c02c001420f040c0c01607114000c50a40448150403850140340c1c0201e00240341a000300d4107503003010300c1e241c42c2e002071b03a504150041c03000d44e001a940718261802d08c0165552640a080b00d95100d40c8112a01e50001d0380140b6809800c070004041103a8210009110303a408000e86240d05038041401070030380700135980401a1171002d01290000da91144201c0e07800c000e05e84145581c8040e18a002030550044400141155180800000302c0c00d420180c02440340031181e5500c166161a01488003c6803002c4c0c0f1000c2c1c00808512510503400e000c0c4000b800c90f81610480540d03807492a6000c038058a030212080f40003107031038240c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565623875 1250 565622625 565622627
    0xa030605091c0e09160302130f0914040b0103020907140a0807231801020c0a060507020414150f040609060b0c010e061b180405010e09120903030a0e0f120706 69
    0x4510314901c519140404000c150001545032201505d800980391110f007200c0d001d940070354121201c0840716030740c0e242156929000f04907520018880c20003002d0400305121340b1040342107005c07440b0f15400075031094940d0a503024040c01c448010075030400d02052034488120155802d001d40030001b01a9204c907842c2c54a8140288000307a070080b9664010041c1490081151500041c1e48528a912140c10045115080100e242401010710300760132200900010036800c0d4444d0003071024500a0305c0c14040b401180e81e000510400c01c40d00c503a1000c514000e00002480e100340c088a45000040c004100a40c56032480700072035040342d110380854400007960441c0d0340021701039030403400d44800c043c04262920041c3c6407002d0201c0c2e10b941c2c42840c0000f503078407001110786040c6560b00401510800c00c1750f844000802d5148801e40307000340385206d5007095000d2107480c2c8044030900c1c40c1c0174010798240a8142010764014181003138075030b400380c007043c05196251591030030f0500168044c2c000308442032a203d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565625125 1250 565623875 565623913
    0xb07030608010e1b060d0203100807050619031805121b0102040302180a06030501020d05010303030b0312090d0206070b070e010f090b04030b0c090904140706020712110a03060509 78
    0x101c07004059050440348070129a0110b80f500720b864003100602100403201000641038894001005a00d07480801400b0031006032411400a031041d1204a0300c03004e03101d0003000301c5c40c080c0221071070110f1140704c00002c03000d02ca0b800550300c54451840801c20300c1d5256403a10308014001400c42c54040f004544a0112110102d0386401c03074171100002c514090443e00417514a07040c001c603107032003280803c000c51094100355210b0070007140c00c40002c64070791201d030711741002500c020700c02600007a05020040c441e0389008036881c1030284208607005e203000c0c0b05000b40101601400010781c0d10200500c44540420354800300c003849140d250703a80302505c0b01254005800840b035154100c0410400d000280980800c0408039410f0341e80000c26410180e0760402c032000540f140f13a004030b8003c2410424013003080002d001081f42548600c00303480364691620000ca81d2040b0030320408018079116154580070604007909010030030405801c100c5c0c065100e07140d107420b64405070f85000155011608007600f07624010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565626375 1250 565625125 565625129
    0x3030a06050609090f130f111825030b040e010507081303020705041104080a0317010605090d1b0f0b04090518060a0e07050a03260a0c0809030c06070b070306 69
    0x450071400c1103510008203134841801002540b03000341d0302000c140d501c3e0b4001000e6094940c04542c40c800340209240090325403d4040b03409004281008800c2c00070254088064403402440d42c0c40d0745006007000d03841c8074505220700800241540c2d0940300845840d1350207440107400264001103814108024010715107000104142c41c10094003c07504c0000707034042200422590111800303c0e00584140d64642c85108540c01210548192107003e02090780161454440418122450105a980e42001d0302d280c4601280d4580c0a22404041790000e14070a01480031452446803441610381c8513112034200300003a80000c00100f01c003081c10131001480340074407644061940c0000100c003018118059480201900352600c0e1500e42641003043c50701080307540000c0200a189520342070380e0341407007031118464807105590740b05c5025003450b00d038507800102c4922503aa9580c15160121070344440d480d40c5c00000b8100d0741402504c0da140180c4c3d4807035020b0007980e0300405124540d8140360801500710350321a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565627625 1250 565626375 565626379
    0x71109060105040807181811030f06011a070602210103050c0103090209071d04051f1203020d050a0215190b030606010905060f0405030318030f030306240d06030503030a0605 76
    0x30002031014802c0030804000300c49180040c165404551446c16014000100074400074030700c1241e41000740581200c0d142007120060301982c0010000d84007d40c3c90760030901447c251012004144c0c40001c1180c4014a4510300521006003404034601000c1c149200710a10301c0c0c10402000018018480c0c01d101c2125156400d0804019240309580800c0351405c0040c6080103021118103903882950900300c04074840309006101b00018903041e40d40200041e0204400c1500501c0000c01080764958001c005d540741d03401d60014070386040c18a40840c0c080c0d00264140086016100032404496214100180170b9001d0300c0e560184070911042480c100c07038483c0b00c1944a86e101d4024004c03240d82004d8820203036a0191521952814034030a015130074425684202e405d40710000708003208212840d9107500c42d840131015100c075110654065680c030700054a06603807254180180002c00b8002da007500e1050080301c6500307403c0030303030761800d00003104da1603403003a20a0f4000104100e0000d16a01c9404003400701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565628875 1250 565627625 565627627
    0x703020a090b090f0d0c170309030709052a030106030c051215060c06130203213f09120408070506030606040e0c0405100c030230071109060105 63
    0x41403802404410503200c0c0c0c0d84152030015207400c55460340d040700948100041c002c0303280c0341e0b42c034a00714240c1030303941c070a44d504180d046000b040744200c04000c071014904018010090b541c20403410100074180603085c1e6108280141859200e0394001040041e03090f4502c805944070341c5001e0000e410f599848443c003003040f0381080000d4142c80b105100c2d642000c003c40e000b03112a240c410105845110300e6a0141203441035200300611034150b40140f4001038400c0d0b09540c8002d11100c05442c2e03040c0010041002084144520350060311481d4000b40d0591522103140d003040300c01d2640f000700858000c0c1c200303c2161b0f40f600b04240d0450403c540c0402107000b00581e4500b52a0244035625480e29026087c072a400000102d220b60390b420080d1400340542e0312401c600c50030402e0036150309600c10300c107241c0070305001c0c42101d86170f50240780307002489501500039045000d000300200314115094641d04901281c458050081c10500c140a400307807520840654404945440030402a040020f00741810000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565630125 1250 565628875 565628887
    0x914180c0c0d0c12090e0f041401021c0c03090305070b0405010f02070821222a060e01082e080d0315050604050a060f02030706111206240a180617070302 67
    0x1404401c2c580d0300000030031f480e881c030381c45901d48100c030003641031120445980042101d02000b0580b41c0211031f06c010980f002c004500c0d01900a8007512013510380500810014002c41d004034041c1d80c010344d40070b44502c3c00040c0009002c040941242c1010005640420010940c03002083d003120303024900031b60501c1c00c84400e24111000390b0742c051103044136010710380c0e1170340004007003165510b000c4031945a0501030110760903181001050f00302c1e1342c0c8101400101c446100d111194010100107000b60f40b40e944480810244000c04940c0d148000c0f00b000000b5090f1100003003606052002c44126410380c2d80c045000f05101503c901c0c2c84041e034000e54455403040104008599452000308100c8045081404d40540500010b038114040d4a9020f0f00c0a4203040d402941d81880c03000524040c01401341d005543d444110511041c10715221249035500c500d0f44444010416a0000c1d2004d034100345400088440300b0601d041c404448c590004004c0340440000001a070042610b03035920031450b20301103080031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565631375 1250 565630125 565630139
    0xc030e0d0506150a21030239030a0b01030305131715040201170106180902070c03060216060e010f180506040b04030e031c0914180c0c0d0c1209 63
    0x1002e4a03a58950110000108841c2c030741c01307004002401d00100c5041c0c0014400700004407a1081181100103020301210108808444070000c02d0982c80b2503817000000300080c2120300740b003160f410302a505200c0c0341a444009103030207411901a6100c0d656803500c400c0c4c00c1441e1100d4262a400c07008240511409290740418001040703091080101d204036919100c40c00180e404441d5030680741104a03c004c00818600d400c003400b40104644d00c148104001c0d070307803200401240030300307000240b00104a640810100c0c0d03403600542003106104d049621855019590f0100b201c40010309907046944030444521140344911601d511300700f04a40c0c0040005031541c4003916410020300040c040303000400840c0900d40300c0c8400104050000c2e040b12284e20928841a0a000c0105040780000c0c49000000c5125900b1034001340c0121005808a840c11b03e00f20182440130100070101c81d2402014007411108000402002c0b0380c4014035108d1b10b001031b0f410300b0864508403052201b602441000c0a080141d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565632625 1250 565631375 565631383
    0x309031203040c0b07121e051b010605041a1203040b1917090102031816180e07060c150204050a050418051c110d0e09070203070f030c030e0d05 63
    0x208000c2100340d41c075959032410540c04041c03030308189500b44001c03030030300c04120713503001ca8540300851074680c031040403499401c10792002151120300700040e82c20310501241c0310800f07042e89801d602c60000808c0031a268800304045035102002d004005903451400e68050410905001500119070301940c034050500040000c1c2e4807490000201540f080d0342c3d0b0280d038504c145070844100c114200c4601440c00c2c485c84481c081d40040e100309610350524000d8002000f40001d400c0f4845801c9002101454904240d080c205040001407020701d5440b0030b0925400301040c80510040c1c840f5460b0b1070032400c0706040001d1461456018062150f01c108010300c0f42c1c1c1d680c0c076980b00131980d08039408909644c0b00704aa1035020540c0100034964882e032100d5144c0e5205044e11610881000ea43d206210701600c008103654440510b141e6001c20b4060004401d44d042c0341004a42c0000c0c18012a440c2403040e942d20076000006134804d030002124a00c111040580c4086070000104080320821a803030b13641d0700d07803d440d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565633875 1250 565632625 565632643
    0x6091107150501120210030f02030414010b040624180828050c0603090a2012010b0619020a050d080a0f0209010e040f0e011a01030c110c151207110f030903 68
    0x41480c4c0c81b0f0341c190b2114400d4001c0c014176400464259101e051078a440300d203070314031054090312550a00200c50011305003440780c9002c9601c0d0501e10b42451f031010a0402810495850701010044008408208102d0b00c03400400100400001080b016002c0b03122203100f407072408810304000381100c80a20109800049440c4003030000c8070056940d8a4000d695032901d0368600008001c0c481c00c40124000d400524900c00308000c0503501080c428003c1c011560817900005201075020300c09200042166541d420914000c10042c01200c2c4100c4458070b80600d094400701901001481450400c00c2040c9140900c1c03410b40d049031419410200050000703801801d070300170441e002d50380e1801601d80949041d04030150049108008108022000c0c003032000881c400ca03040c601081c1480101458188034084512804039504050081000d540c0108148419001000c0880500500c000c080305489140858015240c540f50022a12102c500c500e0402d42501c440c003a854000b48a41c550549020940b114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565635125 1250 565633875 565633879
    0xc0512030a080c04051f0f0201060e0c2109030c1207020102150603071203020105220203060a181202010911060a0203041809080301030503030118020f040b0d060911071505011202 78
    0x30b043c3da581000c940c0c032402640c1c041036200b51121200501c0c001040c400f0515908a0b0360f910480c050b544000707901341c502c180f0409004141c940300207040c000071040a8501c401000b03046030080300b940315190b00b02c0403058408044581002034081c801110811a8070300201c102c88480d401d0062130340020307407101e0f400440040103603401e90001e003a50350241310b0764015080300015218a0f29070350400030b0007000100c4803501d01c44c000002110884004040010185500900178410703a0784444010000e0109110081c00c844412350900c800209841c1015003c00000d0780005140b2020303007860362540c111440306501800042142e400c0301079001c4200d400b903941c10340082d403c0452452004d001041d603c02c018205ca0800300c00401003007000310055040743c103440c44800c3c490070031543d510124070641e4043d104850003004100f1030380c2541c20240544da0107004001070040d60329880751040e140c8440e080c1c20b081000040510400c2821102c0440da50b00046c0e0400403503040541c1c0c140142500340e00a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565636375 1250 565635125 565635137
    0xc01090302060313030309170c0c0f100c050114010909030206070807081503030d06060f0206090d0f080604150605031608060a0302090424020706110910110f0f06040c0512030a 77
    0x1d4141341c001e407c00c0050a51040c2550012000e90602e9162600200d04820a500a205400d0a246000c010b20302405400600610196280c0c0c6015030f013809614104071203a54880300036180341e104072240c09000b04a00c102c04540d015a07072800134100391008014405000342c000c20f009903d607200c04240d91114041900340240c10440f00027a00d5802501050408c8a003008004280c1c981d2000440300c0141c1c298080b9200d40d00c0324403003580c07100c0c0080b04620020b41d05641820f81c10340720b111456080b26018200082c103540d03145801e005032840341c1004000c82ca00000b444240088100301403140c44413031500c3c0210341001800101255010300c0007170b2003404a140400c00b4041076000d001110061150f440c0c48080d20101200e000e50458101641d401d807820342d00200402034081182c030052002000c090001c51009800c0e20388001c100e940300100d00c904e0b411444407801c10400b00f5a28203003040244554a407602e0030750202035841c1c0206004200c001481442e80f4000419147c49910303600303080d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565637625 1250 565636375 565636411
    0x105040b0c03091009060b1809100b040f0c08071803151116050a0201021e0c04110d0e0307060b060c0d030f0f06060c050106150e01110c0405180c010903020603 70
    0x4d16001e00f0182050101e442e005c8044200074440d0b11a01c081c4130300341c0e81713000c00401c00d8900d02603000382115001c1c019089040c8540c9848025400a13900d400001c0c80021b00072640d600c2c0300100c1e00034440c244003207076108050214541d0403404214140b11826100c110303280c15a0fa50b00f01000762100c410207500c0e00c070724000710703a00400c506a0307103985810800142d43d0741c114281150381e40400c401c20b90240c061900040c14100c09203030707080b4143c011701008100d012400c40900c0010214201889038910b024448030702241d80c240100d1070100b04880056407200c260f81010b4013103034000d500b00c47c820b00040001d415008804108003410303d28504002880c0e5003d040b81c907000e070009003182012030b03240c5040440c641c1d8000c4d42ca0034446028500800c103854071070070400300c010348140881700400e070140102070b119803141403030003580301c070000070f551034000c11801003010303210180d595940e40d03440e00040210700c4800b00800c01001900740307400c40c401491600490403501c0003401f94521901c40d0100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565638875 1250 565637625 565637641
    0x8100b09070c08162a060827070f150e0307060206041b051003020d38010c1a0118060b07062f0306131401050613090606050a030e0105040b0c03 63
    0x12124810f904680200300380c0100d03032103407411805415540100890310803408903500344529822441103015121022000800d1203c90445414440c1100c0d198403270414007051294100c9019001400100d41d0003403d10318000014107186402c40c200e41c003c5cae1003c0c0c000c001c6184d00203003064200b0342060f221501054400e00060b8403850f150040707600000c4545410100507070690080043e40304001c41003200c4047c020b40d1035094400910030004d40508003c098002d02200624a031120005051050903603603581d480d4852480c1e4082001480414180100440790aa0240d485440c1114400f00103407400c10f19908968020b8002c05448195100d40030142c040c604200c0c201d098422500d000e50201020320407101c01d46c400c940f81400f481c0f0007501500d5144942c015440035004242c1c114504d03130f0030310060104541100c900c1c01c40c0f0300c500030344c0003810701701c180314140143c44695603080da2400d101001500b5a8440350301d41e290b0743e1400c400c00c8049030f03182012903007259856070150b503241c0320700e04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565640125 1250 565638875 565638907
    0x1060506090d170c160609050f0d0206030c1213020f1923090f100803070b010e07090f0e1e01080c1210180c0807050904110d0c08100b09070c08 63
    0x11031a0501c41c421443c0065524170441700100c030301c581c1d1401020344c0c65405000700b07051034003c07030745d0032039502454280180f5021010b15803103440c000743d5504000744c668411300500780a4036082001114030800c0c500758140340d07892280740003040e1414449040c0500314103009948a22a05e04503080c01d501901f5803600700c61158004550007007040106080c002e000c1600781c141650010302c80154141700046a400c0402a1582c6a0304502417001d81c2e0b01e42a00a1030002c0d008200104000c3c0c2040d0104002e0000000040a07010010307040c0480e140410703006001a5800700c400c40300780c151000410034210005451040c4040c203990342d20321928002e00c1c01d441d240721401c0400c0d8460a2a81541d034129101c2103810b521401a100301c084169200b240548500881c0107041d04548818000b8022451200c503103400c03590b0141442808a034903840d1401407007a29082610380b60001c44403151450039070b0260708828001100c880032181054280603204440d40c000c024903070000492000c0c40049562 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 565641375 1250 565640125 565640137
    0xa020a0f020604050a060305251403130c0608180102040e06101107080c180702190f020315040201300f060b0705070f080706080114040e120a0201060506090d17 70
    0x14085c0c28006485980260103060201d17044424003826020301200c104c1000b03000c080085450711401c61910b01703850100c50300e51006241051107014821a000060900f880f082c00030242a81c8024050604026940d0828030011100003075a00601003840408000714400b608400b04807101d200c46c3c60646403c1d1400852030300c1d2500c890040035000590260007203042c02e4032a03011104c00b455131002500b0f084031544251481c03801a071040104160050705485c4c1d564800b4000c80119945e0074140d8000b074a80454011804640081003092004550300011110150141e002409070f401c1e22440710702800d00306202c110392050b600c03103002c50400f040c41d43c06a0060b045150040b940c0e0074503400c0c10341c0d40f6401803080c0f00380d01c11001400101e480c000b003400c6003030752250342c1c50351441c0e482d00c00204c045107400441143e00640d150794812049004100120031b000b11125a40c0d203030035421101a084074070740e0380424001c10040140c1c0e01942c2e00c0c1c2d84041052a1320800c00f0304110b800302d86003c4030f80900c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 565642625 1250 565641375 565641379
    0x503160311061819061101050c0d0c090b070615290a09031b03121404090207170d0e010b12120a030608030a11070f060e0906270603010b01050a020a0f02060405 70
    0xf05424181c5416050341d02410341e411500c4005080c10741c6c5903518200d440032070300070070b4a04092110007198070458101015015503403402960740c0b505e031405841281e0181a00302c1d00c05580f40c0342d0340c0f042c00090040710300600c9441d4a50b545514120b02d08035a40c0c07850311000c0c540b81400940102c842d406041c507103001d117810440079420045100402e01803c02607003c1650f2682140780d80a00d501d205654204041c90040c4190303050610305030502010b1f40180000b00c076048520896480044a09809440c01011210006c1703465010b179003040e8212540c0c2c200c0700d40203d650f03005c400d003030000c00101102c003900d050310902e58aa80304803084000b0030441c0c01c41d038458080002c03850220390340900d01c407a0500182c2c1c166003545640340011049a41d640c450398003c10350580701d414003403074400c400301e80c80a406007515901070b65902c1d00c0708080c00002240c4064505030b00920025003801d105a9040d04001e0074880d10f400d45a00c0041d54842c802c01c8003e002c2501c03a9185011520342c0c90039500100f00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 565643875 1250 565642625 565642639
    0xf1003080706150f171b012102071401020304060e030f0a050706020c0303071e030605090a05041a0106090305060a231009050a0905010c021c110f03070303050105031603110618 77
    0x4807000341880045e04e0218000300d10136050092042d000c0e100190500f500142c4642a40304130884401122440305940544036550901400c0c000c5051001c0c01440f00300144001a9249042e28028003200c1c0b14440b080c0d1654010320980c030101d1500300894200a000b03041c4aa2110b0203450030b04064403902401c3c5819000c08814000790741c1c1c001440345a000c0c682d440c010880344000e4000c408850084c4a20b55100d00c4503000300c1d8000d8403d50100e034019004100c03070b4503e401246c0b0024402c69080c0c4c08600025041ca904000380b201c24802d20341c1010400c0700c28846203072a510325000d01c2100c018025a4075610310086200644209502e000404150806114515101108400400d140ba109807995400e00d01e100070010b01c085400022045a1284850004920a400c44985160b40c041c10300b580308043c2c0380209030070100044c180c843d110380c1d0045807941c182001c2c1800d000f940c804c4000c000d05001800c2c00000c0f181c0c82070948996041e100282c0381c1d03649400048040c14030000d000d4200314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 565645125 1250 565643875 565643879
    0xb0715060305070e0f0402010504060c1109040b06100513270c0309020a320d020a0e04050d0c081905090904050a03030612020915030a05060109050f1003080706150f 72
    0x80c0403844100312000429045890354414045c40e0005108071802400140c08000c14003100c3c1c05420008c09083c001c0d091004404450070202b0840203080c0c501399940083c9104100e110b1401c03071014440c010491410504000c1d004003c2615200c04e40100c140d0a00414140d02c1414100c101250702018845401d00070501140c130058000d2011a005034010042041d01080c902140c1c80c40c0c40070b5240c11900d030310f241c100c0d0482c603182146140e04c0d240e80c80100f640ca6180036903a0340c00c0c844040c24103901c58038058105440c15030f1400d42507540a1090000845a100200385460150748419104034908442c88883c800110381c00d109010650358048811428041800f80c0043c401139641c0c800d840030000d07180c4904446c4442ca8110400a40c050311642c0028a0b14a0b42c0d51201100c100160480380d0141856541c00c2c240902600107001040c2d4800820103000440c0070300c150040044800c0585660941d101c940307503841082005409a5200c50010101001000d071110080440444003070240ea = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 565646375 1250 565645125 565645133
    0x11032a0a1d1f050a09060e032d030c010b0307080705010801120c051e040f061a0c0312160e06040506030103061a130e0105060402040f030209070c230d03060605040b07150603 76
    0x40c104c100e006002075000c02c8042101401681011880c110050080c1407003c240c400d0085880e4401c590f0201240c43d410460700100c0c0100044e0072484043c100104401e03005100381031412100da400044180d02032030f81042981d0b000b200441c1920150b6071030749100111420000510030043c0d1005802c0244098941c000000d420540088050116014000848441411403c4e2025402081d03403280116002d010802d001e00c0003855180399020503203080011000e0700014030007080310b02d0749841001d0710020101035444101505000c80449160382000e050901044c1c580c00140001030405540f290180800a2040762030030240c00020441c8180e02100012000036200c2e90a11310817941c09c00010031214681402030740e05a4125400c0f028146c0c0c40c4d0303003c0050742a0058459400d01c1002e01c0140d0210300c1811300c28545001d0101000b052900c9000068a02080071407d10100351070000d0501031603034010300311030460314403020702c94031012941070184002c5030b200b851140040c90300310008100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 565647482 1107 565646375 565646377
    0x70f0b0c0a05030a050c151509090f0d1808010b0d08161502120609130b100e01140301050c16060f11032a0a1d1f05 51
    0x1c41d240398403800d00311344c000c0d488000041c50024840611792020450601441038038004101249000200c0341806104843c1840c41551039801007010340c5c0c8100003c618400170340307013950011184107401601a026489552500441c4a42d001070703040818451801440009411a0311a1049590340c1a09a00101c00031810b4203484079002e010804030210850404035544005a540c00b00c007003c50441d140c01010715204081000410090070242c007400e028599219050354545c2d150b40c1c3c40f141c0317905066000703030203d050381200015801d4090010b140c00c05078261300800040e02c60524248691050248007003402d6101101c0c5030001c0c445601411031000188000110f01500c410300140c140e04c10b5510f290304042d000040a1504000c3d2840099501c0d050340940ca010f000d1300c4043c007403208a02400320580d645001e2207601741c5524500668240e6194010380034401840800707001 = true := by decide +kernel

theorem cover : BRFrame.Cov 565467625 565647482 := by
  have h0 := BRFrame.cov_init 565467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 565467625 ≤ n) (h2 : n < 565647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
