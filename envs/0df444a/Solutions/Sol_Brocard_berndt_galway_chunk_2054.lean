-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:44.435042+00:00
-- url     : https://prove2.me/submissions/289b1770-3ab3-4e7e-86e4-43550ee58bd9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369244604 ≤ n < 369424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369245854 1250 369244604 369244609
    0xc020402070f0501150e0a02041d0402040b0603070309030311090d0b06010912050f1507080a0b0a1703120c131e0503030c031c1a060a03200a12060e06 66
    0x14003159081d0b4824400308802000310300c0c00d00680f1450316181085503605481c0000c11608038601802c0701e20614010001000b118485209560044140d80c0c4800d249880e5807000500a0244d904003507000b110110400454907055808140500d000c1d80301441190800810b1403000e1103040007007548111250750f000080341e92602040d60008041c109580165242c0607407148800701044119038517802800015540c0d42c050041c5810200d0b141c60325011410402000340008800600d003028460f0b03207583c00e640c0b958900c810500200784442c10300044c00c5800a0741e036100d5100c42c060b40d100d400203001041da4a0903d80843d204841d04400e900049401c0925110740842c5200c1c0000f0071851041c400b050035681400100b0b1a5a1080001c60790b404d4142071080c201850410402c108a282c40c1d4940340c1c084c03080703011041c1080704a845503950404814182d006240b0001071100c41c2c49021540b0605c0d0f002d0100a2030210344640300d255102403c51184000c0d603155000c0e1160507040000452400d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369247104 1250 369245854 369245857
    0x150509090a030908160326030a0b040b03010606170a0212040b060f0d05030d1503081b0d0801121205280e091e130503030f060a0e040201080106080709090e0f0d0f0c020402 75
    0x1447d000c000809880d18000e4011103800564000080c142d60b480d032010940b0382131090008040703056000b40309081c6000300c090700c1d6150302e41010150456050029140c8030107541200c0300400070703e00c0b907009400c007820701c0c0c40a50422603a4500400e0302c16611041440e000d680d00310415801001907281803030b074ac009003001d000f00c1d1803030481ca640041000300c00548108007400300040030180251400d8091314815207001c540303c8244090040c010010f20501c042c100c40082555000410001410078654040743c1c0c5200362942c041c1e42d03400080051040314111003441c0700751000c55440410a004410800041c49816588042d980b01e600c0c01c4e43c15120841d0343c85a43c0507003080f0030303903034201e0440c2c0390b090031580700302c5245100da000701080054615080505a000e80303541c0d0000d40c00d80ca040e03800039000c070806004200034003001c50005003416202c0c900d00009020104000d001d10441441003503900c0c482c000e9030b1446801031079103008030700b0700c121419042c0c08801d1350382b0003910302281c003480000e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369248354 1250 369247104 369247133
    0x1060201050f04081e0f0c15070c11151804202a07151814090c0c0f03070209060118171509031b010c0f03150509090a0309081603 57
    0x1c40c1180b034171284a60005001a114500c1c003102c03900c3d030724a014440340c5c0c00e03c1806400c60520918503801d0045d1382e0ba11010210160340d2200c540074100074007100191501c84c64040301d020a0034000388075240980f80681c402030301c0b0000d0f1400c4c405080c1942000100035044981314203050380138420b080340003a407601401d5031b40000d03400302884c80d004010240d0526002e07400c91021814203041d64100d480c0e101e41c0000340a01c9011714008040e080c000500354039410600c485110f051034901046203414500704440502071250304460210132810406503d940144a007070b0720071b150000c0014038550181c01c04aa00301c2c0820780e00304595041c0010f5803800b440007140000b6038410301140c14260001c4a450038007480b070341401982c441014050000c0f481580e5035006440d6410000440b80e0143c0060200e0240c41c1c41d82000300344021240003a42c807201c2c113940300340d43c044806007e000388000301050001e1039500030760700e00760140c0e00c6400303003a42c4a508400340720740300e031150100700045552280800340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369249604 1250 369248354 369248377
    0x61804020f0303070f030207050102060f160e042904090206091219030806120d1e1701060e19060804060203090f010515210d14070f1a01060201050f0408 67
    0x1001c002080032038a90303040b07808110b51490200516105240d0100011070052400344014005442d00c00d03010b01d9030801c003600c03264000c4094490b124030746000c0e6006081d0f40c00081c0c0100070740311100c0107030600120601290b0701d4104066241100300d007050f01070b0303401c4590040c00b45840d20003800b0900200c0204400204031a010b1043d031070b070080c0c968502102c4207034003958070f206c1982800000c01501030000319039011690712074600e20407055040b500f0103441d45074543c0d01410aa8090106440c92440342d0031141c88000b000c0c002080803070304070300c0c10184000240c880d01d05400d0022980700441440c2e0080401246448000038000340298006552007072101c0300b9982410344131211a802c3d104103885014410b100854107428a003041d1045221351400340b602c403e0a80100c20180f5100d801ca140e200081002c6a0031081514040703c0440e030245034040b01c00d92130b184403420000007c1c0c0b1004580310010f034018000051862050017500d025032410101060303603032250b81d01c0c440e01e58040c01000c134 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369250854 1250 369249604 369249619
    0xc060726030a24150c0b1005041103090c1002030d0203010b1801110a0f030309020d0f12050901090b0904060e130302070e041203050402032a03070522020d0b100509120606180402 78
    0x400140a0803034060081c07d1507540da1010350305085c10002030350301c2e40c08000d08040c0300b401080070650001440700c1a6610541d0b40f6440130b200103d0490440c4119140d0024007800000001035001206000388061003403c0450317032007039a0307501c0111441060344211803caa0310884c01d000110380c48400d030f040d106100c1d003000500030802c0c0d80851105280c8030415200e41710410140c409022350b04108166450300ca02d01140f80052200010f0010100e070700a8100e03080e030114414140340c42e2603000401401048040d060180303070188038224421092001100140644000001e0501c800200343d4040c990012600e166000b00100c1140200001002a80d02d8840c032400141c0404092175040900f2151604001e1001c0c80310302494601a401c0d031016000b0070031800700f08030050b44c2c40c480c1d01c5882e42c0c900015949120209145001c4d1000400c010b030f02c001c201d0510411680c0200017001920b0090340c050070052044010076495050460b0150b40004801280300d80c03071541c082c0a40d610a00c01400f98 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369252104 1250 369250854 369250877
    0x90901030311160602010b0a060e100c02042703120507412109030307080703020409060b0301050102060901060b03130f0b040b04021507050c060726030a2415 69
    0x2454141d4544c052000350350344020811090a015010364094407040c141349114080900102c1c1a08080ca0201010040004540011076495400c000740701d05880034010710510a150110071210402801100420081d06c01d6100006240c052144641501d46415403500480b80003040203403441031182c040d501000415045040030850704454015100850f15219082c05d400a6881001d50101007584080c460400100010000446e64050150303c0c0c080d15030346a880080d0003034007498100040903410302801255881308803016504a500980c04c0307410342c1e240c10219900f03c60b658016034030341c00410000500e0200d442c103072106c0154854000c0d0700481000d9100d4800810056034200c90505600c01404154500750b1442101484c001c000e251070246030341e072080c1e940c00c1c184804501850000c0f9022040c0032203585e070400c10054950b4008c03031181243c008a91240d100f01c680051080c0340c2105c4205944800603e0445c40c0c400e400380711407141c1080b020b075502000044804c010044c108101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369253354 1250 369252104 369252133
    0xc0506010602010605040609020712050a1e050a120e150601090e09070303021608030406030504023d0905010905090a021902030c15060105091905030307030206061005090901030311 79
    0x200e008000540c00001c8190070002044140c0344030741e101c20842801441042d0108229008141a40880d41411a40c03903c8440b020781340b0002070800701800e04c2d003005002000a401400030706002c4660b40d00c042d01d4013940b00280084aa0030030325003015034094a0147d00744001030040036046041410000c0c81d00b075480038110b1240030101c404404603001800100b0405404201543e50703075800d041010400c604040300310384c0d2406140b140808058a4401040654907600401240d0000d140851501c20311591140c0a6240d04002400724150644025105540c4144007040560310141d41d0040320341c0c80c0500700041010043e20900100d0750070800304060f84079880c00c92080c0c41007034020315200c20580a6603810310303002a42c589108050340041010710f82e44042100ca80721001c030f41c1e0b201504e004d008d48103000c607466005590184030004030301c1c06042d0000b83c0a40710303400c11510082010403c40f030486190082a02e1103411a54410046c000039000d9414501d203040d031481201c050503c60b90f00b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369254604 1250 369253354 369253363
    0x3052d0313150503010b030a0c03140c07030e040501080c043b1612081e180405090a050622080a0f08071814040f050f010e07111504030c05 61
    0xd2100c041414541c00c00000c0e403900e00d02400140b42c0c0c10042d080d03600d00407a1011510006207820381207652006600812030081d405a10100c24407099a503503454108001c010580c40820107802040600c05500b903c0d103030502034141a100154082c010030700124007440086c100e0700300c640b082082d50308500c048003440c0300380480703201d01089075800b000b60310180101e0511304c1c8411010000c442d0400203001810b00350444516142d17004203480d50780c0348503100c504070000c1e6008411000740c00008030fa00a09941e60841414504219020001c41d01d6041c0c5c42e0b43d98850700c8000900c81d41291000828210f1503e801300c1800d60200c100103415006540c43c0401980329441070004103072070007a490700c1c0b681d0005030150301c0301c541d050010300901e5140c00700660f04100d10450042560030413074411503858941041e44400b0014600340018103080c0680c0180820074003038030002500d1030780000d000324803401108140c209090094645690740007004020044010b1042c1d043c000c41e8100c440000e4010030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369255854 1250 369254604 369254617
    0xa09020a06030c210204150806010806010c030309120f021014040206031009020a0302071a13170f03090705011e081f0e070e09010602070305030f13030206070c05180103052d03 77
    0x1000186d40d64100700e5041e000f600700c3d082c51070402002c40100300041c4d0708040610b0700b03c4400d091080d00c000303203443c0403405842d0003080108035440e10201c61000c0340e0000d0102402045680aa45c0c1400544046a00315410310306c0400703071100180c006c0b5001d82407000c01190032554105401c941c60ba00c030040300b02664043c40d0070030002030340050b0040c14010540c2c18180020038a001400c868106400c0c480311135000075074041d041c071000842c0304002e03404600888520602160700c0303075228a01035500540303c412620809011680c3c0d508814401641001c0c8064080d681d0307100d00c20162940c036803001003640c94480ea010031a61281c404030300c505160703d46600c03401c070569906003090220001c1c0034103050183d100c6070032f41d07021500034800284088180c8682940d05070810792960003200c3c0380d041e012043c1d80046d400807000198007080c010100d0820080c0e500954000c05190140b021078a82074000f440301034135a4028020400c0c440d030808128008031078241e1948030010741311089542c1141e101c075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369257104 1250 369255854 369255917
    0xd0606050a0609360b010e0a0605040e01140603011203020337050f0a0302030907050904050a0b09070b0409152c0604020712140d020703170a09020a06030c 68
    0x1000070802d5004d525108444992a41c1901c1c41c1401c0c843c01021110a40050300030303a071620380088024030f911900030005280c0b0001d1000c00160342e40c0c00f0280040e4400d01030040b0610482c00003040400e031400c203c100301c02d0041c0450b49541c3c6480080901d0605401d41141140001c00403540030680084050454112021040440704d091407900d00200c090880000306000090091800310150481500c0032902c2c6800e0140c2c2d2560340c000007038103013002e5404c520b600c040c03c4001e1100380000082c1c921485403082d90208125110145420f82c0e600d2284510019001c01700014400c03e031940c1c01c4441d52441c041b5000071076a0300c88948804900490a88000420040018825003c1c0b2400f011350084401c0d03d0852501c0c800d0307140c0c0040d100300441041700384040003e1a044520b50320080f10381004019400710340b1402640340040c14080b5911500c2a41e18141010600007180c5101d419582503001700107a00032460a08250701502203a54641c0a01400003001011048049003484000109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369258354 1250 369257104 369257117
    0x7050f070c0f150201060509070309050a231605090403030f0e1f1a0d0204111611040605010203090a060f02031612080714030a0203060f030d110606060a05090d0606050a06 75
    0x42a0f08500c1c03500300b40101108582c18000c01b000710f901c0c0c03c01d0054002070246008112081c260920034a05100c1030401059045800d2407801c06011010440680f0700d80d00065038414800c0429190144906000e21503120070380b0000315000034003903404103c040d0704040021807008003000712541440c004958101410380c1e4002c50f041c0e03c0e9118498401c410f50302c070404404a00f042408a60ba12154040c0203004a6584412040e1149482c050318000d1809a00314400180d251509002e0b100f000d1413540c0c081c42c1018000f00b402d41c008000d07240c1451005c2c1c1541c510500c0c0010403594140410385240035404100104c0e942901442e0030707080380c580200955802c0103030b244002080c810005241004201803910264615400141280c0d040710202001580b60b88600d4002010102c8100d101031f41449a08030fa10344803034005030100f24101c0300805036800340e0380c0e10050207641d104060045001590800c10b15219252120070701c24000e000301c1001490607155008226011925000a0040760b075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369259604 1250 369258354 369258359
    0x1b02122104110108090f060109090c030203100e07120816172802060106020d05030703150e0604061403030904050c0d0c02060a0c030b090a020a0e041e110301050907050f070c0f 77
    0x81180d80304c0d4000c184000201000c22000300191740b00c9074103005002e0201d441d08050340a002c0f24400110140d07030010107a410102410521038000c4c0703070700e280e440490b00821400081140a29150340d030790b25000308005242403451b0f0728000b600c80c4c1012040350300d54190107811700944c00400141000460001003801040039550308000301c01da452410b14110b5026000521032550301040208601500e402c0c690b4581d203c003401a40503055000d410100e003031f144100001c81484010306540102d0041e90104052502c0d0000d422103510500700840e01903204001905060400341e1245502c0f0f4244041c2c02c0c1046010907248064908440d9500c005074003500c180500b48510b8030800c0800000d0b41030400c140e0500d800481c08428005100c3c1090942c082451500a8085c0e8a01000b01030300400c100a00501110040c5e88010b07482640f025561400d141900c8601c80c00c1e00b100c0c140d82000b485503003103940b480d00840303c540c0288500d0445440c2030010500092401e2100d074064050722904403061030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369260854 1250 369259604 369259607
    0x60203192c06010609030f0c080303040602040302010f0c031e020a050a03030c0801080d08070f0201180503180402031e06120f01060501080703140114030a0c0b04091b021221041101 79
    0x940300d032006200750300b0200041002c0c94210320b5040490b44d000024001215250074052031200160340804a00e0000004010070405a0750081045e85d200340c8031440c0030801a04200c8180d4103500004000c46c04c101941601680910b001040c6048240304840480d551703582d03030f5814001c032130f10300300d010a49400c0741e14242c60b00000c1c0140540341140042c4044103c050b0024603400010f40440d05002c04505a10407543c0f0030340001031101e100d1000088180c42500e05a90740b540300000d072025984241100c0003582c50540201c0740916030b00320070340b00f003600d0030160f5024020001d442e840c2e001118040e6506d0303281051160703420b440700340d038000900e0501d00400035201200042049003090304d448030845400c0c43c80d285560542d90b0300754602001c03840c0d100201e460010403e20150400f0002c80300051103104400041c41034070150b200602810507a6101b02c03488600070265203002d03820903c1c289400c0310181e0098001c980e22040650071315440c42100d04201c4c0010b44080d2000d0680c1792543c1041d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369262104 1250 369260854 369260921
    0x212010918030507020d1e2a05060f0c0102041733070f0207050d11210a0f1b091416020703031103310504020702060706020319 56
    0x2003210452a91281c01d1680c1c004043c0d220f200c4000388076100303110b50b1344180401d481e06005160031a071102010329890303040010003007020070880c10800031205610040c20100341c50544c00c0b518044d155030304282960144426980010000b140300d90b42c01e1200140c6084514001c1800e204644080c0c807140d00380d440c000302c00e005100e1401e8a0500301c20f4908041542150041d40c3c4214249009551840c4144e8100c0c108030140e4001680041c0d441d8542d8140840316102c3c11601000f10748845401109030038400070b15690100c4408147c014800c1480480c11059485c09001e02c1041220b0139901c0044a0400e50049600700b1442140e48842c04400900c0c03202005411806400d048100d15200c1d0100a58a00781408018108080000d400e656680100280c8807909100c9890042c4100e1409050300246000194a2400001d07450001000d05161003151407171030b0007600041c905003ca072500806544007030001c01c1041b14450038034104114611a103030b0b03101c500c1c883e4295000400c079102181c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369263354 1250 369262104 369262121
    0x30a1506050409150509060603101502011a10050f0a0207030606091b0e030d050c0307081801020607050a1d01020a050f0d03110414041e09030801030201110114070302180402120109 79
    0x1070b0a200c14148065030395003007802d80c006808c40e01541c2c0c0b07948200440e14400c0c0d16900600e1139a288403015095541c041d0042c58a0030012841600b86409110410118100c240e00c0b040100714100324001c405941c0707800921541c51540110742c6296500c0c5c2c3c49504450342988014000d5035580408400d489143c074100c08490304610b4900d480d0000303030340020345600301902d801c0280800000c0405030410280300b5501c1c07090308804041d89984e0030351400343c1c2d08070b407980e034243c0140912030008060a000d1401e031180704080759a1100d0484c42902003581001080b510745c1e06621500c004000001c60403c039000b41203503082d000d49020500c0c500040c081c0d85408000c4200b880040c0000d10204014172529204080202c07004120000e41144864074820059a034001840c188407604041c50b4120f841c0364102c0e4400ea9030031071507070041e003000d50032164140b40c080c0460092102084000384a0b4020f05049480d02403240098240f0304005001c9030310020680f4284404000100724802c0e0520400c4c69 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369264604 1250 369263354 369263381
    0x40e070806030c18070207420518060408030a020f06090304030b0c030c16080c1002071e020111010612020a0b0309150c1c1a011803020402030a1506050409 68
    0x85001000e4001104500090144040c0c04d50650002e65075074420000c080003402081542c1448d01c81600c00c1d15140c400500c98141c01e030b0341060407051400c0b00c070369401c8000c02590340d9650800341003180300c0070390400405640e684542c060102064007641032008051451080d001400d00d100400c0d03407503007410030041009a03590424071041021442030101c29a104041c40045a9640c1e01e010014032280038002c0380c20650195101e422081210420050003240040d0089509803554100d003c02a442596402480d044511340c01809040740a441003c50078030504000082403440540c0d54210b80340f642c440410094000c2403803041d4106803000d4400782c0401d000003840c40c50004640c80c2d4501408098040c00394103840060b011006441c00e9a010b4040000444000718201c81000081d02086e00d000d80000560b0410500d41c1d0b000f4648030120030710780480c4d03214031803964007040000e4000070f103813000250325a180c15a0301c0ba0a0703c03140001c0d007020744803c2d03111381c108242c0342c0403511032040303000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369265854 1250 369264604 369264613
    0x714030301081509010908070c08010b0d120807020f01150303390309030506010b07200901051207150801060206010e09190602090a0f0915151b0503040e07080603 71
    0x400400030030107200c24074140f04626003685a0040030b50061401500c0503100d100c0c0460307084104045c5101e03040031210003c00a00c9801d0f4140104500b038000381030010b00d0f0b610210324061a283c05542c0c466403002d5540182d840072021022102d0954641000c00500001045001c2c0b0170160482c00b078451001c213001400340c8401d1030844031051035415450713060400000f20750600c101032060820001039a40304055440550b515510703195550050801102c08409088800c041c54212080305403c004000b0082140769180c0300502c01140d074643c0c01040e19010700500030030540c40c583c0c103900c00000190b560f017005615200c0c00034141141030700f202d480042d0320b4050200441e000200300c0c1c1c1c03c090f040c0e41c42d0300e0005c00f850000000d00c50703600041d40080541d003000946e0004030f40358800301c0c0c03095801405104842043c85e186e00300140035081042d41000c1c2e000c400740b4440d803d8103088642040850030700082d15168589181c1040c0e0110098803082c200300003803180d10080917508070400b0740c01413 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369267104 1250 369265854 369265859
    0x30f020705030912030706020d15061e182102030c03060403020c0603070504090507030905010b010f02031c0212040506061e010f18091109041b091503060e07050714030301 75
    0x26902ca01c07a03010418030400d9400300101c1d580b042482103943c111380c01341c011960381460341d0440020b04040701e07461922540ea044005489400741000d252681010f55005e140000801015200044a01c0f4289000340c001d038400b003440824080c010f401c5044840969040301c40e60320405161002d41b05c05035002e500311505000010f500040d250158040c212403482c0c803541c0d40e81d000c176a80c3c09a0303031104d8030030340c14031042c040410381640c4903000d4540905c0007030064180d2000192130101403000f0300700050b4010480209840e0740781f00b0a401580d98000c01502d0074140805100d8901c005035400d84d02030300f080050101c1490000c100c0c01e80c038101d0398006d20308544814006805040100301e042c043c015180c42c0041300c00e80d06032144000c1d0220400401c000d145480103000c060304941d5295000d18608121038030f200c128555140c14480d090b90381d001100c0e0405038144280100d0240d84420700d80c81c1c900c04154100111381b80d52196400c3d07a5a15102d52590400c1c0c1240c0d502c900b040c0c0b0141c3c0003000107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369268354 1250 369267104 369267113
    0x50102092701030b0606070206030103060c080603120406050c0a060c0f090503011b08150a120b09061012030e180f0604051504200a03020c0d0f020307030e06091201050601030f0207 79
    0x1c00d0469030481500015592004042425407160480080d40010004000300c01c100c82c50313000c8010b02805660300c0e00c25594240c02d0503034845204415980d85401804200700051240d4000d10340822400207030755150240b0f6507002c00b6101000b66210205014103207003d2081c0e841401c2e00000e0500b10000e1019290000c007807c81482e41440e44820003100e0f800044825505403003a0060000241210400560714061a0b01030034100350121050f50140c40450104080098001e0150a0700701484055524011281ca8041c062007400c03001c1c00a4544a6070301c1c0d6451203081a00203899050715599440c040d14690300c0d0b1600204920b00c96454007081c04001a00f0300915039810310f0582d00091060303111001313080c00c018401e1881c8a003c50003e002482998190090112940300e0400c5441c050003100c0107607103010682c0701d8180182d20911000010134840c02001e041580041c20051038500e80300e01244250b0040d00c4025400d80d101d03018007005e56030610500b80c045070840011801c150281c1e44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369269604 1250 369268354 369268429
    0x44112070e0c0901110a03030c0201140907060807020a05010c080604060e0f04060b0a05060d140f040b06040c050c011b1b020d02040b01020102040e1302030c06040305150a06090905010209 82
    0x300520142c03010403a608242d025004030152009190704032080f091480c54014081e2204108400c019400c000008010f0640b481c078950040c5505009041e0044c2845000c50303550304014030510862044121130741c0070601c01c3c803d856030009240e40b02e07450b0f4500842444155481c0c0d42c416600d00c0399900402c1500c500340503009400c103912100100702801000000f0b081024145c00040c1d200380005107000003070019921080d04c100c00103003c000345540f200d07451001154216070140007111840b0000b01c0a2030190301c201c2c0c4481c6541402c41c00c140064800b6401c5901441e09644210f034005c2810110940010400d80c20035400300085030070342019404a480e80b1003403880240501d45528003c44240e0007074055402074103109203407880618003c412055520503042d803d81c0240035200740728002d8104281110240c03a044001403102e01c031a6078560500c450014901d095156403004007160301c803110301619243e00d0081c1c002503251030300e140c200400300d4600c401704001410b40c003918001d0588078aa = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369270854 1250 369269604 369269611
    0x60705040305030901030e0304270b03030403020d030c05010207061806061703041413110315010e0f1e03060a0e071212080703061a030a0e0c06044112070e 68
    0xa004150804e40d00c2001d0319500450f00503011aa00544801c4112b20300b40c00140001c004032141805109180000e06840340708900001c1e4100c620090186c0100f4054500c1c01c41944c4200300052520ba00b54a441c400c58000704000012039044504a0b0180076841c0034410142c01d20f6034884000b00000003505680744140e1042c00d41d080c0749900109130650307800c0740c0e070301c044001c82d1028440c0c0014511580c030994000c40e0343e080b5940c01005030450750b5201c0c00d4000f03007031200a41024110004601003202003004050180e1191180b1104004603443c14485140211000c1001107100d098488101d07040c101e080d080400d201d1021051240410300d03a0002c041192070b00e0030403103800d1721161400c8010b07048035001501c0c3c000403046c0c610b078004955401103200e1108460b0400c55005c0e0a08010307160b10603889081e0f8400f0083c002840003e0394001c04142211401c0301c4144483d09014080c44841d003424540403151b0081001001e441c100b410b010f40a0481c0705020b0070b0030b541022882c038603400014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369272104 1250 369270854 369270857
    0x20301081626030f0a030b13060503060f040f122001110306010c030203190909050105010309110f0f040e0102030a05091504030e0411310f1a2109060705040305030901 73
    0x3202c0341c145229003402115032000314500a5555140080405400380125540060060b003002d100810791000324494603040c0e0b04001c010b080a9100c81c101c0e503c085002800030742d0810400008134000840c3c12340b1404440029032900c496400300c40701c0300100c101c54034048641990400e051040704000f9901200d50001090912120309030060074100e180d1f000768204a61211000000d0000c802d070890820310455000e038605010f031381c7c4c0f9540110299120050003c0404400421140644c544002d00e80055400a003284202d840080001410754280307080f6032145950000c02e02400ea5807a0240f00e502c24100d04c0244170400900c4600401d1001c001c0000e000c100c1c081c00020000c4d0358a401c0000038840c020465074440c54001d0210801250320400345910f50b48200076964205404c00c0ca2404a0b5002d04880c4602d074606202600c001c00c207903807a8282c1840400000d444d5210f003030b040904007405a0407403585443c000c0c050503c1e10201030710140910006200801c00988004216480004203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369273354 1250 369272104 369272159
    0x61a070f0f0c0611100c080402040b120709090c060201020906121f032102120d020304021903050601090c020c0901050409020102150a020d15061e050702060d0203010816 74
    0x4906101c0030100d041900141540044480010f0300c55010000d8480c1c900c50006450390000c41c019090304a400410815005c1590400000c01516050f030007000030354001341244410482d03007403446060900d190031100003543d80d40100814000d402c502140034200038002145048120400200a400f917400000d000c009443d0020382d820305070015005100e014001c0e03503540603440c0c0ca08a54000742c403582902c22a000c401100f0302e072510019a6001e000d0310410032928016440710130101a41c03004000342c0e04901a0414000300c1d00c001c4a00100540c0580081c010550601c40c0303900540b21002e0307907441154012070310749625170ba0301e200c042d0441d24111000901c01c0d21601c0180c1c01c03c0c1704403200b00c5500001c0e10400429600d5500180314450802c1c0301001006140a4001c00034125401404c00040e042264000c0038a01140300001c2c2c04581d044c0304c1d0411030141e00051803903202c00320b042000c640103c010001d003c410032140722002025013070004170310300f454014568540c0c0c000b00418142c80 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369274604 1250 369273354 369273383
    0xc140607051606150b12101a130e010b09012303011206180501050603120f0406050a0909092103090f08030a0b0406090516090806060d111012061a07 65
    0x3d9a5128444808011403030b040030a546403140b400540040141c0e00b24442110000751001c14901094402c1c1c5103403810705000c0507058002030b0007580200004101c00035440c1c9001c1000282005100d00074841803500c82d41c2d40491000040060b00030340440d11449409400c01403c074520b6400f62415150710801d013003210341c064208a000b03069903070045008088524400710501c801900f00b548204410307001c4550801c007192a800d0301d486181c0c1500354400003070009004881c481c07001006000c1051410942a07512600f5104c02c0301d03501e0904498500b14016003032000d0703030342002e120803e07071a60400b000014400c1d103038074011409026000f0114070001000442c000d1250740040ca9007030010f041001000e840e49800c40042c401600d11001607000e4800380d09400c0d22400c045000d45102c0c3d00581005d880d10010310044402070380b422a01f081640000c0d003140e483c2c141900d90b01c0e1046130384040175200f542c07444104444040e0000903000e0181140c400405260400722201035612280100c01d511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369275854 1250 369274604 369274613
    0xf11031c0f020d051f030f0602160b010f060815100e280306050a09050d0315030b0a020306040615051e090909071d1e130605070c1406070516 62
    0xd216850700840c1c404202484800c50540c0300d03c0c850a03031008000d92805141070340e40c90512880c4002042e000c404c0c41ca1800080c129005411840703020031402040340ea0f00c0d0348d5250f00e403800b41c00025060301600340410805901403007007900503050701c2402048100c00400b0929401703072481120240030007007a00300841e03200c021215803c400f00d01560003030440c0f00da201e00c07441d0002d4030055688604205c0810020741307161003000038003a44000100720800500b00240c0113010340d01c002c40c00b01080e1071800408681402001445520031040050380e07032420208000071580240c10122400c81712540d0140041d0300081164598001d203804480403070300006149000348a2840e5064101d501d84c7c0c02e0052440c80000c4100941c0ea00c0210b07803004880c00d903070003072440c2c40450b03005003003a815001001d00d0030441003c0580014142040052095a540303444094440545440001a402101e01c40603c60012502030003542a03002070305160400f120b00500501607008030a03a0441a00c2d208070410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369277104 1250 369275854 369275861
    0x30c05121509070e1b032d040b07020f0a32030c010c20030306040c030212010e070f020a1104020a02031b07061101090c14030309150a0f11031c 63
    0x80501550310128508142241c3e100e5034070f4440ca0a0030f80c00040880c0c000080583c0d4094550354070740700c15003980c0c0c03649117040502c000c44801c115608110341e02011580100c0d031320540700d5409000b00908074200100d0003458880c1038421940b80da04054401d80000d14101b050906100d59102910326610601e6104810407603240f08212840c88001164034010b10190010500d22200e038461a5414109242540280ca29003c0400c0240c004000164107850035034011038403445149801401d0880e04030b18081000c400703812044901026004010400342c1c00b007044004500a07101030401845255900300b0380e0b500740500984595008500c0894451082050342c0d4450024401c40090078a03141d8025200d508901409000403a4110304400d05401400741c003092035400150100b80c02d1915032014866800b452a444e0305000410411089a9a540c140c00491860540c09130b62070b1076045002c2c0900b0aa0301043e814000301c2c1d002c80600d001c0c04010358112103c010f400b543c2954150303a802008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369278354 1250 369277104 369277123
    0x2003031606061e0302011d060706050109060b070804030b0919030503070e010e0102030904050604110a120b0d03090b2d0702030705030f07060c02060705031b060a06030c0512 76
    0x14400461052400409040e486004601441c010080141c03501c0000003e000d20b110110002d00c0c0c408030420040d449403510000c02c4000d010f00100342e2200600144207070744030000a1310a0742e01d550043c0003c5200f8881e6274020204c00176028a8042690350306121402140300140140f040c4900141c00c0c3c4c4806e004071590b84198015002094005180103031454006845540c0024440b1907000d0880d402760141c1d141040c4141c00550600303044404110140ca00206183c0c1c0042c1c444003180281241c000180602c1c622980b2030701900d00251314042e044940707100104d4460581d98445002003500030780e0540a5900d40e0171690350f034514502c8144030aa000c00135602495451441035040c1412500c0030f0100b0310302c201c1c1070311241c5582e1000c056035104c0d5440411041c1d0032481081120501400103500854400f4201e5410076076a912a47d0071500b2445014002d8041b05982c6820a5000d12405500c6010090100092400c0d52a0420580010f000301c6000d403051100740320001c041001451207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369279604 1250 369278354 369278359
    0x20f0408030a0c0507050306011d0907080f0a1104180f06141815250c02060a0e0a08010e0a0605061206041416080a0204020915030406050f070e030a20 66
    0xd035002d6a1a000b80802d500e2901641ca070300030b9040c04201031030013041080c100c0d032810344281c4d24540c2c044034a410002c0301401c024a2445100000104050140450300d000c502d81c00150020f1000d50401c440760441c800a03a43c802c0d460241d01111072401c007540041034541001400072008007900d8107900030040d401c008005140c4090412800031150b1600441000650050b1424420101c2007401c1e03026090b51280b88138103900580500b10310003004100c0c0040340354600304c0c03214030f8550041012940070300e407500300240001454660505020b00181c004106900007004000014130000352103003880140207002c180c036078010a030107a45401da100c202c1700b000002d84029052500d07056501c611629030b641d40e140a02e41c2410169107420800c42d00301c82034070700501183c81044c1e003000025808030300002d522141d103080940000402c14099441903109400016907030a15880e569590070004103032904110521071881c10f642c501040f80e031800c5501410186460740084e80910114030301803100d54 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 369280854 1250 369279604 369279607
    0x309020109091e11180f010c0b090106091b141b010f0f05070302070c0e040221060103020102100b010203090d2f040b040522230a020f010302090a09020f040803 70
    0x41012403c0701c1029400d40740301d90820144650007544003075400b504031410607900d0b011a442e44ea07401c041c1c58942007a101490501c012421654944603902c0701035594941c40c2e0742d100d80030b00950b400740c4100d2035100d1000d00040800c819100c0010400000b502c50f92021220104041500c0000e10070056040d403240c10080c00408000102c6a0041c030444200002d46800c3c4004a40440c0c043e108070b60206400234591401d85040040d03881c5401c2c8003400c1260054a66001c541c043d500c1940c4026000d00598050542c552440c0002403415540311601d9203901c0c6401d81901040e0380000403100302c0141038512042d10041410301400019142c104101030b81480701c40b5280c6804455088022060125401c1202d82ca42ea41440101e074401c480300380d84d50200031000e810001c0008034502d4860b00c41d505802000001e0b51006107460301d08407400c40c159110300d40a0007103150201361803510320004c1c60210300300f0541d0710000e0103410340d9105214a29a001588400c03200128044501809200c070450303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 369282104 1250 369280854 369280871
    0x7230d080a1404150e0303160b15180109150b0c010b01170103031b08041d01030501050a0c080705180a0b0702031605102601170c030f030703030902010909 68
    0x40e4600d910180d4000c0001d1107880320780c0070604812054409460f0201900c41e030b0100a050140c070132810880c2170300d134075210600420940c03c8082c802c498141d40319503035241d064141000c080091b28034444207140301e4a000400302d202c0d4a048103031203044504070f00c0040741e41d1141d00c11401d40c0d03980c0c82c0c20082c04c104000804030031014054202d1000c1c0c40080c0e0f1380020220400400c440341070801e0200400045209a00002c0e00714000c0d074064415000b81e00c003e103000c1c0d40360a010350014a480354040080070358001001400420b00c1003d85c010280c040c00e00540ba03803201e005000620044c4660103025000c03c4100c0304401840740804050805845840101d40300d40800e0854cc0280400320f1180c401d1b007460b00c40100e2074903403603421110080c0640000749280c0d0415502c1d000190100f02558001c407409400144201841c64024404030a4501101020004213401c00c90030130515070281d440001c510000030000401c03106515014503000480544070f00c012aa64107066105a4501d41440b420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 369283354 1250 369282104 369282113
    0x2030111180a0509070e060d020a0306030b0901090c05010f020708061003060b03070317091c03110c0102070506030103060c0e10020d08060f0108130201360b090307230d 74
    0x805012510902140c1c0c003891000c20004071050a0060701e0300211a034000c5a0400d00074a16000b110100514040c208009400740b40304036080340c1540704c002a1110704c204240700554021503002004c4d00d00034044045142c65400400402d481082c3c100032909800900091080c804c0101826051007500c0150403c1d80c030800020040e40001d1385e00c985401c928007003900d8005005412130354484500c03140a0b9400c80c0c02400c1d0b130065802c3c55041445c034a0041e500d440d40c0586502968840d494200f005440b10076594603104100170401d0666020b10400e000315901d40c1c080e00d0459600010102e0312000c403090450b6480080e40307406802c82c144000107100203402081004030407820b640d03a117940d41c3ea0a810090070444529045011841550100700900e801106240c403250040c10100081d6801034000100d10604c44400c3e41d0560700a002513810b0740c400d806490003030400d00d101c47d062008a0001a448a00d04d02c5011008003400a0005c0000c800c01e1a00d458113000400700002031549080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 369284604 1250 369283354 369283357
    0x18080312091006091a19090c030b040f0515040c0507060b06040e09030331290c09030f0c18070e0a06030204090b03010507020c01050c280311010207050c010f050702030111 75
    0x505172240101e100349480305040414414800f14914003402c6122071400d00c6070001009414102410182c941c03604505513110b6001e2161000c000d810002101d150092541660300300304a600d61180b410310b0940070540364400280c4e11155003080002070310481702000070740c0c0361080d54008844110b0642c00c011402201002862084081d401c2d030038030707015540140030a101c03411404070b20040740104c10b41002c968910000c0b088a100c030140440e503586440d0411141d090201c90402d02c5410010360502e10342001d00180c841410381000410740402e4100000383d00c4000720858815403060b400010388080d00c1403614901041c0c0107880b65150984528005000c0e503c14050316802605150b03610416050500c03a02d03100d0b85081d0302400014014800444c0c980d8000c10340e5403081d1080d81000400480c0c21004140320107010b0341e031404010303620b2801800700e5091020900642c1d1040c84030760003044003c42c03107151004003443c1265501e051000280c0f0385014021010750158030b0b04480e800303403402a00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 369285854 1250 369284604 369284621
    0x10306030c0b030912071e150e0309150301050907140f070605180a030f030c0e030f0a02030616080109020a05040e07030b09160c060b04020415020705011808031209100609 75
    0x80507200300d0f08100f103d1744520710600074010412842d481d4400c269403c4a0621302c0040e1040070210844080581c8010030b540e002c90150307030550000212449603250400d035000c090341c4989101400c40d85003800080d40c050b8000c280505001007200f03c842c884000404841c9614600400d4680b10b02042c18100014407084809041204064010030013089000543e051841d6169031080d050307040b0618110040c04c0860055010300c1110f44a8914a41d4180301701c0c5204122000201552025401018604503010f031012040c040024440000300f540702e04000d05460040c070002d69a00300c1510701f15803d100f0303540110304112030b400c180040300780d0680225003500c80803110300d45c441d00c1d032070b0000c0362a030403400f103610100c1c1e0519a1140010300d0b503003081d0b2050354000c0005040c969240b5500101840c03a003a1040140c0005c00244041e60f000b0810784038050a00d1001c92a0380d00f8007040030351302d1080403007060030a1241c10002e84500f200f041408a000c500380005e000840d90791500d00041c1984a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 369287104 1250 369285854 369285871
    0x20f03090304140a03120f030b0301110304021504060903030e0d0206120f10120308040203011404080421110103150306020d0608070801020c1c2d030c0c0b01050609010306030c0b03 79
    0x1184080c1d0f245802e1241c98152034115011036409418254291540310000c000d120178503407070300102c8a1a503002c1c403450010900901031180c2d40d2400d44100b00c071203102c0340000d855129040c801031041580c050403541c10380e0b6140c02d1404030400380400203229501034601c001c5d80200002090101031081d054024090020141604407945807208500c421040d5401149041442003114901181c40781c070f40140c100d800074000159a050341c1e060300110030b4044809550414000808211800b003240c400503031980c0304034000007024125074070f290208a481003500d042542764400009820f074407028031401540e02210840d603803180101c240010304068428401e8601a440c00082e9182e0103008650302d0308070000140c20660303541c0302c10071203000e411007a100400011108022061030842180005080c0d480a8030000c0d09034550002c0603280c0104a000030052003030700c00070003d0510703040c1c54151582218410b4950703807410300480061450343d1010307050b406040310009072400008001c0d40286442d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 369288354 1250 369287104 369287129
    0x90e010c030b010807030f0212070e120a0209060108040501181410050105090f0714070804300308071b1b0b040b0702040b0f04140105030f01110f070303020f03090304 73
    0x100e90164121507045024034003240c070610000e12070f140300e40e0040c5941d0382c034030000500740054002c1000c0500412141c200c0411790100180e100d51904080065444c01c1c480020300c0b24029980c045143d40d800984080e0505c441100030030204402900b080245c2602c04455030088034550504618000c0200c4c4209118000c058a15001c0181c0d4090a07041c0d400c041e040103200d88400400c0e110201000300a501004000780d0040711010517030303008000c80d03806101240e8580d42040300011440c1c1c4980100c100387d00d803c2e40c130925140906094004041c2e01418991038640d9602420380f4240c500d54001c1d442d000050181d1030800c801070701000c41c000c26400701d0119450700c485168020340300d0350142a00000e4103010640040c5000e81010451030005041c08890b0091030f4089020340310b01078100c003191143d0b28014000c900b010881412126102c6c0004c0c042c40b180c140007850584545144c03801410400105081414002c2c0c048410144940084a079245040f0310b010f40c8982050054a00182c0c1c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 369289604 1250 369288354 369288371
    0x20c1f06090b0a0510030e06010f050901050d02011d120a05011d07050a0311010e120d390212121c090305030718091b1404030c0b0c16090e01 62
    0x7242c8510998654003603d02000c484c1080c04110844401d4000142015115100945920b00620200340200b09000001034603a00f40001c2141c600e4050f003000f030044540c042e8000241c0c0e403010031035141420841c0401c8555540502180c40f00c0f00200070400c892141450080400c0015840248003d408104141001000c0084a43c4550307140c81215407141c06071800b4004911008041f60810005040426074581d00c030000c10512049000207107443e4000c1f2801e0303203419400c0303681e41442000a00000050350126140750070324504041c510020302c2c2c00302400d8011511a100c205500d496000d00308d82e07980d0008518200b45901680e0400105011030606942c400650f010300c2440c20b500d9150b040c00e55454140483e441503140068008500c091240003649040911030301e070310b1088600c8061505c0040420290170900755140f0011146401c210030404078074040f8210080d140d07807040303265948030301c503100c2c80ca02421040c60203055801107900081e108100e90101141a02102c002c1c0507010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 369290854 1250 369289604 369289619
    0x93219110a080312090106050307060906020c0301050402012001060509090102071a04210203070c060f03060605030f0721020c16091a010f050c01090f03030506060a02190303020c1f06 80
    0x50803880b40340c1003540180058a5603511a2a54560080c403200c00001e00715580d1002030715100301c0750702030804a40300c554244003281c1d040c804070b00004025002408641890750000349544494141810500491201c00248800039001a0000c01d0018080c2115081c60640300f4000d41c1700b40e0b400c40704035168600c0c0100102c1d44504003846941c0040400b01020391081800317510b0f80308201c00c0808c50200b08039020000d80806c0900c03002d80020340e0394000303130600040b001d03044560f6500402c05020040c4200b0101c214003440c40e540c8400759241541d00d01a0030101c1d50300c42c2c900d052290b851580040f85d0f980c001000003d480c4602903002c5120030000d540c54441d001103030302c0090404030b62140c5215890039035000e0402904900c000345442032410b800303503200900b100d04d04003081f25000c020001e03844c02d066150098640040048442c1c5151203440b11000c0d40e1411107c10320f085420b8600200005d0500a034140e680120926055485e6040c20306200b0400c0c0b0048803100f01c1061610a01040c0130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 369292104 1250 369290854 369290869
    0x101d0406022203111f170604240f0503011a10140403241a04050705040506040305060603010c03060b0409050604020904021c051014060903072105010c0309321911 71
    0x203509506c608190110010214118460050042d41c00645039000585d100f9460081c42d07030080444c000d6510790a0424140900c1d00f00720307a1181c0d1013030b818401c5446003107c01440c07050140310211001300350300300700c4541610300400b840380b903405d00803000c00d00009100800084120078805181800002440151081c00700c44480c05400e0440c02032010101c0141090b6018540010310341c20b105041540d2140025500c2d4031a0b04121190b400040501607607007070034010300c0c6600200d801c0a000040c01c003201c2482a0181d445008121916117000c21900e03100d0307030b04980c03001350050070655580300162118070144c4081d0011410003031030b0030000380070810751083c40c00a548205100c1c40140c0e40400c10004250810301008e5818081d080c000683e103c2540d8142d40b016000907459111503501d805c05070b007100c81130120803090500f05203c5e40300140f034011401900908130325400d0380707062802d070b06035000701c2c4207038281c2d2640d01ca030f40c820192000b10301c0c6910031507611413540c48134408000c1c030601641 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 369293354 1250 369292104 369292159
    0x12050c01050406090b1e0a021b181f1e080c0d110607020105090901030f020102071502070b030c0c060405010501090f0b2b0614101d040602220311 64
    0x191501130034811171008000a1142008844550910300c2d49404018200d522000840c00548d01403100780601545069010701290070458203040442a1200c2c9560075110081100c00303a0700c2c2d40c402d0840340070007141014029001c0c9400320009908018500c50700f09a442c000c4e800c070b5200c1c11000c04001c1c549001a031030380591000110704400c000c20107000a03038000a00c101c0c184070051010341c0e82d944600e900b0394001e50003007480200882890002a0500301a030300b00d600c6c2c604040e900c0c8940f0540015608003181c5101c15001e0b41c0795508103a01300c06008908050440380031740005e10046c44015084941030f00d078641000c100c0703800d610400f1400c81d12055101504009480a4400303c070b0089403d034912204500520503082045075281000c9540c0e250820b001541d03928248200c0c00e190610007005030940340c072485080500c050b815100c0c0d16000703100500e81c0c0d40024518070040c100b03e0000514185130000750f4419034076854000c0707240503013600450084800070b10744280f0140240c000e424 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 369294604 1250 369293354 369293357
    0x30605070e061804022a07171605010f090801090308060307080106120f031b050304030308100e06190f0803040312050406090311030a150b040608010e12130803030112050c01050406 79
    0x1883e003a030002d000103034220301c010381070441c042c0754400f44000d040070240305c0e0880d000340581304a508101032042c11503440c81031655103504c15021955200030020445003501d00c242400c0329190ba5012048035480c506070440b001c10350814081c00d04054011140c103000e0a411070503185c065485880203822a0503520070910304c46000d0380e46d800407580c40e10001003598020b01c0c1c050400510100c80705104440c03e80b08480551000a04000341940316003203a401c40213420601003403910300700c005410340c1c101400803071145038480d09404503540340100203001000c02540189106940e100c0c03581d16500305104c103441d144115003200b0003451007a400c4800b5640700782c9510040d00c0c03c5841d40083c507200d8402603038151003040080b40c0882c40052003200c4075843e428022030881e4440e418802039625a07401044141e0600c03081e24403004003c84e0000780c0c1d8100c075405503203600aa60450061001c5503020030382c0c9010000022841d16030791201c0649840c007900884400c031001000440b8544614400c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 369295854 1250 369294604 369294637
    0x110103061e140d020d030203120606070c170114010815130506010605031e0a0203011e0b030c0c07032003060c12041403070b0a0b031506031b1207030605070e06 70
    0x14841c010982c400d050350140419004083d161301040c80c5458841c03095006d0b0b403022440600c0802114004c991207603065600a040c00b025580c0c90703100000600030703a13040c01110741c000355860a09611021185018028411107940c1d20402d881e01c94101000450007542c0000008005480d108907641c40b895200000344440da02c1e0450468294001500034504080301c02c134421032044404a016000d015003100042e030b65490100561b24803000303515902c1a04c50203a500b00300c40e10840c000c1e26804894503a040355030340d00c602e40c170320b00700741150b08002c1c10a03030260188400d0244101d10640340050580449101d926107065948490003074a86007001810301400140c000303904c5080e8134840d08800c0003204d041c56015034440c860300d1001c03900b44a40540d600545451031808008400d00c03998100590031b40b50801401094a5243c441350041056078481c502c0c040b00c0d21010301103400b000d04201620641500c034035040001d0030b4152800000601c8410000a95103000401ca800035100300c0c3c400c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 369297104 1250 369295854 369295859
    0x50c0c010b04020c06060d0c08010905010c03050105010e0102070306020d0905030301080c1804050a11060f030f04121119050c0306040302030a0e010801150c050f0703060212010801060f0b090a0b07110103061e 91
    0x7c20003983c0e042040780e80e14480c1ca800074070b40b03100f40035885039503101c0da00216844070381840040886505074007960410401d507c0b403112076600407588c1c0c4252070700400c0241e90344c421104201c010340038800c40203200744400400005c05035804510b00c1c078400710071035071858030704040b1a120081c1002550040e140c0d802900880001440404840c110000301910041c200200640c4c2c40c40c0c590002c0300c5950003460010204410032101040150600126040590302c910806900d1ba079682e025065840120104484440600004000d07c00043c1c1c070003411036096241c2442c00a4607a00180c075800045000425004c1d000d40c02a04401d06a814024109140d009810000c03125800000001e9500b8010040c2c0134040307681c00d204404c0174500800e005603880115100584030014140e100c40000c0e45018020302002c0c0b02411401c00700c0e803410140304d4a401c40d802c009004c5508507400341c0d00d41400042c1c0d080400000d440e0300c0744a42400d80f010415541e442c0e580940b0400c18400f008008130111809 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 369298354 1250 369297104 369297109
    0x1090b07030228020307290a08060a09020406020312190507090f0902041d0415061203080a0e1c090b211612091103190516061704020d06050c0c010b04020c0606 70
    0x2038501088528a5040c47d180c40c00000040c44d80040700030f03400103000710104251408c04410440092207030840441c909071038481d00a440e40129888014200b0801000c00c0c0c401626070034500c40e107150b40608100504110700041c00c192154442c5517103400440200060f9014503200b50f904850518600071310218004c41c2444404500400c122222440303002010380b841071038400e00740941407640000200402ca820007601e1680010b251000d17003800c000030100001000300703500c402187e43e0480c04000983c840c00c207560b4542c0c01c3e00003000f020808178040100c130b502d031074207010f0780e102a000c100710b40e8030740001c41c3c46842788002ca2080459501007205403440e06030741c400c080450003070b0f0020442641e0780001900b000d01e01c01d801070500d030a4005800501c002032082c084076405242c03011080030b1a00c100139214014001c098002803003418001130640d00c0d24003014108a03480350041019150900700c01205410201c1da03040c0940c0303480204800303410309108440d090f4403c44010120355945404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 369299604 1250 369298354 369298379
    0x605090106050a0b0703052514030a022b0f021e01061410080601050c0709060b0315010f021c110a030306030b090703030504090203130b0f010e070503040201050d0b01090b07030228020307 82
    0x71035490708d150486402c0c0200e000c040c2a540c2a441a1019558544001c0c80080ca40060500c0c10a020b03c400f00c244403220802e0010704403a80f8480c10241038120f00f0b400182d0400340129140c034005000c25134007c0b840981907100c44207a440c81224001091050307000c0c4000240e070342900d14049500240030820a40c00b88025050203520f8400316034980c1c0d124003841040d680540c4c050b0801c1d002c04014001c82d41244240d40c10300c14428a00045214103101009558984002c50810301c803281903008000c06110342c1680100d441d05008440740e4000c0b51500500400c401e2005039161841c2c2c20109006800100c0c980e02200c0d0103507502c030700306818101210001c1d80040d04041900040780503403000036018080580c455106030071010783c0340d03241800791000200014020b004001c010010040140c2e081b6050704d050304c4110100042c2c1c0320000005903482200c50b0001482440b01051180426900042e01140b622649081c00f11082c4150040d001401c1c003008020b40c10380000c41c05008800c010003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 369300854 1250 369299604 369299647
    0x824060409020a080a03030b180c03040611090d0f170903030f1b0601060c120206130303090c0305030f07050c0d0503070b04051603152d180605090106050a0b070305 72
    0x2c0c60550141da8844d0070038034003442260100c01084e19000140c015261003e030000101011203030b000d1061a02c000707120110f100041004121b0307582e420002c0348102000c41607403c94a00540316401c4450300c0e09000ea0f0529504008403010107558480c1400c0d0669030303040d146403400140040d4141810b582003044d00360401004126255101c800341302e0401e004101702402003500c0e0f2650402c1d0070b402d05021040c0324010303262001b5075029900740f00c00c0500c4a40c461200c644c151074001803180b414904035000940e941d00103003070741c48003143c00001a071600c0000c003071851044003110142c2c1e0303000301404030340c10f240755003d40700e500203001c3c5801041401d4003480e4041d200790182d0b014a03a28080c00f210080c0780380c000b071f21140c00820360500e0242c0e0234030810421100388950311000054020640030010060040c00340345a0300c9941040c0302d01083d1a0003401e09034050300c18001850660141070007484288116407050f400c8040000786c0001c0702045406084d050b42d181c40c070300f045c001d1401c5c81141090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 369302104 1250 369300854 369300859
    0xb280e07140d23070e04110609040e0601170709091a07050d0207051b0108040c0b0a12050412020d0f02031207050d1503230307020d03140310082406040902 68
    0x680c0c0320b80000d00b512041800f02642064400b00d030003002200900e008982d4008149046000007444082080081405040c0c4011208150389a00d00404640a05800303040d140880c41048000304049015500c41d1140324110710403140115034032180c01c3d0540e080781102030402090340c1c245004c03e9041c148220b074030a24904240d4071303042e8410084001c0380e0009005440e59001090742d070791001c61030054031042031800d00e0601e060741050348078041c41420921a0080c0c54000050422580c1d0041490310b2125180301001c110a1802d820410702003281030a4200c014068680c0081c1c08601440145004089990065007001000f40c0c642c2a2040b02501000c1400f000f44150350100115004020300548090940c0c400d161551400a10f80306060041200e134203504061010f002d11300105481020f6011511303a80880450b04040e50a0380c032648a000c417040c1d0001c100301c84104018118070482d0600c508582c00c1406465161010b681d02d0070008403040001c0001c16950b00d400d03041610640d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 369303354 1250 369302104 369302119
    0x612011e1d091c0e03010f0506280f12020306010b04150503090a02090a090506090303090d080613060e070e01020a1a100b0d14010807050a031b030b280e0714 69
    0x803251104110f10914803650020780c0c1e204038162141428040c01000c249a560280954200380000501c000382710f030201014003241c0303d032180101d2039600c009402000d6489040c42031071b4031031340368040c9003100c8081a4041c0c401c0380000980e440b51036040301c0865010741c3e040720fa080c0c403030542120540d101426040d8280f0a64510102503544c0b07405050040503582c10006200d40c0a28195080031401000a0384942040c410040700395404a44104058458501444c242d5561000600b441485103920001d1903e89040132500d2080d21300164040c041503180c2c1c0d0f2000148600481e603941402900804200c42d80c146a91418040380442d40c10a850300c500c01c1d121512039402130000c4c1c00bd1805040000e4a516680924054615685000d1720081c0f000d031001605140104006421500c801030140070038100074101c5c060800000c201656002d01050100d080985500c1209408543d0319410813218101894501341c491158115507010000a4103280d80b40480180312094600d02c00c1703810010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 369304604 1250 369303354 369303373
    0x920271b09041103070f09030201271503140129030601030207060504060b01140c030a08100315090303050c09030c010f050d091208090a031403150612011e1d09 70
    0x5542c00343d40c071504850282240c9a141c042130080c10b9105181e030400a2054551003480035136485628440c80c00902c48000b401c4440c100c0300d000d0010b03055403149410a0800d9501303200d80e43d16400600b1001981424407010340d80311080817070702010b92030b0030070310f01c0c412540280d400000a8018540c01441410014142400c0c2c0d140d00c0b0a032503045404071550b40d9182e104164039070700708800c0c0309180304424655007420710324282c0c103a903480b0b02e41103441070040e4100000e24a0410f9000b110103154403040742001903003280c4004000d0040a01c044001c0b13818440040c2d02184480b0589640c020b0080007083d6190407000151040b10828440381d0170000100315000e103650141c052400d541e4414640c000c2d031884d041c880106900d0f07001d08110095002984890b000c694010503115542400304031042d075945410800105182c0d9031180340da0420300100b01e0800d0610341042c2c0724101ca40c840c0345e10008882080100d2000c0303c00e030017594100640090b031081200c599400c240da1101c40c2d9011aa181035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 369305854 1250 369304604 369304609
    0x703021c05240106030c080a0203250f080a050919171b0f15010e1302090c0c0f01020406050a180e0f07020f0a0201170402040920271b09 60
    0x18034502c1150b044104410720040d1025000b104107004108615040120781c00110b0028010388014025000994001c0081114008000c014801350301b44c03103688115015141e94040c3c1000100303250540880e03860380019000d400701d4091a131080c0d40d803402502c0e0503180c0c4031922141e0950006c007903503995a00340828280d0f0001500400c401140081c041034101d0910003294a004ca0080c100c0070b1503002110000c0c100c0300f00011103419229a421031420954600750440a00c91130074001a601003540001d021007105414018150013050350306541038002c60040c207900380d1160384a41b500181c41041443c011500c42ea1120704d440740c07118810040c0c00c0c1e8a10092107480d60a032590100030052000348809690100800008402c4240190404410f9600082c1210050004406a04061900290840d0b540360300100400340e000d203d0f091005414850403a071041020740c8240941c01103440c140039100c804040001c94841260b9614089d958900301c00700b481903a0541d020703000b00c18410b01603190f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 369307104 1250 369305854 369305863
    0x10603031e18170c100801170f0d11060609240a050415060210060b0417030903061006020c1509010c050a0606080115050f01091512090807020a06110703021c05 70
    0x10b04840f01602c140d4a580b0410900b420b6840382c4240c0f2039000b03542c404c8007a6401c200c00c1030469005e080748800700740c501015142003406100d414031f00d038010b00f41ca0310f0030704ea0024100300c88840090203c480c0c60380c0c1d8105021007a101030b202000030004080031882e03208807815039040f002501070103c20400d0b070f540e40820181d894200480c0d0001895034024400113504015030310851540c0c0310288041880d104101c2d030f161245000c1d14403c1d55070343d008480b441c40300b0000c45d500d44001804841306803600051203102005240030b0240103001d0300d80004c145240880041c0c412948484003a450142d0b2403006503100c1c2e1a59030122414003415983d030001c07034010300c12032005000e00000403d8081490182c10f22808150300003e21802d1300008844031641e0003541e000950300c00ca403201c0344d03c8000d0042a1109a50054854241400c1c0300085d410019240e000e0a0010303c03d98440b40255210201611541804408425181d00c02ea000700003500e04510401541a0f103103444081c9140c031a100d03e03080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 369308354 1250 369307104 369307109
    0x20a0801020703030b190b0a0306050909010515030d050d0e070b07060b010807031407080a0b060408070312080601080f070c080307080709060201180b09010212010e07020609010603031e18 82
    0xa80c1d40c00700d40041410303054000c030b150010341102c4078400305550361040f048000c80c0b4007404200003030218072840003600950102004e8400100b116611b032421828403406001700b01c50024070400140d40b02d201d681800214061810319540794071341807045901140d402084c07082000c40349485080800241400580000c056060245602003294280c0d600094100c54000e000c140400d817600c00c40a2100d400712034804e401c1042441c0c410a80d44400a460000d001c0c40164168450320014001404010000b011012648500c00110184480500994900100301c80003400300d0b034800e00285066201c007e4160307102d038190600b200d00f50681d4580d080140c00071a0f180011032140805e000c2c26540101c8058018501031000740300030704500310303141c201900342c100050005444102060350130100390141d400d5410091101200d03581d59004042d029035042e0f80000150081e940425100c00060240800782c90705500d511800c02c0c902d44d1166641222202d1000400c0980c10413130700f480d082e60005100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 369309604 1250 369308354 369308369
    0xc0a051c170307020705010e01171005040c05072009010e1305030304062f0412030e090a0b0108090307080708030a0906151707181503080f0319020a021f09020a 70
    0x2c50f0724102102a10300241600b0040c1404480298000580e910164854aa0101c5002c4203282e40f120142c1d40e0080316a90045640103051114940c441540702c8050034040e40100c074280118a2140710104003098140c4040760020540e5005200c155403080d90350f03070010741c100500007120403951501d60a50304252402c40ea082e45400d0301d5840d424030f20407460301312102d0103418000410304180502003803045110348078440c036198082c001410700030065420340510103800c00002c2e10707001140c0e000802d0501d1050340490f45000120301030003070000c1680e200741e62140509161142c240c98120030791300020001442140c54600800015009005d44462007148094984065050412584150148400c1c0038034a0344040801c00c1920049050442541da01103000904c2c0740d0345010380c01d011089500054040103001030142c1401403000011071040d0001c0110a02c103581e08000541a84290b1940d00d006030320640480e42c1c0803ca60220880c100784c0700d400081c41c002e007540801d0790304032194414031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 369310854 1250 369309604 369309607
    0x1e1209221509020c0c01140405030105040501240315110c01020a030c1b030c1403042304110c1510170a050607090308070305030a1d030d0e0c0a051c17 66
    0x8240300107086040064011141d0650a064061880c5680c0d0807010410604000c2500b20a62400120004480c040d0038007500a10141c134090400c640039003035032400d2039288030700c0141007030b0782550010022064039845900a103264111034048009007100c0c0d196404400303002c00613850102801d01c02000c0064145e01c6c0412004803c0c500036101303076410780f00031001d00d01081d403640011f6441503c1018640e07000d48c2d4084c1c10001a4007807451401250030110343d0059468109450340c1041612551780e0720b00b102c1c10f020700d00c5026003400a41c0501184c40c1c2082c2c1c001007507000340030040b169080e0f0266214641400709540d550319150200c0380c02000114907040b035440d40701405000d1040691005090901c18150391466590300c495104410010b0200440440801e01400198014940104419410700200748960482075142e0780000843e00f441e82c58010502d520030b1020031901c098900c002c207031403a064540003d211811a0544c02c540c100e40118003907400045c05405490140403e03200c0c0c19 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 369312104 1250 369310854 369310871
    0xf0f0706020331260714030d03050a020c07030c21240b1005040306060b07030507031224090e060108030a0302070212070f031a0906042a06020d021e120922 68
    0x2130070401303950045a40305040c146c0c24000d5480004001e42100c020345000540f9940308900c00e8028060344500d41614003442070000144590580c4286c180d40c420051203942100084042e80550801e01004183e401032804d141d41040c8000c500c4a020306005501243c01070b01c4800092007034140a08a10104070041018014482103104540c05480c0b04100d82c2d00d00006601e003c1c01728054034000804102421000e00c031040115085540c80040101151684034200310501c115450f0314003034010420700e82010f042d054800000c00c41d040311800e501a510740301512100b01c002e58059403090360081c54000c04068400c0b01001035000600581007a1491300f8113618180200046083c140d06428060700300f4010400c001186194101da4807074200c20146032503400d10090203840b50030403002908006000030700726401003020000548a81d00752070344035070450a0700701d03a052021040d07500e680c400b004c1c0800001161005200b110002402400030800348075104c1d50100c00c42030000e08054444208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 369313354 1250 369312104 369312179
    0xe0c0904151a1e010c050a0503091f0c290c1306140405011803080304051501210206030403030e121e270604080f0f0706020331 56
    0x244854882c031054440268461030001440918180240c0241582d41e40c0d591a06a80154810070509074840142e130000249070405a03102d03046030152034040d03403408480d0846002400d000790340e42806912290b02c60f0050381c03650030030b1050303000191600e001c520701c036488510b10800340c0512030070300c2c412810b9858495105a0f20070b645a03902040902080403580141c2c20b45070010340d4290b03a401e1814034105428801c0c0c050040d00141d0010380b541000000f4841400004124079a0308a1400505085030342d84040300c10110140c121020506201059080010714180e801103070070034000c0c640429140c24a0050b641030140c10b440080c0c240c0000035486403086001100c0366401c07441070043c2d60501d0b00720304019188200d2015024030080369201c05c0b4a070340c5d58002c2554094070040301200c85807003800f460b85079070380b441c1100c50382107100780c150003d2440c0c0700208440b184022080b0307103190301c104004114084c5d05090005502500e241d100481d0603443c0004156180c1c6086500c1e15804c2c100058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 369314604 1250 369313354 369313361
    0xb0103021003020a08011202031c0c1407050a050105070203031306020607031109010e06090d0b100f050406151803170d051605041403071d180607020705040e0c090415 73
    0x1c60006160050100720901504a140241101c081400900080f082440024104071182c0812034220410040d44d0104a40c00780190f00b005204984a210240c016109159105903501c10341c2e600108070300c5c007408194440c0010700341007803001d01100e0820100503c542a1541c0c0c41d0401c40042c0c3c8400104200580d240c010707129050b0540b844a890240c9040c00206040265811540140b00000b103002071034891030184285160400d16010303a50400900880c0c20441034440e00310a03d19200c40404d0300d10303291003030002700c4084190306281100c54120070b03101c00c10f000e407030415109104080040406c1a0710460340001c41d014a803140d0700d2591100140464402030064028051b03511415594207810004550568102c00013800c1400b00381000286800d00c1504000c8204c4201460354200740c1100c0d40c55409200c0e0b000c2c40c910a00740c140b03181640d17488215442c82c016886007004000311f00f8554003400d100c803440c800380c8203d10800e00100d00880d10135101250124404089030451086d20710 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 369315854 1250 369314604 369314629
    0x30818130b0916121e0e01020301180905030c06040602030f1e0a110c010f060305070515070219030206070f1202030f04140a080717060f010503100b0303160b010302 72
    0x1501000301c044248042100380600505900c1400451400038a140340101c40718404a1030344031003804401c001944040443d10380c2e140540601c0c3c1844100d101000046c002d80c1d050b0f404402c2c2d56000e855141107100040e05c1e81c00c400340c030a8001002005205181403002d584600e01071000940c0c0d909080d5003900c1c01040040105400481115100c11f03803440c01c18551380c20465500003c1115a848008900b0911918807a03485030341c6041941581000b0355000b1038201d074000d005590300e1680c0e0b0340521040241128150303803246c83c03c100031030051500209440c113695641000c4000603889502103507403a0b01080e001d03620101204090003c104860040340c41e090ba00b413001d90708140000000710040d004900807066100100610216640c8410107444009c00c124800c80740c0c0700d642c508002c0d0f003200f041010429a8040c0200090003942d040503080c1c104c40c07020f40280180c46034000c0b800000e113800d08080b44c1c5070004008a02d04141102040c01680d0b000303a00d80000d65146104201174001d912 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 369317104 1250 369315854 369315889
    0x1306050306040f020f04060f08060c120a0f140a1d01200705010b06161b030c05011b150209040501240c0507030804030b091b06090402070606030818 65
    0x50500403510046411604a0340c0102d502d074041c010342c40050340c0d9070124002540c05c20728004000402c0c89401c02d4000c200c409400c180c1d40b00380c48030381102e1418414030b980c80c1b8032501c0190100d0a9000e20790320401c040c4007000350000d0301d908410b85044265a0540c1d1500c021f0740c46581c216400100742e0400f0410701000402007000745240b081101c0400001d2a8080a081002c9503c3c01440020340112800303d10080840380ea400442122072000d440d174000590300440c0304000e1141000108500e00207503904a4889200c82d40b4041c0111072803007811001141e1448000b000c04002504004100c0b415030056002584403095402444206c40050303210f00b0f6050018000780388e203001e04044904031300c0e1042c07a21601440309820164605078442e400140301d000001400024071030b01d89100c50050140303205032081d000c101c1111080184051080321783c8040200504941c0d45010f600030981e40344a0480400c14030703540c1d25064103580154000f00c02050712010004228901705d5001c00e400307004d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 369318354 1250 369317104 369317111
    0x90c06091d013005060412200606210607051905031003121709030702040606020307020a0b0a0e130b010206010b0403110d0204180c0608091f050403090e040303050613 73
    0x5200002c540e07007a2043e5101c4445442001c2401d0308064901e0070720345103400104913403280c00d003480c01c80c4c40d81040c82850f10004042d289407414690140304550790480c9420020301d80c0d91218070801030f01025583c034400380c400c0750380141c2e01d5000d410f128061148500761285902c1e000c040c8022465406105c00c1541000400c100300050fa603070100c103070003d40b5005901d40c600180007150503100c50003840c1148080140f850100a00f0110010007400c8941c425078061100769540c0314141ea99014102c4002d500c0741000d00e050044d6075051024180c080581e03c0d00e03210b0100100301165101c08140390807081c0035107504084185580402002e4014001000b10510b040d14503190f0b801d000041d80d551900c148050350461040d540c854000d0160882d801101100c5102103103050060717070207248110000701d04400002040841d010034010519110003189a5109000c944200001c0c030004100300c06201e001c0b0301c04592007085c568054865032107501c0c0020a03040a2042044881708c4100950144d801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 369319604 1250 369318354 369318359
    0x6020f030f180603010909060c0816030e0c0a06090305060610052d0414010905011e0e030f01051008011a01090306150e070207030314090d08030901090c06091d01 71
    0x11110800007107003409407104a5640349036160b051031804103070301c400e0110000c02c0150441c0d1204013076601ca808104503101042c4401e4507581021140150082c3c0030412460005000f50404c1c0b0307e904803070080c1d9000e01070b4200003d60150319074202000080722a1818030410004000f503580004080301c000c5083e4503800c000801e20b00c40d15014264112014260280d00304207038100703550140d046429140c4594403440320280f0750254040c85800181400000611540980715101440701e462a0030520480300310342c1559081c8604542542501c21912003900410081c444d550245556078040400d0f64031b0404128252400304203d10700c076012040349203080340e81004803502101c0d400440441c030741410a43e8a51080d40b1540311084031003d071020015415800f040086c00d4070312984a04841c030b86055080c00e410301902c00240d410200103509400411005005558003c242100104030140d095640740b1f202000d03a4070503004a5032840f0148200750a801500e48081c1d41009005110362 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 369320854 1250 369319604 369319633
    0x6050c0105090a0c05061b060103082119110d0504140f031c0c021f0b1e091b0d0204080703120816110a0204020708280801052209030c06060602 63
    0x5020311940b4424100050074628002c0381180b500c03e4100d114050748d503a503969041040203a880450515641ca6074240a19010141b00403407501501c001c140440203c426507144100410748070800d20101c80041c04240c50251241c01503501c40c80c403940348000d84a8100035007500c0e142d03200620800d990428026144d84200d400c80307290100c820381e43e010032220034001c0141d060240c84000c9002c1e041c0b82d2041c0c3d14401c64145c0000c07601d441c0039030700400d408416541100c00241140401c1e580500717124041031740070b48041c2204118003145c9468515040101d08640e04a0b070003a44101b103135811401082081c8108852100310106990034003020a1400941c2d40086c1d4403540480c0342840100f01280d12640020806050318682c007620455031075009042c107580355000740f54146280e084040c0d0f020a51745141c160110040f0068031111811390070541088400300c030005e02c81144840044076200310a8040c050a041c2c180662540c6803419110304124064034040d40000c001c0d0b50000c84641c1d02e01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 369322104 1250 369320854 369320873
    0xc091009150b0a0e01110a06090b0c0c0703111c050d020c01030b01081303021f02090301050c0703020a0b0402220b0301151508041a2d0c0426030406050c0105090a 71
    0x10300c0c3c0d8030344004804420030040c1c07a0030070b0304403100449110325680001000010b03441288094081c0160203041d0361003120300744d0584140710424000703800a00d001c1001900348001210b94060081c540400c070714283d6545203125000960540d1594040802030740a0340c3c040c041c3c5041044c083ca400c2c01580980800a4501032010b003c846510480040782c0e020305100344250618600c0c0b001e8015440320b000c40421002e50081280c42c4d119510b480007180c0a0078a8104031460543c7c16005044081015101c41e0703540840104242c3c1c00042440b01d200605050154400e402c00240b9000950301c0076180c103042c02c6804540c44540003201d1028184900c40700840c1c1c0c8405010980341c03030b0142e6039688c43c000b40d10010208114040b1a400000d1005610141000c0a0030500d0312003c800c0301081158401c2e110390043c0c680a4621400300010310810411a00618038a000c00f00c04402c25046070040a15640c000c0d0300c1240050320100c0c1e00e4440320b03400e000d40da0700805500010880c81519840300c4014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 369323354 1250 369322104 369322117
    0x17071706011a1804020f0d230c030a0204051305160801030b06060c0c120a050d0801180b0d020d152301050111070e01060906090816170c091009150b 65
    0x4414001c20f00e18500c00341114074003004000034000390746480f542c1c150010320780c00503103078007400d030b410100c4480c3c080c484190f113a681844507100b206213640743d68401c1202a84041e00709a68207408002c003048545450300c0403038402440e45d00c00036403403500b004a04503401c050b072000700801c002e8200400220340e424622641200c404c5803426941e11350600c0d05440c10007001809070300001c81400c0900b1281000c01c401a42c1402101030b1154040e108400b210100424000c1c80c4480da403280c4012003800c2151300920800c140076040c000215803d8000038040c01c3d000d48100c2d0303030f0311101802140d40c0c0002d00603246211018120030711071054a03410301c06d628005010701ca0410005010842c54002c04200400081c502050780301000d5840b480300a000000724003a1002190b02013600069000001600c1e00c5040b100b04c030070122241c100100b0010708031001c50920800c1c411031070981e99640e203041b40341e4040c0c1c454044440c4224540003848040d2081403200e0f64240e040d5100800c590b0030b40c40d084903030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 369324604 1250 369323354 369323399
    0x8010902010e0f03160306090c05010f090905041e060e0d0212070209060a0b0c030702210a0b190f0b0f0103090206120603030d09052505010903060908041707170601 72
    0x59841c21100400e00d4030b88016020414110209030002c20f022840d423248440314050740601440c07607118001503c03503191f00c6800000040c0800400c004103078440d4003103a0401e102d4403094010110000140031210320740081610600d0399840311038000f00c010440a5205011800540441100c44040c0f04d0039008540d00030f800b071100b410016815950b521010350250406404d0a521201b8105903130742e503500440c904900440552483c038444d1400c00300f43c00d0f8506080c20080c04205406e43d10040442005001044012500b054150400001d4098011000641e00d40051a01040c008011000c500c150105041c107150000c0100540ca8420488240c2c3c01c2100c425550381d250280441e00e113204007100202c80524080e0504108240418000d202d14666000d820440751991018a00e6810f00d11905000c504820bd0410014243d0f400c0040b5050107400d4030350074540d841d211400182101914400035030030080c41400306e0010030003900b20329111400200125030500303507030320005800e5040201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 369325854 1250 369324604 369324619
    0x705011e0e0303040b220506161101030b210c24160506070f03050a0507020601120201020c19050102060901020f09121906060f06020a020306040303051b0301031a0108010902010e 78
    0x40d1240c404100700c038010544c0c45c250740c0d650030700d00701c1014020300ca0310580c00d607065641c00001007c0c50020255501c0e14454445403910f142e160b59440c0d80d00a4a982e01c0c3d05243d11a030f48202c6903030320801d4144000040c09400b074103802202480c10b040902c21000300c3d10803100100f1082d68900c8100a40c801510035055a40d9522103144480040c00340c02c01c0020100e01c560720400540603441010000b050141e924240001d45403683e040d800e50307004488103c010f0344210010000e4400d032609140c4118018010b2702c40a0f81d0050101c0c20108569100d01400c00c0a01010026035034100000c075071007002c01000314100080e40000c400540b140750308007807281203c0154076502600a10040b909210044054003820009160602c058066841024058040c42c24006043c40c0003083d0800e80f11b5004014220680e201e40d810f90050001502440d1000004c0d0640b600020a9200a502942c02004003415000303800f0b44448001005800c41c85282e4140703041c80006036002401250b40310070445040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 369327104 1250 369325854 369325877
    0x307030c080708040b040f170d1d090a09020f060301080c0609040f0e010614010302040f0b0c07030803130c05010c0809040905010f021317030418020729090705011e 72
    0x349405118005005203c00040c00182c01003445e008000321052040390342030140c0d55158144072034014200000d000d802c850601c0301c002d48502d003041e04a5500540c074210201e071503c00701c0d1404004a420310f80d415030740ca486c0b0003540b912206140410100b01c80c1a881c56040841542d1111004c0030064003403540414201d08960f034541040c03503d4070141d4001c0105000002825007c0d0500d03100d209107101e8079600e0b04801d5442030085605850014000d115000d150100c0d92525600600808140d400749540200016058000841c000c0c08140140d4000c40c16900744900740ea0007035440b09041c828091035880001e4034010540e94024030450300003e6440050601901410080c501c0c1e00d8003d00c00600086d1907805072842c10251101c400103040b614a003007617803070b80d41d200724001d0f0303003218040301005644c80d4561740087c02c51a100c0d07a403002288000e54004100301c60160503040e501c075019010003e220340100401402014240b0b001100b85403000e81d44689035402e504450208070307162050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 369328354 1250 369327104 369327113
    0xc10020a050d0c1706101b0501090f2003150a09020307150c0302060907052d0a0b070210020a02090c0a09031e2a050d020d060e0105090c040e0307030c 66
    0x1660740300384041d00240400e000c0240f00500744000b006002000f140c2c1100407070f1190819084059460b41d654441d41c062500c004000d1900c00c0666070111229900c404200000400041074000440c1c81100b184101c01456034483c1c0005a460150740c2c000e51204031050240c8107140318064200310804800584000d0303500109090600c5c603041a506480944000fa2003a030b1700a00c1460141c5c025800e458003600d503a03855a0300d0310010f1140c03550090000900701c04005851401c001c0901024500300804040e90001c01c00f480016485140f01503c0459030a00307504084000f034440313001c1c5102401c414050ba6000585610020708900c04068020030700e488440d008050a41c00f562300302c4180c5045a40d4018000440c00044800b20f031050b80f5081500e4648203042d07004545a40841c200302e03641c509090500005018440e0140c0c2e000400c0464500030403024403440703080c4c86a81e4008207040c5420b014485c0b921300c281c1480ba02070743c500038503150304c0e02012050380d6046d903040c58424407460300740c2013 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 369329604 1250 369328354 369328357
    0x30c080d0906060e150405040b010311180c031005030319030b0d0507090c020f120301060f0509061314220507030b03060f0a0c0c05030a0e010311040902070c05060c10020a05 76
    0x10000c00c0300e450700002007156070309804414880c0005c2d04244504008400c01e100581c0c0d000d44000300301541201c010300000f0307112030b107c01c2c8003c000b41c02c402c15070200068800f181b080c10740d117011640758008107000390b8510b50116540606410381c015460150000b007041c810205041054040550f00d03030007282c40366120120b9641c03058204048800944d29104000f0080c070519803c1d1003d8440e840080341005c002051414052402e891000d0940e885c140781a1448140c4035040c1c030812008100354034131951440003801c060055428031518507402c08454039074203040c440c12580308110001d52181d0700e0174007074000161698401c401040396128840150080c0401e1071215a05000d0003040020a2441021161059244a07400d1003440c0c0701c00c84c1038504034a040c0c0003070400d0300200155900b140c080c030341c040ca5265043c9000102110002c1d6000301a8000303421115400c2e80020710b480c00e002e600749884001e0413044031942c3c6004004d00c072040d6a0b4403604d800080701c40d004118070040340d0041c5e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 369330854 1250 369329604 369329621
    0x501020f0c0601090f090c140f040606021036020307090c1706150909070c020a080106091d0d08072a02090a0b010e040e030c07080c0a0b07030c080d 65
    0x34040d5100c44446003402e480b50424014510014984403c001c10011180281142c01d500201c0d01c85609003426000021003070881e440641142da94003481003035807560301c9010010f042a60142c207070350182d80060416550000101c1c049c000c500f03401036030300c00b10802c2d00c0400135007001c440030120300c114400700342411815442594946d2400884c00704451700031400e0441700c0420043d46c1680c0d5101402c11680078000000c07641c082c5428050b110260501490b910b40110b1581800c903010b503015400a000981d064000340d90a0751a820104240b9a49005503e05a207448d0880e10860080041c41d030b9841c44280004070810034050041010540207030124049e214000704d0140303188030b81d17422900d078018000c1c4040380651000b0000802d5031044d4443d4200c3c0780416500c1d00c102600f40001c200150801040d501040c1c00200b1010b1400320382084420002c2160f94003400c0c14040e54002c100c407105569100640304402001184002640003100c5801c86a11001803a1289550070303d00e0f00400c01c85 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 369332104 1250 369330854 369330877
    0xc020f240f031608010609121e03050c010b0405190c0513080a0c050105030f0a0507110f010603050d050c0d12061d0415110315010c080d0605090130050102 68
    0x1924403000c04070140158803c0508072402031543c03802c84812260002c1c00d1140600043c009a41402603000100145031410b0040e0304c0e0b410500b10707404114503441041002107002c942d00240746078141c1c00a001344285404200da04100c01c2c503091983d03000e2103004001200401d0760300c00401c80f2090140040e00e8118041a106044041e1035601196807600404401c2e40c032400c0c00c1130001900d62240c0c040b0b03446400003041c00d81081d1240d4004002400001e0302c3c1005000768194604018074007044034918514241e00040394051650410300c1c100211042210b041240800c82c41007200c02c0000c80120608881c50181c05601c1b141010744020803076a000040c1d103440110503036000c65051044140175602403000202070300c582e612458202d071f5240080180085080c40024000040c0208140500606040988009096a4039a00907511103480140c0c0c8558469051080d402d1164207030f405002c0c00904280b05603882100007180007181d1b080c540c00740d4982c0d012402001020340580d404260034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 369333354 1250 369332104 369332107
    0x2040816030b0f07120b0f0411040e0907030b04030f030b090a020304030f081315020906071a0a29030c19050f060a091211030703030503060f010c020f24 67
    0x5030025004801051000355042c40001000c074122103031040b0500e0090703c0945809908600c20702c1c0740d801034144030384040c0c2d0004c0c0d4048103a100351654003400400c0201d2007206555603041400034440d0010140c004030701d0342d010010600008402603103d54115806040c02e88804200e11400c5020300f03aa450560340010040d81405200c0f180c0c2d4010f1401148691600003250180e40c104448031a8211000415110350300342b041d01040d040703224a01000c2c19206c0241ca05045c9030003003680c5500541040300e9400f00720940c90320b03681c1c69580039070304503403010824040922940790700074640889114080800d050070b402c4100d01d903030030003200c4e081c2c00e00a0448000100c41c00c00101440c602481030b91301800340140c4001461905074102c4001c0b12803501d501044c01e0811084596058001c98102c440c05061417030302c020f80e90304020920045121350b030b0f125560710b402001e000320004a0500c40f41400380c480b60311401a92080300384401c00d031058903142c00310540d0107501ca10000540a010303050000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 369334604 1250 369333354 369333373
    0x7020321040b1908090105040b060d050309040204081c0e0105030406180203012c030f040b0c07080a06020a03140907140d1b05011701061b0c150f080a0605030c090901020408 76
    0x4210364180f12151181c6440036030b5900c6214140c2aa142210001c01c41c503010000265036181c50000000003e01071011079040030702d00804902264400d8100f034003154000b6900380c00c8007400340340c030b0800420107160620300f580c41400080c01a010160000342480d8030741c299031284d10880b154501d82c0c607800900034020001000e00403801060f801c0035164803240100d1000080b58800421181c080300300d101064517083c42d01031980d0303031500004442060360041e018001044041007188103000d50040100503038a4100314000b804880d40c2d02c042c410351101510400070200c3d400300d0004121040f008820b14071501d003c0005468415605005040c0d50b041d0f007045800020552003a810380350282c0b0b400c8240d0588006c0c403040e00c4001d200b610002481d81014950034080c0d078a600f52907030300c00c00d070072094262180e0040c0ca10690318a0508000741070304001c403a01d9076000010300d0301b001d0303c04030070000741d0700700008241c0302d003031000315607019072640700100d4040c010950440d001000680142d074402e54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 369335854 1250 369334604 369334627
    0xc0a0305160203190507050d0203150405011b02030d0b0a2106021e12090c060a030905100f0c181409060a092a080106090302011101090b1f090207020321040b 69
    0x150036000c05c0c0c0d010321821102003124101403041c07216298008006022041d40c0c0e100032024440c00520450b840d5482d070489040756036246c01d10b9880b80074260051500c40903a1210f100c11030b92036000e028841c02d0003103800c015000408585204024540c14030340c410709500d080007000780c81082c404540c20302400c0952880b030100304024040701500d90113000310a8551101003a6079010038840c2d513510840c1001441c10701c9002c6e038400b400c1c0c240300f2029a9100c1d0041c802c66400c5540b58012150b0040e06c403082030448691162016078445044d44044501030b040c4501d50754002502e00c0814001c0c4100340105140c0d548400c1c0000092162481c180704003204e00001d00c1c0111b8090203030601c1c1d4039403002503036101d81c010442030741030b20900d80e255400140f454004440003004008e80e40c169550701c0d48a0000b141c840400389202e001000b5000418150400c11034200900170380c01150f1062040c08080c00681d004900c1c2540f01c01400e031006d981d0440d03040e20345514401d0f948441c0e00400000303081800c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 369337104 1250 369335854 369335893
    0x1008061501020f03040b090d1502030a0204090e0a05070b090d12020d08011202101d2e02030705071a0408100b040b06120103080d06030b100302150c0a0305160203 71
    0x324080e820344494644900400d40d803030007a40181c0c6c0e56041e090250484d14145030001d94001ca0080c01a581e58002c594034003000c0381e005a840c801e507190002018000407001b40034921a4540e8030004003100011a181d903078440030f0305c0c001c5100309400003440c240c0030750343c01c01520704041d04614650b42003485a000a541d444120085a01260030380c1d000080300d8607066101784600750098543d003948040d904007101d400010a5100c85160f01103207003004542c0b500c80c2040410140038480d5407641301007107015400e44006002c45003c55100b00701081c000b0301c020544c1c00480b04c0e03000008402c60b030040e219030321901454014070281d00c550b0600aa140c26560400122210251010007410704214280b1007544a810450102800f41ca401000028008001400049070712600019065143e960304001c840c020780e18070740d070044031400510562401c270b041a0410072007102c0c094548030415810a40b0340c0d29000300a000d024011581050004400c2100f01380140c1c000c0c169464240f00380e20180700f6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 369338354 1250 369337104 369337141
    0x6020d1401091d160b091302031501021b0a03141c12060506070b060f13020703050301080d020304061e021e010203150a05010e091504050103141603080f03100806 71
    0x10354060402205101502044c952542200e8641480019080c0102c000259011a131160313000a40541e0010006500784040c6001c0c3c1003907010384116040ba0b200081c6010701c05481c0d82c048440b1500070100d40d596590710300742100d42c00541d101400000e880078904003801c607502010701c840041d00806d09240e1000c001070004040b500304020407600c4005020041c09950380040c900300004020980030300d4080c0d007894160b07000400441070703580030710312401c1a40c101001c128080761021005114020041c08074a210b04283e20080d41000d1800d040249142081c20442d80c024406010540c50710f13100307129601c15a03c1d0310700c0b000d600c01c88c4c060400303000798422500460b506000458031010303407400b040c1580403542c05079540b401d00880041001541d580250032281100e1095041d802c0a8480d030140c01e008600503401a0350040807402d540c3d0500b0b12900031f00c204072100e254180000307079800003035480c07162107602d40035101d55800000507400c0030f05800800c1d061003070200b000710120200c64860700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 369339604 1250 369338354 369338381
    0x10b12090a0f0f480305070f0305060f100b1e0a0905090907080d030e01180501090c080109080a0507140f030415030501140105091f0806040b180406020d140109 70
    0x80419104a8030741245000d1300103440907803d030002452065030004108060251182200380c5560303a80c1c0e072901e00311003548501445034000008205002081c010250312180126225034075140c101c2c03141a41c20340c80c1c01200c2072800c0205950020410150045030240d031403080413a6600c3d10b0400142003124640703e094424603110000034001d5138080350520888416200a000d144102141580585049407075488959658080896a040b070a002c4800c0f6030302035000051928403c1c1400740c3d800300d8a40041049a04000e0740d1800100c8010844822540034541262920583e152240303113112225084500383c42040745a002460f4041300400846030b43d021200e010009803c0290190381c001d220300041203180032600c01c00765004d90010807924000134500d01c85c4130214956594011800c1a4010000f800c800403c561810580325117100d0003022590038004032021400150341c03000051006042ea40c01143d80e8102c0c4015801c901d040541c01c04c4400070310b68503481aa001004404580341 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 369340854 1250 369339604 369339623
    0xf1204060b03010207210507170d0e03041202042d1413020102070510030608060903031006030b1e1c03020f0606010908060414070b0301032306010b12090a0f0f 70
    0x21082d1030140308030f0700c070705601a07546000c0707482e6060850700e1a00103a01c2003003840020020a40000d540d03040c007400810422000d191a4560708900e2030072518403a000b6640342c0e10400080c03001d2070b108801c0031007072641281c0215907041600b8860100311521446485074140c00707040d400142c0444c0c1c01a480b00304000c2c5011107140d840d100400c03040711182c00081c1c0940c00c030a5040c0524140310103200010350640c100072804603a0382500c5440c0003802c98880181340c00200038450050b14100404004101d24601408001c0503c3c000a03d1130030750740d1424200b40040943d01002c0e072124910208020a42402c12943c8080c904029403540b0b11003680403074600070000003800d1980149401001d0f141c903040107212a50311503941d84a8590300d9507150010703114949000070351030101c00045000c1d40c45006040d10440c44240c82174125001141c00440341d8205a00501c102c46491b025141500d01d494402c000c030340c90790210b0b58200701540d180580320f0902c08203180b05200d07428040302e141611070714520 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 369342104 1250 369340854 369340871
    0x302070b091f05030703110f07020409020d12180b040609090b18070906090e13021909060311041b080a090213050106050306090705040b0313050c130509071202030705040903050f120406 81
    0x25034911841c04030007500d940500032500076061640c04640746a2019102020ec003050f5115904014407480300080081d500c076a600d1141e11400400000420200300010f08083c2400c03070260102060f4050003886da980c1c2c55081038150340c0e03a01c0503001080c407110aa41d5608110000a03d042c070303180210030200360080c0c0d00048000d50021841e110b103807003009103203909020ba401c124900d40400c0e42e40188041520005c0352046d8684184c000030740c4901c44074118004134900f80800d89e40044c656500c5003411990580703100341c00030802580310102e5100082c28142900c0010040100140c2050382d06151500100e40c003600302c0011030296a049542990581d110141114244a5405050b501000610100f4000124030300e000000900c25429039801410200200e9112509030182403100e5444d2000c3c80340482c0188000c2001c0d007408081c00c0c060300c11a801003940c1e20840c0c40340c01c0c0a0766581d800c01e01070512030403e451200c40d8083c2050354800304680000002c60003660242c40103032420300903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 369343354 1250 369342104 369342131
    0x8010209101404030b10030506100302130504120e01050d0609020c0c03030301080d120e0a150507020f070314150a1a0604051c021c0c1703070302070b091f05030703 72
    0x2c820b55648220107040ca424110341e117445000700c003e0500081d40032500004000074805004041c8200f4004000b50207044c80d50040060103c505c0c44c0605449250005200201c0c411844e000301110312810300e0350001ca00b05004940350301c203841020304064a081e2001c03030b42c410942c005021500c1e601c801c90300b9083e0900d082580b00d10083c4205400d503804481214a001c5c00341d0000071b41445105000501429410f110a0618901100890700d17580840030340c51803154035100c0c0075009a5180700600039112a440c199079600001c0c080904200c1042d0103003080b43c40c08121310744a1181c0c007080682c46051110212000c0c0441409001050020020f001c08908001058500702c0d040101007415220b1035400b0005405910141a030b0040c100506086203464001c00901d059842000102061480c0c2050000d02402d00024400260030800500c00440d600007040402d894000000e250703260303a0040002e4103070703800c5081891000d0321400102c01003500540958803502840c0c400303100036820a0348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 369344604 1250 369343354 369343367
    0x14042616090c050f0f031902040602070603021804060e0a0c0e010503040609030306030503220b03010503030a11010e0d030c030e0604020102031b010f0f090317060604031202160801020910 82
    0x11004041030451801c0008101a812001c1c000d1803600700185000b469108601c0182d0044140038060100002030100c541c5440940c21040c00f00a0070840c203050a01d00002e40351441440b4483c1050b401154204044004c0c2080c030602c640c006104100203540c0b80780c500c449030411242149424a0300304001d00c018060319000039015016501c1e07500d940d50720f64419005240d078010641c201940d6550200020300100010510b04840c0741481c0d2095600400d8240300c1d0485400c4803e910702c0600040105482c000280c50320340ca01802c100c14003294280c215070040c214074000040911070341008000c07007905a4414190180c240e90705120310400326180c10359a80c000da07002030040c1d0081000c061b006841580f2040005400c90010440010300340b0118103448140b881c0382e419940c0c42c0c00400825400041611012400d0b0160f4001403500000080d201c2c000c034030011f40441650445e0010062082c4040321505d0420741050b646c468507004a14000c0d080000c2180c0203074401c0d41c02a010501903403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 369345854 1250 369344604 369344623
    0x50f0f0103030905330d0b030705090406111905121312030f02220e070810030f0c0308030f100b120414030405060403060f0c030228140426 61
    0x1c40740d030901860324051200b01c403017640381c4062040c1c1000e440710310100d005481c074070410281a42d00362100c20500f100c8040350340c00340209209600140d82001a51551040594040d400900020341d20b134624100c071500c5c2c0305200c40740c0001c02c0054810301d6517a8102000d060759462881e948015956140c88043c1040454200074141d909018141901d60303103e90051003a50b1411007015040c5244600240003541a030408810542d0305858280503460340001041da0008035450300c01028104100210890101800041c040c01d00100d011000e0001600120b802103a01060841c0d49150038140b9140c0d0a10a8034042d40705400c03103200145007410302d015106600c20245c0001240e07250341d60b80420b10400c000c0101c00c640018000010b0700da841e1406400251b00a040100700d1100401c402021242040105070a06105215049031110604140c80c1502c044403030800c8000056401901c0c0562051309c031800c2503400090100707109086041510800d0429890f00b03c035082d075440003c0e194650f85 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 369347104 1250 369345854 369345857
    0x19090906030807110a05120a0203010c0807090b0703021903030b0f030606060d1503050a03080a050604020307050703030209041103130c08030721050d060e071818150801020d050f0f010303 82
    0x3c1c01403034003155010a003100d040d03000800440300580d40f940407a02d8040342d008818a1034000d454040103600b02805059160001441c00900600d4a000301030441d0401d8002c83c0701d0907401107500c208040c000c00626280b10050412103240c071070701c5d01c0c1c0100905030708081a801120102895070b518140050380c2401000d0092005003022080501040140360101c02c41c0304150f481240000030035010f02c000880d0368000d9541c0009807410b40d05080668002901e421b010324070401c108890207921505451060354180340c0940d554043c40009005450020a40007601c9400400c1c041c503000c28140050b030451041c00c0600c0c600b50340318070403900c1e401829409010000c9940030240d40050761a4504401c81003030900c2810130614414003400c035035660f0030035101d0314090428409405d40080071103001401c005c01d0400c03800d0070400b0041088a030f5100502c80c1d50344403036040c41c2c107145070106c100c00342c11284000c43d190011081103001030102501c00c02004107182000c038200c030b180c4000c0203050b01d400d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 369348354 1250 369347104 369347107
    0x124021605011206050a12050615060306090a0b03060a0e07080318150706180b01050f03100b0607060f0b040b0a0305060106230a030501180e1504020f0303190909060308 74
    0x4001c019180600b60012080c5582c0ea00e82020600b9500c510703041d0003a1404500e00a0203c2040c90031900c2c1c1600076003143c3c00c191040c0d15075100da84d5604101c0fa8002c5e800c0e81c520400380c070341120100240180c4805554503000c0d8408112520825511801156201000f1a10044d130764181c510303128840d020b8031a09028022410495078101030141182c030001c06c040b510710302040c07501c5d003500b07c0c1c0300801281d6190184903002e005020151600c5405040203c1d200040f03800d800300043c2e52030f40b0b0f5503100c00083d0f45504680d1000c3da1030205845680e03030000e00500070002811000c000800c0440781c2c0620581c9041c200d0286802e010104805981d070000051442e41d003071500640d001c44c035040b100742103d105c03488243c9691480c20301420b80c454490700d0114895060510000c803d00d00d03c480d0103985480c002040001d0f000002d00ca03454100b04490070030154543d070020031615020483c0060305448009400c50f8004078201c0c603140002c020b03079200d003402ca0312040304500782c400d2840042d001100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 369349604 1250 369348354 369348359
    0x6060910050a0306090f0c060302031f24020f07090e1002090102190c0b0c0a02130b0a050f03210c0d0309030e0103050709030b130506180a03140c010501240216 70
    0xe9511145401e1b002d61409040e480003030780d55100c0d030066a001000066004010f00603081d03081500481c08800703e40094803a03078100984d900e40e400f100d1100f0050030789200c0c140c4e1280c900a210107907082c0c20030015980040c2c0c03100d07100c00241014007909026071080c82078038224040c2900c01e0b1500450142e0180510154020503d070740142c2c1120240c030a820310703444c0020f80301c1030341d00141140d0030000042c0c0340e0002280100040400080046410f007030401c841328a50342d03500d0039030900385c40084500d14148224940440d04d48800b0042100103540c1003050a0720482520014100d4518400c0c101d40b01d40f016040201c0503900020300c020003103403c8090003440b941c0650401c5520200714a814458103a80ba181c1180e5003a058650001c00c8607040300e508140300e030038406550700180814020901041001c041c507519200740e10054100701d150f8a00003880d54a900c211101000b1600090100c0d5844500c0c0d0200b10507010b10304ca00c2c4001d43c861070000640042b400840815590b100d0300c1042e80b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 369350854 1250 369349604 369349613
    0x305040e0406020c2409010b060d0c030603050f071a0c0709111315032009010806150310060f0305100e090f0a0503070c0f080c04020703170906060910050a03 69
    0xa80215041c64080c00340780703024030f8100142000d15504007103032484d80c1004c0c17081451005000d44490300c664100308200582c1e4581200702ca400402407140001c01080502c0b04400520007500700405074001e50014420b454000031b644000d64150700308402203201c0100c80e07044580320305e100780401604442c10800c14201c90f94020300c492500408682d1a180c0748c1d1807659807140d566004540003028000405804c113525100d91a03d25108010400c03606003040c0c030240150040300410307410070100301d001a1564481071200c1c50000f00403c0a40c3e16424403020f0b60740400f990b80646000a1380054000d2001e0703201e8003400e40150300720500b1020ac18289103107844807003c0180f01580c60700c01c02c010121100302c01c00c80c0b5181c15000c0d01c040e51b00c42e003551404003481c1c2500d6000c1110380c458003100348a071901c0401e40c209591401c50b001a559150b5260956051160791103810380c41600108100140700c0c003083c500d100f80412110a04e0360b56425201000c1503003a80103054020465000520005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 369352104 1250 369350854 369350879
    0xf03120302091c03111002040303090e09012903010b0907231306021f020702010504061d090103080702030f1902060304050a0b090a030e0102070303141e0f1b010504030504 75
    0x240d50140101d103070b24250000d03000c1e01c100b803c101240040d045a005900740314080c00781c00d10b00c0588000941c60140703036840c0145280114060701c100c1000c40c0011805c00d210940c001054180c00410700428401207039007038030ba00f1050302c079224000d50074610032103400d180c1240400d04c1510241c40c0c2092111150002905114802007200f25200d410404401c0c40007448080000a080311350080c0320600300c44211003140c0d0090420300503520700501039030700145e03002030a4a084c0c0e149071034141c641d0704000c00b03000c8440009440c69500850a000040103102d450002004118001e4044070b0500d018032840d1039544000400c144410007441400c00c00500d4034400541d0080e000e20111000d40c5425220754001074021b440b500007540c001c0c2c8003c42050382012001c012080d00740043c2c1f11491458501400c00703110255524407080300013410500d500099840c80b190440752081e6907440700342c01d45540010341e1010006220082d190400b40c0140709050040d81e22499055913980d0509182c020561400f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 369353354 1250 369352104 369352117
    0x3121909051818060a020a090e0c0708030c070c03060606021e1908090a06020606090f041e440720010215091e2d0309090c130f03120302 60
    0xb0800c0c2401c1c60021820490603004003e629170060755440141401b81c00305c034180e80507030084100b250411940e00e050f50f00b5200d0f05074121184550700c0d91001d11000e000d100e480070042c20104036450100510005900c03075019250036400301c403c07080c44c0b5004e5076422003080e031292546910000d42c0d041c4d0b10109401c034414543c4580f0829007003816640000d03203001840d400c604016800b072001c0040900d842a11a60040d000c01001c890350308081e1209140306001519546d0765401002820f82003200f07180410a0000210100800c00100c074040c01082d00034074124040320006648848002090f280104c51100794031108080041c00e8940d203242d85141305003c060305500900c1014084112922501ca00c00c400c0c280103030040720710b40c0d07140da10000d8603140e500410307034071209521418044028035040b040f0301d51004052000c480d101ca491a52156400e10758000000c02c0038000c8519040002d011100d210711622030764140c44051f0100110901c3c40040c006500d20105104100d0281c0d008041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 369354604 1250 369353354 369353371
    0x3030c030609050112110d0c060804030504031208100b04080c041a0d06020918092517060402040612020307030f0f060204060c03090503010c120203090705031219090518 74
    0x1c545a56410b65022500b09034010911104129485030812003c00b28464003024100ca00d80804495600c8891001406000d103000388040e98021506060242c0c05950046030b00c43c11441045808200c000e0480109542c7c80c810640c1c1481c0120b0080004816101139404450090403040034000c1007101900d02200407030119880e046641c4010f803643c4c080c444080d030242101580c2e91780354006111210b0700070350300c20110480f00d0080c07000d100008540e2940d04034451644440241d14803940d94101c0e0340c40e620009440c80042001c907034120700860b03c580b00314003c84003044816035880803041000110300c00258540c01ca400700b0f000003561040142e01c1c0b240142d112408442042d51040201c1c0c0c003640200001c120418034100805502500b03410141209500a02c1510041880982090400c0c0c0c94a841c03141c01100240d5408410081100286070003000ca4400c40410060101c255000d2200e2a02e00c4809201081c440c90007042e80c1c0d01150030140081d01c140001500d41c2441c1c51001d000c40d007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 369355854 1250 369354604 369354611
    0x10f0f020d2001110c12040b04060f020c130b12010218100c0b0a05040b0a0603150b01180b0309210a0c0303020d090305090f0103050906071b05070e1803130303030c03 73
    0x20702c80e4003d1041e200d4800400d04003503501c00440d1000b80c50710250041d22292164100010b00906500c034007628102c0705d207420403966150b00e50758280c1c00c01d40c82c4542d10f9041422450030a440e11641e8000c1c0c0d00e4440c0680c1c5420000807000305107420303072180720030342406c1e210341c03409091440c1841346044003200c48903c0c0a42040c2800d0342c900c80041000e403102205142c0310001e100a004130301103000d40080344d48504100c100d280d80da403540c81d0300788801220203041d543e0b03102ea051640500880c180400d2a080000b003125101d50302c4039299041130340c001045101e010803a10f00f9404500e0b000d240355510049103418003080400440d040e5482e0344044081507000c2c40a04032520f101c0c0180b116a034800e48500c0d484000c24801e0043e0540350320542d904150a1105018030b882e0041010384c3c0100281c600140c2c40c1c85041c5141464250180c0014414442d1030f2001442c0e8682910b00d034000c5c14140088081b5410542d45260789005010310f41030507000c2e00f002000024020361000705030800508021 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 369357104 1250 369355854 369355907
    0x1803030f0301030b060a05220b01050f1201080c0d0b0103020609010c1202010905010f02120103020418020d1a16020309040906060504091a090a080316032009010f0f020d 74
    0x11000d9002a401251203039803203000c0c81301510300a441c0c0300103090b05480440c0c015680040003801c00c02111220540c1c2c507500c0ea00a0000d91180c001c03502500030240616030307900c3d1103200301112010244903050079801031034060b00c920720705400f101d41200d07048a40100140d0a507004c00c10181c0c0008c0e002818414076000d8100040c221080c40307083c6141030b030000640d44625040140c00d403400301205070b1906104200250542041a01c0a81525019900080c1d018603208000742c800c4c9a80c10043d5004400043c1c2c6020000300305405104c0580800280049846032084444075410703060070107000d6081880103034210f052650101e25654002c240100e001541c03000031900f02d41c55040290f4084610110b00c420040c03000110755007012201c0c00403cbc038079180f5182d000e0716010161004404901400f4845040c92180d0840c442281d00303000303050440055174200d0724032a0f1050301001d01056107521b0001c9180c0c050420040c0000312500905416802c120382100c04401c60300400803111501e036880c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 369358354 1250 369357104 369357127
    0x7080901020d14070e1504170309030105010f0906080102090a14010c1704060206011703030106110102120c07060b0a05060d0b0a0b0a02061008010902030703150b090c040f0b030408180303 82
    0xe10942d1043c200c0841564140204024038680085060701d000311000c40610800000340c2d401c45049842c04405103800e0102130380c409045110307196050390700d50309000001ca0480b5003043c02c1c0e800c845a1800c1041295075411841342070b401060340707032a80144101070400554005482418007950305140c640e825148581da0048132981444484443c5040818148001c1c0c0d0100240317400751002c052207003640441c0c0483e00355a13110500a0300208000209103180b030400940590b400c0100d0303141559500e141a0312511200d0304510015159907080a0700080b4908100710380703006841025102030719103208204148080d10b60001560b81064a640e00000c204c6240005042840b00a502802e164101042c079035095408036088401541d1524042c0801641c000541c10304607039029080c0246031400080d40b0000b00366111005800080581c02c00203580b003244000c000380d440c004000240b041d00c60039030701c0482c0411a00140343c05403c2045064000d61040c010b02c4c040f400074122490412031600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 369359604 1250 369358354 369358361
    0x30e0109050618010515011b0b13060b040218010e06131d070206010e04020d0c090c0f020607090e06060f0c0a080316050304020102030d050907050604120615080607080901020d 77
    0x40654031504400244003110f003000218904200c0300d10000d110904041c1c501c0044103a0303124609041c0000c0030702c0f0441310000d092000303d000380c0020510041d0f260a034240d07820fa1406c0340003203a41c107240c09a40d408600d850b10030f46071100c0040303011180c41c80716000150344403c5000d03e8145c0c04032080c00785c800030246005100740a800188041e1075003118030a460f40001002405940035500844014400701c0300007090280d100d41c046604019040aa00f060740b4070103190742102c00e9080c20116281b0f400c0b5045065071039010b034242d084543c2da40c0c5034141101c09580500a0341e00300c001003000b20f400351500700041d0415940d5552010328005600d580c0700d182030071078101180c1c01c00010040010540e80c85440002e1162581059403440c03a160380002d49900c2810207200b0000c0d92040856641c18040201c0c401410000d04229503e82c1c44451201d880d9182182c00c4920074204007551140c002d60024220403941850020445510340440c1030f2901c440c0140715102e1903600b4001003010074690700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369360854 1250 369359604 369359621
    0x15051b19030c0606050d0f0f110405090307050610150c02060d06180f02040b1204111216151e0c0b100311031203060f0a24090807150f030e01 62
    0x1100c44000b121a0b190070400d40c2c2441c0d1026104010700041e4001160148100003100f5901c14031005007140e061a1a1242910104050340c1040c5001e04100b0343c040008001d004642c061070841d4a1541c806048091713403409030240a41540120048281880c024002880030710b100034001030a19454803070900031100b03640e200101420480609000d6406180720303038511003015070003e5242c58241038103040305110300103014134000d9220740014240060000e0b0803c0c51140207100c043c6502c06095141d5030b503004c0e212102d01405540000142d550280302d840140d000040e03c900c055022000c440000b01c0c0c240701c5680091141c50b003920f000040d92140c40601c10354070f4017010444a410340c00e110a00c101a5151107000ba0320540c689d141c58007903002070b00d0744039008031041b0440c040e1940101d1400d5099034064459074284102c0454440095003540300d000702683c0e103000c04a41d4805005aa40229100301107140300701e01144045203114488624070b03070b113107410007003100c1c80c0344401d05003119100f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369362104 1250 369360854 369360857
    0x10e0c031c05041a19020d020a030804060b030a06020d06050a12020d031e230901080a050a0902040e03030105010f090f0e0a322a0c160906080715051b1903 68
    0x40010600740b0003605c0f08501001031004102040711200d010356250480c1d0400740034802c040001a080000c0d0b0380014400a07000380590b030041401c2e02d401c40c065002981c1100240d400d202c00031403075081c00d40d0b201089030034001d503012160b00d0315024094040000007056040003006021300c9036a1058105d40110b568181e580e903074200c1108100f032201540224442c0302c0704036040003400c2c1d00d47c0e44015190340041c2c10240005158403034010340c100030450210000d40090038401e610f1701088020010314100e6400703032241d0f0341311440c200c021141145640aa42d02d4140320f000c0c2808040e18907440554400c5800d000003400f9001c0071a0042d0302401010707035202c0c00d4440200560620b0f0004134203904007402c450400728104030520328010034503103041c4040b0801404614100101000c00140703a00b200340b030f84d5103524561940c0e5590090001d60040d44968451000001010030703183c0042118040c00f0b5584c6401c08042000001030045045003056980c410032a90140002c030810076041e1040c0700b13 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369363354 1250 369362104 369362107
    0x2090a0b03040b010f1512022203020310060503060a0b030a0f05060a110f0901140702190e070507030c0209061518130b030c100c0807060e010e0c031c05041a 69
    0x40d1405000800050704240d02c418074817242040074141c10b0096280240d000d04100f43c1a2410f054050024065840305040e40b11040b00702c40c0002510998030000d890095054414142c40500c3c0102aa4124441e45030581d200d03100051010560340c0c0700500b03144004050300d40f82641a02d500480f421128002e44160b04450184a0110700d144142c07180c44080c80b644c2810704005014008940c020240800c0c184032203101080c0c0b84c1d4500f0000c071001d031603008004a0207690400c030030310300e0301400380035051038030480c1c2000c21310140c010420b0341d4185515590710b44d0042440d5090143c0c80741d000e0300b555080b44031212205501507258002d40007011043c002008546040342c10003039948c2c620354160103514645031005510f034402080c0b2801003841a0358441240401002c210f500c0907440300041c0101e0400318249080101c103410100da80607042c80244003413211695a147c4541a15024030f605600c46510003081140700d41da090403045450802509043d03a80d40b030b00c0026080b040e03294260a20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369364604 1250 369363354 369363361
    0x6120a0f0b010e01121410030302061b04270507080603010c05030f0a1d0709062c01091e1a0907020a12030515120606211e0102090a0b03 60
    0x429110340320200491a506008141c0d4000000e40311203075031041d49041100c2d0036904401118580c10140d035007011840c144400c2d10b480700b1407010150a0303010880060080c04045011400411540c12990b440745420302d1501e494484141d071b10803000d40c011000041082c0011a040c40140301c0c1c948140b000b600c602c0c4da180380c444101400c44a9844030700050007010f10900c20384004010080e40d0204000f03200013400c444000090003c4050490400203902c108075010460090300c1c7c11000840d0b0382e15907413002c0d022004071044006000703e00d0150340c0200810041112039401d8001c40d22560b442c18810001c9183e001c1504152a0000c030030355454040207110400c1d0742000301c00c0d9070344030341148041c03c1c899031344d55590300c0e8000700d50030601c003019150001709034803c20980d100d40010400804244200d0394401005845850031681180704601107000c01281044440a5541c0742c09954054490095130b16a202da203050580f020340074039942440500309585038100f8000160021588c02c4c0e80313918 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369365854 1250 369364604 369364621
    0xe1b090f18091e10020a09030f0c080c010e061603030b06070606050f040504020108040f0203030904020a030f0506040e030a2a0812060301020733020a050c0705040b0102070317090612 80
    0xe107510110f041d5844480f03110856118003040c0c1440509143c0b01c0940e44590039282181d9804040d0005401842002100020003a41044610407540180309590a0402040054071201da203070203565008001006295070252a1030034520341e0611030b00740040c0c101102c0010480580014008913012b503602c40c428052460f190101c1c8240e4801200c00b070203a07190550008280b80c0000e40000c003552040c0c5802d01c00c540c2c061082d1500d00102600031034498282000050240c0000400c091100c1d150030046901070038540a601e210700010b0009611700406070743c0440310720148007007084111800e001c0c0b540c504205455481c0b100390080090545882070b44146070900c003009005140310780c4c81001900c000030030301015190386600c0d4164910404165018107a41c0b4000102c900d646503100143c21031245401c240a4180700c1c5800e42150315058079a010702080311403d184036409030f48541c50400014640450107000804804002800c0c86d04100100d51141c001050049589155408000210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369367104 1250 369365854 369365863
    0x20d140706050d20160501091b061806020714210105040209070804110108070c02041d190809040504020612040804091812050a03200c01060e1b090f1809 67
    0xb02c000481c1c1d1420641c026504e00e151241c6001c0c0441070b104405e2000901c102036000c03820300f40d000741140c07c44198140105201408600070100404d0b0200100d462551404407803c0c10390b8940d4008021a1b030814800a049920316000c5690140744010b1500712075103504400d00c2c40c1000040003003003038105441000301d000001010001084041001c03c404240b078103042582c000020700700120030b80c454210440301c4441d8110007075000b034201800d05c40171140141042d03180004420a072042c83c220120708041c085c200140190030a00184015070b03461030182c0c4043e0b0050b00c01000d6034681048915090341e1044221b0301521056000b19003004500890f000d168000c0048101841d50084c42e035607907a014003000078954003017040200b20419920b02a1740001008012280806003844904040c000030707034070509510703205500308500054030f5440092480c2c080d0781130840c140d04200c025040c01906030000d200d03155010b003054000341140e8441140d001c4924500080821075458060015842d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369368354 1250 369367104 369367121
    0x1a0c0106080d140a0903140c0f0409030507061503050d050c060a060305150c13240207120b041502030a020d150b0915040503070e0f070912020d140706050d 68
    0x20381d0000d1100741541a4420b8804442d826542c1055032a0a0101c1044941c0b5101b900006c255611440521b8002c0d44001600103180c40126038502885034006d060100380e6141d800e0090108105000804c00640590820303290f28140d450403c99a030303540d458107850201001c0400d07010950009281041140602620f0343c800001c0c04180402880c5980c0c80d0303078a148045030580e042c4140380200e6002000c0000701c03100400d0940506407565200d103503801d00300801d1413188081514040c84248014004074603081200d14000c07118234041120f840700c00350108000e008540404504014001035002c903c0550300a003402e15005846044002c1510102c450324040a8070600342403900300140c461200448102d040252106040c0000e1201104024020360b0000d583c1070140381342c003241c0c0000000c1a01d100f41a012486142d0383c0750030a041c0c0b001340950141005940c4103d10480150030300c4000c42c10568801d80d00001c510506000e118204462900f28100050300003840111002450023220305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369369604 1250 369368354 369368369
    0x2070f0506071115040f23150d090203030703080402090f33030304080d080f0903040302010c030e12061e061c0807050132041208060a1a0c0106 63
    0x20100e0410000072154000c01c07000420728010740e501081c094903600c241003200d5034003d0242d0340b285d4a481c0c112041141e00c2c0a22807407010f120000501c06c0314555a584070b5040c0180c0340c070f01d43c01d00120990300c0340c0e802030140031101a12501c5d6140180c80c204002c103002da000b5074407103282d810a031040100c12000a000c0b80180703521107013440702e070089509801502804071214907403600c5c011030aa040c0c902c48011507070343c507003c0401c00090541006c612000c0c090350316566404c0a40e58016081c03000e07001038482900d160b0013403200340010350140c1c0d076842890b402030412040340303812100000e01a844902403001c1c190004010720400d04c400800d072201c0c4000d6075406040038945500810240100d1803070a1440d4030fa400091014020224200d03030486400600034841c0b658001422840c4402e04110b002c04100314018407243c0c103400c00405c1d40a16400391018140b00c0b49480100c2c0c9424004d00200d0b8800c0d902c0d0800502d0a42009051120a0400e0b501d0707622004291441400c444045e4008203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369370854 1250 369369604 369369629
    0x30509010212010e06030f0f0606120d0e01050904020f16020f040612120504150c050d14030f0406020c030a020609010c080c07030507060f020c01021c0605010512060315160207 77
    0x880e44801c900303d06503200391141c0c10466443c035000920341803010032140054000c0c05400d28448a001c200705100f110195080d0700007940281e4250f64482c42201440000ba4004120350b141c1d622913002404000001040036042c240c044240703212079800500d55540d40c0d101c41c0d44690850820018800480d841220308100301c92400e0b1003480945030002004002000c1c50b091152814010002d0b64003030182e040800310400c0801101400d010301c0e00340161070610558180c81e603542d1080c004220030a055a11f400d0071510b54808055000001910881c3c00301d4092040006111003000a4101d50000307600620740c40c10003003561800c5a00103400e000402441804005505000d40101c1d41e20b56072500e03101c5e58841385800c149004100c0d0200180c5405c0c00003c030801c00310015000b130322407195141000c5400a80c00740341c500071a0717030511496001c11006c1c800000c80e042c0c0e06440c10f510900180071b403140141c403110845d1103038904441800001c003403400008440c2e541001000302070001c03c007400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369372104 1250 369370854 369370867
    0x6011e0f081005060405010c1a070f090506040f09020903010902060d150503031809090c030d09051206092a06030717010e040b0609130c08010606170402060f07030212070c05010305090102 82
    0x1d6043c070946c0200350511003546591010001461498019035602c40d0040f1410308160400503c6408689441c000058650341302295038540f002c226801c680d00072401da02e01510f00003541010f5007083c3c0540b503146d5079424144002d61180c20007010f82c400390071000206126200c000c00d13501c0b90150071140c0a9401404510141c0a092140c040381100c00c50f12001d2607694070f11042e10b0320b41c041c40c030300f9014003841d80a98916508504041c0c143c0b201141c54001c40d4041c15a04c942e181c1c0e0482d1154016031102656a1420315440026100b20034100341096016075404041000ac0c3c2c02a5455800100c07900590301c0e161240442181c050441e203000c49855090a0302c55010b03d00c1e020700000d1245000310046042c811352170341c22001c0c40360b110000c440071030b82d160700c0e82d4001c051302e1140c0390109034070200d03d1042e00c04c200e1029114650040280d404c00c104034401880039006010210254401c981d00a8101000b50014140251084400c690814107001c00102902d101900300c20450780140b100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369373354 1250 369372104 369372109
    0x105040e21031807030b010b070c0f090b09062e0903060204080705010207050321130e280c020a060203040311061009060f0e04110103110d0212010f030203030d0506011e0f081005 78
    0x46e241105c00780d4240075120b50b118200494180382d16488581e458000a20010701440c4907081401d038044200c654802694030b4105100c0b05030007500219080b200013071085840d07500308228844001442d8a070a266035500c99031204100e03401b40d000362140380c0c0510303020803407503038100404e002504054014081d1003040d581012643c98450025035040c5c0d00105003121410001295400223001e10301c00c0c4801c80c00e12026070640404141040c00045203140b01804586000d03000303260700c1032540d50003040c085040da11554000c3d00064012020402d01186071144ae600c100700c2240254a81c82e0340f010038600d0a41807004481050340041c542819041081180404030140c00e40e02c5500300e00340b012200020340c0100c000306018042000b4044010860441545966010340706014960030b042903240d80b00c246404007092540700081d0315600400c403031045000c00380c1016800450606049880c000700c6408070610001c0a008040040c0b0304202c500803580d0301001d460b80090304000b0702c11209040102 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369374604 1250 369373354 369373373
    0x6041503020a120c03050a050603121803030903010501151d0d030521011728030f020f0a030305071b0305160203030403080c0a021302030606030105040e2103180703 72
    0x219024503501103441103031280580410038070301921003c200401d0a00200260003003009885c689100c62404001820505001074200c0046070100360b00b038206070710b42580c1c60840c1c00c0e201001d501030005104000040e00e09000d8640a003444843c0c0e012003019044000b89046198500d54244250302560004151540f13841d20707000c99003614010781d40e00f03101e40c19080b01c548009907243e1121200000019003030300c410790002c54040140252800c24000b80b4500a5003c0c0d50020040728201f080d4011001a002b8440940074909a0060b14072032107400385100d080103040c5605402281c0c60ba42004040341d070005c0e0442e54402c20702c4246111031500d8500800034080c44480302600a101d40303440c001e640e02041a40c0c001c1d9400492181ea41c5800d1b50550f840301c0340d40c6012401001c5514032414500400c3c001d41f4030030742c400790075581541e00e0710003080050952071846075100d002e041903101d0136440200b05595078181c0e0a03201542c078108103110300c00c03400070b400a800d0250070820b410320004403001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369375854 1250 369374604 369374639
    0x105161101050412080402030a0b181608062214100e0f060f150306041110020a0812180114010807060f1d040225020315151e0d0f110604 60
    0x2401769850b68842c4003280c03401d01403c101a00c1c82a40c2001c000c0b8807a040f9802c14194008013007540c80c0001e1414460350400780a02403190260001d0380050090700c42da0204a00c2c40d25106104001200c030b039218400e00c034644151442c0d040d0404401034056002c1e03400340d540b21604003c02046003020003100140c0710b20f800f60800019081800120303410500c003690702607090381c1c02002d88084e400c040c60300342a100101003d250048800b1003807022214004101006102d802c584901e00d4401c0300c500c4000503010003090b0000c07901d9017a0700c216691100f440740c215003540c1a080390045c1d5040201840c5004010352200703080089450710b605000307601441006d48140501e400b126081c10309000a0064081c2da1603062258100300e40740410801103008082d010b6000354140c8002e000e50303440900140e041200ca1444d05d201e00d80c3c02044a0a03c0b11145013100c0c40d54040c0090419040c00107407841124201c25a000c1881989620a00503030f000d0007503034500101c2d0311a00d8507180c021261504451700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369377104 1250 369375854 369375857
    0x4051e04030c140708060a06140102030315270a0b03031c0b0a0b070c031b06050429160501060803210709030506010306050f070e0a09020d06080105161101050412 71
    0x400030104210b8020402c03002c3c250050140c90010b0b498078903055641c102100c00312401c41c188040044c5050044450f043e4105042c1d01451030360fa43c02d09008401c515003124541c02c402030400c030303000c501c100d003110121800c1140320b04030590a140303901409031081c1801e0f07184660400c00400310b000080080b4400d4000080038041007580c2a20300059040f0f01c140e00c24109114005036820820500300000740586c3d105680247d0718004000c13200450000d075000780c1c004280200b100b40142e8034403c000d41c00420040e465116203004500c039071a0641c110780ca5480c20580042110000c0100a0142c0d1006d06000740086041865800149003c0f00b035903010580f0096001c2d001c25030072803140d5003900c00380d600300088070b80b1940d40746001c000802040f507034510604038600115010300d1140c090952401c1c0000c005010142c103200040c0000c0d40500000c058a560314440011110001c1c02a07500c101c0d116205140088003820007e41400045a003040041e45440c040000040808031800d0b1800c0a5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369378354 1250 369377104 369377117
    0x1c060f140901061b1e0320070302090a050a0f1b27031b24030c0806031f06091a040605010504030503030a02031909060c0e1e13060302090403080604051e0403 69
    0x45040444d104002410783d81e818044150020061540003460407103c40c0b032110505180c00c10300c05290740c448d551350100030350013550000400c0300441e01e500160340101d1a6080041d082d4188030321745044910301d0b161000c00108115040304030341d0700210560540c07060760010401c600300c0392103424200c40d100c0c00000c260f10320200300c40240e68800c00141018040d103a40040010404040c19000f01000d214150006070404100e114018403800c5294010300000e401044294004600c01884145220205200c25907a40300040e070300495000e000104070380d10391203c0c540600d060600c010f403403598000c1030500c402000100009503000003165400341903254010b890f40c65100c400940029030382c08001415080c44030241c02d02c142035001c00c0102409845030b484480114051007a6542c1d2904010304400b07000c0054040350400f200b40c560800c04030000055802c1c1c50b0341c0003440b21007040d2020b40004182c6030800000e4105480351135001144e10b1028682c2401c00c030300359040b2040003400101000780 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369379604 1250 369378354 369378407
    0x10504051203120a06090c090b070b04060e0d2a150906060306061509060e13090c03020901080714030a2a090203011409060a1401051c060f14090106 65
    0x30700b841070340d02003681600e015800e8240301c203880b400752629008130b0032441d28199003100c032280503020307160403140d0500c0e4050401d0050b84982c1600c15008006650054481440480d40c0c0740500142001c10003544030581c41911744c40201404844100b446102c0d030009003040e030045043c0883d0014007040440010455040b00c2c603105002d4009640018525800c100700841c81c2e50240303210305101b443e1692151000380d941c41c401c680b82c60041d108190802c2c0b5210754410f1441c0140c000c50030039409840011541c4d5600c1d400304680c0a03090344104c64642142805000c0341c0341c80c0380d850b04014012001044440240d0320b52184001045400032201e98010a9a02c885000d195800d070003040c0c00d1204540b01d69458040d507100741d01d500c005a1080c080040041e8042c80c0603030341001950146031380034003001507050064500391300130030301c0095121000280200c0d4003c01c3c00b5400c090718036000e1400341c2d00e103450350302041070440180a5200b24034802c01030200e981c0c0520f01d0b2004210604080b1040c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369380854 1250 369379604 369379639
    0x90519050102090d0f060c03090c120206120a0e070f0605040b0d09050a050f0c180a0207080d09050a02010f020307030e0907030b09011e15050f0304020a050d050d11030901050405 78
    0x407540141c035410144c030f100420140110005040c0d02c040c01040240040c0320142012030441e0b038403060041c00708ac40d00b241444101c0c40315101c00740d0540301620940ca401d0000c0d240e50302c00d11007228001e46040e110320318212002c40030f202503002003040b141c10790885410400040c0c001d01444c018a400180c002c00c02d03074052541d5030031880a141d001001e8450121003814982e0301d45a1003043c3c5030440c890300010800c1c0e07040400c800c1200140440e0707840b8494440b040040040e511054040d5140700b003d01c8000c4030000e541c132078071440d68414001450744188900c009085076440301070039800e5400601028000c07036009510401e0b00d007030484121001c0d6032628010750090070b8011105402c54209000410805902181294080f0b5460b2100fa18555124506100c2c9211100e03580700007902030100d4202040c00601840d0028801005131480e551140003194000309040c2c1c003500c842d03205034482e85280d50003400d840602030f039207405149403030042d10002e069445544141d5018400407801209840d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369382104 1250 369380854 369380857
    0x70509040c21050403020d3902130c0201050609130311030c03121008031e03040f1703070806010201020a0f080903040b22080307171b010c05070312090519050102 71
    0x900d0524002e215503281d282040340203180481d000c50161245440c100710080c0180301c400c1c5000004208180102020390010b103c10004403214003a010042e4488801642d440c003200c0202240c220000032489082c0000030300356000a071060b03018900e0b440601050865842500741d030b9903098200ba41e40c0110103015903256100302029644503010110f000110142001d501070301600120714080700e4152103450f81a00e03482078031002c2c0300c852000306e1204c08001c640c101440c0e0040c01444850f4020030151280340401030401460303c2c000d0000420000390a400012640e0084000c0c402181805220301010f410700d09441407075400e0042c800d00140d00c07140100200c6010741f8190700d005440e4804d02907114010940600301071340c240c10101001c14104000000e540d40e041d00503486103040e00d40c0c80c030b2a80d15548406000030401c09841900240381400340585400c03110f0507560284c0d10603060030b00500c152031850310451410304001d030740c02c04100300040d0100580c0001d08403d82d00c110500c2c1480c0207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369383354 1250 369382104 369382127
    0x52a130b0c0307060509070f150e060d02121015030b220504050f0f03030c0a030905010c0521060612060612070801051f08011e030605040f061103070509040c 69
    0x880400280d4140380507012000e0400588034803801c1c482e0341c80310000c0c5a101e5050b40103251001c0c0091404103c80030502d43c400289140300d0800003a207910a8020601550203d0f148101c100d0b00041e40c002030030703106810954081781d0402041d5409040401d0a09514a010460400c25440300661100b0b0707034691402c06801c40c03121801c001c0c001030350300d40e680140000322016290b50140708100d4107442808190003a00c420518065031840d5160240d050481d008034440c4000c150392942c5110000b1024400c0d10003600c016121261600c1750f0044440600c8a0458034040c80c04002e4140310154554009a8924040300c1100380403959030040868418050700300304002280113041441005600180011305803081070381d6034100000c0081204002d02145600040014940c000400540394160061038900d034030400d03007010843e40c1e42c45050a40b5000d81e81501c8500f20181d20a0801089114110100d020004442e00714500907001812900540c1540c80c040c2e61582d400308042486544a03a02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369384604 1250 369383354 369383369
    0xc04061b1a060625140d02060123030a0506012c010b091206010303080a050a0506010c0b04150e2404030c0f150507030f06050108091020041206052a13 66
    0x2a0f508a2400c1c00750041398458080c0c039144141c2e00d007906074110200b25030304084071980003003a8507442c0c03018180004091007600071240303084425541840c1d4091003c540000e002ea0002c0600d54103041c0b00110010600451307004550700000030752181912140c80504444005026984503c00c18010440303155500240c61f11034000c5d4000442010307046150039000b284811070410144d659400110304030342041d034110303000ca03030020403c1d80040c0f00b000c01c05911601c105000c14a810140e00b1f00425140441225280c5810501000d100c01000b0300c4000001244d07034050801c0d43c28944c40103040410514000342840030703500c050806102d005c548042500c01800c40c200824a001e2800600a000503032540002c91f05088000030207603c24461603024904000141030200e5040e6a444002c2070708411013030302c501030008421002602240900002d10040050410800c0c252905204403070000300070516a14081400d40c60809414650140c508a440343e0a41e840081040c48980c0d64610307802844e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369385854 1250 369384604 369384637
    0x219030810030f0c091406060906030402030f01020c07031407140d240b040b0a0e06040e1603080901110708060c0a020a0c030606080129190e0c04061b1a0606 69
    0x104030381c1303220810803610308801c05c000681d81e40325030315100c1301c054400680c4010300f8803139402640b812200454006100408480e4140040208a826070b0000040d0241d81e4220050410912084103c80307948440e1800140942d642060104020100011000e84c061612010355804001790080f07540303210780c60101445c880040f01c03090b40b000762202c061014001c40c14940b5110b12800c0a2040c507041d203510303c9144000755150818000103044010ba030340828400c109a1a2500301c0240e030001c00b07103002c3c01c0341564641103030300003522090845110b6409584454410071041c40e001c9026a045904600003903920911410100d10300202d40c44044c042c107849aa00204124144c1c9c40b410450f80004000e1140c1500d143c1c50011401c0e0030a40c207443c0c907561102c1c0d0902840c000a4044804c0100d480a800281d01c80001c00c0e0403440c110740000c0c50301000103060011540040c022000d1507807030000004084425504d42045106007a64160942445004240c455860f2010354406409401c1c0e80c6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369387104 1250 369385854 369385883
    0x1020c0f0a1203180b1f050f0f102303061504060e10030905030307031e111806210603010f23090c1203210f01030f0309030f0501050601020c01021903081003 69
    0x54075514034a500f20380328a1b03980b080000f40c600382102091a1541e00411441e00324405205100030002c2c152140001c110042001c0e072481a0301c1e14031080101050000b494036407503c9410300100303021107618014050401c0c40108440d5a0085503001144000c0e12002000c2e0309407031058029041131540140203010110801c803450354943e0090801903008103460031204100d0300c2c3da404440c50201c90303094039107003005020708036803000603010102d42c070107003c2a02d840b20f03d000d903440d000000c00313040d88000f4030034040c4623903450240a5104078485100302080501545081040c50069843c0c100a031100004005188070406002c15200300401810100700c07070302c00b100d401381c5030380c02800244203501c90028418401008070000511030b49444900403150b0742540c495040008030b5001c114200280a00c021000903003416202c50058070420010038941003107000a030030100d607030340902d0440d0f00c44a101a003c8201085600c00c1a400d410407504603190303825038408031000f507000508030025040b0305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369388354 1250 369387104 369387121
    0xa0908033c07021e030f0c0a050703050604150507090e041a011413050106020a1509021504050907031125051c0801084b01020c0f0a1203180b 62
    0x41c68850580c0b07038241e5015580080440f803551410111406460b40180003803000c000c5214001c0005d43c40721001c440712480550b42d0245022000e0300301f1100d1390000c005100400c46190703001e86003402801410300040c0740003907006102d8140c0c0d2152210f1101410089414010b15001c4083c40c409040c20b071240f5176842c4ca040489410003100301038040c401d04400620320030f03403074801e4505030380044d8041d1039290b1083d110030003d00c071030480100f110ad503188559001a9a5940103d030720515002141d40ca541c40c120400c62181d00080100307080c14208151000c80c140401c04481d9070b81203050101a00b8200d601e1042140c43d00e00c40020100c0c80f40040a40e8804c0807050f400c101820315641d000070b02da80b604005500c8140941c0f4048200100c1c003401c9090040c1c0b8445880840354800403581c6c40c0d15200a1007540c02212540800c480e503002030500c0381c00c0c42c14090030107a0104040140790750100d5958039075200119036101e004141d80c03000c8001c100c00c0300c41101c5a106401c80c18207880c90409451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369389604 1250 369388354 369388471
    0x4031b0f1101020d2f1f0c09090207050d050f09040f020304020913031b210c0209011a07080d0605030f010c0905010c050d0324060908060a090803 64
    0x41c0a40588914100c0c90051440382c42d20444a24804060719540c10501e16041c01c1c1c83c00301081008140a00200c0c1d00c0700f05040c1c100040d420b035038000301240e0145050006450031280e43c100110142c010054400481c0000840b154001101d02c1d00d15500c4081c00100607a5020398000998003601708401c81140319110703000b96006500031074881c034464988070400b140498440d44005c01181030404903400b03124807400d960720818014459601804580070900e40d1000c0110241000305100121480035410710f030307103900d0241a810b2750007031454088104095843c021544001c0400000003452405030b08113820a800520014003221000d140f0304030314030b0103424000f1020000607070002c0001881d41c443e0440326807040d00702c03010b0b1600c160035010460140104010303500c140600190320311104084100c044d0003d0109030b07036194216003400c115038108940500341c2c4482a040030101404600d01700100c030740020300801340000c901045141000411261110f00401a010400c0d00400900254 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369390854 1250 369389604 369389633
    0x20318060d0c02060621060714070605190609060503030d0b0301060e10140301050402010e0d06060503070b1806030405030412050a1b170616032003071e030c0804031b0f 74
    0x8461001e1600e40303044101c00f520841b08981900d920000c040380d4014080e41c000700385a0425810645421f540b91148019030300d065400030011040a0b042400d06020307441945d001c2c2c1040b0703009105039440c010000e40d40340142d00324a03003802e9943c801d03005144c0c0c00750311010003410f003018a90400c1c904200d580c07042c0c01541c454044031405407001fa078024501803080510803a8140c42d100800b01e9400c3c2880441c4945110840765240e95043c00700f600d95080113201300414507000d049135196100b440845114400e0000c05004010034000d120010b2004002d8409860343c0c01403260f000101810b05524113440d42402801001c0c0072035606144402d07118104041d203400d0115025a0f5858081c2255100022140d404002000305030402e4824030135002400d16500c07074048a800d40c5d041015601c201e500030b0301d015011a91039940004481038046004e00d070713003e0608007048101c1c0003140c050524000100003c04100440d015500b11030880f01051102507001200f9403159012450111117884420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369392104 1250 369390854 369390859
    0x3021c0c17030405240c0c0102090904050d0207170a080f0415180501080601120c0c080c06060f061303230d0e1c0215030a0b09131a07020318060d0c020606 68
    0x1124242030b001c0f0700c60380c0040040d80001182030715030342d01648003102d60005d5400b46008d5400300250705069a514031402e00aa0084010f0403402189800c040e01c2e00d1110780c02110240c00f01104c088091600cc50801e81e0142c100313200780da8501010008078082e220b07d030448007114600715183c032a900d92200b0b01103c40e04105039450f008640b504015941420308948240c0000c565600c5201810059000180c84a07100c1c10181c1c1c54600d10fa4403a12143c202c807000c0021684040c040000c1454050321181a080e0203940c4d00b032418001c3c11104a40422038040a40a044034050050808961040ca40005a9410185c9119411b210f40041c4440e80c56005c0c0ca11800505001c2010201142c00024000358014894071080c41703000101612900028140b004880e5202e448000755180ca4030064411065a0b1402006040c94603040a0314600102117043d080b41c428104000140c000044072030503d13041d40516507072804000020700074400c04c002a540f00c0d080c0038615000907000120b01c0d000d071904 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369393354 1250 369392104 369392113
    0x5010206150918010605060403030804060b011b0605070c0b0c0a091403071208120108030309010509060f2212090623031605040803040e09010f060303021c0c17030405 73
    0x350006414048164030607207a1201c5140c0125140b000c00000000c031029600c1c0002c60041e03511000201c044e0044e91080c1d0210306103000b00420000284100d803c51542400c00e4240c800305404231201464144000a000aa40300041903080b0301a8075903014032648109960034904c1e041c4a0b01c105c90700050000c0c40800c040b22004a500c020030404415001c80160041c091a441c1c04981041048400d5041e5000a41005051044109440ba0f80d01030104100115600d092800350b150868030010a106241d401c510203002252081002c01c54222840392520103500803184445180c1c4600850010942680340d0000060550802d1361901140c0b59921140941581007242e0a003400301511041d844000800c0000c80003016040c043c896040b05141542c00c0c07a44400404d0301c6c540c0181c01c00c820b44000d010400c01034400c24002d401862244c05000e000c268610740d40a565004441d84d610004201d01400e15215841415044110b5800c001c40501052b00d0311061400c5138003d9800340d845004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369394604 1250 369393354 369393361
    0x130212060f0f040f1107050706020d0509130509010b090405100b0d150203070908010204080604060609150603180b1311010c200a1d0601081f0e0705130b0405010206 72
    0x40c007054104500350003806040800610500f00701c0240302c52560b00003119035a10302d02000510107070182c02e1142c4240010114241015006442c08400d070100808200080100040686860240300c101014421002c6810b441c0c103800203024080604105030010902c504001c01d10400242a02d10041190410007440c6000300511070507220005029218507903030700301c1c0b043c41400c2c0e81c001e48d4841500e1508060441c1c40e0003034242668015444084507a00c40da080c401804040d01c5123500074148031008001d2100009a00c1e0016a8148501d200340b40e5076004c0002180c0f80410034034170b8564005030300b100c1894101010b80aa00059100b07235080050030b0101801c55008181c000109030b000045410a900424200c66240d1600c081c49030704a5004400098162a00200740c1e8920404403402040d0789040300005081e901c3c01401c1d15402009031200c0016040014203d50944400c00700b1030106a4500a051750076100e03035a004200918250300004c2c0c0c450f0007501400c10b42d8400d80c00c2d10203c0d20b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369395854 1250 369394604 369394609
    0xa030c0c05010f0212210127020309150402060913050f010614071712070e010f0905150711032406040b0906100c060507020c030708060c16050a0213021206 68
    0x5a41100303c0000d6405010308822101c15980a04104d044900c0c03203101108100f0040c02a51700203a00400101408200d001d4862352250011a0201c0344001d04505501d008000182c1e03502c4400032480001075864082010f40d00c900c800c5072110100030b800c072740f01040c00c0c0140d5802003200701c0308061104034140020400c18801d206485292a40c40702481c241149600c51140c0b10340305400304403029804004041c03100d10007134845803090085031540600d901c1c5850000d8494148690800c0811602910910080d0b0360b0012554140e0070000689490341c04900d03140036141801c1102ca0b50501c40e0b044c035054507000101c0f034000c2002074040b0072302036905d81a0605c8280c4002404081d0300800c484005801d50914010310081040c4614107050030201c15100c100444005450740f00c01a041a01c1c3c119440c00c08001007001040741d03100502c41c91519030000d40c410300444004039850000020756000707101382004155461600104804043c0160100c5480254080b9180c9000025140700064640c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369397104 1250 369395854 369395867
    0x90c05040e010b07170309030d050703060303300c111009030f030510060e280503070e15010c03090e100303080c07201201060b0a090b040609030618050a030c0c0501 72
    0x2a175000c2d07030118100489601504564200810080c1c0d548401d0155100e207070204d0103a54010369942d1400a030b03090443c100140841000c2c0c52458807010380313158030800c914005071015505e032540080000c04803080c840c00c49801c1000c001d001c0b8103101d290800b41c2a050355034001c4a8072072284e142c0403c00070f05030405170300343c031000c85516403001003203001001414041c541c8072258807001802e21171000b20007081d407510007148c0e6100c3c8210780c0341441c05110034201000b544000e0005007280321001c2c501020300707101444800301d0341810000b0540c0104205400350009002801140e20344803482d15003640b1480d0711840b03900c416800141140b002c01d009520380c10480e0b9640d908a4003240205c21582d1511454001111129811000303001602c10718603001c1c8299409042e40007a010f9441500300c2d00209420100d030004140420200004c00c040c6802c01044021a83d02800120f6a241e43c2ca80115510b80c0e0900098000c4c05401803140406a00003040310f40c0c1441081505940342d140c400440e9503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369398354 1250 369397104 369397117
    0xa0e0a050c090a11221e12021c11041506270503010e030c120a0f080402150f0702040c02030c10090f0501020a0f090e041e0c090c05040e010b 62
    0xc907044105640c40c903080020304150710164014012030f0720110860300703400c030341e102c00a10003103001d201e859417420b00d1900c40000020b0030322401d1240b404044007898822060380303210f80d0514103c91001c074001c540300c24000c0080c055518040034600c07401410408020096282d2440c4203030329105140620302001083c400035960107a0300c201c0f0384418a040304a80700081c0801043e1901e082e80002501c0d9000d015401c40182503001464446000e11002d0b494484010005040c20005000c01d010440d4013001e0700c4101c0b000c0346000c3c030362030310f590002c40c0003000f12aa010300360000c00030300070380c202c0c03460401020100e10a590411401c02e600030100e8490159010500780754112403440000e4403915000360b800e0b207000e0044e031084a142c1e5581d03079089a0050352400081006070407095103a170341008c4404d0040043c3c034400036251406558a661038034a451652940300707801d50404007441f130611104009002003000c10400014a1800034010341c21920917035001404030301c00400e50300c1490050780c41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369399604 1250 369398354 369398363
    0x306031e030c0f1c0f0c02031212010b0c19080715050402030d32040504061d0a09080706180c0b030108100614012a0f020a06030506030a12170f0a0e0a 66
    0x45003d815081110721700342c480490810800d0520503130016035024411943c458500f040c886654070001c5022400158059200c065440c0c42400040a140004903584001c4540d03050745c142d04444a1a00300401d009158001d017012042001c800320841032a4049030255000f1403c4400683c00320400f1552002118807030904500024000140d151f243d010620b00c820000120030304103a01c803c08101114000d03130180d04000c00c002084801030070b42c0030002d40c00958140007032003203c040d51103842c410720503d08018030369690344014103001c0030b44070b0000140d260301200a0300c25079a100e5081005400038002e14005009101442c08014030500c1500104c80f56208141d5444094500541d9612581d60030121144103c40d0321100c0c1ea46110f141d546a184101c1104a00400d03d00500c4040b081c507400000a0500c0c1105104c140e56002400296495101c520b600c09580c04030b90031100d258500503c502090b042c4000d021000c000603c0e0b207840740c07641c1e40041000c4402020314680d1030029000c040d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369400854 1250 369399604 369399643
    0xd0f0e0109120f1101140109111602100c0605040f0318060206010e0402010203040e1003150920040f060e0603010c020c2d1c030905010203030106090b0306031e030c0f 73
    0x50b81c40780981c00396210743c4031a08004070451880b00805003561000d058503ca440e4000307006101c1c070700943c0710301000560040303507480c00c11a00c03161500d150414920068400d001d560080c038120b40c45440410071a9078815000e1115007458502110070040b91503007100460140101c3c200c06044a00d003007808c661280c2c1c01400c039646400800000c00002410a034114001004041a41030710042610b000c0c04142008480d410302e9402e061084442629085014908210749500072650b500050703184124510650420300c40084c3c00240144040242c441c40e050402500261145101860300d1051006074003d001e80d0817003407400ca80702d10703200b00c1d02540410f81d500d0210441c05220380804030190140300c0701410780300820008021054038a0b601d40f51b4511040780808260b8001f1102c03000f008280010b5085505000c409000c025a901400c072440601000051596030700300901d030310717284181b00c0044c104041d002100b42c40b584450582c1c13907240300f04491522102c2c0c2c0051164810648212250b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369402104 1250 369400854 369400883
    0x306030a02040b0f0d030f12050106051c062c06060f030415060f030803090f120301051201020706060f051807020c0913020a090219031517070b0d0f0e0109 68
    0xc0600741c11640c1c1044c1e40d4001e959007503e07800f404a62880c001d4481d00c2c407000443d0390040481142d0b00720105e003141440010003145400c0015034001c0c4c0320810301236171508103d0300088000e204c0c0754800c040c03183c0003100c404400c4446c0d401d82034900b403030308219240b19641d8100b48102d622440034065854402000000d0210b201c060001031034107940032010a803c2e5840b4001ca110040f41c3e082620030007000014400d0030000ac01c0090780c140131500c00b40c088891800fa00840d0360005228050040d0090400000d2103a400c1d41151241544103104000e180c1e100c1c11110268001c60142030700039100c0d00010800d2615415030703244205030580c014060300036000140903c0074009416401440aa43d12240050f903d909031240609141c060058882c1e081e103803c13030300624680d41c9078014036141200110710000c6000702002920400755020100301030002816141000540c400348050502041e42e02d490181c641007003080014900c01440484e00079a1800d080300e0103083c000b400da80850050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369403354 1250 369402104 369402109
    0x501051e0a050c030706050a050604090c05060c121201090e1209010c0f0f0f02030c010306060512040c0f0f030203010f0b0f2b03030b090f0108060117030708040902030f010b0306030a02 81
    0x248010708007460b0950034545101030340d5146401c0030300c08a560680b20303410040b502c100340c8902a80804100c43c14841c0c01c081703844522002c102c40c0941c03801842c001940362a030420030400d0203040402240440c1ea541030f08041c03c814130000303004010b8801d007004031142e445c14001070500d4800016103c814a40b49030782d001035485130a80c00c01120300c0c074810544030022481111104040300c4c000c070001d40c0400340c648100b50912005403402c1c0e050518218080c40841c0c2d010f4180c0d10340c100300800203d00b0303855609081091701e0403540070040e00300b290318002c42d10001103120542260b100368020302103200060808401d8542809100d90050070718210f0070010319040d04000c078031011240c0c04d60b404500500c3c81d2030041d800c91b01c040c1d021a80300e8995410604011088c02d0b400220b0044030b50155041c86a02030300ca0380706110344c05200b07002d011015001ea409004440711158441341c25a0340f02d96600e00000a500216802000c00040200004020140c0300407680700f402c0c0140a085880001e908 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369404604 1250 369403354 369403357
    0x9060f08060f0a091b080d1701060e010c060207060908070b010902090f1009180207020a0b041a0c0106050a0312020c150901110307020415030b070203090307150e03010c180501051e 79
    0x2070964102c50380e400000070171000e11004401905490025000c000c90f0a103002e00120010684903442c00f03900c0c0c004009441c1d00c1002c50030242d000340780040c0d0107880340c04c0502c040c0c0030716079020300140d1802c00000100100e40d0014a5440e2103030074a03903d96a07890440008a00441101e0303900000c1801d0400781c10714102100140f81d00480c00d00c001c1e01ca48402c1c0380174481c4041c010441e68143c2c0001e1070f4041d40f60140f8140c0007040c019888a140c54107203615203c1d94407441c000089440130215070540c80080a4128802034100904143d000aa40703050400515540340140b101600a54404108506084000004c400d000780301d0140780000d641c004507000054105002803a01041c444200141d44900403441c00f43c0c091301042e5400c03800d40c2003401200e1400381035503040d944100303c0207074261400b0a05800720b42484003c0460118000c0003a00c0fa05411001d055040d440c0404a13404150030941d07442940c5440020110140d44580042d80c40e81b0986000c40040413501500d00b4a40c201c01c0e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369405854 1250 369404604 369404621
    0x10605030406090501050916090b060a03050405030f07030e041d06010312120218010e091b0304060f0516180b040b03101706040501230610030b0a09060f08060f0a 71
    0x1d0707904650b4540508451098810a9240d0010f2960741800d11039000148d01400400f1800c00c00643c0b900d000490034455100004207040e101c000041c10710105005a4607100c5e940c4c40301640e21040c5182c0180340c82c10006201c2c1c851031500326082035a8000e407184200b031440d24030080211b41d085480303c0c0801902120000200301108003a0601c40700140090122681c04841d907280380210000090302c04c40035116018001c021800c03c009207512002400419001043c2c2e07199900d489500b02100603101200080b00b06074241001d000c0984000400302030081d0460303980c1000b0b06c142214180c8a10307514854001c188100303000c1444040111001107800030340c04080c1103c0b1a645d8048005011030f07040518140750090020001400000c1c00b881e0102030240354641d0908032219120340315101c02a100700e0160880600c0d20729014025440342070028001001061001d40d64606080178210301d0141e201e08001c400d500160168000130614040c00e40812030310710351359680c40304000814003003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369407104 1250 369405854 369405863
    0x101809022106010e01060215130807081b0105010801050c3106090305010e0313060810030605180136050319110d0e060a050a09150203041d0f0106050304 67
    0xd400c104606164036800d5205200031000d807030290b142c0341e2a0349441030141e111b8001e40d0070400000301c040e000c01500c50762159240c0d20315214010a0f00b000441d60040710070050140e400002c0040c80780303031010329032640110280020301c0a80c3e203511155003a200144c441c1503e1260902440007458040304c10b54541c495040b01d91050b2400040c1079810181c45680400c0201d40141d10500c1881428001c450501062100451130b011010070300e90f2105201c1c1c0701c0c00b400c0160340f00105000845982209009641000d0144403a081c4000140382c11601c0003180e5a03290700e0803101000800c4201443c8407100443d1400302c01c42c603e07a000400500d954008119000c0c00200704501c11140c070303d070b1280009a4036a071000003504000b440e680c5840c00140f10f0005200c04890f900881756210b2003100d0074445180382080d00c40701030705415105003050f40c01051107060580001c0060540c00000780080364100c4a5100c040d0440030b5520f4032840382a6800c0d500408098014044a03000d0030085030098481d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369408354 1250 369407104 369407119
    0x102030315040e030711010f141603020c150a030e160e0903120403021b010e0a1a040308040b0c06060108011d070507050312060112020a0e04090503090d080d0510180902 74
    0x2600c3d8035811940108421204840380300c900300d40035640030701601900d901a003040612019051146d0181c1d000300c94285400c4000c01410702c08240c42803081800280d0003600d050f103030209003564400550004811240000c0c036240007032008120009228114003034559a40e1401d501b0b05003243e030048401000322600d4817007004030f100e0b0b503045200c0c21171069001c1d5001e030403624a1f441c10080ca02800a10741410411045584411039551604590031100c58410740523480390410143c00c1103003c2c941c00907000071404100060b800152100806d0700701d0712042650703483e650311001554078802c00e00900307a150414000c40b00b846000c00102c150015450b0901608110302a0b841920b103602c070000c0c400c185802d9005210403941c00200c0b0000e94090440203500304a07552000420700355095000600c40c42d11a440482070090034801c80708a8000540b03440c2040c411428004015405850f001d0340d91480c110010310640c03035000e0f8910948203103500e0701280c0c01d6444418809445507140c1030364000724 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369409604 1250 369408354 369408371
    0xa020a091505130f030203150411060f0c121603030902030109020a181a010f1d0901060512060a0e010b18040501060309021e09130f050105191505010203031504 70
    0x84541001c0900916658560b0750030800071040340e858040c1e40850300b80c1503220307410700040e600840d00f402160a0200102070982d5642000034440180703005643d003203100019000f45009604c0024040301c152802110398003030480808030040d2084240010340340c0100c00c08840045d22a070440c002da00d00060000c101411241c0020f84d042115600c00e044491a0b4030340e000b0003058030300481545500c1d04032005070703540280f40042c00f210710b201044010000071000c3c2c13481040410304049998580941071034990368460001030801d900c50943c80c01c0300302c1031a0002d58240781c40070200c0c00352500400800c420b640b80a122000302d410001161041903017049800c01103449521402d802892030745d60200704121030340180150703102e50606026000345d0200d011000c0c0d4880d41c45035a0860007025844034414840d04003843d41032811b8400034065400c04040c8640389403070886d20744110f00003440800c0b0403001d003c40b01011811a01c00c2070b000d42c0007400010801100040400410200680040b40c0c444 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369410854 1250 369409604 369409619
    0x20d0305280309020310090819050c011406030708060712050a020c1005220803042d05010501170303090607030203070e040e0102040311100806040b1f0c020103050a060b030a020a09 79
    0xe8642180c1d00003a039180d10b14401e500e82045002d00fa81e0640004000580d8070f03440d40c203a1885045050364030028404907140485100318200c40c3e01801c510002c00c890348009180415401c0161031403842403250480120b440700700482d2150240201340c841080408104020f1006000300400c0c8040103a400c0c46581130284050010300c0361000305000005841c504044d0030585104580103c030b00d000401c1d403c120000e0303050b10032650040c1c4c01c014452a028507203824500e20342032074104040f40c0001d42038600300b00501500314a05881380d800d82c10b0001d0708400302d9245d0303a000840e0780844562042d00450306141c001c0e40215040b034004d14003c140100410040b809492928000242a03035001501f00280b010140f410b8058a60486016404c1422950020031134100500503522a80e40c40410f040c2c1541c600e107204004c910000f60b11903030619072000c05031070b281034001c05901080c00c0c600011070203000c91082c101136440743e45400382143c0703c001b007450080d08500e02000c140401880f02040c0e00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369412104 1250 369410854 369410917
    0x1050f0d1d0d05122706190603030507080c070b0403050102190509090a09050f0102131401020f2e2f0408250b0c07030c0504060b04090f06050909010e0c030604020d0305 74
    0x4c000c117a0080545040c606080c10014229101032907840345800014000650b100007160003050700002415110500c0d5040e81e4109255640715184454000500004102040d0064180184078945160045201030420340d402c0c841d01000d80c0d8014104c00000d1080c0c40e10780d005c0c40605001318119030594041340440344c00c927481b01580e4540c9a0101c0c2d001c0200c0d20202903030720300256081c800b5220680040c0855903640b8955600e00d9040318481c08a0349508609070313075004248080c1c100910401c02101c403501c0d03040200010460480304c10070391085204140c1c104950407182c0e0b81000f445001c00003028180809985192944800c1a4100018800b007541028024401c00301d0041c0c90401d00c1c501d44402000004e0b800036003c1d509009081101e40f0382c01007910203d074013043c00402c001e4080605480180016005603a12090010600030440c8055001021541c040700c203c4000703da060741055070321581103400035408030f40402401c0010340308002170300c580110a414030012300a40f620240b1031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369413354 1250 369412104 369412171
    0xd05070314010e0f0a05060c0a050c010903030506100c0c060e120601350c04020903011506020102270307140109030501060b0910030b01021b01050f0d1d0d0512 70
    0x1503030f4488000754424041400041201100e103030050a8014941da01d00f41c4498005103034903010540407900d450700b41d0107042280c03071110001c80204035541407807401a00034441550440e001d211003400c04500c02d8050581641400e403c0181c9010451420b031045410004001d41d464215800c41440c8500081c00c0107158040d003100904211a03a05003203504031351201001054240c46200c04900074144800f007400400214203450140e030342d889000101340500110808100e0500c0d80010000704030358194090403100a0544040009006007580e04190b0b420a007185513142d004200704120038007440c90030000c41c14060414490303c80d50b9495150845405900034200c02c10b002812800e0340c504259a28544140341c1020022980400300007076030742d0103480041900030255002e0030b1071607000b8000d0340e00c00300f582445691b41b03117103000d12000030340285c04d845201000c01e01300c10b02142c400810580c1220419a4900b0704040407501100c4030704030050849000c030b454201c6d20240b40340c11201055007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369414604 1250 369413354 369413393
    0x20c0a1e02060c0a060525080705270102061006091517090a030f050408190302011104080a020a0e0609040305090a0b070308150406180504141e011406010e0d050703 72
    0x840300e0f00c504194041d503200410080c8500d8202c0180070040c0303107103075080602c4446232030040c1a680d101e580035105441510004543e140003002405000c51a0b01342c0040d00030400c2c1e080d82d49a403a02c5060341101c1b500c90040d130000c00c0c3c0110041c040383e00801826440420185050750b4260910300c8500e4064601ba925104180c2054035a0f1003032580041c0f000c41c0c0d6107003034500145441d1401c00344035203904402c020000d1041c0307140c2601042c14030135004007403010100d603a01c903590b564a8072019642c42910404a000c1c04010030002840c80100c26075904c11803000d0b010a0f1555034a941c01c6031642e10440c07840390b101c12001408903051141c0c1014090462180d1900c0c040740c1840034901140c1d00c00002410301c16070500b0000e100352240b080710014100500d00c000f28840d204c9280038032503129910840c00d1140708620505880340c000802e1f620034600c5a1000f0044070508480300744080030225441130200307031200c800c0c400c20300380031100c0c10350103000b801901c1c0c0050b01c030391715140050010b107083c9a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369415854 1250 369414604 369414613
    0x3040506071b051018230919061508090303011d0702030f070809120616050a020109051603031403010b070f050a050607120b030a05100203060d1e0b0a020c0a1e02060c 73
    0x501c166440016002902401b0406102041c01d501d8091042c081d6040d02030049454030701160440d00c0307040d480d00a0009140341030200940ba031403128000c62443c810000002c08441c04100544804021241614000030902c0040c90f5030750005685030070060008030031440304004c0d40f425100981e01a060407071190310440d80d80c0b01c200d401c000302801004030510886d00b0040c00d0040500709152041ca8442c04c82c00c0c40c070f442d004481d90603401002a07520251070f600400040180c43c825859681042d240f0a40f40c042c07035100c42502030041c030f0000b402048500c050030402c10300442d00c850130307113070070280710304c0448803542c0f81c90703031600c0c1008016605540803c0041800100c0340886008644060200794010b10032010952281c9540d180000c0704085100e90000102c2c0c5c140d00ca84001c1c902c900e4009207001c140c40c1c519168008110340d040fa003590b91088000c04a100c0301d4132402190142ca100000505d5500c0a54480f074440301054001886205103a00b0320b000140c8461020f89451f100c07600151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369417104 1250 369415854 369415877
    0x4080d05010303050d1d2503060203040605010504050c0c0d121b0c030905030c090a050c09031212010e060d02130f0905010e010e01090201170405070e04060203100803040506071b0510 80
    0x10030340d40000c00c0c0c401c890f1025401e800d2111b40000b11030301082000040d582c18015010211100c501c104d4201504080c000802c0200b4070034203030403d80c103c0d081500d0400155079401c04107185400740100b0300105030805044552840d2042c0c42d802c08400380e10200081c6a40d20407000405482071000d88000f00d0b4950f1510303010306400860401c01014150064141b021b507180024150010040a40c010f456680340030a0040c40e515041ea002881c02808941002c142c0c40038041c140c1e0000c181005400f1f4a040005c070351540381c3d45c141ca000300e80c05803c0301402402c0354200000c0780d5840c000107841c1592018900d9140700c05000d0400e800b4016800012203941d07442da000d0948904058140036681401513040050760301002600442d20703010341c28110390310b03140752441c100005540715811416000c020710040c00880d500460280c0c0740e4a14001c10640c0c0c402009450380243d116081d0f00484c1400302402040310043c82090854800300d0b082c12280d2914001740e5100004851840010782c0d00810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369418354 1250 369417104 369417127
    0x90402040306090339050a02030d18140105040e1f1517060303040611070e070e09060904051b010315171005131707020d110a050d05070302040504080d0501030305 71
    0x86680451302c05001c04d2146a50030041c0d20302c1148040c1c0218122042d4102e0040c040240401f451f03490b8000c099078031994030014000c08043c6540300d1041040c0760034800040d2000fa9152071080d401068443c503081a00d070103c2026000e000034006d41000400840c6d8804c03e5159044080140c1040310b214000342c40030100040c08951900b950014544114003803080565000065034100d801d1894442224030425070311078208031040c1d00c03200003041104140404207820005c4140030f40c90954158101d130341d0f00c004010a200702580c02400940000c0503024100d0202d4180f425000c0042c100424003e6840441c14000c0b119940900784e003450300341c0c41070003120081c0008050342070600f10a0120741040c101181e6154020310004080d40221400460f801030110b05071703038025070000d1004021398424202407240c460307207501440c0b140042c001d000c030769490700010900c2000d81290027840018110380c28880107050260066170040000d04c48156034503800d006440c007862080c0ea41d2502ca4000500e07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369419604 1250 369418354 369418367
    0x1e12030c1d1c0813080a0210050a090513020405030a08120f0f07080403090503010203130209060114031609030b07030e0706050a1706060f0a020303060319150b03030904020403060903 80
    0x304080149211034420307000b5607070340d048448800024480e8a040b466285007902d454880c0f41080c90030308400759400107541602050511745103000b580d00309203502002808907454490f40004c000490410141400f25080c110550034200742e540c02c00514040e00d07000040e2401e080c411044a02c19800544461880507032158260003000300040c000e00c0d410103c00015440070000c05401c100403400d00040c003418807840c1c0c0c01d0700a00c40500210f6481c1000c840791100612054001c1c0d000c2d0300c2100104502d94894005840070701c0455880754210740b01d1800001c0b035030340a5003165041015240c0c02201040b10849001e0042e0b589441c00107a801c0f08a0350b150800354168005014404103001c08001180c01ca4002d000010002c42c10b1041940c400c000509c1038002c8440340c4000d010082510600550000000d44c0580c100b14220307416003010940d400c10b0660402700c0286141859020140d600c0429000b402c504500101500e06043c3c011005c9012a0007543c02640c00c11303191840c040600d904030b42c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369420854 1250 369419604 369419627
    0x705031218060c06010303030c05040f15021e0a06091b0612050106090302010c030305060d08130303021c0509060c1005040b06090a0506010806010c02060409090308010e0703020403020306041e12030c 87
    0x3504981004030f00300c0c10a13240c000510014041c140c40304140c901440c80381c5c0894020b0410040c240040d90703214442d071006203a080301c42c1d1005d44241c180c0110300e0800e80303102a0070040144000d0418841550752200a082514812641d010102814202c1240e6000f08580904003d03a03c80c3c400d240c44aa88001b40e6006070300c24414405084011720150340e2000980b00c00540500b0045090b4880902090041034110009402d9107000304000c0403041540204404586c000e900311800303003420301160300302c003030202040350085082003200c40401d0030700710060300402c0d59407401c2d10f102401a040b04000d40c0c20448040fa800d806500400c42c440c42e00341c13586600303c8000c00c8200f060b850a907001030030075000a4003080c18000d0291040d402c555403d01240c1c05451480c1041c01045020714001d0f103898000e0280c588900070101c0001d456510078801c2e1411660000c00604158035140c64849582c0c03403040c4990041c06200c035519002c80d08401d40b02c403001d24070b1764001801031a1320324010124000d88 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369422104 1250 369420854 369420859
    0x203090a200d080304021306060e01091d0703051008030309150114011205062814060f0706110405190e060d02090103060c0c02030a0f03170c1602030705031218 70
    0x41c1c0828600d0b11010001d2120941c0007503140c0e80d83d10340e400041c0f009020741c410146100e0074207501003540365200400441d01c171001e8076030108503501d944900d0b00c4040784100c04030206401c2c2c4001021148a81c11190300061400302c150882d41e250507000e8190340c02111900316034ae11000c43e01d95506640c01e10680100303a8003042440c00480000000d1410359611035007030001e5102e5011031180d990360be000480d803140d69200010020111203480c03000ca0400e1140840c01440d510148c022828054102e0b000c01c50008103045c544001a6520030041040340725002c2000001d10020819840765441142030f4581c115081074594a030600c0f021054000404260003000d1000d802401622900042419240c2c03060000c0380a0040300d504460035000000702070360620501e0498021310841542d25500f0b28020783da00001d018840002100c151415140920480f00400041c12008103e0054800b1940700070151003405a9440002c2c1c542100300b94551140000007801002501e00030701c00c0707103010909 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369423354 1250 369422104 369422153
    0x14040c0e0a0e0606010f1b03031a0303030f0c0a170c0c0705040b0102031b0102090604120c060302030c03040b0907030507091d0a0201050712030f050f0103151514030106090203090a 79
    0x30b508a5944440000e0002030500c03d42c2090007004a0090011015000001c0142048030469043c002c015116581c45001d2303107405141e0301a540d00303011080342d104011a0101d00c205440340d4141002c1e81d0302c15031900f010450100315004040da020303e100e0740102005d80c84191120f221055041c01d105e501d0348000c1c4114a040404980707032360088144d9101d96120490070300d01c80c880613240b901900c41c42e202180d2204d80040c01280402e6004454041c0e180501d01c0c00452940f40e10b001e60480c8400c1d11040c20204007803002400264810554980c0306080c40162581c80f03640c0d43e10706140640300d80000340216121011a00400c401c1071041502241d40b80040580700c8203134002030014840c9040c00f90243c10303042d00382c40c000c078000d8211120054050a0802403840c1904030304039000000c1c08100d50074100f1040082c104840c80c041c080c55140d00400b030080e182c1c42d0000812952604003803054041d5228000041e540c4500c4c03000d90301c81c1142e40c3c0940680c0303101d8501341681c1c0e0302800c00404181035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369424460 1106 369423354 369423371
    0x6140d020406110609011103010905070c0b0a0b011d06180a030f0f02010e0f0906040e01091401050708130c14041d01060311120606090a14040c0e0a 65
    0x940f201038510b036032a050945400da517014107504240302802c1c8018401406168807864112000303050000d510450340d51004d15149044a0402c6803a5842c1d6075040f155070405000c001c01d4001c40101180e4007600d00004009000e003a060030325040e400c4500e40110349940100030702868100199440143c8a032402c4610025010412800541203510b02e14090821b000d00000c1054001e144055540d60081031100800c1540f054030010342d2142180d2000ca110524240c0602c1c038a980080ba4074581b621015140c2c02d03002e4003250840710395106020100344a080004182d841090a25100c0d113103880000340a40004860703050401403922650361050b105600c88400c032441400309a007142040f50030010100012000c00046802280c00502940790089485500040030a0009584c244032080e0b82e1152a0844e02101c2c038138400c0805000000d20701001300d030f01a030b0b894000c1c04980b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 369244604 369424460 := by
  have h0 := BRFrame.cov_init 369244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369244604 ≤ n) (h2 : n < 369424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
