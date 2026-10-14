-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3700
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:25:01.787192+00:00
-- url     : https://prove2.me/submissions/c9914871-714e-4227-b23a-9155680ce87c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 665287769 ≤ n < 665467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 665289019 1250 665287769 665287783
    0x2709010e0c1302130905130204050609160e04020c060108100c180501080408070506150310150504050907150e011403040305070219080a030806091302010909020d060b040611 76
    0x290801030005942150209003452484055600180c3d00010b08540f110a030f540404000e001e5000c4c10002c82c9815404180c9100c01e03410103c0c81207013008007043c2c0d1850040103560045400044001c5c2740c10403060161080760408045a0f046038081c00300802d4903401384001402030070b0000251107100000b0079400c0441d96141d007040c05011510105180300030f040402002aa14223080c0701090b515941440700d003500551400428621600041003001500c400401406000a9040340e030200d9818040106440d01c030703405e442d1400401c9000300424505600980d4102e440c42069801c10f0351240e404280e0000c542041001080f4a50300110955901000e40d44034484181d2825080d81000d682c0240b13948078526000c0d10554590550640c039601c01104040103003400800c5441d440c1640c900079120000c00c0701c24900c1807000d080011619a01d12908950260741691194445400c6c600150003d420014406c90419554000030503034a4003c0b00400140c40740e034685c0501d0b0240c80c040b880c5443c3c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 665290269 1250 665289019 665289041
    0x130f15080111120c0d05011215020307021b041d060f0c0405090606070516120c0e0103052a030d030f0509121602010210090c030213180f02270901 64
    0x32414980780b184401e84400d444010b035004078040040d03101c0c89403d00b4039000301c1e80c1020110707240c8400042e0616140c40c0c009001440307041c90030b2042e242064800120b000c21245131000d42c00200380d00d065916003074a189405c8070000d10000d00094042c2010031010401c0e00c181d100d6502031400e00641007020183d140d400b00d03424181c10301e030604140200d030300454007070951400f94101103040c80420000b4843d040c0110003030b243d0f0480b65640c03030600a40300f41d00b6820070707200032010800c04154099031803582c50690740c01c180200315070480f05080ea03501010070b10035104507504c1d1040c450360950b0107102d01c0d504514107a80c0031a00035001030200c421108042c0040b40b150384501c1c00c050241d203081094508540c5840d5080f040003015000603424032400b45003c0003400e1809a00c40c003004641e070b0b90031007680e0080e43d075072060b4680c144540c012a28441800358070060720321420000204d0201e5010a0580b01410315044040300820760540300700144407400c1117150000c10800c822100348540b8111403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 665291519 1250 665290269 665290271
    0x90302180106090b2b0c1206032a0b0a030203060f0916050a1407083f060a2301230316020106211104062102130f150801 53
    0x751401002400405030381c03198882d030383e10124130140744038048031216150030100107415186001da00100c800500d04c0d0004080892625040603030007144920500040d80d81c0441124041600e0001c0010003941d0159808079180422602144a0001b200540f156003003649016889040c020200100a03801344085406000c22800304828021089032906080c070079800e0030f0340c2c4c56003169412140700c0000304445107280d1000581304100800b4000400341541200700c601d001c0141101051154100110102001c0220320903941c2a80420103a09810103002804513800c0d680e5040c2e01e00c140d41d841013a00c0004030103201c000d9001e582005c96030004004030140004008500f4090004c01c1c000603184211071000380c008145014000d6100c100502110001820750100c0e5959800541158240403200b000c40f00c13107415a0350405001d1801942c0d0001090045a02250f0600000c410000c20503a03000b81c1d440d000d040b40301c1c480c1c81034600d11700402030041290202d66012074440d50303d0394020015a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 665292769 1250 665291519 665291521
    0x8010c260a0b01020c0a0f150f050d0e010f1a040606020105060d06150803030c03070212160b0712060b0706060e0f041b080715030b100813081909030218 67
    0xa600c035004825405900380d503001030720201d02c0004034640707007a4000c80c80e005248410041a07403651800c105080760480d05403183c00044440b000c440ca40a030b14054404542c0c00c1c02844651941e940012840340c1c444400050701c50345801c5590290b407075070424448106012201c0035498101030281c4405040d56000a01c003e0400078007103052035644140213840c007070740e888402001c046400340040041503080d080340e4403424120911000d170781c816a03005015202d5603903081c0303400e2110700c1550000e280f004801c280b00c0c2c03e80d0300d90082c00301d8000c01d954104144081e1403169040326102c0c41001d0316040090325107a8003140b40c440102e40480d00a002c01414400800c00d220240e000318981c455031210ba071000d01c580690700d0351448a2540c00001c0640540031000c224080b148615a06108503039500384603050908c0103010081c03040025100005034124002103000e9030b807a5100c4040307445031034442d02e040707207101151076034004007403144002500f003071030400a40c0751100c1c06110180b0340420252403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 665294019 1250 665292769 665292827
    0x4170c0a0609090f090203070602160608060315040503090a08070f0504050f0a020c031b010b0901060e010c0303020c030f12090124140d061a0909010603240608030408010c 75
    0x1441c0b54454011125200ca0001c103082d074464011400c00c0c0c0d805004c41d0f0003241c440034042c2d21400a03910300142e80071200c0000602d14802e15a5502800000d009402441d00c1d40b0f101000c1e03010004c1007543c0601c02006503035080c1d100c0050400c02010480c000d00085402c0454200e0b110180b50302851089050005200c844003088030103030b4000c4401d450040e0749031014003d4900754080d038420b0480812036941120743d07103841904600403400007180c58618681e298541034455112001801d40002c1c0d02603c07250020b03000354000c002201802c021030b41040805005118076034800140d8407011039854041c04480c0400f4060401008001421003451034603580c950001160984900d501416045080482944581c0b006c810744a80143c000c0c000b0320020101c42900160000440ccd00031095031000449160061185038103880c3e2005050181034021802004180b452a100746480307035481e240010380010803c01040140200e81c000303d03031080201c60242103070090448400a0316000b0045c841 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 665295269 1250 665294019 665294027
    0x15020a080a0b1c0c0302040507081303030b1906030e0f0c010c0308060406030b010b311403030c0a03181a0405091902030a0e0f010b210a050304170c0a06 67
    0xa408003016400142c1e5110038800248055030036210304000301c210104031400d2010694920065a00a40f0b00303000ea40c0b9a24003c40c0c40c41b10868250400b49031450010000a2003600714115950004010401261111a00c1c00c0740b00c10903400403004c01c3e0703642c030400e4220700b080c00581218030503540540000e00407000060102045aa00181041103940000d0b40c3d03540d45501c100c01854201a9140040d030f101c1880b0003441d442000f1910070002c11590090103035421504142e100d440540c0040955442e201510010040c0c0b0070b00741381c0c03500041c007120305200c100b0020050000d01a90b00c0110b40d680c02242d9090400ca59001081035407010a00001801016002c5404480d401d031200005581c56a120f0b80821110320081e429460002090080c40700190704504c00003803003581075030030710380c0c2d40e1001500301d03116600c4140d042954050a8138203080c40d44524480031004c0b00c00d582c0c4c0d001c06651110b041d940150094948d403100741a404404890400c46403051117000d42e5410b02860620030054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 665296519 1250 665295269 665295271
    0x20f06090a1a0c1e0406030b09010f1509080319081303020607110118030e03100b0a2d0603051509090606060f0d0204120b0c0403030c0f020d1b0315020a08 68
    0x12080360b00140481d00035a4403e0445002202d142d4000c0104c104801e4035910a510038131491000900f0f00301d404040c0d203003c0310130504803000d01c5460403901d40380002848000c0a050000c01c01d00c1413103200002c00c0303002800200450810312003004840000800007501812000e84200c41107440e0007006000240c0000d030040d0009800c0c01c1940c85030b590a5000e0313014224200d15090030a21807a0300d07008042e00320f00e0720100d0940443c02d40f209410303280e02c3c540458400318019903001401c1001000180424902480c00c40c811941d400f071000c2d454458003e08920075805840000da07100208500d2070050000560b202000b00c40a061a040040c04250346600240c05140314070000078401080402c100216040c110702c1000175900c41c0d175208074024006520703031000d03a1881907400c0002c9255580303034116010b480c0c2c5a251300d00440480e8903000008200c0c180d00b00d810000180300c0c3e40200c2c00090703080414801d0350308005401410f51801c090400c2c0c0001e496101d8500620080d08030581003200070f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 665297769 1250 665296519 665296553
    0x20d14010b03240621070509060405040908070b0f0907090b030606010f090f0320101b1104110d141515070b0f01090c0e060703080603070b0a020f06090a 67
    0x2082c00100c03c0a00c26505044100743c66408003000a1200380c6040d0b240c3c0b2540f003207040c011911001e0751140000d40f118460082c0140d80944104018800f0b0310305a80301031031003409490000e08280030f542d0f40c00050302c1d0588120350b80380100c1c0c013007210700c5c50100091806010042c4c41400700140d0000800d50301c100c0078200d1418003409a8160342864842d183c1080205801d41130201e010f542c034284010012528500314903c4c80250020780c4031810081c0b100c40e04102c2ca076403068510f481e1044050f04a000310503003101d007aa401812031025903031350f00074002101c4005c40519600c1c0d820408000886008040c0701040703460200404c51048800c42c04500388241c1503481c0620504070101a5000307224008008245100c10000d0000040b410300445059803c2c0110030442c01d01350a9041c6c4403851400b06156101e4400c101d900c000034810071449400a20150844124903100c8050200c160461590703080140d005021506400c54200300854101400201410341d03002c90b9243c40300528861680 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 665299019 1250 665297769 665297791
    0xa0c140d14070212011a2b20040603060c020c04060806011206021308010b010206010602031309020903010e2a0d080417072c0106080708040212010902060d020d14010b03 74
    0x11001d64581e1216004ea00008100030081115010034030b1101b10000b202050003801111951808420128a1541910407600042a40060982d00c0a401c109200048174210350000011a4241c43d10f00429001d5441440007007900480640000e00d01000008124800d80c06c05000f00800d00303010072080d06580c0c0c007041d00d0124090605003940a44139005049442140303003040040e9800041d8030400c3e0544d801d0b4281d807a540d0340c6d503604aa80c1c1c000c80244080041565200700640c06040e4001c0440c0c1700081c0000c00c40c8005150920306041d054109044c68400500c1c0c45121522103070502c180c0d007501103a000d641c640305074880c5007141c065402201850410400004a117030403c02c038010083c104513070f1613400882d015524101502d00c0e48140c5124451000c00411440e0080006c1485040c0700c4d0740c3d454a990340c1c0d4003001002d00900262215955807203a0a40140e19220010a180c40700c0c12030150741c50000745c601e00200c4160310034013541a030400700180411444901140c0d00241d0b081d072 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 665300269 1250 665299019 665299027
    0x70323070e040f0902150306090f150415121407300602040f030c14010512040b0a1b05090307090903050a03020f130312091e050d080f0a0c140d14 64
    0x1620f00b0040c420f0940181d40040f040c01c6440e40060100e004620400c400c1d541800c6a44800d103000200740000d40300031058a0304101b00b02d8079070a05501101c01000031443d4041219581e240d480c403904104001036901f8034031104600c0214104000c0e140007000c01a031103079907803251149804c1c84c100001860410f56401e0aa840e803e025954066030054035100301d103400700c0e582c3c1e13241040f002c120354441c82e0071564078500b940040350b00076025141401e220301d506030119521503991092040000b048106965580c0624208400480000700080703002a100c0507a00c0006904041c0303042e19507809000214108081c400c00640c1c001c0540745130a50900b0702684450124011030b005002d540d421544c1d0440880001080c00501540351441000584580e001c280d10303690900b080605c4030308007078490420060100018242440c0806102d4000c0ca02c4504003a600e031030540c0c4641c0302520450009994610130004d201c02d41c0310f0754016a00c0c01000b01200e424412001d02820b6230503068504200000c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 665301519 1250 665300269 665300291
    0xe0604020c070b0a031401050f01052101080a0b0c0406091802090603040807110306011a0f09120703120503010501080606090609152a06060d0201021203070323070e04 73
    0x501a1030400071081c003614101515007a005045800c01c1501a0019042c03190310000d1040b003038801c3c2e05860000d001c2d8201c001100d00107503410b600c0101c6210805042c4054000b02150103c9064080c02c1148060721b490b5020f414001009200030380000c0729030004002c100200b0340c2000f00d0008840c291000701080c14224004da0009008400d003a43c0c101d80300000700310804c10a0300050148911030030644214030000814159500800d015025190a680403600042402e0101800c008400340607850302d400703e0000480c0900203a003c403c0840d62001a040c070811403d0071482c4010360300c2c0d242c07031420341d03141c94002448035001030b01c998001c1a00049159554903114111041c0303900240c52500c42d00119481c03d145584124004814030001c44489040607001262000d1000f956400802071903c43c9010090041c151b580704034150722400442044120702070000e184140b0301600c000410000001c00b445400d0100f0301c091051224070b40c1007005440d04007414061091080d10700040502e050f13 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 665302769 1250 665301519 665301521
    0xc1306051626030a0b120a031710051e03240402013603021509060d020906070b040530070b0c0d18020a09060302011220070b0402090c030606040e0604 66
    0x8090311481441c000404c02000340e0054104601219050343c5021441c503076580584c1d01c07070301a000000c0000300754022000701c0d50001d917801d981201d00480e288441c43c0da81d00004100710342d9142000d0359003540b00501d040914040c4128540500b0820744800600d180c4030300c0c00980700780207000905209004042d02d15440754903080e848840111214903416a0286046001408940c1300032441100750644a1280c82700c02d00c295592403801812040c01d00302c6c1390014401a4100346040381d08401d080c40f10308007042e034075030b58140a00d01a070042c0c081502d42042051407180b94041040c15282c09106890550105408071400700e504641109842d40b20118550308030f20490b9281e00c232840c01c1c0744035030700c05038200a02404207610032118140056070b11000700041d50300501c80a400b040c0d904014068040d03040c0c0200121030280c110781c148500020039141c803030340c100e0041510038100c49400c0004508020700301a07085254010103509520741040061103a1249005e124280c100b00300c081341142c1c4032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 665304019 1250 665302769 665302823
    0x4030f020a1202160b0c07180219170606030115030504020a0302040c050901020615090115050c06040c0806180303181906020c060f0408070611120c13060516 69
    0x2001050000403a0b0307020b0000d5807140c2e00780504101440c3d803400040c2c590550021510380031a40800b81c96424544000c81d40701307102d5070754590109502080241130800d0000306100c0141c06513110030b21525207041603500642c1005020601558041006211140384183c0e140c00c519110328010403e07644a20100f0003a00703480c1c5c4025006820030611039000c54000001c0c1031203503000e0303007219902c0e0785000002c4034616521045e42d4100c06540014807007002c400c1c4409007400c99030305100703252810100c03111345040c0307040b01c05452225100d041404491401e2041c2900300c18a005203511003136005c284240c803440007170b184500720341c901348404115500c18800e00c20b0721110b090003818802c4103800c1c072401035405050b00c805180070b81c10008800c84d907000b90b4140142c1e04000c0403814040660395900c001c0c44901d015480c018414401e900171050341c0003d1503c02c00b020001161030301c500c1d4201c102e08001e08c3e0400c4040c00401d001405200b2941c5175402413294000c0b60090443c0b407280031742d00c0740e640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 665305269 1250 665304019 665304023
    0xd02150c12240a0e04020105090118080601090e030703091e090204030f020405070906080f150d1232030703060b0313031d1f0311070605060a0504110304030f020a 71
    0x204000c01c01c103100d94036403000a1407140b802c9014070003015400400a200c0c0c420700680300c1c581010f501290140d482840a0030740000103050981c624091200300550a100c40d80c0001d0855000030014030004400d409105110000c520081d800c1001941e0098015070181c0280e115407555140010700402c1c0d4050050010400075200f1555181c5a04001c2c0d0302148440052340600d0500c400704ea0110f2181f10100212841c50f0b5811417941c03074010880d0342ca0640a4502c0c100ca5010141c002c4c00c980d41c03070036100c811610801b2580103031100f038000580004507461182e04160040f0f0003441140603040c0000d42c000601e80f01d243e9507035030b4040c400c1d0018041500055000711000c020842c03e129001c2c88218841c1c000d4031000c055002c4020610b01c0e098840e00c240e600701c0c032200c1c0014542403d1070881e4a5121090902040c0031800d1080f0401c0b6400c500030032b0340c7c516200e0082c09428100480d081c800380c1019541404034401142e4030b50103c1c80040e2000741008441a4859103403482031004908c015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 665306519 1250 665305269 665305297
    0x100507021609052d041202010213080d0801140a1e0b040315060905041203050601110d09090b120a0209090a02091015020a0b0a0c02150106020601060807020d02150c 72
    0x2d4407190204000c0c14110f40100c0f00540351030540d00000f180e543c0a8010300582025251203640300c1c4d5a5003003000116820105541d001d2042540180843e4047c0018007280f81c01410380224483d8005d1042106034801300a1004099003000c0d0b907101c0d103181c80141d0300500050b1401d1440e200070344403101c245602440c0d000300082804003c0246410320842e880f1030406050103071030744445a400071070310190f400810383c1c14849072000020b4041d07045075030302c202705040c80b40403040c03107840301420307c1540302d0804c000422008003030182040601c40c0d040f6101c0305852240c070440d03925080f03c0c0c3d20814040007034441c0480900044100208101d44010181e000c0d040030b00c2420855422030440140d4000c0f0310b480c01408000c01122480000c4249200741c0190130600d0903151070545400620704000900d045000707061500f07039141c0380041c0140c02070510764000c08080d8903102c401006120045c1504085401c03582414012a60010b5010710368800500544926155105c0211861041c004034030310304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 665307769 1250 665306519 665306563
    0x50717060a24140d150e060112090f0605250e060a030e070902130515090a05040b0f0d0807030f0f050301060e1f0201050109051e010b0717040905010302030c0a0810050702 75
    0x1c1242a0000c17020310151001d1000d4050b12610020758404048507250300252003102c09840c8258260090f00700ea0380212203c002e0404181c6461040d214111540380c5807903c0343d84007200b4610080400300b11000d0614003818012541000030f10035110780302041c070406840c1c001210903940288100402000c07003070011940d43c0e40c220501c1848505504c201c2d0301c60601c042c0c207214214a50011100c03a00c03c014000c9400728102070401008101d08514250040350280c41d150880c0c59482d140d54019024205241e00d40d0307030a2a000705205e84110440f0201305e00707400700181450b0408145d070706440c1e550424a03911071140000c01c0741586e9001c111800c01e11041c4c0e820700c440760103603c800e060340c3c8a000d0074012a0707510310084685040b280d03507601004008000400c010620740c03014090703080c0304002103518001000c0c1c003001700303400c96040180a03582c0c0d07c004008500c1c08009404004406581c3c0e9440f0328134203a001929088e006079420b41260715400084e0302c0da88248220b40345007840c100c4c40740075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 665309019 1250 665307769 665307787
    0x112030c0b062b210c03030e010221010504110c0a080919031a10050a0506180409200f010503010e04030c15150504090c120312050717060a2414 63
    0x74041000e20191845040c0d01c02d103204d950001c0c28120410081504e030f280500010b9035046009106510249034203540c244860b419800340b0a03c8020390803540c01c7c184a10394101410041220310003a01049039040421038509040c1011170b440c3c02e1300d50400c0e400c503107495480001c128a116400d02805000513207100103c10411000165101d0b1510700401030361590b40e04086a900c011680603080d40310344100c0040185242440041001c01000000413444c220600e021800b079444c440f1003190104800100000480313161a908038801508039640c071040c032142c50010381540b106003d0582d40301c007800005801d160081901f502d803154080320040d440485d48945100a0180404009200c1d101c1100015181703003134000d040e500e42c3c2000e24821000e2601d013500e210030455140840c180040100c001070780311040e22806100740e040340c448440a088500070003852001c024103030340c40388401c1c1c101800b2005500d034825802000c0807590031a0b100f02c280080e600900d4010004500000004503020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 665310269 1250 665309019 665309089
    0x405150703020705150c092416030809070f1a0705060403030606230d151703030f0703022d09041b020c18191803020705090112030c0b06 60
    0x11140b4082c4094a4017000d40c918950b680b440151040d04901c1c0c0148600c0ba05071030301c0c00641b0340c41d5203950709079248220003c051281030782028402211149000e180c6800b40350f088002d8903408920240948541810009003041d00003903801a0124150040074110f00581c130700c1d0407501341035000703403c880a52405103030090107054a8043d00c1d0004003203960700002d0309800602c03560040c440d00200c2c0e061616105545004201c041848082e0000e08100010300c100c4400a580004070307282c01841e5a031030146040c0115120180200c0201481005412001052940000d502c1c40226072490902c10044503490b41600a080c409684507140c0b889401e108040c0c040e1040c0d074402c203138007540d00420410080002680040c00c42c03220000001002502c4100400c0001442c120060f10010b1283e0790684e91030074a85110b5030440150740290b0f8144058a04099402d00510b154007003901010101d5600900841001070004d0840d8001d90101300c1e030b5074680035440400e40c400f1000040c00e104042c00c042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 665311519 1250 665310269 665310277
    0x905011505040b04020c03030411210109170304021c020121091e030203042709030513080309060a030207081b25050a0e060102012a030e060f040308040515070302 71
    0x24032692500c0690f2160b42001c0c001d560038807108401039070840e6600d4903524010389441140d264080401501c8204500c0c0c09441c3ca8124050600002072071080e80c5002240303024110740d82d0031282c00c24402c020040c0e8603040b40780d10100460904007489002e6100584805058006015016100c2a140f03911303004543d00c007030401401240704c07500004500c0f2003510042040407010b4010b810401c010700400b9070b0b203031403c000c99400d10618000020001d18803002c44040c20710031030000e10009502c01d14200400350f10ba0261161030091494803200300f00042031446042041e01c00d00d0f1b00130071050184900391080e074548006101102480031100120207803a6816054426610303604652071314125100005204107403040904403003451400c103001003c100200031f000c82e045640352210889030344403040c05d0b025800c0700c2c00c00b4000602540c049c060f040e034409812a0100394002ea040090800341e04800035049905400c0c800c51980b9582001410145003c0c0b889440c011403030140a04640c0c954024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 665312769 1250 665311519 665311529
    0xd150609061d13080f0c070305060c0403051b01080a0b0409020a0f03050d1107030f140109210503101401020a05120a090801090c0e070c140606100503011a0a0309050115 74
    0x10815643d80c110403d010003401010180c80018103128510801c0000310003810b8401401b8101d80c10b8507941d41d100380c50245d045034010328051000c5000c00800c0810407121510036181c5801c60440c803644400201200d8000340344681680d150b110044040d2290360000c104150090001d20b805a103403280c00078424094801245d1920072a180900300b05d20a134140741300c02d984000540703d00d42c42c6440701d40640940d100d060300c00e42c05560b807480e0012070904c9452001c51054a0b030b950502c3d03038800400c03030b06800c40180c10b05004c82001009081c0c3c01d0300d00100d00b81d50900c042d4000c1da01511004034684101d40360010b00b103124108240076001441c0014011413261503039050b1146032600e031807501340d0303603060b0f030041c00800c0c070900c01c0c41580c00850510703030300400303e25107003960049648500d00d0020002030411040e421038014082941000000202d0845c1c203414403503d10352404030399503007581c1444410903215401044410340c1e03070300c030350401202580c100d0000e009408003081e05200302c0c4200e12034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 665314019 1250 665312769 665312819
    0x60f0f06093003050f07060f06050d02010c0b040503130602330403030c050c01060e0105030c030c1810090f020a09171b1207030f061a0d15060906 64
    0x10542981c03207004038100095603000400750880442c0750340440b8400b00c102c06000c0b0502510341d00c038400c44050010741d4060b050111f800c00a0004039401c03901103400050040504140e00750150f40c1002e031080000f40d2020301c007295541c2e04d0070a141140280000c0845c1e205030607a0007e64580e000400d21118003402590341c803104c2030500c1c0032400e280400c0d401e100c144200400100481c0c020f5011501050b40e0341800c9152001c5103a0050860742c080d000348604c403c44000620060500700210701100340c081d00200813100b54600007603001d10440880d1042d110180d80007480ea80c50072a500c00c0185000c04007807100e6039803200c3e40400781d048204104002002030b5000605003c1b40074601d170396084040007400181480c01c10312600300b4000b85030950084003030036034036144020820400d80154002c44680c1e500741458502603003916400409000e128201c4412850f1654a03040d01001c0760794030144c11213089910302c6c0c0030740181000b03074000d501d41c1d031400c44001442c0110044005c1c00390b9000340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 665315269 1250 665314019 665314037
    0x3100603180c060f140a0521060607080a12390e0d02190e01183b1c020f210f070b04030c0c06051c0f060f0f06 49
    0x141e040c000c9003541402401c1040342070020880c040c05600f002d0050819450454580e2103914070742400f40c0d05c040c070380c0c500250000035000c2c098681030402210035030151010341e10301c1c204000002c40c58014039102901d1302c8000a102e02186010710401000240d1014090018114080800003010910350744558800b444014041820020350300d007000e500815201c004510440809200c1c202c042c01c4822a00240d03030380390480001b559031020100400d01207500d40010341c10802c0340c0c052600340483c4010541e0501c02c0303600c0728014000e0551513483c1d2001c0c204089900c800c01c40d101d8512038102d0410381c0c1c050094047c7c1c1040412a0003030995125800704c032030950814041c1030361610b00c0421515280200d170080c044040c20440142005520102600d0810b580c6449450200f88261030407000310b03120150210170403456888000c001d00741030038480d081c04034008148241811414000403290341c2c4074541e0300d140705164407007005441102c7e07845011603281d03802c5a49444680c020351000c61041e40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 665316519 1250 665315269 665315291
    0x150e03030a02060703110d290a0609050108060a0b031e072609031923070201200f010c0e0306010e0402280b07080d0501080c180c0c010203100603 64
    0x4850140382540d00070f107500c0d41c0b0440c04070028401420035901a513002c100c83d41c089030302802103c050103a4500f0a683e01039060501311480300140c0f00b454000c41c1c4c00342e401c0210316041807108007114000e00b007118059440000241d918462a008a0700c81c04010060004203202c24000100c540c00a515103074440c3c503400e0069541001c010145408440d416261101e052461002590082d45540031203040200c0010210425103d003420480051580340d41e500d0101068480084003028040b10343e403800030150002400f01d00c000d08217040c1d2010001c0d14490918040160324a8000d030940200820003001400070090750741c01c07004070704c00e208000000c6058030003c1c100c07900441c0d0041c141e0742d03245c0150b8184041d0111070035441207c18400d04000a6142001c03008000807485095920764030150b2212000031103d060b0805003090344010602182903c0b641c04240744000f060b580007a40740d84203400d640c000c0c4655036064038254000f000748a070b044d02c80c0781c4140998030705880a00212010f4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 665317769 1250 665316519 665316523
    0x70312060b07260304390501080405070e0114010e032e020d14040204050f091e0f0106090608071212050a021603050601080f01020c0c060919150e03 65
    0x50003210032100e0100305520014a205420a842c0303003800b1040020011031074020721003500200c606803484203090100c410a01c03001c05580d00030011011b2500a1400c82d0200c403281c900d501c1c09086c0c1402441d40209040c420104604070080c05040c0346c1d01d00540c2c40e2801100c880300ca800c1d1f4180441ea05004020031441c0216545403c48000403525400032210307031803080b90b0365a841e00814155802c00007040760320703602c3c000d010903c41c5000c451010f505141c814030003200c0008150a4030b0301e070f010301809081d41010500c0000d400b003245903a4411107042d4a11400c001c40b1520203034040d881c21800046581c10340e0040000c640b03400c1c09803090169100140c00b900418101c1c000d18440541c110307200c985000320013030141d040329441141d0710b68210065540594000d40c1080d14641e01150040003900020007601841c9005030000354201311812128560b1800e16083c1c0c40c4c4a540046160081608d801e402101804400c16000c002c6a58850482c0c44a001400300030001070350801880c1031070700340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 665319019 1250 665317769 665317781
    0x151b080901030c1d060306150703082d1b0c01021605010b030d05030a020d0e010e01050f150a03020d0314161a060105071407050301150806010501390204020a0302070312 74
    0x44c55440400d00d40401c4590f40c0001d0005610461517102e40504031040f9000d401401e00c65201c8039481c0c140740007030343e4030016030f40b01e10005011040046086882011031440c2c02040741d14281403072030641c00c9850300b503010b0071200e200503620102e2508500418044000c1d0050f0046c002048812504000d040d11860180324540126001700301081d4008216070080401030440f00002513100211403503542910300280c60030340c041e034550043c000540c101c51041600300070300800300b44001d81600086400015039100103440340c91070801d17500605024001606006401001140d030b203401c4d45103458020f0b644803000b610300082e02c0c103e1542400c9110b0205006280503100c43e400d0101540e40c040d007134105004127806600944a001403291001d001d0040d980551014100d2640d0500c281a440e00405902160400c600170743d0009410b040140d00c6d95030814880c0400751114540e0308220140e42c030014000790000d200090078400542e0541c00b0b40000c1d8881d84d248a50355100c9032444d000d03241c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 665320269 1250 665319019 665319047
    0xc0715091403221e06050a0221030403081810052518060906080a0c02010f0614030c0f012c03150a0507030c1407020109030b010b121f151b080901030c 66
    0x10054024003032030340201b002d0417040c11184102e8040c004035a0300f603e4415285681d40c8402c07140030040c4410150010700c0c81d54000d01600c031188080f005505041e40d2010783d002c1c29610503aa820200d81004c0ca8005400210790704042c13200002200c040c001010720a950305100b0040d1070041d8027281e02c500ca1003401c2c003216480d039224443c0340c4561940358001d0803104440402c0d9941c030b041400c52450603004010040c20341e20100c0c03e1107540502858140400e1500c1c0c1d40c851218581540816030b080f540b51903403120300140386080b400281c10121312000354034850700c0e45481000c50386407070b07002803291003403207462075903804d00603515007103420b9045d9445d4032881c01c00304204040d41c540d414498805420762a00500d488d0b100c0580d00d403903124449100381c01c58640c20a0026401c1014044c003140325411084e422002a064180c1d1400c1070490b800341d001e00c4400c120b0205000c038600b40304880c1044280c2e05001d5000041c1460710305140b16510001e801804242418215524a030085000e0000e42e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 665321519 1250 665320269 665320319
    0xf03070209070f032027090403030504051504061a090717150603040c030b0702032b1409010905010c0c0510051b0403030906080c071509140322 63
    0x24442d424282e89107082000007504150751502071680c5001c0005c1c101c0e45900b840c21501e81e4880c1e10070f10740d00101c01d03c06814000c103a00740c02c0d031003c0c2ea116a00001e03400f541501d8005141d484510700b0310b0410081d41c142c8101a196003051000340a150350026801e40e4100c130006200d0001e40d020300061030011948400480c500009a41c078001c8074605969100301d0303c41111210102003c0002d045820648080d1f0340c07030300f01074800d0040028500b9041c0d040040c9000850600415a807070000e4205819020b0310540c95580c041081c009458100c00520014202111094907005500900800007035000361025802c2c50300043d0203502075640010b819401030090092004680000c82c05800090208070f015050712002603174401142d405000514800d540c0c01d94007034a030110042980300058000da0341354804010365800070f0f16205030385c840710040a5002c034907079080c0e042c41d031008280ea00b5a070086000019816416a20914050700800b40150b580d0f411142c85684410303a1403a00940c401800e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 665322769 1250 665321519 665321521
    0x70b31031215051f021e031b070803030a09061b030905120414010c05070b04060c1b0501120915020f040f0902093106060f0e0411040612020403050a050a050f03070209 73
    0x190001d50400c0c3c0c00a013181c01200c14001900080a82d50aa15400c088080d0804a60503030221800031861082c070b80140000c0408600305149140c4a200103401000380c03a0713540c800101003121a8101c46901d00000001c0340d9a420b640d480900035041c0740404995901600c26010000e010704000c0d10161042001100480568000191411141480161410b200b0500005001d0402800501c041d280644c0c0394219440e0390310f800210030f46400c2c980050107800d1b0718140403d0340d016682c5118400c44c40c0c07020407500c0d0b060802000e405007a140381d00816000103600800e24813070400400494281419403d15507035226541d45c00c0780203038506903901c00302000701032101503280041d9990700703007082c25074862484515222000b01d40d526813001300480c506448070649250001c62000b041d1206407010701c2601c0124031041d80d00d01c00c9000d1101070003e50a00e549440000d035064901550f03006d0101c810403c81030408a0350707118000d0b41100d40344650b04009140000100a60304800e46c094004502 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 665324019 1250 665322769 665322799
    0x29101e03050a0b1806042a050910030905150c1909062c0f0a090f06061407020d1205070c030c030516030809061b100501030b010b070b3103121505 64
    0x6000f03c40c1c500901c84508000e1071100400040d101f08260034507403180b80c2d480b0906000d01c820690301059440505140c24007000c085540030500e124400351511f0f0a5845642d2240e0902c0c1c18010680c0075401010000e1000300040d812008850076102142c440e5580e8074503d51030200b050071410b022050743c406c6030b107000c5114103200c1d203600384c1004024002c4020759221910242180e210704680c0c0031150b1640810015584c21540f00e0fa00160820984c40c0b030b1403c6071300440c0c0028401d0398024030203000d030b0a101c111644910161096107030301c50f40c00c0301e065079607090485031904503000c00d07101c03400f840c0a010215461202c4080442c2d51020640307040a55010801480b07801401000190101150002c0c14075075083c025412100041030300000c680d411404c080c41c1d4800d05030000c2110030f01c100224000725110703a03900c60744210301f0800900e045101c2195000c0070342101003840054103c5001480401d45c020264455242041c41c0030000c5031007044800408944511600d030304243c0800c000c5807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 665325269 1250 665324019 665324021
    0x121205181b06310e01030809090405010e1f0c080105010207060e030106030b0115080c1303020d02030f0105010b040603050c040f06030209041514010329101e03050a0b180604 76
    0xc50000002e041e9030a082d2006041400d8459855040c2c03003404602c0c4003003100b06941e415090141101d5512004590706681d1818200d100703096911340b040da103841c0003c040060035045404c16056440644410003000c14001440303c12600d1861300c1d040c246548030030760340d100c1e0f403080d412035405900411201e0316045c0142d5800c840c204030305415540320000400801e81c81c0440600038244110b080c00d450f86214001007150f0406400c0d0303e8140c1e8104030340c01c83d600000102d0801e4a030112600e546007007907440000c0c9849240016400107500708800081c0c10340480380500215a56514107100135541c5040f110040d1081e4002c0d81e400401d901c41c140001403180d406800b520b0000751000500c1c4c0ca0842880100780c3d007960100419428003400e446a07540c1c14042c6090990544040c1c981d24010f0803481440440a500c0c0c0b140124010107503c910035201d40c886101c46800910240c09100c0c02d05c100a0145c14210b44009899003800b00005460500503418012140c1d12440c007801a114041004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 665326519 1250 665325269 665325313
    0x1c1511040b07080d0603080901180501050306131d0307030906020303240d020d140106050a030c090e1002040e070906051801030513051617030705030406140712120518 73
    0x1c0e030210010300c410709504d41903105507400385000780100e5840381c800034001805200360300d10020f0301200740c0303400700001c2c0d80007001c1d0798000000f181c0840c0d100c403c2940042c000d2100014a000d140400c800000000c5000f10007400018000d41c4d40d1914143ca5203400c1c2c4e540d101c2501d132044d468403100d09800c0c045504a0090143c40401054004e4540d42500000c5030b40025403810303a9004c400000740114160240701d200024501500c3d1410000d00d192a607030414034591003000c043c2c81c0c076142401c401081c00e0240701c50312128841c0444d00c4907100c154484025208a2b60180401c0c8001340c0811150302880503680300001040c42c0d1044103010b18011006898081c0c80105580300c0607103c0800210107001a8100240c400d8043c49528540b08042c0e5895030b207422015401c0e007080010074003060001c81114242c45080c00d000d1000300d01030b0301054180c4151000a0004e1b02c603221401b260300c0d4440100c5840020050043c032280e281d4803880b5a40c2030101c1c0301c52101d680b00e5070610100b0b0340014180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 665327769 1250 665326519 665326523
    0x717011116061d100c020c0a0f29070b060114030c03150109080f06191512080d021216030b0d150609021b070e06090601030207111c1511040b07 63
    0x2803d03c410340240c803858030140100c0040c0d05034030740d41e0303401101c1d40c10081032107052030803210017001910b0106000c02d012568090704e107108403030901c00c190500105290f0014000c01400065851a140c10020302c15101510f1142c0021040407040c00e0021051003942d0050401550b81441c6440d400c0d001a040708207a40c0c0e030f40c18801901c00001e9a920140b1a052034101e0a0010f04841c1c68038a01d50222041031254202041d49000024961200881d0700b2100352440000003100307100860602c0d003024090000c0ca40d05460001036669072200000780440e01940c01811550b1207621040c5096090710554100680c100d500039072460302090052003540c500340c64401000480b26107a0f01c6da1026684040581060f0300002207803900c050008020680041460f49158801c85c2445800152184d1020b01910704050b008103001080c0090600b40442c1550300400051410380030341800e0034882981e2005071406403c030388040300c014400e8000c50361a01c55910b0141e1400c1c1c1807980d10b1036950841c1c482 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 665329019 1250 665327769 665327801
    0x602011a121c0203040311061317010b0d030f020118150c0309020306090f1c0203040e06041d010501050109050603061302031e130605011401120b12071701111606 71
    0x1e5201e01820a0b48081003030091580034503a61401c0d03051038844044081c01c0c250003054204080d54605c41c40810703030819952108002100901c00d140110b000d40b00700c914003540314110f9240c000030150010403d8850411540003070000240c3c02c5041a080c1d908401d02404220803d0030104402180d54003240b0755102c54100041c0c401c51035000f00e841c051086134584a90350000b130303000e5a2480c0402c01c0310f0341e800c0307d18480801008201d100a4603805144070f0203091000b40e4021800c030755503980200e94040c1425a00580c0c0030842c0b03140d2406404207108c2c42d80071460710503000c111405c01c013084a00c203480c0540300010082c1001e95500c025440240005442c400d00000f802c42c1c242c0100c0801d00551064080003035122160030800d046900c103034480b400140c0d0102501e05141d070030a850154010444100040d44500c643c0852280c10b6003136802090313400381030808035100800d6000c0c031407003000c9003000b000803680e60318800055108640025059200c60347d000400240c25800c060301c0d448039010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 665330269 1250 665329019 665329033
    0x10215280513170708070b270703021507060e0c01180617060103140403020a021005031302240423060f1606061a03070f030b0105090103050a11160303060602011a12 72
    0x17240d0a0940000d101101d03846010014011b607006a2901c1004031140c3d40204802c41011600c8a40e60b2141440000d000d00c0285aa6010300008c000030f07030b001c03140c021009014051200040c0c54855a405615070f011540c00c0800941c2e200c2c07800700d8102615107a44404089103400a0310300035140c8010702e450b04040e10b801036200d1689004541500880c400d4005142111451041008440b038460500c01088001e0040108803050160054a43d64040c5d1f8410860103c83c0500c800c80348004140740c0040d100000e0005a5818441c9003400c50140324414284e00b90a205c2000744c3c0d03215080c04071068040034840014008030301d14003025000d00c1800c0020341582da40e0801400b4031140c000d4a03e09003008410000340e240c121024200c84092850304202c51703001c40c0006031140c02400711050401d039885002401c188056842404200400da90007602d82c0d003408498039001c0b44100c000c4000a041c032400042d694014000c800714209c5a01e064100c1003054000d01098143d80e948840440c421a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 665331519 1250 665330269 665330273
    0x16031506080a0b0717190203340e04051006110f15061f02100207150e06011a0f0301030204090f0219092906090102152805131707 57
    0x81002c0803807040e006450b003440e0500d0040c00500c2c103024810745a5488800700f01038030510922a0030b901903240710042c1c0f651940038410a51410303480a01d0034403413400000003c014212070b40f051907400c451703490315101c0c200b210600082d904290f413440381c01080c000301031100c9800fa1540e088000c2c541800c4540341121040b0591030428134080350104110010b0a000303042c1000301840030703241ca80c3e0f2404c090000600b10000d5890425500362403140fa4045040d1041000500d241c58950a02d56414010b06140089507615003000303225031003111040c4956610030304840e0041c0e4400c08401c1202ca030550786145c0a200261446203c1101d61844007028580140c0ea0110b40032504010721600c4000c0c07a050074542d03411156040c1c440d9808946506280b07541444560664002410a0f03c242d034444c02c503d0b0050b46000044900f5070300910a0340204018500c1c00c0c0c200003094025000096034084603104d140040b1141500c40440703c011f002c05803004078200c02128120701c4807039500d052074520a6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 665332769 1250 665331519 665331523
    0x4051801050a060509160f0e0a0810020c0c010c03080403231b0c01020f120711030d030f0f0c0519020f03280315030b0402010e1807111603150608 64
    0x110b814104040d580c0b0800e1025003003030a10f05030701807a0440103c844100d5100080c0140401211070310410415008428440d00c0390b443d40d100a00f00b030002c82e50009820348d6800c01940100f00c4000c410f06c24807185010301d620a65248400e10b4140e1603082c02500d0b6a20210340103206c035080c01d40b003440559015180f0788144001803c1410490380640c4070040080c6640d03090002d0080990704640c00704d00c0702d13228000046001100c00610040742070b91640e041c540000001d51404125603d805034140c0401c4094140d00500c82c0c0001c410303010400201d8603203a050460301440000300008405000341c8041c04000301d00c0110004890048445c0e0b5009490785510390740c4010020301c50004072800e61422860100b5078841c9101540c1028000b400104100000c3c01a0314403000c0d002002100114095901032400e0f03450000024200448540e44540450a030f0281921201c0c0041c81041c0440c8045001041c40c0c0101c2e1070304544410b00503d0360b15440903002d02080100806581c813100040c0200003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 665334019 1250 665332769 665332771
    0x1404140403030b190b040603050a0b0406080a2603010b0c071a0a110105060d02130e0d031d010501030206161e0501060810020304210323101406090405180105 69
    0x22070364021801010f42800e1050301d6902402903055500709107401e10030311040300c05542c10f4804903e0f00180c5c6070b495030b02c62009800398076803140e041072500601141c01c5502040144c0d0040c0981043c0b50301e03080c5c880311010540c05031031a0b582074035014401800350300c0341c030802440121000412038000a071108070309541c0c462410f181d40000307000000d46224041e00410001e08820252000704010310341080403c11860a00f071000b880b4040124140c144003c59030f00c0300c000101c83c1030840c1d42c10034100d00c0c0034000b03003414002d0391895420702040750422201400f0b440d06882e40603100301d0510b603103401070307920420100c5400ca0341c0c80c8240050301010311f40182c042e030300c03d4080d20010071491310f4142c015040400440c4c3d040001c1c0d00400401000c41e43c00105006058101d45445142d00b02c6000124010011002100304965440c030300001c14014440c9014001c5948541c2c06030802c0e900c840d41c2180c010011444c5821100600c140740aa250540c0400d030710007a051401550b9807840003106086944c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 665335269 1250 665334019 665334023
    0x13021305012c0105030c1207090f09021e010e010516080327060709050d060204090f0f3e0c150a0b06041206110d020705031e0403080414041404 63
    0x46030301000c060140e840e0b8280c60060101d95160b54106004a51038010703a060aa0040c000101d64580f6040c080161100400190400f0442c1c8464501c501c0060216100309131710039484992a1365440200f0f503030fa80c00c680416120b0340f520f2200e050064030b8603000b0149902440c1112460040400d05110045d4420300c0d140d5042080ca8140c0325200b000d0740b015410307046055001d801007022181d04484030105403482114100603a5849107404800391150703130420012141014905403110f00c00c0d8002900703240622505000c540300c441030350341c0100d401c09034501c900c54108840707403504803084001e0f4132104000c01c0c0c03141c0307003032409040145000a2042c03138002d1a0010010404418494071454281c3c0c0b504a0311285043d1074009a001004005c000141406568049000d100c00c47c100c100c0b10000711402083d52103030740c903051594403500410f4003c1d50030240d0015840b601c0c0804800c44040e43d5000c40c03228102420a007000415501050f03140d03400c00d59030304140c507440c01e0152401e48107c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 665336519 1250 665335269 665335289
    0x6121a0d03110a0c09050f0103030f0315051c030906020c0604060e030703080a120506010f0e2e20010203060a0e0702100f0204080c2d0a0e040b0106020706050901081302130501 77
    0x40e01c0c01003105c0890750002d0071494185501001031001961040c10000b0b107140f246008503465062403480c04625105611882d4040010b0034004c10500c6030401c0d10714118001d80711002d030356a03501001d03030312403440b11030890703005004000c140007035400364590550b0071030050110b40760203441b95110985940041c1c2143e0209081c54400300c66241c0a0180941c002000c3c604000300b80c0c40030502601241d0444000c62080e40c81400c802c00c0c034070309001113182d2008070401c0c024980f603000d0350241000c850f00c0d81c286081085001c0126a241c0140200e90207204040c02080a440c90100c00380c0721034030040d145030218060300600c0c8105404034054540461640040165194500a02140780004280c1040c0c000c02d0114100b08a61340d0710100110180054403600c80c1c40c1c04040300086403180c10345c010364102c003262010b0005100840d00403c0c10394009408490042c1e071614407d9995000d22103805001514800014043c080c0020060200610141005026404031304030b080544400760080600d50b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 665337769 1250 665336519 665336543
    0x60912081b031e0a0e15191d03060c0307050f040b030702011401061b08090a030609060b03060f01030b0115030603080a080402040605060c1b0607080304050706121a0d03110a 76
    0x2116030481c06070142c0880f04040707884c251102c40041c1440c030f0780842c9a4803c4000340450003840740105c0c01c65a41042002040c0c1483d030071204050041a5854404801c2100345070003e046801c000807628058960800f04500b9507480b00c1003150341e0b621600010b5402c1c00240800513942c2d40c048042c600800c02a000892000a4010503000d0244c0581c030a00820201c0140c000184080300c051006040e046441c41d030307641062202061800f440390b4001010540390428000601400d54062103983c2c00480c01c1e90204d40354500003014800703080c0405441c1958007801001403903480c401d04075039803c3e00d040c003003078044e41c03501c816a1607008111042e0104410390104821443c2a00c00d1402030801203c0040c10200007050f550b030366410440070000d260102880b0407a40f503541c202a00c04140e4055100c0b592441d00e440c2103602c0e1412880342d000824250508524400414006c2d2064081181c014550950f00d0a080003c50110604103800b40540166840c1e00c810b0240b10076503425020300041061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 665339019 1250 665337769 665337787
    0x6170604021030150b1207030e031c1805010c080702030a020d030b030c0d1a0906040b0a0c090302040c270f1a120a09020306090106060912081b03 64
    0x1500d0356006280100802c840100940c0c4a01085502518041444200208402d803070081c0040c1850343c208a40070004070341c00594000d8405c0141804250710a44078402c0e214a1020350a948a43d40d0107100c68105010400800041a01625500180c8180407a84009240030303440d000d080070310155103607519804528425074101c0c10784d0360000d2846c4000d40c40d0071003220340251901d5aa46d0303690304042e00c3d82c2400b48a950100000342e40b05600408140b40d0b1045403030012211500c800324001610340720070020700f00440c0840e00503c91034100071103080c256a160303a0003000782401c407007010911049240c0400980c1312446000c0013031131a500c4450f002103d4280c076006000880359000c100b0303070350f0140520240745807500726402c4075000524160102d4204071300c800703980100083d60003511520700410180c00f60702e810449140b4020350a0380c18a031030b0080c1e45401d9862500680300800c40c0200704005104991903404c0d030050242c02e40c03a0925000d00760004400070904d100610f039601c08108929 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 665340269 1250 665339019 665339029
    0x10605090414100b0a021c050909070c0209131515061119060e0f012909100e0a18062004290903030304150b03030a091502010617060402 60
    0x2010030b00701085207903442c00c040407601d010564040d038a900e2601040204545008001300d60f1008174404885544040f60038009046810180d174841c803440c0200e010400f0107028244c0c29103c0c540140144e000e69891803402098020440c00c00c8914007145842101a858140b0070300d0030944d0080720a82c1d000340b07440340c010209071413000a00c90741d40211100110b1000c0c10101b1003074441e4850008605c0c0e244400030036003806244a5401000e5082c200b003020380303002e0415400e103c1d01d42041c0780c010305298401844241507003181e103c80032240b40c40c0140b2442c4010340d0343c0e40c0d0002002c6400b180491600104004402c0705a004aa5494a9031445c0c1e9880340c25001c0843d06601030302007076003014500050001d428280c501611211804c4200c22981003064500b201c180240107802c0303e64904081c030700944500c0001e010031000c50300e804806c26543c40e001c01120001c03074950350789066840c107108804000a40850000d804d56595241c001032600008440c42d41046c10710780038003001e01c1c1c2401841 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 665341519 1250 665340269 665340281
    0x3060a090512160b0a1407050703092103030f0f1107020901120519030c080a081005100e0405060d0210020f010f020a09140d08030910060b07032c06030106050904 71
    0x803001000c2800f080041000b5180d403020103a400c0312072820300b5164103104000501e00c040f003103400301c0380d44402c1013246c0790001e00928074a4400d50b075041c640341d80c444480009900040309000000c0110042d0030110b84a5045a07500b010380d04030004010702e61802c4d8504550301e0481034072041d000490b940b41545080b4441c0c0c1d004001540488a41c1d041c103950b11034403468500400c00f440c81801010b0800d05202e01c40e5000442e80c4030480a68400b0850342c05000850221503045190b2506407000c111401d10040e2075203140d0407503c504082c5204542040080c08000300419008600201c601000d0f036107164803170000b010035030081c0030f0101500381458296402605050721641c010020810304a621042110480380d001749141100b81100300001e070001525400a80301110110900031607101c08100e0b0403882d840300c0c008000e89075032803007080380d14082d075000a008208411071609000381800c203071410200d41820401c02d014000c03800240650001c2c2c100000080d0041a0b01126003420b100388 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 665342769 1250 665341519 665341543
    0x2011e0212040b0901111803011a0102061b160813060503060604060e03011d010509190515060607052e02031003031d04141b030f010308160203060a0905 67
    0x40d03142050485860a2900c0060801054150940c0005510403420750014440c8001c1e22081ca0341c5024490381180390075400003d1a1195180c1407041d2414098450548060201a00074142c1d42d600d05882c0407003207001d020010404a410010082484194000c00741e0491056038482d8842c0200d20160146441c1504180b052003010001c1c800182d60b00700a41d41154840d00c1c148001c44586000700e030250514030004000c80c14008140c1103482010341109115a41c04011a03d0020803c001d012003c56040c1d4054600d03006a120130424080c07230b18416030700c0034000d0202c03480c8c44080c2d9038103868100e1103048440118034054401480c01c80900d00c4000000300d0b920154210f04165007031b000800d100f40b10080078002d100c4070030b2080e0318030b0b03164407034200100400c00c00510300440d51015103100d00f2510101c0595003904100504203480d020ba9004250502c1b89909986c00e50307440c0340d174030340c016400039051003544004040145e40412503030b44280c002e04804101c554040c40e00900e014104044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 665344019 1250 665342769 665342771
    0x18150405011407120b0d0812180a022407080c0f06070f1d120307060b10020f0a030c081b030c15221401020a170f0c040302190f0602011e 60
    0x5000c03603c2e42c041c5031810b03448255440018001d060f80002508075041c9070008121580101d0702604814031540e505106d030442980c12041e6400c0344898a8071499850300096105201200084100c610742103110403800b10f100c80680381c40960341f242502c60b045006601a658000d441c2400050010f004180e0000c0e014203100c10441c8290300f01602500103140721245032000050350303400342d544040c03213641d602220100b90ba9580f15541409405814a45900c9008407103998141d81804e2001410300140c1c805030020b06100e2110b0ba804030307054405d60105499044091182d5103c100a0a80e04035803030446000544d6038041d01c0030740c5403d100034042460043c0258404004c80307000020b040841510810a505141c0c1c000c51a00c0b0443c190700b07100c0e14010358400705914050076000a006501b0141c1c0482000bc1c80da1080340c22640e10004030703000908010180010801403d1011407150031113160008282516200d409010030ba003816404400182e449003581c600802d00c112205004502c2c041c0c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 665345269 1250 665344019 665344021
    0x62a0a03050a110c102303090c12010f0507030504050c1e011103131511070b0d0b010203070501090c0914060303041403120d0506040c080601080f181504050114 70
    0x30007a106001d2080d0074010301c5100010141d003080b061020b03030030407000104540340010042400902214030030352950068000045003004404251080d24803034a003800c010205072481c070741400400503901400c04099034840741485004645030107801d1007070b600f9540001e6149420b0810520300000342c034245000c3c0303100000400078548500f6880b060300600b070800000c2010701030401451889580c41c2860407081c4060003240c0c61040002e90a6212920b81d20000342c1c00d004104030340c4828141c0b20703405091004211080700455107400030340b00180140144c0c0d04103051610b4450070744075000402c42e11074550440900c150f0419109403981300e07044201001c6a45030000c0403d580c4e21441c001c00c18010f0040b405540560703010401c8500c840024030300c040d00c8204031007803400a000e09a458a100700e090020441c220f0f4414802c00707105102c160f482c4840358075401800c0003d2600541307054015000381a4040d200e180800c911031100d507130b4001d1540c44e45030034201982150041e552601052031000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 665346519 1250 665345269 665345273
    0xb090d090632070501060816060921030c2001080a0b0102061b040b040b0a0905060f07030809010b060f180d020a06030c030b10020102090f061309020315062a0a 70
    0xe00750411191040958000c401c12914281c00034050341e43c0c0102150700b401d201290f9028081000d18120301220404002603031189030580b40b164003070040c0c0a1000402030004000d42c4100502041d150103814015001d03515a00c2e54490200e042c0e0300290200b0400302e000b151541d1164a1580c0b00c442c403841042000c2c00100004d46078200508001901c50805900c0001c148501d0101e400601c1002c1c0c0b216030700c07030f5640c0c4903005035000240360303001007104d0303100002c1c017800d107030b0102c80c400500c514490745481c3c403594050b00d00410203000740101c0e6503a1121031407503031900b10041400b0460a107845484003c403214906000e1905c0a0f0103008440304c0f4901c400607110101007005542c03941c1404625030003020807c40c024a00c1c0810b16074403901e02070410f071700250103500500078900e040e104020483c0d10482801091711030103660840400591030100b254070175613409107400280005507080828102000683d540d00f11182d030000c00c66620b83d10210034815005003250f41c1c81d001c4060246c42c18a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 665347769 1250 665346519 665346557
    0xc0601090218120f01020714100203040b13060f060f090609061d190903080609090d0e371d1504020901030902031015080a0804090c0203070b090d0906 66
    0x4020403074054150b545001050120900c10700800b030580d00000c6440c1c8206050110b0607618109840b00d0901811110440303240640c000c40748100e80164dc00b0040ba1034408020b80e407480040c0c01602c4c0349030744001070240c1004600440740208061000c01a0460a0001d4079048482a510030b4100c1d0303103007010820004181c800c014104034035a02080c001540c1f440408620841d06c581100e406900d000c2001c0105a003006005016200c280c861076500d0707450040283d9034820124400c000308242c00d81d03c120500d05600140710010410360323034552202d84072100ba0010b640c82c6051020780e0312800c005101400c02418260135080c2c95009081c5981014002c01c18641d206200050041c0c2c0c00103003840b8181d010340c02214003180c0c040d086441c5098000309000c018046844021505103564600140d0310100203902e168098002c03a005240c5854403072a01b00130904040c444080d80010b10904020135100d000c0544510b10100140c140000c01040041440c4a0b03034110405102a2001c0210000030b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 665349019 1250 665347769 665347807
    0x5030c0409170901090819060c081314030c0601180c08070504050603062704030306050a0503250e0405010b0109051e1e04020a030207020301110309060f0709030c03080c06010902 78
    0x2c844a020364890143c40102e03540a281c0c0c202107005c0c81005034602210740700c0c01001c54024001e140420041c480600c003220741d4035041e1103401c0c031150710100b0500440c0385411890881c01c240b00840c0c1c43e156540e030102d03080441c00d138011410b030807a1a800b2580b41003030303029004050000f49043c00ea035141085018080340214042c0a0041b480031001445075214105651700c41060192000c040f21680e800f099170b003000860f011400282807000002e150308054414406036140107019000310170f01c1205140e0b0340085a801005c00c061005400501c000101c01024000c2f40076000203d4100310800c000740904509510032406880328900703a41240c0502907451031008000c849600c006031000d0396003e0f0704104402d4090b806032000507101515505a0300030191984242c0003845a0300c2c400c55140301501007181c0800e9aa00304500190f054603904012076401207043c2131402340c040d101d0711241d4041d44a174008507080c0310001380302000907008009442c01001d084605500e0003900810100140300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 665350269 1250 665349019 665349053
    0x1060e25080a090c1d190605030a030c050106030b0711150115030c0c0803151807080606160f0c0303080a2007060b06030a141302010815010e1905030c0409 68
    0x7a40300d200c0e00030030007451800710042801004d801174031882c42c141441c000c0300c1036908106070b00210000c800e8180c854010201140c9004000d02141c10f03c40e101901d200c0d07820441110903552b140c4010002071a0f0b501c21034015075260380c0d0740300c01400c0d81c0091031424092980c2070844a241100400103454010b01480501c0b502d07144c0840c0212145100340d0707444610303800c002c0c1150804020044a640e8407004c20409210445401e00c3d604c5a00c0680c0303402c2c200542c3c43d81c0002c1c2c051000900a030800900a001c0046240f207440b07800c10241d141c0c107800c0d0802c114115041c01601c1d40030014036900c19280d0350400201402044080003000c20240040c40d10503058100310404503503482407115a9001c42907041c0c010b44103640c0da25055007000c2c001c1681604091880000c04086820305260a040c0c44480c3e80c1030f165848161a0380030382e009181c13081610103042000044c3c00c0415621140810300c0340222750b03504c104003181010708040c00c00641080d103900591610260701c0126050030082c4500c03034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 665351519 1250 665350269 665350271
    0x5090607110a060c030c1205220510020307030c0806120a120302040e010801021b060c040902030a02040803120402040606111005100308040e070306060c022103090301060e25080a 78
    0x720021181060300442c00074124500e00030304040b02d2a050b070040c006100301030f5160303043c3c4c0502c00140821120156030390380c484020320400312200711418184480140c001c8003141d030415481d029020990388100ca601001a8440365445141504401003d03040401200c0e01d034100903860400395614204220003a007598403082c02c10a9131802981110040c14412a07000520760712403060074082d50150305401c10203000d00d00355003070040c40860028003a40241402510702807500c08640701940024218080cc26820440020715038070400050050201c0402c8008075450940100300c2111307030310b900c10f00610890304000c20b804400414883c807684c5400400140903201c000c0c144510340c003180c000410392a00040c010850601c04005680704000710b0f42c05100140e101e40048915694101000750800402804049000480398082442e41c0c03c8404507400d244c3c4001c0044c3c2510290340c4140140d102c100e061003001ca08903a80141c000708090001031130000b483c80c00404601000302090a42 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 665352769 1250 665351519 665351537
    0x10b0406021005062701030510110427020403060f0623090405071e15140d05061813020301050a09021818070e01051207050303030c090f06070501020c1005090607 71
    0x35584140000100c25138a07038500814175441862001c02020030701045d0b0301c1d0721a074000c40403140140c2c06202c8105010301403543c1090300d0012012103d18200000d1440706540c40065080f400c9503101400046004560205000d9120350010003280c805803c41680d0480c106010034940200b0400070069a00650350b8101d16039450034140e04008444e0444001c2d1030041100c1d61010410640304419a00b82800720380403400303081e40a954030411992158001e5006200c41e252a010700e0b401294040c1014200850250414800c0001c00d0000c03601d41403900140a5124150706091182a41c043c1003802c013001a2142600040c0040c00311f1001c181142d1980000511220108031080b400c2407031140032268060b8442402c17180c501c0090040b28000c102032203c2413600c43c00003d42000701c61025002d5440c42c0c8580e00301040d550301c01024650131050340110341420780c442100401056020310001601c0710303051403542d410030408d140c280c2040390510043c022040d1000c10401e400603a54205450a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 665354019 1250 665352769 665352781
    0x1009060503060f1f200a0f0f030516081b01050615030405191505060f0a03060b0105070203190203150c090f010e0d060c140a02070b0a090f0f0905010b0406021005 71
    0x10705100b03e07101000000042c034400d6413550001c045946808443c1088100c00011207031540e542e0f9003080c03020785010300c01900d007008210f245400202d0103000b494401c1c076081002c6d94101c030801c03003054201c4044500050015000503c0f100c7d864841400c04020711050504100190300910446d0041c240751900101007410040f0412014002030703680c0840d0000b000d0582060b0f070408480042140314136043c400050031070326100149101816008100c160740c01d00f16100c01d00142050b06440e41801010000c080250781d0400124510400f0108130118480281c0305140c1404c1d00078a15195602d07030039051010504040c0165000301d11700b40c903400c8103226000b0040782c050089071066034002060303032002800d00c8030a410440440c1a00d40790840301c80c10700d481e008054031810b035a510041e005450207100a2a07020010314602c0354030300c1c0031421a51030781c1403003202d520f083c2d0050f580b4a90702d4004100c00a80340c010720b401021081c4802d410030b890240e001e0341b52081d41c0c1c6950b950507034030000114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 665355269 1250 665354019 665354029
    0xd290901090e100e0c0a030807050114070c0f050c03030705061b030709030f020406030f112b0b04080906130f150918090c0b090909071a0f070611091009060503060f 72
    0x940d0610040c50015003031f40d2030071f06075255400004d003036803254202175840c0c140c404035600352800740215591318280060783c1c0d100e2210b5440742c00422941d03402401e500c04c6c102e940400152106a000e40c01522190a20070b12204403040a250a60190382c0f051081002182d0816100d00440f60021001014080b0b01d2000030004c0ac95900000c01c1c48004800b00c03c20f00140d1400d40350074100a035005a06c61069001040c880252140c0c3d0301600c032101d610f1a00000c00214001c0d4200c0d2080321014103010300400002c074543c20501d246110101313104400c1010341c1010030004028005c00e900390b90404010400203294107000d01424450041141004e11140402c3e8041c4d0b860070382007014122410b0300c801701c3c3e01090340541c10480c4034461140c04181d4203900441e1001c1110107a0b0b01c24040080d03400c00d000e850b07801c10b030700d4041000342c01e0060780007044441c002c1500b4491200041c80e07603610301100304401a01c808183e0740400041c42c60034429250000d0480b5003050003203d14004125100340011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 665356519 1250 665355269 665355283
    0x4b11070f03050f0d020c010c08150402070201051b030a170606030a0c1115091510140105190c0b0a09051f2003060405091903050d290901090e100e 64
    0x1511000940f504d41c0b12543d81c013804107003400a000b4882c00703081d40c0c01150811000c4d60080a00000c06900280c0781c6440c0d402402c1951042c1001402c00244d90030300540041c1c4800c4900361600002890300095900c182c7d08100c00c101038180419509000c40443c030035000003041d98180c0c960b0f03240c248240b00e00482c817240381070060030215a441415088110070790b041c00c0e6141c80c0d039031203500ba4013941800c4075400360b0710072003183e5800c05602c2c0c5010071880b00d2541c0104014113028003001b98044554030708040c20a6103c094807202c07241133292510f101000001001d25550764070340012040014800300b0481d10005000e07550300214089010070900803d56800008010007d046d19081c54141c2440034521560084600301b0070f5582e900456511a442c0b02c0480c4c0070840c0003010480003a01031000703040301000c42c4000084074201444036a00c0100100789201e58aa0b07440103801c07162803c00d80007030140269040620212000b4034405942e4104105c0e0480708030b07200c030480441c2d050104210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 665357769 1250 665356519 665356537
    0x5060604052e091116080d151e05060313030c03051c0e010608010e0a030309060204030b0a02070210180b07211e02120a034b11070f0305 60
    0x7501201481401e111890b00780e407152160780c03800c250a855036010100e0596135418500070018241e1402030b560034100794080c00d50107046598840c0d0034009400098040700c05014444542521036082d041149038503006540101d100b40f00c10010030107180c1001e824000c01d01d505051020704000c8600e4182c07040c1c011503022403881c0403101038031220710305250400c2180f00e10314002000b9058651000500380d07205400d550f107c5500c000748841c00a4802d030701140f80103000b4403005007003940729929102d1003e01900c000801a40219101d415490318500c649a4800141000100a044461549120a1684101142441c009c01c0b003506020031b03e030fa01100724440040312807080343e103920043c1c01d00c0300004450740c1141201542c5904036000040c081108004012503a05040700c01c1ca088000d0300b0300450040c4030b4043d04036540030f8801610025014404000c1290302c1c081704551983d06990388224100700014180844400e01881c41c030101c48049400c95141c007a0042c0701d0500b80e446110348080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 665359019 1250 665357769 665357821
    0xa030818150307022d030a12020f0409060513270302030c0a05070e0a0614090603010905010f0506040e0106050603010506070f0b0f040311010c0918060902030c0c0115030506060405 79
    0xc11038496801704070b44641c41c00342d01c0c25048003001c880018120b00c0c490850480ea603401004604da50b28000c0f01c4248030700901000c094541003d5540500544d00690702070001d50303466132014801442c04010b0031101c0a000902040501e121101440f98150508072040130010f980e10200300303045c400e00032200c444544804a030120300c41031629907500c2d034103445803400031000c6401003055141c5078000d0350122011844903068004404003040082c210291a1940c5136584584403400600c003802400300d4010642800030301072900806200544025000001031139140030014000740d541c80e020380e810750702c0c1680c2c225101c15513071410482140324032030060090390a00080140701ca103800d2181d40720314071a5a8094a1720380240085090300c100a500d14085480c050040c4111441185100705250b9000400300f101a500c520200c1264810344d0041707030f10080014007a401c2c80c024042c00030025002404d031004d5038074603280e0b01d4652030044d059511854641c4003084000280c02c072110901c19201c24 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 665360269 1250 665359019 665359021
    0x21e0409020406152d030507110f1c26060411030c030402041a0d1104020417030306040c0207060903080c100c030b0111010e032d0f0406020c0a0308181503 68
    0x10040b655801e024401c40c00585a449141c1710103e80209145450500c2da1015100740c081100036000340400034001d40401c103500702c450900c500100940114426a50041e01c0f80c0c01c0d4000c20030030a5003014907104203001e24404650b000b034008550300b0a884500003100301441d211400040c001d8103070307460b00424180380402841043c1e040000114000c520845c2d0800107a01460722142455036121046540041290103800204850a0480c11103200003400149083d45a0400090254104050a82035071000c400c0101600b45071194640d81803035400146641ea20300302c00100840504c0c00024a40100412101d110b2001000040440d40710f00c20305101031050010002d00034400c501d001c2e0b0006210380b01a00107a00c043c400c008100c80b460300503602d0845180005001d511811404600ca80301080d500040b0030600d0001d05400c0c1d182000325075469190500081c0341a4040003400d116400c02281003000484000c111800003a00005056050720a80006103402d072510516401c03600c4000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 665361519 1250 665360269 665360279
    0x80d050a05030c09030d0f08150616050111030946030504030c120b13051903020705030a030206040c0b03151314180d110a0b250f0e0d021e0409020406 66
    0x94800e5901f43d1b030340c1e60785050b282d4501d00002c8480150b10103403034015034100941601d04040c0071360004080e0043c070010030b01160040210b0700c5a40211202000c5e5000444201c60b0701981000f000303006e212803041c00154142440c2c419401a10313000d0200014201c00c0b40980c1098041d4007a40c00850308000c0141c0500d0f61518500ca000c0d440c010200c0d000030b031800000e1403448100401002d925040f10013403500d4490104c11454500c0199015401d5125151000810760303420450009260310980c0609103030300f0545401400485e6a81007040402002d208100750b020b40c0c0c501445010700200c0f80340001a452401d000300900300030341c40c2541d5010702800c00800c0f525203d440104075441034202c0700c010714640c004481ca1000135003240542e40002c50711a02080c9041c440980040e20314240200c04c0000081041104142c1e42c54003012541c0040b6140c9a241c00c0100d00c0e00081042c0d940c0c1c83c624078150b00080e220700c050303803540d01ca0706541a0215000c0d160703a80040c01e0341754094402c01002d6120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 665362769 1250 665361519 665361527
    0x1f020105010603050a021914040305073b150402070b0a0e0d030c050409020d0e06040b060907080411221805010b011836020310080d050a05030c09030d 66
    0xd01480c00440d00300f00c0030031a201704074800c8030948159586069400b4a10110486071a0050b000d64005000c0910011010840034402c0100a20032030103400c02c0340b400100e000045060240d0400081d0054050ba40d122403000c002d425409078007000401103020300000098028040d4010141c9221082d504201d56401395900c160302503c0110203c030514044554100c042e0340024902c1c80010300d09010030000840c80750064445050910400318003203102c42880c92609000300c0f815100100000b051140a0511120440e04122586006651482d0a80320016404000c0908030b024024141420340100c040302c0030901801c41090040c004180c0b40301c0c4500400c020440240d4455180118004e400e40c003070442c10074400d84200c072040c00d040c61f040242694550740580e805402d010581405100459150400b030f10042200340183c40c3d08200040007000c032580d401500303290b4460814919040d400005030b4070019010324200e5038035074031010445028012542c1c0c2503014070981061031801c50300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 665364019 1250 665362769 665362771
    0x2010b010e041a06090a0b07260301121506090c0e0306010e0f040f030c0f0b180106050922050a050601170d1b031b080c0d02010902100c021f020105 65
    0x2640e4440e4045405020081280e00341d44600314400450b0b4003002c09404d00344007a2a00e03c0004000c0e44005039214074000050f4800703c012100010107400150040c070720a00b000c071019450310205800e540c180b0940269a01c2603d101401c1c1c209881010705c24141d19410200140c15005400c0c0190070f00c0c440003030045402a00281d20a0051000104039000d01101d070300d20805040d44001d4280e00c45440c0c0041c0e1f0005d100f41501003101d405071820124013a052001c0d90b4038031643d00c01090745050000004400011448101c051b41003400801690340d8510f15290440510005450b010340d8070300040603e100750440c000d01900840c0185000d000020480354101c43e60040c4003501d04c80000c0701d00d074a40003132035090300208440001104801401e1401c0e054070503c00c3c10006980c085110f4001420004614119000c1400007030746040c4075018400301c110590750b40024041030b552540040c051491540b54801001450800d900035599086404101802540b420054140d07000b40d000703000c0c1c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 665365269 1250 665364019 665364041
    0x2032706060f1806091f0e15061e0d02070203010e0a0c05011b15020904051612110d0b04090b13050606060f03072709020c070f05030307120c0f030201 66
    0x60307092951126030400c3ca1900c90b403003c94000b00c00300b50703590030108041c3c0e02c4007610320090f00c2c3c904007082d43c00c9540c01c0120400303041d02d904404038a00d4030b0a0240c00c00304900400314080c000600c074801c40c082c100c1c6d0742c640b1618036141003292500ca034003914100900034088060360540c00e046400320b2000011039400302c54ad0058903280e103060340f91401960003e4003000003140901902e84580d010070901c1d0070a8180300c0c114030000d07281070009000201510310540300443c0245484800100c9690800310800e501407600400b0700203415a6108102a4090a852856815103840946e02d070780d6583d41c040c1d406154801c00c54007050600300c01c042040602540c00f107506d0b21400000c1000e601e040c2060fa86100d2100446a2450b40d03064412510380d1601050700e100706441c07600c564022280d405810000d0a081d000c01a181e00c83c440005162824a0f030000c3c00f4040f91f00c42c00d1109880100c1294802904564048880301d403081c0e044601c000e11840c06451032401080e103108060307043d003004400e02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 665366519 1250 665365269 665365279
    0x2e0302090c0702090705030c16110406091e18060c0504032904080705010b0a171209010c0b07140f030f090c030706230711090703020903100203270606 66
    0x156030401806900d209098000c4c0d0300c008050001030a46206e08001c590001c4590451400c048003426551810780c001c400407500d901c3d0040e141200c904261140600404100b441070010850b00c801245c0e44600d405034040c0810744840b50802521180044081c4c40b82c1d0118041015202d01d800041454100c0e01003100d04201c02c540301110001c00c80030707604031400082840680c546490741c0e05034069001c68401c803543d54850285d8011540c03040b0381704005203140840042400a5468014141041f20450b845828800e104400460340c0c0403640028450303000c44030207220b4682030020380d140c40003180f81c00103140c1c0c0001d0840c01c1d10380d141c01840c00b039a542d410220341b91f21050760040e00d071641d000c00b1a40580c800c00042103240e1042600ba0b200c0400e0741e4201907408230541405080e9400840c003038814401503905d010203401e161034401d512100a01d000c40c2004066400a9150f110601d40d00c1501c0780c0100c041341030107420140c04085080050910511003110a2007103403078800844d00c0c58820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 665367769 1250 665366519 665366521
    0x80c0c011205010617060d05071806090519020310150309020103060501020a032f011503050c0607050604081c150614090612070c0f06090506160f082e030209 69
    0x5003401e07014a50580e01281c44913010480d203030341c03180c816030401025144e1141403800c40f200800c000380301e61006018828502900701e1908803a600540318103a012a00340381c900340070400003502204032240140fa000001582d82d850310340323007800c24014a4109140c1c0c4500c080c0c00d51020f071f030141c0c00003601d03900c00c1e01e0074081140c4d903800681c0c480201c6000500411142c414001101c82d1030708141508041c404440710000309070800d064211450240f803d50710641c189010b200380070302045455056034080314047d142245a6075800d8035845c01810043c0401c00104581e0902801e00c02036103011602c52204200b8064110691007180c0350724400e40001c68280300161120410030b60845051075006414145000c61464012501140007401001004122151000001c0c00480036002c181e002c0c030350104a12145040039810701c14017a00c80e100e02c5018140000b030b0241c0001d4030810012583c140b000c0740f5a10140c0e240c00140e941003613114480202d41c000c050310b0968480c0d003c1668001d550340105 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 665369019 1250 665367769 665367797
    0x100c150606020303061302160b091b130513020d030816020d140d2301030b010803030f01060e0f03010204180f02040b091c0f060203040204050609011a07080403080c0c01 74
    0x8440107402181c00607041000010101d0500e003098410028024200624014480208250000814000b10396401299050201031704081105c162030b244400740752028044240000b030285a01d424040d403405858200207103900c10b8030b01c0d01c1040d081e0040e121130018862850000d0005804640c124444070031035840c821010f06c0000c00f550741d00c9154440c8480150044000c1640b40c00440c45440c18a854006440b0b100d90b0b44886141d01450120b124802541145000c0441c008160007088075580700b40708226800130507000442c1111500d00f4640d55002d056008030700e100801d040c0c00354056000150002e92007070716196403400840ea00104010600951542d001a8480c0d84140b886010003480048458982500b0b103c0041d80c1100090318603102d0340d0b03600f02806580c0c2c0004c1d101d09a0100030001076041600695038426402c50320080c10358100503604c65900c22002d9404069400807516401300041201110083d5400510322516400b40712401740c1e403034445070503007800a0810307141100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 665370269 1250 665369019 665369021
    0x2031005250f050c0f010c0201290105030a09020f040504051606020703020603010611160602010c17060d0b0a090f06061401050c0d080a090b0a24060c02060711100c15 73
    0x24511965954102000e101c4500443d1a900503d0102c6090300a4070a8a0f00b012024800ca1414580d01d070004511800111034a440001a103041d2507004002a4400302a036a0300c0011a540003944650020301103416002040583e0720b4000d6594015181c034041c0700620000003001c3c90741040c44404106481c4d00c1e1603080f43c8859082c0b100940003081480103020a0340107030110810800080d08843c60040c419029503819403041d80400b002d41d5451102072607c66000034000c420b03040d01a03043c0403d0070417901140640301d10031000703054102400d02081c201c0c0181d8100410181d040b0403040391a4280c0e0078014000c2490303100d0360b101305818022800381540108240c0303202c0d144110103482d200400400c2610200b10081204103419500d2444100143d41c61800c50300031362983c800059001c1040c200d14031800c020b498200f44020080108000c01d69002c0103103500c5a038140c46031529a142c0380b03801726880690800c403540c05a210240d22903c1544901c000c0e400900a61a001d038112034912840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 665371519 1250 665370269 665370331
    0x27031806020106080c090403020c031e070f080a1106090a080c030f0d020d03151802370e060d020703120c090f05010804140709060810020406081f0302031005 69
    0xc1a03007005c0c600c554685802581035a0250007801600c00502c003001c00241849001a12041c1440405d002400340c2001040010b002c0c1c045002100131060801c49007a03640c0c500440020600c4498104000c9281c41e140180c40a0810182c148081c0603280d4550f2921190301c403040314000c0c4521040080d8040b800145020b402c40241c029188403900090101e024003009481c41d800c00f018140005803240031003941c4122000c031114010b803100c2d00344940e661a41e01c000288040035030034600c8224032018030864242e80b0401400c0a00d0480c0c6c460021074414080c051400c5203240c8042840b5042c5600203c29a004801f255070401a4005400003a2401000e40c0650800e5034200c81007408254002c44000740c0040c000e80380140f0007600341c10701501e84100340e00f00788100c07912800100541c0e50100301d201007250740c101080d8241402d082c0700421b85c520080c20300000505071072121400c58840200744010310340241c243c07010345003143c0c450005000c00b070321041c00c20070303101105003114418035403a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 665372769 1250 665371519 665371529
    0x180203010308070b1e04030f080603060105060d020a03060816080d140306010c05010905070602070812180402071403030405072111040c20070602011b05040927031806020106 76
    0x154204031644c0c48800041070f00801c25128001c0380e1060b00d0040040f0381007244110320a5a0b41c40d00c07903042c000010400240505554000e034040c10041c4429643c00b03003510218019500b0040e2501141d900481c080d00c000d90150a107801a501c48000f070365600700818043c0e0b00d00c04c08070381c1c4001e204841100e100c0d40f020121102c81000380302003450b40d03200740f0a402c0118000d0002103035050250300c80c1800c201181d840040035910864081200e048103220034030a4400615846040502c015102c02c1406c440f05030840c03240d9400901d07001040310098004500003421000c6a8992400e40f501d0359851044d07001d04142404d200394900003203901d95003040945580003000d1f0780310018810a20000d42420f403078040c14407070400b0100d85140c150a030206a40900d0300e0003090081d1a14034041d08407000c2200f8080b002e18440c06001c0340fa60071000f11021680070840c00580c02e540c00c102d8441011084640503400d9005030510018994401d0002c11481d40224400441035078036001a4201c510a00c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 665374019 1250 665372769 665372783
    0xa0614031603020904021516020f0303070305070b04292502100510210b0c07020a140406030803180c010e011b06020d05010b0705070e0106050702090a061505041802030103 75
    0x2c0c0018249280102d42140c07025048480c1d400f00725140070503d8111404107000103440170304950030340c541070b03403680c0380030708154051031400401d0b81b002003c51040c00300c090300f9010144041000c1001e1007a15070078400c2e0f144d680d584142c60901d51046d81840c1550b60118480301b0081240c2d4070b4174401e01c0c0701881982382c1c001b4001c000241c40da4401078480200703682485e9003604d10010724000c440c1d084013025854400b0104030b16107949401044100d0203480a165a48103106c12070058544c1914103069403100709100001c400081c000401a28030307034000802088020050000d0181e000e002072034103040d0344003911203c80b400001181c0c03418480d50030500007140465800c0002c110b40c40c015003c280100009403506201ea024001594000c0c3c3c080d40c1c1d071a500162034000c0c898103108810160408140f46501c0e03514140005042c4d004050700a4400e0340e00307a010540c8000c250340140c0052008142c810000084000302400d00e40203807140c0c1d043d5045200e002401e40c0050305c00c583c1600e0f44048 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 665375269 1250 665374019 665374063
    0x2090f100b030709150908010c0c02040f18080f0910031b030507320307090608090604170c0f01111c1b180e04061a061608030a11030a061403 62
    0x164006510f500281707440600c01107050100d2800d500f170140c00c02e0044d454840301e043d1303680c51061208464840070070141040c83c1500c0440300302d00080d4450a810781084100e626441d000c0e100d42018454607841c2b0303520039002c0262044064140e0003003030724014200820042c01e40d80c0078055040e50002ca41400c0001e00107200144034151103903050082580010038090380d101c40c1c00144065600507907101010580c043c0081141e40d501001d60f90344841c5003c054851410306640d481e503240e0090004c01b00b846404103107131550305001c201008001e81d6010081c40741d5046040000301d290f00100002c44a910740c602d0070701d8003842d50b010310f0300081502549001035131000e840458100703106018054402c01d02e0300002030b90190070100b1070302560041300001002d0101c1640d070701e00180440005030003090300344a4810112009000d80c89440d80280342150350b81d48071a042c00040101101c001e000c4600401071007001f50056010505550082500140c1e41d2000401c041c2d0740c1c070003c1d10568a48003401c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 665376519 1250 665375269 665375279
    0x3020604060c0909090506010801180309030809131407030b030106050109030f030c08030702010219110d14040914150102121c060f0b1309061206090f02090f100b030709 74
    0x151000300b103481e0620f001e10f5100c2e1a101101c0030b50700d00060954543d8480d03030061024090038450020600180200da2070701c03122550740034001b98020310006d4055017010610090075103800c0d41c090480c14412000f04841c3d5022040440100b00641d194000070746800400c9403681814401c48082d224143c50381c107520b03480c650381c1c65110303604200c0071403c0019003c0b0401c000f918400c00707035008044540026131030303811654944c1224200d0b51a07500402081102030041c4041c0424910310301c00b141e150140c028407103404500054400c9600020007580381040c10589036081a0b005801a00c030312503d1105d02801100490f1340309100840c0100102c0304000c14080c0e810507000b020030032070b02c4117800319259969075925401c19945a018001e001c000146c3c07000d0345420a40d00501074010000100400307820805104a80748451000410f0f40d540c40018001f03025110307100340f1010390300030205000c0307140c800c0c040d40c0300390007d8848001d480031801000c50102c1a24066074401d0340255a0260710601d07003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 665377769 1250 665376519 665376521
    0xe0345030a060603121b12050d0b03030a0f03140c0406080907080105010b0405041b0806011103071b0806100305060402060a031409240402030c221a1c0302060406 71
    0x40030350510444032040300254042c0201402035002c0e40756156244032207040030304005582104031800b5181c030302d0a8400201d100b062038050200c2898603607140d20258080c01c0007401c0640c0c04d0b661512000c2410002158071024801340c0d0484d903941031043c0441135501d011030713100607501d406e1600000d02051000324810070074903622a1481c42240c1e40c0e20b0b600c030441802c503902a003160380e1401c4001000e01071030820380541c1056080d0240c0c6c00640c4d03114480020007038540030b0907540c1000504059150214003c00070f031505a0b8000e01d40e170417400001c5c0c8079250550560700c2210114003801d000204e0000d2542115401c6030f070404040d181030341c0c1d581d0030004954003201080081c980d841072280b0440b40d42c1d140a03442610307100010101011034800c0c518030312600c1107084800c0217074041044016100800c1d01464000c081d50304003030390300340c0c04812101141e0042030401032511b07100e072032170b0902d16a290400c00c5c0001651100c0300b07075226200d15000b070b1903410405400f5a201c1c40100c1c0001d802 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 665379019 1250 665377769 665377897
    0x603041212020307031b0215011a0f120a11040b070b100b0c0f0708010c022a1f0801050405040809101b06050906010e0405070e090705040e03 62
    0x92070704806520900c404201243c10540c0d0840000e5aa0000b401004c1050103032403202614600044c28050140c50900d071882805008491001c1804040504504105000d8039002442902e600c0d48680c1c802e03100482d800b0040759000304050400c1e4120920264100c2118203440340f0084180c45c1810941783d04040d9000a031110f20031b400c640c800050f40c140203002500e418004607000e8140d6006a140403031070071605400010b416498140d15441c1980c001560034180e070180032040a80d4620b50b12140e41d00c80440c1c0c215a04100c1d043da405047e600b0300b4140301da09203ca83c55881300d698840c0240001c61f80102d6004001c4801004102d8040c030f0111400a0100308602e88400c0700400800c05000c0010103003402c0301d0050701c44c8113000f0741c240148030f0540541008a44090641340a440b81c560380c00c4688034072203d80c984507020401e00002030203644040d000140060080444050440d6034039449400031403e01d0002c81c08a030361a810b004520500c41200621290745d4046100d000d000c4014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 665380269 1250 665379019 665379053
    0x320706050307090e151f05180409021002070f0603060f140d0507120c05030a110d0f0c030b160806030d03020d0906050f0106021207030c0f0201020c0d080306130902060304 75
    0x4003c001059032002c12038610a014045024807154000307018862a15a81c418845821505034042020b8030307400026201880c40704500318034100d00c000c020070b00800420001039001052101400c041d00d4001444608031907460310404c504543e1050200e0444002c1d0040300d808100d9030b001003020002035880c0b400340000080242d8484074941d42c409180c501a94403c11400c44035a904c44c082c4003810458400804095018143c03088840e03481d099142d1072402460700c6050000d015100b8800c0101039104415480a550042c6945900f80100103a0080b00d9440241c1c001c506030a000b9849000308c00d00400003e00280345507010000150082e4000e0481d02100755910410900480c1990040902503c0c04c501400055410448001c1c14400d1070a16034503446820001440001d5100c105000010741203000040d036040c1c00c0c80101c2c2018841002d00d980a90401407101c103010b180f5008600a60742110219048401c01c21010305490041202951000b010700004e004a8800112070a00030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 665381519 1250 665380269 665380277
    0x132619090302031f230702070b030618180304080109060621021e04021308160b04120c0806071d010c03051e0403140109030f050f090111030d09320706050307 69
    0x88600b0b848000070005d40c112444c4204041d005201e1042c2d01407100401514000306454a503150410105103a03103420b0fa041108910020b0004250400038450301030310300310300c4080e031ba038542d5a03a40c03071806807199410565005250500c00a0380e100041984d003560103110030b010a00900b20f808000d10b0b81d07070300c000c0c0b00c902c8241c00c030481d1520740d1b442c030080c0104401c401c52400850308191005192426240d0220b09140084209100c0700c6d042d2002d46040754a40150307000711140901c0c114404403110350001200344105428080c0c0c540d0010328880d40c441e617002001521014500044411100000300500030a0003000074141c48160049000c01521440000343c1c0791580c1ca645101c00e03110041442c00060755110b03141c20030560b00c4841511aa8441c0c81c14034200102030000c040c46100300ca2825040c45a1705044d0001010f0920694854020601c01040040300908018011070020b54420b038086c404050b20702624521031441c41056111400146005424000c0580d480e40c000b405003010300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 665382769 1250 665381519 665381531
    0x20092a0903070e18060603101e020412060b0f131a031f060605090604090b130f060617220c050901032102010c0206132619090302031f 59
    0x65141040380c40000c10100d150300c0fa0314503000d085039044520f80000744940341c10000922801e941c0010340018469814000082d10b4207095440d003400c003140042c107010483c0007090005203050384c1000016841d000e460284001d9a4000800a03907520742d041e40c5510050000703460f041c116140c1d0107210520500591003500c030402c4e40003c1c3ca04001c5413079900c07800342d0a0700e0380b445001d914001d40f03005103d1400c0250038201c0132000034030980a18003840641075540d8400102c50341e501c80d00c00002d0309000104001c034820041100012701801d00415010400d46000d4038040484141110310032300c00d0080f1119840004107080400301c05186090b101305661071004500ba54446030500c0c0210b100e002c422003c290b0b43c82c84150b0350f89010040c0010b5900d8511001d41054000c100150b00c9031f0200e030003140125561911407011889078061100300104000817000c110740c0e600042c03098482e1030540f010320701014038045030240110b020081d01504411100708524484040a4142000518000c611 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 665384019 1250 665382769 665382787
    0x207060323160216050906060c0313140f0d020a090c0c050d02060f0f0403140c01150e060f090405070909080f0a080106110a080f0a02160320092a 64
    0x901c03006464000d0b0508001500305a0142c0400c695440050703804a440b461503d09000201a2000144958000e802c00a812544420184100c0d120110345c01d511804107612601030a010941d44081380e4081c0400110408103841c0450401030f07026030007040302001606015801000d40f421110013000c2c01851810f03640020707410b000b070011b40c0c645940102000c0c0341954400b9000f80003c0c01c50b07409e10a402c014400400c0d0700c1007818007610740d94100d180d13881d8140281030f4010100f603c0c55151952446401198800700440000c2c017075a030172560300d01401118010802c26000a580041041e1b0116404111030000b0390008009140516503660400b64590502e120301e600c94503180c00060110300c01444481e801070712860000044500400050005941c5c540283c8100900b84481c1c07100480c00074034441c401c00116041d102c001001c840100c4e624076107440f01e464a01d0005900d0f250100180e80d003030070401e82980c440e0303e03c0850103a85481100282c03503e03100c000390002c0540020010740c0d007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 665385269 1250 665384019 665384081
    0x50411071709040b04091a040219090501150809070303080910050f040209090c181302060a080106030e03070c0501181a0417030403020121021e09010f030b0102070603 73
    0x2078103035030200780d00303540b000d42d4010003040b5500c42c25a18400d40c506011640031405840c1d42c8441000004103003c00c90304d49000041d070400c2c040c5007500b45206005c070046403603491600014100d07100024100304581c00c072402642c004030110b90044a13540426030030004603200310328568200c03e1520030385410700c1c1c500b0304034820b0b10030031214104080442c0c0140f0007141089428658030968800261038004007000004404480746140d8030350000000d00440d4101d5081c0080101560303008007030940d20f2064060244c9526400d1041001092918400501204010080707400300d40e40b207010407000d6800c0c000107407032031b220a040308414480800381c0401c1c0f50483c3c9549604a40d1100300ca10344a034907017098102c00d0032107509401c041e07030018030007000140d0300030340d102448000c942c0b454840300002e02403990080c000c10003400a801181c13007080202120b85d0340109143c04003a61240d0007080c5446c0107074192941c40700040c0c01640402e204000c06172083e803218051034517006104408030b00035001d0300d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 665386519 1250 665385269 665385293
    0x902030103081207020106140409080c010509010b091006141b340b0904050c190e12160e07110109050d030605030d12020a030e06090a14011505041107 66
    0x10703410440056a915070312820070f40030307078040c0242c40240442c07801c06004c1b2030700d01b401030a414000c94461508030104070904080c1c983e4000118020003092400d07464940c060860400298003400e401c1011502d0021440321640580f02140c44004a00c001c280d02c058155100501e90304150b0032002c41d5005c80d034420311888001c0815108800c000d01000d030001003627500088600c02c01c40341da0760020081d4070a00c0060f03d080c004225000101c540d141804400540300c0d100c80415103806804040302c80c1504a18091102c0b4403da03910800081c0040e06503540b403035843c0c0300c1c140710796114034104582c084405207280d1100c0145800340c2000c4110182c0e81c00d66070341610469094014110344410564944164070041c90218002c100c04080c0c25000740003003620151900340c060b000101002d48078000e401440003042c081c0f0440708145401003c0c16103e46001e1800c58940d404521a004114014050a4aa564941d40140c1f110346400100001450a102c806016210a01c406e1000c41c600c0354800d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 665387769 1250 665386519 665386523
    0xb07030f031107050c150403080c010632090415060603050a0c0e01090b160c0303030b151e090a09110304030e1801030f020a030b0118060f060203220902030103 70
    0x6985000324004060240c40c1c4603a000c1e03100c1182400701001241d07001500440c413070760548244441501242080109101d03580020f0404200066803010005c1d05600c04811104809181c03035164000065865a40301500d1204038143c1d002c5103614103034036010303890b0754201c0e210300036209181c140040602d0580b90158807902c00f090742c034801c1042e0745000d80142500320640b464108080c586c290b0018048107030b24040c10120325000f07d1718810b542c05400c0821445908034444108241d41c9140040141030407100041c042e07803440c118103580c28000c4094a07620100c600e001038040c00081142100c54100342c1090303034000d41c0d010000408040601c075000b000308808640a0b6030b417070981000f42c05540d0003c51103000e101041001994209941000e505481d4495401c030b20303000450000840e0802a5000501610003900000030624801181c1e42c41c0141b00c50300c02c1c008207559a4011448500c0c034401c00000d41c10070464580b0180d4140e054500c44d00e0701a40c40b40f10707107485420200483c1c00907001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 665389019 1250 665387769 665387777
    0xe13090606050d030215070201180605041b0803181504030b01051f08070e0301090b090102220b07230a0f060e1902060a0905130516080403080402090604060b0703 71
    0x18028000c80d40035101c0a00b0095511568001099a009645619030300c3d40d56011514007000c1950302c0e200390070059864800c420710003111003031428820010030b025601210408440d0020340c198445a0b4075180840710030700051400e00042000521091011694099014140c6690b50301c0d034220100151000d075000f482c40c80070640c144003c0c0326142c80f0000054000c1402050b00c64580d540c00502c407075018041d490049032600940003c01d0151101e18070080c14155000200014241c055000e819900039502c00c400d603074100d0440c5600369a84600503069024003c014030808a03a08840c0c8100c001c01004006003011441700780141016174201d401c891900700e407200c0900748411801403002850100015203242e10501c40141e0406009280090140c1d00100c0e090002d140180810401020040d06401719014881480380040c001115000d06085ca850f81b507a101600c43c2e0325591160340d040c1c075991241d2701d0716002c00c41d800000030301c206c1d030050301d403000401c1c00e0b80c01402070040d1034440d8071 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 665390269 1250 665389019 665389031
    0x30b0601030c1d010309081b0c011d030a110d020a140405060402271201020a09031703010303020307061a060a0512060405150405090c0319051c05190e13 67
    0x200040640d501c0306490001c001c0c0018404158560689a10003051400d00380010f01c40c40d2458244514007650800181514800d40210031018010691044c241426600d102071030701807012003418000702107101034240d840030380702d40f0001d40c004c85c1a06071920000c1c982c1c5145421540000c1195419400c00c140c0107c40048003030182c10b043c01041d0304090304aa0941c2404038100e95800b0001241580380c8400c000e4207114482e070b865a505441610400740000d550390841e5090103400030300c00b80300407222482c03100c46900800e5000c0041c0e9060300ea042e800f440c0351800c1d42e2201409030030900f008002488050344640082d6403240004c1014000c01d869031502d800107401c074400c0c07441008122900903800d0500300440e0307056480c100d0386894070850300022203464042c5024644243d00904a81620074400100c03041d406000f40a080c90340325004841529580c1100030f416400d1050400d80800c03014012082c0d42c0c0082113040490130341601d000242ea810850024001c9940c44013010320045c6e48036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 665391519 1250 665390269 665390281
    0xf05030a021204031e0609020402041401260c0f0f041512051005150c0105090303010e0a0c020c010309030e040c0806100201060b1b0a0f0503130603090213050c04090501030b 76
    0xc0300c00b5989100100d40a07007010300d9034852010f1070702080034081c00e242d5642c1d4100104a599406010b17580d801500864503a510f0360b181d0101c2528510704a0301080b4040d00301c0301e000310900010b070309040d804070b2001404d440d06841f50005400120200120358020b200c60081090348001034401086407200d041042184420040c200752440c000d00c0e01c425003440c007080b84142000c0e1810f000c44400b61011441c5a0000b000e90704d141c001c9141004055003007600744082810f0000207507050710a140d80105594584032000400c46201e5080840075030041d0f505020b496001c0e6200080c0310380281402d081d02400c00d0009400c0b50b0306000300c9004a10b80c90706100150a107404110b034110240d00003000464240507900e4820b024220882a80025041d207402c1d804209000200c03600c5d60058946101201c940b610640703a411a4841984d1000d89850000e83c0394031900641c810700d030300681071a440071220440c20300a0500203000103620701040000140000d00c510905008600400314007065013040303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 665392769 1250 665391519 665391523
    0x203090309091b0d0f060816150c02030a05010c02120c0a110a1e23060706020706060f08011a0901060c0201030906110a030603050601120201050301090e0106090c0c020f1009140303070f05030a02 85
    0x40c3c01a08141d840003240b448c079810100c00d90000e40c3c00d108010081002c01c0e000c2161500f5030148025014000d450a440803c44150458051400c6075003e5800c070700652a80e00c8160301900d1012000c0d41d00585140000c920810b0054a81c00d0000e8188003109880728007042c5290403240c140400c182c49607a04001b04440d0901034401d96107501e4425074415946000118507000c1d008001e0031959000468004000302513210340024880414154026a5220b0205008109074441e0300c411501d00c8a16100078a0f03c0890a4141d42d00ca444850824103c0c0e0011002048008004c4036a19a80c103421500382c0d1414018001240065802180303042c00e5280c4076003440700c180c3c04807011001608a140c0180c0c4c0100a4a064451140700021003044d9803801a015105903401451042c2c039005000003180d03030001000105500940b48040c680d00c1800902469664100350500012251076045c4070200c0c011480c40909400202224100700c01da0715000014a40d0500407034040c0d20014807a01d80ea501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 665394019 1250 665392769 665392781
    0x60810050907091404060e0903041403010915181b062307021201020702150d0b180c1e0d0e0708010902102a08040609090203090309091b0d0f 62
    0x30a6070101c805091201e4090810380b600d029915101c4048625502c26441d9980144010301d01404030303030040e003808403000b91240d101f03000e850b42e0b4034110740b890105404c0500600c42e401d58000c01150b050708030940d0907401802c6558494443d103480d283c1410220f54030a009045030f0703c810102d40c0200d803400c0d4000c1c2085600101c50b85010b106540a090740c28100c2090b1489185c0640d00194121380c0a21404d009202c0c0c03840080d80a606084010402500200540465001d240040003644c02403002c00404034940c60002e441c02c0001c3c00041c0c054448000a4611004801a100d2226034a0380310002d45421000d40e09003c99918041403958000402c000700040c00b08400030042c5000a80110b4401480c0d039010500303114400e481007184030418040e5202c119250340d40f210307c905151a02030b005038454890600058002003010600c071031544203da018a055400071860031303030b00c041449000e42c401041c0707004065140c25051301f08040c0c4402088203a0344080300041140c2021141802c540c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 665395269 1250 665394019 665394029
    0x305060609150a0e241b0706120e150a0e010f2412030507030513080609161a1804110d050f010f03080307210903030b030d0813030c02030a020901060810 67
    0x10711039000c085c40141c9004c2c10a259420040103a42da03d010003101500c13075100425240c054032400c3e00001d0455130007610b1000024200307009200b10380211030060380c3d46807440c948007a604911004110544240d5009012804182001080d80a8115104002c45400c030005001d440b884d42c08248141d8400d40c04900507210f20003105054030850b40b8000c000f0b00950740000c1c02d009000a50b00468003d240d00030700105041022515286040d03865036480380a1960b00f007103440f010800218490070920301c0858005424a0f80c1402c00c04105902ea060503d0303042c1990b0042d82d1034004ea11200200340040420181c2d9002c040740c241404020100c90040c16030005188241e444028000202402d04613500210f00e03141c0b51202d000d4003007840d074020301c500301400322003403800b0b90800030990140c01c80307042d481d412402c1d82c1c00c2801c01c0d01e09072680138045075080a207038401046000042e000d0480425040d0000d0201c0e40390078219404504111420f8004402080d10f90040114030b044043c50305001e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 665396519 1250 665395269 665395279
    0x3070509040f06120f0215130902030403350c0a0c110f030d0c1101050a0f05070c2103080619030b09151305010b0f0102210705011113081b010305060609150a0e 70
    0x1c40c00381495000c0c41c11b9010303094504ad00003010405041c03184814545440c211a211014414901d122151501041c01c000c401040c0030000240a81c2c0250251804502c058640e038180c42100e0f43c2d4886035400b1045440c1e40215420407502c6a902c0c100b100c00c1d0203400a8554419089140c18481c00300ca00e400c680a040220403c40300d0389090303201d042d072020b010140c14110785858562510004609541c0c0080d15841180b600300401e4540110001c10494025215201039445082c140080780c114130705040008140450100005a0510070a65206c9041c0040d0340094088041e8100034560503030b0001c0f06505054090018000f0a2080b2100ca800071101130b56807844d01c0b80040d454a0f001d03c1ca943d08890070170000103055840b48111810749a00000801c40c10028058050094201b100a004074080d5481d0210b081000000c01c031105070701728072080e041e01c0010350045014040050000b50001428440d904903030f12406a40454410a4400d16440c0c2c0c6401500811101e291102c5600c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 665397769 1250 665396519 665396527
    0x10207051c0207140105090f120609060a230103080310080a0f11041416030e12070506090a0b0f0c0906070f060b01090b160f051510060503070509040f06120f0215 71
    0x10f80e0000308540d503160f019142350f2902d48080000410312410803803600c801d0b0082000302b042c080000315019218904c511b40400107890385600040201180d6503004019105000050000c0f543d00c201840c4d01c901c842444201d066118030714142407006800c4100e892058541066042100300100b841402e88190740801060a60790340450890380050700104000c809101a0660944030b0341083e1080300d403450440c0d04408411008440c0c9501604041d0f0745402202d010410900d004103130400c12076040041035200e0b8655076030031049544068442606600100031001041e201c8502070304009028450400100b03001d030412030700b5543e03034903a07040c108030001901b030014200580c15a0812a1224001c0030051480c1c601103c0f01040e0320300160907449803041c2c44482c80d4400c580180300da40001c10840c200d030340c0c800003540c3c540400c1d111100403c0050081c000d043c14190300c40303041030000314408510707207a03030b09100402c10095041c2079850b14100048901941065000d4611350955440c80501d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 665399019 1250 665397769 665397809
    0x12031d0603270102070309030c0815040b0618010e0406050a0618020903010204120f122d180b1b0a020906190f06081906060e060705010207051c0207 65
    0x310721000700340000075100c10701000200d12206108400006100e00210341e07942a40c10013400018030b0b032104582c4206521000308a401b07000c981400c00701020116a491b54846d951400b044c410001e00e13242c1c01070096081150004868003545008041a0106c0b00c03003030800c0d05022040d80e00003407080c12003038104003042080444040c0c1b007030060b070005000140c84011250009019102c0c03503015064011a000c581000d010368807400401861061b09450720741c5060540995001c039000d40c50516120780074044e10441481003500b0290440c0b540f41007a04c0e06901c072030040e251203a68000102d5a0004104041611001c9000701102c00c44c4a004001e0f0003200c1d0300045481c3d10050200c0e01603030b400c188090194405881c1c0b1009000c20502c14500c098882e403006040c1501180d1464441d040c0d68014440610b4901c10701017034426a40c0c0d034010030076100c0c00748030301c90b031011804840e40c0d9803c010707150204405115031100720401c0d40700210340c90a0400000d00d00a050341110701501c0754998446c00d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 665400269 1250 665399019 665399029
    0xf02150106081308040509070f17060a0e270106141906231c0c05070c150c0206120702060105010906020d0e04020405130b0901080c0310021b0712031d 66
    0xb5000f40400e0b80109041da0302c0c6040c65060140b580501e8000080744103000f5015000102c6025a900c0c0380d0311f91000402c050203c014002c800d03140b55400000200c0148451468002c040781c0c8101a60358004606850842095000d1981108440d039a50754410038401d80040c02213000da812001c4038000e100800405003503103c41e20390311414083c802d1030124048909003a10800070b00310301d001206904d900c0304003081d10410980004801c521894803203188080d50141e02030355502c48e00000540b0080b820810040c1168042c080018184100100c1450040e90b6500080200c00b0b40302e10501110306200401919000040c0c001c1414003484400a00c44241d00203035100e01700000d440c09509112502011800a100b03d4101d190020a40000130802540d0b6401c225050b0074151509041030b80e84044450f00c4030320020006915030488000707598088403d4002c1e009c055403884003943e0010a4144952400100c1d60100000030351109c00501410740101c44480754440c5005000301740360700800011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 665401519 1250 665400269 665400271
    0xf0204030512180603010e010e0a090519030327020405010503010c0804060c170a0507020f0102040b04060c06020c060103030801080f0a2d140c040b1203070f050c100f0215010608 78
    0x103a08101c0100d07a09100843c074035200e54100c403000d032080d075503035031214a5903403000801d02a0143d80c10089010034000d09c19481034039515600800030381082e09030200d00d41c030014104a800c0d030400da1a04031594000101640e013401c10b14185180050b11102031051105031101640207503c05c1e403404400154050f080300080341d03c6580503c000a102800c808185e0f52113403000703100d040e6203801d5420040e042103e50321144c003a82c201d801301d0b0414508803590301e00381e2145010341e10380480700b4802005014050242070240c0d0b80311301009410302c0180c1c4501d91070304100342d001b51f00007840c8a0040002800c00c0c45003600b5020703408040c058110042c2c8441d035480d880d248402445002e49071600c5442007130310301c6128400303601207040c41c03803c4006007040355282d02c90038180c0d100d6850700074104140d15040c1486070301c0b4503480b00a542480b441e03440c1d400d0b551500080603a46030240042542d965512800d9280803454180c403250303180c2c000803000914201108100341c2010302c046c0f00500001e5005010a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 665402769 1250 665401519 665401543
    0x30f0b06090a05130905010f0209121c0e13020c01020a230a0518090114030c0d0c060302070f12020a030905030a0308041401090507031101020609150a0b12030a030902040f02040305 79
    0x8101c050009100c428005c0c46107500203444c6500c4c00d40300559400c0c490300185651002204c482906243c0e014546440340d504070341101070080c4014540d09241e001d0b918844514100610301003420f06004103540a9902c80c540e10649a5800100303049001d82110b1103102c4180c4000302c1c4031030038000101d03102251080d20254404e116002c18004440c41d9940349d007890083c4081d04181495940e41038419a202c1d01802c0c50740b2a0145800b441200d0508a80c00d104440d00030704681c041603d04003060303000350300c05030041d036072600d04010782e00c049006071030001071002c0d003507000f0038a4201a0034020080c24040c3c100390300c00d40140c1821000b0a40c0718600940090b0441c181c1c03d424010844040d00401c00c005000b40180200a0000140004032941110b0298281c0940c1c0c02c95035042040c03a1195a0600142014010600403552a50b4030b45d2000d040720801821711010030703400a501500d1900b00281c00b20000b605d0b03507861421400e040c00780c18002018590154202800d683d5216280c40200b008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 665404019 1250 665402769 665402779
    0xb0406020d031e150801060902090901090c110d05030703150e0609060a080706110c041b050f04033516140703020423090a020d0201050c070b0406030f0b06090a05 71
    0x88070311100c0b481100028200c240d400c0401c100c2c44c1d420041c03001c0c0103203442079049652074003000213008850380c0200c810600005200440603800c115902004000c4031a5440c01c000b220528100c030000108489060189251030341a281d1800180080c269038000002903120440d01d401040f910700000080d9070002c00031140e80000360754580210700c0410403540490501c0c0300e40d1600040c00c0303401495401510034994266000250680d01344410345070700c12241101011551030b19600203200d00041c2c800702400750241450582d59031125010040040141c210306001c401100803286040307602c455a850340c50490074100a0b01c818070b40b9188425500107410101003400c440300420050102802459005000b0810030300400c5104030703210fa038001442c81843c1044003095044000054074012150300400d03035109155140d004440c15001040c0c42801445854000b080805500c4043c2c00680344907640006d042003894881c001381ca41041c111400355004005400658a409001e04151042512 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 665405269 1250 665404019 665404031
    0x403051608250e1503070906030605131e030c2028120203010b03070602150c03090714010512010312020d090f09320f0603030306030c0f03071a0a03060b0406020d03 72
    0x1d0040004d50b00d100a551501405c07001103400c1b0f1255100c00d0036640900d204024035503030760303601c40780f1010040801f4014011410003901d0f46840d040c071180d5014442c1c900b2000b4584140e13200d21100798004400d50307400001c030080040c64101000d1031040788240005113a1645241e05051060509902880c00504075595401c400d6441c2500803008034103010301281e00c804d85d5083c000351074903000113241c1982141076002c2509001043c050724050201503020b02501840c2880100403400f00c00c04280c18032100340f002070551210002c0c81d60003107000d5000c0768901d000c0020020300f8001c1a840390030034890851401c0c0f148907000b00184e41a6144480b00050070603c034001c014441a9821a0515007009941c07042a2082080a03281c01101395500e01001a118041003545a020485540c0e4050748aa441040e19103444140201040c002906840b4110b864000d41c4290100c0c400240c0e030813071000201016030070760601c141e03401402c20445042c140350404a0081d22390f141d51101e6410141c03151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 665406519 1250 665405269 665405281
    0x1014030a021503040f060203250c2024030601030c020a0c09020a1e02060406050a091a1b0a230f03130c0819120e01090905091507020a03080a0606091a0403051608250e 73
    0x44102c46040d48490075000f603443352949002c0c40e81c400ca401b0343c0002d06119410701814000201d09850a504c145035078152414091074000941120041d80200000800c0c2803c046d074805414410420059015202d80e01e82410b08a00b44d4001520404240d4508908240405d50310703240c0b081084008000c00c1c0440c1c880c0e81203107040c400601e4604420000004910110342c0d0041c00f490049010a010001e00204030101c244442c05140d10130013201300100001900481c0d40b201c2c00c5000c034840c15080d10900c1d00d4140c2e00d86007601009140852051843c00c0720144080700301c2d685805081d81c504041080d042c900001e08004403031150035041c540344c10108130f00d16010f10140740d6410b0318040102561500d0034000b5600c907407446003600414541e9021511442c010301668043d00e01c103442d44042d6500d08008000f00e00c055138008548018140008400102d00303107d840600411040c03009a440d041881d21800c1c940da0640e100240d4244040d29805880c01a18000031521085c20000684d5958 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 665407769 1250 665406519 665406529
    0x31209100c051222080106140d020a030501020a0210060f08191e03090914240a0503071205060f07021c171014030a021503040f060203250c20 62
    0x300150303d40b03408041841042c070042807601070528030300c1c0070004d01c0255031080c2d0582201c80f14024800c80001010002342035041950103800e00c0c5101801201195035640c0301c103401ca800c00b046c01c10050304120b024009404080c012500074000c40390141c49064074015241da598111a42c96124510200c1710b00d030240210240c020442d0b00b07210302c920802440c03e18008181c0300302030184041d510700d0104603015080d1030070040b038455031508042a01000b0708442c455a0807056400080c1e000d02060400326203500c044c40394100a00780d081c10791401031241d1601c41d003030400003012107424040c503501304504241d00003035242202c03009940da108030100d034420071901d114072a003c3d90030309441d200a0007000340c1c0009082c001c84840301044515500c030101095141c0c6184540a54484284002c281005894900458216100340c90007241240e0656a0700181c0c0c1003218030035003010200344141d0310b20b007544901005500c1c00c0d142c00f49403ea5103903919030300d05590b400260300d00103a10f0001d21942d151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 665409019 1250 665407769 665407783
    0x30506190810230a0903080708070801140607151b08100b0d0b093402060c0a17010306020c280b07050405030102070b0114031c18030807050309031209100c05 69
    0x16064402c0d8083c03070140744613005040c0481c0210000b81041002410782c41c854194540107850710350b100015a440c10002c15403860543e2110756100f030b0100310040010f000715005001c03c160f175501c042402e02c90801c1c0340e24480c001000c8803040c454503204000c1c0c01e4159451040c242c511171241e0a40f40cae0341e022a5100145144d42c0e10f11380040340f481c18021000200a200401902c20203101c1110b00390742c7c0409c00c0001d02056654001d640614007080b110200e240c05003041480b24a02441006010f0384100f0000c0e1081e803044d1a040d5001406180f02041808843d20a140150040c0c00407400b03040316200180e0107000c0500321007842c901240600e40b01c2d0b81220002c113030060003951078001a080020000100b031140c03c04140c07450507038003003074103002ca030f40710b1008031107100080c0150316140166600e01503442c403110001040c220101c0055120400b8200080c0104011601e8040e407809161500c003214591001200c0d0030300034480150b4801f0201c40c2c0340d44062074110f2941100f03150551500d01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 665410269 1250 665409019 665409071
    0x120c01060e070c020a050406051c110306040804060206070e0f0409020301090501110409060f0311012d05030a0b01030e120705160801091a060d2907030506190810 71
    0x72060007400038042c3d01043e4080b040f8000c903005095a50f491042100b11001d500c115500620030600740100711102e100c0c105907050158200071000522900041c0c14600304640450700490041010300c5039950412506610003e24204454050f1060000480c152810485103124944801c64201152820741042c1203540d800802403004410305981541350b500103004004100c0e00d40040000ca601030503072000100c9400a411071440c40c902001180d42000c0f03c24986640140707081d00383d80c008905070300380700c403212941e50325622800c14426403015260300b0394116040608080701000d540c0d41c0401e415a208807607540b000ea031002c03546409403d0076101d00c1b030f4082d00102880300040040040d00070310030031403187c02803d41c140340c501c3c00d40003080400c1d034055400c07804110080d0000780c0000c00117111549108842e0410200707400d059211120101d5100000a880c0c4052000300e04000f400700004a0013004110758240c03c1c08051a40c41d80350f84440307203800e83c44010034a4200442848642400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 665411519 1250 665410269 665410289
    0xa120510060f0801180b070e060c030f070201120507080a3902010e152a03160807230f04030203030c01020903241501020111040306050f0a0e120c0106 66
    0x20b542c9590a00d001c1990344103400c829401c1c800384135002c4030349a0f40d200d00300382e00c04815a03154440c2901100c40281201240381c00660800094074080c2d0100042c2c01d404090140041ea50b845070700c0010004407680b0601042c040c142000d1004043e041140c060b80540c00781c200191403e50780159034011400f15094001040d051250076801c100404405902440c40c0c0d00244040040c4d1114255996126011078860407032030303000b00c0c030030802e0340d107400800554980b241601043d40d400c0401d0141c1c000d40380044c13980240e8040d00b560301d820230012a4000c03c1814182545980c40f00711911181485e283c410000500080707011441a111003030f40d01450700039080340e455082c0200c03120b00075485050ba280c800e2189801504145010801003030206800024041040e19003004c89142c4110740940107056540320740c13488583e640108003500003503000b004081030904050310040242c14010342118181414460703440a43e0704000f0310070305400300c60f00d4100e5903045075402490040109030002c500320 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 665412769 1250 665411519 665411531
    0x141302190602060a0e070602100209180f04110a0803090118030b040b0a06050904020d030c030c080c03091806090105011107080a08030f070309020306060607020117040b04120507020a120510 83
    0xd940e00007000c5100b000c030b88004000072a001c0085c640d44044a01c04d140040e4071050b06080c1703849054019058180025140c0000b003914034900a90250b021258505904100401c010030302c0100007110794115403d44074034080c2800d0540e416280d100e505d407403070706010035281080c1203039041c030f840c050003140c015580000074203203880d1940130301500f91014042c41e800c0440200c0d440c5810a14140100d07401000e4140608080e64180d4039156110415001c1c40511900d00010840860040c503c441e050700140d96140c642c03004102d072007400b803408600c5000941003002290b80300c140c0d140b410745100f4202021110316059045151024a070044802c600912001104010f07060300554081d0b00d80c155000c03401c3e60340038070403400c8508051000c3e41c558840d03c00709455043c400010040c644c0180b41c80c10f4410034041002010107400c1c1c2e8121030040e12002040144085460307154078030341d8117240c41840e0503140d40000d1443d00440c003070545402e030307a44050300c1004030402013400e680d0b50204081c006 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 665414019 1250 665412769 665412779
    0x62a030c02010906080c1209010e060c13081603020d081908011401050a2003160c0302011815140d1b020f012a050403171c14130219 58
    0x4089900d40882c04105507400114400e401581d44510030301c2101e98107402c04c9a8030315400c0d10003402400300c0d200b5550701c1603400d0000ba001d00a05106400c01119283e03108a003c03120003603c031495205541d160000002d14031010300d001018405c0340e804843c0341c404a003540c2026541c6105a1003030b0b5803103c0d4002c0190000300d4025584038100c40080c10301d640400300710700c015612803244040800008480d00f01c0b003004843c030f480e24695100c861208070fa007071403400a50030b1401c0b40c0c05c0f8016038080680300400c10856910522801c10041c0d8583c2c85240549054030066441c41040e0110040c40700c00300d031104480c05080d0a035a5098045941404401c004c000e2400c803055081202000502441c0c8142204034014081c0701c1c000080903c400b0306080d00b03240080c44208814007400c080107410000007003c01e031043c400354030444610441685d5a8003601c0c95920000042c8030500060342016106034892250102c82a0702c485d0302440f0000b000f005200181803c814002e01000d02940d2030740c0032034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 665415269 1250 665414019 665414027
    0x4050d110f0306040b060f09090d032004080708070906060c0f050c0603040f03120510060e120601080304090509011a090601031d0a110d02030c1c0501060b09130506010801062a03 78
    0x17010b88010340d001f0014512540901901d1401101e0006195102e4038002c2c03c954445c2e4450100b408039821541c0703007295850301c107400690055110b065268410760f400c2c840400140b1402004044049040010918240c2e001d01864800440a044c0029030880082805401e1200503945074004111564030320f01072900800341c84605005030009601614070000341d81302032203030b54090003d441c0b450607da440c00d01e00310f951292400c3c0641c5c0004c0314500c0620122000c206280c0030300701c500301950700e4a0a0806203011540000c2003146241e050030340300c0502000c001500000c90000b56400d020680e10200140c000d04009000440c5c10038103804c0440c590000442c42d411224400c00c4011045004c1504200750719000c0b040195240e0070540c504840d03480c04028801c03400c02039181c5940f5000007034071000d00311a01d50344030f150018400500382c00249030100d0740e044500c8a5030410046810b041d80004e0a0100502404040c080914142c0750200950141240c03ca56a10707e86080740c10300f460014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 665416519 1250 665415269 665415271
    0x190f12030e090f011703040504050c0408060705090916180303081512060c09181e0a020a0e01140f0f0d050f07050f031801091208090304050d110f0306040b 68
    0x1400144400104050310b1800070141c50180c4a12091000583d00b00b101c030042d240303051420f13180b50744003c200005641d1118040c26125046e1004400d4540707151448040c1001c000034101002c2281c104000800c99540180d40d03600301c40445510360640c0442c800540b881e1307034411400f06240c41580e00c00010554030092603427041352a026244049800e034000e10960854015145070f0940209000a290b40a86006051484402400c0c440000014602150000401e80303684e19101880449589101c0480d40000e800889040c800c51410524a02c0207000d25111751803141042050400c0c05400b06a840540c1c400201242105540d1412581e03050b8181e40034000c01116942801d00041c8500203028445201d800c803519000d01c0e10041082c030000c964002095107030192a100c8480c10520002d110780200070340302d04440c801c6800000d0020b015604002c0010540e544200002c2c0815110035050102455100d10003080910074103000a5070103290916803901442090204014040484001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 665417769 1250 665416519 665416523
    0xe04152705010c050408190f1506050109060503090307060c2303090c01050c1009061b0c020316060c0f21020a060f0603030e010503060f03010f0207060b0d11190f12 72
    0x30420020f190f50f007034034140501d100b04e580942281c240f0843e01c1c1100b0f84245210345c400c1d541882180d90640c2c5800d603090010207444111039603403400b80b001f544c00c114882c1c003a03c0c060421034258036009400540e03920491030002c00846d100e54404c200540904804403010f41e200301c80c003010345126400603c0f142c204540916440c8680150700480354066011502d050551310050400e00d070303804084001411040404032a080d503a00200200303004003580256107002a55100c0042d0b51050041526040004240c0651000c1c5078000304075281e04080d0400d00140e0141800c0703130520050914500e0840c003142e018540c1e144803524440e109034042498100c2d681b2445c8100844c400b09100b680031103100d03010080101d4511503c002a41d03000b0009160310a02c000c005400d2008081302007401d503040448002105500440d42108000890141003000c0c0e07804e4503000c0c809034182c0c44a001c420280c51400f406100145000000c81c1c80c000d61ba40d000d840030b0308841c0182a642d0514411255540c402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 665419019 1250 665417769 665417771
    0x12010e01051516170702031c020a230d0e401b0801030c08030304080d02030a0e101e0209090c090a0f0608040b07030b09041b0306180506010506040e0415270501 70
    0x80c0e48030030304880d0099416230000d940140300c4400c555907000c101d4940200404072003c07001403140c0306c1e21070400688102080ea40d40303a51183d03005a00381f00c032030130414489004004004a05225003c94941a059140c11070224980c0300962804080003c0550545c3c1c00a4040c0d1640380d10500c41d00095094120391080d6540002255503444058aa020595005100c1c0d0f030b0070010250406801c1e0061900009520380c0090066408444185819840301414a016445407004406c0b030ba0580a82d16031a60000e174158600480103000800c0306a00a1126140c0c02c00400e03c90003075195682c00d000a0184c24003010811a04d420b03000d000200221400c48c0c100f4040c000040c1c0c0c040c428022101c041030b015080c1e510580300d0381e4a055140c00005d00c01500e1803d068400004101d183c094a1071240510f188a40300d00318908180e42401d105822032405840100010401060100003080d0b1264000751010401504a0800c9003c0d0913a0964000d00505000725131074040b000503900c11486100f880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 665420269 1250 665419019 665419033
    0xe0906131104021b0a031704050d26040b070e10080103021314070305011406180111010e0d0e030c0415090905010f060b0909010f06210e0a0812010e0105151617070203 73
    0x300c15080894115002003242e004041100c881c070740900241d40d07510001051007101c03c070030840291230083c1c045330159030304030010052082c0340e60810880805981c0603603400c00c2d40c0d0400400505002c3e010b10000340504411034038031131000415407024a40300b80030750b0565103500b40341c50018081c0c4420301407074003120300842c1e00348024940441107a00780700ca42c0c20080030519880c00151060707001484900d0a0307540300c1c40c2242c00c41009003c194405034507600c40010400210060501d040c0e000e25070140581e140c2410482d10b15850103100f0103c50140e200455491403e01d4403601600d0902c0310804582d062030004144d100d451406403000017802c3d10180314503a81c0d2002c004200c5803921482012950350604150500701e451440b2750b0040052401107000038101a00ca03242800145007910007440c045a04100b5043c142c2c01e0a0040c104403080580039410903002880b00400c3d038a243c100e90600290320010750945401c82a40f45400540400342c203001000800311030740c00074004030b2103402128 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 665421519 1250 665420269 665420297
    0x40609060305190c021c02010e07051525150b01080609070f031512030e030d020610060c060b03060a1b0c050a021014030a060e0906131104021b0a03 65
    0x201c00d00340300340d0894490f4011903954401203030003400356208030703811805070000d00404001e071070b108200245815800082ca205e0300500c06404e0100c00d8120fa8401c200d40b0500c60820035266081d03805500ea0308070b00e040c40360000d07070140320141e421400003404406421002201e0404a40c05004100000e07200c80d01d803945ca06041210702d400c2100c0c541b000c52040c204d103800b920f11907800040c140034103800c179018540d00c9400070020900002c00c01c5000440c981d040f144541428400e594100751240000c06407818102034040707006001c3c1c05240104691307203540c01c041c4807040d0820051040c019040e00c1403402c04958180241a4a232134541c4080070703103030b02140814442ea4400d8400c0c0e4200d0054006648181c0c20000b0f405662105142080340813404481016400c0b0000c40c05072094043c0022404c0c07501c3c10003250010700a000c0c0409421210400803200008000c000c5c072130381d0104506840030f00321000200207000310040e90400304252040301140140000e5030946c8a80a85c40b59015284c01d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 665422769 1250 665421519 665421521
    0xe04030f030c180b0a0309022e0203040305120d1d0c0103110f030a0908040302100206070e0103090209190225150b01090902090f040c0513140d1401020702030a03050406090603 77
    0x110f03004880c04038824108100e0000c0c0807003d030503103000724030b0003203500c004d80e8002528007032045404c0884a104e400c8255100215008022183e65a90000d14142860354681079102c60609100c0a4030b0b07030000854486c01c075410380c0003444a080080043c20340401200b103032036484400340d9001d80401e15100440111107032400c10703100c400010303440092640e91100008005031198400c110380040d0203000220042e03031081c1d0440881c0d00b140d0b0003400d00d441d01000041001035000d0820b41032501d401e501c40b02684400900740d03445481039084080308c140000c0c1801c024400d101130400001c018144883e850f0084286040495004114802c6120b0a20b1504070031143c40d8200680440c041a50810400c48290098060803800610341e83c0b0401d03c2a000c1426500d00040d04000034800090000702d031851014008042e00800a10040d2641e10001103030410b1016034016050142d0100c50b00003014094040b0b40c0013a6020702075170440081450003030700541090040d070011901440003c00c21601c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 665424019 1250 665422769 665422787
    0x7020c01090b0427200307030f0911060a020a1b0e09030301050a290706060503190510021e040603021b0c01050d0506010c02121b09060a060e03070e04030f030c 70
    0x4030354400c0c030b448807840e110b10228100c211403103050780e0b00c801d03041505240d490300c04206003420051040c1d403454407d60040071210005a4401c4103441c00302d0100204901e400400038804044d02d4031540d03503002640a80c5030540c80c02009003104a441401c00510240034080c004681c3d800080d0030b00c607100c1422840e2a80424081c00d07800c004544001c006444460203104120040e1800a04c0a5a44401d00c41d5155018900035160380c0e459000401c07036400d04101241d240c10348885a59014241d96440944030000d021151420076004034545146068030014402112a80c1c081140d40329902c0c880500a50002c482040700d0404001c0c46801c128000b09408030745c100140d461628100252507404014035001c3c10741030400495088650060704c0e01d0030501e1b021000900181030304030601500304465144600b00b24001e424032000e010068032040200c0003035034040d007440003018200303001081c42c01903160700100c0e03500c0b5600b09000505402600b0111300c0102da58041c4014050b4080684095035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 665425269 1250 665424019 665424029
    0x6021e0c15040f240c03020a111507140d06080d110f06010e07030b030d020a110103020a14160f060605010e090601050703120b04060f091505030601171507020c01090b04 74
    0x50402a0310009106048225207182d0481340320490b07144546650382160055400e04000c00e500040801c00560001000082e0b0030b0315800074039200340031425410910401410500c00d112180c40b00f01e0441c030f80107003a0303020f40048010421155903107240c0c455440c280b8540360004505994850315501e1404100005c01c1d1100b03c005003016460540300c1c2034030134001009a020199900a030640a40d01400640d00f188050f034010300881c449400c100702c083c40c2c42e0343d811341410f204000030948103030008410209807080c03aaa042c0c85946a42e51000000004c440c001c1500800700d004070108000b07a88100103a54081c0d0b1494039680b078002c02d03c4210030040c3d0b501404203906004240c000ba03c150040c089a0340403c0003c60010031110100c1c00751075590700003407140d20600b103041c030542c0914840d003280c1a07520f40500a034580707070501103621544180101306407081c00d42d00c9800138440412103040d03071900e5031800c01a03078a40600000e444000896003180003c009980001c0ca14441030b0540d410f480b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 665426519 1250 665425269 665425283
    0xa0504080406050703030605041b0f09081e0c03073b06040903090b0307200120070602040e18010b0411180f03030403111f0905040906021e0c1504 64
    0x82d080c103406890a4029080403010182ca40802041c540c0b554005c1c40c0e0340e941c1e01c2060942007d400c10340540101c020f00e026404203c151102040807603800980d100626102c44104403108000748100390520001580c0700e0b03010301c1041c400240f01115130303551200072603081c03514100c603105d4888d01d45060880400501c007041c0c0f444010615503d46544000701d00382c8a400c00c0075005584040003103082d001241d9884c0819451180711714801a00100d401a40c400312000b0040314141060100600022480100c110036000c107110003000401c1e8100e40107804400440386603464024400700c0a400e803c01203160395400c3c24240b40d0305041c60300641490f01807015885041900040080345118600e8012aa005e8400c86210324070351010b1008001850055102c0302ca500036801c02e02005114900100320b141c400410718000f126440f0024600b0749900300e402040d402d103d801c0410103409801c80e61503601d8040720396020f888210b50020306500e14a90140c980c50500d0800450815004a40146c059 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 665427769 1250 665426519 665426527
    0x3010501023a1101060e010e2a0c010b010e030316060e0703171e0f07171b0a03020714090103060f0e1009030813050c0f12010903020102120a050408 65
    0x4a01038405110018444490b42264140030035950081c0401080404010510b481d8604840c0d0300280070325409041000960000c951426602c0049034000403c3c2e15804c441e00800321700c0121003d03150103c01156400811f40b9009401e52040c02071100b00c820034027241c031504400707060b420040b00b07803030711006c058200359240038081d1980390103811403003c10744076401103440100000b50300680005071000c240c0c0c80551281c5807107051100000400d609440c42100500c000041d110b9040101c03a44154092611030004240c0780030200240102c1d1662400e54803288207a8803440380c00552101c500f0b010381e00300c40a00d03650b01d1284500c5210114002e401c02c07083c0d401800403407075640003450040c982190005003104500145401c1242001d10040da1540302d0428105040d480350b966a0092506500350400700318950301d2950b2021000e0030140221a080c149001c0c50380c0d05202007070180b80d290000d0064107000d280080c000c3d13009001a04000542101041030450940b0491348503d501460b150b01e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 665429019 1250 665427769 665427793
    0x3041e0b0915130b0c060105030f0a030c0302120d020d0b151b07030813030b090102031905060307180606020f0a050d050d0e1204090f0b031b0109090e160b0301050102 73
    0x4860080900c07280a078400c0143d00b0702c0360380d22264030000b0402d078600c0544a80b540005907080c40c0301a804648071341d0128442041c200404101107101e542e15041c9062104168a0140c1c00e2564500821504150208800c04280f078560024103003c111300c84100129203448042000400380d102408030083c0c130601058194150202c145200d4032511000c641c409941c0e80d6500941e1343c840d01c82840254020f08003003040041011a80c5e030403040c00c900070350641c03504102d001e4420080031024085151124003040c4035480521250340607007510350640028116854001010708400e110b8400144140c50790250b0040c40032500b482001c2d405409071580c3d07051081c084545801168015503942e40d100c8040b01180781c1000000000b15682c00c20b00d841d549090040d000320f410280000740058200203ea41d0543d0b004203555090340480e04203078448240c5800126100c140c80d4000c03043d228684a50f181ea130030f0001401080300100c1c840d29003c0c242c0c840b840000140000c0c481d03240581d101d0070341800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 665430269 1250 665429019 665429029
    0x200303190b031213140108040609020d020405071808030f03011707093615240321090305100c031113090506180604020c070f0803041e0b09 61
    0x1086000301040c071005650000303007400c15107007403456201400a4120340041c08401c04ca4020000146510341c0c0f8407240340083d024880042004141d503540b0720110045580f01000c2400d05500a1700c2044507280007840980089407807903030030182c003900b02000204d80c440000ac0302d0050790070707002075401c2d039182081c415042d400c1c00d1020003160044020110381e2540c43d02c80d100707015030030703110280f43c02142c3c48034a81a180c03400200d0610000300b98455010424079601600d09500c2510005007003254410b031400c81c0526000c070013860314000f02000041c03080c0700e4080c1109000c148000c5180000000059510025034400140203800400f05940191002d03070294088050505011444502000040340a0b5216100340d502c000580182840041680d2160a500c05400e5910701a10b4450006490100d035009003014400c6070001648112988184021401800d07030202000c03071030351100e0440e51250001d004851941c29244800e15008002419a50803580c440785803e1800b800c01c01441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 665431519 1250 665430269 665430301
    0x12706020903010b1203040e0c04060c0f0201030b06070b010302040e0604020d0609051006030501240b04030230070303020f0321100b040609050103231810050c0a200303 74
    0x90b525560b603050742541621085140042d02c003034031014554684c24009958402140502038418600c0705200c10b11100b5000a8544585a006490310680d500b4503c0100c02070441c5880c07154012001180c1e00c0704010b80b010320b0a0503a4401c980900c03d80300007044440d601d0300110782c06540b05604d00440c0e40442c0850344186000350082c0700f43d628503000500c01e4000d548040e841100c1c0c5030754901804100c041c03081800140b482c2142c1501c1b16040c50602d201119004902020b8825407491245550001c5040c1d1100c0585514081200b00700c02c0c12109540c0b5200c00e440158058040d001911040711004411611450266504821503200c80c101e024410000240071640284c040c81002c100f100940340600020300003550390484c401d08100005041d01ca0360405603100303094138240d080c0100c4100240640c02801200404c5d0320314080641c036132a10f5010040708400d140340500b402564011800102550000380d120350706000c00f190488e100b03049c003030001440540c20520104110585a00c2e000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 665432769 1250 665431519 665431537
    0xf0a0204050d0c03060509120f09041b0801031a010b0301030b06040e060a1d0307080f0a090902370207170c090f09011b0f1209050a0c0801270602 64
    0x141060348038404580303911200b02c0140c400c107500c03090402c1000500e0250544c03020342d01014203420801354002c9560b0b80107410f81e140b1194404500500e10391510703800003c1d00c84040000c001b025041000c0a01542802c1c0000e42d40c904545401141400d170f8502d41e0b5040301c40b90035041e481d503882c60300c0304048070101810722640103071200c0d010442800f0030090140900610600052140071118418000864020f003204194005000c0d24000c0f80103001521500700b6040c20165640c400034504488254142c1c020200061010800070002c038072050803a50070803071000b0700d42c40c038004030034854504a0881500d040140e122110034404144586101d8604c40c1c6044200c59400502c03c2c001100c2d02d00c125910081000c60b07404029002100b4003600d02c0c500851907240000c103e00340ca0092407800300c00b0009041c41180c484024080e080355000011454000059480c00c00340c40c41c205100590522603207841350f0030060010501e8034114152040170b80ea00c3c201d0318001d0210354522020350418101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 665434019 1250 665432769 665432771
    0xa03030f05091302070506013b060a03050717070b0c0a03120e0102070809040f02040e0f04170d0f0f0e03180d050f24270705060408030706140403080f0a 67
    0x84020089130002c0c0000031b1044000d01415814a20800c0c0070203002d03d20380001d00008202184580c84880040b80d01c55078016000078143d0b9500040358405110f548003c00610814000183c00078521080e0111001c000342598103c680d07440e460400e0740550801d1034016003100b06030b00d00190240910052500b0b64010100340419244c101d03d0032600420820341d400000016001014a002d1043d40e910810f01241182024240200680841002003824070380030000804101404692005062904140040690780c1c00741d220440c8043d200c09403080e452107041001582c0d4460690060010018010300210705050340500c02e02e81d0102d4603020150015900258180070503030a008a41003800e94000518000001e0811200c024812010300403103400f646080c051442d040200e031156484030f0b0b8420352010f0030341084050611203c0d600507980308000207400100b034130300440503242c05070141208000070351349000e00541070390089a0080c00507a01c10001030000c651846125005010910 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 665435269 1250 665434019 665434039
    0xf01050c28020a241d070b0c0f0d03060602150f071d03070602060f090606060304020f3706081902070f240c020f4204110a03030f0509 59
    0x2100c5143c0c058400c0e8640c0021030000c8100071349000c50040103103420003a4a01305d480c1040c940c10341c0e1510110f008413002d00d01c00080e4440012820400342c43c0f651007510580c0c1907a40d415a014006004501c203a80c00740c0900c3c07901000c000902002c50b48259004900c1d061075640f03400040316424803c50005030480f181500405041d00c082041600cd080c0c150018500d90424180254001c4402490a03d0a9001000b048460b80300c910640b90015410340d0a2591400fa1500140704034804440d440071102e0840c2290001d1407110350b124103084841554800410303128601101c600400300c0310742e141118080c411503507411140c0c8c01010601c0c000c225042c004c84080c3e031850507860501c9401c01e1b0030280036507001e5050740c42c0e11a100070b500c401c0c0020b10807208031103903c60315100c4d101010300002c00040c0e03035501d045480e40d0101400c41f8241c650001c43da07441610300080792400391010754100900d40d900c68280d0a1802c2e031038080d25016291062480d50b0620200c9055200ca5206608203490709 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 665436519 1250 665435269 665435273
    0x50c100207090911041503051203070c060e01050708071106130507030b0109051005011e0809010b04090308041e081912180302060603030306011b020607050f0f01050c28020a 76
    0x449403c150318454040321101200e900100f1060f01c1c05002e0b60f01d080e8800050800026400190344016060750100c90341e1241e481180544551140b9503014107d14100510003c4069040d44240c0c41421541c540c0d5566880f000401c50344c0e4480b4000400c030a5100c1808038604c0004144d20042061003081120481a204d984161400c00300380e104406040c0c0707420034008150b00441c00e07140503081c00c1c640000500b240c1c14144180148070071400e414030183d2004603070701d008290400315005001900900035240705243c014903c04013181e0a03580c0c5007161200308680d50f00c007001aa28036400504680c00d1203107054007401d24010749002441408003a501c1032008404d94020202c1c14660445468501071941c24043d0030504010001c034441e4008004200050f03800c40c42c0a4240190005c410303549907800d1003c07540030300c90900060800d115040019a44100019407a40d10b413401c46c0c0203024940703406009228502030000a20000100c400c0062050b07404c09031084403d4010b4411104000015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 665437769 1250 665436519 665436521
    0xb01082413022217160e190c0917070303020a02101b0b010509100b18040b030102030c03012301080609090a020d14012007021005070834050c10020709 66
    0x180b4007526441c0c0c0341000b00920000030081c505110512009018241d001704141d41e0026924068a00b40140440c08030301228088447c148410202c1c400400200303e800700090490340b00391080c20880d07888000c8105040314045007200841e076240d001030801600503400c000c040204581c140003004a082100341e034980201082c4207401c0d001d4600d0703041ea54104801d1108150b0010080c403428100d41d0710411405441808803078512142100030346240301c0c00130004001c1c0411059060345580040305104880c04034000039812a200f5000d00e0720405403098185180d1041544071601282d038003c0003a0b0786081805c162a8000c0248040d0342444445030b0000708140940102074440b9901c40e640f03040c10030300034031490342d0421030044500c0702000c1000e1500140d10a00070300034007031100e043c014010311b03000b00c0548403050390000c9041c2e00c0d1140c0411103030011482d06022000010811800070801d07140c030701915903468214000c0c0100e850740c101448682082610004210f00c41c40c44005036020380c2e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 665439019 1250 665437769 665437807
    0x3050708070c051305070806060901111006170a0507030240050702070503060117011e0b010207051e0f0616031e02060f0a050718090b0108241302 64
    0xb20b10b1100d07010714100700c10702c88013040e00e4402600c01c0f8900380078000103a410900c0c043d8402c074101d034869070310000007004032030200380c008440c0040c1c403076903410300e0303c5000c241c0010b8161110050544a04141c05290540e6000c9010014141350045101800581000300c200100c0c60494002108046143c28403608900308507843c10300c50040100c01c9092100c41070040d9504003600e403005020140c14180000c0c2c0703c0d0410f2040c4a800001000d803e445100290001d000100c48640281e00e0f21032101d1f0a00d0140050307080d0305006014142010540c0d1900c00d150300c501039100500c040300440340d5001d110f040c3c00f91504141e80640e05010713005905008a050b06051031003a6030f155521300d078501526080c0440924000d0a40d0010b2042010700328404038055803104007034402080544a0140c156108042e40e22898100d8003001c8000c916800705401c061020b2100780e88060095440041d543c0644a0024406070b0018401c41c3c500f220b481c0c00024018003141c0c0c010700514003011481080204a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 665440269 1250 665439019 665439023
    0x5040b2e09020a0e030304080c011b061b0311030f0a1a0306280203090d0516120f020c01030501050f0d0507120c1802070b0121050106290906030708040305070807 71
    0x9000924407501d01c0e40001380c80700061054005504060400b1001e545601070442540c2c10010b1841c0036076030704180300a034998542e8010740200140350104000f01c1d000d089581e0700320042801c251301d409a51158070102c80c45421003400c4980309495040e1480e001e084148a140d08080c0024928011036405114081c0100c5d00004018050790780076814210b0344120140082c2307a5441030042290201c4042080e075005a62454906d80e10000d41c1290a44402100b002030726664050046901e11500060729840c1c1c00d00b203808460230060441c00450503500d09000c4d6540280f03c86100d8026410550440c482003441101030303408541d10b48402c0404540307482000d407504c0b103c4910400148501c0000d040143c529a030081d81303000743c2c03174558415001e0184601108151310300710b500303001041140c0844100381d00000038012990740d41001c500070710103107041b0f0101050141c0b00c1e0514964040c02c4500e00f12003c0c001178215518031100396001d4400402c2a001c1c04000c100d09000a0074000050024038 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 665441519 1250 665440269 665440271
    0x5071502030c0708011a0a050907140f0403030c02040b04150b0309120f04051f05160206091201050604110c07210c08030c0601171b01020c04020a110f0105040b2e09 72
    0x110740d010001c18076406406c0043d0103030969100c280070544943c95025448515820b05156000000e100d001c01340c404d00c0000d503d142030100b8040b00b015400700000030000c0c000ca0741030001c1c07c418030411045072441c8a0352181e21003181c41c100015074942c000345500c8800c6206581e00c05420603820b000301e500410031003000000005003801145450301562003408090345800a01811800f80a07141d8441d020128003002c914990607011561100200e80008102601c801e031408040c040140c0030f0901076800903c260f040c0315030340c10380344000700545003480307860401040018a004a0004526005280b0980b0b50a000300941c0106000b081c9050080c030410380210b55a5007004849800c0c941c042e00300943c0300c5484a0900310340c403000075040003200140b0350180c50009032000142e240400034046942c100f4004240a50416004030350313065203242d1141680c1c9103140c501025805c07035504550080c60130301d45ea0041110080c0c03542040d02c02e0024030102e10414905150581003550751544514802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 665442769 1250 665441519 665441531
    0x30302160e061c08090a17060f0c09010809150c0a080c0901170702010b0919110918041509081b0c060a1d10050702011403010305071502030c070801 65
    0x3030030080c5100000c0440441c0d20803642400e00c00900c8003858842e202c0b00ca400100340d481d0500040c0700032541c40c400d00401c81c42ca05990740800d8103090701d5034a1031803940d00502c40000d00d10b00c401041c01d0f12924000c644980b5080c0041c006585d2504050000d81480c421440c40300000340c0042d40d054060400d420032640c460301c1201b070081000303074014000c15681d241445094000d90700480781410440c00104da00a456441c140300301d00611100e480395900c410840c05210141080c0c440c855101101c140040c04020060300382c81e802e074031a1b8000c498001c030442e8400049660700c84840c641042c0700d04419500150054101c4094600c00c84040c1c4d00e1003c009441c0340a00c4140c5510200440780714050201003a00900050f0180244000d030400d0150781c102c021303441001d200e00000010002440301c0003c010443d4000c2140d040440205d010070f08604032407a00c00380000950741201d034000c00078411701d820284010386035005088040158802404650401202807083c600030303210100000500c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 665444019 1250 665442769 665442793
    0x30209010e1006541409040803060402070c170c010e011b08250605151c12031103070314070c0c090c05040e0403020a0201090b090d11060c0106030302 66
    0x419000d40e4451000c0c00841c0404242c2d20304c8a0010040d04e507400c542c5120314030003150b40d4180c00d00c44a42c100c104d040041080d51518814001204181c0300c003017803c11110513000c0280503445038140c8020308900020f00020300d0514281d00285040c501c101c07103903003a00c0e541c0c40c0340310038a12524441e1031080d04038010251070755a010074100000242444d00312640d099040300005a1800c500d03000d00b403c1400501c504a00c1d0903c41c0da140510132804011030030780301908114000740815100100c4c0307950f46511540091a09461320340441207180401070b610141c55032050503060ad0485040c0c10705456052071403841d005403001d03510645d026280411b00095424113501380340340052251060106101803140400c080005190903a008003c00142241c2000e000740c410740140e510813034001c58900c040100b010b034081010880c040c400e803a07582203192070710b20102c41c1740905021540c100e104407040c000410414008143c44040c0030300b1262400c084800350310309541c0c4503003064016900072009000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 665445269 1250 665444019 665444041
    0x20d0f150e060a051603090c1a0705101b1101180b0601030f111b120403080c1b18070c06020a0c0b0c0a020a0b04060e0d0816110316050106030209010e 66
    0xf41c88204000100071a143c0b0f45046600381da282484001019910140780e0104106000003170054003401401800309045e18030410150781c010041140c40b030088000c0045c2d1050107000307400ea40782c0e00780c000c070040303216100003102c8020b1b980441c1c100564a0b803070000c0071502e190102180840c020200910b482c507003140050166100c0c1032210b00d04501d4094071840140303900c029545600d4410300340003106610342080d01d15101c5a07040004900100060001c1040000380c0108010f81c2c12009891041004174005100e2100c0202000d802c03046000544901c2d10000c0803c5900c0b00c090b050500b02a01e5a8840400700d070050301003000402c440c417215605204000394003c0d407060f0040d003075526200000200a440b80301d600c80041025242001090800030300350041450703d1000ba007141d10b0b195405030000d05541080e45c050b41340f2401c004040c04403a111314080e00001c11a400110700d48128210300513641f458001d4142c070300f03541c0d0b0000800103030b40c3c0f544002c1c021300d11800120003130704100f11200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 665446519 1250 665445269 665445271
    0x70606031a060a0b0c010b0402030a0207020108100e0106081312020609010b0913030807050c2407050310050108060a0b04180e0303070c020d0f02041803030608010b0d020d0f150e06 79
    0x2101c60156080080c01e9803050341010980c0c00c002c640395241d000040300c440c050020807030783c25403150001c020030654000a07409441001d000b60b85880c0d6940f50b44900d01e61380c0009006400014289070010b00c185800380e5081c0390081841109400350750b0668031004080c80c050104100182c000074140b201d901824081d034028200220340780c40c07140c10040913980094490240041c284a01040010025809003055611540050050f03a150300b01e07010309080d180ca501005509d50401650200f0030261042c030907284241d1704842141041c6041600544044c04002c0155500501c100d502255950380c4001810051808901d4644040c900e80715035420343e40958520381541c0c0c805e01c10010280e601c980303510600303501500c42c85000340503030a00407100720b41080041d40207414071010314420602e800c8a030a0f024001d56080240c1521f0707a040c1404d85180d003045640c44524025404054a400c5010200d40e178803400d4070031552549030384e44032880b03803030301440d145100e60b2000c10034860070301030101b2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 665447769 1250 665446519 665446553
    0x7060c1707030e160b04120218010b030613020a0203091917010204050f060903070e1b031815092104170706140403020105040902090a0504020f0721020d0c03030605040207060603 78
    0x11006600300080322409000341c0c811a08038401f8a6102402d41d21071040210400da00b2a020080342d41c1c590000050741d074002e440c61405075a00c0529103443c40024800d5030740c10740f03013540914500f044000800001501134403d18021000381708001403001c82c0c80d1062020300140900268445140408201c1051028902c460241c3c008208440c0c032940c0102c0c665042ea01d0b400b1f2442c24580340c0549c1c451480c045100a5100c81c0c4c0e0010034490010300e44600000406c580404840441c41c0c6c0038045601b2040c20741d240c0002d507010f100701c007861309103103000c0b030b0f0340c0f5140703070301000d050a42c1e030a103098400500517030b00d0406030000345041c041e1a510100001103141608035080c030f050700d1540000c049208511844045550110740201a075980d412030170010400200290345403045d6820b003000546c04490102d0b16002c40e1500e650140d030717a14200010308021074000d40030070b0103840000e8420b0480158210101580c6803000b10305a80c0e54809810312078010200014039504601d01901808106284 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 665449019 1250 665447769 665447803
    0x60b090a0c1b0218131505010509072a050307020d0609051509030901080915042a030b040623010b0310320303040f09020c0d0f0507060c1707030e 64
    0x2c4050b8888a041003000344c00340c01a030907259034501071030040c244402001085180c0b1100c00000404450b040f850686d41d04030740c004e0319038480a038140d65806140c0c40c075481c11084241c0354160a0502e20709a521140140180c2c0e141c040340382d00150001420703980032500c0c0e41e1740d0b40083d010300c9010800314040c0d0314400c0c400c0e0b8440c206a04890b640e170003903501042c1085400c1000440c0003506109182580c00500c45504203424149028803820003407150207925281071402c030355458090450b18008403070b0030141012007525151200340150440355075854071021109003003a040d21a00b8145802800030040854407418547d296000e00f1141e588800e07807520140c0358103840184500c8680c9150340140f00908440c2c1c4000c00820304602540c1e00445100590040000745021150024007182049a042c2e441c0c9002d15030f07058030b01901140101000500a0282c0d5000406560001d0015103031804c0200e030350004600300d1003180c40e04075040c1c40043c3d01c5210350348580e071003089140650b072600c801e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 665450269 1250 665449019 665449067
    0xc0222060b12160e1903060507210b0f040504080f1305010807030204230301061502070f06030912141606090201030b0406082a03060c0406020c010206040b0112060b090a0c 75
    0x90f0090070990700b840124401d171854020440542c0c6003440000007954003001c144281d1914120243c84606d50442c2c030001c05585c2028a03030004460700c54800d0140e80140b40003030201c01c103002c0c003009200c0108211071805080100503aa0007800019045558030904440e003828204800100036500141c0305405260060106000244845170090740010021122240f0f8410380700000380503145aa010114881c000c0a441585580c003141c01d206840c40941315600c0c4560319241101143c0f0b0102d0047c2494105128032010310307115101e07000e4100b0300f8007121800c04440d1034103c02104155001184d0041ea1481d0610031541c0600402844410450b410400c0d076240c18025500c1d0b6002d00e5130030700803140d010800c2992071040f0540f000d204001034201c42d1070340313418000d0000f268483c1c02804c025128000c18460103610010780786d48101d03445a00301700c1d264a07102d10f210036a0b0078403c08603113481d2546d10035186616542d08445c440e4030800c0010810310b404a001529911602100d650b5100c44e5031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 665451519 1250 665450269 665450311
    0x601090b01081311040b0a060906110d1403181f0e070803032d0f010f0915260a1b0503010b1e0a03050a0b0103060e030a0c0222060b12 59
    0x112000c1441e0061309a1221040000011700200120385805070b1013004000081842d591100c8088140c488a4650980c0b101864462715510000c0d0b041e1000001e024440240003804440091500007544001a800384000542c1e00d07401d01385140003110601850202100c9920600c2c040c0340907441101018203445804e00c8a103640320310000308800100c6c03400a10141141843d00c400c8040904501c0e40c82d503950403c0051000703500300a1140300c074100310000000c07505224900c1250303010b07001e070802103841c40d14090000349000026040c105281c8125030344002481c3d0103006a18903548603101102855080304003030135442d001da81049000303030300d443c02541e504e444201035000c891900c265801d1850100400141c14400c4a80004040e030249800103810801d2035404030b1b0680344540c0052104000b0400015175034003a81c3c074458005130000c3c0707607000035080400c4030500d44100640880c00c1c90501d0000722007a900d030f542c001c400d44c0b04c2c00900ca20820340003c180c280c12406c40c0101c001541046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 665452769 1250 665451519 665451541
    0x10801061106070509060903031803250501200d0207150c0b040b060616030203070b0f220809150c010b0103020f071124031006080606070303050a020c0106080601090b0108 75
    0xc0600c001e1000008a510702d51b601c000c2503d41d0036400404603a910200d0700400901c1d03d030650b14250181c466006900b00c05583c403440c540c00c0c104007541e4030311900d00c1c1400440e01008090a0f03c0c213884259501c4001d000300610005c499a000c540003000c015150160f01c801d20f00d1038408800800c55070302041000240d4203c40301d50855003151400940d45c43d1600029040e10415840060f0746c140c0c0030800081680200113010100c0c000c8040384c03800d41e20340c500e004200b40b0072103101070304100c80c541c1003442c050460711142220f4014031805007071070f0110020039050206200985886d02002c202011080c03400d02039020258002e03e820360501c1900d4140e01510b0040e000020b01c80054160b40d203200c0d840f500e4441e0415500169030350362132129500700c80c5959000b40d410110394000e10102103080c0e401001d466003c2c010180035070b80782a900d610220001d0801610002245400304002429602d09020b00780140c011203000c1c10340340d45000340500480b0000d0300c001c0e05020040c410400201d6807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 665454019 1250 665452769 665452771
    0x714161a090f0a05040227030d0c02191502031209030906040302010c0302150406091a160f17040b10290904140f0118051302040b18090606010801061106 67
    0xd40c0e55401012441000443d1481d4079040690810b1001c2140d0801c10342c0510703201c80381d883c0035180c0e4a5840350001450b844411501e918404101c541e03924030010b081203101210480c1740d0000392010145c85110011110310052078000041c2c0c07010544d503100388a031084064111141400075480d1400a4000ca01c003405684406414010b61000450130705000f8040360b078a6600c502317204100c902d000c0c0307400030081503144030643e1030a420280161201501c051030380d000d908842410003540c5005041101c2401c4004107007010048041d1f1a800c1f22540a8080b82c010f510841e0404070500d400014600240c2d801e48c041a40320b64180751410081d04072010004a0901140083d0740e00e04a80020030064901d402050b0715a0784131008002c91055141400d9058500e8000318003141c17041c40c2c51000a9034030030381d04107058513030f4030500c0d0005207059444040032240113045008100100007114a9040c003c071001c0e6081c0d080b01040041e9076a120207498013500b81c1d42490b10342ca0500e030848076a2040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 665455269 1250 665454019 665454037
    0x40c050d0302031c0906061409220506011805100b0306060703090e07020d09140603010b0a09030b0403020307060c05031603110d0e1b0406080d080c0714161a 69
    0x150034a10316092610a0040710760032000021100a4003004207903003070051458800540e0114039140b00401c200c0161f1816807495140280034510766200c0d035003c498002c048c0d0403a00c1000a03100302c5480050b509001d9203008055403c11202008084201401990402031660140150142d8180709805003a03040e290801c0c0152140b035201c003481c5c5419074009017207400c261541c84040d801c2203401940011140b840c5203490340c80c00d00c0d083e61170400c004000f10104100c2d5101c82c0500c01802901000310142500d190340c0c1c80d08a107540d9403070319510600b03401950182c1c01070300000340000074060306000718409507806160007481c500d0010b46840184840c0d44400c010561201c04c0e0000c0b035409907040e1200c40c00ea0881c108a6440c1e00740d07002c1e5480c4a54040500001d540291240e510b00e001c0c0300307800488070b081d0b01504040580b004202c50400c002000b00304128024495800420001148030b20440c0d818002810010220100d1000450855007c1c0c41c1e040c15021200340742075840c40a4800c034107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 665456519 1250 665455269 665455279
    0x11a0c0706260103050618060106020a02040b0d380720010b03030c01200c0a030507030219120215042d0803040c1802040530072c040c05 60
    0x101161082a0400e4042c0c114240c503040110003c01484404540e05005910b03140440b004c1042c00c03149551189001d00c103140140c0c00002c1103070054140703a0001001507030300508d403800b0390103641c1d1100d141c000c550004203407410740705d0f14800803000d450b0300981c4250500c159101c0e041c81e010b20000c200740d008503100400d0b0300c064000d1080340c2c2003d400035085448000c0a03203440c0ca04400016000300a503401044801040040504130107099800716204000100003514922034503031001d440c154040c00d8110214030a14199007006220840c039800d00d03c2c8a84519100d44801c00c00c02458020080c040880c075010000c24440000d0502d091000c038400142c1014401580c9040708020314000da200281a50100008120810024150034001d8074501c03602c441d40ca1080312096012402540201398000c1c44034541d4050403400c00c00000040340030031866102400c100c1c0005818000d40303510241128284a030489805010303620004c00d04c2d01800040131583c50545c486070721500c15882401d01407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 665457769 1250 665456519 665456537
    0xc01050d0f0e0d090603090203030a030c050f040803070b07020d0801090f0b0303030f071107030b0705090f03100e100b0913031b0b06101706091801060608011a0c0706 73
    0x8000c079003001c0d1203207141c01802c11603005031211064584051a1110000400d0b1110205090340248289010b003178000d0011410581c1500041c1c004126510031101802030510404000120074001000907001a2000e0b54850861745400d20302c180c009001c1c0b4081d504040b408545240d4400409411070318280804500100c000c0c0b040e07402003401d40c4d42103815020010820101c44841c1032804e000312115510240101c1d03202d8140c2d6213031b0b6101c2c007008081e54418008607213042e00c070308e0250600c0c801c02003081d10860400030003e45000705030111140400e407a418000303001e81080c0956010192064030901071803054000140d8205001080822182d480e203000006051047d0058044a106440904140c80b2a41090034502c0300480300d01d03106100008085109521a59103c44256560300106145032110010004500c4c030080c06520241d500035407042c041d910074001c25004128a4860b29020b50525405900000182b4030031030000c40308104150f001200005c42c40221400741c41c0c02d501c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 665459019 1250 665457769 665457787
    0x90e030711060d090303150f050102120918070216090c0207120602160b010e0a1521061a150a08010509070306030614150306010302013014010302010215090c0105 71
    0x1d0203043c00521507240303041c480000b0140c15621003081903158901d024003403903a5815020b040c50b0140035450058002d2560b80c00c001c00b924010304405040104090146500489440c3c0a65811071f00e5400607402002143d0393342c0c07443d00e01c40c805409a03410500100d03400b1030019586038568443d5440f9840c0c4100c0c082c049c4002603040d103611504a25010005c1c25281c02c20020051084c00b800000c4140030f03022aa425002e441240c20602c0c6464050318000d10303102c1d04410940c8040c0002c5054444135141000240503441580c1d118134946005610024040b8240903212400098214002c20104071154400f40c21043c2139045540442e503154080c3d48541c0110042c0c401340c3e00040101e4100b03410407003640c2603070200500c581d00002c0881c00c0c4102e044100b543e948402c0c44041c0c0401e018204070401090241040001c4500000b0814500030314000e06400310b0340c1c19481d00c03503040d40c510300500440d03905100d10b054640b118415040c050510082041e184e0840300019810f0040002d00d00c91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 665460269 1250 665459019 665459029
    0x50118090203070f02120403020f0f0f13020406170603151306090b0105040b09060d080901030e030c0714060301030302070e060f131a040c0e0402070206070f0309030c090e030711 78
    0x140c094940155100c0c1403c0c81c3c00f92411340450301e00c3d8090701512140b44600a9840c01780e604030f0340c005040545034503d090a108107000045e8116800c101003644103a10b646030a5681614803c0e000e60040c0c1d01c62410f800100000204c06568414030b1901c4140140c42c0e800065820300d0025107006a16991a0340491850712015414000c02081c2000d410205002030480018120394080c0d405109402c522030811002c035000b01c0d070807a400411554a00302040c42d8502800078031758103050024501410a5100745103821808a41419510503c07040c004103902c00c46a0480100540d180c506550466030081e48809281c0038200c1c880c40d4903000540c990341c0720a502100f007080038090b01e20128551070104060304044000c0822181c81341c4a618590410340b168001c070940940d00c07500a00d05400410000e940102021b03640404188009004501e4000c03072800514400e0319111940d038030390f2904001e6024a03070710204500345400704094090070084200d5134007035407280c080e030b138071a10900020b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 665461519 1250 665460269 665460317
    0x60a0f0b0901180506090106050d0905030919031205091e060f0a0206091b06092403090a1208010e01180e060a09050708060601170a060b16210503010501 67
    0x541d000c2912000054030b411003c002c0f41040c0504201408165a007030f09211a085080c81a90001542002280b540c0e03200c1e50b01040d69140b103a0709a1785404807200010b001c00c0300031a100700035503c40c04410020056441e0b08a903030701c40d560600c031f41070901020000b00780d0925030003800d510100c4504180600d46da50001c45001030314800d007454481a904400940e1504119001c040300e1140700b1590051240070220303a101e20b000144514540041c000070311007078001104000c10721030141020040181101c50217036200d103c50320020b0241026506207002841603990a007000e010f0743d40018442c250078801942d0544204000c2c401800c02c805906200911107a00381c02060b00070382062040803001c036046800380c2d0b40204125028940c9030b40e100b94441cae0003038500501145d040210311400e00903003541e5070707031220340c0c000c0004045955854643c0f060340312519120301250303d500b40b03504000160140e1481d08816141a154100441d000500325100601905040c0500c400210750390543c51078240c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 665462769 1250 665461519 665461541
    0x9060c071b0e0c030105100c05061f03080c1606030e0a0206031306150513060f06030c1b06140f10140409170712020d020c0f040905010504110415050102060a0f 70
    0x5142c94900391014500a8000703008843c0328807070520280342054814005039138904c0d0880050445502d983d402e0007440811036101070b42c41d1500850000c00304010303030090164590044068640c0300d008112400d408035032500108180f51900754072039060040000c100c01071540c103a0b85c481da60f0f21031600220764281e0100000303001e182011081014045803298500480f0001d42e036190a070151907841c1e01c140c521a005d043c05540d460329040200368400e4100ba480c801050501441c0b00302c40801100030822820415200c4a40720401042c66140002c202c43d400907206124109608001138184442c026612032181d0001c00e4402d0075920342c0e51075001010055221010700e0003014124014011074008413010703980394880c40c80c0c1304403480c0003140d440001117055010780b01042c1c1003001c100e07424543c1541ca9401c559151090800140248070701409503014503602d16a802c6241c0402c01540c1000380c0a41c10740c0a0b051082003070703036000a18550000c264881c0070691002413241d500080034003100c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 665464019 1250 665462769 665462789
    0x70e06150313140f191707060516031b0c06060b04060c02090c0301031a0901110d020c0111090a0302060705030c0307080d060f0e01030f23010c030509060c071b 70
    0xd20440b40300a64121800900c500c901c03a10541a00d50300c1921494983d070380750020f40040c02001c12800000d19484501841011842004c180040954005412048045818564403030a00c100245404148c580341e00e0b042c03905118011586d0400c41c900d4401c10184800d110031500360004100e6681c000360050010300446070388032a600d04008001c1140e8450903400f038400200407503032191a00c811281079030303040380203100101c1c6015000901001e0080960340f1b555079802207060b4070280700c0001c010501c4040781c0940c0380c0d008a2040742c04c50350821100c6003c003000f002080181c5e250ac442d118100c2c4c0d01195100c3d00c400a60030700504610440034008114000082e000c81003040d61009400c0150100204000c1c96072140820500d0ba9418091038418079903440040000601c04c000f202c1740b072880354a2030429501c400b004051418030a507038884107030351688420f146d440d5041c816158040d000b04000d02541c1080e4085651900c54002c000c2c1c18104640c00714010500581401c100034040f40035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 665465269 1250 665464019 665464021
    0x50a0309080c401a0d1e1118060108060907080601121806061703030403050414010512011811090a050f01020f0313090f0e120c01090507080d0f0809070e061503 70
    0x40620420303071301149031003585041c01401c1a00b08509205d900440c180740001e9599102000c04584620485070703080c2010284400e42c94020403071081800c0c061003d003150030700e54009009180000d00c424068080b480411009036070001000d600107100303081c8440c1985441003003034040e0401e00d410b04080d41060400c14200245640050f048449000c002201e044629440a480744416900940015030512040c440d03640c040310000950941414014507140211591221201e0240d0041030345140f07103000c4080c110311502411907420110105145840e5070343c00000c441d0304d0305000304c0d401900c220b000040141d000304202c482d1a80c41d001140d841c1e0307048611031656200c003401150380c0f05041103820102003807503000d01244d0300d80d07503400341080240e0065684859003080002d44015903e40345208003080e400d0168801501800000e0095180451005131599112014050070401d04034104545e0080202c1c8620568000b04000811500c40b82c0001d240e0b10a51001c02c024540d0000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 665466519 1250 665465269 665465389
    0x906010512090f1c0822061b02060709030507140d151a0103090b0a050402030709020f0711090c030109050a06050a0902091005030705090913050a050a0309080c 70
    0x302c0405200c040c004075480990400035600f03980030505000d20111702c2c400003007203c1e80d0b18191455030201e8200400e0000307101d1500c40009840003501700501d04070000031899204d0b60f0501c075566000e85241080501180b0310b0381d5840e640c211a1044001450102e40700b10895615100b80e00d80c860f8205200c0e50b26000301207081d400404804048c000b60000e0300402c4e2801c1e5000c0c2c050142555009402048507a4031061410080c1000400884e490b021340c2c00c02042da00c0c600d1010300000401807120540300d03401e41c641000040d00d1162218400d0450004000c00215020110381c15945001c40106094444c582c0d800b02510064104590016021501249076071096014220362041110b041d010440f00080658080c4020355600740010401c00520800381001510381740c01c01020300c4690780c9108207449840c10004032000c1114a500015017000c03d0640c03040b4400080d01402000c0e000e8900210002241d661980702116407005d03240c141c064102092459123820481c04010f0102080024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 665467625 1106 665466519 665466523
    0x1e0612020a1707021005061504170f010c0f02010f060501020706110c04020406080130030e030c09070206070212160303091502070809120a03020c090601051209 70
    0x9001899070010b071540d00c05100d804698054003030310325140d1401d42507134406000144200045140e49200b0b9005008840c00c444015802d0020b10744900d403103038101340e04900d9054895203841b1900c1056034110800d03021180690703000708841d080d004012404c403041406034900503401983e0500c0290b02580c01440701482010466141c001910006030980e0300c9500114001840d00c001081803003100580b40f84003189011450482140b800d0030702c0d00b24114542e014040203d60030140c4500d17102489000300403180502943c0c440d20305007034065600d03c2d06941460051050880f0403e95442e100b0a0b40da01800b0000b1107803c102440c0c4041f0041c1ca41c190068400c03400011107a11410001d100501e2142e01c10b406c016215480e200030070080686226910310703541c00c240d880d03c1c0020f90220350322041c0310089861101540307a100040b0f42500601400c4d000e000c0f0703c01c09120305105c0c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 665287769 665467625 := by
  have h0 := BRFrame.cov_init 665287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 665287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 665287769 ≤ n) (h2 : n < 665467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
