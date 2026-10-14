-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:59:39.178482+00:00
-- url     : https://prove2.me/submissions/22e7e2bb-5f4f-43cf-bd7f-930a2c3d5c7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 258633093 ≤ n < 258812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 258634343 1250 258633093 258633113
    0x409020609031510060215040803100f03030f1e020d030c0e0d0c03030e01170a110c0604060b040b060708090d060b0306010305030c0c090f0708090f070b040824040b1b0403 75
    0x1300c00056800d65081d11503008036500c2d07015050708402102c0d00c0b0003043c045540b0788040c562042c1c40714a28021a500e03540d40d404810308941c412004a903000d40403403182504040c6181111200c04080011a140711400a40da10038612491003415500e6900c1da048d94403503000703039054040c040c000d5003955043c2d261001508400b40300a40000b00240c0003611a03601c501007031143d22440c1c030180f008940321040c2c00c3d001803000b200100d071202010400c00640c6041031040ba841280648400180b501c107031003c0c441542c910081c1035205440400c20040014605da096903c40c00d07040d0b51080e42003095140c05001440c01c0b021092741842071200002c100a4000000e00c850200c4a0584520f65140c00038805002c4040d541e08a004054400054046200300f21a6602c001c0120485d032400019607951030030300035650800d008000c0000b409200b5400200040705e10882404440410000d08500c502813400300904009c005c40c1d4a18040b8140c0b403144061400e0300340100c0c0c41c06a85654900d0031400c0f030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 258635593 1250 258634343 258634351
    0xf030f04050a0602010203010501081513051305011d030f03060406080102070c0f06030603081b010b060c0c0901150e01050f070614010513060b031815070903150209010e04090206090315 81
    0x160840b1030040350551042c020b4a049038070617100c8010303075200c06c0c0707201c40b80b4003c2411598100d8000303001401c0503051030041c24090340240c0c088220003505800c0c5036003942c045000091030801c603040e00d0100c01d0400012110019103090150b03449442d820b00003009081c0c2070340941519030001c24240c007030155107030171402161500e07003020f164141d48000aa056480c4d61001401d44030080c00082e038070940c40c071186c10880041c0400000c40b40344810005403185c000d2403002c01142c1c080d4407076612504001903510b0147c4428040f10b0414501045d000341411031208105041200102d640d084120405d410340c1c601035442042031080c08183c001d0885040b4003440b401d84600f0381910154400040ca10800c802e640030b4061092135a6070301d00d20a20302d00d0803482c0c03500171403140c400003c00c24101c0c40700207802900c19a0b00c40c11503c0c55410241c3e422031086000c1ca040d40d2040121404580c0c100e443d1755480c42c0c082e10046080c18030f5000140490240303804094140c0181d0f90302d081e00c1d8010203042c4d823207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 258636843 1250 258635593 258635599
    0x608070206100f12020607150c0318050c0d08040e0406050f16080c031f0306090203010b062706072111120403020402070203120703050c010b090c1204050f030f0405 72
    0x4a69196100c285812500b40305800040b480c243e018022000c40c00b908a0310140042c01c1c4514240302503a071619041803050300f00c46d44a90310010010700991502030802d002c0130141c00c5020090b201c0c0c0700c2c01d80754846030f400f203442080191506001c0140c04c0040e500101814a104581c600c2c15040c002c018140c101c0d8090b080000480000d0221007061644040e0701900c1d94654070305544401c001721a0741e00c00b52083e541a101c03860304410040100840401075441428041a03501091040c1801d480d03800d030020b881748100340101c62880340e40e0f0400c20014071511011400e01900f40c00132031717090b1043c01c0026003a80220764030080c4c0c442124078113003103107000f80d69050318000c000041d194450400740c021041c0050200800c0000d0b19184d0050200369000074250780000e040d02c541c14480707a12480c4114045800401e220015880a10411140b00b01c2603895109610b402c040c194030501c140940032010804034004141803100c100400c5a4905d540c004030b95a40c6400044c0c0c0f40c2030b0b04213200b0300784 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 258638093 1250 258636843 258636853
    0x30209072a2402130f0e071d15090405060a0b030f0604090605090a02010f26040204110a021608060c030a1e1d160b04150e04020a05041401020a0203060703020d0905060106080702 78
    0x2594101100b01c00c1c046403115006e101d02c90f03d42c1134003125000d202d00000e1543e202100072260b07681d541c401c031002c400e00c12081c070b090307650002005000035207000920b4948101c0240608010f01200d2000310395114807a001120b000da030721900050003c007500c91000c2c2c5014a4401046820714002a840d0b030403078000d0b2200300c0066a00241100c08072400340100c485024540f01c0c4c0c0411030200010305410502c014000302e07890306000040041a00a1024000182e00c1075107000c0100840100a00c05401130030040c03c1d4070b140000401c812480050612440290f40f0481e8100843c00203285810403280300d038091001a8007a941c43c0d0102e0340189480c80c0c1c0d40154900403008400e6038451000b11060315101ca41001e181140c09181036208904a00a0200c800f840702c0035aa00d910051120000d070340c0750030f40c0321818609481c241c40900306c1c03007906540c401c00498002d6540050310603800a818600940d60b06000d00741c140161a8154009115201304070000c40c4058100144078030501142d4200c3d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 258639343 1250 258638093 258638099
    0x90b1809100f02031e040305091009330c0506010e0a1e02030a0e06062b05010606050301092d051005040e0a050114043216030209072a240213 62
    0x1072042e88043c3c0340240422340c100b04000d00f500340070340302008008950804020300c44c1d41c0c411954481c62540441c00700728440e990300f04000850300e0415411594107140a241e4840540d0310140d8a682c18000d6441c80880b43c00018200b0716603420484c1d0814042c9004051300e0300d9100f607000a5003003580d071950440e0500c4099801000005951440358034002e101e4042604400000100c802050221b8440940580003060200c2c8003409240d004045030f50340ca555075894500100110784109003c84d5020031750024440d0020309000b52204808134071500040c0f00d4031001004140c0000c0c0f64031032608a41000c4202480c04008142e60481600550081c8940030b0355842200c0c0da441c045500034518240104403003c003202d050b0352a40f1070f2003804034050390600e6141030a0b280c0070500070701c114030030340b40d078014021400c24405441d00541141007084501140c420880b5180742e0041300c05040d8000091840180103044070401181804a00d070035401d00258509040a03510400756203120585c000000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 258640593 1250 258639343 258639391
    0x9150a0201060303081509131e03080f0f0115080c040504090c1d01080706082d0a0c05130b09060708040e0906010b070b060f0d120315090b1809100f0203 67
    0xc400c841b001b00b40e003003030380ea91200c1c09040b5008808281d42406d40f008001902400090520204500a44410b0079900e45546001c0c40c000000b00030f040c50302e0110740100800c08602d020022040f0060626542c5541e80308220140f9000d40c0c0d00407030340b06090420910a00030b4041c0e50300196100c5140301004c1c240301c2303002511544c0c420f02c1280e200e0b90086004000443c40b400c401d54100309805201403180030440c810099403941c0e0401800c40001020620010074141d05c18918441c103039082050800300710405a800f2054240306254441c42c0c00208100e140c0d54482c210341d11503512002d45038903143c541c4907401c0019812152010680b16140c00807400c903a00c4001e5908281c0d00006030200ca070b4600b014071811800c80c5000a4004040140c10400907003943d0b14145105515540098081e60400c201c1ca03c0d140198080b03a00c1ca80380c41e00000391078580c004100f0001d01070240501c0c0b507444007001c551a0450b08284406102d00d001407420403c0601c1d0001c0d070140c002c408075003083c51409a45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 258641843 1250 258640593 258640621
    0x120606070302070b07030504030b0c0c010b0f300303090607020f03041a0d0207050105070509131503121b0c0906090b09061203070506040602030f0c0408030f09150a020106030308 78
    0xc0030300542c0c0a800d0400421288800404c500c40c0300c1e00c0d2070f034186540c03036503058403076030040d244030b4100d901c08a940035440ca403d1141455402044480190780820240030503841e20102000340342d000e5024a0000b424101c0d00601401c40703881c4c0044aa0300d01d00603102d661900c2d0150340c200014083e5029802c07a1040000644042e03803114014030005c00f0032003030840010b0380418200d0743d080b5000d0001380003041c420701c62148604140c0d1a640c0d5610107500c20805821000d4a0400100d0301d412107110b09458440122001d0300e9000320f8012560341001c0d0140e804440f003c51000200170b0308403501c4100144081444100c1d480482c0600000392604202400e4810703501d1170070b80200e0b040001078444d00c1c20003070080c034802d05842520300e49855078650070708114040310144c07401500041031141c510300500240d035111601080c224102403c00c0401c58403403141a44034101c10b807010580780b80750398410f00702483c05240014030030b503200021040a806071610b40320a038003141c60800020342c0d00120080d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 258643093 1250 258641843 258641857
    0x180507031b06080f070e100201060905010b1218010207020904150c05040e04200315040209010e010e0c0706060b1909140a09091509080309010e0a030804020909160b120606 75
    0x8500c20b2a44d035445180030081001032a8004103e0703d00c040000649404080496002c0c4c02d0703002040075810b022225060303a4041c1c3c0036610003441000b90303106440c045980c40f500003c4078007507000340c0703000760302d82074007a020350320019510121ba4020701c010010f140c15070003144402c4140500c4600d8000b40295028012441603050007000b0070002000111441007420004031181c3d900b0a1280001020074034020b1000c005010500a4100740001e40ca007854099005000e0107030b640e82e1960510400b0000308801500c203131103060700400d41004203c07150f04028040c0401851407503c560100e110128044488000754010034000000806c01d42840c0880110036100646402d40c2d947c5031000b06002045060300c01e441e0800c0f00c000c010440401405505102809030210325202e06007111058211000325450a0b4151b0081907660000b1390400080c070380c4a9011079101460b6601d5a003201d09209001032200d444c0d24900d02c0100d2040f48550140020103a0001031441d10380d0350405000d242d03c0b03000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 258644343 1250 258643093 258643097
    0x41d1006050304060f020c07081507020c01140906210609070f11010615020f151e1302130203070e0307050315060a0b0d0507030f140604020c01180507031b06 69
    0x12814031445005800071038209100c0c480009600d89940c940c40100c1e0403c00b0010001d03001003804010a010401c03001041d07200150a00300c1505013100069628913503c01c0c1c007814030200a007144041a1407806855100c64003034692956290240403900481d00d40b480042400d03103691700801e000341420800c80d40b1540c8141c4555906140c001415150b08441d8108165599241d01021400a00c00c4d015203424a515400820b416002010140d051010b803035250000c003074440082150a0000b01301c100c49032a44100c0f001c603a61224001160b107a0720341c40000c0d411450b0072041c034400141e02e07402980702c1d031350903500c0c2044040079400300364507541e00e440781c144e0503840404200c10501c0455031003900301c800105000c088540d6919a520550400b501141c0000e035140e04000005816024840000c0481c0c0010810343d462041012034070180540741078003695000ca4092a140d500b503005104078080c0c442c840b5003070b56030761a02541c0d401643c0402c545001480d800c4402403c5000c805c5002d8492603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 258645593 1250 258644343 258644371
    0x41505040b041b0503012f0a05090f0f03160806010b0a02100c0e12010c03060609030f1401021b0a050f010509070303032004080d0906021b0d02130c05041d 68
    0x141c55030020040e14004010f4204104840042c03660b90034071460340382e445240704142100c0e0305c0e8113a007606021010700414240000b0051a02810381c49012580003620840d0300321201c00d070103c00b091100c2c1c2c0700269036406104005100c25400c2c1003007800c0d011520541c1c210f500c4c036038980301e042c001405000d035000090b900103440b04046e42d030f00e6042407a03041c1d118070781580c10890000c001103500400400a40c820f0b507640c1040700c16164103000d20001340503203003000c040796032841d40c813807540e0b60b18048040c0c4061307003845036054002c0017034040b580901c82c0c1d0505c0350502010121100c0c4c0720044072004685a2017064690070304944180142c45c40b4008910140c148949513480580c060702c1c0d540d07402803c1c0307032007500480c41c0c0200d600c4c0a04060001031f80141000f18000d03102900c08000760304800f056621000701d5030411001c00f0040c2c414080d003601c0d080d6007803546101052000c102c0c51600015242052001810705610101400844251385455001040801d41d4104100825602807403c40b0034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 258646843 1250 258645593 258645601
    0x6040c090f06140c070608090706140307050c160b040914040c17030903030a08010e1302090c09041503030c12090f030215120906060f03031207080c0c0703030503041505040b 76
    0x348504050841c0702d48107103113061040c000d91410181079806c100007050301d1205010351308008009000140c8800d041070700e4444040b4140102c9808010480c01c1008000240302c203c8410501c403810320502551162070300152601401000d0b80c1150040c080b10300d1505c1400c400c020440c50640e4041c81e00080d0b81e42005081c40d0b1035202084107404440024441003000031b403d0b8a080009000901c015035404002d94180300741d040c103c2c000645003114120070700185101690703990880c150040000d85145545810480206015201d01c2c2c04a10480e10540740003c14146c1010054000e13a100b81c00503ca0251904e4082e02d03070804a000300305003400c2114040c0010300301340389100c80d481d603405169401c040f05246030000c0710f40202c480c011075820031414401282000407800d00d003600102c01440c18070340c014842290007200103104008000403440440c01c2d10646500316a4200102c2040da215252070f804c0182142d402501e040300e0744004808101004007081c80340c0c80c0115803160946a09441d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 258648093 1250 258646843 258646847
    0x18020f18060c070303031b0f0e060a031103040c0602010509030a0903080d180f06110906090f0f12030a080a0c08151207030c1401090302090c0715020c0606040c090f06 73
    0x21505503481d402801c01c1001c0d0125403000c111000041d40f082d13a0100d20009548800004012094420028801c13a41000213041d81c024401b1941c0d54015a02140c4400c4050411000341121141d003005022000081c0010702c10000b4606042d03900c290001d01c0301c1c3e1503554615941c9d21a4032101400602500001e0001682d14401440308181c0b030312002c1840c1405a000c0d8500030304c17804085503016402003800e0104003640c0503001e00c41c29140c1110b070070607a1840c0822003510888215030300c41d00008524414903a21800c01104003d0041c1880c0010f664102c1c04542c1e9a100c2c5000e203010820722000211244640c0c0a102c012401641d101d0f0b00c191140c0c24101c4a0703034a1140032a42c0024100e45020190700c04028000c01980191100103c041c9840801001240b4210a0324104008070000344096140c4a54042d0066080e900303c83e40c036401403c0202ca8088140c81e5001d506000080c0340301d48100c0061780710f0080303208860411a043c20803400352a0b0842500c54031880320030680e000c00030b0078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 258649343 1250 258648093 258648127
    0x903210a140f1603090b040b070b04050321010f05060316050a09031b090609050402031903030207050d030506010f021b040e0114040f0b09030c0a08030402010e0a03050718020f 77
    0x141880c1d00726400e045040c002032500d074120100038103904244480303000074198801c2c0c0c808000c12150070550720385805c14032078840a102c1c848024005038044000b08041260400c100e03508404c3c14642828503028000070500c00c00420b105510f40c00480d54004141132505070110390090309418444c10006401100a1b05ca5401001058041c80f0500350004041000070342e00c650048124003400d030390740381000b40c100d085898581004415600d0101088016100002e01e20005040280c2c0701503280840e00d000c4010341300d41c40008065000b5001d10034007860705600054010302c1e09884000f0114010f480403a038850032900083c04040441c0103220041c2000c0e8001800b00030540b0020450242c01005071000900c280c0e821a444a01040105d052251049040c0d03004203410010b507203008061f0701d07810f03178600007008081d0448100101240440e8051040104010307009082421000c0d07581c208203403500224803070980f0662004650140140350b03442221944202484654242440094001c00311 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 258650593 1250 258649343 258649367
    0x30703090f0c06120e0f03090f0a0f08060601080a0c08070e0f121c05120f060f030604050f06090a02010801140103060e090109030e040501050913150f020903210a 71
    0x110765101ca5002c1440300a11201070222a00d684806010303209901c0f04076203448014554540090b080080814400701c01c072000b6120481d6810388440120000410004841d40700d006a15140720000074075800c0420064481c040c01d81b03c0043c10760f288075424060f00c403403250b9180003540c0800042e051a0043c07101e00c0002030b000d48901c03400303030012010030004041c2a1420405502a811442100c264051349003d03600161810a041640f1040300091001002e0280040b0f03030001d04c001529038aa0618064517008002e044603d1400c05080064172400c482c0d0341e0170700c00d0288000080c140000044e22020050341a581c1c0502c5030302c0c12420b01c941180c0c40b00c6560426031620b00008402c894111006e02400d1400e0000404460034500a0039031254002c1c1e480c0121308240c0104456a079101103150b020382907201c0204609254589070710758030148927034209114540b00700d5202d403040a901410408109a0032505100040d4000d0600f20405000c0684294130801072880854410118070404c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 258651843 1250 258650593 258650603
    0x603040f050102090d0c0f06050f0703030507050d0903110d030b0d030c050c06030f2d07200303070e040b0603061c031101060b0a02010c090e010506070201020f0d0323010b03070309 79
    0x20310001100080405e400140c06907516107200c4410b2150312400100c2000406903805e00d0340ca449820098000310740200301001e070500d90b07144005290240030318102c522058410104000d80b01032440d005e0050640c02d15488400d00c249109103940381c1c00b0384038150800000411a40d600304490b40d007203e944a950400301c2d13140c00b4a0514a00e940c40c0d038030143d0300840d04281e52a20745c0c070300342d20412098030303000d0f0744203d0100e500d0343e964045000307014036036400c09401e140041d01c182c4a54203000d52043c0b05c0b43d0b2850540b00000402858a6001a003240281c034100c40501c061007401d0208103a5010a07a140340d8031000c80b00c80d50b1f02a01002d0030406015101e424050b03490440004001d003151080d90118841c1c040009190300443d07428841d0b07080b105007a0034080310f070328180011541c0c0c01c941401000d000e00030000d040015a1b008005001505100c1ca040781c0b058492054020090501d040c00c0f1842c50000c82e08000103034a100d0707030340f9040c0c6000300501402c40e40d0b0442c0890182c0a5170f041621 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 258653093 1250 258651843 258651847
    0x81f0b0d0507030c05310305070302010f05070b0105010807170103030206100512060723040e0f070f02120a020106030803101a12071206180e06130f020402180901060e03010b06090603040f050102 85
    0x8103111b00841ca0000b540aa4003500c48185540005801542512003020800c0410071880c400550b0400c1040c4c1525420301e0034101c9a40e03202c030309948107400c1c0c240c01d158845039003000004055000a503a442414400c0d000340c08913507a803084c80400740160380340480c280c0103c0c0018020030300c1540c110040020881d170700c59241c002a01490700f598801e0300100c804010702810401494500b60302940c00a200d850080c0e40c90500702e80003921040314030301243d1000d1b800079074020100e2007504600c01079038100d8452552402d00c0110f40e120007141d80300f5680700b142c00300748068400620700305131461051900703442c02c8160b4800c00d0480d50206000c0c80700d545a83e580c0300c00b04901e131440b60308110190003003c00155414151510303d2900c0c50041008a840802a10f440c0000d04030000c03820505605950160701d81c0343c1000400601e00c049041150805014000000c0c11940040010741c1e200c41036008101c0c04c241002800703094810106c03011341040080001c9400565503480500b0b600340501d00040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 258654343 1250 258653093 258653167
    0x1051f08070311010216060903030806180703050c19030b0a060320090112020d0506091b0a050304021c052505010903110a030203071d0a050405060403081f0b0d0507030c05 75
    0x6c1e440851600524000742c880074007401010b401041d0907812807400c45503a1080b40210200c090700c920020459002c054880d004150048001400e841406820983c1140c3c1c52048a40080007011540706091055030601400160740740203208a41c41d085c11213090b04899100106a0401c0340d112800d500d0420039135500320701c0d0f840303054800b500725003c00315004100ba0400c43d041000c1000c01808160001040c0c8090840041d00c610444103840900d043c86501c170b60f1a8000100800305445140202c00c50342c5210380100807000c00d80f06203003400320082042103085881e404203110054080d940c0850030070901440480c40b200880081e203980107004090242d282d0f070102341824500c0d8000105030b0341e0f52846060844480c400c00c0c0d440b400d13212040005240030380304d00350b0340e540c003400207018815000d0103c2c04203142c180d066450b5205040c003407201c2940d0307200d20001d10351080c503035602c03040d250401064049110740140c030b61080c181d80d14141411210116a25019511200d64061a404401003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 258655593 1250 258654343 258654373
    0xc050703081803010c0207050603190e030304030e1c0b15030307061a010e04020306030c090402031e0c0a050306041127040807170310030b07090305010e01051f080703110102 76
    0x14640001008200b61107040e01c00249030a5904102c680c1081d5000b6503001d11481c0c844d00262070317114491a0002e404820030301c9111000b0a1040b40740c2c1d4031404000100014150171131082091141c064a0a0300000b10309041000c01420108008003940803c0000c10207100c010786440e141c2d40401004ea03480c10100f507592031704840201002145a038040004010590b030011540c032100310382a50290300c0c501e4038000094603640004884c910900180010800b0354400f0015940c004401c4898610700e10740c400c0800380c0c1c40e0030f240300580c468000e19201049a0a0200791280201c0e030103004a1212041c0300c0411002e074005000c2800403540c0044000c0c460240d5000c0c0e00c2c0201e0107508034135610034060610800b1203000d00ca1001c2c0c000002c1013489130150764808000c0c212508008018042c0d06d0f10314007103c144030194000340c1150701384075450400c45010360080b80141112804502c02007550f103103191802e0303218411381002d9089500100007090194010b1070491105105a0b0b59480c40241c007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 258656843 1250 258655593 258655597
    0x2124209070206070801050d050303010b030403090e010f0f09090305030a0e010f15050907020303070203160f020d11040c08070509041d150403030f06150c1112010e19080a0c05070308 80
    0x4281c0140c1c03000e0180302000d5004083c2a000d040c040e144283c10300c8442d100e071640c80c48188502041c0c460000b0004080c03600c5881150054081003000010b1741d40d56101424089070705000c1d2036540362403641c1c001050f41f550311400b1600d40d03040d140d103801c580d0307405100d030000e1000381c9900c2c00c80d54031183c2c1e09040044510641845035085111820680c0c2030005105881c20000c1080003598420410311130a507800000350780100d503000200c1e600e00c0e151490712030000c0c519001c000b504100c045800a0070000d5400d00311411440c284c038104424480310204907400c07103017610a1004280d0070010701d440c0e8101500f00040800e0150018a000f0a0503541c1c685412880300300409c2400804c0700348000c055144c00340080b08070240800b40309041c20a2081c0303034a03501d0001d990041c80701000a050030840c98020203015100010711811036520a0034416000e0825407082c64600c3c05a0f6541104c0302181c0c4401482071a080340515003014a802415035131503e0b0081c06491600c24504008000303548040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 258658093 1250 258656843 258656851
    0x203100f090c110f060f041511070203010f09021c060b0a0303210b06030601030518060c09031501030803011a0c0102030a150e16030c0e03030c0102124209 68
    0x20000b03203109120000400450242ca80051030307030450398140c2c2d589100024003640003c003846055403207494502d80900140103019601c80254140074408000780d40700009400e24074020350017803124000310900312085035400b82c4000d40c804040e180c0d000700003071090080250350f8400e01c070003d820050003000844002c8140c0c8210700241a8114200c404030621401034910400307a0800c0c8512210000019040e0000601c0107040564a030000707001d03100c4030058000040c2d440c9082d58000d0a01c4200400160b0018844038001d1084620780c107208046560001c1c100d03a04109410f04503400c3c440955107101001960048090b0b00b4440c0d0011450300384002c6000d0001070100086003da551240a000e46169104d000752848000030130140520808503c800c82e5150720700090800f246400a07945842d440d85656003501c004600802507100550040000544044c5008a039507180e07504042903000407805290004190001071308803c2d150981200007200025040c26000c81c150003141c103454040f1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 258659343 1250 258658093 258658109
    0x1e0c110f0313050603010e04030309020d06090c08010501060908060a020c010605031608011407020c010e0109080304090504150506030703030e0a120803040605160e210a0b10090b10030203100f 84
    0x40c6144a01001a0002c0d00400041d500320b8215031500345051500b0500500240074551581d104104551b9485502540310340d021070104103c022a00748008a80701d20b000c3c9096075881e03d0008a031080c000c00340c0100300c1c0e0012004003040d50700e040000b4040e4100c00c001c3c1c600c0e5174940701c01080d0b980d01032024044078010b010508055078a00b04000303080d1a140d45020b00d0b801200d10a102c0d00c1c0f5404502461444002c0c20040108121800101c40e4072095034802c0c0c4050201080106141015400043c0101c0c040c01c140e0403082000d038200021100103881d0294107901400c030800000340500341c807a401a9008118918055036001d07018002c1e086804112074041c400003c0204001e064401d40f50000c820310804084210900d9001c0d10903c0b4402d24144600e01b410822008540d07085c0740390000d0300710078098626405c1589422a1025001e642c1116103d0280c00c010802d03660307038850b02502040082022071499036500098009500141100c0c1040c41c20a9002c40d80c00403911148000703112070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 258660593 1250 258659343 258659347
    0x60306050f070207090c17040c03020a06170a0501140d0318061119020f060f07120e120d0c060f0902041407031406030709110c100510091e0c110f03 65
    0x1102c001d040c0011500480c5801d46030030691100d240d4440e4040000743c11030004411152103d060084c8503003120740c0000d40c002140440401c025a00517107003400f807800c0703c1e10941d2039140c191111050382c40074010241c2c42c47c1c07030940c0d132000f07840c4c91400002c5c0341e0b020b42002c0c22240449410540c2c078040d160428000304040254646903240c080005070740ca80e4421900e002480700a40c000342002540c01910780c41500007082021420300c04000703c626156009400100c20400144003070008198450124420a803013a80380420240c08620901c0221203a611034003014855076034075000300a94001c520344c456443c3c40c49401070300c440c8901101080300c640306d00402d1400358001070656040c034140d24403810344030341800b0300ca8400058003030030380b1800b50b004201800c0d20110001240a00248281c0a2058000c07070603151701c1541c4500c3c000c44a10803059003050310b8490f408140c0b03090001c01010307005004c42d40664903c0350b81c00300061484500c0c00800209000300e6152820131411610f0441e5000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 258661843 1250 258660593 258660601
    0x60402030a060b0d0f0807150c0f053006090c070f02040221091c050703021506190f03020a060e010e1026160323040f020607050303090c0a1413060306050f 68
    0x54949070f442d507048003403041c03109d1080e9200080540c0520941c003021b104012606140d0f1030f1000650840c500c40104c4030f1210030381c001d001e450305a181650700a02424415021600c401030040407500c40315006100d4440d59001e07507083c03100135840108000d803d01510780d10340c10900f100074030641c0038451101c000c01c4502a944038003003406042004020500208100e100300190300402c88424901c500400a1060381c1c50b48003064910500e4101310001c0b0209000100f620160301f4000f8040e030303000703442e811000c5032500004c0d204002081d16940c085001d2018100d03507480c1c4148052820401890003c51024104c02c2041c1403111420b110140500050300304038030107000c41c0721810030b0310081c60103020704c0c03004c02900b40302814240c00d0107904403001000034081c040d01c24101014168083c00c0f1680c0c070107445c10200c1d180d40041e150000c180c02100003041d043c2c0313081e0214600707a038000c11078000385002001c2004103080c05002c1d4034250361785a280001c04200b083c031419215004c0203189241c0c500d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 258663093 1250 258661843 258661853
    0x308010602010b0d0213061505040608010e190207060b040f0204050312040f1a09180702011805060c091914031005090c010f0e0a08011508060402030a060b0d0f0807 72
    0x505800400071a0314001148546070390700d808180d00240c05079078003107100e000916141702030452a089480d0f2460150b0b4107261599100c0c005104031401d075604d002d0f043e41c8800b003815035034130140c078540c00b00080e440003c0c0410724039030300801c03505d4810140020350300c100c07202050a58844a0114442e603602140c200700d10704090005406a603140c80e18585032a0822410400c0201540143c00101c003070090700f100911240ca0403100000c60040c450b84075055403e80c00a04035000302c8650005508105210070710b0040070b81000131a95100000c0c01c1c540d500c0c1080038a00d50840024507902c00d04803199415800e04107413441d0041c1290100030300d07100315141c0c10300d450550481c90a0303c840d03142404002004501140001840500f440c000b13032403461a00080b18040180845960303c0802240700050191055002e03108500b50200c0a02d8842e0703481c0340150301c0304002c480281d010b401075048000091400c0c0c1c03003400b4031080184a8050707140701307486038010300158082c104d40d011030000345001448 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 258664343 1250 258663093 258663107
    0x30203090d0c0803070f0c0c0305011d0318011110050a0902040507020d0e0f060f13060e03030a1205100b040e0603010f0203091c02251e0510110313080a03 68
    0x301d407606051044101940e201c6070781c0d1000604003801c000c071050030307800110f2003411201c50003500b080b82961881c0d12410994000d16810401d8807182100d0120120001c2010041e0b9418144039070764814600003ea0041d07030700100c512800085030292490724120084640710707443c05560300060000303860441d0310601c011600d015182009540c4000e0f0224555176110340581c0240400707071441c62008450b2008101c690242148000218501040302c440c43c104c404100421240c2c2a030356414401c2421092503203030322030b283c3d05000180054029403041c0c801a0822074109003e094000c0c4c48942e1100b296000d82c0241d00f0100c9041d4030002031082515007401210203840300460210b01e0b45c100782141d543d8038440340240d000c1c00040c02d8499400d042c000c2c88820350441c40d00c80e0001007000780f2034004000601d103001c3c1000c40740c201c12031524140c1004212400780c0710003a100041c0e50a0401094807141324110001d5184d11081004800d110350f8507510400811541c001002c5a042c1d0f858064007207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 258665593 1250 258664343 258664363
    0x7050d050f070f050901032013050f0105060a140309030708070302030403060c032901020a1b1d040302030a051602130504020405090a0b06040c021c051314090a0f0b09010603020309 79
    0x6254143c42809603585a40106044903440b400040e020300d589015244240c2c00ca1043c0380d400146103980d408190364580220b4800da104040d10a482e030303203d204000240c00f90315800d00c0001c0661850307500c407121000095801800d9081203c1c18503465507a101503541c030441c400c4005030404101041084014082d521812070f45040500c60809501e402d9140302e010740c101c1d003442c15140c56800d68541d0082c0821118a81c10541c900d400608000c881c90070110700d4070640300c9866170300c13a040e4080348040309000d0195a15070f005d9840c0c01ba00c45022503890300401040c403001c00021504d00b00507030b02d00005441010300a003000c501441c003030041004a440082c000f800e1600214114000100d1051045501800c1204d0001e511880341d2400ca10b003202e08280401021030701d189480c00b564010000d440749031100c9009502454070784050840080f4000d01032508a00000041210781e401130f008800d10b04034031440050391300514800205c5443d0203900203008030398000103020004900703200340140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 258666843 1250 258665593 258665609
    0x1140d060932011e02070f0204060e070e010c0c060818030d0b120f060103080a090e34141b061005030f0f07050f0a0503100c030b01030603030e1207050d050f07 70
    0x410200d240c034050001312a41d203281840d8002a003c04000151400401254014000300481529451084144181680c0d0308000c143c1200d0a000598421068010b81c03a0380401c040c0d0b80c0c076181c081c0c1591008405445040d142d0200038100e6400c41d0704101406d81c00744d0b40e1a01043c400c401c1414043c3c0346900683c0440c60b500b041c6004c50581c440062042c2c1100da00440f95991404040c03002c4801d1501900210008034061007401558134001c1d03201480001483d40e890629110a0f0f020505065040d21031404200003094801103401480040c201154000e030050100f807808042c070300e041400440d6054140036000009101d00d04080150801810b41c20009148003158a2000c40d95028540700d0103100740100020084c6585444011034010800071f402c807100c0d1100c40c0300c1c0101512408164000080c900700880b065580b09001c0c1604a0390503446d94010702e08214140001c034112002d0340c04244c4500b190000707070380e15134002c00e4601034019805040c044455050045c00c11015a07c00f1003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 258668093 1250 258666843 258666851
    0x2090708011211060d020c0c090c03010e13030c06060312110708281205030417090604030209060d120c03031409120a1b0f0204050f01140d06093201 65
    0x1108a6041000c0d0b010b880e0050380d8458041d22401c00100716105049001481500100c1c3c1c3c6c01500c0c100045850010b001100d4400083d6a1685030860700d0009100380c1c4088a070800204115103c001d203d01c0d601740c000e14104081e07181e5500c3d085d0a4553b141d00407600207510181c46c080841d8005ca0300c43e010400d010180140c81d251054480c0d4410840b5118402e546180c41c0c0b240342008000e0001086650048145a800700d0030070010348a034200f120155034803001d59001c2c062104444084507042c9034000e020300e0516040d03800f0303c086c180c001440250001130120410000c20150344003d9500200b41e03582d002035071010306d001403d075980124103000f1082088244443d41102140c040612031880b000d003a144d10104400300c0340c0f01c244625900d0070040e96900102070103060b48066440600944080c00b490b103607081c801441c01c000741b06403070391038906000e0000c56207412a00400d056008510105a2401e07a4485000c0c458010f90600e041001c6100e4200c0d03841182181c81800f0913464000300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 258669343 1250 258668093 258668099
    0x711060405031b030417032505060112060e06090304090e0613020d170406090f050105182115060301051b03070c081b34140a120803040209070801 64
    0x1da0350b400f5030095101d000d05081c0303442e10f20040400c10b030384c01480d0320012400403001d444046901c80d40070320800c04400b41c05a06100d020031b606200004603a90103801854030341e2800c0c0140d0140003506004840701d58603045e00c05008401004610301403091180515515480c200006049507001c4e5049801030700050200b003414110f0702218005140c05403000440e410a525200c00400f44101c0720f135441032004075000c44c50542c4600007200385d81560f4011055076486400664260007803525800c440c8502100800c01410480d0f0024803e0751075402c1da45040031100c034181c1c00d00310112055580c1066807004c01c02c1a207024000c00b500007114107001580180c905559080c02c4c400100f152003841340101c0058200921041280e2100c90740300182c2e000c15103109100c1e916855402c04030f0701003036a4058100c0b41d910850408041080c000282c014003140f818074078849015030343d045558001000e01d00012305e01c2c01410707600c410600c900c100960381d00e070074410040da000c40503025000b0418640014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 258670593 1250 258669343 258669353
    0x27040618020703020a02030307050105070e04092003010f0c08221e03050702040c0c050106090509070501030b030a020402030c070507150807030b0d020a080d0215060616030311070b07110604 83
    0x48110a003440030241e5103200a05069184c5040e41030005d40500c80040e01038140501903001500a101650b503000320303e40250204030030341c0d00b80070020b461310210003000c41e4410011f0f40740c0010041c0180c00810f8034600c00d402041101c00101120000c91b10500c00c10085004110506c422000d00e004080480d500d152211301d4004440c00a0a008005080407081454011402c0d102c050754000d10a100386d00315020010504550410211811340c200007010070002c8107402030501c5641204000d148492400f00114040c1014000d03041c5c16000d059113210250311140011417045010340c68065603032040c1c0c6005442e00002e540130f503054048602e013481d03513141e01203001c435081600c501d000301d94a40401c00103a6126409040254070174000c09c40020442d00200304050380701c9a076000c2c0c505440703140c640e09030003600032510385601100400855501210608100503482d01a250000301041000d208488540c031040085da1102071003400c1003a1140d118003995120f4003c00050300580c1041ea9403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 258671843 1250 258670593 258670619
    0x11a03030f1c020d110703080f04050c010c06020408030f030103170901050f0304061404060b011d0609060304031404060e040515010815062106010306060f0f051b0102270406 76
    0x8041a0740882801c44003500c00c2d260190740880c0584041080394904c40f0200000740d5020034004c80100e00201c00281c0e4001e00b2420203481703a40c0000103002c0340039146004540e10820100d088030929400e000100c0c80e0302007000074003c022809061240c0d00d504505112021903130791810b0f90701c6902c00304030781301141c1d03440015501040f02e06200303252a52507503d4203001404403980c1d040701080c107080400050005680103103208880030f8a960b1100e154181485486000800440c3d0b04510204101821400e198004545c0035000e41f038003000f1200040514001a881a4060b800140304c60903090b850749428800d550f00050000c0e1144c030300c4001c0390006001d602c0b0081c400e42100800c00220015500c0c0d0301d08540c102e07600380c0d408440c0340a01e04942c2d0304e001000e07900680004e01d080b40105455002e803203004092507031901c03105000950315400301c0700c40c0d000001c06000c2003125400c24880781e800340007401029a680c5060254503940d15801d00da014464105244204d08004081018241001c0c2d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 258673093 1250 258671843 258671857
    0x4021b010903020f160e0c0c03120402040516140a0509030607050901020105010b04050d031d041d010605030703021f02070f060c06050604052205072c0c0a0e0906130e011a03030f 78
    0x141001c847d0b0345030500e060b0540a46a8068140d000018840c04401e405001d9240b0030b5208131400c0050781ca42c0842074880424552511010510000842c4005403d58015281c100072a14010f40742c10b8609020038140b500c16166480810301c0820860425038080c00741c0c902409580c0b0f0366600300ae10f03150018600140c000000b60611214540038203441410f0540704240d41c0015200388506034610103000981074503034404000e69441c1000104d881e02d40842c0c0a000c0b0787e001041d0111860913101c0c031204410254180e076096218600d40050140045003664000704415107a0440940c1d15060410907950010800d9100314603080400c00e00b5001c0e01484a090003d00302608850b204502c0d00c1391400d04d064110704010806100a005205034074014400307032021200030002d85840e0070040040500031288110302003030344000d0901480c24400640c0d41e00120042c00d0146070280e045242e02260400303107000d0f0a03a510789080d00c0700c802009014444ca40d1080d0010f601d0001504101559401290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 258674343 1250 258673093 258673109
    0x607020f01050703031506090302011706010203030708130213020a081807170f0106080d020d140318010b090403030f06060801030b0a0e0f070f060905041503030e04021b010903020f16 80
    0x300f406000d06210394010480030300060980c0310a940c554001405000740c0784070132800140b804885144c002d45400017a030059506800a41c1503407a0050701795080c5000604c601c1609103103c2100e000f50780c460010f070000702401d181c0143d4880b0540b0b801402c5100080046044d0302901000e54000140061a482218140401b640c0080707405512941017581d54284444158280400450050804900c500b081c050315000c0341c002c83c0d10030310181ca204007e5000300b00e0ba100213100181648084003001c9800080e20000018400060000100c0002d425603040c2c0c0007030741c0d91001103400d160601c254406407005080c104055851a61490070140e001001c40c0a555160604680c12030010000c0903140c1e00048113031154191030740c810010504881c4a240f0000d0704800c1c00042c28103052182c0008150b00414100342e803410343d00c003511f201e081c0c00c80c0c80d900180d0800c251000a158190542c5999051200100c1c25503850b04000b490444903642040440d0419250322540c0f94806d401c0704100c030821 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 258675593 1250 258674343 258674347
    0xf07030e030c06070e030102120c040f080f1b130213080705010c080906070303061d0907060c0201021b01140706060924061b060f050a0f200f0d0e100b0607020f0105 72
    0x85c000701c3c0c0a07010b0f007410b51100d00003a10034030440443c2c5001410031303a604690071104951340c41544503520704246500104d01d40003595002125010f500394200590030117004003140d103540041d003408907407200080c4031780b1301c507665001e221101d004c1c0303e0710b0001c09003481c00c0501405c09441d400401e200b6070114522540d0b0004200040500030741040e402001c003e4400001c0304500c00c9a18410380084030002920700548102240031f40c0142c800d146c07103907010b900602100c0b00031700400011424904815041c400020407002c01c141c0010001e00e88207228103008120b440c43c1000050940728a9050a880055000b02c0010048801c000c0031044411614010405410345041c460900e200c402d00a03103c6810000a80e440740c0305600918003420181d60100480540202da40040b140611240860203c1d600a00c0c46644840b001400e50511000e001c2450401600310300011a030116039101c20540004002907940340c610710403c1c41c1000d040c0e980c6490309020f82c0c002003400402005183c148900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 258676843 1250 258675593 258675617
    0x705010603050303040b0403020106410312070308090c06070b100b120103110901060f1d06120615071208070c0501142d0a0b01050706050f07030e030c0607 68
    0x109410050080d500700064a542c3c1c1030608069030350510441d415000341d0f0074424005010a61a1825005007030800105c0f1806104910400321650400d1662410750003540c2550485607818400709503a500c81030116030b03503a005441c0c0500171f0100203041000300c0d08645142007142d100c4208036074005600031f01548541d90b0b080f01010560306550060500e522020680720f00501d0000c139110305036030041c0040501100480704110040c03c09006a2000620080c201768000d4010145021010306030941400703414600310100ea20354100e204850b04000c000420702580c0e0070f1412620015a540e190824030300300326900c8030303049080c0d03c810410820802100164881c1d1054020254540e0f22a000740000441144d491007024001c5d41e21459030000004a8014540950604024000000c2c00c00900d40d441c4400a002441d440c0386150500a080100c0c10015000b0b12402e40f141d0001c002e8030026040c420002000c854540c0c846d442c141c0d004004104a101d000a06c10364846c140c2d1a00b00d203030b544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 258678093 1250 258676843 258676853
    0x121416030b0a300c05120c101b02090903072f090a0b0d120f051c0b060c0304090c0f0504030201080a0908090d05010608010c0309020d0327080c1002010501050102100207 74
    0x1007924a0f58050110040e0340c481000885014042121403c0707030112030f14a0b11510164442d40c046d20f10650021924008406441c0104421140c00c5c1c4014210411700111760086400d5001c01c0381c3d00c4849030130020b0040104030300784501c0e041140b00311160032661800b4411050450180142e281e110b505950000f5088807050342140d801120040c0c540c00c0314045520b0b1420740303170242540040108954a0110078000d100c0c1066504140803c41e041c102c00701e0404010008000031080c041e00f00740100485100006c003000200002c0c58007080008030398400c06030003030420103119039080411200304401c02c00750f81d1054415400c0f41c042c1d040010441d0780b03441c0944192140b5503601d500036004003507500c144030b410341c00385003100c00c540e0080c000441050310807402c83d0030350f001c000e60000d2500601c3d404648039201c80541030908501e484280c00c5601c10205500803d03a202c0d044650104400346403c0c10702c49060405000300380000e020075414103002030345a0000000300000e40f60301280c19002d1013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 258679343 1250 258678093 258678149
    0x1030308092a1503060f06030a02070f050a030206090d050d0209010315061125180b0a090608100903080117070506030c120906041110121416030b0a 65
    0x100004200300d410008454548182c424010a491240500407901006000c51204880c8074100051014000b403d007142044403907040500201d07115a820310840c070005001c40c00b091f01c1c090040c0001c14007000586402403805500400c00500d54100405681c0385a403c1000da039040359003080d000d40c460443e0310040b4020a1240d07041209a0b00104002500d1b07504058800e403090000c6003940d43c8030811541031a0319030208801500e9107404040c040103c000c240702030003054a0b02c1000400e510081c40c00144100311a9086811010307a039000c1000811030030409800b10040d0340000b440300c01d00d10303140641031100500c10641803240f080708000910321700344903000c0500002000943c4a040c2800e901e20507070003061451a4044104011451007600014902d2017a0350180280d2410041e00051120740c96031b4803582000d10035246010b0b216134902d4007a503182031407000e05480b05417a01d180003c1d0583c15040841042c545081403805140c0c88485078001942c410150f24100d1603035560040d8540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 258680593 1250 258679343 258679363
    0x4030804020f030d0908010b09010b070602070206070b040b160f0c0b1302150c0f1207060c03110a02011a010c051504140f01090515010b0307030e0102091003052d0103030809 76
    0x18010140040c0e25103070880c0016083c6c0d03031150002c016801c0c21005000c0e0982082c05907c0c141c000a0000c980043c06607001809040d101801c05403d02020b96990440c014094070202e03221901c4a007041906034810100c030701311010b0380c5000c641c46c051540380a84481090000a41031180351700024040d820115801001380b60b01070b00c07402000841070000c01c001d0b0440420416580182417000f52000c00000c2c202c40250541f455140ca411615074030b0100422280750384405050300d805074030f151405040081c1a40035000c0d00040f80c121380c030013030b00b06034202800303203a50501100c200c0d0200442c80c0052846014141945162442e48850030211081e03018242c40103498801c0c0c1001524400c0306400c0204001e100d075084407255100c601440c41440000d008490310f04900b400010a0b06100343c000701c1244103d0f40005103001c01e000301145202c0960106c20f4042a2207200f4022511205520410052401070200d003240d1007686032412016010301c4044c00300160003000c030714000340c240294060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 258681843 1250 258680593 258680599
    0x190f08190e0f060f0705090114250305220b0f030a110a090f080a1104090c03020405010f05090c0403050a0212100507080a0c02060c0406141215030706021504030804020f 74
    0x4010100c02e1680d599032007180d03451302000e2201c01042607140900165108640141c564901030080d002c0c901200307400000924003540328400d00f055210307907040b15000c41c2b54080c1d580c1c255a00464624010680e0340840c4170940d50441d20400c12540621006031a003094020880d6540c81d21040076001c040d20801c00d0041e5039540001e4010541c1d070b000b0452208503080c0c01080d80f84943d6807046d180d203901c00180d020b03090300810b1010102614103984951002c51240e40444040f42d03d035000320f8200d801c241c1140035a190740300821f010f01d1070a003901c15808040c818985180c070342141c3e21240c03550020342009005440012540c0903e80040c0281112400c5c5414200b25518100e000107041030000d17941591101e01c2d03c2e10644507540b000c904a0b209100bc0c0d00300360300d0149840c2084450040c038405d40c054114040c08801d110002d500e0351180070380c2140c0c0e0502d031a4540038041606200b0154088000d660016042002d204000d001030b690040d09410b2002c0320b541e40b40007080c002c03083e015055074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 258683093 1250 258681843 258681853
    0xd0b0a030c0f0501020607020313030f0203030c1e2506080606071704170a0506220b010f08070e3709030c051c02030d050c0c030a05190f08190e 63
    0x500d41d220701040b40840300c00345d007120f020382c8500109a03103074450140d1021950921400074400308039208444030314680301070216850101240911424022250b4000301000440e9000502000080142084c1d10499440c45405403044c0d9a200300944d8042c8140c0c001d00c600c006c00102e181c0d403440207640e0810340020406400b8180302a049a81d0342c0203009040c1200300e0036111a0065200140c0b0b0150658084000d201d40e44a0801c2440000451607075191210302c0c00034458001001e0201c03860080040040201c412401e0054480c1069440d170041c00204106108200718041c00003240806443c00c10b9098020304044000c00400c1340340340c20342101c49410070300b8040405030310209415001d80a441558018810071401b03903403810f405241100107034010b0082000801155001c0c54115860102091820303650350903090650304445584404180c0109a213041d85040301b21103501d0320031529080301d1b10907054002419842002d04003017076030b00303d011a810f05403d140e44403601c4058940103d031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 258684343 1250 258683093 258683099
    0x7080105181602071a040303080109020f03060f2d1005031006230313020f10051b070317130806010b0406030e0f161e060e0d050118060614150d0b0a030c 67
    0xf00c50f86d800340c4000c4001550400002a045041c1d109481108030540d1105c0e182d0744900003080360780041d82103d40e03404554110b125000b140303034214480788080c1d00c298520508400d20200010001862502c0090040420804c818040030340a0750040c1c2d1110b007000900b250b904c0a010441a0aa0017918181d01e0f0000a0140481c91030340d81d00070483c401c9450131030301c1d42003c05000b0306803c208140000324006001003050070880c0c84454018041120885000340d50320b841e5001040303407a002005030010001054500d800b0100746200150201200502680d458015810300d80e21403445201c04043e0b84a800c0302d0011070910844000d01508800c94103419004c200c1144003050360702c00e5444115910104d545142e06c50a084802c480706516891600c0007581e0a0008114080d8404c6030345540c0c0f6840d00101d0721400d00d102c0e14040c007401d1f001038a00d081962212951542990313a80c801c4203c001e420b650400900c0c01c50b00044c0500c64046900c10704040880c0d51401c05403c000c15031080a9008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 258685593 1250 258684343 258684389
    0x9090406140a06240309020a0303170a06051507080c01060803040510030b0f010c080c06090303040c050f030c060f0c03030a0f0b06130308070201090504050a050708010518160207 78
    0x4820805036203459908162144419801190300c20720419000400c2c4c80003400c0070f101d03072040180c10307000c03282000b0031000d6180d8005081074523950011000300e50750094220005007c803072100c1d0321014940e4204215402e007000920980400b054400d18420001007540412a03001d080d07c46d00600980240003032615910650344a80040c003500c1d01402a000000d9940c520a0080844640001d0058400a0341c814011102c3d40308210b419201ca000030030540c0d109081c00c0201501c10f03641000a1501c0713003020701d0892400780135580507922490001c90036088554012800314850442201c90940e5a600085200002d0060020111803408040304001700c1e41401c0c1c200c59001b40e8040000c0041086900411189005841c00700d040040c03010824400140c4103c0140040790050401c030300d100340d4580005082d50022510b0004c1d00d07440d0400d001c0c996801021882c0074083c02c0f1102c0c510562070041480c0942c0c2c0043c07005280c004510043d07214580240524030260250a00600c0004820225 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 258686843 1250 258685593 258685601
    0x1c020d0905010e0f060a1515020c10030b0a0f08031204020f0307030f0b0f0c0301031527021f020307031206030c0f080f01091106070201090519090f0e150c09090406 72
    0x860722160155100040d4486601c2c4203031f202c941c9181c540403181c2c508002c150010310329144800c4065102c1d466038030490350b64100700c1f2600441e01c0e0358041801080318060040e0110568021081485c1603842480b2001000c000c1c2e601c0c4a050301120006507031903000142300e5686200210342c250052510100a1060601050400d6405400c03041030b61b4071051000b18090b02c0882c0c603645490b00c1030005200182808c1144a400c090b0003030302140c80800d5140c1d1040c0c5e40c00c00d44045006040d40080318046043c003810104080c00e50b10003a0041c4805040041e4a0b8030807140003e0400401c1e2552501c0800154440c5000d1a042120000980c1d01c03002c00f28000350050007030140780d1080320781e90503000105014201c400c540c003403014030344110680c1c180540c42d00094812814844250404105078a074000100031101c11800f65507144c504d01103840b0201d40209051444841c00c1001c070b800a18000280961400c0004c1840e1400c1e03030f20003403503005034025240c00680c0002c0640070700c020300c291508 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 258688093 1250 258686843 258686863
    0x2040e07081203130b07030e030d09020102010f11030601180905180601080c010c060c1b03180504021204020d020d080a050a030506010c150f06120f050c061c020d0905010e 75
    0x204072211001c0c107a8035010280801ca030040003901c02d03504c180000880f0003440e540c02c6680f03410089407520848241508503003100180c8003016540b84052001e540e82400b6090030f03500700ca10100403501000d1141c61951000500050500842c10081004851903040810041c07000c00800c02c80b6090010850f501c022461034a06030300d110b44000401c0401000c00e4843c45d07448161281080c0ea940c80d6102c80181c03000410100034880c89410320740400000041c0040300744d21a565402015000d1020344128400507048240101e205000380c0071500c1814070900d81140e0100c656442d1312616100184903140028001021040e01180c0c005050750440040d001602003614148515529600110b44c00906580054241c034654000081c480740190301095144201c9000031400589650343c4100380d0b0030400048994039002c00a10003400401d001041d0000300c211034903071410382411003500002c204041038840240c0d000a001da0071242e0742d40481d0400d40d1001c02442444142c00100b03846e840984 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 258689343 1250 258688093 258688109
    0x10603110a21030c02040b280602030a080112050c03120d0b010807020c0d060b0d031d030106050a15051b031903110726030c0a090909080316030902040e07 68
    0x4560006a8401d030862805814100030306a0b00070f8030116032030048404180d803c130765512941c6111391120303030303000d82c1000c13003d081c010040445030155860301c40c00b5400802150014008440f035654010f80060441e030200789c80e240c4448482c103040d03040c8a0ba1081040c0d05104160030010017800000241210242d41c7c5010000e4806100064614030012150200141c00c1902e02d1109851f0158500e40d81d64001c0400052680c00d420101d91045032034042035011802c0c01205200041c54035540200c0504194000c1c050700c0e1034600884e0f0050b503180144154415080480e8800743c0c801d009a509240810181c9401031109041041d145d0703201c08843c085200300c42400040303150103030091088951240300b40390b1900b6500d460b40c0341b0400d2003078a091502d03030354241111002400c01c0003650003484980055a0b07500007902c4090b000d03200f10350000910505000d4508041050902a80d5208a07140c00c0c07004414402d035421001464103100096019150502c90001c181000031070b40c00b920144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 258690593 1250 258689343 258689359
    0x50114130e100608071b150216020f0a12080a030e01062309040c090c0507061a09070c0203030406030e0a0c030602040515070209150d0b01030b100e070807140c01060311 74
    0x20b1008883c844c0702113500380c0103e441483d04c030b40c1641080005404560080e1080c0c2c1008804003014010b0ba804a040f2202d8140c07507401c07450a618012030b100d40e0b0000200c600000a03031400741c044140e0300200d400900303003040c0494030322415400b80d00102081305201707000300800d80c1c9440142d07019084200c00844100c460031040201d80c2081c44215004a07000104913290b5890040c1038005031080c0d0799030404001c000d10080340000c18501561510340c0510b80809080301070381080c445c20b548000c0620702007144160b40800503072404011039080e40c506280109850a01e00002403405900520040540780c0c800c0000050010950103030003642e400b2180c0c120284072003c1c5060740c50007402c034007952104c208408200700d9624401000007911000c0d158000c0c0d071420b601e03078882d0080d090b801034507410300300020000d400d44035904081c01b41104001214203820001030080500b00c0040030007081c403c4400c24100c3c62900901902c0000b5186002400450f031203150000d4070146200000d40a4204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 258691843 1250 258690593 258690599
    0x70c0516060f020d0804080906040503010203011721090906010306030209040b1506130e100b07120305010e0c03130516030311060601020a0314030402010c0f03032301050307050114130e10 82
    0xc00301d4521610340c4e943da11131a15840d241c54040280c0c1c04000c065a02080400c000940c2d51401e0000e5402041c040d90b03002800c6800203a0785003410f11403200d42440c0001c0c1111080d00c1602102a698211021748190391302da500c0400680040c1201d03040a58400b0340c8030204000c020100303820340c0c8915103501ca2009000c44031024045d407030040740544007910403200000d00c00380c17034884046940300c5501c02220303c0b020742d5400c2082180d4050710040c0c0c0c05410085d0410304958241c09820700502e641a2010300c80e18144140001c0750001414590f103102d8100c19013000e0010400c1803036000000314a2030f050b006c0d500d01d006040c22440305d00c40911801003c0011f401580046401d000f8180c00d51242548400c0d5400711682c01e0340020700c101d062010310005100403a44840c45c1c540c2c0740c1c1c03280d2800281252020300110704002116040010011020010b018580f0f02249150440350207081082c100c0000344118800c0d07000315101406204400030300001d200b02c20742c61203402150481d0310007100703d803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 258693093 1250 258691843 258691847
    0x51509191b0e011809051006060c06050f061c0f1b0806010e010510050c010e071203020c090603031602010e04020316090909030801170a0b010b031005060301050d03030203070c0516060f 81
    0x8401d1240500782d03018000304440103996500140c00c00b86c4508256028122603d1000c000c8440030b81040001031000194002007024610a25800c5060209000c100e850184002940001c00c2c0c0c01e803912403c400b4524001700114841425030f0b06a021890004070a01889a003c80a6080c0b10ba000503100b09000080e8015140303000314181d90010f04020704640250605498590001c0b880c01c4481d903039151f4004072910f0a010b00c1014001c104900141c0c2e49945c10024071740603024a04900c588110010b000081d6000011581c84600c00480b40040c05010700050350b1703501c0044078071500140000b081020050031149007000d0706e070b195122642d24030b0702d41c0c00b40070459031031000003004114044014004402c280e00fa40c030310522600704039001001c1c00d5543e860068801c0c4d218030707090040030003400f00344904044008051301e410384d02a411036240c0800200a104050750250606500001051719244941d104c9403070150000115810b0b01d18021030701d580410350740702c0d400028901c00b4410710024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 258694343 1250 258693093 258693119
    0x10e040915110c0a030c21020307140d0c03030c030212091005160c02090c0904150f0909050309040b0a1d040302120315091f0f05030712051509191b 65
    0x81e0103c00200350901090b6016101c3c5943e036401070781c000c5130a01580101d07401074031084d56141440d0703020b036031107001030314240c816905d40c3e10040c0b601d03030400307400102c0c541c0d44010403400070b41e09482c000c1040052690241d00a1048234050000c2454060410010f00c00c0001c954000442c1c035a010415559084802d1248100d1a044140041c00c464400300140c9400d8855a40001e0390350501460055400d0006084510800611030301005d8140100264070740280241c000300a48001889200615505c282d1a40300f0304880030712a40d9030b01e00c003252645690030307488042d110a0b14484120001d40300310509c250000c035012001880386681800d86071111174103aa00481c14041d031030900c46111010801d10050091001039001040c0000d85100300300700c4070301c1e0f009000c0a807019000c5400c050900d0b040590a400c490b00c440314001c242d100140d400603e040c03d14012120356942074445000c9a0705000004030300d0507000104c0045081480407980c0400030440080155444256860050700d17102 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 258695593 1250 258694343 258694357
    0x501020307150507030f0920030606030706180503031303050d050403111215070c020108100806010b0304080f0403060f050a060501020d11070815010303020708060f0a0b010e04091511 80
    0x400c1d0000b1045000041c0d40d044030381c0010311420007048a9802c0f07191413045640d000d00a685280056440414107000a0100c07801c42100f6400742145280010100c2d40d107105500c102400c1110402211525031a0a43c5000143c0401801e4a40d078200a40f000404091140001ea8603070155000004c0f03182c0c0140c0480f011070390f0100c0714042c948411020000c240b05a25580c1c201401400d425014081e901d84049200310103e0321071010900450000409a101c010030284426003c41d405000e50032000424074110b81c540c00d8200d90f00c0d615850040414015021003143c41c01c80403030007104000d400c0d004140707908135401040049a0ba0070485d10281c82e85440b0b4940903811101a420119200f040d0b400400941e007002c0f1071003103a40e0344c3c00e2454440000c034140f50b1180744a0060041550520003140240718800050a05003415216808aa9000303058050b09603501c003594070099000d112642001d0400400c1041404418100440744001c0190003094031449c000c1e600c1a010340c0744047e6203030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 258696843 1250 258695593 258695603
    0x6021f020703020a0611070b0a0515010e0f04110c1006050f22050606040b0f031602030a1d0111060906250e0411090a0305010921020303060904060f180506010501020307 74
    0x9401d0304c580710000100512042040e8a040c100300c40400f050300303e07071200c0c05122411400200d40c54a6001c260b0810007100e00b450400c42140b0070340d1810b0381c80c05846074020008075000146440310700040242c9205401011a250143c041030707900c220040d503c0841103550950350040744a00300010000c040c0700034003500c80109044610880344080d660300166010402a0803185070645808a400e1150080b0b480f259040c0c000100300000c0c1980ba0f0620390f101c0c0d0550000b5030801d40148005490b8426510001d8804425041c0c914050b82c4620f081910144814050720304a081c000310f10780d29903e0448181ca440142008520304c01840051006146001607036081c80004036182004083e05c580e003c1000c4a0b02d007030100710950f955040c11000150311540002840709150701d00307400050844856034203456407002d61512000d0700802281d40c0900300301c504030500da0341e42c60b10100500003241c0640007145030801c0320601d001024100902d00d8054012642c00e80e070b0752001260307203100e002c0c4001c3c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 258698093 1250 258696843 258696853
    0x10c02090703050c040803070b010305011109150705120c060403020d090f060e04020d2c0610051309060c020f06010905090d0c0503070f061a0a08190204140106021f02070302 76
    0x90507074401d62102c0d4010345060b400e50f1400c0da031040942d18507000a482074541e800120010800c11600348038a00c40c01c2c50700e17034034941854201c4000500082c043c5201e000d113804001070680820800380145140d0b54407a0f01284d072a0310300b80c0131803a0703500c2d401c0380e007140907221f1021500000c0b8001c0d1000000c4586501c0207140141c18544100c0d000c44580440720f030086d40a20000c9040d0040e4011208421100c0c0c1302e80c198403980030040d0781c50541c900134880c1c10382c00c00c00501110340a074015400c2601d500f13841d4140c1d01048000c8140040441080152a491030001120f03040b0354080f0700c0201112284080381d0540c1d8840c08281d081350002d441c00c84490f80000e20a010180c000c000c84090a4012000d8030b0612a4031388500603c000e4a070000c540c900d0b51400b1a203a0800c462444a285080076101202800e0804a5040d03541000424020401140505110465541d07401015450140d41c0e030840c800e5a488501a5943d08956200f40041e40d0021090500021f03038400c0c3d0f03004540640c0105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 258699343 1250 258698093 258698101
    0xb0f030706030c140705061603020403050316150e0303010515090901140111010609020d060801090b0105040509010b041803020613052d030a0903020405060f0a170102041203030b03010506010c0209 86
    0x140040079003241c00000e01808005011136414100c010f4441303580a03e024110901d061082c050100c4c0c9001012014148140701c2800881c40002c1625407030300354042d92012140d6141089008004c107084c071502c4042c00d201c010001d412000c4040d42c12554162211a03000d005540c01c01d4040c011104040d410100305401040701504003180552050018100350050708250400c9a080d90444d4001c81e0655800040325400d901701c0303128060041c40d81c0c0300204034802255503400024078040c49100d10885c6c440010540001003980700d0600c450004200b00030410b1f4007050455455a0840b00390094011a0300140c06812860005080b072540300021707140941290340240e0030103010b004103400c55804400a810702640070002000003142c192204802146140704100960f00010801c82c002c0104d00c804000c5911118503440079155503154502480c490102380c0380c02409141d000c0c0d0700751744985800f101456019400016a050250001d00c900c4c2c0c3c03084015114640c01281c02500000454002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 258700593 1250 258699343 258699347
    0xf09090a09150506090132130204060206180601060c0f0503090901080c041109030a150e030406080a1103040b040308070c0c060215150102030f13030602040b0d0b0f030706 75
    0x41035120101010001d034810081d00c0324480e4400c152148401290380d4001e001c12850080e0000e8010043d84521101c0e4075016084040000d202c08600d00d0b01c540210300305407080c3d460506000d0000e030512011911580d41d10345c020b5446000fa1840b8444042c8841d0900c00c001000c074807581aa081c0351104944a41c9a99905c0401081041e003500e090200380041240c541d81c2c0da0320f840c0205140d400070942e00c3c2e034081c200f00807110304404802e0341400404c0b80850329180440c0342c1c60865000031807040003000342e1043c41e01800d04d001d500e0225000014001c01c4040d0040d6443e4080c42c41307000304020000304071811038500e210588001d44104048800200001d00c14081254000c03c5c40c035081c0010800c998845516020030b82207030000d0f800c0410500e103078089420005a000c81c040c891400e22094550011751a07100358550306085030000100d103414a240300401000940d803082d4115640c99842451800c81d0304102c0607605018244450341860345416007844451210040c0681040b620b00103007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 258701843 1250 258700593 258700609
    0x30406050f04050d0f03030513050c060a09090c0c120c0807080702040b040606020c010215040b040807080f0703020d0306090b0915030a060e071d0408040e150d110103050c0f09 77
    0x38404181008000104994a031321502c2034a20740b04000800d450081480c01a090305c41c000c15210080d071050702c615021034000030300f04841c40070640e18159140721140302101c4c208001d400601100c0e0612030001c0c0201d520802902c0950701400600800d425401341c00c03600124090700150074150244179007004034040d00c0003881e14500c0104005401014080440e09a400690040c0056000b1008070005542c040c854030f244034444907403030401460b040d80c80d05107540d805000544141c6020450804101a09045445100c440c108050325230074285030081d41c035030311700707a041001905000c4001030308040c60280302040c0c007000349141da00c3e50303c07541200e903502c85183c060780d494840c460440001c5602445a0b5403484a540c015250386400c1040b00c81110300080707861030301c003104003080002055120081d141036072040d80c0700016580310501021108514000c82950000844006130104800e000c1051001740c000c1c0c809012030307a40d10014a00764040c15001d100154010400c09203680707080f0318 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 258703093 1250 258701843 258701857
    0xe040b0a0905070207210515040302030403020a0f090c1106160909020f031806060105071214040902030403030506041b0e0a0b0c1509060c04090b0d0512040f0f05010203040605 77
    0x1201152940e903a010700309681d410b41c0e00b07602513001a0b1040c04420361018000d5980ca11101081200c180036555440d07491f17841814142c006460440414201442401110021a00280b1046240762111480c50700a04288101900b084c90100781044031800340c1c20b0b022060b51614080c100d641d82d12030380c1c4d000582c2614141802c00111003000300c0c07103071a01c1c800742955140b092011501c0349040300000c107108840c4a0302d2444e07a881081000416a8040d04481880380d000008075820b5080c207009548840561541505240d00401c0114081029034050340c4954001d50f424442c80d110b58041c8005c9600441141e0710001c4c0416403a0f440c540154030000b86140c0107030240f070500f95565802c0f9190307049010301e0481500a060041d00c400910309503940c100d8148006005035007418414000a407090348610380040d40c0b6031440700c042e03907103081c0751201c103a13000015110940303102288401c2c16400750081c404802103c12012842c0c048507000e040c1540e006800075841c00d410a41c0554650b00024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 258704343 1250 258703093 258703099
    0x31707020a180c0311250f08070b0405010b10050f0a090819290112060207060914011d0a080f04150306050a090203090d0806040b0306040b090601050d030e040b 70
    0x650000b4094622840e10b04035201c0241000840150050b03008041e00c450f4015100400703030a1020211040c5290745150800c580b008910003a4015481e10a241e0811502c2c0039200c3c007404180341341840344010301d4910951103440204600703241c8808004880509030440400504c01340120ba801e40c041d40000c140f030440c1c0e400c0201e0700a5171542e00c0c614021041909481008107030b140303881044660002e02d8407403c1600c030701031203d0404442400016805210f10b0b80440c0c0d980000a00b0300409504a441403500080241301c0d20000b42000585060b20210040c141d610308882000300f002c01c070010150458010010300489181a111032240390081e4a0450a10717004100001d1300032074074980e001c440b006235203010525500d080c007040000c02090740034000c03a5004004010140d10702040300c81c403880c050708004c2c003d03032600b001040061607425480c541611611041c4001d121038a4800ca2054400c00102e401aa032608203220f01c04220080040100f0440034010119140175044211486406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 258705593 1250 258704343 258704359
    0x120f13120810030c14040507022b0302040e070e03060c0a0507080d0e24010501050405060a030c051b0a171207031113060f08010506041508060a08030406110c090103170702 75
    0xc0d00d07113040d001a00c4c2d0100d44c018102c081d80b045141004c0c010a41c0c42503460001d0b200c01000c2c4a9405226961052103a110103202c60450610701e0003a415a40541304820321145285080100038190340074400400b44203114040016650803034610481d0307003400440d030740d0783c0c1006c900d80c1d244480c40d0045d0340802821521203000c907035600410001c2c404101101002002c80100035280414101410307040b003410003408000a20035500c8540407200c40d0000351800040800300400c00f120306005540c010700d04e0117070358506402d4900c0c0000301b098515011764650b603c410120301071201c0b1481480121950a0400700004441d00c0c0260b000b54250992880803518000600400005602c1140c01c58008500c01d1400c07128480d40c1715602c2e601504060381c000e4505418183e22100c410f448883d804100101e410000c1d1294445090180c01000c1000c2180d40381c0384c6500300038011260f0300d022540f4a20070389040741c40520700028414101d0386c00a140342c07440b0300055109140c90344401000d0340c001d008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 258706843 1250 258705593 258705599
    0x609031104091a070306050f0d02102a05010608010b310207030f110703020603160509060d0c080703051302040902120d030c0f080103080a03050402120102120f13120810 74
    0xf9500003081d40f07442152048685840350002e0b08a07100c40e004036000c2ea4404107140c2554407906802100d10360121109000004610011a8007140f0b618440c00d92070b80445001c1d0440b8080741c4c8444109220303500a0040319101e60001782202c1e62540610b900031211040310918101d4040b04400b46001c4a51000c0c0f02980f00704244142e03401084114000f40b1880f1144000650141c0b550700e44034a1b800150840030b00d5600021136078000905841100341d000b1811103001406001154801c440c050a040d444542d0065200000e12058105001040c1c80350700091500344a0300c252840781c5041d8550407180ea600d034091000074411f4820072070b00320080300c0d1040d000d40010000c0f202e0072100b0740d60100d0b2107440b082c4024117164440d400780701400316510040c800562403800350b85002d0003c3c41c0002e16542d079400021300840039990112195480041d81c1451a924900c0e4244a03120840e8400140d4503690740303000107100310080c040c04900e6101d68540d583c900c03807140300b5009244c494003503110b10b132 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 258708093 1250 258706843 258706853
    0xe1b0d021f050909010902070302340305060103060b010504031a04080f030f010f1a07061113030809030d110c10120c020a05010b0a0806070c050102070b070216090501060903110409 79
    0x1d108580c40400e01c00b1400b01d4883c41c082c00800d003d4071040c4e0040d03041440d130740c2e0007a6640f40d0081c440c0c00c1640c040303d80d1300c48400244a0780c03c5680d071810810701c216035403420469103e5101380070039160306040c030558140550143c000c4800b100e501803100a451081d0000328004103401404c100c442e41c10800c041c0551030b29560180d0300444c102009a4215450700383c942d281074443e584202d4070050340c3c1540c0101300ea08001555181d50b0800404144000181160039070b030f05c10740b61124082269440c0200c02d0002c036802070203540000b90111042031080003005d4444141503082010075600c480a2884241088040d100e6514014200114020090040c03d402c1d29100203540300168000c1d29000f06108090150200392441940c030b80710050b0800f070301b1648500d00185000240310380303a001003003000800d604a9180e290400340b04001820701a800a4440c0503410132041c2d44954010045218100d81c41110704880d40c03615920401d601c0c6a41d0038480400b5034448950040c2e4800380100424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 258709343 1250 258708093 258708139
    0xb04052512091b0f27062c1e151f1214040206070b1f03060c02151017160b03040201111908070203011b0207090e1b0d02 53
    0x261043d88481c07038003142d038682084070302d12583c45103a00008048003001068000252805800c0d04284c05516803184500b00801a0042d0f0384540000300354018400506946580e10320386106026420b821103444031103400d40c000b620103c101f000c3c1c04100d0003040001015410b049401000a4500401d104c20301107041036241c2901542c0011405000e50703031040307913450b108030007940d0301c401c551200606007500494054080c000c0010548010200400c44040720486003d80b040480e841200c5a40e0f01c82c40c101001e00f104000741005841114040d01b0003560b004c0070284214800d4100b40d003001c0c036001100c00140303040300c1210b981e4026025440020040b0210038009040c05040ea0365590074184001080f000c5800079201c001d4000200c4815800c2482c0c5503854450303000b0300465115002400000e0060002c0d440c0c444800619210302d0090540100303140c412a6011032080049034002c0100e207440307400c10f400703c44d0245e0300700ca48100b203413601c46280c0c1c0a44d8006028940700307190010601c4029 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 258710593 1250 258709343 258709361
    0x160b010303090801110f070b090a0c09020d0b180a0b0f03060a020316020307150c050405030f0d020f010e150405070f0e0a0b01050906030601111011030a0b04052512 72
    0x501c6002c020b00c0394034002d02410950890816556203841c0002d0304004a5020740b1100078201c4010300040f992814080000c0350760280c02c0340403e2207860b46d4282890080d0311103910021240e08058040c03105180c01d440011448500414015199584000d50703002400c40003200d0340d010440c00a44032207a103003006114407680a00e480141c0e28240005000b50100001c5640320031503001300540c07070000f50700c04100f1214010f00800462600d42215080d03032280241e03049075416114000540513003005c00120f404010806400351015940401141402c2e43c80d0300711015006d80c05001e0065103503040039400c5601c03502a00070390300ca10b03403508492000c030404c561000c8806040d031400e02000308028405c51054400908050b0324002c51500816094000107201c0340c10f102c03100c0601412090284002459050751038401c03c000500d1004140c01d0b42c20a48480218515012410107181042e1241902a502c001c00103500307451001070840071401c222052000f00700320441e2085d0f0041481c0184400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 258711843 1250 258710593 258710597
    0xc10060905090d050a03021602040216060c0503010f030f02030c031603050d030c12051009150306050c070b0103082101030c0501110105190b030307020d0602041d010515160b010303 79
    0xa051814444205591024100003080d401c0000300ca014070740c10004642c2c01480c1030601507150315401d0748080518100d40700c0690441c1c0002121140031240030000e603401c1d0b21441b01001a80c1044a0495060109010fa0700c00001c00301001d001003444001c0aa003050b200400f19030a807066400402d00f00009041c0f001043c081d1828203008101e01071003440e50401c4285010000d00c4002e1800034400da180e0341200c0d80c100c3d61800450070030012166502e014000c030003c10311542010644814000381d0390710040c0c401c41e00e0700d03001c284800e000b88209c5a4458018a50016590039500c2d1180e565005000000461500c02c0f449480c0c0d201013075801e4021400792484514885c60310b0005000401840900802a454182007007044c526804844902e90440c3c40001a150802d00c0131915520450601a5000b02d900502d142041710f19001001542c049107aa007943c1c4045111b40c1920703140130f029155100345481c0b00c03440d0112404000e4810340394280c145d031004c6007550b01d03241c510150030303041600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 258713093 1250 258711843 258711851
    0x1b02150712080402010903030e03100e07060e04090b0f070c0f03020c01120b09150d0503120114031c03020906070206030a09030207080703030e130209030d09030b101413020c10 77
    0x52140c048140701400c20766003001c100a2403d40d00082c000380d154000201400344070301502d0401c4d1800c00c243d0600c1d0b0b450396010407440030070f903110980c2d8640c28402d800005001c03011503081c60615024100c141c1c1d50041030147d45407901080e000001c4401800002001151036103100854881001c0142840c043e40140040100700d2000404c407640ca40e6130000c803035040080410064131088074055010b84405121040c0c0560140007030000994604041c2081c0b00c0862440010121051090304a820281e080001107180105164070b90704807107880b0f40c0150303401d2144107001340280c008200300040205528a03041869000400076002034900c503d1185e5103138095400c25030108512805494154001c010700d6203141d40090004030a010043c0c054a100c5030903004412482d01507980b6810000c09032200340000f10001070464007148030a07503910903c50046042912642aa101924100c04403e9070182440042c0301c0241418151940b42c0c2d5403c00020301000024020405c40c0040c208001c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 258714343 1250 258713093 258713107
    0x1052707030305340b0f01090501050603061302090d0c0e07020604030203160c090903050a170c0f09040902030703050d020706030b0a052e0c05010b0303040e19150b0403031704121b0215 81
    0x7251b003000c140c0044036403501e0b00340180810f035160b0013513039405001210b0000d192000c061040003c0d00525502c240c000320504002020401900204419107125060601d21a516900e04a03614101070782c010b03000d07030002c000c18942259a00d0b40000d80501441420fa0403c3c1c0d02c070803200443d4044141940021000305d0703e0718080340d0015000d00020107040c0f0009103420503142c5803025100308010b00c40c4d00c040000f2080129120341d000894926001015102d01d25980d0520a4441458800d160014000c0d00004101280203101d800d034114005008203642a04010500447d0441d400761000c020000c0c3ca50229001c01e1598450345501c80707642c5003040c2c00310500d442070950380095001803282d003050000740009052211a81e5102c00011510b40750a03842e108a031008010750070312034940f0305500c0e5012408440702002081128840e03a110001c00b049445d00d41100c0509407401807580d1121a034260700c151007010f10107107a014982e00780e1845ca10f560300140501c282804020501040881c0302 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 258715593 1250 258714343 258714361
    0x3012110604080a030516020d120902060f1b160e09011b0e030d03050903031f0905010303051801020a02010903060e120d060504060f06140a05040801052707030305340b 73
    0x40303400000f0394108012003191b40101030340b184d000045180811902603249104400550424218503401800050f5104030080700b5070a140e100f01c1400d0345601e0040d09030303101c90800044034a121528204180001070501400e0180905d02400c0300c0c41540d21221842c1d44018400071014004d40e0a445540c0b030080b1103001e140c00e0840800c20070050510300b5003001995600402140c1e4080c1400311503603801060300024a00382d07003042e007011078124a080004010550400000c082d503042d110148590000b10900490340e0706080c11000b800a02d0403032040001505507005000c500003c80251903001c41480403048040d0081000c601c1e1240c0c40c1d500801030f604152140201401c0071580710035181d810715070050030905260001401241000410203000740c440d405a901a2a4020080c405400c013000e50151100b4103441c0454983c284180d8003444420014468085a80c151600d03030502c107100d40058a5000c0400300103891508038030f00303144000c0440401040e034601c45d189401d101d007408000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 258716843 1250 258715593 258715601
    0x10501090801020c0601090f0e061609050a0b2b14010906092702060d021612020d17040f08040608090705010c0807110f0a0f3012110604080a03 63
    0x3041c801c691040000900010300411107506540a004021808140e40c1e034402c4010940000c44140c1405a1001e00035441c05020340d030701c0d0498090f911078155546550400001e80000d100da02c00c006001c00000120841108200c40b0014544041c0000e007200d031008081503802c2c4815450b10344030040d005206c61041e920442c2c004d0602402c7c10480689940125101c401e540003684101c21107400d01c1034115074500c4100c0d0408000c40c0710654442c241704c1410446071000c10301c01c540c0303902170214100b0311510000d14040558000e40e500e0560750000116403075054009081602d50040090246002c10016402003000300901d585410b09403508031007060800e0b102d40c01040c1008124941d4202054100013560741d0150010150000424548005000e0100e09620650480b00c55800040c2901d100301c42c201c100d40c0048000d0320032500b80b101c00c000111400806207005031140c160f201c0070404500102108243c641000c000141c45c0304103003841d014086808981070500042d00304c04042d81802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 258718093 1250 258716843 258716849
    0x2007140909010c08011a04030503130504141009020c0106080318030f0d020304060807200f0f0a080d0b06070512071e0515090307080f0a02010c1d0d03030905060f01050109 75
    0x7008000300d29500b08010032090041c4501c11102074146520020701701104103c40046078018112076440e0001170b0030503641015803041d2441540b9289507110000c0642203075130b126a0391801d865001e00c1c21300386820001d4100e80801c141943d03891801013244c82c2d0800040c1085110006443c064030400c400301031900d05064121101500690038601c01d003500041510255800f07820070807001e9440c02e20448101401401c6504202e03500210f040c07140c0804551a0f4840c0490790640c0c100030500110507a990b48001001072211a040041520b4115a41e00c1185099801071401e480c14030903880b591310300204185181c14018002910000b004043c051030290600f0341103d403002c0241c41e489040d00c90a80001d540080b0b1603400024100c1002441160340480e800038403e6210056080c0c0700f40d19810003892400951301c2c00c403103550034500a0311007101d0201c070345000020056023201800440b61101c08102d040c15182d90769000064802e000d4640700c1d10013003020946540c90080010b00300e0810354 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 258719343 1250 258718093 258718111
    0x10200f07110a0609141c0f0309060e03122d0904050f0106120c030605060c0708060609010305070915031709010206071b030309020f150c100b090720071409 68
    0x3140420205401413450022100214a1134041005010228001014003c42c10260100d1111084100801d80800c3c8075464000e42d81e8020301626114240ca40c20b144981030f2758164040c041c540700221000d80204180110b2101d04402014854000041c03540d82030042c11b81c21002203110a0300b400d061280e40e601c03c0303043c1106141b5500d4100064643c20f9041104241c0c681c850500305849130003078000700d00410b800b620240e52001c00c050720a0719241c80703014011090141c0030200d969441d01c0c140e003038140c98110380546401032034075155000070103280440c80174255a1810000100f9102d4041511f401580101ba07a6614070580c002800d01c50000c007241d06000c000070184024410504030403015950609000400304041e00004200c403071850b411507484203403482d400300c1d4154200c0c040c0400e400110b0407501d211020f0070328003041d40d9011032210b401c401540009000f90b4401ea450030704c000c01d5015440b95249004c8113903414024a1380150410342c00e4144c10825900f020b100441e03201c0282 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 258720593 1250 258719343 258719359
    0x8031903050103080a0e2209020906030d05160501150b04061101110301120c090f0b030628053303150c0706090203030c0303010e01030c06020f10200f0711 68
    0x684e01d20000f030043c40740c0b00c03040085104c40c0b4502e584455001000f051000036801c082c0250000b00c0a02401d03611000324016104c0f0800304030b090a0000b514048080313161151400c102502c0080903104040c580d00351082e41d22045d446507401c405105400140101d03042c4180d6613070130854054040c18455001c040346078944040c407014002038006903030550713518030300f2505c9000b40c070b00700a042c0c44030302e0304510391291421100354400c00c0b4a03400228414820b60a03544e940c1e940007a1b2410304d00040069080110350300d0707058000c005050b400142d00c4800c00c007004110081c6004141e107582c1c0705482c8058a0310702416401100e1030200074080100000c01c01d620840e11300703500740341518003c60000034491500d41500c2c0086543c18003e50300131445010403070351290b070754140c414501d50b020311040d24030b1500d440c03021030b9048c0301080e2070f0a0030324620010070350010b10b11203a900030320703d81c00c01c030300d81076090030004550b40c016034014092440d80311401d507110001802c0012040c1e84440c0350303a105400d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 258721843 1250 258720593 258720599
    0x60604051e0103060c02030f0f07051e0303060f12190606050402091509010e091006090626041407060513050402070c0e06060d020301060201091101050a020712051204080319030501 79
    0xa8101d09040d641e000c1808036124a1540042e840e60040d402c600c100301c2c0000ca2003003074200d40c010281c2502c0303018200310703203909803540064601c0c0d240510703580205420400019a9a05201002d848080400b411240c1035040c490080c038100302041c203512929107110000d4201f402001d02070040540b02c2141c0441c60518280d0003d18800210b0010012010001c145d87e04149e000d40018005000b010307210014915041c101e00720546a41d000d68030204401440100300b071441400e807a507003a4000c17220303952401921541c602c40b81600400c00c41d0402010000004400418000341d0001c0015880b21500c0e0074082000222800316504001d001e40d206001020100303249080720412503c0080703981101c1d49844010500c03504c984021f540340310740000300000707040d070381540280c0046c0d000e11210030403030792032034011515449502440d00050340401c20510416018812480400344140200c81208040084010103034105600500c0305030000b103024105109800705103001d10301646820460f645c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 258723093 1250 258721843 258721891
    0xa0b0717062223070f02121c0207170d020a1407020d17220504140105090109020903030c010905010603021507170912100606170c070f1b0806060405 65
    0x281d0300510619156100d82100b03c0d00c075446200e8030714405a1005242c034218102828a2000c20001e400620603403c032007880718451f2080d80e0001c020880c07202c103c144000d40907800380d001401c0c140c0c3c0008111070f4200d40c03102c0d460018103620411150140e2110942c02024042a55400f040b4072110300030044100140e540008070300c00c1d6540920081285007079445c0091560241001c450300500d180f040c41c101c182d8016800f0003c40d030040310180042541c1d1794042c0190301d002e00c501c50304003041a0040c0103401190b0081d10000c04054104d17030038081040740e00360940708001c0b015075241c0d41d40c1c2000d105500f40350401d166144607042100d442e061055840c01e1001d81e50b0f403200d19202c5004110400703143e950750f25080b1036506c00c104550941441c4005d4800400c030318407a0b2404070b50003145a41d104003244091500c039410024490f0f00309811030700c802d03d0044003854122004074a00c0038481e8030880e10344604c0050800d08000b4802490a041400304031600034010066800c070f240310100382030b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 258724343 1250 258723093 258723139
    0xa0207030e13381002120301060207030b0603030c0a02060f070812040c150e3006010608090c0a0e04022205271c18180b061204030305090a0b071706 65
    0x50b205132000d020380300306000201d080c40900300c503240c1c841c0703400400000d00035030001d0f480040d03e0003a56604625100c05003015034a100d03d800f2001507070040040400507240100c0640480001d556003189810480e41e5540d031294090781104140504d000144410b0050802e080ca01406601d00640200310708080040c0441c00e110105600c00c2d81c8400340e81000d600600f244c40c0181c95a02041d001544103404603a407241024000e0300000f5241c1800900b60000001e40c500794804041c051000260030320083d4165210020000d1340c208544440124004101d601c215041c00490b040001e101e040840c1303020189554001000341213200100300000022000c070b045400d1810504090041401d0a44250f03031204600240e000d4421440c40d00103180391014904985801107140104070340215a420030160340640c2c094501072404070400500003d000c0d6004640010303c080844104216950f9185010718045a1810014003242d807541c0d800c20325070007103a40010b41210684c000da00c03491140e10f580c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 258725593 1250 258724343 258724451
    0x3050f0706090b0f04090504050a110a0b0d051308070c0602071d180f010612020906040504030203030f0c0d020301090f18020306130f021203030f09060f0a0207030e13 73
    0xf0003002500583e8010340302c08540c020880c4040901c101c0c0307072900780251900e1650106403071001110390506024070340451400d0940300c03034400903418103800090b210020a03000700801c072104680c2c400c00340414007450141c1103192142c0446400c00c0c4c28444005d08102c05944000700170480b0400000e14a440c2040143d48011a075600d40c01e154480460700e858040c0c031070f081e028507501c1c0400c0450f070a0141040c42c16400c0c001c2d6282038450b07e5a80c240801c503130040b40d0240058200b84045641490400400380d0800030040b146414a0b504503461001c982c400e901c12143c1c1c0c0d50722102442254100e01440807560802c205103200c1390001d802282c0c8a810003410a19102024960354041000d0910381381403154016048089ea0150348410655036070059500c034803c80c80c80c41c00260081c10014100388200b040159801c829140c200d0380c0d10207900110802c40500c08208074901c0107440c5c101034031003812150800030942501d07410b05c40a0008007540000b094682d031800400d0b810000907c0030940c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 258726843 1250 258725593 258725609
    0x1103040c080d02030c1e0c121b060304021f090b1201050a0603090224040b030f060f0d0f0f0204110a1d0d0305040e0c070206070609031707121109030f030403050f070609 74
    0x8091b003810001070800504059155000128001c104078100d00020703403051031460b5012007175025044904104060100311802540095010601007555280c3e580d8013001090600745480c1d10b64a031986842280c100f001d46010505054004110614106100e60001e0600303003420001c44c641038002c113a030001030401503400540c4c060910581c24008600702d60040005200544e1207003001212401940c0d4140c441c0351007001c55041e070842c41e1518415440100c0c0d800701604503100d0080d6100311503070f00020340590740503584064440a00d8402c0c0f0080c26541d81556844201c07104960903030103400071070301501c3e004400300c0b680c107400203401804a8040e90300740c42c4004000d548004100f4480e00c11490300035005540420b801042103000e410112105102c1c0d00c1c1d590303c819262400c15500601160004000384444a450072031010b81d0b84008580070340700b0410b6240082100102c1d10340900401801c0311a0310024080041c0402480f984403520000009880d0f010700d03003031004052205d13a00804c00c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 258728093 1250 258726843 258726883
    0x30503040b063705040203010f0611120a020a030810180203040c050d0812091c0309050f060903130b0412030f02070e0403030e0d2a061103040c080d02030c 68
    0x34256a4034003107a800402c5040c1400004061120040c404092030b81e0000380e01004018003213840e18241c02030301c0c181d13014407981e14a440c1ca051402c407611080c02d00b680506008082400303940710810300080001e00500d070010890000c161800400c2e000f0014205580c1a4021300207002412a1103d914202c420b800030160b2292207a0621200d145400d03802564001d8044c0c0c3c00c2020020f9401c0a0035a109003100b0f008207580d45c01c10819118400e600914050b12180004258898003907840040414019002c0f00c00400f0003030078852826100740c42c24040c0354800728021080c001100844400360441c80c1e0042d040c00d06e880464901c400400307400a050080d552801c4034464400c120303c1009014a000b407043d98181400d000d80144202c034810002402104450448a0702a100c0040c1c54032024040220038903005003460341030135088001701c43c0c82c1e40300c500250380c20748024080d43c040d602910700c00440b24901058645018203404525040d034001740465001d0520100710741c80180b106488001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 258729343 1250 258728093 258728101
    0x140411150409270c0e0a02120a11090a030305041418060906150a0503190c2703020909030316080c0906030a0615030c090f0e06060c190501090201080c0403030503040b 73
    0x50b0034202d0380d050401d4079000d402000240318510f101d084c112880ca0031a1209501d40f12882003da1064060511140b820140410451141e60340850005100c1d061010b0401d40700b100003900300c0c4459401500002d6000c42e0501104200700c40e03002c2032031000c40340c0d0b81d103e40201c03e905600003802000188a1040407000654a0701e41184c0512141c6041003c02ea07a9081844058010340060310006e40300042003801c0d40825100d8030803840d6441c201d446510035207a8100c60b0f01c1d0668032807001c107030340f000c44d0000000068442460441c01900c3c6200615101d00d0840800d01c011710804158204000050061040e01a50b500444450b10390542c0d034950780b696004e214102800c1103030300c18410481100404042e169040e4807001d203640030b40c4c4e10640020f540d24082d02503160700740101128001c0201c04200540380060041101d100c80b00162135174850320345e02054a45030259001d0f1080d07516810781074115a07010310440d0748800601c1b6442e09243c11a2001401030100400003043e0003880c00c082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 258730593 1250 258729343 258729371
    0xe04080a0c050303040f0b010b0a17040302190b0a0b03031c020a0912031e0f02070506090f0901240f080c0702030a051e0c0a140105030c070204140411150409 69
    0x6070010941200440b5a241050b01d0132000c100c01401d425107041c40910004101444504121442880b0720b5407004401380785210003806102c009001201580b080c2062840f9039401214503401d4a400340d400d203c010728100203040140c030204046070744a900104521514800d000319001e4888540c0e00380180c5554445a040d1640601038000e0b440003030300e405402040590200c030480d031088401d007558a040212440540c1c0b0140310b0031011000d030700100d100380940d0a181018100c143c03001404280c6608501000c900601400c1e0010260914003651801da406d004501e520780c040101d02e001a00303400564401004000040c0c076044600070b00081920a558003045940c03040358000040e40d2202502d030080e1481100c0002c0c0a0045024440348002907148c0b1100d04400c0f02d080b014200039211000004403843d5100030b10464859800303122210250300c6a1060901c402d071142c0710700e4403508060900001c1048802c940621a180300000f860300b00700d000040c1c0e01120000b90b00071510036880d03214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 258731843 1250 258730593 258730607
    0x1e050109110f1602041a0f0f150a050d020f03160503010503070504090f0605160f0918020310090504050309130c0e100314160905030a050a150e010207030e09010f0e04080a 75
    0x7070f505c82d04100c0c2601403403002403c0309258540807281102d0400750b900c28080401941046070740d0181c00701d10075050407100300005000451603440c11170b01d0321400c01c0141e03089070007890f48084e400070b01200704110084111903108924685003440340c15503243c400081e0b5611854040c19006907110700c0744500304034590408030840380d400101440145002041000700754801c23251000050503400340c0d50b01d014003d0001405484000b4120216a0b08003c1c201000e90701c0685a11184005894001001c8460384035841c05244184040c56a85007804108500036200041e802402482d205130b280c4850b0308040741075036102082c2d0780f19402c906038500650041c1000c2da642c6000c411031a040001c5840804c01c240000f0b001600c94040990300c0c0c105042d03541b0003c0e00300070225448a41c0b40c50110300c010078078041c10120304e84003155403800c1c1e15090742640c0008070700300c01045660011040d40d140000d0440c2c00340842039100048d0a18003170040c0c1243c2c1010f0300c0030303045040c0040c0c15000b491084507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 258733093 1250 258731843 258731887
    0x120a0c0f08120313020a0305031602040b1507020d030c051501031704050d0303091e030905030d030b0d0602090409080c2a06070b060f0904080309190b01051207091e050109110f 77
    0x162500c0b12b98900264140300545003040707200e180341070b41d44921881c2c210b40d4416041ca5020803913051080e180d09219910003124415818003101000f0500002c00410035100d041c4840c150191641d45075280c0740718000c41e46004c42108031030501c0148030644407803480c80303129501032801085201c02400d000d11f0090b100d100254201c00915018001d15800518080440300141d08036607500c280094210b0407180350005150313120101d030b8420400302c1e283d034014107a0000014000901c0b40360950b11044507a210060064240e00080740070f144d151030324000f84020510841d02140058801c0000076924030415100801c42d410310f0003c42c0daa6103d40400f19148203000e40444241d044c80c2c00c002955820445036400c0500c41c540a00402095454450040d103a0200e50082d080c2d00341400c121b05104014a044101d1040d107000203521001800f8080000101c0040c000100028260201c19110143c001c6403800e41006c80701498045000d04480c0f07008034403514903445806d030002c102c02e80781c1044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 258734343 1250 258733093 258733103
    0xf0921110114280f1d0f0703031101060b030a0e060a1b050d1404062a0504030b060303070510020901020118050d050a120c0203090f1801060e120a0c0f08120313020a03 73
    0xb8032200e0080c03065a1010b14403052030f4002001103850120040d0b03503000034140c03914003900307c4034003000000d0081e038041003400c0a080010520326141e9218020a4004494841c02c26840d106c0400180301c0501800348c10102e10502442208031152800ca030044e00340c9541030420800081d00302c4500207a500c0528080703c0305107006030750b0900d4100000502013210740d1403158004050208403403884021a54124803450b10341c1c17400c061460b20b98518884004080c0358241c00308000302400100144244840a51036040050321610350700d000900711464684424290720381d150401c40410400640d04071a181c0300d1800a40e00d240039101140c030900354442c801c640604000303e9000254001c00036260740e450a031110000f042c2c02c10708120075980780c0c5010403a40b031004401882540d11442010542c0140a444e080035403c0401e0701c14a88042c071b45080d280040518030a0100400d03490082c8005e00950005100313511a030034402855100c040c2240340a0b010f100802401c40d00c0d40c00758800103503040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 258735593 1250 258734343 258734351
    0xf0405040f030e01020304030c080d0305010f060206070e1201020304031e0908030904020a2102031501030204050112050a270c08011413020a050604031109010504021c0f092111011428 80
    0x2c0400712f03905d04030f140c1c2e420b01003810000007282e602d100f81e03d6803080711110b038028981038560a109940c0300409403102031300440e00258001c120817003400254081c601c00d98072400340800303001d010084030030907441d41d00411400f0ba90400408800209940381054120340c0140d8800d801d04c0706403400f65009070410800e0b11955001422456030341e025500c00d102e20050301f42c03a81d0ba8003004604a104c1c5001d01d0380032903010110346940340c0155100e43c0e4003200c003800002e1861080d41035491104030040748191003aa4800c00c000400c901c8054040007040c050000744250440000c048562003001030041c5c0b020f034000882981555201c018800051a02400b40c581d02c070340302c3c1400700c00d4108400a16000b0b01003d030000406091620031100401e041d00d0401c1da118a607010343c000a01030413042000860340b990700780c002150603070699403610000460700c6040201c401c8000b500c000c1004041c010b142e4580074070316211803158882c055010540000d40f070b20450340550083c00b07961038400c1409490b03140c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 258736843 1250 258735593 258735599
    0x603060a05041806090f140a02150a0e03100e070e1e0903040510090302040b0109030803070e06040b0406050703080c07201810140312041a040306050403020105060f0405040f030e01020304030c 84
    0x106c0c0810121050041907000d28042c1c4501280360b072504500c0009401409001c0074003403400c14480500181056890301c200d952a15000003441c142000c1c003602230241d51011207400c03152040048030300500d1145d04c40700c01480c100e51000ca80008208840c1da8002c514400901141402d000300ca025000060140030307241044d0034010940c030694003040740a14070708040300c203056002c3c69008045a0b03000080302e1440e40e030030a003140c440e4000307500e640d0806010b00c00402c156136420050b00c081e00d2184c0d1a280c03100358070b0800401030f00010b4040416400b0030011000841c41108214100c0d4210325041d40c0607201c5000460a2801c0511040d07040d2500380c018090301d50814120f0744c08903040106040401d0f100c030020181c8a4241e108003688440c003c00c030820501010205080366040c0c00c0744601d0401d9070b80e403910815100110340490050f55507800708243d81c03a0803050380528a03001da07010031451800d56500c59a00a45240240a00410a0940d00350780e1081045602440c0d001c40d124101603a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 258738093 1250 258736843 258736853
    0x30313080c0d050403060e1f150b03040b1f03050c0405040305071b08010606030209060322051c0323040b1503070603140a0209010c0b04080f040605090109050603060a0504180609 78
    0x14042280d049040400300048404002184000a40c0210028966001022360800108140c041011300380040c0e0000084500c50100a140304501039412091a8a08144040c1060407844001c10380394104109c14404200c1c0060203060300b4078203450004141d00c1d9800d0685140c01141c0b00140f503251400e0041c110400000c40c07070303802c50351650001c0c08540e498100c140e083c0d0048158103600007030140002800c80080642c0304c0018120711089240e4814103840d254140941d11441c066a42002908540c102d641481113a003410340d0500080d07405548420381c40040c0c40013030b00192030f0100d9040814607c00101c101118800802000c6a4040769200c6000d8050310a00c41403030301c0014081c0005035580b015000300c500c5100140e644900300c2207a81e99a0f428000058000d4039400014481d04009001d0b91000700f001d801c99440c1c1d940c81c6c4070850b0004151035a1070b0013060045800b802440003640310312144000380ca00440c0d01144803003072000e01c2c41c070112580c18003403c0c540c24900040e050003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 258739343 1250 258738093 258738097
    0x150c050f0f091003060b070605190509070e0c040609030b0a1116110d08190c021806031903200a02030a0803041a07050d09081314130b03030313080c0d05 67
    0x2d4003654642e100000741c1d82c065003211031921a9004010081054800151003031b07110a80c0113110026042000340c46031081000c0303400459070a42e880d84040c5090000c1c500034080070358090301d0814200e14040c248035004043e00c40600c4000e08200d0301c0808580d041c1c08540240406090780c6010300c1e1141680350010304500291842680c002e0750341040708440f8102408103101c2941c11074941403511000a41008240078ae03d0114020407a41703062600040c0d1307414a810014140c1d00c244d084880c2480d0301018204080c0c08189480f00712036800d00c8000035084407844401000410403c440c40c41e001a4107820722070040700c000d500d401031104940c20007a43c80b000e5402607000714aa04000002c41c1c01c07040e00e0107415140b15000c240184688481d0b401640c00c10208544501402c40c1400303415001201140c103613400c441801d1807003140c800140d0420080c0c11350302145a61051201541701404240c51b4800a04090302000c10140c81c803051064010455034040c04180440c1d0041c110031500800503 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 258740593 1250 258739343 258739357
    0x609090a0e0f030a03060f1208030928030e042a18090f110f040b13031e02090601020a1109132001031802060d05060a0b0c0a0b01050d150c050f0f 64
    0x300c0d10f811000304118540f01e0840e410388e000e905c811902071001d91100c0050342c10007082c100481c03240184180c01034401c5003807903000c00303401800e52080500e02d01e00504030f085134042941c01249410148103003802c0480c2e405035003600d6076204001040a24a040f40c0f440b083c02d20554802400081c00103800b0003aa001c010140000c2c0010040030707815641c000440e20401d05004850f08061000b8088980c1c3d0000410312080340e0141580b8166607640d40700703401c85c400100000c510b90080350500c154209030203140c2e8407090900c080d044c0f0f40b22aa89901581d00a03010090142d000d40001650003090088000c0d612a004031250354417a00c0300c50343c0454000708040b040c2c00a8100b5555103101c0c4510b1441d543c2c19036009198a00f0a060035074840c0041c50002c01c00c0398442506400015034a00c0000200302489950000d40b10180c0c6906000100400691000b4041c0c0d0b4280008000328800301c841c1501e03405211400f04007642101c0013196580500980d0b080034a1000400800e1160004000c0c010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 258741843 1250 258740593 258740597
    0x30705030405180403080406020c0106090e0307031d0a06030513021f02100908030105040b03010b0a1e1403060f0a060f0f06020f16060309080c0102070606051306050609090a0e0f030a 80
    0x2819040d030074003140e00c3c481550000c010a090401040010703003103402801c0c0030014070000040680c1d4480045007500c4124054441642000500b00305040c0e2002c00740e00030030321a00c0a20a4007030b0703503404100d41030360381d110704810113a88402040150303140c1c081c03603604240c004100071640c2c1c0039201ea92240300348071000200903115401245280b0b004034010820500c0c0c10801d440e04603880c28003408050503104000d581d043d540c0e4840c0c41500d649412903034020381000301405003046003401c9800426205a0008242e0326080307404a50305690000740b240c1e0010512803418000d803540c03444c01025112076007200d800421802c1d00400c0d0740c40059007442c2110b1841c4c1c00c580443d0710b0114030984a1981c041ca144200c1e4500e0390030702c107840c0a9000303142041d11540ba2280f8080340f001c180d900b2038200507400c80d0401d45440c0104624940324140740c4000c40308072400c101451400780010654410311181ca80590a034070f00241b04103005034403062000300700300c0680e060140036440b41601c83d8010446240 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 258743093 1250 258741843 258741859
    0x4080406080f06010804030305130b07090503210301030f03090815061c0201020c2812050f0706121d0102181e0f120723040605010c020d0b060103020c030705030405 72
    0x14941258032420b01480f010b84640b02161103a880403000b4010060200b9001c20b1018240302c0040d24400c1080c0c4103008564802c08480d0502040604009003145008850500800c2c840807501580080340c0c1180c4e030129989003416920f18040c0c4042940380e0003948140a00c5030191070072412441040c2c40395070101d902070303000d5001d00b5000d0300e803844203d00030317006911044161010381080c3c818000d08003100030500074075034205c022a1160495a40250074842224200041009020010100c10302c05500c00f03840100e0034544010300c0d50303490840c0c01403071b00d80310301512030181e4680e014000e031001008000d40d5540b402154950100d4400c2c0c501b80d0080400e89504000c0403401100311801803c0104207031b507051a410100250407441d440b42e10700c2c50103211300000302d0460b61224401112001000786040c4080d034810001125100c1d0300407410f0041c0c1904100c01a9584110040f416900c4162842c4a0300c2e040012130017030240700e81008903880001034000500c9000000380c4201d03402101c90b41 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 258744343 1250 258743093 258743101
    0x3b03101e110d0e1006030c140306041214090a08160b090a090e0712050a03030510060f0c210302120907140915060301030606090f0e0d12140408040608 66
    0x14003100c1e0700800651204405114403468509550400f80d00256104110b844840c16504500d041754040d5104607842e98451600300451a0740c00078598042104a003c2e0001e89000e40740c000c414443c0c01027000400c500d04103004016603131501540c03855240517000000381520382071050358901c80c0203501c40641c5041d050001e4074001c141c040700c10204024100100907441c01c00380101400d0520a060b000d03015400000c90801902c501e156440d034000c41c0107100c03628150a0207070890700c01601d950400600507000303022150b0018885070444205140130528194203060445005172864071002d04080800c42030380c800c590503000340108501465501310161503003d2880e58a00c031512500150b08140521260b480c5881c40c6e2083c1e01501c52007102d0909200b03e00041c0c560352003604101d80455481d00244008261842074030740c122241c140411400b520080409d80c0c42070210b54000070081c071011146a0fa071041d07000079402c1c1900c400d0020b45410f00d460b000c60305030405c0c0104000266900005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 258745593 1250 258744343 258744401
    0x501020f010603050c1c210809011404110118090e0f060f1807030524071809110c0615040b010215010306020708040503030a0206010e073b0310 63
    0x540c04403135100c4000c000c014001d00a100351510003a0010484c00300712003010700400e000d8015154110202c0909001c5449000700241100402501705925a03252486580031000c80002e0590041d070003200580703942038820b004803580d115074120b07180d040b400144001800562900310300310441d4241d05803240b01104980813a80e070031701150748041c0c00021001142c001800c0060170031504a0240584442940343c0d1180d614052500c941c0c81e0020b4200c0c05a0902c0154003407240e80c0003c9240b1305940c040c10002c02d5801e658140380140c6604aa0b54032216071440c04000803120b2a11300003058034000c0c80d0042a907c8003003080c2088502a0f810050b0314206584080b4000341d01824080c440314080c2d00f9900d40000035000740f8011509807008100129869400f04054410801c00d070380200019030406840c03403002180a4840414803070441e80c01e0a80e840c0380c0c885040005001228034500d00c2c0e000e000e0240c00c1e041c1c00222078150050900306c045c00545c0d5042503401c0801c04042d8071400310302c2000c2d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 258746843 1250 258745593 258745601
    0x705030606040213210f031d0a0305060601080a0b0319210801060e06040b03040803090111031308070c0e07020303040b090c060d0c140f0702120c010206130305040902070c0501020f01 80
    0x221200e1182100804c1c003d01c96507406610840f0900d4501c060b42ca0f00e550790301c5006c110010820340108a600720742404404c016141c407014050181d43d0404124070750303603c8276035441020b02198188040d110004800c20801c0e8800312403804000c04450fa19807203845c11846841078410103036001c5910b102c5a0f4a054820701040004c6001e6035aa0000ca130300e05001142c110064090740307503010b041000005000300a103405140214001c034200c0e03589041001e235040c2151801b0b011031008400c1031040054112400d40d0501e10717550460141e503501d240b40d01e448113110b14240c000c0d016003d0a001444003c0d540000650310603485500b40c403180d40c80341c0700515134691000840c5644154100081c0313400078019040800d0b130803003500b000c034407110b0030710502007064100301204040494045221002c1d4600152a8540c0031650406008110b4078100000d4448000503d000c0d4614203d140240415205070105c034024141c1c00d100319100c124a11b080394a5401a104550040c421103450407c0c00c181842 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 258748093 1250 258746843 258746857
    0x1306050f1206040f05030d050a0e19150b060405090106080430111009081e040b09061b0109030c02011e080a1a043303200409080a0207050306060402 65
    0xb0035090741d5540e01c4d1080b158000808648078001448980f6064006000b402c3c0a514041c0000c01e40c000244085440c200000000b4008403519100071400701d2401c01a400325015452004a00406c10501181c4180700e0b5034405a0402c00d41c0c0000602958400902400b440c0b041207001041a2540d0343c9040203040c9044145012a54600b488403060044814482000002054807240300c45024107000302da14030441511054400580030044c490300d0780359102b0f2002d50f811858105401e0500000c0c03280106040e250142d400010800c01350041d00e901004030310391150090100300140c0c42c009003402208a000c078040350303c254030128800785505049100720010303611402c0d07560721240040301404480d00e1008002c1c18407414052103440f280501074030a03900400b01e84100180e030381c0f8103800c05144020b02010045120003400041c0c040450b160505402c3c02e910070501168100060007400101e500500c810b2000444204042c0c010070644126007045054074031a941e080140b000ba0312540f2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 258749343 1250 258748093 258748129
    0xe030601060807051804180b1b09190b0310030c0902031312031104080105010312080601171b0c0105100501031803081515040f05030d08040b06040b1306050f 69
    0x4001443c807807250024140690561044130504242480070808891440c0c44056900032001c9104043c00b103c0c1d038000c1d03000743c09111100018210300a14089078010000310343e00c2840070840003c99070020b40d0a6002078140060001e6682c2444000616206000d200407140c06030310400020300c41c0703118826244070784184410900c8045282e915085410800708096091503560010291401d5200700508050071010000084550440c01e2400f400c035010101541008104400c20850740d038407a04a507004080300040e0442512801d00c43c0810110020384045983d03400300308444a101c054200c60301403c211500e241c101b0342c0b560300440507642c41d400035a000758801060a40020f1050550742d40c803404e00320000301110904000511005c5113105c0b410b80c82c1ca0082003e0120095084042c030042800302c4c01443c159802600240c44003c1c0100080c0c420001d603c00a10302c0d4556405c0000e100c500140384240d00550260224020102e40c000c0350b00903105403030000114100307800c510418803508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 258750593 1250 258749343 258749357
    0xc2718200a030b07031a240c100f0204060e101b0302010b04090602120c030f010603020904090c080303070201061208090607021201020301032006180402030601030b130207030e03060106 81
    0x2140d0150254034205000a40081c0c072040000302103440c02c10424052955980c01003a101810f010000c00c0c80e0300b50307402c28031441c1000d0348080510980790b88a890348070561404c1c5e0725915032241640c20030400000c1c252180d8106480c5024540c000c1e8010310503500d0a85950421842c50414484860700c0b0b44044408105201b420502568400902c1d20301c00344039200109000700c1e1200810300f40c400304007080300e4040d0041841c40340c4109405901d58041801c1a0150171481c20310f460440001c010310a003414541d00103245100c9032217a810204d40640c0100c1c048a031709648000c3d05950b540203c4c0c440c030046d4680080820607010030300c1110100c0ea044558181441d044608200a80d80002000c03a03101f01a1044441050b00c207001540c02517014501405520b454800c04810070007102c45d00f0752103050b00304042404030141d4813032240e103a03400f41d40050301c1c1d41d204001a0000c207504011154401e010442080351100982c0040201a100344c1da180780340c41c00102495580c0d1028028400480d541c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 258751843 1250 258750593 258750623
    0x120a0b010c080d0e16051507050a060b01170708011509061403220b040c050105031303030e1207080306130b0a030303020a031b0206060909160308070c2718 68
    0x50074020300983c0d480000001000e4410401482c030300310150401c00390303540645404210a103404043e03080044029010146458080d079a103d850307080b0100c000380075642e0703806d455071240d104040709a80380541801075510b07030402c03850180420509200d008004c46091f14296140362189091400719134550321800520610000c01c1d40454000030071402910a1061521042007201c03190050380c140964451129030420781468440d440d01034000c641404410000d0000c2e042c0c41032080500b803605860002410080e102c6060306004440aa29455441c081102800d01200c24000c501420046800380200c4410360440400d03590320030445a4000424042000030070302a8005140c1041149070000e1040c401c0c00d100148100340550180042c1c0c44541004881d0900c3c5080320f1300440b0b00001000c5020121107050400d100c180001405250007241c4181000401c98100c03019240c240b070803d0301c10218820348078003040c000c0051903004d81042050340350b4560a07801c0c0003815400c20445005003a13 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 258753093 1250 258751843 258751853
    0x2180411040b0714030703180b030606040905041103010203190612030c030807020111040f05040b010c050601052701080a0c0603091104090503090d050303010618300605040503120a0b010c 82
    0x9800c01d41319006134401a0446034420700c01000854429100e50340300075010440d002039040c20b40c0100f14414020014040c09070b48510607541160062940803c45544620344002007142c20f10301140c1641c008001e002c610306241c000081012030b94072040040d0780d070356080c03a209a09204000750104081e09541004240305d440c500e80c2c003803035a000210700d040200c1e0300000a41d1295019103000d0000010032b10032071801e4050310140807800d1a10b034154083c40d480c0c8684602e418429144a06000700099401d5060604140650000001c1540c0150703521401217071114055902156941055003012402d540680302c0c1d2842240c1110110391a6002441800010081c40c002610148810b00c190845995034680d4a40c840388640040c589a514000300500b8020b03c407088980d441080d603409101c1e514079005043d50080040740381e002680344040c8900c1d5010545100601107a04180410083c88400401803001c10005080c4800a50301c10702c0d0303941141c00c114421400600b0000610010071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 258754343 1250 258753093 258753097
    0x111b1504060c050d09061e1e0b22050720070b0c0c0604140406060507030203091504030803180601060c02010c020907030209030a0809090703020c0c120f010f2703090e040c0509040602180411040b 85
    0x3001d82b070001c0f01d04d0211074441c034041c00250201081e43d00d4a0800c2030031680090704400036900000b40030040100708910584030003040c02a00700c060000710751181c04080411840c2680d5001807c02c42e0743d00c0c0ca5964030303050f058810715151302460401c000055143e20800844100c0c80d0580d000d1420491810700700481119075900071002d00c1c0c024400031012982d00e5005600590384c100c6141c0200654012840c28914140d0114040c404043c1034600580d8002101880081c3e040b0348000c486d03503529805400038000d1081140d0144204082d04080083e01002032000b25000c850006441e90340903421030a070f20a101d01080e1582003d04d503d40e43d42007190208020550f0642940c000400b403501c11030848110300c280d250941c0c3c42e5450b051455500750010f0300a8446030000c00e100a1031500c0c050003803655841010400705289001405202c4980b03098006080001d207070203158103003810400c0c065006544485651800e01c482840306240c107102e4151034080c1da8107042d00b414600000a5065 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 258755593 1250 258754343 258754361
    0x6030a02031005040c110c010801050117060319030c06060e1003060507020a12032f040b0304030212030103080a17061c0201050d111b1504060c050d09061e1e 69
    0x542c000d00350110301d5a6580c040c440703801074a0390314407405a00c0c8a801c2c03480c25500d540c42c0360500c1000e600512669034030001c0d13280c3c0c010100c0030301101c0340c6034680400e1074094003200a060314415100c03440c04042d0b1001d00110300c5406028140300c00c68841c8540d001303200d000d403a00c01c1b070b07804801010000541940c0095a1040e0039005440c40a6599103507000320941981090340002da4411400780740b010003e1004034404146401864003c1c0e0b02644494144280d0048545108011000608151080021394041c506500e0859180c1d41c3d2031900460ba40c1104156a0110382030001c8092039449400800b072058400034413000090144030040402c42d603000e0300580c10031200b00204035041000303000b120300241d107400b181603984100101059000d9032210b41c0f901d1a400c072801041c022582817a4040d04590072032000030798814940800d13600762040fa154520410b0400c21044240486603101c11002c14031140b0254003000803d902302e044030000c400c3d6000c8078600d1480d0b404502440e6000290b6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 258756843 1250 258755593 258755611
    0xa02090702150103061b1701030b1b07050c270712060509010803031509041101050d09060510050103060506042702070218150f0d06150504020a030912090506030a0203 73
    0x400c600110000411409070000c0d112103444000c0c00400e40000040d0114204543c94446447d44c501102d40c41c48450600c405802c1d0b11a090110300301640c5007019150450303003c0a00ca9442081c1d02c0d003191210400c9400502c0b42c40c00740031420590001d0114403030612500390782c64840b80d0f0f86010540e1200315004055000d19600c0751301203090348503240b0950190076600011070321b038642011900c80d000c8e00041d080340030300807050601000411008000b210543c003401e200c0d0b1540000c518850081000f0b50025203268246800d0040c03080b01500c04209484003030ba01072144948920070710407688684d1003030a100300862030040c5000119401f81c000c0e01c50440d0809131038090584c0024809103148801c21501d240700400f4807980e82a1120b041540f19001d0340c1d08110b842003880014160b4041c100f0250000791141310340e407036000c0810f405001500c4018401c5455040050b001002800428000c40c0e0b07a450082490b01214041c4c043c402c2100c0d0010205499980c130090514081d410203010020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 258758093 1250 258756843 258756853
    0x18121b16030209040611090a0909110103020c030d05220b2e0e090a06091a06041119110d0e030708010b0a0302010f030209130911040605060a03150f0303020102042301020a02090702 79
    0x91072303842c03140c4c00006101c090300c0880c0121480c240102010440714295040c540f04205013613501101100740ca80c0703240da08900103161b41e10301c08861028607407030104004540c0c0f06440bc00400c814045054042c2c14800f14406008603000030803441c5001d608002e490b0545a10300400c164022107810b10f5104600b001600c0714080e50355903a13002d0326400801102c00403a0000b070604c042554424060f440742d011541800249100303910f802c0030388141d86203510140084c0c900307800414000e0110700d041c4407480040313034103014a501e002420600010580d502c2070007403450008641d02c0500030340705580030042030368030540e24603401500d8145120100c202030540034090030105e41d0b8bd015600d4076401011601280f800d403c1d1500ca041241c01c2080c0512842c50080c05000700d84521007600c060740c0180c01c00151403511140c2d42c8620980a61200310341c40c1d2403960102c1090384c190090011210000c00b18080c01c00010320940d1a8100c020f40e07140140d011805038130140c9409081150801d0540c0141c907 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 258759343 1250 258758093 258758107
    0x10021b061b060912251a0406061a031605030402210604140312010e09030409020403060c020706080403020a0f0305121501111518121b16030209040611 66
    0x60400e07044240708141070b0700100c08100070801c05001942051091000f52071402c0d003070640300804000e400e1004c092030303450300841c80200240268045500844506249400e02d01490000043e0249001e07008050700601c142c1c030b601c540d50708140d038042c901d010030524a00211100890340740d00000e00c140c1e0b020038014800840b00420614000748030042c030f006090a403506041885100300c000c0c0b0f1100c150360041160107c1181d20200e035506549520491861a4681c00416491805603400102803544005400420400d16500011400c4a55005d660031650f4401e425240e0b1700c0112400703005070b003180e40b00500241c0340700041d182c418030078144182015802400b4054010b022211020720040f0305c5d06c08459982c1140d800c2d6014071031000104418010032000c1983d80401500c18034a0a0281c0c40d0014000d1007481650341c140054081551a10142c102044040002130440715107030103600408160407000406120640c3c0e00604030780d005031148d035600c00083c10062130040520100340005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 258760593 1250 258759343 258759367
    0xa0c0c0303030b0a061d011206080316020a080705060d020d06090c0809011b022e0213090f0203010501050f03130c2601020901090302010c1104181110021b06 69
    0x524080c6010b0b560000c1e03031182030014000462007a42040042c050f07401001d035202c916620300c00c000003c0a20380110300c8a541061000900b0140e000380d4180d002c00b280790160018560700000085000300c0782001090740e1801580e86524031805a542c03c014100072080a0303072000c0d002400c1610003030368001501983c407013110b42102d5060908000041e00502401300c010000d0080e00302c035070324861700011650042c0001968914007541510350003103c0407454214007084501585510000b00c109550b2040c54035002c0c0c0300e00d0480d0280d00a524584106d011000001d4800c0c1c9040e5001070b15142e103444000103000c4100d41008010802d0324400390081400030b03807600d4a030f100910848007010f003607000703c20161550413009405e08409070b2042c4183d04040e0307071144954048940a08001a010300d82e401c00c83d0090385411405600142403901c1004003038451920560b65601480d010850000401300300080b0361003a0115400684c030501864010480785019042e41c0900240072500d0030311f20340c03c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 258761843 1250 258760593 258760613
    0xd030c1e021903031101052401050d0e0309031912030902030a020a08030c330903042c0a140105040b1311040501081008060f19020d06150e0310020a0c 66
    0x296a0142c0002410402c243e002085060b800807844003d110514010610310241d890b004a2076406032300940b065110359021300102c5034000001c00c410320420711a9010251703244d116004440c00b0380300d2412007070502d4840d2510061000e52108003203100490000d000c40180401c00340903a81350245c1000741005a40380548480200a0400695228400301ea4070a003407a0340114040303071181106506100d42c502840c1465400c080c54200228581c44203041d141c80c5000e25080340010000c8141e8140203002c070261244480d03003004116100b03640c0c60b040c0c40403d461042da0701d80e615101e40d00c01030000d440c00e9009441200c07409081d801d80100c4405005046d45d148003d201041c4400060502c55540c0c0404a00c0d8418010115540c5407407401c0c0803d5a1190004c003407903034001d01c840104040441c0e4070750420b901e40b100e140035501c07030b20001c502030000c2c007052184880101c01280038805190003031420000c003840080c0503004c2d004881008e00040d510000707069003080300a1703142c0303800100003120b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 258763093 1250 258761843 258761869
    0x31d0f07030605150108130507081204091512020d2f04050c0301060f0503061c03080717060a14030a170c0c06090a03060b0f150a020c0d030c1e02 64
    0x1000d40c189141090300c203c48019109401403045401e4007a401c0e600204610340280b82c204203070800721202d00701700d8100100e5800c00c2d880c50040c00440c40d50801401b002d08159030800c1e008100c103280c901d907240c0075035046200c2ca00101001d10250809031411500c4102002d0050380e90180a1406101a050b1401e808280c040d142d65940d03e0406541018032545502501d9007002c0ca1655042c1080506441e0b600310070001005000000107145491f40f0b2005680c215140b00200325043d811314010b01940e0003101c00b14009158200782e000300d9044010b1075809142e0140a4540d01c500307004864166001c900b1011784c142c464070498400090580e2841c1382260501c0da10315403648000d02d0b40c0c0341000c81071145544038000074030032407078503583d000600c03c200c5e0386c454800a000c101c24404515030b040c2014009902171009481114106000d0000740a542800e5090300d0210320003408110200c1d00300600680080c0001d0f004100141d020440050110140c180d0320011803140d50020301001140c44d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 258764343 1250 258763093 258763123
    0x1051e0c160f29130902030f09010c050a0507060e030301080c0a080d05120717040c06020d110601151b03090608070816080c09120724020d031d 63
    0x110003180d00d09003454240e03028010804216640e686030200c00c0d070103a0700f2940200c940740544101c0029440303810742103c400081c0c0f440c20b645040d03510b40854000b5001240d5507690b4048a60001e48170b0641131260b800350134010b13180c042c282016040200e4480d00300401c11584960350348007180d00c0400030030107035000b4900302d4010000d20f0748460500a80300da1583c455081c95001c07100b40c41d101d0341c100d810ba81d60042421040c1440341d66a800480c1c414004541000d05852040c040c007081c09a02c0c05560305650040d02242e202c59906001141c6030700d50100d6401072074000b18010700c0844800001d0881c400c0c0c00d440c2c580b0046000e0002100c041c1d20b0580203c001c12a0048100200d5800c2412250b1016040c1080f0000340350072500d2040019916242c0820801044002034819001c0c4003a00c0741c400001e030403613500e000c0510070682c0e6071205014010710249640f032100c4804200f4813a500081c2500e5020341107601054a00b580500f084818080000080c2e00d00400340758810400c0c4803d04280c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 258765593 1250 258764343 258764353
    0x140d0603140f1b04021c091505090d0503130201020c1002061608090c0f1309050304080120040905060f060a02010c1130040b0304030c0b09060402090601051e0c 70
    0x680c540c2803030072101644032482ca4201d0200300000566140a81c0340d0030300e00b580e016a80c3c12600007420355400910015505203454507094a0a01800d2052040303401c00901040160361034400c111942c400311501170100040c01080001c0120342c1406581d03000030700c180112035414454000103644101752880b400d0041e071001c810031510301d5034900024001d0540303081c4124241025070300b00307407207115104860b070144520b40144011511400000c03501c20050754801c000c10721183c0307080c544a41c001d114803036040d230070300e55030f6071031208240c2c007807415a0585451580740c1881c100b0b401010300b00050040b07500801c2d40541148035101c9600510208005500016049062032006031050040e030510f040c050f070000300e40711136040c0960341d607072040d1403d0000c8090f0449201c00705010361060303030031410031403402005010800d80c01c101070501081c8200448034903946d840c2c603980d40c0c03400116400b80d4440380c0b00b004640a0b5006000401c2402e0050b8407481950f45d00441e5460b140c0e10803c04168030343c0c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 258766843 1250 258765593 258765623
    0x207020a0806040f031205010f29130f08010c0e1212030a0e0d08010506220810020c10050c0f09040e0d020d0e01030207110f01050c01050a02120c0304050a03140d0603 73
    0x102c43c441040d400340d148800c0081e94100110208495818058a1004840c19081024030301543d020380702003030151500d8642cbc0e004010b080701400d981601c1900d14051028001040124060040398070a50702c40d601d02d40c404002030308001405c5002201010180595a030850256411200652144880b00e1021030750050340aa640d103801010300482d403c000303140f0014401d0f44d8a110480d01c0922030b80080003070306202c01d102240100358550007140c191260062460000850350090203101e0809400c0d116071103e048034140a880d021925484a404100900328403044490040c0040403170203000000d1015401c42c3c10362600041400d018050f80c00320f0080b04ac511351060849034003c90a10741542031084507603c07480c0c031b0340580c1c1190b48541c084030b90403505644140c0079180107d00000c020301481c1400440c90703000754404092404440d030001d0004404004030f00490307000c0e99001c4000d2084148648084a40c0c000307000c2c00b001041c20411030454002420300484001e075004032180c44130030740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 258768093 1250 258766843 258766847
    0xa180b04260c01080702010e10050108010c1110050712090501050f0c09060313051504151109030a0f0c05060a020102031f06200703060e060702100615030207020a0806040f03 76
    0x944036009000103407200c04201d100c45400b250040c084102820300300b03055103640c60140d0140c0f21140f40048180710300c9014912511f12a003000d4100c0708007078000c00c0315800d00c000c00c0ba99403403a544900c005600006128826041c00c0d03101c254406024540031015000d4041d8503004e590f02403409807026919042441950000c00364910340205001900902e010540001700d15280001031203030404222031141e120078000284001c0d80c0142088000c1801403505252000d00000c40d8a60b89010034078112020340240c03050000c0b20358003c0018000c1011510903074808a8a044021003100e004080303640024498441c0030160605140c02e4001603182d10f01160308804500c1fa48448208181c0000741c00c12207150020403261001c0583c20104044200c0d8001852134503031550300051201c0d180c9078820540d0440130820502820242d401e46030742e58100060b00d0151050b40c0110310204000e801c0b0040c02c54081e03030041000300d10141900e84025a262031150a01004550580350642048100d0040603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 258769343 1250 258768093 258768119
    0x50907030c1106060a1202060408030307180e010609030602092107060e0a050f090903090a03060b120d050a051b0d02030304170705060a020903010b1009060306060e090703020a180b04 80
    0x2c405070000f01110b00d060000a05010010320514402e0003072585079000b9521070303000311006001e0110841e070ba207051915004025482502c0e06060780d40520001091010036450802e040313840360350740c8040f11401c68a580703000707510002042d90f1003044054070301010603491100e0507451291002030b021607860050003030b00d1814002480c0e44100d079911028005580e54401d080e03800c2100382c680c1040c558802211515621400031400e610410340e040002c1000240e40185071168070a80e40144100d40c2408500d0b9102c2c002c08401010403c01e101d5403154600c03800107440384044500c445d1410b0b80b0340300125802c0070710000c0c2280c01600008104400c0c000d4070004003d900c5108036815241190781d03101c01b84c9403d4090900b408868000400d410942d500750064a00b00c41c00800041c3c41d4083e03101d0180030480103109102c0400c0c20864000740b03a601440d2003255028015104009503038482400b01c00031341c0291004401d10880b1b00d00322038014004401840540484110555518180f030700c1d0740e00c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 258770593 1250 258769343 258769367
    0x240702010e0604150203070c0f060f111606110715022208030304032f010b0f0105070c030f030c051209030106090b0303071b230a080f060708040c050907030c 69
    0x5940a031042c8800036903a013615400d542d0041c4801601da440700181142c2d000e94038500503241d80001961182400f409500058604079010010400c9410110031140f01e0700030300002d0801c2a0056500300085421608030b56015070b07950f42000d15142e02507482e00c0d07444501c01b90001106602060214103005883e0070104500c3c0c49040c08001189031450b0250780c1c0c40700a00043c100310002c0c2281140528072185c90480c1070300036800c203a21540d0a500caa000700003481206106180d00a11505954000c00440d0074075500320300780300e900c0c1c1d040d9110841084a00c800440402040c01c04130000f060003848a154004030f04104913607254050b80c101429503a5079008a00002e1908100181d16a0b001045640b03840d40120400b20038801001d441040072490b0b807200400e185810702c0c8480f0340109110051410b00204c1e035200410340c40700305d11603507404038540607510342d0b2001c008201d4a0303000c0c042c081d5001c0d2081607110070003900c035004601c08400031b843d0003000c2900d0707a080c041000c1d00b1440750146 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 258771843 1250 258770593 258770621
    0x9140c010e0a1406070c080105150a050f010804080705060f010f0f0f09180501060602030d1505010503180a050d05210c090f0a030501020a08060a120218070224070201 73
    0x440700e240c2000801501c2036204110540040c0142d407141a01d41c20143c640d881c0d040440007184613078901440b40a407000b1504a00042100116000c5500c0c0c0f00c3c84280940d10050030803100f03924414010740b960b0300c020b4000d9505480600901b80081c07010410f1520a089140c0341013480c0d450b0007503921510311190800c032688600329009000c050000003114040768604d100224800100301710341001c1d000c0c42400074000c2d50900e4004250760350000010304aa60103a00208400882c5c0403c00401154900505001070801c00c0801c50b403064071821600040000750a681503011a0741c1c0b828901a200112503011907404610750600c052809038403003940d4019000d0705910b2a06030103e0381c0d81d10401e00036920030360341c080a40b01c054549900e1203000c0c0d94840000c5540d40d80000010341048000c075403561141440c0280400c0c100c564104605140c0e50140000c0d44480c51040040c03070f42c2000901e801d086200c0c160710300c0d20624a4800e2620703003030300c503a6865a072414060300c001c0c2956040501802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 258773093 1250 258771843 258771857
    0x60504090902041145010e0f0306010609210507060c1e030c03082a16080f070501111201090506040209061b1612080c070e0a06090b1c022209140c01 65
    0x903110105190ba605c5103a42480c101070302c0310380b4900084040f403940340d031240c05204c1d100000c115950080b50036829500d44041f50310000c8001403140142e9000b1000c0109141c11107001041054085c01d900081c4600c00c102d030400100710210071400c1c00f041580203400046880031200c09241c1c00101103038110700d0380b00891580038401610034281030700008801d80c034404001100303d900c1101c55421251960f200b03035a80d944008510070004a500702c00c00540b0075501e40b035024442604490300300c5401b00154040a1000c0e8038021070400203240c010f1185804c1138003002040c8a558521008204069a5814080034160500440307881c2080424044070244404001442010110224032441a6028520070365501107070103038034141503180e8098250900c2400c24004194030355001741d0203880300820100b0280e1100d00c00c10410071200c41c4a0003144030030404100240c200010350710400940c00124007155145041103000700c072907104c01502c04c40400d1420f840c40100c01d0115100000092800354 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 258774343 1250 258773093 258773197
    0xa060902040e130503090406030b0402030c0604060206071d0a0306090b06030c0a03080f040302100906140a050a0c050703081c050907030b06010f0e10050c060604060605040909020411 80
    0x7042032001038220f00b010f00780744480d1010000d04004564115501600904c282983e07840e100e036a0407015a07080303219000d00038211109041c55019101110843d0307000b01a5502ca9840640700c07000c3d06071100032804045421030b2aa500c07a03445440080d8411140050f101600f402d0680c0c1204001e80918403d4200c004250701ca41d466840400a4035008210315076a100c7c04040c4030400e108941c002500712200c08540648140c00540903012190360352942c481003616240010098070550001c0d6000c40d034140600d2030701c40e22402280303400500c00c800311541c06c0d4403604c8100c0b0b95001040c2d100030006c400419004c5072212405110340081b03c9100030085c460070765a40b1400484000c1c00750f41003005810b02004114401d4510000a003c064102401c4c40c08056004005078003008880c65030748691004560942458400d950071200e0a60340c40742064240000c44015044a11082c3d03071103134480b0707580c0440b0742c2e001004200036081c030915403142a244203050907134100c26401d101e19440c4248111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 258775593 1250 258774343 258774359
    0x1505040f0e010801051f21060501030b090d0207080d0f031d06100602010506030303040b06030a1707020406120302060403081902040b12131713090e010c0206011e090209060405060703080a06090204 86
    0x5070f010703101c11f00018040301074600000f0b42104e02d503140140909061000000a0040d144500b03402030010806498516090100903a6115058816800ba0707901040300c04180b03e10546c203100c41401d0318a408500e045a041d02903803882960b07a07400c0d2494004000340056159504154401010140000d010503d40310002035124003004101501d40800000012200d6a0030702010382c2450303001c20100140700254010848940009108078012407034172401040c0b0b03100d07800c9503140e20b40e0b140c2c0c001e0080750781d980d800711600e44c00074200e000e0241e254030501401036443c0c00588045d040c40ca41003921440803034103c9003010740281520440030300341c940020100d8000740154409030400460035641d0031904500c0c201001460384841d12491400510715000801074100d440c641c442a401c4800383d0362142d41400228140b0100107480481c0c6036001c1103031305002e4001d840050002850070b8100b60717403140440e03110340c00080708400041c003860030010080c0b41c83c880c075006050803420441c04c5c1b5003000c8072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 258776843 1250 258775593 258775651
    0xb1c03171819030201110d050109060b030c07060e21031b09100c03021002040b07020906010905010e01030506030a0c1203110a03050a080405070504150807090e03041505040f0e01080105 81
    0x341c030007502c8011482c007454000d401111501c0c0c110081c6941d41c3e003c62000400500f4280034515000d0308002c0005501d11000c81a24000e001501906180000399030310f040080041400c40314040c05205002001106c08001c42d1058030351400d00d1a986c3d16116540b484c2984c070036050307042d00c020180001000c0c0d0301c03028802c100c40c031820309012058401c1c50400740c0c94242d541100501c09400060049400000d10015020032407081d2080702891f112180192016130450103402d001900c640b84103c41ca62080e01b010390040700103410b9590f25100c90b100c8015062103500708011891100492004060340300d41c110381c80c0d82c040c0d409401c4254055400a080d4402c41d2059410440c501c0042024805e0500c501d0004140c002d204103c0092a4032025000f13600510841009000340304002901180074000c01c1d000061840241d46454240054805030808030740110f01044803d200118803105c905900d80c002c0c110f02c0380e810209600d0148502d0030746400800000000c2c814004910101500c140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 258778093 1250 258776843 258776863
    0x6120f09050a080f0f030a0204060f0c0308071812080c060f040201021903171f0503120409090f050105270a0b04110d1e032d030b1c031718 61
    0x903554401c600c8032074150300569800c802804800802d0001c1440310358010301c110ac815417502c03230b880c901c40d17903041d99030b40282035018002c50450700014560a2041c0076629400d01c2140000000c0340c0c440d4201641038001744c10880301643d0005440c10210020080b5691140c07400070300904520386580000e45840c200461403580f00c442c00c021108060140300d1031f41030240c402c0e105a4245ca0180c0041c1e1900d03000788c5102418010000c800b103658100820341440603010382d6121403501e0324143d440703002448026016100c905c612451480025400c1c080d890203070010f100c9504000d0390780300f2003580c2c40d0950301181c0d030300d0380c0070703242000004940304006a030090b080704d06c0c10300b1105140045603c0705105e000007082c1110520705090402c6504a160003224040d550392203100120790308426851101c02c05000070000020001d2240510940010928860103440201c0002c600070015000d2002050100c02240440322001030010f142039005500178007411600c00303180342904200c0d440e060801c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 258779343 1250 258778093 258778103
    0x406090f06050a050a0c0b1612020c060619050d0f02090c070f02010f02010e0a05030c0d02010510030803060a0b0c01020309060708060a030201080408040e0106120c0f17060d06020406120f09050a 85
    0x10a041c44598018603a1246054107c03d414406107020030081c54800002e80d882408078043e04032100315800700c0e00c261140d800540004082c5078482d141000b068001c0700400316012101d814010919480350450f501781c40b03100f400600505000f40c0f0400c52010002001810108000d00400d00441c0d48400c88072034994080c2002c1103520340148089000d030810140e00280340c032981c0e1402e0700300310000005004180703400d010b9070b9075960460801c9081e2a01910b00804c00303c403007402400424084801544c00c008020f0801070340c250b41d4010321045802024540103030740d40c0841080031404052007116441816441c01c406185050400180407000601003e4100003801340003e00304040801210050103e80440e61110341e5140303001030072a41c08000a41115040800c8040c80750300841910924000700d40341d51007010310480c3c2c40442e880d030040841e9801646048150041401880140058880e40c2e80e0741116080030507250017035032184c8035090340052500d054900820408a032400b8095801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 258780593 1250 258779343 258779347
    0xf111c03021303020a0b270a150302090a27050c0313051f05010f0f03030203071401021b0c040b06090d111203040f03290f10030f06020406090f06050a05 67
    0x90088801e045481c3d8000039005100f06401064511001e00540344045203410700c03407542c0c40751803c4141007250250446400500201c000e00106841c0403600c8015403407403400500b0400024009401d51405a02c0381e05240c1034a0a20740c3c030104c620861041030032140c2400d1060781421482c0302500c0c40014200c070b90902418140c0c20401c0020302070034802d11a00700d030943d00030500c1a031404c0200420700c20700c4c40030040386000042d44040348041504494058020354241300103a1112000268815060a01950308101c84984503180d00d8450609840540041118010040034001203403500c440c81d0703110398424080300b0902e5031901d903d082c12650118000d405a04800c022030b600030007910182440e80800b14011445800c940441c0301203901410f03c10500003039852070344c114459281e40d0f80c540310301c90b81d0004d18003165031014550040e0726030262040e011b0f500e4907501e11318003030010304071151a00020704100301ba610043c100c01400550a004d0000d0f80740140c050480e114403440300b801d010700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 258781843 1250 258780593 258780607
    0x60d0809040e1b040c080f0c13082a0a05241e07020306060d020f040515030f03030f01090b030a03031503021002010c020f0705010f08060301020f0a0f111c0302 70
    0x40380c1002c041c44502c40112101c455126035901c0f018a1001d01241c051494144e40b0442c05200e42440c2d07001d820007190004441e220104850310507407141034a00c1c41012508030009a640b0b08100d641c001110a000403c40b02d01703144015200f40c04000038561107245044010701103a07550200614031080ba840c0c55280c1404013184803036541c0102c0181c0050740380040c101114600c500402051001d1080341a580c07295134100801610515141000c0c0d00b04104080681d003908055001076000b002406d0020450300030f10002a01c1c2070034030b40d10b10f00650004401c2c01a000a07811069024180c0e0f5402800418409404a980c0c0c41890704042c0c205038032008016110418860700e20f02554016000e00324042d41500080e002c7d1000f03181c600010f10031402a6090320002184030401d0381e038140c0d540c000e0202e41e520110780100303010b0070360741c4d25560810200000c44010b60003005940c0a54641080800c000000503105011072009400590000403000d20140c035141c420728904440ba080050321107034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 258783093 1250 258781843 258781849
    0x1305010b0913060b190e060301030f020904020a091107032604080d0906020f09270a0b060c070e0f130b1605070203061005210d0c030210050103030f08010806060d0809 73
    0x441135100440c210381c0050480440303410f2144c514030850756900e40c0c0100c15015814024030f4482444082c02d00c0700711845c0e03000146042411346421500092503c000141c981c545802200c448100341c1c03d0200c030009408c01015000903c18081c2004400300700b0303101ca0800c41c83c001c21310300144002d240560001e400c440c1d8a000f030303000d034450b9a04608210f45804000c0a80360807580424000303440384510140008002110030501c0754600c2010501d0141511206619400f134490040781c103900c0402070040503c480d004000000c0180000c02c008000c5083c40d24481d00d020700f000d08428054618036803a04003107583d045955130404a80703d4040780c80c503800d0a00f15101d004003400290b15000304001e010034030b000380e0b4209080e6081111611214100044180c41165842038100290342140103030100c1540641c003a541141d019006030f07000340300044103040407582c1c241c00c114003081604d9448401e15038401c180902410360f4000a0085007448c0001a8040030802c00061100c10b00084407c00c5071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 258784343 1250 258783093 258783101
    0x2030f0a0510180221060d020f01030f02070c0f0b0c0d081008100609110703020a0206030c04031e05010b09041a0603030c0106170c0306040b0406111c0b1305010b0913 73
    0x1d5030010442940c5040f0481d600a54040100740915500c018400180c603048402d07a03601465005050b41c8160400d642405000039005101364140b6650300306d030174070401c013074001407605912904554a215040c2130740c1080142c1290021080c80e1000e000389001c5a0000800025000c61420854260790700c0760510038001c1c200b07402480c180d01500400201d8991683c02480585800c200180101c0d04001010b248a0069180c05401039110a2110303001d8100000119048002c0344a0180b8190300c9480b48082d540150b0704410300003241400c40d04c1800030030b2045900c001c104480a6120b410145c94003052200c850340800d0403144c12602096480e41c00304115041848808000d00c80c0c15522182c20105031200d241d40c4100d402481c9041c0c06615010030250302c110341c000e81c5a081074545498450041407940b1052252400410003d13890807041102903549040100000c107046002c43c0500c8a020101c080484102703091400501c4425042400c0e0f5403254416981103071905000d0714881c0c050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 258785593 1250 258784343 258784349
    0x609020a03080d0b01080106020d0504060e030f0f060a0c03020f030109020901030e0f0a05102711031b1201050114011b020405010803090907050c0307020d05031903020c0106050402030f0a0510 84
    0x114800103143c11101035640100034070240c26225180e0b242c1c0d86000982e254501c86503000001142040140003050198603440110703500501284c9030880c10740c08441c0f40c1100e81ca80c03019154400300401030200c1d464011200c4c4038019260940c180764090010903040d0006004284100d6004603556500d64401e030b001080e21062201140c0018a0707500015454000d0408180d450380694412289651002d010340c7d101c0d102000380260190198591340800402204000c81c1da402e0580c1c5114020760382003011052400d01c41c80d8043c1d0013085401001000c170700014241d24240d0400e0010000c0180408503600e8401c420b00308800c001d100161403141c011440e0300029801841d010001c03415420000140105440035108140545c48014007650580104039100a25034400c01607040103040200414000030b1058040340d0030a10a01d00c1c1c2e01c409030122240308000b9a020600303820020090040720005c05081d2021860f40c00c226204c02081a4002d09a045598440380404d105602c207005070001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 258786843 1250 258785593 258785603
    0xc050d0312090b0717040c150207080d05191e030b121501060e0d05250905090610091a040b031606080405060105100509010c0602040b040603021207031104030609020a03 74
    0x404010314000d42c07200300650743c20700000c0001d0120a60540c188441701d000700c1d081080c0080e6949400c0d8041e07d103604910b54682103000d0400005009841000642050304858030342c01c1c1c49444e4000c81d8422402c80002010400141540030050003042c10a44515012146004100740c10b10717802048008100840d2240d50307115001c070f609000400102c01078107842c034039500e400104000c24104001000c0044010389683c10164103180344003030702c007042e2002003288010340041a036075034100c1d030486804036141030443e0050000c0043c0c0400d0000c00c00c01a020201040004240d6038082180f03a90090114074021f41d40da9001c408a0b64040208843c1c10020180c40b1203610f03201e83c001464114259005c45042c0714100002c10030b45400100380c0c0c00c81c0c003540d44140c1406680c900440348500300c45d4083c3c4105500300800315405840c94000c0015242c5500d0150740e55114510090840c80010044010180741c20102a003500d1664212030840b90040d6010a20022a00000e0140d0f2201c0c0d1008003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 258788093 1250 258786843 258786851
    0xb0a050a0b040801050109090b0f0613020c01050405100516270f18050105010f0309030c050607022409030a0c050316150b0312091201060e040b040c0b070c050d0312 72
    0xd529407800001d20648007104002d10490340d8800342d22043e1404400004e00880001c000a6651000700301016840000140a116007100f1640982e003240e00100035024665162070411041c414200400d400b803036241e84d4200264680100c24003880504a03030403504000c8070000402c00c245031403d228003000c20180840d03014643d100c2410440d00b5580c070031024190819041c15088070101c0c03013124101c84060f111043c01c858500c004130000d10540f50214140200c45040e1404074008000c4180b1420b003507001811407000d030500107500c0380004074884112b0210035041041280000c01544d123829044d0810b114044558a40182180580c1c0341b6294107940403600d050510007140c1c0c00c07280e588070002c03041060510f00411b0549844060308407880e00081002102181d00b0208401081c0c0244c01000151041e2642684c2c1c1d0014421348007554004da0700001c2c8000d00c0540c64488009028a528061030134595a80c0c0080c50398003445260702c1041d141c0c881400745400390305094203024580600308 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 258789343 1250 258788093 258788099
    0x2030f0d08090d050a09050d02010c0b01260c0f0118030b0916090212010e1905010b090a051206010504020a051603021509070b18010c0b090318150307030b0a050a 71
    0x400c4514220b66200140c8100c2c91180151400b0704221034101c00c440e60382d418071500300001d0009240401c0c0040b8100b0040e074219001040c041e901c914060568101070f200c0d410340c03031200035050301c402203050000c640241009040a17503504c4180b0001c48001c1c00c0c00822220a40c0c050803070a08180c2c0701908040088040240e103400209101c4c5145550404805d00d031616444030704124015625284401482500140010450308102d40e0340b01e52011107040e0310b80c5441860380c043e224203900040840030042035090301441d207030702c0200180c20240c520f036500c0c18090010559030390701846034034000c5600050b282c00c00f904c01c404480201701c211a0701035180b80f1500d0025602e20980304041001011103000c103190200c08500081220f4901030440d0a0109004008000541001c4018103000f101c56456002405813000039101d906128051074071403c082c00a0451400c204c1c070300d94400e1011004804d84002100c00b83d0350010850f00d00041c7c180c0c07070b8802003003c880355031b000581d00c0b0031200800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 258790593 1250 258789343 258789347
    0x90b2503020c03071d01060f02190213061e0b091305060d020d080a020114011a0f0408120d0506030303070f050706150b0a0306081204210c030b070f0e01091202030f0d 73
    0x418105c00c00c042e000303100c0e40e90380e000446420746600a500c00507005181d000c11116603411450a00c6030000300001c07054403065031103008540641d031084840e03203a903e00b03031910b00507403d04041c01018607410782441c12040d1000160b11644041718080b41c1c80c0d950002c240d0710f80300d00540850300c56003c1c14051440000c1d0501c2170f4217400110913170006608082d00840d00d41e100c1014581214003205e82c0e2080800d013032004039440d41050700c042c161001d06000000d902c580810402d041320030203090080c0c3d00c41c03c0c1c0124405854000b01a940282c2c010000e00545a500c15a0440d00c4146450620385a810a04c3c10030040c1c8103e010003c1d003104800c1c0b012610501d04070003054020350a40341005416510f52005880303461001048000690501040000600d00d5800c2c01049010082d51810003800e6502d0400410880d081518014506010880c07101d41007610a00c11520310b0400300e0f0703008440c40000300b411000d405142e441020740b01c195421900c04100700b0010400e80b106032064a0030180c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 258791843 1250 258790593 258790619
    0xd0203190c051f0c0c0201020c0120010c0306082109040915111909031211070e0108010c0f03020310150309080d05060405010506121611010219090b2503020c0307 71
    0x1100780a18081c030300e2129174010b68001c040707035606030084c0c61418207207001520324010342010030302400c505149140c0c0001081c4640000e030700c050340700000d0032401c09024a1510410b1a218412880020050b0985400351001d942d08200105d074085000d166074a01050203c41c5116640043d0f42044000c640b410240c20103400440301e80101e503400c4001e41c540490f5841454480038109410401400780610f00c00e6030716407501d280038001c86064a943e00385000e9400c40036070140c0c1c84c6956034071860032400da0109040d040d8800f14a400c0d429400c001e00300c4201c0c2d000e0343c45101000308507600003800b0640250001103185400903902612001402c00340c802070542100c03450301c118540000825585032010540d034403090f12003500c01c01c0e42c0d1a01604110840f090030601705010305109180f00042003400102a02d8010303000c56249a55950b40203011a0026002003601c20750a0001315504800803070102c841890103440404102c1413414240d040c03510081550380c06000b45400860340640c1116 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 258793093 1250 258791843 258791893
    0x50a0e150106110c06031801140c040306051501020316060f0f1e050405060408030a0b060304030c0c060302160f15050f1009050705032419060207080d0203190c05 71
    0x2514000342c2e04090b48207460b140c5a9010540c84241071000c07c0629000b8582001e480070004000554511622500800840103d4549440700c000203028410860303180101a0040426081c002c401044000083e46074042d211005000c0d8003810054402c2c0415600041d11245041d0000c0048071809044c440107400d0780310001680f01224180d12224507901d104141c803440d0040054281c42d200c6554031101603002400f4444601d4071a45001c6681d942e1000560143e07200e510382012903140e80c9000315110005901c684141803041c400c40c500f40041c404031060b1036078001c00b002014085481c2002d44402400181406140f400d02001540c0380e10551480c022001d102d6500320841d61183c80405403036003100d490000800c00d10116610242c1094031110840d00d0722800d1032207030041d80206198641151150080490038141000a40e80501c60074018040e5040504041000b582c0080e59074030440355443c0c0d400703001001d0341c500d86214800c1c41d000164020265501005500690049401c8403c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 258794343 1250 258793093 258793097
    0x80a0c02121908031e0117152203020f0109080403200607080a0302091504170708030403120c06060315050618010b18090f10050105040605040504050a0e150106 70
    0x6030358401c1107200241862055204502040c84a0340660300c480c51500050f0000c1741c2c4401c0b070400c0c105212800c0500300e0203001d042038001c01501c9040c103004e02c2c00902149030501c0c1c420b05410310501c00d085c0c000d0341c00c1742d2400c002c20700c9207150141f800b00d1500e84600c401c0040341d440c1a84e00d0080240090003801202d0140041101e4003204c001d024030b50382030074422030740d11810070000c003000140300c50064013072015141030050030890080d0200343d059102c2188071404490000c3c092020f070f18080503505107541001c004006007400c1c2040340d6528030860101500109a003003500101c1c45c030403c600c000d425402070081c81030b2a0349180840201e612030110400d95800d00002424a06007110744030442b2840d81d0084c0841c2c0d103000d010304102d40c0324210900c0f400c41407480c40c00103501d9111025010305112480c0055500d0301c40e42a042c40342c4150801c07410058104001c02c2040d500006540c103884003214006107548818088900401030000042040e000e054901c0001103005240f540c102c522176 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 258795593 1250 258794343 258794359
    0xe0903040302041a01180e070e060904140a0c020705060306041d030d0504061b020d082205100605012105070203280e041806020306040204050604080d110102130e04050703080a0c02 79
    0x25100d2003100c989806440401c5903007d00040c02d00c0d00c135003e900030110020b4403103480e081c61340d0041020394041300c0c03000160130302207018060300074003610428042070318601c054205241030000288581c40090f020611450301d0381003068245004c441c401ca15081528201c1e60b0720760a03c400078003d4401160301b5582646000d50203c040100c90030740300c3d029001540a800d2603a8002c5050b1003c410207440d45050311f092005c2103da490700030100011141c041d1000b020800b08030810881a1030301a00030301d0422403100c42047d044550789024000c100d55104000c0b50540d05c141080340b55015100226001e00464500301145e1080e100b50012620101c1c2d8950b20f4000f6000280800e0306d03100071103c05540c0aa40c1c038a00451059400b40d41c10820041000d803400765078400081c8150015040051140c000c2d44211703d1494102c5032100c81805401e00035414000d0250028109030714038422002c52011001c001000c108050250b200610390110000340c03190b500b0b91000b4100d1800100484c024000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 258796843 1250 258795593 258795617
    0x105030c010503010513110c010b09060406121415070509040c1707050f070203010e070513050f06011101140106080910092001180b03042a0e0903040302041a01 70
    0x10118940d09040810384480346075919200600c900c40000300342ea41c40c1c1c0e41c0d460360044e005a10602c001c1800d84c14020006c900c09206c00f040024900e0046e200900c00c0d0f1800300108000c445620940c541540c02403001660348803400030302030405545c02140198407030900c08100c4420703006005058010001e94003009008034446094034881d1503081d070204103080b0300c8000380d00c05121b240101480a042c421441c2070450541c0840d003903614401042c8200d400c09602404542450b01000602184400e03080c059418100d0280d17001c842c01416042c1002009025041d07050b20035000711551427402c03904001c1d50341e59081d00401984080d600380026001d1920050441d8159008140f10076804c01c1c1c2010f2440c10710b425406000c03400b040301034184000c10f0078100348000c0f0300810000074894001203654074a02441c181d60b00c1d51610b44600401d000340e60400507003041000058080e21403203440703513040e5220b20142b03e155001e540d000030b502a0400204807141455001d4403505044280c84038504a1a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 258798093 1250 258796843 258796849
    0x8160506100f090c020627060c03070f08041203050406060b0318250905040201021905010605010221031504021306020309040c2a021f0c021305070507081804021606050105 75
    0x20004280f200160720400100e1b81503080200c621020b081e4052101082c403d040712554202001120000e27030540002c010030040a03041b0311401c02207042480d041034207107070554904104920b244141000c16503210006410028580d10100282c9031100c5204d40f2445e0490180741c540c03446680c0e02403980075090001d8042c0148246607482c500d2520321a08150b400c05601c1c20040c200104160304520903c421b50080d5118030808010f46d80c020800462001d0030b1400191509124440010030b41d80c0380e180b030f42446d03614481500e810400047c06180e04440703210000d0040e00500034241340703003480c0d00b8001412a400000800c2858000d950912007540d00840c10703200c3c503810115880c0510340080012500103082041149a1840140200c1c16041083c00403080d000c1c00d0440710000c250403005480942ca0002c1c3d05009060008005020500d030443c001031013400742d608010640100800e0840d454900712038442d4030741c0c1c0083d20441d115104080c401483d98020b003000c1c1c07420b0749410300200d4541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 258799343 1250 258798093 258798101
    0x105092e182105250c170f070b1e18042d0504050c01050a0233092b1b03050405180906040206030408090a15030c050306090408160506100f09 62
    0x4c160296074603000c40c1c4d80740e0078100350b03d040390080b145820401404103481507140000f52485000500420b2036180c10300b02185030410741d8001800302981441404403100e54503004507070a107002040c25469842e5010121115015030f030f03900c1d030303c2810000000305100055100703400c050010180c9a07406003000740782c501260010344010341640c01c442010340040d40110028440c80100740304868000c0c48202604a40030b00007980807500c08540c074a020030b4800825542134000d0031681c05094105600c0e0180c99600d908064a10358070417100200802c1d460003160410314500301c11001c21000001481c00074a02c1d4002c0c0256031061005101c40804400e00d80900b074852019140204102d840d96020006580c05c01402294400760800140c04591a020072200050180c0303501c0000006d0128009410344042481e00c3c070410200340304210456450741d403001e400c01d0f000712041d0b641c0e5814501d20703a003c104090000e8858440c00090050b13009044501c1c40031180c41001035188a80c488a8036000c1d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 258800593 1250 258799343 258799357
    0x16030b0315041b031203060501020c0d0611040e0f010e1602030904090c031202010e01050a1505060f070b01061e030207051e010b03010603060506030105092e182105 72
    0x1603101c404111050300c0a00e40140e00140118010340003c0b004080c040c00903005600100d40b018a84400340300036a0b018020070300902402d001500e14440644040740d0510080720000e840355458501c0500c54884000444016042600e9107d003103281203000d10390661000e104640951001d88001100102c10038081282214943e02840c5018038603010400980080e080035202025906e100000285042d6094410300780c01e50004140e845220107810708441005000c0740c2c0d04d50501200c0c46254040c08441002c1c0c40c070448a440e1139404404444ca4076020700c150007070880d8145400882d615800c40759044096440100343c04445010800c2101070b0701800b03900034a15488400100d02c84400c2c04c1d400c5540901103000065030301d003407000117030030746031242d0080d1881c55039042441030741e0500303004290f407285082d0001d00040341542c51007100e00c008103140500150580303840503184d00d46a0400c0b407000f003101c000840072244504004400500c1c0c10141c40019810001408a450240c0305079508 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 258801843 1250 258800593 258800599
    0x8010207140606060c250b19080f1005152109070816060507020f04061e0b030115050a0e10050913050f1906030203030f040510030501030b040201200607050316030b 72
    0x41b500075805d180d070070f4000000340c0545044030303030b2010520070303400030103001e0580e0000d0090194000003603000d011100c0103000904003041340c0d4100100b8850b00c140364003c64a060390507403e00070310018143d140d17004400c1e00032010070b02800c0b0000350764040c4000c58080d0380f007001a5601d0f288e0720006580d03a5050403056110340c8820102c1005020b0054001c0c3c1142b600240c1074803402104c1c840060708136a802d82182c00808100c1e46c41c20121078620f0301c40400b0708540b003182032840d41040c25003680010411075a804200f000500c0005852055240c802c1070750019011a000c01c0307039080702500c50f0f002104518002e40d0b143d10300c2415900035001d8140103054812804142e80c60711000c685480c88806054607507940c031580000010b071010030041c06c000b40c0d0030700c3c0b640d182ca007032204000002c2e0084900340c2c2014207100042c004504040526600250309003800c2d84820f840000c0700ba00d400c5401d2140c032660285404004030682c218008500c1000301750302c001003482c5604010b8045420201c074440e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 258803093 1250 258801843 258801853
    0x21302120103020d021c03020f0106060905031015080102040f1404020a0c1104021b030409110c06061e0301050a15121e1112010902130504151508010207140606060c 72
    0x405401c00132500f80c600c5001419890080e151802d001684e000851000c07801030388484050300030300c8428030460024050a18081029601e4100000d94034031700c00001078580c56440c19683d8034035500756404401441031100070740d1500e41d10250003407800c06610682e41c00e040c103420100028a0306200301c0700310380580c2d00d540c0008222511001c55403c01c5826194000e542082096003413000240042410885103000390703030301d5040a2051055a08450004040c40020301a0740c088440c085129940007a09842a208014050040c8440c500c8004803a40d0154600410312061a940c0d410020035071a0443c0e01d52000380d595562881401c00e034044c058980c0700b42c00403101c1c4482c425415a00c201c0c0c02102d4400400c2e60040002e080307030751200711103280d81c1e554410032011400d14100f0031030071034020700c0104110b207003d0321024000004120301c00d204903940c800701100b803527a4180f2080a89202002151a22080e140036803180289113103031292403040784005030b1240b8001040360301035001100641 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 258804343 1250 258803093 258803099
    0xf0903120809100608061806040330020301060c1b080304060e0307150203120702160506090a09060906051806010e060309120706050f241306030c080105040213021201 73
    0x1211580c01410482d40c90051241280c2c655903540124400303007000c0e40c05029581811010760305014925400c141041d00714038100004030f41c102c541504201103c42c64203041141e2644002c1d1002442c0488000c0e03548003000100307880e640024041442442500e2a4451441d21400d91a404c05180b06001c1241d00801007480140d200c0e002201e500b5034040c2c100c90050b6100c3c11055900d108080c0d402e001684045007140d14a040100d8032504010140090f06045280d000c0307280d002c2606000f40c9000d80d02c0011422031603210359845100500540004000041c0c80d4492000981401c0c8210b522950020b0506003402c440c00300c003e400740b14140c40341425288100140007080e000100034400c20b020765041034410401c2c0d400180350a80c07050f54002440d240c0303d5200c0000d140050883c881c0281060528280008098082502c40104030b561480302c40509000d640a013489410003403245851503000548504150001800f4a03c2110f070b140040c82485105412030061005d1000f82c00c138204010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 258805593 1250 258804343 258804347
    0x305060106030914070b1c1b0804050321070215060a050d020a0803031e01081c03020c0316080d110304030804151d06060a0f03020a03060c09080a0507060f090312 71
    0x70742105204008030340c0c9404d11503103001e0800e00d26070300408501c54002030010080e06040c40100300300250a0041141002111503000842c00c242c800006105252000c1018000c04009454009400151100004d60003004009207000103072158030140c401c1c1e824900d0011081c540003840b45c2d40c0602034040b550320703013020407041b4815105d043e6008501c0c4100815042d8061004600c40c080b41c600c91640645800c500880560050b0b2100d0016007204918010002c103034003540301c480c0c0f101d01c1c0140c0c4880740c242e2018298401c00e28005444a0b010400f00c0070000d2100240640a540c00010032540032103a0f01c8902520084600800061139040084c0c00190b504070100f407502d600c0700300000c5a0301c2c2d100c3e038403940e461607030f184501d03507840101000054605101404050100c00070745c05043e07403842e40400d024203a180002041e00e92204000005240308076050401042040100c0310000200d0a003651516114000e110001d9110b240000c1814001c1c0000011a6807081450020b40250602 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 258806843 1250 258805593 258805601
    0xa0f1d0402040908210a020a020309090a0219090911030601090b21011202090709061b020d0503070b010f0e01060e0f031f0e0105090109050c240a050301061206030506010603 76
    0x1040740e210395220b9010780441c0155020700070710705482d011103014481c1401c00c1080340400900303000800d1b004100623602d440d404025070f40541001e0300d1182d8251035035a06400039014100411039100441c060b10121140c0c85500c2c0421201100400c02055030a05a000018802242d226001c184444410085000e0b24401482d40032404504200101040032010070103400a0b84540c80102d4507107a824103500d440c411150b0001600d00304018202c1c900320019010251001d80c0040d41e9002813124070654540b181810300c915170020a0301d94440d0a03150003050040280100d082d14051210046510041d0f1072266059400a440d640c7d900880002044444940000103541501650701e03510174162451b0f8a90380320709140c12001c00c14400111140d4215240100207008981c1400c5405001c03650204010717002e80015203a1803041c0c00f41192084024108440042014070000340c2c07180c04980c080050b50684400d40c0d00c0303004824401c9208000d480c25800081e10980200c0b0041100d6402648 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 258808093 1250 258806843 258806851
    0x314041106071b0e0108100c09120c0315140a0506180901140907060e031501031e050a0605070807020c09160c060603060218190e0a09080304050c0a0f1d 67
    0xc002c3c850424160f500f6081101c041d40241e903800c4150005001031b0310180942c124910b18450708003d424282000180020700910940c124101041d0340c020038040740e1000380e400340d6004220260314112204501000308942c40421941d15031000c041103045c256030117414045ca000a03c00c045414030285012024540070340410040c0d0b503204021400001c3e025519445507549901602002b8508080a042c0c65a0004c0d164400d030041c003100d140c0003800c45411070550341c1003d0340b1303a01c1103480c0d03076400da00790761240c00030b40613100b414081c40800c030b03168000520604881e0b8030401c043d103480e5005e0340d171100200700540d880b40c0800300240c0f4140c0841c0d900d1800c01500d241007803182c03401c5c2e02e50300200d4449401c10b03a00643c0014003215048500070100d58906001d81d14084425142c0d4192201180300d8090620340c4c0f0b03614008560022402c0e0001d01050341c024035255030340d007400e02e401c0b982c03400b0020311a4040c06100c0340008240540003000b1045036001d240d68400c8030760312555050090320040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 258809343 1250 258808093 258808103
    0x2d0442030f1a0a0b090d121106010b0c1c1209170417060702030705030a08040206120f040204050702030a0e01032a020d020c03031303151e0c031404110607 68
    0x10030003103440501d80101e010768a0800b005080400312201884031140060b046003042d050b0410446900341c40c2d0b0329280a40a4206650081c00913030031808650076030b07500b04580000e00c107980000c1404071048009003400d030140c408582441c9035410041480303c5c07801c0014004107462290014124049401404030f451007018269010964101c0343e070019080b07500721034400100e83c0350841d030300c1d0000c01100c1c0d00b00001d80000d40c1401e880390743c1d0941e00d20400030710703d0030410500c0100d000c6407191070940c0d25018100c1d02c0d884861a10840207074086804540580c0700c1d80c01c2c071000c9000a0700200840e44511415070340d44000c003020700010743c081d04074080c4984100c0316654000760580d0151030289500e054550107800d108003076410080c50300100004032071094004000f201c082200b03948013181103d0340480302c1c00c0c0c0c0701c1c50524050000c1100c0c03909848801c01c040c07801003200c44568404220801c05882c00c018038403d840420050000c102c400a007254240c41d000304892500c0c3c005005298030071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 258810593 1250 258809343 258809351
    0x3020405150a0803120108070324060e01030807020102160612020901090e04050303040c08030c06160210060e060a0603110a081801090506040210031e022d044203 71
    0x950200385410000d03032206209400128504040507a42642c05e0300400c0503c006090460650300d0728007891050104000b43d84076011801c0c88114200e4002d00c009101244810a0342d6950b818070035065400b60008a0050264000558951450000590503242e0035602d2400007404c0b142e04000960002310424140f20a46070f00080c03101909119a11070791091020b140c5a040514010381d032805a81c000342400e030414040c0111002001404a41c84001c00004100105180c503090781031880010701500414100708000c10411040d95140f809154280c1d00300401a80d42d1000314115130210041150403141041256450341c491508250045445a818030006030902a400c1c02c46034880c1c02190280c003d0750400c0154601403002102c40300003801e0601c8071a4800c01d0880028111480c0d203d40f00e580441c41503014603c105041e40d4000c0d0b4006410f03400e00481302e038680190440c4c49180351144d80c2e00302c014240c84031b04500071980c800360365180e05107901c640e2481d183c1c11400710496040507a5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 258811843 1250 258810593 258810631
    0xd050f130210031808090f091e0604090f03020106060e011d0609061606060305060c0a0f0305190e03030114182802120906240111070b0a020610060f0903020405 70
    0x1072002113000c24460b5000c69658139102c028403402c028020b4900e4803030707001c52041003083e10728201421510041c43c4820f400c5075569000080c01048059000f6158502c4200c41c1d02c101a0150321020980320300340c54150b2141e032039000445104905402100250314041c00d8130368a41450b0000e405104001070080b81022004006245a02c440740002e68500303486140c1041484801c1c0406500560300d0b01a2516098404001801041c0400380312010190303100000703120002e015642d250050028081031000c0d10b5121035003583d0350401c0c05a01100c1049405140b61441c00708411a64050711422651043d5034061042c0064100d848910800b05171407052152901c641d032005008411480800307422a0420710040307441d00701c0c014640ad440d40c0b61910810110309801161010803082441c02d4044410100210790a140d01584803e03650301c0082540b046580e000700c0c9803440707075441c280d0081642da0764074000c0341c04c0300e01180c0f503070003040d02000c0a10144c14a6040f0a83c82048c1c0c0900c07810700e0f03403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 258812949 1106 258811843 258811871
    0x70906081302060412050106030212160b0702100807020a0807080a0e0910090c050c10090201020d0305041104111903060609050a080c09041505010b0d050f13021003 72
    0x45017070b03224007088000d4108001441d030150003540c0c40c80c9404c45041d40e400010251b00301c5540c0391200460ba43d1041010ba41c00c0b190001c0c01e9040b03003801840d0035240c02c3d401508603800c500a0112003000700354840000d216640c81600d120360384000c0d17842d0081c01003080041d040d101b009070f8003e1244441e107482e800d0055680c02800084e109400810599103489440094039142c0110038a15049050035440050454000c1e02918902c05250310101d00b2030348111801060320401c0720016105060a61281c01803c4119580c64a08403400e15158140c401c4c1300900310019031945414085507a00c280041c1c010481a0350a01043c0c1c20004155101d00c40381c0120760003100184001014803614190282480905204c2003090356105c0701c0d281059800035030754000d0316081101040480710030801e242d2244683c00c01c00d5a640c1215400c00000b24044510201010f07111040602c2e040c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 258633093 258812949 := by
  have h0 := BRFrame.cov_init 258633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 258633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 258633093 ≤ n) (h2 : n < 258812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
