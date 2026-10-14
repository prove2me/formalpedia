-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:20:50.921994+00:00
-- url     : https://prove2.me/submissions/9304e2c5-75b3-41d2-abee-09c851fef3cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 598381294 ≤ n < 598561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 598382544 1250 598381294 598381321
    0x140606060f09240a080c0c0706030b060c10020307020c01180603050705040b0f03010509070e28080601090e0f070e061309080c010b0415210c0e0c0918 66
    0x40d1107901015440c0e14110300821030030540e250342c2c0c00c00140b0f01209a454005907000034513080d440c641e0b450541e0340d1b9041c08004113108500620205511020007080194404c1c1c3c81002050002499513144c450f0000009203046041000f600080d5400024011401d03010010980210820f003800300b40701000f500481c905140e81d205620a141d1140005900c0f54400c1e012a4050140340035a07a4603052041c0100d003c90300300740251402081c8043c0840d129500448a000c8040c6009086982407082034428030240317094003004010f00c1e02e414001054040701801000c0c080c01110900180000521400c14030307129061035101440d0b04103010070300c510403400300c02d258064415204030300c041240e0300801000f4248404090f0400b800486d0f01d414000d01900010301c0c200c03040b00d06200743c10101c03030f40d4100f0590342d116289024a80d0201505510422520905818010f440c8508525620580251402ca040340c802204450003c0d1940c01b520b480c410318041e844080b00d00c0c040034545115001c852 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 598383794 1250 598382544 598382557
    0x6020709020c012c01060e040209060d0201110304090b091305190206090429120d0c0f0c030503070606090501051c0c050402160c150503270a030c14060606 68
    0x80540000d240a0610b100350401224050072906019040d282111030780903114500d0b83d030780e4841d4280300b000940d03414140703c82401036800410840321034403104100000010740a4089040c0803401c0c04a00ca07805051000d0401010280380115030f40c14514200645940020846c800c141c070362845403000300b20300180c41c0008044040600311509058000241240103024a180e8841d0600a1550490441c0c46c0f040f100044480104001101800708101d00c1e601890030303516040c2c0c802d001d202e5010388540501800c9500030100b081841b00c00e0b454028807440345401c180d840380e100248120400030b240c45003000610311100c00700515414100010307000000745490f059210608a000414001050103010041c500200704564580004612404011031741b0720a5850b042041800030b050310002044128105080d51414503668800d54003911000b41c0200f061b480341d03074040004249020410195416900a403900c980a14003131900c5c1c550901c1c149100f442681201e002e02c1816205c070010350f070346d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 598385044 1250 598383794 598383809
    0x10c051609020a030f0e2509020d0c18031e0c030b010b030118020403020d0228180e0105060a05010516080409020d0e0a05070504110c031b0f1516200d18060207 70
    0x9170034465042403d170307d480320342012420a1002460100e20b06d4194441000d03180c0940b140d41c190b03003e10511104080d03451101910707080604851000090103080040722044c803800300c0c0e0807140e032a45c0341c2c5030345031000340c000c00f00d19a0000300620800e00040c00300180300b603030030400b9850142554003141d440020303000003c3c02040207500b000182400e01d040ca00100e210500301c1c10b00244d0740c00704680110b40485000700c0c1d15180c43c00c110805101030244612030b14004e1310281c0d178545030000444441d44400340100246040d00c00c11000a403402005000400d40d400e03001d0388404003060294211180d0100c4d031651036010524120006602003242021a841200e0005900b1034003010003009100d8060716078158040000c07000a2800000d2a01c0b5074008003004035004203042c07240c0b40b035640c0e20074444c543d4000303545070016a00862030500040c1c44981842c0a50044144c6103584070404015440800107401c020313100d00b10f40b6840b090b4184005281b10700e00d40c0d0300303107054400b0391161003d010320308 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 598386294 1250 598385044 598385083
    0x206060a03082505060403030c0e0103090305090906030c090901020703090504020702030a0209101e0f1e1202060d02040b0702150313030825020601080d0201050114010c051609020a030f0e 82
    0x207026200f0800300d44107140c00100781d507000e160a2070000d0041803411400000709261880491003075200341705541c03019a040c1c0750b041c505081e44040140211004001646c1482030340c1d0320016a48604410b070340558861000543c81304074514014088506a40101d070045205108074805039030300091804510344c041e9040341d080c0c1c81d850310548003400c460300b00c200350b02c0910925500c4142c0d524030010881e11a00a8016100d4844003200010310b8901030801c80000140418411030700c0c0001408103803071000741500e1074031404c1c00303024060ba00203038400410a00042100015820411499807070b04200403046840e5141040d6034948207a60f550b8045d041255503800034a41c41000c4400ca049a509a003041502d0711344100c0003503403800240100c29081c05507945400040c1d0050103094140e4001040d46810042440011181041c218600f62002d01c60741d82020382d40841000d4100292222540160b80d40350041d102a013524188042c0d000170a282c980d124100074030110340b682c0c0340f801e04000711 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 598387544 1250 598386294 598386337
    0x318041503080a120e0304050111030c07150c15090210030c27032a0e150103020a1707030e280f0206070b09060403090b0307080f07030207050106030b070206060a0308 73
    0xc440c80035802826080545c0b800326440d03009000080075004484099a400e201c8048105010303803030740500d140010b419808807409001c96030720708506900f20030503403510304840e03602c03034a0b2006401501c0520b00d000941e1000034900b035040070f450083d40e0030b20500b020f00030400900c0b0014100d000340c0c0312400342500301c0c0981c03404050030444132000954220f0280414814411482e8401e074074850304032400c00e01c00d5400080c21000c030320111803180200700c1d88140180700714001900a54081920070003006906074080d05002500420b841c05510340c0d50340091050f941e03c0303102b80b4202d24240115090401c04c1c45c0210a0565100360b00b0510b0350020041d007401c071451012900a02841ea4010080704074801000140000040c210b48514066a25031100c2c0d540d90341101c0607484281c81c8040010040d0700021181302c400c03944985c00c03540c240b400600d400445e80780c450858800c1c2d00b04031104482402404075581d410030a064100304200e5200d207003d4039560b0782c0401ca02c00d2500002e000f501e0744002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 598388794 1250 598387544 598387547
    0x7050c1002072d08060c071e0f050606010f170109150506030f10150e0d03021905011506081311040f110316080c04031b080109050318041503080a 64
    0x102e0010f010074840360320500d245503005032011000c4a6450404101c0f0b038800611070303400180b0349001e04e1070105901d00e00440da031030f0450400b011255a001d4840180f8200c40012011116400d1007030156000e0110b07402d1941c00109140e0007e4040c401300100900d82580840038074251030304442101400182528400d070301455404100e601140d8010004010007206900704d1204501c101340c1c14080d0b6181d59120071a02016a105400c848000350503589001014104004014400c2c0d01a0045806c071200c0d03000e9040600300a4002250f159448407005a00300000f81c42e4900602100e0038255098600b01c8042d01181d029104098115008228881d640351180d900c0306044503c0d1030024040b00601805070841c1d40d000b5501003035641041c0540c650424415075006001301590001186010b2841e02d410100f1400d000c3e516070f00400b0000c000456600910aa04140344568003464440000e102d0094144041101c0a03002c1c3e800c08014009592030314400b001030b690701498241d100c0160000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 598390044 1250 598388794 598388803
    0x120105070f0e031c090f0807030c0302061305032a0306010305062805010303050417150a0c2f0d09080d03050718080705040617060f09120d0507080c07050c1002 70
    0x59a01e004d41c03211051030700d460703200540c5000d480c04602d4050740d8580d00c0b002c455590000d480041d12000f0f609909200614168001b8a000650352201a00c11500c810000381081d0224070105401c0d45981d24200c40081481080b4040c000c00b103001e40050761440d11041e0700e440f4001c2c49000c5103007490020000c0340c80001a006100c001000c02044150b84901d00a0243c1e8084e00968400038040189040c00c454002180180320560100f0058103407980071019020b45840101101400a0740c0c2442d80204c2004e8a039201515841824480112944400d103050040008080c010422074400c00e009244000801c60031034801d5203400145a034a0380004c5950480050707005240350541c0c1c5002070441c900050700b8083d2001198200141e59407880950004c040401c050702d2190013020011b6800010107503060b602000403810354101c0480701c4c03a4413025500c40100100001d03500d001b8070100941c08a00240d100c1c1010308640d20303100c4252a000c5d03448458106151007480b03000b003000c19042c802d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 598391294 1250 598390044 598390063
    0x102030d051e181b0102070905040f060b0303040b070305070c050303210a090c050904080f04090606080a05060d2d0506061207061b030c0f03030b120105070f0e03 71
    0x10104624100300c00c1c2c0b8081154011500b5681c1e01414000c15000d80c41803103400c02c20b0406200801c0418800481103508182001d035130303819405107000000f52026907004e9540f18512903090601d480480707103400d00403101131301806030003580148420f200d41e4031014211140c03107030542009601c90225250041d0a113910381c00c003a0f014040458081d1700540d50b4200000c503101d0348010408580c4ea2030b440780e07085921840e4080c0c42c00203030000030000d90601007141c5401c18010000319162165420000c0c43c03650040d40004507183ea00c0204124881e0720051298118494141c140440d003004000070f110003000d650b000d002e492020040080c0b0b4898008558070030082c1811703003049101d240c10450707221142104c205000d000010140c403444078020030704a05440c12a03d840b070030400800030b54a40024044001c4041c001c204003140085440e02440c640001d200360b80102c2d8860004080c041c88140c010402071050f0704040c01d03c0303d0f4607004400b0000d80242494482c0005070040c00182c5800c0c07109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 598392544 1250 598391294 598391317
    0x7060e0a0909050105070305253f1103070539030901021c020607082d010303020d030501151b0b04050d0809030408030f0c010e0f072303060f0402010203 67
    0x551a0b000300b01d0117400c442d1003036803035807002c000b50354440b00e00f8842070080c00550440400c0c40a207081d0441d014405103c1c54007144211410380e08074401d5200080d07102d000d843c01404aa015014000d60414082c5401140da91801641541032401d806415405003102030191035101d1040d04a030541100481464112800c82a214140000c141079442c0e6204001c0c1078014002c606110f007020a00180050982d512a4020440d0390f840c200201d03845030015200002440102e0f05e6101080704844c0c00300700c01d40e00d03c0d4038000154503520b80170385480e07480f482d01014541050010070a400d20b808108840c4202810000c0c82807401100301c00c9402e2400000034112850305040c00203000c400510000d81c07041d29220f0000035140d42c0b1450b50b880c0620710481c0c2041d4000c21a449401c4d00d8040940303110801c101c0081010310180240600b0202009a20b0000f079020b01d40810005000b840c51250008003170310b80301220410080130a84560004080410945080f13001c1021079100304119000c41510303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 598393794 1250 598392544 598392551
    0x3010b030a03051b0a0206030406270303060e0112030f0305091509060411030307050a020d08090402030a0c020c04060803030c0a051207020c031c080f0601051e0415030207020307060e0a09 82
    0x110315003e001504500c441001d5190031251000e501000028542c005540060040e400e40e9102d6a564000c0c103c142d065402114800c285009400c0c103d41071024842d120b41c0f00850b0640c1865104541064141d01c941100c1007501c0590b400b20f82c000e40c0d116040d007101c0c90302044540c2c076124424a401d0841e03c851000803080f8003000007081d0045192800f9078454401d0001a5401c5420565079001784100549150048240e100042c0f8242680315070840c400c440355420525168000b4049810403030b24a20fa4036280c13840c1900180d410301082cad0f00d00c101140d04105143c200b50a039541d90000500e8440c0e0164000740b02056107028405403600b9601020701c5004510300910025280c020801030103020388111104007041c04458400c194079020a552504a50f50b80c082043c1950703200a0086814020104401010703800c90000310344801c00b00740703001c075512484d21441e19201d00c1c41d010100101407050003000b00682c0c2c0030920300e0858500d46407034800071040c40300203001c4c0d080b542e0000c80d00351316 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 598395044 1250 598393794 598393813
    0x30309030e22050108120d0b031f0c02151306050c13080304060201111c0c030b19181406010c030207050414060414010510050d0f1401030c14010f0e03010b03 69
    0x5080039005210365442c0107100903681c13040015500c4025118060b44003000b842050141192a84014564800101110585940c4103044405a805410340001d8180c0312042104032540400681d40089410110950286401c450407100b0001c8a13030003c010580b150045103c92100c0c800340c3d5401206084c001c5003541c1d80382c20704c075601d42c480d00c1910059400c000d221100103030400d068480c9000f07040c2d0303586505e0a241d0551802480a03000c0a07050542c3c99200100d03076120705c485605028200d0010705985030500a002c500719548481c00c007101400c0000200601021000c0c06170040028284240c1081030f6180690904d0101d03040b16802a00e040c021003011003016003954003400c0c050f5003c20034008012031221980700240510340c0c0000c0c41c6c107660506244904000d041c0140756000005419004010480035119069403880201c4071140c014801d210200304002d000b0329185044001c41e1681400190284040c9003d103020b0111006100145440a4120898000008041c2c4101d4030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 598396294 1250 598395044 598395079
    0x10210020d090503160c1a04090b061605010f1409031602131e180b0606030a020c070b031611060c0d06091d0f0307020906040b06120f070f0c030804030309030e 70
    0x418100141e518495440c0c6c002540c40a165a851508040750340c0145403c3c2000c4001000c0c0c0101001c2c2600100c08124100040c180c44a150703174954031403400410440c40c03089007181074401894004810312550010302c481c100b000011180ea20405541c134080010701d900020b00c03814051940210052701304211140f22001600d600700d40c104003500100140e8845001810501c081600020f1a83e066440403030030070314104001d10ba1103920f58501514203144c02c80642c2c104181030b84480c1d042c0b040841480250109030071102c1c40c07002e0901e400c0100010640340c0ca607951201821301034620200003905180604181c205501070048107006101aa00e107451240c1011403220f020039050180c8500e81881d044080100c803000d0ba0024103000180d120b502c2004014a210080f0f198041001c00c1401007a0280c0c070f1035544201c8402400e0000b074604000040c01b034a40ea59030500c00c02a142541c031002a0300b0012598005400d40fa00081c0c058480c0390960710310100c01103041e40300849046c60ba8168 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 598397544 1250 598396294 598396327
    0x20c090709030c0e19050c1b06040203010506040b0616020d120e0a0905310209042003070303050301031119080c040e190219181a01020c010210020d090503 68
    0x240c0c4282903040c01c850392604140d00414083c0d402002170b41c1501ca0200350022250000fa800540f02c54031a03150652003540750842e046c00b46040042c0c1c0d00100204825454288540d5a026405982c244850603044c0c00051481c030070022514080020b4a600c501552500b8010041e51507000f0420104042030079005450982200c004a00c6182911008102114603004490181c2034040d2215290f056a0b01d91880480b045031a85c003030724a03e05150030160313440c242120300403405902c55400d902c03401d40102410260750340015001354401386040001070b502a0841c0e045a0700207401d0303270608110600160018000c06442501d103102080301080031000400c820351011011242040140000b0409640f104c8440490713200d900c8030542c4134005810441442e0040c07132021013025070000d03200e21599030710000c0d1030b01140980f603a070710103c070b00350400c5100c41d42c0d074130000d00007001e80c8103060b00000e568800d41c02071403800c0c2d80c000c6400d003010701071f0b43c210800160b07008081d6510f80320241b440c440d01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 598398794 1250 598397544 598397549
    0x10b030d0203341a0603010c02071406070c06180909080423030a080d1802100c0212010e1606020c0901090b040e0709090201262404020a1206140604030210020c090709 73
    0xd108040081140741ca814403a0000740d48c0c02e6005801d034186404021050004076118158004a08000d5040010000d170600710241503a070720b9400d801c1500c2d42012448100d02d0300403059031031814001c0b501284154042d90308440009801c0c0720803040e1295070b030003858039448085130944110100382041040f1003001d0000703060300c480100400349840b190008809007000001e904a2414000d91501d148215015061240080c040700c018001c034600c0c83e402c42e6662560100745800080ba10a00b840c00046a0001841d59100408900c1c003000005940100d062140260075541e8010000090b100c80d04100d0580c0580c07800e5a40e078954501240c1c0c041c1245080880c00580351340c0000c940611599200d1500c59a9501a0003c070755440b40c2c0500000c11a00d108404003000c031f58103d040740d88600041150861550f52007030340d40540704051040c0c940a4000a901d080e540780042007980355441a102200c1c1c0488014204502c100800c0c0d0501420072502c5d50803805000401c50025008080d0408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 598400044 1250 598398794 598398833
    0xc030a08011404150e06030c030a03020705090f0403020c01081f0305060609010f26011803170a0501062a05032709160507050c120d02010b030d020334 66
    0x1c0002c80d100c1040102e81c4c05615507207000c8681c0b1418001e0000c041c102d2580070780040c0031950780509260000f450580c2c07522040700103a1101038280050300301344018980144140503900c41c1420300303a03800303500e038008030f05014108078114000404032400c1c0590040c450440d040c401ca0b003d07850b0306000d0388841c021201c85000c1c807601340002580418407114441210300c0d41d511185a0303114001011202c1d449d42c50103004d80d40d00c4902041081c0f0340c0d0a507403c0d140744030b921420720303250001100d2042040018008052580341000400403160803501500c2d011040d84800e000b00c0c1c1c0d5810b2410210188144052b00c540320100d070300d586000b000b08821015480000c500140c0c610303c00c00f00280c1400441d00c40d161543d4445020401ca409100644541403041c03054070352601181020441c1950b20100900c01303035009585c0d80300703603a40a01c15000f2588050f000b60011603900c2d4030180d0740340302c0d106418081d44038004450300311042541d1500f00c20f0404084508142c0100d00300860f07181c01100381101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 598401294 1250 598400044 598400069
    0x1f060531051905061201080f07060e010e01031407050703022817190509210717070e0702010c110102090d0809040b0409050106090c170115050c030a0801 67
    0x502200c0112041084080c0340c000c1a2286082400340002d1184104140c54004810800851030b9919071024040c2e4281c5044070391032640c5091074482ca4402c030004016055040b07440f090041d51b41c081d000f020108400e0800300000407203880100d0042c0f94144906902004807818031142513030103001008220f01a1303080340c05851300c981000c041401040b00351004007000d640001c00080c1c9002c8501c0c0c80c0002d440805007404a0f00341c009100902c400b49680001700000381045981c0b4040070b01c40d03440020381181c001d29480400c01255030f01c1d00b9005814005030f030415511114841041004041d00d10400740610710b00f843d0b10702074041c100c002e201c10003003880a03105510300441442914800c040c01401880a8030581c0c803020600e40c4628000d6030410b8440c1c4a41c0f2258031035014a4020620030400054400c0c40d0400010854841c41340340030411807031484100b14030b8004c8140c0390660320f07504244001c0041111042e40c10307200d02203200c2801c0c00081240007a580c2c020040d541251107080200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 598402544 1250 598401294 598401337
    0x110f03040c08061b0d09020f09040c030b01120201020601180204030203070602100609020909060f0a09020f091305012303150a0207050606040507050a0c020d14071503140a051f0605 79
    0x94400400e07582d44104c444018800400c2400d1a50840c0702aa400680f600c0049059640801d9078484122000c2e550384041a20400070003400381d9015004000d00d60b0000c0b04000d05600003911404188104c00745400030030114001141c49038103c40c001c5030b0050440301100d40d5130300c001e5101d442804802004524007080001c00c45064001c50b04101401401d07841156180350800000d0804154a02d030401d00c000c0300450440c0c0c942c4000c0048044c90115a0340f02c01409080045c4070940c0d034400ca0401c1e08040040240c0030300c50440b514031410290f03810611040c0c00021070305d03080d540c0c1c243d000d2880400041c400d8106080c5d0081c201d15000c4c5050783d00c56035680052005655007070f2040070010318100f00c052241c41c4600720114a051000300b051302501c4940d11025009400c0204109030341e041414100001752031813130000010005130500b400bc50307191a070161391980000f0121600e0b5512500054446866000b060b900107684200113140d107519040010102e81007080219078080400808 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 598403794 1250 598402544 598402561
    0x62117090a0b0d060f080309120706020606092d190b0306010902070c1509050307060206071d1201050c0901230d110f0a0e010927110f03040c0806 64
    0x315695480c024101420440c40c002480c000e41e8040711510348055a68500440c0407107414000400404008005540720802201089800c0c03811825409583d8020350081006a4000c100c16a003c40101c3d41812240c0d0f5035001110704018244030010300c41302003e000c1200702c030031405160103107240e4546203035003ca480140c034044401101c0b410b9495800400100102d030b425800030001d040c131a600604000b56900c20700421509000c7e8000041790300c0241c2404641800c03c2088020000c501c01051141070405002e0b00e40d400c5545010340101c41081c002440d034607424040700c03c141d00c9200070411442d180d505604150042d006c02400182d01185100b0014103040e010107001d040f0214003440d10b10444d0869000788111088445108030a04c00040000c6240c00586903101460b2070f041241e045c0c04000405c4503680c2e8001c80d00e024420280310240e1202d00b14000409115104001001c503c0c4100c0080345019440c0f08980900c0f00004104c00c200c465001601110040001c880b031588034400c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 598405044 1250 598403794 598403797
    0x10e0109050601110f281a06010c060911010f020303010b07030507032606030c060901140d090c0e01240e09310c170604030e0d0606240f020a15062117 66
    0x10290105a9500e036080344c0100507101f40e50031034014182103500c40b006685072004d07142c2c6480161143d828406900c201945c10a6466624800b81e1004d180b6640c1030000d05202c03400b5400c40501041404a402c00c10180540b144091802c50841088041c40307007802d8508100c0d0049460b42c0c0207010303a40c5945200d013801c0c0280c958950050315411807408014150b14842d03000840728800180d04d0303001c1c03140071034181d03810f01025001c5c10381e035241c4542c1001c90b030346120300e0300d021100705031440e8031300c02c41445034801e04c54080100c1c00c40c0d4420705ca4661200002002c80340d42504c02d105610b480217480c040d441482d01500d002d20136101c109a603a65aa520710244007003801091641d00000006000244107010360110140010314032401101680c558500311011604240c501141300110640e00c885030118014000c94103142c01c0c904c18202440094603010550740c020208242d00303150134110740d00c03a00000701414400501c00080c4443d00008440f0003d02c0c0c2058400814072505258030107480d50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 598406294 1250 598405044 598405123
    0x4080f10020c0c0d210206040614012103020f0106140109050d020f12010609020d0903021c09090e03070213060f0f0305030906030a021918080303010e0109050601110f 73
    0x18003038042e2040036800c2c0000050f40110850358a0780c51580019800d050611719891107a060307008022030310302403400302d0842d00c0c056100700740d284c072101c010015040344c0c080c011a1303006041d2403581c5040da2881d040c0c0c42d00005200f0101d455081c07c034040b41c0003041c0141c018142c2001d0340e0f800b101c1c9903a002401040100a070002c0d411540102c451141400c0c4080c50b24142040440000b482d079540303402c442c0807030300001c0c11036030a1902c0b11201c03810b040e8100542e101c0ea001c416040d140382c2c1c403031060103029041c8602c9404c01c1036444046c000b8603a4028010780d003160344c010b022210301d810038001a030b00a064500581600388900f000100e203025200340c41d08140c0358408011403a2000c4c0d0020082ea9800007003c41001907000c0110040620403443c10504020891711001070708080e06803880c02001d01d07504020700c15482440100000c2e080c0101283c11224101400661f60319498012a102c05820491801520400303047c10900040042c110b8420500700700c8291504000c0e0225444155800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 598407544 1250 598406294 598406317
    0x80c15011202060f0d060b27130506030a0804030b07080f0c04030308130816050606040b09060409050f0f0c0103060b0703050703181508040233031b04080f1002 70
    0x2468070304014240724000300000d0ba0001c6007141401171982480d003d9074020b40020103401e8010401d1600d45135101c00000e10320145484108215101c01d003c50841e88400d035032596400d8032240030800e29241480380418058115198540d9076403030f0b0401c1650031a06481c4a400500402d0004d038900a0400009014840c101d602600c0c1518545048503111030150000c01b0541a007082d410008011070000e00c00764118144044030154281089400c2200051855000740c3c105000c1520b2a900d11451035840b8104880008001081d414040d180450034504c01c41a441044070b80001c000000a2035400c000e026a018421544c48644210781401440d5000340410310920101000078003079802d000036241004444440513071b85510210707440e05442040000b20312a841031005600b03041c3d02c2c111204120130482d04078119414101081c141d021041c10112400c003001089400300c00c9612020014450851035403101c0e01d50b1802a100d0071649140c002904c0740d88500301c040e204600a0701d0300700303c4c079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 598408794 1250 598407544 598407569
    0x213060314011e030b0403031d150a201308030304030804060c0f0f050c251a03060d140102090612012d091d010912170405030405040c0219080c1501 65
    0x541c0e1702c540c40e011003d44204e05058840101c6504070391400c4407040401c60280c014550304540e041034400125024002c0f1144030b0804560310119400c0380019602c5c0740d1590182981c0d000824402200849a5000780151740000801c2c0401e2681c404841406a07005c2c107000c105500ba011802e442c014080c01c0c440d4041074a04105501c4140210058100390f107405054588e8400c00d003074509034942c03a00c1c410409005c254502404180a15819200c40740c290011040c81e504000000508180e4142c40083c55808c10800e900343d90642901a903d1030800606010b444410501d49080c2c003420902644480140711001d04054440c480c041c0728043c2c481d50400d070359940c14400c04401070300303801c40404181141561000e402403030902c201c04900380070b00c441c00e01c0741c0240d61000341035000403015500d0303884e030380b40902c00410004400c58003107448c200c40c00503108902c030342e0690511080300d10840d0303603900c0d1051450078018144018684016014241c51200c000d40c6440300d2454001c0c00f543e07400c8440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 598410044 1250 598408794 598408799
    0x10302011b03031823120f131a04030b0a0c0f230c010506040524040f0605061c0b010c0b130f0b070908010606080c0702040b040213060314011e 63
    0x1801076403680d11900920300452440542c00e041030b10f50000680480d03400d05036100702e60420b841c640f5001441522807000e00002d100b0303158850010301418000080700880040c0c4140c50144030081003008002081c14a0046840796289000f00e4220f1310050380c0c016411800150000a640300d10380d6224082e45512240c9a446513084404101101d504c9640038046058503100c1141c082c06401d00d080b01c1c0e000800e503031805005110039500054801c2401c150521805120307420246110303426120240e070f00089121100b03203000007500341075200b25001f900015400491440f0010a419150480c3c1428425001ca1344011502d81c043c0b180c008e030001c88410040385030b8100002150310228001e844c0f54440d040e0035140c18000307940c00e130303881c0c004941c24074420004040280a204014802c42c18000e000f0700d0110406955132090800c000d1140c0d0b030324800d05c011940c507a8150756881e035254140d0401d07540c607140060021300002c40f8204031000324200010f4140b141107100a4042503030701d0903107412807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 598411294 1250 598410044 598410077
    0x8070509220b04140a06020912030c030f030c090a061101060f0803041814010e0103260406050a0c0501020d0f0f02030c0405010813061a040f0b030c010e040b0307091b020601030201 79
    0x90140c4100d8020054520015031214200444507001b4003564005039100c102c0c50400040c01d204100d8028180c10510060340d20002c040240da02060f081e0f0841c981e00e03560700060100c64860329501da40c0c00300480001080c62a481322030603102c080c3c7c9100170845142c940c00050024070803807040d6030b05540108000e10030300c20210354550451011b95808100c0c40b2601c040003445a100340c01111040103000f004005000e00d44280a034007210942d401030901940c451119802e1207580640401d2001c00241c00e0700b4540b0a13a4440702041e0058002c6440350b001c10f01c01e60107001d0003c03050071030300d0414603103228102843c421607008501c1950402d150605d8440156403405004142d04074182031a000207010072203501031203150319004881e40540822090400c001c541904003d84401c520b41203030300c10140c60010712481e040e10300f400c0c0010413480308400100a45254000c2d43e4050290000004504c0301c1c5400c141084183c170303400525203540d480d1040b40d41e0102440701900280c181e10746920701a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 598412544 1250 598411294 598411313
    0x30c0b070e2103070b0a0c0f030212010909023d1d010f050706020d020714010506030714030f0f07080c010c0b0105060d09050f060609090d081906050a0807050922 71
    0x1001688207a0341030102517128504884004c0300c452600c140c03034240000242c0d40c02007420040b030340f40d81821814024240c1444d00625014001c6984695803000310704113540c1c82140803904460414405c0c28250304041c2c821003141e1000b004100044000e6000d0118980101c0f00c2c4808416101071130316400281c00d0044500140b54246142406000c20480e40803416500041440300a610409a62445149030012130400c0e07801c10712015900d0401441040e940114182d0101d8400440c40118a8403803400607003064051003031118036225200c603541c1c1810001c6640400c8405110a880b40190118010350f4100d50b40800209110f0400005209519101300034000742c2c45108000104070310b00382e40f520326008070601c4801866000404200c0f0503e000241d5541c4070b00401c0c060108003d80b28000b0303110f60310141188142c8640c5c1103000c80703903c4c0c1c203610080041000502c081c1c3d0b8941c0d1102425101c007042c2c05924080c60708880010146140078003040c000004c0300c141003711000f16211030420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 598413794 1250 598412544 598412599
    0x303031906080703050102180a030510090611070302160b03070203120702070b07050a0c08011e0209060706051e0906010605031302180a0e010e0a030503040b090c030a030c0b070e 78
    0x1116036803107000c02d50a0007001208051403041000607661070b0704a41441004a4511320300e80f0a0044000a000280c4c000c0b82c0100c52180340600411514000e2030500007a042544a040ca170700d001060050a0540c0010068030407090001096491070300c0c1c5800b440207120895a58025030b000b040b101802d41501054140e00c525548165554240c840401c269141e0082005892a40c441d198650500429070051002400c4101c0200195144910440e02210a03116240c086c0769000c01c2440c1c0310344031641101e0b80f40b507001008001a1070b141c00d00d1050240c0d8481d2109003801c01d000020120800080d40b103058910705d4035001e0459480301c0c145480d00022880403078100b8018012031496004440303189000e4406040c01140320445403024908480c0108085030981c0d000580e110007098014040380d41054100f900350032590743d0500a1842d100304c0c08081505841550007030001d00da0303c5012026060300c1804080305c20b840b189022219500401c0c6e40d240d010007841e40d0040410348a46d601e201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 598415044 1250 598413794 598413841
    0x10506121612022703011509020a050c10050f0f13080f19030203011e0e040623010e04030e0102010b09010506030a0b0a17010b01091a0304060b0d050129030303 70
    0x65144402910b040c0e80010780d07aa161183d044074400b50035400d140c5981500141600200080407a901c21100100c400d4070554024650024640c8005403040c0101c420141c00002241ca0202c0c4603c038040090004840c071030555040000404c2501c0c0500d00e07864007400c3c0c1000710404030350f515100d0a84e5035221941c540308131031041045055811100f0f0748011100e005440040c0c0340d602d040d00111400c0300c1a11500071401d02e0000c140700175180c1d99461a0046c0d0004030000b01c40100c0c400704400300d00d078400303103c0400b05800300000f202034032840c02c40e00c1399100342e030b404500320282070040e800d80700c8841e00d440d440740c40c4800601840c1000005958416500c40b0041018404034021444072002c6401c8480c0044030040a2001c5460900903a64104002e1034025003a41c0f034207a407c46010388100464502e07500c000041401e000c42908042040580248402d000c03c03100c0c41d14a00030006c8910480da500001c22008000c401420100a16451301401540c5144c0d1841c00407000e42c0492402d1f0f15 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 598416294 1250 598415044 598415057
    0x1606140f0717070b070809060618010b09010201020715020418060b0304061512050a0501110a0807050f13060503040b0a0209030a06020c010e2a0a03020d02010509010e150a080105061216 81
    0x5011400145449004105c0782c0c80c0d2000c5c0d030a00080780d03424080c0c0200190b0180c2480032140d1a00070244404074112511100f440c0d80342c101800040340a07114410b0090171540900021000c080c000340d0050080b24140164000d103442e00340c01c0314080e00c07414822900ca000c1e0504c00130740440c0150308000c3d110003c644112103a607842d030041c00b942041038241650181d004a014800300710092103001c1c40b10600054160401040682c01410810002c0c10001040000f0410307080f910036000a44180001c54a4080c00142d00c640c0006d0194104507030590384130180d0408140e005010348210b600000c005809089003501e1901c40303c003c2d41c44000710103002e42d41c0d00405008650140214105045260300d00c076800065113080a640b50f00510781948a030400c2c5604100503581c41c0565410030b0380c203082060f00c801c0800d00594410385504d1400303802401d641c5c0240340080c4500f000708401e04058450803d43c0e6200c2050002c00d00841000c107240546220200d482c041645420300000c01070761501c04d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 598417544 1250 598416294 598416307
    0xc10090b0105130b100f12020301050901030f05012a03140907120206040510020109050706020c0102060a0f152702030f0f090f10022109071a09031606140f0717 70
    0xd5400104048001c4c00185004843c4141c9079004000b1f00c4a5000b85e00207500315410071001484100c41031100a0541c8069010b00080110030340280342d0b00b041410010500100020300308000b04100c425201c0020b180034888610a100422100d00414802d8024a861801c7c038106020300020b40c40182e0344480c0a00c4006919603c080441d0155441b45c0d0010900d05968548985020002c0c0c020405642020858000c41d9a00085065006032205030209941058648030402002945175039030200200e404003090140c0b102420326902140f05220031044003842c220703a0200c0c0420b9030051003107840300d00401d072026022a08079400110103000d83c0d00b2090882d40c000e01d00322605a000d5030407038004c20303010125110421040e43c071412100300d5003954503100300442c0e200c0c401800b90300e030300c03a00603000c000d0042c402a00340c948030320f40a0200c8602480d4500030421a40ea0340c0300700c0f000105191821007014400d60b0079501c215049511075401d000c0d00e42d4840c440803001d0040d420ba010b0050180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 598418794 1250 598417544 598417549
    0x60f020c090a020a08060904030c08070606170601030c210807030525060b04020a0203030604150f031a13021f0c1703070f020d1d030c040c050c10090b0105130b 70
    0x810300402d2292001680c0d0b00200328042d040d841c004013100e2003509050308001c0400c2d048040005120b034000d004582c2c41d421450404000d0182d90042444e022940f0790107141004002a0141a01d00071610701c80500d56804074050004801413001e5400c214000c0a000082c581d180904001d500c05e051181c100035004900c42d2800040a07030741c295078101c00c80000140f0166101d00c0151402c01d4400394503190740d405029690740300251046020326030320800c28518070070107080d01011b030045460701d903a41543c90a0040e0301e07081001030300000c4c0d040600800e51516003510f641144683c041c000c00342d030280c044284000e0450640c0c4003030031701403404083d0340022803803011100040541c01e40d050300c90401e06402404240b0380c3c561901035504c4282806001d07508410700303407420a03d20101d00003400c0c07840086030074160f08151143e041401c00019002498100000d055610304d01000c482000d180d4180c1c2c0c00541d11103000203000c0094100042c0154100601c41c0403801c031241c0703000b14585460b80003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 598420044 1250 598418794 598418809
    0x406021e1c020a0c1a030103030e0f040507050c150f0105060a051608040612050c0d02090402090d03030c020628050a0b03070b0c010b0901050616021f08040308060316060f020c 77
    0x1e03400d0058200c010080704021943c01c440004e003541c5600402492030200a00920340b20601018040c0010918581041d03601d90718104a80301000e0070900260070f20080192554100544080080c0910803c0800c883d04d071207409032107080f100d800e0700d200b03918180034071610750b0162546004220003040b02e2000d039046480441a0f083c0300300107140d034951a200c0010010007400c48442034250620080c0701c10704180200780c0d24a2481c1007401640c400220001a00038468560020b8101900f001c44009050b00b6a2103800f0040498003540d16598844109141d83d841652890013080d42c500c0d16111064101d81c040e9500030024900007411404050000e0301d05006039000d031620500001d5200201d050030300a03103a01100548048110354104000109039001d0b001441c015049081301450540d507516100b03111210071040000310480a10900500100007194154081014000460240d0400190200311144600c2050040d40e05001040f0780c01c9260a20810441c030500076402190350300c426 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 598421294 1250 598420044 598420093
    0x4020c070e13060c0e0d060f150e09010e1212060f090f0a0b010306080312130b01080604211709030f0a081603020a02030f160602041203030b060406021e 67
    0x1002c079107010310615080069034041403045040006050100600b40c4484070040d000315070188000ca030580e11403a035071000382503011400d40d0820f199030001a80000d1001e46501070b8281c04002e000039048001c0880d5124245024400418004c10412001440f140c10890b08840018101940304003268001513190b80181d400e1805011140103100c5d404c1018400c464800c00d0a09041c03040701d180ca00480e80ba0b00030880b0a10030446404002a5a00700e800c1301000103d900420700d40d403c0d43c40c0c845840c0ea40000700c4044a0303028980440101c1800c200c840b800010384d0711f6491a0440c0401144005401d1000e41070666900c810b00207200c41c03001c20405022504400d039500e0003540b40c06c0e6110a5031008201c801000e1501c1005003450b100d50200486085140d083c0050b580da1950090000000302c0082c4050021403000c44c1c003144050030040c5940b10305005c0d90b000d1162508100800c6800c4c0304174440e500259000d00320b0329151542301c0d00fa804800e0b59110a0780c86107042c000d640c034901041d44 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 598422544 1250 598421294 598421311
    0x4020910020d180807060c1103010203090f12090913051e010e0c06040e010b0a020a06060b2703060a0f0902040903030903110a050c131b030c110a02030a0204020c070e 73
    0x4030b810b420b501c1d8010a05204a001c000000000b0340c909203503241c480c00345016180400802112580901014401c181c07a0302d000900210350f80d141082e11162038400c102e9001c1454042d005c0300c3c001d81d40c0366030182c40600790001d02c0304450b62200080c0c001784201c40b5000b101e840c0205204034144c09a00c290346008900c040c00041104100b4404a07800e0a110004a521490050106121500c07109e48428156400355100565940b150f20081c0c0c50a0002d010060a9070706041021440400c2c1902400e0414900c200b154031854500340d8481e25164001141601a40854001062000301c3c0c2c000000000b40e04400107010000e030f40101c0c05480d070503101640401d03200c4540e0003c05611240080118074043e010744201401c1c0e80e01d5a49844400301d41a204008240e5203246035030440d407107003064040480301180170450035140a000782070b10b0300120300030980c508120358801d04041408602560b0040c05444101030640c03c1000075080052012103500c10f8804c0130071041c0720320305400e0290004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 598423794 1250 598422544 598422553
    0x60510050a06050c0a060c020a052b020102091f120f060e06011d2106040c080105010f06020304090203070905090414060604180f050102210a0c08060d08090402091002 73
    0x14541401034070600365000364108801000414a101d001040c4c1c134140300e9220a01150940c65028101e14115840c90047c0c141d0061010000050002d55100f83c00c00c400109100546512410260300b00e001d1a5452a0481565240140310500754803c00c00c503c00310b03040c00c406003800c244503003080301d01012140c00c2c0c0c41c3d40c1d101c0501c0800c0c0881d04069000d8801d2a014020b40b000c1101410000e41380c2801500441200e01d00840030201003900000440800040321010301c0c050a140c142510301d03100b070304919480d050021482c4000c0e960600e00f559540e4008501d0145001e0070180290310041164080144151005c50641d0340c01010500442c050710000340e50403010030541c3e05001000c1d10b0144540c0c07a151000a44044036202c021031203400001c1640e62251a0510602910501c4ea648502510741c2c002c0d801d01035210701543d4002e01601e8420800c484d207518003514800029030790382d903101c1103036100300d400202e04000424425070098000740c00c10380b5040100300c1c0c0002046946000d41c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 598425044 1250 598423794 598423799
    0x1c090f0603140f040312050c040308030705090f0604060507320f01180c030b06180108010e0c092a0d0c03020a0e030604030e010f0e0a03030905150c03180409060510 72
    0x109108035030884a11000f000181c1003640c2d001d00b03244030032a88000c1103919070380040d00713200303a40d000e4600560b04030980341e0303a0780b8110f00c00034890303071004070041c1c411006840101441d003402411f841c199055078030744500d428510303105d0100c4000d10410f030f00301e007003456104003200c01030403089141e0400440c40100f54903928544290709460f051021440b103981c0b00e10311200880e201394400411030b5040b103a1002aa21000085a041105c603c810b00091003814000201d99105601003007a041c1c04c0c000b47c0e01c90140e2501005103003032045d55a400e409d03600750100c409030200074040150300e034000318100b881d01401703076489030079a4070783c0401e9800302c1c1e80821500200c581200502103500011405041a460b103960058210b10200b54014104908840d41408140c0154241c0c0700e2020028100c2010035520f02c1c00806e000864003905001e480851641c1000c00740305807e407030303000590002030341c00c0c001031218149901d0990b042c0143e10079103600e090800b03c0e1141c400c0700d0180f607041e05500300b00750 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 598426294 1250 598425044 598425071
    0xc0b0a080108160603020705210c0f0303100302011115100e0a0207170306060c0a080c1203040c030f210c2109090e031b15010501111c090f0603 63
    0x228164401d10740354018156030141c0700500c103c2c0501350790542c00c005072030b006507080052074005051456030711181c0030581c43c4031100d10760000d0041080390904461000c4100c0c3c1100d500da000a40d850101441800d50a000540c040ca030038562100e202d0084501d90041c1512600320703508151140d1100701543d20044c00840c8140d40042e601081c5014198030f002e0b210b940d00c60040c1c0c1040400341854070040003283c85580d60b10704550803400c00c60220b070814001414003c01d10781c48182110001c7c03054042c1d491450f114070341074911641c0c01054440381e962454407600c40848903841c0403200b01859050700e900d0908003200d603541060481c0e85c0c5d80c041449610781256203494401880384090840c03604c80340c42d16404040f000944552020210302c5406c13022206145000d803552044081c440715002c1d40101c4000a008070200303003010f180c100507903a98001901c10070042d8000100c1e50300301041e07440307030103859001581c19034140e483d00015003952441c801c450601190001c01c00039489048412005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 598427544 1250 598426294 598426307
    0x30606010503130605090c041104090b0a2102060712110d0504080d110a06020309030304060f0b060d151a0901021e07120c0e01120213140604180c0b0a 66
    0x490a0801d58a5424102e0050700048840303000201500d880e10005070b100081440203102000000e0801e02255100c10000da00790b420902400890714504200d441701031406440c5803089411800031a814445800d50840000c0a49801641c102004102000000302c6003000d14070a05801e80d5416001044100380c1c50a0500c3c44803c3c1c010040d05200610a4600102c0ca00500c2c400791300f008491540000c0c00c0b1414852000d02c0540b03168070110400c1040300d004001503104074440c980420500d10310705521421030f8140742e21a90841000e01442c0750340081c581c00440d048074510b1602131100e0360350102118101100c030f00b0f07100b9207070042042e1210f560108050620b081665200c0441a015061450340c1d8803039900c140f12002c403048101d20140441c000c1301380007078518170408882540c0c441140706511505800220300402c0c031106007000040c9103210340f001c2140049407030200781e2201e81c1000050080d0b032408800c006230348000c01d800030300c41801d09001026209a20384c1c88003540321020303115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 598428794 1250 598427544 598427551
    0x12010602011d07140a0b28090f03020103180c0303120b1c02010c02011707050a0906051801050d060905010305010504060c0f0903080307090b0d0f0c0311120429060306 73
    0x2042d07035440016107030700c0012407200c050b90b003181c04540150f000200022015007a0342d1081107600d10014400d40a40115003103070f900c0507070009690000e89030000f0103d8030821a403148030b8070b01d03101960600040d8802d400c0603004071074011070407040c8202c0341c581c144003101c5036100320040b03003507000d041c1d00401e814011040078290031a4a10100311606210400c6480c0e60700c0002e041112400c0340004580c040c013240d40010784504503103001031a1950001c2c0140d408080c01d0400308980c0007002810f14802c40481d01c80100d41710800741c14004d003d00554298000350342507100300782c81c0c07400800c4c1540a48540c500a40c0501c0000c507c2d41010701b440310880e06904890001c0000000d650340e45941c01407140d030100caa0000c0d2441d96980e0b04102200c400f503158119043d44000001c00d00400013003a0884101800324400c01c110851010344158121075a282040360486003d1096103084010f004800b5407290051440c14014803210a0b4888980380184213140c02006400c1408054242000307000d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 598430044 1250 598428794 598428821
    0x1c140f070206030702120d0902030c0a080d080613020f13050307030b01030f03170108100e0d0c0204021303020d150605010219023102040306050a230406060b1201060201 74
    0x18201560840028a1080c880081d0040c04004007186034903208005a1a648440076100e681b04c032821a2000080c00950741c00340d01c288608501c0106616244000d0422545d05034010008030924142c03d45552a005100d140d10400c100c85441e40203140d0f0009041e44030090741c0719503407900c40a042e0f10b14003c40360002030095014410900020f01c0f54020907042d6038000c581c1085000540ca821107103420a8a0801300f4044d120b40009010100040c940041400030202485400c1d82c005001d96203814a0702428001101c88601801500306540101000b0a049a80c2c4d00340315125004900d110003460b80c01c0b00c01c42c80c5450642004103a501c1070a02500c004d1003e040f00c0c1c480f05850b01626025600040d124580b5810041c454951070490000b40008810001241c940021000b000940042c80190f07041d0f8101000130384140702520034289184ca10b18000390940d40081031b041706010005004481b032903a07951300402d5080340c8001411038404481c0203910550305145009082d02c845184000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 598431294 1250 598430044 598430047
    0x5010605100905310e19121413180c17160c0503030f06130203010506071103031e0a111c03110d0f3201030206090a17030703031b080c0a111c14 63
    0x180019103001c44008107d94501c0c03c0c01010702d0034080141d075485058440c403a086900b4400050848071380601c11046800300d04100111000d03400305940e514085002c554003d502ca2000501d01341081d541100c00e05107501d80700790301e6051543c4861565009880404004d40f801d8100011403505046982d0100305900e419400c551410000c101e441c000d6076001820a0f01c0800c0800071034070100140c0d404e03401211600a65491041d080c0c8080764080003030840000c0c008003440420780f00002e001c030000c000c0c01d400042c3c50700000d0001c80082c1641c0c91010746c2d1050800c05200c6900c0700d4040c0341010381059000007407000b5900030300b60400c2d1650381001500b60f28001c01000141c0c00119050440b138068491641d506207903c002071320a2029001091140e01404001c0d02d00d040000107810703220700c20748040041c40f40322449100c0b50b4964101070710001e000302002648440b805800307040ca8824500b00480b003125030000503420000314100000d048443c4c0c5d000003101d41c3e0f0090202c00018070000943e0f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 598432544 1250 598431294 598431343
    0x10f17091b240d020f030703091401020403080f030c070c060801081e1908041d0402040c0e030604030f0207030b07050d0c36090203040f05010605100905310e 69
    0x1002d80c02a45501007a1114081440d045414070382c0c04481c40800b031100a07594034a4600c8000d0014404000c0965400b1400c40c400264035105200f01c5090342c0c0c11150329030030003144883c817103110703840103251001007001400664000b401084203040075240c80d461b10a20713981051041407809036486148040c0c040380300c03403603c00420007103480c01c0041300ca00e9075162030300c03c182041261841a5800026070142e1421100c01849200003030600543c401c0b24103001d200c45d260411560a00340d45035655042e0840d00c0410006402903c100302c1245050064568041e41e81e12815268602140d4101c0481e000042042202c2081e00c240301c0607015034208140803000c000d4603142c0c5011040c5c4030013411024090604221000c1d4145180140821413082d540ca1400e85800303620826181c0040742ca940c24910080313100c0c5020791000c07900c010190790305001c10749071008009020b06080c4804c00c440d400681e41051000421034600c10041050b000820b600b1800c0d08000c0c0b501c1c490525040305581c01c074110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 598433794 1250 598432544 598432579
    0x604031d030114180a0803010906090b040e19050a020d030302030f09011a040903020304150207030506010e010e06040c120c200a1205090109090c030603020a0e15010f17091b 76
    0x20542c01110040c54500765103d04800285030074441500a4400403007c00001005000c03070704101d0664420b144140000b400341e80c00e001c107440b8040d00c0d10310b254010750345040416041c0886030b082e840c0a0002c440300b030380003038010801c3c403e1480c0d0282c00180d0000704001e0710980c00f2002540010103030008000340c40e88182d030300d6510030071460280e2040b40c954501500b458400c00586000e010500b40321301c3c5188844401035951040d07480103d0702c0e4001c0100004d61005055451030407280c070000c8042340c90f5220380c1004020040d2001344010b0250415101454142c140704480a403109600c5140031a4030100c1d0041c2c00440d503404001d50b46e40320805210001e00c841d41710b520002c0711403c1407501c80d00b0044c0107031076050040d04070841c20761826194400c0c40754140c000f6001c17a4000d80341003460540fa11480486180112440c09044000c50740701c100552043c03c1c0f03042e600369249420340b503a81040f00071844803441a1800d085680c04200c0740b820200c0b5034030500c507000c402280c1c05e00c0000d000005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 598435044 1250 598433794 598433831
    0x406061415090d2001030e06070504121a070e040b0f1e2e031a0303070f0201030b04060e01030c0503031201150c0b071709030f04030807020d02030604031d0301 70
    0x1c0001441008100840542c0b20020b841c40c00035440001402c800e225004070052078503c8589060000f824000b090325103620200390f20707000d1100c6548062501d0708003032464414000445044404203820203d2200b02801c2c610203174091915603840408078240340041000307560f6510303071003480741c00800d504840301d9441c007108007841070007020038204007502e100c0083d02c24020240d51503915003194900414400c0481d0b002125032942e51010000744a40c00340000800c903580b903003582c0681c401c00013000407034030946004054510515010810302844d0000c0b805841040d40098100d0440b02c0041c400c102040305020043c00f410707401941401e0740b007500b4030b0b110350062107060240c5251441c0c110744070380320b20140400540c100503500340e03504010600400260b84007903402c04219400022403030300d62001c41181e2038011500e00941c2403a00f56201c000f9294005101241d1000090fa02a40140c9050000f248240d000e5195a05071060360241c0d1020101c00d081c4030341c845e9240045c6280c00101021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 598436294 1250 598435044 598435069
    0xd0c0e01030c090f12150c0807030c09050d140c150c0705030313030b07090815071e02120c0a050f0307050d030e0303010306090809030f06070f080405060721021204060614 75
    0x5a540c0702c0f4144030304003034290507021b80d80c1c1c2e440d160920006003103940c0c0240c0d4060140c02c081d98100620b500110045441403094040c581e404050588220040f40072520b5036940390903100d051720202c2150b000000c03030840342005010800440407502d00e659180900c1000001e00050700a1498200104012040b4070054040204920040808100c0403031190340500040c0c40c84000f00c4510884088090552420449100740090303076144100c22a180d0078130090301c58085580003021058464403c1000c1500003007030340e030380d039120340c06084011a20030050150041d000c8800346d5640d44603030608a0034051100f491900f45410b1a4008804141c008102ca044981105002440c261a031a004a0500c41d40b07401c01c0e814420500352840300640401c2c0e03035000704101d0300c2c4e144008407803100a40c0c1ea0b140c200c40142403030304400002215540107000500e42003c0c5424405d040e280c010854000301e07003103054a00b00d03210707014040208020040c81003c000d07000d00c4001104240e840d000003098200070350b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 598437544 1250 598436294 598436309
    0x8011409280b04060603060b040b031c0c0804030c0f0b031302041802061b07060f1709070506070b01050901120b190213141813030509060d0c0e01030c090f 68
    0x44000052844400c504501c890750010500b205400e00e400c10a000d17004600050b04c10510b0015007407000d25091240c0c1c600c0100240141044a0051384011950000c0352005028050003e02c2c04000540d1400140080c0d40308810070141d460604800b503e0786542c581100c030101c43d040040c00580c0950120f0165110b604035008140c8a8001032200011840c90200a4001d40041518000840d0f800c03003010761610f900d400c80d103c0030f40c0e410301100c6000c14a840b07000800c405000906d8240c0441038460362012404c0126400c459039203000c42d000703921414082d181c40840310014000c0e40b42c2003410900500103925040d179050480e072182c1c1d10b00c150192a118071600d21900600c1c0304201c40d010b480110f481454850794460b5645103402081544080061041e640580009420850b4181d002e019644804022048520f10303a000d40f065440640001d600c181c0a028918400c403841c06000010112a9500b0b1000c0104c84005403d8444240041d014022581d909000c41c200440300d440480346003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 598438794 1250 598437544 598437583
    0x906090a080d060f08012a0c0b06060c0303180d05030c310803040602010b060c03030705070302030c070320090115030b04060e0f0f0a090201090315020c011508011409 73
    0x42c0100c40e0003c0409900000919a03141d100140080044d8020016407850303c3d840000d422600000907000d0039002c1400002c51003010310400854241450243c4c41b0f81c01400c04c500c0c240910b4585451030300211240701c550340881030b031452201c100744481d41000c03560341042429800d0010031490180648640408035040e15040c80c0d50350807065020039150360303881c0403030380010751a814900d40705d074040d026010266080244a071300c941407000c119160155075034003550864070350300b008a417a82e00c001c20550440c4030500214841400c18015030005501c140b4010301010070f62512210182c1c03a480480f48194090001007003090300380140785840d00030b64940020010016000980242010b03008070b160002980c0411071410750100c00c2c14060301101381d4103a001c2c0d40d06c4032640d09032200c021000340040c001c5a01000010340d02642c03945079003c1084003500307100c0300d1004642102c55400300c510b031452140404003c0e81c0e0003840390030424142804004004d00c0d041c0c22250307680200c0c5450f800744400f07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 598440044 1250 598438794 598438807
    0x20304060b0a091b11070b070222091110090e130b1e09030a05090910080a03020c2719200910030203070f080c040b07080d050906090a08 60
    0xc0d81d90103030046540042a6a00030b903220200b100080402041e081d0b1440610f6109603400f07402214159880900c0200030064903042400013400c94010711412038010031000710081800d0080351002d0f001820840340010040c55509240003420464510980a501da45001d04000c6174441c1c031005c10758000c0c130340241c0c041d122b0070452f0100581c18800a000388594005108041084922802e10344c0d240d42c040c810151956040c264480c450070f84501d003c140e08202490290610f000340300e81c0300a01d1a60780c0310321540c59043c075080049000d0b080300140c0202403051410b1418140c007105501f40e100c505915404d01210200600d0806008511038030105401860f040d201034005505a2523520001d07a402c000852080c81c20342c001c110400c0c030941800580d8240a0312a200780d0b440b07030481d90ba0708142182000320a44a1042c05800c226110300d0400010984005583c0240340d503d12840b2a03c0d541c401c0068584121803001d403046c2040e4000308144030340c524000900f10021a04a035980d40d581e03a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 598441294 1250 598440044 598440053
    0x703140708060d2012060a051b031501030209150c011a06120603031b071a0307050418090506130b060d08040522090b06031e1018171312030c020103020304 68
    0x152064040b0385e000e030b0a11141225241e02051003800f9490121081c130143d2a9004515820b81140a409018250600c000b0ba051400070700210030060042c18014501224000485c0e000e44001000c00800795000405038404a030912410405604c0074601900d0903196000054251051881907104035001402262456500b841101c01c8041003414024580600809182d00da48081c4182c00592600040a000010890044034412100340d03403030a01d46400c00e0301c284280c0355007426001c48181c0d00c0b5021070004a0400c60f16010701c0ca40c4042a01d1160b2605e88030400d4003000b001c0310702401c1222190b9000881d800151070584104035120b2400c0310011796040e200c40c0558542e100850705021b03460b0309100700c0e040341034060030082d4160b40e94007084501d160b00300842c3c910190501d91241d030491070071241d60390212111009103000d0b074056030001d85802c69540c00b40e8140c0c01e445240012450305411180314404003c1c4124800341458440c5524040c01e0984241d402a0516800100207070800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 598442544 1250 598441294 598441343
    0x30f131e0c0b210702060402031504141509070f301a190c0e1201060905100f05030708210f0313031209021309080c060703140708060d 59
    0x500700c1c060600c0c0c4800d800002c254081903038980000100f900f00c40030039038881c07001c9485441290060000e001541e04502034040000e0b000b00103880903110510150410117007488905e0000748640c00700300303c90400303420780c03070034451075500810400503240c3c3c0c01c10400c8040c0c00d9059440e05441144012100701c030341c580c0c05031001c2041c002d0111142200020311807140a0341c240c003441c04655110031040c418444141115a1138007003202290041c8240c1e00e607841e20041d00c100440380c140004c00e009945603900c409a40c030580b022160030520718014401e5246180e81b0000825048005251040c604002e00e80ca030f10f1014000508060840303042e4006010b4102110207139804a00390b503079a80b914494260003502200c2c42200000c401949244a8907900d004041b080c1c0d8006100b40c1c0d200304048540c60080c00c00e0901280c12400900840c0200355040c04200d200300d038591000300d08003400c0340100c042e0041c01003c40003400441c6041c010700303884c0e400c01488000c0c0d00074003c010314a146007000845 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 598443794 1250 598442544 598442549
    0x11130b03091207060c080a0501050f041d0307050604050d0c1e110a03150b0306060f010804020a150f110106060f110f030f04080609060108030a050717030705030f131e0c 74
    0x1038100051034804c03c440e40c3d201c4d0b492018640d8600c0a5070311445645010380d402840390390380c0010111022040c9182960003408100200d0b5001d0140b4143c50b08020304507005980141e500d90496400c01c018000c0030702001554641074608284088490b6481855282c1410f40724074215904000c41e0003002039401004c20004001486161070940d60702e0080341d2064030500b201006030911020800301c1c10001142d03406400001c0c03040c0441d4000c41d004450104004005aa02c070038050b400250303034000f103540d110400702c0340d5441014448900030080c040000300941c00d040341e03240c208100711241e803003041c0803030f84520ba10b4150b581c64130b40c02d8410301c0c00072001c0360702c0840d02000944429502c0514014012a0000c0064409942d201250507031240d03401d110b41251604100310828410f840380c001028154498034601c0b031200c50301003200c8001c0d00100c0c3c44001045000050140030009000c800c2e070f01240c3c8a180841584841c3e540d0b030000c40d0100558a0244c0c0310ba0781010401c114034800801 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 598445044 1250 598443794 598443823
    0xa0b072a1a04030812070f033303080c0c0135040204140106050c0d02160e09070f030302010b090a0513080f040b1303030f02071409070e09041511130b0309 68
    0x1117518821542103110310040d510384012840b0401c182c1c131501e021340204444d0400d511480594580d540a00d0311141c241403242302c10207040600d01200045554000c0d0101444950050506142c2d800c005451040036a0712041d048040804181d0f0a004e941c0c810080e0365114003041583d40c40e244086005000568001d400390707280780c000031440c01d41c444054010016808129106110b0250742030340c817881084140e540c1d001350400306204001210003c01d82042c444400c6031130050340c1d043c0d084441d288035003003200143d440d2611000c4900d040411305820400400040199090490b441c211409010000034851040446c9102c00d00002009841c018403102d004030b65502c2166200000320480c3c0c1c00102d0204500c1480301c0c074018400101803081d43d02400c01648564041e0b0200109040d00504075010458402c81e1075800703440c0c040340540564407411442e041c8102d005c1c0c240081d00d0074560403580303a0006214604545401d480194101d0301d8060301d403507603a1039100c3c400342011194100c0e0131 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 598446294 1250 598445044 598445047
    0xb0301050d061409011401090c0e0613030b0408280e0108180a0503090a270b061e09130218040914030a08010303030e0102041508090c0a0b072a1a040308 67
    0xf04e0090190040d8111101a40c0c04e403140c0e03a21203402c4012034690300c1425000030540c20301c0700802c0c24a00010240900350020240f00c8568a07074034403062850441d07044a1000b030110388444200c8440b88450a59140c0001e14155184042801001140500a26810400c0c1140820b1132100411403980c450300b10401540d48a480c1401e200f84c2d2603005180380ba024808071a80000e50200e00c0c280c1c82807141e0001020304406021100900181404020a070342c8150108000441c06001501d07109503443c030500010340303461210080041e6010340c118545a4a40100b004c0d02c04051210f00da0078100108580005291009040409940582c00c160700c950f4800020042011034100400074101c0748203940a11125502c0c010309403c0c0c1c0290310440744d4914030440e000500600442c00c1e1544803241c14200e449420b0402e000500c400916070103842e4240001400e0420f000003058071510071604400d071001c046c007100007107013040c04980c80751905600c09130154211900084003214001d5402c4460103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 598447544 1250 598446294 598446301
    0x40609060b0a0e060306030c0907030e070609140d020108011703070204020714060703060f15020f420127020703181d04080a0c0606080f06010f0b0301050d0614 70
    0x8041e0750b12107400b40700030030740b44080d003109481c1c03000849200d054090060a4076210a0092100d00ca50182c1a40103250b02c1d0011300041d0001000310100821580c1e42d017049503441d1081480d600459202810b001c0c0007030941000260343c00441050440e407000d01e603410114414028113085010300c01c0c0081d4003500000301c00080c8039054402c500c20340c51010036074200b5141c90909070111443e510444518181c1c01e0810050004203507800307480020140169007000c41420502410003c400380c5135000030129202a42103d910300c48481103040620b500c52070207001421002d2240d800c144214003400c030541002c20319548a4440d03019402c90800c10540d02c0300a180307000f0b015007515403c4080f040d07148441c0051001d035154031941c1070481e003507245a074603203da032207032100c940c0040702d000d052001504032100044c030b0510440f07005209a402410b011350392400094201b11060380030800c0303003a01a41c1880782008c8101140c1c1151411211001d09030241d1808002400141016084904080082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 598448794 1250 598447544 598447559
    0xe0f06040f030605060604060207060c020402041e182901110a060902040c0801051e0f0303040803040306200a030b03070b030a0902030c010f09062001090c080c1c06020904060906 78
    0x2500203a070f202d030b4800c0c007055840e0010b004003406035200d0000103074006a4100f001c50f01039000d1100307450002d400507241c240c9a6041c1c4122501e4003048102811031640304001042818202012110a10303030140300c1d892041400d250341c0709811100c1e0b28001c130b4081c48450168014108400c41c2e284000c00e81d01d0b00c8080c0d0500034020552000241e021700e0505104484581c03240c40401d06039000140741d402c2621403050007980302035440d59416004120f504142c1b50710ba9040000d400100010300045547d44e0031482c0001c103856a10b10403c4288055440d00e07a803900c0c00303000791103a03145545000200221b004000a2500700c49a002003d504400800c2c422100b05680240c641c2c980241c0032141d980124900450b10802c00f0350070070000444500301400310b144030b495444040d41408030042ca220060140c000e0850300102005c42c1c0188880108000c0e403e01484107074001c3c072046074000d80010083c0036004403081f14102c0141017070381c0062011070316545c96120348080c0c05100c00400070036803906034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 598450044 1250 598448794 598448819
    0x2706040e010b21010b04030807060b030f1b1504031407151106070c2001020109120305160f09031203090f03050c151605031801020c061617070e0f0604 66
    0x2698290040d0300c03c0000c10038071400b80d043d0704985621140914184c40c540b90351a60b45c03c003110880c0d00540b41e40f40c1607100d81d070400001e081e01c94084003034000d5103c819500c4014880407840ca50240e42e0441d03150503440321100660741101e800102803081008484100750814a85400c90404045503104a00d0207683c0b00f415a061202e0310700c102c59036502c0300c00056a8204008000800110b40d0281055030740c5440d8803140c8588206000220b01c0054a039a0030442d900c80110400001c1d944604000b80c00e000004404544041402c121070104500a17006041304a1808040c05859603e40e106200350b00c40d900c1600c80b9a00825680d0f24202940380c02803841e88140c40340c200c42e1141d881d2515400304c500e6000342c058002e00c5403200c0c0c0e01700d4001040c1c0e03980d000108038046640d900c0c850350075881d400b80010b00810b00312a018005900d01460f0701e0440e11455002d0350100300c2c5205928070b5610401c41b1481e00705041d0308108580408540c0082c0c1e441d22101c104d560030840114000402155000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 598451294 1250 598450044 598450057
    0x70b090604270c05090d060b010219110307151b0f05030a09140301060501050403060b0f18041712060906060405033702011202250b040501112706040e010b 68
    0xb50911103640c1c0c0c00012901406828182c0761700480100c03540380000d625074042100300c40180192165500c510030314502d085020b5100b42c41c250300705003c4045030703e018460a0090520a4641004046e40c03000040c45640400c94940b08100e032204100280701c1d000e60044c404aa115080302d0780c0d200002c10050146030603110700c0c0c0c1a207030400c45d5020249030600032001650780607912182451b1458460002030502c4103200f40c1c01c80300002003441d0039126840415840100da01042080e03007414908444c000c170f205680b80b030300c0e103900f84a1103010f242e41c0e184090700414116100c5945440310343c00226144200e070b01c0303250f052007080003040c1e0302c0e09040d000c54802410720604160132080c0c0c4415403820422044000e00103032000507a850000d065034050440101c1c18840c269000300c94010900141c07218000a45183d040101000104203090040ca003900070901c90903810240c0040c1c0303811803194111003501d103844c405c682c54015521a84240d5009011196011019503590032440310781d940800c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 598452544 1250 598451294 598451369
    0x5070807080304050a050c0913230a0f1703011404020702011134030201092601020a05070210110d050c0f0319180b180612010303020d11010e070b090604 67
    0xc55a00d2031880c040d041503100d01602884127200181580e1501c400c5072100700c06c8000a85003200811b502e510421124008904c69800b00441102070300b4a031081d0203240c000369120110410040c040203c01440e0b040110800f5100983c0f030b4142c900c0180e5a50011140350542881200071406404036410743c2d0107480e07010450021714031140400e900d07401e24258003020340402d0111038200704c4080403400007850201100c0722510404e0581ea40d103400c0e030b8080e401407000281c000c039854083d4902003000201c07000a5007020001c5400d11421240c075100502126000d0210205410325000014445946004482403c0d00d699220200c1c0000039030486200341d200165510800000c21211101400c003034501c070300c0843c1d003803240114040b006040c0003000c0e590000810322504228480455805010714440c0c0c01034100680420b500418008641d05200060386c107003040c1042801c0042040e00584600c201450b60302c04c0c2041c007146c181d11541d40100d80e01d0305c0400c1180c0c500c1d00200d802550101a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 598453794 1250 598452544 598452553
    0x204140a0e0c0c0f0a030201091a040c0e1509040803012610050c1603093002060703031d0a02190501020c0d0314040608010315020309030a05070807080304050a05 71
    0x110400d202040c032a601440140d08000400b00d0309550411010381007885030300013203c180c0b00b0107200044c241210030800300d0241c0c2d11060310b04100030490b40c440403c0d44401200141506c0c4ca178072203c400c4082e611a0403034504822000c02c00b241104448018002c00c050800c41042c2040d15011966500c2441a10410800b91002008015100d03c08504214280c4018031b1020403880b200d500600002d0024042c0d80030400102032001c00002d43c1c25807081c0223450382000d541ca024099001c001d20007d4006207185070034544400b0300100481a01c040ba0182e0300107454411601e0140c0040134031405c4185900e11003840f60031100030000d50440c40f144241e4000c07100c641c2040c110750741410507004041c09600190503000340360402c81da1041d0014003914002d000c0e8a000620b000150384a90007000c0080c0032280103100384100038144415540f0300031411071451074043c81c0251030f03014a0741e8500c100040001c1a070f0501c100b01040e1242141c1141540da5070341080d00e4110340c0c40c40e0040b400c5480b8002d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 598455044 1250 598453794 598453829
    0x2010b030322080c0d082508030405070509061e03070b04081b1f1b1e210509090a0b0307140405090a080406030b03031201080a03021018021201140a0204 67
    0x100030a4182000d07078080d01c039541c5c50f441980d80381803e400031600c09215810401200521120130074880328210b00079090f4035940c1c205400c015080046070703081207004103610720500005440d00410843d44041d202036070750f01d0100b89000207050844603484164035880207d00482d0344038000c203240108031043c000f0700c4102c00b00c410500c14252840c9600c5c5094078008180484118000d0032951030f189200c400c242c042c3c54081da50846880e00b8503c10488030780000c1d10348410004811000840850200355001c85034060b500000c0c080d12421954500070400315000c075404100e036800003c20404010141e4070b1850b1501d03500000040d01d1803806115034102808581c1402001c0741d1504801c1d00141c030b16140078201030084e4040e0082d00e082e1905844104401d001043d1170501d001c1c003810b1044090041c4e0003440c10000d05d4454200007521115107011403100001c540855003c2d603569055622501e51211505454014403010303e108540c600f5110402050035810360042c000d5415525a5030303980f94 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 598456294 1250 598455044 598455059
    0x11031216020f07121a01030507091d0a0609080c0f01020a0f031a0f0f06130e07081510052701020f01090506010302150f0a1706100c1202010b030322 65
    0x2c440e04580c04490300300140074030540c8210301c40420014003807296000d070710540c06003459144600741d0040c0d41c280c002d002d0901400303035140141305104003030042c0e42ca10174084131000e9840d4156400020515643e52003147d0420408000350b4910500c9141500c6d05000c0d020146c6010307621a01100000400c404a0500f1050007482450010f251180b48440d60305103030005c0c001d180741020b900c1544a20f0764100c5108075503640d030062194425203c3c4840c1540e00d4040d0f004481c420181c1810f0500c0020410030846104101e07240e404c1c2801100c86410601c0f8103102134940c1d01c110108c9400781041e4100071600b141c0c000100001480e4203908580303100803807405960132944940350041c0030b80c00c240010009132806400e06021442041c03c854030346140d003500c04040303900071451030000c2100701107180546c58240725402e5200740306444255026000e04030042c0f201216680045c02c4580e40304003003448902c01d40c04440e41c03001c0a011170b50344038800e01c1090070301e03213038500b00101c03040160740c000c945130 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 598457544 1250 598456294 598456303
    0x9092d090506070801121119030302030706051005060f0d02160b15030f030a030f0204050334032f12030d0608070806070f030b0306040f1202010b011d011103121602 72
    0xd4150b0960608100916900d0003038107055034040d2507102916480750060303d23003c100303800c000318070913001946e9a1015160440603250010b1190301040c0c2c0c2e1040c1000191944c20484081741c04039014503648024090141009010710030500400c4154030042ca02080b2640e45228023484040400c0074000c02610f00705581c40c610b019650045800034401c1200300380c003c1d0002074000c01d41171409428541c50f20003081c91705450440d00002440710300003054203080c3c2d14029803090005000120882411900c4c1c3d064408454040040303900312203900e800c26854400c4040c0c941c03481c01000340c1f0081030780c1d0303408513941e4028094030000103140802c005888100040d8200440f1507140103441c0036900e02a00b41c960600541c811401c0c9170b200d22803c203403503505200851242d4400d400150030b4821504115040c80c100c510720406681c0f40c202c10303102c03580c2c126544410590111581101096100004075040c500a40a00203035100110f803000c0703550040c199451040010b410030145507544d0f0741c82203990307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 598458794 1250 598457544 598457549
    0x62a12021e0d26100e130206032404050106090503101802010806240307321c0e010203041119050409030504120f0201020607020d09092d090506070801 66
    0x2242e0040141e07003007103070280d06141d01110040f0f0030740c81018201542898080003c58000a0840c0e2040c41400700e542520305642e0880110041c031140142c1c65070210f541d0748405424044020400c1c60380d98001a4014480ea4810038054400c3c0019659241c01400f54425401014400d0151492002500b422485024030340c21072a85504210706040c2c0040d035203408003501080d0042c1d007000c04440e40428125030108090207125803140e90b443d0007403000781f0420242c4201c0b016510032038414a6034550a0444284a484c4203041a03075580b481030400c40d801c05030b08042c1c100e040c2003480310100c080f010350295210b2802100c0c00048014400700704640d0052803c1c45440c0c1c0c50014000780308504007035200b41d86d514402e040c401c5c42c00b074035100015851040707100c3c100d40c200340c00e0280604550341031214a8020f04980001c080e045140100601404440d01401700800d90f85c000c00d604000340c00717551100e07810b05001044100211807000300d003d84613042003600c042c4124404114140e2207901c40030b04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 598460044 1250 598458794 598458853
    0x405060c120c03060f0604270c080a270b06040f060b070b040309241206060504090207260c010b09041e0309050603160e0405010807062a1202 62
    0x1190360b02d0920203110340000d010150031840808011906072107603001032010b00400a00d2008410075a10340002134a14030040701c44140c18086c070784040320740026075541c005503074076000702c0c0000c030300010304100c40c10841021160202800c003038824050140042e60045c881510284000012104400c098629900c00d69407850380403c00d1001240551043d550814407901c4c00c0b60307680d07556018162000004a0100e08042080082181500d400030502c4510104c080424014a854070402a00c28020751003010500d0380c000070201c0410003405001203114091081540c8600048400c07007400d87c000041125a6600c0e02941c44403600d00807442c43d01c00c0303074014080102441e4001000d0140039050804030309004540c040428244c6d00c82001d103205101981030600015281800100300200351604640128900130061040d6a004940305055601d6800e01035100e40c9014800751010780380e021000b400b100c95a150703030100884c146c040407802c0320f6542249c0980c83c0e074000b41418805a0100c95070f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 598461294 1250 598460044 598460077
    0x504020708090118120b07030c0e09070c0204060f061e0e03060a0e031e03060f09040c17160602031215280306021308160317090d080d050405060c 64
    0x302a43c4107000c604000801c180e0510b56460385ca40d0b01070005080310307500311090a0040104030001d94188128040ea1002e4a080744c0041251070200d00c04000c00740a11040002c5141281c0070b40d1299040764004004040b1000e1001c1c3c2e4030300380141010f600004001c003205440700c10160300340c4038000d0325020442c024003074003260301e5030740e0001d0041400d2107064100380014041075101d4003042c500c42c142c11008101a40d5207103402c0d030401402d089510400391050000105110104081d800f103202a0b82900b024251000c407402c3c4540e1402d51064103d00d1110700306c000100340540d020001c0e206040502c0050102603c402310428800a003001480b42c10804d405180c80440c020441c1c00d15408425090703001003507440707440380d000340c0e070100040001c5100442c6041043c4241080513004202044044002c10350666a038082200b150003134803482043e02140301c1c841c50b91401e04103030030745502141d500e0341d0b240f1810009019201c100c030113982da40a84400600741707540141c1120001e08404a086 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 598462544 1250 598461294 598461307
    0xa060501020d0c080f0a030b030a0c0612022109010617070626190608101a09060d140118060c02070f120206070f0204050c0417010908030a0b01020a020303220504020708 74
    0x1100e4110280f031800305519035150230003075201445144102401502502241400d0a101501100c05ea0031401e01c1d2a01c104507013035002c4280041c2203201041160450102c4d15185141c6001d019550851003940d00000603031502200c000860780119032032510384c410300700e80401c07030840e110000305c0b03c1d170913403195240010b00700c2020080c0e403d6124440000010300c1949441900b0315011743c003445a02110364a10b4815030401501140755441c0b0b0007141d10501610301080410030703491003503000502c400e1a0f90035001528200303410020003d401602880484500b078101000940b00d507180c0000503001c0c0346404030f800f0649e0010f800c251862885004401d0030b4940c24044207500003001070314010b44039041c490059942c0d005440c0180e02d40318120b81c40f40e090900c480454142500031070741d10382c5448640e2001504a0003a40c0d440350f004480010120394410050307051031a880702c0258140400500c010305030312041d0303609203028003c0402c11903840c0c5070b005100c12881041c0d03024007511803c0c0040e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 598463794 1250 598462544 598462567
    0x51c2d05071b0f120c0309050f01020a02091305010515010f020604170a0e04021b060702060f0a0b03011e050106090806131e050f0a2a1503140a060501020d0c08 70
    0x1c080c42c41e1091105520001c1141c5507903182d000b0314501407000a6050faa06001d0681c00705c80752018003401c1b62195498110500003079954175400390000d009210941c000f070100070503c2e81054506420800921061030102e058501c06051380d80014042030750624a034082c2440014003500c03d65004040302c007840d0302e240882d9002c1d04009600000c002c44442e40820300d8a90780013800c490706642c0459503001903110072050503c0360040014046500c80c00801024000003074540790820120b036400070b404002800424007421546c2c00c42e04003584800700d22281c0c0d801d241e03c41c504a45455442508107615042c0c680c1d121413040d500c00b0800d0700d951280b580820180124440700083e20000081c030125540d9445084c00d1104441106a420a011090510106009034007840d4000341c0489607107500d4040c030f8282d4800034080c0e034004800040c805c0c02c105d402a80f00c440c0c44a00d2080d103100901d07014030140040d00c1c0354001c032401401105880040c136800760b444404100d80c0082e41038101189945c0703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 598465044 1250 598463794 598463837
    0xa0b1306030e03042301030501080f0a110a05041505030606040e03030619031704030605010b09030d0e031002040305010902030f0d080703090305040b0304060e0c100c03051c2d0507 79
    0x184561070000300000240c0d0140d08601c5d04181140100092852407020005012100164000c54254200c5654908103500c0896032038440d80d84840050b03075640200300030a0081810340c01c466001850042109021000303c0c07030340c1044030001c4040715403690700c0200348003d80e0305445001042d54414001714103207143c492205001003080b00c0126041d20b40da074680400c20040c4880d04400b00c000041c051051100d28000d69014214007a0300c0c07841c05100c0300c0070a0b9501000a40001000880baa510640e55000d0080c48042a4582815919240c580c00c0080c002e12142804901c0385c0301c2e21402086144010808003901074480c1c0301c0000c3d595940d00180d0152101502c1101085410040482c4001064020794019030041200050403151502c07550310300032180100900c9424071840340030050340d03c840120402c0380e1626100343c84003081240901c414107040030383d944140c00c6c0460480d070340c43c0307144e030005c421314610540380154155070a02404403170b001c2d41c80c00f00080e012526000c41491000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 598466294 1250 598465044 598465061
    0x307020a21050a030e0c04020f0a031a130504210210050a20070807020d0f20032116080a0210050603150414100507091d060120030307030b0a0b130603 66
    0x201640c011b029100b00244c100e0f0310511145440355008101d40d40e13405d80c140702e584008a41040d40b006d0b145500d10000d500712610491480020303807914001420841000d07003903010003070b020496054148090001a40301e4035400c000240c603501c1d1000044038025507004042c020030036840c4402012003102c8900038244e210601c180c4d0480070810070000161698410b007800b003030090781d201207007605a241010088401214502c1607440c0d64085041d0b6540114032402030700150441b440c1450740315905400c0d54090701005007082481841c5540500041e4401082d010015600751303045444001000c00803203505540720f90701a40511114150003098180c035030341090240c41d04c1c100304600580000c5c68581032001c140c441c161100b0030300501540141c0700101504030b01d020358000d50101642030612460049c01e146c108507016011007040c900c00181c1071070503510b490640c0d5491034407500c003070f0143c03c00301901409143e014000241c2c404145081d188030b4269162125036540c0b0380385d0214051310001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 598467544 1250 598466294 598466321
    0x1505061e040f0e0105090c07031d240d050c03070c020d060b2e0f021c05070c1d0c070203030304031d0414010905090c01090621020307020a21050a03 65
    0x40001240710140c52201c14002c083e4040c01c00019030600060200704400a400007210b4041071290400080c1c100d50340708414900241221645200100011441b0f200c0c040508105180404d00c406842d1940d801006042003003602030101d501d402e01d50845a20040344c20900142c5641200f40051030004000710540c0d0040d0400700d407003440e100000341210154219140c602c0044049009080902d104c03c56038080c85003010741000c425400c010f034031000c0aa00c41d0007918070090620560034052400e645845810181d2003107e07544400000901103006481e020b08151407400103506060b280044030b0602c0d41c003902031803e6499a980c20b45041c03044030522480b5924400141c4a29112446002d03506829146610a694074080100f000c40c1c01c090500c4116802201c0c4542050b41c0000183c01203130702038900b40203010440e5000c0103891080103c01c0f00e0960000050014843e8001081e000c641d004d07480581180b48084014029003000101500200314244621004e29020303500c54a20003165 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 598468794 1250 598467544 598467547
    0x7060b0604080c0a050319080c01020c030f0d051012030e0a170a1b080607080a020f03010905270c0f03010615030203041a010602060a0b0d0b070908011505061e 70
    0x2000003003040e005504420420391040040d201180360010510004003415405041034004036011f07032540101040003d000b0300d0000414489101096045a2500110b601074036169819078040d1003940d07001803200c00d405030900c00411420b0114180180132501d040d20001c256542940d001d95103600d409112550001c0c04c60b50019110038585000304d285c3c14403002508403400549012040582c445100c1148442c0300c501c140074115000410540102c0107007480005a0b41ea4401c000181c42820650170315014007200004641941d0f0700b206020300f00d444a6258000100d0407104909100002c1078a1642e124241184141c2420100c10070300d5940600003062182e1210241050b804050050000280d4000f04010030700159010451211032440610b03100d1754501980259214030141860485513521894018940d07608402411038a40c0201601c5032464a8240581204058403900c1015420a0f00d0500400040880c84095480c000c0600d418514114002003110040c1d904500f0751550 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 598470044 1250 598468794 598468811
    0x1050a0c030e10051b030711040b0d1502040e01062f0c060414100906020a0b15130902040506041401150207032001090e13020904080910020c03010506030705150706 72
    0x181c0442d104507902264940b0ba9440c1040488044c80200d00c2c01704a501e5042808a030000401d5142000002d050840f00801d03000c6120000440186a880008100038802c1c41c240080000e150050012140000c8400001e41c0e0b94803402d82e41c0e60720301410101071105102116400510044001c507506540d103040783d0f141c16003500400c48650081e008003544d00c42505142d0b146141044100b25240310743e103050380c4181e18004000c2d60b80c2d000c40c200180450184400074919101c035914407941c0da20001c04689a0200000c1d26030014900c400d0b09a00540c00c0500003183c0342804d0140011400b00f00304032080d56864006000001d8199461500450081039000004105900d1042c1b0214842c2d0100a50324030400e0005400c0d0300066014950713a0303e400081000a48000042000280c2c06071509001130303456280480700c510a28101c0399000e0b01d044520076400e980041d055004042c00d900800990301c0d407000b05030350b45601e403040c140c0c4003050300c48038035880c444d5401901c0401c1c41090302103071804 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 598471294 1250 598470044 598470049
    0x60a0618200f0301080d0c0b0c0901020a080403030f030c05033c01080f060a0504080d1a12010603030e061810121d010c030606020309100908010203100e010803040501050a0c030e 78
    0x51280c4802d6418040120041c0140c05040c00300c1040ca08580c104000401e00d40d940700e8442d403100604825800c00c0100762005164000e000941c012035110007108d0340e590304c6c1d107806000713650302d600544006450452030b0060b0030b00038812240a960408440b4200201684064901c9501c4108150954850401c0400d00301c42401140d8081d0064001800329030300e200035084d00c0c007000140724041d11030900082c000410704c14400c030303400f04510600100704030911082109016000f002d0040d00078014460000720f010045d03122205491083d81c0f5103417050a0201006540e0154020544c650314090325840d1072840c220001c11800c02660402ca080078140c0d02c0554100e440c8454201c0e00880d40c840411403844003845418076207007060600304501d60070070400079580c0c0603100f00c99014040350b48003691a2130042c48440b00400b142030080d55a407a120091260f1280b040c0704034180040b1800000c030300705030b0110549003a640f040e07682a00346030a402085442000184040e41030101961401d5101d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 598472544 1250 598471294 598471297
    0x1030b090c0c0f06161b120801170a0c05090415020d0c0807050c06060f010908011803030b0a06082a0c0109020f041e0e120417060a061820 61
    0x40c000341d407510b40c031003200e80c01e41414500c19103081c1a007034005034104020216500311681d1030009500d400b80c034178440169420f80c00d00d41404c002e84901403100e1444070155200e048181030719034108220a0180e1400f4416584d17064041c0002d14480300e100301803019040c0041c015500c94040c010203e007004812000400300d0780300804403407005450380b410600240c2c10441d050b820540510b46680791004030700074107440d0301000d4a41c51050001517042c8103540e01c2050000302410000c002001191503c0751007a4802962000032070200782440e855212501e000303481d03030040f682c0c0c2d03440d80242d40d52542c0c800114a164001d1428070001c5c002d06030020140074074044d2100007407800c000668820b0a0042003084943c400086124074180b0b685040038000d000102c561968000402107400080c5040c418248119600d504000c0b00010074006a913a602184030740081e1440d00c1a03805544801d0070340010348181d40107502040c00d4074070f5110b60100701d6900965110100c003401c4402c0c2406181d14401a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 598473794 1250 598472544 598472551
    0x9020a030807030f05040e0a0e010b0a120506011203170604110c0604020108090303010803070b040825150506060a050a0c1b03021e01020a0308090c1801080c030d0e0f01030b09 77
    0x7030200c041002c50401d03400200d6031560500034203000b42441c1c6030404054640380300520a604c800d84811207035401810940044000b241700500e48406191100c1500340400800304065401d40306070740001070100710031100504956050790b10300203020490a4800d52825018020b2500aa0b0b14942c4095021480b0003900000c00507a000d00a142407030b000040c80c3c10800340440f0555002000100310380700c8000204c07454240d000014620030354071802e1a4590f030086520241204410707001004011813040140400c1d50b2090303104840c42e40050401d40101c0342c08440c2e098203c0000c004814049020700058042c0200d2442d00648444041c4c0c0c0b0a500c000c0541000742400c2d144a6040c4210f1800e00300400d038402420309140c03564020340300000d60b00d00140308084c0501120a000c181c5c07100b0140300749004c0c0280034209071103c0298103440c2d10043d030300348070b05403850090509004031850003203038420f4810b510340d0310103032125a98410460180710000d40c040c1410355989441c072042c0c588103d850720 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 598475044 1250 598473794 598473803
    0x81801020711030c100516140307142814030d060b0310170601030308060a150806130b0102070e0703060504050a1506091a0d0e011e0615120c0309020a03 67
    0xb815905014503151601c600002441280200000d5440c55402400e8600c88007011541c064410054181130300b0000102010074071500001403590140889035040294181981080f149902141701104140b0f1700c8035202140042644e10016012a0680383c28800c0b40c0c0004e01135a03c1c00d071080c141d1000300e030349640c00460001d401000300000c021480c84c030000100b140b8411a208411042c4102c1e444401c1400300409214105d000b0500d140c88010300000a00800042020398580c1880050b280e0030701290b5482c491499490030030010003444c05a61060681a001400068102581500c00500040800c81090340c0c501c8000b44e1940c550280d64041c4840c0400000c2842c81d0000c00004580c15030007203028401ca900c1d04200c0d03c650085000d0310404080315950303c0b091406240c60203810646901c0d5419820a07445c190300b05a105031001c00820b040c901080659506c462440e110989480c41d00046410340c02031030380c5400c00d074005820700445482c00060801d003660005c1d9040c0241d0b08140c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 598476294 1250 598475044 598475063
    0x30e010e0301050f0402030c01141207140f0706051e0a0504140703030504090f0c201002070b06030d09080a020405060a15050d052a090a0308040914011211010818010207 74
    0x1b581000d100700b500c2d103c0d0a181041c0807a1518200c41464419440424107038000c1c00c0000700b0f910300c19184040e41c000084246a80c860f140740075102c4642107600c00b0b461088c544808103040d40400d11032240c10680001ca00c1055a4507079920340000c24005000703440300154041702090070b901c10310005010358440e854045c0c031076040040350012102d4858034030003141c2c5002c01d00c00140c1e8202c040f0b04c0d402d80202c09441000070007100c49030f0401600300303002d2040ba13002017028001c0020340d11405104030b4054084440307004a8030000c4501c01c2785882484499001009900c02508140c0c20a80d40084058100e1a13074542da82400c4403403c8898000c4030000300e010130290a000014000d0301e0702301880c04440c099a4800340d24088044c240036402001440c4001844401c0d515424000310003550821001a12190b03914580030103442d848581d0086150080000710304403d078904050000750304034914410310003000006441c60b0324060070800303040749884400c00c2040f10900051800501c01c0c0c1410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 598477544 1250 598476294 598476301
    0x2613180b120d12062709061104031103010506090c07060b12010c0f09080601171c090f0f03111c0f051c08091f0b0d0f020a0b16030e010e0301050f 64
    0x204030140f01150390070709a00f0400c00b007020b01c460a5403040810138450103036040100f00403944c00180b0500c00c0042130340b03051055401e50124200013410482c1d000d00600a42a0015010075088840441d0059800004c502c081519044404041c040c140c2c0300d03101c0009e0320700301c960002c4c4900003014910641781e07444169902d0410750000b0311f11480720385030425103152821310084a440344414024240e0000d01e6800c4104031000c200030998001d20f80007401103074045906d200070000415030090003160006000009902c9401c0041a422250403ca140300061948070030880e8041c0381a0602041c2610340c0584004154012086a0312030300c160020585042040030050311061a2020002800210010000c1c1000007017107806550800305ca81070744540c0d545010000400c1c015800c581c00071142c1480780304102c80f8045000c0c80c01e00849298801996440c2100c03400e10451100d000304500070300387c80000a0042c0c0e9034082040e0141409000d4515040110713084230400c407210090200100e060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 598478794 1250 598477544 598477547
    0x5040b0703060b0c060103080906042607080f03090609041b090f090501030f02301f0c140903010609092019230306042613180b120d 58
    0x2d0b03100400303a0703640c001e0800f144500c89584030f070014030020b4545640007908a94a5840c403048501500c03052207611140e06024810200700211405440464401c4540102d1035001c002101060b07160001c004600d4081c45401380143d0743c1100c1010340d000768507500907801a003844619401c8110841e944d43c0f00c9546413891070624103800360f200820040c034002c01440821a200300c0441d80f50b4040d03601840c07100040800d08214081809240700d0700c103100e19688550440454004100780540c0710070a45103c50300000422100f17000910800b10f03c80049881041110002030030003107600800010308aa540c000c03040c01c0d2000d038503003292100c50a4a03030001c0340d8800c800c00380d180b24081e550580034482d044580950141540107402010011040f403c00d41e43c107510346001c11182c0607069070300900301490030380401800d50070490300b41d19019072150f8003203c080040d6610f080c0c0e21085042c5044c500070720745407161080851b0116107070f1104815013454448e002c4000e03442e4900300080c080005103040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 598480044 1250 598478794 598478801
    0x904020f031317030f0f060315130201020f0705010203120a1b050c0d0f080612030c010e07061d06031501021903020c0112140708060d0519110301050f0a150905040b0703 74
    0x100c3d0129001d0a2042c058032801e02407026034002007180580f41640c8508001a24100115880c0041850100c013000413000481071000e50b554401c7e02260b944100c0a0030454407031080e4051907005a10500c9540e842007003019035181c01c061008000200344000e0740e01c00700101c1089540c1e00c0440c01c000744402c0441400c124084001d082032030008000045090b00410442025000510400030f43d614518410424021203c001c585d1030005c003c0705007481c1147c0e4a54003240b0600c3c0100302000d405142c8030008030030401c1d0b001002458039107142d6034607242440000d80e2041d9a8118411300d0b10302c451500011030806040d41c040d800500c4840080800105a43c00c0d641828a50508080f1143d80c0703000c100441c01e412481508001103d0703a03980f00030032403000031190041d001d441a103c44da0341040820580000940c003c0703240241c1002c0c1394003070600740e403002e8802030609052807000486490040c0c0c41078103180540f00646c600035903110484400ea4400341c0301590400c231040705009610f0f40521 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 598481294 1250 598480044 598480073
    0x40b01110604030e12010b090615040b1201080d0507080a03090609240501230607170d050709051c030c0c08120d0518070b0f04050d03020d02010b030102090a0b0904020f0313 76
    0x174020b212204103940450b40355080501104d01a2026080a42111418209880180055144071926003d00a0f480410750100707108084d50b9000d101652841c040c40346044601c41c40d040714a5910b4251241c0c0d0490083c0820b43d410307260140d4804600f8002903150b80c2c4c075280e090300c4000500b4603c40011072001140c1301030b408420aa11040f0780e1202a45d00c0d20f1201d0000401103071001c1d12004203013441c01170000b6045120200031000160382e124410a5400725000f1061581c94101c103030785034001d210103800c90f034050f0764403080000d107a84002803049039021801441255075814495498803401d1174051b00701c0f0414090b0304007140c01d50b40d01e1114070500f644104891050301d0201c5150894644400307a601a00340801400035902c0e1030300301d104040b0b03802410050308080b074002140c20000e45076030800207000010750800341203002a10f01402600c8100100402c60740b400340c580049003d0a41c42144007507005138003400454500f44240c1d01540c0f25942e0440309402980e042d00e40101c20f10700b0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 598482544 1250 598481294 598481329
    0xc03131205010516020c1e1f11010606122310060e030706093f12080c0d0e0f0f07080607020105010303092303010615090f03050309040b01110604030e 66
    0x54204504d1550000f003c601000043c3c50f9000c0385c0b00368001119012980d00100d54020000b40f0940115100328404d000030300456075501d00030f000b42c1201c0309098614503c070316400140e03601d00300c82102c003481e030113801003c0c685400c2c4c0b00c07842c4100380405080f550031502c0c16080c6a0880e001c0068503000101c180740308504070082c3c8081400c100020344044c50602603840710410000c81100b0068095661000300050f421544a9040c4a00b6800001d4440c0e50380869180d1101c100080d1050b00801d0303014060030007051071a040804811804004202c04c41c9800c0e06842000d08030f40003940e051001c0c00403907031828098010941800d9802e490000058030b10021a0324000041000c04d43c003c400c001034803040114040b01100c0090709241040c0c49045899055181c440000390b9405582c8031141400e4070380d22115101660b4505a1a101050740700151954004001c100c0b860b1070664026510b00c1310506100744017103044200b0a180c84422142100402d0070b80d6244561860070f07041030b03000c00f00c14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 598483794 1250 598482544 598482571
    0x2090316180509060403030213031a010f060809120c0723100c05150421090e01050a120210031113050906040204051c03120c03020414040203070f050c031312050105 72
    0x42c3c0d005503958100140060200750707011642c1036810322002070f400001c0d03401c80310200311400c050802a048001c00c0c4204c54205e41c440c0070004400d402202007034414034060b4050150000f81d04801c04c855808502e50711040c0c06210404100407030702014114060302c0d00001200315420500510200000d8404283c0902442041140010350300050542403800031007102042e54840e45440c2c2c102c61001c1d00380b00e0002080c2141c0d5415280d00021032030031260540e0400e4000d983c0c0300103111100e1664010f104004070f00f80d5090026041001007601406010720b80002c1d441d40d08492000c451708200030f100c8083c1c400c2501000760b450300300031031500a20212011883d02d840d00000444480c8a1424078112291544103001850300034030010160022900003842400c50b040401070081d4854050103840070400030004035141464401da1340308103204e40741e510010090716410760304c0b034002501100700362004200419101520514000c0104028181c605484140d840d000e070954070300030300e1410805003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 598485044 1250 598483794 598483801
    0x303090915010c0212031801140a1b12120b150306010806030c0a1d09061005011101090c0621050601020c010c0302030702100504060f051204060c03020903161805 71
    0xd030982969008900e045540040c88050030060300c681d5030441c4040c0d030000420710301c8450310002100034511300105104401311002c19000659001d855200109109003040c448034480f240244c00f0320b6607001d4101c0c00000c0c034182030ba81c1c441d41c4000c1e105803480065a59000c003404500b06000e101c1a14504036148610040c40c6601504140001000c139810024090003051150724203001c1030400740300181258003500e40b40c80c0d40d42c4448001c01203040e041d000c000001203c0460200301680922980050700380040e29010044901c2d440c90403100500d9560340b8000c40000d8005180840200308a03151070013a248101d808444850314a441030711140d00f040c1c10410580c4c0c1c00b2920000103042401c0015040c2c00d1418200d00e140035143c0000c1d0800d00f40219805015004000b41044844503a6007580032801140c0c21074bca8025040010004102400440c0004000b034000505450032072400508008520000070b00e49042400d01c0211004082d9090092b2030500c9040d0508009500e020f008604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 598486294 1250 598485044 598485049
    0xf030b01030621031b200118080619020f18030312040303050601030b030a020901030303150b03250f0806060717030a0e0115270e03040308130f122d20030309 69
    0x50000d03d005d100b00b02e11065407406c1da03000303a42141301c0c2094540703036030181034a400f14a07a07200d501740c8603202414045002c0b21540300090003210301c540d501702c3c54507080038107240b00f5480b1032040326101caa140c00107005461404418240180c802c0c4d00035a00810203060101c00941110a01d2580c9400b135001100702c4400740c0c8a0b8100c40e0f04480c1c1c145000210a80d00c82200c40700d45d9007036000b4584000001090081102c40c21303a214141000855802d03401c1c0c6940a81501c1c0c02d090300c405038011a1a882c002030007850000d01426a1038005c04182a2a00c501d03103511000340c0c402c450031914150b40c3c1c408120b84560900c200f00d40181500b5400b0009801c007000c502100e03a0440131504030810300000f00e1002c1025411801010619104890f2225113030710307100c0460703001072040c0d4104082c140300c001551615110244201e900c80c0210b44540407440e12280007401148184411910340c00300c03500c0380c0c0454101e010803024000c5482c510806022442010224543c000d018803951042c41600700c0c41c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 598487544 1250 598486294 598486313
    0x90406230a0b0d1a0603030c0a0c030b1f0e0402190e0702060c251a040308010e1f09020c0f191a09070b25140105160f030b01030621031b 60
    0x142e420003c4c0400a0341d4000000b46544188200350410f030003400c1c46441000048030452007903071b102d106a50840d940f0b40b9400b0012145042c800700e034482c500d8500b00480c4010710003a64000340090b0038026581401151010138103110340c070040c00341031034404204445a06010960700302c0810b041140c603140440c0300362401680e4840e803c1000454004100d4200903c401049901440412403c3e40500d054200504402001d1117440841c9441400184e4403912511030802002e45142c528078049040030407200003904407030021201c91041400f081c04c00704081103070b101c0d03e40d801c4018002c0c900d41440c1101070310704503040c1240c0400d0383da001d11506030808251142514504000d281d16440c3c00600d104c0d81c000c01588400100d030354003c8000902847e030000700b6149044000910250322440d00040c1c2044503812a54000f8007040c00d80d524051207a0040b00003a04145404901d00c3d44407100e55944000807012a50130071648105901016000039079919542039448030342d40c0391041d42d02c409052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 598488794 1250 598487544 598487573
    0x12301050414042027070206010b07030c1e170309011104030203150c040e15120a11041509020d230108030301051009420e090406230a0b0d 61
    0xd0310094070b52864684079034600d603a102c1500105c0d07409210384088800008442503c0850060059400104a4107a400c0440304200c2d03040d03550070300222182d2140811549012181d003460b01c131600c440004912006981c000340344203600342c2684c03070030a26569821106400c0c24444012018002000940c1d00400c618810f05c041c0d0b014120a036403405004d0400d40704a0b0001d1a0345150032040c8500100030007070402c04c1900654014064003030179440e083e0744004101d00142608000c40402000c0d04068028600c6401000342442d0b0f03042e100c600000698000142c61079410f030780e984881000f18100c0c910649056100f00300b1141030750520394255100d01c0b050080740d000d080d0300703041d100b40e0500c643c405038010154880154940407052a0171507118044d208580d020125110f92486403201c4e141501c03203044550346034400740800800610401d041e00030000c5d50140e580780628414018a54401d290080014498100701e140801d20310b02201c51200c141ca0040c80480390560000e41040c044610 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 598490044 1250 598488794 598488833
    0x609060e0c0729100f150c020a05030708032a06220f140d030c05090112090519120212030c03090a080d0618020708090603040501230105041404 63
    0x16110400d04201407000000c0c0d10084074035403c401410300005000207501e000310f05807a00d11040e0369552072443e03900c40141c010f00003ca290452095445401050206d1035140701a000340c0e02a556140024209409039200b0129600009800401d035003801c84440c52065866004035188804102d4035640c80c0700003080b0983d0bd4202c24481c0076420b103135600c010074056210300c20b40144003040c035125101100842030141c0510a480030264030900030700401000780004d554080c1060b0001d40110f406816006080340480d03a906c0441d00418401c0c0701044895840740c071004800c4001d440d2809030320302c0400c58641150084660f00990780d02c1c20044035040651000d0007616920303070101751828405009402000a1000a043c45074201036400400445000700395100c0d02c0b407000c11080f030903817154880007072841d001007000820f140f400801842d00140544000201030745030184c0428000d10400452109903003403030040100d031400340240d40e022a0501c910a420741003950364000d400320360f0200c518 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 598491294 1250 598490044 598490047
    0xf06060206131403070c060f0801030215071401020f0903071a1b0321061c080a0f091509050f01210f0f05040804090c110703061109030a060e010609060e0c 68
    0x70b060000000031100e021003ca420f0301e58892803450110200682446880003060300510240e240b18040c04282e4102c98002c2e000b03403040a05d4443c1c10615901c03e00c000c8404410341c0f1003480040b8001d1000e40b05c81500c1d50003c40da18075940c410540b51812581c00468090f075010f07620850b2040035000d0301c4105d04142000703801c03040c0201c8004c2c254001d0200700c000d020403d40f0f00419a6130300701c60301d42c020401a500340d00700500800720412246480c1c400a030800c03204110b0300320704500c6052100703401c174030a1070200c00203503c03581030841840e1512a0100014200d010a004038985040d01c504541424241248003101d280d40e2101450060414020364960b900c0c1104514032082c0c0040103180c1c48080c0c1084249018940081c4907001340c040d00030228603081c8105030780c81c001e04543c0e41d46680c940090810038a5a03959001078030324900c2d01010f0300800d03c140c2c3c1e05030328200070082c012441643c3c003041041c2403004d41c44c21a0b0031607100c0e600c130b00c0c1001405c110503001080400c0e003001c400d11516 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 598492544 1250 598491294 598491331
    0x1020d050f15101b02010c060903031d0c01020c0f040e0d0206040203010c080f0a09031110051005030c06030a0c0c0206070f110405010506091c1406040b0a090b07030b0310051008010f06060206 84
    0x16205030118a90148c5240d003044044800c06a00d68001608804003228850900368030661080ea135031a16500c0b503002d42e122a84440452902180c0000c450308000c1004c1400d1008000c507030b0601010107204009a07124000788811403600b03001d060f00364042c9161032441403070300d060b980b40d80c40340141920740a1340c2d42e00c003004141071148103a010301c01c90120440c0c4070b02c04061404802440c3c2259991455a500e5101040c0307813a01049112003808014000c50968507a00c1645004051400c658014040351000078801078440401504070140507000f041310005550800280b4803140811540c40303680703030200520003940c13007209a075500c071000d403141d1502400241040316800208070002d8240c001c284240b90f05101c0006455114030f1003075003120702580794124813800f80e40a13050024010400d210005141d03521990100490540003421651208031140003041141c00513030b13400a81e500e81150500c40c4280034002c8078070350301e910101044060300e8810002e40320030000d010401c03c010a45000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 598493794 1250 598492544 598492547
    0x110111091f020f010c020706020c090610050c0a150c080f0709091e0501080109120302040f0b0705011b1206080c030a120c080c0307120c020d03030e01020d050f15101b0201 75
    0x840c0510503906001300714005ca01d03031019561b081144100ba005105081301c00300103003045281d0ba4040e11000d06100280c41410320244c500381c0003030b110280ca6204040090f40425101503044941c000070480014540c2e81840c1d0007860660002c0441c851440c4000030310040903803003440c3c2c0088036007044002801c4c00b04550104074004500c90004021401c110021910f40010350106a0745481000c11600420131144142c1c03e074007982c0316117100700041c0b450401c454500c1400800389a40b09000000703003005504852210b44407503000400000e80301011807103860314148250400303020054002c0c4101c01641c0c001071351300c4104040050850b00290949650a0702034400c00300307480d40c040c008075240c080f038840c0540e481d00700710360545040f5107010100030000d004039034600e0503a401506c070360b03500c0031140c60070743c050000b4100386e201542d400c01840d88449514030a09000c0d50411040080d103092003030042200c0e100a42e1894410400c03e0f4512101580103110241c092120486401c0e81001c00d000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 598495044 1250 598493794 598493803
    0x801091b120e071d100b07030e06040b031f09023105120a050606120d03111c050604050a021201140a090203040803090f0c18040819110111091f02 64
    0x50389011889001030210303050282240c20b00e41500440c04010b4a6680d61117000301e8000d85100e0310340405003c100c98408203101d0020030061a0001d00158a8150364801414080d8400c550400c003405961420608450a080c000d0b070050030454030541c02e01c502107041c00003401350001102400241041305030b100700c1c4100c401800400004002010307a1680d41413a40c1c0b295410003080303a05009070307000608135151401d1001510400c91004061a00254a0030b50042540c110580c100d40000c1c01003080100b81d820554440060307a10001c200f42c1060020703c415140050401883c036030052201014170b0f44c099030640c0c115221501e42e00b002c043d914010030b03201071564001900701400007040009214440000b1750080b400101298520400c62491907110f1418a40b01a40f100b0b040e0004102502108541ea4009025a45d02c51401030850a2011040c2039000301c00041850a2400c6012a0b02882190f0081ea5019904c603d4030040000041039110880310281d13101082d11401140b0f58405c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 598496294 1250 598495044 598495061
    0xa09051507020c06030612190516120f03120c0306060816050f0315030604080c0c090603030f09040f090f0c0b0405150c01151e050406031e05190b06010801091b12 71
    0x50a0342e9402400d114a011200c031580300642c0c0c60710410058200755102b015481c0f00b120782c45902c50f80c0c030300c1d25590341602c200e0b083c00c81902001090640d07030040003994440d0400181d00d40c3c800048a9160141c007a084103001084039400c880704c000001a2140c104040303501040740c0403c40c80c2d407130380d80803007140d04908030003142e64051007210108400c00402c3e00040c61545005011034510604100070450021000c613101d9400d9081441410340b8440104050140d002d8001d00100306038a42c000c1c528110781c11131030141c4140860000f00707001d00126208400160050000c05454141003801148071000290080400c10400003004480c3d0700080d4408180c1d0380380b90b012401c88640c4c07194190300d40d074200c1c03810b841c00881403c030009141c98a48903400403668001d00c008401301c03464400c005144809101900d5600940c0c000303501021300310f54100b041030720482411103281840c0c3c000425801c0142c101c0300c1c1e4a880c1001c0280aa03031304050f48880c1040f10700d0103c01450045810340054202d10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 598497544 1250 598496294 598496329
    0xc060d0b031006120b0903030702100e120f030f0c070c030201121d0f07120b01030f0f0c0602010f180b04020d06020f0f030103020418030801030314120a09051507020c060306 76
    0x30202003405034002c000c4400c4680034031003102c3c481e151810959108d11083c0c0360135000d82e101c031407a00b245203000c0d080141e0807039089007940c1c50002c40d60201016940300741110941000000104103000c0785103040b0641084c41d03c00c81c1400d2054507600c03006c401d0310b2400042d06102114084a18030303030603034020864200000884040d0034002e1851107039a1003900c0c0d02c1c000c181c0180c0402055006254082c80e01c000c2d0003010440c3c050b444d68541d005032004011007030312040c01810341c0c1030115507101c000400a03c80c1e40d0002803c0c80b2024241400c4600240d003501da0108861400000300d26915841d940094049550940111451400b01e00a2040801340700c0ca000020800300c90b0348010710003a6040341d00070359082c0001d68038030801030024880c00c2401004a101c1c0e100500101c0c0c45504002401540c42c2001e501d411204a8450032410013254680300580d00d0f04420720400c44103202d983c52200ca00300501c4d0142c00c1140001e515130000121850050030040300085075640d403017205500c0b05102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 598498794 1250 598497544 598497551
    0x70219080f162004200f0910090e0105100507300203040801060b1612020a02060d0605010e040624021608010510080604080f0703020c041a01110c060d0b0310 69
    0x2450400801815820940d0f50600344003900342103800c0c10701860004009a000c03590044013003c02052076034002048601c46074500b40b03c00000d0b43c450071102c0c0244545501c0e01110a450122a460802c07c160000740c0518a881c2c1d490217501d030014103403108180c0c003201079001c0c60700f000008481d40d4460200750110181001d8080d2090b90040001c2060380e900d103000f4400c0c1621080d04680350301c15105640c004091688000700418201d01143e18051091710580c0d80070455500043c00c1c5401100311030f49c559540c0c0408001642c0c201030202c070341a101395014004c19241c407580c41c60846010301550707021000803130b10750b6215209014210110350b0300720007480b205440e1800203000300310444001e07584602c0051f02144a1800140d541c0c851503001e00880d182c2107481d64810020f0700000012000e500c214281000c440d0fa40c1e010b07441c2d02081010741c405a825256000421000525050a030706812045c46520203032140c40441d256a52a840003003007640d44000403c0c40c2030030701125007201616 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 598500044 1250 598498794 598498837
    0x150601030c02150109020a0e0d0c150504030614060a050f0a031e0f05010203100f0b04031b09050f07030b01030e1504170a02010203090d0e011b08040527070219080f 72
    0x217040d8040e2405841554440032040004c005100c1c04507500403001c4c1c411a6600b80c1000101824801d28248407a03501d00389040a0396661413400b5170f0401e805502004489004005142c101890701c0300007094220f03450410b6400740b20220703072070344924000034010405110031105e0503441c614010711425840f400c1c01c1620704560601500135001900e2180308001c620300c000558038036102c1010181d075050f60b105442e15145503605031452040030020003c0d0a40300c000040c4805103481864800c0e2200d10343c4141a15120000900325410412001e040c1442c1181581b5000c0d8006007424020782d5103003d284054445041030140119890422480d0260000d0b45104143c1e0640103103000d11b00d8401101c40601c2600d005480101e5101c00d66800030300108100241890081c4030603c40e81d01480301189001e45402c04100040540101c1d0049001c5007096042e0100142245907440350551003c1c0600b01182c0540741d0722018407081c042c00103400071a80a100606450807140e030407000301039031001e426 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 598501294 1250 598500044 598500059
    0x50618370b0f010908030a03020c071d090d08010f05010e041418241f1715060301020408060c0c03160f02100807050f1c020403030818150601030c021501 67
    0x56180c0507140203207010080c60301e07103500030403c800942d032800c0061410030030400400c9001790410300c096007441c03003104800112030142d13010b0f6004001011074140d02501c0d03c1c1448610308149116240e08100c40ca100410404281c0690b20058903402d2a01000c9000d4140005014098500b4a4071010b441e00050209080300d0215003101c0c0d40604050340d184100e400b800d00e104001e140c5c0d085209045000000d0316043c1c9801079840280f16103412545056280d0300e56488000c40c00307900f403401c0c0d4041694020400034250401e684694100d0080d440c0600302140c0700c2d1181780c0a48000f8810002190140c4003050901c165580400790214001c03458109090030380903284c101c981a070040052540f00c6802d03e1040c0300d500d100c2e45160320b40a10784144009040c1103030744801040514400040802d1071540d5480c002080218000d0341c40c600b090400082202d1001c40c01c1c412031021741c3c081d00205031401c4610740040c1d0300c25824240001c40004040c4182d00b4021606241d00c200c41082002041c0d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 598502544 1250 598501294 598501301
    0x81b0102270901060201020c1b061e09040f0204030818060f12040308090d02061b041d060a05031506090c09030a060903091406030f15060a030e0105061837 68
    0x840088402c60032070b0340c0e00c1505034202d1241c5038552429411a8501003200115100500202d01d4090480d620340354041441e03075003400c0f0b01010b0702c2d050240020758480f81d140901510161490b050002c61034145103070750310b00b10380c407e60b2008840d440c0e021111050558490040d103800c0086d20500d16030b514086240d8604800c000c4408a01250201011901c500030018420b2140b00c0540c005101c00e4480d5003102c581004280162011380300c2c1000041003e01c5a000640c40082d039400d00c5002504286040041c0200b0790b4004601a5000e5102221601c008015140d00b10f10140c3d17400d0304a48852955041d50b200d2280841d800d8800c40d030b103039001c101c0940c0c01508203074040c0c0c0d50100020345034172030150480890360320301d0f0b0b20203001e001041e80313890008c1c132264101000980981e0407a9032280410200c2c0c0084074a030011a03986c081428070610280145a4446800c889081031200c0b21614420901009000f83c12064249100d21141c60784289580403044081f0803000d002544942420019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 598503794 1250 598502544 598502617
    0x112101060207060e0306190e010c1701171207030201020f040602031e0306030312100906081501060513060509030109060204090902040e01110304080310031a150d081b0102 75
    0x522072680d00007403142c130400d094407540d20b00070f02403d01901c40380c43c00d1034099155100148919621412028440c101344144402c1d250360f5224242030248446807040301002c16449070001c2495001c000c1c41081000c905d5220409241002c9501e40c0500d050407402400784800c0c0c43e02c107240000c1c02140154001010344081440d10404820200c0d03421200355550000707480058042d231080c800e0300014481011185d030300141805143c860150344d0030780c0c0c0c8280c8880ba030105480fa004460340709280402c816041c0c0c050400c40c14224078005544856001c0d00072a07208401c200f10303000ca0000c84907503085d00503410050f0010400d640b034a0311584580d009101c1d01408074402e134039200b841d004480e418002c10a0200004460700d045940e0340d21502519480206003040c411044a4007000107070b07072512141810031100d000c03032082e45024060709002001d4044207502c1907824059590000b4205030440e82041c6200403030089031000c00d01064064011400d1400c0e003260360341d01c01c10300c3c8140f00006165 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 598505044 1250 598503794 598503797
    0x302060315090a0b032e180201170123031e1b0306150f1807180e15122a010e01080c04030b070e09040633030611210106 53
    0x503580710003c62108903200402203680503003040695190f10401410004003494000700b1a556004440c40c1240880ea0001258607140e206c1c01d046d8815542d004544110a81c18141c0740000355040c02c5840b080100381d041c49009600d00c6611815064a090148a09003014213203030303242240324640040d454602c6010840e515800051203c0c41a2400164442c0160024800040c54000d40018401c2c1000c0a0088541000040305a002d030508460400341c401c0c0e0036a40d410700341403c501030030058941d09a01c074000c25100c0c3e1b400c1c00705400100c3e2a581296100721904103090131100c10090502c000d0f0003500900c0103280d540010040118502614010826130311000080c0c5484015a14903105131400302e0701800c1070106000099003201041e8124520341025003807940c07180006010304d40304503801c0316100d44540220724040e541c0600c100c0e0040c1a103103911108d4603400d203d0081c0300b100e0711001c0c2459450364510703643c81d96038000300d42c2c0d00000344d555420f89001c03c01e2020100c031400e124010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 598506294 1250 598505044 598505059
    0x9171c0c05010e1c03060e010e040f1e060f06031a0402040b1e090109150303030f060302060a03091209050d0605060d020d1b0f050a0e07020c040216021e061902070302060315 76
    0x413030746032091050743c040e16075100c4049a0381e4205081002e00c0c800090048500ba0707080c6003003201043d01c081c0c0b14210200070740000d03601d0714454a003680c19981c148801e401c1143c1041020310001e40d54050662042100704504261030351140002b44c043d0140d000c0a42d00030041200c84007580c40c1c041ea010701301100540d81481d0a17660b07204001c0465039540d01c00e03402e40160040610000b4400e03040180c1c407490b0b00201013a020744a13000507840c0c0d1303c200f9400012a54882500040054890b0141201c0c100d50903d0400e02d45400d02041804041c003c004000365aa18005107842e5550302c081040e85402070561403800030b182c901a40d00214440502e20000e03814003000400318104bd2044090344c0c0090843c01c1390034a0034603c10020100582204198002c040c99040305458a102410441c0540c0380701c044a0b0500f40140004400c000302401100b07100e16504507070b1611a138040700c00e030409482000e0001407003402d04030301f0700d103281c0c02c001d6110328004140205246000301c04440301c0d000701c5208 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 598507544 1250 598506294 598506343
    0x3040f0204052a12060127270b030c042406050901090801060311060a11010908092404120807080c06100b030f0423070e0709171c0c05010e 61
    0xf201d801441c00e41004071102c1400a141c0e544201c00b030f0340b9500d80207107906440d220b100034000c1507180c40e500302030b901500d012002c1007c0f101a00010556103840c0004001e9450a0004292103040c203071078841c0156120781c96268440d0415030048000c04001491001242e26424000c0c01030b03100e03401040c0040c41c250004200b0f0001031041104503a4008040341001c10701c0400d004950700459020f209004600c0c0b80034001e0741080c0200c0300701c075108191541e5281000001c00440302e0b4841e410880f171052003604a403c1c690b84d80308a805940001e45055103041c1c182c074092029205288000340720f008007040c0036101c882d001401d82d004001000c1d14160064460325926107500040b94091801c3e00004041404660542e620100000403401100f07108640040c03a240b03001d4240e4042c00c031080d500010031031b0035940a50302d070004d0324a5101070010900c0d9000c65940c0e0300c100b200ca1000d010341d68402d03038000500400c1018100e941c0030000303100380c1460f03034003a0f511141500100c501c185501d6040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 598508794 1250 598507544 598507621
    0xf052704050f070804060b0f09090d0f02030f0711040209130203040b0a0b03030901030b0103060b0403030221070c090c03020d060305150c1903050414030f0d06060207060804030503040f020405 84
    0x20900c100c0441e0764521300e540e00d984500300030304103c00009400400080c090880703929807511007845410044010403039001c01031801045a401c8108607400c41d00b052014800e1068110304490b003d40d00303c4d400041007111384002a0080c850104001d82c40725220700c401c2c162280c50b80140d485a070181c1d007507001c3ca43d0703036042c1103040e40d018000e811707031642040007140203541c069031001c030f4001010700d8002012510b401e0030740b1880d405900150b026070320002d19109110790141c5200e0360f1100181c480380c1040110307543c50080c241f642c01101c00080c6c4076040b103108680300364141d4645c07520101c0c00340702481d03890800c0c0d9150003010803480c20100000c000144101086011610301c0350640d42c01c1000855444811801444060f00c2241c4116015400a041a008101410b010010810760903500c1b0a080449002c45006600000654211040421000c0d400204c40e81c0d2164040c1031141e0b9039607541c98074002e04079208200940c0a4030349010b00c12445902e16126486c40026180d40350910000c150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 598510044 1250 598508794 598508821
    0x16440a1511390f0f0a021c2109050306091f0f1d0705100e030a060c03090515010603060501080402030a02010c0f08030901051b07050d0f05270405 64
    0x41401c07440c04100291902c00c80c0104889402d19001c04000c010080e40455070070341e5041090610046a00074a0721858504091250b900b26401900040840600c143d01040b42e44240384003141c680c2600c60800c2082c0030040000c031030400c1a808088014543d0120302030140291030280a00910030716002405c0344c2c00020b1044c41da080c14800000c2506c0750090090060b00c911400d0b0a00a0744501c040718694107090404440c00d8802c0c80900741880c185002d209503170021240d504100325206d6901c0d0140d860106004800c1fa400c44804611500c3e00345094001d44180b44006009100303a070058480d070315031454024169182a135051000d9942c032001150080420350300654582c00942413540150301034030031400c81034030401202c0405041516404800d400845203590103944a04c1004024000c0c200100d035800f2140d400c160602c43c25844540c0d5810502610b942405951000c3c2c0001030700600a8425802d05d48107031201c2a0700309441e4020781c905c8810018082c504000100c3d905a070300c0704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 598511294 1250 598510044 598510061
    0x8010e09070302101b20060301030f0809040603120c060b0d020112203405030a11100207050102130b070f0803040c1805060316440a15 59
    0x1001480740030304503020041450015120700f001c0c429000a00700c4842c241140401030340e809507840780d4441c1c0420030030246008070380215038030030882000140005065405110803003501300c03410b00e84ac1e90501d408203008084035040038154000c1e880e1016400b550142c0442015449410140160100402448140c44590300000d01140558a400c0702e01c0030360354000245204022402001d10702c0200e07140c0307420303400b10381800858503403480c01602e45031107110140c0180d403144140c021114121b031074840d202d0281c00c11040800c0000c15000d40d00400801040b500d0f1340340030200310359542091810038000c0d03102c444914038480c4040c500140140d6420b06603050950040001035510030aa41c500f05a580024001c440d00044842e0201e4480b901410074400d42c1d0614000051608108040616010b0500b2801c020030f10314800a01490000384a0710066030442c00d044402c180c144280403a400501403141c64840c0140060541c61000005000d00d4040c01540c450300341c2603131505180140d9880c103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 598512544 1250 598511294 598511311
    0x30a020c100e0a02090a1506020f010b09011a0a020a080d09060b0d0c260a0305120f04020a17030c0a0b061009060806091519050a0e1905060112180308010e 68
    0x4a02d43c10160500640c41680001b01010004032440d400b0a094200c0721150030000059010441d1a17008907424418924094030444010409600d058850850158100501da130b00f0003020405d0010a40200181180250301c103904a4441d03140c8002d04006100c184401d03103010342000d02202c05410314160031030030395402c41000d003d0b1600384130183c640d11500c550751030040008490324609148091003078807a014032951b0350700d58990102c00ba900900d0000f42c00c030368044284070280001603845590000c1181c44410080c2c044a1145200134114050100058001e0081c07002a1041010024134980f0a0000304c481c0b100c6205504c80c1110300d03018a016900100c0c82c001c0c0850030030f00e00545210303400410181c84580d0541e0f000d01280020960092000440040303c04c188030038035107106040c0c05010741d0300c1141d40e94648540440112403c0c21803c941c030960f50130204039964841c0e111041100d1417801700344102d0840a0842c0c030f000110940550000d001c2c0c0700081140d00f140d484003409850407 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 598513794 1250 598512544 598512553
    0x51903022104030c0c030615060e0f090a020d0203090f0106080a05101a04020a080708011a09090711060112110f0306060f0316080708010b0406062c0402030a020c100e 73
    0x80d5004541001c0c03014100b038090061110440c400914003c9550018500c03600010441d005402190b403155802c0d40c120030180400d003080c5800c0742e11034030359400c040c0004884000c4242c0714107030700d10000e20a100020002d03074000070800400000025594000ba140c0c00000c2006641e10404c0d136442e401000700c001e01b0798102c1031810400b21801e8000071920b0303a0403e00000c42910400c00641240d01600906012646000410540320f801c81c09441c01802001c01e03044500302c04144600f86c278814231440c50322641c83d54010410131071059400340384c1080345c1d400b291401e5071a400401a082c40e000c80c12501a20164542c03401800c101400d40b01507180a4000c040d145c0780c01c01044113a00c112890290144543c08949509041001c030010043c1450000703410f545082120b20b0b400e4a044200c200e00581c1480010004280e1004079030741040a0075100c00d001300300e0254044100707180d456a4980c8540040103000380f000655000b0000e00300803008079005048568401c03801c0e60000011b145183d0003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 598515044 1250 598513794 598513837
    0x904020c0f070b1e070c1809060b12100e030c070f03060b0f0904061e18150905060105060d140106080627010611070801060f050907031415060702090705190302 70
    0xd984c40a0181244074001c1d5240c826103034810514000c0c4400c1040c010180c6032000c2c04140f00461140c070100300c0064620040e14035004203450384c4c5200c80c4038107640c120395803203010201003810b0003940c805d501d0700f41c281c1c1c50741582c031100881c01c81810301041d140c030342c076049101c140c030300e069040381c900700c3d001520724203031951581c86441c02000083d4400c01c020b1500307890540c1c414411f109111480d504144883d100380000c3c00d01301400000e05540118003450110f0040c00714500280c25070464500b00c504940d58044028504049d00402c0d0403040d00c2e139508000400c401d90040741c0540310349000c0d144848211029502c003940000444000702d0450400c50041c80024811601a9006120707013089803030143c0d07501150f50071a00f141c2d201d07400c1035400d60030030300c02494260003058018085140034031603035000354020301c4084005401c503086900080d5403000c541e1100015101840e800800c4100a460045070242c0940c0c0b00d54002c0d0000c0c0f02c18540074218070700a1003035881031301e0382040036803000c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 598516294 1250 598515044 598515097
    0x513020906030a140717010b06040302120a06050c3c0901050c0f06010303140c07050f1302160512040b070b0a15060e041d060402150904020c0f070b 65
    0x40007510058040c0100754041d00030400311841018110329010040105030300d80240f0200b140200c600c4c0f085564148105906240d94460640d801e9070740485155003030594103140b032442e100318610014206400e041c108041c0c0301c180d40181c1540381984104111000d40b10503180c440c0808501083c250244800c1400240c0c501480600041c1006042aa181100036105940f41c20040080c40c1501e501001c0107204150342b00c00400b2044240e04091802c00c0350140c0d03e00e48482680c0589402192003042c100c2d026a00e0345c0c07603840b0030a03511300210b60311255a070580c0e81c00840c9502c10785407482803403c0490001c020300112011a01c072011b0f80c50808031181e03521500224041e0012903040e48402c10f100650b644005072000403c095100c0700315007900c42c024071054403411182c0c41559640300459680e4041c0201e0400d41c0716a04982e28011046043c4d9140400d01a200a02d5000307403021500801c00800050380101030b0b001c600880b5401c9a0340d80081100f4030503060545e403c50210240135034800d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 598517544 1250 598516294 598516309
    0x9080d030e070f032603090601151b051605030619050c0405060f07060f0203041101030207140f150f0c0f0c011107060605040e0106031106090a05030f1f051302 70
    0x80c403010589880d159510070802050f902da40080d10140616030950315214108a4105901c0052055460451415031100b0341c40340c20500c2155180b00035000000a990720442c4800c02461000714011440e0019003025950750b150f00c02020340d82c00303400d00302041d0351a000a0b02072092a4583e0400352469180c4c603501c001d0100030344599100041808081882d544100c040d00c41034031904012030701d4845905241301074078a6000c0d415001803040050001083c942100c140742c40100707013000b594403605464088003520316205c050f425030045140b006100c410200e440100c400500c000005252a20b07540300e007031005c00391000b0320107400400c2403030300d00c940c050043d0010302c100c58000150028030104c01e00305a07006140840e5803c0d501e0b0818042c0b4a00b41c49607010000c011002004001c1c11541c1c0c0c403014060f90301059116150102d8110b10b180d880d0580c05001c1e04018007034411300c02c454900203689800c0102144201c00d40451104254003040c401d661183d0540501740040000980a11142c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 598518794 1250 598517544 598517561
    0x14060420030c0402120613020403020a050d03050d0c02010b01020d0201181205070501050f06042a050f09040204080309010906180605031023010908010c05040e06181003110109080d03 80
    0x10700488082c04095a224400b40120480d8041081c40c1c0340b900400b0003107600054124812010b1051109201503220702c00c011069a80581d00b01046280500381034810740a41d440c0b01044604002d0f4801113140d042d004245126020707000c03250300b05406481031b8240c494071101e034004418800d03c5040481c1c0d11080f84410302804e410000e1030402c041d120385003075550840c7d000701c00c0701c1c1110600c801d500f4584501c040300c50910f00c204000e50703110494440d2762050004580304101c404130f0202804c4c21110200d8007460b0300200115074840c0e40c0d155954a90f00910000d40c0031a00708600003400034000c0603640c104401f0001084181c50500000340e900d03070406840c03034040f00b52514020462a01c0d6105038804010f5002d213008000100030001406417140740c0003900030380d040c24001861182c220080d24141c45c110640800d81d0754580d0013081900c4041d91226035a045144188245031449494100c00e581c02441080400307040300005542e82c1e5594400e00420358030400404400904c1303507220180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 598520044 1250 598518794 598518799
    0x703050708030a0e0c090c030a0e0304050d0501230615160f030509190b04030f1b0f090c0507080702060a09080304180e01150b0d02040f090914060420 66
    0x522405854046042d0401c903016490300340e4540058211030010011101a00c00490307840c01546050907000c100e50101030704100503191580340ca45040a070038001d5801420002e48071124038605810320074041c0c648120303181000074040c410006480380d510300c2c0341e10564014003151001e4502c0c440c60401a0310448008132a590181400c60010300c80148400b90706001e50f46141d25545a5170401c040c00c1703c40c10fa40300d074201d9007850402c000e200000a40781200c2e0041002641c091355401d000e8803c0c010351080750740d0580c0d6a900070400c0c0d1002c41d02c000940340600340070007846601c0402901c10344584080542300c07072020b00244006107000c0c4018854014245040185980d075824482d00d107030840d403c444005003601d20310000083c00d07441141e162001d0400284844454800b480411420724007078000105070004540108004a8044400400d2100501094141d46506410040c41c5c026001c564070001d081d1400802031000404900a80d00000091711683d400352404c060f4400e440c64898 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 598521294 1250 598520044 598520047
    0x2a0c10050c07180c08010f0b0a0302040b0f0406020d05070507030f02030a060e010b0102010b0103050c03040609032304060f08040c050907090e04110910030f08030604390e03060408070305 82
    0x2030741c01c402c1c404036000b4542611980e203c242003c41e42d03010b8030004004102000b16442c010488205017880e80c40403944100070041c0d0b52141c40d40110007078800e542103030004800001d51042e00b042024003d00888000307a003600c1c1000b031601d800b16180d104d03a800140079503204420500208515010840d42188000c1c12101c0c44403259480d0030982c0c00d404030801c0141d40d52103030300005580a000c0c4800b281401d103010000303841c0000701d1a00070301000d00301070115665004280100f600851700c095110084080703e8401006200885886034400c2c02039038000340c59541010049801303400c0d40b80c00386034041c0d00580090300300800e0106070100282140c1c10407040c040c00050710b41d030748001c060140c0d010f00c400448103c21501444500d50300074000a840c0c0d0303640d41003000881c00c15480e040c0941e912031203042e580c1d1114000100a04120402800034030740351100035140386610300b44070311420f01122002c007909003052801d0f05c6c10741450401a8164100c1c000040016120384010a10b0710300c01d0a103075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 598522544 1250 598521294 598521307
    0x2040905040309142713020a03050a0302070b12040303110405190302100f02100b010e0a06020a120801060e09090a06060b0c0f0309010e332a0c1005 65
    0x110140d540540d42a408610450400d00006080d000051080d01c402c0e116080d13040c2e842240d00d207407000d802d5807555044040c18082405440c449041004c00c0b60024005c02a5a84a0900c00c1c1c65440e111403c901510842c0781c00100101030310117545038481c2c6940001d40039a01d0351400d030046d00581d484880081d00c2004080366694030382c0c503143d980c84210f020304c01c0b0702030a6105201c44503143c0e1881c0300a1050541802c0625503000445034134114081401107180002c40006031252a00d511406500425496010800582c0000c1c5411090302401b06084842d454810a0340c0401003130186200180381d0106900c0e1504000a02036049401c6c0c1044803281072094079a00125000c0d0340252101802c000303130010b1a031400b0046602800c5401c8050b510704205c0ca4000b07403085004105413402080021102003080c00f0016001d1031400c10341ea9160a580c418007420055688940001205038503406020081107150700c50f20381c050b01c40c4000031300306078400c481009960201d18079030204200303040110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 598523794 1250 598522544 598522559
    0x17060616140102041805060a170f030f030a0b040c050301062a03090602060a0527010e010905100638130303210e1c020f070f0314060c0a030c030204 65
    0x61000c00700c01d14000585660800c1414052a0a00c0149004c0a0300701030521803580e036000300034011a032030352580300880310381244243d0400c000d61042100d10302010402c0d5090081040003503100c0d0f11030701400c0040b00908070400c405c459480428000040c81400140301e01030141e10301e5200856400f4450301c0c0d0030341c0c0100110442ca00c00d0400c0740010321660b000c201150b0104845a0004503800c4144400c0c03404042814000c0100070103011010481e943d10080c042c2c003988442c1290340d0b01402030202440e58240310741d0f1060080040f00b441d48c03406900003007c0c0b4545e001e02441002181100500b40b5500c050400c0050262440c0703d20300d02c0410100c55010003110554006501c640c44800c002480c040701640303501700300103030b034030a66041201a0000038400f10f1541c00c1d4030103100007a014131085000403413504802016440c018450182c0214a0f03641d0b4034dd100d8216446007109005d03000c10464419122a02034849042200c01400b503910f10f20b0081c2c002e10150f00c0c15140043c2030070340d5401c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 598525044 1250 598523794 598523813
    0x30206250c030317090a030f210e0c0406050d15060b0304050d02070e0702031b070f09020c0f030c2e1a030f2e0603050a08030106080717060616 63
    0x3000c03129080703803007000c20030140c000070030100300001090356412618009600603190349110b1001010441d0802d0070510141c02101104094070107c94140910b4504520071802400003a90201d8544280a501510781c50540500c00075510090410780140c0071551744c0b041c1d140d0040d143c1e00c1410303032220004900303904004041c5116a01075001042048a4004081e0800c58250441014000c0740002c10041e540c0001c1107407a6821180c000c451050581200681454a280c005051490148200080b4402c503034014250032400b0743c042e24030041d21807510300e990b8410044040b0407500100c204400032508403030641031f240050444040143c02c9403042e03e045038030121100307001c800c05108030304160408125990201071a0001400000036102c0c0410002054440241d030024032004040300a610641000008643c0b000032100040d0183c035148003150002d0007040009000040050a07061041e54581d0000b5156180c00c500303a10745006002440d4006007040b02904002000d6500141c0400f9 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 598526294 1250 598525044 598525117
    0xa0306050c030a0501120c1509090f09050c1e06030403020c1c03030b1020010603140c01020d03090b040f050a0203070f06020f010504150b190618091401030206 70
    0x404a0390b0345042d809150440b54103801c1040c0d501c12001518000030f03540c0c0c032010b099030005492003401052920044840c0d0015030401c000c0c3d00d051946146800b00503802c2018403e10540942d0030307051000082c0072105c0840184c403003071800081d10300030403820000000d40d042400b038410b840b8203003e84008130345401d1180d0700722041d0710300d00800841459498419403070115411102e5054400311801d0090166043c6030801d00420007036030441c0040002548503a0003036a114070700905903441c3e010526101c5040e00c400d00e015004103604680c2e001d1091240704105640b0031700954081d26941c40c0c440d18904a181c00701d8242c070804c440000036903004c02030b2000a0400c0c084100341c0604002c0f0081c01c00806410076209607040a092100080302818a1038001128000000b200803a20000030008114104481000d418100010420070383c401070386c14607000408500b5840a913266541c2e000c480c0c5606072170902420403c010f000502c0d1140085c003500390412104801c0b4010310b9031009140031a00d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 598527544 1250 598526294 598526311
    0x309030c051b040c080f04030e0420030f0105030601180207030905060d0509010f0b1305130b0c19090302090406050709170114102103090f090e0106090506060a0305060a030605 77
    0x90450000b6180c14002c071156003566140140c61400e04181d01c04003107401610080038882e003071015840648942d80004007a810703a00703a4244907000060443c90640c41640c842e02d40c22182400070840381000240f99048030032620045000d550003030281c00003500042d00450030444100c100003038950380c400182040318458900090b0a0900202240c00c40300804007841045080005080c640c3ea1034034900c040b16542040b022030503071365059280c8851664038a000b0801c44440c402d010780c55127100c014280c0401180521070780e804802d0010b40d140500303844029840f44140c00021f000070210b8000940011850420b82606500c40c0a032442201c40c0300c4049045039580c07914103501400202c04a904606c502d007070748031250704040a41e0f07105035050b05034041c129808007001040501c500450f00003417080041d0080c64640b00e00d01040038105141c060060b66003045e80110b281c9005103d030780d005200051010b8a8200a40b17000d802034200104139643c09401d20200001003000341c01840d200c0d1041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 598528794 1250 598527544 598527583
    0x30a111209030d05060f06120c190206010602070608010f03120e03010c1106130c032406030605090f06070e0d020a05040509032709010302090a29040e03090906010309030c05 76
    0x320003090040351001410346214071b10403e0065440d84a010071030f003031804c110381042815962007901140074400c0c620710051a0014001d1001090f90104d0340f030341a0b60340d960175112020354a10b02161505000e00446641c2d40d1204004c2001609075041361815103c81e05200d00d922582c0b20000f400c494514540310045000c0368403c02c41094180080c07940300d050540400040c1101e074640c1003040c5008d000c0105130100c10f649030000d103e0005040c9440c59150b21080c000c2a0f120b1034050040d050503103243c04241320749410140e15100c04174076244210b610783e581e40042c000c21b20400044010950059070090700554001c100c039195802250700c11b220400045941e00b64036001110648110740358000d2030301044001c000b842c0e5070745611a0441c0d80450340b0a00503103170300c06214014085a8145040544288140c2c8c0d0607001200240204010480e010409980c4050100361207100341d014044d4084032580c0001c0350756010780d1121224600074944a450300c0400d80c2d401d446c0a0184c800d0402b100e40c1b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 598530044 1250 598528794 598528807
    0x9050601141b1618110904150906030f02090a1a150d02030406050708011e27180201030b0316120305070c080604021005073c03110c0a0803030a11120903 67
    0xc4080e41c3d030080080050400034600103400e4119140615446d080c03047d0340f04c41c81070300d4030852030600301d0180034481010001240e40b403802e80344034a1010400ca015640280014103d21002e1090686032021014151000200304e001c00858a05070114181030410600010009005078400b940c46140703d4500003405051009010b842841d05a00c1a0b044050114184150084c03030201d0100700ea401d00d564465204441e41d0100845c51070b85000000c04c4e24013040d441c0b00e0b0006c1007141c00780500070388007006000e003d007090540300d203441405605404070403481046a102802c0d103e4200f6402890305909240c4150b903940e510315550b600800a070352001091100750326104800c400c40d040541429440c0048669540f01c2e40340b164038100000b03010303624188504e4824004a815450382d0301255804003001c034075014002020420486840348541e19803c03025092000000046c2c0b40d0b488011070555407101101000307403070701103c00c150a080c01c0c04070f800c045890808030f0780030303100300ca01541c1c8070354 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 598531294 1250 598530044 598530059
    0xf04060e151b040b0d05090705181b0313170d021204170a080a020702011707030903080c0a020601030210030e010504080d0c1d1c02031e0709050601141b16 68
    0x82000c100d0b400d001e4010041005a40c20990031141c2c203c18014001c902c50740d60350b4405082400703642c07000d41c00c02d90745101c2d050031a000d03003c014400c00c009180e0070014031200440040600003240d01c61082401d4000076808120206907418810681185041ca0501d0800c95801a6040070404000c414460000e201c10011103110049a501d01c11000d81c0c142115940001c082c101e006e401c00001c5940080c1c43c40035a4400c44075807520041100b403201180c00e2001c401002040303042d20a800007202c00c008518220454001c8501d401c400350300030a07803a401e41d020000410000e40d110020326030b030784225040c070140c02e005041c8914050740d070b41c0342c99a61201c9240151072304840e115040081211f09070342c0c50135640c8000040c020061740c094032551408998021410503155011303515100e8200030325806405102403c40301041c1c030085d43c1045035503240344019210107940d081d0114140600c20310441117074502404c8501c0c8050107512200c0c0d050503c036420141c2010b030b0500c2c0c03444004424003208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 598532544 1250 598531294 598531321
    0x60709031e02060919062d1b0b01030506010503100207050a0305130e07030b0111010b0102071502070b0417120c061504060e160207061b020613051f0f03050106080f04060e15 76
    0x4035075401d10010105440d1210307454021031f052032502408076400c0c1c04090100384003070000e04564012901c2d0040d58480c01c2640d03072034000740700c3e080c4244243c4249170360100550003901c020b641d010b4000c1420407415601615160800221801e040c41c0b40f0701c001580c04814640c06001e176015031000a02d40710420001086401041d03203809443e03040803203503c45640d0000b481d02c2100c4052500203000f0325404822401d1580941c000c070920400445d0100c0d0f50804480e01c0c0b04d0820040b4105c2c2c4641e03425110038403150280701207014142e000703100050101c9480012040045034018000150151194150b40c0c128000790340c0c030f031910450812020000364040107000e020f0151410106e0240480001c0b1001c60921590300031702404010030142e1001002c0111000a4500106040b68a19000e801d0304a40c4140340f10f20b6000808444200b00141e00038031070a8140c0748103942c1d1010a50b5869440d62606101405c00c88500b80e846040f00d030200b20500481512108505858055003803444204c404e9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 598533794 1250 598532544 598532567
    0x1e010e010302030f071d1806100c031b020301090f03031523010e0f031f0516080115170a020915030c221a0705060709031e0206091906 59
    0x41c1441081884202100d5001c0c160303100e071007032401c0840c40c2d42000c0484901d05000826a03081601c01000e0000103d042c0c0b0401d200300d4064400707020042a05004444950030030502401240c104003486101d060007669980c14540064008510128140c0c0c0e842250280304005a0000e40e44684030b042501000702242d00908242500d5020b13104c03001601510000c00f80245814403000c1c0c04420016101c0344071125103110000c0c00e5505050004100c5c0804940c0c0c8100c241c54079141034002982480d84442a4042d0702070f981e1001903980c240a1102c44290300c3c08000350504c410200c4074410380d2100c0c50501e200d0071a8010141e1100300d86800d00c0305070456103c0403403c0d08014810420b1500790380007030700d50300f4008041e42321120040520305441f140483d00f0480d0140f030031308001c040c902480002072502074407400841358145c0e12001c00701c40c0d170907103400000d0907000360045213130061810540d514000b6000401d4a841d200380440041c1c24000c1c01642e4001050f0301c803a04000750b541200501c8207 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 598535044 1250 598533794 598533797
    0xf1b0a0c0b0a0e2d0103090f030305071103030921070c080c0a17030d09021908010213060201090b070f05040503010e28031e1103120609130b010e0603010b1e010e01 72
    0x4001c0c041c582e41134281c0032041000c0b1000d40582404440760b21a42000e00704075086640c00095036581c1c180140170300f408072a04800b0501c0302251280c4282d00000300c0b48180800405464403690020702107001e444a11100460301c80d09210541c0452005845200203041540041c94000301d01d8042c4190720f81c10707500541a4044030282203442d0403011003240c0c1c94200800700020a40c4180c070008403c502c0205451581d00b20900011524800550080c5803030010301c5882603002da0f888800b28240c58120800030b1403031003440007040c0d41c1402114811000d81c0c441c00c2203800e10351500042800c440c5080c410459650140140b01e606405251001d603108088500b0080b410a41c0e48015010314049000c80d4588441000c2c8007081921442001c0a4103602c0030036079940b1f140c000b00c40044d00000391380961040c0006d00105002c0304aa6205149544c0c0c040140c0801d603113061110003a015004110a4165481c4c10400e03407244e507854990001c2c1e003640c5a24021300d8403524001481008484410703070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 598536294 1250 598535044 598535059
    0x20307060c030203120606070f0b0403030b060f0d0506210a0b160212280509032a010302070507030503030403050c010b0f1806011205090d140f1b0a0c0b0a0e 69
    0x180481d034040202c411780f900301c00c0b86445c1d5895140204500744a007140150007082703010580720800190f460b00c1350269019580610034142d81c07404102d024031803000e03211075000042081c0d00220005410940d400203004000e030a500c59400050904504052003c0355250445c400e42d0702040380184d0004e4200c8070b505031014040c40b848102a41e20f840c1d070004040300c2c0b080030403012065400720480d0640504d04622039034640110718809000d42c1c01281c4a00d102c0d0142d00d41d600c00740809420440301c040a0048100410f04040380107600075404503005481c42d000710100400420810401107000390302c20f5440310740c0d40e40c0071315505013120301c0c00210910800140d400d2400b00d0351410030b811544010660a9401031710740c04010b90f002000c0c022a0a001d50420007003150310740000c11000a91403550b19205040140100498150310030b0f06001c06401806000c5454245002860080320140180848820050544806500c1003035540510300301000081c16030300c0a41d010341011320b1080b00b52a11b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 598537544 1250 598536294 598536317
    0xf0a0f0e0f151e0a06091a040b10050d11091810120803040201051b0d09050f01051c090503040b12010914160518040207060c020613080a0e0409080c01050402030706 72
    0x1c2d408443c00f018241521002d0003c00c0c00701c10103074050300c000c1c148601c040004c5c0600f02c40404044c1c10700480c840c86203143c21110111810070a0b0109041e1f00560348180c6442c2403510220020480303030011070070405050181e803080e80c0354401e00001690000301106401c0c6401c13800703003842ca849600300d440503920303a90a6000103089842581c0c0c21a0b82400c00546440c0205040300102c0f1140c0c030038013114030a4083d481590354010024a0550710b040e964841d400c12494019503503131040540b1842c6140c00c5100402c070094540d880030b5038981c0300c0d0050301d103080e81d203800d500c03d90b401180050140d0048040100038000301c500c2524803e03941281e50500e00d140100002c115004400c150078188400050080410244000d00c0c40300310000400c11501c0c2c035040e0404400400303410740a540580719202c003040c6d95900c41409000301c01d5010f070341d10b45011060b10044030149485114280c11039111031025000407415006440c202c6a084000100ca02c1c0a00405140600c079900c154180041c04411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 598538794 1250 598537544 598537561
    0x7020c04060f090516020d200a0f0606090612081315110106060309030f0f1b0b040c080304030f03050703090306060e10170c0f0f101e0201140f0a0f0e0f15 68
    0x6061f0f01104d1410200d881c0c004942c06048091003450f0f040c203c6d806144541001c02446484038408540030b100200096611041000c045800501411441c11800c018080003e6802c1d002800064800d582c50940c49680700c3c0441c43c4074000051940c0807440d10900e10501180900c41c0000411040c0f5090210744c3d161340b005888229403154460400000f01c6440e00c85038018408400380700241c041969940d074250401c441d0002c019682107910150300b80d000a50440004190790a41c0d422003c4140ca000381aa401d90f03140e0f02061040301030042d420400000f04019200e84d40c0140b003900602c0c5082d25120b0300f51048400707181c020005020001c40b00309840080000c1e10240b00c141501c040c3d01001c480400100034400c000390003640208205c00f60300c14160b000b106104562855010318091441800b0700780d0070f03260b00d00c508107400580400000d40c0030250180300c9030401204007000a4850210403441c058034130104525406d903001c00c44514000c3c0d420002c1c40000089000b0803411414013099 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598540044 1250 598538794 598538803
    0x90603130606050303040b070623010b130503060a0b01030e070e060f040906050c040806100b0d020f281205010803040308030606130906141f0807020c04060f09051602 73
    0xe00050180305003080e08010180d8000000b41400404032503c0310750b01c100b40d2400d5440490110344131400c00c4411402c04814912140780420001495003850f070038007009548607003010b03034807a0500010980008003601d05000b9180070340f2080d075001ca5410300035000075080e941500e408809a900040c010083c80e1001d40009400c0f8404844548103000500c00140207446500c0c0090314191034036060160075508070004108540f1403005668042d03031800b44640d1055810710034080d43c20000c000b00071662030103600900b01c10305d0403401981400c0081e41410300b8800e079404800c00d90032440d20412815604140703050040300b5003c01c10311003036040605280e1203019520000304584030101c0403071003d940b0b0300306656400c0c0c8803040e21004c0320380c1c034600074002d801107100b465020f40341c0105040c194144034020080c015001094a2050b500031030301102e0040b0014500d4085001d0111004441d41c1c0e58041e00e8010701038100580d0241c1c4c20f10f4001c50860707001410218445000c00200e4413a60740110f03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598541294 1250 598540044 598540051
    0x60715150f240e030f12030f010e010b22080a030207090b06160b04020301061706040201031a1c0302120409050603060a02040f03030e04020409050a05180303090c131410030512090603 80
    0x3d0402d24078050710740840d2500a0a080780e0070a40246044d514420032440003440c4107603000711403582c01d40d03694654004880070a015803040c00c0401c100c48005001e881044082e01e181e40149120f405640d482e540b81402c101c1401100160040d5004109406407805403a00c100f000b00c4103249400341e20f0300c000d09403002c030550003002c819001c0c0004040d55003e5010300700602c5000050050110740303000e10354540310120b40484c04a450039849800b1501c0b80c009a081000010300b41e111404560b03034180305109020b0004138210300c101414058000c0481e00030780000d0408200c04603003400c001c1e04050810400501d10f50160b407050004001e00e48286501008403a01410030781510720401d004140a07101d150048032001d810710040c0300c001d42150b4805845020031801d000607083c0040d078182d440c0d00c400c0e1440c04a0b544000031400c007501e006969245421003030b103030026601e2070000e1001444c1d00111b6450610300c403e620104103108051004200e00711144490300d1800c4102e1340050326074040038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598542544 1250 598541294 598541297
    0x806040b040219060e2b141c0f231204020409080d09061d0619020c011104090b01030b0a05060d09050d020a21050316030b0d0501050105150702030c060715150f24 71
    0x80c020b000b02c0c54000d01a210b84c0c42c0646410114440d03030b13a040278014030080c44082002a041140004000100c121305003d280102e4429900d4a081510b141d40d50f410040c0c001c0c3d17841695601e0a10003d480039000b4241070b9a4103001245680503400c00d0030896613000b07510550450180940352214101142007a8006040110165000b2441c1d01580090007403407401000c540c60500714280195184c1c1c0030b44101d89400400b031110781040070044040c0c61010039516000040700d0003e01035440c002000d07110909040b640007800360629101c007071410504003921005a00100340c0c1c2c4c4184100c481040a0b410900e0402d100c083c14003c038020000e10000707040580b007014400c1942206071098101001418000380310308500821414080c0c0249000c0c07041c5c9104524080261015101400664803c582c004026000c140458014001e1039804103504035488a60210490120b00c801d104484901008120b1940414148501c603100c5803480c1d04110034584041d40710710504042c6042e041c003e180903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598543794 1250 598542544 598542563
    0x70807030f0821071d0f0a06050a021207060f0b0d080405190306050f1f030201080103060213150503090c04092003010f0204090213050a0806040b040219060e2b 70
    0x1200700091a42c210300c0d10848460081130014080d840340d2403118190402406080c500241000c001c401a41e40402030b0300403c40020800025000300083c254020160040e9958161007400d0846c255100180448115644130a0040e04004d1486040b40000050b00da04d10709041c2038131002054001c0b40f060714440d2007441c944906101b80c0d0740e01c0030000c1d98452014001f03410000030b5001c0c9000200e80b615404085840b0814800c40007041c900f00300d0350107840b1a40c2507404c5850b182c001c0d500c521003c203c1e050f40e0716000643d00ea800400c940c3d8103001070f9aa00d4484c00d02c2000c0c0e5045c8100d0ba0f01c032901c0b950802c560100070558200c422041c5080d00028200c1d01d03100340340401e0141110380800301803544082800501c0c1710b0310303400501c050380c0110740c0008495200c10400070080c849000f8840c090380320a00040000c2d0300500b00940250000f0710b00b540902c014119800c81540740d810207000a04d0942d1094680c0c10410b0214544242a400c412074000461802c25024000603c1c00b0b0100d062 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598545044 1250 598543794 598543807
    0x6060a2003190503180c0d0b1b160b2805060f060d1d070f0b0f0f0d2705030a200712020306070305252f070807030f08 52
    0x30100125144650a1100003542081000014115410450307688030a42c03017045c80c2203401c030800305042d48141300090036810040303103585601e000010001c2c5030303030700500ea01c000d00080d10f00c503507003d0114000031034420b0100070100d140a10f20b08001078642c42e95000030903041e9001100554441907190301d1650001380c0b1303a582c8000610100310584041d6000344000420035990300503600510b0b000300d07040c80c04441c207440048100d5610041032040008200500d5414040000d207203008083c942a00c04403181030201600c1407921030340c001148420919a03c181c030410040e200c503145820480c90b2102c0c041e022101e9110f07182c5a1080001e00d40030000d2401c0c228014400c484807102c8034002c17980480305036030340342c443e08400080c0d0398409a1283c4910000100307414802d006881c8201030b0b1001403018a807004443c8440288500351034014040c1030001341c0f40c4d10501c1c0801a13807002c09446c9035a080c4191207056400e02d245504181d200f13401200042c0301040110703081d900708a61140c440350362140c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598546294 1250 598545044 598545107
    0x6030c210b0408090d05010f0c0e0a03030f050c030c030d06062607031e020304031b111302070b0f10060c030e1905030609030c0c041a040e0309030106120b06060a 71
    0x4100d0081a900c4080d00e445c0e5030500805510030000c0d40c200600400041810000c243da4842c4030400d0300d64400044001400001d200350561001c80c0d040d801c0107070130801006030b03044c1180c210800d041c840b68004152200720500f24001c0c000140342c2030074096040c2089000b0800500310b90600070b1001c02141010481e028840d9010a00c010807240c00039102c00001c1818501a51083d00e00307500048000082903e45042108081d007115400702810412500802c240b000148941009201c0c01d5824004100881c80004070b076482030007960042c2a05181c4580c1d40105c0c3c02080e0080000c00c69000003030b01c00030340c010142d04545070088424282c0d2040300041c0020001d102d40103150540140701c00e212040340008041c00241595405481303000d07001200340400c036822000000c2140c01c059220101a003403640c40340c035801050310192450b180e4683c01181c29916160301820180280c202e055050180190166420a0089070351524010701120001c149100218044100d00b002c1c20317207510500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598547544 1250 598546294 598546297
    0x3061e030f030c15010609050d0f060f061d010f0b180a030c0b030a180f06050907030501110405120105070507031103070c09020903060604090830010906030c210b0408 73
    0x41c0c80800b16aa1003d007111903d8990450540200d040c0303000303a0001c200d580c001d044400070780d0f00c060300945070040f00d5101c20780ea02034001c0e01030301c0c000e41d03d14030f40c1d218910034050072014121058203000ca1a9014110304100d6005030f02c421039444180da02840004804030845914040101c0811043c5021a00240c910f841c6036100800034200e0b0080000c610441e103010318411120b46200b0828260040d400318116241100028030400b400000103000503803070b0303200980050885c0210741031140c89503611401c5856008800300311090109080080d45450043c10b26003201e9440280002c3c109a03501402e103000300302d00202400712105201b0f40001042044e030348015040f40f50030900302d0391452540020b50000300c0d0309020b400b030503000803400d08040c02890180c540c48002c0382c0ca4000301d008040048014040c2c0803401c0c51a44e03040440e4903009400c0c480c041c1480304c1000900750b02c0e502c3d0200310048a540140d00c1d521b103085034800c040c0084003c0d80209900b0089040803540c0e01d1a048403103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598548794 1250 598547544 598547563
    0xe060a0b030c060301150f020718020a170c18011b0f1406271f0509010e0303160f020607050d09030e0603041401060506090a0513020f0708030a1103061e03 68
    0x42507004c400041c041107042c2e01c01007541d8054031004030480c15600120f032184002d00901c0d40c0070301d00369268405000240e0050131000d010b07203458080250804280c004e0040242c540c0c0c69104004207a211044e039407a4410030300f0b0030090904044180c0140d141500305c1c4820b503400303003c0c8402d03e02c20130706000c0200c2e122065445208203540203450b02c0c0c948d80c04000c0c052450130309001244002401c0b22640080d103040709030750b551076002c1039841c81e40102d0090400100540e605540326000c2070b501c0c9100700080c42c01206c00c10075009100070421401411600d41460200440d8407240c2408940e0390000200e821300c1c02d082c0300105940c0110704043d02c8c01c5d50302141c25074228100008201c28003050281220610204400074418903996100b0800380b4001d552449a1003891000100050316048100c001c42464a6101504125181c0060710703146d0420042520f2030140081040124149481070388d9a0200c0000141d00f541442404603c03503113210401d000c000101044a11000e40c1c003040390441 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598550044 1250 598548794 598548799
    0x306050a1502191b090905060a0906061d2202010512040503040f060807080c0a0905060702030703051905060c03010608061c0512041a07110616171c0e060a0b030c 71
    0x14040854541149241340307401c500900100c0444c40070070342d040c950080c4404590840f00900403511202c001d03c00809100c0c1c400c841082d0756200004104030f42501c1642c810500b21910003207031801c08011441c011a00400c64001d8030b450a0080050380c0000c19102009503201d17020469595a1400c2d0786144a1600701000a401c01200095410380c048401440b85029031707100d400d180c5405415207131500981960701301182c0020001c2c172940c201140542481800201281d88059881e1103403130612401602c1e0302c0d02c00c000c01c00c0c00300c103015040013003541003405029001d2556240c280004d2940c42c0142c41c80e8400c40700c1426106540c606c0030010740000e9000000e6901240000c8014605d035885032103406859181b181341c502148652801703485520750000c0d10500d2280400c004c00c20b0710380c4086140d5503c280b44d40181e2000c592011070480605a21156490340c415406070741001c11100440030600071403c004042503041c40204103660080f207000c1c0c000c1070038400e510000b8109510003040c0c98 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598551294 1250 598550044 598550083
    0xa030908040321030606092d0902091c030e04090f0b07050a17010510050c100c03020a03141b0c0c03010906021809070c03121805070e070306050a1502 66
    0x240700768482e0440c01500c030f48820400122000c1c0d415000e4034540e20481b4042803200b141000721902000000140460840900b603c25000980d4100c07095425040810b0071540856041d4044c100031800400820342841015402500e603070f0001e10804581010b64080d03500d600711f60007084124611003070040d5020345050032038580001c0c0105075801040000b40040c15505042c0140440080c005050320b00203080700440b0098810162500c0d807000ea1001494071030104907114880d0b0511408500d0011a6000360b41d230b1030300c140d00405554142c1494440344001d0014040b403502c40b40f4082c180940d12080b0355890700104010301d4203140024242941550030298640100a030355030050600b41e28200d104400501040280b240c07809081740e802020a191101c440c01181c0600c0b07560344200900f0001149800303d100c5602c09041c541030f03040302c140c0c0c010709041c486c815100652036404040782c501000800d01d080000340d01c0d40e102c1c1c0f01e00250360088a0464140c1b900c00d1007035581d0544e6404040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598552544 1250 598551294 598551299
    0x211e0e0c03070632071a04061506140c030c070305030409051b18040f32010303080414011e0c0206010512030d050c0d090f05010606030c0504030308060a0e0a0b090a0207020d03050a03090804 83
    0x7070206c1d00105c504541e200e2078034070003a415946054035042525081d645078011004012200c1005502220519549110078008103080300700410203071000e14401c01c06152224505250b0806846020300042ca20090044058002c0c800000a460a45580f400c00303003046a0b8000100e0000d10105452200d02801d10f00c0322011081c1c8440842d001c2c02a40822000c049110211a88203400a010041c006046070f030100d00428841440421441d410314000115105003420751540541900041685280c6410f611802c058043c0a000c0c01804d0a442c03684031705020490654407882421205040c1d6a555404103c1ca141c841023034a0b0102000b060800050015041218450001c1c54045034258200903020942c5403085c0a900c00390000e50b2622410142950307010754401c1da00034009500680081400261501a00700141c001d0380000e20024840c941d100c02e1001c1082c0042207184d0907030041240d41e00584038114610a26a090302d0b00742d03115101404200e0140c94050307009800d018020401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598553794 1250 598552544 598552583
    0xd090606060e130b010804080f0c0703030f1701080606040e1c03150f030213050a020d0519230708070c050304081507211e0e0c0307063207 61
    0xb02e480c1012030312030040d424581550026100c500741518005000c0c0008500011f00b4800948030f4a40b480000c0c5007080c0e0700d403680e10b140140c2e542c4103400140d0701001c40f00b10581c1090045c40a080c402d40d4104480d13052590385507403060054011400f49545102564801c1001d101c50b070302280006c0030311201804603142c0100641441000c541d20030920309070000e40480511600c40c104c0e540640304c0e040706140c10410702d008000040c00c3d02500740d020412030001c0c000e03522820384a046510070100030040003541600c21a0500d2050b118499050440d405810340c06850786644001685410946956881400c0300c604120b910010440e00c004070700828044404600c010401003144621300d0341e0755612108a94010359881001305421080b600410300241540000d400710702d031000b40018040c4440c805074100c680c0001c2242c03c03600304c818540810b140a00a14008051031f00e000b526010781d50942c041c2c50850010001030201c2c4000b8948550b080300304c241c07510740d90409905160300820040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598555044 1250 598553794 598553807
    0x3030c0a120207082b020d0806010c0804050402070b0103140a03021506030c0a0603061d13020f0411070602030402090901050c03010e1003150b0102100c0203040b0906070b010f090f0b10050d09060606 87
    0x8061022415086005c1101132000403004905001036968150b607803034550041d0382d50400c41e0010340314200c007008089419291400240078003817103500115915891410310402890320410004003981050340000c001c640e000a44100c1042c1d54940602e0580381c0c500082e00e41034440c400d0580040400400185440d0181d1000341214645201664920f0100300808581d181c21100070440005421000001d8200b00c4002c11451030094000107100c400240c01d800a038002100440c0c1864001080008600f010504582c2043c10308000f032040e428070504a800900050182440501455000403410703000c00452400460300002411054a03080124102a104020a0a0140c8155840340c80f1010451060b0184070401d075001c0c6052604112441595521908240f640100c0501140d00400c40d1058014020606189641c21840c42c004246003370710f2040b00340205a42c03410801141c103071901a010a00389005203012591303010140c4c403800042040e008058070042ca0f000e03000c41c03000d40100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598556294 1250 598555044 598555093
    0x609140a080a050f0709061a031b041214070b0306120a02090a23060306010605090105040b0c0a031404150f0c1b050a0b03100504020a270f0503030c0a12020708 70
    0x102960b103170b0f544034006001134a00611807081d4803200152417403610400b8038040d64000051328908103036554030702c0700b010017a081034002c071284d1164440072004200040d610700d00302010301005440e50a01c0e00d5400340b110b0000420b05401042805580c010424092003003002d50741d40100b00d0001401c00c001035400502500785807000240042000d017500040e0304001910611000b40103003403a80c208401101c0c0340d000050785505008080c08046682e5001801901d902c802680c02000c4860306400c1c01411440b004200301440e60042209201401d85440d10b4003c0700001d0401501c6042d41c410101d0702d1034100d580181218400e440c180d85c4100703614902e4002c0356001c41310210300d80d4031114154502e1009a40203169000302440c204030300d0409802400341a80542001412800d1400320100c1c5100300c0041506810041001072142910300607024028090a0f401941019000081c07980c1e612003100002e8403d0341c200801103007242c401c12441018090b524142c800b1124030426190b4a030300c050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598557544 1250 598556294 598556323
    0x20715060906170a052802150d0c09080a0b070521060f10090302210303090c04051302100e040b040606020609100513080a0c17071205040609140a080a05 67
    0x12410503607000380000b10b1404c1e45401001030003104403130101c6d5066007444050b082e10150203050031040982d4032042d91402011782107010781d03a9584881c880108440b694844003061240c100700034448101e0000307800080700d0340b102840d5001e884e07450b010340d8a805a51324050392818240d010501c40d0940c02c1202e4080c0d00c065802181859445040140c080c00603001440001e6a010303041015241c6091104005e51081108511590200c0e0056045502c1201c14246a902c407800100007420300e4450b09a0002d05c4543c1ca030031140356640000d1086030341007a03000c1000040041c40002c1d50b180d82c01f40d4072040c00100200205943c2c1c8001030749501e4121a110802d005e2001801010980c6024203031050500d5402644441d0305542c64100c0c4d80c2055411008100350020500d0009a01c0702d08a9142902d03480003a441d034216140915150083c240c00d00b0400000780020461950840803000c00c1d50041c0e49d141054440c0d05d80820711601107948103040b20700ca007140b200140b040100796144001d891 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598558794 1250 598557544 598557569
    0x150a020a08060307290702030616110d0c06020c0c0a1e0b090d03140d0c0804120c050705130b04020d060e0c040f090e030921070f0e010603020715060906 67
    0xd4800301131301d60381c00f40b08034a2607078140149511003202c03240340318140c40e032990695810030b082d90700403d1405e4002c48814101084080058507402c0d0030100483c0c109400c02d00804000e00882d0004000800c5240300a11242d00031500a14020050040c09040303440036145441e4655a00701059074070100e40014007075440001404107005108030115070806802030005082404640c5e001c031640c1380f4020b026881d1301028000780e150f00f141c5005840400c1c2590743c5140d05820b040c2003080c1610102255081404001e9511400203600070511104507281240c030001122003e5030b040d13010f4000041d4280d0b0084c8001440c0000c501560720000c21f540c0c0b44408000305a445540c20f000c2d034441c600440700307a00805c96003008035031100d4109130394003954001981c2c01d1a8074180030410910400201f10b450032003c2c00360207451390f41004810700134040b030a1301c0070134289402591b1000c40018000ea4013010f030001280420320500a62039418041041d2080054039a5005040018915405200701c7d4454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598560044 1250 598558794 598558801
    0xa11131d1f090206161e0b1005060306010207090c0e1908010b120309040b120f0d0e010302120402060a03090b0c0304030207060302090609040f0605060a120b030a1208040302150a020a08 81
    0x8512600301c070660b02405091174084144907409452582003401c5504000c0d80c400f80c001c00400301d2100440c10300c07819400c50349042c421b08652a41d003494003e94000c1a081c0300b0005e040ea400213003c0e00300c80a411000540e0192a502140e01c0600f0741c01050300a140c0c441044455821407400130110382c00d01c0b000300054a800020001d800d005074204880a03070081c00000f16a10341540041640d060003890f0003560100c440405050141161017540540c2040b10084445a001507150042d2a001d190440c5844141c1003001805000a0400783c00b512010900170900c1d40030740d0003282c010f900003580301c42d00e00e0014a032503180d600c112400c0300180204d08001031814000d0003600d88103c4000e0483e4140840301c0309210003005600c5401d4078944d00c0d04400105070b1507420040c003064509544010540e0640d540b21025583c00060444c040c0d80400f003500046420140c414080c841c1c00d28003810300f505d8038141203162400c1d41604c898800d40c0d50301880407a4550b5801890380c00c2543d02c400f0010f55 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598561151 1107 598560044 598560103
    0x103060c050d0c1710050d030305040602210106230d05091c02070e09070e060d03020a1e0605160807200303010f05120a11131d 56
    0x5800040350f02c00001400140e90740b180c45d185101501070300c5c05021519200380d5000142c2010fa840c1d020400b04800f40d011900d5540003500c000f0380d5024002c000680030003080c0700340da000c680b00d0104580c0e4009000000d44920700e40d80c0c03840342040c1000ca603103c00340030000c200c85c0c000e014011205010341020000880c012105900600c0700310706005014034207410291101c50607070300402d000c00c240201c06042907030019054480381180003951400360319220a10341d00030700380c5064500c0781c001c94024400301d08180e4014181405217840b1542041c802c035080107111800900c1030000520701c540105007222414041c40c0383c0d04600b091419049085800a070010b01402054140801261802400b60090301d55024080c21411855a172042143c1e403089100741c0c0035080f00145001100c44960214412404010a40d1300030326507441c6040c0c5605585001e02c00c01a541c0c0d008400d81d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 598381294 598561151 := by
  have h0 := BRFrame.cov_init 598381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 598381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 598381294 ≤ n) (h2 : n < 598561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
