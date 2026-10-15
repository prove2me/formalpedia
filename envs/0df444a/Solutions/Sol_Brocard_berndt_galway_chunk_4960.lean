-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4960
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:17:33.043644+00:00
-- url     : https://prove2.me/submissions/5934c6fc-1f1f-405f-ba42-d14ff2d18e75

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891906474 ≤ n < 892086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891907724 1250 891906474 891906503
    0x1404020402030601020f0d03090c080604170a02030d020a0c1505010b0405040b030f0a0302070617090c100c02030a111009030512131a03100b070309091a0904150501060c 74
    0x1031907001507034045010b0040320410a413001c482171070a012989450002070fa01d0295004024030740d40c07030030014400070004101504060302e0b5041544801c5000c041c98143c002801682c00f4000d105031060341500d6641151200d5a034140680010700f5424100d42c101400c40000c440004c0710700c0b844e81640c128003001e0381400d0820052000600c00c0710071181d8103110b0481d1040000340c003003110140c054070070f0b030103801c25519001c07014080001200c590300301000305504100c0d217035400185c040b2003a0401c851203501d01c840d04400743c07a41451620080d4040c00f540e403000c1c050010130301014400c4c00c02a903400c00f060400c034074219403d0a05000080540c0c1140041040103207100003c1d24104074100180382c80c50b40d441851045a1300080110b5040c2d0002000300107c15640201d6a0004d11844000d0307464500385540040c20a0000d0081d42040c5030b80708414495454240d052483c204d50142502095003028105201180701000c0000c0f04c0506000c000f065161040e80c1d64508290b00c541d2400ca0149c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891908974 1250 891907724 891907729
    0x5010309170d0e0304031101030b0a1d0408191806090612020d18050c01030609050c030414010b03100f0f15030605070c0f0807030807020712060b0f0a030503030901060603140402 78
    0x14400d10381d01d80b4942d100c03a51a09945018801840110310600f04009850302d1040050261141d81034007038418240600704012009441000f00010404c1c005080d5440e510f1340360440c113501a1356440842c1110342d032421544c668000e01c81e4084501c041142e00c01aa0b80c07117008684004550260038006440220f245000300102d40142040c801c0800e030104000642910340c5d01040e075000c5003501c803507102d000c218100356051310550029140d004d0003800646403c2c50114801d201c003410013032034950341c0c01d00006200000e512840010b4002821783d51440e0003030880f2006000b0746094560f19034075000c00302ca001300031482814101086000f0751042a40b840c1c95440043c00010101000d0002d841100720016240084064032188120b40003500c0740030604000340060002000401554801003050000c2e01c3c18582080407a6071005011440e0390020300400d554190305103189411004e280004401c0160210203117206085400007040020b0341c841c401c03001d50300409003000220341e950300840c0160 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891910224 1250 891908974 891908977
    0x127120c03020418060506060307050a0e01020a14031b07120f05070509010e010312080103051b030a0b070203360108090c0a030c1404020309030315010c15150501030917 74
    0x103405041248481541ea4003c642581e9103100d20782e481c0480c0c2c124500401c402032083c4c0341c1041080c1d80e4a801c1d071800c003601500d80e00c078201310f290a200041011424036071080005100300c56211812000b1170000c80e0245540313410a41200700350903108540d4581c4d01d0030009200c0e080340c60422401da40720440ba10703841500c0c425403005031041e0150440100c1d05032240030046000f8031101d58500320359855070420310f031610780311001c120401a0f420010000f180002418001e101c041c0540c0f0103081d07a030704001074a44401c061008000510390b804210700c1c01c0c3c020018080d001c2105000769a8000d400742c1608994020b10821103242041c0c1082c1d00702544181d42c0071360700084c40000c60f00314800281c0060304200141e40204ca801c00441428072140107680352041409409690942c11800d00756a9140c407404000c108214508a00007020b0300c0d42e02c0b43c07074840380c515084480310042e01200300c1c445d8040c048022040440e684010800541548030340314034042c50b0f40100301945050404144500a07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891911474 1250 891910224 891910259
    0x12090a030b190e030912011b1103041a070203060603060405030d09330f02070803061c02060309010203010801110a27050a090b04050c09090a1e02030103110127 70
    0x7081c410485101e4841014070688803c04094002107840d42c25803002c1000300d400800161841d81d0510580302c003008643d1610380780364015414440d12214490340010315502469201040c10b6030340000039005c80a011004000403402507080c1d60107656090140742e82c031401600c0c0100550300400013170122000591080c20218072802c010074002611810325030400c008000d600f8401c00075244001c46848491080305450b0044040c1035040030641e894204443c000284840c3c000d503030306400c1d00c503c1021141c000302003d42c0101255101d0500141c0705000750000d005001856180c080352018102002082d84d08040855640c2d5840c0c440702d040c5060100d1201c0010040d500d002d51001c94641e407240c4684000d003850b0800000c1d0021044c0800050301c1014068024001d020030500486441d80394425600c4040c9c000d010031090302946885400c0240020b16950b43c42c0f011001008224815100c0306c28113801741da80e41045111380302946a0848140440c050b440003104003040f81d442c524190303108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891912724 1250 891911474 891911491
    0x3090d0f0206160312051f060c1a010e100b03060d080703092606100501200a0b0f07080f060604090e0f010222060c05150402120706080912090a030b 65
    0x104840140600d0943c1c24003c070407404101e0000c2140080411449540d500007a01690744200046000d6449840c1900d8040e00003045440c2d0120f1042c4003805040c1d614012a04003228403e6940f1b19805c00c0c043d00a9480540c03030001c48a0000c1d43d0716024060300d0080500600800c0391091941d690105075014001c00c40c24000b002100003035051000082d07000344034401c45480c042050380749640d410003600410303045804984083c24041a60b206064100004801c1504084181c005201d40c0c58803003080d9004041c404208200032884014400030b034090325041d141c2d0040f544514080705443c4100301d4125811a00034001000210126000b142c000440c0704141c81c0c8001041d100d4909a030f2010341e08016480458041d004041c82c0e2100d2175004080d62300d0601e41e0703101c00359101078460282c20040e4a541e040705003c1415075a8040036001118405811156490307620a8040d1a080003100c0192050040701e0556a4900d00e080444130501002848060b1075401c0d43d0790000e900402038030a86 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891913974 1250 891912724 891912727
    0x9020117041104090b06040e0f06010501030914030a0203041805040b04020907030608010f060608010e070c2402120708010b070b01030b040609020915100c050c010806040e0d0e0f0303090d0f0206 85
    0x6489504c25105850701904d1142a40c0c40c01d4814003058441ea0191a01550300004201d4048074020543d141551800d01e800b0610b00b401e0b0803d11050b4841c031411440070300000541407607498000005100302c901b05019903002c0c180c0c9100380c2d01200c40480303001c0c00381203800c0e001034010715002603001c0c0c0c0000c480c100040d101d40c0340c2e00d81d2401c59810701c0d9410308a03540c07600d00380b00303003900503178054010038500044072201c2c94400c20003000d0002c0385e00d009100318030240e2400c080210414000046c1c04080c0021511303030281581c40035040f802a9035141c00704035140001b01c3c0350070a44044901780e42d00148081c1c1907034655950390720448401441a2500c0d0f9031081c04600581d9020f01d10342c0520303c041c0c1640e183e03013020020030000c002400381171000d011244140707800180b404210040b603038100342401c4103e07982d0b00020038041d141c2c02c03011840134040c022500c10525041400e10101b48000c1e100720b003900702c1c40e2081c1a500d01c02d06600a6000c058040018000703000381d0814500144040d2096 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891915224 1250 891913974 891914003
    0x316020307081203010504050a050415020304020a051807180807030212011104030506012111091302031f0b041a060d0e0a1110020723030708030307020319030902011704 74
    0x260305108003151410043d000000c01007081c2d25050048030782180ca44a41001181010780e10001c554a031100840302003a0003100003030655481d0750046c4010f0001518000c00b281400c0c0d030503409603100301c859601059403458012081130f6a10004400d81300c3d21001071140900715020040c1040c3e40c03a100303030481e64842e01440c84400310040a480118030070320003842194144114001100b0524841c030740314031405516240400c40840c41d080d000c3d407060b150805207454621601100c000c4070360740039400d0310030700240d03004a54030004014201d060b02403040043da840c030410130040d18060300e28224101c0b00c0541da6005450884024000c40f96400000508160940c2d01607003040c007268025100c00250a59001040c20324900b46000c1110620160850a04201c122105201081d0500d040d100000c001c1c120140c500308951000b9001031703000c6907100c0c039003803000035034a500022001440e802000c01d00307510070b07002e0701601000701d5058451900b600030208042e0007080c00104151000848561036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891916474 1250 891915224 891915239
    0x5091509070b250302010207021005120406020703020c0d030e01030b0d081819150e010e030a1416080714180109020d090b040303140916090207020d1202060901060b0c0316020307 78
    0x46a100740d04c66000561140c10318010028040719060b101c80a20404201c01e80d00091004840d0b5445070380200d0041e01c3d4000d5050403460101c18034007045c0c001d14110200018160000204001403000f40c0e024840d0301c014405010340e1b414004401001c2034014410012000500c500c40200a58090700c021800074107503600041c4411554400d000000340140200c0000d54060007030aa003c4081c06c01d004045007401c0803d80d2000042c601600362044c500c0d03014010a0107210710300200131500411000c2d00d48035070503541c60310041e100301100020380c0e840801281c01d01300e011507a40503049101a88683c03078410301d60080e5100344105e04216541d030a540c00050030400c103007409140a540e00240d0350241c84180621802c0182c105000d40d40900c101e098165900b5041d80c05076040d184015032103954902c0480d4080a001c48000e2811001104605074540c4c00600240f1400c00f40e0001d000c0c50741d075007450711908c0c42082c401c0201a0403c1121003800c0b600380f441981e066201500b10f0b900940d50340750 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891917724 1250 891916474 891916537
    0xf0317181018060e0d020f191707170d0305091c080f180a02011d04140f0c09150c0709050a1d0105060901030f17070605091509070b 58
    0x7042010801a000091403025401c0b0a10064441414062440d510a800040180001c01c100038070400d02d0070301d0003246071901d8000000354030b140e00310306081e02c0e152420305090708140d500c45980d601c141c0c0400110101d1481140e200038000e8000341440512800088021f010020200029441071b8408000e028004001181514843e90348442007420050841e25042e6405007502004035090068500303a40c0002c20464410360782403e201000c0c91200762050f642113a95a912603100740740c8142c2ea140d560710071403954400c07a04582050182d03629030340c2000b540d024804819070006003d0044001a00c40c0384003c000c2405404104c0381c000356207912400a5900482e103034001c2039190240046040d08261090a40c0030142e00240003c2c80e01c0030106824020511000c1c0030000b842040c1401d110b20407101c40e195810b0300c0c0440740d65149504007480070344030030307108401d0b81d10451300c100c104041001d5115000740d0004024180b100e10707151030000c04c0c1e0484000080548011000e40761080307000503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891918974 1250 891917724 891917749
    0x42d0207080f22030804091a031b090c04030b0f040f0b0114030d02030f030604050711010905060708010512061b2b1b08160e030102030a0b0a0f031718 66
    0x42c6115030f0703030207007614039050081e110f59580d114114040c0c2c18000200703c54252002d031103501c20002006140d101a2486201003104c81030f4040c022a110140c00c1d0341d01401c00d0030019020341e8002440c0d03c43e040350312150300c900d11014105050b09000300741031044041820760424003030b5001d000d82c2e00540e100c01031446001e03880700d41141c5090102145a08081c410702004112900166003010b048040c0e0354024440100024400ea80e0303400000c1d842401200000060300c1c10300003c004440f151b1520f1550781d0f1041c1e030400049a5070000000d00c500e8080f850040e115031110207000d444e110008000c09220110f03c0d440b07a13943d8144102c002d04080c90941d240c0c121040c04900014441d0400300c64201d441100c2001c0c800b1800581341e24810743c001d20001d4100007800d0581100ca200740404444400000c0200d540c994000403d0006024403500724141c110400c9a90750346996a6200c00d042c000d640340301c0103000045500500c0d40c0500b010010300908040c20072030a484050250005d0015080803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891920224 1250 891918974 891918997
    0x10b090d0629010f05070804051002070b030c040e0c040501050d0c030b030307210302030603060c031b0f031f0f09051909080309010b0d0201211b0914042d020708 71
    0x100704141c21980d000340d581c1d444d10b103070342882881c15080c0e03210043e10384118010640503c0d200382500e9107451017041031400820804060343c0d10307410303c0b1007040c905602920075032810100850102c3c5002590104031421164140c4034a4540320303200700b280002d851030031801001d0540e0354000c0790345910140b00070b040c418442c45805440003101c0c49540c2d149503070340f00303240c00b01481401040510b407000250f0fa900114480c480940b80e981d1003900b00d4040e880c40108081600c0c0204006061a80803000755004502100404d03405c0040c4501501c11031401d440f450140c240020010070040302907610241e0424000d44070030300640200d881741004c3d910242c80403681440c0000030800740074400e12071040110000c460000c050007a5400080c903a0440c240c1c0c0004100c166500c10340c541c04680d010040028265a81c41108024400080c1c4000c00502c1024001101c2064801ea01c3ca0b062051078200301c101c000798102ca014102852652020049071088a26030030014000800d4600c0c000e041c080c00c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891921474 1250 891920224 891920291
    0x10909021c23180c0a030308041a070e1018080304030c0f060207170a02031f0c0302030c070615030606090207231209031501090501060f020303010b090d06 68
    0x310751031201110007078070040120080103070311a16240c11400701c59030040454110240d007400d0aa100c9401e0200d8000c3c126803001c04441d0000400d50043d822034070403406060702e144400005010100325030421141d044c002009420000180e1400c05511003414400307107480c08281c01c14071242190318105404c805000e0303001007030070001c00c000900301350b0182c114007106810b102e14054010390750f448180034294001e102c1401c0050310400c02c008049440d60010304590b45403110044540461a084000055550074070440c02803040c0031303008880c05040d0445449281c410b00e034a4050040c0010481d20101e1210052b0000102d5040c1c0150400b42c04441801603a900403464121401804004010382c10003045041024443d008100d0b03080e8208540d2602c3e985205240000c0e04041c100d00c40c851924260788008110351407564801810303131b6440e0710740348515000c103d002c0c0e940380800d00c034500070042c0c100322254003820000446020580720f080007060480300740c02c4402c04620200c40f003000e003002c4c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891922724 1250 891921474 891921517
    0x1d0109080306040b19050603130f0f0501240b0c070806242b1b06020c0f030f0604120302190512060103061206230403050408070f050907080601090902 66
    0x1044d100f003207a001030440346900c11078400c04925000300000c0c459184150404000500182c80c4040703408003150380074a48604244c540d1401072081c2403180c5096803198600310000c104e01106003d2525000c2d10340048880d06841c20722110544ea02c0100400c031a2701658400050540c410003103a8080c001d021496900d1ba0f110000d004110b100501a80b0b00c148402c0040c0b5440c00700c0040c1c085103102150401c0381c08800103041c55500c0b80400c00209042c171820403000200245d010800031114a400c5400c8034550150b50f0826554a14181490134a03410400c0890000340d80d07120949003000303403030802600340000001c2440545030724103001008140d0020b214900c100005c10003a90040090030100709650800100d180c850622030801000c160b592040c1130307890ba501d4000d030100503c00708041d1245261a18006002c0d0f00184034003020340c410014041414000620b4800644001420f0784145c1e94503543c04850140014101340c1c10b101000c180490310305210b00041c030b400700b82d401c4038145140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891923974 1250 891922724 891922729
    0x7031115131404270f0210030b0f0307080c01120f0504030c0b0a050f010b130509041b0905041101052101060816030e031e0d02070b010f14030a03031d0109080306 71
    0x1402d10345502c10f902e018403090440d145191100c4400c06281c901d010748001618010010214541003c0c0d070100549401d01c50b40d650580013000100e5007540c8070f4100d61110801d065950340349015a00c203640214210203850b51103041e541400c80703100700000c40c0c1038921428640440d8001c0e501500060480c0c8250030a200c4031100540c0c02c050b40e4030741040186000c103500c000c910b40c1070050780f030301d0080055445082152000c0b25009404002c140602d181080c1c81c15540c85202d101c4040c1c1c41038001500012510018841e0383d2050350070048000e1850044401102c43d54014940e540300d0046e07100d643c091050240c445c5c10301070800c3d0f4940301300c01c0c2012241d40b8101c018a03405030b0105030425030713584401200401581d00210300010410400742400400c410319014240f01034500711300c00f0900c5028804801216412038112a0380d0000040d100c8104d6025013150489803a09a8851440300d80040e10170b5100c0c9040702c5a4981540c1c5d09000e100341d8a003580d598000030b0721042000b0080c0000383c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891925224 1250 891923974 891923999
    0x2040306110a0c0b06042309010e0f03251e050606120c0d0812090d09060c0812041103010e06010320010c140c042d0501080703111513 59
    0x291041a141c504000403598001c000b2807420a005094511110204050383c40c1c0e504408800d100262410f01c8a405039200126000300440380c8a4156007040c8003800145804140c0414888414000d036250404e409008801c035520701c1e00a400c4020400c0400001c10140d42e01d8045425200c482248102d4560810fa0700c2d211015101c5c1e8807440c4102901c8064001c00148070001450035103640f81c50000a080002aa010300000011121840000c00c141071001040441f0380b2804e944490000549400c1e0495100114250050a0800802c0444d071202c88410303460354007030b1040c0424a80c2d940d280c40424252071007003000d5140d59200703e00500070480a0100514102641c1203041001110000000c1240c9114200600102044840b41019050502030407201d01c0c0040e005004810030416000c3d001c6620080c183d64a017070307800d0805c0441c283c03130040c0d5048502c620010300c086811916250403400446400c7e0750b2200007a46403091010900d405803840b000361034020203042d45001c0340144d05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891926474 1250 891925224 891925241
    0x209010905100e040f0902041104030302070b1213050c03100b09090d0f0c030e0312030115020705030c01030f02070c0902030105010f022406031f0227091308120a02040306 75
    0x1501840e40e82c1da41880d8000d00206001c80d0486001c035000c83c040014a000f0080d13603c01a4205040c400d25420a502002c0284200d81c480d9089400e015541d0402c4041400b942c07080030b0321281c0034800300e4a0300f400d921520040600801c140e413040000e45000030328203107030256030203859501c03140d401d6030900d4403000f00d82d8010941000b510f841c2c03e500c5002484950b40c009040207001ca40f4900c0f1060510401c18500e5a8001900f201c8101c00704000c602c929030403d02c590000c000c01b9005100c260352001c20910200c0d20050010420121610f0055000d0b0021203072040c40e02d68240502c00c041032071090707008018554080c2c0185d0780d5040000040c00801d0080000d01507501c00448440350803c200c503121100c003801060150309494003c0024105100d084007203078402070301c07080d0140c0516a50700408440d00746046001200b0141001c4041c8005146640340d400f0070010002507581280e0304814001511170b007411407031f042d0b4041070041c2d0030806072100042582e0110f01070040080e03a114161a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891927724 1250 891926474 891926479
    0x606040b03030c0c21071206050a0e0d0f050d1d070b070c14010306091a090115120507050906190801170a060b0312071113020c0d0c05100c030209010905 67
    0x30300340b641034036a5591050b041d0300ca03008207410485c040c4840b0300000d040d00c1c0d40d61030409a865603640e9041002c0d00c54281142a02da0502e0b04010036840406441340c1d111464003c000f8101080a284082e40c500c840101850180031003040422803d0b40c1610405c00026801c0001c2006001da10605500d804540d4000021901082003a4000b24601801150484208881da80b40800d2100d0048025040d40d40c00441c2c4281041803035401081c50030103491001206030788500e066a6580f64090510030300901001c04980c1c2d02c0307444511500c0c00d41115034443d180d402c1c01490702c034801000c12502d61000180206d02e07441a010600b249501503586030042000c440c101445c00301e402d0b2004d4496404030f20081009d036580d402c007815034406100c190900185003810b152106041d0070844a08030030807100c9031045040c54201d00d00c070762071442940d00481442006003540040303000c05413040c1580001c00e440510540800142c4031010380955030840d070250340c001d40c480114000140441c0b0320f0707421039407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891928974 1250 891927724 891927727
    0x3320a14070e0603032d070b09010c0e0d06020306030f03040f060320040b03070e120c031e0a0b04150903030b1c050c060d0608070e0103021801030f020d05031b0606040b0303 76
    0x8181c2d540003090352038246d8000341a41c0c401103d9070306002d0007051602407110f46100495010180225941000d03c81c1c28050024460390320911405c4480c1800c1c0c02240c1d0b07015800e003050070b010590a60265a00510281c00c03103100700200409646940c0081d48044820301a401090154039418090080d04405ca0701c15003001c1011400041040e02890103030310760b2050040b0000e1210f61040005981e09000504111080c40c080f800d240d45031001503101502038171410b040e031301207901000710001000510802600c4a03a0055454001d04000900155400c0d6040c650b8008241110321840c0d4a180c070070b440c0002c480c00c51300d052001f259078002e010303e0703e40f403100244004143c01094806000320b00700d501c140c0c0d4200c0089003100911094210820b944202040821000d01e0603009a0682c0d00032aa42c810302c07030804207d00c8100d102404018880c02c580c600d4080141483c198115260784520280c80c10240324580194031310308110740b1420154088010b12100c0c1c1860310860745414020b60145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891930224 1250 891928974 891928981
    0x1020f12070b0a021c0204050301060816090b01050d02130f0b03040b0106050a090b0c030a020601120503040303030207141005060f030f15040203120706090201030f0603320a14070e 79
    0x30303841c025808040d001100800004a0018266040fa400d00d1024880c4161079542c001d000d20081d0054010310380070b0742c41d150011941100c00140380c0c5089441020981000703080002c0d01025104081d07019040c0981400344c9001d000c29400501043c0100e80420b440d207910b4050003444071005540f1505440038104103010215842030f0b6154152580c40c20420360301d02c117010b81141c10022a901c10000702c180810100303200c11012004040e61299039084501c181d1700c1d55074155442c0281d18000b841c5500410040000074085e401910740903020720540c1c80c200d0303140d02d072150030141440303440030b08140d44004018a9140010045801040550041880c00701090020303645500b4014805000c0803004002001c559007000181001521540313071a4480805140c91030142004040490100382003906040800c407051140c2c1d000c0f2a08000030400c15021074420000712005240d00e012005011140900f1ba07540030401c3d2041c05201c1c10781c1c1c40713102c0c0c0440c52441c204001600304551032240300007070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891931474 1250 891930224 891930253
    0x405060f0f040b0702210d110301060c260c03030405060c1303031d0607150c021204060c2a090e160b13150c06140601050d201801020f 59
    0x16512550043c40710305581c6440030164038040d500c03114a0001d42d0407210000707001005801502d0828003005080c80807140100c50009540002d0065030002030b0444410703808240c0c036030501f010301c402c0807002d9000020020b92000965115030000e00c00356000001f40300405c5401c010702580400701011150a203080b281c040c25100d10035101c0030b410850804c40141c59503503030280103900d4060091150b5a10030362440c090508008202285078441d00c3e02182a908500105440c9488583d2802543c54282006415210400f130700034180c0c1e5904600c034000701000c402092411011410440341c0c3c0c03040349040001420342c2e06203e5104056044903000000e07490540c040b0740c060700c1c110500c00d40c448481c0802004441055401000c50002d5401b810000c2c641025954040b2030080f03106001045e0441801d0945000680351030b070000d0020040008007070f00d03d600c20340b5040340941018500c207240c0200b819058020321119400c0940f0030100d03080540c0c040120340341c0200384501500c2c42450a100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891932724 1250 891931474 891931501
    0xd020909150f030c010806120f0f060906071e03240806010f090204143639090301062c1003050316030302040518061005130504180b07080405060f 64
    0x88500402c8ca03140601700c0110b0034072003c10407a48a000301c039400da0500160b5640c3c0e1006880c107940500800002c10f190340d2248180710590404040c0490148110500440c01440b0034800c0360782074110500c880c44900040b590507402003c4c0303040180202c0d4105501412000001d40c40210104e20400c401c1040445039046142c0010044810110300b81900c0e40440c01c0300703000c60031100b07861403003104501d81c0b102c640d00315401021800990311030501001018081d00d070307a005000b0300c4042040d880c0d500710040d04008141c040000740001c40e805903900b50031410300f03100e45c1343c0d949038201c60072090003100c00102081d40d110481c5c8100c05a01403850b1034041d103a10031821031203644010742800f00d060502035011a17004203005011a5011f1800025001c0c074940c0a440d036520420084500f40a850311075026039500040e9500740c0c60b001440c00d02000010100010f503540c0c0f40c0140c1980b4404280400386c2c2c1441001c040e00c61880d40d18040c80c00c0c900300800280808100b0880c0d01c14054040d84420 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891933974 1250 891932724 891932731
    0x3060403120b0301020723190c030c170312090712030504090b3309060a030b0f0301060501141315050a1404030f0f050703151e0504170d020909150f030c0108 69
    0x2d0840700f00311642c00d100d06144000d000300700c23420003141140040018280300002143e003d091200c03040c0f5125101c0950200c401e16501c040341e8410f0002036412003120344000e40181c10740c0100c1e00100d0341c401c00b8a02c04912104280c4c04650045408c00a0039440c0c0500300135910101d441c11060032160315103601694150380080d500d000301400040c0e00c0e4203a40125096104003c002c80d032542241c0c0001006031402c0f0007a2409032594501c44c0145040c140039800a490f416118481c42c500656074189158103c0c400c14010784541c1c0380e0015090241203c00c6e910440f8030303034072541d0316075034000007070009150745180314050300041004001040001c00044107069007c08102ca0701c1c1d156080c110320b05905500040c00c621000c0c4603941c242119a401060f0b020b980c101c080b00c0c001408002141110b2003228050f280201840e40b1181d03640e1300100030b0201d100413400060410304008045202000c04503442003c0040d901d0142c0c2042c64444101208054128000c211150070380340002d18452024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891935224 1250 891933974 891934013
    0xa140a0e16020f03090303190e03010603140d030902030c0607110402120f1b030105220e03040f0b0c0606042f09010809010b0f04110403060f1505270a090203060403120b03010207 78
    0x4844601c040b40b0410442750b2900b030040080c400c0d035440f41014628401000420740b2240b0803aa550314016010307000d1041083d400070b0142402c0300e002c20600520380e000c04d8003210191080002210150360b030344041c0c07210600e44200c0904501c0c000000c1c444110f006071100007080d0084202d4950301e00c0b03040840c1d0545006580406a904603000b8082d07000480301c40250f60b890a050b1404039000c0004050800c031602107806126060361580850198812003c00c610f598100100040340c600782504113500c10381e04000051111101104030f0004049080b0b184109104006003404031582c1c0602e119400c680040e008200100c40500007a880d40503c0d01000d02480d2a640160381d10074940091fa801141c002e4800d01029240c00d44110040505441c200741034247c594020030a820001031240b0321020100c10a50b90510801d00d410508900520b5641c80c5c649401517200161802d104050207280709031118410391401810203026551700f4a80c082c0aa0300c18810440860130b100c401e4840142403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891936474 1250 891935224 891935257
    0x10c06150314030708070609020f0d051c09061d010915030b0f01030e1c110f0f010f0209181f0e0604061e03020d060e0d1214060a140a0e16020f03090303 67
    0x42d4400300d18ae0745480302403142e00c001001441c006105001c940c07074140784940a121840c0f110040300554413010a401120b000546c4031241420311f00a5040541180c5414180a00300c03996580440144590003110000002d458400b51480c0381009480303010101c2c02420244007829812242070b03a10005214000500a40001040350344c4d40070f01a4a030300e03a001c00040e42c0d0000c1c04180d511341d49070b841c0162000507601e00341c0342c13218007070091084d0b5006081c001c00c003003400c7d0241c05102402c01406429000c3c208515100307000d80b245038a062200410383c925041e000740c0390075010081104d19035885071540c19044a0510340d844901618a0107503941191000039800c07080c1080c400030100319002403103030300c80d40449400040c1c201048452555443e4414420b102c83d6007071403101e8107410782e5515003242500400b0710200505e84510445000040c2c003000c0c1c82c60342c446441c00410003e94114800740c540f0070b00d4401550341480865040302c4e48800540c5042c5030900800d44d07900c81c401030a01c05919 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891937724 1250 891936474 891936491
    0x2090607030c0b0c0918040f080c0a02150309070b030405070f27060b0d020a05041703040f080706091a0705010c1d0301051e100807030308150405130201030209010c061503140307080706 81
    0x315025110005270300034a00e143c8940c40d0550090b602e0401d268168899100305003210801e008000449205101e0803024000c01450480414100d40024008581c180900e100104882e48072400480080222680d83d0025200c081e5100d0300c40d168501403000903509043c411301c2815400f03401ca492030640711800690f22302c0c02400031117060050383c021483c000f203842c03803605040c81c00002400035076500306403032a00c00b952040701d03643e903885521901c00810a03084042040b00e001c0790805803940fa0b0020702915105540e500c003401c6031031110380f040c0810f022a4603508049105010541c007440709030700030403250030041915004250441882d0742c0b008080710010300c1d54140b10030558020b005070000c60301c08a44030300d0b02409908045912040058148401005500d828050580600051000e98110b0015a00110061362103011070310b05001113008441c0c005003540c80b49100c101d501d130500c0075145046103822201d51500001091465209006000204080500f1128150b41c04400024802e5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891938974 1250 891937724 891937733
    0x118030b070c08040311010311070b0c130b121005010e01050d05040807050a051b0a05061902010204052701080309091810050a02190206010f140402090607030c0b0c091804 75
    0x1c1e02c14074028440000820f00000700030b852152000003480c241ca0a000d440c0040300100e8090141d4034014100180190100c0d004845c0400141891130810ba0440030041e00c81042107010b600076052015001080c3c001c1010100d15014404d0241000b440e0a2900310280360000703203e030244440b030b004c0c0c2a5803200402c0800800100711050760743d00030291120b06807542842602e49404000307110040820003c00b055134908849a0829100001c00c014100156a260408001e05102d002d00039590300f0000426581c0d60f0a004030302030b8001402585014140800c08000350ba07060b07000d460030354010f008061130b43c1d5443e0a01c0385d00c00c100d000384804008100c00190300c1d20011141d503000c02c525003018081000404d030010700c968550036031401006000010100d0b540c0b0b00902c01d41c141040b400500b03001401d0652030344108008010005801e110b11000090f83ca940441011008a030883c0302c001c04011420900c2079210b01c0c00c804040c20704028a01041c1d080580140a103541d00c8070000080410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891940224 1250 891938974 891938987
    0x1e0806011a031806040b0103030806040c17061305100611030a09051219300815010207030b0c1e07020310240803040f0902070503071b121209050118030b07 68
    0x20707100d08013101c5643c10181045900e41800380008ea000400c1040015441d081502a10041d2400d99840361a03c50380e0400b00180c6100c0584219884190310102d4080c50a07a4025207001d01c00104041c1c00c3c2900c0e085019006071400415850750b50010b0242e11a95900400c03400100c0303805880b00008422000c40190034061030500413520802c83c0364090303040c0302e43e544016900d02802510850816086a07600724044035000051740020b030b0303990002c1d03103800c18904941d9201d601801125000c2c1c0d100d9541a0404e20215641c0003880f00200e200b1200d0309102188039010703071000e0092850801e480d000b094071030400841c1309c80d11588500e078500d401710307001440d10500c4030030154048000d0349688901d5103d81c80741c4070f0308660182131308004c034000d401c510032115001c1c0d111000754a03140d403a946190301031181480092001c407040c240081c1c0391800541005403c0c4c0704803002100c600301e82c0320140018649070011170400c40c14070b8042014000c241080016660060b403001046c3d51090001c90b4071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891941474 1250 891940224 891940261
    0x60f0607050102030903191b0305090d0b090a021804030c0210051207110d0302181302190206040219122003030d3e030705070602041e0806011a03 64
    0x1c0e5031002042184004000c409010406000c100c0d0840000c81194102c5d0405004000059510800510940001c0c052002482d840501a15441402032542c4840500241c201c82c5071640d038004401450462030154001d900c2144941554482404d0584004002c60010b4034001d009480c51f0a52010b06030046e42a140001c41a015000942c50110401405015290b508945601c21003200c00c800c94002e0083e5022501001881003c1961660401c0b141826800006400c29400c006180204902004040c40500c0703d0f00103082a0074184107011003003120488410708c07411104002d1001b02541208000c0d05a000603400c0c4c40c2120f10351321401c0107404074070041d6061100042802c1c0c05a12904481d9808038500060021100752180000300115186114003a50a410103460151208007000d15000030182c40d04c00c0c1031890036603403003040380c0c40358110010316091004802483c0c40201d071102d001d0030814015001c55450300760000440220038901d2454180040002911001d0181d2911038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891942724 1250 891941474 891941483
    0xf030c0204111b03040b0d0b130507180501021c030e01110324040e0309120102070804091a1801060c0f02100503190b0303042c090c03100e06060f0607 66
    0x120540311201d00402d5400204150141500346042c40b20703100000c41581d045802c5a03080304e00c0c10584030001801000e490b050340b503102e005425050703051640c0f4496940309011948840c07004201e003100d10086031480e0360119045510903030f017480c040b21254075054503444640c1000310301c0480d81e0b10620702424441881d040e55110110810080e98503c0030540d1180d640c0c0ca005000220406090205548000c000000e507540b00300032001590410242c00580514014001070078115555100111b541c450782c441000340e625110b13441c510500b80d510045007044129201000c000d00400801e078900414464041030040b040491424040c0c0c981940c276038150b0061006001e402c4544000c1e016810946101d0940c500f10001e80841400c14442c0705000796009000750305207454100c4a80c4501400300c1000381c00c0103283c5a885200001c070b43c1a40c090885640905070803034040050501d042a80d040c0e400303280342004c82c003510b04100810f040350007400a40d040c2400c0c52455001c201c061044500050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891943974 1250 891942724 891942731
    0xf030a020d0915060918120908010f02090f01020a0201090b0c0703020607060204080115120b10030615030b150904060b030f030315090f0412081504060b04051c0f0f030c0204 76
    0xf009082800c00381914a07880c010840b042d1074910b103500300c5004098a1000842c0c00111801151800003074603005603031071401032003031502d41c41c9907401d503003e046125820640101c1c46034680c0c5007410595036110000c1c4001e048604180d0002000100070b48603000b501000050300da000d60205020180240d600503040554407030080ca0220000d60180c440c250065203032400c000124402c04003150110342e8001401e06258115440f003c00c4000043d10384135036410310040010015002c0e00410726400050f04c000440a85503003404641d00701c0007000d80340c84031190b003012900c1e552210a0a90065000003002400080c00004030b483e104500c020101c040c0320200410941016401c61150b50351010750300c002071615030a08211001d001030b1030090441d14003528030020140301c0c000345644101c04035100001c1c42c18080c0854102c1c0d21740c1d0000c009034003000400b0f0010303040644215040030010004254551882d8456a880d001c00c0140140507800b545442420300d827160380c248240c41d80092042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891945224 1250 891943974 891943991
    0x61315140109050f010803031f030c0303030e070801021e030c040b04120302011406100e0d02090a0c09051005070209100503031605011506020705120f0607020304030c0905010b0f030a020d 82
    0x51814031003441a26182401c240c00250011130b011050b82c125185103008604644600c880310b0f0315846c061030b107400300b000121000400302d020143d4802c0154000c1d180050b58503401703c18142061850340141107da801000710740c070444c0f40306d0140030b0004003086c103d64030b07074940794442e65051080c1e80c000b00088002107008542d030012183c0704075080344030f034000300700c0003180b4881c01d6040c04040391007603402558000e06aa41c20700446501450810050100507069a5540001c1e9a1401580e040800c1035a40c142103140715000000306014050480d00b25102d5100c51200910604c500711009000d40c900c8008601d80101c9407070040b000d04001020380e0f450b62100c800d001c00350140300006803025801c00b40418010025078011805698040e400350500300e040405200e6041c2004031000e0341c0d4880d108203104880c60606c84076000b0701199028560716480d40c00d1001c0001040c3d0800b1030b046103450010440d01c0000c03811501c5007582c20765640c3d00c07552003991507402030145030080c0f49010708140d0394 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891946474 1250 891945224 891945251
    0x123040e25020c150304030c151b08190225030f14030402130c140304050601050f010f020616050906120f13051e0715090801051503061315 61
    0xa00c02034071401500c11003461801c04200eaa44620092040d0014026002415498003803801554000e000c0e08007140c0100e40c03541c0301500f901e0181d61040116507248030664140014503c1c0c1001607426207030140c1c10303041c541662001000c24658000038540c1c0020b14459001d0088801c10040d00c01445844000314203040c040c0038088030184070400200329250322000701d410441500d010f240c0242c04540c8410725803684400400c190141141441601070a014240d52640002e5128510800c0544055403400c0180004821450201e074140a8580141544650b001400d507a014011a080d003000884504040c1c2d43d6101d140b08043e000400081e18030b00c018940c0320207902031102c5a200c81d030140e6560900c001c0190801d1001000c41e000318007180c005c031032030001500c0e5600040080d81c403100d03070780c0c0c0303800f00328032a40c104071004501101030401140c1e200b841065409903400d903000000d00c2400f00000c0c2c5800000300080e20550b2040e0012040c07100601290b00200701c9000c0401110044119 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891947724 1250 891946474 891946501
    0x180703200408060a0c1e030f02040b1b0a120309151b0806030708070603091502040e0f070c020904260c0f07080d0c020904080715050a0b010e0123040e 66
    0x809480307203d60400301e00141c1d40da21074158201001c3c0d89a5136440c500980b0601070701140c80c8140c04050f200c446414904405200800c014448140950380c0c0b10400780354202055000034140c0401c3c0c00445000010804542034602c03a04440d25002413143c4c0d981ca400c21a2090b021078002034545051038003604010351380038001810401d0340b03815070b40b41e0310380d410035590b21a030b800380c0c0c60703960000c4c8010080c4900a41100112074484c40202d50505061903241c2c0898019038021a5001d10100510280c0e03142610700d640c0107000303458004032000054001c2044410041c10003410324013002802000c200c04081196070010245205540e5036080ea24820381c0e075059800a00001d000c1c59000081500d000510a60a00c40d603807038007114140c4c25020851041ea00030005d0320500001c0244000003050302d01c0108d001d180102000a16051803181d407800c0f504030984660600c83d86602d082c0352aa0030000700400c1034080209091a8606806050203038010f9130f0100e0045100c00701400740d40a034404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891948974 1250 891947724 891947729
    0x14060d1b080114030c03030d0b060405100f12051e040609020406090e070e010f140d08120a0b03061b0c07081902010f1404030335090609030403021807032004 69
    0x14052003941ca02c03c0101621071012101c5143d156004001607007d8141c0c41e00611180c000061806080c140e640000c21a540b45691448001030307800c041d41c3e0710306030308841c03504030080103c07404100398540306041b10700c856241a171607000301040000207002c221603a0011010b803540070380140112551900294081c0c801d61346000f00500880d00082040031003010024100c1d2000c40c0260b80e12481d2000844151408180d800d4111110b49038180110784030600403c22440c41411000c03813850520f12344030495980b08903491081d0480c0781808500d074000c0150b483c0424144c4155a61408003200d118500380051740f00032914000c80c4450f0201ea40c0e0520300d04105030003030f200c000d86002410811600640d800c0d14032002ea2074240310500200344a0480c960b40e02040007a0110030064406130760210a000744c00c400324462446042000ca440180b1043e90012410801981001d086900003410009002c85030201203e0010020b200721b031090b08860007400b01040030b50110724482e50704000690090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891950224 1250 891948974 891948989
    0x27060402090a0b06120c0f0f190504050906012709050604050c03010e010b130f0909020a08010e031e09040c08041a0705090d060b06030a0c140414060d1b0801 69
    0x141e00060022032075004848245500030400d40c6000a00003500014041c090140c0d602c002d41405821000c04002c0000c000031000420741544844082c2c01210100805070884010404181700170003998031040030054000d242401d0500e40c9807652540c55041c4015181d00e00040c4030b00c0a80007400007182d5000318040d2500f6101404240c1d640194008984800e01c00e4070000007074400100715a084104c040c0c0400f0034000c900f000d40e01d0f0b84071401c020300784030b5400203000c1070b5442004004510f4150b450b000241000002800a0014540401d4490080701c0349025651402d4000c407001508000444100f02d000030420000e980e405940181a500c04071000c8441c05c0c25078140103142c03050301c1c101510405481e0390b9a45405010343c117001c0314102c0407500b111040d441d10103170341c1940d03a02300195205011040f0002121084943d006104000e03610701008244010841800001800b00106002c8036003500e20350b43c1e4a000c0a19a0300401010000141c0507045503440f41100e41d02c003004e54102e6004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891951474 1250 891950224 891950239
    0xb0312041701051f06050a050903060a0c08060a151218050a020a091808070201050702090103140d03020310030f08220302151918030b010305030307110a0f0b27060402 73
    0x592210030a20030080146050b4484d1540702008414803c0c00200010901c5203011801c054071100824a0031406461107210b1a403200b10010f40030303174428182030380008101d580c54581407402415500d503510024520040200360803094131261995013088400b044030406503101c004140c1001d6850784000f038812841141183d200080e001c50782e0107510004e4000c200820114922a40c80403450b50026004030306000041c0013440c05030360b8080030701d402140a6490f109030b40040303000c1c4904200129090b0024181f06009000300124101d45d440160f95100001a0080044d400c12102138000e0b100250f0f042c450351040702d115660041404011a84251540c80c02c49000c808114194001d080243d0345035550f020180d80803900c621803000421960500c0c3ca5452510b944480c660717181c003608240c5a40e07000105000240394860500c0310103809020190044001a55800301540b0300b60300c0140031180260003140c3d4000200401e010081d8040b05299145114070301601d882d03070b90031074091344154071307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891952724 1250 891951474 891951481
    0x806010501110a0c180905010c0f0e19181103090304031505090337020a02090a06061b062711060f090d111008010e0c0406120b031204170105 62
    0x60807050081d40040c4081301141040d80e54002403000e4000e110050782c6401728100800c1080c031030032101f40c0e850f5894408603410b5580103061100003520960050382d000303260100c010987c0103424152880018840761030a40190800c0c0640f65401490800d407000009100c0054170000091048a110f405802d00c3c0e1100704034050308842085030700d140c25400401c003c403a6541c3d00f82c000c1340b074020718040201611090a149c2d5a50b0301100d540d40001d68007649a071019031515007103855004d100a801404203504005008000b03401c0200c00740c4d62462002c110504120481d0052803030701c264545508031903007600d8044450040140010f1301c0d5120391906010b074038200306041b9600b020702c0c1c200d610300e064000300c00d0281c0d0303c00910094880010300342c00b9840642d650213801c034400103585e507414541d50415900740002c0741c000d0144084410108010880e071500000da80c00d40f0100e014002611221a00110707007840c07100211401d2105c3c00140109a201d4101c2240030a41201d200130403403943c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891953974 1250 891952724 891952757
    0x1050108040812042d0b0109090201022a030a2a0510120603051b0a0905060904020d020d1b14040204030c0e0907030807051e062406040308040806010501 67
    0x140305440280210504000d1082450034641c40707140c009218000c03080440c014042201160005411780c00360108600d0f40c02814043c800f217080d03015040203c8208060300459001070340e5a00a4442c200c0700c2d082101c03a081400703500344080388401d50b002e000c0d11030500080ca449449081141005222907940d1400d1892080000d00220309583d40980b5465100802d0b035000c0c1d4541164412004204c1c0d103980300400010014441c00c440c0b04418079a450496404a003003042c4814a5004806d10301c1c81c04042102955905800e245c01036010b4a80c205400b50600104080c1821002c0107021800c140728070b514180030203003c000488003000303413400c2a14480020001680300c0c61101138100c5080042c140201035048084642001d144800c64128030f43d265500030352900070000070303101c42c3c122200ba02c140100320002c200109441402030311091070801254001c2c288000030403a00c0b65950309200040313840341c0c02201c0245411034811502c403035840004580e0781009001e1035000400f04840308040c40c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891955224 1250 891953974 891953987
    0x3050906040c03030e21010b01170403021b0d05030c0a0309080106060801090225080a0e01050703050d0510170a060e150c0d09060204032006040503071a1917010501 72
    0x1c0e540505068070403451030314200c89203000c00c0180c0e940180170044555444051014600e00348803560004107030110320000251000004000b00b01e25680c0c020f0800c400a03901007003c0d48a624554840e00134454004081004404c072464000c2c45d510000601540d920000100581068425030714114044d441384925401d94110303100e140c02180e0040e0040c088181160090100d65244e010103040d9000c00f4101e040e0980710f010002c0c2c0b165000001d01c2942c2175401580d458800743c023800c04624289031a0303002002c40c8104003440340d85a5030782c004609a041c00641d40c1c801009483c00f0301d1081c0c005d0221b22600d4410a44044550600d4200f100c8076a041c003255100c101d507a0300300b890603241e03180882e01c0c540380e0104c01f246504987e039040e4200010344500c00303030010358011402d8480204202e250045100e18403113880e4420002032100b0001c0341e8002400c00142c0d040c21903070644455400381510101c2c05a031298408582880840780109544041110b0614084c400301800c140d0b0f0360001926107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891956474 1250 891955224 891955231
    0x903200a21020c040515040612121407060b03101e0b04180210140a0504080606011d060c070f0308120106031407030c0c021806010906020c0d0b0403140f07020103050906 74
    0xb60b00700c501003c0e91031030701e40c0c01070f5844901241110407215000000400302c81113038120340c46082c1404000014440550541c008040c0942005521301440307081d0008140a8100018111512a549012207460074044901248014041805006007014500e02c440d18a4094120a02e2516001404500e041d018440502c440680b00160041c85a02400313070b0b0803030000503501402b500c100142c81c541c803031340000c140d50440d80d960913885500344800281800300c003820140c1000220040c81724120400101c2c45803022046a400c0d6032403d002c81e10605000c01640960440b2032101b500006000800c0c00920401c41002510381c156a2905019411500f01000000701c000f0642c00081d8514000d074440700c08060607041c81c14444141d60300050380a4041440c540000e8a003105010b00c5503042603203a405060240003401144030207401040c14020240d00240c48051444045020b0500509409203600d0300030303c605a40e40d40d032140b4a800c40e4045542240003d14020000340d03440703008980b0600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891957724 1250 891956474 891956477
    0x7050a050103050907170c090105040506030c060d0b0405090102210417031b0d0b19060c11120307080c070e0c190e0301060609140103060312030903200a21 68
    0x2016820000110300800d401003060007284501c00c0c000c1403d0100340d600440620340d02c1c004024488901c0e0074040421070680c4403a000e54246418400b850360041001e480050f01a071742d1030f03120323000b800c0c42d03101500e25007125607007191416090100007034041d0000e281040c42070741c0b1000c1c02c80c014a00e500d6a04000c460190030110207000e103c207500d0881c03000b140c110b0009030385040c0070201c40c0c4000b03030154407031005209142d503078082005071801d00d1003140102252a03891071942500c0d0940c080c00c2034050020082c40c4101070040000c1542e02d100090080a1850007100e071103180c686007100325588502800702d00c034414101c1c0051241101c2107414445d103880301e0117504101ea04890143d20300400443d03042405030300118102c09803400d03c00c40f030040c000b50b660503032514a00301d00710205150101482e41011b007400e80510200c1c180548450143c55645000100d8041504044445042455404541e959041c0800309402d000007210800a405028070f0038441c0260100c81c891001881240d50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891958974 1250 891957724 891957739
    0x1716080c03030d0f021e0304060c03060501051b150f040c12020f0418141e010207030c2301110a1209050d0c1406090d0215060f0f03010f050106091401020705 69
    0x5001c580f60b0001c1d105803160f51005420006c66034001130100b040710100051940c4003108102c14402d0a000d0050090285d04003081490301300400280344c1c6c41a4104100707101e44800d6051043d4404101a041d01b20440300001c40500f003180e5400c04003103041d2020b60b01c031840040e0109008118a10403840982e0080412901005070300900014105680c200b42c0344505517805c3d000801c402c0e480340c0144403400c1c006818443d01100119861211400c0001c403e07a01c1031003c440042d4012200d030b05600e40042d100d6940012000c59400c0c08404001c072140c2c01e5081000d906e106401c400044c01c0980c2c083d03120034403c0b042150714041101c42c0400c001c0c01580c0081e0b00310800e14052404000201d000c1c451403032086030001800351425400740c503415801e03840340c8904500c5950501070303444410525285a42503050040c0014100a001070045104049107005034146076025449581c0c1a044e204050050b982e4904c000b42103041c1c00e20071b01e00c1a035510040c90f0380940c800f00e01c42054580c001d040780b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891960224 1250 891958974 891958987
    0x601120e0c090a14040503040501030f02040b0d0e0709020c0a0201110d080411061b2508071413050a09030906020102130b09010908100903030f050606180a1716080c0303 74
    0x4440102e0140010410b02ea071403000e401040d29164400c2d1190b8084c00c015a035842c43d020006084840c540c0704118610310500050007010003d10885090191039200440c0e120284034055007098071541c0261416440042c10071030149001c100782d00b01034001d8a401280d0b00c0c4159080340c440304060040d20001d1700584c00200015040490316005150107003807a4145020039082c102d410151003a928070716400240305408101e1042e260400281018030003949061a040120399943c440f8020f000f4040d41e034601054107604c9402954941010b2000c05001608080c02c1c0031004040c80c00c0250002540c42201241050050080700c0d80c145003490300504d04e924125074450342c0d80003000c5a60402a00d0790740028101c0e13003001101e106466070580083e81000500d8098110f408801d01c0c3d08209d82000c08014090b610b810a60702d030840221070b603121200565001610a1241da0800351102d8a4110040315110000803441c400a0015480141490300da00009541e0440841c2c00c80d815841004030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891961474 1250 891960224 891960229
    0xf06250518012d030e0c0d08070803060612130c05030105070c020d020a030f030513050a03020a0902031b0a02150a0b0a05190803030c03152d0609060706050601120e0c 73
    0x140440d0350f1a8110000c00782480d00341080601c0c2c2032900200000342c45461500c035640c000d00407484100c0e0100c9100c020f07140241c1d20141d05020f40c07030f400340c0707030000110018a1544410301114030714011784480e41c42c80c1c60118411a5448400d443c2030b1403050a08001203550300b8148103483c051020b94a50244500c40c42e400c2008242c170803035007280c120154181c00400a401c805001c03010702e03c81c3d03d039951940800852010340140030f074001849000c0e031103010009a142e40c2a03220945407002d00160340d80d5110b1216070400c051240c40317080418000110428416400b02c1c00030b0440c2d044201451003a01c401e158001518900c102c1164042580300042049261500058444401800d141001c0958400780507055810480d5200640c0310004200702a0308510f220b4458950403c0300d400458456480c0d10540c600350b010f42c2040c01c61012210000296110b00c00d0b142c4003203005107a035946030382c42d00c1d280019200a450701804a501004400300d410340a010b0000343c01c032403000420034410078804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891962724 1250 891961474 891961487
    0x5090a0e03040e0f01051f0f2a12170613020919080105041103030703020d031d0105040807020f100c0209180f0a12052a0f0625051801 59
    0x110031455220801000032800e9450b42000d01c00d01c00000c000700781358984401d1060100b8280c1d44140842c076100e03085010303150132503012000d94080d40f42c901541400380c41030715440c00803034032a901000050158501045404802451a03100658844e0150f0070841e141c0000a0310a442c225440100e1840c1d01c1c40011007070307010349103000e0010044030b54000449030300660301520341c0100aa694448042005102040031b4022410806600448c0f0300415910000c1d280c030410004441015160000346a45011116242c41c0404440c0b0003000141403c0c50488059400040d0490080d10703880b0394040540752850b45410140181c0e00c5a441c81c0382c3c00e0b420012030000080c10485a40c4411121003002c01d020048120381180c024028180c1100909103441c071440159110000c0010401001d0140240c140315181020031441095000b1482d8000c198149004170510441034440d900402036001c40040c4035001c02054641d0840f8110526203003220503220b1201c000c2c101e42c42c03110410019510500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891963974 1250 891962724 891962741
    0x60412050a12150b0c030304050118050618030f0a0206010905150306070e1c120e0319080903030c030a05030103031e2c03060c0703110a211205072705090a 68
    0x603c00b407001c940710001000c80381c00800f903800e040c0d8008400c00082250034440c3c456807100122083c1e0101e5032070343c3e40365640d04008010b07190303d41c07003007401b01903030b42080050741d480c1c1c1000a610b41d215288218002e50b01d030340910650440d00c3c100400728038000b020144903042c2c0e40c00a0081c1c00749903521101071b03d160741c0d61104950020984402c2c10800e6621401e264641485045a48004400380e08000d0010120340140c610a40001c40c4000c52810b0141c407501c00d03c2d07848420b1540741c010100000b400c50003814414900c43c000000e1030851607074003500442c141c0f8400e4486e03031500501c5060f500b0174403d14686440100d00c0341a9185414500034210f13189850658260b0703c180d4001c00c001c00d00300701040d21081e8401c00c01245603000c0640103a0a942070048031402040103d4441d190000488416810b00240ca10321035030030078009200700c0a00c1d1302c52280980074801c6061044000317190002d8050680d45800038980c00c030048590005080e400c5a000501000f41500d5442c0b01400818001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891965224 1250 891963974 891964001
    0x1207020a0c0f060807030e0606010c05160e060306070504080c061b1c0e04050402090117030c301602062203140706111f061205060412050a12 62
    0x550900010900140280681080e1a92002e580d2030104080c1c0f0804000e020b072414141030640001c02490300044241d400702c801d00e0813204085c502c0c1003450a06100ca000d01007001614080800c08501010685018010542c119200fa6513108011207250080c1d00800a440d04054400303103480c684080606641c1d00000248008140d0110b4111300d0030102c40d607242c14103004414980700c013640204065251140c15a4103000701d141650000302c148005009040c00212503500016074003070100b050380c0d0b19030050000c6030301043c1c0c8c600c00305140d10210300c17808807031000c80c0e89210840320030481642c100786c40071100340300c9040d455405c06c403468011a201c0310100301e10150745501c2913109038215000314022400c01001c200000c03034071030601d0802e4100c582841080382407105ca61030001201508126084c040850890b40c50000348094a10b0740e1102286c00030301d21141007444400300d0300710701803445a2444441294105020740c2c0b107010301150000404c03030500424071014500c2c2c100c075807091030b01d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891966474 1250 891965224 891965233
    0x1509011817011d070e041506030803040c0510030902090f040525080706030603080a0c0203011e0527070504020c010b120f060c0319020c0a02041a010314040503120702 73
    0x8030306504015250070325003603850343e4403044000c08a0154181842c00c410440d070150038820b0030013010000510024000400c0500b403d40307205070100040d07000d4005194409034581d0391303003440c3c28103918003011401081e102e16070021074030f1a294041c0c820b07a6007090340641520015aa0300940d80e440c0580184155450f004c3c08540180401c4c8042a002103080c4101c044e4000d50705000507a4901101908030000381480c00f0002e02c086400740d02610741c09446031500d8614211a8408207014040360249030b5140340030f2908104507004030f50002032140b10103144a5000c1c40400c012815030b03500180240c0300542141c03105001c28202038005082e410200f070300108030181c4080100d041c4100c008144050b80e00300c001c1c000394424050201c1d0f40c00840b258500741c2141031034200c401c0300696480c4c02004c000d60000701040303140d5052283c0400240c00030400c100d8122400440c00c924142c00c610070303000904d01940c000c6804500100b0340d0080d50400001c40c14083c1c103401c0c0d00b00a000280450003984074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891967724 1250 891966474 891966479
    0xe12030109061221020a0c080d09080102072f0301060306091109040804060c05030c070b0c07080105090606041e29040207080723030d0f06061d011407061103060102070515090118 78
    0x131f0246828001c4c41418000c03c5801c20142004000c0071690700205d07400d03401080300d0350101d1144407038040c481c950f5511045145d501c3e88101c1055054580c501a01542807541c004244040e56000110031801450b00d40c13803d401e00b800700081000e00301c0b80204881800e20052249a1151110b04803040c8500d044a1600c002c20212614225036a402016488400103501d40140800d1001c00010400c84000740101c1c2000560642c803520002c1845024659585d008804070740c5000340c049001c1c8248400b000000540c10081c2e0314441c20b8460542650880d40e410043e5080a208075907a494104d9803103400d204259980c05006000010201c2d01400b5085800203a014213200030004100202000030b18880920205000e54086a0000082c01041c034102d01c1b511b000c4200d10b000c40311003440d1a03041603059060380306160240302800b42c0060300c1c2c00c048134642000c01c4000d41c060700303007602101c141603903c008201c40090250700c4052b8406040c07011001703075401059088008031109041c07010158 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891968974 1250 891967724 891967733
    0x61f08060604053a0c03020603060d240c180504020c1c020a20030a0b19091b0f1a0304020d02040207050c18010605040308030a0e12030109061221020a 66
    0x7404807400e07070b200044107611142500c1320300d030904a0461655902c44000210340c80f85071481c03d4a100c0070f030081500200050680d41c4044048002e0b56221a44409a20f01015042d08035034900200c041954582070309100050302401440300e492690f81c03040c24119007400700b4040a5001031903841018464207440340c046500c010700d410761918065000b441d00700c074181001500b485240011040e40324055488180644020443c40407140d0440e00000080e03d40980b0591135144031969400d5281c03400000204110340b100e190b0400006c119a004807043c0c90715060740e00c0403510f201c0c1c8981c090035010716003549017000e00603560013030000b0504984206160007040c113070380c0040001c551581221140c500a4548107450740e60007035207481a481c043d0304085015040d881b0f01d01000d0020013010000406510060300b10000c1160100113840d060b28542e42007080c290003c0c0a0f4100c2c003814880007045149001c80c111490b1382d040940b988292a01c00020000c002a0700c00003030450044244440c0801c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891970224 1250 891968974 891968989
    0x260102040302061909050910090b0a05040e0c03160501090312020c03031309050a0507050307052b150803090f010e030c18010503010c020606030a02042f030708061f0806060405 77
    0x40c01352441c0c40b00303403030444e4000700744030600d4116900c44c004403800c1c40b030040b02000307040b000ea449101000503859049000280003400650107141c0c0141418000d040d1100003050550b1381231429011941d002c2c01d08410702000000d03500465000802a40c2c0800c003040384108a008250468010754810302c450f40d0100b030440e031000c0c0040f00c000c500c02c0c40400902e180c8e03114261303000210800400490500490013890341c03002401f81c404005000c180c1801320059031101d0284d0a0550300c07a9041801c4c110601c1c13010f00704030740140b07060442103000010740c800048102c030f070034000050644440750100c81c015102c01e040740024035090721a56a50070440d89070018bc0060031100d18958950b5589041d00301130a403502e5408100854220106028075910001003031a045941110301052080c6201c0c2100d044000c840000211840170000a15075114444000e50080d5142d580300c0406070b503141e05002c00d080c107401400b01503154400c0008152807040766010703003041c0f00400c00c03460180d0360070004180f13 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891971474 1250 891970224 891970237
    0x90105040b0307090501090803070320161401080f0f0c0a03020d0504030c060e120d020d090b0f1e06030a0b0703020408070906140d0c060e130c080f1026010204030206 73
    0x8248404c8081c02550f070010700c041e004002602c011850110583d0700201044640d1540b4070003034052507415070f9451700030b000e20684100da01042140746035540000345107442c81a406c403808a807000c00842e5a000c1070405461007003910208540c8aa06c9000348414142d0002d2030302010994203200d02c281005460080d01e00913400380c0da500d2004460744c2010000ca40c0c18505a906650002c3c619100c45c05220095a204d82d04040005854829405020f4080c25260800505007950681046032582822411034081d058028034484400f0762800120f051071410303102180c0c154400800c840002d040001c1c1c0c240d0110452030050700300303a5100d107024a094620381015401c03545506d010b010209c0c1203256078811000413102c500201540f40c0710b01040b404580241002c2020041107c4160340703c107410f41600a02030403081042d5416480010800384080e182c02141c0030214010440200c1c00d81d0015080e01c0c0f00d00601000a00c4012840380140f00c400440030322075400703100010140c0e0b00da5015024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891972724 1250 891971474 891971477
    0xb18061e0d0204050934030f17130815010b1206010c1509060e03031303052115040c0e031c02160305031c0608070b090d0f060b031020090105040b0307 66
    0x2000304400e20072580c006c0d1117100300810034401e11040341c40d212044046108503034000d001c4001c0311203642468a60110503c3c018078403c103001402080c00401c268160301260804000c0e03c2091000c150a04040c1e00e0038400d0441454081c0010310800d480740040c10b41002c1c2c141041900d9441658a81d0004210a030440d211140e03201e50803030a100e164080d440e200d07180780d80954039502e00f801481c1d6005011010207030800002241412101c000c1e01e082c140c46599888070281c86282850082582d0b40c0c000790b100b806541004000840ca9000c0e10102c0c104080c001c014060000060721100102d00030101500110320a0b1070b10a40742c007a60780c0c15035001d140100040c40d61002186206101001c0317a20041512a02e410000c1111010125078201640e42400e4016580c403096400a0b00e415025180585809903501c2d01038108600795120407500f40d41a002e5401800f4044200d408841000c8058103d02c4141070f6100000c4844000030281020141400750a0980f0f071103d040301c4d41c104035a07850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891973974 1250 891972724 891972733
    0x16050106061805091303030504051510090c0e1503070e09040c08060105090c271c05010b0d050a0b0c071b0f0b0a230c0109060b18061e0d02040509 64
    0x141e0034440ca04840060036044c1c6078403100e42428540724040350701d49500034040541d03070350105040010600c00340d001885144850041707070411102c10440c420740c0d48105456036181403401c51896014001d00f05541400400440443c100601c070f00d8095400100f43c0d00030801490070009913951500300e214016401990621070307040c14005c80034a45003068208502c5101d40d01f04003e6440001c0c0200c07a00d120310180300f00341107202c440c0382089226400c001207030b11407d031241c54418041c002d01c000d005180036400900062050a040c00003078480404040c0c0b1070b80080c441c203404111866807030364010b400410f4051a0421540340c21003110f403c00c0241035007008072641000080e04143d03140d8084d00429107032500c0c110120070098142401210040c80580c0c00c000c0300d1045074103000581e0000d031901002845041d019150980040280e169164864100000c9016a482201443c20311854020b4600144511640341d0360515212032190070390b00003d071803071103001a292401554020803c04000b003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891975224 1250 891973974 891973997
    0x1a10140907032d052223070b0f190e1c15020c2113050d23100614030304052101110307030f05151201061a07020109080d05040603021605010606 63
    0x240000c01d001715840c0b0700d218459448004142d81d0420303c141107440c2c860070a000c00c4c1e0004810300344100c0d5440780080040c00b06920455501400081485d9034004580320350201e40d5860170b41e00c0400b400340d41c1ea005901e1921050007440c800c5080040b6501510300c48445040c0c84101c01300b40d910510303000400e03404c0318420120468400c07c05507284101d000382d0700c2c10008680744104004181d40b1030903226284409000302030213054041f841e5040b070845004001c070702c07410642507a00c0c2c1460800d0f800b030624000c000200c0703400d44001808026001805141781a00c0c200400201c0490403203140c400d0707000c100c041c0302480380c00d1080d900c0034000d008000e502d80c60700110103400c0f00c9000346101a05c60501c2c0070009220404007074441003c0c0101c0307907540f864814425984c014400c0e40c00c02c3c0c0600c1c011401c2080180315040151004030b20036641d0408040d1101c55175911805035400003000702c2c000380820300c03a0701d0280d000380421002d5402c024544859640740c0509666240d0b00841c080f500d0344050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891976474 1250 891975224 891975241
    0x110301020307181d13020112091b08060f040336030210230a05070c0806060907050a0206010e0c0d020a03141003050a080a0207031a10140907032d05 65
    0x40fa401403c480500310040c1a100809504c0207070b0090407224820390510002c41168001e005443d000e0703c1c4910200184001450040340100b00d10b402da0801c10480032001078044c40004815124242214045c04a80c0701c9503800d81d19510305241c140032044504e0120441c80a050000e07100c5001c80300d1800240b14a5401030040704c11500703480030200000d0b8110f50000c20008982e01a0f1001141d064603502c07810844100c407507000e07481d0000c206080c6a040000e01d04d1000070418000c40040b101d00810341c07035040040d501480f4100068004da0007110041100b107a400200319800112511081d00e803560302c01e14001260b01c1500b290700482d6581d052817500000a4858603800349030340c05104621401d40d02d034140c1d51400c06030300500707000300010000752640c424000344d00103540c070040340c121114403080c1c40d40b14030504440e600306c8200c45500000d2481d200703075080c82c0214409440421503031904034040740a000d0080402c0074000081c940c0e02c03550740550f0592403018008800c0041d05082c40344c03d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891977724 1250 891976474 891976517
    0x1206041203141614090616050105070c0c0e07050d020f0c0f0705060711130606050703020c01030221040f12110106171e0705060d05160807050412110301020307 70
    0x205501440c01c120b0411a0091220a0490220b102820007402d00b8102107628034540c440c4040740c9800c0740b00490340ba0542d5038050300240129201390001c0c406599078000032147e8900040c0c0240001a40b10300030800690701c01c0da0707070790040000d00d01107103000160b4007041c05a9204407a8941c4800000030036180d00034003802404000c00b0007070302400c0c03030624190014109019012014002e60b00710309a441c4299600442d081c90b8111001c0103000740d80e0380e11800b42103a00a07100507405030060080541896100f842180d644149900620034140c1000440094000000307208a0b883e0007800c1c91080030480035100d0b41d1600450f07682e001e0071560020441c1e825a170640d4071440901d5040006612044404140070710f010a0a03891060792280c400301c054035040050b0f1040d500b005000850444100315030308034911a141050a486041003a900304907a090b6040302c035040014001d1009200191011883c50400d80c002c520480d044240b6000103802c80c0c0c02564034201091050b025180c042843d02c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891978974 1250 891977724 891977741
    0x3301106060d150b04020702031e120c031c020702090405010501050a0803130b070f06090602030703060e10030b0a0626070605030906010b0f040b0a12050c0a0215061206041203 77
    0x8401000b8071940356a071594041600c030850759007544500c245080c41d1129810b545201e6001000c98503416510f84c070710041d103202c0b10350784111806800314411205102c1e90469201c81100b10080d03240082c10b40030540c5070080d0090104d201c0313400b003000201580e070708210940594015400080c2c0d551510b810040c404e003c0d0303440400c003500305001c031000c0d0020724515002100c8d04910a143d6440d02d51030402880c2d80c96060040a1502c0d040c40401445030301d42c040d40c400c80450710700b0130030b454840100c0f034104241101c10380807440882c90b090000500c4403440c241c1003050082d010035000d485102d200c0060310444201000000305e000e81d8600000c0070000d03c001000941809440c42c1408004c858645905000d034581e200d400080030400ca180110848005017240c0c1103640d21500c4030039005000d00442d5158082960074000421300700c042003801c82e806240c55800610210303000d2403008003501c0c0004c14613030f80820b490008441394031051005074411841807201882c4c0c0d00302200084c0c21502c040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891980224 1250 891978974 891978979
    0x303121103250e010203071b0b070b010e01170d0c03030f0e0604060f06050a0b0a0c1202100f0612020906030f120d0c030506010504030602031b041805011401090330110606 75
    0x400300001a600401103030019600896513081c1d001234a8840401c3c442158004541d07403500140e0324062000b0361103200c1c1618000302036a0701503680e0351468410b508003108407440c0307604050003407045240265842e00c3c003c0e10038140030898510408183e8110b1b00240c01e41c0b0b00f1500003d0402040010912816504841c0c210303080002504000100341721050601034003114180c00103024203000d006140c0070316420b51085002281c540c55900086d151084040301740107007400c006c14030004006c41d00031842660811940e0011045440d001c214042d0b034043c00c9507400d402800883d01d1900c0007800301d54210405290075a0707607140314400c40700403680d80814180c1050f240006026a40e81e010007100d0403203810803c0580c594590007507001102d03410683e0148050380002e400940d000d480d0754201d481c05d070209400c10251707030b82d0380c140342c64040d40d482d01034000348143c4408d00008502d50110404040340000c4003055180088062110010252041000c5294460043c64950040200e1075100c0001e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891981474 1250 891980224 891980237
    0x30f0d05010f030b071101020f1801081e13080708210c120f06400b0a03060e161202090a020901080c1b031903140907030312110325 58
    0x4640350412a40005001101000310581d502c0c6c1c0144425010b0710340c1c03220074078041e9640f80741c284505580351103c81602ea001c15100400543e41c03180c1c2002d20f400584c044001c5030100c1c0d890308080441c0d6401c0620440d0964002e00000010480750320240c82200c00880050302a00c2c2e0030038400c420590000e0105115100c10804240d40140350580c06800030101c8411002d6611808006103001500c048001e51500e10f0031514544491178200c0380000c080040c8074040905500401c1ca400c1c1c501c00d500594001481940030400907200f41d21202d05c1524500c16914404214803012805c000c031903008880300700220040205502e0308001054002010000851038035010000280c01038400030705400c015800429061850001d10f52828040058002601c0e40d8180c143c241c0e500440c44141940b00091034002c80844910101000300e000f00f003030381c0040480a1a640c2c1c02c590610800c0b10400005c2e444031084000303a503080001c0e5006005484625910241da00c0056045035448906981045034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891982724 1250 891981474 891981479
    0x3062d0c0824010819021801120903170402060c0d02030c0106050402161407080a0b101401081914090d08070509010905040f0b09100303090503122a030f0d05010f 71
    0x31200d51403140d031a0203082c0b0401598600390403180b8a4840b91110540e14000100807140c607600e4010004620f47c244c80d07499003481c070b1002c40401c94036144c4000300401d001e40310f500025231407502c82980c06403001700b076145041c00b038600040c14100340341100400743e480072841003c1000280220809807000b560300318240040044030600c140181403014001c8180009501062482401088050006601120b031018041c2c0341200980000300c4a1340d40c0c131460f1140210700103005c2e0001d43c1d81d00005030f40c1d035445520b40ca1081c0d200c52080801d403106d0b80f0740d103402940d014415110080d12540b00c113005455110503d80000d400e1650040c2800c0400608201d8410f050788c0040350344003650016140010100c090203c1c0500030100490260b40c00780c5410100315031000b0480b14481664801d61715440c23003940c2c0c0d0040c075a49510107049040d1600f0184048070107101544034040710a2100c0802c061075820150b86541943c1c06200c0d40700c45600d00007002c0c0030a0200d4007480c0d00500d00c0100c0520b00a1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891983974 1250 891982724 891982771
    0x28050f15062706010201060306020f0901080907060e10121103180d02060c0a020114010306051e010e0f2503020408012412020a0f09020d0b03011503062d0c08 69
    0xc0e40d2040b1075000e4101c08901640d100758041d1003d564070020856441e090b40c407041c5029009101c07914000f5100c01c00040182c84085a07103000c560f81c603244c07110b40c900c0c0c4604001107150520610f6040200c0d580a40d84440c0c46801550b9061401d041e2859907404d10700c900007014281c5c03980c0c0c200b05501c2810f00da80303410b900203002540109412011510740e031580700d04078094508104d021540201c100300120a0100703c1e40030501406040021080b02c1140c0f2010240c203550902c1614140d40d240790003f494100c01400391584804584248241715120501401c038040e4400040c0000990103d818082c40c0024401d0030300003200400c04803001170783d102940082c480c050003600c0304408001c00590454a54444100c09082c40040030348445031903402180080d000074080045e40703414042a20081d007010721444824201d42d0105040752802c40c1c03038032400740851010224500302d9407000c5041d44a084021080103810042010911060ac060300070704141e00944201112030640d4070058048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891985224 1250 891983974 891984019
    0x11103040b0904230f0901150b0a020706080405060c130509090a2f04020a090e01090e01050c04030f020d02060405130e01050105011b170d0906090317010828050f1506 73
    0x11702000200001c994403101c4140c0541129a84115030f596290408144082074034094104200151b0894006e55030f102c4003201d4840041d200500700f03402a4010aa1002141006140002c0041c0200f83c0c80c6a40318040b810b0100200c4150709250071008003401003015444d41c002105415855084211101d01c10b034280c440314071032519200c1c0781d00182001c0410b00070084d4400810702c5c101040001e41c2d40d0440303071001d40400040503101d5481c000014529200200644040d01e8110740c0c04e07803400103150b0030321600e100d840100b6640f02d23105010020b929a00d0003100c0141c0707189a40c01041c18075201c5091820348030103030002410f01002480c1044000e0030280c0c003d810980040201200b05510b40700b2002c0c41c49440c011201c443d05009202d41030101075001283c0701803007503503240f07904910501d04c034114480038001c1101507001000d0030340c1c54507006840d804030b09407081a108006019643c4283c0341861141c808281c54200ca804108450300a18290b0ba01842c1943c0254803003c0d1000f02c503000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891986474 1250 891985224 891985231
    0x10b01050d180b0702030309060106020d05040303030b1801090204050a080703050c190302060d02121501051603120501080c1003020a08070f110706020f0c0102070b090d02011103040b090423 83
    0x1559440c0031800c40000b4100c0e44030841a08081c0f0500942000c680c000e450f54000c031400303400751284400015015100150050108180d80e644608103030460760100c01503c2c0c456401c6a105000c0000c001c035820504090178003d0010320001039850b46031801344100003c00e6403082445800509040003c528007207080d5a006001311900e4a903d101c4003009906142143c101940020b000700d8003505a02c665401004031200c940e030400c000f503564880d240c00c9507496901c0140050014005030780140e0344070b821620100d120b03040040603280c6181511007101c00903031080c45c01e45d008101410032818450050010f50f10315140541ca071640d08103002c1c01f400c00180200040207914080035070824880e1003007014014810b01907404061703803403400a544081648200105000c0e040082000c8e40c00094044103d82403040c1050500007001c08125507403032090030690600288807a8801d07406400d10041002d856605d64654880ca1030b0700c1404125200711200001040d40c0d001c0c7d442c3d50390380c4501050350 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891987724 1250 891986474 891986497
    0x201020f030c2208010c030b0d020d021e150a0906020a0305040e04030e1207050906030d12110c030403080d050c07020603040b062106061201020a0504090504030e0a1214010b0105 78
    0xb038607018a011029180d01e519054200c0080b01d1501003442c004c190805400d9107400c2d038042c005400c0718402c01669401d0132500941c0489644101c20050500206e4131203070506600400800c9842e42c800704008503501004d07030000c0540000c5c6105015049084400506041e00c020b100303140c040d0344c1c00303810b03480f030350140e000c1140071a4002420584101480c000c8140064100c1868050902c601541e0380c0c058001d01e48182007420000307500e4280022003055000d6113950b0040c030350b00e035030a034040281402d40e41c04075071140801c420046a0300400c0248000d51082c11f809960705481407452040300c102811590a1039400c10150000d6503a07281542d41054000d4401403032a1a808001140e601c0310072009d1841c1d5441c80b0034125182d0020680500c5924251005e00c00b28029500080c01c038810010340c00c020440600050099505076409503038414480e08003851800001800201c0070038656100c100c1403600c44448008020420710600e035289a0350000f44100c42280c000640341d8001d009102c00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891988974 1250 891987724 891987727
    0x5070807080403082701030209030c090901180f0b1b0a03020307210c08090303040b071b08030f16031b0c1e0302060f0f0105090115030e0601180b010201020f030c 71
    0x40a201641c1c0448008540c0020f009542c0e440d0000240080c0120040740b080c9083c0c1c2c0581c02449501034022504800b0004003d0080c1e5000a02004224130000d820181d5541d078949080f02c80f074110f0101ca81d203150058885949a0307403245044e05050000600d5102d070b00030382d402946026138081040d50051549414050303225503620710211000925019035112001d40c0e40100070590000350311044c00e074003460351425040c0c0c1d02c000969642c0c2c031013943c004128481c00400075880d0b0344540420300d200f8180031903140250465494022a03030b0801d4031b560003916001e43c18042c2034078090b404a0001519820180090401a0250f03040031004034105d07001d1010343d03a004000c103d1005014810010000c84054401030141802540c58808541804400d00000045041c170906442d21030304880f8010076070740e401d0303080c600c452100040c45000c07a024192684a49020040103100d020302900c02402c9840754080125110b0042c0d490100300b40d8190b902c1000041a2030011204695100c6100d48109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891990224 1250 891988974 891988987
    0x5010807180303030219050403020f0405040203070e04030e010305011508011a130b250c030f1a0a05040b07030212180708060a0b13060803180a050409110a060906050708 74
    0xd031030103084032010307041e440641c90002c020142c05502400c1c55800305100401000480f5038103654501c110700001e036000b2000124131000c5c2c41d0030340247d944284040d090790010f90351540301078245175050301c0031801b194810400c2100743d40e043c440c141c01800124400080000c402c003000c2e0500c0010300400036000110f444aa841065103800c88101d0b108030003900ca14140d0350111548a504124031005046090398540003285030703810f0840407041d402c131114225035032666440d003100b00180e007400c940c3d480007802c1106400074170204e42c1e480351555071401b0400c0c0c0313098034005101705c0e401000031040c148103100d48140c003180e107a02294401e40720303180c520780c0707040319011149400d41d0369200714518454a82081070740681d6404c0095907a400307446900d11000c5545401059a00c180903221990344140007210a000112441000e035040190031070200c40e803075401150659000f920306480c0260018081c14a500740000c400300102198585600765070f007090b00003060b80c40344c03900242540724041540c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891991474 1250 891990224 891990227
    0x1b0c03030b0a0b04093b0a080705010c030b0603070905040b13090813050607080d02090f031608061303021906020d060e010602010b0a05090c2d0304020a1a030105010807 74
    0x941c1c4400080a81e401c06039208000c0c080b5a110340510007025061002c4e40462400240c43c491005c6010341d00034040018011800b0800090b604400030540300358000400442c82c400300902c41c0d14021030001c5411020765a000d4140d9003d0042c45000c6d4604000300000035502075502400c0c0d03001101d0204c1c00120002c002044d000c5080000070300e031840c00b00b02c2010096410010302d40000210000003485603a181000144d0082220140c06280c0c01c202c54544005264010400d501009110b82c01040d1504e0220303181035001c0c803000c24035040c03218050143d0b00080003c15400030000d11348000300402647c0003901c407034000e0600c5903a16032100c545420030480340c05445525a00060402c14980e488a040000103028410400994a071024501c142c1c00d2084454003940c10160041d6034984072101c405209600c425045146040751981001d618410f0860b40214548482c1c80107880c3c3c00c190040200555a0f070f480005e055510301c841d10590282142500e0448409081440701c9946c0c0500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891992724 1250 891991474 891991481
    0xd0e0f0103090212010902010f14120703090f08040906142407050129041b120b030f0a0b010e040f032d2c0105030a11091504050907031b0c0303 63
    0x20029404a48600c44d07804244055104450300c9000340d0b40c1c0e0b440001c0540094404000c00f80502c0300c0340710104886001140514100b41d0002d04a240008441200b52901074440344406c80882d88038100240400c5460280d0040c880a8a40112420021401c410000d040c264040700b1100e03030103900103600e03591042840b055a1307100750000300911001ca600101180700c0c60000f10120070030b5010004810b0142400e100360716000304420743c003000802196030706643c60381c0c0d5100b241c440c858a0b03e800b4141a2024041c0d99015030885000300340f18102841c03d130b0070941c41600300048580c5c5d14000c04c004107030001031440b0380d6a05400d014034605e12110f0360045111a107246079021040b4440c0a0404640c0b14141d240c000040042401d401101208411f500b50a0b6807122030020703d050005c1082020160321001a00380d1006a15181480440c041802e0302c000106004103514003280402c078905103020316590007901c0f490104441c81500c401c000760300242c0cc49074010001d00f03450b040c0405000c0e51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891993974 1250 891992724 891992741
    0x7111c0501060f2106050c093a0b0c030c0f0c150702030c0a11040905010e0f070603060b0703030504020a090518010f0509060103030c171305040e0d0e0f0103 69
    0x15158800886905110703019210380e00c6072941001c0402000504014040000c070f58a1018440d04407414074030391603680140070054030301d0070b103d0010059090f00d0303070702c0d20300318403c1940060043c80015501c1000700d110108449440110222404e801d1000a681004181c0c0c08034074142c6075602e940311904041c03054010141c4074600386200003001c4040d682c001880440040c03a4103c1840c40e641c2d5008100d1300c0c0d000d01c08003c060365100d1050140051901034282d0114038021f000064201c001d82c80f00c0d425100d410210f40402c1d0840c0110340556401030007141d010b0011030600303015003880c00400c109140304946001e020075603903d000c070f000c655610104000510303041c1d4040c0424186005002405124003c2c0c0c942150320341514041418080d000e800d03c0346a0101c040c0226038a50348040d5030080541400300c3e200d802005511210114500140c07014400e80c104002045050109102c212a00042e80e130070181d1125048102c001c2c1d001d42c4210441c2010b55081840d80c0d44003006070003911803036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891995224 1250 891993974 891994009
    0x51c2309030d03020301030203012306010c080f03100312110d080a0b0307030605061309020f0105130e0c030609241002030c1f05060108130b15100801080c150711 71
    0x1501034403100b03039040d005541606d008070300811000010150000700c0c5412641c100740b1101802000a8543d8000d54014030301c02d0060300598544039410552001030340c030880359010b080203040010b105011400441070248100340c04d00e280800d48282034165501d41c210544400c201c40000090818a1150403541d400003000d0103d6804c50f450b480c0550103004c040765414003950392030401104c06c0380d4500030084070030303000b80c4188a011203620045400c4c0e4483c60b000801200d17089c8000035100e4600c8541441240d18041c465228205442003200550303002d41000504118010b49030304186a114070711050003000c882100a00c1c188142c103a0030b40c01380d20881003050007184038844c0d8110313400e440c00e20741c003442c2c100070441c960340c500055500c0c00b4141c9003000035101506405000511280d003150300f00c444003c0d1103140303030620400111840c41000401c80010460401003041140401c10000720110460f000b002d0381000441039a150300902d440a0700e800c0340140a95a5920350152244800506 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891996474 1250 891995224 891995233
    0x151e020a031d0c0607080a090302060f031f0503151009020a0c060c030c050a0315090c200c0102030d05100801060b040f0e0f04020f030f0303070c051c230903 69
    0x204000500140300080d2048500c8100c02c0d80503494603000300341040855001414a418101c43d616008840d41244d4140c006100b146070300400507030f07210320241c1040b043c4291300303079074910b0503014012000440501904220380c9441c02800b00e554003050b140c0644400e013145842d296200708401d02c045115a11108680d8400214181c4880d81b1194030001c01d400b602061103e80541d030421411280081c0105000900074045241c2483c0300f41c00100c1c14006840c102d81c0c02c540c60381c9841045800200d40c1d031022940d0708451207000c0030030f040c46031401202c2c280900120711403000080d4580c490b0700101202c441c0d68100040b4424074246122002d0030080e4020400c1503107803243c2283c20b50042c001c04040180c1070305c00103403c41c10800e0711489200725201625440d25940d00b440f565042180c00c180e0305000d8040185042c84c0c0810207944a0041341d601e040e107001c0c0d01d0520030b0410f84031000c4448103032041c0d00440c01c0c2e6504540318004c2c461004800c003070806841340040c1c0940c050f242c0b01aa05015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891997724 1250 891996474 891996487
    0x504061e06030201140301033909050a18080d091a0702030a1101050919110907031b02120304031b0b131a0714090a0909050a06050c07151e02 62
    0x650350040c002e4901c01e8030343c04c2405250306403040550100344002495401010060030715442c0c0001c4050502c03104191096a01039034150182003c0c21542100042c280c3d601e0801420286a005002c0150f2086d81030902131a10b13501c41c001c00d40b1982940c400380b50303151441e000030800c104521958044060040603010b0a040c44020740b1b0303a0001a180e0001a8a2410f1003e01c803410300c00e59000d0504040200003590700c04d9042407074020404025240e185690b5140300c1151545040184284441c1d41c0000c6d011039404603204601c0c0c1189044000c5500150442200305021300450360040d4060038141c11102810440320104c83c1c036000d0007450446007800307125449601191428021b841002c0c0c0c0750003c50070b200041c0c90f81c1002c8820341d000a030b42c403426480030000c80008000041020f8542844d054940341010213440d1000c004035400c2d80006043c0052003294883c035500700e001c1001151170300c10107440f85c24005440854040440b039840000c0c0d1a100500d0400410342d1481c00ca05540341e96 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891998974 1250 891997724 891997781
    0x305090f15042c0103020f040f14100807050609040209150705010b043c0b0d050a0b0604020a090e06040b09070302090a06020f030d051506040f060e0f09010603050406 73
    0xc1143c0320b0a9200450002030b10040840301d14826803466000d14448003503861602045103a5048840880d0059503c41c1d405015810601540c02c8210b815001610141040020000e981c81c013503011002c01e401c022414811a501c41040310410b03d011a80035845001c034400107680700702c42299404a030000000c0311001c001064000522561040320100304a1080e229800001e400451a281100111180d0030803106041585900d0502c501540000e0240750a0702190810100c0307001507c40f0f50101801c0f5081184410301d8a51142d0b00741c0741541071500400c4082c0240c40d65002d951410301a1000241c01515181c0c0401c407113800c014100c03072080c1812240900203510013009180215848540403641c0c6000040300c407e6412408021403800f004000000d00510300174054804141181c1c441d0401d41d65640050b101512980034041d803018900f05c4098000c040401e001d0380200340e150b404070306a6542c80d20780340c1111940d06000c500c90352185400c1c40102001c0c55400c199290f5a540301c0e6000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892000224 1250 891998974 891998977
    0x6031509101a0105090d05070305011d070b0a080c1b07030305071a0c031f0b0a09060908010501050109090f02070c03080c0f280f080712031b09030305090f15 69
    0x40007540c00300820710105551018001101440c140895410000500c1c242055100da400b19805031003510182a1643e84582c291100c000c0c1100c042003061713001514501050000c000200303843c0d60300c0c1c3d01c2c000030300c0030141543d180205019050717032020503e00704400c402040d10746100011010340c0c2c44651a468040d040b034214030020b80724220190505042c0e41c02c00d0000380c2c054a0006411402d550b40c011040518085003103032820700540034000019203440e4138000d84466031040e16068501403c000307004210850365440b0b140e041e0b0416004110a90300406808155040c00344c01044185c070b288038a0b00640b0031440300410700f03181c1c25000414001603802502d1540000c609031a1404e01c5c0980443e529080b0380c01003030040025070340c03620000d000c3c400202c41d040c2c0700c1c04140c03109610f00c1e101c6541f1500110010360307209251103c0e4031956640f5205842402040d9039008401600d603480090190029000c000c05204000407204156603c5803022204084000d00620f00000f8010846945 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892001474 1250 892000224 892000243
    0x906420406110a02030703020609210604060506090f06060a0306050d0f060f090b181f09020312030c0a1101060902040303031a060c030715021612020d08010f05060306031509 76
    0x10304026070710240040b0215004583e950010003c1416070708507001c11015a010041103075101d07007030f0424040104441803103d41140c003c8170107001c00749010300f05941a40c500400052140c8000390030000c030002c45200c00c640081003900c40d151a4038613a4003d60040910b604070580c00400401a481044200d540c01d03003c2030310500b01403040c131821030081c505035400c5c25801420f9103002c000141c400d40d042c0203100300d0046d400b811201420044070b030140c05511408140858581c4510141040d81000c11005486542d01c0c08210300d503140c030f5083c08020340103030103c000401942c0c9400c130041c64001d400a5000d03081802086644036a2803a0280003070444201d8044c1081485095130312501e4054180c0d00d5115809000c0c2d8a003005554541010100140860001e29804c0c08a0070509180c1c0e151030f88064840c902c41003020504410203440c02445040038410441c0d100c005020f018010b482c0c41c4110b0b8000d8500d2230304ca8075100c0003e81000000506000404285800c002030fa200005240d0704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892002724 1250 892001474 892001477
    0xb03060a08010b030a1e0c0b030f07051809060a0e07020d02071e060f1202030a0c021c1b020f06130e01140d0b0403110105010303030c0e0906420406 65
    0x109581e68607445800e88041404556140e005065070602050440b40801c00f0069035a0540865603050f82d980c91141829810481a510380441001641102e25030074940094450404509100d416040c80600108075007400d03000d0007032040882e659407600e81820b070240100700c940718503506c0c28000081d03031003080707007032240041c421182e0024045485030160448001d050203944182410a0b01c01d584070354a0542c0b04040042030f1106900524851010358000c4104c0c080100d80c150001c90004d00e8900a40d40d41030560388055480c2c01140e410900f041c0b0301152603854050050000c1c00022040e03952030310020b4120b10006001c1e244180d1924041e010b503042e0041124090362125207400c0600c4503070701c41c1e94020f104101c003403011482e0032100c281d001e840380c50640c08600c4041003003420b44030280c0c421804a901c0b00950000a40c005101e84c8400c0030a40e46080240361080014000c2c1412941520214407400d45d901c1c441c410454640292403494900f0700105c01c00c100b40074070580d00501c290070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892003974 1250 892002724 892002739
    0x160506181e0303060108221a070e090127110310120b0106120b0d1b060c0f080f27031921030605042f0f03040f020112060b0306 56
    0xc00c2020a4440002000c0d03540c00443c21595000300540701c2080c003601c02c441100c0552400341443c0c09030100c12080070321422034045540c2a03071890fa2000c92000d06007805210034072120811644964001c0341c1110070061650700700c4410b6a0380414242c41c26509031807000d00b0542d800d8071800302d200013503014011042c1c1010072550341d0300358080e00d80b01c2801d0003059084a01c004110741d500c9144102e621000102e00011915900800038166000d000710403542543d01420b075012219008200c0002000c2c2410040d070a40c060742d0b500c9805900f00c0c103000b80700034804a441c1031100c0000c0252406400221103001a42e00400307007100c0005001480307140710b48200000701c1d40900304801441000b80d07000d00580c00003000f00340850f078001e035240c40d00c004241d43c6e0000003403540c3e6140200c0046280ca07070441c240340c4003110940b952015040740308403d080300030410603071b0116444c41181d50140d042044a60590341500c01203903002d989401c100140c030b042c103038045040e900401c0254000d64084031040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892005224 1250 892003974 892003993
    0x60f030c080705010f050a090e09010f110a020c010809121314030a02060403030e01020c0a0f210b01030b070e040501090203010806060909071e030c0801020a020f010b0a090216050618 80
    0x40e56030700b0503000e0b15002a00e03075111807000b14014006000035621606285070115101c0303100c01d2962078100c070040090782d12241c428200c0000c46c800c41522040d0111541c1c40c0141d481006542c40d803015840d03074104000341c80001c1c001c3c44107100010400401c003506030b50701c1403200001200c9000ca40540b54034a0103c2c40040c2c0145000600d00341059800340155040919644091b901e120407000e0300381c1540070307802401c90180e4902c0e400310050007160384400141420311081c01b440b0090b0300d0050008600c0200356202243c030110380641100d601401e01442607450364002c450258055845a40007802c3c18004182c001803500507506a1301c40c28101d4107555038180c00c00550030001d0321011341ea90401403081c4607211000d4401d1040e107644ac031000b9008d959a540f8244134900650100b94030341d5011440150b041e50512480c0715103c50000280240ca406800103005c0500c1e178031400b0702d690707800072329615680d003260fa10400180e0014150f030618584001000e8000c003508490128a00415120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892006474 1250 892005224 892005239
    0x633030c4803081614030405030c01090b1029090a0801060f03030e1c0209090c0d0c03030813050d08060d0803070314010f180f0e1e06010902030631060f030c 69
    0xb00c00404549545e510941080200700c20596070000d0429140c0340000c0000c088003900034061051514401d0003050010f02e030080440d00042d13069005040c00c2c003402491850f201920030400c6503031914880442d03960700030490000341ea0300d0a90344082c00c25400d000b400582650aa5201e0303044a010f80c0f10420301e4081d83c0c00300302c45445854082c90a040803d0b003100c1c01345c10050b0341c19600922070700840d84050410307000038859000642084804001d23001d8188101584242030940107205e05561107034a1080d41e13609a200c0319650380550410226100103402caa5522171142e589680000740c142e5a0f0801d108001e02038042e0030318518110113540c00000d1219020101942110490b0701c00b54246030b081c0f066034003d80220804680455100c0e200b0150812042c01054129a1841f112425003038a06107482e003061b0050340500e0507184140300b00720b4180c13980c08a00c0a4540c1035000d002d051161740c3c0a0f4200c8405000d00304031910705d05100450450300c1c00002d14140e0740110707184815160354881 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892007724 1250 892006474 892006501
    0x80703050115122d020414040e0d080907050a0b18011b060b0d0c06080109051e07111c0203090a05060a020c090a0633030c480308 57
    0xb02d280025800c148030042500c1903806100801c2c0c02d08a00300e181d00180f00311410207541c0c001590b4069500060402044030044082298001d05860510160035000d4100f911401c00b8603500d400c0c062078000240000c5001e1001c2c40103400700a100c180c0c00da480b04c0d506041c541001349070141030f00000101200070741c01001c204071007961075180105050300030f591380405012030780e400d0390f000f04510399401c001411002c1c01c440502496900e9000f198035003a050002c3e900c020707064012880300c001c0200240c028200169521002d0b50030180003184514103018502850800031038160400400003604080d80440244080902140c0c1d0b4001c5603100c2e800c00030365101e0f00c0c408001590114072501d4840c00d02401d500d900130340103500001c0c8903646010100c0c2242a9683d40c014000303c26041820380c8102070901245500f0034036080003006090300010b44800100070001c0380e21036804458000240101e0303814085129215012920880d00d000d10341800a2416005c03030206805e50b00240900818a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892008974 1250 892007724 892007759
    0x603220b1008390d0606030303050f0106440403021e031207030b030307060207030507061a0901030b0c0421060e0607020303240405070903051c120b0315070807030501 73
    0x440d0750710b003107815001e0030a00c3d80030100c264000b04011855004501603100c5d0780011070003600d010403185800d01d40006c1c0003005800840500c41d010710038201500c09641c0c0c16041030300d017030b1020080c00c500551f0f070312500425017000c211203c02402003100300741d40403d00700d650612414148219100742d03040c0d25240d00031440c20140700c804000002d900c1078869005100801c8014043e40e1403c0704586a20059078064202035020238070000e0b5042c108030701ca1107108001020501c0c0c081501040302d001a609940600c030242125520501280507001420b040360000c0c0210719025141d01d06808604000d960740500540303145150540707680030050007158040c41030b40315501440c03865440c0e20182c0c04022a5800c0181560805d4101d89078980359446800d000e254943c844105140c0b4500d0110f2800c0c4642161340881c2000f00c2034a4203151b00a402c0c40954940b01901041d01000c0201280c0f4100390225004018000703032017800200b80d0080c00e000e00031000e86c0d5051107183c2c0c03103403100310000c50001d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892010224 1250 892008974 892009033
    0x501030209090609070e0306010308180f0d150b330403020a12060f050702100b150a11120a08090d0306050604051002070b0a03150e060603220b1008 65
    0x10000120b044c0340000d01558400c02a0030032080b64116140800c1c54820260030460f43c02c080013401400c08807055401200e00c000131645040091502c1001c2261820300c40d200411080402d035049100b40d840350400a40b81c500036000300000100d2114808070595800301c003028500d91401c5c0c680380c0602c198202d9040c0c1c0d40141100e5074440c6403042d881c0c6a1004200f013918a0740d40d400349010845068001c1e14002d043c00d0b4010726041400004030000c072204110924031440024a041c80c080b600881516108a800c0c00c1c90000300503000036050500042d503c11903000007000a103030b014190446801801040d40780222940f14a484005a04407034250083d154051401c4c48100654034002c441000700c182544180c1d0071059070b03981c0b080e800f6080521800301107503d5804e1813070b1442116034010024042080220f03020304040300414040d10024080f842c0c0c4158111181e0200c1940d440a134042d60b42c45542204503141039210030b142440e140c0100c00d4113004501c0c1545810243ca82c80c9a4541c1c0d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892011474 1250 892010224 892010239
    0x1c1d06092103090a090504140f0616050d020301090606090906031707051608060a11180402210c210601080f130f15200405100905091f0501030209 64
    0x1d4041480e0200c60108019072244000c001e04441d546582d4038520083c6200b50020038642070502d002e40c1d52210450380141725a0000303d44503403188000641341d801c02124850898016032851088501d489200700403600c0c03d000100004001e16a984450115022951581749e80c0e42c0350740800b0144d404030300c0041d004901c2c44031320142003a2050020456684500300b2109150a081c0100e00d031500d80d54403040564000754200704200401380601901150301c006205d142c10000c07038040c4481e2442c0c0348054003d0394049442c0d8080000c3c41d00d1124140e45110480d0450310b024000c00485500041c01140ca03921062030b143d6140803140000c50040a0503150260195a000c4a00c119a8401050030928501080c10038001c9180d0740202a800360041048050051001c43c0305001d0b14050400c64020b5818030303601c0362403000301c803007510b094807412120401c2a81c3d040400300ea85002d641c01083e0f03c4004175081c0641142e25074842d03040903180c4151604407907610401901280180808242c01810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892012724 1250 892011474 892011499
    0x30d0507060c031d0c1e030601120c08070f03030e0604060e0d11060c100b01020606031f1d0d0305010f06170604020f0a020601030b011a070b091c1d0609 67
    0x5103038000161600c01071500182d1081605241d08084e10b801c0149441d540010400d0942030406404070442c582506118400c9243e00c0c10201e43d40b041d0510401006444403c0c2e0b250400902e08980b100410b8050308580d402c680391400070521502a10040f000314841d000781c2e80030340c20f212007503404689080c4c83e00c01d481341206052001030003500c401203920200c46001c101c0c1a6407610043d100400488008000008030303544508101c0381160b406605540c403c1081056075500002e01001001c01130317074070541100c4450414000b900003504003081d600c0d1000c44600307000b14002a40c0d0311401a6a81c2403105990315103201c104101140a260006004c1c2c45c4415540c50540903265001580170b032006292145406c8100880d4200700e4184c00184c001000401c2802206201e060251040fa60005074401c4500405103252150441c018000c0c441c1400041000c002403103c02943d0307500694401750700f10240700040103960500f82201d2400c8a07025904403608201c000d5604003030010700028603ca1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892013974 1250 892012724 892012733
    0x50d1106071706090a0e070f18050114220c0e010807090602031e0c03030c040512060c190c0506100f080f0c011407060e06010e0c03091c02070b0f0d0b030d0507 70
    0x130002e240d091995250204808030100411a0700005c00102d040f40e034105052403211380b00c0d00090403018034114180380050100d420342c060569207404048070032900309000c260f0594480701000c0e540100c507925104610303a2143d00414007482d0301501340c1c5d90044598448070141c5a400361070062100591051150150144a0090b045400c1850280c80d60803d940c082c04245143d1044a1000300304101080400040c204540f03c00030112588001d00390600d0075050440c1c850243d041040b0200c0c00300c0107110442030003a64525801900f11068640303030702e17000b084650024042d21640c00701c0115418001003078100800d07a210a46a070102406038505518011030300b0008060215040c04800c04c03a03240065240e118980a003440c10700a084291716148081041034801488040d6551003001005003d03803020a0720702000160303082599140d501c1d072030308900e803100f00c0c3c01042c18803500003000441d0170a120302401ca5003c003000280101300c814014161252090924007010440901c49800002e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892015224 1250 892013974 892013989
    0x12080601020f011e0b03030f1606060504020a021608150615131202091003020117070201021611091501080a05130c0311011413051c050d1106071706 65
    0x1160520458404000c840c0016007160501108a4a02c0480000c0d2a5680ca11030088100401d0102e01841c10121400211251449414040c8010108949403102000a00c0d4003110160030007910441d2140400080656600d0394944400304551882000040d24040000d0000b8001ca207400c144e840c42d25140240007a00c900e000b41040c45d500203102144100102c2e103039036002040303491944c40154407203006000d110b400180003203c400f081051b081c40540d0700811081518070080148000c1e550f00d82004900900502c0300c003005401d04070f441c68060145030604031810a4084851560a0f11240808010141c0042d59940400c0d070300c2c400035100311525801107a004009403800115200d688c0d40300a0348c81c03520b8104580303c064040c3e00000c99603000c010102c034480d170b0308840c0e460b0402141d508846041240700d00c512070001c1303050b4034103141090ba03595490242c0c44030072108040041c6d44058016884a980b840071882200000381070f07180709036004550400b41008581c2240c68800c244140d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892016474 1250 892015224 892015231
    0x7030807020f1504030c0b090a140415062f0d0503070306120f05150402011d01090b03010b03040201110a03120e0a02100f0e1807050304020112361208 66
    0x59040a0031400d251106440c0c03201d41d90002c243c0c82d99a60a40c9080d52407140c80f5008201d84541c207224130360858803078100b00d905440c905030030385c83e0100c02c14000501a00b44e01026140c00c290181000501503085445807002c070f145410a00c02c80902e082480084500941001550b68030801101841502400082d80c001c02c0ca0b1401181039a241d050700c3e802c50404132400c841030114040035a051040c05d2007000d101851141c6580820305003900002d0015050600d1110b03602c11290b05441ea83c0e010704200707401450070700662038880d03945090b880e8180d0000c69059000c01da8036122001d03200008664114644e85c5520381c0c40ca0702d04011502401005030300300b003071440c0c81080460f1025030f81d14020912030665036901e1076105c0b00313580c100500c003900080070a801600c01c03502900c0d0100c5002c00c8a030307102c0581d2900c1c0351039640f14001240c17405484030541c0f00e45443c1c00384038104611042041074492008419201c0c28490b40c1004c407003c07403d0784001506140c80749206078501403107100620740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892017724 1250 892016474 892016479
    0xf1506080414060903031e060a03150612120f02240a060519050102010b0a030b04060b2202031005011704030e120f0a0b01061e12020729060a080703080702 68
    0x2d020005542203107003000c199400c10082d0700100402c804010b2803500c49480c801458807100090601502191040149000050103042c490420184038440b81c0e0181c8001d020b0000c06d01d4a040e8907040008491100f6a01400080c103808180c40b000742c0002519900c0f007000110428083c140c0000e001440e15000e8600500740c0d4480c10002281e45e61644010003045890040301d0369240b90034000383c211541d401c0d0fa54022411403400300f01151550070550b034004e42201020580d1b4009000080b03404003940b021840018075009401200c2000c3c0e0701451150b030290045020440d01c4000554511000e040c800c030300711007a14002400a0300c0b82912080c0c08002820504090241000a5080c0320032045a034a030f41c0e01c0341d800c0c80c0034001e90760202401800d031401e00345020810850703040307107940c3e1a000203024803902e000040030006041e0304403a907080c0c2101005030004000d0384100600941041a11226591a0040b440360301d41b002c5508200ca8000300107000c88d500d151740d4500b07a900040420fa9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892018974 1250 892017724 892017743
    0x21e010f0309031407060b0f011d0607140a0b010617270c0418062009120304090908030f070e060315010509040216021309120c0f1202010605040f15060804 68
    0x800c21081136010703056642c424880420500314000a106501c6030520a590400094010b400380301d10b090910b0480d070200944c1d0403070b46c621003420701c0e01320410304240d0a1035510442c01c002d01845210303000c9030b050701c40300c2d962010f002c08aa118804240c009803614407a0b03400f10003100c01540081f0105220501480c4d0550700302d83c00d13081c00a41210f4007000714035100094601d00404001444c0301b81c5010130819500a08110070030201d1381c2c014095034403068003401c00812140c0d2219020405d4800030500a2001c2c4600c00740ca207007201058000b5182c0c1d410103615600410a02130154215403580803010300440d00f166107941605100460f0410018140300d02003200d195692500e00042c42c503070764076190f6203008690620600a88a0510440c44002d5227000a84400250658154440c0c050726260445446800b414a012600b40f200344c0101490392600c04889901d130190041411520102e40c20040e5494850110080c2c60b46540032800c01060002c080c0300e0a80100d00043d0828020041c09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892020224 1250 892018974 892018997
    0x609060504301410020412110a03120c03031d0a031b050f0705010e060309070909060b06121008070807151103030f241c0813030b0103021e010f030903 66
    0x58042050740d51003600e0b208505285811a080100320103113184240590840c9828600707074030325a03074141c501c0000b40045140c1100a00755501d0102c89005550001c2c00c80b000c0c40758007a00a4519000b01074218007190901c0b000e00118052401d1611152401034050020604595000c442d00c40ba031a48810260310081d44480c00b040c401c2109c2034403e507054004120703a41c10301c40050107058401010a100d50020010842e0000003c034002c0100c811031100809d03015503c0c44c104000d8207c2100c07094100e10041484c800c1c50445880807406561003c695096040d120403429841c1c2100340a0a0003583c000300003000340c180c1820740703d844011f0519100e902c10383d02d00c9859046034030950740e84419002510a002035600c3c40b1400010050544081d0840c001d810808a02914000703440a03411344490f42c107810901a5000456140c04c0e4400b130107140e40703a100d2501000c160320030300003a801084150f040780701d4040039032003101821105868980070320896004c1203024254410781182040b4074030752071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892021474 1250 892020224 892020299
    0x708040f1e0b011a0309030f090a0b1206040516052506020f040f060306030c05061303081303110d0f12020f030d0516020a080a2007080607090609060504 67
    0x2076000c02e10690038224154900754500c040600186602200800d080043c0141d00030004100d49450348130f49400d035180c07460b03000010340c1007500740d00201d02e54100080350300a00f0710401ca0140b140f4004ca40070049038458112804c0c91031414554903003c075004026950189810a22200d00e003030320710030004403120013540d0b01002ea0f0412005035014000110f0240442c0c0b1101041c03001810709031800304642d628584505541d0318207849503500810001580c0118040c1c0b00070004040c40d000b1040a6031041405040d255203900c2c0c0c0700a41e4940c00b02d00c00312080789444505619901d81110100000200d02e4640031510340d50840c10005500c9110b0340d585444105001502a900c0003142c002140c3c070341107140e6481d03032800410f2402150416000315000551074810b54546444620b488222042a24110060045071240911181c8100c0400044050001031400d128083c260b4074040426541c0344280d6503d003460148001143c400c2c0301c02c0c840030710a04441e0a81c002c4140b400901c41c01030492 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892022724 1250 892021474 892021523
    0x2e09150c110f0607050a0f0507050106080606040f11040b031e01060215070c0c060e04020d1503170a09030b060607120f0206160903060e030f121e0708040f 68
    0x200020405000e03800315903210511206142c0240701c4003400552a001c14018882e10a5030500b006020700040f40303941d124850402d0310a90780d84040200405515907004940d58042201d0340761003036042c100103c00b410f0250142c02e680d8504000030f9030606003030502d5440e103600010030482c4403a058000c3d107019010030b146064002c1a00b074000e4008034688090420b941c0c00010080000c3c480e0329100500050342c80308280e81102c02c90f10380342c41703204a210300040c007a1203110b080501060601c2410400c41e900003204008481c49a4410800d08940103079140c0140907406841001c5a0150401c201056002c1c54443e8031200090041e45000490350710200003001440b6200001034240c0008214290100f0120b40c10081d02000f0041c001300e0107400610300f550717900008042c0c03130b00c0e0b0500580c0050108141e07442d84200191080d114200b80030000340790b4104a48592618401160201092203195410f601989003555440c0c030540d144e031941c4e2800c5540031000c8820124511001400b03031508030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892023974 1250 892022724 892022741
    0x6041a070f1506062c0d0212161401090e0f060402090409060f0c0504080712061104150306060c020105040905150310090302060604050c070f050f100e2e0915 69
    0x24000420f1818000d00030300244110681d001e0010454402c203840e600c24909500704864200c602030341c159880d00c04075800784541d02e036845080c0f140140f52921010350100d4002510440381da181400201400111802480ca12500b14009003000210b03400040180f800d030740c89240500050b00c1c00d29100c0c042002c4488801098034074607520120740d10901d003103004210860b19545000760501d4109248203850303410b144500b044a080c00d2144200b00001d5030040100310202c2401c09407030715519201f044106106010078400245031182c0410303482e0040d40010b004540680d6401d041c2402c00d0002001448007428800400451300c1c0f85240e50740d0200004050000a06808912006a4903021346088400340c106445142044100b00c441e11150050311145a00103c1500d61091241040c9051002d81030030002e40c0e0250450b1094404100d810002449a601084522801e807424508040340480021010080e449540308001008150882e482c40c90041188250384268200000304072110318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892025224 1250 892023974 892024013
    0x100323010b03030a030902100306150509150309070602070902030906060f010c0506090102090a0b18040203060612010303080105151e0d0b061c0506011d0105030709050d061a06041a070f 81
    0x46c944001142415180300f03440c4032003424207001d001d08007c000d209004c842c0c01e0032002c0020214281b5405d0b61102035096800795501c1040342d40e030502603911510b44030680550300141c80740c00400501d82841d03100b140c3c0301da21000f01901c030b1502d80d02c0030800091000d019603810001d0300c4624202081c401d01060340074035445000180d47c4c092104c20f11030981c00f19440411425020722211507900344800c28032018150444005075207544030780000d040d41c000d01141c0750025140600200426400540c11030580750300300c80c41c64503a050786c032881d1410f10800b10b03074000c00b2059107401c000041d542e00240901403004080410002c1020000c02c0040c1c00400300803d07080c0284000c2f4001e1a458810b6540014083ca0708881540203030700c000c00d00681c0c00e0700c49410042c0000c000f0384a01d10640342c040103004020610343ca4908030b410710001400300b81c05030300d1b00081146065440c0d40b80c10f000312000ca90103030741c0454503c4ae4048034085c0940002009a030002d0552207040b00181c8000203100a0b410003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892026474 1250 892025224 892025231
    0x3051c0b010e0618040b0d0f120215040f150219030618060b0406080c070c08010911030f0c04051905040f11010905011e110d050a08100323010b03030a03 67
    0x32640014904030000300c149024000c10400250081c1c000b805001109200340e030041740c861300074000b2412052803c0c03000f40c01c12596244440811950031111201500710b80e0071a000420100307406030301480203507402001c6015103050540020810001c2910000c1e05200040c1003001d10800195070004a4844c100041e03a9042c4c240a0b1010309621000c1040b42404100f10190403d0b0040119100700e0081d003081c0a18000040d0403c00b40200311007180340d00103881b28080d51380f20022406032906210441c2c002401d041c80c0c1000d4100083d0800c52601580d00030502c90030b541d41408001e29002c0e105c0f5681c8400e81050b50103203562805250701071481280103012040d61828904ad4034612148003d0411500520400c0076a0b4031216120741e200c58000d00c4001070008180588018481a02c540403d00404510421b9560010003030641c086c015110408296503130800c0001c1401680001000441c10300a0300003c0c0700702c0300c0048071551061000043d190747c0300380028551340040b00f07994006510f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892027724 1250 892026474 892026491
    0xb0307030c02101a011821113c031b01020109050a0308010e01080309031e1c110f0f030f0a1107090507030612050705090a060906031505180a0201080403051c 69
    0x288501141b608928290241a4841c146800c0900604442c0520300064002e0b10b055011301103805081001181c006140f05001e040314040f0303140c01c0d22407543c01440e106000f00710131524400701c40004020701d0024090603c07001d02d0001c0e00e03031100130040c60504642d0394205040020b1401c22042c02c815000b0740390202c00d5031601181c01444a4160001036582d002030043c41116140024091300596514608801c91081030100c40d00e051008034070505030704500c495021007280c1112a00760400e1110040c2c0c1d5070920b18540c0c02c3c1d45da41ca5550540c00c2a84200901e01051400202800100316030340380c40030032192400d10345494040281c10818007107685205101d00940c152240a008001d034030303109210707461182c17070744d60b26140282300701e42c014603040d800070b000504139a1010002e44400c1c42c040088030380380d050011014611015800245103040c011410301c0e01700d09003118151391a403005103000400e5500469144001030700481c00e100060040b065141070b86a2000103c50700003100180c0b042 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892028974 1250 892027724 892027727
    0xa0b030c0a06090302010507290a0f0905030414030a0222050f16110f030f0c0106060c0b0a09032c0a06110d2d0503070206010e010b0307030c02101a01 66
    0x1062200350380e11030494124100107042e0040d44440072603409083c015211500d03802e007568802e6108269451000844000181040c00840c0c00d50094513103070410080f1086022111040f42c150000141490b031050108010118011840009114001d0299500c44120760b01140c83c0c03180c08c1c60b441700f00030841c998030800e144040c810a50f012050410707141c450f0a150280000f090b58808100342082841148000300040401c00c1111145400c030880c2e80d50381415411401e07541140311082500d500b07200000904078030031421000f1030b5801c1841c90640e03031184003802000f40032880d82142401000c19144c0344010316009210f042510300140c8141c40d202400401c6144200c41d040303001400110303403211004940015207841410014180100c003001084850070300f410301600313229519042c600700c00440f958404065806030000b6021100c7d940d03250401180c40b18824020340f00e00585c00e2000403a200d2003600f19202150080c0165507900440400720400d0710707080515000d501000d8803041c041365 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892030224 1250 892028974 892028983
    0xb060c0613060e0a020d110a050a06020304080615030613050c040c05090906100f0e03010902060d020703090b070f020402070812010905071b050d03112b0e0a1502031e0a0b03 76
    0x4002d1015081c0000d82c0d50009070384046c0044090807905844a05035515190700d540403001c0c100040813034000e6540d40324000c0d5207520038002c0900b80d00440300451402086c3c00086065600010091f0070b8542d5002c001002c0952110810707541c610880311a854280c640d486082d4940a46a451a64500e13a04041c02499407025164134040c81054950080183e440b550000d540c5846140c01e500350a80c1c01c000130f001d0240900042d51001c030011701c0f405d080b451036000f00440da1103030b140d4807a0036596a0300f210540c014a200541200307900c9605100500e01a802040140e109501da1400c02c00d04283c8034482e070300c1c260059101e60340e0326810301c6203564000c03069141512240240601c5c1d015940c1d00c0d90307250b00702d1210290a054039480300c07030401031302401500d1024448200f02c3c800c40001e0720760207040f50305440306449030030301e005406204000c0c0440c800740ca09401964100800d0b040ca00c912b002540024600c45081c0450b60304501864801c3c20140d0060303a1516021689a12042c101400d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892031474 1250 892030224 892030241
    0x241e10230109081b190902031501090e0c030a020f0c06070c1401090c030611090d0602070605062d04061e080d080f07080a0b060313050f010c02030d0b060c061306 71
    0x3554800e0b42c4014441d405100b00c0441c135a825520416030360408400340d00d044409400401000e07001004000c0b510005880ca002c0c09842641d580f05840c0d81c500030040803640581e8000c02d0100100002154001e40360010000c4552800d012442c2c802d4000700d0750b0400d24280c0b6a00300241c07580345203009000c00c3e152103141070680c0d1002003140500c1c80e07950310040c403028440149507076140d0501da80c02e44441003d86000e060098246400c00710181b901f08020f521852084407268035040c04251141011030240b0442400c402c1000100703a0480441e05111900c442141e0b4425200d0402140c0e9128126102e41010082c00c251100f0700d0400c11021305020142c8090010040107804001140c0150684150420b1150401c00742d42e40b10300180780050b046211140c0d070005000810302280301910b268102c09180120140c0f040c1c0030740b8036001070981c0c0321012100d0060b4001d0120044041907944007000040c0020000d80c40c0a030320081c0c8a0030901c0403103481c1c600500049030b140a016940c080c80e40c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892032724 1250 892031474 892031489
    0x606021605010e06040b03070c1203090b040b041b12050c0607030509060a05040e01171c0e0f0a030203012f07030c0f150608241e10230109 61
    0x461040661030000341451a108003030400101c1d01054026844134011500504500300f007096692400500c0500000c500300c00854407500740c0031900c0c440e10b03c41c0c03003905080c1d0f0b4443c0a03807009450b02d440b500300c4107001a105541c60019881e120705062260001d02006251640b01b0249082e05424403c0c1080454a2403a0150a0800c1030100203a80401110014401180d002d5188c00c2d044008031010b005d544c0120051412100000c140303680002c4045001200d00b1046844071030564600c1403920405c1d412070000f0a00901c682d64080c900806003655440303015100c0740300140d82c0d4002130b00350380510503084c42c6140c010081c402402c01b44001c00072010307008036185140211035900203007021109180504040340010000c001c019079004c0d50911060303030403c02c3c01044d86482046e9200c0300360300d101ca0508052a46603492180184003035a104840c100114000104040e07284490264010442d900c030070010712020a80d064480400c0e9065003014410102d9080c2d180005401c010a5800188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892033974 1250 892032724 892032733
    0x1407080702100b060724020324010e010c172104020109060c05060123060c0f010f111e071a0f064908180d0506010e0408130303020a06060602 62
    0x10380c4d261203046a0766a41c0c8070515003000084400e040c0701e014030701003000601a00000a1088060700720922169840040c1030f00381280352150015a20404424221400b1481c50440040811048021520340080084100385070120708a202844c804036902034504076810300c010300066580c0014000041c10460a000d85225600d03210550358000502c42c00c4002e4083e0a403000c5802d81d1000b0724104030790082d011503201e0380e59199190b00c0d286414503044680d0700c1c08103a92074403034050144010a103619000103141c801700c2c9214007000c101050b46103101100400220700011114020581c80303521001c0d00d03082c00d042114080b02010b50144c0b28512030408101000b00e820300c10b040c04003407900c4071661161401766003420003202d11499075101e000502e01c1f882010500880d100140099004a1003002c0c0404581081140c0b076505400d010b407896100500610107154001c500d16000307405540d0041c1070504682c03459a141003150002c80c0103030800020354040045501442c4040e196600180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892035224 1250 892033974 892033991
    0xf05010612020a090b120a11031603021e0c1c1d0103151503020a0306091a011d03010f1a0f030c06090121020903100b0604090f140708070210 62
    0x41008101c507440da2001c90380001e00101060141912000502d00c0108244d140c1c0741d25074807081d596500b182c5032051182000c80ca5010454a0301c00c80c1d00c1817200103c0c0d103510810b4180214000e40200110301102c103103403112000c00d6403c000c080c00710140c5180042c0b40780349040400c0052210350314103d00500c030088040b40307041002990301000c07a030020b280c009008654407903610306104441d8403d0401c07400c10131034442d4007903168008001041c2591003e0200c0d0741e903071560408640c0884180c6400c0011101c9034071076988580b240c0c915a00f074840168062a16040009084503a800b02c0036850b20f0740c8000c43c0d80520089d8a001802003000c41e040e0551140e9400030a0300d401c03904122030300c500300003e805040340c0c0c007a01c03540e0240c0040d0030601c40b1045148400c4002544540c070036a10030710a603004c000c2416120b0041c8a03052401524903030815140010410180c900c420008080b03070388504400381940104840c0d1841150b240d5213a0400b0708041c075011381000024050040214140100e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892036474 1250 892035224 892035227
    0x90f14010903120b1309051b01090302031e071809030e0f0d02010e130f0e060f190914060f011e050306010e0702072705070e22200c010f050106 63
    0x30f081024501d0303001040b054040c130000340c9600e2000581584051800e405c080c14402c0008208814981d420101c504000a41d0010340b003070000f6220080d40741d40030200b44026184d2031448004114a00021555840d466043e60015040903482c903016848d5925041c0080c1584070300b4400f000e210648003485504d441001190a8180f1500041e05025080c5d02141280e00e036480d044014407141602040b1803640c0841c00c2e00038002c0e140c200d80d158031a500c08a5483c0d0140902c4e18094440409034400d83d000042d40400a40180c4005403440d601b4980c0c1c02c10204814800d2a211b01c541030201c030076030b40c1403428950388940c00412481229110038820b00182d10f0010750b0a0542d0f901c108082903554403040100d240c1001c9400c00031703e242d240601207051101482c0384030420343c034500c4280034030f907a4800101d0b41c500310141d02550081c0000d0504080d9903582e2150801400d008001007000021030146401c42069814440580003001440d00071002e42072040361855030034400d0601c90365160050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892037724 1250 892036474 892036487
    0x7030f0318030311211503120d1802150c01151d150301060b030717150d0318080a020111030406080103080c0a02030a0305121015110c0301090f14010903 67
    0xb002d1654500404004461620070340709030a01813080708005010790107810441c1c0e070b403c0e21a8001c410f02c408030103134035207000f2a41c0100c0c046a0402181441c001240c01c0c0b01400900c640710240441080d00c2c180541c4940e650780da290074800310032943d00c480c41c80f051402c448a100900395500d10240c3c007030100c3e0703000896101c00382c038090b0740442c110b8440c3c02d06c2c200c000250014141c0c0c50343ca40440000e28034104405140310b00e1254854071000742e51418500031541e0b04840d24400c1e1b1600000aa035940362181d0f4100196010f860034040064000c1030305c1510f240a13421042840d80a818078208640e4404c0b802000e907000a800345003010b142100143c060340c8113010061068a001c255082c04030030800900803c01c0e002012241401c0f0281005442540412100c01c1412240c000003040610404004021540300c41d01d107d034420302d080c008460702c1d100c10901d01c00a014003403241c109070b5424000c86c2040760140703400b0015200d1307a01e0b01203080081802c03000f0840c1d052090078004242c0109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892038974 1250 892037724 892037771
    0x4020f220c18031b09110405040921021606020a0506071b0c09060e130201120e10060e09060108070605030106030b0a0e10050306070302040b09120a020603070507030f03 74
    0x104074204418400d80d14041e11050840d5900c800c000c0000034080c0c41c0b013051030300d0001c100c864a05103441c0d01c04281980e80454444025040c20401040703642410b41c0a14540c50041c8005141d1107400702d00c882410203101c00510040e4801000c4c218001203011000c8000c1a450000341807144895685603254500140320b1700a010909040c1c81c51020000905c00391140c0c0402c0005089407580d003c000144818001c0103062444540001c10305059910480d8009030142c4540080704841c01f200c90281c1080d0350f0300c0c01c13a07010741c58140b04001042d0040300090810a841c403003452412640d182e01e0804160300c103402e581e0204c1400c22880350403008680c155140c510b008030b03270341452002007901ea416903849080c200d6420010021034040f4464214143d03082142a07644949601a0840680c0254004d0b0400c4007810415140301d46007446100041d04584001c0ea000c448035500040e00b2a00211210004600d0001e050300805501c110000e0280c1800e0400b040a54040320b6410b04440540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892040224 1250 892038974 892039039
    0x20c06070f11010c020d0507090b040605060313170a02100b04090f0809040914060624040e180a050f0c0108100b18041a090109090807081c050f04020f 66
    0x4142140c1e0991180304c41c00340b11600035107142202120740c908569221054412101028a0300e01401c5140c6000d0040d0f4027140c2008290604546428060101842480740c0407100310a00182101d0030a42907000b0b0407040600341c0280010100e100d981e130f402c1d10b0341e40e031b100c5100d070b890a4450f20000769000300b1021450341141d601526160300754007140007400c003490090404500041d8205a00c0000511688501420b442880c80c5c013021100d660400240052060503200d401d01c070910104d440318280a600045d00b103006a0126694140309080151030b0f1401c0d2410b410002c1419a0302104000f0309480e50020710341401d0510b450010061000380a010324591b0a90004030031418001d043e5402c0c03207000340107008212420805d0511800d000c0445001e0740600c0c0000c0000550482c4c5105002000c1e80100038140780a01c3d40e900c8005c1c90380000e2503040c9000c00f55560a24641080c42050304c1000442544400b074281801000740000c1c01200c418412003452440c500d50302b2401d013040b107000105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892041474 1250 892040224 892040243
    0xa0b030d32042105100b0f01140406030902030c060313031d0d030e010201090c0f050a09060b09190e15121c030507020a0f0534050910180c020c06070f 66
    0x641c001e40c3c40294070050302078140d200b039142e4002104043e52140364030400c110f1390001d46007070160041d90050f880b8101c1d0342c0803d60511007008000d00a42101400502c0201510143d0901c5000103040742c00540340700400d8013036030000000701a00310005d01310f0000190329400703100360b5000c0090101c03000c02c1d00041c10800801000c09050b4000d42080c0d40e4182c5c8901040300c40b549860f04010b8100c041d1083c14883d4460f00400500c0c40c0f0184114015074203000c008500d022903c0041c882808414202841040d8a1107800544904e1071880603000720b4981c21200116150801045590741d1528178080b000e4205120410002c5c244224442a0070b02ca42030100d810790b100134060b4184488428054401c0c00c01c9040d03901000000f04400b2148015a842c842102c015050b001c01c1c069030307101c0703412080b1404500078000c81c070b00711059652005041c82501495270b1206a6101100030b01d0010198494071000e050618070b406126000140100380c52013030030040320b5100c0c0451440e4824003d0022440c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892042724 1250 892041474 892041509
    0x8240d0204090506040f0b07030b09010b0f04030b0a0203040203010605011d01030e0102090411030a14040209130c0506041e090b060d02070c05060f190e10080a0b030d3204 75
    0x58a80000e10110f400070309403072292900742042400150381c014100c0313003802e580300024909802803040b07010313403035003d00300c52101d0f0f0a1040200c100d0b4070034110700a03003003810301c0000000f03031a400700c403849102c89440150312410144103041c2500c106401440c1849840702c22003130400c510548074104040e091074049105d00da0803403404e00901c16030034125006800c10380c001070002409001140214200c003410001c003001d005001c00c60101c2501c0007076100d81b004c4089000c141c64613a4280881e03000d07084c0002020390b03030350024544d903105501035074030324252a002c0030781c42a003801030000502064009000c1c0d0740d41e02d00003c1452103809542858160702180311000d000500b44298041c0a000c1c0c4610340e03516500680746c429800901c04928201900c174000d80046228100000c10490003422140040b9000300c0c040c0e480b0300009109201403603a03103183e0b80d6140c0c0c04001c1c0c03841c008944e490764580348001035a03c54a100c6080e440c00c0048030002c14503841e014031034084500b20b8003162a079641518 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892043974 1250 892042724 892042729
    0x140c0a27110d0911040908040303053a0e06010501050405220207140d03090209220b0103030504060f03150b09010c08070c091a010801061d030115050108240d02 70
    0x140030312041c0714049002d9450340229800300056901540e0a01c030800307001010007090324401600144210401d000c2000040c0c02140581600010014841914000c00302e401c0500790400b480c2031291100e21016086480540c42409403480c42e07400541669030510340080c103e403245103e214081c04d9032080c603071203484003454051520070f0b85c2e260035503446605080c02455181c034040c200c0f41e1801408880440540644941e0045c030b070b03010345501c0700c0f40e85210b00c0642c1c01855030101e00c00613b401c5403240c0080c1c08900302c1800b8501c42e49610b600c076400c0040081a6810b403d410a0034940780482900d074045002054100b00e4601e030024981c0c418850004032200f0045900042200e45c000c00d0306420440048007080542d507400a08200c484201c140d2140c0c03109410781841d000c2036115005105092144444050402c04030441c160305071a81000709085544410b1a611242480001444070b50381c041401a0088226905c8851200701d074051038400045901c40c0e83d00c100e520310840c0b821034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892045224 1250 892043974 892043981
    0x11b170c12030907050d050606040504061b020d08061009120602090a14030c0103020a1e09150314090601030503040b0c1009031d09010f03030c050f0307140c0a27 71
    0x102a0082650511500751644150641040d190440507004250300031030b090130460050600141c0000c001c1c202511650300303010003440080c3c82943e06a403600c1da03481848000654811500005500402d0b244820707041c01040340c100602091b00ca0780f08010f45100565205140f902651f8016400480c04241803410b00d0091007030100c29900305c03400200024050100d880010300031f6000390709669912080d00d004408901c2500154001703c1c1410b462411040072074070401031122a241803100c001e9032515121144004ca04414078006621440401d1550010f50003064000e0b41c030034000d10f07465045035107140e103a02881c05800020789003c03801c071610728010040945104400d1004000c981840e080c000c0507403901c040207085071084002803940034105911254100d076000345c0030000150950760300300c84805a5070000d8a1511075440c010405d08018002044030b18803604d200c1c0981c00d45034050381d0501c07281d02001481040a0001003080405c8040080100c0c424014410b07400c030760462016004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892046474 1250 892045224 892045237
    0x20c010b150c0d02120a1b0b0a150b040509040b131704060e0108010602030406030e010b122406090f07050d090605150a050d1719120506011b17 63
    0x1000300249804012a120000c0c815500c40d80241c1e100e52004000607030b0f17502424104140f10382c908000d01e078100c81c407401001083c454282d18031100300c02039840d000c1120b001070342c01521040d5140e80241010225458440080c180c402005080600c1e0400162240c0c000401c00780034441c000c07000940203c0324100c2c0d02d5506500400c102c2d21801071202d8860140c100d07004601c08152150b220403010342c00b0314015412036209900030351401c2d00344081100540741d003040e40710996480b424084510381d10603a151010207000340042082c5d038511449800d0101c10740c40000090a5040180b00568852f0b44200c0d84c850b1010810340426118240b04482d60710a1502900c45a45414190020000641c000038081c42c1048001c09401036081c0410a02c0035152041640c400030b00e000c1040011070351418904a103500300050760600c101c01c020301e5545601d01c4400400200318000c0118049194462182c001e14286000c000c41219680082c014864040c0c01401800c0d00c54000c61510601c10101c600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892047724 1250 892046474 892046479
    0x1090e0411041112131104050f0402120c031e011b08040f0213050f010828060b030c10090807090218041d01141503150a09060f091a0f06030709020c010b 67
    0x10300d80f8005c0d850002e2000d603441d08850700c00c1c1250f00c0d81d55601d03050040c54020344080c41a422a03032125400c202d190804080001800d000e00d05144c0c0046da0140034025092491507503000c0c4040b12140814212101c00b503900100c0180606100700b15036005004076880341d844912450761451500000c1c52820082c42c0000c50f00703003004d01700000301d0507a100640c101d03501d620403140e11782c0d0b20805d0700b00ca064810b58900310000d0f90708880d42c08035004e6000180a10005419120208680d00200308170300164144140403032030150741000711540030440c400040641d030f0011402d18404422892042500891040c802c585a200001c0c0c4040840e070500440c82029008001004817444408001c580031034030031003029140c000500030b9080101c1c482c0304111400402c041540c0c1c901b04140c005203007040003a00e000355665000e0034040128807400344194000d10039101c003010040071b0f4406a030300c010007110124016500b8051f19440c0010080c2c01d403044682c0160303c8018800c6803d0050888072082035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892048974 1250 892047724 892047757
    0xa0f0302030405060a1d06161112060f01030b090318010f0306090e010c120203070507030c08040e01060827060703111315020f07050a0506030720060601090e04110411 73
    0x720300d40000c500c602030a80001d20541942d40c407401c1095032300400c00d0741c01d1042034128404000039118030340050100c038010900c1f0300c404041c40d0340900d060700450f101c09451f40310400610520180084d100d500c203010300000d5240c40c4002440556101c840c465050610030385010307e504480c066044807000d001010410003075150b2400c4a18040c080e602104408550804244219040d1038001c0764800c01c260b445240c900115070350120382c0c1d1940310505480103c2c0a100100c3c80b100c418000f41c0c000d119036a907088240c103003d45880d92900e10881c1441d107166030341c004081c000402240b07281d07004415040005041000c40c9400c001c9114190055000500803034000c910a82ca13146503c01c045825800c661101302059061580d690315800b6a03640309460580400c007910700b0030021544402107142c4000c1c0005080c810340060101d00004400503081407003009101d50744a0040d000404034001c0c108440d04203a200c8910710031054038105d004070f440300c9414031803100c04400c5032403604c00c540410303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892050224 1250 892048974 892048987
    0x6080d03020a02030c0a1115030114060307110a050d0f0806101101060f080307030f05070b01030209060d05011b110d09050d0c0b0406050a121b0e0a080f0303010f0f080a0f030203040506 81
    0x10300c1f0480399150070342c401c0f0287c014099026150740c050701d058502c2900b00e1450229500100145904001c0460b81044a50440e28a0814041c01440c00c018864001040001452440035080e032074440074100400c9028810481c25565481b44120a03150a060400c05a4881c0700d200d80981460303040401000e016580004907154000000e0028078041e1782e82c28801071b441070381299188103403000685568101c10041c00546410b4049a40003000200a40302d207005959030300d42500d40c024501300c41d0220300700078020400d0f006010008128810700c05002240103031440644000d9083c01058040c0c4442400c00c8100f10440c10508050031500d051239407141e5a550300104203901400da40300008085591126a140d400d01940c000c40000e8850b00c09806180e080403151018180d4035903510091502c000612a034040c400e06002c2501080074682e25030516800210820043e48588001e103002c80e420480e050022840700d6020b0382c011001e14540c88941000c0785980540e0b00000d82c0f080000505 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892051474 1250 892050224 892050233
    0xa0b0a0c021e0a0803130e1e07050d0f0c110d1205090a170a02160e13150e0307021c020a121a100302040c0c031d0a08070e061306080d03020a02030c0a 66
    0x1c0c15811403e005401511911000340c0a54040291044c00010701c4044480580100f2328040c00c0e4048428074096042c04050a0040c0c15600d03402d0903020a00e641d61590b03044264014800400e902c403440c0103004074280110020807408000a0700241903949901140387d00034240442c00f00c9a030410001d40b900d83c213005410405a11a4141001610814040c1000201070141074000c98107000c01d480070581d10b1100c45030030180805001c90380544804100764402505108455a68100300c005507182d01e018414010b904140d4503500c4d15024401e0124001640c0da101c02c5070039601c402c2951818121245031040e201c000341007800d110704502204004d60101c40b00e2601d012240203c5003070184040b91001605c1080103284050005468003c80740000c00c04c9003030142c6c00b01800b611b034102c03541c1d494072400d043c19401d4214900c1d280e210360600c8074901e08083c3c001040c02180030200521890030700341c07507620200300740d10a060603000f254507907400b40240241d4083c000c40c40256182c50009291 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892052724 1250 892051474 892051477
    0x6020d0c1e050309090915160c080913060e011a0301030b04020409020d0b07020a23060a0213030b0c1b06010b0301120c03050a0b09010609110d09140d0e0a0b0a0c021e0a0803 76
    0x8001c10141380002503850740c54084030049106164990f4000c0340103548510743e00c3c0d071042c040ea5400080050cc0710307054035424428000105001c00c51001ca5504040300b001d0794039030488000d04a9541400144049400104c03d10f0300b05904540019961100c0c1c80411010f061484000e880101202c0c100440241c0205010461034860810402000412900d0a11a0380103117040400303540542c0000328413100326030003024030181c03c841d19041b9a030f482d41d8840c41008129a0440d02c02c80c04540d03032000e4052580c03406d072010031860103000b096041400720300590105208014441089921f100103000d900003845005e150410240c0300841090f00304450000010b44d1441e400350328107840002c00d0300c2a4442e100c00241040c806628041d02c0340140d402803c040001560745c00801d0f8410482064108026018680261102e8821141b11010807548070643d5000880e803034020000103d107540e010269035806c41c0c2c11a802d012140030030507148501e07a291226140c01c00451003010510210010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892053974 1250 892052724 892052743
    0x51f0803040608071e1d0406061101050a0608030a030c030213091e05060d02090a0e0304060c030311040f0521060903071b0b030612010f020406050406020d0c1e0503090909 75
    0x849990184e1070b000f50488044030203070184c010b8039100c1048002401c0c490018442d0400d04010700503c0c02442c44002404c903881a0b020702e01203800c06c180b000b00c040b4280161503000d86110700422038140b501e036101d44c1324441c42900030101503440000416040c06603060b01d606110036640ca400c0c80ea01e40b5900401096691651015081900c140b209000114000c1c5481850040c0c0601c6075a0465401e00501c440040c1010388219260082a1101d00f41040a0001880e07503903513101c0c01e0129409e02500301d0f5840da051444201c0c08010030301060000c12040070850b801a01c08886404540c030030000500c96107103180107140200401d10003401b5002010b005c0c000d000b50030031b8403032105202026101c0d038003920548403218020300014043d03142034241103d290803070b07000109405605d14002800c9904c2a0490404a4004039082c03051550402180300c5001550820340783c42c11640c1c80d0f903a404003105205281100040884008010017481662440740700a0305110881c01c00520722900c4400f40c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892055224 1250 892053974 892053977
    0x30503090105062e020316030f090b040f061101020c060906190902090103080f0c160e0906071e020c0901030606090e12090904020d0212010c090f030213051f08030406 73
    0x14022a10034034000900d0303481c2042103501c403e014416603013620041010070b62101d056000070b22114200d60b0317026074034201c41d5119a540c0c1484282c41c0f14040c1843e100ca8010070354140007844140f01d41e40890039100150380d11410f0007003080c0200c22159019105030702524070f0710701500c403c0c8000c032000020041c2c0524525030314002d40c0c020307046070003003100e0180401a40c06030403d0010400704125200800e01e00700c543e440c3c9403618981412207480c00d0368102481004202030308040010003403840031950407102c100080c0a0900300349000401080c40320880c800079204071641605518001c00a0300519503020300590300d25a900c2c10048000d10702c61043c0b14080d800e10040c2010800701041700c0026034500103810b401d2449500c00e0260306000104200d8000c1c5607c82d080e000350b6505810700170003150001c00440c880200e100c0041c40d071a1075911041120740100320078001651101c403c4280e0107161540068155503400b10840015041d44240e0320041a400c000700c2c0584005c0b00500543c0d0f8103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892056474 1250 892055224 892055231
    0x5131a09060a1808090105040803030903030406050c070f1103011508010204030c05041e0e070302120604061409030d0905070e0c0a020106060206100e0601110d030b0a050d03080424090305030901 85
    0x34074200005a0f445610f5202074000c000c1140b40014590700064090b05106240c06414680c4501d06146164000c0d500c542160b800802048200040703030040d0741d131114414040c5824804595645041a00c0040740189821f41894403045d55460950020001c10480303000007000ca551620003e000350310600003038814071044680400c1a041031b019207180d041141031003a07024020b1651031001804c0c134001c40c60543c01140e10000140e902e184940741c070083c040300944101d043c2071428900b21802600c20310350f00702000c81000318001c0d01100b074400d00c510800b00072071400d00d1860900e0030450030b0b82100303a00c4802e000c1807241e51406800580044549a0000c0000743d4480314180e0341e40404507056007e030320160742c06215150360b00319082e40154043c10305600761901c0486044c24465103142580000c1c1d0785040c80c1c0d44034a49104840001c20003920310684d844c0e000d44004080000080c40600b40c603051295603218182c49000c491030306440e280d0b082104184071b250080155000f613404603125801e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892057724 1250 892056474 892056481
    0x121809060a2414071211150a240623030c040302130e070e090d0905030d0806030a140a0b160228380c0d05131a0906 51
    0x91440ca560140c0300300ba0040007140300c4807811009039070521160041007140c20120310403c0e090341800307081c62521035400078051150741240100303030080a0380e41c0700b016440789101c02d1420b80c2d404409600010541c0002c241c030010407119000c50000300403040c2d034201b9245800603031309502030728154170344101500304005081004008007440c001a038580341b1214003000200b0061500d03540702820102c0c51000800c0d40c01c2035852007814010150f0081a865001502700b080c1a0002d128260604082e41441d910050030034001c81e0b135a560055000050011100100e00c450781d0030404003e03400c1d4007601c201100758078030076a07a48810708030004442c40d62181c0080307800e006d207149100e0800e0b1000e80c02003c040f0a000200d0100050b01001022458070b52103400c0c0101d043c88500c0c084002030090003001a40c0400840140d409108134621041382611703003801454065841103907107100c0c00c1007000c100c6441d4200a00c040d8161024006d101603041d00c500c0600b20a000c01840c414450a000d5410310380c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892058974 1250 892057724 892057729
    0x1b030f010302121506010c0321090210021b04020f0c0a03030c08010e010602190314040b040f090902090a0515100809010506060a050403140f0a031110090c0608060312180906 76
    0x207500700303130b20b0781ca503510600016800d500c2024003c221038001d240041d600c4540d1500001129031075501e0401140c0c035140031800b0350400c661580000318080c03000300002c14038030700315451708540850902d2080f42c0008000d140b80006100f135615442c1d84200340e0f00780412078a0080d00508809036401c022400310000020001622a4290b04031000c9401500d6a20710950006c4941d031031211013281030281d401c114250303400d0200040e01c0a8030b000e20380b440d56a402d001009001d2a05940111030841c2001c12660060300d030f9204040d00700112f40c1c000708003034540d94000c0f50a84c1d03508064070381000740c0c00181505107500120b207500408600d0020070542c2c50385014000c1c1d91241440e80000b24004000800c0040c2c050031440858042c8803003561225034018000c1c50402e9882e00c030903400956400342c03400c01f4000a120000c0386082d968000c10190391540e5031504441214410b0005101c41c103800194617880602c03407400f0345181d5102c03055948016001c0303007502000c0c1054103030090201c40b00050250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892060224 1250 892058974 892058983
    0x1801060e030706050406180f1502071401020c220519051305030f0c070b0f120a15030f060b0409080a03180b0a0902030a05030406031e0c080106081b030f01030212 71
    0x3c41469892034505070501741c0c150703495083c2910314000005401400150f40c030703003050f58102820300d21002e618400c2c03c0c0d0324028074042d100d40208003c0552204003100c036a8001489150349541a02d62500202d218010401000c501850035000d450400081150410311007a00c0850160008030070402a00c0710080d1074803204503588011308a40c401c0089007900f400d0140908407d00e401e00480b0074240e12120380072240d410003444480c106070085400300c42218010501035101e60b1001c41000703405000c01c48000000c651b032201900010381011568140181341c0c10008017102d0150082c40049560301e4840200d0744103400140000f071074900100e00742122014a4040e55420100801c01030f1030340000b92008100b80e510490303040c441e503c1c00700c00160060000d880280400d0320700240d51681e280d8090b03406901184100003d6191502903151150403101603030655005203040101903585c01d244581400e4598803e40380350380d0110401c01c0042e442054503058900c261b5413507450403030900d00c3c590348 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892061474 1250 892060224 892060229
    0x100f091a0411011227050c030f0604080f0d0c0f0906090501270e0901050a051e0711070801090507050301060608041a07031401080c030d0203030709120606051801060e0307 75
    0x686011090b00d0519610504041060103111031002a0741c092031142c0b60030000414464040000c0c15014002c2071141c24441040b40107070a401809003070a07100102c980350200100014242040481d10050440c40e540c03c3d20840054141d040110324110740010788070812100c015000641c8940010991920071700700750080f1007068452082d4030f020a40040300e030340f004182c00c00740c902061800003846800c0c0c082d05409501044000120f500309a4103c00035190000e1080c4103000c4824042502030303440119140e0300c5009840d1440c036458030b140c203590806115070b000d080c15600744000981800700c0030900c00111042280200b00e102d07a500825505400304440207001c840700e43c11003a000e403d96801e80c82e8007000b14540001e900005201000c01a0400c0e04000b0325a8800e200a03407150500f0403041c00510030900046003145056a002880b12007603005646070500f40a100404011450300400d0180900030442050081e520360b550350092024403c0b00000b07044400054014100401e400c0207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892062724 1250 892061474 892061483
    0xf051306051b012d0212040b1014060306120a020303031905060d08040b030a1812170423030f07060209091005100302030c07140d0e01050c1b0102100f091a04 69
    0x810401c0280d03401c0000c441350f4a030041e5000c00408405240a94a003441103100d01d40382c0d074044c00d0079015840b14501c030f50010f40c400083d64000440aa4820041d81c3e44650200c40d0410019454140c4a04010344803000a40521021060055042d843c3c0c0180c86403912000c000c200070396812080156a0103204c001910401040005000b18814207008551103000d185010402e80c0142e0f0780d4405d1012880b00035103001107407018568429038407200ba03d4828400511841c070605264036400c0640310800c4400c1c0c80a0072002126a480d8401e2083d02d4900d40040a00d44e00d840a505058020b50300c1a030001d440b41980c00c0004500c094500c40c7c41d01511009084461850707541d140a500941c40500910500c0006000140001d0385041032080b00030503010140864454058019041c568400c0c3c440303051010034000000104400500303a4098181d844410401c085031070010f03824109826030030980340d0308205c0301d034102440c0368100c102e40a1140c680b05021840b440805108017400f07071801003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892063974 1250 892062724 892062761
    0x2030d0201021b070e2d07020d1b11090a091b05010f02060f0a0203072c0118050924031c0206061008070804030e03101a1903030f051306051b01 63
    0x802804103144101506d1480e0031000c1c0303102c41c0d428010391191508907031640050b4008608030089561010b80c08039810058070b20201e08001c07541e6401001ca402280c401e01640781680040c003003101c1600050030458204401900e540e01e80c1442e6092600136000302c40c0441c00034210251400c0c400140640320f060b08003102125a10b5411660f4041c1d4805411042004038081e0242c1040c03041100e0010410710031480c818155420b54005042004030b0f0b1071880c12045c3c1d480c0700308101e0b12407503486a4440d10944030401c1d109114140318402440d10f00019400d0700c078680b0780f4400890000e4008000700c14035000c0364a0341d81d841c404c000001901d140c822000400c0e54002c920401e0251007043d42283c40f905110004000c4100440c0c030b0f104142c005042d89988450044042215409a0640580060380c5103400346c9203005042d500c2a00c135220007020000142c00b004041403085081e02d12005044c071410030b43c00d90380d07007000300150051101041445408144012083c005210319041c0005040c00e04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892065224 1250 892063974 892063981
    0x60a0e0a0b031918021002010e060a0b030a02010302090411130e01080a0c03020f01090e0c0405240a08190c03050109050a0b1c15060f0609060e0102120d0902030d0201021b070e 77
    0x100500a0488941601e00b920240900141d8591b01e400d1068002c40c1d00003d0800700c100552440c01d9800340c03050b10403a00e04035000c1502e46000ca540d00c285602070801598a09101001c14014000000982d020020100e44608500015060740080f28042d210110151340c948604036140e02501d44010b28141d50100200014100640c41144912050400c0400d41d40d4035400310005480898103c8660b00000405101f14074014415a41e000307102c03218102d8840091401445500c03031081200c080c01280340000c1c200034011028402901209801400b18565072003002c6d005d40700a0090404040c100800100a882c4611aa992040c0000c107049907003503a8011404001d5500441510483c0c0700850000309002d41d405010300500034842040302d15450000c0080c0ba042064004000b040b003403110501e1581e90000781001c070901c00c24502d995500054001a00600b401440203405015201c101e03105d058040d80071300b50445001a07258849030141a2258a5540d00e00030300c0402100f44012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892066474 1250 892065224 892065271
    0x5130b040311010e010c1427033a03021c0e0102091c0b2404020d06170a020a0b04033206040c09061401080601140405060a0e0a0b03 58
    0x80d0014002c1c100141c001241d1011242540c420b00341600c0a60746030461600060383c401c0c8228050b05280000350b043c0f620040711011050140c40c800d60046a4182c1c1c5550311b581c003030000c4191010648000340050052480c22540015451303020329820118001440d411402402141c1d9000d422052400c80f52107680c0409006000315440c031000c80d035003400050525202c880c0006007200314951844034070310032450101c2c43d1140c014009448001050038100f0258044082005081401c0368050b807511070747d0604078001d00065011034600510704508641d04000030804204032030095446841268613030300100024422844012311419448440c00f068003c131000b00c040d00000d6404100c001c1f48000041031034900295000e480d10b1280302c03c2080144c406214a2000f0b00c0080301a4403240322940c0080e1000c5d00040c22241840700410000300c00d0410b010455000c0c4c04001e003e01d480b013582c00d4009112410294280340113a000301008144000c3d428140c0e80f146035031040340c04031504900c0c0c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892067724 1250 892066474 892066493
    0xa05010605090619021212040501060927080f04141f02210f07031d04060302010f0503040507030b010b0a0e090c07080c0c0405070c0b06040504050c310b130513 70
    0x1105021400340e40410584081c0410013087c0c65241c6d4000380c425402d26051031030850b84944c1c05000d86a140682d44401000b2039941c60245412005a60190342c2241c10406602d124040d009000301000050203d440c000083e41480d41c000182d0312055100003002401180d00c4000e602200076901c1006041180848650046410800070f02c00900340114540c45482c05c0e0060001140852048800300720443c4000c9080407500310115810f01c403052039500064000c84110140d24100100000090140b040400a400081d07920483c0d404080d03035210703190f008036002981d15030000780403965440b0b41d91915490203401000b01440c158603000150303482a100e6801400342011074010b010014001e66654829203114500540317800d0345203c0e85281407030700b420000344150b02c10392a29043c4004580001f40c03070380300c240b401c4e40d48011505600c1000c00750906101c040d0b003600911a1021002d0302900d80285030318a0040d2140412283c42c00a51415205d00720307540409405c03490380600208800c00e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892068974 1250 892067724 892067767
    0xa05060f01201213031502041409040201110607082a0a0503060a1d060f062107020102040306050408042408060607020f06030703050402240904050603070b0c01050a050106050906 78
    0x2125503822400f800052240c0200b414509040d1040504005008541200c15040800a04114603090030000c030000c0d003820724020540070700700400c00a811039010701c108100c4801c4041c111034607880c000100504500045030307103840410142400340c89406040da9045450b504c02c018850605010034011181500018030540d40030301540740004118981c21120941030b80b0760054078100e49410420700044020020842e40601c80030000c400d4100880300e4061030720080110505810385440b5001ca000e03000399000901114901020b01082001c100000c0c030031204039401c0c000805c0086c00c10a80c00c42d03591904072010402c040d0010304075243c52401005864402068a00d01490001c00705640e604100d0f00e00300481c0e500c1c020720096140c03400152900b1921325291480c01e08000c08145620300a146c905070156440d80c000c02c0f02d6941c180f00900281c51901b8590391601090100680070f00000d50b50482c074031f444c01d40045140380c82001101c84d484000303070201e8900125440300179070f074503541c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892070224 1250 892068974 892069037
    0x3060d0201090e0a0e0c06160b15060a0c02030d05090109030b1f08100b0603130201080c070602030c1314100f020c030607021506032e110a080a05060f01 67
    0x1808041542044021100e000b0104d40e40c0004102c40100c4000f0b2902c5400b941c0700b842081c1c10300c1140c08640d01c040070041c03030543c00507503491281c5443d04606050310209070300e994407000214105404680c429100044a8000c80031200201003600341a2554800d03201c444e030000d16000b8040c030120781140c04494000030403a04001181828903d00d80ca08540c0390003429061708003d050284410090003a00b071001022980c4500c1c41c10428130044081d000301c40000d05000480b8002600e41806405692416822240c10340d980d00d0000b010b078506511080e108407c001429902040e00000d00012400c04c0c0d401904400c412494650144c0d41c690402c0b90000840c0f14060300d13040281c40c107100c6180030325400c0d0001c0143c105000c072107151b4280c00612131402030344400c072801800030108458102d6141c4a05003404544042003594024000040e000ba04008000401001c40c90f4403088092003244044001c0000b44c6521040141d1a14030500c098000768403501d00140804034007003800d50b8001203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892071474 1250 892070224 892070237
    0xc150c0c030d0b030f0d0207120c090c080402010801171b0607020301060b0c0f1f0221040305030609280203060a0e01080604231906090204140a06050105090603060d0201 74
    0x40ca012500d180d01076031800395890784944241e1107600381005413070004100343c809803000240d4240001d54641d01031113440c0d15041110980c0d828048100002c0c006440c980509004158075100081d11028007924100d001452501c00040d0403014650445040d251f4000038214041c6000e4610b910384010340465a8400c40c20031403803006030380074402e04004103404100562070f11112140e890828200c54220750f05904102c0f0b211078400203c80a00400d0310300b82c1401603c0d01200b074100b00c0010900c075408021403403c0c806200905421201551244a04465040541d40c403601c2c08000c038030401e00d421403c0440d5003404c0b0120813172a0091a0b0000d40a04201c00c0540d8605401c0c1c5002020f9000c2051a006401484240280e2260313200220145094907125030401d16012559580c1c90340c8d4640044040c0407005081180310f400034036015070001c000b4050300c0030403242403102250680300b841200b0728203000090994000d0003a2544110002d04040c03c51707032002e00384044613101c000b04070304100b00c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892072724 1250 892071474 892071487
    0x7030b070528030902030f010b010c0209180d031a0109122d0b04120903020603070c06021b010f0c09060512250504290711010c080a020a060b060c150c 66
    0x20081036a2902038043e034000c540c00d01140181400c2c040500464009130341480e003183c60302d980001c600c0340002e50545005d001c036640c101c0d194880345060110202d60780141c295510013254150050100d1114400d8120342a0300c02c5001966058558444d492410700300f00c0e41d01c00460f00c0ea0b441c207800601081c05400401c4151503d40342d0100b0500003c0f110351080e00c0501c400e00141c3c90040045120745e040445e040790540d0006642400000c00315010403550039455000c00c98950107460300e113490320101050021407031442c28080c07c890700d0f00d9610a4034002461110031300c107800745021030300c40c1e4440074580700d00c40d035080d0312441c1d0080112052000340052406c44120003088401c1d415216614903884600700081700000300a81c40c80071130510b03120044100807021003c1211040e5501400d6202c15078045d0380181d564400d03a003405010b0350404100070128540114014101038400c040802c504940703002004010b024046810f462a032002c04071200d480841240d80d50050040d1940e1303401c044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892073974 1250 892072724 892072777
    0x1005060c0705060409020a110f0c120c032e110904090f080a0e090702031216020a0b01150e04020315040203040507030c0906030c05010e0d061a04090507061107030b0705 74
    0x307111740d01454400e60b0001c0d04410007035200002074100c1d04007501a109103104000c80d15921403003100c00500c03c03040282d141c400242c0070840c1048021000d002ea5600c5549a440500001109268500000c10b0500081c07d4214070303104d0200c1080c1c4803114241407001050a12000305801c0302c084070220140c9907501c0219298001801d0094019513807501c1900009041c0900f22201401c4038065500601255126101d0b40710010350080075201940c031101e807051030480c81c000c442800030f02045003600c0040780b103802810300c1401940c1c450712000c141c1c0d24610280300c01c0b4401110300d41d2070440c000c05030040e945801e03001940c02c14000c0307084550f0b0503201d44030344140d100240d01c000780c0e045c3e450900700108204400064000c0c0000d090000902ca80000454140700e000007004009030f0b650710808035480d14480ca5031070f4040c1c02a10030070140584c1c0c80e14503a0b41d00980529070119480c0c0601c2a0b18410000d00c010682c0d50140f400280e0762101c46013aa1160007041c0d0205500d28220095040903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892075224 1250 892073974 892073977
    0xe03010e10020304050c0a0305030a0c0f0b0a0b01260429090c0f010807080a110d3603050406050a050f0f07031206150c05010b0a080604030e06031005060c070506 71
    0x2100c0000010f82d80d05251070a1840d04803480d800502903981c40b5000c1000c40c0002c000c3e6405c420650405e00041381042c41d10001f10740c1e4000b4001c010300b152100b480200c0c0c200e9406105911402c0c3c942c2c616010b100300d9034240003c0c8900010601e04c1c0403400040c005800040680c280040702031070791844440344030f0207080009003215124043d500420f032600c0c59207014009a100d40000703081a001e1420420001401c54500600c41e5007c680c894003020441d01c07400c1c0481c3c050b0005401e080040503c240c90b1703c511034450f0400e010084440c69603100700b40041102049403141d03d52201803400d4135010b0281d940c2e400030b10a190612005004050000c0c01010003001c00080c042003642e0f44264a1030301401045640c5601e820b19860a03801740107004841801d610360340001d092a41c5099030b00d2070107501400000014941200c4c82d13000002e0301190000d20305002c2d0740710f03807141d03204600804184291800100c6514041d609000303010405070400100902c1628800c070196521141c0719000304015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892076474 1250 892075224 892075243
    0xc01020903150f150d02040b0f040c2303010b0a120905070906080f0607271e0509070503040b131b03080306010306060201020c031207091d071b120e03010e 68
    0x2c0400c2d0001c01940510503102a64041203041103035070011200c4001c170f429110000b100a0003565030701c1809800ea40e07201e40304070000034020b00500040ca000e81009182440c2d010b00d0ba82c1d14000602584407240305a400d50f0305a4a805120504242c040c05e4100d030300944510307649035459a1082c146000c60300074400c200162a602e80c000c95044c1c07034001c005241c0300d2046513450a58201c44140040c1d1580311030085a00c5004a0148403d0010100302108080903540301c03041403c05d606404085005405194084a104488040269899100c2524184801c840c000d02c01c41d558000240504114440b00514a01400e2b460403c0e070540783c3e102007040300703e030415503c10001108101c1359691502074030010300203d20095003021307000038080d035581c0219481041080070000024a406100b0b8203480003c004503000d090310380305850140300d000701050382c0300800688404040c0070703402183d0a902090a5011031011181c00e81c40743c003201c82480f0092500e034075549500003135500000c1000200369 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892077724 1250 892076474 892076503
    0x170f060d0503190e031603171b070f0f1d0a0207150e0c0609060301030803060102010e1f151d0601020c0a0603141e01060f05090405040b0406050105040e0a080c01020903 74
    0x10f4240000250091005044a82c441c0e803164516990f0301458400c1070080740d030f00c00c08908644841048452a80c0613040310300d60240b5075003003012502c0c2d00000c1c2203c11a0500040403410700d44421081070380310524080c403140000c0350310100d2185880300800c203501c18002000181401d0050341c415101c41d00852002c102c09840306201e60f46e5202c00d00071107a02001c1100d6543c43c002c02d4002050f400d000511010303200003004400148541d00039040100e541d180e80045da4050f4080100ca9844450b112418082c00f5260003c040302003c105442d260a0b140184403086140071100a1a00c0340c80c402000c443c11805503280030031440c0c40f4444520007800c840d443c003240749507400c0c2c40000052002040f00003001d0900c44851641c0e42c9031018981581c0203807800180188041c20261034a1240801007504281381c03c0401080c058103044140c040c0e80308150510503643d07260100410f6850f007100209950b00641034410006890b0802007030b840300080d0025080964031070000307003030030060303204c050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892078974 1250 892077724 892077757
    0xa020d050a090b1602030c03190303090606050303042702072a0902041d130807021207080604120f0e130c12111b030a140a050706150503070501170f060d0503 69
    0x110b05d0140190000903006070000e01c41501ca09c1d8142e80d130b4058049010741450768404040080c0034460300198050480a01141d54981c0d4131900f03008941d030052011a517411700780c0f0f0302e1424080785000f150312440e00002e0700102c0000f0b40c0b114104074448a41c80c40388022010a0014040f501800948000c0445804454a403401c0861034410180000e20b60b40001c6d441c0003800e000643c3d41805e4030320060f0151804a1480b8140d01090b2501d0003030341184855102c0d5004000400c410b4000d40000703072280d0b9075a0384c81da14030401c00760b170101841541168400c154003080c0030034070203941c8a03400180d0700b45425441c4080e020204000c80d20800355010003003000081c000c0c0310b0903645003400c83c44686c9070011490412855801062180307818a00501e01c1030000b14044064411400d45501503000701c02082420901250b030103002c81b6521401e40079000d1020000340e25070045005088010090848502c59920a150460341480080c0840c1e07105100542100c0820350800c041d040c102048040078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892080224 1250 892078974 892079017
    0x120e06160e060301051809030c010504080d0606020c2101180510060e19020a140a0f020706030207053a020601140f010219111005030415020a020d050a090b 68
    0x41c06000103000550050300c0820041245032540504401c1c08078480394807111039101d10031203e045200b00c024142080d0b080906100c14000f0450003003000c415400c00401241d0360b145001d81c1c44586585503254000d0301720099403c8812043c401c10150b030501d41c0002540e5019041d07036104007800c40780a940b581d1041000100312600b030320810014115035014070103240b90150300000d010301c0030a02e85c003034150041014258903000382400700001c0008000316440c2c0320840802003103000300c01c903008010f118900d00028141c0c0240b0881d040c041d0018050418401c07111800c01c02c5034003070884140303060704d0100900c46500d200c4648103004492540908055413408101a00648024600350701c20303d4a4214050181e800040d03140c21b142e420102d135542c040603401c181d071080315020f00346a0000e100104001115a0210055210b244551000c08003001c0c2414200124007a190303080c00585d2065049041190081028019071041880d20500a0745c80b0000820142c010740801401c204100000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892081474 1250 892080224 892080227
    0x30308040b0105240d0b130902040f05061e030c090123011407022e020f0f0f2806020a200d0f030b030712050a120f0c0201120e0616 58
    0x110700400e0f08513012a6100601440c8100014036081081c85071400040c400050b1113041d001800080e200401000d500300780408180040e001800c4220b03c19864044030303282c0d0103940d2240350300441c005803051003511141e4241c02522003100004507454462031024580d10f56a890b000b5018288030f407090300040700322070014003510b00740e508040e06001e034440b05001060341e400142c403c00e80e011130340c0110f0092005c92505a140900c0040c42400c182c1c2440c03d001c3c0c03500000e2143c0980018811580035441c1c600105e601c60000c540c06605541000c2d549828850189414501440c000c21200c008059643d40c1c0408a9106140f000c01090180149241c1e09505104e070482e80b900301c0c800307410000c00e2020024011410307104008281a170fa10a003464a440810a00c401b41c900b101100480280a040c1580c4d180c20940f41201c0c0f07550807640d040d024901c2458100311004241d111a00c28206650040d142e89101000c0d204070643d503002c23071512900c0c04000c80e500414035483d4804030424030050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892082724 1250 892081474 892081493
    0x507050a090b0705030a0807110f010605131401050103050912030a0501150f0206010b0c16180e160303120b0d14060a060b0d020d1803030213050d020f010c14030403030804 75
    0x1002c605002d05000b0507021035008000c6400b502514a0701380083d60f22140203603030525100050202c184945100e898410505522035001e5410869018192000d904c100b401940d003c5100c4c610194141d100400455000e038200603000300d601c90135548a69201102c2428542007120501025501d8000410446031641d54541980715113160140d8007000140340607580744010710608902903000101d20f0a0382105100c140c0040c0390f668180072403565910004a82001d59140703880350103180003041d8806003c001044114040603d401640103032441c0c0301501c1e4402c003541c80c40c0c1500c0c2c9813240709489948106100c0d880f14441c40030a07488000050042c2e181041c000d1418100d0b600d0140305100c105041016100f80c200007400c091b81c1c5185440144c0c0c00740c40c51050002c4004070b103404500030075801d07030060300e80c0e40103200c88510b0803a5681d040100c120799441c4042d4004d0700c103a00d611000d5200d1a1207010a038014001d04000301d0425000910716449a401a030005412100b480300b04441d185 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892083974 1250 892082724 892082729
    0x1612030605040203090c0906010210150807050a0302010c08090103150305061608150d170c06011403150a0f091e05010501090c140a09050d0609020405060d08090607060204090507050a09 81
    0x2c40441c00c1d03143c2410101c0c5d441e4155055184668100400141281c0c03081140c0803180c000e091303040c41140301f8054240d5002282d0f000c0d101403802401008912402c10380310110031039405170f46903400b803921607c5400b1142e12070060390b8101510780708003507101d44001c1001c40003144504005c140f103180c031041e10400350f03d4220350141004426014007820340200810305603000300865003001c10083c203151150b07035460400d15100c040c80c00400d15156428010400604941c1c2200a8048000c076800070161507000d41400300e45000c02640200d285000b240c3e01000f1000b6800700000382c00c105584a01e201e04440c0c80c8a40d082212200b1003201304a028003401c1d004001145050220201400020301000050303c80381100c00400301c0d000c210b461140c0d01c160010280686803080b24007241c2000c4018240f209070681c0521b0509000c21202e00780303400035030031007900500c0301801c4c80701e41010400298051401941d80d150280004a0000320520401e4024985502c81035507030700c06080c01070606185035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892085224 1250 892083974 892083979
    0x2c0d03050c03071202070c080a12030c0203120702030904051f0b0c0c010c0224030115050a09030311030c01020d06050301050c070503030712060b0c0703050105090304050618061612030605 82
    0x11081c8800e015004095a8001100e0706010741e4404040c00c0710402400b03034150140c00820f141c03100203080c41000c01c800d52074078001c032801c1242d441d0500044e000c0c0d404003904140181e10401c6882e02036800c0c4600c080e0000c0300351060700d00e003000307000014043d90780645941c003044045800446004031403070000001032a28425443c1081c41c09810b1301d84031001102240e041c45802d105890841d5070380c0d00d1170307040d418440300243d05080d60703a0758804998009024201c044450030021801517401901680c840703420551341e203441c0506582e030481340c007000f50a020005200500585240c40002e001414642c060340f000015514a003400b010b09541e8003070003c0d1240380082001c00c01098003c01126400034042c00c14450301d0181c00d81d080010310b061341c000c0808800101c1d80702d1260201040070000c59000c0c4000b4003c50303c0d0701c3d14050b00c0e4030842c86040d502100802150000311039002c9a42c0000c02d0090042d07040401c01910b1480115040904071481d100c9030303440c031011640520800c005000c06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892086330 1106 892085224 892085231
    0x10b03030304112101054615060305060f1f0804020d0b073b041112070504060807090f14030120180907212c0d03 50
    0x1941c02541108000d1f201480e409241d00900200c81400c00302c00a60314900f101240080b5a20142d00c030300983c50703001d080c8864401c207010360024508e0351004038031480c000e0201300b00040d440700030b82c1c402e01840c2c60107c10301038408624481c04000d0304007400c068680d4000030b0500d502243c8010b082d2404442004150756201696020481c460391007040c00e603042c4181072020311900d800706a410b24011054454918080d00208000806401d521f0301d0000c1d40300d00d8280004085600303401003100081d0410940d039112104961008903494041141360814540c25804101c0780710b588814106c908400741c05503020b500000d417401d9801c600308684001040c01c035a6640104100c2072a070b00050003851441d0070005000303481283d40d50b440c21400e030805540038445504100c1522012a5104800d6520342d1351520320350192107448152540820034081c0f02071030101c4094280b0201802c = true := by decide +kernel

theorem cover : BRFrame.Cov 891906474 892086330 := by
  have h0 := BRFrame.cov_init 891906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891906474 ≤ n) (h2 : n < 892086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
