-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1906
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:06:45.81966+00:00
-- url     : https://prove2.me/submissions/4817da7b-986c-4c83-b783-be84236b83c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342625899 ≤ n < 342805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342627149 1250 342625899 342625931
    0x60b01050a082d07020114070305130201120e0304080a0506090d05070210170a0204170d050318033a0515061c020c01051909030516030c060618 63
    0x10748001e09403542e500741c0da80c015102074202040424204950303040b442090307581c500c40c80303018040c030304503400072a0b0001e907404000c1045c40041e10020400d0314107001c00c0803640781c5884d01e1540540c2460421021844c4690143c050241c0e03507100b000c0d034000000c1c00125260f0015444404500c00c3e4280d40c415907560b803603252112040150980030030401c001d00401440d1074901e07aa54051b05041011203030b851a00010002c140480b05001e803580d0006080c4000c1e0f160a2100440c0a80340004181c0b1070700184004040780006003c404c00010b003a82010002e400500039215608000c502d043d50007584502c9040c0c40b000004201e20448182c01142d410021003401400c0c410701d4201e1245960003000403d102ca294020310380c07581d001510a00000c3e111120f03000910381c6890b194004192401c0c2000b54072501800c041b00914002e2034940c4980010b40c118003a205904203140c00035600d0b0485007001d45941c020254000c0c5000c0c50b00c80f0101e82c60010241101c1401d1006c00100302c100c0009002003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342628399 1250 342627149 342627157
    0xc1106010623090303070b01181107120c0215131a07050d050a05041205030c06070c120c020d02190e09030a0909150f0b12060a03111908070e04060b0105 67
    0x1480b2106000c8064802da00d2003002055881c81c094202da10f003c0581d100d81e6031000c0c082c0c03c9031119841084003c58910708502550401c224000011480d1100e42d96607103034140f04910303c40c8240000d8400c508207540d80c103081e40101000d0031210700e540b52030718200ca020011403130141208450000c003580e24a00282c0c1c09540070301d80e10070000c00e01942d0501c415516034100b42594030810200300000708440481d0b822003590180f040d0015500da00340030500074280040203241c0c80400c020700940c54081611440c0303a01c00600f06041c88082c3c0c00880c00072451403c1001c070081d4000b41c00d801010b0610034603500e000304031512030b100054952030703032208183c4074401c41d0011400610020801d0004560651054103800e1701d00704d42c501c0c0c1070368030f254044c407019a0b42c1c0b0401114401142400c0074220702c5000a52101c01180c00442450540d134400f0321902c00b461505014075100e507030f02d103050b032506070ba090064405c0e0030032211010751300ca080507c1c103441103404407100390505020f200a075000350165 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342629649 1250 342628399 342628427
    0xd060f080309011116080109060b060f04090903020102190804030201052a0f0d15031b05060f0901020109140a020f100203030705130b070308060405100602070b0f09040c11060106 78
    0x19502d40940e03000110f8902401c816004000c2c010128520360180080403240d004203a65000418903101c1c80c103000045610001503940a888208041d91414031490201c0e002c1c0c2d82d00f080001519034560070100c2c0240a8507202c13024030141640301c000c0407500304c0c1c485031040341b090b4020300c00307503071110040650342d000803203280e11207050140c0b401495104800039000d00f0762007000c0c103030070000300c0403100082e1144d000c03101e018091411018000d020021955024006e074040070714140e40d1808011400c2485004070511090320003003001d0002c4e038400c1d0131200322603030065413031032189810f076150680700d150080e4202d00c219100b00c8404a14106a10b03845d05001c00ba402860465441060642d81c42d8000e280701c240000307000342c0105001d40410040c0003018000c0e41c405103c3c0c03900720144411100090b05001844411842c10001c0550004200b800d507040d0b0500c460b2100c0e00001061401d0280d8498180d0160411480a0b21130f58440020024851510b044803c03c0e41d80c0d03601907031030310904070507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342630899 1250 342629649 342629653
    0x1050313140d030204031505070909051314100c030504120c0309080f030915070506010902130503010203090a06150e0c0f04030b0709060306061d0d0501090203060c0d060f08 76
    0x340c1140000d04140a241c0c010480d0201018498282a0901d8007403140c000100e40e000c00c0600520401144210051085074020801400d11410140c1000854403410200d9616040040e90046c0c904a01c40005644140a40c3c4c030188640c107c1c03a00c0c1c01382c400e100c055145c42c24124000d954400e0140b20b0217103401c5911042400f020b41c1d011a00916505030540501103c01c200144154081010040250105003d1921145040100900c446048000d03c803551024050080460b034007140450440c1c03a400d81c01680c3e034181d0900c41c3e43c00500e0768081d540c154404400c00c020300202243c1d5194141c407960003001030000c04a1380d504c07030800900031190400d0024000a640c40d0754080106422101c8c440010708141d580e9840d080a030008880c0003000039007100c030030002e842d00350040320064a160705184003004000080c49200303030070a150142c403d02000d00004113221080d404401c8a03500507054507214035181200c3c5030940c2c442c507070380080320389030450004400c1109500d00084d114070b100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342632149 1250 342630899 342630901
    0x30c0302040b070b0403141801090506030402330c01050603060606030412030b1318050f0f030d0923060114040902010f0507210c0c08010204051f09090507031b020c010503 75
    0x1034070140b8030310040044003404a03401f80c08090078590800b5242410742e420626101003803240006151840540c40b050240310b0a0090000586d030b802c05900501c041e038074100305c00c4c00852219600da0703083d0301a051361034880042e032584940c1c010341156108640560450320346496000c04c0c030009100413580940600880c0c0c1e2603c0c1104c1c465040042048c800501c010304c0811108000c01c100e039490036071400c40405003e06201005130520008890850440103040c0d456502c010980e20b0b48a07100c0c2c2102542c0e940c403007803005c20514021b103005001c440d091201e2100500d070070841d41c801e0203014050b60701340c51102130744203458180141404035506940301260a011024240c985420100c1308540c0400711202c2d030807100011101003421804169680c2d0032810440c1451002400540c0281c5002c3e401040f00740116101e041000702c4154041002c4d480308250050111b51024103a04100a158104818010702d1640742c0c000d203000542e81611440e070700c080a0340036079036200e41c62995030210b80140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342633399 1250 342632149 342632153
    0x2010c02120109170403060506090601051813020309060709150c110d02100203091c0c03020f01120501060c020a0501020c0a170307020a030b0a1b0804080307090b070303060501030c0302040b07 84
    0x4105030035070110800001c208a8000e03921043d40b0900d000d5041054207003c1020000e10007180505508140151100c103002d04003e0002480c6100d40d13510307200311840e40e144807202c540f00c80b02400b9841140c40f000b1902e83c1005d0800e01d07182d100c02c0d203160380000c03070000c004101800c0ca080c010500c4046a10b400d0301c54091035880c1c111036001142c00c43c0c2d00c011094000700150711606015243c2940701d50103181e035061041d0800c1201d0510464280c1d0080c40c0f07090b401c5c000740c2400c604006a9404641c01c841180c00e80004840310301d400070390280d103141007070000030707245402c80302c8c0c41c2c01d0900c03c65500a00356112001237075a0020110950750140319582c0c1049280382d21102d207403061180000b5286013801a4022600310652075000300c1320340030b421040001c950344512400307101000070081c1d42004107008200800c0210013805c00303840c43d00004003180c51140200003140080c00c1c1c082d40741c1c1c0c070307070310582000b03401481e49100d018003003818603448000d00e03031181c4200d400f0303030304510045410a2215 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342634649 1250 342633399 342633409
    0x6120304061419020c090714030105090a0902060a092105060f06030115060e0a0801142d010b09040c0206090a11060c06040b01081605100f0207050919140402010c02 72
    0x1030318100510900c100b0840003221041070f1003040c0000c5a030010208000424140070003c82c00a1504c010002ca001c02d0015048510040b241141d00403240044035482e100d5140005001c0504025841400000d03607030101074006c5a4501103662901d2020340584e451405490683c003101c90041c19608000c000800f840f2000072080c3d0030500180001500d030b003100c0643c107901d00054002a0118000444562061800380c1034040a1700d080d0b00207100040c4005645401a00041e1004000102204d051480c80752440341c4510002080a0b100c10071f03580d21a01007203564030a0f40c40a01860a241d41d00f1000c1e400080d08a0240812400405452117640c4445403240c0303800302500d40c4001c08021402d166041084035a0250380a1070328038003903514103041c1e10f25280320b00898202d21105444208419900d03120b403011411100e0502c01112140700c0c20132428000035410099004885901b440444010b240401c20001074004003004015803400071076580c1a0100c60081c00070340c17005c400b08014100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342635899 1250 342634649 342634667
    0x10f03171602012001050709080f0a020102120f2523120a030906020309010621200621090106050301050c030a0c0512010303020a11012309180c040603050612030406 72
    0x3507003202c103504500a0b4107480c20341e101551f44000140e1205014891034005010801c01509003600410412316503074000f035111080404001d0304100007007440c0c108142c40008407810b03211040045040301c1c40c026020303003e041e5000000e481d00b21000c0f400904014152803081d030405c0a00000b0621046845004101640400038190801d41c03582c0c1302e040000c030980060350040e0403100c004901c450410f1100a540d0500203a492030100c0084400c00100e440d400c4001e5010f21100c00501801c42c0303100100350345206070307814411050f90084030051084034024200e0701902c04040240101075039442058203039581075990280000080001c01c80c541c5141e840301c6920482410564282620046403d00c2d0754030983c819400b5801240c5403c0422000840c514083c2009081161160b505031032a82140c1c00901018039203504000307a1701c1030540d40e10203c0e0a00c6100c0d007d400d0001d15181c80446600d40080c030841c8007181c20200498001d19080b440207516007058401941070620380b0000300e4280380c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342637149 1250 342635899 342635927
    0x102040617040c0b0d090b01080607020c03032803060b030f060f0f060f0d06080d080a1b0e040c1101020f0408070609080a0b100b0313050705010f02190c0b03010f0317160201 76
    0x11b41c44800400140b05182c1030b9000b0b1503040c002e4000f61500c000044d0a1a0f58000504e100f50410480403450350002c22000c4980303c0c140320b50701b02d4a1403000c4264010b202640042a80840c04400c0101e209000c8a0700c621070b042c144c3c0c800203041c0d00501404009880c4100d079a034001002e0051452403a9000302404480502c01808030300c4a40d181820307802c1551060b5200c000401007001c01c20040c07058000d42074441e8943c4002c114000c420040181075814603884d0038072494031110300c042c50300c1c07141190140b00c283c010000c641e10500c500c01c051a0b42d11901c1006407600504000240003070041c2c2240081700c00c0200a00340c1441c669803200e218020090070051f508142600c04101a114200078610444d4100e1001c00c5d1510a030800c14909510740c2e1215042040c8030720290b8a0a80c003052528583c1d405081e108003d841c540792001d04942d103a0400e0000b482c010000190041c4d52603800700c11a400303004070081c2100800e0038144030344151515180403074030000b40c106c0154072450040070112 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342638399 1250 342637149 342637151
    0x307060504080f070f05010e15040201050901120e030a11010603050a0209040609060c0e040b100905010f0504050402070c0e0106080c04050f040905010f0b12031c02160507080102040617040c0b0d 85
    0x43d004183d1002c584c120060554403824000030890400400740724018180310008010101c84c0560709503410f41e4800140300034100140400d4181c0e07180d01900c0d0300c030445400c012003413080c00203040c1c0041d80c81d00000c442c1000143d0750401d020500906105040075240c000020703050b001d03815001e000f1a1032004c2d00c212995a1754500d41000b2400034072444219407416540d0305031410a40d030801058498500d40c0310701c01e040c02d00d204911039400c0300d61103088480c00e00782141411a850b0088e1914010346d40490741040c0000f880d202003010103000c0c0800d9900c0c5414404050341c07510401c65040c502140c000d0702c03000b030421082c04185003188400b2000000107002140c000c0503030b5209429a42100d0f04080e0490b1034610103019850f00444000d1150306440045081410640b04c2003140b442274400c242e0364540c001850620105000650010103400c04100c41071159248005e6000f0750061040800183d220300c03074520030300025107016019980200604032001c1c2041219803243d4802440c00480c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342639649 1250 342638399 342638407
    0xd03110c0303010806100b0a1e02010605030a0f0303051b0405041515030f060803091e01021606090e0c0702010f140405040f1a15030106080702150411190602030706050408 75
    0x525040004501810304d207800b420380c5003801c07608403010064a400108840b1710074004107000a500429000700c1000950400c084444100d1041e401028a81c02250301401032001000500c03600c032041e403122621a81d006c029903990514213008180b190400e01e149480c04102c02c00c8986130640001a00241802c03004010590340c8112080001000342540b01190f10b1700c1c07100880502c18030a6030024200f4002561801030403500281444040b4845107443c070550280d40740080c1d100304100d1803200140001d41100710b4030b50310b000e07115034001d109180e0003800c3d0000245e005001c500036104002d40c1070311001882203800e07500341c4103454070004039515008248400905a5078601903d0341903900c05c000010a07070707100500d0703400b208120710495000c1c036001c06500d982500c526003180d044070003e140c84940d0f611166412420481008840c1440b020140b080c041030051192148007200c2c0c04982d203241140c07a404402c811601c42d44182c0b40540c0044c070004001c1001600800d911922981c180d501d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 342640899 1250 342639649 342639667
    0x4050913060f0e100f02031005040504050a08030108030310080d080c033d080a0f1b05031204060f080f0117030d0c0804020315060d0807031701031101140c0d0311 71
    0x1c5400c1203c110320598415044020510340600c0346070464005e00406500e180380280b9022182d501a220b5a40102e640e00001001c0c1711003888a00c0c038140c1c0c0078106550380c2d60350300e03400b41d62600103440401600b010b02900040c0c0c00d46c0003904c1c0170580c5032505d62007000e66600d0813036401508001c204080768400600ca034400e000c1103030110003074490300c2510745400155407200f440360325105421518659000d0740c005c8000c41c41401c80244c030389901c15080b03406001e40251140341019140c0c03000c2d8161040c00c00061170b4210280151060350802d0361048034075200e900086800c0d81d0240c4868810007e1800140b0114134807803c1c00092900c0002100e25140000d01110101c030341d0242c0d0580021249028081103140038081d00031794a110310701a40c00c6040034030010722440d10010340140003081c0003030754000701800b880700c04102d0740c158101d03c1141d6030340703040c062852402c9d0f03e5124009000100401a9a50b103a030030b0741d113402c003001d008250034580b00206134010507513600003500c952024030540728 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 342642149 1250 342640899 342640901
    0x50909030d0e0715080c03040224042601360b0a021206100e0907091706010e0a02210414030307091a04060c2307030807110604050913060f 61
    0x22001d4a2540100022460003a00300e010340750b01481300c420030501d401880b0b00d4002c61819680c206404458040001d0280c0310a04c04480341c2040e40c11940e00b02003030000716225075480400a4a00030103030280c010a0780301101d0300b2143c6043c00c2e90141c00202c003194500b4960b040358005400300340c085499014486d515445000c800c00c4411405040d000980c1e51035074041281c0c100d40103101901d802ca240049914042e1005d0310066002d400303400c0c00d6000609051041c0070000c000c020050f142014003800003150382c0c441d5400d00500340c40090700e80c0490b889014600c04c44082c4003c034480780c1080c0e44100c43c2002030007000f03403058500d072031524000444400d00b48000d501448050b00e80d500e8084c500240c2c051a403442c2560401007250030700c410003400360040500350b890b640c880707200300100f801c641c00004001102a0004e030035208141c00801007144140081910f14040c182500209440500b000064403a40c05003a4003d5448004510038100420440d48410300c1000e0114550307030400c80c000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 342643399 1250 342642149 342642161
    0x90c03030d15060306050604060305040507050d030c0506071407060216051501030515010f170708070816051f08181c0e03070b03060d0305041203080615030f01050909030d 75
    0x7007a241e691000100368030081c1100c0070003002c45003401d2049514290008940307000310f115a005041d100d50002e01009014001c0c4001f406c40101b10354054042410000c02c90040c548003280d05200b0000854111401024103048810074900064a4120140d85010182d000389001094a80304011030700006001404a0a07400c056404032a40c03961450400c1440c2c01c929044004094501c0401408010001c0706444150b13002140c4e041d201004503000c00307103050050343c040a954040d560b4082000a80407410a480c01d0b0200c404101141c1c0b540100401013002e01d85c25a120403944284034012400348100d90b5000036142e082002121000295a083c0100d100000070074070840d111a02c0039a401151120f0100702c10f40c020050141480c081c00e4040c840501128414603030032240720101031190b8100d5015008100d100c4018030034502d0042d180c14410f071143d611940c400d19004640074400416a0710880383c03251000c10b039900e070401f44406c203400034155482d1070004201e60840c00d00d441c041e003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 342644649 1250 342643399 342643417
    0xe0c07030c060518060c0c030f0304330b01080613090507031a010603060603090b07030b0a051504060305010b0703050f07060e0613051905060103150e150601201005090c0303 76
    0x10500c21030a451000d402d156000b0000850982c0622405141080000c10344401030109e4a8580da01d445908000b41040c4054080402224039512507007221105005007021449508030180705600b80301c00107483c4a2011522607811600c0140e1a00c1440e0641c0c0040300c6580c0110300f0744400c1612500d81428200c1c1c0c0464071502d500b0b16034010001075038944998001004245000c202e6141240e407a800ea4030400f420200415459aa0248080e5540120107005180c01000c03030350043c51400d0880030680040c0300d0100440d00c0c2400018458454000316044c440c3d06680e464a800134004454800b80c11006054400a54a85081c100054100903a03030140f04051200c0400c450240340180c90100d07252200d20340c50201810b920000303072001600a0550f540a001072000342ca85030000d000401036101350744070354402c464800f00094140c0d010640101d40c00c0e030396070008001c400c408102c529101c3c6070110141d07020038241000364010741e000c90342018240303050760480a032240010f07103950040b401c6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 342645899 1250 342644649 342644671
    0x19210e0d080702090105090f04020906030c100c020f0d080a030f0b13092003120c01020c010204170f070315050a0f32070c020d0f0f030806190e0c07030c0605 69
    0x1200b070562416404d42030040034102c7c0e214000303141170150900d1810024000901914085000c11060381d410b112000400c03201501c000c0749104900030040050132601d90036070103212a90040141400d018107404603083c1c006009a140c0070f1003030000c0300207002d400303030840900c1e80d0341c001ca1025980f0325031000d002500340c03400412102e104d800d0108408454442c0c4400c200c954072016619520003040840c242d0f003040d03040c070752143c10620006019109544115a29510000c0c000c0754140030041000b038480c0c503017000c580c0309115200001d55070740c4090102a0403950b1142d90700d07001c2c1c0c0039504280e0f40046a5040800c500039481448070503511588019200c0c0003812005844a4404500a82c20002541c00e80525814030450245c01a6280c0d0806806800c0601d14201400b02072041040310340e500c01e8416030005050f0800500c0d4803416500036214a5944a800009851681b1603409460320114a0398080e225038121941d1540300520031828040900303400d0300421558401e0314442c15000d14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 342647149 1250 342645899 342645907
    0x1f020d05060121090501020f040f0e0901290f030703050c0319020901140114030106030b040e01021e031f0e010305010c020a05150604020c0105090a0519210e0d08 71
    0x61400195803000300141e04101520b100001a055401c1c140f0900c0000504001003c0003d0300303180340640300b003905c000b05209000600082d001c5241042000f1603410395040c0201d51038640c1440c1c03c0c0c0d40c11a02410107a540f80341c0458488140c03641c06540340764000d122542c0301d031150300449e040043c01c2e070003520190050030410003035003021b100010340c580044040c20120410340e40003600341d820602840c0c21410f06c9040200782079001d201140411920100203070345030360b99024001c0252695042c0b240c00f807820882d12503c48481402541e45080031454a0301110150440301403103074000400450241400d4070418a00101909420380540040c0c002c904180d03055003003803402c0d00c00d425030b000210341c0300481400c04103d020410b4035480c0101054103203507481d040002001b80c010300403110007035442d0038240004d002e000100352100741d00c034400303581d0544410003040d6000d212003080030741400300d1011601d100724034801d081d030850b0300c19041480e020081140490300c503400301101151542d030001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 342648399 1250 342647149 342647167
    0x91503020f0108010e0f06120d020601080634030b060f090a0e06090f0c09120c19150507050309180a06090c0e010507021804050307061a0105070206070f0503160605010909030516051f02 81
    0x1100c0581c1c8803910002422110b803829000ca1142c0b52241c010a42050300e206420000300e04c690894110303000c004100300d071910181d4560340710340d0b4853030b25080380f00b00c9030b944e000901c0205016580d4854a0010480310341ca64031403141010b400c40040101a0051081140144940e00c8807011a004800900180a10a21041231001c6441038440703905800c0340032201000111400c03c0f4460242c1e0300c0c0d10342181c0710192480c11070320b50f00600e03a0007513001d06038604030007414a0b80c014851040314048000e01015030b1f250b41d841c085500d00c140346d20002d800c5001c19516035000303400510314940b0240034804482500600b150300300809440480d0b49400004001040c0900d0b4001d40d8130f4600c0a178090b1442003000c1d400030307045220700d2200a005101c00303d440c00903c01c210800110007908030061325a030b141c0c00c5c0304043c0502a03500085a1030380c948000450900d20b90302c07605200c50307415143c581c6044102c031042c0709041c04044c3c03b00c656101d40340321480200f8001450180c2100410300c05621900d00c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 342649649 1250 342648399 342648403
    0x91006120c080a0c0302240a1e090614090a03050601030f050f032b021902010227101815030510050418030807030204091503020f0108010e0f06120d02060108 69
    0xc0d070000000390300a844507400300c4e05449048007102d80c100c81304025501d40440d02c1051301c44180350940c3d2400c6c0800c01c035a013141c000714084140c444945021072a41c901d03000565490459000320400240850721060b500c040d11402010306180013402c00303030308540d03c0e40ea40b03140c080241c00032030b100c1c022811100c00704801001400d030024a104091800c0070018044030b040d01c2004038002004202241c3c1d140c1e0502c0c040d03812104d0044001c120030010408a01c2c0c0a8041d5006060b004820f00481d10072200626408046402d0350600400101000d00000d10440e1440009508600ca207480c103000040c030300b2101c0c01d4418101046440105461404c1c05250f1000f04641d4400e5004a05000202e482001d0b1111032103096a81800e05032900d4650b104120003d0141e074001070807403454482d540320245c104e01c02c0038041324800c4843d1114000e503507004484048082c86944038000b143c1020075002a10101881e03802607015150040098030214000c4c50801002d00502c007617044400184022601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 342650899 1250 342649649 342649673
    0x2071809030215010b1623010c020f030418050705090a06090603050f0702030304060c200c0307080f0714040908030c120708070c060b031608031206011b0b09100612 72
    0x200c01c1e0011442d600d80b08000f0528030480d030000c1c0911040c042c52004001d8100720f1f0b1120100e444403068083e004510005009000002c1240094885e651440c130151500200725406e5601d02407142c1005d80100b500d800c0a000041d05076807d004040c0000d0030961901014040200036560710841518581900501120006007003402090783d00c104104481c0d80010890f500030358050750000d0700d00d10b04c81040f1100c3d5224800c032140e04140c1104070b2248000010204d48001044058030940c541c1c0d191080d030303643e082c04071600752600b200004100000300c05034080e00701000644003148096040e910008140c0c400c588442d82c040700810203440d01d46030303402201e900118504007480103080c1820080c2a0381c03e9110000c01c0b540e00c0da16151096142031101065954a040c041c40c4090380b103500258880d040203540080001c1c03258002240b562240d04400c020703480c14440001d030021151281040700c0d4005011501c4c0d4403038118090821750030f0b44110001000308100505c038020103441c1c0140c0000c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 342652149 1250 342650899 342650923
    0x402121005010c0308010b1b100b130b100c0c0e010e1e040c12060e0a05010e0f010c1e051303120f020109020f12071d070806010c0c0312020718090302 66
    0x140f49102c80029802c00c5d030a03030641b00541c1c503441d21204001c008420141c101d1030380d40011b0003419611400240c2a0300003062400341203034000e40000300101c03004111000921801d83c420300102030007060704d028003030041049000700c40d00070311252240300c8020b0b1200c0a83c001003001c0080780420500c0c10145070417185295517412000c41ca03003400c2c0c40780d0104a071940950781002c600b01c089141049000d80c0869002a105001d81c0c139001201d0502c60300a0224a1703400c1402d001e001034070303000b03540706129222402c02c0303944900d99440101d051f030303945039014101c014061140821403c0062003040c0d078030100540c800c240d001140ba2101d5001042120000071071001e5a0503c01d1940050342c0301d128070035200000f51003015407640110090ba142010950045a80059000161224480d09541244504510744844007140c03034a00044071071079444c44018040e200c45044c01d00024042a84600c4c80003040c1c41100c91040e110701006c60740c4a407800d08441c0c40b40d654060311041603014010320745005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 342653399 1250 342652149 342652157
    0x1509060105030405060a050c13030c030309081603110105090301090f03020d020304081902010e10050c0c100507110301060f0f1503020703090b091306090c090e090d0c0c05040212100501 81
    0x428140d0b9402c0c5e0320340f0090034400819071100b0004401c5191601900c44003030607c4c645100380350b40c9041505440c4003034001900020072400010a980c00e000440401c2c41c402c00b94240c00c400d00c0c54482c2c0d4405820035024604000c0c00300014103103a5030074000c110200f4001c90310304615030035525010b40350281c020003000079504240410012508042420030014198412490420000380b00403a43c0707201452101c2c3e4440350399084490003d9211003d840103000842c00c0750721003848181003100d0b6031500c00d01c000015004021140015482d0300e6101490400503002240054030344160845074422500300c10110442041e080083c125410351290404055040440c41d0450a86009041900c14084d09001c1c03100022251a140c0700c0d000e244680c0704545900300402c640b621f4181c3c0c06405002142800164046004945042c2d60f20240340125070040082c040300035050303810380e202e440c4801e05030f640700700480000895445ea80024118104010700900325840c0080d1310003442c54503902310301c0c100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 342654649 1250 342653399 342653401
    0x60b0f0a0f0e101110240515030402240d090510060b040e041b0f08010b0901181116050f0d0215010b09040b0a030b01181a04020a17150906010503 64
    0x15242c10b2981d144203200c3d0301d80311818030600140a840c00000406100703100b450110094441001090b20f06640700f40e4810b11454655900d040001c601403051401200f640c040010a005141615128150050803ea1000c03d0420314105551036000203210405140e1285401c0c0204082480501c0c4124402c1700208801414405075400a01503805040e101034401400b24046c00f0300c40d00c101d500c105500210b8400140c880c1d410110b100c40e8dd103c0c444080d0b0804c0206084c80c130300940300d941a186010302c0c141041300744450300c00250200c2d101681001e18204030041f0010404030448549600a800412190b5152a15146061440f5030168115008a80b4440c1042408240241146c4010300980e4480d4142c000040080c420a000140c4c40b0034001c0c000020452202c198504a60441c4c000c0400d0760002c500c004103885c2207440024401d15040340e1800300d46019805400400c0035403901d101040040c1180020504050361b110209034030310420f003241468121070340355002b42c0a00c0d0142c25 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 342655899 1250 342654649 342654677
    0x150210060806011e0e04021017011e0902090906011b0203030d0209030d080c030c2505060f0105060405010e040c0504030218041104020f0d0519020f031005040b010f030906060b0f0a0f 80
    0x1c000d85c0640f000344500b07001081c0c0d06420307100340c03044072405c5c0b500001c403c950f507500e9840b541c0b44e07840000c1c1001a00345042001880803010300c26038000d000050310821403550b0f0f000044a005120404040c004d054904003030005d80c4080002c0e01450407098401a84c40c41c0032810546000982c00140040207640c0c810019101581e07804d4030340155802d8140c5448180c01250601d00b503a1080c2261034607020030070070006000f030000340341d4001c1d014000c00b02601d03600d6105010882c03040d806914081900410071800c5030526034000044400c9030b01d050f40c02c2984a0f070001d00d06214070600c141c548a1041b091100744140b01c03078071050000302245c0840c504494204501024040d031028040030a580f500040e804c0783e20100400c000a00c03c030004c5555011b03045070009550401d4907401c0c10204000d5010409080901c50b046004030140c6801d0701611664000310080c15200100301c40b459214100050081041e0001d020583d500508a9413129804400108805001107500e01000025182440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 342657149 1250 342655899 342655919
    0x7020a031403120a0c09050307150809100e1f020403020a0e0601090b0a020307140f031209030c100501060e010306032f0a0906082104150210060806011e 67
    0x216035200c8545107214245180a40c25401410600e100b0044070000300401c0140941c0620201c00d100e4458905040c1c8a1040c0741d41d0300020701605d40320301140d45000705040d004103807080d80720a556080300c0070203010400d11000c2c0e41d000007954420b13900c181a100002504d01c0f102c8500c00c41c14802c2141418955000102520b5061081220224110000c14500d03480f40400c2d81c06042c030102107543e24809000000e54130b90214800b601d012445c110b1041003c40c0101d110725800c6100c0000714280004030918060542001d004000548010401c030087c1c40d0081c0010a041141c5450000d00c542c500b6030b01030308030310039004a14101440c09070207200141e091040d640007810300c249100d40701c819600341e00605d0400c1038491680480c40c8807000441c0314051b00f0050580324040191030b101903054882600340c912040020b240900244024000c10149080c020f04004040c070455240b0303140d4040040c22103a06070040845e81e0004d000500c440b80d01c40c42900116260059140120780c82c100440d2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 342658399 1250 342657149 342657169
    0x3030f0206070e100c0228050405060603040204180512040905010608190b03071a09030c06131a040306052e0b1c020f12070212030f0f040201210f0e030702 68
    0x30b0312519101c100099020302c10140c010300307154081c000ca0306000b9840c00c1c1c04200541f01043d52202400c140c2d01251a0500e8020180140c802400060035a201c80c8c1c00c10000d4900d50343c40185803040d008025000c2041000503080ca046580b0106070f0f034600b488070030001e451050b0403000c1807000207014420610081141c8000f0520003100000350303403510500003410724440307a210006001c44585459074200041c4001c00b40d00b84200c044403164159002409940c0c0140340e80c0d0000c10784004010001401d40403040141e504e41404003925080d22a0b461a00311882542e1890b202903100740440004404d5000c40d80081c0380c8441014144c074600b06039001e4a00c0b5000a090040710805a070007032405044e01603401941c43c0020982e160400d44514180d0903104862250052044040680c0c58510030b8080740c1c0110800ca02010459468a5101c5580707000600700b01c0c104a034244084400d28a00d4154180310307480c0003004560b5804615400080e500c0f5a80d0492403508100300c7c80700180e80b401c0d000c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 342659649 1250 342658399 342658427
    0x9100e0303061504080a080c0f060c0708030406020d051306050c190509030c03120d050c0304020a2904120201090510090e041103060a0b130c05090d060f0905060103030f020607 77
    0x10f403441540c6942c42ca419005030f920417002da00c516901c2c42c00b00b10100e0f0280c000501d4800032906501e02002c01070755503000641e42c8400028042010700301090201d401550320901429000d440c000b0542500403c41d00308541c09c0501c4101440f52008100060040d6031b0000c1e0241002e034200300c1d107404c990b0070310350094900400340a0006a00c03419134405001051804400030306071001004145c680003030603405078420398000e40c07801c0002142c000d103450a4074021364001d0542c210450034090700a00303a002608481240c8440707140c0d44001041240c1c014400b4002107400c110b4403044a10014003a0007035904440e1042e5041d14068990f242c0c0450070004980c010219240c0f80d44850a1012100103902d120301e4160060008020900b84c89803c42c030301c030450a07110542401c08140d1000304030b690310b0200e8030016408003c491030320310740134100c409094000c820000b800031890554400725440b0b503608943d59081000104149508500000d102465a002070100d80c5001c9000501c400c50134088 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 342660899 1250 342659649 342659659
    0x60503010f1413050708160f061e0f03021201030c080c060309060f0606071202010218040213182702010305180712081c0b03012007020402090f0d03050309100e030306 73
    0x10f148203000c01005103030010120103055400c94000c0d541591401a0140181d05884083c000b0004d0824800c24004920300100f803441102d40c6200b46c402c949003512560600b0426400f480300d40e51003003501e44200c1c000c5104400b01c0720864034011000d4204000b8900c124407a410600400c0b003e00c1c004038a481c1e01005901d0304085559584c40064070500071500c003d040b411110002c44007440d0154010140d0b640e20b040c2c039404051150781040184c0c410689203804400c100001046010760010720a1241e1240c0360000ca4803084c0100d40840d0500c0d482d40c0e800d00320402c0c010510542d40c1500c01d00da007000e00c49400314a00e2000034030003556080541300e400705904018034a5402d20a00c0016100c0d440c08030380c4003003c2502d14980d480003802442c40c100e40b09502c2c2c031065546800040702000d643c4003240000c82c0c103100741074003000000c3d044210001d40029290b80100300e280e6401d05035102e018400d4032401d440e400c169050074a04040c00086402c0986403413194201680000103513981300a040790 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 342662149 1250 342660899 342660931
    0x614060306062802240115080603120c060a23150117090a110103021c180b04150b040501030206030a0b010e121e060606030106050d060503030409060503010f14 70
    0x20300c144090083c91110741103c3c1c03403c4a650807a58007040c903100101c4200c1170301100c4400d030f03408214035080a22a0569207003820100c03204190040ea900ca500c480010181c4d8180c1006c0760254020340d00c00c43c80410a03800c207a0400c0b403401c02a2050140f0a0000795400c01d13440701003040858105c00281155040d0b00b181800c90b00030741e1048407050100303024140450a2801c0900d42c82c0d65524403071108462030101203c1c4609594441d02c00d840d080240b04080030707000c0c242104420001d00401030f5084490303d07042d0900000c1420f0000e001c1c0160b125002020103810240418001c50b20108406031065007440c0041016a4070601540d80180710f4500c001488107040b00181c594800341c0c25800e40202c030300c030a10701440c10003040c440301400c2c0e07200d0800b40410f24080b10a4a5900c201c4489505c00c50600040c071260380b1650291144109401001131290344540001c2e186400507403100410945035501449a0b090030b0150700070b88003000000788400d2408151510a00000828440e4414a255 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 342663399 1250 342662149 342662167
    0x23010501170c16080408010e0d230c0d0f02071a0414040b0411031e010302030d05090315011401110303040309060819060b091804030c082a0a06061406030606 69
    0x1400716001000d00030841000e903c09841d14803c950018412480e84c0d502c4d00c50000b5100c00081100c00481046503105500c0c5c1d00c84030f2a40003e41d40c0c8450040e000c3e6030521101c044203904000a0007151041c3c2c64a00c1c5405000c2c07002441c000382504030440440304902c1c04191a1000d8050f80c05482d120b552409040d0704500116004000b05260182d00070b040c0140d40c0d909030005401940102201502c030040502044807002e88140c0c00e22009400d580a2f07460700368018800c030043c150652000301a21035048035030f0741c81d844030b210a8004d41450006254001101d41c0c00061180200c046c6034080c42c1580b5003034801604440f01c1e4844c040900c24080300060042035034210310308540304020b07070412540c1e031200c807000c0c8142c01500c4141c0c010051000d140c1c1089814500140c840d65040e0303200e00c000d11036907607400d40b250408103d410051241044550460740b03e000c400ca407015480c40104808002da0610b20250f4035660b0088040a00c2824400803a403251811a58017130310541e41c10b55914010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 342664649 1250 342663399 342663421
    0xb060c0d080a0908070b040209010617061c0f060506010915020c010e0f030307060510051c06022503170a06050604050f0310021209060106031a0f0a08060a2301050117 73
    0x15650084c21a5030018004081205200d4094007030343c02950b00c0c5800342e803a000240d40a84860303442103100255000042c2891400c44c1d80707408841c442480744e031201d0306039035074186800c40143c03402c40c0d145841d64200816541e00031884d00041c17400c410200c025440b01c00307010792101c0309a001d003810410780306195441ea03102c0d4001a00c0c00700028048960383c464505023040100802e903016a088030f81c2d060001031524241100c200c0d50107038001240000d4000d50348020095100d082c3e0016004a4960031800d00b54150a404220034040e849220b600c000c0ca801100c1c802c01c0042a4078000352400d9020b010720384808003514242c4500f5921602c41c0068140041c1c684041c01092150305800055251031f03800701c02161501540c801c0007250500e07629054143c0070b4a140d00d070080e140d008001e0300006649401c0040e0000d05001a03c110f401a480307440143c1480c2040354005202c030b484417051461000011030300c02440d219904000520b504180c0028000c035450000302075281082804607050b0802c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 342665899 1250 342664649 342664661
    0x1020c06090d031e0203040f0801090507061805030304030803010e070f0e06090301020d0608071505183001051f120b0405030408010207030f030c02010b13020c010b0d0507090b060c0d080a 82
    0x203a0201c40c0c20304c3d0400c0c00025583e610034060301c9801e200100340042c500390140103a100569000c8058080f013410300310708551079a0300e0f96032000345046101c40043e441d01c090000700091401007580c1a625030400710020201c240240642040110144409107150360104092000340021905140d4427941600007034003a004030312920a040740f400700c0c0000c51100c001013071720849150302001141a04908802d4400b80903080f43d01ca4200d9413600c02c0d0700185050301d4040b441ca071125a0701c2ca0100444030504012400c004500d40c003031780d581c905020081481c0714205440305031003c1494245c2d4140015009010313800e4000824030203008012404204d82442940c0140c51003100840d01d82c2c1d41c2d41001801000c078489a0008285070101c0d1000c8244180103210781041d01810b900003030551201003070002d52040700c10319a903541c0c0700c003c401655901120141d01034003800003441d1150903c80381500b1a441904030780c1c400c0700300300021410010045200003244540d401d0801d01d42e42c61000401c01303055 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 342667149 1250 342665899 342665927
    0x14131a070e09090606010212120105010305040213150609270506120a1b0f120f0206160605060a0b040503190309050909161406040512101407020c01020c06090d03 71
    0x2002104004845100240285c03013142d00b6800c4500801c0f048884a40c2449400d0f000c009089002006100300e5000390043c1d41c10500c00751814a03020b6980b120001250668000d503402d0540d490020030066030301116810181124485200c100e041000a2010b10964024a001000d855200103222592041140c0c6e03100c06034101039803412441894407110306805500050303034800b45420013280340c03903440019905a620f0b400c01c059400c09075403151269070030446022603000b142000141d2600303150a0581000611400300407030a4203108003013044017500c0f81c014410f00c44007440200203560300083d80c520400c00740401a00229418101142c0030099500542e0b04800d90301c0a201e090580001c4c00c26529400c9070540000030b84441c41e0100303d13500c40ba1219448a4140014012403502c02400585140c516080301c8100e40c81612290a82d2000400030080e0102c0c12308100880341c050180680c0e0708000d1019081682590300014058000d42c0e0410b401040ca4440541c10075000388044a0050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 342668399 1250 342667149 342667159
    0x90307030b040c080d11060903040e0c071b1403070b03070f08150306070f08060d11120c040c02010e19020904172803151805060a030c030614131a070e 66
    0x7040c1714001912071a40c080e900715480c460480001d94809000c400e490a0b05c140c109000b031207888603200c419070b941040300c050700d4440d590210f504101c503c1030082d9000b01022000e00890101d101c04050921301c0c0e982c0141000c090800801c03074000d602c00703007109030780758142001c1c1c80507100c1003424070b9074075001164103425125200038801e0441d0040c5164442518655a51210748c1d151814403100010744032000f03010860031450295185000140840812040c104035030000c90004000b4013030381c038098441c00260350345000749404a00144400c41038a030501540c400c2c0c40c1d840d5404252128801000900078290301c0312808030300107043c0c1c12680740c444c9102c1c3c1951403c02111070360241c10400703000b4130b01083c5002e400807000740007900481c1c21550000c2440711241c064034141e4003e008d005000c2640040c4440005c80080c80c5526420082c0d4021400003600c500c807041d40c0c24010303802514203420b41c40c0b04d9a2a4000078000c020312080504c0410000100380c851400c240e521050f000d08566101f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 342669649 1250 342668399 342668413
    0xa0c0503040608060901230f1315032307090c050904090b010e010807030b0a0207020a030510061d25120216120c0210110a080703020d0212090307030b040c08 69
    0x8243d0000da071074001c4000301d03400b000a90307035811130340b003a180038050702100d882c00c40c0c028550b245400b5030301d00300340d090151142c0552002458110304441c503e0640d494003403500e00c0c0500500120744a90885000002e1406821040c0e43c0d8880d07a4030f0280707102e00001c403502c03800c90061481c42031040d2082d008010b4070522244440313141c8240615400d0250300400b44000b400000c52440c00030309036040700d03042903040403079031640c1d40704001941c00740310141d0b00400401000000218100020b40c064124114009400c07400c00700008044240d951407254100800070610500070325100e0f030002d0340c02d1072440d01010b6084000e01a15031480c0d2461001941e072011448a52481440080b00035952103441403a191110030300301034401404005001e504220648881c03130300c0e50b0090300540810241030782100d0006280707580d4026141e103c91411001a08070381d40710340c90907804020610807182001104c900380032040307000c01d980c3e03480e41c48043d00080c00301001c20140007204200c03c0240408200392649 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 342670899 1250 342669649 342669659
    0x2091b0f270603100b03060a120f030206150901170c09130201140711130608030a0f0e030601080d030f02090a120c0f080a08090415090c020d0206011401050a0c050304 73
    0x340c070085032051909141c0d200e1140186030007412a84107142d50b4400e20700c580e0401c2805c0035690401844150002d400080204110442c00c0500c1d07105840707900821014001454000c1c14000c000e40074000195a06528865030f6548403a001e0541d4044503032004440c0c03041000714071b041c0340301030010b800c907010405021034038400d2444041d1250003a21106802d0308010b0031040503100f580005403803081f10107a1080145895020031181e0350010300301198281e00c2c4c113076080c115488000075001280c44148a06c001c641c01810048500030b08174080c003c0c56140c0802030351590300c840c51403001c152355000c410b075590030780d40c1c16a1804071003e08018400b945440712482c025102e524147c40f1000000800540500784030750760000c0e00c2000e409040483c80d19502d86150340c000b00c480d9940b143d203c203821428583c03c44c4403c0c0040509450205984200c1840641801040c0700203008540081d001444404e05441808020742c5003031030715170b0b52006141d8040350301031004031000f03015000009002075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 342672149 1250 342670899 342670927
    0x140403050306040606050408031602010507150609060e0906041b0b040f090e03070305090613120c062a0215090a0305010606020624040c0e030a080d140402091b0f 71
    0x1220b0601030b10304028650700d48005552501035482540c4030341d0304c20020131400c0d181c448800c0d514240b06050403400c02030642d40d9000300c51030703110380008400d035685010030049000f40503030380042c000f26201008604050003a00e031600001030014107803152025609152524545890000b000440d15868070b03240c40304281d80401d130403480344400c45420010348581241b00801150f58040e8507407600f030316000e801011301c42280c01145165144460700400060100c042d1114044501e124918050f11941003800c05050a030030030811504161f07207001c3c0f0f480d5024890041c030210b680c04813003003600d088030000d60740850300c5812146034000c800108000204201500040300351000c2d5020f648080c0e83c5d00f001e240000e004444608070500c02e00554800d641015030001c03800202e58034200c1c80c041c15100120b880c1a06074281180c180c80c0c00038459a542045104454030203801d00e20301645400c03c1d40001e00551000f60040201d10503803481048a150f0301000c883c0d07500d03140b1101d95140c040315200c0c2c03d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 342673399 1250 342672149 342672151
    0x10091107200307090b24070f05010f0e03190509060409020d02040305120304060605060a1205070c0615091a10080702030d0501030c05011101050108210f0c1e010c02070501030f1404030503 82
    0x907001b6a81d0310700c05c80103075155520342c182100c01a40e0352828441a45c44058401d2881001981c065588029201c0000203034001c44e100c0d0590000155a01c41c09a02440c509400481c02c0d8805c0100601620105680e8a000c40c0c049813083d80c800350300c5500c80d182102c02403190f544000c00c1c911035490480300c401d42c040041c41c45103004180c100113656442c424064688103440a880001e55009950b4802d04860742c046070b00302c02a0310b02040407155981c0c405080f210070a4200404d001c007804104541601401820028200a1070143c02d40d41080d01140c04000300e41040828440c0d46400a2030043c403c0090310b021100a00c403d00007940d4030700784403464580502170280051070340701041e40d20388414002d00703048601810040c0f403224640c4081c1500d920840d001c14104603010400e1165003030802000c0c080c00428903003e4080525681d0b01212a080e00110f40b0f0840e074104403002000b5034000c101c02c41241d100382008601e030a01000110001e010710083d031101c021070f2806020515502c00c02039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 342674649 1250 342673399 342673421
    0x40f06030f02190e040f050a0c060207090e03040f03020105070305070b0c040306050c130317120a05250c02090a020f0a0e091012110a0e010e1009110720030709 70
    0xb543e402c0000005205008200c4c020007104100c40004280041e2a0044119445000c1c4003076400c0295155510008448e82d9409180140c2c07001206100305412841251b020004000046103007528060003602a90107901c0068144000800d4480a1500035000c503041954020000c0045241a15015a590b000b0f0700096802a180c0030001d0b03542113540d400c0f60300e200381002500400c18955078501000340c0d040e05c00c2c501c1545061018600b0b040400001c01c0c00380a80302c40101d801d10301807501201d40340d18240703603e01e034900c1d50402170341c41500301107060f0400340c0548840e11a6543c45070444040d1182c424000350412001031030b14100caa10488050800b8401c8507a0030480d2514a0344004c0d43c80c15010341a45150041e0304a000181e9034100d800a450000d410804420f0fa6040050303c0300b10300761321600307684140900704061800c0140e4024090803d0403c20402d2191400030b002d0742e401480d00007801d01c0d210380c800045403152524000801c0c4401000c4408081d114100030014145404138 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 342675899 1250 342674649 342674659
    0x3010f06021005040209150406050d050f010c020307020d17040b04031b240305090f06090a0c050409030e0f120616030e0303011518052106090c010207090b040f06030f02 74
    0x4014002d207a9409640c0c062a00245406190303103071105004440c100001c0710390f0784142d403204c000405884150350035114034007400c0605005000460a10309442003e102d16045400402041005a030366529000100741c00a851001000414154140074825500308803690b45d00450000700300301902660300308250015440d511082d5035802c0b200c0e01c0c0001142d810f020240300c100e0440c02d00d403190703100685c403a0082d81294500203d041800d07044c005c00380c0b08030b82c10341c200503c881d06102d400c40320000140b00545003048208217946000b82041802c5c6680c0e0310450a00380c69040e59691140d0501b0400681416108582041001b10401602010743c00300440d007003094000000e200807096904a90340b407445041f861036032850488410a00d21100004000703035140100d0140c0761400a9101c006250880003007040340d648403203140c580e0040c01c034506a803000601c00c0c03180e6800f280071812a03141d100c001c100345001e0000180035201907440e00901a24004000050106003e00201c0395070090318 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 342677149 1250 342675899 342675913
    0x11070609051603080a030e0712050601150e30100509011a15030403090b030408090411031b0a030e0f030901110303010815100b22060e091b0c0303010f0602 68
    0x45070840b00d000910002c2c11040041c0042603034203019030403082000300b201050f6108191521514030090800f0b0b482601e0941c0083c00501c00c1082d0000a03420300d40c05400d10721020141c400004000042c6020800c0a12034500f240041c11000c4024000a28680e03409a41c0d81e03100c00407600c00144002c1320440c405609081da2001e23016481103440180c024090865800c402c8508c00030201544040d1084040201035280010110a21000b56008911072010381e56030756612010041641c2810740c104d200d03440100188106803090ce91307120000715404140580f1001004419002070030040000076040c0118001201386400c044001c0c46040b40c00d881e4074203911481c41d5229a240400d00401c1c071aa40305c0c402e82802c1c4040184065405160090401c0165440340134408294001058040b0800081c84000e2000c2602401c0d51002c1c041601d00040700358032180c001956070b400a010081500d604e1a5010504100c248c119049220801c007226641e5070b580c0d80c0c081865070548039034401405401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 342678399 1250 342677149 342677173
    0x9030a051507090609260f0610230f01030e03040602071706010602060c030402130603081b06090c13020409050c0c010c02010c0c02121c0903021201050103030f050309011107060905 79
    0x20042503815641e56242028209041108071808400e042506e030b400001c0c9881c0031a2042141241003210b072405042c6078100350144501c0600079400c122410501d880c80000c5041070034500c001c04860481e81a910300d1031340c0005800410700001c25107414040002c000c0b403642d40000d0302c4012690141d01e9010718a08030900c4903210b00b000c0c00344000517080100880c0b101d4804c2400786400500040c140445803400f0758082080b146250b00480780d6120100d040e003480002280c041481c0429503010f004a842c040c4a0701d0349945550b01c0451041e0050710940f0118242a4103440142c2491a8204101c0c18049110400794010b0100c0301c13029030030300c2600d07108988180515204600c0c1380d1580044840554200800c2040c40c0060720344a103c2c41c90702460100444e580c0014407415070b107401d4200d5045005001c00240e2101d2050081e83c1410010000a80e2118071042c20081c145400ba403240c507003180c41c9014000484e08414007420200d0648180221684100e01d110710820072903034403031459 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 342679649 1250 342678399 342678407
    0x311030c250e01090609180b130305040306050c19020a05060f1806070302090f0103150308070f05150609070f0f140d0f060f0602030301240509030a051507 68
    0xa041050410381040780d03000000d20080d281100d411020100000074030740c6614025400c054240c2c0210211510741e041000b40c440c152140700200380201c43c014508102c03645540e21907080c00340403004035004902c485818107101d84141c401030345e403100c402d02603418039204142d4070750000085070300c1d0000500d051f03a12890001440c0daa05560100242c50303240c3c1e070902038110f09200185240d1170242c01e140441c0d100c540c00c1c07103400d20404903a1030058862503800c00348080c4ca403031420850b040c1031820ba80b04880c1541d2061800c112a40007800c1591501285030450803d0f82881d00100207104002255545410403202d043c440e5009446c100c1e250b81d03030380b10f044840381a12086200410709410600c00c109102d1000004020038000010307290000c00d40240048440e455030000d4850341d6424140301c505000a003c030000c04082c401503080d941002ea42044d82a407210210783c201ea501c070581c42c0540e0090701620301d00074005003170315450100c1e41030080c0c64803400000ca410711a140c0740051860303401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 342680899 1250 342679649 342679657
    0x1201080c1903080702040f0207030c0507170316020a0806041101080c040605090d110a03051f05071b020117070503041101050a020d0302070f02100207090f05060d060c1218031103 78
    0x70012840301814950f4076540e1195210300420390b0002d8030f800601000c4030f907a000030030100b4071990303404803601040c2c1061814110590070030040148100f600c1080c1002c00401d071108003842d5503045403c0f410794400a800500e280d4024120382c010030302081b050104803112044014401e032101e00b031640d2004000403042c03059000d14000f1600c140010611400d2104031758580700d205151280d0381c200c1b0600051141c4207280d000f1245903101c650700c800d15000621104410412551040c000d43c18619006000d81c5010824100e10054405a80040d684141d4660662201400b07a2100d43c1c107105d40c0090882c1d02c120707030a8071102c0154000303960075403181c070807140080b03620b0b80038007004100390500702c019620903002660f05201d40302000c8056603c00042059050303039074000b40003145c6800807010030365410400409003585400c00304001c2e03480d61500400896802440003035075010303d05080d164801c0700c4a10a021314500108014610707010400c485c1140c0c00303611540850052000c8556aa02c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 342682149 1250 342680899 342680929
    0x1404020f0a0503070e04020f0c0c090601020a0201270b0301060e100509132007150507020d111504030306051513090509030d050906040b0108030702011e0201111201080c 74
    0x300804801c40c0d119001550300003c503440c105000c0c0d2803d5000800342d80210b83e54030090080058030792a100300030000d80c0e1007802c00743c418034118a4588000b0b515800360b0a030182c1441301d803018040c2020800c1c0c1c2c0b0781e00c000c1074082c8070311203039915000c0044c2160800d00032600441c000300b01210031071a00341e10071800c1920070f41d104d520b001074010501602078500b1030002000782d10780c540c0c401810029400403984150307104100341c6130070450030080041200102c000d416940f9101c1480320643e80821145001030890501b190084031400d011458200c400130504060340d07000083c04101a41504050100c91044440305d4000190010f860214410941076401020340c0c24030030041c0020a4000592101004055034100300601b00640251002201e4282c0d4941044d8104820003180c03035a4140034122040007142048000c1d030001e00b081b8440240e0012001940c917078544c201e4402d4010800c08084110740702e03115400034260704209203080c0102e8101380103c100b00006401e00da111600644 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 342683399 1250 342682149 342682177
    0x7051309051c0309020306040b0a0b180109020a09081c0305070e010503011206090f0303061a0f0a1818020712030b10030f110c060709080105130b0c041a04140402 71
    0x980b200d400c0e110411040d801d50040c16200c81c89400035a90a00c141131007180110344080e0f141c9000500c5400b201d6043c5015445000f4801e0100070300c09442d51501e041d283d40c5c40780160341d0f101c480c000351184081a80884030301e1180b80c4004078261344640e10700203400d045483c14002c5880e107610a0382c0c8181d43c07902442c00904140700400075030304010b40300d050050003640700150030b0f07010f901c6000350307001c1c029030540c0460703120320081041c901041e22295a8007403c44c14a030500716481000840f51055080d040d040011009664001801320060040100302d10300c2452445900072801501075040044103031040440c0000c401040c0f0700030700035140345c048000c1501c040400361400950003007200000e8107042a0751040c404802801500041c1400c88043d0300038111850420070081a03641581c000c602540d04110601101501c503c2010740b11035072081182e03010b55602d43c2c0c0b1600a0107140e1100f0b0b0554544c049142c40c03282002c0040098548a6104808020f681c2d000d001c20780c0301d0780020344055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 342684649 1250 342683399 342683413
    0xc08060a05150d09051207110a051e030106080318030105060f030705060f0d06090f05150618030a02060307050705070b0a08010b0f1308010b0a1e0902030403050f0c0705130905 77
    0x382c042e00b00104040068200d0000f290b075140d440f402c1ca4203040c00e01c840c0300320380c2c001002010b01c00340c058070f01d10b601d000b1a080742c0302038100360100d00c0e030f00c6212700d17403c0c440c910400c1010700c00d07602034210101600c040b9049070707142c01c290078003000401c1d0814a000d000c2c0d4a000c0100c1c40b42c0c00c0c007e524014404c0003900408589280001b4000d807035026075039501c8059014014191b002401d80107680090100140c041481d10300d07039500c402100c0f4090030360301000f0b50103203042209071506006c0d107910f14070000e042c00c42e0b6003807000420304110111400035405074000007002410b039049005806594001c00841c0c1100340ca603002c40401d4070407242141c01140482004100b0b075002000100b00890040c1901d0341011403808c1c1c00001380c03080340c20101169468100134505410045a082d005000c039480b9000880020540c44c28145c0f210301803c000c1075000000141458000c008440750402d42100140d030710074150700d1071500c1ba20a409194892a400c5e624441081d000b030041c1c1082a401201400d61 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 342685899 1250 342684649 342684679
    0x9020603151f08010303090e07020a02150405090c0d050c0a12020912030703030c1e0e060d020906070813150e0405090718051602030a0503040b10180c08060a05 70
    0x1011012140503074000600e900480c02a0101424000b18a02644075010194110710b4054600c0595400403080345601d1340800a90a900140e00d260254041c0c0d07030300490074220b000e10409032003250441a04000d810051181b80d021706002841d064141001c00c001e90748548a01d2410382c4503440a4100240820124120041142c0d00610084e100140304000c0320700d40c07844150a54203e62015000300740e82d04181d058031a080310703260b045c0395030b40c2102c1d400c00e424000c0e000d42506240705015024020104e504011900243d04840130184002c266135218042440d200085a1180c8580848000510b800003100303c0c07003e1402d044410140c490b500030401000034000100002071102c50b1600c42c00800190340080300105514070130f1a203001040034135040e4203413854003001424020442d401003001c9414180c0c41420b40f9000b652090602e4a03030384032011203c4294050b90404c448a00075044c11481d00341e20340e44004008641920b030074a4542e2440108140001c7d1481075a40110816040120f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 342687149 1250 342685899 342685921
    0x302130e060109050a1d0a0209060108070c0303020d0b04060f1806030308011202150a0908060105090709170a0816022806050703020f071706010e0c0a0309020d0b07020c04060909020603 81
    0x1d40300c40480c20004401e4004442d004e1b030175914941440d800d07000704200341c4c1541441d124003948480c0a003088029070801403c0180f05044001e009420541d0104801c041524140c001d000c2601c0028424072126403035803509451000680710300101d00f1a440e508074541140e5000702d01c1203a8054442031340daa881d01900044455080e44e049038031821009400b00d0007c400c001504c0005150340d12015450304103183e2034030705041a00504e100c0c5103a04200181c00ea88468003a0540e40045603101511385640540c0786004c40c203030001460b0100104040004030907a20740514024005c881c00c1060300b00c9094000c5c0810409000400c1118140d0307020301c5034a00400090458511a204440300b180c4a00d61050070b082564200100d10a03035442d610202d03010800c0402e01510408607e0b450a0401c00180081c6111f0030700100241919440d4007415551040050b1400c03580013600c007a100d10300008020744800340d150006102d6803410f400451140d5461007071411040e40600a0f034550345410941074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 342688399 1250 342687149 342687151
    0x60901120203012c0705010905030d0f170a050708060111070308030606070f050102040305120c0d03090c050402070302070f08010b030a0209040f120309030f030207030c171e03010302130e06010905 86
    0x70381c02d0364840d40307002901018010050300c20341107540d00380c404c107108814803820003015511280c1041071f045001d06c50b9540102d44100d8040e80d5040c4034003c2c00e80e280064401c4003da0994052500480041009030051a080648100032903507641d007007a03441d00700541d0314034120354154640b90311090091000440c602d004503084000141a0750410400e550707819030402029008642e281d401081c00c100700601088103020700123002d00121b084c00125000203035581c072205410010140c03100c030386409001c2c514070700e00098503014205540e80c405c5410003a65901403403090f1a9504000f4000007901101880b80d848604030041c080e02040d5815002c00c40d500310041d0040c0c455030403280401c400600e9a6490821304403958601040341041402e000d08109600c200c00410b150040040100295002c8001900c165000b1101ea12016400d840600d03540150955000c034005680090a5004040000745048034421541e800705510b111400d002075034445008000c0d941d0184d00103101c0827a05812032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 342689649 1250 342688399 342688403
    0x60a0e040f110a0f0e060d0201210605040515090906090726071d0f01031703090a05070f0302121c0f030f1407030f140604180c031a090606090112 64
    0x1080145003030b000011040d0200b03074800d45010100c2c140801204110307504042e800b420442d152030044081c0d03000038000c1e91002e95034808001c8072004c5000c000b4483e5000a018140160080000e441c00041100b403002c05201e0b80d0b40304030b181c680040c903542c1000910702d1041101e44050800907290141d8030000e200d091500d144003801c01c2c0840c401c1c412003000024001d04501c4003464541001d1806003101c0c607000b400c4800004000701c018030100309540188882030300c85040d003e42e01c0e40c80800c0b040c03d10310080b000820600031003500041d003a10407c11030017928005c5592040781c0100911150380c3d01c003c4074041c07099820320608101201d0040800b00f4002c207860078007151456144058008441d070030841302400224902c180074401d0b80c1486800e051001c2081c041080c0d01495000600904004168911450b2203084054a812164030a0010250310501903100c464132450240c00c0d0000c0092117140500d1b82400080040030300042c030354050440034005003c2c0380d081ca0404000c01c0c40503c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 342690899 1250 342689649 342689663
    0x30118030e0607030c0209091e010209061608090d080a091211150f0309010c0828150b0f07030e19060c0206070503030a0903020106061d0d06110c01020a0305060a0e040f 74
    0x105c00243c4c41d060340b000c4c4281c0f540b10241000c800c9000c0c0b4a00080380211208600b40e10511503c070280c0c96900c1254610105a03403114084103080c905245640700d00c0d02c6103900000f911154504100d481c0e0302508424105071240b260903911901d00c00e00090324940050300001c0b8094880041d070030714010300d03101c0d600303203000b41ca203000090141c0706030b10361040d5900c40c2070b69501d5400111081c1d1024145420801c1400c1e02c0b29139800100040114550650241d40801e50720790301022000e24400c0301c1340c01400c108019075100c0e50180402800e030740011005801150340e800e2100746e103140c1480203002c5203803008000d03804503041041c121411a03403000d040360802c4080200e840070030001c102031031143c4a60760f07000c07844c0e065030326000b4203449003071388000305001c9030344c02c80342201c100442103800c040c509a426100c60030480c10400003034200070380400c40c042000105003c50342810340042c007902d034035501c0c00d01c5107860f554103005020b0481d100e849001c034060004600007548030420070340e0f06401904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 342692149 1250 342690899 342690917
    0x70c0509070c0b0c180904020102030a030b031f0b03100b031b010513030b100806100b090f09010602060a05101a070606081b01111506010c0c08011406030118030e060703 74
    0x144035000e0440503948500c40c643c001c2601c80c00c505c1c0b9a058617035041025241b2a407107082c9030740040c1d1340b8020071050005054813911000c1c19624101301d1803800e41c00b0042480105058042403000030035040d24514060702030741e42c0e401d03aa88664010328030404000b034018030300c0c0c0c4582c0e04003500d0003600d240d04504101042103280c091403c1c4803840000380d40121490301c0745040a114004c04066554007242c942c1c0c014604101c2184041c840040484250350030b0b1580e103050900000c0e411301c0b51b40d2085681b0503681e0300081489176000400c2807040f12556000c00c2252150300d118403440341144074014004115407030614031518000060b0106911031000400d565031940c0d45582014100190103101c0509040e0b049281c0da840010f2052070b40c4028042d240408060007417048c02c1c1001007045040c1308860117054100501c0c01c40e0383d00180440b0f00200440941c0c0c00d41d92400c450142e840600c01c0d070074084501c500d0260400c40c080f503103038540c9034a00582140070a01c0135642008400340c007030005903d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 342693399 1250 342692149 342692153
    0xd080405130f1a180c0315270709080309060702040b01030b0406091b0302031e0405100509100c050901020c0108130533070504090914030c0c01090803070c0509070c 72
    0x102850400b101084801a1142260018041d00314030080e40031660075080801d01002000f61300c11683c100d000c5801501110501e8004510810504201102c5023000e05415280440c0c6c11070031107001e4401ea0351180801640c1d4038801d542d034010700000f030380e02c410100b0219005241507405440808018100440c40c09040f0700003400b00c2d42690b000c642825210b480d070300b1010840203480002c0703400f0b5040460450078803e00c0c1c54260380480c00510380703411010340800c0038454204450308078170300981018405441d04003281901d880e560111070304072600b410b909014550140c0282c50340c000040c0d0080c46140364000c01100d240340003500420301c81c00c850003c10b001c80c0c0c0602090f07000e605101d0f1900c02d2f03516203004d00e00c801c4140710348080305d030601d41090040a50b070081c212403c4614000c408a01491581408404070740403003003102e69880001070b0700010b02c1001c00c00900f10b940907220104d10715651204240c41c0d10490800800500c000039080c4090b02c0c008080c540c1103007540c0f07000c400d034225036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 342694649 1250 342693399 342693401
    0x307110a050325020d11042904180210020c0f15120406021603081008070b07030302090a0f080a03090806070c060f020706110309010c0c08071101020f030a05180d080405130f 76
    0x180d0b006e440a1042c1002400d00d03001d607414202e010440f0203008028240000c10b00c800340059503100c0c6403034410303040b51101c80700c84440f100d43d0010301c2070340b04010581c006035407801103101d0903000720f01c50514005240b410b00110f03642c1c440039881072484c04002c03400245002d4001030089a090758280a4450800000000d500c0180e1098a41040300c0c2811103007624820115403269840380e002500a001880844050f40d054503458100507032108030040c00100b017101642c0140004a100400001d010000018404041402a01e4242d03150b901e44030295124181180c5520200d00c4101a07071000890300d5201200403180b03008010f003801c01665410040d100d5442000302c5188000c4180301c2860790a108814199409082400c00c1503580e40c0c0310b9285020314040a06440518850011164000d0240080000d060390503640d80e2400f90358050550b8100310404404940d110481c0134035810600a6800041e070403040b00350a0501e000100107000710030303801241545448040d05460f201e01c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 342695899 1250 342694649 342694669
    0xb0402031c020f0c031623030a08071202060601020712020a09110301180603030206040602160c270908030c130905040303090210030903120203090c060d020307110a05032502 76
    0x5158040c25040035103d0f642c03481e2164280f200c91203608054000b030071020711049a042242c0c00600c1c010000e0403a100c4901c82d41d294025501d8050050802c1801007203500c0c001000020310400402c4944d0080002c100d0350b408049031103074017580c008042403082011046982811900c000c21010305143c40d007865000340c51040c1d0841039205401300040c003e4a40d080704800603141c20303102c100304403840c54030000d50b24240900301800c06640001e4140301015200c0841010710b41203540f08250990387ca42451003200c00d51201c840c03151a510703280070048400c2c024805059041069581507403640b00c0044100d5002d6403c1240b6606100700002d4a401c0c2401428450340c041c0c2c80001d4112890300511010b1220034282c001054a070015003400250002044524680d070884016201e55a603070f0000c0c640802c0f1142250322400224041e44a107445400031031051000780c2c2c43c4e002c01d8140c040e41e40d44d00d01056074000c085420501c50328440340400302c40101c4c10100c000303410088203001d070041148618 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 342697149 1250 342695899 342695953
    0xc0604021201330605070b13060b0910050a0b1e0c191109010603020c061501020118080c0c01030e100b04180503030703050609060a050d0f0209160801080d0c0b040203 73
    0x86a10212540c1e100c000000303000411617401e15500c1c1c218207036102584850001c004a0011608806660034851154441407030010042c0040c41c0904000e551020426010300c9500c0c030400c10f911020941c14000020780d03045503240700802002507071020760401c5e50f40003060b0328500d921801040c0c80300307080040c0482d5000340c01680728145c0351400d1001d0001c0c008050700080149070041211890000340003542c203620000e8848040119040000101c1c09000824006000104510104014800c1d040c0080c210340e200b00044851809005005500f603400c0a803410296400404022604021030742146410355001000012007028440008142d905444829507099001204200c0940d4241c40b903135800100c12204c40740710349001000a520b18402d4010301d03001c1c80e401e104c80000c209000744034610b060f0303006210308000d07d000c0240c0390b8290103c29030900040c011500020f8000c0e00802d03072540d2001656034010180310076031110510740308081d0003241c040c881d170464415070f9400c0e14038014900c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 342698399 1250 342697149 342697211
    0x150c03040609060f090e010302012601080c03010f090b041b0e0c1c0603020603060118050619080c040e04120c02180a110309031902100f061503020c0604021201 70
    0xf41429401000c1c0d40166000105018a0140034000e140c1108601d03411aa4246030040c0010703240261484920540202c94444070500700012480260101e11400504030540080110034195400322040d82c0200a0140c0032604150100c1d022030050b40321511403160030100a46819034030b40b00000000300c00ca03042c4c4104080403580c2c03440c2c91070307a010120308842c4d0000d00380034890940d00000e10905c00603000506112105400500103010701d22064001d2074010404da440e114120b00190031071440d0540e403000601c0c07480010743e24101020036101075541c40c14185d1001c0c1c2d2242e5a1099003140a00d02009100c107582e0901c0050391012001300402d0011940c0d01e00500f01030820b08182c03014180000d91006060081145650000051f150308d000c1442c690f45d4140d031111808d070b09080300c04020f2030546050501030200d041184d0400022a017624041030083c1002901c12000c0303010300c041c02c02944e041000810b01520f4402d56003180000300c1800001d8444400c00c88494541e1521013004c402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 342699649 1250 342698399 342698417
    0x22170a020a11041a010e01030b0406240809030a050702060418060305100b0f04150f030308040c05040204120209060118080f1b010c06090804090c030f050604020a0e150c030406 77
    0x10081400840690654003070000c500c9484c2132444548104100604105131205c401003d6031203034000180301c0401400070000507469100450b90014580d001003480803800958400040c481c1220600c03407602c3d0790155003482035100040300e03a03a001947c00da038001c1051001140c98075161002d40c1482003410303400100c26146183c41800e0840c42014122800c0c602000440a40c503650201800e00f0000c440004400d81120880340101c501c6402c20545141220070100070541c006d580f0601070f0303004400302240f03e941c0c3c0c02007005a204c1c030b0140c4c00010320050741c80001400e1524005810042c1410115031100343e107800010707142101d03403009040754818440c002d4041418080b40b4281841c42d414280b11044600010b40b002c1c80369003000340059a54034080302031001e820302b603401030b10440343d080c0102c0005441c02005041d68400c0c8060451404010a5461130913208441c214021074541c1003890031503008002440026444020f038402e0b04129450044070284001c102030f100c252205405 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 342700899 1250 342699649 342699653
    0x2210d050108010f0e0105190902040f240905060a0303030e12030c071109100308160210080109140601021b060d020a09030c0b03010819051510051822170a020a 70
    0x20f81d0452400118503034036140c14070030b104014049030303d00c00f06500c0c1c0202d427071034581c4040390007488682c0d801c0e500249050f015004604030707520381d88800008070401c508115150121001140e4069074490b50011017600d04000080c080c1e0445041c5010810948140040e2108500060740c42100d20010302280000c2c01410480c0e0b40100c907041c1c0d20107450b01c03050b9103000200310340307228524000a0000c0101140602841c8010b0001c0b03c9055070182c80d03240460358602000e07010700000c0c081c0b29a03840c00e0006007a070b4502c144103618880c2d48164010030341403405803425400d11040a0050350401c81c10010188802694001800980d11a41ea00c0c2160b521b54100100150b801d81c103c94407400c0e0401c0104813107000010440c5800740a0b0f08142850728580c07800610300040c3c046602c40c4a82e1407010000b503403540a07440c0048031004c0d11406841607000075406c0010400b00e8009410002210010360803800310031750799540c42d205024107100c50003c0040b00d119504219803101c0182d001c88144c4c03007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 342702149 1250 342700899 342700901
    0x108040f02100e1e0904110607060f021902060702120903010902180901110a0c1101050706090c051003090203031237110901020a060504020604050a030c1e0602210d050108010f 77
    0x40d8540c00034800004a02280002500340170041e201601c45020582c064809948003002c0b070356410b500c80000c0001e1486100194040c0d0805041c2c004114030815000e0001400400e045100300d8196002c0c107040c44100c04816130303940201d6510f54042d961080c078100161900014a03c002c00b0b008081c0c6c10614010441d070b400d550b10000e00289000d0700340400d450480c0c104800300720a0381d00c60641c04007904202c0040703445004883d00030300303060706080080e42801022907100303003628400d44c1c0761b07a2511060b140c141c040c4d4012900094041d8002c10207242d6000c007408180b900070120503004400c1c0520080d150460502c80a075a600060a00c480c10342e400d4040c5c80b41e20200d800101400303040c595411b0010303480b15045c100117400d1644450008045607100c108540243c080140700740e45c0aa140c2c10124907000f10f0340140390200c1c0c90a100c111048071440919401c039036450340200340d4052180340d0000c603c1072140d01074503501401c0c402e44444a0b400d0003001d02a180d07150000801c1d44c0c040c4185c00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 342703399 1250 342702149 342702169
    0xa060f11070f050f0a050d05030a0b04060306090201090801060b0f030406090204091202071a030a05090f161a03010f2c070e270106030c110f060f01080115050108040f02100e 76
    0xa1110381c84850070000041c40402c7c544030100480c1406501e03503480700c3d003803809006c806c4d003070580c442c0ca013039004810015150300268607903000781c3c0d5a445603a140c607445802c03201c0c540558205a4000d0201c041060b08100081d036026204140c0441c40b010300f580410142d07851f00c3d50855800d80390300d10000000c0c1c0c0c1080361034010641981c003900b008810f203030030480503c0301401c89403030b040c1c032040010213070b80003004010040402c0e18100c0c0d803011510303880c0c20017a051501426a2808042c0d460340005da040c0821f80b070507954000070802c0c40c0380c50305080a0304190759865406103008110070086001006554291203a0a240c50f01400010000204841e40310074007800d520b245049036407424108402c0003400e041d5502800d0004000c600d00c41d040c2d1304450030007640c41e01885103001801421801241850180031212018012a41c03600403403802da94141501414071305803600100529841007000581050107502e907002c054900e6004500044254500c68021a51001405800d4140500388c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 342704649 1250 342703399 342703423
    0x150b091c0204110306310b0409171306030203040218060d082b0e100c050c010914010506061c0506060919060e040c0219060204081c0e120a060f11070f05 67
    0x6d2000001c503441c0601107192040c4010710382d66a13401421004c7d00c0b258442450b003900042007142d001e20100500b01c490384080d4042c141400701c0d480c00030b0920300900a807070155500801d100441514804484a4940c0c0105080d610822010b403910114000700002c0c90304040c040120401e19070700400300510608155907481d58503190841c04202d00201098001e0300c0d458000300494209501b010031241c074014084281003551030f00d1942000c0001c0c070b00c01502580e01050003030100da6a0f01003048401c1c000e01141c03600a54205111010f01c4d42c41c0e0f48184da100c400201828107024005000c40c4c1d1031035000780c3d030041908810106021640d0404c4c0125074200d030840301406240384692002351110b81d0f41901e10b4203503214003020401c1066540541e400341201c4011240107a4002046031400d032080c50308040400c0040c00302580500341810050b81403c685401401c0c044855601d4000502200c00070070301c804d0703071081020080d049940003018180d00400380d500103210b450628134204040d1601d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 342705899 1250 342704649 342704689
    0x150f0a090e01141309060b191a030c121b0c01050a14100501120f090b070f02031206130609060b07030e0d1716060c0f03150b091c0204110306 62
    0xf0060a039910324110b07148415581102068455030791620b01d0241514602c080c0d0301c007061200404181ca1400048002c40d460100d00443e0b43c0301d03031004446940300c107448240d0140010094000b100001125103030308a07110f00400030310707000c040b000e8440c1d0380c1103840e40503941d94441091100b0f1214038090914031418103021a00b0904095100413011203140c420079050003002c1c9203280312031800d5840700303030f545001800921403441c0750715008102c0ca00840f044004035003504580000c00f4800000e5031012501030011f0f4150340c60752020419107a00d81c05441d442107449007404121540c543c011000180194650161a50906d2401400d50034191450300c2c02014030140d40c02c00b04241c04891140da04501e5241590b482c058080706441c00b64103007010303040b00e04142902c850035500c240201110000c95404001d05822035101011480300303841101d003904e406000b03640f641d1400300042e802c441542d0380c0440c41114941d005c141958a2250b030300c00d01800c04800c121080c24040c6091001820342c0781 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 342707149 1250 342705899 342705929
    0x519060e01020c061c1e0b01080f151509100320130509060a090207031e080f0708270102070303110c030f030c090d060507030f1a150f0a090e01 63
    0x804a00a8003600321700640a6800c030018440709681544130443c104001040d13610018402c0080c28090800c58900d140050020000078890701c8a162142d40120708480c0310344082580c0b8802c00c04048143e981070701411004002c2c0f6409503450070383c00f1500405a07100440c514440c4040d4114408440c4102c080e105410098440020341c0f072030602d0182d0750111110340b45525900003060440402e0b410038841d1030310002c1e0100a058101c101c4030800080650400c01c075000c0514100c4101e0703025245038001100c0080424005802101510740c031820b07030f0240054a0b110000980780b123620004240050381d6001905c14107040d0b02d8010030300004400c06045282c00c81c1c004002e1b64a220700c0010345403d1002001044400c01200704580300c220300180009014442401d00100510003038411901103840e01c0c0007a59000810300030501a40c200160404d0b1580b00482409440c103241240240a640c007000812030f41da90a03005400c0d041e1686d92109202401c20800c5102804103803c40b0300b80c100485 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 342708399 1250 342707149 342707173
    0x8160905010614030c03090f0307060203010527060d0201120c090806161b0201091203021e06011a0705030c010c0c03082503020702040e03030a23040503090105070c0519060e0102 78
    0xc11260846101945c4030350326501c054400e400d214800c6212801380c000012048140300d0f076600a18181c3d0400c480f1124240b1503052200c02c640c148501003440030b0030020000b20240341008a140d0640d0060405e80103800c4091200c0c81219001a144404a0110001072007001020400d0540c42610031001d54225401d0041c050302c4200c00181040003001d603841d00004692040780d001e0003c14412080d074078100420303c0c000c2c0d04d0b1a20664507036968041c0100c0e402403a480064113034104c0311031901c90010341125240c0510958411101a1202c3c8030402081c12410700074420b1050b04166603a41c503502c20a1864000c003201405403e0f18000640380709089210500c5000e1840e4000c05400c0041c1d94120601c003160103803144a00030202c600010080000080342c64102014104c20511000e10b80c07038030350f1440c40100d0f07000e03a0003804a60061185031401e5000741c0003000c42a00502c4406006992500003c4070f07141480b0901c03c0812543d80200005c03170300a19540a841003d00241441c1c1704a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 342709649 1250 342708399 342708437
    0x6090c081501150e090903040e04080c100c0f030b0a05120a0b0c040321030f0606030e0d090b0708070519150f050906040b07030b0904050307030216060503010509040c081609050106 79
    0x44150700c17403800c0c0310114502d000c1c10000c64000305032620b131003200f514160411403440d4201c101600f40c580141c22141c644545032784959a805c840c25141c10b0641400f00100300c0c010030300c101c1b0382e90300101e0800b03010400c2c0d44c400d4015207203c0c400c100101100c4210349040341c41014003400d02c4404840c148001d01c002003400c860701c071902c0800142802d20030f569a1044000d0000c0f04d01e100c0100303143c090085034148d456000700c0030b0f142d142000ca13042a0f0260700c088070394000d540305007801d13540103000200020704198002d004e0306008404440d145400d00d01a000003e00b12042110502680d0548194a040790b00031422442d040c540100224980740d61800d4441900510040000d2502000100400d01a902040c200c0e8000742c02a42c00b03107000e1a00d6503496116110a50152140d621001c041c8600101c1050035905d00c3c0ea503c0b82181d1800c03090040594010703108403034101390f003500030804000800c01c1c0e0610030000c950b00324050345001c00d65070840b601a0080307010412081014000d42e004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 342710899 1250 342709649 342709667
    0x702030a081906080f1c17150112051005120d0203090f0a05060d020a080f0f040b220c090609054b0a050703061505160516090f0603021005030406090c08150115 70
    0x8c913075140900030203400040340c800440e5000c81c81d449281405000b03080c941e005032078080e160182c905066510401000304e954980d00350860300180e104010480940c2404411480100030107050b540035551290002100d07504104074640c4c680380d000c600180309943c054440368101c18484503009490605030340030380380390000070700c06088001301030b001c50000f0b0081c40032069403105a603032665024030303d49044095440c1a120740c00a070340c02e00070041051a0745e40705540c0540402400d194450320040381803581402c1c01d000074000750317031860f005407940c0c020a4000004d6107603201d070303080403841e10000040484102034640010075290103024000008442100e0b00d9410050400036150311101c040e080c04030291100003880b500851a001203004221211a4165000004103110801d1000c80c0c3c5000c40d02c0301d110195014200624041d40c0c60300440055406ca07018030008241d4041a848282d81040c5036031211506a0001c0700c1d120f408030900e40c0c9a0701410701c01303130309001d441c92000c0c1c01000b0581c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 342712149 1250 342710899 342710911
    0x30302061506120609041a0c090f0402030601020d1b1a011805060603060f0f03011107050609010507170c0903010c020d020706050909010302060306031e0304030b0702030a081906080f1c17 82
    0x20383c440128042c0410b003005080302e1030841b6005160b510745004101c0d241e8102ca0010341c02b6000b0042042c801d45058025a489100d060380180807100e01814201c0700f80c0c40407038415002c150b40d0000000414405024040b00161100d0100415490641150031200110420355815441c05d000d010072036848034200c0c1d40140c0c04840c911124807054000800300340600d21400c0e41741d842c01100750b8442c40840f0180c2104c9000e082034070840c2d074900e0b802d43e098400469072040040d0215504403d00c0e15105001c581044c0c1900000f0b0a100030040400d08540b100345509000d40e01909540c50394581c10091032003e41000e107040c40c2080d1120000c01c02e404018000244640300100c0012103c2e10100300300d07210108503080d0400072041548840d074913a80075001c2070300d560341010002000940000111502030303070745580700b4400d60741d02520030750b0800002d100d0a21079510f60500040420003042680384030b0510300080c0070300c080480091009011050509000d00030602920700c6444400715070783e41c2c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 342713399 1250 342712149 342712159
    0x90105041115040b030a09021903120f0512130b01270b1903060f06060801060804020d03020106080f0304080106150203070312092a0e1003061a04060303020615061206 73
    0x31a10034802c042e40c0603542054014001c04004c0209194454004151840c0241e59072400300502c1c403805428a0010302002d0301c00c0d2680c00701c02482070b10410f8034101148152420700e0601e11070100f10100351605840b154002c2115280b0304c3c00340022981d40c20300524103401070132007546202d8541e40040c403045540c80d03109551000040d095407500300c51007100340018013a60160340d480e85005030090018001c030100c7e00c1c0ca00540440c40c40d01074080141a22440c0d114454584d6403642040b9507488501e40c00c40865481c1d0b040043c032a02c04015200c003210400c00038503140c034100000c55003182c400741e100060f520110440c0c01503054000c01151811a058a4488411000303070f06400f0260092003c0140043c807100c1c07500c900048164080103400d4401d554084049503114240e807a422000d82c3d91003480360f0f0564040001804035070003805026040c55180c07941d00701c0f07680094115080f079030055001d40c10500c20410945102017600c0c00c46101124032604143c0d004111f40040480142030500070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 342714649 1250 342713399 342713419
    0x40306020c12090a21080406120b1009170a1e020f152a0d0504030201021b130207050f01021201082b11031902030405010e0109080a1101110a1a0901050411 68
    0x8034040401c41c1100346c0c100075400c1e919992024010300311241070410840c2036107056120525440c01048254840c00716a540c100400d003000d21016801c50405285a03c03031141d00c80000004043c0502641d0a056a0388210b10348142c0740140101000420009882a0f02500750b4007039130b00b240001e50b8a0754030300540b40704082c00c5174015044455001c0c24006000d01c1080c50165010741d0020080003660310030303801c0d41c90961000028201e28082d103002d082e4440310f091385c24110780d03003e80d010340009402081118400e584c0d00841c9405c9a200e00700794683c64a1910060181007410030524a04416186880ea503490340806181c20341c07400d89c6102000c10440c0d400d0b0303c000718010429142c3c2205901c60340064100d0f404006036a83d0310a1180c180030420715550301030958050400c04045802e030101604800c10540c0c4c81c40940340800c151541030000303803103260207130100402c0030b10022485080d03001c45003460300300170762490400245651a96810f1104100010ba5580b00c6180c0700c00050700c6580c1c179 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 342715899 1250 342714649 342714689
    0x30b030c0603150d063b1011090612010510080c0a1b1b060816020a1101032d050c07051c0e030d02030d0b01020a0c210602040306020c12090a 62
    0x41000da280e01404070380c2801c03222034000381c40070383e88505100d606c280c1c40c0c00100100e280d200c0150885604001c0c1e81c2200122491140040c1c001100d1030b0310b4511064500000c00300054000c2d04402d025a0031b1f950a20010b1150f414004480105591241417400c56403804104a401d0b46c070890a0071030401c07032001d4990b00e600c1580b40c81034104562010840102d030101c2c00c607039903c10042d44600c20004500c00041000c4041000c4042035983c0c01da1302509001c98540c0751001001c10b06001c013410180c0c4c800c101840c94100c2d26070880f030b516903c9d451304040d0142d04400800d5a1010b0082012150f0030000d080c0090400102244030900760504060030046421050b0350840c084400203030540a101c006000c0c407075012008290000711104100402c00825004a85c0c541107428014800c0715101824000b890709541c02c8001e8400000b50040d002c034280d9901c00a98105a104a50301500441c100800a005001c019880360f80050348905143c288000101030080030710480314102607980311254 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 342717149 1250 342715899 342715909
    0x11060a0e0a0f050307030f1d010c0c0b0309031c0c0905043329070b1f060c0b0f040b060d03120603030917210d0f050f07030b030c060315 60
    0xc0d2290b00941240c54018440c18801d469510400701180040c5c0c1c144040b00106d4051400044592906216004007030003a02c01550f06840c4404103a0703461421030030015002c40d0b004000d502ca04d4400700559195006460482d858990003841d0010050030640c0300c42c1c0c600e074001c4110089400440d00803505540440d00350400303460084c2050b00c8114002003054600101c89119001c4400b04058001d8036400354a0030564508000d2040480c00000c01600d00441d0406269640280292401007201010381d00e5006820110f54000000318100c078015009000c440e040c425400301445052008929003035440001000d0020b03c8548600105400c0b00145807080c4241224100743c500100241a140e04014049880c94458100010300103c0180040d04d07001c1071540e420b441801c98004076618405502c1c01d190000318140e0104c1e0b0340c5030841c01c40c0301040c1c02000e003d00c0043c60503002d071381803000005058484014100f4007903403181420340240e407904401c495101c100b00c1d4501e40390a00c0700d00091 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 342718399 1250 342717149 342717163
    0x21190c060501270605100c17070b0a0606030e0a0b0a0b1e0307060c0f02150d050411100c0c140f060408010506090a06120b061909061511060a0e 63
    0x30302080c0ca80000801c990403200d001500c618502d801d111680383c41c090503641a91214040c00d074100c1044041d210f1068003c0d0514030344039205031032110320340e045010200c5854100c1e29094400c000d402d400d01c80c1c80d681511900b8050310944c0f40c2804003465044c046603550008110091002e050a000504401d800b03038801c03100f03190000d20800f56080d0100c04004000c21141b4070a100307001c1c803900000d81701d004a1500840d03551101101242205035004c101001e1542409065540000c10402196084501c1038511581c400d80000102401034401d00514401c411000d00912221044140214140b0780c45142100c10b100b0b200d0000b101048041002548e01d0f04525400010100380420300103019005244900c1042c0c8200040e0350380e01c0790903c1510307070034030070020608802513010010414940d0b003558000c20142110034401c1d5024005e1050100300e0388003039125661260288a1a620000c070041911a6860134888007018200b00340e8583c07901900700e09150b650f42c0104c4030400814403041d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342719649 1250 342718399 342718403
    0x22050a03050a0c050d03120203130b090307050d08060102031b010e070e0103031d0906120109020909150906070801050d050c06040b04061707020d030b1c0302030c21190c 74
    0x9001980d691030016550440e01c03004071803101e040390010800e0700740b41c2940118541c06a681400406101402c81c000f0b52014000819548448140102140c0d4081c0243e01400b140801590783c0e0003a41403c0e41030113403018408007008150003e01945aa0010648032540000c0034902c05151600a000d40146116500103880703016030300002603481c05d0310301c1c2d4174100c901075110703150b0440602e04103400e004954524181e100c05854045001d5081c9402032a43c0342c08004000500c644d8990005000b00c0d400b10350542c0340d5401001c89103546100c990445800a241d40700a040e14201200054000f4505008940c01005081c4070360341813042c100a5441d200384003801070345d5216200e40000303001d40d2290007a000403d103905140074104080c02d880d544500d26640c054920807109090407009071800310300b010b81c41141c240a20400f89601d40e001c2111510070b400070341e42e03800007000301070900c2d1701401e10528080c045400b0f08040c1c10084201d030003001b5070b0072490100524221041d1000c2070780c0240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342720899 1250 342719649 342719659
    0x120c020109020315040c0b04060507060e100e060702120903060f190c0503070e030a050c13091a06032a0925111002040302010909020705030906030c030609100302062205 74
    0x803802c80c41301003a142c14019400748820752100e6407a42c0c1e91481c0c6104a103e0880011804c01c1804040b031b041d0381c0b0010741c0001c014103031240c0c0e12a49441c801950501d2001e084503411035001d00407034a40401024402039407400780103007011003040000340c90f0341000382180e00008030800018a2426a09500c0c07030707442095041003004010320304009285820440310f540c00b29030081510f1000c1c1c41c0004440100c0d03a440f40040c858140035000b804035200000a140d02c0194480c1f0b00f1100080b918a542a8810440d0400326402e1a000c81010710342004000f1844c850443c040d52401d4400c443d03001080211820340e8904415112000303940303112241d804d030302c001038040110392642e01d41d8001505904012240100c502007204100540100c0c8580d10000b4040381c9405002c01c1034007007903000b6028550050080c0c9082449800c00700d0304a520844280504402c0001041818034010810035080340124400140300c504550100d0040e01c0390703804240030150000d0456403c2c0c0c5482d48803034050580a06 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342722149 1250 342720899 342720913
    0x161a120705030901050105090402130b040b04061806050a180e0309210c010203030702031209010908031017010203040309180b120d080f0f07050a02240a0e0706120c0201090203 77
    0x310050003900243c0c3c0c0400b543d401c1c0400082c152604500e802d0107607400400080030705158014280081c01c161000a400645844160080766113038401c201c000c1601080660915110100d00800c8440b0341d0840e62280c0095a0305004880507820307102a10b202c07402d40080c0e94500000141d143d40103004072664043c044105942c0030840b01c1c144200901d503440200c60060442100690b01c034002180c840c00181d0043c411003e90000c172024454004e2009000010040740680f1a40c2071a40203d9030080401d0440004001e60094220205044101c80c0021419070500d580d0040190344980b090b0304080c0c8144041d40303c079582036480344003010030080802801442034441561144e0a202001c004141408002064007401d41c0b40700384500a401d01c8904036580e1208295445d03009041071100318071031040c4a1484c038031060000c442802aa18500c1c44d00d250900e00780e4142d40007021031641e580c022200402c11907410001590f0007141901c408100e51042e103104038014001c54002a6061003406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342723399 1250 342722149 342722161
    0x50114070e0108040809041b17090613110901090b0306070c02030303131a01090e0c0a030b010e041a09060411040209090a02030c0708040321020601030c090c03020c2d161a12 76
    0x10a4030440c40e003035881c0c044c5000f09c0600d240340e82034001c94140119420204c0083d21007004d003801b10007038500c101c0e642c907000911100440c10f500d070260044003610b0350303481c440f0200d45810400d140d44803031545040c143c842d801c2e43c00b00344c90b40000341c00c0c0c0c0c0c008080d121072070381017080001100a0080d24280d1203c0c0c83c2da900e18a40e0060a0180f070003803801c0c0944105841d440c1414400401038035086038061207282d21300307070040c80d640000900a0358014424018049108119410980510107050062005040900304140c0e488120f030800d501c070b588100814102d0342c1340c581c0c2183c1c1c0701c40003c1c00103841c1d60f03501c0328211030380c070603498014441e400c009000300030403c030140580d1244009840301001d041807404140e03501c290a001c0035080e00340710741e000c0101d4032071038004030018102403a001d81007400300d0906501c0d0009004030f161045e41caa03020b220b40610032003000c00030080d190006101f810645444510918028003c0524030f00390005c2030b0503103960394422128400a80c8011004501c0c1c44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342724649 1250 342723399 342723431
    0x60c0c05010f05011404110f09060c15060f010302041805060105090301060815150a1707030c0b1b0d0504031b03050601030c080f010614040c0905120307050114070e010804080904 78
    0x7401030048215110345088010f050a215003587d13480300303c86c2c9514100808c240c440072900007a06003a0302034020055060317810414400c1d07454445210003d0196424070100704007812240d400650304041c4140020003240d010003140b0382480b1150040010181c85c0c400c0101d98504c00c044c40c694241d824104001015500001c11018001034010b56040b10f44422078520501c81070000e4180c2c2c004907216090203041d549211142c074034140d1138202c4540c9641c0750b0310329840717001d2a4010356000001180140c0d4082d03907200d00c42000c403417800280081c5245800d0260183c02203000160541070100354407103c80c0742007440903003c3c0d9003001c101c40f620340e560304d011910a8401e010383d50080c0608140c1c210f8581c0140210412384208540c40c1c2e15a00c050030901000b8002c3c1000d00342000500c10340080c2c10b844a4010038400e11060000d19a00c040b1410820b0a40d0305000a98140d0001d40b0b04000c80c16a10007241c03c4402400d281080c0f264540d41070100e114080e1004183c1c0c05032810300c00081507204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342725899 1250 342724649 342724651
    0xf021c060501180609060e04151b090504050717130c0305030313050d0f0504090b0316180b09090307170c010c09090621080f040806090706200a060c0c05010f05 70
    0x19283c010700c51562142d01d0901500c0c0780d071094010915068001c80d0000340c01040b14141e0410420700080c0c1e1010545801d440b860001c3e0510300880c100240c1444241403d0040a41c441601d0030030300000201406240b005400007001560410750a204480030008210032000c0216008401c4903100c1c04c10b400c118a442c0d401800840d00c80c882d041280c0e11240c0183c803036080700f2106841303160410789486540400741c0942d40a807a414061007071302a510074103440d0040c01a00c0c0d03110900e40549000d81c045006c54181d030308214803500070322041100b003a00006c200c44100741c2c081c0e89440b000d52031710102c141d1402851907080c495404c02ea50703682002c0d4055454400c03038203140300034051580d480e00543e00408400c032951828011409241e4007044991009002881c40c590f48145069074800092b4204030007544c42d0074080e00900400c000c003513445000e80714030000341c0c4411510b0010078500f15036507142d9050b0080101303459005802c805d0f80078903040000d07180c10500906c0201c200c50f20300402014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342727149 1250 342725899 342725939
    0x27030706050f0601140901080613090302010b04110f0910090509090307050607030203070e0f0f0301090804030204060e010819230616030203061c0c0506040b0a0305130f021c060501 79
    0x200600000c00c00c0d171207031030040007445649101514003041c0700011034405200901c802c3d00504070a031780d1001c2000d18402c3d5103016009074000205400244100710689190080c142e01e102400d000c4a440046045c00701c07106520225a031400812000c078017656030400d280d2000b64054103400410a0030000400140750342485001a59459611000183c0407800183c50041c00503000243c0c1400905088400c51216200180f03c140c0104400c00060700751125840100c40d004070225040045017464040c2401a200b0710401818075230401018960f94156030103c0c80144281c041c0310414840c0410034066503140807401070082c0b51048144660b030b14002e541c1b2442070b401c00790050702c9291091007624001c1c0c0c0010801c02c00100300452090614403a03440540e4601000640040c569890800410007011000d400c0794039200110310160803103000400c1e14440070703428110100025200c01c20310341e06560480b001c4040000b0003240400b0940c24410007040285071034008120342c44520300a4a05d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342728399 1250 342727149 342727171
    0x1050a0c021809030408060c070c030f030309121d040204030b1311100305070e030109080a0f0905030f01060305101509270507080d110307111302040b070201091d2703070605 76
    0x18a43c0c00540a08e0320911001030550b83da078040600010390980d00300164940070749400300d50010700b41c0756066840404000f0740041900c09140048040700c1825030020200110740c1182801d1654a62015820004103007010310310529401000b0001301100b03002610401500f00075504269440103401044c0c185c9194011600a05140d00549014043d12034025032145040f414504207560641d80c00c82c54842000034459050004515038034100b00d66002401c8000000c00c9951450420030b041900064214140301e0030148842c088011000001040343d03000c441c0040e13504020380308054071040ca126090300100310341d0800c000348240091040180c41c00b082c02d03124a0441000140d0300d40441c559091159003041c88840042100940340002140d8058814044402104071100480e801078200410a0b83e01003800d40c19964040c00000c098960790210a0201c0810790403032252400c014038040803640080c8011054204801c014034080740c030711040725140d0b01c440c030300103000d482c044503402018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342729649 1250 342728399 342728401
    0x1a0f160b070e0607170906071a100602030412030e0a05220513050c12070509040309090b012a23010905010c0509061621180f0501050a0c02180903040806 67
    0x1454900f0813212142e512590030581c003811070300c0c03a085980000f80030316400b02d02484403002080302c048025411030380f0490b11200c0c0303141c0606003403c0306809411403400c5600500051100b0080000002d400030341500b0400003413500b08002400000785030304141e410002c10b82c507602d00c00c0321001c40d4074039442610380284a81d64a840d0003080b40320f003418002d00254080a03042d0814100200c003034814600c1c0c03c00340d13070901c0e80781e6000c205a0340c01960100c0020340c1e07045080103401110321070810300a0091030042200800ca402400021417191030b840401110507a038001084000f000b008400c4820003000785800c1d5110144500801440f070080c1c07465402c00d000b07045107520800446402c00b00c01840c450810711038200108845004c004101e5014881012568000a0312807400081c1c41040c0d40e000d92240b140981e405026540d548086c281ca800e5560030310050303030050241d4032040480e10704144203018a00029610340c001440310003044403020305010011401000078019109003e0844074a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342730899 1250 342729649 342729677
    0x60f08061914030706210e1e1f05060a0302090a320a231815040311161e170a0201021b0a05010c03020109140f070e011a0f160b07 57
    0x40c185c004000d514202c0901450b0701c40744403250303c5414807c1110003115662503003158808070140c2d010300c2d4244c09602c50380071004204c1c01d0710361703800c0d007050401c9040c4968103109000ca03060b6980c40c00300074031400511001444900c102d0b80816080c040107440300000309840d0075040d40d000d690740d1000700c422864800188220860780910b0504081040d211200c00d21002c1c4a1a45800f018001c004000c6400070001d491400400800804d0b035155803402c443c0b82420302d800b03441d51207400f40f203c83c1c036003007801e0107403202e000000c11008682e100c015040c4041051514800904105d81114040310000c48482805007400204810b046200f80c0844441c0c0d00035034000100c1100c600306082c1d108586060610195104404400b4014400e0001080f1149203035a50009841e10141c2c00d209a8003000a0a0440300200700300c0008040000009801d0350401081d030240221003205110100c0700010340481001c1d00c00221244030784002c10f0030701285514581020030701030644510002603484080015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342732149 1250 342730899 342730907
    0xc080105030d0509360403030b101e1112040f0915030c030206251401110c061303050405100207180b03030304030c110a0f05031204060f08061914030706 67
    0x20308030b14001c0c0b035029104141401102510301c200d1405c0c071036005554800e00c0c820a080c401c1c5004500c41e0320042200c4800303901740724500040c69640020800040c11040e151000011002c5401e2000c1c900b189400c0b105448a1345000180c1c256548001400107001821094203d850000d03104148010f01850106a00c40080721003140000b0b445002000d40400051424000415910b0b1540c02148042c602c0d1141e0b0300c0720600c003100c09540013600112605040c0c0c0080c0b0560101c9a4001705c0c0c0307401e11090140c01a590f0a00420b40d1407907050f50b11400f403d16004509642c02801c0050001c110540d090b07000079154074182c400c0e10821513007400c00e182900f003203001c1c207100300381e0190041d41183c0e0350303071400c80d2801c1440d02c0c150386c80780c1c045208840f1a00c448400c400a00070b140600b140d50303071500040c14a02150a60328140100040c0800e01030203034400304032042182c61b03141903181c0740c49410000300506211000d00092880b9100c0000725801c11151802292004500341d906a03603481d02c0540d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342733399 1250 342732149 342732157
    0x50c120a021003020a1704120806010201060612020702040b0603190b0d330e0304141801030b0411061923030a150305030309060f0c090105040e0411040c080105030d05 73
    0xd42c4034a100c030307140070354600ca980078201511861034140440441900c5062000c14107030740603075581c0841d44020b01e145030001803041d0010070a20003040341e20301d0848003c01c0742000c1c10244010303a40018040c1e0942d0740e00d4000b9020040300500303550356400c0068010b8411030440c48070708483d03030408103070402502d05915021501e5401c500c040c0c0c2d0440001c51072000d15030710700044a070611501d01d41d107102010030384110320040b140b8100031070303955061100c600c11499110f0146485404500d4181c0c1c05051000d01d124116a40540c5032510f541341c40ca0011980c00380c2c04201c40c1c1100380800c2c00000c1d403180100c18241ca03170303441c0c86035051182c140c080041d800b42c0c0b000920040305800c001044101800d03030b10043d444983d40510354605626550b55030b045a000343c81e9490564022030034010410003118410350071001040b80742e80f500c802c40c40080c1441c0600c0c45949081503c400016091100141c08500840b40040040081c42000305015085007000c0c00360a000c3d114110081400c14083c00c112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342734649 1250 342733399 342733403
    0x90106031d030c0c27091f06080a0f1502030405011e020901080708070509030303190c1b0b1509181e12031e011502101b1812050c120a 59
    0x80c00303a040160782800345d4201c5142c0e5650452099007145504403034040440c2d8050100e07a0090040035071380c1d480d100503c0c403804015940076807400800308000d100004862901070351120a5040c102d2807030401d440e2501d41c00b03c42e0304c41c1d039000104100400c101940403403417662000792501c50004c07000001d40220700460000300d0110f0b1405010a4129000716905a440340041c580280307050380304008213080d50001e541e4030a0310304000b030001880740c845c0d00419104000c10314103100d80003040c6d06842d080d0414854040e205200a101007010101850f075101d40404024000c0420781c20080d942a00c0300f40017400e000c0b1030b80144010b40e1619641809035020304801c074002000c03540c407a6500c00c2001d130710151100c000320341800c90b95041f81c00300390301a9000344130646128104e000c0d0028041c0c207204500040c0600603281c5440b0100401c220b00103400351f24814a4081c2c100c2d10380d09000e40e4040d420b07421090b031500841c028041000000140d43c07423120300c1035507081d02c43e00451030200d64a401c0304c200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342735899 1250 342734649 342734653
    0x106080609130c05060d0203090105060607020a0627060206161e1d040516080f010321020703051207110604260304090c0c0212070e011202040b090106031d030c 70
    0x202d403081c25002d414055003402050107918007a40e0300d000031103a40c000c0841d03003032944e000700402078030b103800703200ba40d03032060341034402c540740c07804c964001540c15450307000319420700424030301c04d004001a00c0007400c1c43c18210600601c0180d111040030350740d10021078840c14210680c501340c0174440d21400c0030700c00c4007251030f031180800040d94405945084c1203c803000480e080000440329955036134007495002c1c0c000840d544d44c50458072000148540c0c00284000c0d06103904100400004421241e55508001c0720329020380354407007a0350102e08045081e8006400d520071011517103200d090300d1008112207442201c1c40c080c20b04215080c848107008521402508000c082080148000c5400180965a203d84256440c2175280c5c100c4c00111907000c1032290024401c4072a01c8210300701461031a407021038000040100c1450002020b40643e41409845503410455026030304546854204164480300240307850341c1503840740001801050049500044440041180c511480e400310880c1d0040b010240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342737149 1250 342735899 342735901
    0x160206030106031d0d0207090f02130f06081510080601021504050d0f0e0a06030b010c050f030307030506010503280f050c0c010c09140d0c051e0306060f0a030b0403030b06041205060106080609 84
    0x234481d00100241d4002550b09034081150b402441007040544000d44031520707010103a20705090700140340c5ea0b4000c001e00c290311040001c18009a0790303260b4001c11410649001213407980d400c40101c2c00c00c22810a5801d031035541c2e03030500080110105807200e00310459510380043c18400c0000700c9107080f01e6801e4a4000510b007509002280c400d401c14803c03c0d40604000443c0700340d81d1750b01481d040008504c080d15400210500114682c14001e40390070403000d1804030706604102000c069000c2e0301c1c00913045810070701100c024640c0103e42040440e80c654640800c01842c200104031959480f200324079210354a0701d094688203900684514054a0b00503010a141c02c080c0e4090110300c92801c002a00c0b211109100080c00c1c1c0c0d80c01c110803081c14030071143d1040705000705081c14600303040a02554400e0890001c00c00c015140c10b2a20b03403c8980101d1032600d69101da080030b8004000c079800381d80e0004c00000f000303c1c000d43c80e403803400e1189124004840c90781c0e98915003190301490940751540c1c440030081c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342738399 1250 342737149 342737159
    0x903030c021207140a12270312030c140d0501030c0801060e070c0c23130b06070b06040617070602160605040b0a020c0319020a05040c020c06160206030106031d0d0207 73
    0x5111020348140f88401c40f1410b56443e1120101c8070f111b00c0f611000240349101d03407d01c1403001d68a921504815800711406a82940d0b01c0799100d0350381d20007440030180d0303580900400b140728120701499651351402103030366240001c071004040c0c4024001036600050803030b800601c80b4014806c44003101c40043d01407110f5180c005003110403030f603090401d03a00919060f00c00f1924815211094100e4001100bc010382242050b0502007021510181c8040309480d043c2c01030b0b05a119042250412a807004040600d5510b80001600a040d250014280414844001140820001190700590799250200e44401c952030801c00d0000d030184c080c103000180300b030004100e4508007101800c26513002e0700694840078004000700b49040040d0100d01021740282c03000c0410360800d500c400c8068801030b2024011800c1c9450040d540e01c00090711036006600000c7c043c80008104402444940e5004110b43c3d6296510440100a03000884a01d24410344865428803800c5000405045507013483d00035201c020319007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342739649 1250 342738399 342738413
    0x8030c07150212030a0e06091516031404080318060624120c03060a060903051203090f010507050702011d09010b03090705041d0c030a0803010b13180903030c021207 72
    0x401d107060540c400c6440b680c4001900c80003851040c41070f2100000d9084029020600d003d4010b0078102258000c4803080001c0d9112140300b603800425102c08000310b0a40440c00c90040c4605924120504178600501003003104581c004c6010b10501d45069441030035000c0201e45414041e41c505620a000040c1020b0075800c000708981c416044520182c1888203808101e003449a00b02c032110140303c000010001240b42c07205007000a4645841e10f0400f050565031010b80c0e800140f4604001443c0200000360001020490181c02000c88002031015041c44039010702103030808013089002c04c2030482d4018481100103224801b803a0010801515a4a022610111680007a000800c2c4c3c1c0104100420313545c4403401038030b1aa614007502d4142d5014401c840500b441c00041a103442900071510010109040d0f0b420703a41550302c00100309913148451812031050700c076030780c0c002d0840d5240c0d40c25441c0514250350100316164000e03103061000018070a4120307100c0390005044204002c06000351800310300d02d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342740899 1250 342739649 342739679
    0x601050126060105251b0b090d140d020a020f0405040203150a06120c05190e04060f020d0c081005060405030a030c050f0303040b0910050112030807090302041d0708030c07 75
    0x20605003180360105440c1000303002108170f0b82403e2001c04010780d03074041001c00000200301440d85480020000d040c0031948000348164a0341e40c0c418140b459801d414049151030382030724000c505040710800d4000c0c250107034846003800740691090500201c48941d030701f05030107814401c1c1e900a015082084590004251021003c1d06496803141d8070032000c07819511420292000038000c000d104005480c00302040b8101c4640d01002c3e0000d05000420032002c44040d076565045540141e020811124503141d00f0020f00070990009903280c101100e081c2c0d4581c005148900075240003c010700709a4494052051a01c101e1003442e4065009102800c0428855400c012031144a1001d4405624108804030b14681050710183c0b03d0040c50000d1207628102001b90f480c40b81c80101050103598545072882c52075114006000d0103001000707000504480c400c1c5110406168020401c005600c200109000c5d440348808070703201244203d1401042c826400415166561441c100030201281001042140001c3c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342742149 1250 342740899 342740911
    0x180f0614031305060903070636060f06060302031501020703051b030307080403030807090f06050a0f02010f0614040b0a0b0405040b060433050a0804030e030c04020c0f0601050126 78
    0x80b5040e9000c00100b050160740d0107103d05000035034480320707541029005c881091040a205030000380d10540c001d1751030401c0388142e40c4031045031408010141043e60180101c1205260724600e050004158a41c2550143d40102c070031010440d000080c460041ea501c411501010f08250b0001351101000c18030803042c01f00100d00501503c0c04c04400d039942104540190f00100c0c0461461010070440740c0c0c0c004c07010001400e4581000c4c00ba5450305502905c14800c68440c00100058510070500c4c02c1c3c000d401000044110103003c0041030382d2290a10740c19103210040c3d41c4141c0c14515a480c00d4a03006814109079040110321524161902003044000d00c10318840c40d80040c01400700145100e02c80450350380300c069501c4481c600c880c428080304855850240d010b03003840414045094000e0344440441d91180c0c0c1030030302072100c02600b400645448289600e41e0350050000802e01121813000c40d20003034090316001180c8442e6255001034443e1002401c041a00c10b01020700040000c3d0b4a00780030350401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342743399 1250 342742149 342742171
    0xc09380705010204080703021f1710051206060103050711030d020c0a050a08031e1302100212210f06031218060d0e102c0c03030a180f061403 62
    0x489681c0d003820390300a90b000c2c00c06074010401c1082503082c91804403280380d40c004078814802458800140c21140c20240148480690200054051038100110005404018a64481c25840740300b072aa46020403119030f400a410540410362444c002c00107401804540c501950601d40071007001d00007900000702540d40b602c00c1c7c82035600882c009200c13040c8494040d8513103640c1c80c41c01c83c0d084a440c0c9605400c002e41d121f20002008a501c2c8240c54496180350b040303800110200c00140128038001c0b40000d480031500001801c505d1101c1e41e00b1312440301d4100ca1100b01c4940da20341c007001c1c9521900f106d0a40e01900118020b1596038841401032400855040c814016108071802042840d004040d1808042d5030300c507145001c0e140e04218010707c4510018003440b00340400e0b07900840c400100c41450b03488000c80094000050410303c14801440b074080c04681d1a901c4a107001880010108101103079441c602001140208500c2c07141d2095420f10389800181d41881c444803480c40d4402840384000d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342744649 1250 342743399 342743407
    0x70e09100c020a0c05090c04030602130f060c03022a0d14030a050901080a06050f0f0102030f0706020901090e060102070303050f070c09050709090e1c0212030405010c0938 75
    0x526400d100e0545003504a50040121a44a2415070100c50594200c1441032113000308101203040d01d5008c481c1500d500800168640070482c032040030110391500b004401d2003030b034900442c800d98408c4502c642c80f406642101c01c030381c10304025040402c038050700e07030810b849907040e110710f042c02c2251620412501c0b036608491306090401149041d60066503840002400002e49000190703030201069400c0105901c003007100d20726110009030031103251400a401480100451720180c0e00a1054030303014201e2003482c42da40c4a403480c000009521400a1070702040030b050004c140360042003c224810310040c0c00a120360b600b10b0301c040d9000d42145a6a0102200821821000401905c12440144030109000ca038078180610003500c020300c070b0342081d00d12030b28040908000860018000e4401c0002c440101020303d00001d04909145c2c0c10031003110000170000501040000540c044a22440d42d1b680d1440015180c00010041c0120b0b1403002200400494050f07000003180200501d10203825480a450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342745899 1250 342744649 342744673
    0x302040e101a01030c031a120c0a2d12080310031202010f0501050d020607110103090b24040911010810050a0b191b0303020306010e06031602011409070e09 68
    0x16aa070000390960741c030400a50540da01e50301030080e40317000d104030300b41404003402240b4583c0307000120f02c2001d84550f80c801c5030010821014070194800d448094005645152902021944e2154014200880c2c240c542049411142045484c43c29250b52401082c41d001e01a180e00d01f09401c06402106210b0301580004001010940c0c031801906081d000443e82c00c540b41090720444405038051030003205200140401a5070b1101101c0810344d2108050a200c5d08000048004104441c0024081c102c40310a102d0b611034002200c4c14000c02c1120801e46000c0c151050000707445072280020701445801101c40607a40c010f4194030fa01c07219001245884590f64800296004c6541e8460350000310001180240405031030301000788419103092504001d4400000c454060b0300f6540094109136010000c10b02c5a8801c03c1d019030001401040c148d12410a2145e400102601d254400003543c0380420031060060440d80c12880b030321030700c406080760b40d1401480e508082d40003810300980313006040368014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342747149 1250 342745899 342745901
    0x7080a0b01120c0905090f21040b0d020c0a03050c07080d050f030703141302030f0309012f01060b1812190302010f05042108150409060902100f120212010302040e10 72
    0x101c5618558001d05c41c032104110070740d0618850b011201c1402232074195070400c4850303110883c0c0482d400201400d58130081c0082c0f0b60020b0198030f108940d9402402140340602d94080003800c0140401402c1d118815500e03080d10350340b11a07140305140400ca06000715030004a14501441e400496401c01140c074544032580c1c80d44508084a82c0c521440c68096200d05500381000144203905001000f149007450981c000382a500a102844084a059041c100c0030748064070000c140340c0c42c4280080c404941c9444241c2510b410901d0305000724200f592402c20343d481e1012410060515080160190440e100e01580d01a004410705074103664807142016442c100c02d2080300d11840c00b0700c80180010403200d5080310784c001c2c24441182000440000d000e8441c000721580c030300d6842c0407100016002164941034000e07058400d80030f0360151302844000d111941041072440703000c0241e0f842808804c00d00300c0003c00c90081c0c01c00d00782c41040140c01400141810350240c2035017021074045480c2c000f80c1e61001c1c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342748399 1250 342747149 342747151
    0x120903030e0105012903010e0c03060a030c0e0714070f060b240702040c0206071e12021206030106080106030302030708070204060f080a1109131101121d07080a0b01120c0905 76
    0x241c284003c0c0a0500c81d100303101c80c0e03c540000d413014045d46154074080030036140762009840d0100041c00080891486da031800001e400941e400b0902e010300d40da0b2078868074010300d4225580c1e130200d503800d030308805050b8592040f104e80390b910402c074105011710344c0c413200018507540703019540041c0340c08491560400c4900c208c03803981c0b8400c90307450b0307403000a441400140c55001c800d581c255801030342800061a08a0303041841029440341e43e60141c412590100c80048202511500c914030000301d0020088403542117501c152401e50007403212503a69500d5608070340d164803014005030000d05c901400528840020b1880500007440800c9443d00c0c3d000c0d4003103070803c5034000781880c2e010720400c00410007102c20340c002d04070b0116008290b925201c05d0080b42d01e841000010010400000d039840780b42e01a1400031100d0405c1c030000c10500101c801c8aa60001107091000301500c21003034009002d20f0006205840194080c2c03003c07400d070f468164a01044000c03400100d0b0590901c3c1700101e1200103900c030321 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342749649 1250 342748399 342748409
    0x10f1112040b0405040b0603040c14040204091e05070810170c0406121b0506030705031b0307020a0b01050a1d0903040b070b06011d0603060105070201030e0105040305030118020901120903030e010501 87
    0x81d940e03d924141c20001210b1b00720364058055842803081102003240c004280c0c08480d111110034035070400c0d0302d001030000d1040340c2001c1d80c00d620f0101c16241c1078a031540084000007603194100441c0d11045810f45188070704869070502070345500c400b1310010070030012100c0121001c0040b291025211000901910301c46d8000c0300c5154600d4030f00b40e040c460103141c080209105c0d02119600542440040b40e038074813000b4450000d0000000103e01003041e0000101c01b216800306045450f410800d42c02074072003020f41000c9c0c41c2c810100c80081151314000440000315426030300c0319040881c15001140003074400608035030f02e03400280400103c01c9c6843c0014140302c4d10801a09100d4030380800054980300c0d00c210700c3c2c0811503092907500b255440303142c11030350410000d0030195150300c820b01c0103c0c05807894000700181c40d400e22060204150f041700c003031410313280740c00100c03070a040c09205544220b005103c1c4a41c0000d100041c103d01560250303000031311550191070b020030480c0c458501103094403802e03445 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342750899 1250 342749649 342749669
    0xc030210170a0605061801051c02030601021002090303040905040f0807080406080a15090b0409081225020613030521010303030b0a05030304030b060307050306010608071d010f111204 80
    0x8071411044541c01580306070441d104000d410300b80400314010f4041d000107130701214004010b01c5500e80c0242d05486441c0140503143c4240e0200c1d290101c007030b40050720128094071035400402c080c0300d41c07802501c400c101c1c0038004504080c41e00c041440540005030040c0c80031901070a154021400007001440194000c1d20030660b96031a0070801003800d1350040c01f41e00700300e19202c2c081c0e00c20f0003044816422152415004108800c0080c0000c0c0101100d040052058100040108080041c0c0c40355a2265410b0002c0403c455071041584050788a14a0580016041400013422411428002544041c007a2030701d14201240c402004544040c02c440200707503555100010420194940140c610400c003d1302c442110720310f448042603590040e40030080c030344100140040d040341c504010703d100a141c028115240380d40d40341009010840c065401d100007481e0254980180f00c00c84111010300101070391144d41411640c0012900034089004800e414015a152011072503050b1001c1e02c05002003650b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342752149 1250 342750899 342750917
    0x41112010503160e0f0603030d150e0c030c0f0a02160909051e030409111204030f090503060606030c0304030c0203010e03121005090c0a03020f040b030609090a0206160c030210 77
    0x2c1502d8580d00043d040d2039018000e20501c003c03501c22190b5900641e480e4044011a1658800642140111034020103968600b00300788a1310440701039110100c5040904441d4151104040c0c0300c1c5620084a5100d0034100820a006140203560010700d4112000d206668082041200350002107510358480465691111144014410140450001285140c00205400b4076104029459004d00d01c0341d441070300d5070b904170007a040541600304c503540659080005900d1074607141c003134041c100c440d400000007004e0442c00b0407d81000034005000340c100601c11811940d401c500e503810380d07000900403010404607081082c01030310240104584c6400020241d5113502c00c20900d400f0040009044e0b60a841400c20200030036283e01c05010b0f001020b00361002e503a1105400b0a40207403140c1000c420020303a001400060002c0c100d4051801180100d403240f0550701e408046950b560780c04003020390b001c0c81c100126444510002c0541008507c2038444041c055502e03000a43d68020507000e01c1c02148400c0303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342753399 1250 342752149 342752159
    0xd0204150c050c150702040e010606230d02180a080d020f03040e07050705070e091f1a01080618040b04020a051f031d030a0e0a3204111201 61
    0x440d0048003010910308070604008546034280d40340c1d40740e01030754052020501e101a0318500402110042600940180700700d201100c1050f0080c0780c0c0b4421140000c00035407160512400442c06402d10022204140b03060a6440e24003100079800298000d4100c9140c040e40c0ca03654841c01c0c00c030381c024602c0402078181011049030103400d14482d012040640d800400092001384441c0b0f900320380041751b0340f030300c2c41c1c98250758a00149040303029008282040c10314000c00c12070190006468112542d1900500100c0c4c2d100e882c1e590944118128180b080c2d41d5051404503154440e100059000d04001c001c2410070800d0184000010003da4095a83c0420b9000700300030f5060010800000384000d8911761100011451502c02d111500f202050406440d03a501802000484154000d91084001a20303590030040c81c000d401d8021550352a4001c0034041400221001da42da074221488200740c0243d07100700441401c0040c9402400c030800d80c0070b55140801075130b10600d1000381414521014540035154180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342754649 1250 342753399 342753419
    0x606040815040c12021309050a0c080106060e0108040803070305150d08090405010b030c040303180509070513080c0604030f05120406080f0f070c021c0210030207030e030f0705060a02030d020d0204 86
    0x284c00407031011a00c66007580040c0c81300c490b400c1600180300000140f00b5540c2c5080c0e810a0917514020701100d400b414003040e868010350246084903800d0300c40d00401c0c50102c005440041d421140501011410b000141c40d1038080e0704902e038086111458800b24800b420001410750f44195010340d0000c02c0882c009410b4102842407034090664815824114a0a2201d00c0120301c11030000908200f405110841c0b00c0d07a6011504019100003849000c031b81c588190b0041c0181c210500000c0b85803403400c0002029480840c00c1c01c8100380107000c3c60320f4503065444043c0344100100341102e441c0300d1403d211400c500568058406031071f2541d0b600c10319007415560041100005040d150307400102c1000d1044007a00503c0c000c469070b50541d40080003140d000204c82a20120307a00280d0000010340c1e12801c07a40d4158003c100040c42074881603a0b01000d481816543c0308041c03100781d0b166000329800d00c124174201010b0a5240390b1481100e00d4051030742ca001c4180d07005420041086038011500f400011782c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342755899 1250 342754649 342754673
    0x180a0606270603020303041208040911070501050a05150f0102070b0f19020102030f13110409050624032508010e07170a0b061003090b09030c0d05041508060604081504 73
    0x410309080c80b00e5401c0d07800090322442148545820510002107240c2000000070030303100140a890750400081c01c203d20103040a91007808126015442c0c0000114146514440d180c09803000300402c103a020480020301c040c1c10070301850301f8150302c01c4000000b85111880001c00c000321902c80b2503a100d1049010080e848400008007405690040c010461003004204006074041c0c500309040413400303098240000d140a6240c0c0301c51300142030100c40c9013030200c001445409041c003c481d002180d500301c0d50880d25801c41441d085d9058000042c00a10040e00304042040220003101941c009541d034000e903030843d001400031200e25044078000300010041342076040110b89403500a07010100f2195105020224000c145501c0341d030208080c3c51040d4800e030302030001c85030f10501144490410190307840c0d0303942140c05d06c40a207114032004c68034940d1098040d81c0c02c64803540c05041c0e80044441080c0c804504c01001280c1207002444001403a01080000c9054084105060807103428541042e5140c02c2e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342757149 1250 342755899 342755969
    0x13080d021f09080d020d05040c080c1e011704030804030216052121120705070807030804022709060601080702152a0301090c020a0b180a0606 62
    0x16610244854100300c0782910141540740d000281104245400c4816000e50f5110703e50503403010401e03000c1811150703c120f0140d405980d045003400c2d9201305455540c6000c0980b9038204903a207800745a82c2d02150898100420141081e080100c003c802c0c80c01c50030421502035000446160600007415014442150b5510a4032a40c500041c03c01c0c02180c403030340e0390861450041015242d0100d842c0010300240c3d1000341c0307600540cc80f81c80c0303030301d0707680425040891071891040d2001d0102c0c0e03446000300110741046a01040341401c1030200c1c2c5058851890041c01030b80c204001210f0001d07042002902c03030014003665402c0c00c0d05410301c6044545800001001c1e00d05001100d000d20003800c4d0001040b00d006009460741d00c0c1645d03200464405007034000da9403010801c51880411801c428260044e43c180c4580c018100510300e00800700b01da81e80c010210117440780c801c1d0400704407800128036102005c0454803045a10034490b6940b84d008440c00d640c06010208803003001d00380030404201c85104030203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342758399 1250 342757149 342757153
    0x501110d0b0f1c0f0611070c0509010305070506070602040510030c020c0334090e0a03021b060d0203090a0b0a061502060915060a080a033f050a020d0213080d02 70
    0xa4290b004110240c8041d058400050b151551903020020182034640c00b455001409010315030300b5020000880e081800103c8103008a4200490f0a060943c29281280e412800908011b843c11092107a15800702c0000c0e101250200404180382e240e520710710300206030b82c1d80d00007128583d40d0002420180c942450380d1080c1c00015a1440c1074030101c024480c4111440c003001c00382c03100302a030740c0d0091500c1d40c01030310b009007802c652a03e108008190074401901a40a0300c01948101501c00950003400303850a9104005001000c461034031a400745074881c1c01c00302190b0032041c454a640318000e0080341e200120640741c02090015416040d48036018210034002405a4285200d000c5d4035071552400902c2e021038914005012a0749064443c0c00911860080d02c003100e8035400d006059003400c00c140c400c1c00711403000c100e14445e82c00c407075081804000d0500012501540b0400381c09000c0161018070320f56003d20504806003501d20007088420b80796000036151a1509403424100240c032a00c1100359 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342759649 1250 342758399 342758419
    0x609050f010909110408060f040b0915160504031a01031209050102061303170118110405030c0d030320030610080c070b0c120103060c0e040c020d0305130501110d0b 72
    0x96600b2070464801d4079400b00700490701c542d81c004203444c0360089502010300e41c424541072102d41c114030b002c0349010318000c2c02584031540c0c4000403140e40b0b0b080004508003826003070002460119141140c43c2d0120341610b040c03850140d032030b2165110060607190355141e00c41c50b00f0042040113103121408070344076003900300001c0c02071400001035210307140186003040103c0300450000801d4071440c00b02c100c51401d5901202079584405010508100d0350020392030b280e181c40390324540d4030160015541156001030003081614100010311a541515038022001e1507110b100144800c80303020407001d002061070701d41079241d280840c104844080c00141d14402e129000c02400b0010314098101d03110f49030040c03100c407896203803000441410310500580450428980001104200c03243c2c01c0030391030024540c0e4203004180d800c0308001c102c944d03080320400968442c0701440d01950203500440c0d889030b05005e5007440180035849050a540c13032400350909800f000036800f1000011442000c840c40020b031001550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342760899 1250 342759649 342759679
    0xe1b0102030a11030c0a030513051906030e0f01020307020a0201080c03040c0b0c030c0a08070201110c011d01110d03062c040602180d03030608210d0504020a0b13060905 74
    0x1c81c407850114000300b103401c0d044510000401c0045540c0d80c00001d04a91011485050040a5801410346120300340b451120018a0341341607440c44104500074a40c0310f83c070358070700303031040e0010500340b0350240c914000c0700d6101035211001c1c8041d42c46030b103298018001e08422440010b0449500400703070707a2810030900030310012485c0a021003003550400d1110607500c0000f00c00700c9144d80103042010070244144031030107042002d00005407004038801e882d0a000c200700381800603151812140524001001c00c01404d0400d0002803014803000018140355000200c9205d84038100102040308101007a1035031401c00c403101882c0c03480c0000d80f00460303180c6204550b81c280d024244002030300140c205500483c08154620660606200b40305c0000d1000303d5441844c030f0702070084d1085110b020010300031424200d600041152881d5040c407a940070652034020020b000c400185000340007a0b8200b1583c00c0081086414103001305201600390081000c07140c9084001090140d482e0841801441401d000b881 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342762149 1250 342760899 342760903
    0x51003140c1b06010b041a0f04060e0901120510020a0306050a0902070c06020f0a06021c0510090b191502030f0c06010e250806130204091d030a02061504060e09010e1b0102 75
    0x7d840070340744003040c01004025035200c40d0150400403e00c046000400040d03240e0800c140345c0c0002416102105039a0703990404c8441000522030190550b00a0070500e9422030712507006100c800c1e103d0400050725616800031402c1440503420211549070b0001d0860f0503c151002d0810040041e071000b0030000d8050355100391035203048078000f02030079008034212614180300550009a13125068007003045180140801411a440b4440c01d000e4a00d01402910300d03042011400058050814070580e0ba9440c00d01d02c6101c031460f2a802c0021070000b4800a0a05c1c0b040200510b000d031010307401020554144040d400d00400b000d407841104401101d9811050301c2c250086c080c0c0c0c0c841504002900f03079a1300001c20950460100303810540c03480018080342c01180d80c0d21620b8242c4450303680c44c194124420a03e03907030344690403008015078401000a1802c046640345621080c1d806040800d01554445c1d10030b001c00801d8038402040e9440342c200304400340d410440e040d0b03000c46003103c0c50b44c02c41c400030010b5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342763399 1250 342762149 342762157
    0xf1b1202040b240d11070f0c0f050a03230303040b10050f18090f0f010e0610052101020d0609050108060703290f090c090913020a051003140c1b06010b 66
    0x1210040081a101c0048207182e21030005c03000c4c605030890f507076855860948010b41c6220000c0b01d1100003000085a031181d401c012509692000d481c00e84200c1c21a211300c9195540006282c0410085102440c0949014400303540500c4c802c0107266070b28202460072010604054100d18000c6030321055845040c1e1390040880d181015220304550b554542d40c9215080070a0850403003294410b082c405001030005600c401110041401a10021348502412540c00d104a100b916070041070084600101ca0f807101000ca0398506420005203084441c0c40c02500b40e4541780d01c658180e6941d04010044140f00340f2003150f01905c117203410840f08410050780c0c4840c0304204075141c1510349140e00319000341c589605d19060711000409840003450103a0308544594044030506005102440100b2003060198404408207540240308812860611044c00802c070300c8030000004040d101c1c41d401050640c40b05000707019000c501003055641c1140024002c0c80011001032040ea80c0c0301000400003054108269 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342764649 1250 342763399 342763459
    0x51e0a03030b030c031c030c030905070501081e10090b04020a090924140f0a0807031502090402070c09050907260307080c0102070c05090403020a0f1b1202040b 70
    0x2071072121002c08207203001100880703075416100360240c00c06815a518807103100c4060341c1d034051018011200d011020358404940090143c4e119000c10300040d07019220340c5e54800851108a8000c003034514800890b00c400fa0fa100740f01e004c0014051001141d907000d1111480c00a9805500d8021034004c0102441454071801482c5a540d040c11948005040c030707103904071503903110348100080e15620036200450b2420302c0e59200e01001007040016007842c4007808101d44110002d04a1149552151140740e00c4045030004101d9007040100103513503d504c0a0030359203000310144d411903030502d4100c0c030440c0c0700030b0500442035006160070410a480c8042034026541c41940c04a05c0030540009a03145021f60900108120004103650308050340560203414075501590030365504640c3c513414043d0f51701c01a500580181c01000620000c9110f00c400380002030b1141d03110902d4443c1c2c4202c450000c401c80d801c156042d4000f48801d00a503d000d0217181f0100d0000c507500c0403590a1034020003042031420100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342765899 1250 342764649 342764651
    0x15030b16030b100801080708070b0d0c09030602040305030705060106030509030a0507050102090405092803050a031d010510061e0912061407110d09080c0f060c010c03020403051e0a0303 81
    0x2800c006200303400482ca449009407499920082c9424040c08410742402600c8807407052540000314898000303003010407240c2c1800d0b180c0c036100c911108080a023806106160038440d049074000001255440104001d5020380041c545450316454018201801a40326600305814801800300a000c044121922000c0d54201507903154031a00c0d18a0182c012030a900780d00c549000d0401904150103c1d210108000d000100c0700c9034450301711542c000c50000344000c0e000840610480441ca400380e84012450103040304103000d080714440801d0b003500e0b4101c5d160408040c02c1203082200c02e40180700002c109813810f0346901d5800032000010000c10003803054048130841d1a14000602c0710582c0a079480d00110444508107141030000501080510300e00911144103024900c040702d8421090700c4c05841858019010130380004003000b10702812002c841c1d1380244c04020008856400f44669182c8a1403500e0140e01d85186091035420300301d0b0354405180b00041e9803400d941100c0c01040e5600a1545414 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342767149 1250 342765899 342765931
    0xe0a15180e07030209100e07020a030203030f06031c05180f0d060b0109090504030201140708040b010501050f0d0501092a020607080a0b060a02010b21070302100219110415030b 77
    0x103100d02d00540ca030f2010750020300d00b106014048500101070010b0310780d185080100c41d210030390100da607051040b40150040c1c00510100310700d1400100710f9500300304003c0899500c0b040703100d880101410b02126081c08074900056041c000900e0500002c00701004652643c02030101c400400c05108046100511182d6034061800850b0f025a84da0409018a410100074a1800c2c2ca8007a0007040c020b1401c625020b01240065459803141c5c4519114503400034107000030380d2801006482c3d6400503d0114590302007404241d00c0c2c0c54262040710f000b042001c102055548150405030201d4104220316600300701c440f6141c000d06a00016019040351b1a8900400e560ba10341031080001c111003054940c1c4030200150401245505400412035140c0c11140180024051005412440009040000150807039042000980b6240e456040b00c0c0201e40180e82240c2c64420302d503480d41405640854800f520400801060b040c0381c40392074103004900700704903405420340d03c07007841040c8014012112000601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342768399 1250 342767149 342767171
    0x30506010e0109031520041401030b0a080307110f060a23070b070e04060905040b0a050105030102160f05150c0703030501080d08010506072a0801050604050408090d14070e0a1518 78
    0x1006c00c0c07860424000480d02c1d1b580715080d12560301083c08a0600007410501e810382146003040614040f84c00c502d00030b40c41d01c4de40d66640c0300c150701028051540000c201000c0b0071a915082e004101c428003e643c0c583c1001420b80001c009440c59094200311400b0a0018000180d004000300c0e4225551b030416042c0c07869000c0005000c0e00c115000142154142018001004840028603015484100044c40036a885000385403c0740522014581c030806102440d201103040001150303281400781055451071120070641000441007503070340c04e155440004800c014158148544d03800b400c06000a401042d650031002070801c2c506010b00b5204041c0041d4400403c17804200041000c0744500303040501d40c1d02044d14141001e0b442c412105107508000002d40d441c030302846000e11513a070003401c0380e04102d00001840b45001441e6800c82c0e01c070b6110064451824405c100b244000c1c039502036207030902d18040340c0c45030a54241018645d0215082001404840320b4101003008907045d070180050492202c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342769649 1250 342768399 342768431
    0x20f0d0c03020607032109111306090203070903051911122505030f060108060c030907030f061a180115021227091e100e07030506010e01090315 63
    0x141d1000398000000210703142016041401c611b818540c0118144842d95455640420b8440c00a80244100921030040e1800c0c82c007094216441d43c1d0030394000440035150b503448001c0b680280ca4400c040b132403891003042081402c01041d00301d0040d8903c4070001101c40c1e52201070780c82c984054513100d00020100600c003c001040030f420200ca040c450242d112102410314100011180202d5000b40100c03001104401c80c0040c4142c121143c0f20010311250766210321601490f00003410f070405900980100002203600110500c903e0f030702071040041d011068040e0407640211a240041c0141c0320b01258862940211080f64111101003605102800940100300c0c00e14103520044980b2180c007041c440d1a03078120740010440184d040c003602c640c801c03c5a0420846480c01c440b0140c450501212403040038450500715600001c65a100800c80e54403400540380c260021100100003c1e44c817401c01c503030f540c2c1c0085400c51004003800d04040702c07802d50702d981510031715404c111100f15448147c005048022 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342770899 1250 342769649 342769673
    0x604020705010c0e010206010b0a140703110d020304140f03150c04170304030c060230120112150b01200c0a08070801060b0301050d03080702010f060b0a02070909020f0d 74
    0x2000008000d000c03c4000702070855020203020324014400c00b800490a41100c0702100d6409000e030300c0d100c0c02000000c4400d03ca40c0e21101c001c40c100308003021000d0666108224006a406658000d90346450411a900e24802c0034401e6861184080203652144c0751804200b40000203000c07102a070140c0d8440c0c013800300742d00c1258400f0383d51961008500300d034110040301a0041c0e80c400d03030814810603034071441243d6400300d0a1140d820310114205c0c0c61040007005440c100744a12040c0041d040035640d001182954200340d01480c40f020346201400100112480c2c0303561058010182048003042200000b800f18034544501e515405149025074440d182c100550456054018510400a5101c04900b070b1500304901c0f61085544c203140010503914007600c01e0382e05035100508030132441d02d2070f602c00302c03a10070014020700c0c2555a980c4102c00602c500c0d0181c04040c1c000c12001a58606910100903c3c00c101548a40c10103490401e50000503a070300380740207803c00d0301103403441c100800c3c0d13080000600d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342772149 1250 342770899 342770903
    0x18120e13020d0b0301050f0c07060f02132904170f0303090a1e3f0509011205040c15110d090501030c022407020a173006010806040207 59
    0x1035604412034400304550001d207100740701c06105109030b504110a142c207952007601e0513403c04814a0005450072004000707889050700402c1d0104a603441002035908a0380100c028485801241c641031091050004c4a40c00e00c6101c00c1c81c51040c0181c403d90107100d40924052020407041e0340a443c04040410000c6901c480388600c107903940e0342008030426540c2c4200100132103500440d0040c5188080c441c20141100a400c1032180c2124080ca0241d17044925540000c110304900001c0e6a4000d850b2030713222000c01a401c1d440c0c0e15a00c83c0300c0300014201c540034150448105050904010018080704195821074100140700f90485200c1c4070145c0d080780120381100d007680319801150391495480a040b408541081c0c81c01c001c15216164105e803540104149005040718015017601d0084c452401c6960125507803043c0d031401d40a680d42c901c0d40310b071004460340c100c040110702c2e10a01d08543c07101002d550082d07101c0350300c40e14000360704501c0d040380149064148084440060140c0d00c4032b404803080d040e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342773399 1250 342772149 342772159
    0xc0409050118050f01060509010810080105070c020909010b280302060a0c060c0c0809190b0703050c0d030216030806010306180920061806040b0301060207150318120e 73
    0x340c0c545041d0a80a81d200700200b08103420000402d01009001c2c4c4864103a0361036645007803030715014000540d802c0f4400f0380f08010362503030740800040251003031041900400c81c0380d581403030301b100c075004024581401800307103429a45009803404407540c4e1054010f8410b83e0b040c482c0d03000721800b128202c144c003030680e0010350800c3c800945044066800f190280300148148403c01c421840304008031900d080190380280021800c0003020024542117116915254aa0a0b1903013010b071141450901038005200460100c1c001080b1440c0c1400c1c10b014140c4036119600d0114180300d0390883d00248041140303c081c0034440480003140035030b407090b00030388058140c0c03040c01500802c0a03210400100f04840c4c0907130356220f0700b681440c0c000ca01c11028221030500240064100203114901031400080701000301c0e8041410080000e084603c0800b0354000c107515000780070140c0ca050080c08003a0b2840200d003080514003690301984200144c09011800d40040b2803180d1044160801e989299240c600b0580c09 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342774649 1250 342773399 342773401
    0x110a05010e060709081b0d1b06050a091d010303080405160f030b09060f0109020d180f03140702030d2106150906081e2d0435030c040905 60
    0x500002550b00d00803856555002c0c00541d898517003544070380c540c40c500408580d01d88070a107402d01d056031000e04111b000e15080000558115900a814440d69118002280020a0010005400c106184014101690307070400c81c8052080c444c2220340140001802d101044001c1010f0103010040a04101c02d2054102003198480f00b50500da94840d02c021540a85800300040c05d10201140003401071400141d6504564200851240070350801c0301d503103181c1a600d8243d5074001c0f6500e461032800a018400c200703154905420018003059207a21000d08146080014000507140042c842031621410302e4104462502c0000c06010030784c52050010700c20341171140100e01c00b41052054040889180c41e0306149582d500d07002d8450000840b42c005240c10621100c1d01d012844ca038285030f00c820350381d40024041c0c031665026054010059501e03c14549440c0400c410014903c174000304d40203180702884a03d030612030303d03800403070700c1401034110b64407001c4080f9050740e030340d2003d0310050f000d0400d0034089 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342775899 1250 342774649 342774671
    0x150e0a1107052b0f02063714090307050607030903031803020114010503010c0c0b13150f0614061b070b040914011415071b080303180304050d0201110a0501 68
    0x100c02e450000c08454603500140c518050420140e00404a802404040d504d01004000740c5090310600400704403007103100c0c51f40021010401120b0450380c2c0d00000c0000420080a442c2c120042010940360310030080b000120320002041d580c04440d81c43c0210b414805468114054200c02c0383c080f48203001c0741c456408158064124000d0280d0400501c0c866a81e00d8003014266a503250390720300401d96945410780400e03602c0a03000d60089020342c0404055201d80c1d95518061a5102c91b040c803182c0e9140440626030640c014880204181c0c00d503d01206807110016506d48102d01c0f6032845c180380c1041030b00b5801c42c1403003014004c1025080c150340f03842e5101003180180402c41c5000f21000c0428001050350603000c40140c5000302d000c2d0031400301d002081c0c1d440c0b040307901440b01628030f40c9400c40c03900c052404001d054409041c801c1d003d5a240e0401130480c00c40b215a20b030350a03140c3e0308180400c0c4126291810949841502440d0003002c0004d40d140303076400d11004900250040d4200840d4002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342777149 1250 342775899 342775933
    0x160302010f0b1c02191703040e010b03010b041511010509030a020c09010f031212090f05010b0904050c01050d0e0f1c030623061c050a150e0a110705 65
    0x406050700403000d00c00c0703101c2c4108010b000b510409054891403050f000180250034200c1602e0b4010107400c440b00003a41c0c644800809064031160041c40a6000180074010ba0382d00c09001c9005010301c10352a41036504201550f500d5005601a04182180804c0344c515850f101d06201e25486c00c0c000c008200a0416046c1292281d2000180d4405881810850501410481075090494003e0301480b180503065030b0312081003603101c42c032140800c038175200b0340c0070072050911400e0441c41c401e081a500050b01d614110303003035401615000d0b22134400c000c101301c0031500104001080c03260901c1e04076500e00490400e000140304002d00240d89100359030b0043d0f80c04100140c01030b88169a44402c00080282c0101201a1104d9000d1509030780c51034080c44182a030407510001500c040280154203250b4842c0080007644103110142005c29254414010404402d128002245a0940c4824051801d01d40100080d000150981020743d9890380303881020f18001003681e440366030040031345400100c8011003078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342778399 1250 342777149 342777161
    0x1c020d0504151409060a0902150c0105010306050c0a0905041512060b090f090c191502010b09070207030305160f120f080703020a080f0a0e010e03130807050a03110616030201 76
    0x4483e280055481e5200791010b02d0b148541c1c85040104a42d80e50030502001a06ea20541240c015100590b140f1080f02000d0180680004403000007500d985503051510686001030034100040f801000103000d03895010150a0540303109607808600a15000401c5030070f81c8003580540c03070180055581c43c0800880c1c1e004000b482c1c10484215010b0744442e50f0b44c6403491400c2d00c0b41006540030301c2c0e10030801d082c1720a241440300303034950b441d0080d03503554824190645140c5c42281d006035500d0000e83c00b10b14000d402d9640014040c80181101030942d84c1c080c1c035601c6112a148001116607401d2020000b0a0203045605e59101200b0303231111581d14405050300301c01c40d050201040402c000100014441e2007a5038025049a50300e18854580b9240d0348407103100a01256801501c41e1109130360300b2424081c0d811008007200040d40e0b61928020303200300342e6516070000303401764100403410055075452061120aa03a08880c6800c000101840081c140b44561000d10382e07400e00c604000800d254040d8491 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342779649 1250 342778399 342778433
    0x121104050405060a05010903060b0604090203132627060c0f010f1a0d05010b03010e071404020415080c070c06080708130c0b0d060e1807060809031c020d0504 69
    0x2d10803521800e040001011441c041c960024680c5403040004c10034542021080310f0015150524003070f2101c2c0503c0684c1d008844d1000c0a54041480000f0080003107800e81480424285c400c00030040f468a40741c00b03108030f814502003211070310300e01d07040020f20300f2071060008802000309540d0b100805900340c44503100078500449500c1c0804d102401e41160080010b0414541c0d2810010f4020004000c0080c0190000356140e650b220506500c07a2000d00c5a681e00341d80d084000c064262070401000480780300000401d000350b0040c0002c20101480264940061000341010402c542e00c04204140070b0144006c05800b50364140f80c0000d420350810341e140c4c080e011a5071901038560320450756004204101500601800c903003030040104694407c09044400007240d004585266507031604455040309031040005180039115680c10f00c10b0401204006040720701b010306a62030101c402645900842000c0007200070003415400012a4640c11109622500f460800450070311b41009851444a2940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342780899 1250 342779649 342779651
    0xe01032c2404020d0f050a061109030d1713021f080a05070f021f0f0203090607030516021506040603080c0105070207080c09011a04030812090706030603030c0609031211040504 77
    0x621494004060141e4071550300a4055000583c0c3c66540320b85501010134280c80902400c5405c400180407402480d03c2d01c0c040001807038843d001b010805003020342c44d1035210203100043c041e408140d143c0040481e408581c1100029842245001054843e00074880c988a10000802150103481d00151030a0003038000090400550350740000a60340c0c1600090b2000150303020b0030501001d155240c02d00c1114084802c000310b010ba0103448104141e800c107445080568204070304210f001541441407591140403c0440310010561140194440016181c0900504e040c60000b40d6103403075a0304114000c551114078540e82d1003006103458001c01c0c040d85e000005004040c400500355400080c0700c5850301d001000c4242c60b9180c02c9074044606901240307061001000c5c0000070114040740050301a500c02227000300c4140c548549038a06055240d0000000d0502e809000d05c04a5800385540d051998481e0000407082142c1c1002e80300000004072029241d400c080c180352641c0c041c5030183c412550240c80c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342782149 1250 342780899 342780943
    0x90d0308070f050301080a060c0203040f081018120807021f0b01080105031f02030402030a08070c0e01050a030308040209060a050405100801051b07170d02070b150f010e01032c 77
    0x1c02203d691000b07203c2c1c42c031507510100813440070036041e6000c0040b007103079801200e207001d039101d044004100d0715030b00524041c0c010740c0c4090f8481e000340c00341085079102c5440e20040d400300d5613541c4003000940c0a114080049010002e078842d4000c01c80c0724405080d0050038080000d002074401c01411042c444c05000500c03e000005480c100098041001c04500f24000061034221024600035040108166411310404008134081a6024010140180507920703003106541481c0c1300061403c4103a018601500d8080c4080002c29406000c0540040e81105e80d50302c59282c000000d25031200940086a20524100501c0611102203c0220454694038002d1000342d031500041710030810520407814009500704a900001208051200c070072440030301c08035040032880d000314030403600030110458450384100c081c40314018504003174140b41d034801c4886012002c00704000802c401344a44d40c0358185900c6d6004a03610013410500b48c881409149000d030243d0b01c40c42200359892070901c2d0003d10b40f40c4001703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342783399 1250 342782149 342782177
    0xf12020904060312030c2c0f1f09061103041413050901020a020c030102070b3909010311070f06020c1207050109030905010221070614090106060e040213030f020402090d030807 77
    0x746944210343c0c07804641c883c04200c0382443c0d03580035005888075234455520b840f00d00d40c0c3c3e0b50300940c2d840c515041e9034445c602c0c03080680c40503016407020381080090240b1303e00c00c285000f500008907010b9500c81c00c008100004960040f6451080440040c60b4181c03c01040040e22001580a003010b100c00e075080301e15085507001414203c0c0b10360507001d4031111584000480c1e03145014040da036140b1140700c6111010030039008094085103e000e4001d10284000380c049a03969041c00342400c00241e103c3c910307140c130000fa03031009180015010018006500810319039407170101400301194402d0342d5804507035a00d42c10300d4564003d000c090400c60200ea01140701007000d51001800c044a54080c072100711500580e0b24095016401125044440365251183d0001d10044203c14601804030722b80085481402c00da4060002a485c40409009a1040c03101c0a070103054146500300b100d81003c42c0400003010742c0045006449108049a000700d685020707801010342c0290031610503001556260120b100d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342784649 1250 342783399 342783407
    0x1a03070f0b03060906032b0e010f02031602040f020a180f0509010b0d060f1805070f0905190504020708070b01080a031215180f0b09070f12020904060312030c 69
    0x3a0050004003801800054841e080c41c01c0d00e150096001000c888408000012141c40040e12007800141d00c401c2251220402d500b10f40700800c146802d00304100164102d510095503070082024031004612000c00d0f1000b591a00c1c0d10402e035504001d0b0301959108455070700a030401659a819907000b0440d0a0002050101e040d4204240e40004000d03650592a00401c035030b040c2c00010b9000e4405903104000689413100012980080c44119803a50220000b002d011048400041c904018444168105400c0b2135000005000741d90003114807400040524440e4422662075402007a0800d1000400105001d01c0001814509100d01075801e0141c0e01d41c040a52a8840b410000300030030403480c2c00940807801078018400c0e04000d81540102c45540e032501c0c032a12040740040f605183d60f079401a41c41c6000e10701813203111000550719078076141417280008100c5080c1da41110b041100300411030200a24540440d0200c01d8000c1044c05055140d090040c1d0740685070b020440400d240840b20301d0201c0c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342785899 1250 342784649 342784679
    0x90512011803051b010513060b092701110f131203090501120b04090b06030c0d0f03050c101b03050a090c090b06040801050f040308090a0b010b1c1a0307 67
    0x40078a8002210510780d038140c0300d03500000c0800c08068814451101149000d104051080041e21a002d81080150a010040340c1000004c10300820383c09081001207410488010605078254400c103601c94280042d450044c80c004d41c08050b000d00000c0d8081140c8615000b0b0103614900c3d90308080b440ea034418010625800707400c0e0080205008640400903036014640d85400b018009902003101c1540d1000181122100f0f601142c0c0749480109204603410100411005402d0983c1c0250345940f06486120100da0071200003410090001600b00001c5401c1c800c0b9840305411030b40a02c40544045c5412001911001070000041e140c4400600b0303001a0f4020205810b0b0400c0d2b000d040c0b6420a50584040d00c3c2c0a0b82d496004402000f0001d05141d091240d5441031050000030724003800c051400414000014026450a42c04120104080740080000e40d044900100c40c442d40c455440700c143c00c085003104e015070502e45c500f190a14541c0300c0102128540581103094800407038584400000e1004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342787149 1250 342785899 342785921
    0x4030c1508010e010b03040c0509090607030b0a03020310090c05180a140105060d0b060c070e0415230604060506070302030c0705010302040f061b0c26060f1f0e0709051201 75
    0x43e02c000100880d48600d801035030402d0055074103411060303c400104c0c000d503000361400c038070381d80c0b00d2801c000c01507070700d440f812100d880200d81d4000801e00d0745c2c00107655003100c03040300e100c1c031a41d03411540c08010b0440140300040c0701c060090000140010000c03045c0c140f007200d0160800341444500c142560307036410128143c42004003a80e04022010624500400c0c01240946d04010108289918400d00f044450700030550b50341c208003145040d203030a240301444032400000850911090381e03030301150a001c4c02c069040e5800449030356610743c0b0000c0e0141a4076071200e41c11040c0002c000003455400302c020b0455600c1c0703a0441e40307881e40c1d540c0110100d104622170150b10000c94441440703128411503440d0002c4004102d1030b00350700030700d0311a26400300326544440805507440b5942d404080401541030200a11311018040e10300d0070b00b01e07030300301490000d00c050f43c0c2c0e0f00040c100780d9112160b03201100c003034a20280310207014601414064411000c6002d0a40301e1012000090084c8005001e00c0841d48 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342788399 1250 342787149 342787169
    0x6020c100c080d06030c081e0102090906120109080a1e02060603060115051e270a03060207050f01110d060803040b040b093d030203060f0913050304030c150801 70
    0x1d0281c542d14060703041a002441215140d4000001040b58481000301901c44000508456030584003520010b86181e0b02000345a401070007480c0c241d545070242c15602041c243e60180401c50390314110b50040c10010380003014004040360a84a0302d5002d0b640c0840c107a440000e103021101803201c00c1e6501d603030884a040e4182d20240c014001c150801d0180c480d0700301242011820f20b5001045418224202d0108100015010a01110194071107545803c180803134043c48010804500218203c1b60280c0000b030401a00068210200034040040c2000c400901c0020400810703a180811015806207182c148003505180c000703c2d186002108035004c03600c0c599541440e081c90314182c0d032a0750300b05031520769105424440301d600c40e0b10200303c4d4075511244c4d020760b0903074058181d81826007040e103e13583c1c00401d4414000c000142d210b0300f540d030684d00c104036078920303da5072006031991581405071402081070002203400400c10408071041007d136030b021194071006030381c040401c89071814244139100b091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342789649 1250 342788399 342788417
    0x100b09090d0e06090a030f02010915050403110f090a060e28050a060b1606050c030105210c180906060906060a0c0203030f0703120e0f0a02010518030604050706020c10 73
    0xc0c011030b080032030200007400250510040d4400901403d0040d4410345d41c503c030b10800d00045691185000d00a8030003030001d40154210760340000d02e41e000328040181841d80b518410411a503e006c0075603125500101001c0803890114052400f03440b4078800c400741c01061070082000c0641e02101085100010f00f243c00d40d294120705900081c0401030030b191a825924800800c0350317544200200100040b031082c0c0c031040c4103503103054012180c0041c15080c5000052006219940d2104564803c1000344c054805140151041c0c10f418904520011035002c10a140519406c0300840e031514454214a015240b071b568a190a00c455440300316521503100000300082d907119401500d40102d010b0001d001c072420f00c0e030581030140c1a03074000001500401c0d00000240594000c50003829a019800382c0074103e59400000901c2d61103080050083c18480b01080c481510b10500380e086075461001012100f40d400c09052603034480465014007401070148540b04056402e1140c0d4100550344141d40d00d2810f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342790899 1250 342789649 342789673
    0x30e03211e0406050f0f09030f030c0d02010902210c030712021c030c081602030102071505090c221122140303030f0a0b0306041407090603050d0f050d02040602100b0909 74
    0xc5c03a4000a0040380404051001510548082100100134016440110b80c1d451039050300d949455244600d1104581c1081d041500580394004c60f40720309503610103440d074016100040c890402d542080220381604c03815034000341c5e48512650707482c50b1328000d43c1d40310070720b00410815282c40c07080d60a0150120310740c460000000381d01e1034004c00140940711000101e07401d00c2d50002e40bc1ea4000502500c2c007081601c800e18450754548a01900155104000c0c0241070440c0b0219584003c5032180010064800b0a0070342c03204031941041c692046481305465943c14000708400513a08036481c00f80304078012581c0814030500100b610214210010011070950703540d0f070034005085000038400c059540d1103034000795031500d003002640e00841c401c140f99000064460303149880c0c01c81a86c481016281400b408101181000c80d030740c8000c03100b07454560b0b418101c0322001c4d10280306400301c01a400340300050004229601151208030000070b03190900540c4204030402405a009551408040d0801c241403e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342792149 1250 342790899 342790927
    0x3090f1511030c0405061309060f09050a090201020a0213090b0f040c060903080d05060a120b0712090804260303180625030507121401150c0c03030e03211e040605 71
    0x4000c40e07021b10f004e10043c3c481150b00c0c141c650a92107202c0c1e4004041c000e000c0d003101070280f241d201d000b00700c0410015009400003552e8002014019000b41c076031006010402645400604d886072f080062450b032411310066805107400d089800b80c5042c505c0d114040790301031241201c0000c0b660401241410035840d80c071040001c00c0d01078015540255000000100149030089821410b8040c1000352454a4440b0015111803129944042800d01e0840003500140c2e142c0295000d5034202007030031001404104107a21600400c9641e000503110200801c007601c0240a503040d2104013500c15591981c0b07aa683c000c6101458a20881180380501e4030b810a46100c0d9202075031241c00c1d4076181c00c03d0040342010700c2c1100e11404562a100700105c0042c04034141003207044c05024603c1c03401e1b080410543e10340c10402c82d5036000080420800034048001550100b104440100c41415441d800354104035080c42d00d540946401d01c59015150380c0036540003281d00a80b021241151600b80c600108110322070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342793399 1250 342792149 342792157
    0x10206250201021201090902040c020601050a0b1b15070e030c01050703110a12050c3a18061d011706060702030a0609030201050709120206090405040303090f1511030c040506 76
    0x3004541d824001403c40c1ca84503020036000704540307207000440801d240140426102c5031402501594000782c010001c607281c50151108840b9010070260301e0340024000c2e104040401e1100560904c0b07500c00051003080c4124400e0b0060f009500c410b611400300b03000b495111503030709648a0207c1d0090224601090044c1e105148a4080c00d055920600703096944110b03100c16440c9070070000348046180071000004000e0100c0b40e40b095a116480c1e0a07140104641d0014444040060340180c954940b100358026a00010142c081745c420034103007034460303a004084048100520341090b8850f41d458540e54050b001980740820308441c01e032101c1c1d5034001400081ea200768001c0307030184222105080492100c0c407600714964840d41c00070401d030030000402016402944c0254a4148420600d840141c0d90103046440140340cd85002c41c0540e00c5090540003041c2c0c03140c001d001c40108100c2c1d00200200cdc0c080743c8400707403a2220100008007020b60a410a4001100e980090305010030080c4140c0c074100000e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342794649 1250 342793399 342793471
    0x81324020c07061b0b18060a150503060108071a1204050d120b0a060311070f0803070305070504080c130b180a0e030702030a020d06090c06111903050904110d091104050105010206 78
    0x300010044030303031b04545441e90032105090307580e5907190704038400505c40307803004001d01c1d00f10001c1880b5410009403649a254921851107600642400c42407282010302c00e40e80c001e450720304504110f01d8642072003519440d8501010002801e8442020801441031040324040369000c0d10004042d400c00000380c0c02030070060000c40010b0000d01c01000040c4c02001002803880c494594a522428102c1c006400d07248042c0182d0f0620034288400c3c0400a0000350034010400704840000742c0300320050710b0f9001021028001900b0100e01540013085903486154240900303074000003080401d503012a065141c0c011840021741c9a0480c0000c9400f42c6042004071024030f0144100158210a1b0303a500344503070103540d101d03001045c6004120641c2060034002598080001014001100d00b15680141188a06071006200740c2e80c540b0511340e4850081c054a603049c105100400c10810b0354107004514190000c0d48510542c1014000705080d4408a0014000d85e030031000c901c080b603000005551000d00d13103400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342795899 1250 342794649 342794671
    0xc030209030d03060e0f1311130603030302090f46060807020f1b100309080c070509091207030804050c0d0b0124081324020c07061b0b 59
    0xc0d40e50038040c0c40151101501c000541c41c1c0380402d0344c03081da10002c1554044c20300c4c4a0401001810710b445607030b000380d0310222548140d01d14500140b64896011074034030880d480d0140100805170503178028201c03020115038110028803000204010a9140d035110000d10168854081484182c1c0821a00082c060341d0041810454110004000c48065001d20f0000e00d002d01804140740e01400207506003c2064081d202d2940039400f101c5085009243c2140102c00d1243c0c40d07031f1400e00c246d000c0a569540808000c2d91442c014501f1552070b42107002d064440c030086404036403644c40c001078003a039410000390319500b8081642c90039241c1e058020300545040c080c3c1e0a900031242d60390b180d8410020701c200a280c10a50400c12141c094109188801c14a154001d0840c0c034002d030061401903201030740003140e40942441c0d19207810590840c007114960010000d0003100c41030b201e90007038494151030004544495a45a000f1100d680501030b040303448a81c49107510002c902000c03004c031385c072221000c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342797149 1250 342795899 342795907
    0x11e0303020705010f02251703070b010e04020d150c0311090307060305040819020105010317180910030515061503150f180f04051605130207030e030a061e050106080a0c0302 76
    0x100c1e202000d84d401d00c403407003c0807001e5001d20114a140107107231512080da40065003040442c0e0380310010480706028107210101c40000140c00c5556410354400b410303912501035411f4482c03420b007041c09020950740d480b010906003a01240c803481080c0030782d41c610400070002e20304c0c2403030704106800800c000350043d240d44104214070126030035140459000e8203103a83c00000d8640c95401c1051034542188030104d02d001041059031182050410b2002c95050202c1c0c2047c3d068840681c160070a0038958001402801a4601040501061007115104500c2603403075420b1900d1820350b030310f00d070300c0101c0e0b00f0400a4445203d08003541032848402004170320107095448c0c251a0100c1840803000300b19a4006401c00300410041004001d0104512071103561414680f45420500001d0120204841110000c2c1c2d001c1020010f151060450880c0d81d40041e0584451002504295010b4000440980744649223000b02070708603001441554122909542c601c5040c4d1602013207c009460b00d0028141015002e01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342798399 1250 342797149 342797173
    0x30102040f08032d0702011d10020606090603060702070909170c061017150916060807170f06040e25090f060303050714010908040608011e0303020705010f02 69
    0x8421280581000c42c001c64540c0c080f1804110605484903002c115103442d2404004010040303016a0941542400c051074014000c02501354030b800c160210552100c011480000c03841c0e000300341c85000301001c0d9038510032641c4e00c900307041e540c0d407082c0c561100590000d4001c1005140c02e911482d12148100d10380707141c4a40d6507a02061942080381d5640141d00003400f0301c1000ca2520344004010700b5040140d00c41c1080769a030032a1100b040c841058110b054940c00074800d18414000d403448142c45001c0c4504c01603d40e0700c024145101191240d001c10f41c03d0501c129842815800b092203003c0d400d0741800c066441c80c2c140000f0f0044201d030b4140c03c1c49035070030703504c0c901d907191405c6840c01c100c88507410130f540e2600048200ba540c0c55211010018600702c01030000c60f81c00021156100e82009429106891810725103004001d0081c02034003200380400c000c146181d104510f58100c40d1006140111440040c025604500032448010301581c0700420400c003d502039514445c40701d0160040e500800241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342799649 1250 342798399 342798419
    0x10e04050d1112190806040c12110f0a03020c0d030219050f0c01050a271722140a090c020c011103040807030f02090714181c11150a120b03010204 64
    0x144000e00904c0e4084102045403d500601c0951b11400481e000e11440d82100c4010308030b05205141c940d00d40b40c80f101c040140050360012a00d0034400e000c002590307200d150b074008001750401c0b010320016000302e0004180f518420300a840107031900e89400650704000c090140c44a0303204400d1410301040500409125000030300c1120b104100d103c1001c0f0f410550010400c140343d01031001241603c180d40020070104081a8256918044502d1800c1d514080114071119860030700c8051301e406498101d0124144d000030b0241c5200910540301902c0c0242c48500010682d02100100d10040c1d100c1d6030f007030030f440d8030442000b0800007900b0b003074030315168460704410700b0040d40390020340d00100751025030702c00c44c14000d0840b5417080d0503151002c80384143c02000c02c454810017610924211406102c03a103079991301220494900f41b042c032408541016440c160710028440903446200f65400c002700a00c1c9040a0308403105000c0316502c8414030044040e040b4024840350064030303010b650038800070480c4406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342800899 1250 342799649 342799657
    0x614070c0b07060e100c090602280303020702090a0b0a05040e030313030e19030b15030d050c0313030b04020a080c01020c0607060608071d011202010c080903010b0621010e04050d1112 80
    0x544400710303074800c95104c0a4001c01d01a0b108e4011540b082020a0000d0204166005865000c44901c40140404d0500314080d001d055006988040707603005204400d1000d5100801189041c0d480c100b905540c0d81c200412144d401020600c2d43c1c0042001820040441d00c61852840c0301e4100198940803400200c2c2010801c4c414030505448101010700502840314440c42d84000402001a03035582c0e1040829282d151941c1000d042c40f4011070b1040d2001d80c28004d81d15401d094281c40504983e99007010740301e1034000d13141a4000d9a40c2940802d500002144c0700e6080001030b001816011040b20500c03196502808003560345030340c1c40c03001042102040c420b01000b081081c9401c000403a108818409004069102c07080e0b503800e07004c2c03000051360400c440001440c1c100078800c2e294001c2602107400340140130b44035544030100103800c240350100002400340840741401c105a440c0e0b00c40c104000040070070b40c0d000d00300d0b901958400c4200c5205440c03450000b8204001d44450392440440070f600340d08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342802149 1250 342800899 342800923
    0xf020d080406021f150303053a0c141602030a080d0207021003090b0a020304030513090c0906050708030c0310080109050307060506031c050906090315010614070c0b07060e 75
    0xc0710781c0e07450381d00a0b04c40650510031804000c02141e90750014030725158829202c001c040c0180856040c2080344120449544000c00162440300302c40014607420300b070800012100000d61401c100d210000d84a680c611810040503d803030f6283c101c400c0c241c200c01d030320078680c100c1c2d15120b41c10843c070000326800c0143c81d62880100b4007507110706031481040350350b400ca002c0200406250808150205001d852100c1c0c000101c1080103030b0342d8460707040c1182c182c445c06091414105400c00c001400035819803100110443c0303a952828065290030045460748241072010b0980c6400b400866680c01804c0700558004044001e000c0420381c2c0d54009900b0b40d0881030381540e43c1e0300b010421405202e29405060781c4050114050540700d100d0005120b111400c490310982041000300c1c0340704150b1150011140e4407240102122030116200b2a60306801009000d08000070780a42c508011940d0382d2000c0c0c86505901c542800c0025040c42e6201c1010b820042041c0d40007615201c003900c081c213082c0100b2111038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342803399 1250 342802149 342802153
    0x903021e07090f0b010e0904030e0418121701080309060717091c0b0a06081005040c0f0806150102120403110d0614040506060f0102100b18180f0a08070f020d08040602 73
    0x940650009440e03d000080f501f40110040410400003961084c040104000c046030300188410070219038180702100703100c005240e8640b90b006019030540211007100030040006444600da0b8849036202d46a01440042e0341c2c1056003403103c000003032020120100a0003030010342c0740c1403000500002d1010300d0341103181000711070181100010f011300c43e80c1095010102c80380c10301c0007a00d08210b0030380e80c4c210101180e2600341e490000c10108541000203070b0003810306410039140c803070f103030b0000e6070b10b4003030a403080d81d08403e5010006a0b19400407a50000121485110605291440d1145000c414910203500c0e480741400000c000040c1051080d2200340144090b14021840d10b482c2581c5000c102808036480742002d02243c4c01e160b03900041d0407409035000c600200b0510000e401045900244400501420000108210540101c06103585080c9a01c40444091100c20b1000c2a122819060b02504042081192901003107100d81c1c482961440540441c4004100b5104d40c0e225406c1904100300603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342804649 1250 342803399 342803411
    0xe030a0602120115020309090c090301060308031e1501020309011101020d0c0507060f0621050a080f0a0f08010806160507051c020d03050c0a0f0c050105010906030201080108010903021e07090f 84
    0x18061102e221400c650903170000310f243c860442c0015a1701c040c01030246507504c0d00010155000d4a007074210100850703006030300944900708241d1400c0c807100d801000d103908030b18150028015004000042c04940d00c1a000f42d4034040301d400044500e40c0b482e44080c0d8441d0f40820607640180030f180f02d00b2954030f016503102e58454002d858038038160b030203144213010f44500b003040c00c3c0000e04400c14a48440031403030a0039a402082480c085042c02c500103405040e540003c0b4440040900c0f51005040d012070b0fa41c2d17001d84030310000c1019580b9003401c3c041c45000380d100170002900403660380d2030040300310410708085e4102062070b900d152070b120768141e188081c8180b104c0203100164040002ca1115071090600340220726000d6211080b9000c0d00c803980c820402542d5091000034003441c178a105a80d04400284550741e1201e25100240045104c03c9001071484000007031b0031391040c03049202d25507040c1e014080080d81f02c030322840d0190403000d01000f0740c000c1e441e001880103007500c0384045c000280c54000c01c0c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342805755 1106 342804649 342804659
    0x915090608070216051e0405010f050301050f010b030604020a1b05010c11070617060109050a08010902100f1e050405100306142b06150e15100f0e030a06021201 70
    0x20908e4040042900c03101308584201303441c400d40080c4030700e0312242d4a420008109100700094034006001043e80c0f898150000c1805445034079242801c98240c1812040c00c0460720000c48190b990303818152603064025440400f40043d00d030240104502c0d03d14003808e0600803140315980700300c21030000b4220760f0160701254003605010b80340c0d0710065114007446009202c444000d074403038900301c448520124451240300000c00d200d50303200481401c00c1c2103100300144070207130f6800500c4005c5c080880c0350340303078901181e0782101031765008600c15207010b42908207050740c0501e04e03015007044100d81151440000040c2e003182c0c1401001c011000740ca00303040d80246512000c070142400c3c1120000364a907900c001d0346014422480307600d00c3d409100000c00c80d0501c20408004c0c04290f0603407101210f68052950400d92140140c10785c0c0c0d0100d819680c400032070380110181012943c0713200060103 = true := by decide +kernel

theorem cover : BRFrame.Cov 342625899 342805755 := by
  have h0 := BRFrame.cov_init 342625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342625899 ≤ n) (h2 : n < 342805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
