-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:50:21.155895+00:00
-- url     : https://prove2.me/submissions/3ab7f3e6-b8ad-4037-99ff-545024c16d3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182194244 ≤ n < 182374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182195494 1250 182194244 182194273
    0xb06030f06090c04090903020102040305010c0507050d050d060906090b030c01090506120402040923150c0d0c0c0b09070612090b010e0a0b0411030901050a0b010e0409020f03100509070e0603 83
    0xb000030315510701c103107003040007041204030f91141d1221180607500040e1102d08600e061800c5800100581062100c10720014000580014001070010b00b2441c01c0e03030722581c1e4030740c1081c090009500500307641800c01402242e5a15294020a115042107044a070307030024100041d46d110319030340a05504508104889141114036a160030b03042880031b80001074900d400d03200d00c03924a1242200c0f800d070050666003050098420441d40b5a03650488101030b42500b40100c00c01c0807407159a808c2c0c1c800640360010002e60300e000700005801a6008610380045e444c01e59030301603e440c020302400c0c002c80c0c509107100c0020321541c80b91000103030340f242d101d540f0b990034880d0003007607801d00900224150f0784840321690280c80e40e024929140c0a03100381c0c180c0b40c1c00c01c040200d0a488004005080c01c9140112203c25a0f9010388200350f4402d040d24005281c8081d400440c81042250404c640c0510802c403094600b0401030303218034171441215081d25852504c1e0043e010560009903502e9a25601811404240300d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182196744 1250 182195494 182195509
    0x5160518030a020604030f020a09020c0303060108041a01061101060f0506092e020a120c0b07050f12090c030705030304060c0b06040e0f0f1009030504032d060f0b06030f06 75
    0x18000182103030480c1c82e50341c0c0010708961007604122840001c010f0074404604001c6001c030050a141d000039410072821800c1c0c03564070301000789454104440302010a09105040309482c58000342c03000598019a11410040c2074907240545880c00b175807914030005481c190300248042580c20003440e403072030803002d04200310420032900303100d121401404410400360950081149034040f21a0042c4c0401d218504203e55282c440c6442102071200080c0e150000402011049600140380d01385a9200c44000202501d540141e001505e85200307100207001c2003800000d510714040c03804804580f202c0d515081812b40380c0c055440341c5404600c21415000c0096803443c803403580000c01402c00520321030702400c81d07480c00c02c070f044541c64140c002c400d481040324014441142d5030481c200040c059254140d400500d00d205920020b0102010f0160345032203074080c01ca410b0006840e0000100c81c90000d4140f8400030300c0c8482d5107407103070f0b40f0b803111008480c1400c0c0166442030384d44c5401c401d0310350345440602401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182197994 1250 182196744 182196787
    0x201140f0408070905060307060e090f0705090303070b0f010909120f0e060304061e0b100c051608030309010c02010b0d02041a060d1a03120702270403050a03051605 72
    0x44840c140404950303280100442c00080c01c181070042168202a07083c54180602030f040071040109807501c400d5a170701d03108000ca41240c3c41e01404034203640e4001e0100c1d0706001e031509141d8140000100b40050100031654607028041040303162080b40d036161503910071234002c52001495a00c3d00c480c0c02d07860340c1c01480020510201404c4c0990303005185000151550b00441c0c04483d65592032102e041c0310100030b034405240804111082040c1e00e20301e00042d0b00d0602d82c41006080203003c0c4400d100300700e07040c003a0f00010000407070b40340708654460007111f841c4c0d0000c070b40c2070015620b00000c081c1144c2c4140600072045001070720003100b110160b02803201401074610200c04008200070311240646840000300f482c000200e200042c0c00c481d000340e070034613600703a416064403a038449a0304106040c16007040b100c155a0440f102c0043e02c032410000c10345c1c0d0030040c141c1900e04203020300f0441896084001001244c203140e03000c1200d940da04542c68204071030401480e0000324140f26103052224181c850410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182199244 1250 182197994 182198017
    0x903121b0903070902030a230a0b0f04020a03020712050a0801061b050625090e131403040b0d06050907090303030e030d110406090602070b0f03100b03090c011803020114 74
    0x162107000008a807920182da40b25107142c1e5030000c100584510240b04584494046850114400c0c0c2a411007101d80c440c0034245800d00c695440c0d00d5695581d4100f10070205040c0500150b407503c4001c900900250003900c07050713170001ca007421140c11041c40782c400c80311000d90302c3d1104040c5074240358007142e0940d07111011703215100348a120300c0041802000018420f20b0f5401c0380000c1840ea803614070f050042080c07c0e00c414000c02401c18000c0c11044014554401c0f44c40c81c2c201c241071075034181a8000c040342540200907000c0042c010401c07480300001005100c0c030211050105d140c0e29402d0180e5a2000c85628001a004900600c0042c2c841c0d00000022054030b011a4100041e800c8018220740304d000c4c1c03d00c0c000e44001420003004d6008541d40008140300e00103003485d186048498801481400521501880000b0014111210700c0c07401101409002585030307101d103400d0600c196101e01503c44603011501001e0745191400001224030152a0306944003440345a04013400704c0980c0100c1c84860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182200494 1250 182199244 182199247
    0x10e040f02030307061b050c120c030906030f0601091203170406021e0417120403080903070e070503060f0f130e0a0209040b04110405010f0312020a021c0b0903121b 72
    0x160b0350400141204501407440042c060034900801c0070502800c0042c4014020144540482800c0101301100070742030200c01d0581d1201c603102558118070482801a900074004801d01030300007120030155114078000e80340c40086540b00d414840041e6098a00200041c00101c1c0070000d507041840c015810510510016003450044500d20010034003455964104032008101040f4a260351a08100d0b00d001c06000761120200300042c0410600c030301d0201a040b0381001a008030301c1c1c2ca003007000b10028160f04d100c92407541880080105550320681c2c01030b2040706985454242880c20441e066848400144080800c54243e0381d000d0181000320344184260080c1440d010158135241c54561283d441410600040c2c80c04d40341c414040d849412145000e40c6c0707020018046a40c3c1d0b0200034064980009091403c202c0068081b4a0318006100c000c0d00060144840b1003050705600c000140140b003406038401590303554040954074095014000150031918005c06d070005040b94100003900305101429 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182201744 1250 182200494 182200523
    0x100c060605042f040501080c1b01110405040c1701061d0405011e081903081504060f0f0e0411150d02031e010501020c0d06050601020f0f01020703080717010e04 70
    0x40c08403145005040300c90000c42443c406041a020f04000410445190f1182460b0504000070400800101060b44400e030000b243c1c0c225407003004407074000d100880c000388800b040307040e81180b8642141c40b46901590808042c0e000303150080300703181e0815200000d40c1480368640502211244100846103c1403a604400d05441c0e03121405098041c0881107502014070300283c0300c05140c480954000d03030264000d58800c00c07000b2210f10080d100b03035415207881c0340c440c1c1f500c65032150710249010aaa0b801403800800051160f0080620012103803a98951010b03655548161000007008681c010300f4080750640088152038405402d0f8034119950f41c010342019091a0f4100481c1d2040e900707806540b0b071044c001c60300c2503840506940905020300c0502454010f24002c90320340d80114200600700781d16a0005801a48200404260502c226085401c0400d811800d41d000394003442c0c1c20b40024559a0005405600803402502201c00300d02ca40c10341d9a29100714106240e038094011201041055401d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182202994 1250 182201744 182201749
    0xd0e13061d0106170c0405010c020a0806100e07180504020d0204051306081219030e210711040504031e0905040504050c040506040b01050414061b0d031109100c060605 73
    0x21040074000218280d2035040441c0600799a11107400b50302c12201201c104540302000109640407540282000106c0040901c00034550302c0c02604420303c3c1d4440c2504004545800441e00070490303111840071f003030588a8900c101c03218060001c500f80902244401000b4600b480e078001c040c40b6440700720040c14940c0b2140080c07200808010aa214140c032580305011604042c403000000c4200c5680c603902d4030b40d409200d0f007039418941582d9000c1c5a41e45001800c905400e01c1002c05012402d07690640c10518141c0040540c0c00a00c000d442070310442c3e400c1070301400d1600c5418003c942585504003c0803024803c01c5a404c8445004810030100540004081d1070720b000b4903006030b1080b4060501d10082c98140011501d00a210b00d1045013001071036111a60444100d5007915644509840d0360030003203010600902c20010290214a8082c07200503180c1004158141c8030582d983e01072241d0040e40c042000c0340d0103410700b0b481d80183c0d04854855514000c082c0c0355040d9104400205203169075000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182204244 1250 182202994 182203019
    0x5061806120114100e041203020c0a0c080f0606040606021504080906070f20010e04020903030708070b01170616030b041803090923010303030b0607060e011d0d0e1306 73
    0x1c9214046607140510903140360b01415900580301c40d01005c0c40d0341c58075840351413007000c2d0740301d003201499800504506049001e001c4905215007000c18194019a990406986c0f201440002c5066001d0100402c600e0324060107481c00310351955006080d80c90b0a00110005500081c1c42100d0021003000200d4244e02c030b14014144c6140107a070780714075403000f42c10500c1c0007044203000c40c0c0035443c000b564135500b40e03040f42444010301c1040c0d03001a200d2403540d000c64030794803812401903c00c042c04252074007040640f0310b0803416501c809007100900c2526551082e581e910542c2c4600d100100f14109c2c01855100e9440400c14a20091002c80d071000d03200e0501100c092070420070ba0000385180d0090003030f00840c0c0150b10740454107184100c00750034030661007180c005042c040101010385070300c0b0405c00e0740d41c2d09058800894001c0020041100b002508500a10781c0d0800716124800c030152007002c4007004200c1401c2502103449507140340e40c442c0300700301103071f1075000503842095501c01022a007140900c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182205494 1250 182204244 182204261
    0x30e0123030f010602010e060114031906020c0f03120f04020109031203090c0501180918022d040c021e120705031309201e0a020102030712050618061201 67
    0x10348459403414151200242d800d0160414000d580c14680d111507040300c00a025411940e21155039100c5c000c1d0300c00024108013489420800d840d41c0d070b9000c0300a00074a9030086c6401405181220380c0c11b6040c0c0d03041a00c9010324210511085040000134090860564003658400d2051504d0340000740c880d030701d81e05102c106602800000350340b504181c0407c0301500341c1c40050301c001d0801903214008030040c09120350b031600500030b0440e15000c170394003d241e0b800c1c481800c1d150300074a10180103000e900d0b5000c00720314140e190222029031a2a6001d0303802c062140c54004040c1d580074080d035001015030000403901c0580884028880c0ae030004042084150250621510513800f43d07039030700070340c10014402c40c005421810565207449200303890000c4180a48034a03102d40c00030f2645890000c141c00406000028013100e0082d00040d900741c20360350640c0210302c100c0042d10344005d542c0400042e40115242141d00c1c580154210b4028620b028054514035800840180407024255031200d001e800d4030040c2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182206744 1250 182205494 182205557
    0x207080a0810081f0e011b0f0e01050a080c0304050a061109030609060f18030f04030b0105010810081e012403021f02100b0d05010510091d0a030e01 65
    0x76400d100c1000b449000440003072090400030f000210b410428003a1408004121000d0305641d091081804d031400c1d00000c00740d20140c030002c1c0e540e040008000e0b000c146400c4030035000a07242c0001a0300b541c0160181c8400036219940c40c241c1c0c1e41c40b40f60b00f040f2984058010340f1a8400c8840103400039100d80aa6800011000b40c0540c40352040814180341980107080c1c064907800103020041c4022442c40500c3d403044000901881100d12400b40b20304621a921200842c840002008014008100d9800c0d04a88081e0703039484c105c0d65071000b0030b0320503440d038040d84401d6000b9280c54640200f01c2a0b091102c840300c0000019010443c0c11801340510f000403054240e1182e1900800030762038150071005403103c040030316042030032001c14025110415084030390082a0f8400340c9042c1c43d1030f40180d840140e0381c0103000f003101d814541102001070502d882890541414041041c401211070141e18405c2081c1100500c410000d55406072880c1c1e0564032040d041100200c80c8420924040c0508102c40126 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182207994 1250 182206744 182206757
    0x7080114181b15130b04090b0306090303041b0e0906190911130f2c0316030305040f0b040303150803070203030f030c09090a0207060f0204120b0406061806140d0201020d030509010207080a 82
    0x41187c00b0050b20f14084545102c0c1d0054010008031100c0401103d03032003030344090098942000011141104003054024251004d0080204038203140c0c0082e0450040b0626041580c105604642c1c541c280c075211072009221205400c0070148900342076080d142c0c800e074a0340021541c602d401010b03000301c0314a03070300f0b000004102c005e4584808410b200402c550502040265240144108049205a0030031400400305542caa000034240509418019a4940d01c1758650b0007038142400d0040141c8551600d4243c130b400c40c42000500598004101e640c5198040d020750b09042d204211410180c00040461074401810061206145d0702c01d0036151141c3c400000c016100c0116080c500211501e81d05c52480383c900c100814845d020b540320410400d50b5201200508658440c40c254000d00001d500c296070220a000c202c014070399494000030107a82c01e00d4100d01880b0406010002d41503042c0a000e03015802130566001038134460b41100b540401d0850000d03207008120340d03840714564050380149000481c4c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182209244 1250 182207994 182207999
    0x20d14250c050a0e0c03100e04030e102309030a050f0a0b062d0f040213031a0c0f0a050c06070c061a060a050a0207080114181b15130b04 60
    0x4824003900644000d5032031943c000e09055600410480181a14000e81d00200c00111700c22401901c0310050054200328460504041c03030041d20084801d03000c248151440e07042c030034010703100d42ca00901c4000e80800c10060039408488521655001542d40c81e00750051796803c00110750100302104540b403155008141d01801800c0c00404044c000e0302041c4598480c6400c103040740f000c2103043c2e000d85500c00f0062401d0f003a0500180240300181c5506030000d0000c90684100380c441e031005001c0301d0140305903689221082c142149079110440380b450514105001010409044d03a01401e030701c0c440d80c20010320303000340007c1e92460007808a51241c00035a403803d0840c1088028040c04448100c8002802c1601d8603038800107640303000e84010390040000c00300f9115203e51080100c6401404488020440c1041048840303409040c1250140845503d40140003d420800102000440100c0200c080744035200780802c8400100504041450b44092002503080010050620020024160126541c3d40b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182210494 1250 182209244 182209253
    0x4020f12120a0f020f2d0c0a0906140609060a0e13060b0307260105011d040e0304050906030a0b0c0304060906050a0c020d030212040b090f070902070c090606020d1425 73
    0x440c203401001903802c500c1c4400c08580c803040d0300140030485001c01b41a044101c1303004924103102c804078294450038180c070005500d0b40d01e40c4200d0558481d400304594030f519040500606100b160b9026070009410005096a0380c0708410328009484010103070051840610f007000151003840c0c024a04031103000040c002170302e070098000d4241d00c00d80c00500500f400b1002c98404e2100c014441c09050040c50050409000b01c1e0b0a10940040e10042040103d11941c5503034a03500d0b00b00b80120b600900d101404680e043c0b5001520b850740c140d00c00002c0200756200d18205106030000707041290907944a5040034000f4125004061082c2050a00084c821200020003440c00008121030300502d48100404007142c0701822100c0d0344190004100210341e00d50800051402d0040003404482e405500d4001c5a1045170741c0007410300f0b90041016101181e15490b80c80b00700d52880c400c040c0503901290348030243c4e03802031803034046440043d84801e0400d90f1040c030383d4055804858080c0c0055003120840820003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182211744 1250 182210494 182210503
    0x90305010b01092405040b03251e030b0402190c06051e04030311070204090b042604050405060d05060112060b0303090d03030b0a15020a170c1e010603060c0e1804020f12120a0f02 78
    0x1413041c5040102100802e080030400d0300f000cae0b83c01c0c0806894007022059a2078a80486141c051a5240402e003c4010880103103c2c01d042c40044a9150900c0041001c4685944010180c020071f99045041503c440d90160000e0007010441c140c1c41d20240b04120140e030b181d10500070702a00889501e10a4a0305181584403030720103c002c800380e00030342d41823004c210302204240c80c203459094900103600d07103a540000b02e40201c13140d0010a940305007400400d02d2102c20804611031440b813007040c490240c02c00101070310707809001d0300a60407000e1080703c2c50119109030024410300f240a4092000161240c04c0c1e60114030a2941ca0005070740160240402c0052071928110a0100010462304000c1c10300324480c0c481d0414502031020032081403444910040079408203004550010003003240c083c00301c1018205580004905201e0b40402c190200140c006190a500c1194002c1000200111003400c02c03140c1d0150340c03c1c0041074400c4580300384c10084c0040050416511035180d51300141841e40009180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182212994 1250 182211744 182211811
    0x60a0f180e06100314060d11030a080c191104050a0f060308030106120207020a030305031b0301090902010306060804020a030602130e0901020c07170c090403120507090305010b01092405040b03 84
    0x40514040018080780895411740d03404c1030040710311482d2141d081c20a180312000080a003545801030701c00f10010840000020b024088806007030751480d20043c14114000c4092807409011071110450040c42450540d011581c40080c00c8400200c41c1f000100880444250780c10844006900100500c81290031003250a0345006940c82585040a04c0e401300301d0090b00392100801307100c00840800d0490f005800302081d01a100e10060ba225a910019607020f460850400d030b0100b442c11350040b034070074030550140d480340341c02a203685200c0d07180d9605e1900960000030714480d0460301400c08220740d0b465052040c004c0c0485000983ca038620706841d42e08185a550014034021031103c442e040004010030091800c080031208001316942d541000c2ea850440a40c01182c0240303014200650981c126511a090320300400081245103201740040d5030104250051440f200b0050440310030000f044c000c03030354142c0e006140850030207944142ca50040e41080d6506207942d160000c000c4141d0424069080c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182214244 1250 182212994 182212997
    0xf0303061703161a1003021804120f0e0301020409021e070b07120b0d030203030a060806150d0f0b04241b0c06060e0115020c03010b060a0f180e0610 65
    0x10322440c00c0a40c0740d581c40b034142c001095540300703103283d4140102071001003203441c01c40d00c03004107503d0701031824103400c2c1003400120722541100c400022070b19410b0004a00c201d620421000151504130b200b07884c06400e00710780104110060181c5003203038400b800544010852401c01684451007a03024046a407000141071003942818004100807410441d103941d0410b01d07c0c2881580440700b11543c501038614940640e411211106101c0c007050ba00100540c170030190080308100054031740303444e15101c4e4010b46900c03a490102c0d40d02c140d075070314155a0003151240300c1c0d5483d000e01012603030340350070080e01150140d846085004044c840b103980c2d15000e5401c43c000b140100104082021907201a032075400203002001280000360040003902c0e403040c0d0140c180c040754161103603550303500511071030301407054030005024480c40200c1505050082c3c59076420010000c03824103042c40012103840600071403400030405032908011780032100940002c09001085444111403030000c0a104405104034401d80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182215494 1250 182214244 182214269
    0x807180e06040206031324180c0501050a1707020115060f200a02040f02091314010603050405030f04060207140303161707081308060603030c070b0f07050a0f030306 72
    0x40c5000022800960150b8100c444a44135100c4180a2000c00c225400c01007102001c0c5000c100c4242c07000000d0036892540000a1124014540c01140700c103811200003000c0720000081403100d9800b400c0903014441c00c605d07003031442001c000c050120580c4203551a0700580d40d0f41c5908103684134002c501801504407070034100d15000c841c0d9801040310b01c41c000651200200f598150301441c0c0d050000085440e00240107100c80b501c11388a50000703503c0031900301e00c1034400a0f10380d5003405030340c054115166a0b054681030640c0c40c0403070503005044001e100321968001000318800c0c10095002401c0906800d07401040100d007401d41c042040c8040c841c01d244280e03c2400f41061001043c00c01e03c1e861a8410203012624440c9491b03038126015055008040c2c680100302c0740350311031100c0d03030100840c0c02610848030705844e414103064507841a0305800c1007a4018000038011004e450008240d1303c2780d0400c6240c030f4180d207515100d04150302c1070012522020040440b405044e458011140507054044e044e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182216744 1250 182215494 182215511
    0xe01050703050d0518010504030305011e08060103080f09030615151206010c020301150905061e030d08070215070c0b0906010f05190509092107080901030510050604080718 75
    0x40d1080c01000d40c241c89150300c032800645c2c002c1d01000500c002203000c40080c04103041516029002c2d1a0900603030100c000d01c0d8903881403c01c2c0d055425422910700c0e50103040540d0030740d1180102c0d0342c0b00014200e10600100007030003040c3c5041100c1441080e43c0d20349203071013034001710030024100a043e44081d95030009104500c0c428448005176504203a090901c01c1c1c103503105101081c00341c0360000c014200104d541ca00010003288030b0304414400c4408803420fa6014005203601840740c40038100276030b010f60002100381601030081c07140c035400031242d00407591040701d901c801164a5500f1280900001e003098400e0341004021203c854006a0b40303000f801b202c0d81001d4000c1c0c5e420700ea5104031031045503800320140d035100501c1d4003040a4600a8040322982c541144002d40d508038a0072401003804261400345c1440d03650000b40e42c2c0065129600b03610785410180114007511010f048514180092a40001c1070741c1c0b6a00188010100b44000e02903080c07414040202c41591074504030340380d60402444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182217994 1250 182216744 182216747
    0xa150305091b060a0207150302180409050304030209041719080f0103050c0d06020c03030c09150a0512040206090409051b090c0403060c0504030f050303040b15031e2503030e01050703 80
    0xb0741401d035419941640c4820036240100c6c0b07005c0d40795200b4120700740d803030720421942c41c0d1580044c0ba2102c502000c103d4642d60500900044604da40406409600180000e10040c50110100c41c2c109019500d1301d82c5924040c0700c1c0d004c46030710041290b46007466060045001a8201d51015803000c0c0c000c40c580d04030b6165442c1c00b43c031100c0f0014482d02c80d80901d080f0130304100042d81a0707444140312604803501c071715242400c0042c90b4440d2100c14450101c4401c01c86844071144201c1d8166003a1f9070303d00c1d0400081070f40c00759854001900482e0312200c144000d264a0315240303e111140c034091002001d5104c1c000f81c03c000590304030190680110840700070004128190b03022a030450350b0020300024000740c81601204e082c0140e4100808402c08000701c001481000009140910b0080344410b006842d0b00c0031800034140c031b482030203406401180c440080101e002c1c0b0401c800c40184802e4078210503100c91960030703900ea110340c0501e003403480d50018814154441c281001d0400203090041c40c04209480 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182219244 1250 182217994 182218033
    0x32e06030507030603050105010b07060e0d020d0c020406180504060b040b031b01020a0b010f0303030f02160b041e150506030f0616020a29280203060f0a15030509 71
    0x520400d0603200c60100c0c0c0b12510a510840007150400001c004558440b00c48011f1940a80c100381c52190408416441d05040031845090b50710098004144070302c5000c0041e0b690100c000826a03005a4a180006084101008484044c0050307800000d2900d0a80b4080080320850030b41a0b01940c5440d07024085520300003000f600e55090403a01082c3c009016004034601415060010454030f0940c00000300a0703401c03043e40c0d081c0d9109880500050000445090403805084612000c8400302c11081000c034400e00c3d00a41c11a001d4040c0d468803010308411840101d140d00801c64504143d880284208101131081c0c0b030300000118060103409420060b0607560b818003070180713200002c0d1107003c800110300030418142d5041d40f003100041400807003c4070a0301c0c40140038201d05900c42e60000540154110f22201d141ca8181d0603140b0000408060a000203410081c0466044129500c00300c510707075640a200c0d0010b05002c20307407444d0440200d000400b6540060940e0b00c1962000e600010300685019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182220494 1250 182219244 182219249
    0xc020d050d1802100f0e010e0a05101403010f0302030f0d0503190902150910090605031513020c160905090318030a0f03020f0d02030f0f0a05040f0605032e 68
    0x1180402c58402001038001040d40c4250000c0d13201500300140d240307a981020103007641038101d4a41c403410030790303510054400a42a071a0164000d0030040144418602144013244001052a1124034112420400c503541d03030003030304203818503034401e07504200310b1400700170500c0d0381400600a4941e002d039000014105000103000801e48800c110100e648040c816400b1450300d5400a04002c05030461088690490384218401406520107814500601340038141c40b81c02c0351455942c084c0344da0344d502008100703a801101e2166018405403442400150103001400c900b6040310041c00d441c1c3c81c07007202c045807103080703501180c3c6441c03d01c005c00004040110544204c41d08401400014031080300000c2e080c42600ca0303000701b04035101014502403550000c1c00724081c6005004075843c40440c16410781c0d40e40250010078648060070004083d0f41d4200c40090200d00d803260614a0520781c07603004071f034580092600324000040300402080070044418042d503031100c42d0a8900f80032030318034041d050b60f10030190 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182221744 1250 182220494 182220517
    0x515040f020c0a03050f0c0307030c02040501060503040308070e040b06040b180d05100f0605130f06060203090904020d0515090102121006050304020f1f0c060507031b080702030714100c020d05 84
    0x30801c1b0b14854044400c0300e443c00741c40c8041c1c99542c003081c9405070401c038410307000b6405181340900200b00c15000b0300c1182e019540684844049a0b1030100440303030700103081c0b90640c1003a00da0301c4400e140e80311100030700081c02c407400e01d45491301205d083c84404001c41501403481000c10003403020101d0004a003c0303007220300301c01c000f050807100b210600000d48504c1d40034a41113065182000c0300700b1801e41c022468180042801c0c0416030380d4100c126901c0c06810204c0340e004d89003202050041c0341107c4220310491081c0240c52000d07480b0b05824450000441b111030159400155076503200d6410803000d0382c00b0007280b0341a590351742444401045800000c000174002c0d00d80c58109031131035944001408451070140600600003a0078031000740301001d07605084846500b0f1401040350203000e03002d075040503c001c503041d10f00e0030b403444400c44858001500da1401c1d03000422052010440303020b0251403c1003200000d0915a01c03c0e0343c01011101d0020003141103400c01800d521203036034010100e450201d600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182222994 1250 182221744 182221747
    0x140a0903030b0907050a020c040c050d020c1507080108062a030601020106090f0605010306050604080a030c0f1b03050d1103030a0c05041e060801080102030c030103140c03010515040f020c0a0305 85
    0x1454240c0040a080c04400d0744100f6440810a100358044014180300400c0e900f41c0300100d5103141400140c480e24443e07000070940601c541310b00e0b0768059024000042c03904086450a4802c13003060381c201c074000d450000024400e0f41c010f0021850401c4101c0c0c018282c403400300c0b90303000080d00c2035401c60f10880724820780102c0000810300d980e100f5000000a84003001040140410140c4150020016403282602023130405000141c0d4dc5052800d440443d28680050480c010460340d00703c0d000052103000300d40c00320039982c0b07800100b0468170700d219110403400520040e281c00c1d800c090307203000b4907951200200614004858a243ea011040da0b412140180020614042018060340d01e4042c64003c080e260000d081082c680c1c654000140081740e0b441e848102c10380c0d03201c0c4055803d07448110b4040c226124108010400502c1100c90012500801c0042d541032545c0c00000a0a484050707a01a0042c403000d59443c509240c107100740401c900d2001320031860300c081c0503555501e4001483c0c0140c1800740 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182224244 1250 182222994 182223011
    0x8060f0721020d2007060b03030f0301080601210c14060c030c0304051f05090114040902031806070306030201270308030901150e220606080a060e10140a 67
    0x149145481441a680d01d440e03140408415480003500522042e40409081480200740840d07541913850030003601014203440d08641d030b00d0f1b07980034141c2c03508107d030584001c002610b5400c0070500518060070402000c0c1000d0751529101c0350840d030568800c41440b001e00d210b1000064001000c1c0404c8a1081d020fa003400320391040018032500540403000018000082c0e460301c45e19012008006907142200ca1910807400c6070b00070541c1c4500041140701041d0b00700800e070659802034280f1032890062403035991405842d503580b403081e60001e4444145240156034112100d507070a125140d03010705c061404100c0761380b40d500000d00a941078152200c0510465050340800710281602d0805907400007090381c1d99041c901c103914000d02d81542c03901e052420540300880c400c0441c190b402d00841d2180c105418140300c00038138103032610315610100d031032965598001580750300034800380f0700203401140e00042d82500d40c820755003062400605920032a15100903081d0b02c400c410300c2c5030b40051080300001803094 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182225494 1250 182224244 182224247
    0x2306040b16020406080c090c0c01150303080402090604020906070803041a0708191a0405100503060109200405102715110d0822120903050f0708060f07 66
    0x1159401500aa0100054005001840c80207800545109035000c0180541c0e912806441c0c40030004401e50040700038011850100c91040035102d004819400054450044502082d820440307500c00c40115030058100419490704060456102c1c00a0b80d095240074100130010b2028414013500909a100201c0404c050094601c0858400868840003089500f801c103400342080e03004a542610000c14416501c0c00742a040c00340704031841d01e050102e680c041c8400c0030480a4400200828140c4a0034400015141d4042003000c0c0203146a080004610008115198014107001000d1004200411041015450780c2e03504d0b04183c002031800f03c00c0c4004d04880da0b4661700c0301d051580505034105001040564400100c6010340805403201e880101c0e22042d03e80c3c950b605004a000440d8031000003076240104a15141100e800c0321344800310040a40da1111440c14400c0c5180c000a41400c005008024040108100c0303010804010b103e00c601d0a404565600030092100700700c00c1c803445c0032881c0c1c0d0707 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182226744 1250 182225494 182225497
    0xe1002100207110a080c01080402101e030614030a05060c03040c08010203070e0906030606031b06070c15031103040807150b0916300908040e04140607092306 69
    0x3040516020342d03a6640d1418401d10624400400c2803003101902400569500002009490380f88107855819190fa240c1e001c002d00310f4001030130320007402003052854009641c0e0144000c0d0088031610006962403c1865001280c1d401010080c001d03031210b20031078003045001614982c081611b15605540340d80d149000351941c4110307481564598004014401d13002e40000302044030000540e41034690341d5405040542d14941070b070701a80c154004100c1944000d00c200e1041c460340c0d801406e102d2500c04140c1d144030442c00940e00201d8102103c01c1048007003541801040e411604800c000c60550615440e0003d241c403401c44010801c4240016040c5001029000054003103401000c03500c0a180c40080010840e0480d02504e0004402551141e00c111301d0114541c201d1101c00510b2540640e9110701c40d0007132001803001c0d074a20400f8080001c0b288811011070f4451441000c4260706094243c810614082000d84500d007030000404007800351805100a0303160300300662081c0941c3c03049981c08103456 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182227994 1250 182226744 182226763
    0xd150204050a080f060f0f07080c130306140a020c300406080402090a020c0a0201050d090506090313060816030b0a0f0605070c090203010b1603030b19080d0e010e1002 73
    0xb02d07074080c0004030039a002c80c034901c100c1c4846050b10456518400d0019100c00201c521034281046680481c26542c418425182c0c03150070480d03164900342c200004c1c1040e40c40a075004460036a150402003491408000b44281c000c03011120560a01805594a42d00ea64422500008101a050311281104031000400b0b260400700000c096845807100d5000307100c10b008840690184441c04040740700012640708868003030422401802200c0c80701e0740115403a904c289032926031075460f0501000070420070302207140a080100e008507a5194015540882100c01c5d034030403410700c03038031804001e85c3d090f0950008140015034070717000402c0041c7c4000a50300c02003542204220a640040110b541070b00400200b811a0213a1410300c10140e45000100c280d00c424011200c4104007442000c2c0401420380c0a14081c6119007400b081e00c0f2211000b05254114402e215040030003038200411808200f40903100b81d0381c01c030740f80c0039040b090300800103007a4440e64030180d40594115406000c10520a0081592 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182229244 1250 182227994 182227999
    0x60318111e040516020c03151f0302040221070f091202060c0607110124030212031c0504030305162705030304090209010e010503012907060f0c18050d15020405 70
    0x51030400007000301802203000e03c4d2601610440f24100014030f00001c0700e83d144004400214100d999510700400c0d0b1042c03d10118041d0002e6007000300061b520b90020348440f9107801ca0327105e506000740c081c04900c1c04e005041f060520801003035401030290301120702025203180d030000c0101ea0034181301007400340c07007a55401006805808103218002d0790000810780c01c018484001c0c003642c10350350074400c0c1030381844c0a2885a40ca94800c20401420700c0304102000b1520841a00c0c10021703664181d00340030030601070744903001d607640080104050700f501c9030507007054020305904800803007c0c030301400040c541040703610b040940450401500101e02001c0000d03110103000e4a071a941c0c4c07050070030003035003060303140382d01146c0341e4a100e4100354440c4064a0484442e0b6042e0b00100071104481e00301444071700c4080d801017004010385001710b5168000e407518000a40000034018442840060152850010902031b41c00c403004104520f84e51441d40c15822600704600c6031480c4020f196801c000d200f580d002d6138 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182230494 1250 182229244 182229251
    0x6030c1813020a0f020609240a0908040e04031403040206070f0c0f060809010e0d09150201150e100509070e040510030b010b07030305070905100c170301080106060318111e04 76
    0x883e060340280c401e8005005a0200c8403180c5035401d003e07460300782085100b0218010f45400041c000f100d0890180c000c20040000100100d99807245d0032660301c1340c2c0113054110703800d600380410144d10181c000740e1401c20504803411414150700041c0c45119690000c1d084910404650f400c0c0161158080005c11412003880b6015603221400303490b810040303440c0c6010354a0100c1e402082100401d04200c5c0008690340d0340b20307403401c000c42584100c0101d4070150031903680300012507440c0014084000078100f8540781c49041e1901850390200c0200302c4e08160301818940382800b0704250001d4000703501c07600807103021500d941d440f40000c011000c81d0f80301400d401d078001c00004100c0ca040008040c00c2c1c3c0280e509000682d0751013170035180c1d400188a565000143c03902d80702d20b07052169180c4072440e80310b5040d50381060150030800c012604203801441c150307559110108103041d0903226030120f11a0304512440001c5564442c041d081c828904940d018850f09054540304010b08800c1c061900c03001081007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182231744 1250 182230494 182230507
    0x1060815100c1104020a3c110c1206131518031106090709020d0216060e07050315010306020c0f0615100e0312090303040801180b0606030c181302 64
    0x2c101c0c0044141c1a5480402c40c5005245030616000320344a02440d074030380c110750709246103062016000c05100f00e4107020800c4a01d4104441d0b144220300c49094503aa5040490200852039050020300c83d00c852003400b1856000101010110b10300d94000c60140307424600c2900343c20400500d4601d8144015150315020072840d1900d0b03440f035403501850081e601c40ea440f1108807031190f9100026a55044c0c5580303d00020809502260000d0108500c401405814000408404100b151150b00100d40682e110380c40949040402c000c540003c01d030032802031102c0049003158041318401070002600f130580024044501900421005149142e40412981e407450100042c0c49070a0b00603013414807420750407102c101c05620030100315850f480c0090240110b240e044100e141c071580050030540d0180020700000030072080a105800070311840c002c0d20006c82d259481e05903c2ca4400505d128840c1c0c5040c014040da588101d07099400c4885000e0100d10b00d000094001a56250301d034070701801c89400090075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182232994 1250 182231744 182231747
    0x82e08100204030308090d171915030303152105010902030d1d04020405030d0305040c1e170a05030f070c0b1803070806070f03050c040e0403021c050406080106081510 73
    0x1001200d0090f0341741c030b169440740c1c018191a00c0706545403000040e6060b2641421a01d00d1941503080900c250015810505c480c3c40d207030903200b20510505030307284980d104000345a05805064a403000c80310f0031400a038100794105c1e021400e1611540ea941c2d0022580c8030801c80d095200405180c0c0080440b680011b00d8000100b80f8207a2034810000e414841440c009541400d001f900c1c05d0381c80046c043d200c001d003e580c0031002404028016500c3c103e900c1c20028480910201c8004035041c0c03040661111400e00300741d0340c06000c1200c40c80c003961b4004072014020800101c2600c084146c10702d0582d070781e01080d040600d50300e40c4507004030380e04c00c00000764060207070054010714035641310503002d40742402e070359424161300c4a20846004000c51000c00480c84124444d5000e10751000c0420f541904060f15030b03405500c00c0d0b0040f04c0840140e485080e11520305a46c046038a800181249421071505081a400800082040c0b14101c18031188001050554040460115018101501058449080c000c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182234244 1250 182232994 182232997
    0xd08040501140c0c1b06070b040c0308040b0d060f0303021207110303041206050f040201093302030406090b0702060f0d0b12061f050907260f0412082e081002 69
    0x321461248945c400716840b400401007520200d82c1c00604d080c1c200780c0541c4683c0d40c94040180304544c43c103d140804000502e0078006000603180104040d41c4402040000c1c004884039030300701040b603141001b420030009500013030115110b0f10b10070905894210905e801042803100228286d03042c0004900070403070401051004141501914052025803a40902503000003400c0ea00030740014a000018852504140b00304030307050512440f0500b102014050070700b145031001807a640140c100007820800e10b507104441c000642482502146001d10f558002250792081c920385001e8240003103000760b40c200322580400030040e000342c00c43d01185908400d1548440781240c05030a50341c030b00ca2201c6203103000c02020005907400540141c0a40e100c40c0c00640d0701d51481c110000300b40c07251858a01c0c521544111345805901c006a094500d8101031800000221040c160304013004803120800c0406114000c41505440020400000460707a1034000d60303070307600d141d0000c4003113109403030418040c00546e50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182235494 1250 182234244 182234257
    0x110712020916020c041805060f0429070e0109080a0302060709170a0605060a360c0c020f0307090c05030f0109060b0d0c05041203050a02060601030e0d08040501140c 72
    0x65a0750016a03820041d1400a8001650311005910401189039035042580c01201c0e0038040c2d008408902c00c183ea1040d181590841e808103010308850240320420120303021010728204850507a01e201106598030b012407140c0244094100400324981c1c10b031907401080320201800b1810107a0b040c0c0c00d030a0070082e545140607103400002502c032040004403504178010441c98040c904001e003400a000e6150000503010281505034881031004000407035141174102c800c000c0910810400a00510380740c01000540313408072203031665080542d402c5030f49520090090400390304031100200fa51031007000c41d00d000c2c42500a142460700c3c24000d21040d40d0001c026510501000e031042516a0701d0740400825103915201d11600f6250600011100c00019040703100c4c620510314010381440e94032800141d1080100b4000e602042c00019411102d60b410303c03400e40c1c03052082c00c0c2480400c03041c03081030355204d9801580b03008203c81d000228041286c00c0d00810000055403105102504180710f41803840d90149 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182236744 1250 182235494 182235499
    0x1b1b0a0b0d0b0f090115080901050606091210050702070312030507050405190e0c2a150711030a0e09060906090c0a030b0d0303050105010909050411280b1c0b100e0111071202 76
    0x20001452400140203107444bc2d9030180826003000104410b10020300000b5103900454011198925005545031040c240b050307840e03034003d1444134910f0038020412072240d04000700309800c045c20002a50342020444045640a0b510503107816a1103413480552103054100403001c0f1701e010240500301618501501500c4100940014920070850410320300c242c02c5a00c1d0011508400004144c040e844075009501006d90300f01101b03502481d26505055900c0b04401d1408070f00002010f03441400d101040d1a407000081d82c0440d11400e01000181d8007400c000c15034002440c0020391500031607c2508041d0b4020001740ca0a0b404850514002e070180501b401441d00060203d03a00113184402800703aa401160426548106001810203004040750580c0f594a0401190b0b41c00540e100d81c4120441d00a024240d600b5031684038014202c03008085603540c4c5680541440c207145100e54582ca0381078552101410b10ba1050240c400040e43d040800b007440550720f005d0382400082054010040c04c1c0002d108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182237994 1250 182236744 182236757
    0xa030e030a1b05120c03120c070e090106090f1802060310030803010906061112040e13050f0c030106050109080c0402130302030a050a1101030621081b1b0a0b0d0b0f090115 75
    0x92040c0c02c3c0d079171500488080c2d259101c600c44400c101c00c4400108180d044502c00e580c0007a031980070300701d400c0c0001e4609082c0f580d502c400c01c02c0f5091480c4034500004070409010301000d6007400d450f050310790410302e0280c407800001001c1020020842521b400075a48a20116201c1da03445026200914a611641001c02c0010404c202103a202052405103e907030060740030300740b608004071085402e500a01d4141300188000900000c140d00700301305060061040010603928504006050a640d01a0b1199050040c0c10f1400e2054910201d036114104009a5005840b094062588001e42c021580040e415014180240c018004040381c124070142c007520a10800c2c5055500450856000d88540d4000302d0741c8003094484145500c00d1010345c503001c0d21009080c050041511840340381100d00f0707442191302c0b942422901c004040a00c040072001224000c050610700800c40010748070f02040e40000d1607580125030ad0984c3c0d4068141100074024100004560310354850b081c03440207031000d21001c00c10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182239244 1250 182237994 182238019
    0xa08072c19330203040b19120e0102030405010b0a0f030305030910090812010b090a06050d090c08160815010509040c0305120301170a15091505040812090304080a030e030a1b05 77
    0x1c1120106c03151a540c041c54802940003903804030707808400500410a031034040503419000d60142c113140750301d00f100060b600d041c00d02e070003802c48408a0300d40e402404104004c01000072100100401c03250141061552951903040090520091722560b44031546005050424043d0100240420703445900c0c200e41c0d640d80f625000041070103104402c2d6484400c50809001c028400c00c0601794030b003852100407130114801d81c0d944007586190740008000f07900a44200b00000c00c0e203201480104007910103800e4078030782a280841c00d0001402440e00a280d403c01003002c0003500d005010040d90000107075094410701d56900c0606a1080c8120250890f800c100c00c0c5101c2d001003080814030781d101030414490055140083d0242440c1a4241c1d030385990b0703c0080c0d0178002140078a82c4100d1080411a070340d0f1448801c0fa4011620103414080c1c46d5000344418800200f00081c0881016094105080410318110000789800741480c0b005002a503c05c501d0075440354903500130425504111021410002e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182240494 1250 182239244 182239247
    0x1707050705030d090317040503090f06070c0909150608060a0501080f0d0e010e0405040b06150412150608011e0f0b060d0506040603080a08072c1933 65
    0x4109026116800030066611a00c845074004900203121b401c181c80ca04503028815100d1400031075081d1004c0c0c100203100c0c00e4511f4240140c4401420440d000750501d84075171581c01500b41640203040d8010b40d1080b400003480005240c60521840080c010300440391078031519902c551301500c810b900c0c64205800460054808a00d1441c20000000100102c02c040340b01103424070b401c024014107014005d5a04c00083d00d60340175003481240103050066043c14a00280b0034a8001d862040303a4a40701030105022002948105807000c0f81c01050b00c00115242c005000300070041035020030080d628000080710032088120280c048200440000c2183d00c0c0800242c5003514252000943d001c0c10030045ca05503d04981d00854001c40090070001e541516640c60f0540f80d44224040e60200307400c0020070600c940d11994170702c4880d00f005d02e100e41000d445201e2241c0d1060a0040c40d102d105401c6030300c100d807204138036503100400d1f184180038030a8450086204000c92120103140801200382c1594400c0ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182241744 1250 182240494 182240497
    0x20a020c0d1a07050d020406090810090f030327051b0402180904050106030b01030510050109020403030e090402040f06290c0718090602030406020913050105010519021c170705 77
    0x30b500030201440329044103202c111070600061030fa40070301c1414852240c40c000307180701400181c09503481e0400000d083c042144c1c940f0341e1003105102d1840c101950240040c01070703031546c00c1766645030401040221420000d81401e914110b030005440480c40c1007082800700006801e41ca00c60400d01c0e070070038056200c00341b105a1003040b01d40e41101c021840500c0641c203001c04400e51041c012000003038080c1d103a13910100c140f1070a0380103a40344d40c007041b4a62001032280c030410307004188100d01145014a50b5501519240f11284200e2240d4400c00004055454540020750f1004a1100410a0b603881d0010940c0c5003690101e8144c952156010310400da041200403600c000000d10000c0110b2441c0180501c240311141018103c22038079081141c0020700e080c006140168031500025032a11408801d012800310744903a000d0415041c940100242c0c1d8029003100c00d01e2418241c642d01c01840d030002a45402c0850320030b070b1821481501c040849a0f03021106029946010020820540354010110390300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182242994 1250 182241744 182241769
    0x5041d040210020f0705100207030b0f0601120c1b080c0106061d010914090727090b04290a03150c080622020703110f0a02090606040b0405040e0c060a0201020a020c 72
    0xc0d900c40c041c10300082c82c0c00c1d0100004c7d0703a00c1e807048940c050346039a00d040b04021300343c0b0b030104000c40d48401c1c000d1030f6810103841d05e11410010400c00c9100b00c81c030001842c10b400215052041a4000d5038a0248a03a000890b600401c02e00004c0c06030554582d0000e19130845421102d001c4203a0300c2d10600607601c01e0100900700e583d00900e80c03407d05040e0040010400c0081d10042c2442016090380000c00c0c04900710f04403401c0200c03c0b403a1858030703001d016002c1d0b406018a0034480c5151034095002d200c1e0042502d040d210800c007076041c01400d01d80204103694515000a000000100308141c03612840d6040020104016516940c180c0c0303030907061000f99408201c9104c181c0c6030f203101d2480155610f901804c0f04134040c0c0b92400c061003103107602a0500440c452802d280d038210002000035401c0900d840e41c1c21220070741d205403401e031030070025180074080c6000b424855600ca10159640e400c1c00c101040700350400502c41607980b0101c07031011f4000e40c003586c0180058051034010203454079201c180d0950 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182244244 1250 182242994 182243023
    0x10b0f0603061c0516060e0a06021009050709061e050a0b0a050903100e030c0706090524040323060606040302060d02030907080f0d090503070501090e0705041d04021002 74
    0xd40d10307084204800d151080c030000045101c3d40208101090080140103103418102e070705081d505041a00003000d8000c204040f03402100b0f0b003002000700a40c0003c10317041c503a031031320000603550200d45005411710740c695004080450512101052a0040c80c941c07a403c0d50b8034690a4184039541c1c014803103085c01c02d20481c82200f100b40000f5003558050001081c40b424024103452198116641d400c045035081e10007000194408144442601030400c180c03000303441581070018040d032404002840e01a501c06800307002903120340038070514580f00340580b40516804001c00c403030b400300b00d0714108880c80002c4440030140308000c0070806506002d02110140c0750003818040ca81001c2e15440006540040e0080c0114810705d0400100614140400d0020300c803440003400c90224403c0000b060034810b50000307171180e04411801c02c1180c3e08448103400700d031108072100400780e4419000b903a50303009950040400c008000000c1010041d03155640344140d00c04c503140c800c400c0030b01000700d0340c0d07900c81c50f403081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182245494 1250 182244244 182244247
    0x6030c1e0806090c04030807060e06060a1a0c070f0801020309070f060e0d0206070c030305090f0108090d030e10050106030605130207111c02130c200312070509030307030206010602010b0f06 83
    0x142c0314204000c0b810303400000c1d540e4581c0703441d9a03942d401c0310b03640c40700c8000c1d80ea1075521810203601c41c50034401c42c3c0d00300004959180e0401d04000341c101e070030340608001041000e00010850f100e4030060003190300802c62044950b6041c0da584c516030b4086d52003118503d1250240d440c010458a03608400300040e02c106580305000b41c0c60340b0042c001903500315031082e03034800b1040c00752800041c1c800400c40d001d03507c02e541d40d545401d007000c04e003d404800304a03680d05100d094802c01542c5903001580190220035413401040f10307420b003021103040100d001ea4010b00c084c1080004503000c0c0e01500010700711001030707800c8a000d522030f1000c403040380144030b402405800003211020491070812409d0315082100c181c0910300750026800a0200903070f204800d41d020f41c43e290310301010b54010300051a0f0100030000507001600012545445c1d200d8441d020300911815030100e00803512030810b07150080c2c8050100c9039550424140030b5034902003446094010740c20142107800b1401e02d2844860404001f40030386 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182246744 1250 182245494 182245501
    0x117010e07080c2701080108010b0607110d020a0303050301050109151e030e0102041409070203030112121404080303040b100501050403020d0203010f1401030309080a0f02040b010c050706030c1e08 86
    0x300d46245000d0810010724005101c0080721380c503083ca45085141e9a001410f1441d24950000342c001c1074140d100035400d0745805080e015030784950301104c0c1d00c0c540c818402003800c00c85900048015500f2080030f50062500c420100800d9000f40095050f40d0090301c50800c031541e1480c150b00009070b0700240100042404420111807100c10896403071180f15030801091172022013a2003800c981180d84400080702100c0400d9220303080c41d400d942d421640c0e0b44080d525641c1030045007114144d0214008000f000e5401d10f1040141c42188554372000c913100c0301e9940c4954500485a90b90410307101964090f11050120788100001c440010071030703070706071181c0707003010300c1c41d001c1003184041090180e0b0555201c0307500a500800611034070800219800461210b5411030030000c125400300c1d003101503254041101280402d620a404004807039048401042040c10840103d58040d21000c00424a22400e900850490340580042d07544020b81da6400c6046407540c80403044880022154001091241010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182247994 1250 182246744 182246747
    0xf06030d210f021603140a0e0d0503070b010b0910111e01060902030406090311010c09050402090d021906030c140409050709030f2103140601030216050118020117010e07 74
    0x4100500c0780140c00059000340090000043e82d00c4540004401006400304501301030700b00d0300400c5a8110040c04c281056000c0380d01902e44416284075a2162055440d0002002410412a112981d003c1010001941e5421905489070000601e15205050130082c02d00c419100d104d0001440c0104401008141c00c1d542c441401c40e0041d40e40000255210a0003054a042d00c1c002940601d210b507000141040c814180104880240c08881890f41d040c034664800a50b0311142050a07075504580040c0d80e1181100022032070601804020340281190100244d0007040307031184070171a40140c500380310b500c011940494140c1c044000340c0910b244284030522098809502c420341c04000c900301203807102e8481d21000703090b030880e01040728075107190640c80c84000000c1d418145000450301b405e0040348042c0794003228008009100310f0415a006c121b41c818aa0403003000464103030404001c20140c6084400101e80e0401c0402c1a408a070000715040c0b100f1603c000c5086c100c4070000c02d003500c80c0d01c62800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182249244 1250 182247994 182248037
    0x50d0b0c090303041a0c06070203030f0c1312060504050c121b190b04060f03060501170a0b0a03080301030b06060a0207210b0a0b0a0906050307050d0c080708060f06030d 74
    0x28258140c8003d04c808991380200307040e50810981244a410303142c0c105400d0041c42e0000043c141c1e02150024000c1c4103203042240c2081d03030015002041151640d111102c040754403401c540c41461220103030403103101406800d900040c09140610242c3e030843e2910310610030560001c55105080d68001054449070304200606c40381c800b44010044000080f01800810607810a40c108000c03590b00007808000c1c075030300101e2500707040215050070f0102605c0e050028081c0300100c5481c1c6c08240c0710302d001900c0300f9107a0b801050340407030081400340d0030342d160b041a8410703400034007007211948042030108159140502c1070f5060102c481c1d00a280e6a8100048080314140300d0380c07070100c0032078000c03520300005041040d4688070b0403000302c000440d00311403810051010703041e030300103403e0074900f00040c001501d01203030040c191038041e1940c5e090320880307103420306c0103203200e0348100014050640d000c2001880460442d0003503a68032400711094807a441090303240c48200b031a600c00719400444003a5108010070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182250494 1250 182249244 182249257
    0x6091005060d0c06020d020607081314011e090606050306101707180921050406050c1905011b05030609040f301814060310030606030807020109050d0b0c 67
    0x340324100c1e4408039954143c00b044150070040c0583c00c0b0b400c4884038180e0400030030303a000200746401c1c0c4650401c40c2d00503e62010f00b04010340590f81041030b20000c0c280940004540c81d5031030800420005112000b0b4000700019542284d0b4a41403d1000a15250003d1140d0142403c049209003540c074100180511400401c0b14000300c0c0590180001d5911101a021034503045103200810340451610300500100c2141520326400c0340700c03403a82d030b013429030090070740342900c0d413900302a61381d0390403003046c00d2406003000581c20050000b010300c001080b1064000b1f41c03c1c000e060890310001a0b003c00c0507100750100302d07441604000320b4000580441c2e0130301c07611445540112098408540c001c290584048410341044402ca5003003000009401e0b072000f0302e40a00c0604c40340000340581407542d070b400c4440b00d1520251240b0f0010012400c48001d154040c4000c1d41d026504001c419904c0c900424a5044104240d002c100740002c0042c40d0308000c1503042011341c1c410500746c03150f55254401c05240e00000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182251744 1250 182250494 182250499
    0x106080601060c050712060506040e0a030c0b060103180609060c05030403120903030902040219080105011713081606060f14010206070c062403060b0d0b01030b0406020708030c09030705030609100506 87
    0xb805d00059805585400c800720794091078010880307141c0001030005543e121000d10701a540a20355440111f6403040c00c00d00130503841140006075880e0304004801a00b2600c0204c0155030f01d100065041050b194031003a40241302d04824000042d140005907160b000440b0081c1c00300e1403c8042d0f0b000b40000e42d000c040386920134140055003051035004581241c02c08103648130030030055070b00040d240e604460a5401400c003484c090702000541c540148040f0f04c040c000900c206030001d8441c080002000075100b2112000310341c0d48010525040000142c0601c2c440c004070562500401b2907070075000c84002c40b400c581a001440c1946500e60111500f50b200c5a040d074a1b241d540302102c0d0100320b911101e443c04d0307012071081000707641035003020812181c4a01c1014401d500803010180000d000500c90f5044942100c1c4181c070310b50780c2d0304028019104a0a00600c1c1d11400010084200395400c098100c403c4168200c4840700c0d02e0783c05044d9607000c00d9540480030b1303000c05c0304442c0c40c0ea116013129a00483c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182252994 1250 182251744 182251753
    0x120b07020102191805030106120809031504080406140906180f040606090303090902040f0e0c070b1303020d02070b0301050d051c020705131b030b011e05030106110106080601060c05 79
    0x40220b142030807204800c1c0480020384c8607241e04c03400000310b0050405800110000c01055240211803046c903904440002d203015030105010a1750b5405001101c61079100041d0000c103480c080c50003105c183d01038013480c004518002e0400c0146004442540c80e850300240c078803840c100e10b40c1041100b0003c018100e03640308181604d456110344403805154010070b203945840c0c40c2681580340c00f4003180c0c43c035000101e00501c1400100403940d400c5507070b01e046030800020304d203c40d151022081051310032510b01502510005081c003d00340700e00d105104050703001e982565120010808100e888500301c0c030800c0c0c0003002c00c0c4014400c91400e04102c0c1103452141c011a100c5040c802c0b50210b05141c907040300d201681054200304410f0402c0c803080e002c075501000d0f04004001891025482224030013041074201551080001456400f403003e4180343d4041812441d0703450f0b034111005201d41c0c001d020318000600700d0101c0180741c134814018001959003950140078184e00b841411241101100301c255501d125 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182254244 1250 182252994 182253007
    0x8040b06030c030d05031605070203030a0302090612040f0b06040e0d0e0a1d1b070c1202060d0f091707030e06070201051e030709051002190212070e0906010f120b07020102 75
    0x400b04442c81d0004d00342e441e41503c034030b4241c41d00e9031808035440c044800e00c60200095070041e0b40110443d16011403e090060303c0d4010325002c04c0d01802041d6585446206030000e000600010711400d041d050310800080c9825980c03017003032009031120700c9110303011035101c00c05203842c86004440805000c5405071a4407900359480601c004101000107442d800c480f554402c2c028543c20740c80180c010f0051749a00a45403004d40e6407210a171113541d205080b501c80c00300b183e04046503620001c039058150064010311201102c1300c403840c020a500601240c0710000584c0500550000030207850b4442e416031644030041984a0600c902caa0200e0301c100c2c104901080300180f000701c070340c00b20b1641c503d03041c91140e128540950040c1004440d60800e0307200b070703030054985c5101e10381c00a07104400e03400fa0000604140814400301d9146083e042e032040c0c080c01519800301d40d111006a406106004003411107031580d98401007010f03000060f000d02e1103e81070781140230b00801c550310145c580003c01c81c80010320307058 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182255494 1250 182254244 182254249
    0x61407141f050901050c041d1f030503121b0403020607021c03110c0402040e0a020a020a060c020c180603060402010c05030c120301030210030e210c12130e0708040b06030c 75
    0x124000c12190792542e07900148000d00c80b0920490b0b0340040d601c5140d0b40340c20300300122554480d03d020f25507000b40d210074000440348550302c40500d0f128030310b180b081a015900c9103007140d01c90f000703044200346020440300069426070070760b0845923540c1140b50602d4601800c580074000f56030710a40c0107903042013401000b03404081a8605103001c4030b0007583c034031610101c0f481010f410300001c040180e10860040c0824003401d412118600e4200548043c01030341d5031180e510981c2001506030001d0022458408003806264000c50550340134001290130319140007a1101440f046c2105940741c0b40c0541c4044009001940a05121a140c83c000c1c404c4030708102c070640160349041c0c01140c504a00d124048010811428101c1c0c80d032618006a040178000c284842c020300356100745204840075022550f018420300344416070704842c11440c2c0709040c0d480f20031080d417090003980d000d400d21103501c141e0013100140340d8140010540c01920655107040d007503115600c98000c40030001d0403280e810b0240451041c2181d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182256744 1250 182255494 182255533
    0x170a0605130207030807020a240908030406020a0908010b1e01022505190b0d050c04080f010605011b020f01050f0708030a0b030d0c0803040308100e130c1d0f0919050c030706140714 79
    0x10750ec40c0c00003683d42c2041c040014030510752030b4040d1a20f0380c1403074007180e0140d8410700c03141100000200384038940c441180040b40707481040e0440014007c082c0303010568a69840b00300000341d60342900c02803c4440e0075090680800305501c5800141503090000380c0c0320307070301d1034101d01e400580f21424a820300352a443c99908000341280c8180850399122010071003541c00034044454032800d48031007071401c54142c011072060000b41d01d01504020001452410054490342a50070381c80d08880d18039180d15010000c40c6c0100b20703003101103100f886078481007000540701e10010303529240d010400741e00b1521580c4e81515102005003c1102201c140c0402091400003280914030540001d809080c6403c07540c10701c081c0109441d0080e24101401281c0d0051551b00c440d502c5412101c64000c01e01e45540301407825090200895900d11451001e8842c2028003400089500d40030704100c0c266089252f4440041d582f100d000c1803c810040c0060180e6008282e40c00400e4407810380c84810303504200f8990b459200319 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182257994 1250 182256744 182256751
    0xf0f0702060f03040c050d0f0f03031107030804020f06070804230d0614010905011d0408131217120a180204050c070c050f01170a0605130207030807020a24090803 71
    0x2c03030601008002c180301040c501c08004002c00d0b0f454080d03428098590b1701c3d010004440182201d500c0c45400d8003014401d60007008000b01d040078a944500082c038009106907400c0d201688909401c030224001d510f401c9049501080e80441440d1400703107026409645044a0400007600340000e0001c0740003922081844081103104060000342d5803c120240d032003100041c1c00051500d40f0b400d0061165502c4440c0c02900c03100c0a03040a13315a6541ca001ca5183c0f00d00c0620005283d81c0000005091100c403a05600d200e04c20800c00e403c10640c05180c02460041e01444200744842c80b0110b0725200c02640107042e0001b1f00ca0084a1440302a00031400b540d005844401480f0301c0011800c043c400e10541c9100646021504400081d80400000f4800c40740c2d07820340009201d040c8003181d410308259120800920f006804c1d8081100c009040354003e4100b08819408908202c7c001401030384007041c86001d45a01041045407035502c45015107018985100701603c0969803144900401d4461024510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182259244 1250 182257994 182258017
    0x3010507090e10060e0f040608010e03030615192015090d0e090a0b0607062c060403090b0a0201110c160605030708040b0403090504050a0912020d050f0f070206 70
    0x9003490101d842d401480000c040c50030a07041207005003c003c0d442600c215108100b112082c0340c0307107080e900140040040d175210202c00e610700b503102d000348603000c0f002e548561003c84500c3d408010624090386c0d148600c031181888000613890a80245020320b80c0b004107a41c400c20401d81d001c146003001032030014501540c0c0034070b440120030001c0c1107404000800701e2404500d0803005002401010a400b03c0003c0c1003070f400c250b02c80d154030025465a00aa4020b00d801ca00240850780100c0d503803044e1000301504200341320040f5142c00000e008001151409036905956509880e4a82031001c921a0007030340780302c0215501d5500c1000c800000101402074034007072002402c81d03148041004401036040d940000240f0100340100428103412a000552261b00800b96900d41e91321481c040301e4440032070f040b25034014945410300240e4500c60340400425845095110800200c800d0300745d03510002c0403084000180c04000910340380140350040e0003080104080f40b401c0c00003d41c0001c0e82900042030117072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182260494 1250 182259244 182259257
    0xb06070501090209090a03021f0b030d080a0f050112060b04020408010c050c01051008060703090f021503151f23040303050304110a03020a0e06130e0a050c040b060306010809030903010507 82
    0x706500e05130b00d40a4100111000a000217030f4140c1c1c2c06511a03040079121480120842192103000303510b41c00c06592820000c05580180c24202405000c2280c10340d0106009807400d614005243d11a10845060b40c858102c00b103c550125079070a800b4110b90103490b1b8000d6028400040c110340d090040000b080000c0d00e0b001d468507600f91981d0b007103520051090400095204042002d48408141d01d078016100b491301151030b0303181d820803004c01d0021040003034001c401503003c1040c0091030f601850090024042101509000e0010000c070344526005800d0304064500c1e82d008800e01a0710360404150600300d40f0305000722201080380e910381040d4429404184c00004200800400c003007881400002100d10042ca6030454000c5402a40c403805860440201800400c02035030b105074002c2c8042200a0045c01100a070740c21690722641080d4040712140318110b03000881d0301d000d01039004a100094122802c60740c51500441c4d1520b4040c0204069000070002103440340c4007801003a103c1d081984616 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182261744 1250 182260494 182260511
    0x5090114090906060a051003140705030403020f0106030b070c050a06140405070f0b0a0c140124081f0207020621070e091b030a0209062701080103150507030b06070501 73
    0x7082900003420712401d5003241c1c00308055075507000d00d2241500d10503103100d04a40c01076a001c0e030081646240e5480d0300c01e108001c000c030040e4030500451083e4403d90076907003049031411a003403c1e200d00d8000240821b241000007008680b041c01b40001860140085903a2400582c665504039071b01c8024445012914808000900408000e042d00a0120445405100c0d1070100c001d00540502d0045000700038aa0340c500d01800725041003100403405aa00030440c125000030122000c408240c5903100d5040e085400082501010524038021145000221421003581000b400203501c0100c0c2242c0c4481c1c1400790000f0080308141d4445141040c000341d0105042900300a0200000d1000c3c4521800400082080c900d150388130304c07a0446d0f912401252a5210302d82c00310003900404992682000020640c010841c0c50f004007544205c4800c24000f0000d031480e001100d10081c24080038003040710545900c5081600d581c02194014002d140000c0e8103014480040d24030f03413210704262142d070f4454415 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182262994 1250 182261744 182261749
    0x19091505030708150703061509030507090b01080c07081e04180501050d0f021507080d0b040605010c2604090504020109051f18031704081911060d0605090114 69
    0x8010344000c8000b071100d949003a05099807015030704206800310301c4a4000c110528001d03000500604214880321048455983c402002d10003584010b036007a12507528005100000351080006801d03041e175400c10203542c0d0a06400c5140d00c0a8400c40b9030400802c00444058546802d84903a100c4000103169124a000304101d0445090144004690f00e442e004204660b505840080d48640c030112041d03601151307000140512190030302c040e10a40d0000380000400004500814046600c0c14080044a000b072051104603041401403e003c510000741210108001c4550007442041c0c181c01c0314110102090300d80c070250020740c00036501e00e480b041070200310341e04101c1c00409040c003510403160340c0c0e80c0755000e11003a401007810304040c06100c014002c2084014007020b400303941c01028031101e98140000781c3d4031580c450b104000190049018405000d54002c1d0a507030f2a60b004607a00710449801d0040001c075a01103d1380d00a42652182c0001d2140c031202040e078000c05d0103100605041040c40b05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182264244 1250 182262994 182263031
    0xb0f03040312020421020a050301020c01090204050f01030512250804030302150408040b0f16030e0907050403170309100c020705030d050304051b150721020d090605091909 75
    0x10720b08406006000501c0031031151000a80d228011805840b604841400864481d85c82c2d40c002c04e400d5400001c40030390b040c0054100350b003120310a8608000c0da9407002200b44140d0300a000090103074201c41903400c442040800605810200ca0403403100e48140b0302c0104c4e00c10303202141c08580e981c20100c0c0402c04c1c907030103001c0e4030080b0055251166141ca4241d403018203500c9180036902c41c800b800304224451040803c140c48401400c1060161505010b04014104040e602541d902c10701603d40010305a6110300c082d501106d5112602c074212a41404600d4800d41005220070581d1113440700440305c08407640030740d5150340100c0d000740410302d00307007414142030203645210031040c0f25041050000003400000d001100060b80180c00d0740b4001081c000070300c00d620000a00041c4a8046400340c20b0000c0c0078040281da00c0c40040b040c011166441040e40c84002044a00300800e18880003002401d001d20024000c00031f0050071507142d440c003428140c403a03030102d402c5556850b540b070400e400308420010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182265494 1250 182264244 182264267
    0xa090c1b11130b1003110c0703061505010c03050306013515060403031e0e060d1a04050603061f090f0b0310140103060b1503010312080a020903190503040b0f030403 72
    0x310144205000040815840700d0000340000805680d12040940c401c5010182d1f1340800f4503806031686a6960300382440981540201c440144401c00d5001440358041c90810401980c15100e85082d60748040041d128600c0710080d01544a03e0b40102c144110f6440b00445203103881c80c01800c07600d003811915480d41200ca01d981d00d014075820401031011940001d140003107510030b41c0b8595040206400b08440455440f05860782110000c94100e0740f88030103802c420a00c2420b484000b12000d100020407040e514140d4101e40c040e004031020603004d07018580102e00c0e292101c68010011a078480c00716044641808065203503541c0c2e003071612010300e010300018030056980c1e0014410700b0319845450641c264107200061041c1da44011b01241610780100b4131542c580740f9403110b0344a607581c0c20300c3c0141d10f402e5840d0f100060b64450000c0c0c03c4004600c00d07941c480324003900030030300911042140180350701503000c1030f58035200a00c800996500d0a0000745541e002c5203803c0c0c0d8480c10203180c060320003c0148e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182266744 1250 182265494 182265529
    0x30207060b01030612150608010513110103110909061f05210108061909021f020d1e0507020f0301020301080f060c0325050c120301170307020a090c1b11 67
    0xc204444159241005c5e611074101000f240107105401400c8000c0044e984002220750900c000c03c841c1c100712038a03041c1c5d858060807141884402050044048400e622400302001c001403040c0e2019080c00c1403101d034860300180800d5461741080d1514000116007034015000507000003a20900c0d80e01007600311940a00c0079403000720399410f00d24010346030040140300b0b9a604418960784528030b41c40e5000b41c85071507000360200468950b01c00c200c0c0c031a0308079091030402601c00c50003440070300d078810311104142d2451003002500714828040d003110309611155060f41d208041c0248102d01c0e40d028801103000707281a000800300a440f040c2c1203414034000400500118030113208100800c800b000c7d14114a250f19802c13202d00300301d2254280c5150066450f180072900c2180500549888504001d43c10f0f20740c0d0848403014035201c0c483d051303500d201d4203d000b500411006010400c4a48070340002018507082d041140d4001400c680402450420703501c15036903d0103282c032260090412580d19840240754 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182267994 1250 182266744 182266751
    0x21518010f091112120f0304060c050a1d131a03010b100e21010e0d02060c0406050708030403140a03090b070f080f09100c020703050d050306010917070510030207060b0103 75
    0x41d403941003280f4246468a0b0083c2100300d641c0c120664180103c0e60103000c00c10f00a44c5900b84010440d045810480c0d049400c00e19158074400380034054020f44160341451740d00c80d4038910010700c0d05031340000b08606403500110703482410301110240c0d0082034151550b80031200402407a007020182510070024503d40031b038403592480d1401aa03c040c810300841c5e410340301c500e40c1e6415890141c0404485120721212075203004002d00d01d0d0301c000310301008030503115403c0740d42503142e41606200078031407403281030040b5204115010010320500c000d180c1c880d0103410000030b90030302ea5140b248030361300c04600303c0300080e5100240000c20001403d030a4201481d864540c81c0584524405000000043c24030800b40c0600000104080010410721201d608001c400b8480d0303040c0850041d42c3c8140390300088960703000d03075010110094811070649200702016914000300e40c0c030749002c401140000e60608c090900071044003107180e807182c880c0d6610354072a580c0c005a0f114014200340c011079086101d40c40c1014207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182269244 1250 182267994 182268011
    0x40f0204030804090504030207030609030f02010b0901050d060b040f020726070b190e160f0510021c0c0b040308061206060a05010f18030f02010f03020c0607050a021518010f 76
    0x2861425102503d24020000817130740c0300c40c103050b440e000c41c50744000c0c0a58180300034441050fa001c50614200320080d00280508007403d0100b01c40443e013400b80507001400c00810801182d101e0300100800e001c040d00014442c1e81106042050f42c0c00708600b030700e030241c1d20503a044080354041e240c10f01c070788115485107042a10550750b42645c07850203881108400c480e01d0403174104403200da1050b010900403208503554428031040c1054844158862419214110140000c1608000c20201d40181c0245d0240035034008601d0048080b0030a1600d01c0c0401c003c2018200000d85401400d500032806500e80c11000e10b0704804201d607801a4944500c690341080d001d0051944500e40e003041581c40900f802c401d854004042200d541d09a030850075940e00403078900000703100341d12242404250003a603480341418801001507043e0301c01c241d00c1e00ca40c0d0b803009002403241c901c00d03400740c100c100030ba03c19100e551410312845042668280d600f0b80d044c3e105841320b04400c1d4407d210f403806001820b8400d106002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182270494 1250 182269244 182269253
    0x1c21020601080c04020702061b010e0c0d0b01150c060213050a060f080103080a0c02090f040b0c04030b04020607061103072d05030402061303021203090913080319110c0309040f020403 80
    0x1480e038481c034004d07a00803880f2021996020156100c1c005010803070600d4400d640c4840c0d000e0101415070030f4070750280640035005400e14060107902d45800c142100c419920381380c84616a0206a0380340c0c820420b5542c1d00170002086070005054000000700001c0300541020100f00700340c00598000d00a00c001036070781c400c1da1038015803064112900003048a40302c801c801c00030baa00d0309848e60000e611120359020440036034244c0f18001d01440c0554298001341e610605441118030850002503c82c1c001c90000600600d460750003048021311950001c20008148003018a0300c0e0029036a05011482040b01198142c403000d12341112a284000044907044003400090018400644040d009501c0000d40c1c01c426050103805c20000c40c0c0c043c00400003804160b205d10740760f82000700364a01c0307178240303c0114030151455482c4245040e04030030420301c0c60b1524030610101d0644400000c0c40d072a03c80003000359506039840608080c2900c68080c5548281d1103041008403400d41c02d405c610a03105101c00d10104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182271744 1250 182270494 182270503
    0x5010f060816031d150c03061807050d0920040c05091203040b0c06040b010e0103030f050702030a021c051c09182702030c0d0b0606091c2102060108 65
    0x505891000301412803100c1c100e001d404130b00c00150816808400002410320300050b504000020354440c0f140548a20f1a40034003031106035038a95002d003102c0030803006040e0001c1c2c000c0c2c0142003803d10920f40101070504500307403602900240c403580c40030b610002c07010850520b109080841110108541054090090514043d58a005014280c2003242d94240402002250046e10300d07010407c2c1c42d0700c00209103d6071800c08480494503400303d0000040d006040f200300606881d1306445401884c2e08260003182d031a00076000c00c1e60b242c800d40e102c40001da210f200103407083d0000d0600004a4035031600380b00e898007000304060880c104c984211032000310342c8030661909444104100004072a02c2a60781c1001d00100c2000c004030030000d400ba0303041d5140b2058a0202c081c0700350309840840590800f0000701001c00c0402400c0707001100001461490941d0060001c448002c1c94480e80c02c400b0050481885840f101c222103814850560ba001d4900da640c24250030542032005003060f606002c4499200c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182272994 1250 182271744 182271751
    0x4200603011e03050106080d020d14040501141e04050414160f0c0c121203050405120c0f0f0609060f0c190302040e100303030b041122030210030b0405010f0608 70
    0x5000c007150701010300740c0380c0141410003541c0144c000d01c210343d181e01100e516141c001c4407540c094460325444085580c0220001600300ca449513500b81801d203000015645a8502e41c61700340340b02c9003000380c0c5d4038005030889441c6a0350340030b03245a520341d130410060204880190b9104992840c03030750200004c1c010780481ca0103006240d86000d08039009055400d40d010143c0680040200c0c02c05840440c07260f0755280b1858441d0f000c3d0b011019034248600ac20750440e13030b040c3c1c0d001e81681c100b40c0c040700315103215800070400003050304100c960604401005c6401c00c0c8086150741d205c1e400500500c41104410045240c1050101c1c540703400500703102c4e10405040c0b01e040406a100108043d0b0407144600070b0381554002d00016410740c10910f400841c4410130ba007180000c40200f8600b0310906100c1c1054494500c1c0542001409403900040360b800440140342241d68042c0c0440f0700d000800142c45194100e407100d032460b2000328804030070708204015610160001040c1860341d120401c84654850006a003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182274244 1250 182272994 182273009
    0x50f01180b041202151501020c0105120a05041502160b0a020c0318060412030f090602010c0509060d020408071d01060f05070303092604060201060801020c030405060d090605010b030420060301 84
    0x104030003824000d90421204060316217001c140030041102510400c5900c48041409030b0130b03100c42180d15030054499020382141711400201031000104503240a40c89290030a02546200070580e001c456031000384d038448000d40315800160007005040003425040b20b40c10000c41082982080800400e440e500c0c01103109000303880a00800000440d200c2c4402c84020f00100c09109500e11114100900b41034140c0c0340d42c2c00000c001690009200d0301c1842404a40030b45a51a03510745900501009050340200c811511072030b034200000544800c0800c40030005010507900c05201c0c40ca80b000a40700e4040c164420818000f007842d43c2c0303c0e45035010040741c10305a4542800542c0c08098100000d50942d500d60310a07241480c00c10280019102d40082d00c00c94540d54001e0150360b454450701740c240c0c05402d00d003200300e07482840180000d10b00103000e00300c030800c6413000050141e842d88408060315070a074001d481c0044000140b00c20700806400e41e160b0700721007031503a000364207a4030040744051105100321235 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182275494 1250 182274244 182274263
    0x2072907021e03100b011106070212091206090109140309060d050c0c070b180f130903021510211a13050a0803060406050907140904060909050f01180b04 67
    0x32241d8500640e0b031014000140880340340450321035482e0000c1c03681009241c0851016555102d0202d0300050283c40f031501c95010b800c18a1100860301c05a400000340d080e40041948018a0f0501040200130310030090f41d00082071200300b80c1025408480162003d41c4540c0080104001c123403a29011101c06440100001881e40d41c0d01c03a10489600401d08810303000d0050910005a00040c000600381540c01d83d500008a080c4400410030301030000143e0701e0304030410384c1241c440400158840d84d40c030750103401a2269800140e080305050341c0d08582c03000a800500038280245003c0303030045a01913100030f0410703d54480c0c030b45481c2e680e100c03402c15182d0f03131546030700025010700ba4000d81380f941d56503c241169010903441c40d1a01454008403015802240344c00710004080c0b9104414901510131610360004145003070071600c241d54040e400aa400030740b40e480c00100c0026a02c10700201d24015005840701ca4195a87d09080d500311845007a000d9a040f0410408500e00940c41c6402547c4510401c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182276744 1250 182275494 182275519
    0x9050106060908032704060801050a090308161e030b0306070929030a0e070f0e041205030118020a0c14030304030905012a02030a0602040b04140301020a0c0f020a05100207290702 78
    0x34000e44988e81060f22154201018801f00000b01d4000380c0d02180f0a844210b01540c0c1d00003a18556001a2000800114100e01c64012005141c0304581d1020385483d011803001e4030100468501030f01540c1d00c1000582d080310412400312206e8a010301d143c46900606c0e1000020180a001808058202c007a040d5840102131240402000403500400101404086003a81c5800030040e1013422902929002c0040040c0c005e21032281048a068a10b1900141e081516651640001390007076a420700c20301800000e42000700e0f5010074251140300916004550341d2030507280052a4102e29444581030040d801602c01101003069003134507204504402120800381c40e070002901d84a1103000240c02c0030720028020802c48280301c010f001381c4152003040c14071900124141400c0380310b0300a42c20001381131103a03403600050201d01001901800103041d800d0702034076040050724807080d0301502d10240e488010200503a41102a10b01082c0303003d200c01d03180d00040070403500050721131554000d10400148044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182277994 1250 182276744 182276749
    0x5091507110a150c090806010f03140708060112021311090103091e0305040812090112050a0905060907050109061e03050601091503020904050604051005040b06090301090501060609080327 82
    0x582d00015001000c0300030702072406604200801142c602e6400240000c10085040c141c00218903040714440c0b03c1d40303983d82c0e18640b2881194440d06981c1c442c0d90189a40001e11b0000030020315000e4240032040d00c01c4c12102d0300c1000300c6e040042060810060070300381c1d100d000c07200401c01e90391150401e00b00828074410030f1620403101c0360940c1000d140490076420600074168810301270002d99100c1d80c21211800c00c021244140c501811403001d00240444444401010341d6810041d0801200390340490b207200c00b655040c0c18004219081c2070903600a404c200499070b8882c200f00010a05410700250012120107a40e90707a66030070074010141911130000c01c00c9a442203880500900030305144051075002e18500034044e41c0483c0700244544e0900300403c1c0c441c0f8040c411980244c90b400440282180f0706400d000240c0300d075402255214109000f070148075107080c01505041d034812400011010f003440400380044000360030448a6502c144210564200110307005c9128008102d0a8000c40c2c480500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182279244 1250 182277994 182278003
    0x5040b0103060b0307080105040c08010501061805010507021203030424110d020c0703051c031a010e090901060b12010e0a0902030312060a050d1a090309010905090402150a0903060509150711 83
    0x801c1c450b1f980b03460104814084400140c1d0140c0703400e01d00074001a40d80c0c15044608200800b1603416a481c4144100300940c041c1d0010860a44083c29180001c8240000a41076030001c4505070b070f80201141d441c5200c403420b401c8500480c44890001c000010903c000a000c90040701140f01401d47d00280c42040d0a90030420381e0001c5074400d0031146a44010803040e501070340c2e603d20601c08a400c00c140d044c140280c0c0e11446450300c2040e981c11081642c0b40003000f1081c280130b0300040da01e560f100d0011842610f00710080c6240348420102c14640d51411081903000c00000303041c05045460010b04000507078002c011106030040808a5103ca40ca42d4400220803500b181c0c403860744402c0001da9201007140050079080031004400d0102d5090341d481214544038414002d000c1e0004100480a20031481d1610300d05801900282c06850080c483c103c990035158840001403001c60341c080801c000704041d0303024040e401007051001e411070190901441400d80c00c041c3ca840d080c49480c0407109002d0a0400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182280494 1250 182279244 182279249
    0x70b0c090904150501061b0201080709170c03060f040c030f060b03031303060c1707051e040305031329030a0e0601030c050a120507211a0a0f05040b0103060b0307 71
    0x4094074041e040c40e00e040758880700c0300b801c003100450400b400040c0b958000d101c004552648403a21a0301a1059401160800001401074003401030b130342808130356025024001d0031070043c80380003032040d40f068800301841e010f4010a0312191450708010400016800c00b458800c80b036001341c2d0211003500343c0c0344c03c27400313090500c1c0b270203406100103d44da64045000c0b075042c4003164003440d004c05c1001d4030301c00100c86504000710380600c0c0f88554008501914810340003031603004001c804502c4110907011000d50503502a40c000c0d40c40c0e42c00400c0d040e900e0303030018414074002c04000305058a420703452114041140c604d40c51a402c2c0c20004000a03503030038000d80103030200c001844161106903840e841c014204007101d01819000e040e00c03040c04160490a0b00c0b03160b0711503401000410801c0e05c0e0410201481e12010200d030241302000201c0320000d042042500c079280f00e20308503900d1600d4442c020000311001d041c00707d540d182c141014400400c1c3e23a001010f0550307401c186e001c80d518444e18040780c903082135607 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 182281744 1250 182280494 182280499
    0x1c0c1401020a050405041a1e040b1f0215070e0108190504060501030506090a030801050f0d0b010602100510030b0403030b0a18021b160b07020307230f15070b0c09 71
    0x9011208542d12400030015188101c40401c08856600303d030107910b04c80d000d001c88d00003404040a081101c181035605001d25801400481c01400c08000300308000641803584200d40c1c90b0302a8010101d4050100c2c00c80c1031050f020014507458503404c0107220311204418141800b0510380481c43c1c03459055143c0c002010000424002420b00d1300c1c00d100104824401982c26011b0040400d200c801c004c038030030010030341695807203d4913401d000410140324080c40c01c03954048512462140002c0b5010041402062190090b046c402644400c18040e0395000380721140d0b0b1881414144009000000265000394145c540010703215400c4001c1850542503420803669101e200e515040411216001171102d0004000d5580303601c000000c20f40d030340ea142c41180c00718803000d40c80140501d80b50080500b8080380010100d5004e40d039244107049410381d48880d00700d100580c80b1100036813800c0c000f40b00401680d040e80c641e2a8520100d0040c0300b41e0050400c0100004000700c0800c00705d030580c6060b9038440000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 182282994 1250 182281744 182281747
    0x8040302030a0f1e1808070b0405040b24070507061b060e011d0304032d0b13020a24180902130305070f0f0806010503030d051801050709050a081c0c140102 68
    0x101c102c080c10000c1e05d03101c04608030414000c0880d8941340455420111102000340134100703401c0404000c0540803c581003900400c840466031506a60400d9800f10300c0c040c02c0c41e03113a44501c142000340c00c0a15641241061200e50840140585d5600000000c03850300580c0005140318000c001c0c9003d00b5500c3e850042c80340142c2c9040030300b01c501100910449101c0c80700c1d0b00003080c403100c2e0503507003620000e10b04c40008080311042d004207150f11680c80d4050003003a400f9214440d035900003030907403599801204a20105000c4141036926401141520400906001a040e500918030b8195070406015a082e159004141e010640ca840b243c1140903560000680c1c044607118140c61440c02998421829402459803000411800110301241610000350185141c8440c0b580301d0000340c10b02400e42c10702041d03030707101c1c1c04c07082c41003807145d14050850303907480c802d400d4501810400c1440c041c0d040107107180c0050880802d03465074081960445991030501002c4001e40c0d0521a00c1c2101d01241140c3d00d500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 182284244 1250 182282994 182283047
    0x20609090411180a0c1e0309080f0f0318060402030606010f0905040509060f1303020c06030408071a16030606200a0b01180c0516150204050301111908040302030a0f 72
    0xc201d486440b13401400000c02981158074400c031030b420300178003910401d1215581c0c0d003c0400e10940010702d8150081c4802c40c5030500f06a00501160f200480d80c0300503640100502801000172109010001c091800402032410a40c00098503402d01800060511011142c18602e8500480c0400e000f404020401c200c43d2030541111034480a080364400304101c071140020725400541008000c0c12074041d40106881020441407024039480688182d0701c2803030520003240042e1151041c1c42540080b084c1d070010504001e15414420003494444806060030440c5c24400c807030740700048401510340e0f120700092880080c07820034104090b1400207403920003490000b01f01140050309071030101402c1e50b420001e1950020703046900b8000e50140c40c0d002200c403082032000c18104905414001101d6100500d8242d0b80d00c00030703084401c41c80d11802114400315502e9005000c01004030241512810140c91034a402e0703034020344034801c074440e80040c042d008080707103501449600030341d21940c0c5004841203002e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 182285494 1250 182284244 182284279
    0x609051e07110313030c08030304030801090f1508010b01080a02091e0607021c1101020a1e0318080a0b06030a02010905090c190c140705060a110307120e10020a020609090411 76
    0x80d00780820340c0c07101b45142c030002e02039000100312846250103543d2401c06034249036070315000d072181d02d0040c0095074591455124000e510021040101060343c000a03103099000e00240913a00000d1200c1045032040c05001e01c42d4075482818a0700609941d4601c2441c0e42e20340c00143d01d4010210081e401c60040b000b058114034004020581060142040c3c081d0200400c0049a5520f420780000b02048105124030000c4100c2c031000c510518840d00780a04000d0702d0801241414031160301140003540719480703c6080c00b600700e0303419400c40300c10350207003170252420b40019012551522520f4060a40080002d05140c040ba081d11104d8508801d00080c81451500c0103180700d0b1051003e541800c0b917011030907202900007502404449014110504200c1c2104046e6500d10355481384000b82d000c00c1020000091200300c21280300c520725250015002000b00600c1103154840020340b00750340c0000c0365400540e6480065402d015400c8400c2c103183e9560385491416100308100650f003010b44040d2580112 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 182286744 1250 182285494 182285527
    0x3040803061804030903060903022b0e0d0c03022b080901080901140402010503090307080409020c0c01090608130807120e130b06030109090302010b0312090102010609051e071103 78
    0xc01d070403207100300c16030704400002a01c0d000948000300410640311307080000441c00d41110032003c1c000d0050300c5110081c80d581c100d01070b00c00e11400056181c0f00e045000150b070066400c0c6070340001070b140c0c03d4011100d80d0f00c1031210302070360002910a200307035600309009981040110320301450710b030b0800e03c0c494068a44440950402c45a42e4049000c04000030140b002c140301b084401252400428455120350f001514260707c040c0002410303000421910002c00c0e0700700001c00051218010041c0d1360083c404119080078503e0b035070340b4104403164800704000d0790b00200e103580220700d040c0080f000c6184c0c0c1c13403c0489032055400c005c0c042072100f0510440d081e040402902081c8040e948622922a5004201c0031100c004402c00e904c01c10910060041204a03808002602d10900000032000708000010b4503282c41ea107900100302c0400103a11409590a009032030007000c0e42001800036044c411405441520031808416400c214a8001840f0074403413055942e0441c95401074907942e003049205030a49 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 182287994 1250 182286744 182286751
    0x708180f0405040f03031a040c020610050402040308040b0c19050309191505180301140403030e060105010504031101170a06030611031b2116030f060501201203040803 73
    0x11030540c030380900241818080c1c6803045500c040ca00d0600c280550b0140c00030200a8038102c0c451107030101c0c8010310340ba54480d03041c071710b0b04640003410545851000b45121102d2a0840b902660050108200050342c40b020b0328140c60640c19050b4a403484621124581403590000085142582c0c0d8403100b444000310090045003010fa400c401c07160203420b9941403044907441040c00b41022b61260241c0c4910640c003404480000c811811881d00540c5c0010342999040c44050b02d08680480602c400c242d0903100e6000e0407400340001d88429071510001034598080c030b1002038a52014000d54104981c801d05003400305900740c030341000380c60030420300c50340080c09a0b000894641d4a4030102051461005081e81d03ca41c00c0310b120084180b00c0d00240070309a811550484820100480303240ca8512080d0803010711428400740880d101c50386038000141590265080701c51894030b00721003442141d070702840c2c4640720618a001d0720b0301166892110351500c45403003c40c42c8400b1011003840704220100c4000c501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 182289244 1250 182287994 182287999
    0x408030603060a06061e03321e010b0702010302070615051203090901050d05160b0a030506091e150a080d030c050307080402040f0b0910030204061d0f0c070818 70
    0x4075980c0f103251108a030041d000c0d0001283c0300c010283c451182a41020600f545180f0b00444c0010194540c0a04208800000e84004005242604010038110305450b8000e80340000b1082c1400351001c200c1110f0810701603001d078003400083c04c0c41564001d80440320b03260b901450420485031281803183c80710015004c0c15109402c1108994039911001092302c400c0c950040c01c0460a9103403004000080e864034030125014000c816119518299100510340108031750b8071203e0707685082e01070017002c440c030080400d40304103402010300182e441e03001103440c910b4240f40040c5006458038000010315080c43d200042d844151007401040c046070114031601000c510b0b0704e0a00c01e01489801c1541d4070b0100310390002c005014100000c1c09450700360001c1c0b10001c6100000501c40120b47d02084002d90f0488050b00b40d80c12201c000c0046080074401c1c00700414005020984160025000114041014014000c0413410740040340d000c4050104071605180c0c00310541b5541c1d42540000320400c2800c110891 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 182290494 1250 182289244 182289253
    0x801030201090902071104090201031806050f01050d030e01030903050904060f031502190c080708030c0c0c06040b070201030902040b0a060909051506191701080a0501050112030507030807050906030408030603 91
    0x51600d00f1402924045030707110402c80070080d0703e1000d02004103032010099042640b9102c5d00c482c003020842c44085501c1c0070390000705061800b01d81c26550050180d12480c011583d1040300404283d1096090005507801d03c1d000c5040792071070408441038080c003840130f0360003841c2a4000410342041e0001004892080141d862038691000e0110102d0046030a4142c1d180324041c80f50b021a0721031702c10103403102e20502038181041c119071a1031405420464031103e02c1d080000740c9000904c0100700d0480d608800311a0380703180c40c1c1018151f0340c82c0c2c021a10b000b0f060540b1884900c0841d80c2c0c0b50401400460050f104149050340c490000300006420b04c0b4008403180307024081414080a40c804039510640a044a481c1055503400c4451000030289075808000101561000c1c45448034600ea0080c11100e005180048040c18070600310348040c1d00107200341c100031121100007a0840d096408007038050406031241d60314404180d81c14030420641a92190b400800c10080091343c1010314004c4605500b101d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 182291744 1250 182290494 182290499
    0xb0f091f0504020a0f02190f1407080105070e1e01020309060c0304030503030721060e010b030403030b0301060602010f290f030f0f0607030605010f0206010e0a0b030307060b0f0109140904080c0a03080103020109 92
    0x1400c24a0301d47d8009482500c425010300007082103404410102442e007003c9a42e0181c7d0342d4280c0b401c60b48c0503602d020005034009000442840c100f000c0244c0c2440400c3c04107a1403c140c40040c4d901d22400d1040f6024075404610f01c01d8138070050003500c00454001d0b041d83d43e6498801c8006209034400307284500d0444494034412000d084078132503007041e510003154428103a420502d080c1e02c2a00020822020544c55000314042e6850a00441d402420150004202c00c4280314030101507038408000c140410a07540300d104100010983e42006d074040c151076145500400201182c20078407940a419003600c80d01003d01511100000c0c282e100f4074142e43e0070444e44c1c0d19603004440b141c08a130549001680080b00620001110000058011890f40b00014600d111400407900f1074101d1031003520601d9603480c42000d01c3c00c01504011000109103401c0040d9820207030b5403410003084d4031000d80202c0b0364400050812106904851000d2141f06c00c96898049514006003158402d0104a00040e00740d00c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 182292994 1250 182291744 182291773
    0x90a0c08011505040909080702041503021f020c040e03040b0406091418041101031508031b1603030804050705060403060518010219080402131d010b0f091f0504020a0f02 74
    0x620b582559540e0b024030b8146800641006018141015241c0c030904010b0b0b400103070740b01d1040b00c2c80c500e400d0030703051a02480c5004004166100c1014006540348038044041c441d64040307817102404408590015841020115507891409507402c8900c041100160200d4001d41200102c400c5a44283c00d1001026285043c00190381c40c45500d003510641030070209000030103031201e1611a000624000503031030700c8604610015a5a80d10101c919000021500d0b4104981c40101000e80528001019088285401c0084020b08e6120180400180102080810000b0321003400107140092004d40c40700d403070741030410081100761a080c003500c17054a0200b20401c018025640c14000c004106a84c0030300030481520003d1006204a034440412001b400000704540f088940c03500c090000364601d5020400e0081c03c4440701031a5a105442ca040705840543d1040226644418600e8440c01400c0500400304544ea50780c2e00120740c082d0001c601c0c0840b40e90302011011543d80142c3c21180d229190300301c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 182294244 1250 182292994 182293019
    0x306150807060e01090902071a072001050103050a03140408241303120914010c05070b0112200409050109080a030c0c0515130b090a0201080124030507030605090a0c0801 74
    0x309408141e0b11700080051064680c0501581400340d901c246554241810481d81d4590884505010030b60341c01d4a600002128104280303180e030100000c1010f0350440d02c489070788400c188c10003800c01100114000a421448043c2c600802c1407100702c442110341464440c030171400800304e0504250400c00007503108074501500d4850103400da00e0b503c82e07980000350102c0140c040b6a200391100304691840100c919001d01c40d008444942d42c0c4d80c90344074965458503da000d03006920803940c000d101c0d14180c0101c2d00200740b40d03081c160080e10907045500004007040207080d01d0b16029005502e448885030600111900804111a07183e070200001c9070304600533501d401907003c010740340303a000383d181844100c0084102a0012076aa1094081d01345039510040d0401046448030404d820142d050411560400311a07805440c00d0300c01c8022030b1102c280c071442411400000c6004042d211004245001d004c3c0c1e2250020707160140c542c001921313010703404c1c42c05009a0318034880011508400054031000d00e20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 182295494 1250 182294244 182294267
    0x60608060f0921090d08070606090506030a030f030c110a0302010c0e0d080403020f030a02060705010209030132040c1703030108070603060e0705070c090c0206091501120219030615080706 82
    0x30fa04440300420325441d00d040d41080c400e4a801c04554002a404a4454409000218402d48000c1035040c248000c0c407007076440c054101d80c000d51180203401c00180e040412140d481400345800512510141c0045403c40d242c040980038900501088030113155064214106ea0080c54485030403840c0103100740280f4000c111005068201e0a100c203000502d004050010403400c000d040f140d52203442e800141540d407042d0000c50b01d50394009550025420280141803944014260f03036014a094010301c2040c204494615440b5000703ca00007600f08510640301e0400352040b504c0a009042c04402e4480c0d495000b801a05c91521a8030000544681300707000d50310541e00007d43c4052540ca8449054445d5044130030200c3e43e036001300c1004643c4520b00d118440070b541c1a03600904082c20510f03600b9083c00680743e40444c40303800e240014004d80000390300c80108d0031b90545c0c00b484035100e0442c1100140080380c200034035150800706092070040da5089141d007a00c10701e902b580c100d01d54035081a210a003560 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 182296744 1250 182295494 182295523
    0x11103012411121e0c0f01060501020102180d0f050d05120105030a050307170405060a030204140d02030c0d0812010f0305070e04120c03020307060c050a090b0301030b180703060608060f09 82
    0x405004204040c0301070303d80d068a140c4c0c0401c02240c0002d6444868014821001155110220b0890840d40074083c1000500080c0000c52500100c02d07040341e484080f900596000b00740203030001c0d04019400d5041001541c00c101555130305207060000074804da120144a0b26002203500010426290120300002021f0b40b2000071458200c60b50745800ea5004016108d02150400380301c00101502c0d554024243c07000a40e80c0141d44500789a0511030784c801126440e8014607480b5000c00040e1400a41d0301e1007118111040a00040d00c0d103403442003803041d070031480380040c8824000100541440382c1e00050340e04c61010b98804545415a080c40e103a4100e501402000800c4401040540030340802d505490080c0f044d60301d031008584981040d5901b5561303600002d54001440f20b5016482071602015007000c100280c9154950f484030820303004043c2c03e503030707251400380c00590756060100a05401141d1000c0c050000030b81d1010041e8540030202c448408480b001c20015030981d2011620a035210f094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 182297994 1250 182296744 182296753
    0x40c0207120b1803040305010606120209010f14042103030e0f030d1805030c100e0d140a09080613030206060409031d122a03011506030905011103012411 67
    0x3591145903201c80b0180142c00c0030034004032404202075082c4010009140904000300d000f80c640758000b44007400d100220000140f06000c1c000503603a10001c0c1d0540f410302450400030700840d041c0031a00c64130556100102d0700921100e910080c070011349108054a0007a1000c00010f100117403903540761810800605415042004220a004a03541c41400c2d070240610702c0310490140c50ba00c00740b45078050303560400e00703034000340c0b01c000001d140340503d80600f20b28401a003442e10340001c024181039091800d50700d0358030002c180c0e155060710851070440208581d00466400c2e0600c0c2444183c1000c00070020b40045c000d17500000c03642d0800d0700400c1005e640c1965102803d0000390b440c4103e075081c80c3c0a03558400e1060000386d4a0001c00c0010016984188043e8009654420003410b00c1801d40b400c8280640d04100040003200c4c034503020b00302120f0b1241400310701182603151050040c494049003c141a40210000c654a040d12100b01c00c42d201c0c000c1561072181c041c50b0b050700d00c103030000c0300c8080c140e11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 182299244 1250 182297994 182298029
    0x9131e06090e011e0e07031406160e030a1104090f0b1902040e060907110102220509010303020c091e0c070218100b0c070f0b0c070b030105011e0e100509040c0207 71
    0x42c50740a6803845e134240d001d64060989a40e20f0b1481187e8060508443e64000f00500421603c0104120b06500c01c078105002500145000719443d040b8004022704401d40c5105000c0343c03500ca03500249070303040e84056040241911880c0800020f582980d4141180c0d010035001040704400d4404c42e02942c6407002805003035910103080200c0680d004003443d08119038820b24801d420340900280c220f0117900c05004c42c50074800380324140b4410b016800725109084101c010800300b034021a250100880c00d035081d94055543c03040082c0b00200450501c4160050a401c101c4aa805d140250511078803c80302a400d06e0100716543c21201400c2e110100c44080c090820080c5442c2c10004049a0103060155040c0c0340c1e0b5018034000c0d0700358540c0022604840020940c40c401c100703100300000b800b10509501d081d941024002400a000c503003822480b18591000c01d944907002c0c080d0324844c0b0f5001052001c0712200c0040040843d048410302c1c2d4001d5090032566401540041503034400e84215841e204140e15 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 182300494 1250 182299244 182299301
    0x5040507050d03030b09040c060e06090d03270f050f12060723030c12060943020d021204080604020d060e060103030507210509131e06090e01 62
    0x32101e1034110113242d9515040d80e050b456103101140720b54041d9020302116890704402400c4580ca0044c01440b84108100b101480d2780e6003029008a2070305450490701603483d120356030324541d85014051a0401d00341000103079221030701d1901400d4890580f1101c11480e061070600140640300700e0b06480c240c12141c0010300403441480a00310f2105a1074114213041e110301101d900c294010388100603001c4001424141c1c0c100505c000c032360090030a0342c00030f47c189010705581c04d24000e07546101900c0a06d031080380d5120404001e0350750806040d6894540e142c0700f1028041d51351000f1200880150203004c64094403030203040182c0d0b0454403408068026655a036080019081d076400044902c1d0360340d54181840da0400704911800b83d07120780c89055841704a4140446280c1d1101c90a18508000c0701012151030390000588070040c4047d142c2c00d09403070b080d00e40740d0080e00414465821450b40c4034142c0c2d40d00d01181c3c12001c02c1710501e600403c60a09503060607402c0e02c02100307060840c284010f0003d191003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 182301744 1250 182300494 182300509
    0xf04050d060203091903391401050f06031c030b0603090a0302101b0c08040e0c031801021c020a031d0d1202030705071202010f0203180d210f06030f0c0303020f010504050705 76
    0x10030a910803940c1803a080741c0402c001c40180c101502c0056198231503444000c0240708503a041181d45081d85601e1400c2c1c0d0019503118505420381c3e40d104943e042d90602070380607401424181c00010300b029100d2406200042d0b80d1800c2510030b40061103500c96589491036035120710100e00c0005034182e00d80100b16030007501c41c420310020458080f2070070440081c0710604001c0302401507600901c1c499480c00c01401508804030b00d6000c07100141d10420000761854041607502e8040c90710103002603100c0a401105400408c14402200c40702c4c1410800802c801001148140f20900e00e92203180c021111030301240d040340411124400419070170058880821890070440c000c00070030f440049103d86402a2840c10703600b05441540426610344a0607280744410702805081b40c4241c501a14000c0d02402e009007080300ca000c6285040da5207040d03143c02240030350041c0c000b17141c01c40007807020b0b2440c0340303400c00a00b105403005034018020504a4180c5c48018010140690781010040242904180422018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 182302994 1250 182301744 182301797
    0x60903022b0c020f03030f04062a030e180403030b010f08010e0106050708040906060c0c08210c010e0723010c0c0303050d020903011806151a0f04050d060203091903 72
    0xc04c81009801c10b42e0f01000101401c0d01100ca03813548451078901c001c0d00b2400c11800103450044e13080750406124680104a1140582614200e032264610074085026070310241031440c0780c0c01448040005050305600080044942a603940c1444000ba10040380c00c4a070a0003007a5000800400400805200728050240240117050f8280f40c19aa80e141d54100e4410f50300003000701c0c45600001052020141901d80100310030409045881103400030111020744c56040003142c848041040400400309510443d07410418008035016143c46001ca10f0603d14002d13134074000c81a4850030480300754800c419140189902066041d40303d4119917058030543c01c0b16461000c1030791309100c3d8589581c1c0074081e480c140904442100901085418400180c0f06071408510301560200c404001d050040b4003d82c80307c8900070103103915406c50800204e50b5100700d03030280c0e40c810000884001400310075801980120b080702c088524552030721400507540d124116015011829600c08000070046a4190f0b038030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 182304244 1250 182302994 182302999
    0x60118020910020c01080703021801030e030409020c0c1f020a03030908120f2e030f020a0b030403090e0108060123030f0609010606080c040521120403060903022b0c02 73
    0x200382899001c02c003641c1200c0304250050b8043d195200065820298407a0044038074030b000c2d4901101c0381d840c03418014500341d04604040d62a005000e0810051081c0c501402078480150f6480362900d810030b03512061080144e2280d5003c0800c10204103038440102d020345242c0e0050a0008200d46080e0020800e41c1415148118100441991200700a4020b481030302d0f000d480f46d5481c280080b80e010383c3c4074030742c1d802c030421900400701c60072031001032145400f00e0303600074241d00221840d4408120b14078110760285031804004400e1004254001d481c28060b24100c1b1071b085010307030f42c034841c00d643d5010a210707007880e4540300101414011145c010603c078846000e011280d503c0c40c21107166207811070450f4007d040da503403514144039659000c1812500f0044404a19003403509140021700d1918112140000c07080c04007440002e1080b0601945100500d0361400740c0c1c03181d07a6818100302030880300c9000c074010f024901040d01101c080c441240c280540c1d802d4030003c520110441035408000e241b40603603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 182305494 1250 182304244 182304247
    0xb0a0801180f0908040e0a050402031c03090c08030a0f0f09090b061620010206010506030106031d01092102060420151303060612082512020106030c050607020306011802 74
    0x40c002e4000d02540c2070f032a00c079a01d01e40c0d540b460141a10314100c400703442c03070340054200720501016075000604503480d5440030030700b88910f001d2a030065008110b610801850240c0304a0002404440070000d02103644580d02c406203a2052000c0803604440565903170030102d2111f179424803030103800c0c1c0d1001044181c0a8010751600c54601070700d81218a0f07003101102c0c0c8008480280305801b080c00b401c1604001d0a0004084075410302c40024040e02050042408059580000d012003420381d0342003250850403440200529082410000905d0060708110300244c0169038424a2251001500c00d2040c1d400810149109001c0a8902c0081503c203004c640e002c2d50008000360006600c800405101d20103c040459851641c5440c005071441c0d94070440300c040d041508207011030305031400c80e40700401c44000c070307410180c03a414900c00041d0401c5002d03140c41da004643ca4101d580544c040c82c29a40240504500d10b5552001c11280d4031541d100290581c1102d001000004c80941c40510342500381c00c03015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 182306744 1250 182305494 182305511
    0xf08010b030402011b06060504060b070b010e040507150207080d080c091905030d0e040507050a0c0f0512030a1a04111e07060203160912020a140a0f0605040801060b0a080118 76
    0x609000e10085c05a070312542c2c48100304082c2c6098820b210050880d026241e04015150701c61417200346c0c0510410145485402c0007e082140c248110740252a10f60000307207207800c4006009503103124901494810384200345081d20795034011003040c0c6c0702c2c420081029260481d80d000f03001002c1c2003010b65103940342200002007016a014058102d80c440b0380d54690390811281810030065600240140013400001c1000a100a41c46806900307419001030035405905260710700700c0d142c0f0040301c44141c44244044148031901d070365030b084070410001030303004400126402420001110480c51401d1041e0908011103803140d91a80f220420566041300e64600700340d05522110266441200da80001c00d21101c403500c456a0442803400c050640d000030017601d0410f5602044910049029038280c41c483ea0980b0151940e070070742d102018042c4003480d01031050740e03000e0140840c0c0007806542c0e40c0794204140424007490340c41c10ba4450880710366a40e210369113403114042e1840391004a4542c05611554017 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 182307994 1250 182306744 182306777
    0xe07050d0609020a050c19050c2b03110c040509030318120301060306050a0812040e060324070f08040c0b03060a0911040e01061b0204020c1e0a120f08010b03040201 72
    0x41c26010204e03841d4156a4030901428a007000e40d07005840448900001405011460010304642041c00581d10080e40307403415040d03e90065031007941d14003000400700d401010180c0c000c001031a2020842d04450700407245504210540f4011141031015034030500000300e82408001e580c500781c50036403003a1404a00200b05661150388260007040109459203c100018200010715100074103042018090433140c07903030a0320103440f40d4480d0994803c400e0703010401c01d81c0c00b80180d4803851141481c2451074440d0100155000000711500400314503401191a4814001c000e2540300b5075201000c4426107062581030110360300090150740e0042000305020a804810348610401c185052108503150703450b28625800d4508160810702c104901e0142d1106500c19005284500c10741c1182c0268545000240091420300d98510120240300c140710392103466000821403001180c01024075500ca11200d4500b070b62030aa20303254100016615100420035032502101640d0002c0c41450964986000f4000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 182309244 1250 182307994 182307997
    0x1b0109080304020a0f1505090a050d150e190b090708060c120a0c05121f0f090b030a05030307032007200109060c02060f0f070515100e07050d060902 65
    0x508850800c800002e1000f50301d4040c07203040080144204a0803c0c2e81841801d845900000840700c090100c08070ba01d08684c3c0d590009880640009031844080d15000e080009131075035504118210b9a01d040c81c1d2405444001c500d8241c01e002802a45442220503030790300107103400c004d2248009015409012801040c10300005000e0a21004a0360f00c0e1401c1c40341146101c900503147d00007061800411141c403d800c08180c80304c04070031190b101410381c0c40c039030040c81800300800d4018600881e000040f40240014840400391a603d810030414a400136041c107644003142000a42039070300a01c00280c0b550300c03d800c03500c2045201000c07000314080561250079160030201e400c403100032140c43c0c2c42c1c800741410140811005424601501007070300e081c2010741002c1c6100c002038056680080c146140d480c591048458003e42c181c0c19a40e41e200d41d050403a281c04d0b50780404409002028082021281544800c505444225039401c0d95030f1201502038800794440d400414101e512107800203203030f07101d520 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 182310494 1250 182309244 182309261
    0x1e040c09090b1006180302040c0e041b020606030102090d08180d0303050402010305090d08010b0a090513020405150702130e011d0105060102070602011109060a1403010602070314211b01 81
    0x15080d82c036802d003081001c0600c0c02c1608050100800c03483d4244013603281000002c12a901902c00044c081035040003100c105620381c849a410500b8516021045807200b410301a92050705e034203841c0d07540c0320a81018281c0c801c240102c0c2c0d12003100c1c112a4049900e20300100001340d12401112202c0c2009008109d65224008050380401c1d640d608000035542c040c0aa070b913010300c1d032002422180d000d02d180a0000f1406008002d00316902080000e2503500038070300a0050480201030001040688120402940c01400303490302952389890210001c03040b4a040d5429164004e10001200b850008000010031123080a03140c0c540d241c0e02000b2901c0a05ca803240154144440045854239050002919000d41c3d540130340116031505109031a22011101035608001048441e20703500e0000440480d1002c00c0104142005400040000360440e00041c08800300c034414201140790300b420310101c584a03449002d4040c4207940c0c0704941c4603503010303d01c024480c141888200e07170540103091000508460307070700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 182311744 1250 182310494 182310503
    0xc0c0b010b04090e030720010e060d02070512161101031d010f051e01090c05041703040f060e100f030e1501090b03030a02070b090d060c030b10081e040c0909 69
    0x10144141101c5018503138007090624000d5184c00e00c00d540d22102c5002075503078050150490443c0420320780c844c070500800243d0041000b03458034840740036030300254801c21b021121842a107041c0340d5000840001d5800548010080401a044540b5040203050495214504260799160304841c3d182680070307c2d00780701029a0000902c80d000800c1c46003200c101901d094080e1170a0350f08002c084480c0303422241907444c50030002c900c1c000c680400362080d0180f604015000c11041c0d80e103030311190303001000d0812a0b02da82c80c201c084960300c9030140e840480c40d4420b5034100818038100240103000d60b0f00c40002030b0442c9000641e00500f0303106141010010707161001048036120040003c25814003513500d0291084000d5403038810002c1c0041c0d07a03014a0321501000e180045502c401940e103a8140c21706140e04040d081c01034008104009008240e00c43c3d40903c11000b00e1000c10358184552001849040a440c807102d200b4a0300b0340c00154828000d000302c5405040d0500801d603140c2d60301a000320184076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 182312994 1250 182311744 182311747
    0xa14090c090f010f140402040510082a07060209120330060307060c0512040e06100201050c1c0608030406020604020a080f100c0c0203010608070501020f01060e06040c0c0b010b 77
    0x34542040382500001d000940c0d151441c070014803480703035240d260030203c9030b029421a141c00c00d40300108000c0d0156520069003c4030000d0b18000198006000d80c1c851a40c19284940d1003201c4d02003241c82c4180608220b0344280c0c141b0951000407002d40c0140560800185072034803002c0110000c0d850365200300500014018042100c1013003100040500c4824540d844083c211485d10501096848983c1d1041d44208103000d820070061000900c81303002075844100450380c3d5030b900d40c1201d85c6442019541c0600640401090040031072041c810070707000301d440314030131498012841030810700e5411518100c1141a41c400c0d00041340d0b002080100020300d100e401504561506004003c20816250300c002ca407a0414800c1c070700301702d201044a00206c01e000c0c074005046020742800321110150032100079095842d001010030103040c0040c281044039000da00f2580700d01d580e00c9140342652818070034440003008007804030310795141c50f800904184050b441c2040403058103840e007a00b00d400a80c0004042d020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 182314244 1250 182312994 182313013
    0x40602100e0c040c1812030e06090310050c09060408060603070f03110d14030a030b030c031605100c300305010e07030b13020706020d0617150a1409 65
    0x20148208245100c000c80200100c5030011041a2290111850b29119030795580c08641801c0c02007010946100e0a850313100300094841c03108200d0030a050380290081000c400c140c040c903180000460b0540013018001d03115128007004c080000c2c280140142480090920002c2140e80311103020308028003601e0020422401c225080c1400c7c14059000300035a8504a1801c1c070200c1d00040d2800d0300010151070b404c10b6103040c1c0c01c0c80140c9110540940c070440c040050a4100710f903154201c450342c0c0d90704400380c81d080d9100408242d42d82c003c03c85402c103850b400010030441464401260184040a820b04480740141c03955000305c0c00da0403031210000e030a4452074462000e481c3c04240c0e080e80716981400c11080d410210051100c1e0402025042055142d6203c1d986a841c1c165039960110f00180c015500d400725071900c84c0c00f0f50800e0a0448086103007031000680100c1e02c1c20b00217812420f0f14050015105808203016505074005d203a507070741c50348603056a05c0c690030f0f11031081d00c10040c80d4083d002514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 182315494 1250 182314244 182314247
    0x80d02031b0c0117070c0206070506151906050904150f2108041707030203161706010506030c03070c0f08040501020d0806010801331e0221030403021903050406 70
    0x4409803188425400035039040103e0740c000581d03102500146840003420f43d60700400300c0f40e003030f8080d10094000002003051400c10000107581c0307001d803e0164100c01408c240300c4c20707c81114120360566000c48480f5808005803070044005207202640a080800d80e0031190f05200303040c154031781c019549814041c0041082c1e042540c003440840a0f13428400d0441d16141d1200340890140d40501e050302030a4240d445080001045039400850707015043c0c40e100e150802030303900c1c854010701c50091144481383da160501100400e00c40d060350340081c030301811921f602c0c07803010003600000c2940082c001446903100c0420f0f42c0210800368030388039480c80b030355803401c02c0002400c00e0b41c009440f00510650005000107070781c2005201d41510007801003003807001c0f6640d2468950300440c1e1500600c21581d640f07008000c690100104000724400414a0440452000d0880e900c44040060242c101403407444030f840c00d036241c8011500103003e407040b141800c1c2490912130401c084080e0440206400040c00c00145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 182316744 1250 182315494 182315527
    0x50903070203060108010e0c01030e0a0c0305030a09050301060f06030506120102030a02030a0b010f080103030f0c080f030603070b07080a0804020a09020d09060c090b0304021302040b04030303060504111809040804080d0203 97
    0x4001c0c5c080240156008525450755a4640d1180e0a060588030515800740d20420054124183d8101c10403040283c0e4074100706031130b9440700092500140051402040a0505000350021103c0554280b4905844d0001c120000d2202520003030b4410003080c01c0d6640d05030309001950040c6491340b00140c3e40e007401403401048035083d0310014140000c000e18100c1d00d54000d1002c40c1126018240340c82e031280594011079001565150041070400041800c00300c405011000e54402c074010307003c030303005a502c5100781c43c02800340c44001094410108110900a48103160203504588007428582d1003030b03107402910059800048601c9581980e90100d5014000e59000e00034000c4400d092090169062029548062000500207801000200031442d03200c500c51b4104c07802840e44444468950fa00c03850000c01400851080c41c0c031890038061f00f5078101001c0811a01501e800c1c000b4650201d0080050040c5130200500503500324900b80300c00208941c0501482643c01810b6001d56a0b61023420386280b0700703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 182317994 1250 182316744 182316749
    0xc0207060e0607030e030c04140415020c1c0306051e090c03190203061201061503050901021201051c0818040e010c08070813020d060509010e01052e0302040509030702030601 76
    0x700050640120815181c0c00c00325403041c1d406190166040040070046441c0c51250441c5507041071902103003c0700c404400b102c41303000d00e2180d40c042000030b43d5034a410090703000c0c100e03914041350800b845500e4880c420b000c100350081454100840e04540e29800651504890800d0215000001c0c200b50864548525583d90101401c404182503040c00340003000c01030a0b03540b050302c499900002042e420360303e01d005141686900030007882107548501d810031840035004180400300381003001040c0c1111042c000e5034240082e00c5c0007006c60fa0b00e088200a4010343c00c000c1c0c001000140e16215001c6103081e80149400c0c030150268041d01c900d0398050000b16284503100400c00d914000c0540b400030342c001c0c142170b000f00c00d81c075160281d604c80c10500210280c800c076000350700404604e001020000650050fa21a42400f0b00070494041903c03851400c1c0d070000c595898642c59071200c20f1030510101c03000082851503074402030380450344907130109003101d0080c3c900440a62003c030342a001c514081104501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 182319244 1250 182317994 182317997
    0x1020d0216180b030a0c031e0506191e05071403010b070809150c060a0627050a020c01020f041403191203020f0d060e06060a0207090b040219030c020706 67
    0x590901c0c0e0050411600c090103103401c2070000d0a030034440c0c54290341091640040082c1603034612801c0f49040c6108596034801142c80c600a813185090003204542a00e0526400c50060022a45d80e5605050a0a0040c0c02002c00320399501c0002038841c6105000400f9151074203001402d07041c0031001400c0c2ca0340040000c8072140080005204501c500720a0301d1819622903070003600c0d01e4841002540c0c0500c41c84c281d550b40d40f03002c19450b44c001f0300052414000c4200303e47c01c200e941c3d1618410b41c022655000d804d1206a40002d0341c9200d0322855100d0ba90204400400505020300d01c02f00b06e0036603100c002c40e070a03c01c4010500740041c0c1010001c00e140400c00b00c0041501003061603102c1207440d030004014228150f22035038211210301039011101c4400b0401c0c0c640340e80b2000d00c6010402081e4501841c1d40c500030050014605003060f8048802d030b00b01680013050301c02d140003003004c0a4542c048400303420540034031a0039020031010038249419020b03604d01198004440000901d04078032a40080e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 182320494 1250 182319244 182319253
    0x70f0806030d0e040f1407020303040b010b04080a1202010e0a0308010e0906090d030b01051c090c060306050f040506040605150c010e0d1d041517060105190e15190501020d02 76
    0xc0340c0300e410800d00030f40210156004102040802c84034001080c6524000c1e04c091410420843e910360301000841c40703688580c0704d4907070598803600b1011060140c1e01401540c1d500100309000403c915600260205805100102c0c1d101c180004203070825400b001c041313020401d074900602019800340c607035582c0030600c01c005041605c2c0c00b0030b44560314500c2d080100f06065403002040b050b644100b0440e00010300ca40000100b46071030001e900003c000d2850280c1d01690018000714605100c1c1c040c100407078100a1000440d5510501000010480600703c0c42d4040c0d41d903600003440d5141c800314443c246043c0100140c40d0301d2442f40c05402d407410f030103000c10310790007a41d41c808640da00801e4004050400b000300301a01c8c402100401e008110845289000b10b040c035000254140f402c50010300d440b41d400054a007681d99030350600c120150b0301620403040140a500601031400c500070300c42c0d4410100741c030f01003030505024003140088051481c10101080e50500078007035960100700d4442009032500c003e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 182321744 1250 182320494 182320513
    0xf030a02060106050705070e070c03020d08040c090b0d020307060302070b09070f030f03050c2b180e04081902060601030e1c1101020c01020c0102070c0509090a030521070f080603 78
    0x1d44405050103010180040401d800701405810000e12003d400c440a4071800c9082407540902060480a0200c00511407010000e1689200b038200d503000c0c941c080049079610341009584409000c45070310103504a6009824100960b0341000708100404050b100103940c1c502c0f5041821000c0c030001c0501c1015030011800300104010a042181203e40000b56407015810720300c0c2c11250b51080c002c503e03a82d03120300043c0840b8140c403c862240c00c0c03020f81c101280007441c00b41080d9030850540c4640201d0707440c4850100b0000002081d034941c007900c1a2005840d261018100018003a41c2007004001a840441000b00c20b503010300c10200b111452100034026021112101400707158168914000c000c0c40b02148044100c00b50142c59001003210020740d01e485050610724001d411030001580d1902c1c886c40c001a041c10a0f0140601559000000c1d00103403803292000c0c1e61f02d5005008051a80304d071030280812440c0b50344a000e00961466503058070f2049508001440e400700039007a02c0c071942028100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 182322994 1250 182321744 182321747
    0x21509010b060d0c200604110d120906020d0314191b0e0906010503040203031801180b310b09010207030204020f0307031a01020a02040905031e03100602010b0a09020306130c020109050f030a 83
    0x1c1b158401d9100305001c203043d180c14040b91308a10940390007008940031030216820303140c100c80444107403a4035500325000915400001c50944030000d4030300403080340f640d000c10400d0103150408032611481d2000410342c1041903800c200620f4050340082c0001c2e0940c90300012070701d081c1c00e0a640280342440c02e83d0075810542c00103511382c4900140c413003405c0c0100c4181046640600381180341024180c01c00c9070619960003445049030b1066025201c8040b43c417150b820f01c1d0070090102c1401c4aa40d50620680c42e0030070714070703030301d141e12801007a4103510030288004010380d1240014001410004203040e16401d20000c0513050300c0580409180d2003451005140780d81c1d07400900c2c03164075601242c011840842500f041e03820340c800c0030003080050b034403400042d030004c408030700440c0180c0c0e480307a403040c4c141e950303803401ca080341e104040701540a20561002c110304d01440d0051500004000c242440c030000b22012102100d4ac080003030009030b516510900c0910605000d0041c807000d1400c041d62130000140c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 182324244 1250 182322994 182323003
    0x303080606070f0506010b2101080705060705010605130b010e040b15090406090c031d07080715120c0207140415090e0f011a1c03021509010b060d0c20 66
    0x180d2400380c00e020402c9000c0c4945510400c580315086802d5641c15616680840c00380da0202221007040c1e000c00900c15444040005460b049580030000b6040003800e103c10848260701c0310009903011340d00d48001007480e540d129007160181b0b01d10a4001514091800050085150720021503c110310340060410340c0d0b2a1a040300c00b50210042d052f0b9030b60862140060f00500c096003122410a140244040320a6010392214a040e0074910041e0381100c1503000403542c0d00040d0182901a402001c000c04c0000c0030a140d01800d901a410b112504c4003985001c00202e030600c14003840140d11420041103200188107030300c0a04c645c00c3c0d5050141c2d5401c00d8480070500c10601c62003441623611003081c1c800d003901340705880c030b4100b921000340442201c5c000304440e52507025203460f2068034815613000f0007044079401600312a5060b006018000c40c0708481c4202a41c0043c151905035403600c44000340c580e5004c004141020504030300240f034a00c83e6100801c40d200080145412408003041e50703808240009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 182325494 1250 182324244 182324251
    0x509010e16260c0403020a0e01080a0b0403170f010f120201021903051315080a0504021003050402010207081203090f03071509080f0c0109060f0507091701021e0301031704030308 78
    0x1003000c42440c2c0b00e07002507089040c80342ea034294588642c040c040300035141d10080c8110ba0084500d0030900b84c40b040d0162204000384a01c50fa603600c17690004000851f0341e410240d1050080c10014101032404c0e03c107030030691b412100320100c81704010051141c1d510150b0080040c1a6084ca922510640741c1e0021f5517a0100c03a0a4441070b0813110005004c162007101120301c1405168000c4201a80d1920180c150900c1d00124030045944100011030b0032a4600c903951140c0c2d0010403800000203400342c10341c01401c001c1c001360b0450280c0c28001c160910104449180380c3c501c002c1d400d60b80e03c0c10400c490b0520002d00380c00080d45c3c104001035408102c0c00c101d450b60404540400042c1c0c502c0c00d14054069110b440c42a0100710f402242c090120203041d0710445615004800503c040040848850100d6a0071500d100100b2401c040520080d5160000302e4002c40b0040001441c2a009040c100f00c0026000f0096808220000041c8204608066640c100c40d508440c114101821a40c01401504005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 182326744 1250 182325494 182325497
    0x3070f12060b0f190206091e010b030a0f05070915030807150203090d02071202151308010903050a03181211030702090109050426190e090a020406030e0a020f0409020a0e100509010e16 80
    0x7500c234039030f01c29080d80131005440008045035185d80e09407402141c1ca41075101c1c1601c041c06400c10000d0000c1460094a1039600c0d110075010a0500b150340d1102d43d60042078003500c0c0e000c0d64056000c055040351000b1402491020000d01100175604802880c040c000d800c000d41d112005591040141c41d008864070400040c000c40c2520380e9405809481480041c0e031040c00658281032003c03082c1b5410600801c0852010b540034400203c0c0c034401007004071076400d002020f0624117410b0340c5842d44203074002c600d00b03100c140560345001c405030002401e0310b20030780004441c281d840040c001001140003085000700301d030307881410310101c854550302140d0280040303024481c03421050505034035209a020010304140109920004c0c209804004000e4109021303130700100b0b181088e1054980070001e0300080040d40204400310507501401400040e203000c6104a03041a112240031815544842c03603030b4865a0841c0d0411503142c54002000106141030344102d13032501405080c4004601c0b140031420000200c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 182327994 1250 182326744 182326783
    0xe07050604030f0b1b0d020301091415150d0608030a0806030a03270e0f01050a141e060c030703031a011707110f01020406081b03070f12060b0f19020609 67
    0x1240c01d840121380741800d05e01907131070002071844001c0041e6800345059460807403042200455000c070400441c02e082e01d400c85103000b0100700703080c0c40c034001c4003410311a8102150941040c8680d50090207030b0f00150000c0300c844d000410030410f0140e00c92411507020f48124010f0078003050644000d030506507501d4020f940f800d00206450a10a2440384a0000f8020540c003103a0320310b0b0860141c00c2c020000e00905100b004202170014122903107030f0703800d5242440203003071080f901010b502c5984015400c041d4140c01c018107220712000340e14248094000c0c2802a00c012036660b604035011000c80049590550502c040b0401c643c0e904100303d5042580142c2c2030400241e40c860031007a1500e060518030340000e442d8000a03000c100181d10100c07031401114410340c1c81c042e0002c641c1e0006201e000480c1c540002620010b8450000e0380b08840c04d122050140c0d5000030032030346980c107490081d4080141da0840e603c1c001103207040e45240b81100580c0340c049201520076030500d40c0380c0b140c44030360b03040c510106100b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 182329244 1250 182327994 182328001
    0x503010311010201180f050105091c0806040603060c020a050601060311040b0c0a020303160302120304030503060d08070204050c12060301060b0417010209120c0114090d0305070f050607030e07050604030f0b 90
    0x3d5012a0304140b511620403201c18175460101004001804111400d5003010003048a203500090065529448a584200414550301007207070040c000916466201c1d03120a40000450281e104007641a00c0d2640540060a407601703080385072a40680c0560f007010314149401e0b0704000c80c0c1c0161400e03611000d92041d601e203460960b07545030051000c00a5414040051240340103010310819440c3d051003a02660f242500070400e01101e80002c030303400380200700c0800c0011b090303140c1820382e803501d503101d84020703410300d01181c006c1011110100c0d1004803d01000a09610a6070300b8031500764002e01c114021301c0b80900301011034100d400340c1e100b590300039444950100385883d029010f80362084009040401407030100c103031980d560700154040e103001c1030303100d4141041044d901e800c450424202138004002506540e4080320580d200c40010341e13003079039000c1c0d00200050b018071443e800b50349290340101e080d941d490115800d141e503d07030089105000400c410000174080f03030001c444480c0c01080405040d0b8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 182330494 1250 182329244 182329247
    0x2c0f01030f020f010c0c080606040c050f090909100f1a03010c120c03062315030f010b03180f0f010b0406050d29010b1207031e09030905150706150303050301031101 72
    0x640343c80d00406c031281d1031401107411040000e19a00c0f80030f00b29800d10000b10844803e4417103104411200c00581d80c2005a10802d041504a070f942020014080710705d05401039192604640402d111009029103911255075040102c001c2c00800030421030081004110010005e410b13105540000303440b182d11071000b00111806540320800030081c0312000c04000d00f15201c195030307001070b01081520803202021600704901120742504d200d0b035200d241201c10381e401c05490318400c0c0c0009008428032660010b2819103054107002210029500384014010444040c40450941e610280f17007602491910300304000d03035541d85c03105100b400e4100c0c40e441c06580500a00c0c03000000c1854034084655418000000d00003030000040c0106000c6180501194441c4d51040b0250b464000003400403440d0103600300c000440d00c0c0d12901d1018424141220641e5591001c01d1001c0411006026580070106d4500b00380009401a60360f1501c200d840010954199038001d0880d0006000c043c101c50008000d019199 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 182331744 1250 182330494 182330507
    0x601051206191b112529070f0b0703050c0d0b031903080a0f0b0d060209031e030c0115050a0b0a03140a092102060a020d062c0f01030f020f01 62
    0x4955950401e680380c03d5520301805072044040501e8961141c1982d9043d08811003842c2d9401003180380c0007078440c0d40382140c05c611001070510183c09071030680038010b14030000500140440e5214003010740d280d903594200350070380803c004c10142c281400c0c1000c1040c8030031004221104841c0f402c00010f008800340b40130a180981e078000c0e02e0310103040941d441b001e054014000603c1100101003c1c42400c0600c00a030702a195208039440d0007441d480c0c00100080c0300b94018100300407010301110209503400f01c810090002118040c0c0042d040080d04c0301c0340040a006042402a0211550007002c6ca4040460b800360014400d20348110400700750303448400d200343c02603540c1c42d60b44426101c0c141030016582009000c400012203940c564421098094980c00307160b144420050b40181c642541e03504208070281d40301140640e20141d07500d4010501c8050700304524510410052860440b10700c81c001c1d051b001001802120040007014010400a2402c0d01641001c9a05440c00c0001d41d11103030040c2d800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 182332994 1250 182331744 182331761
    0xb011d010c11040509030c100c05040302010f0e03150105031204030c060507050703080a0513060f1d0d050f0618060f19021204030e030c04180204091110090602060105120619 76
    0x21304082c244500c0d118000b000d06100803100301642d84c0c4401c42a1800b0898411803140c8000c03884c00d01040000d98002d070115804c0344000e080201d6960a02800282031008040c0300b090080100030060045007800c1150440040464101502d42402c54455040c80c0c082c031312a40c0d04005c400110702c010400c09004410085502202c0d19886520600c405841c0d50841c84062000904158001071068441e10501801c00c8440c0ca556030690684000d10401c11030011b401a04542843c0050300010401c2280301d0207a0001c0e0301038405410302d910744050030340ea030f075040a0032940b120041c45180700c5039084035500130306056445080f14504040420207030040911990607040410f04000600d9008505041500011030994003500b200070104000c88000131a070015844803503015100500b859484070840e103015140022100c044180081d102c0d003100200300f00041c0d01c01c0b004108154042020a02401301154220004030303028902c0c69941c00001c2c1610790322506100009440c2d0101d5020700315 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 182334244 1250 182332994 182332999
    0x507050d030b0f010c0b130305040b0403080d06090e0d05070f060c170c040b04050d0602040503030a18090b01080708250203041707081e0106180506040b011d010c11 72
    0x1602203040c0040c000b400c520b8541802501440d6080e02907600c61826145185e0740003030310a469440e590864646a20b010900b00c051000400c00071400c00345090107400103601c10420f5035596540411550151000c1e0341c0202c5461b0709011189a81b039070042035280b403100d00ea21341185c541c01581044480b0b8040d80d10050030251030801d0b80048254019170b0032601104a00e00c124041d1100c2c0081c40c070030320861241d08035006e4107000c103014518011070100e1010380500005030901c3e0711f070300000f0f06507405081120f000c03407200f450b80ca12044c0100040e000600f140c00041002505030f900103455038030700811403000c01c0800d800007050000e10307401c8030f03810314101e103000c2c0382d0740c0d03070145020f0b6030303035016000c1c50060410002122085813170002e280d0040c0c03210240070b8019514080c41e46010940501c5035000c855484803030100d403015145034034031146203c940005c0f441d400c040043c4411161881ca040e410804104d0310324440d014030b41d881020403031080c6070140c182d00304c600b4020307a50f02074942240e5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 182335494 1250 182334244 182334253
    0x414060708160b01150801081c180603050105030f060601050a1b0c09050a06050307030c0306020318010507030902040f05060904022709010e010b0a1a03060d080721030605060d05040201050705 84
    0x109200d40310a0160503a416415500b264580300c1788269606102403149800c9a4094488240184582c4000e00c18600142c1800d03400c040724801c1d140c80104854100d000001e80d0303000100001c0c42d0802040070900c0c8070300081c0c080c604105000a03d244100341d45a8103105400c0300c0e13202e620040780d45212800781c01c1018003810075214148680684801d950010545081920200b640d140100300d2508803070707012031204001e6203581d440340b019410040092000014828049050b024280100c5200d1084c903900080c0c0c0404610400c0120345c2407400351461240b5040401185e43c40f500c000341d400c00e804403071060030b860300c18015803100c441c514070301c500c6403d80d80140015110b05422030200c0c08070050007805034102640c140109103615100303428005020403000c5c40d01101100003903401c9900074004000044060703d070464035034410782003202c0a4090003029160100360140d00c03a46511f20745818070000345020000741e01400307807e24010445645001090844e070050b811201c6007a4031200342c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 182336744 1250 182335494 182335537
    0x1090501050103021f0203040306090203070509010f0f06050f0702010c2402090f0117040803040c0f0b0a080106051905030c071e050705040b061b10050a06080c04020414060708 77
    0x15029140c207120817800f41800702c1d440c1503c3c24070a01c0c80894140ea0364020750400340b564881c0c2d400350000d0326041e81c150040000100302925041c0d43c0300c0c080c00203488850003091606d529070f441c450540d0702580400070b0a110700c141c3c40001000301d0f00710070380901e000c062105003410200e0141e442c109180c24001c160f0707080c26141ca5181e4020302050101102d2590040e080394006581c1c680301c180d0a0002c00d91404009000620618051508980101e82140c00203865102816160600382c20083c001c20700454a00701003035000c02098050104c80c5840c5041a1a65031070103000700345000704409001010002424802d00c110985124075006141102142411034184451184801c010b03100c9019814000c512414140500ca00c10b0101408040c6070500c034007614401c1184985400c803843c0a803101d03141d100825401014010303003150b080000c0342490002c5c014500010010900d000d5801480204000e00140b0900c0440074407d5440a070f072800300d031400e01d4032803080d40342c102455250071100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 182337994 1250 182336744 182336753
    0x2190e01032405120a020a1a040503190b0a060b0405010f020f0313180902010c230604030302030601020120071e06020706060312030b090c160b0906040c060c03050901030b0d050109 79
    0x28000b11481a2a0800000344d0000440e48500d45030740081e42041d141107003046000500300c0f801d5000710b10454003600b481e86400000c3c0c100b800494516602e2801c1c04000360611038038511072600250301c48001c0107103a03d070007824541c0d401248a20b90603c0b1800308280e082c54005d101807200d801c00e00d003e49503184881031625040d1281401401030b080440b000ca40c542001d540b0a12940a4058407240540b160f646d80d00706c0d03d00140090410081603d50858100082c00c12a440c061032003034801607103070300c0c0806c0024215a500c00700980035440c414440d01c0481c50290803182d000d900041d0440030b504a48203003040550ba83e42d0000c0c445440058503406012660340203206a0340b01d0307207254454684500d422810b1b1001e0980044c0e02011a0002c103140303020701c50007004c8000d101074050250100c5922804621201100c1615041d00f181040004202c8800c950703d016000d28203201481c0380c0d480e10002e04034042c400c1c2c40703814903645880e801c0141d0b0b500014218620303440f0307000780300c002d040780751 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 182339244 1250 182337994 182338061
    0x10e0126010e01090c021204091d03160b160e060901020a080a02070305010b040b0f0108041718090a021603141e0a08090712110406030807050303011802190e0103 71
    0x3821040300c3c41c18a01715000c5d84007195000603051a07045a41c01e050400c42544020103842a04040d020b5840c402d002100c85c081c0003a00c504103200c1e040707110411b05402c0074003c09600500324420000d128180704541038104001d8100030200f0ba0700141c4445002c00140e00c0c200300601c000d00006000700382840c20907030001d90b00303003500e02c00e01c002d0102607a6441844107072040751560300d500c4480c0320b10382c005551040c04081c2d07000340120ba50300b900480c4112815031590224120a84100c0000044e115500303041c080c03950050045c903421854038000b001c0040c0c41440c80140101000b10a070010f800401c0d506041d0f0b036182c0c90401400c2020b40210f01e10013065440500c024021800940001d07142490200315881141d20f09841d40c903138922a95500070202191080c42d41d8031503510350000c0045a848000303030082174400d200a66a03541084031101c0c0841000301d4a0700380b54010041004000d850191005681c00f80341007c2d0307810b0106100517009010070750102092b040c01c01d03012100c0040c0a08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 182340494 1250 182339244 182339249
    0x705030c071e05010306060c0b1e2d0601050412082505010e0c1011010603080c0105040302100605030c01030504021c030f09060207081b010504030807030c0c090209010e0126010e01 79
    0x740504040e0f03aa44019000e4844900c1082d0100e402200e4035400700e881c6840003130b03100103d0080ea5880281070708408407000000d6500001700c8078000113004507440d08209130212006074015402a625003400000c0c0b031881a4000d85441c10100200c12042200341e909903400e041650710300c0003802c0c01307905154103c0c4060381c0065a032907081c140c00c020342502c0418048246d4802400c0c03a8400075190703e050f58081341a03401401659a209000400702c3c100c0310161012200040001c43c181c1000d0070002e1500c42e82d19004941c4a00d0b02100300010354000408076240f010a080c0820f65581c2c1b03000141201c40c074444002500200030b10007100b090790007101d401c65644503468400f00ca984500c0704036a0380b58603020350243c50344451610501088900c0c00310b00d003554145016441c0a407243c0d95001d82c0d8000c20070450100d5a248903050030004044144006400d0b0844210f091180780cad8002007100034002c400505104100004080005081003103003000c00302e45d4011072480d40e403490546136882c001d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 182341744 1250 182340494 182340539
    0xf0318030f0d0b0a15020c120f0609032107021b0f060c01051611030909061909141324150803030402030d02010603200a0f0603020309070503070503030f0705030c07 72
    0x82c000440c17412203903090880c0c0741341d4950092002d0458581030080100da61001c25100f40b18007a003032680b080040006520400038100595100c00b03c0e980d0744400c140ca0740c40041c0c1c1c40321640003081f1303d49034002820458001c2480e40300e1058030021010480c00110740c90300c0741d003140c400508030340072110540200e402590411401d2500400b40f510481d0740c100316440606003500f08011602032450a2101c03030782c220100400c1d54240300044400c1002d246000d90000c9034030754669220030622050780030101e5000d0202d0031251035100032036980407110540705043c641c8a500d50035001d80c002d04035502c4078464240c140d804000440c4c03580619603407070304111000c0384248a1190112509031042c060303a400c076640102d15002c04a6000c0203082414804c02119801402c4100700080c8402e8048803030006107401d03100140e49040648a40d0304045c495006507000b9070000320108040d480000445812556400500792503000300d1070014158070070302424480505c602c0c0c00101e13940c1c55078107030f840b203950700d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 182342994 1250 182341744 182341759
    0x3060c0801052704050106050414010305010b0603160503090f03180405220f0516032a180c02010e2e0c020c061803010507080117030f0318030f0d0b 65
    0x80c2c0c02004002c1c40901401194103000d48072010041d5440e403180381d081489070f0000f00f0134540352030200d011601c0c0c4202d2840060300e50001001440420f115168180710151a03003441c40c500b000c5110725101300c00f03000500300800000010400c110038061000090754050582e0307681c50302045800d601100082210f40309510701408951450321070381d000c003110a014400000d40c0b28050300c407201c044d41d00285c2552240a545440c50003103501c1c0d100e074409075110f0000d103214445044960761640d618010202c224040701c00d8144810214451040004070b071180020456102e00e10049014166103e1986143e200c0d59031103c000301001c1c00f02400120020520403490b02180107400203840d0408402809600080b40080c4c40741090002401c2880602400a00000040e00802e085800031203503100000c1c154001403103004a444800301c08254064015820f2503074281c081e030401e120250080c00d4244e40b08000c0c04500801380b068989005100300c1c66034030fa40c4403082c0a80070b005100d44040c846d210 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 182344244 1250 182342994 182342999
    0x315010e0d051f020403051005041b1e08030304050a0210050c03030906061c0b0c090d021309060c03291215061306440a11010801060807030c03060e0103060c0801 71
    0x3c0740c800e41c0c003220380085c02002c103919600f42c01c0005060251045d21415001c0a1000c004081141c08200031b0001c090141c4070154804005076505000c4d03005103074642c0040052001041000444c0340364030350111540d03000c440c030a0000755103500c120242c0d00e00c140004020824180030115140d8441c00040d41e5a50410316038400e00540b20421a0000703200b90940c17800f24036020046005081181c5001c4d02c0706144a119800007000d60000c0b0486001c031640b588200001c101843c0a441d0b03000090307003802d10460301061285056400403090440059622081c080c9981e503074020a0b140c1c800c040020b031030144444c902e1011891504458490082e4100030001e40919024070414040752040c002c083c4550150440c0c0368402109040c0c1800c00402101919101e40da00030a5010410009001031001d600315262194518404600c190306204064004000032a040458140d0242003071600203007001584006400411580d003000c8a42d2804d080048100421a40888034404142c0c650070a103a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 182345494 1250 182344244 182344303
    0xb070c020303030408030a06090603210e030706080a02070b1f0501020a0b0106050a09090f02091503100608040f0c060509130c052709130c0603020406050315010e0d05 73
    0x202810002505035104100140c0031894400c003031500891001d40108156035500304503415190a0b810907110030101403800c0c0e00c541e94400d80ca041b07030b0803241072568a02d0103c0300000d41f0350f1118417840341808203450004c0e03d4481242e04440c4000d5202c81d1161850030710b18003000c1e00364400c80c990501d440520070049000d60000890000080c2d01c1503640c0b00741c1c0e00b0000c04a0712500701041d500c090140c04a00030501d00d40a0107130710405902000c0c0141c50704180f200f000760024101a05104960040003804001585600c2c43c0050300c1042c1448200c2362240c0c45e1a06804841c040081c003031685994020910b603034041c00070450300404803681100450200480003c071443c621550022031402c0200a00c401d0b003c00c40400c00c1001303444045204c03048600485c0810704121201030307000c4180540c038001c00c51a26244030281c195850111705090074900d018289100c0034000c02c7e00744600202c004003e80c8225050190b13085c0c00b81410100c1500fa1a0042d0fa90448003240400941201103032211302 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 182346744 1250 182345494 182345507
    0x1060902040803131e090b0d0f05010e010605060903070308090a030b01030308070f05210703110d0509010e0303010e06150c03121909080d020a020309031c17040f060b030f0f03070b07 80
    0x41c84400e0214103280c41d18600301b005000300d6074110307000701640c0c00590125110681c800e0f84c0c0c80c015000030800c0006c00c00341c1c0d8211042604182e00c10b010502200030a41c80003c0c0d10019070b54001923256403020407600180c458002c0303a00c000c26240c1240000700c00c0541c800d02c003070301402c1c0d00d0b1906c4262074080001031314240260320640c0031100c1d50001c402003590307030a07070261380101c01030030b0006d802001404500c00e5070b4081c40d0100e20b52900e0385d0901030584002d206003240201000040c5007107504080c4900d41c8900060515841141c25000c3c500c003001a50080b00c3c2c0360803c6804603a518218500151245903085070f40790540c24060041144050300780c0510042c042e400881c845c600501401480000d401c4154440110b01c014040050075403020041c0840e615034525003001c40180c0079000030000c00341d1a2014803a02c552034144070009480610380b0780d610b64042c0020481144540101e86000020b00c0c001e1800d20402500311509103000c00100038050282d00005103980d50740e01c040d20744 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 182347994 1250 182346744 182346779
    0x3100b04060b03040b13080912060907090608030307140906160309090507020a03081e040c1a04050a0302060a02162705041110020c0d030306061b080d0e0106090204080313 75
    0x24100000010b9400403a070725600e80b20707907c50100c20742800144e00118512a160300102c0c05141d0100060106e1191304201103401012200801d02100d801c00c0c030003d840c0d000140801090113403101c0422041d14028041e9030042a003e45141d4403480504040181711007d981c054020802c8454017150803002d034095640b00c0d8869400510040041e40d8044440d00c500602d011400203000500b10089280b07014014000c2d07000c0c038844409a41001c48444100c02d010420f10b0f1f440714100010003064807069141c40484e031f0121145900c031103505105a08091100380c01d4841d00200c2030001c03600f84864441820800490003c62070014000381152088540c00d40e406404404c100000712800d02d040745422900115502c1519813506d0001c000c1500c040c804c10049001c00e03220502841910b030f000140180b0301c81091200030710000a03032541c2401c0e225040c017800c3c809458a40d05040500d00350005e200a0030044000c40d0303216075848000d52a40c03c44400030300100542400094501c25107018050b5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 182349244 1250 182347994 182348003
    0xc0402030c07030c081e0a0f11070b21010902040812040f050603091c021606021f05130503030703021b0d140c010e100615090f0e06010314040b1f06080103080a0e03100b04060b0304 79
    0xad142e820850103040e141c010403500f241400945104840c06820b010407640204501d0401603101c138100340342c00d4103214204454800c010000d000801c40a0903032200d44084900541d00341d035030b81d00c0d14001c49080c03085888100240281240c0d850041c00d5001030010000402200c0020341c83d41c40704000ca8603030036030103503501c0090104900c0382001440ca501041e0000c0304400d2a80045106a9510781940c00c22644000840d0707022400e0012800d002480c0308440d040070700606940c041400000e00780704035008050660311004039070b00060a01c01d50007032618410341c0c82140c02e00081541e802e0017508003070081d0f09400084141c070f031250724060248501910500b080302005103040200110f02c01d00001c28a41c101511422840d4401100d008074034091401420300c201341b03141400c420f9100d00c85010b001c8444000c01c6404000c01035000754102d05403036000054507550490b40804a07402d20000b81d005905006850000a200d02c1c0340d444081e5541d0151801e110386a036030101100300b400115406407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 182350494 1250 182349244 182349253
    0x1217060a0f0e07090317070303142701020c07030c1503020306030a0f020105040e0708041205030112060518070f061b030e01051c051005030c0402030c07030c081e0a0f11 74
    0x100c40050000359590080740d51600e185813580d240c440703150f400c45901e00c1c40f102000c001175203410316a0501403140380c0380000d040000e480c202511100d1195052b800c41c4c00300b1134080c2c1e50000c400b0b04c00790112034143c101c8108851640d52282000c4490710715078800c0c1151502070700b442c400b00c24001d0007a40d101d400000c01403c40200716445050001c014a181241040002c00012407040c100b00c6169008040e01e5030790200c24500742c900240741a880c1032004003400070520042003c50b0b4290800e08883e58403a601007400d884041d4110b845407a1460000d40c0d44c0680e01e0045510f9800b500d448c0100c40081d560780000c803480c45200c0f004019800c1000d03001925980c03026060354001d2000f0a140d000300418084104101414201100d000350f03840d01083c580725104022602d001c11106112032000c50f011840c0d401d010608410700e01c030341c0c54003c0900810301030340d205200d040415940001e40d048003c00d03507500f200340005140c0e884582c2c00f0340440d04142010700d003548129002100781e85840003d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 182351744 1250 182350494 182350499
    0x1206010b0a171e07090f230d0b011a0706020f091c03020706081e07120c03020f03060d080d020715140f04031107030203070e0108010b0114040608060d1217060a0f 71
    0x6114030080040045c007031200c01c00902c4a00220512008104140500911001d5100d0041384102502d04c0d4a1003641c3c0b0445200c04500600c43c0141110380c001c1d004a8a50351703810303002c44140101c80380034011a10114507071030305001e03000c002d2000c04800c42d4080402440b0140144842c0c0a000300a0b00587c424241444041d0007565000c1d0031040c890b06102a45070b40c8120f40000200854200300090340f5520380d41c400b80c01ca0301581401103001d0070103504010044d42c110301c0c10b0000608103442050714040030418820040100c9002c421003803070555031206141400b40b00c54110700006280b951070300700d5200482404502150207405075002e0746115469644044a140460600c494520300642c02d0000069a04004040c01445401c000d040f003036161400c2c45003110750b00344c00c503410722140c000e040a01c2c1d46154116400d03103400b4105010139031618008286c05040760400141210100701ca20001650040910b50b03000002c80711642e007641c0c03000c007030041040031480340e07904554050006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 182352994 1250 182351744 182351791
    0x8100303050307030506010e040911030727021809040c0e070801030f0201030b0f19030c0603060303020304090f11160c080d0207031e0203030403140c0105071a04021206010b0a17 78
    0x1054006e40c0500d81240314040150010301100c40701071084a0001110f60452040d040601c9a0802000b00821580c6980f51900e9801d40b81a002c07615a68a20390000d0042900e40074003904501d81c41002d05059054a00fa203000061060f06d4014000c00c0500c0000284a0034803662030281030b00d074030141820701e00049a00560245c01201409540118450242215030700d031402c04c008004139440161b01c030f4502d1810502c00303005540c1c00400c01c1600701a000d2021035000001c0714211605040002500c4000c880b80344024003c180390015400700005080742d000c0f0822070020452801486580011669243c2060f40d450041150701c000d13030418501000811480f0790a00f842480c0e0b5a964044180d80e54000390656016401c1100c0c0e07503e0b903807108102101c04000c1c0c02e090071000c0c01c01d5840c045031a11004940d060b0a41c4201c400218500003e003191502100c0c003074015601e070101d80065840c2c2c1c042c01141d4000522000000e14610300704190080214060b0f030207440340381a503010320003001d201d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 182354244 1250 182352994 182353001
    0x20f1203070e13090501020c010f0f1515030b0301110d050601020606091302010c080a0201151203080c1c0603141002070807021017090703020a0b1305041e020301080606010810030305030703 83
    0x40c880e40c440d545110791340100d0005c0c001030000070300a07000000c0182007204541c0807500d690000000c01c07032a1034101d500c00e5100b41003003c15101008031881030703101d01d0f50b021000740c5880c6900a40550030f2070b0a2403003046401d00039081e003a100901c1802103541c5c10004903078810017222510b601c03000440202e94034a85c003001505132140185410100b03000d041d03c440703400364800d1031a00c0060303640307030840ba5840b01703101d1020000c2e201d1004041e4100403035072001410321402500044100d0400a0b01500360a41c80350b40045150b042032060150654a080030032145000e090356084900030444640300c100c200703100301c82805134050f1440341011081e80a000588421540103800d0146023121105815001c0b29103922940c4540300503c070360703800e5105102c4104c00b01d031b01480059800380110100a882c2200d02030540b50151b80010303030074003505054100b82c14164400d540d00c034070010002c5102500450300342d01c01ca20a817224250f9445681c00d0441641083c400075000034000e0011461141c031980 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 182355494 1250 182354244 182354269
    0x60c0a0207031a010503010507020712030f090510021509030705100203063d0503160305070224010510020d050a0e040917070b0a02032202040f0c020f1203070e 70
    0x411602001d841e42d42c2c84150b032078001030070401c03c000c0b00d0040000385824042c0c11f50141e241d02c06840c01900e043d17a03d0741c1207a00c40d8001001d2020848103a00c13041d224241c0c4600500c0018904109841d00503000784d00c03484c24110102c2c4002c0000c0010700804000421a540550b1210007040c0c1400e84440d4400250000340c01d8940c4071100d18580d52042d2003001060210400034050101440b04818095124080a601c40028054140b00304000340300c1162080c2d1000c400f905010500d44c0e2090b1089040514080301401c101b00540a0314012001d1218000d05840058586805060f0045000d0ba81d07111004000d2000540400c04803655620031030a0504058018101098800041c4e4408144c14115054102420008294141417001090015801000880c1e04603d54100040303030981c4480c3e0300c031414022901c1c0750303030850440d11560301807d00400700c3e0008100110303407004001e4841140c0c210320b00051046201c644041584401243c0c020752040d2503541c1c85040304400e010f0400c2041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 182356744 1250 182355494 182355497
    0x501290714010507020d12060f0b0903010605100f0809030c0a1202030d0618050a0b0a211208010510021c082a03071b020f01050c0316050a0c090c02060c0a 68
    0xc000580207503024011640154156000703400215072183c40102001104150305111034100719080041010445124059452881c02c8550741d050480110340903107855400310303401003001d10444041e80d0f4868201c402561231a66441d1840c1c4903001d109503640140100044103801000e0300000240c2000c00342c20b0030308210300540e410030100e141d2040480300154440d447c0c054010f418043c204116200c0c0d141d04c00d885040401120894602040d000103850042113244003071000c00141129180c600c0f48081903100d4fc418000700007015005102140a00c1424050368110792003030f108500105000f41601d1002a5448102c1110502121200c3d8003a101c00100d103100d00c10500804103a50b01c11500c5003540104139543d040c444802040c01d9a440c0300320044030403200e110001640e440d50518160b0070700f440c1480e00c59203c1d00d0300c94114490f8000300510f070640c00081c00204072002c2210107850b4003800e03100e80c095031348206240071f0300c00145804005811260028005415400281007a52640d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 182357994 1250 182356744 182356763
    0x110a05030a030207030905011110180803040c0e13080915120403090e09030a120c090807030b091203090d2717012d0b0f0406170105012907 61
    0x15112542103611600c0340c480001d4000607040241600089400000c2c442072030542602e48002c044592520941411111416110f01400c20445021614081c00d1900011180ea680c1003030310b0300004181c030030320502c182d80c110480010201d445a910101d80160008806890040d0030700403c40034142c81000520740c2001405041e026409864081c1e10803842034491404503070502100ea544448010105100c5500400c480300e02c0a43c0880f07100003800d40b07600b0101f0907201010040d0743c4c42c003094008071000e1064100000902c1080d00c009401115007074207a03291034100c410340d944188001c40d070304e800c25071042951020243c4a110f00c04544a0082103400340e000248449440c01c03c0326500c0904a14030580e0001d046070401c0c0b061084140c10741c0d101d0740f0180c1050449072110426600e02d040c0d0140c0d5a11125100c5d11a0035001d542d06a009004210103601d520b511250001c512116840b5503103060000f0a40399140c88081704124409400d00100c80322001c42c582c56644070301c0044405005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 182359244 1250 182357994 182358013
    0x9210c060504063c0b0303040305010c02060a11040b0301050603040204110301140a0b1305060315031f15060203030105060d0207051203061801060e060702030313141206061011 77
    0x440c801c1d107019501c1803001140151494154440d0f100400c10090b10f01c070310482500c0f848410100001e81804040d510100c0c0038101070000a0945c0116803018003075500304480300002607404209944580e0b06402d0410801521580c2d440842c020350240324840e03070342003005000030f1403c04040d40e80584014804901c6682200c82d03001030f908280d1191000702d2800c00038028a103084140c3c8805410703401c0540d400d25400001c0c0700c11100c0302d4812a0b000f00d44c0040030600d040c00e26214000000805011114511072080802c411004d1a50400150360b190040c020b422010b581900f000b01e503060344c015400c5074205000c01903141d01c5080040350090340ac01840c00000ea00784526003124111001050f10f9150260a000381004076095010418a02d072006010b01034014910080f500390035a51309440d2030003032022a00e18071a4034056405013181c00c500040400c10010f0b80000090141c802d0700e00310440c110b480d6954802a81ca040d44010300078a582c40d02d911070f0107210000a5030108403520581c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182360494 1250 182359244 182359253
    0x5030d030b0f0d0804090b061201030b1e01060e01080114011e09080a06050106021221070c05011b0210230405070f060e0a231302041a07050606030109210c 68
    0x4282c03c00480300144081000c000d128080c0c0704012028070190340f610302d1300040700c40c040d0341c1041c140001012084404042021007034a921507440c1c50389404920962942c441d80090504140c80c0203140c00900c056001081640316244846c0c10f20350181c60b8040005020101d00111182c172030074132010048440000603c800c000c01c055410740e805080d000a0950508030700908041009620500c69001002504200c0b449452800504001116200740c1d42d101c01da012200520110006086582011680024403549a88400b0421455000c403582052000060f000392060107101c0991480c00007215147d030f012031880c141c0e10a128000356007441d80c4406000c000380c2c0d0300b038000600103407011000d42502d04010401c2c80160a028002d4181c000c0b90140c01035030040d0500e203881c00359068108038075000300c540d016180600842a51003203102040b042d04011500180002d490b030344074400100e49981810300c240310000350041d2442510102d0002d01c0e04851301d08486001c10004010200004103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182361744 1250 182360494 182360509
    0x70f020c03010f050a05060d080f0703180e18061909060603020306130614040206030c09010c05060903120c0a0516050c0a090f0f110d0c030b06040609150201020405030d030b0f 77
    0x3036811034400104c030b0400041040850784000c040c68044d808041a20020070309000a603495404143d01d425519010341c0380440320246c034640c0d281440803280d00c000c81c20001200c2c0040c81861601c16080484101d44205a5150030981d40d580305460100303801940c0030700a80004c0d20440c000c54001c074095990307502092401c01c044803040602c0500181910400420340503d00b001001c0c0c0c01000c3d414201a00042c0c1d49201c080c0007248007210001d404542a402000c1d1602d84ca608001900d4003458450001c036201c0d4807030111807054042d81c0380007035801c404440a031031140b400b6a994030308200d8818941c602d8410209415a81e9211300c400120055030340d40280c80203005045000302c2d9a15a00c181a02524541c0c55561403040c00d04030204513100304d960580b142880c04050101e11100386500a23401450380214a503009140082c001c1611600040080c0071110200b001d141d070901c009800b00d08030b000d28001d45034036403c8149070040039842030300482d40c903502c0144584ca01e10f42c40310006403903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182362994 1250 182361744 182361761
    0x31204061806090b03150d020a080120040806060f01212c0d12090501060e060a0f06080112030306050613050a080a0201080c071a0f01081b0306070f020c0301 69
    0x101c244014910191800d80600018411800c0180300b207414501142c2e01804000c0015080c0c61035003020070800d9982c0c004203001d4540103843c80566a4880003010b010702041e0600c3e6130440440300704e0f181850580021141100e001c079001d0180e645902040006150706000b1650404c013030043c4c0d403413244541d080490f241b041d5101000583c0401c0214440c04409100d03e000901201c5154091043c4000b0071380c0710f1440c100b4070b800b90069070000091030081c400303454081c045629103000800c6400c0c0e588003090050100b1036a44980320783c0c950702c50074000c0150159000042c52400100b140703c01002c0d4400e081c91190801040700c684490210f40320b0b4001001c0c200107150302c1c4908000506011406001418803a03018200d0304100b500040c048003809014900403d00c001100b07418080714144d56991030347c0c10f600005c85070801c0300c080100e81d83c1c28080c490681c094100510200e08ad000708051904401801500603666802c401f0384100d540483c554081d4082c1001507080c1d580c0c2071051409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182364244 1250 182362994 182362997
    0xe3103030507180905040503220e06090103050d0c03050c0a0305092803110103021e070b01150509060f19050408010b0d03140a091e03050105090c03030417071e0608090d0f030b03120406 81
    0x41a1900e82402c4ac1c000f40600014000c0414000500c04580c0105803141d602020342071011400b403ca240480302840741d070f00a65041d0180488030810160b21400800c04481d084401c60900c04401c2a480712080e00000b403960300c440b9100c400c00029003800681c42000205040050403d499a0003015602408000101444000003110300800002804072030150101907186503031040000700152151107039140003445218042581100e15441c101210054000142c0d20a0624030002c0c002d03046030003034010301c02c4a50800f00c140207a03040c466904003e4613056950309511035440c0360300880fa41c3c04040b4041c10040480d0000c11070014413402c0140700d2881c1c45c035046074a813940c1086809c5a001030042341070340e000544440d0310750341c0000540c2c054034607001340b840c0c404489107407080c9080e2a40e03210501d11614940c250800b107010013010303801c5074416100c4120700d656107120140c45100800500303000c0307141300300d8401615200c0d03800b80d0f00201000e411502ca148010f00c141d4207907082988060b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182365494 1250 182364244 182364307
    0x1208120f0a0c020a0b06010c0c08010e01060611030c03030601030b03150c1306031b08180118032a080309030c0a080406020c0105130e3103030507180905040503 70
    0x1800c10040e10800b008501244090010343c3c010341e0707640d01c40e070a015013440d0421100380d6020040c0400d918248004100e0000200b024040180c200c0d4003038211031080c10003003032000d880f40c07142140100c112080341c2c9144004e14a181d0300c20006400400d0801c142d07136010304c00c1c60540414079400c00940b5000309807034800e2036181c6203c00034660403107005800040800d410442d042c000343c03502d110803030102500341c1407262150f605c0004414107600c0e104c400040320b6007042c5081ca80c00a20a44803000c1b10f009a032070b000c1048440785c4051b000945192030040000c0705200b1103020810820146070803c2500040c4d9161603044103031036240402c07c0d0002e88000340d0004040003215010000500c0007142800c05505081100a000e040510765105482d02c400f029000600e82c1c0076003401148550740f2440e00a03220156680800444502040d811008645010040351b4030b41c0c000c01503810001c0030140c0d00c0c80c0d001d0400f04044041c201c098800c507824070040c01003006080f0722081c81c06e610a4440b0202 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182366744 1250 182365494 182365501
    0x30504170304052a030a020913050a0827100e060408011104050f0405091b040902130203100f0f050d020d061404120804020913030c060c11070f0509011208120f 70
    0x1141c20041c141d40685249401c1300c0f8400207500d011130381868158045800724055641c3d1845459010182003005140740944c3e010318003041282c0e00500183c1c0c0300d800c582c4c0030b0781014001c00c0c81805034248403503512111542d203003c1c2c1944514403109841d90040c244a040c140c1e0340f01c1c540e00351040d0130041010150040f8050041d07007020401461244400c0310f0611441c200902d00b42d4989041414029800c54003010110f256200e9030005040c1c0b03075004d040040003c01c00c02c8004000d40060390040030a903032245000407914441800401a01c400c0c80b5071341c02c40c52400302000081080030310201e802103480034a110214031a4412448100b00356081080f6518080c90449010450402e95100380200001400b001d80c4a0740181030348a008050410f01c0003140303080c140c3e0046802200100281c0c1005001c420182d0f12040768000c81110308110f0f4445030f2116040320418500c0e010300c60704010340500410110300142d00c0014064060701034145001e0100456841aa40880e20850b80c6411401403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182367994 1250 182366744 182366773
    0x8040f0603110f0f03100b1204020907090b0a030c02100c05121012020909010b030f03180603040f06053c0a09050a11121014060102030a090603050417030405 69
    0x10000e0660084070b1003450103d4020308002d06008840355007440490100c0010280303c18402c030200501440d000598413030720b11a042d0314206900f1102280030b4150b4201098080b03000351203441c00e4034068039010342030840c24801140180101b440360000c500c9408070801e07503ca851711640490074502c1d40c9440d541d0640c41c02c201069403001d0151856101c03905420051200f50391020b111465044900c401d06495040304a070141900704400c80d810300a80e8800d502001002005040710203003942c501d07542e1648601080b1403030004a8000d4400340d82c1c44021400035070f00d640310590141e40400040e074068502e4003022030501111401f00c0040b160f1440742499039910ba09450792159054070103100c0583d4682c2c440c0d494944e1300354000d02c000c42607000f0b041941d84003402d846000642d282183c20002c1c06c401c200c4050300c40b004094901c4100030000ca03686500c0032003158000182500c1c0c0d504540d280c440100c0003030100a10076100503441210702003104181000a5004030b009000030034011484088 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182369244 1250 182367994 182368001
    0xa080309120303011802070303091b080705120c1003090c120b01090216030e01050f0d0203041a04022d060705030901020601080708070303270b19170f090a08040f0603 73
    0x2000282503100f8001040307a000340f4110b54802c0c1c6503584002d6200c0b001850281e000c0c0c1105040280b0b0b00b45002c00d006020210345001904851000c011101c2c11588c0f202800b0194204400102c1140c1201399504c010342000c404c2125550901e00e000215034420352110300d0380c5841c42c1c020039005580302081c02e0600c074000ba6042d001d000d0604046241c0401c07290350b8031140c205004010107203c01c40002e0001a03004100755110410207400c2c1544c0c94900415210080d4000c40d4101c3d484442e4203404800b00e0301c08a403691142e40d01400c1104105200001c060545005403d4a405a9801d0000703841c1030f25800003a10502d4410401551104c030800006800c0180503009440680d00040e420000508006000c00c112605400e1810820340f09100801a414400403020661990040000707810500d80c0010300c18000b00710300910990055a000300c030030200031240100304002c000041020032201b8050b00380c0103c13600d41121407200050b6603200c103c1d003050b4041640a2288141000441e82501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182370494 1250 182369244 182369269
    0x131203020d080a0c0f08190219020105090111072d11010e0315071805030a0f1205030903030a05090c090702011508120a0c14030309010f111305040f02090a080309 71
    0x20400d0000491314032000704428201c81142c0200280303840410010030040422000280b461f44096560300009420700c2c07503610198002000561170b150000f4200d810611880c540b020010000a1034518075413a5489560151050642d46540131580e85034141507100e03032882154840e035899501c010118001408c14410400c0d054041c0c0c001402c0c03c1c4805801429840d80f100180c1090103118602040d40d00321400d01c5c1e04459010301c40c15010409100550102c41903051180c41100220748107005c0071100d500050b41c0002c0d070756200b40040380400322036401c010381c07141801086400c0303c0302217400600ca108041e41d100c00540d41d80ca904401b12168010340c031014041001c000c214508820b141c6c500700c5d1003407042900401500104903001c000d03900d01210302c10781c0380300700f04c82c0c681c2080202c003802005030b0b03007101c0101864072200c800380f80d600c501920f01c100c415a1120550525000506c000350003010400c148140d800c11400c000c581e42d2035070010140402e080255200c000040c180810010b191 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182371744 1250 182370494 182370511
    0x908010c0c12080f0c1e03041a071b02060a030b06031e06010c0f120207050a171902030a02010f201513021c0c032a05010f020a08131203020d08 63
    0x10010000600b40300b02d40300c1e420010143d07120b586c0703030b0110065050b4200c0c6200d580810705c40c000144024854043d0f1003920407624000102c466441d10710702500c202129120304c10040006602041c05031600d07102030960509a4100810001d400400040050317000700d6502e0311201611803031410070041c2c841860b6006100b82882d083d04030f00da4491612043c000d030303001040380c41c140d041e10000c01e10911080004040c0900201303a15a11255007095011342c28038501420321460b4101c49001998000c460181038025018180d00045a00110f40c1c4106c0940464103201d034064904c3d104900301101150400d81400161110000c0c140500e0f6410002501d41084594a03e010300050b945103a1203916011619490140100030340c03401c549c004100d5480981108000c04c103801d03040324050303501c0052468011981c0040354551006440038884518200c0060340181481400100980000d0a030880050400c408590b590200d1802107014580101c00503000f8005940c941c41d00b088199800c407841 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182372994 1250 182371744 182371757
    0xb13090b06120606070605040302032d040608100312050a1808031c090204051302090610050307030e0f10021e0c0c010309060216050303100e0609010302010e010908010c0c12 76
    0x40500040150081c40b00c2200c410302c0c1140072480a0351854122100c0d41c1c1d005c0d07424421445c250601940300e8001c0d01000006041400b88450344811403100d03400d000d0700c000781140c2000e0814004507100300d0024544080382c0c1d0754800100109522040c00305404902e41d4036903a0341d14840000514890240702c0c5403007490780705e110521071200044281c808142111043c8a04240a811090007404403244042c5d042481d01c401e0000720112002c3c2c8642050081d150700e07080d5180c040c1071007001c17091a0034010001d4400d00110f1310f0a0301c00c0e007080c403001e85c0034800c8960110328001c1c1241030030030918403056031660005461048542610725082090f851468050030205080052511441c1c01c900250406513209000320401c0490360580c0e00c0070707405846824640506140c603940da98001d541e01c2100a08401c40050340c41220102d8a101e40381c01707004045541d295600660b003010b0000411414084810004640c141007440381514022140c2d48030401c010150601038462516074020f034040040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182374100 1106 182372994 182373011
    0x2e09020d06140703051302030703020f061c0c020c010c030801030816060f09050f0109170c0f031c0b0105070b2404090605090106080a0308010b031902040b1309 70
    0x8075484c200700503262418408150240301c0002075142e80301c80030901c014248115440c0703082101400160502120351140079180607401d070b4284c8031613510035122400799410811070b1420102802c01d11540c2c003070358a00500f203100500002e007500e80c0019411181d909507d0b16600c038250401d42c2000b0b042c103a503401d103029201c074503070a86c0d4620600a1031100c02d4810300c65078980d90340c0070150200402250036200303010b401c100403a8046014803442d6190107202400200b202c600c101c11004d502e000141c03480c42c115071402540030304000f414846e000005140130b0742c0f59080060100c200e55000a149040c124081d040220950411705180d0340800704072042c1c001c80d010b081e00c440203020307454644008035a80c03a00c1110240010304030600422041084900440e0402205c05460030040910b0210000f81c1e0b000c6d5109400820001035010000c41e0004014030240c0090001440b00c0720 = true := by decide +kernel

theorem cover : BRFrame.Cov 182194244 182374100 := by
  have h0 := BRFrame.cov_init 182194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182194244 ≤ n) (h2 : n < 182374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
