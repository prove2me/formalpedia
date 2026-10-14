-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:18:41.093855+00:00
-- url     : https://prove2.me/submissions/d2ae78c3-162a-45bd-9e8d-d9ff8b9a59ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96043165 ≤ n < 96223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96044415 1250 96043165 96043187
    0x50907140f2107020618070b03060f0a050a06020606040f0b010c03080907120503090a06110303150102100c03050a1d030703030e0a050d080f0f06010c03080406091e051b0a15 76
    0x24000c421540b030060300c005e450301000d07100c130f04540f82c590050500c41003000413080c096030000d95032107245841d20001c00c0311640100ca041c682010041e400059243c0c0e0300c408101c0203020325006885149001400c0108691540090b205518500281010140d13404400400300d66410301304078030b40d42c0b41c0c00c40e180d00d42100c5504c40f1214000c2480c9440402001101500c0641d1060303910300001c42c1c440304140c803030170306030795008103550b1040c80040d05014100484428810044c01070b201d48000088441003a0703644250300c407022a44510501014040c00c3c1300e845499046411039804c18413508204d80c0c4c81e07120b1810007404054a500300c020901400380b101c4800c0c19401412515500b0b4002c801800200c411610044c5200c2d02000148501702e080e50784a110320b10507901e42464105681e07055480c4100035100780c440d607079203401e0840010b121551105002c1e0807801101c0c603075a92441c100340791080944464080e0308021030280c02541b10141c004080e140300b080000700c0a480c40c001203510003404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96045665 1250 96044415 96044467
    0x31e0513020402210f071704030306030c0e070e030f060601120b030d0c120c03051905120a061a040e0a02030603030c0303040303021201050916031a03070e01050907140f 74
    0x4d8407543d103003400c0041c50031038102040042c8003951800c02c0b0031610442211000e011510803880c0304c030082101c00c0ca0f903500c02d110f810006182600c80e2200d00480700a500002d503c1d0b03a03400309000001707405c054000201c5204400820755104515511500e031a03004d04401e05010b000301d42c8081a8031107030009000c00700013070111010031040500040c04c034a403041d0180d8001c1003104041e61503500c42d0714402502e13901510f400346001440484201c1c40b4001542c1101008403c4c0406410a500784409502400c0011404a40c0504003402d0018100c0e82030300c40c04c4c1c1c0c000f00304410016200020742099100c1c09900d00181c2381c0d80c400b004a410740c8180401d820517408000100000c054042c1d01401d42c18080c802004956a2200b0911607400019902000030b0300b80c1d00301c00600301d4401e4001030201004025103108016580d0040781c0b4041c0300c1d8025210207229100107125606240d04000e60003045071800145070912455180b03401c0c40795003c20140b4003030024149107484040d410380d8514000c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96046915 1250 96045665 96045667
    0x9020904061a060301080604020603040606170a06241a040b1210140f04050429011a0304120e010e060408010e1b01020c12071e08070501031e0513020402 67
    0x1080c54080c0052550841d03000704202d02294010240c2812400c0d030703040c0e40001d401407400344c540e0303000c000c0300340c0000b0300481c2c010b5103a41c40420a541103190055100c4050750080c0010f41031890100241c0c2c011042c1c1c00002590801d8001c8103c021401000480c2c0b5901c0c0d856810745c0841030846641d00c2240c0100e03451003c0002c5c20f134003030b59102c2c1d80340d40305075980303100110040d458136802510306801151440e40054000b50341e1100b0f182c5a4009900244600350080c0384100450951a400c03a0710f1405910060031000104121490381000c140c0e141642d503600741c9540307480e0f038540681d00d04a0b581d840c00c1004001143e2003030b0f4015011045844001801e498490f07075030f0f13100c45001c0c0685488460700d90160b040c3c81c00c04001d6102c3c01495540058020b000a1401c2100b841f00801c01034034010050b106503800002c1c2410761007100030325520704003031100a80d41440400740c40c00400368882c070f04040ca0031402940c41c80e4080740d14560304910320f5020400340ca0b0304496055840700780c000603601c248 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96048165 1250 96046915 96046921
    0xc0f0b030103050c030106060503041e060c1110180f0510050406091b03030e040b1305090114070908030f09120f10060f050d0210110102041e08030310060503070201090209 75
    0x114001a6040324070071811180e803640e0800071705007070307851a205004c00b146007840401c0014210030703040066072a250041d40980c01450b1150001d0350440020700c1d021a0603084400d00a06090091240d61511040c0520680314115211041500c802e0405000c103e403042081007040303000e00004200713403411030301401581043c1c1490f42c004d051a00089801e82501542030025034688c98000c02143e415072180e03900b5044c02824440035000c01c00b40c60303902c0341195240305010482d900c1454080c48403032000180610781984600d1000802904800c240441c0c0f21041000c064004100c81c42d541c00001019102d10310f45010511300f1008030306240c12070080240da03c02684d00062542020f40d4090418031005541d024146404000b81c01200e4000702d07010340d000c015007000301c4280e13810005450000340464411040d282280c000341c0003c1a8264078a5640b0041c600d0a0340501c080c124a0740035501c0c3d424a914140200100e03481b076003051000220005607a24000c0d44440385041d00135004144a207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96049415 1250 96048165 96048179
    0x9110d08040909120906110606040c020102040806041505061804031b05030d0c0822080c120f040906050103020f19020f0a1b150c080315061c14060a050105070c0f 71
    0x2503c41e501360350000d0030240c0c0c0003e500380308500201030300c9003160181100e61280c2c02840301a0040e840710b18155034081000040070302080008502c92030048042142000b2244041820b69402811301d41c441c2c800760b81030070324031201442c1c510380003075160600c0382c41c41820a0b0940505c8000d890003030042d01010071440c0000e41c05801150f800d012941d1075000503568690034250030800095500d5034850105d01c004009095a401000c80300c00000480e00c10001d01c0c0b141c0748555110b08082004044e011404104446a9002c3c801c0640000d00f0154104810304200626a00507542c003007113100000d8009448850091090100d0440c6410548101e10103908107802c08085040e400340400d0901040058102c6d5400d011345860340729a601c1c94a290500c1e03d0f480c84542014026040d442e500d01828201a5030f40030007010310507601025215240b00c860006403c542d0405010300e440650079081100b660f0310280301c28140c03802420001e0b11406281001c0c08190740313580140f2400b03140c03400045015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96050665 1250 96049415 96049433
    0x100507050d0c030509031605010b0604060f0306050a0501120f0b060a0c030905060307090b1b0a03080405010f05012403020912150a0207050304050d0f0b010f0f0909110d08040909 78
    0x84441141c00d001040400700d0480440e01c1c00c0f01c10b2062500b0030312141d1039204510803c40200d60164001003844030000e0000b94480c1c1c001d40c0190f022802c0c2110450700241c141c01501c000f020202e8040b100686040000b80485010b266814041036550b45810801001c651000c01d0707800c0080c0c02036403501d410030006000b03d29003260030b402042c074010000a1b07525200003103900c50201680c861102c50b250075a01580e40c0c21590070448001c0003050400b210850411149020324020395843d1030707074200b50400c9800c40e0410829a40d4183c280300040c0311a51680541e12090108101040300c00600c80c6003c600900559046a40c0150341482a149600c0002110a84010b0b4100841e2407515440c103007034100e20600c40020100d03001030000300013600d40844440078985c09070300d04031404102a07850724445882608140122480c42900b07004400401141102403c00701004000b88035040d00c40c107040b40d00c200c209a12034405034880e0001c03c030701c01041d034005000401c810321082d91039103030411076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96051915 1250 96050665 96050677
    0x1605090c211f0b032e030f06020417160302090c16050105090d0203070507030308040c03020402070b070e0105041d072307021008011d04020102120d02031b040f0b090310050705 77
    0x144609442c0441d4019221049030b01070804078200003104030341200d034244a40c08001080b517100f0b05403030002000c60f0f541c6908940d264800c5c0e900595503818080a580010b03400400361419901c040e15405401001000e200b090303e07011a0640720310303550b40411407860f20030940c0c030704000d01c10059110200201500b0060150480c4025190358290302a41207a03617019000f8040c10541c8150b0080000c240104569a0001d00441d0524205912500410b003070f41e00c0900100e800100d40c0c0200b001d000e9002c601400303000740910b4540c1c0b6162402921038408500c1003000041180000041240c25003d10003100c2d80c41845071521480010303251105c04944c10481c010383c0101d11622400c1c81180c8140412416200c004e50000c020b0034010800180c51007000700228158450301c00303a0b40304504000080e08051006400c0540d880c035200c040c0c5e5010403642074a503e40078005120a00c003545003030b4010401c1e0740148218944030503031400000d150400211140d175900e071a05091112080c0d1107401040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96053165 1250 96051915 96051961
    0x9151b0f010b10120c09150503070801080f0a170c0a05070f05040b0603010303080402030c030f16050d03090e0c1e030718030503090f04060806010e0403021605090c21 73
    0x800c910101c403d200c0840040d81800c8000b40142c0302822524049510040d15032426140c9041819110701b180b0142c0443c40300c848021481c04420840c035a5401b00da914090043c010141c40c1d4903549805a40d03840c0074081008085001c0f080000031800408015204421a4201281c10528490800391345a02d903501030034800c1040f0000104150034640100d803000b040180c0900c1c903580c61510104c03402400508101d915010b82d90050010355002c022100895440b8409840c1c035200001e9444e003002956480b46005180c000401c0001c0394210741c200b0202e4000000143e82a541c151201645200741001190011050003188408444200c0914800d00350380d2503c01040d1402c1610b6041004c041c032000780203a10800c917800c070900b0f008005424907040900003150440d12004c000d410210260444000084100100418587d0400840c600c1000d8a00e182070075134205000b01d002c3c51401042515214000039071015040c2c41400b0b0340522803442452640315042c003410708225907a03681d10300e01e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96054415 1250 96053165 96053171
    0x50606030c0616020d0218012d03110102010213030803070906020c0a2702120a061215240b0a02010c17160504030803070c0212070806040b060d0b010e04021e0609151b0f01 75
    0x450414000310744943d400c03102036046041034ac03455940c00180305140c1000390444d5004e000e01c204034101e070109100694460607400381c0724a42004000c28490b050f82c0910215405160700781016156031040070305681c000e0f0403030000038054806000c0503d00e02c034034103203005100161042c101032590001500560720030906100d081d0f035032201c0000d00c481205d0040d00500444c00703a41c1c4030a105501c111481e0316004c60044088000c80c020070000c1d21142e1203030fa4101c40000318400b0042d428442c90310415094140084603046400e41c00450907002041c10a81d42c103408031b8000c00f42e004e241506c0040d548100701d169680ba151500500b036401015040380114040101d48401040101d21103055030700d00001010300d9900e9883d4004201c40240503550012612640c81e0007150541e591107019008000014200d42044d10500080e42d41d04024603a90b07a00401c0c400842d642da210403902800012103404078161100e0b402e03005644168034142c0c00003100d00c40d403481c08850214003d1a103c445400030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96055665 1250 96054415 96054449
    0x910031b050c0d110f070e060306100b0406050d18050f070f06020c01080c1303051f18020909100e0f0123061302040b070b04050606030c0616020d021801 67
    0x140c81e42d01400c4564000754111015000f149440b4200e50310000292100701c40c1e0344080403c0c40c600706015500300002024031003041048908081098540000101c04003440d414030700000000140500c2c01b80008002c4001203a0903411042e40000d4246080300c1350002c0400072510344070f6690206222542c40d0360007420400112a650810034104031040d540290000e050b0180045540e21401000c1240740c4105001c0607a1020900314a02e0145110314000c0200c070301e500454104011140b042120710500300522905101c6202105001040e811f4408610585500081a007000040d00b1424103441c9444148500c0000015082c1540750190008110b142c2017507422000354510640b0314041080c2d56001708450b400c00740380d558510b10781010011700b095115400c9103600d520003801602c52412030403e00060101c240090358126101310b00a0540b103040c18042000b50041072241d61500104010030002e549400904005482d4020081c0c9500d2282c0d503050044100203020f0442c54011080c00d0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96056915 1250 96055665 96055667
    0x60e04031716180801050a0c08090c0d0f020d0f03030218030105010302030706080403051306030903120b0312091512040309170616030209040f090203010b01020109080906070201050910031b 83
    0xc0c0700c1c000e000c0020128030040d50841c040d41c12030341d448100103a0004001d03000500c03a41c00c1c89101d0050184003030101d80c8041c001c42c010304498028103408119084070b40c0d0500c1c29a01c100000341038540c800c1010100e0112800000c1c01140040009822260001c40210815074594014907010b00803800300c9078000500014103080300c209000003034050303112100c280102e600540c006503210b0311900d0014500300c128884510008904e510140220f40c40b00114002c0641204842c01c10300e0103000100442e0300d644001995507441103200030f0504200080040700b50b15544003240d410502e030105299555188003170300138551011a021b800182644001190903940301c490302c0d140c0e045042c0100b42d2038543da002d520750b407441000b8400a0541c200004101070300c60303014000c200169820006504800c0e4010f05081d075481221f080e046902d403260120001d68400140c3d03520b00402d8958989400c540e1005942d244141200d5070b51051100c04000d9000f07a264020340c41f1019110074107511281803e40c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96058165 1250 96056915 96056957
    0x705031201050a0f05030a0b1f03030c0203063103030204090c0206060a0e06060301140a03062a02010c051e0f03180c0102030a0e0d1a01060f1b02060708070302030d060e0403 76
    0x3941c2c0d899001030175030201040e2040400c0d49c00c620070030209a01c4002c508130349045443c4030340c0114046408c604001040d4a014000750b54000494125000e03442c406c0c0d81d150306094038028822141244104000f01803511a9068801820924404110607601524041d540341412140071f44104c6001c080030424001080740107001340d0000e01842e00318bd0a098a44c10407100400c440d917003140111600002241c01402007107084441801a00d1a0b0808425240b140b40b81300080c441c25a03040c125140c0c801548130044a0040254012030054040d1750b88100410f8441c1001c80c1a4000000c410b002a034581144400c040c1c0101004031445420f00d0001640c8034020001610045000d00160390340c24205800c0595900c0e1080305501810030b10008560807034003080c1c0040340040d9031420f5080d001a0008400c00486401d00b12003c030000c019070020b9810b02c20454011f00718400860800b04050003082500c408031601a000e024260b00c030781d1404546d50303040320190300180d1840c0003400034492000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96059415 1250 96058165 96058169
    0xa121803020309150d15030501050603070807061b050708060123090a05042102010b0a0f0315090c17031905120a020903030904020d0204060f02030412060b060705031201050a0f 77
    0x14014505142000c3e0402c00304801c45505041c3c449002c0005a115000c41e00c19510075031504a030ba0060641141400760844900510303030790003a0303c80d0b2800c0c080b600c0c0010f00502107034241c3c40c101c1c1e451803011025541504003941d000b440341c4a0004040742000000c10034506880030010300301f080c41c00c80610b5041c06020700d80304036041000400490001761180d0403141d0301c24090901c1140b038902101044070030640c640700800040c0d554400c1c3c4142440c0000b4444001c14025002c1600c01d406d41e00e5000544807041040c000140e034589003001001035900c0319400500031440594503182c110b1001070b40341e40c0159420146035125800400c401801401a0b1b510480d041706006000d03174440d10010001d50240341613a9252006105e4034600750340701e00083c45164803c4101688452410f400903200741d140c04074100a64100303000a00c92404140304255005402c0580030402e04800c0010890a02c0b582202400e140000511a0f0700e500900000c2030495100756003640d04a65200281040c140e118 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96060665 1250 96059415 96059417
    0xc07080a020f101d04090503160b100602060612071505030106142701050c010c12180803040303051e0702011b020706090e040c120f050d020105130209090a080a121803 73
    0x44556110007541e6800061460740301405c00103440d141c9446180c5542c0202c825000c00c07484202c40c42d0108101c60f00010b40140207040c00030855800c0c090042d4a0303840080080d4007400f042016040322031000c10503c4002c221801d03001d00d51940c500e0f4010103645c0240039600114880d18045070034800090200d401500070b00301c000c50064100d15808445000c42e030460746c1080400c0c0004040810700b8840c0c0e9842c40240d0f02c0c0c1c2d42002040b0b000400907907041200c1000c1000701070040c1c50100c0c0110381107070b5115625107400035480e0f030b5604201e040e907204042c07490641a10907041101c1c2d0794055110081000303e0941d0603107171441e4080120703580c5100b801210006549030600f001149000707480c482d0080d2250381d80b030960541300c81e40c1e09030519040000307980142d1145403010910a060001010081d05e501c001e100e6882e28401c64884414603190082c012031104e00002c1c02c80e5002d22400e101241e0240d4950380c2c41803100d1300206843c0351181001da101d458914181e200030320042425602d1541 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96061915 1250 96060665 96060677
    0x60d0b010512070b030114011101090515041505012c150402070507080321090d05030c0a0201090f11040c021f0b0109080106030309061407020a1701020c07080a020f10 73
    0x30a4144010202e0341e0800102c248900b54010401d42c800380b018601804000120307100072034910000418031486000e001e01244d00d8882c0c5076010480100d03141d050102c003846c1055880d1078905d043c0b891401402a040b1010740303441c0c004141580d1032510181c10804142c0e1400079a0400d0340204010002030b41c0c11003101042000d10707075250420f5005406058055070680740c1d01c40e034400c0800d05561101044060340012001003a484072020612203030004500c00041c5140c0c0152030740540030b4030018002058030300c3d02040b00107840340300f50007070071240d648072042da04102d0251516801c00040824070700d00c950305200303840c2801c910028800c04404050351840c030212090f8104440148140324105040140c10440483c10400034041d01e00158801d81d122102c482c9804001840600d42242040805030308110680151350340f4180d500c25604030001541d00f88660085580c0244108250440940100d0500041a107004549024407900a803004038010102204000c110400321840c500070880b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96063165 1250 96061915 96061919
    0x3031a0a050f060c1b01111606051e0a08010509070e0f04021b0715030510050609040b0105091306180203040c03110307091109040b0301020406050a03090c030b010b030906060d0b01 79
    0x5400110440d00410140c9400c3c40d0030ba8288000e8142404c0c1c0044020302e4601d0a004485c559104001c0c40c1c585004101600951400346242c07000034030a8400c60040002c0030444100203601040e0082682c0807103002180c4d280c4010602411141d002d100d000d10801c0004000741107207001d50b84500d1680d20080403048484904000c01c402900b00b08a1901204403e06612003200e40400244001d0032801d6604d005021050720010207466005042c55510044004204640d40300c1e1804d80312044412580440d4214004c00126040c0c01740100c500e500648047c8580000311003640a102990031b400d00c2c440f0184500501d9100b43d00c000d0b54010450880644104003003540000c00304003401005040c1c03040e03a9681c402c00c0050320682d40828560717a03c0081d00c0c802d145802d216041030780006500030740c20a03150960182880c06a54803c1080c1602c5804400400040c0d2040b84050760b030011048085503184c54510220381c2084500c0149403240c0f1020440901d00341607401c01c4641d00028504403a8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96064415 1250 96063165 96063169
    0xb010210020705010608190516120323030115030b03070b16050102071a090105130b16050702040c0c0209071409010e040e1c120e06070302030916030f03031a0a05 71
    0x5071000b8001d880c59541c5c0d4101041941003403000c07100b1030f0601944c20b0f4030f140c4181030042c18506400c580628810160f0400c000d04003007102550f100503014101080106510207402070117456034a2424040c2030300000221348154076091401a600259400f044991504800d040e41e90756903008a40c11405d05003d140c19145081c400b0701d2004d8411400581046029911655651030f02c0c4290621143c0400811125440c2485040d502c4032401100001413016a11181e46d040c1d4007030000b410100d00034a4440c101400b0310201c801c49940544200001030355000014002818418102e115203240e1000c00d2a052180b040c0e02c140c18070522130706103409000344c01900c044080c880d006070029210f035000b0010110038484001403092244102410155141000b0100410080079459892601160310400d00c2c0c0010100c1e0b100b02d16003801aa0f0b9200e40036120302c1c1104400404451484c00b20010041042d58901c446806119403020321013954030100c2c1496800710840000d030494a0194100014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96065665 1250 96064415 96064417
    0xf01050c0d24092406051b03211e0109020403050606120309010302070201091d06040b0103020708030f041109040602041e081518031b0d09050a12150f05040210030b01021002 76
    0x25181c1d030851106002030f0000e0000c0c11000d45d010394081440030030f003c4035122481e201810f1808491014502c2c0110120545460481010700d403803498020f18005000750f00600407050500c0750040d144841980d50f05c1804d0b001c1d42c081e001c1120076000724000704480d41060a06081d0050481024500344031081004400a41000348140e040100e5031000003140c0c511401c0d4640c00c00640c90260a00b440c3c444140429a03201d03000190425204200c0d07075010a600c102503d8000b07008c5044402280c4a83c10203100e0902c810701042e1f80802543c0c1804104020350780140704568840c0750442d62019281c0034045407040f2445614819001200201407079440034404a92102d5441c40240100d5001815146550004c81c0461640707902c180c00c81e101c40604000103022840c16240c944101814140440c0202d8098800c244c0113242d01c81d804403c0042d0600f1400b1490100f00c010480309100c214250701502c07050b01d040e401100c018040c0001a4400e000341c0e4100c07601a0024400c1001d05607094000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96066915 1250 96065665 96065681
    0x3110c060304060902010f0e0604030209040203010905030310060f05070206040b0a02010e0f0114010f150503180a0308060111010501060914010908030a020105180708100c020f01050c0d2409 83
    0x500a0550569240d40d40201641c0190f025641c0081d41d203c8034030001d4403900d01040400d050100c18522526244c0c1c808003100c0c29250705030703034680f600d490720310200c0d0143c0760440e001030050001004004021700451200320440e081c135680c22004580750a0182c513a8403640300080d4014400f00414030860940d44001c100c5410b580c400010a0146d4600340345c10110301114040380b5075124550320724503065400c006801740c0100344e10004441d240a010002c0072111480c400305020002c00011303d40010700004d01280c00b20b6406a41c031841d11490000e010032401c0f41c0d65404a01218052054440f0500c1154140c842d1922941d4011382060208030724100c041d0412170410183c81804640c030101880601520303406600080341c0ca0614040310601c0b1801001c2170906503008030400c21051200140c8000e0208100c08005449460104200e05140c03840708190540d6003040c0c22300900c880541d006012442d1440c108002d000c80e1084941b120074440c1c05220010354851b04284400400ca2b03108040f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96068165 1250 96066915 96066947
    0x4080309091f17010b03010e21040e090d1202160201080615040e010f05010507080f0d0204030222050703090506060f0105040e09030d060f0b0a120b0411090a091803 72
    0x19031502080d0700b12080c90a400c4a0311810404101a12400d000d000e1142c001c04101c0003031103020310143c42103940b41c0c5081c5841d80010022810540b035140d00f50121005014483c0181101d440e1400040343c0c1d40003030b051030a0005081841c685c2e0000e030b0902c25226a21034407242c400040c005030300116900380000d000039602200d003c80031200c1410300c00050005103602515504c0c0c035890460240300c0e40c2070903409507041c010100401000200d60b00d08a800883c140e00c0070584410902d4481802406141c100035006440c0b21b0001d810f103151500b41c3e94401d881c42c1c000307214540d0b991a044042e20201d1070018a240c0c07005001c204d0724601401401030302e000614005040582da8940d80d6510320054510b120250000103a6240590441c014003014002e0414a181c00d9440e11044280078030074818154100300e8002030030703026046984c10031441c03088001c2c824005490b48150305981ca44c041d8810074483c1400c514000b40c8510140203600e5000101c030581248250143c41c2034801010480c4414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96069415 1250 96068165 96068191
    0x60403060606080a060b0304200d0b18030913022a0a021315051c0b07170604060f090902040605120304180603050601030f06090b0c03010608150603071206030203030301060e03070b0408030909 84
    0x22040d500d80c0c1d842e40319441e0081c5860030bd2400c14110118800f05400f4a5140a80081048800782e40b47c6451640400700c1a00d40184d58041c40403c80c10702492032009500ca004c952048550894000900d00124500849401c509030300c01881c0c813000c80700e80010a4200f008001c10402c41c0740f504da00c3d80442c0c910460f00aa40c0504165589281d01c90115201c0002c14140b03540d254040909000c000c1c0e200e6004c0d141044964104110b648408c5c406206141a058551b0840320841d103481c0c010341c0062101500035664001181c525079140d0708a400b900c20100b034841009a910714907030044204594012020701296403e580319801241900034040e035080703031280740810004110300d4246210300d51381540c10742c995050400017040c100028200c00e4112400c1c00304040c0540d40c01c800c40c0c2e0440b40b04c1c2031208003000c0d141e5020000d8406944080d52502000c40001a003681004d07107508086030031402d4810286c0c42d0031100220740503600030070b9042d40c000d01c0765000f94108401c002e46c018050f80000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96070665 1250 96069415 96069473
    0x10312050c100518070602060f04060b01051b061503030712050919060302031509091c091d040201111524120a050f01140a0c0509060403060606080a060b0304 69
    0x1c0001d80740240c629001c0750544013440005800140050000f5104074030290800e400c1a400c4138803440c00141002c2c0a05590b0b075100f104e00c0e80580103c500c40d803002d01c62010600e0001c401c0d95100d0b80d01721a10344003a5802100c401040c40e01000f1240c4171039008403110f0f40c6064040089415400c65142250001c2d5481d50900703011141c2401c000c02031200f076601694134508a0440c40c2100c0040030301034043c66a8405000d0288000301f01d00c2000080b104100940c210410400c40e000e11f21540f12207810351100d04584410825045500d03c02c41c000e880d4540300c2c5445060b416035804202480c28074000501000c140604100c9070300f1040031104e50484065410100c000501c0e0514030800719443c1e17480303180c604040000c20720101c007a244003a070003009204c2c000a03d4602c0d400c40200240400340d038078560908818000c07002d4501140380501920b8a454684c0b5151004240d00d0207264041180240001d501d4800d502800c02a074000c1c1110509640381da07921300c0c5c0560ae0300101d80718181a40081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96071915 1250 96070665 96070693
    0x10110a110f0a1806050a0b0304120315060305100f0f060503070309020604080a0311070506090d0213110409270303090f06050a021c0c08041b0e0a0c030b010305010312050c 75
    0x1920025000e031143c0d00d0420030003c40410121181c42e4405030140041500401c10040e254058a5206030401c9c41404400d0a80904500401ca0f1918590508010510120300298154805445010a04410076000741ca50703141110341380441c81500e4805100d010b092240034450310148d03801258030b08002c00c5204540e8000768003a00160407080b040e80c030160700c0c2402e040e48040400c103080d017140c016007100d50a04010031018415503900d0360160380414161000c644498020040e40e600d100c104014204104003880415402481610002c0b420700002803010f0180408010f050040f01c035410003245519903040e0058015000140d03514070b2a00545400300d1401d0007010b02c01d01a0440050b40c1f036120015000c080c24140b00d1040e500d42c90711801050f0b07242c02940d490b400c15041b1440c4074000765070f5182c40e00a413806030083c00d148000d84003800180040d41d000309800315120b4034180b05030300c3e25500440445509100103032003140070300c0408101c03901500080c80100c0140c0300b034640a02e46c13210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96073165 1250 96071915 96071929
    0x9061516060b040f091e02060c070305060405060f060121020d0e1c02070e070806060f0a1806080f0403050c070b1b0106060503040b0f07090e07030b10110a110f 70
    0x310070345406803641c0241d50070745014400c0300c400c0342c20400c0030006964907440b000b0f0300c810002c01d501018008282c000c0c0940d0744040c140c4905560703c00c1160001609e0b40f0307200b41c94042c1514201c800344500303008079000284040c2442c1c030401040c0e40d54540b03130450300002c188030050b50700415002542045030030500223081c0503800204a03180c1c001c2240c03003610140052251210101c03030007107401c40740007885030880c4000081c0c1c01c4441c07403030302c101241c94200000300e580c8686c00407400c0034100041c1e141d85250700400241e20410301941d242c010260303200c00a9400341d00c02c40f20300031560f40c81c1c8000b0707001a0090010b021407182100c11210386c40d44807030035070740c0b9503201c0448031104106402403844003020900880000e402189000c2c0c0c25414250f607038542e50b0034082c00c02e05c02481c4c064005220349100f480c000340200300d003031107440c810f0074a51006001444406d07800c0f07008030381502a03142214002c480c02d05c0c0c00b0740007400074804e042181d102c1904290588184980c000030424580e038141c0c1e6800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96074415 1250 96073165 96073207
    0x171501050d080d0f0f0c09050a0803070507050405061210060302040b090702060403031d150a06170a170d0203070c060b010806030c040207110916031a0a060503130b0109020901030e0c090615 83
    0x18a4501f001403c210030046284030a901c0b40e59580e00402507980042e40101c0c03405c2c2281c03c244c6000c58141c40d8500024140000d020148800e1b100300140140f0041140d040941120300a0b178040140002c0c5600344140d0450031070342400568032040108001a00ca0f500403154020091440b8090785e40e61030703150381048070340101c18007510065400d10100c0b980d180304490080c007510154842106104002ea42c45002104000c2e000d800040c100b00590515101126148592503804540d00d00c2c0c01900903220b00c190400031303180e061030039402c02d126500951119016803401001407030003403848070800010b13520807682240c0740c42c0242070b14655611500340e06800394044407152105002c800c00700a0850784001d98048078040e020724006555100c11810700c09840242c5440380d502d035205500c071a0b02540d0801c0040401d6681c030000070300c145565000d0204035801340c1c3c1c24801d0005204c03a0079901c1ca001800f0640c0805584c011a0b03041c50400f40440170100004400c50a22002241816401c2840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96075665 1250 96074415 96074417
    0xf141305072106080c010f02070e0f0702010e0105010b0412081c02191403130516062705150901090801150302270c0a020304171501050d080d0f0f0c 65
    0xb4010440031080e0078980025007103507800007040840c0c908482c0ea5640c100d003100590501002e1a103400ea403501c24800c10300034001c3e00d0035406860416500341e203503c81b001c440107401546030201c800b400500601a1300d040f41c03403246c01c00d03041608100c0c5000780c1e07050b401011246200c00700b1420034004410207400452640b00f400060325102c03901d080041c1800d011620104003c84840042407101904069030380113104015080360503a210b103446890b100601242d0500384070340c0200000c0359035000c00c000360301c485420780b21030124220030142c5012900c54058598480101103100840341e0303540016040780d80051505140c0569922206800c40d030310301c1c80c800d0208043c05403c0c81036041107000d41e501905aa108280d1070100b01c60184405400a0f2104124010000e540810030f4800c10a680251440e64a0025378103000c0c50700c00d954404913180100c0c1400c0d1000002440d1601c0d840f40310041e600f0411040c0380c1010300d4007140080c8034a04002900d29520700701d1450b8151144110f086034506 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96076915 1250 96075665 96075677
    0x9031608010b010908070308040306051302120706021c0c0f1e0b1b030403020c1e1804050105010906080703030503070306030803090109050c0906010c0b1b03040b1b040f14130507 78
    0x70030001011380e20030350405241540142d10030000946444120b4003280d41100c400a096211603210240d000c508480296000c1c3c1d00000c0082496400b2900d20125130854085864280c5403441d507184280049800c03001103001c0c3c11b184404905404c00070044648645121020b44490b00703007114207615150005c3d50400348000030409030188144903024607250640d249400e62800307940080d0380e48455680640250600c50340008a4906a507160308801d40007801d5505240710f40081c1d844c1d0010480e000d41d125800e2a00014254031280300c0c8005580c14000903151407400c50720700307664690018054000301580c1d50400030210780d400018500501d04600042052030305401d0203450a440c90541500c0f58284805001c216030f04507072184482a070104400407565a20701b0580c0d42a503510b20000d039400000010441007118001c00c03513200d0105c00b030254102202210084c162030180c1d0052402500f5400c80602c800f03080100021074028004101552102407102d243c4107035141915400c000c181 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96078165 1250 96076915 96076931
    0x705100c05040f08060103120e030a05030a120b15030103080a02150a020403020301050714160602121e0106020a0206030a051909080a02010f09021804021305070206100b0a12020903160801 82
    0x2d02c01c12100003404c0c0040100415419503c0320400c00300e000c0301d00814422061801c1c0c141c0d480c00e0065103441e030f0704581900e4403000c00b514058400802d00704c7d5615064a4840a44031070f26265000c118000c06101c1c1c1603007560309558410003598803101e00c0c0415403040b0b244c0c40404404162844c6e00c1201c00450242e04c1c1c4c0e107548181400d40750090044400c0c42000b0499600e9103d01c078090700c3c0c0002ca422400c00c00c102c900e007802402440b8a24020b43c01214100400891422003006916120800e680c540d140340c0e81e51200700c0c1c4400210900a51180041000c40e4109003980c00050f0454800d00202c0320250803640800102c80305004111040c1c0d034045080e00d211754083c45441414071480031701307105140742035002800102c0c00325018000703203800402050940d2154000801000e034140c0003040030341004d1130065a5824100c5200d1030030140240d01080d07030101d103800c2d2103101a20740c960340300c422582c0800c1c002a40141c1d40d415014030900a1080002c456582800010440da17400090960 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96079415 1250 96078165 96078179
    0x25050d091a07030209011d0105040315140c030f060f0406050306090f120a12090309030209090102040f0b071509080c031b0105010b1e0703090b210603011a01050705100c0504 76
    0x41008200c2c0062601c10b01403038005981007600c0d0844a10740c1c2e0200c40750b200700701c801070341c1a01176500064014040c1460310000341c0203a9004400012906907034808640e24011520142e12080354030f807241c852800080781c0981001d07480510389500080012400035100c6000c20b1038801c1c00c55030800c10340d0210701e0f501900d29080c003030010300751f80210b10240340c1452244041d100000162805a542d507440c1841000e0600c01e4034160051903005264401038140403400901030341003130140e5041483c52960016a0350901404c4a9005a00c02041d014078085204600c0003400c907043c042d90700070410402200060010b00c0108135034641707143c400e0040b0203801007042c21030f01c058100c52070901c010409003403049285848070785605007501c4001d035188481e1900300c40d048200d50112400c00070104201e003148500c4c03001403005810b203681e4100c280c8d0351402010f0984902103145554640103c03040d01065105000404d0824040c0003190403155031420036000722144a80707404002040890f06000c0b072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96080665 1250 96079415 96079463
    0x213120f060c020d090303081f08070f0806060109180905030a030204080606060708070816021003050601030c0e13180c03050705030706030e060f06011107060201020318010525050d09 80
    0x2d40b00ca00c02400010f21890000d00044103600000d800d020003140001c0b05c126490050142c1e0301c40351001080d0141d078514038141d841c4542c1c001c6880b0f401100501080c81d40001455a106080583d20b101c16640361034502210b131042500e14500b510b440d001110302059040005203460080d50350f005903650b1800a025040c5200600218840c0c10200f082c80301003210f000a44602c00d40100d00345540782140e82081603400b5240070000d400061a01c40c02c2c076000d030544e12880c460842a201130180300344280f01220070407910a040355004102007902040160309134046002c0203215844410341292503115000488090307401111964001042032010342010300c05d10005004904003030052180795111030340c8414004101c1440c0440300400a01c803603109454459000d5024020f6500c0b4944404000b8003035401210103141ea03000304004040f0380d10341445098807603540c44980145000205a4400c00041039600f8078003044000d00c0313107100b4000311b44109010944203c00c1c811011030091801001d03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96081915 1250 96080665 96080681
    0xa0611030613110708090a08060c03040c080313030b060f1e0a0e040c15120207110103060b0c06011203030204051002010f0b011b120210020a090302130c0207090213120f06 75
    0x810b81c10303d800310544a4084041e551240c0e448440c036511403422802050441c40907030f11802081c07113800180309800c42550010b600a600801701d242c1c03181c0d21001d9aa1f642c1c801c8103070b03560350315900c1181080400c02d000d00540d0070980003007090f103075000c0c03d0b40013130380140d4541f000b03040742241800500c02d1894004211401040181c00201e0b03185042d440740d9500003014810026005200161105058404c01e0300e0f01d110002c0c241c0071910b43d585800c0a1004542065226011030300d080400b0540d5801101501e08060041005000c00c1e824000502902540d02c02c0850a01d50240300104041c0d607111700c1141e1443c85540000341038090400300390f003645e1414118a05200d20018158544182000d021440d83d81201c412560f180703000004a00d8641440c0302a0000b138408102034100503406107050088a008840d880c5c2130300401031448040300d03585900b25000d41c0c01a2400c029504803a00a000c03c82c00103d42449000d64800461244602c44041100c9082c4c4440e1042c08011140c03080d2a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96083165 1250 96081915 96081949
    0x20c0705090717101205012019120902030a0302030309101a010e1201020a0f08010b0c19080403060606091701050103020a05041d070303050a021203160c050a06110306 73
    0x21141031429010b00340300b1604003459030001c0e003603000030301c03010804d805400104252552404146203d0403c40c0c002d240c00d42510108a1020116803070f12680c3d1400e80749a000703140d03802d00e5018100c030000d40d182102d130103d00713081d66110755143c0c001d69400d018503c0703154040d030061039407403800407079143c2004c283c80d03031034403281d450070f001655120154009071110100030f007400c01c0c000048500080021143d16411000c560001569030001540f00c4103011080350729486036052a41c803841c514559014148400d180c03076200010800160035a003280380f030698003594241c0d15242d12034580e0780030360300140c0243c0041140e0005c100003007410a40003a160b09600e0008100e55411507001a6045400748501c52207641c807803002007250f50103480680f01080e0070034100c0e4291603891501a05580041883d0409401502c00580c8142440e400b103901c540300540e50707042c038009000740a8a00030107244007620144181e000d1345000070340520480030380c00205143c094491414200300f10b0320400f400141031b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96084415 1250 96083165 96083179
    0x807080103120f02012009010212091804080705010c0203180d0b06090a02040929010801140114191e0c170306030a0b0f0601030c030b060a0f0513060201020c0705 71
    0x102c1d86420510280d0040762808000c120b010500484c090042c80390f40c200c804150032070450040040d40024441c032003083c5c09684000b0889014040c16000341e444080d001326170b0401030f001150a80200075070051141c801d10781440c03401e44641e0b084a0900b4410405684002030a80c4001280a89907030018000c0700c00c2007481e45035a440700980c40c8090070084c080c004d110041000640140c042c2d4010301501d60040040d01e00200e10f0400040c03024020400604051401039100d500c600c3c901d50507511030111084d07c04c0301a50045071801d6006c40981018141400b401940030740965180307215070301c140d0b40d42d561402280740d00a000c0d0070305032076142401048a603881c00101d201a0540d00c841c80c0880494903540d500300420b04101040c0c00040c941e4100c0c81c1002070000709140c200c1c0c01120700380d0b400c000c4420030341401e6046814642074640d12070820305c0800d0250307202c2c04411181111620704581804190f0b6548400c0800c25040540540d4020490fa0090042005142e0062400b00c803c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96085665 1250 96084415 96084419
    0x30e0a0b041110050a030b0609120709050c040302150a020a080309010504120518041a10180509040b1305010605040e030406180501050301031506050927010504030e040f091502070308070801 83
    0xc0e141741324032510b4209050300e40580e040d00e40d4910003075984040000d01180000b466469201d510b6240901804c2c490364a0b00b00456403510040c415582600d60141c00d64902c02002d2070018055080303107603404118070403460510002240e00000d180210501c40022626081524188003440550b041e0101000401d0101804400020300048070144054400044010400075176080380c5071400480c0d03400030005420449001e81c0304241d004024880d4030884100c42e158010002442004e0301c019189004040c0884c00442200307180140c460710800c00041c034a80d03250041400d495402c107858034240c2000c1020445160080385201232181d11061400c0b02904100c006460ba01040c0030280000003588541c010801c2954040ca0103428003c010003d1464107161019008100082c200c140f48511ba0801c03542c41c0e01402081e014a500d9102d00081c00d0303102082c4401080f0407100c1414090700d4003d202d000c206d00341d252000aa020400140c0c1e60b16041c10007030300000018100e102003207604001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96086915 1250 96085665 96085667
    0x4140f030309100915090f150e04021c0501080705031e061b0c0f060a0c050304050615030a06021603080708010e0a090c1e061206050105090d03030e0a0b041110 70
    0x1250284201260000401d00034044222000c0c203141d008080c00e842840c05c0c13082140e411065240c1251380c00170700d006080d07031038401c103920f0942d5108400001c0351030080041c00303525103500a00510b100c008008501c50301e4882c0014141d881c217078400d035156080304000340714074203003840a0881882918540341c1d01410280314107942c1e29004100103600c20b16000300405102c0024215001341040104135070325954001803054440c0c00c05c0e5480710405103440c40d03107035800703000c0c4013680e22071034120015104076511240f84210f000400701c00a030303040c0620210140000d020b0300c09031010400f494560030800310603150142000501074a180305104140c0010025981c035a80c1c00c592100000c2400300c1c4001051030400003900f8203800261621000c0000c040503445040541801c0b5402d80d641d40216507060400c81003100c0c00ca01400d40028010401c41c0c5aa0820b40350409003248245400030354200304401c01414451100c2084420020030014003052101c142d024440070b1a003103c0103042d05a42140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96088165 1250 96086915 96086917
    0x207080904020309010e03190f0f0509010f02071505030604050132030a021e092419030f030801090f02160b1315060305060903031012060b0402070804140f0303 70
    0x1034914411500000029907146082d00b240031411400801c0300e442e0076480758201800e03000c5502e070900103818403000700d041505ca0803c001c192400c40c5c44203450180300c140111400401c0d07001c000c003907218041d0001400101452071101d203443d1a80c5250700c9044c2034040005490069024103080403040e403402d00d0288010007840c90710510900c11222002050021a060100300c91300039603c01030080e1300c00c0004800c80e0500d0f034128421075801c3c01e950343c1c0c0d181074503481c203400542c1e07240c0d0304040001102504041891110364801270b08140c50142e0307a50340d1113400740440402180010844d07001004500f0b00350203a01c12404900600b941007241344254102403404101c40903101c0310310f040c0030400311001d04034881000c03a040006811440516090640544a41d100c1200c0c1485800d0001c0c041c0200842583e02560050107400c4142d4074000342d581d000c04008205603940c0e65104000d00180e40c0303034802040e800384143e08480e241da20308031940148032000316800d8002c1c2000340501005d81e5000c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96089415 1250 96088165 96088177
    0x807050103110408060609040303061e0501020f0d0f0e0102030706050108031c0606080703020f0d0c030c0905030c0a0905040c090c09090c0c0b0105100302160503040e01060207080a06022b05010801060603020708 92
    0x2507000c47c1c2c1c130743d66800c2c200d015100b21751060b00740141e03009180c01080c680c0c41d641c07001d4600a801302d40c142c80035080c6a69444100c0f054600025246203506801796128025403550000c051049a00302982521402c0c12603a0a0388800655400000c000d003000810000c034644045c1e12510402041d450a44090640326008210004240e030000c0c000e4055641c040694060120301001000314a4281e04098010128040b90f940800c100080004191800168020301550003a100305112032900c8455401f500c000f0b4070440b281807522901103000040380c4184424034007a5664240c250b850403c030402150100d48014040145000c0030f0004244202540b604403081a208207046c080c80300300031070080c0a540f84842d01c41d07566040c14014808004068001c0d554074400038501c9036a01c0c203080ea42c400540c03058058a4006c0d0b44844085410b541c050301003903111101c03443c07100d20340a4a00040c810f4203050051440d603190018840c05109200c1d5601038036890408510f0090f40d5281c5486500500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96090665 1250 96089415 96089419
    0x40305030a090204020d140109060909030c110d050a0506060901240c0302120d0504060b0901030f030c1a011502060a0b0607021e0d0f030f08070504091a090108070501031104080606 79
    0x240b05002c045495642c100c0c0c002c020300102c204000340c01e141d07034148072000031710903800206c0c100310021441086520400b1005981511030108205080d41c60510f000d04c0061b1a44d40425011880e0303020840622141c0c500b18401c2000e40450316105040292094040c0c2003107042000181c100c45000303407400c3d151120703400d6600b80103240d501c003440c0c02c0b0b00e80514107024483c2100e0103d0320801aa41030b42169000c1d61145005100f40d5010700d06000c00d01c402480060040c404040c111004640120032600d103450041ca99008400d0b0f031154400e0780ca0000386c2c0302c041c03429004005840000e078140480c42e041014036500f0302c40360404070001100d0f40144bc3d40a03104101c40c0380400e4117403401d9003983c1805003000d4084800861076051491090000030016404103510191440c0c6035403141659a10404103900e41c03604240c180b0078240010000a500e08000c0d0642108003095a0342c0d05078040c0c000e02040c40202240c40c24440010161150280c1d0074901c450305100a2021523800701c1c0c601d91051003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96091915 1250 96090665 96090671
    0x4020c0f1005011a0d060f090c020f010513080d110406080f0f06030c01030c0504050a0909020907050703091502030d0504051b0604030218090304090f020d230f150301050a06051008040305030a 84
    0x902d5019000506c0264417102c2040340d0703864000350302d50240c1c2004408203901d4086e1500255458072040c01e80364125007044007080c0032440400014189000b0300700d240c40010000400d00c500305c4110040e98000c0d0424008140114204455190315104c44c41c1d008642e50f0340c8030210300340000481d644119024880c0e051648800205007501c0c07103902620010500141030100d040c0d50303145040700904907044203a01641000300003d50076401901150b420390b5156941094180c9480c03485d2802040404040c811400108034503001c0c000765000c0e42d8003841c003030800b81c104c0d66010080101c6017040c90250320b025000c02d200800150f50f80c0304c01a4a403855105984d81d00c1c0e50b60300c119900318412a0480d54840d4545603018201d91940e5003e082c88826081080080c4156010030351246080514901310301c01170303540002c41c001a5040c2d041d4000305a20007007407076510804000707030940703a0031180c00340140d80e00c1d0000c001920340700e00b0300f07044e4401d142031000f414141510300420903c40240111000340d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96093165 1250 96091915 96091927
    0x2a0307050c15070203061f0602060106090504020f12042109030203060406020310030b010825050303090d030e0406080114060f01050415050f0703080601080601030621020f04020c0f1005011a 83
    0x1031008103c8800550040a980f1603161841c042c0700c40041d68000d060410120080104900d400001c0c01810b03a89207448148100317140400b0080a5400524203900c0d044051201c011407041d140003c0d4080d131710031aa40000d00440451004503420001002c108210300c01c80200302588000c81d000e80c1107900710f00c025130389a0300c104214019015a5000410401c041e80000910210200d80720080c0c2d0b4214a906160a0490003441d00004250140d980d050b001008036081602e00842c015211a00ca410b111020800d8600010101c510350ba220502594650034940494017561803003691107401226003445501c51400001c140d4081c0380119a1a5904282d030141094002c1081d02c01203904205459a10206480c0040c0941d10036181140890020b80114001d98042c1c05141c05071240700e880924803202c1c0c0c20720100602c01c40441030b41c01c41c1d0302850301c110a848500080c00070030340b10401442010f500c03010075454444641003125100b850200107100307021514104a00c08195401603640b920 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96094415 1250 96093165 96093199
    0xc03230c090d20040c0e060706112209140f070c0803070e010206090c01020607030b190609080d230919080601061205011d090a082a0307050c 62
    0x200ca07a094042c1c1c003100da20740c8481048100300416001d02401c01510100c1d0090a0070320050712032802500010407503520380d54a644c1481c02c003900903503024a20104801018079441d5003a0390040d03040355080c446221540c0c0e40040d4400300000200314440701042215009803024961b0000500303004160107408000c5041d0520401a200c1e03015000b1009581d03a0406400142280c03203440030090140c09000001303040d245022400c0c603440003043e0041c0400341d60700c51007107004100c0c41380c029030700680d080c50030b015603002500000c0c003500098903910010f90505002c0d44c40d21515070826410840981c03c0f4200c040304555034504103200c44224140c4a03c0b424000491000c040441034040e01c11700100010b807540d000460f1412143d403912880303469451000700740190b410900600600c40890f110300700c54940e503001e1031544114400c00ba100310300c0700d076511166a81d10219030b01ca41510b4131b42d104602d86943c600d01201c012000d0f00194504141540c41b1615058400460f034450b14042c017203243c107d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96095665 1250 96094415 96094417
    0x30721110111070f03060506030105090d23070c030308060909030d090f061b0305060d050a02120c030a121e020d120b04020706090b060901060801030f050313060f02010c03230c 77
    0x10490b00001e5941043d140c4150403100c490600c0b0a8400604110102d0b20a05042c400e8900a050b032001400c6520415003003624020741c0c20725a0006110741190318140381101c85d020b4115240328800900480d465405c0040a55201428451044491000b4088151000001c447d441d03200844e0104182c2c00606140c1003015a40d00098800c904000850b01440c02c000200e014440d00c40d00c0411042c1c8a0304248600700407030b841700600c154420402403000d403a00c001c800c045441d01400300e40384001584042410300951480403900408000c0025002d940c02c2281e10f0b0102a2051040441e8024074800950f107160005d10681844420070100c0007400749504031802c4c8040207031007035684d00700c14034042008110088040c0d4464407071f100450414540011103034121109655900903e9003907444072075180000c48402c69140c0f0041042a00d60344106500900420054803410545810a81c002e402d59682002840070185824003c2007011000d540c486c500b046124580415955001d14118003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96096915 1250 96095665 96095687
    0x9060c15060909080901090906050a030b13080f0a0f050f0406080702011506020c0a0e01120311030705150f060307030c14010302120c1b0106080a060903030b1504050307211101 77
    0x10b00d4185031960003031040100040011890030303a200c00b60f4550724181032044a005001c0c0395441a20950200f021030802090a40c0080400e0382e00020540305030f0b14044a5440f000ca082422140890940c107440c1d04112250b0030f00c910b40c2807040c6417280f401c03a181c0c2c2038400e42c00b4078418000450b010035201c52003580300b8940c2d502c0c250b4480d44600c1d254030021355940180c19009100701a0400d0200381400c050f51560b0488100c400e040301c40000300d50f0140c490462014002046100500800c00458020040458900340c1880021f00e42e060008116540280090030140240d0044404000154103044a4001c036a9160015015009048012006482060f88801002c160350040c8280485442d000708641120f2405d456001c90382c1a40f45802c0e100c1d207201e90301c1d803a04442c1c0e031701007c02c0e090340004410b03500c00c2c580014103d40e440d00207424100380c60b001c00c004000115050249081c00c210f010003130700310000804002c03410f8000c5155006c001100080110441d548000c0460b4003607040851 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96098165 1250 96096915 96096929
    0x20010b030a0b1017071715040b0415140703110f03090304080606011103120604110304030c031b0b01120303060803040909021509180c1e03060a0609060c1506 69
    0x803041690802d05186031050321510008100e2200010b200d080c14581080074144130710180030401d1601101003003990016409102c075000f6848541e0724852440e041070f200318400c51500c161410982802c13148401c0118418800600c0d02120250300d00c0310110103a0300010b81e2501080342e0740c402c03400d405035000e009400c8031540e03c01f209108129801001820948280c0301c21540955500c800460b0f019030b0a01e1170201d00d070410482d200c000074191100c00d600c500040d1000c5a4030110400040c07690780100c50a40020310078403030b200c041552181803284c0309024a51340d060013000d50b17141d076190310070306114401c2d000600e03403854010180280c00c01c000400550054030303104c554814004025040049040344501e8481080c00d05041e1000103036003140f40050301e4030044003041c90f240c805001d00901172808140c0c0512040b402c0190030078400c82e0000480e0540d03626810010f080c41116855a00400c00b403128800060200b15803101701141c9440c2c00003010300071021085210720040c84550803003d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96099415 1250 96098165 96098173
    0x5070e0301020c2104050607140313091506090f06030e0f03070c030c06020111250501020d060501140a1b03050d0504030509010215150d17120105030f01050720010b03 73
    0x4900d090080340130b8038a00001494104c400c92110003a4040b0300c1a8011a40d1141c408e211030030220754041d6040c1d5000342d0210446c0c0c03501c0d48008200c5e00c2205283d0052004503142d0080410b41002d000707000c00104500e0405403003290030143c8100e9201064020082010340d514111008810104440034021494405503035684c2418181886116203501003522160100000069070b50320500c0740700040403a1041b003608010f0031000c81014032003001c12424000d00c1e520100c801082081c40140103414104000003691468500058020702c04068000b03440042400000080d0740c0003079500320142401e02c600312424550b071909454034014020400c0a80d031801c82000105070300b00c4021f1094003026004c4030000d80380980010404401100e04000d102c50395165903009043c0210007452851084e1444c0e0b5224078190700c841d01d203801441e0707442101d42d92800104118241403044854080100340240308a2a20100c00340540c066509140180006070301815902c403820f510824035000010155 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96100665 1250 96099415 96099427
    0xf050706020409090507050307081203040b130204060b0901090b0403080f0a0c050a0305090f1e010807050d020f09040b100f0e060f120612010c090b07030203451305070e030102 77
    0x42c46e0780d1507840c00303814064410400301040c080c200146002d402d120b041122031560340c46503207107907603c1c001030709001c00f18215840d024016501c80c040e900c05405030b00341c207135100c201580c001802d515059001011080040000b4004500c05030308a4464045e41020070760340e0801039000700c40c03000c1d2000016046015400701102019880002040500e102702c844045200030f5400304a0303411007280d07003c92480211101156594054000c0c950f01800c2402d04c18201070510000c44141e900c00c401510a40c9c8000400010b540340921400d2a000d9050300c03840d2165040c54000340040301da404400c0309200c001c2410501e55a511811a4400484142e085441c3c00b0780070001c843c0800107482c5a0320552034540715900d0078a0512030041919280d60712140704910300003120b5040e5118510550450008010184007182c2d006a040003100e4183c0c400c403030021002c05074000581c454000d120448250074032003074507030352055600d81c2c40054011000640da1a03042c0140d400c100c40211040e0107500200705 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 96101915 1250 96100665 96100673
    0x3090a0c060c02010e090f040f140a03030504171207030b061e030402010305151003050a02040f0b120901061406090406210203070e04020d0f03020f0303010e011d070f05070602040909 80
    0x8403070700640b003030321703880300040000e41004440e034000c450094401d11803000140100f02121ba8a01d07605002c0d110504140154100d10740c01d00c10290001d40c0800c5e182c40a0008200e022940c00c1c2c048502075095070f00b4010900c0c0d46081c4100040d20900415480c3d90400300c070740c0c1d40c00c0d0881e0303684c4e14401c031a4500c0c610110410314650b0011038080c2e001c0303450440054050f03440050303035a0792290700038001d010400083c0400e40c0141341c06070000f03440582c244000704640072000155005407565080164440800071008141200002c1c1850b62990514200300702d9a0903440700601940c20440c1d505403211a0240810300a05541d400682c1400450b182c07a2000c9180a4000720303650300903400e071000652501d00d070710500d18050350020741080040f030880c1701207490500d40d2a00c05219105850f00104004805803840d0820303002004060384420041044001c803284c810440512201404003070f01d0042d80141c0200207140b2000140f107400100c243c1005095030480e409000d001400b0442c098484c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 96103165 1250 96101915 96101927
    0xc021e0901090c081302130c0306051903050f03040f030209062806030605040e070b090d0503030106020607030605010e0d02060a050903030706060911041202060702130513020103060b040501120203090a0c06 90
    0x5000110b1000c0b008501702c0001c24000744681134001d0182c0622100007114040103102074003000080582c0d41c01d012034142d0381c035502104071800228050003000c1c21400d20038200307924059810b403150701c10882000051707811401034080780d40440703076540c59548800106510303109107864905680c1441004044910341400c242c0e06544450b54100209611b034014030003100c04203079802d941984948420000a0480c0d4004c000030324000e021045110b01c02c3d42c415142d50400c0e0440d03000f58005d0b40801440c0ca0341441080000d0100b460302d00d1050401e500440c0740f00c0b00300790707029004a400190780391140c2d01410440e030f4000b130041c04680ea03442c41802d200004080c20f0203064407050401d001c0c501b8034099201601c0a6032815403980703154025550070004e00d5403141c070f401c98100360710800307a09485000c0d10600e840784030400079403454240f15100050850702990804681004180010300c11a40d12040c5081200e440307000043e80c030340750344090386c0c640781c0c4580c0000c0100c9000800031035203660100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 96104415 1250 96103165 96103181
    0x50c0102121501050a1215030804030b0f0a05060609100315060203070b090f031c0b09010b0705070509090322031202031306020703021f0c0816030e060306010c021e090109 75
    0x3840881402c1d03901004448511a48410400103045044080e60343c4409a110411b45003000f250480701a60b40d0307071426520340065000703682052180c810084800110000c007544071001c48003c110301e0ac0e01e90300255940c09401001c5000b0b081c5c1d8550104424041e5202d680001e0341400e040000c0d50341d0b124000d41d40d80c043d010440f244050f00c0d010524011000450039200800c0c2c07000346007000020000c00c010001c112480001e000e403210240b40c2d132070b2140a15079001e003140d411459602c0640c0d04010307180241ca40c0c8803a00411b800f0040000c114004420341b20300044024410b141100380c01a0017286401c680c002401c1c02d51040c0064500c00e030000b0051148001000000c04125621a8140d86a83e0a440040d40044950317800101a41d0500900e41440c5030b603040c10b14160159031192241034220000100d40f802e4400000002d158102c2e2014400d200e08461039441c6107032120008040c28003080c0000e02800350386c1742400f10008554042d010085c4003401141ca6076035038118000140c802c1e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 96105665 1250 96104415 96104431
    0x1110303010f051215070503070302070b07080a0e0703200406080106090e06070908030301090908270f0307290f13051005120106050313050f03040602070e0f010504090201050c010212 80
    0x16444495881342d010a50302d0304150b0000f603003c0c0542c0c03514401d40e80c940c0b00500580c00c041d8204641e0002031510100c4030b000c0c1e0195074500100c3e107090303e070034002c41c0c0314003c541c41181d0290100304000340454141c460340307000c031011030342d0001e031002c0c00320b400340c107058010203415400d0100124803102345900403100500f00b042102e44907200c081d42a01c01402c580034042d80380e0002c1005208844050b045020201e2240c07035410702e040c05400d1541e42c08121a1460500015042c8002956142c91400c0881c821401c034007a0003640e1800000f81e6182c80280d10303100300303840e1659215400c1203104080c2c5040c0c98103040580e607290440c101d2044c5041c52805178511614081e101d8600c2c85110341c059440c3c901c3d010405140c242d007010b0042d40c003500000c000b010b5034003001e5000000104140442500f28090400940c0c4540c02d0200282c100980340d0044507001d1061307410029182c0d1070710384060448000b59070001c0c42807518001291544100c22025110f90300008002448800c08403045200f1440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 96106915 1250 96105665 96105679
    0x402070f021809280b070816030204180c05040b0721050403150e010605030307080c0709151203020c060301030b06030d0e0a060305090304030b07170c040303090b070201110303010f05 80
    0x1d2080391802d00382e920400c181c3c00114410361001d24044034941800055000c442144905e9a0321422080c0480c5d0040020f00c0c0c000a01c0340c100d0034070700c8070580340a15003019401c007410f01803810660f12069010403402d541b1120203896050050084074003a007403a6005a58a55003800d000a031303c2d00355001810440c1c049414600354501c40c2040d80c0a0b2548010100042e52017803200202600c480700c070016003951381c2d5000041d9a5030400042c07204600c5194240d880d020048401c504083c1c95a120f00100c5007401c0041910700c0c402c800c900b040d5108c842a4004a45c3c20b41022881c12540c81c11907600035200100120500883761401743c800c04044040343d45540d03c1c503508442c2a01c18580003600801a85024403015000340c201c55400300c0000b08a0f400c5c50394a407607001d02850141d402c00c0c042100c035652800400711182c9015840b140f01b14580307103040c0c955503004100460600c15100d40402c0455280110b80c81040904062240c070707030443c0d8903543c5a061045010891b84a00c92203810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 96108165 1250 96106915 96106939
    0x40c021203132f1507080912030c0a051006050105031603021201140405070306210609080d020702031b0a0e06010e0406060207061706100305040305160302070f06080f0615090402070f02 81
    0x40c12030b44082101340c44071001814051141ea5540054100d404c5460344905a00c0a0819581003003000e014044500390081201850070b040c101d040484402d41c100c4035500344402485103980207002c40303400c0380a030282e00c80410184c200440090050f142e00441000003003000140c82e0425072100e00c1e00d5142250100304644030550107504462007031280d00440302d2051000c0700003040403605c502c03030107006500200d0a840c0340c2d0f50360010340c1d000286007807400e030740071400300302f035081c1004031985400c400340001c02e0303110840c00007412103003907441641c200708500030000e1807a0344906000c00007007501510911809480711341c00f945804541c01444001548680b80340e400500c0740a075240a5100a0070042c0502d5101c04202c014040040064081c01403c0001140c92404489042c13002401703a40030b0945142012031580c064074050780507008100400c410b000e01103498800040d0020001c480d44005050045500c83e0140165111540c1c820b101080c0e00c818000c5081c20f40404078421140b07811040e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 96109415 1250 96108165 96108169
    0x1060302030601090306020906040b030f0907080f1002031e040b071b0213050a020f07050a050705150a030b0316080304081e0303040303091b080a020f040c021203132f 73
    0x1001c01c444840c00034482100410105120343e00070140c1c0c440103045285007945900707038a5416401500e00781074100b4100300700b02e500c000074001d1001600501e0058812031800003032a1b1780ea480d40d141110342d4550f0000128402c82120b0306030005e24011a00c4000c11443e0504051040040071180440440c0d441869002c0c0d10f00d0020600d04119801007000b00d1441001545400901000b891415400d0f030803c0b81d281009154000341080b54401d0006000c2052540741840c107048065010714060091182a030300d4042ca600103845440a252400094000680380000d1410058601441c5d8078200e18002060514001c0018800d54141a00301e41d488180c02c83e0140b5031021410300304803503030404c1c000f04000910035005410390b14011362480c002825003407051100a001c0780e0010030342d58064000e620440c00c00602224482e40c049800300600034103c1e5000c2e4503141d603186405a249070000c00504903a8459400d10480341d0851070020714640d07050740c41c20307001002400041c0d02859080d270609241c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 96110665 1250 96109415 96109417
    0x1060e0102031606110723010207150207030306031704060e100c0311030c10020a080a0b0303030a0e030f04080f0f030a051b01240603110c031909080d0905010801060302 74
    0x80006900540c9000030140325048503040b80c84046400b1615926078243c001040000b4000ca00c1c06065447c0c50607001030060504111050a044002e90041c003c58000c40c40038008801240b0303a0620150340ca405c10b280880003010320742c0005182e0548a42410382546189010b04142c0b840c2d0340350b120701c3c503c0040400914240804c003860000c0c1c690303101d900000340300c0c800e54000f004448040700d0400d02104072060070420f4800000c8107842c0d0109201e407080d5130080001b60090340701e403410485030182002180c0c892200401741078071745407654241000d02c101082254150800f0403c065216030302c0d0f214050310303500b50f07516024651192206500b17943d600030040b5040c3d040c9585a551804c09010701c0d100352612404010303003044d580c8083c0c01c3d11f0300f00e402070328107200c01103035210590a5040c5000030302102c0e010300280309500b0081c010840f01407000000c0f20f046905091919480a0311168115241c8178281c00c49185c40c010403080c48111500880c03800c0a81e0701c00d803208880da81c1c81c0c080c11400c17 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 96111915 1250 96110665 96110687
    0x70602070b0702100c2f091302010f0207030b010e0a050c160209070e03011d28080304110a0e0a0c080402030a02280f08160803040e100504090305120106 67
    0x107240002c0000b03000625228030019020441800d222442184c1901c68a1030280c0d00b480b80b045580c2c2c00190105003d640c001d20000079401269010460304065080803400a509007009061190f0758003407200c520300070801c40c402140d0000b031001407903071500481041100146c1e03116005a08000108140071a6442519006010903a540000c6843c5808000404602520510511408254411654a081c0a00c800305a6504020341d061411550300314034001080380e102d2480d01c60780100507201d00345001071116098008100d00d0b260385070b90a00100c90f01100b00919400142c126001502c0d401d440d952522910098900b005800380503039081c2c8185a0843d0001e43c140c0002d115600145441018604044ac82c0140f00610072003035080085200c51076000f51010241409040148040c1042041c110310000301000071003a150002460762400742e405030044c08040b900001d0710802031500000010480284103116200403410080c00036444030110700001400040041181401001080030b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 96113165 1250 96111915 96111929
    0x5040c030b1507020d02040c0c020f0306070504062114070216030c06110a0501020d06050906030304030b0615070503120a05090106080304050607030903050604030509090906060a05060f07061401050307060207 91
    0x219100c02c210b4107040550200da03049074006100400740e005600e4a118003075160b038a507100c003910220710740100251200d0b21050148a5400082004102640304080e40c0464100341840c0010400c40709003000310301c002661801d06a0300e00b0182c81400c152030b054403802601141c0076140703454509a0038110180860102030078001c0c810504201081c400d880381e031441248007041e41d200b809246d45076800e82e400040c2542c56241c640f48140410f18000d520160429400c60045207813a18603a07400b000c0c800010003e91260100c2d200f640082c200140803501c010380c2c01000c0d20b40d9001600c50005001c00c00740c4d8800c004901d4038001640c0e04105114031004c1ea1a403000440c1030074941420080c09503c070030000c40030410b004e6030000005d8010030859004a12039103907282c44503500b6092240402004148000981c000d00900c0f0554440f05250b0058a10540c5c3d0540d641c40259a540800e20848100501640c54012541041001d03000814183c51084094640e410765a00080340d0311880303409406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 96114415 1250 96113165 96113179
    0x1b08010603170304060b041a030706021902090402030a0b1e01091415010509040e0a0501050609040c050f011e0f02010605040902030303010920040312030c080118050a0e1605040c030b 80
    0x502c2030718150701071588544915004601c150303074131011409960324082004204003010400b45490b00c1d0a1205601520241c40205000340401065405641103108041d0152000ba4049401d42d28180b2448c002542c000341c0404560400300b41d0710080d070003108200f9032044a01400030070414000d005020700400c50500325202c6844284e910510360496421460520000b00240000f50b00c2d24000c00c1f03083c0d0740e01c101801c0c1c1083d403800d1180c03c4d070307400034410342c0f00e0303035050303081000082400ea040d9050794800d8401e2800c03550356500580311003500801c0e449007030708418071004040b03522503d130300410302056000b40300c11641e503000e11080d50680e600c000d506400902c01400314414561044c1c0e41c0c0c00e0302800c14100f0070281420315100c0d030301940003500c0c90551542840030307240e00350203041054109890145120341c5440601c40307000e600412001580b6896101040341191183c100c407642020316002d031481103108500000549045106140c01142002c51680d000d50191040e00030700750000d01070f0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 96115665 1250 96114415 96114443
    0x10050a17040f1401060f0b03060f040204030807060f02070f060902032506030e12040807030c0b030c04050108100f081e0d0f051b0d05091c05030f1608071b08010603 72
    0x200c1003d03881032000540d607443e00012451502e084040040480398480340e80d030b05180083c84103400ca00780c045405507004001c2000081d0013841107568140c0c000308001141c110224a4002134410060041c01002c00c0d5103c0c501440341592040d20343c0c0d07100310704603041e540c400001c5800c18541c1c2140100d04810041c02006482e0084d08209041c14081003510ba0300b6040c09207030b140d01d030400d40007000103900c4080288200401d0b01e9480c00039281080c03c1c0b0b400e501c0c03c02120141c6114901911b0b04000104010502c1041d0310350b01c2c0d40190880b14140c4164940f58641c280d42e03248004081d08905c404855003034000c0101241c001c00c46612683c07440118088130006440591009001c28510030741c100c050207003100c0910121f00000200c1c2d507416940d010301d808120441c400c141c1d0114080340180c81000001d4800011101680c0c0b420031102c0d103a489480c3c08071304a200030700e4040e01c0f1540c0040e4030030800c210300c0005005042c01d145603036910f80e29905900d0803201da0f408010001c140030410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 96116915 1250 96115665 96115673
    0xf17010b1801091802060d0506010906050702060307030f0f050711190507031713080c010e0f01080402040e010b12060a05010e1b0315040e070806061020070510050a17040f 75
    0x9130030216054400c5110803206a800b041c0664482d2007261090303503492061000c950b900c01014802440c8919165007031a002c1e40000f9010300c0050310b110b043c103588000c880040e25180c2c101007108100b88004001629141002400700b4155040c0300c0443c1c0140440e00c0400650804000a02500440204011405c0d60b44c2c04650001100da112080c800500c16812070200d11000304003c5c10b0190054010905c0072000500740000301d583c1c0320312450980c000c40040ba6409850640e0103070301100c021400c0c0d0407800040d401000c0742c034042600718140321a00003c42c00006800741c00307543c00030410480c60781c2e6030041c00d880b4001512280e540d292940c02c1c203400c828440010356004003010340d2209101d580e0400040032203201b0405114107800c24002001580300601802e80e009806aa02c00034603141d81c90000c00c0120200341d0b403103075158500d9000310400000c01c12003001d01005015544414030a440c05400c54001484520010741e0ba4000608524040d1011a0180394080d014100100f81651 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 96118165 1250 96116915 96116921
    0x1407180f05090403050c03071b06052812090812010510080c0901091d060108092107060608030417100903080411012706030518071206060f17010b180109 67
    0x40143c080180c244400806c48600340001c0070b05600c44c07443c94401001c4614044107a04403907008000344041404600801c10348000c407030304e400013000c858201c0c0303c104040546092200394858040c0500e44442c00080000e903800131f0400c1030001544002580e600c80030084a008400303040c1d80060403010106032a225450080d000440050402200f5141c44500140d0307951641e000880341d258585090003820f581202105070089021005030001034504000703103004000d1540c60558515002034080203000440d44003c3c040d1002005403983c07036944a840d090b0054950460001030b00440c80044d140b068540708076a51075516898003451036a4603268020342140700403440e4180803814900840300c00f10800394000c4d030150244e4020b40d181c2042001411210010b207241007202c0e6200d51041b80690000740d0104461000c07079000303404407c1d8944040a028560706c03002540d04c803100d0100301e20001241541c00d0400d408020010f4881305020403850080f141c0519405040400043c0140c030401e030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 96119415 1250 96118165 96118171
    0xf05041a01081302030a03030b040c082403030f040e0403020d0504080615180c0307021014060d0312050a06150302070b0402040e01020c031b010501060507030203040b090d0203011407180f0509 84
    0x3c00e15060711140c0c01082c2403000700c00d0128002591480720074241d07d040c2c0301c0c03503600150f1031404c1c5165281025a03422039510b104118642031a0040203c4a2664200100c9440e040888034403503c550741c031515140e800c6010742e4110054000c00c0810000789104074140c0b011030300000300801c0745d51600e030104400740c250201195000058200b41090482d01d400341d25008542e0307988602d50320f1901c60030003800e2024100b03090003030908151901c4610710406040540022040354035508810451509480c41e994000e5400001c03030a200c1040708021460f4040d0044a0034010005504401d0803000c40c100d04c00c00703200510700c03400c0794003050160800783c0c08a01d080482000041c94503444041c0d66146421084c1c03e074a0710030841141d000300190a0082038014007041c1807160614001d6075001e03449010b03034080c180c00c061000c5450b02e40d541d1820010070203580c005d40204608041030300b24140c4041d084840c0000706202000340407a0140c18032245040728024405010040c0c02c1404111010b8409 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 96120665 1250 96119415 96119431
    0x114030f13110909070f0902040b0403110103090b09073003030c02010209030703150b01030203091203040317070302030f0105010f12110706140f0619060e0a031205040f05041a0108 79
    0x500b080b01c1030700e852045900030440c40004010b085d03c0d04654001100d02c6400403400300340140810020503a1082c02e803010b0700e50110b01a52010b13003442c012002800d20312009428070200c9403d1048004c130225101d0240d84051504941078000030044021030900c4805440d42c18514039507900200380b082d80481009032080c4000340c42e101119000030b10348038868005403044c01103040c2c4200820f41611884601c91001c7c2019811460444e440545030080b40908103901c03c00000003178100351044896100201c4140fa01c000c4905040c100140250070803500050b0015040001284ca50702500403841080a1551058a0195000d030700c1e4001c0c01d0500220840c3c07080500c0000c0000314030b8000e10030008803a040c10340543c5061a008020804090003481c0070398203039541c041030365101d0003001c01510103505002c410810030202041c2d170300910394000b4010540c3c100594007040e034400d004004840e444421080c80b41d80f01da003000100c0701481c0040110b0054489160b400b03501400045500c0681 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 96121915 1250 96120665 96120683
    0x151101020a0c1101110304060f0207090b0901120c0e0a02030601020c030a020609220905150a0605010509060928050a0807052b060e03031e100303030f0b060c07050114030f13 76
    0x1e40c45c0041d03d10b40150308991301182c480079100303403001c0d41004010000c01054400b48103552030840458086d607018020505c502c0e2011160f1000c0c000c40c20030311030042c480e51100d01010320b03003a045c071002904150380542c010301070300d05200e80b5450005500803d0a400504252030154080c0800c0000400e0700560440d2000c54404600005084d00c11080024000c0c1c01070024401005d845a0045030014074220380c5610345036003448683d80c014240d030000c00b0165a1243c0e5055114001a4038800fa1550148602c0d40c41851400000c00102c00408480302950300351109901c0e80b1a43c0d8031104140034150300480700e8103000d4546603c06020b40c43c11001030001d44409003442d1142c030259181e4107800c411580c000402c4c09107000c04a00c4c422240b08200742440b5060901c1514501402010310001e000c01d9181c0c4201107248001ea4080b18090a0040545076a030481c0416a0748507a1244142404502140e207950f4500c14400101e074800d10107411401410b41d00d51840140b08038032a81e00f61035a1907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 96123165 1250 96121915 96121937
    0x7030f0e070305060a06080601081b011205070309150b0105160f021f0f0302160311011d07050f0f01080417040906030302060a050709120303050a0b03010501151101020a0c1101 77
    0xc00d01910010b98001c5000d0701e828600a1030000c207031105e940c040c540301e600c01c0c40100243c84000c07038050780c5407140c82549410703481418012502810301c0c080f00d080640c80c26050000c1c00350141c1c002c806031480341c2424040400a901d0040c202c90234a80c40c1c80c0450020025500d29100c19008081d41911030425403d091010742c0108003911a46184801c030451000510301c03120360840c108221900c03c0307150035480d102d402c50300e02070001c0894100030240444040c1c0a64181002e4011081c1c4500f00309a20081140b0400640e95907900c07407207544e0203580000019601c6092041c0008840a01038448640c47d4545944010600341c2c2610081d03a8082c0521001c81c442c000c500a040056000c0d0f8000d10403401c0c9090048102c40d4082c2c90582804200c0c9003c000a50144034100380c0e454060a0005513070740e039035124001030940240c181d50f0651034440041504114507001d200c503e1110f0756002180d80e40e415089080348607500070500400d00140d0040c0000c1c03c6480c0d21048100b0601d80005c1c0c001e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 96124415 1250 96123165 96123191
    0x112090b0c1b010504020f060a020c130f0e0102040e010b03072a0203010b0f10180b07080307020d03060b0412141005221104020c0a08072303090907030f 67
    0x200007a40e000e682004000b604407108002c010407038104900d541d000308003034105580013070381405c1c4c3c03000658000d00000c10f8246c0d0503802802071544002d070242001410b448c40f0300e400310003010100d4985916600d81096010350f02c41c14030a4500340c2e02240c0054510f41d003010b030348102e6030304001c00300d0080044502d44d43e05e5000d20344080c0c0701c0d2080c0501c8441400e103524810582507403211000e2a005036400041d00302103540d10500300200c429682045009900c81150050180500c0d0300001e040300700000fa40005c02c43c004000f54441c0c00b040c0d0170394940520640080b01601c17642d00c01c4d036007421400e000c1800718004256114440da442182080010905418a02d007460100750b240ba10741580c6804010340010b4407025410000d00010081c00143c0e41907480350602c0301440c2441d8081c0c2e034046515001908204100005580c1008145440d92140e00d0241d0020701ca403c803280000c01c52200202040c0d400006851a090004102e0b801d95500c41b0800c60090603006200c1d5500c42e22440416910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 96125665 1250 96124415 96124433
    0x31103030d09060b04050109020c120a0905030303161407050a02040216060f05060a050102010c081617090c01090906030b0703090c0f0e011706040302070303050d021306030e0c0a0b09011209 83
    0x400d03c100e101088000c0f07004204011a04160301006400d40104881031a042000c601082c5811040d0109500e50807103110031603a55100303422140e05803000105001400541600001640702680e480f6916020301020100c101c0c05a00070040c480c1c0c1c48904600010302e406e0b0060043c80b40b80f00b4200c6c20700c0015407203e10545a110580448140d03540b0140310f418204a159000902000c0c0024401c0750302c00701d40100300a10041100c01661801d40e10308200602c110741c070064200003600c0311031227402c013404640c2e11490036420032404031356520800540c014550144500302c1e0340024180d003950b076400d0016009019404011100c00c00c4944003c202038081c90745000c068601c403200100a58140380b000c00c81030036040300c55007440c0d00c90390070080001d0340040c4800680707501d072420030707101c41400c40780700040c4c007800034021898010a0400b10b485036169002d65561915441100d9144110800b44a4180039a014564000c041044140c545500440b0b500a0382c0130f0300f6500007984261a202e030740c50307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 96126915 1250 96125665 96125681
    0xb06180721020711180c040302090604091712010e04030503041101200f06060a030209220c17060a0c0e0103230705121509011a09040510050a090203060604031103030d 73
    0x114400200009480c5c1004208200b8200481100044034200005c25130b4590007680710081c4034500e50400101c681d1038603040807110300e90240000e8010030428400d20404d030801c903541006c55102c4000024241680510786001d90b0b050340701c0c1451903c0300d490b00300c0c20445140c601c03030503c603140340022202201a01d90707030795925600340500484105440d5081c2007a0020b0032041c4210656041400541e45286032640c005104400f1000e1040c101c60b0301d0340e603404031000b0140540c10b69410010302503030a13140030a0303403590b401d050b581a9919000408111244040c6400c00102c44200c040d9440d4045d43c40031500481822101b03011029040c050000c45604807060400181c0210740a03a284401c0110300e9000b498000b4050000328450001c9108050f0500c40c484800c006a1443c0e030813040c40b08112202d513a40644280014908412001102c401d20300c10a8080c2400300c8001404050301d100b964054200201690300c1c0c5459521415442e080c90720348030b035044c042000500204034440c419011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 96128165 1250 96126915 96126923
    0x516110c0a0806100e0408091c0803090c010e0d0f031803020901090c080105101409010903050303090a0b0702210c1c030509100504120309061503050a0b061807210207 73
    0x78084c40d02901c64589100558001c01c403400403d030501002902c11000d440700104180d85040c413190001540c641415103c6802810080e80001404000300300810f90b010552000e0726000c00d40c101c00f01c00d00550070590b402c00b8101d6000600d6001c000380c41044081843d030002c071000001c03152203800064004c4020ba000d08441c81d95501d11955840c0c020800da8010a8200d0344541104019040541645062820002d005034000781000c01680910399410246401504072503c91905103401079440108010a0310aa04943c0c00151443d00c00a4181407200c010580c525a141006446101507007100924880c140a01d0001152004414050b1504c46146507030110302c90401d030085500304207409003500d0b681410001000041800426070a1000f101890002009021400c0400080a00d400f0580740020200b0000050003000030760401814010310324030070692298030030449110189401502c000d62050001290580036004441081203402400c88800c400107001030120303404580112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 96129415 1250 96128165 96128173
    0x2090711030a030516080106020307110303040306060806060301150b040b030429040b07080c03061e060d0204141f120b03010504081c06051c0201050c010203011214010516110c0a08 79
    0x1203003104110445c245001e40d0030040e0311541807a500035160b00c6030500c05403400308821020a15610304000b22002141c101c0e0b004c004a07603c8017042034903030700e05940395072182d820720000c0031660500303140e64411101c82004407440c0a24050403070019403c014070070788450107000e540d02c001004c507003a94115030690222050091400b41b03810101410701601510403c040b11007001004000702040307030340101d0300311214402030284100c00c440c80c030304081445400140104281224010540184c01695200030000300192400c40a00000d1700d01401008941151500018880c40c02071541c520520700700100880c84035001d00101e401c0d2401928100c50b00800050082060303003503500304a0b2110080c80052110300d180ca030002d113007410120103031112801030403851800c5a0042c42103c0400c100e29000350740f00d607518820914608850311040d200401011000f040000040c8242441052222803880c0088007076041113601401d40e0183c0340640c4241700320744200707980700749541e0010480303d4020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 96130665 1250 96129415 96129421
    0x60d020a1814040b03071208130b0a0c02010c080c0a0b010503101107060c0c05010c050a0e010518060328051506030c0d022b090201020c0a0302011211120c040f14010c02090711030a0305 81
    0x4c8546009c81c1d005003046001801100354095002c848145050380918003081941182d00b00203031a44941e0354240320611400310031000b0441402c11880c120b40b42141950700a00503102001c0a660b40d000f484164542c0410031040051103562180c80c0500451800340c115005654a05085900c000b4110000c01e13404604094026442411b08080080a2a07e2810480400c999080145400000ca441071030040b002660a4181d01024040d035100d00c4484100c07445988501030007408155000f0307490b1183c07000041d4450170300c14101c030b01845201b1aa03514000080c2d41a800a4100c6e241e1196a02d03e201901c03a12015554040c4841c424040c0c00000c28422500c00a480d041050001c00e014a0a1050420250ba041442c80656504100010131003a508851080c09031042c0c1c502552080101014800d903052090f002d001544c3c2094090b03040d82d5110121000d210300c000701c0d5180082c000d85500c00042c2011140c1076013241187c1440210041810440d6045822041100001a69030420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 96131915 1250 96130665 96130687
    0x2a010605090109062108130905180307050303070c0c03080307080a06050f0d080309010e0a050f150c04170703080a12140f24060d020a1814040b03071208 67
    0x1481c01048820720401c5441e1603d2003d10f5a401c500100e2070700308045217940c070b0501081c14103c07004403080c0750b262140c2e01d440382103c200608050383c2844440030b11004400c442c9000104a40c421f0b0b0b0000d00440c115555400100c5803c0c0c40c0110440b036114480c0d400000080c68040558040c0e8140d807100c10607880c0035141e9108175036a541c003032480340740c0ca119446c5050b104e0080046011760001c400c20f40d207903900e05103e40903040d880c64091180c411003041d501440b0001c00c6800340060755a042d214080802c0718208441e0806072968601035034100b00400051841c00c4198518040300000d580c2d42550700d4941100c0f603000700401d0b401080a0031607419000c0c9191198441c10b41e001c0301c1c0a00c090030640c50b030002c1c1110013404945200000802003110034a9400740e800c004000600380780c0c0d5003ca90795050080d42011302c54030003080b0507551860310f0419185001045c0e406170100030520700d0240d01040b019001403080180c141c0100100807602803510f104102d001b0f805852215078400890034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 96133165 1250 96131915 96131929
    0x30804080d0e0a0b07060b0a030503030402181e0603010917030121050606061e0c0c09070305040308040b15060403050a020f0105070312050a270c0506090d06022a010605 74
    0xc00e4020000c06419000c410396418201c142903415400004d51504c9440c0340c4680280804a401e80e40b19050340400001c20000100840c499482a00c682c5410103900703010384610030701130707440c1c0201038200c41c0503200100c40702503200d52080d001030000c0340704034858540c401c400c6120500c40c00000c0c40000103100050054006034082000c1c0031128100b40d087d42c0300c1d0303501c81d48040c100d50301c111000942c00007000344001d9840300c054500c7c10000e9580c085482003541e540b503c0c0c400c1901418a6400240e4050f0107031145520868068440181d1607070380381e4030841c82210052aa0000010382c43e00b1004a80310640603001652080d07005001c0700070180100910000384600207410810100006000250711120755041403290002c04500c03901c6010006000d0900300401b10a600401313103240500e60b4000c0220303e80782c0c1c05610303025119034035141405010301c07a0805040d04403004040110000702168000e041070701d10700300001c81861070200340c918071030070f80b255602e00d42c0c0d180c036000d05c56031a02c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 96134415 1250 96133165 96133183
    0x606010c03020309040e1c09050910030b07030c02031909030606090b0a12080d020d050f010503012919080a0308130f021909020d02072307050907020a0c03080408 71
    0x400c0080c015036059800955910420801600541e1a1282c4540c10707001080b170001c4d018055450524600c0011000901040d46480341c0c5110b415035401281d12241c1141c0c0e0324044c2da41018075040700e60b80781c080a81c050020f11450604511040040340754980c10b10040181b580e540eaa210204107245060a1041c0e409540100600c0351400f00d40d072040d560b03443d82080c11600301c03001301e8113840c1e11400c015103140102183c4030611800010303042c6110059070b003c58803030b00032003912110f1642c9640902d8200c1c3c0d0500600456080c0040c104914150703151011a00d4201c010714a646a81005440700c034441d0465110741c28560120005500701600031503613a901404446e1028485505030721003400d0704480100190007501502600101030704040151006800241c0c403e65480c3c800600d480000e5001c4072083c4da02c8280039015a49041c8240401c581e40c1c0c416070000e001d41030600342000940d2402600010561207000403c000141c0c0030390307200000718004c0404030b807038900c0d05601505151245e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 96135665 1250 96134415 96134417
    0x306090613080f0d051f0b1b10230a050702030301050d031e021006050102060f061002070e0403020d0906050a020a0803070c08120106170c0405040203060d1208010602060601 76
    0x1500801550000015410340d000e000744003081107400307003402c1060483c800c1c42079821201c0e400182c004500c0c540350300240c1c0614070f1166480503c255150441414a483d4054640313074180c10000050303242a01e900240882c0000d009450b800140102c0820132500000c800d060074a0b0002d04804000382038240041d881868410180039502d1f20200003902d9120500407203104041e04021101498400d079201d142080e21002c403040044103005000c0d59417011407142c080d040f030412401107995480401e0f0303036010700c0d280e0030000c0258440750104030100c5050784030003003140300b0510001400c28416850601443c003a401402584a8408000307041001c80e802040601c43c0401090707803001c1c0d002848002480e0400401c03034403501d9006044075005000f90001d040590b02180010302c034100c00460324101c580540f5821040c0707804d010400d0014200b269507849250090004104904143c0c008540c40200107010341c1101d80c1e282c1d29903c45040c03260382c21002480c600018414180c042107030030741280003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 96136915 1250 96135665 96135673
    0x303070c0504020f0403050d0c12140301140f0604240509060909090c0a0e0a0501060903030c080a03060f090e010507020105090307020d0c050306071101202508030709080c03 76
    0x415150810699a03601c03a8900580d40041c2c944803000c00305050b0f60141d50720405407155450f03806401031032820009030030b444440e08a8801d59032207020351840403503090030300302071411a840c105e40e0001440e0000f80c510b400140e50701c0d048149544550003403000e00010600c413924200d00c441050801d0b81c0800003034003400b404202d020f4a555601060798000c080894200c031440d036440c540c20b401c0a00750024103400c03900c94a40803a146560b090014458000e05008001c0c0b44c0c4d80c1c0400711003000c00c620014010440140b51400461320542c01091544101e05000c230b1015900c070241280741050354802e20b506666450801e00d4480280142e6030000e6581c1300a0049051100e450380d128800e00304001d2162101444090802c00030000180040500400b92616440c214202803c02042c8445840141d460505070310095a607414500240482d852595800d00382000c41c0400e10040c030079040170410801400120000d244a80194811582e950f5034405441c940040140b50684103c1c006100e504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 96138165 1250 96136915 96136927
    0xd020c07180e03090d08031302090a0c03051b070f05071203090608060907081302030c03010c080601230d0f0905010f0c030f02031b0702061c050402120f120f16050a110303 75
    0x5100f500c1d000170035810040403170303507510f600c0d074610302c9880d014100941010b42c0004003d003106841d4001c5009000580b81400f851340c035841c2c4005a940702541000c14004280f04000c08203035036121801505115100b00c030b41e8580c481040704140420b0900440005e15800810700c5403036403084900c0e400c881d00392070748201d90070010f40c064400d03c001010324080312244041c04081d540c080103038040e80d0350040c008202009544100a00503e01121054003082c00111088669410724502030341d820740c2c004505040c00c10a255044c00b0b0100090305200d9152204288000300d01c007803046030b100c4140e02c0380000b40052503042c0078050742c0090109004051051080001e05514001072a510710701e01c1600c16074446203880050260b0046036880c0d40c105417880c01c400d61107c1d01c2d601040c0194022910100740d032007100b102580e40e40840181c800c1030307003141c9020041907401d4805440d009847d049940c3c1080c03c400003403c00b03668901420741d1164094060202440008411400c0c07034401500910703d840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 96139415 1250 96138165 96138169
    0x30c0603150501030c03113f0c09211608030406021b0402041802030103060f0c050d09051c090e0c040b04150309080c0c0102161a0d020c07180e0309 65
    0x5030a102d010306168698030040c800e14401c0d846854986000c42c40c1c01c1e01c0b0035401600319000c11740428860210007484c806429081c1e101394160408200902040780e144d0741d8800000c8658010014440c1c2008100300459140100340c03030303e4001e515010005042000007070780c2103901207a50f5031000801c8d8004000902045a0101d5464240307a80340381038104000c3d80d100460001c0c07040f607202d243d10030300703d400c80801c0c0e4505070011070480f4000e22003800085800084102110000c05440e00030450421082c20351510340c0e000f400040740204155254081c01e00c81c090005a4104040300005110344420b001f018030944c0e80070b40206255100604290428003030f04401d00c95409007201c0000c100481c8100380748240c101d0300445a00c008060303102d074201c40c00b055491a40c800710a0260082ca40c107881c20072114035000303007150780c5408040a00381100c15240c4296014103410b400094081180540303030a010400940180040010600b01084140200085590314481d250654104102300c0d811a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 96140665 1250 96139415 96139451
    0x2070302011103250c140a0e060102011d0102131203050a080a06050a0f030501050a0b031902040e1b0117010b030c0903011d0c1201050405060c0304080408060c0301030c0603 76
    0x600d6080c28010111588540d03035516602984000c42c034201105118002c1800c2e208041d420303c10301c03a10700c016009468801c0c804411000d8199030750040031952080000051080040360003007018000028690b51266940d0340d101c184929506180e9000a40c0c0715465007501c0b8064000d103806081ea004203501c0340c1e8000e00d07500c207840f03d0208011050300422100a007662141c0001c200090158440c10340d05c041e40c690914551100380c41315403801001407c0300249024034420700034010082c018150304000c10307070404240e54030141d8101c0d40e580c03070400142c841008103840115100072440c02d04254000018840040c0716004c1207540d03400d030010400d0030320085c10b036a00b1408180502d80c9400792200402d004005454048280050759600b45100000100345e1001f00341c1c1c00c2d00e100ea2a42001180282030b560f064800030490741c130000c0000d080051040265030405c0c41440c17080c0c50580c0d00c050711440c000701aaa1840c00540000042040151f6002110300130f04190170148100c0003150462103035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 96141915 1250 96140665 96140669
    0x5041a071403040303080a0608060712021318050a0b030319080613020d05010603050106020d08060d110a140f0409030815061306030504020a050303250213090b0403020c0a060207 78
    0x1100008603445081010101a5074028080d20302226225540c90400400d22402a20356a004519090022031400300216a17140f0031030300c9488403092141504141c40c025440b0083c00b600040f2107510124100b0800090402c103c0c05e18507001c2003504060400340200c0d8014070a80c0d100c0d5004011446240b01d01084d40c4031401802d0408050340c0d0340340b90100d14a107542c0602c0050356840002e070824034500c2a40014180c50142e5400c11003a0b803200000c2e40c0d00e00703044501d10301040740340002501a2070101c0017034900320f10800b0201600707031804000c5440010f03517410050411403030710150380303260503e08459100403c0c2200c080c03000304182d0302c018080f854080c15074080c3c03c4030798000c0b0605488030001c40d40c850350380f124003410060b51268020004c000a4404901c1380070489800282860000182d03140112004080a4203200449060806069140080342c0100398000c1301d040c8080a4481e046d142401400c51400d9407800b0b15009041c0729140c40302c2d5119510000303003070012039800905642 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 96143165 1250 96141915 96141959
    0x120509011e0c090b0a0305040c050111030f030a110406050c010b06042303010902031014010b182214040308100308030118020d1112010603140a0207030c02030601030602190504 77
    0xc280c4079940b800c80d442c03140e41d00603074000040010550320980d4140c0c846803040340603542450030a5103401c01181d1981e0100c1d40602190300c2403100da03a0f006403902c02180c01001d05500050b01d140040102d010580040d440300300411800b00701c3c4004a003003801004205402220203a20b00390500d1030080360000743c04407000e4001102940070314a52401d40c08401071940003400c07030350081580090003000d01110000880520659000000d82c0c5c80654161010704842031042e00810b00c0003014131140b000103803035248046000510700b2030b00040d41d105101041d500c5041c2c0c03200740d1905040c0504030f031501904581d005802c0c12402c10110304214250781c1500da201e0800c8428003090309202c006400780d8050303200c0d4280340c00034000743e20302c80f0b8004011058150044041c3da0b0380c0d800c426001c64024450341c10400307466500050076052030f90300074030b5081c3c42410049200059900800c0c607002c001d82044501e9075000810109a89140e52005001c108900d483c0703150500f000200c030424125a41c800e1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 96144415 1250 96143165 96143171
    0x605070c21020d0c05010e0102030f04030b1b03070203090a05240f0409060b031608010806040209042310180c120c030f0b0a051303020d081b040303120509011e 70
    0x1858001d40030a41945074008100034006880c41c00c240422500620800d400319030a0284204554008001d07900640d82c0fa4070b80504041c42d5071900081c2e448004c0420007191f0070301e070b0300401030300e450000345001d01001e03801503868424007400d101200069400c4184244030001c1a07a54404011000b8440e20030803400440c0c8551440100400034000c9400c01d009690500300f0100f0f0031045200a10304c55544091003420031400d07102d00f6901c40e0400c0c01814410b4110000003805814000b100d80e4001c0c0c4030fa1520894a80042025124080300b1002528103400c91031042d6400c0c003041c0240c0100d01c14000c41100035491070341d10861005064442ca4110130b4800031581d003404403442540700215000001c4604c0b00c42c0f10701d8071948c0480111845841d8500d440c000c01d0100711358001c100d8140c2d51640003442418a040000d90344075070014901e01811454620040410340035001400085101c1e80b6840d20115881c0224415100d008001b1032040c1c2c901070281040246001003c0003e5204035800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 96145665 1250 96144415 96144449
    0xc141e0109120f02090703020319050c0708070605100603050c0d0504060e03070807030311070c0506130807061709061512010908040b04180504081b0a02280605070c 72
    0x1030701c400742550b00c006585551100d000050003100c00301440ea0034801c460400803039584203400e40c02c03404107a0710801d007a10005050b62041c19140e000d10b801025a03071105051503550380e600141603018084c1181d0301c940740d505000c10b00e00701601e90b4000d00280d00f41030189241199140d600da00891102848030b580354408502400301c65440a036101c4085019659102e0b0642403d22041d40310034030440001e46480071511000d250700341521103c3c0e90021018109502d81010070a00790081c08405101685c1c158000170000400c2008000500301038a074203000d14660004e00200c89802400740c1c0a50300b00104019803804060305010750080100e0f4010046c61000d440c2303e0040542d844c004000e07110028021641d00b43c1d00029104440d4821a04e056100d01402c000d402d9900c2030358000c4c00c0700c40600100f500c1d001c00c10340c01580000c1510803101c1c40705090700014140d20b2014040b41084a04a41c0030a030502813540b40c402920b92420b080b89071580c0c036600c0703980b150010b1240d40e0100d6554481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 96146915 1250 96145665 96145667
    0x206130c05030102030103080c100c080604050406180c06020d0504050f120f030a12110703120b040f1a0405061923130c08150619090308030a06030c141e01 68
    0x40e10054103014008549030340c0c491801c0c0b60203900001c0a54418403405120203451a80360040316460701040d507038a0b6031510703640e05110181070050012904c17a5140c0c0402015241807031b0a060009000700c582001030761800f100a420540304072010000c11600b00020300440e254020104103c0300c3c10b40c1d68845029105d05d0301e50801404409440c0346000c0006d03031105450303020210040107103c49400300106004010341001a1041481c0180862291490240c554032150302c0000705400242012030070301740c0600e401040700c00920404804442c80d100507101c5060038072401ba0b03c40b034152081811034000e10345051103c0968401e101101d00354002c850314088000c0006000d0311800752800e8200200d201d450406445070791002d10014800e900010300c0c80b1544003001d200c14034041c111a1400c0000092a158142061100014454003450003c002600040150300c190466400010700700d0851030f1200c081c0040e944201c441030b0854201245c260f4030208a282e0741c01e0921060100d05640d180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 96148165 1250 96146915 96146933
    0x10f0e06120309030307050a030215090d08041407380d02130e04081e0406050403031803170304050f0606060a030c0306081009061803020705060a020109020d1a090c01020613 76
    0xf0240e030540800b05007841002030024250480385c0c031a40a680d03a0034041400d58ae140d0404507a032046561200e41e1101c2101e0182903030341d8009020b11000c2c0200030307210080c0c0f443c10140b58402c201844c01c00648003c001041061003901c4c4070a90100c5210302c0c400764407420b090045290b1880c00701e50005101000c0f01030400c54000814055001c0714051406084c108907641004d00340110700744440714100c80c1e4045680031101519500e8890508003415030302c046820805520300e80e492404040b1001c0041403090a40000c1d40700001c2d01e850707a9140a142c0035081054034107a80e40154004001d005032580c40c1c0f0103854510b001440c001980c586281c034110040d280e00d0340052464047c08000e180b52100390782115280d14000e80051007154907007850000b030b41c220044040d00503081031200b4440c510748440108020f100c01d03c004200203081e500001c40f0703681c117000c00b00c80000310003100c01d450b101428181030b44010404082c0c03110090303ca00103034450b03c000b0b125001040ca8603d54104006500d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 96149415 1250 96148165 96148177
    0x50c1009030f0b0a0e210c010f0f0209030706030209100503060607020a180605010c020603040219090612030801120f2d0f03080603030310090c110f0a0209010f0e061203 74
    0x741004401e00160a00c10350820040d04c1440446060600c03614203180c00040e4840d0103545a076038407100e0002403071000f2058002d4110005155280d0b11048941d03145030094249501d00000c0c01643c815100c81007501e441500e41c8444113240c014444e0300c550340d4481450003e011541e04045949544020000c0c90341c0c4030310100203600180e01540860145c14003203207a40050a0070508106554031742c00191a45005c0d544006d5000e50108005001400c008510b101038111541071030380d00a859286000039990541c001384c000084070f550202c02c2c0f5030310010460062103800d01100b542a01c50f1038803442c0010541c805001e029101180840c18903c0c50a0380400e065004561800b2400a141c401e412a45079041a0300050121001c41c004e441d000c81280e005403003401d54100c5280c5806407500c06069540c001400b4003526202c02201201d05006482100309984050203070108240f04000f800316040e040356405503100c003401c3c03285000c0007000340e4015070229000c000038580c40a01c07901d507202d10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 96150665 1250 96149415 96149423
    0x905041a0403020c090a0b09010b070615030b040201090b030108031911030a0503061e03060a0e071a0c0f0f0a11030a02040905100608030304080306040b01020c0406060f02010b0d050c100903 83
    0x100402d1590200d001044c0d030108450483d43c1d0745842c0d0080c015901c2d03042c1d00680c420420f02c01005032084860060101510034000030450101555105003030320103a900680780c1d040107004200856a010000001a06079000c4c002d0855040a07080d907641e0081c00c2c1c1c06180d00324111104401c8a009102e101c0e40749840c00100c90b610568400000d1064000340c900b2401840d50140d21501c203480e4a5030a100404090300030581036072505107110181240c42c2d940e041d240144200843c019141001c00301301000790b44091981d6030040c1007014540416901c640e026a000100440b0344051701103044980349170005000c1074104134000001e4203003000480c3c0207500601c0c140704103040000115100c110b41c858050100189956200c0103134580c0300440b00140101c4080000404514042d4000405298188119141e4040e000e001c1012035003141c0200703021656202c2d9a502090b4240078800d400d250a9070340c1c01d007000e49540d480e551a42000c002604c944080040612003a00c603540081c010350300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 96151915 1250 96150665 96150713
    0x201030e0708030405031504080703050304080906040905090c0901060f20101e09080f03130b040309090b0105070b070806060c07030b0f0105010804050d030506031608061f0b04090504 80
    0x140b1442e1660701d60080c07044500078001c0c9000e00c95500e0021410521440e08141a07524210003a601110307281e01c01081201d0f031003001d100c84081901e4036009040a07044d013280004140c20501100c40ca402c0104c002d4134411217900d8014000301e580045250320713070100d90605c0411200302d42181500c10040380030240203441030960b400302c16919030300071045c00080610010340e40c2c505022034209a50031140058010b500422800d43d0405042d00115401401501d00310304461044e500e0009003101502d040c0c000408006060000806922968140b01e900b42030561508030207a071411611100100b2070800d0200d0440000c803d91a072034204c03031074180a50140da02258070785c0b40c20f0340100307000e0f65801160b060500010a2a50040c0c10484c051030300040200300c003400104046018180040035941c1600a08542c2d912140d5446e4860b8054000300e0301030f1a0074030700052001d0188018251b11009207194020401c0186101d6044406030342d020385003c40c0d2650365081022403c103551000c00501d280d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 96153165 1250 96151915 96151919
    0x301261b12060903040303031d06160903020409150f061a0d0605060a05040e010e2701020f041202040b061204030c0305160b15010306050105121510051206030a0c120201030e07 77
    0x1034080005e1082d030344640c40820503a50303052540720303910400700e500ca207080c0c2c003100c0031410009030161000700b4280740385000c40e42c094903a8080780aa482c03008080307401114a0120b0300e0072443c14041c1c81004940510700300420352428022800607980100b2480c00350100060181554415801580151202034907199880303107500303001003055002e0f110711001c0070702e0803002280391408082002c1c0a0070700c841420074018040e80316607200701d5444502018640d42000003840311107200000e4001000180307980054911580140002e6410b0035a6152041c20100480022b044581e014550040d80610302403002c0041882d060360203105004d110b44030b80c601418250200304c00b495a080c810500041300e0000c0c110b403c0015400c0c1e4186000e51400300b1418000101e50005144e4240c0c1d01801140340400d015200f500843c0e1094a030a510380006000010b50201c0707a040030440d19007208058000b04001e400c0d944035107a02d04281c4c01503801c0c0700108901c15040d68402e402c03491040050760300f0b0f00c00140d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 96154415 1250 96153165 96153181
    0x6111902060a29040509011506030609110304030921020d061a01090605030c0a090506130f0b09030303070c0602090301050906160201051509060a09020f0301261b1206 73
    0x408440e1107904508142c3c00c0c50007803608142440340071210504001800d1020020000030f0701c40140500c910790b40c1c4070100c241c0c158244079440c00805458900284807414a0250421349603861100000038404100380000030345d2056020044035012044842c50708800c00c0080c3c1c1010142d80040e40c028642d100210a11900c2d6011004040072001e8881c2c0314010f102c0151900c0000f03105000204100380001060480a18014003e0607102c5c5080c400e01901c407070015469410042c0c0e0142c015255010610481d11460039101c06441031503091390801901c2e10020b6500d100042c403920421040c00940000c01c0a0f40e01503a041c1400100244100c2c603000a80c0d80d524141100e00002e0210812010312080d40107104850082c0102048903600c02925018041c80345005440d040e00308104030300008280c0390602c00740c5800701640004680d654540b4096032107001c100700010403412060f202c20000c0100c001034071006600c5024610240f009400e00250b1105801580c0c01e007075001381c0007041040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 96155665 1250 96154415 96154423
    0x7171f06362c01050d0f02090a0b0d0501090b0906040c0501030c0509130c020d0c0506011208040806010306020a020c0a0501080703050402130204060e030d0201062d0b0a030e070603110706111902 85
    0x22108100303180046a90f00c4d01008007401c0315080203014400300c05004d5015040c141c030010b520880c0900f011996403601400300f407510004040c00d030b0b401e954800c41c1c402007004288030540c0184d111b6005080c0c030f04140d03e40000c1c400003031088078140b607a100e0000b1a00c40c0507405a5003c080028003162031044807640810181c030030b4034113890050146803807542c1000c2c0a0744022080c44c1e04540202002e80c20105a29007200c100e10003039400c0c2805100028004804001ca11301035807141c0000f50302c86940c604044c1c54003180301c0c101441090012010320440c0d9000c0d484c60b610840d05d20300410b69850310b00100d40300510a40c5540ca03024000a00818004d4010703001750044001035080b07507800111010100d01b04d81940c002c0c40c1c5030700c884007400d490b0000d160510300c18012801c0c1c045505241d4500944c505031f8040e0391040042a00c5280c00005010f081c4078210043c0310786c0c18140b00f14020044031044600c9084c82c001e058683d100071040e03c01d583c035810388002c2c0369a004031920801d41c1e00c4c8081c2d91 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 96156915 1250 96155665 96155729
    0xc0e0a080c0a050301060f0b070f02100207031209060c03030b0d05010c0203120109060308090d080f04090b18010b030c0703020109020306010806010e011205060402010807171f0636 79
    0x1d00750030400161601301441b800086402c00c13007603c2212401d0240d44401980108000c0d111228054550710240e81d80420600c03405085800820443e45145003042c2d0380d00c0364008170400c0c8001d0301420402984c0004400400d5a41840c0009291807070b00c0015202c140145005411580b82001c1c90340640d40010003080b040004105444640e81d803000d41c8015900c00d4000103002c04420300c1b040307810703080c80000300d83d00c030f84140030711030520030000d450325200d402c654805404d00307803078404c001c04501f0300b0725881081442ca14107038071056041c01c031002014440134100d0303441c2c418009a101c2c1418400e502c02042c66500a01b910b4007540d6601c030082e61503070207000c2c51398541108000050004e6002122411099201001d0015691907400555400c1c134002c01c0c650a00c038002e06d10701400310386103107214441d52903400c84000d00783c0c88204488a81000790480414000701c0000301200300b01c0c10540c51880b0640b081d036022034a9003c0d400245085555000c1038200c001f0300411001000800b8040d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 96158165 1250 96156915 96156919
    0xe04240303020f1902210307150501030204140603060103140c0603040c050a12050604030f11010c020f010506060903060c0904090812010303020d0c030e01030905070807081e0d0f030c0e0a080c 84
    0x340c05868464808440c0080784000e52041c144041000c1c070344a1136034184a0030501b48141d9040020584841c0750942c11300b4042001c07240e503080144214500703880380d13070004900441275414610701140420f0f590001800080d1034140140b401c0700414808000d207131101003015040d662a07081a2038450601c451902600340700700080038010030f0820000502625190308000248496213541d14159440c000c86c4481c1801c00450300140d41105001340160780c070483c4290300603c6400e1844545600b124009401030380f1400d800c2090b0021607600140c400e820517100d41d40c0d60758503c5003000180c0248894bc20003841c03514080358400c0010300300f0306154122402602583c0c90b00c100010304884074041e40b00010041007d0400301701555100740c5c440e241e214451811104007907104c2c100145814400d60140541c0c0d8017018050405051600d0020b101103407040040c4040071001001030002d41d509e659920815540b0200115018840c44401c18103160290a4500b0b00b500c50b005d003625423100380310040c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 96159415 1250 96158165 96158173
    0x806060303070c1401020c06041d070806030c060c0a0b010f0e0c0a05030c03070309080d0207140610030b07090905040c0e07080903030a0e0a0c1d01060e010e04240303020f 75
    0x24606080100c100d4400030340c415603078610141443d261161801d61060030301d04500c100c604080355a21a10b004101500700440c0202442207411500c014080004003250300b008140010301c42e15071000591282080c401300d8030705032240010302c18030340381881c20140078260250240c00051079060380f030340d142c007900c02184040314555140b500b151914480c04007c240056001c00020f040c46106801071a04808031b8a400300da204a182c0383c411454101806a900103a030010f000c1080040049500f0307801000500500a285401341e0140d17040c0310b0383e1002500c50501d040010b08031600c105020750240203a00c00c10082410f050614200032581801001580d194410125000070302980c8405e206502202c0210f19503070703501961801910344044c10350342500c81c8030a0030303000805a9072250040c1600c00040d02c0e4070150004139840da5035060b440041401100995030005990180560a00e201c041d6404076001103010076412241188002d18170800307540d0800031003050360210701d42d0f420480346401ca03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 96160665 1250 96159415 96159421
    0x180310020306030a021507060603060c1107050a140112050f01060f020109051e0f06090c0307050108040b011221030902090108010c05120c0919060201060e040305030f04140d08010806 80
    0x20208a1109641076989030340200798400c01072500003251101c100c00c0f008000d00f0076072107a6942c820f1b00c1064100319003242d121002418410391081d4210440b08280c001400003500c0c0c180071902c6c2c0c1016028640001404000703c41d40d07030340a46100c0380680b1010404114624100440341d0060b030080c012100001c1402240c0441c5502c1401000003241d040800340111000c0c003121a0f003074120010040a00e4003e11040350740c00d60080c0446031046403400064080c03410075800300b41c00c0200d980c01c07444c148182c01003444081054883c1d01c41c1903808070307031500201c1c14281c10010100c0840080c15080749207480649800c5d141d01d41c000203105442500c0b409502d90301c4048ac42d099685800c5043c0008200344481d40550b0700715240a80c1207000c00c0407062401c1c181102080c0741c8926043e17202241035500c0c83c20072000c2d50900c1303001c00410311f107065030255092903076004003e8800641000c0b40c6a4000000c50280040c4000304100c0c2d035090400c88014950382480030300342c90824454036a00c1e000f0f440c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 96161915 1250 96160665 96160693
    0x30403120b03031803100c0e030f070b0a0f030204050603010306090c0506160f141203010807060e0904030c05161206150602060f07030b13020d0f06050105040504020f07081803 77
    0x81c502625802800b03142040050041c08811914031892658103114034100b140710008248215501940c1d00e0751103207108030420007414a8480c1a500840842d40806130030010840710780103640c1e40b00307030510f8190000328544500310043d00458221650203000040000208800b981c045034006200e0755160040310ba40b40c0400070140141d40044c00108400c403540400156581540301031184984142d44c05403006803455468610710002280c544440080103010b1403408010b80c8008102a01e01400900c0c0c2c14404a20380c00e00c0a4401030030301100c51141c2d000c209080c0203a80304684221a03403100030b90b54002011051444107000d82e00c0c103141560704115013030b00309a2402a18540d070002c0920341c603440341c20001810000d0810040503641d030081c40c003036030701c51044000941c0c400e030025888025441d00a021501c101990301e000620b003400c2000300e660060262412614203c60044e217a0700101c12440062041c3d201c000c0040300b00250364500c900403e18610381290095044444a0781d00140d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 96163165 1250 96161915 96161921
    0x80c0117010501030902040204030b01090204031704050307051201020d1b030c0815060304050a0501090b070314060a0614040807150206010b070b04060207030504050d06050702010c090302091b07020d0803040312 92
    0x4040d00190100602032075000e40c0001c3c0103103101400041c039140d90f94445022198080c2c00100403543c00203400c00911180f6480c08180380780700300006107030034035100010f91755070000d110320383c0a1582d40c10030510140c82035054600c1840500414003840f1f000c0c0c810b4818a00b2072000c20b030f0200e031a2490003114107100c2d010391031003107102c10000000c11020703170f08102d03403500000c004a40f148188111000050800c2c024410902e20031545603605042002d809400e89100300e5440b0f0403440c0340070400c03000781d031202c440d0800c80c1c90038100001c0c0040448544c2c0414402c940201d036440c8610303c07001480c6c44e42030010000ca000a5401d883c50b0307903290903c4410a204082010704503103a071601003000318800303600070b0000300c2c4241003035458907551304085150310013552001c1d1101366544003003061258083c05203c1030f4410394641341072001d017140e000807108100508a00507065105403694400e403000c5046510842d0003c02039400000c1916081d411a40308407401c0f40000c000c401541c40a80740c0b40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 96164415 1250 96163165 96163187
    0x3020d0306080303180309030708061515070b091608062e03030e03010618050a0e07150309021c0b0106180b0702090702070b0f040503010b03060c221e080c01 69
    0x2d00a18516110341e40d03e0700400b904003410944d00d00040240c0041c550b403c000907001030594001810040c904172440c04000e9118045041c0a40c0866034903049501d0b409044507151303a071194141030152160840c59280c10b18110801ca00328024140108580c2c10004400d8420314510001c49030602c4e61861100040350501848155421401030500002e801468060180f40014000240440d640c109482143e45e5020403000074643e0350307041c0080481640104007000d01100001e0a0041c03a00001c15401c17481c0403078140801d41d4403d100c0c3e0440d40c409804244a01c0504001760155004d82800081c1d10828401d10010400424020b03255050620020003102d1b120f102090070491180c080c801c14880081c0540118062071001003441e210982c040c042d4cc1815981c410f488900704000c2c1803c4507144049240b095100004104940d0000320880b4170703004101c450021947d04a1a000240b0307103003a045480000100002c41406d9405085050200c903204812100700503285d00054403d00c4106e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 96165665 1250 96164415 96164429
    0x305120901080711030d0c0903020102010b01030b09190906021b1006030c03030c030318080d0c0c08090409020a030605040b070314100b03070c060603060504030206010506180f13051303020d0306 85
    0x500b0010315442c0c05410f6400d010700000d810741c0e00d08411a1101001c03503046000803130100320083c0e002d0065507424405c00b00b40706020301b010884580158001484480d0013424500c03640c075140e154100e0182c8540201c1101507000c0015929050440400380c0d80d440c070208600054410080c0a251151080c0200300c2103036041184449076030f007103403404c43d503221402409074180b41c2c498800945c941c082c4802d03101d0541c080c8203038a03203134851800c40c0c00694065400b5501041310b114405008100032400704c0f0201542150006002c01e01440403818091550740042d040b41d1500040105012410410500ca09403d5a081081509001190f00f070240161900035600d08d00550a00902044030b0055400c441c91382401411106075030354280541d00c154008079950740d100c205020406804110b0f00d805031504807426800d110140320a11500a8082e2820340700344d040540c1c005590300c42c40351700761101061003020304c160326042d40704c8200c140b01080200d0051164082c5c00c0310b16840303480f0345015a201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 96166915 1250 96165665 96165677
    0x90327030b060f0306040b01150216050402130b0708070219060c060b03120a05040e06030706120504240b010e0f010905011404080d0801140312070b0414010c090305120901 75
    0x195107951600490042c8030340d421007100d00045296a404005140c8110301c60149411a5030411100c441c049070504950303420f55102a44101c02403145640007030584800707540050300d403403210036000b81d6907640c5e03030016049600000e68001808025801801e07124020340d882c0b643c289200c044030509101c00c2c0b240c003001500c00140940000c0040d0003001c2c54210040407203a079110001985001a408100f09001007000041c042045600c40240694446e00031405000001d240c500301410f00303000b8071541503c15a44038001010010651101c0e4511081c0c0b101c1e100c554040c241c402001400c1e80007045022803900318511300c0c20703e00b83c0b02c08012480181e49194040340f0306001511441400d200303800d120301d0300384800f04014604101480510341242c0d6030026035450001060300340841100110301a07001b141c40e40051180040c1154042a881007030b04880d80d13910304141c1c0d10304d007040310b540780503500700002100d034694851b5110341500c1c000d8083c0d400e210070f8550701d002648202500b0601142da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 96168165 1250 96166915 96166919
    0xc1306020a0b04060f110d0b040f0603020f060705100213080606040603032307020d0813060507210201090c06090f05040b0d031b08072d050606150708030901090327 72
    0x9660b422017103811000f4000400d8190512429201642040350141e02c560756508100f4483d00d1b2500610005020084013000440d045030003050201c0983d0100078040c1d00c0003c0c5800800404000740f40400040c03000454032000c464008039101940c17403003201610700c00d8a002c18094a4284681812298151680148100e10b5002d10a00c5c8003003040300341c50200c0900000c1c0150301c1d40310601441e184245d04541e55920520b0191030076105e43d41040003040030910001000450300c0b04400d8040541030003080074010010340c03c034050001c803e402820800600320005009030000404016110550ba4103070900752504288022030b001040c84580c0001300b051141c020070300900c030003820001034070407000040c2c0d03042d169105c995010386000c64902c40040303903250360f0817070101140e016905109490300c0c0c7e4841c50b841c2c440d23540401400c240e00c140c1e201403440d0410170100e4200c0740000d60080c0b4198580c41d01c0e01410340241207040301600400d01c6129a440c0d00d031308200030310500d4900310804012081c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 96169415 1250 96168165 96168173
    0x2120f1011071b08060702060912070c030812010305010509010207051b0402070c0b090a0e06011205071e021b010302120f04021c060209130509070e0603150c1306020a0b04 75
    0x120904603407040e000800c1001901241c0404010019290f80c51002c010807480c1c10511403520100a018104540024051019500001c6405001402da6040c0303692030740aa818455880815540020b082d60700024841c0c29800100c402141240d003c1c000800c141e41c2c0713801c411401d034402c402004101d81c1001103844c580140e1194661080c2001600c01030600c6915500c4011501943d0410503610300089801703050391078a030b100500600080c014bc1445801c0c480000b9105440301a98000c02c9900c0b980090107851103106481c1981f95420114035184026400c06911707030340c0c000c42d6081a034180c1211101c6550280c02181d01e20014800c2880041d41c40303000e5540719581c058000c03030303101d40c0d807584143c1c40100f88821711910700d014820059a5202c20002c200c0c950f412031189001260070001088154400030480b42c08440029a03256440d82d51800024100754105604802003148402484042c10800020f400034401c0c00303241c100419217032541642c0e6003040e61030003490422903800050010b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 96170665 1250 96169415 96169421
    0x10b0d0602070c051009080606011403130203011b110c0d1a090f010207081c0905120c0102090604090e0d020708100b030a0c060e0f0a05090106030e2802120f10 70
    0x45401100902461034481d0b00140188901840035000901091002d01034107400380a0239400c90424240101064040300f4240400d0000400c1840c07120304540c60341c819034500790882240000c07120000358090300c0d4407501401d4003108000c120254480c49020005a082c1580c46401581c0c0001d18545000350a10101c1030354000101078034254040c003c5000d050482c01d001900503144500e206648035042e0441c0780c0921200720341c00041640c1811000800304101084ad00741c1c09038001d1101d9a100300007440c441c0648a220707042500b11000040000d50020f03254401030144010109070b4030b00c01400a42203981d022a401406840c0c0c0007003403084442141a4041042040e01506075000b08000e0745070b100c0da20341107510120209104402c1305085280002c00000c103403030100c0711090789606280100d080500140220028981c0c1c1d440720210318030040240001213d41d0040c40714481560400c00480390a0340d0800301c0c090300d003031400c03400309405c0815400d40303180d580001404040620b004c01806 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 96171915 1250 96170665 96170677
    0xe07050303070f050f030309060412031a06031e01030503030402030111030919030e09071205010501020304060c0605060105120907090b011e0e010915020106150903030207170c12100608010b0d0602 86
    0xf03030310425451751400081032002d9481540b400010b07040c546072a0030b28103000c0c968611707e00304052902c80c47d4804d0300704480300b144101e1070a40d030258a90b9100c11380c0c40107a0202c0d40e03060907048032040c0000f0801034000b00840c0708520940080c885100e80c0345084000c0e000035107862680d82c00960b0411081e076030141c02240320764000c3c5060402c0a40d80000326511240c00d859160018a480002c1d100030003031382c05031900420003840214545460b01d00018148400d65800505032500c401c08580d15a04c07810941d00c0c0b0310b60400450017035080080441d5601c0e4001d03c1503560a50820003039a20301d40c010458001c81c20264203504000c5415181c0c00c59800040a25076814403000303480200e07080701c0c0c03140560f200b00f000790000116a810000e660000e600b0044440c1c04100901c0e00c02e0001a83c003080c00c80c00c0724034641548007100c2c000c10300070782040f0481200580ac9200b402900700d88410004807080b55420100741007028a03115041c0c076090b0f521441c1000c0c0c0140d2682002400a049a03000f041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 96173165 1250 96171915 96171923
    0x1e0206070f0501061205100e1c110f1c02010510030b060f03161203140a1403090703050303070e0108090c031b010203160804030c06030b22090c180e07050303070f 71
    0x1542170300c0e0044010003100424050301c807503000024202e107800807489882d1010750b81d100100302c01000c481090141c1d0344282000f200b00711101502c080607240410a0040d03410060081d07610a0000603580701e240405805030707070300541c00c16003c50705400454803482e040e40d130020a540407603a6044140021011070503c42600f5208801d0320025407035100300894060000150461a000801d0600404810b04190103020821081088103a80d0743c2040d82d030303034050b03012003552034a80d0f4450041c0d9091402550000d40207004c00002c01c030a10350f004041484494090302c40070b2113601c030a100b00b42d4a52080080d5601130703010b400010000701481251841107001481121329004407051007071110340f00d0f240225180200400c05000f0803d0b0080b07840301900f03480c42d003000f04030401e80010f243d5000c29940c08410307144c03103252070106120903008280352503004580c502107517682d1f0030352240e904e0003410009440d51810018401c0c114011070507600300c03079008005508001d202e40f90b801050b50290030440e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 96174415 1250 96173165 96173171
    0x706090812160207050f09041101020703060c0504051f020a060203060604030804030b010303080603030a090b0304020a2d090905100e011404030201020307020d08040203060f0a0e01020d091e0206070f0501 89
    0x5107010440c101e1510a0202c2c1c0d208040720380300200042d1805505801140c400c80364180b50001d5910340000311a4040d4100c8052011000c0080c0180d0038910f2542001d0002c50411310241200d54100b402801110320070b5604801401c24035031441390b400b005182c4139005030005140c02c00402e2490300a5508003000501d03a9240c00d590380d9800859502c198401c8884111450040051503008036007240d11a01c154003442ca4180c1d000801881c0c10250300840a2400010002c20103540315048140003401100c80c0741c1d40e81c10b0608003001410100c0d11200076030040d407414003040201c154082d410780b89600900038048200c4a18520000d40211003107039046c0e641c1c0300c0c404101e80c10342c00b034002d0050340039800050340e0b4280084005d0901e946904400d0a00600009100c016103001403039541c40302d584410f810a1381c0b104082c074030241107500031500441d030010840c5509011190b10802401d88103190039100d01451504c1c40310b4445450401039030180003440303100b011540c6681c0611036144100000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 96175665 1250 96174415 96174427
    0x30e10020a020105160c12080405010b090403030516050408150a020904062304061d07020a02030d11210a0c0f240b09010e0a0c03140c070c0f0b07060908 67
    0x4100c1e0000445500142e443d00c0622201a202c8590110000807600d84040c41100c580c841211f180c081032000d00401c84400c00060a1201c03c0d80450a0750303900030103071111800c10303080080c0079000c246e610050340b400c03038603220f01000e000c0c10840c5c0440b100d080141101080d420502003134103100400d81c8171015001c100001d1103548503c82c0c10064909408083d505445508110b22104034124660340101e1070541d003402141c00010b8900c240143c0f500c028205540d0340c0c40d0403810705c070803a8002505442060507041400d600007d0640c4403600c0c0104039881c00c002e80c020900c00a0b60b03110a000103220410000420502c80e0040440c410b008607041d00c0f8440307140e030740c5905200f19407804000c600355a40038800b160501d40100b4900d06422292a10716504000c414400204094084000310303548505103005c250117504114091034500d08012110301d041604102150702400c000c8554056008001c0b81d4a5076031a100700c240da2507030600d141010382c1555280c0041c0b00000302518001c0050283c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 96176915 1250 96175665 96175693
    0x16210f030e0a05010c0807020f0304060804060908070c14010f031a120703151a030a0c05040e0a0206070501090303060f080a0615080607030c0207060e0f1309021206090c010e010f030e 80
    0x20f100f610805940c3c031b00d4241d19003c20002d0514089001408035030300200401c07c18a0b502c0600e981c0c1081e0040d1000800c3da92601e003000203480780140c020029036030002c0020300b42c9401c0c001c5101174102038a54155495980004504540c50101c13480009002100c0300380c201d0900010392000200c0103000c861000c0c0d01c9482d01c030202da501c126510403203a21020007962054801d19007410f0b4800607001031103992003c1e0390304a010501e600405000d01e03500c90151004010400c40d10525a8001d02516910340c81801c055029016003541680420700309100012041104c8400d541281e44420103040b400c03010381e5800004d054104c00908085120b070002261070b00d014400e07030f0702400c020346000403010074204000e402c1031810b61204042c045041c2c2c0380156034030f84000b11404203004942d4510038482421450008256620010350401c81060700c9900c040d02c0010083c0c020a02e1030100c4007000c040c0f50044502000d2005224002802d40320b00e01c42040c007a400c18050428214251140c0ca0200782c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 96178165 1250 96176915 96176921
    0x4090822060c120c020f060a030b19031502160b07020309090a0209010c15060b04030b01090f05060d060203060103060308031006090b0306060403021003020f16210f030e0a0501 77
    0x640e00200c0c041a92030104800152140440208071038100700504071450b49a03560012444061402400200e44410045588064140010900040105440f20b500200080090940d1445140544078107040d490000112010010440347d010b0002108980304042c02d50194028041404420038289405000600f003040d40c58031800301d0f80d00a60f01c581d404000c002e10390303101612408002e1300c1006881076903640a1040d90509801c0b0f141c100d0507001c1240030b10018121035000981c048808035002c0100482d042c0e40e20304031541c41c141032110201c1da4076104200c420684403903901c0040c0b07003208000100315402441c0c4c440d80505000405550703c4d02c0c0c1900b04d500403166100d640629075410321065811010100c080c0c201d9041082c11441e00c903010800d14816404042e03c500c0004840300441751094044030a601800022992100e4905000740c1c6c42d000b050380b0441d00540081102c1d10740c6d4402c05000fa10b480704c15503850407254060340040e001040810345801039401007950300030205800340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 96179415 1250 96178165 96178177
    0xd060605030603190c14060c0d020106081209060412020f03060a020309011401080c041d0f0102071203020a0801150e030102070b070806090103210522030b070306030b01030f02040908 80
    0x18403190780e01e15090040605000038a15a008004602d50980c00031540412408040e03502102e030084102c01d407500018100d00414090540500c41c403101c41800c6541908180100c50412003103d0761406010540300c022f000305618031f40c0181e402e1008104603017140707488201040c005006c0c003c801a148000c2800c01c0b170111b0700c0042442d0000f0600502d00000d00c40d0640c4180d6600a080307555040c01d00d515200c42d20b1000051080d40c542c036031000f42007030303007400b4803104101d80089903d200042c0c400039000c1d42140e40103540d000081084860458003d008454401c401c5644441603030f07080921001c08240203180c1c040410484010420150b1024030040070b0140c001e401031165880c0920b0001c0c0703007040003040307a4058041c1500400008001c90196450103468105044240c41e558108582501820343c0c24480d11407106055040190301c1003209007034034000c40d901c45199680c007070b040c3c09903291848010709008810b0010030205030ba07076880c840a244000c102080362021500d42d84240d130428 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 96180665 1250 96179415 96179417
    0x203091e0c01080414010b0a061106390f0a0c210516210f020c010908070506090a030c0b030906060d0b0a230a0606080a090503090d080d0606 62
    0x1035800031182101030380c44008510081001024801d1801000030b0140401500061401c03400070a00320354032400b03401c04810342d60084c00d02d02150743d035103000421a01031300c070004040d4010500400c1d845840e5100c101644030b502241c400303036030f648141c101c0004a0b0754540c400304a482404110205103000008140c071444d40d6546045240042c00d00c00088401050b007402140030700c000010505030404c2c2a90403c0d00102264183e04c1c41d40d052035140303010620f040200f01c190200311f031040d294012a00000b081c0441c0d08581c4501c41460064844034464046c1b04d1059019110030092841d0250003001040c4c1301524a41c106560ba64805103050a660000810002c01000f0081040410000190310201c200c40e003031001c00d2940c031910304500d00135080542d01c03900e5000882c082c0c1000102c040780c20003c0c0702210014901281c07c48001c000a004201c0022a50808990001c2d0240289040a0b030480095441c02961a0420a0842803807030200c5404400340600305060425101d102c00030901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 96181915 1250 96180665 96180673
    0x11103070305151c060e01180c08030703020703030c0c15050d05090a050705041a030d0c0b0c03040f1509120e040e0f0706030203060d0f1109010b13060f02030702030613020f010c15020307030b0301020309 89
    0x146070460303851006810809503682f00b4442040825400146c600485ea01401c008481d40140e0804400c15a0300f50410f40c03900500200c940c4040d6440b500a056a568900042055465a9102036114020b0200280c900d500c0101d050045150662058407020900c0d02c59030040c44041001ca420610f82a2a58000c141118000014007060000701680010907115035440d61070960b072041d1440381d800d08061321507034051240f03090345c20b0940c2c4040b02083d00003420a200d003501c1400209403500c2c00234041c0c091814040b040d1244600058081104451040a01080c509040048001750001040980e0103600884004040b490000708011224003402e040940448008140500d00c00103a0103880c00020803c0030400b5400c4104040341030701c0340d501d4141807520203100100e2450146550103035050040400340108030190041c0002450b02c01d5a00601260404005403450300b044072000d089182d501101282c200d00341d600556020455080000e110f400100100742260422210140c207688 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 96183165 1250 96181915 96181961
    0x906041d0d0f090b0d0c030207020301180507050607151802060403050d020106060f0c12020705120312060d020a0905060a030b010b03180d170a020408011103070305151c060e01 77
    0xa4003002d4400c0c90001e90805010682c40c00540e078000b882903070000c00100780c0c0d4040c850b21141c840e4040f1071079142c008009011002862040b100c010078030a500311841e04c240c1c0d5001426007060810b44000ca03800c2502e01014414440d0307690040e00f0801450b03296602d1045c0741c900140c0d1050040c101940c02500140b40b074001711700c400303400c542c500c4c0c0002c82441500a007040d1415402480c04c004142e020185c0d81e24a0704c0380000340d103071092a400c031660114107082c202c142c50000001030800740f2107036000c15031207443d10810700caa881d1903024041e4012034030300010300000102d0742026801020141031216001e43d20384807400e4044003a00016101c3c0300020501c034000151014850031030f5000009080609000031000d0400c405039a041001c0760403903000100040800d034140e038014168031009021100444c4410241c551003205c0c0d4030701003803038040810604140040d485440010140c0011140031115104040202c1c10001c2100c00a840312510f0059000070f0040f0081e001f12580c3d942d0f40c000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 96184415 1250 96183165 96183167
    0x1205060a050604150e0f0d0f050f030415030b060307080c0f09060a090305210301090e0106080312010e070c0b060105160f0606061407120c020d1e020f1903020906041d0d 74
    0x80c0600f10644c8103544007440d080031587c3c2c43d0740309104554030448a4a80ea00580340c03490a2150317039800b4075503500011600140070350168a842d90041250342d810031400e4651401c000e268003003658464002038400c0d00081948039144000c2c41e00e91135100c88542402c07880350004441d68407401c1a8400111100010030402104000c2c0400c98550988c6051200f0b010a1000c0002c1c08140300390002c0c1c98440c48000310f001001c1d8440c4010380a2030701a6070752000d40f001100c0044c2000e10a0040c60207025000a801074171441c080c040c810390104400016445075001111903400950744800d954a100d88036100094240078a401e149100e401e000c202140b812002a08100740004440901039080004034001842e501d2150000601403c0c0800b00d55058008202400350220000b0410f40d04000036410780044942d01400b010310845901d8443ca007074009203d041c5003c031003241e46541c0d045006000514096032920790020004d040007d0080b94a0b00c0310040d04440c102e040640d03004409100c404c0c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 96185665 1250 96184415 96184427
    0x30f03070504050f060a08060123040801090b091b010518060c0708060a0c20070518010f090207082a013206100804080f181305071205060a05060415 65
    0x84c003001c60b04141041c81944004c4c140c41380061405040190454800d200910f00c1102c070444d0b81c2c500c101d07442d1034075103481c8070b00d00800900c50142c8a03c11403c0020760401000506038480000c6824010317100080e40c001561580c000040b405150708407801200c8168450101411407410310704010f1a10300d20b8404002e0802101510703035017419041c040c0700034000d5003105d6070740388980407401240000c000e01e00f0014201008c50704040d40c010482440c0010034600340b41068180d40a205884001555500000e001c9101d00c00c03000780404014041c0c0034000003080440c411400001aa000803058820716060841d61000f1440c4100d00083d82d8482209040300d0350702c00d034416001c140c0d8155040c018001021a2072101585d0b0420940000050422502c903040d40c1481032040b0016880381e08c1100c42611b82f15980340114040e48028040d6034601026000f054010103c0303072070340c0b50800740c41c801c4d80000c0c100003801541c02000f0881c0c002030544840d001000103240e070714022241940c07429001044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 96186915 1250 96185665 96185689
    0x30201090b0c131e080303040506090f07061713080a211104050d05010e15071205280902030a050c0a0b0918041e03050306040c051306030905030f0307050405 69
    0x444102403040c032803005210a8030038252a0184e02d1403070300c4100d18100c218600e01982003111140004400d010030040d0000b02540545200301c03d48580443c0c100040707a5680080c4150701c0002c105080f4074100d1075001d00707801d07000340c0d031041702211100990f11489855400300016000061150103514603409132000c489400446070718061240c0210b003808e5045a004a0041c0c500c030700101007904040081c25030102c4403060616041d600a02040d000f85002e1050440b813000100e4001c3c03c8880c8480701e00c0c1b00d5503118101611000507191141010840840c1511161264581d40c2e100c454000d030364104101910359118000600200710b8070740034000408000e50150303500c0d207024010081030382d49a450126000c0420400303440560751382c0c141114074070a6081c1d103001507120250403505069000c40190310443c2c0a880c184860800c2c2281120765220300b00c4c17060b080030301d002d0f410302955210b90040c0070402c0c040c0040b41e0914407076102450403940140e400001060000804003c103003490946018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 96188165 1250 96186915 96186931
    0x1c12060902070c0b0c0a0c12020108070201181103071a0301080118050a06020d18060501051513140604031a010807050d03020a23010c0c051c0c060f1404030201090b 72
    0x100b02110b43d0340791a07000810780a02090301c280401e0505c80550108080128160440e140ea02400e569103141020107003100400ea00045180b000114264014000d20242040c0031110505030314070350b21600081c055509181d94180075261000505015200b20380b0004002d859000e9625494900c034503084986070404400d00303000251101c000700d000843c0d10718010f500040b000d650340b42c1e80d0b00304100600265803841d10343d0044903440b5044c04150f6112905940c0c050f5107400059a0f420300c801c10754040e0008583c01d005000c0c10512000c49503001040307203c00c0140c04213081039201c3d070722891080b0f140031400a00c2c0302c20100410542c00100030724402030100796540300c84440d45841c000e4840d110100301a0900d11084034184040340201d0b81003010b100b0380e4000b085804c54481008040030443c10702a5403910400d888002d80c0345136030f482c0c0844034005032502c0107808413aa9a010142181000e07000100d6640c54444440540c1130082500c19882640005541480c1c0d142c107040c1505d01406c041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 96189415 1250 96188165 96188167
    0x7090b010c030f05031f0b03072a11060f04030b04170a0807030b0102071a13050405060105030f07030b090c07030206090c060d09080405150403050f0f03030703050403021c12060902 79
    0x207400300341c00c032011810562040c0b034503507601e980e415403000303100c02e6121900b503440d070300150300140b042c1d005800f560042d03045555000400c078040124003034001684281c50700d081d1340300006800042d030390f02c0c0f080080c44000e0102e03400e0401d4101c92481540082d40152181004034042104010803810b21400104a4100080c1801c0d1007040040c1400f030003c058606060380c540160145030700030071544c80148110014031910f446502e83c8140030b034102c029800c0341d06954101c003054519081c020544101d4040e55418115581d2074240312980101400d400c1c245075540c00741c1003ca4945050040c403420020980179603800361031a00919004000304540c2407500181051078042d03076410111041c280007100085400c0340f003418071042d2403240d680034903449540481c10402640030721000e00200c2e0b0041c020381e51407262518800f511060203c01c2400719400c2000007408550203030384210307006402481125030b0450302c64004610202c4500200c40803540700862078030005c9440c0220030280030940025 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 96190665 1250 96189415 96189437
    0x316020102030c04031e0f03030e070614071b1a0403020108090604050606060310091508120a080606030a0204080109030305160201140408071103030304081c14190609020c07090b01 79
    0x140030f940600c0c08010300d10040d03948402402648815a06480354014030b080c02c10100914000c0c004040c05944400c041c060550002a51402681c0680012468015052070454160360b00e129070240400c405040084040c0c01285404040a050006013a0329001c1342d42d0714192b00001d009808010b1078006550f011104000016002081181d04158161442a2241c6a0a03150307100c044440d00b001050501e000014280c240301c0c000d25000700c52051041e01c401c5004c642e5000d41d03034400e09480c0400b04100102040c41400e186000f154050344200006082985400300c0a007911580001900042d07102e2040c401144407070321002c000c00c0e03000e0000b04003840c118154441610300013032000d0070152011500300140000c8124451030520000c041d80d81c3c0f450a440c190301507810401c41c01e454003010a001c045d500e440da1080e8000c0d060724020b0092140d0359208041031003100302580d80c0c0380302d4854900007043e100c54005000c10100d1240680401814090610100e900307a08030715041100c24022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 96191915 1250 96190665 96190681
    0x2010915060f3809100915030c0203030705071e080d060510091a04080124080304181d010501060905040e0c090609040f05150106030c230a0e04050a02031602010203 72
    0x15146190703030203104020040f90035041082400b0b100840e0342c00c0b848940c4405d07040d0394031040d09002d580c820028007120340b490718000c0f42151180400000940c3c000c0010880c05070080c4094010230348515514142940f02c4071606c00c2c47d1404000480741c0006c04244442458014003c0d040900001c1d142c20081c51084080104409841e2294800300f201c5159031028980b1407004540c06805084002c9c483c040c0401f8a42818074049001c03903075140450b540104000f14007100f15130458480300030a101402d4446c100000500f400710120b00c1141c1c0d038a08198604d507080c010b0038020001c0d5100d45247ea4648818441524041104803c15401c00f240703010951792018411900070005031014640d82e80c41d4940810341c030340200d9004d0403601c5240000601540c2c000022410b0340e0b480d50701031000e004400004e641403001d554201e000c2070035001800f1642d00303030f407805803105044601d0098a40205d20022900711101a1110120700e0380000804c025020600d4945d68400014802180703181780040c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 96193165 1250 96191915 96191969
    0x31b03030904020708160b090f030a17071707110106050d0f060b060c03071b0806070206061e040203160306060504031e020f10020703020f0d02180702010915060f 71
    0x1516601c6140c0c04a40039003800f11040c1540e8007001d40100e12400ca50447c05e046502c5901140c508195106000300021700e11808400c0e21412a91511031550251503541c03440841c0800420000030008000120002900c4240304c0f98021403050311404040068030b151a800d45007241c11080c00f42c56003006000019003000f85410b80103400c400006038040800300010341c1c9100c0c1d9802c82480c0d2201080182c103200c481036010800c1504904502c003034a989184103522450b088580b9000f6810a8000511034200216200400394600d0420910355407040002000c98000761059000c0240686a0700d01e511b416204010207000b441c10040e080a1469540b200c800303d003000c00d680003040d4210f080046496051409400b06801080070030f00e0219090000c1d80c460740d07807106900c10383c01002865000e0a00d00c003020102d0f80c010308506100c1c500007003000324001d0080c0211045640e50b800280100d03a1928010003030301c0d041540030500c540703801030007000040290400341100f120300400110b061a180c1d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 96194415 1250 96193165 96193177
    0x12080906091f0504060815010c11030c0409150f0209310c0c0506070908030a0e0a050d030909060f1202010c0203070509010b04050102070e060303030103260d0209031b0303 75
    0xc548a96541d5801d002c602c091200300d2850500c407401c1c1612001164100028009a4074036a444c503102e981c03070f8040180802e200028241c08030311008013120100e04c106144804012010381181c0344983e9010125088074007444007500d031000c0d115404904140c490050006250b40354405608041c50300001981040241000710038001000d810f003190300100301202001a640b00000300318030318030b1001c0078040e40000301040ba00ca028010000c0c940c035000b00d264009aa464100440c1004c0304810b00b0303290100700281065000d0241100028140e8880406420b428404d03600c07203070301e01e14014008064801d60740180d0320f121041e05040c030081c1074456024044540918001b15204030f2030004ca03080a4154200da074002e4035034400030a040c4115001041120303000c1c1e0846151a0751148000c10407402614040c1c1e05070010001000404c4c079004162044000c400c48082004040c08840c00c41540004400c010040d0041480d210764901032040980303465525021554a1200d00e0000c3c1e200d00c00d003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 96195665 1250 96194415 96194419
    0x6031d190302070f0605090f0414010b0c03040302122802030c04050a02090a0603061701110f090111010906090605060909060a0507050c011d070b120f0703090f060c020601120809 78
    0x2845280050501c204003c00080210110181c80161175400c014034607070005003d94001c0741189000ca003182007610a0f44151842d02c1ca80b400540d080c88072960040c0d0040c01e50310100c2c441400084096034400b03d004940b80342d55002020403200068000034a00000481c0301c80708422140381303902585001c13610100c07a45084400096940d01d908004000f8041c0c0d03213a450300040000400306240c1d4055106206881000074959200d40726942020700707913070003120503555071001400380844145090003d04040c1805042181880c1001c03c0110308403418940c05603a0340d43c507aa650310034021a44a0130707401400c296194440707868500c814994540c07000d05030f102e5465880e0001842240b0801c1034074803246422000340401c40f000070111001a40c000c8807185140280200051041e900000b15000030b251403912000e1a80d13515414604503038001c180c60b061640320101c540001e4010187c0c61881c0d44a14000203a611100c1002881c0600c16000303440e4440070030410700081590304060f680d142ea02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 96196915 1250 96195665 96195703
    0xd091202040609050f06041104050a050d0602040e07210e0c0d0c05030a0305190207080d0e04110319050a27300305071404120c030206030a020406031d 66
    0x2403840032a0003400c4581c40704010740d290030b05101010095509903400f5090817074080c007070000d01000400032445075112300e644c000d50f1018100310f203081c00d00d6039200407402a071005003041c1c0d507004001c0381820704484000c0000c44101c1d444030039603804540c8c014003160701c5070204540710300c1941c1140e440d400300810f94031400360a14840c080007454072603100540701c0130317068035540c110500d03011b0610f41094802d449a00500d10140b0603840c40040d0800c102d4200c076004080c1c44142072415690143c400c40d2880d0410f49441c5405a041c0c4c1e020020b5014a40c040e4501c0c00800030000140d04550010342441c0001e03040041e12688020780c010030f002102081515a0b5030a42645492541c45c0e00e90320b0648615800d242800b03e080b0f08021200402c1440ca807028000f030783e81c40701e0132118030440002010350603509010501c10b038187e00201d40c2c480b51041e8001d042c0581c990300055000d4100710b03032620b40ca03600083e00740000fa505001ea4010b0412603d9080b0344101ca00122940321820402441400741d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 96198165 1250 96196915 96196949
    0xa0c0929041506020f01141b1c0501032d031d0616080702010206010b04080a03111e01060503100b03030d0207022b0c0e0f18160e10080d09 61
    0x1035540d00032160109403000711003a0300e40ea41c0f0041d40303540079510744082c29443c0031030240b039200c00d0168003481044c246040310388401c901d1004071481d40062036122038440c200541a1040d014a1140c01d01031401022800300c040800301b03c80c100d600040c800d8104000400d034100c000290403599058240403484440300301c00103090302088c000e000e291100076040c8100721400090181002c010318201d4001e0303090321f00301d07a00c440c003100d43c40c030a0b4400c00030241c0c030600c11403000c20300c64500d1003126030740c03581a101a10381103e000c0d40d042c4071541c07e0309880e9641d008200305d00e1400b002855812501c56406000024071540065240d005003031003100495000a1840c0031540c1d41040341d0914450100c0e94102c41c113000111203650001d028044407442c000c0503010421419201805200f4400740c800451156154a12049650455003008490344512480514a030140d0303000f050103040d170071512400d1483c0502034006940130300ea2010880c0d4210b0100020b955a0000f04801a80c0714440020aa52 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 96199415 1250 96198165 96198169
    0x80d021c0201091b0503070e0103081c06031506180c02070308031b03040632070e060d061806140607030c11060307031b0f091701020c07080a0c0929 65
    0x410300c0d40204521880104d45640c02003554408055800c150201c40760303a520b5401d4031000201c20f0002030f081040601c0398031000c0c00060301030107501807540ca0200d0100d5503a070b10a040e0240414802140548031002441002680031a40c00d40900c40107003408150788402010751140082d01014054640c00800030b40310b80b01a0a4810094000090301640d0b1324042c1000b500034443c18500f450300c18003000400e21140540700842101d040d00c00d104450903158241c0c1036605401c6e0040d101d8101d44140700e43c11200d6840d120f05401840703506076807880480010f540c002103416a401c250600e2030b4040302144207444850079210720641c581000782994901d400c2c51950a0b055900007640a03000004001d0120f0b41a0001203082603442d181e40507400400100ba5898840711540c0c8002404a0038100310f80c00171992261010518100018a031a0308800e2682c04e02403190032002c00c5038084a20001041100e0340b551000700f403110410450303552290b04003d41485004240c000d04020852600700503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 96200665 1250 96199415 96199421
    0xe010209130c09090218030a140d03060e13140609010b010e0a0602062e0308190e03030f0d09020d050a0c08030c191407080601090e060f0c0f07060c1701080d021c0201 73
    0xb5200090840722303150050310700000700840d2040c0c945080d01866042c1190782d4000c0c00342c001036410600c0c144081d6510460482c098041c1000d041d141e900000c3d00e6449101800d104081c09102c0c0d140c0040741940800e4005000500c01d1400980504000d10040000c56408940150400365042c21003031a202005c0080703281c107d4210704c919038041120380020411629a009240e0b41411000400301e203820f40105646158000c5419a0542c0042000100e40100c0c1d60084c400842608070004140120740c010600c05003010000321419403001c2641002d100349100c0b0040203000302e000451821559601090b2140c6040c44240754038000c2a207003408011041c144680c9554802c030884044546d9a2032081c2d0b140760030310545c0903c9180180f90180c0301b0010426500c0780d10340045045042c1c071050180c00030340d4040380003140301d40c8050190380c000a01c0c40c0910f090083e0325070348600e810b410465003103281c000180e004640560019130a590401e07008112030300c40341d54403107100d582c08007170240c02d81c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 96201915 1250 96200665 96200707
    0x1804090f05060c030106030f09021008070207031a010305010b120309040b22050a0b0607030206040818130203071803031706040204090609020c10110d0506040207060e010209130c090902 81
    0x268001c000c1046107441c0703c03602640c102c403402d40c1d050020f00465400a030484040c21000303501700305240f05c03411070680210003060b0005403a20484041c188c0d42e44074403c0340d40102814404a030a10f000420521500340903001c0c518508a640f048988503080d0709654078402d4010142c01a80c417604c5c414400d80d54032681d40c020b49488241081080c41c02003120b001000c08543c1466624035003044d06105c0e00b05241a905120340c140c0092901e0788658641c03880641000c42c0c2c50210411400701041d66403200c94490007480c0c894900942c490802d001d02501e8503000d5418480a0780c0a032101300302081e8400c00c06507814600a84031103c3d40c86100209000c1c2c8500d4020b0000706040580001d0814001c0c0c0c010704080780c481c3c0984d42d258001288502c1602c2074440d418421200138480010300c40f040c1d82c00b59402003030003003006160541c0340e52114140c410003005000c09075800300e80301d1000e003000c40799a0082454400c04020f08509000050650321743c9018480c0c1695002c5a104002640c51000b21a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 96203165 1250 96201915 96201923
    0x903061119030c0807090b0a0305090102090d0f05010c0507080a0c060b03031801090f150503101d040b06040c05030106050c0102070507030f17091302070201021c090512031804090f 79
    0x40729250381d2034040c0190426100304000568050006100503202d5081174040d500c40501c19071038001040c0086002d0103004d810360f592554200180303031040e690b2a42a14280340b181166410155490a02e40d08440404414100744003040212030b00041e09030042700c0f0380040904041d541c0c2d6101782401c0c0d0040c00c014140070b070075100c00958203140000064404500e07038001d980e407615243d10b507001111884081e100b5010420a48c030440981e20b401040a10b5001402201e0240c5440d0359191040841503104032a000103107045090000b40083c00c0305d6a9407050080e1010700c10701090000c024850b10051281408210780440c2d41026180300790101ea071032503000780c12610929181d04180801390740c1a42c0803607000c240400c5441d00c1c210000d050701c6080700028840d00e400c000c0100c12030046c0d400380808074114002d100e00288880814161081c800c0029903405052909100c103210217070000802c5400503500c244404039000702203007803061103c0720035140420a0740251420302481c4e07081c000010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 96204415 1250 96203165 96203197
    0xe0408070b041113110301050907051201060906110a02090609070c08030901450303020c010e0d11010608120c03130305280b06090403020708030f070b01050105040609030611 76
    0x8010f00140d428203580942c401c40d40c25840c0c030560245030b0f04442c040405000340020a0004201500e84800e40030350181d1203007441c3d894100700701c40100d00d08100341c00040c0860040602030003010b5203d5604100b04295100625200312240c000a40d580341c02024507200310545030008200783c0c820103441984a60004e903481c4c482c144200b0050180c2200c400d000d1100314240b03803608001c040849500414994215201c00c188010380106401224285c019018581c08118075064003009105d0842d0250350800a010450f910841c020030b42c0c5404220b41e0102c0e030526a05011152021424820803100482d5440c1c2c1d0b0740704800284d0441c06811400340340000304050010502c1004100f494810000b060741c6510601d054460f141400c140c183c01400901d44040010300608000c0e0f0b09580041c040e0045034261070340c94030128035551140c2c090164810021440740200314079131541728054036003420624101810510000d041000a00c0017a19194481c0c403140b0604061504a40340c017000c040c2a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 96205665 1250 96204415 96204421
    0x10b030103260f1201031a010302152203030f121a09060d05070602060a060902030f010302061308070b04051201020a0206070c0f060507030b030c0d02060d27030f0f0e0a0e0408070b 79
    0x82d04c0380040034842a5009212108a40e83d0304500c424494162903000745100202680d003482010541c000d890480881c010014040d1030703078640d1128140017107100f95a450000c4038507000c014601814050b040a1140c00c041c1444120720103400401e000001c1610b02802030703541c460009101119807480900a8003841001040441d0b01155103441442c1c00141400348650785d650b03002c22880300319003032852620164018001072418034000e00c50362003d901150007841d205c0342c00c2d0717040588660005802040008007000107041c030300445010038148100841c00d06582d00800703034a90200624203c02c000068400808110071400444041504201e08112516100340041c0091580002040c4a4880d4901c400c00c0c91500c903007042c40c1c980d4060401070a0000b8040000b0141000d038280c600303031040000e5094004500b0b07070100170100e03000340c2c0c40c0c0b0034482d0310a00140800911034010420000044001d100c1c5440380b500c9003044841c502001400c0c0c1c1c0e60b0741082c401034010072100400240d00c081c14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 96206915 1250 96205665 96205687
    0x140301030501060f14061603120626010b1806030f0d02070311040e1509030408030c0a060b0a0b031609050613060e010e010804060b010c0209100e010b030103260f 71
    0x3c0004d4a940100c1d42054503141c8410859103441000f019500140800120a40211500c06640e2881c03080c02c0a0452000d0510701006139000c0380c011101d2681d500311420b044082900c035002c00b400c8028003c000b45c00080c8041258230880450b19804000c803000404c0d0151020841c0d200c80b42500010f0b43d035240c0c0c0c181402510f40b049440292100c205407201012140307058403400c1c032507003281c1c00200200400549003c0b0080b9004051020303900082c00005002c880a000403c0180050000b4004801e0715213404c4d021145e4282d02c042c0100a521030a01c01081c059045941010200e00b10b010051100300040702c001d08642c00c00c0f6002031011500c40c002134000320700c84050b911182c0350502642003010045440640546c6181d00154128000ca4040742555200e070746c140e4030615240b005803003580c010a0000b4002c0e203849030780c0130035400d0800900486010f402e014100c1102c1882c955491516620840b02c0145c0d490030030003813110070400300e4452050443d01c07802c1d4521950307901c0b01c040d064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 96208165 1250 96206915 96206921
    0x105071a0f01270905030405030a0f1a04050d0309020303091203090108180d0c06110a0c050c010201050c030f070e0a121b030201140d0902040204150e04050c09040c140301030501 78
    0x41c000e540c0000000000c10425040f1030040c00c00415040d01c040c01d001d10650f6a000b40056900541d810300041201113280e8800b0b00001280c0c0303015503a400800c40351880c16484d9505561480c00390046120180320014601250040001c1c0301490007091000761400080d00354031405030360700d40c001a03017082c0d4228108080054a00100241c841038156669500030380c0d000840e40001c01c5072504022141d0403040e00480c0b01003401806810001903070009200a01c1859100c045030001041d101d580503001c0102c104200308180c4820720091040d800d00c40300041d11b900001d0311480840c43e4490008142500c5900c420701192130090580360102da45078104101c1c4041020251303a1400b524003203003800762034004903d08580c6e042e510010100408001e8900c19084026203070300e0161a40584805a5118000f8001805002881094404100d500038215043c03d4665034012401c1c00c0c01c00c01d40500010036684142819540860310a00075441190690540642d205451102100210030300c18154 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 96209415 1250 96208165 96208171
    0x5040b0d05061e0a1203030e06070203041a0c060a050a0f0501090c02101b270305010c11012009030a02030f0304171917040504020c0109020306060a180b0105071a 71
    0x1e140b05240a040c080c041c565400c00f8a0540d404c07401c019002c0102c150411144411140240b500041300807980010905001d000d03204980142d00206007404030480c1886148490b12521401a25181e4401b0900c4d450301402170041004695800000b90407142940111b01c11000c10082040f5540e19080e0f000014240c03150b40c90014890141c16248000007031203040e10403c0d524030b0301402103030045000c80c0d04442038414107420ba161a01d12400d00f038810040c0d0350145100301c0000c25081510b2400a00000d250100516075038100215160050350b0b80c40c1000508403100f52559a488541001c00d1801d80c8802000350544181d4540b0b0f001e501012000d8000c1d5280702c007614001e0724030303e068035640790f044640a41d00884201c00360703000100d4410030b8100a641f0801d2203410103964000042c12600100d42d1a142c0d42d4540e84505c08601d024031140e40d10080c00c9907181c7c2c00508252044025007464814010460756480124000307070302400a56021582c080c1d9204651035051940345103110080d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 96210665 1250 96209415 96209419
    0xa0f030908030a080612070806090a170306010f0c020402301008061f03080a020f0d08150411040911070309080d0c0f0201110313050f06070506010303050a05040b0d0506 74
    0x10500c0840c080e14080210381008295079038445484d101e0008101ca4854004035284051007940030025181e0002d00101d40b18001d04c01c0030b02401461802c190005030004240520481000c00412a50f0b80e040806409460007a1a02c070a003108a0f20126000380b02d45031000d80c1503007504c0c00c0e41d072030902000018413018840c882c40350391940f225802000741d0304c800d000e88055074010100280700b810018618401000411070f601a8803680c0351281c2e03240380d1001d41c1d814010b130851000300d44006000c20076504040594134041e4000d10b02210141301c030146101703100d4031a80e115411040c80d404050260f9000e005076003002c0141d00e001412400705a40b100074201e01043c0700010010340d0304804901c4682019194070b40d80d1403021540e441001d00210010228184405102c1046080c281040540310303242e01e842ca039100300c4d8200307000c0028020030b030084188200000c01007080001c001061160440764103081142d29001c91880540d518010b94000c01105100800c034034180030115000720b03010b000c0c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 96211915 1250 96210665 96210677
    0xb2a0d0608011401030201120f020a0309050d0c03050a050a12020301090b1801030b0c090402120901150e06030a030509010c060f091e051203060103020c01050a0516170a0216050a0f03 80
    0x1880704902e00341d444aa05009585400b24010009940522188044410070702c000148000201c042a0103c1c2c1000000e00c00003035503070103101c0c01c0007010009001710540c40e00b003021007800c43d41e40040c058807400f088001000b10102c4c280080c540581040c000724002c42805545940c0c46400e100000c11080c550144940200603404c0d40a03821010214140c075002400680c03203566491201da841e0303215104858100d41c1c00c01910302d184105008550107a140c8400215026401c200401513200c1c4c0b0383c2084d0b0703448501c5010321a442d5000600c2806055041c1083c03916541400c4c01a140b500320910702800d10b90804103405092001588028a0701e0700c28411484401440e29030600c40c0c00c1c520400400f9a440307409644900d400d0b00c00516800310301450058500600c1382442801d5a20a4035581000e80d225014086580c07584244152800d1343c2d440c025600d03010540b100c50051074090410144103500240040345400380b0b182c1c040c1d500340c100e41103d8142d2810720b00821000050b040079000509 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 96213165 1250 96211915 96211919
    0x513110f09271b040c1d010e0f18010806010501021b041512050607080f01031e022107031e0209040b0603100606020d030c02073002031c031a0108040b2a0d06 69
    0xb01601c550003040c1000d440382606c000d13400700117603501c01982c42640ea10030441c200c40419956014441000c1c0000c50210069552400d200b4906d08035042e00054190f401c085034900450a681183d1091420304403000f0604501d05045109440c28682281300c0e0106001c000e8000d0090000b41580110b0903581ea098407aa280030307154800880a0000078041c0c0d030340707000c2c048040c241a8090710300703140000d0141007103492510b454070100050030780140c0d40d5003001208105208010b061560060001031511402040c15400070754203160003000180340815072804070f191501d0401c01e5851a0a00e51000c00810b81c5440001e03603640601c110600009060012817105e8070302c0800c01a04464999a0b041c41601800c1c5000407864000101d105022900c50b00e49400f5903400c00101c40304014a080703005032008650001400d40f580b55202600290401e01d501c561030740d02c8142c3c0f030f91064024401d1941900c075040382a00b240c5502c500d40504180c1c03c41456440a1508000c0c2442c2c0d16840080040319 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 96214415 1250 96213165 96213167
    0xe0705030915100501030e0f060907080106080604030c080f0403150f1b080109020d020705010c110d030204080618100c020706020c030a111504090513110f09271b040c 73
    0x1281d5007450f8410300c08007005194001d4005082d40e0044805507904003200403001883c01800701c90003005544010001c00812001384100d5003c0d03c86c681c081e01031403030240c40141180014108c010142c2000182410040b0300d00000c0c0c40113581c0c0991041e1070604000d003200f01400e41400000d90052130710b00501b842203145645c002c0c0c0c80c038143e101c04403071340e00c1d040114000350400600140380c240c003048681c00042d8284030384880f0003803d4507084036020f00a40400e103082c0c3d01860310300a0600c100300500a80d440058002e03840300300d4201b101030202014204908020048505002c054101200030b0131841d0081032180940740c150f421644454801c42c10550385800d42d20740039100030001c40700d0000c1070800702500d910415410828914255070b07100710700200c4108036102d4210508104c540d10400683c02c8003000000f0341260000011100e2a0003e035483d60040d08a00840406400d5801c58401c2084410a0001e408045e507161502116180d96004800040c0b140304900d001c00010445e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 96215665 1250 96214415 96214453
    0x12180d05060604051f0b030a05101208030c1209010504110102160911040815010503061003051c030f0e1c080708010b03060117070c0303060509011a03100e07050309 72
    0x1058100005040755250201800700401015083c2c0001d0f07014901600e0b5402c0000f101203004184900d0340703d40d24030b401d1903158111200540280d9600c0400c2004020100340d5280008209030800c491654076183c9034005040c0b4840d11740710680a1188108011451070198000d034400c81c015030f02c05d90444004401282c940c44d8284021406c03100c0c401c0c0910400000d42c1c0701945d040441070b0264545505e48102c54035080f0508100351644600c0001804982800d0210b00e400250529a0950080c25603481c1c54640010742008130305010380d456020000b40c4217070003940107030400030010801e60101400072929104140001203003c030f211004031000502c10442940b00c0c2440d03036a074080d83d07402e0ac2d803041c0050b400038000c01e0400820300f8100c004108050b070312a0041e900c0340c45141d000b0416103000303819180f02d03500c11032048400b00010040048004101506195103807486035603a510301e00c0400f14181c0d642c007e603000750500d208115610340c1100003140100b88000840340c50621070040080c0f5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 96216915 1250 96215665 96215689
    0x70504020f27120f0c09040c140406090c0e09131703041b140f3a080a0207050901150e011d100f03150e06010e0607051218 54
    0x1d140400c0005503031010b803040082e0203205000e6500d00d01802c6070710024144aa402c2000c04041e003005210000400c2e0421001c03034201c8080d560340c000c0d89007940340d8441014441c03060b5051085505a084103039501c661003035016100d9070000300503200c3ca420f0010b190380c05000190f07010350102804140301400240d280c0281652020101080b814400008012a0006041203d0303166510a80902907626074041c9805080000000c0320100780300c008100440200c4804540510400c00a0603612340d00d0280c00e680030038010002440e02d0140301d5800c5822108054080c00c1c41501141d50a5003503400714aa1089850842e03001d0000d9894845500100300c00c20150004154802d2100c0d94a5024006031355403103000e8410011000704800100d600b03e00c03002c11110000f85600281c0c818281c0601c9501d83c1c003451102480c10780ba003000c036400c40d0341802500090500c950510138006070390b20b1008948103130780d0000c01d88103800031105001d0701d0303608070122440154101c4103981065043c000781c0119 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 96218165 1250 96216915 96216937
    0x20c0a030c030f0305040906031b0608160f180b090a08030f0d1107020603101e080a020d06060f090204030c0605120a1a0409050c030f0c031c0e090c0a0207050402 71
    0x407640c90340c1c0e251545105480c4049042c8201404001009a1548501c00045000e0181c5901040da1400001a0121113030004810701c01c1ea08103011342c0e0000b900090b504078403682070248185000110940b42003054501007180d500340d80d0303c041000b50444e0041d004545e81928403c01d6251180f50a9032603000d4040d641141c0c45091101070030707400803074120780c8175104204401c43c90040160045010f5a108580d54040b140e0140010011241500c034150480345000c0b810a00c05410a203141d902d41444100282c46042040c0c3d0140501c00f50b544010000c204074a5441c0480d41d03103000b0200030b0f4001388000d50741862000d1000545034010404c490303600e0650b18408680341d441640b00340050458a002035048003a850551070243c0300c5100759184640550010250700032150704151400c41250b0a0414580100384250010380f80041c2c0155829560082515107080900f0121941140c20f9807041c0c2c440c0b00f4400f84078103036110000a0000503110703400da8082c2c41c3c4030010300040e0300c50080541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 96219415 1250 96218165 96218183
    0x6070f0c0806010b0f090f04090803150909070905150402030906040b060102160b0307020a060e15010f0501020c211506040c0906020c011206081506100f02120c0a0f12020c0a03 77
    0xb8105c0030317610020b064040c002003c40d0200c141c03540204086070601d244c1264512800003d001d25032996900c600c40018048988000910742140482e4a50003c0d2290302c0500d40c854003c503800d44626507500e0152100175108649a2601004240da0b8480a45003034400d084204040385441d480400d080c248182c03070030050307140f0b180b50180300805513000421000c218011040384030002115801034041850081c3c00070120058140c0700c0c540100010b1780301d61400686c0c560104440d9801050418015004452425188503002003c20070201100d08e4000140078011000c0000401003810a004207000d540c01c00190503c2c100c1950101d807180100c4000d80e01c04c030740201040d849080011100302011a0200d140c95803003541c2813800e80e0305203240703114481e03050410903d41060182c103605002c592500207810009080702075120544038141414010000a083e07880079820803441d0030556000b1944214405d1600303281840364400400080180600c0d0903010252900d09102c2c0c080d00d401900308 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 96220665 1250 96219415 96219427
    0x11d0a020a14100e030a050601030501020a090504021201091d100606030c0509010c1509150b010e100e0402030417070f0b130b0a0905011104080706090515070b06030c06070f0c0806010b 81
    0x1340c03207900d02d003000e10b581485541e51010015505102503402107200360009a00d5088075030016001a04a41140340503034414828805181b04840d81036045071240d03400080c10410071414040e4000804894040c6449501c00903100c5031055440a002c594080e6010000f24072041c40407291031003000340a070b001a407144074903c08101300011316007200d002003e000800b00d00316628042c0c000072420351100c24aa03a00501d8100e541c000210542c4c0041c00c85000700f000020301c3c40070708081000310308503000325400b00001e01081002c60300a0021281d1381405901c80e03405107480d80d0250005203084520144110200300c515240b0111681050350000c011255a9196041c5100401000d5801d4425640740c1d1149030807104824002c1c005820b05d4405028000c3c2000c01c0a0403118032a80030b00c1c058070b01040840341c80c81c0c9420603186281d40c4500c80341496142c040000386000e80440090b80c1c0048c1c0003485030204607a02805071005403051000c860300903583e6003100c0d1945403d20841010304002c02a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 96221915 1250 96220665 96220667
    0xa0201052410032c0f01201303150519020a02031c1409071502030a0509010309020d02041104091a060913060e011503150b040501030e011d0a020a1410 66
    0x1c03540c124943c80e0000d8501141c00d02d404003c0b181214540144000000c00c1d01c01240a0000e40140b40c0b1190091101401ea280c82980700d9403403248071444900302085004000d520140d481005641142640e8a544001d4204200900007070703419403440c0c0c2d00403da0f103021607414026a042d101d510f4003d9800d0068480251040200c01da00c54001c050b92040c4001c054030010304100d0140e5100c80091068a0621141c0d51910000104030003c0d035105226801c81e041d8071001701d850415081c40c0108185040d0310215405000c580002503102d400d051040c55088141c1c000782c0111781c10f40609025590100e0b5514a50340d20000110341c0100040010400c0b900780040e04070ad00d46800b000000d041c0d951000c818a10003420b070060388625080c0d85142090355414020302c8142e02001020601240ca06108100d0a01c00c83c414981810303214212500300c41c0084d07214421544103441007080212a008541d038440d0213140c030807031144144110119501c550032491080b000c0020744040444035403000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 96223021 1106 96221915 96221929
    0x60310060e010b07080c0609060a140f0106080c07080c0105151c03120f09050a0b100f03061e1a0a06050901080406021e0f0a02010524 59
    0x140c28461100300e540401c1c1103c0c00c0c21802543c41209240c81e104500801e00b901e440350040c107040060a01010414503c40d01c2c00d18410030003400203506911081c00282d0fa19817940007400014060107000d01802d0703401c40d00b40d247c1c00c0e0805100d80e50ba408190312100c07110b00265114070a001502c0703410b07900c034008400204e8000044205104180201000e40340028040284400c54101c4c1d488252340300000c844509034081c1302207402030900a40d00d60b940d43c070454403c500c0d8000184013150640902d0b0035201c41c030710091119403031030703c51300c010b842040890b031207803100701060551a42c0544903509a94400d00d4890696440f1081001030442030b80d84010b0604c036007000450501c1c0c0c2d20181542d03211340d00040c016280c42d100d0082e05100001e001c20900911310016503261803e4012010f46548079003a0b00034801582ca01c1c018100300c88900481c0b0301c0030060361401101d00e10b0420 = true := by decide +kernel

theorem cover : BRFrame.Cov 96043165 96223021 := by
  have h0 := BRFrame.cov_init 96043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96043165 ≤ n) (h2 : n < 96223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
