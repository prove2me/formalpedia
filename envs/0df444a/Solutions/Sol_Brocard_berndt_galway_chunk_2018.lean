-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:40.314985+00:00
-- url     : https://prove2.me/submissions/c6941232-6fc4-426e-8b44-0c2376587178

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362769784 ≤ n < 362949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362771034 1250 362769784 362769821
    0x622030302060c160b040201031103180d050a080606091c06050a060e090a0213061703030618090d1101020d0c05180609011403090a05150a0e06070c0b1306 68
    0x2903140103032030114040c101814540c0244000c80041e00c0101c0d00714841500600611840c3c2c4660005030010880204040030408000081100c9005e01d12402e4003000311400c01c0340c3d401503c191003180c81d40075010700400000e5001d00031940c546041000783c810140000d2427041c240c00c04240300d00701c1442040085842c6e64550081000c41e40302e074800c40d002482604c4840c8007070b20307040840b00d4a41004240c003d10400c48a0080740c0e42100a90118003e80106074100106482c8409882c0c0c0d43d400854810b489600344503081d4401701c0754500000e00900c4090300401c900035416070305581c00304030b010143c08030799400c0c010040303540c1c03280c0100340800b042c68036078640d40c0b00c05004084880e02030342e65013401800104030030249079030701004001910740d00185c80c94603511201086800c1905249001e8103510451450481d210744c000d141740d01502113007e0401101c18106100c070745a040864080004c240c100d00da00000c150007001c100c1d800000c40303c2104203030741c0310b6442078112045181000d090448 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362772284 1250 362771034 362771039
    0x20918010606022107020603040b04140118021c020a0501081b0f0a02010e1c1202091302130f0602030304080a1206080f07050a0b04050f010c060c08042a060302090622 73
    0x92144c2d0702c41c54084541c1000d03103440016008034030300b0b2002400040011200d1000070f000e00600c3c0e402403000c0748004000380880710201c000500403000c031101c142e126034290344001070b440d042031a40500480d80070380802802481c00005407104540100300078501c1c04080107408804841c00001d040307412444c0491a103a0b07101403002400c6811000c542c1b96564440e140c0b502c1041180b40000750b045240b458000ba6480b08034004601074003036411015046414030307480c003980c406983c0103004108900c912480c089542c40d1003002d4111464815107001d43c10402c08100407500ca10000c14509829007050b00805c004444140c0446010782d1020010341c102401040e4002d50501548e07004100031602c9140ca142002000e42319841075105091180700502240070700f59005e0303540218500c1d0000c40c02c010b4075001c80400780031030f0707011101103030400c40c0c42030105845040c1c094103804918a40051004090030104150300035800004c106074401414000d12004c80400d00300c030862051b6a8602825a51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362773534 1250 362772284 362772313
    0x70201020307063902061b0405090901050414030a090513091a01060801090618020a020f0717071502030315030106150210050a06030f0303020f0708042c07050702091801060602 77
    0x107041c0d2081c0c0c64805102c0b82c2e01c01308240e00003034041d00146041d10303a48405500c41d08104803441507622041c1c110040804003c1c41e501c06500c90751240740941c0c00034801400506004c2c2d00e0b4864007903c0408105841428071981c240054002d000a14900b000240150984c8541301c50700385032000c0070258620703940188402c5600a034030500404a03643c043c01000d04001000d4403a4148000d000805a400304078060400e20070008a6084107583c01903501c031740c2c1c5584510183c10803485a1f82141d1051400000d80b04001402503056111254050341c02c1d80ca808800341803042204505507410364032000c0c0400d018803000d0003c20b01e1341e020340061405000045d50442501d10040a440c0c0b4a80350403810000708444031000c11920f0780c5460010f0b0b4402d209a8411101c3c050707058040c02e02c0d0f20119010441c0221460010f2240d03010501040b02000b00100708014142c040380c066001982c1400800014180780301c242d5000074901c00600135080380b6460392407c441e655444500164002006000ca41 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362774784 1250 362773534 362773601
    0x7090b0706020a1107050d0807020d0b070f0e0907081f080d0e011b08090111100207080901021605060d02070501060b0f090913050604080d020702030703200402070c0b07020102030706 80
    0x2412a4041c0a51a1404000070480719558101600c0300230300007460f07001c556480703424043e07003035001c50148000e081c10328000302001032605214011848880c00003040340b42c1059510300c20881c907501c01e00a03a5070700203400746d03c0f2034200601c0d001e40c0000c8004910210240f214810030b4045649415000320b032000010b100314481451803002c0446842d112020074014000c0380d140003028281452002d00d0012564a080c0c8206040c045562000ca120304c208a120780040140d42002d03821100100e003e6003a40c40660100e1181550004003080901d000c80d40680242c0301d41d900070000014015510714100e000380c4e01c18036860100d03420005043c7c02616110b101c85801c043c20940884030650305559196950707501038009044800c022405490003c0705030120340203140c2c09802d40b40c00994918210b010b103046150904481d40d868400000d075402c2c54402d43d9003854200c80703c8000c40380342860194880d03000b080240c0c1140000c101e034001040060096981140321380c24250041d90030310740d40f561030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362776034 1250 362774784 362774807
    0x503030a0f0203010305030a180e0405101a030a021540080c0103090624030303060801020708070209070c0b040b1611030a0e01050c01060f08060711060f07090b0706020a 74
    0x7080c0b062006101040c0000182c0c0ca820303c0c0c1e414103042c00b1040300e2907001c0c49001c0f64008050314a4078010802081000300380143c4a881c000d40c1402104c844440c0b0030016400c03c3c48a640507400b2003520405440e221304083e010b2664000301e41e1400301d60040c010005001c40c14149414600700003c0342c0c4821452421100400440840d0081390741041c4505e034444d0007401502781015212000070702030014550003000700302c0321942c0d0a09245040207490f400f50400307200a40100b403901b1800140980706000315422994803440c3c1c90324014a503820081c1e840c0000e44940104068041685e00007122440c0c542c0c001c80c020b04500c031242c0f506201221040f99560305140400c00e142c5641c80f0099000829208903611a05102c0704041c040c1d401240c1500861031074119540c2090300c0000d0034003a2000e001d09490300c0400395526a85e03001c6050320162510004090b00d0360102c40001d80c84081e901100360080c10b00c0c540400099036a03000c04020741c01001099849030b90010744400001d81082003140c5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362777284 1250 362776034 362776061
    0xe1f09031a0c030106230d090b070f020c0108040809190810020f0d02090d170a1e080106080a02070606030602030609100302100507051603061506050f0901030905190503030a 76
    0x1924a05002c058031940818410700d018001121400615190f03a8002d00000750320803e803494480034280d04541c003820b0345030b20a550084e0900049100c0e140b140910040141240d001445400385000044a44d450000e03c16131b41c3c1842841450070030b0395401c220081d0740390302141c02d500480c14240b100c0c0c1401060041607071014410800c1c0c074050b0440100751030b03c0300c41d051001030715414100c01043c18140c005d04001e02d075150740244c82e07440011480207086003244c9a038482071005844038180c04100b200c54181404900e0341d100420405114000495006606c14000340c280b60340365441405071761480d0012928a0b40110402c089400d0101c0e1142c4d10421242100321014a1500400c0c206411000c280381008000142882406410004e0068281100c0103c5800c503940b810020300802c3d5242100365803001070400042d40510a80a07181e1910790314810501c3d0120040054000f044114001c490500072a808111090040e1070040c205c0782c080d402941e03980c80d04210800445001080781c14 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362778534 1250 362777284 362777333
    0xc0b21070903020103090f0f08040f0e040b040602090a0e28180602131206060f0501050c07050906130903030b0f0a0605040b0315090703060509250e1f0903 68
    0x155031640000c01e0400c581c0c080c2000920702620303090401c0740d400c1c0c5500150004139249814420400c00f400244110b40d00e013401400819195049807a00802c103940c083c01000d4103c01003800308150f907006004140d00205210f50541d5a0500b111481404840f1071402202c41140d6101c400902001c0c040341c0404510100040840c0d6080300c0ca00c140c1c8480b01034100d84e4041002c40c101a071200581e0090300700300e0070b0205203528514180300941140d000c0d02940e501040800202035003c1c505070fa259640c2c400103400078605102c04e0100d4070000620090b17000b1007001d105134100c5158400c0c12809406a5400700d0200b06581c00d01c082440500030141c01100040810403099900100341e4054814007007021b640c81d00c441c810002143c2100242d01d41c003880c400306110f5000c0d016800041200c00c1554078a80b0b564401000d84114800c1c1081041d1207064035a8034a11107101d441c01006607503004203250312050349060524038100e04034030f000010908a01080c001e1000500101220b5a000c0340080e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362779784 1250 362778534 362778541
    0x17060709150c030201150801020408010612170a0210020f0309061602250302030111031b03010311121203161715060d2a1b0302030a050906070c0b21 65
    0x80c114041514607281003002e928162410103200390800801c024084154020281c0c482c2210780c001e500a11030910190f10b0f0540004425a008824041c0e8603045920a030001e0b041484040c0c01d0341c4801d10030740843c090b01d004400c0c545800d20181100300141d000c41c41e100d14040500700d182c0240a02058810014140080380107540068481141c200c3c2c0c4410460640c0c0d81201040c1c12a03890300001c0d850f50801c0c41c0040c0030341c000c00c081e5129200b141145800c0d1058640c152186100c02c1c00701401e58402050741a006041c83c03082c0d5260f170703018101200d041c51419507841740700743c00c140c901c9911086100c500711030706a0b12505249950381400d00803c0c0394242800a4480b680714100403038012900030450003914600c42e80702e5400029264241e00c40344184c628904044005032004001255042c1d0319400800d01c2401603000140e03143d001107251012115003511240c22100c49541e02540420000c000101e0b0100080000d124000e11662602c0c502d4850b846100340d894140a1802c0700c2c20b041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362781034 1250 362779784 362779799
    0x50f0c060103210905091302010e0a1203080a0207021806010c0614060310020310120c030609050105010501110309030706120b0a140f0d11090618090a14011e0e0309090117060709 78
    0xc1c540140c07003c4421a4603110234030068810035400000c95030302503800c4030000741c000f21641c0c91b000070b00d1007551402800e40c0d43c1002c0404a00401d14041d40105209000402c80c140308468a600308605061224810485a44240a4400483c0383c1e144202c1200280841070400f040400c1c41d0781600241941145022112411508400e1103a800000c0340d48803440148408682d82102454109106011003021410454044c2000b845210700290000c0c051130a5140007001381e44800000502500d0101c0c90010210783c80c28000240307509803507440c890303002582e494800391001000000121a07000d000700c4204078810b82c549103080e020f8201c0341c001c400000c2d400301d546520100f04652000141d1620760104112082d00001110001c1804090003000c4000141d840092031080c9504082914014111070a80d41c030062086440f03894a4010b501c69145900400b040c202c45034100c2c1e04001c160070000f04184002e07030064010b40140d468002204000384846940004e06060190170946447c21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362782284 1250 362781034 362781049
    0x32070f0518060d020406030506100f0506030c1803030f1b0607030510030f03030f06091a061908090c0a03121103070b0a090203010f0501140901081c050f0c060103210905 74
    0x1c0e15101c2d0311145050f40031540d455100e107024540003000c45440b481c0c4010a100c407452580a000d04950b216240064a494480116407241000e0001182041d5050070710700c02c420124002140c1c0350005010014800c80410050018030030b4005141c4841071200003c00d081c100b014046004041c141410060a081c226105a040301e41c0551840e01c103c06c0c50404031300901ca0462001c0005044c0100000c4204181c1c108062005160302d0320b090f1000b614080000328411302c42c9400d5809104404621924002c0031001e521001f90300a42c1c1c115640c04000411001c00380e002101ca011a40600c421190742c002d0407580310008000c001c514003109501c40354540400103010400700e40c0c0300c000740c80440d1020341081c00040c4581200b8445940c490b140c0d00498202112014010510b1100003d10008005041c9407004200c000400080c1445401121180d01248158200031400c1182455003202080024001c600540c0d003880c064451282304000c800004880c00e040011008091115a80e50304 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362783534 1250 362782284 362782291
    0x1f06030b0108210c100f02040302040c030504121b02060a05030108060c0930060403120f09021f0c0c230105090108010603020d06030822080607080432070f0518 70
    0xd142d8680210002040c03a114480035680111420404140e1081c14903401500540b071003200c05000140ccc80c0241141240c004503009043c0700002c6402103840c9019a150f1701c901e1003551800c3c1400e0360b8580101c0e020303521440001c000110000700410840500f40f140b82e81000040031070358074191001001035070300f0442030081ca5000c010280c3d003506c4140055a541e030702510035401d551440c5400d0502404103035030340061111040c204142c40101100600c6405a030030b82c020700308818052034204030182400c5c100c403c0f00c28010041c601001050300241400010580c400c2a0103810071480ca25100c1d07401c020201d541800002e20100006030703000740ca124191946450700603140c000008038017028004650001c0c1030301c24005150881744840b2100d404c00c400e0503039a244100c590316020140d803407000f00c034100009913443e0041000608030468600100351491854410414080040e2286ca0440c100c0b0810303d6200044c2000046112180e00004040403100031941c0d03907103121401043d80d8000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362784784 1250 362783534 362783593
    0xc030718050c0c1510060507020922021807180b0306090622060509010b0c03032409010b03041202010204060e01050d18150e0712080c1f06030b0108 65
    0x610024854010361020369103203110034000c548144c03680441c1074124520540d051002145800008074105004504481d822540a05440201d03551010442004040045d048882d000346164000140e80c0d20b00d0401070450506014441c981000d860107030400308001c1a0f80d000380003c58080244074115000c0d242c1c8104165412501a9100f01c00039151054030004080b044400001100c10300c20b5660103107003503510031f8410451690b2200c03000d200754042c403800c5001c40d40c0204001000c4049103002ca5090941d190714138050060b40600040c5891001d070400382d010740c804002c000510103d940c140c01600110b0000314036140c10160000c000f02040b2000343d061200015440c0d00d44800ca82c40404902840d03040c1070000d8800f171400b05400000310074a10080c1d41071610900603901c000c079034a0116a82074004038900407584e41c4401e05500182080a0785000318030180740c00117020b04400300800104040010240d0071858140c00c0710b003060300010078035481030744002e1282248440001982c440c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362786034 1250 362784784 362784791
    0x9080f040e060f06090d0c081b0108062b030306080106330206150102030c060a0b011701141201021e09031b10140f040602010f0c1701030b090721050c030718 69
    0x41d800c040d2001c0e54550700542c2c149c0300380403d408005081640901c04031500740e840c0c1090361aa1070030048407030408940a40043c0402c14651101526140d540f60954401d0601048095690034518212001c0c1d9008070340a41126400049500512919014101c08411071003071610240d54003d644202c000c00301080700c50603090328030850b8020002d80708079a1400040742d800d40791404001001c3c25180900ea0302084d84103038003030200040d4008003416110803c003d400240100f0007000182c8500151198444d503080000d00d440e4402c4224800051005000c1a940d540100303040c149403914950180f410b602285000c0031166451426041554401c0d01e450002c1a0400646010301d03c900c201803012840c001600080703641d01074201048807854403404100e03040e10918260341c0c04480c107002450116010005000140343c0211003034201c4031400480f1040ca44864581e444400341401c070301c81d9624110781d89010014104802c201860095020b007600074600003041c50740304980b91412030b40c2601d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362787284 1250 362786034 362786059
    0x70c0e06010516050c030706140d1e020706060e1003031d01020102120f0106021c0e010c050c040218120d120504020d020904062405030309060d09080f040e060f0609 72
    0x1c00c2c419100f0050144480091200d102d290a9030389482002942d4000d01904100082650165065014040b5520111031508000e00c800b00020882c0c0c14103400302c510385d01c0221706e0110075803014140180c030841c3d001464600300007860f2807541004050400304091080c0c10b00009520094030340b2103418181901407013940400041c1d0180c0500c52000b40100000c1d0704020050110400c2107040b038400340c094580b143c004602962032150305810340c0000c04d0300701060203140d500c00d000e0110100c1c002c6094880603500700001509a038410a0700119040100c40003503038900c0e00d03024a250300b000e410300515051942c550041c142000c0010a1045c2c40c1c0d03590700140664407442845500c09600524543c01e03481c152514100030002d0400b180c2c40c04041c450806558240c4180e04010307248014000d60501c1c00f50004c021065002212022407151100030100000d07070700d00090032014600c1442c0726101c5052900040e8404802070245100342c4c24050007090f562901c5c000c5404900041d901e6105000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362788534 1250 362787284 362787287
    0x60418060504080d0207080a18060e060c1c022505010903031110021614010c0e10021615110102130506210a0e01140613180804080a0b0705070c0e0601 66
    0x501300b0f04840042c00066140c1c200082d00008110040240c1c03955141c9a19480012454800c01d001e0700001c5010000d0a040c24030f40312003e00302984e441011585007c600001d15900c0d403145c4290300025912000c0d9820701d03022908000c5c2101c43c050b010140c00f40e45072100092040896101c083c003880529001c1d02c40b5490203001c0315075586200c2c20700795551a00354100e04400507020100341d80010850040007120001030107520440b181990399401c1d00c1030f594081040390444d8503420001d41c0b2035006540b03091500c1c5c94004004011640314840c84400313200018115400024048032181d1040000310b0f5025074541d00b02d800c0c0d400c1980c1d0b041c4c841c00c404c3d1807107100c4540491115103a6426500300118010145c20250311008110b0003800200880341000c1000682551038940c40507850700110690071099214a00303600040f904d0042e141c4403134130350030300c554000e030440340341c83e080b00070a0400e022126000b1508a00c4515003145000c503541c135000d00c50740084c0910a644403c04001c1611607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362789784 1250 362788534 362788537
    0x90207151503120c200922140304030b01150c20030313090b0105070203060f15060a020d020d0801080a0303090309180204030c0902090901090b0612071706041806050408 74
    0xa43d4000166402503000d0f090113007098030903900442d00302d10148419190041204041c0c5142d0802801349262600c4d0341d82c0a1514182c580c000560b5a5040d140c2d8602007400071403105112189207000d190384a0a5040c0742a14200507040340340b51180f002c0002003010340c00380d100100d840c6c00002841c8206069403907a001e034544140d80950521010404d0300c000241c17041c40e18200c4082c0901000008080c400541d0140504003001c0d51642003600090041032b1081c81140c0d1004140341002c1a00340010000350741038114100850050f48608002142c6e00d404201c81c56031000e03031f420440700359131400000581e03a84844100408144c2c41d01e0040023054003031a8003201a054440300f403555515a44000d02c02900644800d56080d8182180040d682502d40701310b8080d07500281018986a0805091801500041c401c59400c090200070606845400000d094010300d201d0b5a2030101d4001c0a141040d0b0b00c2024005a100350720b41500000d030172a607151811046548030700040382c265198106624503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362791034 1250 362789784 362789789
    0x1506020a0b0606040b0316112a0303040308030702060405071d01060f03060f091509021e0304030c02060f0c01140f0711120a050307082211130c0807090902071515 71
    0x41036008006c0c0501e03501f901c0c184254044542e030b60b0904d4035034403480607a61758500d611600d01e480d071042061030307088050071110400100050f0032a4605075a83c1d0303540705180d004607007800050708983c0a1204100741030181000602e8601403080e90007440408441c01050103104150a1105136044040040d00a4020070300030400e0400803041982d072141c0d00c001522410900e10394114040b50302284120310f078425180303c00c3c9000910007201842c0781c0c150b94180d20103801502030101c65060030340180e481d0303001041c0c65082030324180d0b120112441407030f00351410380f043c2c0f60aa0300d0b41c000300a40c0300108408554481010310b00f107001c0da4400707101c0ca410900c6800d4000b01c070780310000700301c0b9034690007034021401440c10742d54001c1e0b941c1c0e0310b5150362200680700c003601e0701d14110304040d00040341010bd0b2031010710000078444035080070300e01300040440310341000c507078089403024040018103030f0001e101000078420341000b03602d003600950701d800030400c0e042544a00f80390b48150039000d0810f0749111002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362792284 1250 362791034 362791049
    0x30c1b0d0915110712050f030a03090b070503070e060a0e0306010801050117031e0904020912010603050606041e110906040f08010b0d030c0f02060903070909061506020a0b060604 78
    0x11180030508009210310301e24012802c001c0c1d0449654039410b0f2103107a40c0301c51061a0b1001d13010250801c0c1403222040755601c0c050baa103109046400c6c45a0b0803c0c0300602c51603029440c0090840c1d00d41c0b404c0d0030960310041c07020081c02400d00c10004090f0f000031000c4a4003030115415a42c808400c00700b6501000000e201c10381611513000082807c0741e0562110b130589107100801c80b82528100e00b0320381c0e24403d001000c1c190340742d20341c40300e0f0302e240800024010104000b0409030030b0045d07a101181860301060800c20103691101c104005001091121540200082d5410b0000600380f00d01c2d0400402150f13582c10b0307400e6444150022590009050750b10602004011658035a610702e00070f146207049014a0090394070740710103203031640790441d000000160315441d06003182c2c245407140c0741c88404600080e80c004808008a40c00c0380e40601011010b8500c5482c00140c1404501b425411141c071032004c8080b07468401400c2c80007507000501544001e92105203540165241400314132036028036841170320b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362793534 1250 362792284 362792293
    0x1107021c0c0f0e06040e0c150a03110f070c060503070c08130902071b14010801140d05100629090904050c09070c050f120d020c03040b0310030b0108070803030c1b 71
    0x5041000084111300481045a051102015040c071403515100d4503034400382e2001410803100c0710b982030240500392111840c03d0000384030989481901065018825007135098400040d04020040d03e003075410007600c3d040c54041d040d0301e0005000303061504154000307808600c2c0850307070b0002c007414081d2742e00141601d00003e5440d1909031410007605070424a45a000c004a0400821411080c41c14100b01400503036458105903c1d155036200e110900100300f5410400f800c0b8240302103403041080c1341d8070030070207200000e20a00d008135643d5a1040030b0540f590b01c0c888500b001160180c80d406803000380100300d07030302c00140d2201c0c5049450180e5150341150044d44003030820201c0c2c1c1c0c0010f4480d00c40c5d406042540c415216019419444040f151500a51001d040c0000c4140703407040d42c0500b0340384000b0000c89162503161240004070350000c0b5525821801f03484002d10420002e00301c0b0784d0042c030303a40300108107a60401c51604d44034003004004940405002c11110111303045009040c08c0d005c80c420554 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362794784 1250 362793534 362793539
    0xd090303032d0b0d02030703230d0c060b0409140304080d020c0a27090807150506030d030c0c0602070b10050d1109070c0213051605040305060105060a030e030406030e011107021c0c0f 80
    0x80c1d41c983c9c600d0038a10851828460403034000b01c0b0100b030701148445295a0725944500f550750b80002450714139412030700265507d121800013013070b15800c180c075035084000554407249807002061414038850076441c03c5421612016481d034030303581c0d2040107031124480010010300c10820741c0c100340300e404000382a0703040c10008000e09001040004042c5240030b0039059801c980300b0003955003a90b03429a02240c056100d148000003e9101b58044901800f4074a41158009216110181a40c200c801c042c0c561090480c1800150307030342e12849000620b020b8034891602c4034140c840000a50b02903510340d0003405054001084548100000c10140340d00420340746a051001100743c0080104889103004512402e031804500c5020700141d42c11a0380c440010f0256078208000c0c85107603004240c1d44810306486030030700303903840609101410107402556400070700207050041160035643c01c13540000213444100600d00c0942c8420400d0580d1880f01c1c04d03d20341e007200b107141581c102c03019030344a803440c0c03442c100b0003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362796034 1250 362794784 362794793
    0x100e061204110a120303050a0b010804150e0f010b0a14100e0402040302100c020a050a081020160b0106081b0a1103030106180b09060910030b030d090303032d0b0d02030703 75
    0x4c5180c41802a80c081107190f42d00000103044808249405010681c070600250004690b480682d00f4a10345182c041340000c035001c2824944002ca5404100c140d468110507036460420300741d400010034540802025084940010600301038202040b101000406002c843d560b8540780c040b03c0c02158007410074041416040710040c0720b460707440412442080841c034000340c03500d40303a2100b209540182000e270102007848404400113102c8411b014a50594211030b030829545081e001c0c18100704d00c112234404200651400c010514016084601404510700c103000081d4440050315a01407050030900e0394a01c280202590a0b020000d8002c101b480000b001041282d440308446150b0003072521035007030040e19860f07503510602420942981240d004d020386042803924820107070420316603050000c1d0105601d8042424028a000362701d0119003401c0040080580c14800d40c00d410781850b1080403600d0860307412003080b1881130f41040001c1e4490000100b030b9a69500344000c440e5008046810080d1b42e89070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362797284 1250 362796034 362796059
    0x20030408182101051b09040b0f0a0305012f16030c06060807332a08071e0f1101020313120309060903030f18080307030e100e061204110a 60
    0x2c200b25424600440c20401d90071400c00c2c0d2043c041d80c101030030b290840d401e0000600034941c000f03511014220201039a82c40d640c814174081c501510022071000c4040c5002c2426521141c1ca03000e54400400401d40f0010340413042e224107440c44092210b01c2420303403c007164001c0c90300c5c0c805010581b400100140030000005d42d11b007110402080399044030401d03e09226840c0d00c030495801d81122082081036175a10564032803110681911056400c1030010110510320260070004450300000003071000c0c144001542d4070802d20b810200d41d40721140b01c036602c4007400c08005800402407000c080c0426a642c1c02841681c505081000d41240540da44110308482c2c92400c42d401e6000c12880749012403a00c0c4110410801d40f601501c846112010742801291500d20302c9180c21082183e03020003003080d80c02030000f843c28a019075101c0700b186400d013041162201841d0303010f0052111101c000c80041c1c603040161103440900e0320303041d042d556441c1000044000d20420403a4008403030900401e400d0360307851 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362798534 1250 362797284 362797339
    0x20d12080a0b031204092f03010501030f020309102a08150a1a0306010c0c0905070815010f180e0f0108100605010c2402031005042003040818 62
    0x520030b1025105100505443d0a0040c2410b1001601004103014a02c0c40b0b4000c032a845103005001074004485220100d1500184070400500300e0b000070042002e0741e4940140d110a4000040440c0781d0708103190302d140d81e0043c6246404819490381410f500d81c284401d05144288089506141310704100e003401010218100c07850b0b22001180d10455200b4244416190305527207095082d02214090b407004901c1d903401c018034150403c1138008080f000580234170714a1004262103100841d6a05007a0009440c8202c02400340c41c40c03210780c06188040760f0703010740303c00307031030720f40380c2400d00300e25111a40341d500d0038403244c1040c0204e6045006001c00a081c800343e085c120b1350707180155901044100070b40307000c3d244d40e8851140040c00c140004404125803c4000481241ca01c012085070f00c118a100c2003079130000c64200c0c0c01d141c046c160400c200d05160183c424880c04442415070b40c00403881030b0051500000d80050107048001c103900413100d20100c80103100460040420700316042c0d10004201440d07161 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362799784 1250 362798534 362798551
    0x1200705060f040525050a23120316060222031509110108090a05010f02030a0b0909151902030a0920090a050c090a08010c110303040c0b0304020d1208 66
    0x28511404000b0058000c0fa88500600010301d40004009580248400c0240d9401a401000203050340ca000c1c101c0300804c1540c017100c40310100c0c102d00f18903951050010602503054400d00070301500000c812120760100c1d81c580110317002002e05004000f4010703078440c1d0690000c4110001002c0c000e02c16140100d0b403060300300b0100141c03026544402d80b00740310340042244441e01400c4101358068940242d000d00e940d4102c034000e02840d11581d00b920a184402c203400d03a80041401500030880c065a644084292001581401c10303621003a560807010b040c03001943d56090216a8503c0084112500600034000c299100d080468443c001401050000c6402880340700041240c051004140d0f41900b200602850035940c60072690405000b00078900003054108004110f25940e542c0b101c04003424540c130001510186801c4040c04e145480610344070994414001c120000344088641400d440c54801030f10f07102d483e02c1c804550001810400102172240d0350750340180003580300441d1071084051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362801034 1250 362799784 362799793
    0x3030c20010608070b07050a08090f0306040b0f01050d05070911040f06020c0103140f1612090506161403040f080d06090b0a05011e26090718060b1b01200705 69
    0x40d170030a11018440d801c0c005180340c000a0700703003001c64041d1020b080c0f1844080c00000aa24410740000d04148040301c0c116112803048061015043ca40761115001d04016100181440380d0b07902c03800c2c0d0b07900c29032042c2c0004c26114442c6104207981102500c00500b01e80c084000785c070307495a034007170345904076076500500080c640071820440c807840c084182d001e4004800b03607800d0394640146040e11a04511400703000e101c084041d142c0000c2d07003031040c804414054005054913041094400c0941c0441c01c03804010018980498551003507000101ca400c26401010400072288518009119004024110003158a0640e0005025005410034005040304482d5070701c0c5141c0329001541c81c4450300d411134608030b00050ba0300d400c0300e00685510854a5000089050038490b0702c4041c06101d000701c429070220b0304000d50810140c40d20303507142400145000302c1401a00c2c101205001540aa0400030b036880da03139010b103244a49401c0d13100300c0c4000b4401c106850b0f80c4e1841e80154240382d006007030442e0035108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362802284 1250 362801034 362801039
    0x42112050a0207030804031b081b12030103171c1103060f010c030206060d0c2c100803030a0c1101151d0606090f180702070302040612050a03030c2001060807 69
    0x602e208680c4000d034141c852034200d8440340c0301224a03c07940b00200034010014440c0d1004121824040e209080c8100348401c0744000d2401c140e400d00c603489642501c000814001070000452201404042c81c00a0f04035070740f200ca14200c1c0024298260b84060300d01d51a01d460b1800f0f25907903800940c8200d0040e03a0441c3d03800004001110340040303800010b030050b0040c034082215850041050b501040c0a042c0c60003503a41c4901e55070301c5059011554100750280405c01c088070841c0030488030780c0311050031420280540b070710002907101d00c0300900c121000d03641c031040100301c2802541e440d006141000000c100c9038201201c201c0c92450706001c4c00060410070764010442032540c0054070312455002c0c10042c204202d203810f0250f14403070680c0c002c0e44000046c0c1d5000280a0040f20b241c4108215401050300343d00d18018082143c405420514164503500038000c08a500080e0a0107580c0c5c0c146000150071000e580c04880c20700050907a100e02c88880e80c030044e014401500414103964001d000d4581032035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362803534 1250 362802284 362802301
    0xd02041508061e010f030902180103030306080f03091c0f030e03070803042403180f0611190804110a0b13060c1a060604050402220b13090504211205 65
    0x1ca8080b2520500062000f21181c0b0b5203d141581c0e401071480c2404a140c8015a0000c5c00308002542000c0344100700f84010000c1c50307450b0080c41c0040c000d03100540340c150000609681c43e07206205c00c09000d424541e1810602c00c41c4070103c0713040650850700d42450310141d4a0001c101b01d0a0b0807166110b07200d5a04c0101c0c8411001c03040720100c071000050101908140d503854a4815600340480061680d10303a0360f6402d028245855151203481002d03c0c00c03602c0348a103020340448000180d4003411180a102c2d031010004810345000c480503890418a178203076224540310030307816a5480d0040c0c0004a482d400100f140210024103403280c81d02411207102600d58108480c1540c0c1c2142c0034000c0f0f070a495040181956065200c0d41062001c1c003940e141c1600c88012500340e03070212100550300400760310705d009c85000c0000c1000c040c0140450350780c07134980708403251509400e50340100440161b03150003150802c481c03252000765421501071b0080c507803070282ca80a040c164070010658800380c203140018130541d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362804784 1250 362803534 362803549
    0x801060f050403080f0c1006270e070e0a0e010b0108040b0402030a02030d02010c09080f06040f0c05100905010e040c0806120a02090405030304020a0621020d090212100609020711040c050d0204150806 87
    0x4130410380c100c07003d0b000781040280d007462740901124031056807103e40b40042c2109003e48806130040d815052a075040c119100b0044800c100a072001503494480401c4440e80e0180b0890740160f00103204022030b0302c44d800024201b180d03d8800a500d4401c0c02c0000f00d0b06601074024007a0858aa203841c00c00565480c683e0351507045100398500243c000d10b00003800a8030301c0005a0b01180a00714040d00261a00d0210328802c019410001c041056050104203643c2d0042c001140d504041d207041c000d0004000d00500081c4000d010f0522614070442c0350ba132500c0d410000603c1c00c0341c00608007016030034681032546d101e03817013514107074007400d140c000208070a800f5149822407640c4540151800708241c40c1900000c1d041040303a0082030f5143c2c1640c6002d6030320f615107420380c81d108101800b20b40802504010803206a640131040540c018003442e804a26031801d102400402601d010030301c050400821078503845600d80014103584040340c0841e030b01010031580120306010b6110025561202c20400100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362806034 1250 362804784 362804789
    0x1205060a0e160303120f0c0e010302090d050a080c0105010f0e042315010e10030201020304030f2603040b0601051c0b1f0e090a0c0801060f050403080f0c1006 69
    0x1a610000224404264a40c418440408200182d6010601040c00c42d004014194401c1e00080c01075011480419490b205817101c1c1e0a07172210421500160800c00f8145900310010207040c10350200303c40c406a02d44521082000d603101013503c00001491502c2d0708580c00a02102406620304000800c00007002c0c4220801d488c8a1121903d8660311941c4040342100b03001851b1010560040001c408410100300c81d4540d20b4110708140140d40c1005508205900001c10041032040300c1c810801c09070340c000c4210740c10b484e041031218a8a002c0c038203107040d9503080ca881d1000c01c184110250011000b0744000ba50040c0d11a940c00c000030344581c00112113502490043e04651a09000c0400c00301c2d42c198400c2824100190100d039040c00c1d4103e04020b0b00b4100c940540100d0782d85501d4020600d441440507034080880c001c10031100809800081490005005800a000314910800281806141030b07800840d031008040366580b0340c1400d01d030480e40012031041d0491003421030102c2c1200345070203014123 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362807284 1250 362806034 362806043
    0x30c06050c061302030307020a0602010e0d02011505130204081c080a150b030907150914300309030a151a092202180717011512020d050907050a12 64
    0x103540d00d07980c0040690f6007050a0032a81803104200a0700183c803403410307520003090395170000140300c035030f440b642410944051000001c41e45170881c2c0d00644404403400f54180c442c151107401c0b011169046c0c58000344190303004040d0920480a001440c41e185040449602076588e461240b580c50b684458402c0e241c01030b05091880d500f640052242020700005191f012141c10115510b1a0303031180303150458880200c8190016a211000b80203d99056280300000f1006440301e80000c501c40608181c01d90b00e4000540d0845918600c840c90340004000340d03284488020142d581c00709c0c26240c2803107444254a6581c000750304000c880c0e44030a841c4907034445004000381c202c80b03403661260203252030b01c104100d80c003020307000d18143c86000d612042e05423004455280e040c507003241040b030409050b98800484030b20700c21480c040148032116055010301c1e010040c509103503c041320105003444c040d01403220080142d1340340600700540f4100000303034042107400135149a0354071034441c5190100c0f000c003014040d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362808534 1250 362807284 362807293
    0x1209090b0f0d0213050103030521090303060603040c0305071503060e07020a24050c0901090816091d03180f03120319060302030706020d030f0c023013030c06050c 71
    0x241c0c508000c2c1c01803086610040c0107480707030315290060b241111000e0700168009200800c0c1120041681884800b251803540292281d600e810010355680e44070080c2502c0c01100c010021804004400f4244406960b01c401942e031f43c82e445142502914803030448040000342080f000051020061680da40240d250f40d0242241c01034035183c048007028032880503850340d400401200e4115005104041c0100028020117a480b5621030005046480f0340e008000240c2103003102068160003540301c1c0301101d680d60408164510040c011405000c1c2c4000c0c0c800e0300307000010b888010910030035201a080b83c005c4451174403a62900d003e040d81c1d00e02d000c1c2c03510922481000801c0c140040030820b060706c426440c002144050b1680c5c042401c14400303900c0500581d00c180d228013100742c3c2500030107294044083c41084803140b44c0000a41ea03112002c80403044038041000300f84c0181c2001004866401c107a10b00c9555041000c0000c841c03540d03d880140c901a11500002c641d15106e8070031079480100050051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362809784 1250 362808534 362808559
    0x501030f021e03030f07021813060504020105090d05010203090f03030705040b090406120b0702010c080f040b04030e03010501060f080c03040308071110090809010e2d0109030b01031209090b 83
    0x100076034045080d034000802d5040d030400d04550b0108004c1210107040144591034014510510404c00c45a40341051503454100c00c2240c9a40b544128481840d0070400200301d90b240d07800141c40c14480d203540540c001c248001010140f10054000f54000c1c20f42c54100c1d00007004150345603480c3d0100b618402d002407070411040046004503009800869002000042c0c40d07651280240040c800447c8106c52411402040110b200d4081c840c281914096080131011407512a15514142c44000c10060000740410041003d062142ca144507480c007028008002e5561250000340452404000400c0007a100c0000a0b08102c030807804c3d81c0c0680d9143d1510741c455110020182c40201e0b001d803d00c1e02900c04d0004060224003a4020703612440d0143c0803080d60303520450001411030600c208000c0c003503078010110300700c00b14920400e980117141646416038403540001c012074610040da80080c003403c40074000401481030b04907003008100000d0b01c52a000701d54407140741054600f501c4120b80d101001d038002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362811034 1250 362809784 362809789
    0x906150901030c02150901051f050a0501050a03020d0f0e0d0c0f0209040302030c06150411090a0608060d1401060501030b09160f0c0b0f0601140f0414120a030513090501030f02 77
    0x10780c3c2c0d0180540191484550290f0308030b00c14240071a01802c182c0e44803018008441d214182d41c0d000b402c802101841a14284004103480310418450541001800100110042d111768103031a17000000080500c00c154664810700301910102d90301584500a010385002110701601c601d00400703501540041a0503060340030040d95004c010b0082c0c080d4001046250b48041e01805500d1154842034211280b420b001c0782800102d503014011441c03503480c10030030a42c1c56911483c2c0c10003101d0b56441c0c4070718165038040202e0a5508141d100074484a05480096942c082c19003050041c0c403820b85c0c00700404661281000201c140c2941c0b010401400c03512400c86035489104640f40700340b01c904215585062554920255040c1144e890304e840c03e20200b4010b080d079010360100e01c40030020310f101d82440c0300700726980914441c0744500042d402c0304018109150310348a00b0001003520300d80070f035900a911418042e1082e07111889001c0c90200c000e001054020301c034170070681600e030022070440d1501e00701d90a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362812284 1250 362811034 362811041
    0x70f1e0e0f0a03080f0705060609090604060c030e1002030f0705030115050d140403081801020f040e150901060804030915050d0b0d020a0f17070e160c06060e06090615090103 76
    0x52940021020a0101c0843c4c00724005103c2d41e8a0700a010340e4034211801d20b1800c00704041c0046200e0702d1000144420943c00003131040e002034100200003440d00c0c041005800414260015050341d02030560515600b000707640c0514420340c41800815900c7e600d40c1c004071294071090040105001604000d00700c03842c420006048410381606c0001445415082c40085440b01142d048000811181c100094078001e508107a910300394410080d0300748195100d12000c180200d0085a14440364200050300c064070015144904a8010301030000359612508001d000340c030100ca0640104005441c0003801c0645010000702c08103041d60b869042400c0008114041c00751400401e80c007075000c0c0c96139000b5030f032070303014000c0100803c1c041071070040d00c5c2440c0320600c1e0040310080449a041820b04215030545400c82d5548010f080720f00c4402d02003941001ea44c08010044054011840c00e04046400b10f0340400f018001c0750f040b03d480c0d1079503a9031420041c4071402609980440d039400e10040740f10754041e40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362813534 1250 362812284 362812309
    0x10608061b2b020c1e0304120201120614011103070b01180902041e0f02040f060522080105100b070c0506090d14010c0f09030305040e040c0509070f1e0e 67
    0x11490401d440b40c0700580c031090308942d800d580b040d030018264400d041c080004a002a2140111800058850b8080354403030003580714118403840c4950004045a21504240d07403039a54003801040f82507280c0394540a1400c103000440c0c049403554610305a011000001e4802c001c0d44143e0b4203078540c3c20400f5a10249815414108140351240004001aa100c2c054659159021021001c4c03001044c21144281c0d0008403031400801c5c030410050141800c10340d1288161011746c00c003e540c82d0b4050040d120829040c0311540c4a011022030085502c40b019000580038111042064400b1a102c80d59004148130780c4400800059810308104818140303d0080c0c02920390080c80c1c251040c030517886290190583c0705061f2030380d9540c0c3c0b11403043c258118072903054000c81841c004076083d08540d005086441140074420031284948001420081140780c840b003e828003402d44041400e007217401825224a6098241c00f1503044980b80c02c1000040100381111101c80c0e503400038503159032007800704082030030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362814784 1250 362813534 362813557
    0x2071503020d27060c170609060303090a0f03020f040501150e0127030c09090206030a0510091a01020105011a1e040801091b0b04060c0b15130905010608061b 69
    0x791803c0944484811400ba039510200340001a00142c1c1d1901c0c40841d00304034100d409000001040c01c11149601090700c3d84518103407403140d505d4440310300007407071805000426544410400b8010420310032444480742100c1c820b540c0090020070600400041e60824052119a1b0941110017101603108011903e00e00384181007003044001ca40513904800c02d103150101c100444aa5820020042c0c041041801005040410407080e42c095000801f10302c4060b001c461603036110030200d00324100d40c8040c6d10080000e15010024000240b12100e582003140242c240554a020000941940e01e031401014400341a4101ca181001c000a0405c2e03420141ca4581c1008006010110b1004000d2140f415510b020f214850a40740300050440c11141c0c1541240030604030512041000c4c0b42c0105203101c500d91b1282940e1841da60312500c0c0e00200e103d4880459003d656407012401721440ca03031041d07030300d03d004070000d026590310349030704a03925042980c1800600b409000b00344000301d070f600c01424045405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362816034 1250 362814784 362814791
    0x904200108161d10090609050301020a020a0201140f1603020c012a06021c02030118110a0e0d060f020c0d0318080703090902030109021c0b0a0504050a060b03040506010302030d02071503020d 83
    0x4503408511421402104980442e40d002170a01c400c1d50081603600003031100320000d515021a00d80d009444602c040d13802410311003e49230b48000502c01e241035800c084481545d02d91942030011144546600c0c2d270f03e06501500521a102c1300d5540301c3c0d8444060342c09134004041030700480d2000c081c1c0e24512840159a00d0340d0130f00401c02c0001d621154619048140a000360301c950416081c1030054500c020414422803a00202c0241040c000c020b40740b20740024202002040e0040c3c01140788500c05202c001c10041c903010309038881810769030203040c0d1500302c0f2044954000c00751000750202c40340c241e8644030b20740b4000e45e408000348140c0010300049110780703020f1044583c0c6a100d8400d980023038000d104100d40200f00c2c5411214100300c1004418060302043c001540e040c00805c9a100840c02028091a2203400080d414090781d04410020a2041c092a41e41e28040c1005912040e080c0401c0707110303004442c06070350241d1001801d682690101844007448000c541c405030000d500a81c145003100e034a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362817284 1250 362816034 362816087
    0xd05211b0a0516051b01021b09190507080a05090102130306020c0c0306090c0103150e070f1b35180307050d03080907060513090207050c090420010816 66
    0x7180c481d0700f01207205038010451561422000b00c3c02008620006045603c4400d12012481c2d030f03075421120f85881510b01c10b429450b103060307540d15180b211040d801c005003001d09000b600703a4800d05443c881c0b10300000400c000c1d11130050b00c0e400e0384074907032051010612420090000c180e040c1d0051401000810407a031410403660003185c00c1c1201220100304c0c5800c40ca05100700740d6090b0243e13520078080201c01704541ca0801c9500031a130031015083c2c5d4204600440800b09150003840b40c010391b03802451120002c0981e52802e042041240300c5180001c0700030801038428400e068910007050f92041031703640d0a01800900c481c044000d4040d80300d9052107040710000d12900c91241700d400799070003a616400c040c070b070002c5602c0c5052806d9004c0c0301081001c0002c01c00203910a50321100b90f8465800c0960364071094102030b4602286036984d6640608000300303000401403d5443c00390040ca4002500791b0340120100107403003183d000c48903038655580f500c0761600c815114544900c404400001070165600 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362818534 1250 362817284 362817307
    0x20f04020c06010312020d020601051f0903060509030403020a12051e01060b0301140f120303130804051f080108160e13120905030c0306061807110d05211b0a05 70
    0x6007070307000f907400c403417004070401c0c80d5a41844007005184950000b030200e5494007006c0342c3c40e0201c1001c609500300348160300b0f480d141d00c03815401c0000c50b000041440b4908080307452989a80c00f5200c00c030321641030312800041c0d03054284200c99280303030081c028107041c03280000c024500c45030107407030844603568500c1f0204124000002844c003a03c402c03908091140c071510309000c0c030504042c0180b44140984989030b110b0b40c5c40002200d60040b403217982c0c100c280c8440c0c941b000b443d001d03640000b580400c1c40006050144083c013500d4443e0900b603620a40c2c140d83c0c414200d81c07280400c1c043c9a10401d801c04c01881042681ea01054100c0c0381600009417200741074a80c0c44820020344440400211002e100b0805840d04206013009140101c0c05024aca007410400181d04803822145415500001800584914066158552144400c0050316258002500f005000390300c000e04008102000c0c00115001142ca501050b11507900c03015006080c0c090060066110340040c0605410843c1c100b1100e49600d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362819784 1250 362818534 362818543
    0x2160b010603060e06060c0c01030216061805210708090d1506080d1b0f06090f0f06050109060501020d030b060d02040305060109050702010903020613030e06030f0901110f0403020f04020c 82
    0xe0140b558002001401d01c02e802900c0b10380504a14400d460600c903507070f001c0314045400c496250b001d003401640d5041405403111110404000501820f1501ca2299422800c03008240141842481a50342800b02605c1700030030400400d01011440605000d10000102c5101c0240300d451001045203200f200036a8855503081025000500703216200d06003001b5800080099a0003004281445a142c0003460229100805a0300b406070041c0c0210030b50100340421a4060103840c0d800c040c0030002d034546810600420505800200c40003890300c2c00009050380144901426150144d0180178600c43c0c450044015056800c0510362010041043c0301c101d802a100500041d445100608503961410740c112040702d50050009066904100d103250000791702061040c0c4c0101134404144110b41a814103c901d0500c0c8146d003900300d02c001090246040420600607c00c045980c02070182d409d46110900e01401075100b0041e24000502040c0014601082140d012100141c0f0042c2440d40202c01940740 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 362821034 1250 362819784 362819789
    0x9120c03171f06050306060d051b031303020609121b012a08090102040308040324020a051206010e0102070b1b0a060902010801140d020d0201050c07081e010e060a02160b01 75
    0xd890042c50340340b682c111500360074001000c10781445419071401c107001c114284510f02070110700c0d030f41d550b00003110b040540440360010171006410715128689000d92800340215072209a000d4400d507800201074020009400400c00c40d500d0f8840d00f001110341c42404824950011034955540780d03207241004003030707a400103110030070400426106a0340081e0060300120001e8964400792340100014400704034184203c0703085030b5007c2e880741c206c40c2000c0140740c52501e16403907402200c5c0c00003d41c401019480800351080362618402208030b61111801942c40c1c40a0f00c070000c0c0507030448102005085101c0300035050250107658081c0c8805014501282807002c0a542140e1041d5078402d920259623001440c10f002d80401020a0b00d507094050001c3c0540758500c8009100c1d50b800b042070021a441a07081c0d130080412041210805511380707042130380390581918000010345c000c10740007003034520501038082c50302c40d400d000c0c103042d0311101d0021000e540003c44030306104420682c0a4005060941c03510300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 362822284 1250 362821034 362821051
    0xb03180d021609050c090f0604030c0b04050a06020105151003180804061b030c020d06110310090e0d0818031209010f15030201020309010f110f0606030607020109120c0317 75
    0x10700c90b15400c41504000391a00034a092620f00420800007204040450354070341c0e81141c20400300d0104100083ea07078807442d00001c0c000c02000000240203120003025000b0ba40301210510211a1100e8003242258411034048010801a06450045013403143d00d402c1904100d1030b010400d480c0c0b50340c3c540e440b5001c074074045801c42c038000f81c1048615405507d910500410512081c0b0656054400500361035103d03002078440e04541c141c50080008550210384981c00c1d03500034984910703110602208014441c031a01e4055400c2c02400e09485e540418442040421a15003a906442d8500075101d0304d8180c00d443c0c03560f44000c000c288a00072141001c2e0b4442c41c1c1901c0041410700c0d120041c1c006542c490380f00c00c0002540f800c41480141e0700803050b141100020b20344800c18040c4928200c9000000c42071300080340c0034002c403040c6200400f19619120f071030107a04a5040c1c2d1a001800c0307080391940030340500300810bc60500c202c0741c1d10400c0c02c441104e0281ca0071b601601d0b182203070b00f800e540d01507a1a41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 362823534 1250 362822284 362822293
    0x40206090a12061409120f120403050c0c0a0b0f030402030705040e07151806032a1106060f06030112060b060d05011d09060c0702060408030a08190608070b03180d02 72
    0x4040000f14002c444030000c4181c501001030034484601c95540001308104081c4a6000c82c84241d007841a400356800074504201101041c1024200034041c4d5108201c0c458060158890752a0241000c200410840368000c0c2114a841010a07a40d0299040680100d0f81405610f000181c666214080c2803289119440500380721490182c40c82c074a00c00e550704501c14000034085d0010140ac0e2041000102c030694100402c50a404240e08141141c100001790742150804240d070105a80c0312070742142c050358002c200d40c1c01e91541c2081100b06d940150415620804c1000140210070f400070102481c03910030340780891401c00c5c440001d09190814440700c003109076900300402200464051030400200e071404584104c0c1027105c6181d850712002000f81f01a481300040c401e0454a812044a00508800080e80c0d184c2071600d00003406d4490960750501d1620b501361031440c0f170318054426542210b802034010018a07182c10340020f11508000c0c410000d181740d40c6074031701a0010520403e80020065400743c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 362824784 1250 362823534 362823569
    0xe0610150c0510061511100507020115080d09090b0a06050906040f0801090b0708090717031e13060f0903110111030a0c02100c0c0506030405010915290609010305040206090a 76
    0x10045055901580c0c802c00c01101c071b011b03240c0400800e95081e419040000030811f81e0780c441042e4094240c00095409041c100c040018841c1c00200c1c410107550301503a14900790b21758034032010081da10408880b5500c5024000300300200350040c80100f95800e805050141042e5581c06d803c2a080d4490384660901d94440f80654100301403500340644c419244e04210358030b03090000100340d5400050090510002800142d01c44000c0701f0002c0d2400070300d0a58041130301c09160754420744d41d5000002404140c400a03c0040b40321780c01414410442c040c25604c40002031300d0f6031a8119003042e5403d00b18107000400e401900c0360501030000b0a03034154680c4480300e08480900c10710149400101001c070030889a9111800000c00da69208400c980d01203420540f25126070500500400000c000140824907900021941d888550032503460940c0303c900c2d2000c4403e103c041c1c04082c642c69031007241e0010b001c0001d10607940c025801550010b0000e04003030300349000640030802260550704103148154148058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 362826034 1250 362824784 362824799
    0x12040806010b071a060f03030d0209040506060c1b010c2109050111030a0815030d09080c0904081c0e060a090c080109020901120f0203010510090e0610150c051006 71
    0x8141c0102a0180c500345065081e84881007440b90b20f12040c8908584100481e1455580c1c101401991100909417656000401c46000081d40803403074550045041c100015494a403000680716a1880c050140c6040500c0310300e410b61061200e0251810b00c40481d440e080844e1003420080c11040c220304000f044064510303400351500220381d102d00e0401502ca84070b03140700305020081c0c401e015070900301005151118240441030000d5500544d40510900c104803800640c401020400c0340c0041c0256840c042000d010302c01407803400c80d40900341810400000e40300710504d0034800404162004000b54100d210035a45040500594110003496183c4401209200c82012032400403e00d0f10004c0091071300b1640030902085052207411070303602c00280210180140c0f0344c120b40400b58000c00820651400c40f1120000c03043c00d0080c4506185402c07c40d20f49035100050f204c0c0100001003078080348910302420f01e40006c019040130300070482c2c1d0300c11540028008105114810140c03507070204025083c540d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 362827284 1250 362826034 362826043
    0x309280302150106050912100207050705120105101401020307050106090605190509060103020f040b0a0f08060d02032e0204080102030115090b09061e0721090302010e04050711120408 80
    0x1e03100c0541002e40108101a0807604541c0d01c0c8005031000b96000000a200740e06002039050701520f40f034000501c0f00b040120225440013540c8080307a6048064008d0b0344024208e03601180c0f144000ca50f829818048040d0304260281d080740144112482c0040c156246403c3d645694850160103440f00818841481c2103900c3c081c6141016450108040c41c02d400a191001c02034510760625074001001030300c031581e60080f60080c1100c00d0300c041d07039640d01c4034005000c001c03030212202c0014500310120740e40e490302c05841030391150000c006080303a201e06000c5c1c202c031705100024010705c4500c03903c0785c03010b40c003050020384000e2014800058403507142c083d03111802c2d100301e4003020800880b01d00501000c90070005035004c5402c00d40e010b5440e030004c41072842c00e4620f10700c071421640d40081012070170800c140d05403c01c10707050341d01803240c5200440750684074030416000090109030440110074080c14994041030f80b00c4010b04d4409070f0030708841106414a95413065508011400050502c4140001c21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 362828534 1250 362827284 362827303
    0x61c0504031e081f051c050601050409050a0311100f060e0903030702061302010c0c18060b090d0206030408130b030901060e16030b130507030603060501050f150309280302 75
    0x80003140442400a01403000108082894007501d51145002000b0034800700c09080e01400b0220301b00c1daa03c18000d92424002d404a8481c0318200002c41c007401e1a015000a03940d2000003040748c1ca950360303802d41d420005000c05d120644541900500702101600680c00542c0010300c00140803405c01c140f400d00c1c1b90b402400070210303070300030014028010750004400754802100002d05200641e00c0c0f0040311946c0c9104000b81000440302008208075030000354001c030b14005184200304007550b401281035140506d4540c41e511042c560b101501501340407008561107032050848034902038951512801c062125002080014404001c105030240300340f145070058049003211045a240c5013081c11901d00504451400b01030315021990b02c02d448807000300d03200300050b01c030a0010349400c80f030050040c0200e00c01926081d05000000405c1d00f80081640c80890001d040200202081c400e0b041580e40054040500b52080d002002204500d00f074114118406094072404542d0490030000d25220703465 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 362829784 1250 362828534 362828567
    0x1031127100912050a06090b0105100309020105040b07030903050601030503070b0a02130b37020111030c300403020c120105070c060e0f030d06050109060c031d061c050403 75
    0x10100c010300d450304452180b003140c0400c0d600001c00d02a924100703061040c0d11900411443c18103e050081003000d0300c600c4e045c3c030710a680c0c450001c0703d042000c60030307210307100310107400b086c0104801d1100003107802c01028228000e003072502140c0d950303030340c0d0301e280203400d07401580c603170700f0200e01c690800404503001a0404119070055050000d41101d1b0840c0b01510700c1001d001c22800200c00f000b0300c200a940d80500e13441200300c001690041040c1840e0031960003c50801540b070301c86100100304456003524001c00302035450900301035050f5049034280d2050910403881140d041000c0b41e4071140034680910442c4264080d1000f0b0b1841e03000c0c0001400c01d244441d07050f904010400101e16880444c0c0d80c1e9103074215002041445000c4c4926080681c1040d01402c540400070b8240c44104080d009081110001e030380395410f40781e5541c0200d9241c00c103c00c0c0140055440c90240035071030b829101c000c41d2070000a00c01072800b1a0561008072500c0315001c40300c6059160380400003495001b80c80901000c0310b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 362831034 1250 362829784 362829799
    0x30a0503090f240315030303090a0201020c0a03150207020f0a091a0a030b060f0a1a041d0c030414070504090b04060b04020a02120d0612050307200112020901031127 72
    0x1500503e4030403401030059003c89400800060030340309000610b0f2007244405025250b41f41000d0f1302e40c6844195100d001c3c2d0240c4240c0c120724400d4141400c00004490308030301039104282e850a0b80502a6204840c140da0090030460407281c0313540e5003483c0324001c2500d610002520380c455000301302c404010003841c80c03280c4207080c02000032840030030086500413000ca910311540b62010000131074140581e040400004030840711400200301180080c829074400d01145024801c202c0c2074040c810508888400003500103001040c005081c04034074401654000090b540d2554441d00071800311000308a007528402c0e0f000c400e000602c80c0c20700c20b00346842c3c41a07509525021401030069910568400d11402040000414022a0610740c0c40301000d03065000c0345418240d500d080503656604221020f503404601402c030088445001e010744140d01c90181c49240b1820004150000207400041c0740506261f21140c0c0302c0c481c01c0340080240400300c0711840400c084210011020041d8403543c1040c0e01541c80c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 362832284 1250 362831034 362831059
    0x160c030f0309060908040807080f0f070608070c0512071104050f01170c12010903020f070e01060f021f0f06050f1c1a1302150a0f0807030605030a0503090f 68
    0x144214404a040c0090401091050700b40c5800002400355550203081503c4c041808112040045400c0d400c40f0411022a080c4160502005880e0038100320307500312590000100704242c0c0d0041c042c0d1940070a2605210707180c04142e8441c40e0600b03a8004500301c0603003000507030808001c86105200b01a00702a45e080006160841c107001072003c040c0a0304002c0700b11454500c50b40c03017042011900305000506201d02042244101034060150100308a025000b505038080d41d025000808000b00c85000b2020301c0c032a4a007000036a0144024045142180a013442e00501c2003d40320398000c0740b46030b4250002c2c03103903100c0b4101c40c1181c4071900306030311a112501003a17000b5034601d08460303101c240b45890b0907001c0d05c613440d082d40380038580030000d0ba50314000300810420440715444045441c2c000c0d504240008861320070340140d482820b0a20012079a014900003049210b00f1043ea80216641000544070303484600081c58028020011142c03584001604203060620508019420a0586a0044208 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 362833534 1250 362832284 362832287
    0x30f17100609090903081503211206090709260a050706081f0b090a05030a0f0203060c040b16060b030f030c010c1e08040507030609110f060918040f0b0f160c03 70
    0xa030054850b520300d00c000307e8030400d26a014003403d00c0c41d00c4007410540c0c00302c29001a04100e504a06c0031002032101a1000402504000c10150301c6206c050b40d48003804c500b003065640d085110700d030340000912111404605d1525003048001621401032000300345540c0f41110081c09010f00510461061510788031900f155145900d0480c2500c01c00ca140c9902da00c0e1060200c0d8404d030241d4401c0798035100b50821b00c3c040c040e0145428072500c1c000d90681e0788030380d1044201c0115200f03502c9030700120742d41004a10034003d0203034600c00100b40300c0ca202144084d012000245000d000b07200c5c80c6800e801c00900d04d04500001d102d0503a035a4014180840c810882030101d050f40320b1605128024080c01d00300242c2040428856180070390781c403100410440100382000340c0a044401c001a01400b813a101003070840c070f0500e060790381d2031074001c00010151038081401500003101800c2210012010b200d803100041807004060311942c00b8948070300140c0750046659148404240191092041400051001c03d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 362834784 1250 362833534 362833547
    0x130f05092e0f0c05040303020c011707050d11030a020c010605090609010302210111090f0405013605070f0f050403030207140f0d060203010906090605090103030f17100609090903 78
    0x11441c0441045441100101c0d20007800c46800308000b05450a41c0385425650000090304c02e0368002c0c0d0131141e042403040015078810503295007920804484800183c540c0b0f03c100d0041004552500c40851842e40da0002c5858a4105884600c0e039550040340405640b40d091050400804044681c01020304160340410721012060102038090042c4401d4144584c01005400700038800d000001c00041e0726025402d8a20742104511610a080c41085c03004603107418002c45040c0c2c1c00d014502481d081c02c1c8072440d040b0080a12100b00c200e8907481c40341070038401500c40c291140868ad04c03130b034050030048000182000401c9180d00c0600c00309010070300c080b0358001042d50075144900c617100f500342c1e128400541040031140540c3c0d0f10074201014042040b410f600590304071a411841441640c1e00c0b80d83c00420703107204e0b000346500f0680020040021a125011039854110309003084481d0580c08036985001a50848480e43c42e030b00c0c1080204400380c0d100c60014014111604204000c4d515070380d0081c1079 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 362836034 1250 362834784 362834833
    0x100e03091201140a0903020f0a051e0607091712031009200d150e091006091a0402070807080730022d0f010501180c0c060c0e130f0509 59
    0x101692840e0217400c00d4002c11240d103c14881c2030854140e074003189006075846400003030200b40a5240324514030111000181c0b02c2c043c5900e80c13140b4400c14149907401d00e0300c0c465100e0401e0544550b002d80c41f400c3c1d06201c0158021180c90869a4086040c060a1400c1e50841a0050b501005220400c00340016100c25140c625a0340c0d80e011407202c40c0c5c17640d4003840c2603050b048030311020803800600c4040500001c51412600030403009001e0f0982c0e41c14440308a030503044081c4a050390310f400c40080c170300c0c159004050880c419141581000301d540c45484050304040340c101c41041992406032710510000240170000080c11031030309035010060300e00035150322003400034888544403000794555499035201061111012001110380c4130100d400aa8060300c1c003880f8140350126803860000110031103008030702a10006884039202e00b400c40d035400001748040b1203d070341080203a0301144401d0b9208070110742c14618010b808141002803410100440b1000761001015a000803412449540341c0b550f0000c0303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 362837284 1250 362836034 362836051
    0xf030a060209061215010e2704140102162a090203060a05030303102102220b0d060504020f011701050d030c140109031202030705030a0905100e0309120114 68
    0x202c480c034400c045a00d81c01103001c3e0700584d1045804008860300c2c0d40d41500014130090b6164455140c2c22024400c000780c160351300003211002d000d0b13040d81c0050040081138025105640e0a50a601c07030701d0340e440c03c9811460b6081110350400c3c0e8000284010a41809090001200e41101d050032040380d050b4580d00701d102d880f07d290f4010000641a6843d0f103441c500401016003501d50303d1824050405801c8502c0c0900c41e00d0680b48a140800c040f00c41a80b1025250f02601f04503254155181041895641030180300b0042c0d20751003062600d413241c0034003001c1e00e4070a0801080c903090500c104004c96804140150400c0980d8a40011b03014108840030304682d0241d4403080741e2000f81c04c0032100b002c925800541440d080044481071140b056009000b1107020341d85108c589042151141c041c0d10080d40e5a00000b10306201003844a900c82e0303c500b403064840c104941054100d6110042030b40d8601507000c0c030a42000c24012500d040007088030b000f40041100030001500520819808654043c00306a03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 362838534 1250 362837284 362837287
    0xa0c02030a0f08031006020c1003020903120c060a0c0c0f02040f0906020f0405030c0303030709030b060f0d060b010e0103020a02070306050711060103061b050901020d0e0a1a180f030a0602 82
    0x4055403000d200003100260030184412041c1e0040c10160480d0f0b00682e40c141e41d8104d002800038103207101040d00c840901000700b007540d140d103190030101e010b9000361154540c14040c042280001c040c0e20402461034400e6100582441c0c83d01511031411107000c05040014404000c81c0d54001407a08003275140740c01d40c1220005001004070b85c000b80100640440104050310005040c0d1480e031080000d8030880b0811400c845c9810b4607201850b40b24002500d852002c0340310950244000b464641030381e070f48a81c000d450421110390400000b004500c0c0c404081d59155981c000c010300c51350380705860701c5a4030003e0a0645c035040c8082c000a6541403c2c0c400546207540d140c002c0b43d0040c3c8186600c5846010740c2c0300302d41d440e5850341040401020160010030304052a420030100340c60003442074501e1030034140c01074a440710b4402400d44800c450203141d20f5010b00c14800c04124001c0512003000d0324100300010f1f58032241000c1c00400d4500c02260018810385021074039410030303a400998266066400600075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 362839784 1250 362838534 362838557
    0x80708070807020106050607110301050601022a03030915070201030506090c0d0e0304030606060f12090f0b09101a09010f080309120106080a03170612070b070804080a05070303140f0a 80
    0x8038018180354100030790090000904c8e00900944c2c480c000034400049000704050f44a01006a950306800d102104028041451081c030741c18810640020154014061364a0320410000084512820007002c069240c4003040401c103550307151080a5012500b560b0510711814042c800904502416074014403035603d56030a00807020060081d200110342c002c00c10300100e621410003400c034200417121040015a00345c0820343c00542401002589078100030f40021005841d291940c1800e00102601224070418401701842e02451043c0c0038085000c119a81e84022005d0400a1290040c5d02c0071a50285c0b00c1414042c5034400310890307400480480750021448004014035015040c503a01140685c024625040141900800444080c0e5041d40c42c101143d0b403200208a103040c051062110300c3c0d4030810f400d200c03003807a0000504265006031030141c101596031424520f002511b2004a41c1900308410804c1010b4000d05900d00006180c10b904e401e0503041e061803a42c6000b490354400070001c2e1408d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 362841034 1250 362839784 362839787
    0x914010206062b0803010803220302101b1403130501021203070c14010905010b0a0501050703211103010306020a0807050307081f0306051f0b090a0e0a02120702061501080708070807 79
    0xf21041c0d194030501c015101c2d80d4601c1d15688a8200089140310035101c400740c0e0341c0500201d014401940c1d03000341034641c020a00c003012106420701c42000250003003008441404104017030005080644088001d40e0758407152405590503560b01e42c00541554803c21300c4a11081c043c0050f2944440c81d4074003002d150016061110011880c0da038420f600c0d501c1c0001007410300c0419040200c0018041d1034030040c096441004440314884c01d40c000e400207001c4001110607104419a00403a00c1d4411401b1801c2c2000800c1517035180d0007a80201c40060b400680801c0c030700d402001096100380d49003401070451900322800707841448000c1111085010001c4800c0c010f080c0d400c2004045e58100408000c03502e8001c44c0d00181c0d003a110f260f8401c044840328006204681c80e01151660750003e800502030b61720340703007541c2806d00b0083c00e041480d9400b884a4010140e07400000d510030340d5075a00518032401d00d104e00c1400080400422410008003504002007a500810215007011242c80c02456590710900d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 362842284 1250 362841034 362841109
    0x91a01080412090e041a150105070605060a09061202030106050402030408041a0d230105091e0402030a05030a05040603050606030105010504120c08120d05090627100c091401020606 79
    0x300d8048102e00e00203000c01d100004644c00e40e980000c02d1b0503443d64a5407060100b070340c800c50040c1d0340011003c01620b40059010b410854108402401d86040c2c1501c82c8070300d030155040c68200140c035a906040240c1986000d005400013004c065408500d181400e45410300301d80300360300428444800d0f086481d03200320500012941c11b100e240c80b013040168500700c80704003c42d40301c1004401d0b5001c0c80c00082064944043c80740d0040400c1c400c1403203030811100c4a200304c40c3d402002a80e0500660342148045a801d2000308001e003000c0d40e84603034441c108100a011250060001b6004080c180f006200e5070b6080f02c00c40301610212051000d00009a103041c0729005060b8102c00c0b014020364054444080254010f804c091140700400d110681d0b0b13180030070383d03515801c0f0380c0c2080d01100d0f40724084204140c001e0381050b43c1f402d034040c1c07940038003642c0143d41560002c000700c0340014101981003002d21070755005082c2d030507001d00c0541480e040000001b9440c5140c450742c5000d4506040e00904011001c51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 362843534 1250 362842284 362842289
    0x302090a05010305010b1f0c1509030e13020f070818040e010f0b0103050610050c0307050d0903060f0902010c0b0907090908030711060405030304150b19091a0108041209 74
    0x20108512460450919000340c8801c1c80112455070070500000320700d20308030245101006031511424644060301134100d5903001c01907025552840c480c0c2040041803c14000e07640070502a4803641c8402c038006043c001134040074070100202038030601c800702c60280810100c628042d0000c1c02c190b120310b04521980c20001d01492059070051804408075070120064200c80d010101e26541004421000001502954003c9404d65032180044c0565208540030784c1c0a04081c2c061201100d06044141e0b66072450500c0e229090004501104000c00c01c000440c081c001806004600034000d1404a5001134400d0000b00d070000c017a0b4079440001000080b08005c1e43c3c000b400154003c4c0050243d9041810140d4020b44110000a641c070a80108512000400310302582d800030065186540b19190400c22050324400040b101d0346426080702d203641e543d40d181030400c1145103803401c801d140c0400d140884240790509540035014022541c005d81c0c2110b4681c1d4440e0300260b408945452680c011101c60a940c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 362844784 1250 362843534 362843539
    0x1502030301090c0905120607080c040b03010504090f0f031706010f0f080a0213060503100906030b04030e060d0614030115061b1b0b1b03030105091801060806070302070501181a0705040302 82
    0x91b080c20040400041c480d0180109480f8803000d500e499a0103901e51155015190200904000400031402c0c2039010021750b83c0501c025a401e81c1c80c95550707500111030f680741500000c403d1840449d00b0f4900061454210409003040b400c2c42020310805061003c0e2803c001c0148054400000c402c4012078046951000003a540300d4609600c850014005801c00e544000b4840c130300319001b28190030b2074810481941d800000c04515903441d0340e82101c00c4000d0422658000c2d0b0705101c00c5d08800c1e0940144400317401c64060302d00351159048245403c613110144040c40c1000880e030100b1580b604101c281c80341e4511700f4480c0c0305100e42401c144007440000036034030600380e241400010341c002144001d0800412a0322130340207600c0f24078144c29038130f00013130281c5940007040300082045040071990030880720000340000b103440c40c1e03901c0d5441c0c1001030480d50800401e030001030002c00c0100a00c6051620313904408000640b519030740703c80301910780c008010b01601010301c1c0402c2842d0b0182c2c041c0c3d001150b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 362846034 1250 362844784 362844799
    0x209060a260111040806043008060126060d05121b1209100822030203031807030b0601030905030c10060504061d041203022101030b011502030301090c0905 68
    0x100700301c000301409800900c0e10b510b001c1042c60025001012142100c605000a02803038445444480601c10f042c41051595030408480f000102c40c180ca440c0d040d024151104100d030b00d0305800140c1001988240c139034050540c810b07462660505248910381041040c1c80c4988081142d241a62908103d1400c4280101c0040b418002040341104000c200e03024000541c2d0b040300740f11004442c0c50060508807a40144544803110085100700c8903580d200301c03101100341c00c040205d241650401c401d1601500143c0000003005101b20b000055015103d4000c40240015031071900c074003440810180c080c43c101910b50502c0c2050150410a0b50460200d400c1a5020761684131842801065184201800303241022400101c90682c2516504520048002c1e00002e6640e66a40c01c50044c141d0400024181d09001c02156681c113140b405040360400340b0080503d50650070304c600e03682016070021038072515074909200440c1d404001c0c1c1c0d045039603040001c02e0005420784240e80d83c0c2810381146030030141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 362847284 1250 362846034 362846069
    0x8060d150b0405041b0503070305031c061806090b0307050102070506030c0c0708100c03050105030319090f0306020d0501080c030307110f090c1305010305063a050a030305070c0f0209060a 82
    0xd032142d01c031000e881101c0c2117420b100d0f61982415121038175031001402c0758000784514400021900250041213464000000384942c48000e08640502c0c14a480140c0740d9440500303200b42c1006100d0080305c108201c009100052404000030743d180410302816004403004804154800040c4095a04511501081c0e0704d00548036030100b507070ba8400100e040045170402c001044070a01a1050505071076000c0d024501d84004041110680001c00312801e04000a880c00005e0138002042c10602039032145002607902d44d804110507040c1ca0f07060300801603940010009000541c3e0000480b11600d6112440d840100c01c00c03000074040c102e2141b03c03150042052000c020307081d21001e000300203c03000049400d1455484d800110110341003121b0641d041000000c8580312003440d0340200140b801c001400c0080100281000c24403180c0c0c541c0200c415500021240c0100741e0075006656104443d4a420b041c10707c1c141e12000c421800120019010725002c0c40410050b81700c8080c20000303410794002d2107400c41c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 362848534 1250 362847284 362847293
    0xa05070c09180302120a0f0e03070806090c1e0f0114040905180f1f1e0c0c1a060a090203071707110d0e061905041805010e0708060d150b040504 63
    0x1030341281d0450041c0140d03542100980c0050741503410a00003035807000c890700e0b421031f0251a6114103070b05055061042c51800030390101c0400a152140b0580409030180e449154180020901121000301c80074800d2100303d0040d0320b400c2c0c0c0e6814685001d103881c0d000092aa205501c032071150750040d0700441d082c0400c02100d0703003003075840a0442188800320b901141e01241140c2d1208405102405070341840e5101305540e09007a001110200002d03601440c2243c0001262411074522414020104801c104c00b075045c4406403405410542403188040f07041d19003a40002c9070164680a12071010761b003c008907000f5449241c0f00c010030340c0c16102a4245040400018180038800d0b2040d0306a441140ea03840f805912580407d25140302c054040e5040c445c10040101051100034245010400140030002c1d98401040d0a184080804900000d59505250800000880c01068402031000d400e00b401029182c02080d1000640c00020a620300b8428000c1d0002400006a699500034100310030b010070702 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 362849784 1250 362848534 362848571
    0xa0b0619022406090412110604121e0504030303150305030a030614030f0613060b1906020d0503070c020405060a0513060527070e0303070602031801200a05070c09 71
    0xc0340324001d50a82c084144102e024114021038801c1e03000710505000c10005001059418201d011504200b2948280c0740d140c9032034040210780555814003010044014030b40c200401c019880c00d0070280c0c1001188000c0d0150041c8507074400201015a40d10f0a00d001c00f5108000c400a1588101074079540c400420004001d440e2a00030703680e08840080c0f4078141881c0c002140e00900d800e0b48080c020580d2116500c035410501e180080d02c26940b64070340340f1102d643d503c000003038295199044048143c1820710081c501910341220350107000041050000c02a00901c3c01040c0c594101c5002c00e05907220404038512001540c0025044200204005249081904501c1c10340c1c40603501444447c0307014408003603680002004000346405500421511849031242e40503945015049900d04031060b40c1d900100d0b4402c035614407484103210701029041400380070f02e04240308064490b08146011040000c2e00d07100708201c004c10721100140f000104640c0e82a00c0c2d0041c402441c3c1081107040c15110341101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 362851034 1250 362849784 362849803
    0x51e0306030d0e010f05030a090c0e04030e03060c030613060503121b03180d0303022a010c2c0a03080d09030f170403050c03071b0810090b0a0b061902 66
    0xb80604141400c44034400c5440c1d0800403016900c030229080c80c8141910703d94005000f0203081c3d52504481c4002c0380404032102c0040100ba2a03418942c501030400410213002c00c00001d10907000101403140c60880c11080d25000003003162180c03c1c02c3e4a503103d820041090307500c45074150141070070014190509001500c91050f10805d80091890104003079500c0348200c0c10b1020207403041c88031035601c0382071111000c91840d10a0400600d802040740c03070510002c0826241e004006d40519880c807031002d081c081c108021b2000d00b40090b486200407104451203d10801405001241600070180d0b0f41d50200c100e0002d42e005005180d460f05694480c0003c0e203100c1e01c003039000c903811f01c00c100e144610032000d001d8140104001190a81c6175a40e003100c0c01d0740700c0c0405240d54070044c085007001c02e890040d0041d1800e4881e002c1420646426441402c0c0100040444661761820304120b02052040c0206a8007070503501000400075030b4600003540c10700410550440014500c6a582034207500020349040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 362852284 1250 362851034 362851039
    0x10b100203032a030106140d09060204030c06030903080604050618010b0414060a0c030516140c030606040207080304140f1005010501020c0d030f0f1b05060415150b0901051e0306 78
    0x2034003a14140341c200030000f240f41000542ca00b080100001c6200300c07001c1064038180d1131030510785411913082d0001d40e0881802a42c0042e4001810010811200c10142c0142034170705051107505a00e8602a0400400900080c0255201c40014115684481d128004504180800c0181d0f5031030310708425032900300303020300c0740084418400040c2a1074242c064408601d00e5a0f00c1940303001c41640d08440640002868030b00da2420350501000162202c204884501e5140c0300800c0b0700c01c10b6904043c5098005040f10703010314410048103020540305021290300030b0b00f05031500d1030500594025450500101d441079014082c540c403401f420b813040d4100c141203404c26400c41e007501419404020303101c210950014045545151556001400b55a0402c4081c8403800c2034045c050b2040303809220f001400c04100d880e42c00840802c0300304040c1103400c02da4807960360350800c00c02006407444507140c01540150b1031410008143c1000c168403500c00c403005100d1020340c40341400407200d400000d94005558503803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 362853534 1250 362852284 362852311
    0x30111030a0c030915110904020703020307020102070504060b0f09150a171e010e1513090309170d120902130504050d0c03050a050c0c0d0b040b09030723010b10020303 73
    0x160a81d01c0f07030166004160704508803140c0804201d41a6005002081c170300481600b0170700001c4031503502d91020f002000e01075006180c1d120010707c002030a100458004501c160320b8000184240000b01052f184030180703140c80c1954904004000a80344501c113200e0a8070706000103051000c185e40048000301045010321a8a03407521801010358201508002486d0001290401004401d20703c5e2a580d0300004a80b42916011160201066500e0b42031100302e40340b2901c0c1c881600c10164041800c00080000a800c00d0701244418026620f03940102442d401b001001100d2411410306944088500342d4014070004101032060082c2d40509011030b416682c60044160144090b03004240d42c500180c2d240c0ea51502d051a8201e0035100f58211035a02c80080c45840c010401544441e40c007a80c41c0c41c060080c0701070070300c4d2a1800d156030840041c03541e00941c206101410024425074000da002102400700d0000b40035401c01454014189a402550302c03000b0052984c0d085600400218001d840c41d682aa = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 362854784 1250 362853534 362853551
    0x609051509030901050a180902040614030105060f07031206090914010e06040210110f030301091b0203190c1a0108010c050a0c0b0a1508030406090f060804060e0c030111030a 76
    0x922541250007903440d4000b00a14852503100d0401070103040494100f1103c40c42056800744070404098220004540d8001401d0204036041002d81c03d240d00c1c0340402da413540d818600410030502078042c2c0007a8111021070010304140c0181002200300441c440708210309980c2d82c04250107050b210300d0030348040d200c14842042c0003006010340c0120210f00340081c039040d2501d030b003840040403001110804214800b8650014200203100968020749800000c5440e541003440800407200300411000c00c0740e00071500d50300780c0c40c2c000c001d568112012030209074041c4030480080ea460f103100e400040c440d10302c2185181078aa4403480300d9060740c4511000b00001c0154540a503518824009800c000c2006c029000001901ea05c4d40d00d9070100c1ea61a000c10035106440b055500340444c3c4c0c000d9402070b00042020f000307284c0c0c070010350030051203520300703440000d0b1074000d0181002d040030f800130301445d4aa8000d0410000100300001d200d0304003400801060f076044540d140d4903003064070004203190801d40300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 362856034 1250 362854784 362854813
    0x3060b0604060c0f03120c02061b030103020108010e101206091b0815130204050106080f0609070509040b0d0b0a060303030605040e250e04030e1003150b090d080403060905 75
    0x151002d846054031001c2c0e00d008542c8030f80c440d184190508508001c0c107003100e601621154060100c0f409043c0e001044241000418500300c6c480403100210660014001080941e81c400708550454070200384a40403034441c403000d2030440041d500b1012146402c3c0420382c0070040c2607482140e0103405030300880e0007001d64041600078030b034081c440c02100d58008030000031024071480d4503c1d00140000a102d031003010603400704054500907400100494000c03010000402d54440780141d00440840b030031141c40c5440c060203009400740d00083c031301a80d5661401000e680f1110600826030340c000707001006e075190143c0c0d0a4060607003800224000303403c01c0c2d00041c050405000b44030500409002500801c903428030805d03209552017403a00300b4903000e0840016010f50b4514114000c0c4d002e0b42e218550b5480070b80c24492802c030544042d00400d0300e0104403284070703144d80c10030034207488a0203000c2e0b98640d4600001442e103046c180d800381ca000800500001040000d074042902c180c8240306441450902400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 362857284 1250 362856034 362856037
    0x1f080f01030210050a1809020a020717030412030509130c020d0c1505040f0803090703030e011707050a0207031e05010b031902010507020d2112060303020316060209130603060b06 78
    0x750400d0140385403c028070302540180682c02c00528040f541c0480c02e588a05000c021580820a40c030340c0010307001d40b0180d040c072880000e0b003d1241510796116140c0107441d540d100d6481054201801041c20504040c0300303c0032a8071501d0014040300035007100100f070f031700100032901040e40540b18a0419a085c14015494041c0303554000352070f58046441000300341d01502c0e00920480700c0581c01800500001c00440145000e0700a100c0100f103480d0862501a260510001041d070611001d8500d810711690b8188900d540620107182107920760085800c1a85021443d410041081031a40b001800100b811008200082d0150000307108011000041c551140c110f10240303024010030404460155000b44002c10016201821418484d03040c0e44074000329802c0c072030140c400410041c134075022456010241307400ca10010041004000e1460b44e02941d603218120845610440b4400c09400b408026810f0f0344c140d84001c0c007012881c02c0c1d0350081e01300030200c6000444269107001c400801c282003020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 362858534 1250 362857284 362857289
    0x908210112020108040605101208070528060e0f030705150703060602070e09070b040b0901120b0310050604020910050c1501051c05070932060105190e1f080f01 70
    0x2c50751360071a180e50711400003a25004111009051011000060360711401082806650084000c0c43c1c4544803450702a007400d0142c46000c06c1d803089034543d4442c107008a6241a0120362040b00011a107d140c8541340c00c14503120071802c0e090102003a0a02480008940c0400060118400790744c40d03074600e401502154800d006080c0180e02c82c01080c80114080041039404c03001c0e0100302c80303a250740c5189120700756219800c0b060000d032000c6801550f558004042c5440c241002d42c003840784104c0385001c04d61b01c0b410380842070b60981d1660041881a01c03998102c6410001c0503010a02c00c0c0c005902c0900380340e1100d08420350502c81e50000c0800c00c00c080039440e0581b03400500c0c2803c40400c02e0060344004010103030544050003118000034088100788600300300184100d100a241840480280460310b030316078024621035080030100f003002da9021080740d0b4404201d22200000400d41003040342c0b422035406000703402c003130501030900c062440405902485081c50b40c4101540e0381d4507803440404042031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 362859784 1250 362858534 362858537
    0x3070905011d09041208090a11060f1c05012102010e010c24150e0c2208070602060a0b240309120304230d0503061309082101120201 58
    0x12a000d120540c401da4040c1034080000c822958494804400981807580c00d580884d009110340c40d00e45640c0d90048107550b03100c0b002202520080b1181c3d160b640f1100030822400384140f81c00604024080428000e0743c040441340000d0491205502c020180213000078050076900000da610010400341e24441c0740c90038103606940f0615910958001074a0083c2c038a10200e4090900c54850000c400c010565054002c083d0500800d03810010030406110316469004404030460020402c0202140d08080b1010a8003440112049401c040d40c4111b2036521504901418001d08100094035a40005c00764051025030320304000c100713607060801ca01e00c02040003041c0300e60000c085035400c1c200528003031640b01c1ca006050301d28800d1038002c0209194821503048817646924041100c15034246440880c18000c82c200401e04500d031003001500074000207010b05c0c420360501140d2140c0042a410068501da4400390064890300da00c00b0b10021100045200e100e20002100002007225000c5c004145140c1c06 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 362861034 1250 362859784 362859797
    0x60f04051507030b0603040501091401090b011a0702060c010f050604140a09050102250c060512043017060306071706030a0206030103120801080313150c0605130309050301020307 78
    0xd0400902a0030801000300c2c0605958002075495500e883e0700441c803482c800e0f40002030200c614030340b022803c800d00440c3c020984c9031154010021b03c85042440c1520700124900741e01c031004803900301280c40750750b400035080100401d542c0520201500040d142001c1a1002d1020380e6680d0284001c0704d5640c1c0310480550660700200e08018010f90000c0b562a024200140c500400302c4407607012840c00f1070010340880084000e00b001e100e2128151006010380f898480d00e403a0b00070002320001c9102900c060500c03540841800140c03040080a10034034100807005070710051070300c0ca0141c8502410b0070030318400d120039000995107180c003040080c032034041b07905e411407650000000302007900780080c601c0390940b28600601c3e000d0f03036858016600a5120300c084038140700c02c040d001820414180e02c015101d902c244000b4000c0c1c0300c0c008100741034400b01b105406050f08411400c0f0303580004140c001c0d06170b600d00f00522a90a859211603841c0078000e481e41018184d13643c050508030702c811255203001405 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 362862284 1250 362861034 362861053
    0x80d15140f060306061e0a02030913060e0c030717010e010503010f110301090f09320109020a0320130c030b0607170f07080309240f0115141902060f0405 67
    0x1030170005840c500000c142100350403a28034281011641c1300703040c01c4000d82d001080f4500c99160550101140e084404c41c1409520300c1c00842c1700952101a02c8507001c1480400000c8046225101c1d200303100c42403000c90142c550303540b2282d8800380030a000b10741c000d500340b054840f80140300d80514101500900d62280c81e41e843c112100e001005000401d910158482106101080039103035003e201340c50380f100741c1208848200c001014000b080700da00d21030f44d040c00000c030701607998440d0f540100c1340c2000078072070011001007500365003545014080707501101044200c5c00906140d80704011040d51b07030b00d04015190801d000c003c01c1d4060544000c100d4076100300211442441c20002c1c1030f00d010444001420950190340c0d4410b150000c656074401070b80040075000440325103413195400361038140445522030901c1441242c02400501501c410208901800c1c00c03160f10910641541c0405007240c00c3c0c5465600040541020b0030016440c010720621000c11644001908924012503114008018a09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 362863534 1250 362862284 362862289
    0x302070b06190801050c040e010f030f061a0405070e15121b070510090c2403051f172107030e01170f040b160507030c080d15140f060306 60
    0x80c204010141102e481c281c001910707038000d00500340141482e94101d078855041411500c05020140d1203001c07503202006041001c1074a0f41007007803505411020219601400000c10320400c2c841e46041504289814100700d0503692100d800320380504110350011001c0750321110301c445070107801349010b000c807600030100d1083d00e80404c1840404815510711414240702d40c0f116070900d5005201030815545809064080100922000001c0d04980340310910300d003404400e503c840300b01c815511041c5692400400c044010802d048003210400c0c00040e1000c5455103070704184120442e012010910443c044d003c09010780a9004014130119420a41010196107088608140b402000c43c103001003950307090307141e1110303080280c82080882e02084032410a40382070155420014602410204e00420b0700d031006034004103c81100d41c052401a40c00800c905121850788110008035008034682025201300c51345094000c03080f20012243c05d2103410543e0b040c801e0900034124104e84c800340410000d0483d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 362864784 1250 362863534 362863549
    0x100b0a0620070b04150201090b270615090a050c160c080610080d02011401051e060d0b091003020d0b09010209030f010623100309031103030403030b100302070b06 71
    0x9000e010700040445000300002410010b481d00480c94615002a090209a1000c03c4a0058101c10702c020001300b4160344580c0030260b00a0320514044101c43c4030841d14a084c090920701480c032140c00d40304141810a5031101c0203428560a901582950002900da90000d1140c0b40c4a102001e25552900780e145842401c0d800c950f5804603889070349041c0100d00101c0c1003051071b220710030110390348110b5030070055002e00e8441006980c3e000c5a042120300311010306001c4056044400544421003004024822051140581e1102a4011102203410b11207080d150300849800342c01511030b40c200d51101c07880001000010700020b90001da03034060342e00004407000c0900c4da10400d1103000608092080b0b00280c02c21000b001084c00580d103d1009001d202c99101d07007070103901f261004c803411101030b2102090403849000820760034550741e21400750a25001d0a150184a907860090f06e0341c91401d40b070064010000d444110f406140003404001c01a400b0b88220740c0016001040f821161b0748840801210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 362866034 1250 362864784 362864807
    0x1d060405041e0c02060a0e0c011e050f18100c050a02010e040b061215010903030219020303040314010203071409060337051503030f040b07020103111605100b0a06 71
    0x140120b44054400c04000d220305141110031341d001e000306080400446061362030144020746583c000703541e202c042c1d0ba040301c0c808210f48503402c010b159a4458450503203c6010300b803c601700c126000a102c903d00c2e820195030502004048611401d01c00c01c41d8000c880003507a80c0d81c0100359a10101c4130300055800341036002c0034903100500200c1e1002410340800da25812001c100c102241c40722003801404040c500b03480031824400e28150000b917107592402990356254802c0c03043c1e20350440c890142591418001c540c0610780240d02110088aa40c1d40c6030b000f5441111072030300040c1028140c0001200c4841140c601040042050781103480e8248101c8c05010410540240034061400111034210101808101c4440c0e5079000141c1349000c4c00121061000217002501c690030803c41c1c90104403000042d103007030319a2500100d403526410310058000f8a82c031464140d0b4880045507a01d081112400544140c0b4440c00543d5110180d102100c810303144840003165100d8031201042c0041403069400d24074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 362867284 1250 362866034 362866061
    0x7050f0c010603080a02010c030e0f030a2d0507050c010912060203070905190e09071d0c0c1903180f0501050a021204060206180d051b1c03020405011d06040504 70
    0x10b002c0d960b81c4d01c0c15042c1e40414141000b5035107900300c01442a1705486500d00f070b0b0f40082c02400100000510305601c903c1055180400d00000000b0803024003003c00c1c0e1020b1005540341032001d10f00e520300d006002c58100c02e00440325845010309000389944601182e1084800c6144c01c1d5582d40895610301c1e01030341006102ca002c2040450b00004c56655082058080320310101c0d00c4c41c4a5410652a58401003000700302001c16032200d0000c00c401403c0c2d00404003803070b0196203400320310f481d071040700707006485004910401e41c45106e07074030360014039100c103d40c03006440390319403054074865080111400f03015031040c400342c40c2c0094000c02c080c2d4011002411041c1152060383c00e003030104c041145403500940c0162005a01060400000c403007018038040540041c040140a0a010980000c1c1503114a11241d041c13035924541e600d82032001040718489007100b12100300b0f4180c400c000c006009401c030b4030400380000c074006000740c80240c0d800340520406102034a000e19160074a000d000143c1010703d082030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 362868534 1250 362867284 362867291
    0x14060a0309050d0e0f01050403120f0219051c03230a060504050c12010608090c010c020d061b180b12100302060a03201602010e040f0f1b030507050f0c01 67
    0x1c000800a1042d0544044651a00d0740b550720900300b403100b48180e81a143e414808204824070100380080600f1640320200d28045c0d400c0132803244100d052883c4114091072040d9601d14242c20810081034030b5403112042d0b0301040d58841c003007100b00c00351184410402172059a040e0890b0700054011aa60780c88070084002242040e5103030007080842d0f0084030309021819020401180c0081e034030130701500411b0b0f00d00d4082e04604192146c00d8542400005041c14440c14540c0581152103200c0d4080c40b0941040081040c4d5180e20001c3c0341006c40603032401d0024902c9210250483c1c44440c8400540b01140700280c20048040012001b0607006422200c0c13000580b24000010ba480d180104900742d8140e0300031846802d200b00034040e4402d420004034008100b8016064a04049218041103c0d024070742860000304480114004103504110700420781c1c141690780840704842d400c1401410021780300c0400c0500404800c0b81104c405880590000f801003000581c44007100d00a09141c2000e01d0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 362869784 1250 362868534 362868551
    0x10b16030516031d06040f0b030411060f07020405010602120f090a080f030403110a0e040204091b0618090c020705060a1806120510030201051b0118080702030f010614060a03 76
    0x140b00d0010204110f0000d144908040c1c05507003080009507040e072050300d1003414036091020808042c085800340319626500800003c060181000508829220141c07040707a0741c0e00308000644555120b1344c4140c2c090744c100340c00059110701c00a040f2503042c03800380340300d8202141c0c2c5800d2012603000d85c4116a100e0711040e000700380c01805002d40d041d1264410001e5690303625510349010b140340313000a034920071002e031241000302e18054400194841d0707045800041500c002e242444056059161841e1041d80b410008207029800252060f18000c18045000c4020780e80c80240c2c06a0307135040e480200503009040c0402450404502801d0f00e400c103414030440182401c1c0a1141c001c0140e03001c240052000001c92490380c1052286641003824110740410399030464001070300b54814942450f0840b01c120314400f48140082d80400324001d180c0050303120355105824942400d40100e4020780c0300e4050b6062503030101a0505c40c11003110307903d84a10005c41440700c1041042e4001c1c1110005040d200c1400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 362871034 1250 362869784 362869807
    0xa0e072609010e1b011211070c091d030304020f0f0d08030c0409050105061e0a0e030601090905010b010504080607211805070f0302090604050912040803030a05060405010b160305 78
    0x558481e10340d0344000201c0640c1041d0311442d00c138555032488140250a50144441c1c0d071300005400c03615422032400720703034880b6035801e0780101d1040680c050509c00340c0131004100d40d446500000c0c11100f036040200c1c0b4005490321010340b21310013514001d600c0040c4c032149852604050700d0705aa401d10041c400c81c1c0c04551503c3e1040300c2c0d40125168107000e03c00190500c030581c0d152007054003600d01510070790700f00b031441a003944c6080b5141400344950240481d031320004a00c288900704808402030b05540c01540c0d0307490030030041d00120344211a40e500b405503d803c41e5100d20203440444030f0342d0780140010f88031407200351110300c203a041d03500d6640d03810301d60000c0c110b01ea4056001d16104429805843c241a030414500b0030160742c000401e40d46083c4800c101594845c004680c00400071a00020b140e100d0480c100d25060912000400d00070002c00c00084016022020710312481421009000a64440c410401124030074014920380410a01c42c13a40300c00c9210307400300095403080c2082454480700c00e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 362872284 1250 362871034 362871107
    0x30705060a0315060516060f020f07050f01230a0f0216231b04050a090209090703060608010504080a2006010b130f0e1305100507050403050c0a0e07 65
    0x281c400200b03441d43c101a607040440840f2100030070f041c2c0b8081c0d080070b80704980c0a5405074132501c0a000b1940381c4407001c0402040b079048032030101903410aa6503a21240c54011b440e5003194080070f82039442c083d91070980d0302003a62455040e01d2036410f921410754929484c90010954050007400390781d401d0164640c1960420400c60940740910200719104600744c11110441404042d806000d410012620390f90303140100c10b02c21108402c0710301113010f40c0c450014100a1180342c0c03000e5030180040c030506c03c0c0c1c0702000c034560301034030702801c0140300c01c54071002d050342030f2442614010440d0004110141075148220141e418158104811901d240015150702d850320300300fa045000100b00c00034002001d184182c0c06100104110441851098580160480107140c0249104440d2124000300402c200c42400199000c10008204104070704000d040103000f03811074001180d03140b090700c2c0744962074601200c0da58112403151880f4002507032504004c94255400c0003c0e902c817a40c6e02c002c0c00d052441d0484 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 362873534 1250 362872284 362872297
    0x71a0a06090906020304051903022a09040c060206090c0907141308010b12011b050318010507050703120504020a03031409030a1a01060c031e0504091a121204050f03070506 75
    0xf0301507201d003040c0c10310504100a00380110202070304d46161320002500400c08034010f60b40a0300c00c84080300c101c0e8801105d04207200404c2e61240501e0200301c20045240c000d20184c1e0355503800c454056690305a055031740e0182d4950240c3c0300c91560300150103113220300d0645900c008140314190a1088400c032071801c00c070182c0c00c14030720344e515044000118103086090401c1080c0d600b00900041c1c094041d9240709032502142e150400000000003114501212041092601200000c01c21071400e00c0e8000e08a42117214101c4c0011440704d550030581c441c502a9900454000740080e8134a0b2075a41c0c180c80c0611805080340342c40c1c6052203503026643d004e1003000315050041132200381042d01d112058074070450503006442880b803401904d40100e58018800c83c0340c032680306540b80c007801c0e807030741c2c195520300450340008111810540894140784901c40b051f503041c030040c1d4089496446c0410342c151110320710141c1c521f04d860103110806c81807a0000c44940d00305000b80c1550720990705c4030b000c10025030008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 362874784 1250 362873534 362873543
    0x6091b04110705100f110708030402010212161a01080318121906061e0e0910050c070201080a0b221b1d030c0d06020a0e130c02010e03071a0a060909 65
    0x40c10415070742540c5004114585d110044200402107480314400824080c1400107403032800044002003c40e4002c000354141c441c288191140c441c40c1c0300c0407815030070b50107504c22904c00521661000103031031100b4510b416506400302840c100025286035210440205d0481a80300100d00c2e451403103400280900000e414847c0c4041c2c14001c42424204190b82e200c0d4401030a50302d4040e01025042c00c0b18800c0c2c81507600b9910f04105da51240d1154510382200b80c84904202880c003c1444920032198004006880c401c3c1c070703845525558400008101c8095801c019000741105521340000c0100308810403112043c03003800503960b840501d000d801c41c807400c0c501e075011411048551204213188070b050710040750f0840050a0100510001c5002140040c20090401d500403400900290141c1035000348041c010b0312003481d10144810840203000019440f4002d54a0920010034503800403003261314003500018524241c00c1520703000040c45a00401e030f5039040c1d90ba100c010a59140070b02075001441d008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 362876034 1250 362874784 362874793
    0xc110a0314030901092103081b36010816090e0f060102070806010b040e331207080604020111160306140606270127080106050306091b04110705 63
    0x114000074008080c1500441b1903400c101c100c1d624210020540a1070303543d810300c0c102085071a0007504019102e00748140010340b01004c0f4a0f80070000c090240145085030384881400d00e1410b111100d0384881d10a20000d00007010b40001440003045200d05000108451134007408080c2c0da2440c101012005542408100400b078040c000b041d0b0b4104054000b402d94580034180c20351410511011901c503500c40d0740036a18165001640c02540003aa10481004088410f41d40301048010324800b040e02c1001d03188101300314202003400410001e2180305654941000b44555100c60b0010741d00081850030141040c450741c40795a071080000701603080151b00c141c10104058540821b6910480401018140960010300003401d110000f0540401e80c5045102c64102409074400100e0300c1190080b40b600030304240d50b002000c14504402c0240460742d901c0c00805c50141c6507010180c681001351001a40c960140118a401044d1415090080d0000803c0040c4104084c480019560805c0c00b09440c035400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 362877284 1250 362876034 362876047
    0xc0f130f080312070c0c09020703180b0a1d2403040210030b030c011218140105010909050d0806030a1a07020601060305011d1302060c0313090209010c110a031403 71
    0x1400009403019065120156080c40390342d003107011104400520f035108002031a108001408014182d420243c4001d900640d40c451890074050042144e5520790082d80301009400070f06082d1a10503120004020303690350b80d46800d40841c20312201e00c50810a94001004071f5903446002c1140000a01c1100d6500010f4407403519004001300c088100410405060904078810702c0c41e9008030715114120403d0a085540911082c200b400518200c201890986144240d40c4e0a100c44484c0c40c184240c8208001e0040340e80f80d02007003083d15211000102035601503000100218004d0f5022035200e080039040317842c0002191502110500c1c45050004400ca0a5082c03000c51541400058054001800c0c14800f552601a0307a034180c19103540080f4079003503c000400d00d60364000d500d2440707650700146000d440308440102e17a51030394810101c114017490030040000fa000b01030f0080d0785080d00c058454450803500c540314004401036001500c5c1d484200e100c004400941f024840c190401d0403800110380710381 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 362878534 1250 362877284 362877299
    0xf03060c02030307090e070c080307180512030f0c0f01020304061a04060e0115030e031b060a05240607060c1101060807080703080a02070f060f030b06030f07080c0f13 73
    0x940c6155010110b40040040050107600315014074111444c0d5850304566944090b4220f07800e9000c200c0c014141e00700081402215540030494912611348203184948854ac3c400403c400c1500c0303030115001540080c40000304051481d009010409440410303110002d40e10b07410300d0308981c01100e044521681c0c4900f42d520f010700d101c2d15204400c81c04e907010030006040450383c94803003005101d417001c960817840e024011a0f110b6000040e0149440d01205e8135021002c50502c003a0303080f41c894105512507030001a0342580d0f1801068028002c0300441000d00b010205095558403807401c1180d00f0038002c0042d5000181107115100100150390794120240361606d4501382966402c1d07120700d003580d00c40f01040c80300900100d0200c049941c4502d2040d588da084c04800da00b08009035018490034007082200142c015040710400c6504107140e0740030002c0032181c100f04082c0d8041640c00c0e40c992100b400c00290f405000b0b220240c3c000d0241000241400b4070501e02c1e00c8140d1001544050300001e0000401003074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 362879784 1250 362878534 362878541
    0x12071205060d0203060118060302030a12171605210718050103090201052d03040b070201110c0c120c1c0c0504020a02030d05070905040203091b010905060904150506040f0306 76
    0x3071021034100c00124040e0300000d40d521418014010602e40031001803072030001c1039004600455015043d40c00708441c0d420006101c8081c40c54072004a4401121601800c240004031840340150054440c0000c071a6102111715410090702424004015030014014070601b0221511a15036903846280ea0f440d10802c140c2030b0344280c0d020505141c14042c4510060303804ca41039403607606070f912854019511954802c030059142e605107107625080041031006209207008070600c290081e030001d00884070104000c1c4414442c06c1414030441e0400d2882c0d00291030000140442d03040c01d842118232468207040060310101c1f66045c407050b40c41c1304c041c03114100110340c40d4580c02008129030450420002003c082c1d100c0c81307a01c4a0030416652480040d10190003040d13100041c1c00d01074021916450841c20103039071003504100212181403500c1200365250302c1410f0220a50b20040c0000d410207190f0020300003e800104882c050509005801107a252a19000b030001407e02d0090481000d2860500f032044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 362881034 1250 362879784 362879791
    0x513020f030f0c0402070f020901030f0506010e01060c020d170f09011103040303140a05250201080f040201091703090d0501020415050408060411180106021f09050d1412071205 77
    0x30742c01451050021920100b03000e5403000d015200503940304100d151441c855101e680c40290702101410000c4203000d00c0028603031010380310740c04a030200d903282c2102105400e02481150002084a1442c1005082c1189840c9801d8450458007c1e156490319141115030014501d00320041c0c070124581d441076a00801c24022025144003551030b0508503103000700b00d00e04801c003094489800045038040705104000b2110381010100074040700714075400843c504003021600507400102980007050302040e803100502c0c012541610361204040c6820b200b04d500e0a8120f000202d103000601c001101c0fa294116600029845440016500c1d800d02500c2480c116402815004200042c8030601401e03c1c006540c641090304010519940200b400010345c0280c034190841c0c0240700702c8000000c21035000510701c03203c4010907490070300107400c1400304c00407079035014409002540200b1005001c503000e08a0b40000d04580e140e1a0302d80304600d119004d103920b043d030740e01002600e10b4600c180521481e102d040d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 362882284 1250 362881034 362881039
    0xd050105010806102306090a0b0a05030109060608070c02090912030c0703080f2a0d09050d0906050a021c1710082415010e03120d05060904030c03050a120513020f 71
    0xc40c02030811150320110f02081091b4010000010b00420982d10102c48100030f0840e41015952400005001026504280300d0308140a041c000c0204505000d4804140b10711082e40d02c240545205808008102c46c02821100c054003842c0701e04100b800b07051000b18841d0400000072981c5040e036250003030a00070020000409400301005005d0120b04951007100541540c006041041000003403000c410b100340840c2d00312040c074200300310b81042004103440b00112900e8455000403540c5403800d680d2881181e88100058220210841c518003001c5407201a038045840c003101d010b0a10211aa810f00081c0c0764000702101e01c000401107103600304041340680405400150003640d2b8400211000400500340e240040410300d0f4045981e4802c00480d0788906c8014105e072400342491094403582c0c1d00c0340014003103440c1401d000808074101a401d03540910360550350070380b040d10243c070100c42ea030b00b055540718100300070a41c0c50000d44d20f650040354010000e4000340c0200c0d80640c8100b01180b0b840e07403502e90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 362883534 1250 362882284 362882309
    0x4110d02130504051f0e01060f0b0904020c24090f1219020129031b03120f09031e100c0e060c0a0506010815090c100e0d05010501080610 60
    0x6899141203000c01c809155000700300c5894924120303080024007100000044070303c009941c1100416003000c043c00070404002c200c100d0302c81150880401c100d016510440c00d041000300020300700340d402061444400410f541c080c5c406038210200613119603030815451200b9409011401409001c014001051213005011429030682e10b080240903d41c0c9084008007a25200003109000703400030f0072801c85000c0064248843d0340c030220511513510030140c1c001d10921000c211444056000581e415200400501200d680340c0322a0305580d001e500505081c206c00e1099041d661801c100c0394280d00d480c90000c44100340282c404519140d01d0386082c610190070522030404943d00900300b0b4036001c0c03040e0703243c550702d054490b2600d00d84603100c40000c0c041d100d001e0000403250408241032000c00c1e4560040c481da604c42e0141986d48850440c0000c1d403202d41d0b0404082142e004500201c6c4104028101e0509070545480356802c4640990104200b500039000b0007026624850918005c1c205240c84032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 362884784 1250 362883534 362883559
    0x6061e0507030f0804062301060e0105041a030402012109030305090c0a0306110c07031b0506040f0b090a051002010903030f0213140415090c09091404060f0e030703080411 75
    0x28218600c81e00c0030300520035100c1c00b08090046c1600013401c4001c1c20340e44030b8003040d0640d4143d8012a803d00c01c0c0070003c0c00308150382c0f1840d84a002140d0480e200b046c0300c107040620101e842501a840644124144440b209401a035501081103800752488080c04c001002e2280d420003400f600d01c020a20303c065004070f008447d56599041d0503406994108030000380d480c0983e44128403034440e220320b4a10512400b0800810800e4031a82211190840d29095600740d40d1441402228042c4d0b02840441018005c400e005581d011000b5008140e1300030b00c1003c07415034500201e019205803414260040c0d45a408482c01d154050084010840d801101185003030440d21a00400d2400780c0500814448000e04640304c41c0e450b5000700350540c007070b00031700074a07148e86a6a007401008040840d101080c907148002070300500c180310b5560000140a40c402c3ea9a5a9947d0b060040c00540b01100160b59954116000c0c44070801c06800814480c2d100d0781c2c4076040500b40058001c0c1e580d0615481090424540c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 362886034 1250 362884784 362884787
    0x50f0c070b180a05060109060605070203060a020c0c12030a02010c0801230f030d0c0b090303010b04060c051002180906040b030307030c29250f1404080106061e050703 73
    0x8584500707801c0407a01d0803030303100d07034005280c102082d144000151050301075000c10f010004c241d0f203048500e202800c015240c2d40b100203980502880c80007a516030000000501c4510740c507001020b840c0030480c15200c03200000d130b0018200711610983c0700b045903c08195115038a0302482100030200341420045020f6142943c01c40b201c600b00d803010013000150045458a9440d650940e401014000303042d12500d00100030300510010f200e0342d050720310000c0392010460324000481140d059030346030785002e0300c0c0a05040083d00d10300c00801e0700310391a100e145040c4911180d1840589400640e5030b11103d044500c03038007081010040941502d00c1145445100c88503980c00104403143d20b1790500702074440000300d0030700d982c844a107a0705400305c410400d402c00740d0340f0228080e9180305d229119000d11060348422041c4110701c04401c000d6010481c1c3c15a0049810f02820764000420300012030b041c6020780b2244410f00b5201203600171004a00c2e0780d007800d04000446c0500b017803068a5481c00904007440d40c3c60 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 362887284 1250 362886034 362886037
    0x2030309060901031806091e0309030201110a05010608010605150f0723060702070e0c030403080106081305071e0608090a2d030c1101030c080604050a0b0904110301050f0c 75
    0x1644203000c0081c1070407043e4000c1d003000400159405540c140d42601c0d0074a0700103040d00c5e00e822900385001d100c0300fa4a4411039682c550702140c159035991201c42c156801560040e80103204040b0b1403042d0054000040c4003401003002500c031480000c21407a150000740440465058424105128180403d0340300318042c806a03640180c10481c0700e034810400300a22038030700c529034060058a000d054100030040c0d4001407610100d440e02c024120150340c4003c600e10b628042580c0c020001541d00700100051441070010a800c000c9a00c142c0140395078a40d149840d00240e0b9001804100006690101c00c48503456608000c1100342000100761030889515600c030003004400504000720410200810b208009010560354141c44201d208841141170180c02140125411180708105407808091948240200015181d40392150401511070004010107410011b01c100e9030705644540c03400d00380ea01d0314100360185002d000c8500b040c088820526007912402044201080c1624080c40400305a150 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 362888534 1250 362887284 362887297
    0x280905150d0c0509030d05070c0e0c0a0327030305041e1a1315020924091309170d050108010c09060c030e0a0f1409010b030609151309060b0409020303 66
    0x58005040b005008042d00c05000d00c04082d40c1511615604140300f58018000340500d600414407521030956408610103c071034100c034009410030041c050900103034001c0e00080b0741d4105c1c404102c440c41c40c18103c0a51a000141401c0d030000b51a0014030040c032020f1100d041900700280d0111041110980300c45c4010b182e034000c0110005928400144210f1030000410340c50b40d84151911814402403001c10042e4100d18845849850720b140c001e28031500002c00010712aa4401820b420894000f0410040c41100301c0700321980f68840c80b5a00001d00807a43c0b012100d00e08110464448210082c401c088410503003101d40f0302d81c135040380c1c80003498210034000d0458002c0d24202c1c440550034a001c4419844401e4000c0c1c100403103000102d144002601000c0503190745c000c8548072402450200507240030b02b8884c4440c401803c1002c11064141400d51507441660700100200c1e10350004041020b1500300c010401810b90307110b0501e0704104060080c284038075801c4405006040343d68001a449220381c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 362889784 1250 362888534 362888557
    0x33207090b09273d060501020d0e0402040801060e0106203a03021c0506060403060b0a0803030703020d0c03090209060108220f020103060b1204060902010528090515 72
    0x4103810a8500310420007803010001c01220061072484440c44c10910f40e80300920381c1c42040b288201013920442170f10172034089540c142d00920041d02410343c01c1d18034407084e160081e04a9001c02c03011401074000d02448008141e40d0006d142c45614146000305580b03090f400c1006651717501030051150180000d004843e400412210509800403240700f00183e003014000e11a40007200a41641c280c0c0e0036501400744821000300c40c5011284103418074040304c10451301c169208405120070b202045503944500c100c0003000d4001202c3c9500c943e6035502d181c0040326400c0029400151040c40103000340109003841a00e8101800420844e90004040301c00040045040184000c000f409074a03804105018142c5118000243c0070b01038204050501d81c024001c0c0e0120781480f1001825038840400c89003034582203000d510c0640c45940d942c1d0f01801d0b0085c8217034100082131001e000c40800480042030f103082401542900604201d00c0030b0616034051780b069102e80090046d81290700d0149040f901110484d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 362891034 1250 362889784 362889841
    0x105040e0601050d0b12150601020a053309010501051903050a020904020f04110d110a120b044d0a051e0a080a0b0a0f033207090b09 58
    0x221381900000b41000781c1801c0c5e003c0900c15000f00d1129020503e54005050030301703c030f45a60b603800010380e5110f0740114010a554410403103034401c0302c05105848216076080045650280310260041824442511075903460303551140100302d28a046a15541500402c50f42419014a551181c50702e40070510800380c0110450000201103644814050711080402031080190044510fa0200c054000300500ba00340f529007200c0c02440c0362500c1c04d840038000f8680d01c000c1c940780e10b030f0320000c013506800325456003094a8901d07c00000c0e810010460445505000440f003400680031000030300c50081494080403040b0045400783e400c440ba040b6034200c001404e01569880c407524083da14061511044100420040340000d00c0951100c415070040a842d801801050340340b008024907540e083c81a82070320480300e0b03820000a108a50700c203c0e40760208030426a44c6460a501c20903400b654000000241c01481082c0f0010903d03110342010050195061000e51800c94117078213050b1a1121403a00710081c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 362892284 1250 362891034 362891047
    0xb0a03081e030702070501020f01090519140607030c030c09080d0c080f0705160806190c0318050c0418020d081303080a03150806040f1b170c030105060105040e060105 73
    0x880540400320702029030800c1d6564604414003d4682d08240030350340c0113025448844c10648014010203907040d4210010705042c515000c0300c60282d0500c3c00c03045407485074048400e4a506818410103207e54440d890106001c5d40418009003200c03101000d02c0c040c00403068041c0945e400c000780714000c003040350801d0000c6d1861030030600501c1c011009043e000c0e460009a0760100a00440d80002c44007150841701e0800d900c485e400ea0312000212042039080d5446109140040300341d4011034610b482a0030f00084401036021028010f0f0903003c402d0380c5590040c954280b890800c0e208142c0c4240f0301501d00840300e12160300042c12491044000340005801091400142c031003140f61600656000d072225070740784c18004015026201051a00f01c4018400c0e2000400200100705030b481142c0c880036200601c0e0712a0741d40f148840030102c181100074085940810030700b0100004610500949000b0b10030043c40c5003c050a4900040c0110b04200c024041004000301415489400c48804d0800c00d4980e01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 362893534 1250 362892284 362892307
    0x901051009051005130c0e03031c0203040c03060e06270307170c060109050115050703021c030b060c030309010609020703050d1e0203040f05011d0c150d05180601050102010b0a0308 79
    0x281e6034008960000804030852000141076200440c0c00d03c6d00d0711075446400480c0105504c07800b94242c1d03e61b0810301e403801d511070004694001d42d0b008e845203c5601c030307032520781c1c81d1201225041090059154065420700c003043e0540520b500110207007070070b03c070716035401c0c01c2801d5160300400100408440d0b03003200f014046d20101e01500c49498146003103400a40c0e4840074240070b0301c0c00f8400c00105a80b1040030407400707031040701100c68258060300100742020019840524054002107400308059030361898100c640e40f0300d0300501c8121145030040d43c0380d04003460720b5800c45034264420040c2034810091400025080002c2d104052403d84000840e172600809106c02d00345419602a011807000003000704000090546400c8180200000c1004289001c2501e5040c54050070006043d801003500306850302c2c041d103442c56110304214090713003814007030200c0d04151141a182101050030120010303030412410048203005180910081c4007101c903080214240414601015156072000501c0d0b04103903 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 362894784 1250 362893534 362893561
    0x4050610080c010e0a031e110109050a030201050d091e0507120201080c0f0412030507050d090e060409020406050301050c03041a1006080a15180f1104140111100c08090105100905 78
    0xb50741054201602149a0052250a49081c2c001b103404490082541448e548903d07a0102580c1c0003400a2400300c1c01c40e001522103030803ca01e002c0c0c407613484182c1000001c3d0303030046080d02c4800040010350340700300380e107030160501c101500702c1c14401e500260740001503a0711401d01030b0001c08420045550703c480d0040c545052040e500800401c5000d42401410141e0210041a0407401001601c0000180701e4046030000300c80e20410103c501c1980115903d40750961106900510040000441c40d590740b000c24250703042210b41c495201004401c0000b03001d400f41c158aa10301d20185055014617203036482c0d052440340d600800c0200400b03c00020001c2c1d001da48002d02341c5103425180d80411b5075505001d12100b0003024108159810990003051103d801d00441c44085034a4076050304041c203000701155a8003072415001e041085411860b0341200043c00b425851820087c0080342e4100b10b4100a008414081c0c2052101d83c50303c4100013080c0c90603900c0340b058443d07194020501ea15002640e4844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 362896034 1250 362894784 362894789
    0x3e070212100501060c060e010e07090b010302072901050d0f0f2901031509020310020a0e120309010201060e06130b010e120313050a06080f0406090f03050304050610080c010e0a 77
    0x3189840b00100f402074001c1c01c0400c0c080c0c405c0e04180320344045d0001041c241c0d40390070480001544426400d000d426684d030040240b200301072400509140c1107464440f6461220050707400010a120300f905448480c1440140c05824280c0e4035050b5211281da803c500b0841c0341b20060f0a00700744200c1102009104640e01b15610400c40e00091101d41549800e1600d200038442118503840e8250000d088900da030141720f40c0660010b014080107812801090041e40c08100c91404101700411410520703500c0446001d488441c00006607140c0314824006400c40305135410002411074458100302555817000042c1160616500700491002001401030302d03031416402b20258011101c03c45144000310010103001c1c0307000081818002c580d81c075024042040083d008081c0003c1c60f07680041c100449102e0300d0394110340f15110001d54169243c43d54840d204100038100c00082c400420700092000c00c014445e0014001e204040c100c07840c1001a03642c0e045103032502070610000214a80c1070303940300303200f0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 362897284 1250 362896034 362896063
    0x100908060408071a01140f0307080703082503050d0e0a080301091a031f060f03020904080c070306021201050405072c0d0b01061e03050123030c043e070212 68
    0x10305e584480b10f00c00e000000d400c0d00350180300d811018042c40c2c0360004100b001c540c80b080180030741d2400c1d034562441c191f000e0412861040242c000444048910f800c3c01c1c041507001c0d60b00d054644009021407001d0b030329000030304c8005030302004040005c6200e00048174111501c640c400100c0c0300703401103400d0640d41400c1455a05004851100d400c07040031504500c003c0c2c496510801c0307190744550290408400c5400042d40140b8540006000210780100500c010351400088820300b603a66516031040c0e1340300140d4500c00c603000200401803400c0501032941c004075603080900d4440203c803140c050545402d4268442c06003c0740c01d5054580703031400320410301c540002003440c1d0396841c1c1070090300750105a4042e18150214100c43c0604910a108280c141da800d1007958054901c3d8081c3d1012560140800c5985400784c000c10360590b0f43c0d188182d40706c0d002a02880303810074900111041d0112a400082650703211072813074540c64991407204861034182c1c1190b814000985070200d20780707400b041341070340c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 362898534 1250 362897284 362897333
    0x1b1b100906020414030703050c010507141c0e040b1516060f050601020607050a050409050709090203070206010501120b09040f110d14010b0d0b040b0601022a10090806040807 76
    0x1803001c40d030014029510013008449540000c030080c15502c00007844060400d401c00d030f4405003598850001041d06a0144542000f8403038004446800c00d40d4080c00150541010004c8142c1e0701d806c000103a050303040031602000b02c18000300206000031441341d0002580c0000080b6440801c1c16500700d14031050b0407100402070001006000300041c04169041c0307000d40300c3c2000040d92640f052045a550038109c0d5501424540380171008000303000701414000c01e04c14403c4001c00c4d08040c900c080c612511003a030081610354500000588500c0380070001c140c01505044910f070300c1d5100c0b28600c80d04070742e000104004041070b5040c0703010b20040e01e1140035408401840c1c40e1003408101c25400003c40f0b086030003080841603403c208290744806440080002003100001030100b8810141c0c01da110758180155120941007802c0103041c0d00b61500010480b0701014040f0f00c160600440034510000141400d0240508098450f0f82d6150b0040004180110020f01c0d0402c0003001d655005805c1014080342d07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362899784 1250 362898534 362898551
    0x2030c0a110906040926191d03030415050d150f06090608040b0426030a0608100213150e10030b090f010f052106040c0e1b1b10 56
    0x202200300c1c4001259100c0d141c08804920203241901c90b0800103a400805a01d0050800e02800076440c0c12848051041d0340921409083d41c868050041c207103a5543c3c4c0724010f03030314080042040003400c01181070096006202c24410562400c1210f0351040540c1055502c0c0c05001031701401515084180c8040142c3c100b100040d807101c2000c0000a4030400d4450084c001d4965900321050541200d001c2c14a090382c001250200b40141c04003007549559111b49007000350307074988c04942075000b80d880500b400c2c0d5a69082200400502500040c40c80d0040294070b4060040340308541c880c041d000d40c000b0403500c20845038003940030700e00085090700c000d400e000300040400d101070300401a0400d0309000b11000c2c00010a265006085c01c0d06a0b00107a441509a07402c140c14801601000c0c140240c0d448150840250700400c1041f215101d14841c83c80b8990031401c003004a0301c11340300601442a2140c00003a440504078040c42624070f18411a2465104900445405031070504502e0707090501030b00c0e2000c01d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362901034 1250 362899784 362899793
    0x60605030f1501170d0c030c06141b0304020901050405060a17210a1713020405160f0504030b040209060a1e1401050403030c080903010209091e070f0c02010305040302030c0a 76
    0x8441082c51051002840d6079a030b550390003180340310035030396074454025000d00c0000c01c0c0190510742590f40245003a01c49030680395110b500f201c802c00001a95032203640200058001114450901c40c00300c10400c0c0e04500f070607804114a108103001d40784c8500d486100084858031400e2a140003401a40030150800c105403d9194580a15408000c160001203010801c91f0104c0411105074954699890310741602d017151500c1500e001501c0b03800c1d601440b813240b00250f5564041c40d8010f980402c0100090032114030040c0c407509000b40c502050020a10042010036400c0c62460b500a0701924a025035507503017400648100a181c102e1042c1f000d000201e00e007001301c02c0100c0010388004200c0810016000030054502d8081ca120040000340064054400525404054418500f000d00003608210241000441415045544090620740c20402c100d201c080d03c00d0700c9800c08080d090614101001c410b0081200030b4041c0040e0501d6160004101058400c1007100d610202071011340d1420141480c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362902284 1250 362901034 362901043
    0x150406020304020117061e030c1909050f0f07081e04031d0102010e0c060904020906040602033a0b0112180309091103160903020409081231060605030f 66
    0x80c184d0000e82d205e440c0c50f01c8030704a5000c441c018100200900c010054849588050120f0a15440e41501443c075414080e07032902d18084054030302090b4000310b02c80c204061403040b6480140103108413540402031101340907200c101d064101442d440d200c0c0d041d50b91a0713004640d03100b41e106a4617803440d42e0b40c01c12062651111140c3c0030500c1c1c80700a4403491980c08012420b80e56a86812111a04100700d140740030b182c10300041400540107040507003010091790001d6206c0d00150b01c00c00142c2c00004e040704a0a86e00a0030703440d51107450700c00401581080c0040303283c440011800c3e0111694440310400c91360300400c1605d82039200c1140602c00c481c502c8101c1e00780501604022404200003580c0814081c83d039001d8024607540b84144642181da608540d00b0010807104105d40500024035030110160f121409005040381c02540f11541e50350101c001c1007080180107280b10488a1103155039420000340c8508030099290b1204680250307d8203003007010040540f5804140c0c1407060340110b4031700c03580208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362903534 1250 362902284 362902291
    0x106051906110a0206030a181b15171605120411010e01110a08220e041203330f1403010b011d0d1401051e01050f090c0307021504060203 60
    0x80d61002d007894508006503460091442c02503000b001030002030032002d07184d800038940040e204010f148031910f41d1144404442e00d040351409002208505004042c0003917070700072a5403040d240074501000c540030a4015160060481c001c1500c00303034101000e42e0711981c140e40e00c85824542d10300c1036082520708002611185044540811404c004182e210b6000c1d2070907070075140f0224003400a1b10030598580500703a00c0540000122450b00145080d842e40c89207400c000741103040c1806245040c00c0c101080750f65141c0303140b40200350500ca07160042d14a50078401551000706078444410f40c0102074640c005545941003018062080e03000007440c3d90100390180080c92080c1c008101d84003810004458202c02c0f03071105c03001100503100140a9080104a10040500812009508600e517203a01d0303007510710035a42000640ea42c0c07030328800c40303003a54040e40d401040112000420392000f00040386066200801c000c4200e1801b00004407075600901078003101c0305e02d6074140c1e45207180c0b610300640250010b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362904784 1250 362903534 362903537
    0x4090212070317070b130618050105061903111e1e04110703081b090a0b03060a090b010f110102070209070c0c080601030218040f2909121b0106051906 66
    0x2030b821103d90b6154081103450103900030105004560b5000f02c0d160360400c101a00b2201035507184698030703c1c3d0200b8004004094400c000115140c104241084202001c24032000c80007060b03140c0c100000744403520244e00d202010b540a440200c04007502e101141041c0c032840d40c2041d0300007442608a6211400d00311101000c8504000c0b58100758407034030316401350748402402b10381c0403008580168004480c14402025030761403d444e006104010451010990340a00c0c00494003109101c61403070a400c6100150002e030004210003590980003d28134a039054400c000d0191100e0805994402901240d400c1900900301c4500e5007043c400041c0100e040c00e40950f29040c0c3c1c11404925803201288007412a0340050420503005c05207004240441d10107082100c241c801401000c0c0040c1040c8440f01d001e100d024020104018a5590f031803007203500030705684480c0c010b0b2003541030321010301c000d440c80300080650495406802c800d180e401084d00341c0115074403d01c6010b090003c20884592201960b00c923 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362906034 1250 362904784 362904803
    0x30f1e1e06010b0d020d060605030901050a15050f1504060207080708061003230d05090f03070f0e0903040b0d0204050a0b120604020901021011131a030f06040902120703 74
    0xe034065110142810122030940041004112101d10707003024040e161082d0100502d800032034440c03901120b011b58013039000328802004001d400c00c028405c50f90310242c0c4482c01e0001d10300c0071002c100d549810f40520f9124a010803061341154403030005031078140400a507000d64032a284d9001968603082d0b845191000e00c900040419401030208519002e4410041c15010176400c55940441c2d800e19017540416800c1c0d08410342203000020000080c1040300c1c0c0d1102c9036503100d41d60030310510b50038004140380a81d010304410019801c0107030701e142c102c4582d800800541d840d00c0c0e803840c1c02c5104680c0f103107102c1d00300456038a205e000158001d02c00c41d5030407241c0c00d0f4050740e00c03480034040740940003d0701090300b040350002d034803414643c004040d51441441941c01201020b0b0709602291450240d00310310348804a90200010040402100602010154458001302c2d0128030482480000d19208410241001050460712550031410700781d60b0040c9001c002c562041041c9580340c0d054402961110300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362907284 1250 362906034 362906053
    0xf060402100c15020a050d02030f100519051203040e0903040801060e060f1e03030d0b03010e01020f0d09050a0b010320090601050a0309050a06062c060a060e030f1e 72
    0x62840c488032503800468050155010342a41000350442d00d41d103806d2000070444e01c902e02c1c0c0c1501c000c610a10100c0c0041c4c880d42031040c1c1040f403240643d00958001c00c513030700b40d1007807444000c1028000c8580840701c4442c1700740c1102005056010b04e50200288454203400d00025140200281050310f9050008110312a52404900c03c02c08043c1d4000d90021a141721304042424141070940c1700419000110303139010a080c4c04240365902c508031500300c040e56440d40700e440349003e0240030071059102d0001d50038003503480340010171480f5802c0390214190382d8049410030070000b8007a48c01020b8201c1e031420b84540e96030400c6010350341c208503003184020303000c00110348901e8503100d4a40a254103a490741d0034450040d40560040841d94410b860324400c840c003800c0050701d580070b50005440341035040e14130b01c01c09020480c4140010050780c0845171034401000305544071285048103c070901c2c07402115840b2130001090901542403100c145a004040c45805814000f81d00240c1136201078080300d072501e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362908534 1250 362907284 362907287
    0x40803150a060e010c031e03020d0b0604031101050d0b1807180b16260a1805010c0f0206090d12090512100c02070f030516090515060c0f0f06040210 65
    0x14250040c2c4020812a000c0d889880d4482c110955445119080440481c5030782100011383c0201c8140d240f001a400081051103070442c0d00581060301400c0c1c524074101400c503510700350040d02110f2918100000810300d0030960300240c100481002c00a0b058041d203280c0c0d40c04048152104854410119094404065000340161116400c68103c1c0d8845418080981031400f03141104800555a014088482001c00203410201100f400315422815540b038007111009080d031800d0503444408000e20110030021070340c108440901700ca42c40094041041d5140c80080c140c0c2c0a2055529089230300c11540e0020041443c2c00f9118056146d2692100c1564640c01c004541180f07070348409098001c0c440d004a003010542205911001c9801659041910307100800c440b01040d90040d9141e41c03011201d2040d10160840f0345015241504040c00549400900f0403000c039110144a80190800182031103120414802e0f80a845110780584201070300002030241c1d42c0c0826a41644144c0307a0340c40c1001c015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362909784 1250 362908534 362908549
    0x90804120b070311090d0b09031315200a080d0e100603110604031e0c050d05061b072001051e0403050f010905071a070b01090f050c130b090607060504080315 69
    0x818000700160240c94079030b1f035011880340000d81603034141d11080c85901c0c030b100b80d0011100060a014070345000d441e0348400c0010440702280c0c0390584c003074220720a142250000031403440e0380981c100b000e45665907000d400c03240050030900100303030241c00f50724040600700b80c00e5045034089078000d100a1145c0e6441c04104044c521803488010281e035950606a282c54500c58080003c03107000b45224001d4582d00c00100d135a00107651001c94190700100c0402040c200b101d560b00000340c0480d0900b038100f45c81982c4096035a2086c030301d00401c8401072070212169a02c210708840c4252a15600c0c0341d00c0700b6200100a4054101d400101d4640c01041c507210100c0030305110f0b50600710b4010000b0700c00503140450f03d0120082240c1c0d82c1030140410003103240811642d154107030091051920001b00b14103850410400c5600150081e030206034100040c40c490100309454030251940d42c5080313965803030441c0002e002ca11a580b00113003000d06040801c402d1182d184043d51042e60300101e49600b0007104410410720 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362911034 1250 362909784 362909797
    0xf13140a030f050a05161109010b0d05070f0e01051b010e010903020c030604020a0e0a14040803180601030c090b04060f03050c032104090203040201110f01050924010504090804120b070311 82
    0x2a40621a03880d4208400001c0f03d000c6d0f000b50210b4140b0002a0045500b2132400d030004288000d0000350303500030034454450254400d0306d514011105400c010750051500c40008000744c10002c002c14402c62114200300d0302c49540c4484030080101410a81032280a454810016000b601414103240d0803420f002c00c0f80ca00c95640103200c54603287c102a4140110b142c007402e29060039a85001c0c0740807044020f24418010b5008250041e00c0c0d00e00714003403c5c07008a50210104c0d96801403001080000c001c5401032007a2100c40e14049100413032840030600a180507440000f2030758619000105220001c11440c50300c000135010344103001c3e54021030410f1a4014303802603241e84402c0200b0000c0c02c5045c4d000c0d6400a00c14035002c070500d0410b0004529140b2842c1070111681d40d100203002c1c440c5820016450007007000c403171002c01c10242c1020026890030510441d03000300c1c6c40700e141c80100030039002190f000d404400c1e9070350500403681c1041c0384d00d03610494a01010070320f00310800c40c10100f6041603421 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362912284 1250 362911034 362911037
    0x8070f020106180c02030408060109020304020a080109031d12070315050c04120303050606160b07030513080405091b070b1b0c0a060f0b040c0c050c09010e0f13140a030f050a 76
    0x76907910703d418000108050400001103000600012904240c14400103001300b034208409070b203070b003424010010072204035400540d80d031703240c04880c20010f508984c034041185c07160418415415907002c0440c00c04042031030000d070b150050300804001c1061152407490101c403105820440c540e180546d8450600c154051510500c1c00c000030000041d102c2e41045034032402c064006801c00441a04488844244440855400e8030080801002d29494401d903030340a2480d9000020220745901c0b010390070301c1640100c40c06004020000b64561725110071038803038072808040107507541c03c4070704100e01098000da80382c40031040d4214070041d00e0304495041d208803403240c901402d0403c1c2150342d01001004d0070b0f40300803016601c0301095103040da1380e803096094554480e1250100c0c0c0c220f62800c1418240324058242c400e031160401804101d55842d41c080e80030040302040d040f0358841e0200761a40f020040d2005000c4403402d810b0b140c4401000c41c41070b82452183d00e8110150000a80507200c50056420030390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362913534 1250 362912284 362912309
    0xc0f04090f051608010b130f030f050606012c0307050607030207060e0609090c1803070b120a1a0907030902130605030d080405030d090218010f031509110103050a0f06030308070f020106 81
    0x704801c04200140303c40c15110017070522080d42e1300204000c0e103c40ba8016a152b54400d40b642081c00405d00c2090b030f004c8801d01c0d000320300074400305640c0c2c0c2003603000340070500040040010722081c1d00d0030010b40c2c02400008044503111100340c034009655060318041c0c0d40008221048490050400005481140c01c005101183e19075600c50301e01c6041e000f812400c0801c264007000300c00c50b61428041c41c005000d9805c0c070b4075540c0700c4101d00030f1035900000d40f00c0c5501924000c901108100c4e100049003410100b110340f600940c540390011000f402c800e52001c1d45c002044510701d1028811644010b040f508140c0959070081d181c0c071010358010700d01f19005041d640003084003458102159009082c924130050002c40e5002e12114019400c01c0242c0001e255060300c003009100b84400b5440955038600c0c0b0150910481c5041d65410240d40c8458081078141916080891403001a5030001c1a1100285404025041d52420f000f0309991040e68002c2c042008080c0d060307106441800f4030401d46540c9002e41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362914784 1250 362913534 362913539
    0x40c080708030a1e1806020d020f030c100b03240121050715050417071e08070e1e07020c10110a0f060603120e0a0e06090f0c0f04090f05160801 63
    0xa08050b001c04c02e09010000c600420200c4166011000c001030941d42e402041c01741c09155002e403414a0100113000a90710512038002c69000000e107500031241b0108010480c00f46440110b4a031840c50b54001c040d0285200501c0c0c41110806506030407112100c100405040040d00c040c145d06442840c040c0060f00030a20a000c0f8200254021140c00d90518103289495501c01c4521405140344100003400d4000301020000514045804140940130004080f0185d140c80041652091144110b200c040219800110041d049200c00851a009204403100520b08400c0003511055074541c03071413040c02108011700b03400d4032424003003044000703580082c50b4142558030350402891401d002161007985400020000031440449060800269100d540004011004024400116402000e8540c264404000d015a6071a40b0507800c284410380b04095503c0342d843c84d600c144199524030001c81400140020424034662000c03884480007a0b0401280e21141070641111880d401030400099040300103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362916034 1250 362914784 362914817
    0x70209061519030603020a05100c0b07030207060603030305100905010f1a0f0a17010b131502070b21010807060c082104030f020d090605220905040c080708030a 70
    0x8800900c05207070307031141007042100c01c400d141c00100d4081000652916001c1086007020100d01c0c01406089914010018507200f0040c00001c3c5108043c10008032070300820300d604c0c0258111003030280c001506012407034503428050082c0c01e041d1940c1c2e441c44808400003500968910415060700c8031000c0610643d0700c0c1003001c0c4d180c5602c9810a500080f000c020420004610000603d481d0790a619142040482d8044480c142a4140d020031641c0204100000300e05a83d4022607094038190590307400c110300310f024100e20702150742d00201d8444100007858851402c29003214100b61100c1400300301181e8840d070402c1c0d10f500b020702c03c16003c40c00a580d40d03000514108080c1140d21000c403060941c1c01d100204801d004030f001d4801764041081c114240340843d81c1801191070605080c202206d245290180c000d20b24818090714061900004440a44450440c11100000d203030444003030040b41440c0c10080780c04401c5100702c040911500b0303400900000080300b541e54132a242d0301d5489000065003013 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362917284 1250 362916034 362916049
    0x210e03160507230102060c030f04030f0203090a03150b030f070501030c12060906090c020309100e04110309030c0f0a1e020a051f090501090e0a020a090503060a02071707020906 77
    0x100c03800d0040000100d00043d070301841004901d10502c2e2014440b014400280c10070101601010140d2000c004211300c00000c0c54015801c0740d8580380c882e00c20304810f4801c80c25400b51603501e030750141d1090800024010040030310b0403030f2000c8001c100007001035002095615400c16078035105035001703810304001c9580240d002c9000800b90b4104042c90300c00620f5840f00704c0341181c01c40b0011950300da0f4180480c07591031042141072a0280000c61603c408500090380110324005080200140883c0c1110317151100c1e040303001e80001d48213074541c40382002d80049840340c1142d100c0e4285807260941100c20100005101c4052540206500800c8130303105114412544003000181d030807900c03c0d0400100340c0c88640416004540800074907001911918005014000076807103141000000401448800c010010040d0082007120b00180d407444120310544203129254031556250081000700005070382c680c0c006000591184030f1030060ba0a43c103030301e04054010004040d41081215000880306d00784100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362918534 1250 362917284 362917327
    0x2011b020d060b0f030a0302060417091f050d0204030b01030212010507050f0a1709061e060a120c03120c03020d0201060b07120e130e010e150402010503100503060106210e03 76
    0x1c0a043d1402900780101b40b904466030021001684050100428032070201c407112420401d04185915201c4d9250001e20140018403d102d40142c0500d5034046407801081110704003031001600759115581d0742009030030440e0910080c1e004405960251461aa040c461036104958a440d2542001800c5c41354103440e8205041001c01d00c5403444041c0324981c0c03e1940f2900c04c141410080000d85032070110600640000e88000c00412024001d015040e6501d050210584a070100303a41d5020f5418200400484419440500f000c2004003009040f5131b40100c41790b5040c2d010380c080b1242106281422400c0b5a16446420300461003400320b940000c0d0140d03c00d611705030051400d0740e000810300000130f0700c5840d0712058441c40d55444004141640080c0104009840c003c4007030030308107140481d90030170300c40010002810854004001540d8843e1510203c0181c40d014080350000d684a2401522401110600d8009030440b00084542a105400364641d001055000355082510f481b114940308038458 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362919784 1250 362918534 362918539
    0x12070b0f04050f011b1e0801090911060c010b030f1c050901020a0606080303070f03050402091b040f0602060f0a05090703231b040c0503040812101203080402011b020d060b 75
    0x40c0745244091090062605505031400301d84010b50082001421203424106003c03c0d1b5407000d006402c049810034056811602001c1c00440c032081140b070030400021180e520142d00c00d20214084036209015072200420300826412113035113408149000340eaa2021165440c4a200e1500301c40d11105d101d0009890b5a982c1801260745101c09640c1d038106031b0740c458100114a030f00200401a001c2e80c0101d003d4a070041e907040070003040c01c0035008500a402c00403d0781d07911600c11021040010141002c8070003c00c1500030011100d44c480c0f40094480c5026070750070003594800744c048bc448050b05d00c5805d00411410008007030141c80d41d03440c140b400a001d15143d200700c10b001c950201040e006e05c04014841900d500c6103841441035010401280c2180c0010710400c9002c0c02000009100da60423a620f0408500c0341e0019540c030303208045003102c41b60f0020000c10106441c09410180c20000460203207200740c0311000d100310703c61030112105d01201401303540085500103502c01304005921020428401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362921034 1250 362919784 362919793
    0x307020126041406010914150604031a010303140c030702190f032307050102070909020307051003050901050f06011209300e041b030209041d07030512070b0f0405 71
    0x60070701c0c0d420365030002c89055844200d070780b2200e959003205000043c050b06031080f0800088062804e6400129401441032100c04003038103541d225566103c007034400940c0c1c408458000504544144800701d002171204030f001c80d07070000c081504800b481e07041d01e0400c511200103508205142c2c003004071510f441414210084660707140402c5121150b8241c1c405140a0195070203076465024540c51404100061118140c1048a09010aa038040381c400d0032551002404101c080c41c6000090600c0340c1c5903c000d40c0440e00c00203c402481e0550801c4c0d125044940c0200019074405607a10820601105c5a038009803a0500d603142c1d60010b07a000700841030080c46180c419694008001c960110291190b1407040c03904c5088070301003640030b10792008901d405d440c01d111000c01c420140000702c1e001d00c1c2010030f06401045402240d100c40d48400c00c02c1c07241c41d00c036082880401503960b4581d01e050009071a00d0203280c0500f40426410011940000c1d800300e6403000c26a0354020301c0300340300400351044070f00d4081e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362922284 1250 362921034 362921087
    0x9040b04020c030c10020c06060613080312010303020c0a06020d0c0524061207030803043306050f0306060f12030705030f0a200d030c0e0316030501060506030903070201 74
    0x4907440a4403040007454010750760383c2c0803011040c1c0382030b00d83c18404510600402403440c1d040c0000c182160458001d443c0c042d03d440b41d81941e298401010f4011456522000c104100700072040300110303048a01030b400760b0394190148401d00608148038040d0300c000d40c0c000c440d000d00b01449200030006090103003060392000e202d9031044500601d0883c42c030207001c04083c03062000318a0540c5a5034092002600100b0203580342d80e494184ca800003c002070b0040e00c0115000540c03040d003a542d207107004c11000420400b4910070395a40001c0030b56009540c050940900c0401150500240d01401004001e0078003905020720380030882e0b000040011304032580824485000001c0d0108049c0600b102035500d042d8a91a0b403000081469680050204c0404a4148440c0408002242543c1032040c02d01d00030500c000988010b032111845c40d0034030b85e0544034680c002031000070700600340c1c4280d07403251b4000e001e01b60341d1300e0802c0040e00060b5030800d01238004100d5000158010b40c240094601c001c1611406141c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362923534 1250 362922284 362922289
    0x905271305031317060103050601030609030e03150103060509070b07020d0609020a060903150204060815041805060f06030105010f14040f050a05090606090702030d11090406080708160e060609040b 86
    0x4000c861140f400321520030082c800120760710180041000000000c120a42c5103844465451406101c040e010035074584484d01418443c408030b0711410409002c849040903110400c00d40c0700c0e001d220907900940f80202085101e10049808400c5680d0301007401d040c03030030540821078101d00814045544a555003041001178880300100001000f01d61951070415156080140d1035005003031080c04a544100300031f1210355040340e034041d00300b03070661880c078041e0582001040062400e1142040c0c011884800740c3c003000400030700f42d445102498a0144c0e030b51503110500d82611003c0c0180e50500404500601118800d841ca0041c1000300a001107460340d040da071140c4c21580c040e0740e6504c01c0c41d00d40c420090500001c100598014009076440305a914061034002c0d103e004001d54640b1080e200e4481d01415400700003940c03a01c1c2d0000300b04110180e502e002c540d5403400a44915002406100b003d20340031a044512001182c0b410260742d485650f414003004030f2540720385c0c10350360300c00da1300c138045840c98 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362924784 1250 362923534 362923537
    0x6030c090a0608010c050a0f020114010e09070306020d09020a05040606140f130314010c020c1c03030b10050903121317031303030f0e0a03050d03091e12090527130503 73
    0xa2005e5101c19540710404003005101042481c001c0080d6814105407082030180c0e90b03c21030454903406a1038096071254080241072600b203500c041d06507400818040d580f001142d00244a462080b0b401243c0203643d82c0070b22090b03c6c20f61007034002156008140340e80000c004401400030300305034900036150044484d441d006100d4503410684501004120720700340031000344030341c1440c102c450004091007900400042c54183da00410100c0b00c02c1108000f404250091700b1441100310b005140c07071038102014070004c1082d0001000706200b445003506880240080c681240c604da95900d92003820300381410090010618000e4455500380710401440039134100990100000d10b01c83da803807041030103104000500c95510081d0036403041100d14007c00004e0800215212810a08d05001c200b8009070300b003101a40440f140c0354829800390014510412810803001001c000300c1e9299144501c0d102d80501108032641402e601d10f0948801014100458100c600340d03020241d2000c03603116010f1a5a0729055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362926034 1250 362924784 362924801
    0x4060203221505010b1201051311071407050105030906151f030608011a0a0918081308010c0804050a030e12100f0608031e09040b0604180c030506030c090a060801 71
    0x64035441541000b10310200d002d1640140441ca401c80e0074995040e4102e61a01c406200d4144070b12440309034007007500f2044e044202281071801d0003541340c411508100d084d070504000420b0b294090000085034560186094074000d04d44a00207103296561800901f0700080390720301141c1d00640c1c5400028a040022010005004040d98041056441c092081e401d462207a01145141d8100140007903e40c6c803400140d0003102d00c40741010402603d040074803a1a0681e1020140825000140251028100c0c00c4070780c04032103074140200f00050200304102e82100c000d0b200280103402c2001c1300c8001c24801c201202121200401e404031118400358654601104042590b05094680040c0c1c064001e191040600814864019524100001c0c0000060084500040c0c8080102082d4808182c54a0380b04440100008c0c01d03107507071652680116984000807c41010065042411241c4032078424080e072406a28003400815280307001c00c04001301c0000050922100c0c0342d8035000012398100900841e0503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362927284 1250 362926034 362926043
    0x9060406030b090907050d0204090c0b041205060903490e0f0601050a0e150a09050a0b010c051e0f010212010602070f06020318010c05060a2c060406020322 68
    0x8035044202c052040403040140003003215045107404000c2629608001650a5812940051042100c4c0381c904001c04071030b081482c000c400401c0100d4040401002d80c046a0302800840c2d0540e9101c02c092503491080b40003030142003010701031810525081c2e80b029403e80100445851041c1c0e407148089014020b51401840ca650300c40030040740840c02802070410522454010700300960405e004a03d981e10303140728100031150345e0b50006007041c4045003c5808214001c2070030701890f0f80c4d00d0080c009000240c0c0c00000840c5003e40401e440e41c01400040f58142c0c1c808041d01d05c0000400281a1036185982c5091282c00340000010a1310310a03c0207004200c03403152076040c0c550626500030318042264201c1c007500b90070b0a00501c08160000250741ca0003100001d100e0b0212141801218004214030009085219403828406452025040301150289600800d054080510344400406100f01031400050300000302040208000390015544509106007a00041c6103201c1850294003407240c0954 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362928534 1250 362927284 362927291
    0x309061e0606030e030a0806032107110102160b0306010c0803011205151e04080405100906120b0f04110c031201180516180b0c0c150724020906040603 66
    0xc030600518400c820250103245010807091280100f11a038034480d941d2810207001c0403400044807981c0c108941d00c178244006009030702c54101d05000b41c10304d8001d100121516840d0f060440c201c0d510020318842c211142d03440d08110186444940c8007182c0c0042c1c83c450401582840001c04101601c0040d0300925100c0d000c4000b40b021810560b042c09000320410003200b03054410311000111509880f203141490a00d01031f000c2c2c4452410103560b1069510884d0000c0c241c05902c0c20305a0480c20b05011100709272a000d007001741040d0030b0300c112080445020b074014840c520a50140c14036034004412030486017902803070b12141c180000d1035234104441982041d85040c005000c1d4061800d01c0c0b500a4107040020320041c04d042c00c410488444000000040240304c00424250480986038000204014407410350340d005841c8190b03450324082884107004404041303c8041200d10401150714942c6c02030225150041c0d0400d59040c025051342642e82200d400f800282c2c4030b6504c840050005020039100027 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362929784 1250 362928534 362928581
    0x204031406060105040308030a0b060d2a020f0d08340201060b121501210c0e0a060e13060806070f2d14040305070b0703080c0a02190201030906 63
    0x300e2800c00020304240c1040300c00d01c0108002004041602c0d0008000741c00812180a544045041d03401168445294581000140d00021864402d82d1526500100c01d078024001101001d0341d032807030352180c250f80039403000c000800528172540013244c001d03a4201841549012a28455550007146110700c550036118000222810350240314000081102402060030f00841c1000c1041030100141b140d40b6103403020b410242168803039220540c008015101010160300070340f072858020705050066601207800079030741041c031345020300c90300c82100d010380c2c4c80c802092a000705002e05241100142c050198440790b000c00c0014040c00564421007166079041000e03c00c20304018074a04600d040b0b00225100c80407005401c060344d0440080c0380701c09040c00c035012440100300c40f241c0d00c20b03584007420a0140c04404285006a0402000302134002d60380c0c00c00b0707616126901d020034482d018041001d13030b000a01c131045202003188444103d82c0141400036040090392184015680b04000159502800401c2d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362931034 1250 362929784 362929823
    0x6050f01050f060d1107210206091c030236300a05301603050901090806010801020c151e0406060b0c060402040609110d05091c02060603060601030c080f0712020403 72
    0x74000b061624401049c29040c206a100c2d01d481d0041105400302c800e10031280700302c601a40458003813000e0903510020381c0e034502002c07190b40903201a4175aa00d800c4910310703145ca450603026408400d150040c0080e00c0d20348000045804100b40d080b540100d0080c03049240124200f40300c0705c21080500300814080c40f0b00b02d1725a004c20f40300d170500703038408200500041010300e0812110380f2440d43d0605005903111a81001a103c1b200d2a510000d01d41c82210000300d101c00041d00688a85114141126810122404489a240400c9131200654003018003081d103000c600c0240a03801601804002a03416250882804c4070341c004254500386a10080c140801c504040c82003800800b030081040140032111048654107209803a50692645d80302c0700420120f09040c07114220503210011516400c1d2400b01c0069100c0d0001c6421a1180c02032500191555009018440340c5100542e5020303210743c1c400c405820945800340a060820841024609081030f0500c024006140100b4884440c0031001c42e8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362932284 1250 362931034 362931083
    0x3030e060c03040215040b030a1d0322060e10081909030c020901090e0309010c050f16060801050303090d30020f07170c060c0a020301050703020706050f01050f060d1107 74
    0x32100040442040200404506141525000b1441647c0450ba03001507201020744010341c048900ac2c1400000384503145241b00300b001e4046400c14800b1800341c2c039941c207002d569106899908580100011013110030541c41602c1c0f181e44400030100034482840c20b200c0210884000034011004101c12040000c01d40c60407900c40f500400322544140800300e41100344980b40d005200c401d034140005820f14004101c0280110300c0f40620120450340c00314049510751035110024401c1c00c005c1802c002c0045890309000c01250403e80000e811000e00300280c0e51238107e091020307032a10f5005402c1070104102d000389003000c0f504c0d0101a07802840000e80c1c40c7c090500f00b92071540003010940e00700d84000415030340070607401c1c00e240080320300540f100603007040181041000c010007540765113000100003006030140d002d000c80078042c14040000350785001c2d0040400100b80113091b48a401400480650300e0543c009149902c5c40047c0418203404403002000c240d002030304220303040400c0002c100640200c041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362933534 1250 362932284 362932309
    0xf14010e040c020c0114070b070503012d0b0a1b030504080f07030b0414120a0f03112d0403060906020918041502030705090d150e0a0201080c030403030e060c030402 72
    0x9804220102c688240a5510341030814114180601071080291500811003540d0810703070000b2440340b00703207050180180198401d0198001049043c800c90001090600701e0b4400c0760a02d5280c80c10040c10012109a19006603807082c0800084103150300801d850400e10141c1540309032541e507100c5003010f0003d0b05104690f5001d03100d0354407085c81040400c480c01b46098000783c00100ea81d0b140380e40309403110300307215031485603e8001900103165086260f2040880030305540c10f540c100b19500d51610071002a1080301c5100c4881e00340002200854203401c0356903403101000d000c1442c9010780c0c0741d5404094440007041590701d5603000c508128582091482c0c61444244220790241c00d1074a980c17107880c1603080030408202e01d07601200007941d40d80160b08842145070000e1100300115040e15100d202a5080c8180b00402800c01030600d0b070201c00040d052004d2603050310345c4042c80d510103410340341e5500000c1080d010180c40704d103100202c0310184035a9000d650107080307896580c07030103006102c04d920300c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362934784 1250 362933534 362933539
    0x80c030c2209020a18120f2904121e021c20030d0b090412050702010207051206071202030c0708160f0b0f0f0f0402010c0501150f030b060402090d080a090f14010e 71
    0x880007100003540d147c1001883c81da2040544c0e01090300e8401d01d100c03001480048100e00034000c0140010b1000d20260501110840e945070071503c002d240649191064101d09038015030b00034000c440a0172030024440c00d00f42d01c1807a001107141024503001a2081c824603802c801c0c0e0b000010381e401210514090003041000c261034035a01402c0680d64580044915000e400400601144660440e84280300560007800c0042580c0d5114404039152500e40d401580c2240c0810318918000b030780a83c42d8020b584c8640d02d48051141801052344410300d10747d00c1912040c205840d15440c4c1400900c142c3d2100c598a4000d0046440c00e1030103144030300360100c0241947c4120f098002c01c001082d100d0398200e83d4010307420328101c90089a036240450140079041003901d580074a40c180450b811011000fa5421203000c1e064011543c0c80ba64280003c03441103418058210f5200c1004002042c8160f0007040011414500704851541e917600790804441e440c0c109600030100340722404502e60f4000060340620b5000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362936034 1250 362934784 362934809
    0x913210513090c0503130f020d0c091503020a050d020102030d050703091a0f06010311120a05150108010b040605070311010c020c04141e06012d080c030c2209020a18 72
    0x200f48024000d8080280803d120ba4030b4000928100324002480800c0302d58047e0003059020010324080f000d0401d0341c043c5002603031800c0381c026032058102481108603034000d00840c0c49981804203002014458001c01c0e41544400c00030f405040344240301c4c41b44500110780e000240c520031803503c2d450411004030804460b00320f2400780580e0310048240180c003d4002d0800090310b0880b1040302d07010b03004425407004c0010b0304804000700c0c5011900958440c2031895825401c4034843c600560381c880082c06042c52410091009200e424010300c000e040c118000d0902c0c66000441c4103446080d1150f0801c0c1d0001038021418094180c14076003da4203107001d12000c00103803460a41462803082c0a010000d580509004001c11016405407141015488441c0158660703080781c9507122801c410800c2103070000552800000700982540c406481c06140c61049403490400b1441c3c5851141485807034580680c3c0c0c1119000031514454801007204140325150034500420010707074102004401d5008000c1c4a10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362937284 1250 362936034 362936051
    0x1507210f050307050a1b0b0f06040608031605010e0601080715030b0627040f05190b010516020a050a080a0c060906021203100504060e150f091321051309 67
    0x4000d0142c990040081c40c00a480d0190440c088684a031032019081003640440919400e00c07011005a92040004084441c05522204d0502c0b007242e0462003941015001401030701c80c40c00035440250a0745000d030002086441c44070001d01d0034003d007a4494000f95200200411540b22000e4445074002d106003400c100381c040c410040b429510940d60000300aa041c1c0d14005c1a502e00412a4039200310003410802c000201017008d040240700540345401d440c04120300712082045680030311960402c1c180d50f05800d265591090035a20b403285881241e000c045041c002c84d494540c1801013006213405002018501550308200448400c039402600400c035a00b1010f2086a4000400b03202c4001e034800722035500d03640c05009100d9100c098000c0d903440f074200000080c80421007032a642c003c2c180c10307075076032020035209081182c80340c040202903400c940244000f0f0fa001445075200740800340110f110140c00c15001c402c078803401104051200c08100049120442003081c00031290240881d00700401c00a072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362938534 1250 362937284 362937287
    0x607021b0f010c0809120d1d030c061c020c060f0a0c020714010f030f0507050a02070b0a090312020a170406020d08090601090b030307060614010f05091e1507210f 71
    0x1e00d1080f01808610001941045035212810311004030004401520700c01c02c10710000a04514072641c010081c035510383c0b010b02262070b01191510101c103004041e0752400c405440c10001d00200c80d00e580c1d220399400e2218554030718050040340c1c490540882c010750949824014201281c480c21a45800c561041e54280600c8840000414500009080a9044581d41d0354120007030301c0844c400324481c600340000d120302590410b02034959081d144d001c0e00e820607201c850384041e40c050010040e0009607030002c10000f0515400f0007a000195901c10795100d001281c841e440300400100254084150003d800c004181c1e0503c030701340b550141860b1001702814a2074445540381d5040c0507520200340e5502c03602615035010070031240d0351948180f0500026584145101c541ca1030703001003e01081124402400051050301115000b02005000c0720b0108641700c002c2d810401d008500c40c0e00328003803c0c80c18a51080d0100a009007902c21a04801c81100c800070131600c400c110007c1c002444050742c050680c0c40d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362939784 1250 362938534 362938547
    0x16150216060e06060a050111011d0604022b08070c031a0609071103071b030b010f0815091b0301021b010914060f0f061302031905100f03150603050607021b0f01 70
    0xd031b10918000d001d808186080d14014045c80c020b004c024030a020607614144008141584074034022a03003a112819068074070120701d090489080b20350300c3c00c100030000058044000c0c110041c0a05580059580c60760b50b243e80c4005526002c50403400c1007030809ca2140f030304180d640c1d070107040361902d18840f000b0040215544d00a5820041030b00d440080c2c99040c11500b84182c00c01960032246810081d40d4540c19600b0460450044036110300a80c00d5088401c442c1a80103070040e41b812008045403101ca1410026200c0c0c0c00380c0040d40355408102101c8a40407190000e6254100300c000001e0309403035031030040000025a110680b280c1c015204215922840c1990385610440f1001a520780d80c1d110000076004c12031000301002850320220601620300c030140e4020307001d0709038000d081046071541c0140d94985040c0780300304214405060014000690595100d03049040400d8001c180d06803680d403880c1c28100d0442d480e10050340507481c04411100c209078140003a030030640707031100348a01610009040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362941034 1250 362939784 362939789
    0x50102070504090204140103030f020f0d050307200d0e12011104150522030231020f0702101e0c08070209061c05010b030f0303010b16150216060e06060a 67
    0x2c07950740040c1c01c10f644a83d04070304203d1603256000c6440c0e42e140d01d8050000344012402c100184101007400032401c2c00040c0400c103200560315000d042d5910200e0413507107120a54207039900c58400020090031080b0411420741d520348207403501c0c00c603a5601c409101811509590380701480e81000d01c6040f100c289202110187e40103401ea0843d40800803c080d01c80d44100d9507515030442c1c0100e60060b2200201c400103045c1c03807003100c0115001958080032840482e500d16440315020ba000030b01c00480c00298003d00381500b00f000c00750700300b012a4002403602800b480b01f85c0f011820a45444684c0400744207100b021402a080040614119840c0c00000e03000f00500280a0440c10780402ca055640d16101c84050700072a4294815620625261b8064140108628041d100710070700840c00003004000e5030b040e640030001143c286000c00740c0042c2c101c0c400d83c01c203444c1c10b004200c100384000e440340014503c05142843c0e012064500345012802c071080c0c00d410312000e80011040c89007650f92144582d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362942284 1250 362941034 362941039
    0x111130314030f0a08040c080f120c0a02031f050106080417030c0d02070f020405010501020a030206040b060f190513020721050c0a06060302040e06010e04080703020a17090f04060501020705 83
    0x44055807812664614440c81254401d65400440c01194440d4031420b0701d0301c2544150031000c2c1d260742e0381030754940e50355001070580341079000001008080c64811004e000216401001c8940c480f201f5008217040072407405002c180035050128080c1d0800300307030251500518140c50011658038260311180001e000c045040c218100e000404900c2160b40354056504500d62208119640e0070305240c001201c1a480070100d009508200c0001030641c0041400703403800e0b8042d00941041c0e07a41d595008402c0c0002040c4903444194a030440b403058441d01d00300040320400c581454101820315042011400702030b40451005401044401c0001c1d40ca5031024441990f50100064048034090b030694480c021014074001e079105050940d42032045981143c000c40b402035804101c0d00318010032668a07980d090284d003500000300c0010a002454481c0100220388c000d2059444498641d9100c0308521002e80c86d100f10380c130b000301c0c050044c1d01d0001c1d421020410210f408000c0d207880c040010f0b4680d002c074442c492 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362943534 1250 362942284 362942303
    0x1a2103160c0506280216091e140403020601050a0302011205090703080d0b04050609040b190f020d090506091b01030f020c03070614100506030109050a0b1f0201111303 73
    0x3020082000e044901402e0010a0203031910300115541d11610440b01800801041d41180002c440c2c0c00843e0741c0c8502c81d400c40d074400c00681450201c20250200b0820700c505107203141e1900c42142218400c6280405080d003009081e400c003814000d140c0075060b00312a1068501d4a800c10042c1c0e00030326491040403500c40040f0300c6a42e00078409040c02040e51001c1c00072900001c4203d00201c06500a80f62000c0446042005032103c10500400b850115401400440d0101c042a0806003a0090340581100150f0215400c107140c032881090381c11802d81c00e203542d91294950801c02400703000d035680c071012110041c03504820300c5ea144030f10502807025060505580d5690b10f03480c1d0107240c0484110008a4048a60703a196904d0200010318442040c0d80080301141d0120761803a040c125203104547c401040b040c116400c00044400134030f03003d03100038006a0348400360845a2611074610341c14105080d4614900300d0740c0ba00c06401d4409100100700084400c010305450b12005080410036241c1098090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362944784 1250 362943534 362943577
    0x30702010f180b0d0f05010305030d05062209020a09021815041a031f0e1b070b090705091501080408071403041401030c1b020d151a2103 60
    0x35503108406001c9012003003103036100420082075100042c40f864010701005c0101a556040300c0d0210307070080c00014680d410410404030051215000180c002100504942c00c003145200e03180e00c40050070a0310b918064803110701400b0340c501141a5401040c00724810f5280c44c943c15803420b40700c80720700d40c0d0610601c1d076070302e85004071000030f016074001c0d00c0214048896640740c0502c0403c641c03c1114030a450354200441103003c014452002e0044403500c00d0b106045031030b003c2160740c6981d9a092403004448040c8090404a125400000d018020400141030705d141030005200056030003d00c1e29140e8241035000c0d6646990261a5079406500070003002c0e250005407400aa03001f040842c40d101c0c0e8800800c02280c00d9210180e81280c0d06000d0320100280782800f00c00f42c0740340700040005001c4003103034191100941002d80f500700351280702c0c9801c2e14030740e602051250704880800003403000e04a2a403038209800d0404080d103210700343e0901c804112032000390307044580d20322603a02004070081066212 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362946034 1250 362944784 362944787
    0x10302030f180709110921030a1116060c0c090b0f04020306030c1915021c0302180301051005090f1b0703021903080604050f0c030a090213020f07050f01020c030702010f 74
    0x43e401a0001d07000901c6a0701130000250f01c580c00119080e889207d80b07626035500c1c015000000e080f02c2000348040d5007000e0340f0617016290f000103520100c403180903c0303601c0403846c070304080c50388081c1910b61540c040e01e1001d0704150341c40400c01e03046180f910307141000e80001d99030799400766a0341d00d1084801580c1c903a25140440d00f48024052015000000c0c105042000000759400750180c51040c40c940d44601c282c00001ca94804d001e810841201d5801c0500c3e407003540c4244c0040412410a00c1d40101407551800801d003194411100c103900300030325510500407840e14004c0306405c8242540c0c0003803142080425100a9950b00e1010107c51000262880805000f8051a000042d00c10007e07611580300f8103010b4910401161164811850200050601c1104910050151104845e0942190b0b900e10031b40000b004520026a40aa4030103450700c0550207a0006000c2c5032041283c7c903440380b00758580039162000041c9164100d9005000b01610400d000080c1c9041c9902441e2115082244400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362947284 1250 362946034 362946043
    0x318010909060e18010c1d190303050a09050613060819050717060405130b070306170a060e030307081b0f03070c031d0d021002070b0309070f05010302030f18 69
    0x1060988609020000a800c400c140c070203071140042240c2054007080d8404d020b0b00301d42c1e0801c008070210b0350580180170088041401300500590250500341c0259050390800c070021460791040f000101e00007511050a5485012840240300544030a41800c43d00b80c0d05034000d0740c01d4010345040200060014816901ea0052503405840342038042000c0e0400140007010504100e20502c803091f1400082211400c15108241c4560b10486144140035000c0c0c0e140682500068001d00400d501c441000c03500d21040107034200c1302d004900090550a000d0300c5d00c08146c881e0500007040b0743c0c10500421443d607400c1041c19602c5030340d101d4210310a900303c2c03240782d03154000e1810745540d030100441002460740d007003101810304602948924007500303003500c001c080b00c0181c0c12030a504481020000001414081c503041c200640c0d0b0700590300d680781c44101c504103a400850310301d112a8092801000f5105c203507810040a080700b882e003036285181c13001180244400181401e0484c1e00ba4035081d10750002c0600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362948534 1250 362947284 362947289
    0x20a03060209030106120b0601022127210c1f030510030611130b0412030e0307080105100e090601061d030f0601060e040605090601020c01050a020f060109020a1d0303180109 76
    0xc0c40c801b000126410070303910501c0e0485400340584101c10b03c99120340505445580c00030a000059454521540800190204849030446074814407950801841d81d0301da8006c00d4008551842c0c03400c6c298000c4ca0361307203004400520940160300e40c0c0c1d43c0c1c0158020840000d03800b41d9050901040644881000340300041c5503a001904051402c104400c0c050303c82d8004000000b2032445a90342203845030070083c0030f4416803040084115945c0140300c0068058441c4643c2c4080040036070b03403c1907550700704c0c130b003903030b50442c0c5152403d03060f003001348040d981c0600c5007600151a64000c01c9950b040c00b5001e4001d2160340780114812201d010304040c01e40d0304202c01410710385a4402d99107156511400030f400c4408540c000b5218504061002c1910309009402d83e120b0001680146103a018030b03001500d45030300040384d401c21401410880a0521020040c41e402071900400050307a512241d40000d048500c4e400b8040d00101c503204844050340d400009a071000c8491050004d06180604016240303501075030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362949640 1106 362948534 362948549
    0x3030d090609050708010c020d1e050903031c0e0106090209030607030e240a0b030a02010e040c03020c0f01060807060c0b011809201903020a03060209030106 69
    0x250020346059019400028849181d40c681c24240741da103411803603541c1e45900d4180d842e00d0b41003101128103003091030103203000c100c1c140d9502c580da1038031840f51042245c049440402030b80e0610848515228280004030041407000c003220140c40d01c00d81c000229440e14100054003c91402120181c4600030003401c0641c0d00e5070425002006101d80d40d404620565802c03c00a83c4c0400c01032040080041c60340e410761500112440c140d07003160325007a00a4001910342c100507604060b041c2100f150454002c5001c0072402011002402410071124880c4034042441504003810350040f0700380d030211001c0d034a105444000a607040c1c0f00c1150001c000701c480303100420103011031040510440c00e024502003942905920707100310040c0748134030207907502c42020602180e40c074081c0e000102c00040001003081003851500084e04250b4a44000341c8039030340018101c00342c0c1e54294014009404030 = true := by decide +kernel

theorem cover : BRFrame.Cov 362769784 362949640 := by
  have h0 := BRFrame.cov_init 362769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362769784 ≤ n) (h2 : n < 362949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
