-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3716
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:09.446588+00:00
-- url     : https://prove2.me/submissions/42a5a692-d9ac-4bdd-b1ca-d349a084d764

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 668165467 ≤ n < 668345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 668166717 1250 668165467 668165483
    0x30a080a11071a0114030304030b0705071202210f071205091009031103240c130b0c0106080f07140607020405070c05061b1210090c020c0102060c0a05071e 68
    0x20b07180380124105042d03107090364104580c58000201407800038008080b41c00014040d40c50103085995030134031201c010704031408000d0b0501c2040000741d28a110b58803082c3c4150020a4200d121300095840340010f06500441c4076824041d50b00b281c449182a25003407540403007040150120501d08a425002e0700303906560240e1600d4144003c0ca80080c01c1c201507900501104e28000d802c5805d15541c1d0780c02c0d200e001841c21350031081c0b03080000c5e03c21015800c19000010300b4500070f15100704a0351244039130450b982c0114001441c00202c1c0c13003485500300900341003000e0079480000e180343c1916030005204520f9040c401804104456440c602140c280b980d00400c104507600304418003d104e41000c8408a80790322070784010641000708440c000c011030382114111303880c01020000028110102501207103580c0b002e07900c0410b0104550082d40b4203d880c81e030041090f04019000240f9050b4040d058206400c070802c040201d00d940300342220300c01c80d08140301c1c0b81c0d4900d01c824242c90030f40f140e030800780400e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 668167967 1250 668166717 668166727
    0x1513080a11210a0e06032512050f0118050c0406030e1207080901141e090d051b18010f140a0e0a02040315050f0f1b07050a1a09030a080a11 61
    0x100302c507025001420070f60743c80210315000081444102d200c117031032101c2e000048042c0140d0314000d0b4076811200e8002440d1854006102d0002c0e44196274065459221002d40d05005021940d200d4049506581a03200144821308040340002c40a11070780c01100d041503151900000341c52010021428900100341e412075986442c0d0078440c42c0f54010548040c0000c0d101200c14015000d160151000d142d52034100d0200d41114040b4010540e21152405420442c0c24116501041b01402010b0103c00b4036141c08401d4040c03141080713200c4215162050003615114010301c00d042d055114881a903a0300010b4034100d0103420009500022540e004815403904c100410581c1c80301500548204c034171030f903d4101420086410711055500449100300303400e03240760001d0025154500800d0708a040d459803140c84111009a920040c5d109a030180c815030f20404140042001d003104021002c0158030700140c407030410100042e100d01c2041c504008124801011403100b072003175407000074054118075243c1d60791 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 668169217 1250 668167967 668168023
    0xc02030a050d090602030414010e0d0203060703060329180a0b010b041505070203031c02040803040305061905160c0305090402070f0c3c0909051513080a11 68
    0x70346144003820300040c0c581c43c0005481c074000000e0f201034419410035800c0300e03400c206c011a10070704480481540050500c50410258a00303204c0c43d40202c0c09940c000c645207003035080c14200380c80018518601017620400c3c20010080b003290701d83d0004508400c116800895840c000c2c030707144444c5405042e00c03506400000b00d00541a0003403046540300b0f0810294101c0901d03096031140aa03001c003030340542003001549038a00403101f10848050080308010700b025200c09005203142c00c80e030000c40e06c560140041c403504510121800365203030b401c1c0c40f040c800c91408100d40024600c800358441c050219400742e44040502a00c00c1d075000c1c40c0003410854813015141848600011207040a9a51074124903012410310401c00012880c56109011014604051052120150140054201c003142c40140c041882d01e0180030721007001c0d0180b030041011b0200310010074200748010b80140d000325100c004000025084409030354103404242802e0880c5d1585044d01414044806406465030f882c4140c41214 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 668170467 1250 668169217 668169223
    0x209030f1e07031707050a0501060b1210080d080903160f03031d1f09060606031506020d140a2f010c02030c0a0807020d060203090717060f01060806010c02030a05 71
    0x205880c0c2200c0d402000c1c08052494035000140000f40ca86519510138510800125004056031445902140c003e85c510b81c403228210350868000300d445c0030000454480445000144581060509400c1070300c070342c503050031250b441410f805002c0901180800151191006100b030703c101150241505440e40307500c5c54402c0f00c01c5450002200070070b1800444450021065101d440c44c1c030b8090b40100714910351100226494041010880407940e16880c9010000707203140034a400904003600c000c0703a001c5c59a404009100e030035401880840d0b000c40d0f44c0f00d22117544802203540703074082e5214050350341c00c0d0380c1d1003101d400d0717880b2032880c2d00c07403080e0710341101c08581c84000322002404010080100e0081500c003240c40c1d204543d05424190302211014000c01c00d9840288903851000b010f20b25941c0b120703175076542a81c0045849081a402018040110703902c103105842003107030b0b2000941850307c0d245034032591108040c0941401c00c00081c0020382d259005152507094207800900b281c0d803031142494141d41d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 668171717 1250 668170467 668170483
    0x309032001050118020c0a030503090109050f0d140c03030c09060702030105040b0601020c01030605060306040f020c0f070f0504050402092a0705070302150310230406060302031005120304090905010209030f 90
    0x148145010210801244c078400e9541d40541003010349043e40c0503840c1107480350405840480a9580c9003a49800500100b006030315420300040940b10030255944080c10350501020304801441c03041001c807021000c04001c580d803000f0b0086c0007070b13100c002080c040303911ba00034190000d4140d0310781001d00051044102c9001d11074ae01c260300300c88031114020011070035255540304850b0000414004103c0516054100e00d020b0b0441c030070300600700003030901d10a141a04c0e0700c03003406058104040c2448178861080c040030140105460500190078258003140b0542c20050803502c9440050704946500f00a42c030100c440b81d41e0201c1d0b99a200e131201d01b003060f100d40c2284001ca100d00300f801d03ca01c003c6103600742907a1141c040c0100b00e02d40b06203000c403080c0350715015840c4446621841c7c01180d41c540d03039500c20040600103d590040c0c6a10f050700c20401c0d00c144a410091140f010f02c04155400000002200c040c4c0d4002000895141003501c3d02c140a40104c1e4030311130341409040106070b0026800200743e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 668172967 1250 668171717 668171729
    0x1107080d060b1c02220605040303030c020601140f0d023730080307080103050606010c1502092e090e0601051b0c091510031b03090320010501 62
    0x1000c1e5a032000b42006922400c2030003502c10f10996807905080c04241c4c0a0700d00103135001c1c14803102c580d103440c04c400004616001103002c584003050920a05925106e141d222580c180000c2040d5414040841002042040010f100703850302041202d00d903c0700910451540c1c1c1c00f4005025034560f0001d800d04119010f44c0301100d03101c01c071071002981c041c0c0004840c12100034903081401c20070301c00d0004803a12120314100c041c11002400c1000041c04070350003180300e0203103a80d500d02e9039410351800b1420f00c50080e017014108282ea503c4000401d51100c1c0c0510b070140f24039001690b410065012800e01d104407a42924211b8050102c000a05000201588082007982c0c0d51001d0a80750116a46803940036074040b80041c0b01481200d4040c8005882096481025011190591840390001da0300300400ca40c00d07848a0750859070790a4a0a2800e250450a019418240705000c0c2d4031591001c1c0f1030320200007034201038407840701e02c0c2414040e0035058500082030b0004803600d1514840580a41800c0c0300300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 668174217 1250 668172967 668172971
    0x120f0f0717060c0307080c041d06012d2001110c0c0a0f291303170906030c0a0905060415020d11030912030c100504050c03030c0706121107080d 63
    0x18000ca00301082e100d2182e0300b228402400d60b202c1d020304656940008010140503a000c10000c01c0780d0001c910b4000c0a00d1800c031081c0384a02e800800141058a1020644a0803d003540000045085a245c1d40d41103103462a03c4502c821400341e440140c18440d4051034120f510300b240b03980c0c1d0b0b044420f0080401c0700007042100c0d0000344c80e4041c400b90f00424402c00c41d034004084000e1000101d41201198a480c040205900102c0d02c01800d2105602814103e0100040e143c1d0800801c0340c4005d51403030142c40115014100031014021890510000300143c030b41d40e5001a00c0d003c802d00501288025190107018191240e40340c440240180740324401000c0544150070220340081d114112070030b840081c18001d1424001c621060001020503600c40c848180400e112001510204121003415107540c407801040343d0500b0305165080c0611000c0903406038104021640500400040300d81c121146483d090036140348102103400249900c0103602c0d116000001c040301805820b4002d41106a9800c0301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 668175467 1250 668174217 668174249
    0xc02032508160b0f0a0302120126010501140111330c03060109090906060306020d0903030e010e06160203070807110906030c10031d12031e0103050c120f0f07 69
    0x18820381e00c0c542e4031400e070043c0b03030401840841c0d01400001d415051024200503052551944188a20031401d0700305812a175030020042d540c01c4103116031039505512840c0200519410807200d034503041c0d0981983c0b814040c84084903404200c04205039081d0300f441c0c98110310030001c1c000c0c1e924007440801060381031001141000c43c01d4151104112401808141c503565540d5141000620250485010542d00c10790b56210010200310b280c001407d030035030f000d0b00020b010f40051a000d01140c000141400c2281e141410a110804000035160340100712441c0d40300c1e0107200d52000700d18510030000b0040040e071000c5450300402115440492907100b00700c480d1042d03681d0300c0d0149960790308203010643d4455240683c1440850080d030000700b4001a40d1122014428400252441e0090313078039a01212090001c02c0100010510041c280b80c0051450f0404030340d45580c99003951001a14030680c0715941c0004059440c01d42084000300c1540d4000944070100c00c00c4102d10740b99810352049000d0318180c002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 668176717 1250 668175467 668175493
    0x9152b050a14071d18010c20070e0408070c180b0a05060307090b030601090504060b0c160806010b09041407081006031103160507050303040f02130911010c02032508 72
    0xc3e1480c280d44181c90f000d03c6240700444c0113240b045024108130405d002c007000126282070280640e500070070103602c1d1203191035041a02d0b4110381021031607402d400e400c004400e00042c1100a465a00315810509598591b4420f05040b8900d641c650700c03000141c0c1c0e61903070b68429484160000250583d0840e5441d0500e96074009019031440111036410029000000902c10416204041c2d0341010040c0743c50201c040e1a10003003802c0b121540c1103844100c02c08a05001110720400820611401c181041d5100c40d24041840d55580c4060161301750001c40820365504a0f140d69120106000329010700c0c0c1058288080045c1243d4000e0355401c0440a40c5031002c600b0500900600d0151480e001088e49141c0c0ca0402c040702008280b501e98003042410002c0d0b5011550400c0a90f01a9025900000100410748100103460b0086a01032485508246004010450349000300d64400b5081c01c001000810320f200203070422176100610180d16441c4080f00340407003204600d100a03691044216006000b60007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 668177967 1250 668176717 668176723
    0xf03031c05042d02280902042102060a120b061207020622020103050402150304080c2e0504030c0b010f060228021009031707030e09152b050a14 63
    0xe41201460740f44084003401400c1c00c1c9915030201c200000c044000c0000648120b00e005990b501c404400c030740208040c00034040812110740c241152200c1c216181c0b666a01080301802481c90b220140244c80005820308a51600706a0300440f00402c100c1d44e800c1c0c000700088104030142c8440005105140010310120581b003207521040e030044064410b01c040c00e038011000b501000304100d03040006801c030310380c0040c00030000c1e5026038400c0340e203e03484180110b1b08919003034041151500b2000007051176215410802d851102e0408005030200b0240c1da40d0405940104e0103c000410f140022000026004c8803103141805032855a800d80d0f44004172a4013000840081142c000f42c40c00403186018018071b8101c80040d0303104903e0906030201d42c3c2d20b0300e43c1401c1000c041d414210007100002d102042603400408840c580d88129441c1645040c41c482c0c078503c00308148861401032420346618610b000221040803017416a60f0085801c0b4103c52402d180c480070f4000003215004200418086001404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 668179217 1250 668177967 668178023
    0xa080c100902061b070b070804050306071b0b06031e101508030306120f03071a07050a0e091003170a1103030f07080a0902100c0506010602010b0108060f03031c0504 72
    0x10440350810181c607200c450201090b0050f03844512801100041b01c1106002926129014107041a1160701d05800d040c10b092001700303842c042011004d24800051074008002c1d0b0b02c50b421404c2410b0694420000c0707803a00c81d54062421002c52000d40072459080e00061600544500c420144650082201c280c03402d02414094003a082e04244000740c4981070075110034014075907030070403220200c0000d2071490035584030400644400e40f4500c04200711680c04511950020041e2400d140743c0704039841d0007080b01480b010101d220342049001b0941c54610305886070046c1da00203404034864154104076034600e80c02a80d1b644040b64000c1021001c6e27a001000380d0380300300c180101d004415a1104000c403040d12006020b071010701d81d03e08000f030160f01c407046a600b400c186515241151075403410030324a0258164401c2c4110b80c1441c51051182c1d034089401d5170010016902c50021016840003c0d055001c1c409100c45020403400301c2082906280d005107004900821880700702c0b80c1503541c00303c5c00c040700c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668180467 1250 668179217 668179219
    0xc030204140d0206040b030406090309060e100e060d06090b030f010c0c03030b04060f06030207060b031911120d05031b040e06010e03011401080a0c171f020c0a080c100902 75
    0xc00c40401c070260804014952aa6100805103032400f40c40d400b1210755900151000c3d5009a90782c8202000c00d50030240e1000600320340c1c140906803104120010341c0f800b20f94040380c400c110242d507410480b41c07580c6080d18500104010280000c5d51141c08a100074031812140521922032615490302c006410300c1212280b40195483c48030074802c544064002d810441c0360b00d40c100f03a41e01e40c00600c41ca48008400050240b95802580c4c4021a00b40802580c1c075001c28280b01e13420980c80d03101d114814525841c07209500c0b0f00801d40c0c3d1085180064402d80d4030445d190740c4e5000700a141e03081658040000c503c0346034280300a1034040d032407151106050040b4043c41c0c0300761801d0300100744c043d802060b070f60f440c0b0310005001040b4400540d410304040343c000e0b0b014490a5026030600e80030444100e81c520080e0074582c42c0c1b0548215040252503a0720003010a025082181d40720314142d200090301210a090b000340100d41661350203240550340c0f60b02442c0c41880324000c2c440c07443c495440c1d50007101043c80d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668181717 1250 668180467 668180489
    0x1012050c3c0a0e0301180b0f013203060a0507091a030f0405190c1d06030c060304020a0e07020a0605070f0c12020f0a2003031213060b1f02010c030204 66
    0x49040010803095000082da003080c84840040c1003880d5409010328105d1100c141c001c0d0007510004d00e404286520050014145e500e061030041c07107048401c5455a095003140440c030841c0c80c5a00454002984c10b01c0b41180d0035010b84003c0221502ca1504011b00880496a030a080e40390b4a18030302110381007900c02804202400c101040300221004101e540050103207055440b00007d94078010f4500c404204d0446840071160001c01c0a4518200800603e12801d10a00c05600d0030b000045d03203c0095006003031141384040080740a6448808499010b0302d06541c05400500742100081d6907040048000c85510f400c11002a9116100c0c00a040b58035645032501101c0303906907914038801e40110001c420031031003042d004401e40d40c2c0401000f00e2040c00b81c103155000e1100405807000381e40240c10114080d034401c0015244e441c070105200d0b90f001c420300249003e0a43c40d4584503000d400980c440582c840101201180b10301101c162410307034a4041d03002040550b610030415016805948a03c0b10500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668182967 1250 668181717 668181817
    0x6020c06130603151206060503070602010b030a12110601080a02040b040603050616020115091d0a120521070807030b010305010605161506060c050706090e061012050c 73
    0x1038000d030420204d003130801c40d140810310380f19101e1118901d415201904c1c2e107a160305042056007418480080135100c244002d011860084001c00e0780c64010250040c451114405965030041c03244a100d0078a80703541064480650303692450341da035040500000e80c0705900c0c0030720003c0d07940340c02e2150000b125031010141c001541c81001440c0c110002d00400c01c00d654a0b80034021b458080c1400000140860300c0d000108654030504860341c0d082070701030300e52103940301c02c58007400300c0c20090403c000409207180c025600c2a6190500e80c07401e000f414680d5244070f00105000006411850181c42820f10b0394040111041c1c25004400fa50070a100c0c8a012440070401032581d4203011800f04011802205140d541111301c0e4241e030122149984924005105001c010080040502a00f070040545282c1503000c90304050054941580150a051090b0403c815400103140102c0d036071001199542d4080040c1d15043c020540c0b585d0003508490860300603504807250140381640c015a1182d5a125200005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668184217 1250 668182967 668182979
    0x209030d2610120f051e070906060e1e03070303030b010305060f1309060207020d0503030f0a02040e0c0a121401080106121109041a1603050c090d15090c0b0406020c0613 74
    0x1c80c4010b00107131000050704460700c0c0401c0c0100520b000607580d118003401c16041411400d402e00103039800043ca0181403800402440d0761020710f43c2a03501040f20001d20141c00041100c0c1c50b02c4050640540602074240300005068041d40054050802a2400e1000d9900c0304100012044c0b100d01c0c05034840c10075101d034001d0000c0c560041000b9440703401c00600e005c1c182d800180f0344128840701141c01e80d00c0000ac00c88162141d14041d138001609260960815061505105600f00001c14400d5641c0011800d207107924814810941b840221000030054a00441c184596155007400b400020b58200940000c0304450001c41ea0701d550f42008901d043c020b1a03501b00040340d0804bd10591707403030000050304009014503c000500030440103401c503050119061001d4256070004023400c1d80800180500603d54858511600490fa40160740c01e140c000c48911001c01058000f0020b03046041464020031071069003c0180103031000c1d5000c03200c603050312204000d550700c18240340340c2040d10a10b40c20024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668185467 1250 668184217 668184239
    0x9051c03200a05090a08071e0e040b0c07150c23040308070f020324060a0b030402040f02040b0a0c050f011e0e0a1202010212180d050d0209030d2610 65
    0x402ca0092411a1402e6032050000c2c40100d4560030064854121100c10400c0500d5040407280340710900750164141480d080b001189120001d0028111003078450020745402901d004032165964400a1340d00004c80000150005120808259001c10650036040001da03003210b11041c284e01645d0000c610b49415560b40c940c0a400900d41200d200d803139100b41c03000507039042c0a07600b010810070602d00100100c12091042d05400900140d0040050050a00074030032184120fa500940580d8085400080e03500030348003d110303542c02100e040707001140e01e05c082a40001d8205105009004440e031451040521074200d030102c240342c03c1c115042d918166a200c41c41d820641103131140b141036452619030b0b80c454210b4100000c00010060750300050340e2a000d00142c0ba4207400008941c3c1042003668103038041c51740c2d000509468002e000c00403c1e202222040c1d80c040300d00058001d8180d4440050410700540309904500e4240480130540300d01d0380744400e1641c070300c0c1e108044a0444c08081441c144240c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668186717 1250 668185467 668185477
    0x3011401140d05090604060b0d03090b0a110f071701050f0106120f05010b0d0f0504110103020903070f06030203160201020307090e1f1e080327120109051c0320 70
    0x240c070001030103940c0c040100c91046502c10140c64024045501d0240b0308602102c1080c03200c81c2c4103c07902c50041c0c0100c1d6200b074400d0309031403450b0a681e130745154448082d204a8020120f050040c81a07248524004001040800880f124003008100400d5000b9446d03007078860850b414400c519800c0700401000d0b2190a00300c000c09060400082c0e03110054203038400b0b961090300150b40504000410000b07c422500c1001407002e02c0351030401a50a056482d400c404000c8041e1504058000c14010416601800300100904500c0c3d040300a03580c0c0c0c3e581c081d010307401c102c1303040342d51410203e00242e0032401802140d2245000782e0328038102034200007044585942c05850901100442c03481482e80390380c01d00000c0b0150580e0080c14102600f01196800722200c01d420000f0f29401c01d014415102036440800303174242d11b0014010900e444904042413042102ca20500403941c03d0188180034802e011a000e01840e105003400340d10204490b1050701035400702e1006508150244904220030540e030000b8003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668187967 1250 668186717 668186747
    0xa2c1903090b131d060112020306060d0203011e0e0103050d0c14030c071505091c061e09030201060b030c0a0e01110307030305060a091b050c0a120c0201020d030203011401 75
    0x7481d141c5610911820780c1000d91030001004206000380140403541d2042042600c2c2940b03006032a15145d40020400000c070343c6464600780d00031010a600d0b03134800050311540000600c0071500c0350394915a22244114804002e20011125140410f900b03c400021074141c6e0303081001050701c884503d00c03c035259a000c0105541007a0156000080c2a85c140010005650b80400a10340d00d03091202903004481c40c2d1400c401400401c002c0910241c40d4401c089250b104013100044002c1c1241c200b030310140400c40400b14802403d010211100a890790058110900a03030082004c2d40e240d000c40d070b025100c142c0751100248028080071484501c115021100140107240900300003845c4403401c0d20310b81003010100c0200b900e0b0b8040120030709003207080ca0300400305204288004100e00d030070203102c40c4608a01038100a400186180110401c00c52410060340c0202a01c00300c05400500604980007035004034014000c003c005082d440c03003170090b0b90503910341103009941801101d005681e24004550381d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668189217 1250 668187967 668187977
    0x15051e010e18091b0a18060914090706030513060e0a210e04060614131a030711060403081f08011b09060201021e030c0c060a2c1903 58
    0xa580756101c5891419000e00070440e007903034900308015014100001c0c081c484440f80309071203100005541c2c000714803080350760409604441d9192540100041d003541e41190425904084117081e4071007022012510132500b600c00d5a503082d8944008909a60059400207a0f2090381e18002c0c01040385603004803940c4640804440d00130015aa4400409941c0d0080941075140c002040c0960340e0401c1c0c0071099942d00f00d80401c2428185100640054940302c428428028007044414010400c00003e202801020600c240041c84000410100d50b108440c1500040c0c0701303d10942c00c1e601c000802502440d810b40300d00b1026034550b0005c1383d08407080c5020003011704000c40d0010b0031160a00c07a10301d055050034441221001e03520400350065005a018904581c4100034500180fa0b071079001d009200862418160703203403038111149200d8040c1d0310003e2280e02074282484801c0140b0345c0a07006800c40100d04402c80c0c0240490313000c0352009850540d905801000e940101070b0700021104225a01c83d00344 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668190467 1250 668189217 668189237
    0xe041e020a091b0806030a0611041a0a030612020906100909021201060206010807030b0f06210106080c15040918080a08060102120301150810120303050a15051e01 71
    0x60110601079015500c0683d8a4682500382080e8030401165902141802c0f0114240100402e40d28182c503c809003045641d1205004525010000c0364018610780c04200d0340e101032003400310465888600c00d800420300d030140c006100c040d0510305043c100d400034019000c070303580d02c2e0034810280b40019402c1e0401c4170000020036406c010317101034040d9264000c4203600d60b40c107040c000f070302c0c02c001038110b01426800102e08100080c280a01180d0280e02000071502036101d040106507203c40700028000380f40c164a52224020005521200443c1c001030212480880118280000c1d0701800c0e8450f00400c1040009101c101c00f96000280403050740e102c0704103034000341d441d0750340c840d0815034004001132045801d01c20349680c100101c1d990400f103040c0b40c51455141c0f00200c4c01407100152010240004200080c42d1401900c009100810707404104516034101403600400614080310f84020180c6006540368010490802c000b069502c041c0207100e46c3c8024180e0075011608440400e0704010784204 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668191717 1250 668190467 668190469
    0xd02010f0302130b070605090c130f1103040b0421020c3a060b01050a0e0f0111011508120702010801120609051204080f151306090501181b0e041e02 65
    0x41d403c0100740c1400c04a031500128036021099440183c041c030f80d40d51000460b41c529980303000c00303900017080c5440000340141075004101e01805203000b13007009844022003008207111403d00303500c1c4128443c540f1669201c3c46a40c0120300c078818800e00300b0060b440700d42516003604150300c81c58044006070a200300e20000003080d214580c10b00c58070b01e8110f4201103800f903007001201d004404020000f401c0c41814412001001020f00c1d0078080564800c290580340c03011703540d000d40030a482002c0f8000090000d43d40d2284005040900c5120755240c0c0e206e28410400c80300156002e6451030343e4141c0d078a907003907441d00144c00780c3c0d2404010107079880b83c1d890070610000f03101000b105110401d98079030380b034545240064041c10004250094500c94010740b8200c41040003940000368044001c1030701e69110125414010000d010301400145a507203045850322203e00d024003104005449258120404051807500002141c100d100b20704c0090304034004240082d07035007124102d403c00020520050b03249550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668192967 1250 668191717 668191747
    0xa241205010b15091305060f040c030216030207060e09040206120c0f070302060f010e04050d030f090f1a100e0a11220f0510091206390e0d02010f0302 66
    0x418074001030b000140303e44090801ea028540c07403803005c24007048103141481c042a07095038401d41c014880c07696901480400d900036410f651000348254200304950b0203524001e1350314006409400d01140e6101241e12941c5869080c140c030659018040e075042c011003400c11032400d00050a82c0049580522094401ca240400503000c02400783c0e0041251b400c22a401c500b084106801c20030b500901c1c6070030030020070000901c1e45130940303291500003003080c8061140002020000d20061a1400011840042c05202c0400c407299501d0019005419182d0b0f0300090080e00b850f1182010326824000015622581e40d44201c1701d0b101c0c080400c3e880e01e0140c8058594031100703281010011400d6510078001c40350b0020604020f01002e0383c12500c4490b8030600a85140121b1290f0300020241e100c1c160200111508105076009440e140c2109440e508504060150590300f1240301d5040e00703061140049100300d00304016990007801490011701d030364004440744001c001e0940107140c0c0801505081c01600b03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668194217 1250 668192967 668192989
    0x213110a050307080109050108340b030609070201050403021e150702100e01200306150c0a0b0f0403140d14010611120403030f081005030105010603050a241205010b 72
    0x10365100c503640d24064001800d13066040c2c00c40f402c41440d01c40140842503000030a4200038021031402c0070b41181551003c02105141c59138001001c944150000c1c2c400030400c05540900c4048a590426a4989100701d08032181180e0160041c1c2c007018180c81ca140402c0306007114411448190340b03201000c0a041000c2d40310a079903003001a03000c1c00d14102c0d005158800c401100e480e40f4000e006041030318004400740490488480c294520010100301c6d1a6141d503003602c2c0c400e5110150b40e0f106e00401407071541351107010105076582d000074400140d40818122102d4422a4940c585040d4168042350801e000d410080e4030424456803280016020700080040500815469861594524454100c141440b00407100110b0740c4000b448144006600142d003599800703441c2c071b0220045c1d52450740c600c0b4a100194400e40d0554641400440c0042d49504101e1050841076401e0200480803c41c00c0341140070505000c5207035140c500140714648401c0c1003105250300400020401c00c0303181002591900003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668195467 1250 668194217 668194237
    0x40e07050d15091503020603180304120602070c0902160308041a0907051809030901140d02040618120f030807021011041a0406080604090f051006050909030f07021311 73
    0x9120400c1245018080c40c07240d03140c40320303c80e080329140d031b404500ca9002c041c041c80800c0030a9501001c1c410400c0080c0c800414413903c0f4500d2984480c10f02100039840b03144d064519441c910004a0558450300855070341c011440390305c1c094618a510225007115001d0021920000e664100312604040f5590441c058150308000d00101450402040754906100c0d1800c20541440340800c40202000b20030340f2740400c0e082c2080c0c1c18440c203201d04590303588210220081030610216000c12059406a14680224403500c40071402c541c4598022413a030f00e22080c01026410109104030010b84258242604101e160040707621181c240c0244605407444814042c0d41c2e810046410490b0100140910500b04d8001c00741502d00f50034000c0003800360a0003480d81780540d4840c1e0180041110110700c440d0304541180c140c0e04a8400c201180014040610480c0c1c420705040700821041d5a01004680795003d80290321441c0c03d4030b07603081c041da41e00c01012540c40255110400d80c0c007828480e009050701d0396 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668196717 1250 668195467 668195501
    0x38092104240908010b010203030609060102210a12140a0c0318031d090f07050f0d020a080601090b091e03070503010504051c080402010e0103090c17010e100c05040e07050d 75
    0x1d10345a000b0072010320b69001c049180e0506181d403565036004402c0f40e8020006513031020300303075135170a0050340b8080821140383d011001d0f2945101a002c00710000e013407900400d541d0071103c4403209900200740c8003a4410150107054900100e40130582c541d00c07402c145d071840d00303010a0450484181c9180e9020350300007070780071401081600c8444141e4102c1d003021f4078004c888804403070500225512a40c0002000c40080c040005503104103010108141c03204e010f17606205664407480e06600400c00d040a0f00e0842c00b0462014022507020101c005031544250040d09071302d0007103034044072004101850540c8a0301400382c2c803c089000c0c2c8003800390078400c80c0504010441d01c003804402296a0700105052401c00040105101c010b030b9001c142044020b00034071700410307081e0690410703036601c0c1070310b50081c02070350005c0d1240407030504190001d041c0500c0780c0742960101d45548800500303071002c03801d055000800030007003072003091041c0c90745607001150f500e8a10f04241d0107401035000c4038844da50b04a1291 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668197967 1250 668196717 668196779
    0xf010c090e183d090c06050703030b06071a070206010614090a1701141503060106030f0b18010915050f100c0c090623010804080c0a38092104 62
    0x19003014080401696032000c104130080150f01c545038640c1041c002ca40c200900003913441c042c1842504682c06031031005100a5441406281c01c00c0302518010525030410004400a4092400422041c1c121203440e2100301c0304a10b003400803105903000e01c64041d4400c0c202480800d0f510114000049880f0a080c00000c62f82104483c408100c040200282624003030801c3c64902a200443c41504451440c2404500c0400c0b84911002400c807081405030004110802d0720360240704075141504070b8400308401c00030301c18640c10325190482c0502490350884078507200306600e81410340341d00c00030000600c0d0030035200c03215586400d1803035025030150302030b181c403001e06010380070f20400508803030003211641585032900700300040e146040041c8081d201100105402d00703440c0302480640d01d1994080381004001041c8012254004046810410ac1901140c09101c03081420011103020744c020000901e42102c008000034200c4501e00c0c0054040c0c8801e0100003035240d580714a030480c00d4035000e0783d8400f01c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668199217 1250 668197967 668198053
    0x6080d0206010503030f09010c020409060f060302100203040f030228060f0e10020d0c0501020f041e06080907090e0114070507120801050f150c0303090f010c090e18 72
    0x80072060700581d1098204000038820a0700746004c40e146070000b824040585055400082d0041821000181c180350802c0b02030111450700d0350010042d24400c5403079600007180e140c400c1b0780d240540d001d03075440421401e809101602d001ca01d0810051119030b240c0d09091249680a6040040d640c04100030445941c00220107640120b4005498582600c41c04042c840598000790f882d0b907107001d6941032280701c0c07042d2000e06c5020340403608480720606602c0d69860361ba03110300302c0742d014071507182c680004600c001042c07480c403c4910700d0203440d02400030709050341001c159000030030740001d0340640d075943c800d40c003001d801c14008414454246911901d071280d800d41480f80ca0308880c42150400c00202900600591341c0b002d00d1440d9400c0c066072030030340c00e100386625031400384100c0100c0609484048108800000c00144590317101120000038012070522400984a401041c080d908010a20000243c0030040035080000080740f56802c603501051068407455403c010b0200071a00000300c0b0b4600041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668200467 1250 668199217 668199223
    0x100e150406030c14040911040207140313060914100f02070503010504080a03050a05091b24040315050405060f070c020a0b1e0708070b06031204080307030e01030c0207050f031006080d02 81
    0x44c2c0c800c1c0c40074030081e9416030384e06004400c0b07041c816205590110701082448001c0b84103a880103103040403a99140e0205103001032140d064403400c4000740102202142d540b81d1103950000c280c2e405070200741c2444e1003030800d1759a03080a0701c0715000c43c41000707800601c0d45e409000781809107004002c142d0380ca8444e02001030946100818490b40c09007080e060001c40500028500d90180e164a52081c0140c100f0001401c104040701601c40c029094880541240405100400c222031040d0010410001000c103401c0c15254102c0b03000d861904031000140a0881503095a0390240542c036103901c00340043e60000700c0301c0400d0341202c1003900c00810221040c05805201c00b01681400980d107042806680e91000144180d0200401d000c1c80d82000c031b01036032000c110545c0181505039002c0c0e141d5490752a459502c0d0031281c0140c000500b81030424042d9402803040040c45140c9601600d9603d0904080c8210244c00391780f90390305445202c003880501d10301440b40c44043d001c00c0d000340c00060810580249 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668201717 1250 668200467 668200499
    0xc15190908091804020d2a0e060f0a12022b050d02010b01020712020d050708070602010b130501060804020f1302070b0417130303080613020a0503100e100e150406030c 73
    0xc241c45000203100150780c500160190942c0d103c541c7d60768202c641c080d910000d2101d0031107900d407031004510105860420703495a0344160002d9450084450000c2c0401035506018490310001c103041009003805420181241940403101d1910001c00c103c201ca41d0301d0b40d40003585003d0b6001c0d003011002450190303080c000c06905035024401004030900b0b00c80c142083e0300c05c049000707108014520b00c0c0c2c401c0000a0019100a11001041d601e0380395440d80c0290213808001001c46c0325103a040140ca210351041e110711416030f0115950382010382d59940c2030040a9040100740d5a022002000000c0850310b14001000018072524000031241491302d010111600c034500c501303a002405210040d81203601c082c050046980500e00014144c07204004550085942400c2c0c0384030900000750142e1141e0800300850140001514a80025a480304c40c011107020950b00ea81e081e44050303508000c80b02d5400c8a1b190000c07010460a161527030f16000141c01c54002e60f02c12600b280e5210002c000020044607408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668202967 1250 668201717 668201749
    0x180a051e07051602040f0617010606030618090212030a030603060b0d080703051803070b071104110a03090305130806190c0c0b19060b0c010b060c1519090809 69
    0x5400360a00020241003409038000c40c00e80368060301440e1080d5526900207049180e0f81800412180d501c581c900d0350041c80d8400014282d41c00c2c00000542c4a22030321411007110060200101d2420409440344040c009541c8242d130302849001c98130810050900003451903822640300051828910700d001002d40d43e681c54154440c03110740110300d0210714040308484510783e040c5081c60741c40d141c11540c81c0c0d0031800461807941611030340c000801c3c0108603000504041d0b002e5680c16603c0e030403000810047d00e8050019a6110409001c0005514029040341a80342d11904095080508401c02c010001d9015800440503601c1802840802c00d40c100c6010a0601e0814080c0841d40e828400074000340040300000300f203c0d06410010b41d100320070258400a1480d042410b000062355104004200e420210360a42c1ca5481c0011720001c61404408035908101c24070301821148100315013030740d49800002d0030a03000004500603101010501d1040481c1148216001915030001509002c0d03a800c2d009150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668204217 1250 668202967 668203021
    0x50a0806060a120c0b0403050a440c060a060609082418030d0506030d0203090904060209040e161814060907020c0a03030221040e0a050402180a05 64
    0x2019207a291815000705455083c0001503440303c1c6881c01e010501c8140c0e001d82d941c0e10020030084100500401c6551401c0c0c01610a008400c92201005c2051034200100a840305a1500c1202c104114291240449581000014140092a160241042400c41310408034580c0d0307140138000c0a40091740c07440508004030080060748d03000c081400800c54032007e81c1042c8070b002d00014074182904070091344161030060a480e2210407800c081805010142e406510902840e070800340300134400810f581464000030084022a00d0b19240d290003540003a03e15500035454902503512460100080b83c5141b0b110728041211914110161416100c13940509880c0e80c10305040013035080341c0700000d03504003100702d50042030341e101e803042a45491034500c502038100200500000600d5008102c2c0c42e0b03144154068040224880680303105180710310b000300c1014040c98800b1a07140c2da090360002da402480688030242181d00c040d8403032800101110712407000d5896004005d4501107001107202c15990208103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668205467 1250 668204217 668204221
    0x2010b010504140f040612050601050609030c040b0d020904050307050f01020412080309100e0c090c0a02070312050c06040b01080f0a0201090927030e090c1603050309010f0f06050a0806 81
    0x700640b060303100d03a00306080540e007044810383d22100181c00038000103000308040c1d42d541210418103c5034000540340c0d0b0080c40000a907a0070300408581900c0c90080107070200c0524481044000c0149461031a000b2000d00d80d9030005031a80403070103000d01e02460046072908106d181c1a80380c0a42156454138590052108020010b141da060030440740d0310100303c546039518405114504810306190051440c20443e500d003484c1800b01e41ca50540e2030a0b540e6040b181c0e0303802118101403041210200050f400b0f0340d001c0020070703400c06024840b69614a46285028100003206140260a131004c1e12002504001085007040801928103860b40d0354018111020042c3c002801d0130301e0380c0c0303d0803100d25283c40c1000c0070440e01c03440008448170400e60200080c007050074001c0145010a0401e40282c00401c049404a400b400560748440190341e24100c4d001ca56a404444640000d001c110440d0340302c0d0030300c494401c0c80b401962040b0410907400180c0038600001c00c1861082d03640408855001034007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668206717 1250 668205467 668205469
    0x91c02150402041a09010f140303040e04260f0307030b09240d1506152a0f0206030a1416020319050705030d050a0b041a011124090d02010b 61
    0x36a031030348550112400510035503038800c001101c036005200c07581d1000e4445c1c00412070a41c003854540030b48801040c42080c088081d403e040da031348900d000300064000d4080000d4001842c1c40010f00030094000d5543d14104503902460b00c150704a0b400701e580d2000d0100030004c409915101c1c600c4200307002c60704400681010844510805601900ca00007103040c07541d004500d0316031002200e42164070158501c541e10000d40184000c00450160300d40c20100c0e81c1d020000c4a1088404445a00114102107104003500b0400e2130b08031000041250303032420950f03e28002d80e0b10400554030800c1d20035004030b030b4169030310401c2d118040e00801801c9811440020003001c2d0703900006844440401c08520340740c2817100f000507100c5000e142e50003072a51100145100d0740d691580c0000d8018030080c40e09100303402c1103800f08030555264030000804002e1a603005550f40d03101c0ca03d01c02d607110300030098924404e6020f070741c0a0f240d00e5945c48410342030981024422420b408000c0011074000901c000c11031740c2590700c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668207967 1250 668206717 668206753
    0x3190614010e030f0d0c12020a12120b0a030b0406060603020c03090d0503090a0803041e0317030a060504050c090114130302061c02270a060806040e0a0803091c02 71
    0x566050400840c120b2141464400304008640104032508072100000c406200030150068000c00310386002d06001c05030101c0380006062610683d04c00d400840d4001c44100172948581c0d80440c0f929210744039220402c42e51030324a00c9001440c01241c03001068500390609005441c41a030103042018170400000911440200903030b81480c0c801c0b40e002c00f1262f103604000d403460140c0c240096021311851400607403041c0c0000100219a03c031000b0000026000801d240898402e00c13003c0c0008400d000310040e07240c0c0e86402950f2081e40107100159081e01c80340403030100c480407a404100f0800014400c036040d030b0403643c02c0c80b4031502d070100d0500d402e001e16076540c1c0b145200e100090040c00041075070301540d4030300010743c10302c560310900c11510b900486070701c40c0c19642191004611310306020303101d28840c1440e600c844151081900da800341615440e05200040000b200300c0c04c0c0ca170103610146000550106c0086005111100040c000b0f1480110705220203104a41c0b84400e5520041e40340d400a101c1c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668209217 1250 668207967 668207999
    0x150a0e0120090411070b070801050312030c0f09040e010f020a030b0a15030209120604050c0906060a081803040324060506070b0708100909030f1805060409020c0a0206070305031906 79
    0xa44010a0660310b0700304819142c010712030010318181090382045140c82e8802108d6048490032011a0443d4141c05030b42da16500c425940127a001400700700b280500c1c4204001031a0400021b040040c059011040c1c50742114407002030340c0c00090700000c01c40701613981070007005142441118a05440781ca0224a0380071000c0d0030030400e0501d0b030081440b0040d035a40304484d100c81070000d403c0d248a440c01e8604581c482590b0701c0021300c00d5142e140403601c40d0400c0400e40c0c41217145903d8500c8151101a29140100c80c2d503045000140700401c03005c000614444d0202912a0395604c2e90104401d071002c1d48425070398141c0000c0d00604091001c2e0001c5408540c00c0b40d00220b50341451041a1900d40e030001e1102255007014268a0a0001910030198840c82008641880d07640e03244c82d260200c81443d0b08504948030750313948220184014014181c2d41d500034049243c1d0762040300ea4114540d070200f46240c121040541c08514003108100710488805a855072801c2042c20412006003440e01d090340016003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668210467 1250 668209217 668209219
    0x712030e0f1504060216080d1406091b0d0e06012102060d09020103021b0307050d020708070e090f060c041a040b040308090d150c110c03031209150a0e012009 69
    0x1100410203001045d8115000d55026100d41802e484d860f0504032500d1b44880f41a54005290014220003d5803545169001d50b0000b40007600359250901c50380041905078641c5000414200081c64584056110303018410315824090400b540c0b52020001e4502d02410102145007996260400160340e4401192804d860481d40002c9040190004078000e0003400c0c0310050000751402c070640c4064000000e0941c1600c41c004032030001500b82c00c1240c651109201d00e6100354400326042c4000340814404562041c0110b085518514923417040500e809011f440039041d161000600307000301f01200d00b8801004c0071030782d241444d00e4508024401503115610000d40320f1000840d0813440c1d03a55104504144c1600001a80d40c890b0310600031200504a014000011516401c003e1501c3c03500071a18603c1410020091410b021403a03a0300301d00381e0402010ba002e507018026251800440c2d18481ca4041c1540d4030000444180c0c1100150854001003c80e040103038150954a00c1088518112061020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668211717 1250 668210467 668210503
    0xa0302150c04050406030b06040f110f0912030d05180a051c02150c0d18020d080a0207030507030c1d060904080912012a050a0c0b060f060712030e0f 65
    0x540c08901d240d0030702a035045568000e0900000201740016548040e003e05400c41e01000414241c2c1c148101704c075110705001c0c510401c20301900c20745001c114054001d4440c0581145c0d54040800107c0d400d5911011082c84142e60351012b000240d038040c4000d1036409d03180e20090c004a021034480f16556030074a04000c3e403088a89200c02c1c0164801d00c000444100040003103003850401007204406500b0071502d1204507841c0c402c8440c240100521035592017600074140741503041054031003c8141c0c3c4440f0701d01080d4826002e0000002e102049644000c60190001803c12401c0c14800741c01c1c881902002041980002d0603c0007503954640740303d0b00300380e028510300d94800e40c02011900240804505600315444c0c803d00520350301c0c0c0d00000300340d00483c05c2d024412000c0c8405094840340980c69503000098048620400040e82006403281c0100e0020002b800c07401070720307001a405500811041311513001001d5500040394140c09051034120a0001030300c2000540e0140382c0d0784459408140205003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668212967 1250 668211717 668211721
    0x110304030b04020d021210050a15050607020a0b0f04140402070201211e020910080f010e22031106150127080a1a060307060503041101200c0906030a030215 68
    0x5652113000a9456601511003c0c0040060302c54036203801d0340050800f85942084001b4a0320b110340d2140c0e11180781d0162480e02c206040009022040d0001c040c100d0700f041c80410f0124650b95828040c0a024403d50ba200d540c9030f0031b241d001407e003001c0c491a280201d0040c4003100040c0e8200c0c99251758556001030141d10a6168580708002c0c001424403080d8041c1040b5142100620341d800803c0c25800c180c1d0080c555041811003102c0c2003000720f80740700006541c078006002c5442010386083e00600a403d864200c0129814160f80e8040b03006000c8020643e9035055500054040c00225809209281c0e0b15030720141d03a00000c0c0800c001c60031001c0140d000d110147c10012622841c41c000360035128112040c58000f803134565501c60341c04201103112039000c03002403d1460300240b030806849182c0d55050460312903949040d083c1d21040449418400301040704505099410555824100340c40d000b40303200e8540c801801424400503001c2402600180b4840c404a50001008850030500c99800c201c25 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668214217 1250 668212967 668212969
    0x402010309120e0321030f070201020f132405160507030c080703020909010b030705010f0e040c120e1504030f0207171b0102030705070302010503060a050a08010c020d110304030b0402 80
    0x10121070100070301c200244040e4090320742d84901400302510003581194a5021401c010700e00d01001d0388402c240c400300400000313005004103402240c000009000150400d03550348590f1680d90404d41100011090b00b207010090a001484040c10381c14082450300742e10700030050000d00c1d80c07003864002d04003510340c100707160100078040012400660704030841c490440c0d110701f405030f21101284401d0780701c0d1064901040c40c240062068600d4600e00030000c2c40d406192100541c0c0610341c4004500901410049a4071030b612113000d14505011680e1b139081000d4654035540b0101c5400004031403869100e20134400000450704100f0b50456018103002025a803201822441c099113078100600101e51640203109144000481050010b0400001e5a01904071001244c0c2d80c0103510300078110f913010350401c1002d94007503002190810005403210380134030740300d03400300c0c644c3ea525511040450395a0a039400c2030703690611801401102c43e02d410001d03d995900300c180d403030280c0d01000d010074128601040031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668215467 1250 668214217 668214221
    0x140c0c01180f03060c080603030406020d2609010905070b120c09210a05071703120405010222031b0f09050c16030509090f0105030d181d09071a030f04020103 69
    0x24140b503000c0081403034480c80c00b0405400001a400045200f10b0b020a81c01d1a004c41514140ca299500910184078407907002c551010f161769461440705145c848204c4454544800540321722030b490f0020400307602d42c0c5080e91501d005984140c44110381841515801140245442e41003c18840e1840d1542041800900c0f41e0100c504203080c00324a001e08901504001b140141d021070080c1c041d2484c161303035103071500060024858000c6454000b00201009204d940c844580c2190003a8001410404000c140e40c281643d2143c400d82109014007040003003042c00909007030a420100f0070114824601000000243e00303501030b0009090711140007411550f1a481035801d000e51070004245011391500f8091310b06c1d449104158012215840020700d90214191658100c420140c01021500c1e00702d8001c0314120b00c14280d5840a4080b03040000d1203602c55042188441c2b032000405034141000038a6502d441019880440b0045185d0000c4941101d1001503070390040b0783e4011032415507910710040300 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668216717 1250 668215467 668215469
    0x705060d021308100b090c030f070c140c15120106110f01050a0506120c060d0c02070506070602040602060112022d04090501020c070504090b13150f0507140c0c0118 72
    0x141d02e4074800006144000041c081a502c001d024041200500c4101801a02e040132120407024120030000710300320031860202e075a80100140303040d403000d034a2030340d4000078008030f1411040c40da4040b00d1000003e14090381c0c8a5004811804094070303010001c0e550a608000511a0744c0510403223100900c10003030700b488403100302c0045100070449850100e00a40040109590442c0516044210060b0400e0300054092181d20300400840c10508003018190190058400c50b004500455000050703030b444000107803028a06c101405a01e450420400030728001050380a1005000d4002408016071030758598900005503588030f008081c0305104078590307a001d420450a410500d001c40341e105002d03041d400f4240141091041da034203195500100010b80d401034002030100401c04003c034580b21071030000220740d144a02d09421014018003840c0040b1542400c0c840c021948500400c001c4a5211942031440240d01054500700f85006626503521255184514140300e004101801a01e01841c503400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668217967 1250 668216717 668216737
    0x50a030e01140c0a12030e071e08030315182e0e07090303031109060904020d0e03070609030f09060206270111180a0803121902030703050708010e090705060d02 70
    0x6691440b8483d001540c84102d504140e54006090380d0b03a880082c03090052a609200300802048102c2c1014083c03c80207145100c1c0300c1448485c8040000e01400501c05180300b404004500c02106c840002400201c925150076268038031540e00400c0180e20000310350368541071503408803400c0444014040303100c012168004030fa90b40c106c1810006a540d000d0b1690054911039541030102c00c03c84122083e0034021284015407000c01840b60780880d0030700380d000d007a101035603280100c1c0c4083d2b00c16946085a20888059a0b680d84840001043c1900f00c85241400c00245c60540c100c6881c0517002501c07800050440c0301e80500c0001d48000a5045403c0da06000a035280204649020407103550b119a02c407108012100d01e946110075900d180407a268021101458042c5103844c0a9445880c442e01c001407441c0380460601c2030380c00230310101388060340c07040c000c42d08c00003964106044080c020ba06d059000d0a0300b04082d2080100c041c1e00410700f8000c4800a0724044c0c0c1710a01010608040d0180800071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668219217 1250 668217967 668218007
    0x405012106090e100f150314031e1b0604030e0402090a0302150a18030206040e0c0708030a05060f030d05340b0f10050f13140c041d0103050a030e01 65
    0x1604496408036045030b024904c00750402c00340c48000408400e68016508503142c034500208100041140e0160400350082034001340c910704034040c218441e59640c0c280004980c00c0380400c8410301c0d500c0040e0008074a00840004007160700d07081e41e00800311a046001a4000c0d0b03004110007015440301081c090107964020020b207c0060000c1111445400038482000000d00c4500005c0408506200d40819690050300c4a03140908022a181c1e10400c06000e40d00b020a040009101042589000d5400350a01043c08149401e018081000190401094034882d40014400b00c0e02c5130380010440742d00d10b01c418081d00204641135500e00e1480c80c0e480c00d40c070008004c4464102000b100c020b805100e550707170350001c1241d1b03100d086240744100741e180039568100640415031840c5d464a2850b20016807203804000ca21102400b142c40f0400b242600d041c9245079001c00c0c01d001c802014a03800c2c2c02c2d045c207483c07020855890346c0c407038503038034016503038003178107010052081d818264801c1100a003500c81024203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668220467 1250 668219217 668219231
    0x10030302150f0a1a040f0c020c0405040b01060f02070906090605013b0f031e15091f061806060e010e0a050d0305130e07090e01030b071103220306060506040501210609 73
    0x100384082d0041f80031401c014051b0b418655038501e0507200341d602641d00031240c035500da8200a02681d9202001094900794480d080002850351711601400c0050b012882011942500d00310026015085a0032503900c05100743c8000e1010041c100500d10720075001d403070742d0503c051501d008520324603000800c0c140c250081410058401d4180410711203805400c2044500300030050310810710048003910030f504250801c0200302d01c0c901c500404c815020440e0030001800d507503a000c50440b9000340031020300c0b00c103840c1e0008100140c1c2007400d0b82c0000d042820040d0078003860f90009134400e1401c0c0251880b0300c440c10b20744001e040c8914140c400308127a48900001701078071602c04107003d141c1154030000180c0f98420104000840c0000c030381c120781e40180e45003440c0e103803c401030307800303104c903180c03040c40c1c1d03c424811290b4100c1e9038804e40441e0a800620002000d0039410107509846098200c1400352208200420041e40d215401c03e2500f0070000400001d142560000d1b001f90070640c0c4498400307400d00d45 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668221717 1250 668220467 668220491
    0x190504090b090708010b06071401270501050903030c12040623010305190803061e03060115020f0d05030c1608070c061209110d050304030b10030302150f0a1a04 70
    0x4020b00501800040361102c560b55181ca5003642c2079042a5078000c2c01c10300c0b01400191002c125a0200349850300082007021071002c03002c40850f042100c0040f4000c100b1164010b0010030711401e038120307080b680594139614040e9000300031071240d5245400030600d03100c0060701317000680d404240e10240706100070302d0580700c01200c1160b0403c20302090f2040e0040c06100c580750589501c40850080d4001c03491411607941c50304004695044c5210300f5521003881035056001c1e503042c81268041d1002c09081d40400ca2200c0340240303008003d4810784555841308604409041c0c2180540340d00450324072000b541c0b5261124032100c54030007180c0046c22284042003110420280c40c210710240e0318240d0324101a5039010300c0c0c450581d85c11500c060003c8801e617800003941c0c2829600ea4011300d0140080b05e18003550707655000e8815000300c1c0c200081c01030841c020b204044e414406003100005081c850500740c20034851207500700310054000440c16a903941e524603e4810304489061009005204004201640d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668222967 1250 668221717 668221733
    0x60a02011401090204061d060715060816080604061d0708012712080c1b0703030f1d040507090b120103020a1d0606030406150b0903060a020f03040219050409 69
    0x84000602107559400102c1c580042e8403e80701206d940340d5502c07101072455030400c420401028616504100d00f04500d20204101c4803010f18034890004000540710b00d0040d60502f004240044060407401404c020400084009003150f0411b4200d41e000805840000561545a00291412409003c1c242001900e21030644c403032000d101650300c054610303007001000e8000b00d407045400185486100308141001c680b240200652004104504070b00e000c0700103201444207094005d0280b001c0d400404107208042e070100b00c08440a540781081c20300d4910280503001501c0200d1344860186988400050032070b4817410f422401480c0d500c00301565918480751039800194240010781c0103000c0e18500003012840030007801c408542c11000940340f9241d040c10404140d0000d481500d2190f02d0309150300b1070341d045403841c01c010f200d0b0180003555a04404145402c09000800c409000e610601032500c1e1000e07004202e0b54801e1341103408154680ea41d107000c0c0304c0c2d180140c020340c2c2c0242c5451a0113080001c18 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668224217 1250 668222967 668222981
    0xc0c0a180c0921021c0b01050406080105220203030d020415141c020729190c080112060e030301140f0604081e0102121303030c0804120f0509060a0201 66
    0x380c188103807903603035030190361060061143e481002c1e800e00c2c2c4403014002d03211043e941a0f10040c203060b0b00d46600051940c00e4002c0c2a400d440c0d00d422140100580e1400d4403510005040e540000d00c080c0c03400c18070780d0148042c1c0c441c0d0084c038102d40018280c03c55400344119512440c507250215201c44d02c811000c0c1c60441c495851002017250380d940819030000796030a4621045200e010310203c000054054006074003c180110385032404540001890f00d002c2240b459020071103408e80511703150030a0800310400707107174400614451411401e82c8010f507200b43c4031415a00b032981c29007260341c1c0c10b10340303000102400b520b200b11500000c0004102005000c41e00d900451003240d900690380c1503082040350382d208030f00c40e480303031640540b81e0104094440201d24046420440006041c0728a0800d044001c44080764042c081946003000300040680521401269000c10320340f41c45c0c98641030340c81421000c80c10b1011400d020500ca1103d002e284140200d50007244040d00740c0762640031012003e4043c042c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668225467 1250 668224217 668224259
    0x1f051302190e040b0d05060109020a03090206070831060e131a030c0102030c030426120306040614311803030c11100f022b0b03070513020c0c0a 63
    0xb807406546261405e1010900101d4100c406424103910b070081e80002503200e5004501810f848102950160303a8640141951a0241192a41c0d4040ea2145468207010a51144115030340d046010700c040340003140520b0564110f424102c005d00189400a40c030610b03032610030104076007400012100302c15244900f00c0c00c10000d03001c59107002c180c2001a40c0380d006150444030304c1c1e8014842000200b6070041c3e90114409203080e6100c1149d44900704500b0900088469101450300006000840c20248140401811420004000c0c014850700050010080501c0e608a4101d81d4004080704c001c4100c15100c2c441c1d907503c08105c00854032040406041c00c0f01002d4012070b00c0c14401d80345460090750341e072070a5000000175008012150030010010300e00c1d400e1190300c0641c240280044101043d04500040080c15040c0d5003882c00d480c80301098030300c0082c5c1e00380680c101c840104000c1d180d100100e050b41080410158030307042e80e020018035054001d10340c00d034003107100380d000100344d81c03400005486650 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668226717 1250 668225467 668225471
    0x60b0909070e2d070c050d050301060e0d0201050d1a030d030e0105070201090f080307021c050c010b041a01110109080406080712090c0e07030609051503061f051302190e04 75
    0xb460b104010150f88010f1683c004444141100c20350780c50035800d11075440322080c2041100e160407030300c840b03161282010f4103802048000005000198201d561b040d40c0c400100c48100082800ea40000d04134001d02558900e42911282c411003400f400381c0700078000b013101800301d4544002c0100c004001e0040034a11aa45501e0400841c200034410f00610000517040762580c1207401082d40c1d407491070381c401820349003103008051882d0252180040303d458a010b55699440e104c2d2003440c1d405085411002c80d4030300c6280340040c80b120b5030000030b42801c19080309082c29065404180070341809401000700080c03803100c0019000c1200b90700200b1050064016554645803000007046010844c3e01c0755001910011103c20104100c8001ca0210b82c1c0c402001e250205429554040c0141980d03820380d605945c0d101015602c00490a00b0481103500031201080c05154640742c0701d040d9110030850003914007070184005e20301c00a00302074044414248004845410415000c00010070590800f100d0070300c1a8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668227967 1250 668226717 668226721
    0xc0102040f05060909130305090418030e10080a0b010c05010c050301061b0f060b0303070b10051311160503211504200306010c05030d0c02070f061407060b0909070e 72
    0x410400c0a6071041800038144543c2c640b214460b07201b038400403500440400500b042400c07255101d070702030302002d002d090410700c1c03c03002c41d403802400741c80c1c00110060140d542140c8041013981d00c21203203a00f1007048100041c03800084001226419441d60020749150700b04841036100c5540000114100c0b115070b510810b0304d059001c1f01c040c6802c2070000240c10800c0300f01400b00400c1d01a0701038081d042c0d008007281d00d8522545c1e40c41d00c0c0100101c941100d081c040c004100000d003400718040c1d4400030039290421644e826188560314501906854032503081c0c102452408101c402c10890b50b5204600914407802a1103880b80d80d50148202c407074040404400c2d0180050342000d0103284000305040320407019400840144030b14682000742042d0401c80303032046150100e40c0038001048060040c40000c982d14040311400b0b450301400c0e5003e8803901c441d4003004c000703140d0302840c2000500711075504155104d03c203003890b4000d400761000099018840405020300da201c0010030340200e03035030008044026 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668229217 1250 668227967 668227969
    0x506010e011e06080a060513051504022b110c01020301060f080609070e030115030f020a141f030219050a0f020303060f061b032101140d0818060c0102040f05 69
    0x10b201d1426015a8200918414441c4a01502c451a8041c0e444100082c02030b580344002105813503244200461036a0360000c3c00350010014406a40c4082c05a4056180c0034010711503c141c0c0c804090256160280d05100d4401181d1a4000341802600c2d2501d0316200c22440210a000354000e118201c0882c000e4801b240856010b181010701c1002c00801403036269a07421801d1f2096038001884681c155031320407803c1002c1c1624400c01d03029600412508440300001c0c414001100c2454100e0310320454520108962980d948030414140d480d0f510804d40c500301c03004800c0e0060301071b00049e0702c41d1800c6200002005075010b00a081c0c8090150398401e00c20740d1641d000e0740c407031000b0380e007140c5c120345000c00c201c1050a000d0b0082c18407445001800905100e0f51070b1440c19a046181810104401005003100b001d1408110a000d07181c9100d11011303604480e000a4502d079144400104003403004225485a01800d100340064524050081940e54034407041c030500030b501ca401103000810b5061000320306 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668230467 1250 668229217 668229239
    0x60403080117070605090d06060b03070201140117060106122a0825051806070308270d08041b080f100b03030a030e1f050402150a0e0f0105040305010203040506010e01 73
    0x100c9041d42c44d82450910381ea000d104180b000e1860a880d016181c110001d001c6090ac0000d62040e14a40d00018241c40780e040c1000181106a01c440d549250500122103240c4010962904503a50f0f030030804041e503c0c00b108000682404501003642080d501208074080001e0303211a0400b00305551840e40c01e03030300c150304c82d04a980c4803820380141c4507501c0711000e040c82c092070080080480001075403580200e240b00140407517201f0042100010001d01c00c2c803041c554246598205040d11510040d41f01d8003006002e42c4d1400b460340180108940f01d8081000d0000d00a4a04007841c0103040424100f078a54110940e9420a600b912a540c13040300148030340c000a070310801d02402e0700100510b103815000d10b8101d004e001c02003a10001402880b445003840c07400402d01032601c0d481c50388046013900d00b5004110f034402540340b80356080c0d48108019256158000101070381340c0c50031119540f1001021004880c0750080381c000a01540c400030920080c00800030f0501e0481d100600a802507a0300e0340b4038540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668231717 1250 668230467 668230469
    0x406120c020a1106160606141008090a020609040b03011d1e0303180705090a0f0c0504050616081909050306010501090608042d0f03030c08150f0f0306040308011707 72
    0x20414280208524600d1310400524000700c8030781c60582142420b8903400104c0d4842d50101440000d05000000b5034101142151032042c0c103420f1050380e40c9800080340341c55a00f4030320002d12072440020005129942c81d4820428001b02030020090440a0000349a8100440250851505c15082c6105101e4048090001e03020742030030142d4259150000c010708070118100382040310f405222400328164581c07030511482030010201c04200103400c05010b00881c0c0e2200f801c00c0810004200c14400d0303403142003c07540c54042d0522006124405824034200c103009910b000708808403c8082c800440da40554000140c03503044003034585507643d85005640d100520b00c03c5c5c001040c00706000a01058901c0d1102c0d060410700c010360142060702955801a00c0000c44003244d001510003041e00a041c1e1521441c04004070740c2c10403101504148602c040c0d6030381581080740c89020ba14401c280d5a0701d5200680024103000b43c2281c3c05400c140ca0080c110368000d006240300d0714002800c40c03608403000107200d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668232967 1250 668231717 668231723
    0x809131104061206090504080a08011a040b0d060806011211040203091225060f0c090f050d0c03020409060c120b01080f06120607030b0307050f15070312020406120c020a 74
    0xa282a240000588980074007114603d41580e07103030310014264541e8020548514807a02074503507240340b0311a0282007000c2c1a000590300300320050071100380100c200c0c00ca509640d203c10003035403114141b04240020f0103450f0442c1506010f510000a2490155401031000c00c0c070070302d01712109141407000e00040b03000480d085045035101000000c3e040103000024840f140200c100b46141074000030701a8610040c405044400c5662669000085400da10a03200b100c200352401a40c554544018610400b855000e054442c1d9140300b0300d40c0401c0308820504000b5940608140202c51280c2041c20042106260040201d25110b118100f8000c039485540d46041050712508806d44842d400328400c030300300070459908448005050f40159004200c0709202c0d590b40c0e0750101c3c001e031030007043c1030a050030384e40214000d1301d4a8260f0001603441d50300c4540074070042000300b0740b120094203045500c503d0400011141c13a100050200c0c06a0384000c0800003414003200601488106000c200d96074080401d0207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668234217 1250 668232967 668233001
    0xa0b040305070510050c0901080106031a0111011e0902100206130b041112010e012007150b060c0a051e0c0409150e0f0f03040305030313060f0603080913 67
    0xa000074040d03005001d803980160202e030300000c011040401100c1066401801c4090089110081e030f607840503401c0e0140400c0d103014002d52250008808000882006e0340d030510640010302561040254000801d1201000056010104c8078403207000901880c04203900900e11079200c5080d00d40001182400303000d0915007000000600c1c0c8810b1050603000c1e0003258080c0c1318040400702907543d4150542440288400026031444c0b2a0300701e42120350846100300c00410004045c0c021041c12800c3d11120b5810078074080d514000090800c0c010285c680030154400d101048014549400098003d059441101110310180c2c0342c02c1c12900388400d9100e8455141e01c801c809403000d040c1a0040c00741179109a4400842241940101c001c1ea00140941e01459200300d040c0403100703008001860460714100007540c40c003411500e07016128440206070304607c0710140c2002c01003007086e41c070803a8044002b40080103a2900e91070901d4403680106100c81c818400601da1002e04080d602c2003614140c0c8041c09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668235467 1250 668234217 668234221
    0x9221a28060c1a04080d0b0109081002071415100e06061b070314010e100b010203091c060f0209011206050a050d0602070203010203010b0405010f090e040b1314070807080a0b 76
    0x40b24100da100c80100c41a100b02440b241c80b035000a903100e809184aa800a80c40d00181c407902004c41c2c06026019040242c1d47e107040100180106803000c2a114014016903078480c0c0e0305050b0014032410030f071005148541e04028100d5108412400d010b202c8040d00c0c0c2015035075500d41c10702e4407042a60102d80c040d00820141d81303081e5440c0030300d0b0300001095003910601c0d940e0fa1508001290390f0132409115075143c01d01503076a40403d12003400342410440c4100125155940001c2d03580c0500c1da180340c065888007001c42c1280d103120032180049540560184120a01540903402a4014495043c049070200078201d0840100b1300440c0181c88014225030b03000c030b250204214100001c0c030000c1c0c0d50994200503030700140c4c03400e0005502904014280ba40d6542c5860001003580c40038502c107004001407040184003000800040640007500710040d052203884124403506011a907030001000920040d024080f07410300840c981c0211200c400541308910b91740c610460301d8004600c402400c080c40900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668236717 1250 668235467 668235479
    0x50109150507020c090919030e01030b0429010c0f05010209010e09060904120e1504051005070f030c08160b07020708030408070b2a0102131a09221a28 66
    0x80342d181c0c86203221084492203020740301c800d0890a00c007c1c05a0020f0b10103803110609580600031070019144c140d8003004000c4e0200000030001b100442451000141c030340400350039a10a610741d2021030b800c001c000080f07080c1454410300030b41c41103040303d0104110700d10344030092030118282841400040e1105c40696100c0d662402100c900c0e40710071092004d03060301186c16480d43c540700209400440c1134150b0300d5080c0010400b040102643c1e4208009040064000244400c060b200c00d880d45400c014400042d20f103805041c900a058600328240c450061030001e009414001da4098102d40c2c09880b41961a900800d440388564001c1541c551300425080040d01c4c40340009011201041c1e4580c0c550304003048000c050071071080b041650a0b0b40101d580c549207980100c0c0306000b40922031f8040c3c0c0311081100064024040c540360b0034452004000454045501142104036654038924204040c50a2440c000b000003070140e40d450081031a0200000e00691440129406140108269a40503c0c1c12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668237967 1250 668236717 668236729
    0x106030816050d031131030c03050106120f030f030b061204170a0903021513080609010c0518090a0b0402030702030d14130f050f030f0315040501350a050109150507020c 74
    0x1018031541441460161b4007140c028000c00b4001c0d61081c58400c003400c5c550300380365094500310f4004111028010326401c00080c0c2d01004070048036810b003070450301c030b801128040d8001c0610303c8010b42c01c61030006024400000f400a6248900c2c8508a8090400c060b400c440d0100c0c001d4649102c003050b0112014405440c04405140b440c041d95a85035140400401100d59485915405910903900460074052082c074203015100c0c548442c0e20b07020742802803d400e0311074041907149a0302e0150064901048140d000f907008000400340103001990b50307040961f0029031700da116240d0700380360300e150040e0880030010341c4040900403a0320700705041d0221283d40381e22070302d860108000c0b103403071140044c5000d040c5000e2001d059800014001c4546078a003202250302e42803406c8407070511403490140144544882c503104080440e051807000d0030b40c102d03420380310940d43d010301501600034860008000204801500030790307074030313442240c04401040700c01840c001650015070b02000981c00160711341072141082c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668239217 1250 668237967 668238007
    0x11030105040b060c01091b060206191d120405030c01080f0609060d050f070608010503012903030706060f06031407080106080c040542040302120106030816050d0311 72
    0x80c10f16140500c03050f1804c0c216a24601c1c02c031045508981b4000b80040003851080c02002503002034103042c80d0a8044000c41007440102d0003106540c0c0d00994440030b80600c1411700c09940c0c13402c45041c4c20710b295100109030490b1080324031911801c00a544954030519034039020b110303001c0103205503032030380820040c0c0e10344010070031504400b00c8681403011420420004501d86200000f500445041c107100522002058006501030380c14042201c01c0700f03100c002c20305d4118010504014501890500103801e510410902030a50f50603c2d401241d50110b5a503402c2c200c4100d034900b0040111322034071000304484102c0e2068007180310310f0010800b150148180b164850b02c003008640c44e040e151000920366020700500d0004080d410402080048050303210b15400e00c0350030a6034125200116104405842180002400383e0150001c030342e10141c00b508402c000d10360000c045900c541c102c052440c0d00019810301900c040c800c2031f54000069010f485104da0782011500d1052a014800c102c040d0780038a9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668240467 1250 668239217 668239219
    0x90b0306010e0a091b050909130822080105010f080616050d060603090203060f090c010e0a1502240402010c0206070c0302060a2f06010612110f0a1211030105040b 71
    0x9880c0c1503542c5800e01c03c090314807494001150802c10342c0c0d40c45e180e03401410b40002d01c00d082100c810280d0703c038681e40da80601c09c00303400100700900d4031345800140a45041045441d4159861600516088403004150361758000200f000e40c1c1d840c40001c9055080740b280000640202004ca044000910211a45d642040c1841454980040810803c5501607400140025602d045050443c40c0c24018150071460340d00907040303207041605a041e2240300c4031680c0c60501500000d10419a02c0b41d1003050000c2130f1a46012108200404010791038101680ca55825400c1d503c40d09196030021790101c50080b50184e461485003440d540c01c2c030925502458060381d04107891580000144c0d640801404114050380d138815100c0c03108038210015842032a03001002040700c15002d03200403800104281183c4e0780d0300e42401e19440700c400200041900b00b20b03440d01c01c040020038011050000c5c0c01400c018256644004100b0030b144d06060440301301c40200c03a00a102000108541e00e055000080340d010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668241717 1250 668240467 668240477
    0x2a0303051605032107080108331018110d020d090b04060f060e010503150606040801050106020304030c0b0c2a0405040b060a1208071209260601060f090b030601 70
    0x5000c0c0c98107855038200d0809820180d041c0784100d444c40c0d2010716030341d40000490501403919418000d169482d5601128404058190054200103075054680c1074400c00020011200ca039080c8403202c0c60f0b40100500a54916a9031950300c156540d41d40e01c1a00803403002e4100440c28400320240075000395000c0620300c0141911682410085005283d2142c001d501c9810005008045042810181d524540c0300c040b5942809004000a480c04500e02550401c41440c0c0180703039550b100020031034041d94100c0180c0e90329107800401c1058000008000741c0303008601006c0e441c1d6852500b08541d04c910001c14110350040b42d0319802c40b80240980312407030200d0b1080128032181920100d000c6990072942500c0070108102440013505160070b21001a160841d20001d08010342d440d00c90b06c5101d800ca00a0001c2c0d8602c03500c40303c1c10700c201c9820001d4103e0308503500d8410444080b10100c1c052092400c00c0e00e00800000040081c06500b452400e03007403070f48610401d83d18069085410303400c000c107a141440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668242967 1250 668241717 668241757
    0x7270c020a08031303120c02150603030901020303040b0a090f0602180a080c09180f0a060c020106030b0c0f070212010504060509071401030f02040b0a02071701060b0306040905070e132a030305 84
    0x400314000d40700047d00c01e5000b401d04010642c0808204a03020300300342d019030001c101c03030a030700e0743d0200c01c4030f078440e8010410317110540702c0720030100080c20616400307040f0110100e104000c20407035030000c01702405002c0030180c0c1c8035103041c01c0204100c030034031410486034442000c00f16281010090150310181c284110300324441119969814180070384201001c41e0030080052040003000e20070143e48070b982d440200000c50455542c800c0c1d00802800c140d6010030003182d04108046071404450741142e001c2c22480c3c898081d00d0303060780a0042924103c03142402d02c00000d01e1071600283d400211411516103040e15416103005400821104600030040c1e50200004990960050014090081140c4c0206a11880e04031014012440060081d0386c503410002d0800414010038142c13900058119030029015115281c9949040010b0384654606840441000f042030085007012200d10f00803506035002211600822480141c0c0000803958001241400c3c80442c4c4100f02411403059030392154844c0c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668244217 1250 668242967 668242997
    0x40308071e110712031416210e030f0303010611010204051009030506160206011401031506030b10091a0c070b07051b0f0a06080907270c020a08031303 66
    0x14440e801108012410301d8042e4400320400b00000b00c010228020210b0f1028002d54004102030051220080f01000c0490803a440061071503020003c0c0c1e40c40010707201800c9426140b4440e1244090143d00400e00e000641200c90501141260705c5a212101442c5144e09000007603807091046d205a407a15942400003090a03110000070701c100c40340ca500c482061030314501c0c2551404500070130a680700408074016848154001900d581940c0c6110400203080c9400d8004800814800d420002141405500040c0c003030381607401407100d510b0580704481c0f002c8241106448108103841651907580100e8052115901c0302c20140c45681101410b032480c0d03d40d80c1644441036080804180c4a42c0c106000404c080f10324481041714080c000e9031042c1c3d01245a000068040081d80705610a011507240000c0e850201032003001301414910701120445402d001502c440c41c42d000e801820310515200503181c0e051300001e503c00c4410381c40112185103545400101151000c101d03411024000b04485070500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668245467 1250 668244217 668244257
    0x1060f06052d0f0c0105010e101d062e02160501021b0402070f060c031a0102101a0d060603020405100f1205100509250503070902031b07080301180204050904030807 72
    0x13032001880300101d82541800e003446c030b0071a800362200101d54401c201c01c00c184222000411061001c144002d00c1680d0343d030000c107001480085512088501c3c008242000505411181250a4069080b0344246050b81c1c00c0c598035a174640505409a48001c81c0c10300709116561481d134050034060005410315074950703100150380d0340044c0c048809945401d00704c100304c0c0d4140704107103c122030741031100040306031000040d4171080400c06410400341ca42e80500044104d641051103401c5000d001e0841035141401c0030002041c0c640030880c403c03030602010030141802c10f0708050580d84010600c00700b0700e00d01410a03107102c400040441d0140158615000000500d00c0f03428400ca070b600001d000122050b480784281c1c91031106040c041020340c41c02c1070100d920300040040c15100340920042e40c3c0e44842c0787d662019000c24602050004c000503400c001c007c25000a14120b40300f50444035101c0d12440040300980c0654080d15400245030380010380840e01c00c80038107410464604028650342401200c03d0f00f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668246717 1250 668245467 668245477
    0xd0509030c07080312090102040f140f0a0b0a031407142b06051305250e03072d1503090204090b0a0b0109060203030f04020d080d020c01060f06052d0f 66
    0x83e10780c2000c240e404849080b202640e030b0000c009002117141508200300004d02c2d81240c00b0300641c1101c01d1200b110075458110540000a4008110800e503550310b00c04090306a00c4211510002303410030311420148070503007034000e0281d10240c40b12203c603001050b681d180c5402200c44190903608180002d00c11070705c42c103a00078100010b03900c042580345c2050240039010b55a50158110700349008100500044089901c2d0a11103103c81d00b40c0d9808a940002c03250072485a0006130715000360703900000c4400c000c02c200b0070926113541741c101e03515001c4e18441c810701d440ca20070403420318002c20081c5038481c40b9901419a252000700300140065054513070200002d4200e44075501940e0b240403800540d80c004406100522191000358a1480c10b804110800140904000d01407410715800b6010050700c00140c6412f00e0841c2000c5444054444200d07000c0d007510301c0347c008185070580020440c82d10420403102c490180200e90340156211640481644030500340001c003240302802070700303024141c80300100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668247967 1250 668246717 668246729
    0x305070606060e040b09070905060c0717030c0601060c1511040e090a020301110a090b09180a09060506010c44090907081e06041d060421050d0509030c07 67
    0x603c000140750184411280c407100e803144542c0300c460030401f200c0e0780180c444d01070300e80c02d45505840b04c0d1740101691410342241c1110b00720395540e0401c91011640040a0260001e01504036150360b42d0f20582a00e1901c0921000350100c44c03908101c1880205503040362001e46888000c0d9460b0031307640c0c3c0c07400c0e08503039098460308001e4000c56244810f514090248003000c02600191501c0d0003a400f4002d0101c0486101f591030500002c00c20040311750b56942400b03030103102e0b41460440b9107090b807807640007032103480d0301211940e02d0a00424001c0d40f2800d00307951a9a48078095109603030291041c0c110001640202000c0007450b403a5209040c0d10001450400a014030f181980341c01c044e00070868892801881041040403031401c000351081e80794858095010201c010007181d4803082d012030007030300428107507042040a20b031100c0e1682000041e0b0b030b0311460040c94035169400000c401d501140c000c102c0111b001440038004401745c8407443d4000350f00301031150226881c001207042d15606000d1070f40e0040d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668249217 1250 668247967 668247977
    0x9021c140403090803030903071e08030c041517070c060e0d02070e0c190c0c0e010312170606090f0118151803020a030b190f05060f09040b0c07030507060606 69
    0x8842019080b40d030b043c000c0c005240c00f07181503141071900941d0b24080d03644041c0c11304050b08400d050945a000ca1a88800c0e0441030950b40c03494240050070130350b406071242400742042390545084003482070a6009004195190400c02c83e101e201c000c944140c8648400c1d98019541d890000106500300b0003811054900c0d0040c2141d186803a00b400600c00004000703d0464104200e501100390881ea04a03500d000e103810090042d4042c0c1c00c148542d559103820243e10240045c001000f40421b4001011360042e90b40d032081c80c81000300e4025502c8520694401e074200c80309110b402c07070518020b181003c1e0031b0b0701858240c0e00717643c610582000e14030482c1c1c061001d241e0707500c81030035016610030015140b0701d0700581a40d071042e2840d804540618118400a4012584000400e20308494681140c150140c52072007841144014401c160042c03406459151190b00880030006642c140004e41d41e1145800c0011100540d80301803034200d5962000a08500f000400c21911002921902c585005402e1554031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668250467 1250 668249217 668249221
    0x21050d300b0a05090408090910080706020c090702160b0307020a150203040b01060206090307080a090302060c06060301060906141e060414031603080910020c0604090f051f09021c14 79
    0x6002c062241ca4000c94084d9400604100c0800c103144100c410101c03085d540030a86aa8852000c0c40c43d0350f687d08031039550700448500041e074541c0021840752481084845d0b8505481e5480d00341da8030300c1025400350364803048079000c002440041c00599407200190058480c1c0ba101075888180114941002c104d82d19400f000380b0080c05800f084041c050840d13400280781604001c0c5010b80d17280204100140031070b000241c0c104900d4404c02e207603070003180d01401c0c5a445901251b4110348854086130483c2c001d41c680100000c3c00c2d29280601000c0300d01a42c2e04956141c901c4080c8142c0802000d54659080a030800c81089600c41c480140010a04420107020040d4208109030409000b44107164003045450030500c0882d081c1c002703d600c2c035241103841c07004041c60303e1010381c140041f4400031a0b1252010030002040b9295421100031010341c1c20040001f503030303081011520704070011100400e81e1340d031074400e0102c1d03802c550080004014400800c162550140215000d0720386039146200e03030f4440320301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668251717 1250 668250467 668250469
    0x41d04050606030a03080c032511010e03090f04090203030702060f0705011b080a0504050a051f05090d05040e040629030f0d08071b060c0921050d300b 66
    0xc901500200118003801c1c03402c6491714014017050700541107101030b20000000c20089180700480040070752181440e0303920039500400252084000c104001c59039403d049241c420340d0008004ca075403e09005105521480c00c00c3c0034040200342e205000c0f81c0511040120002680d80e05000d40701c0b034031580561590b41c5000e803030180c2c203440c0d081c2c0349500031410fa10400190a0380104405034402510040042c640d513850070410300e4101d0b519006005400381001d500b114200c1e0080e00c080f8613000b11010b101c140c403001c41003580c0c0c080c02c02584000500c14001804182c0200240c50740140c043e00d0302081c01d450081c00e610303450380130100c1c1007c031104188038a000e508083c801c1c000c0f101da8200213044442052540a4261000141604104224070028440b911000222024143c1e0000010014100740f90301c09044505540508000c03500200000c94009040e164803291940d8010064000d401c0346003815180600100804081415207065100c903603241c036944801007412809012a007149000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668252967 1250 668251717 668251723
    0xf0d0c030e3006060105090d0201030b1009140105090a03060b2403061302030603070513020c0f0c090609100b0702010905330a090b07140d0e0102120c0a0314041d0405 73
    0x20303810b00c2650480d0007004601d0303800c001036031100003056a000c42210340c0c51004030010711550340c106071300180c9043c84660a030343c403141c00010b880f0300b2008619081201001980ea030f0140e00d030002d520100c580001c5c40001c1c0700d03811042c0000303800391030a031300c004e42c42c00c0d42c4030700d0781112820075044400882045414500900000714940300c444045246090541c08a9103844082c01150302590321a61515501e443c03d5049440f40d00116055600c84506404081d072a40c00c0e55001d288104510000721307095240a509140c0203210b00c25021040a282030300b015050382110000340d051117540f07100040c15445800c1c60b81400c282c0600300c1101c20b00502c1c055807001490270010a014242441240b840a4000b2285030603149888012078481d8800d1402c840203814182e940c044038020706a014607025000300c1c01c540035401c00d800b0b480d454860886c2d030100078094040040c04690010890602090245020300c3d141c0000440c00d901d0141c0720318800c50988043e02c2b404080236024010001401014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668254217 1250 668252967 668253049
    0xa0b0105011d0d020a21051c0c0303090809040608010c0906180303050919080a060f05070c111807020f101a06180409030512090f0d0c030e 61
    0x2401c0030405081d0b078440d8490603a000400c4103001d8108600b90805558a40c2405801002d80a00c0020b80443e80b0304540b600d0400118100c42507c2001c00e02c4141200d21080210481c006c0c0c1d07030301000c00c2507a8904a02601000070300765480300081003602895100ea010724006007095100214112601d1440181a03103000ea0150040001010080100c5103a652000b0300316901403601a4a8040500c005802d820041000042d944900c0000144481e0702003250300055019140c1004109411645401070301c004503001c50001b076082010760f0004d80321400d00c1003040f1010380210a0108515017140c99040e040d6030302c2002d40e0140080140684040081054400030f10b601402241403c100c0f00d200a101064014811000070a003182000c0c004440d106030003100030001c0c800803507682000f8055920540d03981a20b42c0d0040c3c0022402c038800034000121003c000300601c2c4004c1d0240c411217284110796012810440c4907042d18400d030782c0b03841c420902205580d400d034400303070a103603109007184503d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668255467 1250 668254217 668254219
    0x30302150108251e1a04030b0604020c03070501090b060f0618040c020f030712080f0907090e07091b08070206090c04090218040c030b060102031c2003090a0b0105 71
    0x1603401840448400700300900705490101448440712514240751162035815040301120356a1003050076080c1074051042070440b24900000054011a0412039003107100f00c1c0809040030f02c001740490200d0609500408040b0b800906032400e0066075038410b03083d5071010b801500e1314022101070010ba1701c0c01d420800900a006c80d009860502c4a900b0750300300c070076038280130f40c8110358844945049600a0000490264130036058a503240340f40e1a08450704082e10403400b0002d002c00c0009404018410801401890b96038000e1045da0301e40f58004e4068040700380328072500c0c0a000800141d920541c01282603180703403080304030201201c0c020024035010300180300030111351220007071010f40d000102e004c8004a4081e0780114901c4060b0000c1440602000d05072260140c140041000f0f0012010500003070700e200e6907900d605622004012a50b83c00341402c2102c122040d03032904129054079034449070300300c40e014942c040b00c04981c1040e408250411140e00755240c120b8a080300c01c01180c0c9050a000d000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668256717 1250 668255467 668255503
    0x1090501090903121d0313090b0d050c0f0604170708011406010c0308070c080a030504030e0301050c040e100f0b0d0608120d09380901270f050a03030204030302 70
    0x440b0303407401054003580741c40c103411541c0d41340840600c010103081041e00032080e0408580c3da0303072090703549007110391010710503a01c0140c603113500e003003a51529501c040d140c00c0e0014010018503801c83d04225030312000400640d4007010802001820010080709800c0222051024210203454200c40600351a5040c410304211240341d81008040d80e0004004021740781c040c07821031010b640b4400c0c01e40b2000d081c8007010301618400301d48240f44641c5908581c0c4114400c3e0b442c1811007011005143c2641c1081d54001c961071824441401155071800310365a0003042c03049950440d5507a0f40c055034500c0210741001d90040000951301d0743c00c560501540b0000c021440c01045101c02d90f1004619a000342d010440c0c207076840d412400306010541003408464150616541c0084000301401065501d4140c0c0007041e0882c10070000303240c00818801d154002800700c0300030700c04001d030042001c840706001c038007124149810184100891810081100a14460340f001a030359821810f010303140c0100000d461210300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668257967 1250 668256717 668256731
    0x1701060623030403050c0102120f1504060f1e1509030b010e130201050f070204050711011413110310060303122f0d0902030616110d14130e0405060109050109 69
    0x1201c6007140c0e4466010702d01180c60344055086240a4854609071641c80c90980082c486090070001d1f403540900c0c483d05c500e55580141f00c00f80409c0e154584117405060524a004101c0d5107800c084000e207201c070041e0040840c0e030711782d118207404c444072410400c001242042c0600030402014031080c007510703040302411903524100040119903d1210380090400c2004145000355100700402d851a80d540103105104915044200400882c811444400c4540c00d00b100c41146822000b180b50203030a885540c0826101d81c1c1d2a0811503006005000750540704c1c951056100b280244644c002462280c0d0728200c44004550076001030f00c68843c10010605100c5400c2d46505101d5003c4810603840c2c000e15a0701d94060910003070050110401c042e405010b9403040014444421606220341c18258a9580c10441c4003200d150303403400319544070008503140341c4210a100a500024014001c02c003c3d01030303811a15001c0d4043c000c0d03030580381118a50f00c01c800600c4501e40901516000d407141d10401c000c66 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668259217 1250 668257967 668258027
    0x7052121030c16150c030b1c17040b0309160f05010806010e040b0a0909020a090c0807030e030d0204030515010b030c070b040c080a12030b03030f0304081317010606 72
    0xe403201500c00305000a00140007070925002080c0b20004a42048851541c0001c80041c070028007456001000041c0ca0104080594980140c0701450309142840541e1040415600c0b407069171104180c1240d007100c00c1c0030000d18035005000031885a040040640540003200c403010340d685646030810811840c040e003040c045a6445040c040d070021007480c20106040c41c810208005043e42840355802c4003083d440401c40c03062030781005500d240700361060410141c5d036505c2e80d0112000c0e60f1425001034038441c04141050f21941042101000010a0f20319205070f03c2c049001701c4e80503a004440380d0308040c1d0440442c261071880385005106c80700d811032441c6016143c00d60b241c406c41c0c10044c0380c1003841010905000d600c1d54808054100303041101d40c2942c2c10300305601c0702002800441c00090512842c851503090100943d0707c0103420716071042c1103460b10740e201c4e40190040b85407800b06000840c80051059190b40c0c003401400b5200000259140c10220024480342a2000f2080b01402400d40003074a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668260467 1250 668259217 668259283
    0x30a0f120603030503130f08040f061103070210050f0c16090c030516051305090c1308030a0206070c0201030b0928050c0403032708010606030e010b03070e0603070521 73
    0x110000315041c15140681520300707c0c00d50041041c000d000e2a40c04680411519440140c500684806417110880c001d00050352650300d115101000b0f410140b404000a2118015006801516552800242442c865581d01403500e4800c0c0c3d6940c803200c071801d00030401d0030702500c2a44082e00340b614003404186401d041045400350180da071441001b800113010a543d0040d1005030000c0c01c40181600c1d40c1c0c1c104240500c005e07802502002c200230711660000104410008100c3c1d20b80d00c2d440d005480c0c0d43d81e550109841c0102a0002a414580c1350b607002c480b20382c0c0384904a44200640714030120940c4445c00c040c107517080c0440105000a00d408184005000302109440c212503051400308000d800c900141c00c410340181001440c03403040960040780c8014107410050564603030b594100500d803104800d81d800c1c1e501e0300304c031650590410b01046c40300306200794009906c24400b038115043e8607600d0012800c0140d06110300d061204100402c3d03940c0e0704c42030140907898021040c5941c240c900191005d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668261717 1250 668260467 668260471
    0x111060402011b0b09060402040e07060e01050f0708030a0e0609011509050408222c040b04030e030d320a050901031e0203070305012304050a0e030a0f120603030503 72
    0x4140311081c403181c0b04000d220343d081c55400341d012030407080b01e04040400c00d50b0f491058070100d01c500d08284103410000c800041a100300c403503e689240120400c3d000641d102c3e840300014440342c200811000c40441c2060703004501a00c10920300040d500c11041c0800e041080107000d4075026414044044c54040a40d10800140e8050316000602515031345009002840346544128041c01c548005801801850410b90104d070505400b41040300c24000302190990300007081004056140340105000c5410000a150700901c87d08011110309a41e01c0042d1410006084900000310081c0c3d540071030039012040034000041101251400a52a0031001c14600502c3e440b0b4042113008aa16a0540c0c4244c0003528540c0c0d05d59440b509030a1034004900295200726500e40109080000016442502030348a11841d81860841001f007000c2e0410071001d80720240015017000d41311005201c071220184000c003807080b405d880e0300e6045021800003a0040c40705018a001503440d2510410100b81c00c4412a5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668262967 1250 668261717 668261719
    0xa150917010209030d0f02060108010b06180a0504110c10020306030c13180c090b0d23120d0c121e0e1f0507020c030a1e030c06050903070b060111060402 67
    0x240180411074024010143c1d5158103204050f8030780b184d41d0f08686201710100c101c0d4281c132540d0780c841005901ba10b003150719464000e6410000b20556140800c40c0818140c802010b240071146d481d000a015600182d851256608000a40002c1da031000c001c0b00c0c00400060000350b0641c81d0020000740c982c0440b8403541e0007030400a802c664110b980354000f03e44995010140c0c85010840c0c2031501a103040da0141e100310618201040b002032820340d490f585000c0c0e120203904555448070308028854170b140206070751103114500305186408080c0000d030440c2280ba10000611851200c002046030b00907040d01071407145029041034424201500100c040180c2c0e58011560301d004407030f410f2414041a1502070549a5900200409146504840e001d501c1550886410145800030103450352060100200b0603402c1000100c6525001841c0d04101c601030308007071508407041d85480c4e080d41d0302211850311b581c00005558003086201103143d07400400a20b06922407460170106665039400241c80a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668264217 1250 668262967 668262989
    0x3180e27060121050d0804060c020610090c0e150d060b0a080402150405040f15330c05031303030201150302090609180f0a0b0106050c03030a0207030318110a1509 71
    0x10f4450790307440c024441c06540c88011628401718005000b40540020385040f1002814221203070301652000a086025076070780c109000500c0d00c3c0207420700041c03202480b5002800340c0410743c2042a600c41c10034180085542200da03a94184281d288000c88080d508003207203001040c081c0340d040550140c241648160b042d02e5003001410103051f40e0007907000700d600c80d40e4440d081c0300440815940581203084580d0f585840032480715111603080e941d4522107190046148581d81e00c2d100300c00c1c511038802c0440340390b60130400004003441c1c40303860843d801048079002500240d01d0030001c043d42403141444d000b041080c44d80c0c0141c15640021140800585264403514042010580000440200744403000c03658045400750006036100c6a140d901e454000c3d280d409200740000b45044c010406c8600060282000d1072860b40d030f000d10344000390443d220581c2015601c00b800d0075030010450030359844d903005160ba0707941080d0707201c00c0002d011110f42040f00307410740c12038040c0500c680050854060740c118843c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668265467 1250 668264217 668264249
    0xa050901020a0b07030e01050601020102180d020f0a060f080c041401030506031204090902031b0607021c1a010503010c1e051b030414130c020606090403180e270601 72
    0x100d1900d410000054450f03040c44090010711030b0194010030144034120000e021581d00d90300160f00705d004e56280301d9180c1500001400c102e2808020504980d07200805250403401404c022401d81103803030f003005021803503840e0403c1817941c000415551040d0a28406031900d81442d02980410405416103410300d82c0724808035109542c203000400d00342592502e00e548460380c07800d50801030904070405034041e000e10b81c030350a400240408005041140a01504c0c9030a600d42d00380900003285440b0028480c90300d0708204000b03110280c1d034101c0c244031081002070a50501d0101400c50b03504100308014444041030012084a58011624014901c2d0900c1138552101c81400040c0303915200010441c3c2c0400540031603a170400c0c9a4451082c2c4060b5400d0408442000183e0b0803100e2282c4184050390240001500500d001010319a00034800e181450b07986071841102894000300c0e81120140c3c5402e80c0403c40d51502c3c000d0007940702040c04450003a80c009004c0c440d529580103002d09904014a206 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668266717 1250 668265467 668265469
    0x1060f12080c0f0d030e0606090f04050a1a0105121c080a111c0b01051c110f270d1a040809100c0c09020f0a08060a050a06020f010c0908030a0509 64
    0x503548140034200c142c07a20704083c2d210694440c50410000804a0b00e40140014500d60025185100e080060f0000210780c407420400390720441c0040080319244174410381000090a5004001d5200300d850034010f1a55042100700b098101032800c0a00d0320b0b920506071090078142440f1503200d000400e003041401621105802c1d0080c1c40e0a8600990000000900e5000306400c0100010050303401c80c810010240c2e080011116032207400c0041c004546a090180003031304840e8014054400d04207030042c42c0a14903608641035030041800300e035042425061010307000000781d02000341c0350021502c02c01c54040039522001034034404181c0c100e801c450f0400040400c84000c0c120b444c100300c000d00c492224031100000602001e0a0002255480c52041000900030800e000b44c414446190002c00e0800c400e1200896005100411546d031001c1d8427100013526844500f42e060240540d0b60140c4203490518085609680421242d881004485482001711500210559014000341e180259403000d40c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668267967 1250 668266717 668266733
    0x30c1710050303040605070c0503122209060b0c0d0206102102041104080708030901084b0603070e0c070c090c03050403020c040519090501020f0309030c0f01060f12 72
    0x303040240c25203c00030340403840541280c01390041d05c0c89072040900107030300d503014161210480ca01e417000000c2c0502101d8818580e25040c00318103200c403003004859580da00800015210158003007400d0322000107d0101200e0309119072651100a8002014a03007404454100c0030700742d82c49840044559070304144540041e16415188181d00113105111504050031b801005034005c1c400c8030bc09208182d0f00190b0102d0102c185d400042051710fa000c1c0c150b0f21600003d21505115681c80ba01e100c584940181202c00e400b42c18061550344400d40d040d9540d9400711130001070014240701d00c82d03800640304008508000e00c1c0d9079440760542440580762685450440c140d4501a08001400c605104000f0384e10303a8103a0140c1d2180d40a82e00b01c444806c0c01800f13000c1200c100b80c54044643c41c13001400c81e42c0051a411404103a4481d1000503c0c004102040c03005c180c00a440c141d4550f0000541c2e42c50401040201031000000302d0000c103c407a02d032125600019180d4840d181e03042560220202c02c0c03003641 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668269217 1250 668267967 668267969
    0xb0d020904020a020706020f070812030c07060e01020306011419032d09021c03080601050c0f1b0901170601030b0402010c060e0601050907180314011e1407030c1710 72
    0x2500c1551103c0c1c4885010791101090700a107030044c0700d0000e851440c2c02d000586d03402150000000340001040b004401501c65000030002a919a010000503001a100307200d1003500500100006844e0b06292000500510303065a2020a40600340207400341c44102c42c4041c60089290b080028003d2040b032100c090715268088180300c0380202141ca02d901220580200440030f208030303a010300c442c154003140b4280704400000540050061000100c055009800400016001e08126440c100d0594126440c3c90301c4142482d4000030900b1045035181402c0902078050040e14074000840d2081c000c00e580c0d81c07001444080d0a108030100403c055900071707484401003e0b0000c8040c440811540da24941d01d8200303120f240d0048650700c001030102c070312401d0340038800005030206001c100e00d1904c2d414000e081c0c2c0c1803880b446541c0c0740d83c214454050f15042e82e941c0c0b0144c1030b000c185aa402803000350852402001038040c9814505180e40c80d130343c04122400c5210709070a50855903101c640044c0004502 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668270467 1250 668269217 668269219
    0x1030b060c070f06030203040807060e1f0f0e071a0a03110c010902090601030c140918070f14030705161109070302180a03050705060d1e0f05060a030206040b0d0209 72
    0xc041c028501c001c106001614000c0a405407016074804003181280f1088802424030b103420b10000002680e1034000005140300a0116069054030f5103c2e207846000c135510381200ba907652030001d02104014002d64001c0800c0f14007514040e882c0002e41088202e161500340e00900c0300140d0034103003a009900803c4000740f064981921440c0080f02c4600920210809078801c3d00b140300003030320075880703809800000745080e51880070041c000b980c0144035400c80121558003003001c503061002c400c0103480c02d41c8620650b40d20311940b0741c404100582010048500c1020381e00080081000040d04002214411a0340c0841c11211500d0703420842c2142c17203401044e0750b0240d041014810f80d030707500d40c01400041682e001e001c5801040c0c9420440e117000507210060403034115010800c4649003800141c000c11052841c04100d0500202c0390101800d10805070007080e5642d21070040340d410051082d00d612040980b5042250fa0440d00020700c07034012480b8030b1b215004001098502502e09030165146400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668271717 1250 668270467 668270479
    0x641070513091d1905030f090d020306041a070305150d0f060e0d1803050601050103050403090306050106020a0b01060806010e060c0312010902090907090e040204092d060c020a02031b01030b 83
    0xd0b1040c01e1030200d034000ba50003444c0310398020780009009021400100c1d40d031060003907181c84022040341320b85d0340201818075070040b50b08240c800962000d00803140310b10b114044802e51607040001d22544d0450180070401014039080c2000a03005840fa01208403e00c11504091603048034079200e01000c41c3c42100800b00b0341400c02d54a844d46c800109405801e8042c1c48a84801c001c4101e245141043d910015011780c2c8903000401065009512140d0064001c4c83c0195215450341c51300011b0702e5082c1e003d400142d01000c41a402c0c0a050002e0a02505051800d00001d04141d40003c0c640c580c00c00000d8801d0000007192440124200101c03909600c003015018042d69451025800070b42100c6849809041034000180740c0d10b200b07641d6501078401d81c00c01540c07152656024040200082042201c2d00440c0002d000c00035803110508003850941001466900c82c414a0034606441851040c441035511800a010060b42d000c1616401c1071400c5000400d02c600800c0100c014100d5400000d800007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668272967 1250 668271717 668271731
    0x60d05010905070512190b0612030c03180901060c022107060507051002070312050402040902060c161509090e01110f04060806030c0108130f064107051309 68
    0x401c58204440702120802c5500824480e00d0b5100c0c050031300c0100201001c04039000000c7d038040c4409801ca24098003a000f000c94003c09103141d0f5002c206004102c0d0f0000c9200c82c5610b4030880981c0c4a001c0079645000c0b0755250080180ca0000d0381000284543c2510791011030000c02d400b140c0f10000c0c041d13022207803540d42d1281c002d0455400044255414015030b8210603c55410b0300880340c01691558580282c80841c020090082c034000d00120390003920781e104000036940b01f0003e400c00c00f07034000203803102010142c2001e002d244a6800441ca00f00c0080100c0541038219a24004075004041d0101e858002440898011702c1042040c10304020080340800d1b9003c1003a0213001a600c09883c1c00350251248810140d5504401c240d080c00107e1600004440e40070b4071151103582d5216001d51607030807503190745000035144d0400080c81d4007800c02c00070742c0000d6810313441c01840e407040b286100384102140c0e00c03043d803040c0300814072000d1200024541079182c0301d00c00010004d060301c09082140d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668274217 1250 668272967 668272973
    0x130603020a020f100614090108060f1503010c0f030f09120e0103090c03050f2817070221122110080d031406010f0c0605091207050604140a0515060d050109 68
    0x28603484c0941b002c0402d9860303130030805080c034000d40350503114070100410841e551100a552000380007011040208020300d0007400c252004d01801c807141030140c441102c140c0c1b021600034103d407112500b031a230041c105440d0402207400c416210058102c14542008e13841c0410300142d0140c900c0d00070041c005000c21000200b4481d01007582c1d0241c400031001d980502c1c4aa0f070010402c200307400e07144140a2250a01400010f1000350680e2188010401e0103090044940010b1641404400c01048581a29141c103c1c0d841c02071260004900c0d040c0755a509203890040c0803c1400c1d1198203403a485154900030403034213082c0c1d00c05036006224030401c542000e200000c0040180110598021040c2c03c0800070030034a6006061041c080030041d034904403001c0060302d036040980303805850300070306005080b041281340310340c200245045030041004141c00d050500e030103520f8602020385010150003030301c0c00701c000450208212030300381d42e026400415270320751500056a0403400b4130000e03c15841c0c45108420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668275467 1250 668274217 668274221
    0x305070918050618090c0d03140c0c0a170613020a0312050a020c010e011205070516030201091103070b03190209040507020c010e01050901050a08090102071a0f06010302130603020a020f10 82
    0x124401c02e503682104c41e038008582144c581d8060703840c0c4082d0340120428003107606100c0c12140c540d501a10740f0100503890707404052800da000c1102441c1f140c00901c40c9401504024030308100409210040e403440d03061810803942c43e64400752500c40e0b042019a074210655407502004005140c0204444211141c00d03003003e80954040c4803000e0141c0034084242115602810034048604010707100c5113919400e400040005000081c1f240c01030002c14014084150003011b51100450306c01d4000280481c1a402c000c4000d4184c1d5039250320a50050310180b00d00c0c1c0100701a650401c1d800c040c6038540e003029102c00b401a008450026070404c1c03400301017118183d40092082c0ca42d00c1e00380ca50700c44980d10103004590500c2460300c4103010032810001e60201521616000f81d11520001c001070401c81c00769180c00c554a4018805050141e0200038881d20500101e600c2d41c01000c02d0804528101c81c00d00300300e41c10f441c03a11400040c150f0106600b8656030091100c149a4604582500e218807000031860b00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668276717 1250 668275467 668275471
    0xc0409021212070c2106020304060f0c0903061a010504051306121a0708090c100c02100302070b091603032f01050a061202212b2706030507091805 64
    0x1851188500001513000717581d40c201200180140012136454400e5107516001e0b500c0980203c44084d0b07500d84000280b0140c1c807460b010414941d488404291460406e03000740c41d9402594103d84445d4880b4010684c0c0250031942154426929007016001100742980108801d600000d2002c40c180c10362010440d090b40199040c850103001c00c046501e528104070f50102044511980d65408000403129038505074928030b80391211450140342c06c0d0320a034082043c84594a000402194010440404003e02110300729404001c0000400b490010f10a502d4600400d500c0701905005480c0c86549428945241d80740386040b00c81008041c1d0120301d480360f030080200711012031b015850700b5008101d50a45680e11000346030000d020000e40310030840c0700850400300e1401e5204d6881a400400e142e0b95598280c102c01d8140c8003d42d02015071400300c043c0041451a40c02c8112240a800d88810f0b8900c0790707040d1040d5a0306290000b9203980301d25040d204101c070794100c8040d00d0440d0020590071400da0300028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668277967 1250 668276717 668276723
    0x1b0813060219090603180312060302040e010f051e06011202040506130305060c07020d02060307020102040e0702101a240c0a0b090705010c12081b03040f170a020c040902121207 77
    0x1603c0380d654180450442c0d0810208000880c2481c0844011074882c00d403040003c0d400700d20026003a030341c0340d0000d01200d04511100b1400c0e510b510700d403080c58800d481415030200620504201c00c2220051400000000a004078144480040032046148041c6c0c152000f40c400513003010341d65100c1c4590403803c0780c0e82e880100d80900c41c2e10001000c010640d01038400302075016003102d030450660380c00c0003d03540001302014119075092200140480b40c0d0501c9501546042d0044c1940c05030f6803008005581040c2c481c0a4079200d02c032000341c4ea07034031044040062108840a890000140208507090f58803030700224030300030301c02c24115400344144124040d00598000040740d11b0f403584c907001555a517618080240142c107080e2007503035034a401100d08980c0104000100ca24030101c00741c44205540040c1e400755081015005030800300402401c3c00311040c168010844e007071007000c440007955108500413050156444030501c904648491100750641800e101c00d94108006090390880f0030340000e0425 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668279217 1250 668277967 668277977
    0x3921140c0720010e0d05030c060c132102060a090312031d070305150a060509010b07290a0c0c0503030411010f030207020102030406051b060c0a0e0102011b0813060219 73
    0x80c00300752156200c1d48030400b041c2c42e4130341400c84d50010001d4589000380c1c01e503480c2c00200f01031240d00e14207028840c403880c1050003194903051307005101c82988041c2d821005800804800c00c15810300c8030b1404c0c151544d412101d0b142d95448040c41100d03104113a41c80101000c050401881c485500340d08408080318030205103222101460000c25611001d80c440980281c10454003401c00044841c40594040b140100200710150f42d5408150304000c26488101d004002180680c100003a800074624000902d0b05000c0005105070a07a8801c50005030032442d0455480c3d0b410401c0e02c1c020a40380c80704640010942e40c40c1c0c03a080c00c21240c920781c6c82c200d01c2d0004002c114010b603054080e02c241d40c1d5031034041c3e00560a10741020070a0b40c0300e9201410086001c002c40789070728259001048100c3c071600c00140c10031b4035041d05c0000949800380a42c800d41c156410064441c2c0303240510004003420724285e1900c2d80030743d101ca90080d8846c001d401d074040d002d24000141c00c155182c0d585031580000c41c25940d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668280467 1250 668279217 668279243
    0x80903010e010b0a0504020c0304080a0305090405060306190519050c25030801031106040503010c1206050a0e16170708040521090d0606093921140c07 66
    0x1e070032159042c2190340d00400c80c400a00003410b00c0d40c0030b41405480380c800ca0380346c10346800c02146098961801140004d40020707007003a543c101801410b400c0101500240100c4c100209030a0984190000105080d503a41000405018a03000210908150305d48100a6420840410300701a40450309142003407a0b200055282000100011200d040c0c0640d2102e0359030b400c5698074020450301d150029803040c424800450103640a11483d01ea1014946810b04101280903c1605441c070b5a4003061054600420402002003440340b00e0390300581031800681c10500e012400d803200a0b03040d92414141030303048100308029422851180c042c0b80640107c0362404012200081a0000c00021400050041c45502d40038104820741c48042481000d0210358079464400c1c1c0d00441e07a40c20f44403150440e009901030083c480c0101042015030ba1200034081700308809001030120032aa512483c400300d0f82d41c0c2307014004001a48913a1100d05900c00141e0a8202035090604c95048050b0641d4901c0c58011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 668281717 1250 668280467 668280491
    0x91e161d09060103050d0f02011508010519050112020f0a0f0806040b0a0b010507030e010207080607050d05090a0203070b130801050711151b091f091d040b1308070f08090301 76
    0x42e074181200c3c0d0041c010014400044c808580040e00640c80c2010b40d034031440244070381c40c0b0540740500a04249400050140b511a000e60b03000d200e1005050611031804006120100d40c004058104c01d0b0140d501202d002508008200e00c0c601d035a0184010a802050110303032010042103071406030740100d0303000d819510340c48404011500c00060700c6002c102c003000b0341d40000380641d05400203444140181ca10351595110b0090608204840110018000245404d808070f41445841d4006e45900000c02800400f0380c080380d035076421405422040e100200d481c00d04c292880020340060400786000788514106840040c01c401155454503120b40594213090b00791040c0040d42074898a503000051400c0003070000c40c42a29400a402190406004081000c0c01c009031900031040100307a41e00c58203541c1c51301185102c3d1b038856500000382540d00001b4040410b100020464100910a082da100142d0500d40405d145c454080018802103600c0100b8062050b080c0143c1342409042c1e0003404141c807010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 668282967 1250 668281717 668281723
    0x8130b070b1521010f0c0302091207030c17030f0f0d050105040b1003180b0103260703020d12060513092604090c0306050a0b030618091e161d09 63
    0x5000940c01a10b240d400b0031405280c88440f032080c010100000407082e06072044141902c81d1141018042500020703d291141031141c10401803c01d100701904825045540304a02c900c01446010981d00c11035035000d01d04031061085940040ca0f250700316548590400e094541600311003010703500c0900e410300004460815005151805100130224000504820b1060340103001300e100d54141714482e5580302d000a144840c03560302850081581408580c1c90f4003082032250000851260321034000d00910700007035000520b0400c25140c0d03061586145240c0c3c41c1d0407000748066070140d9408072800103040c480c0c400c26881700a00501440c51200702481200c1640f400845000e00e82034103040c00c1108100b0000c8690007035100340c2c1d4920b00414903640d520000344500c0c0b1150044601f0391400000d1042c00d20700b101c003400081b40110301258045c544500c1840c1c0750540300f8041c20b00003180302c406444000c3c1c01e114801c0d440c190f0745407407541142c8910b818a41000b00c1031883e0211600340c0007107901c101c800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 668284217 1250 668282967 668283001
    0xe0705010807020d030f061e03150908070611120a0c090f12030509132c01090209070c0c0305010e030406180e070c0c091103062409010c08130b070b 65
    0x80c3c00074441d4490502c811070082103200c402107040d1396981000300b007003c03031403007100d450101e400f10640d882c6085052175041c60110241060b80135144c400c055000030360490581b050380c0d80103400014481038024004d4003d20075098000074181d412403c00c400380081e0b40c040d0264940c25941c3c14105c2c1d441d401c00140840320f501849d441460b86400100011303109030700070b11004802404a00700c0b00c41900d1200c05841907101a150751a200b0a90551842440030702c1d1b0380200c0810740240681703401e607004500d5a4201520000402001c1d545020a224014a4410080d1f40c4034008100e0700d00304d403100b00e8403a00140120300000b0668011000c0d0404901c1081c070540d0b02c480080d0046450740e000030398400c0c0e0f00c24012603d2600800f000120b1805078882c14005918410145680b85440f4040202515403441c0302001c07080e6469034502e1305a001c206680505000382054000c011140c1030594003030140705203c103403600070340c100030900c0c1c4001e07000340242900c21998444242c84920b00a8809000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 668285467 1250 668284217 668284231
    0x2070b01090b121c140c0d02060a02160206090414101d150105092404091b020a02040e0705040e0309040617030d0908161a06040b0904110a15030e07050108 68
    0x4040305018400e8503201840200040c4e83c18602459961640502d034a03402245481c1e45a40200d50701103901901030082030b0b4441001c2c0411460959403a14600c0d490740e1302039002c1c0c007403270303002c200000c1d01d448075440010000c90b058020350385450a1002441400c000d170040303d4909a1403481800c045141c000610700a50090326102001805d0100458260300452030444d80304603048000c54514180c103a42d118005040444159a5801d060350182a1004020780709401d0074640403048443d640403603884a00340c0e044034041102441108801d151880b0f940006600c80e181080380704450f000003009080541c0192024002980d403010a0005800140d81c2c0c0203050700300300440007030001c0030390090706928894a00e440c00c003040129a0020710301130b03410803281200503038050746d29005a00f0060780d101500302c4060101d0144038010807109180504024810660310440700075680d5a0b01c00000503110988a80100c000c851000401810100e40c00769414040d155000c10103511a000705481485 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 668286717 1250 668285467 668285473
    0x30c011106060f061207230910030f0f0212061206251403072f07030209130b0c1b06010e130312020f18030601060c022202070b01090b12 60
    0x246003403d00540c02d070210310b52980901c0412071892443d5540540600818040c0d548440c1101c200c4018000ea034180411079443c8042404055074540c0c4a0710400d44000403442c01042c88050310030150b005c2c008048904990700e0011880800d400603541c2200c0c40b440c0d007101c201c3d03916900b412a9a403540004c1c1c070350300c40900413080365070280806110700080252007407818007000c2e000c40400c445190025074004001071400ca500041210700e2528903145810303c15010742d40c4034919008155909803034032000780100e0015002603082000741c100d00c8146a0000c25486407407500d5900e040e0264007040c00b0303444458007000c1c1d045502d540090241c1c16280080d01c2c01c1420303260284c500820940241c811000c11400724844090001580068440380b045c1c078501a45403510301032003c03002c0035162071250081d0300510040280c158082807a021081c3c0640380001c220b2944c040c2c4407040c18403505114482ca0002814108201510703414a04941c10a1000c0180081e840c04102860714040c1010300558 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 668287967 1250 668286717 668286721
    0x10b12010303050c0a020a030606030323041503020405030106060306030b01080102030402220b150c011109030703081b01090b1503030a0806040c03181506050105190507020d060e060402030c011106 86
    0x20b0043c0c004001300004081100d1940d2030b903030300007011203115401c204d94142d11520100101600960840d10800000e950380340d9100c22100001d03101d0185129a42540100e0a100c3d09202d00aa044801901c40070f402845180e03200e41d00640035040520007152403c1d07140c07000142c7c4040c1032013601d01550f401003070503050040d2980c1000c0300c203018624858149a9414941e000c69031621586a00c010610100310b449103059807503e42140d50916007902e00c54000c000b4030010f80d50129908007176035401400705807a070784100d0b20185454030302c41c0000002e61802c0ea4039018000c040b0041840780c0c1c5040c400a090400040900d0b44a0203a000070002050408010550703501e0503410880380301d0450b18001038180200320000c2501d0601c9001507034000b07440d8240ca0ba9005140c003d0201070b02c8203080c62803030140c90300c1c46846c40050248104040242c08122002150b5070034012081e800d801c000c06000c03c1c102c0100c42925940d040da412803081c0300321303114071103154004d80c00203c0320150403000c0d046503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 668289217 1250 668287967 668287973
    0x31e21070210211d0f0c090403020f03180406140303090405090c04020d270c090c09151101060509010f120510020c070e01050a15050a02010b031b01020105010b120103 73
    0x4001d0003210300500c074000e0f11030341c024070300c198140c48040d00212000c41c0c00c070b40c580d003031651032104072070004400d03003200301c182c0b408803800a2000072030002603407520070740d54403420100d003000480600010700e03010000b00105024800c1e4010344100c00110380820040b5614880129038662702c04015816400500480509140030b510040d0b008016800343c416201c6a00c5c0014100d0740000062524a079440c07e13103006c5c2880611310034045075214040060b01c407000c0d4444011000c02c0c0c0c0b080e60139181d01c1d1a000000b03e0b04c01c00400001b440c0c010000712041a564001509a11800e4440001903282a40008152400f9002c00381202c440c820300c03071003103400e16034a080301129059080d2464485e000d081e40c1d06400340d1005011010800c00980125401c0c080c0c1d2550009041e405240b0510009205020f40507250307a5910002ca11410001e40d503481c084002e902420301e103035240d0350501940901000c503507034120745401d102c4d809034005c109030380e00ca469210711801501001620014120010300c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 668290467 1250 668289217 668289229
    0xf01090b01021c0507110337291b0d0f060f06110d0e01080f070c15152c0606071712090105040f030806010c02031e210702 54
    0x25403040c415039143c0403800e00c0107010010645030305400100002452002d000401074013140a031022400360591b403196111580c1c442e06030f507100303103142991200f402c141114241c400e001144e80c06055540c000600400f1107503c041d107031407070a000560802c001119058a4002c030012096903151441c10044100e015000502c0029050001e2658943c1e0100752039585280d100005c00c0150b40d15080074150f468071505101450702c101092102c0c0780300f4130640e80c0c7c0104646500a50003015920150f03506001100e0a034482c0e500501012030406040d034050400f0b4102080c00c00790700c480344425a1342ca0341907403101500c44114481d00088468003141210700b075005141c100c0c50041c003003030421405440d142236410403159910304003000065a00031410300451265802000c2d01c0080010745019102c3c18031001111100404002140c0c0c00034507276078001d42d9284070945e0054121081c6049014400c4401e007040780701000580302e00b60241d103c1d8207405910390000080250002e05200c1550700f8000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 668291717 1250 668290467 668290481
    0xf030c031c031e0207020a05091902180904110306090c0102071a040f09140610050d091e03020c2821020d05010902010e0a05150702060d090c0e060103050f0109 70
    0x80648032821140b40340860380f4960381070110300000680c3c1d10034030300c10001490307010351001e40200e0404003000640240d6180c0c101480640d068003580e1181f041076140400042848420f501030901801d21060202e2001c0342620118150100c07540d40d00c0740503c040d69581042d00f0700340140c2c4240024000312449003030100c80199168142c505180d00c4647c4010b10b00b140b50410458242d817903205000c1001004811a000001035950700b800c3c0d82030b100010b1180c802c1c01c01e00d1a1068490105108001401d5010316018503032070750b510090003d034a4000d448890402d03000748100702c01d0341480c40c280e919007810b0320f0303400a1001d4140d03a20310b4103500900c484100d600107940080841c440c60050f850700414aa901c0d40310303000009889003144005000700011070241801041412418810798035006038140c0252000d0403c943c4a280600c00140148103508143d83c00504100703160342002410000c1c0302c00d4801c00026848107546100c01102114403c4030340d128040d01d800d004200d04400c41e4481c0c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 668292967 1250 668291717 668291773
    0xa0314090a11030c0a06020d0207060305010b0f1305060a09080c0f030613050a1a0103120c1e0503090604091508010b030a14160b0309190206070303050705040e070306050f030c03 78
    0x602c81352940000941441056000304056081043c441d290b1030360601102020b084d45040030011541451803a080e14060f4200d101064030000a9404039403214240c1c000050070010641c50741c81c01c8001005040661510900b0101e03c00d0361400c6140d4680180c00d42c034030140140c01860260340f44492806503030501d00f02030329540246507005020560507400410030003068103515403507502d1032900e5490041d8001d01d01040103200e0a4400000d001c0c2a4514080e610b502c1020600301e84e2400c1441c21031040441080c0d2003480040c002800190384e4009040400390815640d142581c1c03031048a0984c0c2040c1d404036850b41225442900046080c00480c000001d190210f032040d009682c0e41e00d1190200342c1026402c00008410064811000c000c020300c1851828010350322601d0381e6003c607201d40a414001018180c491001540591151043e14000c2c5041c0f0450003c60138424005401020640241400b480e012600d0048030305000501d90081040540200407402c80c00d8211080b081d2108898 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668294217 1250 668292967 668292973
    0x1205070807050304060c0b130b0a05070509091e060d0b040204090807060504060b0a06022b03090f08181c030807050c070305011b090e0a0905010f110a0314090a1103 72
    0x507002055041002d04040c0c2840d4440c0c040c2150030f41030401ca50701d0010056031801400d40110720000301d80d4003120380c00419072880031500e030329144810380e001e000701c14805400688081c03c00c801c28802602d44030714100300b0f895014183d214003082c014146441000134001e0b41480e4080381c01402e250340452601c5d401440d0700703401c00500c0c2e0380b01c005031003084e84c0c01d8030009d40714420b5190a00e0600105402400280006c0c0410034000c0306803641c41404400c40b0220011034580c202070180a80c000b07495441c2e2204c041c9840040a240401d9541c0140c024404a482e138079285c0b40351424001694040907129112514211181756000c13580c501d00101a0020800c090041e40414001002800c01540c42100081400388003001e07010420b8550b1803a0008106d0300100c00c00203c0c014408868110791046004209078070746082144c05004075840a8020900e0b04064448440b46080505144c0007240c0d400d0190442ca01020b040c0c01c0029155281e96030420340366500000c50322020302c0350040000e025 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 668295467 1250 668294217 668294227
    0x30a0318030204050a0b03070f0513020c0a0f141213090506180108100b030109260f12091006050f1915090503190309170f25080a12050708 61
    0x100f01036490944040190644506100c940d600e401d100c01d10180600315520712080d880d01000490680801c640c0c2000660b00140102030402d0a02144007401c0d0842c5201c5810b621900e48420021070030600b0202d98040e041200782c1040c60b00c0100d80d8156101e00071100c6007400c040e00d840c000c02010744155805448003800448405040c28420300030940c120280040d42d242e4002c41094450358903174107209900d4216084000b03041850030b0600c01c14900700c0542007165516520440388144100742d09000c5002c42c810021400301e0700c1c0c45119084400540f1001034000600b203041d0703186030091580c00305200c00c40c001c03282810300241d02170002e420241c0b003006645100281d02110b21403061000101c00030707014400c41c20104600c10415204001850301ca4908c0e450041052540d4060040d4541092001522100e0100700310780310b0a0141040c0c0f483e2035040c480c00c1041150f6a81969925000004009101240071416102441d0004960704122064400446140e07010400480d074170541400f03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 668296717 1250 668295467 668295469
    0x80709020a020f0d1806080f011e0b030c09010e060a08041b0f08071a070c0501120902090f0103030801062c01050f0f0715050105010c1203020d0c02060a0f0b030a03180302 75
    0x10441054416880b07110800349001111070305c405d650703042801404603031000c2c81850880000524111001c1e02140c000394511031800c00d14107a4a540006183c00c0b02000f80809500f01400600440c54262510005203180505104a502545c0705000109107000c00180100303c801c5080203c20789010b170240c18035510350007400ca0351040c94201003015403010b2024441803015000340d081c0410f01181070790904041c0da94100820155002d101e040003004912103010701040d401c4412400c1c4c2c0140800d002d8600030b0040080b020003444151b00254004000003082402240c108101214141002c094101413800c1400c6500e00e8038a00c9042020801c0394900304400140079102500e03006043c42c0d929142d5003041d5650b8905040c909410500d0074004029a0b030b04a654091101e44c0000486018100840190028002c800101c1c11050800c0e42a81c050390380803698622070030562204000c0341c01104008000c64a10602080d00359100c2c03060440403034040d603030b40154546402e0451014070344a87c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 668297967 1250 668296717 668296723
    0x1101110d09180b0d32010c020c01050f090d080c010c020708010f02040f0e150a0801090b1003030804020105030c0f3907091113141801080709020a020f 66
    0x1500c2400034460010600c1500540308810007030b2820740e8002d0111003030fa03000164203058460030003050815855640c0c2ca11043c9205462103521880f0b05206400b05000b45050280c170300304d110030300180100340c102171856008009a0711143e00f8400011708120380300b024090321040810055440180c00d20181040080134003941c414203041d94082d11001c2d00d8009000d003940d86208528003140c5c0140000d0000700f20201c502c4080f039062126a03401900d40c0d02144d05100300600a0702e8008450f0500800c07100c80542142e100c440c8a090780e506d03203544400258554103070301c0c000100044c58032000b282c0550720031005560400c1c442046203240108245021030301346c0c020340516014034a41108010131a01c180b03189290038040032681781c0f00055600d0126100c0c0110b0040c00016680d4044402405444c07000741c40c104070b4a080990002d1b500c404030518150035140510740b00395002e1414010001c2c4001203d07048505200043c60200e0500300680003035080b0008140c00c5200ba030103d001c4d008420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 668299217 1250 668297967 668297983
    0xf09200c0106030309081f0c032c160b03071112040602010b0120060a020d02070b0a060f0519030f020f090403081819080c0c0d0602120f13110111 64
    0x40300024030381d843c600d80580b48003513582c000204c0380c00c20f1a1035040400b0400704200c00c01222400060f010b030705a071003a0014240d002c0c1c40d248200c1d5400c080040d629103405240c0e00c082803141110322009040341c0a000741d0026020380c4003481414400701e185240590414940114500c1c02c1c1c803104445001c4aa90b00d4000ba03000b440140e444150f0b0340b0003540c2100800d09200f01040790134881c0a020700616a4640300540f150030040ea001031140c01c1005c80390305440301c1c10f17070184401c00ca9060809520300038100c0b5000300d000b00310000600203003600c0e2003034403000c5043c1c4489076034082e9455903c805d600b170b081e01a0140e802840710181e0850036a2026202407281d84241c841c0380300e03400e00e00702c04141d0b0032100f00c0d0f110650307000089940c03002035810f0823210104e501204070307130392051680d201e5820085980401900b00b0010b41550041002c40e401a09000c1c034021164505079407014082c240d4444190703030500c984101512401c000c175206a41490150006042c0714070301c00c0304081c2e018174000c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 668300467 1250 668299217 668299237
    0x1502150a06030b0f010e0705120f060a0810050108010c050406140901170103230118080304080d051303020118030f2006090a0c09110a361503060f0920 66
    0x1100c0011b014048800f500280c214a09280190429900351189407a42c0c1001d031046041d0a00c24000441035624900714501400481040d140f85211211025000d4807007070050202035400d002c485400680b04009131011140d16998000c00c40290a200c841030b9400109000c2c1040b03141c0d40c240c4141d00c4680b124a0095100d05071580c1804640a01d202e21840f03440765440240c4d0601e00544504418180d4000ea0240c00075100da43e00e8039107192004107841103003a0310129a04020400a0180b521801c584016003e03030000d000075800140602c03c1e020071751800034041011841d9284106200d024002c1e25a5124440580c52110b24011585048411511107403940d0101219104000502258900400300904184814414000c000301540200041601001061080600030415806811210030761101c2400841d500c81e0404402203480c42c050000035401103402180301500c244102c904480450704404081c03420140511b01500c85540d03500903220014941e4481c03142e80100410b0f10843c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 668301717 1250 668300467 668300491
    0x307121107051e061605160606051c08120702010e070e071101050903160c0f0e07030e0f0705040f0b060f03090c060430050604030c03091502150a06030b 67
    0x80c00b4034142c2e1070002500044202a1421080b2000d41d01001031426003040d5004584030416419020443d402e0241014114000d001c015040003441296805401034034426500c90340700078400061142c2c04851148014401340c03003040907005030384e8614942900702006200202d00607000c0c0952074a050b02c0ca8001c809c080100e4002e110700d09401480b007080303085400b0001d00151400e81701c0140c5074000c0070321840c00300c0f10f500364180c100a149802d45001d0541070307a08001046d21640e0108030000200d5202000c01c1c5042c49844060800103080c0d482403440d500180790081c1040c0500c0040e00790314012214207911240400a1940c0740e0029143c3c61490f1340740d95851b4a0f004618605d01500c0d60250340c01250304000c03c0c410350100c0d0700c00004102e010003083c1d141d07030306803035260b84026629070303019003540141014001010341c84040743e510a802135584680c030310f460341031100d5500d401d40014800350b440403000010480b41c103108035030700440c040300001d011aa0303902d0300313a5041811611118040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 668302967 1250 668301717 668301727
    0xc0c051f0806040902090613110a02010c020d03020304120c02060d020c031c02091809030d1107060c14120406021216030c0c1109090a1b0509130f030503071211 70
    0x5902505040d03005004440503c030380c1302e19030082201c440d009000d00d4016885801c00c8659085207402c0940d41040d4911075541d80c42803540300038001c110381144440140188050a00c00c54420300a0304e0090f0781141000803800c500e5002078840c0b8000390000c82e0001c1080c41030068400c950b2018180c0d0503d0000079603038866038920311414090000410080041c81070102030705a85401c0b9500311a0740000104140d5074452095040c0b460240228100c041410b04400031052a140c0c0041e1180300d109030030520411028010a80d00740000700780e9200d200c00d050001d5407440c4c8405240d16045400741d20014a000ea15003154210007808076840e0481d59001210000d032554188690440a034052421a1680c7c00d90b9a642d030900d0740e50513000e07200b1044d41d004910540d4003405000c03002c42d488401400049810603e08071051068818144680c551a001610180e882e15450045603400300c1858080221a507054405400150520007041075001c40d01c03002480307a1061148540c2c003c00507540311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 668304217 1250 668302967 668303029
    0x20a0201060f08011b140c06040809041a013606020303010f0b0a05040501050703020f100b1c0807080a090e010602010510080c0f120127210f0c0c05 65
    0x50320396030b03100c41d800d0380c034040c0060001517502002d180c021400b8600044810700120307401d18140540d034818a80c1d4041c0b4001e100400800308000c212884040d581488241d60100b9100703618010303004403d0218080400710f14540c01310560004000c07a0621a6002c03512078030034000c8984407550010805a44008014800340d2a540c400100402803c40054549801d40f04014001e00551059a041c0b040100c0e411007054000d00c039900141c2200001c8030254480e05440002074019250714a0089007034024603101c4282d544120340105800040044c903003042e981d1070001550048401c1e4040000c0240007043c407102d52407006000305425400494a4180340350510014400baa10900c01036210001c0b000d003a03110f016880f018800c0c22100c10499004141955024000a1a5540d2141d00340f0080c03140310724658030280704c9030b40610040884c523400e400090264220f01d0340d41c040402d82200401154600ca17086107610a84900d04800100da61207010036040c06103481c0084030b10071862008009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 668305467 1250 668304217 668304239
    0x605090109120c1e14060307050c030a0c1b0614030604020f07150b0f01080402190506131a120a05070210050f04030206070e010c080c010204031e031d180a0f020a020106 74
    0x5113003411108500c2036180c01c88070803442d404500850300400d00400060000f5000300140c48240c58282c007900d41e1840802001048000b14880450300110141d40400e40140c11840000c02c3d5082620f0f04c410b4030300000c41c52103e5820050101d80c1c0983c00300140342410f05010058081544100024180480800240c0007911800c1d80007501403901840c0c5844540e0b880b002040c0c00940507503d8034506800b800592000091a0b0841500301600003420701c900500021501c04a4464610040e044030007254602e645100d140e0f4200450700f480c0002c00d6008a040d840203800000c80d00461750143c00c0e14464100355035080303c2c840002820078040205058050015642c840c84d40d14203005801a0800081d2400d494003001400314900840c1782c60082030f00354100c0b00176503001421002c1728065807080c41c0d01d20603029000c40001d0f0021102e00240c2c92020320000d48490300400082c031610b26850440303052080100703040240c5468860001c1e18180701e200408101c2085d5001050751401c103103036028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 668306717 1250 668305467 668305499
    0x70c03110616061503050f100e0607050307120b0a0b031602010e0d12090b160f03020903120711041a18061018180c0917070605090109120c 61
    0x40940300c104141442e4441640002c0000b07a4003072070000320000d00c104805039403045500010032903c581066002109000a020b10740200088011b11400711244446501e409094411030701261052001c100c0345400b4040c2030810350000180001c44400502c005000c08129a10035288840b00005120740020201c05901c4517215500007404900c4584107030703550b10108000c8003820482c070710089000091680e0400d08140d500041c81e0b09080c1008000c50036072007044800240402c0c4c0740706852860901a0080d10390303610004014006d40c03142200d500c04168840304007100e0000c4440e5016181c2c1d500e030301c00c42e041014020264031f403410480c814000655514194880c00d445e9a00800580380d5600c0c01004041a503840c02c0c0c040c0500156800c6418451500301c07051280314610034040440b4a90f0003400340d600c01d5590b110305140c1d501407254207220068623440b10390b00001e4080c819103001d0703c0204500d00040c540102526035072618000c0654110304215113525040b030080101e1035441885030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 668307967 1250 668306717 668306719
    0x1c0b19060501030c0206040803091005010902031012032705090a0e0606010e1309140f0607030501120308040320010e0303040506071106011419030b1009230a090503070c0311 76
    0x700380d040004c030181d51214024402001c0f00b074004000f8440500c00d00c4504500c1c2542c1200703010950310740c2d10803006508100c42a420442d032504000070b00c801002a8070001d183c06444840d0a0394201558007542d5080517803511070513032081000215504e40c0c849162050312034038400a1800d41204a26003400c002402c140d0402032032941640960356180a0441d4100c804400010507041c0c0340b070f0030f040c0850014030226083c05203581031104041c011455500c140f030195010400c9a80700c44500f08145903400003e8002001c4400007800607000c1c051401c0c500e001c10f0400010448100c81c200d003502c541c600c0d1b0301d405030008028041041004c001c42504142141080007062816040203951000c05100717080c00a03082003121001a00d82c41c5150f228a07005480d035212840d03d80c240300e003201e1401e60b40320070204030b100b10000d9000442d200c1c80380d0000d0114120100300413040c0324420600c201a04240b21a50780d500784000041c4208014001148141540001c00b4a14200300c005c83c11030324401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 668309217 1250 668307967 668307971
    0x3050c091c2a0612230a0e07061409040b09010602100e030325030908070f15050f01051908070611070906030308010b0a11010e0601141c021c0b1906050103 68
    0x442d4001c081000c0240c4042d454402d00c40004186040082c02200303a017401c103c42c03000d0141004c0c840510040d0b10984044000303001111060340500d9451601d446218000b40301180a08106c026480003130103ca50002c00208001110f01c001500c81d1000b070344954091b03172040c0c1c140e034030b441c109000d0401005010000340d402d510300304000c1c100a00c41d000c4074120306403150910108a60180e0300c4200801c0d00300d080340303444244c0c0b86803600c404a0a054260760b4001004403041c1052000d0082e03510440303108483c0e0445918060902c013250035031150300c42c0c601d2009030b00800c6d16002040650028141355940148050050001c24180025900a4141b150418000b070000c01d41241100341103401250041c3d545865101c011140703e000004040040d50900300041517031400016a107041e07856a8400c00d10494507082003201c282c1c0050750f6420a410b02d8000f450141c40c081c6404603107159485180140095256035190541c1001c40304a071003020316600c20181c9c5984c0c0e1140202802080c281 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 668310467 1250 668309217 668309273
    0x6081c0905061605030d02031504050105040504020f1504030f0f110303070f1b15020a060605120604060c02010222140a270b040230070c0303050c091c 66
    0x4200640700f890b421080c4030f80410320041c01c02c01c0c10400c07500c00303000d4030204546a051058107c6400f0b2000921039201c1c506010000c100c074a010721071f00f07009a5005243c0d014013803c002c140b10351076041e040b005142c40b0f4113120020108500301e19000b540c038454038404050b02400e01c0c29200c120a400d0265000350b2044c0640070025008600407980e894202c502c9480ca01d8102c400e21418416613006a40b00360301d81d242120401d500000c0015000f4451581840134070388803014024990032082003080140d000d200031030041019944643c5030149548000340c9043d285003030003440d6400769580c0000b2044595810004408801c01d1001c000e0740c1294107406092824020040b40c5414491a82410108095680b102d00d1158840165094040c3c802d43d144c9929500e541030b200700310301c5c03401d0040048030f95051401d40c10005091103014161548414078509031002c9008000082032040419410015180d043ea10780141d00a0009103a164802110440c901580f0881098210180301040c80007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 668311717 1250 668310467 668310469
    0x10f02091302071e080a0908030a05040522021306110a020117100e19060f05011b0f150b1003090c061101140c0a02190809210106081c0905 61
    0x4950050070710074401586603241070400002c0d0546218501031030b81d00c0c2c031400d42d041180c09030140140d002c030358039880940c1d966078491507168460b408420000030703410070050186141c0100f100780c800c40095080c030101e12070482c88208983c808001c01c000030119000c01c012640d4802c1e5416a10551000603040c0550b45030b0020700748109081d1400d090b0580a000a0b05010342c05d01d50000a04102d60300011320300300645504102401040021000c40c2044404901568079100100850b003040c0c2d03605400c00c40a1400035600000d0120072503044036000600c07000f10304140840e0082240004001444010480400100fa50034210000c285410480d0400102d02211646002c850203814049900c14525201e9130042c0142c0761102da180540800748940ca2021502820101c10789808a409a03410035880328060b10740c18000615101c001c118030400390505802802a00381c0e1034107913584191150404034295030f080d4003d801c0c20f62241840081c03149540c2140003a42c038050038030352031130341c2800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 668312967 1250 668311717 668311729
    0x606020715140409020304060e101a01020f06071107081023040c0312051218070b1341010905180604021b150103020a09140a0903090801060b040305010f0209 69
    0x4c860f082c84140e002c800101888101d80052007040c950b1004d8076900e142c080c60800080540301071401200030b50000807007165000080ca00002407c00300200350a99440e01d00326090000d2650b95001c0303000f000400101c294041003040d6481c3c2c0c418401140c041c800a142500c8a00e081c0e0080840c1c400b0741c800e11002c51480541141030700c1d0440c00c00058894069000d44040c8508640780701c1c500c10080400481d038401c2d00390410520038040503900100e41c0c80c5020f1455001e4514644041a15100c080008112101013a17031040121000786004040000603c541004100c5c001803000a48900c6460b00390390111650300078000c11144a81d84060203825802800b1006000c140150380c005510020700c0303024152440300718030100895580c2203004440006040302880102e00960400401194004d000c0c003d40c000052114040740d080d507074007074014018180040d4241d091040e80440414440400c1c041c1001070300086509550b540d24600d442821600b00002c0da400003441400240069030b211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 668314217 1250 668312967 668312969
    0xc0201120510050a0806060f0607051c0903020603010b090102010c020f0d0309110a0807140301020301060e0607020409050609070807090501080c1e03010903110c0108013606060207151404 82
    0x7140d03a00c0e080070554000d842d030882a40500500700016044c0d000182c0c4920070385003038940c4440030341000207001c1c013401a41801080340d007040d4a502d402d412183c505040000c02407a20141c0d0135a02c2e0045050359000b0307000400c501c2e8002660580550302401510000300d2217100502240d4002c00046459078007403c802c2d1b0070036032202e220f181070200582c1c40c07160000c0010050031390310780c4c0c95005940d1003a8910a525040001842100700e900d07061003034070704a5010f521640580b40d0200100091340e40700c1c40e022a030166440c0044c80c04510204032807403003003500000800f20b0a040080c2c142c41d200d503903800407040d20309100042c0f00070300001c03070032602c0000142c51240402c0120400c000212017400082501513292140c9142456885225034034040d9800d825192504052001100c00e10024001c02c000401c02c1c0e0a03020180340000c0059024404007949410300a1556410105641d12035103c170b0016070013001d0030320130741900c01030310307003042c52142040b032580f030381424102301e0714029 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 668315467 1250 668314217 668314247
    0x40b18061b15241f0201050601080c04050f0922061d0f0304050103051003051b2d011101090f0c0e070513090207060906020a09091107052a0a090203070f0c0201 70
    0xd29079024800380c0700c00e4112941d85000d03004c0042285a011002070080c801203542c1400184000041030244561000b240e068482c040d06c1c4815444106082c80155000500401c250414100f603101c160720b8103903500c5007500e104800110b0a50108000040d45040c0461034a465410240420b1406940002100c048500a08011a5030381d17a0309001d10381100d542d44082e11901914210440c0008102c1640d00f808408440b103c1040902c804901a01d1071486012507841080c10300740749035503006042070700c507182210f0008a009035030f0380d50b41241d918403603004541c11884044244410b0f4840341001d54070406601e4003d05298038040300e01103024191248812041c0e00068160601001da0400b4010b070381c00c45401c2d950356000c24001071415420744941d450140c500038a2903200e40a9000712054260001c0041c0a00481c1085410451103803c5c010f01c1142c45140107240c040e01d071b100496008141100d00142c982c80c3c003802c00340441c0b410320407410400071003c82030b02c0182e03000003020701c4548c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 668316717 1250 668315467 668315521
    0x306090e0601030b1003080703020c030106150f032703021e03030f0c030601140f0c120306030c130e0a030f032406081b0d06060212070305040b18061b15 67
    0x214660071032001e00c000d82028122030f83c005862803c0c1a000030341103100bc44181c000308100e5565400e110449051000144c00045035880010304443c400d8011802108640c4e0700b513600c51403004201200c80d90540700842c05600144003203004005040c2040070300810b103030080c510f185040c6a070150600c40c01440d0180c3c454010000c501541d2140054210040545c0c008594a00011aa4110b141c03c2690b20035090f00c90026040031850f004400d0b03e00032400503008020203504842003103049a655403070b42c00e07a00d079980e50704401d40c00e08000c421042c41c06611070071006e4001c202c005040e0394030013101b1180000e4000c1d82880f0002c40b03401076422242c0b41e1410103402c1d20b030401c0115032a4a00c58020201c03500c080b5009003042c5042d4040790032070301d203a005c40f1142c882400c02c100c101d001d06180500450014401001a081d10a00800d00c4080e515070292a1209403000a46d1540204d04417400c0e00c0d004419214070687c00f00710341e215606504050604500c1c0541100c02070704c030307100000b0084134 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 668317967 1250 668316717 668316721
    0x40b0c480a0b030714041202030c04060b0f071113020405191410020c030f1038011202030112060506040e0a03050c0a0b09010f0501120f03140f12070306090e0601030b 73
    0x19201c1c26280c0715100064280c2540c46e6a0382030411010000a00306900c01d008095140105280500c540d00880704c0c1e0780304c110b052405101d01c10900d50081c007826203410a020400e010309a5503e41d0b0841c400029410050b1207504020a0040f2108900c0b01441e41c051255410302a19001284000341071a0464151100c1030780c9031001c81c1000e030102420758040c0314005404940d81720210b180358040c041c0c6001006902140301d4106800c089505070b4002c102d6030380204195803c3c1d44081003e138040181061310f0b12196054021042340c0c000d9005680480d00f1450030700420409000c0c440e0040ea04880501803591a5103106403210000800103041c0000001c070340e64052818013100204a801079036071041403800e20f01d02406408020511220301c1c0c500000810074010b5024408040c9421044010307805146581c191040181d04264003030003a0180465203103000642c0003014081c1c0d2013400c500e003a04140c0000f03016164a070700036210b03550500310505540000001d0480c1101e801c8055500e8503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 668319217 1250 668317967 668317981
    0xb07060213030203031c0b010302070308013305090414040b060906191403101e110d0c0e0f030105070c060b1318111005040b0c480a0b03 60
    0x411030307680c4004c3d050300011134441648841c0f2840c0450505085070180201e03c0204011001c0f403144140040204803510010f004c001140203100d24680e01c000c552129100b01141c5600400706001c5007500025000140790800e81440d0144c0d400229020304803840d2801e2542d10600c030350000032300050103402d00100251003665086480ea640328038a04149072a0b40c0c440e05480144000402d206000380b207101400d00403039404e0310445e298150307420040038803085010b100703c010b04100c1c3c0c80e138500d1550501050003202294411200101900d448620301d40c0240c0c0284501000030403500c0e40300f030345040c01300319040341c00100d01401c0d158031600004410341000001005040c9103a06031071001d00e840310600b0300501c135140300256275001d006450400030480d0100259003940e0b440b4240000c00030b01007001440c44a4003c2c1070003482c850203a942841d110205003001120101d458408407188003202000300341d20b00840418910745400c0c2801003010217002c581084894411172092510000004081c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 668320467 1250 668319217 668319247
    0xd1202031e1306020c0703060605030307170a0905100e130b010f140f030a0e06090f0a11010e090c0a090f050a0b0c030d0f02072d0210120501031a100b070602 69
    0x16032079002c00c01315161950030400c1d540e912881d000c00c40b8001d2501c40049041c0c40d0000aa800070b603403244201d250130a00b14800465a00098540401e104030104041010398941000340220603042e03031924a01c00c2041c0070008940c140710b0016100e1450303c01c042c441a648688640d41c0a0402c0c2000070b805030140600d060144103542c81483c101c0000f01c00d2143d0084076401aa080c200540308490003522000c0390561a058413105401c0b032135101030000000540800208070b0350f400141001c0e00c0306070700807010605c58281107850322040f0b8000181a00305680010700b5101400c200a50b14450700e0926001c84c890360201d018000d0350202c0824904034410003081107070341c91a2680e00503c404041c070a8010083c1d04404070031910010003031550f8a800d0b00c00d0f40d200740903007034088503602c00000035024041ba1a40141540c0200a000000411102202c0c040d180c020340c41894018401e581005501804040182043c9200b4204a008104009094007914880784d04038038010303510780d41c000321086 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 668321717 1250 668320467 668320501
    0x150c0e06090a0308040b0a230405010e0406080f0a0b16020307080d0e030a0c0203010f0c05030f15060c060a0501080f030d150f03050d12150909051e0d1202031e 70
    0x5130000900441c964040c070001e02982c0c0380320303202c501d9804032000e49080c4480d1407050184110300d003071000b001250b1080d00e030060a40e402600000d001c9844031036031410040440382c54020b5a103d079841c203080140004816a10000500310515190030081009440e8860f4100140c0070700804a6100c1c24070506610400d01030318603108490340e030aa4200050074001c1c010304c069109500e0b001c2841318509450082e090340c8140c1c0c0d40c7d214074540e10080d04055401011300001d03101c3d030380c07240b03207469580700c1c034000384604400f080003840c0302e1405403405401ea8105802c02d0780700e034000c144800388410700042525480c001c80440481c0c5d014803900f2180c0c007a40203900c16403084100c40e03400010701c800494400005900d03683d5403903810070a40b44400503101d588034070508c40c103202e0f1010402100e5541c80721211911a40942d00c2207580c01000c0606190303041003030714003504524661103401e500181100b0b14100c1c071030320a506610b000c282c0e030344140b000d101040091104500005412056007074210b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 668322967 1250 668321717 668321723
    0x60c0d080c09030d08071205130303020a0c050d180b1602211c080906060109063005060a14030a060c021504200a0b07120507061404150c0e06090a03 65
    0x4a030300c0d01c031082c01404071000f46c036050045200984036030001007407401801d10840781c405103081c280c10181c1d4100e00a40c801c20350482008050704460000134170a1019181e0410300e0781d1030400c540c00d240070131034008040c0e03032110805a004006144408003494042090544c0403500e07a0104180400042142001c00105c11690300402402c19584145084400d40c4c101b403565825540d0b907141090256101c200352020781c0401c140b074008020481c45261110032141e404d070030710005507000d151203141d030b22034020050900940380c0080001900b04611142c0003001818500181000a0700201c0e444860f190707009000b090311040e01c481c0c098020000e03101019148111a0407500d41821710381241c180c1080b40402e0b1540c80301caa6030062601010740d000b80d8501508252900c0a01d90721900d1084800302140d042c0803061080d01c001c160700340b08848008070028000c203058035203840c00c4017800c00010720b5401c19500e0013100c0d0013882d622035a0303406221000d40e602550b88000c28000751006d071041e4401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 668324217 1250 668322967 668322973
    0x4050601050f0d1433160905030a120e06030c0d020906040e040c0602010506220e0c1008010513020f0a0e010509190e0109020703021504030302130b18060c0d080c0903 73
    0xa2400f0950001c1d24903440f003944900d1440385a0400c50b00c50208440fa2060505c081129000c00d8454509024441a0f0107190500c1c8103000d5541c400310382401070188003691010a240074008042da082580c480641d41c0869540d461442c01002c400750b980150400f1000440e0f01007030007111511414116000340a17680603045040c90030307107003848000e0194000e143c015420a00402c0035410000081c44c5015140c844074417610f03030044440001001001c01400107071040511044058503074001c055400066039480711129070402c002c0c442d10450098103034415610402c030401e4180b1207941501c281c8081440c10080c60810800100ca042c050303498800d0307000d0b000c89401b89600c560b50b8419012103455481d000b095a984081520480c060f407030000c3d02503082040e81c0c0c400e03007400d101c40c103a2151180c1801410702204003080d01040025400000c0c0742c1400084103550810000d11034202e071802207411502c1d1204150240741c441d01080380e01381c10710944d5000724501400020640380664009012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 668325467 1250 668324217 668324243
    0x14040807060c14070303051b04030506011e0302010c030507240c0201110c0c10110106090e0c0a0803040501032a02030324090402010c230d0e030604050601050f0d 71
    0x4240596400345030211009803500701040c400e14011141000b070352100d4a24035041800644081c0c0150000420351070012190510148070180010080c1015600800041000c0d60620202110706010728078a0244030b50391800401c0140e078010300305405241c2c540f0300161282180d203480038091024548a000c66040d1900d4120b00724150741c0804003500b0310b50f00070701c92104080201103040c4981540207400341c11058522246080c0a403620010149525004000381c0801d00d00600f140d1081d0041c006442d140e50400074400403c20215901c040c04407a4680041c0c030b4a81039a03900e100350b104413030525482d8984070000c9480c034080845404203000383c28110700f204074402512070b44100c07412a50410760709038440310740612034102036245001402c6600e20392a5500191103a464000c000c0b2071400c0041c5400800800c1c0318510400b50810200800200c0c01c01c19002e0306500301d0100c1180070b94001020480469400925181141d02c190341500c032482620007c5000c5002520000d0805201007503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 668326717 1250 668325467 668325473
    0xc0e0d05030a020c0d021804020619120b09061f03020d02040b070320030304020d1e03020c01020d03020c10110f0307180f060804110622052107030f0302011404 70
    0x700030721410410740e081e00c401810050400c12080e1301c1001c00385d0021111418101d00c8203101c201d880d00140010149814000b040120600050342110000005050100c21038803210b442d002e00f081810742260444043d01d0100d01280d9420340c40060012050510001001c01c14081da0448020100301c08040d5a07540e00c8020a5802e64400314040b000201c0c0c82d85d1346031a945110724800180c00c84007010f989180c8894003080396042c2d1a0b601910041c0800c5030b444802c01003c0c003481207a81c0321f40c0203409020b1001001a041c02c0e8080004410301d401041865000d05010480c548000e02c1381200099031440f8140380c1c8028022069a07503003900c2e000040c44a02500300b80010303442000b0741d4081070380f2030311050f50740e42100c0030307100c0c4001107914400854001600a0b58623980484003402072400e0521101c4d044003105504841c12610034502e00040c0006e091003000425071504140440303b118000807200c95440b0b07164070024005040c00c1a001d41018405c0d004030340c1e482c2105002e180b217810282 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 668327967 1250 668326717 668326723
    0x4110114070b2e0603020a140d0509010506030105130311030f070302031903180602160203070906051e010917030c0709050106120b0310022209021222060c0e0d05 71
    0x143c1e4200003515501d00e503040c034250303101c4001d02c00d01c030244008074054a4a141a03010b90030000110341400a940850301d1003000d168003900341c1031140300000c00c0c1410b202680508441c40640064040e905150400c150044405640c1c1d20300d59051800c00c14102c8941181c60030b50050300c0340700c0c3c41d4910004241040c903a00102400060b41100f50011801000650503011950b60040c904d0801000000f5000070a80c1070340a0500e090081151100900c02030307000a0805000e60440c16501e69600020b000c9800c0841c1403450a0360316540c40c8500412401c00070f00a404944251a041c1000c0d00380144074140030f1058800d0041007804940e40380c1c1e120a280b5001c3d080034000c0200040c0c0780100c540803000103008829410f034000e03024100c1e101c0c8140b1071401035480000015a08030244000410106e4007100c0c0d42c0c0280b0428500580b1340800081070164800c010306000d440140e100405c144c030708028041103501d42d5020b640055103001c1c7d020140ca01096651526a001d146003049809001000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 668329217 1250 668327967 668327971
    0x91903150501030b090c030a080313050d08100605090d060b1926011a060a030b03030309010c230d02130905250504140415030c0b0d11030f04110114070b 67
    0x60395452685035500c1d0390142d82d0b035031b006d06070310b80c50707808030300e402000c604008021604004010700341d80c0d2280c0e0315154640380c51760021003640001e0041d4104210b40310047c02140243c087c40c90321501e0101c000000401d03070381f400d95025207459070b5124003d20380d9850155a42d406040100a440700e95900c02006034450700010910301c00700e41c13419000c4420790062080c40d40c3c44420344030350410030300d0800511642d40c01510303d43c014550b0b107240380320241e6070410145109a200d20000b16062078003440081c0008180c460780c2d12a5031540c4c1002098001440032788802c04040480142c07901c0000007090404103042c2d00685403d450402409815103800e03074805001041c449a5040040e020281200e0520441c4a0135482c50031101e0325080380c3c5040e070414803000903245d010030000ca031682c41e0180c4000d101c2c2c0c44030310f0b0701c400003e00c2001001c641c05000605d0100c0b80700e5600b10b2403d071180d5500c03401b00030310040020030452441d81c1141c0c02001940d82c0054804525611040b56261500c0e8040701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 668330467 1250 668329217 668329223
    0x204050c030601021c020c0d111002030406021f1401030f02150426120a200a0f06050915090d12050403090303050c1f090b060a050609190315050103 65
    0x4200015102000d81000c50b8010b0324181d004007100004107500340c2d90388001d805201c08501840c4000c20003030369000300c4085102d01410081e110607445008020b4102c0070840e00c6002d5400034002040b91540106c0d0300c0e4020146c0c001e183c4030680301c04142400030140902c120003040191000401409044500028000d10907a8043c4001c00c608900c203a0600440c40b85281c180103020720b082c07200c0079816560003648079800840301c0044000c000b602e02c0d0f4225400380700004d2149038801c000518104041d01240c20101e0142c8000c00907900e40340c0c8200c145910141006480c2c1c2e012a995190401c508064000038090900039402c000409507100d01390440744600099a158410580080d079105550007941e01d900d0705100310745907580c140ca45400190110015001c0c03840d846900301a01030840703c0c10b410482c00001d100d022450f10200ca144d028045074089e16000300d0a01668980004440220b00222200f0259001003405038441e0350443d000100304040100f84c1e0a241041c54004034141d0388 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 668331717 1250 668330467 668330471
    0x40807030f06051e0a0903020f0102040905040c06050a02030f222d14010e01020f0a0b060429040b0a05040609020c0c180a02090a0302090907030309060201200c0a0b0408070204 77
    0x10382c82044d004465843c12840d5011507400c0c04540705100aa106848080c400c2c0181ea44019802d510642260042d60102c0d4145031120100000c001c0000703910805007425040c07903401c148003450000c0d9a400303034844044d0111380c00101050b41103058125092000c4155100200c82601c0f1541c9069107035001404284010003001ea40c203525810f0100c0c07206079050465001c00300603d0740c00449041103003c080d41e05500030018880500c000078842807000e02d008600561035801d005050000b210348281e0100d80100842c901d5019001c00c0b440c138681081303030454010a05078864400100107511a50082c1d510501c0c0c2600054040145d40207803000a007903209807080d0500c3c2400340850784030700400b00d00828500c180043c0c0c121075036601510340150b014041c002d02a840e680032030070300401a42c10720342d5580202810800c05034020803003005070940b88024404603030380d80401c84607191900c2d5075170881000803c0d400ca5031101080707038450b02d9410004950283c1040d0816120591100038241d0043e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 668332967 1250 668331717 668331721
    0x41a01060504080a060f02040816031a06100804050106090f2004030b010603021315110f0c1804050c030321010807060801180912050a0e0a030b1803040807030f0605 72
    0x15004005032003c543d403441c09002c1000855450b00d0050074245050845a0b40c01e11001c28042c40c1007110001e404a080f825809007821800c0a07031440741301c607080000340c2c09184c0800415440712401100c6c485178a0400010701e4445145c1980500350540254007154508000c081c3e41100380d401c0302981c101101540c26660700040200e000500c030301d00004d440e01c0f40c0030f00104000e900c00d038018000051304c4c405c00c0382500d0300e84025040446d07400203801f0000d40a4080003040307501c20320402d41c002c01140001c24010a6103004100002c0b0700b042d40f04148488000050300307000040c0100c590a1000805503aa9207010b040b001c07410401c04c070020502900c0504c00450702d44400100c9000707075046a1118000c0d6840c20043c10300145071101000c4050361030700d40810004841c1c184042c40642c42c2d4558948501c0c040c0d00c008e00e02c40c80051034a202e070152440c00c0001c81c18200c0f003076070050f4006c20f6440d0f4841c191801d4a2542c480c543c041002846040340000500280d82c8203141c10a101d40020b2041d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 668334217 1250 668332967 668332979
    0x20111040f03330b0111030c06060603130c0f06030e0609070603020a030e01051f08071a0f07240b030105130318031203090b06010309200d0f0b040302061e060411070b041a01 76
    0x80c0500c6542c8c4546500540102c3c0039071400b10302a503401032890450b403240c50465900c031002c111490303204061980050005201907901030094030029055800141400d14011402c1076840c012031180340d0a1640c001001d2039002e00c241c1005018104010080c482030034801c424043e5441c941180000303403c06600042070900b00450010116104c600c0e000e00b40d44070344074000f0640d511101d140090350388100256800140b0031148a0001c046101e401c412409014540c0e400f580c5141c40300c14401d901d00001c015107800c500c040c0180040d017518010040b040041c0d00d250b07230050690800f07049105905402d140042d41070300b0444880d845950100c40075200c0740010b4007a0b0303864640040070f00700b680d00e1021b0b220700011b01c0d00d28a001c0042c940020072043d03488900c1e98101056041c0d420300982c00c10882451303010002160410f40a08120382d081414829030080c003540940b4940c4515191081d40782c2c4141008251180b05420862204403401c1c50301d01140505c032100d001e1000011428000502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 668335467 1250 668334217 668334223
    0x607030b01110c0907030207060e06010512010e1203130c03060b01031b1e2003070b0c0f161109090105060901050102210310091b020111040f03330b0111 67
    0x514600004120f4814200200141808001c00b0f5070101a420700c43c3d040810070301e014402c02e07000c020b0080c1c2007030750425061040002e101500c0c02c0d001e03810007200341070269000500e101c1b04180000196144e80700c081320f203100d46141020107481c41c11804c0012050044551040c424050240c0301001300c030b4012501b5100c58205141c0840100307003803625071a0207820318207510201158918041d004404007440e000241000185071600c6d035400803d60108000070440070302e41008010024a06007240501e200d5018810b03140c00c9506024281440c40800200407080035900f440102000040e00c0c00100c607074000c2501301c50251003980e07400c0c0002a99400480d400345801e09140e040c049090440042c4419580058603010464400f03c0c8001005052403203030039103c1c00c0d5401040c4800d18040d900a080d43c0040c290508001020072080006118181c0b000c011658400c0d007002046102d04403420858200d07038107000441102c1050301803032810340c3c0e2124a100009885022840c2c19030909595 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 668336717 1250 668335467 668335487
    0x6080a0b0411040e0a1d2d030a0f030603060908120601030504030e0402250302070e0c03250e040603060b0a060e090f0612010908030a0e030a020703060f0e0703050607030b01 76
    0x2c020301c03041000380070000780481496480b421041c80890714090700e0085103692494942080002d070009405030902403582500403c06c2584448407803125404014403680320b10a490a40d07060212103145441000d010381c000500640d0404010003880c01a410110f90343c0d403080b41c3c005180d0700c4545c0043d8066000c1d20800e402a40c0607542c0f801c2c2c010035141844002c0d80800d10145000c2c4d035045844010052010300000240d21981c068071302149480c50600100c04c0c0a07040f0407030f040d4140100401c49003007200b240140040b40001c03850b10389150300d0690300810403800454025042120202c10303c00c250700f04035039400b01a00c2e414400d41d507900c821a00340c0714a110056001e50301d58040303030032203404180650300518014150703c01c1d200580b02e003500710303521400102e0305001c01000300403da0b422032244c840c0500b00c001c0a1490030f1144130000b91154082d000050855580380003841d070000ea20790059021034001c4003118003e5449080c196601c5508071260400079042000000f295486026029 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 668337967 1250 668336717 668336741
    0x100c09090203190f11031303020105090d0c030f03110310060806030111120606040b13050306060a030f120201110409050103110a0e070c06020d0222051905040b06040f06080a0b04 78
    0x114a1030300c55100002810545a400143c1a10345c9a40401c0000d04802980121140040030580c5e00d075519010f800c2d10401002000190803048902c0010741c1c202090034240d070351501d001c04000e60003140c1607004045607840c500a08402004210319104aa400f0f48166003140e00c40c4e814030383e1350b9800c15080c4c601c02c0340804101c40f011711101c014100c1c00140240c02c82e07801441c180c240381e10303003081000c65000000382502d01a8211000c01c00c1d41000d1100b260010401e42e17a0944030307811900c60201c1050743c440010205200c0815a0000b18400e601040c0d00310100500256500e03542ca13400c0002d4002800242e46030010050035541510300f040c03a21007210100004540c4650f0340c01d4041c2e911001c1301e202911015000c010711001c1c02c4007440204007d4107100003002807c600550284040d40d0075420090160398117080c2c10310010380b10000d41e81203a40440340416104140004112180202e51010720701c0300340e440700400d03415000728125100d00d44d031150401c00c0c215200d0400007a100d03040005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 668339217 1250 668337967 668337991
    0x71a01060507020a0b13120206040914011a04032109030506090d08060f010f05030c0409020f040623031b09060a02150a09020d031b0f0302030405010e010804020a120311100c09090203 80
    0x10041c1f0b18100c410285050b000074141410190b85241307150540e900c03161101052008500107011880e080042c1100001114011030b09050442e6038100030f03234050b823403a807011400302e0461088152007098140040c5a0202c2925082c1c20140c1400e40e0750340001000c10f000c241c1100c00505e1900b0501035048402905030750f101415981603800b91100c0c1d0000c2c0c10031078841c908100100da21407107400140400c5407200480b40d511032518500030700038501d4446c83e1071f80b010200900028407820401b62900070f41d507810f45810f07184e540e59147c0305600c5a0310420340c0004022035080c8102c3c1e0007080d0203400c11250040c41d40b4580c1c40c48121403c031608101c0080d03010010710800d00200c0c0c0f0035007150f5050300005000c0c865a032600d032181d02d090702810804a0052340002014021540c1c0903941c03038040042801c0c48481824541d001441e2404140208450198084101e509052241501c031011400d1030040d94031000b40312408070003400301e40d104440850802000003812400e903108403032060000007a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 668340467 1250 668339217 668339219
    0x103020603090712051f05100e15130203070e03070f0e0a060b0d0e0c01030e030d090512030411090633040801060e0109050a050603070605071a01060507020a0b13 71
    0xc1005a401c09054030b0581c0c816a0700200d07400e03c2040f0144481d60060700144043c8848075003102c100d1031184505c907002c500300014050820000740c0d800080d5403070011041200e9844401c070021000f1148180c0383c1c030a19681c91010900056802507020b80d410780d41d2503c0c0040900145699081c8a04c02c3e0380034940c12401c100034680c0703080007468000700040008203503941c0e10f00f0000c01641108503001d101982e98500303091100403c020b8007900303002c00c2c20103004c55850701c1c1d051a00c80c041c0c40400c0318203989a6582d2804c10030b06100c4409419907140e08140c5074281400d209501c0d8082e29046805110601c000c40c406241801c0c031095125810344190b5a5000c4014444d07503050b04007002800c40d40c8c4107000c00303d416078080c01001302038091002031854562401c022031050762000340c25050035074502002c7c004603890100d4030a0aa0f8040e0034066a528182d00c1d018218a807030b4030460094510380e20001c80c0c0c065010006040103402128400d0115440c2e0715801c0162142201d151849048400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 668341717 1250 668340467 668340469
    0x1403060903270918010b0418030e030703020616060609050606072901140f04090305070f03050c0106170d020c0a050f1207080106080f06060a090b030c0d060213120b010302 75
    0x140b04002c402d102000941d4914400000ca4581102a244d642a800502e40408241c500c240305140c00b54400312000d120b001400344002c4074019002c3e9004c2c003008581c40c11080682c038100814402075a001d04015591464102c14824415520504847d05805d0070030005405945008a60048070014607040c900b00319030380c0d0704c0e407240d907103241885a0440003164103200e1120310b0600c5000b40011115443c810140380104a048210040094402d44c40c010444020940c00300030366117a142e10402c803100c2c06010742000e485a01035140e007000c240d070804001003201107103030012694122003501150704400c4001026038030f500c0c81c076030303503070b411034103c4c6020400c6192101d0380c003420f00c2e005450b10307a06040b02c40c1c4c402c0c14000e01d50458516a9124141000341000820a541140d000342010f0180d41c00c000e00001d601000c2c5109907a03c003919207a0501c0160b0b021b10000001b01002040790160245e01e280c917001942003181079401040811748001074030b40a80850300322b841c2d070029101c2001d80c01c41e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 668342967 1250 668341717 668341747
    0xb090d0f0204290102061003060b010c050703291501050f092d10210e0a05060a0f0e0a0f1a010602070812090f0f010201020c12041403060903 62
    0x48420354414100c2056480541c69610401c080700070035914400e90035801d1805603a4902c0c05100031811940450108004e51000c442c0300016654001400f01c1c1310301e035450040b10b114285440152880c001c40400204100c0c0305000b20300a609400f60b00d02d000510b040d40342d01e8050f4101d0304140c0084600502c2e0307101c1d600c1800140501003222603014244003040700442c00030f00341035410341d59050110040d010012501c060660310742004891a80f041030a040004001c034001c0c120101d4610407000e00c8400c4245603410007840b155802d821a80a0092030812558a040c1a6095900c075841d0a10421a8003070700e0146080c4040782d075000300500c000036a41c07100b15660340c8400343c0706042482c08000d10360044181c524000e040c598001e020081c10200d0036030800c845103804000d43e04040080b01e055840b900c1801441c5681120b9441c840c0241c840142c1c00380c410151514410301030002d4501d815800480904103070745a104130808910380020500d035550304151040c8030a607009001841c45640d8130 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 668344217 1250 668342967 668342989
    0xd030201020d09080c0636030405181f050127090c02100b03010b1f090b0a05250203060f190504061b0c0809280801061e0b09 55
    0x248001464107a1050154088400300241110130010024145001620400c25990400d1a0b401e4203440074400342c4c0d01d12441c4d100309001291951104241e1240c044003030050390018400a016500c1d101d2154845100c2d028045441c03a040302c1c081c01e1090143d018007004c6806079001a100c50b00b4070b4183c8030024555800000f98010180c18982c00840c200304e00d80033705614044039400601c080c40d410084141078038500441c2c140242c2c940000a595640c0e84070705404a0300301440700712a00d440e40042190001003d0f0021010504001260400c0507441001081200d5209082c4042075610390000c51340f00c4000100070f03616500000101e07225801858034190409540030742207100c0c900708a00c1b80250390085405698040d66905005c00c480880f000850200c02e80f071500c080195842d079200a0365000700000d8901501807038086141c51058014082d41800d40301000c600c0040d95103440324007800e041d001c0d10400305130050f4102d503504408400031040da09804419801c0020701000d01040440c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 668345323 1106 668344217 668344223
    0x609060a0b0d060e010219021c020f1509150f0a11120a02090316030f05010e0d020a020f1305040f061805060604050612060f0a2007020d 60
    0x20300c0c640355902c1c0703a00420000304141e81c8039541e030080c02150500056085a0350014007403540025906d007a01e0940004000a074005040c1280c80718841c5001c014254070006809641c9005005034035270043d100b00441c0d00c42155120400e102c503009030b82e440750311941c11040c0170b00890036001e003982c807030115881146400210380100210490091444148950200340c50600343c1d0280034424240e41002108410303a500c074100540c0b01c3d03e00400445880d0701c0d01c0c000030250100421207544400c2c4a40242841f40c08907000c0c040c1d4102840c0d00207030f1100301c980f03560048541c80c0c418640201c4c0a400e00b9150030006240480c03c03603c2841c188180d01040401500005100061081d44232000752000b03d61601c2e044041150304006504440450080104010800105450440c800e50b2a1041888015a61070094145417520300892540c0e55040000310050b0510718000c100c8144 = true := by decide +kernel

theorem cover : BRFrame.Cov 668165467 668345323 := by
  have h0 := BRFrame.cov_init 668165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 668165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 668165467 ≤ n) (h2 : n < 668345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
