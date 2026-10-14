-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2629
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:16:25.748684+00:00
-- url     : https://prove2.me/submissions/09eaa157-923c-4d44-a092-42eff37c82c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 472661870 ≤ n < 472841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 472663120 1250 472661870 472661881
    0x173004030f02010c1b0f060207030201020306190f050405042f120105090a0b04031107080c010e03010c080a0b030f0114150102070b07061a0402180109120b01050d0602091f08010e 78
    0xd4141e000410b0083c0e0485d16010a41000398001044907400b0f02003a00015411051640540003580194419105607403e514145100846102c25001765400d10400c0e1100300841d282540115800034010603550b104404140705800400380000c0f00122086841040b840c658540800c1441401c07404100900151a00080d600d40340c2144400042000b04120b0108050500c03404500405484000032a5140c1c1d44031420590344502e04091140001c1403203050308600d040601403403101c0c4510343c85243c0c00351107a50f084030103404c5011006405d4030410b054044000c03024000c0100541000020080c1818201030302c1c0d81804554860a040d0740c854101003220a03e81c000301c6407410780051000518800b03186035000c00e184454a899802030010449841b98810314a0340d05848100740c0b42e41052982d140c0080b012004a802d0140c07044662a00400441c2002c0800401803031040c1d00052030311594000080065140c184940b8414880e007159845094001ca502800f4100741c10498480d441c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 472664370 1250 472663120 472663127
    0x105030c04090f1202010e1b131a09061302070312060806040302031207050702040518010c0e2413032001030615030e01090203030c10110304173004030f02010c 70
    0xf50540180401c0326540f414000314401e52001241c1c5218034143c1d0280b10007140e4000720840d000c0c40c814850105441450319504181c45000c04000c48410841401d8003c00208511444000c01ca65041149900180c1071480300344000e2011511a442e0b061015000e0003d400c00c45030690040552607001509001c0881e400009813017040c80c4516003424075507104101210180031f40300300203401c42d0410b004d1049204203100141a2109540000c0021590210040350400d201a14032508561960182c0020341c14200718a0692035810039124a46030340c940750110074039070303e90003520a0302c101000b0304603418000006040401c42440c081c800e4604000380c0c000c43c0102d1a00040038180d03a141911b02068080d0008101ca680080680e030b103600001c2c811a890760802d1a410350802e2420740313243e001000c8001034a0240303421802c860480c00d48051074986c1548600101082c6c1e86010040142000c050781e011074260340410a58102820039250150400765a60344200c02d6905220007426410390 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 472665620 1250 472664370 472664393
    0x50601030b0a090204021801021b0a05100302071205071203090c0e0402122a0d0503070828020703170702090a0c0c05160f0806070206070815030a0b0105030c0409 71
    0x10842030800042d00c078040094001e125200e40250442d0020032109040384084181d41031002e0700303800f0b558020518048030501e50107040300296106840c200248454107101d91407141058880c2001860000036031540584085513004403400500002482c1e000c12642004d0590082410305003808601c1c0e1302c0d6a8850ba444541c00303103144242c4880000760a56a0f900800c000c80726241c030942d00303072101d0401002883c162a81c240312a025070400030b0401c0f070410103904200d10303800c14055810071050356140a1540c1c8203880320500c2c480c1c10203d1101500d131161b40c1c0715502c1980d4004208003440c51405104810030004503441f440d0082c0241c20160f00c80013306a4040c0500c0340000b440070201c0c2c0c003030b603104506200c080c005d8072619810100e50343c2c00000480c103a5490564809001d0f81e58074429039200412222500140c000d41c011502c014005d002150b0000035180140300e104000c00042440e00b07842400559003000e08000420181c24140041d40320480c09880900c164100380e180d0841c1c604 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 472666870 1250 472665620 472665623
    0x30f0412050a120f1409061005031504020d08091e1e0d141903030e060c040b1b0c0603090d030608010b01050a050706020405041d0708030304150b1f02030d150305060103 74
    0x980316542c5004c250b4255110340d108902c004120031040c203113151400d54a03401260702011400e589400800c00d0303c6e002072184080c0035a004024140e03502e03a4240461a081017504845031013042c0a41d82040d40e885003888144400001c0c000b403207254060070031460148008040c206c000720002420040c0d16030329040e0a0080e08100054039100381407031030078a410324116460b2242080300307030801c0030194075810101001074481c0455203652510344141602d4881e511500100c143c08100719100d281c03880000d03029045000042d160146ca25501144d100c0d80111482c050325001504550000c0b5050312820000e000c07050020400c0301c14880c0041d00d14412400d0360402d12002062090809c152a0120307406804040c105119044e036101004c03050280104140d2000d002e444008102c100000054a00c0b41e500b05010143d45031482000b44000c01c5943ca1407030300029824207072400e190f0072803171880250805500031503a44141c400700508441034040c030800903504142007040440c50006601d81581e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 472668120 1250 472666870 472666907
    0xd08011a03060102150705040504110406081b0408070321030606020309060c101d060a0908031611060405030c010605060702130e0703120e041419020a020c030102030f0412050a 77
    0x1d49075100145d01d4407240c014507244090600301000101c076846000f5200b290f80980b030070b100e402c6510074184120b00480c0a040e0019250b10006007001c0c0308103038981c92203408080c40919054842d4202410009503410175244100354412444101030b4603100726a028000d481d0401c901410440c0094403442070700e82c03042c8948404904007622402c203200c0d4070202a9105001c0001d60034658540f1203406006c4141c0f002ca00607a400a0700864080c025404060390000e040e40c0380d80d8520880040307080c80311044100700401800746010f03801c42004083e0240303025400964403080808007540c00e40300300d5080b03640100c40500214006131a81108500c601214407404039014590036900303450243c2070ba1024050034a02190316503c2034008400c0201c60406842c05e002803500700e001c80b8504107081c0c900b28020070034081c500d440842107a0207010310f45080e01c182c600c07122a000c006820781e00243c5556018020a4050000304191000f80001c400040d080160410f01c0742e144c0508410001485403015 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 472669370 1250 472668120 472668127
    0x702010e10110106080a21120c030b0907110709020702010c06020315150706050c071509020118030c090506040b0a06030e15070302120a0e03040308090a09020f07050d08011a 76
    0x6141c01031a0303108207614150300030082d8680d0745d1421617840700d42450960f0b115241410342c518031f8000c1c6c41c2c0910420144d07282d5041004103460360000401520f00c11008255449180884556a1160b0385006040583e81c07070310703125400040341c0d0134180070341e01042085104004080060340c004a00b10501c9802c002d0040c1c882d40d912141010000d550122160700c0708003002d07186212026107024080140c06140c0400c120b98980c08074104601c120080541080280c0b24a0b40308100c2d80e400502450344185064462280c5034151101640b441e0740003103030760381740e001402d000b0b002c3c451086070741c030000440d420700888040314082501c5942e6400740f0000c2544030403856001000c00c10842e0104010030000105524100c0c1d0024005c3d0005010004c41d2064403000c6403096510340103000b40710444c1d50140d458945581e40c1c01c045a80188035003504110064000a0200c0d007610161140c90300c0c9141050340c031070b504d2510700d041c20045907852083c000010010f010300008032039888035445485000710382d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 472670620 1250 472669370 472669399
    0x30705031207020d020a03050d0306080712200306010605040914060a03120525020f030609030a0e0406091d1e0304030f0206070212010b010f140919081618020702010e 73
    0x54480744d2803001c0c2d00324035280700020030402c00040e280004020303980d0801010344c60320042038640c940b0707105010442c0b00c5c9803408004500c10090050403241080c0c0701030840c030b407400003007401c0941c245d03c40c0c0c0120320081004c1000100c140181400c100e07800102030f03140d00d80b480c0002c0844280340009400161424119242c56019904581e5101d201030840411400418050700191210b188120302a00f0109182200f50a000500901882080015505080407200111010405140b08507401034a40800084807245849036451005e0a99000f60741d03002c0c80780d0400c1c60003451000c07021060071113540c51001e815011003a282034a0f4000e0340c1c4559a1010700014409015405001e544511060412000d40e481580410b00c421000c2e21000440e43c54500b0a40342d03042c0c08016500501006c100441052078200e40410102c96628988841107444124a5142100313820062040c00701c0c410f000d10944a42e5a45206400c04043c07003945000242e0b4002050980100030450103240d1419503000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 472671870 1250 472670620 472670629
    0xe010203040807450b0a0e0a06030611190302032805161b0b09070f08010e011b051602011b111503010303080f0c070b0106050a0e03070503120702 64
    0x1d000304001011954804c1e00ca903044050416040a180c0d0300b004d080c40c0e5800e01c1040444502442d00c41503020b516801040120a000350a00c0c440f255400400c0b0003000c5a0b0744c000c10801d500a00d040100050414110f1422008031030001144008036001404118501c1102c2406051011102e19016899841d174060110390341c4143c3c01640710a0f042000c4414081c02280c5c0554800c0300e10010392244000403000c2665004890030114580130111000039011501c04c1e818540c00c4201d400407214a5507a4440e00540d0b98000e030483d44c43c0d44d4607014401d0b0200401d0254591400200074603403000744819001510710701c038012049020080085003502035a02078960049000707180c910718010001c2602c1d0014403000943c141c3c5115920300c04003096048418010f4034140e030703416240c00d2015291100d1100788ac0c0ca0040c010346c5001820403180f400a000d22122074000c0c1541d84802c0d469185100010307140340710496085000e0750206070108a1541c0000c0d11511310500e00d0150307580c4404034004034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 472673120 1250 472671870 472671877
    0x131704090203070c05061005010c0b090304090221060f010c20040e010209011d1011190c0e0601080c18011101150512010612060b1305090705040f0612030e010203 71
    0xd000a00c0481005143c5030000f00080580d0310540c16241c0642e01e4031103266411100c0d02801d4001883d004034840011840c42803280c201c062035041381d003055500c001c3d5905aa0014400080c5d00c000c2081103c810344004856940100007101c928000c200301ca80000c0c14000f24803000f034803081c0325804641540400110704428520042d209006404c1007000340d41c00f0354441902240040e8600002115250102c0c58030304400400400215082105030f0044030010100d02010400e4060f1454041403195030010758410588181d1400529502d0070340c00010b4042d00401850520081c0e0301040580d2a042080f1f5407c004480c4501c8210b103503000040301e160b09400200a159803900b00c501e604000c0ca0341500d070807540c048440c1c2c1e028840c0341e02d4203401c1e102c6620400c407150201c1c9100fa4005506508141012100034102d07803501034502411005484094520206541049105002c18205801080c0b500340303400c20b06021031480c02850f0a24600e600c94040d0030400c0e96580a186a8400d0044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 472674370 1250 472673120 472673129
    0x5120c0312180d210905060a030203041a0a0b0406080307020102101a060c030309060601023d020316020607020f06060d1407170c01110d08040206041d0405060a05131704 74
    0x2410300302454510600b25804003c9070540c0000307904c419105100310154016604090503150a1040303241c0203a000e03401c050411030342101d01104c05c0d481950700c480424803e41c041034003c612000340703a00303101c103d802542010101d9041000b005015036000a4a0000007214182c0002d50240d90300e544850701010400e5580d101c9400100340c80d100e04000b000d1401201d50109035651510781d4401680e1700c140841003081074403070043d446a48030070960401140c00c800c03208103010380c0c0c403880c0100c01246d004640e0a59008818034400c6002a410001c5a6000a040c00106540400196004e980e203400030013040c480c2d0f00e0b00c44608104041c2c88a0a26500c8110040381c541607103030090b9242180d108241ca10041c13180e0308806035558402e0040c4015000720300d02a20a51001c1881160044e000510070f98200c8000c100c000740032031711a0322220001e60040d54000072030400b03250003418258068258103209043c4011b12240c0400301049451096005911317104215901c8009882406903910 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 472675620 1250 472674370 472674379
    0x60f231b0d06050907050720030a060603120207060e030c0603130605241905061806030a0c03060b04030c050d03030608070b070b071706040f020405031605120c031218 73
    0x40303207200162550000c00555400700d44144055032a904100c2d800e028440c5e001d42180c4030068500101455010030050800b405800e03a01444159281c0c0c1d010303580350368021034586041c4502e102c1314580c14080640680354500d13090200c0c040d4900001d681c1e1900b0900035100da04000081541c40d034003417850101666104000348900e03d001c103c022544040b1752000182000a00b64a11407441c201c0d107142543c1d4107010f40030001c00c0c184801d10036281c00c00440c0d4250b0840c500038040c007c2d62000091803280002c4240031030304c564045c1d0000c055510940c849280080207000c2403002031180c1c0d0b000815103100f030302c40c010142c00a0600320042c00685d0b000100601a5540125502001a0081602c20301803041c3d894140c079038a00840d50b01240030007580c0341d02041400f040081c945900401d9044800c40000f5042c036403500002420140411400d14030b14100d20710411a03424441c0b00221940818406050300d5545640469100c4c0c0302190880761740f41002814581130b00b81c0340e2005201d82405031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 472676870 1250 472675620 472675627
    0x1504050d090b0903060f0601050706090b01090b030a0807080307090e042003030c060402150d0f0905010b0312030718090c02010c080105190e0702031e07060f231b 71
    0x10100d885158491005001802000d00880e2509400c4102d070100e00001c4c0090100e513403043c48000c0c0c02d20001e00b0480c1040810025140465aa4029041500e020b4003a980c0103525004030481102d920034100c43c00382c0c000908a00c04608164190703040517030400c080300d5580c0c0d994001160320922a4105d4400120f0400601080c800b107103104607480c1c06103c81c4802c0103000c840c209603690042001e044116405a000a0014207040c42510480c00c0c50071a800e0822607149400000e80b4034982e0000011740c0e5440c854005d0100034002e0340c100032000c0d005080038a40241007080d162000802100078016803c07500c80305120301c44111001005801e10400480805880c000d02810b80340d01d0000009168400216003454140d2380b111031b203075200d14481c0040746481640000e000b0f0007400341080d4001480070321034411542680382c03e0320503040040c80d658122890250111703240ba5001140c4a0320b0440c540031b0306107004010905040e82c10314241d016540d0140f2007a110074070314201c103174142c1020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 472678120 1250 472676870 472676873
    0xd02030403030e09090d03110904020c0a1a0403170417031e1b0d0b12060f040b090d09062d050c060105030118080c120f07030e04060b0a050c1504 64
    0x2101900a4a200760340d15202002d11604121400800b03861065840d0003d000032069140658412202841c1c518407846c20700820380001400c0b03801095540003035400c480540002c00030400c6842c00c06030306518017000c0908040e1402800418619203050b041c0f0b11260204041c00700068040c0d000e600700c850710598901d1704908a511880c11603d080044402c504080f8110b10b04224201c2600d403140002241080c1c0b5100f1800040c05120000340d0700103110301c1400c200200c05208462244c3e289010300070003810141382c94942510028080c0d00c02c0c0d00061402503440c0c0e0303c40c030002c044400b680383c8081da414841c0108810010040300e5910414060080090440c0c0c20401800c000880d100c00e88403280e0b41c940a042c265100701d08103a441803080411100081d280d100a8601d02c400720088807100300c00840383c10160f5001007044075600030301080356410540d0220300c642c420502540d062200b03e00e0706e501c111550080d01405018082c010550200c42e076401c004840b4507500002c10003110381401d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 472679370 1250 472678120 472678123
    0xb090c271612150506030925060c240507091409130201030207080409020a0215160c060e010209030a06021e040609050603060d050307060c080108070f03060209060c0d02 74
    0xa2051059010540c40054001e01c80c550020658036556103401c400c904071081803800030403100c410000a1030640e000450b041d2a0400654481e01d070040080000c07105083c031264818200c5401d0a190701100b0109000040e0300c500038002855202c291740c9501200c00d103a18407029041c0600c0b440061800b41044503182d4000101d0048a50343c0c91090550400c4c403051001600c0112078074000c2d12601d03003003440107512a40c028030322140245125824aa100c000901c1660b02c03200450b80140d002d4007401c0c0700c401095840542003240e00d204032620580409001d042001d108501800301681c90031541c10124003901150001304000702610080784007454040002c1d0000ca4409003802c0c4810455550320190000300d07000c1d20520b4581c141054a0700f81005100d0f8001859950007510501c07070000011001c1018003400d6200b4034000c00c5030307280c008006041400503403140c045a4410706081100108100e00b070b0007902c0e00300c1e10160b900c106500c04100288910f49210411344203214448201030790 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 472680620 1250 472679370 472679419
    0x4060b040c1d0a0b1c180507050103050f1302010c11030d12060807060c11040204090501090207113109020603130b0c18060903120408010c020111070c030b090c 70
    0x2440c0ba80a10030004010611084000a003e01104500200b00d0b00480007103603c4c100842d545030b200c011507450a8600c41100350140a036003150241c0c04a01c050240b50303014054181e0148a0448030085460902200d0002c01030886001c2d050007003007040c41d81881034000c411481c408000d02186c81044060304001d00b00e50410380818241ea2401d400070481201c003241c0c4200f22040d6980d0340f00742141c141c850140880c050707100290311683c2080001a42c04076402002c1c0201442500144c80d02094146000c0ba00481e250321072040c02c82280250b01c3d0410b0040030102c044051006400955401c0e6807c80140340110001e588284003000300030018503a1112034000c60f00c540072140403921003000745031089c042d0642c80400001140400222410300c0300240c000d03c000241255080c03620914421000d07402600415800e07511101c4002d03416409018004400400301141c9281446a07152212000c0c07903408010030071442c04006c10b01c0c8840401010b00e100c81d00400025001000e013202440c100c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 472681870 1250 472680620 472680647
    0x7021c0242070203070b0d06091802120c21030912030310080106140105071b090209011106010b090d02030304080d0302030103140c0a0e0a06170c041103090a0b04060b040c 75
    0x31040341074812212000c0c1600c012541c083c00400146013448600d981e50303002440e04504c0d580e0f840d600002c6d904414040c01800c400c4241e040e4501401e24010300040002004a456466004c105010303c03036154012001a0038200c81e40c0041d0700240d40d8200350440c4507840303000d94880248a004201440084000e5011b001507420601d0b10541e2020040d003651154403648490b040354407181c1c00310354024402440c1e083c3c400c1c0c80700b54500d81c2203445061442c2840d00a0180c1c20341c082003901155800c0140350820f1920503004015941c07501c4c514060612405591602035110f04440c80d0464800304180c401501d102010345030407451821005000350001d200a0f80e41400725091452400004203180440300c001620400d5034074100901c10129000c09400801c440c1c0c0c0e20680066034004c2d804000c10300500340d901070580c84c01410200700660f43d01c0010b2a1a804082050040c29080010083c600c50f46c000e40480155444d403c0c40d83c010f111640e61282c0050825041060007940700d048401001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 472683120 1250 472681870 472681969
    0x8010b0a030e0a051b1005040e040c0302090405060a050c0c190816030c06110a020604060b0a0f230f0d03080c2704060608060a2904171207021c02 64
    0x401c5c0c1c010018405007121040d00487c50800c0b0034001e52003410b000076801030181440744c45495580d4085a00584121000c0e070742600140144401c03071180d4081c41c0d030030540308511542070103410300c02651a203090240d0311a482c050442da100c104589441075848480030b84200e0504a8001d050150071001d100c4070448074185840105c000c0e04041d80f0030380318140070640c01001e0b15a25552071340c0040c040d40342e807070740d1100c000072002440070400060b44001d05041c06040310100c50f01075681190340f24000d24503204190b001c00d003a01681718110395542898041c40d102a05171100c014008942c4198504050103400205005c0300007114a07000e400440000e40b810020f5a585803c2180c12841c01d4036000d6000c600300204200f95040c401d085612050094040002500c000c10340e01081d0740b040d84980224580e00311900240d880500072415002d100d41005490f0a40960005540502c024620300a208404d142c1009548440d80e00080c0d202a4502c03400c00001d034003401c2042010041c0f460000c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 472684370 1250 472683120 472683163
    0x112508010e03031003030804020a0806280c05031b040b0714061e012310090f0f08120c0319031a010908060601050a0c0606122108010b0a030e0a05 64
    0x12801c0002228030603501031180c100c030b0078110b540403104450003030001e036405800c449001c509c40c5000d01100b40500a640300081070101d0300e84016068059580030740d8000c0d0310704240c070000789410508584c2e214900440d100b50300c4210203040700403401140c200030b10140007c1089010410f000e03403403041c8185178504607080356403840701d500303582c0c100104182e55103441e41d801040b241d5407455001d25102c0003880000300b01e051910100b01100000703204032002a0065004110448100c0c000c80090810510703915022810651060368039103031200841503140b400039650019410500075070f00c1d03500241140280088030341500a001c1d140e404400003c1051200780c1c241d01c4c1d0300901800c0c0840e0f00b40b45c00382c42550b44500041d1229004012a00d06101088407404001040340c07154401a2424004407400f408842c00d0526110888514031203466940540c0ea084017904140d11a044400320610741d1342c5c1344581d81c0c0440280071046401e68880c030a81c0026030400001061300e540181c0700d05c075032841 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 472685620 1250 472684370 472684391
    0x7020705150c1c030e0114040b0c07080909040201090e070c0c0f0f0e0c04030804081501050d0b0f0c0c030f04140f01080a181226100611250801 63
    0x100d100340707000b0402e16405210014070041d84842c2e41c0f84201c4007800d0002c1c0700c0c007440d2040b50035900c801c00c04220420000082008011950f0b44190700410b11241407403d1109a5480407200e00c01d0440d002d1040a202d40064110ba1084000d60082c00e060702888086041000e8007404030b01000401704d83d1021541c1c0b0115801804507074080440c0c00303d040c0100c1441c40d151601503d0580600100c00d800c20800011000c01c03103090080c00102403a4009046030f08401c80c85d8850f581060304840d100e80c4441c0c4200c030103e034503108515007000c0c401c02c2440c1942c8548814102e00d216441420207036001c0419000e10000d8004c001c3c1003101c40c403001460500065000300002a0140c1d40040c0c0401c034070001103044244980e000440d85081481c2c403030740d00001070711061014150825040c0003d00041c0003002100038040300540307015030000072501039082c9102c009206035454000c400c10002c07440e040507401341042000c5188100c24030496040f04280c00344c040110308640c041c0d8481982041c42c186d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 472686870 1250 472685620 472685659
    0x4180b041a0c040306020c0f0f07030b0a110403020418021306060e0d030819020913060302010f030e0d141b0a03080907060206070c03030b13020301050f0603040807021903060507020705 81
    0x10301c00e0020480b4146000e0540d51024029044132031409400e204074039003900d8a2000b0001130106a03049001010294a945003241409070010411240142080ba003100c0080c074501c240e4083e0307603046801168051540303020783e48080144d0710280d44402c14801c0004400c0d070b070350300c000d06540055603200c00c11500b03101801101015084021700140003140081d042c80c004241d000e0b00c82c001c21801500e811405000030f0302044900340c00c240c4540e5a10700800031980c00c184850782611441c01c00317100b6000076000c80c0d0740302c4250300041801d00400c0c1140400c041f44440490310180761300600055003079820703441c0c00d80d01c0013508012030209150034046203c101c400104142200c0036580180314641c1d8541040f9030580000a0880070300d030311100880206d82e00c0d580c0000030499a4400140c40758034080c1001264074090f89800c2c01100d0810911011500c007100721071351940c06131144944440003900c603944441c844c0d44040e04240c5003105101c20a076001c2150300844400701c4e07643c4641401e040b103c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 472688120 1250 472686870 472686923
    0x1e030503090d050a0b04051507021b1903080d06080622030e0a08060a290105070206030c1306050316050c0a0f020604150c0215030702060c030604180b04 67
    0x50216030041c040c80c0c08500e010406202c0c076034400c030700b5070f014072556540f0140e140340161030494550b00000842c044e00a000c042640c3d10158070310003030442c80c00c00d100b51080e140300000c00d40c1c0600d4904040440c1c2072015100c04004540c4030303d0300c42d0384010460450004000b14000c4a5944c00b408011801846440303846800200340f11448400b10162681d05840ca05c030f5213100315411000800c1c000491400501000d44200e130048408103028071488c0c3e141ca0240c04001c0100c4030194285010001a644002a81c00903039042c0e904d503540c1c1c1c0320581e00b10068014a030014040d03141d03126002c140f86a0020155000b00c0511341203005041e42071034143c4a030300620044004544c424455100420035100403000b6440c00a4140e03840c0c40d031108000c100d0220400b940341d02089400e40500d046040480003048407603aa804a075045040040b0001d44490002c2c19001010304042302003070321551a944070a204040304141145031044030301e054103189108580a445529450890103c042034000d41c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 472689370 1250 472688120 472688123
    0x6050702090109050403021911030f24130f05030a02070608130b040609060e0a0309050a08031603031803080711012a020a0f050304181406010f0e0301151e03 69
    0x120403840e0f08000e810340c01007400800640c00c40c442c00c404005d00b164a1810581c0d200d0040c0306c0035455107140790905280c800a6405110507034040c4a100c0040034003e181030009960020003800c0503140c00c0e00b00b605c80140c1110203081d075a503004001041003400030080c840003034070b60250391425603035840275695180d0441d603070034a94145007062030010b2100c01702168014420000042d920740740d5100e00d000c803a000e800341c034110f51104101500b8581c112503d0001440c08640000d541401d284419481e0700030f44400e99030001021480c0720406000c2e4000811000c01d03140e074482d441c1c1060400604000c0281c403c0c44c0484c003500725100c800c0c0301c1801034800a41c4440705016a9100c40d56400884005048040086005520030b000029008041301c07020940a01c000359120707410002008140d030540c8200d256903910b4950880442c940c1d03990f1741c540c01a02400c0000328628126000d58807640b050091a601d9440c040d00899502c5000541c03e069a400300d00b260080b140c0010070b020000100e010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 472690620 1250 472689370 472689379
    0x601171606091a0714030309070905160c030207081c0f0507052116060b010e03070e0114210709270b060d050a030509090a05010608190b0307080f01050106050702 71
    0x2d110160f820003a00700300260710800149400c810380c403449101050840c1c0741d0415000002480801c0804024190141626171010480e43c14040c0c070744543d0300c0000400400340040644d005040c1402407041c0401451150291100c03218034003400310580170090800360101d1203400880440900c508152541e441c1d206008090b20109240b000d19a0312080c1400903190904000602803078006591400c0c40c648a0710020601540c001f0001d885c0f44000280c80e070003039000010800501e111421401d04441c100c3d0b26a0b50401404808201c039045034520a00000c41c03407100b10008541c000074002c04441e00c104013007181010b8a00c80314808000001449000c44c4040844d03008038281400f555000700c0018003688501c452943d03001e003054907000042e8040744002c6401d01a40c01c01e00784030303903224421040401196042038030160603144007400105603800c009410701240c11840d4880aa0050014203e034100c9a131540b1840c2e44d21204110001c99508050000458a001d8000d4078041030b030051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 472691870 1250 472690620 472690637
    0x50901120803180f030a0314060405100e0a0f29010503090304050105032e060306050910170a1e0302150f040807030c02190302040b010807021b120601171606 69
    0x26409a22800f0340315641c0c2c0078004c050044005442c20002840003070703107075200410080c0054000c241c0c0c50b030004210070b02a034105010070681030f21010340d043c19110a2a000d54032503c4a220180c001c00001c038460001078a01a10002035007080d1403261108000c07200410b56251805004550502081d203c1c440554418030041c0507541c000c1001c0d50b80708094103c1e419020318110000aa0009a26050f100140c1c07d000300f489807560500034000907000980700e503240c42c1030048410810700b1240c4500d100d158030046024042c05401d002c0341d50394a800c03030039108031005400180300c85040800300450140c8900d21590707603000200560b940c4103007505642c0d513015a0781d0352501600c551089008408100c0c043c1110401692000038985500b80380300f265829090861051008079100820751724140240c240030008850340c00a46949082e4403088170f1500d184011001c1000107486203941a0f1070b008250000c1110504025002ca20341c04100c05c981082201c1d1341995031410103802280d00060301d61 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 472693120 1250 472691870 472691881
    0x10905040b1917101e090f0f081b0601140d1a150a05040902030c04111606051f0b091e030d020a0b100b0d0c020a080d020301050901120803 61
    0x7a407000340c5042002c1c1409078408562140d05440c0d500541004006034030440c040c54010004002d548130805018404201d5800045180512002c20742421007000b5160411402000150440041034076801098420f40c1d80f44d030326017900541c10403600c107018480c064400b400400000110b0b40c0c100c604824864104100c01401e0161100201d0001d440d203503000d803540140d02d840141094401c3c10449000c40100a40100b002140c440c3c0741d00192049080c1a00080566004240e450f403540080703900007a0015000034800e5140502c0c00100410b1400302095824000b2a8012500c40c1070a0303100d68244500d44030440f0a840c1c054011009500000d100301030417400c18071581c1d0030000b20221a2402c0b065280700103440c081c4554200801604000c00080800200302205070b004007507425401c3d985070410f090924580290703850803001640718002d0b041d41c20f0092110301b010640020100390384181e0800d05030302135070081c46070f14060340c4c0300000001c40422101400340225480308580b861034849 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 472694370 1250 472693120 472693129
    0x3120b0d2f0a090603020f180f15042d05040f0f0503040f120203010e06070f030b0609030111190203070803040b060f2805030a0206091009030c031a0601030902010905 73
    0x718004180e40110486009549554000d05080104404035000c42c00301e081d071046c000c200c207004410500030150300242520100b8031400081c0d0060a4402c0e143d2103980b1606448070315950011041d401c24036110800440b50020a026a4040406088503c0c3d0400d0a081e8000329402110090a0071019030f00c0c100000d03d03803440c3da0519500640440342010707128035028040d959950700c030100c0814180d84074400c5050038028092070f0140d100140c41d00d032811400c050a00c5042c000000304069642a650b45503a582ca029601c2040300a002000300c0b41d58803800b100b09500001c840c40300341c03000e07800c201c070490f200000321095964006001800d50701e455490095040b80a0031165008000b410101c41a0701d544100700c202585030404410b00315081a040b003080c110075003009001e50002001c80700940c5400080f04c60035101034480314002c1401200c120307180d4085810040821444034000000d0200c0b03c446445102d43d01160885252602c0300103504442003184000e0114076812010091441d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 472695620 1250 472694370 472694423
    0x312020c150c030f1b03031005040f060e06060d0e06010906061403070e1509090a020d060e010e061011010f0603171201090c0201060b37080114040b03030703120b0d 72
    0x803165a60b85a8403142c0b660458008880039502c080280d07008200034072b058024180c2c01e502d6410208101801c0101c0103020a0000704231a001e102d0004041c40d10308000d03400b074514a0421002c0c0e60484d40c6610360304026184511070b000000ea4020501c44e5540c19031001c580c0129802d48502d00308a1030041484601c420b51640148800750a00000b40c6035208d88072800e206001a03440107940c1c02c0c1d00b180100c21284160005054154a2401800b01c5c40c2000c0c078058200c00229030f05102065401b00846000c0320303d0400c803200f5420001d40e440c030f8100b25000f076001c0d240701e44c02000c003941030714514007a01d01034421403414491210004110400701d50b0f000282840c40382c8000b00b0010344600c45001107603c8a044000840c3c82d8071003a2007030412900b5849401c0c01192039020401c0c0104a000340b00380018010300743c42010b41d011107921030340c3e036a01c40d00c6800720284c192a25244d041c1000f40c404064000d03441b42c0d45080503043c400d6071a107034500710b06041d40f01045e008240b0111203142510391 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 472696870 1250 472695620 472695637
    0x1b040b040905161e030320010e0f0a120f080a1109060a0e030f01050103021f200a0303062c150901030b01090c08070503061002070312020c150c030f 65
    0xa40d502181c0012810a0029414410450030300030401403401c201201c4800180c0d90b5180c0c2c078501514180b00096200041d040d211000e041640000c1e1900b041041c0140200f0000032120300c1401c5542c00390708008200204428024101c1c0c64000d6000281580c2601c0312031111400510340200003010f241e038950062441c00d5842103502d0405210b0b0000c50078540c0111000804500540402202c5282c10002345100c1c1d1031000013800310354510742c0415021640d00710102002c0045501050b0f2030703445200e18404100108000b0b0041207265a40b10b80c49c0c840e84002500002d09151001c01c404038407040f2940d0f000c0380c40003040744520285007130148155001d0304031404406000010542030b175034800e000d8060b45c0104004a00307549410310307140488041905030401c1c41203280070090210f4100c0142c82c1e210206036030800f88603a507200100e0a051007900000c1000540c0504a06100e03400125406424800c0e03a00e5920b903040041c07141030a009004404090f40e008002424400c41000040c0c44c80c032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 472698120 1250 472696870 472696879
    0x2d050c070e0a020d27020d080903120307020606030607141806030106050421030c060506030109230705120318060408120712170406021c020301080606121b040b 70
    0x75103501031510040c90030b89064004540114040e11107004602c200f5019560b05215001d0309076042c0f010181c1360a14242c003920414295403c0030920a0326011945808002026548901841d1421031f9590b041078032004014800e00700092901e00f000580103006030001d455a010119000c4045c1000d6403104a001c034007074030464560710441d00e40001542c041c00643c0c440c01c0d143c5051809403c0e405980055401d16120408100000b0075046800b00c1200c80d000500881c05039101400300340035004103503005000b141c00150800c1440c00c0304420140c917a50410640360080d0b034400420803002c03118140c0d10b01940081003c0d407240d100d0f28110705800080601414145540d80600358140300c180308205052800000d503100401080d006441145061030504212020340624031072a9500c000307200402456000943d035068503440e00380a00703102801c1c2c8095540350384500440c0e88640090390014028038070144c95194070b141c0404c2031280551409881042d00303900600f00405042100800360b0032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 472699370 1250 472698120 472698133
    0x4021e0a0e030a0f120f080415020f13050a0801061410140c01020715050c070b09010617070f0e04151517250522060f03122d050c 57
    0x1ca89051040d050414068080314902401a0400302000140310008000304000d00c5029078004c1d0300070200e40c4e0002c0c1c00209a480b4141c500d9001c40084c803a0b07241041600001141c64805000f5800c1e45400340d58050703680c81a425540d041250a03540180240c8514a102604003120782c2058246044191010310300120700c9800c00c80b80f080c49501103104080f0594000a452040c0440c5910515900384803002c00c0100d40b90401040d4403601980c88001e1a1040e82c501150142100f504540003502c4402e4400111005003030700d195590059224420380454004000105600040201d134442c540100c5c000c00403910343c4681754010074008904e11284011980003081040ca008880300200300710a0003802e4441040b010804082c1c41c00440b000360f14030001041c80191111610030304100e081e940c000c84500c41c07108114001c1c002c03c3d008005010741c0d1002c000248040820003607031000c0141c83c1d08109070108429280b03120440c00c98880c500092040c11912075222750f0003400000e0040050303d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 472700620 1250 472699370 472699397
    0x38010504051c0204140a0b010c0b0f07110f0f060f010e0408070501020d0f0614090603030f1c020d0204060f08010e010302090402031507030e0c03160e07091e031104021e0a 75
    0x846850f0f41d0074011182c40c40d010042e1046c51480740c1851803000f420f01c91100c0d502903444445448000b040c0c0040184140086000740c1d0040300005424a14001525248001203804540d20341107040101c2e43c1d841000c010954400a50355114140c07548542c140425548586585074654030212040314a990300300325090702802548903440e207100c003036980403550600d0955003500c3d140702000d1061041d0315031809d003c8241e90010864840c50015450141c80380c0c0c030b01004620044000140801850001401d0019040107500901c1900d20944910b904410798000803520b41c03000340a00c00c1e02e8601e078030042c000761500802e0540c3c03082c402421240034460700442a400c1c00021380f1003402003511a40c19801845051044030440e0805400808282407880040102001750344a070625401c0c0c04408a0308807031040341654050201c000904000c0c18075030314070181c4d0b54410b1205907044590121a19500c0c03400b07000300c0f03103c00207403032418010030100007201c10381740e201159541c2808203201c2e0208 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 472701870 1250 472700620 472700629
    0x1e09200409060e061002100507090810020309060c0c0703030c1104090516060203210402010507050d0806040b270703061208030f0603011407140d38010504051c02 71
    0x30700003040000c10711a142c109038800154028261030300c541e035010000c221160b80002c3d0124060176001000c107550301c40380c9007610b9100e460380290f0f04034000c2101c18819030000d50000c40c0603c102108440807a69030019901090007040011181a00000c1082001c244075000c5500c0b0140108081c0168203d084001030840b2074040d0101c0340b98204000600f44a10301403940401086a03001030b6107003039145001044030782c82000358010003688802c0401d041da4842e03025036991962160880b007207102d0101d0b000d00f00e91030407107a4910a505159901314141000f0078100c6024104c55090f03106074246070303001c18a00307038000c0080007019510310000940c0308030030b00000e003640d000c0c1c14401d641c1c0c217050000c103000c40e400034190307400b90303040c02e0302072009136460848039034008400e1505070050041620001018803d541e414a5400d0070b202d40d15528850f18603c070080f54900c00640d40501e0307a005280e484040044000a011990600040040c0c0c240491306403e415920030f0021003000c4680d0006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 472703120 1250 472701870 472701877
    0x1311090d030c03030f0507120f060911070c0b092b0c0b070204051005060306120c0402190806030109050c01140d180201080901020403020307060f0e1011071e0920 71
    0x10380c00240c803801c0b210145a0140301d0b0907114100c04e00d00b0b00942c40c04d1031026114110701d4029142d074070303600c0150008448182e40709074003070a0b84503030522141540345103544054101c614140c0ba00c9016000010390350300c41c0c84c00c5401b504030107059180000d411305072515003a0306144680a003000c8200c0e4000000d542490b40c20040c2c081e035002d060f151140c0d40184412110020a09680c10034040d406220941e039103015240e00c0302c02100c41000c4912001e0386e880c108942c241c00c00350098000b05507008041050002108901c0013903503000c0203692688201420382ea00302c040544550403815414030594422200010034508560800e0315242d4050010340c1240c0540807411201c84414110800319a0302000d40343d0400000c074025802c0606580000c1e840d00203030b00c40c080900041c1c604041c40180500461007520400a0442c541c1070f0790004040c00381e12013001e04107080c2c0520040883d4544286c01d01000c039450420282e04030505042c0040c1c01024610b8902c120000b0700b0041840701d4145030001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 472704370 1250 472703120 472703123
    0x33102090405031b03031009050c040f090204060305070c030e2803050106060225140a0e13051006032001030e160812040605090f04180b1005030c1311090d 68
    0x10f50340c4948000320319204c10581404201071350801c10500c041e0003085a8160140c9001e550300040e1500d4488010342d0910990340304d040c03681034402e40041c48100b80c0d8040e00488080f07403030038046c030340d92800c0c202c1d20400080c00c01004113445101b00c9545003031071031043d41403020012030b80741600c003400c20307002d002d1981d548125804c5e91268010f1001d41c3c3d051201c811100d60403041541d160b95280025a07120003240901c42c85060840000412a65240c0652004007003040340f00109013480b48185204081d00001565244100c0502c402e01d080d56114070403c40760401c0483d01c444000a01ca1140a419845018101034547c00c0385210030320300340a844d0304080445c10001e0060f10740141182805c400b128a883c5020b030600c001c0100c607400004846503510212110349a000c0d016002800400490791810030f0840005401401c0251b4448080c0c09100702100380500306a80f5010180c0e00c8075403105550b00328240079601035080800d0740041c01c2e0850000d000504060344980422006a01c6420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 472705620 1250 472704370 472704373
    0x8030c070302030106150203190207050a09050f061e0609040f14090d09060e04020703031e23040f021509100504171b0d0204110403030e15033102090405 67
    0x4000b1442c00f40b280034010144442d00103d01d0503802c10280d1203000d20034102505005c80700420041c42c1c820300130107024000050000000d5915454042d005000460b4610348040400002c24843e2914040c090f007104035904171500702a2070311303040c0085600682201c580068503400500d15002082c000c100005000da4449089031815410040ca0a00302c0c80c154014040b4200301800681d620500c1800021010340c3c02698401003032a0480092800708040d200b024144014030503068015000044400d01c3c10403161058540b130f4060700c000e940c0541c0c004141504145115005090607101c8281c100e9031401028107249405001c2400c0c51115080e41c4000741d0300040c144045400c1c8552035400c1e11048000307004040715002d0b01a40d4180483c2a182300d8215285a2011580e80f904074200048410091546550b6240380107080c0c4014400828801c400d24950b03a401c0340c0004040c1c902c03c00c0a90904543d6410651118460580fa083d40b4030601d00c0450920015031070b01002180a64030800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 472706870 1250 472705620 472705633
    0x121303020409052b020303060411120c0a0201060b090a0e0c040f030308310b100306021909060215042003010552021c0201090b1e0a0c0908030c 63
    0x18181e6507441c4520400101e40d003028139030582c0f0554004103680d03000005590000c0d880c62060048a11030081c20151f1040ea109001040000d05400c2e010345030840d1690000d1003034607280d822072074043c003502101940010300c3c1c280c200001080100b006401450301c108403841c1ca62541c42e0044100d80d290002d5010840c000140f04284841000030302018045c4820044400ca600b048004203c04104c0041c00d40154440424800a10014008011a44050219500d98070a10000c00006503c1c041c0720106405103400030b9414000f2a5105000045240102c0d0540d126a40c1160402c00000301090546550703511a00f10340302485818000e0003c0d000c1102d00003058000340c1511006d040000a00c4003850524600c81d04103c0701000103040c0c050607040c500a6003842c1246810030002006c003035040e00d020940801a01988008861402100151016520003442030310b5241584420701d6084180700005104514070380c400c0c440e81d005841c0a0404598034060685160800c4030310f15103603000740 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 472708120 1250 472706870 472706893
    0x303020c0901120b0c130806011403010c02060c0f04030818041b0906080a0f09120f03180615050a0b0c06060f030604021c05060403030501060315050312130302040905 73
    0x104109201000e044407542850340c10500310740210341240030010280700000001c200c83e081c4c20001c1c4c404014203003c070b49056503650552a9901e640a10400e81c8400041242016505040c0203901e100c0403550010316a039101d030104c94080c7da0181e03d02100c440b00500c800b2000890712001000e50765100601d501ca0b0505c02000c0008a03081c604641c0c0300e010303d00010518142d08407840c4030440c0c0c03060401d06644d580d5070800c0d4001d0b0000b042000c04491500030345400f0070200452114020009558054030915505815011540050750154071034103848000317000107040c3d801000c41107984127151156150b4400110f0554230035a08010000706010590740680301041094503400301c821a165603100e0219404203440c1c08000c6d00c0a03001d003440b0070600c502d45002e001d400b18040e6014003102d40074502410300400800d021f00943c00003070b082450110b80300200c000a50300f92200240645400003a5002004055000500c441b400a22001000000d0390341c40c8100c004441c000c40240800b420398 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 472709370 1250 472708120 472708123
    0x2113030927150501031a031b041b02150c250201030e1b0310020f0304030c141902011116050103231f082107030309020d0f02030c0a0e04080a0c05070f030302 69
    0x140c8416400d5603c40c01d01c034142ca036400244c0b014002000307076400620070350b41004940540042c141d02d04902b0860318580800590003c0c0355140b241c3c0e1885043e060b520382c5841341c07003503124015014480e4019000091306581d01100c004900900c14100007030f826804822046c1040c1e8540e00c01020925144150011410144900300380841001011403400e5045910b40c82075001c05070003c0c041210f500d00b580e0403c02c98007071890b038500510080794484041c42e840d110a14820141c200c2c002580d2900d40004288000740e8603000d0b002ca003404200e03030350034100110010b2035540b42c420390700541c502c1c809840194582105019001060300c150541d169111300340e1054560385d11849295010001003010041c501005c1c10140d100341c080903a8030809070034210080d1003031400280d4049845003001081040c1d0b840d01145251094040e9100c4484203401c1110540d982d00c106c01214042400203000038000780010038564003c1e00b4814607107078103610381c145801941d4100c500509031851060080c10380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 472710620 1250 472709370 472709381
    0x16051e01090503030c0306030106030c0b0d1b120b01050d0c120e0c130c0905040c080a0605040c0c020409140f0d0801050607121b08211303092715050103 67
    0x4951000344191612a07440c2e0b42d407480002d00c2c2051390300700400405c07892346c4d00790000360040d50041031980b00a44c0324892501194000000d46030000d1600c2d40c800d910324501009000881060348886164100711070b04140a0300202140b00d04200d81040b8003011141180b0807134012000d07603520400310f01e298000d0602201c1403042d05203c198050382c1c1c40718103544c1d140312603038440712961004615110782000030740d101203403a0005030340541440c0d8039201f440d1f40030700107600c110200c1d0000c4c014103640f64103000840da000c40c61100018105001d18015080503001010600d2048501110303840c96400030328144031400c42d02c0c40280d04044400800c43d82c0c040c400c0c40c00f40c0011a5958600290307a03903030340c40c985851a0a481880302024403000000517414100b905030341c008124981e102c0c403102d08183c05070710821010401031030f040e000c0744e0a0440080c000018903407584510083c0303410041c1c411710300701c1208510908505008a802500e40a9010311b400c0300302c0310102c40f1191401c1c0000501900d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 472711870 1250 472710620 472710673
    0x70209060301060f0506220905150a0605250b0a05040201080901050606040306050c1303060c0908030f03010b0906040801020c0a111c0b0a09021203030f1008030a080c1605 75
    0xa0400b0700130b22a0300b1546002008461040710382543d5085203001105440c4d2017403034003d0302d002074154001003480143c1c0120788150020400e03801c3c9042d0050800590980c1c500540700010301c24080740550301e0300001c0e030070300c01089000b1035503914a0a99503091300300340459107602c4103900e0f107052000310350f00030356455080302c440f034021701841c90f2803000718265000d80d10010f01810380f9140803604401d0498100d40c06c5070380502c401003050343c8a05059000d8407100d280c0c003000500e071080000c0c80c4000072040c3c031a040406454285035910b42800c0f00c125400c0810300690000041200144499092008101c00103090025241403205400c0600798851891003150040e1402c48540840700308410b0070000c080c4d408240800152100101800101406d0a0081d041100c0c03c00382140040c0000145200f4a81d8a24602e40c0741d079000103107900b400e018031856410754014800c0840c55405032194070b500c502d00c4920300b400c10702d90b041c407110038122000d000c1e18250071001080f800c44440510030451003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 472713120 1250 472711870 472711873
    0x5060901030807030f090e0702070608070315030f1106181e0310050a0b0303220501020c060a050c0a080f0a08010e090307020d150c090f240e040906020409020702090603 74
    0x5601d19207034803405114a04006080002c0d403002241d00030b0284c10a074015140040c0346030a140307040e49010303680c0c0d005401140b01143d4150300003070040d807190003040ea0000314401070304101d45c510b030b540050301403039104200c0d44403104241d10010798590b02c0191051b00000c49544032500e401d0802d1092010100050500b40e031807940c91040c10b0b40b000140d05240801e40200060141da4546080004224240016900d400300080411a2030507440800f52041100076002c2c520707a5442d1300590fa240c600c0705070f881d0040c4043c0101c6505078064006009801c0c071880a40b0040144c6944008103a40007103040210940c0110340d134207090b648280e1140c05403225985124050400c0441280e8034003504100034890944c03c00310b641006100da0b0260400721010b0020b010b903081d6140c01800c4203956015520340d40c1090100050003c00003503c2c849642000009060000050f41049400c141041c66807500203460391110800100b061004000501d550200162280810300c1040306052001c4d0480703109 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 472714370 1250 472713120 472713139
    0x901200c07151211070c2603180301140702060f04030905030a060e060a1514040b03030d0204060f0807051c0b0d050709060603090b06010f1106011d1f090b0111060a0207060506 77
    0x4040c03032402d40c147e804148607045141c0c0c040042d0856a0108805405180804156403140103454658501d41000c120f00911069014000c0e201640404550280042e4010000f203804071031820400c43d040350192500b0503d441d100c4020920f460100316080702e403a9039609195122420510860342c1000c1c00070000c0c810840c410381100c401500c5806070300c1450345600076041c0e0aa034ad50707000d0204207030040d00340c135182c07089402c0d840c000317420510402022888200380101d001e031181c54403903c40e0303800343c80d401d08152034403c10907821f54401800900c042d5482c042c0403030681d210031048492610400040402c030f410090360074150f6403141e100c68103140c00e02011400042c145002d50354003403000c9ca4480d940103c4007004403000c0b4502140c1004034020316002103a0443c0c40d25242c1c60300e0058000c84001c580328400000c40840200d15049a522042c0a0038031400d8440d812001000d001407400b20001103000180b14102002560503000341030740044c60204101c02406075560080048034000304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 472715620 1250 472714370 472714373
    0xe07032d0201030f020d0f0e1c0f0807090519090b061c05060613090b031209060d09110423070504060215060103200c060901200c0715121107 62
    0x111400381000c024180741d01c4501c9900050003d41c1526040b54120078188045140c2c4401319005010b6005002d8643c001c49807079414014100c1109510123040d540d58110f01d0740c1d00101151030b040e0140c001020412001000030352030f66940d00ca00040d80d248102c80c1992464400040d0071a048252341f58000c40051040d400360f900c4010f0342c6080f034a24408040340700e5a801000070150705c02e40d07142d01c122b10080040820321708500c1c0d01c0050700603001e40495078810000c40c1c800a150041009280d80180d04000500070f440d001c4d00040740c50752260341d4605030003c40d040050140c55030410020007032249880f11900c90480e8245068002400c0d051080c03074942480c030001d480d5a501210620104a100081040b07a40b0a03030080c04903005650300c007462181e030340180464030f034880520020b0901c1a6404500e0a150600c18201d81040800c1d1019a801d0f512640c6d102a402002561a05009000000072185581c10b00300020007040d0740c0c2c440c1e4040b0011181c02c1180c3c2400e01910000c6c105009000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 472716870 1250 472715620 472715693
    0x60509031908070f0c0602040e01180b0a050609040b1816030b2e110703120f11190302030c0601140306090a03080f090118082d0405060f0c010e0703 65
    0xe1207580c20345000d00e903417601c0781011406485181c0c00055207421180000034243c11603805c811000318920018402c0694607010032413160400d00526034000c03010004086249060740c0700099290001d06000070f130313543d40c0c1c00c104201d5400b251100282c900603142e254145a1601c551020340070100e03280c5c4079109844110025805801c40600d12400c845d401e6401e840703005000000032030b0091003c82c3d00d0180c507032506c07400010303464120001080859480a06441c00f0700010301400240b44000c1c840d01d01645020b0002520740c6509030194001003215400c03d400501100c0c4c082d04240c820320400e0121142070500d4580c000b400c3c10030340d8101a6510000035031191881f9040461401c2c4142c4ad42c42d40503c442c018031072241031200c000c080020020800800c400070306a120050402c0c90009401050f400b903140b1203006807145811002c00040c0711724542a0050301704283ca00c0781450801202c583c1580c01c45000000850480e400700c8010010040300c0c00710300140c1d41042d00305810b407040188062 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 472718120 1250 472716870 472716887
    0xc0d14030c0a0c080d0f06051c15110f040e07050a09060e0a080a0308060420091311030901020405030c010e030c09042f031b060d0506030a06050903190807 68
    0x2078035407207000200b9100700d52007400300b4500f0603084a441e40e40c4001da005800010300e107402c1000856802d044c1d0000d107034540242610340061016090346900d55040da140030f00e80380c6400c054440e842d40c1e0350440f84c0c5000c1e004051f240341400d055110742d17174604003002e810300100024a5201000f00c10400394400c5503120400c00129040c0f03080101909000400182503862a500a10210301c103001e451000c1c9607000650500901c0240c03810010f00031800714544c0b000900010748030016a040100003050b00300b0a085e8030703c20b11000030004640c01074031502c20980d8030a03510042d0703582d0007140501c00c0303140030700c0b4030920202c007400c020031500c0c20f05001c262240d0b54130070440d11652990000400740201500074507184101c02150760305c00000c1710a545252104518803500a100d000076100c200110302c5800858400010300e441c2c204130010034440050480205680d030075010380ea10b03850004072940140d9008101d0300005d5525820080f424a01d248503902603a000c1241c6c0400307002180d0740200c3c11303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 472719370 1250 472718120 472718131
    0x3091d06010c121b0f030e0a050109290a08070207090216030e040e191a010e130f06050f070806030a020616020a030c030c0816050f04020d0e01050a020c0d1403 70
    0x21070042032610038041c3c130b51045002d001c03040da000d180500d000300003140056200c1d142c031a03125aa0440613030010301611440b140100750200e070481406011201c40740c0c06125108880150f0802c2c01360104400451070340242e61807a001c03800c80c50a1160b01c5030180b100001a20000c02c04606000e01d0404600001d41001805014445410322007004c946854202032041b002d19801c84030783c2c1c0484501c1040c82000000e00382d0b60100509400310711103e440030400c1c100d82c4d0380308000095840700306920081750a9000300b12070b034400011104001a1560140301d204044039582848a8507000701f0160100c00b0062001b4803a4215000040043e43d1b070b00c0c1a610b036a01280c45200560180b403021804a07450383d0405090030101c5100001040b420401d000255a080da081d6030343c5030300c030340b05040d000411400b4680d40001c0e00020007070941010307800f4040c42605403c3c080342803e0950b00548c21200e0655144841710340008030182040300400c250280c28426190443c00781c03d030004030407843e000107440f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 472720620 1250 472719370 472719383
    0x305101109010318021807030605030c0a0510020a0512040905070c0c061d030f030c0c030f0604110414090a0c060f02030403080f07080a031e0516030c091203091d06010c 74
    0x21300340c4002d020741040048950251104044200e0300c00800a2118107c681030000780c04c108020078a8100824608114003000d00500400c03070902d01000f810010341c1d019202144164045074000c01e408011450301401039003541640d803420181c0c50801e9a900800c494141f1601d200320000003034000141e8412903e8074034040200e11518400c10f600599200d0100b503140c80365204c40d924440c40403000705684040e900441e802411408145900c69042914100032500008005404140c01d00881100e02200a0001400c3e80610b60004000750040c0e0714002954880c00320002000a060aa20098070690606561410f10a00000d680c1d105501009141100210b10190710443c040256445035a0258210303449180c06c55004005184810350304881c0426507403880b0341d0301400c0c0700e070a0241c41030300900c4c7d00e4440d1141d03040c0c0282284451000c10000d001a001440c031403200302c0030042074800c1c1c1e00e0607080c600c0d00c1000c0c1c4c03020000a00c684001d041000078801e0580c0c10410144034541d2008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 472721870 1250 472720620 472720631
    0x80c0c0618150a0f0311191d15040608060d0c0e1009020c0d1d0324011401170402120f03120a0b01230c03030c2205030d050d180c03051011090103 64
    0x2601b0840a005400011003440c80302d9440310401d83d00070038000241c1c2015075103030340b0051040c020480d074a801591102d11b2640208000d021042c4103110751640b1a0010f0007400d04c1c02440e60b075400d03424440d0350140792294450390900c0310045030b40c21401c008029403842503041404d000704481d252480b008800c4213014010241c1d280c1c001490441040412000701561070340030008024010700c07102d90300710b05843c02d441400880c41c5840d1481400c04d42d0010383d1454840303450000c2c0f075085d514028200740d9000904901c0c1683e002c408100140032282003001440e11002c00c030320140380ca07407000740c0480394550802038007040699012006017034081c103c08064030010801c2a80749424402d4518111300b50000008010208012100030402c00c0f6101200c0350f004c1c0110410020021110301a940e41600150740700b800c0c051049010f4007900e1803400740001d054a04015400340548850002c850341d40345030800308140a400e200403c4142080d8809002076091480002800d03c9130744842c074149503460 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 472723120 1250 472721870 472721891
    0x4020a090b1207060504290406031a030d090603110717071b080d110d17100b040306151514071109040609061107030903080c0c0618150a0f03 62
    0x42c648403040c004050140c80d58180c5035600208568407601949040e4540c1c0424112410221800c4610840c0c121070054105424810100c01900c00c0c0c10f58150400312141e200c02003a641803003401c0852403661102c01c01c107480d06102030107035002100002181101030050b040400c1da0070005200300704280c602c8a54444035031034604d02d0200700401101c1d029400100c003240b411400280015105119116080904141045c050361200746201d00f400090b40c501c10300b055031780e0300180107811955003152409115110700170000a50443d6105982142c1c856030450001106204488050b004c41c48a142501e007178440084c0034050900c1c10642c0c0c40f40002071100030f00c08484141c901c441002002800a404d06050950103005c2c241c4080c0c1e0014980007440f050b054000c001c54115039130544524210501c1e607203c031046a008021202e215001d5000d41c0b4507990f940c50002d091960098685443d1401124180401c80d0324403002d0201071076017048102035458006213400b00b1012036140108450f044c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 472724370 1250 472723120 472723129
    0x312090e0f041a160e09010b0a03090c0914151002060705090303070606120c09061514040801111c020717030603070e190509120f030a0204030b0414010506030604020a090b 75
    0x194040710f900089088144400c80c244203403400f01120303650783ca4a00f609030200c10000e140c5400e02c9044441d100030050300488602a40001c90301c2c2d070184911604050f5500c0160781070300c0d82c094207010011440e404105400340086034581c44548203440002c6d455800d039001035030786c0401a00c0d28040c010301260f41344032076600700102c4036603540c800e90501070303140d4a602ca101003c0120034222489049240d001c43c1c000c556114220484000007090010501821401d035110304803030b81c555403510020003001c2105002409039010500c0842e8050342e5034003505400a825612a101106c0020b0041000c100401c0511961240c00740041e00201d40da41c8485000a00d012004d60150445c012000100015140140c0000c0030140c1078103c03d000e0303955444481c1b503c2e107250221190513081c061144a440c2d861030b00185a02c8003807082e00500d42600c0303845885043d00c01316400c84c0e2100610000c0c0b001000c00f07000321900240183e00808160801c0e074001604042107006200e800e030303501c00044566566 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 472725620 1250 472724370 472724393
    0xa0c110a0b072106030b06010224071b051519140106050c010e0f0102090a05090c0403121209061d010c090b03090106050607060c0e010929071208010312090e0f04 71
    0x55140800034130b5664a400e00351164202c2d11113016005000c541e054483c1d05103805040700385007250440340c564501c0e005481c0717a03142d01210851851074a60b1240002c4003001000d80040d80300410070701500d804481007070564401291148510306004c41c1544a6030190102415038409003041619010461520360061444421401591058600c3c4600c419810350080c22080425a89411025141d0003800305403032060f1416482071108010420102d11181e08584000310b552500c0002c0c41d44916016054852000040d2031309603a4527441e078030f0384191421040018011800a01a1400d202400b0b018070381e09216203140080008000f841e001c60a5000e8005000d0042c80b8a0700c2e040d142c249000140000740030540800c5088010800c0c40d80540340041c1141e90b0441c450204500703014846420010545e82401d01180c01d10500e03000039104425172040300754a540f6400d0729850760078804014044d01c100034052007082c00041c068440c0c0041015800840c4d88082c160a0303c40d8908608100e2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 472726870 1250 472725620 472725677
    0x14030f0612060703050106080c0c03091002012003010f060e010210240603050f0702030c1c0c02060a110705060a090b090f040e060103031128050f01050a0c110a0b07 72
    0x10b2074100001e40b501940031300c0c1641c69554a03030350240e40342d80c1000e180341324041c00d005240c5e10510208140d4900489a400e22000b40d100200300c460b461a00850050214104030405480102c0148036082020101900404180c90b0107801d000c4644000b1b501da8058841410099480301420990100d072070506510b190101b542c1400c055a41d400d00900400c010b80794a205282d801c804036081c82c0c030000c01c0c0d501c442c50a0020b000e060003892070080b1000e140100d06401c0c401a04101009641c54102820952026441e49006003080069a50400920350401442800e050044c0504d444c1d01030103100a48244008a030381d62407464000408044030f015085500c44d041c15108441c44c1c101103545070403030740320342c0701e40c4910070300100300503111042482d0781703101010560340e20500c440e03400407120841070041c0107403a504136141c10501c3c00d544044400d030380203c0c0c4440514081390790012580749000000c00c06000745600c0d0750750b4580c078140c02070401002c000d4440811820020160003044856 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 472728120 1250 472726870 472726873
    0x30309050f03180a03050c06071e0803150909030a0f02030c0304030c0f09090f060209060d0e2104032a09020a020109170306240c03040f03050d14030f0612 68
    0x10340360000e06a90383d0b404100c002c0c5a03640c81d00e20014481c14221640015242c0c404050f010031344100042c40f0141d00824025544a40000074808000b0104881103210500440005070f90380303409151007076104000285140034101800401c6260341020090790401c1e40d1a1034004e21500368031000324518002d070394a4501038000018000100f1a41081e0032088a444504050801d590344141208888003c08090103070020001000000364082e401044107010084c0100d0505448079080b10481d884070001c1b0342c03940d000c108918810b480c2c010f8541c0c00302640703000c410719250950755407200c0200c14232440d1140c0c401b007040141d040d0400e004200040d1403504801c54555010841c002e020700042d0301d00760b485036103180008400c400003038201c80c07190781e0252203414400b880058000d1314000e044c01c0089204c905002c0c001103440284000e2000308000d02080300710300d095041490030101461041c000380030780340b4200d50a840c03100c410740e60710048040c1d21205030307038a40c80482c031203510f0110402300c079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 472729370 1250 472728120 472728133
    0xb1206010e180c04050420041404092301050a0623040e0f03031f0524041215140603100e0a060f14011a160615120b06010c020904080703030905 63
    0x2220f20100140044501c03c45040c03000036074040c80c14862078240f0402c0c031030410007040b00740001d01001c452800307528005030000401418984a54100d00d0414001780b008000f84012004600000d006060f003006901904000700c900c1c1070000b400840903045a81c0421961000c0c8454551310342c1e10452081c110b101c1030ba0729601c2e13007070722076a240d0780100c1d440c00d014030343e0800d060300c0101d0305488a000d565000c1c040c551010002c05014404041501003000401020000862141548803503009a10720540900b100e200c2800d00038000d54070722002c03100013403003c0800c01c821964002446056110701c0b00740003c41c00d240c1c0c0c070f10340d0801a2020f00580082d050020211031440c0c203511264851902d80710322885a6250030311202c0c80003204000601d007620501108211010703003c00601ca151140700005500064030102901c810110b52090300480701c40801e40c41403100302950300780d00580928000c0500721090340020101c490140001c2c0c0103030000304001e0b04250081e4000e21840d600081100d54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 472730620 1250 472729370 472729381
    0x20f040f09080c210708031f090e100903080f0c04050402190e150a03020f090310021e030402090c09180a06140415090209011e09030c0b1206010e18 65
    0x1010f61041410107024441e410300c00700444c810303100b10308a000b105a1454035142441d00c842800d0b81020300500c02e02035216419142c035107003a948070801080c03031180c0840e1000c10884000e08212200070095055410901803000084d0322120043d4031048030712007148551581c155a03e5640503913000650085d01c001000780040344000d03108a00400c0613540c07510103588204c01e004201007100f000c095051001e1003003801060107030300581381c842c100310400b60603d0b03603010001b40343c01030300384041521542c00158290140d140100b80e030205200002400d00d1428a036000c0394140d81d0082043e800848045130f000307401d6841500714110311103110812a001c0c11b265040000400440c0700c1c0304400303001e9a20000440c1014060300800082d0410440d84461801d06004042e42c4019603a5041182c0000c241652011231b2aa4030b920030903603075a4000c141e04600e480c064201680c1c0014440b10b0061040c040d00400300b8102c141d20110a10309088607059a0f00071690281030f03540d0424003030100d0010081c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 472731870 1250 472730620 472730633
    0x80307030209090a020c0a02100c0c0b070c05090c04061b0b04110111010c170907050a0305011a0a140d020609030f0f010c0813030810150309150e030403020f040f09 72
    0x10000100f220115501e4540c605035104912403081c444c5000e0700154950030152070b003282000154401401c2c8000b42440b60b80ea8544040c507990006100f0601c003007940d00030303c010040c000c0054201903410640905140007415494020b5100e940200004010010500b40e204805664100c1c1e1200e001e00503404c2500e0305141c00d540c40108540014800c1140c03c80099050240c490343e03011a40303844591007005408141e00b4280240000c1051088100c005105d85960344564011740c028400040c03058858442c0010304461016081c0c424107940c80140811080403012440c0746c8801c0707461001d104480e201141c2580074400f081d0f0340c103025600180380c00ea00e01042440b100007982008000d1820031000581f00031000784d8071592034070350b000c4010740060b001d0045c454000a801c403290400c00d9175031840548030680c82c401500000d484861240800c2101c0c040c00210b403450035001c0c810ba03d40402219524040d40c840a44610b0214222020503143d0742c0c02604100b000350001d00000d8250305014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 472733120 1250 472731870 472731877
    0xc0904110a03051b0711120a050a050d050703170603010b19050316031208071106040303060e060102060403050a0c0804051009031b12082a0601150305160c030c0803070302 75
    0x40c0c046400c3c98001080d14020002541121602d4040c007424001962548090f4043d07242c1c044d50000008005403900c044100300143d0604c0c03042000300040c5907540b501034108110400140705010052241c080087d8100030b00403010203115049440c030381d9070400002c2c05008000c1070340c3d0f009038a022001d01081e1140401a080d1181681101e10341c4403501140802d184440c800640482d40b4560f0302800b251007403121581103100e51a0000c1050030040c40d40d0304101e02542c084002c25603a001c10044525130b800e4031075010701c0034005031800c0c2c5815103014000d841946a0b80701044a032182c00000c00c142c543c151000362101405220740d02d91b4200016090b800f8030300003900c400840035511f03c86202c0358507420017981c20427503500713140c019141da5802c03181e0030146414000c0001040041c5020008000000480e03d600d0020039140d4904200341041d0f044a104d00401c145c01d0000300051000000b440d07031004105481d20100d201c0c0315013411a07004400c0807005205039030000c240714680e641074001c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 472734370 1250 472733120 472733137
    0x4120c14030a030e0303090705060f070c0b0403020a0e24010207030506090601090b03030a091503061503050103021c021c0c080303090d030c08011409061318050f0a08030109050c090411 81
    0x200031350181c0d04c1116030340b8002107072004110340c041202800942041c10240066403220882c0c5d50030f0030025500c0082412050700609117811000c5410420b614201c0128002800501070750206405e000780002282d1860391034180303000b0740116408049901c04c0002e04000c603080404d94650741007a0490ba0b4640b0f40138808d450101d802d001c09081c0914010044411320340d001d0b00c903000081c2c42c280c610a0b0502005500b8424542d45078000140f5001030454804545400c0ea00000e043d0b0551042102184103210742d07035055201c1540c4203005884404404401120404039110003030504d01e0070b0104000c1d69002048540404414401280d4000035192341c0c4039035984003400320511101c412600000d0034480d9588284001c100003055060145019400c500041e0050341c00c030b00740c250150242c500503c59030758080b0040b40c0c141c042c05401e00950b00c0c03030a504070142075030072080d8885148500060280f03000440c0c1d20b1000c11011f0100c1e0085071010400a0010302900455132146542c58204802 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 472735620 1250 472734370 472734377
    0x308120415020a0314070503060a0e06041b080405060703060807030807080d29090c040b0d0905030c070302041505010203090105031003170d2313030212040f080d1704120c14030a 78
    0x446c80c942d00950036a4818400907103c98a228034140d4941180c6c03001500054006a079020080360000507035030032484041042e114018941041e240c0035250007001404482010714102c0140700052010640c7c4080340d801029403900c84039907007001c41c442c0c8501048400c0031481d2403230b010400c2c0b00c1074808564403c419502440d40c00c24034018000b0f00c00781100c5c00080ca102c100824025050414040c02240310300700d90004007418565112480e6a00c0090381c055568401d50040045107864001c8513410340441d44032001e15480d010010b5900d020340d2007541d06002c000300001e10307040128000e203001160081d261142c40d580321170141c10203034000b00c2c1500c0e2050030070400005c0300300810710321480c94070b0721110702182c0d03030f0b82e0b16102e0881015010110118094980018011104980a807010f008000580d82445141241d11860190405c2c2003409015a24508840f00c800b000035003944240c2200206116030305011040f100188181d00041405504401503168058000301401d09004c0d6900d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 472736870 1250 472735620 472735661
    0x605030709140103021509100504051c05030301090c2c01030b0301050403090e0a060b031f0f0b040302041e1a012a02040e031207120b0103060308120415020a03 70
    0x540441c242d548502c424041050500010401400c0c010440300b24108110482c03030408180304009880c2c01d001c0c0740c00400103100803a05104500c0c01d44480c020381484100c100d40488501c0e07842503128001480359080d8582d48262400303640f4000ca40c102c03502c0c046004401d81500105140507079100c8600e819a00080c80d0000c1c2d0030310b6060511466000d0760301038507828501841c0840d6041e1085005010800c0c80303458210000700781c1542c101440c05050441220500ca14019059102084071036010a800032070b065010850b600081c82102d003641e40581b0040340c0b003402640f05149110a6190300c4002e140b0340f50720600300c0424010160031480f026600d50742442c00a440c1c03400411415400c1c80e100c080510000001032805911800a101940702a41c0c107140311004d00e1448510200c903040c0100381941c0c240b16401c07d5034440c45024140900701001041d0841c2c5510701389002c4d201c84c00710102c00081c0410b0070700c03030300a009118401040d1029940c0d00e4060100130041e1200c09103c4800d4540340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 472738120 1250 472736870 472736879
    0x8040309090204030b04060b0f10020708060a0203190c020c09090d09090b1507060615020f06010902120a092f04050c0c0c1314070c030e09070905120c06030a06050307 73
    0x1802200d046170380010110315180c80719103841d80200881095a03034494403413244048141c0311429401d00d101c406401801250b803500100c281000401050034408038410010422010385481c1d60039604040c0c140001102003885a0a81c030b0107880007d0154011001000c0001050b80082c4100030f110f03042c3d07100c40103e40c0e1454e080f0103684d000b50109603c0105208001e1300c8281e5400540006c07030103640042001aa41c01540312015110441d80700140c211240070282004200300c014011301941c042140b0340b030054000c00c40c04d042c01034050351580d502c0c0d440d0003040c49080305241c0b1a0340c07204000c100c41c40300c0c8044440007a0714003407025030143c7c0c00e0000041e01403039440d007900c55607005000941081c044a20811550350751082c200d40b05140d0b14101045200075440545104001c0d5031100aa258140d080c0a021051a9046c40f4810801003080210055000c00b140045507010f640c005c004075046048141002ea1102815401003000f00800150003129002041210b41c25016216010707107a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 472739370 1250 472738120 472738139
    0x303181903030f1b080c0312100303090608090f010e06060324010905180a0807020406150207050402130b0f091206040f020f01030f0207210207180b010903021008040309 74
    0x3a100c060081003180381d4414456000d42480da00040340e2030308542010f07000342c0e40e0b40d80d40e410510118135154070105a804802d9001e004054100e0032503d05000402d1545da0000d1401815019510410140c43c02203030311010100004107244034010024401c9200486c00a0756601d800ca031018864443c503e0b104401802e00181010308103202c451a07510340e07003020000b8024081c09881c400a6904c0300e0342c5107140d2642800703c1500c440c880d0f0481741d51810280100000e4408070b422100540d5800341c2c41e00101500000c241c800c8601c2964090b0310303144c1040850601d405154010f80c00d80d0400139480d804020b610004150187c81243d000313105a0102440c40c1d5181d6003280d0041207582c100304200050f14010045214400051602161200c60038031404c00b03076080786100b180d4030501c02d000c01c034801081402c4500208002c0c4000c00301760746440c0c92208210842041d403080d06543c3c14148410781d02c5404080d0145402514041c41c1010208006290700400c0742c041e800909000404100d4140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 472740620 1250 472739370 472739419
    0xc0303040323072003031902031c180f060e0a0b040c060819180210081e09100e0109080f03040309050a0b18220207020306060409052109030318 63
    0x1c124083d003004030103502d0415400d1055150709175040c07009011044c14011004402900103100e40e020315243e8408849000e00e14800302880407440e030605925003071940b0803100c059240740d08a10216030f004003e04103c8001c00301e41d00401c0a90184119030005d02c03205100b000d02a51040c1500e00f806a40e0b038904480300c01e415100340c03801010b01c0c40030a0103010709030003c0b021181c207412803043c0303014564002200890a85035800204031400b04100c0714184020b10f19032626064224140c00d464055a200d80f2998805980300f2030030b640c0c0c1200c14112800b540000a801d51154844c2d80d50f42d9114003038210b64200b12801c800151603944042900c0c2030086406c002c8521072030075a8204030100d030803c0c098507020482c040d040794018441d1350100c1c4411500382182c10502c080141e0315490f0340145420428002d001034007580c2003003190300008070b000800c803d044001034414030b82002034010f0045180708005409030316103c00f1801008600700330b1070340034402204031406061040d010406813903520 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 472741870 1250 472740620 472740623
    0x160e090304060206130303140709090e0606010203091c020306040b090d1b0303111c1a0301060509010b090105370206060d0303020f0d060e060114070804060509060c030304032307 78
    0x20807020224013210340701c41000c02d04601c6404c010964059404051100b23010803a910381c0003032101c68042143e14120303c140148250003e01400f018506040042c0d44c0384900c0250900401a10540c400d03180c1210100c0014242d0040a9403039a0a190801a840d5202035607615014000d140b242e45103180103c104240e11854156501c01844660321706400405500d100343c51000410031078040902d41251501c2c2c1d459001c032f900041c0200c400c181c14624422040861402603140a80c148016a582005141103581c0325894659600e03101004070341030302803103045007403001c2080c1d644102035800980740284a003c0503121099180720107004c0b0390796041510b005800440407417013a00880d12a4005250341c229070229075251649509594044030000d038455151844140107110701583c0c010318004820b264100c916091081944410020384901d10920043c00300020b400c00740b54440c9019920030080c528242c98030f902d8941000360101c643c0c100800c7d000e803891200c1403600080c010903104030300d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 472743120 1250 472741870 472741873
    0x120c0703171306092901091104060509060d060b1b06100308070f031103070302100c020102070507090902040609390e0103050c0903160602010b0402040308121305160e0903040602 78
    0x40103611100003c01e80f00c00159040d04811031800429412441c0c1d6585d2040c40b0b898035800c1d5803400c5080780441d4100c40400e50308020402c410800b103580304c800d0b56424002169090380d102520494130780141110381c0100070003c001304009400b040c0184440d80c85414000940b01c29503501d0030410b070356200500004146410074041d44011070103050401c8001440ba0030f151000d0004543c00520319000918110b006900040b00b03541c03e5546806107407407140c698002035040c10310030b035222500c1d40c5590198500e15566440014195941c50300140c0050501d80340400400e00410603044000c040c080c58001d07000071501021009800c03212000b290f07030800c0ea07a90270301b20f81260f0045016000243c0a100940b00501a0881c0c503503052014516981c507508081601d540b801c68060b0030b5500320f20308644228414401007010440d00c5048408006007040d010350036681d1078407444900300c500000030f8203074464100c0c42c81e01040c410306003e066588145980c00d042d982e40554036560b00c201c0c09000f005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 472744370 1250 472743120 472743151
    0x71704060504060804051e0109050f0f060721020a030c1b08090d02010e13050601020607051e0f0715020408010b040e071715041a090a0b0105120102120c070317 70
    0x3ea100700010344d00581b146099441d281000c00c0d1511894201c40c604201d00d9642320400d50070044200700c480828407400015007442c20081c2d910765160840141040d003445848101c1d446084000a01341c120070015410440d01c2d60080742008004041030b070315605c040b4591051070402410b40105107502e4562010f181842c0c1100071050111189101c08200d0502c0300108d009501507803501854600d00c0c07404180007845140c410002443d002014000005001c010000c01410074a5a00d1400ca0070407001e0040303544600180901c01d5600c0340480c0542401e40480d1403568480310b0390000c100f02c90500f0020701403550910f08201c11955106465a06c59000311000c019130a060070448442e07812042c1600c0c400c5000c3e5042c9900c0a004031011078a882c005814450000c00e601e220903003040d82c02c07000380b0807145659a00d00c0c0741e00c0706000300e5205282c0c0d07208600b418002501101d0350140700c1d800c0c489007410080b440030901e412640c400c0300400c81803400c003c1d000c1c2c81107005038800c0f50702c605200170 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 472745620 1250 472744370 472744379
    0xe0103150209101b0b0f1b0a0e0f010c1401140a0b011b060b09090610120803060906060d06080708120f070609020409240e0303070c290c071704060504 66
    0x441d1380d440d10304841d9500807094000045998107070403d2080704d0303180554040d40707482c2864142080d102c07500b62005620074401090760b00c2e40100340041701c030010f40d1104c901004610040e180682c0c0900d00401c40038030189441261103041d04250300801c51141c2c15085619a40044029521550340460000780e0b4085009103151045180408140c0503090008164a1400105070548001c40d42140b059220700144542c2125641d05e0f00000d003110000030217007004540d42d0400e03078070014003030602c640c005501141c001e5581c01d0440310500440002000525581c6000135115041403182240710300070244884280e040e54011110104d081c9499540780c60b07003941c1c0c0c2e14010316136000e0598101c6e5603401800c00140050304842c600455040201c40c4043c0e48015a0041d9441c442503c10a80c10078000d001000b500500190803160380025613a4842c53361108106046026a01d41d030005000f0405024590715040014038085029078007020002100b0410000d082c4694401e900018208000402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 472746870 1250 472745620 472745627
    0x605010f08101e0e060103090209060f0a090216050c1c1403040f06082205120a0c020901091b03020309210903120a120603020306070f050c070e010315020910 69
    0x60b4400380a480701c2042c1c0e52203003001c1d100100d24030140304122036183d0042c03107041420704220350b20110074038051100802c0d55020030f1700150301826813405840c2000700f0140c240e40e07032507107040501141141191504588002c3c9a80f145107810300b5034590142c00840d840a0a00004624210b001c0e4a284e561080b00ba0b9282c03160340b414200324141c2c40c0024440420b00009124149005112551364010307282080b819101c600a42d140050381040700341050a40052008103120400d031400e080c0264455200c0d100036120107001c000001e5001d038000001041d00368059020359039a07401d00300e1038203034840f54442c00d508a10003582c103200c56600940e4545a141607556603110202203480c51030b030a00d02400d0110b450041d044890704440c43d4041285940746601000c0d85403102c28030300d014040c0520b075401003911054080d10444c00c008503a0000a0481d0040049a001c00f1215044802a82c0c1d80e00e00005449000c0c001101d0031880700d00300c450b400c4031500a0392041d040041032400d003046201c4094 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 472748120 1250 472746870 472746887
    0x60513020c0303070e03070f1806081b09060402040f081024030b0c0702040207140115030206040510030207050f060702060a05071e091503091403031b130b0f07110102010605010f 78
    0xc50341407040e2000400c052a40c0102c0300c0041040480100c9c01c044103041c40003d5540c1c603001548e0591201c0390307030301d2000000da2803421080d40603151401543c417080041000b034412030300041740342c0b0480c042c001a680000600411030900c07034482041500311140643c11001e241c071510702003001704840203001041c0e200c00c656410a0b950300301c2078508001540424141c0e000315505481100703440c00c011491303ca0030f000f01906c00d6418150f22102600710f43c0007602e01d009a00a5074094542c03d19004207403070295049540c110b401100b21303080c0200c0e00f699103940c3c080464511005001d0140895414070355400340f28040e02164aa04d055082982c205404141128413000e04126142d0000680134101d50f41042c1c450368195008141a4102c1c1000e828001c10324a440c0c165078020402c024128642484202145440c50150703545e4402c620b280e003041e0a45900401480c03840000c2c00e504225420b80100a110b11a01c8040e071041c41103c01a401c803429407086601080003241041b086910607642c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 472749370 1250 472748120 472748147
    0x1309060303080a0c021009080702150f0a1202040305010905160501080c0a0e0d060507020708150c042619020906040902090601211b180810020c1f060513020c030307 72
    0x110390350f00311495030b2442587c0444905403009480092400c080d0304140c1070703540c5c040c50144c3e591450041d00030108201c61281800160801542e40300100c03d110990701100c0c021500031000b4001e948682c14101c2c0c07201481200c0001e08071908030005107030f500607115a403081002403d050b050501c080c41c2a82c6d6107081c6407034282e00c82e00c00e20705400020360510566024082990040c995542040c0256280151150500010840100401002e0301e540d4046800b038503216108140220240300319002c410103040c0940b0309900070848001a00b0446016007440280200d82010b41d640b580c200344021101044800780d040a40303440001c40c1035010785000a500c861055003003c004030043d860008a0380c540e0109042c140203007102c0d1003401c0c1d12245102503005120340c42c004185c5091042507484030040c0380144400d402080d8001d001000380854900c4003200013030300144080701d420780707001400ca0b030040c20311510441c0d40108010302d1601c00d840b859006500210316540300c0d00d40075140030990f00380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 472750620 1250 472749370 472749373
    0x50f03010906150812070f14120c0102031005011d150702040f0615050313030c081b01060603180201020327130c0914031903030608010c051309060303080a0c02 70
    0x441c001840600c03408505120050715000b4181c1018603072410030107034a0f19080a040b0500c10a8041044081810440c0e079114820f440c0394018280c0705414001c00c0c80100b0008400881c0d04800d2841c103400940c481d4a191040b41200e640b54801503036281c1800e448440b00e1008581014040c4c00c2550905201c0301385803038194244461030340040c0c147e402000c0420135190311000108502041c0e0b003000d50500d4940d0a00714258644691200d011208446d005020071080c1105402808121821901e50a1030b221100080c1c400c0480c01078082c1440e4420840020710742810b0707000750349079075003900c00c41541640a1840c00200804110030782030301c0081040078031400c42c1c00704032aa8904c2c503d00b040c0042c074000440c800d0550407004e007190490340e008151280d042044008180c0e400700c0c0d228507498400640702404010350401f10018012500002c00c02d621700742c00c48100c41e4016000d002c0b852285c00b46c1c21104ca40740c000030320a81d4002e10009000c42d040e8800328a41240715000280c24205034070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 472751870 1250 472750620 472750631
    0xb031503031605010b040b011713062c070501050307050f0d0612050706140a0f0c031116091a060307050a180f080c090108030d0b0a1703030f160504050f0301 69
    0x701c00948000c50000304032400da41d64141003001b03080c103014021a10a00f4203042d02178200b8003c1c030101c9184002e010600780d00302a420752040010720b500401e078203240003031900c0c0180e44c010b41c4c60341c6a14203200d41c86001e10034480001800c0d88114110b034803616488c0da649007080c2108802d00da094100d62302d014915512400041204141245511000b0b40518000e185040c0390844c081d000c4040b0000c1001c112108006208115400070350203071644a5514028000c0280d0b0f0808451224020f03484520780d0040c0c100500e4009680402501540c01c1203c04100450901c3c00c1c401000303031182e8605822040900005079050701400103011080e195040403031218400d2030942000711350343d800c09aa0a841000148640c5504200d6102c0c0c0c0d040980c2c40d400c00d5418120f80d00e540b80150722070210450b0719902070714920f4442c11010030050080500326a00c00b140a150603890350400c8603600110180c2310009990708403880070320840300b03829807107080c034240c10078092160201c841444103401d0364849 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 472753120 1250 472751870 472751887
    0x11404291c02030d18090204030809090a09050105040c050f030a1220060109090c06080f0a0f0e01050c0703180609060f030b191401020a080d020918100f0509010b03150303 75
    0x6004c0c00c1070720540c950701c02402a030741c030300503000244d5150003c058043c414841800014020002c603000d00700c0c1100c000c1e01503034800b17440001510710700b0070040a550a0105020411844805240907100c044030803580ba826440b040c036998480e4050040c080c2d04150000e17044d05070003035810716403200d03121068000501210055a10b400740a90007848091343d110550010b002c0c07448020805031986252160f518203049410340d1040d00040c180801c2c107a5a10580c103402401c6034003110704003130000001d01c0f00c1c0c50b0041414813590000c9009a000c1004407000c02d410344506101003054585c00c0e10303038000950414000b20340000c100342c02030040c5640c0710103400346540c619484044400d980000140e03403034101590401e034840022451419544404004c0000950240688481580c41e4130010303140c0b903880300026840308160b041155094044824030080110108081c4250744581d0711070589180d9410600002c0c100034451014120001c2c40412085200d00d9151090100d0007000c036401d10615 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 472754370 1250 472753120 472753123
    0xd1b0b010e06010e101e17060108191401141002120c340e01210c0509040317070804030c0803040c05030601060512010909050c0105130b03011404291c0203 68
    0x58103e810040340100300300e044801311306120112134861b2880c20448042e60300c2200c00c0007035009480f1506204016001589081c003400342c0b00034406800744140140c540e440c20b5104400710a028103940f030306854040d0501d508140501610b02e1a050380100b03015107090346004240d80161008001e68022642c0580040c1e22240e11441c0855503400002060354101500b068040035952081400c00c04542c010030662400501980052001e21944d0b01000b800307107030524040450f608440d51040300301d4280410705901103c2400da040100c1e00400190303c8030503065030002ca0445004002460f400403000c0080c80100186070481e119400c0d580360f164842000030304220098200800003200032400c120890400241607004200703042040100690719210280c071034a08a003524117002e400140510229007030034840005041c00000c090b00d0b944c540d00320301f070816021107920f40303e64149034a480544004000210121741d0700c1c0498402c2c100100f040c000d0460306050b141c10302c45101c107071080c0544c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 472755620 1250 472754370 472754389
    0xe0709090c0e09071806110703050d020618060603071a07050106091a010e0a03030807051204050307020406081902100c08030906010509010e0705031b0408010c020d1b0b010e06010e 79
    0x2503503200c07001c102e6500310038030400e6440180484e041101001594518200c1040100240c500601d07144441100050695280c0521031384024000e2145486540384550701098143c018035040d100407500c0d040510318141c0c2c0e21800d940c181c0e41500070f6001001035103d4041601c03400c80d601c00c12940ac15905480c1e1078210b5844c0c3d03100944498448c51050403180c8600c6d843c0280c4082402e00c02c1030240701401041143d0000d01005042c0010000031446150240095541481d0120304000041c506860229144e400c00340b0100c0c0214107044010464010200c2c0c8805a82c1c040c0340902051040c5408000031032154014a07410700c2400c0741e00802003180c0c200118841c0381641c00030182945003c06109062405034488611260000c2c02c1c4130302d159020044a400c075840b03021403a860400808910780c03510035a84030500c590320700050780c500c564010030599030300039894903004d0360a86010202c1d0a00781d84610010207105041c00103001c4e200d1103042d800d40015040c5010201141400c01080b490035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 472756870 1250 472755620 472755641
    0x10c020f1e121603020906060702090705190305010b1614012901030917071b081b040506030c04231003060e0c090a180b0705041814010e070909 63
    0x40d54511001c1c6400c00c68014600c0000c01c40040401240d0b004046035080c1d0580002440380e00301c40c2c00f00d000c640d218003e507500d1a07002801007400b41419a40540782d940400171b40030107032402c0c4060071000c60003442028126510358803501d00e410503480d084c15120354000c10482e5041441079030f00034071000911070b9121000136007400174906070924402c041c241100032000e5040506040900002a01d4400424644403a076214640ca0303110030b15210088078480300e0001580c1407104800190404001900e82040350a0a071120a008003c01440143e900448815070564070180342030505040070360024200c100300e4014a07070f44001c06840c10008090a0b1003001e071000a080c800d0044c03040e0f61088035048030044004050880d60180850358003030004002c08003242d0766490704040c1e070841103841d00e086a405140300c01b0a00c0c064a01401640050294050885210090800001003071040c18950140840400080c2c0c6ca090740f220070084000301810308121390315600050b0f4400e24018080b006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 472758120 1250 472756870 472756909
    0x20a05070b091302040623040504050f040212010501060806011206050d030203070302060901140a0519090804061b02090408090112092030010e10051605030411010c020f 74
    0xb20900d07010003600000340c540c0b14480b103104110410806e80c00c40403042000070004103022806509800014250041e42d1116030054140b004011000030b403614840e10440c8200c56610550705c034401d490f404c84030709015100103e200700000c55076540c050025820703056003c03080458850344a0011861105030654104c2c0540d1000c07840604241d0144401e0354010f00e184020004100f16401c0c640c49488060000f440080c2e0f640081001c082034000c2c4100482040841400518194074212011ba8040e100da000084e05c2c01003100702c4211002001c0325038580040c05000c55460302c0e180e1518991010040a040c401c1074240300e46444202e026138019540162400d544210340007400304403141d0074003405c5120b40500c074007808403d22417458103804001d180b80312400140d138060070301c3e0050503040004020361150308141e000140040d0092441a0400141c036020b000a80f0703810364150005990042000030b08118692165100c1c2044501d014001058401c1200550002c50000c44c141b40e90300844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 472759370 1250 472758120 472758127
    0x140f0a0b01031a132306070c11030f060a0209030106030f0312060504021603030b0a090f06030203070504290102100e030a020d050a0903110f120706080a05040b0105060a020a05070b 79
    0x703011981c000c0f00101c0d00341800043c0c0c0b0b40781031031030080700b0108008001c260305e400c3c240080b03c804000c004030702c104200d0303011500e050400404c00781ca0b025080310210b4400044030b6950303001e42000b090000c43c070a000b0004110320f0712103a4449010f0340001c80b11580540d0390304000404a80e40780600c101e00ca00030f80740c80d1120358008504000f6200c080e0041d5000c0d0340100020100d002c2d03000310b070f03a20558042c607001900c42010030000f08035654076440001c43c41e08201818a03400345e15407140c03080f24400c504440300d07541d1b290309110a46188164068031107210310000b0740c10f582d0f06080000c0807a014815180c1e05401440184110389511030f900c49140e2010500d020416010020710050350f03641d0034258140300d100c01c401414034400f400005d100a0074040c2d0000c3d06e4030360110902c4244001041c1040580410f040503640d6142442508000380d280b40201e29040b005105180c004c0b50410b084908603820582807040d40e03401050322108611406a031007001c5441070207050702402003210003968 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 472760620 1250 472759370 472759373
    0x501020c031c0509010903050301121104240807030b06090408091503040302010c080f0a0e01110c0a0201021b030303150d020d111302031611100e0a0c08010e0a140f0a0b0103 76
    0x4860005140c4d0301c45078504507885000c25001001d9074116129071a091082d81601d02c0e000c18004481e14001e80c01505200f2000246900c0400c0c400456450800c181c500990f00d00007590360300842d11000d00301c048181c0100c2d856040c41e208642c0d0090150b84003a2510140801040002c00342c0228400b11a401005102c2015420300660f6402003c0e4942a511428026221007030308001410000c400d60340d078a12903158100039044044406070210215440b0002c4e09070a50300c9007242c801c102d0050142e0350800070282c00111589c686500050021411682c44e031660600161008040340c0e40f10101d8041140103a6840380c0111200344100c841c9000103001505021802944020b44140c060040c010065007000480b6200c12400640c03038140c1001502003581800c041c40c00207240510382c01c0c0b070705c51310000f0720024880004074071510715503540940d03d04800e400c0b54658210040c1e0794101034010000b14401e070b1a8000d0400c0d0103030546200390302101243c0e14040d5804804c50720241111300410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 472761870 1250 472760620 472760677
    0x1704030801090e030307120b04110408010f0513050a0308060604180c020f0c0310091b030605070f0e010806010e011808060f101505130b0f0304110a120305070501020c03 74
    0x424420f4440002d50540c10226009403001415001c0e84840aa40e001c038403503166126040000c5990a00c0c100039500e54844650f14060310420342c040301c1a07418000070400194180212a03451900240a032035052170541e421240e40d540a040306030700c00001e0001252503403802e110801d500c004414000783d03075141c10b034002e070805524966800458110202002e5592000700e5117010408803c140020b00c1101c0d894203000c801a07501020240f014044008020819560f1055018814507218030600005a60041b00c4c80000e42110703c0c001560a00401d6a65000f000950004401410140206400310131100bd04e0b00141d40220406d611900601c80442020010303a500b00355414001c0f0316140c14100c0c0d10342c05002c103226043c100840040c2c0740103012100701d40c81000c0d0400410703985c0c0d51114111607035455001603800341c800742c035420060318440c0b5141d420308040302d12082e50b00c000709009071400e807a02d810a60003036507155000c12040e244c10300b040c4000d00c0940e0807084008940015a071140303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 472763120 1250 472761870 472761881
    0x11040e0307061a0a030b13080a02061008030412080307020717030409060509130308090f151503150a020d0f09030528020c090403030b030a030f020f0625170403080109 73
    0x8141852110018442e04d80150640681e9000701c50000282c890015a517998009400d001d0041180810b06500c03280c0e0201d0240e000d02d8400c0480740d1a1034036a0442070b00c0780b24622620900d0301c1440450b50029406d100030750762001c01030040d2140507540b140300c80e1300d19145c0b04075500541c0000500340441c074a10b2060748080c040640d8094001e10703140c201c8101b80200c0306809000d0003245000900c92000030002c0801403012041035580851400c01684521a000d803903001c20a945400555101d05000800c007081e49469030707090b043d540b124102030009500084080100c503465480060203466640a1003e1640c4241d5809a49401e84000010f02942d40b108901105010610764240180d000894100885040f40c040e0250b032500e24050b40100f4825072075541500580010f0828980c210700f122031070b01025001d4402c80340030b106000d43c940d0011a401020043c010016141a0403241310078554044613041030080581c070000031a4421800700c9049000a100d00700500c1103000d0783c0100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 472764370 1250 472763120 472763141
    0x30516060504051302400e040f140a060e03030f060102070b07061e1802010f390503180414090c01030b210a0b060901030f0f11040e030706 61
    0x5040600b0040082c1c04c50803a40c090741501c40d00800c0ca104c0004062585907030f181e40d03002c00c6007020008011221300711700030480d0901c40f101c4140c03400a01000811003142c41564003072641003a8160700e560b0804401c07001ea102c20304500c101c13011440001d50713910a0310b1312181c0d2b01004544034030f400c441151029100404150464210f500200541c0c0c8510080d1038a50340e0041c00030075211000850030003440c0c0300c022200d05450030481c0140741010006a075003031240c001e9940600120031060107403150b03285544500d483d00041c80c582180071a0307002180c441130141c40307072100c03121905458542c80c60f04031800556229400c140c841100d840c01d84039110300c00301c03d42c00e100414074000040503101d03111602c51605040d00c541007000c5c80e96074410031541c8491003800440880d807400300c100355522404031045814518040209050b454070300a850704807603000034112072401d1640e1b030b002c0079009000012100e22141c00302e03007a00d0b590f4134014070006403c100e00464650020341090402c2e140c00812 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 472765620 1250 472764370 472764377
    0xc0302030d02160e220605071706060904050a24180c0f180305061302040f02030f1f0302090c09011d0a090b060c070b0903070f0501170a0b0a03051606 66
    0xc0c58481c000c1400c4000840c2e001c0703041c1021a0b500c0300d0003a0717008041601c48a02c0300e0343c00c8820004109803035000c2030180c040c0b9170305c0c01c100306054001c55802c00c0c804d484481e40000240120195407038540c004a6000144041c049914290b58038544da541004aa121a8044145109220180c800040700742054230300e22003408021102070001d0011046521920208070704640c0140d8881c5800f0302c48402554003100700c3c1e1a9140207a400b03100b00100c00d0701240b00b03600305100c0f0007804000b4025240581d594441502c0540c8481100520030920b1400c01104010340300c01c0013006d40d0b5070302d103101d200c1c80035000102d0740d9070080303000100079622004140e2900c82c42c2505401080e110052032070f0a444004200140e011508000200d960040c42032400843c481c4e0840840c26000c0030014101b11042a01112441d40d100c0140c0d564542160280350700280c104401800c802c0c100407035064000f40c200000160021540d40401c2c1a6501034109a6050b800120f011101c020711064802c001c004619 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 472766870 1250 472765620 472765633
    0xb060d0b180c04051e100f0e0105120609071b03080412030e070e280c031b080c0d061503320a05040c050d1401050606070206090d06020904090c0302030d02 68
    0x5055002e600a40c091940904d110301c5071581c00151005416040383c0006004080f00090048002e00080d140150180020f120081c1035101d075005105442c0f052030040b4600d0910340e01c0c07c043c054042d00080480b01000044284130456441c02e04511058500958440c8420300c0c0c00e0602650b04649000c956007010f280103051160450007107400800d8416031410a1119182c2a9940000304204c3d080c420440c1c190003008030340f040940c2c0c0400054800c036102030101031361400b054003825648447c1da40100340c003000001d03889040c000042c0f203110540080060341948448030207440c0760a601229003c01c3d0b03030307042e0000420404000703c0d403078030503046070344440300300a640780c912800c80580b03c0d500c451b498001203010000000c0004010b4040a8441d4000c841241000034416041600754a119403800c8042480c80c10008110f038082500900268500160b000501c0002e000225040d20299800c0c003044007140c6d01c0d4001c18410030301801e01c5044aa0039070040600740403000da040020341d400103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 472768120 1250 472766870 472766881
    0x501091b12030f03020d140402090a1e150b07260a0212031509070c1a01061d040e191a010302031c020114010e0108010c0809030d0f0b060d0b18 63
    0x62400300e00c0c242e810700d001c403025800e281d8250040d0040c0b0100c0113041d400c1580300c0314508040c0d07e10910441c003c079016004c6840d44038201c0c1c11107401e5201c810445034824610001003105d0703040300d000003007142401100740f03a40b403054007054ac00c10481100c6412068041c030741c29070382e1048030a0a0700c0c014014a4540700415101079074401c107450112881440c04800141d00c407034040a1000c003840003400c444c66a28003404001c04070104108200d65141001701402c80000510440a051301d031f0f00d89130714207030780400503046050b104500451544143c80d4102040340c0c000902ca500c1981107200082c5191100c14a0f00e0b01c04248000380402246074141c0c010400342e030740001d1010480c0380800c0c460740c0d00886418101e0241151071440500c2444200c0001750400e407400708981295000b0000700891917990a00311040d22054a510885030310520400f010f0002c150700680850488042c00100d1000801c08201d4540044030002c0210703a4409109c1e9240c05e102140341140061692146402d2810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 472769370 1250 472768120 472768139
    0x6100b0901030f020d090812090c09010501050304051006090c0306121101111903020a02100206072c0a0807031b120f020f040906060f05030f030d270501091b 69
    0x1901030003810543c44600c0070840d040c10358121840060740717242c1032003030543d03074140000c07580d1041d803040b60700000e14030004d43c0c95000031039203504296001740002c0b4681d01c2c050044800d0341010f0420743da14011082c0c40394401c80b1031311504000703051044011a1003c01c00744007508503021a840580007281c041010000603c505803651000d120909148203a2941c2a82c40d130b140030b400e8041c0c518503c3c952451101403580006078034075640c0c8200c270510803042800d5000c81e1140310a9a400d008210b00c9035407a0361142403250070740e5050701c8a40e88041c0c501000300004280405541c001d01d001e0700981c0e000c0c41803000140b200d50f601140c18042060840c900f400d00400983d4006004d0000c204900e400001c6640c1d4580d8040c458100800030f200101e228100b110041c09d8130322a030f40103240c0e40e400000c0d59003000b0a030302e03050341c0c1204040c605010f0303024080005058408070100e0001c198602d010110b07918856200e4045020704000285400b140c984880610240c0394020140502058204020010b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 472770620 1250 472769370 472769377
    0x110108100b12070203040f0b1e0408101d0106170d05040e16030f0c0302120f0108030a030b03071a07030905031f09021503150103050112020d030815040f0c0206100b 72
    0xb0042041242681e410404034154010360304011161101171b04000b401c18000ba02500803d8480078001c408900d1240c5005024451031144040c0380d08000f030503000b0341105500803490f22801351a0f18401c0c441c206a0542110803507045460790b904207140e000c14441c010895410501142d00709a45080c1c14204000040c0d4002060361030307990708105103913049610a4220106101003110240910101d424014010f9003040340c07403000da00c01000005280d0369610644504881c5160301442c81e04126034800c0b0060041d0000380c0e601072207412000101d0f034040c3e8803c52002c10204103055140c2416103402032402c1e1150f032003e4441ea00c048403420503c034032208085180100c149000039070059920210f03407006121140f455211070040f080000d8280c00b40c80010010109a0b0100490b03a25403116580d8040121006074009031100b025900180c050300c44140c02007851a820f5003401c0c607150001c0d0a803681c048821161a859041c0b6403100358040090541000034050004010740c10081140c21030300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 472771870 1250 472770620 472770637
    0xc180e06151f050d0f0501140301092a030209010303020c09130c27060f0602010e121801090902030703020a030b0609010816090305030c0d020c180c0a0e030604110108100b 75
    0x500c41250086032800f400848940c2e1112000070310103e01c5030f0300958005c1c0130920610246140b00b003500301c0c1038030b0107118403d0880d500c0784040311103041e80d441030481500b0305118031001c5008901e0120260b510a114079000318880c0d07005104e481c403074405101442401600d00d030258400380d0b03d100000b4100c1000b800507a801001801000c817994444140040300003d00e00380807916001011038441c00a400e6107040e1030194000388088000c0401c071355526088080340c150030400c1840403035020314035003200c41e0b04240c051424024030740d21b03050300c24200e80c8162428404aa800100b107007055401d4061a40e10711801c8403024144a1003500191105400031310001490001503076103a0014000c079040005907401404894443d950980e14540c0c84411b240f804000d031042804181c51442c0c804d9060180c2d507041c04410b40703952580d034078100242e04040702d0f80082c00100c1400d41c030f25032005c204d481e2080303006106c7c207044001d4003030025021803409000180484031404042c00401c48038021200c1c00d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 472773120 1250 472771870 472771909
    0xf2906010c03170f0711070605090f060c060f0603070b0c19020325031406250c0807060212070f020a140717031903060509040605040c180e0615 63
    0x5000d940b0301111914100e040b51409007082500780720307030f40d801d628400d0700c2007100b5296544c040355030b1003100d6511591442078000003034041002c1c0e6450300708524140070066010b03050300c2c02d02035121200c5040081c01c1780c88e800c06060403804c0010030f1600f08085e88c000d106c02c44005181108402469456440c820f0452050400340c442c200f046480401002600203034120411250b00317000c0c21412149941844140d442000b41c0340011100380c00030919038046c1e00004e103101d4440c0742045026000c016106005414050242c05000100d0fa07238500521b003107440740c40016031390904603002c200000c1d0050141000c0002800c0705070310190b00000c9076a02e4a41003102c0c0c04104601501c0c00c1d1030a002c1e60030400e002c015408400e900000c00101600c8009d0720110324000064901008030308a40280c8502940140860080303404a010b5070700064100707003d40d0124111035101c680d958000004c42040c950907030f54561500d051000d0034000182c101081ca05510207150343c4e200024002407620740d0603820b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 472774370 1250 472773120 472773137
    0x11030106050f16050d0f080a0506100c08090904060b01270918020316080f030c061501030e011a030c01140405010305190e0703120206240d08070f290601 67
    0x70b07504412076400c000e071340a421a404c8640909004215118080340e601c085103164000c980151890b02030070788a407001400800c5055106c4104490564101c0c1c0c003a40c8401b41002141e4a86d1281401c40c0e114502030301c40413481889003800140b4140350b1484910031051480c202c0e1445401900e420400c07102c800101041144800008680324006c10744002e51502c2040103008070b603803401105108a45209081d619001222691a82c41c2d104403505c21600b85c1181c4009045c86465a40d12071f4003404c107240014200306503460041c21200100105000281d2000c204940b0f0300d0704104040703054100b80307040c0241404c4d481307020401d40141d004644c10b064035030780050100c890000c405030312081c50724418000c1c0c0f43d188038640c5d22104180410b42e009a0504a1302a00c1400000e880e0b0160744020004440000059406858032403000c3c450717544001c070314503d08049160100540394041c00f808500c00f00c50224500200300d1034407030b82d840d42c1c81c0301c0ba02c1c517810703601c1ca150f220268003907401e0905920 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 472775620 1250 472774370 472774387
    0x112d030606310501110102030f04170405060711030c15090118030f0506010e06040902011b030e09100e01060f0f1d120c030d14070b25030b03010c110a0816060c020d0311030106050f 79
    0xa10707013300d8204039001000458544140f088038002003440f9507081d41604c0c001e426480c01d005262100e06680f5103d102d040001844a5102d0625001404001c2d02c0441240d6103940d074107a0110301808c001c1c2c84a500810040c00407005540009410078803c441c20894a100c66001a0802684015141c0312008004140e01458000c200040c01c040d0001c150340303494601021180d08a120502034141c2c40c180c0d880c00411418090780381c0e95042965034a4070403000c444108103c602071082c03200001084200c1060b13074103607111200b8a003010702082300908080c0000344180b500c3c1c8901c440c8090101b210004161a400c54404200e806094014482c0710007540c80b4cc03140e0444160407000c910542c4409003840440541c141e01c09004550214000e0084500030301080342d048110f00c5540c00c0c20b41084583c0700016400c20001c201d03642255040500040041e01c4e04011900510110b034050303000383c2e01940550740c0c03520600c2c3c100021450001d00750b506062008002e8002c0500c401d10601000800d02c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 472776870 1250 472775620 472775663
    0x30f021b0a0603150b030106090312080708010b0d06080102030c07050c0a030f03080903130603060e0f09062202030d0c03260622112d030606310501110102030f04 71
    0x85d20301844829940e5030b480c0402060803542d480142c03044c42060207003040c02841441100d02400b096500d07030181d6402c1c441603080c540c2c1300d04c0c030b200d814070340e105400217450308203002a500c119003058a40b5128070441c204641481c0c0141c02c030902c034071181c040501c0010b0031812038144070f03905854110406e64940107000d00e1840342c00c10314010b0090301d00000605540c103804c80c00a44c0e0b43c00405407043d0300c80000c42e00348a481540c0020551f0000c01c000f03148001c031000f03500d42e140b0030481040b00c50b10b01030300400e00309140380c40c1c01070001d9a008138690515030001030004414000c0c0684203082c42c00810408124034020700950311a0b6003d000c1d01c10142408410b0080044d0b0100c01000300500710301e0f03c000b4550000c410ac00d000003542d0482c4040038007514004402407524507480349169107801c20401d442e40000000c490105200450211001102c800312038100380b0b01002ca410a41054000f4040511281c590040c5a004004000c0401020528242c110342d001001e0020f054080304030320b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 472778120 1250 472776870 472776911
    0x901110418021308100f0c1809050702030403020405010b1b060c09010e010e18060f0f01052a0601090504060f0b1f09210204060b0c031b0304030f030f021b0a0603 71
    0x44c0061003070307401c0c03200c100350140c1c414208000580810007031022400300c1a5000c500c04c14204041248c421810085150789402195203c1d42c0c1d48141d92519459a00040c00c072007081c0c001c09080b52000c00c5200b00b0202051005c0c0110700b40000a1245290030007000c0c182d0303c6003038101410040e1400480030240d0044080301d0f002d41c1c00602e01c030205080c4511000480c3d07401c1782d05500c200710f502c5c0c00d0540d0f420140c100c04450203069480c00c0ca4080d0782007618000495010b0810001c0d5000034102d040f030001070140c40d000c2d00301800049801d04040c01d08506403918800340c0c280152804080c100e20b1354840004924450190f000810200711096050b660712030598409443c031548010300b4846074071000f0120703918510882e002c1102c01e8403030381549854099190304550a510811088900d40c0c000440e0011030b125a904407031902d0740703994501c1c401c5c0c51158002c0780070400a944090a44c1d406006420295449100c090f00704181400010300311481c510130107060603910883e00200007402c035030f407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 472779370 1250 472778120 472778129
    0xf04030b071101201e0d09080c2a130e0d200708060105060c0106030f030801050f0d02092d010e07020d080c07080a0c06060b0309011104180213 63
    0x1584014603056102800c9a1510074180ba0b280d440c0c6520352069050b07680648150140340d8440c01e0510080c0003109000300c03e03030061031711228024442d0042c0d04032140101d0800c24401c4504640310402400c0c1c15150076036010715030f40340c10404126850404000c000300703070711f0301821511240c9548501c51948018200b100b070006e114013506081140301d64001500c482512100025641344c6021000c140e900d0350b04c0e030f0040c0c1c450380d0894001040715240410240c0580c1201200008140e0b43e2940d07211144150907030200d0108e400f40004010b6485c000400048408080c0c454410106050340010040400107060001c00e01041c40202e54405113500d2205280c0c50301031800d100c0b541c5880c05289040e0b011074440005201d12620340707005520401c4114001c02401c1c580f1810700705141c0e20b5402d2a00480246810401c206488038040340c0c080c09500300515180c8800303940c9003040d030303840790035142c4c0b401c11104605401c11040003807030226003006103001a480d60040e11040141d0322442400401c0c0e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 472780620 1250 472779370 472779383
    0x1e09020f0904050c030f0643080f1e01050103050a020405190503251811120106110712020d11061207090f0e04032a060f0e0109170f0403 60
    0x3048100000014460304168007203040711320146003012519600c002c1100c0341c0103440032040f954140c15052001c150825148000705491010f201c229130043e10203482315800024618105006688164910060308189030a031040700200042110445441061203410b04055a60b070015000640c140c3c169006000002c02c180480e00c0342541802c0d103119503016107486800b4004c0002c248035007018a50480c4060445044000740c6088040107032101401145080c0545442c03503802008680c000522681c121309001d03000c1541031420041c52107805071646000c2c0e074040e80051080c0d41121591210351603045803440010358540c17801403c00720004012039000f50000c503007a07103400300c4511b0079480f50020350b0b60711401650b607440c2844031000901c034130001941c0c8000420082842030003551414050041c01400321080055528460b0341000000d480e1780b0b82e20100800b500145008a0703a00d0b410740d10091213041c0e499181c802038000e01c4080355500d800001002103040c0071100554004541005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 472781870 1250 472780620 472780639
    0x2102040305030309060c0309072d0e04030905120304120602070c08030a030510060509010503070c1e0b01140a18091e151e0b0d08030a021209011e09020f 67
    0x240095494005480c402c4d050700408000501d14405501542e20541c074540040445600e0101d402d002c0c1180e50b544440403110320780b0084801e02509038140e0083c408a00041d980b032034a41802000b003080380d04010b00c200245840030b208450000140d60940751400d00003015501c0740d1401400078403541800400c4a41551000a039044000c0701419184d002610240302d240c8d51286414404107080c001c00f0701060051081c034050b5403140002d907030f03c03262078240748031568034548542c3d00c0542e03400415801428413030855010031072007450250040014084031030040c4500d000003060f00616020f00700b01841d060b9243c0d00030002c141c000188081e0051601c68214107041099440c03040a40340c103441811481544ca01101441c0c868032850300c10003040482d5011410300e05070054014490816442680c2400301c10118500100030360046044080042e5500d082252101c0e07000b030024900240703a40b428101d415402c256030781002031382e800e050340010b0040341e6100288035021803110858002e1001c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 472783120 1250 472781870 472781873
    0xc1e050a0f0c0c06050307111203010801141003320109030e010c050703020108090102070c24110c400609090f0609030212120f0708070c0321020403 65
    0x480180303540c05850703032400e403480aa1181a101080c03003141c02403030018400300c00c1080c1440f4201541d00000039252110b800c80032000201d281154100e842c4d81c80ca1030000040094940074407941070340400350f241e084036900d0030100504410b0401c1c0710141c159801d20201c010f01031b0000b0b0118024001ca01407000383c2c500681d40e100d00810031080c003200403590102082a466004010020741a0342c45002070282c28115030044504c0d0380003401441166409019482c00106806161000792800b10b107800010210444400a480c1c0c00d55000c0e828001010401481c140c004240c1d60780e48001501c050582d40c50300d001515002c4a15030800c2c42010142c0d9441e000303a821040e040114254081050010b1510b841c002e808407045080c0c01080c01840791020030000f0b58a07080314260340e011740143d9001408000a00103242c1c041603140031403203110310400c09141f0284ac903a03a086422880e0410017454001c00242021608800290a0200751403038121055284030881410305080c44084d519559039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 472784370 1250 472783120 472783127
    0x1d09180d0201060302010e09251806020c0f060f070807020f100c0201120e1b150f0301090509060c070f0606150201150b03090705061e03180f0d09090c1e 67
    0x40c0c04124001501f0365181d44403841c24000160140c1c5003807801443c644400400000e142c0700f6102c07074405014000304820201c5020320500c40c02044290054000c4030100700802c030085440c00f0100e44511010310000c0c50111016003075030895a1301c0b0404541e208074500024100f400f602c80080d41c80381c0701000710744400d40c3c49951928410300c00e03205c80481c03d0324501c001e0140e400d00407580f07000c1c1e40441c2c4016418211082c0c044c20a00b00500100c1160310401c4050f5084c2d40122a001820711000004000c80600384c400d0702da2040c80b1710003800d5941024420080140705a400160240018003000c20038007005c4e42c80350f0b008181e0140c1c0d40c1020350080d10082c1c080c0c40c00c444114a0000d8084000441c0745195086912640030200980002030802c2d0401400c1c1c3c005480c50448071052017a1081d110720310034000d500404480182ca00c0c407603040034001c1d20308540c0588041c0039422052000f90055009072030300c010b9840344003020034108070100048030036510918034010598481544140c1c8980c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 472785620 1250 472784370 472784381
    0xa060c020105070201052203031407030207050706050708030103170d0504150e0109020303040504051909050309090a1812020c031501140111120912010219020d1d09180d0201 76
    0x115400030310055032009030680c200c60381114028035480c0d500d4048180400492881f00c0038074400d04001501440301070008146020840e0810b011a134006039070001c0c0b000420a5070b0007400d45260191401c100c0c1d54901c41140010300c001004500c02a40c10048040941c080e0f6408860b0008200b00d180380c00e040481010b010304840c0c0d008a4504402c100c841d500c18042e84500b1900640294030346864541404020700006145944400d400c1242c6107107006140030f0404410300a000070368803503030200100520030602420003407101d072400311400c0c444034801543d10551500176005541c1d00f01d0303855081e400c2001000030964123005013446411000040380c1014182d070751007100d0440c10341d0f2100041d1518000f10035258419031180c415507000e140440010300c941d240241460001d804d25900c03460036600030600d440100d2140b01c140058456041000c0000041d0501c0d018100c408807843e03540500081c0e40c411802001d4090000d2501490101200840f840c0e0034111070440f00481d400031300821 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 472786870 1250 472785620 472785641
    0xb1f0f060804030e060d4a0a170408060a020c0d20010603150507090303080f100b0403030302031503160e0915040c0e06030d050412020a0b0318071a0405060a110a06 72
    0x700d07030107003042c008446d0900d6000ea5000307460b54114846809036a01464110a10b8440c6091140d01c45120004038035031427850000d412400c500d612142049942410810014a50104188103000507221800000340a100d10300490900c9854441402941d0340f0544075070882195070340c240000001085a1520302c210301d006441400c111340d07211030008403030300046888050005464040400e4002c07086018041d08290480210011107a03030b001f245110707030410f0340141e01007603000c410056583c0e007100c003412a045086010b08440c46ca540c1628005030b60a0281203039400182c4006081c01000b00554960505200381c0c03810355240c140340a600a601c0d41c01a2000d484003100400c103a400c0029820b01140c0c180c0d151541018103102d0134030086034610301c081e07030b0182c10400001440403415005601500c0c071841c49286141e1076480061508802e948440040e50740910fa40c54000c0d0700f1307400d880c00e40344101d80c2c0c0b0703a1f680c004510484016000d44c9141c00c1d5030141c0d0030298100041c55114002a2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 472788120 1250 472786870 472786901
    0xf030a0909061d092103060102010e0a0203100c02010b090a1d01140f15362511010c0f030b0105070c030201050f0c0a0b1f0f060804030e060d 62
    0x5030700d4900210540764580f0845083c402c409810120201002406030b50214441c000c4030760b028174100341c20039200e50008010504041c00814030000796428003500011603e00c0c0020120b00e1a554086681c403028080c0241016640c0e02c007115455200b90401031034103000a0001d0118100f0090143c01050320308000071341d030040d02da031010b404031040c020700f040b810340b4140b2075640303075280a130007030810100a00c4086160103100c241011940c1e050001d601da06400340b100d4000411054446640200701c1081d1052a032000080001e20101c0d006032001c15100e001c1c0041194181c2c403000d41d864049031401500c513500f000701588689031300c40402d11407884265424410b21440d0303001981c141c4912000a0194441c6007001d00c0554011302c02030a1451810200500d003003400c0801c0da00307001c0703007110498591014009002c0408081c0c0c0b0200440cae5a1500700d0036520b49440e10022400d50030b440b400062001440010701850b00404069603461805002943e88000819103140108a2060143c0c07030b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 472789370 1250 472788120 472788137
    0x61908060924070c0809042a0509091303031401030f03020706140d0b060912011d030309071a04050a06051306052d0c0a0f140a1119080f030a 62
    0x2180000800c040c02442100c03031140d06900c8003d000c95446007910740c10740e981082080b69212540b945d01c96014050300070440203203040800020b10305076030345000080041002c00d101e094042e82d03502803850f800c4141c0350740c142300e030b1f1425250a401801d104c50030345202c40101d40002051107280d200d03038076000784207509032407005884000589620036450b1603108014414810080781008950101661802c001c18560070300b030541000944e801c0003421a070316281d454100c604c114840c100c00c082c0050344400041c60139032800004569585000340b04210403003070000c180380301c0c0900d40d00031100913050281642a640d911a00060016409288001881d142907d40081c0c29403080003a11200c0c5091100c01200c01c0c43e25840d00100c81c0349444140c456181040b94004c004030400070165424481e5142084956050905080700d0807103c501520701e4100910400004102d00000c0005000c04c50340c440704c1c0814a1541051107810740c00c4000c0b43d115046d2280c0e880f5900101404418030715541d44c510707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 472790620 1250 472789370 472789393
    0x3020d08040f0f051015050a090203070e090c071a060108060a060207090b0a090c0f021005040c0b030421020105180307050304060e031c0c020f0d02180619080609 71
    0x308110100c1c0c01400c090080145240041d401100300c1842c0c9006100b103070414000c01103404110b420365600003402c01d00038201040b41342002100803000b0808d1b050114250f1a24810150120003580840742c81409503400042429903100300392021a0380007014051143c0b10158201c0280405958282c08108003000040310b034501074095200f0f8900d20741c003074441c0764a4020200080d01094410562000a0b540003090719190b0740300305090003140341d8a4104078481e205010f4102501000400c10b01e40c100010400407600c4420404112a4105442c550300d079501d08060958248030000b034a2a00c01d0300c207401d00fa0700e605401090007106614940c0c0c80d5503046580e2540e50f40320390754004203035030028801000010f00500510080742000b40540e114000f1200303224990b00064541c880c00310b031840d17243c0c205509002584402c0103005581e14a5100c02e1500003c1e400c000140d0f0078194182d5220000301c09444440703041c1928410400240d401e261542d40310f507210b4a080350a10034500c5405078414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 472791870 1250 472790620 472790627
    0x6020f03240f010e03072d05030a0809010e0a0504020c060402040501051215090a0b190506010906020a0f03030e030a030504120f0c0308040206041505090f1009090e07080a0f03020d 79
    0x10811000906403031042d03400784010f5920243c2d000d00f00e9454010308030009603000e03608a0b00c0ca010805c205060128130030103c001108401d0076000140642c0c02082130f680000d486800300c902c07080090070034a2010b04105c0008076404d6031504150340040c0089a501d550441c001500750240b03108031002c0c8540d81e02c5000f4040580b40d0000500280e40c801004d01a02c9003d403074281d43c1120105098035154115038030385000d412401d582440340d20703220300010312400d28180304894101030f091070300402c0785c2d181600080da00e11000a02800340e10303200d210241014029480761514010120039a47c64480c80c0350098002d0100300c805880c140300421504580611510110300d4503241501e8544800b40c545e04c044a150304001c0003281c101508110210b412966040c81e00204502da0ba11107030b98001d40d80030320503202c6006250b1401541c6900d00c1d10713000d580003803c1c9825520100c9000030741d0034140364120310b03100b45a88100901d000b4034400c1c400740151803054400081c02a004c50f02e03002600c21089 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 472793120 1250 472791870 472791931
    0x50a150803090901270e01060302090f04060506060319020a020a051b0312090d080d0f0f0e16081009030509060406200703470901060602060c03040201050705070306020f03 75
    0x2041688140704c076039881c0d885078003102c41b140c0c81000010742d080c2c4036030200354000001c0c2c41041100e0071441c1007104100540c0140c5600641c2554070a0441c01d01140d000006050b030b41b80068115004906100114403c20034000c3c9540c0080c22154a0501340a0013000d07140803085250080c02491110200b0300c205504594560002800c1030400307181c5911070314440c1e001442101e106c0c80d01c5030380c5075240c200540a40e00800c5520000060600717100850300386890a403045c07140350300091560400c51210003141010150803401c0c0040382040c3c5600e41200c2a11812801550041000c05c01182c41e50740f095522904071380006501e40c10544d9403c001d030b0340d400144001020251940d83d0f8181000e0303804032507155070504101d0305100040800b0440d00e264950383d00184407505040420412807000d000c4c10300105841c0c0040d005038105031442141901c070052002e8188100002c60b007003003040c200107160045801103021901c03022032421424035980300b80e4a910407540030000101078406401d40e80d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 472794370 1250 472793120 472793159
    0x6030b01030504022103130f051807081501050d050103080306030f070f120c051e0405060a03110d02030708101e0507080703092303190e06030a050a150803090901 71
    0x1d440c030405c3e6101818084541105c03a0424001480003181039070b4440c40d00c401500f111aa0821468240400d0108031150000e16003c420702c2c4001b8041e00c5908441c42e00d820140c5c000c8030480c41c452103c01a5114030800401c2000750345068000800c0c0070085000d10700500c4d086058849002130b42041940da00054050200c1940c8800000c0168801300d0f43d44102c50b81c8541901c5980c1c669a400240c0800034401074640d4080c0a03c008141c9454503200e4954054000c5a80c02c9945046490309000401d0069030740d4003440c210001c5500f555401c0240340b00070f1111004440c1c9841d80c1031440700c09414a44420004901c9504407005003003224040d1520501181c0c0e80d50955a13250f00c02100900300424003a9407100c82e100d0010315040262946030340c03214034a0300441d80e07a03a00851030049842000324000c07c1090031100d41c0f1440e50b58a086a40166900901040d1510390003070b04401004201d00b10805007070350b210001074910011014003a440012500d01e40d503a0307a541e00c0007400d000340f00300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 472795620 1250 472794370 472794379
    0x50d11030f030a0f061202090a11070206160605090703051207030e0409060b0301050c27060703080907080105070c120f090b210403081021020d2a06030b0103050402 72
    0xd00540240362005180e01800c60000495142e503c0d00204d000c6800c1d980141c0f03104040c0e400c0a00550411010003500104401010040c44c0c2c001480300304c040c01f80400081c81024000350031029070700500301c2e015026030045c00800c42c50600300d5240341d403401d47c2d1208540a002d007500f4105000300f540c064400c940e0305505d0b680103141c5403008000003000403410846030b80d41d50f01d0f0045000e88003441220710441d200c10300c86a94800241d00c4000d0104402a07a00210b10130214035900c0d80c403481c040e204104e17410306003484030b40c4505048a0901c000c0d5000f4410320b40c81c200c1040440d690220200490600078404a0280071103014101c407403551407a02c000200b00c81c050b0405c40311592900802201c924204c13040b20020880c0d08242d00c03030405075020b42c0041c00760700a006c41d20712403881280c0103000c1942841c084014640c0e658200c07400c1d02c40060f06c64070343c050b006418400c1c48168074060b900c030f40f40c4034488010312206e0701c03400d51554094070000920301030060120754000d104450146070000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 472796870 1250 472795620 472795627
    0x4050a0b090a0603110a2607030527250902030a1b030e0c010f0c14060a0e0d210603120206040309120506040803040303060b0313032309090a110f0403050d1103 70
    0x81c4143c0302a122603015a8241300d501f0f07460710b1104d1a4144040c0140e111384c1e0b0220f550f00b48000c1100a124040c282318840360701400e4440c0350400300040320300c41c1010080490141040320101601074048503400911114000030400c5080401ca900044510411300c250652001a40c8012011217509107009840c0c1d50008603660015070049410315810345551500380950441640c0e104d40055501045080f5584080c0c01c0c00340502d601d0058a901c0e8010348010010310806400040c122200340108020480d0034002180c5522540c0e0055401307182c018045494a100a68000796034a600700d4003600020102c14000c80c1c0032941c00c0014280302c1e0010003d1905403142c1e10307500007a80c0003400440a1681c0e440000030250030201c041d600c2144004823070b20007840e580c107000d0200f020b0752100007194015180b1035451541004180d4100e00b500f0349a51a2039502c03140b00f00014154501c1000c20040082800d0040c082c002e8024400e0344e03c00c000366005403c400c0029182200d404915105580061 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 472798120 1250 472796870 472796887
    0x601090902190804080f070308090d05030403090e04020a0e0f06190f1a090d05030703080108030f0d18150b03010e06010303080c03040c05152d09040b030304050a0b090a060311 77
    0x141010364000d800b1740c20f0a4a070842403040c04216074442c4100b10701048103242000301840051159401c80b00d49414140e141d4545690024000000d03401549180e560f20f1010030155198141024003504604540540b02e05002d00440d9000c2c008039091072152140c606110380d0720880401e14030454103d0318020701a1802e0a03100602007840000c00c11044109002d690951350f00c1c00d00c80d0941c00c1c0140050b680e02c40c40c605006282c1c240580042040303a20802c0003001040c81c4c0000c481020310800d0f000506032121f0340c140b18410404c0d80c405040c4a040800d0b80002c41d0040d0310a001410301280200208607104402341e481380303002d11002d0049680c060000300c2e8000004000d5900c9842205c0000c0b241d529140000d11030711500e035a150301d4181c04211052045550f54864024200100b01d00c441d450f94140004210310644906602494441c042020b103618104244d40150000500200c045529900904000c3c1c220040b01c0f0712401ca04080022901c0c001e00c80c8201c40e14400c10300e00c0c60103611 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 472799370 1250 472798120 472798127
    0x30c1b16181103010303111c080403110102070501152c0c09130e0d0306050f090a0f0e061f050d0809150409020304030c050105061206180c1206060109090219 69
    0x7100502404562280c84540c12601c008004601070340c444d032504140c0d204c2c0381710741c5840e01508210040c11020402e214061543e0888405a0f00a5040c6800082101d1018105000e4022403c0c018007942c00c0a01c080011040c00c403205054890408540591010f03859074042006d501408130030b007040d400750104001c0c0b160a030041500c01c2015181e1525001851341080840b800c01ca06c12060750400407035642c2103030341805034000030442159041d56403010400011500031028221040701c907600d080e01102039000317030000710062161005071280c2d072800341414804134158894070b40c0e01c80307000500400c25140c24411000c2e81504408410708086581c1d051001600324039003040d902034424000042d14220500055101d1352299550f240800760600d40305081da2406001644515040390718009001c0002034107070340c001d0440040d007540c000600c0c83d2504050001c008507800059401c2540f001c0d0000040190140c03d007a038a102061366152103038822400b48180f1001900340d204004a802c610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 472800620 1250 472799370 472799399
    0x402030901061e0e010909020303032712070b0a0c09091109130902040f060b0d050417042d03020609011817010b0a09090f1b0302030102030c1b16 64
    0x306100000340c2d141d02d490320f0300180c0010074144441c1040204080c44100311800c2854014494408288a02c8032582d000a469000041c5030900b0180400166400b401c40011741c2401100c0440564208442c184130620141c0d00403a000d480427240c9401260786c00041348602403080300141d950665050034008410090080f446541c80d0f035020911604130780303079035803003101d90362101080380000d94006a01c1400141d9040907104a80303d4a8030404001d0149404200d66184466100c000755655880c41c2c03010800388402d02c0b0200e0400045004034941045405828000400a55140c410185105c4242000c0443e01001350800401e215010507075000d0850201482c1d25803503460482038990b13600c003c10100c0c3e080d0081980c3c0d1500c02c02000d50070650400d501804011209029035100c0da02c0b480354038115000c005102d10b03030182c9920030b41140300940300c0c01340d039005000759580e04000c1c55602494000050001010014420088000d40300060b04401d605101e0348660f003861800203c080c1405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 472801870 1250 472800620 472800631
    0x10f0911041a37021515040b0402130909020a0e0403140a03180602090406060c0215071416030201030b10081902070f050312070918020f0d0c03050106020609030a050306040203 77
    0x7141902280080e00200030021030341240d2030092280b845000307400910b40724180005d044050194414440301c03201651403100d500d02e01340c501155070685000850002e202d84072030760b8201c1c04030003404a0308003003a0f0000984036000300c40e10b00017141c98803401417040340195002408140000701000c0741c44940001781c10400184d090000c0c03120f45d078000e428154402880111740c8103600203a4441649410b00c64031015041601e03000c080c500090b80402c0e090940545550207056001c11240e0402601301c81c80b049103c4404150744030b030030042d081c072545885503000403404281000100302e201d0501074a40000729071603a40e4480a9111001e408a00481901044a0494007007194002041008000581d01380c464401199244202210f50045035406000c01041020b04030b010002804c10040da04103003a088440142d94a90a0550001c10710801000d14600b50802d60845000b40d050b0380003504a0b40e01e502964420303600d0400340c0e034480c441ca044807808618240082401400c1a60286500c00d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 472803120 1250 472801870 472801897
    0x604020904020d1e0302120909240d0b090c01084005240105010903030f0203121311010302030907090b0d0501023f0c21010f0911041a 59
    0x1014a8031001202402d09160030801080e080c400c20800d07504111010050040a8409060540e9000080d81913040508000c5904c124402d40902c0c1d0010b0442b10015450020105003040249180464690701c080b40c804175607001e080944601c9501031940c15100d60400d820f44002048099145542060540110130108400319181c402c101d07203500c00b4480a82c054030040c01507102d2440c1040d155204c81d03e40c040710039200001040540d0b086001482560740c0350404901140c03400703104910303500410b4110490f900d1014240000400922642030307420380243c04c013445240d0300344015800e0740300595801515500c40042005074a41c1da6101290b882802081070b85110240e8403443e0980c0c0285c030203502111600203080800a031b080c02b2004020322000f241014048003100ca4101c000c600400c0d80e00d03408070000340448000d9003440d03540c1d01c510325040802c0300340d61155800550f11165000701001d0314640075810a842594034281c40c225420000c6c0060000c1151001c80910b402c08240705d0f100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 472804370 1250 472803120 472803139
    0x201051309020a0c0507244a030c01021203091207060209010e03010b0f040b060705011a0a060e010203030c030712060303030b101b030c032c09010e161d040204031211030c060402090402 81
    0x40c8144109900c640c2312000064114221a01c041014103400d07074010720039407052181c070b640d42c0d8020442950346038022500c2a04e80d41e0702d654641c00c051440300002d10980c0300003402000c01074168094034007404283d03140000320040d401458200c4100300030380c80d84503903c032840c401149041c2d00000300c0400c020300b6440c2009060790b03d0300c0c25075082d419400134010160280d41034a0508004000040110337180001b001c6a4080000c0d46921028100c100501c00000000d05542d00800909880e1440440200031680d52402c004004000e1600301d240b0544008946409843c4a610302000c600958882d00303184111f241d030142c90605003050300b1001d00c4500101c0f0454410150044a81c425040c41915000300c405401c2010900c41600003d2080000302e0074425400d464041c0f120b01526641001c102010180c04c00e491044110005141d100c3d000150100801110340c115944903420341d00c03000450603001c0030068407401181c0c04456554031000008015180c215000c0e80c20a0024220009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 472805620 1250 472804370 472804427
    0x20d060503011a510703080405100c090e04020316090c02012a0819230114090403030216140105091209010c0201051309020a0c050724 59
    0x7500c02295812020709042d0207107881d18101030000d600304841c00381c180042440940d1501c03403c4068a08800d079001c428095070600500150030081a0881c04c00c5035545440b0580340c000d0066170115003c960030f004034801d0b007040350303110300035807201c0e0307400e5118800c03060b04002100d40700387c1c00107006984c10710800d0480c107010105840302d03102800d900100401c9c2e0340c84110003c1d0a45011200141200e403201380c090251040c1568454031400c45403030009820781714400c100d055840b0800542e031714a031038030050308860065044500712042156030391281c1b580ea207402c00c03002e01040c03100f841e03007020700300d000100080d00c213034001e10405404025a140c0390361152900f14141555402c4d03c8030b140e41d036100380104094104140c4c2c29185948501501c2c050258000071702e800c00058000b07051140100e03540081160090b03141c005005040d404640f12494807074004c0411100200a40d000e001c0c80501141441929400084505049201d0201040210001c5030503419402d940d03c02290a80398032034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 472806870 1250 472805620 472805623
    0x3080319110712050a1202030414030a020a030201180c06141608071a19020705010f091b060503280b0936281208010303080c03100504020d060503 64
    0x10300d9451014900740c0c8418076850b0040340d00c05110b900d5002d2010600c80802050350082e01010046240d02000d6141c1c1c4942c9042d00007800f81c9610305c0c0c0361340004180c4504050780020f004504900030340c001d020000810303480f01780407269044042d09d00e103403001c8103010060158054000f5821020202803070169090941c441c154a240e804442c1c4a0f8001100d00920811941004056842684d14822400c2203072954007040d204c55025048207030040f07628000e0110a5021041d00100a2414400210245003142041317441503900303081c010840c0c2c000724200c2c1c414800d41e0b1003010340351034940c0d608034108044000c028505c0a6001e0607500d98500010076182c03c42c4503402200d840d00101c8400b41c001007140e81e80106a59070603103e1514940a1089502c006032810702010305000d582c240420000000c1001d840621005e045404c02c4910098036a910820aa040320b009585000740c42d2500c0b03078402103a100c2074440701d03510100000107000500c1c0036802003107000055100040d420740c0e14004603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 472808120 1250 472806870 472806881
    0x4140709020d0c0201051303030513060f0b04050f04081206130c02070807150c020f0a0b030403050c0606100c150e0d020a05010b0d020d081303020604030b070201061e03080319 77
    0x10040c03140c02055503052030840380140910000c650009000d07501d4006200150000108006030415880308045482501000b06510809410150501080d42810303c00f5010301030041d42140a14030703000014070100000141a809250700c282018078204800c0700f06a0024809080213900500280351050324513078034418260041c045e6000b0b840c0c0f00b4540200d081c148143c5a00540380862051030b13100308181e104a02d2502c032130b4120362101d0000c841e40d0101e15038426580218800c40400001c0c0014140c200c1d0160602006601c1220555600c01050100080d441d0310b002c3d000c154015400000103510b03601012145200c610001441c40d008030829190034009035910001d0f03000f04682400307100c07080c0588803090b03a003628150604002c95010602140c014907019001390801309606601c030340203510040056400500301c41d02d90380c0701e0910940200c000d80300d02002d50300e0018009001003100c804200c0d43c07056089442c0885245403a6091141e200030f1072403541f0386c001400040006c0252144 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 472809370 1250 472808120 472808129
    0x90309090528150f260307080c030c060717010909021813020102060105091509090106090f050105011d030c0105070204150b0406080919060c0c0c060e040f0504020609010503041407 79
    0x828603540020407246003035050b400c0b407082c850802100380203a007420604480b01c00e88905d02403c0481008085604601520100915590b4002005452000008054540e0307454000c10350340280c950704015181040b00c42e8800c0d4003809000010014110581c0c002501c003800940030344802090030720204240f84040701c5035600041036400c0a01996810050140542420346c1c480c003c03070070604082d500401a90704058070511118000860985080d00000020042d03640c044c03100d000b6400d80c020151400b40640790019441412100f064031640c0c00607066420b000d400f40003081d03d00401110740340d00c010b4040c0d070440d440304c000000805600100c0c6000384520002d907500c40d420070344002d001c000050021641d0b0f903c119003484c030305c244040c00c0a44040e4015800103400c001024180c0328050041c0c0e0261580340107810014410f5000341e11851240c504403010010801017000070800c5402c142c0e8003940004041c8100d0320254014001990030130700404210000210000c1e1051511a02d0b810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 472810620 1250 472809370 472809451
    0xf030b0a140405030a0914060415261504090b0417070515070e010503040308061c06021c0f020a1b080708041202041802090402040c030b0402040b120601030903090905 73
    0x41c12003041d5840561140a000c0f58412055030700c00b24800103230786004902403c0071040c0080120720707195026499800007140714940c40034011842100004c1d803008111500b00600404100b42009032903d0320484ca400e0350b1103008100c5603201e54881d83c4584068150240210364200700380d40c0420010009590310074038000b0003010380e2410b1b000080149143c146164103100013032041c0400640c004950560100302514500b0340e864107120350010320314110401134000380c07000480107041c840c18480303584e9003040d10030180191180c14503414100d110f01d5040800140c0c907220815040c031054481000100d01503600380c0d080c00d03a1902c2e2036002d50b0080d0700110b03082c000c40c000c240850030240144480760403a220f6610840b801a00400c6a180000b00000d1003103a50f06840f00e044c40c0039510001419401400454980352200e46954555000c0c400008044040500103504c45d0700c03a0041540301541039890100d800c0c50600c441002d094050041e12484103440000104040c82c07001003051680002c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 472811870 1250 472810620 472810627
    0x70807030c050d021c300e09011a0309030c0106120605090d212a030e01060501020705150c0a0602121003020303030c0912070608160503010f030b0a14040503 69
    0x16162207108020703446580191900b01c0719401594400d440c0381d09010b0340e14812401440c0e240b5141b240c014000664448141c3c0c038810711000140040700060203581e894595100c00e2000342c08104c44044244101480f07045200d1151003240e41d000040d40c0c0050400044a0520044205440c00d58806401400a20030b588145900b8083d46008454100000c0c0c00a880d940806002c010100c074031161660326018080913640ba079000c52540561141d102c8420020034144a542c00c0300c0d00d0f00c0300000d000c0002400d104000125040c18410042140c0058005049451405050107456081e60121810322401032020602c0c2030001d0044011a5200700401030740d50380501e440032284003010302a00a0910382da00c05000507200002141c0d04070200000c401e0f05d4030061030000c2c0003c00e0414105859000c0c2410004009400c1444a4015105402c80e0b00300f8004019048070030340424400c0841507044130100300049101500c2c100c0d004890b5010104120a41c01c0364003001c003038181c400711032039400007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 472813120 1250 472811870 472811873
    0x909030212122505090f130f020307020c03010b0f0108040201020f120a12050f0f280902030c0312040306091707110a0b1812010b1002010203010519051807020f07080703 74
    0x704100300710f030008030607041d500d003418200040c142d01484507103078082c2c1d40b0400304030342aa48481d1806484800740c0c85c00e0003400409078540010350800e6490340058440c9040d0b0320400d25040c01201c0601d90302078040c508545102c0d004444210f8007a0041c0c0c10f5014003d90b4068a040a1000449481c00c5400482d0758548160b002840b881090710100d149510b00300038400009024020143c00c2a11811001c52984680c080080804c842003404ac5061100e0145200300b8950760b0002000140200c05032524600030000745502c64140e08100d020245003000300341b0028560745d0000850f58003030b0800300f080700c80c00e5982d0340705603101e09400d903040c1d48a41c0b817000c02481c00b120030b00054401030703550905040f004809210203480303904000d403041814401640c0d80d207109520822111034000d064601041184101a000b94002cac0601ea0003040e18108521b0040001303031148003200c5016046249444100d000c0085102010b000300c402c5000d00d807903440780c21408002044c05040a0005407035018550f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 472814370 1250 472813120 472813141
    0x411041715010b030a0525020c041a010c0b10050409030e0307080111041406070c0e0a0605030102030402060a120b0303041502011803021216022e08090601090903021212 74
    0x41180e600a4001e400510841c000081641d80221003a180410f040c0c6525148191980d0000110004000d005003038a020039400038880c1c0100c21b00740c90800000725030010511002078881181401718810b40c0b1042d0000303001c0101c26034000c0302110400d0800d42c80d44005003c0c6c625442081e000a0f8003000811001c0c5270500100d801000200c00030010040791800032109801140300d1400c1c0440e007000c003d03001d51a9481100c00003940034100d210041c0d11180e825000c4502a01c0080e0791514045000c10345081c14802c882c01150010002403d012804008445c0c1800580c0b00f101700c04d4691003d20b01b95102000607001600500320303002c03100390320348000078211051200d00d045041c501929040100350045003620202c504e00301c0c055500c0c50b28100b00022016001030080d008503003424806e805200310005c41c01d008100341d540c640081e50080c1d08031220903060f40d14030200d070006401040300030b085601c1100b00030b219005982040300700b5000305099400c0004075100005600e004c0004088a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 472815620 1250 472814370 472814383
    0x3080403030b0907140702030114070503100f030807240603060e010c031a060f0408070f030b0601052a01090602030a02070507170a120908010e01090302060a09021c0204110417 77
    0x900340c03003406640c07a040c80000e00502214409490300301c80050711b80300b0b40d00c0039004200e65410106070350740035052801d002031855000b22142031040800103008110b00100302c01c220120b903000005182844115100c0c96805055800080015011504090407810303203405450015400f50340c001858460130042c2c24203450b000706801c0d04051404481030118903101540d02c510314025284203403915500d6108481c3c80c41550014680385c4201180080c400c0d03104c2c2c0070350094910034000c40203261100001540c19000380c090480e0440c0540c5403580f0304011110b035144200820740e002044040b2161141012039000381c03114941030740c0010f54201030140030400003005181200c02d005920805010258a1320010880240340c0100080c407040c0092042580310081c11008000f082040d0448440500030900044101d000d030184500281c4403c0310361040c5c41d0032540241c440d01d0749107110b00c0281d1010348800d40480e0700c65650040a030710002c0d081d01030405881241030001850000000c0c103480e022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 472816870 1250 472815620 472815641
    0x1140112030504090f06080f0d1205010b0313050102090402131a0f031302180c0a030e01050714070512071209050312041203020a0b070f0e030c06090607030512040308040303 76
    0xc200800c000203520004031402c45256103030002d0141c40780342e056409804250701100e00b610036140f42540111012030004071441094482200100d40341c191442990024800d0039040f0380d040c800680c0c0303000c1c03a020b110312040c4580001440d05c1c002c0000141241c00c025268200409101f07001d12001d141166000b44160785a0215401d01c91586455040e92200808041c800c00303000c100c010454542900703e080c0201210405001c40c500310300c1c0c0d0482c5070446000000083c2c1007003500c41d1174250601c0303268043c0c0c00a984040c2040c9070b8402407401940a01030495007441a40c1e40300c07101c4ad10507000b4010440c42144030b0741803054420001003881490341c00c0148640c0001403911a03000141d0304a904654071880c01701e44085690500741d00b400115013003c0c04d0b0002d90010030112030340c44282d5581102c0c05032078074110116600181036442030800000c60f0032081c1080b00070a240b5020010b400c44500c42d203040c0d441c10116071014901440c00307990131000b05403000f09020425805000d01c20000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 472818120 1250 472816870 472816889
    0x80105130f050304030203070b030402042301151206080d02070e1012061b050d0606081b160c06020105040c0b0c0d080a090206040f330806120f011401 66
    0x1810309088032a00051000002044040d4404420080000c01d1003078a004607001010f854100e81d8070012084903600c12a412403203580303000440b0814410304c1c2407400ba103581c0c0c2e01581d0240c1e030900b400d061301410f8507010242404494480c800021a080c040c00000c6c1030307000090b02205060b030001900d0050281c200585d050024010042103071404001503044402c0d00b6a03030350940a1900340300c001000724003480700041e0001546210a01d400000418005407003080400c0039650700c11048800d014250740e90001d4091442c40c2040d0704c28904050b00d8140300880303000490644581d03d40046840c141d00c4240940d44034401c120074400c81c1c0c0c1c04000102140c254803490203a1510f02681c450700b68001d1a418400c0e00c1c404030720218210b81c00b45110682c0904107030780da60749681200742c1c0d1140300c1c07003480142004140200c0c40800c04041e03541c05030005d02103ca8241142401c2030f01c4a1400400440c4c10544083d5052080207041201440b03410b065000006c2c00d6014810061008105801c0001d20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 472819370 1250 472818120 472818131
    0xc191508070c1104020c0a030801080f0312061e030703141501030305190e0a03060603060c050c060708060d2f010e0a050607080f030103050d030e0c010e1002010f1d070801 75
    0x200780d08240c114010b59800001c3c071102072410400100280122a01410184502d0590408244d005240c1505a6060038112200b508060060a0341ca2251074840030b43ca020078008075005060400305070342010343d0f14084000b41403c52000c00e1805106500076201c00c3d0094044540e00d800c180f01510720034a40124501a96045860140144c880c048565a5004011810719141031080e648030302c03901d000400f01140c0b250380781400d10150010740003d880003403a00b03c8401d1014000c1c011a0602c5031074601610b511b40d9405010f440704400100034581004124a0120001e07664203100a4440c242c403560440404160114510031070514000304e06000015038404d03919078a04080c0411658102c54007079483c0020f284c0191213000e44000000010004400442001000308851000f081c01da60104040409407803003d540e0b5454507041d038046a00d03090541c2d41c60a2031000c40141c50744030700020980d50500b81507041103444119402c103031110340701103628921600703200711802048490001e00c030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 472820620 1250 472819370 472819381
    0x9060105010f211a09060901240203210114010c02031015080307050105041b0e0c0901030b09070f0f0206192316090506030411010f020c191508 63
    0x707000b0420b103020040c4006910089151091002801c0312a02c07101c0d0240200c28113031004010b041100c01c2018881c0841d1800940a810400c020034108c0c0c0c140109140880c160203034406040450740703881d40860104110f44901400146514a40030010300c1043c102585810720b115404075a0307014450400c11140f20000250ba000102c1c1c240e03041044800140d4100720384252400248568844c5030f640c04041101d005202040d0301c118441d9001d00800c82504c0d11031b158039482c4041c5806200c0020340e11501180200c0c0c081809404000ca060400080000d81600000d843e15411510800014030740c1c04130040705a03000d13404030b182d071001d80002d10450408102c0b0000300304c081c00940885580d0707184081c030503488145e1001c007800003114249031582808105500c0d00080e503103500011400c02d040000715400c055045030f00c51604500c0044201d5040801128604281c045402c114810041d1550603955080c5030f28254041d16003881507500d03c0c140060380304080d03900090051000c42000c004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 472821870 1250 472820620 472820627
    0x20114040305031e04050303010303020c1912060609020304200103020a02060105240a03060509160e1905060d140c130b0702040f0501080a021f0f0315090903050a080906010501 77
    0x190081e901d418480d842c0e81d103543e41d2400c2e402e2042c00c1503d030b000c0c8800904c001d0120100003103068034001c2d425606001020411b0003011395200c000e02c0b410600b601d1041240c052210407408a440c800c08002c00c07010760f00c4150006903042918291182d01159002d41d06210b8102e00b017154491081c02c1c15400c100400c080603450350b90512603d4013444515404c403000d42c1c1e40b007a08803100c1751b010620b00d4644040043c01001001103004542c011410341000c1050510170003a00700401165641d40100380440c44240a56005102203c4100071705518000c6000e03a50b08001d40040c1000306000105001d00b003a4642d60a003000c4d00f0f54008040800c41010207004034038620054448141c45169200b60500c0454008c0001404c241440c03443c00002240a03840442c0d403007001d40c0222114000708603c07804021826101ea010900411240458440e801c0c3c001d801a08001c100b031440d00030300a954108a4040d151302c200c088000580c0082d41c0c22250b60400f002c945c2082c41030008141542c149030018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 472823120 1250 472821870 472821911
    0x40525050d2901030b09150607050102040302030118030206100f0603021e0d0906060b16081e130e1e130c030609050c1201020a09050f030f0d3605010e0a0e01060c120201 74
    0x18010040010701c01c08ac00000d40480b0011603002d0020031090740649004012001042002c80041c062000890301c080d00ba401020300750341c4600f102056142c80c12a09400a6010810010040c01e20140c03a600b4428400080d013002401888041303100c2c869440c0020450741aa000030803414010b003c801e201d5007480761001d1085c1d60240d01950355a82e40302c00144149845088540350071000100c4528150400c2d403d4800c03500c5011801c1842c0d1602012080c3c440c2d918086944034460200000c0da0610880d080d000d826402a0410911940c8039201c11081d543c12850544443c1d005001c204407030f0520090000010201a000710709208848100410180b45842650711503081b507280499680c1e0284500c0c9a0601d0a90895443c202e051304081c203210200d9020f5884030750003c4c01d501d400b49200840c0c0303104014400102040303904290054035640809009145c00c20030036080071601e800000780301406010180c0742c030740720b207409440c296a0b051062405e210841e4101b84850001c02c0f0f400703074103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 472824370 1250 472823120 472823161
    0x1203060608044e0306050603070e01030515150306010801051905041a03030a1101150522020f0f03160c0803060d080f040b0702040525050d2901030b09 66
    0x294611502d00740489111000c000c460303a6140e5420821103070f24200901e0410190b020703071401c2c044c043e40e410405c103143c00308484410205031282d07a01e80b81da602c0307540026031000c0c0c4d4040b00d41c0c40f0916040031500020124215210b42000042400445e60f04045181d00408085506d0aa00512035141c9945603415200c0c807400f0b6a241d134640208a07441e03143e000030002d00541140c0d1034580d640700081c20394822580e001000d501c0c04801c000700041041048041e90000f8003400041038403864407180c60030800070000c901d151709000030300251724040700902400c1c0c0c1c81d0400702d407282400c040c1ea5841200d039840440c10b221000c0c10340c00001d607544040c0ca81c8030208a8199483c14801e0a1465003032151001c1c0103898080002c02140f10a8503c026004190098034204156030350003810074100d503118840c1d040e01c0d4201d0a00e10041c54420300081545400100e00030510450300c0c2420028503141c1d603214490000c81d42004442541c1c14419521622401c031548c03900c078100004241201d5050750344 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 472825620 1250 472824370 472824413
    0x120f090a0303320412030b060f0d110c06040c06030c1416050102030a021806070201051209010207050d05030a0c090f0510090b0a080906070305060f1e0d120306060804 73
    0x3030360700c0580c0030001120483c1c140351022025195104003003101c045412502285d101041c8005000460311034460303102e0311700000d0801032070070312242ca50000f15004866406c1581d034881414100b00c108240c007500f845003040c801054181054034100642080b5900300c001090700c2c0c10082e000071503125603840c0103400458802651981940da01e400200c40342c0d00058a01d600001c140705a650166004080d51004410008035040d0014100141c5210f51100603002603418851020340c8001e41051b240c000c50000300062501d02241e035071034208007003407840c50007040004c801c1004c01c1940307001c0c105a5001501d08107842c05e00f0405024145000e0703001c4d16000320745a50100c20310f41c0c021200789002d800c0d400340c2c0390340792020100700034a184400c450700d601c01d001d44008540150b001e40a0070340036600041c0100300c0d241d82e85007400b0105c002680c0300c5100b11414048034a0640358548820701ca02e016090740083d8201101002c0d082d260b03d0381c4041d0801c1030039401c000c00700700158440c444203c500c21 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 472826870 1250 472825620 472825631
    0x2408120a120905031215030c03010e0312060a1e061b02030703080903070b030108070f06170103020d2405090115050a15140a03020c0606010507080d0e07080a0602120f090a0303 77
    0x2040c03803a5006000910718204d11603414054000c01b01540d0103142d4004804449903004c18400f854281d0f50700f600034004680c02441036200c2c0f40c849804680e409400508800300c465034a8600c145500300c0c3c000c81a030300c0200d45c0300070301801e40e0000d801d02c2d44202e4071403942c1094200e540803903620f1001c0c0c807001c0c294600c00300b2101700580e001d0041400034102d409006480356150300c1000e4031600d142c841d620071a9800351000600c02d000710410003139442985060b600f103a02c0c5400707001d0011903c220403510034440143c8214810088280d43c0360441c040703c1c0c0050a40f90a15499084401680340b0410054448c00300b000316a5071310f02d801c410b40310f032011156600028107509840495510b002824034540224200c007100e940343d4090b004030340382c07070088854070b8403904019901446401c001800524003004240d000d07a01c5a00032030395540d09001142c0746d5030b6a0303680700c90800c2400e582c01c552a40e0000340c0d1100d10310100300c4883d000a1131484014007810b2240016986000c0070f00010141516003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 472828120 1250 472826870 472826873
    0x605060a0e0c191e0e180405070e0c04051c0b06040b0f010c06020730030c050f1b06070c200f011d030a030f0210060f1403012408120a1209 61
    0x601340781e0f020350041d0780700383c2110f1401070019000c0080c0300100d034010f40402c01005138004000000074045c1d038014014042c0b280c1050704149a03003000070300705038542504100002e03a9480d080d101302803101681c5111001e030101460103600c8107001600c0c0301d00c185d041c14250300d25690744150f2040b0603038007400d0052086c1d2083c039242d0064080c280018040510b48100d8000c0340203a60032200300d000b8882d46882004041020643c00c8440c0c4291250014200f4001e511121400b03000400d158120035124100b4180740301011072900500701d81100c00a4180d00048042001c0000850044607184885210030464240031550303c4852000703e5041003203030b0f00c12081c100b072200c0608445078400b5040d2003800c4507604025100700b03020030114006200d85d583c003840080c0b25100302400c1e41d42034035041d11454a002d1030110700b040d50041559241d5610481da095104402122050f0081c01ca008103802c40d00c4e0580361414171602c504881c140f8041007105034000c80c0d0003102004100103031000050040c149 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 472829370 1250 472828120 472828127
    0x200a030903120510060206090a0302070317070c0f05030f01090b0c160b0103080a09120b0c0c07080303091c17010b03042406090c05070332070605060a0e0c19 69
    0x281c2c41102e820a260009201c44198440c24440a640103a001c90f02c440c0c913848507642c3d840d4a9400e000d00160080c140c28400150703844002e042070111881141e0800c1159200c442207440d25a02845013488100e030108500e082c1030184d1400014000020444074801d9120310005010041c07544840906c0001c421801c80044070008241ca5007002c03ea0200b580c5031301e8210b40f00c0d40081c900c5404507582c03c00001e01d92000512042466602082a04a43c0c5444444103020b401c8118007600a0294020108684000b0400741d407003907442c032000f0300d00b020220b0404c48000600c2000c620801803120001d07010741a243c03026504450440c805e051f0343c0da541d4245240075170030301d481c0b100751056046111201440260403003400d8855000c01000a180000025034091150300700003000305005108103031103080d400c41810b20351505a680c100b07803144141d8149115601281c2c04a40b05607441d024440341d410070903001005858070a500f0184c905040211a5070303070095442e42d489019141d14440a100e10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 472830620 1250 472829370 472829387
    0x90c0412080d0c2721030318050d1808030a120204080f0601090e0d051603050715020c15072f03072d0213050402031e010b041b0c030c0507051003020d200a030903 71
    0x1040500e00809001c030709d0007a40320b9218013015000100e48410f540701d0030611850560403190b046c0003d6140242d00c200aa4001510b40c16413105035909100000d581c28051201c03441c0c0704200030140400d98103000c0461b04448000c110000d507640701204858600d900282103c47c0aa6154081c0c03d001c0e415207011915440741c82030007008000b52295040d20300c4810340151007280d4204080d1001c4101c280c0650304e0480b01110f02c4400100a9503814042024a405256800040c0d83c1840059824146034510b940e1003501c04561202000b042100288085440c070b01107880020080d0402004a400103011607121504a07845a5504e0004c101190f508020110300d0b6500023158000501d1a400355070b0080c07000c40f2201e0701542c1481440d01d19400019600b032600802529141281c440c90785086403441c1c0700300c10441d22846201008160340d0381e40c11000c510400b0031395015a0b40e0100105d26020382e542a2100c189071500d4130280c0c0c60000c10801950050038441c42c00040c55019410111400035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 472831870 1250 472830620 472830641
    0x6051b070b180102010506010e0f04090b131506140112020c01050c040f0e04170309030c01050405060114120d110102041e080c090c0412080d0c27210303 67
    0x4109400020000744039000b802e0181c0c0359050005804800c40016403da03401141c07542d002456230b480311215450040d0480c400428080d0000400360960f40d508608880d044c5d40c07a08180da40b550b84070040050150030551011070704001402101c2ca005c42c0314500c0303102452180d060021000f081d8407800029810340b0120b21200000380424140400c1032003059001d800340c102c205400401c08038138140000303020343c082c0354400440011950001d2050302980c001810348130741c0b40010020302d09800001d00802d130040d4000d401904003945800b004e0b0103841d10b40c21400b40240c4c030035003079604042c2c008035803040316aa144c1088003040320503400703590081c420b5820100d07411500740311294440d40720307c03116000d035400d90040f21343d109204c1c02040801315040b61004880d15080105018294810302e427003032400d1084c0303019420008004c584c042a240880a40c00c00075020b084c24201002403020f1180700c00030141c017000d44903801c00f290710601281c01d0f9000c001c04146101c42d50708042c400c0d404a007401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 472833120 1250 472831870 472831873
    0x30703020c1e10020c030f0702060903120d050709180b030c0a0e010806070c020607060f02070f110f10020c040e0f06100f0b0a0e0415050a0b12180706051b 68
    0x82c0642201003551905a0002104030f2103240032a90180030103108448504000600540c1080202c180803001d1f984980f60880c1c01c06010300000c0304d5900d08100310300d4541d040f4080d55450b8046c4c0d005440490740014510010880501c00400201c0346c9000c2d240c510100e225000316a42066501107484c10184080c00c1d5080048003400007124104070344030a05171b03400700d41540c2294840c00011528003400000196001c03100700043d800281840d0700c410300140c1041009400c0408a4907848920000708105503003c9894030381011881ca031900c90704500360401c07601500310003000a0000c1d9660082d4007054007542c3c3e81d42c141d60340743c8020013034002d002c0ca84808031101c500d030a504400d084440c03842600c0540c5490940131410790000d0f810b03100301c02842da484110318444142004040c0607011500ea81080d178110b03020410383c0f94201644050728500300800d55a048910301c001034001c00034401284074600c0c0720103e61004010603010102c2e03010b40740403074031140100402c5800181c2072103c0c421a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 472834370 1250 472833120 472833133
    0x10603050616021e0c060703092310031e020703020a080304140f06041505071b080c10020f071211060403020a0209010e1e15031002221a030703020c 65
    0x4801e0202c5040c0c00c2006180d007602c282003200c1d07200d11212511521280c0d050381213139020302000d04001e0041d2504034001c1ca0b010b003580350b17a038520b19000d140d00e400d41101d407a80e0807512081c50820b50300c0355284400b140b031308120683d10042000d104003d800740d0760703102580002e000d40c2030500c02c0042c00c03d010b4022180781da4034149446c103c0b07429040120b042a41d402184e0700072224039000b2500d01c0c070030780e00300c40381c5811460325440f01d8000b80300c014011000d2049000f4145ca100c800351000000c1c20b4400d0703040301da0741d4080010040c43d00c020420035050b024010402090090011410703108100e5100100320303080c0107941c405407a80d010240701d000310361160300100b000f8960f000400c0c2400341c2c003d4441c0c5a95980351800280c11400031500900440041c40c2c0c0760340300d280c0d00100240d1040180c851944502d001100007800d001c9040300d0110480e4001c20a210504454000c451b80040d106d1884040c162802c2d02000301a40c620020944011000c0f001401540c000d80480700741070580030a8504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 472835620 1250 472834370 472834381
    0x10c02130b09180a080703110307140c060c030d0209040204030f06050106030f05060117151009170a0b040b0a0906060924050f06090a0b121f060c020405090106030506 73
    0x24144181d040307100340a01d0020500d0b0604405603801415103c02c040c3c00c16150b0b42d142d104075a40b007039000320b08001c070500c0c45952003074051020f040b0061050903001070000000c1140b5180000801c41140b01704070400c07a01d04550000400c40e136224540311000350700e44020000140082c0181e900180807851742c401841d040113103136805503040e00c4e070707070345082041d030050003181000c0b0703031045441901051800c1ca01441006642e072100b644210340751030a202c007134440004201c2c010101900c58000c1038402100b408a6030040e1400c1072160801001003150440c291542c0c062036a015001500543c2c0440c0410310220141d0400300c3c50a801030000d000c20b6541d11514402807070506c0c3c117107551b420b40d40e001084200c5d9182500041b075400800c0c038681190ba80d002c20560b54000340c3c0305680420483c5000812142c044090901e641d030300074100050340380c20340e40210030142c10101180324540344601401183d40100e400c05126030151000905580c40206540c010855908050300c640b065000b0000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 472836870 1250 472835620 472835659
    0x501150f08100f152d05090f1801020c0102130e04080f032221030b0f011b02040e0d1209030503070f030917040609081203010515040905011d2a09010c02 67
    0x1641417500c0d00d00d04541d068405a1484403009001c0c11745e100c264036002c20b5031034030500c000c580c00054031402c041554094911707071800ca038003040748604107940100c0e0f40c0d03440c003107000b0703c8900400500061060500c1e00d43d580d02d0f04c41c861020503641090011020038800002d11030078a05400900780803880b2800d030303401e006401070240c8882075014100065560b080030711074010f103c0d42c40d1000d810300ca01c0c0410200103549000c0745480001140340e05804100c0947c0e194082c814070b8200d22800b82104c0c1080201c010b01c0410401c0c454901d403820300e001a00001c0d40401102c1d4060140e14140700a4441c4940c1107010f000b4040c405410740510300e074030401081ea540000d1080f66295150400305960301c000440d00d131001080305002d0010184010801800d000881d002c0603043c3d004120324260329039118104582080c0c001a01c07100b008507600403013080f4010140c0d0050a4071030303081d5290580104000c411080300d84250b4500e90042000356036a40294201c9880b05d43c0140440212050000c041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 472838120 1250 472836870 472836899
    0x360c08060a061502070312020a0b040605040212030705100510081c031a030a1713090f1406030604111f03091a040302030a05071b030501150f08100f15 66
    0x4119242c02800076611103112440740d82c400494000c0c0c10b2003451511100c6142140c80c50b10025030040750011000114074950b446d1040b03118840014142c100340c0103100c0500280911901c0c00d80c0100129000b14030006801d980002c1c90748004205503481d014542c0080000394406602407142d40d0050401d18802003240b880c0002c95a003c01035440540040500540201c01c000c1e050303000010340c440483d80501e0b550001c01540d00d0480d24140084040102d01c2c040e540c460380503641e84803c181107455150003400c41011140c1e0301c0c4002810260002b90f01c3d22000380004240380c1c0e071000401103c1e22080c1180380c40c1d0402c840c0700002501003050180c0034010568088a200080c0840004160207004d003060140c2d07015401542800240607040d40c0f40c0e401010181c4641404051200010010814900140d40300748000b10750200c419030130802c1c034403054201502c00c06094506100c5a00001007e500c810348041012821280b4042c2d114000d10f003900c5805a00b001110001c00e0312807820804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 472839370 1250 472838120 472838131
    0x2060315153103142a0603010b090102120a0c21020319030f0507051c06060203250f0807020a09060e0a09060e06010f05040e01360c0806 60
    0x64103000d41010600482500c207084120b1406403201024401071a4501c21a8050301c1516600681c0280c40c0d0b16640000909913515410513880f001d00d00e1114907001310b054040a410300d00d00b40c1c0404001c800507041c1e000c140550b41580102040d20b1406170300c00c004400b0f1960109840642e11031107460010984200714400f5652440000d0b12404a601d00b094011481c0e83c00d41d0240d42040d408650072038049174800301c200d08144d180d180301c8034045540d00c00c041c000d00d1692201c40d0398600d080d9220340e0080a103d034588a040c03071b1172401c224407034002c0210b5101c0e910300d824904802002c0200b40222001c07902d4050588007102c1c50213010804000d0040c0302d000e0084942111703d69481c0340381402d9801c28082c001211800d84045074000b240380d00080602c9102e1031001c40e204030140600d91a0860992000501c1a00322608201038100340c41003004100c01c040003440032611024118142241c40c1c80d0f1030040c0b5501038140117060404040900c1c0c8650320062221034950389009081d41e03240c0035183c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 472840620 1250 472839370 472839379
    0x4080310080c0a06030902120d021005090102180906040f0612141b0d08120a09110f18060f10030c0e010c03020c10021228080408070f080702060315 65
    0x86801c01c0c0000b1458110040100312201040c10711100714003520003450102d0304040b11034410b010b00700c0c0078012080300d140d040d8010031102c08410603203421b07500c011388030b1310882c0d2041042d0131101359503c0328040780c0031055500c08400c1e00e9450200e00100043c80800160b54581000407072500307480144482c2d00c43c010007600041c2e21028460307070f4544012881d410b00600c581041300b503081c1004030452420500a0000d141400144130000e603c15108480003540d0b00d55840042003000070542d821144507000355120b061012110011803900b10340000400408266000060010f0341d8103141e03442e030310001404108006001001c050003505030728003081c020940380074854483e0b5100301c80482c0d03000c2d0154000c200d255512014801d4099900c84040214025401100317034241d6044000c05d43d9001510740c004286038024985a03482e9940ba0262081000b86814000461b003031600390341d80941c00040303900c1c242185140a0440e84956400250421004420011200d81d1143e0b859100712090341e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 472841726 1106 472840620 472840651
    0x501031401121505130b0906010b040504110903010c1211030c070305070c1707050102060a0c0801180b1c020306090c2107080703080a020f030702011d060909040803 72
    0x21448005130b0341ca085d15100304041c61032400d90041d4000301401c0340d0350504e015000c20b803180e8419180300f90303101c01002c0c24026800040300c0300100014000c2100c00e58a080c06460800318210160440b460016003024180c02c0000b224404c4035045007441c0713000d644e070350165015002400156045201104c0c0810042c0546054410300c03401200109502454000024582140105540034950620313281040c1980c0003040d42e41980d81c030600814201c030252070303d40000c0800110255004100300304c90070100302d040c5d1034000703414001d4042d2200c9544941c901341d40d810000652a42018010815251300350a001e01405d01145901c1130b40c140955441d0b80c81d140000d140c00c161204000042c1c0c0100c290b80400140ca920b40100028504254054001804c01060b1014820510b0442d0418844541e01c4404450760030f10001c0400840c0d0510f81001c00341500100c03040200e5591a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 472661870 472841726 := by
  have h0 := BRFrame.cov_init 472661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 472661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 472661870 ≤ n) (h2 : n < 472841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
