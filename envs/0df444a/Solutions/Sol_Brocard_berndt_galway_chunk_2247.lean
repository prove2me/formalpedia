-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:23.39398+00:00
-- url     : https://prove2.me/submissions/04554e8d-b79a-4117-a709-a63302b2b009

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403956834 ≤ n < 404136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403958084 1250 403956834 403956841
    0x307120605030c0102060f0406020c0724110d030903020f01020d240506190e100201140c0a140906070605010e01030519020901090b13020d0204050423070c030c02040f05060108 77
    0x20301190400c034000068006c4c000c0ca940b1011044000d07000208100c42c40c603801d22002803113080c20070404018000e5902c1070620600041c00809010092100340800c100c00c0c0c4400d0008403102003241c0120084508003c0740c1041c0c07920301039041207000a10000b2030740c0702040c03100580322681c01028809502c94068005c0c105e440b46410030021190284541114040004080c111300b110915400c0303840300d15005100070f0a020000b807514803100800da0050b174540001c109041144404960040402502d5a18050b11900b020b05081d8504c140000c1c000000300303205050351220f000701c4001591140081225603119052059030701c1c0c007808160b0303d9100381e00c5000c1a000d20342c6a01040150003d0041c410b9a1074030366654003420751400c085030030002d9848079508601e107034005401d0520f03240030050780f1035040005200c21110804001128082c481080b41e0107101c21803503141d00b0442918002500900ca030809861004106400a412921301203600c030284e45540d2000d8001c2000340d1351002e4544 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403959334 1250 403958084 403958089
    0x170109020a080c090f18010f050402010314160c05031201030302070f060302070f1113110307030c051201090e031e190309050d030b010c06020d060602061f050103090c0b0307120605 79
    0x5855202074001c055080800c176000100000c1950002224032868007125481d108542910104001c0381c1c0503d4981091000310340c4c140c00b8034010104a003880003002e1400c0805030044015103845182407003400840882885005d100300c80c80d445101c00701030003959503031038002d548502c14460600001d491280c0412024864001c43d40300d2604810f03038500c0ca58090721001d0041200d160340710707417100240c44c100b0b8600d2480c2c050030a068144c26011070300da10b000708002d025100c0701e02d03a04d4108003041059082d0031040da200c260549584e00c40005091149001d01440e511540ca1055007400040e03420a06500e505401001c01c285182a03168111000010907825140e8039000200240c00404c0070000741c41c403aa1214604c000c0c1490088190402c3d0b450307840481e400040c4032207a0a480d000c0a01440303030100034450b009001070400045202d40603000300c40da0815402158101519070280b002482003207292107002c0c00304090000d590303060011020b08100703080113220f042d02c0d09250700041e0f1407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403960584 1250 403959334 403959343
    0x70e040317100303141210090b0a0515070c05060c010204090606050a051903150e180d091401020a0209180c0109060504030b060a0306020307020f010515010906050a09170109020a08 79
    0x203000c0e4030103401540c0d040d44da054803e000100c2841d213001205004400c007030040c4100c418040c030380555040540c1410300c605a000c0c1c58101c01068001c9010000400654484011904180001e031464986030905441e200d8842c0c1625070109600802c089030020783c444042d40144201c1d101c01d201044580c0c1d6880c000e40e4a4000d0114030000b145052003c4180842c03070300d40c1d03000350345100e00c5c00060b84820310540b501c1e1080d00360044101c10b203443e801c0003413600003070541084000c0341000502110616610040204000340105420b88104030007001320b0364002c21200780c02960083c0a2002460003c0d56030a04079005011000785104004d0840110750003201c0910a98410b135032481c0c6400d003180c8603000b4040e0050100703074218180b010000042071503071003d03502520340c0340d014104074441d2410103803d643e1301402c4d0207a80107618501039940d83e08040c140d000c640c101c0c18241e498142c02d41058034905484c8d4400504a0182d506d038924403030303042d44580c040a20840703040e511607850b40300041d660b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403961834 1250 403960584 403960591
    0x50a090909110915030106090e1b15072103050f1302011e052106030d030b0604030221011b0212070c14031e01050a06080c09010302150c070e040317 65
    0x350b018845400c00c60b08040000f281c1c420120318650721200c1d258004a405c4800950061006650321103000003015020f025840110b4082c0d2220030042d03140348000740105000c5117654081c08000070b010006c1200e41e1207510303c45a0954030b001c1e01c400d003501c4060080c0008a680100340f542900004030f004c604040203114154040e0369000e00502d01c01c00c401c90042521450006008050202101900440380c1d20f0b0706004884405a1440c00c0001c1130520708600200003400b41070030001c003e0b00c1529840180d82c201c9804503031414402c03481c010088040321042c1c401c4003841d400c1c07503401e00c00f90032600c660641420965088562907800100d00740c15500448034010b12162958808100001001403030130041c12005081c1c0f1a803619101c8021190217506d2141c0c4800e9469038200f10b6100854800c3c0350040c0840b101030202202d5a6000a0341c641d01404024800c10020305010440802c980036105800c140d035081710800c54560720003900d0404122003c800188051003400119026280762600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403963084 1250 403961834 403961843
    0x51b03070f0e04061a0c060601050c1009080702130e1c2003090a030b01090f0b011710050406030b01140604051f23030406060b0906090904020a0312050a090909 70
    0x80c05a24608126104618810b909a2290b16880042072600700030868400c100440c0a5299584000a018600303010b0014106414000f00713218110385180e01180c000f0003180740340f000040d10011840c08001c2d0380202407002e0340002015204003500c40300c80e80700714018440e4504642d0102210718005100c04504606040040c0c08000c402d0b240c0c140341700725841e1000b0303d0000d480c1450441400b260902e603072a0f0058840580c1c600c01000003140c540700d59a14541686030a002e20040c0100190549440c00080c41049103c0000075543c1f03007002056102034800240705001c1981d4074104203030b802000f8002c100e01040a20205011481c1c04821101180c0003e0000c48480b0000c400d400340481c6600c0c0407005010340c025190300e4412034042c2c40001700700c24060a40d103074101030500d03800700c510541003421711203420005080c1c161345040a0304d40408085407009443d5485101081038901d09034401483c601d0410640d454084d00310020341205d408035078030500c8084d6583e548400340c0d24501d40151 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403964334 1250 403963084 403963097
    0x10513020f0406030807050601060e032407021c0903060f020414060d091e0311010e070506160b090102270a050f040b030706080603070f0503100902010903080d051b0307 74
    0x401801d010790400e8105000400c00a83c0c030b60b40340c980d0f41060380a090100c8071a0000c1d8014000300360001c6240e00301002c150005c2c0311900010880d101c000151080070f8544100b83c01c00910750034400c000c0e000703940b008601869040e0303114041c080d050040d40d000841d01c40d410a03002d448441c001e4800c0d42c0840d5000803214141001410500200d035101520700280903480703012500204020690440c2c0c400c050506528582109044c000d040d0001844140d0b51030f410200c804c6449003000440e242030b83c0084400d50395502c9502c0c5c1d605880e02e0a040004c0581c4690420040d0f8100198081c03d110300e280720132201c0000034400d94030717401480040c4440d4410300d10682031006060a03207030320144c118041c00c0014a1060700000a00c1c0800711390040d40016801c2040000c2400c0610069000380343c00c10100b84030360709240000b0740b599031a47c0d1480c5007a0340ca040c0002568802c1c01194011034111342615a207110708904c3d80090a802c4544080c1d442a4000082603800c00004a9100b020b4030350700c19 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403965584 1250 403964334 403964371
    0x21207050706180e0405060601080c03040b04030807020f10060639020d0503071110020c010903020f0414010b070221030904111c0b030705010915030f020d020a020c010207080105 78
    0x1a1050100700c040c4003500709410030f02050081120040318082c0b4000d10040c0098070b410000180480d40040030040f0948041c4203000005a03030000581c0c0080d41410180e43e1540c0d01e0400301d03c0d21040100440c2d0f14401c1c6413100e610700c0708903400070702070300c10603600c26981d0540321030303d4280c914110310b11580380b04030300b414012003889101100401c1e038801481411282d0481e00e8280c07440e040520709076850401030303000780e03070703901c5e1826000070305051a001a01003c4600c0c00060243c5540c0d1001038002c902e9484041c003550713a982d000040195611001100558403260303c54225081040224011550007140c1c2c0408086404010004139005004600e0120b012051102a000e88032940c0341707604c0103206140311550a41000c0c81c004074543c03800190219890101417031705050350303c902e040c428009010301400320020300d03031501040103050100d440f46c0c447c1c0d2820028851000c440316000c0c4003003240c03d005540031a259440781c20036422102d5498807400124200c1d88140ea1800e10881000340740e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403966834 1250 403965584 403965587
    0x40b011704110d1703060a060323041401020a170f0c0f0a09030c1e05090919030207090606120c0e13091403070b1006142a0f010606021207050706 64
    0x1100542c20001d030030020703001e2207560707068950200c003600c203400c0703540201c204038a600b4402e0b112401000c1c070b46130030b100c810b411402e90b14044910b41d101c9076451001c200010f003409070f900208541c002c04d100003150303070300090301c0020030082e0a050411010358204010417001b80540d06a107010340c0404002e07503e0031307101040d85542540102d80c0e683c24013808040000100d010a80d0050040411030a407100041d05028100c4070329500d40c01c8142b0881508060060224000803421840480e11454090500c3e070760606a20b00b0761b01c1c1d44110b80f40c03800c00c00e011030452390201c0d2022880c24000014800709562400545800b00b41011490f00072410041c4041e02038425002100880d014190000f215030b5610081800c0d544040010340e41400c0003018464031110719201c480042889141442814240341244007081c42080c488281c0c0d003803c2301c0ca0921030714040001c6a05c200000c412910200781061066000e04042d204071405400f5083c2070303000041d021011141041d038814090010300382000700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403968084 1250 403966834 403966853
    0x8130507121104060602011a0402040308040620010204060e040509061501050a2f0c0306010612020702130c08040201180f0302040507021207030507050d0f05070f03050c011406040b011704 82
    0x10280e55900e00c0304020350290b02da511a6201134917060b4004180d444a14003031619400d540c07180e031402a481080204049846502902c0584883d0f150030203503004d01085031303405941140044003581d48002000030300c05400410200c40d403034090744c062045503101c1842a4480b03004440c02e041c1c0c90aa42580740d4107600c694001c1102c443c2c42c5c2401c00281000741080444c20f00c20414210340000c144002c042c0c406030403c10210781c4d0b10300b10f00400c039946c10000b00411800c8000c2c1c6480b0001e1b00030603020110360b60031949401d6070700ca02c202001071482008000380751030b1042d5000e90200b41c80803550b2000c255104002c00076985402c10004000e46183d00303000007040003c18020031801103c3c2d0700100d890142004141080c029501c90b0784515050501e541801d0980654a042c0204891100c141c2c64004007520b96454000c0c4982c0d0f1403000c00d007400c4d6118450f04001200130b5280c0002c3d0040036840b681003602449003503d042210700c11880040d01c0e01c100d1411302c0f0810741d0311303c40000c000a90744031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403969334 1250 403968084 403968119
    0x61311070f150608070e0f1e060d020904060b0a05030105060a1802070501090503071415041b0510170a0207110d0f02090c0a030c020615100318110108130507 69
    0xc402d845030b0644030542c4400c403a1190800d40c4503400020040100c038102c4d00c2c403690407000c85084000f05d414010112110244100081c0c17a00e8440d000c0000ea49030340f540f0221440035009031035000c2a1802c2d00e001002015400c594a1192a42c101c0218940c00c05103d6035105890152540e000c00e820300c811485070002c1560903954854007044090002a03003800303404900da00ca10020b5454483e01d00d00000e986010841101e49030340191140d8a416865000c0f4903000358111400070750b42c0d0405c1d05408501e003e6900720075006003882e217444c4901a0b008102c211318103c04c15004200b41c440c1043c60041c1e12480f180504214047c890000c0103142907192581528805e070010420039605070301092103503108030788071400702d040459450209034060081507000d46035440540018a0003442100c1521180343c002802000c5010b61529100c3c0a07505c0b040808130108034584640b1514606a2128a07082c0e40d894005017135100070030041001c0348c1071804a80d6212014029460421003000414072030b40303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403970584 1250 403969334 403969343
    0x6020c010c02041509270201020615130e0304060311120105060903070e130c060f17070e03010e070306060b031015030b040e21070203120f130806061311070f 69
    0x8004c524091101d110001001700000c42d00890100118080030401c085005443c14403840c400000e440180e90214401d0b5000c001c000b06104030b603162001003801c180034180b1711603c403071034031400b04000c0c04000042c00888940f9034003441000b09403101004140281500c502100e074511005210702d141c0f100140c82507001c0034086400003a0344105216455030151a41da68528030145900e023404100c04030321000d007441e0b003840385114091101c02445c0c420f03c0300790000d01c2000803000c1105d4a2040f12040c055580c028006e000c020b203040541a280e840030303c003c540381c03442d0840000f41082c900050b02d10982040c1030b030210003032034950343d001d5104c5203101100c201551021010031320b0b0303920311440007050404c40041c03102ca42d40088802e455001d9160b50b00301000b0510800005980000304079034004400214540c46a9002c0c00d44a258051041c4403c42603d08030000b10324003b00140d10b5106410807200044841ca040a40b101101d0f190050b400e0750752070821035400455140d514002c41c50b48034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403971834 1250 403970584 403970591
    0x40c090c0e13110a0903230a0314130803042310050a020313090b12060c1614150f060d0804271107032604021519111606020c010c0204 59
    0x300f41c8035000d600c424820310100315640b4090060142111581043c00941003000045e00b07241100590b8645c1c101c1002010402101000b19142c40d010f0140c424029400a40c100fa842d190240c0c940c494020b03020311180040c40010703128a08100c4641d2441100000c2c094044804003d441100d4a501080100007517220800c0601205180781c2a6a801803860b42800901d10460320204100e00442c0948400f03135074080340a10102a8070001150807000300d56807980c65190300d43ca004400c10b284668005c45a00031801c4400d07402c0341178400b580c459020403058292a80c1e5010401c509440c40545c040c0c01541c00303010a2041c9031314a503014071a20b88140040c806850074101c0c1e0710603a4403000310003914013400710316202015040010000e10f440c5400040d0129400c00301d89480d0401c1c003d10103480760001340402015030240a040f541840c3e004a44280e005480c0d16000e040c10003092500c036003511403040611140001140010242c03050765000d8201c1b4641c6400449165181600582c1e21a54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403973084 1250 403971834 403971851
    0xc031b12160f061209020952090305100e15070f030c03091707151514030f0a120e0607050703050105180606060d090b0708040c090c0e13 60
    0x150080c140010018400c4005006040a41c002c3c130400010f0300c1e840c1c44c03d051602c40b00c0142e9407400e01581c8118145103909403420b00c285001d0403502e42d00b00f2503c820701c4400e10140c4103507030100c1004d5038005080384603252945200c01140d5418440c40090407070781004254820300d015540100c106d039000c81c800c60f13500303840101c0925200001954890007245410030a0101c060f0980038940c1c8040b1203017010824580c09450344c89041030b1601617880c54100010310380c0704000341d84244202030126000100140e01500421940c900d20600031080149001112280940343c009122803810140030050a04601d00d070b07480f0070f40d40c0c1000000c50248844010414040c1e100c100c0a03200560080000301602441e50402c00d08480000e002d03508040e400340402c3c002d90744001b070116007026041d40c00c50341da01d12840c0510000c3c03000e001c0041c01c080c0c0080c10300c02c056500200f81c80c001e074019103400a8207a40d54000c6000c4078000035031000454211808160303d860040da800c0c200401c40c4001040040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403974334 1250 403973084 403973113
    0x303021c0516201f020f040b091c02060d0b040608101b0516121716020105060102010c02100b120601030b09011a060313060b120a050c031b12 62
    0x90084650240420741c10607603003201c55009481d040d43c2284034590002e60b00c1c0b11512542c4810304620800d2280001985038188442a80e0407141c682c1d0451040303946494440403030320b8072a8071000b0321500c00c9030341c00c01c1007041002c12001d5601c4140c0c0100001c1c5000a14500c1074040d00c5983c001a82c020758840c0d001800c90402d01051031281038600c00091120300c06d40500c1000305a4001180c20804240200d8102640280480f600700c0d4021040ca20640034455045548200030542213180c141d10300c0622089680e03030400fa1300341c002550024040d0b03a4590004908880b004aa080f00680c00824007001c9851154070904035a54054000c1c1c007410010480546040802e900454424541008101c0020000c1c442c1900c000c45280a055500941c0c200281290002505003103004803000e841204120980c0d1086107054806003448046807220005c1d0b603101d0004203804d9903280500305014046180c0844d010010905544004103006c003550107010042c1d0580c8084900c41c41503c87c5004100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403975584 1250 403974334 403974341
    0xf0606080601090903020610120807060b0a0f03061a090c070215070305130b0702061b2518050103170705250611030a020c060c07180507030b0316030303021c 69
    0x7801d2000e000300c4c103500a890020315143d401011040c849100890610551002c6c1003045049078200301c5443c4c460f110342c20484010501d0f030f4109030380001115800101030410110020499014000800107801d12000b1280d401ca10321b80b00c6075021061342c0000d0010b80c0f03541c010300805400502070012420200080c040103070700c4081e0035000300d103000c1071210700510301c1e101034006001c06a485600f002d00b1341c0d0215029000c0e54122a80391001102c010401070020084138100c035500640e04108807400c880c5070801141c2038050992081403890004e961640320f4001e40e81240ea000100c0c0810803000101418079130030100d0115154050440c0c20700c0352580b030f40c10a00015103107000d000d00e0113181c180d0141c86582c0480401807240c0007841034020075a000b0910705d00c0e6240544907650340b81508801396081009a41201c012070010541007415044c1e294095032148411740c6040140b8080c0008143d91101d5002d070412a190b0384144c18400207120790003800a41100001d015100c0c0b0180e030303c020030b9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403976834 1250 403975584 403975589
    0x5090312040504051305030d1802061204110a0f05060703020a02060c060f28050405030d020a030f0b03121903020702210c010807020706050c0a0516090c020610030f0606080601 77
    0x900301150600c07803450284a8113420000c01044034001c43c0c100c0c0daa10f43c91340248000d4000041d5290a0032004114403d880a012540182016581c41303040000084800061380c00b0748410441c241007040c142045002d00c0242c4101d142285040f524020070040150701c2104100d0440c00b500000a0068a804003e054401c00407400780c2800d00d8050074010b50020000e0101030300c6c03903c80d000110a404915107081465114103000f00b85641d0307a050003031030b501c42e10448240344e41c40013451385c0513194940d00085859000510520000c041941016547c028000000c6407046080208440c2e42520b8003401e40507a540742005420300c8019000281d800c2921440c0380003801200b1203c081951041c404030580d95030074200b0740c09600f05024029035860071401000d081c4100001c007051030b00400c0001001203075202c001c4401944104100d608400c00522480c1305090908080000d10350000c58040d02c550743e10303d0f070540c10a14588400b0f40c000c00040c002d46040c5e5840340007250454051158502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403978084 1250 403976834 403976863
    0x6050405010b0403061b0905040b011710030b0f0c0a1808030d0605040b013b0409030e01090e07050a121d011d01050c1623070303030c0215010510050903 67
    0x1151441c5007001c105a1b07900c010403020803d80481da00191540000e1020152030003907130001803980f841801070310f410743e10355110000c44101c1c87c200f0000c04000c01c121000d90344101043c002c02c0d2503941c1c001c000f140c4140e680c179260b40c4043c0710b00c00250784a4040c0c400d0900030440d2000c6a15911001c2c6c1d401d541c4260b0700100d51980f140014440c43c241801508403d03802071824076000c0300e64080401c0d2506421030355280801303030011041624240720844a04601c0e0062080065809038980034000030300c1c00044a000c80e00c0b0010024a810302c0300c41c103174441c021948600380350000146d405c071760740d50480314035400303040e0b80e4814520781410b034001410403e0f00b03606c000260790300000245100003e020341c001c2c9007a8145801c04c10a441c0241c140d8441d030b1420403815000360f51520385007110904000208402c4409038100448425002134039200b100e0081d01d0800800c1542802280c031340c0d0400c14102650001c44004100781d04000915800c02c0c031603441d1050130158180f00203424640203003072040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403979334 1250 403978084 403978087
    0x1506030303070c241b110a020108090a080d0f180309151106100f080705010207030204050402150d0c1412180102041e0305010b04091e05030706110309060f010501091806050405010b 79
    0x4517004034454141d003619040c014135000e10008000e540300e4068a00038104482040031400054040141015040e03102c65644d0319803215130440c0300146052130071030900e98100303600e000200c1ca14840a401c09601a621310303003154102603030002e962000c0070310341c010070550719080d080040301841201c2c0a5480076503502030403854902301000c0c55200741c101c0702c0306410800040205a030005240b2044960550303000c40c550b5144e000048900650345030104442030001030024000c085944100050449515500f20f40314a03070350581c0050107105c002829481c0743c0d8001c41c0940813001030b2020014441800545001e440388219002e110752255907500184200e0802e10070080c080c05a10a2008141c508000140039500c40031080602c075400c0215507402c503001c010911005000b2200300f40e8021070144200521060524116481118061303418010032001c00c00c01d440d2030140074100c0704140d5030802d12078100b1014442c0031400017000640196509000140c03038580c4c2c00b50500920003030f100749 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403980584 1250 403979334 403979351
    0x3090b030c030603010b0307052209080a0c0c0f1a03040203100608012711060a0201020c1207210f030b0a05031c020f060f010308091c060e1506030303070c24 69
    0x144c2912005403105209403c030f23940c14001c580b1502034080101d10140080400154107003a40401406044405032041d900050f2500362141c02c5181070110074483c0b50902c407400d0383d50302c0380c0c41161164040e02440c040b070414080d0900e1074800286420900042c1920081100000e40c0001c940c400d900410059450300001e51802411264070381d00c0200901441c1c0500c0501c1e581d141001103500d410030312540000c00e840c01894400d6050301c40040d5040100c0c1c441104240680703003183c00a8000b101d10034880140080c80500201c00001000038644480d86401c0000c2030075405408820f01464101a94072400034142d036040054400b5080343da5a040d607990b503454402800c0110300102c4c0c0c0025400041800904c110f2a40c2c0241103c1d08241503d45641c40c15000440211000c0404030103400703901c440400b07200a6910008603038204804031a80100060081000c241040f62015032541043c0001032440340111040240c113803007503980045200f121816003040a449440d018445075803101d41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403981834 1250 403980584 403980589
    0x90b040e0f0903160605041e060b040e010209210304030b09030409180b0105060d020c0a120810030c15030204030b100f050d030905060c010902030a050c130e0618010f0c030911010305061c03090b030c0306 89
    0x500ccc8a10302008000e40c81c103004a400710300604172000c0c6950149141080000c030000081c0140c07409180e2040340c507802403d02d6040700d80d0b030307400500422540e246001c84424444100c140d054030881da2108042100c1d0f86001704002035508030000e400c1d1007503020088594607450601c09040414070644400c3c00e400d000c58002040741c1002801040601c60303c690038004501c0302e140840885203800f0151000f4101a08118040c0c01075900c024200c800381004d11941c4c0f890821310a0a1360380381002030340410303541d000b0012000e8588402030042182d984003440380e810000004c00d803510507030700007054050303c0398082440c1c6020200f080c1e400390054802000b2903d85007203d071050b5442100d00f800f02c800000001c40d00e40707401901d45800440ea1000307014890500790007004142d80c0d03018041044029510000e006440003681c11504804980c040070b10560092003801e0040001900c0b00f102c0b1140e131681c05507120b110075015002c1c00106400001d0011428005610a100c1240c225407681080f005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403983084 1250 403981834 403981841
    0x100b28080c16080f0703080402010e030102030c040e0a0207021503010e09010501030201090510030e161d010e070c05030c070f24081501090b040e0f0903160605041e060b04 75
    0x98041219900602002070054001d841892040303440e401105042440c00624501c21004004450080401e480c0241030b04240b18900c914001c2e00c2c1d080444203880c00b098201c0c40100d442ca40c03013050900c001d10a40c1030340c04045500100b9248010300d0a451038000513100902c0000740c13005810004014040400d0029180d41c0000b490b900920a039415540003800e00320443c05103074000ea1030044c0c0742000342d03c00c2e00480c0c0d80c20f2406003074031070b41e41000500300c46000c07d46c0919444690003118002c206400280c00380d040765024000503d4a459031501150741300262101070f200d0f072100303012207814010140a00c4d0001c048034000d02e031101d0301e040785905850012a07040e2504910100c8142d0703411740c01503200c2e584081c1c030202c0b080030781d150007005891303191094001c06070b00c420228001c645090554906030281441202501450340c50308d01d0030744c1c0c80c82122131281100300040c2542d8006119a0001c07070300700e4850714805040c10640f1045a10320300954006480782c0d91200350428140c10f1912 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403984334 1250 403983084 403983157
    0x3180a0603090510020a18240c12050307050c0102040608040c06110d0e04020408030d0507110712030f050f0a170105010c03052203080a0509030d0521100b 68
    0xc081c04410b0035074641c40c1d103c150848000840b1900010130100c5548100c140c0620081c04a194019031900d500c3d0320802c4401d400031007809900f48800c0080814001c601c00c40724241e0003040500246500801150b850308090030b00410f0182c00e03c821550343c0403c0c00030304043c0940f81c1c0c03001003a207454144100354020310340c40170052140041c0340041030b000125000c2c0034140e0300c0c148501700b8141400881d00a100750740c0811442e0101007241000d5106580001e0b029501980c0c0e03290190310b206100075102c07010762040b00c5000c144507000d032000078003901071018051194100141072124620740340815030711042144000405c10000440351062a48039540904020b28143c000900b41e654058010300c91440740c00c0302100a80496a1291811048100034590003070502d62200d9209030041c1254010722031843c07090240180d00b0107410300c640142c45000b0100100070300341c07010302c02c142188607a0250824200e55600c0502003909402c48000300200340d5940b00760344514844e024000d84105204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403985584 1250 403984334 403984337
    0x20601090e0d032d200405010c0303110912030a120c0509040f0e070b070c0501031107140a050321010b07051e0102040e0c040905090105090615030f03180a06 69
    0x2100d600c200980000380c0c08001d0b03501e070800151078152030011103003603071034a01c0c80b50500d00761200020807030501d5003288000d491100414041c502c00410a82000d000b02c0c007510340004c203006074640209100e44c204240f00801c0e0150207103005808000714204401c080c079040381541c030001e51f4090040c0e00100c5030a05c3e18240d8010401c440d5030b800000c0c070034855040ca8034850303600c52803500325500540c1d01407812541d8a500310b91141d80c0e58032034002c60f81c01c2207030283e6907804815000642c42d4086e00510810a1040101500d41000780e43d51107006140003482507810b00c14140c552000480400080c50800903200396494410b088031180100040d0580200039501800c0c80300b04002040021415526806420460102e00750aa00785009004c1c56008011004d028802c1c40400019000103106a5081090500c401c1c0c0d60803040c40e082c0c40301500c105c1c203140e000000044411044504101042c4001010344004688118450f80703140c1010781d001c488100044d01c100480e1a00120341001040706 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403986834 1250 403985584 403985591
    0x109030e0907021b0d0c09020a260f0a090501020c071707051c0303020c03190c060e010b0d020f01020c040f020405010e0904030f0e0105090d030c02011202070809120a080c060702060109 81
    0x2000c0340c0d0341001079a0710445009203041d10040d001c1281b001d0141c0098003c5c42003c6450b00f83e076450080c11405800c10525248440b808605440e141700f2240601c9245040e40c00111a190000400e0060903080030903202035500f4000e01e541c44000744864801030a0039903424940c1d107d102c0f207017800c0404503888944504405070202600044079002001c00a82509005031220200c540060075413180d0140383c41d6120a000301e40116940103420682c003207020306410020480c201501c2401c0341c0c030151049034400c0d5032300c10358070044c42c201c1c0340541541c2040c81a80c640c0f0440c4400308040e11240c2040035a15500414203002c0d43d6030001c1590109002152142c200d803c041d100504403a00e59840b420801010164054041c1d0240044509100001d0048000030085080050003c080c0e14000c900054000002948015045c001e440d4402c3e0000300091a0a40171020403c101c0040d003070800c0240100341d40940420010009001040807038006400b4078546028001e09000e0140c204ea264a440e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403988084 1250 403986834 403986853
    0x24060809070f1202010c0f0f0605010905091011221703040e0c070c0e0f04030806090915060f0d05031b0102190e0a090f020c1209032d0109030e090702 66
    0x602d9611011211810b0200041c1603560004844960090343c018102134200200314040010440ca43c50145008500c100050307600d8a81440607184140d40c40d0302a03900c5030000c4a00c018040c0e20003004030441c16030711446d120722034260b8110702c2148100594401c0032840d04008012070410f10345a0b031310404015615190030a9002044094040c1001504800104180042002d50200703030380036040c528814001841d0074400d410b05500b04031004c0b40000e000310041881403d0400742c850080d60300300058050005c1600c4003642c803101c000c00180c0e22908101800007143c07200305140032100d004001450750303000848928209007501c40a07001c400d80c41081076402038540c0306205048810b01d86442c1d000b510945000440d0314500340c201d20802460108a10f00340200c541c010b1902c0c10b4460705492604401062142640c000d01d018103825410507800c04642144170704105884054214a203402007031014420317070844840c108203d01103130100d248203140d403805003881d030340c401030700d100800100740f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403989334 1250 403988084 403988099
    0x607020d0311010902060412121103030109090c05040e010c020f0a020918101415030a050303161b05070f0e0405071824030b060a15050d2406080907 65
    0x4000c030300501000410039442034060429040240c0c22a0000c040c1500e036a26903000817030b90303034a1032002c8a980080d001e80c000070740e0151040c8a903902943d80a1030070341e80703400840000390000c4d400c201c0b4074803202580440d25035180e01c11940b07403c13051000018074002c40c0c0c2010340341400202c003034500e41d84448903000040c2d1315490200d901c80d080c840d00d5240c1c213020901c040e280449108203103c00768240304003404030711482003000388100900c071200002040380c401850f460b0f0311520b9000c0c000360010000542c1090501952241c00308081c5410755581c1201c1c800c2d910302c07814283c0c9c2201c0e140c0000700304001003000845880050544600b01c101035040550790740381d50b50903a226441000d50100e142a80c107402681c08000c00f002c441c6441d0002c89207810254000c080c090108440707181c05000407540700c0c03c081c40000251800c021043c06900965541a2041e402c07420150303c216403561808600c2200741e412880c101c54041c4c1070040c1083c10701c600500b00c0e4500421000c41070f0700c1080c0811200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403990584 1250 403989334 403989349
    0x901050f090a030e0604080a0308040c090605031b1c0807050105010504110a032705160e070c06050c04091409011b0c110a0f0308030403110c010f0e0103090507061d060702 75
    0x8030f5040c101a20701d164010041040c03030149070300400c401c0c045c41d8888000d054029480c10b00c143e08c40c40d5050003107603c0d5041d11080f20081d008450701580080d001e6000d0408002c030f040d4801e00001e00c00c04080e02c800510148014101ea07003154030344030200340c600400c00240612070150908a40c2805408803402000d00140660001502050348480d0900d120b502c04001e03000c034510a8103001215442d00d400d14035070b900360507017080d02001040600003030074800846a0078001e03030f256694286281d209486030005460007a00d02c12003005c0800000605c00510310452480e000c10222044181ca00341f0009030840324bc0f58103904d4200a00c080b034400c01a404a1070154040d40b241d5040044448800030482c0c0110a400c00401c001041801005009580c40610300c40d5200e5610041d210342036139809500d94100c446040d021038030540200f40071a0040050308002c08041c0340024007031000c1c4c1c030742d50b280456030b5102d8404039410200300c03400608a000c082c0d034401015101d80e0302c0c1044031340c08103640 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403991834 1250 403990584 403990603
    0xe1807051c050106050f0a140409061701021822050a0c180302061e0405040908070c0914130f050615010f050f0a2106032009060a05060a050d0e060901050f09 69
    0x3900e200103181d101c0540561030100c8c0e00082c1e00c1c4d5540d200e0f921004a0070090809000d4603013140142c503500d44101e10705000701c43d040300c4d0141c0382001000040c0103000c04d105030740c0c81120b49000c1c2040482c1c1070744400e200e4184501490200450103040c04d0b078019060001c0510150aa0280c02c001071001d42c41d2003041746e06c81865010100e00f20740d0110000c3d00d03903014980109034410304212015040c0440c41026068031805100140741e07083c6d0350022101250303008011001c0346120540010a80f44001740501207946c080d2010300d1a40c0740c156a02820008211100171aaa824a0b814582d5590003228003840c0c02807810000d00d001e44240e500b00c218001d401c0700c402084604001d04400d900d003028032a140a20142d014440d1039102d24042002209404140c9407050b58a44d41c4155454000c0165004210142c201c1000074205401e01c00301d030b0321a240f04012701c4010030081c2c0c00107420f4070403200b03c0355501000e001d6504000141c182580c40103400d05609180034414450095808500c0061 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403993084 1250 403991834 403991857
    0x3291011010b0306010305160e0123062203110303210907050a030b06191415040f061716021c030f020406080402010e150702010e1807051c05010605 65
    0x8200d265400c654003501c910321000d90180501400001003140c0000c0f90656981c03070b003c00b401595110f840c032444074002407207400252202000896281121664220501d0780041c064034a0503180701a04c1d100300488024000c035200740c54000b0818042c103440c5400c07201004402451a140000c01e41004d41204406e06072502518000440e400031000c0241000401e406014020300d10307500e0510200751003040b03a806c0e00581003d4420030700d0070600c400f0a02565a20158070407144091410711814508078441000300100400021130210445d00400d00100065680c0c07010b40c0758111405120140054042120100c3d0740c0d50401303940d038004c03d024182010361151140724110301481103000d860800f00e0007004901c0004c000c56607a511902030f601c603900030380303030030000c2081d03402448110b0108103c61151075005004400056109411121403110001d02d101e010191840c00d1805450017a83c24038040f810019040320038090052404440032442c0e1400c214542c58882c6c0a4150310401d045201d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403994334 1250 403993084 403993097
    0x40306020f0d1b09080a03050a110c1e210c011407020a12021f09060e060417160909020102061303020129040e0303150609120607032910 60
    0x608011207010703507441050003103061103004401c0901075003800b480c6032040300003440c1d41c402150f07841001585d00141503041d0f1b1181c1c81d100214408039480501d00320361003017030f000310b43c900d441a544849183d10501041038000400c048010100440d80a01403111010800d41d4509083e218034003017142c0c46401028201540c492902c014041003e00c110703e0f0083d400350a0b0080440d0b482c104540c25101c2c581300355140c80202a41140000a12203203602d10130018070440700a000e810b00c1481d00301c540f844084c01c07a07400d10381c0704c1c0c03005001f182c05461020403073351102e4000a0342054001554004041400e42006810304a4000030f488040040a0065142840c0807920400d8800d600c03000b10000700b6524100c4084965080c502000280c0600d0f0f8415400e02c001c410540c040030040303901981c41400c18407416040b440038803003650031011a29900000c9030140401e111024091681300d84941e54001982060184a4107010b1401c50081008038004050668036a1280c0d140211882d4042c01d151 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403995584 1250 403994334 403994347
    0x91e0a110118081b090f01210506010b0a02010c0504150e120d020105040203060c1303020f2106010312030b03032209090809040501080a020310020307020c0a1d1b04030602 75
    0x41e00c486940c801e0300c200500d07002c000011071002c00300c0c0d1046451002140110030180e00410001c0401003561041c055012030401000344950100030b10b50804603025259071141c075180ca81d941030240992012007003920004400e00c0d03903039081c40f4181e0740c0398490038110709050820800300002d1640360050360920100042d1881c0be580e440d203e030707110756408108591001404001c0240a0001a0f03022406486040003107800000c0d400c094484c80400901c11100041c03464007001800c80402580a4000200000ea900443d2801084c1289032a001c002402c0e15451031422006802c01c410900040510b41401806151340200440d07652800307480c1144101d40203900c49068156955001c030760014a40f600010403c10f20002030280300804403030400c8180e80e40c0c0050b0b81c0340d0210740c40080d8150880e2103504903690880e4080c1d50410140e104680102c2030110204000329155004503180040441300402103841019001d5400707400300c550308022140d00c100300e4a09000340e0000a22450300801c0340d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403996834 1250 403995584 403995587
    0x106170604110c011a01082208070813030b060402040f0b090406080304080d080a05070503061c0611040e07030e0c061c0501060c171801030216120305091e0a1101 71
    0x580c0020b078002443ea64003c8882c002e009080d88022a440780d60b4400e0420341c190700904025100d0f82c0c80c1401d845008801c4004006000c4c5004d07401c030b0790381c0428010f840100d40344101500341a084011454a03c60840c00d0903100c003c2d0091000380b280d0300400c8103020b10b40c00200b21004a410140c6620789843c0501c00080241002c1d0304103010300c2c84042400610300a0005944050641c1502c2d1007995480740c22269094a0b0101c8030240801c0040000c40c1030b81c02c0081d03030a541e010305011409034001d056030340c683c01e0352418581c1d0303119600f002c80e0a01545c44038144991308503840b0300702080390003403040550b6250300f85404600c1c41a200400e10142c80c005020034241c644000003001c00c060f42c0c640e00081c00e082458001078903443c2c1000964940514440122005503400301c0580c500c10500c0f900440c060340c41608141a080381944052002600010382106200090f0310003048902d444d140c420f01d00650b0180c030240c07240303042a6044860b034000c1070050119030045000380356001d00100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403998084 1250 403996834 403996841
    0x4110d0504080a0306050409110d031701080601060807020f07061803080c030d0e1b040b13050406090b0601031107062409090b07050711130e120c0d080106170604 71
    0x140201503400d01003008100039480300100304003140b41d181080b207151640207200840f074402c5001030500c61102d0800c45589419180407029a100f23250070f0701603603d4250b154044100030f9110098550000b001480300540014645900c0791300c510060007690840f6034000c1d40c030040341c46044180000a9000500c00014440300c2c0007441d0030445003a036030800701c4916a51381d409004e2950325903180c40d1307000700b0b5010301107503040c100080030070b00040d0300e100708041000501c260240b091303010300d8800c4a80b800d0006030051910940c0207a4002407491407908012000503001041d040c10103251120291654942c80143d64120740c0019001581d0300c0140d40720581045025108540d18501040c005085462508405490741c400e803000b003800d40320480c0580380c500441c58014001910b00e0170351101400d2400640301038800a583c0400c1c5042c1c0188002c0c203045100c108411410b03000a4204458081042000c0849a29140c840d240c2d41c074025008014003000c4c02510344c2c2c1070101780458400c1c4c5d6541c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403999334 1250 403998084 403998097
    0x601140d320307050a050f0d050307030203100e040b0f0a1b0809210c120412201e120a030c120e092707060f0f02070f0b03040b0c0c0307020411 63
    0x7165603c803000e0070103642c0c82051860455481c801c00040c9050ba00b8049109044030016403074203803c5031169482a8040d4200400b10113a4288800d000034820f0340d01480e260103140100e6080270070742000101c80b4072203030380141208801c40c20104000c0c1019010414611070320001d2500c040d50b521507040550400d034010b180440c07041c0c4114600301c2110040c00040211190300300c122503110f03401048068160146100d0800d40b00522150180842c0c030806407010b00303002a000c011540f95041001850240c00f84203c80640142c40f21000801d0070060503c0410005040003014007000720382e8000c010780400c8000a10041c07201240a01d5140030b4010750801850003800f481042c03078122071a4815201041d03220910500301c0d403070560180f001003403031402e484840da20a0380c1410050419a5052a44c0347c000f000c520410b000001c0080d802c501d418042e1502c50251075130f034180350800702445030014044070162141000000d4a81000000b03c400706503040c0d8000c03030b4070341c81602074145a00466 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404000584 1250 403999334 403999433
    0x3120a0c032102031e090a020d03031506080709080c031915050106050706180c03140c0406030c0302030c09150f01050409050a0603051c0c08030c19020601140d 70
    0xa15545038044180c0c010714401c503407404500020145020000703000c6030060b0341c2c80540340c010b02e0001f40541040418480418042d080c0820070b81d058412001c5c1d40c0300c256100e2000111000d00f800301040d4010001002004040010040b40c80b00318006030703d4001446940880545804102c010408030101148442810300f00401c250360356450b0103801903100c242d0845801d440c0003003c05140004000c100f14080c3c2002d101c42049080d030f81e8900c11110141c1038007101d0700c250540860b00303603290301903000076500c20715521b1402e901e14818503103858500c81c500c510039000d00701049a41400d007501034510f4401140c00800b00301d000b5006031414400c0d0781252410504040420081ca00e07031750003850841e446802210254161141d90309000204142803000041c0c86540e16030200d09244055500003210050301450800011040c0c405034000f645554090b8100e400108105c0703064070240302d6549815180040030500a0f59820344990052680101c484141100000c0c04e40a110041e00c00f0400c0c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404001834 1250 404000584 404000627
    0x1050f060c300415031b0e0d0201020c1509130b1507030903020a0b270d0605060f0d0507081203011d15040e010213051203030f15030a0309090b03120a0c03 68
    0x2500e07111134207800c0f0150304201181c204480750300381400c0c910400d1555090350b5034080000501408102c0f080e8407101c0140d04512580340030303020580d20000c1440c0341c0f0300e116004c9980e404110051001076501d8581f411140c510b000135005c41038031403444c0c084101010f001d410365500520318056442c10807076003001c1d400a8890001141490080c40185a003559041c007018140c42e0031194000307804455000182c01000b0360501c0400184160800703074103d00020403103001010751b04045001899810380546895002d00c0c0200580305040c4000c601075424050480d166604211003644806401311400000c10500d0707000480c42c403c140c0c9003252028000303006120100e0002801c6010390800503135032600c040309000000c0d0925105110242440c00c04025500f1561040d4009104a0006120100c08070b032803041c010b421f5500344403640490f4840e450303010b03900d0b04005041c4111290003611030b000c1e40c4107611100d1a4400081035602c050628504641002c80c00d00d81107995a4040e00c610001e00301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404003084 1250 404001834 404001839
    0xf0507021e0a0812040201031b0509040e030c01050708040c15020a080d0b03010e030405040f020405150717130614090a0b0a0e030a06020c0c0a23010318060501050f060c3004 76
    0x44480c14a0300581c003d90b400d001c0c9d0b14000c0c66151040300d0340a80c440124000b04542411410315030000c0c18014030071415207080c02e81d43e00c00c1600b512030407502d0800081550080000f00101401141e02034517040c2806902c9205a21b0080d60324100c5281c090840d0501207010419504150800ba0700c22a0180c003e000c0d8001c07408900340d4035007050146503c81d90030141d00c40010004e51095804a0784000c00c12503074003903000300200541d8041107055802c0b0280140720400c150340d1000500b12a00e841260380d080c0c030b207010b4008000f2a80b014203004203034820000c1d0111070341e401680321306807400703020140d80d5030340d08034810744c0c14154502c5815050b014200c0c1c240103102056000e0000f482c0d02c602a2268a0066410403045070a9030040003444c0404a605900c06090320031044903246060400058540400c102882003440319501160090f03203c6005201c1800c14036080307000d086c010345d58182070040244000303480340726030741ca01400f1603212100031080c45900b400403100d146e40081d00c150b5654 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404004334 1250 404003084 404003107
    0x9051c02011a060304080906040506071104050f0403020a1401330807081f090605090604020f031f0504020607020a030305030f011508160905130b040f0507021e0a08 72
    0x21a410124005546880c0c400d81c05411034082000007000028100703072450780d45517214082038011101840c1c02610920010034507461f01030007010a80d020358819003001d1501003c1209445004103100240c420880a00c80060b800240e1040c099a02c05241181c00003039078a15401068003a410808420001d5510180843e5150440c056004041c0c0e600d5032064a8984041e900c1c24580300d0035030554000443c02400d4103d40348004500c0243c5007010032007040a1322405c096640070b4602c0c2505030050b000b0f000842c5405000b2040f03444040e0098044605c42441072180c81d082c04883c02d01c540d40b00c900050440d910502211300b460390080070310b0489522802c009101ba002281c0c01d84209a05000114012110703441030341501380b080d581c035002c0382c3c0e940c056852034017a241c20310400c3c49144080895155500d0b0324546615000240000d00d07104403000308425a481241c2c1740d84506d2070001400035441d40401e4080103040c1204c41040d000c2140c00006241954810700070344160804241007100c1c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404005584 1250 404004334 404004373
    0x6050d0e121213210207080703020a0501050c07050d080919030818040b0405040c050109060e030d1101020d110a180b16080f03040309180e060a05090f060112061112190905 75
    0x4c068a0742211581a10f5000c407940d618064080a584440c00540800807988140000c00c4000404d2054428541d610780126072501e006038001c1311300c4070000c070f010300700703810004190541d621040e00200a9180303962101a414841d00c4194480000c1507064410036490340c0d0010007031890054000c01040c9060b007010075010f011409514009605d030580043c050384588181140d20714020068903a190000c80c4c2581c00d10605002c0306902c3d5002d0003050f1003120580300d1041c0e219240402a683e030f0b008072000402c0d64221804035444004100303070510261140005682100708401c0482031907040b1070a01d81114020840307112282c2c0d90000c1000f04041e88a01d554040307a610010030b107008003162440d4016680084599107881d440708000401c1c0201c0764020130b8104084605680111040300d103514284502600000c4071410070360100001c0018501c681501c0b541c1204c019800c1a682528091142c4805410760f030300315000300054840f0403c60317401010300350b0f404004c903000c0340e580c41c8a42102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404006834 1250 404005584 404005643
    0xa0c03032714060907081504020a0b1315020a0c090c020a0803010b0705070617070818030d0b0306010909020102030403080d023f06030d05070f080406050d0e121213 72
    0x30300030030004c518291000200c100a40f001032001d040b60008031542020381a000420a90744a1220303000051410000c03070040003100402415980c00c581807030003101480c40034415450465110010320b0300815a00c02d80c050a07240c1e4458080f402040380c290803483d201540c0e002804d0142d0010002451680e618003c1c944148503209a034034a603a03070310040e21100c840d520b102501005180014a00610ae10f08180c0d000d80b04d5000f100d40410440080307407542e04101c00440c80f00f645d0b08030421103890100b04503030040441090900c009001640004d41f01c0c0280d21000301000408902c52000e9031868040d00c03502d60f110065a00c0f015000c3c81d1564242010a06464035007050608480c542118407110b288500d201030000c0c00200011042242d160348000806d403401c0f0b1454000000040720032005200030f0103203030340c2d15403100100144801180c3d515810980c01c0c0d8001d689480a1583c4e00041c0c03103480740040c40d105020b943e2410300030741280f41450000c244200f4040e00c05c4210514034100c192 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404008084 1250 404006834 404006873
    0x150512030a0915080c1e0a0c0b06030c030a1e02180411091b180306040f0c06020a0c05010302030415140703112503020a060c080712020a0c030327 64
    0x82195101840202c035111002103c0000b2500030000300f80100900041c82c800c8000e151041410b880b500c580c0b80190425440300d07000810140050b01032003504c4448a400942c12000703080100d06000000340c0e2070640003030041894995500c0758080c013000000403c4402e0300581f80080141c00b1100300c4403240400c03602241c2014048005c41c009041c004111882840d042c1d80081c81d80e11018400b401d40d801000c099800c1304502d02c80946951018013440703002d01e10414000320014883c0ca401202051701d50801c00c00c5502c80c814140210784409a10005c0701c1c000e0170010313a66111414507e610b4108580098007060900d291411091107402c0c090340700300710a41d8100004441e070b08080c40c042c866510300705400b000b600190034000c0b500303041c1114000d100e40100e41c000b46140d600c00027900e0846081b0000f145003102003042c07071034000c0e00840d0294101402145003071082076003e80f20800fa0000a400c141c0d41d070180110045a103241101c8040010700c001c500000e40e80342401da404001480c1c1d02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404009334 1250 404008084 404008097
    0x512010b03060f061c06080d111204050405040c050301020a1107050301020c0c10051303060506150a1b05010e0f03041503110706050c04030611070c05090910150512030a 74
    0x624001140940e400b80500030003942840c605441040f81540103c0802c8010005201303002c10550500c0c0324030001098a1783c064080d0b0040781201814a8a01201d499040d4000340303400341208200808a03002e42c0c40440780001c0316162421708101c03600c4260003d541540c800210341d14481e80052080c003504034400d048422403500c42c1d061600384d0040341d503081d00c2075200c1c645c12121031070f00072140321b180e09061810b5070420700910a6075100750030740da2042e51604d5a903010b1142c1414060107141d61403840c030000ca840c04e501104002c140078040103d0122038015508a0800c10000b9001680403408076801c42d650800035411113078403940144124000ea14460062410440c0240078681665400320b4650342004065190741002e0840180301c1c0550079020800400012941e21a0907026040c000c0e00d503031a94042c3c41c105c6800360950b04030611030303c5004208510300c000010b403c00303241205400821200300d1114075955468968100d142d114005107442041c0000006c0903201e034807040d03940c21 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404010584 1250 404009334 404009339
    0x816080d0e060732071a0a050c040e0f1b04062f030910090b030f180f0c0f0105120106020a02030d030b0607020105090102030d11030a0e12030f07020715051201 70
    0x7501c2c41000c070906010b020301040200140d015595803980008010752080c1c500d042119074600c50801a00c031042e1060381101800d07c1401c0c503d902c101503000708401981807509040201003220180000d018480d030b00ba40c80002000b000b85401b00d080d000b40e0f08000251219140c1c50040c10780440048075030000d94012600700341003003808401d800120004d0000e50305d4a0800c8080c01507260302c030155142804401400001ca4160020065104008003a010344c1c07141007106101110302d02422240b1015031006412241480002c00c045142c00c400300d420144024000c801a25907009415012002165100000440039000714102d00c1d8107208800381c0344034001c804000da0072200383c03602081e0003100921030000194000c500602e190170050040383c3c1010256452081030300ca8a221740e910103c13010042c0f00100101740038074844d020a1101a0024010b03051040400703000040203a00c1082c046004120054024054a409400c0000c1203018150340700c803001d840b6a0007812030314582040c14000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404011834 1250 404010584 404010587
    0x20301080c0f1003240603060501080604020a090b130e0a0603030e19030b0c0c0d0e011404080a020618100203030405061015080406020f0703020a02030705030114040816080d0e0607 79
    0x3880c0702d080008000c003100a10b0b240c0120000e0864002000e0708000c0d00404040000c21894800014509030381d01081090800c400101141806000d0070f0040d801401401d5180e900901c00d0f0b401d440460000340d4076684074111a0b0010b4005600201c080f602c06c000740108920190800c03030507680281c03200b4441c40c0e000405d20030744090b0681010221942100d0601c0002d00b482100c035040004c3c6900307036007062242c01c0c03c1810510701c12207150100351000014226540c000300c404200ca034200c08194203040c946404640c0740e00384041c000703100304800034103d100c0103040340b010705903850041c144422491402d0000b82d078a138000c3d10143c80d0b501c50a400201c4002c0310b49401c005482085207030300c903421516001a1101e40340600122143c1da0240803403054001000064885940243e00600301ca80300d50041c5420400c19402260180c2d04010448800a13210a03281e80c21907404000706648401440303070071080c0100803070f0007000d040c40003800c5800203603240c00c4107406501c01002d694403510390340c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404013084 1250 404011834 404011849
    0xe010915050c0706140f090f0907030b03060c0a0e0f0d0506010305100b0306010f06030c020a1209030606080304051005070611031005040c090503190609170403150e071202060d0f020301080c 83
    0x4492804620401c60070254101e003030f0240c0306080014221001166144001034101039044440b80300103070733540710b40c01840d240030080d29400c4801c155400385021050100141000095903800c0c0c00b0b015080c0c4010440c0c0c031401005034406070014142d4411b56164034155071100d2401d10107124490410461360080d25012a41504a981c01184140d04500d465410707406881101104c009501414900b040400d40d1864000d442c0301082c4c1c0c501e40440d095113412401c848160704240c50683c82404284500c0d205c0fa030b4041d043e00b90908080e51034018514014000e400792170045085046c02000780300c01e82000610703507006c2c1d4038211030505c071303148201c9000c80d600c0c0c1c5a845070541c0740c1d1040103014000c042c0c0c3c190032864240075000114000e0340da525405400c59404810708590500021b081003400301ca141081c1d11200030290070310400302003003003c65852484d40105078200010741900011503680c0d00403210412440c881c18848a400c6160440081d0000d11500391319004012010500745040b80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404014334 1250 404013084 404013107
    0x5090f01110409050c071b061103030411010c14070b030a180c03170906030c0705070f0b0304032f0c010f0c0308240306040609021c030c030e010915050c0706 69
    0x1a01d604103450500244080c010103811140c081108000e0180030a20100030400c0d079440044280240b18903000b0002c2400c01c0518413090107400034000e010008100c91050000501d023464502540e00320340c10801c15465445030301c0d1004d80f0541c0000111031b804140994480c2030007a4040280d4880f9a0a810303100342450001820114410824000a5201c041045040d00807013803443c2003100300700c04151980e1054400c2d201070301e004200380701040802c10094000c1c160040d1010002c03854091207031100e0101420080501c01283c080400c40c56070b00c001c031b190b203150b5000b00c02442402010b84503140e54522100a001408600c1004e840c1c50051071640c01031541030350780902caa0307600042021004d07821400e105054000060340409a0b801704001070150340507800000300ca80c040e10421000358101c01f405014202844000d80100b40c000c40440d035029010b007000c8442c51090b0004803403a200d16004400400040e43c90100119884805062001d0101d002c84403c6038441034181c914403403e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404015584 1250 404014334 404014361
    0xc0509063c12070905100305010f12020904031d0409030e040e03030622091b08010b010c03050913090c1503050603060907030807050c0d120e0d02090a0c0c0206030a05090f01 76
    0x42001011080d080d00c0b401e94000000c2c60100c83c480e40b204005600068221442d0000036111070060040003103a5000c1002040c8520807d59012019800f09000b154020006001e01c807108042c202c041b00f030364105504020b0000d004100301d850354a40500544920072046002c3d42c6800303507015020710000100c0e800340400802102c40c2417124a9191418180c5032481c0e0001a2541c44480014071442004014141d41b0043c1440c1c071420003502c2421558044805410403400804000c00701340c015086915240c000d441e00400004030004a0f8050002a03200a252003105100084d10000c0f42c122280048408e41d03050005031100307420956140d000760380c440100d800504007003000511903001002c2d0280304000790341e120135540b000240b0a40e03074003105544030810034403003241e0560f0050082c8040704086421405e0144270350003140c412403004124002c0700e03030b55408844400d03008549250446a008000b6517891521764040805400169512440c2c2c0c41451400082030320b042c020707107844490a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404016834 1250 404015584 404015587
    0x71d01090609170a05030c1f02040501050307050d14090f010b0109180518070902070201030606230a0210020304051e06070518010306050315061c0807060c0509063c 72
    0x81010543c044030040580021a100b0b5010b80e070000740e010700107450342d130398104050611040c4580c1d4191328000c410321042c0380c0900c108418406030380c02c4030960390002080d02d0442d450f240001c031142c0c01802504605100110100c0800c50600400150080c0015520000b03000c0c035461103005440f040c81c58041c604580308204180c415a106507030103141d0100403a01c02142d038040300c2c0425814a100e0b0b811884105400007640030641d6054000d49009007407034138100004402c0b603070544550030081d404240302c0000024600509502c01c010b42403412040d43c40443d42c0342000e00d0596602d2040300380484840365086501002c01502268042c440c1c006610b840307150030040b01928900c0c0035400309140c1459500d00c4041307000c1e2810003d11001084a0207090014245001044044514000c481d00e45240c0402c40400085c030580c15201d00681c441c201040c2c10314200c00a641038000c2c1c003412900300c01e000c0f0705104088101e08190a0b24000b00340d00c110030b405c0b0f05405042c69000b141600584000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404018084 1250 404016834 404016839
    0x70602060402060a03021905040801060e06060d090201030f1a030d0503010806040305030402181305100209010e060306060d092f0105222d1721040905071d01090609 72
    0x3c0100041001c0c44440c0307001440d2030000d824400c8050702038401c034070002c0c00206050024030024400e450207002c40c260301178001d10785140060118401e8150143d10b880c4c5a50f541421640a5000000510210310052082e00100b0500010303281828030194802e200b12120100d00742d0040c400c4034140c0e407500010341415a115282990143c0c80540103e0b000340c4005000380e030603c20202094003440f10054061494501401c00a240455984240144c2841081403100740d030380281310141841ca080c0e03440d54a95442c000000c0d5140914850207071028204000003040100110a00b14105489020090407924561003044402082a41d26020900820041e20130b803d04100ca04200c034100f094082c2d00320f86480d480c4024403d0f00301c100c2c4802080c2d01500c5d003140d01840c00c1401a00020481c0c161104080320f429549080059060a046000c00b0042d9510544c0c10304441c00703030042e003405200303030304017120000d202985100a10546404031010807d8942c0301e4503062040310515039854070020f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404019334 1250 404018084 404018089
    0xc10060b130b0f0c0102040608151806010c0302120a05070c06231b01110d0b030316060e0f03040e070e0607020d03030c17040f021c0c060c1509050a0303060503070602060402 76
    0x42c00703250070262600c070034000c50b400342d0384c00d000900c041d10003076070340000781d0414050341b640007161300e0886031161401c604a102e04030411004960712001c2483d00c00e00c003040900f4181c0c24004620f4414492140025100c0141070b08030b0000e1090901c98421446219500c6800f04d446444040c010400070400340e07605c03820411400040c1c81900941e615500c000849030030000d007102c0201494600c1e100011820048260482c800d802070300718181d001c0c5103800240381c1c10040810b58aa0014111560f422940c07514003000c1000f0390300480300d00100da80c1c2d2030f2680d0f08403201d90380440300480000c030f044500501c242040d106480d482503024184000351161a030741900500562000c4100308004101407140c9003100c2403026000f0340c0600304200c00c5140300d0044c0110100c00c1b501c03c442c28002d424020000039040c24040c4101c5011b40383c80e26514a113840d001b0030b0f003440109171542c01400c1070384000c140880030410141e00c620a403020090540c0e00c01c04d040e1103005602c5110050f800c8400001d0250 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404020584 1250 404019334 404019337
    0x1809030a0f03060806040c03050106091a060d090203030f030a0c0c0f0b060f04090f02090109050f010e040305040302120c030d090f051905030303100801050f010e0c0c01110c10060b130b 81
    0x1207019050100b240e0b0b45400b919407600707104940a88803400620003c1040c02028881c04000e070203959028031210408458201e40007203101506400f41000042141420741c903603203c1100310f0381c020160395540002400a0b80c540d04190740280929150030070542880740600382425090780d020003d144000840e4451a241e880000d100355045100000c04940ba540c4a11510303c41c98800d801011f030009450060010058058120441c66450081403090200450300500e0444001c100d0002c0260b980d40380840c1d050149500c000e42161039000301d2a948840454081301c505001e030115206481310b00c40840f80003095105d40701ea4a89003900a005c24240f01c500c90900c2d0070580c005000066a80d804249154811a8a54004060618180403c69007801159080300c3d002010030441e5042c644205600a4042c00803000820001101c4103000402c0d000040c07680d101250146d00c6150710f00359507803180703101e11002845030f24142010031108041802d9134840c0381c486880d4042c143c01c060558205 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404021834 1250 404020584 404020607
    0x180303020715060603140907030f0f0f0218061e010801090e0115030f021c0b0703020703180f051003140105060f130303021b06070b19150b07021809030a 67
    0x2c0084000220340404075900412000340103942c0c0000e4814110b545140d400e04020b806420f45030080d140800110702410b0f054030346242c00c000e101d100c60207903103001d028072090000025000302d0124481030701425004003251282d05c0658850011181a03035102c0380c41020700c00214040344609005000105251740300d0390020941000015685207140402e0200d214181d0044441c40c589040c3c180441c00d0441d990080110b01c0700902004005564540b0085000105a81e0801d5408139141c01814441c4007880038031012940c0b0000c18a440d4403409400e004180105405203807900d40303000285109104481040200340d0000002e6400c1c0000c2102a6101c0d0010f03000340f000500c42b042c10352079245030340030085200340c00821200140300402c2101801003c1c6883c031134601030008002007a4103080450380611031a0582d4002c660f0120503c000301000c5501040588004801061950412005083d0180200d842d804c040c0301040c0e9040e54020208d491042c2900305110030001c490088001c01d20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404023084 1250 404021834 404021843
    0x91a030915130506040503030403170c04030303090204020f03090a05060705090a031101200102030f061f0f12020a05041d010617060a0b0307020109060b1002030f07050115120311011803030207 84
    0x410b42e900d6141c5010002d68066440703410020a100425401c5030600703111921501c180c044a1134038400c848414001e510001d020b040c1c40b07140801c11550b81c0c1c1d040700c00c103e43e450340da15164104005440c2c0c0d07600780e50404032b4141c0300b21f02c045070300d540c00341c030585402d401c2c0207080704074450543d90b440400c0c284210200f0305001c0130120724401e5110410201a640052100060712803402c2c2d071280c2074091340900250302554a15600004110980380b21b040004410b040c6014030500c08001117607042c0034094504c0045201050000110340d201c1c000303008403103650804110740d2030b41d64500c0c0803242081c403803900490208a10807101d581809501030348804018544841c10356284031740746d078a901c00c0710b403140140d6407800f41c0400c201d6240714642031164180e507400b6011a1000e1301a59030311900404281030100440ca080030003100b5000090007002400c1c0000c036540d81c640c4400501186d0040460104210080340c0b04280790500c03940e0100c0300065448a020005520300341d0003980715080644 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404024334 1250 404023084 404023111
    0x204050d1b080d050705060601080408030f060a090e01091104050903030712090602040906150320090307080a06200903100f0b0a030c08150603060106180e0106091a030915 75
    0x5075816003484004003c0f41652101039444160340381ca64200b0030001d00d1581804465414040441c1105007902d50000304da444040094440c0700000c1c1c104203155121460045c10505d2847d003070401074100d903040307070300c202c0003445070396003140810041e1034040380c8030485a8020300c0040c4246109a4401581c040d03503050015030001a61901802c0c0d1380a9000140300c261104030401c000c60f01c1140c240c0c0300c2d484502e02000b6110402404c0c84a410105018040d0200702190820300c0d680e0610261000701085011a458003005141140241c501c43c1c00da002c0e82400d0108040c030340200c400c1201c124081c0140a00301c5484e8a40340c4600034a0011600d0800300d43e1032040d45100d0321604a49005540540c060707000291408503424504401003000e442c2ca4000709051119540380041c1132030646a5504200c4040d2044104000300110254400642e0482e5900002113403170b04001e02038140c4c0c20420b08140450207580b885007580c0300903980400c069100b810680402098401442d800c10032850101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404025584 1250 404024334 404024339
    0xa050a0303091712241e01020304081b030715120504060b060a0e120a02150c0319051305060a0e1e0a0602010f0f05010302090a091e050a020102060702010204050d1b 72
    0x815000a081c241c0f000803440e0030712028001e40b804005a17040041c86200c413040c40d940c00303c0c4055802a551080c4400c51003030310b40c004d0380280b069501401c020002c0348c2103101c0755601010102c1d1044100c0f4028037450340c001ca5800e40385e6601c2660600e06494116062204d41001c10061030018000e48180f59110b101401d255600c1d401040e401c1d040f035480007030b090320b10010402d2111905d000d128007907008007854001622039010300d0350309074051810691250014200c05041d4030510422903259a1514100340e0919004006490288007100c0405501e03030f20340051060034400c41c1018404031f91040480c1c0300a1a11003a002d041d4400c103044403041140d0780c00801c3c9112030540018000d42d456401c07202101c0005c0c070508188440344881030106501d03540118101ca90301a2090503c41c0d01e030f031030038420300092146d4146403154600704075441441600f8600d8568002030700407401805540d002c15541c510500035241513820003030508010f410965500c0d100900c4000300304031030003100c2c0d500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404026834 1250 404025584 404025623
    0xb190807090f0311091018090602090d1a010605030f01050613150c0b060a030209041e0b0f010323030301060c031101090f0210030219030c0c30020a050a030309 70
    0x54001141305100800c0d00a04001c100805000e0090001c001c0381d41c86e0f40200140840c01107514880c2c0d100c40c03c000352998181c10084064407030280c050313400c03101c9191084100305941841c0c41d280950240840c40c1a41c0383c0d0790454139840190754410079903094500510943c60b00e00002c001010030140da05221a542d00003491482c110014660003180050681d0020704c1711000000d5882901210840209030031580010107401c030180000d004c102c0f40c03c00c081d02489481030010110798000426020350720b083c40c0010300390381090000303d80115075140b40c845141c0b050b003100c10b0000b03072100185045070b00300300d811900e00d41c1d101c000b41c007003007251550b0a100390401e02c503141c40d15000f00c2050b030b100c3d14a4014001e014445044901c105403040000c1405440d07100859910a4440d1a010441c01050380d0b08458122013814058441c0c0f41d0501c04407040304103010009100a00031480303080c1d9415403201a41c1328164020050242c0d0001070030032000a00c25841100b819100300c06003010219410381 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404028084 1250 404026834 404026859
    0xf15022103070305061c030816021603080a20010218030a0201020c01050c0312010e040210090807030b0a0f020a02060924060904050106080f0d02010609290a080102070503130b19080709 81
    0x10240d0201d441c8a0611101e090b27080f280698400640c00100070b03400c078024000100521603c0080e0011101140c0310744080d1289a18007038000101c20500d0701d0382003211005000b075024121650116071aa54280e0140c100801d8210070701c1c4c1c058018005a04c01c0f8401518623904c900b034035030090b01081260f90a05d20400f2502c1d4040c01004485202918280c03062100d83c2154210038418001030400401c0a558001003903419258848661101c68440f100c102000e000d5040f0b0100d030140c00070030a8070b04580d000035031170302c203c0303032002180c1c04a8001c4428040d041d084d402c0008849040800142c1a41400f9929680086c800d4000240050342da0b401e05050011202c980b4103c4d810030080620415424083c1502401000d0801c1080100c0c02c0e00044c0341300009010342401c030080f80103104240da100040321005240900081d595404039240c415141d5102021055049094081c0400c0100000e415200e003200000038900010701c0440b0255410b250062003841007050340c03070000c10442c0b80700c403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404029334 1250 404028084 404028139
    0x11e0e1906031509020f0f07030309060912200706030e0c030105072007050a05040b01020c030d05040e09060402010503070c0c080307060f0b030a08091203040f1502210307030506 78
    0x550010f40700301c0d140b121503114030b900e41c0b03c202c4c000d005019082001d06039908640082c1c0140746525038601640c641a00034020407440504003d00d8804002d0902010b11600030000d50b046d0384401c024843c04400c800700716440c101b251138992011006000c40c030b010b81c5c00150b01c4103c0c40101c0e403820703900300000b900b0348008581040015488010070300c18008016000042040031402030940e09041101040308503143d8890103100d070752507106018191340244000241c145024050b43d17600f0541c500090a2a48039210f101042102d810004503c5d1402044407030081d0f034140e41c1d091454454080440302001030600035500e002c83c007000010711a108000410000344215004035049514102c900c0072600c0741f204490003504618600c400040015084030011130080340d80104480001020601d0b5000c1c6400200201d00189000710310700c08010304110520340c036642110a415a0040700c0740700300e00b81300f1012450300310a20100300003600030307044642d01000c00340c1444c18840720302d81e5520702540c824 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404030584 1250 404029334 404029337
    0x7060209150a1403010501020c0105070f051e0c04060320060d0e0a060b04090201020d1404050405011e080a030903061e021b010c0c05120d02040807080d020c011e0e1906 74
    0x40c54100c0d140c2000d040c020360f0b05100410340c29503161800103520361f117401c0c1d00c0c1b40c100107002500314200b10700f000d008000590030034221103840c403000617144240c04074501d00c403c191080001c1c4915078501402070b08103603a405620800c8031403102c1261268003034110b415582c02107003480480324111980c440c4001c1400b110000b458003910360b00706081100c903502c3c495800365082c40d44400240c0d800260055034540c081c0f030f281a00ba4804d080d841c410f405aa080282c0c401c0c18032000103207070b00384a0094248061406060600c2d1690707482441c1c0e48508010000380420358001c1e0030000304030540e10020002c003038400801c24550b00003003448120780c481c080182c5c2c104000c0d03004803035400091140b1441c0e001c070b0b81840f41749104c803600c810b665110324600e11140207000040941c0d040c00d15030107880040c164001210891605c469036151a0388240006c4001071059003c48011584540c2c40c0b01001d1802942c230012880c0750420031220040038002880c0c1000b017602011604000c82c4100d24000e046a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404031834 1250 404030584 404030587
    0x40602030a050f070c02090604061706010512010b010903060c0c081b070608150f150a080a0b01080112060b040b12012f0412140607050a020c0d0b06060706020915 71
    0x9a101004880024001024450030f840800036880d8002e15404103a40d0100d5005241d82e0321000054080c1185030000315249800c1c0003a000f014800141050580d40101c1381220b04070450f24100c0e08817a2072490042c006000743c0804c00200e4126407100b80c0600452411407036018007a220310100e6401904452001115400d41d2000900300b40140c5d0050300c49841c000c500d5060000043c03010180302c5405901c00c04100d41840a00d070390702400c54627900d40030314010340c80360400b900c041d0044008689a000c03103403c0c03000c80040d0398400d10307106050318005118811500a44c0d120b540040c807090741c00641050344c61251a80310743d10503040441c4044404000b0443e014800b01c0c0207003402d080714002031995100c94074200340b40c0d05070083e03070244c2d8208100f1500e82400390903d000b22034041c8200301080d001d000240400346c0d40c410300925109140341c08480e000d40c90a000d12a10b0152401c0140c02c480d061004030b079043c42c2110083c01c0d414050440942007003080030000e0f8643c2425040d00302c80103070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404033084 1250 404031834 404031841
    0x801050112020f010306150311040f080c1c0b0414010b0a09060918080f0307140a09050a0e060904031b1a010503061015230703080105010e060f0906030c1204060203 72
    0x305482804071000c0217280038014140b411440d041c0c0201d43d03980103010f06803104401c0c0a00c0e5003e40a50b00101103842c01305400c942d4a0907030720f03282c004841005000e208001140c03260001c06010b980603103580305440074080e0759aa1107183c07040f1161541042d1f255200e00c0000c09956074030105101a1041e10b000180d49031500720ba43e400c07102c01c41e650040d500d0361131818601160160381a281090001c00070550b82c4e41d91030100b120101d13064151070402140105085c5451a80500081d003618070540d9048031507512644185281c03001210020303400141c50300040d000034420340540841d130040307070140301c884203407a50f51551000d201da220840d0785da10342c401040360386003c10416401c050b4110990542034103010b0300c60480d09030040c40a061206890f00d006400700c0b445a4009100f030302c440c0c826181d4200e441d00601c542820702c98240042c0c1130002010403454030104807040040600c0b0b00c1803500100030117002d00383c0c0004000b171200b0003092151400d81c40003662528480c510981c40140d480c513 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404034334 1250 404033084 404033089
    0xb01171e071125080f0a060b0117010905041709030d120b0d0f060501050f01050d021608040305060f0138041a030108010501060c0c090515041b0e032e06080105011202 73
    0x400d9513001c440503510009400c00e0400003c1031044100750400ca01154400e40d6a0050314020400e8903440c0008100c4800040c01081e00d9102c1e600446c172940c401e1801038602004c5525500a2102040e4903800107075420800ca80a4000c00d03041c01c58180d000301d1120f10020000e103406000d241c00395070b524110307400036003081058891280500b10841e2150503440862000800500400c0c40f680c0704030f0f80c0080e00411600b010038642c240c185c1d2000f206c55840d40c41e071818a07298103041d240301e030604154400208a5101800101c0d00758050f00250b0200e0b00d6200704006881128618550040f038001c01002c6600748402c924080582040d01d0307101d40d40e5161400050844105030b0012042000750700320400000d98150000081751140705001c1417a40301d04130440d8003090704142d205d51262070071461003900c200c0c0c00340604407003a003078982500b12103002e070501d520f035a2280c900b00e4681a0443c10605070300051103d117070014681c9000012926103440f10f0710308448080e000403581680d0302031541d0851 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404035584 1250 404034334 404034403
    0xf050a050f0301090c0810150f050105030705090907052508031315050a06050118050310020306040f0f15050a05030a030309050f0304081b01050a02070504020a050c0106090b01171e0711 81
    0x42c23512a005110310302e07150840454101741d001385410454000041030301d03184a0b80648190090083c0004030702e0601100240c21a484507807408a629081107003200704251940740012801d400401c801d01d1695001080c000d5503c5a40003114210384e5043c0b8400c0c00c203600c0c42058450700c2c142c0c6000034484e0805001414008820212084d0300741d01600500068401168595145000c40809a1a1b449607400600504048480c0b803103201e25240302040407000c5a006540a03001444c000c1000e40d49074410300511024a00509405038030a04500e400030f03110364407042d1418043c00075900c0a00e5144c00c828115400b56200d40300d20350002d654103805c2510103420b203034180f109007016803a11155400280d2070750518461144596408586840441e01071021100c000d6050700c002c103c0f09032a405820010448080f1581c00202c1c6180100a003844501041c2c2c011456840701c400c00c020f58000c0e2010442d0002c12080c2000b02a0034172030015002004000904c00b600c00c20301d1003584d44080b4a001c4e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404036834 1250 404035584 404035601
    0x121170c0115141507030c031e09090506060a090e070228020f01080f0f04030513090501080106090903052b110c06070207230301020705030c0f070f050a050f0301090c0810 75
    0x110286041039480b04ca0b4070048811141d810305240925020034101034580e411803510314041c2c0f051200380c98280700e40c80100681a00c1e10351008100e581c58150920060f4043c0300b02c20b0300803880380070b8180507440314101e5150b8011384030700c11a00d07103103000e0085086010f0300042d072408400c10000c0354411440d20700c4a070004483d003843d11b0720740d038940050b110443c0e90300640340c01a0b04540b000401d050611407421034070399079620516840ca07260f40f42140c00c000c05091003000c1d002d520f080ba0104651040340540120300d50540d545034140b40d04e6081c5841d00c003c6c562807208003140324002c031440b4800f107402501c40d41e6076600700702c0b81c90700e44c0000c82900f03040000b0400000c54100090901900c1d0422130103040e0310352189041c0c011080501c0200380240700d4608081c082c0d01c0040751542d00f1181c0001d050311200c810b8803d46009542d0f0307074043e11581030640240c075130010070314205000c03030b0610658810a14030020008220440e151f1030340c525080c2641c01c801c0040d00100340f40c0302c40083c00d00a8141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404038084 1250 404036834 404036839
    0x20709050c0301140406050405151c030215150307060507060c0c2621010f290a030b040e0309040e0a11011809150e0121170c011514 58
    0x25850070906030480c510050050028841c0c1c1c3ea400325407039454550203600a0325001d0000c100e02d0138681840c41c460354113001481d105446180010f0b070404800c1400d1032045a040d0006c03c10b82640403003c082a0400400d081405116018490a1650104403007802451280c40340c47c0c1c1c03002942000301c103454000483c1e1052040701c4011600103908151510440000c1c0405030381ca6004045008409100359030494021008910030250800a041e80f8a4121040c40c0210000a550340c1d090102c0c03003d940303541c09031050341c6003500c00c25052030b20014011507001e071400090750504030001604954206d42d140e03013683d0001c521003400381003600c1508808140300000f08482c60103a500d540580203861501703810011440700089015400c2c0311018003422002c041440216004903030340d101e9840c180324841500b0410000019405107810604054010322551300c014aa59503d80d58400a818007041c00c1410741006441c4e01994280b0500e10380482e50705102c000c580c07411511a01e10f034280c1e001c0a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404039334 1250 404038084 404038091
    0x140304120e0f0d06020d09080d0507032d2a110c180a150e01082b0c12020f2a03060609040f05030706020d020c0d03060f030f140703080a020709 63
    0x9401d5a50300c414901025402140946e82d02d65809404000e4120b00b400108030020100381302c0c01480464211602c6010159010840303c2e204c030005d9074108002010060401d00da0b905401d2030340c2540e4000d180f110005039403080725240501d40c0341d4a5400c403003541c0800030300c01d00001c0f4101402801829411807088582c3c00440b4405043d825003000098420406940e0700c1700300d4410402450300c02c40041c071144d20183c00960359010a141c44080700f224103101c4468005910640906242c015490100f0a40e16880383d0b22082d59824a28200d4071a9002548614802080515804c1103001e070505603c8524280640002d0030b24000c0001c601081c0d80b0030303004901000b4058850355407070356000ea044038040c0c003071008a040060451081c14030140009000141c010381c1010f268006003003040c1da007800ca52041200140c206c04a0301d19004001c0130039089141040800c81411204081500515034800032040c2e4088091601001e6481151215004907100c110140c050049030010f00c002c0c981031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404040584 1250 404039334 404039359
    0x708070509012a05030f03010807050414040305070303090c1511070602120d110a0903141605012a030801031a011514090a140f0303041401050a140304120e 68
    0x2c0c00603444205032421095140444003890401000c40380c01d5a134110741034030750300c00f002d50003101e460b0b1007402449001c0c410b10000007114200f91040001642c002d151300380c80b58956076070440d000d034002da406408240d103c0360700c4004119403004600040501d0440140b0400c003446015040500ba184104070a4002d00400c1003650340200d90740d99642c0c034682503907035503522240b0420001e21619000c14000c0340c0129000481d1034001035001c060300d000d200841c4c07801d104c00050075035a0560384a8551b45c000500c204100b5540107000c50102c880d214001c818610b62900c2c0d500051455000c0d0940018203690300410500c424010996030f00502041c0c9a0a41e604000c404c1c68490200b10203142000281541c0c000c2800004040d5131403034000504040c0c0c4151344040c141e61a59401e2038032885102415903200c8149000401c80d0125072598000400b103401d000f00540d21a0000d0070311500380710107100305044400840c1c5c0118801d42c0324402504040210020040a9413140488140182c0854000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404041834 1250 404040584 404040587
    0x19080609010302090615070c173702060c060402040c021501150519030506040b0301021e0c0f0601060f020c0d02010c06091b080a02090901140109091118070807050901 73
    0x1030781541e805803840c50f4140c0718100410b01d070200e4000160302c860b0011441030100b010365505241164035034100c00e2034510980413411340f03035000e4502da9901b9410040242ca80220030010a26440700d49041c0030000c58034a4010413559408404c03040e42a4000d4010042145001c1c80340108080462004000c1d0611000c410300c000e50b01805800c82c0ca00d0103c039401401c1e0312400444502d0400c03411040007c0100c080e001c0c01414040c1d030300ad07201d103060005082441c03d05209880b17031506851005010040014240345656000380c40e41c09950082d404507812500080052500810541d9590050004c4424000323041c90f1055807414414400031030300b0310150380c1c0007034410f00c0c039500000c0c005500505482d00d20455030794484100840715503043c0001d802e03d00826071200d068001c0e6104161540c60071100380c01ca071282205e0207402481c1c540103000c0d5144561000d07401c5c910840315070011000c0399000540e2035108080f52807a1410110821842a602c0310f02e0036041805410083c1c10a0042c030300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404043084 1250 404041834 404041849
    0xc0a0c062c03011e05102405090402070c0605180303040f0b16020406080d02100606022109060f041412100b0316030b0915010803040501030b06091302190806 69
    0x41c0185840301905a07403658290b011103070b01c0000c4140d50082d60328a00b480c40117000102e0340300c0380c00504120b001071400c581c20489800032181c4075502c01d07010142d80c429a415082083d286800079424402d00d00080c8180b00c0d00400340c49a51182e544030502c0d85415243c0c2d07500c81d25054040d4200340003c101002d16141d511042e180c8004150741c03101129205070611420946019500a0400d03100060741d44000c248102801301030303801d03510001142e800080541d80f0b140b00b0310700141e1110b00a4080a5007401d481303480000403c0b40545000001d40001e0410742001c48008424540001c040001781c840341038101c3d84080949800400c0c40010040c0317602c8191038a0351090309038481260308070b542d4090003942c1c1846000800002c5003521780c20188019203081300d413042e280c0300f402a0a0b0210114414250488a90384011443c0a04240045028010140707050307800010501440f07945a440d070151084c55100048016161108150002003810030344540c0c8050100d00c030f0601060782c64041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404044334 1250 404043084 404043137
    0x230901080c0913110301050109051509040209040210020a0602030c0301090608061003080d060909110a1a040b0f040b0c010f1802060702060915070303050108070e190f0b060c0a0c06 79
    0x1000c244403880b490030b001c1c2245068a200170b034107501e02000810740c140c03a42e0083d401034940e001c034801462074080038020142c20a54010f0342c410341e0940060018034000d0303c04400e28000748182c40c808101951030106a82003507030b0840502401000501110049100b4813000f840c1090003800581030a8030700380b1401c003803808054212400000e40106609648d008100109441c000402002003a802d00f0541c2007195070308984200e100900c00901c00300824500d000c1c424010564514181c0350013000035055010360345030140d400050200281c81d140c102d0103044082803100c00440e100c100e11340000d0032980c5100102cae403100c1c00741d030158000d62100b00544031195410f507042a91580c0510020304c40081048048500f18070000744a402c2550507001141240e15540407112210348400d40040f20741400c88258842036111903200c5d03014103040d003003403141c80300a40000440103c11004100c09601440c0034085541c40090503000b003140c06032205000708a00c1c81c0c16140e071401d85c2c580b200c00c1399909 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404045584 1250 404044334 404044351
    0xf0d030c170601180e0123060313020d061a04050109051302010c060e07030305190f0507060504061e230c04061110021201140d03020c010c03020304230901080c09 71
    0xa5000559590040304610b00540f448410713203c0c07003507544640d83c030040c10074000c3e0100740c1800002940c0c0c01e5021204c0c40d0301c40e90000e2581d402d503521084404000005450103030b03804110040c401021920900c113034a01d02c100706404c41180c070b550b0b806100940b07206900c8007003610324140402c901c98164a82d2541059070910340104600c0042c20074038060a4180c05450090003885400420190020700406401030044120714068105440540301182402021030118004200040c0003501d81d5120640c0548200c1c00014600c2040c070740002e1800015615000742951068465442140a8421035550030a0722a9000724a05038000c19151301a078807407a0248100007c01c044030f00400d00240c980c11400040071515440c0072001c000806e4802c1c402c007003400029403180800e500b00030100341112501a0000c145154200004445161010300d00340c00b1404240b1000ca0144600701c03003451524080428414206500c0042200c61181a0300881c040e5000c001c41c07221a461b406038003a03004044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404046834 1250 404045584 404045627
    0x102120702030f06010b07141f0f090510020c2a01081008030a0906030e030a0914060c0f0c091602100b0a05060c01090309050409080315041407020f0d030c 68
    0x14408a480c04a0f00041d1007802c0c0501070010520191081c00b50425602a031000c000c40c00c0380a90701901d1b6540c0140008038149919880c7d40c4411250704028890400d48400203040403060310b0703da04000103065441c00c004d400141c80f0410443c10081c88201c0441c2c0200102c6000109001d42c110320a03060b81c140c144401c150000b01c1c0000400f540a0007458048240c80e6038042000d8028288506402200e001c00d00c0c245140e00c42e0380d0300000350346200b000350b26080d2175542401129008422042d4299a0011080107604401403051010440342c1c1a500c00404103210448108944404004d001d0102e032200107a0201c000b0303500003075510108006010001f5400ca9540104846020941110303400c920300107914240c80e40c055022014260090391445000d0351160200f0080e0340e03203a0b00207040c03000e051020441248580c0862801200001d000060215840380e03030310400f1004580210150700b18807080d8114441c103010316004c03500c5901d0100a00000840c1c050690004002841d05540301c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404048084 1250 404046834 404046847
    0xe0f060612040b0712141f080312040506070311180d0f03020f1002030105030a02090c090a12030801050f1810030b0a0f0b03010c080105130b0613051e010212 69
    0x1104001c54100c010792000c084450300e0103043c042036960040e10382c540000e801121200c440c1d59184250102940b180740800141d03102c070200941c0d0040491f80c030384006503200c8400903c0d040100010075180016a845079582c0ca01401d00070309280d0011b0003c4107150800001105c0310b5810b800322450310b280800804901e001880114484880700c0700300900c0e1a204400142c280341d0009030b01811014510704480e4142d01316081082a40020310a964142c3c0c8900f001c4801031901701d0400e5403000441403454240044c20000400d5040540d01c4040804540049101815400120940034140c00e884609691205c80d02144484d04400300d210a0020200c020556821b200406c040c001c50308402007031007074188030b030b10200240803442158468501c1e0051094035400c0600901c103050700c0c0c94803248010ba183c80140a40f00c080c1c1280030007800c0ea40c454416455480b140034144003826285501c1d01582030505214400701550b044110040d9460441855603070300044514051710b81c03440042c0c0301d48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404049334 1250 404048084 404048089
    0x10603260f0d0905010f0e1006180f0b09011403100603080403060e010902090405100c1404210f030503040209010504020909010b0a030b120105060102370c030204141009060e0f06 78
    0x43c0508000b41594281000030742112041c0e0050120012150141c820120801c200300d01180c0441c820444281c218102480709100c10b544030ba0280d4038200b001099140d40d100000c0d00a030800d802905a590805031200801c0c2000c00c150799401c0c0307202c0c1007000b03000d0a644414040c0e020342c1c44001c018036160085000f240c5400c3d003095042c01e9002d00340340ba4070300b1b00386800e030344500304100403441091410986e10007292003001440b500c2d401c0290200d00c0c090611000182201458000f01024401100f203100007920b2800c2c0808018004c0ea03986440c0e040c10b2041080145060740a1031059005000809065940e50002d0741103450006807a503070384501e80da06401402d0203180b1290b01c0703a400d040314011141c041d00050721440099007540e0001c0500c45840003103510f4030910b208030b124180100108440000e8820f5100350143c440c0e04e030440d0383c2c2d500080c1034880c0140c001e500c46569030180a03510074141c04680c060038185000b0710003142800c5545c03000b4030b8003c0c00107203000b00500200b000c54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404050584 1250 404049334 404049341
    0x1703030622020706060e0702190b150306070512010f03200f060414031513110609040c120f0c0f0c02060403170c2a220e010603260f0d 59
    0x6030400c400b0b41d200c04607400d20500400701481425240c0028000040c1282e101003403800f08034010b281c450600394801c0e20b41881c00301c802044e00c0c40c4007407100c031824a15a001c0100c01d10601059444135900c0915040283c3c0360101a404010684440350080c00011081c1710410401310700101d002030010701e25000240703255074544e003840e0000d0380001d010981004424419844c048140c0403500e580e4450000d1544400c0100d4107021326034561700d10400000c8a1000c035200004000f040617051800140000313003122140b40000e400b203146a003c00034810054002c1126640c9500c00421269120305006403640c00720255200400c207000d6044400c42d507592003a18040c41c1c000310f841249054a48032403205070300114040c5030510854045141d00b188090840110b00f01c0c08460600116844040c049030103454103040b4513412101e215045401c082d0b22031400c001c00428004500103183d030608843c2c025418208040700e0300e8501070b000b50501764004030b9100308080300c3d16076a1840c0f031a04c0b51008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404051834 1250 404050584 404050639
    0x310050603010b070c050306071416022d01020f1209010302040810020705121c0e0114040b06130203010f2106020f070b0c0903060c0306032404060617030306 69
    0x8100e0200010900101c110080c081c0740b481026079031191900c070000c0641e2030030203c403001c00049111862500c010303071990180030400c44204282c01e5058681c1c0c0050780e43c10b0320183d01001055040314241c802d45107200c01010041080c0081e1240c0102224045d445001c03844804490220002c1c84000e0750740710345c4c1220300600d000d80945138a440c40b0040e21019520280007a80c00b80f0600c81150781d9468220120b8006507545140b030450b9071103204041029020038a90b0650555079081d40c4000210b02d98549440380c0c1c030034085800030349001010080da0614020004c10b0741c0f481800144212a409040407050f40c040c0d0725007010510005c0d4000120541c1500300915071800441c4001c840c02d0a100a048070078400c81480080d40d951a524407824044c5041c2c442c1e01d540181c021401001a8000540d0421005803c0c2c401c42880341445000034400706140424000000c4100b2007403080a10401c80640406507101e684609407940b85552808080c0c071040c890708100441e050315250b5141c5041c003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404053084 1250 404051834 404051839
    0xb15190318021903050705012c06040b0d09120c0302211e0904110906090d0303020c031b06070302040305070e09150a0b0102010c030c050f0d02090d1b050a030305040b031005 76
    0xa43d800407500c403010380d50303210031541403103444000310302d5600505095901c901440e5181003134418106800c090400100c00490700104208004141d001c0c54400415500110001c003003180000c80c50306441c114032403411001000509021500040e41c0800c1c51401d00407080906090844540d460948920444000d0800300304208108046020884041c0203040011030b01040074031543e000d0110184154100154044020010044146424200728071158001d150050400081d4824103145501c00070400006000c1c104611b5a1044100010b651010b4549000e600702403071039948596039040d9006945089840c800040c1d03104804204564200c540a0072503021800c0c02c90350030b0014a960383c02c160055080020a6070304a000340603a450318002544c50614010240e0103e8500d90002c60302d4001a6400300810700040d6601321031001c9071030054040d01180030000d900080c80300c289501007801641c414104101180e00407083d02d080341c2520320450359039540e05000104c1120140c20040d0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404054334 1250 404053084 404053099
    0x206090606130f020c0a0c090509060c0a084804050a15030e0106030f050c01081b070819020c0111061306020309010902030114010503010c1e0c0201120f0b1519031802 73
    0x309000440c030147d01150140202001a034591990140d00c901003103d04003035008041000c0d014092244c5461540911000b0384038108140c1e26620303480c04a039486035250500410380e06070184280011412840f000c00c1c100700307490946440041806200070344a6a411049203403485800d4070b02a4010f00500341010000b0085e10380c60340f50032401840c00d004191528451030390007031001e50182903c5402a1200040000e00c0b068905030a00b40c1d034481c10302103a00581c18010005240b4404440c1c0d00e041200740c015100b0015030800050014a030120300300220361084080c00050f04441507007800d0703942c101d030016036686e68481c0c2c2e06024003c0d112009400d036103012502c0c01c0302401094074a040c1d0343d003100244844e2031035401c01c540708074020f40c81c221a600036140c0c00407144e00840c429801c103441030602c2c51948140d4403a020403140e0b841d0b5100006a00c1d42500780051426040000e000c600302c08816003452070264110544041001450b03051559645400100e6440100d0820080d075000b170465 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404055584 1250 404054334 404054353
    0xb190504050607110c0906100e03030f191b020108070c14060601112a181008011506020c0d0203031912050708091515060703020d0206090606130f020c 66
    0x4950710b2604a40c16000103248100e02c0014120124104240c014010111000e58503842d040114141081131840d003031008200c810000ca0310288060105000c2064a858a84010b22810302c82e01e00920114030400500c284000744281e030740c0030824403040c0c080ca8991b01da950740103400d0f24640780c1140b0140c00d0703400c8402209550300f40000c0d00d0b8460902030b6141c0207402a8690100c0d550303658100c0403001003510255800340500c4074450460160001000e058090b03950f0b1203d02c0070028142e503419004044240140a215000d003e030510494490030846006803611900940364071000b10401e1065a0f021100400d56400b00107940c1c440051011000040c901c108002e018445441e0318042e0300740c140000a4144e034002d00c550385c03160325030741d0150900106a4a0300c140420000300152034080c400082003039182c5a400150990b240f2940007003821039801c01c80a0700d08107000345255a00c0c1e00010801a054890048103941003800903004655000c1d030412803400380c01600c50300c03c4148102c0004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404056834 1250 404055584 404055593
    0x1023418020c120c0307020112091202060708060607030e120a050607030902010e0409080a0c1b0b0403051c020d03020a02030f121b040812070f05070801020c0705030601050d0b190504 80
    0x2d0800303449003421074400c43c1010440105030b000c2c2c41112149900144101c50140d40144240188064445030008869243d552070b8001788000201050043e8000030030403140300c0e04600c52681126044956034242400d03594018900c9070780a06080c0903807c4a600e075101058100401c0c4040c035030080c29501d1500e02100010002c0a01710b0003640000c440d00c0c45d03001b80b0b0030240700c0d0303880032038010210910304000c0600c01d5402286000341211999068040d030366840382d20400703034000780c00b44407030440d561440c5040007803500042030500da181c49096102140c1580d00041e00d584114214140580c40b174002840a9085000d01c854000c8010740008001c1010040300d5111780c800c4820300c050248041203a07036903c1060090740113000255211844850741030194201070210b00b841107101d03503c0b9403a1562200e0030f00850354459000c603900400c01d60a50780e420711032074018040c1500180741c01c0d0702d040001040131b102a00040c02440711000070503402807640c0080c0304c068650380402c0c032441c2030502d070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404058084 1250 404056834 404056837
    0x30b03210a03151809020a0b040602060708070201020a020705090c0f040b0a030e0f1b06040b070f051b0306131a0c090306060406061d1210050f060102341802 69
    0x400000c1c9003180d4504480280058502a1043d2440e184c940000c90711814005011080c010790b070000308001c0028005102c2c8000708040c04c50303070f4041c10060510aa011700050800f810320303c00e690061040c0c8404550000b805d20440c1e2040718542090303120740c2c410204a00c146480d0369a000b8001801190343d0164800a11102c00555410400d50106000840e201c41d86941a50307513036000703507505082402420740030044408000300480e02e0305546011405a031307408400101e03a000c000590034400e110b0305111141d83d0018540c0724003030a4100400107500e509001700581c05503039401c0305810a108a04450031032154008401500700d04000032828116004152250310030710401c0d00140381c6090a01450045603c03d4407041004043c04200b186c2030042c0c01f5200390442d180e0700304d41c20314a101b088802d080c0c250200d00083c4500301071195200c54100100b08606542c88944001c246c91490704040e01301c902c0000b00c1703543d084546206102da070b104540c080840f14029020300800081d650b030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404059334 1250 404058084 404058097
    0xf0301091a06060705030d020f12070c03110102040f06032a0c121722060519061d0c07050715030203010e0a1b21090c081e0d030b0321 59
    0x2078035035100d596164200720701480b5075040280150010700124003c0706580d0084c10069001c204860b0034680360121164108200720380c00400038107840f030440181504810011411000d04009500c0d20341070942c81180c4495503c20441015034624009800b003840b545284100350700385010b19001140d80200600c64094020244e94052101010861060140f4106131025009884902e600d5841c00c403014860050b1522611038500000ca6260000740c10b44511880383c40c40c402c81d510700c1c0c02890400c0e8204c546a400403000034101c0b01482c2400c401d21205154808075440509a9452a03850041d007004099400400801284541d2020a980680266058a5100040c140107659407100401a00c80413000c0703082d02056803040d040f0491085000b0310b007801c48410246d9a10070208519411a900d00c8010384c1d11070200502842800c2091120f190020156500d510008400030706198807901c41181823004e1541c1c600104a581d1010700c6109140c05400800381d2901c020080303001070300d5210f00e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404060584 1250 404059334 404059373
    0x406030321060e010314031e04081221091509010203060f1c030809031b0a050f120414010309080c0a06051008100f060302030a03030e060a050408030609060f030109 72
    0x5050700d0703a1005040c400c2c9011207205030000c0700b041c2d2a5403265644500d110152038524001000703111900001c25124180c1604080340d00c2369903604e040302103400c11115119004408a040080d0000d040281d42c0c2c860070081040c20404254684d00d01091130041d000c15000861000a030800c1140301c07065005e07500c00c0ea0b055585a01910020041250840400e410055022602407940c00460300c45e08c0c2046d8440344600c2224030b05203610701807490070b01135142030013520352250300280204002030150b05021609200204070a07041103c40b090240541d015149607480150490501a80720f07412030105140c11200d0b080d80d40a20100403502c80c103d8000075a841c1c2d0504011400d4401c4103844d030000c03034100c80c0107803441c0b940c000d011801800d11513080c9120706440340c0300407016030340034082c0f540c5840c86501c1c0040c442c000603040c00d00304a00106907982481c684420800425240011039030b1111080740c8c0c00c0003070f40d640c1c400151b20300c400c1c0300d0762038041d031921820004209080b403207091a44041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404061834 1250 404060584 404060627
    0x504060b040506100f030b030f0304090c020304121509080403140106062303130507060c1704030c0302040e15160806060304030207170a0204090c06230a0c02010e04060303 75
    0x803201440181c540075240b858000c1046180da040300f900c11100000480da09280228010400d8400285404a641905036140c1c0000508010450080c4110750548040e40051070909290014100d410011901d0107421a2440303020b10071000e0040e80310000c02c80c1d100c030760300e034941d070301ca0401710f04444540c990707040c1662a01c1800b04200303000300350210221084840d4480038136201107905242d904090105801c0c0c2d00503030107084c00202e0a00005000c3c1c00d80780d54040e0781084600301982101c060503224030400d0810401800440c44041c841002e40e0b4069402103100c0e454800014a0103d1043c2c07120841030908062180e01548800074400410304d99483c250241c6a620402c0014441a18000c0140c0d00107401000400091141c2120100180040d1580440c082e00460296036503910b00b00c445c0042d80c2000e0000581100710820241e10000302c00b11140507141c0303842e9a40c4600c00c182c0c0244042c903c03225085a215021000c4404405001442820b560f07181c003811041c8400c11070fa000044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404063084 1250 404061834 404061851
    0x30f0c08090304051905150a1205010501052b0e0c0102010b06090f0d050304080a080901080f07120203060319110907110714010509041d21030604111c050406 69
    0x2140640078050081030015600d050300d46020880e040d110200865541c9040f243c00040d40d03915448a0039510607824203207950b40c0105880140311540d005948000c13586420014031070344c1d0340202550040110781d02c1000d800c0c4420b1000710348908004410301400c03410301c03861142d803460202c0d808010900a800a101803444002001014040d41042d65004006008012224a400c480301c9a40034042c000b80c07440c00b9128004113090100452081c0c82a81001600c400f031564412002035000035807807000178050a16401c018201c0d0320b04800f00c1c0450303030080042000795905100c681e150701620300b0003941a07c4c1c1464048010082510003d200d01c2d42c131800241e036103010320026500080c800d000340103207030300780080c005441102940e03d41c1044814000150346451b03038820b481000c4a0740b074080c0b42c0010704920591621618081d0201202d94146580b42244903040070340e5084502181d000c030f140304520118040c5d5000c0c545510704160401840013011600c5a403000e80981e0103848140f24000c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404064334 1250 404063084 404063087
    0x7110d1113060e0a09020402040302130621080304110316060801031403071e060b0a0306020c010f18020f0d080a09060f0f090b030711010c02100516020a08030405030409020307030f0c 80
    0x10014800c0455075040f01c8005840741c0a19401000502d2009000500f441d07260b030007165540c19145103071540507507500c40c01e101a2002c01d440c08450380301c40203282084d5000342d40d141100c0c04080d1000f06540700310079404800396010b020f082030204c0b0304030304000c0366592610001d040704001c1c4020360b408513040507902401480401183e41042e00300e0149000707030803a03008039101104050001e4441d581e44215400c07455990504100040d0302910000d6180c000349070b105e0703003181c0c11310302042c0c2154601195858031071803c000c224015501210b0700365860300140040341c560100510014049200090503c03015504503286109541041c2d40c3e118082d0740c444403e0310708400020034280420400d05040185925030002503030320100500d4a000040078031694542954034100301c540c00b60b004464061441007103840382a501c9500c20500c601c1c080c85c0c0f040d02a46850100c0c0010b000b5050002c000b9003809402c03c1101d0040c102807a085580740741c4214010000c1c002044061070b960304045040413040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404065584 1250 404064334 404064341
    0x51f11060f13060b060f0d0c02210901050705190c1e09320603100203060a05060f12010906061e0f08180102040e010617130807110d1113 60
    0x1c42100c107404155071155281c05030101d2500400303d80e65034884484c01d100da11450094881604001c1d8110346440c0c0165101c002e070b92080f4054011584000c03d08000101000040414850400c030b01542d140100d00c0100d8061140c25000b42c43d601c510814030600d41d035046942c5c08600d0042e42c401d60107030b8650035401003000b205817010140ca0403500090004650a40c031507100c82d072800200e026944020220101d421045811045810004104001d1641000d21048d0880d5140c424110314510f410000a20310b000d00d0b0103868000c207400700341c240d5181820012038180d0040c2c84130f180c40d07540c0d4444d070000190000340224400580d02031402c00038515150100314034a421500e07288090281d980080714840001071040c01400c107080000c5685690030710040016082c4900a50402e40c101040603248040740109034030404804400c0103d180c82010103c001c0780c1d03000802c141c1d03802043c140400c80c14458090146e0003080440854100075002e400c100b0800c100751840d40081046207944001c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404066834 1250 404065584 404065591
    0xe0408030403080601031b02060f010801060617040c030206040e0a0b040902030a0b0415020d05090706140a03022113150209030a03050d020d02040e01031406041e0c051f1106 76
    0x88010310225000034040d210302940144185000a415001c110448143c000c6485801c1d0140c0c000c84e06000d0714900710842c2c240500381e410000e002d8a464850000c000d032401258411103540400d01060410204402c00402141c00500c103e45590b1a00050903580c44c0c156108000d15181c00380c50016800d281c080c0981d2141c0080250407601c807291039042c0d4542d401441240c511030402c24244003e10703184040c080f81c081800c0002160319010351252f15010158201c1414808040c2ca1421614041d0040721103c0049180160f1a0260303a042d0f00e14003400503c9080c0b050700224204102000450188031707425005081048142412070181c100328420322040e190180c010a1418020a009100801408649083c011702c0e101443c0c3c040c204a80041c2c211070111580c16004109100c14090418020101180904036605083e031b20354045c1e40c1c0001c01c0640c1c0c10300c408040018045054105002400d010780482c03410b440e250200c0c400300c1c07540203216012440c101c0001070007820000359a4813 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404068084 1250 404066834 404066843
    0xf030d200f0d2d0b012f0106081207080c0708120904140c04050103020f0c0607090e070807090614130e01260706030b0613030c0f23061c051905010e04 66
    0x18001284000300d01030501050141c0c1401b13650141822a80c82c02c0c102c0c08010031024241c1c0340440c000d50a0242968020303808007101e54488c0101c152901641800c4425240c1e20000d40d0786c0d20300d00c41042c0c43c10000d842c1d00009140c001c04c01116482d040c0c910041c041500100da04200c1d401c4100c42c00d00703195030160b90400ca01c08051006000310350195008080481f560348919080c0040d04984c5403070032100725086c00001c0d028240800222001004907a000342c201c0c2807001e00b030300d0007090042c2000000d106e0303001001401c0d04290b81c0031141c0f02c1121204e030540ea0381030103155101c11184100180030b1040d071038040d210345140c40110b00080a560701c504102c40140ca607487c60110b08030b0240c010319a616510800402000c01b01d03100b8030b0301520040d0300c15500c0c61040c0f40351a40b010000117107a40000e0442d1052080b950586003c280d050108040c01c95107183c4580d45100d528030440ba4111a20460614000a000b101d1302d1441409181c5850308030244039076070300d5402c003142810082d9070080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404069334 1250 404068084 404068151
    0x100605100e01050d09020901080f010b010c0305070b1b18010f0e0d0b0402120601080f060f0f040b04080f042907020a030b130206030a0203090601080f030d200f0d 71
    0x10540d62056004040084c0c1c002000310f8005104d030001860b102e001c4e840782c100d0340d002d05412156040d080c090940c40e00c50034203222048210907100074005104102004010308110400604441e4601190200802405a20f00d803202c4050303000c0886030061104181c003190003810280a400c2c8124480c07603203140040c4c240e038ad1a44003992070265450002d072040f6400011009040403e03442000201d008000d0700d00100b900d810b48841290525001411256444803c1c1040114440000c500c00341c0265105030010038650386e40c1010b9109000308000c0900c1114002400104840e02084990307181d910314504803119022001c125103103101d40784000750041048401000465902040207a111444408a03901c4a9040e400100781c2d42c81203410300e000641c0482803010040d0100895809072004130000d086101c03110203010750324010400c8100720039485e06800030500e030381500920612089000103503180c044100702038407250050b0484036429807801000310803e001c5c01c00e03002440f80c0102d80c42c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404070584 1250 404069334 404069357
    0xf0b1501050d020c031b03041509210302010b10180807030b0c070c030501090b150306070504050f040b09130512130501050708090d03080105040c09140108040f0f0510060510 76
    0x8003e0340000d040c203402030105000e06042c40e0041c1003801480035051000e56500c0381808130711107100404080e00e01c1040000d110130720001ca980c40650f13403044410740c44000203100510307040f809458010310080c0c12410900c0500c1c1c01c1d0390411001e1b4800e103159003103151815214416603503214200d101c040e106170f000c1c20114000210a1009052403809005404c0c0c5898807a250b141c00e5076040e10f411180106030b8410019001b581480c8400c0c40c1008501a11040c102940010507030300440c011644200d030038801c4182d80c2d64441c3d00c20008080c0103440c440c1c0b0340c07401d07081c0c0d010090300e070110030380f007600405030302004550f2010102d0300c410108010101e100f5081c1001150143c201440c220b40e058010002c001c0c06550b407400301c0c40c03c14826507513504690306082c01d110a64500228003401d00104000034442002e40d0310004108681c00e11b4465503d035507509055040c0d104090002d0314204941d5003c0040c060041090241161f030407105005103540c640900400d59164005c2c0c00001d01d035900da8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404071834 1250 404070584 404070607
    0x20c0304061107150801050913020102120d090f050c0906060a0f0c03142215020a0828080a0c0e0d0b0a061502010618060501120f020d090f0b150105 65
    0x22207428806140458043c0342c1c4a00302c110a200e00300701c5003000300c1c40c0c1c4401001076142c408406035024480042c120124400c40e400070750f8484010682e110101d6000c030305802032032400c3d0700c00c06606412205050341c41c48a81000e585540148103550b001c0c500c1d020006055040440c202e40504001d0b070740d5858219405882107820000c4218200c0802170040e02c0100c210ac44032020300742c18074091444443c1c0d61510340c5210182c591a0b0700110500a08103581c0e04416000310748554029041070391581e5500c06810280c00b0480315918024100b280c054480310002e921021280c46101a52420001031241e41015503440d0039071803016610a904842c014002070190a80c140c0050061001140190701c41130b100303d0a4036126003810050b95680720800c4000307000340c04000e058544500820400d400c2500080000c400e00b40381800154449025038040d03200c0c1c0c0d044980344080c0544c05c010780c40b003514083c1da40c0b030084030040c3d4076002c555000c1035408101d1180c841841e6016120a80303041d43c070441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404073084 1250 404071834 404071847
    0x402040e0c03091e010510060f09050d1401110403170306060a03090f0204110a080f0903160503040308030a06090b0906100e0307030b070224060607020904020301090f06020a0e0103020c030406 84
    0x600030042c081c6049107003401d155407010103031105904c80007182518290f090185545d02507031089041001611103040d403d9004003054003900d0b41515034005c9220a420041e07203204102030390030b00342d40c6082029030150010700c2c0600140c0c0c1c4a42c440d01d100400904580010307000980d05107a204104011000c3c05a00942c84607004a1203106c9011010801c0c2d00000c2c1207078680c2000a0500d48000740040342d0350303400500c01d90311050034030103005542821101c40350f0b20b000310075140207144480146901440803c206840083d544050080c0d41c900d0040b000c1c1005d01500d110f07640c0c02d9406c0903000b40c1903251070511380344198000f03800119400c00001c4100c03800c48120401c01c0d050b000d070450110125098102c054030070040354006080e10340c50078080700001c207048101e284104814500f4005107503a00d1044400b542d030100c0d035403080d6403903d0002038010078400000401c00c2c48142e00110400400c1d80140000344099203403524840101c00c015400ea1140103400d0000350030800c0148010340c002c11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404074334 1250 404073084 404073091
    0x507180e0109022101030c060e01031404170409060f05040f05070f05181e120d050702060318011d010c0c0308010519270c170708070e1005070c050402040e0c03 70
    0x803aa119a180301341e0038900700e4400e0f0000d8904042c0850140040c5400c00c1e10204014420f00e01001040c44410b2101e0010354040d00007080010000720105089081c0003d540281000395002c0101a0740c0e1000018040d0140c4a21030107142441c0f100d50542c4054886d0901c190402e072903146001c0000231013203a181e4030401c0001c000b94242050480c09071650042d603900510083c11440b940414001008841d50590550306129804481c4003007a651344501070350079840e03040d9031860b12034a414800310f4081034070411408035980380c0080810340c050210003400c111800c90f0f000300b2880f00c411504541420600401078041501600100300c941440c0701800314a0051904201c8145e844003c06016914121607000314000030b0381da01400321102e440b0782003403408982860360b01c03108254009020818020814001e01800300c0000e001280038628201d00c00c0c60040c070340708072485c8000c4083d246802100c0183c2d441e2071100d01c0460942020300c00c9600781d407400c164151031951060013a8100ea80000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404075584 1250 404074334 404074357
    0xc0c04050c0c01090b06090c0306100309020a09090f1a072f0a0305130504021c050411120a0b18191a0c0703120504030801360507180e010902 62
    0x800169002c40300078403a12892078030030007001483e401e119003000b03001c40020f001d402800c04c0803c14005259602c40004040c40c0fa1340c2008556a00b6500009072030041603803010f5010707804c0081c0e00e4100210548041300d03442c4107180ca080d01001204001944000c201e030404041070348011a825141c04a14500315000050f00800742387c174409006543c02c0200404003200031a2022691401e445d607443c6204c8050321041da002c500f4000c15410040c0c45007204018184079640c2c600100c1d0031700ca00c61814a001040c090b003400c1c9807154544c90555940c0810b181500d4001344407000c1400074116480203130304804581c0042c04600d8020014245044101000b2180321945603224508143c040711441d21450180e1032450b21924241409000103007801c0c605042c9030302d02820407000940050502d07054401480186413064151847c81d11500121001040c0303084552041c040d00759146e400040c4549010703510010301914908007800c51142c2c40c09824410007149005201440d4a035010303180c000c406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404076834 1250 404075584 404075587
    0x3160f021f1d070302011b0503090d02060c060c090103060503070b03011e1e0603050a02130e1503100e01060f150e0a03120c060c140f0702190801090c0b0c0c04050c 72
    0x400c00c5410b0740c080038501d100064200ca03000300195a001194440304d0b89011b810141004019034039280c0700e2041c440698800e81000d0000030654988200380c030200d1800e082164418141011468007070b4006c0825280041e04121010400f030070f02095190441d100300c40c1d90f40c210723424802d240e44194a1007220301c04210300744000041030403100300c1180c071040c0204005000941800c3d40282590b10007040b01440074010490b40305040b04204403c411100d19041c8220186c44107103e8048080104201c16458410300c1000f08500d045ca0380080580e6034000000c002990b42e40354800b80040e054030408070007444081c3c00001044c014051094101c20007842001c031291282e84114500c20000b491b0000030ba80107203040d040201c24072801c00310400d00c1c10a2070280c81070700c00b181c17802d104000c00c0c0540d100020654000b103458010050380c281e01d00300e40403101c983d19406041d0092010607002d4400e61002c96002450f0024101142c00070125600500341110011041c00003800001c0d1a08041490 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404078084 1250 404076834 404076851
    0x11040f050a0b0f0a210c0b0d150b03070f1107030c050a0503150403030b0103150603020d0f061202040e030f030103080a0206520302120105040213121b0b03160f021f 72
    0x900c1d005601404200503900d80b2110201c6001040b40c203d03109c52150615a4001032002117440c07825254070000d82e2078150032040b10303960222242d9580e130315050720720320400c0408000c01c20a001880141e600682d5038010700d0fa0740f03500b010f6403644c00c1a002114101100c001c10007003442900078141414040c1000b103041c0c8040c1400030500c200c181e015200203540400d00c840740c110385000c1c0c401c03c2c40c1c502100b03004150510b440c49640141c03443d0028440d550303500c07052601110034010380340c003800306d0070300030307481e5130f0b59051512890f448412003100500034000007400090700311207901138075a41c0b000500d0380c1100402c50800d00c02d81185c030544684200f1510101c821030113000264a401440da400b40c0c0b1050b0000b0310300c882c801d0680100b4071841c014800c00406100100d0b40d40100c2d400c0a03170384402c0b1950380c18070700f040c5000034451150640801d0804203000d0790520003140543e18040580c602170714501411110706084004e07030b01c0103070051034036010035141c0c8030380080010308086800183c182 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404079334 1250 404078084 404078093
    0x70501110a121a0f040f1803051b03030112060f0f2f040e15122a060711060c010f0f0b0f010804050d050711040f050a0b0f0a21 56
    0x40055031074030009402c039014100710b4151406290740d6040d4019694925544074000244406071030f11307049000b40d035103806900c40030f42150020201c2070280000b4400210090070300409039808014000140c00030380b62020007000d0004210780c1240c0000440e100ca1120030383d180b401400c8000301100d100d42d00c5030781654041e03500e48203d5440002c1d00b81c1424600e140d11280302003048142114858000c1c0a200401400e81c1b40b2510a60000c0c41c0342801107002d0070600003801d00102422031041c180b03c0d00c41d6001c04c0011460544040ca0081c1c910041c964008104001c0c40b48120303c0c0080103910112036442d03103410404040e007a4580c9400001c115003060070648030807a007400a1580a0307d86404a007403460420340030007440d001b0280303400304051a0640381c141d44c54405410394020131200040c3d910501030201c107420342c0b15200900c144031000c140700d00c0d134019007004e940f000348032440c0c032120107001d25200e401d4884040e0b01909401d1134500e411f40c103e0700600041e49004401411814810004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404080584 1250 404079334 404079337
    0x21c080d050412090303141b16080c1e010c05010204053c03030a0c030c020a090c021e190c08031b06060604121511031302030c03010b010503010b07050111 68
    0x210004000303028030b05403d0040305441e600b0741c0b030030900003043c00c10320100303901000d100d594692a0002c00e95505c1e0054a07001030910174280380040d802900c248103030b2903200040e040200d0b0108411608004007141c2000b204c07100700e62991038080b000503184119940038044100c1114001c00005090a5480f07022500160a1402e0003654000b01c40104c036400000514601c1e6000e00301108196400e0303050080b0340c2d41d110b44866031051182e040c0c1c404007090310508942d20341642c06012140116034590020001c1c10400d8400310140c0a616a8035800c010ba81407513003000c0700e104004258240c1014110b640c44200b110003610803141403e40407828100c104001d180181901026040c1008284c0d111410400d01810581c8280010081003007103103034043c80d400c0c1190b0403103450104e0301d4009080038010400140d1005408001004114102500f1b17810517081d00c1c000d400341d9250710294400c02d4221500301070260f01155080c4010b0000300415800303041c8407032140d400011544a002c8103030085 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404081834 1250 404080584 404080597
    0x11060109020403150212060d08090409080a1d0918010f0608070e01090e03091c020a03140c2d01020f03030405030301050114070203070513090b010b0910050412021c08 73
    0x1141c00103820020803c01460070010041250021810071181030b0322000701810140c81140b040c9010301500302070101c618215105001c0040003000043c0b0f152502c6000c541000f603814010a213050240662101050307900140c420300142041207580d01c40880d116400844004606150f42e558415810090244a08009051140000c2c66010702c0d0004804c2c26600503004403075014144500310102032000400c2e00c59002049422800c03402800301c1c0c20422000e4504040c0d4043c40b0001c1c0001841981200c241c4010301d104182c0e102c40f04044103200707000300c0c160b02071600310b44800d4804040c2d0740f085100341807800c0305105446e00c1049000041d881c1d81c10644081d111500000b00400032580c1120101c641d03840031007103490401001c3d400094a4000c0c40c0300d681e00030002d5020854038107030183e02501003158030200c07049540d6101c0b2544040c0f0f0f00284400e074007860340f20000624450040c4251811181451000c0080740c186609101e08012045c0400402d0300c500c01203d00044c8400c80a03010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404083084 1250 404081834 404081849
    0x60a0c080d020c0d05190c02040b06120402090a0207110913050607090501020c15091018092301083406050703030b0f01050f03060a0503030c06040506010e0c0304020d03110601 77
    0x3140c850b403c0c81c00d420302d400b030348158060000802011842c011441031003401c0c04021b003031821101c001c500104010f403240508541d4092000207149000381d441203c1e0034040e5000390341c0d00c940c07036031405081c030104c3c0304e2000060f220714128486c200701468106942d660008084450344000e4807155505480d1030b005492400c003045006005108559040046001030b5004481c070401081c011041c003402e900c2440901350040c041032440c003c005000b42d0720b008116045480310a4030380e55600c1c1c00c0005180c44040f07110000341d5095885c44488212000c00e042e80d4030140a00505142c4200703494103491090541e00c44c007007243d8400c02811020303000c0f040c000c0016407110359036400c8919008040f1200c2d0200710388203200e03c1100103a1642d02200f510048229524066926140c2c00c0000d030740c84505601443e0b042c48000365580c4842c0c008070307036240903500c50011121280d0301e0740341801d110785007155171180d00b00003400014007501e4142a8010705030b0003401c00c103440840b900b2500c0d017040000d800460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404084334 1250 404083084 404083087
    0x7030506090d0305062409010c0c080d031d120a030b0901060c0203060a060605031303020c04091112010b01050702060d15170f06060a030f02031c1e051206060a0c080d02 74
    0x1c2d80b0035010700400d644160b08032206030080511001c151000e504070800301c51403940c08181000664050310b40e0750040741e0062280040c01d5039440748140c0e0b40c0340200c1d0910000e07040c8800c104494001c4607240c02c10001040140c4030700380d80d1145c00012a00b0042d83c68040580b540240011034685001b4140070700310300d986100c0b10181c00d0041c1464204040e008800082c0b034040100807156005040d690411016101a03041d1806428204c0c580105541e85030360046c03603d2016000c004090000722203220b0161480c580740e00b0104000c0d401c0318081a0810302080d001c00484c001444d20328000c1c0410502c803d80041c41e8021000304004959140d0498448088020410b108107901084800380450070711004100ca8a0a82c01042e16626148001480102281103000441d44e05000001c082c01074802507846a10041e00010f01404180c0c4c40441e04061580d10780c0806031165049074082400b81e01e8401442c5c07550f01c04e2000d16070002c0c806808000c4403032210800103022030000c1001808001015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404085584 1250 404084334 404084353
    0x19080c0409150f06080f0601081302030105010b040e06011e0c0c170604050f0c1e060f0d090201090e0c12040507050a060e0405060f03060712020909071e090b070209090703050609 78
    0x20844181682048080c00205c00405c0f4016a101442c150b0240c0300b03190207a20b90311401108843e04940850080d415400c00e0004540c00542e800a40100c41500d0203210f802d880304801500c0c08100a45501312003241e02d0880c003070303840c0180150103107548154000c0c0712075603482d040304c542d50b070400d0b50442080e0046400c1c0028000708000050f030f204020405007a62801000c0004e201c803007190100d00c590003101c0d086010980d50902070b189400603407202d2950b16001c10141e00001c011210080340420014400810f00c0b03044003848a102d0988442c0c503501d8000354564018807060003d01c03c07540b40c415001d0104880d2525101070008109a49540318003590500c200401c1e40d50007041301e8001c044000c02d0020340d5400007a215000f103190b0801103120b8aa510601c8040e11500e0b02c2540c0120180007800086684040106030031010141802245040c0e040e08039104d88641c03140036182d02050003c0c001615281400b030742c10005074011640041d40d0b80d07545030306280c8200d400c10301c80d41180c0f502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404086834 1250 404085584 404085599
    0x80703081e0112140a0804030c06020d080f0c0d110c0705040501090902010f080c041a03190605131a0d06060f0803040303140c013b0319080c040915 65
    0x80850014003040c01d464560601000b08075040810780040d160900e25480d09802007418000340410941110a050f582d0b500c0e0304014030611020300c43e200c014414800e004005034410301040c4e0242d80d20314191070150b20b46c0e04441a541c1c00c045200030301e084d41d610b201c503041d5411100070300400d5030f02e030064120185800104811540140e20220000341040c40003030050b030340112940b84007410342c101400c40361980180b00b0294080c94001c00e002d4500c03d2100c18081da4001c1c042d61141c1984080e60342414100850542520070f144501a001600b0300c42408c00550b6603000030303200d10b4161400c2880c10104200141d05a01e00e0307803043c2c9141c3d5071000c05220440d40e00d8809170181c800341c0011464145140d500402c0c2d03580428200d00d43c08404240000024400c0d0000074500300d12003070181c026410400e0404c5410400a8a1000c00410103031000c0208404415200d021402501e00441144010829a0781803001041407072541002c000205d0411418450101520403020300000241c0c24080d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404088084 1250 404086834 404086861
    0xf01121b020d110606010c0309030602070305030f06030109032111030f0a0c0c080d050a020409020c0d08091207082104051014040f0611040801020a0c061524090308070308 75
    0x810401c194141c0c10111000f00240c22908035a0a10345002e00560508049420b02031035040102041d0001a508042c16484409503000d100e04144081c0f9039100c150425089400a020003030104200799000c2c01c4501440f0340707a1150b00c2c000c51000c40c99240c4808000e244e0390003100d4541000440b2070500c80000d0003485503000c202e616040040717001304181c42d20004e030300409481c203008544940010703040090a030140c4008140c3d214040d074070396945056035601ea201c03000000b00005c40c60b0000401054002411201200c01c07c4111407505100351501c40450340113030710740001150441119001c8107a500343e528461400307800031380080c001311900d00741070340c42006504c803400306104280004100c400000003070b1541d11032400145001c45100b0018075001e03581c400a010b501c04244040e03540d400040c0c090b0540d220300f10400ca800b505101340255210389000304110000c0040c4075541c001d80f00c441490704041d035810081300850350380d56008059840020110001241c0c80c050040d444000c1c0c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404089334 1250 404088084 404088103
    0x31b0609030a050f0922140a020a0c2009070507051005100b0c01140709080601050409030509010f0c12030c0e030105150d061e02030f01060507110f01121b02 69
    0xc0185181599a1074028414000c2440c1c4030044d03400054000c26681d80c5158000681161300441020312420300402c00040190304040342c102280c11000510301c03455403017201c0e0000c0f500d846120742c0d1845038494000c0c00550901e200401d1414854103095603643d1540180300b202c0c540d441e29aa2200f0b840c0260400200c449118640c60406040c4901d00800791001c4055031441030700651610860f0540a015000810740c1030665581c40043c04069a40101d240064035000400c40d40e140c5d980b0010b101c1120b1610340040c0c00903606000290040d88940b6801400072003134640007004424a465000800c00e46000c8640400d6643d8100d403101d40c3c00c00380400c0ea0800440003040180303400079800d8040303842d80342e940e40f0401c4082120020810300b0750021003015059180c03c003504000600000003507105903440310240c0201000081d8003841002100c0c03005a000000c0c10f510711f07000c1c091148946002c1d407114184840541d40206c2c481240c81215402072849500030700c801c4a042e40139003440b2218 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404090584 1250 404089334 404089351
    0xf04050f0a023d0f0906080108060106050304080409060b0d1a0a1a161b050603040c090f0605040c03050703050603120415110d090504051332031b06 65
    0x3003031074801594030500e0703200c50f1082c4040c256061481038500344030140c00c0088010041075030b40300081c81c010341c40121100340d09145c0e15542109038640a040c2c514041c2441481c405602410040c00300600c41c2c2d0103540c1141c451b80826050540318015881030b01c5079504402220100817030480910000ca01902c0c8003640d000840c4d6418170146000305408412502920003030340410001c01602c03c001c0c1c82224030074285440c4e0390010424501d0000d501e080001c41c41000d100d11514086480d152400440303000710342c000c1160806c5490040d14034054800140c03044807180d511140069252214010080f15000d150341c000f48500d0000000360840e50043e04050195001240041102d01e40208135019102c240c0d842c0c0105049001045540008180030800c0902503426260703038594114034076070207445007100c0510035a030320300301d0302000c071103000c1e0001e06074012031680361304003180c0f41710100707440c03c29150f405102286148103c6d245a10507040d80360b00244245044e800c08a0500c013568020464 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404091834 1250 404090584 404090593
    0x120809040510080c150c1506040c0206060d1e0804091b030c0e0405040c080f0d1e050f0706060509090d030b04181e051203151f030c0c0501050f04050f 66
    0xb407008260750340440310139203409915070314600746040c0d9008080d161201c0340c3c0000c07203090000c102c0d448004036009880c414000c130b04041c00b1050240c00810100e00c5520054507810546540d900c41c8000b603040341d011845942c40308200310300071801001c000e101502c1c4661020840d482200d49481240640d034601c142094500702065040325488201f414070200e044401149984440c01c10020044450b402503940f4850010b2108100802050642c000ca6550b100e0026280301d0707000c0e40e0748411030500c0b0310b000039200300302c20110054001e019040107401003c000600503202d20210b044600285c8100905511013600f5901049e0b242c001d400e0580c13801d6506220340703181d940798007091140100c0010b000741a060703c00b1482e18000c20903216110b400030119241e02210940d5190300707034015a000c250700100c5034002c1a803400c0c01c82c111280d01c04a2038440d4040845040210000d000903c04001040b40e110142004680c003401134034004c03803a6200c001d066051601e0f01900d80202c2c1038208036036800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404093084 1250 404091834 404091839
    0x1060605180d0c171e010b030609061501050c160305011b0201090c030b04140a060506010809160e0c04030c08030d051003080d20130f062c01030204120809040510 71
    0x43d142405811181c04d564411404c1c103c4103d003500341081c418801c04260220441c45000342c6054100102c402c0c019419031314a03442d40501141c0f1590f0807551031484d600000c00442e02da5100300c0040003e1803542003030724421304a241e09800701040030342c0309842d80e0391074078005042d801d403a02c040b15102c0e007180000c0046050703a50b102c41e004c21261002030704030190b2000140a21420360503042e400807004003036031a0000c00e8585400108400d44610380000c91140001e00c00a0001400400d83c5001028010000d8508442c214060b1001000151045420712001001595000448000d018000061070315281ca00d00b2001c100d4400070812064214007900c1040824113800c02c89090790129000458016044000f51410005008040d0104c8600103a07417005442d80c010007100350b070744900c031200760281e07140012030300510381d4200100002090249014403424009584c040204103041c094200341c2c0d1817401d80031a00c0203d10945000400045181c50341c9041d1003111380c020391380c1c4050400c40b030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404094334 1250 404093084 404093093
    0xb060a170616111b0420040e0105040b01020615011407060f11040320011709030a0e220b1906021e0d0c0308062202071401060303020d051b01060605180d 67
    0xc40c104d0044c1c405607881c40507184140c03200d80108000d22940d540e07082d180c4a000180301581e0340319201d925440407501d000030607103152a01403a00010016401002d040d115426011104494403480c0e07414004003203914070700e81002c00e02500c0c00074018000044c08180d11a40b00301a0303942500755400f040c2040009000180a4200c2000449105001030010511364001690210a00d100b01d1510825207410460803000000060410750b4055403082500c01c0c0030405d100300d00b403086100c262910420320b40302d02d5a031169800b00b03100d401c008011010300e41c21044d000e0422619a00400b00581084c0c0c121920259004059a100400d100c0104004070950100400b100802c2e00024100511413011417000d56501c0b03080c2541c050000000032144182114150003507203c10b204403120030b41140c41500d142d0040c0b15000450f90150050700285803854011580d9501c62541400d41c00000c00588084413802d01c00d56015020540b140360f0785407074200300704900e1480541c40c0d0348104151003864001a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404095584 1250 404094334 404094343
    0x12020603100306230f0c041e080a20101202070f12170708100308090d061a1305060303041511031813051510170405070e13030206040b060a17061611 65
    0x98100f00d8554100b0140f00e004a48c3d030b404954071028091082640394020f200c0c202c2403180d80f2009010b128590100c0b04000e00031201003440c901000f22307106c1403210ba04000b0031f400900319240324460304203400c4c1c11540c0d81c1540c100c0300d003445400107a107081c0030202441c80008880c3c120a2038207140d102c0b40b50001c0c0e07500c83c00c3c0740c42c000100032140102e08980a9259035101d40b140aa1002050202454030342034401240e4541030130038071400c01c11441340e8010407580301d801d00503000903015500c0c00b8100750391312130301c07107684c4d2041c0007042010f0b4060b12010380140040c2c4240030010b600c0c511051541001c002682c6020040c0207003151900081c0720328411280345581d020041541c10200410144406450384c00240c0b0049192004200c1007004001002c00d004058800480c01d103c01c0e500d401090340400c98107a100140541d02200c089000300c2d0b5903010f407583c4004010088515207451780d841c1c40c0c44c0c0c1103107a881c0060354030490a001c41c02525036021000720180c2c0c683303851002038000072190350f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404096834 1250 404095584 404095589
    0x3100806090d0e0414090d090f03050a020409080f03040606061409090402010f020c0a0305010209041d03040b18040e01020a0e011d0114040e27010612020603100306230f0c04 76
    0x20300c20403028883c030644030b0340c1140e81c841a8015480042e03103000748120f5251541520001c00149110b140070908038000011035081c0c80d0004000c200b20382d020790034000180313140388003a101c2c07080038000100202d51150041d841944282001300d440d900e030500103000c1145852000310640784c00e000e40b0100c1e40b00c1e55805503100d502441d146080800d0391205030304001c00204940d800408035a004002d03c81c0c1500117144803c0c05440420008902c0400708000c04012001d40d031064200304810050008a040508840341c4041030f000700d070300c03480d0002808070341040303001c1c803c079075008291a40c820740c2203004010004800e00f424282e0900c4e9008801c4148440b2100d24140b10b0800c2d180d00150602c0c4c4107640141843c09100303031007410140160400203d11003102a01f07910105450b911551060240d00e0403070b0102c0800d07505a0003179600300070007900000c20440c1c1c4a10b81500004c04034259014020302040d00d5144802503800f210b240c50055000203282103040c00c1c46006020400c0d5000b8225000c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404098084 1250 404096834 404096837
    0xc0f030f06010c060f20070503030103030f02030c010f09030e09190f02070203060901091203060b0307080402130f0f0b040605130903050c06040b24130b03030708030c03100806090d 79
    0xc1075940c100140c81581e600c010240c006440c00d4854058490640d2110140101510a40b602d662203031400507a94480ca20004001390000d0004000003802981000042d02243c01030f0b0f402d16001c6401c0300d0844040e00c480150494407501d20034241508225000d101038429108025a89080c509075031002c942c40d00d800c00c41e1a941c02006240204942c180c032510b0741c1c0101a107a4504003042440d0180c20300d04400d60b1750141c0c03400b81002d914000c0c4542021a00704036421415079031403280035075408030b001b031041ea000340c808560252201e52920400159030341da4030b00003580101550409084500e10b580560040385041c5050041e40d44240c0f541070230b0342a000011078580b4040c42c0c1210a4064548851727507038030840d8240410810a0030450f4400c442d039082486204400c0052030b8001821b88803000d422112071180300907040d00d65000500b070b0510240442e1300e010f01d2070742e42070500c1d8011142042c98400110034050403001807401d0800401000c8028100c2e402c1c221130440d01e80300c04028007070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404099334 1250 404098084 404098111
    0x90d030f17090109050c030a0c030b06010504031208190216020d06060317091302091c02240d06171f0912030c20100213080105010312080c0f03 63
    0x4050301d1042041d88400110540ca444840c100607a41602802c900c1c0c00454250040d00c41c2d08890b420002000c40c22070341c100340c2c80f200d443d03d9600c661480c000d02811260402c00f04101c04004149207801e2842d1112680d62030035031614121604541c51524090912007031801005050802c1c0b03400c2200c24440d80c1c049035084400d4003a0b00d003503c020302c06075000904003a1758410700304203410008094020725900f56551507402072071402010492146410056000061010b40d29002c44204080c00724144040c01e0341d88004034030100e070444030486601ca4000039500055040059500e401040c00601c444902048440c1c3c1c2d040180d03031620141004400c0310a810410f402c044403013038014040030341e0070040c200b43d458078171800140513048018184021039010099481ca1081d6005024944076a041c05440320301e502100b510b0107948011325220b85004181004924501c0a2041500840c4075a05414030040391040241601c00020030386041410284010f6448400101c01c50f030b032200c040203204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404100584 1250 404099334 404099357
    0x30702152d09010b030a030915140d0c0e030303101d042102120a0c03030b0a050108060f01020a060c02070305060f010f06140d0510080c0a08030702061e0d05040b0705090d03 76
    0x143c0100f0b41e01960b55410f2107510250310070b0640001e1101d094a0280d00340203102104c04ca401c0d01c0b1441407802c100350300175003000225885105580b10307118210369454103801882d642e000103840d5030010340781181075981c0300c0420003980882c5080325018103a040c40405c51407405845e0342030300c0c0080d44c01490305d84403042d590104c001c2c03003402070460049244500e030351210101c0700010520120700d14100c01080c601000a010f9140402c00401121416900c5401d070380c0c0c0b20403d0048984025880c3da0562151000c0540010a9400751407a1690142d000f0205036107142411443e01001802e800059190a0300500481c86501c0c071100984156003031030201d0400d080721851040c4284000c3d0307910700d8136042c00d00960102e0a44000d040f10012011141c81c90440d00030401e00d0060ba01c612115a0310401201005007010006445158000c2c5030070440c513a1140c241d03031310319801001306110b9141e442042208100c0220060b54000300c403407401d80d04000b6170340c010518400c00c1210240c1400700d141c644 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 404101834 1250 404100584 404100601
    0xc0406091103010510050c03030702100b121015050306040807030f0507050a020d08040e0a050103060f020f0904050402040b100c020405150f041104050a030302010204030b09010c0c0609080f030702152d 88
    0x440c0c547c1c0c070a59007141c0da80e25114800030340b81c40f0030000301d442050410030040c95920b07003130700c0752518100030720050515242017141301d4005081c0600c907012645000040003510342e03001e0040510580c01851100c1c1d0320304451071300401203900e600000c0140305041c40fa0300c0100d400000c0510712294192010014250316040c548001e0155910450300214603c082169510f8190000d0b4100c030700c00c0e60240500043d07101400706a0044c500b11103c0040f0030700c007403201e501d07240e000103030458000b03000025040031040114264a10031400d6401081440e1806821402d03d48034090340104181d103a89102e075900800501c81d40010103505105076240c000d20000240c149080b10002e12005100d841125980e28000c0d01070b4000e407209035060400900011b903006018003070b02091490f16660340751604900c0d07942000800502100365071102c0c040c409190309151080007180500d00640041642000084d0342607404070005110108000c0f080b99050380c01080c6140e0300070500fa119200580c2541c3e14403c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 404103084 1250 404101834 404101837
    0x301140d020a060f0905100f080a0f09030c03170403050301030f021f11100b03061303050d0906050906090a1223030406140c040b0f0a050909090c040609110301051005 73
    0x14081e500400c030391800250f00d07030021440c0440a5032501d40013a0300740e5840c10880d0568401a04501142e01800a11550b17880b6074003655000421300d40024003690007a00780002c549900008a010030340d4501c0341014142c20500224088480070f040c81200c0ca495035004029001c1032100914800a101d10384046545d041120818041508400b440200441070004d00031031041c02e1100640c002d82d5242e01c480012401070144803c0c01400030902902c0e02c6010401d0401e501d40d05a040003c1840f4400c1030201c10f00038250704a01400700490340b82003202c1140c2c00c04002a05031400c961141c0250030000e0560410300540e4012402d01c108030740686151180c03842d007a070030ac0d28500c0d10000300300410010303640c1c0010204d003024884031806079030303040e03c0c40300c1d0b440b90340201c1009140078000112411803400041045085070b20f815401d04504201192410b4400c5d41c0f00d5010781c10811545545007802d204d0900186000c0100b844030211440310900144410b01459025029180c8007030f103114058ac0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 404104334 1250 404103084 404103109
    0x7090207030e180105040c020c030d14040e010905010504060909120806130509061006180302060d0b041503051011070b070e0d050a060b0603092e06030b011406030c030114 75
    0x2c15018900f00102c00b844040c1c1d0302406414031407441d2080c801401e40c4002520b0380c50450150003481c01540000080d1103800340445032203400c400030032002c03a0a030141c0c3c002500034150090041b4141d4101030410042d91020b8000c02c801074500407100d00490b455010540c0f1703045850401a00e5a00c424011507802035400303712215660400c0280040c0000004850707119084c0010925203007600d030f400840d11101403a00380118602400028405840e041d00200503995119000082040404010a0a032458444402c0080c0c003040380400c24000c0c140206001000280d10400c644040350702c0b04000d600401d04c1c082c1022a9820000304034138060819910604802059845803094074941a0b40d500c00a503003c0720602d0030f003c40300c100e40c11b20100303032401040f641010305a4400428550020300c60003c2c02071800140c9140c481c4240c81c0b0b075128500103580505c4950300227604086004500c4d400280c00e65000d81e00400070407486c5d0060304196410b440003000044035034140304000880502100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 404105584 1250 404104334 404104339
    0x2904020c01060806061908030a030c020307060504050c0301050c09012c090123090609060f0d081b06160f110c150408010509010905030901030b1f170c0c07090207030e 73
    0x282c0081580200003813058440c51003121604100000f0080b08030300f048161140020340d500600c0f598250a001e0b0f00450854000741c03040f00c2c108151511340d0340c282d80040e00d06490070780042410103403d040c04c0c02020f44c020b0542028070b2802401d400024101e95103201c48217400c1c2000d00b52182c800c40048000c2400e01c03802045410030b541c543d006e41c10214201801c00d895046030720b040c0349050500a40c86481414014030602c0183e4a0300306014503000640c0384180d200802280c28400108090050041680240991500f840005002c245802c10240684981e101c155040012131544040a0101e200040c07810101c1d401c0605c1c0d605203400d4008020550005004101103103210b2948041d00c100c401003402445551a01d0030b03083d0880d103808001500f10b800170419071000d54080d0300000d40c0050054032541e6640311030514545681292a07910000580304042806140e192001c1150000d20b500c048602c3c0040c1609059610411440785201c00380d004200d0005050050030084000c0002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 404106834 1250 404105584 404105591
    0x702040f050f15210607180308041205011d0c040c020c0a0b0a020304180b0f09040309141c0b01052707081506070c0603050a0b0f060702120f1605042904020c01 70
    0x1844e00aa480d50021560600000e403248500480960380c03405600c101c1c0c1d08940b0b09444e05003060501450304c4c031054820f81c0e056407203035052080d290944090000b416401d50160120b1500c000c2040b040d54100d180e07842c119809188125605c1e0b03070f0503190b94115554203030300343e548403280a416410360065501130151900d401d69003500c90030713080e04003452011044072412004401d01040000002050f1000b070005290104140b00400d03000034407054000740141001d80040412010040c410103292049592408a0004100340e05086150150100300040000004040b4910345884410000c010f0400c0110140101e16000350505901c03048010113080c0c01d40da0710850a0100c03165811b4411000041e29042c00110801000d01c24103a01d40b100404411240e0800760400c6550b401100081e03a000000344140110f000c41048002d40c0c201c8104041c1280f40300c121040c2440384c841e54005801981050710701c520705800c1100d044820402c08400344001d04100000c1030003402202c400d40032a40c079 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 404108084 1250 404106834 404106889
    0xe04050703020901060c1b061b2118050405070813020d0b13120306061223040b07022e050403120c031409030901140f0702030a03050702040f050f15 65
    0x107008074400c081034018420b03040c21401f143c2c0c43c1000c2108610844000030041180c2d54030310000f408550420301d001d590b610341c8680354000f02c80b804403800ea0f805408a1080c0d51040345110000301400c0040c5000c6070100010b103008140601001e0703001307111004050000c0e54090865035000c1e140c0c1d0040d608001020b4146c0b4020392040c0301c1e50003d0030292401c0c05081500600144070b406001c082d100981d81348400c5841ca02d10a101034540394070103580d1130440640c818804040700006522550040320101030354141a640641041e0060700b2958800c50114000b10800e410701c03552145040d041c200014180d5602d0504a070040ca80801224089040c2000904002c1d41504000b0450400360162070454a403013000176030f01d115101c452070200b0586212500c20b10748800c054064000140e04551804103c0d41c0007030704000c110701c800c5010031008243c4100303506051248802e05804039804010600300ba0410035500d100052002c00386546403507110034941c8841c220000010310241d00c0092050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 404109334 1250 404108084 404108087
    0x4060618051801060303120c05040825060206060901050607080d0c0e01020708060f040b13061e0b04020723120412121e031d0303090c0f03010e03040e0405070302090106 74
    0x1a080e42d8000d0404441080310740041818807420003100e5041e142c182d4070694201020018040440c0c8810074003109100000d20040c0900100e08000056021011010392000c0c1420040c880c60b000030045601001c104105911140c1d1003030b0654404030307612500d4070307000d01c1d0524085c0b00705904040c80c582400310840209030805142001d50340241c00740d9582644601e81280d0300d0f20211010400c0d02c2c1131502060115011086054100303003500f031030300910340360b40e1118800d680300e070309155044400046c540c00746051603108024800e601120b00303520b05401501ca01034460150300c404199900f0708449444094400c0081d0030510f0980b80c60682c48640c3c03801c0615221201c62001d4170219810792807984250300c925014803654131444088a2109690f1a0441c014000302c0040e00801e80c403400300a00090041000c0d6200301307410b400a091002490060002d40b443c0000307070a02984c181a804066020080f06580a0706d000010f02a220360b01d90920300e15000d403035072000e50041070500000c10800d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 404110584 1250 404109334 404109341
    0x207081b0c150304020603061903030801060e0904110f1315140111061503031c05072003040b1c051806060915010503070309060f4104060618 62
    0x15065001551500352141c1c0a0100d080d00402d4080210902000004c00618000d809140c00490240454100c11400160800200c070260801e0b40403c0380c0a0040280c550301c80408024030030155840d0704036007403559889142c9403c083d5220710230714441a0040440e280c501e411503030114015400d10400c40074a03449520040140100f02c0285000000c540d0305502469107010500348480c01055503545103036030b13003c9002420b02a40d90500003040024003410991a858410460040c8009a42c0c01d103006d02a00e001c0d20412111601e10400c103078403403481d10100584084034250368800c1d55070440e024108903d9041c02800c10b031218604014030010041c02452000d01d02c3c000000c0340d8140d1260010004403200c1150391540c3c0101c440d080800d40d500c1000910f403c500356003008510071500760b0312201507a01c20a01c89030640e5445101091034020016503130308001c00400d0807210403640b0380e001616030349140550300000c4150404a01001900d91044001703100f410510000a002541050080c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 404111834 1250 404110584 404110627
    0x806010f02010b15180a030b06060a05070f082205152215021908161a0412090f180209030f01050921190818060c070c15050409020d020708 61
    0x1040003000340d0701c05050440002c402d42350081c0c1100440d0f074614003042082c0e40312428280c00c0060510107a0005aa451401d0450b9841100340c691940b5140704072a800890b02c50f00b068450350071074010132598071400c401c140d044059000b02c0350303074003111b140d0b0380e1703446101d100b001c8a503010790000045e00d540e615003a10107a400c2ca500340c40d41581c000789a0701001c142d025010b130035803c007040301510a4003c1180c4410040c4105006280c21110300700d07000324400102c9042d42e0343c9007198442c00c80c0d543d008400c0d50107041c400c225900550f080c00c00795100350220122440340c896000808183c5030347e00f0131960310040c5c4140000c0c02076240c10029280c50310000c500c070202d01e03100e01c818030800712070204c250b82400c1500c28071019074915907542226041405800740b00110020015481450020f1200c0f070b210b82c0710b2070551565a5500c1c90b0501946046c0d900000310a164802950551380d8880c0c122021075440c0340d8007503150a9041d845c41c00034800e03c0700c0240301403800100139017a8400c4031428802c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 404113084 1250 404111834 404111857
    0x302090a0f0e120f0a090b072d03020a0219080d0906030b0a08030a1409060403050601180e190302070b030f100503030903070302150408010c02030310060903030806010f02010b15 78
    0x2c4032882d1a81c0d0380c80000111500764048244145480455a03402510860840b40740482c801035840c0b0820741e181c1d10160040d5041c1d0b0304803000710b6030341d1103010350000c000822801040c0e21031030580b0001e49401046900905c0b03030300d0345a540500c1d02030503009480500340140c00d43c1d0a000600320064403c068600c0340d8004641402801d02c0740b4686031081c041154012800f66141082c0944202e80d024500710680d007003d00107111651051700c4404c0500051071040c401002e00d54100b000308d810500036a900c02c61101e0034260306404900c0b0110303080300c4030340b2400001400c8602c145003e82c2003900a80140100f0a03012040024906c807144420340a4035014208225260300e88082c10b8407480b4510300701c1d4050703009040810041c00c10902140d002c1280540e09070a0948408980303080d21301c08100a001a0700202c01c0c000451124401d00009044a080428116186a80103005c115000b800241480302441c1000d0300c00b4001c0d00b150b03009203001404cbc1c00301b568a07072115541c00c2e000000c40c4130 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 404114334 1250 404113084 404113091
    0xd0e060f0c03040b01090507090b040b07030318081204030c06050a270c060c081603030b131a040c030905010507050a020d03200a05070b15090606071505060a0302090a0f 74
    0x1005070409404803402207400808484590b0f081c00403500140c8009894a01080308a079070019481a400c0064005042d5443c042d583c0d03480c00742001026920400843c5000c017100d00519400a002002140c1031042c02c8107200c0b82a641d5401c00340c40e81c0d648410007400c0741e804d040c00c102c01200303e54007482e050082064068810071201c1c8410005031a111030003400c400c104181444684e00401101032510300c0f98448034a03282540000944065041e80210082034403490305003204e190aa48152031110340070340400c42c03038a408415240b40d003c2e4990060180e40d8500312840070900c2604004030384c40d0010020b01c02c07410102c0c03004145a100005200c010b004c0c6076480100d40703110740034100e00c14500300340b00c4245120240c144c5501c3d50110340c00100f408810403003000080c030491202031068400004002c0d01c42802c40038401c0d21480100b804d4815a010400000007a401220142408000680024180e43c07500b02080c185495a000698408804000c02a80c0c510603048a25440a003203800d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 404115584 1250 404114334 404114341
    0xa0b1e07080411041104230f19030f0f141b1008041704031a07030b061207031d030d0b03071202010906050a140a020f06091f0e030d0e060f 61
    0x8440180c0191401030280104400c061054501340d0041d100d101821581185010740e117100120300408000c0401005030341d0b01e6016012071511000a101c180010341d40030500003580d07160018440c0107400004c00c04054441c0760414000c0d040300315030101d94002c091407a44c001c04070144c5d0756110140d035400c40100300e01503c8405424044c088440907032071501c5500e41e58645540f1780941203c1001540b00300075090100002059840d05013400c0425000506001070a03e180020282d5100e40741d024001e0004020441c02d05900802850f0300511910307000030307045c2d02076050341d040c629071988100c610312010030101d6001000d54003214001d00300300e00300c0741a103946080080d401c24051402378042000e85504003e1140914020a034104242c50322400d0718070410700d05452900f00b40740c082c0060f409a00d0500000e5070420905401c809500c0c02000700d011040f48021400c00301d44000c1113020340303d5411142001c030800556102071802071040c040c2c10320007031280b5603510045450802003558500803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 404116834 1250 404115584 404115587
    0x20306100506040302090a020702030d18080114070e031005070528090509040c08190203150c04060c060906020a0503100905010501020a060504050a2f010302190e030a0b1e07 76
    0x951089840182c645800d00d80796808001e11131400030510034a55800300b08050040e581401071b60800f11079602c0b05004604199100c004141158004c108181c0c54980442c4101c1d42d5020000d03070140740d9150442c03178403444002003410807040c66a0661400c0c20f2100703001580d81c0113000b40802540c0100380c5144810f02d80d08a44003080f41c8003948001c01d941c01c1e0144030b0b500f0a21003641d8064060b00b80c041006590711542480d200564100142e107200c00840c803c03c41c03400f4000050074101e4032843c4030032400c204008815038811485004240800d17001100c04000b1560070000740d42e0780140c0119200d10080101800b107910860b50f44642e55224800420400818854076041e264103030b0040100e4182c82e030721140104409001540c89101b226154000503940307540f90509600481c040032156640503403440402031260b82131034145030050001c0300d1210401203040c80303161030070f280c5200441c82601c0840d09110b031029015020422050400c008070b400c0407202d06c03180c01080f4031080070750317140e070300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 404118084 1250 404116834 404116861
    0xf1501060e0a031a040206070c0e04110910060f030e0717240621060412020d020a020f04110405060409063b1008190210090506070605090c1507020306 66
    0x400e1000c0c514900c4d800d0034212003c1907030042c4041c1c00240b0305009030300c512002c0e003166400514511007040400007041500c4001003a001c00546002e07040d4244903c1c3d4814543d130a00170b80d030811400c43c1c24110780602c00d8200315001d441500a6580942d111aa040300000f070180340c1081394810f010305141c415101c4c290300ea020190017640c04100b9180c807002c1110b4590301540e500f00c4441480d2540060308018815540181e105031074061039408404400380c1000861040142550071107807822001d61217400e4a00e2a80d1400c550000752040041700030255805682c1003150400b101103800301d61180d882e0f001d5000e0b1604055403072070501c48489031907014071181220410300004144810b50032100c44c2070345604001502400f8043c551107a84040c83e0841102d0b103a61941c0c20280c40205609001e648858140002d145c4060102d0500c80483c040d403080100c000d0045980d400007504d0000d0a11040b000d00d0740080943c42c00000124002c090f58200a006074441c0c0030711004602e03030800114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 404119334 1250 404118084 404118089
    0x10b0f09040c1208090909060a1d0a03080405010216150f020414120f0303070e0f0603010503060c0d150f150201090201090519031b1a0306011205090f1501060e0a 71
    0x4008106a41014250840a00c1001d000c9030013200c1030019070460b540303140c82d1070b02c11a8840001d140c545040129082510035048002640d043c61440452006002149003000c00b0b0305400c2c406125140c40c9007080c0203106100c0200030180b40c0c00841020040100d000781040441a081444401c81c1a0400e0007240f080e48100b12200c051484c0003512824049000c0000b00c00e010141d4154108104080e4110b40c0704407282c10020700314001074206407800044421044030f00369034072402c540c1000301099440c140a02092150180460070307409028042d044100000031800d0501c8065079541c4641904400380d0103060b84181c41a204a050144148541d8880c660147c1d0303500a001d00d0302c0180481c2c51001070300400c241c40708460100109240494444c071000310016030243c42d0f03151104a1802101001c0b810b034400300c040051100680e03000140913680b038124840080c4039294404101e16104038030b0380b080610700411034130401c03142c01100c565040391841e4443d0f000d015648001c0200782500760 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 404120584 1250 404119334 404119343
    0x180103030c0510050906070f020a0605090319030e0a0201050f1303030302090a060201090b040b090708120901020114040b040b1005040906050105010f050f1e0c160504060b09130c120e010b0f0904 85
    0x100e0000e50707002d204510700e40c00e911549c01601d90a4441e1b40f50841561011240c40f0941da00009540c043c884025420020030710040c9070422100040101d01c6403940542ca00103410400c0100340ea104640304002141d41c51410603952095450307482c075020340650000341003648540742180d000150b040c01800390400c405e9101c0401804c41d6101e5172203014042000e42041028810182e001c200044200440841c40140f81100c42c3c171071207c00002829100d240f00e80316140c1c030070001840000340b031480003240c0103030303200304094481d03503d260488040e03444682c031aa40c018201b517080000c0c000a070f401503061f10000c1c1d9462800c0c3c00c1005050301d4900c03c000c2c40380d802420810224007207e030041c00e03140800c8420300c0d08070b1401d81c0409410345061141c003180c0d8034018400304c04103c01c1c5001c0c854180102407520b0700900b0000340340f0014000c118801010045240c43d03504c1000128850064141c00c0d262154080100151055942d8020604014400d006290f200850143e51415140fa9071189621 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 404121834 1250 404120584 404120593
    0x9061b15090c0914040203120a08010605090103150914012103050304050120040e060411040504020901021f0905010e0a08031803040e0103110f04110405010e180103030c05100509 78
    0x81401040c02856281d005403016114000c0100e0440c0c400d009403903d404800304c46803000e081c0f5004050400310001c0c2c5142042404000585803d07400c0050141140c1003828416118241080140e001d4544210400041210003201291080c0719074002c071614910341c2e00d02400380e0b03200c113142c03000481149000c206141120280c20f000034030030740086a120340b1403800841d0496000368074506611150790b184010300400b00c1c00f4404105410358550303100e542240c05000312034010075080e0709031266006003401207400003100e0030664020080c0c00e01121241030706a401c03601c0701417028020a0111070403503003542003824440b04024006403003a082e680081481e455034070360302c031840654899201c06102c1404184000101d106070030300c01c00e000354040e17068000280e20755410403e00010341c0036810710492038240c8809100058209a406482003800d0040c03d8100340c000080f426401c800860a803908040700220415601098807004c0e10300c6002103da80508010090069980c1160701c426036511 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 404123084 1250 404121834 404121863
    0x10c0809030d0207140703050604150506060304030c140f030c070e01030803060910031a010f32011202070606090606090e04030e0612070e030d111c02030c03030709061b 74
    0x40358000c00c4c140e88181500302601810b5002c160820070769900a03100c0c0d0b00000c04100c1440000040d5045e04052030404201c40c0ca8030400198040c04094405400c1201c0c0310404c1e401c101b160140501c01c040c694007182c40c144c0050300e00c2c6549600c0310901041c50b0060a00010b842c0c241800703e141a00c0e84050780c5070450f40d456047c400c0c2c1320402886450341602001d0000b01041001000326207919400d4409400340d1304020700101480d4407980044994440000300c1e00b89815610440311896009110350b400f0040380d000100c40654084090003105840000e100003005004d90001049030080c050901040b81e0740d00e800e550701c10240c400d20903d080c8400000300040d00c100d039524810b040c002c1171141481e070425070400030b007001118110b0104100120406492038200400685a8a03500c1c2c80380f18003041c00740f03a588422400d00c40640030480c5c42d00c0e18410900a2040c3e600300e10a013003c81e51079180468008040b50624403510010440408a03085083c083d22050808903820589e010074858 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 404124334 1250 404123084 404123107
    0x2a1104230103082101060c020f010c0b0708100b0c0102030a060501081e07030f050109140a020c150612120d05070302070c0e060a03021c030e0415181103010b030702010c080903 77
    0x140042d01041d1118804c0380c600040310034103031105004e42410303510b42c201002c0300d2042c04811078011001905000c8011100d01c009411805043d0b40450a03103040c2140383c90311420b2404c480d1964008501d1102d010403002001070701507010b10300c1106807000a20142e5611001501ca25106075500442c4244c3c0e1030214034480c483d03540040c0c2003034180c500082d50b10246074559003210300a802500026032a0401d5031094650b00b0f1040e074102c05802421032404102c91807140d903c80b0001c0c2245581806d03040000c6803a80d4900d004030323225036807500399a0910444089000958000889000072a01e0030780424009486482078582040d40000005603150404003503034070700e07400213289a0b07000744414004001611140006101d9085070900398000302c20354500035080590082d8464022850110956000b0440c0020702046644410140061041d031440c104060038541c10000540d40000000180400010707000350300c1000a40c0c020030038840729040c21101c06034241c0d1318690700d41c000c1c4044101030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 404125584 1250 404124334 404124337
    0x606070210090e04060603050f01060b040909030201020f070b0f07020d02060a1d0703121211090609130905060103020a1d0109020903071a0703031d0a032a110423010308 74
    0x1128241481240d241e500c11079800f11500c00c43c4c040702c00755140d80003001000303001c22600451445040081c0300943c01d002400100780964415041007076240e07050001490300170f5040301d500074003103100140c0d80e00e403e0420b001e00d030209581c090b000e10b5400c0d0000d05440d1010814600c54185139015040341e440718204000a0001409c00011742504000c1c03180c00c500080100c00300a40c0300300103030040803900500150480e407508502c500d156040102c0c4940010421049480300202202d50a441d9800707800455200540e0001018490780351060300d000344030300091400e040728400c0310189081511402c0b1005c0d00030141103003d9203110104014030440030160054140e1001c050226003815599000080c0b10b05415907008007000000a80c80c403d040d0315015110244903c8410041c0820b601511155030f4404440042d08010a80c0104050244580381003074100103640b80b1a4031103d050b0428216541c5042103481c4554900180c422040170b442c56180c08041014840c142079a1840d10303624182d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 404126834 1250 404125584 404125609
    0x7080609190611220603020408031b07030803010b04091a0d060903020f03042405090904060b0105040905150f09130311120a0507110906091503011103091b040506060702 74
    0x100b94640000e00d0700e8410031000380029002203401512800c8000e0400c062441c0540c0000381090700401090015034400000c072901c00e80c1031404411060781e503401c41340c2841d45035000101204400000000c2800c0054042c106484203000d041040e01c240044600006282c64685600b16154406803000b044c0740e40d0003d4801406401510400701c1c5504000c2d066610981103482c0300d00760720383d42c0151a005c80d21000140f29060400f140f800c099000080e03040f640c000c000602c040d0312990100300c3c59206400351001070078902024840c2c3d0400001c41001480c0100495029030030384101e6541070b05c1c20964003402140b003142c01d9200b130170498604a40748000c1c1000404030744540ca0802d0301152030a0028003000c0002c0e0f42e0b6680f500d540d49400e0984441c809202031103580c003c0c05014040d500c2130580707034014200303521100d1022070b0700d000309014211940c0b0b0100c0f91000441005080000414415034810804061140c4115003a040008443d015906240c001800380418001801e11130002c848 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 404128084 1250 404126834 404126843
    0x9040809040b1203070302062d090304030609080a0e0d110d03030b0a0e011a0408030415020a050a03080a1508070b1c380f1c020910080708060919 64
    0x415001e500c01083d10442c151000f080c456000107040303070625034144006074200703500c119803000c00114465503c01e8000385102405d031021301e03003011840000003002190000c42c1e20035014022815079080040c85a000b003801c0502007094120000e10a141a181024401c1ea000c0f0001040016040c00c2c41020300b07003050708a040c035584420906641d074641450303200910028005103910741c188442d40354400c103ca903101114400c180014440c2280c08410f480c00d0341c01d003040c841c0c00403008450892821072401e4001c0c0450081703600c1d00c03080c1548071800b948119000300d018810110800c4030f40e00072880500c41d1080b603410540d42440b150000c0001403082c2c41d19032742202c1030400d031041e03076030212035001e0b01c00b080401d800c6248007101809404129202c0b030b010a012280c100c51a80481d000f0640044030030300c03e2910061000c440d101043d40d2054081c0c0146c8041440d2400c9803401203402454001e8100c54800d1030800980c6e07600c005000e9104e8603900000e000040c9990b22070101340388100c1411203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 404129334 1250 404128084 404128091
    0xb010c0b070e0a0f29041e05041d06060f060403020904170f07020108070504150c05100c03090611091008220302010b040605040e0d0c050c0a06020a12030207020904080904 75
    0x14030030380c0c0c1c02e8200c40280c9400c0100014240c1707403441050285192241c100d01c0d044441000410b00050001503d045841d0101025400521038034010702070340d00b64114907030061410f03040c9001601c490360458005951402210144d031140e1003005200143e10622661002c8100420b1005041107203940da0418403030701140e10b20000304541c40c412a000203605540441e400f080c0d403030642d070348462056000890ba0604914050a0502d80d000044078130a00105000c5c9900d000342c100001000071091002c400da104010740200f2034002006441071640648216003411000b94402e616001180c0d00a80002c201c005000900c40701030750b03401001800c1c00c0c03000c000a06000e030740c21f0700140c444050b540700780c1c00010a11003460400046445907000180680e2400c1d0200d0170f840705c0022001d8408a560400c40030007071035490102d01c0c0103c2e4102e00c4d6000101250001240c940004180810034410040c1800007040628110304074010414065809100d910204000c01d180358001c04402c0070281010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 404130584 1250 404129334 404129357
    0x1a0402090f060d152a02010b010c0b01051e040c020c0f101b03090305030313060e060103020109090e0a0c06112a010e042301090b0607050d0e0a120318090b010c0b07 72
    0x40030701da03a180c171054020345541e0a59482c00750703082c03084101081d801d00701005100815240c8a91a00050246d24003900341c034440e0305d42c1c03207028000e0030755034000050042c450b188000c00c00944413070f650f2160ba07000d03d006004e800c4503864640e0841c0d0964560740c0d280c031110300d5076940943c10346181c210243d0910a00c40d0f0301001003042400218071600c101001c100c9415010702c0c0c1541282e02c007803020b46617500440c00620041c0c4e0703c100000c1c100c1d10384600200b910321352084840d082130a8400d00504504c034141c8006511034011040844070f0072480c0507202c0000401002048400722070b54035500d07182912401c100d0541c00b031044500c000e82c01510006140c844141074061032042e04001c0446101e4100040260b10140e005085560f0807e032009802c00d4015640c955890b041050b21405001c50009044d4030740d154100100020710050321007003250646402c001d0041070f81c1407207203417a91650741c0c004554250203014840b0780a406950300103444895469039040c400c0007030302200411441c5240c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 404131834 1250 404130584 404130611
    0x2901021506150403171b01021608090f040501140f0307060905060d021b1f0b1503040807080a05070605130203030714072324041404091a0402090f060d15 67
    0x2120204440d0b201006d0780c41e920742c94031500000080c0900c4000d03a00400c0254801650ba9048100480e0f00200a546400d0307a10001844603060101603900945454000150180c100306850040e020544200d41d8901c12030040c035440345407502031400400d151803020025414598014075061041c19030050034800c0c00404110128155060103245034010003c41c61000b445548450304a80014420001e030085e88012800f1a83c104181c18101800031000806100c5031004072448280e02212059a54410280240c01c94202758405d13036103940340800062802d4035941c140c1c40d01c03070340041c000d500380011039841020100c00040401ca4900480d40b0014141f00104000a00d12211510f640c401d0540641401124441d2050302143c1d02170303c001e10b80e00d040c03503402220140e4468030503805030502180041000b42c000550010010301c401e0071100d00107290005000d01840c4200c84071070003a20313920494107040405603100c5500005601c0d0020008001c0380c8240f60780d004151002c220300704c1d40901c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 404133084 1250 404131834 404131853
    0xa0e0613050a0c091e0b0708120f040b090102120c0706060503010c0c0611180d06110d021902070e0c07032303010e09071503020a050d2901021506150403 67
    0x10345901c03464459441c0d80f04503410040d400080c001d0401220021100300d100d4030700b15000d80c850f0708858100000c24205009541d8100c03035000300043c407c0e05a070300b000300d07500c0b006400843e010748800c1ca800c40490210801802251080c078218541c1c102252680842d4031000e50200d2000c803800c5030b90b030100281c00e850a000d0004030610984a013071241240382000c8056814000c03001c04418000c01c81d0514054556441c580300d0801668182c0880782146083e000031b1a40c14000f010040010800d052200f0341074000301442c4c1903c0714642002c100010040c2d039290082c1c00b4201118581d0400035059124074405000321502a2030000c40c0c5200141410f4a800d1814048040e5244008010b01990811100051f0840740c048003c014041c5040802000040301d01c0c40364080640020b4102c0074140700e07000380e40c15a001440c04003d240169510302c0c1c0c10703581c0940c400c6c02d84100e00044601542c0042000032007100b030103491101c030ba0b441c034080141410042c284000c3d894810f00000c008600c0706035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 404134334 1250 404133084 404133091
    0x1303020c09131709010e09060d120c080d060302010e010804020130063b04030c140115060801050303090109030f061103071106100b071502091201090219050a0e061305 73
    0x50002e44d03580c41d500001072901400100c040d010303203460b2003030003140d45403d41052401c54024510f4012031350b02d1710381140d0048500c0c5010380581800f00d1701010700015588800d0407a4803d0b202d103100040d1020054500440807640640464850510240480031006807110001603c0e18a9034030750060780000404c950b0603410148041c03002003460010081002e5000010000181007190f00c1f404455103030702c0108004000404028016003100b0411145807507020074150f20038002d1020301071408800c40620040d215100015100500006960030044202c40d40c440c0180d54508401c0d0864540111311501c6e0001150b040d40d5843c2c00842c1d41001802550003029180d40c1c2c69540300103520032516040015080500c100842d1808002030b4108008590450354440400012040d0a081d4078000780039106185401210320750752107122550651050348240c0c400c07a01c480e08008a500c2000074841d00d8090150084084503060040800e08000c403580180c0040c00e070720401c4440c2403414143c0e442078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 404135584 1250 404134334 404134373
    0xf04120825020601140d1709011814150a05071b0b0a0c050c0a0e04030e0a0b0d0606090807080a330902030114070e280b0309061303020c0913 62
    0xf8006010341003401030f039200c0d22002103810b0401800140ca40c212200342e1341468100d00000040d007803e481c0d001d40841010500b0014110181e5642c0d24210a100004014510301c1101c4030030800541d40540303400e5681441680c0d8455080c08807e0381c541d22403007900310700201d01030098075000400d65826001420101940d41d610720403403038246800b5280542d01400340d84903048171601170003a0b45560040c0ca90154046c501081c920300008081030a04185420410001c032001840081146031608104203d0340c055a40803030640d43c80b010b1a41f241c0304c500a900c0550041a4503a000c01c2c100e8190300824031041c4651402d41c00184807a1040804a510b1020a10b0b04d415038a419450207100301842ca20740308450303000038034195000900c0107003109c1036584510303680f00c02d0003c2c0e2040251b44407042c4503e110081240c030745603200c68140b42c00442d00513a4074841c1ba400204140d40391403108081d035034142c0050120000b0001000710202000740400301c61011030f42c29074007240c4031101d481f4485911 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 404136690 1106 404135584 404135593
    0xf0a02180a0603020a02070e011d07050f1606050708040f021003090812041704030510020d0e10050a06140306040f050114010303090602060f0412082502 67
    0x40150704545a81408114503806a000b495190324903001c49103d1a03031250107150000b02401070400b4501e440e62040000310142c175a0300d41042c440c0c10b09074140b514905405030742c1c0c0c1001c4484440d86082a0909040c02060305c0342582103811484c0c40d40712461309807600c3e0042c1003013070030007030003076100c008482c070314a129602c1600025440b40c4902ea035006908000c2c50019001c1d030342910416050070170031070b01d40308072012102200d50003005001007001c1038030100700a400030f4403080041c03030701e0300c2c045041410700340401141c1e000f02c01c00005090500300c075000308070f540320340088401e14407c1c40302c070300555000603000f0340c0668004941d4049040c685840781c0034050510f001010440000004400c064006000f02e0648151380d01300c034059a81d4140341c08070060140c801900f1341986250020a15118400c4240d0000500b040c0d035100a04020700300c0001c591154081c2c0042e0032 = true := by decide +kernel

theorem cover : BRFrame.Cov 403956834 404136690 := by
  have h0 := BRFrame.cov_init 403956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403956834 ≤ n) (h2 : n < 404136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
