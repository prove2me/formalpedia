-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:51:02.716605+00:00
-- url     : https://prove2.me/submissions/078f0adc-489d-4209-ab09-9b09a13aac9e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 182733812 ≤ n < 182913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 182735062 1250 182733812 182733829
    0x30b0702060901140105010c050a02033a05090103090519050601061106090a0b10090218090a0c120b060c060405012711060319050901091b081509070305120405 70
    0x7101d400003000704c1103d1600d01e452001d0180110f904003d40c40550f0010840100440c488041c0c00400311001505100c1890102c071000848401c0d41048070300285841801462070340060b000203484a1341080d5220307004400406e0f010b8001e8070144554850500d24850041c035442c0c1d001e0041000d0815907041c0301020303212143c4048c402d01c070341c0c0c0a501040142d100108a92811503440f0820340d5907511000b42ca030702c0b801c1c1a40c012606482c030005a41c6028a21a0940036060030706807a0030340d02c3c1d0b442c1210320b4101c40b0145010300204400420004100905034001d219504c1c008101ca400c0422841400c2d15080301211700301d034030340e40d6035020910306410300d000b5041520f98901d40500421041c2d8032000480c1525504c20300801d404004203070321f0510f40c603d000210140c4242005580380400b0303558040e1585039000e40b5010303011200c2c1003000d20000b180d042601c2016000713041740034241d0f56031a404030008140c0d1405008602d07010001800601242495404034051aa111403c1100300030098 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 182736312 1250 182735062 182735071
    0xf0f090f0405011b05121506030a09060507050405180601020f100e0c06040b04030303020d021c09020f0f0f12030904090f03020606091909032304090506030304030506010e0408070c030b070206 84
    0x8910108100c44c485a1000c12201c014040000240d1103899076003000d4040340c00e5018213a4080404400c1000802c480c0d80a41c0c2103500404c024042c0383c4800209548501c102d000303039a0000131031140c0e030308a0205000140d40000c0c040c41112014008803454a08043c036660000d181c15440d12040101c88004004604a840f0301301d601624080c40d00d081d00540303200c0e41c4070050a05401003a12500d0040da40d041c1d070005205c15941034030000c20400b02e500180030041c8128403400e183c10b03c80d1218103101202c2078521b84060b00000c4044c1100040150324103c1c13144404641c40200040748498645026003074105100702d454603407142181c60080d0801e08001c1400d8024400c0d003040012110a02c2194040040b00c400c0020310814541001c841b8104009114418030002c41d0380b9400b400c44140041085600e061802c000f25121101007640700e115a100140055000c40018001000000c040e244c00a02c00c09450b407030203000e5039541403950394581c030036600c0350b00d0841001881074051090b146c0c407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 182737562 1250 182736312 182736341
    0xd02130510090807090e0a140f06040803011508150d02130912090b0702090115170c04080c01030e06010603240b0304021806030604030e0411030a05071e020703020f0f090f040501 78
    0x346100140907d9645070200400340c02d2a2080c02e003603408441c180100c02c0100c60900c1605c40c0c0703181070f081c040d40d00d510038410b0f403501d00040c01e0107400040c402d02c0036600030500c0c1c1041c2e85918004c0c00404c40b480340c1c004401d9a2006841811010312441c5114282c10705108a01c41c1102c0048004068006a8644d100586103402000b541006a80d460102419182045980080100e1164084404402550312039802c4200b54081c03104e9010140301900498480e007089880381e1940000440607100c0c801c014140c01d501460042c840c2c3ea00907003040040003040c0c6000300c03900210180d1200f02e00740f994464803041074008240029030400310303080c602482071a1004020f03420046d0200e0783e501001030000d41080200d85c410002a940e81c3c02c6507121a0030307035070040d4a0742000407403c0b004100c1540c4480204e41c10300340c40c101c07038901100051054006500508222031440d024016004000f619442e809420395030790305c82c6a038030f03041d079503000b12050b10200d810b80c5403925003142142c2c0b10711410380d00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 182738812 1250 182737562 182737571
    0x6060206040b0f070e040c09031e0f15090503040b030a0b010302070f03030507021c020f100c0f0c0203010f111819061404080d020f1507050d0213051009080709 70
    0x4660000507064010071110300380f940540e00c44c00c1c2251580006401d055010341044828401a07a002c0c070b0a40507240500c0c083c0c600528920415920071410102c000c0094203104800700120f00000c01c0310440c440022000f0806c001c0303995645041d98001e4120001d103141c04000d0100c440064480c0c0d03003100c482820110702e451100e89404880c50303802c1d0743c02020991284000360f030181c428014050350150350701903008a10040c1d00003070b40310724828019040303a02c0741088840250410780501820f90070640c803400681d54002e40200c0e981c0c040c50038180c1e095922144503070f14a0400b4410000305084805a913912462a15600c6151200d51078809209580c0180d0003500c40b11203014441c12030f055400e2000440e03a09000e0030f5090300880c0c1c800b4030580100d4804484298000c12105980042542030b5404814103a03c5452010025180000003c005205e4110b40e052940e0050181406c4400002c01e0030350340f40e00140f01000da01010b0f200040c0d42003800c0000f15400c0015001074501e8040900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 182740062 1250 182738812 182738821
    0x1061a04060e061c0f060302090112150b0901030b090a0206030a0509100b0907030b040905070f031217040b09150106030f0e010207050607300212060910030b0901060f0f03020406060206 81
    0x740121051401360703c0c82d5030b80e860700500c400c029030300000c021503002e0107845035583d42c4c200c040c81c000d00141041c0d0b82c0b40d0092a145c0340c0040301d03114150b0aa44000c100d411f05034250746030b0800084004240c1034031f074406d50b00a8400340c3d81c1c52014510400403072030040369514041d8546401c00348801c1041c12800e0510034000d1403036450019981d40802907240004130b52591074001400b07012100310180450148400121759805da00c004102501e01606680c4081403407510100c0b4030030303101e00702d0307080f2455080e02040000c1d00007024035030460341103070444071074036125849100400000e0b4080000f0a071344660300a4420550300a1380c031140300010023103050001c0340d00c40c0d035203c120061451003007101011010740c20a442d801c60b014980c004d03d020340e911807a0310407a030009500040310980760040c4000020079038507114651501c1941448221a500ca1440e547c1010403003025003040ca407952620808210601422020001070505008401c661807039401400215649178100c403085410620800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 182741312 1250 182740062 182740087
    0xf12020102070b0924090405010b1c0203070309060c1106011e0b0703020a0807030201020307090506030103031e09270c03020a09060c06020910051b0c030a110301061a04060e06 77
    0x10403189000c0f07010360344285050000314115000800785582298504000c03040c050040082e0822500903a0208081e90301d60400306071a014808803846041047d03505106403d07040e4010f160041c402c0e080c045a981c500359580b00c181d030010743d02c4800060301103480d20b07041d2030f082004078010075145a80b6070034031078010765040290f102c074003e06840c0b4000140c0b83c030416100b0400c0742e00c03058000500580b511042c0c07800901035072041d00e90000140d0040004241442c188c02180d0403264503441c0c00c044581041d94040a01341628040340c10311882e14000150762030402a00d22801e410031480400c103060040000040f00ca1026030803040510500c105400260890340c00000d40c1d10390706050307a130024a8a0008080c4c422030010907005480b04058150150700480034004106620a0705110070a0f2854960381d2401e50048556150b4403d500c3c080100b48424120345650034003400204800351034600103000008001c640d6868800700040410020b07510056100e15040100d4100e45022000340e20b9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 182742562 1250 182741312 182741323
    0x11060a0e010810050d03050310050f01090e1e1006030e0c010e0607060e0706031a150f0705190302240603030706230c0a09050103150e06031e03040f12020102 69
    0x42070500c0404000700e818010100502002030400800a603d41c4170300789030003840750300300741e071800d21450100601150721f00d445034404144440c182d4a550940d881c1070314017818118088d106143c00d003150ba0341c00e161039204001c494400e172a0b620940c0304d00c2d85040d00090880b017081c5103404243c6c0001c81106403507a40503130030b820035900469401e9101d030058100704004100000c10302c007082c0300c1da41000500305d4158001c0d400e40ea155481045502581005014102a0020f1032200c4000c0402021041c81000c07400780c00841c1c041c03412034205807004140400c1114900c50141e01590011044441c040c0d01080f810455104102c040c900304c0c14104082a9203000780240100101d4959410b140e03400600144510000c203040844145402c0401800303c96500418003400060079520300031503954000d010381c107081d0b841d504010800f02c0c6030020100011602400c020b40c036004680610301340a000105007265100348801031556540307499071019450380190b01605152540079040d40c0941e070041341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 182743812 1250 182742562 182742587
    0x60e091612060e1005090105060909060708010506160204150f080f0a1101030b1c150e030403021002031e21010b0a0c060b130f0c0201090816020402040b03040f11060a 73
    0x1008550126103c11460a2059400b1003c4050f4034000c1004608101500002e0081909030745a00306074540380c580c182c85001c00c482e2003002c075041030010022401d000008120380b80e10201204130b80303625540014241c031030154004078503040c2c00d20140000c04a2154110041800e07100421512a00f8211a40c07036040d880d102510440c29051100b00c00d03402a0010018000000d000701d0284241105c2d0b107101c151100c6d0252100705021500100c0c81d025841188040b420704d000440c146851039003008035444c0b144580b801103000038043c4042240010246010200043d06603540350108020b03d10451409c0c0384810340503170301250040201e400c0760000c41d0b04920b010b1802c6400e00c3c04509244024161042a00c3e030001c0740c0103402ca07031200481c3c2c800e112080c6141424044400c4883c001c034241ea80c2c4030781c06468804208000825003440d0910800c0c214805003025003860344d24922040c0035041103400b52030241c00203840b0303420000d8803c0300032596103003240c9043c10003101800041031400c942e01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 182745062 1250 182743812 182743823
    0x3070812090406090f0507021b03070e090304080105070207090b090c0706090204110c0d08130206090d1403070f03030e011406040b010504030f0c06090b0a12020d02090301060e091612 80
    0x1603881e038541c03101d8104030050a0042820700c5104030021812004110484080006014007684120350081590b88020b0a2100500a2548504002d16449690805080d0816070b210400c0005070211081c01f0310b80c411140c0382c0243c10310750314044c6c40005481c90410217520813041881000149404402030310500fa401c450002504490740c40070400402080f032000c19910800f04a05901382800144419505141d40c0e500e0003a4982c084100041d2080400082d440b00c414001d018050400011000045020700440202c0003c468141803c581c0840810340d043c003414903114040c0350f05030140e00d2010650301d0080003443d50541d100c038080079001c0e01e82032045880341c03050115681300340161000741d0780200d03000d04403e00300d160580d400700d02072040801290302e1040c00140d0301105800d981c21105a5103070b492f501c070141122600294400603d0514141e400d000040264800344540000b4010883c0c00f000076080c0000d042d07107080e81081000310102c0301903c003805080d02c00b1484094465006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 182746312 1250 182745062 182745067
    0xd020c0a1b0e16111f0c030b040203090a0201030209010912030207061e0e100212040b0301170303070f050703090314010608120408030d0c0207120c060e010f080f150a0905090c03070812 81
    0x43c80241000203200c4012440c1c1c202040041d068885d5a00c84204509180c0b01040400c3c0702c0380c144000d03800211400e41c03003900212014005540641c0040c491600145040220300b43c4030524005070754102402074006034803000e810320a00d42c1003100c040030b42c04c030422484c5d03404904c078000030800000c043c45603005150090107510f180340200310400702d48284179440d5489541791400b81e00a03400c24459403880c2002c1060751040e074280401220300489079550345240b510000d100546560340800822020043c41c44c40c00004540410071240030b80800c20004180c16140609051070001540241600118200410003280310000b04450120b0300d404404114107904030003c0c0c2c00c01c0480e900441040c07800da0030400400041c0c01e01841581c450b5240d001508543c0c03001118007030b0742510803401196510002c50f000280890345103070700ca1140410100e5410842d0041015420f096000c02502901d071030911049010500502503040300c01c1d00104074040c602449160342c1c4c0d00004002c145030100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 182747562 1250 182746312 182746337
    0x20101103130b071209030203030304060509120c1f050c0412060212070207030618020901120c0b0d06050102010b09090d050307180b09030c120706050d020c0a1b0e16 72
    0x62080d074241041c402400100c050752080c1903041544905021210a44c3d2582011059030094001c103003541c0c3c02400550440d40d583c0c1d95040101300180c5024468410441808000d00401004250603030071180030b000d84006490559101d0040c4510b45150b250500c0200401001c2c07480640301282e00300e0700100201410382c100310000b40324240361901342803480402c00c102075800044034400c036441400d0400100c000c206840d0544140f88500030742c40000c40004000b1a00c0c41c2d100c2e6031070940a1a200780281b070f603800c40482154001641510110303241e9004100c2d560702171241d40c3d54180152000800c0d4581600301c01e480701c02d034040450a00c280800480d0788948146041c5203004441c2c100f02107243c3d1a1a2440030395045030040780c0c030901c106081403e071800c088136034100510315140105849030801c4810344041d001071308007100d015800d10480d54200c1c3c0800071a1860f50240c000f02024041c132180c4098680c000c0e420506508440074180040ea4900a100c03220b054401c2ca402d181e0b0915 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 182748812 1250 182747562 182747597
    0x5071103070b0d0b0d0b01080a0c090e072d0603050105030c0906100302030403140a030213060c15240e090601170c091003050f06190c09140609060301060203072010 72
    0xc400e0b0029000345104800420b4817100021041601070042905503502c0e0b503200bc0d24015108259642010342e0040001089040d0989460080b92580b084001500103000221803001c5440c1c0d911500003c1d448000400039810140700b2204005800d641000c2c851400b80082080011110440c1c402c1650000000e002c0c144500300d03070041003501c00320740c070780e9140000b00c002c0c060740000c003520a01d48005500082c94900404200750300c1640868428040e001da1860600105140c500b0706e1102c6110703880307132800c2d5480c00c01414090404a085410385040c0781c0d00c101c1c6800c8050700304104c01c4135444080c016000000071a0099264103e502e80b0303041c8d43e0080342e401609034543c0000d090744580c5000b442c0110011605a10034099003041400c1216944201d4007030b5080055500e01051180700240f1165a140c1d050012440c8094882407500b01d110000c180039500907804500160400301d20081000350f05000950000e01e041c0c00c180c80c201112001030030741d208900d83e4609120642c40c038401e0030b10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 182750062 1250 182748812 182748829
    0x1f1d0d0e060c210412050a11090402100815220e03040513230a02030915010f0303031113060206190510140d060c230c070e040503090d0305071103070b0d0b 68
    0x1172000c180801001c0d540303407860b900c0d04003c100300c50019545001d4052803c080e0003551046800a207000b1356400c0a84042c0c8004001501c00202c0721610103d42501d030719020707006940c1c201550107200011580c1007e58046614401440c016508200000c2019a54205181101194401c0c0c00500c208241e0100c4804102114010019519071800c00c005c520069010b14400e40012042d210518a90021206010024007820700301d00581c00f170030710129100340d02115220f101000c17042d01d440c64003078042c000f810099014000580c040d00400c0040c40103600d01000c031440401080c045c9040c81c21034020850024001e2030200306030440b1241d8282d56000301d582c856600310200304084040742900030400c24041b01d0ba01c00b80e020600031400181c07003a43c00c40f109100550040c00445007001c566510610b00030b44103403440d2005108100711035a541e40703803180b4a44291100e03590ba20442c40c10214089641c0c403118842d4201b444104058002d142c00c9a260307000d00400060390a20f01000124050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 182751312 1250 182750062 182750069
    0x209030a150905070909020f090103030f0f0912080c280204050403021e01060f050d0503031303093609240212090114090304081f1d0d0e060c2104 64
    0x3480344d00000504a059036221081c280c1c026a90110a82111b03018080448230030711000b00020380b8096004020340c0302d0700c02c020300b030355039860148030003a601c1000d52010f40c44080299400781000070070101e804c0c810040b40c0460851140200d084494000c0c410800c21700d0498003a000e0780d15071001508040c800d00001c1d56107034000c21a0746c45802101e0b4224002c204500605000240c0803001080925001c122102220b902000030f51840e40d070030304488502c00b1a6002203040c498440e0000c1001800a0340c140500c003550081c02c40020144040701c0103485405400104062a00c80d100303001c1103529400d050507079803102c0000c074400214072400009224070710600105044460074414242c1c019042100c95410041d100c4a02e03440d0700c260561240318901c1030700c58503402482c0c010743c0c0d2400444644c803081e0111000181200803020301c110a412444404a00343d0003103142d604c003140d0004040c4008400a44c0c1240c28254014803903079440b00130300d00030b080c0c01d03c070403114504503111351089402a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 182752562 1250 182751312 182751323
    0x120e03010e0114060103090206040b0f040b030a0c090f03080307181205030720030d0e0f090a141b1e0928240c11030708030a09090209030a1509 63
    0x8074907180400900800d03c0d000c5050281d11002d0115645600c6070046d41e450b10707001000c00e40350529010840ea141c4c3c2c08401314140b801800d220000306820864095071080320901d1000c2958100301000903d1300701e298120640100e10305030b090000c01e079000b00740c913808840c900700120010107007002c2c43c1c0c038400039a012820040049804104104021000d0f060701c074030900001c051307802c6d1812444c00074841c480c009901580031031188190b41d0721921000c0e05000b0003500c0014080350060100c1d00f80c84040340e20000d490707141c1d40c072407c001102421941c0e115040701620060000c90280b009124441c0043c56060402e025100d50745000b5103104840300303140c0040103410440b051180c29061900112140c8036080f52030f420002d0703c00c0c41c0400105410b107505440ca1084401c0718029501c3c1c01507040180c0e080d541c899002c01107034404011210150140c2d07801543c0300c81c1003c100605035465504203002d8180140714021203600c000602c5600039520900882140d10f5400c0d280c40200b0362694090f1a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 182753812 1250 182752562 182752571
    0x807050f190230100b090106020312041e0b041a04020108070c1401060f06080a0606020c06030a020c010f06150e030706051b031909080109030c08030603030c1c020105060d0c03120e0301 81
    0x240c4800011340400030040e458030501ca820f82400070070014900910403080540c008200391003001c01107071036031584284a0007904043d403908103100550308000350070440300f144100c0280424042d08030108142c02a041e0041c249904e06940003d141201c058005400e000401c07507010204151245000d6120203d42c008000d0720b9a034034101c42c1c002d040d51080e03034049a09000851800003030307400303200c0c25200070340c0081a105801206200003584004e00e0003600541c24040105004801c3c014007082c2c003c0e164010034080e051070702c902d064256114199090101c141780030701e00380d100402d40108a13180d50a01d16110341e00404540c1030310500c50003170010f41c040003a40b4907581d6015030150b2100c4144d07036a0008010744a0040f5400c072050840d010380802e05400381880029500c50007142d1000d0090f069909100000d1381051030540b0f564200300b69414501040014079609120311380e400481202c0c2694401019255894025460b001c003410641c041422080b2180c06421079a403107100c003400801 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 182755062 1250 182753812 182753899
    0x15030a0e0a0b0411010503091510030618020406061d55210c09060306020405040509010203070c11010c0b07020a03020f0102091e030a0506040807050f1902 68
    0x20ba02048404441d410500a0014600d51040040d03e01c1040d071980141903850b4040b03840d1000510041c16104200b561844c0480001c01c5c074003400880050020090304030980c64030420055546c144c121000f00800c211941d0110303118150b1082800c06c040d614442088170301840c0009101d10b205189102c0d10291090b0450312881c0c9a185e080f140400031104441d81800707540d580c4500d20307407141c4a0240a0b24240070002400c100014001034440d406034004140d80d000c0b010181ca000340e005641584d8003040400a90625009469100c11b20400071440c52501c900060440c0c1c030209409040c0d0840d07410010120390203425482c030340c0750304071103200100d19003060000c1d541c8034100011001802607840c060030f130304414025203689000003403032a0841c0c48801d807503880403506110381562600c282c42c020004604188101ca00a500982643e07a640e4001d051047c58100d60302a00085648801c11039820a60ba50713408015090341240c1203080b840c00245200442e2950900c020740800d0001c4281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 182756312 1250 182755062 182755073
    0x40b0a150909050708041212051602010e0304060906210614040b01032f04030b0c09180105090402010e041e1a18060904031b030302040509090105040215030a0e0a 71
    0x42040301100d555a01d40349032200c1c280815a1010385500b804201342c0b002003000207122043c10b1030240d1207450f00b0114446d003600110700303507a81958400d1000d8440b241e03000007298280204000d42d009000118541498440c00410560350b42c0306101c20000700160510103407003a40a8000f00f4802e1200074805162103408908903108410009403140b440c00d0a0071070507501900980c9450b141d003640b00000220a00c0260300c1220101c020481c585034100030102c00030b14000c000078080c2d0b54649110b622010804240f103100440c0800d0161051005c200410032580d03030b4000154403a0313086c0b912400d1405c0400104020784107110f000100ea1010303141e5030781782200ca41d01c21542201e072055010900420310b4244800e445580800e0388a4400407800101103003880249141c01a02c0780c5030492031400740d40540039401200c044210002a00094200218a0b0180406821506d000c0082102d400c2c281d00107694140e0064089008040100000b81c032002c0651001100110000035110299200d1411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 182757562 1250 182756312 182756339
    0xb070309090b010c0b061012090c05090f0f15010c020303270d0521040e0c04030210030c1209020604050a060503010302090c07030813210302070308090118020906040b0a 74
    0x40040d030782c1ca402c210152a40c410412003a0440d00190700e4400c6840f00700034061400500350048040c4100340303000061420302445848215801b418800d03401e00d04000400c80030321000780443c80a0006481440380c20301003003401075001000710103151484510240141c03480704040c100139615000c041016119094030320228503107150f4403648c1c04107021110003000390f0280802c00142c11070380f21844c001c0ca21a4207900c0d11000085a00b0302d9400d250355141c1c0c0b0402c1a200300c4054020300b01c0030030100114202203150810036034460405111802d08480024a00d41c00481d0742c2c0b1080d610b4441010039900c074107089801500014207100b000f65220040508290320a104c00c0740100b0400d000524070840000966070301960594560b111500c80e0900b2851110552006a42200920544d2002101850b00320700c0307880000c8e00d01581b00c00480c01c0103000810700500800481c1d0418002425540783c1c040c404036010390403126900706407240390114009054000c581c5d500f080309090007044030001c4081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 182758812 1250 182757562 182757569
    0xe04050c0406060806041d190213060b1e0313080a1107060905031203040203030906030a02090301180515090c0d030203041701150b04030312020c0328110f0d030b0a0b070309 76
    0x302400403c019095a1440c0410502458401d03002a1840c101e0b807600307880038011980c002080110ac01c460380a44004403165a80a1230520741c0c0007800d606c051b03840310b0350b104007002c41c040c0380c0e41185081d804d0710810460300400245010f4001400c07041490141040000202d418406c03903901c1600d422020702502e03010b01940344284038a204609540c101d80c011207200d20790240c0510f0030b1400c0c50301072219035000540120b80c031030740138082d034020f60b2070900c5440c0724180b8807203006102e80c1c11414041d0400c2000015202c1c801040b50800500c1d0000103040074000300c05495a05080d80d840c04c0480c29801584c100328142e42064903e07082681c0150024805201d01c4000300500594502028901307202b0b510008011070080964201d54410540c05048869030b140b0540cdd151074609021032041205e1801700241c03043c3e64071414211941d003d541e42000303910110040464003d014079981e41c1e110300498850406441c2da00f221482c1d00c0da0a01c0c4801483c1008215484e40c0301881c0162000c400b500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 182760062 1250 182758812 182758819
    0x609030a140f0c060403110d1509030503070809060f010501052109030307260402041503080706060e090d1d030a0503030a050f160e121603050a0b011d010e04050c0406060806 76
    0x118400c1c6113070440c00c9900316a4407038140c64000d54418280000008100408c0d1182d0781407982c40e00781d24056002d04020381d0712035900c9664034648007402405014006c1c240ca082544801c0400c8905003002c41034906440c1d090a00c1c42e129003000f05140c1901015020300202c0c0e500c0b2005110b040c8900101840c003914450703c038201810054420794080e02459012a0310304180d950120f009400d295125040750411741d01e502c4103454480e12814410340c0640c0d0101e034110303640e20080002e16030300902d0341d80211091010b8008004045001800d440c213450342c00d8032032484040a120305a40801590701140da2020590340c8070f1800d4142c4c0301c0102800c48804844d076101c2e60024940e0f000020541d0300070300d40da8881d666801c2d61041400f03101c80c1c10684540ca244144013024203000c6c4600740b0800194480c4e001480c0401c1c8038505000c0ba1401a0301060110a80c2c17100001211001c030007050640e0515822880c8650750f50401a2400742100c403220f800515010011170031690100c40cd40c8194801d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 182761312 1250 182760062 182760073
    0x7050a0813230a0b1e01031b0b190207050603011415040305012c07060906050318070f05030c030d050301030206180618100c24020d0e0604020109230609030a140f 71
    0x103130941051201c00324100da09088170401400010340c07000002e4407408203010b0803040030b5201c50340000194090f104030b80d4420ae48074013046220382c1c100a42005010144c640341c1c00d55151644000c040c034030b0b14900d1031051010f00e41c2e445804000e107040d40c000f190058000d02030348041441031f00240e1103082c1c1c050039802caa2901180a0f10b00000c2e060102e80c05070b81e86c1107102d40b501000b241c0c02d400144c14403185611109520180e1082040b115000d840c2c501c0302410101e190400300b5140c4004485690300075003026160641464000c03040d0390440f501521116920440740100286111414183e5644450f01055001101c40c10319017a80d07a01d4416903500c0210141402d00b503035030000e5414001c0000c10888610100c0e031603404140603001c0c20000025050000d03070714420003502c0e10130080982039840355041206640e8010113a40040c100405d9005985c0c521591000c0820200340510f07000729400a160580d5440c1000300e000d00701e030041c5044804800ca15600754072448040e40c2c1d00b003c1e00c1030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 182762562 1250 182761312 182761321
    0x60d0f02090723031005090405100c050903070f080307111804030305150402120c0a1701030822030507120804090203090d0f0f020c04090c05090a0c030507050a0813230a0b 75
    0x9180132240520761801e0302e000820310303040c10480f03180e0b0300070411a00c0d805140791013102020540101c030b002031202d44030992180c017188245460018682c2c040501c91a04d9401004030310780c04801c0750030031900322180c82c448078603c2c030110700a080c0030b412045509039464200428550b0680c4203e00400601e061288200d070480c0400081e8080c0190003101c03040d200003c507103250302181c01004100740504040040500088040c6810f6900340d1050b6174403000003480c0c0c8906c4512445a0b0070710348202914404242c11a01d82c140c0d5090b041c0108208013422080c0b04007801a0b510580e801005060030541da04c3c5040c5603150380314035592103448003040b1079820b40110f16000d070340070b00b541501960040120448c04420080645500c803400d896941008001050540b9040704044c40381070000340126640c2400e09006044413001442e6608100d024080d11001982c800300c1a0342200103d5003070800341180d81012460803071b4191207a440c1e016001d64404424a012442400c402c1c0142c2d10034505655 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 182763812 1250 182762562 182762627
    0x50106150807031a040c020604050705041418011104080f0c0102070b070605060f0909150f07050304060f1b020120040e010e07210603020907020a0308060d0f020907 72
    0xa4100c010042000380c0c002401451080d0711188140646030074001c02c84803a0b0300400d080794030318809000143c01c80820030043c01020006c18000f0f09091b10100304451b0a10640c3d22aa800074010300301400d444481c1400c420306c03d402c03250507261034070142a521552281116a02e1100860144e03c2d8020001c0d49e000c250300124142e4125811103105074904031141c0e440c100184001054039510800d1030300c100f080f40e200c80e030400d485410791400400c810f8034841606452240b0050103416094138103002c002860b40c1c008252900140e02160200709107a01d410b51310007900b440340d060402d180a07400c00c0e01c41180e05400000900c00711201d144403036429128481e4070741c400e5008032955035081c1401003205004840c1e91316171107030440c5841071801180310000014015007500601a042d00d442060081d4a01003641d65006915800101100c6080e80c1e80580300c1d200c0101200e00c924200018074050061440391589143c0e4010458011450721039006000c035500d490401d5034900d5005012140c048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 182765062 1250 182763812 182763839
    0x40f1d0a0501080c040c030608191a0105010215130203150106090f03080417070e130201080106030507080708130b0f090609031c0b04060302040218030c040213120203070f0909050106 80
    0xf0303618000340c000c09032043d0a00014207940c09a5000f050b0361928000782c00b48080c4208032400c8507441503960350000e641400c0392214540040006501c5005004111030b80e00012540000b02000800c9549035031105c02580202e110307100f0107500350151050b400300ca0500d000c40103043c0c031b800d03842d6041225215609400312101c140001040b4540801003803000000481c50b0f0102c000e2b8017411125103e8a900c07081e818440c0580c4ca03400d0312541c0e000b07140119a0040290b0340900381a01c1c0c200151318200100600c0c20102820f080305201d003550100d0310038401d41248032030701c43e00701010301c00340d0070b190400750350625084078420074500803100420298034021007118034040c1602c000350210b41000b80590010804450040d42c042d54540c000001a1a6400a0325101c0b8040ca291440116a0802d240c280441e45440902c5075104010f2032a0444c40219054291880d00740c00140041c0d4610210345006081d410840c2103288419001502044540145090500c283c0081c0203043d0740e044000202c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 182766312 1250 182765062 182765069
    0x10060609030b1008070602070503100b060d0c02030c0f1c080f0412020a12020105040c090203060a03061a03060f070905060a0806042c2109010806060d02040f1d0a0501 73
    0x21000203081000c40e80c0400d200d504260101060000ba580d9030b10501c5c41c0c03041e03e606c40c0c005a040317a4010490752800340414000c0c2c0b0491002071104c030036881c0c00100d10b4494504c2030707010f4039a1621510302c030520800030b40d028041da180890368130302c0c504a50a951085071800b01070424406540f07a590380341c864481c2d01c0c041c1c83d150300c00401070380311030742d6090200d40c80000d0300d41148500340b100d2000c510410080351160300da50300009000c3c201800d0000c0703030840076040407580f02d0040050180130b031502c80313294046a4110a0010f0900c2244982041e608014140e01f50b0602c20300b400d000c03003044140c0141d40108150b0300d881c2140307070303944060040c50701a0341038803404038004100003a95800c00d070300407461500240007034590f41c3c00440c804100400102112610903400b003600e510b0030200c5000b4a0048000d52038505042c0044c0000013030454400412441c0100b4020441c1c0200540a80550300a802103042c002e41060b00c03104035002800e0881c001c0c0492a8a6030049070a030b100e03920615040e07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 182767562 1250 182766312 182766317
    0x402040302031905011e020403121d0d030e04052d0606070209180a030201020d0c170a02070317010b03040b06010c050d0e0307030c090e21030613020403081b100606 72
    0x30b041d507544580c000c1d26034110301601e055489641000c15606c008140035550840f4a0006031110308500345000c5242e034858842c01400000324411030311401c1130f040241d480310111407241c420405840c040300d482c4c45034002030b07800c6070500040c0101080300461911100c1d00d00b10804242080310032174a085001c3c295a01c64200c1d2080000741d01500709158050f50014046202070490300300666114074140d80c3c0402500140d41c0441c0c1040181b160f4000d450b0107541ca4986007400300198096642d50200c00b801b5131030040d03400601070041600440d07841c0b0403800e406414403002d40c0d40b000a02c146900c100c0e4100c5001020100155566000e054a00d0107035401034018200c4514000c800d03100c030301d86030703850652501c10b5001c0000020010003011024110300440404e2141c0e6201102d458040e680080c080309c200303a0910360344411124000d0700d40c1310f50103c400c915030301c40740d1010f0303030081c400c0e07420281110340009864071001d0000c44104c076500b6407040444040310b81441080d4211046400385400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 182768812 1250 182767562 182767573
    0xa0b0304110607242f2a01270b0a0f0b040903090e09031207030f020d0207051b040e0d03020304083702120a03021b1608060105040204030203 62
    0x820301c0d05039282602000603058a02e0301403941c49a40401002002c4070b00d4114405400000d014001c2c000e03161402201c2d1000706451510840044c1d15020401c0c03280c1d400b5401151410b10385049940081c050030040070701c4d018404440701124043c0801a003505c6041d40080c4000079880b50016951030103076003126010034952559032601020308070000039440041d40725040142c8650f558403440c00c15074825142c1c0411a4079042001c1d66086c0c0003071101c1501c0d0018003420a81001810100780d01076418640041d07004d140030383d80c2000780540d2460004607072001c5050317800c01000044c0710b0041c900010100d003403800c1d454100810b59200024014058001e410b80354450344c06500950f8100b032103101030b1410041d1103040006001c03070081065001c910840380f541e8020480d08036608584000744054081d076801c18203501560312030380c1c044c0300400d9030000c0c0c00350b41b82d00d06031130f040c1c0c05c00000029190040f882c0301c40c1e0512300c2101c1c09100464041c51000240900e030a200300c070100ca9000d8040d11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 182770062 1250 182768812 182768821
    0xb090a0516140f0d080d0204030b090c0303040501210603030504260304060c0f1a071b02010207050f0420090a05030606091b04030807080d0c0c030e060307050405091005010e0a0b03 79
    0x249141d21104a00d4110000c03000303c0c4c00142008006c2d0a044071607510042c1c48d54a94140000601005881072449070000328512103144c8007c81103505483c428281034250314902441d283d40c21002e0f05180c0c10081c9417100c04402c1603440344c0200100c2d07015901d03040390720415005056401c0f0b6810b2042c030039503000708801c0080c18080c9030070448060050308412080001c03504c03040160141010510351080300e41040100e40c9030007160240007800c02000f802d954081d1940040d50b51040742c0200c0f80301d0515000c45407100e503102c1d0409601c007031340c068581c80008200c40c00c4008640140d83e00a2203111a00d030f0102d003e00340000c007948070350300c001e00401040e142c840844030140c1c400b01e51650b0712001000003001180c000b0005200b0b052290781e81c2542ca1255202d031104a0b40d014200302c0c01c1008104a103000b2a40c0b0118a1044480481e652a41c0307807250b4009035500d12480d4084c503080b40168080040b0b8904039070242d001c98600381c865003140c4c007140041204d10803a03030060743d140010510204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 182771312 1250 182770062 182770069
    0x52505120f07061b1703012d0605030c0c0a0b0f0c0c0c04050601110d02101a010c03030b03071707090507030c0807110c090c09030d210e07030b090a051614 68
    0x256401d11a071908041c6040203911041c100121315200304141005c00801002070310040107500e816080380c5603803004010400413a0003818000303403146c2e104204011020510308804c0700e0448044034141802c030303800d08009140484810100710740c0c403040140d684000076104031400c8201d600000c61040a49414002642040000d0201410850401c41c1001c00e114075414200300302e00b600b040c203800402251461822400a8900100000000e1403000e110301d00166045203c10038491742c141400b1034049400c20200e0700c0c3c681160700c00e40240000c0108043d1465002c42d280c4e099895000c000d001550380d030f48055094a00d003811280010f403210000421041c0306070b10103d4082508000e840d100d07100e0700001030040721309a4001c0d00c034010014100c001071804010704e191800090503c80c5007106a0306502d401810381780010701c400d945031480740da1000340603c2002e02840e40094010303d1402c0c1515160b5450070201c1049859100d0300418041c3c030805100b04500320f60021951001105212050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 182772562 1250 182771312 182771327
    0xe0a0e1b04150b0c0303010e061516020d080f0702090f04020109030311010e011e0b0f0303160206040302090403020303040c06081909050c0409060c02070509060a090504052505120f0706 81
    0x40c0146902c00e024007103000021600106401581000150703203d50406c01c0000c407400b0003900ca00d104800040c9003d1032600c080c801d550140308c203075130301841518150021642c01c840c408002844000d00281c01c184102d410b102810744c56000f900c5042050391100341c40307503401005a1f40039010511421040000074490380d41c507803a0000c4600003088100c107050120342561011251040c442000a003084007400180c1f1440700d03c0c1c281100c402e074001d010300000c82d03103a108442140d001502c01c01c0042c001c2d901c4900440d00215405070a082d040d20382070500075141c5d0815202241c00054240300010300d0f920441c1614081c10340000210408581d9515003401003071455001c407900c0c0594100d420312a90740e8440c1846041c01414081103111703190000a0800c241600002d1040c41140c2c18401c994599544180a903400d041c03000905407640d0a18600e040c0c954510b603400c420301c10155070009140e905c0c803078046401c2914000e101142c105c10880e2500c2c2141d20820070b45e4840d120400c4064401d009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 182773812 1250 182772562 182772581
    0x1050d02060c100603050d0f05130e060a0e090106030209180c04091a040b0a1508030306040b03070807032103090506062e08180303060102070e06010e0603010e0a0e1b04 74
    0x1124101107800c00c405040d00d404e030f031003070b2100d401c003401590340550070562031001c10320286001d0740707080c48011010841c91075500404003100703440e4001a040d501c0d6402443d02401c00500154002d20b81031014a004e005180003c071300491050000c2142d45034031600c449070000b281070203040c0440701c035014000242060704040d41e00c0c00c80310481e0794400345640c171110300450003141c940c1d02c00d01c1c06243c0c0b40d0a0303500d8640d101200c242908410020b02ca408810f41b074000030300b120041100140440001d20b454070540040e00300d400b49400020400940111440c10f102200300300c4a902d298004090303080303e04002c000341c02a084075000441510703142264010fa03103040c004520242442d0940b4207480c03032554898001040024007032184c60480000c45000960000008500e18901880002c2d02c1e03485a1007009030f050340300004521140e01840340d83e903110314043c01c007980725a0354580300e210400c0151040c42040e03280c400d0460300210040781000d445099640041c0700f41c40c0385003d000007480e8504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 182775062 1250 182773812 182773837
    0xc1106040f050f011701030b0a1407120c081b0c100c090801140402150702130518060609041e0812070e0915150d0f02070506060108160915050702040e0304060e0901050d0206 76
    0xad10912221810030301134040d01c010b60b0340340c9941000c0c81a090031602ca172000801401818001c01c4010303107000801c450304041500c00140c6031203100324600c1c51721503510002d0b810300d400d09540540e0349d54060889070413680c042000b03102c03152038844100e075640001d4070003a4001812801c07020001c2d00c02d10043c400c0b588040e000b11072914481010300c04569050f40d1160004602c9406001c141d0340401007541c004c0402c81d10b40300941010b6580e14450282c0d40c1442408800101000e810b000610742510000201d82c0905a401d00e040381000b1701708c4034202c410b40d20a02d40c00c00490385290154000c22030111014114140012000745141a242c00c0180224016a200c48030b0102c148401c0c0050011b052040008012600304440090002d8a00900300320100e140c0c0030702114826404290382e4208c48460910404024504204840c548110031010750060300f020f4246c00c400e0b0000000304115000341d503582503100d6070082040010740080c4120b0b40e024100510400142c0780c03280040c00c1c2c103034010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 182776312 1250 182775062 182775071
    0x5040b06120408040501090803041508040503040f080601050a080c01020c0613050d150e0303040b070e010306030812070e01020307030905040e011e0c080f090d0c1106040f050f011701030b0a 83
    0xc0311481e4010100b11011030396090042030810803940c0107000d4601800594026504040c03c0c07602d00b110040c41e50b42d40008000c1c07688041800d002d000c0c002c4802411401c072070750605070f4955088a03a02c2c5028411309000c5c5555080004c1d010001207032224a90340140d0151885000e10303020440107405c80307c02c000203800140d0340051503945448100c04a80c0c440c24403903601848030340c102d0040300c04036084c1c44503980080007008005806821220707440142d904004181c080f00c0c1d4012801401e072604001c107860b50005580740100ca240c880d007849000140d0f1020b1001d03400780012a141e00441400402013640f1300c0043c41107152680080b0340101e0683d00002d503108500c00c200d807802c001c500500803072681ea5580f2906040e4040e400e194080303101c110b880d0301070400920213031743c480c000c114101c100400c0c260100c2c104407020f80d045a031040014000c0c3c0d04c848e101c6014003c40c4440384140c505c18401905100d400f03501942a80101884446046680d60320355110301e000f0020060492019a554 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 182777562 1250 182776312 182776327
    0x20d080402031018020f04051003030c0501090602031e060a06120e010e010c0521060a0b0306010207030204050a14010f06020a03050a0908030a050306011706100507020316090e071a0405040b06 84
    0xf5072050082441c0d901c0140c805510071401406110001041c0d180c0c0268100b50800810301c00351541002104d41c545040540901c141c10068010700b40c60100504207800001031001521003040d46080801c505081a03c207902c03a5010801c02c900c0c184030b0000451041118800080e5559200d640c0d0900c00400108204004642e01402c582c00110340303d021940c00b01d6003030b01e001d050300b4903014513120030400c1070030741e08000700060842c65141c422091b00343c030000002280740e4428050340005550180007842141850314400c40680010108130300c1c140c4c1414000207950070f196030070004030b80c501e8001c1c3c4403400c40d5880031111980002c100000780408030400040c0d8130320410081c19078610f56592a900e03030401c00001013030b4420a503020000940d80c0020b01c00c2c180d550301a280000748690501903580c0394181702080c01c01004043d44508800c00d000005074450b00c80d04180d00c0341294030301343c07102d0701c0e00c422400720038540c0d0f907100c42c0c0f1581c024801801241442e6201841509006001c4c6050034030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 182778812 1250 182777562 182777593
    0x2060403022e030b03060406090201020a0f0b0108010b150906210403031a01030207020a0512010605090a1b180e070509190911070b0a0213080703030825020d08040203 73
    0x3032030111002c662442c1106600000715420086400c1045403809200c442418000179545100c0078001809039552a20031908580c003c00010070255445004031b00181078a06003942d032034000740b007580c903203501b8000602c04c103141485101c480340030b90054681c24403410000380001a0040f004a108500da69040c002c1d4401d040380000b44541d100356000700380d2148400c102c202110280d80d0f15414503005000c2c0000696542e00b0f010b0070ba44055603040b042001200c10740340036060036071003030f500203520100344070100c0c9060b003000301107000c001440251a24a0340c803c4495020b8201e09810030802500c1c24000c40d004021140d41102003464240d080c400048000782200b0200c3d241c9030000f80c50ac0c001085484402c0c000c00200410499419040015a482e039a21000c1c00a000044540d4001385044070b040120307501501505804048540f031584919014012560540c6d01c0c0e002519400d02c1c000c041c4591440e441084100c0b6800b40c0030b40c1e01d0841081d0340c1c1c003c02500803a4140640c03200c1c2104001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 182780062 1250 182778812 182778829
    0x51902090904140c03030f071b06120c03021603021b0603100b03040305070803090604050601080705060f030901060b160611090a060e01020a0b090d110f031905070b13031d09060105070206040302 85
    0x58450f01a590081841c09c000c0c80440203450703174250070210008001c882d1700000d0300300c50002040b0000c2002440120120020710840d4900a1b21002d0b0002402c00c1c994000f441915041c0208044c1660860030002c105850004482c5800740494600f010302000203d80042d60300301d4070a080ca40d050040690702c0c0034854100302c900c2005c5038001c008000c01c0c07100c01c02045004204400190482e00e0422020032100c1c42071081c41c8070b14002c0040895a8074000750310170801062816800340c0c907001c0d81200881c40c000e13031071030030b03541903040007102c110032044081101e500c16401092000442d19080003560090314008103241940113103654031000c9070035004000d105107076942c0580b070305400550000d800b5202c0d1111903482ca5000c640138a1000d04000115200d5501280c001d030610101c0b548200c0300b034460070900404281c601030501640504400110b102c00c1c5c86500c640044400031400424000d40005085030300000c00c50100d00254000d400030311070705001521480c07800d91241c01182000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 182781312 1250 182780062 182780077
    0xa031514030d03050903030c0c071502060f10140108040203010207061a040614063709180e060a150e0c07021f0903081b010e01051902090904140c0303 66
    0x4440c0c1004503241c5018000b180d48101c00741020051030410a45403a40c07070100600c3c41001c014001901d046074002046035400070140200c4016040d80e200b08029150801900c0f036030a0344200402044a030295200c3d108282e514030425203003400314150044998080c003071310a82c1c06541c2040390202088441c091030752820b03070110000120074144030034003048850690000c00e081d42070b142d0110720b6507600b04c00c9070040c07001c65052415211035050403c0b140341400b10043c8c4070701200100200d440e500620101e080742e03004035810b48003030460701417a801d6510051001c03845070015000261411b410380d00201d20740402d82d1105100c2501c81c41c0320310b0040d2041d01e030b2540c101c102060301d000f14907000304040b0690440301d00440c900840b145010345190350078000100a40d0740480e9102d1414214100c0c0103000103403c00074481d060400c41100e0080109903106d55100d001c01402d00300350840c0b4001c840600c580544130341066a91920ba003861038032810300b401030b2030140c10720740062582c00704013400d400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 182782562 1250 182781312 182781329
    0x20706060e040807060515040f06081908070f05010e06090703051c05221e08061b0a0e060904090f0506010506040b0406110c0604060825090b1b1609061e03080a0315 72
    0x128145092f0038540b995a0040380c1842a92000640014020200391003920703030301240542d100304180c5405800b420300c14402041d50f00c10001009102c503c001400d200300d901480a441d1200f14021080400c4103089410001252003041011000d8070030800803640c80090b03880f42e100203034940028200018410800c031a04c426010390a001001c024450075801c5140d424803018620b03107540c91800c0c580941c2e440c0000740001d6124022640c2c4950b0119085032000420420042c1098903108002d0b5000c404103440520a4100100d16821b01034121003d03602c929001e181441e00d000780485041074041041074050003004aa0310701c070785442d005000074041d540c44104041c902501e03004031130810700d01e40f41380321141080b1045541c2c1c0c00c081800241e50b90700102554a1010400031042c1e003480503040036041c403c800030005441400c4269130103849035440c06016a5540b21704031448840341100d442c9a0400d4000c1c10400a2485030007000b901400c0e050101e0603c800013a5550b02e6484c1b42d200c000c030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 182783812 1250 182782562 182782571
    0x3060f0a06031e0213060c050c04050a0c0806010c11040b1915180f061b050a110f0904020f01050a180b04031a0907090e0c03070801020706060e040807060515040f 71
    0x1810800781e021001e040b0001001c5040080c10915200c4e42c101a1040c6e03414001c0b22058001400b20a00c12400403180292040c4114180051540000c0c00991260000a1081e0002c50b100750b20410380d849285130000ac0c41d440c83c81061041200500c041b088955000201c1800904002c00503800354004000c0751f1101c9013080103030440074211a40e04540c1412010f4071000078030180c034054501c18242e07400c1d4605188481003d80e011440d8501100c809807030f038801d8910804c10031840600c03880103028180c07554000c180f0441c0c03c1c0250a401610025800b081c1c0c929000a00e510130000351842d0746c2c0b40d20b02140443c3c03000e4214030b080b1140d41c004111a0800140510074444486400e12a6844002d5000c50310310b00112519128001030180407542c64652200c0d0080c03031420081000700940060035510340c0340c1e94240150003036000724011a42c040c1003032400583c1c0300001c0d43d03261145400402c2103260280c659190001060004d10340c12021050b4202c540e126166440345160b04000b4400004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 182785062 1250 182783812 182783831
    0x307020606030703150c0c1a060f060705330109060303230a0c2103060e0c070c0b03060a0312050903071707090207050102160b190204140603060f0a0603 67
    0xa0415100074200c600940c400d01e010000542000c0701c00d43c0c10100c040c0002076403000c40340100d80002d22501e01900d07070307619602c0e04078108603100c4807103004d031074100d0b64824080e40d06018008580100e400c05000c54000c090720040c9442c00410703050030445c25010030117a0100004500034002800e8002c1685a692541c00740f0805030008614558011000c00400660244054844007881114400000c0144900310b42c0704100843c0020213400a5103810740020307141407000100140f00501c254224035070b64401190b40300c2849011200b0468122004c0300645043c0300c3c0c4950140c0c8040c0880c1e0704030518040010209182c1c1500c0d41000b0007903642d40c0d42c0c07041c4d0a800c25103001c1d004e0b044104180140414915104c1e030000c7c0d41c0c4200c4000130b50240e2034402c141066402800350443d080055013404880d04100851302418a101c0d00c0c90321350041014491100c08000c80c003841c016114441c40c501800a202d00c0d1400196500020090a40b090001c0c400042000c07660658040340c0840d44440030038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 182786312 1250 182785062 182785067
    0xe010e010801020f0901110a0803190b0a121209180c0f020d02210708182e0507050a05010f05060109050d0507090c2c01030605011d0f06070510020307 66
    0x80c010440c1500950402d80e580601250b248560708840d4107110b030198840518260512010009a4102040744d03145d103800b01c28849043c084801051a4a1514a00000500d010115103050f070340030900f21080030740e8590324005010954141041030041141000602c071200901c2070901088007103011443c141c1c510070160102c10500e1429055400c52240510802d60001d140350500602a0311001511b40e5041003410034403030f101000d40704410008039003a0581c10340040b18220a400e0b10f00802c519192031090501c0c1c50404d000d404a0480300740740140b5140b103a4050b141d15401141641c04203011340e07a88600316003400c0ea05100c00d9403540d0030040151307040003881004000a803004005502d1559441e521002d83d4011380d4a083c2d80e651440d6140da2151210302c131440607031140c01144416015a4512040080040ca40000c2c1000c1d4003003400d500ca11101c0d04905001e02e41901d5a9250000308910403101c1c0340d15a4010f10f0601c00e080c0816810070440140c001d84100c0140d4030b05040e41e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 182787562 1250 182786312 182786339
    0x6021b07030302241e130507140307082802010e1f0e04020f07060c17100801110c031603050d1503050d09030f030e0406030c030b0703050f0919020409020a0e01 70
    0x40c1d40709056800c001c10320b04c0a00c111040405108080030061b07841c0d400d01520070605000c0030705280309a94010802c0350110010700520f4000300c0488134856961070341301d540c407650b14808401001304101059160b852005080d0801072050500e026200c410750b01091010800d100e44004007800e00103e00e04098201000c0340d6a180d003070b1010b5142112450b03d14075240b02c0d003d8024015951910801541c510503001240e10020340802d0003400e0500781c0d810b0400310707120300544415520b8030881500c49150481100c00c03500da0741e8003540c20080e203e0b0200c83c03d244c0030b080c00c2d82401000c1104400c20880342c40381d080e2403000c01d94915407150440c03c005103030420103942c2c801032280f286421300200d00c00301c55003004c1c55494034040c810310180d8004240501100da000420216116002004021070408414070460b0155010415640c48003500c030b1400b20300303a40c1c00d81950032004800701b440304003e004a83c3c203030000e4800308600e400d640c046040c50300c103684085003540742c80c0c0060100300b004049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 182788812 1250 182787562 182787613
    0x4020a030f05090c010c080906220602100501030c030f1401020406030204061707080f15030a060b030d0903020f060c0304050909010212090313090b0d060c110c01021906021b07030302 80
    0x1d1440244d150000382c1102c0c105072000d0144000803900104554524040b40c00e1200703014141c22460744c040000301103d00103070107110050f0245014400c2c41007030720712815048980019854880350f03d16202c040074200740318015500c0346120740641621941c01d00007000204015540140e585103003134001404035403031206950181c0f800318180500c01c1e034844031494001451171885001d60701d54000c6a413010241e00d0f0055014010300803190244519680290400c90060f012f540700140c020004558400150000940c04400304c6400c0881d0f06000020380b0702030807500100da2625850707a0020b1400c160441c0c414429039000a120580304900d1110b140d001940c4900550600d816803001c6c0c9511001ca000b00e0101703c2c0c1d076500031496a030302e80030001c60181d0042e00c10408080b11040040c805044000c100c070a510402d9100b088035440012581001034031040507440e104156540d540103503108004c403020005001c224919811400d20404009611a4009141c0010020b0f18003080b800c102c2c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 182790062 1250 182788812 182788831
    0x140f0108010e0a0b0a0e0702060f090604031205100801090b040606170d0c020109150e030607051e07050715090305070b0a05120a06180203011a13140f04020a030f05 72
    0x42050031070042c0c149400c0b0300e080c10046100c21460000c20051092030344070100082e0040300303102c030498001c1180784c090052901c0c50b10712950703242d11855940d01c00351780050009800c2440c80903400303480e511054000e1012a01c43c90b84c5982c1302c0d1b8040c01d499102d94180c036030702807c1040c4010008584030f45030040001001480403e01006105034071207102d00030100030b0180e880c0005045a11814840d80a401d010401a44005c2e8400005065208400034140030340300f0319002c6860b0902801c2078805050400c610b411240c2c01903001c1c00243d401c40711080307a440c41440c9000c10601100046004092100d40e2056041880d500702540b5150840d07100701c94a2008200103080260f000c0101d6003030250207a16101d186c0c84040d05080100741a500208110045492440c0780c48099001103048400b440400c03000740c052900ca0341d0f028890200703400ca51261111041040c800007000c26810752000a01401825030107401107000c0c1da00080c01c0030b0010b0b40d11151400b40380724a1003183c1d003100c04007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 182791312 1250 182790062 182790077
    0xd02010902010207141807031b030506210c031516080f0105060a02070807080309010314060d0f03140307030902010f230d0e03040e010e072c0f0a140f01 67
    0x1e40010b526010350f4020065400099048854a1b445400c001c104241c507101d20b007010ba14200b40010000c000c0d40c02d03206032a400c1120000010b5209000301c03406064020900074803080c0c030070000300c148158078404180034001c16a10880584d004e01440d4403103c00c0c285658110300d070450028508031007000f401028440a101841514070314a41320606441054541540d55107541000b645000c0455000003035611441402003a10940480941103c2000381ca050005241c0d07a1071072096102c4c100c80c5150061100c0c101c46003c203580c01040a42140241008170a10244803820380a1307620896a40340800d45418941c0c0440d64061035498440d1a546054220707400310a59142a0424181000e0b04809010400c480000820750000b80400c0e600022240d40c3c40d925502c03d841e0071824031a00780703d040070340001554940106488200702403481901d400a840443d03012090700000f21340c22750410386500110841c4e81711605488064a1680b0750841c03d00030b028208842811032074452410010107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 182792562 1250 182791312 182791331
    0x40212010507020d0c05011808040515030610050a050d0212100909020906040234110102030c21251e0b04020d05250501020c011e0e04020d0906020c0d0201 68
    0x7003606850303511181742a901d42c3e0b1942c28060301514131841034100001c41041034508028a0000401c03c8135400d540c81e8502c41c06007072003542c081c00121703a15500501c1d54620302e00028400c800908011400d420081d007020855440321007260050103914400b207210a050000c4010f1361111b0134001c0c80d1115051200050507804175442c140b020304401d008940100c0c4071984010394010a0754a10850390300c9060898080e410700c01000e11501d415139403042d0f0b0010030070180d44040111401c0c00060300040c1000814020000e0018a00c00f8520b0440c01d414010280c2c0c030f030ba69035190001425a50300d0162100c0341801e0403003800e00c0c0c0744105280034403101603940004209100c125841901240d86a04001107401d11a080c5044082a00b200b4180f2400111b4800002c1c0840f500380c42c030070703421254050980e200542d104241000d10208065150b03481b11811031180e00d00c40d0f00220041e02c0075003010900c00104054030590001218015004189040c0c00c1d10708000c803140c4404584020300c841d408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 182793812 1250 182792562 182792567
    0x70e04030c0b040c1208071112070303111c030e120406090e0c0c01110a09050102030720010c050106090f14010f0b031e0103030305010e16020316150203010905040212010507 76
    0x140d107000100b07000030b01d10004083c03011007a500ba0051801a0420303c0f190442d180580c000c2c1c3c1f110408070b480c460b82c1c0000c0c655a003032030710070482e4080d01d040090185030f0851300e003583d00700410000c201e142d00c18000070580d60300c0291050302155850f524046403034004007044c1c504041d040001c0204094060108101c42d070b9010010004075101102800b030692140320b0076190307138070504c0d1140002e9030900e4001000030581400601385016550390351007801e52920012601c1e8481c00002406020350389610303400c0750300400003010202d50305040c260404841e6a4032542943c42d158840d58400e940c401094005030303401e00501c2c81980729440d1242240d810040d00b9844400d0500a03040000b1002c00000e604400b4022440c0c50242c40c14400d010b59039580c41c0080c06040240100340101002c0c17004a0300048103800b042d03140b0526030b005035041c14807035000d03c1c07a11340000c402a5540c0b40f0207414840080c403a0710085029080d50f030004201ea14050040c0b107a0103029041c221856858a002c004e502030303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 182795062 1250 182793812 182793827
    0x90f0706030e070b0f04050a090608031b1e030c10050105030d1b0f080310060302160210140301180608120909060103060506030702010603020319022803080f0309070e0403 75
    0x5200e400d0014041e00d140707100c1c9160500c02d40040c9509900018000301c1e5802900180c0121002260b181c40059120480700c2c054800a102e42c40080e4010f001e4440c000498484200106040c02c0440700d00b80c40e14030300030f542540310b0384a445903500000340000e4241002d000c0307006010749549041c0f180307505d0480403c0d601c14507030540c00704010310502e520340113841d003940290b0420b40040c071035601c007010b50505150701d0344285d81140103044003000008100d406402541c0a04003102070840c03038454250207122840303e19210304010000c0380e602e00c80c001081c070702c0030314043d149210305032030260b8040c00d188044480c240c0081e621540120389d0110016034030811601209010740d060720058843c0401a00a040070750426907105201200b0042d01c035a0560010003120300841c2101c2150403040850007642d001d40401035000080c1c82100d840700001541c9081c0807844c1281104111607807900c3e0703440c1c02d030400d40343c5003c40a40001481640a400c00504000c1c1186500d414640d0030207070750152102c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 182796312 1250 182795062 182795069
    0x20a050a020d0303021306050a031503030e0d080d0207080910090503100c0c0f03030c2705040b06070f0b0403080606030f010501031d01110405040f0204030f0f1e0803010905090f07 79
    0x4092061140b800c051082e0196081d904a05014450702c40d2101e60141c59038109003000c41c0040e24049c0b031000c20381000d8000e0802c41c1e80680b01d070310386501500d090241082400e01d007621480c00030001110031044a20043c408140a140d1964540c032071582084148200414102d00f0040301d001e0038032860703074042401400c08041d01000540000c80d48000ea0b000700b0329000c06007400f502c1000800515170141c10080c1c44d00c4141d0784450052a000b07202c4c0c2d45041002c90060207603e2070100034082802e041c0e02001000c1303001401982040c20558403c8039a80a101044898a900c041804100341d00502c420703400400455543c0d0551401e00c04120307200700c0510a9070304064454824000c180e03031141d40a002605194000d1152114072100c68016500501c10140550315000e400c01d0001007610036038007600d81c8410f0250b04420704d81ca92140d40124040145c80c11031481c0602c40c0d94000614500103506c3c07090007610388039032600ca5250121040100846466008000c014019081c00f04c0d5200a0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 182797562 1250 182796312 182796319
    0x180e030f1204051c11011b05090f03030706060b040302010f0503070518061c150b040806040219080303071205060111060103080a090b0408030702150a0c0f02060c03190906020a050a02 80
    0x140d502c90500c207281141c9a02203180480c800d040e413542e0103038000d51130444a00044001d100204a092044400b01c443e0400e040028900f0b00014000b86003d005894011800070101c82c10421b1079102ca804451043d44581d04826001800300110b50300b00305001e40424060605071704500d042070f0041d1551250000402115405c0700200d0b800d0342d600016541c4d0242c06038609500e4426101e5154001c007041104c0741075400b120600064031200000c101e8080e42d0544000d40420b031038943c00e102c011051484083c041011000307000c1020f00c02003000d548142400d64940402120541140080b80c03c05480d0904100030404100844640041c05504403507020104a55a441001040329001d00c1a0090082c903c00014001208180007002d06046402202c0c044a880c400209150f07881c810210a04045141031600074003007a4a00b603e410302030300142105150040c507242003800d55001d548030070001c8030100400240e10741e200003840003800c0a4001400c41c01d02a071a05541c6440c0000d00911 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 182798812 1250 182797562 182797597
    0x1c020114040f06200c0d0908071a0d23070f03180311010e030d0b03070906060f05130b04090f1d0703020f040902090108031207090e01090903031104180e030f 69
    0x41031a640341c50700300d100c40340c80c130039944071088894042e40f9000585402d00010f588000040360055001c2200d5007110b03440b00f040e40c000080e81c2e4a5140c01d4103c041d181815640d02c201150f071034005521510419405982d0710203007480c00c414060306032070409051108261802010805940f450914000500e40504082c4440304401d001640503190302c42416080f0300012640004000480d040a07107403040450075114002e0b154001e40f0100e81035481841c0000c0d4040b07507103484075400b41e0024206c804188043c03010a90300e4410150382070b80aa8490403259a8401119064210134480d5908034400001c000d4485902c4010680d80d903415804040c1c451110001e80f501195501d510103031400360f001d052204950b87d195070840d2690020303c042300006108800182565224103e0203094682040144940e40d00b880c21401c020111404120280b40d40d4103007910040440c507000e1700041c01c41024000c0103410104803603050300e00d00d05d0010b806a00c103002407142d01702840140e23842c510b0288507100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 182800062 1250 182798812 182798831
    0x206060a0e040c0b160b060415061d042c070501050906130503010905010212100e041113050c0901090509040f111306080c040c210e0c031c020114040f06 67
    0x42c0d840f84154050903003048005082e0048911128600039801d000352000044c0742e8513441030205503000c40f50001d40055071101c090011a004041310710002c581090f00c1008402c08402080845030018108216411041c0c14402c6c21014410341340311004003407000e040c0a80c80d05001034018002c050300c40f0701c12040400e0745660340501c08071060040c04020f009006641450905130f00030f40c020481c0b030302c3c0f41804c100000e18611401c0814000c4030040180c04015940ba5142c84e600b84080b50b05550740450307040000c0003100d5160140030300904014601940e1001d6030740001d013000750349070720243c000c580c19000c000c00b04603000740d4a407511383c02004050540c0b5a480000f10300c111105054445689081000311ba0403500058902400c1c400b5a0101704034804000e0a54540b01402c099440035200d2112010341640075404c410941c0148604846042d4503850009041082580a0702d0500b007480b114031903044d6090141c0a02210014a80e9841d8181030b00e80c8089420b541e00c010f03001c561504800d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 182801312 1250 182800062 182800073
    0xf06130308030a020f040e040302010612080405060d020720010905030a0302061314030409060504050f0c0a0e12010c02030717040605070f021c0b040b0a050c0a2003040303050403050d0206060a0e04 86
    0x1720203014100f816103076100d0711020500040101950150300542c03070048089034103604c601d04400c0c0f0b550080d2005081c0703803034101040602c0c1e00a042405685409200400002c5d40c3c801c10000341001a400d070451a1100c82e000500b010b2050380001c1c880d51020704100c01003500401e41940080d40d002c00150f44021604004801e10807a600099551000103000500649140e1105040d5441203800b489a51550090a0f0907030a0546450701c503010704215400016010740101124500003500540c1200c5600040c0307421244025140c00240c0c100042d2002049125882c400131000c0204181c2d04050811000038060f0181100c01032011614281d91010741d0303a070350000b408405504200003002e04044c60410300000c1e082d03c040713440e02c10803008100015142e0268500ca500c1c6006841c0c00c00c51282d0007103800c40c507001e51440c3c1c41002c0e6491201d9a41040c4003c0c030145003c3d4030b81a95036465071030428580075848c8808802c64002c1e005003c455a00c210840b030880c1c03034141180140c5d49883c2000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 182802562 1250 182801312 182801317
    0xc09190e010b030a0506150f0706060b0f0d0b03071202060d0207060f1a030a0201120f0e01020c010e0d110706030f020d0e0106090e15420f06130308030a02 68
    0x90003980c00804000118511000000c41c8540207503407045c0940c0e1608803d02078110b0360100c2c0100560310078054800c410323220002401819000b100b020600980d640c0541c8032079400a2a806035980c070001f28505940001d000d4442e0209064000305042c5203000039824803492010300080c464480080d40c40b00054003501500c03681a00407030204422503a0b280340700c0040600a40221850b0300c01c100d103102c01c3c81e000c120002d0160301a12842d5580081d10f50704070003018650041c61000342e4540130300380074405c244090800c2c0101c4000006091700524070f102d1030f0003034500d000c4040202c20980e503d0070321004034204007221414103001c40c0d00704940d00c501010303029500800c20200d01d450400c0320110300542044084400f01d280401c4102c248803030040d107449110f1880d801e80a141c01c04034040c40b130400045001c554920440c0c1900140144403189419101c61094030048940c0c0b00b001058640340d210700c040300c4030403181a40303010f1034802240b001603601e110140c8500b2003c80040c0d070701c0050f42c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 182803812 1250 182802562 182802569
    0xb12040f050f161512050a0207200108180307020f1f09050103060f120f0809060310090c081e0403140c0703050c0901050a0e0703091a15090c0919 64
    0x81d950b08030b0b211054655240f038842c408046001c03000d10f002030704034451600540f044585031785a0000401002ca854003400700900503001142e800c00000c808107540f03182d00c250715100790681c003e405c2a124001800e40e0009070454414180c2c02280141c0703d0f80020032940e041d0350540781c0098070403001001548201c14003501e21420300307200c468241c0705075022010a00380c0384d00740c81c00c016150701d030340414601100d6405100042034103110322101003001d51025422407403040629519080f10305011420581003603030313191a0754200382000e202040980c0100c00c80c1c92054a48001c141c5056900da450000002107160350241c3d641d00450180348c07044581001c455140b00c0c2c002c0d42d43c2c4481007a03ea4480c0c4038401543d040c0100510411140b0740035070894121503009069034910b0b0b051011603034003407074064510300605030782d4000708000442c1e0308052070075403005170300022a6103071041e01440c0175005205058407445401c001c11600304241801c0d219454020f8541e0310342045030101150183c91030b0b80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 182805062 1250 182803812 182803823
    0x602060115180306020a020d03020406020c0607060603050d08070306050f0a09090c05040507210902031c091a04060e150324040509011b0e060304120507021305010801060f0b12040f 79
    0x102e0200521900360010100892203600325000b26058520443c22400740f13005241c01a080220b0409179898980040c0100500800700003031125525a1003604e002886c1881102044102080220b140d0301886a2001000140ea040b4036100400d00055000d00c0240286107805a075190380300207110607141500c01410010784100501d003083e00015042403080c0161000d141d850300f4860301218800d01a240c120380d030140041c02210581000344c1c0160a07000600d17020410680c40009130300003d91210070980e041c101c02c50f551a070030040c0061050a1a0149501070901d45400d4000c001946080300e41c48041480248440c0001c40c51814211410840c540c0d8020f0a04040c0500d100066001c4500810807403640c40072410164801d03a01039515002196008100f480000c02050317900c0b8040042101d14a021442d210480d0300041a0031007030ba5400c5080c1d1350b80c2c0c00500c9080e200340305001c05085403c110b811203500e04000b07443e09100d50301d40e1159031113a1002003820001c00c0310900314500e5001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 182806312 1250 182805062 182805107
    0x6180d110a090603081b0a0606060c0201140306010806240d050f1308030601030c030905030d050907080118110d080c030702040507050702030a0b04140d0e03010e070602060115 77
    0x14140800300403030214110744190a803100024582010348500411264801095424a80e000c12111000480c010031094075008400724000003941c02e108a4011b000a503e640f103483d00070740001401e94242c4e405098011a04209000d16a07810130380450b40102c00b107808000e00b4405a1140000c0503603800070480301240411040702125441e00118400c0301d141c2450700a680d038140150070607201105020700350300810404541154401e400540c000c00031400d0104200718141c1c0c0c0c851079980981e54154500340e4a0003071115000c0c080c0000300c01002a000207024070850380301d40a410001501d0000c00c071004036040881240ca503010b0549655400c211040d4481c500c04000c141c03642e10481007284a24500300015074590f000358281c4070129000b800a1420300b01655a41c000084081c20030b440300c0420300510410524104040e10f080c000f1651010103010300700c000d0500f915500011112660080c20043c0034480c0e000850344d0454225039070911001410041c140c1360101c841d01e07198001d4080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 182807562 1250 182806312 182806339
    0x103022101060b0c061f2304021308010903020708010509070905091501230301021809041a07030f0e0303010b1e0f040609140f090a0906021b0601032f0618 68
    0x310343c40344224a88842030a000002c680043c030350303505900800083c1013881c03000c41d003d001c1074042c2513a03400c13000d80010300d0070000b060741071030f1b1030001d4bc80102c1e542c1d12004c52504040c1e0501c02c050050094800074001c2d414015545034558074140603003482c50b079680c40012001c0d40100715954002914003a01152075860b401042c3c0e0002c09100202200c000b550a4882c003410305100315a03000245851401c0603003030308403c200595102510030707140c010301207404c2d11204a184070184d008030f0b42a1000510383c04029041400c1d03801010024190750030900040101e2081d010031904140710340129440780c14a0304142c48007074040c107420320500020104010407019002207040080c1d0300b5450135103603901c00c00c000f049101d0031100c220702c0c0c2101b2400042413425074583c002d2404184212000b40c2403400032982d44c8007004251107980e03403551250004000340501342120798080e6880d49105495000c40070380c0c40c00303030301903e90140d4090b82d00007a2000581c400d103440c2d8590200021714242c91600c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 182808812 1250 182807562 182807587
    0xd0605041a03120a0906050901020a02091f050a030206070f0311060a02030103031101020306101b02150904060b0307051206061b010614060c19060b03060703020d0c0302030103022101060b 82
    0x101c20004074064030800c003d020501c480001550150000c0d642c400141e10304100046420b90490714002e070640c89100d034040c00580e103046119205005c41058072411788440310035031400c4180350744000c1c000c2c1035080043c800342c2c6800c011104400e4121080840710500f61400300c0c0e0700c01c03031461103401034001d550034802010741c2a0000c604a90090303541c03e5180d181110075a08030303c410354400c1d81c014880000c0540302801000f0080403000ea02c440c2e54401c800a80105091311002c0f02e6881034107100190301d81403403801348150009881d10087c0346086160041001d800c911075200541c01032403003a0002121607032520212817031402c400031a44404281d005540d8041d060a015892008041d07100c10345580c2008801c0d00d204401c1680203280400c0000e03051271011740303045819261541c45401c030f0070540c1c404010440c09210103982c0145d03100e60405c2c40c20304403891401c3c00010140100010400341c0e03070708010b058410601e5075086060003102e085460050502d64014030354243c020444419004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 182810062 1250 182808812 182808851
    0xc0303020c030115050d17040503030f12011505030408070809130504061a010f030b13091401051e04121206060f020c04090302030f0304080c010929010f06050d060504 73
    0x40c070603402482400c43d0000041d00194440c0600c682040052400720045100c100610b10500981801d0b5440c00c0e80790300100b81950b2120b652401e103902c0000c0c070500c0c800200e2807858014560142c5a66000300c1070700300200315100140c40a48045404111001403010f4802100c0c0b01da403004044401300c0201c2d070100009040c049030150b66a138070f442c443c403410511840007050b02140c1651104550f602081d07060300184804440d072a00032582c8078000d1010b86d5130740300f03540d07050f4090341c0d00b0302d443c400b0f11119500b03484006055561251600c1054101410b0707130640b0540290707000c0303541c1d8101035100c0021039007400b2400510902d507050500005100c0c2c3c008a1000030600e042d401d403401803914005003c103a072510400100168420440480724042003c0610b4103e84200200340c50701003a6941039003950000c0310141c031003c1465041d80340d2030b2201d6804c0f444411201c242c82a05614080c1d4007031101c241c501c190818030400180d46414514240d00040140c030000f4810041480811442030719103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 182811312 1250 182810062 182810083
    0xa26070b0a271815030210110a0f0308040b070e0d080313020915010e150d0b221401050f0d030e0103111204110102070f0302011419030905120405011d0d0c030302 71
    0x42d03140c002d500803002c44c00c4c80b0310b509503a00030b44100424440240220b640c03010014920310103001d050840c5c000240c40100b4412054069602c0c4006800e00e800d0684105401501c0102405900d664a24040c0c8a024600c850550030190003a141e503110401c034020001c1c02e1500079848460b1400700600c0720301042c1c1074140030078280da42c141c0d9400c050f001c0c00b107031400901d0783d200e08103814006c00107038071071941105c807030782c01c0181c5240000d9000d52030700d034032103203201881049907074646105103c0c59051013981c41c01071600300d8590325a0310761400884d0130f0560074040602040b035580a5414940d00940000c100c2260403000d02d940c80074000e4410942d2401503c0440b002903040b0003d000542c4005001020344503030314100c0c402107103980d0041d03820784510039440d001d43d0001d2000c05241c100f00c45a0b080340440316140420741c0315813482c0030350070190010004040354a0500c020701050743e02407440c010ac1d84427800111181846500000c04030240300700018100c032261540030003019408250760181 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 182812562 1250 182811312 182811359
    0x1d1306030501051b0910051c0609050705030c07030e0a05060705060a061406180d02040207060b032a040f0603020306010305031b0601030f03030c0e0a26070b0a27 71
    0x2030307072200c8158014204d403000302e2400360031060101400c2440c106003854403481032810041d20340191001e40c0308988140c2031200103500d554080420403246e40740a1550f011711289069482c41c50300b140c5881c114042c43c01e0150030043e00e00f01c5008103803070b00e450440280c0801444161250418a40f80d950340000b01d8146240c14249000010f03072081640b40c1c450304804c01880340e4245960048101031070705512040340d034032003035002c4c100000d07841e20703c003c2c610103010740300100d03810002800303243c079184050072107402400141d1001c02c800c0c00005598012648100d4022030b00407072211240c0003800c91a0002f07545409101e0000042150020080c030f6440013003102c1010040307000d070760903880790720911000c9e20444580d9080300001b8880d9000d86101c8009090120925040c1c0c004603060a40342c2d00003c0b01c0403110203a6400068055035070400da092010018007c1c2d07804c00803204e0160280c00c1c1c0d070b6001c0c07094038040c052281c2c0b181d60064400044486000421503621b92481c00c007c01c081c0c44800320b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 182813812 1250 182812562 182812571
    0xa0903030b030c0d02010c050a0219290307030b01230c16030302060c030601200f1009020d0209250201060501030605030a050d120e030409020304020f01021603031d1306030501 77
    0x41d9810b0100d002c2c20014002003045500701c003130740c0064804141203181181d9500500c241d2134010b80c2d4105161000542e594502d8586609005074400009441000090300d403030001c0c18072505081d04812250712002c2807501160000c100360059901002d2001040700803843c0e4100070071004e1444000d8410b01200310101ca400343c0c6412503400c400c2d41c17217000280042c0c008034000b4a0905070900110703003002043c9441d002e406a030308030440040841e41049505074000551440b00c0010810080c1480381440300308100c06105680051250302154070000e02900d04080010100b19042103a06880c004400481c10f03400e00004000b8001e141c01e004143c0440d10b840c102045900380029650301e21580720b03000b031940c042452001e0350b040d0403015000e10a29121007002c00044405d10140c0700404040307d02580782c1c14948100024550380e1a041811075221840c41d210300740480942408690305824020f4240040090401202148400072500000b40446074050302d200d1354007142c101ca016000801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 182815062 1250 182813812 182813831
    0x60e011e1a060a02060406020a090b0d05160914040c0201111303022d01081015020309040e01020c15040807021008040c09200d0b03061014010503040f0f050708060a090303 75
    0x801c0c0500f482e00b030010b034031800020340081c0c2a40e00070b1101d1440d9091100541c1d94a504c1c030400c40e0310100320640156251014003d110044500c121101d003218144048102e0400d100d0314030712241180d8003803180d911844c402554600030750054040101c4d5040c507542d2017140508035522919103202c101e02940a070044260322a840d030410700c5031905a2400048030f81d95070401199401000360030241180c013410400642e800070441c9580a6849503005961210f0030300042100b241c00311012150164010400000d074160040790400c0e40082c00a000059501d55051207009402a100020341001c41c40341c080c0004c0d9004024039100c0c51282c00e201c2c0101ea102c006140a540222a10702281d160900324662230f4103070764000d0040c41e508100002078446000340068a030200c1915815951f560720072080c041c6002c0001202c0500e6801e0900c14036504195840b11401700c02e81c14003818840301103e20404000c0309000c240b0040c1168802c45160741400e0034444000c00320381b07508801280c80c0c941c590 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 182816312 1250 182815062 182815069
    0x20c07080d0806180403120e070905010b041419080709020405040f1a06070201030e150601110c06030402090a0e0a03050a020d080c040e0c04120305040302040f18060e011e1a 76
    0x492207008094034900c00340810f1301c18807000c1d40000c2c00850a11550b1001011802040e00c248845104190002d0207103a10b060544e42c116203068010303e41d030400400050100d26020341c40b0400e00d00d400c5d1903294068031000075188125100d500491181e004421000484020359006401600c0c41107800704051402c03014110222a1151044000a01c00005400c4a0310300480a004031074010b04000c52003c00038140d07181841940c80642606c0d00b8440305000080d64881e0000c08038100e540020003210180200082d0180001003000f031140300c0810005004144a4210300892040d0304103d51042c034251902600681101c0c10b064014400c00c000c41d60094850703029240100c2228a0140c581030611850111081c001401c55509440400c030016442159840c011180c0b030099851a40301d500b140704005c244ca04411004d038990381006140d024420748529005500341d449070001400030b07840580d00d1701502c0c90a06a00700c4000c011107450503c900b0350484203600f15428006190240b0f0b02040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 182817562 1250 182816312 182816327
    0x91c11031c0c1d060d0b0301022116090e06011e27031a130c0303080105030625200a0b15100f0e0a05150a09080f0c061c020c07080d 58
    0x14030040e02583c5901d00641c00c00c08001c15421404440c08554039443e64042401c1e64080e81028050740d103145511f2b0502402c2100058010a090b01c0300074584000c034030024444550390240e0419220180d01045182c1e004260721159a11500c501c4603040844000280103001c1040c4071510305065050a4922001c091101a054070750104484d028032162941400e500c0d038009200f64a001c420700c1014000c01d80c1582a00000c611070fa8032400f00750304020500d802e1550185ca120208004009110140d42d01d0380350002c0c8884451800d600185a103144100541b1407410078180240140c820a00501c0340150080f4400c40c0a0182e11344041c1c42c4030148140000a82807000000b030500444a0200703108404012030040001c101307521068441000514100300c0304a1710070404030026505000e55045001400207001103400362050b42d103080034154413600c0381c0d102184030702c03800900c2c00403003580d290340d652003030095000441d00c07490f07a80e105650752641e40c0211801c42c86080c000441140c429500d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 182818812 1250 182817562 182817587
    0x7030c081606050913050c07020301050124020613030507230f0f120a0c0f060f0e060708060a060f021e0a140304060923090403090f0608091c11031c0c 66
    0x307140e00c5c044480c10300c50700070180035000b8500303000304000700005070350300b40510340c00303000e40600b40114100010400c1c00241c24074075940046d500301c0070411540d04081182c00c110b458246c2040c40c9c0e00c0a0390b00d085410002442601e8190501000e04075629101c00100320140c1c00d14101102c001550f022402e95960528803080703881b44030100111f6840c01d10414044136064460b01503414042555079454068034190080340254a45d2a080804d211340300b0400907810003850704048400b4101000443e11f030101c0d5001d0a400e1245d08007561040307510070032000070300e6480b42d5214410b141d41464000d13150f2200135801c0d50118802c11110710501408412202107401c44e4488800f42854400c04102440020752400107580e500c1d0009102501c0b00c0d85490310407403107580c0e03078941c042c10043c00500412450b0801e004010780c0900300803203e2400100315285a054100400d07212034182c60855003c00c0c8820f014105010100c0c000d41d409080d41010014840034403424030076801d035010304640c91a103001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 182820062 1250 182818812 182818819
    0x50a08030f0405150f030a02070c0504090b0601030203070c05011d010c050a0503010302040b010302040503010203041a1501051c0e07060507060c0c050309040b01120216021e010801090c0207030c0816060509 90
    0x20000d514001c0098030020721380c1d0411034240003a00c8010440303600103c410042e8039800003031050802124810543c0540300448040014507040d498400c9002802414075051586c0040400c1d0890f004a4000150540c408000d0010030070300c01804880b050080c010044641c00c044040b0b00e02c5006009540203140300d6035415041d80c0c41c0d030f001c00015041e2a880075060590800000c1030070344080c001075200321b000710f410702001002e60042003180100100303002c1025521448131912a031f44413044030300526408100c001c080d42c454a4040040950503d1442c040c480c2072000030701113070010081c280550080c2820420100555002d072184641302c0d10040440d00104401041031526034040900c100c410f01d48240744110f10381c4450104d910a8402d00f400034400098841140307032425240b440c001c40c080c0d42c201c00c1900b40c00041c01d681418040e2000d034a0710b404182c401c45100b00000340c02541c00810264010303648002e0151900b1500da5403046003441e400c4c010642c14051400c451840c0400b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 182821312 1250 182820062 182820067
    0x11060609040209040f0602190c0507090501120209060402040b0a0807030507020d0c02060c0c06040b1201090b400605040e0a0305030a0e03040f03060e060f090c01121d07050a08030f 79
    0x9903251171040c40c24000c2181c105a084c440c40c960000710440c0c000c00c00380b00c0d03141c86140000900f030141c81e0411a070300c031181c814105001400401c00105400e082e0381d070306841078880e6841e4040018040d0055410207a000407003c2103565210381d001c0300701805210f464070200074940741d6a000303e8440c18800301a0001c0390790146c0c001c0044c03c0c03500c01050403481c107078144c58009506100040f100e900c183c0c0980c0760f43c0e9000c140c3d00d00d136000d582019401050300c070308104032041509e40410850410b006101454034000188820140c43c2c40e4104462250041c101c24512440082c00c90002c1c0041d0060a003e14544401030109171000240200001e8150301c401e400c642d0380380f40c10b40c0039202c103903c69980e5010a01000031820b110315500070140d8480c0701c020a6464011444030714201000384040540c0c184c101c280400e0b44004200040220020b03e806400c0200c1e00b13401e80054a481c20744040844008503242d503410501055070015150211000c4100c1c0c2d54841c05a0340d03e00490400c0740992408 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 182822562 1250 182821312 182821321
    0x1e0305041a07080c3610020105250203040f03080403141f02130b030f0403021507211409010f0501050636090103060b010e0604060203030703150b0a11060609040209 72
    0x3c4601400a802c06030050845c0121685103111014145182c5c207030101c4800d583d10440e40c5480c42d80c4445184052000300494500350860703050700001160310782803071000403403c2001d0604c02c8c42118043c0420290b1824032039941d00c1c0c6410158481e120954600c156200c102d40c00d0300001c103120030b044248a0340800d03990004107004000307501c503c401400f0f5070081140020121103036030203588503007540f40c020202071605040203418259045204548a0703450f40c10440d5103500201d20380c84011a4000601940703401102c88402446100f9444442c4040102082400c5105401c0111310b03482c5200240a03036640d65003030111500800c1d142868031451007124240f46000e01d00801405007030175000043d40b035581804101003401c203800c1550060344415501c2c11a58200900542143c0c0a540b20303072406190100003500c0f408054040760405440b015940c0000d00b11490b858040e203d4180c04039621442444040c0c10a0903000b040c1380e0034055807000074028649000128842c5802425020f11030b640e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 182823812 1250 182822562 182822581
    0x120a020c13020d140a05070c15020c011514181003080918090a060b06040e0a0b1201020406050a03050c0906250507140f0a0819031e0305041a0708 64
    0x411016024260b007440406000312060290340000c1442c00d56900c0c841c10455070b1603090315001024201403103140e400f80c000144440040b0300d0f9201c042c80340140c0312500c0b49d2030315024110820300940c40c4c0c82c0418012400340300c01d54802e01080c2c0100c0d021035107803070a400403826241049a1051800c00300f00d10400220312448020010020000c207847c02c0e01401d1040e0700044035050f04d0004290f4030841e200800c10001d4422030f42d41000840f07019041c0351500c815003684400c014101d00307c0da0f4452008880d00c0c1c40c0d540d00044109640002035458a4403000020856004100031000117820180424031070302000084401c3e003070000c0c0115107800c601210341c040303a015a00c1031a8206580c801d613140416000c0c0070480280c1002c00440c055007001004000c0d9290f10410560308c42c158006042180c400c0000301110100c0b90038010440116250600380c030141d040055643c1c144008500c0002c403168035a0045c1e01c114402c064103004c542e00e1f811181188101100d600d00400d150301e022411440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 182825062 1250 182823812 182823829
    0x3050c04151b03110631020d0c031b0905041e05070e010b040303080114030a061a06040e0a06150c0b1b07030207050301050c12010b0304020604030c1205120a020c 71
    0xc025041489003030074403000d400400e407007030b0b031054001030080407034a20515414000990007034a0b0250f545d144c1103c1c9000c0e4009174252486a204641e040314014046494959903030341c3c1160454088064503540c0d0a0081e41500462704440c0c003400c8050300401e5000c1140b1605000d030390032100c0e9664402050080548903107084800b520300d4414a2400180e65061a8aa6010340b1440c11010b484515619010b4296081a0001200c4260f101611000b6481c0050700390b46454000c0e4010442850051a40180440e6080815044080041c000c5990b040c3d6510950240c88100d80070400c00369540103040a5104010068001901055043d8040340e07142c600c040d0051401c841c00242405100c500181075070010034200c0158003c1c1904100307074502842500d510040c0114113504d40310840c81c5503803800c0414080d05c000c40d00d000c400f280035501c80c1000c0d6030203154004615081c03103444500060340001980c8003110180714410105400311a000d00380e07441d6407050340040160383c00300030070482100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 182826312 1250 182825062 182825099
    0xc05040e0a02090a08030702030733030f090b0619030f060b01020c040608100606080603030421021206040c0807060e102c010e0a0317030c073003050c04 67
    0x40d4083c010341c503481e6104411080104001001543e8400c02c51050504021041e80180c801101d03001240c21030501100300f5030184003125a0307142d140303448220141d00410115407044081850400b0311020070000c169100c3c011541100c0c0700f0140d108012940c0000e10b114040141801301e41007a40700050711a0308005036150050041c1e50010803842c020408803551584000000c2d8409070522484840340d10581000e000245818181340c9000e03030100e5941d2140d80710b0941020350700c0040358140c80c650105030000d0f1384d000300301141126201998542e110025101a1201364001c45c0004180c000098698201c17061921040480c2e2010700400106a141a8442e0309100c0b42c00001c1d40b20382d42011902800c50075400c0352001ca40c90b00c100062a00c4406d01885008800020080c0f0119501119111003800e01000b507075642d5582e41160320740703806500e20061140031406071000c1180126114000551110591041250b003074200c110156002552030491043e02000107100d1102d036640d03002e081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 182827562 1250 182826312 182826331
    0x9210a020f100203160207030512070606090e03070506220212030c120417010b0604050910030803070507020f09060f1c05060a06051c1734060b03010c05040e 69
    0x16200d40103007590030041d50542d5154416400420410703a200c1c0a040002d0510b07161005160313003030640c0d4030195034111a1140e8841800b010900f14204091600590041e01d4405000d100b85060f07441c0840e41e17900188000c0720140115800121040e1440c41038400b00c0300072101046442406400344120550300101103103040c08104403122440304100b040500001c000e69040341c0d41ca1504105000809114440081c3c69050203c0c0c0d40301340d51844159415140300701c070f40280e82d8a601c50040c26540c06035000030030b10080030081115098006025100140c0240d1394810760307001c08030070040140412102d45a02c941500c02c18002c03401c1c100280c2d11001e20701f206a40030a02c030b43c0c40b258a003045c1101c80c0b0b000940c40340c42c1070126003810842900c1c074107851460032040039410360b58244007a901300c0c440c0c000c8a00100f0000c3c04c4894103030706004c51400c03ca151207400421101c6130020000070f078005644076401c1000844403401c0500c2200c041d2005c41e6901802c060500404521a03c0c0107400000e2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 182828812 1250 182827562 182827573
    0x100b090625060e0d020303180703050d0207050103050604050c071113091b0504020c0304180605040c0c0308010803031501030b030f07080303070201050a06050f01030e0f1b0909210a02 80
    0x1001e10600c52050350a510241c10400c50030b072a104042c0da5900680e008141c124180110b06a07400000391b036007045a103030034503032400089002189084466070000c1c02e50320805860208258000c03d025042d01d40c00e980512140d0b0340c003424081600c40c15200d00e848041e08212101c0450b80b450005401000d00034090309400d080200d5030b5040d249180e1007654403011418042030890f0181040c2c0c401400e0944065050024100c43c0300d8070383c09144606d0014020020040203030001a5110031701508008000304014840344400500303504410750b003180418000030000c02e044500009a80c400c0c0300c0c20b000703803110106240044010700308542140d074151003111482080607a0500c00c410240166600440d103d180a06000382941c4000c1d00f4001c14520707100c014400c0e0b840c4c06a1040d06608203080c0800c071150554161031800c1488403183c125801800058000b485584840174254107048904182a0710780071000c0751516145d100044c600c030350b8200320005c1e841c41100901090079641c015280b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 182830062 1250 182828812 182828827
    0x7050304121b20180f01050904080705100e1b09131109010b0a0f0302030601020c010807200606040617060103031817060f1e04060e3a0206100b0906 65
    0x103e500f20407a481009038082050907456820008019141291400103c41c1c403414645401307000040180038a070701a9070003100090a0000c0da13012244035941c008110345413421004d000300001c100c1004508940c0c042c4c003400500740245030711082c9461400602e407a4440e10342c4819030402e4080d14a0482d00c0f000708107a05e81305503450900260007003200d950303540d42d907110444000700100005840d00090600c18403e211050342e000030a9240713214282060303c2c494a0b0913009490140c0550b24698260000c0701c01100c440310f01040d00c2e801410159001e0103440d0302eaa1b64407401040c00070111140d503002c0310040000c00c0c45441410310051a80ca254040c130703030300c0b03641400500040201d1110990b00503c140465a0401074030070354407614031900003105240c0c100c8080089800038101070b280507280c9103841580c000900580d0441524403c042c8a0301100030601207603450390710f602900e81070706201072042d024008220288541100d032a0f29000c18208280381c420b80e0800c848541d0048014000407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 182831312 1250 182830062 182830073
    0x309070b070507060305010611060103020d0f140a0215120c0f070b0f010320030c150c0d02060603060a0c02120705120a050306100320071109010f080607050304121b 72
    0x18000c0794015000341868504080740030f0203841707061f4840c2d820440e003646e03000c00d1014003141183c19641c0c11900d400f21a249818441d4260302d910402902c01600d000f1803c8200c0000035895071041c0c800d484041c008402140306401ca4055107102c0c55400001200040c0d03103e4400004004802d0292100343c103145564039600b41f11102196811605502c0600510034403035200d00001c040400e41b8840c08601038100042a1a60b035420b4100707028001000300c80084a4108058034104581e4070201c0d00c003040e4800e8000d54412040c1c94450003070003400c1c04110100c455014668211603640c0081480d1804540010b016602c8503200b52014020f480c034406141c04107100420220b100c99840710380b2030500c60100a0600d4184c2e80c01403c1c50703e0592025013445951074065008162000d25544030306190404c0000203402c40c6038140c1c000035041c000300b00310b0850b028503001d407a24a004c0750010b0355004000e481510056070058200740e6036003400f043c030300d2280514810000c0010303002820400c141c0d481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 182832562 1250 182831312 182831317
    0x60607050d02070906080703020f010c020414090703020f0303030f04031202040b2a0c03060606070503070203010203040f03080a0b060d020a020c090106020d0e0d0b1b0f0a0507021203091003020309070b 88
    0x44001078000c84002c0100c4c1e1418043c260191110201400d522451540007603421250040c43c2810301040c40c64031001e540d940d510078030f000701511031948071a00d40280e8450302c50707225000491003000d81145900c20b40c100001503c1c07007200d890005128170344482c0ca080d02c049003120002000300390200404034050022401900804846603080a814244150b4040800148120300c0c15a94409100e21041e607600040c515000700d07003a54256a82c90700760904a0441c416490701035019800002404104520604803540c40c1b802651030345100d4864501450680c0c94240d042944880d09001100000c076265004110001c4503004a840c0d42c00d2080c0400c103200390903804100540c06c450100840c082d0062004281e20b04122030518100b07107950b56031049984d0240107600074101c03988412150701c1082d001c403580e09109505803611804100c0703005050358440c4030101d0107000d200a10a840d039100005464140500410700c40c200000080114000d410080c0000344921610400144a110700c000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 182833812 1250 182832562 182832583
    0x303140d09050d0f050c070e07020c03120a1808070504050a0f0c022d070b070f0b28050c18150d0f240b07020109030c0e0403030b01020102030907060806060705 70
    0x26108140ca5040040c003090b8981846100740042041002806c4a01107280f1083d40e00250b0103000a860300c21041345020200301c0380c903405108041403807103403402c8500501038040e159940d10180340711104800800310b500c0d1292640e16800502d040c0400d14094004583c030810b09031000580282440c98541a10015040c103400350300540d05180d2114040c0780342c000001c160100825003500f402d503003165158014840c408660501203400000c001050340070b40442030300304a500e03220341058a0720403040440c2c44c2030300300901080030044074051442d0103010310030f44d594614a805d01ea400c5801c48080b0380501009580448800c0c61001210070990162104c00040d480000b524038a807015541241c0c00081c0c54202d640c402280d04d105804851101c0058451404006449804510051f20004415000140b064001c402c0118110b0b01311491f09110743d010342c2e0180600081900168200e1109840801e0160043d400500c14a4050801907412400c05071400349080619200da84c01c0000740c45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 182835062 1250 182833812 182833823
    0xd06090203181902010c0611130602071a090906030c09071d0301090816050c06030103080702040c03060308191202030a0204051e060a11010b0342010303140d09 70
    0x5011040b020400c00d5056105407000030304007089001804100f005189100030704004030000c48404201103038200c00c1d03000c04102d02c450345503280c99841405100745409081d0062060400000310710440c440e40039108a41494402e00d86110201804145140246125010701c1444102184c07503c40000d4548505616034600000c03101d003c04030800c800d07081c482540310303a04001003000030882c00070490313546806a451254030394000e850013500b001031f01c500e2250720042c00304c00001400510001000c0052007242d0401a41482c050140d00b2600385000c0a05a02000e010790042c20585102403c1d4085860820b0002c007104d1940c000e00b44d078411514006e48130f8020a00700018185005406040c55004032184104c602840c0421441d001c1c41c2000c00c01c00007103010340c12a4a00139441010081030250035500381c032400d443d503269010010080ca0005040c05c40f944101005520580b41121103212543c0b116a407071601c085415000c0b801600c06120002c003d8145281c0070b6201d0582501c0c40b41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 182836312 1250 182835062 182835067
    0x20010203011a070c05010c020a090c0210060b03090c010f0e1306090606021519180501090507051005090f010e1c0b0a0504020d0f080c0f2d0616050d060902 68
    0x81c15900460002d1030903000e001081c01000001a042078800e1300f551828070746001c421080340005500c0307828076406002814600135100140c1603002c40c4810544044240c107101e0326543e55801c504501c800c8580000c10303040380302c440e92990b200e8201c0ca8032240c0c245c0323000040685c8440010b000081c1c3d4800380188075942d15820414103100740a040d00070700d020300280084102d40750305800486401403800d00c0b214505030660740100c0203a80444448179201030855003c080c40e18100d8000e110700e2000355810f1041400003d101c1c542452645407511143e503074141440209801d01c82100081a609030601c59040074032440e41d10380418545e81100148940c0d8824101c5017050500007001401c1c103143d041c10321042102603291100c0d82d040c1385500a06101440b0302c80d0814004c94000d41e00714048a0040c03001030086503e001950348014000c200c02c444c20407104241d0b42c80c21031035010390343d40542c02c03500004820340001c038a0000c82ea1414100740346411211800c45003120591b400250405032701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 182837562 1250 182836312 182836319
    0x150503010b0f010507060e0111180108100f050108040606080f03130501020c06031303092304060e0702060c1b0a0803040302060f01050303180d020607060501030201170c030604020702012001020301 86
    0xd02450800c8102542c82c04030350007244000134020300c20b04401400c040e444e90b5404011090950205080755500107116440d48852a026030888004c04582c900181404010038214220f8485a800729011582d4081c491480d1100556403084014403c0da034495649000141d610014042c2d204403070225400385550741003c012607082d8450a4000b54115440107100d8552038554000f00d9400c030101c0800c101142c1d5003480c04503802d82141d00103950b4141072440081a100f041d01c03001000e804e0495041c4201074403001c500020020444144005034004400708003030340c164400510025800030b92408002c031408202d1843d1440d424011580004000b04220a159062281d9a08140c00c080441d0140d490540066174130702549181d10700141d00450703900300d26078425201103080c0e076018101944604450414500030a000d100c00d9021400360060702008040302c4032800e2140b40c6420b85079095880319400e00c002904100780880c140306115845041003650078200b0950081c4600003d80d030b0b03605 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 182838812 1250 182837562 182837569
    0x304060917060106050d020903100501050a1208090402130b040803120a020c2509060306050417131e170709111c020d0207080304050d080610020616121505 68
    0x44550140441c800040070300036104901040720390440f00e06160080c3c540c0028074085000f8806c1c10b00700f0754980b18040020384800615000f1a04861040700d01c5c2c1249aa40c540900c3c0c940003002c802014400100015013062810f075014007030a2105110402000d40c4071800c840d00c9a100f034002868640c40806d6a82d078850070001242d52203000c40a0943c10104c090050325130711501c0120b58440e52008420300048010080420720003022001014840595a41007107401400156403e036070b078a5074002041c00221100c01102c400070718612040c01401c1c501440103806071046042580c012401301400214003003402d81402c801c60034080606052450003050750201c0b602d40652800e015010f00c41040e000b08800d80d80c51201548510140e0b40d500501505002480784810052070490003100788070501400040f41801c0c0582a1241c0605484d80c00410441d0031803010014016880407001410204c0ca81d041401890401c1c241082c9108800017250241c541144120721079415041e8204414070703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 182840062 1250 182838812 182838827
    0x100c020d0b1b04091506090503030d091506170f010b0901150912060f0c02070b0d150807030804030c060810060309060e1902011403072307020405010303080415060f1802120405030406 80
    0xc6c4904044080758500400b10f81c582c0502e41c0311004035582c40d06e00000b48103c5e2091115401d1114804100241d10340c201218121041c040c50002e904c41c40030300301c03c031100c14840c98641a20007401d40100760b18010000c1300100041151008001c50110700060a80089c54442c0700ca0f4403a20010545140b4280040c0444d074003092080110b5000e100c4c200300c800b50003012160340e100114008154044aa038014441101d5640090014440c0c0c42c000000e00c00000043c0064a1045403000f00140d5a500100ca01202c203840510580030030050030003460703020380e000c0079001c1d1060b0b1003c107211751125425800c00e91492411100092001400d000319a40503840603e40e000109200b030440c02d026000500307601c0c0d112170004001d2080b65031f007184852141300361126183c1c01401403281d0341c2c60385001400200107072006c40752440403000c40880d5444030b028001c1910920002c0c002c07500e00c1c01c404001c00c440d0881084007415420401c52504903401c100c040d00c903a01800c001c41e40c07186040d40041c5a41d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 182841312 1250 182840062 182840069
    0x908030f19140f07050c04090b0703021e0714120301060e04180f05030a030c0305130f02011e12050903070201082805040606051518130608060906010302100c020d0b1b040915 76
    0x120700e0b11000000027100159500d80202c81c074940140c8a51607250714a03000b0401d8242850009000701d110810003200714000c2080d0002d100c2a41d000e241c05103054122400280541800b06140561035001170805910100c1c90b0041c901601e840928591149026400c0005060320307640c100280c27180b103640d01401074000d014424a8100701514203414458115040c0c4038006200303030421102c29083d03a20601c060a1404200c845000da82d010b40c840142500b000700d40010441030030b11000035080a008000d840c400f5406864080301903580720b403200b076110100f10903850004800451000031103150b00c04c1c14410341c8036440010b08030341021704000e442c140903a0003009821080100112a60245030407400c0340760266075000f80d904990003e030340504103d0708020300c00d20030a810000306407800076080d1304072030081e200da140300348810f0b01c00c952500304080c02079000381c1e6001d900e0002034000c3d8a010b07400072810300540e014489110244d03945c0d0f48158401038503681c03980c00654484400e1031b240b1000307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 182842562 1250 182841312 182841319
    0x30b040c120513030c06020a0201060e0903070c060c0f140f01020d140f040c0603020a0509040c08160207080309010804050307060524180403030207060b0a150908030f19140f07050c 79
    0x9581c024603403141c0c804021b120366004140d4000c624000d41111000c0c2c4400307080502103103011807035503907680c02c02e1006481400310fa05001070014000c0008181d41c5801c0700c101108a4826106e180307010710b13a014038800364030901403840c841d0030080c0301a009010f84154045110310000d07408150703407a00a428074a005178a60107110000f03200d804440221203042c1000b5032212403109041c1d13454082c900c2d007075070003d04201002001a0740001214451100210a6400c1d0048118200d960300380b1402140041da208003c4140590301407102154840d04c94001ca902d8501c8540d54842580d0082d140501c002c1d101d0f0f8804004c0c94a082e841e61101001500d00b80c3c0442e44000d000400010054005414143c0c0047d0401c00d008654010000700e401c00f5207102d9815503160180b40308000b01e5015000001c640c010003003100c400100443e98103800b60450740381070201c034524201038041d80310801010301c18030800c059900c0c006007018040c1e408800b81c0c003d84814041c100181480750180c001c170720 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 182843812 1250 182842562 182842591
    0x3030406021c03060e01090b040c0f1d0d05010e01063201080c0705060c0a1805100f0c05060112061103060a030b0c0405030601081c08040b0a0c030b040c1205 69
    0x901540019410011121800300d0348014055042c20350081145402111031150f501d400420080250703003000031900800d45082144c0d4644074012607031040c60001060000e880b010503040b1041c3c5050420802a00c0108055600c141503500d05003140c0ca0101c5503244e036511407404010441160400460302e41150600741150180340c04003400050441d05c90728107114807100031034101000340e0107541510390f004048034130a08103140c05410b1a003122440800107050200c4031071148448421074130403118040e015122840125005641c080d0300184940c0070440718880200124900300305050082c45101d011601641b00c60074524240c51000c01048c41c4103004006220b4540c8508802c034040320b030007a95a482c244c46503080f001040c4526030005501d88208800440d10b0400030a030703501851510411101d06840d840310544070300004580140140c50710b100020000805a0424a03682400e4a80003508105c582c0000d42181d012019a20010b4040500c030f4104614030711525400c151400003850 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 182845062 1250 182843812 182843819
    0x4051e060f0a02040315061401180302090a090b0103031805040501180b0604050406060e1206040203030304080a020c0907080610031a040f090f080304061406010f110c03070f06030506030304 83
    0x1661944080c0c00e588490040000049580c0510383c141d801075540255000c800c0c41d49070030104003410442c01501d40d540301d41c5510b429150b000c0c40c425500044001d0402000c0751850b0204074075540000d001405050700c0e180c005002410802e101c1c0d0185120780c6420a54502c2d000c00100321b0029070304494021403500d0014042c8104042c540c12040d4820480400c0e100300001c04581b1728005c030360002c3c0c0c01a0034944046a61034010034451001c603001d80308680190703030b082103940c1d8510003940c000c0e416030001c0000c140844c001c0001000304130181d00403034410f0b20030318010a41190b82150284000b60454082c480107241c05014103a500300c10346001e00c140000c11600412188140e010941314945d20800c0900004568001c141100d4000c021034030360402da400c0003500c1d41d0040710201d0790b191030000028481107580c800c031401410306946448030000703050307410b6030a10300071000000144100d51441da210340d070400114000e03041b001035000f00d8601d0320002500307655000e8072151183d0410300090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 182846312 1250 182845062 182845123
    0x20c04090317060a03080f12090a11150c07060903210207050609152a06010e13051c02010c03060602010e151909030309030e04150306020c1905060405 66
    0xc0182d4604a0b401e840d09444020004060b46041e9000400c000c01c08100401c2000604000d04044078030036101003215960807111680303e0018030001001c0752030b41c1c03661041505109046070317024000d01006030714103101c0c440480d1910255030301403400124000020700c01c000031131102c6104160b042d24408603503c0043c5000e52200f46c18003c072400f0b00300100707259000355660084031254010144503507a40d03018500300c13003660b40512041421000710b45039222108407000a00c10381200d203201d074888107503100c0200305a1003501480b0180d0b018800c150505000d441517204031109403e01d50000940100e00701300c068240c50903644605c007564034010b010b0b1318000001c2aa203a8948650240708007d50b1070810004511203800b1405404a11300b01d4240c6c10150942d00030b002840c081d48580f002c0e25056000c00c0183d40c02000160300d00d5400041c2040051250b4029190600740f07074054a0109900da01d800102410341070040d44c142d8095020722080c4001071298108c00c001064140180700c0714003241 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 182847562 1250 182846312 182846327
    0x14100905041518020d050a05060105060403080a0e060d020c0706091a0315032404030306470a03050406060e0618040203072103090603060503150903120412020c040903 73
    0x1031080ca51034400103c2c0d000400c0c415412401d50062415920404074100a580c070704810004446c10310510001003000c2c61b00c42c098034212548007003000e00c0c0c003100345400c8031352a40480c50302d40c00850501a0013000b001c01d0016003041d49100004110880c074111004050342003d501070702c814a030b038030305804074007003480e007243d601000440c81d00c050068400702092910b81c0c0d03044489000741114444259842d0092007250090b40640e60510025440e880c2d083c640040c90300d10540040c004c028810791440d0200d0400a03032641449a1070035083c0342d1414071b02641c2c0250280000260b0f268100001c010891041030080d0006d4020070100d40344c01d00c04034524504c06440b04010103201c2c0e000804640e400c0080001070501d202d01220500c44011242c5800602d0010031000f0811840000c20120b10a1150004a83c8000c006100e044500038018210220203495a01070f030208105521001e144d01002030f000e1841440500d01a10215000078200910508464440c40c1400601c40200c2d40c0210b8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 182848812 1250 182847562 182847593
    0x110a180c1128020612070305060406050a0314070911040f0e010b030103020d050f07030602030a0c11031608090a170d022b020118060b0301060b040b030a0c0c061410090504 75
    0x310082c0c1c0c48003001100000c0900030002903000000240810140d4400450f00d0300400c11500c00f0f00468803810204001d603203035801020b8004c00784140c20004500140310148189400310290350760b0b00d0300c1c5c151070070a80e0590340e03002d443c1100010b0108480c02604548400504840201507541e5050130b1211100f848184006803240000042201c244001071010500c800d660108450300a9502e00e45000690011100e0500d010300d0252000d501381d00802c507000c4a080c800001c0c62603c0c0b068000c11034810140c2ea019200702c0f105000000c2d05444414100010304600203103400c2045401030700614001d4072a1020341150003899800041d52183c0e1008016150110300780302841610b848201d0060080250045010038842c0d1038905005069000c03450581082c2e000340700c202d481d05414030580c49a4404c0c1c00404500f000018000d140c01d61102c0b2140ba01454100d40110b80d03512003009649100f0607040c0c0c03040360b10080c41a900405001d1400510440600703128910740b5442d5044080c07000318 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 182850062 1250 182848812 182848843
    0x9040e060709141f0e120a290403120c03180b010e24130f0207060f0b030705031504140a08030108101109010e150f03061302160f110a180c11 62
    0x4204915907031450180e00b8a500d01e01c08036500d0600340d0420150212180303042c0c802001490b2440c00c9480d0845c021140304941503222f121a07104440010001030291540250401d0303621405000008400c0902c0340301c803400341e000e10a0715410a01c04165450004d0180d01c014604010520568a030a24cc1e02007210b401302c0344102d03269030a100e010003511031301c0c061421141c400036421081041c294020b4044290a220820101542d10f06040d0341d82100c0c02115499404007410042110503512010f9002d4030034a90445480d1345021907628000c0070070800c680540012006102c0e030002007001e1003e50044020034060005900c586840b60300c03d0340e00103810400030304480c004035100c10100303842c07003c009806a41d41d81100704402090303400c04d0310075a2103425101629001e0140c0d500076100c42c64102c07050003d985440ba540d081c00c04e80d03080001c40e010042c44012441c1562485036401c02460008580141c0340d08201001048030b4907868a83c00b031121216003090205c0b00040d58512008888 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 182851312 1250 182850062 182850077
    0x4051516060c0c050c0307050f13090f0510050f040201050702060706141005040b0301050f010b0a0905061204030f08040803070f02010605100504030b0109050906070509040e060709141f 81
    0x1051608005a001003015201604101c440088241d1152504080d10700540c15104038559050405031105018032406500030f000b00e40b00f003542d10b00b003225071020101103140040c0441e12a602c81c09031402088040e20f45400c510b104a08805081c0605903206001e0600c00305689801d6001030514015400040d000c2d520100390b920800216600140115444016603021403400a800c4000074005020341030141b41494080c5606003414059240502c0300c5424401c80c0f45c0c2083e04880c600d4106050000c10440038850004542e16182c004045011580903c41c00340d02e81401c0c00340c80356041480180800c1000010040890b400209403900819207107000ca001080c240c0f07049024009541250f81e00054007105400b489070011700900450b071040d19841580da98a0185c2002c5403021120850b0681185c1c0008075050300c503400411081c480100001460129030020702e00d0007404503020008182002010b00c00b030100f40343c00b045052411030b40c0781380154003001e0a030b11800d5076110344414003602c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 182852562 1250 182851312 182851327
    0x6061103120408220807050423010915090203010b03040c1203021c0c0c17060f090a0b06010c080d050907331704120909020f07021e0a0608040209090102040515 70
    0x4840f408400c03601310940e000700310380341c031020364030b034003c034031800b44a20f192000009090022070354103101030140820845091b86010281c1b006040c2d0038106030300104d003c04c4081041503007803003d58007902c0f4046c035503510b070f152501c1c0150401200d900520800c2246688050000ba400524604603508a9010621030107032050f0548251a1203840100300341c40011001c1007514841520207140070040085a07002d8450190041070810151060051078000b0340c0340101107000001c078070350005018940132215581c40c0e1107480705500700c10054005191100f00f40807402c1c078200103202c0542003c0240052100c15101c8503000c41c0c040ca5061121107402044882c6094001c0d0030050441500e0140c10761149400d1501900c80403d040680c008240b20344c0c004905140c0714425540e407552000304051500f420791b000c0084007481b03000c00c004003080c2c8040c035004503115080090300610042d29940c02a04240c4104240d103000100404416807040c0400c0027190b40b407801e06e13924011034404d0760f0341d6100e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 182853812 1250 182852562 182852587
    0x40f0201030f02090409030302070c05012d050f03091608011e050402040b030a2a06090b0325020a02010228081e04030c0e0901200a0201020405100306061103120408 72
    0x8411304941d2103440c003c001c0c0d0a00d0340503002070409610035401c0050864852005445691107000d040c1c0d0100c0c521801444000380c81c81c00f40008018500300350741406038103540074056a000301c580140a410811201100030400034100000d0f001c000024803044014049454142002d92118035600361210003140c195110340c0c0c010028a0b0014054941090503410191001c1c0d0000085010700700d0b071520700346140080420040c099406695806020500c2c01101c48071706d40014001641c41120f02c0907044141011003001c00c403e800540140050002500000e07051a0011a1401142d1400f141003a0580d00c44003e00507031640c0020100c1d15544022002c0040d100c140c480c80089090004010050010544020701101d4001c0c91400c041da80760b00400c1c0c2a2001030041d42021040000060012224480504554542840010f0401c1d5459000840e4640c4e00c0348844042a6141c10a002e81e80e4080c000b001075240e0710340111715010b0442c00c04240c0482c0104007500355032010074201c02401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 182855062 1250 182853812 182853817
    0x907020601140120030a180603060303051614070609090c02010509100504030210050c040302040605030d023007060203010e100803030402010f0c060203180c0103060501020c0909120315100305040f0201030f02 91
    0x844d0744003101e03180c03100450701405507402174002d070b84492030f910f10001c1c2641c071038016003060700d034141e031103501b0200d00311641f0005112880c41154000006414800900002c000001c000c9c20180c2c0c03442c002901e8102000304480840b441c1100b10790520040000721000003804036024400008002000d60340c6080881c18000003541955640d405c00c0280482190104080c1c020342e402180c0c1000b03415039030710406070380d600c0a500c9040581c0180305042880c0741b414900010075000d50300c0c001c07845240b85804544a03403000300207d8040c0c1c0e012005110060340c1204056000382c0e0001e80107030407800d100c8020741e01c1c000144000e0400810010360103069218481c0c01045030340c40801075449080582401c1410011019240210300c40c1008014007580b00380108402caa5041c0c000d0302c0c4181a40c001d0011001004020101c28403030075018255064940f030045119819442c620442c40481d4801c120ba03900c9103202200801d8240014480440c0882020403416642402c0002c5c00c0f2403d0300382d81340a070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 182856312 1250 182855062 182855117
    0x406050120010213031b0b071e02060c0d030e010e0a080403080d0b0a17060a0605180603010e15070206090601060912051005070306050a091116050703170909070206011401 75
    0x14a0113180c0081003005903070b4030492a0b03819a002404d101d0720756010207030740d00414070090035002c00c0410560400144690b030007110f40c0040c00c0c081c0f4268404000f18501013460fa0f007100041c0d0758452440c0d40010038400d0000d107460400140600400316290323500b90340964000070305407a10000c2c0c040c00d010300b00d42c4480c084880141c5000019a500c07200b01c1e0540c41c0d0800c02c080349004000000b4041301140c401e02c130550310001c18400700340c0f401400300070b03090130b008007416055985c41101300c062913001c010740c0c070a1406018130018180341c0804004d080a00280075041b00742d000c6001480110703007124500307090f2545100043c50600c0c19040c090302d04200d29000703401203882e00052220495054104005071042510003241080d030b90074030303203080b03524507a2000100b20080c0458803414161071a43d0100c5401401121031443e100c3e1112034450040b40c00305100d400001403810384506068070303402d07030180722070000c4c0a45614103081d840002e48810304890400c9007002118401c030300f001d542d5019a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 182857562 1250 182856312 182856337
    0xe130e120703030c021c0c020a0306021b07060e0303073206150f0a091503080a031b05130b030711060c03010906080f0703030c020d06230604060501200102 68
    0x80462003420200d20751222006900103400c1c5200200b0740d500001342c200d0070002240002d100c0c0e40d004031003200c40410445040307a014030707a02000004130307050740041c003104501c2070150b014460400d05181c1c42e0640755840740d010711144050408483d54007201796401143c00041e4030030301d224480e1611860400403040c2c28030f40005240301d5000d0740000611a40f00310f0615000b078840b070301711004111051800548455010a1036030080c8040d2074981c001885403608041c000c6900c1d501c03980e480686411000d02440000d07901c2c511111500120000e05c6858140790421616003030301555006005541405540004038000003c01c214900c20118901c0c44281081030f1030300340c100500c00c100b03141d0003813180c00c400c14146080451801004213028040a61490050030f401e455580d00360382c100260181030360f10000003108000800e800b8080c8100750001c0c80c5c141c200800354030b08001407040c07002d032071140524070b005014015a41c00240c0d4940ca00b01c0c10840ca419943c041d0382c04c0f40a031040c0792401c1c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 182858812 1250 182857562 182857573
    0x170a06030f0515091203190b12010207020102160b09090c1b0109051e06010611030f030108100609230c091807081506040302040c09030501060f03050c0a05010e130e 72
    0xe0240200e509109000d1880403d14161180d5a44940c0c0d0611003401009403d42000451490480d0030b045030000003ca580100d1406122800580485404500c025a41e5000601c110856a051104807603420b081c07042c1d940d2042c2400c18081c031074004c019440d4000d41c1c0e45c8002c43d41d191802d8060710380100350303410715201180b81103400b14040c1c0f0f030484089401d4420b0200554400c003843c44231100c03c080c2d179001085260310b001403c6a0009092680c9007090104001001d0000c01003001036018100040050a0344680342d800402110401d60000004500d804900e01d5461f009141c88003490520b21101816611551007800c028811000444d6010f148099288400c441c5100007038410a03d5858844c000e6a030780384100104203007008640e5020300200002d100620740344d403064148207400d00d45482041d032280c0c0e503242107a403075801800c80350484840c10800c100040145d05038542081c0c0340e03100418503210020f8014248201c00c103100310780d081140c407516140d81e480700f00250048011500d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 182860062 1250 182858812 182858843
    0xc020d210f050907030c0b0703050a0c0c051306050108180d050f091e120d0917011506020f0d0302070503040303080603030d05072114060111031204110f0a06170a0603 73
    0x20b079182500e12003100c48030b00b40c100007c1c508201c003090f541c200f80c0544840f483c1456105d4101c90f2200350240c100c0d072040c24810013044d151074107207045031244900000013039140d040ca00050203040c0020300500b0008601c3c01402424003010404d0b40540c820703030070483d071590601c0c0c1c03401090380542c070320094001c100d105441010126140c14400400307070550341d074821003d030b4441b8103860780303911408403001c13510300c40c070400004540460400b08100c0f03a50000808080c0740451280035a11075019100592142507592840c4006103c40a5040702d281821454030307000f9500d1541302d0149210150034004401d00091164a041c012140080c404034020045460604800782660b040114940702250700c9600d5102d000c0c0721842120f07042e111545201c01ca0780d0b1504011902c014802184500c0382c00180b088540d1040c1942d04607000718800d01a801c3d00100344418009006079a03a8464410708840c8001c0190980107003c82c10240304c0401090b049076208c400200180c691a4001004442401c6092 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 182861312 1250 182860062 182860081
    0xc0e0621010f0e1c09031a0a020c030a09030b060612010b090604051210110901020a0f060605190e070215041e0206031305070b0a050d02071403030f07030c020d210f05 73
    0x4138051802e151011044005102d003100c6500050000074540400308065845894024280340d40c004034054015151003000d003080c0b404c0d85c000000e81d070041145904240700704142d030072000398891400da4031203050103000710245452003c18402d01c071003180e00041c180f4240c0c03100003c541c054076002c0d0520700201c602010980e500c280e42c5003102d808a15000c500e094500e00f180849000c128168014003030021143c0b42c04541181803c012207505135038020014098442c0760045000300e806400b400c9003145440c0310039a0380c0c44000c0281d0115003002e07401920340c00742c0900381900306030440c02500180c0031a1012442c03000000328083d50044002c401c1111000c010540c13800078030b00c11425100c07451345c3c44080070040c3c0510b40c0720101007082802080d01480c0150b000e82030a6010701a8140c0300502e001c216411580103a40401c2d800301002e041145041e014080c07025400880d2009010070400f000c0000c0c01e1050303501020744182d819805589410107541c000419003403041c07400f004607061a2446 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 182862562 1250 182861312 182861323
    0x405040c050c060106090e06040203070c02270a02030f011203091a190c030e0f0f09010e16090513050a021308071401021209041d03030a05040c0e0621010f0e 69
    0x2500b07900d1040500114209100304e484800302c0f0440356180007240c8600c0100705c041d40005001004000d01d02c5034a801595034403841c0318000b40700d070790407003c00c8074203588121226000800c0702c9207180c010018010100381074202c86046544800400216109600e000c4804a103261b20801558010a10815860000d003004010140c0000d1321100000700c0c1640a496485240502070041230728000c9031a0541820900050b04130b40080000304588800720000341e00810071b03007181e652464642e007002280a007903a04807911648a042065040b4580000901c41318007000141c01d5807034651012891941c05074040d60b408602e52401c1030399503a11400250b5070380c0010300c1050381d071400c0a92500300c44d5001041c040e50200c3d4442c10989000c0402c014040038020102c403503410609120340400c5c030004181b0245010303882c0c0c1c6a01040b281000c2c10015100b0815400541c56094942c5c14401640e6030018220120b084100342900e1551040300344600406400c3d107144821030600324080000c2c2d40110301d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 182863812 1250 182862562 182862577
    0x30f03040c0f0512070b0c0a05010504051e120f0d0b030d020c01021c0c020d0c030b07050909060402090d020d02030c0a0f031403040302060a030f06030c0305011a1f140405040c05 78
    0x16289031559184200018450f48413075030300742904201c5041c4107441c0c41c03c0c0200341e000401002c0707070b00a4400b41d031000e085420880d8155055000101d00705812000f003514007040c4800e0340000d009803008541c81c5c0c9040d2140002c2009130f40e40c001090b4180f504281c214880c1c101004003600c40341d066035000030351180b6520008500601403050321000841c3c0321170a8841086041c3c0d0f564241840079424402e090a964900395800210300b50000002115402e80c0e61164107103a450366101c90740c2406000a004014240c0341c4500d0041c4145076050f190710f504032036490780486500352152080d0011130b05140171940b6954002400319400b05240403100c1110040300d21507001040040c2c800c0113019280d000d503003c000e42c465410001003203c20311a800002141c0b2060b500020318540d00d96505031000c0c150350080351140d4480c0d8900b510103900c006115030100c01030b03862469210302107600e0000c8002141d5440d01380007611040c003929988410030366003e03150281c010080c0c020340c0720b00039129400400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 182865062 1250 182863812 182863829
    0xd090618051c030507140c033f040209040b1812071a06030a080a02030c011b030b030705060f0a0e10031407020c0a0e0c0705011109100302090a0308030405030f03040c 73
    0xe00502d9051280c440c4a10460650707486909040c55500c030701e05142e00c95004c0203143e1000307010b05409080c0310500e885070301500911151036070700544040c00829030500e0b051004a5846020400561290b940d41e07980907602c000340d424a9074403a003091181d8513604581c0100341c0305031146903c071065000018003101d802550b4001c0144510321544a034201d08440454050700030103c0309001032010700141c400c80c810b0380140c2e0300302520345c081e0600315860100c0500303803c2d001a4900762113640522030031130300d040d0680c007a0003264184004a2018464568440c0c034a0000080c0c0302c43c014450f00000e110700718010a0740705000c1700c03c0c00040103003800b580003094045440000c500d416000156030030641710090b141c05261441e0100c8c0c45d400e04001419214110002c04c1902c0c0025802c0c4110f040c584c40d00b03540103407612188400e02c010081e07101c80c2c0c0418188100541140c3d0358440080070112a40700d01c0066032a40c0e54a0540e095004100781c50307030144004020f01040000072070030101500c2040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 182866312 1250 182865062 182865103
    0x2030a0f06090b0a2c0403050c0a0f0204050a020306030c1302271008150907030603080c0d08010506070305040b0306010c0c03060608010b090609060103091103030705030d150302060d09061805 84
    0x644c111800b101740c812040c1c3c075044228004420105a00c40b100e54818003d06210707080c1020108800d00740b10300381c5400c07101203070b40c140f1400c118685032003042c0d04660803031400c50440c5080070101c1e544039050350100740f00d0094038414082d400b4042e012902c607001d25a0138400d04018421413100210b0f125001c03180324502654145240b00c0c800d202d128824291181e0464400c60700000740424160007401c4c1074201030711401c2c08804035901c2001031541440d8107009114040501d00c00a051200c11b800003803040c0720030481c04000c07d80c02000d0f1001e84442e070301e0069503a01e607080180d0b403e04e4481c1c80108080070750100001440940d50042c000c450130340c0300070b0001c038103800d007007060f00101110515030001c0c20101080481d442980000c40e02445904101084100f40c1d0009107150401d40c4111010307400001c0381324618580d405000301603409498040350260440c0d0000d201405900040c1e0a61075580c41480d041c000390b03070409145070b54901800344c440452420090344032140381d946608000c801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 182867562 1250 182866312 182866319
    0x1742012d03020304170a120218040e0c09011e091e0c170a0603080315150d0902010e1807111f020c060601080903090f03150f0103020a090603080d02030a0f06090b0a 72
    0x48421074101c12072035a01c25003800d047d6803484c00250403550448079150144d500d08400ca88952148090301b45d0800000c100c1000e031002001003588058200340c02440c1c0e9a4075019a80020320503c2081c0d403003805002c90482841c2003c42c500780d07040905510041e04041c00482090380020200dc008140200034000540c0e411000c04152107407440020980001040003400045003100703082c200600041c00c14052404010700e0041a41203e02c2d4231604030b42d110f40540456800038408030f2820300a4602500055115400c0352000c44d00810072014003080501c209403068091009524007410f11862203055141ca801010003500102740c1c82c60303980f1840020841941c05141c8261040c101c1000031450f00c0100c505003c4856a202c400603058171810304400110440945114880c021035448445598918010071041c0c429540c01040e4962900030184040f61842c1c0c11125403403000c8074003503a25103403008848000c2443d000403800c02450104049520800d98000080b0300d40216200010a078a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 182868812 1250 182867562 182867603
    0x20603270a081c0c0206040201030f09240606030b031b0d0b0f010608060409050706032c0f070e131b090203070e0108070306120b06011742012d03020304 67
    0x4130080c80202607400440001d0066120b5000302c15184002100810402c2d0940d03985a600088020700c0400c1c414a002000ca40e51894490318000b03006a1900b48820584403003c01d40f540e046a08440d8500c00c80c01c240e0940d5258980e003e24059481441c01c0103a140413a1201c0d0749541c06e00074180003400c444040f800340e14150142140903904040a044141e28181050300205060170032031800440c140d0880c005294801c450030840c0c19058060310106030300c0111541002001e81107464910152801c1c0800c20186411040905601130851a2070100302902c041400b107007540168000da00000400044036801400702145241c00e8031001c0c010b0300c4107002035050b90154020807400a40c0d0000c040c0128040d9840c2c542c1004e018107061000c10452110100a04402c40c0e4440a01e0891071254034014020802c107150178281c4900c204150006044101d61900c2e0400d01c0f1f810428031204400c22400d102c2540303079406a415401c0c018030710b1900d902401079042110103450b0340b441b02c801001c2404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 182870062 1250 182868812 182868821
    0x151215090a0c020c193201170a020703020a02060a020f160503210c0a080406090e01150f02120c010911040e07050d08040b040605030103110d020603270a081c 69
    0xc0300c0d0b005002d01e10042030505c86004055817200e031000e051002c00143e0380203030b0b80c002e0021824410700240554840c0b6810388540b03204084090403c258402e001ba0421488000c0503008116000056615096820100d04d4150f000c5406540100c00145140040c3e800044941c0f1120b41c04085c0d40c03c0482d505000200c00c0b50902ca2603405030442c01103960300b2100f0790f070f031100441a651000c50815920340c24180c03500900e407004540c05030000030700b4464148c01c03010ec14000d110000b05103480390306025052030f402c1080350000c800c5c08000c1481000c0c26000740440914082c10480300c42e03e070405650001d02a10450009642c8900700044166143c1800d00600420085040040030f00511b0801480308440880c00251106602031001096415a02d40140014200e564980361a5410b50a2100c84075054407440e91190b0225000d000043c0c803000305a0b81d02c9108642c120686601094460707003101c102c074503102e00074012591940d040002c0a8058103004203048452480701566100b000103d5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 182871312 1250 182870062 182870081
    0x21c09120c030e210a0303090b090a021c020303160b2707061b080301091409010207020a051c050717060907031106090a03060509010c03110a0509151215090a 69
    0xd00e905910200e5420528000b200e0013403101c460b0242c0e9081c40c1800f6003000c03003003041140000d444440031400c2c4440d92003604c0c0c00c0f009000c080c00c06d1403000d0340010000c12205040310301c84d80c01c00d130a20381996002d100b5220b0300c00c076000d032050a0241c0352078130402c5400c0842e104010000d030710410403101e1141450400b40401590000c0a6040c24904180c4548103001107840000040c4e109a0001030847d80180d8004c0048100100350f00c219007180c10b0242d840180303124216031060080b5005039450804080c2151003ea800c0740ca140031505081403c03828105014201d403240010000e13281c8039200300400181224006d940035900c0d4106015224035071448003030074125500100300c0e440e02e44040104103045000308141d600c40e0b0380e0307900d98041d40c500301c03440c4031542d42d166903c854140e0075010b4521410f1040b0142d03131600d456030a0240c800e014020750070340145044441c80c16407031201000c070350f020030903401140c49902d49440e1840c45c0d898100d41550040c0381d032101143c0982054010342640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 182872562 1250 182871312 182871317
    0x2070f0203100606080a05270a0b010e0601080720251e0b0d14011e0b040602151503010908040311030319110a0b07050a02070b030c1903021c09120c03 66
    0x40d481b0300c4d040401a01010b014480060b0103442d42401d480b005810f50700d4804a50800380211a0081c1081e070102e40c416030160b601725000d20100441a81d010314955030003060b44c14009a0f0362003408201300920503a80031324500d841040c034000407010008840340f8022404540c46448252a40400c2020100c0287e83d0000950868014050741c140341d000b6100b40d0b900c1d1600041d586400140d9100c0600f03007a031003003058810959094010030302c1118084094200144407524040ca000c0c0d00070f6682e064a072885800300c0090002c0788010348440132050300000000d00a00840d02c143c03d2401e41039106d40300c12a01e003204000020303003505001c0140c5494906141c035541c840d5a8045068440310b801144981090261491b84000a003403034043c0390060786c0603680e80d52545100340d0042d2815401d50880ea140c103000303008104207491240221001e00c501c0a4032081f135281711042c243d010b4094a0000c01c400d00b1603100a001408003640f007a42e170756004880701010499081030560f8103550b041c002500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 182873812 1250 182872562 182872577
    0x91413030516080d02070c0e070c0b07030c02150115020706090503070506070218070201060801141006050a02030c030a050a030612050a11130e0102030f100e01030b041502070f0203100606 82
    0x421004200c881c0c10300e1405050424a0244c1c1310720160300700c1c0c0c005041220320700d89520050040a18171000345600c001c0604010414a88640381c02e4103e030002070107902019190204a00380c1c52080c03002c0203205c2800c2201d440a561100499510f10303a244c07070400b00620a0010000d015480b55034044220364000c0c001d450100c0c02c28080c04003d44c03100da03040c0e03040314254501802001c00008801c1c8503950b1680000390b010b04244069085d22019005034981c0090749040c400a00c0e81525180122021410055900d80c2c1000d400d90550050b80358421813800046040303c103050300100240158282d0760b0b8100030301500c551174202d400b401084060400c0c3d1002e143d0000107143d91b10f1019100c00001c3c0740443e41c6018803000c005403803a00001700501d94003c414400c21009010800750081d100c04002e010f4a820078041c021400814800034103210306007004130f0305001880310b081d200d80c0074002d806d540d6140300b406c100a0140812000328080c0c825003611552260300c9200303c100b602c0d12645e6008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 182875062 1250 182873812 182873827
    0x307120b01030b031507080c1201091a0d060b0108071d090408040504020c0309190501020a03080402010e0901081e0102040605090f0406050301090c08070501020706141803070914130305 81
    0x4004054609040d8181035880c01003007103560301009403618001e244110040c0c0c0d0320f403000004081c0e1502a00c26851102d00b40182440d4070f61124040d810b413a140000090740c50300c104804854001c00010b01074010901a181d141840036a40001007035072020b032075030095034580000c1160984a44000d10001000d411218000703450000c51047e0010300655110742001e864400050480e070007203545c03030340c250300000f803007006401c004a204003501010107803000c80a2620001030f4442041c50b0b80101000361a40014086a0040070300d8812010042c041e00503a60316450b42c6507586003015156040302800040301c000341e01050080310160303031030741e651507040c903030700308140300340e440c40d40c00da10f940076817922008102c948092061000c864010311151000510301920f45052420a401103411074005403814004150024000c4a44c944040b00b80d130342e21740c0c4c2a02a003110382c89000c20f05078035000b0b82c840081d41118981000c01c0b02d041c0741c0104075454803a0b40800710310984040005020841c180301c0507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 182876312 1250 182875062 182875097
    0xb0a290d170f0a110d170406060803040b0304020306181b030708060903031803040506090d05010b0a09051e0f070c0812130b0f06090c09040209030a0f0b0c0307 70
    0x210036521411016250741c0700005001ca498000d000040003602000c620541c0f05030f0300502407041652844094605002c4143d40106020480d0000c2c211650507170380400c0400000f0b0344039400501c2c00c88142c0303880d15114954844507620607141640b0900c20000481e4544a081d1580030704007038110014243c9001040b1113400384486404a590b03d805401c0f00021548000d2201610403200007000c1c5a4a140114261550f101e0a60303c0118981c014082132005481d40c108480e0b40400813107030340710480107914040780507050041c0b445410441840300010740b070009400c901c0c003d0300390a11340d00303550145601c0140a06c504548882c0d44155617408602d84500503003079400f210307005111032482d0000f0804450703000d04c001d880c0c81d042d003440b00301e0202c00d00c04103810380da030002130748090700389182441c01c00034540d482c001c1c12003440c069000035684003940d01c990455498410182c255003d046182c00d1601030b02d9500e00b0155a4800e03c113001031160f00d000b00031240b141030181c456024000361205034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 182877562 1250 182876312 182876329
    0x31015020a0506100312090608060f040f0e0106030209010b0a0203071103010204150203040e0f01051315090c03060513020a021207030201110706020307090803090d03050903190b0a29 80
    0x4000350700a0100240120741c091209030300c00c0d0803d8030b01c0c05400d440c5180c51b0030044e000d00d284108010441e4003c1c00030903408540b40b0f070450743c11164000400800c0c000a070040408401659659251488031500c003141900302134116802282c1004060b0b03039401d40c2c0b004500c510810000103030130070850040012181000810600301c050001402e00b038540780000c907400c0c003030100c100140e840030400b001803641804079103602003c008a6451194035260200e24400c3d2400403107007a660b02c4014a900d210a00381240000f4180d440f0248040350480001400405141c0601030040c414100e40f2030070140c840c000c442d04580964000c04502d24000d2004015030000001102107540b00e1492030480915080174082283c040d1100696070b080540d006030200b00356074411070150304144403064099450741a00c507403040d054102140d6070414000000e0812003883c44004000180c2030038042400008480184074444585042004602d81c4120355400f06294081c5145044001c80095070317424407150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 182878812 1250 182877562 182877599
    0x1a06010e031203100506030414010e1c0807170109060801060e130209040618230a030f0f05091201060503070e060a05130e0a0506071b020a03140a080f0316050310 71
    0x8284c040e5502da81c005450b0740d1003503070700340c40c004003803803103004240007c1c130920110030a400c008004607030b5240c2802d601e258a1116040921901360000341c155802443c0106d06100c045210a440c2d40c1c590035004001c003400d000d900700035840c0c0680414603004d8954198081c00c040c44038001c4040c441d41c2040304c50303103000300112038440d1617a035012030800ba400410700c1c840d4030444050100540d05200540100301c03102d030020301988040502d03c04a50002c095000b90a40c602c0c00e2000d6594a600c1074035039101e202201c82c2c00c400301038003c2020349019070210701074070b60803420f48140d150391348080864a402a2841540002c07403500421941c502403421000e49040000d0100f01000d00818560910412807000d13078154014608002c1d210b40d00100380d41d02402d420341840748032001074020900d041101c2c00010040099001101d11107031041000080c49684501c1c4603a0f00c42840c0710403403668100341e40003011082c00304549481240182c066034412aa891000c841c02e0303240a11491071f00030000d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 182880062 1250 182878812 182878831
    0x12051b01090e011503050a021219090f080a14040f1503140f06030f120912010608030c03070c05040b0102031608130b0c1905060a05070212071a06010e031203 69
    0x700300003014255441d4042c02810801c00215072104411030260039070714000d04495550b4410401505204402171080d500000b44040eaa0311500c1c03d18144e01c01031903044009032881c0048603454007000010303030080c20320710358507503802e100700315074094084040c0a54001c5c900c54043c039002c207200f044402e04011866a5103840d0110346240d00c0c80c00a521036030160381000910ac0703070b4020004a42420050310a42d407030324000511750710020840310309241c0034441283d03104104070700c3c03680700d80b1209401178000380400005403a40c401000890b6a680e6006110445282640c45800a20340c5400c1c82241d0300d00e0010b0300030f035140261251400116259100d01184c4242c1d0038020241b54400216a52002c1c00c405001c095860203210726413450042c2003100c0380000c0070301e80200c100017200403c2098000a14000c0481c00b030701c0e1000281d0030400c43c1200901e4207400407800300140016001d000c0a0001d514084007103580300d440c011169608010354042e099030081044810080136040210b5224100e070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 182881312 1250 182880062 182880077
    0xf060e0301061809020f1009051c060608060a0b010c030c0807150c0914040b01230408030304030521010501051e070c0e040c0f0503060115050d0e0106080712051b01 72
    0x10b41c40c62001c3c414006a000d8a5540c0310002011400d012119050403402203800032801c146040c40100540c200d40900c90003100110038200c4007901082040d049164031140a008181d1900740080d61030000b01c410781c9a25041c1a0038003815400381400c051000d400d551002c1c403051164446c01d40030740c0421000c688281c00383c1035204a1440034422450a000f41d6610100c000c0e107400302c40030866884080030b91080313280c0500143c4d01da0700f041c92400001c0429014405d0b8180240314072549010300d911414590000001704010594400003c268000d021028000c2640804e0b86030044c041007402071a020071410490503007800466900b0034880d0440c00e030b10514040840d910301d00008001c0e440354403000c02c014180420401407010a00107010703241e000d40041171501c2c1c0000c3d5182e07418894050062190500030941c0c034441d070101c4d4500002079100b405034510342181786000302101d1099230300a003e4000082042100520703590385080d0480300030400c003843d10041c00c483c00c010510681c10302956 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 182882562 1250 182881312 182881319
    0x303040b0402060c150108010f050108030d15030b040602071205120c031b280815010806040603061401060f05070201020c0427211e0c020f0307080703021206010f060e030106 76
    0x4025401d60303130b400885c884000b9450414101c0c03d40b9403240e00a2140c900b00300051150b94000000e440654000d450003003140002e031191104400d07e01d400c040c0461030440d00708010311905400a0007094480d642d0202d551102060885950047c2481c00504000d00d0011892510400740a9038011681c120180e40c0034800c449481d1056101803a0050300f8000d10b40c806118080801140d11100d245003000121450a00380c41c80140e11552581d030b051240c2e04020580c1ea468a81c01000a158005010007aa002440b006541100244202c0001511030401180341610134425101c20030b41c1a00140b1648035404100409008540b40e803405082d5041e46500000c007150740318401a81c01007001500102e4401554021080f81401070814040480e50f000b241c03030401410715039030203082d00e00000400703558800204034440344207826a040c0301d0340a001c40c01e1440401c801c8100ea200311101110303802052082c640f101024410360005100343e00701048403e01400d45144880700007400080c1d013544 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 182883812 1250 182882562 182882587
    0x40506071101060f080105060a080106030b01180b0d060218010201150306020d0b060304030906171e0a06051e01030b04060e18010908071a0604050f060d051e210c0303040b040206 78
    0x1c40e40e0081843d40c2d1180c051010600f4007278072031005024420300900c403c904540710ae102648041c4101c00d41c2247c05030001c92034140d140c2c0010750091004003910540b110b1803c0142c0a5000310040304031a200071300d20310034035600500c00e003980f40042040c0b40c800a07180d500e801d8001c0d04102d80b1004080e4840500340425542c620043d882103119842e803210803803c0110040c2202d00c5c507503000510860300340a203d403010b4803042009404d0959100e14506a50b0040702001825699200071b4106e01a124001900c101012030244000720a0f0303020003d81000b8000c0106950051141d03100e200e81c542c0104d02c401840540b01c0c1c84008010002154440c0e01c0d0351000048e40c0600810364000842d80505a4001c0d82c040f2120f4104c2000c8034180054100f10041140440014200a01c02c00b8071b480c6080030000e0a220702d901a160040c40d0041886480e1116520b85982a0341c0f04040180b401c2811443c81c905c4080d500d01c2170440c0019801c5a8882c1c2d0340d038400b0a00a032090b60f100905000c030040194 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 182885062 1250 182883812 182883839
    0x23062802040e090f03030c1602010e18010801150f03030c030504180603110d021813020a0b0c1903020705040209130c02010903020d020f06060609040204030b13021804050607110106 79
    0x1165000b000c854a0a884082e0074035140c112162029003041007406171001101c1c1c11b8640e1585401d200c10022440f0f0310050318406805403c80350000400700d1801060350003c440c41e412500f0501c020700c0002100301c94100340e402e0f0360184401001e9122810300200c0d00c201003881c0c03010300c01c1c2080b5180c9038407805090081c0d50b201d4080181a5161030003802082180085e111000c0c0055641a02010003079001960400800908a03804000c260000f400307040702c61242800f45802800c20306002d51900012500b940c013880340304240744900c17a403442d500c84007242e00c0001c5642503030145c4001360614003008040c3d0f1082800592090740e501502d240443d41d407140c070b4510b900b140c000081d0401d061070043d0034a0000c80f45ca100355000350684140d0058045051544580100c8400b0384d0394130a84001802400f803900080c09401402040000b107050301011100414001c40300214814880035074000c81c420100c8009203580c01c1000403a50070ba0050f40551408005400046a030b0354880000c1c240d180f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 182886312 1250 182885062 182885069
    0x13170a03020d030501030b15060910170c0705070e060d02060c01202104020301020c061602070e071403090c1309061a0109060819182306280204 63
    0x1500a448210201901003151220355055400d080c80781d9850741e1070701208903100070a0828010100c25600c013241e0395000c103d0715404c000810084650800c0500184085081c01d0b5400440720620041210740a40c04241c0e0b0700340750701c1002008024149414107460440142000360011130600030764005994150141c4060358901c6c000065244413891100300c0c00240d003525071120101002072054100501070010302c1f41000c00b140074815101e07803020a0081c0714010990320207010b4103040c080b14500b5070030107143c2c0e242c80d5030840c3c0101c5d071102e0498002c41c0054034900c000c91840440080c3c0550007001542c1c0c07002082c02950000d40c02e50001c112001c00c9118031184059072014003074200446842055100c00780c2a1280110000301e00000e480c1801c41d000d000705009a4000103841c041c0031082104007200038074130034081c401303040700703100c400301c4024100301e41121801014070b4a6070000140c18002c9a00d0400030815919060b400a105107006c816809150034541c0c2e9880c0c40e10071900003030004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 182887562 1250 182886312 182886359
    0x1e0b0a0f09210b0f0105150c03070b04050102040f09020c0607081e072001020f041419080a020f0405061f051b03030106020c060708090f04060503010f090b090109150213 74
    0x800b54189400b01c0f41c440000d00d0f120040c0315460040c40300e074440c2d0492102d2058403846c600e50750030950505a10318000c0c900000e0044c00c0a40401c0104441900900112280e450040340425283c801e4041a4016401e0034038141d0300c0000000ca805124020594010030f0004d0049100d000805400690000845901000c10940c02c00445080b0340d5482c11110050403170000c6040c2420700b04c00030400d1060344a1014202500c101c910580d80d503002042004201110218401544d07c3c020781da00c9000c6440d050b40b1411100c841d00e1050b080a00a0500c40e5000801c52814080071611100d013a184110304181040403e0000100003400c0c5611520300e07a502e1001140c4a602d0410024030700070320344000900426052101400007000e81d000d03500d1079001181c010100c210340501240c000c0409a0081e40d0640c200800c0c00321100741a0f100c565500d01810504c8116540d8004445c00c0e07510108004140d1170558050075954003095000e41a00c01c19515117100c1180d07191141c2d82c0c0b0580c503404030303440c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 182888812 1250 182887562 182887619
    0x60105040803190809070315051f0905040b0c070f0609050f01060e010e010b040803160213060e061810050904061b0206011e060906051b0102131e0b0a0f09 68
    0xc40c2c1d90031444c2e199105d54050000c00c0c07818111707640c100d059003d0020003000c0700d4a96010036102c0c9103c0200c4000342500c841040c4206555400345809807006540c140e80075142000401c4200001400312500d03ea04007015054581c859a1441c000304501001540c59000d100d1400103a000d00b80174031001044107480501495051009401c3d416106070320220070180d0410041101082c0130003582d100148081441040322064004200860700c0240e2296000b850403002250024002c540c04e40a074409a40c0e4014018042e40f412220bd0001d48807000e48100c0034200300b00c140790410b41f0b01d910900c201d10218001c1144031180c0000c03455101c2103030158000000501078080c0c0c2540e040d8200e00c1c22805200090b1410402500c8103100f4003d40c02040000504e0040c60740002c901001d440408100031036a803000000201c504036103074025003441d000006040d819140c940d0f000300c41920070032001c86203000c206110944400c16010403800a0140d60280011003d07954450f0f280005010401010b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 182890062 1250 182888812 182888857
    0x80d0204050414060a031e05070609090c0f0813080403050105090d0f0203070c050628020115090509120304050a200108071d01050a110106030f050708031c0203060105040803 76
    0xa4540040340c050050910008200c445d540740094841280d40180b0b241c00d46400e0b100004441c00c000140c003500c58801d510000500340d5200c40440112003c90004000e002da40100c110b5000941030b002c500000c104401144c0607585c0070154050b4144280b20761850b0958a90b170b02403e503401269a40c038030b0b802c2130020381c2d142500080c9041e6030f4061807010703501c0d0082c6943d800c10b500405028160059002003074006001a0107140d100d580317040c841020810480c0b501c0300034084c020702030620340c1c11760a81c03500160a20302c0380185070141d012040035091809000d42c0b94402600000c0040e5224440d40b4010300c08136182140101124a2030480c4481840e800b030009040c80e2800750480c1c0810900c0c421003000039072050040011180d0074a0940d51b11028a00c0c00ca4224441c1400c0081552a1050000402040404150041c0d114500340c40560750744c2c505407510b0303025034460f491800000e071820b540c0b801032a60045500c420305051888c28281c8030091b0038075540080c3c00020550234504080c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 182891312 1250 182890062 182890069
    0x3080405030c0a080304091e05090a0c06090b30100519060206040209091e0609010510081b04090b01091a0906011b0606050d0c0906090515010509010309080d020405 72
    0x5000b103039060380d0a100861034034520b15900e110303501c03c0c50074107650f820701200b07141120240c0d0b6802460003042032200b420805a000d40702c1c40c0100701181c225851440000303a00c0d000311014400c46001c0c51402c0d013418034010086a55001407610003203100c02d00360fa0301002d1000b808609020b03040c4a0f1400c550f0310b0034001803146907034a03a003c0c21130450340640108a0f941d0b0008030180d2007a0f043e10381403a0703501d1340320140d8075008140903014101b1040e40c1114031604000218a03101d420804000c1c17100d6110005281101d80e12030041c110315810000340d035241c8807100c0800d082c00d1074001e030001070400c2154540b44403c003402e801a1034690f4641c44ea00003001030400d00c1c140401c1c0c00300c401ea0030a0421a0010b4613080303800ca40d400c582031200c000141030066035841000201000341c000300d003146403071906210310080b5004e0102d04529059011881c55a54402c0324450040c090b69540c980c004000151641d41005414a04164541c0b10600008203488080c011581c11128090785550030582007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 182892562 1250 182891312 182891323
    0x30f010c051b0115140a15030906140411061b0d090305010e0c0f150c0318130c0e041e1a040e150a02070507090504030c140a0b010e0a0f060308040503 66
    0x203000740e04052013442100743c05140798040b01c20424001380e000440c440070454521603580407504c4601d10403000e000d07160b09a000304071b5242c8280820880a0070318075004c3c03000401907401a210100d51041e050450a001d80103240c20b14407101d40455450283d440241f80112289680000400300c007810010030100b40203440c03c01c0c1542d009003540191102c0402c003008440780c2000d01c04c080401003070a64492420444107151585030a80382d6a03480d180144100034840e10b569030094101004000c009449445055040c696554440c80c0300703221101040b01428000f80307200c929076041d982003ca01d6040e44070b0b0b0701100c0c40c00b2445005401001080004444154040c02115003007809030103000908030342d0641d070040681c400103171943c2c003d0525900e4500c59070800c1c1c5d030a42c42c02c4184800d02d0742151000d0043c130f1103003d4203182d0303501c6107c0150300d40e084000c0c0101040c40000040c0082110020102d6001a641c20002542c000380100001130303403c268410307078400000240601072403e05128 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 182893812 1250 182892562 182892607
    0x1d091207120f08090c040203070509030601120b06031209010c0206040504151e06051902120706060e0a0e1f0e0d0918022a0703021e0102010605010f020c0906030f010c05 74
    0x281100315150000803245c59a00c0d81c10b0480c0b1a603070010000e941580550144c1b1105040982201c04a6071105d00e80001e510f21500190f801c0e00e6680300040c214900080c1340d94032101001921402c00c1005001910162240241260b110301c00303200200721915144a80d420f2100b900160b81400c500d4100402d29100c2a2510300324144079100f02030020359041030403a2140441a841044250b45603a82203080c42a1618280701540300041c2c20710900145400a009a03110f07510040040e4562821410456681c3c0d80c440348103400c1010041c01013918210404040ea002d0400440e411850810560400d1014680e4401080d201d01c3d060203040079401030700c607450302c441c141149020000341d0101c0c0c50b0300c5450b00d8000c03451046c0c601400741840c14004100190390140c03c80180d01c040a02c40c003442031035148590300540ca010400103179980b03e224030b28000c0545d50047c0c564130f90450107018041000a1003282c01d40309841000400880034030448094a09980c0c803251503144140d840800b64403002d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 182895062 1250 182893812 182893817
    0x402031e06030d0903320313120c060302070501090c0b0c1504020303030c0f040e01150206070206010b180102071203030b01080c03072a0c09020903010b09011d091207120f 75
    0x4103c64580b035000070f2210203880e00302c80d00b4403079898201c04010410b02d4680d107203100300c1c05000804c10b80080000281c400030448100300e40c001c1e80c540c03c1182c0c0c600c9403510007806c0317968000d6081140c0d602030750003012544d010320004030300010301e521840041349056000841842001405a00c8000c080c420850205204842501581071540009549000c00307812409845030005d00c2c1c05540a01c607007210024001303801501716541c0c0d1004072202c1c20042d6080304000d4061400081c0302103202184640c1690751043c690350405418160591540c00401c44e0320741980301b10003000c83c40b0b60607050b01c8114280310740d40c081586c9644600050074508050100881150184180144142c200c005032070000314110044040106240580070b40005940c4003402d500100f036004182e041180c1c0041042c10b2040d4024081c8050300c0003031000b00710f82445508400d02e890b180444601151501d140e801c82d0782e00040301c0c001010803045501c141d1064804503074005d00181c0072401c807500704c000344041000a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 182896312 1250 182895062 182895073
    0x1b0503220b061503190c170103081b0d0f18050904060b1f020c01030b040b120a110a03031403060604030212060f0a1a010e0a0909030302032a070f0807020402031e0603 73
    0x400b09840c042105061766220920203100d14032500c01c41203480665004a003081d41e5030700703240f4801d0f88100b442c4c9220a803007030041031040400280c66151440c1554401c00c1a041044003122501c0d005041c8075982604410000740c0c03960341d04d80f00b40c01940140070029540c1c0800c0101320079404440601070800c00035030340303602d090750f004184c6650b54042800c01055260018000600a007018400d1940c0900e690038410500c0344d000803500303400c911500d14400c0d000043c00400c00004410b02c07005000651903c0c403240c00c0e4002601864000c0d0003d44001e040546960005180c03003000e030301c074003040d40c4040701300049500844405a0042590070b42000401e1070701080c0301c6000e11640146040c0000d0503d1031103d611030b109148000c01c5020f078100002c4089140090183d0f10507074904038055002c26229002e4000c91004030900803840c1607581c80c0140c296681d1200308140041902c3e0300074240b014a002d81c9560005500c00c00b002c00b1001803011081c0402300e28041d02070007490103907000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 182897562 1250 182896312 182896321
    0x50307080d050304110607150c030506150c010621120801060818100c0c11030d02031e0c0318031504050618030d180212011b0503220b061503 62
    0x110701038000105929125681e41e46900300410380d12031a050312600601c000911005001d0850100e8410b0b0541d0b28050010760041803085003030722015035a503030f0300407000c0c2e0054401c0c04188005101d400c20800000c03038004c0e6220802c3c01c20800c1d600c05101010100216402000182800750070010264180b019503541001e030028011a4001d149a5481c001c12184560400f002c02c17541c50b40e400f01980610a2101a4a008158850000080300c400c02c0140660b0f0140c640070440c0c94014106600039410301c17191043d001049540900070003009242002006a2000180700620b0400b030008105100340c0091800d0500d003900c01226100c0303840c0b181080c84001607022850030303000400060084003c0b840600894214842c040010400720f103401c40c10000a080c0b82125002e060085072210351082103a81e10b80d0903104005250507140100c0c4042840381c500890240d500b00003082c28010402c8221040c110080000c4401a65400c80e540108009440d0003040b1052000d5103c000c5401d50030f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 182898812 1250 182897562 182897579
    0x2071505190507050c090a061a040302060a08060d081603080109051501030b010306050405100e0601170619030602030702150106030614090612060f0a110903190303020c0102040e010f050307 83
    0x307454103581000b4000485005108040040d6904c4580040c0b2100702d6040284a060060540d482480310700360321100d2814590001c10181c0d803c0781d0300608024600703010f60404403640040100034980c0a6407240c280c07404201004050081a12500d05108003003200382806031545130143e0180b00c02c0d0b401e19080014a050019101040440c217003400b1030aa91a94010382c00b4140541016811502c1c1a0402000c2c12400040317a00300c13440d5005a4a042d12100011210080c0d40d0769044000c00751707080800d6903810190300243d50018108001194551a540c601c0166401078503d400164450350681d000c80c070200b00744500400c11402c4c1003001928180510b0801c501c2e900943e44200c2d200030004610341c03540f64824404c0c49030082030721400d1428207100000d1030f106a904044261070500c5101a80341c140040b20120340b0020300038000c04401c01a0582e40c00d00404048041503000d00003580c0e610700c00d002a101400141007605407940c1042d22040c1d001e030080d40300c280300c1e0348003003010420a035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 182900062 1250 182898812 182898847
    0x307062706150803160b010e0c030408130e0a020304110604080706050d0e07030b04030e0607020901050d050a02120a0203121312110d110f030d0206010501030b0d05070602071505 78
    0x25440000401d08041c090800e45103031640d9403001c3d03094000042e6441d003150300b07660400402c078031400151440d0798a40025010444c1e080768440301100d020004140411001c1e40908060f0010291a045581d12f81090754001c00e03043e9038030b0720f075107402000744010070903451301c03072069204140d0b451030809150a2405542d02c030640f0502080c40710000308a0900135640d000405161903c8007190040350340ca00e0a0500c0000844090300061400940200c061030802c04440e403042d0014080c0c0c1441c1d0a080811801c64130714001107901e440f1b154020310068503080700c244507407400000a00f15000450050505080507044032007000c0030100100c9040c00c220043d00070035a0b81081848400310102c0c540100c2c0648546007a551140d000c00d022020400200c2d4201062182941e40c0424544100141990307220716000401c0581c2004006021551203544160000d400051a6000ba00001c1d21101d003003000781d411444c0140c012200611180c0d1514440d41042d082615142d490504103240b60803091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 182901312 1250 182900062 182900141
    0x515040506090c16020d030807020d0503010303020c06031e090d0f0311071212060305030406110102070201090308090a09060b0406030b09010e010e1308030901061406121b041205030706 81
    0x1d90f02040110380e99803011403107075640d43d02500340c0c0c540745028180900000b030104d422a0061090395174840c00340d80f059060300e040740e506030002c0c100c540c03c0604214041c3c03c010241e4003030341130f00a0b441c4820214112018000c032090000b92503009142c14000700000102207458040c507003044050010188950704803080140c116161000c0e1070304182086030410b4800c5c130303404812400d040b004818050044001d1003205d0b12600e445103030080c05110380c0d090b8040d058010313010580b040c40030030104600000601704610010615140661203c800c8001c841107034020f07a085900100c0e0070b002c601d0301881f0b2241d0034007040f14000420743c500360544001c880d05009003078000400b00040303041c100d561f010301d41c032103544000442e80707a140515520b40200507601c01c130340703c404d500211607001782440001c4a980da5454050104196180d8400000f0003000c400c6121034698108000144a080f0601c0390030414469005155200c4403410420240c0310b2442c00c155601c4016110301500500408603070080c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 182902562 1250 182901312 182901331
    0xb060f0d020901020f10050106031404121d0604140a050604030b01031401020f040311101d240a1d060f04030b070c020a060f03110a020303181906051504050609 70
    0x4500c00d00004030300f81100641e0141c010322882e407242c01b409425800082c160382066400308558801d00200c00f1421005480c06028500000301d048040e40c030480d11850314100b07031140c100002c940308010821070751003503006440700202000c26144034900044100020801290043d041c10300b1520b907006076000610000300303800240c4841d11040f040a4041e24610007200d102c01e0348031030362400c10850403204a129988200003010318400007601501602ca20140101c0b510002c9850314018055039140c49004d00345004403000d070b018507804601c4c000300002c641560f150b000081c88641054020104142160300c200000c0c081c1c440c8483e200000d540490f60401e0b640e00c0e01e034803000c2c0251190a00c2c0e2001075001240c20074049135013034120070356002c40304442d5010015030b1403c0e111004903009450001c80142c1040010443c150780740b10741c154011090000f51520400b8010406000a540c048121406512042004a504103e0303808071440c0c4810b8500344024a00380d00000d010f00b00c0100941b48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 182903812 1250 182902562 182902567
    0x18120f270406030c090e0d02250807060f1e0c0605060f04090c051503130b0c1b0a1703090a0201110307022701050312030c030703180c03060b060f0d02 66
    0x4401030112400d4031800c0038004104080d101d007480070b45640d40f070140c440030500f040c801c40094a800507556041010560291004003110511802c291754480301c00d0350b0708090241c0108440d841071102400501c0c00362110008801c42140207001030b084041c207158503c014000205030303503400420340441c4d2a40603100061a59460000070b5100c1c640e50100c603042442e00a2407002c01910030020002d0310001c44513072600c3c0300702c6001211640300c01c13501c4d442d0360f0308200348080024000800207a0811600705605041155078681b11a849944c0d0440170110760048e0300300c0d0284458502040b080c40140d41119255280c10b022040d40e0b4025050024100549005d07070251146d401d02c00e40e4083c4c0d500801c1c1250700340c2c1044e2400b84041240c0e10900c4003110380000084c030f074a00003510a110341c031010307051070840d600c85c0b0100c091a0001040c500500d91030b4104603060b400c81d41a0a140f03988145c0000300000c4c2181002811a41c0c0b5810050095108210100600e10080e0645020100d85e540169 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 182905062 1250 182903812 182903857
    0x3060406081902041107020a030825031d01090e190e01020403080304021912030804032a060608121e0c03030f040b06010206130210031418120f 63
    0x1801094a03600012050041a80b072001401091003040d8070316008842c01c2c410210180e015005600c41c0e941d009500800001c01000020106c0000d000304120214540114824408820708071818090b821000500e0044404428011060020311091b4080c40c04007200e40c01d090b144002c5040240c040d220100c401c1941c00d020312201d0b0040c8400d0001171000350740b51030b40d03440d000090780c005a408038480e0001016480440c0c2c02d43c403030f85045409011010012002a071410781d03400c0d501900940400c035410001b03441000006440350040c200c138140f007200000e401d040034421190b451300245480c0e0006800600140c800c00300351100c0e0040045100c03004d40101c14203014903c0340c4450781b13000340400301c10000d41d0b507404064144114050b03801034400b0b0742d840c0c004a0b2190011070b440ca1003d01c000b815040981403450b00d01d110101203081c00500d209085202c0741c50810201c03006041c1c84001c1511403040502842401c104442040d040d0f0b0030108441540715040c0102140398040449860108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 182906312 1250 182905062 182905069
    0xa03050603070b04080c09060409030527040903110d090302030c06131706160f0203030a05180a140d021b010507051005010305030706230606160b0c04050406150804080306 75
    0x1100510f10f400c5200c4d640e175030f1030302025100d044041245106607a5000000d007541803600906121035810f9407420301e00302140403c8071613a01c420f804c40880162104072050141c859110f500340a03400303500c602040c0d02050309100c1c03918080c0d901040411600200400040e20001850030303101c4411194184c984004041405d08564240e0001c014034505820854500e04081050b9005001c0704c1561174108041100c01c0c0e810030300c096110001030340108009640b21009511058021004c3c5a540040c5000320f10318500c2c044a1800584031100815001210484100306080d4004071600183c6400304100c80c2920001c41e031070340a581403000018180e004c0100c00c0c0600740c41c0c1c200c000340070881540c607820440d950b504400c1c0b0440300d4600d40a80e2816074a4016032010104a01c0c2507603182c60303078811080c00311304c0c0c0140f002c40200c0c00280000300c000074006943c1e588102c1ca420b089984440c80c103000c200c1139640c3c5034041400c074101d4140d0038189039884000203a101e5001520345a4984900010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 182907562 1250 182906312 182906323
    0x230117030d050f0f1e0703110408060907061d060403141c0f031d0d120b030706120612050a120905060d0219110c120a080f0408010f0b060a03050603 65
    0x1840718003403406042010240c80c80c0007803030042898000a4580b5a00c4d4140e980315114185400c0310b0941003600000c031601d2094016110804240c2400c07030400b996440f0780e07482d01800b9a9105125082208144403130b690103000f401081c2c5200030384086402c00000498094440d41c040035209040a2814610039001006118044c3c842d551520070004101a401803030b0000e180c25a000190900321048004034095826550740603000e406030041040301e80c0181e0b25201120b9605035440c0d22001c00043c43d0303409002e660300501503900e6a00030012682480d03401c990068010108507035691681c2c0001c200c00048010f0300300c1d888844043c070103c801d00140c13000300e440c5d40003a42c0080c000828002041254000d85002c0d4200a12088284004c0005a0300d03056209903000c0c007607000c6a40c000b007a1800c0c8580243c68a900c005641004800752180c071310f250f0017046201031a50000031b04000c40c00e02445208001c19010008001c2019502c00080440c412091400101030b240d00101d28595000e008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 182908812 1250 182907562 182907577
    0xc060a0c0912140f071809110d0212071401020f0d050f0310050a1710051b0f0d020301060905100509090402040203070e04240b03040b01061404080f060a23011703 71
    0x40b59562240385203001c0d950f171800c0c000c400c114080d000f075140b000300c3c4d02d001700c900d03060b8050b03010780e44101b80205000d50041d541e0000d980c0120300800d01500010248070314005000c00311a000c078500280800649010120717142159160f105010a1000756801020741e8403030080c0c00065035480d1103028060b1510240c58216030303440440ca600c0011100001501c4014440b00d4406607012401d200e0908030480c2c000f100c071482d140008031487c01d01442150001c02e4003003041c030081e50402280498090403a0801d030405004106004410f100e5441d05a00c000c0d101112450158a0100e495020506c00b00018000a00981d00400401c0c44680148401c1208550141c8108810010809900f240402c4624103c00148011001103030200f61503007200e110310781010502d1550b91910b44c048441e0100708002c0440c080d03050001003101ca1080c031151941501c90001002c0c0f50905c40e128600312440400270380208040e8090891100000e529024116020201c200114400f18000903056106840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 182910062 1250 182908812 182908853
    0xc05090601020f1204030204060b1908060604120b0105041407020a03030216050d03060e100b1210030804060522060f031e020f03040506070309050717030415050c060a0c0912 76
    0x4151040c1e40c444d4000740041303038000c86013030200b9907940800d241c55101c0d00c241029500c000725500c5400300d0050080d03980200018002e40d2030a0b41c2c0d8801c0303142146036980200c440c0c43c606801041289014080c08094100d810000c034031904202d0700c040e65511030403000905154005c20040e41c5032401e6809000995003040a848500d908000b004008082501509001020500203c0c0c0c955030743c1208a800d0f035090010036454600400c0180610700380060001065030900d900200c00100d21b500908000c14a03034507180e460350903204454044040d010384126000c40410000c12201e035000c0c007c2c000e81e034564140014500d0541d0403800c0d401c100d01c0c660444590000526a02c0307020305030021032041e4010001c0d40e01d5a1100e660031415188070389409090b540c043c00b000d210078111113031100c8900d42400100c030720b0b144d0b80300901a0705c0f81ca2082c004012550200d40180c0b0040d0a000003680840c0300c490400024900e260080c05c40c600c0e60044415503042a03640004201000c400c0301e03000b94420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 182911312 1250 182910062 182910073
    0x11e1116150f02030c070302010804020303160302030d0b010810380a030f0510170705130905010506090610050901030e011505010f0e0f040f18060c020d0207030c05090601020f 77
    0x1801030032070090480540d040007520a00d02480d000b0710100079030b501446040d028144091a58004403884880900240da05020401501c61a090304221111203d40b183c0c0166850381032100341e6504480e03d4071182ca0520203070340308001084030007a14000a4400fa80c0c9048090501745402401c42c8520070302c02540c084400d40741010004520f0094504080183d0341031014400703040181040d00c0c0182c8923840000c2c20f03c1d505101092020b00c4110202c00580e0072150b08a95800000b40260040d140c00e6005a503100c021a06000082c000d407a4818004e607154081401d00a001c03d05d14032503504110704204000c281c11810380c2c466001407030015810030090000c40c0700c41c11040580c074120f118040c0421491a000c841d6140102040c840000008000e0006505c266090002520180e0110340742940d50b01da504030b0314107070700f5501c81d41c03203000b070310000745070003607800044e2825502c2280b4505541c412542000000d9001019809641040c5d84540d115280c0741c2c0181d142c105c003031000e1809400b49 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 182912562 1250 182911312 182911319
    0x9020406090e220f15110306040609060b030103060c0c0506040602030f090d0f050901140309012a05040902071a0910060911091509150c070501050408030d0902061620011e1116 77
    0x1c0c1b6025500a1200b110700304a0303569170310413103411600944100c2c007607010240300401c040f4065501c1401111070a0500000480480d82d40f181040c40072102100c0c0e8039400b05c1800000803d1828069001c0c10078030042c4044d50340041d01074510010791000004014001410307041e030303034483c041103202003042c3c8200c00c4e10f0742090b100840c0a004103040802d8069580c2038039180c8031244011904200095481e020306c3d041c100305505020394411841a6404801c069180082c0b0128000c0d140c45104d003c009042000041e4105105403520359000c0340300326042602002e086949841180e604c4a001c9440c0042c0e0200510b032442280203440020b94414080542c0d0925200c0701d200412000085505407121151102c0040d44c0e01d0080c0c2c041e10510350710501400002c03070300aa002c071101c103000900413801d00381030b11140b88074070300d2041f011034210251641c1040c903280740c0d1201030700000090824a04200e084106400c0c40005940e551b0304000d03a9041d448051041800405a0b00d652168140e07181c0c2e45 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 182913669 1107 182912562 182912591
    0x180b1501140f0f07030c050114010b040506070c080114070212040605070303020a09083f070201080a020706061401110a031e0909020406090e220f15 65
    0x14003000f1610589081401402846109540c0c88515038190720741142940d0305004000c001e484e240700140b00301d00c240b006035016100180c41d4141c4440040c00c10441d040740355800082654a030160720104005480040ca2150303202d0b03004c075000d6050b900044142c0744946c1c0b107103400190041c012480000d11a400600c03101c10a4544894015140d46401c1d041102c9070300c012007201d40030340f444100415103502c40c032600f1540d0350840029429546d064800b0340309030300d8000d040010300c42c00900d110301c060781501d652a40282007000210f072103d00100e5000c0c2031072510341c040740944104400304c040018100c9040c6505541310030081030f01d4a102080d020814540c0400d0000914001c07920309180c1c0b0161006221542da5401414a81203402d01c2070017003e403000200b400101c40c1c444440e2081f00c0342082296102d4118009444c9505020030070501010343c0c1030005003400c64203140c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 182733812 182913669 := by
  have h0 := BRFrame.cov_init 182733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 182733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 182733812 ≤ n) (h2 : n < 182913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
