-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2839
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:34.207999+00:00
-- url     : https://prove2.me/submissions/ea17e190-cac5-4fc9-9404-155935268f45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510431654 ≤ n < 510611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510432904 1250 510431654 510431683
    0x809040c17160f260903040f03080304061b1707050d09111f0c031b15020c1c0c08071406010609063f380f0a050909121803 54
    0x10360000701858000001511405603402c0d80044e5919918030303c500b5032140c2d600910410051980200c1030006500085014074440c01e000c110522032510042809451088200c003c5990083c44400c095408416154004e0081c0741403881c05000c0c410b440100c407034502080d9400e078500e0400343c0351401d1580c100c00304201c0d0785d07030030324a040c00d0b0243c002c002a0318100000c0070010859282141626401c4052070351a902c90800340c01300300d007110b2a5001390009440e03483c080c40b6141c02e020b02c070f40c40840826401c1090380d817040091500758403000280d81c848034003200ca5050603041441100d5003404458043c020b642e07075036140280b07440001040300c440182d40c820b02150291708000c1c414099103026680d8054282000380100c0320603002001060105408460a403c81e6a110144820702e40d601e20030144441071041e08880000a110340c2209090318a90050281c03041400345141c400520342c0d000041404890040201040391992364100d1034051050a1941d0b0708142c0c1031070180429030b40c84010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510434154 1250 510432904 510432917
    0x3060b03030c061602030702131b09030503031b09120a290f040609021905041401050d0318031403070b0a021207050f071a010f0605070809040c17160f 66
    0x42c01903242c603480c0242c406a0004001180e00f034455009009594401e90000e03c00c0c4203142006c43e0000c054507800e80da000c1d21039013800b0910350040c080d209403000c0d0f0303030410021400e50795191062440700c00ca01401c5d41150b082840016a075a07a0b40c401c021810090001920411009183c9029400d030644218503c0700d1410b02e00c042c40e98550030000f503001c02d2000308060300c1e40351414000020420f01401039080040380304291000484034440c5001c9171410740d000c00440070411150941c4100030700816600140c0d180800f0f000c24864801e030852650742e0101c80d002c0765501d43d00c80710200e00071840c60984e0741002c1058424000000d50195100c0503074401036140c10081c01c0e003442e10310001854a0305010020500d03080340b44072041640d8050780d10200744110103606800d0305074690000d200f8241407040340180855210710030019280701c80d1340820940e041152000401015041400c036580801c2401c4c9540840103400711400f9018000c034a8414500d4a450f00c8001c0411074804000701c180503e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510435404 1250 510434154 510434167
    0x503030c100c0909020a021b010212040306020d020906070606080114070c020108090321010510020c061602130f0b04050a060501170c042d0509150d060e030c0703060b0303 75
    0x40204450200445110300000e20618503001910840f100c0d40029488901c042102402a43c002607610f0050503002e80c0e03100e0003603621340120b0360740d2003c50038170100c4c50040c082080013417039903009012110300464002d800e2004100c045030b80b941004200391821500c9420401000e5400c1c81500300c4841d100c1c107003032510325001703101506202e00214001c5c1000308010000351501d109000791003000c2100c110040070108401a62505103100f0300502d480744400c0020121803500020301d0301041500580024140b0710060950881c1000c01e0400340d0700b00b05a0010f1500103000303032003552080c4200e120001038000f0782e5020b0104441c00182111030700da1808100303110036030300400a800d90001425182180b0340d250a00d04845018039800481e078176000c14054200b2018108107000b90741c0420002608031940c6a00300031030641c00707450a541107001e00080400c1d50500a0040288a00070344020402d0311094503028038690004034080361070340040740180b08000c420b0140d042a903070110019400d000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510436654 1250 510435404 510435427
    0x801061403060f0d080a030603030e06130e15061201061d03100207140a1101171b1b1204090606050c150919061a1207060305130c030807020a050303 65
    0x1c405060b0900c070380c120b003508485940e100ba407564100ca03400122261100c1110340701a0142066010445c0441d0900c0000c0d000d07800c103c0b0595001034004076070400301ca8030700107130902d0340c2001810b07076a40412200404481a01d404005140072450165a8806985003080090212440402d0144111600d04800d402551300142d29082000100d60042c2d8521492800d0748840202900300000350089440400034082e0141b01150745040a032039185020311780c0d400e681210039045403641c08003d00c000104082c21420000340c2025403541c0030750350088440184a5251000760300b0405100800003c00b13003c21b010034041c0000070100c4d410000e040c6414501030640701c1004100340005280401c0c001200041d08000001c103483d1504144440c0311024240007001d022441e8660004e110f0700032800403e414020403840b4100910b0340900002400c01e40110090b05000d84204045025400420082144202410021407203460a169117940d44d2043c8450340310710390300c1a842904180003442c05103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510437904 1250 510436654 510436657
    0x170c031e07030f0324120201030b0603091207060e0114070914010c0624080a03020618060612010f0e010f0f060b180307091a0f0307060f080a02160f0308010614 70
    0x58040d802c010403240c03060500c214910784084450b40140170746080001d801c48074034400c240d2980c000ea80c2441000c02c92818400c0d6880107507a10308265000b00609214114030b40090304449110741004603090b610075440c0d03425a4125102012510300f03200134040040d4112650b20014891203c054032045111000600342118100300074080a07103403049024404141c0d1007640351100b5090540b042c490300c489143c1d0b501c441c01242100503200c5c00012a015059190055008c6072940e80200281d07070b02c213170074040b12240c084101001c540d00c5070801c100800650040481e10412000001110016508282e0585881103802007a0518040d028042c009200040f180c00744801c4c291101c0e0540c054010a140a0580e4020506c651034241841c0c071021010b0032403001c01b00c084549085600680b02010b449144520030080420f1a820000c0e079031314000d410301940404000380040c184144103c1c80c803520460001e04480001401c11003d04258101440e140941007034a00071030b402c1280c01114119 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510439154 1250 510437904 510437927
    0x21005182b0302070807020d0b010e090106030c05102a030810150c080702090a050a0c0305191802060c031b07050f010c0f0c08011b0e030316170c031e0703 68
    0x405800192150a001640044428040d8060543d00d46c123020750410310365030003081c00b490209100d0003011070780703c5005001d070f1001e403130704509842d07a4582f030030f0100001400301842c400240041484d80542803000c03496180c2c0903c107100c01220400b06a80790080503110b00520b116400300006009009154003032103125581d0801e403d102050041c5c0381002c005034024400003e500a41d1081008607805840d0000784c00350040540500001c0c6202e4020b40544400311100030b2a440170088480d142000c036040400e0703c007107146041d94508855004140d9550011850b07180c5584005042c80040d21105101900340c00007401a102207401d001c00030b00301c4203110380c02a04214542e1345210078001c0414200c035400f42d205010808159480c006e0741d01a20030300f00011401c1d05d80c0d81d040c40c2c4540c01180d58440600000740a10301e0600020500480002d1403070081e1502000010b81c6c84469440308001e200a002c039000458440b0000120440121107202108075010028410000000c1c0c00405080c0b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510440404 1250 510439154 510439157
    0x3112b08090a08070f1e0c050d050a26040e06120703030c020d0c09020a0216050102031602100302070f0b10050d020112050711030a050319020c100b01021005182b 71
    0x3d80d04c0c49401c0142c080000410040c004425241c5290791403040c80d40b8061b800740c0f00d10f040d086038a07611400c020310842e40d440301034120b42000d0b030244001200341001000018555402c0303500f01c101c000310303010b25410540000c5030314820703901030003918a00040c00b1003032a10005c000307003500c50070f542d0010202c3c6601e441c02800b502e07022490340100700d28030b4228400340c000c08108546905001e00000d40c0c0305400c45458161002420380800d55510100072125600d000d2000781c130800501da401c0c04522560303014031500f0103074240a800002443d070380c59110800d00420518146003007440414503018142c0e408180320300307291001c110050740c0028020781111409540012140d513400d2040e07503100b00c075541c4c101c501d00000801100c0103030040043c500a40224144900c60403106801004903c65401c0075a2039910040e0004600b00ca143c0105598281c1803040c0c84866100d265020140e60007a6940e40308000c0d01d00c0c0d00ca00142d820080c80508105400c252000c1c1488880b0400e0100350741d0704080c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510441654 1250 510440404 510440407
    0x8100507030b0913210e190b1303051006030308040803130c18050604020304020307150509040f05091005040b220206070803010e1008030f0703112b08090a08 69
    0x4005500070790061502c01e1015001c40041d01d001d0314007821040d086041281c9075065001c1c0201042c1d40b0b200b0100d214030850b119501d0b9000580208030750032446410038403203503403c2400400e03410001c40c0034141c04203c0540c0d8001c1c0505500e002801c01e030820308000c200900c1c00c001000400c0d07024520036001354100e505265262285461150111250030b0040c00c0031185580010b1040307614122400b10400800c2d041055450b80c40c104802e910058501952580c401d801c04d2208250010700c0000c1d03100142442072501280902140c03e9585000300d0a288554440c100441c0100174088554480c109880402c502d14007541c650940100150080010704012030320310105041d11005405e080b0340003000180c40e010b0720700c0c01c04159802401a4101113000d0720102c0c4e40c4200d44c05050b02680c0003403019600309a0700c2107011078a41c11003039055040000a4401c049140028400142e10b0080c0c61714514010300c07040e0080c0c0e508a5110b610301c082108070300420200103030104c2c4210810340d0010420703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510442904 1250 510441654 510441661
    0x63606030c040905030a120b030303010603111b011d0a03120f02040e040f02010230030a020d0e0106050906010903020616021906020d180602030912120a020307110a081005 75
    0x181c60080d40d185a590024600003c90003480000006401186c02650307826041d0007019032400191855046030b217415910a00042c8891806904011003c1c0000c10721141003200c191302500400c001003004a81a9569540d0350b4404184103d50441a1100303900404404056070740040c25900d0f41c100c0304019582d50f800281c003194454040310010302aa0f0b400b16041d082030f05210b259005030710022130240c0308149090307144102d5490518541020419080c103290344285400039590700c01084803403030960070044081208043d204101040081100005082d402c14051101002015081074140b046500342000180e40d9141100c00d0302006c49407581d644d4000703102144204408006103c00104140306c08140703503038001200030100d2007a54900400e00c0c1c003840718180c40d40c03487c012540141c1042101e40d0721030500300c4890300b0801028044800c1d0542e02560344805403c2070819000680000070742e0300510ac0302449514000e14100c8003e05000c1c07078042000e945200c0612418081601d50000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510444154 1250 510442904 510442909
    0x203010608011505040501050901180903020109022106070201020c07090f0b0a0b0304110d021e010e040e0705040b1c032604080307080a05042d061103063606 69
    0x803400424501009000070301541000d200d04203034902030580580d10300400000c203880c0c5400300750304070303481c01c5620112038040002000207058103146c2a0150764132100c2d00401602c0e094181010b241400401c00c0c4842040a031982c100000a001c110443e8010b2002d1500342e040411a40c1c03c441071034800051403074006000d44080c1070191025640141140c50000300070280e40c00441c405c91080e020b070101d0646110802c10f00702d040301b9003c1e4006071280d881140c541d1104610003d140c00505280c1640700c5008009410798141117652802600059020030482c2001d0050001182040f41c40345200050086051005250005c0c06401c21594020741c0000c030000115201c000b0328491069030171441c0c181041c0d01e01e5481641c000e80007861410014840e0801d620440d80540e522901c074000e00c0007070f05504644610101c81030810040310380410000200c0a03c0344075118513030703c01c0040c1c503803401c50200811401203007181c512003014182002e20380c4490303410061402c2000d6040c1c0803292070701d801 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510445404 1250 510444154 510444161
    0xe01051e030103050c13020a0503060f0607060c11070605210c0c0109120807030515040518010906091406041e03090528150203030610170411150f09010c020301 70
    0x9030100c40400000070041c0300c07002c00d50307092210055440d41903103a07510300100124460000e90900140e0240046046844e08075504202168001d02c218107000498460404880300c5600650204104050300094504203200b00001400c00e818483d0904a40104401c100c9003681c4000820410f03110000349040c2d80f940585410785140002041031080c14034103441c07150703112054040070400a50008901d14400e00034140305070500c48007224841c4083c0d00307110141c00d010300648601400301810708000c0c2d02c2407244100c114050705010402d210281002800200c3d1301c00a0601c9810003010080858100042c9400e140d1030380c00390340d103209181d0404860384003a98100951040074800c07181d04040c001c6145081d400000750040c034015983c0c402404400e010300c29408096007062002a50340c0c609184c8494822081c3d0a044070390810f028a030204408046804a030360b00b05d40c056040c01410300502c0d41c80255030900081d031504410041c2d0025034091041c0890410460040801c1152820b42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510446654 1250 510445404 510445447
    0x80d09140a05011401050a120215160f11011403010303080c0f04080d030501080f0d08060d08040e01060f090f05060703020f0d0905150909011a090306250e010e0105 72
    0x82911100801c615040b070203444c40704a80c0742c44140c50800441d1a19181101e0802c032200280f02503084a1181e0074010302c10410308180b1a00c0e0004d1000840d49a1220300142001c0e00c14000d081d0614038510704000300e00c036012003180c1000b00c042d0011221042c40412607041d0394250800c0340d40360303990340c0c0c410071648202e049021000340302080000b444000065006213060309601c00b0302aaa0b01c07050090b681d80c040d1041e409850340300300c0031840050300a851498200002803c00b440701c0c003254070f0344401548142c1c0b1880d0a1a81c001c01041400d50140400c0810b10040c03420b0a55240361580708610740050303000b02c030310030140001d0400400d402008503603031001124041d103010003c03030180500320200d0b42c820075014400d00300c02c20070034448910840b44269001004100705908060b8502a40c60782540c07004148101000803031285e5500b081032a2040d005072041c1c8484003001345d46d001200710140d04001c144660b0070310466240e80c110707410400a01c820310300151540c0b0000c007044c242c0d035041c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510447904 1250 510446654 510446693
    0x10909080421051c03140405100b0301110f1306080c03070806060c0607030b0111030309071214030d0204050414070909020d140907060908060702101805010f0b040605040207080d09 79
    0x30700300c0b84524444c40038070b110f1400e4182c60811690820140c0c4030740403001210001e215801040c410180041140d1101c0c601d081e000c2c000103240c0c00c0382d0485541d01c7e400000518039294020601c8400350300c494500381c019262501d4090780600b009103603550180800750500c0b041c001d9402c005400b68803600180d90780c0b61140800c48041d42081d0724080c00802c800c1d00300301e000651040311030400040c004101c0c2e000b0500080185085e5107001800c01c4034410248040b00c181ca9102c1444000f4101000540744410030002c00594441c601400c01046482846040041d010040108100b40350003c100c00100c1d01e85d80c0f80580c6d181c0c0c0e086028001070100303402d011501ca40c584107004200c4000a00081680d40c180c5669041d41d498251143d07032000c01b200c9070401030b0b00162031100d52401d070f90401c80c1361860800e81401507003490754400c0d003907940840440700001e40d80c4032a20390b07078545402040010f00c01940c0c1145001e81c2c549401c192072041d60070711460a5140ca150b80104100c9001d6110b06030101e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510449154 1250 510447904 510447913
    0x150f140d240e0c0303091905030d11010c03060602060f06120a05011a030703020a1512020309030702040614100305060a090e0312060f1f11120c0601090908042105 71
    0x4a220242074041c050180352a8289810700c1c804401c03500040d00207502d00010011424000d11100b04480c60000c41c0c12940c840c94980000103150320100902c0c41c20341d225485d450150300c040314000c2d0840321b007030b4050b504240c00c25508012458000c214150403020b180c80d01c8015603241c0000c900e12550800c400c001ca0700c104195841030000c1035008001010161080d200110603403010156200168080658800c5090b01c04010780045040c654018540904011140b0b04840b0681001c80c0c1049030600383e5a0400a901401c5103490721400c0080c04074050702103207400000b8042081248100d903140c00b03141e071700c20114645584103d0b001c00100580c95042c400704121503207941d00e0b90400004008a03034000b501041c807070318140000100c002006088000300450040268002e0641c1ea14031a0501141c501c280d00ca194084c00500040030548856035902c0c051451000d150690590080e2219440c040d107807030000700e10400311004c450410882c0c04109004a1100031245061003008166109 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510450404 1250 510449154 510449183
    0x20a03150b1804060b0301051309020310091505070504060c050a0b040606030b0a090302060705210907050a060314270114060f0f09160c02090c0d150f140d 68
    0x75030000500526215940803060540c1070002d00c4207903911402044600c0400380010300c0079041010110642040e0040041038a07003250b008242006081450078855680720024001804403201c880003103e507000d003003042645004d920081243c010350050404210b0784000e80c4003800810008280e000d40c002040100608040c90200000c0c503041c40101d80000c4803d0000b40072801c1449014040c0c1c0d0940c0290899613039004003214668010b9520710140c1b80c840507429032145544141c24440d44c200402080030710300740001c20800721282d9000d2000c060908c42a032050f611440b0000d07030852100c3d2a070104a508281c07401b1401a0030002c0083c0540c40d14901414282c41c01d11058050303501078882095a01c0d8810600224000f14602503030445505804a540300c024007641807a501460710300300e84503524507070003e41034440c1501da034030503c0008200c01419241030b1050311a50100020703564100b80ca403496030300c98406280318a54981c041c890b502c1c003d90300c1d400301c4005802d9110707440d0b2030140c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510451654 1250 510450404 510450419
    0x203130e0711030f03010608041e030c0213021806090114031f15081515070f1a1e0c12041a0a0614041a040e0609250603020a0315 57
    0x940460703107940080d0b6140c501e01600ca030301004541c1160f100300ca82e145141c0c241712046d42c4000000d80104c91418001c03042c180c0043e88040c1210502d4440d6440610070305140c0100450f480034440f5502c0003e104000032000301c4107079001d280e0180802da44483c0c0700c41c000c00040c2c8400030035030300c00c0c00151000401c203d0404065101800440d211412141c04582c451030108842c032070071070065010070007110210309218070303401070240c05450090103000d43e58040c03a030700300c1d6039007207200300f160154207848009040011040d00a040111000d900c1f6581d840d003141c05180a81d840946008502c001c50003040041c85080300b111092800c0004a401508051030442c90481d80b801c0da046c00b140811021800c4a4070034024141140c0000b030409603607900290402004218090500c05101c419440e840720544482c01746600410b004c0000e4040f84c0340048146050001c1701c03101d942002c1020441065805243c800c003010f5a5031490016190b0000200980c001e201036807007003440003240c01c0c0014918 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510452904 1250 510451654 510451679
    0x2102030f0a05160b0d0207150c17010e040c0509090a050a0b0a151a0901030e0610080706050a1707180305070603060909051005090712060507080c070506011401020313 73
    0x31441202119030050b0f03848181190707800140100301c00310b881000700b0b43c0610780503000b8210440c02103648640149145070340c2c0707044032030720700174400410001000148206075030760100c1e00400240c0001d071614546540c41c001d4840d81790089038440c148000200380c60040400901083c250b02c407040320b001092500301895003007001c40d80c01c03c0701406c0244440041d9202003d11084801058881040a0050034102081d8020107140740c101a6a4a81d904a12504016190003101d13402c103070300c58482c1401c80080c140081c50f00102c042c460108980c00c2159400344000d00001e026003080071203500c8900d0100c610144011820381c03034100800c80030046c00000308400040307c41c103407800c12075130366910080019680d80c90301c003070026000030910a0500c030482e0081c903802000d01c000e071541d20b900c4402082500ca1094400e441890391081002082904440015048020900102e080c007045554441d5034200500401c05030400c0516a050164004c07c01e03100c003480c5410311450083d80741c106500d8079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510454154 1250 510452904 510452923
    0x909030507170702010903020919052a0f030f04060618050f072d02030c0f0c010e420d0e120403030203030705030702031309020309070608102102030f 66
    0x264411a107103942e01ca81d4100880e100d580c0e06840d100c1b480c0703186800300114220300402c0003500300c0003c1e1148120b400144265031243c00000d44c043c02c00c0310102003000240910000392a0340003000c21a80c0f94420481094950004119210300178968491500d10f0142c00035500a41d82c250300b40b004082c9111064018520034280b031f04441485a651040c11145020351000750750340e0a02c1c40e56004440c45040845894a0803e801181d00e002000b841c81f40c941020990014801d40106001d5800366034800040c0300782c5201210800101503040741480c0d07420650400d0581a00070302808480408041c40f90f6101254440c8807081d00d41c5000e0103600003078808030301049114080d03126900c04c1020940c08cd03500342ca415070b00550444c0c2c0c40a034240c819500151001d01548003c2c0454100d00d00d921700910040c25980d40d0240e1a030810505a03443d20b10346401003400d0200c200c0400041403003c4072048101c5961085242541c3c0c00038200482040011070040e4150141c404081c0d108032002070304222 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510455404 1250 510454154 510454163
    0x17010806070806030712061d0d05070b090c0108060f0103240e0124110a0b0c180102010c050d0c051215030706020105040c060e01050c0105010608010501090b1c0203100909030507 78
    0x3070b95120020135440314954042ca42202e06500f241e50013151890340041582940250913041c01036071101c24510f0100a1000d500c00281d000880508010709107000d2600030591070018600d04c0d00c2c80001a1003460000c1050b40150041c0040d20150386c070a07041045d40505c90107601030b80c4a241034058411480c0c030f01507201d54100000000500a024404041052150f8984d0250031341d50a1000c4440f154122900701c0d0301e204286035200400d143d0500280180a01510255180340c0d41c44164081d000d541c2e122410340e498000c04140c0c0c10380080843d04400c0080f00009120710280d070341a070b06800385c941c200c012002d01d4010007500744000c0b26040e00a000c12001c0744c8289030313540b02c203d00341e80c8100c5000344558001a0100f00c81c5001c0c4c1200309081030141415401d0509440586084810907400100080c10400041040356041340640e8007800c03c903038000c1d06d8000d04001c502e0200d40e40141e030a8420ba800030010b03146034003820210000d00b80a000c2403040c0b1019042c01441504030307080a54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510456654 1250 510455404 510455417
    0xd30092a0509270d090e04021302130b0a030f1415040f0e060c0a0206012306032d0f070c030c080a090b190e0d0b400c0501050705030d0b011701080607 66
    0xc242d6540200c080c4629402020f440750303034142542702c101a402034501012604400540421304851080c060003210b0362640d0005524a031460040e4140c68040d400041400b444000340300c540d02c520800001220810b1740c0115003c184e4480e00e000402c00002551918050401408a2420440000c0903074040c00d84c02c640850340c881815148214a0f1144908901d0786120410103900384a0040e541c0b141410704421902d80e0042e00d07c0c460070502d08245104a0000010842076403000c4120580194051819002d47c50040e82d0246c1009400400074083d204041041c844c40d520494040000d0581c441e107041c0c46038118090803400c502c8c0c0204205c0440e040b1600c0c190941440e000e12504140c01c01b54040c86a16003003190640001c4110b40100360751003410107090020180a802061100c1d0080c56124145103410a248041c1242d04098108a0100000c0007ca80c0010130399100748c14203000040c21180d24001a180501c0e603a4a052038036528200016001c040030030801e00c1290240c0b240d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510457904 1250 510456654 510456659
    0x10c17090601050120070e070c05010e0705030a020909160806011d1b090d0206041401030b100801031b1d1906080d30092a0509270d09 59
    0xe5031210002d02a00740024103041c116051042e901c0002c9858070701c410151004551030b09840310180c00e084803d08007080340c5022030420403809204001c40c001441b0040c00101d4140700010383c640240c042c0107480f5080e4000030500700034050002807080d4002e003090b045000d98a001203600c2c4c0e842441100a0b092207041520b210004c10340d8003c1c45166074408480e11006000a44032042c0c00040f4000e4001004480920050f140e21000340045c00403280280b03c8440700d030b0001000d0ba10040303545405518501400000541c01c0781e819815242d00599101c81c025005105c5941080580d21103904001220307140c541a9040103881c40c0203c54000124031070b22103003014803096034644d10a41499600a01700c10100b01e03c0354903003010907020714070029034081061804485442d110141c00c0c036210343d680d0407030040001d80c100c409016920701d20100c03502440c1507081000a60180304082c0140302c0900001d405007044d10001500000111b04480c50b81c0810950702d5a07104008081c50114496a002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510459154 1250 510457904 510457921
    0x6020a050d140901120b0310061e0f0317071a01210b070f210c02010b1c0201050706020d02070f0203060a1116020d020604120c09020c1504080c010c17 66
    0x4808000000501249000f9a00004540300f031000114640e1031035036080c400790f03555400d0041c84010049480049601828944050742c8100d411202040203000c036001040012030b4805440700300c0340c0002491071441c080e51071502c0f0a01c54080010000b03401b135500e400146019034503c40c16200d5480301000c06580c0b10316844240b0840c003101809158143c1c00040446121341083c54110340315140040c030351042040c402ea0001500790304402c0b0715444100380c42550350f0910070401500800c8500c071003500000b141d5500341546039034002e41001000998041448000d40495284e8441658219074461140c10030504a90058030102d00ca0300a403404030f4060100c1d400703074440003034404c0c0640c1d20f49011810010074402e0305840c00c9811245040c80a40580d440d0400350004002c140d4070400100c41c545801700300c040c1ca5800c0800d410384140501101c081700020301300b100b0a1400c4c81e050303041e00c80b818021170318000d2404402d05503007405e40944046600203010004824000001d183c607480b007030310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510460404 1250 510459154 510459167
    0x70f0c020d020f0a06120c0f050318190f050607091a070219030503030f0f070e041d070e0f09010213030b0709051309030215220f061104170706020309270106020a050d 73
    0x800c000027841c144041054100350200072245030022000311020303038461310f80c50180010840340a40c4c000c460501041d050020034400c0a602c844546001c040040c1003183d8081e14032940200783e80316030b01c0801d094085448030314a0031304101540c201c100724036035285805942d03584121481645203280302c1c00b007503840c00c0c0204007a008903090381b00c0c4690041c1500c140300003081c0308001010518100c03d0030701d500c40700c1840414085c0000e20746e4507810f4a4a0390700041043c50280010f820f5a03c1001444280c07a00740400381e06507540403482043c9034465200c02c5914071499008190b01010644416507045020f42c843c09040e4840e4084e0f400000c40040c600103490021200c0d040d1400f110721440500310b0032100c9510040384a4107604400c40c4840d00c82e6012039502450a000c01c1c040002d00b80980014081c01c80380030442c0c0d1004015990625500945902805c14081e0003030101c003055207603095040511101d02040f680b0031400da5039407024000e55504c0f50030320650303040c01b07031050081d041440b801c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 510461654 1250 510460404 510460427
    0x215040f050129040c0c0b0c040f080a152a02010614010c1106070302030c060103051b030a03170903090d06090314030103031403040807020409050a0b070f0c020d020f0a06120c 77
    0x80d00700d05181d800d81840040c05c0b4600d00f80c02048184840080001e003102c802c14001c1003032800752134071a420007803180f0b807182054201c0d148580c4010082c10010308100461400d000c2c100201207134003101e51400748404403540c00e0a03a00b0712036200441107041d82c150721147c02c03101554880036500300250f006689442401c40d0107442400c03000c030b55244a080100c0104100352103841201c3c07606d030031801030341e05202080c0c00031126a0044e003544407074083c0c0342000812550040b40580351841300d07a600a8914108d01c001101c06540403400112405800e0065443c46840034110791a141e00034901000200030118049021984041c200d03d5000009001d0340c0c140c81d859101e04104130400301c21203210f500000c20482c0c4c1e10804203c2074006850b24054a60707428031410003071141982c5481d106180c010003c03d0042001442c041503d00303d5030044c07660706044e406451050030741030140089840e1000c0144c100741c120301c42c81400141140c1c403100a01c440e001c2010100300c4000644000c54203881c0c0302 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 510462904 1250 510461654 510461711
    0x70f05040b0909040317040b010312030e0c041d070803030a0614060412060207120c110102010516080a020c0102160c0849031a030d08070f0215040f0501 67
    0x180102450b50610303211054200b40039041c109424184400d02040040b03040360116614201180104100702132a9003188220101e41024440b040c07030300f52620b590382c40300c7d8100b510441d1034211820042002c0c80454103690305000a40d4000c60b00c400465690b60b0049d6070094a0710714103400003d250507010a49980a07000400305071800e45088590041c0010383c1500b941d080742c0c2017041000049001c2d200f010000300f1500c410300f062403a818280001d07020010b90605690601c401c003c44240301c1d000602460026080104450701c48141c42ca00902076034104d00200e610008000c03503549824003140c151300d4400c11034106c50a4440303812300d03140c2103651440d103040c4811a0ba580400d2102c103803180b0b243d04020b803070b11803003001c10725101215000b480344503404070303075901e601c6c11034107030401640000480182d00814641c48034400c002d0818034010b08600030032010086001c80c142c070a00041c2c0d0f5000d0202c00070030035800d290a0240da13050b42032504451a6180c03ca110b82600342250031194824100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 510464154 1250 510462904 510462907
    0x60906090144010c09050609040c020a050304060201320f0403231305090903120723040f170a02061e041805011a03130611070605070f05040b 62
    0xa0044140d40981e0006944101003080c0142c0c020300340444421810215000440d030160341da194218030308603200101114100442d848040c400c2c0e48030380040701c40b841320990b070000d90705c0c1010300124144600194014000c0c00300090014002ea41504408104000c12107030385180b00c00d07070742d4801c0f461254142600d09a00c034400000c0d0840d0221006952082c000c0c204185008544494010b000025044595848101080c01d126114111000402034402501c1c1c4d40d05901b000700c6150350724000e05101d441c0c840724040016070311a2180b41a9541d44465007080445102c2d1010540c2064010340950305c1d40c440311000000d02610300d010700c140601441c8001d491044829024441c15920042d1000306d085d82814204d145c125094009100400060444208a0984850030b40580300103a1221040c0c50540500010078401b200499400980c00050904407002d80c2c540f20703028000a1501c3c802224002c143c040c1032061541042d486101d440d51303204607411140c0800d03210760090f402a121500c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 510465404 1250 510464154 510464159
    0xc1801210c0903120306060801080f030f070f02030a260426030f04141206010503070905041a0a15050a061211160f030f03023a11040e0609060901 64
    0x159441201c1c00040c0d490b000d6040b5031a034860520103104e25415000096a44004020031944034954602510b0f0840103025079000c01441c032540c0b802080808019454001414400c002010403e01c002c180d0290a480c1140c0742800d1640124032070702c20140151484000042e140c40800307080b6000d441c1c08619555403d981c0940c6c00c10310380440d030100725052000f00b100c980c2080300c03a00030380001c0c40d20720040c6400001c064140042001c103104500b07002d03882400148142ea4020440ca01030fa8000c071400a180c0d500c601302040180c0764900c10403d551240303810304c5038113405034103d00c0160b100451050042950780e001e0010340c4d0f80c030b44103940c0021441400c0720302040703003500040d009044190340702c0d0502e142504090b6228004150464103890504040820540c1000440304035000e941411404c05002c031518010741d030003044205445900d2141001c2c5541220311960b84003484001c030402000301300c11240d14070396105004004105407018005522884c1c5082418401c80000c0c102c00e45c16407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 510466654 1250 510465404 510465467
    0x170a0906060b0307034713270b01060c060f02130311032a04060317090a0e010501020d0f0309060f0f06050618010807090305160608060108150906010210050c1801 71
    0xe141080540410355010444001555051000081d21104d0b5900040f0707400100c1181c03008004030002c503071140f8903048c242004a5500702160307045449a00380328080c19280d12300b640c0148001e4204c0c2d20b40c54408142c0710200002d140c0e90000392407103208004102048541003540e035448801507400e44102c1200160302c00044030390304c400800d07030281c8041303040c3d61030303582c1c01c5000181410740c5011020042007a15041c500204144000d140300000001c081d410000002d407100700c0404000c1c103204e01d000d810308940b446648401e5040380c0004042203110780706a00400a048148454140c05003800c4c400b140506d05070080301c0d180310a0294584942201c8001580c035803400801000078003440c0c2e01c0c0000031480c00e04c4550042005120700000040c00c1c228050000f94003d041d49042140b241e00704610300c1d00380110902e4206040301d80c3c50341c40d611203004034584285003084d5020141071409014403005145c000e461400021000221580408001110300c03482e04490200c42c01d03e42e144201451 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 510467904 1250 510466654 510466751
    0xa150302150c0a05060603120a090e0c0f2208010c02060a0b031507020102071a040803041704050d081e07020105030f0735010b030601170a0906060b030703 68
    0x104948841d60401c0d0514603010b0400301c03102d07004d0b1816000041008013625090002c0400410300b00840780c01d1200c1204000c0c51b00c0841c4c0580a0250a08408100b0404d40c0c813081d1900402042c03039141d600d0b038000c001140038400c007401d02c4042e50010b120200700ba42c810700580040400683c010402c2c0d40e5084d40301805050540115a094020881d00740d08032195070511503c036503415000903a60301024602071032100103a03481c8000e18402081070100141500302204d401c690449031118040e01d100b40d603616244a141d101d254807501841c1020204041880540b148020701d1102000281461003a040e0910620307038001d00060b41000006c0007243c0964959800c0078143c40c00d0341c1000b00e00c40240c041480900b41038103146c0c92151450803102e1400358154050701d9004501401c42c180071001038060508980c0701c0c1c074081c03281d00000c0c0f03140c400e070f40c000f121907a00044240b100650310310b10703500d80e61300688503880020f00780842e40d29034080000080508105010400d000910122644d0070341 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 510469154 1250 510467904 510467929
    0x21515060904060b03010303051c060b0a05090307150f11010c020a080d060810091e051b2701080706020c03070e1e191416030930080a150302 62
    0x20340d00c050214055003041302960103103200e61a19941c1b0812444c80358609070881c1d880d88262801e2003014445020301c08162480340e10740d403c02a884150b1000001d040130000d0308010320f280a007222100d0159480030350110180050384807900f0104c4d01a1503117003664000401c21015074003035810000020320fa0002804114508500050216101e01c20107007450400201950720b2030b11640d54006108100c0581c0460980c1d26030301094088039961400d480380c03020011440050252443d500c0903480704807400d80340c118042d0030b4030b02d0899482d01e20001c80c2e0003801400c5951003164004100e06000040b0040c0c189401002042c041d0302e000c0e2451000320000b061540c8a07682889402040d101d801081401503104c000c84882c1d401d42e41d40751100701c032081e014407000c201150060160490814007650a6a4460b00d804140c24105040c01a103210356001d201000d4601e00440c0c11303000d0601406003241030702d41e0380c2c3c03880e442d26810810010b542d20041ca0700070b0020349980c1080140f408074080c408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 510470404 1250 510469154 510469159
    0x18040209130309180213050102010212010b030a0b09011e050d0b010509070512151c15020a020a020910090b0114030a0e070504020a0302040e06090127110304030c030215150609 77
    0x43c90344078122200c0d41d0101d03c03804803100c3d40101b440148003032003d9240c0003600c400c0c07000310304010700b1402902081c4418030800c0503030180000820031144290b04103892540c030280400c005540c1d590303401040b2040c0074801e0707800c402c1c15240224040c6066081d0746001a04000103220907403d000c1000700c4250081e2840303051020400500d0454060000f0080c0305618201e01150211403042c10f009101003500d509100080d174074580e52001440540741016070130445c050050311021044405d03440e000d01d01c0c201075809503580c0204140041111840d60658454110510540300268010b58514680090080e1070140a000180e203024442e444000021007607800c0359501a5500c000c83c00320fa01c040319100001c0c2c1c00042c140159003c024080c1c1c1c20020544404120303614005401d05003a000b100c440c804141f40c2402001d400300d440c1c020318403036540c0c03040c0a652400c0920b40a00980d4170a003048015000b900e000400c1c50003d0740036140f1480c9001c8050115100b0a000c00c50b4035801514485d0303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 510471654 1250 510470404 510470417
    0x718020d181a0106080c041e050406261b010e040b0603160206061c03051c02030c12160503150a09050a0225051203060d0203011a180402091303 63
    0x811020811900d840310300d001e40c0710411980c6200340c44869a502c16003107a401e01c2520b5060002c441c0180048500301d41c103000c0350402e9032965200070070b040d608503400b02e58480d080020200390003464a6505000e01c41a45241844140354441c09880c1c241c40440d9410705a0029150581540519007140c81904020000104080024005001a00103031203210b5050440d07080380c450642c0420000b40c106208035040c1c426140f507111866040280c10000a040040201d0285046540c01b14008595080b40d0815034582c90012440e00f030b079800108155403400341a2002c0341000c7c0d8016143c0c2c2d40005c3e86c0d0740b01c5d442d596580787c84803d8030000c45030342c0b80c021036a1040012420880c0c486e41d03015a10070b080260760b51290041100070321240d410000070285828074441d00140c0e0014401415140c20401d15450b80c0e03400300090310032007000001a4044d420004031801c40981110044132420040b607060000f40251080040c1103c400c0b50000d410121080104201605400d0071001c107511074504031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 510472904 1250 510471654 510471671
    0x1051e120a0c02100506060403061112070c060501060e010903120e13051021060f06050d0b06041104051302030912070c1a18122112090718020d 63
    0x9034a8001100e000100c1d41c0c1c0da5441c0d1150320360601003413240720342281c0d003449a810424000340c0c0ba03110b03501c0b00800300d5584210f0703005540525010b680110300030710a80e0f101442c03c000041e100510b0ba03c0d04603000c034681400880e200c3e0041c4002c1c07800e150306941d4a100c2d076040d66135224450581c1c00c42c2c402444054803401c1180d50740d0300c00c00d480b07000c01f160012031903080c9050784059440c000c1c1c2207000803005100b503010110441500c490301c4550001804541c0a88181409000b05a0358011941010080314085e00303100500591034004c0c0f42c155810090410440000c0d5844e020764040e03650701c041c840b20900541c00d4150060b40d0400030761000e503581c1881802c149840c0750700102080f5065900da05042080700100301c048074600c8224079042d482c0107034042082481040c071188640c8109800d04100380008000c10642c00d46101e00b00c044042c2c1c42d0038078000160390300301111040d0030f2074040000800d07484002c03980b00c0495040d03030008a00c420304048030344c000c0d4020f012000b4055655880c0d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 510474154 1250 510472904 510472927
    0x1a0307050a2307060e060a05040f030806041803210b010903060510051801030c0e0c03180703020406080c040e011a0607030302160b01090c08010303020c01120615051903050601051e 79
    0x52020902c2000001074100d00d0505050500340000e0500307e40b44e151504000c00b0600d40c00e014101c00754075140001c1c80f9030301d645c0054020702c42d0301d400600140d031488580d410580c115440c01c602841854011560042c00441d032810b80b0052488540011010307a42003000507901c1e044a50401e01d4081d224007801e0b2204003050901e01f0407049086407944030710040003482600784000e4054044c4450b00c070020710b0011004a0948409050b00b040c4000300b00328030345034071428400c02d8040c41c5c3c014001d11a40b0340e148a601e03940d188008090703204514140c03074815012414450083c80c0421964135002207850305040100f00c0e00048426000d060f000c0243c02d070005000d406911400e8070035080010f095041001142c100d0b00c00ca9010803d11200000504c0460380000301403040110034604148c0301c01805002401503d074030390025100c901c4109902650f00c1c5c01c5405090250741c0e404010508080a01085040e5201980d1040c0810b200f0440720f1113205401e402406180041c0401510f401c400442c4c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 510475404 1250 510474154 510474157
    0x2f07080f03090309130b010c1101050c0a060b030c0916031d190308070c020a0315110309060105100203192a051f0b0f09090a05060903041a0307050a23 66
    0xa0b07001c0076410003d4204c0e4180b6004040c661074246203881049202c0c01100042e2805141c488041e01f0715a402001022603803041c011208a0b09020003030300c0e5600b40328a41000a414400300b070b0b41c460300840d600701502e401c048095610818201c460032a404080032003c0c0c3c0140a08404120444a52041c00d1741c400010003140404c0e0041c0000d441c025012070030010000c07a4007402c81005c004642034000f0140e40c5140001080d26007043c1082c06440101d003a06000b0540401c0c000318805011080020f52140860030314100d4101303030b6900117010310341c9004a072a481540e180481c80d072074450f54211190b110300c1850240b01d04a5030032003c2c52400c100c4145420001420888003544100d00a0487c980b0301104070040a0400105008a4096800050f500120074240074020380c100700009180d60000c000035425103070040103841103420080990b54032680940980480494002c0030341e8500003041c003c0360702c030725802c0d40c803d810301160503011900000e483c88894141c2d114041d04c803003001403803070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 510476654 1250 510475404 510475411
    0x3170f1803160f03051c0f0f2109050c0103020f16052109030c040c090308070804030807050a030201050705180603090f010f06180c170910050106050c012f07080f03 72
    0x801c411013840c51070000d141034032910740b008070104011401d0854a40100d60070099042609107201b18000ba010111b482d85451000c0041c00b5a16000c0c5800048540c2d002c4100a4040d1003901c0754100b03000019401ea12500d950310084890412403a58500034a08951106a1007801620003070444200e24048050403130110510600000070107400901d01041034883c54030056800344481c008441002d080344070280300140160b00c00080300b60400203100122030246921210b0f040e15004241003183d035420114500320055864000862011401481a5110f0507540802161007648400c20300c4410340015092110754410390200405806080c003d6a42c00b84240b10001074807440d00d981c540b45400c2c1c000303103446104c1c03900540340d40d01da03481107001842e0346805560030055203880c50744901d046201d84c0101c11041c0362500200e00c01d81d01100403c00348619000920040100c42104e589109018055800740d141424181c51040289406044a00c1c082e003140750605009012883e00d6500c01c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 510477904 1250 510476654 510476669
    0x501050c030f0f0405030a030c0c080409140c09060a0c02120d03150509041104090f0c060f03063602090a0803030a060f06050702060d090602120103170f180316 70
    0x4070800c0020500c031040d07681d1043ca15a075451480c141a00c070b40342c8a104015070a01010307215482d8580042c000c48803a0348050380b01e0f10842d0703260381d600c405a009001d1189414114125000801e00a100310000e948800000401036890300a400101b84d40d030305404a42260081364800e0162020142031040844140382c645001c1030400c2e0078520b6402e10803007030304030911aa10002c02c0c4008641c8000000c03041c4403041e01c002a6251040c10030352034820a00500400c00a441840810701d1039016062042402c0d0300d8505201d225119074040280c4903a40c3d00c001e2040c0861041c4108032400905480352205810301c00618022140c0c0c041030903402250400e500e0b0398000428840100d00c01d200e00c800401d010011ba298460601c540140075202d10240a80304201c041002207100000787e0110040a90280c0c0440d81d895420752100d000686c244000da80f0341590300715554030305210004039040440d49041c4c40d840c2c01002c450003420031440030300283d05881260f500d8018810900390701b4001d0100d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 510479154 1250 510477904 510477907
    0x22050612070207061d0418051608060c0708030f060105040f0b07050d0201021201060804031e03051801020f070b0912160c06090b0301030204050a1b090509011211120a0501050c 77
    0x1125002e85003100c15880101084840340b850380411030840000100340310120b50206811422054482ca0184c090b07402034164081e02d440c0002801c0340031007503000c0340c0b00b56043c1c8103240e44203254585140202c400c044c004000400008865240300145190702c00d005041007820703da1503100740840c0d0b481d950803180c0803c8000481c40c051010030400a906032940d440294a4007204000c507160019040c400c140c2840401e10114003014042e58003101c8085001c40344c2e607410849a10020081d160540704204401c82e40c401c1345140e0107041c002c44109100ca031503010300c2c100042c1c0d6049240c000c01051900107001d51600036101c01e09200040060600e4050303050070060305030900380c051046caa40301206008200c18100540c100c04000ea9045a804580008140d84c0710005000a014440c0b4069210521021107c580ca6045103014056500941c0d420f005681c0711450005002141180074000000400300e5121074940045825030515144040d02d0f000c0149030740d52402e40718103039007a0140a80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 510480404 1250 510479154 510479161
    0x6170102130b0906040b0703020a081603081303080114030f0f16091e0b0d050a051c2d0215010303090e0f070f03051003050312040c0503070b22050612 66
    0x340605a0150005407240b40c6030103007880000c0c0e280e10a910a0322600400803500c0810701d0300a0004a0442d03030000041543c134108a5889191076884010880205031204c0105610482d0b00b24100c0501b903250321403004076400c1040d603e00c4a1402440503605203e440b0000020745d0007401904c006012100041c88020700d04d031281c81c160002038100001040ca41044034082506074545d0400744003c12000080c4503242d100811280480001c010300944190b400035803c01c02c00282850782c00218010710840f8212942c011140b0b100c0e0030040c1d2a92090b545c088003001100d014048a10000038011035284c40c0070481d26003000c5800340c2c01034010460f03003c4100060ba803101c0300300ea80610082d5401d502072810301c03000f4011964100f070100070540e454000400e1001c46122141c0595044421a51680402d514012100c0270480741180d410340d02c02400151400c0000d908000c0c0c4444200300317030230f064a01c001c20184881c0515000c1039858031100005198441c2001071140c9400408290600d00c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 510481654 1250 510480404 510480427
    0x3182301020f0a080f03060111030307090e150f06030c070c080c030d03111629090d09180f110301090b0f060a1202030901110313060605150f09010306170102 69
    0x400b4001100a90b80150030410700007500ca40407100680440c00040784c503510390000480d402c0728082a501aa07110020038005180e4000c1d126004403280c125296002d80d48041d5403110303202d880202160000c041040040261400202070742c3d11220352110b0604082c050b440c0c41d02e07080310a500480d82600868490f5803181410300c40b42081d046941410b00103114192043c4007648503403400d0b004885500c5031040d08020601c1e0070403600d1000002c5048111070840445056140260f80860303041c4510071307400344524050003142e411a251018003580401540341340002a00b034100ca1a400590360f03120240d0045925805180a03222078000090040282410b0000d40080301d10740701d200e00d00900080140300d03400042440904014034025884e0340b2000502400360401c000518040e800210822440440d040b580c41107142c000c420500c00e09694009000c41c03441220460051b030f040130400140b800c06008000c05100006150000c1c4080d0742d0040081c803640c41d95811195a50002400314440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 510482904 1250 510481654 510481663
    0x7060c091503020301060516060b060c0c0415060e1219080d1401140103090510020a030b090c0408191a010621022104020d0b1509070201020702010207030318230102 72
    0x1c1c05040451465051150141542c003132082512000e1944480c0002000380ca600251441c10003e4042030b00d401941001c0740c1c5414200c501640174900e0180400f802e406080101001c9589540701e5100390100403040c001d410701004000c190a102c1e61014084d0320b103040044260103400398414640b141d0440ca4610180c030082540020408440c01c010f1040c49885003520741440c10074200010740c10001d203001402c0061501c0c1461086102241600780c4e140c03da0005266060f040b1810541c4d0380d10001d0b000700c0e900450055048a510556080c41283c42d80c1034807016003801004104500070540884068001090f0040da0000300b015001208003400004051030342c00b8440801d600f400c00311600c170521041702c00035600c1c04a0128011a00350748409048800064000d041500c061510200d02010358201058850080c080000099407481c41071007034a504a80c16405040c0c0c851440e181142c03104210441c00b4000203400707800051195022403011000d03c040180340c4d640c1c0c0d17550000603081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 510484154 1250 510482904 510482939
    0x21020319030203090615030a0b2418010911091f031d0606190e0a061508040b0a05101509080105010b03010f0b0c01060f23040e15060607060c09 63
    0x1d1500610034003090f0540070588a40c81070710f141285240c1c00c1d4110010b4900560303440003a0211102405000d2410716141c1d843c00b0307550030300c51041d9000e2041e8003880000c8400c2c0b1200d01c501c540d03000040c01660419004403600341d410a050301e00700b001103000508000b40c000e036aa0f402200d82449180c04035014050000c14420300b4110030300c03004100c0402d503103440004100a10456045c8840100c2c0001c072030b19080a40082601a10390b03150000c81c20005003014040d42c10181c030a04041800c0d148101c01c154861903001c03000c0d01c1c082c1c851200c0fa0f40a45000390071761012140103a00030414041580709801c101c62242c0d280000d941c41c28000e94210364040c0c0206420700c0007000180180d80c486200302c000c842201c545140d40e06107000e01140107000075002650849112900094403100e03603c000c0031301c072400c52189000023090700d0800048845078841c219164000346000442d002045d001168401c00c050581440c148031561a04111000d180d0700b100401d000d01e4042c407490342c0024a040741c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 510485404 1250 510484154 510484157
    0x5030d0c030e030102070f0803180d050a0f03090516031a060f0909010e0d0801091503111c1707140609030412020d02030106060f0e010e0a1221020319 66
    0x52504060040c0308200014024080c0401e40c00401c00b151800d50480302c0540e00310445175107d003003610789601705500640d01c80805258402c2c3d090b03105540031902d42d42000071a01c0706454404508002d90b150310b1441c41d14010b055440003644d01050040c0300441d0003841514811803042e04501d0b081803d0070000303c2c101030180f18041086883d482d009070003031140d030085440003e41d41d58064507901600d0504e02489040c000c07000300034402c6401240c1c090507a500c0000501c910b1885801421010b20184800b909580742c00d80014040d041c04c000c80c0100904003500701c80211415260b503034801400001030300d2200340001d08442480a14076a414800c0c2e0b1110103007000d810441603d030f99034001c2e4040e4205082341c9040c0d1104561352902500d2049501400038095141d4903140602440034001c511808280a016403130640c0d8803e030003c68161b94001c100043d07240c103040c0c2880300010002da0403503485400d006140f84004003002d0036170011400354004d540d95a07e20055000b0f401281c61400c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 510486654 1250 510485404 510485413
    0x10501030f022d04030c0608060f030a0f1203060b040b0a020c0907090b030c2a06060f090415020f0f041401050c0606011419110d1707030e01110f0901090503 69
    0x18960f6000100380b000d54141548a41040b81c88044480c0e849140d0004101048494001664130f400c4085984540c0d411034601140108817000e250b2a0240500d00809112100340803c00045100f410f49125031914a800240d80b41c840369403c0840c0c0c00342e04a140c042d032004c00c084440d16030400041082010079150a8211f0502c8640a0b01c2514540141c422044000c4001010000c10b4001d075003202c0c0d0b010302018880d00040c030412000c120001c1650701e40340605030010390300e414200e1109081600240542e001c03555075440d0340546a1104101400c1281c003040000e00911501026120903800e8035809541c40b440d0401a11003008561045410b01606000c0d882c40d4840c0851640d90010080c20007141c0785d0410840302c0d0451241860600d494403485103a0000c2a9212058003003d40000d0121081d4160b10070041e00d1800108030010300300030203000010b4000740f203074001040e512902c030300114410b5180e40c840f41103904a00103610440b600403894038a15a031061542e03008100680252 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 510487904 1250 510486654 510486667
    0x2040e070513020a121d010501090605010e0409021206040b0708060108010f09180602031003050c06090a051002030c1506100c0b161704260c0a0f050a0b010806010501030f02 76
    0x101c1004200e10b180e001c8503404501164058055402e450400ca20701008203c00450620800b8051b0019902d000301da6207040c0003c0740d82641881514150381c0140c4079130040c141343c603040001030107852030102d8002d0b1300081a10200c80040180502591056400d018149840400101502c0005119a0410400c0d0004000121000a2030400e440400f0781c08030b5555086014a81d5443c519180181424800800c210011701c420a402059900c200143c4070305001c07480c1080700c5c40c0034210070b40760b014841c03100030000751910214031a41c00da0580190303801e200310004044e060003c0000140c1110881e0010017606140c0f8200944081c07aa500b45080c0d140c3c50780e01c0b403034040c59000b000220012510340c101c001c210b0003180304d031041208800300411503141038508000641200e04800c0006c0568000c09000c00000f03c0680307810282d9040204000103c82c0c45031807040003003c41c241c801e40506040b1102140301161498080c107401c0c40146800d5140c00001811a1148071802c01054814080d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 510489154 1250 510487904 510487909
    0x2070e010b07050c19050406081f0203090f0307050d0f11070b0903030418021e03281805010507120204060e0d0618030f201510090e06010302040e0705 66
    0x11410740e09091000c0c1c1d00d842451a28074507240034860034a5026502103010402c0000602d03443d000d884040d10144111503440802076034940f000c01c0714030410181c61003038490302c540f40da000c1e541c80004442210103113041d4254440c1154008601507806411010222583c0c1742c2001a0102821161925105d180d42e00b82107207032a0301c810b0203400120740d8000703408030b840e680400c10754020b030803801c190070042d5094000280c020340c0714140c1e2807254035040d43d00e81c1200301c0e04402e0364804c8004002d0103134110343c8030803c46404c0385489202e400d403039990860ba48040c0103644103e02910702c0f900001429040c4504060a80550069203091144c0100303c140106903209d032085149400c1907030602040c400c1841c0c0130015020a040d501000000152191706050f0700c19107801950303032903440743c5030b004600d00040083c8031002d807a00500c035804001407110008600d10010740c48401c402000f082c942d114800c0380103842c140e0701e1480541e40120b00500c1946424850325070015502c01c0205142e07843d0401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 510490404 1250 510489154 510489179
    0x30606070303150f0e010e072a02032109010207170c21060705040e07020d09030308131704080f0601050901050112110406030225051002210703050708070207 69
    0x181010303112841c1ca07031a400780c981c21502401d0400c03c80000e458659256403c1c5c00024803440e0113840010300403800f128000e4150ba103c51161f600d1502042149031403001e200c00100c07204a801d8403407416403002c08803044c002281da141c000580e51340c0e5030107108002481d001460300720300c48142c240f070398a0001581c00074507946125003e070340800802c80302184441080e070341030720440c00c2c5010307600810801d01d5010b001002039404070728110701e05441d1980d040783d0b1907412880c900c1c08038071100030074000319010f2a000c0c0d078444c81454441502100b55614411498003058950304003083c007007400e00640781c00703108040603001148000c046640c03621000400005061140034103200702d00c4005c0d800c8031929003041008002d50303501c4580e0340e03503640d000500070340c499a01d1042c141c034101d0713006d00080000840e11004e40e4004d0300500d0000c413001c40e004000c2d4040b151000400802c4410070300452080541540303d0000d54034000340c00c3c5010840a021000c00034103280840d00055428026031001c0700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 510491654 1250 510490404 510490417
    0x3010207060f0b01090e2410050a2003040905180d050a021519091515051002010207050c010f03151d1303020d0806210a03030f2706090b0406090204050705030606 71
    0xc1240e1405c00000000b161098031f403010283d04101540c10312070800341c0000003802841c0c2079965240b030b5000000a03041c41c400158650f0f2409800070482000201d0003508034582003d9a031883d1361045400c484c4141c6810300d420448400301d40042102c248c0c054051240ca68200202c11004d4154948040062505031085200c10140380c3d8580d0100280301c0700200303035400100b034003004001d4508240d210582c890a14030440340304524101c42c2c4c400161060017035503440361f400300c010002c8030200d00040d10302d81c6d501d8414400f00340c0c1c0d441807884805903085507030700104200400250b4000003c00b4a0100034402410580c4510300c10800e0780c00a0b0380043c8100000c8840e20700110a5118240056410118146c2d0101e18840754020901650008954054014401d80f02007248200607250002038800e00e56051581c1342085050322a600c8241100c1810705214070030018a525050f035885d88a80c0040c0c80585069981d21114021824240f2549401c6a020b00f085425860300e2000280c0511034a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 510492904 1250 510491654 510491671
    0x30c12020a17031320032e2007060e060c0c070306020d09140d0e090601020706200610090c0504050a0512100c050c070906050306040210020c03010207060f0b01090e 72
    0x80003030107142c1804d040000041e4007020101e80c0c4907a06074880f120140c020480b074030038040e400d00c0025200d603245c000300029400f0148240f610010000340c0008003020158540360000420503e94061905001042c0c5144240c0d00001c043d038001c0c04592070407000a10a10070940c0c1003285030089400090504100c80e80039001503a00c428529941000d0500404020001c0f0700d48107002d07a03605000306600b071021106680e6581312003c07030020170600c46001c2d165070340540c00480c024030002c2d00c9604c0e50a5004000006101c1c68954001d2181c41c00304102c4074a10408000d00b01840003a00c00d0160b203e170b40c00c0602e8844c0c10542051700003591400303148550380c443e80c240176070030000f401d080c89443c50a0300b04c25020084540c0e000d4000e4840d40c80711400202c140118400402c1000540c400c14003901c40c0500101260b943d191700b0300407a0521041b00c9400c1d07118003440001d490340c090006016241c030504010070000d01d510280f4003515044102d441c1408032006060281d9012502000d602c03a265 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 510494154 1250 510492904 510492907
    0x30c060c1b030a1e0305010b0307031109102a1509031b06020306040605040203091015080115060f112802040203040609021c03050306060703110307030c12020a17 71
    0x4820344240c01d5549000e4070311a400045003003420244c02010344010350016132041e0180004840e01241120800d0056a80541d4144041800e030761203688070000c00d001d0308805500d48410080000c000540b00303481003001403a04442d18503205d100a0001d03050444410140140f0f03c070380d81da0707900080f2a4201e004c00d03669450001d501490f2040c421865100580d0400500782c8186003001d45c042d500803103042e8080c504105000a8a061620840713108e85543c034050082c0c208a4491507014080322080007003403000e540c20200e240b0500384070b201c10407a0070f150160b030400e2038803801800388002c0c20705a40034003400f03044a105c0d40102083d10155442010307455a860601d035000706465554200010f50002e1021080004000403540603030646402120505e1001c0e028011211429588800040000f40c050020885a052140207098024840d0a003100358200c5100002d29503006408164005280c0c0903590301800f030403c1e0003002c1090188081c2c50741404035140e20b0300c117240f1400341c603850300300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 510495404 1250 510494154 510494167
    0x40b060a0504090b090c0d0f081b0613150c210e010204080f0f120a18050409150509011a13020c060c070c0909030e04090c03080a0c0c08030c060c 64
    0x1100c55500014001c01407080004820b00c0c202038000c02011182010644105045008185070050780f90004c254003c40030544400c003075841500e20342001403444540f8140007148071003c1c00500c0000e00c01c0d5069010b80140b81858101000030342035190b08070900500e4a1300301c41c140c507403042607136540b10001c08100c58100c200041405c000c002c48001346132a03501c0442e01041d0703900b0100c0e003c0c92440003071045881d10400c1e078034401d40b50004502c00a428030420009216050300030080c071b44448109042d1104150359940228003a41c0f040d040484a945001c06c0c4402001d60074880d007900b00f007070000208050140c0e0300d0004903404907004a60302c958181c4036070804800240d0112803602024078140c0d070076400c10010012083d001000c04541101c410240800c140b5000d10440103c035030103544400b054420034003817200400c1c44107006e0f03500009208000c000714070907200030803540c41165103105084055040107540b034503c42d0044071650b007040101d90110000010125000040051201c4d81c461 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 510496654 1250 510495404 510495409
    0x705010617061b0d0209030a1211160b030610050909010e0a140f0a091514010305072108090301090b070e101b060c0903050d0504180b0a03030509040209180a060e040b040b06 76
    0xb2000c00c4010001c0c0701a00d01d9002040c4d008ae407038200614054100d9980c03403a154003171512134907107015850014105100146d000d10741400305461119160504528141001c000304200300026008840c2c3c0300f50b51018014112a18841c0c011038030003400c412101230820b0b00000e41c014070040e02c0e0000043d00da84403082070110300d502a0070b450030810003c10007400d28110001c0840024030041da02401490000595180d0315503d00340e5034002001c0f10792050001d81e407859041d4001c040e4403a050b40d42c56003058001540c41c65014083d090310384501e00700c40e0701d42c0c00300200100803095920401c0b48101e1041c406107507002074100c82c503a2145011480141000e03086a91201e00c1c0d00241482c454010f80c4ea02d8030380c100f0008c0064a209071183c40d40c081070700d0492410703540b000c91f0082d00514030400400c0802e02c210013030101804000c0001d450000c01c400010004400208406150039009090003100e11031446200010409860f0401c0325141c56190400381e2100100050501943d1800003001503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 510497904 1250 510496654 510496663
    0x15080a050607031d031809070c0f0308132f15030103201c0302060717130510020d0e07120818060904020c0309030f0715050f0705010617061b0d020903 66
    0x1342c1841c01141d403900800a00c0200c5400140c0016000e03054160100c2c0c402d0307115241c3e0b18003098003c080704520910b9582d084401c07040040041540010000d161000620b544005000003500701603090b250b048540400c45c041e660000c9514440c3d000011003203450742c03284007900c0c112500885a0b0724412140002c901c09103422051441e030003868901c03419007aa13040d40610b661036000750b080b0b03140e91341d40b41411723152101280c0c81006592030700000540200503111824074034511030300c01e4406001e00185890181d070031124002c1121500e5140410003184204402c8004041017550403040c0d2030207881d518040e10581c2121a5a00c440600e05400394070b5140880d5801000908115540d81250240b26201e400604009100e8020300c0c144c01080270000803d14151107040710700d6000806a40000d17203041d840b03504648101c5e8010301000e004201c0030721500008158908400130810a03140401e403e107080101240b0074103080158000034150580242e42c01e0000f480401070307980307040c500000d151 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 510499154 1250 510497904 510497951
    0x7020a0e0405030d1b170a202106060306060d02130306020702040b031b060d0605030f0f19030e01050d0b190f14060a140f03090115080a05060703 64
    0x14a640300040c0810840000020000311607218000c200340041d04030019030310f003040300300b260024404440ba02e500316603401c8050f4003c2000e80c00000e402118070000502c80b240740195403420100850300c001c0c2c0100c1405600c00728020945440c6803481c01c14002600d41c00060186409808041124290a0090b904940c2041f003510401c334401562803074000080d600c004000c902640c00c1c0f02c11180c1d50f041c00900804482c440704040014400345906004041d0001d08110804a072140000255618140010b4005050401c058582464900c40c42c40c40c1c40b80392041c0c032010700210703d0044003083d44541585a442c209280455440464403884000761200d031003085e0303204108074000560b100a15076550201d1b00d080e00301c0c46000d69904031180f00680074004580e000031040102c80e90b40342c4190761120006c0c000042e100c0c2007800d200b003403c1803600704851003195a991495045401c80c00d200d40c0300014a050300007010084c155907100b586520024100c07405042d1102d070789480c58070301600303031206 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 510500404 1250 510499154 510499169
    0x1921060e030a0905040b13052a030703180809060a05040e1305010507031a06030603010603120306050405060a05130b03030c1515040603051209060904020c060f250507020a 75
    0x6684009041181c90790b01100110b40071502003407000909082c0f0740150800400010701001c0e100013180c42c00405440010036006c0d486080b14104100c0340d032000b058403040e008400c1601d03100c0c9084a0f02070704640c4e4920b43c881404001e021400700050240040f9000d441041d034040d91541c11822054929020320b410101c0981582400c100441046200c240a081d0141000344107a88580100b5412503660300c1003113a0072080303054110000e0400760011900001c001e00002600ea80d01c0e1a440413000840d030f40070713001903240c8500300000d280c140a51500508101d41d000e24607480c02000681c070845404081c4622515004425070742d5406105441c200300c0164151402c8000f003820840040f042140da922803006071800c2c010a82c20184141d80c10360741d2001c005d0114501c41c1d8402c001c44c0e000f0702c1d0301d1940088108800061a100c0c2d0014110203030b8042c00504550806000042c00b001c1c3c000d1000c000c1303100c0351303e00c2440d02c0b0b07484036903494000079030a00d40e5441c80c842c0003185410341c0c940c10100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 510501654 1250 510500404 510500411
    0x210106020a1709100c080c030a110721030807022b02120307020d05030a23010302030d020604120f2c090a2a05130303020d0e192106 58
    0x2102a0082a071000c5184250010360000c80504041034850203018001c07034103c2c8082100c03034482402054000a581e0040d0601424010003130003203131647e0700035251800020b480780340054141400b08400c802601d00d8001c0b00500341c1d14191881c08121124401400700f194417004100400d0091003091440f0b994907903002941d4080c42a07911000c0040d006c2d6000500c5003410100107009110143c83c000c000310741c0030300300c0c040c40d0820848441c1c0015207a0700410f9994100707941b045000500000c981e030441d10300c8950079032440c0101400c01101100c0035080d074000c0810030000901090a46c1184887c0f4200300741180300c030b00000c03114401003080d200c11422400010444030200a00742e44d031688070850310280240e4402521a0544d00706076000e25614410030b4101f00c400f500000d2109120a40d450f0103418000c40990760311400d8525841600560030080090841701d600c4000001d24203425110b620f50100c0300c001c03c8410034640d104001d05140c00f00220200800004c519040e007540100d802d2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 510502904 1250 510501654 510501659
    0x60f110604020f0120070b0c0d0809030406030509100905070f0b120117070306180b09030403081c091a061011060109020d02090d210305041a0403050d11130b03010e010603022101 78
    0x1044541c4550920b2144d80706110b421042703d407280e41485d125207100000f4504080c0380000a4000e072601030405199070240b0020180340000c1840350303880c1d050250005040705880c2c020964803942160300003443c00172040201c1c1d10440c0c24401c41e28110340f021408418400c98054559051028a4000034441401c20300711800c1104007080151410740500c16081c0d280e1140c080e00380d540c0c0b15a210051101c1401e016582d4140e013201803050000300030450104030100666100c5410040e038540568101040d94240501810710034403031040781c3e09500346214003c0760700511a88c1c940b01417040d80100307900050b408a9080954040c1c608580d400307451111104824540700d102001c00f810b006202049445121030171910038010140500d40120050400407004d411480e083d620003003040d01400400c1080a180161511a10320801d100c8414144c5600c00d2249550b030285e40741c0d21405141c0d40620042c80344400300c03802141168406c0c00c2c0140d0326649421008400c00c410480078034200d0410000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 510504154 1250 510502904 510502919
    0x507080a0c0e01171b010212070516050301110d0b2106011503020307080114030a0c150e0d0b010b160c090603060e0a2003070b0301060f110604020f012007 68
    0x241415514110b54184480c2e80342c4120f2401c03905900c59090655000c2d1450740c800700c01c0d00102561400d0180b055603000d9180344038002103548140700c04c5615900c81c030f80d00340d114031111440c90083e0104a0091105100040d038504680c02014000c0d501c21ba564001240c01d83d40c2d0b4018070f95003140908440d1071410100404944505c802d10854150011032060703001880d01c80d108482c8140303c3d54a078400c2a908000d00b040042082074150713034251050420050200780c200124030700410a1155900203600e000318001d140f0307250200f04901400610104100244900d2410342c1501c0c19854400c5d1603081201c0590404000b9000c0601602130069010440e4400360700b103041941e000d01814882114910302043e503a400350710f400f400c0400c041180c80203940c0c0c0b6200c02c4441c20402401c0b5080b154031201209407582c02070340b1503404129645000780045400c10003212020340040080c01107803405d80c01248494440c0b40380d0710f0401c000203c0100f010350049191446c070000550403660368a40310b460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 510505404 1250 510504154 510504173
    0x304180c09080c01080a09050c1207061103131e03080c01060e0c072102031b0705030c011809020d021603090306050606090d06020901090509070503040204060e150d0507080a 76
    0x1480c20006541e01ca001c2507036000000c3d403214004040e5900801070381d40382c601e00010001c016080318640103140b80046281d94400201c518151050054655586003040140402040b2503105265400a200754030810b84071460440868003c2c800d849080540064142584c0070305070002000c0703010209048005000550151080d43c1c2400ca20f1030301d540b03403404d4543d2a4080c0020050440d1040d000c0e42c01c5580b0664081c2d1a2190b20b40101c034105a403006207010f07400252611400d85600590b001c106a29040220342c031244000e0070700c11414a40c031880d04003611054054160926000248505400e8890381110890408003600c800040003d180c000c0042d21240310603500e40d800e04000c02c80903d4000111580050300a0500d90113284da0707a14079000e9044829200e05211603600001410349990101c0c80c460300c260f0b035480b81e40b464540304000444066400c06a9040c0c224410448298000400000c00030011902981901d0451034020b00e032400b01e41004500340921007000040008000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 510506654 1250 510505404 510505421
    0x270105010303090f0b0d0e160902032d01090507020a080307030b01080703020f04140d060501031214030709050919020d09060b0f010f081b1206010f021c11030418 71
    0x381c65080903680c0e00c44c0da85401c0068098400c0e0924100700c0c00c0756040856200c0102288034205a5030504580d1a00c00d00402140d40a07050316500001080004000032416046d1028104040420783c03416881100051005004001340c0c0c56540020400e400d008000b4030320655400f1a4142e43c91811020040162908060042c0071030510000724881a02a0007520a031103c28140c8500702842d010900300c0740340b21803010303d411100194040b0040f5000b409824042c5028014004990145150041c0100040c44204d01500307002d20510841d02e511102082c00c1700c8003200e5840a0b41c0742c034001c2d041d1903000303078003554645440003921008068441d00881c015901903801044114000c00c04d00440102e10002c003030014040d4990108060300450304103410102440e15000241440d02e401d89990b40000440c1d0f444a4451041101035070b40500c2e04007000d40b0358800ba00c181c0016031409114030181c442000c09010901646111a5104100340c42c0140600014100010344a0810a0007040b001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 510507904 1250 510506654 510506657
    0x506070905180601021c050408030703050c151e090f0703030801050102071e060c03120c0302040f1e0302150c07180c0212090d02060d020a110106210605270105010303 73
    0x303100450888600d45288030307040c10b030090700d124091503107035040c44c2e00c04440c41b000b404410320000c5800701c0304101404005100380c84140d070300c0c400c004030300e40351006800c0c0c850702c0d00c400c038010800140035050606c0e64075032081e5881074071501c501503401d0802900100c9514a0301c6420800000c0c154008036803812644c007a000c0d40c60785500c0d406e4141901019103100510031184520401459124a40900300c5500a1404204040f445840c420a4400c0014504002500401c06204403500d40070064002d10f842c414043d40440182601849811188800b80c030410703580070040311801c8424121600d00c1128030a03215441e0301c1d0520540d0b00c0202e81c20501015150494a000c11030002507042103104410345e01d03070f040020550030480040364950049801280a0000c6151040707103001520800c1000d8884580360f20b4000039003400c42e080c90b031100002c8040050002040c030942004440020b80090f07020a60399039228810040c0700031840c1450b104641140301c8440302030194030881c180c0384603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 510509154 1250 510507904 510507919
    0x2403050912030402090402010513031b090b01210b060d1a030706020714031002030a020711011d01110102040b0417070e010b0418110316080105060f030402060c0a0506070905 76
    0x14024416a100001d08284101410400c00309002d0b00e0038070207456001d8414900546000d08403640c1d07a480c8170180e40304654460100301940c00301da03c0c0e010000050403841e041081030700b407444002002410041c071312080040400154030240b2400e50440c6914040141540f90341d122034080540c000c0c1041e00c2402d10315110595000b105181c08a4048202d41c259401840c080d03043c40c18a80c120180d545455505120303403190405031400170300146100d03110503000141c41d200582000c0f003514440c608510b04110060303c0381c0106148100300360003c00020310701818071003001e495a130300911070b541110000c100d003c41c00180c40004080340e130500744a0300c41540e50055a4a001d146091828002c040814100f40014801c4000d02aa01c8401c0c2d064088003003281c01c9082c0140e11168400d032914070612015040a2a0594000040074010001510071910346112a40c28130820b02000d400240700360400940e0003042e1004101104400b07420006070340460408540180040d4480c0c4a0715018215 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 510510404 1250 510509154 510509161
    0xb13200301060f1413020f040b0a2607080a09050d030e0c1201060f09050609070e0d02090106050d06060801050306060d0c0e0705070c050402033108030f011d1e04030306240305 77
    0x20070b0083c0e0782061f01003101182064108035140e5500d411034640c600800409034004000325240c044600c2ca0340c407419031203151904041c07400030060880141040040f60070003280c0d80002d240050a03454020261400107100c50001c101c1c13038202103d500c55070360300498402007a01c64078419070000048903039040040c00b25070303921805981034441c11101d680d4001c3c81000000e03415805007401c0f10721000010080c982c41c0509900003003000d9000e0300008005030002c01d0807101490b981c810100900079604015449601d800000396031000028419406140c44a000c8020044441980006401e04903c010700c1840c01600090280e04801000c1d11103c0f1018000140390515100322409644121090490309103401e400b440300001d0300b2038012209103101c94004c0401c0c1d104024500691940502241d194540001c102c58003041d0b0210740f60b40031600f0240415030045419408408030010f010001076961400e05a000380650340c4160221000310901d4080c5a032660010300b412042c0c0c2d141003021341c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 510511654 1250 510510404 510510439
    0x70b0108010e160b030403050405030d0903030305090703200a0b041e12114509060610031505060d14090d0909090203030c190b13200301060f14 63
    0x1c000d491103941d182002c0505011092004c002164024043d0400c946040d5841c0d010a00c1c1112404081d0002004204140101039050140940082c08140188541803c42d1601d119030410b0b0301505200030101d00c9204216150540020001d20b81c602103145c40356921010781152007044d2501000d0354094400c00315425090400310841d494100800c0503061100b0000d02c070702d00320702030404220040007112200400c9035580000000c04207654041b41055002c0c4040d1006038405003011607a43c011100b00070013500c88008103121600245004114084106071039841d900d10381d04032a801c41800a2040b2500400e030300301c82d04804412040300c0b03e41da1800e0712151100140440c06001660b000d40c10450240207800000190740001d0650b4a012210540145000540c039032000b001c0826800002c00d000098581a50110324618601406a0560745120840c00c1d4450100003c0820741068180c9031400d43c0f10b1800352000c207103001006520b82000d0070a00f8007902e0348038440c0c810850100440c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 510512904 1250 510511654 510511663
    0x50f06011802031803040f0302040e01050702061b0403051c180b040b070203032109150702151e07081f080c0d05100204030c030605062205060a0803070b0108010e 71
    0x280c408141d0341d8070404071500e848001c3d40c030280140351240e110045100710940103100a10050401c100c003004024591720600050350b0340200341c400141d24140c20802000d80104211b07a0003a001c10f0049000c80b050605081c4601460304081c140740304c0c940e40542e82c00729001c0b42c80b0301c10f1a03503100c20078483c0c4815036802130407001e400b940014000502041094180b80801b411555200809490514031195101400300c16904007a945011040c410302c6078a4009000301040c610300001c00014628001c1c90213035440c10744500c00c04c80c03540f81c0301c0007540c0c25204000300c6074029860b445101007401c000c08028502e290070b4070a1400181d40c102c4601c840251018400700b141c40c0c5001510101d9410020003842c0c0c040c105081e5154040c003004000020540d100620240d0700c03030025402c1090650420404542004050500814052102110128001c000c1a40115100070082200c2da1100301042011905500520f003d10005c6800810007104120042c1a21442e10007005583e040004190f0364 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 510514154 1250 510512904 510512909
    0x6170a050a0b0604020d15050a060f2a080324040902241207020f060105010305040b0402040e100c02030c0d020c0d0803060409120c12081b0d1b080103050f0601 70
    0x6074071807440d8500066404a081d680550300030801428900741c06803400a07a0080b60010340c0080110310188028904014103202818091421000b103104140c40a040c0c866050b89024104102c0301c4445144003003000c03180015a40421501e413a81004d03205980d030740b2001c400c0400110a0303038000d802c181c2898410b80d50ed40d0b0b00205031000050045420070110500c200000103405c800300601c043c04500144224064082540104400c0000b228024100b49060b00f140c0d04040c1000c0901000c01c1000a00d02d82054044500103005980032400d00e141c0720500f00003203c1a0b0034940c0c6846031a8020010f014800c0c14041a543d2644404800b203840341e19404103ea40802140300c0000450f0504000c0e5a0100c0094000286980740b9210901541c07a0060010001a042480082042280035400c43c1da907103142403180080c02e0001403841b0290343d01841c000491408506541030504540040060031712000c1d55280001c803848008040b00000d0005403031038800e06d94898040031002540d01d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 510515404 1250 510514154 510514163
    0xa0f081b12040e060f09010e0106020601140a060f0e03010c120f020a0c0f0606050a0e0406181509060b0414060306130308010e090c0406061805030a08040b031806010906170a 76
    0x5402d04110340400000001341071550440b4125400c0c5590307807164800b20340a0303c1c5001c2504195898540c3c0245800c038140c01c010750715410707e0043c003510b0711202d45030403d541300c1e8109500102400081219106941d0244503819828956203091081c1c0102c2107208041c0710700018080301c649011900240d1150203a15070000d54000c43c12030103d41c03078010030100c5034400c0c0004038010340d84000040c004503031a0402441d02038200c0030b100c10410184110342082e400e0200c4081c0041182d01e0b0129007240d0581d80c81080c907101d8007500704100c4039901a50aa0760b00800401161031380040c00011a0002c5502602920414021410590070040d503003c43c1c5034541d035407541f20786c20041906c1512201510346051031143d50b400c00303a6030fa03c40c050100500321641d42d075215584aa1960b504100f010760040f03000346c002552080106034920203c40a603214080300c40c0e6070743c8981440c6800740316580750000441c015240045000c281c1904103508850041e040500c4031b00004010588a2128140081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 510516654 1250 510515404 510515407
    0x210020408070b1b0f0303070e0108060109060302210124081b0d1e0b150906030c0901021e06040308070314060d29010e10030b1302030a0f081b12 64
    0x301400c014202c45030110075914050203142910b45c41c001400040d08201c1d00301004006486621002060391300d1400d281004913401c0510002e84614140d0240d40e04240e00084e00340f0117160307403003d0341c4641c18003601024195a503444042a00001e500400c141110710840400c2c00c4500c612101c0780540344105d4540811206041c00b00720780c3c3d02240f4200c07102501d409a0000b03048401e00c07492440d081c02c00d00440c1e16400d84003041880800300c0c0810003c240103110100a82d01c620099075030241c42c10240030f039100c0c402d200607803400907881090342070000d4494543e0305650012035000e00992090b114110b030360703c865406a09541c61010f40c00240c4543d07000007241840c020808081150152a13014038a4480d10b40c101d001075140800d00039024105001045410341c4020125400b04242e0702152181c1c0c15a6280c0820b4034000d440c80c1c00300014201e206d002d641d01800308403905a80318000c40541100d41c0b411200980046100d52203241502000302d42c00900414032829242e0f41003000d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 510517904 1250 510516654 510516659
    0x4080d200127030c021e1203040617040c03020607050a050d031107020f0411030109020703080603060601050931050a0c09030308070c1e030201020c060c070201020c060a02100501090b01021002040807 87
    0x1001d40d82e110000ea08003d0383d0400c400150301c49810300041d180c03803c003c1a000d0403040b000e0003002c0383c00031180b00950744100003c105045c0e100d80d0a46c00d030900b07028108116112420814845140b680003c1e50103400050b01c10100b00f400a20300096511032002e9404010040000b2781c111a5111122854280b081000b10010b2505801c0209181c2c0000c00010740c040741c455258045402c01d81042c105103034009401d00034035030480c04080c0d00040407070050007a441c00c0c1000030241d01841454500507415945561030004640001002483c003039543ca86a8200e500c0305d071405450240d9080f020715140084d00c0070044e01c207004401c1607a4240d242d004594031624400c988030701e0220b4064940100301d09a8480a0159017001c034202c0d402036001685803d991555541060300150203d0600e403000c001410050340c0100d4003c2031b500007101c038079450703440e403040c268100660b48940400b003d150100101e401280c035030140c52072500a13030031201078091b0039842e00c0c00c031311650042007201e60069604 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 510519154 1250 510517904 510517961
    0xc0111010e07120602280e03010506060409150b0706051b0c1507020307151b051c02030a021b06041205040f0905070e030607080f0c250804080d2001 65
    0x1054a03c0f88240c20040c645288500c8000d0649025400c0400c58507048021110259028040705451201100208014140480001c2c0f8900c110311401c851651140d640c020604100d4180d20014500f100030155203038401c1c50248010201125070522102c0301c1842e01c40c0030550071054409550030030008099400c80c540e04000d0060b001411001144001c103d0200025504c800b10030707040c40d0148002c00c09810410407000320480000000c02046014404100e440512a07403100f40003000b8000166641c0ba184480d90203446207505040c00d00c03c01d02c150102030600011028400c078003840f84444030748200e10044070548104d1054030940d0014240900181c3c002c0c0d031026400941c1c504050007010075a101081c03d00d0000c440c101c0c007080c0001c0805c5801015006032941c00070b82e2591081c981125124650102d42c040c07001107007001d150305216010084007404071030281c5018400c0f1030106407040310042186100e0603621144450385500d9041c0d10a05004081080c00d001d400c400705066402503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 510520404 1250 510519154 510519179
    0x31e010b03060d1e0609050d02030a020304090207021c1b271508070b030a06050406051c02040b0a0b04091d062a0a03020c01140106200304080607020c0111010e07 71
    0x100341c5452400c0c1c11390002803151490010134081c495000490341c01181d083c10350a202500030b044041d0740080040f90b0100d540442110b0036542120001619040d0030700104502142708400410310035141d20014007031000072801a100e0140c10380b4000142601c801008541c8080a80706075400f8440400070300304140e95410910f401010030001162041e034034480680784c007400e50b20100c1d80c2e130000414840340c920b99004181c09802c1c159410301001d85028080760303070780116000d4000c081064421340301c1155603d07002564114002000882242c0d02c03251840c8840d8402c0c840e002d002d91400075040d00c110851504890044400006803611340e5680c507a0000035640d40031507450000349030030424020b80c100300282caa240c00303582e0016140d41e4200400c43c2100c4011400074400c03182400100301150703002c804503a40c01509184543c6030070500c1d07040c070f10703500450300814041c7c0951800c110440b680001e00240d220800d90b9800c0010780f60903031103400c0f40c0085c3e091400980000c00284240024100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 510521654 1250 510520404 510520429
    0x9060a020102070515010f0605040b0409112107030b0d110d020d0c030b150d1113060807030f0c320f10170a0c05040909030e060f031e010b0306 63
    0x9460031a8607640d13581002c05601c0342102080c1c0d540d006000005204030075101800c018100585840d0911007020740328000c0c0e10a1060807a02c6898182c0d40301c011400703489100400040402110041d01d0350151154012121400041e1804807194560700d8200484031410f0303001844008400c241d0405d0000060085005a8101c1c649070a884001561400765800843c01031540708000d0512190840410b000c0805040c45110701c00480804500405800c5810850456a6951500c52541d0042c0a4045680000442c1c00707807110000900078081c2c08082c60383d00c13541c848907034180c4403041440100182c0c4404210b4807031000540254030300c5018903280f40301c0d000b40f0400c0c0280002c00000c6420710700d02c031031130005580c540c614060016102d01440d085002e0b8401880781000209000b091400b881c4500701445403110b040c0340506008441505505601500c866030711a69100075075026170042c1c072208545ca44810300d2200d01d480d00e68003075058078000440c491030340e1a4001002054070410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 510522904 1250 510521654 510521657
    0xa0909020d0807050705040c17061e030f160b120a230103030f11011b080c0d1b02100605011d0a05130b03060105030604112103070602120a06030809060a 67
    0x1001c8480214080b10060000e09100307030001c11595041100340410f4400c8130f142c0d4800e204107150898a41c015005100e03510183c15148070030a5540c0c003000801029010385420b0301030142550340001c0200124101d4000c206136a41e91040e0743d40c41f0f0301000c03103200380240754000307505000201d08000c04c20b402c03044109024180c0718015142807010440b4030f44003a402200450304400c0c84540d043d400c88940a00504540b00070000c0181c3c40740104401204840000100600b9000060b8504144001c3c3e8524003869801040152042c0610542c519401104c44000d44648101d000002e03c003070182405850041e03441c4600190b59054a050070041c04080960000e102d550200c0d442e281c0446000203c140408041014000503050508103501a00b0460083c0c0010b07003080080382e5200f01c003280318070054468410b041c5404214413500c094030710205060b40800034010050148503009031008010f42c40d140072035a182d102801c0103d0f1642d01c4020b189501c24004c0c0c005c603141003405030120032002d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 510524154 1250 510522904 510522919
    0x14031003060c0302030a0f0b1c0204181220030f0304080d0903030204260d110307121809020a08070e0f03062e06080c090103110c060702011a0a090902 66
    0x200c0d901c241c1075900c184881000240d010040040c0b4004902824040c070703805e13403020807101c1d00440105c3c1c4005800c4002200101003120070304215102c0e42d02c01e41520303400160340100c4030200d1400300321201700d1002c1e12000620000d01454486043e002d1200700342c10700401140741c503000c4c40c0d1042c40740c0c200410603100410103120002014506006640b180ca100740d42c0140d40d642016403074841c864028552100c00e080b100da48100c0d140002400254414803030a0000751100c45856040c03441c403075100010070008201c0d5001e0209074211100550780965101219090340e19000c4203412401401e041200040c22800410310080c040d0544101c02d15000d4500443d04004401007850080161040d00280f4114514210b0034042803010040704500c51940300200351400e14002d00d02c800140c8902100d240c00107400b038061713009034001100c40520070034142e2541511711415891300b80444001000d9401c0010b80e0143c801100000102044010020a003803030404d00100000d016141007241c22001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 510525404 1250 510524154 510524159
    0x815010e01140a0e010809121e0910020d0206060d0b07080709080712120e10030509030418050a0506270c0c010e0307052a0405040c18020403020f060901140310 70
    0x30842c0200840d88042d181c0310382d0501450001418510b0013000c0289a07003203440c001413948060320031500e04d801c00020190400303010110401c502c1c0f1560302099840000303141c4244402e6004074030806808200c1e0248c5ea180c1c0c0c1d580041c0070075203403030704001007643c01503030005610640076002c0c2d150400078510741011140c1d2a600081d1401c8140d07089460041d8000c031841c5c003080707204141011030703081c280f5100720100041e401055110b2503000f001c0c800d064030f95002411314403080080d6002800d444c05c61000302d00002032941e00400382aa00101090300703150014149090038002c0515000d440a01080302c81c0600d45001901400a46588180402041485001c0c1d800340034280c03400b050178020715540d191038a0136520709405099456020302c0040300c91441030600502d00e00036940c050750081000c0d61070f450403140c82010b80d0070041c0103526030304100e41c080109074080c1c41a00d109468408420385010704004060092520550000350b060038101502c0d02820041e41d0400702d40ca50800d1010b8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 510526654 1250 510525404 510525437
    0xb0c07210f080a11030301300c2102040504031205091209010507050c0405070509010206011502030a0e0d12231c0b010c0f081801030b010e0103150b0d0b040b010815010e01 75
    0x1b8820380c080c0b01000d80021480156004448014030081a504034491480c14541c0d80c11140300f03424414960703003004140410034006001d02c50383e00398540c000d1003000f280c54a80383c003810003440000c080d04a80c0c03030440002c000050026102d04c01041c190001ba081c25095001114540c1c80123004a50340d004580d51050741d0384a0303009107401402c10fa154282c0340c5c21540002407800380140e0000704a095440040030b08a60040100c80025400d86000302d054240000415580200b81d10000e1505408810000b640c0c1e03400041342d8446075241d5112540d00781c0c540d14034140e60150082e461198625400703484405000c50340719100f05603060500d013864841c0350301d401031100c0c0710041c00d44502c0c41c0001d0341e40c030071079444070104440242403c003004005c0900c0c0008144145103c0141d05140e0f6074201c400d810120320400a0040182081041d80c40000420346800381c1240142c1d83d0180d0304200e1441003d40c054200c2c60310400d40c001e84580d00004c04001155011820301507a41402001803e030300e400f2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 510527904 1250 510526654 510526657
    0xe060a2012150915090c040305030c0d09060c020307050d02150a0c061d15071101110c010605090c0d15090504050319110a060f060b0c07210f080a1103 66
    0x92000011a15514211585411400820140a00c00e600c02000c21a1105008009184d0b8100a0b10500c00d40ea0b0b0b62002c54606110f81c0d000a0030600c008107400c01c1e080000030b90b04450b03440542c0c1c1e212050399550700c141c071012561074000354150400d607814010382c10301c005000c2d5070300c0c0020251800c000042c0c007414241d6228282c0c0c40c1c006120001c03803000f4001340703000f11114030300d2a03e088a01d031008841501e0302c59018450a01290301d82801103401940300300c15a00d0a608500002c00845510032800d820a030b0203406e0075401e65080500c009034900d480144075100f00c51401d002842e000c4800a510014140541c660350903400c00c941c0895080005e100d21440303244100c0046542d601d9030390990f044100107400005c200700e94400782415106000c0342d0b030764000ea0712000110301c80c03855200c110090308054028840740800818990b410a0700094030034115035004500d96910740c1c00d8440d1621aa0140c44082c010002d01601c950000b00340d038004054013031880c07070841c0454602020741c9046 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 510529154 1250 510527904 510527917
    0x90c01031a060a05073c05010e0105011404050f0112170f0403030c1505090c0f01020a02090a0203010312090510120f0f020306031002090904120c050a06020a09090e060a20 75
    0x90b400b00d119800c209040183d1500107030201d2401c103c99480c0801e00034550000e2440480c4031514811b20010040250030864004103041300900066840d07400d4006603550766641241b0807402c3c80049043c05d001d0005841c1601c004da016100312203034584138010305104820304420850020010749407100c0c00369000d04007a40c8207070f843c4e0500c140306081c2454184001c0100401140c580024801c00440000304441140170070f4842184801a0900603810aa460381029401040500411100d5040340d402941038a20030f03006d041e0600007004045580818500415801a50041030010a140a042d2044a400540b203011989802c510a400b0503502c071a8054074107140c000c400d000040c603050069072510440110f0450500900d000059100349000c2c0010340941c41c3c1c1079040d11264481c042c4d01698a4210084900c450303441d240080096102e22803400002d101c00b000441e0158041c080e103600c102c40344000305800c2d1a050540e800405031420b40410b2080d4001d065003030414000e002c0c144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 510530404 1250 510529154 510529157
    0x60320030a0b15010e03030a0e0f2202070b011d070810080a050f01180c05370509010f0b0318012315010503220f0b0a1a0108090c01031a060a 62
    0x2c08501460003d0605c0001c81080751107a0030034031a040c4041e52015803102c041500711090b9581d1039000340480c0d09002c400c014194202c510800c44500003103160010000f2034410710a007461f076a41e51444e003100303004542d031441e00d0701806004118001d104161113900840450f500314100e40c0d548040c0d91820100d02c1084540f500900c2c241f20801200b8840e0028003400442c2004207260b0319517800c6810600790061a200700c0410401460550f508420701e088450000100d0302110161544112220210311031684290308600000c038601c0e0100204801701c4800f080c1c01c40c2140c495a4144800000346101c00005640c0d52038480440d052148852107080f00c150700c0300c0e056050204600180940d195000c9040c48002c10507c06c280c0c80401d541e41440381a400d00d92015070b030a01e0300b084a0701100d9005481c050100040c4110f650031a84501c0303098076001103660110321030400540c0c0408007200c45c0c030829000b2000da6405940290440c0810341580840781110100e0b04001422540220070300c1c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 510531654 1250 510530404 510530431
    0x80304060c120e0c030708071512090803010e0405010c0509060316020c060f2a07151809050901050601032f0c0a0602090102100b15070609050109050d0f03060320030a0b 74
    0x1032170a040c00030101502125014082560074a0180d4850f03210f12203841c0c0410081d0f8001c0d204c1d110059018000656101902550741d5a4801003600039000544003902d05510300034000b9170b41d60060013213038400d210161415055583d441c40d0405000800e865603403d502071a03841607591341e01c07000100844001d00c80226220b603480b800405081c444540a07100c045d2076180e048910800018980e0100c0e8102c0d03015842c6110882c0c82182c00f498100807004401e11200d001291030503080e0070a520456804000f004182e6807040118252428200e2a024508511007404403a015010b1825862181c60825510b0201000302c0d55140440350a81a05d2042e8007060206244d03905001c440e454404155060101d0702c040000182110882100b084486400240500c10850160010f08641d50005c00030810f00700d03e803d0280e01c1781d07030030305e04280014000411810f01d14002d1080c602500d0700302000302800360107002c031201d840d212100455450b10541b2410300c002982c281d9494404c4c00e6a05148 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 510532904 1250 510531654 510531673
    0x8120c03090106090908120c13090902040c020c1509030102070516030501060803071a0703090515060103151a0306013510081009020a15090e0c07080304060c120e 71
    0x81d0850f40030f82c1140d00358a080002c018003080c51207007034441c9401003a80c01c05581c0c8400c1030700ca01900c035240e103100f000d040c010400a109001e40c1d1240c240903000340c5d0140640182c1c0349040740c603584400c099580c03103e51591001c0c0480d0410300a80710300c1d4400750005142011300c0e2900c070704c0c4c1144601801800c079018a014001c008080c0911001840450011424240545d0306c01c9000f0a048844c1c1d0a0b403005000020f01e105d00c03e40001038603a03004015118441440381c408880010204d4543d07011070706203131400024006d45003102040b2401c01c4000038024021052006040e44003921071810044039880c10f03518118140030f02c0310a40c0c484131002d504d2483e41819513220840003419100206d40d180d0040005510100300f40758503050140d000500d40b0400e2000902c0d10f21180c2101011814107070b43c190300d9070341110810050352481d00d000310a43e516800780000c14461400e008040704001e00109001034802e403c5040c1010440c20002c41024026070380303600311080d11111f10845d52103454007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 510534154 1250 510532904 510532921
    0xc0c080102181003050105060a08040203210a080609010f060c0203010b04051905011508070c03090b0c010c03050108030405100f09080d0e040c02010c021f110301080f1905070302090408120c03 84
    0xf1060b10b40101d09080c419585002c0018503140649441c00e0144518000000c0841d60180030480c907203c440d042c1c1003044407803220b00c8203258004045000100701004042030b030b1481d003000e429040340c00c80c0c0d0303100384101d0400804940120071000126050342d280d454a1030241d031a802502d10a0300140030285010b014042d04c43c040d10010b07030060709111311002c00d0307003550b80d0f101898581c00720060030440d1700000130749070403101102e1a0f40000e011003000f10300580d1440c419000401c603040c160381c00b4080c99880302c920940340c0c8641c0c410340b58040982d1000400241c024148004600c06500f000c1c03400594482600d03092000d20360303551000984080b41c4031050300c0d19126000c102540d41c4001c004002c0c8180d0041d54840e61540c203a28601050540e101c4004455041003000000d08d40d6542d4507942c2d9084095603a103c8012a80b00c0d1b405403034800d0140100c81c008804605810100520281c0e00d10303001c0c0050303c00040c2003904d003c841080080404040c000845024130b0380c408032544d0745d00e0310016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 510535404 1250 510534154 510534169
    0x90c0309260d020a0210050408030105010e1c14070f060203070c1d041e02030a05070e07080f0114010e3c0a0519080a08130e070f0c0c08010218 63
    0x3030885010318444601200700102401d485881500701401a6a84916041030307240c030312100042d034055401d090070082001055000b40d41240c1c2c0c01e0300d42a00101002040040d00d0b1240301c8041d00300c50308a07044c0c00200380700c41403182d5a940031405403101151140b4079001820703125000200907900000b64a010004100e02d42c4000341081c2a808031000180c9100781280d0b00e015202070103010030ac6010582c0c50100c080c0c00c002280c2e00800325102d00c601454a02d4954000741308030b00b060405200040c0740f09005c1c40d00c0c28481c086070141001c1c1682410718694103500c00301d0b4228101b12a46106400c161212000f08000040303400070061181d4070b0f0101901c1c00c06000c401030154809070000c405194403001ca00d401035941c02c45030511070b400c021541122940303e80c1e00c040c0b4103110388480f420500503490b009024003030701900e140900d030740c0b200c1022050301002d4680000103512001d031888024840c00c04148101d02c250440820290380e48000d0f420783c0c12034500c0e0ae68a0b9500210005d2605e860720 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 510536654 1250 510535404 510535433
    0x130c020c0108130605040305090604091b0f1e0504170322050a0608042a06030b06040311010c1b08070501200303040f0f021e010f0314060d0507090c0309 67
    0x1a00c18414a44032040f1181200071810040c070300c64990001c80c0400d07008206031100c00c08050f10260704c4580d5005002c000c2c0580b0006a54414100029a14134610a0700051a85402521107a00003030428000c012040140034601d400c21800f0b120206543d40204200b00000d83c240d0300850f2114001e04608038203402c0e5a003000c0031041c0c400010001621044c540c50100ca049051036811a580c80c1004509060001e8100740c4400d240903800030640d034840400320944620b03517030401440f01c581f018420103104030700014280b00c1e0041119481580b00f06501c0c014a44a0082d18502c03840550121030b40034034030b81050f40c468001c1503082c045075034040c5486056028083c842c0d4040c0c4920303508241c5920002d0320140042c141c02c03e00900703205240c0301e06400c26078060305510480d610300300d40070040030760b80702d416001400b1030031103d16080c46401800100207800c5070128050f200c5508101d06840580701c102d855000f844030000d02d000044c030a42030416916100450080303014a86162111001c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 510537904 1250 510536654 510536657
    0x15060b1305010e010f0f0f03110721030216080c0a0f0b01051306030816050a080a0203030703140609071b061d150f0103080703030e0604030c061508101a130c020c01 72
    0xe00d14500b0032548030010386d24000d90750030a0281c10000c42c50403401340c100c001602c190b1840c000f8a070b07800c120982d80782c0400b02e100c2602c4030f218150251412800c0e407080d04483c5c1841c603802041e440c0450030380b200401c082d150749002c5469818640d81e030031f0340050305a14103880307c0501800401c0795050588800001421f8160308000c020b04699a000850090704145411a4940070510040110820440c12281e401c13504042c3c40300000780b0025034941c0300b00c91050002c1d00b00100090140d0100105901501c0c0050480400d0360b619a4101c814128807103c0b140c400500800d4000032031411310507995110354810907500350100500e211072421084003e140d402284203400c1080c4d0b08449500d490551358820240303070340c8041ea0705046000d00360100c101c680f42d0194030203210800d50403400c21000f8034441e810900804804150402c0080300510408510f0380005c081d41d410400a58016481c032041d40900c03030000069980031030300500000b06041c0d01260f9500040c81100c0c0c0400542c40700541c01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 510539154 1250 510537904 510537917
    0x3181506090b0d03270b0c0c0319030e0f1f030912020a0c060503070c082701030e030d020f04031a1f0605040302013c12090f15060b1305010e01 63
    0x907a8000b019201d0203c0c5485c43d034108401e006120b0700300c2e0a13200c0028100706982c01c0d103031002da580e95500c8624028506100384500c44281c00f43d0401c3c0078040309070710f1301500c4050401400f41c05012210140c0d210440e40300d170081c20701c1410031050a81900000442d5980007034240c1003843c28450700c0c6000181541994010302038100000d42c0c015468064035914640151662281102920350078103101c0e00403c03c50003c5100511400056012200c06c1c074039881c480b0550040320015422100c58905451080d081007100004801d015001880d0f1104d002000d01d2074190340c3c0d00c81a00d030800c020500d0b21554582000d100c07104100e80300c000342480b144820409072504e81a0003070901c1c0700b5444000d060041181c034001003012443c0d5039110040100c1204a80741c4648081c03107404410040320003011480003210126213466030320a217424194001201180c5d0449a10340310000c0b581d00d051418402d4031080d0108040c0f8144010301500300710300c0302c041d8142c1e0500300050144008400014104100d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510540404 1250 510539154 510539179
    0x4091211070b160f080c030415021e0606010f0c0203060f040c0f060903020f03100e030405030d0e130b060f040303091403010227010306030c0b040303080c0403080a03181506090b 78
    0x15140040d0003034070f0f030040000d4400c00c0c4c140340c100c84a0082980c8074189000200e800a4542002103450445002581c29100c07040c210140d0500b682c4c1d0151484100f951200d000114194022070b10b030b44105030079041031001014941c4c0040d00d001421150340d00d8070b1507910107200130808503074800400362600056101c0814148200100044824400640305142c00c00070051240c0b0203200094070030340943c0080c004e151031103e0b11a940e80c891f2090601900c1000c07004101140710700c0b4548040e04000f003555200605d00105207001d4003980c00f00c5580000700b04000444402c1210040c80190312a8030b074846a549080364104002c00348400c094041d17401000460603481b007070440c4003020000302460200034500d51004800900190300000c08400808002090220503000a0f0048a210b951007010507a10422101c1d030a01592000403c961414032001c80418040c1e00040b0b204c104104001620a280e40c43e00180d038a081134800814942d1804144541142c034094404140da0568054220b601c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510541654 1250 510540404 510540427
    0xd080904020304061407020c01110c15031816150c0203031c020d0f050609011205073312060905070509041e1e0c18031104091211070b 59
    0x21960154910403a4004002001c1200c2940600a1074010b210a200342d480d2200020703540b103505003141400b0442d6400307640990b00300003900c2080761070084d085030b400120181e403200030f0350406010141c5010700841a0000040100800c0e180042e00eaa4040007031072401484041d01c40d0f0f02e092071010820705078500400760300d0000466940c840d034a0703060f101c5030240c0da903807100900030103203a901c029051489201c3c000c0390582000740103a800b00c5038080d8036682c4041107031910a200c42c008000e50031590082085a414103107840702d004200001c2ca0512006041c0000a02d0b8100012400705a5290340004040c14910a41c0060407100313100300183d04120f00040c206000c4e030401144502d48401f90307e00b900d2861400d021104015007414002d007c10704843c01c00c0c1c200c0004400076028a0705140c040402c0c4608085000d56090004c00001c46042d80c4400c040302e501c900e150b507003060310358004200051741140e107824a40310030750b107090744041d0300c10000d0300b0200c0300d50042d20b8060080c041c0072180b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510542904 1250 510541654 510541657
    0xf0924030c1002062208160311060c0406031104032d0606030b0a0533030703060504063e030a1e02190503010503100504150203041524140d0203060405010b09060d08 72
    0x1c2d407c15600c10040b03143e03c0d044818100b060b08184440c0a628103120b0030709010f0001c0c100341d81080d10103101e00f081c4061a001d043c02144030151081840c40e0fa801c04540001c071181c5185412001351082549141d25000c0940700395a10403500005100c040055040d00c512401c0e40040700d03110740702c1e0b03520340e100c0c4100c1c000c000d08900d12071024080b80c6d040610b0795003080785034003c43c0d00a01c140601c1c942800c04000a25060603004400c1029402c0e80b1517589403207007008001c03829030502c0c07070402c9104d01d00c3c0707059500014020300e4015698444c0c100d01d00101e424449842da40800b002d41c2e10866403074140000c080000740b400030300c0300920041c000e07544c3c04502c86580d030400201c00240f69589003410400741c00d02031035045440e4800000e010522000c401d2407050011030250038010a52010036849440c2c05902220b840d510300c1034001c0c00400b1005410342c142c1400146035502c1c80300207030006818848251000c844030381d91506201c0250408040744c80c0d022004440210100c0c4031038450000d0b6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510544154 1250 510542904 510542917
    0xc1f050906150a03210e0105040b0d09020d080712120b0a050402030a0b060d0606030b06041d041712040501060e0613021c0908090f0924030c1002062208 67
    0x1420440c103180442d9480f0704840707600441e00001050380e04515a84100c40c0840300c50b414800050948402c4030081d4020b108440413174030550300b2140b41c01c500355001300c0103160840c8200d80c880f8440c1d5058012802e03030b8001d440828019400d4500080140c400500020100c0c210306100504104100210760340750710011003260b400b0b50b00541e50b03969107c50100102103503550a070703007c01d0102c1c42d65400d42642c0e1040c0700fa101039031001c018a0a8030000c0006c180640e22508120744e04485180585180400741c0c990010f2040c0802c13920841998070144e40798101031011019241103600700402d101003406520010310401c0320b00b5500d414804041000050111107424030a41c000692401c2544040c0407150143e0940344d040101d507641e80b4240c0c00300e81c421005e882c440c0c1c02c1203902225918010300c0c07250040b4442e4a01f0b035034902c40d50f040340c0d1200b84140d001e180d05000303d40e540c0000d616055180302140d2610303409060b85190491a0042418192a4015030807189292290025003200106d40301c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510545404 1250 510544154 510544171
    0xf0d020d0522110f09011206050106090e040807150c030b03070f0b190903050313080606030c0f041109040203091f0207050606040e0f01060f080c01050c06010e060607080c1f050906 79
    0x10080c5030320b00880c4058280010741d50300b0100445c00084e4142c55903444086140c030400c8241b009903a41c56040301c600c4400e010705040050540003140001c0d030030742c006088c8a48112105040c070419100144200c43d03800c920100400e440ea42400481e00d000c0c09924082c00e68041e00f800f405e4140700420f82c443c000c00080b00d0045d0000010f2620441c0903009400c010765018084a0f07548801d00c003010b002d00142d11402a081c866800843d25030301d000304009407910400303044543d4003101c1c041084050300c0c40f2408141d070880200700030900e644a600043d480707422110000c284018180010141c0310a0551001a840d8418890f500010750046030b5940c008004560100388030703001014440c14002c03840300301403066180030300001e00304407003c6000701110940b100303940000e038030280107407081e1180c50580022a0010801404050000b40030250400000750180b42005001c0d99410030a600800e241703203035907000714000c0d007242000716a40d190b01c1489081c14822410441d000d5680c8080c01761a160 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510546654 1250 510545404 510545423
    0x1e130603052211010908010903020c012106170606060a0c170f0c0a0c060905010921080d0209090a1a0d03020c0414060f0103020307120c050f0d020d0522 67
    0x203000d104070701c6600b01144040310804510103200e191a200391098507101e940866402d45000910640601c10b0313450032030b015000b4100e00100000112604041c030781000982c400309021024800c0034071310408018042c6501c60703030103103c00303603e50a01e4280c0c000c140611480041109100e615408000e90850540c410000e09041240c001251018000e016003020000c4011500880018001a03400280d074040c03400700041d144c80f00412500c0020602805000c682c0c014000c00600100b015162400180e14850500390744055440010326031221181180d403d4010030b4001084c60300608541e0006102c200412590031845100c240040e0401881c611031020320002d20b0030b0500a004541540d035008004100e4a542c9840c246001001a55080d01540c100ca400b03512035400b900c00ca0340582c000f0784403808401e00c4050349001804040090600f005800d00c400c44045150b00c000d403074100e8448a000d40c40395880d8507100c040b202e00800755100c00d0344151304007440d01e10815254001c44d0b0840300d0038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510547904 1250 510546654 510546661
    0x309151113240e03070e1306060e01080a0818060a11070b030601090b0c1f0f050108010c020a140312163b0103200301030317090726060a021e13060305 66
    0x285c10030354660300024a803e508410080844150781e0740d004050b1040e14100310454441107130840c2d030082406118181d502c6034240002244841010b4282c0390001348103021100320b0311000c44e1780c5030041c91921340030070841440c06c0c0300e9a6081c410440a08000380c60a400c6240074000240301010a01ca280c404c0440011035a02c0c0000a018600c00390400d00c5080034098500a075440c014014094103e03860381c03400c00003040d0200180510512440d503a401844418619118500c0020510390717550340700d10040041030503842e029100c151141c1102109200810001b50b4043c114694482c90100120000040c0741c2c0c1001050341c07200801403d4900b00079a296920005030014420358102000415800d07050030f0840300100000c5040e00e102e0743d900c00b544110700c0d00303c400d00300080c0c44080280e00008018010025182501c803842903030905049038124440140e1400c0a600b03403400d04040e500025040f02d44032160342a003000f0606802564030301700500020110710300c0c15009540c00c158644010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510549154 1250 510547904 510547909
    0x30201020904240b070c030210021f05060a0608042604030203150103030f05030103080d0207030c060504051608070e0f0408040308040b07150b010c030309151113240e 73
    0x40d03400300c4402800030441030301101e40c940f0400c08150850b15036811101800b241044514041c0e80d02950300c180324500f00c1303041d50308100f400a0000d000c0c0d400c6102d020500b842800700f0000000001d03580590008481c240b00003031268030189a00f040c402c0c85010014040007960315040170382c50180c0c4000c522003004441c44e00040c1841070360f20207035041c4900d800426105000e540d40c00d04883c4245c0b203110014600c01015142400244405801d0b580148950100200c141d001880014428030f0002d04151090303490703d00300c51054070150b45641c0035407103800840d40394004e80c60142038840002c0210518100c807081d40c0c0e007030090000ca01c088811010500704000801030710081d603842009152650384550070f001454012401c2a034000502400c8881720010038031507800300120687d80c044002c074058400360b014001458044886058010b5560201b280500c580d6074100c8413418034950f18407160341c58015002c2e89420804803c9a4061551200b00c200f0400420490613410306d1030700490070200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510550404 1250 510549154 510549157
    0x60501030c12051b1906020f070905041a0a020405120105090601082d0708060403230a0504060e0d061509150f030201140f03180d02061009021303170715140c0703020102 74
    0x804d1700d0002107540d404100180c0128041180a43c0e213400c69441701d076140c0b42d070420f980040c0d4000e0070031490301403400d0f80d075072542501030b50020030900e0140c41c041e510808922000e918802c40d51159641e04184550503d06001440c01802c140d801043c030b42080c4030f280e0019558260002002c405d80c0000c1240c0d25005214000c024907105082c0c41084c9014140540030840740c1030200c01140d18a9035000e40c11052381c0548102a10700e43d1002d04041c20543c0a0303910441044c1200d078000d0505034102e00007100c0d03010701008500c503407081e551b1061401803940250341000c2d50b4240f200009901c284540032100c2e50b003030b084940900e44444900d400540744003c1e0311590103440c62000e000008c2004c40c00c000d06d5900301500c0c1c05400c031080345403003860132601c9000540d072a80c2500d66549040000b42225006802c0c2c071420000780107620b540d25030b600340340c289000c3c100c0700d0039800204490080c401080344070103014541701e0090015a100000100c90b001c00100035100c0d05030081540401d1500c00d50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510551654 1250 510550404 510550429
    0x9090c050414090f0703030801090c02010f0c0302040503011107021f050705061e011706010b0a03061706011715040204180f0c03060509030a120c0302090d060501030c12051b 76
    0x510400c02e80c0d8440040e41610402110603403800d02c510026180800b000140c020101d9800d5034a09600c3e90030b106604018180e50701003501150340b501b90002c44584180b20329501c580864400503511442d00c41403509455644581e030800a000384100d10140e2900301030052070341944c6451144000e0300c420162010702901c01c000d8910f00c108000c0006811061031241942900c3c030701c0107070781aa42d45000590019011042400581083c801003048001c603a001c2c00343e40c0894280032500c1d944600c1005000c007010b03c0c0188541d4401c80040000e40c4440011254032081172000e4484a00f070010700020b42c1303401510090143c2c1c1c0d51005072881c1704002c80c0c1c0c000441e910003c02c4204011608020780b0a8429020643e00e6906d1301010508040f000002c03144d01c1340303140d180e1403490030444401c000100054002a81815000c005140642e6240c0f84071242c20f41c86603200085039411824041d445400b00d40100c0001d90038007028401180b0005411000071880d1a1540841d40081010529515208 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510552904 1250 510551654 510551659
    0x103020708070602180616060b060f120613062709060903020109050d0504050d1e0b0f090c010503010b220305032b0902150708040e0103150b01090303050409090c05 72
    0x314402e41040015001080840b05072150700040781d48107800c0086a11900a24522071314440344104005451034110030364281e40100740b9070600081800b400c407160300929050042c3d1001c80208440351a0010983c0380401046204000150a10f1003100461200c5c84140c1c4440e4400b40b94030000c5c4c40c80d81c005048490340000d040c400b003150b43c0350203030103440241421a542c0c090b02d80320304a482d101c0c80c241d134220364005046510340c040d1903e5074454690100007444140d80740124100100c0c5200b03c0981c018294080c04d44610718044040605203068080c00760b04008040004111210300c45054034103031b03e03603607888000d0011004500d031005060346c1d000074158040401c04200390345810340308452008400780107140d03041c0d68070b4000045480c04600258001e0518172000d101109860207010000d01c110015427801c0e807110703032030140508241e20440c2c50400701c16403441540c0c00d41c06501a485002c5c204a070f51541984d83c090000e00807402002c0d05107035105503080074044407007034000003410702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510554154 1250 510552904 510552907
    0xd27140f1501051804020901090e03090d0c06080901020f03060f04090c0305010609060e010f0b0f040f27021c0e03040e0c04080123060609010903080313030f031107020d020103020708 80
    0x100c0a01254411091007014801e01c010100e094044c8040c01000e4810343d402819120030340e007080710240040c040324403d5421880180203404254503131030081000c0074020042c00b07540070b00d408001001050018409003c503401401422031450541c1c09482d0849000c032100c0c4c8100c400c100114000302190b01005d81030010a410000c103001040d808602980c1428006214032615110307106200c8500f07110337104030b060780858100300300c03526040030b0038806119074111491715030f076889204140d0314990800401001c882d156150303039030800c1d2151030810a0035142581800c042c00001c94004044906011a03507484e6003a860001d0300500c1141c01803c00018a9200d50500c840009220303001801101711541c649500280500d0040781120b80c0358144212441c4265070760ba090000070340202d0381d02c030b045c00210741010000075803007400f40d84140d40607041c200419031b2a0800500f0045102e0814040c145070504580c0d00c4000a0101c404e419010341d6071a0b004006480101c009108074280070382800d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510555404 1250 510554154 510554173
    0x1b091306022101060c030804061a060f030726060d020a08010c030609060504020309070320060d0f050a11040b1e04150207080114150d0203060c0d27140f 67
    0x54150400b400c810401c06182140e0b00e581c3d00b0395810000c00c4002d40803030b2500e80010001001c1e500846c030480f0107486600002420f03480030800355002034145911000c0f000c01000002540308590100030340486400c00c1c03c4c0d06842c5800f0700c80c0000607260758080d01102c2c8041c0155181d00d035084004003002402003000300c100d520300a00030411406080012404c00c440042e10b8505070003668050402407014006c010f146544110b20702a11005007a100d500b050320304101551108040c0a00b10a50080821038030041180ba40c1184d0303008004003a024909481c0c41c56072412502514169004444403583e02c1c03203564860071000600c072102111401c800500420842440307050f00707070380c11040d8007141c82503920b034041242a191044d04034200241c504000502c1083c00da80c5416000c50003030064402181d881d0082401c0c64422503e0340c0011400040c02d40c890b00440c4216589036625901e003100b000403025200754801644e540151403c88000621424030405000e542640b00046044403005031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510556654 1250 510555404 510555427
    0x150c04030c26060108010e100e030a12060801060308040311330403020a06110f19030f0c020907050c0c0d08070b060a0b0c06100509101503021314040b01021b09130602 73
    0x401f0803240d81ca58061a0140100d01c0220302170a201c2c03402040144d8100030602400702c521f43e042171066000c01d502c40700001941142031245d08081d601610100da130703c9007035080c650410014036080601038902c0783c00e00c1d4a600f2414500001d0340c42c50340c40710800c04850f1a034415040c0101d4001a5102c00f9007840018581c0e00407041c01c18010b541000e441540c50340464441e140d1300301401004030400c462a1410000c0e1081d050a0304182e580d0800303094400b030f1900851010b05040711003101103540001d90018402040000c4010701c2000c9900c401d54030303141d542d004194003803840002c00e040c41c5c001c04a0219070714440950050940d00d03603d6a10340d849911480c6c0c0c0c40d641078610004500340c580f804249030404070780c06d9100e65002034003c81c0440c9029088201454500d00c072508042d4240a202c003c1c0c0a00300300c4000520140c07800d4219000c4603400c10044030000c0441c103055600045002409944d800410f0b0141401201d24008950340c031503031040200e80b202e100500c0b0b5071000074240c825a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510557904 1250 510556654 510556661
    0x90f0204050f0307080d230d050106030b06070203070e04110d0602090a0509130308072f010e010903140309031b0a0b060a0f0b0c030d0e150c04030c2606010801 70
    0x588080790741c0c4403100d000b03000385900d8000a0251001c190400010244090300603140c01910160303580344a86070801e00d441824054002100340e9a41d951104010006968140104064244c1c100e8007289400807560009aa81030b0610030381108900d040002814442c02c03002c0160408000340505492041a10300207000b0b5000c1e908491140e00742540104903400c00d1107019100e0703001c2041c0b07a400d00000351000d41e050840100036508010fa0034862940c25000a4240c100300080d1550041d605644030b0703500f07425211603141c1c0c0003181c4c0c50100100d0210780c5c00526203a4113012807640c2e80e9a40c94205c031a0b0b045206064803071966900b80003034158490000503a59030050f001d0380420744142caa00082100c40f80141c401c2d160790503144007042c04905d940000403e00756800c20104c0c1e00e8000c01c49a004151039068142c031400340c010310b000c0e495605110300010380c441c0c940b105040c500341c110f5640701180c280500031040c00c03030100c0c0068145e9605100c6100c98100780f00e011035010f507944030ba00f94083c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510559154 1250 510557904 510557909
    0x6200114040c090507120b03012a090b0306060703050f0f0426010b0303090f010314091c0c15050712050108011d1203040f0503040e0f06120a03020d0302090a090f0204 73
    0xa8001c60b40001440e600e40e4802c203030090341940d644080c003c00c2d003d0780501502c04440695415541c840c440201c04540440764820848980100b0b21318070100d400c045d003120640d51100704141303c10000c1200c20794030307402248c40712585401c0c4540c44040c1035810009500900c0c00000c11a000041c02240d003081603800314600349124808243c25885035032140d4261004181141d8040d4800c1c0f02a080c1840c0001984105400624002803186000c40c40010603c6c416905c5142d00c0d000550b001c86002400e260000c4d0060742410540100003140e41c841c01d044000701c4072403001503601c00100e02d009104403000c86103502408021b10995031103542c410300038000e9862010401c9254050102041310103d00d40d0208511144100c0c1140e0700c40c1c54181882d0400a401c40d10f501040002188081e410707002c860041815241c0c20089192031020301010040c540c104c0300c0144d01ca00d400c000040c0d4009507401400d4220720b809a01c801c00c580102e090300d420f0350011116a801c0c10300c070780480d0b40103501030000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510560404 1250 510559154 510559163
    0x141b071a090105160203070c06200102070f020109060807050702090406060e24100e040b060f03071713021e01020c0d05100b0d02090a0b011202041e08010507090620011404 75
    0x6130000700c2442660ba034410228000c0c02e00710085010000f242c0254244038420004203284150116819810380c220303809180103c0e00c80c108594944250750344800e4000c050510790418070f80728248220007400c2e40c09030601c000d103d9040007000504000711608081c0c01856006040c2c985824960204112060310784955018881c460341ca051171464a4800d803c0c0c4e00800d51038210000000000f4030014218030304815410890400c150140c44c0028002948913010a50300c0c07802d0581d40003072250000780003802c00801c803e410314400c0c0260303840d2944410070b20300e18040341c81140c1030240142e040107504040260700c40c080d100b102003407210200314448540c1011400b001804004020404c18190301140603420007001c0c3c000800a62130780d4445840900141044c0d8403615600c8108030680c0d1298005500c0382d920107000c68160340034052800b0260112100034410b92401400c01401d1000d24070907c01000390342c6064803c0340072049440402d80c1e20241c02400f010050b00e44070019114161030446 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510561654 1250 510560404 510560431
    0x312030c0e06090d0c0e040b0406050105040204140103020a0e0319030e1e010c171626160f200319051c050c010c030f141b071a090105 59
    0x3080035108100315004160700600107810510208140800c0340080401240e003400402808664040f584d10f0103449144100c140d84d070645032601e400e40a903201039014038040c1303005000038030203101c00c980e80310320b800400c0c030b001030f1030708410f500482e0380303e02458446800d80982d03034280310160b010560200100e402900d450302503003411414444081d00c80c184200c070200c410b040743c25130380d8414410900c001c0c0c09100785103880b03074192403029415440401035a610749011607110003003183d80380c2c002001c0401541e5901120343d00d000300300c5203481904501803203859416440e0701042048030b41e400c0c200e0381005030032041251310340b650349001511141040c400d11404050394a00e00c1503400c40012a544100038010028419120398040340d00d0044440c01d2002c14400c05900700024415400315500d40d64020074002c0031030354643d0844041c04850325604151000300042d504004a0107410b1a0428101a0ba40d4200b81031a480f00d880c2da284100002d408501400302c854415005680540d02114000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510562904 1250 510561654 510561671
    0x2503110f060411040504210e090f132306130308010f080d05090406150201050a06050a0e010e0601030b102102271207080709050a0501080601140613031203 68
    0x101d940308022500101680c507801562141400c00740c2045401c03510400f0000400e82814070580001a008090000003034031500002c1058a00800340701d070800585803200002d82440b0b2103000c003500300d03240050b14600c91a40c0b002601e101c040300c40220b00d002c05003170700d00608002d2544680900003040640005104c2c0001145003800c0c184910221210a0014500006007410580342d0707400081d2116030082d43c6190001d0b01e80e0080c07102013108440369000180c0f0b850030302003550843d086504841d00400b80003006100d0150f01c0010a4151030080d5801e1030203a031801d00413000761601002d0650000380202034242c1660b04522040401d10072440703100c20300102d03041c0c072504034044c4c14405001c460800c507210820100c941404a00c402003d0314100100320030383e104034038000c25a0300c80c051a42c0032003070400c14225144501504813208060610055152050b01c0c0e603900810700941b041760800c03009050031560b0b84421212070030401070000d48040c1d980c0c18040d100400305064800401e00b0182c4c40d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510564154 1250 510562904 510562933
    0x90c081b0105030406050a0b060304060c1d0a0306021e0c03041d24120d02030405031903020a1e0f080301051f0207140d0507080a0318030503030a02250311 68
    0x120904810b80d10305043d07075540d880381c201030800a40380001f1950b4071440c8584a4462600a43c40745015240104030150702440003061f68408040e18005500b545000161990710340c02e0160449801ca0005a241c86801c10032503400c600001003540c61030b07000035003050b0010001c0b0151040b82c52000320102d02002105101090100c01c5a440000340640303c2210006d803d0b80d07940320b80c1203034040c202402c04155444500d181184034007800c00540d101240401640c81c0400c008a50340108072400c100303120303465030060741d00e207c0d02c180240200c110940d0361423038250000c0c0400410f40c02900754640a00705041c0440aa4000e025180c002c0403e09469480b0354000c03140a03964640b268010300a06140c4515140a103512089882d030011000c14403c1c00b148040019a000d0003c040c00b410005003e4035002d0242905036010b4082040c1d260020004541e0210030b5941c08440400c0c0035a6844844c000b506000b240002003c0c40802c1d0283d07000c090503272008051212002f801c01701d4180d00f070310121 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510565404 1250 510564154 510564193
    0x3030a0e030408160e151516021806040b010c0803040303020a020307060603080307080a02072004021b01060e0609010617070c020621100b040314030717120705120a1e090c08 76
    0x40d01b40e0800c51640c0c6420304050202c00801e20620802c1c2d44446481080e40010460300c0d508220080d40c103d828180881d82c50705124800380943d00b400c010109401e5950f07880020b000007480a0145039000c140b00260714000c0c000ca81030300341e020604015803a10303480c0c50300858005544040004401c500081d10b90320f21403080703a0650350002d0624124036a011202000041507400140d0450b409008000c485a02c440c000e0001a41c4040081055030800e9881150020000c218034441d4004038010020b00b5000f440004451008401e100c0f07160303a0741c0d44140e6010510000c0250082000500e05805141e400581c074207a01080440141c15101c5000c54817144c500c03809480c1c003060003080200000717000220003c99901c81c8105590410307109440300010194003d890450480c03002850380300010052900550000c17480c01c12909113102d000030000304450040030112119564003680b50201113015480015200d07007a03083c03161000b2031074100c190922520038200244030340e6424000c030100010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510566654 1250 510565404 510565441
    0x1050403081506120a02130e0103060e280507050a060f030c0e060901030f14010b0301060f0201060614070c26010e0303010305151308160b070e0303030a0e030408160e 73
    0x43c180390a11629400740700240101800e02e107021036082101e00e80c40704402c20510700030504190000520b61443c01e08509407280c0200c21a950b80140c0100b041d4242c00d045056581c00d499080f80c1c807141c0c064170b841454004660800be901181c2032200041c810342c415040d4160420503a0142b0940c1902c107400d490400c810307101103074005c50511180310254400d40c00240b15040c50180414072002090070015549000e1300328083d0418000014040030350440c0d1194400802031008202440c0f920100408450800000030510300000500d0310510035a82c07a80030207446400b0429024000f14641c032013141d00307601c00031003165003460b1220181c0c11004c4242d034100c0c1d40001c082c2c01031440010700401c0820f0000e08024040400340b1174103000c42c6d900300240000303104040321411081001c0c00d0442c0b240c10010503c10420002d092a1100d40e1004419a034002401c04000f2504900d1508810305500840c0c01540b0307103205212242c039414401c1c0d04440c00321565560003502d19200c0c460002e03207030040d04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510567904 1250 510566654 510566659
    0x2010f090605191b0c080618030f030a09021305010f050103090515100f090c080a2c0a020301090b010302090f15010c110d0b100b070f0f06090b09010504030815 70
    0x28000b504034014001610542ea056500c0c0c01c0002c3d01c48451030780701106107004d0641e503011071340c0e10034414142e082085171303046000324140c003d4003903001c89925500d00c150307aa5005c00807008804039000e12010741220403891340c0100055a0903809080020003450240b043e95413629080d24005a154003c0c880d0322113254000003c2c008400c1d0f81e10561031131340806000b100382140003460005020081511071800380000c400c000c07595050380c08008000c0030340a8030030445030b0710b010344071480700f00310141400e070240803100d04a445031005049241450300141c4007030b4155007400342c0079080000d40080d86040e6842115082007940721034a0107000110704541501505900082c00d50041d80103906a80e1a01d11907007822102940700b42c0450030407012003030100d40c400703070300024422284180200e10014141c04440c5605205080c0c903404c000c0402da50740a0034210380d00c09a0303c113103c8581c10003c1c0c0c07603801110020440c281007a02034004c0008840640000c4c044c07401055601502d148180c001c0d0301c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510569154 1250 510567904 510567907
    0x20f180406090201050f030103081305040204061707050c0f15070c03140306060f1224060a030e070510020f0115060915030e0f0a1505010617090106031e02010f090605 73
    0x1155102802040c400c42e06905000080c02441440400d400056010314401c070300044d142c1c50b25a00d46004841c041e00010b00c558011b01092042c1580320b405d0380e42e0070860180c3e41440d0344603003a041d00e0030710a800441c0e1803800f42d15030148c000c59001031a1101680c100040200f1661804004c135a0b01007908002800138601c1101c582005a8410117903811840040c44286082c100c0c840745c8110394400e5155041c00c6200780104610b1a5039214102040390188031728101c00e10b030440000b0b8a44c4145921501455034502c2001c500710420440000503090281c1041c1450411140c069940c542d99600c00d07403d58201401150b44030b400c3d46008085070740503200e19001f941481421000782030041401c200b01a65940850301c0030b00200040e500c110f00c0c50014058041050400c040c040038403030070030701c817090400004100e01c55000c07090481e000513080301105192265421140901643c4c0e02c00340c08004090940961811040d100780202352003601c8400c4204a030700002da503103130040c0c0f00d0311012807070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510570404 1250 510569154 510569161
    0xc060c090a0b0703030b03060a09051501060801050d030302040504060b090a0b040f060804060905010606050903070617060120010908030a0b090f07050c010e25050a0b221d04020f18 79
    0x1114014010f10351090a001c210426842c0200c0d07c0c181080310041c0d403040e156503219007400402d00440c00410221146a06158107010026080d44418803a1030300480540c3e42c12801c1c1403003a4191400b40400510030320280b81c1e1141e284029030041c1c4807040c03084903403010004400440e20202d40444a00c26018241035260000c2034400d030303400030000c1d2051510f81050f00c0c0020710038452000a4500c645070141c40e4000e080901d458580c41c0c1d00300700180144d00c82c00380e100032148002c80d94810800d02e4010ba40c1c00041d010b6144d4054100f807206059801d264849003003002800103148254090a030401880400300100418480251120080d07821548085a0028400c074024081d2040d403c001041d001e00700968646440207080b1a580e80703000281b030381440940e01a0303030840103100840d5511001d0b4100203844500b0b04c540c224954014110504101d00c82418400c400d0003084600089481c00d00200307074454500c00100e904034401c1d40c1d07480c600c40591401807040c8407210805185410300d070340c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510571654 1250 510570404 510570419
    0x503030906220f2004020d060e0a02072a150507060c0813060e160303170901060501080109020c070909030c0203151b0306060d020a181a0304031805060408030c060c090a 74
    0x480c400501e110204c4d0140c003540c5498074001040d540708980d0b0001940341c5002e0109034400e10190644e200d5900400c041004500c031455810001214990501c0004d245144004460f200036445020b00c0016032640710107860308900603044c1107018074424092a64000307011625000e0403a0311010ba080c45000290100b03900344d002041d0103118070103c440c007001100c1701c08500081a8000c80000e246044400c0b03100700d4a414150b00040b190000348031481c00c2c10000707084c0700d4050141d00d00040d0b0100d4000c8504808001c04030081c06900000c01982c1c110382402010700320582c038240d000348038284010b01041190340429108164801c00303440d000390300d0080d540080e0700242803668440028440c1000030303c4a80b0007400309565903101c3c01203045403502c4040030110300b41c1c0040505a4100e415449030028002203aa00aa052903e5001d940380070f202c40380301c0007240d0002030700200081804500680000001c00058603880115005170380e0318600501c20788108010550014141c03c401c02044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510572904 1250 510571654 510571673
    0x30a0b0115080a2928050f030c0a0e07030b0904030c0210140a0c030c120915080405030a03051321030b0a0807050108040c091104050103290f0d0503030906220f 70
    0x500c4010501d40e03000205240300020b2003170b80708451104440f000b4081000749403100086906110035805420440081c50024001030324a208850b2100c80740000980528840d5011000d00500240245a6405d081c18010032042031400120300079040300e22404c0781207000719040c0c4202540711140d2440e00913007031022608100800c00c00c600344542e0752400c2c030001c0c40d0201c04014642090391410440d51802004100c08015000d0744030900131040d0034030010400100071101403c0040c200803c03241c54030100c0001030729017424094240d09416005104c0c511244c2c0201030700342d4450b034091021010344420401c1f521034078417411b50380b0381c012501040954080c249442e4081d00825030740a03019551010354042d1855844078566400002909004070360300341c405c090b650848100072400d2050000542d5242044085020317102e91200d0a030075210365241003070340700031603444400d490310790911081c40b9941b40e4041d0f8040c0c1c03000700605050910320580c0c1c0c40c4a950560048503421000b0140d45400280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510574154 1250 510572904 510572981
    0x10612060b0c0d0f08070c03051c020304050115050f030a020d0602120903040501030c030b090f090c060a0e0f03120d0e010b062b050c07020f030a0b0115080a 69
    0x94980300c80000480104001c00b0b401940d40c402e0141c501210300440003060900e4002110060000a1003444510795005203c4e41d0116410304000c0c2da02d03041c0c0001e441e40380c00007003e007001003030000040004020701900507204100100c0503107888580c4440030001e1304054064200d426500800e0050090301c0c1074100500810b0243c00c2c01071620100b00000311021000700d481740810b900c000303030420255030f01d882400f44c015020b00d410130022843c100092001440a0608141d0340310701004a01042c9080c08103441520005041c1d56640366100300c0503003111002c1c40011310860510180e142c160601040c02545404011500d9103004600c0490780020400c0484282256603640c1c010344840c0c54030802068800322030310081e0408101042101c4c0445150300b24903011034101400c2c4400714601c44207450080760304482c40d0301c0000346039001c20700e07202010b0300c05000c0c10f01050000a209015000b19100d0b46120360b140800d5540b480e01c80340a50341c0c01d05100407170100d200b850f82490009055070640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510575404 1250 510574154 510574187
    0xb03070e1c060501060504030302100507050a0f181409091222050d060e0105060d03090612151e08030a0503270114071d030d03090804030f030e13050402090106 70
    0x820038081d1500c100300c510980205c800704000080c00d10034160100b0400a03402a10782d014400c0d80b41285004046000700d0001d170b020320640c8a032080980d80103400c81c81c1c4e43c0748604803412403d540c03a40c050701000550300603180140c81820200c0d510b00f03c0403405610284444580300d01d0100c00740b02586400c08010040400701100c1100820b5540d111550482254000c5c0e101181000b12090703020b00b1035901400301441141c4680440d0006504002c1740303022240c242c14000300d41c83d6011040c10141040303041007040ca407880301d004520b4541c44504100b54140003c10030b904c0d030b5140c50030795a50784580c9103044041842840080c0380e0070410031001c14031513000c03104012440340e070064041c2941d121822000b0f25010402c204241143c0c410b1402d69541002913a4014018038107010075165180004c034030040549a280b2401404040e004480056500005941d0810f40c2d81c00e00802612901c0703e002c0c800d2031031003c49100c0032001d02030180115001091110305920b0f242050351900480307041d081c2c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510576654 1250 510575404 510575449
    0xe06040b0301060c140a111e030a08040e010602120f09040e030307020a11061e09040b0316080129040905010e0d08010305060c030c16051c02160b03070e 67
    0x400c4040000a54000c0106440c0c1022080700c501d032070f043d42d1500004080d400d60110741e441000c01d60009201020780c800760382110043c08414120324010252070303482038152203410501c00821500030001c204480c2e8040031082c2a0340c82d45000c90310b5280441d0680840d100500c118490050381c20024000800024000a400801c1220041c250303081100e445d030260708200ca60105101400c0d05801d07034140101c42243c40d110b4241d0065210309412031240025010101d0700d1002071304e990384444541003000781212186c03840030142006443c514010703ca06542010b00418034101e258a81e2507000001c80a458040100e80c0140001130403ca10140c410b9902c13041c04c44010603040c4648240c0c0100d035922000990b056003083c901d840006450455604c6080003040401000381d4251030018890a40e020092402d60401380c1c982403001c10072f181481844030341c070021190005541004048403a02803000140d42c3c0280c2c1c0c0342404100e81d03030ba000ca0705904041c000ea01e08035001079400c8266070b5072007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510577904 1250 510576654 510576659
    0x30106030c0b090f091909020316080706091e06050a092301031a030a1214030a061e0b090114130e041a130b181501090605041b0e0604 59
    0x20150040182d02008060b000040c0c0380609003084451060ba984045e80c1900e150b0500104203641c1505075003040110980c2d40030110704541c3c06100c045848149010041d4029071907004494550b80789115010100d03045507000169141241e01201c4c0d0050b40582c401e15885c5003a10030b5919505c4050f50744c00b00840b129001c03c9048945600314250807040200302c0320028404005811902c04007804034010035a0001d00d4000d680c009020322499030b01034100c90300d13405640341c1520342c0d0074451101e407906040030080003844001580301d07404481d103041e000003140c45481110540140c140c01401000c01c1d04219004065000d0488411380059103d0398901c0c060751680300c05c40d450b209401c240100014038041c001401481c01c810782034041041c613611105c1c18070384000c0141608605000b802c0d0404800018442c40e12194a111034210010a4a6687c005a0350006208209020744c405591501e800030845090a00c507525000030900f00d8004001e0030a101a500c0a014070401c03a481b80003004003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510579154 1250 510577904 510577913
    0x311183c011502190b04020607080d0504151410090209010903020a0b07050115080c01080c09190303020d02010e1f090f050d030b0f060306360f090f071403010603 71
    0x10903008084811200719100101c81d0b0003410700402e0042240e10788081c0701880040341085150942203a41180d070f10f0b5403600b451610b1592070068294500041e0310302410441400b4410208100e01c0244010030000b074164030344000c88074641aa2070103010030a1110902100040b41e0041060620505008c14038590380da0021ba00c1c00c120307800a101c0300c0b10101d01c00b81000807d000e030f0f5411101c0c034504000c0c10f0b41465000c07036030351030740c00440742c1000030240100d6000060003040307c0d15900e002d070440404c803405081d151020b440c180700c100c00500c2028501401c143c8180b05c1c4c6281e22110074054a0003004050400c2c01280c1510000c05000e541c801c003542c009a2500d000e110241e00c9440070b4154400110745c09812640400905802654101700880e115550541285d030300240440368400c8011807030720880c41c9052a40000c018941c2d0902030188100c030040382c100d2184140040c0300c83e0a9035540d41d20340d1642186040c3d82000c2c0d10126041c00b20015440c00e100f40904003a0002507840da50b40c07117 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510580404 1250 510579154 510579271
    0x5090f030708040906060206040503070f02010e120a030f14070f172d180d170a050717040515030421030c0e04091e060b030304031118 59
    0x448240c0d600183c10016900940600701c001c00c81c40c005030985140a443c2c40d0346a104000c030003001b2010040100e0116800742e0808848458040d0040e940080410284d9039180e100c1a000d50103d203c4056000050348900c1403401c404d6040d105150420029a94420300c95800715805c60b400505088404070340c90284001d00740c1000071100c0e5070410316640359070651001014041e440c0e600401c02c0300c1100e5648450b0244034100c0300766400c2d0804113090a24007080500c4003003500840b0400030791213030400d03409006403007403602805c804100e210481c0c1c40c080d501e100350720445411081650240050a1515014652250080e00c01020030324001035002c20b103228a10180d00030940d68510003004540c010800c40c88481e09480802c20301c00103884032a408005580048c0b042c1503008412001c004540e0480302403d64058200c0b9240e0740c49140c035043c4140700c919602d0080c107103500006c000b0850030b031317545c1d0140e411505c0505c0700401100c0d099100c01c13210b010a081512908480d401300440622 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510581654 1250 510580404 510580417
    0x5190b1e0c0d0206011502060723130602030903010f061a0306010c05010f060f080a05120a0e04060308090f03121611030a050a020a090b01051c090f0327030f02010305090f03 76
    0x50213030140350304203242154807524809040b011980540d00300100180c0100a9050f850201d0520607a403164860030207415118000d081c60202109050001d0102e400201800c074020f000c45c02400104080c4c0d070b01e901118203500c61204000c0c0f2005407014110804002103400c80010701d403082064256841e894252102c0c4080c0c1c864195488404000780c0c0304003550743e40034240b103001a101541031501e66035950f100031640c2125007030380010503405c524002c00310b01c0d00101001c4c005000103030340d90a12011700d4124130345050007000228188003c91501080814030300010450032800d240448010b9003020000580440d840401c0307284600c0165010030030007054920480062044010074418400c034034a00750700c25001d003414406445613607a00001551040141c260801c20a017042e4500140038208480000d4861b0100000d081c091544c440e480f00390000d01032510b0060240c25040c00681e07000544000b510b610452043d500056109030040b90b0041103090440f9841c1008100c0d0609661015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510582904 1250 510581654 510581657
    0x2031e040b160201412101081b0904080304030507020402180103110a1d03071508090708060c0304140705130209090a0b0306010b0d1b03020405190b1e0c0d 68
    0x301d21103021980d00000da400b6010800f02e00b0510798030f0007209000031006491740c100d044051002c502d541803404105441808103001500f50003404007030442d100c600001c0c0256849400f61004411034500041d030820348840c0c000e00001000c0e07440e0b03103c443c040d41019000300d04010081055038003503901d0380054030782c40c03034241403031901051a1000907044804500d20520104010f000d41841c3c02c1e04030094107001c200b2150081c1e044116800040e090948680281286192039800c5403411540050f5641c8650100803c83c2c51a40d103401519503556401c0b5451901c504081002070009000d00c070314641181c83c040200c0d01440d40710303c001a0360a10b616070600d10b0940c0890001118503f00c8a03058101c80c100c1001c2107650840b4022a403103074814014a058a0000502040c41c0c040c558000e5031002407200725590075982c207502c014060341c4980b0600d0b20444008441007007480c5165042411100c2070700e48613280c46203040312658a408680c001048140040c003850384002c1c810300c00501201000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510584154 1250 510582904 510582937
    0x1f05060a080601030c080105030607050a020f190b0a050c0d0b0612010b0d0f020c0a020d080d0e0607030c110a02040e010605030a060e070609230d020d050a050f0c0102031e040b 77
    0x40001000c0711703072025440c810442c00500420864401280982d0810103518229035618030103a410707480c18208220300e42c5180301c0c02c69a00d040440000001031007078407034110b00c0c84640f036004000d01900d01c03c3d0344d003141d45841084a071000d10765950254440940150000b0b040083d034005281840a00b60700500c0c04210001d03180111a032544110980d5051404046083c040340c40c07401079071040080d40c02401556001e1405003403150078000e945040c100420f043c4480d02d00b01000c151110342c2a1510004a4140f096090510740180b4054406d15400c000400041c146902080080c1421324103000e555540ca61002c074031070718280651402d681c00340801040911400d01658901800c43c0d0001c001c0202e5242d0510502c4071010100c2c40c06d64020400b403004188100004401c0c440c5014001c0d84102202c40a01c2008004641c42420900910943e111440c00b02e4141c5e0720f1342c2556281500603003003004010850444504886201d041b0802c0341c07800d107511994070301c01c0ca0740004810590340300e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510585404 1250 510584154 510584161
    0x80d14060402120103171e0a02060a090506060d06061a0405030709060b0a05070203010b060406030b030d080115080a06050603070c1401090b041514100f050909061f05060a08 76
    0x4482000e030030880a90701103141940c05020402002c4060000500e80420410300603500c00985007a5201c1a06401d560307800400ca039907c081840c0c0c00705440b04017501481001079507201d6148901d9810fa5000005007080340c2e203a42c200100e110142c0c0c0d040360000d580300004100201e6041022034001c60a009060b40c46040004140c68140a540310303410b003d00f03202c0c0c207000b9501c02c64143c1383c0803206410401d032140010320000380540b054241168004101050008156a00d60040b0490391400d0302540c00c00d0702c140038215802042400340d050a0100a201017a6071486a0161130b4001d0a00c5400904581c88070b000031038030b80c0187c50420000d1428060003085c001c45003041c0700c0f00320199000f0460030f0640c0c2e0325061120740041003d40700303403c8140d00001282c146d411294403810340d9a204030301803800c00c03204c45094440340508c0064210104010556041c11100e0138028028240200260b0fa244000380b44c681204440115003030030161030009042c0c6030350000d09210310300307910380f50041d14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510586654 1250 510585404 510585431
    0x60a1223010c020f0d140307050c03030c040303110a03020718020c0703110108070e100c030201140408040f0806011d040f0c06090e090a0c0e0601050702090f06011e081f03080d 77
    0x1401d001001d40d00c1e41180c0c044842c0300ea0807105441184817011a01b036101d0340c5100060724140103100301001980000001c12074959944002401920300c6912840140c1020034900c80d80c422960b04000c0240e031000c9424810030a1400c1c401904280315100580b6040c584103c00d42481000c0d0701c21201c448aa5004030304075a0411034569012106242162072000c5800020307807104402c100400c00e10920f00c1c501e00905100303401904030160790084080311810b240c64181c0090348584510040c01c1d000c00300200308070102040080c1282c48118852840c00c0314207d040810460260040360385400004d400740001d1300c0d00039400c00a1120740c5904613000c1c039040c819030410400a085132080d4010300049400952001d144030150ba958a42c040740c0c03640c68400581d118410904069400460344040018000300e81d501d83d481181c0030303030b6801545141c4020074207600b40450049004580c9200010b070f2004d81900da40502c11012451514826a51751180340c030650010f1000c04045807505075141402 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510587904 1250 510586654 510586663
    0x50103050c011d0d030519200d12050a020702181504060e0403120b0301020d200406081807030209150312131e1e031109060a1223010c02 60
    0x56080c00c0030b41e81c40085009914000d81031400031403140b40140880b4050520030070944011f003004240008010b036096030003400780c00311041d5888031807a1260812580b980c0101d401c051000740c51b120050621407901c0b1101c0509401000304144940c2441031802603954031802c84600c060b42c1034104510308203071030359004144c040f5a256001d40e040210810074030040900c1076901680615190b520301d820041c240b000781003030608d6283c0c15800401c0128818469234170047e41041841c11994050a040c0130940d000e000300c0c0f081c1808586041700103081541400c543e5004003044400303880510f41ca0750300107014480240d41d0504e19000000e80d0741d0352814104850a80080050171182c10200115a01118001c00340201c203400314a00840d03615220840c20064060615155200100100e0319030621200f03d1611082e10500c110007c2400103081888500d400344001418104125041064008105031401401c072034a020701a9116a05000c55800745524014180003148868000320020f291 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510589154 1250 510587904 510587923
    0x2040c05030f0a0911010e0301060509010605090909120715140c0301050f030615060c070b04080f12041211010203090a15031a0d12020a08040b030a0c0201020a09090b0a120605010305 80
    0x2c113407400585001090752080d042400c03010074680508002d50100219000d030009600c820342003c0041c002142494209000c2d0402c510191b4a05d0020b6880303222855450f80c030360360307240140c0d44100800000f041d41d41000003002508030f100826480c40740750b40044e1844086500700e04440010005101a00c1c0981c410400f01508800900c2281080902c100e2507440944090b03210744000280c1250000040c84150000e248c24919151a19510000e080e00d90301661048511401481c0140c0324046810007a18150f0742104020ba00c18021580c0e0644036101c502c1c815810751200b48981d100b2940d40c02d0303e00c0c01501c0e10a0140c1e00b000b040ca400030f0152040b4a0f441c01107030a100075605403548540f421b10001c150040d005000c007021145090b81051103141c005003100380005408550307500b0711001180290750b0070600700300801c030b9448120300700e0240c0c0d06030380002024294104407a01c0c10f0341100c44a1003005118103451607a4010102e40b40e061150221041034441c40100140141400003044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510590404 1250 510589154 510589171
    0x3020a0e0c0f0412060e0f060c034215090105130503010f1d01021e18030a0302010204050f060306090a1d0f070915051005070326090c15121302040c05030f 68
    0x4400c401c0b41f02007511140e00500c01021240c000c030000c0d10744079000783d0307001e00610500070307200110300d03c690034203400d51804054000655207048040e065007001c00c00d1b1840446c40842d103e0910303000000440e03040d400030254001034070050f0b00200d05941c0c213101c4c134081c40049002c0043c0d10700f071050f0a140b41a0868203402190391041c000c41030528400c00140021013000c800c0995103a801c0303006212a1481184544d1700362041a0040e010140c05500520545604645a581c140340d45810441540300848140e03030030291102c0410b1049030706400c0081c000403c0e40c0f041c0e240460314114645401c03644600c20140340d0003007104010282c0310f840780342d0140800118152000e428480800c480d4400252620100040020b0040500d0710480300100c85030040a2400d0075014080c10118400c2010307240b5400c2401752038003418640c54041003890940812010981c00d00003100f68030000711710000e103890261f400046602005036694412890901c00f55166184c0320f0801244080c6031240c010503102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510591654 1250 510590404 510590413
    0x40201170f2406040317040803040f17070513020c0a082208030f07082203080406030e2a0f0405010b0a0f05071a070c0b040c0513050103020a0e0c0f0412060e 69
    0x10340e0310b4940484d42540d03080801e041c4030961081c030b65440b5101e1036014000d2800045408107205071169151002ca800d10455402c09210001c440c54560381c080c4a0030f0fa0001640d034400c900c00200c1c2c0c000d0103803e000d640584d44901901e80381c5000c0e9078441501c0e406114101d0381c1d0084c004401c0c0c185035019141020040d03090041400d040c1102c0e00c81c0c1038020b03000070f402048541c8a803910f0b0b840d42d04c2c1d80d03020b0803090212560342c0c50000d03101d400900920000ca03040a00902201e600029442000e89031910300017032147e1140401c640b00d2004030000c3d42c1180680300201510b40300c90198600a0100081c880c0c4e80c0c400b006001002c20a503003d1000400404114420226500c5a011814521400411041034483d00020b980e040000c0c0d00041c903401030442000244442c0f80c0168045540540d00045002004005030742114005d0100a520034421a0244660740b00840110f40c000b02942c1c0d050300c1e0000c24524040690883e40c030802d51410291075110030014507002d10009800b4050082 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510592904 1250 510591654 510591721
    0x1a01050118061d061b100f05010f06050f0c011104090c050703140c0309040203090d0f050406050711010c060c11250314031c0501050f120c100311070303061e030f030503040201170f 79
    0x244014140322f908100040450f84490b0358031910100c03149000d04d0b0b80204020b00441c5c1020303a0681180c8100300c8068901582c1c1c00216000781d0071620090762503a0340304900041500000241e401c82070880e0401d10041c802d030303907040d11144011400799a00f100107040910440360b00815030032005c0c00000070498140402c0000e203411400740c80c00c00c0d5010700c0e2200c8260100004803074139101e460020380040c0c1056048680d9980081c0751000b00d52241c81660651504c0100040c4e05080d806d0090b2180101e021041002c04c6510000d85030740c06496043d80d00e0424480d6540c03d0000d45515243c00e080d0b50343d80108450b25004020710340c0f810040d143c154210155035505170301c484150191901440a003260740c10b500d407080e8071248400c0030008a440d1501f00500340200241110f00541c6140b0000c8050205840c00b1240181c0869621a4640e02c4115056404580c00d400c00340040b4140907242c2c00c40c0410701c4030183c04030320600c1e013004a034569140000b240464200c41036801a40c1d4401400403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510594154 1250 510592904 510592919
    0x5010b06070b0a02071115070302070e13110303040f0816080a08090d1a01062106030f020d110d0f02101e1b1a01050118061d061b100f0501 61
    0x1c4651003c0b0401c00181c4a060604151100c0c0594220040e80511a80d00740b200b02c2c0d051030050117540740280e0882c0c600d680c13981c4203990200d9042d140e404006001118003400201048441c003400c41e406011f513070505544000310307d500c8070b80c0d401000b09508280d560485034500626483c0090070110000e2031040c5031521102482c1c8134411803640100d9542c03120609102c12030140b411101c084004941e407541e0b480c10004e12101d110083ca03100c80683ca0200d55010026000c0e020907a81c1200b138050510340241e00f00003074000800011900c0c010101c541103203030394074640040a258003c4e680d07501014060b00c1004086503422601205025001c8644025800000c2c5e01c03408240013410003950700010540114248055044010030900310805c210704040f00ca4006a41250390a885180128004100814608005020701000222000d28641e6003207046280358800b80f0014002030314101c60705c01100c44141c1220f0401c0030f030750f11076000e46101c0d0805220f828030428681c0d00410965052402 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510595404 1250 510594154 510594173
    0x32e170f0307021f0c12080601030c08010308120601090819060609091101031a1c140a0b0c030c040918020a08010b0609040b2106100603111b100c03020705010b0607 72
    0x50681c0043c04003a00b500c13101d00035203103050600d400502041d201100703900000e0218070708032115400031341420343c00000d442c044c02e100e81c1601c2d40b20b06914104941c5040641c01400024a818100200801c00140d1141c0a2015084040d80503a00c0d03903003541981171001c180d0b803107544a4425585480343ea02e01041902d40724000070f40091030003145401114041c000035130070f00a070840e801100284c00100310380040a807644854410300410700401c410f1144282c80301085140a8051140d94001504520441d4010744c2e000000708416400d141c3c031084040201c42d04800c0060300c0151100c0010b040d0324103400305500a080400003840444492804a4000c3c05404a024041c2c1d44410b4541000e50790070000080a04001490722103111986414640d5083c0a480038505411580303004a2814801e0048210822001c2140380c9804506804000040c00002506119004400302a060907405000d000042d4146980143e01c0307030f0b640d0400740c2c21901c4400f02c4d140714000030410000024003080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510596654 1250 510595404 510595429
    0x810050d02010e090a061d0f06040c0503010608060a030f030f1e120b0d0602030405030301150509100e0a030b090109021906020d050309120a120b0d08032e170f030702 73
    0xb6803a0829846020820015041c0d90300180d088000c517002c0b007c05140d1054901d4031680b0341c046074013016102c40c0140003c440d10821800c0004508000620143d40038041c0542c101001400d080700840e581d4454011002180d201100014018901e00740c510307610240d20301d41c1241e8031004a10034504450080c100a044107040720450b510745c861105942d0301c3d1035401c0d49c0d19810010940d9285414a40191658024001c126014500402c0c2c220858811000c1e2018100301400452400c0e110305429610001c01410490348007004a4011000440b1102030700e020784100c03400440c80d20203601c104801c0961100400b0114180c18108015003075001602481e021600d04040d03030340f41c039411005401c1c40d03510025201030300343c005441146282d0081c0002206500c445c4208000700109040000d213030582e11000d09000130030300c081061464404420106d8907045e07440311000c8a0400ba8401501d0340e142d1262002528148000070040b0042c040c00c1c0b100f407201c001039071034a925035002030440308015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510597904 1250 510596654 510596659
    0x30a030f090503190210060e041401090507060f090b0310151106041101030b044212060c11031c0209210f21091903030810050d02010e 59
    0x80304a4444050554440101250490103403030b601c0050140c001964260074501000510440b200304ca440981845594240d60301c1c4600c46000d03840d142c41e00e80c1c4108401e00113102556881c1034a0000860420141c3c00070300260700c82028683c2c1d06040508618081d900040d60a42c0070410082198014098207055440c00707a40900c0c6900380000c21038a03d043c8000c110040d105900a00c0140700b00d00c01c0d41ca86200c000d0740e060006400c0c80e0b0502082c0e851070340d07601310380c400d0b407940001400408818602c82d2044000002c081548503802c50b00b150f000642c410594540c0e10364088041c060b55000d50140c07518a420154060202406403968038814558103050420548220b46141580c0c0d404440030000010f000252a20064803c2c0040c1411201910700714130038030310065000b101c08103511841c01c0e4041894000e003440950500350310b40c442000340d0b50103003a03600848181e50340d1070403080140d40281c2e0340524500d0010070140c2c4800098210360700c0b079201c4054a80c0140e070301000305111510103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510599154 1250 510597904 510597911
    0x20105070f0c0305030408010209042016020f03010c0e100329060403080307050306030f0c1516140f01051509060144060901050619050f0d02030106020f06010602030a03 74
    0xd400e240b080e6640c20303007005010b8040000e0028a000c01500036046c00300d001c450800450002461000e1810040051004407000910002c00ca1703070f0340c00f10308040d241c1c009003110a6a90966000908507280c1d01102404540b19456001c26818140440c80345440c0e941000c010180e201030b101e107880070340c842104880900b041c0c000c005a443c0c0e101924010350703024040f030b130302e9007171000001e4401d8108564a0f4020301c1180e44d40300c4642e500048049440c9400740114414038464210400141c1c80300c0f03018200e000001914a00003640c0300202e84034a102c3e00050301070010314014a0b42034800203046564881c1c100c0114078025502d202c0b1040c0c005401342410281d01d1540c0c4010003c43c440f02445d08505035490010440031054803021203441ca03c00000c01301203070380e02410402142402c0c000c3c9600004240081402840c41110241e4184079a050a5040034150780c80d841c3c0c940c2c4008003100480303070040700401005404012100480071600f000c6d00d015814018025982e0090002e55420541c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510600404 1250 510599154 510599183
    0x2706160807060902040f14090d0503070f0c021003091703010f090903170f010812040807030602090d0b10030c170a060522050f0613051002210a060801061202010507 72
    0x82c03640520710307183d03001d0420300208a0070068030b8010f01d4100d4076060780310381d0040081c00903080401c0018020149845160550b00c0d20541112180d030300c1c2c03007070304140706440ca032540c0940e030746407038042c1003940f250b03000b054940703061903d948a01410040580c1d1b9640620060000901150908080c0c490a040c001011a0380c0e0030700300c4614001d0043d1607200c820711000c1c840003006a165550607280c91004854414041d01d00e4034206110741d01c03482009401c45182400018415002071001c014010408c1e4011401521200700041058076080d048546030340c8100100250342d00586c0003000007190b03250800e21524103054440c00000e0000749255541d40015020420076464044c0300080c5150003040d5032079901c0c02c02e0740c541a014070700c609403040ba0700083c4600141c07502244482d9118010f005019a0311490740301a4116038041c5007002c80682420341881e0622004912950b40700c0c1c808201c00340790074800d6003100d0643e0085000c2900e40705002d800740c0d800804640c0c1603940284920281f14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510601654 1250 510600404 510600413
    0x10519030906020d0c0309060b1e0925030203160504030f06050901060b0c100501050301061805040c0e0406090201090918021507081210060509150318032706160807 72
    0x200d900c0e80c8001340792400d0074100f11140c1c03551201c1c85185c410441004014010410400300e18644461044054000103855489040000d120703a000901c092104000c2060141c40345d070082e008a0000002903030100401800054501d44000d00f01c1490605914180c00c0d512034200303321618001419550300d8001240000109600c41c00042a1441015480e01c95200d550341d00c0d946050030b1040a0b82c24030002090619040c0305220480340040144bd02c03080c0718410760030140000070010b03905501c880c10001180001d022045124902c80c0f10002150001c51001414080040d0840a00a0b1412800314413141c092091401c1b43c40e0100d44a40f03007008502c2c0e030340000e0700c140d1400404064000c40c0da22412252029064010140d1800422506031a054220340902804201a90126400000c0b1904642032802150000081c450990980040c0703d02d451075030b4850a91007210740550581456800404018441170b81011904640f51130300904400a882c0b20102c005001617a00140300c00800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510602904 1250 510601654 510601657
    0x305180f060a02010b090f10050108040618230c030303060f0a0f170708010e060c0901032a0e03010506060406030c1716090506030402031e070e012301051903090602 72
    0x400c00200402c2e035a80710010001d01030310141250b9802400b00070042299080490740d03a41c400c0c9250000d0001203031a0500440d80e550020700161540d5984100c1d0703d00d29103003030a130310301464060350f003e112a41e203020403400740c24905500d0400c2c9070813203070400300c5596010045070741044040710310414140c5d0000000780c40840c01c3d0b2140c40038844003800000c8962100303c0684040c00032a094503a0580d0781c0b08000d090350b541e10b000c00201c1d004000061400001c1344050700419406150000c1c044003c0540700904a1201882041001d85223020b51117a5034000051604410190024005c504000000c203c15020300d009020506485408a400d807038440e590043c00d1a450103040d44142c2800565943c10005200d401c200182c00303420b02280341e04140048070b0040e640680100302c4c076100d0041d0251044020501e0a0075401001000036940420482c014003903c081002005070a04210008442d4221400c907507040c00b00a2000d06003121020030300180b1490f860801140c5524030b498048020f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510604154 1250 510602904 510602929
    0xa0212150a05061b070e010801060b120406020706090f0302060f0115140c0313030c1401050f070f2103020405040507020601050d1401022106010e0109080a2909151003030518 76
    0xc511039205c00242c5071400402c5103040f650303d07000030091a44c81d007032039012030300c00c440948151101d940042000110303d1742c010702e18140100c1002a6044855440145180c1c2003041036005a020380140060500030301501801090300996940e4010780c400d9005e80b09007440203200c60a1200071031030481c002400e00849482090366588801440d4480c80c0940a080070b901888010400608030820a540a80202c45050650164072030a10906980d412501c1001e40750403241c541031094108180c0380f0a031214680c02da1923441c0036031a1401c044c00d10017251001413610085500c4600104200c1e00d07085940c114858101c1c0104000c0084407125038064070410781e0f480810a4408080c200050448541c0d50140c0c1c803d0380c07003000e1242c0c0700004456040ca21b018171a80f940010700e5080000f508410000b0444408060118208118400d04801c030702044490351001e81216580d820301041e4624000d500014038618100780d6411078034014500e020b100c400b08010110b414514041d030307480890320142c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510605404 1250 510604154 510604207
    0xa06090809190303141201090218040f140906010e040b07020a080a273f0507150f09060305090a0b040302010b031e0a1e08030a0212150a0506 62
    0x42d071488405610200b0840c401a800141c0b8500500060983c0c2c000701c800110100983d40340c16401d18406900035800500a02c451021100c0c00c2520380e00e541c02044a50010f0f10030002d0100c40e4621682006d0f6401040140540c22940041c0010401c500700103400a401a9440742c950ba82d64500341d250078000b000280201d1000328902046981c03041e4140c40952002114034007803a04400199501c510600840c0c4000301e006c00c07010682c1240d044a29040700c02c2041203003c000784001c03000101c02400300c3c240c0301c54022603418081c424450b840174101e1186460300500c4d04011000003080780e4142d005a90030551180d0128895507410040040300d44c1c1c02880c0d4a485092030b0ad0068002c100803800f149c041d005543d44050708001c00d0007000b0407156000302070304d260881c540c0c428030404440e10300032203401401d602d0b084c042805540a14414a00c44200503031f60905010119624040140000c02c00800c403105c000007600c4500f41c2c80100d07481a21002e856090030048044201c014800040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510606654 1250 510605404 510605419
    0xd0e0a020603370b1003090b060103020d06120c03050c06040b0f0a030b1e0301150605070b07030e07170606061602042013140409030503070804050a0209070c02040b060a020a06090809 80
    0x301401d01a48070801100c01159070684000766002c040d01a0b541f4040040c10611322440003986c1940a50000c0086c01c3c070815000914030b4880c2c0c142001c1038007601d01514042c0c04450709100308817080080c03081c0769908880302c41c201443c0000d440c040d4400d1800c40b152030300340440d65900c4039001342c103c8894100c004120b00050502e8201035403600283c2c50301988a07600b00000d0f806060810b00241041d900e0300d42e18a46000b6898452002700a00034011b10200f6907203081c03011181c0803d01603880a0300c0484206000380744130314540740c81e040002d4203a81c400c0c14100200e00c0d440520252600c01c280d07060310003140c509a501980e0b504a20359080c5c4004240d000103850b885115142030701d2017591b40300d0201205000700d40c8240404c4400c0c1250007008500100013003003420b4001c140503031303010b4821f004413251507001d40e02094501009a40c0c5030085006203524608619190240d180495010b0b00c5160810f000c155000f50703104145400039092030b83e55014102400102400c80340003140140000c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510607904 1250 510606654 510606751
    0x1403070509090a020405030d03090512030c03010602010515010903060b0f1f0207090507171302030d05031504090803130c0905040b07020f010b090105220509030d0e0a020603 76
    0x381040e4021111580b203a8010400941c9404031403098400b83c41000d0000c1c40e49182d0a44254002c081c00001035415210b010391002d803100348080210f2090000d02000e689a500d0050040d007503890141a031900c1c41d000d60405801644e0000c000001c13030b6000700000c1141c00b128400304500105440040741c02c45650300e1420300e179a12a40b00807807544a5070b42202c98107a91244004110f42094031030000042800e1958420702c0b04400340315821440c0440010680c08190f4001303440c02c03168079141d1003c01d0022007040422607060565200c00a42a40c0c2404080c1c03183d59401014440280360b4403101d140521071000380300381a59004068000920b0400407803c017800c0c038034060740c030440701e8800601c10003140040c02c03907041c01403905602018042c0d00c00c40e401c08080213a0182901600660f0880480110491419502510380038071305410207161b40705c0a580030f0310180d900f036115801c07081c0e0096142c000140c0320b5008890f030099290103600d00c031030068180035007210901c0782e000700340390200e1512 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510609154 1250 510607904 510607907
    0xb0301060803041719060504021c0b060f0111120a02030c070b070c0609030c060e0409020d12020d2604080c0601030804060e180718080a1104060602010e0d0f140307 72
    0x100f0644d10740e110429661840403682659400804a2a80103024151171a800042654101541051004014102c00c421054540307480072a00502a140249400140640d5042c4041d002800007020701e401d915410b1100500c5a0310118801d0a1203040700c0058400c143e24404d109840e05207040c1001e90703800c00d9481001080d180c109110540303005010300340000303490707004d101a1003c0300c1d0f100805c0d4242c5840c0040607101c548803002d072035800c01d0721840020f00680e0f50358100b135a010300c1f50030202d006200c0500000d15040d8a943d058041c0042000000251392180820010310412540280c680c0c2d0f4861529071468022080d4640d950b1098200103c20031038181c2c003400030744140e039546410110144d0200000c4079006000b033120240c03801c0210300040d01c107644001d4000c1d0048010016a6a140c83c81480d1003e00307001500c0091054001c0c601e540307018005c4030001c0150388001d0202c0b0001c002340720303140c09502004005011240c00200324060068503000310b044000e203d500c0c1c4a2a20940 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510610404 1250 510609154 510609157
    0x8191e060e010503010e0d03050c0d06120b010509070c0b0606070203010c081b0a09120c050a06020c090f010302010e010f230a0e09360304120c14031903030b0301060803 74
    0x707a00c4807140441e001184900341407285403a00180c1030020422107641c0c0c8003d034020107000d4110454031104000c106840c1946000d050000c2c048080c01c18240007850400300b81e5480d041e0403080c880d010210600400c0b60707110398004160354100722000c0345038030f41c080005e081d0311500b07100035015400d00c0045c0810b0703a0803428051051580741c42d140b068040402c042ca1081c421030980001213580d0f0f11051250301403603441c0700503061082450007242a242e0000501c20145648084016842004030250030f041c414031040d0021329141d02100c655055a001806070724800b09081c0c1001890749a0a40c41480f406002c0c03000d0b45030220070b86140c03d007440e030303906154828071011001c10500c0544203000d060644600c0c0c85102d92007038244110b5018403042801e00401500010b40409024125a040d402440244002e0424030319112846040746481a81a0030590107407851103004007211940e51004aa06506859229041c001d242c600d458103500926980034015003542c40e00d01c011a04460000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510611510 1106 510610404 510610409
    0xd020a030e10050a0f06050d080307120c08060a080d021011070503030a020a08010e010f180e01140106090801020a2c030d120f09020108191e06 63
    0x2080507141600920a102c020b0340c0e82c4080c044108064810548003220a440034800c80b0320f8607000031310000856501410350200040060a59032140105401d00d00302c0c901c1c200802c0d402d4071001012600d04035450750050081c03403804192403000240a00c0c1030f064a0b4000d00c141d454480010000d005079030040e41d00c0000510035070300043c800380040d61044c20840e000503229580080010040541a845000701c00046170044c0040d001c14801da5060720320488035043c41e80c43c101440801090841e0481506510740049a01c0084503205814101d030820740c0c42002c04c0b42c03112003d40c201e200d50030001011442ca12404e980f1914440c8481025a01500d0582d07446a103030408a430515803441803240c0080d00d203000c0c0108507805441910003240e20101c04000803081540060203002d40030f402c41085403810450400140c4a0b03030003d42c03800809011125142c0000368010002d0310660 = true := by decide +kernel

theorem cover : BRFrame.Cov 510431654 510611510 := by
  have h0 := BRFrame.cov_init 510431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510431654 ≤ n) (h2 : n < 510611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
