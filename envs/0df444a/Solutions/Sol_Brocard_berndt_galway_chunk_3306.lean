-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3306
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:16:21.748541+00:00
-- url     : https://prove2.me/submissions/43e64957-5d22-4144-a809-d656869591c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 594424460 ≤ n < 594604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 594425710 1250 594424460 594424487
    0x706061703220605090904060e03190e011d0d1103100605122a040e12040f0b0304020306130f0f0b0f1f050f030102040e012603340209040c030302060c0a 67
    0x12003210004e014400c007507000010341d031030b0707042525500c0300c850310000e840bc02e07002e100c200070400c0c0d4a401c0d03105512a0180c00301004004956a07240e10418041103004402d10b9030803100e940c0b2175100050591410f0041c40d1100302d4a001c0812898101810410a070b000d804840b240c590011140360003188101c444000e41300706e02400d100b4119205030205002d00380400302900c540c8075490b400c10910150740d0090040b138548a056138070241d02d9481d0040c01d4401541c0281d0715038089004203c10070b200725914100c541c440c0a4030719540740540e0702d034018000c40704019116070b0f1640d41008440002900c4480c1e100b181510801100c007241e2010254107000c0b40119401645401e5051103c1c1d14254115409011402c40403038240d80d4502c60413040c0684410102074031010113080a00059000003075558850343e680d45850300316000c0c00c00066031349112034003555112051a03083d0240c1c48601c40700e80680d004050402442c1c3c1982000f900c3e015000d4490445440104483d6413510703404008500d015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 594426960 1250 594425710 594425719
    0x4050f15071b020d0c0e0a110f21091606030c1d010917060a0c030603050601030b070905130c110304050f120a0515150306010605040506070606170322060509 69
    0x280c12911903402c0811122100030f40003100c602485040c49804460707001295030300c001c0c513461030350b0b502410700650300046010860302c0401c0c849500103a1490014250756aa0685014030555120071150480341003520304500d140c002c541a500307642c210380302d450041c00c0759050134405140e05550042044040001c02e90b030341000291035042c00ea1052045400402d15407220307240d52407481c011152070b00d0b41521160940c0d407500c60b5130398245000740180800c80f508400940090f80c695210070745200300003402d2104000b40401d000c13070580c1e101d0344420130401441e413000401550121000e4a142e1024074a910700da0b10900041006a4441c04450131161051340c075210101942c11020b482c115050500400300d000301c58a40e600a80d00204403885041d54030303482d00481d8614010305d03898020030b001303010000e04100010b04c0641440c0c001098000e200c0d000003d039940e40d0b40000d051011a000c00da40c041d42001070380d0b800468a074020007003142b06007151005603d24000c806445ca11416080c81d004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 594428210 1250 594426960 594426977
    0x406050417070e070e03010509060601090605030a02040906030804140d0203100b0312030a0b100f08150112050705031008010212010603050403050c160504141006140715020304050f1507 81
    0x80007428041c400040030031458034401420035840c01742800100315002800f96281200060302c901002030b080780102c9c0103842e40302c17100382000d0085410340c0c4014840c1c005540c0801c0001212601482020300950068039443d0f100c5007422505510f12038980242480b5038400080d50001d07980c082442c650401380948005258030f034100200703040042c101004401e1001c00700c100300784142549c00100c0c0c4250200e41d80700045060020a40d220900d445141002600315000116460001c80c50b556139008141440c02c0f04114414a410030f03164115024000628003201703110150340d1100100024040b040001e50074443c04000c0c089008805201d104101a00d8102080516018100b1203410841d50016200c01c45250400c0b01014503903441464011490f000c00364401d003800d030b400c0c140209a41c110700c2c00e04500e015011103c815100d04030b056103041c10003903100020145003807184c43d900006405600c03031500e402c00344c0c00c217070302000003070069003040300e02060140c1c010601662001007414070014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 594429460 1250 594428210 594428249
    0x80c0a090e10090f0605030f030c0601061d03010c0e1509030307110f091519030f020d060e07081b15030f0406020f030f0609070311040501110f06131101020304060504 73
    0x407010b264002d40d10186401d41c00206141181c2100066a0007601111002c010580da026521302c145074403040f9640140d80140850792140700d008080680884c001e0760030004420019084503c0c1881c3d56010900400c00411b030b90030969540c20f9400103c081c40c03400c1c10340110100f82c6030b103c0c9071001800301140032034026456944030140886c040340500203440615025068892400125404d0391140c07035101200080c040c805030941c401d41f54802c1140b4a5100141d0074440110480302040700d5458544450000004042240700010100ea078005d003e0440802132614200ca084140d1601514170900c1810041913000e080317980004d12607071006102d1380c0b00d0811900034018400c4503045141d00105200c54001d050700650b0081d07800703d400e050140c0b00e074203040d41225280741c1c81d1603112034244420040396000b00800c0c482c4031030440503103403070100ea0200c0d241403c0046803120441c4001e04080418003000404143d11520300703000a40c540b5041020103401030049100d01a00016400420b11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 594430710 1250 594429460 594429481
    0x3062d06060705120d050f1009201603140711060a05160609030e030f0607050c010b03011104081c050d0b010e041104053307050f0a050a03080c0a090e 66
    0x10b5001c2d0f000401c1c3e03910854001c0e194030143d400311440441642c1041c0c0411030344113880c100a1300030884c013010240d0991410a89402900d00d5501c1c0600c1da10990041000c45070b00d010003003d0414030550400302443c07139841c010b02070004c0070101f0103c01c0028841100044c030540d0018000c1c40045617040e03150708070f0540481e0795108070184012044850084c680c2085219040400454802d0311070800d03189104003410b81c0c0780da11183d424090390220700440c42843c003404c014a03803c84207000200e000c4441101007401d40d000d000a035034041100142c01c00004a051041036580c1c081c070f01006145038090700004103a40543d007020303519582d40b00c0014806030b000d20404a10712001a00501440f00da0b1000c2401ca42c020784151401074184220000680e401003403505140503000d0794424651658026955494000d07035000c41d140e208490300c0c1c5001e51420001460031074801c00c004d000740341e1907103802407e10380080e0205099060078010008041e40040503401503440a40100310310341d0701d012021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 594431960 1250 594430710 594430717
    0x4020a0b0a020102120604020a02150a0207020607110102012901081825060207080703080c12030a0f06050906031c030f0e0a02091302090a090501021b06040203062d0606 74
    0x404054200107005100320380c064020f007032880f0103082401802d41d00d1600780000d0b0b03c00d0130300400058000c140d041040c21500b50146070070008041c0014105078056010903a01d521119013070340c1035a1004001d5031136607824040d802098484110ba00301c0404129178032441009000500c41c1408802c20000c0c1d0b01c3e600c0300c902d8048010000e02250500c030406400080807904c5074204419003c1a10404140d0071b00014124041340c404800401c0c0052640e00c441400707810465a1100500950002250456035240a14041c00020300b00240341c00700401c40104a81443c0d1042d40901c4500341007125559020403a000302c00e800b600d00800c01401c1103001c038003d180c60b440900030507107005101c900c000d20004400d0f011501c00e480c1d100c050f44075001c400c0d15641c6d000d50002d41c0403411000061030946103800c5280c599106038000f41c00c2100540c00700c0f140501d4811101301c40e034000c004000035072400b00440c9400150f860014041c2c0301058910100803804410700c0f01403401e0500108c2c5050321504100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 594433210 1250 594431960 594431969
    0x40228030e0a111507030e1201022d070506070207240807032c030c06150616080405030a06050609070908030901030c090509130c06021f090f0f060b0414060901030b04020a 75
    0x400b541d8034600c0c5005000c241c10182c0080c0a81c083c00880350008c101403080720560450000d0b0b512850140100480000b000c07e01d10610f03a907014800d42000541c00c103d201c3c00303a04c040e0054a03d031420038000038203403000f40790b00e200b4000e9011120380c903050f0050358441d040030182c82c002c01e41c40040c803182401002d1549003440480e41912021888070b0011020300341080303030b64090358400d486900c03a0792200320b04035541c03681c0480200100002118407005050040384180c0440e802c040d984c2001a05140d07040c0340540e4055210010424107207003d0400d15446005800c082c03a02d6824445802d43d60f01800e1a500d0506035502d00b8102843c0c01200e040c402402d00401469091501a03001d0045294082c011109d84004030703004a501030001c1039a030a00c490580c0c03803640d0303155003e0903a00600b80124041d07800400d985030f10b401055400018003c0700e405050040b0b201d007413503002c3c00125480650741510702030b48070081c44080e070348010711141140d800c03c5160f40c15031a1400056000310141d400b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 594434460 1250 594433210 594433249
    0x2040b0402280f0206041a190c0903060b09070909110f07050a051e03030f180f012702010e060306011407030903020316030201052205040228030e0a11 66
    0xc1062200a00084050a2520b1691101200f4501e6002a0780e10081580c0013005070304c0310388242e124a4502c1c1d2007694418003411441079139200e00c04050048a03280d240c0b0500144405000b401030080c0d0340500b4003a400183c0314140e451510b41d000803d030a0250192690307654541020405c1041c01d40140c0f0180000c80c1041c9176a200c00d450590f031358285007141201d071030050082c4000074085030b425400e101000c24001e5407440d43c44c54441d80341102e00924042840c120a840103100b04030030040c0d00400c1035400000148106005140744094090700c0714060b000c850a160b842c01170b43d00421560554200340c1c0c050b5144c1d1211720058540d034460283c2000002c00100d448414154020520401ca078000d5058604082e408540c288071050640030180c00f10b1002c2143c10300100307011981040f10321900c504040d00c551110300040999001e04095502400190400b00320015400c2c0790302c160000070304003008031a401004041d1281c8000001400c04405001c14841070740300c0c5509000070020011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 594435710 1250 594434460 594434497
    0x1804060b0c07030b150303461107080a06090602041d01090f140c03130b10080c0a050d0b07020c04020706091110020c0d02120d170c0a050702040b0402 66
    0x501c0b9560702c001d20003030b203001902001055a60086410342d90344454058043c44c640364070203110b040308490380f603101e851003210109480041a8010780380a8500c60710f1030740e03a00307404040f00d00520a08092900c41c6241e000203804006800000504021640e40881c0200c2e1491031424044000c0c007481d4003010345505000300b12000000b03c402003605035244010104004010304a00004031064a0b407400c004031215004113044041050140d80d100c0c440400c11a40c0240d0b507560360030119016182182610341521092103094014008904410000d4a803c641c0900d018002000782d4003402d00a00350031441000f04e00b03d2442070085025442010b00155a110002d24003240108005181654041003246c17070650180341c5070b0b025924a21040d4028010300418404115841e00710754812a40101c514000d11240300c0c1c1030080c013103146403d8a44ca41c0c00c0b11130840700544003000401d400a240410071030340940c25001816210003507015540000c0329100000440d000b44592200d0420346070341407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 594436960 1250 594435710 594435727
    0x216090203061e0904200a03050c01031a060f1e0703050a17040213053303011b0f0e0a12110103200d09020301090c120b010e0c1804060b 60
    0x9400071409100d007907800004164410340d40d07007400c510205403d41d00c03010f444003140108404403000d001e829065410580c03d840c010380020f541240c158400c60f401d40140c40c00324900d680501c260480c81d2643d02d901d030481d50404001541520a4010320020940045461400b100c803000005400040c0d0f0400345a513034486080203040358004010640c001021403c0e80c500044c030072040c17180601e0b40500008840c2c0710001a82003d0312000f402d07041440c401ea00d0700c50401e5685840341341e03d140308520903c1001c2e43d4009250030b5800ca030041d5441ca000c844810501954440103014480c0c0b450328111070342d00c04800024200b014150b0100d07046115803500344040c000e02c1c0101c03501d442c0d002d890401c5002852010100c90880c80d84a4407000b80c400d11040300800c6031500040b0030244018000540e080e030341d41d10842c02c0f03030854121081d0f0b040091040006c0124104501d07014015400c400d21091078007400c82005489521680c1400303000c900c4608070580c907150032160282002040300703500c0e031a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 594438210 1250 594436960 594436979
    0x6030a02010c38090120031801020c0a0b04060b01050301080307030804030c12030c2316061404050601030c14300706030e070f080705061c050a051e0907060c030216 72
    0x15a013000640d40313045285418a210701d0107071030424680c041d41c981103039103d0300d40001010346614003240c155020000c4030a042d00a009118906105a06000e07103800d0a062801c21214505106410f03c0800c00042c00303140c0700002540d40c440d85c5440c1488807540d0343e1408071014054440e000f0301d02040100a0a0384503095000742c1410101c55030f511340322514080850074400303400182d05c0c1d0024410041d40c3d0b0049102c00e40c48142a00503d4042050b400301c0c00e0b0705003102c008540582d126002940140200034040040d44003c12060072041218483d00c0009951004030740f2807210f41c040070310304480b6880c25048005001d10703c0e120a0b07840290391580f01802804031048124914060300c1d40200c1c0d190010110102a0b98800c030040a030181010103000266008010100703049020845211400f402c50081314441c4240c18400305103420040603000584048903100034003c44100208003101c0030004410046441030315110381c240c0c450342400d030300300183d6615440300f00e5405000450041e0a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 594439460 1250 594438210 594438323
    0x30907030f14060106120506090c0306011101270308070e090c0c0a060c0302040504060608160809030f070615051f05090402070f061a01050a0f050901050c01020304030306050906030a02010c 83
    0xc506c000b4812030b5240820031800d400100e0781a101e0740d83c14008603802d940b050f06401d4581c8901c0d000040c0b01441a0030198060b5416401c50100300700580c882410554803144103604500e141c00c1c04104500e0300c2c00050203210004148070b079407090110740e0141c4807801300301c00c84255401410411032031890040040c0a9449401040e000b1801c0502c0003403043c0c40351000a00c240703039056603032000d481094001c43d00500d0242030aa1148000c6c070501c40c10f09610780c0146013440c4603c50010b04500391445404010b43c15a102612601ea14448140d8010039040e0003a00c0b0622481c1140c0d5500324030000500038060306c40082c2c1b840c90034241a500f002080c0e40466241c03004020420060490100111454402e006480000810074000d0383d000034080e0700900040c01050404a041090201c03205089800488043d8006502c45000b0401410f14105668000406401800c804041070300042e01188454800a02a848105c410400d007000d107030640504004106540e00e04100001c0d080c2c10081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 594440710 1250 594439460 594439487
    0x40e0a0e0d05070305030c030403410403030e09040219090e071202130c0e100807270b0318010603030906120501050d020d02030a051c14030907030f14060106 69
    0x4103084503100601c2c000c80582d82e44580c15034039246182e8a102c081c83c10f03900054811418882600d8120301804039181042c1900d1044407200403001080548800620841c8030729290411004c210601c0070952086e2170740035071101951100080d441b01d1012406120000010828102c0206400f04005580ba04903040810701c10045640302606c91000e03200b10518480300070740c000d04840c0240300025040c0c02c200d00001ca80e0600000b2038219a0220340c902c0180382d11130002a03456020000140d421629220010007103d0a803c6000e0b0b035080c266002e10854042c0900c4900c010001903080300303040c4445040450070380000c0c00b11641c2e910700540706000c1400f465000c10588215010a144144940360403680e00400150f000522502409070320014903c00707a1705801a2001d01c000b080e030401c100400c840400c1411a100706060720010200161421141141042041400000340c4001045800c1da0381000303080d05580c845241c0000c05054400c460b8905020304c000016581d078001801400781c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 594441960 1250 594440710 594440713
    0x9030403200108270a2a0620010608070b0705070618030f0201200606010e0603240a0906060309020103110a0804031b060603050307051e0c040902010302040e0a0e 71
    0x40400d0451441c400703060341c01074001100d84000910f142d40d0200441d04a042c0310121605004204e8030103801d00422101c1038030015060045684c80c0c00032000c40382441030a401c01c080c4030350308000c0300034005050903103141070503c0c503001048107408003980f020000302200e4040314102a42d4002c0b003002a0000c8a054449000e000c00025800d4020303080c1c00300d4a14401c0d4003c00450859079000d040c2020030500346d0420100b11003a00c1311504103600042e510041c02c00030070305841c100000400c0b4107a41e0548078001c5d60184140803050004000390700307210000b044002014107141c0c000c80c0381281c442d441145901e081010000b0314070781662003041258004e81c3c00b84007202883d00c2441c81d510ac0d008890000441841c00100403e1040b00c2aa002000c0021a0002019607484c1c0700d05a40294200381c07110b410001e03082042010400000c00d05251040341c04001e0154106001d40300c03d49081520f02590711004000704581c440c1d0b0480c3d02810a0700f400b080e0314107103460104010604140b904015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 594443210 1250 594441960 594441983
    0xe09090d17090f0a0b100e0405100903030b04020c060103060e2404170310090c0311031b0d09030201060e061906050307021501090b030d0302090f040b1219050c090601120e0705060309030403 83
    0x486287e50049100d19041001000182d2a001d10328000300818401541019901c010942a03691180000c1209280c00801030450354158103100048401081003c051680700c0c002e601010025441d102c6045200c26928a2080d83d45080c40c0e00f200010000340c100c04000041004410403882803072809a44205c00100020911003506030221030f01da44061001290a1001400100728511410b5160325031102050510300121601801d40d050500100c003d41d4555034244084000403210039440070040307405070315000500608580c0d8164030301070002003000000006440e40c1c0204144803800c08590b004490b650307500c910010050120011280c424018500c6a80c2030921900a0b80d003000c5004240840c03200200c4100070040890121043d000346032080c15412905082c0400c0c203c1c0303000e0007090450740b145460500c2c20301e0b0151001d184210b002105104440c0d03440000c06240388240180003403102107107036400b890b022140c1c1c00250722600020400480a4000c0f000e0b0080b81d11501070500c0c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 594444460 1250 594443210 594443219
    0x1c0f0c031421090307031704050306060a0b0a12020c1b01110105010605040b1806160209100e040609020d140304060f02070b031b0705010504030e09090d17090f0a0b10 73
    0x302d031241800c8050550400a2495101c9000340008008820000303048622440e42c03a03039060059034911403616010315000c1402c01c600d040a11070f8130b0303000c070323048907080c2045040c1101402c0031f000b0903030071208000309003c1070102d00c0180d0b412140141c0b10341c400c480c002103071003020f804200302250090307000034803240400b0784003207050143c94180c440b2900c2d800d041030b0515621b0301080d04078000044064080c88402c0400d40c0740d100051003218841a1640300540060040c007040c000085c04e414400c25143d481082141c1842d0030068110f43c2c098030209080c4624000038000c42980f0801410202d11000c081079010000801007044560a0b25504500141e0040c1683c17152501c0c4981081ca040c2000020325982c1c54140e0401641403a0385190f0919040784c5480f402c40d00201c0301207000c03882c5012882c8462420f16540c551041e850740040c01103400d041402000b1907041100d960050749000080341150b1000c1c0704180103c203655044924184141c1000c104030300040d034414042c485080c10204 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 594445710 1250 594444460 594444463
    0xc142109390d02030a030e01020328020106060216030f301101090c120c031707020a1203020a0609020a12060b040f0e0712050106090c050711010e0f1c0f0c0314 70
    0x10752990010080c2c605e648050f01c094444184450340d460460004000500c0203040c1c00d046503070108010450402081c0541c04047e084030066003042041d0f40c0070070001c000d44181444820b040d2a400b614004a000303cdc2e242c842450340260310480c1c44100c005200014004600c6807010700703141380d6a20124901e05100301e060032a14000006491141d1480051101302800c100080c900781c4141040150340f41e5079103481038030020214403806408400200726003946071541103140904254004040265000c0d98065659403442e400140170307075101d1000c41c0c25561840c6603940204640b003020300d564215403519400074407000001500c03561034898040c440d2903141c428000c90715000b100500c419410308070740310802016800300316840c0d0740700c8402098400003409103060500c220340301c2d01c2d12016a880c02020030a006c00140e0304014810b240080d55070b0b14401c40031342e40841984d0118402c040d0221080c2100c0750400040c125407140b1402ea410040c0c200500003c41703000e200c986c600e00c40f031240c229 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 594446960 1250 594445710 594445729
    0x150a03110a05090f0a0b0a0e210d080f0c041224020d0f060303020a14030c0a0b0105031020070303090209040c031709091501030b030609010c14210939 66
    0x81b40c0c0e0780818131201801d00d0242e00c0c50494800024510406100c10030713090220416403a44048098100d0604204010740100d0015040051030900071054600b0400140182c05103100f80040400f4030403400090000c1d90f68218100544084403400f089540300c15000a50322410b03078150128907000410903424124030402040e2940740c0d003d401d181d030551b1124004284020360f03003002400200029801c10008020b10708035030b031051108404a62500c1e040606001c5c0344c61126581c035050510700421150700210711540c00c000c50344e45907103c5c085810102c0c0105410100250482c003108180303c00d00042c603500c242100d00c21844103454822441d103905989c010311440ca80c01400c40b1001c19000f42c08038090748a01c940615000070b0102400c40002c0c5041d03010780d0340070410395450001d0240c1c9603004001000074400310032020b291449807104015048101d40007140200d00301c5020031003903202032010f202107003003a98010300240c000e0060b00c02c0780b000c000900d45407001034030010b29980c1403d00e400d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 594448210 1250 594446960 594446969
    0x191e06030b090c1e091906060f08130b2802030a020304021c0507030204110d091a07110a20060c10140112020409170d05010f080c150a03110a05090f0a 66
    0x204200c6460060500650a4024100ba142076001b401340008402c068850360000f0040d5503540304c0303403480f4624090701c2c010001d4900041d2400043c800d07400b103030741c2410164000303c4112000c00301d40c400b00c0321011100340307051614115500000c20f000100045030050f5000310b0003165900103880c1180c0e60006d000d994001c008295800000341000076140070350201c1c000f81200d160403850043c0b40b65140088505008088605c030900b40b911072001500740c40c4095015465060000591051500c01d07550742429000051104138400010b031000030b40000184881c120140003a51980c0119103480c7e200c1d05656200700c501480c014514500b00f1500341c00307034121140c00c0340342400d2000c0340e0280005003a807800196110703544400c0150b00f01e00400000c11420b031b0540030019455041c1403031603607940c0859200004680c0b006045d00420f81c0c95103041040c5100c00c00c500c0e81c1d92025810b0030303405000c5c20945244000b00210b000f11406130003000821841e88112240d007000c91780d070b90030400c0c0303000d0b00d000c0e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 594449460 1250 594448210 594448249
    0x2060108120a200c060f3604020c0c030105011203030e1501091a0604060e1504060e060c07120f0b09160b160b04060902010f0503191e06030b090c 64
    0x15007003c000750302100d4459100300c050940d450106400c011814035802803c00c0001d00f4000503903003060128411045c080780c0800d516001041400020b0220650f00c900b200500c9164001040308180c04c0800c052010b081d8050001d0002c0d41c1c5d140fa13801c000c02184941030b00424140104013501000c045406454400035050308100c603400e01e0503100051220180d407841d019490001d40714255900c9001d4801405c2c240c4d1404403c01008007480200f02e0b4418410161810511007489025044400401c4180c1700b40e4006071110450350549180c075000f07502c014890f028410703842c010302003607075140c1c9241800750b07044031030340c1c6c0352004410394a1542d80c0300720030804034580d01400b001c1e5528008150700743d807070320701584003800a86442032070388000d0b202154419a20040c00c401c550300840108008556420603d0542c0307000b0300c0200c025041680210400c564410700c5039554040900524030300c01c00c00300c00304445610307841c0c01e441c0541e05a46001c5144215032201065203008801400120701428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 594450710 1250 594449460 594449477
    0xc0d0939030b0c1b0105190b0108061806030a08030a0b270402010f02070f0b04060f0c030c0f080d0504050703021212390327060a0c02040e070602060108120a 69
    0x8040054640010b6542c0c02c0c0b138850100f100c26200024040c0c0c60090710301960f03c4038840512481d40c2c08a03915132600d541840100340c1080501e0340c4000900455200e00046925540e0325240003d05080c01c800008020002c04810310a4241c0c0d15030141c00025000e071038602120039165241c2055071500c0c3d90200110003110006001544602c45501d408041d82c01254100b581321100450254001e4200100164021808002d5181d01040264a544080c200500d5120040c3c40040c1910710a980250414030441d0500c420440d006040721105e45030b0403020002c606051400540b581030342e105c2640302c1c4030018009808030901080c507504000030360003105d15062559030600d01c0c1e07000d40701550360401e1014484100c6143c0540900c124003046102070350341c03400006903283e8807a03a029503180303080c95410900102911440100c644034280d600f0b040d450704082d840017402130401c500810b4214000d403040003601c0c640000300d1a041e94803007000d03124006a80e800e44a018041c51040000107040203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 594451960 1250 594450710 594450721
    0x18012d1409131e110c07090219030209180717070906020c121203010305071815091a0a1d0108030304110d030e04112208060c0d0939030b 60
    0x55001840400810220800f03c02a409903d01142e0000900840225001030701030440b80003840404040d02e150f8500b1401c2450540d0300d203c880c000503a119062650024009250303540e865862218545584241015450a0b0200410009091040386404504807020030805409a40c010040da426940101401e5010700c08104c01a40c2e103030014a41da0007450900d0008482c444006c602030740c010402801c080c2c0c90044c0600442045c0305241c2803080c500700c2400c55424842048900325400180c5c04a0240709980b5500000c40ca0601d10355030105451000243d1080c45400e940422403039007003d0b00d482da9a40407999124441250700070641405c01401c0144c0e890001d42012400b8000d2620942c148100008103045900d44900b0b0300030402d002c41c15584601c1c44024048480403c480021241d5240035030f13440ea914005814420301030408580002406119807000141d103070040c20101007423684842803d0716094050505403144840c00c42c030141700b403038001e076003003166401400102c80b540c42 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 594453210 1250 594451960 594451999
    0x906031908090333040305030403050f0c07090b0102160302062b2a05090310051914011d0f070f03091a0712060b18012d1409 55
    0x40c04a8028406002d9145103440c10030030401ca0086482d00d030103036219850780e00c50703e81c5002c841c03030024800c000003000300096211054030b070410380c981000c03600c800c034480da118118050182c040c0d041c1d00c01c0740400900c626058000284074a030a800355403810440c91075031081d11040d404041e4120390300f00119680c0084c1c8116003070800b1001e0624480070038a02000130282c0d500d42121344045a11040b4082d241800341950000d490524103020b413801c682c8070b0110343c407600c5c440d00300701c0080d170754000240c10348030540000320b501020190100050f401c9614600c8806c0303003c0c000c141d2841110741980a00e070a49000090140a41c1c540300d1129a9032220308640254030940d82d07100701625040e80d280010703004010855041c902c419019802c5c60006e0b00144501242c1c0003000b03d490070b100c0204480705425044626075403400841e0003003010f040300166030291204030960410000030382e02c40191807680c00e10580050703460b0b407844020182252620102c1c0580586954840040c0c042181c0300b079007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 594454460 1250 594453210 594453253
    0x90c0a050f0d06151d0103020421110a0605070b07051c0c020a151d0c0d02010c26030a0b010905060904090212031c11030405070e0a1b030b030c090603 66
    0x19820b102080007600c8510610742d191041242202040034100c60041e000002c14140540420a280460505180c034400381d4002c240707c5c60002042c0c44400c003841c144800d019512642c0c84018111010380d658424004100b46d1108005590314000240850b0303855120b1070489a946424003031118010080303804000041021540e20700546c411040c0110004112503405081d185101c0c0001801456000d058521860280d2140d403e60300140045810390f82d80718401c003009902882c0c100e5030403245241504001c003c01d2011085500c8e1a0001003c0300070303a4004501c54901084188004c0d0804030055030b41070702e1070041c2c6a10a2090024982604190b131118150900081c0b1442190030403038682421036000c2566002c61b01260044005203580a008000c0d4148151500501d5442c2a8031610f403581154001c5c1a5071416050101d001e841554000400e8008261030296200032500806002803441403000c42c064010b10081c0070003840c11007002d070b00c94103010300508a83d03101000103944144 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 594455710 1250 594454460 594454477
    0x91609030311030408010f02040e0a050708011a12090c1e060a030e011509020c2e0c110d0903020a0905160e0118030c06030501120302070e100503010c0e090c0a050f 72
    0x40241300c0011450401d001703490341c50b2000c40f00140e5560070211040c10740c07034004080781d070010708050034450707215032012580d41152070030701c400100c032188500c41c0d0410b0b125803821281c8074160f12081c000c0c8030502007140700d8001000ca40c00d0116003000641d89000d018080c80441d072024050041e103112501a0308a140402401000007030f190f130b0042d02e0204620034507000703203120582c04100189440c40c1000780c440e9040140343c030a10f030000390710b007081110f158a03240a1840c54031340da0b6a00400c0c0c002c0c070355070f203800300d42d241550000d50031010010681d25141c44160302c80c60070742400184084082c4100b1f1301860b01054940e1002e61043c86c01d5400031031600c011410030888034001103111040600c04400380d440340080104245c41d040d0024140c40040e00b014140019510300d01e03002070340006c0e2110413122424448165640d858079001174030b04017a84040c1d055400e0040c000022648240702450504085980180c50303110740102000c140510311040001c201e007040840040342980000d401d421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 594456960 1250 594455710 594455713
    0xf0308030705181f0206010803040b07080f13091e022106010504080d050c0607021603170f0408010507030e2e1b05130806040201051b0a020618091609030311 69
    0x10320000205104560341070b03c2200b40d04c66085000142d42c1d0500c030250041030b500000f9070803e0b08055007100c0e00d21507440b00400301500064014401074940c400d84001c151401088008030340d4585030203016040100c50a017240c0081c803100d08008881d031003500c00010507401c4501d0400391101d48617000c542d002c1e0019061060610000450001c00c000a070b04002883d03030703100c0d00c801382a15028030300500581a207040d1740103002000741c114401034911044030303081025129010101c0074000c8040c45118905091180c0000e4085583c0c101500418000c0c4e01c55071b0b042185107148440c003600ca4030445072040f4115480190784140c1104c85810000c0c0009090340000c400303407041e41c00d420800701e2021038004544082180440c00c541c0507480002410542c0181ca468901680024114031400c0c41d041551060701c007109031070741003c1005112540e0f028224565544c051500800c242050703901c140c1c800c842120004540a111082c1a000f0440b943c640000c028203680d010744d8000402d00164509 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 594458210 1250 594456960 594456997
    0x14040e0607050a110a030c080a09030609060b190e010501030903200d080703020403030e1201021b1f0207020303031605130608070f0e0102060103030e0d02091503070f0308030705 78
    0x194505100060103800e40d51195691403034100d101900764600c42d160700d60f0a030861060300b800300750400980206c040d480b0401c5a9503032500300c0d0955040711a0340001d04103620304410081004007036404460003210071200011046007044080c4840140c40c0284649041c00e000100602e5000c1d82101042c00d109040004103489048240c02c03a07a01101019040343d48000ca80308006500b01041d581c000f0117601d002c1d071420781180c8010300340d0b50b990340071103005041c00b441c00900070344294141c4200c180c000355181c0072b00d1460001c041d0fa50050104190020781e4010300141d501c60f80740f0071104555400b4001c0d41c1140d41c0c1c3c541240c035405042d01900d00b03005003002080c01100c5044078500151403581c403038030160704023104020803045000d11030505010f040785400704107030780000304141184c1d030602d0030b41c45d0009030030042090301c280080d000390004480d205005c3d41da001c13040100e0900390113070202c0300c00c955680e1212660203154031000e0104401040030581c0148a00000c0840c1070992401042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 594459460 1250 594458210 594458231
    0x51302040e0705011e0c02150405030f07152307020d080a020601151b020f043804050708040b040f1202030d050f09030904150503010e070602061e011404 67
    0x75100c0d0121800720507007020409204a41e0880708070482d130394200090044240103840301400101d100d50b00603100fa030700103288100d40803592046401030720024040d6680c0780c0c1e041e140e85503219028007840c16141502000010a180308507180c40b0051465400001801601c1000c180e550344a01c10076038000c7d807590500b00128003114010003850065600a00880d032600640080011800c0740b2001080314030a404030412031522685e00000342c04441d80e0141048ca14000380040444d108015162280b01d12981d084400211107008180c0103641401001c0c044d08042004940c0115490740106a03101c3c0400c021611a0111075070140c45140007441d15007940d03c0d04289820060341010050f84001026902c00540c0d0040e10303040b04680b40031110904002d010b658481c01b80400080c0210760f10010311800030106c42ca48001400050000c10071280600c0c8650b0701c5034040d0150134058440c103c0420305124802c1c0304c1402442c64100c440070507034204007400e80c2d46516200d1461b405602c52170a1013 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 594460710 1250 594459460 594459469
    0xc0318080109050f100b0d02040b0111070611060a0507050406110f03040e0114030111040603020901030b0904080307020f0d0507140f0115050f0d02030a020111120708040306050105030c13051302 85
    0x104a207000f038000f0039440003001d030524039141c80e100d00580c8842c00c081104c805900d440c50904007a40c1c2c12100032130401ca184004071100c101104105046224007003000541581104407484911a685c00f91038482d036842c0c82440c140c6406460040c0040c8040008001c0c0e43c1c80b600d1561100c0c07074104140c54290f028100110301d5500560001c0d0000186000100100a90443c040c100d400d81030700248810085000c480110b4002d910641007890740000d0741040c41d80c480c0d40113030200072000785a4102801c080c2425401508102c4e200c0b005032049880604c50310f1000075a40a130344125030744252802d401030ba1100c12050007c84c09000b5031041c4035135408841d600303000e815003000c3c003d0074041e1170303515040030055100581003105020301c0001c8910f070f0147c0c07000306501d441c807902030901c1c0782c10001003a141481c000c0207207406d4030f021002007640700400c500b0386c00500c100c0b40a030409202690303c5904254440050b001c210340e2002c041300003c2021405a000141e01808954407242c0440f030b140c0100703 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 594461960 1250 594460710 594460721
    0x405030f0a031e0c020a081b0f06040b31060e010507020d140901050f180a08030a0206060901121b0503030f040509010605120c161a0f060906010c03180801 68
    0x207001003519807200b00e988006000414040014805040c048034402c00d0002c1c0d21501c4405e0050101040001e019586510300c8030102c41c2082448100c9000c9200d07015110749494041c0d60890b101c41c060000b089500d0002d051040104150351a2503503d801041c0c00d01c0320f0a00d030307840c0465509440328009501c041003031103041e01c00c90080e0040c0176618201d0308001c4c4068070110711054002c4040c003240060b643d2000070380d0354601a6811681d0758000040d4040d151142006025904c09128640814004c402202800c0208019004c840c2c983e12410104041c0090900424800c50700d0f414440022400054807200717206141d400c9400d1858407003002c070381194013100300c84d500d5210000d01040b440c20304070f9902c0d004001ca0300d8001c0c100b0f980c00114411000001e40240c44000000c900301c07940955030036903500120340c0030102c105004010b84141d030641e101103038205025040000060114203040c4c000b1813007080140e4610f00702c610715680c2600da26400101a540c0441030042c0828641c0c42485007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 594463210 1250 594461960 594461977
    0x20603090a0507050621060609040612060609060e130309090c09051212030c07061104030c050f0102010b0102120d060b040305071e1d0705090a1e12050304030b0405030f 74
    0x1d00004102801c101c0d1a14685a0003980074280c104540c40b420050013050b0348001000145191540d100d101c00213141d4046c2d0000c0c3c50b800b030310b06003000071254085030b545031549108101c00d014441d0394007520f030102ca1452140d6800016400d00062034141c15403e604072051090803d10442d685034481c49080b10400351101001c600e80700028016858a003c00c3c00038100f0707603401024401c2203210306400c0350101800c0d00c0342140c00402c2c60000c000c41a0030600c20090304074a42900c070313940e904105180c182d040c42000e00511074a08800500d51060050808181040c2c00906900040d04128442daa0200d00d0b898003041e540c0c0b5000c5601da0340c3c80c00500042d40038400410120741070141d111510030fa100d11a615041d14040200520058034240300030312901a000d000a950710048240c0c2d403032240c4c003100c80d80000b18050200380c1007034030141e141c420100301c60b400b074100d901da40085a80c00f0484001414030390081c041000040c001078030309980107203e081501c0c01c0201c042066241c0381c00040c034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 594464460 1250 594463210 594463213
    0x306210c0127080d180f06260f06040e0109020306010501110304090504060c02070806010e0a0203101e0303080601021b09150d1202060708010312030f150e040204050c032502010902060309 82
    0x82100d5003075482170b4015603040401c49a0001d40703140001b404002c0e10148150380521030341043d40061460125850421343c040c941c260181c03490156140308000b0741c03c40b03e880c070403490803003000340000052052032480c070b0f400340003012503074240380054403910032004180415120030000422014601d0241501032481800c01180c1d41c4e410600190400d03007140c220210b20340c400301c0100a6010003214030350304400503503c01039480c0c80d0280d1030070454440f50812a0125501090351181c1d0341d00d41802c20440b03000e5a500762084d01c8403001280c450340200c01c80040b800141d281c0845034079140d400c260300848080c14518190740e40002049244105440035900051201c541e8011140c0520242d603100300c081c0780c001019811583c400034004a00c000c460105070b07449105d65803d0080b80d00007042010018822032680340c0d541d2030841855404ca9049010714101408520030080003419a4008c0700b00c500811444140301c00d001040300b618000d003204541d00d8003480380141c2c940000640c050740d42d040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 594465710 1250 594464460 594464473
    0xc09102106050c03040305030112060f0c02211303020f040b03010c051c02070f120311030a020c07090902101110022710050a0f05120c0306210c012708 66
    0x410000b1684028082280f1181c1003041000081d840300031241540d190002c21110b1204030b007842c2000b0024a000d00400c82d29103401400c1141d0005452901400f560914000f4211443e0802520340a40d031480c0b490400f50140c1480180b424588070410b07148041e00001d10003a00100003400c1d44e4408401c0400b14500007035600e514601001c1d10174002001c1001507141c00d80381d943d003255400328074501a0421880d801b1015805220344c0000301c5203200d412030035803a1f0402c80700240095002100c00041e40c800e84000150300d204601500424680060101c62440e070203031003d8603000c0119202031014050204483c8514102d40702070071544126050a0000300403111034046100c0c07a000383c031032050202c544601102548201101c00d0152145000c002266000006550074081c917a1800241d43d844010001c0b207403082c0000d5441118200c1c0c1c1d21070a030008483d580d0b132846130743c410051a074101074118455035020b03c682c5004c2c29000f803405070301e5203d500608506c002c1d840e00248101e802c00c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 594466960 1250 594465710 594465713
    0x10e041103010b07120e01020c010e06070606080c0406080a2604090603032a0c170a15050f0c030c0406140729011d01031205120906091c020c091021 65
    0x203807001c07200314001d042002a4050046c0080c2d51007a4040c02241003001156580d4155180c0ca070075030f1071569100005110030fa481d5140b40d51104848403050740140d2805900040040000407100b2103140c102940704060080e0b002c3d520803131004000d085104900800000a042d8454844ea4000b18003035600c0d030b00107592404468841c01451450300c110b0b2040e41082a010511101401c2c0450758200c001509140c0c00d45480c80c106032040760060014050a081100c6101094202620428450b0469891039841300c545074031501003610503c2c00310304144024401075020310301c80d80c1001891b06005080011582d03e22441c0f00d080c0030118072240000c039600d010402407080d401d0140c0054be607a02c074134540480001c0390000d03052102804691501307034031042e1280100112809132a020002c1d41c2c0317500c0c011000700e650381019145010140f207542e030b4101355404607280070001c246030381d0701809003140034404101d201080506006201000704a0008107101a416a58a01c02408030170451a0105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 594468210 1250 594466960 594466973
    0xc0f0c1806060503070e041e05040b0601020d05070f17030403030e0c061e18120a2604140f030706030609060902070b0c07030c0b1e1f05010e041103010b07 68
    0x64140d04a1140d06160003444001c0d08801035079070090710f82c40c00f69080300e001c00000b005408001d01c40703115018058003107900701500b50070283c440c501924003140c042d11060012a51000f04040d0140019007e116940024045c0c2d4413030340340103004606240b010b080c5055401c110360301c03e0750f049003c281e550140000c040f80034007040c0454030007140d100741031601000d442d8044188804c040e22035540005010b55081c51100c119a03600764020741a50301022045c00020340d92010800b0540d080c00003000801d091980c030418042c1c1200300d110003d824a803502c0045402e07441207500150b840090010100c0440e24108015001000950340114040e480c1c000007004961650b0844c10410740100031102c041105840e6254101178a00101540d800c0c05090803030301d802c84032400a00d020071501c10f000c001c4101c6c0e400b0080350f030b202c0340340310340f00341c03030700c440c1c0810480c0c00c0700e284c214090310908200560340c010300e4461420500030300701060801c1030640031070081e44241c03c900b4403040c005c103021092089 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 594469460 1250 594468210 594468239
    0xc0607030b150c030f180316050a0e0a0b0904030807030c02030f0712020f19170313062003041b170705040203101509320409030c0f0c 59
    0x2080e080812030158034201040107280042c21000400300d00261000350300004108981c24452040407554031441d0340d0f05480e0b6484480101c46110740318181c030b1100c40c9468100890200d5600903c2da8560916114408000030f400a044c41c880d1681c2d09402c200a0704d5204941e40300b50b1199075842c9640c940900090704681840c0b60f00707003c66101b44600b2408149150440e41000d8001081e042e03d1280a04100d10300312000d84114614000c035051a01d242c0c145100782c8500798441c4224900d240240d04030356420b40001c6601840d105c110013094408035066a1114282c00002d4039001c40c09030400203401c80e1640191003c4480300310045400b0140144640c03c41d0203481240900341a071902c030000789503118414012644100d500001284d50f5104801138a0000d1003090910b4101c10000304018000004c18803c40d09184c0901c10510240204000510603c0100100c800481c1400c2000d2000420b0444c600303d0038006901e58013000706040d026450140c42c8a80780b500c885c207003400b924507603181 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 594470710 1250 594469460 594469471
    0x1121401030c080f120304020f03030a03090c050d02031f02090402040e0901051302090403082a1305011b03030b0a030b040f030f02011802010e0a0e0c0406030605060c151008060c0c06 80
    0x100283c9202c4c1c04080c001c5110200900414401d60b00da886d0350000a45841d41c00d01490361522002540c0018103030076802c19201c460282140c040101d83d14014030a40c51b002d25070095058000040071550310841381000c40701c441e580b00006082c48c8903800420300326072042c0c22101e446c54184041040e00c50090080e294000c10a03142c084507000164040b444403800034000909100160380090300e01000303a03850028040d11403400049603004204404140e86c409480500350310121600410325502408a06026158405403040d040805490440c0200421800207034002d005039000000300f8103442c03000f8011809601c120310b1f03500b480d203400780030f15444840c40025a4188422424100d50b4600600f00e81a0282052815a8008000100b400031260010700b1540d580005202185030b0100c050000d0320120b8508000d040e1719441005264000e881c0408082d0f0700541e2a015a900d02e2180d05800420408607003040340d40303992501c0c0c14410121200d98452102040150301e502c82080381d0340c1c00c00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 594471960 1250 594470710 594470713
    0x1e0608010209091305030f0d02270604090b0a031202151003050c0d030302070b102c01090207030203040f0b0a17090703060b03030919030506180606010e01121401030c08 74
    0x1800e800200e43c4001d4014904050b030080e80c12600d0a01c101441125070010040014507a507282040100c8000e406c03040c0c024000c031011903070011150801070f107a4920280003c281509061400603404e000e00f0340c9000c1d10745c200303000400000004048001c04101514150007400400030b04003e480d1604074000c1032501c2d006007100040011460104c0c1030001c005003550500310b03860725800c082e000ba1080d0340004010140c410108000310b002c041c3c0c071000350303800c3e41c02146224000c400c03e00d400c2590041500035007441078004211640303940c4d0081c0f0400303120740156814503584d0344240001c003180e540005140b00b03001070300d2030341250701c003600c80405942181094901d0405890442d40d4032120b0100804155445504644a03a41042135801012009051310369008000d0f4404070b040929100c1107505100b0030020400c825a12412005031500400050007a5551200111000054004024184008000700c00381c00b03011070241141d21001d400301078840d07514529001c86282c556520402c0c86 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 594473210 1250 594471960 594471967
    0x203131704210c0e06060708030f07091a1b1204030b0109061a09010c030509030304091b0507030c12090e01080c0a090204050f04110d05040f1202071421011e06080102 73
    0x800d0741000100352054501c140d850760385d80340c01103000c80c45a100040c19000021003000450b000132280103101d1841e43c0d940390407036651886000d03000e004071882c0c110459401d01c9441802024400101c1c0ca002d1000f0031079840d03500c2c0c0e81d030b04900c5500c29001510145128030050220103030a00a000080a1224529280c2280c2c0c107541c00c940d000c2c1006031810021088486c00c01c0c03500c90402d503160100014180c940d26642c1d40038000c0282420700c20008400e0441a0742800c80340940d040d11401605521001c1000000ba940e60300300450420b800018000200000f10f600500090446c0c00b80031090b004152a120f50410003080d07051a910030036030180108400c0c8885d86a42035200c04280081e1800300d54803407071900c0f100d5035000e000076241c03120b031819042000780824031030818511400340641c4110b400d071070f40040380c9a200724054144588840b2620b09024200100e500071030300012036070b909145080840903425154034185842c111440c030281c03040000803910803030000b003243c03070700840c907 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 594474460 1250 594473210 594473213
    0x3080412050304150c0e061305041805032d040e1e010311010c11040f1e050106090b0a030e0a050309131416021c050711090403080a020313170421 64
    0x240113081545022400d03243c06000b502180a02c40c03d05900b9401440d4584070f01c4601c900190540c034922880e0300c914204050340e03c80180d54000c03441c5161704100a1841d003141c10602caa507101000c0d00c0c001c0781400103454465050a41c0c40900040c201c408000144c0f030804041c80d202c401c2c070241d04000144000c000420020b4030400c241621500c0070f0a2505d02980b5031b0610a540c02150a101c0c0c0c3c105040524101ca50082607000318469189030081107255100c001c43c80b811200c0c01d000b100082095100b050000814130400303004840b4082c600811705043c1c00706a9070822100300c2c8110303403561010484020034a440715840030700302000c01080003140403400541103028030240c0b041649210000d80356040c184240f01036540e00c2c2c0108102c0024034103410008025602545050b208841188000f0200e484c25003c0719000c0c2d030301a41c0f49009601c40c00c503a234000b98030203084030800381c92045090b4000b8443c03c0c036200c00d82c01c0110405440714600b1001c40c50b00344503818000e1051030702014880 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 594475710 1250 594474460 594474473
    0xf09090705040e16080d030c0504080a0303050402060d0f0c120e06130302010e0f0601030c0e090318060913150603061809061104090209030c0a290708030403080412050304 75
    0x201c56044801041807030511004500308090306000d022507400603d004542c2c0d0030005801d400700c1c212945c0800c0f407499034110031240e070300440c0a10b01e915004240783c2c1c808244a40c200c6900309000814051070182c04241e14000c4405c0502c070100744540b03840580e0380303131a040a00d102d511000d4407828040001c8a692458036a40c0c0100301d0300a00ea502e00c1c4034410325200354444c101c03040c0040d04032070312810341c161840c1d600c80c400d2204940c10065200c000c10000318a85a042c090803e0300001e41c14240075500c800b42205418480d1030f000201403001411581d143c404c549903592090900140560032a440c3d06d008407103d0b0880c0c01403604128040042d1007a004880301100d00400740004d03040110324005010f401c2102e4910510400450b020456105503401032440c1181102214060a0501d090201c021028030424150940310100d0000e0428080a04403402100da150b040c540152607841b80c9041e00f083c1c4040c8c0000f11035004000800403c0e1690101c107030402c2c1801404c515007941c549 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 594476960 1250 594475710 594475723
    0x3b0c0f1005030405150f1f0e01142404050901080a050703080708042c0a060503030301051c0b0f40031b05011a0402041d0709090e0109020f0909 63
    0x2001000400000142400401e00502140180e8050b45da0b0003424003000030b141c4010147c40c0b182010750a100380504481481d01d018044400010364502c890b848c0c0000c07407800f0322031312806170303041304080c0d200c02148140018850a41c1e10325058660700d80e82014180440c40c48142c011214903401080e10901040000a40780112680410056a0b4005034541036030b181c001c66014158983c915000807110b01000345020030310449559040d52a5500c2011202c10b460b0030703100341c41c3c15410410050025041540618908090402c1d05081485213503940c6040760608861003078031303074050105024564003008240780c1c180c0c0c0b05521001c000c00c0444c41912b46500800c0300715405251400c81c0c2000c0502540100800303c2c0d8a0f80e40c08007807411800c04078064081c104c10001c0740d4042d00d800401e949440d02c295002e80f10b04501c00a4071340343c0811020302a10b40640303800c0500160440020b0700a40c18000c8810f410144800824a204c8500c148060001001c2030140300c0c401590820000c900000f550 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 594478210 1250 594476960 594476989
    0x140106091131150816021902120a080409060503121c1a06030403020109020415080606091e0106020c150403030c020409080c15060f01020616033b0c0f 66
    0x100000b00d1418018200700301c119a000095500001540c007650603000790322148213141c902000c60882206007400c0740c440103a20001da108085c500c0510025043c00c122040c0e1280d1403104499211501e0703102c002003034110340d004100c83c03501c0710401e1000e401d003800404020b10302c202905003000840c40d280050541422042d5011035a95240140d03100b850941006007181c024001075541c3c100f03410001d01908041400f80d01607070400b10040100da0541845900300c0d114a000b401c40b58442c0c4041013041e060140c034003800c10001071a20300c4241d40d4031100e94003d003401c0d0001c040107840c84041c03044038010010720080e00b41c1d05000030000310340c05c41c0c07070a00280d904450001e003048aa01e00407244e03010f800382544a038490701e0002e8000c80046065203004080489104100701c010f01c004a039200000c540c10982038034800040c08500d4065041100d4600c0c00e400216a42004541080820302403100401c5200201c096032080d10301091141980e20744040d549a8060b40e03c0e040400c083c90145502c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 594479460 1250 594478210 594478267
    0x304030b010e070c0f050604170a121a03070b031b090d02040c030e030d02090a08010c0e060c0724110f190503040504020705062212030b0d1401060911 66
    0x103207005110f140b0080b04180d00a100e17500c80209410b003241d55032000c44044603035004855981a202c4048001d03035106492598a91b00404242200100a0005410102d036444a046448203090340c2c240002409440090065074980c40c060280c40a02c101c200302c12044680d0070400c03030305151214805940c0039501034401007104082c44c84218010880c80841c1c0c051404042801080742c0c0040d002405084000c498070019551107201e414203c0c1d280b420203001250b0401c4001c0d107603080c581c014280e0502e002041e6580141c0e100300c4042c0061060f60105005441105c02c0059581c01c48242110700135042c0083c070746e441c4295182907a8089102c404241440d900032081d0030443e08104450140c0000340095440d40c80f43d20706543c1c0c80c0816984060445d26540b1840000c050022802601b6600018108805408004141c0040a0008410390441210303078005000c9111011042210f80c58034000203400c510300358524046404516600e031440c48100140b2a015003500c1008104249006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 594480710 1250 594479460 594479489
    0xc060c031311031509010606021203091506191401121b120e0327030a0b0a0218030a050a05010c090b030a050c0403051203100902030c18192301020304030b01 69
    0x100040c1c6000c074044018040c110b0ba074410801245c5045d0002422212640c0856604101300030340c1c01c3c4070b070004850250055200c0044c001c0c0d001044210590013800140a40d40000c0000c242c18504d20259045402c42514842070480c2c03550348042003041c04a0b40714010400a04405404043c0c1c030103c210758002c002100040d0b404000603544a00c041400c840300702d03076403808200044a250404130100641d075a540f11808915410042440100e046e07000c034a00e44079640300c0c0107940080d00400604e41c0c10b1240d20b104048940c50403c1511442c40c015030042510217a6441c0050135221240303500c404208a003201005100c44000549030492941580411a941c5064640208d8040c3c3e070710151040c41080340c101003544101004600031030fa50101444415241c24038201a48401c3e110b281e8805d81c204098015048815a189841c0c0002401d2841c110703c02400c4202401043d003242d1741e007140000c098442d10200340c1d002604280e007030016501f491324603243c1e014480c6c414400c8210b0105000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 594481960 1250 594480710 594480743
    0xe09040f02090907091a100320180603070305090c0f0312031f0b180406061407020f040e070f051c021005161119030804120201050d060603020c060c0313 67
    0x24480c0d00c015111319403003003058144a11614030145da404440c1c50160100c40e5098204a1003030181204c405800d281d030000082740d50405c4803055010a40d03c0741070042e203000340342603a51604001c600407405503801144c0760424031003060a0a0000f90400d105410003c4081c03056140458000c504100014800b44c50341d4a190001c802642000400007118024a1021544810b1500504402c00001542c00d070317018003e0b4140300440752140200c1001c80e10003c000014850024000c00c2c8151021340500100c14500d0045401e1b240f05400c1e07142c86820180060202c0c00d4103034208801030a0031100c042d03401080c0c14441302c0b040c9a15801134000c48005c550b8004d01c078010422140c040d04820746043c6035101600780754040c2010010003c0c4501004d0082e9100600714030120b400740c94206034040d00d03192600e11055070044403a036049040c407509103c101c1d8145031503c64140200000d0f10f01594407031102ca0030a0805c0e000422145581106106005c1c0c807034044c84070040910380c0702081c00c66082c4403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 594483210 1250 594481960 594481963
    0xc0b010b280e011d0a0828020a051011010509030d0b0114030a02070c0b0a09030b010506030f0c09040905070f210c0302010e010e0405160e04090302061303091809030e09040f020909 79
    0x341340d0316034004c943c0c22000034021b031002549400c002c04903402c892020450702c41040c00c03600541006075214a20305400e1109103000e080c1c0010040e094102452814170070404c1700d003950700465401c9941e1b0404204036a4410180c041c01c000081c0920b01607c14281c2445e42000502000e4070b80000749a000c80d48104120000c0210405012092901038076145007120052100c2501d010441d40d135418100000b95505200003905c0c0200c4024004030302032740e42d02d500d014841d0841c01740740c1d600586908400f404641c060041501800c0740b8038080c42d0b0340b810075003060204103004024a02c030994558040000c204c8a43e0352909032942460f01e26045990400104d41180000000580c003628102c2400f100c03544484041340780c40e415071213081048040100300012159511301c00780160300038000003084ca05518004070f004a01c00c0c1003002d20700c1d882d04520f500b86c0c0b44100c40340d0401d9a5424005d002d15404c02d40303186500608541c0c8008900e416a02c1d60420f5103a1000203006020503008560541c50 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 594484460 1250 594483210 594483257
    0x6072309150706020403020310060513140403030c0e1305250909020d06050406080d0806060a090311150f04081603031205060d021203040e060405040b01030308070c0b010b280e01 78
    0x1c0040460700c503270318010403110084c0001e1003803900c104541c5d45040704030350341c80c0603028224030b400c50880c2190b074503510194043d208009042d8100803045541920030b9807810034602c4201c600c10000201440c024501050ba090f07404a010740c400c0500b80302404c0c8031792189010003a680411809a2510003581290000d0705280c3c001341d6100341002070110b00e90400003902c88004001380c1d202e07007070342d120034040c0080c42c071880c4a030f00e0018008507000d101140ca028807020748086c01820804d440c182c03843c0d007011030307070440e11040c0280c2400090410800008111203549099003d08103980d451039594040c025a1075401c03205001921500081c0c119a00c0890496000c7d4014000b9842d59070011499501e9a202c0c1c040d40e00f24010310b9000c00d8242c141032044a10590b0700c500241d01c680d00319142501c3d1083d00030424420007040004980000d1454040310f40200218451a81c6980565294480540c528483d69540000341e0312402440d56016103810440e050a081c0074940300c6940601c1a12400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 594485710 1250 594484460 594484463
    0xe0307022704080d0b1801050f120a0f120509010909180f03030f180c05040b060d0c03060e0108012919030f03110d0807030b011106072309150706020403 67
    0x1001d041c10007060104080c004c0c0807855100d40c04000341c00711a01002107030440c50340c800352285028401401a81004100d114041c540100b00c12140da6101d5181d038a000b10014040b60041016029101005050402003030341c03561500380b140c10b041e42d070303c00200344440c03611030b92a11a031251180030528590880113500c0c1e680240782080f020b495814003502a2040a8014a00302e00c1c0c04801d0001d04030395400c01504940c040c1600450500e40401c001c00741100c01c1480e9840707041009a101380800900c62600441801d440106c2d00d2481c203040c54004000c140c0c0051401d90502101d80d40610744a09484000c0c00310406103548600b80c074011030700b580420070581560001201000c0140443e2500e0f42030220f2003071761205810980c1801194681d40507503420b1000c6104070001c244031038080c0c1c00c500d10302d41045c5030409495001100300380c40c0c0074040e991a0041411600c2d0400940900021030a003030350000c0f202c91402c4d42800c00f00d2190121246c0380e10f0703904e41c04540c400030070016030110303001103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 594486960 1250 594485710 594485779
    0x50d0b0f040c03151d0c01021b0f0a14040b0402031e0c1303060209120a080a03050a090f0317060604050d020105210c0d0605010c03051b1002040b070311010e030702 72
    0xd03904055502c008003215885420120b69811710811803090001d1a0307008041d06034050040560303d61504441d08140380c21056004030b040310b03204010340720840144004e1404140c14110306519009100071541550704080c080d034010070030000c6010605241c98500c001083e0070798082c1e81d0f2011034a02030700a02d4451281703800c0c0400c00006100d000c0d0050103400c00c085070740c1350100c1c080c44141a0340d1020150000c00c0701d081400150981ca00075440254404611075000c20720b1002c0d0f6030782084040b0340100c01c501007200c250300b03003000d00344c164002607104e4402d450803840c290500c000142e00079010000241007003000505110007112021103003041c500311818074900d6040c480c5003013055400401855281c50701c1c090340080c05601c500d00c05d01c18a81c060f21641c0c80e04406401201303252022660f440e14610807440742420303213032080c03004000030004050b03002d07103030413003440c1c011300003414440c80d40810f82c1450781c12100c080c0040100c480c00e950440340c02c20010f90080d41079048005103841004078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 594488210 1250 594486960 594486983
    0x15040b070e120c030105010b2b0624020606090c19110d030e0f01090c06110309121f02070503090f031009030c1406070f1b0b130507050d0b0f040c03 65
    0x842900240803c84690128000d000d00d0307890781c034128803600851180c04811b4080080142d0040d000c58110701000e4844080440c0d0a03484604a1100001018020124640310000c072400725078103001070741d0800011107a00286040c017466044d02c900031000144a40984c1d082c0881c422400303982d02240d0b201c910015079228068100002e00105203450404020340103100c1525642e44042c07180c0c0140c01e40c0401e083c0403850811030100c030605400424103a4500c0304203c609000c1c0d580310034020409071800004c0c020f420011003920081603005030b0350644540144006000a4008019194a17203402c0d81d80580724024040000c0c98184555900200b0518000045051541c40740c400b85050f4056481410281c0c01142d0840e0350b0b07036044940f00006402c3e40721604e20207100d0704001c42074003447d40070b5440c5440c2c503440b0000f4860045d584010316108040c400c00070840c0a0180c2001414111440860071109480300d2004d51030041c140905005d03181c0002d8104030303000fa9020701464004411900707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 594489460 1250 594488210 594488239
    0x10f0207030c0e0907080a03080406110f0c0f01060b0c070b03040f1709010311090d0f080f04260d0207140402040b0301031101030b09061507060b0405041b060215040b070e 75
    0x10f41441c1642d03800250b010318080801d80e00c000003a9510401d03419074504007240c0e03440e1210001455610311030503040000b0026035513074003042e13009043c070307040c00101400c003040340c07580c2d080d08403040c2e944510303580c100900401e6240300c0c01080c010102c401600589550381e0322031420a261401018004207520b0f0080301041250100d0382c081d00b8402c200307132400c200c455034800003040b0ba070041b8075005a00c00030485078400010036240303148100b90b1150010a0a1044800d0071011a400a400c480c0c9030310781141c129151040d51002c1c50714005640b00c05041c501c0c82c81d42d4000d40381c0f1310501a02001201c1c40900040540701da070f0448000303041c0101581d4880d612840c12204003082c000680340080e0810b120720000f0300e88017450f6409004d00a01412044600c40c00110850300f0420b0300f511025034804100e019601ea502a40340700c1c0b880b80b59601000c40d03405802550310800c41d00104d04644c810300c041c1c21010804112250440d80103002c9001581d19008116417100102c0801508102c2407501e445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 594490710 1250 594489460 594489479
    0x1d060a031b030b0105180103030c03020a080d0b03061609150e030102030a050a0e0601050604140109030c1e14030309120f070b0306031506090f040212190c061b02010f0207030c 77
    0x41602d03c524901689a603a400030494041c8000180e810103800000c01040003c2c000c1961101e018400d006880394505543c503400c100d0f0b00040201002a40c03541e4070810785240500c42c4030760144030200240301020a1803c0208806854000c0182d00340c804a906030f10305005901d000c0000600400a5640346408002000a840c0545203c541d05060083c2d4900c501c901240450584001410890a040c5010340c9810940075416419051081080012000ca075441800710003034514030110300161765168404542d24086039002d0019076000d42d0100c003503603801004581000c441255400500f4104000356410590510000e045503c01c2d0a000140c003a071000103540b264000324103481944813204050315141d0400c5411940c0f0100302400110034400018445070894000381c4219443d17401200307094500f002100c02140606442e14400c4200041d0100c04409041c40e49404030003884c0c0d50411a000308044d0400905000a40860701d4041d1b108201541c01550041e02d10300d82c043c0e072641d100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 594491960 1250 594490710 594490763
    0x408010615080115141803030301030b04030806030d08040201122408070b07030801031e290a0b030c01080c090604090b0913080712021011090a0806011d060a03 70
    0xc0d8082000b40c000011865007403026103908604030389914070750304044500c200c000d0b0b201e12141080c200a00d4058002c5d0780b070400281d40694413803418140c60b070405050140082e000100f081340702e60b01107107004180590061200d0f401580c203080807010b440035240c105d0050103244030310b01c4500a050741d01d085c5441c5241c800501300c0c3c00403000d80d03804a0f1192415100d0784100750700a004903400000410018828080a8400c042e0905044c01860b10a5944484407038400c201100c82501183c2c884020046018002da00080000810001800b00c5130220383c451031a81845070600c80001d0000d6a803080c0c040c00c403001d40800074503069540751211012070003000d8620810b4085c502d8040040d80b044408803099031000d821000240c00d03d070383c80e07403811104105500d0303040450162240e05d00318a02035015000d5104002069551140c125505000ba07001c00ca6001101641c05031004204454902498114103510b48080b0001327035983c1c0c5c000c01d076801240d50004000c00360341109100e94100d03040c040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 594493210 1250 594491960 594491999
    0x120618080711090108210f0403050d08010306050c13030605040510111c0209030a0206070602040f030f12030c080a0b0a0f120c0603020705031204050c0d12121b1404080106 75
    0x1c0d01c06640c944c4485d40e42d5a03042c4000113002c640500f82402016050809484200042e2409a2502c0c2d1a42d980504204000d0f9002011841250051042100d503019459014000845160034411804440e040240e080d11014050a940d00d02040601009100801c00e1030403446003808111b800c020311203030503809160708811018580510700121104e42c0212031079000010000c01e1443c005408210031907010000445030f13aa401c0200084500c0c11008070802103024040e40780780c40c4520b0500000f1150b00201d85000c161410100d92044e540020306581c100e007210070001000d0341070601141012646070031800011051240c001101452440e00110b00c034451002e00c08850742d2084160140d000d1000010007035001070082c0200070f40780c0107045600900640480342d8446c2c5100218903410b5900c3e0054a885440313004049113540c202c042c100c1ca01c1d0b1071394001c01210310501aa0490f4400030300b400c41c2000b48080c64141e40d6200719050f2405481c03004000c02034107507511400c3d09501d0642d40d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 594494460 1250 594493210 594493219
    0x7110d06110301180e1510030501050106021c110a031b0206070602030a140c0a0c03031d010f060602030a0921021201050601031128050c0a0c03051204120618080711 72
    0x4c2181c1d400307214011543e510441a00411a0542d001c050394441c0f02e00400f48400c00d0003600e070002c04074909028503802080550041d040404160a00b8001c20044103120414483e0600c1c3c40260080002010400142c0500e04a51900614660b000c510200c120740030f54052008501c52041c00749990065001d40c5030f84008001c45026151080d00480d02290445031803801405406c03541380c054001031005510a141c005800c02d10340c1d40c0704503008103039903115045a5403007030030000d00c007014441c1340c000d84842d000440c1001c1060f0401000d0542074022050503481200c1e2982010004032103242619500500d034501c40c5014441e0640203100445800d4000313410702000c1d05c0843c4a0b281182c921030f01e6040210450681400c0006d154200d44c9104410050204000314280406000c2c8500e2a403084803100000351071070800e10300d4010140d40401403250100030801061450012890815600c001c0c0880c44071198003100c0540003140e9070240402100058500400400000103840c0220466 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 594495710 1250 594494460 594494489
    0x1204020609031b1912061a040507110f0715030b06090a0315050105090c12100f080706090e010b0a0c0c0e0c07200303180303071205090312070807110d06110301 70
    0x207140c569070380c250344a001700d0b82400441d0741000c45d145401450600c01c00c0f41c40110904140c0c004202211000ca400c2000110001d18500214100b405524810b8003a00014180541420025441381c19000c00d44814551381d07030420411526103506650034141d00801c1e0045440d560f080c160110035045000529591412002140520304003000500801c3c4100280b0b081c0b06c1d40380005210b2031800780c0b40c5400c00000c0800003170555818150b100162a40f9000340160a00d08a4041c020141c01c0d00b0405500d00210b0042c0700200d464802d4039030812180c500489500000d050001c880340040c0c2241011103060350800c5080d078000801841c541c2e10442d25141207081c0c0384001a491151210803680c0340d00100840e0300ca06120600d1130194403c001d0687c2d242050720f65405400002b115220400314401080340e032031900d41401400c0408500c14074107403404c042c0380e03608483d40c403d09000070080b80a00c2000c6c1030300d071100080980880d5002e00200801d90800580311000c3d042445000079003100394 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 594496960 1250 594495710 594495739
    0xa020d0309080703031a0d2301050c030a020f0f13031505040c0302040b0a180e01061205030415031805070e0c120a0c020f19050601060807051204020609031b 69
    0x1e1007203501040d005003500f4140000c80d0f4040300076001c80c1104c54210300150b05801102c0d41c034100e42c407403110f208201c0d6000d515800b4182c003072010008200b081b000d900d40410045a80803080c11294040401900142d4030413500440c0d16047c026001e0200f880b000120b00c00f0134000030160303402d081d24081d21080b041140101c82c440203441341220014143d1129800400040c2410381080400d2000144034000e40e5440d0008032850044070000c1e0000151103000313a01c0410828881c29010786a82c8910300d49400c0b880c0c0303420b03940c0c1c441c0e489070a001e0381c0300441e02c0580e64440c1d4001c0080107581c080c0d0028203011030030025500c080034003072900b401a4440c0851010500c1c1411035801400c0910504440e64800d645407004203c49081c18040d4043d40c58214031180040c400002d2080d031803c596244c80c403803410110700d4000141c2203d0203100c0c861080c41341c1c26410030151003416880540680300b03640c0350f10100d00c550048113000d070b030035102d4003003e64a541c1d6043d0309000c012606a5003c02c192080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 594498210 1250 594496960 594496967
    0xb161a061e03030a300603210f050702030a0212010515010e0d0204020705010603060e06010612020703050313030212030c0d051b09100903020a1502010e060105030c060c0a170a020d 79
    0x4012640b5030702c10418030007014024601e2840141c1c00e040100b0000c1c0e0510307401d0038908803590b18441c0b01507031050244200880c1943c101c0011a12038a1500d6000400001904d0400035940b0345045c0322001c00c0c00720840d6020099000216030180c1013030f101c001a0140603004c3e0009440d03840d815050081c01c00c0d500e512401c2c001c00e045200601180d001d0202c1c2d02800020f502000e401e6403103540303591021010074400d0081e2550004400c00401482d0b00d4284010a140612940e20f111240100803071800709a00c84196a0041e02e255404020582140b42c164a0a044070304550002c034008410001040343e018040c140d1074010f29401c1c4101d640e020908030041039030703441c07000f6004070070f0280883d03a04003810206602011410003900580d20791b000580104000d03844020b0640d4027003840c0004036428012401640e0b40700c0001c0400703504000000e91106590203a581c060400850601e020301c20070440b030390b105508481407150300d8819101ca11000d5100346003010140c8906044036991510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 594499460 1250 594498210 594498259
    0x1060b04061d010305101203021c1e0e060f0f120709080d02070f06030513140d031413030f0309020604030501090302060f04033f14090111040b161a06 66
    0x400090180d046060442c50b07c0c01e070500c110181e00318440c0903214034054280c65400e180c1d101c201c3e00c0e15000090f284e0074901c0c3c0500c00301344c0d17038003040042513125109440710001c0d182041d0301551010384030840c081c02640c2e20300829800d545005504000e01420341d03040003810f03054803c0f180c159800c40c10340c4601a40e80e42c05074490a84804101c0c035082101c24426401260010a00b480c1982c02da0015214106c0800c200556000a500800311f03000720785426204184150780c404141028501d42104900d40c07601610402505011039003204064241c400d81c00051899402058143c0751512401d00500801d00010200e0162290001040360400c1100040d03100c4e0b94103a951400c1401c00c030110b045400202c0d4030089040a40078103406c1c000030542008072100e2400b00f00001d45800841c00b0313039200807001e000065541d1504241d80d00801901040300c094078a103504075a9100348070070213100219090400a070141c412002120701d5400320300039031402280d003103507040c01101c07a01d00750044444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 594500710 1250 594499460 594499471
    0xb0f220b03032b0608061602010612030f030f0605061606060b07120c050a0213020307081506250f03080a0e010515010c02010207080709021b01020f03010b030901060b04061d010305 79
    0x603c2c4007560f0540d07076081401d11014000212000c034009644144992506009507821800020342040848020f503091207100000d003010391400b42e560030603032400341c00203602c1200c002c10161202c009105240705030308080002c1c007001e0111540e034160f184c41c0c40c03d00b041801c4200c403541d04104000950401c800c0540301c0355a0030900d15407600e02d040d102945c006010340300c12900d90068099002c056604c01406210a51b40301001580e6450103440081c5103103c01008841c0701c4c000500c084519480354015079010058080600a00305225128001407081c41d100080c40c00e18812900402c15a000000c030303001d404140d4041c401e00641407411401d0314400c80c0c42c00194050110080495032089050a0480d4010300584840c1912804c3c00c1d402c0110075000780c240c81e600000c100355461074405102001c110904004c50900c1c4072070305642e8043c0f0061058203100e020200106032642000e500c40b03001811041801a5a40e0781d6541c0540603212a81860201c030340c0443e140703809035000b8081c551250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 594501960 1250 594500710 594500737
    0xc030606040b13120804090b03150c0915181c21120e1c11030301050904020303130e06041d0705090a0f1107021912060b0f220b0303 58
    0x60a201e5511002d4010f0121000300401280002844800e41c1000c0094240103608070313070f910f07401c1c01c444606481100c0c80e81340c020f41c4011440034220450850707003030b0040540d81c0210358a2811500044180c0c14814400b03000d150001307000c00c04213046414100c05a0703802c0e00e0b241c60260320000e02c11800c06250300d0140c0708540c0380010501c5004014202c405100642c18031010803140b44079840110390b1000b8005295600c1402c80c801100001a0041600c4243e4a00640c406906181803031300c2c0e000620400d800307811400045402c569013441514108003a100c00070420507a11400c444001e54162481b0740124503150340c40426130340400d50007040030300400052910350314002c24442d0042000b84124032040d9030f8000068640940d0041b580c1000c02c204016403109107600402001c8165850401486800c02508010040800110020a5030000d00c00a5200702c06800b040506e00b1641000740d022500c156090300881c0309040d80c400d0410412030401c0450f0303660003416038901c00c6d0000150403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 594503210 1250 594501960 594501967
    0xb070b07091512140f01090e010e03090d020102030f0d0b010e010e010c0b0712060b030105120304081509160905090114070e120304080d21090b0a021b0601060504030b0c030606 77
    0x464064032209203046156140083c1400401c500300c1c5085000303170741c3d0000902a110041040c41c005004191021342101c000300000100c0c000c0c038a036a0301c14541e549000f40224002c1d0801d6a0085c01941c0000481c1c48096990b0800c003000d4400070f100d040003060100e42c08a0125201c0d5126064412a5000c180c4170ad2a126a01d03480d070390083d0740002c2c4000308200d07045c900c0940c0e07034601d4007951000f4450322130860703240c2d41090200607600307052940381001644280420450b001000481d994481d910307400500300782c1c032480c1e100c50400d00500d501114100d100000010049083d90203244542d91802c020040440c0a00b850406084203468107800903c000d03006079070502e000305070216600281d81c2100d01d01b03642c0715066824040d10f001d0500100b980306a1105143c01202d56114412104601c01c100c1d403000341d035900c01082400390141c1d01982e4003140c50807028070a1103203080e1281e105011500130b903a503080014010391040c0001c036002c05900d00030400310030404c02580d002e1400140321609 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 594504460 1250 594503210 594503249
    0x80303072f072903060f091816060f030912031d0105040506100b0301060c200a0b0a090e1302011b0611071e051f0b0a0b070b0709 57
    0x8901c0801216200701c49504296008070380c0d810000e14004164000c40003201451242100918404503540241840820002c0150319690b62140c1c06960b031048445107096141e52180c1603070004030341c180c0081841010700c0341e11907d00c0c2002d4039040b900315641d8464801400c10f411015554582c3c1d000b00f441002c601c0c1c07080400d0003500050200310345110101c0c0c1500350200950709440d001e442c03c0d101a0041028043c154601d61881800f405290280d285507524241005203024100f030000340401128045255009031640c00001c1e91650048c90084c0c040d4030350307004889960087c480040401d0058a002801c2202e48601d01d02c00c207032815040c400c000351900159003460114001c8104030340c81e540e03c100001c0ca148100040025954941d9486010a182040412031510903d44507800c5038500703000040e2001511502c071441e124241d02484254205050142881d004034607800200b80e9008916114050060003085014005900b51510f4001d4250f4011015014140c000340740e0511410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 594505710 1250 594504460 594504497
    0xd0c020d020a032001150603050c0708070308060a0b1201080c010e0a031101050c0d0206100e091b0a08030f030930031906090c080a0c0903020f0a1508040c08030307 72
    0x100c8403150406134902d205401020740e400c4405512080780c0c045000c00d070910025525128056001c58031940c0c0518200d1703640c846150b14080e2450081c00c0000c01e01c0054000e46440230100020103007106180d444810000158030109024081d41e1614030070070041001d1503100d402d42408444000d0041085a41142c0312070f07001e80115860213042c8002040001001a0204070b0016440c05580c040c0282e41000050501d100105a01000202c1c50203c2400b1450305c0105221024000782c0000500d0519028082205415a079200d40c00d24080407560230034050300600218414140f450039524920721a43d10620700800030780c9003010007401d124818454500040041d501300341e06a003d003a00d030f01110800e60950302180c00c00c2c1405d0782c40b0055100c10a810000c103980003044030200f404070b5100c258004019408a2002030b10498142d00d8090b899110383c0c40c25000f401d035804002c50540d24102c0064449001034a00311071140181400050b416004016070780146025981d800c0d030700040d5007260 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 594506960 1250 594505710 594505727
    0xf0b0a0308220602150109051b0d110328020c03040e070203090a030f060e0705011d040f020301240e030d080403180303092904060309031b06020d0c020d020a03 70
    0xc01405004200a0786151440100310003c0c0b050f5801010049900c03424608590010707480032500500300070a02003400701d40c1000c07030443d024801c41241c4800740056004090890348a4802e41810000103105810258081c1c040b010004c3d0900c203280c00d0381100d0b0b01801c034403d060390110260000e000600c0b807040c16151145e080324040c070440382020403420010b80600f51591080318684005d060b070070104800c0c0e0040007203c423607800140c00c40342c0c545030004c0e1940e040c064a01c9245151500508a5076880f58071120403076140540454696031038250494006c036902e40d4992404080c0417420900340d110745241018210081c015100c0554010000e0315400e05c0603004405003d0741d02e20454103491989440740083d4000d40d0740e40003480c64203001448400d50320003110328180040004095400461007150102d5500c1d1038001860155801c0c1210640710418038030921070841d0103160280321094000c2d101001c4100410407403201400e4050703995502c5190341d030001d0381269540501082c080c410b42c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 594508210 1250 594506960 594506977
    0x12060703270807150203012402150f070c05100b0a0b03010b0d05330a091404080c01151e0906033f1d0904020307150e1003050601030f0b0a0308 63
    0x400c0d001c0e000307001307000e0103a0700260054210300015100600d40544844607040b56044140094411060808002900f258004010444d500d031803101059803140715011144039a42c01c882520200e40c0b40981840181c80d503400150b210f03a41140d80414000000340482c0d04036055080072625001c94851550050302000300b11241e43c028031946071903202240740e00f01c1010810442161440d0340c041013004846031041e042119043d14103003d510f0200c500c0c0c0815600950009041c03500c2d2220f4151030750161005401b8500f000072a020f00064a04030306030608400c20040d080d425045840e001114100c03840e510000d011100220401c1e45482c00d000707a41c070202291440c004031341120b03644404c0340441c501078218000440c0030303d22070310f01e031a041942e0000103001c50f50784045080c01c2c5c0000365241068000d025001c1210304400020324001c445129076007034081d1244014800c015405001040210350f441c3c0428181800701a40884a21500b83c038400300600076030f8403600f103484020366900010340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 594509460 1250 594508210 594508223
    0x603050705041b030e030f070b070306082805030403020a080d020d0e100e0a030206030112050601090b011e0c1a04051e070b1326190c090b0f12060703270807 69
    0x41198540a1000a001c80303400b549c07191100b800c1642e80113040310344581c03001c12680c220035000c4005800000940703106408000b00070b08ca0b0b035000d0501506602c2181d100a510207104400090702c00b6010440f40c0500c40702c2e4094541581140100740c0b0a66404091103600140c00c1c80000181801180d02d40340f010700c058000401c0580329400709045510a070044524075401586940c00c11104000183c050a13401d1414014a41d92000103452041000ea0700001d03d504803400e055042c2c0f080110340e0701d65030440c0391103a07131800c0c1d2203098600020a40303003980c407801164034208120301c85000803440542c4580080c10072500d00b1001000580140b40c010808121841001440c030b00302c0b00c001d038030f82c2c090800c2810701c040041c5031309031034200303c00e500c203a1001002d42068013291881400c0743c119482c0b8040480e2811402c3c0000e0841c0001e1440154000c0140225401110740026000c3c8100301c6a00c04010451780c29190100041c825100503845c182d03924460000240d000014164040c402c18 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 594510710 1250 594509460 594509467
    0xd02060f1e07081e092d03040302010c05030c071202040b03211b06040c0602060601080708130201030e0102030403030903030501051903080c01020f0415020c0a080618100e010603050705041b030e03 86
    0x3d01380e00f0f401c4207944030700d1541d0000398199400c8404800c400507045181810390543e40101341180d807a40a64400a410b00110145080c2400818000c8030044001d28080e01c0c1d4940c0c48090b01064102099030507070050389017400080f10750500084d080111002c2130a20002c40e2507e40c245803a552220a4800d10149101900110540c1c1040098050344c03217600041c9015042600007460b000c0010001410080b401c828001c01a4000041541144600a242e040701a65000590103400117901c0e0103102c0d84000100414942e1551050360054803c3ea41030000d40d0340c800410800501c8080ca4040326000803a0410014802c0c1c4000c0010501c12070000d410120110f121313888582040d801440440b120310415603003580d0500c8944c6032900201c41100405040055007696510f00502d003000110301e01c0c90200c001c080800114480b002c0110090280d5491070085074040c020700c1c0703c121903d2290540101e030600d0f082c010744500485c034102c1c00c1c5410030081e104070080c5c418010180054001007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 594511960 1250 594510710 594510751
    0x60f060d090303020903072d0f0b07031b03080609090105150f12160906080a03090e19020f040603060801051e1308043809150c0d02060f1e0708 63
    0x180075550007094840c0c1a8440404e58482300c100e2104092012071403031219180510041c80035200c00010341d5001c0d6901925007001d0301c3e0590b40c0c200d500314103c1c461038250010000b01039021462a108036001d4500781141d444d2001120300b079501c10b4070804100c00f031292680c007480c1004030000a01c2d2000905940c102c00c1c2e41114241000b4091100040840300341d1814403161255000310001400104010f005203401c0da1001801340c4181d000d00c03039044565402049580d20210841c402030030600c0f03070440da140c410319121211540b0500c1400042810f003440007580c804184682032140741420201146003880032f50b203821400c1c0042c6010b6000c0103204244022031310001c06800a011603614500380060403010200f50741030a0040388200c00703060401c4060440c58002035400700c01080e607011010060140804107540240b0401641c540f2034680440c0c580d03580050b549010b82d0981d118441c4c65120060600c401c0e04038803081d8005070040c400801e0203a4070548645501c0055100078004c00e800d00b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 594513210 1250 594511960 594511963
    0x60f130f021f090e040201090b073002010f050f0c0702010c06090f110d020d110a1215200909070c080d0603020a0602011e02180312030f060f060d090303020903 70
    0x11006003035035000041502100580c0c200d40200c016103840c1a034412a8035186d4002810400c19001e01100004089081800c10101c0f01c00c41c0801204403102078620321090340c20760301041c8032510b074600540c00d05108146540e014458240680844111420310f036036648081400da9001d07241c12410850907110800c013050040c865115040e116506052288901d81040e980098100c46007920030103e40e03c0140041e07031254039090201e60301c00303841c0d007455604c0d00014005244c83e0780080c0a001d0610500700400c004d4805040c3c44880a02d01000903108001200e120b070440540ca440c5000400c001110302850090101039010009103840a1005902e85d40c1b90590b800240407800c0e80c60f00e55a00348218513003031390700384040c04052008100441202280907a0240101c0c9410301c001c1d40001d07551421448103e0032029214060200e564008528009248603841280d010040980301030102da40b07442d02c00400741c2c000000500301401c00b01351440e088014030400c0c4086061650170480100e0540b030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 594514460 1250 594513210 594513229
    0x24071e0c090501080c0604050d02010f0e030a050109061a030307031d060c0f0c060313032609100606180501051c0f0204050102011104081c02030c2b02060f130f02 71
    0x1d0301d1004201035151281c4c4030b20300800d0040c424455842444144056111001140d5000b03030246071808200103100d405903049401420701ca80c05001d1004102d0520105400840d500d0740b0540b020050390000018940c0c1207039a04403201d030701d40c008000c2100840c0c070030034090182c3c064284d452101e07188a0000103074a507002000014003904401154181108148180060071105580c2140b9600c3c0c0845407000021b08100e0003414071043d106c01106c0e0707950700d40c40540c01c50b80704000c60440b8246103011942da43c040700c68500340305041410100302c90b446007542280842581c2950085035040c00010745e169040000914150b41c24400116601602070080720300380d0800d00300042c1c0d42d1381008002400d50741240884c83c150030b02080704020703050002454452240c1600d0b0390f101011110032003241103210366079562449105218800308030705990040311404202c0000d007440e1900500c4000d81e00c8240440d0569138101c80400052040300104101c400418400c1240c0045200c1c180d0005043e4039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 594515710 1250 594514460 594514469
    0xa02040f061d040b0108010504020d020c0607030b12030906030403120e300304020904060903050f0c0106060e030a1505090a02030115050415030b0a020d0204051c0224071e0c 76
    0x1651403403002c002150800035441c40350707000d840c14001c04114800203800c0300360600c111402303941d00042034003840c09158140d0349480e24000a07102c01c0d0078020b0b00100504280c4183d1403041904403482c0383c0d503507800412548048006041d05082d40da8035102516850340aa0001c01020307102c0d5003620101c070051005480072240c4099200f19100d201c2c900f2220840ba001038a98005010004e02c40582d49028043d980f0681c4900046030300388180c90300f140c050080e00c680f04100000450107108141c4c064000c0c5060716069510303a00d04002e83c1c0101070780d464800e04007612544401c140380c6030040194101c44e40c000012402c40d90b4048543e40403908403900c0744051029064184070a0109180500890100441444a00c2000d41c1140c4909031a140050030310700f00350303500140010344000181c0556000b080700030300c840500c154010b51407a41d07040c6050102d200d07180801c21407522903181e03e442209205111001828900a9a00d500c1c0f01910110717502d101075102160000041c0921007004c0140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 594516960 1250 594515710 594515717
    0xb0304060507020d0c03021504020324040201030f0203040f020d05030f0d14060409080a051c0c0809010c021c2708030a0f030207024b090123090a02040f06 68
    0x7403405036002814505021281c1080100e21010036006c40ea0005885503664480310411004c3e03240d600c00a4580301c42000c2d10005415080a040c0103560700d10700c4030384510300070380f01489024842c043e2034040344401c48001b48a0111205c1000141c00c00b082d18500007803041c800c4a103800d0000d226440160040324140e14403a40f900c860811042110b8021030f0004001d80c1c0034030920789980e5582a0300e00908006008110000c1030845030102092030a100f2607401e410f04125840c144003000380150b01c22500c5a0b595800d00c1d16140303041d440050480100c0c141c1030007403542000b42c11800c80f00c40b201c15002038490190200410491404010504014900c03403005556038080ca46020f0601070000c078500007494818081c000250300c03065800c2c02404405140c040000c44083c02034901c0840c0745a904407008802242881c0c40e00003003410001c0200704540c040003e07031341d510865030f001804540352080d0040041da07903c01c500b001c09489400c4010210054202512611800c0007880d40c0c4c0d0068000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 594518210 1250 594516960 594516971
    0x1608031305100b120705100522061205181903140a0306030c0e1909020d05012d0509070306020a05071b1d0f0105060901020304030204060311030d0207081f060b030406 73
    0x2030b10788004001d1101c1c1200c1302810040b413901d400140381807024160101070100000e407414100341e900110560303802c0084140c00f1225200c1d4802042c40c8007911140815034a08408200401026003501c2190010701c001005010014420b580007000060000c07000d0288100350000003003150005050291883d036000901d0030b180d0300b00800d00408a038002215919690140a8066042481e141c407040e10342c000032682e0b0b1800d2001c03820b0710769032550190040d441c1c02442c44040b00b80b085a60714401000300b26580c00c0c00d240da40c400483d20305a0b031003001c55000744070400004000740c01400018080e0304216007815500d0721483c504280e0244210b041d802204014000140140625494015041d9000206c1c0c5014088040600010f00590b48124004602e2900390fa1080088601460b80604248504c560f64a850078030180c80c251a24131034001e07081e10101315880022203000b140c21303840050440d0914507401c000000070b01a100c4a84030384800d0049180390b079180045020f180305600c001403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 594519460 1250 594518210 594518231
    0x6060305010b0a1211040b01050f1305040f020a08040b04110603041101020105070503010e1906090c020f0d0e010507150902120c040b0306100e0a060918051002160803130510 76
    0xf1119000041308006500b43d110101e0220090100d03010b009a40000701c86003900016100c038015108050740c031610014400481040440c46c0c4030480b10f080e00c051100c540881c00c080c05900030151002c0020700d8010025002c10241c016103078200c1d01814800c00c12420b11008544540c0c8200c4054071517015809400b1442d50742403003442c1e032240040c80c00b10700795410309403410041240a0410481795805058a610410b07041d80060000d01c0c0050301009002c60f4a00081e46031201c0e0400840f090203081700040340580101c0003010b405c64140c1d1000d2a20f40c12b42d54203450350701c0c03440b0499032995544240d2070041e00c42d560b5030000004004010843d0b140800d0401080e54000403c485c0281c0141c0248010750035070049450903540f442003000b6041d41c0700c0c202100200119441013400310300300340c0300b03984000810010345180360291702512400ca4a86615100317a00ca02030519500c1070902c66542c01080084007d160450005450381c0c00300354240d00c6a52420082a0131003145a55840082c0d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 594520710 1250 594519460 594519469
    0x240f06070804230a06030c120219090e04121d03010606090e100e0106110f15062d10110d11010e06010b0a0c022103070b060103020c0d0e04020706060305010b 69
    0x28803106403000540f03c60320340440862040c15203845440180760301c4510028003280100103148060190810864460a50262060340341100782d0014001ca91a00c0001c00c0038011281081e1069800c4488840040302d070321011191b0101c01590183c00300b0800d980321b02c3c2c03941d084c080e900081c24581e0361290041d0400107641069180a00340090700b65403103208000d03400c0c4800607a4111036240c2800545a0514503140d410728000590501e41409a00c0c01e81144505d10710701240155000c3e40c0c0b810140101310150103d80f00d080e0100c0d2051802005c900d2007034038003604104c10300701142ca01a0760580520310814030f0305020b035002c5400300c0c006003920901c40703c00744644a00012040010150307549056a00c00b1240f01c0c0c080c2200070485401c040405540f1482402c42c26050308100c03594900c0c0045100544135000280111031141c0a40041143c0c2d611a0080d10040c0403100050400f00030104000c3d14034071303003040c40c0c030341c01a0f001c0c040724020405500c2070301d0086000300000f181a007100700800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 594521960 1250 594520710 594520739
    0x121704030510061203020c01140702151803070602071503140f07030b06040509150a0e0702060f01050a0305030d090c2d0617040b0606040b0d0b030f06240f06070804 72
    0x1c1091303604810244002c40d44c006455000e112080c20441c07085200103485261604c51181e01a410039400449003644a031180c1c0240b1000c261070141c0b2500340840410913440c1c407170b94490040140d000304000d00090503058004007441710507040c00656400c02803140c0160f0381044070380340d141981d4081048840740d0180113021442b082140c000c0c1c50079090400244914801038070b4200d003100000307203500d00c0c0c1d01d49040c0600a4408404041824503001c0c2c0c00940c0d840d400c8030140c40c0074100000010303960503c043c80e00241c0398043c2c091400c00340324008610060800b1981a10f0202c3e10410003d00103100001601079400c10007180c02482c0802d080354080c0d03030f07601c2d40000100100300e4210b12607a00c0342249550020350001e00d80d5903c0c1c48190000d809130056400108284ca0001400c003e05905940000c0a0030300a034295004584546846911440202c6103241c80301c80398140303400e000b600d080c080e00918030000c2c0818a03c0003c1804a03000350403030b940898503141c0000d4240034040d0001d004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 594523210 1250 594521960 594521969
    0x1409310c0f050c070f0f0303180506091309140309040515060f07110907090918051b010c0c0905041a040305040504230f07030b06031012170403051006 66
    0x40c03020006102000789808814074000040000108004146107002d0204800800600c003415900644071090003482e0100c41c84114042000030340002c0200b0201c82c6038800315400102802c0c00d041d80340040c0b0070110440c0d80b6010341ca0f41e039400140006040301080600c1d80614000458958a040041c00110385014003090080101043c1c01002aa6504c0031140354218100ca01a10340c0380900c3d28440c85c40001c42e0055020148804011003183c1c44480b0fa811141950300510225500300c0d09080108000d10000d060f54020f810468081c4031515480c101914061400c59003442641c1c03940c01214180341c028041d071540300c0041c030090060841e52440742d010b050030107640b84e0402d80e801405c548207a22504d40500d84440c140d604501d40326000800c1000f0b4105a401c05281c00c40110080c1a421036012000c40e24012100d50507062400039a84102c00da0950455146c1c204031044031568a602421140c00307500b000200e01c10990f600280000714460030040842c510030552800542d09942c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 594524460 1250 594523210 594523309
    0x9161205060a031b09020f1c020c0a02040e030c06010e04020108160e0d1419170a08010302150c030d060e070809030d05100812040306050a060806071409 67
    0x2803010540c0d5500700c0408513540074001c080d160070f8840c1101403400d140d600c40102d80d440070510503440d03030f004402060a50142c4882c0d0004500c54082a07049004040c0584580c0d800b000c4442c2c018102031f40081a460300c0241184d09180d24005080c2c90554260007400d1940300c100244011540c01c0070130250002c42c000003051071031300c000300e00501d400040e01405104042c000c841034144440003014006404aa03030039600c0d502d00010f02ea0f01e9008040710300315240c007014a00341074408403080960300050b6459982d802d8a929607000c120300002e889002002041041140c0c0b4101c81040000f05446100550041089490803400f8100d600c0000c0030b09082c0105601041010034020084544030910300000107001c0e104c024a030784140d0311039009000345124010903c64031482401c045d00407244a068107000668910500c042a07403000e10a20301d09600c50000300d500c0741c0c0a030303c0306407110015103941401c00c5d2070140000d51291300f01c800b89282e0101000404038500180c908041f41d00d10151 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 594525710 1250 594524460 594524471
    0xf06081c0513030b0f070807050f0f0714011e05010803030417070c08030f040e31050a02040908090111120d0902010e030d090f0f0506190e091612 64
    0x203a05144084042140001c1000000380b490448582102d00005181c000f6a08041840c03d031200d0500c00c0025183d036004a440b100001c0c02c3ca070721690454140903901424030b401c0a18114440780c0c9a00000f0302120a0241908980160b1500f48140d40841403143c3c1403040b039103103401c104012a00180c0003404980c00070410000441c0004c09000f01070080c0000307a650b00d02c1141446a06014035403c2903260340000a103d000340502100944140c0d0b00c55500d00607661621944c107680c5048031040001e10070000360074982c0000c6181404ac0d2654000c40c140c6064401aa000404a8200c08002c82c2c14407004502c410b00d41d41c0c4500801c148515800042c40801025040840f80b07004400140080580780c219000859103d41e954510146014040302c2400c0140d0300b02421401882c00b581d805981403000028500d500c2190700d404441c009042246031820a441207200c048000203081d007031242401c041051a01d03020b4945201c0c404440380c5a0a0302c02d0503d00408000c8401c42a09481d410203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 594526960 1250 594525710 594525733
    0x21140f0307020f300c1c062a0201090c080a0b01050609040b060309030910050304080f03130818131a0607110916090b0a12090212010207060f0608 64
    0x20840e01d02540481c0c0340d020181182d0009000a241c0c102881d08004030b280d000810302803400c10703460b54510482c007516541c40c680c40c18002e00d1004d4400300307074154083d4a82803010804507484540502d000d00000d8880c0c0303d841c48030707402050001c41d0781c80042c1c8d9107890038020b102c941200903020b81100f6010740317400c1000e49c41e0305900744010700130244112000034540740540d03a1a44203841c05031b805130149841789005010191660003036072665024099451102c072440780b10b00220b03407003940c0c020a0175041c8610143c12100c1600010101c22071060400036000104281d940608442d00000940c82051903a6009010440c14000c60402e5010300300400c0540948100b811110300e5402910902e40322407650419229188046200c40e411450402c24800140b02130b40d260380c4002010f45942400035039900300e000b410301c070b8041010009105c1c0c51082c507101049800083ca09400100a101381114510441d8226801484103d40e003503507034088088203101d00c0c01042e0040900001403c05088007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 594528210 1250 594526960 594526963
    0x30201080a2f040f0e01150302070305031302031603060f0e0d050d0b040f05010b03150616110f0402030907050909071203120e0102160308160e1921140f 67
    0x10300e00c0c061042400348846442c000c02e04040e038004007803201d480f103220f0340da40702c44480f404002c0c0540220001260709482c00c80e8001d000304c0d0b140e00d9059852038038595591f031680311b11541190702260f05000305d00d0300041156205054102440c040c030303800200e8071010100101292003d03070400089402c84148c48900d950060309035542c603401306034007090011409001a006040e02c840c070144c030300e1600001082c00444075002c4d5109642191041c030307480060303c08010b918080d8101c0704401c06412002030001888594004102ea5005019030880c980325800150980e00121042072280d448600c0070051071a0002c22103030032810311400340c0849803e02841d07224840b01c0840260901445019040c0421050307408000109032481c000c6490705410b16030303001104000b52054000402d00c0300441d6100a1001140005421540f1140750700189103013804550042841d9132001c000e03c840d80012465030b48450044681000c060756050940e40746800c1622b461041089031003503000440d402e0701c0480 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 594529460 1250 594528210 594528251
    0x9010e030a0f030c0f1e0311031005030f070506040b0a050702030a0305130501210203071b150506010809210702040e0a14030307021b0a05060a0e0406090b030c0f01050c070609030201080a 82
    0x138440461881940c801c04250050a42c03231074030341c005020000801c0002a4140c8121050f614105d09669403080e0402e0725968802003409640e030311503c1044200103440c0e200004140c1d4071410f051082c10440b10782c00281c1010205074040e0041580003524065600000d450f00c0007a10f400d0a080c0a41c0a0003941000c40204140c0261001175002000c98152405520b180258040c4900400c80213490751500702458020b003003000b070340302d400d06000c50350b2513010b0002d96115040310b40c0189201d10050450030f1800030b07500300c0440d661004004800240e110340c02440d050b044002c5c010704001c501890020400c00c1d00e4090480990014024002c0e00c0340d0109811a80c0101810715000141801d800100300407190b070b200315401640051500d50b515000000400c0c0024101e404001c00e40d504d40c3e002040e10120f6500c0307035040d0822030343e03d4010314004600081c0201c06241c01c1e42445940745807a488d200c010380002011a0281600304215a4040801c59000003401c106004014480402448050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 594530710 1250 594529460 594529487
    0x6150512070c021c050c1e091909230109150e03040b21060301110906030c040e24011b080325050405011103180909010e030a0f030c0f 59
    0x44418000c1008240302d000c040d05034a80050120803894101d4003045085000284102d071a80a140c03580c0102e40b421582e01074400382035160203c0382440e40400c000e00e40400604241802d10340c506600b101070018861440b400f803180107100706440c6180404206d0b81103429050550742e0400c0309441c002103512503940c2000e00501000300d0502080c01500e8210b001c3e9401c02c0e0f00948000c5280d0500717440320484045040741c4a903607504c00d51503d070281401c1e00c006e100c240404080c20042c03030340503040810085521254002d540e1f410701e501c595588001c1c0c1c2d002d80300130745208141c03600003c1001041035080f42030718007402e05c000b03100300b400c460ba54409600c260181030a440400024203694a0390440c5851002407004a15042185030700139160350098003c007800a0b50803d44061071600000403281c0c0032461444034030301c4e880c01c1c2e0100004000014090350f2f40e5500c450303001003030310020409003400100b0341d2182c00600c60b923403a000b0200d80320842c1c1c4004000c11546a003540329048400200c11070f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 594531960 1250 594530710 594530737
    0x702120102040b12041e0f1217010b0f091c02011407050d080a02090a03030908150408121e15041404030804060c02030c0f0f2a040f0b0315040204061505 67
    0x59649081100b941b1a40e802c0d010300f845000807500301008400740c444081d1610440d41002420703800041107510000850f00c28038404454001030085580040240a6584203041d0a80c41c20b24a00d01203400410214807642d01c001c02101c00718210f60f0411846440100b0301410780c0c1c10f081c1c80c0e441d00f82c2d50b40c45a50042c0c05114031308003c640c41192a404075900458040c1101181d1a030781d15005080c08c001c0c0c49902e005020703510130821407200c0240f10074081c5400400d41424a0801014880e4500000c0e0100444040301125102000a80b0303a01c40d214001c0300c0030b0004070070003075014407007513a1080302c1e00d400c040390440811002980040c1c000d50003a40107100003501e000c2c8020103034030f10b100b811901d45003481401c405000141002442010361345000381940d2944044003410041020145401d415982c000201940c16007020b900030700d040402c4000208081c8885004a410f000680303141d4802000300c02e0070031040d42003038042c1c000100814031140714000e0408000510a004003004040710 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 594533210 1250 594531960 594531997
    0x402091b190807081b4b360a030606080c060c0d03270804140405040308180709050c031501080702030405010e12030a0c0501050106030908040504090c08010f020702120102040b 77
    0x81152440d10040344480100b0194210b0740c0c0042c882d64032424215268150783d406403c104010320400203445412030100b5407105d00305e547c2d070900d40100010503a014282d030506404100d165407644406002140201000560b2a0400c0041420100b00322696805604100842d10303140c0e00c0011007400035161032500040384d415000c0e805d10070038500007031044941802e0b44200c0034000241c004104850030f0076284903018801d1401d0009035841103030040c01103060b040000d00c3d208400d4003103070105041c001c2681c81460300c403000705044490989040304030a50120406c0001c1c0b0f14813100d081c01c50780900344007a85107000c510003540c0f8411401024100700d8080e00c0d14880e40c840d12030b0000108050410f032912002c441d90000e068081d900301c162003035070801c4000190b1070300900c6400000d64020903202c2c2f5050070b060038000580300c9420b0803120380440c0500050200800c0c0700302030700c008082c4c4001d42da840300ea00401000d54907801190380340ea4410802041143d400340c048454512900f071000c040d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 594534460 1250 594533210 594533227
    0x6010e0f0423030c01020c1005090705060c030706090c0302130e0316050703080703030207170c06040221010603080406120608032b020d05010e01060c02090402091b190807081b 77
    0x185201c00848142e41c0e80b1000c5039120b4104810b401a00c0312501c49801c1743c040d11000d400180030b44a003507442c21030340d07001000140401d00b88440101540d84c51101224500704240d52107004544042e0400d0382c0c50f440c0d044081c42145070011484000c0b00482d88140700f111240e0780e4007900c80c030070280040c038004002a03070358082050034050310b001160400100740c1c45403203070b04014001c0d511483c8201c4040c03030040000190091030f54141c80e481a00382004082e01da45a500703200300040c0361401d041e400300d41c2c1101c3c40340c1d003902400b41d45e002e14451329005031a03d00d404006044458030342d1500c3c195500b004402d07c2121400019210080307104600d20f020032149215145030007505420b00f2030b206000082403003112446030401c90484580b80d40e002445c1c1c0e69008111000441900300940c0001e140c8080380140c50a8844580c000401468001c05c00d4808041b050156024400104da154800d00e40740403800e40055800303a000788903041c0155a4640314818040455000f0003202070b00c14046600178 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 594535710 1250 594534460 594534503
    0xa030b040c09140111120301060206010b040e130f02030115060806030c010c0f1407120c050d081c0b100810060e03071802090405090102180f011205060402090d1406010e0f04 76
    0x50056034a02c05554a40c02d40f90a80e07401b65000f4010100944642c0c4000a03503109000105c5003160040115044c6c1906c403e50300d240300c130100010543d01078582031f6541000d65000c0c820004000101461051014a0040301405244008000303611070340000f00310f400305917000100c00540c282d0204800e00d901a01c0d250007a41003000840210481c440e41102054444410400d040c249005440c40c01903c3c0d503031010403d404400c0080100441010320031445815030303110500c0d6407007103102d9001c9114a5040d010644481c1c2e5020354400148a003414400030b00140304400c0d01a0140c6c1c82c1100141d9240300203c0e5442d0341607c50415039900622000c6c800c0980c07541030710b245500051040c0017a003004c03880355010f90449500c070784c0c10300d11550320213001e0f2529510080c840c00c4181c40301ea0489035401e0729000140300003000703c0e401a8007005241000d076680d034510030009201b1000102c074512907030203281c5801c06c16006407006c000c15500340b1001001001d8110341c81940442040b801c28194007109 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 594536960 1250 594535710 594535727
    0x11401140d050f010204151803031b0c0b0f0d0e01020306063001030b010302031e061303090518041b0501120f0902030601080607030c030920030a0b0c0a030b040c091401 74
    0x5241c0355101046c04074210351181106040b00300641c4d22220440842c00c0e107516540d86500c40100482c0c2c0d00b60750b0a046100c07104c080c05282c2d00800d2401d94850303a840d51120540c1c40441181aa000c0000e008020104c4a106410494000034000c40c1546009800300e10b40d4440c0e0b48005140301d00041c0f110201d10b5514155288043c4090402e042c5940c0d280ba0481002c2400c0c00b0481c0700340280c001103406405100c050b27101d03400000700188241c1d10740261207046034003820300507400c000d00194003160340c0d1100500d455015081c02c900c600309151071b0412004042101880840103d20b401d402c101a0b80d1089040800c403e0074076000400501c9030b41220014410200d00a40601514000003020300b00880d00c94410015500d061140c6151204101c04a4602c0700d0b000301041078071100c00005140a04c80791003240806800c80340084140e48a00c5c070036420484400ca020700000404901c141e601d40100c915000055905104406c00c0800103000908140107220300d08080b0980129181e100e031460 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 594538210 1250 594536960 594536983
    0xa0602090d12020705090f071d0409060e0a03020c01050403120806063a0c1418060d060812210709090213050a060e01051902100e010e011401140d05 65
    0x3400901002c81d010751502460b110f041c0c8590742e00400103000c105030b05452445555141e817008001d008104c0c0c01c0b9461060350403c207420a03a15001d081c00500c551158001c071756010320080010003407601c0c000340f8164440035800d04000d0103001c104006404044050600c10050500d12250780e52030000c1307070140c0180c008070f4044440e1070032841502e0302e8002e14151041803007507400c025100c403114010207944590450340c00190020142040003a60380d005401c0300c504104021100341d4104001071500e400494607400f00c1950703003408100c001d8041041e4804c5d00c400044641c20540ca071850681d0585c00c081142503084000ca0004052501c00d030611000b401103440c085407a0080344002c60720002017805154040ca8a000012810b58080c2c0b400221028050756003900c0c0c000c3c0da5910a80a002c00c0507038038294482c8080300803074140d00c1d02904024a42520002444442034a00d080c20740e0b000c072480201c0b08039410014045e0320030500041030003013800d60b19030001004a02c3d0491802541c0a03d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 594539460 1250 594538210 594538223
    0x70c0203011104060c0309050303130302040e0c09040c1e0b09010f030e10090203070905090607110c06190215070e06090112060314371506180c050c0a0602090d 70
    0x1401310300e05412200c1840f030680030ba030341c0c0c41d4520b40f030710181030b901c0c4205a4a0408030071070310010801403800e90400c052141030b500640780024045404943c0300c020a60382150518000c0e80180322040802480180d039051401c0d112449924144038420f6511502c16110704010500995541481c0607030005001002d1070011910f40c450212884c0c801410135030401ca1090040d000c00045001560181d1b600440002001c1e052170b4070b03110416180c00061401c210400c0c00b80c006980e0a640c1e4260180541d4071510b41040105a948003000b41002d140e00040c26103003800b40c052104240d800030340e80c0408002550581e13a20395018005a500c494481d98040e802e6050010200c20001c0f030050040010303035900100d40114070001c6801c2a8000603040e01400584040049a0218201907114180038002e8030f4402546d000c0a06041c15100c1d10781002c1004c101900c0c940c01d5113485440f50840020b03052400703900b07110100c00580d03201d820030030340a40a20740200b0b006405985d000c0180c1c5c64158000d9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 594540710 1250 594539460 594539467
    0x1020307051020092809020307120e06101806050603090a05070e0f06090403030f020c16050612010902030a060f060e0108100509040f05010e010207210207030506070c02030111 77
    0x1c1001d015003d01c0200d0b16491000100070084a030400c0700782c50315618000c0c8803801d10190b491910103802004510314524409040c000130310004c19100540c002c42c01c07980c8078043d4442100145055500c103004106c4581d000704c0401c0386984038220f09009503a2032248200040d901260758002030000e5801955200c8000024080e8002d40001c4c04103603184220165074000b40d44810311450722070112600550040c00c5400181a864000302d502d0b8041e100c6d0a00258841c0110741c441c089070000f44400d0348aa001800042041102404800060600b00e800c00e141240c25511440013a2061003141e8201c6e0300400032403644d0600303802c403030050418400b041c9941c40c1e8800c40208842e00c050240d42c0422054808103000300790800c51201034410140860000e902c581c1e4440c3d0500c001401c0a40c0c2079507131034100e0705401c1070071300081400602a0210104030000d9030411401c0685a60b06002590300407a400c02c00210045002e592280031810b0494030f1403c80d00201e4003605034174483d48000c00000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 594541960 1250 594540710 594540733
    0x15090304080d090801050f09120d090c03080702030106090218010804020409120512061f05070f1e05010b18040f0c03020a030b0f0702010c120b120303040f03020d02010b0901060e0102030705 83
    0x919500c3c1258464402130240c0d80701c0540070f44054405850f00400354003c28a02c982c00c2111000820800c0c400850000c1c1c54a125180d0000c01c59098000300c42c41840000c00e1400c0d4a000d0007040c0152008400440c541450450f501e1540c0b0002443d442c184030700d40b00003400351341d250b40c8030b00e03401c503000701e600e16047c540400010700a0340000340c04036a031600d000c04607c40d400e21648410903407050700d0410740e03280c44016007030304c0907000010101c51504400b01e4002c001918080c44020304605204190703403031761403442c0c02c500391143c0b202c80300c2c00382400500c1016480d85c2203c0360758215801504d210b8001e0500e04082c00a1046a00080e4020b4403004d0b000041014480e0070621403018600801c2d003a8591075030880c05d85601056030000074030b00807500640c015007079104240c0002c0092a0030341004904640f03e055401c1280d00744c810b5120030508006041c0c05000b10700f4170340030740e10003041058000710000d0450003041c0619020040c40760240360307069008104507020903401c6412a42180700300c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 594543210 1250 594541960 594541967
    0x20d0207051608010b060403060905030c100c030b01020a0803011505040e071707080f0f090a0c09090320060f040314031510021609050709031203090605100815090304080d 75
    0x300401c0714242d4a4002600210620500750300c1c00c070050516240a10b1034a841000d000003081c2500d0a000802c041c4482d02008c0081c030520985c1c840d004141801048800740854035108100c5042d034010f20740300c00014404804403415185d800071404000000c5540c12100c5011700d422a1041100420a1092064000070204c0c40c03211403080601542c1d0311043c0860791814140d9040358000b0f80107000c90082c1c50422403040d4413100f0101281c006207141d03141d43c0750700c810b0340e400180040d13503911580b4103040c2d102100200032811403910454800030071040303640d1210020541c9201481030b1001c601014030460820443c3c411040400c0d07280d080000d800d07460780b80741c0403a440c070903f110711180900341c0c00461100c400000da41d03080427040d45414003220180200810101c10000c0d4960040005030b13040000740c10075002c50358006080c80191030903204417000901108041903044004000c005d0000840446000c012551640c50740c030f07480203092441c0519002a861801100b103d908078607031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 594544460 1250 594543210 594543223
    0xf030c0a3804121b0f110a27050c18010c0803010915140f091005090f0f07022a0a03050d020d020c040c0f05162003011a1c0501020d020705 61
    0x155203030520714034000c005980b00d000c0c041410304d10704204010031020601c0d8001c0c040115010700d548100c441ca03102c0014200d8903c1d07800845018413240c60100c489800d074202540c000d64070b00000c1041d410701015408450103031a6083c1108402c5000c021911b03446500007248542e400701c44542c03079584032450312000e0980068980b0080441c1540099000800c44401c1c071100750280481038545188000d000303107080003e01c942660b401141c00000c0984680d525207110b10307aa0702503000182006040c407046000d010f02840304544c1310640018410300c50400d0041d100030411500d10b411603107900450000341c46c0f41e102070400d000b05160840401e4001c03e00140458450303082d0341c0131542d41420071045410254403640021551928110000c2c050402040e100300c404410800190b510354070b50354030454580e900315088490000d0380c120b41c20240070303165810f9030b8204085015076282d00815184d404001280e0500100d1f81e00c1c1c4414007d080d811100d03003513003011040d0b603101c425080c03141d40e030300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 594545710 1250 594544460 594544463
    0xd06020418060521010b060d02070506100e0c16140d091d0c0a140403060b10030e06070503101e0e22030c0c05210f030c0a3804 56
    0x40d105071103029400303068030078042600c40080098903040c240f401070030070b00108001c4402c00b41d0341c4c9a83c00817440e40c1d00700203441405100300c00960f075200c04e4075220b81041c5025000f40102036914500b0302403215036401c41031b4801e501e411010307110401d40b14009a141c803600c4000e82510000522200400f00200301c0780307003a040316154145501d03544c40000100c40b9401480c0354400350080c1c04074005a40c0f106c01810b0400e000d2404c0c8180081071140054550310981c0b040390700c20754400c00721800342080b075526481502c65007010840002318500c4030f03445140c010301550801030000002050b0a0154517680050010001181c40e0304005801c400b103244101d000f00c0030a441d482001510201b1100c011503074601c0c0c00c0f04280040c5809035022b07102c0e0703540c3c121308480c0022503040114540e00c40010b01c05042068080300c06505600c80728150428840c1400400d01e604108080410305400180380400142d001c24800303545080b1044403442003505204d40f0121070305000c0e40703000c403071080c46400c2d0145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 594546960 1250 594545710 594545729
    0x5040c0e04031d0a291c020d0501091811061902031201081c0f0c0b0c0702130203100b0f07120c1104140408030a063b0f0c180d060204 59
    0x68407180c007000034606292007010b00301d01e031824020103004040b0001e02c40c0142d081174280d04084403400004140348480a00c1d500040e070106144c101d424940c02960700400c52143c4c20814020698124a002c2c4c080000207000104450000b03000c0f511260100c40c18076025000d0307105030f1010600002e40b6075004480142c80040e01100108001c000171451074060b0a00080c416890540766505640c008101480c220601c10201e19110109800e003c041e445040010081603656a044c030410201000300030345e1120944c4141300f081180c0141c0491041078a900104007511540d01d07080c0e107115481004c40041c0181c40b07d12207003207100d400039141c503030235489181c2d000c0d0b46851040034001100e806c00d514135060015000400c021500c0c030700c0190b0f00010815000b00c0d001e80c0301c40c1108070a4012190720100c0701046000c4410102c284611110ac0b02200740445486040284241250010140201d680711500140c0b5072404140e60103e92030340500a40200407640d00b500300341e0025002440303000340c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 594548210 1250 594546960 594547007
    0x3021f0305090705011709100204031212090803180123090d05031603091b060e121603030e030a120512090d1d0613030b0a06050307081005040c0e0403 66
    0x100b16000c154101541c81c1070396011240c0002c1200c0183d001c0303014100448601800142d81911801400204007650045054002078140c0c1d00e0000c01050b05071001460007441c2480480020b03202c0b0742241d1304400f48030301c5202c0c405c0c111030b1010300400d07c10b801c0c101145401542d068017107031103403043d901c1030004006489070010441c2007a40c031440200c884604550b007561800403c80c0c042e42c400c0741543c0c029100041e41c0c1c0d0061a01ca203040c54503420440110340c0400b184c3c1254030b0805000d107031442c44d003005013240e921101e44582020546000040610840300c92501036a01e04108074030744590085039540a18045040c003401a501005440d11083c803010700142140d1000108103885001565902c4138040000c964078003d01544a00683c0c000c00800c041981410614100b00195008040840c0c082c10042510001c403800c940c4040e0103a013184108101403400800d40c102002107540011405a88a20b81800301c40181d80001d030072404104180300a00d03911500320300f070075a1a03610405d032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 594549460 1250 594548210 594548221
    0x50c090105060a08010509040804031a061002030a0c200d0b16090e0612210405030c030a020a0603150f03061406030111041a0904050c0a08070507030503060d0c03021f0305 75
    0x92080f519000c003c103c50300300420072820700c911200d50050144065908283e00c03a564040300c042440783c0c00340310754218404e00601d8a40302080210160319800214502400650050004540d942c8050881107040c0204101c071200d04284000110004001402c02d40c858900900d1044066801d183c00c1740700034110201c400e00903000a01540c04240c6012010b9850600b00500300300d8060b01d010b828090030038803050550304942e4694030310000101d1a92140e06000074140f03841e103054640d901c00c0d80010120700260300c84149510070ba900343c1c83d0100f205540214100f00204081c1d00102c40e590541d4000420300800e0391050045510400b85050700340c6900c070400d400c0c1c1e005181006004402000200500319100780c08180113604010a14204088403000900300e60045401400c200400030310041815030161507140e11445509000303080c1125502c0082003400000c0004e40a00201c0a81a09100c20208008021a0700800312002d035061131980c196205100c418240c0401d09000c0443c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 594550710 1250 594549460 594549469
    0x2010c09030b360c030f030427020705030f25020a05040b01030e3f090f01110d03020d0e0f030306040c0c080f131509150219050c090105 60
    0x1000c4030b410521000c480d4955441c004070307503084102090390315441d044034088038080101d510b02c04102000080c01102c07200703005060030f00440710080403080e0030421050080070403654000542c7c04210b03d50390202881074408100034450030700e003e40984070104416820001c0743c030040c000c41e0a25401c451324a50440300c906080ca11222000303500c004400d20600460500313a00002c50310105140124141c0492541c03942415000414040ba0341066070598182400050103034039003d5018880340d00c99405d000b0b08855a002e0a46194404c4464041e0080a80e21408010b52212000f5045c0c501c000d040038130180003507008802e094012030800b8106544440040751541d07401c2219005145140d50b880100401400e880d03481030140728016900c4404140d00b400a0580d15800080c1a5920b5840d070702d0130000e03082a40c0c040c1035002d40e1201d00c210102c0d80402c0844c1203514429001d05020032250040c1c0c00c11030714000d400420310305001032800340700c00044c031042d01d4030b000d442d60209645c80c0c10602 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 594551960 1250 594550710 594550727
    0x270806190b15030a020d050103110102240105130207060c02060702100b060403110303070c031401050f040f0b071e0203090a080706200a0821010509090727020a02070602010c 76
    0x42d60101100e0392002d20721028a00841c2d009105030401450710546003540e0088580030303001030700c0402081e1101c6a6a580404c80034410f03011604886100203084a56951080014010280510040c45c100c82440215030140d401d0039502a80600c04200d10170002944e5940c107c5d40c0b08018401d045010301c0142c400e105052585002420310f503d4542940c6071040d000070140e26064151101700107003c085110407041002a6110f10702500359200c082c803801c0c1c01e444020744120188044d040903c0300080922881b00280c42e88184064141e03900e2020036200c1a2a007000766001e0300501c00c6500c00c4543c0840104812101100d44001c00380d2600103060380d0744040e000700700100e6180211078034405009641410300340d11080459900225982c0c070a40d460300704030303907642004904501d030309411903201c200a0b0140205540769005450251081903803150207105543c1200302d4890168501c1003441800300381950100425503030741042501c02595a01c480c400c400c01540b030720401411461161901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 594553210 1250 594551960 594551981
    0x3070807030e010e063117061816051002010b1e120c011407110d060b030f0f060c07031403070f0207091803050d1508030a030c0305040f0327080619 65
    0x1980186002110304030540c00e041c04070a801b4100700c07070000706154201e40213000c0d603440307001030440b904200200c105800c22007901d032001604030081c50003600411020140880304100c801c2c140c030006252082c1c2c01002e016003180e4021518149030110000e544e41100010300003558030207100004000116220000b6104040c0041e20050b45414080407200181c00711034011140103044041e00340000da0001e040600803140562034511401041c40c0c288031440c000842400600b9000399580c00da03580300c010042a400540300040344040606126840e071440360408440c0d8540d07281804800501903541160f8820010f10134900c0c080388122041c014400d8000c05202d00c132070512603a50b0151440c1d0000800200f40745d40e5640c0601c19400096a0030380280720741d070003550b070f03400e40c440c40101a070b1100013550041c14144800e00c400100c0141111008507010b107045a079800701c050081c4608210141c85491f4206010b1001c200003001040040c05260721441ca061801ca024030844265800c4502c2d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 594554460 1250 594553210 594553237
    0x30f07030b04140f010504020f09190213120f0506090d1718010f140108071809051f0204060f0f051902010e010c020601030c050405060d1403070807030e010e06 70
    0x4100042141564a400078811000f01030211604103039646040190882d0300700f243c1d101c400b400300b981014440b118501d4010f03105107500b89000a0b60b54050710300310320800100303035002801202040e00c6d00c1c040400b40c07003407081d001140e100d81d0802e80f09500250500769441e003e03140218402440008401c4030f100360f02d07200c4242a001c48407003e0303040540240100c481d05a81e02045405001c281f007454407001007410000342100e01d5003000044588141c1101c0001d5201e000188000e144c880203030f98044d5031410000c20a035881e07250480c00c052420301e003d80c25411120410f407103090250058402e40b0940c1e034500c51012201407048420400703031400750f004650200581910078800c0d4601190000070f0b03000108802c4452481d8030f084503180034913200180c10000c014130412444c01d807100b00070801150107000c41d00b80200020031030b40c1c107500000c0c407141d00c09040b082c0a030018804da51a01d6080111140c9070316850138050080c100c0c41c2c01144c00201c2e00c06070701c4810318210702a1810b1020a26 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 594555710 1250 594554460 594554473
    0xd030510080118080f090409051f0c050f09060f0a0c06150501170a0905060106020115050909070b07060b0a0e04060518061303090f06051201080706020303040209060d121d030f 77
    0x12604e20081d4000e2066160482d410070000001351030b02c1c020104624810401130810f064824500303505410354500110300700f428001c40864a035400020346241042c901c4855a6514107400003030b00920410034000d04440e008a031010155410170110340403c0c1c0508000c5c00303440e914803034503010040c080c0111804900c1000242c20000d4100b00f0841c0e2240c05240001a0f110041c1c03100791404400f40d221000603910384c0300008071007891820080007000141c4604041c0c1c24000c2210392202c4a80c014114029008280310092204503081455030040250001078040c2e1a103191001c8041d04440684038141844040340764000c90040e405000300c1c0c94800360986840c2e1a02c0311a080e03000310b909404104080002043d0b8001560002c6d000340895221241c0e034210490301c20100020503802060550401c040c20800260003008030b90780b00d13604841140a0b9031714680050410424103401034503032401000041c0c3c5450b04a010b248180504080c24086020004201a59182c4860003ca07103a040b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 594556960 1250 594555710 594555713
    0xa060912080304060e0703060b0f0f2812030323100504020901020309030102181503100b0d020d0c020106060212040815040f0f0506060a050607110f04020c0d030510080118 75
    0x1201842e0841d114007400304410841c240d505d80b03022000d8005851551b5100c19080c8140342c4040450704103202900d002e0380424520300040c40048885031844000c0100c0340180701300c1503001c400640505075600041c803405880b42401402044003004080d4007043c045a4941c45405411070584100e2080d1400c00210b81000c0910001e5008500028158031040c0200300e2a55400e00160400460b0941c01909030801c82e000c00107684040c105620703081d042002480040c0342030001c0070301643d003200000f0356038401800098009208400550300f2140c40c01e06036440a550641003103046a100da0b00301c454022481076030078850300c01d030310031007000d507004c02e420002d1034015114243c0e0060048080a481c06800d403a150b141c24a10101200c803500b10100304000d80c03038944446006068103841c2d0508104d425501c1156421844c0d024504c54140c6003902205652203804403444c0d0102e081c01d0f16071b0031615030009005058152040c40000030703c02008034503400148614034051041044520210525 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 594558210 1250 594556960 594556973
    0x50a0309080d1e0f030b040c0c060b01110a110a0e180706110d08040804030605010b03090f1b090907180212010b0a02070312030212010b0301060f0e0307140102101104050a060912 78
    0x40490109040c0c0b104400f070b091f5602e070700c181c1c41b01c0300080c1c4800060020516213941145c0c0c0c00000e41d8184110324a004220042c0040c41c101d4040d800282c03070b00c0e480700383e0000840c0440150311051050101d141004046081112100351106000e011104645c0e110340040e11850090303205003440780e005c414140e4a682c400c0c00303016085401160441d15050712501c440040e40c81c02d80141a400100105208103008100100c00c0c19005480c05004040d1000190318680700d80c002d8441d2058030074201007188020140004001481051441e4003440c01d0805076402070741042540c075200070441c80000400c150500c04542040c0d460ba03000e420841e0440d42d6201a03030010700e46c00c0d41059801e000c440b41c80390301141c000b07001e400c8a016441d01c943c90080010100210700c544002085400078150003581c03000100101524083c010b581070319800580101d150910b1510240d406074103000f001c840c15403542006006945007650f80c5083c0d2922820b09031001c400074444c0700c20192000080b08040b810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 594559460 1250 594558210 594558227
    0x11061501031a030a03020706092327040320060c043f060506061c1e021201080d080403020c0d080d0504031d0a0605070b060102010603050a0309080d1e 66
    0x154001c161942d01e0b40200840e180c4a8103850032005a88000420300c0790b180c001c8000300080c40c50030b1040e008590844540341121144030091805142091403850050041e191000305507428140418a1803a06040040c480494040ca0b001c619203d41c02241e1403050110f5850320900a003242145031900c1c261f40004152400d89001952549100c580c3c07055041d0302d9501c1407804038290258241206074240306045410203405c030780c4548410003c9154000d551008040000d401e1100090140c451035501100c10801e4540d02c84020710004007a01001c680c50b0456040c0c82c00042116240920024181c4c1c1d085010b0f9400340159001340010551032500b0010b1414440c4140c1c004c5042002d141182c0c41039070001c4d40c08401240101c0d02061070840e920311002d0045104603141d0608e50316022002e821440303130980242c203007018400080c030241d0007500b0450046034420115400b08615060040800c20f05004000c41801190440451140320b47c1c0488520342c0103200310001c1d901c2c22070040c0c1c0c0269 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 594560710 1250 594559460 594559481
    0x1d0613020f060304060212010906180b03030d021c0506030c010c110117072316020d0c030804230109050f0906010207080d020c01140a0c02091509070f1106150103 71
    0x200c540e2416085448482c050750199129070030143c4c40b110b00c140448005241604a00e40b01403400b5020800e0240000c48031054003100d11000404d0b09103000400d04501c039900080c1205400091b421140f45000b258940220344d8030342e810001903c07440201900c0b104482c0c1c142e030001d4448000000465030076500790b10741c010141420300340c0c00228880c1040425048402d4000708504110510a52400c0e0f0740e00e8604452392001d041c6030041c070b0100440c01c0c0c40100310190040b40001e640c4030070404651003150186800001c03482d261680c5100444180281c2d90740307440740c840c0d00e2201d9010780d401010480300b643c4004004600301f8400000380030381000e00a001f40d045201d070490008503c581440181c480020940c050301e106c050440014000d400f0f08003410070514030800c121174000d03030703c10f11100e00c40d68100c418401544427080b650211210211155a07c00d29003010b20460075000795483c6040c80183d142d13170341c100000d80102a19103038100d80314403034421a4032441000d50312a500c10004407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 594561960 1250 594560710 594560719
    0x501080c1308101d06010302012a0c0e070f050f030105040c0e090f01080c06070c05090c04030c0e0601120c02060f07090f08240114060d06150c061d061302 68
    0x2e980301c4280e40b800c1c8502c1c001d0440d0750340d03451444038030099104403080055082c80042c05507501d550700007003800d1440304503000001d000c4c44110085071041c8078154010b940102004201c580c40d00c2100b4000070041ea00700380482c039501469280c96000da030944205e0156191580d09507841c10f401d02000d002102600c00c00c00040c076405c07070466520781c0303501801107403604074415666041c85409490601c520308840d11420b424030050300001e006910800944200703864070085034817419440a520700075074000034141c066840c804505c83c08400500c51007508266103901c081c044010a900c06c0f03800e203400d01c0006820850001e00110024110076800c50140c0c81c054640702d6a031344c0001d1000107a0f400c4180e10340c0241003011341c8002c0490b294000140340d190b5040c482d524103a003618034803e101c50300070301850b40880c0105030071a40707501150040107030b040615848054003030014002a401c0c41c0448815161201e402c1c0c80306041c0c6c89007540440c00c20300805039516030500f06000c0007400401280d01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 594563210 1250 594561960 594561997
    0xa0209061204061802060405040e0a050a030201050603060c0c10110c10020414041b08091006080309040c05040f0302061b0d1701060c1101050a1106070e0405060a0501080c 75
    0x26444920041c084480c101d08805580e05241ca801e01c1510107040303003d0401900c0201410144e40c41008550446004407400500103502d595041d04214000001910f0341c02010010350030316406402861040702d0842c01d8503541d60302c80805000500540807445a550700441407542c3c900c8043c4e00441c1c20368201050b079418000b00d00c0341585410700c4404045a02030300818208039101001000808418044400303000e0451240c0508580c1e6210300e84000c10001c40c0d0010076014003041c07100e04030106020400740a0343e41ca54148542e40e90101719800c0c041e514016441107921701c20307400d440c1580c1c80c40c203030188458510740070005180c204c0940c40d48880ca0420503d01504002c100005032620380c1d45076502c454100b904000511541684031105004910038804001208500500f051000900381503880d101c2d589400c81d030748014504000800d114003814040340c1c0b50003418100803550100c500b80202e075a818248000d0b402c2d14490340e03000c9403ca00102c1e8083c11030801a0416075115810180c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 594564460 1250 594563210 594563227
    0x12060f011d100b0d270501060e0c0304030f03020d0c0e01110703120e040e0a0f0c0b0c07060c06020702030703030e03210d0e03071b03150c020c1306080a1a010f060f03050a02 76
    0x1c3d01e010781e00201c4003117100c4400501000800c1c007443c00186140c0307846240926200310310080f5844000c0c00202000340c07000015007000d0003903043d100d80720200241080103001c3c0b0748002d0000085018040e0100d60002c400092030880011228162a4401e10300715440c0461a000e8501c134403900661a80b144d1664402021a4030030041142c60318080d14540c030f01560142080c800c6019a900302c442500010829002804000201a01241c100e4507006003801007900b0414028002c10200130750500801071b0000c1803562004a04202c0304040b02074410b00c0055045100051001c051010640c41d002d000d14012090164081494102040140e0b0700d003807011760702c04480368401e0030010b9007051142014800d00c100b0001c0e9026070703200003408207c2030007005d030043e64030440031064910595890300300c000a141a5044403009201d0a03003103e4107482c1d6442c01c914400c64070b007402c9000700c0c101000083c03600004014801103c0086c2c44001e03555900314021000303044001c010300d0401e40c00300440c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 594565710 1250 594564460 594564491
    0xf030b06160506060427080307090810050a050a0207031d03011407050d0b09010308090f060d0603050f0c030105061003020d150b070209060103022712060f011d100b0d 73
    0x790300a204101400c440c0c58010304000403150740d4120b0540e0007107030300d0246007112200080c2c004442e412849446e281e80d5580d03030883e055542c5802c11500741c0104031071000c0e52851500540e001d402c24410038001c503520700000030100d0040c0318010380050807003441100409000c0c10800d081100180010074050910f03288200d81007401d031954800110001680c00c6545164815086d20310400c4603000d4035549103031140b900d107000352260548214403d816074150b80d83d4540c200c0302e0680158001303104a07a52410702c10f0725400c040c0d480b2882402603e01d00c80d401e19040c4034143c49010002c0c6124911036a24400300d0094121021030300c2034a40d14504100e4004543d40504024180400c9696980d8001d00c148402c403440a0b1659040c0f60060003503002d46004038280040318019012900740c400520b00c002003140100766074600090091209000c101801c1c9240c1c1810ba41e01042d0601c0c59121624080400203801c9505138445010041c0600c41c0406041c0181b911150b05035011604c50700d4611082c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 594566960 1250 594565710 594565747
    0x1a060315090403081e150405061305070c21050a14090a1518081c050d0c080f090303091002090d0b180f1204031e0b090d17070f030b06 59
    0x343c0216010780c0c20400004480003290000215001502c600b80c20158100e012088900d14032500c038540b2200000c03c5a104e041001e1484080c0782030500060a2040c0003078206402101c041e108004c40010034940804210b540c0400812150348444c07034886520f100320b400c4d04800e1152070362001e003001503101981d00c03258000044c00d9081d08031070301a01d08400140c02c4c140c00c07055078003c0c0f210307801c41084420340c04190248491340c001800303030060301b502c3c0d0110380030310030340e01350a001510b420211800c0e1648012901d12a20450020a0154071390b542c41c0f41d5280812940345405034840ca443d20300101841e002741036541c401401c40e07885e0311941c1d42c0c0c0d00445001112010809240c0c40003090303100710200608003520040b200500303800c0c40042031880c020711640c0005480c01100d100300074214510b240500352801d4100300c41014600341110b0307154807405203000303030000141c0f0f00c4480c5000c5480019114090840d6803030311103510301403a4054ac007415007440d2690b48080140064400c150307200084c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 594568210 1250 594566960 594566963
    0x50a0c0b0103053306010f0924111507031d060a150501140714120a020a0c440f010603020907080402100e061c05040c0501031a0603150904 61
    0x1e40900415040814805411440c0c0800c900340522081c4008400c4d0a082c039411100070f2a010f81c010801410643e04c0440d240d002c5540b01c0148060709024020080d03130010504256520a94419a0180310560b9081c119403801c2070800100c0100b1140350081d405075508140d900448001a51002c003d607041c5942101c80c0b680e081c3e1a04519441c00c2c1c900c0810901410007428080041c4070501600209400344034001003500300b1843d010794900404000e56840182402c000d50b0382c03006e40306002511019081c070222042041c1c4640810817100680b9080c403d05490045040d45103050607885203808411003880103005942c1c61040c10400040c01400900075010001150f110b24501c180071045030020f089004004032a8203110059580400f2000d5070244c80c1303000603056401e400080d08034441c403078400540d098902003031000c14915802c014800c0d0b00030354064045a90300c200640076034034a1214090080e07042c030b040085502d85a000b40d6003203598042d0030041c10782d200d800301d00b900000b0741d070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 594569460 1250 594568210 594568213
    0xf361d0303040308060901080703110a080d020f0105010e06092701021b0712030212182101050f3120120a05061303020c03011d01180210050a0c0b010305 67
    0xc11007030640140b040744d0040004c0e505080a0340c945107069440c9e0403d4000180880e0f50000152100d071b441001c494083d00210080d54150b560500380a91340c0c406824980501d0b50811000080c0d6030301c288821403080101a0950a540d9030358011480d1f029141c0504103040c3c22100210170b0719180174405400c0e01d00c405040e40207800d031800001403410189911410640305e500d4058800a0b41c0482c044072481c2c22421040d84a08013409160090a10b500096070000109002d8440401d4980743c20541302031100001c02403030310341d4504169078690454551406903000b42c103210b0703450351a01000c2901100807000c48000e9107150741e030112441040c280d0801c51407901c00c00c1c00d49841e169103c50102885078008110040c481d42c0e075107480d030400a280394800c40c41c200041c000c1c94024445850510f500030001c0107000c0d00c1100f451007201300443c0a041c40c0d8a89284900045c2c0244580742000c0d40007461030400b0b680c036020480c0c0540c400a40d0341d0800c0a20301c2c0c04030001d141c000d0440e029511030030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 594570710 1250 594569460 594569467
    0xd0f02071215090c170d0305060108070207030b0c0d09050102040815011a09010507021306030320030d2703170606070803061e060c070f361d03 63
    0x100028903203000d5030000e40c9400020215280000d400a203400c07900b1400800c00f0684407010f04011041344599400ba0003520100402041c03000c4c1c0100780503401c61308a84080050b030700c400f001111000c00455803000941c1c0001418030100d06a10f0400d5400705c00e00e880c9902e4841c42d4600742007950031865040f1141d07900807409124031901800062549001d0a41100140d071410042e0300e414001501d4038109030f0000203207149aa4818021a548a60040c128031600c50700240040000e100074802500000c0d0024001400030001144030b41c110160f03030000b58107180c2001c00c07410060017400300240d403020b60414045003014146050009040c000d4884040a0a03104001d1401d83c2e4004c1c010792107003100b08615800283c1a0060fa60010300580e40044c401c007201019043c42241003450701e0340030f2400319680044030800100076090f20540c00300032025940c2c078245401440b0815071505030074a1901d0855048002041a9442c0104840000705401140003941000f03041d94020b44801c580001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 594571960 1250 594570710 594570737
    0x705030106420c020402040e010b030a050a1a190510051b0a0305120a0b040f0903110c031509030702040203070306150f080c0a090f0f0305060901021303020906060c0d 73
    0x4102541c0050602e0114a10700c407184000842c815081e9407100c0d0600c040458800203540b11541694080d2106840c0d0681d0b558469603142e0321500f0032200911803d04010001c0d4900e1014020b040c83c1062184100540c4801c200c1000074030340030304ca018242d0b01c0c00d00c480008c49a5500c440260305a844d51186c9540f4040c01400940000140b20542081d82c03101400400080d848001c0398407682100c0b04414603511a201d5031400b410003600040c0d445403c14482c50140c1406511004215102c0c2e1109545842502c4807580c640da141551b40764140c2040360b00c0268858070001c0b6030340c041000e01c10b4902c0c1000071780c00a0102d800c00d1701ca0304002550340e4406c0c04a0323000b000240c1c80d0f050303003801c124034840034150300140a8040200341000258000c540c06146038091404400900000c4164406d000d841d01c0240410003103a00c17040e2a64814070300030452011061084814122141d10502c003807504503000c0c400d0424020301450b030490f01c1007011480201017070050b02ca00040641d030f80c0441e56500d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 594573210 1250 594571960 594572009
    0x6050403110f01110d1e0606030209101b1101090810051b12070f020712060c08011205072303100518120306040b1503130303060905270705030106 64
    0x40641102e40743e850140c1010000815205a9041c9070148901140c41e0138802a100144540c8180c40b011072414800c2c0400e9464242c0c0240c069100309440d0180240c4803044200c174008220010280c070fa1144081c01d0740850f452610351110910181800c03003140781c3c0d0f10003040c0f411400c084513400e01980e440034000390020713902026885200c1001100c0c20301d0340d40c414140c001d00001c0c0c814814040c2e5007842894043c000d00c42600281000e8400d08170111440c1484000382c45c0b440781a01c00110000c00105825100756010000079420100501619060624000031f00e07910310407020046c0d4007240340031010360b030070040f00c40c4094981d1000314141c00d010078128850100108003070036030340003164060041e2007054141ca6022030119400308400c10000045200110090b01110240170300104002c00f001e1019055084644030f031790100b154a950f5203900040b90400d035081c0349200341d03611001080a81c446070020244115100340c8000b00d036a500080e003185d0180e4001681d412142c049950b04402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 594574460 1250 594573210 594573223
    0x40f03050105130803070e01030b0a0306050f09010c1d040f020d0903080c0c2109060a02030318030a0c03120605061b0c100e0910090c0903020f010e01021b0d0605040311 74
    0x4910000b4080d5409640307500131400014040c90404c80800e0707510465130301c2600320141440300544142c151a449041c4030018040448480e28682804000315000c6d00341442031000c01c841f9a50340c2038500d554580811105050310742403580c40754440004032141c4609100419046004000025140c440b900d006011203000414048840409006134a895200480c280da030100011017005c054940503a00c220090081581c02070700000080340b00141c10f50000300460050b803403082091500c400c00e0824507501d10440c51b9410015202504120000e8042c44500d1041400e48001103503c03529400402e074141c00110071003001d150b61070307200f40fa600c80602541c400c0c600290f03410056000121406000304800140340d50003410301c040002e040c0d440800914001e8081c402d011300603105c00840003070440d2290b000503480742c02d8003a920750f2151300610398101040d40c1030300070301f01600036281210300d00c500025200e034002103e44454400601c03e4400e191041e8070a03220750801c0404408510324061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 594575710 1250 594574460 594574471
    0xc0d020601030b0109021b37050a1e15020406030605010504120f030216080703140307030905040e0307050f060a150b0f1b011803020105070905090406020717040f03050105 75
    0x1045540140081500400799138152100c8050250b0b41da000081103030441d16100c00840c403580120080c0b02070207020304000e00b00d01c09041892601d103500c5100e494200c41c614902c0141a9400b80808000056a410340039403140da010000244004a5031100c404409080c100e924061758000b4007480700715007501c60701000d8074081c40e00604280c286401204100b40640700540b00401e0a01d00e081014070030888405100c0403640100c10640c1d03a82c0c80c8541c1c1d10702602048079200c0503190040c11441000040d58146501955405c0c034840c6440e080c00024280c080d11681c4a0004005100204400b0030002d0804040c15008100915010400600300d601450142e0341690980908001003140300e0b05070b030058002103110a6561101c049031003050b04601008808a500305a4285000d5004607202e00c2104d02940080c0031540e078a020440740640b0174002c4590200c900d501150110340d142c0e0250020a2080c903000c051444082e48100380b9400590045d044403070170000900400c0020300030036030406d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 594576960 1250 594575710 594575713
    0x20f010c0212060106022e020d090218040c05010509060307030b01091d090f070e0c09010912060f1b1b0204020403061d1506010c030c0510180308060307051f03200c0d02 74
    0x820a180c4252001341c12000015600e940110300c04841c442d1560100d201e18bd1300a0660343d0f103018540008200c0401200c09543c0c4110130f030000283c5500030000c47d03000980041c0f0f01484c40e075500009800500c1c560744114104580c00b00085041140b004122101c58990034020b0407616112215500e81448464039011907000700d181001a0000d07035600d59002003919a8190f00e07000190012262105194420b03000d40396154801400c1c8846540b003208018501d42d002c2c00324030002d2401d01c6019401140c001e00180200c805406003501c06602020107920081c400740c5090750303d454540a039854520585540c541b80c12106c4103441040062003c082d85e00c81c1c034110b451401c900042c049402041000c0c040c040b150000c901008428024200020109101044141c0d60b60042d00d041141c441c10403404603040201094072498000f44d10b800302c8000a1520700e0150300d554004e0784000d000704400042c10b0716290a0480200100c007030740030a881509855032550300f08134450f441c1271440c10201c01075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 594578210 1250 594576960 594577003
    0x131509050105061c032019060b010c020a0b07060902090718060c030e010c02030f06070e0a0e150f12060f0a0f0515041d07031a0c0c0604020f010c021206010602 70
    0x760340030340004031a110b806007445004100910100d0b5115100317201b503101240a45190313280540079407000e200c0e01c1c5010784000c120a41c84240191032011240c03900be940303c01c0018040000485103801407140b1803103008082100146a0b0214100260035141040802c10348942d9034003000d03091080400138001460150300710010380e10054410780b10020070074100310b414103441040d9102040b10a4072119008100c0b22285820780006140c4040600028441c03100310000242503030103020418024220842c01100644038041040405000420940d13003201a46c21301c030083c5d00003840f03581e21502000c1c12640b441d207481042241100c1e650004072050318684014808200035038840c0e4540c10100340c40000701807012209101c40c5211180e800c59940c40340d24070200401120103003d400080000d001d505560320307409861012400b552550401e958000710000d00940b40151403d4003a00c01170610f0849002107801081c040e00300050910840c0c0e02070307001040059030411600c80501c0055848121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 594579460 1250 594578210 594578239
    0x1401081c1407021516060c02070503030909060d06090b040f030e0604060e190b0f07060f0e0d03020711130212060a05010e04110412030903060b030105010e010e13150905010506 77
    0x150b004401e4082c0c003c0303c0303100b03408640c0c0c1100070841d0000031031034a060400e05454035140c0007401003000c03520018080c0d107200103900c2c1000005e4a00c10340c0000c00324000e50351103a0500140300641c0b1001d0b26529158071a12020956210603c0d02850085500604904040c100a0104140c0d4085035010700c4080004115150340484400c550239030880b08801e8881078140d1880b0b1400003504100180c4600061140307000d50f02c0f500a084440c0f04e010140801031143c03007443d0031075009c0180020990400001650014826402000002e110300303a402a0211442c0100e203e41e08081c03140100180e000550b500a010140e41e81b40c0c1c060003c686142d1390a0812000804000001840c14003c81d21040003001c01a102001d0382d001d0320146100c0f4050100e141001009000305202c140c5042e407401551440300d04041c09014140c030b0a880072544daa910b000d83e4910856001480001c049037612074003000500b0000d020130001c0d4094002080380402c03070414078212040500b40c141301e030039113030355009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 594580710 1250 594579460 594579497
    0x40815010b030c0318010606270305033a0203010303030e0a05070b092b21092102040f0204090f0b0f01110703050f0d030c020c0f12011401081c 63
    0x250311807408240f507a00e82d2515a80488402c4440d0400ea8155003804001f00d02580d00c5a02c1c0c00d200d0001400c020044030032101300701410a428000501281c008201a0324103c0074400f8052140340d40d580540c184a443d86045c0b0800c0d00501010070016070000f00400505a15015a0b02d009800c80081d242105059a5440d940c80781c0b40310720717001b0807400308400001e650b402001900b0007800450382d4070402c1c29100541c203410b0b41094211501d0400030040301d8003130904a490070501c1c6141d1035004a0a050412003402041850141c5440c81e032443c010740016250340c060094000c0001101503121400c1c02898000d030b460311010300061510340164265950b031214200d551000081c00c0140c2d07001010300c002410401d40d0380000c1d0992044481c1c043c100400005d81415202140c0da08114604060000700c5e103841d074480125a014600c0e01241005103040400541405038210001802035080e01480b1503d0b803090f48040000c0c0c200e4614484210703511110361103401010300e01749034196032001011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 594581960 1250 594580710 594580717
    0x60102011515090f08030a020609060106090e0a021b060402010e04020c0a110a0312050a201e071505040819020d06050606070f060506040e0303011d19060b040815010b 73
    0x603029000c210142c800e02d2402640140e02412000c44d00f42d00c050380700c4075419a603912000c0340c0c0c8014403845001030034106000c2640c505032406591034100080c46d000000b110071801400381d1340b84036401c204500d02c1030200e00b800000100602d01424041c545400054000303042444c006010300c3c010019011180c80100f80644c485074091100c1e449450071801154400056400c01080e8600200305040c3c900e070420082d1101d2091580d0318084903110301c90455140d42c1110400c240c9902048403070750359881d20b00708151035441100072290207558541c54140440703815144800401c000080a104401007842035104d44c08c200e9104480c00c0305d4907030118000765105038014100c3e507664804102266500e0b01104e00c0142c100101410007801c9050220042030b05407455881245030000c4070200000100540b4122401e03590324085182c01c00c80c030a070199a005203e0702032512945d640d44030700700d4188501e40180001d03040e0140c545003031410080c80c00c02d92000c8480300b21380c4500104503400349203048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 594583210 1250 594581960 594581969
    0x1060f020d1115130c080d120f0b0a14040f0b030303160504080102211501120209030c060c01050712050114060a020309090906100618050111030f0c060f0601020115 72
    0x1885030310303490000305040100c8004030000c103000c59400e1090000c03036055922000c1d8003c4004c005c031203030340381e62072a41d078003013000c03140045508a501c14940701d0302a070108611503e458030100b82602d0460019011a0458000c0d10004d40c4003030007541181802c1c41038107610800f0500c00c0000b0030b46240041d070f603800000c2481560307058105038507130705a204070300b6907009000341ca00954403803140c0f03841030320704080300035808401c021110000b404225090740301008402040c2c540801041c0c0000d8000040c1d88603080f03003a09486100c030304145c1034441800030009049a5400040c09013002c030f000905d50380410003d00200ea0400c401070001405549040c81c1c10078040b02c0c21691004d5581c81642903015070300510b41d004200d01d04020360b0000200c0c001e17108d078841713480112120303807100c4043d5000b41d80c903045505040384024042c020755014111000c0e00c000c120007120704041c19070030241d2040e801001d000102c0d0704404c0c10711584040c55068203812100c01d0000f80304030900300e4450051000e09116 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 594584460 1250 594583210 594583217
    0x15040f02010203190201021803060f0105010e060c1203070206090d174c0308040b0306010302121e010f18150504090602070b0c03010f1a0d020c010c0801060f020d 71
    0x240004680c0204102d405100c01030015804c6028901000fa00035001940e02051010003242000424500496060b210b00200380c0000003c2e42020011548154410b51003a0030100400003640061010040d1102c100004640140d581c540694000d06000c0d001e01341c244c813a400741e401d04224030303089240c0444100480d034014006658150200301c50241c000c1e48030498812184070340b1340740c4203000b8034800702040703144400380da10104006e20b1a40c501c15100140c80c0c46400e000c1802100902401903801210514000d4102031b19032110740c08070002074495812206401220115802800d02c0003401021428065841c1d9880c3c450030000315020081e000c040c031540e40040340020410125108080c1402030010052003c0d01d2800c00020f50290350259a411030800000b11150f80050480741a11202c02101d0011460800717010150905003080176a6041d091094086415451028105040b690400400d01d1841b900001d0050703001a0048420888000c407059092900013440c103460995528 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 594585710 1250 594584460 594584483
    0x6140a1203020a120c0c061d1306030228061707050703201e010b0102070e221a132a0503060f010f33050705010507050a111504 56
    0x2400b2030910030f41040051207001e810840000a41e40131003e00c40451103071100760541341d04c400c2d05403039620030a4210034055a00020030700306810400c0d01c59130002d10004001c170f130044d200e40c00200c1c0c1c221000481181c0d2a4500035500078090b001c007400008040c0e03410905000c41d21007036040c00701d01c0000c0203441884800988103040600c20800c0e921101c03010240d0848001003c18640d840703901400c00c4000d40d0515803030340941c2c5007041c400c0004940058004100c50740c90103941c8103010318001d00e02a01c0d88404214031104a00f040c0010040f00e1103080701a0382e4140050000742501009020000800e19191108001822078412604400030030701038680c6640400900d150b07010840c7d045641c150141c1028401c5040740d90f90503e060780d0200b619154903507107903181f400042c0c1c5008080070844416031086000640e010100030710101c4c881c40e12510b00a12501e4803825110240e443c2000070b075000901044059002280d501c482d0080f1002c0c1810b8504101c000310001d401900c00b038071043c0d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 594586960 1250 594585710 594585713
    0x1008070912050309030633030a030809120d02090a0603181106040321020f0a0c0b160203010e070302190b0f0d0b1f0f0512070c030203040b0d090606140a12 68
    0x7042030700c400100050850fa007c3c50095852042c0f80d0201c54200b03e4403800d134410050005c4211607101760458003030000c11200c2c3da00d0314210782c51704001d0450400b90154130031068000c1c410310000c18907007104807809680da4604400380040c040041e8410f2040600e0050740c50b0b80f1003104051145003e4100e660b9503422441640002c00f0b901c141e9000138910711340b0050b8000c10031902c2d60000040c5d40c003602920044001c6003001519084085001400504001c070184030b030011100140c40e2100502200032184103003580031900f11151364013406c0055220400c100110b00e068103144445180e102d41644a00d460061000d02c94002e01c240d4a14084000c11005500540ca42c880d00807000700034042c40f202d1484c80300c1e00441242d468584800550741462500100c0d000380202e448000e02000210255075801ba012104100c01c0801242180070801001400e200140081d00101e4040ca60024030b00005142074011191150f005828030581901401c27025540c0e1a04402110f12291500306043e005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 594588210 1250 594586960 594586963
    0xb0a0206070c02041e090b09070b0f2a01020712091401050c16121101050910083607140a0506030a0609060603020c06060109030c050f180c09100807091205 68
    0x5d900e00c4000460791003071746052105490704640605401032024201c951222254551140258020041c0c0310801304803a40e070448020000b03002007034140e999080020702000e00c9130205510b0462400f41a1f40119401090000d010040c004251140c00c04862092502c120050064000c80700681405804207000c2007070013041c081c2ca4034540440340701c84105501c41c7c0000e43c000c1742e10304c029164038180c080030300311030750060040303c910b04801002142c002820300c004407403031007000b810f6140d21142c043c54428100c13640e0070210f10300003c40b590400c1c0a21401c022601d00a1030750704c91687d007241e0036500d80b00381d20380c80922401d40320241d580603a02d5450703007040c0c4090420395110b040024a4500009189a4507034003500e100c1c2481c0c0283c0704141c403150011550910280000b410f6800c280c04100014603020307a09071541d0001811843c23804510203044050514200c40800140d807000038026a40d141040320f100c0f010701c207428452914101007400030b1040042d4000d40001143c60320b01031050140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 594589460 1250 594588210 594588221
    0x3210206062d040c0c03080c0f1608070506070f021203060a0e061903030f0f0828090203030d141602070e221505060402040b0904020f0c07030803040209010b0a0206070c0204 76
    0x2002e0010310442c013010740010004034080005a00082c02c0d8408684aa02400c048809002c01d511545003426a041c041480e003c1c2c60380300407640d49504010342c400107642800b8180c451075280d2a0b4246503940307104041e0405042000100001008000700700c01984ca02001100382d81600681500e655100e40101d600100409145600d04c044044000205603102e4104c44600c02d8a070303603400c800c00b25002c1c1521152000c2e19880b2103242d0340030621805200c1e06034500002c6030b9201005c502841203402090071680034041006c41d07151035203aa01c11211f180c0c0340560f0032107a444070942805518101c003d441e080d0902030f40008020303035004550403070b0313000204d0741069032869011103070091107140a80c40c0020009440d0340c418144000140580303082e1003554121009010064540120b0030100710003503002c034640c008046803c3c40030540c01c0c841008008040d43c46030b200300359241030900411840358016400804150300401c895000540d01140b00368200c000d50403c1d03603030b030300c0d451000070003422 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 594590710 1250 594589460 594589549
    0xa0609050a0b0a021314011e02030d1409010e060702060721021b010b03010605010e150c010905060103060e070501091511160303030b0609010c0206031801060321020606 74
    0xb1802c02c240400079006078020000389540c400311000c03295544542c2c50000d80b82c2107160340070550f280c0086108403a01a407580e1040518419286410503800407201101c51105204c241c0c2c44195080150a01b0248110b441c3c501d6620018180751428800c025030340c0400800b00ba04100da4540c042450046200b801035402c02c2d00581036440e1a100f00415090008040c2070356a15802d04d00ca01180741810300c682d0060310300607500c00307007440072a81c01c3c002c40d42610702c030801040100300003040c07481400788110f10754184104041c141e103500d542130813030681d00d003180501840d13009030508104581c0c006000108031384001032010a4911445800c2d80c4411415038440c81030700070000a0317814a500b10700940b060301d109407420440101440107000c3c00d8001c400d1068041070384140c4180c05072407c44003441c3c2c8800c2c42c41c2001075640101d00701e00d0030f44501c0da000300c2d00200d44509000260750f911b0b88000140b8110702c010200780c5402e8000400d90071207400719415200e01a84c50303a40940062000c40c6a05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 594591960 1250 594590710 594590723
    0x901060f0302061e070f1b0305121c09030201050f0f0f0103150f0903021e03030c0301050603040f2112020a0815030312161e050706020a051611030c030a050a0609050a 73
    0x10070b0179050000e0360b640d005600f2100034101c03045e0014a680501800c0094941050040c0f017401002c60355551194408900d40713820ba082058801000a1140903501c0894401c0d400071550781001041e464000f403000d05444031111550080003000500307441c1e00c904480c0c0200d0744000901c01c100100300248503094010f4452030401c400603080c181c001980000d5901800820614402c0a010302512400282c848030303c034900030001009540307044806107422501686419036109807554810004090541d0b00e164808101c0c0c000c00112038200c40051011403404401307510301f6000a1004015100040003107114080c09411142c0c0d0b80c03020800d0351242050080d10140c070303040046141c000c50341c80e0810078000900c1440110a136421266240081440507180c0c9400d00005a5a00020703401c810400c604200043c4410361441079071080060f146400b40c5494003681d00300300141410501201c0d0464000d82c04807100f1f00c006a0001001d41103c1d0b08940700090494541c07800780e091000b94071010307140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 594593210 1250 594591960 594591967
    0x70312090b090604170a0806040b0a08030409050a0513050a030804110d060603060f02040305120304320f0708030a0e060f04060807020c0f280e100503060901060f0302061e 75
    0x84102c0020120300840c0a0790311003104000410042035a07114903504600010001c4010841a00701074011001c444401010244800d85030031500381f075034001e68041c0c04c06a850f80248542a0850b220b400d80041075400107100d50300c0d103921001d503030b02c5044100904000c0001c0c002800d00c114554a01e00304031009014400304407460900c00050642404240c0340340e8640f1842440f040154801c80d81241d5115000c1c2c8a204007640c03200009402c018800d03101c0b10003420144540c220764080c40340542d090b8201c2c240114a1782403005240a121408440f160380c00301c0c030f090081e0380001055030104015864441400e4040c400803407000d0155a1509003002d4002c10080b5600341c0001aa91141c2410b500320345410160408205052411612598004984059420000c05020310301e000078205604854070b00d0b55256100315040c14115021001589010400d120910702800080c0e00100c880000f0b1151605082000441d01003603c0028801d020005040c8000c1e4144030442c0c1c00c0b0b010041c5d0b880c1e00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 594594460 1250 594593210 594593221
    0x24121b020304060e040516200316110406031104021305040f050f1b120402011b21090509011e081219051c02130e130308010506070503070312090b 64
    0x10749030014011400460404004c401c1c080c1418800d41c1d124003c070300303010031078440c0407041a240040a01045504144001e130603c0400008100909843c1030340782d0100ca0a0801e802c006111422003889948601d081080c00c00200b18400005644080101e80040c1e41d090101904840800d243c0d018a4100303081004941403410780754859807084041200000c40355032080300300b0445240f104c2c0f0b01109a40188880b034001d403101c00407a0b501910604007032000624a0311030b6103204c103c460b0308646108070003e41c42c0515100300642c86181c60942800e040395814000003a4945005005081c12240450b22442c4c0c01100c0900b014001c100b14420f698402c00d00a0101040da80102040d45a4003030030703908961a04d20800403030b0150241d5907070a8800412002401c00a0740c80103c4075503414070100c00120b500310519941e5400f0b031840764801e14030040b01c0e14000d040448142c0c8180c2c1b0802c41400b070b4030301040000c4100d131055945840c0c503410300c58640e8a04801007113082e4016010f4500c0e00d08000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 594595710 1250 594594460 594594463
    0x15030c0d110103050601020a12050304022205150f09060607020d0b070201020408070e040b06010804050c060c030d0c0305090d03050c040f06030c0216050f04110706050c0a080124121b02 81
    0x800c0c41c90030b80c0c00340603e5441400582c1c0c0c458842c0301c01400c024110b401d0792a010700c10750196030014801011070314400c62600c50024589007000c007002240b2790b103c0c00d004421780b03840d256481c0b0920035124403207a440b0344400110a048010304550003440000b54100031584c480d09120002907001c0f0f100221410b0442000b4000d41207402820861b01c01c5180108008421020040c403c590050080c80e950b034660004680700c0034054000c0703c0500c14600886200d6a40c82c0142c21089803200042d038035101c01354130160641d07852482070302c02d0500c0c1205004004102107043c9921311401e0030f000c03480c0d488615140703c1301d2040f540102c615280400000c41d01a0b45500200650381655003114040200c500f40400382000030300c00c00d0742c4400300240050240c2019040203240ca2003050300c181c00c01c20305440d48000c1e180100e402500b1040000350351620146c001c000e01c0d0141c40150354160064903011401d0180c0c1501100c607405100305106813081d03100c46ca40244403030302542801c46619901e40f0b00040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 594596960 1250 594595710 594595733
    0x3080a090f270e15010e0604050411041a090c130e040f0f0807120807030e070605040612020c010507170a02160b2701151403030f030402010203041d04020f0f010815030c0d 75
    0x941b078480000003082161415008490080350011100041420504100300080400414408441203d40c604011340e0340c030080316034450340c00e0000190b500e4140c84840803882142c5d401030071602074a101030001141c28a000d141e4607a81c400b940070303181d0304c250078a02228003403001d00506040d20140e00313106081d0b20445c0ca43c040c0381552001d10020944480103501d0789403902645000a4040c401045514801c0015080c0080c0010006140400c40f0244c5400d640782110701d01d01040d03200c5844007502c0ea050052950001700b5103070450904550444410000c4516440039000e12036a0002c1008607110070703051f160400a0250482c4054655000710f0301902da03040c0e0742c18440b81c5200001845c4140040c4517140107600402841c5094a03200d9150b80c580c00252050381148001e11001ca941d890700e20b1038001c0328203000040c1031035242c18410091400d4406070081e004481d903041c03025407030f42c11185143d000711302003011007422807802c008640313071900b03102e4015030040302c00c2504000c2c00302c0701014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 594598210 1250 594596960 594596969
    0xa1205070509060d02010e060a1205101409010312030b060c0307060f0c090501050415050f03041506092d18060902030c0f060d0203071803080a090f270e1501 69
    0xc8002d6596842d0421041c12200781020740818040317141d4143c203203000f0b001081c00d8011800c10b46201160b0080c41821954122280ca46e5108000310500141928011410003120211a01102c0d581199104200e035020080350303205042e104d9543e00b01035030320380c0c0658070001d40e00012a6212109820000044c0111240d040c00c00b80c9054002c0d0ba48522a41150065440c181c4446181901c0e0403900d566017a040015a07013048000c0c01844e281507010b00045020b2809030041500002d6031110342c0c1d04403002c80c1d0100441e80d02d403004800c0c100b00d42d00880155080840070f1540307110589640f803400b600c0803100003a40011110800d40c00c114030ba5000000c01ea000754101c51507050041c09100300204c40c55401e5074085010302c20030040400c103070000d6610800900c0c00300b61003010030304c4560303000d42c1d00c0c0c10850303c2190100c3c03022010f544c0402a24004d0505040403094280350802a05441030f40550103203030990180c10b10280c501e615081007c3c0042d0760000c5650344451601602003081081c0034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 594599460 1250 594598210 594598219
    0x209150f12030906030915010f08070609150c051005100e06030316080d0b06040b0d050a0b060a0507111c120201050c030f15040f020406030e01091707020a12050705 72
    0x404030540c200401c54801420003a801107107000400000c1086a0708000c10700c0c1d02510070300070392038008900309000600030078881c107403695801d09185445041c8034080c1c0102040000c881c01c104550b001280c0410003882da035090011100301d55003400c0c1d003000350710010060003e04082c24414580164005079048902c07640c40241181c0315502015141d208a0300b8403c1c6c00209140c019002c5021900180401029803000058005103040440c9041d00181d000350240c00c4007088690001101c1c0c01010341c0507050790400c001805441c00042d07100d010f2202c1510401001042480801080d48002110000000d09030800300d0b07443c0040640c0806024812140c07400f0070a07103601524014050750340685c1800f02c0c01415961a4407508620b81801000307603801d60b05094000602e503d552285424044801c40d0142c2d60301e00b449400740c1654180014402140c0c0341803040c0700416500132440c0c1c20540c9000c1e416940303500b2800011010056600032100e0440d20724440030030170900007003010840780d0668 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 594600710 1250 594599460 594599479
    0xc030a0b0607080d020f0c010c08060108060d0b07210504050c120610050f0406051206040b09030909191e0507021605130504031812020a0b03220f020915 67
    0x1001d00c203003806010001030444806100e02c0d00d00600580243c402c05250042c880e06041616042e103003074500410704000800c40007420b0110550740040308550114050700d40d00c2d0385d40003035920508941e10051981d002c0126104000c0603000500e003002c121480c54140034412420181051500c80c400c116000344204d540103165003105030701146040c882e51990280300052480c040038010205400e80301290710079a076040100380c43c3d81e40802c81c5a0240041c00070090b501c0d00340350000c0c0c2c110020340000c1ca84c3d0300612402c500c903610064420762000642903c4030b1914081c50b1180094101d604907050f003814080299a035400c42c0e94041071248589608464240d5450451a0795829042c01240d401134981c402540c01c00005401154001d4840d190080d000c42e000c0d100728106505a803c40080000f14040700415464a19080e4000e090100d14a61441c2030a04202c24100b038907840f002020b162014000381030003803103080c0c00041d640140144805207030030481c400001544407030036442580d422 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 594601960 1250 594600710 594600731
    0x130e06040e0c09010b0c0c180a0506120c060d0e030301080a031e0e040c0905061b011a0d0f1a0f0601030f0e03090607060905010e031c410c030a 63
    0x10700400e9044060543d0b5210b90901c0101c442990110900003101d20540d5413124041d111703082c540c0100d8080ba22900241d0a01d44404000e8610142c0280c0c81008d050382c0c402001240440c9086c0c01900844020703036600d006042020141000500d41ca40c00d00000c00000b0b000fa42c04036040040c144070340d80b0030101525040c00342c0e5255000401c2c100000394102d4008801e07080550205050148509000e00c503a0b645000203a61640915020218070401249062205000b4011482c05030040141780c01e6034003541000c1490260000d401502c0c90b01d0341070916041c42002036a0006808400c00480310520700b4074541202850182da03400d0020b4a088120f006290712442941c80c40e01140025600d4003100c20100016074000002c1074501d41e40d41c0c0040070004101b4032032484441c80c510040c580325081c103900041003581403901010310f40d003841c401141081c1d01582c00c901c148100100070000e4880000c21201c1d5805480c900324407200000309110711014144080d42c455424050180003c0011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 594603210 1250 594601960 594601963
    0xa08060c1b150a05090313140109050904020619050c0a12140304020a15020f1009030807090e220227100b09120f03120a0b0405010b0a080606130e06040e 67
    0x18082c150810101c0b9402064030140c42c0d8101ea5000000c1c07070b08690824100300700c03e605551081c0d1280c640804031900c5d1241550704450100003c2108a5105401e0314140d00030510900c40d9102c0000301000d00c0d071107010240e00582c00d03100f0501440341200e07506c001c1854200740108080940d00c0200300c1c0d0101c07084107032501c481141d108a60280c0368680d154075103c120081c490554400209600404003c1d4041c900104090030625001d030001140301e5141d402c000c0e103462009804135040104080d014007004076001041c580002c1c0c180320184403820126017840280c00394420095201c40c40d11040f004400c40c6010b50704401004010300601d5403074443c0800845461482000d400c00302c180144056403400c274000440e942d0070351054410840101100c0e42c1598001c00191a1400380c0c5014810340c68031502c103000c606030055a08001c40d5042c01c211704a607002c1e10180000b0400c5400000d9426225602078440942e01c410880f01c40c9911140000390059044038200e0240d0300d44410b104a4000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 594604316 1106 594603210 594603223
    0x506310b030f160b0a232512030203090a020d05070305030427020f04050d151803030f0203041e050f0610031b0e010501030b0a08060c1b 60
    0x202c0700360944009120b80c00641c490003043c0140094540c02109055101a00c010484071400000544202901c60741f40d180402d0216001c0b045182078540224414961180003d8500350006440440490108030340e840340b182d108030403c4015040000c030005503a401401034829161720382d100c07545540c1c8140c2c0224860698800d070b00403a40108070f0f4042c10440c41070030543c5010402d2358203d400c0c1c056406058464440c800d40f0804000ca801c0820310041d01c405001c1c00510184078083c85226921441640070034200000001d00802c0d81c42144d1040e913001046024142500003403811621b480201214584604c80e10f0420228003002068422182410444800d03800c0d440e01d0369031044940e440d00d00521600d41c046c880b5100603d0f07a141503070130a01c2c00041c1285260000f958010059000303c40e40e000341300c00d2050b50a010001048131400c0c80307251b205002200c0c010a907aa00 = true := by decide +kernel

theorem cover : BRFrame.Cov 594424460 594604316 := by
  have h0 := BRFrame.cov_init 594424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 594424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 594424460 ≤ n) (h2 : n < 594604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
