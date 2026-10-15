-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:54:25.510559+00:00
-- url     : https://prove2.me/submissions/e409555e-d665-4914-918c-61e769b2274f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980035971 ≤ n < 980215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980037221 1250 980035971 980036011
    0xe0a080403081c020a050d09080c01180b0702070602030717130b07020a0906080d0e0441010506090d030c080c070302030c1c020909030706050f06030f010e0304051e0612 74
    0x4220300c120140000006c2c01481030515240c0c0c0c0c0e4021411060041c0d400504112000001c2404c4a0301c1e0311100242111500b81401040120070700c05030302200f28005000000e1030404040d48070b01c10141d00a0218540d840c040e05802d280c1d4064a51041c24500b203401c003161109110503065011341d49c181c2c0f040422382c40000301c0c40c00c680030340001e03664214050300c00505106000d0f01daa07489119103580c0181c4404020104120030300102241d42c0c10801e0700b106000c5030301d041c044004007040c1d0038461a07004e080103100540b59281202c0308003034140d88560804011f4281183c0e800010b1800401e000e000082c3d81e0b41c80b04002520b5020707203000300e041d2490710041c0c40400030100700d45510000400b0318181c545015140011314290311103d01001d5030703d803402550f100c1c1d0840c3c2003140d0b84003100a2160601a1900302040070511540e03a00008210251030b1002041e940d00462085a00c140b862004107006190003440d914001d0360013910701500c41c803004205810780541221010304904000c80444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980038471 1250 980037221 980037277
    0x1103090f0c03030a0e040219020d08011a040605030411030610060311180f1201090c1a0c073501020702030c090411060904020715060f081f0e0a08040308 67
    0x4031814002e00541c0b50801003081990555070a8201942c010703130074012070b102c4e01d0182c912250780c103c0c56030280121141004000e8044881030f001030b00b1141c409a100400313095440225030580310306081103a142c4e134491400814040485c8803880d052b000c1e230418040e048040340070400a641490700d042c0481900c000032500c041c02010030303859030780c665000000c2050502112400000402030b080140c102000c50010342526003128044400323065440f400c102d180c400c1980c0e038070f5004100c1040b52a00d600c20704450390b00c8801c2d000355001311612103001440003441090304c010b1172805021405c020310000300d0490003034001403400c5e40240941d42d0310115074501003150714407c5034085895090400074409100164101035481500031340d0070804080862441d0821031300303202d01c0c520041150f506000c00e40d5407200300b0b60301c21f4606500603d031a501381d03449800000071081590800003140200990704914190703080b0380141c0000c0f00010701005007e0740e070008241d010207510441e01c607000343c40012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980039721 1250 980038471 980038483
    0xb06041b12061d1602012022080303060f120a1b050105040302010909020d092003100c051209070b040e070306060c020d0204020a030f0f020406021b01091203020304091103090f 77
    0x3840b001c00d200002075400c114840032913180d41010710001852140091980740c0c1e0400c0c1c02e07000c00361945c01203106d110740b00aa8140d500c5181c8191800302e2800d240800641d0b480c0130207003015100341101d01240b40151900d0b001a00b4418008045540c494950305283d50340441d11000840881c00e8800d01040c19400b650455044076810380d90584100c0c07030002d58100075004100703d20102504c03a003080c008683e03a180350700f40c0c696420300e00d070901140080c02c15241c84e812a079a500c80b6070625081c00080b6070040162074410302084401c0c01c4c140d0352810705a0600b10f032600009811000828081500d10031200030750310580c002e4904200c00c03034441a0640302a106031070003e600180c0381c40d21200505080c0c020300300600c030b2800d000c5120f00e900100c1000b170f01c44400c503002045a000c84c08000300c0d5410402c4140044100443c811074104200008010100b64092040454003c10401080510800c1240c0081240e42d20400212750605c0030b800d0141d0054482540c548903803124160790b00c0000c41c0ba = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980040971 1250 980039721 980039759
    0x90602161a060d080d0b0d11090f0129040e0702010203070815030a06020f09040608010506040605010306030809090c070f23010507121e06030606030215030705070b06041b1206 77
    0x8082c0110f1643d44600c158001450070b02c255848440d200080d8955076100d500c4144071381d0000d401c00721068140208540005d02c1ca40c00b07000b070f40c0010449150382d06142d03442d40c0c610310b59403003c0b80d58007028481d8a11071070b844100100d90036803c11030310a41c19400ba600415403995203240c280c5604074035180c1910000303031b1700342c5c5034011080c0c0b04005803044d030003060070194a043c00e134106008039000034100e9610794030900fa107035180c8081020324905403244202a0800b424104003031415600d455465000d01c1c0c6d100f0380501c043c03001017408800c1400c1510481e07913010092200da800e55140022000c0b245011005016000c0c8018401014040c080d15100d80216590020150750156450024101c030601c07129900c1c48111a103ea400006d000d01c8001d14020500030170700c60324600c140009440380d210103280c006000e2040c403030010380c4413007201c404e103400c0200220f5588616001500810080c2c0e03100c8408035800310110102500008040f08000412004011aa40e2020a41c010b0400082 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980042221 1250 980040971 980040979
    0x60507020604031706010e0d0f0521070b06151308120a0f0e0a1814010602031207080403092c0a0c02150a0e060907140109151101090602161a06 63
    0x3c03490124110130324042e50302000c1403505070000120440070541c08070700c00e82c0a4420102c007a000b20b040c0141009507002d1601c0c4191102d44410625a0f440100d0140c4903004203480c070381e00301140d203955038010800012000d400c40300b0741d00c000f90030101040d500a4499404240110415040382d045045c1c02e88440d01103c3c0c641d00e000c074140f007034100c0c0d480844c09a9140d000a6003140840c00f00c03007680202c603940c12810700c00100e8124800d01c4180d84c0780c1c160f014208551041184030305242d0085c99058000900c0d00f4488400c8c1c5070781c94191400c4200d0340003110350b4071b164100141502043e02c440d240b264805001203540d0b0f1103825500c41035a00c1034403400c0240e0f2250030f040c01e51121600c0040e510800032035000031054161614203040c100e0984807161071303074404102404503070002e00000c40080d400342808000f69103459400c0c8040f2038a01c20140c140a0402c0d0a0544d0300020b4002401c0c40360300c400308560b03c56805203000c5264242c698141c56281003401d00940c041c600040751070140300010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980043471 1250 980042221 980042237
    0xc0804060b12030c0c1804030f1b0602070803071709070b0a0c05100507200606040c0e090403092309041b0306050c091201150312050c120706050702060403 68
    0x244405014000700d00d0029003202c08540541900c1605002030320020041c4005070402d10302c40c10030490300c885400c0c02500c0800819081c040020340040c2080c0e811700701410000040384034100c010316554140340c40545807600004901081002c02c0c070041d84241826110b203680d039800c08114600010003110a41d105a1101c40144004400b43c80078205c90b5a5514140503114050b940f0176061040322240c2064082c0c5901c2401502a04080214601c0600007800c01407040140b0903944e95500281005003d5942c0e0840303021041d100740c451802d00c060282800805050916005146004070b11030350740c00804450558231582d0306001102071070100104202c0d4140c40300d40300e040285207501442a601d103158540040060036500960384621100c040c0b560312a40c0c0c01e418042c0d9120000c081c02241c0e49050119505500e5920b0408140c070342190031210710034110300d0240d030644140201e01e41c07144107107190201044104c0c0020103025200c1d610511458841d030394266a95034080cac4004012070691 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980044721 1250 980043471 980043473
    0x3030f0e0a05060f0715061d0c07110609180108010b100203070825060902040f06061d131802040e03090a17030409020304060c17070c0f05030c030c070305070501030c0804 75
    0xa00d0181161076100c41c8200e240550740d0303541d14401b904c03050200054603114441081681e106400c10303004016229030b624003900e40f4000a26152040b02c000401c0c505a004441c009516042c06039010b81c00f01814104420702c1c0184010910b44091083d240b1030340c2030601a00c25030030b101c620041e644003990000c2d4245035056460310503540000c1d1302d07010070000d41c503072803c4901320282c412003103079014800c0060706090714010b12050301d01500c80c0007821400c1080070030000b58410002207001440d40707001c0c00c5900f014000500c0c2e091400448083c480d041900b1201d4500500c50360783c41e0188222010000120b41018240d01e9010f184c1c0520b0384069842c00420401006045600300d41010b1801d032868182c44a0101049030402d40e0b040e280c9035520040b851109807c650455401103108040203044d1822003002001845080001051441034001e1081000f42c1003003543c030000360000690b40c4507940c0400e0365a40d14010f10041e0740314450a100060594002c5c401c510601c1500d07a103e044503a03a13 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980045971 1250 980044721 980044729
    0xe030f07110d020a0b0c12041d0405011e140615090d031110021218071a190c020a090b0f010e0f09010f1511030d05071103031003030f0e0a05 62
    0x191107019608420551407850044c2d99180074400501300d86034406449142c002801417400503010481c2e070341ca41c801c0100f4015025404520710350380308811801c4c5000c0e507607450030501418076000107107484076010740e14200c0281150045190084d28a900715076070f0396540d080050115844510180154040021040700c1c05c218200385649800f07410404500b2102e402198502034000c0300c2c05c00d649601140c0b21030034540035003201e50441c0e07460107500140d00d00d40c0403a42d00d42450744500703444201c48041892440201e54142c8220700d84440c0c03510203105070010040c06051200300c1c12031191074000008542180380b03200e80c03d41c00c0303030107062491440c0098005403a081c2c0346c0c4002d01d504c01c20322000700e1f080d982c5003121301c1e01818001d038294240c03078034003506240c41011000001050165104948121503800000e81e00320391848940807030542c8984600f50740d841490403d02d08203000c004100020301800c2044541180d00c250f88a82130716040038002c070798040c00520b480b03a0082c1044400c210501d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980047221 1250 980045971 980045993
    0x140f0c1f0f0c05030408070e0c0702032a04060f0617073c030c030609140c03040f020a08010203060f04050603210d1802100201050c07240e0c040e030f07 67
    0x407050506040806494540d2444c5030003651012159600c070300c0003480312682c1190320b960000d9081d02041c0c2050900c0e40000c0c2c6a903498408100e810140c0b0340c4250150700d102c180745900b21405401000398a07110070343c408002c0c105002b80008074452030207108003000b640c0030052062800e580c0d14003d1740500a0388140c6050340300880c6215502030508006010302d2014820b407001c5554800090f00c4014010141c1a50300661111102524005c004550001601c2000e5800001d001015a4035912031a000c2c41c0f00c0e5251038081d4115050040120780700724150700450103102e0407564000709008040401c000d44000310f03100380d019001080407881c00c1c0c00c0584400200c103100c1c00e400b400c142418210204171034454944266a00d82d990f00321055060140c1e000c144a021403009100030f00d051421242d00c0c0c03080300c500900d0010381071841c254070402e8000c0f01e00b170178841e0070041c81020505182e9955071144102c1c40c902c25031034912040b144050020403290100d910800b141e01301705686d295009151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980048471 1250 980047221 980047247
    0xd1b0b0901020d1812090f051201020d020a120b0a0b040e060d02030f0703140616110f0601120b0601080114060c12030103050307050d020115090f09140f0c1f 69
    0x590240f000e4801290507000d50ba0782c03139003d0140d0540c8085581400045034010b009114244417803c2c20500241c40d21070451816520251180003506104c000d00d98024400d60302c103d40704c81e101080c48046142d010400341c1c1036121a02c81401176024800c104450030005219a4800760000c01c001c000c6024000c0c591544584000c00501107100d480d008281000210411400680c21030101442000070f1055031203400c0c01c45000501c0f00d450041c1009103001c50105c540e1742030043c43c0c0d80c00c1c882c0c120200294150844614180d42c62540d54112002c180382141000710760602401d800a1800e5125020302412510401ca806041556030024403d003a0b2080c4a041e00c0780c05000000ca41104d02c00000354029031241c80119a1044141816030404c42001ca40c0d00c11641028003a1450b000e9501c0c540007904c065601c00151a102102418024400c0d41401050100c4d40c01e440c81c060132010403000d000e01d840b0b8081d01c4441861404001c03032992032000f41c4008101040301805040d10400b017074005c0c0e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980049721 1250 980048471 980048473
    0xf0309040c030902032b02011a010c020d14071a090306060108060a0515070308011d010927031706040605061b0106050303070501090204200a0806041b110d1b0b09 71
    0x658903135000b2078246681154055818000c920941400c2c0e0010440d641400e14240300801590f1841c00d107180c0e21500034410b4504000010083d0340665a48400100000364803503028000c50210341d9016880308294490a8400c9598040200108a103c01144c0e5032a100a002d08950781d01c840c0191841d81010741900e03040344059401041d030307880d45951003000741c0300b00180c44e845520b9442c0013003261005812400300d581500d54501e2803420203002050640700b288002090030504910740050301e002c040d0421030783c0741003943e0000038517410180c200c02d00290304450f0015541c40d201404103888031841520b4002c0c50802100e92100e50b02c08030403035001d400c0c0d400464490fa0300d000003491600f1680382a0790b1a5521100d0004518003031040113401c40900d003640c1c0c4494028440c110702806081a10000c0c02a40781c00a407180d65654012172408a0040510400001a80c801440d40c4800c2c0207003c2c1d40d2140d089400600c1d40a440603902102d61240801c40304032041c0d8035000e041c04007908100e22 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980050971 1250 980049721 980049731
    0x60f050d0e07080f071e180c0e10170a0b1e03030c1e1009031b0c0b030702030d050109150b2508091e0f040e0c12070501110f0309040c03 60
    0x2e0800c0134000c42c0307007410104c00101070b15428031200341c000498184001040620320304040040885117030052003080558200001d211a0103001a640d0340c2640f00c9059210180d50190440c003030b040410000c030715441500d03001d0389a40704941d0008540d0050181680440408808040701d2415134003031046002c0501501c2c03d16022008a40c40c1503402242c044d4101c1c07041541502d036040812146c00c114031110014040e452080d10060044485c0c149081d145000c0040c4600600082c010031200404a15140c165a450401c1e0003d48175005801039204407400c1800024994066000c0c010b00c80341ea10400704000ca1503c20102c54552051407618000d0104c03000b001490a0011680c1c10103a0060304041c0c1d43d800c0c0c0c034003000f0407824808500044d1200501c1c00b1a0701e51518121740003994015030b40003c2544100c0030a44c41c0034421617243c0d601000c2c51300e80c0e98021002003105c42c2103690030380b149800c0700941c900e550380f910900100704410760310074070040c039480c50607410070303001c8c03c81074100019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980052221 1250 980050971 980050979
    0xf121806071e0201060803030a05160c0c060509030c0a0312020c1f03020c1204060c11101202030901020c030c0a05010e030a0f030c1101090605010e060103140a0b03240103020901060f050d0e07 84
    0xc04c48c1c000700c504440c01d80e03840e41000318810313201b03042e1400c40e8400e1908007150880e59a1380080c2503018000c900401601069250407500d0801102d10f2041c002040210195030380d20b401d62052507090180310060042c00f1005c00c0a0800840740c0046c5030341800c8556901d02e07901c070120001e4100902c001410300c1404007030781a0104d844014000340c2500d50780c1e04541d80c9181880c1c1c9000d8940ca003024024501c1c410414141076019580215200541801580d40e40b00c0d00c1c0d14601a010341c0e00c40c1e01c0e2a0000240382d0042401c0010700c0ea0b141440b41000b803020520305c44105441c0d0144001500119041042e881e8017144aa80660394490003418500c007103c0d00c108113a400c4542201c000c803015644d800043c4031b0070741c5003046503903c0b0742c00f46028040c03001035070110300c12503101405e8143e0003070f02e403004164203035000d0103100603003c110300d840c0e074860407250300d60b0b9060102031005034090448180041400c0d8494001d0100b400c410b925058541241da03208180280b21640600680d40940c400100b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980053471 1250 980052221 980052223
    0x40b030903090a080c090c0c030307110f012a0801051e030a120807080114031908070f0f031202070c0e07140f0c060901060e07050d020f121806071e02010608 69
    0x20f020b003c8050050545981c04002d0004075000a4a044040001884110108003002049952001c42441c0c40c0300c0c01e084220f04a0702d050030450f00d1800f59401c00540f01800c040b20060490745801c80f180300c80c841c006800c016a071002081c0946904204000103101d01d080c01c2c0c40b100070303d040c030150807034270841d050791516488203140ea03a88000199280040c025101d0707000744d05a024004a09401e0b40101c50303180007030f5a4660043c00200111801c0320400c1c140300c0c43c00c0a445a4035041000144120001e06d401c0d1801501c1c00812008103036800000c003400c500c9842036990140d40074401c81d100c9811302281c1030a62000901c0c880c208220080354460205410703018003102d005200d0800d8903001c515464500300200100144038980c90b0080401c1551404070f0200d07000303282403d0480c2d0350280d021440000e80f284032905002640005000050317074600c040c6481c410049002e50030384003241b5140c0300361100d80640d01a00010018000280d002062005802c00c3c401c1c0750000150706d6513518071079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980054721 1250 980053471 980053489
    0x51e0309060f12070e060d15080304030809120a0b0c0c011806020301080c060c03040e0606041502032a0a020907030f061706090d0215070c02040504050a0c0f0b040b03090309 76
    0x942c02001c0c007280d02082107100010003500001581007449000c80c07070001080302c0d8090190139403c01600e1703000b4000c914080148030009480c2000c141c07a5036030349906041020354090440240100681c0c01c40000328070000c40d00003581644007541414a0326104800e00841d0005074040589540e80da60440301c007052852010b501501c104000f51f107940c0b6092005003041c1ca10040740d0b01841040220107000d4401004a4090b10801890340343c003900c4c2c40c0007144840c01590021024590914002000305030000080d00c0c0d01581a2410540f8469052403000c15410400c2c0f01c02440d03000302c40640044c130385140c2d001d50061591a0000700c00505160390826507029500165103070001c3c00d1082d07a50402031190a6002144500401c81e200300140000d545101e031200c80d4003000c0800d008122040c2c8104040110190020000c4c010f50429040c100d441e40c0c048a000c41c1d0840303892400103000401400448100e94500e1340182c2054a450100712441d0b000500b80c9065010030056800c03190740344502 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980055971 1250 980054721 980054737
    0x30307060501180c050f130302090a090c050d02030a11131401030c0509060a231203030f060f060901080c0d0207050d03050a0204120f052a01030b0a03051e030906 71
    0x8112940b4100e110101190f840f1124a12241002c2d1252070244d00b00e8100d6400724030743d0914039610442811880264445500025400000b52003800300d5042c0d5904181007450150548444881c0d4400401122800030b40000703400da005075410401140350540e00d1489900044d0111001c0d180d0300b000c200c2120325424943d02007402e05801802409007282d2118054141a1405d2040b03061000c00113901d49044e00c640e11903031500300c1141c001021682d814030720301d070000b802340901803444419031038a0b03030003c5850318141e01401c80041c60619140710341c441c00c04400b0b00420715004029004441da10402030a6140040d801c0040e032890350114030041051600800103002111a0000014140e030000ba02e109a2940180303c1846500c0d80510100741003a4001f020f08082145880c189082a6030110075000b08514403030f6044a2044c0003496940c80312090f60204012002a410081b003000039000240c03a80d880952508180c0b1600c081c502808500d410880b41009107000005005900082c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980057221 1250 980055971 980055983
    0x2b050f0d12090c21050705180f131235180a02130501051903170703110d02011b091d1b071b050409050a02010e0409020405010b090907050c100f0209030307 68
    0x4c2620305101d000d2240c41c000e031000b11382c550b800005071151500702000c00b0701514030750042c40d00411510020140404040c0c0d602607004080c0202c0c08030040d12030f60208041481c0400086075510315801104284090208071307c101c8116915028411070000c66411080320081c4101008600907a0304c109680c480b4000c5000086000c2d81000141b1260304060406140344010303580003400002d01c80303842040742840030450192603900a050071141d43d2600c484001c0c1034018031403041c8031180c1c190828441064420081200c0342c10350a4201c40d0005184104030030f81d00789510048080c03078040c0b07400b0341120007007250701048103a803e041c82d01c035403105d8401c4032003444007a13404212041141c06400181022901002011160b40340c442c0c40304035003000281040018042890f95980f1503100d5842c194002d0810011581c4654404009921242d1500d01c51520800040e41e8544580c08175410702c84244003410b011503403196034201611a2191018a242c0c007809104074548007080502a0395010702 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980058471 1250 980057221 980057279
    0x20c1c0c1a0a0e06010f180b06070b1005030d050702090c0f030906061e09070c063e07020307180603060f0f0c02070605070803062b050f0d12090c 64
    0x12801401c840783c03c880424076800c0800100b046400d0b4210480480e10480030129111030090312050052005a01d416881803011620400340b1180f07001d041d20030510b201521001548500c20180e9034010b10b02a01c0002d00d0400c0002e005080c460703051a00140380c0d9000b2070501107800680d50103a04100d50b0440c0c10f901ca4810010b641c036040c0c00303d21100d1240440351030b5501c0c1d01404180704a000602c098180460407008204103c000c1e4842807450b18039135140c07010340606001444c640c60015050109002400607201d040c0400f2000f00c5880c540d0050040034158501103503209648682001c210003547d45440010201e8624000c46600c085005000910410300c0403206003140c20070300c144c0046500c2410280a2241c0080854803083d4108040c0c07501c075a0340d00006084240d40d01072a80796a4054030f0340d440310081c12200c3e00700003485241540c0040511159040c5e48141300f40f41e03400007503100024039548071031b5a070200840340d000f45038049010fa141c00143c205841e040140c400781d40010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980059721 1250 980058471 980058481
    0xf020c1302130e0c1306050a0c060b1207140a0e0c0901210914060709030327080a231513020d060c050901260732031801020c1c0c1a 58
    0x4030100b54091b01e40d81c100b460400706100b00007080004900c100a254558a500483e210f035900c035010403020440c0c2044811254031500e10382440301c1110322060013422115004a904456241580d2080844040c81d9041c0020b030001101d012200d41a0b05080120598101d480980c0074014865100c0c0204000009600900c20480c50218000c040504004040ca020720019a100621000e6508891204807040414040d114603500c040e60000001d489104000d1041260074031a140102c01849104a0005141c3c041e00d62195174038401c1895180c4228009080c1c0b4030000c603041a100d00240140c800e070302c0503554000403038900300c520002059010441081c83c0d0790042098400040d440c00e9504500c20b45465203128150180600007803140400c284102034500590440900950314600ba1145180f13500c420410781c8251003034455020281031054050308140211040e40101c100101001d50f0021240c610786494080c9060820102c10600004224150150820800480c1910f41c6909103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980060971 1250 980059721 980059747
    0x90d031b120e0402130504150503030c0d0e060f0313230a02030f010c021917040e06150703080411030708240601080709030312141302010f020c1302130e0c 68
    0x100e020b41c0719900410500804001c02e111032812a1410f8401141a100300f58010100040d182c206d07980610021401e14403810300091074920900c150789a008540c0d104005001e114411101c040c20b07102010408211812607620f0501d003114007940e080b11011032444109980d4203c103040302e0200380c1c04081c000056203002d000c0d20003d500100e000b00680542000003035101e850702040c03010880031041003d414043c601c644118403d22400785165a1615000170742264031007039a946008061410002440c0502032048548058164444008681d40d654500711300b10129104030740c05019421000810b41420400142007a400c9045034004664500c0118520200100700a04100d800c2c400c0c80340c580d0300545081c094903014a080940d81a01410380c50160a140150ba466440d010007082100c4000c0c1e118201c1c040d100341c1e01d0348850122000101c0e5541e8941c5901540208180c0c0c2808904410343c1c002d08a03510355041002e0744955800740081d03054012603900640b01d02c00107071f200e00741e01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980062221 1250 980060971 980060987
    0xf0c031407180e13050d090806071d0402070609080f0403020415030c05060a030e0a0308040506160905130b06070614222d21020303010803090d031b12 66
    0x1000d49000341030001075840c5403142d41898410090700040c454042002c12210110707100106030042c0440d6009400c85000400030403440c4628101e900910002c5081e0314400c81d42c3d18480c05a10b20364203948201582000300075800007a08031001c0340d80c3e803107a2000a2000020b0503031010044030712600d892950040c0005c2d80d050001d000c40c1e0344101801440000c0440003408107940003a2003050b21052103200580080546160441c0c00d0b100d0103000e20201540034025510503403040d400d4404540754001401c2c07440500c0c0180704082021803005002c0b608005682d000d88509069010031400340040c0400c0c81030344402030641e101d50f00d4144030f01e429526694960380003841803034500c2a1000012669a0b48411004003e08100c0e22407030b524481c148664400100d034004a80b2803404006a1810a90f540740b12801c403034941e03041d180304d99116800801920704031015800954500a046400c210320507c0d40340040301440800750040079030341e500510742c07407400c2d00c501034001c0303024455003001e003500c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980063471 1250 980062221 980062231
    0xf200c01030629033304110313141203090a05210313060902040c031a031b0d031710051921031103370c11040f0c0314 52
    0x5100c20310b03612003200f81c8824105001440b0300181e280c2d10780ca007800c1c00c40a02c110071446100b858102d243c91048045030007a80e040c1c0211010071000b4207009820010b4041110300d03000d2902040700344c41c00f0a209210300300b41e40c16460152451100b510700a544950015262a20290b00c0340d42c040040110400008c0c0c200700000009482c0c1c40103600d0850f01a1000514900704030100b8210300c0c0c10458a900806982c0354010701c180304600300d50310010024019038031514400e440c0c00700d400e4540d09000c1005050b10900040300050700d0350410600c2540f040500302203041100000c00c000300d910003141400d0148802800c494520340c9007400308191620941c0d02140d42080044017084400352007009440d440400a0b0312400c501083c1c00c06641809840c10f010109000000c3c41c903640c0c2807012034205d0454107441d064909100011913040c0860310383c1c00707c42e02180d5490064404514841c291300550030000f8004130320455002942d0342500e07010449140403c2e101e400e001c00d0745540d80281a800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980064721 1250 980063471 980063489
    0x50f070207030c120204062714150f0a09140109060812031303020c060a0c06050f0105031f0603020d06090b2802070602120f161b030f200c010306 64
    0x1c0c60660301c0d2142e82c07100c0c502c54074028425010307041d82103440d69001a001084448003203229002407107a030799041c203074500010640c1c2c0c0c0f41c0360756001c0d80003078028140d01034182074210f203001c8608041400f07500e046120180c2d0748102485000545100b01d80200f140c10810b55081c1c582c1c0e945130542070380988a00c0c2d000901c0f43e401c034803d401c091480c4082680d0380b16076480442c484607082410117030b08110000402c280c000741c3c00034054a4080e0810641201c0302d00c2004c0401c095501c030162500560402e024071545030b0020181c0440130006102090140140301c1000208950350754005030701c18020210480e4000e440302c2c049402e200c060080035510000441e861540800c101c450008080e0554203a101c0c0260b010520303406104443c1d05070703116040c0100d20340b090340c140b50f0795107280c8680480740240d07215030407441203607914414190307031000d602c0c01d090540c1c504503036582c25242c050101480c00c00b0800503030042280748031002900044103c11101921101440c0f10004054a540d60060008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980065971 1250 980064721 980064733
    0xe162102010e10030e1506030705150f1b0706080601030f05060d0b09120705011b180302061b1c0206011202091501031d03130f0510031a1003050f0702 66
    0x542d0308022140c40342c030030440301d812481e1800c002c240c00038807040240c008548030765040c20b0000740d04a0203840c020413081701155a0956a00d00b0800904044802c1e02d0b014801809592005040f12000d0140c0c80940c036014428034895001052800c007485d8040c00005a1030000c3c041d040d6003501c61106400240c20040c8820300c0e1910100c4c50f4a81690401054020004000703074504405005c0c0d080001140e03540c441d520b9015080490292800c0e11081c6800440030003180005409408011615155030b00b608004500e1902080916003008400084d240014036802c014148240504165410511103941c0d420019a000901d0880140c02c20402003a01e030355450056030740e50505560220a5102c0f0254161440e40100e002e09641c1c4140312448035481c0c4061910030300800a082c2d0404a4400007100f40c1e0b0315507109010700d510b44a505d40024141c1d0466410034401c0d041821071240d100d140420114440021030281d091000500b00001e0b654000d01c6041c8101c0e0340d14a070417000c00d10003000317 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980067221 1250 980065971 980065973
    0x1050405132411091005131a09040c0513050604120b060d1b030303110304020604060309050c150a2c1e040908030906071d0f01030e1621 60
    0x8820607a24401410030300200026900241d821080c40300c1d5004050300500c01910b4120240010b90010040f181c811a040083c0014032441802034400d10328211400c0d2511a2814100040008117010b00c100c42c010100507000c8907403036900540501c120385580e407a0b9a489032002c080c60042050300911710403031041000304090b90081031608a810303040300c00a091030310f23038200280300d07050308042c02080b0401c2e0802070181100c682da1010101c074000d407000d012480c1684204641741c0b1048070025480082800305002280c0710f58040d0803001c4c400d20840e929164000c0c00107034507a1030038090501412001408143c11540484080244220503101d2500d01d1065032400d0652107410038040d025070819000720000701c00100040d64100c2016004101000042c00c140320300e5407084944a545105180100310701d1449202c8070075035441001c52903000c0d48000000c20a00741c0c01595003d040584076544202e041c04144071805260b48148841c4051030302d042d2100300f840189085980c100c480740c0507450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980068471 1250 980067221 980067241
    0xa1404020603060118120602030618100e15090405160801050411041503080720010c0201090b030c070206130f0e0f04020103020702060c010e0109111509120a0510090b01050405 77
    0xd40043d02424840390400c00d0ba010500303012020b40c0800341c1400c4076848007040c055141d0080d0301684041e50610700034840500d900400210030f42d85c8070580c810b14081001104000074115401040300d1907480030a10f40d41001a801032000c1d038040d201900f12140106c0440c0610807141e00400e41140244240d240680f965680c920140c64200d000b0354039200b8140150f65020184400303150b102c160f42d2303114400e6080400d0300d02840e0003030381c00c0c18003047c010b1081907004240d1240c84e030741d05075902c00d071045c2080248051908041e0104152440a1004400598034900a006402c9401140308006031420121014408181d8408210120080309000c4003213291910598010340a00300545d40e400d103880401c54034443c04040ca41c1d00e5181c400c00b000340d031350706401c8050114010341d0584000440c1d03a0801c0003407803101440c2e00b0030710307001c00144140e0b0a03c5000c000a804440c0c040c0c0f00307210b02d00c3e01c469080c019010086100144c1c6c0d640114100301081c03281e40c4c00341c402640c08202e0341ca0300311021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980069721 1250 980068471 980068477
    0xf090d08060402090d440a0e0f060f0c0c04021c0908121602010b0102031c050910050708190204051302130f08030909090a020901030308070306030b0106080a14040206 73
    0xaa00954000440d400039442d03c45c0701e1052598022516280800340843d05440c00c4004c540c0d00d4901e907082c1010201c035200b110700380d500b0091120100d62600003010000e868140c1811240c0f5041518824040074179550b00d4040d144070310325919456a0354000e00a458100550845d68900c17072807051000a030480b40c100e911440704840014001040031103820201d01da4052101c0042c11203403600c041262000010b210b400e280800340d0000d01c8440c08840041e62030703014181102d49018845d5800f030302d05000c1070308040d821010b0386090b41c07592a236509541c0300340d074000c4035000d000c505403405104424000ca0407180c0c5c02c02c0a0301c0d04500382800d00f4000f51800d2090064044400c0c2c0100c4d14845016103202d1310b0009015140061085698842c20651283c012070241d41c410311450001075950300c00402e40e030f594258020060300807607085940c165054800688140c04141da20040031000032202207045000e0441d9498500c903505d0110f006a00b80d5000d08071f20508210680d0902c00143c0310300082d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980070971 1250 980069721 980069731
    0x1603050604060b0301121416150c02091b04050301050a05100807030b0406020c0f161a0405090426040905060a080a0b0105060d0902042c03040b04030314210f090d08 72
    0x464000c10f1030a0512030640340b030340c5030038030300501500300b9100d076092080d0780090403030341d00c50128600c0980c802010340c2d07040b22b10300002c3e4002551500184806501c4004000c0303100c03201181d1400d00341c5407008242141c0080b40c0540302103035148140b14294041e65440c031b004114080c000d0000c20300310b07540c0380307035851000e4002450030750049262080d02105100805100124030101ca010101520f80c600a100c2e1501ca04003031460809014180c1d80301034800c450580780c010b400f411035500c40b135450380055940d0151154200102c0450028029840300007803000f4114000085242e080c0281040300000c041c0d840711506510642540c0c0c001400b003035403681100e17821240180c0f1143d8446015002d440d11150081d4810f00d00510801701602d60041e000900100500074260500e14000e030555a2107a40036115400c0710501040001900c140c003011030b0305c1114924980ec0045282ea81d000d4410803540c03108402c0507490400001410b00a0101d610140c0c940082c4000214074201a00e0920060a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980072221 1250 980070971 980070989
    0x705090603060121060905070c0f0b060607020d060b0405070c230709060905100b0c030301030b0a0b12030c010b03060106090509100321020d0f0f0e0a0b031603050604060b0301 77
    0x2000a225a0049540344690f0b01e60704007028180201807004c10040209009864640740303450007281ea4144130b85a44507686600980c0e0302c4180c1c02a4403000c1d040c040c000e0400381c1c03014041044d80d0041c1c4942c0802c03501c85128038408107018014004002c280e410080c01d03031041102c025101c1c804a08285800d040c0400c1c000c5070601d00c0c2c800c0d1404a42400384030307000342503014246400007070f8000c92548240c0c8590b0995105000880e2160960955071045201092141e4014001400071403028809a0382145560000089500001d00400d803080c02041a11240d038101150740124803a01703000302c407109107046010b4542d41d0704000c0c016142d40d86a00855000e030040d000043c114070880400c0002858020618910016581e07450361000c3c90210318840c010300510018a11050040d0564800110300b5110800d442d0110502180c040340c41c0c900250780700c00c801c0c5001a2266015008500032104001d0080241a8101e4081d05503000a40a24082c17441e24008000e203003200340541e41583c407081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980073471 1250 980072221 980072227
    0x10e040c09050319050c060702030d1d04150501030b0d021e1315050a0902070c0501030c0e0a03050705040e0a020303031f090501080d0816020604120302161a01080607050906 76
    0x400c04075103409072500215010711a007441100102680c0600a068521800c00c603498406800309104150240c1a0025019803108004492180c018903088141c0110840001c00802d01100003609542480003515820b001500081c81b455034076010b00c1003003041c20395010489580a0f4081181c00459100c40d0fa54441c018410f08900d80c1d80c504481d00d41004e65600340f003002d822103422180340d0030302e01c10b05104400c13030240001d1600140c000e440c0f2890b00030702c1c0e0002c3d241c80c00c0e0041d400380c01794050701010405198070310000c641d00d0000100c05540030314001c2c40d02505100034081214010b8103540741d00d80c4010110001079800000700c1f0b07441400e203102244001e4241d681040301000c81c0c1c001d0210603003000004104001c000990105c003519654840e4811b4a410706a561240d1082c0c010f9001a00040006004035100003082d5004101902d8010f10f0308005100c201d080001c0b40c1400c40d100b03000340c401d009407507030300d841540d01400340d13040900854206894094110700c20b41c0200c0d40540c0b404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980074721 1250 980073471 980073491
    0x1b081801020a0314030a15030606051f1b080403020303030717060406050a2309040f030807030207050a2a060302090411030709062a05060f0a0b0a0501030207140a0f06060e06010e04 79
    0x79400404487c0c003074900d05d0741c260342c0b20b14050000d40400e0040038050900c80e0900d400002e0410300c1d510b1000b02c1a1a10840001504c80240d41800b51400540d050f0004001c0000161010001580318aa866540c3c020609182500060095010b80b440744a103042c154284505d588000012049442a2026603148450003590307510800041e541d550344551041d040200b80a1140d002c441403e201ea66120354664600c03400341c0483c004c4078800341683d4070458108000400c050f0082e510b944800c0c1030000030403071448005144142c66003260780029000308105266013054010211809241c074002030031841d00e180c000342038940920402007080a40101c10140e18a5000448400d019400d052550042d00b410b240d9903940c070a54420140d050154000382c0c486104e03103d01003c0c00c1c4000c000034007640c54800110042d4221002c181c4100070041940091000100682c083d41881210001c01b01119401c203d411a4019401a91045100c00800900d80e038001161850a041103030001400030403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980075971 1250 980074721 980074741
    0x9180509010f140403020d03091e021305010801140f1e130503042c060901142b0209071b060f0e1618020414060a1b081801020a031403 59
    0x8402c0392164400c0c0740030400000a8190b031000c40c401c500907000c403a030007044980100c0c1240e17881c02d005070400b4010140024030040003411000901e0000303210350301e40b200390101d100031a502a402000940c3d9566000c10311126160922a400501c400700c1481516040e080c08a0403080d10340b415030f03031208810024408103490b020720842c40b6001000c0301c2d01d542d111120035201039507424201c402d241305107007900301804550100602c04d60001d003c1d04480c0c1d20b001c64a80f0f140c1c01030700700990f114215880c01d030880b00085d0300f2602601013000080744c03058114014441c18010250283c000c00090081401e5800111500a40c20507440000060f542c081c50700c2080041c02e0242c288c4140e8000c2d2096960442070081007030080d01d80b030918500440c2e02403401d94080340300d00e10032900819058a8403404919040c0f020b048003580c9030620a6081d01c030048500d0800740034900444a199000c190301051005d80c02d10350f810480300b0300051518031030310f403070180c8081400301170300c001d9075000000141c51441b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980077221 1250 980075971 980075981
    0x1203010501140f07201c0605070e04090c05100f1718060a0911031f02090f18070f0f17040804150c0b070201050147030411010918050901 60
    0xc140700b81540c46501c0c0c0d141440781e4000e60b079080d1711001c0c03016110320100d151041d07401108800c0a072080c18a038800d9a81e220261100030440c0341441070724031800f10b00703460754095850002c1c80f400a0300303a428205403c10000044400f040750400064440707403003049403c80d81d110325058000b1508141c5990745070130b09104514812801c00b540c081e800c140501d92100d900a0180385120b0310a8080a80741a01416540c2e4a604030000b09003010003681c42019026034010003074680040c010b0040035860740d0115240c514550941000d6160941c104004540c1c400441c056917500f80c03520000c6482c7d80e0b60002c1c000f40085088141020600004c50200080f038001c540040100e0851002c0c4100001e00250148000790810f441c100b132203500251442c0c1c81071251078161114180400415000780110550000c4d000c07ca1140800c03c041d4440c001c1100e14550300101e0041500e61a0b603481c0c24688510b14040d0b81414905119414a0031b1090b0b008079200e120464021280c0000c1507503a0404060140c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980078471 1250 980077221 980077237
    0x111603032702102102210a1b030e190f0303050c030402060301030201180f08030c07080f0a03110a02090a1a01020c09180115080109050d0e010504090f140a1b02120301050114 76
    0x40c4001038680b02c2d55510b40c04010711540c840340040155880d080010151100010340341a011230751164120228040c0e4407903000b4000400460341c0a17407400c0020072103040c0c12402510340f9450284407104040e410302580b584100d02c64040d500f10b09117940400c0f150700060000034103112039180c0c4242c2d035000b48035000000740790482c00116440d5a4040c5981c8940c00184d03098106d000b56500400c004000203200c03082e1b030350070400800351010242c03812600300310500f801c0c400c0c0d409000c0400c0c0150f995100c2d00380c0030f9224135500046070504106408020308040c46145d0640d0000680c41e11a41d4588a11a0b030152601d4406010300e0b4203914024010400104480360404042c13002085118056004020342c4d8422403c41706640e4011406442c080820300a060004408000c24070800504d508107103900011190003080440e0701c1220042d421600f1030709018021f640d20060341600680c224085000c3c1c00c60700241c1107012103115041c0d143d01c014041c2c64107000c03d44244260ba40d040301c04440e600c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980079721 1250 980078471 980078537
    0x120a0f2105010e1501110a02010e03030708040803090f040c0c03031505060d0506190e0a09171810050a17041103100c0305070e1311160303270210 64
    0x82d41e155802150303203107001d0718030090b556100600f944965014551a20010402000502d00300d0a10f6004403008060f00c00c0c5a90940000d114010000b034580002d8000b03448501c1c00707540c580c0001300601155051180d045841141001040c0311540c5c3c10a840c03402054040c50003040c546103203040300c038240e075003a849281c2060000030328481414540d44a00c0c02040c044407101481c0c591040b90800894460285030210000329002c1010000a6480048107502c5110030106004495001807125040400e001c14011018400021107152030300382c0070408003d50612508103510250020700300c00324121030314041009030740801c003405104481c40f041d000c8001c00700c4840c40d00d9010300c1e1024050a82001c40400c1c00c0c02d000c29000703805110107942200c03019107142402501c1e80f6044028104640b00e13803003090800c0101c0303040c41da0142c45c605034450203500e02280e030006400c881e255503141d80220500e01c02681c00500d0050783c48101450000b4107901c1c1072600e02da482102160b036041142c40300109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980080971 1250 980079721 980079731
    0xa14100501150c0512130e060d0308010605030702210702040f110a03020f0405040204060504080607021c0309061104121401020a0f051309090f060f0509250807030c08120a0f21 77
    0x82c40d541a4030601500c41c4200091f2a903107070700d01404040701248000401043e115030041c050288528081c6900016510454000500303240304588580c002c030080b040310200000d852029810b0038003031610081c486034010848039642c0c00d0580094000c440000c400c25400040503803040980e00281c2c0c0203841e00400c115503480e038231000500603920512034440240070f441d000500c4280041082810159880c4481c200c41c800f4050440003041042c800301c40d215071380c800314104032113960302030009030144861aa100d0f407007134203004c0511303910344d034407040d07581e0040103070018095101e115281e1001060500c181c0b41e050f540c070071551000a5821800c1070360b29100142042c0001c18055105050141c10100010325140c0b00d030100343c860444510920b507000340e4509003041040164049000c66042c000e42d90f0b140c8034442d2904040007548107031950880c546041c0440402030021580030300c45109600c1c60b02451700d0000e0528200791800006000200203508600081c070b082070000a0319407481041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980082221 1250 980080971 980080987
    0x6060f0d030908030a090305070b1207121b0809070801090f020409080f07050307021005070b1503070503060a05100501090f09110d02070308010e010b040b0313080c0a14100501150c0512 81
    0x80e1106e180710540d114404e10000103070680c0400211122050582014a4980d42d0481c0903128a440c200c08410841c1d03503000010510641c1c80301820810100c0ea880e0545804c000355041d01d00b441c3e90b0041c451a91518403074000040078039080c00310b51a415038000c2a41c998a08240d50356000b44080700d0384410340002d0709420030501000034000c0c00d10880d00f5404800340c404040382c960294180042c0f80e02410b03c003103201600000c08a03461240d00500b184e0031561a038000c40d0604030107886c0100300c10b44403420b00a85034003103291100078003028644819139030f10f4684108051004c6120321900165100303150242d8801c41400c03074084002509081d541c41c086807030003c100b080d0910441541c0c41540d000428403240340400c54003284c049011190442d100c403000d41120700752199045030340050030440c1d62940f0005212040d41c00c0e003c0c420000e0b00c2440000c03030509002c403003240203120740d1505006110507060040516040700e81072401101c15902483c1c0103180100d40c0c000d540709010045181c1da = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980083471 1250 980082221 980082227
    0x6040b0702030909090c0414060904151116021509030312090a0b1810050118050a091704080705091e06180a06050307151b0c050a06030203090f06060f0d030908030a 72
    0xd10000010341e8200300d04108c0f007100e0f2800c0b0b6001d55030103030303c0b486039400305003c240010f0f141d0104448040c4000b60012900c00b03d15002d80c4007c00001004c1e4642140d28203610300a0001041400c1021416240c06003000c0000e0300da201c0c90400510303584400000c9020f07004c0403c01d50b103400354080d048c41041c0c10720a90801c01180c0710000c1c080e081c0f081d50100c001c010141d0061074100d4441005c541042c2509100d000050a4000c10200006036184104d070701007800c0101c010005d20150302d40e99a150f0030305401f10b04140060708481d0161038001d090241e004a04442c0008000060350181020b0320340c1d0300080c0e100250061808401c44101c020312003000d40703581c0301c1004c0700c00440440702a540e594020700141100510b400e00403440421100040b08440c0340c008070080d1060481100c1c40d600c610001c2c0100c5511340085001035404810003415030300c20844101e15201e0384004180b40c1c9012000941001c8005460700d014002071707110141010b005070303848000783c602c07901620317140d514101d402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980084721 1250 980083471 980083483
    0xb0f0d270506060a0b2a160f08060f0c0304050c10050a020d1404060e0102070f030303150e191a0303031602190b0615090d12031b0206040b070203090909 67
    0x150364030301454021468514046504100b114410129982420402180e1b450710040101400390060481c901160705e0b5038050050410b03820301c4403480e9030040c0c2001041c000c280c0d100c2e08070030030991081090055035410403004c40c1d800842c42c00c5140e901d9841e03150207070034a40c405a105030001c041d444001c20302c0ea0003030003503c2a1030440d4211040c49804a6044032070f12204a0b00f40700180d4100810b00c0003900c6600020014a0180100c49002d9a01c9202000d0140c090b882540003e41d1150007015407041c0091030030042c4072031060701100e070520942015031902440b00701c080b01c42e03a44c0c080c0c40743c0025100025001c424018141c07600c928100700011450081c441c194001806000c495400e1040c810424070b0586412140c180f103980d0303648043c01041401c050103608011028000c11110b40c1c1c4004500b12140d101300540a2070341c0201302c001d0140c0b1426000040700f00e0902c10414680c0764006106a80140c000b0748114554680792402d9081d882500340c0f032030f00311024108016000c10000f0316 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980085971 1250 980084721 980084723
    0x240504141b090f0a06081504031d010509120c15030a0e150f090313150909020a12090c03230f0d1b02031218040f02040b0f0d27 56
    0x141d5004078103129005410601c03014200b81d00522120210f0082909210815030044c2186000070b81280c6400016280400c912141c002d1100c02038100020103a002c030740040032505c1540b00007694041000040e04030f0044001c3e4500a04100c64061402802045000c5084034060120000c4e004040c4044140350300840c0c80c91401420322588032110140000c40c1601140300240f03407201603c03030160304007282e68060090020f62106010b4692003481041c40d05000700f40c0b60ba0092000705aa810240110b8816404074145c103105018082c01107402a000303040860500b8000500703c038540c50608e074181140d8101800c520300b10300c100344410806441e4500003402e840c044800c80031260f0362080e031310f11a000d51200052000000801d080400c0d2920412461006050301c1e20890701c3d12030150660010030800d600c2c40b00340700101c02d49081c0b074498200031410010040d841d040c140785003031200d8850b480038141c3c12400001d06070240030141d440410900c041c800d0f58000b02d404101c03180c0071511001d074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980087221 1250 980085971 980085973
    0x18150a081005100504290405090c250203010506010c170f070807032a05100506040f05040b01050a1703041e030804030804090605041401050f0307091d0f031624050414 73
    0x401510407240c0e0350054014000141c0c03024500b42c2484144032700420007403e0a41c800005203c05441c1c1c4203a140402040c540f8000a11840c00c084c0c010142910000381c9010705001280c02e2040204030480001030508c8100d800c560766450608018400034442c0c1750001c0c1c50190003080d0a400c041d8001d6024405503254400f805041c0c0c108103c2400303161032103400030040c0d0320108811314091029040140e01005c0100002428800207a8102c15142c0071507084070346418840042c8264548004043c016101107070b96800c280c450141c5036035480c0b2460299454106100041001c04504d244c2a040a10303400361440d91156500d00d000c4d019034000d0b010742c50256080c0700d004030341d604043c800c0f84044a404910140d41d43d18007414001070f010080c0c0e1058150060680c041441003040c018460124044c1058401201401d04820f05140140d50607076035681040052511104c2c00d90701200006401c480710300568044c0c2080c59403210640e02c1c20718000c80c1444100024000d00341404551140d041c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980088471 1250 980087221 980087249
    0x20d050603120703030504060f0f0b0a0602034003060e01050112150b010504050418110102012021010603020c0c030607020a0b04060905030f18150a081005100504 71
    0x5030070981c6501c4000d9080403110414020362020910035004907400501441000a040010074142c1080d80c9266450490950315104064012308003020b10800525061000c1d40c203010751b103522000405070380f109000300419640060b0442c0340c6405000524810789464407164107640b450700002038103520301c1114841d4070b032600004040810703d0070041d07165400381341054001101c240342e80040440d029442d04000b0103000101c2c40d038883c1d206804140b0365443c1401d01c8000c06241622058003180e10f02411641885000f50038070b41141d03c002c040000003200c5948806a203c48041d840201c00001c0e08114140e2000084490b00b541c003c11200003150246c500d4020f449051565880303003662005d005a11074500d46000c5512001201e8000b4403070000890a80c155482c5c061071600510100d041c0d10100103144140800c1030000180280c40643c0d46d2031503240e2402465065002c4e480008050080d0040000c0c0e1002d40c01020201a05005111000c00d07000c00c00024100e4000307001e80601c00c5088 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980089721 1250 980088471 980088481
    0x626242e0212040302060433020c191212030b040903030504020f150d091e0812010f05030a03030b010210110d0e1506010c1a1905071704020928020d05 66
    0xb0408842c1034030b4015006514251902c0800c1520710760f100342455541e05107206010380c00300300c2400b60803030001c0355000f0400300042e4004c1010010240c8450050300180130010401680380240c00b030040b85d0016032026443c8003e80081d00907182c0300341a164058940681c0e00308154055001902443c020754000b405801c000c018031610801d8003401892610090008603100c42c26501700c812000e03c42e40d00282844d80d18160380c47c5034490b01b001114040000704030716990504002c44107004040b2042c808040c1454100071036250f0b00396500c06010103803134907035007125640200001109442405000c00c4070540b0114240e1041d0080f010f0300360900d0520078685d018170b800041d1004031200c0b07206910752544070400159034100305424100d81c4c042145100c00394414800d02114451100c2d0458400084040f02030f171001c465004244a09000c04240c1e0001245003580c8001e52082e4196452006516034261103403d48200c0d40500d2404030704100415042c222076009032114204a100520042d154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980090971 1250 980089721 980089753
    0x108030304060f1a0906011808070e070c0308040206090607020d0b0702011508070b16080307050a021216060b1912020a0806130b0a020409060626242e02 67
    0x201c48003403084c03032660300c0c54101a481c000c0c0c00c65400200504011a00340102103c000d06500154400f01c92074008000030490030070101d1441340d00542c14689007809070780030b1b500035095442c083c001078000d132030106400103640c17191821504d800760010050060584103240101645004944100c019420203041105680c1c3c4881d110313068030280d074040c00c0c101e400c024205445400070140c1e0b121424121b19128042004180110301032101540c40c9503854803002000b914081d4010501c203006a820802c6940b015030240c1c0860301594004c40200f01c1d20a050006a480039443c0088080d01300c40c0b00000a4000c15151125034451094131015a0107036a4407000b920343d181107a04171641008064007a0000e4140000c040d07000301ea0480050505485003010001c0f0380d50303078000c68080384000380000d507940b40000701c00d0702c1100c01519a1300c041c50040329008600b6120f1000c0c8620b00c0c00444401c42d150b548034007005881c0f5940b007182d40282401c039003c0a40d0946c00c0b540c071025005032111040d0b10300f5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980092221 1250 980090971 980090981
    0x42c07090510031509080a02070f0b040b0f0306010c08161104060b03190216030804230c040906060902030a020310080102030601020c2b050601080d0e100f170108030304060f 76
    0x507011030440c0c0c40d60300d900705200c0386101c4ea103113110340d240b42c0b8000003080000500000750440d401000c8203414858060400e2201d0b4010740e1a100c01400100000030858045440b084030001106403692101c4005175000880031000a00c829000b0070300b81580740c4000c80c0c898140b801007404510740074464040c4004c4440c10301a1503254032080002484040320003102c01820440180c0c0185000203c5120820400000b9011000143d5050031310080c01100103488510000b001010810640d4803216203076201102444a40126200d5036524103112984c0c0c03201c0000d0000c80b01c1551340e481c0203044400254421a2002400964136001160181d01482034a120b44811303001401800c400e0410404840301015001c00c8100c0704002c0d4649070034250b4034208005100c0d000415040d41000d10035810200400004010005080c0216038990384000b1175840d102c08034281603aa5010900d0b08942112030030038482c001404100002900307020000c0114400d600915003000f1005580b504841518 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980093471 1250 980092221 980092231
    0xd0318080f010f1a0d0215040308040501110f0c090a06080132090307111c150c030b0a05130605060f09011701030221010e011811030609030703030b042c070905 70
    0xe01408502c03005090266001c10110b0009044042001043d51003131f02a80c0650012150350001180400c0745582013011401e6007808440600840c0d42984112942c03001120b030828071501000d0b001c220b002800d0740c012070207844410024410031011622400300b181c994030110303036200d0010440c0d49140c10301d00b203941e00034500c00c80558a450210348400380c42000500000340d000400d41c242c8141005610404210180f0461131400c00d040b00c25025000c0740d403920303da1024141042c07044811541e80807107803010740780100c41c5007030b1a025900740c4500410054000c5504808000b44515941000802400e1000001d0741c90075420340030300d807c03000070600c00c1c40001e402940050790440c00c0098503611f208003404400001170700311221300c0c08900356a202803281c06002c03078004d2040180012054030400102080c0d006154500b001004241c1d42e2240c100060101030344d41982804a5990390420480b0745014581d8084245e2440448a140d03c44005000400e12071340703400040b00040303409520300c01c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980094721 1250 980093471 980093501
    0x80c0a080303220302010b0d030f1719020708090d030203130807140103230705070203010506030d081f1a0a02100903200709090809010801140303090d0318080f010f 72
    0x4400f110108078a2038050813819075480d116044c0040d210030400380c402c503011360b94120442d0328000300a4800c600705d562010160740e005080142141c2d544200703080d02c0014003001a40e03031840b402c1c042040c0c010200026800000307034a44e4001d065002018000c144203c07659075039125031301e0b800c490303440340f141c41484030303034482c280682c0b6103580a40d206c0c000c00c00d046480140651018228441c59003c1184c0c1d0001155000c641003003942424032625500c18025001880b000c0c14481d406480080b0042030804004510040c42860005040f0f14100800d41c9607001c5030420b0035810a04001c0d0000d140740e82c01032103076846502a55245000b07000e011a01516180e0104400c7d0001035480c00e480790100348c46101c4d0440008603000c035881b40c921a64003a0050035218000080018644041a03000080c16048411142e101d684d020044460741c0030700700c1c2c000c80300521508d420343d1203200140b10305400c405003100010701d10001150341c000c42410729001f005402c091100010032507410240724100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980095971 1250 980094721 980094751
    0x5180124030f0507020106060f0903080304020d0816060507081312120e03030411030c03071a0a11060a0b0a05190b160f0f05190809150d06080c0a080303 67
    0x3410958200e10644003025240205018086040d24000d440d015941315005039564001003000c56400400c0c18418081440e00c1c0010500d1902c480000d0b00020348081c1c401c0c02000d03c1c520400c040307042103c0c048030a04041012006103818094010101215240d0101d0f00f960000390f0100c00c142c44d0f11806541c80001c1c5042e00301c120108440000305940c550355020780e106039075442e03030000700050340c0702c0c80c401c06c0c0307100d5000410f00c20305081900c0f4481c0c19004e44e004810501c200c2c05a02056221402c21400542d240c4142040407201c41c0d010740d600c0c0010340146014000602c185410180760b040301501e41000e8203544070300b4410041d840c0742030070560b00174820052008809903401050291203070007a2024008080d01c42d084444026402180c1e551000001c40d401c102050094031850783c6c01102000e03800d0510740318000030344074001e41148111400c0d003890324001d507454161440d003184444208040b545a0103040d550b10390900440d4810380d04282c0c000f9070134200004503842180000d100c2c4103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980097221 1250 980095971 980096009
    0xa08100b030f060a170705040c03050702100e0120030f01080f120309010e070e040501050705041404050a24030606080a0206450405180c0126010807051801 68
    0x42e00d1502030102e80d880100c0100001d443c20202c0c00c000c040c01d200380041c1000d40d10f07100422049800043c403060a141c00c007420420000e8000c01c031002c0d52046454041048285500c215005140003a810084607203521041d08140300140050b621402a003c0c00000f070766291140f05a0710701200001601035440b2074162500c3d6000b500165403c40520340020030813500381c1e26800c0c24100c21b0f811400c0100d955000700000d2240900440d60418014100075140500340010200c4440501030140c1c000c03916040030901680d000d5102500e80d0294141c000200310400c615449548000c2c80160f0b0010b04040002c03402001c08100b0b4404541d00030310103443c1c82d06102c84098081403c9074000d030032006803c0680c15000c1c003029042810007041802d181e90800080c01c01080364800b0300300407158904110f20000303aa60002d212070000b002400c2c004003021a0034011240752841c1251103030f6200e0003100000b820140052004140d0700102d95980c5003c0c0000800009102c0900c42d003040c550592403521 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980098471 1250 980097221 980097241
    0xc080316030e0c100507020f10020109031701060f0f1b030e130b090109150b0a080a0507080403090e0c07150b01020c1e09060402071a101203083103050a08100b03 71
    0x40c1507480504292303440c03840d14001503400b9604540c2580541d4440b0f0b41001050390184005940c0301d2007110300308065051000c01043d007900b410382030044c050000740b11f10019002c0d086000207505031400685d51241c2c0d510780105031200000c0014001d80800e2220320001c0f000703000d280800c0300d015100c1c04043c1e10b030400c241c016003036040071010401806000440c2a103150001840820100d844031601e03030414201c1d00e821030354000e0851040020380070a10002a40c400444801c0b62204038202c0340c5d50303d450400c500b140c46107010040101c1da01140c220b184510640102d078102c58240c0039586205c12540900c4005020a0135506002e05140340210403454210400c9401c1000070304018180380c866a20320400d03505042e08600c0c0e0354062420400794440610312100600401c031024100e280f19030f903029000030380240c241d5100c55502400c1ca4040607604040d00200c00740c1c0c0541d0803410f030311f03400c01900641c8600110f2002410340000504079002c181184021240741003050b61071956800888 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980099721 1250 980098471 980098477
    0x9051201270804080303040f0c05061c0b2814060309100504030e06031e0a1b030504050a211116031b1e21020a12030c080316030e0c1005 60
    0x100d4040c0302c103120200d45508100302541c81148528140c49405c3c94a003002c1400e05000d5000c5407040d00308102c42d5424814151101c0c2007114a10300108081072002e0000d18500e059003080f0211100300b582c490205144901004100c0d03445501d0020521a11002d00041e0710048516980c40c0d44250020f90040c2c246900880c8d100c1d00030b191810303889001d44c00080030b0b0707072003562202c01e6582311107a0740100066140c021034018400e140104100700c0f51311041541c440c28050070f101071660303d10000c0d0074072405011100c00c2c0c44e4058902c0f0140103a111403510382c03444031103a2a000400141000c9810f050005840d15034000d0900c4403e202c501d1075a68480c0c0c003c0300381d4251100d948810300001c02d024101d5160404101c0904141c185508050800c844404003504a400c410745140d03101001d6241c200d02c490945a18a00c42080c0709000d0409a07140b40c001400100000d00c0042040780380d60210b60050014440c0303075800d02a420454403c142c1e1500c040703c1719580803c002101511090180e402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 980100971 1250 980099721 980099723
    0x10f02150406090212210a03020405060705070e0c040e04080d150f050324070e0d0b04060c0806010203180907030905010509070512030c071e090504030905120127 71
    0x440315429482010410103140503078044815580310001602185005c200102010716194010403840507060800c0c1c10b400c03415001e00280000000321542105d10907012500504409003902d0f03650b40b40c03403800d566596028400c00314a8445400841e000c001110b007250708541d4119251071060f00e440c1c9409100381d1110341000307402503450801c440340300c0c02910000d00401045281c1c01c40c81740303000f0916003413014030322280111480c01881003455040c40240386800c03900528042842880d56000f0a40e0800443c501514039142501048100300e4903411842c0141001e40d6030742510b4407181c00690b5079000344600010000f0611070100d03101e0801100d007030340c0a50689000301c0c01080548556003122010348000e039103900182700500503030620003180d04940900b2401149000301c120192501c0d4507090042c0c001e1400803401c08270400e003010540c0000b0304071b00d44013000300c1d041c18034010b44410101d100d40ca01454407000b82591020040c400c80c0c20003c03149d9140d0f038020040c07407408208540383e01d0f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 980102221 1250 980100971 980100973
    0x140c0303120408090f09070c0302010b0312040b0a030b060f0702211b01020c1302040e0912030a090201031d06040317010f06050715060e071d0a03030e0a03080a051323010f02 76
    0x840f117085a5140a000350091840f501c03500300702946824002d0a42d0000a04079000351b100100321407145506508803808c445060319195220080034104030080c00890744c1507913012402190703e103102d5103008010209030b8800c60340c42d1008111211601d40c0303c8101c0103003a28680040c01040400d150000705100000d1052060314078081001000520082d80c1c0003058580a9020809008190b20400c10a41100d9107100900c0300301c81d17410800c009440300034440201c96807680011021a402900411039000c413040750343c540e84481c03070010741e81c2d040129400e4002600e00910002d040e195134054034142d03210314016130240e074182801170b115613014a40403906a00c0da0001078521401d02d106a0001c0c11866181901038100000b00500801030304200001e03000301448200301e50b0b511002c901084941c14202080e240440034006112800a035202a1000c0c00009000c040c042d4090010000030650990703a40b600754862290000001178203060b8004181680ea0600a45d8001c12a0ba1807400b00f0344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 980103471 1250 980102221 980102239
    0x3160314070906110730051207020108100302090105061c051f0e0c1e090d051006080a0510151e06080108031903021602030604140c030312040809 64
    0x99080d45222004855200c00101e00307900c24014190300040005040c4014001400c600342000c0c0740313401400e080740c4080b0861180b02d019a00303801c040c101e4280305a40103000c0e10b0255890b000f1900c081c1c0d104000803400103011a00280450b100d2041c503a007504c0e006441251103a00340ba051100342d510901e41203101041c42c00c40d1600380d401c140038080c0300b8900c01c000101840504d0110041050143c0c01108407803000c4000c00c000140ea403004d0f140710381e090903800050f580e450f20810303e2a2203a110700541064402035400c0a002d40020302a42c1d0295030301c8100040c643e50390b0f15585682c202c1c1c900a01c20340140e51a2040100c02e500952813060180354003000583c0d540b6200700b00d00306d003104400d01e42e11502c0070070001550000d5400b4010254407002d98500544100c21060910200e180d9505155002c02e020a082e00714110104500e80e0160455140e0b007841d0500c0c0c02540d100011a00c1d0328070070f811111545080200a1700c1c0313268401c60a44250e51225541c45505370000d82100b1341000850b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 980104721 1250 980103471 980103491
    0xa140a230d1817010b01021908031b040905070807021b0f04020d022101080105060d03020604020d0302070f06091503020a1d1305040311010f0e1504061401180e0a0305031603 76
    0x1110f004041ca861034400000c61500c002d00190403c1e2007201c0d04440040360b80c803054042141c0c03004999200a03948101c10b40c00300c801c0c0180da054012600800b03c820316100c1080903081e00030318264050340c215001c07a0041c40c401a882c07082c00b00103074800c035040500392080031010308058000d01090308185030094280200c1a0200c00251180c8035070841d441380d14030040280250a208094010310141e401d00b040c1c2c030040d10080c1da5201c02400080c028081171503c40141442404001c1c00b82c0111114140b5055542200800044290194580b80c503c080d80c04000315000b03200f124000c14860301c51110305040d110040301d008007202000364000d11350b003020342104110361041e10302ca00e210341c90f41460f41d4080d00c201030840351140d02d0f00c480e08cc5080403806485900286541d01007100c920715441c603581e5898040041d200c298006503910703a00d80d0000c52034081d40c100e10700c0409605201041424044140e1603604e41a060010340030600820100342d81030494080000c0301109800e02240b900c2d92 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 980105971 1250 980104721 980104739
    0x1115040b0906042c07081e04030c0818190602071206020c0105010b0d05090a0221010b0d030c0b10060e0409020d0c140a050a03051902030a140a230d18 66
    0x20b00d000313405810400c4c00e0b00125108002899070030044a161100d61854004140780c12090542c20000b40701d0040000542018800c0c1c40c42008a0b030b01c8050141c40f002e021201007142c0103c10300d201d100f184010b080b01004441858072908641c407503801044070390700d0420300007406d02c0c58001c140c400c940c00708150080c0c8a002d004290080a13281e103000da03103100440218046480151100110381c1052040b01c0c050380c0c450069a4601c0c500c400c1d40e00031544a11040f60041c000c1c090307110341080d04404a1014550001040c01c0c0d580d018180b00c1016588942002c21000d10600941340440c0c0030383e1469407942050751014124078400340c586a444105c81d01e5252019a01ea2b200100075080081c00005904212390340300000c14094441801c000d046030303140ca42f2134000d502542c40f000c5a0070200d109664042200703060942d080f02c841201010a415520b440348480c0c001902c00005c03070165400440d580744140c0c003070950001c005e40b10305a00c0c000d01321070000701d0617646c100410442c10080782a00e8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 980107221 1250 980105971 980105999
    0x501020c0928020f03060a0501030218090a0207050a05070305060c0a0215040305270a06030b0d0204022113050106120807060e070504020f0d05060a031e0303110a0c1115040b090604 79
    0x840c1110f916846c000b03003007111004440d0801e80c1010700612986e01c1c604003056801c40313080030850b40340103e030740d5080b5084028000d82074060315a00c1207400580502002051b00c070b01342c81c0110180c44460380c0e07100c0c0704407552142501c07580040c1e0004481c0d0f03190401031050250064401c0c9402403401040f11018000030036941700300121055103c503a406286030000c1750a00034405800e050103402e110400040000d04800d00203402142c0000d03d5000104680110301000110003119040b85d0404000319691655261703000c840f071358030308280171801d4040d010114403015401903030103103004d2141d51948040c00c0e1040c0740315203a01c20304401180301c2d41c0e1400a0325070240100311351900c601394055420162a400340c0410b00034450b200092000c202000081001048014050b5002d003610345002c40052424a90030309800c07502264130481e41c2c0d030018061410300c0c0144100070102e0030b10020489034000b104a0f11000c47d90400c0100040000c1501800e0084401003d860415607503001e9030301084 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 980108471 1250 980107221 980107237
    0x1401050904141f06140310090608030304140118110102010e0118230d1107030c091a040606120902150a05040611160b07050a0614100501020c092802 65
    0xa00d039502084004500b9003901c103030340d242c681e200b940f01614001002d080425044101c0c5e205000000000340c44041c003051203001841d21000070040d00380e58118a07038072a00240c40860318842c21602030044080140141d401800d135240c00910301e5680b03561001038001840322120706554950050001e042002e108840004c7c01400000700b10100e03e25002e089c0e41b01d51041280032445814509120300c3e0001130103081c80c1d50701d08284103e4a0081062403a00329140e1000700b1004400402241e0032240d5001980c07480f08040030002982d003481c04100c143c500300d0041c440010342100d4460400c250325002011014005031041c1c85800070500b018200380c2c00030030110081440041c1c2003000139481018036001c00c8482018241054100d0702c0000b41000d41c1c89400c000010115918003405420b01090000c2ca44c002e00402201230092090a000758040303170240503560368014002540c0d400400c083c00401002041c6003070b81c0d0b48142d214242c2181c204964100381017035000d01020990300b840140368203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 980109721 1250 980108471 980108501
    0x7030518100237080601020312070e100203090f0609180103110109061805061b030c010e0105281a060d020405150f0304140f150906130803011401050904 67
    0x40c00807a030f01045a0645028440300f0400314011003050303160300200b0a6202c5524502002540c0b900d00040745140142c42d042d404520a5005106c10650840d94040039850266100b10480c140000103903200d005800f0201d412862040c00325665151400050042ca0380c01803084251240c0100c11a036561000d8008032001014284410341355a000b0382050001c2c403546c60000301012958007031000c0c00a0794482c460007000d0201707114498800e010700c801100c1c1d80c0740003165114803103aa419070103040e0000c001e0303889501e4800811401d85201170007081c461038001078605030150000c170035001080c0c5031070b18401100e20282d014103155074400041088000a1a0160312542001c0030003180309281c0e01e0403130240800304040704602190f0f000fa66071003504600180100400c0c101054144000200a000240030b02d2444460801c1580c0205004041210071246965503002c03980054079069400a00564024001081692444083c5164142c0107250550808148100ac1341c19079091111039241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 980110971 1250 980109721 980109727
    0x4020310090b18070b041203030b150901030c08070f1404030c260a0209040308090c0303040b0d051303020c10030b06030c0c0c040b010e010e0f060c030a020d0c0b070305181002 77
    0x60f104011841062640a4014050281c078003c4002c00500c124800c24002e00c00345550b007014503019a0011900c0080a0504101c03c2c407a002c41d541c00ba40142107084c003080c40c1483d4450681d1269207403a1255020380c68024600d0480c4601b9036000034010000c2901107003c100110014512942c00c030300422100d0360745200080d864402410011102c510101c3e5035007c4050000940c0d00c0c082d40640080d05070900401d5030f15a0002d00e82425402c40c591600341c840040c00042c00c103c0c0400600403691099801c0040e92168101030010030012540980103074000d40d0300801d03616004103580b0140c00c440c100007540150320004181140c004880e09103480c540811100c240403418401c002265070704440c2004018141000a000d110256042c28100f01101c90701600d0340c4c0390800d1282d40c140e8020500380c0c1b6414142840c9643c0d9000710790b01c8006004466001d40c2043c09490626216540240480c0d0b0a039142c00040b0000c1070000e000c00b0203480c4143c80744108060034065084042040e500251b5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 980112221 1250 980110971 980110981
    0x60e060112150605031305070e1e010b04030602030c1315080c0901090e0c0c030c07060e091b0f04120507080106061b0b0a0b1906080a0203010b090904020310090b 71
    0x44100c644510201d85282003202410308681d068102006469450034400d490341c60709030b0809845207043d0001000d512800c0004501001c0348104281300d10540d48008841c14920900002156001e1282d0170720301c02e0501081c0000b5020360042c540c003400a82155043c10200d80c802c2c4040c014590200c41031000d0581115030f4180d01c61415980310044240d09072800141c1d00000b000440b507481200d11901918010543c801c06840461300d81e020341d641125242c00c4d0300700e0041c3c0c51b154bc1e849002c01107420b892440c01541414049107110300a034000b0b1074400702140001c001c040d1720800400450a10401006c0381080781060001c40b41c42c000c034000e140140c20000902e00710780b1203800c10400d0100c40b4010484400c25281c14020040d4082400d1145423108411000506108000307664040c60354003401a034901c40d00241c10031902a5a6850025111042103100b00d00c02070040c03107015501004202006c0c2041241d840d0800e1000d000c0710000031141000000b101d00115089596548c048140302d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 980113471 1250 980112221 980112227
    0x50a020c06250311031801060803180f12060403081f080a12030e030a1b020a15030b06031312090b041e0f08070303201b040f0b0108060d0203010906060e0601 69
    0x100c00d400509041203500b0080034460744d0390200800d04203030b0500513450402c55000c20740142c80240b80081c226a04c40030507034031841c1c500d20003400d600d00a00500c0c00d012120700c1d04800e5180181000409002c00303489584080380c09880081103101511041400503074145c0d8440c508000914050000c1c0481a1240c58103d00f0030700b0b04c03442e5808150500d4402610303001c0202c210b40544545041c00101841c4441508101c1d10510780040d50180c07079090001004800444d100d82c4528095808100e01050581049032a0006442c0511014000c03800540011280c07170040911110508040c4100c6580d41c03482003d961090700036076112401664900c1c001c502c0801007001800324500e480720341e54103140589941d612240301c040c080041e0740c1c41481c1254011340c114800300c1e540c0c0060322500e03840c0d143c0e080218000641403030702803032400e0410030f0b1612541c8980b0148040c140d50300b8003180c54400c10480e0342d0844030410b03a41075581d400780300002152845040c0040000101262013850060009 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 980114721 1250 980113471 980113531
    0x140c01180602300127020406050c1507120c0c0b0c18090f16111204060e0904023f010615080103030504050d0606050306280603080409050a020c06 64
    0xb19140008049070304014940801c0c1213410368205400b03030800240d01c400c0c000700c006544040403103034510010b40401d80f1540b050040401d242100112203450840c140400d501410444114000601c2e0b400c158003450a1500b000ca401e143e5494003e1182580380c44000e17181c0e4068824849201303001441c2000c03130708680340044080c83c00315501800e0348ad200040394046980200701207500140000425449800744100c0109603038620200e44040c0303090700031280660b100b0b020b0080131564604980d082450542c064901c03695028110399405a0f01d0000006178440c10700c408c036035a20309105414011050300c01c128000f90401800400c41c2890032007040c16401e4002007040421254000510101350001c041fa400c907001561150070a4601c0d042480c02010140c0000c1c1d4140540c0d401d21880721a000c800c107200035407091010075044040005401180c840d440001c182c081c05200410079201d1541c041c40d8002c3c203500c2c015140a130004145030500780100e551003025070851005030034560074801d030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 980115971 1250 980114721 980114767
    0xf051509030d0c140714060a1b0501050f0f0103050a1205220e06030c0901060c0c05060d0f0e0c0f061b01020c0307120c02010e0d060914071e0501140c01180602 70
    0x31704816803c02002240050000c109a0f014000c00104082402d1140b0804022209505100313810001246846d9010340b0069482ca0035619040700800c0282c1e00700862541200d40c0b1400400441c03d00b551a02c0111707000d822207909014080c0700d48000480307640c03071101d451440510000400d50a00c11341510011011342928000d40c01165003032020b86a402e88107064402c64100240d01a5052901c1c0300300306015001150810000304050741006010740140c20b403030480203000e0001c6800204404e96405d0480d4170140d001c2c800c1070321480c2e2404d105008085a09814140000c0d84400d40742882c2681e10051820603943c0c00012203009000e41011060344101e00780c9804400c803903564000a054401d101c1801d841440d17a480480300f0040c0c01e41c818840a540310b030380301900110032080300b42c0f155118801c9101210904214202e09071004041070241c40058489044124035144250015040002001210740d0b8076200c0f020140c0c8a40d0000c42003912900c005aa2190328048c0e102e0940756042c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980117221 1250 980115971 980115973
    0x91006091d1b0c0a060204260d143028020a020109050607021c110607050903030706180c090513061104050405010312030c08010f051509030d0c14 64
    0x320071503814850604468008188001c01c0b82d212050100d849070900c2140704920040c4201c0c1000c0040042c2da030050800c8071420b61080854441c1100d44414459041000030007981003242e1594455002d0000400a0302d54014003c2c00d1000a85140c0a001107100c034980c501034a0307548a4802c0303650b0340821540f1036030103140b200c12000d0070075184408810080314201140d8001c2041e5100798400d5201038007464000044448078101454007940f0b400c40030303400c6101d00090312000c41c00103000d82d612220030820701e8000c0ca541d544550701218507070060a504d66160100f0000c00011400134001c180780705c0d00c440e0b1141c04914251600c0ea0a03140d1035070087d40c28604000400c96078180c80795900710811703048400030440d140307580c928140f5072040c1d400440d48185408004014051156034580700d09000e510f080000b0340384c240054648280903c1041008001501c060016081a212540128614401c240d081c170b9000c0c40060f05001c8160b20810000c1c056900079814000144089114054120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 980118471 1250 980117221 980117249
    0x50705060a05180f041b020f010e0316111003140a0c05030402090a0608010207060b031002040f0b0a0302041703071704140f0303120103150b0906011b060b09100609 72
    0x203600a070450140c00e210b415204442114240c0903284c10591510f00c4400810421229440d2205410140e850502407801441050078074094404148900e0611900800046092a51120040507200c4901408503560340f03140005000302d85a140703400343c2d20f4600782c5000c00d10700a101919100082c1c02454030803003500300765540805907000001c8a422030380603101d10185a550b95814806442240d1102c14190b20016a034404d12100354004410043c084080d9200390106076107031010390056005040c101315080b00d0070001d400000c00104420760490502600b010350302d09103402c102c20650409000c54000282e0b0000b0025603541e1802090106035020b810203007080c843c1c0005207035411380d00340281441d045d001c2e0740f41d604109480c2c0e4111f1168039a8035a41c1c603031902c6000d100e030440800e0036040c107102c100c5000d480c1092007188501070680d5500c81c0d5002d1410b284108541c080f109a03180703580d5508510140c1ca420215512680d03822651b040c4541c908480102800519400407807002418 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 980119721 1250 980118471 980118487
    0x70309090b0f010c110102010b0619090b0f0406050a030905030a0905012c040b0d06050403032306030c010804061401061806020c03071e0b0403030815011d06030a20030405070506 78
    0x21600c0c2c040340703405c0400f40040510141c0141c1c010244040c5440d8440d00110b03034507a2001c0103107a80d2200210f03942c0c0d902c45455a440c088000c602501811034040e0340300384400e1181ca407141015140060780c3d0318011400e221561109030841d80040800340008050007024001940c202e007542552a903d07480390021282841c0d03649001c07c0c8560310740c40c400c58a07040400856501c44600b4400250081403c0045040510303000e40109041240c420251503050740d00e043d05250300d14100d10845002d00580b0303600e65450011256600c0040048441503601c0c03041c075915801d601a181d01801c030300c1d168095166000c100030740c44a00390f90b00c84801c5510580d0b6840e299240071800d40200c9019503c0c40410820f9030640300e80079815508020014200824008285a48001c8003401208401d01c00f80700404000011a0041c0c03ca070301c2038030401118144141c0c1820040000c640c042000c604c0015880102c05e514051070501b02d460b1040e15001106100034460144004401004120f503250324040c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 980120971 1250 980119721 980119727
    0x10207170901021c023a090f060c030c05060405010509121e0d020712020102180f060a0e15180f040e0d080a0609050a0207060501050108280b0402070309090b0f01 71
    0x318160707248503041340c0610140c1c46000f000301e1403c0703010000f0994080c050580207020b00c10045040d440c14498803108080b8a40d00601265080c1d52800600040c1d05007090403e0714040c0170007104800b00a16005d190020400a00c82c2d540107910640000c200c03030400b02ca5141c5014200305400c5660382080082d55007078401106d00000c0c01081480030343d160b505841d1020024018054040c010546000241c031156030306500030865440e02c01d002100902c107020074000c0c02c04040003240d41014040011074411409030b0290500220001c01403d1510040d80e061419500f011034100000c0450000050302d600d881081003401c20020341d4200103015601a080d41c2e158060b900c0c820600542c0b1010030905c08168004c400617107416030b030a100c241007468295000303520010050741e1103460000081030a6203e41403442c028020a2000006644070111036951107145458040010740d903615215000d03111800984600d50081e111174003417626192440c02520541007240340f0807810289030311941c5e07170 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 980122221 1250 980120971 980120983
    0x1050a080706120e0105010807031a040305030708150a0603150b03060f101106010311030d0216051306030c0902090310060308191106100807060503060d0303200c01020717090102 78
    0x542460444811802c1081510044c01d0000c0ca8140135402c00c000840c02580000f0003070100c3e48103505000016034012141c9103160030586004000031800c06c04075280c584503214040e00101d0580744c030400c80701000c0001d0803102c41607012101181c0c5400400592500d00c100d00b900510942e18070500c1c61914100084681980c043c10394070803d0b10381c1c0141100303482100111174284501c002c581841d40c490800007030504005100a201e4880c04104024240c40803507851a5802851112080c95091904010324810f04030321001009559220010200e0850b00d09680148816440160b548250006050401c8200c43e01c00c81c000b070920303000f000011565011141001c0d501000300090031880c90b411107484030003502c10001d51180f0414070510445003002101111041000c4602c515035890b415200c900040f20240c0c2d01401482c4400f0100c0c0c0a9001180800400c50b0503c1e508201a503007201c668203c80c80704d04003a0f5002c1804010031203a4a00081d1052070001014180000c01c4c00003580c1e04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 980123471 1250 980122221 980122229
    0xa030609080c0a030c02120c010207030b0a0e010f05010503070f0308040b0306040e0f0d0e031209040c18030c061d0913080d14090d09030507031113020c0f0601050a0807 74
    0x35520031080c800c0c03080c0403095a09a840c00b00c10f44042c0e0b003060030300911205c07210f40c0a9201e0311280b4580c4180e10030020300001540e00c1030700500785151854072064160b5500034448440c40c1d8480078a501849428815040884514180046d041d4100024540741140382d401403100400007100c18004601c0f00003c0d1030440d00e1610394a5a6599400d01080240c50511124200b40c03003042502c60b110400030400d129104500d40c0c50f240c1c4096800100756558010030804903e09004100800c080d0a26803c403900c11400c1d03040c0400060b03001721851119070030940c001d4612511120041c010558042c10085e424012185e4460b96045c003d00024083c41000e80820884030f004a00e0030100072100c82600c0e0b050b035003007904004400155241e07103030700003007281c04040b00d014140441c448107006480d0f413401d80c0d8005000f0f0800d0b500b10b42d40c28140300d8070101500d90150072190384c60000d40090000780904c02410001e0801c40e40c0c1f08100b00e02c2c010068110502c5040080d0f028810768030b0001d04a000c40b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 980124721 1250 980123471 980123483
    0x100f110c15130312150e0a1a0301110405040f09020306010617070801051c020109150c0215070f020904031421100513020a0528020609060606040905041e140106060c020a03 75
    0x1c190721540c1c505c0e0b403c0e40d025829a41010302000708500d02607100580f48200f00c2c1b00700c00c0c59054142054221048001c090501d1142800144180d0400d5405140c8d1244036a40024201744540c0019107400e074260320003000100710581114480500c01c04031a00802603041c4450203504007800110410094540000030b1100e00b01e910f825607200d404460300074600801c907909000803406008254058812003030740569404610075500d1510003040300d001e036030010300907030020099908101b4044e801405c242c08110660706005d0b0072158501c010b003165543c2e1036002c520081c2c0410024400d01d40201144000c3d4180c030801c20060b00c55540b034010941d01241e0060340d0304000e510560700b90241ea01c0d945510380701c445005e401407008024010640c00e83d5001c5605907070b6841045a51400121405034015400740300402000202d82c2000d6041032092405401020035104162a0840030fa04c059400d8245100c911941c5242841101c02620140c54181c01a03d41a0042a035007140351200420b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 980125971 1250 980124721 980124731
    0x230a0e0f0c01081b07060609020405120a0b040f230105190b09010618170f150c12060a050303070f02090c040302150d0219020a0203070b030603100f110c15130312 71
    0x104c40c0c80e40044407500c2d0ba100c8410418161559511b60080d00030340140350180d0004a481041113a000488412182c0e00c44400c0b002ca550302e50f5042c0801c400410101d500100314066101c00703220030f04035010841c0760700d400040c40c0c4c0342211400704190002070520712031929143c4000169103801c0102030545000b800d001d42d400c04240700c0d06500d01d14551050304410405203008072851400715008003402c0c072820403504150019000b11100c64820b5480c1e80c201807042042003003040301e03503100e254130260083c807152916681e840800d0039607001c1003044980651030102c100861424081043d00050082c220700d0601c0e007150f0206030301c41c441c800304040403940070810300000e54954040314030403079400c919450a403d5014003c0d5135904000c0080b8845d000c0c4ea100410310840c040c00b602d02c100802070040c03071110701c201c0c0f54000134681d41e840080342d980c450310300c0000c011407034000b4035896003444020180700c800952035500018014040d05c1c46138100e8920074001c81c5e071090314051903c1c040040011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 980127221 1250 980125971 980126011
    0x50403170f0f07111e0d03060b04120501061214070b0406020a02120c030d05040f0b07030f080603011113090b0414040b1e280b0112230a0e0f0c0108 65
    0x2801c510404c20105544101210700c46182e80c11100702e48481c002d88215491410580d0040d0180d803110300411040b11820b0104114007903000c500319805500520002800d1501c0e500142c0c0c4440d800101542d50b880124400340e0494000c0020a00525041008608140c02e080000303490b0040080040d110700c140b5902049203200034000c461501c0801400c50b030114519545c041c1141d00540f240d098074562404000600ca111a01125500d5901d51764032085e0fa00d0680c42900d2021018010941566a8514074080f0101070802002d44a108240b441003d41c40d0101501c1564400310300790b030087c0d0500300c4c0b03403800c12000940d41d40c10aa00c41d1f201480f542d030350140c4500840d082c1c0000390b2040003100034032070305800c601752440c4101e84101903111119412554101940d580408190001d0610381c00824101e00759403013580390210309440c0c2581c8012103118050700401c180c2c0d80c80d40741b950b0b40300e5501100200704600c1054110010251048046100c0060308000000b002c0c08400703111030041507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 980128471 1250 980127221 980127227
    0xc052518021902150106031404020121050a0605121207110105071a1006020a0510051302031e0607140405040b18090a05121216020c090a050403170f0f07 67
    0x740885003625461000451180b400035503640a07040030030003041c001c100109074103100b80200010b1500e0303402c085201c1c0e1201d50044401e85800c40390b00a80c41c91100051643d80312600415000742403051001c0b5105080c8000c100200354003003e8484d83e903011080082c01100d11400313407036200b03400c8100d052883c1000e00040e5400e1203000001420400b581c100340e00c00100242e0414090041c4ca84000300090310380b8410790313803818500300151285e07211098040b03c0d686590045580202c030310b80c141122128541c0800d1070500d01d84a101d064107500082d139100c0340010403025502c80424a8040c031940c1c058000d50700703e84218001c031402240c41d03502c1300809031154840964000e00d542c1103a0b45a00c0c1080501d500d401d03030f481c0e04031810f020f034040d15003411003064240c59030441500e030b030101c803500c0300520340d01800e940701742808c103500541311040e40b00d82c0d0309034401e0b100705441e00b00402d180c03609140040c1402502103002040355032400910070503454000d41c080d03100881c000180700726202c1c45415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 980129721 1250 980128471 980128477
    0x92107051525031415040e1002031918080304020312030a020c0c060319180c0b0a0801080a0809220507121109033301060c05251802 58
    0x2803100d400c40d01052000d8219020380c1c002071000c0007004032a011041034000c90650321156501c1c40404030b000c000c14201c4070800c030740170030220000f0030015543c03c06071680da08200d00c0451103044241c1c08003c001172280001c200359822410408104411401400e00302071414015201400a03500400082c0854404200014410804840c40341c0c8130710304968544c020754450b0b050071940b4061090806014100542074a01501c5c410004510b150f0041c816600100111903002c40c3c0e0018950700c2c013001c03070101550080a00132840347c9a6454000400260041c0c1c0c06910080d403aa000403002000703d400d450607034080000448203640005d041c101007031509101e4486200c4101c1c9058180610301c0c0e003040c004000305003085810f009400400c08401514010011503a8054100b10003110044803101081100c05100741c10b1307002c1c4050303140c1c00400144c0d0240c1080000c00c0c2000d10040c2409820408021800500920f1448006a004c6020101d540500c02c29500502c42e202d0031aaa403007035015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 980130971 1250 980129721 980129743
    0x12171b0a1824030b1503060d03050f0d0506151903020319060b030105010311040f120302030c060412121a121e030a09080d0906080c070b0906010e09210705 68
    0x207050030b40e008450740c070700d008628422100400e207014940040e42c14980d0003804112045404241541d03503403c140250919610401c4007004010002440284960300240c8004d0700000c4c0e0015070b40c9010b000780000410800100310b0701391000c2c440c0c0c000c44d2081c0f11a0800c100010315025891383c176810b4500c003044044225000c1030703d00782a00440d450300c1043c00765048034001d98080c850051009040c50042c49075002d4428260301200b014411100da40031402c0c4128420b10441c1d00d0550040d1443d1704141301640c08840108038180c0c6a00e003203174001d00100302040c1040040044c04041405c0031102420400b402c0d02528141c040002d181c0d400b44400400c8000290705800d14250704000651240c1c450003011010942d40c013030100c0d50f41c00010b1010007499040e11001d41a90505806460240c0d000300b502c0c120b000204000e8000401034801c039805041d07143d0080c2025410610603075031840008100c0f103c19403200100510b41401e000074140070b000d001055541e24841d60804074240300d00140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 980132221 1250 980130971 980130989
    0x40f0609240b010c1703040305090603010b090f04051311011b060b150a020d12020715020a110f15061807080403020d182112171b0a18 59
    0x5508501c80d191040c2009640c4944900704500b100e001d0041d2107000181501400030b8903960440390071000700000464020703000c0d00702076040404000014180c0e0b40309801108829501013000062800c01d00700803402c0c4032040300d05112900d80351005025881c0c1d49500601440c80d40f0204100036401540c10000c1001c65490003082c103905820b240018042250610b0f0260205a442703131403800703005082d43d0403071203568050001032441420894191504290000003184d0800c441c8000075880310406101e010b4051000d621180b04100280074060304901c010f17a580c000c58010504950080789200120042d41041080d94032594003045400d101c0e0044500f0104085003800340282d08000c40a106922035400c030703100c240c41403a049692001404a5600c0c840c5080d0040c00f0b00214040d8007030300114008456072000302d030f41d1620544034588001c0a404551300b000d1803540104810303a000d9009095010030203991308030403209251403040c0250712003080703c00e40340c244a40300b0403182100105030b054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 980133471 1250 980132221 980132243
    0x50c1213210509011b020a03080c0c06120708070903080a050c010e0f07051908060145060902070b060d050a1407050427021003090209310b040f0609 65
    0x808082d29690100010030301003030014100c03ca01c0c1040340840703d08a0f40c00742400400c5891a540e0340010f4101d440c1c5031f0650b0040380a410f0b00364880f5005400c440101c420381c25640c1c00e005001500120b0041c1201042080441c0c00340085881e403c00c580110f440d625115030b03a0064507070000e00601e20020000c8441c012007040c0c01d0202c4000800800740c4404483c2c600704040b030440081d400f40c3d0300d803107040380c0c0341c003e07500400060486040140c1c04682c0c0c14801d42003280300d03d900708a02241403203c10b0305c00c158104900c2e401c030301c1e5100b03810190005a80842c034060380760307c404d4000100140136070310490034850481d040203420300010701d045a200c50b02e400260310780314005d601d07980d56018030741c019840e141d201c0341101c05000d00025162a00038002110301050380a0003440700b00c0c2c058038414180c60b02a0f08005071030b1041d45920920200e1042c0352001007604038038004820700704941c131166a00b14109404030300016000e5410070f500440f041c0c01e8541c5440d015014081c03001000c1c00608200b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 980134721 1250 980133471 980133533
    0x70b0703232a130e10030308071403100f0b0906220f030b010503100b100c030908070602030d0b060309060a0906090206070503030619060906030f0e0708030a03050c1213 74
    0xc4043c0c006685000d0300d039640a0b071201d2a112500e4000c42d604001c210700402c0c20004030b8001d80c80660031000904c0c06030303210060514058100d6006640e00348008509030b800700710128501420802a00320009043d15004800b400603416000c0c8428150300d1000a00c084049400c6480281009101506d420302140b65a03003030003148603900f441654080c0c0a502a2660003080600c5466840003004150503041000d1503400c65450302c1c100412002e01031507407004105001e04001c0c610080c030700350780103603a15170400103000b040d540c06014540c00fa490a00074441c070902c01040299200c220701400003456a0a42000c90103803032807480194000000050040c18010044019407080205450340c81506008a1400c2d10100b224810740300000c0c2440024010144207030032400100940e007101040d401640164542460360941c001100c980c00001c0c0d001e601509409510303800812601424200320005150004030b00001784642031124100840c40100000702ca590344a604004400c02601041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 980135971 1250 980134721 980134801
    0xd17190c050c010b19140d0519031b08090108090c1c0614010e070c0f0212030306120706022d101a0d020607060c0c08030408070b070323 60
    0xc00182c4580d404d000840714141817540c01203c0c261440952003108600c0c001c0c80101690700400708540c091740e881c035443c000c030720f0400c10200b2034445030644910816440c0381c09011861072581c00e690080e05011110046901d034000d940c82d4074001e0802400316a00d04d40071500f0000c8810030b1176448407003002166154000d240c0050b4116200740000c2162000c004820f809001d0300744942c0008621400c00a01381c80d00c1010b1300c0442c140310304101c4030324422550004002091501603480c90707600100804c2881e1522088a0f042ea0f8101b40142455509241000f51125490030f0804581c8003c45c001c0d0000f596100328155a00b21000e054654102e003810228015002c0404a96507224081418580070f01d004689880c002e64010301103480c00c02c807507a81c100074081d640400d005000100bc0c2060100c0c40490003944100d02c249030b100d58a5a0515020748081406007401c0101844c1c40100c3c03d40440403685080d914111010755040c680d58405003211602070007030301020541c0894559040014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 980137221 1250 980135971 980135977
    0x10c0606140f061305011803050a05010f0c0503040c1a0f0d090c091112090717030a09060305040b0414030d0606090305100903050f0d02040e07050c0105090d17190c05 73
    0x303021198220b0b0009080100401c0b400f400e580008003c0c04044100042d6006603280f441d40304240422a69059a903110541400c5020342e007034525035190b809102d0036803c02c0c45040c0c410307c01e900300307a41581000d440e050307488641e6011743d01c050034041100350713a030300c247c002614503aa00390a402d0b5075454454482101400d806002180c40740c85845003c03c00100a0060551509180d041c2c00d041c0042c1108182d410301004d801c9001900a440c4003207180a8007800c40750880131804015980d940b150701d0020103240b46903110800305482c103000d000016608060032500542c0007498072205010104046007544941031103a00001d180420005915412080c6801103074026015915210001a400d80c140c03400b0100c020005103003003100c109803c0c0b1200190801d1590244014141760b100d45980000c10f1058502c01c012072400f00d501403141000340207240d4084d24050241101d000c0610000c3c03c82e19200040312002c0344120f0001d5040800441d465a60f005420024004400c0f00726028246074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 980138471 1250 980137221 980137259
    0x203013807030f0e01110d0c0c0e041b080d12022118070b03060102210f0d0b190b180102340807031502070201051201090b040e1218010c0606 62
    0x50013602c1d0b0600316600540840400c142c48001401c4040074888084410584880d011217003421001000304110030203890f02c0b232189102d03c10424000001804540050b94590b02c4083c043c1e000d04c107100b00541e480341800020b03941c110409078584a50482103000340108040703c0d60410000001c02c10700791518001d0101011031207041d03810712130b15100c00c1303036031840112400382c05a032090718200c00f82045207039042c00140c4a484050f0a2060000c4610b00a030720100c01c0c2e854294071a24117072920b10706003c4070a100b003c030184641c5000d140c059102081d000c3e10480c0440e850208040840d107034000e11a441d116034412492091940b018420850070880c4a0703000300c80300384003040c040380c3c44d030000070f1040c1079a8100241d83e0394401041d4030417002c0c0d4080e010403410041c085c803840e25038100c1c00201d640070304000c81021a030b21441c03906101c1103074120880c440050748200594118948402c0c00c648810240750308030f1980110030300c0181c03030004040000a00f010310380700c0c000800307240c1030750600d04403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 980139721 1250 980138471 980138477
    0xe07032301060f05031605070c0b04062307020d020f0402070c0306020310150210020a0e04091a06010512060d0606170a0b0f010e0a0c020111040b0d0507030203013807030f 75
    0x7070301015000b104c040c04100d41c60b031401950380c40582c1d415030003600070749140d03407140301492440d64a0b003e017113160b50490750160010900030411030b400c41e513300c00c40c03c02c018640c07041c01d07050406540000d924039461860182c051002c4111081d11500c81d90112042e07182c00c100c480d04210750340e02e419002548216445107110300c8083c00407800c08407061040e04681010780c01061807614066190000307500c484600c000340058040e4201268070323a4050360f0300c0540585516072054000b8048401380c440010090b41c100241000b0310382a40740801f901c01d42020040d902c16074070980f40d1400384010304458200f0089000d80c0e82c0440c020f04400600010f61030b100e400080101c3c1c03100d02c0040c1100340c00b0b02516032568000800100c0c04200c0d603001085101c25071001040e040b146000500b020b41c800e0b00001c40c0460000f07003900c18441d01e402910340100310303450114555031610440b0b41c3d40000b0740311540c50140c10702c070100e40c3d050001e6280c400c054442100040c2c4c0c0368402d1601605400c8008058808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 980140971 1250 980139721 980139737
    0x30f04140d0210030c1b0812010b0a05040303180806040b18010203040206180d0b0915161709100f0501031e050316050f03070b0f01140a0e0703230106 66
    0x185007840381c00c0044059020b0301c1d80e003504841490650281640012203410404443c0362100381d02d01c0741080c0c0202e54000d03a1200d955906580818240d01c5058021440400301080703541801e40e03100d4103d4040f2509480c0c4100301c009109810f046800c1d480e8003090a61141006101c00e00c1060140180541701a0703a4140e80115512101380c240d0108480c042d40c400c409015a003518040c2c1c00f07018454100003040024003508555603481d901301c00340da1540c40c030360140741481b407008200340b200c5401000000c521000e1600c0280014919540100ba802c0741c5001e19021458003c010401c040f5903a815032000d0050103a5100721a000f440c0034401a10500944070381c20354805040d0046c56030706600280910315181107407180f100c114450202c22a1548907a50b020105400300340054814944104521400f078104014221000c80041c0c1003466135504505189249507100342c00041141c1072452140165034030744030306500400c103100000ba405040c0341d40061780050220019816118540c0311840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 980142221 1250 980140971 980141009
    0x7080d0c02071d061e040e010b0414041e0c090c0203120f100e060d0506090106030303050106111f092102191106030417040602011b080f06150c030f04 66
    0x400d41c801100440c3c0c14400140840e10700d00348084001941c40340c00800048071050780d4085000c80f450f11f200000f159541d40e16410703980c605405401c80b0414500822007031410315403600038201e05440403450101d0324a1107280e00308854840c007000103141010b42004900f01c10305002e912540a49d12200c024513240300003604450320302c506203000d14150320b400c8800c50704107503030880d02800143c11683c1c080d01030f5143c1ca000034810091180700e0b402d868000b1902d1031441c60f02905882040c0c1104050040ba0081c4150600d0002441d081001501e0740001520396100e10382c02c01001d0300c803405019120304c1c49907001054510b11050b440d064141c2e00b03c9140503105020200b03202c2400100030208014218a0071040ca03001c0051508113006910b030650070200c0c807500d00305c0b070b80c096401440940d45551455610310035001d00800258a1802c1601541c41e010750304160f2004002c01e82480341c0042c80c48a600700c1480e0302510701c40b42400c3e01302c9a4500740820001a1500240315083c40c024031029910 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 980143471 1250 980142221 980142239
    0x8071814090c130f0f0b1002010b06220315090b010b03060a0e100f030b18010b01080f090c19140409050c0d030c0501050103060c0f03141302030307080d0c0207 70
    0x1610841901002d007403018800010400b520908203100625683c0310189008a40350500c2030020b070309071450000511000c80c070240107280c500e00c440d0a06592601c00450b00644440c001c486000094080480c5001c1e561145510905003d1700068060300b0703843c1c01c210100c680b5a0040349554011895118940e0b81c130340e40030038944000c60f070580d080044840e040100354090031519411405404c80d0744202074480d0941c0b101001d05600980d80368035807030b050014009440c0002501d00351000000c1c01105980000600700f650301410b214107000c8240c0014114150a2107a1074583d43c00811000c4100c1280d000d030482241540030307244540804401c3e4008500e0f180c0701d162005035002000e0280f544c0601e00b00709015805400a0342440411400000010028490140614800c1e980000c01111450004141c45c5001144130203140c50301001c0701010b22010406684410010140300b6403034554404a401e41c06100c2c4003c003040e1000c140082c0e209903a4000206d01c105a03800c0700c00f038954030103000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 980144721 1250 980143471 980143511
    0x103050f0402031c02190305090112141501050d0e01050603010c08010e221a011404090c0b220306050906100303120b0a181a0d03051c06080718 63
    0xf54164840120920403480700c01d0b40889112803801070303030880c04024016046070007164501f1400076200152110081da00402c5400c004400b911017044440c51648e02c0c00b04194018080301e20500c030790034129031242c0c07160044800101d03d14905002c06d4121101c81c034060541076403054841c0d400c003400602c40c40c0c13180000504981134880e5416041c0c036281713a48001c6820b60401101c02c07141142c1c170500441c4142241a00350540a0807841003985404d0500c500e0542d45002d10b44298100315008021542c4500c051054851100c8c846070b1b156113044400b032106104588a0505102c1a40e0020920000307501151241c0019029180566982d410380c10702115640001008945000580c0030700d8412580245000342e4094900f450240e01e84a04640034106003188d81901500c0b031803440344110a81d407032440d00c42810366408001c804079580c050424011154200000e14000701078944080090b0014801000031405603130b5181d46900d254415610401c540800e41b5040540c41d5950b01002c002d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 980145971 1250 980144721 980144723
    0x1120b04090b160f0c1b05120f100504020f01030b0109051512011a0328060306020a0201270f0c030b0108070e0c030708011412032212050d2316020103050f04 69
    0x180210075070907a8614240703005038a01000074401b96800860039842c1e113421112030442100c0200700101c00441c0741442c04401d04050004503050006010041e118805101444a000d00b07020880120060040b1000640c80c0d0140345e004041c3c0200c0b4174408112402803511103600704c51a00c1580e05d030f8a2480611001d1000b074020314100700300140f10b4102503200f08440b00c0030425041c28080f0139046da00c0030344201ea00148c440550000f28001c3c895024804d6511304600c190040340b5404146071003000c501d001040140c08005240380300030030491590042c10140d030b0301c0400502596102c9610954070420760044694004a0f07001007017425944500ba40c0c41213006a03580c4950385e0800d40d106900824020006801c5070310220b030241020400d01c09020302c0395034013001d4001c844211042c801c2d07003003550780805110200211041c0110b0000304500c000c0d000641031001220b080c5064080400007441c092a032500004648a00342c0c0b200341610124540c001d980521054a84d029400481301080d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 980147221 1250 980145971 980145977
    0x20a110c0609130e01020d050a0b0a0305070b090a0f08240c0318102d0203090c04110403050a0c0501170906070f120615090e01060c0201120b04090b160f 67
    0x12a2121030b103082011520415941103000c5007100040301c032036099070021103c0e0310b1f5107500d41042118003d05032141100803841120304e004814030396120151102c00d075002d18000c0c40b00c0041c0c00141c60301c48404043c014140d225003166020354070810252524481c1d00f0024840034100c1c500803016001c2004c0718011040400744501d15240c031019510031070510b800e05882805508a50811560240b240200c05400c06400c1d14001c100101d10b1034002d0343e12601d00e1082c91040c420b001d100000020340d00d0926600b80c030f00146e409180030b01c05506018581c07000f04203202c1c4019980800c94500303405400c40324282c0b00e00b034540482100a88590104444030400d942c007940018040a10903a12070000c071600d410001c0e405049442c01100ba41c038203800482d285500103845000a540c0110140c0003080302414080b9603504001c80117000d500c001c280079040004031000d03074040d0009580301d0341c24010010b100b040b200d140d40c83c08a034101001c0341c444040640e160076800c8100e001e82d180d07a0602c8090386d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 980148471 1250 980147221 980147227
    0x613122001050f0405061c0f0506042d090201210f0510060f080c0408070608041a1e090717010c031409030f0c0102040504021204140705060306040e01140109020a110c06 74
    0x19003801390390381200d0b10300c1c115900300807d0070240c01118880d441801d40e4090000c541480c0960078042903030001c1c1c5160307030a00e0600040e001401da00e20b40c0d041c03580305840c1010270349840d98001203d0b0704c2407a04864040308284034400100d000b080e0300910302c0721107407a0140318136920b541001c149010184120300c00700301442480100d291092031a41e5220505064250030942c448601c01c1c500344054002001051071081404140110121036001805810799000b0080c94041700403114420003503090035a0000310004280085030138088440941800c0b00e00400c1c481c030f200c987c0d9028100b208400c0300403074989495160340d4104800c2e214420341c40580210718084404900c480380340d00c210b02c40812950700740004a844c2c2c0d95400140b0062081038604096400c3c03d0400c0c05180301c0301044580c40340c1c840c032020400c5840f80e000741c07a40071404450004506510303040a50240484201a4902c0205000080f9000590f58007600844030181d85903c602510700c04d0b256a144170b03c0b0046644a1814 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 980149721 1250 980148471 980148479
    0x405130c0e060618030a081c06051905060703021014150d11010c0c0803070b0117061e04081201061e031503141203040f060b0607110613122001050f04 66
    0x28581e90382e200c094101d908a50603a211071f04a50410341c0703204080523801044680704011401000c0240008403140e141280e0340781e0018100101710320840d4002c9901081e640141402401084501940507000b4403200b500d07030300451601c42e400c84040c2107150741c2410011107030030049182882c0d02d510880662000882c400191440c90002c0011221000800c0b000f1402c0314013400a0b100c201d02c03a0800141c0340d41054403c1c441d074004541c1d0b000b5280e00800810607070300894130044c10040b51500010b025034540f1704240303001f8030405500003070f400c0200c03000040f85a0311080881d4282c820442c440012113400000301c05688106807144914140c2a03814804600d545031045610303045142103e030000580007100116400454007510132101c0b41e0f0511060000721b02814040c0402100c03020326000c01c0395210218040c02c0c0800c5800386001083c0d1082c540c01404005014001b40c1041d119243c00510b4074040304c0c0704941c980c100c00c81491810a5041d4000c2e003d0764941841da800690400e810 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 980150971 1250 980149721 980149747
    0xe15070f021b0a09020f0903071707140d020303180405070c031e03060f15030609180f021306030623040c0308070c050d0501020a17330405130c0e0606 66
    0x40102d49903400720303401c0d40c0007441200e180300138400ea0b4442c81c4200e45440c040380804d42003140940c030050745020000300002806074041402000da8a01c007035407200100901c00414116825150000e404d440006000c00e4480f010101c0e6400c8420202c606014550310082d08a4551803056401004124036405100502600800d0612504620b107000100380742d448000300845a001da000088001c512108903d071658540500c42c041c01480c001441080700c000f29461070001c0c8200e001c0c0c00249400d080307008540d6145802004503102060602409441e410088020000c070f542d003943d414038605402e40e4440308030701c40c00e100c0c036040101c0f103544a103151242c500c40c0d0311180707003112041d20404004c0f4003951150058003c07507004030700042e11010504405000158030750a00c0482c042c0003c2001a941014049800000d80844580c0038011032070300a000750303440c607242c041d41c010304000800c840740c904440141d0a0714020400c10103496680c881d8100003a41c191001a0011410005403410101c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 980152221 1250 980150971 980151013
    0x510140d140c090709033f03061a090901140d031214150306090714060703051603051312050307020904240c030c02160306050405100e15070f02 63
    0x2000e0b030304540007050001c0d0904900b100d4560100e50869405d00500014941843d982032000c0890100d41d40510410800c24144418800d2003144590203c502e491181d04000000c200e250510144991242800c16043d04842c94003802100709400016817400301000d0005204400f410199884045480443d14110b0418040c400240c442c2000b0044005480a0a100b071000146c04980c2c540100e0400d404d00b035019001c0e1440f030380b0000b000d00684407007088003401c01700c08584540c1d440c0080e00c1c040d80c0502891405200300d80000f25004245900100100103425404580702034003074072441c034448540d8200070060701c9540180300200050034415800b0fa0058041c400c2c04080c001030b4540703441078a000b03820b00034919894030081d00682e5014040e4400c41e0354680082d1003402c034181c0b05113000b4030040c48083c1207181c44401240034440140180a40d03144c60030400d114002450f2580c9a440da1600001480c1003051b00005d140903100c5c20f5010110302051f40900b6000d20300442c0c0c8140d81c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 980153471 1250 980152221 980152253
    0x703210512090d0e030a0b0705130f0f06090537051c030801050a030201081b0c030a09060e06040b0d05090c0d03020a12090b03040308090a080d0510140d 67
    0x20400c4a180741001e41c0d1005840742000a0040884607800140107080f5007000705054025440141e160000070ba07000c0c0c1c42a805003042c0340840d01c50400407021151203900ba4401030580d402810301058004d01e240350319055a10307a03192500303541d903950188024480f130b0381c403ea0540c0340d14101f0403c48400842903600c20010340d06185c4132641c3c4400014042401c4048a01c400d1b01c1d04402c4070003095000a101c2e40102801c950350b0901c689550000303018060010118407900c2c0c600c00c41200580700d070340c056600c010901c008594880808450241408000307020300c1000c244c00146249041c502401120160b03024005054100202c80d040c40c0d01400025284030f40c9130155034440304171901c0d200900d04501c0d0107640184900e01c2a0700b002000c0b4a4064400c0c0c04104818000f40040c0b01428201d80e00541e040c5030540d220f035607020b03c80e4204014464000c084c0480041c034103182c2825078000d140602048001c01e07002d0750b07442603462415821a0881d6412100c50b8606502082d10300c07004101038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 980154721 1250 980153471 980153477
    0x2100203061f0302030a0e0d021203060301021201030b041b0b19020a020907090e0f361516030507020c010e0a0e0112030908010c23120103060b0111070321 68
    0x2c03110700d0040ca18910a44440b00c00007a400310810841c4103880c00f034101c4c003501001c0940003008511000a443d00010021803800800000100c0c14544096041700c4103c2802c217845200340d40c4902c3c0112000005503000e403503000c941440c0c1030306901d420804100321181f072007503103140c19142070480c541c80d11007020440070343c0610030b080000740e2074010400e40700385800d54480400c68140b40850b0f801d00300183c914456154904200070b04c41c400e20300354004001100c40e1052101600700c580a4180140354181c0f41540103000703040180185400980c0d000f450307480c0c107188103040c480c041142120b4007203840000607400010808015400b4140c9800c0d420b9010f80114403103074803031452a001e018281c0c0306118140d110b0090005242d44100400082c094800090001c800110402802d01e100c10110345001c1d014941c0007140f8142c110104d501900b00da180030a502c0d031303690400d0401002c40c2503031907011400c04400400d0402004c9041c0003641d0744030701540d60003080c8852005548400303000300800c2c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 980155971 1250 980154721 980154739
    0x907031106071406220c060516060921030903090e0a0f150807060903150f140a0603020118053a06020a0e150307030506060d140f160210020306 63
    0x81152041c5240303c0940da031009002c00e082034402145001c0a59040720743c111044410714000602015000d41110494504192603004085020001900b0700800a00061600c415642040703e00d840d100c6900d00030000201ca0160b4603038040d01941c5644030000c00084d40040d0910401c007500040c2c5802028040000980681c0252000100e03940540e032070f082084020340800c003c01c802c000c4c40e40075205901d0000d40903851580c030b14031000c001d501c00301c02058840c0440c1c2e90341405680b0256116921100854141c100f50300d54400504060000307030300103017030b030107010342e1419001c134104081761800b170081c4500c1c0d4031608042c084402e140001c4511518000101d0f85407907160001c2c1a4401d01031800140e842e815110040c02d910b00c00d1390040c0c01a00d94440c010b02c503542000c01c1d60b500c500746050110765a6503500020340d1741d00ca034040141c1200c1c50611101d000c0c0c1844510148610780f91004102d42d5201c803205c0c420080881550100143d000d21002c0c0c40c90041e49d0080c6401240140c11001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 980157221 1250 980155971 980155973
    0x1109010f03020603060d0606150e19061202070614190605150a030504050a080f0a032d2309011406031504120c0203060a02091e060f0f120406060e0c03090703110607 72
    0x106400940c000c00005034007410880c07003070b01e00300034a5414091a12881d6850be0300d091030290524180c0301c0c1804015078003048034400d000792a00041c900202090003000075103015401c0c03060100d00c07840706c0c090041c500300010440b4140928040984401d84082508010140078228040d260040c401c9400d4003030b100900340010030141c00b6100d1084540e140725142c131455480101100d0038101169610300c0350940d210b103204811b060b10903030403241c000080340c0d0307000460044032030194071543c2003110210102001500801036210040c400914101901d06407500010950341c0c0340c40320f07000b546500340000454001103030381c0c5c054805444641044e00c2000043c0e000603007405030403186070100d1a000510690a0f1030030781680102c0b03108280030000c031500a0310201e030881c0500075582941410004089a20841c00c01c01d4422010042901202d0383c07400d0f00c2d091015050603c11189102442c0e000304200c10010009d503407107440000300505d0054919150440d044010f02034030744e0014001c009000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 980158471 1250 980157221 980157239
    0xf0501050403050a0f020c2115040606080f010b331207091e031115040b09041518020a030902060c06090f01020708040b030709121109010f03020603060d0606 69
    0x281c4101e0003a202d141d10354000c004003410750a94101c8204c11904403c440c3c040c19500d00b01400391281600800310b00c0811100541450101d410421400003003940040004102e10741e003010090300d6943c01540c2d500c1814000b45401d035200b64420b1039000501c3e03480040030b0b2240011034030343c6c2c00d02c0b822074400c1d40c0c202c0d1540c001c0940c0642e203130b0752445a00500f00150181c001840b079005202442e40340c260501580398850203451380c0e000c000e00a84680c00380400341c0d80c074210341c4c54850180030282d640d201c1c2d6680307114000307500400c1d22078040da04000085035400c1005402c141107076907103080400c1c400505400d0000030b5014184c0002450350310b448040143c1c5400340a05a0103c1e460b0003071440e8101074501c03a00c2c01600d5a03826000e40e00400c5000c0001f40340b6401d88040b00c020b290100c1c0c5a1302e603294150703608041e54200b9201c45000358444424132402007098400b5140c10f40b4404000e0742c9810021200a20600011350402c4040000c1045801c24140c0102507a0003000c0008280f502c0d00011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 980159721 1250 980158471 980158481
    0x230a05040f110a1e050324270f010e1605070218010308070c090515120f120406090b090d030c0311070f140405060a18022215020d12090f0501 62
    0x40c40025444c24482840218440c0142c54005410300301682185440801200b030094400a040a802da1102c0d560300b82c0c0e195040903000304c02c8030200c1c440300d00d040c0183c6100d01d1101160882c0c45a4644800040c22a1010089901513030b0030040e0072501101d00e100c15109584240380407a0400f0441d00200741e030400089c46580a1803040e00b10550f0380446007000307501c0e8102c0342c009501079490300382801908900c1182045010500baa001c2c0f190000f60f144540c201649446088000d004031000c54a41400e62001001503903550703183d01000e151510050416030054a00305600844a401c5001c0441d001e440c2d2a403005119142034100c02c0c1503880801c0c14100d00e0b81c0401040955050140102e450304442c0001640b0280d40400892900c80d00151343e10885100b110050080c40c00212214841030301141c0024044840d000ca00200d0301880c01c24207240c0f4424074600d92040c03800c88605070300c08503040c1021007160b91803402c01107500c001f242c0105010701c03044904200000780320000403000c1c022 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 980160971 1250 980159721 980159737
    0x70b1005060d020705010507020651120c0105120901091209060e0405060d03050304030225050111010e1e01020d0e0102030703060f060507110127230a05040f11 70
    0x1025894001e541707005400d540001c1d041000759004502000f0807248400940100d05a43c0d0b500300c83c40502e108540d11244040b044401032505050510f5025401c48140041e0110300a42f0400401c074035594100c0d0300c0e40e00d040c1e80103000500802c064804586d000d080c003600418880700001e620001665505000501c819681e00450000e80d0304001d096000170030b150b0118400e583c24411b40c030b0003000140d10004c185400405012021000c5400c0c11f20070040b45e10080c1920501a4154007009040c2158025601c070f52400120203078021804c0c84418000d200d0840c040200402250844641100e441180d0907000b03000c541d070074080d8401c150003034002c5c901895041000140d43e400d0506c401426100c03190061482045000004c0058943c0201116022a08010011144641c100040302c42e21505414075041d002843c1c1e1321820300800030700c4a001c0f5154041c90440070400107400302e5112007a217004c035500c03108404080000b4282500140343c1030a416800041c10f4140719445c46c0c0c2a009101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 980162221 1250 980160971 980160997
    0xf030d0f0f1e02070e06030f03040b0703050412140d0e090a0504240506100903051b0604030f060519061d0a0f0513050d03020f0405040f060308041e0f0605070b100506 73
    0xf000b044030707059140703040b500186d05a01400c5030303440e81080344d40e80780304520074441602c2c00010040f06240c405d40581d00a41003512240500310401d04100040810392b04000303509010b11064100103600411041090a0010b0141c41841e50b90418000042c01d00400545d4007e58585d410000c6042c400d004541b02494003c000400e814500180075101d0604c490b01c4091041400c03052000c9080081d00f60900000b40c0c90035180207183c04c021484900079980010854502d13814184100280c580085215103602c9011540c0d0074054109a41991564400c0311079200002d6414509900c02000c0c1c82e030f200c03a0740b05c404a81889640700343d1085580446c0e507206c8481c00b40c1403d0b41001020302140103003142600d0250304180390a00e4801d02c9118510640703224039a2464200d81d100001c1d04180000c6801116503611550380d0080c020110031001607034151091192404511410701c08074000541c1d089503552401c1c001140d541c44c0308031601a04c1c802e003d50202000047e256141c0008143c0b000c4012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 980163471 1250 980162221 980162233
    0x1906030b09010e16030c2105070b0408010f0624020c0310051902030c03010b0c01090c0f170703050a02060708040f0303051e2701110111090f030d0f0f1e02 68
    0x10a001c0c24044c2203085001040401c010030404100d0200f8071a0680d0f0750401f51917662610401907001444c000e000c001c0c03840c010440001800041040548200c4e41482d000b0700104009403804803c8910741d0180700d0050342c0c0b040c008180311515052956500d80c1c02d004a811312036100300041d02e8000d500ca040321819454034100586106c50308206048071000010660950034440018a0140414000c00344442c0d0040343c0b800c2403c10035000754000540210307003010407640b660300c00480306003e0300549543d1403003958981d141533000503200017100d4214001e011380d01116401c104143c2d002641c02e444442d8180000b00e40c100007401d180c002144070b51607107903542c0144011707000700d0011808002d450003000d200400d91b00c0380041b8220011040c10521400c1792124074016512100f80d8850050190710348a0000403051b010401801c20003c01c80b03000c6040760084c2d04040c0c1d40c0001c200c0940000d05540701600001d030107281d404003507145600700055880300501c010884444000784250050303100c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 980164721 1250 980163471 980163491
    0x1e0c09050a060806040308161403041a0709050d120e1804051501060f0c052109040f06060c2009090309090f010501141309023f1906030b0901 62
    0x9407052038010f00c80100030b0106450261030162800400030044000e0030b40014560705000d214958282d040c1034050f80742610380c102810460105100654030b0140c94801002040c0f03504d00a040c40d00448000400c0503840008a40e2a407907418490301042c02841005050010709650f103460f540e03c0e016400004140b289058245107103007220606860f2100400b442c0180400e59000c541d07114a944581031414000400d451701500d44198000a00c0003031005520f01c0004038050401001c0080c0304540500502c0b03ca02d91003800c940325031181d0000701d10b001e00c03000005800c1d265010041040f850344a00141c25040105100910861728141241c000040080742c80c0341c56034072035400000052044419604000000e0410a21030003035000344107010403940c411203102c0030714401401e0781c12419501c90340345100c0c060a4501d805403010b8803000ca116202200c0110301d00101081b21810502030040d15040041004048000140c41ca51610383d200130010400d8140014010390960b030002810b4014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 980165971 1250 980164721 980164741
    0x306020d1d0d1d09010501050315060d06030510050c030106141201120b130c0627080a0302240c0904020c060103240506030303040b0921190e0d1e0c0905 67
    0x1064403e410380c4040b02580380c2162184001141924000c3c2040d60342c0b81c441c0c0d07600440d110600d01c1026486003001400320703040d0003160441801c6034400c008542c008524803a900c4c064a40c100e0703482e00f10341c0040c4010010a44a00d800340204003102e24101c2c40d12201800c8086405400d0b04500d00d1001e40641c88400c118004082a500440e44650310742404125035803441c05099074481c81c03081200665880c4180c580c507040200741e494200c22000d10040c0c2d80c0d03088507103928444070140d01500600000c02805504010b140710110142c0d1510310803a560400420105d42025441d00d4101b503007441a040c0342e0f43d00308865406903004507000c003110098400700710300d0401300c83c0d001b426090520301805420345000080d030750456801000c020341aa41c05164515200314419404450614103a56192880d5030f00300078540c5407004141c12a602017100e4054400070682c402554101094840350004101c0320b02d8100200a02109a82e4082040d529219611b280c036805c043e404d181e40f1307024031214140c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 980167221 1250 980165971 980165987
    0x9060120030d0c300b0109050402030f010302101b170c032208070506180316090c020601150f08040501061a0405030f0a020112020307020715030b01030e0c0a0306020d1d0d 75
    0x8162545400074000031015400c001c52102d0106201c54907070784429217036800340140401404000e0011074907440c2c42050085421000c1c401640035a0803402401c108600c60402c0400d4000c8204050740981c4580e0f680c0b0020005000207a99103c00900a00481c1c48040c0000e2007600841c141485481e080200d00050b0543d070342d44411204c3e440341e14104855121a401c1d6807106c8100c49030740c0700400252011900700f42d12540805034594441c000441c01d46103540c442500c09800d0b50844505a07200ea040c3c2c0340c02040c3d084c0c0e01c0003091480000010b40c81c0320741d00940c0d0083c0700f20000306865644042c2c82c42c003041c120a10031020032002c2410f02850508018240c0201110700060090755560f80000e407141c151594a900307042e80000004c0c9080c0c2c02000850010030384185614424000d0b150004c006210700c005280c00241083c2c0841041500020380640300e920041400078118590385e181030096125460a03400d82c0d0b01d81d5803810216610401c01124500448040c141902d80f4a00007003880b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 980168471 1250 980167221 980167247
    0x4030c1a010f1701020d050c040f0e01121202010f0c051b0706090b0706060b07030804060f09030e12070e070206010e0a0219030504060f091b060e09060120030d0c 71
    0x800400010400e90084120b00d0044a0880c58a501501c041d03407545400b80c4a03000304149110300344030500900c80d0818000708220389841d10f0a108890726089082c0e5204401c1c81111810b904201805001c10701d05482840d4080c00d50000003415000c640c1792030309442d10300c203502c000718038042a150450340000c0d0b40900c02c00d480ca0050403805080c1b1070042c2c03001f21140281514010042000010444203174450005801400780d03a5448114915005200700f0003110202d44290401002000503500c500800442d260305da01d603445030310b08010078040c0548104e600d290040c400c091000842d5104000c0303843c00341d040e03640038203059030501d600c1080b000780140640f038002c1e204101c0e285021214500703288441081d4500801c1584490070248082c046140d1402c400d00d2070031400408000400f04c50000400d404000c9450040e62180c0c181e80741201800f4040d048a461000942250b2040c2c40c031840c0710106480010640604c1e0302c03000c1c519000312942c041c04076610460240c1062300000000c0e580 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 980169721 1250 980168471 980168513
    0x61609030b010b07030c0b0907090e1f050a0b120f0c01020a080706051e1003032c120a08070606031e02010215190c08040c090509150c1204030c 63
    0x110300d580e0391007221060500c03d40500b40c0d808a4003d0070148a0107440074916040390240c00302d400c020b200b09842304094851260103915120742001201e01c082441c40011341c10710403501d445013000340c142000d400d004024209490f030310b00d640c0b0010307070711590301d801034140c1d220003880b1040d0140c00d030314a01581c9200310b6040d0340c05000382400041980c8200d861841e44440c003c071300c0b0349440042c011031000340b0084a52410703541c0100040180d00c40d25120489002e0b680340d011241d000100103010400c40e4190350740d00120600c141c050340c103002e28403444000381081141c2084cd5240c5031941e15800c0610200c2c0c08176140e040030014032400760070704980c143d088a2040051100741c0d0001c0c0d40c4088480c41c0070704807981c0070001959038001e484100c522109144080c881180c06210050022804403401c031006140b110010650405a01c01e2602c1161140000c1060441800c542042541c0c0101040060344007082200300c3c000e40b45072524041c0d882522264010035803441c100c40340c282d01c49084a15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 980170971 1250 980169721 980169737
    0x1213050405190c0302070b0906041b1202040b03030706110d0e061303110703051002120a20030c0708161a0423030d02070c05100e0d02060a030e0f0616 66
    0x42468801902801000104001001c00469a080c4c000c0e0040820241c002c1c034500040020303031400030070003e02c074910800b003040e01c8160b81c43c2c103880c6041060250120340c040262800d001400d00754045003c00f80c0040450b800c180403983d420059403040054000c0303013440883d00031410012030069407030ba4210f11018020302e1030180c4180d004c0031415140607041004152580d02913480030300155000c0c6070040140c5401c000340031001d101075840b5012500041c1c3c0000002451000d0328030071070100c1d160000240d03c005401c0b2003001403e800141090300040d404001050014100c1c00044c500b800140b10191103003985403c20640c9040840801941c11002100300b00000b1001082030310700c00000c072031034404983d055941c503245001d80040c480d90700b440022004107025024840c2c0702101c0040341c40c0441441809400c86510032541d41c1d058201034100409070051810b60041c00b01c0903140d00d030024161659141061524004061150042d0403c03814000303140c3c1d905907100f48051180c100188 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 980172221 1250 980170971 980170981
    0x17010212010803041e03151a0d0803150108010312050f0f0d0b0a0608042414090a0209090a0b010b0d09080706060801061202030c100c0507060e030c090903030f0411031213050405 78
    0x541f4031182c005d4402e145a0307441c0200024001c0c81605011b0110180400031407400030315006045610079203446032180c1501200c0503940d03200b980f80506a030707404240f00c100840000015030301a0080c180d1090a40381c2400420311f04021240a005103507801790340414605005401e001112700701743c003c241001010010440401c00006620007000118007402031a12896291328006013901040036540c06215400c0c00061000050003402c1c2a0085407110020b407502e4810035907840303005000604055030380303004021907910b2001508203600000000f04e0b04c0b2a90351303104001507003d0b40c011108240d44007018028101d091241c0d5020f020b2030714810100c0005500081d0761210448902442100e0740b5900c40f001a104480d044d0100f58400200c6441030703200c00c000340000c0d07121a03c060091182190311801d034035180c40c50301e02411144018600e07580f41d0b00f0035480c106c54000d0046c2d94015202c82d42e092940c40c100580e084001b1611682900d4041200d015520200940d022900c200d040c032003485 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 980173471 1250 980172221 980172233
    0x4060c0905030c1e0a060c0b070f1403041a010602030a0e030d1409060f16051903090314210406030e0f190c030b0a0b0f0a0f17010212010803041e03 65
    0x2800790701d0200d070981840b0220382544a0130718070b010034031500800f800d03c0005429401941d01c2c083c09208000340006640d07604000c480d000003c030f40000004446c0b9403603881c814114801950450b008080304a44040c4000803800c007480c00303902c1240142d01c00155920300d903078051500e4400c03c0f8104d01900ca120084207000345a22081c0400304400300c4001510500b91341e89200f01c0328a0340b20440200d85841c0001c00020047d200302c02d00740c640780502d1070940510800c5044680d1007aa00d500d84a00450450300c80c6840c11002594088203407159104000c0083e04032401c1018030344080122541d264104800101615a1b00351419006e501c0b40b40505200407020982c1e18200c804c403101c0c82d0324610316050110001e2900d600103045e0850081c18800c0c1502c494001000107102070314103405000000d000e00005603454403070103a5034070000300c0600404482c8518a10b0351640c030f40000d802e000f12410300b8061001c00780c4c00384031140d00000c2c007046541400d10002070704056030a009801d03545103031581 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 980174721 1250 980173471 980173483
    0x3040506071d100908160f08010c1b0201050904140709080a0b040308090a080c060a140402032a09010f03030f050a0518061603020106050901080f030d020f0c060f04060c090503 77
    0x120f10840c00708a0f8012664410303018a40100741603030849060001071066080c6402c8180680c0e402009440d001103101c510500440003406a266034104110041c100103000c030f420509012030400c0401c0040420399601c034090128258000740c000071490401c0c1d07001400304c040345d601800346900700070041c4000c035003c00f41050b4025010b05111600c0d50700c0c5c0d2006814440980d01c010803c0342c010404159604000401c00e2040a4000007045000358400c40c1011001e01220020b40c1a0300c07080304605a601010103540742e2050882c0200461a40c000010b0080b41e0242c201a8410030320304010004d242d880500f248032040242061460841c100c1001006c0d8403420b640c401d000765503e48002c2c0700c0d44841c0c04640c15104084800203122500b0325009018200b039200706881440c0c107400201d0380304c1c00800c032543c400c01d02000039450a008004140060b420031270040c42c0c1800c0911400480041c1481154031500d4403141c601c44500d41454a042201c41da5000f400030000140000e12160b20b000500d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 980175971 1250 980174721 980174777
    0x80706021c0201110c0604110a1203270326070209041205040b0a030e0601240c14010e0303190b0f0d02210f070b1201050d05030c060c0304050607 64
    0x1041e80c00308031854059024014290322001c8010000176007154001e80816034601417031040302002903004195013080000d141034011900c460150100020000780504254140301c0756042506841080c00c84010710b1000d071540c0305441d40c1c4540144005010031090820046c2012001c5281c18000d1640120b01313840c078001c100805c0603801004019007a4018820385d0010682201d04680d078000c01c1100501524860b84817031078600c00d02d03001003442c4c3c04004446007054910321402c000444000b5040b0740784000740b8402d8454920031544815035210071700034882c07001040401940c0c0c03420305042104020854041e2008074a251102040481e0f07a4010419101001101c2d10103a1682a000086e00c803240d50070368101100c0e105010035001c140212b0341d016040003000070303281520342c0c581c0110818800c0824900c24a004107006101c6407504c0b401c5104103a000d074007105c1c1459074214845161007015903008a0482d0048100400c00c03104102480d40702c011403909004802012900c8805004c1c1a14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 980177221 1250 980175971 980176003
    0x20703050f0f16080703021603170d06240215090a0209040501020d05070e0a091e0e070b0a0e0f0402190302090d020a1d07080f060409110d03030501080708070602 71
    0xc0700d694414a042c152020240f000c030000030901d02c2481c024180780c2c8825800c60150060040c4290303d01869081c0750112500001c0a454940c00b40506042c507911048852204a984007000700c0c40c0700d441c5034200c50448600201e00c1000303910141c0a45000620520b0100e028081e030304109416101185441d1000d905640040c030b035481724a403060180c012a000b036030903240740404000c1303541da100d8121a10803009443e81c210454440c80c0e10001d65480c11038050b4201c4c01540e480c90038103415400340440500003801e540c401d617180c110310b0b011980584007140000300c01040445013460148205000c48004440451a08030381e1001450b04440031503491050503408100b601c4a40c80c2c4401e0001007990040c08031228a44903001c00c45001e140c01c80510b05040c012000030001c134051400c0034020a0075000e811015524202000083d0035003027030449802c8400c04104034076841e1303900d0246000303119071400f0400307604201302c1c9854030025911001c907a0340100030420040f030700800d18002d4401c4000e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 980178471 1250 980177221 980177227
    0x402031003082d0403030f23120a0c0309020306040f02060403020307290a120b13020a030203010305060604052a0d1409010c0305100603180b04120806101209140712060b04020703050f 80
    0x200d21258998414520340310341c200009e000070390341d0071040d85906c262102401004050011001102100c1441100a4140e400280880c02003520b9807965481203200522542c07525481c1d072f010038141181c5910003244011041001040c802004014800c1413040d900424106080e900e00204800401c01240307216a548d8040000a501e03062422024000c00c2003007595102c030040300045c000c3d07100f40701c1501d2900891021803024509800382c0c40c0662040321401614000b0744665102030405111820301d81c0204000d00708030701966001e8100c0a40c008c025007011031070080780c450300703441e0391080e5001014074040411814207010140ea07800d6a98510740015000e8940c944071041ca200e003000902103410960401c41000807003505d43d2061440782e42e40780345d151581c0040c4400c04040c18a400042112002001c250300324aa0003540300c81e01814000c0b02c074000c080c000f40c1c103101c032a400058403656902714003800c0c0913403401a006040b00a803800c51418245031801440c0780104922001303403503000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 980179721 1250 980178471 980178497
    0x108161107050a061d0a08060403111c080f070207080d1b0f0b040c0b120402060a170f010617010f0510140a0e04060b03090c0402031003082d0403030f 66
    0x20007402010748400b90040085136243e41000c1c00d01100e10f820100c03020b94400c01503070b4600380051814202c8281c0390042a15440340d80e0103540c0d20014211a5900d8443e640d800c61040c400743c2c6d440c0840481640342e00040e410500710481480100400e0901950f01809007000701c5080010150502807181c40c0c020702a21502c5540d01d8881d00c0010050000b88852000406221818080380d0085100395800c4190716680c45981e02240103145005a5140303040700040d0250500e0002041410401c0c40d1110b1501c0004415402d5040c080d03e09481400e58a4014012542c03c40810440c00c640384000c046550724104820310841c40c1c600909009900d1668510b01260084e07401d40e86400d002c030341e519118990880d0003000c107c44541d50078491414004c001844601100c00c507405054140c02500d031941f800410311019500c0076081403022900404000b01042080000c0d120200003561040060101c5880701000130070544448040103030700f000200006500301c1103c04030515641056201ca00701c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980180971 1250 980179721 980179723
    0xa0906020c0307260703050d020606031501061202070803070e01081003050a1211070801020a14070b07030504050c040e010f2304031103040506070303230121110411070b0601081611 79
    0x142c80d1404e03101e485840f101104010012030305a0f07840b007a03542220101da4541003015036401e0b6481c1a002000d200d80d00502c01c00340f08100c401da1000e0000c030050315103a601d03550211268001c5030000d00084030900c2c18499076900211302a00181c03044010b16115003186c840720b88404003143c000302914000e44000660b2400f4640820002440e80141c0d09511381d2241c999010f9031100b4039100002c1c03000401071070105040300c2582d0400b0f0300f040742d07408299a401410303402407030090001e50f800c1c81006040500c698070390042c002e046500c54000700d43c42005040321016103081800380c4103220507415020708018042e0b6034445e4020f40516042040c418860729850940c8529001650880300001d07499052642641282e0040f008841c0c8644c1440103000c0002110704d030a000388480584550300c6503041072082c803110a1070a0103801010368903204000042c007101d210180000007100c02142c20420300001000e0568400001e01301076440d8a802440b02c6001c481444135041480400c0200c1901800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980182221 1250 980180971 980181029
    0x909020f0307081e1c05071b0b091c1707060f090b04140c030607030207050c04050a090b011208120a0b030d08090c0607110907120609020a0906020c0307 67
    0xc0c0a8240d82e00ca81d00c0308011626860040b00102100b15222041c009601c000240081480790070040000081d035440c02c00c440a6002100954010680260307164400380c11805a00c014400881d03501c0c3e03151075180a00c1480340307600403001c0850104103000300200e13200900c0c01303c02036200007829a0303943c01d07441c1030130080007850081403c10f1303d000e4075001040101c5210601460003917003087c40401202c08a00c0d41c0700e2504480f15003640244020418213400382d0044c01d0303402d10a40c01d440c84052404040b0b07045030300c21183e800c21140c030b4200100034451104036035405007500202c2c08585142c40d07160b001c0d803485407900c0525014003420005070000300b9070340440e542c0740c0010143c900e032044100004ec070b449020350b0084803d00400004261500c0d10f00203e904859001c82112100100c23401004400d5000410207014440217400d409041e40141c0700b100041c1501c0c20006807590760b44903000300a0f4045420850556010340c400320310f140c0e000158601111081010064002108142100051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980183471 1250 980182221 980182249
    0x11d2a01051b0d14210603151f05010212120a060b0a1707030606080f180a03170a0c051909090f0509060c1204031b0f080702100315090902 61
    0x91a05050481c10700d00482c3d48805126140d40b13407040d00480c406814030714400d60404407034801c1140100e5a009a580303942a901102c01001d03100940000c135a42c3d48813000c03c445400503404150403180d06800c2c41300040c405000c081c0f00909840e00003041c07040072171160400b1041808180c8000038482c0c41c50b80c000d4000741c180242500e0700c940f4821005403001c00004a1000603414020000390414460b10904045549039038441419848450b00d4049074180a050224000d400040e40100400100030b03041095103c0c1d520000000b03082c41c142504154064010500345081507811000c20b60b200003990a05c2120b180024051010100182c8081c4456444640c0041c03d00914800c08005940150721a41c04401551596903810840f0300c41c520520034070b00c0d1307000050004200071034816035800768a0040c802c0000b451461070384400f00039850303821045030b010070009601400c50500460b281d40d0046181020700451510318095030100c48140909040315a84071124030541d51244510344002d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980184721 1250 980183471 980183497
    0xe13140a0b0402090402040b0a1d010c031103090d150c14030a0c02070e1e010504050106140304110910091404111c08120123010f0e01020f0f011d2a0105 67
    0x2c41c3c3e20030235200c468202d010040081540b070300080641ea05940015030a84605079650100d802603980c0a4860203100c1c003070080588014040c141007521001a560b034418011030282d40c0e504194129941590240040700041111005d1400040420081629002800440c011414514903917040b40f524880d43c0c4010070b442c1c1400284008161440c8114510f4101c02500450923138a55061100b03543c828811720000800c401e89034034007609d1030b41c0510f80291103442d5035140c202e03240c0c0001c0d00c414170544001010341c148010402c000c50715403095240c054002d8110011625080d1074040941021001c4c09000d07051802080d00102114071b503442810ba8044140e0b030700c1d00d0406020b01103255003402002141c404400b4822110786003451421881c1905958203040088804012959910010b4019055202d0aa03402003008024005840c400065100000d115201d05000448100000e10094541d40141400004541c01001507040d08507525062444510085004886d581b142c07620b038041c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980185971 1250 980184721 980184727
    0x1061e0e06131506030e0c0414010506031305010204060206071715040e07210b06060f030c07020a05030f010b010e060412080f040b0f12010905061c06020f0a0e13140a0b0402090402 79
    0x1c81a01984504031000520080f1138050103807d061204845150820702c2d03403542143c004018900d025401980d00550440000d0388540c0d4a40d109400e81e04140c1003400035030004070410204640c001c043d003800c5c00048003030703014500300a5840b4035410a0110210b00494407070101441200041040398014035031160700982c600c0d0800c00d0f1040030701c3e9403202258840510400304501e03182ca001036070081d002d0b0b14402c6285032540d103000300d41035008000480c1c01107007007400003d003a60140010321515600c0c100200f000c4d4001c000040c00b80900c2c078000f030b02c1090140418004041a10130800400d540a1182c43c1d603541040d404241600803a80582c00c4480005814450b4210000240c12203030803c0300454900d90303ca00c520310070303210201c03207050308041134080d40c0394600103580c068103500d03024210051030102c0266940455034405c110100210307103051003040b49403c2a0001c40300e00c4442010270002d00c0110071031010008409401164000c1d19090b0b4541d451380c89038111101c1190040003156 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980187221 1250 980185971 980185979
    0x3040308090c1c0c0906210f0b040602090310061d250504030303050108010908072406080304060e040902030c0108100b030f06030c04111611040504030201061e0e061315 74
    0x1da0041110000c032070420840130b000a86252038002c0d001541d0384d81140b200100300842c41e011000905c20b03000c1d2542803480c450400032a11074651580554000c42015940d0030324081810310b4400651184540607280880c20810711801e032071442201c3d418461850b4094940c00c080444803c0419446024400814181c984003038000d0000c0007100c1c440d0701d05200980c0e0b10703a612400c8549036100a0440e080400c40100001d0130b642610701b1088010814a07042940605070408840581d085207000e6400003400b806816001310b50028492001c03a0140043e814550220392901c00010711315052242040101c0e0302c1c45014a000000f0f409440780c259180d20f00303140003116544041d205207019008400c1d8509240c217241c0070b40e420400e080c45540d80740190740030010f902c484480400f920816100c110b509040e5586025041c00386000354000306040e403c00100000e5950303581003c0c003001081c82e204025602480901543c4030744100c80d01691074490207803640252480d024403004190310343c18085 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980188471 1250 980187221 980187259
    0x200708060a020a02100b0306010501080a0e061006030e120d050603070b070c060305010819080d0902280e16050a110a03080f090703030206010504091110020a0303150b03040308090c 79
    0x101005100364210b13245c00741e0003d1480c08507220000c0d621b07015007200c8014002075010362000703604a41020340000c0d608040302040c42c05c0c0901601c103641c410070110800c0021a03030500500321041c000c18090100c284c100c200d61a42442114440b51302035807607500090083c1d4082c42828001c0181654099444e261403505522401d064060a00131a03d01000811040400510008604180140640f0494480e1195100c6800c8485001c1ca0b07030362580103110068543c036000034180d9207a0010894018084007070028120780341d4110081c16400d02c0100081c40c61f548104000034003881c2415035547c2410300044078510800c4030414094403408502d1800c050703208141074420b40c21145000300c0341d00c8180303c241d2070700407602c00a401a40007000601180c07819a01480c0d01510404454050714001800b1941c0901c009440c9000368000c0c1e003088040c50f4041c00740c8159074a1803011007a84908081d60320001d4000030300094100408031000600034202000190030044000300042c4941c8040c020007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980189721 1250 980188471 980188477
    0x507080d230609070e03160e0906010621020702041503210e0f09270f07050d0f080310080708100f0905071701090b01092703200708060a02 61
    0x10481e5401c0d803004480e074007030141c03100320b014100c020034500f4a9243c00600722202d4544200407a4075001394600390910103030769204a00103064034440f0880c00c4ca4582507031800c004059020341c0038002011881d86819200071100c1e001400030900040e04c1d000e01d800441e0081000326401d0450804034a07020042c040304210080d00b03494213401e0034008084080080340d8a001c07126009803c40e0341105090340c24544910b030076910100000145480e000200034036215000b104044101d0780e00098803140001c40d05000d2240640340642d1895604a030a40d01c2011117841d095015000500c044045641030101c902180b0007000f07650205d038841506d0300040e9403218503c24580306000d241828440104005026800d900394000010349003140c030f416460341c4410303200000c2c850349550780c1c40c00c0c0002803d401e03d014041e24503e10002503040b81a03204061002c0820840c4a44405020480d070029501091aa1034681e020120030700410b14540180e00e0b1507402c0d000030489005002c1008185090755000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980190971 1250 980189721 980189741
    0x52e0e0f180115110111040503060711102f091017070c05120403060504020a0611070b0c0f06040f1a0108070515090d030e1e0105041202010507080d 65
    0x2614240d05a0400c0044803604656803041d100e1401004002004034900d4150094840741030040102000704a01c9003100d211140c0344100c42c602080c14451810100485544012141000709000914a4000d60b403801940c69003081181c865000007141c01030780e07902501c130380c00d00040c1508050720440e000c06c2c2d43d0056002c4600444180c1d6000c1c0e1042d2203546c40c41d5040303810001c03400350f0323456904045402400013201554a0b11940c64844c40c80101e01005100030350081d0030000d49030400c0d104000390840e0340c6c0c0c41441005045011007603a201c0c0400c0c3c1900301d03400009000d5507000c0c2c2c00c00443c00d014550042d00c2041c0100c1041009001820386003c136103a00ca40b240401c8181c0c00c8005201c145403e0103045440d51000c2d03420300140c100780c1c51119041074150780450600b0800030005010f10b0540c041100081c84140795800e160408041c031444a1240c0034145c003110f010800020300c6800307548210400700111140260a590040d4100c03001c140d00706031210b5648500645904c050316481d56 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980192221 1250 980190971 980190979
    0x1006020105091b150403080706020901020d1e08040c0803070309090509030a14031b070f031d030d0e04020f1306021209010c060e0f0106170f16052e0e 66
    0x42c061240101d84980f01070141c1003200840d60f5881c06200d01c09a40b140322007102e2404000200204481c50094203001c1e118440142e0303140364440009003403610700030703200c0c007408055500b00e002508038001403800092a841c0c151901da55a040a0a6400c010f41c400c1600c0d000001d441801e06600681400a89202d24018003d68032080070007591fa114924040000900c2400e654182c0403515004503001001e1607084045100506210612540700c420b044603c1180407180c001090f4000d00340d0100f0360340000001101c52880004243c503014401c1c600c00c10460000103280c12607840c3d905949018128007007030780c0c5591614103e06480c0c013541c050388001d841070305030040c01c0b03d04a80444511141c180d6451480e00e240d80d480901404947e0142661030107002940c0c0b504c1f0300c0074860b0708010500308140308084920340c0c10850400f030001100c020300350481040c882401c0c5c25040e40c00b040b15010b0354124102024144050084090742d0001d01c002c000c94104580041e52000420010040441d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980193471 1250 980192221 980192231
    0x4050a0b0a1a04060f05090406090f0c1e05090103141f080a050c0d060209030d03021c0b0303031305100c02030405040f140406020f0405062a122203020910060201 71
    0x42c5500803901140d00108070880d50403c002d1140c54460b00142c108408941091810320004030005000d503103940c0c02c8088003075510000507241503103a004070308542c889414149a4410516000c0c4038250b41194502d040c4440010492010303442a40900c0041103140d4040c04a0b0401d61a050101c0800c1c0041c4030503800039600c01f042410001c100000d000b544500203150030040e19003030007524440c0c18820f842e070f5a400d10214540c1e403424001c5100701d81c921f55005175144005a002d194107480321522407ca1440c02100c101951030000450303030404050100d0942f002610700d016880d11200400c0c40e40341c14103000329117080c1c5800002074003e4800485060141c10900c40c8120100c607044540710490000d0715011a01017030840c0e0040003c6501c0308d0f40140f42c41d4640300810b00542c0030501d4110303031181c83e9096180300c44071100308408003034205002e0b114a8100350408245400b90011300004c0100380c1c100312803200c0014030200002c582c060855101403074000d201e400004405c1c86043c000d94209 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980194721 1250 980193471 980193479
    0x90f06010b030f0a05221b09061206051f060302032502060f0603030d06170c060f030103080903100c020a0302011a0109032a2d0605071401060504050a0b0a 68
    0x60b60321840c3c0c01c00300c20110390795080000d8060400a404000004e003800f5091201825a0701c44d002254096002c900102c45420181c5c6a103400541c0010003c41c0ba245040c40300403079904107090f085421500124444e02c0e000310000d001c01000782101307442c800b05240000d91981503005144a038010000901c0c02c0c01802c0228108078502001078401a081800010322800c2241c5c07400782c0101c00a404c45e4208410585c3c40b80460703205800c01c0741804502641600700301e6082203540e00c07020007030702c01d80d060190300303501d046042c081800024134400d8045400402034904004c400c10200513501d0512041070071100c0a500c0303102580e003c1d0015400c010780c1c41240f00040c45601c4940c401a0342d0422a13a240d03403110800f5050b0308038540c07100c0c861450001c40003d417020101024083c0b41c0c410103ca08400701040d106003003000a0144990701e2440100001034124090b01c410383d030400c41c1e40320228a1b10180310700601d0140c0207141c1c840d1030301d0180a00d29030345601c80248100156031202459840b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980195971 1250 980194721 980194739
    0x723091c1205160206160606060908060a060311090c160c09182a08071d01060e100e0d020307060306051305060904030c0c03051c0f03020c1b060f03090f0601 69
    0x183c441642e00d114501c9440200508040000700192018480d80c03030442129640d802d410345005910200014a8110003070260304018042c40741c00c485180020403c0b246140d84515070703400703d41140c51103490348a0014500940710400c603507003527005c1081003220300d01914100c826030b07202c0d00600e0b030801c0c50010540b444020144030000905c1e0008041030208288400c1181c80d44640c2420742038513150000001600e4808008c00000340520108810b010070302c00b16104017030201640100100b148045001907644c503603024094055200c4d152a051040c0300102003000ca42d09600029010b12030f5a00015006501d41d025034142c0ea000c440b801007142035816440b05a031030580344154802088404140040c1c06045507483c9184551100c0d03505a560352640c0f4140b480d91003001c0d5100c0c2c094603221000b95407081c01d400003a410350904504041c52504216600ca08010000350b50402c11300316003006590303c00039103c421407800c622a03900e1030000c40b515142d104031200911a84181e4002041102e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980197221 1250 980195971 980195977
    0x110a050604061b02011404110d0b090a1712010501140723010e010207051e01090f051b33090a060201090213020306060f160b16170723091c1205 63
    0x6c1d6142507404a85c446440b1441c0b18403d5010b2076a00229104100c0b0026558002d20740c8910307000d2010304010403850812041d06981c07104118160072041080e00b0049d9003c46949046d524280b90506e140f0302001d8140d0a0780c407a080c0050400380321084042551030b07400c80041c00d0580132400078845040707404e900b103090340680f2000500c6900071194405038030072610314004030420720500201e20140b0645911115170004e2500b69115080b400c2500f44512100000c0c82c00564195940c1c0c0412010250426007080d50a8109051200c08480c3d01140c2c030a00381178500000c001009001019a40d0002034004d14024504030b02842001e0f50300c20501c51a8402d81b03120354809046036142492042e415180d55000400047c590010300d002d040105800d074686620549901384214045004020042d22085080a08000311360309a02080703a00d6032b11546599800c3c4400e9950600f01c0c01c401c203a03420178015864403c1d0442514840c074000a11180ca01048546c0185d0020040d201c50900442d5944 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980198471 1250 980197221 980197241
    0x1215040c020c0f0a1215050105091003030c0f1b030b010f0e010620010f2315100c0f051e010209010c03050319050a020a0e060910110a050604061b0201 66
    0x2821414040c03100d82000061100d404100500c4c8400160701d0783c50740440d070600c0031400c2c1c6041004020861a10381c980c80768030b000d400116241011444c0000c082c80c2c0001c21404002c0c00c00c00000140d0041115085200d0074203a03000d002c2e034602c1d1504662000f04100544029501c8001050000030b1448441410030113070345800c181c90040307a00b4860161082e80c00c01900c0a0307814103c488041c40c0320420300c0342c9120040101c0703000c85c1d5010241c402002503138802d006502011030750801d01c0745582c00c29007100c0c601da00c00d994030003039140f24040956820440010140c44410040c041c02e081003801710390200320750411200421400316648946080307000308292180801c40340c000c04400300f4081c1001e550b100b48507880440014116a1020080d1242035500400c8150040f6682100642001c0c0d9112050000e45200d07090900300c4002030420369000c003000c000e00102c00041541058103110505040f42c1000807240181064030b401d81c010507102c206403200900b04154070007501d20600030502c5074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980199721 1250 980198471 980198473
    0x1b1012060e16110a02010503190f05041502030610120902090a0903083111030d0e03070803090a091a09041a0c031306050703060f06090509010504051315020d021215040c02 75
    0x80130080d4015a125803014104000c0c2c0c1800060148050031107006400c01c0f10090040880c1606152800c003071010368030340c2c0d11000030740107000300840c68640c1404203503580300c2403a05041d042d40420f2140024160740382e019401031580c4c402c00c018585160880c0201c0741c400d5407845c80640d2070300504071180000c104401c8000c026070711140d00100d00e000308010950301030200300401f81d40640009203001d03c0e1103640004070b0b4507030300c2da040340d803900f48002c000401603c00a546040e03861000541d4020550140d810385035520000c022944c07140410480b140c44010381b940c0410f05080c1040004890501d0310381c1c01450107400020380c450060029030780640d1661050119042055070350601525000301140101603551400003030458085071413500030035113612226a910b040c0b80c24028400c1058001d9409542040140600c24000040c0e0143c0c0e6600308011207680540c00c0c8520008e4890b8120407040180041181c521100101124601035100340440380d00015214091005a408003000c400c05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980200971 1250 980199721 980199733
    0xc03040e0c040f1706010e131712040c090507030902010f0503091609020d06080604230a170316021f0911060706050105030f1b1012060e1611 62
    0xa0080c8094076040601c1000761400c0c20303107881d0030050766034140d440680070380d51068071605455070031310240e405003407041c800000520340341d440d03c000d08640f6a0000c2400303081114040c8210700c1201901d80300d01c08055040c56904250800c40046170030340c011400141e10f4035021030311302c40c082e11034140c040d41d0603102c0d8014403043c11825606500001c00c1d050081c01840307088441c4540d01070f00d0201800d610900180c4802985451501311452600702d00d4030f681c402420b000204d03103040010703000d8400e20a560444510350468182c2003030400b003001850944030030100502c0c44e001502561090103003140000c400003207071000f244e45001b0f1110280380100c2ca0a40c06d540e021081d049050014024880103a803000c8040210324641d2042c0d6058540e00d54840060116103014850b50000901c00c0005000901003456442108682d0000e82840b8244030761100e00303914000d00c884103603440050301c100601a5104c4103c886250100e60710100c0325842c05100c1185800b130b400c001542d500384401411 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980202221 1250 980200971 980200979
    0x20c03120615190c0f0c0e0907050f030a1b080303040501022709010509071403090a020415060906080709030213151208030a05091f09031e0f141908010e060301020c0304 74
    0x36115a04c01c0c019603010300c2c1080141c0210701442050802030182e4800c144c290b2038116109030420345907800c02807245044150100d00b50f500003804ca43e07625045080e451048402c1c0902d00003954540c0c5c03046419001c04410071050120640c09000c600390507418004101113680344030190032048481c0558041c6032a001880343e401d01e04401e5503c48400d0421001c41d01c00c801090082d034008440303800c150340c041901030086080a00404200c610144d4040c0544e07420210090200d481501a000c10040f40a00040c400b9100758880300c0210303005000081c028008410715400707801c4080b401000410705141c00103844c594881d02820268200310703c181503803142c0004401a1001420940740c0e4840d148003101903004210079410403594080c400030b00c4044901e800380601108415846035001d0900c20b40e03440c250081410000301e42c03c1c0c40c1200c41860644a0f44041c0d020390620f061110040c1e280008800e40c1029145044c0d403844041d0071969601d1104040c01c0c0d1040c0d5103d07600b40d03041400700308 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980203471 1250 980202221 980202227
    0xf0916081c12020f03042102151b04091a120a0212120c0a1203090206070609030210020309030405130b0f0d060938220501020c0312061519 61
    0x35010a6545088100b0903010044a001e90300031030400c002c082400000d01c402c001401000f8050b024252280c82d1030b00c881c1c110041e4440c0c00b0940100c01780d0390340c8000a10002e40700988802140c4540400645550711600d4480051006010540055420b0016000c1900d09500441003444030100107201c0a4569405d1014140c8000f41d05030300c038481c4064201c17101881101802c082030510b001042c541c0340e1810305500d144c0e561001181070600d02802100940c440c4c20444041075000744010a01c100107283c224586012000881240361003c011310845020100090013224400c8540301c1c640c495174400ea10032106104d400759400000046100700506140402e100c005026030300000300c0d190391ba100c41d9284d41000f148007034682c0c2010110301c2071401814140d4000c04085020821303520340070b880288014684c41d2180006081110340d038080050035011220242a9042543e07154440046c0c40c0c114444207441c000d01c40c030503025060109840c03030025202c448200400d04c40c00984290010303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980204721 1250 980203471 980203513
    0x601020f2a100c1209120b0915090105070e030c0a060e060403080a0c0c12050c1c0c0305070e012907020d0f0f11040207020109030611040e0f091608 65
    0x480980700390031039001e41c0e90b41d00020824a080b03580310100c0600451030040da4040c410b40e611410301070107036028092000d0b581c40606080e81d0110011503952141d100c51840c25050b5503801901441c8a01007250f00c5006400290142c0c613203440d1352030100c001f1410540ca0300c0180450f140c100319240800c10005204010419801801800181c501501da03241d400495014040d04004944803e41c02020030200c4001c91000742003911200a000b8000e40c1c400c0c0c0c0710384041410904c44c0c812680c0c03011510940312960882c403075002c280800b51039900c0c542107889482d20310406a00b203091a00001d40004224081c20201003003040c00d00072907201c1103000b00c02d508102c009907000b190500603040018585007410351414003e01159988200c94a03001240c40100803d050055005006075001070b41c200581c5070a40f948803901081303035941700e08401c180c0c1c0078540c03040100030b2928007406888001140311501441c0c00c80c041da421041e000c82d407036000e0300540c0304000680d4001000d8820490134500a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980205971 1250 980204721 980204773
    0xb041b120c1704031d100507420609020306060427060311030c030706022d0105041a100e01050d0f1704080c0907171f0b0904050601020f 60
    0x1141940121004096103555030403641107000c645d80724030181d418a5030070030f004a0110304540d0307954a420515401440307405419401454a00d40b02010340204040c035041030b0200a10b4941003080714259440e01c6264030b810000208268544640801d03501c0440c0203c2c0c3c4104005403a142c0340620703003003420030004608004a00c200c11a001c0e01c0c2c99580d074a00511001314020f2001101c4140103004150a01112001c007900c254000340042000a4010450070441c46041a800f410400480040d0f000103803000c4a4900715440c2000700801c201b40d5400c4070004100e40c00b034503d4183d9549401c0380500c202070141e104081040c4004114500d84415000400307131060049800350300742c0e0369540141712111003002101c40e1000c00d0a200c445c10800c00851416422078048185040c80c5d04003038008004241e12b0311405907001c0c0055440740e003901011403010110207a0950a90383c2e8248200d540e0802031000703206500b000b0101c0c4803588000744190310070a00c280a414488210181d10381d1059500795 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980207221 1250 980205971 980205977
    0x314011410110105070807031d0d1b0515090d0806060706020702180f1e040c1a0f0a03060e060f0a050108070c020d12090e0f04060b220b041b120c 64
    0x38422250700b400c1c0034040c000d81c0b098a500032242050800034054031300080d44084044400311560922040014072444031101c036090943e811075840c01d4240c600b94400d04040c0280c41500c00c000c991881d45003c4504c01c0b0000000d50b220302c00c113120119064031040d02d07070a5021a0500100c00420050b0f4000d108035880100400d038113038805503084219440465120b80ca0310203040800c0300480503110300300d5101844081f404110b15007940c9140c9105c4882c0980296404c24241d0079080c0150a812607004a08204110b130f196000804002c000e4199806a010754070880400f0410318281500b50101c001002425104031f40c0c20080111074486000b0140000c000b4002c83c41005620b888074000c0110b801800c80d07070796003031402801901c5203005600c18285809500b0800c098602c00045040e0050741c003800101c4d140c000c103c0006e99140000b104041e074114604d100d9110464554000003984009036414001e10710705010b94160101a2459040452803214480448150a5102e00d000c4502c0342 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980208471 1250 980207221 980207237
    0x5090d090b0327010b09090f1005060a0506040f05030d0c0f0215041502030301170d0c12050d020a0c020f04061815090914100612140f010f0c0314011410 67
    0x1110300003403d40600003a0700c0c0340d41d00c1d40a5052800c00c01c2c81203500241840062140840c4028101d56800301e100c05070700c1050365070002c0b814a60b0385109041c010907004041c2d917142e6807580c1c51418a406648201446403060604080c002e038059441752344181c5c2c00600e0032469005039000e01040750401402070708211820800410300801091170381c803890040740c2c01545c40350304101d0b0b801c1704030303078408030181042d80700d410101282980b0204005c0c0d030f554800d5043c1c081003a980400c1da058040d44a00c00a44d900125140840b15880110110030382d00171241070680410f00c9042c041203038003d01981c80c901c0341d0150910403000d8281c224042d060000c1c144289542c0d0f41e802044126402c1c804100c840303c0300c000c240f010418080000301d2903038540c3c91003000314503d449602800591701d000018400305040c005040048024008299860358070002440b20140000c0c0c1100140140000500071900c0c198800c5c5040c03030081c030468141d840a822402103488004104440201c07490040003c0000e02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980209721 1250 980208471 980208511
    0x7020105060d080d0b010c02040e01020a09090501080307030f020c0d060e061b0f0a090f120c0b0a0e210109050717071203140d06060306090e010c080a050a09050a0506070305090d090b03 81
    0xd8401c8810320360000b2b00058441b4901c40f030080c505125903004440a42c101380050044000110468048980c107041800e207c6403886002e07410011a40b01c0c0c04c2c0e2000301c10300c110b0180301c1250041007000500c81b0039200d0f190f5441c4d56209904040f604d44c16006201802170100000d026001002600c0d0907041804038039644807000c0c84145001c1e0040804402405c1c1d02000300a8108180000703171103188030070350820041c1e4000400102440140078810b664003c0c003903190341408281100050380880080c1700620160921036074a092503c1496042e80030220f509481080c04034039075040d00c015044222800c0710707944046642c24044214003008003030801c4040c000381c10610400d4000c020945000c2442c80c504500002264581c00460781c069040125140503581c0c050900c0e9480a00d1801c00641c94446014000081c034050707400418611511580e01c080c410005800740c070406c40365500340034503500c8004994407010781c8132084000ca00c2d0980c00303201c2640c0100c055580a0b500780d02085004080d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980210971 1250 980209721 980209729
    0x90e0f0f1018020a030510030b0a090804260c03010209301c030b1c0f080d0f0b210a03050a170c0a030e0d321207020105060d080d0b010c02 61
    0x164000241c030550000304c001c1c0ea83c0d00750203860303440386191594803066441c580343c207900003078028030f50308030255103054244c10021070703005940280440820700000d20004020390b40001440b0342c0e1081c0903115000f060700043c40c050080f90080200500303401c0755940c00643d40b40e101d00c0510318240540044148646051a0030400c1a29000e011100c407000b0100400001e000c0702c0c00501d4490141c0b1402c0c1d0b214804480000820550315801501e5501d040550b00388001c1030701688000b05180c0c0c0c04d00c200704d00010751a1300110b81124007240c88a00b410000c1d00c0301310340c000ca003071f80c20b800b46d420541408010a0040000e050403080e1400d01c118806c0f6400000342c12404125245100d51502140d14001c256141c884c49031200501c0005000341c1d0000c0d003001d4851507212110300c1440c0b241e00020700000f2041c000701445080040c2030103898400044003082c0a2800301e41840040d0f10f42030000c2d01c14584609a0745440ea00400000d150a0920310050301620782445c0d85810300841d6a00c02006880e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980212221 1250 980210971 980210999
    0x10b041401140306011d060d060507020a020f0402070308192004092904021c050a06080f0d0e010e190305060a1404111912080307090e0f0f10 62
    0x20003801858000c1d03040c2048240210901c055007030103548070400600c006030481c1c811007010b02c00e40d000d5401e07540d5004001003589200304001440a0f0800b02403041c91500010043c450364800c9071960550184c00050004034003c0020240002e520400070031402811000424100440001d003c9000c4114010740c2d110f0040012008140703c0300050100007040c1d0318841d80d20150110350540c0c4030303c0d0340c02c00d40c0080301c0c40304c3c0343d05446a42d00142080594100d119070510980074850140308510786031160310000c041901c11107003140959019074405210120b142c40550701c081d1524001da4440000448803044010034454000d0b60042c102040d410000300d4020085210b00010041c89c40c100da1680c040d01c0c0450200e6148103440014400011401444e00c804010169104003400780d950002405424090744102081d0a820585409010841e0b00a41c440c2d8100d498000d00142d03200c60b010303207030282200e00d00803840701c0d0070201e648060007002c031031b801441d400030010782c10741c1340c0c049421401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980213471 1250 980212221 980212241
    0x5040c200c010311070210120e070b070c150f1407020607050c0f0f0105160c05060304060903020106140d12141c11120c0d0912050705150606041403010b04 68
    0xd808100740c4881507078903004000004000030861401c1540a1313010803400b8011000400511602064074060500ca96000084210040c3c040b52003417580d8044004059101040681e100d078071040740460102800c00540b007100d910755548050311301c00c1e0a4101d8510600c01959070500f03608014080260703540304042c0070520301440161000740401070400000c4010780384c3d4140581a080c0c1a0002070381c000d001d8a5a401c0516407000580189151042d200c0040d030708000e61108002c41400180301c2d040d40811440c601c2600200035803501c0e9001c505203401783d8020680d00991400810b03001a2028040c0744404e80a420b140f00004400280e80040c0e4000d540c21014281001d132580c6548051307800f4507868441c80c40703041454184800581c05003040010301c4403140305000a52040740800c00d40c4019070441c0c101095402c544170041000f02154401802581c0030300c2460080c00403452540c500600030040103060070301c1c142c5003c10070a0305039180c0c908550306540e200004a41c0b80c071076015200e405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980214721 1250 980213471 980213473
    0x17070519030e0901090e1b0f030f0d030f0b130b0d05060a1e02030c1b070e0f09011d19110d0b04020a0b0f03070309151d010f110405040c20 61
    0x411401c00500a103c0c1d4160f0001e00c0981c24a0000204500c0c08142c0c05481488044042d003e01c24204c0440c02020002c0f920715098070981e0006122048081413a04000c00241e030f0601c20007080e141c5150a5685120180358440c00008500c4440426584900e4082c0c40140481c8200700c4181c03503da04054040751f02070849034130b41c410305056000e4080c4000e42e07110b070b0800450860500203044440c90240010552000221400c2050b410000b0803a002c0100348500301c0c0201c80c46d240501300c40300d4200780c030000841e60030040c5d4001030b25051410b003080bc800000090254801580301c0c0f9005804010050b00d9601c0300d010907054039100c40d5008950356025103658096805c0900c148007a104059000c1d01c00c4100c240505031503a0401812245c000c0c03800e20f8007188070b401c10b00702041540c00884900000916080024040e58480b1080b0450206650020003543e607119141c032046c2c0b118859040c44480c0102300500040c58942d0104e611801940f40103203058801d040d411908040304107800314a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980215827 1106 980214721 980214737
    0x6031a090f0709020702100c15020a05040f09060303020c0a0f03110619090314120f1b030c010615091d04060b0d0606150801031707051903 61
    0x721800016030744096540c500680095101d103404070b000b49a5036030320b0441c003805014110451500110030295801d419103101d4025401000c0400502005003c0440c8080f07004000c40d010748003400c2c0001c0c0c0c1c2821402c0192a02007210b1026108840442c014001d64000020b5081125400300f0b040703001000781c0d00011024014410b80c0c200d403140581d8082c0c1d4042d0f005035000200c134052920010910f0140503c0e0b41c80709000c010088440004011a485405a45000341151b800401e00329500046288009066030b0140b441032400781e449807018030030141c10b8280500d4800890410b0908207240a00d41201211100280b00b04811400c0000702801459086901c45100c02000c0020140c0c4a1400c2d03c001c2c40e09000e05040ca10072880606242d5028003040e50507690401105040241a01c44040b89944680002c4603d8082c0043c0ca00d00210031000700101c81340b2940f034480b2 = true := by decide +kernel

theorem cover : BRFrame.Cov 980035971 980215827 := by
  have h0 := BRFrame.cov_init 980035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980035971 ≤ n) (h2 : n < 980215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
