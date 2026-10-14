-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:41:11.360172+00:00
-- url     : https://prove2.me/submissions/fce1a895-cbae-446c-999d-7be8328b6ea1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619964028 ≤ n < 620143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619965278 1250 619964028 619964039
    0x60301030f1101090308040906030309050301060f0b0c16090c0215010b04121104090521070816150908041d0f07050c0a0f05070e011d0115020a1a041416 67
    0x24202c10840b0014104900215169128905283c0064004840107a584c103014800c2c55080800d160007810214020b0201c9410300100b0003441c1564860410b01c0c0c0404100d0b00001001444a60300c00e845213480c10080c2035032132034108040c04040ca10600913008149010603210a145a0305060700e680c03c0700585030500d8844400c04070060800240c1e11b03080d001e50701031a5a65140624480540640b009241a24183d0890300194440003130421458101b08406000100b100e400d640c440701c80705031b0360f02c240f2025041101444514006071000b0ba4500007084081000030006081601c584565038005440350100300030030b410086e00c8020b2041043c400190342103220f040205954605d80c015100007890950390040b04038660102100c02d0b2b0800302c0309010b880602900c0500400b5401071410418402020301c00a41d001801b034010125403103140742c8030b181c0c001c0010500c0070340e00c010344154141001150720a0500203940271143c0d18203003181583d03401030000e03441000f03075080500017890a2070b02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619966528 1250 619965278 619965293
    0x5040c020706082e080d020d0801060e0f03060403080103060501061b0f0f050607080108011b051605210d1a01051206130219020d0f0e060d060906061706060301030f 72
    0xd04400c1061104e80c040b0542c03940d1180c2d103115541003e242c00103900c1c100300312181400780d00d1203410110b60028644d10896940701d420f10381100e149003040c000480441000c61440b85442040070340500c60103050104156110f00c2141c12280100f604100741d90300c848080700e108002e00d070700010300c2890714450030210302442d590030b0103d44644034101c80c640880d9981405c00304201c6103240820002c42c01001402820b004100c9402c001c04115910071800c004054043e0103400b9040c42c00e4403124000d40100081048620030003040143c15003052400c03800082926440b0702c1c031181000b8240400303000100303181000078011303850584a0f5810601200b1803a5071045008005d00c0c1d0107000b10707141108201161004000d40c5003080d044c6000b208180c1e5000e40340c000000305400c20006c2e1049207011040d0f12410100340710208a55040c0ea0b010150380741000f038074058010f0045145005400515190040c0000d00c202a820140c0c41141da200c0c2d040282900007444041c0144440c2c114050014812 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619967778 1250 619966528 619966531
    0x50303090d0615080607050a0f03050103080d050403173408010e0901110d0b0301151a09040b0402130612090b070c0219060207050114130b210a0501050a05040c02070608 74
    0x1206140c1003c43d50b01c604103450302500741c80700c1d030100f040041c074800746c2a44a240040c05040c2c6003024011545569074801940c070507440144582075031707840842e041610540a8054a252441a81e16542058041642c1202c8145500380e24101c01c0312204003480140c0000c41d60a5200381c0b02c040f0940e10f003842040c62038030b00401e8103001d9542c1d942511010300d0400c0c094400c11079141e0300041e1506a140905007101c1f8180c0410390141c60100d01004490009019018401d08056070541c0382c02d14900490b0180105125680d4070074004a601c88850382c03c030301340a00b118400c0c0d40d04a0414a00c4001308100d40040c00d001e4403a07118440000c02c0140140d80c500c85587c400b0300001c0440101e0b0302e10800d400c505030011401608030102c01c001b40e41e400130325180884c08a03195103142401110100340403550381e12030302900310b0010804ca112a0345041130b46008455440c1104001d2403c0c094802c010310003401101e00c00d02035081c000c00e03503040510981c1c80c40ca0712900100030b518104041607030075100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619969028 1250 619967778 619967801
    0x12200c1c0f08120103060b0405041709210105150d03020c0d08091809100e060604320702070b04080303130606170109171306081b03070216050303090d06 67
    0x91418241c40050158002405519103940d401c54165055140050940d030035041c80034826400d010900c0040381c00310200890000c07281e00d4a40e507440e216004641044075400009038000c0a05801107194081908081c0c07007070710340f180d41e144440807240421017420b0103418054010791102014001c50704008451200060042103514140709030000081c40c100081008032815010920900c0002c00c004c0041c1d0740048407010040c007981c5075a16480355280801400b2511968a40d41c480c0c1d4030511396009014903106003000407007407003480c0046801a0303800341c070210700521400b100003a4404002040c0c60035640803001451864890381682a054588294252051a510071000a034042c160400c050301c1c0107510004103450410341480c003c0c0b10301010707145800140030050088800c3c41d0020712000d450041c1415001a140d00401400c4000c40c3c05401e00e60703d07000014803441c182c00140681c460a6070010005105448800b415120301940c40d40315040a0360000702800134040d50000c441000c1d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619970278 1250 619969028 619969043
    0x50705010b0a06050d060f12060b130c0c11010e010914130f091104050108060106050d231f0303021b150a05130807050312030c0712200c1c 61
    0x1600315002801500081d80040e01154000494070b420a40c54020303a8010310486043e2440c281c40c1803018440d448c00c078080107021655550300450140d85d242d600b8210b9090074601004281420f10f80907000c0c10050b1401e0754084d00041c510040c2d90b10aa480401c81d210607550400035506d03140154503130400b01150143d00400d14440d8010b10003a03407240c170280d80b03a40c03840460003400e54117240c0c1c100460b44940602079070500005110b105030000304903045441c18900b4540e80d030545d005204c01050aa120500380307001000340e610350404a48002405038140d0b0300c2c00b004130013800403143c03c00f91881c1300040151b00440e103450300b0103921895880503018003a00d54a01c50f545800703182403c1e40a201d044e80450b00100f0000700c440071540c42c0c00c02411704d4078000d02c4440d04020000b0780d03810a000007941c1002001001840590101007519000782c0d02100b10701030052000005405c81450801c13030300ca13603030250101002000002500706001c2c50040d013070400308955044003c01e0402070000580390032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619971528 1250 619970278 619970291
    0x703140f06091c2007060e0105070809150715052e2303030301090501082a04092108010801050a150b301f060f11070f03030215160206010605070501 65
    0x1400a681d8804e28038074a5016100381c40c00c1c201c0c003601034140e4240041c1000020711515000550480c11954092000c5a40d0141100d08803510b001c80e00c90701d91300500400c1100346181c0d8082554000c00e01601d000351540c2d141c80d40100420094012607094000c2003e15010101f00518a510000d480403210901e000408000800820b103580d00a1788400002a901c800400800c4828444041050704c00c0900c10950b881218500b19002d000c0e040c1e1611882d9240a60340c100201640c00c25404600c800c052803101c0001080989252824812416036500b84000210442d00398400c0200c0c012500408100550a0000500054000040b2003c100c1d10200100310310511452083c0032008030820750044a00e4001119880d54518004008504032000414440b0513000500e252006180f4503002082d800c60f03c2e00705240400b00c0c0c0c000d01001808104c08028164041040b0001454200c144101c689a1050510808510700301120050304558014024030348540e0040c0781060043c400403846 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619972778 1250 619971528 619971557
    0x12050c1309240b10180501020a02180703020d0c0e0306010b1c020c0f0a0b01030c062c01021e0307061a0901050d03020c030607050a08100b04090b030106080703140f06091c 75
    0x100c254240e012002c02c2c6035050f0100480d401062517409000b0a00c00b034088282164041030085114001041c0010150000a0382942c0b00381d059906441440c182030102881d1400050118075500740c0b140d009010b0780e0004640300d0320741c90450381560240c0030000a40380e01c0760100c0000b50410b5000f051980100024101c02e20300c1000325210450064156a41c0c6500d185094542230085a00103802d001d000040c1d414a042d221a8002d02503004280802e256803810300100d041100e50300002110042d02c0088922a48000020741801d51050b00102300c460f68800c050941c00340702000c443c1e4450203400062005042400d914040580b00340100c030300c00395003040002e04001080301d80b58001040884d840703801d90f43c0043c001f40c21103c1903a01c0c064040c2041d040311014400c0cad00400090b031351995600328094809500c820000c1c541201070762034242d160301c0c00044048440b190300300030b07100d5100515613614011032014054880c03c00207280c5042c08000482075201d0140d1038070148030500141f9101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619974028 1250 619972778 619972789
    0x50703021905030408151302010804151a0406050627060d02030112030e0103050618070908071428030b1e0f0a061703070f0c12050c1309240b 62
    0x1e0a02c07a01c0a55116402d10071054640007403003041c0820812501d00b0712044401d001c100c1d03050359030286448115580c541c2011a1012005d5803c6442c0c0391400765112070002c43c021100c8000380c0111804d00020341d4600402c9030034002d142c00d00c0000c0001e18000020000c40e441c488403104800340149040602da001d968080342c009038060302005a003e00b092040650280741f41e00045404d09003007110703082c6000030a051072900403000f10003d000901081d0392900510740100248503500c225800243c5079000c140c3c00b8500c0410207409022410440618011118039140102c0701140c05400c8252541e20f8003201d120004d4441e55040784c036071f00880000041c0c0d15100c9c0c4030300c0c61140da2021500f840300000d03044501c2d513032109040c030ac020390b003555200c3e502108a0350308a800c84010344105405017805001b00c80c3da0780c442d020149101e01c0c50420000c1c0421000310122040b2401201034400016800698141e050001c1a0314260000c1300c020075a154040c1d0007660741c0ca0710006070b4100b0391001c1207 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619975278 1250 619974028 619974073
    0x42105030406050c07090203010e043903050706170a0203071202120402090907081902031c1806021902041a030714040b0a0311240d050901150b0a05070302 68
    0x103000090b04100991040046400400006d402186150701d48841c014400a01030310003082d0083c60642808040d2500d4420003030f410342201ca112100d089040c00c1903c483d20b0380b008948500450707000080341405802e100004c1001180050059507c2c12040e8000f540024990f02c1400109803070008904d0182c070180407203090000303070582d1500345401000400c020090044170554003c3c0340500c10001c0101f1200007001c6e40c42a56030b141e1441e0310000e414814554920904e40030400e105ca250903500c048a9100050b101d68500f61f095101c0600300c0e141d6880809a02c82c64484c241420b0042c1495482848544007460b10360040001d020006810110564400b403070704100e1030008032440c5454828080000c804aa10a115514541d5004684030600004620808170680c00360707582c04842c1e402c0350010851a05255031101a120b0001c014902a03c0c100e031150f10342003941c6184640003070b0b2407041d900c6405181d800c00f0341ca15070803105903001000450460161201c06107916075402c00c20b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619976528 1250 619975278 619975289
    0x8100e07271b0305100f09110c160317070b0601050304030507050607020d09050901050906090c0d0f0213080f100f02121009110a1205060117040507030221030421050304 74
    0x82c90a0000c142c03000342601c0010741225a0603041510400100c074082c030311001101c1040d1000f0a40d503d149a40b82101c0c020030b29100d4050281c0360300034900740c00d86064201504c4c460fa561456054090100c02060f000d4104001c0c0844080b42c0480d00b10760117074010b150320610030303c1c2040ca01036169803141d0510b00c0075203154015a1002107030702035581c0c02c8030f03004024080c2521120388943c54100000c01250010b44010b005102c3c01000c80e041000300c00032102c00f26260442405907903601706001009520410008d50000c000b508040754005d030218504510f011800c0041c00f2805602402030000e0140340c01c02083c040e802c000c002000c0102d4244d0b0f51203080c500f524040b900d441c024080d0300f91800d02d2a520f041d400c0c2002201c2461b6000b071176003076002c2103a440c0020280d544d08010399240b55181c251000861009040000304180000c0ca07070306880c400c0d18182e010f070340b0390007065110b04403214405105801c2800b090001c461350b0070070858400c0b21404035150f81c02c0c0c00d0f260b80f421903101c1e4101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619977778 1250 619976528 619976561
    0x70c082103010b16150c0905240f040e0c09010e040506030c1216030308160912031803080f031842040f3003200c01020408100e0727 58
    0x4001b0181c0c6c2109401c4024441500c40300341c00a03070300211420091041d85010344821022808015000344201941c0140008480369a0a42011007100c02039802c0802080d0014044d01c0c08190981413600400d4018880a00203040248103a81001643c4413068074200302c40c400c10b16201d10110440304ca80005500035221a240d60410b5403001024003d0504140248900c1c8102040911503030b1070120340041d0035280c1110240322303050b400071501800e98000b0b0300c86103002ca4003080b4802550f0065000d44286808030b6241c40300305031907607112003104a118907414a02446001b40c000740c0e4604c961601410b601859103400b803c08104408a016a0b007618007242c1480280100030b8405483e402c1400300d54100e242011a4003540d840c42e0314100307040003c142d10b5894080c140b01201c810b0070f031400c1039264a162501004100d10b030013500544203041d1107201e070083d150860030705c074401c20402c1e201e070300c006d001031608109401c59240c0202c2c0c0350801114211303443c2e801013415403241e030500c0840c2561 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619979028 1250 619977778 619977791
    0x20108131b1d1e040f08190f02070b0a0e03010e0307030e311d0715031103011a0307020f0d020706030b0609010804060b030c06070c082103010b1615 65
    0x1850881d204801205810041c080040c0440c0102090b11000c005080c0f501103034540d075551070040c0308078250081c02014250003042c00d601c2e00c1550300c0d288074618a1176403600c90070300410f441203a69407164407403c10000c00c00c015802000c2d01c5000760110b01213000d00082265000308002ca4a5940901400e500054070200300c0140e1740b60480c203591049001403500070b45a480800701480500b680501102d8060750344d00c0205050303000c3c00d0488800034004050340e092503a64203c1064142d070007102d60000030702c1d0418104040c0e81c01c0c019603040c1c03100721012800c028400c500082d425400540900d0540c401e98200d00300041c0c0800c06a5211107455014010f440d04d04603003e41522510380c0c09900c00c0c00140000b01c0b032a40d114400b2584550001d1000c2040c8800d140403a00b81000350219941040340050182305200400c25100c080350210000c4524440f0312084a0301100034070909142e60b03100402c01040320341041c40241c00300c001c81d060492009401981c0d10b21170303800c07910f852800040d02d460 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619980278 1250 619979028 619979039
    0x70e060103150b0a050d0f0504031e020d05090f0a0302100507050c040504050309040906110403080c0606060903190302100920030d091221020708011802060403020108131b 75
    0x60303106400c0004030030740380c0e041c10290108018007801400801704240417400c10420301864201d00095840240300304001e04042c100109207040c000741e40c00442550f80d080c40c4c1080c0c0f0000d1120040005683c601e400c011b03800c4100020300d8030056503079510003200324022000d43d0307601044000c000c0813512034542e58201c603d4198107040074a80410f1156141c2002c101c0071410100071965020300803540002e0000384c0e0301d0200000c10701486240c000308004200070080243c3c2500500c0c44030307006004c0f1925940d80c082003029078850a0202e40e01034000c01a0340c010889001c0300a03d9003407080c015508088031042c0c440045070328443d4195003a1001c1001400d002c03241801815400c00c0c10f42c040c04c10803c40c0c0c50042c048034941d2140342c415071400c1010005000c11800d5040b004520001c10003004940c0172402035641c41c450180d00b01a5217017001e054014032081c0324409510780d008e0030040c08c0c5451a001035426a80c010f102d0307c0311440103440400080c81d200d0352042520402d181d090711107410308 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619981528 1250 619980278 619980281
    0x90d121401081b030303071d0a0f080d0315080c06031e07030207020f010c02091f03060c020c03120403020901060509130c031a0405060a03230604030c12051c02130503070e060103 78
    0x2140944d009400820520001603448002111840311608241c403c3c0d01100c404280c2c0c02e11341c0c6d84035010a8410715000300e003410004c40d121003418201d6030700b4010042050004102141ca40c454002598001d81c51041d09045c2540555030080d080180c68080341c62640c0d4541110004403051000694005020b03011480c1090480b00245000e00e0085041c1d40c4a0340482c01c10326018003030151043e282d58210340100744100c005005107901c4401489980c400d118060340e0740c00403091700c0d44603008039001c102c044555602a60100e9400502c0d543e5264a004800d440c0d0750701100c1c40582100303403e000c9581c4071441c0d0280c0401482c0e02c0d9800500d084d0b0701c1c0480100c120a01d0401842142414248051a0ba41c840c503981a40d070001040d020a03901c1c0101c455054402e00e0020b0800e000b000100801e05d0341050b2100503440c0500d82001b00950700c04001c645a2080168a070409401d003600201300302e4007603010b441c05005080007192015120310019240006540c4200c400502910801019580c503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619982778 1250 619981528 619981573
    0x3010e09060f0613060503010f02030a0c02190602090a052d040c0504030b1e09010501030308010e06100e03210c0c010f050403111318061103090d12140108 68
    0x328090a241d06064100c181c66450142001d4491003a03000c1d1100101101d80c0000001d0500038000c021074020129100041d41048030402c1c0c0c2c1ca8a85620510182d0000c90160b071070707940301100940768102a0b07865100a411103401c0903002140000f020405464803002c0500c07110000c0311801400c2c032107800790400951000c1040f80281c0c1040344900f10940c0083c182c03416031f0791007481026a6610020440300e881c0c443d4119006001c400c0d014800c89100c198800f6040c0c134001d54414410381c0c5c03949201c50001209079103058001c4101e00d82c1c240c0d49449102d89941c1c0d4100141a01c50030040c0400500603100407a801103000c4a000543c611104010404070400c076200303003407030b030951100b00a028041c3c0c0114840a0301c006420b120b002144c2c1d5486207500c0d001141070008010011507583c18581810180c0b1044420381d18000c0d1200c00d101451094034070682c0900d0003040018840001116241140c05c0c440fa40d141c2c03030f6451618507808481000340030b40040300080960b54454080280303030303a44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619984028 1250 619982778 619982791
    0x4060f0b010e010e060d0e16180b010e13090206031503010b0d0503070b07180303030501060f0c150207140303090f0727050405030d05190e12070f0503071703010e 71
    0x42603519030b100780d070404140c894a4004035605511b03680c0c2e100801000d00b4130310704a0a064010641c081030b00da2034040c2e020098400c0b251901c140001035124140460b20002001030209520003019036551901450307100504e00311500110b003080c09175002c948150010b40d50b402c2048449400050181401d201d408410fa008030b50200300c04505846a40e16071003020f4000c0e000405045c00140310a0045240c0070040c940049522074481d56400c004006050a000b40400240704202800310380c1d209169030362502e03801c210000c0d004101c100c0c02000950056504480030166030710f4003c20a401800a188610b90440280000d00011215141040c034541c100ba2031039079020b2800c0f14500c6500100d40c3e1046104040014140c990741403041c514012030034081c032890304103000c0001c0141c822131005a038000100f42400409242110300d601c80042d410746001d03144c03091201d5004126111040b090240c001c4050b00e14144c410b45440e60080003d0300c161512100004c01081046256451035501c41e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619985278 1250 619984028 619984037
    0x3011104080c0a0e0c0a020f060106120e01090327090e03041a0304030509101b03031a010e01050d090611040303111006060f181d150a0303080112080d0504060f0b01 72
    0x18144086101402c4010f490740c140c5c0800440c004085030b00030003400307070104040c42c1199050b60b510640148600c1c01c0301d0540170018104801c1c030314032071414050b002e0701a50580b03503040e490702c426010170700300c4203220080d84440c8401d000c0050040303404d2003942071549801001c0c40e40c907070800030044404a010303007401090000400c10000402e50100a441c5510360840e2002d00c84061014120f981401c0c065944c0b01903d000d0020404140d0554010520900c2d858180460300c0256001500e07c002110086800300d4002c200b0b2850320380e03e031b038410403140b0704c00c5030006041c10140b540031180703800c59001100850500d12820414007c10400006042c850742c40a000c01400d00c840144405101d0110a080c40601810114214900380051001c1c2212440b0508080d01c0307403046c1e03000c958040d81c0510a00b0725040c208a01070804d501170390241c0342c041d222030f00329074a055800041608403100c269400c0c0010700001000c0c08507030040324055801804c01040022120764010100da000d00c60203070500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619986528 1250 619985278 619985299
    0x911010c02060714030415030c0e01110a060e100c11060f011401083102192d12030e040f0b09070c08070b0c070302060c090f04020d020903011104080c 66
    0x6a480d44111000b06038000d088842e0359220003c0c83e8651b00480c1c020180028800c609040b09541c10752007100401515030302c12560319401c10041d1000209003c8402060f001100f007000403a02541155803460549070481c0d04076034218080b14200c0302e1f1048403e0000340700705038040c140241003002d140c014020441d881c5065150032440801c4e1407400301d00fa41481008400aa90951020154001170307030b18079040444c1304019074107640710120f400002c074030403480c08010480c4490000d50140c1640c050449032503030340012100380b03a40c052940d0b941611424001201042426240012000d002d1082d1030781d41e180c1908000b0023040d20540d81401c01202d191334075445a60740e40c150400c1d00b001d07140c10034140104031410050b907144901c02c0040e20904441d428000d030780080b10b0080c580d85009030b09031055500c40c200048028407890310b010b80e00c03120241900b10940f034036034028800d00b0142c10005203099010400310b402e43e819900252404440418100301c112000d0019481410040700d216040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619987778 1250 619986528 619986533
    0x604150e07080906011401090e04111201200903060403201219030c0804120e030307050c0f03070f0509100e0a05010603060614030c0d091a0403030609050103051e0c0a090911010c 78
    0x403c8d0b503101e03017592207030b807072000c64140400f00112651881010340005036924501403000e001c0d02c0360f01640302c8201c0c1c200c4122240240b05600b550100c501c0100030f80040d460f43d0300c00322034020750301984510750724802d20b00b8400c1c000100010414481c5000741103071154101064003800c02880345140c41814102040c03d02076030350251034254041c0e1300940d00001d054880b001141d400130410b05643d018440000c01c00d0a0090010310600c03000821074095060b085040141625000c862080700c10155600809201620305529890380c0304030100303000c1c2c0e56035076504000c000124040e22840c610031b03500c000501c2070a03070501804010304900d007403240c02c13a80394200c500b030345100003403100d112803102289441804401c0d8021001c51a00400444480005080280c480040c103507421408030340b400900150006180c01214100c0f40c0101c09883d40105100c0390164040800c00001c010b4020302c3c0f40035242d6904c501040024003d004000075451844d40f410068008004a4050511011b400c00800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619989028 1250 619987778 619987787
    0xe010303020a0320010612020f06040f060c03030f0504060e0609060c0d0506060c120d060911070305030712050112061d060c070503070f08070b07170604150e07080906011401 76
    0x2c4290f418a01003020310f0348001c21000b140c11451071200d0b51350a01c02e0010359103610b03a01c0905194001c450b41044003641c10b0801000740300d40e00c940000d04500c028100320381d9001d2030003040395074060f00b40030a01007000480c0004640b000c440c100d41e1990303a4500c402c81944104401c907130102500005148a041403e899006400341440d4019196104d0380060000c0d1125001d8910b550300d810101c81c80400d190b40e6119158002c0d00c1d03224840f42c03504000145101d141d006160070315496031030319460140662811105988028120018480c0e4124000442440b81c441d142c001c0c02c8442441d61505070303910301403068513401d41e51b48100991914031107204040106105800240d900710380b540d02c6a4601e030050a6005104010b401c859420740e0040501040310001c0c900640704048000360342d03070340c07003415200010b1840100c0c0c8203c1d14000018240d0619921207140c041c01100300d500040c0e030b50320070380c04129422194180000c0060003030155000040090b240035020241c0e24160717180032400000d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619990278 1250 619989028 619989043
    0x14040209131109010e0115020a0201080103080a0e0306090706030c020102040503150424060918050a1b030507031b060813061a030f01060503060a0209090606030601030e03071104060e01030302 84
    0x180d40c001c0100000100a280109000904030280c9914000e40e1759080203074411000b4071501c4124580210040c0b80e061001c81c0d001680d0ba4142c550441c16400d42c2ca818209800c400114018040d42200b951010b03602040100d20a40c00e83c001040c0072420480001d055a01034aa090b065a00501c01032000340e40204000000b030225003140340c1150354078106040440303040007403429160081d01c1803180560302074110a05980e9188018400e05042041c800c042440021000d001a007000300380300000b40110310744040c02d41c034146954080a440c1c2e2036460401e001c0e80e2040303a03c10040040311850880d030204440c01000c40e401c0181151400c880544001840644010200e0f90744800751303100c030500900306200290000d4215030f811000b10059500800e01405850320034800d50f00043d000c14114002c8640e00080500103412035118941032091a81020b030850b410700d03854811185040c8802c201400c1c965008030001808104075030140030480c0e4080e02301d00d40d845019401400465000140035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619991528 1250 619990278 619990291
    0x7050a12090f2904080109020f01080712091106040e01140d2a0f0b0307030e0105090309130f02030718120b0610090b04180615021203090106050a0f060314040209 71
    0x1101d40c41c0180e255030180120200030f1442c081c0040740120b40810154400d400d201d00c280c1d119007000700904010b440000040b2280c50004d9140e8480210b52183c1d9001455228400c0c0b40742c090041d8179800003146a00282c000048490303102c0c004100d840c941c4c0005082105017540c61942c10b05c0c441c0c0340d502d200d12886280c0e40000c0044840b0300c21070554100e80c4c074014401d102e041101c5a8507200c03842081e900c144c038003100184c01c00d807041d1600e84041c442c070760240b06000300542c94007071f4004c00d010702102c0c00c0b0b0140101640e5110809a00c94050008600c21801996200303500c900b01c1c001241c0300500703904440d07004032402c218980080c0c0e401c4502c6401c0700040750141080a588001182c0c005070b184c0200901d40000700c5c000540d49580141d003204480960b1091094030b84501580007500d0301011801c005910085d905401c0d000048007c5800240102c00443d0b070584403004a058010191700030040105480010005664140f188044040d14040032107018103040d00001c44611010b0000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619992778 1250 619991528 619991549
    0x60d0b06061e07030302030603010b09150d0206211f03170d0207020a0b1b1b22061401030b03010c090b0306180c0306100f0c030305150607050a12090f 66
    0x510b0031100482c00d6815554242c1200342c0d41e070342640c80c00030040d40042e55183e02a60030b1140d00c10041c60040002c9110f4140c1304110050a05454100003043c12420b8060740c10240400200340354a0440b0544003442c001d48600d03c01e1390030501a0005507502600111101e40d10a000030310004141a031004142e004150000d520f4410340f00c1264003d104500b0029031201203240c00048501005010b000503100600da11140110001480c544841c2c246086413180081118154190300e000343c00811221144998003083c82c130202d10040890380c1c541c00c030002648128680c02d8841d81e2501403440c2c2c04000383e00a00549005442c080d0602203203000b0341040c2d9001000040c025100c042e00740e012032402d050380c0f52103824203030307a440c0a6a00c141c0c0c140e8010b50900420898040c02410503036501c1d01c050307417010308161158404400422010b40380013600c14107000e10b022a6502c032000750929070701400241c03400d04024504a95180e0341e4421140500584250401a82106407031035001c50303840b1030b03e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619994028 1250 619992778 619992787
    0x1011090603091c05030405071e0504090b10090b010806060d06120506040209220f02010201150b0d0605010c030804110a03080a02010e010605040501050f0607020a0f030c061d0a120318080f06060d0b0606 88
    0x20b5200e00c003627880d08016041031614424600307000201c81654040c4020b200718905442d03e44003d00c05492501c18554007058a440c08200ca81c06d10740c00070035043c0c010141c0021025154109603096042c050703c26030711030f440202400f0541c03504000264100f211300d00908000004c0d840d413080d40200c1e50002a0401002c0c0d400c0d4019a4000c1d007101c7c44c5807156000040311151202c00b0b40803d908588401004c0625080c00070501d5409110b10000340d54264684114540d183c0c2d44045112241005113038021484440010000703902d14080e041c03141c1140c002003840c400400d07016086602503408248161308120041100340c48000d103205610380155038103a90340c4da5600119000d03250550181d0382c0b170320164000109200401e0103c40c255802540c4249280b0707609007400c3d1428000c1d9540d194061840103041025514440b03228860354842d09141e00e189030781c3c03040c0c0b500e404a50b50100c589500401d240d8547d50f00280402903010808550201940f03819483e25031300071b04001c1085000c0c040015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619995278 1250 619994028 619994069
    0x110717031b0310031403040e0126030a030c18060e010c061116020a121709030c13020c122a070b04060c0b0a020c1011090603091c0503040507 62
    0x21030544200c08440009503281030125030481401038920040e80e0b25004414000d0401c02c01104a5007220008c003200c0000b6401c01000b040b841d1641211754108806202d4901c00001e0f061020304984c0509850004a0062807000070308100004001e00c0103101c18210140401600100e0204400341e080c40d002c0039107002841c00200030040c110b6450f142000c0801c2180444001d454a86c0909200380c5640d15080eaa849100004080080b0000c00ca0b01c05440786e410031400b440e0143c0342d051001000c840380500071401142c03140005529031010217030006541c1b45001001c11112202e8848800454030740715003000540050503001c442d0340418214012200c110002c2046840080e01c56007104139519a43d808002d0109100400e0071201c00c0e80640000307002e48031520a480c41c0b085000f01610385001d20400e0302c001481705c00c5040204c000240036805090701c40c0d10181d48268440300080000c2c00344d60500710501140702030000c0c108401002080300140c8042401405c850341c83d03492514801c0c288 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619996528 1250 619995278 619995301
    0xd0c030302030a090506090c030106060f05030109090303061805011502030f09040f0605131401060905010c1101021906140606192d0e0108010602161202240d11071703 73
    0x4c403805441e03449845c0a000c901400415094020401180200715079966180140c90b0045074402c0440418800d0004001e10400c5400c4900310603ca4600082c04e079031503090800f0301c0050703030364442446d556460051045608210032028117002c140025030501200d01c4100c0c081e481640440303801103444429066040301d1a0b00800050310000300204039140b002d1035405c0007000b40850f0100e41240103000014030901070780c0c01034140c40e81039480340c0404040380c8440d208080514412811442400d1141026000100030130410500c950700210390842c02052002d20b120700a0000d1703100d10010001e549910740c00d107001002d02c41c618207060750402c0c218080346600c0801ca41c20900c1152aa51030300d0842a8082a40c03000d44100743c07079120035a41c03100f04c205da4402001164120b4102c0390351090080c48424801001481c2c4002c001c80090304285ca2550031101d00c0440c1c905108038003140c29600050302d4003404d058840c8403e07140742088456140d10b5109080e43d00c1c0c03641d8101e0008085020f01006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619997778 1250 619996528 619996541
    0x40b0d0f181a04080a030e0f120705060f13330b041407080a0f02071a01060807050c060a0507020f1501050a0b0c061501181203110d0c030302030a 64
    0x888820426401c41d100035903103201c050481182d0900c00d81c507803000d07207903800041c0502a5400001d0035081a00049090b8020b02a11445001c6403044080e410098202000411a0301360004242526200645401498280050040110b001040042106185424540b03450f03260b00b00400251208040040003203030707815054403240c08404082c2c0020703140c440d03030400c0c41d00080c151410854045003040c07001e2541c00c15141e8100241c1c804000c215440055040341c1c00806001070018501003050303466800d004400c0c40c0074204944030400410000d130f0080501603201e991030070101e01d090f003400d19042d140c44004140e00780240ea1003022551440c8200482000c401800c800c5451050740c0c00410065034509104480c450401010041848015001a1502c4840610042c000d9807580c044041001d01640651410012000d544101c420094102000201902c01200e048810035060040c4004100e80407801c0b030b984002d541c018501d0303100072407000c4550503180040e100d23102c0000440c0501207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619999028 1250 619997778 619997801
    0x4053c07291314120f0a062714191a0a0908070516080d0509040c0e0a0e060f010e030a020f01050d0603030504150f081810020307020307020a0501050f040b0d 69
    0x2903804080f0f0591800070300c40241800c1190030711900426031136a6580e51207140d00d06841c540200144000045180d04404c042540301d100501913040000d54555807413501c14815684824135083c51301d0000303824419482032410320080e09454000c42d4640f050341502081e0290245018800001e42010199120901d801d40c4045c109580780c0345414415078459004a2500b40c2c45008540004c004c0d80c0010b83c0120b1461036103906060000b50000c100060070000c0243c0c0c00e11800901c1b1420340e64904084401038158903018802501700f20013800840d07013904401c01d0500c5003003080088240e40000720a0403850741101e20b206004c9010004855a0050481c541000740c1003800110030950040050f0066034525040703203964140d5280110303045c00306034403c5808103900c100400c000901c0707601a01d2008012104030340e500c1d034682043c0b008a070302c2212440c00582000c610740c3c0462034000c241800812091901c2424070700d1061318003000e8400e600c500c4603600c0000032a08180400c58122115004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620000278 1250 619999028 619999057
    0x1b1e030d1d04050903090307080c0a090e03040509090d03050601020d12050a0f150e0a06051005070533091605010e01020a05010f0902280306020304053c0729 69
    0x1000741303401d5501d03046081501d202e80254480410070000000d10562000c3d401095144c4051a04003006c00030900415403503440d0204000c04601510740090071070154141c2d00050240070707041c2c0801000c03118081e000d00c0c110f40020761106240c940c03188203030405944d031035800505a1200c00308840209230401c0302e9141c6509145034502e030380c051103410b5421504800100c1100c4da03140f100e80001c40304240910742d8800c00e0200460303001441240503004042c8100304483d180200e405000b1040d02c5044001c0d6140c5441e000aa012130440441c020f410880400c01000c881459042c18914911b06000b0325040041540e0304007101da20810140b040b41d41c000c0000c200c0004080c6041c0d014048040c400e07402044c500e648210030309100301050712001a28109802c0365401c40d510b180203540301400c282ca0510403045c0b4940100607840c501600c10004000344011421202ca034804d40703c0c5004243e07601600105410000d0003a14000c456201c0803080007265004c440b900004201d004642100c041d42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620001528 1250 620000278 620000281
    0x1a07170c0307200a0f1b08061503030c1c02070b18010908070e07050a0c0b0f18070503061605120108010204030c0510050720031b1e030d1d0405 63
    0x10304401180600b000b556100d00d4103000b20400d0720725003000866500180d01602c10034021410254820001a01c100e4041c03110440b86102602105d00540005409401c030230240b01800aa000c1140350f080c40541c007450810880c0c2a10580f90301100241854907143c895402d03860380c0c0700348400c0015140a0407903a072160402c0f412030080340100050640424039500340401e04101c001075810803281e5248440c60190b98400e01110980c0000110b0030030300c544481e21100140c015552644141d92a00200b551460081c46481080b510781c3c224110310303000203005000d6130b00c02050481c0c0c04140b01030b10174044a16503c0442d030601c14500c801600034100b070004a00c540e81034004104a9006203103501480d40c032002000b8542c0c6101c081a0046082040f04a0001e42c9003402525405101500c100500c0c031766a0119082c001c3c0c80b02001e003c0446500d103200d145c81c2025145901c8260380031207282150b40c0c400400c0e5100315040c0b603070080c01103255500f0041064581007041c0203401070003c0c0440d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620002778 1250 620001528 620001541
    0xe04031e021c030e0f03032703160f050c0a080a0b150904210918150306020409022a030702010503190c091503151202010c060507081b071a0717 63
    0xd040c002d83e00070f07590256222400c5c440030000262070268a0401c00d416450382c07402d100700e1014104c41c8107642280000d001c0e6602c0782600c0c5403401d01190048060004d8440341d0301c0c04504100354002e0b014400c20b034500051043c18400540002c080380d11801003401900d0326081c1040d188c801080e202d074806d6040080108000410b0000c0c8000000962120051100c01c0300c1620b0322441401104400922070766110b1400241e038002c0380321010115081103640b9125250758069901c65086222074540000741210000128507203403446d8500c2500e850024803111183da0745901c03c07900701038100030300840403076600304050f10b16001100610b90200480c01e80b0007c0a41240c0240c481c200310301601017088480c1600a00a4860f4200b01c12000004079052856904201601c00f80a9042060052811001031030780e1040c28007480c07064442e1403003882e00c1e580c10722125021250340c186c1c0440a1101d100060404c4020144000780134410308020f54661608540c6110a60f44024801900f102803150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620004028 1250 620002778 620002781
    0x60709141306120f050d0302161106090901140f030c10030203100b0403060906050f06010804031101020f030c09283609050105060102070e0c03090c03031c060e04031e021c03 76
    0x660178440c000340e42080400c0c003000e408900500114500c0d8040c0c1134903103400101140340003200110000c1c0002e0515850344045040e40b00e003600f0024508507404a010000e14141b035108040c542e044004008102030100490b80301b8803107100e20f40615401001080204c030143c06003501501c1300e100103d442d1a600e003000b0024050402040e228280b80c900400c0105c446000543e10580042e11250456202c40d0703400c41794100501c410f9490381d5802d10144d003810700b05500440c0185850500c02e0385811070807003004445020f20340c00e0322403025490840c09161845103450000c880401d0398000c18020415000240007003115080000303044408840310303c1d61314a5000c512142d008070002c0001e903440000582e6640441d0044418414000c000503580311f004500443e800010b0605890303e0514a81c0800d203183c10400300e0010b02c0c5081a0a51885103d902c030758801045007012500150429803009000f012868407040011140d8400c10702515000704001014071aa9466140c03115000800040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620005278 1250 620004028 620004053
    0x1602031c091a0c1c170f0f04060b060a0804050601050405040c0e25031d0309210319020d0f140d0f0b1c06050c0403033f090506070914130612 62
    0x40121742c500c0b580c05d2000400c0d85c6030f1032041e141d200801c922078846a018016161004008a451036224075250850b80c4819016181071070303240e20b682e5020306042c5011420b08030141c00480c02503140004020202d10310340500b00841c1e030802146d20701e1b91250b4a401c194812030304400b402c14040100c8980c0d00310340c10b90110003880c0c081e05490900d080d02c1040380d03071a17201301115203910202c0302c010300500340310210b101400c09007220101c074641003004190268404640b210440540c00c1000c60001050304801070070320003485445d01d010300c3d141204901007203000d81143c00f00000d983c7c1004c030402c1c0b8840d45c4603040b845001000c9450b468804442e0500854001800f11055803d26020070070105205c000e8505407070349130701e03501f074021040c0c0c0c11300420f4160080d141c80300803010300340110b45c03011b01d6034101c0505010000c089038a16003030030300c249807600c05880c1c6030421035a90000c0041500d000802031001c102100c54249645c1d8210250000c1c01c01a0404483c075092118a1020800607400b000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620006528 1250 620005278 620005333
    0xe040c0e040e072304020d0c020a020310090b0f04021207080d020115030803010306151208090f1f0f021e0d0806090c120612031602031c091a0c 63
    0x3032054142d104920b0b034035800284541c121030b500244500950310f0700303424152074240001e000141410541c9540d002a1001584454003503040321803400f0941c181840b513641007101c4e601b014402c4586503900d400340c2c0f00c0b00a000c1c00c004816800032804560710019080c0d241d400782c04c21241031584426810f40c072000b40118010140d8170b406819031184202005007401c40381c1048640f819a0302c0c5890301d1000d40106803001c400ca0003d0300002c10884402c080542d0b4260103070a40b01d0716021106d0500145805100840380f08103111056890940c5424a224503414024502007442c100c0412045e0300d00600e01e090750081810003010710501e20000141d10306842d5042e5600da000340c4400040c0708484406417008410950100a80d001102000030120f800c81c2c00601000404503000f902c460a42e000001c80d000007258259481c015490200300081c128098003101e074062042030032018042940d540304180d802d00c2102a9280c1d80354555003030350418124501903680582107080700100180e030410300d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620007778 1250 620006528 620006531
    0x20c06071b030e040f020c0a15110f03130501020903010c0e180108070902071118061e061204060e1204060f0921020325090e0604210e040c0e04 63
    0x25480c072a1801210301c1c0180e609070b00d40c1c4244070900780900c07014000703038100d043d10542c080040300d0f00400e04010703490700c860003a00804a4401c01401c642d06860a03600294040c0c3c1086c8140080b0207418021281c00006280750510004100d142450180c021104c0155055181030340001c040e40d0003070344611009400f2208001c1d016842d154140380800c00f070040f808140e03c0504144032001c40c0f0360081c0050790007644ea00c6210051180007403640961071080e107880c5010364080c00141e0404000e0161364801e81585013130340b2122000401c045005400941000c4810500400c0a0060035130091030780c001407034166000080c108054000c1d070b611500c1103c00040910b140000124130072100c810a45071010100c0103511140403418152051030141a603250040c00f03a02c1540d810590003500300303800a0450805c03a140340860080484050a100400e41d4104404100001e2000030819140d4180c58100c648143c0025104880050103100050340080c03405082c0d611443d0014201e48021104a40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620009028 1250 620007778 620007797
    0x906050405220f03120c210b0f061b07030b040c0e040c05090717070906031103042a0b0304051005070f14160218060108010608010f060309020103020904020c0607 71
    0x354598562601020070380500302d014040c00041008418550140c0070349441588680e24076000701c111004001010081100c0060500b0117244801c2d0202001c82c0c070080c20003c0307601c0c0e40c0108030241b0f40b65014a102c0c1c100000c0c40342c80508007070101c1181910300e10485030016185d217408607804d031013582c054400c0d001e800000030380841e0703800c04548515400300040b00ca90b80f502040c0480c042018010000b070240100003030000300c000c0c40441c0e20a0083d0340c0c42c415018a8070700b0180031207000901030a0b41c50420020000420901d042000c074041540d062494040316101034842015030035040b00c0110032001045c070040c030000281c14000021150020072040d01d4080c2d0698401440a1064021480300c0c40f40c0b0710b403140c288014011402d401c1d2500c40d130907011a400038450b162040c001d41c030030041d010240896568458880381c0500882e00f4050780a5040c240d411240ea032080c0304901c10991511038420031039100c1d805941403410042c03c255141c001c8108030540704c41048800000140b5500c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620010278 1250 620009028 620009041
    0xe07090e030f030426130b0a1709210f0f07030201091e02040f0204060c0308220503071203200304020303120c0714013b0d0203040e0703150b030a060b040906050405 72
    0xc413540540c103410304d80040740c84c000455413103808c8813050900f03101c1600f07440d0b007d8400308294144225840005420480000c01100003100c01a00440070040003c0c410125400404000c54003203a241c1800c1903280e45180c5030490241011800c01012003d00c158400c5401d1405440b800000e8803c45e07060160b41d1041c0746040884c0160700c5000009600d600024020901070001d541d004003003503a0710540c685d56225043c0542c8500d000844090f400054500f040c0041600409000070b101d15080c4036003400800d5244000300700c005034100241000003c50110f50301007044522641e034441600349940390050420005802c110400d407034441c485206e410022106101d10712072018140c10344952901410b40080307580c80d091078051420060700301c40002000c801c0120350580403056000b50790761801c0062030f240020340a050001458100481e540703d6018402d001e00580c0e4404400503200c0ea590303400403000c0c1210354080d445039440010041106442a004002075503001d8409004d5030f103030038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620011528 1250 620010278 620010353
    0x2904020306010c0221010c1701050909030901080a0216030c0218041e0303060e10030c14030a080313020a180605011103040303080c0f270102010e07090e030f0304 71
    0x1160311500040c244a40310f0010700c0c2403030196541e90076000036111301e02940350b00d4508550304860070f01c000c01c40340110741502e4402010300c540904000c2e0340340d15075820100740965481c003413800800d05000710b940000e102d20f001641a28610411008010994640c5041c06054040f0400d0140d00840c02d9034185541040036042550080e40e02c485002c445040041d100703a40c492450104604064860400042500b0a4414035001b0401036003000d60141c514039002809009a5001002e600c0b80b415007030307415690118a9148054001c0e1805540c2c1da0f0f40214a901c501c09104d000b0340c001e5122601144d000c00440d2200c15503504000c08203c0c003906c810040d20b8040c02c0407402c080b207500c20001400020710401c40d0607003000141c6401401e00312440704600280d0851044a030442e031562080f070a03030a00d03049800d080c0a400303000820a0300c16400045032601c60380d00a914503113459a41401030644101b00701c501c0c481460071035070780b030742802c4c038280c3c4d0840b0080303c1c0c010103aa03880080d41080c9400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620012778 1250 620011528 620011531
    0x40b090a0f241404021201060504060e060a05010f02060c0d0e0307030906021009050304050f180a0c030c1d09070513080606130615120207080703200d0f11010f29040203 74
    0xf014003030506560355900700040c02d1014a00c04080e552120400100703600e40e40182c802404c010501c05502d80f0300142800320802e03043d07000504000c0031105507090030750040b1318690450003180c606541c070620503602501604887d2001c0407507110006101d001d0550001c180c0096403d84e909070384496400c0d0702a20700f500c90660014201d038004110802542c9015070303800c1c0c440a0050040040d0706c2c416001040000803c44598164030746038012108003680c10300c501c1c0048086418603100c5400d410141c040103600c1051190b0080d100c003408102090301403420769512880c0800f000c0801317030311004042d882d50009e881c021700941000196015102e0140141e20a581e41c00c45600c548620102040741d5503007003401d02d03650ba03650800c104004524000001c0030201e004c6e0300d03901d0708001c5c0b02401200e8607848190320303401e07900403660080c1450b6200442d074048500c186408044643e03069207903801020701e04108c81d1183c2c500002c4c0c44500b10760750000401c0510f4021440c103445411014001a0b100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620014028 1250 620012778 620012801
    0x6020a0201150b0a03050405100c180f0608060405091203090a05120403030c35091c0803010512031c0c0f030207030e01050319330b03040b090a0f24 65
    0x1041c071080710310a111ba440b117a0b200340942c08541c00c5007488481001101d801a1554002540d51980350a005549030822801842d0004034606014030300500101a94030190900313100301c2e201e00c0071801c8610100b03c03120b2517100340341844d592070400344081c2d03954503d85e50088505000780d11343c0c008103034001c50540d0122901501c034441c0d0544955200c05041501c5009690400242c6034403090310003513903550b508484245841e41c1e42c1d4019038010010a50300003250703085d402d040409208001070700482683d04442007503807041c0c8004c9411241c282140107440070510500e00340d03504541c03415544d4201e840000300c26100d180805d811040210241c1c070981c1e2005d8041000d020440d8104d522640003941e1083c17041000642c0c800c0704600c401c0944015425a444484604d00048500103a240718103540880da80c09422132a480c1040d00c110074000200b01030107100e108030018601d90020b201502c44030b80d00284404c4c0c0190130740307840d104549030030043d140326017205040c0e0401d80c503092094000d44031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620015278 1250 620014028 620014049
    0x20301110d0b0906100302031b0403081b0102070c060f0c06021303030f08131b030209090c09070323060a0503030307020348011b020604110303070213020c0c060706020a020115 77
    0x3105d00d103058010b54030141920807131100160f50f04003074004c07280141014520030103000d03580320101034100800b0300200ca80038806034410003606001038400c1c002e04086071181e0400c55520719180e58144c440c3c1519580c090309440c000110a00c80d9000c0d00f107001c007a02d220792030310401103681a41c101c9420030200d913009107402c400014000400c10f501e420010083c0ca5080030786440e51280d001c1440d0740c00a40c0d64042d9070744881c0311041c1c50711b000d65110398020030601e810007982041c2c014400b904130840c081010440501d03004640b43d9299100407002410000e002c80c2d50384c0c20301e108000d6881c3e00c0314090311280003a0340c086d031008a081c9160340d154032000c1ca03c0d008043d105410f030824582e64280070b8500700e65a480a2040c070307102e030089202e80d07010150007402c041e1510b401c1401c841140500200c1c82500104094001030b42c038401808018801341c080144c039100d8246016180c6070520f01c4265225101184801c1041566002441c400740c03168002d00034000f0441610941c801d140c0a4450000d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620016528 1250 620015278 620015299
    0x90e0109020405010605070f1b1211100e01090e090102130f1406040b0405010f030b092a040b040e0406060305060c0a180803041202190f1a0c0303060d05010207020301110d0b0906 78
    0x344862782418100c25034403100c80e030043d5840d1106000c11002d00d800319246025454250254076000000303480508103410728404064004000800200c4180240301c0381610303417008a00d50f64025815119074011151311201c21588440c401c04101d803043c4100c2001d021002410381c4c2c2800e144050b00c0441c2c4404092604060400006507082034980003058200f5035030740f4000503955035500031a4020114101c01024040f9212180080303141c2000030358882001c10042044100e009008036021100041d0410303106449500c2d000307018100715030000d0b0280c4541418026034202c2c0c0001400708841540b181c40781c2507807560064000e80d0040c41105001e8009220401c407600d06210081c609a2004080c030000000e400c240c1c000c25084c0e508449483d5595440030301004048402000e450030f1704403882420f00f4051480203540348001403200f801124001c000d8400c0190075010f454016600400a114041c4090000c0141390000406014418200000002141800e12126020b0000a000d85a98 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620017778 1250 620016528 620016533
    0x9060a05090423161814060c07030515130c0b0a03110705070501020606030a11060f0c030d0b030c0409050312042103020306010206101404090804090e0109020405010605070f 76
    0x9a0020728200790042d840300c11042156030311125000c10068401d2150307605082010115460416551280d030600420031211020701c0c83d050980c801310f40c2c1900300407441c1600b14002c80c0c030310b0194040d11400c503c54580b01008100000c9070710060481602904406030390f842208684140e45030340050940f031190203040c454900c1400090104040c10b042c007192901c17880d00781c5000ca0b03215142c180c8050b00074220038071540d0380c140f00c140d8111500302c0c000d1489080315160b071851481c1c01d0b1099442041d0004601c1044018401507034040c14164081c3e985410000004001030401d24425510a004003095146513140038841d0001d07a54020b0b009505003180c0007000b451a42c0054425281c2154407818508810128101501d4201c03043e9005030b100d00b090350001e4a0820050030280b40210419014410031841404502c80c0d8035080b1000310b14128141040e9500d8411a0401480b50f030a20500c0204101c05401c205240f40c400d80301004180e91300d58044489000703030080100140300381c4541901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620019028 1250 620017778 620017787
    0xb04050a201807030204151d0121020d0b040516200c010e03030c191403090105180127030203060a05060609010f030f02040303170906220f020d2609060a 67
    0x207003c0c0700c1e414010714054a1340100c1010800c1583c00e0000511182e888429030b1450854200ca1203200b0f0070000348040c1c01c21031207030200c4a50001d103480e280d408034013290810007540141030b1081d00a0030030001070030500c55840d001c00591007510089220814400030f0f90705281001651100550050161815007400458640d01940600c590610003848100d111b00014002d00f80003080c0801d9103804d045407460030480040800b40282801d0300305200d110303110790b000342c22030703500c02201c904006514107035000603944405d00c8003020303495244001e01c80b4420102d00c003c0c401564021400c4800541e9601c140c1e1003612000c440e0650040d40a1054400c2e079401341500315800760103410041050360110030102c049809c00e920641c00a00e5205002c01460b9201c80340642002020001c0d000720314008500b44038032001481600520150792202005014030030710088002a8001c09518100c003141c20181c01c02601000440e1080d03210080349001400c020b01164110030001d000c1d0750420700e07459030030386d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620020278 1250 620019028 620019031
    0xc1309020a09060803030108070801020a05030106030b12010c0201020c15040c03120903060e0a120c0b0103020906031f0e07060206041101120b030f0a06180305071203090b04050a2018 80
    0x90708006030a03404290744a0740d000380c0b405080b500e001942c0301c0d80b51038041840c15410358805222648100181c001181e803010450f410b6841c5810301007968265400030460b0045103641d07200303403940780210b1340c2070980c2d040d00100150780442d02220b01da94040311090740b40140a40d0000d103c4181e940c000c000087c2c40c00c501114001080c108441e184d681d82c3c03100303000d4a10078511107004d50028501d01c41000440880f0395485c8601c0e103814842c003102c1d0350380d601468906010192140303412400065681c3c2d410483c5880440c902c1500c240507025010345d1a014091040c02d5403c03902030034002203501c0d0700c0014403a20a0380c0007034130011001000350064950308604101e4048154803407505901c2a101000020b0140c0f41480c01440b0051444c00c010044a00034814401205450840342c0c010a91003029111941d0f0000c0301040010488070050340102260b240c01441401c082e000c00042c40400700e6508100c0c2c0c0104c17042500b0035034640d5850540c0940e4882d0030742c02544a0021903c0c440c000803050f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620021528 1250 620020278 620020283
    0xc090f03060e01240e0c0f1813020a090e010b07170901022820100e0d02150c161809050111040906060221041e0e0a0207060e0c1309 58
    0x10389411103034807049505543c108138071410202200c1c200034219048600a6100c41100c0d030250406c13000075504000c1e0b11451455446d01d8800189250030355443d40e00c10b880309030700030b54110340c4ca11404001500d095030a114002c1d00c514220700000e0700441c0501103e54659000003e2a60041c8844400940c3d070401c40d00d440c1180b0503030103044403000a00112811040e45120302c0203014980d4580000441c0c08002200e00040d61005901210340360070161a0200502d420541c02512484002c00c00c034003030309078002c7e500420341c1410328640c00a100c0184002a84407081d9002c0b201c49403c48444100b251060661180445000700c80c02c1c0701c2a03100c44811840b4000100d08808003038150f10217500150043c0441d60365800007080560b804209154501e0300c8030b5801d05014021091205d080c5c0210f11889495602d51010020040d1015004002520a0320400155810207411120003034100d4030040740d181b4980800c801c039146001070141c00000008040707005804a58004a01414a20108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620022778 1250 620021528 620021531
    0xf1c0206040f06090f0b040203010f1b0c03050d0612021206040201020c090613052d09030d020c1c120c0e0a05040b0406090e010c020706231e07060b040c090f03060e01 73
    0xd00042d4103c5c0000201c0b40c0549411009804e2500401d800c541d04081c40108080ca00218804000700650086240a2103424191041040c9060a40b1284200d071030602c0b4840c07400501259036881e54068140b0036000392002e8030880c0c2110400c036a40e40c0203540c0a03025900c903060800507403a02d040b40c2c0354088400303031100381000c0b0558594000d5520036103801c658000c0c80802c09103d10200a580424040e0301803491506090401061391684940318010181d680c00013000c50840d4030800c02c02c20600c0d52070140c00b0030039040400080c1000415400ca4004034140444002c03000d1007035031b00d10990a402403c00e03040c00e00d841c3c00c210092001403240f0b84c1141d118040007400d00460311410360005009000801e9100c10341c0070080c20f04040742c00c44814042d2058004540c0c1e041c407070300010345120341400c49980d00700c5000114030049000d250840c1c03011001642c601044401c2c1c000304041744003924188052401c10400340d03115203c6016550344c0c81480e0104101280940c0c000d988080c002100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620024028 1250 620022778 620022791
    0x911030105042003010209060405120a21020d0e030309040e0106180603020906181801140403050d200702010c0c050a0b040e0f0c030411011e020f1c0206040f06 70
    0x1080c2034807011181654a011505054070701091410126111100e045000f10329100607500020741901480c012540190b201c0d4080112102c410441d0180458020001020250702d52014000541d00e0803419001405152441a6014044c105ca401b12001c000c001c5c500700070803030003407100600d00c0352601c1e0460364807154000b40b1310207940100c80c2b40780180000820090b0030350040c800300c1c22000c2c4c41e441c0070380111800c0442c00e404203800150070800c0c02a1080180c4210307249940944140709040240c0c41c0c48a05000c1056002401400304000c0080141b0040c441560065210389020780440300724101000f00b940150701c10030150003014424800c1c40c1d140794403200032032004003036600034107d2961700040920807461b01e141c00079400782e81d00c69038185e246008011407555000c00b0780018001030101c0706901003680601d90405c0003c01e111951582412980c400940d1111600302442d054014100c02c0f03003c990480d0090f200000c00c136001071406440303958400242142440e801e40c0d28964600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620025278 1250 620024028 620024063
    0x90b0c0c0a1b051503220503210603100c0807051c1803080a0b061602040e0f010615020a0210052a060402040524010e061303060603140307031209 64
    0x220181440401c104020076020300302801e0240002550300a032071071307550600801840700304490103c001800c40c0380307848099030709901e0864075500814110800342c000e441429031300b400c031104a0740e21890741182240d0001d980c1007024001c0b540141080400070340b80c800050740c903a014000800c07000040c0002c08590003105914801240c50711580c94148000c20031250b000e040d8058201c5c5c2c0c00804c1c80008102040e01c50000840ca482201c58003907622600325205401e641c0d656111001c400b00b40e00c04d4580721222031410358000d010b180240d001d90706018a84040042c130004035001d07072580c00307816404000d0a000040e500c40d0404080c2d00c000011180208081d010605403000015003a0401065107007000c1c4100710030f4903c0100b410001c0501c2e07918086110810101a1031210803e0031b02d00da12c0e440340000704105216002c1043c6410080503030000800a05600007002c49006003a2154000548000030f5240d00c41c0240183c00545080c00c207548a440507841100034920800c1007203480708082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620026528 1250 620025278 620025293
    0x30e0f03070b0c01112b020c16091506081f050a0f0e06060a17040501021e0301090c1803121707031b030b0102070e060d06151503090b0c0c0a 62
    0x10b40080c101c030100071548a03007650090003100c0c0003c00a003002c509204c0383e240005c030410361050003e50403001c0c032640c5001a0710164100c0f58600b488505a844000c030240103600e40c52a00e200da00103051402c40e1054082d10903240311011303601c00d5030700c80030300e0307114800f0440015615541d503901c24038000350002010f82c0d07054013480041c07601c0300304c0305409403030854800940c1d0b00c0142005c0c042d0a040042c0c1c0401580250f0101c86101d44d8443c0d000641c0340e6041081c0203015800e450310440410b803080b14031a4151101450403100410400c3c042007140203400c581d0502407100c0038150382a440e4042c00001c1c0c0c03245001030092001e207080204590300390900b904101c1c040da0100046076030741f107122000d169413035143c82c4400850b080a100306d074400d20000356104128401e15030036040e0100824140c0d82c900d00040c515030b410580600980c5204991013880c0780680c441d10403002c200325005080d0078000e000d251034050300542d02d41050b40d80c83c6102030709a030159010400900070b40a5140005485 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620027778 1250 620026528 620026543
    0xa181509050906240408240f0106091223011409012d0207081204110f030303071808100204060206010e15090402060c161d01080607210903210e0604030e0f03 69
    0x1c80400e41c1f400c0d415190b450842800c00fa00ca80640e140000041c000030b83c02000400c01c8414a109080c5c8500140c00c008031403803c0003d904111a44120701c88140d4501500548040211000c2c1c002c030070b459070703035481d4200e0b1f2100e40c9000004068420583c023422100601480e1481e030000054a0f1055640c1c0c3c1042c0d03680300d82a02e4414918207401d01c005d01c40b10f10014004550203403020701044006000096130b90100074440003c1005044d69100c210741e10817100300007800d80408607203803050100c400c48003a40250080c0c00052081704d00000741c42d1941180c0b14098a45171040c3d4491066440500155020040c0280d0300802d080080621882003085040b8a0007030340e010031002c1d81e003001c2a0a5141204002610752404018010322002d8004202c03690403160702d00781a01121004441c040b164100d241045010514000c826424103802c8410700905e0b445041ea5440e01224598001048800000d504091540035034006800203004102c02c0360040b40040c9881d0f00503441c400000e00d803140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620029028 1250 620027778 620027803
    0xa12050f210105061e030912041706090313060507030905190f0803071e0f0f12080c0a020c10050d06230604060f050a181509050906240408 61
    0xd00d5840180903480080c05501621044030713a1464850300040401c0c030142c0d4000702d0040d0440000100740121740401229080c0e02010b0405500c03195160035009103024501d100d488213000700c0c070005004010100490f50802c5452126084c11802c02c00112a40d41004004405002c01040c002c2115680e0300c03a01c201000f0810000b5640505001c103020402c0640c3e80407000c180d100b405800002840500104801c014580c0b1502a12503d8101310501031049440501143d1100039800140320b61200401d510085945427107510791518681018070388100c00f08040140c200755121a002d1804011136188560b20f49080c50902100001e03c2049036607a50000200034520b00d44201142e03000760361072051900c01c40700142420f1034050003400038200d000b181320412200040d1510140c0c0075444658200803207840351040d003500c42184984001d16103410b080418140c90f000541d074900004042d01c101c0c80070704004201d4541c0f0f80c642d00c1201080c20243d014000500c40425940402c00c5000341c3c444 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620030278 1250 620029028 620029057
    0xb04031103100501060c14010b33160602030a060504020f0a0e0411040b071415010503160602030a0509150c0a1401050405120c240108011d0a12050f 65
    0xe1108101482d01d656000c0032580307a030801004204960f0089843c090740ba400a40320301d50680d11b030301502e0040c82103440c0f06522550301900e00361005a0700c01c0003400d0003046502c10500c004c030500c01c1c00d400e00400101c0d000d9406030340031490009160340c003d1b41c5c10801030322010484c251514000340c180d8105012044c400e51021407860f062950250000d00004401c1e14204191500d400c000d5409200d01d0007024039004000404600300144040162950110b520954031b04103000480c07214100001e1042a10910030070480c0ca40c03101500d070b0480200c403c0b54004628058918000703851581000b11381d56408524100c4406c5e80071a0b0700000c041501c0c079040505080041458030500081c40c2240100040c0c1c0741c002040006000040c0c6807200226040d03100303845000009116107407031051041104e1040e040c564940300d01326405007a41c140d8010340c000f8020400050f15404c643c40c1161046043d560040c03d904011911841d0301a0441840746042807601d000c0e400a802d540c0e02080c61180501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620031528 1250 620030278 620030303
    0xa14030c010b150703030b13020c071418010509150a080c03010e0307050304050f0d02040e0606011209020f090a1d0705011205130212010b0d030c02040c14040e100b0403 74
    0x44080c854070803450b50031100c015400000040303400c0c00e030141d000010185a030301d61250140741d9980da07400003080480f410a565980107601c4040d100c43e2284500d1510b1001001140003528224841c04222109007112a1180e031801040007039071880070786900360000076081c8421560310340110b03800190080c00000c02c1c0807500c00c428507003140d20143c40d11109420600000002603004000c40302206e204031001056000e503400003a1403c504040001d60041c0b44c030a48071005d00300850010711895003601c2e012030158041c85410305890845000941c8540402c1c0300c4800c62804011281e00081c2c0010000748410030091117201281c5400c4425009500c0039108100e81d40c0e000d8a981c3d032080c1901c505110508140170004148428528020311801445408103580c071000d500c58421980020b100c0583d0300c1241c10040c205500b81501039014038188010900d07030360b0107800d030100c01c6400d0700c019a24140c6043d00c00140d9078406004820141c89420303001600707584403009403002c0c50280c0f0161040c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620032778 1250 620031528 620031547
    0x70c110109170106080601050901050d030f1e1206050103020c0c06030c0f0304140d030c05030f070e0616020906180606071a0412030509010507140c03090306040b040209010602060105030d03020c0a1403 88
    0x50100592040f889800c50400500c034a80fa030110110043d680b505008580010981068a61103401b50700d3f1034a48449000e240446030781b14807042e81403120200c040081e29241c00046041c3c1c41b514190980c2e42c0d10440c031500650400c800255404120742c9003107818200c01c403091102c20ba0081c1c0b0280da01c0095060200000c820a00114540c0b10b1181410404c0041c0a8809851400001c0820341724040150001d0790150040c0035031000d514004281c2036640c19240e103640a4403a820790141d024201100026042d070030072190846c10502103e10305211a80c0d5a01002150340c006c00045440c00340c0441c0c2c1c2c9a01c00c82c50b0303840601492007052080c0c18400302c0d003001801c4904c010856109030b81000280500300350030080102e46240090302082e41c0c5c1001400003413942c4149107240303801d8441c40040005000b40c10741e42030b003e1071080300c1070606a6a140d60490707803000b0a00546915400581d0388080e0507009500802c507001c50f41c010349a00c0d00880e150700c0c0c041e00001c1c000d04065000011160711 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620034028 1250 620032778 620032783
    0x4050601060c0f02010c031e0f120b18180607030f2405102007030c15090504200c0d0909091703090f0319080105010305070c11010917010608 62
    0x75240c140b501041c094010f884265501001c1c200113418441904d420400385403003506c601c0c011803103c110401c40c0d50301890380140180d090115202c0000c0091303040c410b00320050b0066030480b42c4018200c003203003201044185031b05a000b0300441c00003461036a0084001d2010302007540b140388070b51000211050707894444800d44100d400441c141c0c14200601d84050680d4002400c1620740c00d4850000242044109441c03140f0100718142c000d05c44800c81020604000032218143c9100b02101808695901c1c00c580d030f84c0d4440c0e1400030106004030018071040c1420340c084460030a00790260219001240345116066028540c1001280c100c00d4441c520150801c3c7c0e950b0040190000800c50a03c95485110203080518181c0412f0f400010100360181030801502d141d241c0050160380c0d030f42d03405030981010ba02e1426060303404600240000201903020b40b08d8184581240d44810304100065583c907890708000c7c43c15541800000305010812078500f900107210b08002e040000788440c01c00700c0003403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620035278 1250 620034028 620034031
    0x180b0d200609030a0f2910050d080406110c130b19120f0c090c05030a0507091a071a070e210d08090f0607090608060306160e03070306090803040506 65
    0x6004050800107104242c43c0003882c201e400340c21001c4940c0350703c01c1d49840c00d002218031507404490800018568494103040c0d05d818020b011040300c0d00c0c9041e0355a41800800707148004090700100701400100205c070301a0b00510075807418102900c822801200004602424803080d012146959680741926410f04840b203540c0c10880700316070780e9610301d0008145003080e0703100c40c010b10700700291381100f0400000351008405000d00c80d0041c0140d81050740300078000d400071101440d0356400d100214480900441494041c0c03021440801045800c3d0318140c14254000c400444042089103171403808002c00e0450310b80264402e0b44d4540c440000c000030065000c0318404041e00c06100745e81e01c20040f0780d0000b03c2d0352460060b410402e20704d5644000140c107004150f840c2c000180038140400000541c0b05d61002c0c1030355001c1d210121a41c0f9090281035a82d0710855103240c1036604c02400c0310314070b405841100304c40c90008041b106000d40700d0381c0340703015500d00c150100c0f007402002c03041c003082080c00d02a90703 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620036528 1250 620035278 620035343
    0x6010c1b14091503030d11040b0a020d1d03210706050c040503070501030b060901140408060a020a09090b1503100b040f1712090d08070b040f02030f0c0a180b0d 70
    0x51503d0346066000a03103030b00c034032100804c4607a03072100780c107620707206001c10b98004140c2141c6c0315072200c0d0b4142020b5100c5104402d14400107110b007141d4030141a880642c1c81c1c140201a00a10000c44219031030201d41030882d01c009058031081c010240041c4190103880d10804812490315100c0307107460305251400640703410003410316003403800f5080075488080c00e44034141070034a030608410001481d51040c1e48641c5c3c00041a901803031040000100d125002001030317803026a14690704039038410380308080b9403400107c141d1000200d0041c2c0c001d468804061030f00324450426001e40240d0300d0b581c18500b5401644100c4100d16150800c00c40d102c46428200d00104081000d403903013a1041142d410240f1501040c81d11846403040e580040c055901c09443c401a032010310641c00d800c242c10800141c60504004030f100388140d00004a04000102e2418810304001d400414002e0070071544164030389001c03501c450815502c0c02e81400c1581e803a0044828a800ac140655001901350040192502d100115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620037778 1250 620036528 620036551
    0xe0a03180603110d050403030b03100911041a041d151807050102030319060504020703030e010501290306040b03070b0d061203050f07030c0b01170601050301050f06010c1b1409 77
    0x452943e00420454164600d204000501565540b0741035004006070048150140700d103d4160350307030039070075808164040c0c0918200030302c0f020301201300b1064842074009607044c0707402001c80840380e04240d040141c0ba5260184005070b100d9001c40240d1030641c008403655502016201031044030002041491000c49484011380b10310340c14000040e680384806040103940b400b442e40c00c03a8920032603500c040050600140195522015418007c0280a452aa0b01155403801c0700000b0341d200c00b44910102c2050001c0f03400c0c04000030908441a0343c0006102d1030700f00d52951140f0015560500c110409032402e4040c90f81c9602840003403c0c112405034011050f200e800007180c00c0400d03007202c00c3d80c0140340d0000b0443c2c0c4c0c40b1400e250072500503441c0c4000908058a031030000ca503040c8c0908042540360f003007000311445680c1c0e410405082e50b800781c44110940218901107a5a54450b248600310a4002c44d0508c07082001080d20720b003540560707480180d00c0300d490081d201080c6421241c4a401c0040320300c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620039028 1250 620037778 620037791
    0x203010317030a110d060602011a21010f020c06070206010812090d03050c0f1018081917070e09060102060601122013151704150e0a03180603 62
    0x40301c84000d5a2481c0d04800001c010000030a0070740b4507002040e5041c4021031302905c070703042c0b10081005008580246000740d400e0500e088415400d4103064000b20350001c0420b00380107400c000ba409405500030250129540f03e148205032449180014072011803554000c02c03152611102c02800c240c4180c00003a241c6e04174002d034000404550013a503d98481c00c0350303010550300b098642a10680305107a403000c4140940d43d0700e00300b00d0301d0200300601e0a0b02548024801c1e82803000c04141201d42800005203020401e002820141d44411300340200032185040141160307689442c028003641c0c0440313000d030002d03030302616100040c20550003a58001c9420b00050820303091080001e05284070010700f02c116943d032800342d001c036040210940307000d8404041c20070b81c0d1401c0010713100c81e202e410740c0039004103003004038100c203501d5201e01c00001c164010f0b044010a20344483d550261001280d541c19594242c603200303071110390841480200340d0507100b40c0310701607060030034260070303144440035848082032518241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620040278 1250 620039028 620039033
    0x804060314010311090726060a1a1b010e1f0f02040303051b0106050d05010203150609100c0c09050a0914010c09090902030a08031918120c03030b0306101802030103 72
    0x46905649280485000600340d542c00003c865030a2881451040c0a40c681202c0394000c010840300c40c020803096078020270460711000e05d4542403080207a810002001003080c0a220140046980380e58440ca10000c106500c490642038601580c0070065244101ca0001c0518040541d1080240d100380114083d410036245032400b0f421400760081040c000b031054030418030b00f01420360241000c1c180003002462000d83d40e08001d8000e4004032001560411550001c1403a46005004e40c0c2d00064000c081035641913800030120b0740400303003060031105241c0380103001c540390781c40d030003100c3c411306030707500000344035545800d1004070000b486544800c10303403501c0d00880f01c80d6803008441d070980d070b0405c0c0c021075a1901c0d8408030f8900074206d20040c0c0400408403d0100d070005410034507a038446a05070500015a010b0a0341c40b203030401c2d03000204a08254200d465130180903110342100940a410001445c40e11280401e04081040354840148229100103104160440350b2104500454540450556045a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620041528 1250 620040278 620040293
    0x1215021902010c140f1617070c1a09060a05040807090f05070f080105040b0d061a090c040b1824210c09040914070f03030e241e0708040603140103 64
    0x3c59642045001c001004500000c6c0e4100382c20882e42d111700c05103c2c900504102d41440d4010907401c50b0041c945150000b4401c18001c3c1c1e01d4200307100400140d00d00384090081102c3c030381c4901c5600c028481c0a1000044694060110200600340c001c0045200300c84256150708a810040c1500d040c040c203000c007200f2290b4001c041c581500d07025100041d4105c1c103a000641d038002d949a00400701c608100451521062000c0c00c040e52241c180d036015101c0e15068600c00060146000f1b8901d0882c2c1440440c6003210300c5200b240a000d0085d0440110211000c12484014101c0c4030702440d030710780012040820580e41c1031f1148013044036258200181040c10114540c1c0c40303103508640c41540c854000c4001c0c8000b0b078503d030030104103c0c000ca40b403a075962110810f6a450320b10040e800b04484141450b11401c020500003914810780118152400c000c0c00942003d811940c680b1410642c003c40e02a086640b6000070030404d03004a80e004d46861810600900350f0344c149411601c0c0f030061400400008500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620042778 1250 620041528 620041537
    0xf07091413120909060b0705010b0d1707170703090f050a1805061c060b03010f11160311010f020c010b010504030803150f1003050414161215021902010c14 68
    0x2100e00180c40700c5401104a54040844e04980c02d800e10340440004c2809030030005050f114421030007401244445801c101e00b10b078003864060516141c03d10607050500c1d0382e4005260442c800c61106440e0311804038501c0c02c0750000c4d401140812080102800122650182c2200030442200c04890860410001052030395008001103001c076284c0d80072030b60650b281a40c452181d002c40303003c90000451420054050805034000c50300035440e05045030f00c00d2045000319107850b82241c07580382c503102c07840c0b1840c9503002400e00306608024500d0798048040030207015550940200503409078540300c03071180340d908503014200c1e080e050101c100810070000320788506803a40111100e41944900712403202240c103d500130032805901001d03071403659800c1d036019170000340038500410380380842103500072140d581c0300354010007a600c00d61354200800122100150920450f4071441d6902001c8480d071261505030781142c18415403d5501240741c2550660911407890310320325034070307110000049001120350548078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620044028 1250 620042778 620042783
    0x191d0f120406050309030c012903070302011706040e0316020a08030406080c1602030102162006090f060d1a100203030c04050405180f031e0408030d09050f0f07091413 73
    0xf03000c00001c008180600a0b14000d8141d00001d10035100003107150510b2201c0c9d40c10100b0151040b140103066401d0005800080c0e0740d040e1120004c194001a0721512004c000b040c2d40ea0090301c40620000020701807000c1d000038580c5c1407810382c0c00c200c41e20401420005503003000420780e0081c0403c000150303101c000350360011000d1031100d655405014130140040740c0303050060f405600020303d81d00130550550b46440d00da805500b2410314109000069945074509804455000d0014492250540f03802e5805201c0720400a00c40ca15000d410b501100555040c00001001800068000c40c1f0364180800307241404030440c4040d51851828400b048840d00071400345902640e07545000514080345681c4a45a494a1000311807681e00503420003540c075407147c6c1d820030f0030100d5111101b104170103c005a40c140c1e010390016505006180c1a0a4014030f1500800c1c0c506e4401c3c9186502e141a061061843d103654400150001a0905002d10191501500340c114440c0c00b031404c000201603400c089c0c40c06240e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620045278 1250 620044028 620044037
    0x2106030c06072109090c030902030703030807030f181101140717070506090606150a0e0d0206040b040305030c010513020904030807140a110708060c040e191d0f120406 73
    0x401e0b050a109044400fa41c445640d1480c20580140b940c0221102084542c81c01090003500d03042030b0200c0a9a030039410080d0180e0180c881800080e015070103880e40b01c822840e000640700c5080e00500c06455006007510100d00c0b211030190b0901240795482d0401d18000e00b800c038042500d82a56080364400c2e8007028080174015840301401c81120000c6640c5031703810004031421170074600c04241e1145405c0c2d412a02c05c01d5038a892280540c0708a099440d00c02c0903841d0114a102c0744001d00040044122080780c1c0000c08010201c3c0d800c118902420145004030011030311500b4810045003104c0c4044c00744241c02e090200d6003001a500d60000c298019458906485070b42c41c0c62805030f500828462030084031700c201040040825a0007070341e00d080504c400f41294102580c0781c524940352081910700f0008002d0400061000401911403650401030604500840441e042154411603a1804401142c0004120081c0c020f0700104615035000c10781002401f404074031030b286544103105a01c200410b00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620046528 1250 620045278 620045287
    0x304120306030f03020c090615070308100506070f1104051b090f0a120c05120c0607050a02030a0b04151e2f04030c0611060403050c0f122106030c06 65
    0xa403007904401c008541c0150070308100142854060340710300094045500501d0900300286d4546410310310349062009403410145800c80781c0d00c0442c0d4401c4010a080882401140c0c0012030f61240b400405140d40280c428001c8900c49280c40c0542c80c9480c00e141303100354101400e02100310700c4050703c415041e01c041881581c400284005c110001e6282d0031241d8403442543d800501180311a1006002070f11901d80d00da00b007a201e008105041000610002245d8410039081c83c0d2414107400900b0858050001c607004407100d46d001a10704011642c080755400e600800340000c103d120007000c26056104041440b140a420710940343d42103401e114400c843d512145c000d40e6007101d07100040100c02c4078111301100809011000595903000b0b100442e00400c02c40400140d2a10841000c0e40020010003c2c100702e84494804640503001180d07681003a0040000b03484000700b040003076100415401c80303120f48400140381443d1200c522403511102c12420038007081000c0d0340c04241c40e50425002c03650345071103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620047778 1250 620046528 620046563
    0xf020303240d062a0206040b273a0c0b0711060103080304170a08010308070c0803030702010501150201060b03130503120a0b0a0906030b040b071803080408061006050304 74
    0x40e02401c60024000c10314001c209000d0f159a8280350504e10b400038120189030030142812a502d51044030042d010b03c580e600400c034208039207103c0313640d41c4041c5101c03480069102d10403103062280002507500c00f42981114554060760b44100ba01c2d0008104101c445100700700c11025200421800e0010440885030000034601c601a00d14082c58840d598222060303982c480c0380c6124075900a0380e059130700c091642180010340c4c00c01d408441c01d09001d9910194aa480c42e42d906a80343c110080860b030003007920b00c0c0880c28000030030145201d1641c6c2e500104207549030400754010007208050580441e41080d03800d001100980301200e401c04941e0043c000c21100c1030a04600f5802220300c1d00b00b620001806020840150f5004144203a00440b0400f59850351003216404641107403100424213024840028042000d01420350b0740f0800c10b062120340c4580e82005448501c040da0011a110301011400340080003080048a81c01020903030100350460822602a110f4000100001c05039803924101c00e02 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620049028 1250 620047778 620047789
    0x60f080c16030909050a060f3012140c0d20150121030906030b0406051009080106090b0a03240212061009150e03010902030604120f02030324 62
    0x441c0326944441401000840c5802403c2d1403841c46106002e50500000c102400142c0c4501411030301d6041e0a92981890881c2a40d00b0341e0740e541c140200e80c01801c003400c004071700464501e1282807050031403c1d45000d504c00094120303400000040b01022051000215050001840050704050344c18030f0100b0f0100b010b0001d4040c804074070200700c01d0090001810b045040e015605040e14846d0300200080e462003215202410781460010f00054a05141046141d02950202c01c1030000904040b4515480c0d1021901c0401003080c04000119204400c110102d801c0c4a00c401030164204203000c121294400119444224040540040909038603a180b510400142403603111540310155102d0841da40c4050002d81c0844071070340030f010ba224a00203a1031041e0300310000d6a00c1500702d030f2502a840c44c07044034030954501145406640e10410903001d40d4042003014821442448500703a2035054400c001c03d40703121041e1a4055500074814845a100c0d001e0040c991200c1c2124040c14081c1e4035800143c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620050278 1250 620049028 620049037
    0x110a0e0a0306020403060606020615060301030609060216031d030a050c091008071e05030105090a03051c0e0f15010609030b1905071106010f0e0109020a0c080f030702010b0a060f080c 80
    0x145030b6031000400204110058010000701d40c000d40943e140d694890b2181140c946016640e44c0d070100040005100046c4e46500c03002c0000c2c0540c0e0014249020400040c45482902d1400c1d80452044043c8000c589410411540c03c440309501820500e003503581e80781e0383c03801c9183c0c0061051500500090807414002c03e054000c5c03118400325600d4550b51140d000c20140a001c42c2c0188025146000c50306017014010306010360f040314010305002d2029201204c0d030342c00010075001a04600e40c1c10340d404900324043d80700c00c14003850151480303100424a0910b44506805e29403451124240108400c40d007280940d0112600169500401d035607801c42001c80408041c14940395034a8036040c04400c0381c4c020101000301d10304000304c42c0a84d0721402211030300034251080d40401d44404005004013001034000d00720001d40d505003224000413580e0b400340c0725044041c5040b0f20800110820500c19824050303c03150540540e000c003c120308200c80201584010892071060005940c08281c0c41da00440c200e0303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620051528 1250 620050278 620050283
    0xb07020d020d110319121d090402060d060b0301090b040b09011505120403020f01050a02030112060b1305010b07110405060913051612030201050603010c05041208090904081c110a0e0a03 81
    0x641003445104410040e03119800f105642160300e801701d0300c6030303280074031f9011100c60702030145103010144101c204606622300030400c90708100103004010411020307004410103041e060749096101c0d810825000122210050724512450915041006a40f98040018117403440c1f18113960b0700c40d90f607d006582074481c0c5002010030b48a01c600f00700038180c0c04184410040440b20007803000341c9070103031090306a01080c01502c150700c800d240218001000c40d80185403414010b840219100500c01c0324008a034000d9008581110300040c400c410400007441c1d0f0304411500b00d0b420005070074000046a40b03008010180303440440b240d03072804e060040c2003090b40709101603280c15001c083e0703e40807604100088071000310059802c00e4080f4940d440e060213504034000c00c0742e41d614201442c14910031101e0000281c15220310718108850205922035140c22485940a40207140d510100d50007080c0100c42d200e150441400d00c1c200b50840d0034221031f41259403010b12450411101111800002c0301485c0e42d9100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620052778 1250 620051528 620051533
    0x1b0c080a1404061706120606060c1005011212020a03050f1614031b010b0d02090c0f0c03070308160e0405060301020c190c050105030115180803220b07020d020d1103 72
    0x4070f00c1e03401003135501a014002045045500e0312000c1c06a444241504c40c1d00640200c4000b84075401c20314013a10403080c2075001c598801c28080443e070300f01e541c02c2e0030080410480c01131032420b1240140500161104d01e00c01002e441095031802081c034002c3c1c03a00e000b414230300007a03281024000600000805500f00140d1544560a0070075139a8a603c05145010600c498458141e4405010b10450030049400f41201540c1e01a5070300304805110010301c03105101c1d005100c80c0250070000340281c2800980310000f5070751442a4200075056400090541445191000103143d019030700c4141400100e1094801003044d40750f880000c0e01a011b207100c84c000b9442413403ca08814403000c80c0d0001014018803d801f1819190801118030744000d0041003003404003511850009840b40d40c00c0741c40212a48503803c00c0300c2d1664072960860b0300286a106200075070003000b006049006a18a008104044140d17207840c84642c0410648031000030040d10604042c0c1c089001d120a031300040081c04401401e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620054028 1250 620052778 620052787
    0xa0c03051213030e060c0601030f0501090c06020c0415050d120905060a080a060509090a1209031221020408210f040b04090b06160b040f02100e041b0c080a14 69
    0x40c00c1609000c0b018090300000c5452810141e03074140001202c00d00401400a8181a82507072a02e00c40e05182403800c03030789596a00c120501254941c0310000280c0704d154064003101140300104030a45961603030811000000100030040c594620703c9401e074039644111030314801c00380305405a848030b899501640e0820000603002c0061070b03000c2e403035034415010b040003080120707110018015841c0c4215448100d50f8449098030b4081200100b50f503032600c400e8500300e01002c0d00c03542c5030b08401c0b40c20ba047c40c000c2502c00400d8007102d800b2404000124484807030450405140c45000c0342c2c2c40300c220952468003208030141e850840508401c683c1744589003418640d44e1541c68031000e565501c5031040345201854904070980130b10700f0404640705503600c40d11800440015446420092101600c200c4000a6100c1c0b0400103883e8015242c4820034551030345c460100c41c2000b804195070b0f445280030b45841d650400c03407041039001a80002815005903107551a03000380c180540d5029039807a01140390360000306 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620055278 1250 620054028 620054041
    0x70e0d05120d0f0f060302030325051906050604051506071128081534110f0f0d050901051c0b210a11030c0616110a0305030a0c030512 59
    0x300000c11400f42c2001c208513900400d4612030841d8594000254140c0041004103007104103170855203410440c20074031a200d002c055854916200f9400304406030700440080380d4051040900c0b131682e010a0943e000e001d58580101810308003a5106030441c4100c1001c1018010702185050000c122440608240500b8603501030740c6903902c0c40b00740905440307180c1000200740d8803404150224a0260766040c0d0b40207031245036940c0405002d80701040725008400c07403000c54040c00c1e0044101700c02803c1d101d00f030050070042c4542c0d0801c6508000d0002c2030b0700c00c05103d1007100c00000c05c0e8542864030324102c0c0d100c0d0004001291030380f055805c01c6410700b03000c01c01d04da4070282560080d14182c4080701c00d000c1090320071000c04402e26641450300300382e4004010100c0032078008039600b0304401c0c00409580351048007100040898212051180e403c421068062040005c2d5404800c10300c201110340d1140c040c51640c1e5984e4134480c0c07450f1802001001c000c01000c150040083c2c51025625403060052480d004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620056528 1250 620055278 620055281
    0x10b09131d1902120d12020708070219080f0d05070206180a031505070306050f130204050d11090702031201060f1b050f06011e030204021b061009050f070e0d05120d 72
    0x1420f0784602d50503007034016685000150046042c6264580c04103000c0b42801c044002c1d04550b205a801f40300401811005941d07203a030340008100d00e040e11b49012403e004a1500d8989800104001030b4008000c1407801d98000d002e0750038a0b41e044607240e964100c4a980b076600100c42c9002d0503008401010080100302d200d400122a0a1b00300c4d80410055541074003c0b0181c580600c54241c1010400e02100700c1402c0507005c40d00c8920306601d01501c3c0c565940085114001085415900c01103005401c0e41c1700d03d090b089094102016200950804807005004100d100044c4115014000c2c5c3d82c2c122076103c0e004001525162880c00702c2c94230000190700380b040e01d48640000d00312107400369000100300f2600b4000c4181c0c4240c90a6150b032013050460f8240002548680d103500070b080220550058804000c100680c4200c0820000b0380520345010001019030780c020307104d40790180210040108456201a061181d000c080b83d220005503c1d50910b10708140030141c2041201c000015480340ba01ca45 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620057778 1250 620056528 620056573
    0x319020d0b01240f0f031d0f010e060604060f0e250c050105070f0203041401200106180203190209010c060c080709060908030f030613090308040605010b09131d 70
    0x79900340c0b5083c0340302c00b50403541d030041c000308080818540114100c2c0c1c5032083c0c3c0040343d400c0106c0d000c512416034540780740303180c451010001c0020f42e45540648000302414011150481070548040c42a03604000c050000c102041c0074003020030003001c001500306040c03100c80304140040700444080c2501d98820050554030348070416600c0d90701706000f0030001441a0402c444003405503018600345400c0c021f03c8401305402c42e0b03030b040c1003080100058050021450f51840680c0c002d03000042c0481c5044422102c02004600705c144003841441005041d100780001ea00c0c2c0300350140401a039502084d80141c620704540040a807400d0702d071800280006802521660107425039490740500b0302c2e038a41c81102c4ca201c076401209801e40080c0084085540850059500864000c0446e000100c190342e41c902220280f84c03082d00011914000d00c01030151522a49024021000c0d0103480e0900501c00716250f11107050302d01d0701846d502c0f50700e40407000c0094031104d12201c0c500140c030306040742080e182c4003e824 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620059028 1250 620057778 620057819
    0x60c0c0b010608061503190b010c050609010518070b181c050c0906100507020906061c05150a050303091009150c12050403020120030d0e0a1106090319020d0b01 70
    0x40700102c070745c56014001d032071044003c000c6110722a110b0000200160142e01d550a060007201003504002550030311400348104608800011189001c1da00e040c40c1c251f81c2072590502c0e4100c41e00074858404000c0854028404101070608800310f600042203030020102e04045003200d03854030810070068081100081c40c84121060320070707500d4003800c0108100a001c50800070450030400785006080203002254410001030000d0308106030751040ca0000c10076010161400d59132007003000a60300c90305141803211041a5400504242000b003c01d950740b04248145104d941b000c1c5150055922900110001e4504c00c48048444002140040c1185660b1141141d41c003c0c50f1920703800d51441441542c3c2105e070141d40d10b8442107680c000c004014400d140c203100c0c01d1b0004005460390803901d405960301c280d10200052100d909242040004440070a11440c8034010400c075010040d0740019040c190842c51102c68201c00826100082c2d10700036045004002d40c04c000d00005aa003d2a0302c0184c4111 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620060278 1250 620059028 620059039
    0xa032004051f08060618090c0402030405161203050a0809010f0e010c0905060315090405030904050708090606010801080d1202090a09090c0801020705060a0c0c0c150f020c0a03060c0c0b01060806 85
    0x90f140c5a01d2078a07010f007110000c0e0005010120f42e070210f0719030240030303400101c0b10301515580e80300e010205041e81c1c0211000e40340ea92007103120f00e55078400090201c00070260741c0304640e0006c45d10354000b001d80c81401003c0c820001e00c6008103484071420352010500401c03890040000040060005010f020107600c100d000c02c5e80c0000018483c18100100c84c81405070504003c80e004047c010064000f03070241041d5000d00c001e1010201c4c603251480380c2c602179015515030031260f1401401503440c001c40100380a041010000040000a00004094500c1d0101d07082507040440c208c44118001c1c0074180703c0c40e5002d1140040000d80c40500e03401040500d000e078080304205900c45400d1400c0c2d2090742d10041c0341d0340c031881c0050035401c0c0710740c40404103070f6075071070003040c03001258940c500b410320b9681001c3c010007201d04541031225084025004807031914005000700014050000d001400c981c48041c01543d00d5107800c8107000d100701541c0702010390080c60301c4441c4d610303550001c00300700b03049640d0b41c00796 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620061528 1250 620060278 620060341
    0xa0b01030203011802070305070b10030b0702011802040506010507082701021504030c0201031e0b032830020a061802060a0c06020408070b0909010e060a03200405 71
    0x5521070300803a41600c00c0d030781c140350340d4030f072082a503a00a500c120070030307000c02009014500002e407001280600801304003000b154024290305140c984101d024000e241960314142014160300010008d220302a1b40403075002a10350f89010040c1c41c540704172140206540c41c00a199100d04000b8501419041190701c0465960020075005aa4800007a4210140c09105100060000b88a251000400f51061402003a481844004103071240b120031480c10034146c0301c1a16848600b400c016006840143d8005100310100b0095103080c08248810007401c0c0305040c02151510301c034a188564280302000ea4000485200d402c8000c2d100c2d010708408544860808007603854403048100b000e103690350018261442d050b0004010703501280e5100c2c049a0300358092000041d607100c1170040030001c20030440290f07921040c2104000250348141c001180402e190800c2c44201d0300c402c900d031000e0b40d5001720444241c0700c1d049007122611111805003607100381800c040104401d2124500c070304400c1199484d0400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620062778 1250 620061528 620061551
    0xc0610080601060518010e12210415081305061e0c030103030f08153f0703121b080a02011409100218030604110a0b0a020c0d11030a0b0a 60
    0x40c0c000c00e01c40c83c4009082030203a40c2000d003151606080d00f13141414682d032800c1c41a804a0f070718802c0c144031002190401c0a8412100c61508124401c40b49141111481d003801c15140a084c552009941c804004103400040c80d810306460301d581e0043d401404407192413400ca40078010001c0c19404000a9a81c0100403c90a03804001541e060300c1d890344036400e8a42e854141150420001450709024030b15003041c00509854114407050f40000f01041c0c00001c82c03a00e1801908a048009081c0003c41d84c0011036a20040218054044e40c0e44080260030115118500310b0304070a01402ca4859054801541c104009001d0700610752020141c0003800200d800384141c407000382c8125031082d055001000180d40c4191264001d2a210950413841029015000c011900d0007004490403540090004000e209921f04107680c2d8004000155100c4d260916005009445505000300240983e420100c80010085144410300450002408650004440303090a1a0040c001da4150942078070780411500c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620064028 1250 620062778 620062783
    0x13180507080a0818010e222a0f1202040e0f0619060e0d141006050904053c0604030807030905031c02040b040306090c051e040c0201110c061008 63
    0x2c0d5141c1000c84113013004600e000120700b00a241010360b040000010010560b0342d5900f805141880070128407070412103460041d0300c1141c401031030081d041c401103980711201030340d0b6510110207a01d891400303884900816a090f20354115020121140c2800420042110301c0c000d100c070f82c031421031603204d0704c905e444100c10301c18180d101c06443c101044445100780b100740d0240d807518103103400107000c0b0038a40c0003580300d00001b503416103080078468001c00d021507910f40440c000c2170050501198600700c01c0c200ba6689641c0c0340340c04010410304040c60009140340707038641e801415041d2020030407180b6060642c0c03103442e02c5a408a60480200c0d2a01010940e401c2c400d204121170168090000d501d456a003c0c01c0c1d0b00c0d54201d1024590495408020100b42160840e010f48011880303201c0200c3e04607000e00e0401120100780c1c010034042c2580f00918450007000a0313a00da400c1405a8001a0a03440c01030201c0c051f0245181c1d0780004400000c1802c40c0c2400002c560b40b08403c24140d040d103483c1c44492068 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620065278 1250 620064028 620064043
    0x30207050309040e190b100915140d060c030f060e100608060a08010c0203041a03130f020102070b0310050f24250605040303051f0909021318050708 65
    0x8000307600038040400c050400350f10929000342c0060803190b480504442d82c1081c110258000c407041001e00c01031111041d03241c10904003400c0c4504c0c05000c00341b004407002110020a1141485400179441303858100e407540481c5125454014101b40180030003d54003401501903404c42441301840c2080005401ca80b02c4c10b03443c0a08429460703444070074a4400111085171000d4203071580490941000200d036102441440c90902e0250069600c0ea4036240341d2022040d03d00d0381035072850000300208130860b04250051512681c0c030117004510b01c02039000407440c00740b5a03004010215000001d01c803141032281240c408481d8200c2c1c40100c0290b118041c000000b1301c1c1c00300c098582c00051000848480340f0405420100307610031a190400300201c082011100103c2d005031200c0359100c0600051503458011280d200c03800c00740e903d0340d0300d02850030200c3c0400a8422a80526600c40000086540d000403c6400030031920040c425508402c041014030521400704680510624070000f903080e0000c610360 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620066528 1250 620065278 620065283
    0x6011103041a0c0609060103140d020a080a0201020c0d030f0c05040803030403080603030d090b22020a0506030a15090e070510080105040203060f0d06090501231b040b07030e010e01030207 82
    0x21818545019020500e60800d00681c2d00108410301c220318142004211491094401100901c00c55145040a15a40d8401c0850008d65040101c803501d80a0300090350380340031a4048001a0380f1440c10384224024040e10003210103034020071050720801e5505400100c402000100100b002c5038007490b01703030356501c524031440c01d16401c1840083c002c81d00030748155610a0025054a240c9000904641c04840750f51104507003420411060200100420f0480c918a90480d240030400076419000514801c203544070300391080200000260f5001c82d2908928500484401122502515083c1d1540a809503c980c1074051141160018403450030022901c0d48401ca908d618a6590a041c01d00010b03510040c40c4a03005031182c1d541894030b032030310610002d0b6280600c100240c0b0580300d2420b242915074818551140c0241d0202c2e80c0045440c038023059400480081c01e50880151101b074049050213142c2c0175612150011842d0424507070030480d0711200300401d03079450b15070843c07000041d0201e0003980c2c1d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620067778 1250 620066528 620066533
    0x17090f06010b0723030c0a0305030121081210091806050c04060f0c0305070c14040b0f06120907030c08060703060503071a1303060515010206060d120c080d05010e0906060111 76
    0x10340e20b130a00c10039003003800044c1c044290703450507030b580340450300d040440351040b00041c10000041004d24000600a02000d0200650752044640c3c0e0b124081035010740b5000f01036002741040800c01032428400254020880088180560555001a070500c1141c1480681c0d800d424100015030b0b150460040750107a0340e143d11a01c02251002c01c045522052410b0100c0900208003c1100443c0003426030500800121044904d540083d81c14402a6078800d088070340038280c440c0751108603907117600c155002c858000034001c1565036007149203032134492a68006451042c50100206a0703080204c0c0c8103111311241c0e00e0520007140e40d407007415561001e070b02c81e0340329200010f143c01541c040040014100c7c080380350054a0801d07120f845103002c0720825030f040e030340700360582d80a0105543c051150316400b80d8101d079903820000c442d403140340092011108010420082388200401c000a40007a50001c0b04003202c100160340e100c200c0e402c134282c8142c1d6000e400d441424001031880d03200c0c040861106402001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620069028 1250 620067778 620067803
    0xb060301080d05071a0c03010512060c0d0908070f0b1e06010c0204020a021e0304090e0303150d080c01090501060306180c290c07050123030c070317090f06010b07 71
    0x142200d03141c0185100b205c0a0284940005481d9140b500941c0680e6100340205d65a5140908100c000740104c8031b2600190018010085a603140324140c03066410044004560302c00e0b5441c04000071700c03a081008141c2c0c52001d00850a00288042c2d242c0310b0007014041c0c01c5000e02e0314201c1400c000c41111501d002615030300c400001402c042e006088201c20600440e6160201100c8210020243c250a0b8450b54000318041000c00035034050310000310340c91000b4518504100a00081048446807028000c0010541480c108240d0404890551201c0402003081c00c0d2145400c602801d09440140d404038206034040c06000001082c111039107901843c540d14451500d1914080e16100a0703201202c0b40300c80a00d032850310704220042000868070809002900c2c00e1000250010905200b25100360f040409600490005041129004a564804240c0750019031804481d21005403580724105000ca60612174112800030b120400f20a008058501c1c0343e80381c6540b4140c2d40240000030700601d45041c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620070278 1250 620069028 620069053
    0x200a0305070306110d090b0601020d051c020a0215070804050c101d120706030f0f020306030a0f020f060708090103051617091507201605130f0c02030d0b06030108 71
    0x240b0107507558450302c0e42c040c180510304145c00100c4000010540e6510014000c0003015039044c030000c119940c507801d00c2420646c020200c003a8003940840f001040c5580000c0000c0b28a00070000b0124181c5203401c800340c0c6180c1450002c01444060345c040786c1c507100342c0ca0208042d1034016213038240c2040560302d4090321028560380041c6c4031214443c42e9003010594420035002c03182404400c000d0030083d140420351807a0800048100e0b04007105091031303948140b082c40a50303900440d040749019040b20110350f40252038000944e9806034408815031102c00051840e040066460240401b202d01340c80c10001c55a035002d041ca1100045020350f80065951500d801001000c500b40396002a200c8046800c040b4012083c81d5156a065464102040b08044581c03040b4140400c1148421042806001150800740700141d81401d00e001d00ca11903400780566400038522603101e106038070b4800f0801d110740b202604002c2d4403a88500440d151641c01c0c00100d000c5400e01c0000c5070304880c070460007000d02c0303100d40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620071528 1250 620070278 620070281
    0x5010504152304091e0504020102151509010303030c08090115050409060e0d05070b010b09091602031c02030a140105130207030c06020d05010e06010f02120a0e0d200a0305070306 78
    0x2030001000c842c1c6015100a03040350480c0a00081e01d022800041e0401105003007030f102000c2c2010518429040008100050764003040c0c0f610030015080d07103080c044d00c48107006e10b0a4040004030540200050700000f0a0540c141c000040344625510340c40101d48882a00c2426544a00349004040030004c40c20000340c10301360310042c0e405008200016203245218411410a14078109102c009400401d070801444012400c0d107004005410096240c0f045107000306000c1b0304003c100040d03407001000a008903a0091048910801061015840703003201c01c40d0b550000d410a60b80489a245401400300e03084101030462416600018408035460000182010103580284000c6041003905503080c4001a29030001e0034002c01030810200751903041062203140c41000511003810044203400b4003100c1038000c43c0d41004801c2c2c0002455580c2c0c1c5020f02a12000c0e0f45191480d004190a00c3c10001d001c1110440e0300f81c103805210400d425620002080901c1c1031902018199420144041000940c107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620072778 1250 620071528 620071547
    0x121404120903050102040923010602060c0711090f041401090201020a08030703020f16031b080711240c0c06190c0c030b04110108070203160321020c0a03090501050415 73
    0x2841c0c982001c030749aa03980b50070398006c0e6000b069425103c2603006504078106000341705141c208182880158541040255141c0000c4c00780b2079214000200e0009101045a0840060b80081c1800c0020b003841200700400c500112429503100b40c3e900d03820111800103001c3c0001301c640590050101c1c0120b134950320400d610107000f40c1c0c1455420090642c40c8150b950290a08102d8090b10f080c40c45a030b0305001c1d000c03914654500d6000351034500d0705400901c5071400e440c8800d03040188160052181800329404004020746101546d08905a0000641400d0020960400c7c3d200a0741d01c0c942c240424044a030141d410790003410310f408040002007610031814078038014011150340c000503a4035111034031441000e540c01e58809150f44031000b65560000c000b00d42004103403008601e0714461410403c0e00c032207107440041c2000a0758541450ba5890414075000c80f102d02d210031552404103008440d0f54070404c810440118007400d000180355801141520100c03103144010750380310300d00c4400446e0b000e1503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620074028 1250 620072778 620072813
    0x4050607090b070212070801090f0b0912070b040507171624050a02070306110a02060609190e120301120521030f0601051909181a010e0a08010516121404 67
    0x290f46c50000c0c403602c00340185210580160649201c6450604080c041090020400081039100e004203c1100520008591005400c40002c001c951528505241050714542c03045521034a202140c1e80c4c034043c04200400b00d0b00c2541c0c80c0c0400e2554a001c08020301080d05210b14010380c8a19401182e035009030000c000c041e00d6441030b00c1030325032203a4911046401a4100030210740c0041018a1070580401c03035103230001c0046840717050b10700c0c00080d45c140b2800203241c40c0c40c580352038a03424504420f0411040004c0c00c6419000760316584c6500b0a00007030310b02400c05407054454a0001c4119112012a50b40c14200c805425490b51b036075000d8400009101920080c100b00041080c0704100d0f5184a03800c407a5941e035640d407400c42e4540160740c1060314a4120050025181184455100006154144014800b801c2040c0c40007500400201000602c3e4001d0100b94207100030400c284108441c0c10300d0918a603214080914001e6600c07404440030308100d641c483e58103101240205d241601070b00c040b02e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620075278 1250 620074028 620074033
    0x231c08090f0f0102040603060905270c06030f040b0711070e071e080106080a180b040c0b03090a0b331908030304050106050d08040e0a02040302100804050607090b070212 74
    0x3000028a2402c10b80c202e882c44265800310301031003020b41c94001c643c014480c0900c203010b82e0030300b41013003241c0740c05605049900c441c1c0d00a0300d810305502802484141c0b05c00802d010340783d2411040c400c1034280101c070b040b070ba9802000001000d2601031218030446020b4140141440c50500b451030b003206034041d100d1414464200042c112040305a82c01d0814011980d40e038101c1c55252800c05015038201801c0c081300303681800316003444101042541200c071030b000600d494280e1a40e05150041c4421900102641c007400006c00907584400510480e61314401c1d000c4078aa0b640c0d00d169499800100210303400380b520032604103840f910307000b030800d40c651000074a0b400c2d1350101c50f104110300160030391140085410100400041c00401e00c1540b00a02054803018000c081a03680d5555511503405040d02036120580070403900d50304d95040d200a07541c058406003403541ca4442c050b1900e0011101110603100d8440016080d6200e804158102d500e9880f0303807402e003600c40e401c03c40c589150152260061 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620076528 1250 620075278 620075293
    0x102211b093d020303240a0317031f050916020c0405090705010e03010903020d050a030f050114130606080a090201050d060e1603020f0307120902030109231c0809 71
    0x4081e076002a103500d030390b0a070000030310410b050030041c580b00d80000071000d540092082140b903400008280d43c1d900740e0340c60042c40c03ca14980000301c44d5641030b000078000c24081c10f600c0c000e10105200030760040310f44038006070001c19010a01d603030404440c0030f42d60704031060700c012401120300947ca0b5207a9174940d00540d21007040309004641180c2c81260300d210280d109490030403c1d5600000518200d400503030080c03000b00201e8034069603840780c0c1c6c0e58203007c00c4000074091758598481e03405010042100399080c000c55951310010346003000000d94403032159284019145c1040c0080c4a181e003102d500340c4540b0701942e104500b910046c46600c4050b410301c10100500348a40455114000280c11545076000d158201000f0000000c4041c0041700103045c030411002e81010440c100341ca034042d45a20b040d080d08845541e450001e071986000094142d0f007404034100c10001400303582004440e4501c05800809003c00e206951041c02c0160110140e40a50340f4001c40b502c180c40099000c0340d0ba00840d00ca0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620077778 1250 620076528 620076559
    0x80f0d09050303270c1207091e1109090708100f0b0406020d020d0c020f210c030c01090509010909110603010311090a0903050a0315050d050102211b09 66
    0x90300d110020403145030304004104a101300d40d60702c007010052444004084507004000c6000e41d00c1c10403455480c42076005090b4481d84070001c12146024200740c013028802400350144204c0f0b81007818615220b03140c144100c3c20109243d0710140c980380303040141548038a0b00c50f620190f800c00d001170b01000d50702090140114440c901c0030042c1006000075610070b55140d00d4001d0080c1003518014000086400900810200b03660240030302484640455141440c3ea901000040140e1030310049040c0301c4804000440b05d608020465445941056041d200402146401121090058054039030b1110110b001400504102d9005071521441915aa60b0410f070070000241c19420903401103d0315400d8139103d1000d17080c107007015500884414130078400350000d59009021401040d40402c101a80c421a006802c4e040b00140c00c010310014040c10030001550600034045d60180d03040350090444030f01540e18031000b0017041e600c038440400040151106540c2c0b1040140e01048055901282c0850780911 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620079028 1250 620077778 620077781
    0x60306061b120504080a1410020c06010e060d2102060603070b0d02090a0b12151e010507060b040c0c0605160e010518060d1a09160c1a0108010204030519020607080f0d 73
    0x44036001d11f104061401282100340e03e422528100c034494180180700421440c18001141410f584c0d800740030000b181c2d50b01001c00d0541d45c042001400020000500c0103081c0c540350840700050540d942075628503074445080c140d494030355110f046c0c85043d040104590030306640c1e018204c5000b0040100026035560f00300b00380140c01604d05554004880814803044020400c40c440f000e44055074401c8407038162080b507500c01c2c00d2801c1510706104000a10400f0065594404820385000420402000d40070300401084110ba0b40800c070b807954941404907050104504804514a00641e5440381001c29a4011035580c0c0014200240301d030000030303012166944210280800b0301014070002241424464118501d129000049005003c0c0109000802e10100c4401000418034100040441003914007850f10700d0040041002c0c82034400004140c20106400a10461340075108a0b101c461000201e118502d0440c2c0d8003e41c00441005a84001070000020300004428040540c0c10900d11481c203a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620080278 1250 620079028 620079043
    0x91104031406100909050d12090507080105090c010509090c0901090906120c0603020a08010902031005280501110c0d0809030609010c030609061206092604060306061b12050408 77
    0xc03940203842040203c1d100c4020000090403d008148030b00c1003540c0b61640c58203540491102001190201610284841d40040081550140403184a15980c0071014000d00090f580e07050b01d40502c000c0d890082d0b00c075600760340e0508002070020141c0d89846004000c5036008480b55030611404040c0090301c045184a1034004211602a998011800340f03811071a1a145070818020f140c07040c809800100d51205440b070540d0021400103a490b111040840a0380741c181e442a58050425605004404020000788041e51000c0990320203072503c58005541e00c1d10190030008942d031228948058a00d00201700160007405008600d29221145012a04107132080783c00ca40540c0d140c2c034a45121035030501c40e0f035009181320b0004120362410046004651900183c000c0d003000c1e2240c0116050010180f01703042c540305032202e68600c02510341c00f07441440e0000d1044a01107454480002081400350b0741c81658102c1c082c80c58005c075030700d540c0c0d50f020341a0a0312941c3c04000091001044030b240400c100b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620081528 1250 620080278 620080313
    0x5040f0210021b04090b19020d020c0a0b010807030302030d02090d06060b0a020d0305090d030b03010204091d0c1c030f02071a2a070302010c050313030b0603060601081009110403 78
    0x40c070b000c00c00741d10445140d03010f00369802c2c025840e107a8218081040540b00c0380e0041120707605086410600da4440000e401049410074070300340b00140038201c1c03c200141003000c15200c1c0302200f400d60b980301820f94072191030344005005038104000400c014007695004101c0c06000030100d40c001050740d2201021103406400540039048001009400d894041003455030b041c01510b42441289007540030701d619980000609810b05487e40f402e421180e9003901581c02924040b10304012000c0c030700c4c1d89194000e1002015490a0060403403141c654180607903104031240145e808605c0c46181d0f03542c11103c81c1d45c10b011003402c500030b44002003051030600607480642070207070341c40d00c0d122048030381d41c05c11011009200b5000c000e003002d00000b2492010a000701143e40900385041003c80504186045215440c194450f40c0c1c0407200c0881003040d8000020300503001603048030050366802005613150300090f070300100e581e0b80d2008200b000305416001a24140442c007480c5042943e2580c9940c1268100c035440d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620082778 1250 620081528 620081533
    0xd0e030f03041b031e0f0b100f060503010b0a080402031c0e13060f06031d0304090f0c080609160903051e150106121104120c0f050f0a0905040f021002 66
    0x24041880050414120401059004030001c0c5196917100e4282503101d0f8002c51000845000d044203201614100b00c581c51b4202e620560240742c40c0740454080e0348075020340420005100d4001c40c0440c031130015603050340c007481451454101404419200100c0c02441241c0c14424200d442e690495251403641e008540ca0b1101c00800140000f00038454154080c03001c1400d240640800940c1802000881101c8040c20000f4400d490410a240600751041005015200020700021f40344000e45c8510b41d6500c80a40810002e50070100413103445800740c4856921000c55008506070760568901051001c2e1241482c1014594a9648906145200c040803144082c0381d050710020342e1047c004259000840700e00c460889d0f0401a0141082c03e4040700640400d5443d014040290303030314000c4601405800321000026412481c0c5014030480300d002e91549062507038000241420699001c1a0f9400010010303a42d89050450000007420001d10035a03030b491500402c000542c5800324000300c06030023a0301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620084028 1250 620082778 620082781
    0xc0d0905100f0b150f0405030a081314010503150103060801231e040f0215031f0503030f120a0f020301120303060608070e09130206030a06140619050d0e030f03 70
    0x40380801c85071040b4009006a0426121a101c0d680710782e06111580d01ca001c103a03031211a00160382969010f9600440e41600c109080c0f681444540f4001c4d1030000000e000d8008129116040410900700c1e21100c1c0340814030500102d400c0703038182d0750401c011a1042c50002101940c03109a642500c00c02c000086044150010b03100080b00211030865000f03201080100b102a0144010f442045000300003400c058921924041150b135603051503c02c2111070b00c0030b00d4803814041e03410140d070401c000d0700c508085520038001510307080100c10b0b200580c500b035000604108044081e507122840040031410b060380e844600c051101c44078400342d80603190082c0002050f00013071501908580541d000365043c40303500020001e44c5580200c9a62108001342c8800c40c06072503195402c0040c030600300d0000c0d40988040100203012100d50f00c50400c482800d129840240505010302ca0790b4411001007010510b80c9001c2030110b64050401040084208140050b4622204055a007550404440461034001c00070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620085278 1250 620084028 620084053
    0x6031e0204151707080d080408031f090203060301141006030c1407060e0f060f27010c0f02150103050709150b1603091d0402090604090c0906030221150c0d0905 70
    0x2010f130000d40541c0004002100c11200060b150810040c00100302840020014042180c01e0801440382d1001200000d40607898805d640065001101c50502039842c11000107652003c10307035041d00580d00310035140c14603402d240040b0090041e4000600500c2000c40c0e0790001e1142d054001e086490190a001611104c0d1080340d81c10080b1840c80f01045501c980203006440580081c6182c205e01034281c40c2810765002c0c000c140c280141c2d000801040d500c0e11300480c2c404c58004903c624155950340c203a405c0788036107588444100c1e40a0102910581c85000144071581e019805002c2502d403404071500c0c06640c6148852880c2d010b1844140710b5a80b07450071030200741d002203004015200c400e0390320010036103049450b0500319005201920808001010488503260369219006554120300d000700407580341c440794070180c007030b504c002ca000380c400811000042202c82d082444402007a000751803c2c3c4a0840a5444490094086038204804001003030400c0c41511614207100d110700c025244003d00070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620086528 1250 620085278 620085283
    0x3151e0501110d050412030e060d09060e2410030b0a0e011404050a0308040c050607050318011b03030c021f0e071e0b0313060c0903060f06031e02041517 67
    0x201d080c0c8095402500d0f4001400e0b0480d0a4074103581c08030405008041c10303414101c6142e20007030b0380c594115500040c50a40c200582c0c00480066008a60510095810451441d902c0075480c0517840c0010000d00044aa1061171406c2d03a005035a40781c1450390280c6175100c0856401b07041e42e14081c4a90381d2012004406000e01134061a08a0b000002400b45000e0b140e45458040c11080141000510380000d030801044088400181c00058140d9445140c035146c0b161343d179071220307058650b5520200900394140d8480c41d4102540011100f1110004ca100c1d0b9080d000f070120301c603100c42540155032022201201c031650ba0508081d090384040f0301070303020728045410100541c120003410700040d000064600c84d048401c0044a100720241940c9a913054900518000140e000800030340c1402c2c8086245940b203111001030f40e024403020804d0b1080c14001508a594902c001007440340c048940340612001005c0c1c01c0340442c005007021a140b89200c0d81020030441d240c01100000c21800c0500d035818104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620087778 1250 620086528 620086547
    0xd1b090f0510080403031512150c2c0301020304060f1d030318011b0c1a01080601030f110a030308091002030103080d020c0313080d11060f04020103151e0501 69
    0x142009000d85a080c5000b0844460305504840203020150000ca402c141c4a54000c2da09010303407076008000c1546a1154911410540342e0a0b90507802524915520300518440e14280b01c41d944c4540780c0c07849680f001c461101802d24211401426020312911881e2428002544141e12074080018503039040c40f007070740460305d1040c0c8a9031012000d00703200112001c00000c480e00308034424000c44601c1d1081c00f2081c0940b016950380d00201544855141401d9040020340b40e81c0b6101e4481511140d80e8510000c1013000d09214030030032a8010001000414405404200032a000760401c041c040385840110700c5d010f4080d40704400003000d040401080306801d01c01d80d1058030003101e007546154515240d00050780681c3c612860b544e40c0c00070341744008450070412174000c11200c03040e8070080b90b5114501903c1d05c10302e0100c2c03408503150b01c200c0a104100400c50a10079016803c1c2d003442c0c0d48458004600501c080c007502c504028142c000400d41154128101402e81c848040c42c54016040400040c0795100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620089028 1250 620087778 620087789
    0x403150e030306010c0320150f01062c0f060c100b0d110f030f0d080a06090c02030d0504032705130b030d0509060403170a0e1e0906060d1b09 62
    0x802c0c000d101d0680e07801658482c0d45074151501001804500e1b15241d034804503040e60401f0f604c20075003c04551618540080d206442801c4046d400d03a0340d9000039240607030140c403101c039103004202030b000c40341111000c4070001c100007603d0358545180c442c000c25400e5219850310803165002040e40e01e8410400d00030b0309400c680c180c1c3c40c6442e020a940d94069000d030044c203038601c07a80c0c1134035072070b280c64034204034050402008004031032402100c100e0192401c501512034100e100d0900c803011807140706038081e140c00c0b14041d9004628140c0904400401840054422400c0010107581001d0000c00e24156008418444910000d020b240608014100c0c404030182e01e0340310300305403d12440d9a80880e603803c0e50318850030042c0d0f480a1038030005425100b160801040051100541000c00303450710090103600051303444021310305034038004104480c80c80d000c02d2519940fa2413920110b5060040d0702d1504040c010b0481400c0403441c9211805803540501c4804500d580b209000030030580c0710018900400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620090278 1250 620089028 620089033
    0x40312061202130b0f0402030a11030f0a05090316060209010e0301110a0219050d0f1b0b0117010510060e0117040f03120e0604060203071704030206060a0b0903250b0403150e 76
    0x940c002c00e00b01000f83c460b05106d25400300c0090f100d540c00360405204280c003025056543e2400071414028078100755589504546020001110f01e4000411108070090319074800084003040da44e4440a507100408680c10031151004103405901c1c01d02400070341c0c0f8003040603240c5032045441c000303143c2140c1c403220300300006400302c1e103038013042020032806060302041c50184100c99544209455201c181d03540702e22081c40d0300e16502d060018440a060582c0d07560188925144041c907100c0f8207903034040d10540340614260a00304521800f4500b1120002010304200841079a0707002d4191041c401103501307941d481d8410b0450f104055200b0341c2d814074801d5544007000014028000640d81d03042c000c01c010031141e40040880c16050192910310220f0303020f011100b1081c5010304e4000d48810041d60414042c0a5000c404100c80e49080141e4860030350180c001c00050305081d00910074200c989030402040340100c0307008100000c02c1c10040c0040d500803503d400e42c3d480d0081c043c00440d28003120860468 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620091528 1250 620090278 620090291
    0x80c030c10030209061c02070309090b090f0612060405100b0a031505040609140c0306070c05150601090e2d010b180a0b0c0f0c030a1a04031206120213 66
    0x107a5408210304a0722200d403030016142d950910209a051180c08000510030b10703801c0540e400d44809400034a99144665a140242c070369420890307069503950b000d020740c00740100e0f000904900c45a02c0b1a60f0043c030041c100409101c03101c0d0341c641008401c0e80c050700c154000030803c0715191081c1c0184d000c0c1c03403010348200056501e15202c1d01c4240301c40030402c9903003a442c2d40115060007000d400817009070350028000401c00c0c804412850380c5100250a242c0039000d4203000403ca5400340270000c03412900800500910030700a400e018401e40000c1c0000c0c1400542c020100b407016050003480d2041060040c0e114007036030ba50854411640101c40c5039000741c0f014000500082080105484074072a090703000300d00c000d1520340050310b4524190020b04800c00301203004550110000340a24040d004007041ea00801330120905481d08044803010745403019503507102403400403941c10700f0b61150203850701700303852600510490245c51541c2e20184070380c1c05a00c214410741c43d01080184844000040c00c0100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620092778 1250 620091528 620091553
    0x608060f04080a0509010905040204120c0e10030201030b030316140c0d031b0f05010e0709110a050901050313242d090201170c03091203060d0213150b04080c03 70
    0x2c0d84600804902002400f041083d0640d000703212000c05460010004d54030f80d80c0781c142c074103000c1c11103001c240c6600102d914001041e00e400401140a450f58400c080881030039900150007130301d44242c405401d407004010301221240040c0008001c14031450640c5400b840303a0440c2841c050865040c0340c400d6285070058400660080e190f5001c14103001c001c40742060709810f2031000300300c1502c000b50080d420b184550b44207060100d26031080c0d070220441000040c4041036018401d024085240c4007040c4d007002a50f4030b540c080c5e00030710703070000d00900c84010501080e55040100c400303400708519105c4810784c144003003103040e01074116014400780400420303006100030002c0e0154444031641c4410382e10908103040d0b900c0707a004042c1c41d401d50b1070417541508004c014012650300841e400d910500810640300d40e0440d076041200d02a2800030701880c007480d100c0d001c21101896204a0f260702e20781e111810803680d5602c594035401031440380c5c60251101d142c00662420846004095842078102d522103420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620094028 1250 620092778 620092793
    0x70f0b06120f06011505090a030c15090509040303021e0424021518100e0f070608090a11130504050a140a0506041b081b1503071d220608060f04 63
    0x111007170003103040c101031102c2ca820340f4107108114950b508450170040c0401481b5400c408002100c941740c3c1030740b0325008502c1c0102d8003c03800c0d0190710f0780b00004402180c0445d00c6a0081c06110740801110b84040110a00e00d01080e1300a500101440b00d0b00b81046051408036203102c0012907641c00505004d1246114020038800014098080e611880305101e102410400103070302035920341303502005511c8000c0300c516942d10381c080303001c09107201c0c0801c0813448500c030300a0b00703001d88400d00c01010502101d135540349940f10015507460f0008510071140c0302102881c01080d0040d40100e01600441d012030405203680d245510102490350300094034100003810000c0c3c09503200343c1003000b201021404104101c840c0155078000c0c0302d64424610b110000091100165841c007504850321081455012480380c0c3c40d0108981d03101c007080c01c4060040296140034420180684c00502c1902c0820345c904070001103a0b810741448408a94035035040c0701c4140100305041c1c1003500b0002c45a100e24241d0384406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620095278 1250 620094028 620094031
    0x60903110f21100c020606091003030215070201090b0106030203060901290304080c152a090d060b09071101060e01150c060902060703050711040902031b06070f0b06120f06 75
    0x1d02c401c08400406101c0007050140f000040003280c001d200241e1507110003965000140ea00d103109a5070394003c035440d070b440d040940c030407039074560050070410f105a2202c0003104002810082595280c6142070002000039650601810603a04c00607224100501400710100058025020014034880d10681149030354402484100e8041c070102d98030380c0d89140180e143e0040741d18081452081d1192414240901500517100b026040c4600200f0110300032800300c00800403403030300c64124040064002c0d41c00d0403062141c009015210202d00c100034200070402811041301c0b0302c0c1c0041d000d1501c800d010a400c0c0120001401d0300161400594140015500d0705910080fa0805125010110400700301440c0c019800e80c54000b4020303510b03400c1e10300740500250701802080722a21241d0302c10100e503141c80e21401781d01c960060018070210038280b0341c1c14500c50f00040c0b06980001c0034130000002406040c44003148a01c10400f2550701e003400781c00c1c8904503c540c81c908260350001e0900200708000002c2c00f9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620096528 1250 620095278 620095309
    0x60e010b1002031c06050d03170a020310050108070c05060c030108250902030612070803070309150e04051e0c0c2107080306010c05030a080412051303080c0313060903110f 75
    0xf40111100044d0200007021294003090f0014901ca04e11810715400514016402c000c840c2d40300503e548900926080380710480300654900c0314000c042c042c40d40700c1c0c84d403e5481038140c10007440d00045034032b41030301d4071348100c40c4445401400001481480003d108041a41c800350040a40600409800101102d9103014401e425940480010b0a590710900004400c0500c1d5040c0d03005503403150302e45c503181c0d0b01c01c1c0b80680100d01c0c2c070100012081c10100e42410344038099a036100807041c42d001003001a01c005020a8030f0a44000c110031035003c00e005080d0701404145204503036424103610010708007800f030120300d0400c0a81c58401d440301d0075071004a56285903c061010758a40c1c4000060340d00781040040034145200218603818407035000000180101c0c09400080710383d0750028011a0a4480c44034041811000341c94100000382c910341c0980040003c00003600c0c204000304a01c89568600e503400000082c101c10350400034006410701015040c581501c5408440b03143c40c001c2202c203500f800c0003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620097778 1250 620096528 620096557
    0xa05070b07110607050d090b0a050d091514100605040b0a0f030609050423030a1b140f0717010b0a050904050111130311060309071e080a060e010b100203 67
    0x201c00810820a4681d200a58018001c0ea181d0030641881c503600e058542041010662281000ca03007880d0040035103400c0310007a95150301d0501d104440401030202501c08403021700c44040101c4c110942d0f030040c24900207868003a1400b9183c840c4196403c04080c0e03018005114081209001010004045800f00c450509140d04022681103045000340404c0d407015260600c2c00b818481041000e0b2640401182c02101d018402c04a00d400c59440703108000030440403074902c010041c81060b0f54058490302500030b42c4008000c801d01c403542c0c0c4c01d0200b1074440066a0300310081c00d2024581d000c40301d43c00c84c406603008100941110021070103403211030160754881c0d44210001020001d094012211119410801e2a00e920004041413001d4105001c21074060201800c2c420ba14106101500d10801802000700866890003402c0d2200e07454080200f11020100d10002c110b0350010030000c101d41e4418a400030740105044007041c01c40d120880c01a200d103015041000c0a03590000a8410140741c2212 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620099028 1250 620097778 620097787
    0xf0714130b0405040f050f240a060203190207050d0b0c13060905030f0105100b03130605042d050a060b03070503010f050105030d08010b03010326121006020a05070b 72
    0x214020a40105800304034802014203010822400600c00741044582c182d0b410b00070714065200f02800e0b0741e01100d1340f034100028080054040501200d9103560402c0c000d0a114807082e40170042004101313160000400f5910006840c40303d164429560302c914611071015112050030800010a81c902c511805003c14403280d000c5503661905070201c034068080d8159208902b5030700c0501901141992080900c6801207495801c1c40003010301a23540302c0d82000d20200c0c120390400c00d00d81c45c2c2341c101900c2038a02d03800031084580000d03884c0c403a240c0618000c0c40070707418102c50001d0050385511000204181103104081c0740300000ca0000e01081b660b40e00203400f040000c10840440d00d04030841e88207561640c00c281204004c61082d40c8128146c40058080c1da0032191110b4041d40d2589003841011903088d002c02c0100041800c04003008004803000305107100801d03601d00b0110454100b06080c1c00900141d82c2400708040101106000515250000d00010011510303102c0d1a202c151250580703c3e1000103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620100278 1250 620099028 620099057
    0x11d060f0103031d040c0e030d020304051507062310120b060f0f030a08031602030310140303040f080c01080117190807020301020c100624030c120606170f0f07 70
    0x1925104d0103000b030001c10021142900040015040349100d90090003090401c186c4140301004481c20f55002429940202a945c08003041940c0f010300180c40e03055803410510403102090392104002400713201c1c2d07813100d41008228039440340300551004110441582c082c07000140d90400d0789500000884000380f401440710007041c180022403030403940c0342c05004800c1e001c02500c140070798094101c01c6854401c1001380401681e680c44141c60002c030111203680108032690540303e04071721610340030341620b00b0140d550400d8030200c05240c10030a09070b00603019064440d41d20000c12401441790303000c044c482c0b44000703801c95102c0e800702100920884400d9000300030300814904980d2810385c050005c5564074800c01203540c0300c0403041d06400405003420000a07100c1751440d05146112403078080c031b40240c4040f42c4290000d001d040101800d12614800c5201d45c55018810310009082545440485044036448442400002040000c1c1054600c092020340300c107110341958003000c5801d10b00356441c480d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 620101528 1250 620100278 620100317
    0x608060d15050a0c1e08190f0204030c03050f0c06091203160c050910031a060103150f0924030609080d05010906140618010e040f0e011d060f010303 65
    0x9444001d0914148802e01031001e03002d41c0720503d125500d59a80d100c295804250451031211540803500090501d0b010500074518a00c04000800b03160100003040d0f9030100e501c4050f600b007503009543c41c2c40301c1c1104005000e014031100042c2d00c2c3c0c4602401e01c81100c000001c10502401c035000e03000e408018811000103000f00101e90800215188040c68802d19107002c411a900500a050007080d021002c20403480d1500440c80030f480d40018080b00090243d0415034482000410f054105600c40101c02c0341614a102c1c0503014009004261071041d007058010400d8400c0c0e903c0200c078600c0c800082c0540c1d00c440c5202841030781d52003100031503007407028184003060b0300030254801c1c440c500d44000014200419842142107502e03d03600c40000300304000c1002170034011207a04020001c81000420502d44c465a9924020540107200080e401c01080040040b1104200300081c103a55411101000020003407005e4010f0075004010406443d0541010441e82410700c0b0040c1840720141c09481030482c407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 620102778 1250 620101528 620101553
    0xb1e1515131802390604030e0105031e180c0d0f080d020906040b0c06130302030d05060a120308180129060906070501140f01050f0108100317190206010608060d 70
    0x4413103500481d0300c201c2c05108074006400200c0c1c1080764140f0307400752030038000300b80345225a4040e26450032400d09000191460f034001802c05000141d88080343c0200b00d01c0380c070202d0240b011050107101d120b0034200024507152090026a109140c041420320019100da580105030503404011280c84110f0360045c40086c0c014407040326400540850b01084040c03c04d80a0a501d1040700121560303910790700301003880150401c0000d001078100300060341065400e90400c07508403c000c2d010340300465862140411a03202050128001a0740d0303c1408150700310052103254001480c03000300106408458048402107081842c415102800c562a01d130643c3c801e015070b40390b0100600000e82d03401e01441c0441c000d2604041e01d80c03032030311880e002c942d0705403650f03502c0d6050b928042d0409213000010401503d81200040c40103d181d81100c40100005a02000c0c1f0421113185402e09a166001030007100c8007584071407401c0c001c5501003401041015070049805401c00c405031000035405290b41042c0384031048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 620104028 1250 620102778 620102797
    0xc030e01050147031f0b040b030f040213050703020d05010506040509010e09010b102c030601141906090305061303120e1507080a150509040b1e1515131802 68
    0x30201c20010306807084082800d000d00d00c9007284003d0361b100d6803244403a020354052150a4070081c80014502c2089040b0241c200b4002801c4107510764512203070744151201200e202e80000e8011a4001007144140a000d000d440111503c0707013414108004031f041c0e0f05052007803100505029000c0b0b46014400e52110500c10009041031307804140c00480500750420f02d100d03100c0642c0741d1420b40703103020710758846044400e94002d000d80126446c140c0009103240c00d004199501890010111140780101000b02000303021944850340318619500b402420490000c0081800c001d0560506000a40c0000603100c0e5841c170000004403d02d05d0400589001d030000b1428504e481e034002030004582d00000003510a880d03030542889800c0c000c0c0d10360100d0031458414180c01240c803002040004803020412a44035840328100740810103480d038100c4070400103444165903080340021000d180d04141401c000254031a12107289464401c00d01d95085241900c9030000c801e4405020200c00511a0100c2d0090344c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 620105278 1250 620104028 620104169
    0x4020607120c08070c0e0906070c120306090609050919050a0b040809090709080708010209012a02060a2f06070e150d05010924060c060f0c030e010501 66
    0x100b0f1701c1c100700314042d24003841c201550541c00041e001140003814900c6170140e41d0b245843c6400c0c035510310758040e03180465001855201c03076010807071040707510960700280181c19000c1800c0c2000c8031078504202d90440d2605038540100516408241c0c00101c0414255214041818035502c60500c149140501c920f403a44c094000c07428031007c41c1d805080042a9808070b001e07030740426501d1244500700d10a01c84403501050b0a40860400303281188500e020b00d10440d040705e408107003140d00280349548480e20190205860784808003680c400321032103425280d42d500c00c80721045d10704820a682d4210040001c0c040080ea40300384111502d80a840b410b0440303031000070039252072003000c004028007424041d00031007910b400c6039245030040040440000c2c001c2d40115445550508600303d9041040000940e14a42c6440c140024103a4900c1401d4107d030280c0c0d4001018414900c0c42425150180d01030940001341ca0325032005850801201e4090000000e81000e9140d03484404d41100300102c6080040e04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 620106528 1250 620105278 620105287
    0x2150a230a0206061f0e0a05100809060609100b0901020a050105090d020c060427020f03010b040608090a0309050f030f12040513050108190609050d0e040b010804020607120c08 77
    0x940d4048081c01205181d074080c1e541c6035640c50148101185040034404004000704200c100c040e014010300c0300c814001403c85104507481c0e5020405031715070514010001040f071000c01c07580d41d5040c003c09801c00d1040b0b4001029090001c0b00f42003d500900a10101400015592403141e0003000640341c01e40e0700c0750080c171aa04e8024609511204083d010744058000c903035460815241c05400c54043d10031810107040715500320800d48004540b00144010016801c1004d210180203002c0694024414606015a160300b0100000c0c1002070243ca0202d466219801c07000000b60860444d01c1a12419201c102446020400280ca00b004240c061515406010303595024135000000500544805442040000a0505100044a209216840064000c581101c0c0c81400c20108102c06c58016000440c0359059601d44a04040e00c081052001c00e10004481300c80342007038040c0c0c010021090174119000d20b4150085807140c4100c00700100150010324081c0d401da170140480c0c002403500465416200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 620107778 1250 620106528 620106587
    0xe011e05122118030316060903050f0f040501110102090a0e0a090b09010c0f02240a021b060a06140117130804090c08220b090c04020f0414010c02150a 66
    0x140d031084034841c02c8052240c01001c40b501303000048403400594803050401c0d104160701d90304000c2000d8101102003200407c04a0f41c1c0c00309400140160041030700409685034605800580900310442884600ea40140024183e41da41e00780080c0440c0c00e010799500e201e039108240100108039890000300401620300031302621070310540c480f000306401512074440103403070351005a076610900600d00104c04520b081d18140020740ea40c1c003540114031820701605103500c0b142100390398024107200800f294885010801480c5080c0144401400303613005c400309071580140004d0060424200c1141c0102c6060041242007195486140485810200751074960f41c40d018910b001d00a56610800018a40700208400160000d2148204000c900303041000305003541d1810180b24000785801254020200c5012140d2504d00081040c82054002e8669031403d2501142d44070035082c0c0c0c5141080568010080140c4548400c070b0102d190403000705498118101d0210783c1b895540c000d821403486400035410f01d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 620109028 1250 620107778 620107843
    0x4031d01111204151b030e030a0606061e03020307090e04111c060b09060a050d150c0e040f0e03160609050d110d020c150901090e010b040e011e0512 65
    0x20340e0400d84600c1c1200d41664000c0705c80600c4580001140c0d26644502c2c130001c1d0241002c01440100a8259420207086440d80c0e41150050742c042400311b04010141e004900c0061881c020413540c42c1000c50075824101c200500b590b00324090000b48101030404141401601c00340c0f0000c5010091440d0b13803480003450001080c5900e00822100e55092070549211841c1c000c11a921030180074012070b89444c501070402c24031140090742503c03039568107128181c404080d400340318002c00742c50710740b070240c02200d1007804100e5541e4484110741c54540b2500755155000071040300d02d55000d200d0007071211368403400c0850050081c02c20081c0980303d8030381c1c41e05425070400c03220702074158808269031590110110036a00d88004a40a81c0d0144001d2540c1c4050368240c1c010f00301c024018901261100c0e2110b21808800b0004e80040200f001e0120b41040792904406049000d06203203800440c82102d118162130301d110181c0a01442210340c42e0f490031303200c8010070410310401030304035202a881c0d000425504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 620110278 1250 620109028 620109037
    0xd0c17040807080d022a06070c080d12090c030221030d0f0c0203070308040201050c030d050903030603010e0f0703020d1104050709030302061b03040615080303100f060804031d011112 80
    0x4682c080d0f14071070300d5024008524880c00410740d101070340382131100b6846c51800040d0760f020190b0007036090040b94080360081c0d0b422405810224010000e41002c2d03e4050600c4040710255410a424200c0344000100080c00040849034146c03920007040301c0508224591000c10056041035100125500110f1110380d00300004030050260200020102c03080c0890302d9100c2e6a2001d00410820350204006501c01d100402030413520006032410151140030900640d002078070060291790011043c0107440ca02840781c03d1040d40c1500c0141680c4181d080010b854001a2002a01c290707200c0c0568400c0c0030417548001003d8500401c1000113181591001c0c0c06440c050001340c0052244400103888258041c02c00e0024a0b140702c01c0c581940d4403a0f031014007400c1c3c04080740c01c0e20b1448500002e80c0180c104003a41c020110001c102d040c03d406c291404108a40b01c2e40071000b00107841e0203201c0425048588941411209409090803d2081c40140e0b0140840035100742e0b14802d01c9002000ca48400c0c001d403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 620111528 1250 620110278 620110289
    0x20f1809010f030b070c060b060a0306030c0b07030804110112240e0c040302060708040503060408180402041208030a0608070603140f0702120706060b0708090103050601110d0c17040807 81
    0xc10240c0d80724440361100d4002e5010083c83c10841101082c9080d00480092014070300c80c0380041400310180003c1107031900031200020100c0d44410062041013880300c2500c0141c2940700c1d003182801c8a42e1401407004001400c00b420502c15580e84d030f10310703900c0340c40c00e483c9440c00c41009001d004030484084072109180d201c14000c1491401d00403869002808041d40150f500d15100f5007070a017540c08018180d8040c2d82d08032402c8070104000903003034600740045407046006280040d152446442851000e40c20070341040d00c034920400090064503048005102c0342900414525102d54466a01130300070403140d00a682c607880354000000b0007035895085a48100c901554464154840e0500003004844c1a01c0d0030016030084d84070001c0c600070810282c00b034103000d6100440c0643c2c2c0e9101c420382c103511880d41a282260002460059540c1500034290041400c0c40c01400074103000c1141500d590010041c001041190f07441c11040c048408102c030141410313101082c4c0e41d00d030303505c8290385d5806452144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 620112778 1250 620111528 620111539
    0x50f040308160f1b12020102070c090c080c09121c020d0c0209060108071b300914011101150602011d06190f090308090c04020906090409020301020f18 66
    0x7115018a99444a849086900e84201da602d55030401d41d240034119041202c0c003040110480d001ca04c05e50804c3c0c1c50303055079400040e030300c62690901501e080315903044043e4450805a031110303c10b621050403030f48120042400d03034403000301c540000d01942580078182d540380300751284d50070703c0b418a0101001c0780b8195021520b180a04a000356490040b540000e54842030207800a1440e5000b2224140d1100152504080b091440c00c91120512909642680c00e58018240b24660151016400300d1070360201c900044410b074000002401d40c4464060010b4084d0901400100c43e40114000303d03407013041c03200911003902600d0002011051900c203580040d0b09041a05060840c4686002030b400141406041d495440ba8422340b80c480d292a01c0d840010355500c11150203c40d54452089030512a80c0e405805080c071004080c03820099030031080c8260320403c10b090240d51940211060104142e034041183c50050001900a009298084003d000001039000724515090341c00340032000200c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 620114028 1250 620112778 620112781
    0x11704030906180f030b04031b14160e062101020f0c010f0506060f07050a02150715021303060b2407060e0d0516210e09090d0e06031801050f040308 65
    0x408000b00f039420311407449413560510060010945e441240c6038442d0083c14a25100c000c0203200d090712100020301520700042000382512690f20500c00c800c80401d03550340c0100f1082c100007022444031400b5101d54441c4e0f03036660386811041e003c9060043c5a500e080001c5480d028080104501e6a10180c000c0101d0b500c0c1611064000072203101d01406660003400040c10058200452855031744034900079221340c03240018840041c0e65040d00000300b600c1c159420b90300c070380301480c00401c2c0104409210f50001d0061140038000c1010000030401c0b41d402c00b4000c00c0c07801014010440c02e07206440070b07490002c40d4588006682803000700030084180710340c00c100300b001d039684541c0da2262540012040000d10811603213058010300c024a10000b400f60243d04486515040f00030900007000403680007080b111440700f101c0e49040300c496a8130a1029010b4140d0b42a4010010180c04001c1c0549100e800040045004803100c04100d55400403c40300030800707070904100010320002e0131601180007407882c10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 620115278 1250 620114028 620114057
    0x60203010824040b1b160f060c090614220f0e0a0624030b19051008091e030f0c070e011d010b0a03020c03030406090506090d0f030b011704030906 64
    0x8086100f030f504010030400a45403041440b40c01070485a44017a248001e000c5105401d02d410505406603124443e0380000442c10320380f4009640394030040c2810700030611010010345405c00b82080804100200080d81d491040302d00e0307261559002403064482c0040440400c00c21682900c800a1b2004c910302d1512595800c128001600e24030700601e103008501c521046840440007036441000d070050b0a000c281a00100045140c00009100d90b18924440580410032401c0a00c015440c90710113142c950000d280c0b61a0455032802600900c07150403a0b0502d011101d003005000b91a1030301840700c50b0036a64001c4800b9980e841d102d034021410b22264a8000040c100d001540510080d01140d403005040c3e8680303096171400350081864a1b003455020000310300142c0090000354483c0d8811040024a00480c0c1091846c0c44001403210040342d10145021800c541c1000180005500629012846a189100481d070340000c40100c58100b00081050204040e00098660156a41560b0f12004000b181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 620116528 1250 620115278 620115343
    0x102121e0d06090c09140d03050304110d080c0601181b080c0d02041820041202010c0c06020607120c05072306040c23010f1206030602030108 62
    0x980020005055080c0503040015a40000e01007626441e40300098803070303a0759000c10036a1643c0c2070032000501000c1052051300c0c0e030507040d200c0100d01135503007034401c1200b40d0303000e411440090070141000e90701c522400e0260f612400c0f0b810701c007944855015250100c0c10a5259034030300a00400c4c40000d51400d144046a5251203040c40c00c0803207420031644c241031914160780e0700d0405020b1030040d6004010b1401246c02c580000c2c0028981002001e410f44043d01001084a02c0b000b8080032030341045503600c00f814055270a8405480c0700207068680810f544c801030b02c081d1031962006014145051001540c1500418624400c1d92291241c00c1c5094610041c0c84c1264800c100c0e40c00451410700440b404035041003400704440c0715215211455044a000f0207140c5242201c0444510303210305400d1001108204064040b140e0711104030310b40c1506140042d16400d000a00241008140f040200c2031000580180004507005a01150741e5611214030035111300e800880c10b006c040440d900a00d000000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 620117778 1250 620116528 620116537
    0x50a030207081516121b09090c090510090905040b07021605010f121104030b070212030c0414031c0315060908060c0703110d091802090312210411010212 67
    0x480c1c14010749075442020380302420140c00f52500c1086031045c1d074a2811a103600c02e0a0300ca82400f000c02e004138000d40002803102c4d480d80c20840f8161700340707180f0300c7ca050b03002960070303080da442141c0b11111203030034200c02c4844480d40d07841001068101002d220500c4401100c590086410750300b51803207002c3c01911020100718500ca0140001c800c4a000350000b07100d05400b8030140015600802c1d20704803281406040e0700300da0810344800c4054000e0003100754041048020003280c01c0780003410344c03070b041c511102d540c000e500c81d10840603901d400b40150341c1c2d001d00c0fa0f949401e08084100d900c2e10b101020050040c07185030701600743d10b8107603540452010300545030f50003103030740d540b00610b00c554980c07095410743e80203d1012810301c120603400c00700e064001c4c060800b900005a840d03240e42890049242c0c40510303c004109202c5204208110841d1030103c1d041c60540403041100b95120711000000e410b000d400c80e406403400b814242800f0402c801c14940040c40c207000d0303084601c00001c80e10a54181c0c0714 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 620119028 1250 620117778 620117803
    0xf0801020c0d05130b0705030d05060d15152301030605030f060627160e120a0b070e03010c0806090601030203060d03180b042705070c030302090604030c03050a03020708 74
    0x1402090240c2d500c100010120341d01c042034000d01d16aa90090003c503508140700450b0540c001007a040c000130118407813554021012900d1446422090700c81c0e20550200903010a1525140c08400b0010b0608000390801445408801418682520882280e68103024a043e000905050002500e45800184803502580010107003c440d1648010062040082c03c40c410349140080156240c041006111500c60301c951031388850070480006004100301910140507101d0b0100c000440a81c140000741c50340071a5200141200e2516000b000b5035040356101c10003075056007018200d480c995440040ba0780034510075510a0a2603c55130015416400111542600001d0040000001ca480340d502050a6114200c5501c042c0e44c8504114400e58040d41204201010b502140304594101c42d03103041982c05080c500300224103009900801511507a8009010503402080381101680c0d010212402507038070801c41c2c00042d50342c1c41d1130b6072219500c083c160090700036200001458600443c0d024800745 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 620120278 1250 620119028 620119033
    0x5040f17060c0f12060a03060510030314040308040b0a020709241d060d080d18050d08010b04090f06080f0d080906060604031401090c030503090a06172703040f0f0801020c 75
    0x24aa2a0844c0e401c036004107001d41c4291100000030110b400340c0329031402803d0200e40d000c5001c0c00c5082c01b6118881045103c13042c1f0703d0400003080881c1c610005c0d03400341c908108038140d550300a040100d15050b102c0d0031440d44a072500c1c0b02c0048041210440034500c21041010407401c0381c0c1d40720811050715180c48100d41e044421000a8105c2c035043c0709000d02c1341e01c17404c512410581c040e81000101c2e07050b03070350f80c0c1800703c0380c1039061040c01030401841380d0900782d9141c160425814a8002802070146105d12401c0700c1c1c56040c10400c1da071030b0f50014000f0784001c2c02100c1180c40c40c949640d5075850005082404501080c1c041043c4110206070325100d8800070304054909880c40c0e0310786058074042c840e8110755550302d06080000a208440a0f401503004000a5407039100d0130341000441c80c0203034001c2082c8050b0350f10180d98580d01c80b0016621151680341c11400c0791030032020400f40744451031043e40c1408001800f050b040503c207016400d03100031580c1c0e200e001c0d88402d015402c034403441818501e2075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 620121528 1250 620120278 620120287
    0x1401060513090209130c02071d060906220b13090c050439050c0f010c030b03160e090111030112290a090819020109020306060901030c0605070305040f17060c0f 70
    0xa10140c101c4040c8901b5841260b08941d654a444141400158680003541d04214180000f604d000301841d0340000088034030f400010000c000303150040c3c403444201c00c00180c843c00003025581c0d44604a111440342c1c00814005a451850624080907031402002e200b80e2034200c541c00141104001d0345211010502c1001c10300b00e0340981040c10501e4205100200308042001c02074440e4244900c1d24542c08a0001080d42c403a0180d001d400e0b548100f07650341c080e40c80083c3d10f00c11102070100441c200ca85a141c1d00d0b0068036643c1c07410340580f140742c00a0700c03201c0c030000c000580d140003c140255500c0c000c03400602148880c40c1d46080100c207142c14010080c00c4540481d005590a0348100a0710703200b00c44661174488101700c1080d0340042c6c2e000b20001b41c0d42d500d4610701981401c1c00b900341c0c41031003100d42603019030540d0b9500801c5462030281204110002c00e4400405020b0390498015252251295600e16a1402020640c10f0101603a03c0c2d070f40900c50100301002d08900035a81c40f6250100400e041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 620122778 1250 620121528 620121559
    0x90506030406020d11040b030a0b090c0f03190e0a0b070206040308071d1909050609010302010c120e040513140607020d03150312030203101706040b0a1401060513090209 74
    0x84d4114021079054540e0300c0f81040d820a052500500081505001564485c9410110302c812a42581a481c0c040e90704a0f040000000366101122121490072a0740c40e00d90319180710f061408a607184641d00a90701e400722070301041d980000d1040501e07202e0420030007160368616040780c49410a0b00e009000c40c5000300030039070241c0138405400340030a9a084000315040c0d000009941e4000c0e46001d000311402035034007070103030300301c41c0c01032a40c02542595000703030651450340020046c4d80c0c00c0b0006800c1141c00017076502d0711841484568071f0032100600a10082c00c040c4030302100d4030601d0708100d584001c203100807450042d000c0b884d54403c40041d005030401052625007900907000016680c400d400740c840002c00020450a0307440385801880c0c0d001601c1b0f10304045a5005e00499070004100d1006507507010481d0440007130031a03486544400c2051040d140d10150f42d014005200300011810b225800105406034003001034424000740d0041c0c0e401c1c00f41e60341c00d504128458403044540041103255000132 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 620124028 1250 620122778 620122781
    0x405040b0d05061503010b0a0b181c032d0c0b0a020d0e010501050321090105090a090911040513050a0605151002010c0f030c0e131b0806040c090506030406 68
    0x809100c050100c980341003031599010305100c02180c2000022010396010149030031709204100307604500342c8088441d2400c021010116004020044d500c0c02c1c2140300b00c649a40700e5001144840c100c030240f0b5003c00c491481c02501161481c00401000d10070b141ca2414100c2440c5507100031482c50340c68022600d802d64a4074454500010401074071113030200038a411081c4648a500c800f50b14034000000c095050104250801c1d0039a1007216107042030020386c0b601c00c5040c01c211695900e0900748250385400c144042944600e00f176100841052038482c80100788090b03a444441d620f0402c917410482540c52900110466000e40340103022030340242170000009020743d116030f401c041c030355103002d43c036240d01d0001401728000b403500400103035152225070540981008a01100b007082c0e0900740030103400b03040010044010301e01f140f03120748006d040410580800764070181c400b44284d40f6210700c407806000e004e4800e4106880082c003030b9192142c51440d441c0f00781010310a0390720080061b441d545075502c9010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 620125278 1250 620124028 620124041
    0xa060506030604091403040816051512132f030d12150302030604030f020f120f090f030d0512090304031127010e070e0405040305091c0609140f0102070503040504 71
    0x550520020340c00b03400b402c170104041e2004050080007400c48015500e84041504415801035028109405c085c1e0617240da00d0059a4162003220344868442c0d4a0514071404a060303108085c00030f441148070704502d445042090a0907014201c18600c65100d20b400740350344c03000c014002c0c2002403001c003016141d405207601310404940e90900c0c1c004031b0a489030002810540192000c5022910365003283d507003550140400000c0100c0d8601800007601d4520b51030b8100c0c0701d907014807413150303000003a944100d950300c400d2090a0380000c4c0843d0042c1e04031030005445940300007160070343c6554020028401020000444058a6206c91440454203030b5000344140390280c40c0454440c400d0040010751390040041c0114000c040101600c021403c0c1103401070041441c1ca01a140101e0825080102083d044000c1703580c505000d0b01d40286455402200c0e0110082e8464018096814070950000303003cae4031a025a4000034910640714100c08142c1d24600303d114601d0000e04540050200f00b10910307049e070040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 620126528 1250 620125278 620125283
    0xc0607020a09020406110d030e0604110402070b0708060307170705060c07081507080a0c140c01110d23070804060b0406032f10050d050709030f03020607080a06050603060409 76
    0x4664094075901044203980050b001000028a42140c4e81c1c140d1401f003244880e0000603060400102c2c01351401562116002000a400f040b41c0700b240440586807075044507011038001c6801400ca04090200419075481507420742d100f0721071100086841c14880a42d413403004a00b1008110715071402040c014950031503d04210343d40107555000410040c20300c103405c591480800c0d001302030b2600c1c98020740ba01c2400380400c1842071074020110072075a005218506d0000d5500c1c2400e4503420740c00701d458050700c0c84250f1490160400b02c4c01030b0601c00243c0003200c244900300107c3c0c540e040030102c1c42c03810220864204000802807400700d00451860b03032100c1c0184002410110b5050307140d8603003d0592511040c200c400401017880d00003907524000041c84240d004840c510102000c40400070325900410001584540d034900215401071f01494180c001541d21802c1000764480300d04002c4e44421040390440007084280c40040ca0020300c0c3d1107203000703a9078010015819500c443c014840107040c1840e08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 620127778 1250 620126528 620126539
    0x4c0b06130303050702180c0a2a0c081203091f0204260d1b290106090e01050a050127030c08010b0a0b090306040f030203040b0310060f0903050c060702 66
    0x484104210400c4a5016601945a0b150f940c1034520602a008004003041b4103034021240921140c11440c0d42100d4640c15680381200c16000414100704001c0340c0c0e250340e0100c082400c1c80b08010401540041d03411a0840300a88003009001c104007006488215a0070095400c000101c076900c030880c00340605d0800ca4110018107240e150100051079071003407100640030b406040c804400009080009100a41d8240b910620740c0d1042c03400b00840d071810300c4d030007490780b10303081264005214201060082d150b6030303401011265a540c00d02070b0003423640e170285408454011001180b03505000602504445040c2e440003090482c070b55040040e00655400002910044032000021498440d0b140e00a01481c000010303403080440d0400030500c0241e40150010030040c4010906503801040c0c2581c803035000400c00d406072044c0d141c100c0c00c0d44960f801c4800701c2072020090008840c402c0000d04240d0304d4a41f548109040468019a280135036440300400d0745e8481c114102540c24010b000e064010b102070070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 620129028 1250 620127778 620127787
    0x8040306020a0e040f09150b0d060903050c07080c03030409020304030e0d1104060815060f2d01030c0219110105160f0b0709030b0103020907050c4c0b06 67
    0x140c440603030b40048680d40005503140a52000f500d054805c1300600c3d500ca110030002800c1a07aa0030840c0d8461f560100609550b42011600a85035201d0b05c505030740c0d020030208075240d55450098815005440124070314820b11001040208000450001c200c0c401001141001c0ca04180180650b0008004074100540181851995210404a03918481c0f06503a24540c030340581c01800202c400c95800100d59a010111f80c10744d8a41ea07116283d040b00c801d42d2041d01c8190900302007100ca0001c1480707030060b4a0a80f00000d4051203060800e1a1200c00f66803d2114603200003080369a407011013030850290010098517400102c1c1d400704c00351070030010304045080c02c0b001050b444010f60369231002c3d90b00813464a280d10400c1184000e95903c10414107040800a0542e281c8907a07800c41400020300540d8031401288102d4013607800c3c2d4025103c9403040b60028541d40700c0250811072a44050000c842e018001c407441c2c101e0b002c09800b610500c1241c00c00030881070003048800703040c2d0005081d411020401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 620130278 1250 620129028 620129033
    0x22170c010507020f060c0a4e20030f07180e1608010305030a0807020a0c171002160605060a0e09150114090403030f1401260303150d080403 61
    0x1d03244034040d25005040300340b45100c00c2c1410200c0c000c0600b00d14160400c514802d564114080d00510301c0242c031400f0500b034800105194614428941140011401034800c00d0a8915042000f80401511090113911000250743c002c80421507225941b82c032040c0000750a1a51801806601411b1442d0143c51344a10440006983d00c8039000981106084030400000461128014104d602549003030b806541c5180c88035500c901440301d0010070044502701061420744200801c2000c1600328038800c507a03668640e00712107000c3c0819403115290044401043c07441c101807003038078001c0703c681054030310040d5250f5951b0003c01005106551081c0300701d001051882d64120301c14462000080200b0450000603205002000164024800c19540f182c2c0b41c202d0f0789690040b0394229505060100c1d5079100424000c0c05400c6412041c3d000001440002800f04580c003001e0520b0780c1c16401d807078110b000060b400d0743c8900c03040301c0c01401d100c01d05c03840500d05d0074060a07000d0554003401e5402d050a0322075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 620131528 1250 620130278 620130281
    0xc0308131509030221090d0503090316030212071412030d0e03030402011e3e010b010e0f060711031c0f0908010e1e01091a040b22170c01 60
    0x4060354090340c0c1d0b1010704408042d010844600d40c10414141928243d4205809444a00c0f628504500071024081201e042180410aa618041d4000c080e0340285031100e05480702610b541c40305134401c15920828504003007011030101c0c00d90300602c407160003041c6444144071140450403c2c243c80c0d4802003000c0e090401c110b01c100c40d000e5407a080030719560305150000400f1142c408a02d4441b5a4a40c0200300d56290804150251503000c1a03c2c4060750b1548105c4d00200f0003490681411012569000d040ba0003040d07004440c3c40c80242c80718241da03c081814091206d0101c007071140c0103c0200040004509908801c400c5a03600a08644502d070007007060a4a0b404001c50f200041900d000b00301a10303940210702c0101402114000300304a0718000e01c0340380c1d906006468041c03981d13125850040d00e04400c2d0071107034680d60003490441d1840d00d004c00701901203004603002d03103a498540d030100d065421130780a603003524420454121b41c00c3c50691a287d6202031120003816102804012b20440b1510a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 620132778 1250 620131528 620131553
    0x15120c0a0b03010f0b0c06040f020d0203060a0c1d0307090906021e0c1c02060a09020f0a14031c1d0d0f060504050f01021306142503020d090302010c030813 68
    0x10010aa00d035498011304100c20750f020340003440300020a12444103111000601395520541000101c43c5848150002c90340380c3d0107600001e500360080c24100442542250040001100c20340c3d10021820f01845580240704904200d0b00d80c10b07000140c041005800325000b0841c8035010396401890801c0410042c940d4000700452540034130004240240d80240a010210340c0c0b958109011036004000e06000751601d50050415401c0c0c1e030b07030b6000c200c155145c1900c400a400ba01501451400b80c89540d904454030099409030f120344520080c3c02c070480c0c0b240b005020750004c41d4840400c01030000008040c803001c503d0b901da803c600c84440700d0700410b40d070110b605160b9020b03000c0003c140c01c19060842c02d064880e1542c3d41960300400088000704662100c90085070181d10b13008220000600012400d4801d059000030060b6070903400da4004503080e030141004510907000c840b8007000301c51050300c0c80039a5102c0070f404a1080c408950129000d90303549503000920000e02d0701c0b117020565810030b00411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 620134028 1250 620132778 620132789
    0x30309060d0e1f0f050c0304060c03090b0a0e0106153603111806030729070b061f0e0405041a04030906030b0405060f0d0201201f0515120c0a 62
    0x1000c0f0480e1a0600301480383c024002c2110a003407006140c0781c000300b8207074400600010301e401c0d9100c0300451468804da00170844c0c954040710507030160808043c410003402c1041c020b50680d52800b00d001030b102d14a00c090610282c02030301c3c1c00001e0344080c0009070100c005a80204031400c0044010400240301038004409580f02e51001410f514814041c1f040303000703c1032140031305442d001040c020607580c0002c040d400c46c2c0304d8400c401131515030041681c00441c0d40050201803680c01280310400c010300225040c0c07141304256012042d80085000780025000c074840c20502240040c0701415141c20300b40c01940e4401c1c01090b00d903110310003840305481c4142c0112070035000601c01003400e205059240c0184175200404440074081801c12500280030744d5656400c0d94450005981b0321000c59001d800e0000c1c10300380c00359035203616509480e140c5880704040c091200d50f44410a441c8100304040e84946401582102c4880400181400034080000c2211440210910076540504015918503510030050072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 620135278 1250 620134028 620134063
    0x1406040807060c020a05070e0c070602040803031503060f010e1302060a1106010602030c1902010c1a2d071206170106090609020a080c030a020d0228030b030309060d0e 73
    0x84841c14010b0032506008a0082150000711651000c5100022507006940e081c13102075005484480d1b007035003a84900c201c01822503001040024800030302001441c42191354962181210f40030a00709511070381c04035101c841c090b03440d0005224100050f18815442840090700c0c411400300380c0c00081d582c0d00010194000100217080f403103501c40003802001c0c01011180011400d05030344d03030350068440101c220035072260040d0380051401d42e0322a014200000e900240382d841030001207082905004012201170210030401034150340355440d51003940780507100340d10b000c00140d00c03078900466655018110181c6540d4036050046110079a014101149403800000020040d190010000070388510b03600c495042441440800b500355004008141d00c440110000c41da1307903613580f111100034000c08290550142c8040b466103000c6985c15842c03850101c90381413110201074401c200b01c0544110005191705500103102c840500e0a003071010703200084030200d010860005d401242450200907524034107905 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 620136528 1250 620135278 620135287
    0xf0706090b100e070507081e04180c05090d1e0503030709052103030606070c180b120705130b0303040312260c040605210c03060a080c130914060408 65
    0x2c542c116814000380450a440c1580785000c100103032083c0600e410240000400041141c85480d48107440401c0405894a1070f4942d500e8000b2074401088107029814200d18141981031258081e0082d540301c058018402161045540c1d031b00c002a5803c3d6107c9030a1074000f540010000f6014000b82d485000d0740c0e5101203017145030004001c0c503000540c89003040300d00c0016164501040c0481280d034400310584005980d0350562408280c135030815400215128000441016001c40641011114060031581a00c6402441d51794545814241c0f25003030b40030003180c0d4900354620080d004060361b080d005041d40d041554945460601241d41c00c2c07400002414081c5002c244881300040d44030b02000611641024648120303002e80d070384181e0040d10244a408510410903050707032002e40903016091a140e1083d410048071600d4143c106460f500d125aa08140c04100840006450146554000c1c01607100d4040124804000c201c0c48078181d44014011440c07100446040106070f0185205000a998a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 620137778 1250 620136528 620136541
    0x1806080c3003210c04050405070203130603061410020c040c03090215030105180702060f190e100606030e0c040902040e030a050c070e040201020d030f150b04080601050102030a12020f0706090b 84
    0x1090382c20400030030400d02c00010710404013a04003d03282a40c2050b40c00003240d49501c002680755015000a10f80700304007a0301c0c045400f981c0740e00103d04494090902000129082c8104951100008001f60040e800410904118a4aa007110f5100e00550400142042d52500464084003180f40042140360b000001086141800d58104519004841c40c101d158142021b00a41b85c01026214488045004004c070f0f8007800c468907105448030404000b0840311884810480d201c084543c1d62202051030003800240942c02401500e070554800c03406088041117010820009080c00c1c401a600701d6522855118441d60800c01054894620303200d081c0c6810380c8001c034901e480b041d50440c0c02064451000e05c80141d030001501c1ca9121210b00b8042043c4014150351002818000070b001f4081c83c00c6840054800c0000009000713880100b400d42e0410380c1c903400166600c0c86174601c841c0029a001a94004120030356002d48041c1c1208400a460000940c40714070544680740000e03600c650500302400035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 620139028 1250 620137778 620137807
    0xa090204051e1003051b070308060f121e030d050106210b1804052d10020426030403150506040b0a230d080c071806080c3003 55
    0x30100c4022002c980401c000c0c402040380120442c01801c10702d5110000b02d00003034078100d0581120000c0c0861651074000500b4000d0802005542031802000341000c0e4030101e092180c001181c040d040c0d4020003043d803501c442207086980c000c4c0e4550341400300f4070034110480c0e43c90040c01e0080c565565803640001e030400c102144001c0c43c40e00454001e28204004545481d0750320034055060011b4884200c0c1d55a504082e800c084034141d2140200c00c02540c0e003111420a86030340c1a200200300d00715007060806540d24403c130b00c9103010303510004041c44ca41040c21001307010a04440002d4005423030030140d0700d0b5100140005646103201c43d443d1100700b0494241000e10170b8400d411421908180424a410029194403a84910100781d0741310f94503c40a89484031040f40444550010020396030b0014503600c00c6e100e070001e0003048404d04010035190000d1440340907a009451070b860240207014942020020fa030000880008040f8091508002407021120300622264000030095a510901c004c032460 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 620140278 1250 620139028 620139049
    0x4061b1e0311012a0509030c010507030302090a03051e06010f0b210a05240112110c1c020106120803060103050a060b0a030c020d051c05100519030c0b09030a17090a09020405 76
    0x800f006401c6c881c2d0940765a00142c0c0d02e030304641c02c1c01c0841c0d0f140035606080700079201b000c1c9415084208408000101f0500094410701c1c0c0c010354840060115040070360f2074a4034400e200d02cbc0018904100c09001611070f110060410030b6042011120404003132030104044441118034101040e9a8000c101c4134002c9a400075540d60426401074958491b00780c0041c02000030201011202c5030340c2d90744080c00d280101e044030100c5148000f1514400600101030000700301074070111005500305540000c84a4641001408050707101101d1401c42d40c802d001100281030003002d440101c0d440f010000b4803000e4803c010301000300030b9580071542d1220500080c0c0741c601030b07108410401170104040300340b002030402401228a401407010403651100c0c11102a82d0700190400b55109138115046100ba60420710524116446445200302269544c0199030841c020104125016041699903000180300d807411540f00707030451401c080c2400c1d101c901090f086145904040800707076000909015510381000c068 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 620141528 1250 620140278 620140361
    0x50702070f0e1824100f030c090c2309100807020703110a0801021216020c010807110f100f0e03041a0f041a04061b1e031101 55
    0x180003864100d1212862a0090011440000036000003403161810b1001034804111340280b910b0440a040c03100d070302400140d40801c0c00d0101c09000043c8910100d0350031003241c2e0800074130032410349410080c1000e0700d2403011700d004200c0013000d80d0001070120303442d0300902d100618005443d00c00c1c0000b444107000c20b24080600340308954041100032940004c401c4241c9a00040c0c0464aa61100c04914101141d421102803540081444c09480780101d51441c4035001d0215415021401d440060b071312160b081c40300d14001510a400140f40c1801550038500301c11150007101c008694080c5243e0829000718000e82101d40c441014a010700d0890040d92080130450002e14507007403038000b5001020b402d420b1900d1301014003040300f080030040b8405a030000c103651407484509101074680346c1030365889401040d0201c0d004000c40a0b800c11810506180c1c00c1e4442c24003020b0030090300c0528a01d6004007811401c001d2032310100301f4450400c1c002c05400f441404030311100248601480c45080c54902d41c1e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 620142778 1250 620141528 620141549
    0x60e010603050108190b0105011202280912030f030515040905030309010c1e200109050709052224150501020606060f031b0702040e06160c230307020d050105070207 72
    0x261020410b02c46c1030390f04503802400c1c0b4800c130005200110020780640c010a1400d004201000403400b54010280c001c440056514a1005500c2d142c1015910300145400b0340010041c0c0380a4894034029130206030000c09451040a0a1600f42c000405031803807641d003211550404820b00921950901030205180c1d55424001081664a40a07003034004006a00f86c0810103070400305107500e203000e040c10010389082002130183d000c550500558901c1c10b4400c13542003a04d04000034510342d040c085107a040c0d60340e44a403101c0148032615440d84c0c01c000000851410729030001201100c4204d4442d00707440d0fa080c19407102d82c0b02d14003000a4189030006144500501c01005000d900e0303800c1608482d0311103842d00049a00200c0358400c0d141f580910306000f074005142c00202a9403110003e10284244540c580d0708450343d007090002c5400301c42078540104105a1440c00700840041c1001520044600e50102c07410072095030001904003000780402c0e2641e95403001031003031095044c800c480107401107004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 620143884 1106 620142778 620142823
    0x209090c0a09171c030c021e0c0d0b040210080f131110030218030c0112050604112101050603190e0f030a020d030b180103080d060e010603050108 64
    0x1c000490210a16044c40881c0b0900545401841039406000140450a4a00341007146501180749900503261100c00700d448508901c044640070b1003007482981054018005090f86010030700d402c2265403010044034103017030341c14150080540041e40c0d0f6183c0c0c4a0900743c4110803c8201580e21018025a4010065041d0007070a07440212000a5418842d0302e410599110a00e521090104901503450340300c043d525030206501c03000141001c980b0038220360010303007154028004204004c8012000d0a050a50081c5640c007619007626414510b05001c1442c40103401615200b0422580314045900d24000901c2541d05644100048a07142d20010201940300c240902c2c052000a180030b0b0f0401082c80c0202e40544240d40c8034000d43e1059095480300c1d041984103805203081d043d03c42000003411030362440310f2802401e56580000d203550604190340d0501442180c110b45081c84140c = true := by decide +kernel

theorem cover : BRFrame.Cov 619964028 620143884 := by
  have h0 := BRFrame.cov_init 619964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619964028 ≤ n) (h2 : n < 620143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
