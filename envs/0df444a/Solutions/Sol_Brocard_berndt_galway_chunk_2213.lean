-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2213
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:00:32.826317+00:00
-- url     : https://prove2.me/submissions/701270f9-2e04-48bf-91c6-0f31be47044c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 397841726 ≤ n < 398021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 397842976 1250 397841726 397841791
    0xf09030d05040302010c0305090c15030a0e190c0f0b0a0e01170709140402071716080318010b01020a03020c280801061d090604020d0305071a09190b 65
    0x18001c100074074250030024080c014251003480860b20b4200801c8140c1c0020424122302503014140760355814114454404552000303003c4081183e0f16044002100c2e0181700c42045500031101c8004040300c2c60410502c009003c1d440b1400700400c425080090491801c203650f0080e100d81017641c1e1000c40c0b6001601c80d8501071804200c1c00d0403500400c00040d40100510094030243c01300e0f0f402c203481c440c06000403072140d244082c00000748203030b07400c660800c40001403050b405003001c03a44480d02c007541c5000040d0000e076414608000700c030300d9001c1c0c1e44400744901c0406080900c0105005001520065210a0300c030751074a02648810325080b0701c800c9198000c4642e44094480100c0703c66403030314090b00070480f81c01943d01541c20400b02c400b107041e81c035241d00c5c006c1c01c5500161080341c44507420081d1030900c912048080c8117003802560045596465001720404028860403818a0000d00241c1090036003414100010600302443e804a1258038a00398001100000c0e0540c0c90000c21036844000201c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 397844226 1250 397842976 397842997
    0x20a0b04051e011e0509070302060c16030308160e0f04020a03060b04150f020703110409030306050d14060106020d02031c0204080f0c040b0103050610030c050f040f0e060405010602060f0903 83
    0x44200204442d005600c80c035400115200349003c0710301d0310074142066813410344241c0c03016405a2400c1c000b624000004284514442046514210b4845c0b002048071800f540180d01241a800c100546204c1c00d400e04018860300b840c1c0b00181c000d4060004901082260019000d6640410604074032806a44880c0180410b00c1007951a543d8810440a950780f90014440c001007a22850b45400da00000303402c410f89034003414494026503001c0038400104500001502059103d0000240c151070300720031000d516020f604032441c0500241d81740c502c2c200e8181c1c4030504540c0404034458810ba0701205030b808100c00c0c1d56100c05095841c16007200640269007280703107a401075441416403404009140c601c4c43e036080d10240049800c00c001502103d81c01c542450b000800e68000c0f080c4c01c0d100c0c6d070103025098920700f40f0300d0074401c10802c01c240c550480d401000748940c00314000e1040c3c800d080205540920219001e0001c0d40c1801002512100f0280c4500420500c0d000481c001c127a050082ea050f9002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 397845476 1250 397844226 397844263
    0x201020c01110705070e0f0a0c0504030828020319082706010306200a030e0a200306060f0d020907170a0218030a02092e08030405090a020a020a0b0405 66
    0x2c8403a82c020480c1c0c040c0904a0340c034410250006540f802e02414144074801c003646400a6a136003000081c0500882e200c11400c2040400001c000600000c000d000c50303056506007800031540d0807640300000a820801c0c3e8055602c10b00440d51303a03440600c41170480e441245040c08964442581c055250b80c0e032150300b1a400000303007840d0306040c1c400184072412640250010300c881060354070740f140c2c03181000204d0400504c0c10081054000d0090704010116003502e011502d0307462140d140c2e000710318074640c280d0005203001c01d4040810318040024540120701190380d44200e04114000a00080001500a001e0f000c15030000340c2e214014045c221307000c0d100010150503850402840380c000e40c41540580d590344c880c14448000d03405c002807070310f000701d6015144490b10344522050754100007010000860a000c0e07480c0c2c551010081e01041401081138600940c0c07554244010003e06807401404090b006105008a00d0b285070300068482c0710b9a0040b440780990341b12420814101040e101c0d00000c80c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 397846726 1250 397845476 397845491
    0x904090b07080415182010030b0102010c0e0a090b0105040b0f04030209010e10090e010b0d05010509012301050108040215031608061005040b0901020c030a030507060605100f0e010201020c01 83
    0x160030090b50b5203e90310555055450b0303544030285134101e0f90320880d604050704840c51602d00084c01e0801c11248403124480c0e0a80080421001a580d031560118034400242c0700c000000681d40c090145014022080c104200049140404911006014403c0405240d243ca402c001c01e030b40181c0454000d040b80a84c1e03140d0b202620707905907005500c2844100d01611080c0d0001851541000c00c4074095808001d1040c00b0318034000c02c100144c440c20b01000c1c00380d581c4103481c040c01c0c0c2c3c5500d9006d980d58404c06c00032480d86840c1440e9030840b165601094144070f00c607020080c0da242c1005141d41560800d0070316101c03546950011030340c10042c504680b8901240001404102c0ea40b500400b444601e9030740d113003c16a62445c3c14410010710300c14641d400316400340030030310405040c54050103810700f043c4111040c6c40000c0001900e040f44040341074005c50300000e0302d1010f0200707074090000a40415103681c100e502c00c018008100e9041c029000e0104500341032081210384c801c0d0101e40c001c3c041c44009110b1300c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 397847976 1250 397846726 397846741
    0x1b0807080a0309020324071808070801150f05010f18050d050a0204060504020f0702090402151b010c091a0310030203010203070e01110601050d02060c030706021204031d0310020904090b 81
    0x6183d4070006030b21a00c60b0000351501d9600311158083d09034945039012500751a01c80d01590407003444541d0303280a0800c8100800e100d201001010700903e0508004201e000340340c58041268925a045103005c070042031000e100c01e90304651400c914103058039001c2650403c040c00000c004070b2a8010b15401540d020841d000d000d070000701418041e0007113400300702d1650b844041104074030860343c450001c1c0340140700b800b0261410291135588180007400c41d020361445c40c4620090f543c40300c401d807400683c510301c4468500d0b10903c510310151400d8100100114184858a40c40c1c81000e5007044800b400040003034146c0709481c02680046501070b000355280d01340410003130310310380804c2d560600140c0c0303400c0103c1d8090070008443e0b040f940040c0c05882c50100a40900586500030308404c0054030041182d00700081491000f8540c11252000380991410640307001840e0f0ba10b04040c0d98410900c10b0b075001d0079a5808a68640c422070505001603441101c5000f18010f45202c5d200503140d1042d100401200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 397849226 1250 397847976 397847981
    0x303040303091b031e0201050904090f03080903090a0b0f0705070e1509041703090f0d1d01020102180603060a090e030a0315030b040b0a0e011b1e1b0807080a03 70
    0x61520800007411a03d202000300d0003004a9440b01400f01081e08044042110724030303c4481c089801071520714505919213002c141030310720f200c8088401544001074901490790002100e500b00309064051443c00e50800002820041180124811117000195216031000705100b00c522041c0e02c07509542c1c040e5560324009414201c1103e5810b460030700700707010b52050b192800d1054411130740603c0e50203030388a040100390101e0300010210540f9120b40c03c0054100101041000f242d03030f40f00d030f03a000e46a01114041c01041c0030110400c0741903a0040c01200c803000c2d08200881c440000607188552a0380d10f100002e00b100c200d0394020700503286007820b6001c480c0c40200042c0b00d0020b0175102405401d84032040030070000e150784070142150402401080004903c0c07101160010101c40b000b2507259955a0034500b11010710826071b04241d000d00150301c2154100740e28030b050030150b4840040f4800c0c1140d003c1c0c828494110794000464214034213004111080055848a0b40c00050468031442c0700e0102500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 397850476 1250 397849226 397849241
    0x903021c03031a06160512040e0405010b0609093702030108010b0612040305070c03080f0d0e070609030b0612030301080601031406100909050106091b030b03010b010e0105030a0b030303040303 84
    0x1e05111640400d003c0421094a04450242115140040c03440d00500c8001c0314280440b050b004a01c6d0500081c14606d000e08050840b81c1100c80007400d1900d03080d0b00311452100e043d40240e1090042c290190781d440720a5a0111010b52119820310f001081c101910000140d00c10f0803814101c1e41c8000c40c1020350142d03050300d0000d0020028444408100304080c040c02e400e4407940c0000500140c0064440c3d009803980d00e12401d0742c0300485469075203010b03864214403505010380f00003080d8440e0066480c01251030140d00140682152820800010b0010100b80009020700c5012408104541c44154040210341130b02029240c0f6943c503460310300c2c1c98a2080c401600d01c8001952407690f161404664140142c510314101c03140c0303603d002c030a80c02070000d00030151a65540c80d40001286400c0b4001c0c0b00c802c030b4030380d1381c201c0700c0c40303000c5501604075081820b405001707a15209101c500b99170800c10020302c2c405c00342401500ea958050540e00608660003440c3d03007501000c002c0c08205601030300030b0301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 397851726 1250 397850476 397850483
    0x2505010e0a0b091c050a0903120e04050f010803030610020c13061a0a020c1e0406080d140c10051003050106080a0c06021b040c02160b04030c050a0b03060609010903021c 74
    0x5042d52a41c0c600159602400d032000c14084020b0040b820066000d074000300b205080c0750a00b10905070766515440c1207420b40015542c0868452002a0f4040c90584505944124007110070901c0394185487c603950381c04028103a41c055401180c1c00d030a120300801c48002d409000602d54420008801c0d403500183c082845900000220400c280301050b85004c140d032030069566000b00303219520f4108201e844000c800c8030098a6504041618080d1558043c0c0781c05003510a0041034050450500140101d8010381d140210300b0083c40140d0311144080b0b84100c005540c0b440100312a16200881440c41055500003881c645c1b0306100003031014404a140022113002c1c0b980240c0c0c59a613802c0580c1c58410045000c00040c210711405001c620301030b807100c2c01f0301d0f440340304032202d003007c130740c6030103540c10258010118100012030200302b0880d000d0041c2018000540700c2070126803070040c0c10300813404003502c458400d203404a1240703900e0340308041d078900071500200760928460460f42141d07002ca42c01903066 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 397852976 1250 397851726 397851743
    0x204060807111b0f10030b01020c0d1e020f060301030b0403020c0a0e0f1008031c0f0c020d030504020f130b090601080910050405070b0310060f0309082505010e0a 71
    0x740d0424000c0845285074440003024162415042d420f5100d50840014040d41c041519940c800d465101d01c00e000000500035280041c802800c500003900e406000b1901600c1180c000b107402000510825000c032019007a5210812144964030001e0041844603904541246c8040f000100b404000310310036000b140203070240c0c1c1007402c0020503c140d00009010b0007814004010109441440503034166910004c1c8050201c2116103c40c022419075120718405c14403d4040315645004e07036403c0c40b03007900d203c0aa0b40700708450380300c451000e0340b83c0c51a181070400b0306550308002015510750700240d010814004191003078850248a0b01801420038444c0b81d8064142c1c1000a440d6500800144d030003440700c2d1004100c1040c2ca4289000038200041c0219141d0040200010300c010119001d903004101b41125101d5031401c00500401082036240a1001c05081650140c081400e203811503101d10281d480c1c0d4890003000302480e04032800e200d280242150b180820a0a0f21280421800403080c442c1100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 397854226 1250 397852976 397852981
    0x20c07030f0b16090e0c0304150e0106140d0b180f100501180b091f030f030e24090103020c160609080c010e060a050a180608070f1107090c051c02040608 67
    0x104e03000c0096005d00b45d51080e03400b0204424002c07107000b85510070f120380446040f0055404280d02590f100c020310881aa4443c98240b0040c000103003002c1242006903400404c070203842d250481c00303480241032180010040a6040c81044040c0040c40440a9010864600c0c40080000c0030041c402449045030f09044091a0a04200c0703130b004024540c44002c1a00c1c0c55516001d0f64002500d59410340c00a008240c60000400a00c0301610007000e03030700030788540010100080c00d20900030113400600c035000104a11182045030700c0e405603007105a084c80e0050300c800c42c1c20b000519020080c1c042000c5409840b01c0001e070316511221204c2aa094281600c0803240303500019a4414014003031540c1c000c1040c0007402c5804d2003440940184562840d003038400700803842c0d0314407407080a9080300340024900c6003089016034115400d5001c4004600e010640e406030205580d0b207503462170090000706a2920440400c4511600950390040b010340c42044001003c500c0c1840258810711480000c60000d000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 397855476 1250 397854226 397854271
    0xa140409110d0b0616080a0c0b0411100f02070b0f0403060f0501140f06041e050909101512030f0e040c260106080f060a1701020c011103010612020c07030f0b 69
    0xe469011021811401c4100a41e6440429680100110f00c0c104413200348c40c800486e505003403003402140580414006d15402c002404490074420742440300b80200c500606c04070b10b60008090080b54090310001c1e44484035072003d100344d88215800079140a0070050700103d0151940d00442c103d075110070549880300307505010305c503803840340c03d42c202e500c2003040c0407c12981c49030b589801100d03801c0440c03500803262603100164000d41c0941c0c0400c07617076010400728100100580708148252482d94521035096140c4001c4c0000003907002001010020108084c01d90540141c40c1ca055501e4000c00a205229003510020500c0880c600b004021503000e1054010074251001c2442c143da200d40e40740d10699407200c20a00762880d02074009504507080210008400d124181007866804031b40e00003586d503500104016096961881480c18070000410040200c42e4020f6450208034180240158a95900c0158242801c04a900141019804800b05001c000b64008000d1186070b103130f402c3c207008080155 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 397856726 1250 397855476 397855489
    0x501050910050c040909020406030503041509080c10050705010605030f0c03060f010f1211101d03070e0a0906060503070e010312090812030c0715020c0c0102010509030a140409110d0b 80
    0x503126480060200320174000e0700501d40160707240301d0002d00f0203d04030359a6030704d0304c1c5542d0007070303100010348107119081a19840c0e2110070840103008400c000c1a17a900e80700c002540846001ca181c000313102c0c000515404114080d00504c004040083c203566031b02012400547d01c2c0c4101c18481d5100b40600b100107540104c200712507178182e542840001e01041d0034009580b1b05c12500380c0c0c0030740301d110012102e01e0140e560395981d0301e0341c0c10a517500c0c10951101d602c402d11840d200d03540914880d4001c44014002c0c450074025031684508141c001041c822000d040800c000c0880340c0201d501070152250119504140f40c8555049070311554400c10f07000c10310314003210780894a004208040e08082c003601440c884103401307141c10041c001c521078038001c099581e100c441200c20842c02d40490300420b08210710202448504c0041100303000030310607071030811100b9880744a0700f5a080c041c03144888100744203003260001d50340a080c40440400c40d034000800304008907001980840c002c20300380005a100c174180f61 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 397857976 1250 397856726 397856731
    0x102010c08220c0b03250f020d032705060708100e06011d030105070908010612030e150c060901050f0c070209071d06070c08010f0204051008060402090d050105091005 73
    0x100030031100902500c4a24036240e00c0440141c640ca81c0441012030910031404c025800b40004c0400c03e00c00c2c009404030100484040300d01c0300305020343e0b88640044990042546490400d1a00d00003030b1880743c0c840c41607411813400c0780140c00b80c411040d0510802130001103280c0645815202d00e441c5580c0c0900c1c079907002040340113503442e4038040d001084003940038144401d0813249044502401c4000c2c035000c81d085603c103c2e000e00000702d03c140200b06000c0213224100c007a004010485c148414181c82c0980000c4511307003402d008050f0781d1941c401c0c0c81d00035020f4881c080450700030b65a80382414a203075406880e0941d856002c250b440808142c1c80903032001112800d60b400f40492032969220f0400b9110640c0c03020092000102e41218110f15a8030100240105441245007120f50350400014500316010201e40b11060f92042100703100c2607462003c0d101c1d5942540c40e02e0a00c954560000c100640100d17034840d5003160311100e2250070000c040d00010300c00c904810880300703501004225101079410a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 397859226 1250 397857976 397857991
    0x1a060f04030602211905150a03081b03210708160c05070305030408010603150b0303040509040f0b0a0212070e0a140a030f03180f0b04051e0a0308090102010c08 70
    0x304020400a01d05402408285460f0380c04245020301c04805050f844504481e110780d1000010440d40010446100b415007110540d1802c0600054030008607a5000c200e00010300343d4074020401c1d01c0b150602041d42540c41070f01c6802e0301d441c1e801c1c6609400f89a12001800441c06070400001743c260383c802e800207441a0f00e00382014405200710a400e0341c00e021441010b07680c0f4002c00c000440426400c000a000070b0100b100000340952071030a110018812404102401070b040604c40036036981d001054405440c0201c40d003400e180c1f55480c099090301c0300c2e8240241102004010002270301c00b40d03400303040c03070050b103141288459449041c100d5180900d0501c155025459000500540c51100302013038842c3c0001e800c0c160340c142c698441002e069100e002c1100040e00a5072080010440c02c0807030401480074404102a0905100340e40125024074010103000e43e562a50f14982683d80ca80352040c4550040c15090441c0c0d03c80c00e02d82c01d5a800701056a0140d17081a14440c0440e2003411500c3c400c054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 397860476 1250 397859226 397859257
    0x90f0606230706110702090106021b0108060f101206030602070b1f09050a060506071b06050309120d0f020d05070207050a030b04080702040914071503050705030f06221a06 75
    0x400f5a82d42009240850b400c4034201001d108100050300c1d81c240c0c1c24003810494000f403a04800c446110005003120f10801070401c0089414004240c4540d403807640d041c0011a189000e12008082c11103d641038407264441040c00c0650000038424141d006001403401420101c0050740c846105a01d03006014010031002d03a03100f0300c01c00c0041313000d0380b103c0c0d00a01941c1c0d010803001d81c0ca000142481c2c111090a46440034041400301110410740b2250300103114a05001d410f41c0742c800c90540d02c8200304000d151a0500004130000c50001c90b510198403024484c00440d1104e040c2c54203d00184000c80300700e80075114000340403440d0f10b44644540102d0741c0c480311225441d07856641d40070031034005500480e08030343c40f044c021002441c50340c01c541003504c6490080c004140f401205280346044c1c402c4c0c2e081814984030030b000c0c68591110482e40c0c003502c2403440c00002c0d252680803800d080002c0889802c0d00e03041020305c2d450000950043c00401a185414020418012040201c144680354200d0171314007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 397861726 1250 397860476 397860487
    0x6011410080c0316050d140604060906180c1b031701081903121413030327061503020303042303030910140702040911030f1513020604090f060623 64
    0x800400d00380c400c0750a0703117030203410810314202e0719007070707800080c0c1c01607034200341c80e04001007410700c1d11910009007004a000e0107810f160041e0880150300c20201640000e40750001f842800e40205400b070851166038600710804200c034140103001d194a208001039207800752000141083c0002400e0a8402907032802407401c4500c0d64055401c408102d1090130200d40300c0c60003803c01c95200c03481c1c521070b50130038810b0039218041c0d190080442e5840c0b01c08058150389185254400544a071f1a4034030540e220400148894003544105080a0107610080d41803000050214005080d01e5403034000103d01c840703010b640c0c501402015200d00840c1c14403600650005040c82d00184620b171143c0098160035030365071910303001d500802d05a583e07070304040e101840041603400d01e0741400c02c0b9070f0840c440c07a400940000090781803d81580c0c440a40415400f02c2c01481140655513200f0444000f803490308807c2040110b000d00301030281105125a001180036100c91484003040180030130440c45003001c10b1841c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 397862976 1250 397861726 397861741
    0x102070c09050a14250215100312020d081b16080a030e07080627030a0c0201121407030b130614190605030112111002060f0108030c0703140f06011410080c03 69
    0x442d16002c003400f1841000403200c1f00c0d00d0307140d035154021031040114401090841c145106200102140281154010f001d0803118030f40c40042260046421070411891503aa1905207c2c0b0380964030b00d900c0b4504034034644c0c0040121802c0200f1a4080f03548090050345941f0b02015182c04180c851403017241c00150002e58480305908102c0400c080d0801c0380203032000600e28252440c2c01a0554401082c04950401d06560b00082e000c80007118940c824040d0492480325121428405001c84003415290400c41d10980d90b991901030088031140020460b00355a2031480d569280c0c0301c0d5659002e02003c0c0030120115030400c20751400c0d160140c482d645143d1822061004000c41d01d141a00c0341040c0030486207969446c014202a4112950300900590500700045c4029800c180c1c000c403070785e5104104412500002180351400c072074000d000321040c000891016402d108007030a004c0c03e1400f030320001044000030a4900c000701d0b1021345400040d4008100c0555400b4415100e2a66106d0f0034000280d01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 397864226 1250 397862976 397863031
    0x405010b0c031207031d010603030801090c1e211e0905060f0c0918151f180905090a11060301060905240d020c0f03090d02120102070c09050a14 63
    0x1321072900183d1100c04541d8410144594500c01d08030380d44510081043c150b10440036805040381d41c00811030040c4180c000350200340940c0741584c040801c010010906400342c01d096496058500220f02c03250081c0560788002c01245180d04030299045485003040b084034420304040341d80c0310006006075201c0d00400c0e86401d000410b4000302010410249801d83c4441c1c88803a1109020030008190742080551059181c0c950900e403400748166030313040c0c1142d02d500c05070141a2801d50800060821040b110300300043c0e02500320880b45800c241c14840b03480b200003400d010050007070350130114040c80f120402400d07200c280708010008500c0c002c20301203071820781c0014814009100080c201103030071a44410040d00450803a0700780d290301181d041e803609028010740c400725450401071440e022030640010680014980c01034003800004282284540f402d50480d4a425000004580150f5451041d600a030000300e03205031040d41040c406071640c025520301a40a40340460b44004109190380d000c115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 397865476 1250 397864226 397864231
    0xc0a090e01050a0209010c23030a0509101103031f03230d08090606100203090301060312020d030204080318061b0a0c0801090c05040b21060f070807020a020d06020702040f06050405010b0c0312 84
    0x4515070601c0e08223026180c200001c1c107185070326449a0b1b071142d00707500400092880c020101c0c0140040700b5444440d010003c0100c9510201c01d10a0221f40b4112849220011380c80b0741006004410720000d030308046000c400100850803480c02111003280d03021404a0b0b005005841e102101c0d840440410b8451810001110391690544100ca00b0052550006425101c459001352402c2d18005960b08420b5410302c80004604810304040d49460b03e00340c1959543d22404080b6101c00080302c036898030703d5a900381200c421610000500c41101c0e4440400ca03100c00405200b29030740a83d6080001c0d102e031060099001950300580c18840b200d03e040f044c04094481004059840101013441502058240314080c0c4050031040040c030f0186046c02c140e0303d60443c064003080500c20b00404020006a00140101d14254103039003d004541c200c0c500f950107402600c0c0c00071b61050400a00208149440d4440021528101d605000d00d07641d40744940683c2c80b804107002c42c181c00801010800d089603c2040c1d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 397866726 1250 397865476 397865513
    0x90b01170f030f0d110702060d0c0e031207110307050d141b0105030402010e0a090204030503310b0d020403141615090b0c070906060503190c05070b090c0a090e01050a0209010c 77
    0x145403032851f030b0010b0340c1548400410341800c2d0f500c2404143c620b5000d9403c4210b041c007a001004c08000c4035500c000035008041e401032030310140100c4031216403003d0103101e0003000060b081c1660300140e807400039031031303201842038040c2c03485800d20040c04011180200800780e801a16120310b1900c0d60303001141d420ac0000c01c0d254114803070700000580c0403030a100400045000783d01454850000408410f6002d002544862135024407030032162510f20200c0b0518201d44020001035610055080000040e0066901c0644141f4690101d070b5240c8a02240aa8800e260043d050001c50b8030b80b45280c407440300c030301c14820005850383c00502c055450345006003c041200002c80c1c51042d0b890b1580310680c0c0c215044100040c0000c01481560b0709224042d13807603200070041c18048844a1003000700303540917400b409007402c1032301c2c1d012541418051141c07100c817030030144c00d00044c180c842c034400c0701030b00c44d00c001c0d1a030300d43c681000240a001607109503040504141d485601500640d1110841c44232030b40100b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 397867976 1250 397866726 397866761
    0xf01090f0902030f16050901080c060307020f0102130302120d020d0e04090f0507030213050f0714130f050a060206010b040605090a080601090911060a0c15090b01170f030f0d 76
    0x1c10269400700302149940840740000c1c41010759100745c0004c01003844d400b040c050450000180011040403454072008101074032810b450740c0e18103100b01d141140e00c490350308465200041030103910501c0850b10081d02d0080c0d41416807e080c150361030f5902c0c4000c03498000181c00c4008200f406602c200250620184000c2c408164030140d62500030000e04110011520b0750700c81c020410440c20301e0061000700c1010b11a0412040c44d0038145071403070b002c00600810403c580c41c42c0100b06481090300786d07161402c140301240b00b816103410701050240d000340202032080c000a1000100320b03200040309030586072901c0300242071a1411800381c031039401942070103070f00140b08403020481241c1001030300e0080158080100d0801140d04060700c0203900c0409441c024001040341c540b40541220762140c074940c2c01000d03800b540c3d5040d4810001405003090080c41000c45000000c0e00c2d2410280d01e280c091b00d000c052303c5201100085079603403446108213600c42d514083c050401c01c0f06440c3d0004841e4004503008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 397869226 1250 397867976 397867991
    0x121302100332010e01060203040608010312031103040b07020613030e0f010c0b1303030609020306180a061a0c1009260d020d02180609060706090f050d020307060c080f01090f 76
    0x100607032240c00d078449101d1050703042d0042080c2c3d0310500c00c00c5e00601e601d00255140c41d04007203000340540014040903200101d009a10350610b48030703a01c002d500da80c501c86161b8481c1041e18000c6803000050790b280c4014490303a00465000e91000180c0785500d9407607110390380305255207c1405024404d038100075041c085451031100115103001c40d4907109414005004c1d19035001460040d0440d0401c0c0c1112a05034814002c00040c3d88803034817046030034103000190300d0003591184000300152516400008942010094641141800303001070144686480c0554480d10144800341d41142c8038804064070000380c4940e0003007100d21070114400c00344c0110035120f24001128118000380ea2001c292059850340c0081c1641340384000e1001e06507025011109d10b854490302800040e400e00950001401c81551040f14400f0000c280030f0040e0780f107921106039103000d10400b10203034403500142803d0307850a0a00c0780703840030a88945085403041600c070001c0c0080d6402c200401d40103210680f8a01009950f07a0360 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 397870476 1250 397869226 397869281
    0x100309170c070e0a09020303031305071d01050607020d120e150307020c0d03020a051608010e07080619061a03010305120a0503070305060102150a0222050d080f040f03081213021003 79
    0x450ac201070590694144000a140203890200b1130b501600b40d00c0307821a150020b10321558000750441d076007100c61a03100c064500020f00e4082e50f12000070400c06404031a0844035421030741d0a80c42a1003210182d00400e0340301e80d0b440c001d110032500c080051300708101400300781c038040304482c04d054068812907043c1c07110f9a0b62076181660515551502c9858030500f040b40705000d0140b01074000e04030000e40186c2d0316140940740d40b04000307014002c10752100500c00000c018a540084010320440c100022444800d40703881c00c0c0e0380d00a010030340301401340c80d511900182000c012a0302ca5619540ca562866441c804110010407001d01502d0450103074414044105083d5280140100240c001c0182d840b910520082c0c281c68032880c585880f180c409204020350384d01e0200c40c0703905a4010b01000d542c0d80000841c0340e418031070380e08202c00744100d4101c0032081c090004042c202c140c0e030a0380701020742d0300c803480c0481d2500300f40b0300000d600c140c44001c940351a91080c1c102045c0d03200c0c0c08880502204c0044e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 397871726 1250 397870476 397870483
    0x402010f11061e06030c1f210614010801031707021503090c030c0301151802040803040f06120b1309060b03010c05210103080d0218100309170c070e0a090203 69
    0x25500c2807565000791243c1c8441d001000d0a5410600c11030040441c0740340800882c1406100c0305815031500c02c8500100d601031b004011118400e0030f2018902819140c2e108510010001c42c0140c00c12441d60320001c0031079500442003070341600e0b0050350109944010649003074071680940e10880c2c002c00004e44445054040c080a140a41d4500018040356000c1c48107040ca800044051144260306001419082c45c18618a80e000c0d01c220030141c0c0d26102d84002c0e400c000e4071a0f54421003003403000203000110900d00c420b00312b0660b801030303903804040341010b44030780240e46e0702172101d6900400d106507440c01d100c85a4000002c551180300007040e10700c40c40300003070700310380315910341c080070540004040b2110303414200c980e0b8004071482802c0c403065066850310a854007034038a00446a40d40002c2c021450000270701301d8441e04100a1429074045036841004016011008040fa0011554640200c0782c14500c2d060700c20103c461030052100c685020007a2401c00c401420754450a65034410f0074015840a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 397872976 1250 397871726 397871731
    0x604030809131a01050304300f08010b040506090f03190b0f0906190b060a09140103050412030f02091215130b04031d031f060902070b0402010f1106 65
    0xa50455803200208002c1c01098680c046082d10800e10300300c4103650f00410441c84441d005005e10300700f512030b500d41c80c2000807251218842c0200d4510941d404601129041c2e1321640c4003c10382d80c0c9060f5560841c020780301c9007400e010319030303901d03500307003c10300082c140030018045100c1c00501c44504d1141200109080004010401c40740c0c071080d45520b0203018401031032503009806581d00341640d207020384519403101400b40049012401e000ca0b040040c05064200d4442c0f01c4c002400310b5940c80f0710000c0036202135038522400d150030b898868070010b250700034414244680d8001041da0342007100d000c0220003c02000e400c000c04640d090040b4107003601d4506246100301d80140040000c29002c071680805400002c200d5090300004995543c001841e000081d42c1056050503c1e5080322451000c4410914610b070145405205083c00c1050f03030302808054054245064000300300c92500e031090b10301644030740100074080300c800d9000300f80103508c11840400c0341c0113a4500144101280e412050500360103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 397874226 1250 397872976 397872983
    0xc090402011229010c050a14030d061d01090507090506030c0f0d090c050d17030403201b120a080d0b0a060e040c110607031d011d0f06040b0f04080702060403 69
    0x480402da022025103d181c000488002d00300400100c081d507959980d15604100001d1116501c05a8503075100c00410541da40030114035420b0000c151148020416202844012603c10203190000583c015030b61041c03601640c1c65076076842100341844140321050b40041e11181e5203500820026482054030805460a03d14805004c11012081e080c1100d15000e1a041503108a5600792408005102d0014495100c0d02141100303440742d41d01e040035a082c1942d90001c1c1100030002d821004500800b203803c180b446c80702010308426154040174000344020001901007268440080c00380451a4000a04400101002c0115010960601080a00b0b081383d1091000c1041a1141107030340c0340c18042c1c031901c100c0900d4045e1072160307040e0035141d41c2c02e00070300302d00149540c400113090a24460070002800b0b03141c110007404801744e200c007402074440c616000858503018054412402d007902141d154012a00592258196201c6082c48580d09101410407030715600200580c200584441c00508002d502 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 397875476 1250 397874226 397874261
    0x2011d0a080c09010815130609060c030e010501080105070e0103050901180b04050d0c0804090c02120f07050f0d020703290a060521070918050a080720030c0904020112 73
    0x4824040c011403e8044c2c0140c0015040346140010000300e407050b45611060810811125124034200300c40104110003001d040d107404c00040807202c075003503000b01d00d01c0400e08008004a13a83c0381051400c803601918904001010404d1031a070640c402d40090360071404801c000641011a03090141100540c01030480709400d0080400003805018002c440c102506801c202c0321a540c4c03035452140911070350241c1034050743e542d10072100141c030030404100c01d001e0020b0120f6446030005074414098000d000220340303500c5481d00413a9030000104045114111680080411303901f544d903600c1c4003005503c0860308081254600c0740b270894407016542d000302044c540c001070460034041400800560003010b96482003604601c0010420002154011510300750b80c001003184a404040a0701b0000380000f034494410314424900f03215440c8000c0c80b070302d803040c907600c035240c03c011b080203070849e407001c1c07a103507058021100004003800d084407100d900500c1490a201101440c5000c00d089036031080e01d440235900d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 397876726 1250 397875476 397875493
    0x60f0403080906150d0602090406080f10020f03010b0912010c05091507050703110409080d0c09050d1e1e0b01050f01031a0409060605090108060a050105040e060402011d0a08 76
    0x64000c4801508041080c2c003034215442d00520500003610050940360042c1c4440d214003003440b010368160703164140010410302c0f44aa4940140c2c0d03580040e029210558050900d244007140010310866181e5200704002c0350650380b82c1820115550414412142c00c6000781b40d8881d0107040130302c0ba03800c038003405840c0c0380d807100f0300202071044d000301400c1c202100100410641c404030710001140000c40c2e40c400358a00180404401103000380465482c024000b6001207411000d44c1c119402500842c13103a907848508203580c0c1d100b0480c2c5100c01742405482c4e40b000702595101c0488141d41c1003822030040c0c12180030655051000701390f075140410203440507130f07600c00148803501e418120024400340911b41401182c2c1c4140140d49504410030000d445640d8800c10b0004010164011000038400280400364540e5030b40d042070344546048a54900452030000042507a2411784907144c2c0c1903459000522280d078036030340150344003889083e02d03028158886e008045c10b90b440c14100001b0300ac05001034075405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 397877976 1250 397876726 397876733
    0xc01020a0f02060712051c09031b020301060b040b0403060b01020a031d010e0d11041a0f120712030807030c031107110f030706030c080c0405010c03081b0d05061315090e0f060f04 78
    0x20300701c071f030007500d0300030f080c500c2d004086503100305460784000003446c00301561642e510019005002e11340c0030641c4c0150104001a602142c071003e0070889000700d04c180003c41143c00120307100c03182c800005000c10703441d215444000c2101403c0c0085024181440402c0c1035640c000121003044915049682032403420b81c441d01c80c28039010f00039440e60700d007200740c2040e41b800000071580301003203800c14015800b0310684440361008020100080490200c040e91400c098100201140e10803102840800e00700504044228803030302c0f445030480700151096050030f5046e03440c00d1180c2c0ca0000103e0f440072090081e0840d558003071145100030030a5450004440a502c440584000401007192001d84014482003006036000306280c1d20381c503418a09890075503030b4004c0c0c2941c401ea401041c10000c5c1d40125690b4004040340d88924000d8804903071030751407000818409000d032008501f0050403a0707201c8108000c0348120307421036aa10702590082da2103103105000000d180040840e4170102a0380640113101c1070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 397879226 1250 397877976 397878007
    0xb0712180804031406040320030d14070f0c02030a031101021902010203150901030c090e030c010903020c130e120c0709020310050a0512060106050313050f0706020f0c01020a0f0206071205 82
    0x502c21340c043e054500d010340700981201c995507914410250840000c0e940e4007414000c651081324940c5040080845507d501401c2c10000c544500203c0c007a6000c80080b04d018142c01820b29500500800e83d81049a600321001e07944040c403030a45640130300c00d581c60b49104010b18046403056600040e16460f0010408a0508124070385501480711540140b001c0740641d10203400355440c0c000302044c0e0250038170031985544222140580750b07510b0f01860f0400c056001c698a02005000ca034a14081520300c2800020ae51308240810615408003801c180007403004800b40060401000c144d94a00d551011042c0030390740308542d10840b0710a565420b00c01480c0031003e6a0160105550600e45144800001907a41c501070040e2001d1001c0440020a48000350403c030b041981c1c400140d8415413000840b0307d07960003843c01190050700804012a070081c900107000c000d6001c05a004202c202d146071181c03d10003206d600c050303801000c00c115804c04aa81590000d04000c80ca90328540c0d20122005402103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 397880476 1250 397879226 397879253
    0x309060c0201050403110d20030607080f060d0213090308011505190c0623060405090118020d0f05010608030d0608010902090402090a060513020903070806040b071218080403 76
    0x1030081036111400980d03480000c0c0c0b400e82ea4800b101d1052100c003040050b020341d001d1700b4002c11030300d00e000c403900760b8540e241c0a903201c10100743d0481e09152075100742038884080c03c0300c3d084001c820010014905291000d6808800ca0003d040b0250b00e205401000041d501e1054059011900041c010880c2c0c00b450981c44001a645291181c1400100d013400c860040301507150000f0009031041c050203000721903001d400b003020881800794071042c0c11041612200c608803503183c4114601000a48180da043c000c2d07481100c202e4144542254142d401c111040009280c103031864100c00b019240020340900c1a540580aa403008540f50185010500d040e0354541d00b080b80640d04003481c0c00d0051310b40f0400543c0240c0e048540608a640e507008a20083c40d40d80e11541d8040c240d080302c805c041c2465402800d44407002c0c0d09a480303251725a150969100380560f00100181080000240d90603c83d43c0003401e034401e81c40020880300e40e030104201000340500030507600182c1c0020108100b1000e00844803 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 397881726 1250 397880476 397880489
    0x1611090705030106050a050408010903090305161a0a030e0a03170c1903050c09090406050105011b08090108060307030507030b0a290613050a09092d0305090a050d03020a0309 76
    0xa06140c08840189a4001880307800240300d000f103000d1041c40d0250b015a0050101c1c035000300005655424014042c03480c0e4442960035010300f010792064001040c00703110a4038400030400b04044581c0003001e200d680001410002c06550f44201c2d100714400f03228040855010703641c0c0410f4421031710720000240401030803800300044100130701c2c500b4101c514400010300245090008a541c1c0ea420382021512411004a42c003074040810030003000300c25884903040c1d440030399440c6130b07845461070140039030030100e43c01034180141440152150b42c440c00340366038440d5000c2c043c0c9084a540faa2075a14080060b0400c50724900160104010301c0017600c18041c0c0c9a21481c6440112003d16040009914000f20700901540000551002c002d04c0034a106004290141c09040256a0369480304002d0604681c102c461182c4001d410074560350391018800c880442c0161801b400c2c4559809450a43c0840201900040c40d821300180d19070b111914075407000e000e034020f401045144e02d0010041d200036000300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 397882976 1250 397881726 397881739
    0x40618030206011a04030210090e1005030312060f030307050304090b01050306010e10140f072a120620120a0e0a0807050304050301020a09150e150706111611 69
    0x15008260700103002411111500f54020a841c0c21054070040d903c1503420107134100114504070b85180c0e50014801e0f0842d0380a000019182c2c841800d504110079091107201c4d8164410311804450001140c401a00504014041529800c046002c242140c0007000e0039141600046410000e00c1740c14040c080d51802c0901e04140b46140920018069450706000c030303400381402e038000030342150042c00c540030f0b00d2510070307035003030b19214401e001210b035501200040317031041c00c1c0302c201d881e003543d0925180d51100f00d5901d4602109007448802c00144c079541005585445d1152114211541000da511400b980c0410800d59a45421385440c2c409280c0507017021680d03841d180750f20b0b00d82c03080454502541030f401000c0f5a91106c4508119166001d1034128542c99440000c02000c099004920340c000c951104240c1500350030740307030015034000e802c513400c00d90020401d410701155001d084005080703d5205600002e2003440402c002c1e56039802c8200700044ac028580751020134400c00d007250213900e94084801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 397884226 1250 397882976 397883021
    0x60f0402060409050a0b09090a0201140a0f1206030c06030b0f0a05060a0c020d02090c031e01050d020f01031b030209130501230111060406050a0c11150703060e0f0406 73
    0x109101d4859481072954540d580d002158902c1010b40000c200d0800081000c100ba00301000801c2c1c581c3c8040034200d005c900d1540504403281c0d0017100761013284406032940415888203180c282c50900041407008141039035420b020000a5042e500200502a50380c0c1c0098440795a40078400020700c504103072841070f01780980c2004142d40f07038011500f8008403407822021301c00c0703640b0100e120030405542c002e6110086608100d01e8801c094041c5101d01c401d00440340c160b8100c0ca0100703c10b40820b008403a04115a519600c0143c18546c5000c00e40304010714000904442c1e00740c800486103020407400001a4000580d010589040480d052524000c44800c00140d403510300c000c180101c86529082c44041214100c0d40141c7c01041210f41c160116070a40d41c051900c0d14240340201412244048614038040d096400184a02c2c0d0302c40d10451b5a200a08031310802094042640000401c80c1d01011384070b01010171009030b6814a070b80076992551808040b03042c18030f440c070b041e02c014101030381d40e00b80ca1155 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 397885476 1250 397884226 397884229
    0x712200c0a320402120112021c0b07050304020d1a01050316060c1712040b0a06060c030e09041b080a0204050109020906180f0d0b04301107150908060f0402 68
    0x410b0064925150300760100c0007034030001c1000b0380036141c10004012045030000035080115950002010301c00c540c1030a00e094030f801100b10100320040d01911400f0b0311400508100d0081c0000d40d001400206484600440d96981c00e5010004000100140751400010009800c040022881c2000d0450040280c50705005008080f2490424050540e01c081c04103c031084034071404070384101c122039242c0242c501d4203050960354001d068485070311300b610b0504000b42e0684124100304101d54150703200c0202a024000b0404440f40140068881003500c6603240714030001e66114500801d0400302900c0000398a00402c4200d40050380b003454658010007d25100c0c0e502c440480303c40710b620074401c1540003020300109020210b00c5400c141c0060003014031034244540788101d6032003644100c0d00c1101c101c0d0b04e2240c1c607546403064501d4104208240c076203000c5d0070b4080c02c1480f151169060884101550390324600e0410040050488007280900d40305005a1720180b010039444008904140703100d0400382d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 397886726 1250 397885476 397885529
    0x114060a062a080705030a09090204150f121b03140105030a1511070f020f10122a0908150610030b040906050c0a090603050c0712200c0a 60
    0xc0760140d0401d0341803002000740580481403880150043c2c0305a0725800c4a01d412a5603511041050020841c664000501003001d4021101941e150001c0b484600d60120f0045d034001001c2030343e40c0203100403810340e01d1407034003188140b130241c0c03d10207c0c1d00800d03107810b0b4000d803c440920750042004041100140042c0d00c0015080d545e2035881101c259407403404503d44c00080c00d1852010080581c0010600706001c1d800540300e00440c02140d03141c09141c40c06003003103c4d8401e000d40c1d001c04201c00c0c80d0721800032017282d40101800e524144962448200d00052a030180c0d414445034000f05500f41c8050000e480d040003228641e4070300d54801d5403903040c404002005161303441d851204042c0c0302e0140c0d40040c3c5690304400c8407282e0000341800b02d400c0c0500c201e191608050340e55000144640c80008115109015881c00390f584441540d10f070903401e0311022140c0b00c41030b00d12002e001ea84a114281c0d500382c0e01c00041d049007940050400c400240017080603904a90340582801004150301c55420402003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 397887976 1250 397886726 397886747
    0x40e0601050c071a0304030e18010303110703020405090a0b2d25020109030e010216170a080a1d0d1208060a1d0118060f0b0c1002030103050114060a06 66
    0x9080a580b02c0ca51440e009107003280c0c07a0040400c41660440c400700039074a1801640c02540310f51200da41c0c92107007600b40121004e0710038560707c42104201c010030109000f640d1540b090319400e000d403008281c0300d40104050f15826244c0130007680c02541c0c1c0000340922100011b82000b6000e004c1d03e8020003024018003021005681880304800b405c000c1480002141810300448030b0380d00c40c17200c038001800c84c0a40206032030711081e004180c210300504940c3d8408100b505506001d0014143e01a080026008000138500c804000500c1010104400301e0b424001405001103190344202c280b83c60f040403520201c1621300d400307001d56000700d011000180c83d2040b034808102585840625503880c4030004e200d110f1168000e29800010800c1706c1c14410802442a0690301342c5071540c41081104807502c400c41e01d0b42d10445c000c2007582c030824068180024020158070041e20300701d1721507402c020050000c90b402a40101c407180e644a002605800200a0056018504545c610010307031070b04c28080d0101320070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 397889226 1250 397887976 397887979
    0x1418010902181e070e030d08010b0706090813030b0a0c030902182511060603210a0e040203010e04050c01020c031902061209031c270303180506160302040e06 69
    0x1c550000d0307203a98440040415190003e10780600c02d0400b9800a000190306a06060180c00f4145031480054000c541f018122607100d0301e0382d8501801c60b04c5480c0100b99008045800300c0b000c0150f484a0840c0c0c07040c040c0514028401c4100c02d0400f40c1e41c0b02e040b02d01e5210034205041c10b169514025998200b1030262900840b2990441d03031383c0d20090f00201c0c4682c0f00701580c4020002c070002551b285d001c00c142148081480465601e600c50f601007680e181102c200343c11201e00c400ca0304d10160180c9402411103e01681041001c00100c42c0001d0300340c0e0826040324081584c41001c1000b801810030284014030030038009012542e104102117910340000c6510305040740006e603580011500c0c1c0f0000c41e80c00080d41041c1000c0b81c246094291f03161303801900d8240003000d02c00a01e45400e003a501c50b20403c5414000c542400c02c60000d01008116140c0b0301c1038050659501200340301c5039056070600d00c400d00c20f10180c1072a142028000103c294004114402c0500c140b1050010f4002e01c000240c00120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 397890476 1250 397889226 397889269
    0x1103040f0f050a030201020901030b12190317010b0d1118060c07091121011d100306090c0f0621021b03120108060a052403010b041418010902 62
    0x102400c00c050800c54610740200684120a8514145541907006c0c0401032000d0340c0610001c0a04010884403603e07000b49603520b40c000381200101c2c1c4014040c449007551107801e05400f503234840010111015001da1041c40913480014840001c01410720800010704074074903020341030500311209144090550071415009050020300549422410000e0000401c25100309004200001c51814216045400d00d4140d160130303a03055441c1c041551366024107844101ca84c501e09210360101660704010081e000055410f00d4540100120300c0314062801561702a02f92185500c0c078010b0181c40c6a880d640c80001000b0154140501d44404003402100c81000d800001d40c60b40c2d902040c0c514144510241d5183c0c42c400007402c0065200100700d0513040f101407009844080d41d4282e100c0007543c108884c0d0040580d2a40c100e2070001852000300781c1c0003600035000188206030007011600700c422030340c1c604d140407460a003000b54200d00b11380700711681c4211100a00100341c0381e9010440015840710980716654 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 397891726 1250 397890476 397890503
    0x14090a2a0c0501050c1c0f06090c0504090b0a0b0304120e0d0803040b101a0d0f020301080f010506100e041d030307030e0c180606160506010608040605130b070c0c1707050a09110304 79
    0x4401d8000740c0141278444001c000183ca40312002c0d01944c028403c445080782460700c41d41580c07034003100000840300c05640040c59075440f40c1c3c0701044882180341c60414040351704000019030300d88101190120307100721056a502e08050800350481c10000305017080040e40c1c604103001c503d11407808100081d114101c05500c030b8800744201c001510b038096481894a2010000113002c817030008400a0752407285008004603140c0a083c0a1503040c0b000ca004089a201c3c6640d0305a400c0c02d03031007610300c1094402042451160510940c3c1075500954a000001341c4038501016500f2040c00701004007402294a403802141520003502800c80061480303100782004203101c503d500c000115040c401d0380c42020784059603184c2c000581803903010344056030b14a1900e00001c40700951003012050546d080164402a0343e0740381821149000d802c0022900e03049240d40000b103886041c1c0c0c02c00b44500703282c006820010f0070b180a010f04100b490b8402c01c2040d05102c14464500311020481e6000b0360030500030708550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 397892976 1250 397891726 397891751
    0x1009030e1504091802090a0605090135010b030708070509010303051608070506010338090a020402070c080d08070e040906020c03030f04060614090a2a0c0501050c1c 72
    0x1406a50710825800c4c1c184410209200d4107220301d8005a4801c90307406405844045040c012524280621604036000c100184040c009014500c00403011100740c2d0341455521b840c0150941041c0408400039039180c01890400d440c052201e0780141c02000c00410303580c0d02d003000141030381c1c40611010341071050010fa1440149000c1c8071903140180c1103d4095540c0c0503d180065071b549091000383c2d0f02e00c8910b001ca08407200011211030340d240030b4003040703541044d03000b80c0627152620160251544d44944e1058100586413400680300440c0203150b400781080c030702070303820b41020f03a03040e034a03010480140c0070007004507001420300c2d519040640b8002400d002c4d80c27902380c000b4814900c2c1c00845100100400c10840110340100303102d04d1245400b071141d103a856001c0c1c07280341080c100e10790344105180d0000d800090994000c407144c10070b1105580c41020300011030405c5030000d1402d84001f52003041d0304070901c0024003070590003820800300685031417070340c5c424203060700740c1c0b004140440ca40310b03007500000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 397894226 1250 397892976 397893019
    0x131a071a060a030b0103293d08060a0e060f04060b010c020901090203060307080706350106090608152809110403031214060d06020f040909051009030e 66
    0x3c1e550015a001d602d585034100070b0f02e0900880e050490611118490410050096030918058101c203a1460005c0074601980316480300a00340000d0407200e4030420311030361f184515201c0c00a050040103070000381400941d2100751b03005404122641d50003074040c840003618090900c0d078401d07000742d00040c1c000b00e19001200e00c02d80d5024040d50050080c4004246180654015070103941e0440440c1d41e52581c0c0c800c03c949689051007044041810003032110320714805080700c03100740000700c08032390040c02c4842c43c7e543ca0740390280c001100180d403403031060003540c0c5c005400030f402c0400140e00703010138043c003130004654000e8000000d903040d803c034600c00030b080c28002621016080c82c103c02d000080e4040300c0380403030343c010380b00c2900003c41c1081c14516810845c8145401070345c050300e4441180d038401041c0072001c0d10000048400603420846240f8421007e8003138805050940c00c0450315541a060882c5001c136016222250145440c1903000003d82003082c44090100a807001c0c40c001201c8042070b400d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 397895476 1250 397894226 397894229
    0xb01021c0c080c010f050c0a021c050f0f070f0c050a090920030f0a03020105150103090804050910122003030c0c09060103150e18061b130b131a071a060a 67
    0x11707598185030074044101c01c201d0140204074610b5085505124103940f140d0040f8a040c0600360111b0000c2107155003206120001340b20342a8079103002860804295240c1c04001d003c8807081e0750000c2c54542c248441e1a110503020020881140c1c03c0c03000c064191903202c41c1803101001119000c00c40a0169842e0f07d05000f0410800001c805445030b82c0040e08004c2e01801080704c0d080010300030b10b0b80788011903029119100d003031508215540e04042c141310501c05503010191244141ca40c41300c4000039494021000540c0940c820b4400c009070600510f540e1495061820320240320317800c14440d402c1c90070310004101c2180c200842d030400c1075441c4d00340140c005141c2c03454104d0390074401070004a03000e8408484140070b40c2c010301001b90381560100c2400c1d2510000c0d1420b01c9110458258ac404100b6590003070824481c2c4a0418410140e0f2040040d0380c580c030070010381203000b265030010092858882d8410004030030181603a45003103250342d00d0032980442450180001c03030241c80801c50540320b1214800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 397896726 1250 397895476 397895501
    0x90506100905010e21011d1504140307050303040303020a0f0504080307020d06020d020703170c0c07030f020103110c0d0f0f0504061808030406080901050a0b0607080a030f020d0b01021c0c080c01 85
    0x2071030341e2100f02a09010b00001f091001107031228162440b540ca00020305412142180d100100c0c05031204d030744154060712024058025032000740440004948240015030040b840b0ba140141d80f03410404001d0801001a046070081c40010700c810401080c0100807600e80356030440d441c01141060b4500300009003e440000c10420b4408244641050307081180c40b682c0000001d2a8441c0f5540d004040d00766100e80380c800312464008200030800100c400f140030420031b01c1414041441e0030708a5a0610710b4004000c1ca4405901164144d004690440c00d81550301c0b203a8640104100341041e40075009218611030502041805100c400c0321048001e5680c0c080c0c01e0201c15a030740c450741c80c03d000b032049034213a0b4031340300d99460080820080b0145219108441f0002b03840b01e803c0c0211901c6005040d00028440c6042c55100e0b5009545074805100900351170103004000100303409600002440c02d06000300108050708090751001c8000e400c030000a01095216400e6655195054802405865140700d44c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 397897976 1250 397896726 397896769
    0x12020607020d0f1d01020a0c180b09062b020405040c182a140a030c081807090903180611010608030306060904020714060403091a07030c120903050f07090506100905010e 74
    0x101d127585e0096030500e803009480005011f4005400308103c0c0511064400590011440d03d0713605c0300424010281590044000d9641000b002031b4004c1800d5480c11202111060740d500b42c14051044000c281009519801800b045040c00c60680c503a2002d1040682e03007e01a010030420550b00d104008594600001d020303c580c6880d010000a00507100b40701c424000701e0044000038001c581c07841c80701c0e1020f0740100000c0000504d480d06074001414400415410044490380d5940310740c4081da0001c0091100760b4994495041c910350381421103801d83c0020300b46402c10000c0c8005070340c0300802d860a001c0f0440e00169600d50303615000c21006415081c0245502601081005140e04014448121401006001c0e0076444010001001d80b06919004000c11080000c107800306002c092140600d40103410b01302d002d1602c0e0344079241b0741110b07017a82d10b03940d60048205115408941c003400d0f4100708107030b0348842d8007805240007a125003034030b010712810082d1100c0340a09640e42c11124006424103482c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 397899226 1250 397897976 397897979
    0x24030c0d0b010503010509160320120c19060c020603180d0c2904061509090501022106091f150203070605010f1d0903040312020607020d0f1d01020a0c 66
    0x4a03003034a90903c6803501c43e510305400190030100c085542800500801303400841c072420741d40d60001200d00b80203071040d80c1892981c01c40d0035803562605810000c03603800040c01c030340840008102c0300f046000240790310307410b440404000c03140d04401940460740e0704a0721035840703540d450002549141d41018501e842d1180500d51840c2d20b030040380c61001e640c0660700c01d60502410045801d0707d0400340d0400c0303238203c9025001a001c02c1c1c0c0b507440014203403115804902401d5407059000e0a0700c0f40540c3c1600c103658009540035054400c11400d07c0b0300141b4015815551034500002061400001c1840100315910380040c009866401c02d42800387c014565031000400ca9488000c2d41c03500440021619a0300c0c18001080d0701803101d1080c4111101002a4500360b849188038044850010700017001034031003480080002980202d9200c0101c4242d4010001c038540340304024609011100028148490198100a100d2380131344500b24000080340249000c041c4400101d01d4042c100801404480002e0340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397900476 1250 397899226 397899233
    0x140d06020f31050405150d020a030b010b0a0806091608150306100611011b110703080d0b24070305371205091c020a0803011409090624030c0d 62
    0x8881c008000507400342d034291180e003400100c4005464443c1c0440790031107002c00600e08106100c80da1b038400391a54140b03039500da40e1915851800e801205814001103901d01c400c1c1e5000d0b0313059500c5941200c548069081040c0d030303180c258441c200014200310840000800c03a0304944030510301c1c0c80c0084d00704d0702e07a071505404034a0604100c0c05010009200c000e140604040305005128080c0c44090000069501540058404441007105100d6a004248002010480d80310140400d6100d545012400f0047ca07010421000d80d04883d444c401800c080303909016140140984048035030504141e071b5140c2400c008910b214400480001032040312199484e00003c198504a52036102ca0b103501038031180160303610701510b8003160003c01592044031036a010511221070301c0c01440b00c40c015980341c52001c1e02d998403103a00136040402c0010648058038094101680000e500c0191440a0f09083c103028500b0030b030004040c1113841c013080c050050003400703075407e0040011900300203080c0f550420851a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397901726 1250 397900476 397900537
    0x40b19030c0e09010e0601270518011d07030807080f030a0b091b090607060b0a032f2206050612010302040c0203090a090509010b040c0507020901140d06020f 69
    0x30244290b034880d000c07482c0d4840502031405003207840c10207483c240c1e09011604808030107122817804660004a06516800c0c01e0380329040c0103200c010031074400c4151030b40c3c020f404c3d04d03d40c80130a8071719411041d110121020101c3c602c000e40741d0104100e6958926824450510f003e446200d4001900000520181c07400030b40c49080030200990b0004071907030f40d01d109100d02e510024845414180b041108007218038203503008205141c0300d4a0001946030601c8045605055030b504116000c150000b08160441c1e01c0460854558104103007020011003030301301084081070987c01000000701113120134941d08015400c80e1010701006044030f603c03840c1917030a2002612084c8001e078080c6181c1044e00d501e144c400701c210355070300c8009404590740350720300a01c01e0010200141600384655a0301d0142c4a20f80d41c134003d501d070007030307040e50f80d6601c0345664010400b01100c10ba02810500b40701200041907500d850451a03080c5800420045c5c440344010600f030a0380c400c40200100703011140c1403590000d038411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397902976 1250 397901726 397901729
    0xa031a0406090f0e0c150310091e05240409050a0b070e182203020c1c05061305190c09090c080f0f0307140c0a090506101d040b19030c 59
    0x2c890502c2080101101103441d03440451103946c200240f081d00e100c40703580e128010340d0004100110010720302d0740d03083c491086032079907007401400345020341c001aaa4001ea016984c0c025170825454034024900c07440390341701a1003100b41180a90380324201d80b018007100303011042d89590000c0a012240c50030500007801c1e440e851601c24070550034940520300000c482000540b08003005e40c1e146200c1d4014404208241c0d014590450462041c034440301032948690540030001c0f074035000ea0b502e80b5589403614900300b02e8010070814405689080342d5022580004442c2d06400701080a089100420304000595803160b8010011721030400840301d0420245c0d071082c0d0304460440061f24076a207070601c5825210081c07201e540c41154004c1c031069010078a840348a0741c2d660100002c039840000e0480c041410342c48a54007405c0c5903036603802080220708004610180301341071840c085002c501040003000d903c01c074541183d8002c60b40d841111341d554841d8095040024004c0d9144d825440e0344e03140c0310a500005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397904226 1250 397902976 397903001
    0x70602030a140f030711030f270d030e01030c0201060e10030c06050f0d18120903060b0a0803120a0207080711030c1203070f0821040c080604080a031a040609 69
    0x8096450b00b40101650644040440c04880c591450f2905c41049542128640c800c42d041d00041000c03c8840c5c080d18010041242003c0c00400800c1c034214030819065a00201c5038001c010f50034100300000e03032080c87c0a1000100742400a03221074842d500b00d00611041d00080d0742c00502405105030b03003214181d188100ca01c146182040c00c0d8035510122100d00410101442c03409050041035082003003a0000103400d000e00107114052002501d4660100302ca0318070704400320b0b004240a0081c032010b40030f299178051081c0c4004145501e000301d115668816a81491883c0d800c180100d82d08952507012145916000962640c44030024140003071000c403d241d40d44c7c4644030750403041d141c0f400c04500c1d07035140072180e101440c20511503882d40040c0010840b02115102003c2025a40707020b00c03240c0085603501c1440f49001c03107140038940092814100c5c1c00045560b4450810000002c12540c2181c0d6003000c546008621005944803565101d81d4440000c0e52140c00c004012031424003030340c0a03039481c20f034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397905476 1250 397904226 397904237
    0xd05190e070807090213031410140405060108060702030d09020f0607030206010f0e041205030703061e0905090a230a2001020118080405060702010c050706090312110606090414070602030a 82
    0x10ba840085049105541840b44401b521110403c041645040e00100c1d43c4082415031700c40c0300d4041c0f0740a04035440700d110000c41c0d240b00c00a000a001d8204102c41c05080340000801c0c079400c0501020707580b405000c81340b0350529205c454a00c21521010a80c0c0d138130300304c040c140369107a003d1460040e4a48c0d509009002c000c00000b2070000c1d00859280910340500d07006911204152100c96045455a0004141405158540342c0005068144071405d00703490500508001d082400d11400c0e006941e070241410506d680003007892404201401003180050350f442600c0401b0110f0080c10500701031114030003808201044081700c000c40c0c607507076034410b1201090b8020480310b080000b103465040c1810202401000d02440207201c10b003452802010240e0050410508090076075880a14202c5660003d03400544450b904004010100c05108044020750600003c840200342c0007558400000b460709204490b000c0c041400d101050484598045501066580c03041d103c5901a50700c0e4041c030030300c400080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397906726 1250 397905476 397905479
    0x91407020a020d030c03020114010612061e0519080615091e0a0c03090f050f12040e0604020306040209030a211d0f030f0604060c0e0909030d05190e070807 68
    0x148041401e20010360b0052455142d003100341c13411110040c107588110190740d642d1015003542d69005c02c1c0c0a0081a4036502d1910b00c107102c03400b4100b0740c0c02aa02803c032090302050612419981154900c05442061ba2a2101c07886564170200c0400c00c0390b071180d8020700447d0f05128001d40c512107901c24a480c1540e03010045c0d203030403140c103c1c00d282c80610340c43d4080c021300104014541c0c60b0810b102c2c81d505840c010800103400d4513100c00080e900c3c101140c540d40406038650b0304003402d000c00b1821002040249081c680b92524000c4044001017101d840b43c3c1c4e001000581c103517600d50643d4840c80000d07040710004202e510303001c401800701e810981c64031503c8400b242c1e078141c410030104061102110041103034070b11a009125540c41043c15880d8075020f000e40c440203086042014074400d6004070000b141d248030104024141c0d00700c240b0310314001d0740c1c25820064917a100008440c400030811000046ca5503408803441d0f2445192300d0744504203400c28240e822035220000f10760f000ea92210701034401d0359 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397907976 1250 397906726 397906741
    0x1211060f281209170a0215091c0c020310020d090b1803180621010e01080a110904030c14011d01020c0c090a06080303071d1909090206040806010914 65
    0x4100303951450008445030820a51080c103500b1803000ca511410800d0440346071049010159000020750600503841f2004030a842503c0104040c0c00404420142c0480315022048407050260710300d8645c1030007540d00d21002151801c00844052121150046484c1d85044445070003800d40081c0c240c0ea080303c1840499a843c0c032402c0c2610906051400035480c03c28811041a1041c2e51416156071100007401031003110341c1e400000060304160b0b041100c00c0c541c1000720320452500181c03c5080315074842030740e485c0043e491007c42040540110350002103643c641ca001c0341d00c140d05690003071401c0080500ca1203419015040f0300d808c4060140036007074540c01e0341682402c0b40504401e0f001d0590020921030802d0070440749181e00407c40304408600c0588540d0300d40d1640e031003990409d0006400e00e00c2500025138980007100554021186204801d2000c45050101d009a0003440c0800d940c0345e0b811421542e030a422180145800d01c1550825a90340751000c0003009040365150f80c2565480010703034030703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397909226 1250 397907976 397908037
    0x5040b100801051e1201060302190b0304080d1805030301060e1509040c050c2407050315060d0605090108010203100f030803071206050d050a05010e010209010206011211060f 76
    0x680a80c1d94001481c0c1c40d02e0104149040302c2d01c0903080c10b00c0b020714a01d01c00d80351444130740055808200042060743c59403041c04014101d0f11103504446c08111030500031102c0c510226904107400c911096101c880304010a40208051101744030b9013288000404200318000c800383d81200c040d9114a92460340711301c18002550103ea080540507141003040d00d40360302e0550301c8030000b0800c40c58040e0400d0715052a41d031402c5503101c242d0541a400b10300307115852054807003080e80410f0519009045082450350031607014500c060841c0700321004107400c204035659521100050600a007140388550355141218002e41c010341c1c0c150240d504c030440c0450178440d04c59003c0708030f9900c601e103c2e1031580d5544040320a400c070340503011440f644070040041c1569800f40403a5040e80a58081c0ca01e0301c0707691900d182120503102c281a403a9005011100c0580c0c0c020800c541111803d00400c50030750300303510348280201004959a54848400301e00402d101800300064010390300740f40e4040c1d002d40d00c0d00000410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397910476 1250 397909226 397909249
    0x10e011104060909020a031d011b050a020307173901020408100c030204051302030a05090f0a0f0f0501051006031109060307051308030a11062202100e0907030605040b 73
    0x108610368030810000503943d00600120441d858000b44040c1c014140c041c6039400405810a230742c0d102e0440320811004224000d144142d6400d1191030324000600103501c031300a50f02c0241602c1d070700a000200301808a022142c600e0388014451038a0b42044040304007804003040f420f2140c52001040c1f101940b0140f088a0a64544200030048450541c03110400381000015040070150240f000060340d46508100729090f0400c05000358892610070010001c032240200880403d50001025084440001c50420b07259034210703541c01c1000105040c15845060269001401e541c601030800c101e041949034408250380e5103a1f07092084000300c2c906801d00d4043c0c0780910368800c03402c002007019603029400805981d000201c0c81c80d021076a4401050031130304003918900118107001a200b4205605000d0158041c80391144034403078840034285e43c006000f440c0c00c001d019100340c04214100b1802100441c800210090400e1180d01d0041e000030081d0415100d2640031300d040c041541102d1801046900d07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397911726 1250 397910476 397910489
    0x30b030d1106061c2019060e0f0907030f021b0604150603051207050f06040803011e08211b10050a0516120f0f06080607050705060a0c030b030f010e011104 68
    0x20f08a01203a100d400c109174130300a5054500408090402007030302c0d0040c4050045100d42c04d00c04802d40b5103807026040b90a1b01141c40d1082e145001c1c0d4108030380d6800d503159000840c0389000154401003060160082c425600b606500c4110312035100056000003c41e18407642c8110500031031a0b020600f000c040d1042408000e025808c40c8044000f00304410000d0030780c190281d421100708001ca55038071800c1220130389042d145080700200501503815005000016840011001d03131400749405440b940b0f400c0b8040c1c0ea4512402070100d42c8414100c0503007540c0042240c4450321548500c1800c41c5aa5903020304e0b0004e16080c28000000d209640b148101e501ca250074201c4440141c4510004442800030700c03440621031036852018440c1045184148000c0141101c0b002550505006072149484001402401044801c00c07444c80007a4002c1060394000c0c0e0050404611081403070810b90291040c02c0e80b0940501c12410421100b240540040c050202260020018800700070300300502c0c2e120314020803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397912976 1250 397911726 397911769
    0x7060f020a150b0f041b0e1009050424090c0e0105041211030f030c0c0307170d080a0f0e1b0a06170a1506020d08090601030b06060307030b030d110606 66
    0x42c0d61460990b00880030b084001040c01c1042c0d01144009022510550f6001d8000715442d00107071091900030107610f6501c0c3c02119011041400703c603004001d1007180c02103d0280307480d0810312032842c190105050105564020f2160301ca511004520000c242c1c8000d03000000b4041c00c4402c0480d40514115410b070740201e09400100c840300d8444c9a1000004280c95400d4840d0b88010001d0b010240301901e1000c800b4405842c500c69280e041500d03044940c1c000f01303071000e01b0600c04041005c0002d5085190041c43c1004610340c0c2d80c4518440040507113034494680740e0304101c0101100040418900d07480c00f52010410b5041120301e041c40702d031400030300030000490343c404c0318000c41c0d0300f2800903954410312081022a447c15a18094100e10446502580150703014a0000a4482d04103101e10350100e100c2c80100320562450703d0705071f07844002410390390003581c0c00004038030310f180303c1d4201441c4d80d403001c0c0482d106106080d4004001024241402526000c0c00020600918181e10b5840988110b800007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397914226 1250 397912976 397913003
    0x303040c0b07080a0e13020307111002251407090525090909020d06090c0503060705091003020f1303031101061d0a0b031c020703030e06070c030305031003080c07060f020a 75
    0xa69101755504442170b40411000184484880c0368002148640419510300b0040d0149002c0d052500c1c0f0403241c0080028010f00c41c11a02d2810080c240540c1e00765500340f1030f0310028900b17211003040d414980c1010140034040c00840d030b10300d80d50405c070700070380300f40441c078040e00218074030910440d540094200008031000002c0001000b560840d03040280014050104143c0907a42e40c0c003280c5510f04122403540b07034408100158502488181e030b00641d00d040142c501002d54000809086400c15104145503000c03600800003480101514661000c01c0320b208005522403e0141940100408544a543c01c01e1004a0302884a00c848182900305806030141c6865450442d03010f8102c1c01c070030b16010700c11914540d807400e5024941861030720f5590081e00c4014250305004043c1c500c1030030100c1c0115020030010001a107144c07004802c1325014540191603407500304c40c0152180307481d84080c1c5113440104031019541c0d80803d4039003c80f038003922070100f205e820941c01c6c0e031607045030000a418150300c0d451 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397915476 1250 397914226 397914247
    0x60702060609090a120509210105061801120f140d0809010e010b032802180403030b04050c12040521120708010302130f0204030204020307120b0102030415031a030a03020303040c0b0708 81
    0x78100116008110740411905012350175100c5019209003622691a501030121606103111600e41c9841da410700445558100f0030100800508402e008085c0c1c540720ba042c00c00d0000d03503010124851000400c0c0c0b0019520403000030700c000416540c080c3d04d9480d06504900d801300c1403207140c20111024020b00010b5503001c99215040e5100d180d2030000310b0403082400d0050380d0303000c1c07002d10041c410609a480b0b802c007828010100d904030080325000b9071a101c244010f44c5140c805443c038416107000c000c00c465843d407500d103041c2904048120002008a680c074414607403601c01810700c50306c0c0b059118800b640c0c2c00d00b048601c020203103c06500002c804143d1440581a034001c2c1e07080302400e14004d07240076030326404542240c0c42110184005225001c4403601d0090a00031000d035403100744011410a41400259103c00c0d400b800c001003855502c1c034103602e0b16003420882d1450140d00805499403080704d418040c0d101d60017182c00b15025100c100000c920030b203690081c1e8052541044620382400810742 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397916726 1250 397915476 397915487
    0x1b0a1505070f020d150608070609150e04050112140303010b0a1214040606080607020a0803070f02160308120907030f0821090309040b04050f0f04020d05060702060609090a12 76
    0x4a00b502c00310403051a0b10701680300c1c400000b502510400c141e09003807080001c807904039183c50300807800d6508001d108201040d4440e00e44d03400d50381c54070070341c0c81d2303181103d04152514010b0a900f140c0103405d0100004501c1240e084104985d800307140d01c6112403045ca1903003901c900c424002d03503000c16420b200348001c081c03040345002c0c94400c092100081c0003201500702c2d6050710003118101c43c00c44d110750b41400880360a00540d5000209800100311a441540c0c4425080c00010f00c1e9a0070010249444c01000f4401c00011002043c000354199004c0e440f401d2800950b40640ba08008020035140400c40d1105d0020703a402c11690010b1014005059540d41c4203810f61105001003240d0213061004605044505880d60182e041d01000319a1180c0303440a120585011030302092207a89000c0412400200800000d603025081c0303a802d221940c2c403031000a03c0000c41e06070150140c03003180308029080382c0004100e40119011100615155107890089a4034000090028807181d25259444400d50140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397917976 1250 397916726 397916737
    0x1080c0f070b09061f0348140103050f0103061e021603020c09131b05091e0108030a09030609020612070f0305060906030a0b070e0d0f1a011a0702010c0b091b0a1505 72
    0x40d035400880c003c1c5011811a111801111b0700c01fa040743c5d00013040282440411100907090a00302400540781034501420783c103e05100150840f81c40b1100181c010481c00314095114203008003c42d110190b0010f103d01c0d070001410101d000d0300c15958100c150345007910080d031244561640c84240400316a50314001c0f0100010714030710f400e0006801050650380e40c00220304c1910010800c5210382c000501414160106900c240943d4200300191080c1c168400e14005c10b594000b80081403e189900c0411344034425413200c4c66440d01450141300d100c60b03025544005d0b03924141d50034000c40d00c0360f10400a940c0e105682d016030591010300080d0010705c0009400b031340b000c501d007000e5051801080104021185101d41110030880c89000030781044003a280c0750b01c4020801007105010340c141105101e50a1107812501c080b01000300d240800c681c0706808801b1220761050750400c1c0c030304040d0691641c42c8100400429a008020b94500190070080524000c0302d948400d150300c3c4400580003039030180e000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397919226 1250 397917976 397918043
    0x513050a080705070f030503030910110906130819050c030c01050d180206031603060f14010c0c1208031e0601020606040c09080f0d08010603020901080c0f070b09061f03 74
    0x7542400076088003441170000045000e03030003541c1c1c1c2c0d24009030761908242d0070840c81044289000d206042000888050b1443c005007138a0160380d4001c0c9422520250400c0d6020040b24424501c1d510150009882e0b01c4105030310542c110740206d1251001c05032070b03507a036456141c0041c0301803044102c03c0941e0703085500540700f452007206245c00f05402042003075000302c030062407100104161003201d540c54821500107203418508c0010090504c083c20010340440c034401810040509001c00070300c0701811805008000c2010120744030b0046142001d49500110f80c0c507603994000004010160030f10756031191060740142e0103092240c0d10790040200070a07103400c0400400203102400300310014204003d408000310030008207102d5160b04c500400c3c0362416040f2408241c0140140101640c0000a040e040810340c091240c40f0713000d04101d00124059960054602907882050040c0c00c40089162800364007070045078080002c4122008441c0d804900c0b0060180150b001b030b000714100b80e440c0d070500f841076 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397920476 1250 397919226 397919233
    0x212070b07140c10020a0e0904020a0e0c04090603030c0606060c0c1a120411040e0706080a3605010b0103021606050c0f030702060702060601081501030506010e060a080105040513050a080705 83
    0xc3c0703504080d18124510300724000c1658006045107402c1c1d08683c40e84110801103520715803a11781907020441441c0c0920881005040703903c0810420101d040c11744000e8400040c0800a082d568100102500514941a2003681c0340c85804661940b060b4189000c0a800c00028400545004254042c4142c00c0d80410034040c024400c103490311a0181c0564059401007060300040c0d8040c10401c030494601044e8424a0341c41107200700045604503080f86c3e8421410540001d10a0341c0f030030b6150040d0304564200c0d941003013a914407126110110848400075002d40000c008940b0490015000c9114490285560b4107140580b4070014940d5006164020f5142030136031308002c0c090005814503003080e110b442c00346c0c000c08108540b40d581003246a5110741b003481c10310517030704261460300c10484042c1070f4076041503141d0700003800c00d0340274002000c2c0c0303800040c10072655409040230040181c00c080c0515886242001e01180e21941d0642c841d101190b0804050b084a602c0d0b42e4800b80070360300600c0103c48500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397921726 1250 397920476 397920487
    0x1021e1c030e010b010203090907080912030406050403180b04120602220e0c12010e0709031b0f0801091a3601050702010627020415050a0212070b0714 66
    0x80e04480000c00c5165034501095180264100609440c240c0c2d03003050455109005d030300455170351594010382012560070880010340310328084504000802000401c0c0b407000000b4441004002d80c001d607c514003980c0d988004007414003616030945400d114903403c02c00140818802903101000750b102151207128014a8043c4c0000c9981c0ea50f101ca034a600740d04820f40c4c0c41004030790074040c042ca6000885489051504c07070045d00d41c0342c1a038010f01440c8078130740040d000107080c640a2000031000c0e640050000c1c0810740c07258910900796003240900c08001c1c580500c0020203520501540d42055072114004000c480740020040d58200003c101d40614402810400715022000c400c8986600d282c8024110f0041d1103c0841d0a4560250601d01107a142c014200811700c0c0d00d8001c0d200e90080403c24403d003c1561140c0d0303010380a01c0e00912400c5040d02c0e20043d045400c00300620141c1d445401b5a100313100780003006d421074024400d01401546417880000d24181c4214641240004070400190610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397922976 1250 397921726 397921753
    0xa03120f021c030905060f010302010c0f030201090212030c0f07080706210e0604021e09010e1302060313020a1e090f0204080f061503030c0c06090103090f080405011d01021e 76
    0x9542c15800000c80d540b4104002403000500249a021006070041026940365600080c04a16800c001801888941a42f002054402e4203c0070510350010b0a407690201e010500e0340d1240c1c040c0000c03000510903600d100e100010b011035100100c4c2c3c0040044c000076450702005803661354401715503105070101504d0b413200106052040e8101d403003424005100301d00e05881407000020104014003032032040803032011100d545024000c0d0640c0d480c03001030400c640f03c0744620320300007520740d00082d07004a01004001c1f400e140e0920740e40255008442c8441800d42d40d4011912a0000c030307800c088858a160001e01c154040e81e08200104c0c6a600001460310b0355503d0000c2c10900d562000443e0394014034107000c0302070300040c00d01d10b2003d01100903500c0d140f070305450265100f03a50400035010300408a80d891540c0e010b03900c0b003001d851f08614603819807011ba1030b184c03155510070f000e40750102c1c80400118943d0480300104e491240c00c10307001081514040000074001454812000d40544620003191603907 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397924226 1250 397922976 397923013
    0x210c0705060c01060608010e0103022101180501050604063503070804060314010918290903030103060c03140628060302040504060510052a07030807110a03120f02 71
    0x82c5110180005941c9081010081c4035000607880081e0240c50b0b0380c018000350b90707a580d82e54840154944c2c100300c44905a0200c1d40504000c01c020108001c000890400303002d01900454410001282d081203069160040180800d1254903503010505100e8500008400034a40e520305410066040381e08001c46903407058042c2d8015001000000c0d1a4288804080d4159100c2e074050314600c40f0900c00d40c1011102900140c400d0580a840e1000c41e000704c07900700d644051400c1a9801581820300c00d032512801c181e07520f900070b100c00c540f801d2800d21300c06800d0780701e803007002c103038840c0c03054800000d8540800f000714203040045080808035420742c0c410f400f4202c00e800c040c000e003281d840c00343c0c0380c034680710800c4101d42c02540118000c86c1c0242030303813525951140450341c9024011141880c01814001e440d8102a03000f50600c800340700e200c1c800f00c1880311182c0a4284280b0405004840c640d40c94248403072404a88401040e0f0201100c01802c510b004c0d07e01d02c141407200c1e20449800071100c030500d405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397925476 1250 397924226 397924237
    0x2100908070b18330f1504060b040609030302120c0304140612040b090706050f0406030c1106040602040302090603010c2307020306040b060a06080f0601030f0e06101502210c070506 79
    0x10001040b090b41a140d0004000404600c0444131307001010346044075044d40035203401001c4c0341030b030b1008111240103a43d50f6409031000c0c18854444946031a218032002c2c10440c0765000c00d40141c820541d06100c1401800c00f150140d18050018500f00f0b440c104034144100c0c816005540c0c00407080c480224000b0029204910890007440110303051f003800b140d0075060284a410080412104110500b251141c10b42180c007250720a2a0003d03100001c5002200d85145101e00982d25004040622081c820190050420703039001300c640b00107503280c0d00101400c0703030480504600820131a00440c00c0c00104c00c001c1041080c0c141010610301544d680c00a030030200101e8048030020050828000c1c02d00701119180003070400c07130803c06000d0911411032080b42e01c2c02040e160400d40c4541550100c0165034002240c0b0302d1100c41201c1a900303002400021240070381c01140d0031496242c0c2c40e204120310004441c01c02c02100120410210160f26800b01142e1003004d0619003880303000c40005840d2200d000514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397926726 1250 397925476 397925503
    0x10b1903020907051209010c110a0209040210140301031b09020a0c1b090f140a0209150d090b0f090d0201020405130b0f060f0a0e030c0a0b0307091e050102100908070b18 74
    0x941c08d07030222009002c1c009041881c010541c051400100107880d403595950b04147c040358003181d40e2720481001c81c1c074007150600341d007607600300032000100708041c0000030007818191014a404c1c160312256004d0480c007400c06803074000341d08402c924003c18050b000b044003503c222548440300a03150007082041d0303202c00141500081d52000c54800b0044034104164000c00c600400303501d0254442d00040f07000010b603540728200840002c1030060000f440c0e0100c01003650104000c1c81e10b141c400301802c1c04082c21078007054903000d0811809034503407041c0b00b118241d400052440c0c0c80d01c5400c1071044000d00c0300c0c00fa41034100019070085202e035070b40d24005d000800c8052138016a902d1141000909800001e42810f0285c1d01c5601c0703603503860392842580819100030066454a9a503100c40c00c481000700360740030880741859071208007166035014001a00ba108207800b240c50451401c9440300441c0c01391f20000c0c124440c00d20005c2c000880203100e84c2d8200c0003660080140c0302a4520032820501a1201c05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397927976 1250 397926726 397926731
    0xb0402160312021603050c011803030501050906013009060f06050a0909030503040204051510080703290607020a0e01060306180207020f01050d1418010b190302090705120901 76
    0xc260b40300c0d1542d808188104825424800038008403a055802404010b050010200b284640c402c4250303c1039008004140120406005d01c0c180903005240a006082c06280a40c0c0001c0d0154002d110303d000040383e445082c2d100c01d41011200100c4142c04241d818442d07102c011050101d0306501a5450a1140d1407002940034900070800512003065030180342e96a003450100b13804660024142c0f070b4070680544020481d030343da25445000b02031700139218990080700c80d442009503540c4452010305c83d41c40c5032010400c0c655641c0c0034000d50300c11005a030308010400c010028903428000b01a000e481c0c0301510000109448000b0b4082d00d0030700340c01c0f90700065501c600402c0105039030484c00400c2c00074030100f10301e00503241e00425502d24034564aa4144500007a4440b9102200d134064541e5100284640b00d1505010750a0701c050110325084006030742c02c181c0000da5520703280229010019413610003d0b049132030b541c2400480003005120030b05015050040340101c0800400f40b5100382200f0000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397929226 1250 397927976 397928017
    0x5010f0e0a14102303060a05030a0b06040c050c0a080c0a08030109091b23030709180b100f03060e030d0e0f0d050a090902090406120c09060605030402010504060f030b0402 75
    0x9104005070b2203980c2c9400c1001c4584150350131310310861039400c000e203422041e0359603580d200082081c3c07088030361000d9010b1207840489020320181020340c6025000440d410b01404820500888640c0503400300640139401804103900010070100c0103003884845a01500c103803601030344500085130026070102301103540b50b8048904000b141814410f0104032040d00e910790310300300b416415550303080101c2410342c12050a170300540d0b5a0300304103040040038800300c1071003140c008844e10a40405000301c02c989801d640d10208265035014071400e4207581d48041c603c0b400c5441c5484900291501c0c0310315480300c0c0003c10030002d8004c02805410382d128046001010041c0083e00410318150260240c1020402e062203008a80307075100741c11a084680f07282c00943c0391004240024000e0841d0350181110145074000d04041008a48500d421541020020821a50303075090550b4944807c8030003d000070350812082c031920740640107189482d0b1b894940020400f2103480420201d9000c07510324004c0344e010004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397930476 1250 397929226 397929229
    0x30f0103050d020d0e060306011403100e0a1b050f0c0109081909050303031503010f061409070201050103030c0f0f05061f0b070c1203121104090608061005010f0e0a14 73
    0x503290b4040c09480100500e081c080d10003841c000412070403d114442c0000822640e85c41a403101241c0f1201070840c90303a0782462501048007154078425098030035840300c00100400c0a1b881071825450803004680c503000c4000034103c9075540b010002c1c0312810400d02074243c11071824442e0b20660351050320010350b80c02d0207903d400d15006d1000300d240c0800010200600c0980c030003006494011001003d5142081e00060010380034040c03640e10841914500000064452400c0070030000043c4c013610118100e032500b1100702d090b10700902010300421011900c1c0c0c400604400716440c107050203a40802030410706580d03581c0c10180c06070f0351100c079003482181c07070aa9900d910b00390000500b402c1c01418074010003030786c807900c89680911810300500f06060005042c54091262003012642c091820050710b40713102e440100903040b1340140c202040c0342c645d0210b082003000449600500c0c510360800c1046241c6801100c070001d030382503c0380401c200760580421382d856200424010b04904900c944c0610040130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397931726 1250 397930476 397930483
    0x14100903030f0b0a150201090b0a050412080403050906090a17010b0109080d1e0314040c0f050402030408071202012702030c06040f032d05060702010c0503010518040215030f010305 79
    0x680030340340245450030700e405644c0c0d05402c850460300880150154111140d9040c1d004151500c0c0140c4544150010410050b0455012070301c1346128000f0f40381c1090440c41e081710484d02c02c4a009010070002c0061850b18580b06002d05030380c4a000700741101c410f88075030f854220b0a41c4252034100c107a465041117401988c2200d040b070701070310002c402000000300350000200940700d64a841044402c4c19076002800301d100740c12020612060611aa01d1810030307146c845400c04c2c4901c184840420350fa84042440d03c1c282c000c41e0700594001140354200441920354002c00034003217030303c00b05540d614001109401882e090b03840103020003000282c0a000c09005050030070681c5407510b40310300c50403c402e0042e42d80b0003000800307594100a0401c4100116a500034500710101152400c0354500f01f4000b080240c0020700074460101a0300030b1021312070754207086e41c090000f8000c070303544400c00c190071540e040d444500c4290b05c01e00041207001034060050b84080c15a2050703c16109540006005005011381007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397932976 1250 397931726 397931741
    0x70804051804021305090d030e1e0d03050108070501080a0c0c05011e050c1e1b0601230a140f03070308070c0302030f0f060a090f0b012702090a121410090303 69
    0x4c070020710851815640c1c8945491081c1c44031002e0643c4c0c0c140211283c20304002540f0f0100425a10b0103c10140e4016507607500d0f0500320050000b81041c0020442c1b003404a640360456038181c45662030381d140c01c0300700406012104409020030401003981408030303c09020b087d0100991902401c070b014105000101518402010380c044054200000f00003060440e410303200349480b10180355240c816002c1c44c4400c00c40c00100d074080070302c0b40380b00214604402d003d070b01004035038080010480c10311640600c14020a54030407510324014800054a9a04242e07000c8a03c260000b8107a0300c0d44c585903501c01030190400003068076070820040d818001c5040c104042c0303100c41b0000c1d00420050000840c100c0d920b201c001c00c0301d07a02030340b2400d89004029a102d91010125446041c1309155070b1503000c643e40c800c5549501080c559106003044035116818401c80b04882c102402101c81c0030b00b0043d002002c0c02ca850000c0328020030316101210003690a001c41c0e0729100ca42030001c03039000d0307060400400b550306c2c0f0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397934226 1250 397932976 397933009
    0x211606021b0306010302060304290601120b03070b0c0708010609060501090e15060d0219111204050a090507020a0c03060e1e0309010c150603140f0a1707080405180402 73
    0x32030300307400a81e8005401811281e0455200c0d54a541e6031401000010324110f6910241c1440c2c8100985400440710081c45400282d86210340c0c034480c02c0343c48054402240103c2d40540142c0b400303220340000030b4020445851400300311000c2655503001142110050f902030001550750350000c3c020340da409908040144407008a106060900605051203c2e1754000f01e544209000506502c00241e141c059401440034032080c800c800801002c06418001c414401c3c65a50240d80c0c0c011020350000c2c401c0d54140d07003001e440383c44c0301401d2030181070003048003800500039407007102a4117002689190740e50002d10b12400020400c5a035420116142001583d00303000c07200c40d401d22400c581035000041d200018403d00e0500d0701000103003416040f461103002c00c0b503c2036003072680201c1800004041e402c8000c0c4ca442c00c4407030345100c9003207050312038481c0c550003011194060282c14a441c0c244015003032283c000d482051400380d4480002e81d0810b003ea48051303c0300104010001076240c080c40080c1c0d540d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397935476 1250 397934226 397934263
    0xe042004090609060e0a09062306090a180b040507050d03120516120507090512010e0f0f0a0209070e0303040f2c070318051914030c0a0221160602 64
    0x140702c5e03000301048000700001c098603901c00c0341005001c80d54014813150b00344015642410280001481e01603a021036403240211958008a000382500c0c0c800c0c4924090b8880b49929140c1c1076590720a07414a0207401681d20f885003240108550380d414561091544c03194484c1c032000c919403400740041d104000c000450440c00c40040c1103c42d50450040c56454002440009860341d0701c040907103224031940c20060708410b0309182140310140540c0044030311724411003200d12195020481954074210000c80b0a4240c01c4013411200500b807410580d5004409030510b01e8011804001103840c5400a034000041e045004e00c04001d20111004270507410f0010040d4040340c03200b01000101128000b0740703520101544e803044034070400c101c038030341856940d8007200b5640784c4064540b200900700305280c03050307403003880000c1120308402c800400c544e04900050040d2a11003404e40820583d00040c3d2000f0f442e8681c95030902494070418040d02c1e07100c4580e203034071a2419081c180000e00d0715040c0007034030b0b02c03100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397936726 1250 397935476 397935479
    0x10b0901021b010e040f020c0a030201020c01110f0d18050a03050714060405060c130308221d150d0209130b010501020a0c150e0d050109021309080a0e04200409060906 73
    0x9031301242c105018001a2408103180825146c4c6500034072514001d07908074011a8202d0b41010350640081107900c00c001d0082c0300d02d001c1e03158140354903c605001d0011500c0d0030003412100c0c0b10190040445610115410480a005916420306021409400b02c00240000540008208408a210141400d41001001c0b946050380c1d40503640c8502400e01c801c5800082248101d00c88030154000195500c0a02680c6030800324030320180700c0001402c071944040c420704d00461000c811854100c000c1d050070745600059141d240c4202c0d00000f030382c12038a812010b440c550070090384070740a4035170141168510a80e000c0342e25040015040806030003090454102c020440302080488005d03400352144000d1460840c1c12001003655010702030403405800440c1c1002e00800c0c0b01c010340c0840740042c000c0e228a400180903a24031411900c0702580188425020320203480034034032a940e00412014060000201c400f030544222202d03482c0d005a0754190400010180030500803401503c00800e08070383c0500549 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397937976 1250 397936726 397936729
    0x10020c030d090c2c070813080d0b18040b0a0c0c03030b120d020f07050d080406120b040608070515030424060306020406200607020c0105070c030605010b0901021b 71
    0x7885035102050449444406600c1031010041140e0700601034030074014054440b20408000d84034038890034071080900040003809071802802080d1150074144103030a02000c0036034411610360407169980003820b9507070000e42d140c1c2d02d4420b140c85068410f04c2920f21117140c0340c41e0403e81e8070002020a00501d040c0032401c440703280c00c0385485024951509003c41d800d25a040440d444e1001e00000880c148241c0b1312200001d070300842d401108895160070f4a03001503c90050020800d2007580c020103110013080104052441084100740c003100c12000410a0900000050300340da0885c0c0200740503400c0740300104201c0c0303005410903180302c0c02e1219860440c40c0c107031544001501500c030644400d0080b501c01660004040c2c0c031460203940c0c80343c021500d4a4440000902c0704255140c03032400414240030300700300b0820005003e84034a03081d030300408503628564011030320340c3c1243c1c2d0200e9201107448000701c0065428020140602406060603480b42c070140002403038184000c500b43c0c4d40c3c40610400c044603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397939226 1250 397937976 397937983
    0xc0d17010b0a0c020402130e100f06050c03070210020d0e0d1101080702030c07030606060f020a1203020c0309090408131e05090421090315060b25080a080910020c 71
    0x1112aa0300c1401d032500b11207003082d56020b083c0d2400075800381c800161a100c03500d00c0d115410940d143e0011602c4076541d60000100e940340c280c042e12110450b200f50401000388504000e1004405650540f803c2201c03503800f183d45002104003035070140c0c0140c81020300f010f5101151320071a900444204205a48640300c10f442022000402810002104001019280200104c9111410761012180070039600d040c4640244103038001c041c0041c1c080580281c01c10b10005040d003520350002c1808040c84c90390f16017035000b0340c000c011041160205000a0280b5944e4903100c6108a00031621213960716001c2c65441105441500540c40c0751512800410900c83e425015070f094550556602c6060f480f541080d10308003410100d481c850000d011110b500700c079840a425001c0368412140b109031110002e2460041c0c0c3c00310300031400340c3c803814804031f6000300f6902c2d4400050141904c0481e4090404e0b100d10025921011440000c07490b0b503024401254000c014440c817400302c3c01811802c00c07001c00c0c00542c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397940476 1250 397939226 397939229
    0x24150a0512011413030206070f021009020f030f160503030c1906090204060b091009080c090a021b031b070b030601032a020d0215010323011b050c0d1701 67
    0x50030311540694261402580070940e051042841d40142e880c1c10014104c9140c1e9407402200180074006c04070781d845000b500c01d401410f83c290040c1c0000c1c071513821482e00074507000c40181da1087c03c010380c3e20080e880c18040000f850300b10401a080c0c005001001d5210300416511250095004200224017000f002ca0a00c4c0b0110942e100c006078808142440c1d0b010b482d04080203584180b03450710010301c6e1400039004210f0b1140036110081c604045031002e50307182281d80300f401401d81207001205480d282100d01c40e640552403040c0141040141c400761414050040841007180c0d1000a0401c4845440c01040313800c0c2014200400c849410002c0141140c08050486414580c4a40c88046c0d01d4802202c00c515035200b0059030b010f09a80710f0740c0250b03250f001d40c5042c00540554130031440c01c00f1319100b44605072a000042071581c10442c007000036052240e141d203512a55a03072303024848196040180c8086600c455070303440340c44c4c1d00510f0429040c03254910740340080c80f10501c6040040e000d192071690 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397941726 1250 397940476 397940479
    0x3010608010b0307020115090501090b12060112030507150504141204090f0f0c0206072d0f0c0516030b01080105091c030902030303010f150c05120d0e24150a05 70
    0x39184e0b00c501000340c4c050312803001c000c1020341e041e200c00706030928590301890482d00011000d110085400c3e06002a44002041e1020b440c1c00c440c006210303a91309000d20034002403207440c0491809905454001030a003e4040d021000c41e22001804240801070440c0b8121484100c0548220142c0100e140b20364403c0344154041c0341e45580c0d52105001d2141c0c00150028041e007000c0c407411046240c001d48a50741251403e010407850081451039800e110701e4227512a03502e1112042003032060400b9a5201d2003111002c0800034a802e81c0000243d09102e0141340b600f040c00039001c01400d61070110344011050700050030301c5c1e25101c204034500000042d4100d6071100c62a4841030700d000b60508070090b20740c4401c0a0f402d41300010000a104025100e00740031148100001c943c001071083c0e0031204407056540240c940da1180d20801d10390855040100b0040d0121003000404002503d0703494145140040311000300c00307158a0302c1d18216441030321281d1003901a1407600d504840500010b40e0700b2820b001d11b6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397942976 1250 397941726 397941749
    0x20615100519020609060a09050c04022802030d05060906010c1103070b0a02060105030706050901121e09080a030c03051339061803030905060c0c150a0809030301060801 74
    0x140d2030300490480d81c1c400c0080c07441d2901004100006542c0c1d540546007400f0320301c10ba0000618101e01031046000940d88034003e00b8100303d90b1001c10010390004996030321012103c0148442c030712011060b44a0081d4260040c1d5141e05940d1801d03012101c00904890040711880100b003040e81c3c0c0081301010155104c1d070312203070110141c0007081c43e00c4141c0d00030030554280080d04440040e00000c1140c1247c0c800c0301140d200da07881d0b44080342c180c0103601480b800700758006070090518240d5000b00800001007200b08501c01c0403001c941e000c0e02c000301825104143c000070820503065050180b402c180e50281014407060034010300308410100e82010240412608202e00d0200b2884600c11b0000449400b1000c0c0c3d40303900071407034050003d4091060102084900014180c10004100610102c0f40c00d030300c07031210f45031400040c00501d612804210810b401100c0241c503c0d0366840300c081c04103041e00b0410707d0310f41500c05005000b890001c2e040150b1036105100402038540e1048500d41503d41c9086078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397944226 1250 397942976 397942999
    0x207030b251d09090114131112010b03070e0402040f0e031e04080d181a0301060c1a010b03060f0d020913050703140313242304090203011401020615 65
    0x110244140d044240d580d11041d24814084c442c08150020301c503205101020000303036100c810340c410485014090040400d40e1070001040701e4500f462440e5280f206440011a00c09250310009081c84c0301da4005e258909501020700003942800e00c251150503c08080030840411840348203980c0b8041d042c024004580d00700e2144032081060020344000301440c108480c0c0070600710b40080c2044144140c050413149900e5000601300040005095403401e4404100b80743da420114201e914203295030065525400c043c10700c540d660b92052005000708440500d50740c82e03007400360400400010060a07184960001048070f000360750781801042d045120400e0225100342c9500c0c150b0305280301544060319080f001d11880d0300801010009080c100f040c0141d4114264880440004529410354005014203c03038810b81020b602408901b4203040b40051240d861030f03140491118158066000014005d8000c8010011104104c1682075100c0090010300201d1800030000c160655041401c0b81c03040580819 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397945476 1250 397944226 397944257
    0x72c010e0402030a0902040b0306150d170c010c031d06150a0509040302030a2619060f0902070501060503071a0906070b04030e0307060e0105070825030207030b25 71
    0x80d030081085014006540fa840c104248000a1110120982c092400c0204900141c500481d410f486002c0345400c294221800c2d00078454001c03921002110082e00c50b410b80e29101500f4000790524044c60000401c0e16950450003d00f42c6401103203207110101c3c5c00d503a110005401086107a07000d1070240c40120034000a070001440c0e102d040e4050303600711503000184010f041d0301000625060482d51640703070904254032801d8040c0d2507510131002c41e00248002003031042c03039000c0d4207075000d4001e1040130a080d81c0303413107400e803500b0b0386580030b005816400a080000c0100a008440013020200d01410b047c074680f10b0f0081c420a07030040c1119055800003003100c0c0a90311141550940c642100408829103800d00c0c02821081c44040c0d200d109214128001070418410901c401802c10103075642d40c01c0000c04d170794012440c0c100683c00c410044001c00501c55001c1c01c1c0821640150081e0b000306041c80c61414007050311000501480c800603060641465040c105103000c550014035894a400103d55221 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397946726 1250 397945476 397945487
    0x90b130c120b03160605042909040f2702030f0606030d05132c330a03050f15070e0307030206030402030c150a020709231b03071205072c01 61
    0x60442d80070400d032580801c46550101c0070f00161101c084d840b50200c08c603041508082001f5179041003c1c040304001d02c05880c2000d4000600b15482c10602095480d061200b0000c00c0c81c0140807201c1001030b8007644001e62604100e920400f240038000340140382054404642c54081c95024501400300009258101020032000d06e0000c00e40700e540e42034000b41c1c80b544500e2203201c3d445004c14074200305004c101c1030300f00010501c0540b904444010200038002148000045c0102640303988020000303000000f0480c00c2c1b010240d90381009026203642c1d01d6120450a8400e006000ba80800006802c5030307806403400102d0700c0c250303034048030001c1d100ea8a51002900e001d040154092f0403682524242c800341120388040c0c6500c078025000d54142c6521038040e6000c8034201e114490070100300c902c21401c4074044c000300c140c02881c000c607aa040b0040384001d00105500940700580050982c2500100201c5c4c58810070b508480300d489d140049007440d068444804142400109104590070040e80d526030041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397947976 1250 397946726 397946743
    0x360903070510020d0f020313031412010e0901060602060906042003030c0d020613080f180d03020304031209030302060f180a080405040c05041203080705070606090b130c120b03 77
    0x250444a541010300b44602c081e42001c03190000242c10017842c0c083d844003d00950380300f80800305a0740d80b140d190fa2001c5543c520904d8000305100c03810890511090511002c842c06460a4039134045541402d01c0803a0031104540d021104540040c001e000c2d410f900070134030076045030300031403590424029500360f070341e841c2454542140d05101c0020760040e8418082200c2c00c8042c02074094600540e10340710b5001c401a2080340c010002d0701c04012040034448090080c044110002c1c103c80012034803000804c070031003006074081d809a070020030704208014034818000d0003c4558036043c1122440d6641c040e540780e1020b0034031941486844002140c08644501310340f07004141d0f004590460b070309401c10300c02d903038098003031a07000e1418800c0d9420000d00540c00c58044490b105000d000220981c1c0301111020000350440007044001c02020020641500640d409407511a900144081012041002d03103e010071481003001e042c5091019141e800918904210000310b0020500e400c1e02c030002810308048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397949226 1250 397947976 397947983
    0x406030f18051524011b02060406080f150d020105030a0b031c110d090611030405180a1802012a08070b060a060e090402040b1c05010b36090307 63
    0x2407400207070a2020002d103c2d1641054810b80020684800742c20a2052000c0320384900c88420140355070810394480e01b03840040d0380310300300701d00c000c00f40d240d0003d08150b04c250f2016000074001001d0007090704012a40c2900b1100c441501e418203060800450100c00190001905204010001602d0001c0c241c02400d45208000c00303840380c0d000d920120f1011589150300b600c000424420000349000d500058481c050161754603020302d11440d004088465808030074068110b80011300001a0035141e410f101c1a000e02980461001032a1402604040f541c03055150032910607504c0058000d81d0304142d54480e021003014060a01030110342c540c0b40d0165031303010300400007880040c0800a00106006041c0a0319049907500d4100e03030355000895030382c1503840c1c4d1960700242c900080f8005281c664890980c00c54050020781ca50b0166014140145404800944499450359118011450f010541440d80303101c05a182c0034803a251807030701c041c200404041c0b1042c0040b12010801100c1c08000381c031041680b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397950476 1250 397949226 397949261
    0x1209060c0f010507091706040f170307051801030902010c0224070c05040e121801140d0615050c0709050a1410031109160e120106140a05040c050406030f 67
    0x340c488016000380340403200c0e800041c40000006c58003000c1043c0d07000155805000508141e101c0d0b48503085403200506c1c0840d4400ca108482011001600c405544500401e40b10141c89804258621900e00f0030381c0f0101e41011715219032040140e8010b040420540d40681d0074402885185c081e02c80310040880d000c512028000ca101420000c2c1d40316407405498003600c06000810090b202150340d0a91860140b00d0a4014000318007183c0c00c0f100c03103004000c4e052400c581d421141441c810700640c0246c0b030340e6004a44521051013200102084440213241c18540207140030458031056407604005c0c000d403900151584c001c0f0702c003080da68105514010346407062040906101801140340e10451004881c020400e0501c42c02600c0c1c580501c600c91100c0c0d941c046800203001804641c42c481108600758800400c600c1103090050034428180640a45805800106528401c01c130f0000520740c032107446981000004802c60703904c001680e080341d500d414085292140310301c0b407400ad002c45443e254101e04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397951726 1250 397950476 397950493
    0x11030417040819120908060705070303110a0c1109090309060c101b020715080103030c02010210020d020c101127030316060b0103090c1502030c1c020d0c051209060c 72
    0x10310610000303c0c26201d101003e850500b070090645024555115008041d000307400001c0c0001c0c003a00c02055842e219190004e0408203000212031290482500b10f80010324810340c52007007103901a158105c60340112070002444c6400d800c007036628420440b0303990207140041601c1c0e80440c0c00b0403817030803100c20940003440701c01e940310100d58801c0c81400d5280c0040c480c4260004003801ea0940d00741c1c0d030040c0380da20040c0316800c5450603120050880c0c4103e046200c0c4078010a24440684003403d0807512082c070140e2b903030302c1440b4041c0c50404004d844082040c503000c40c00000500c0380e0f08450441004c40400301c1d40d440c4913600c200c0e000f0a590102c075054040013407a00f40d40811107285002492141004001c40000c10004508032204640c00610700714400506210410300089a0920b4101d20710442e4580448007014a090403249000340f1600800d2920405d9401e0301801440202646c5150207420710070951140c603580c0f20603004000c842d88000600b228192074007400c456005942500710f89a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397952976 1250 397951726 397951753
    0x30c050c03031f120206070209090c190609270e0a14010b091f0504110705031b060603060708071808010507170c0f0904051e040b0a0c03110304170408 66
    0x558000300204101e100308000400e884080704c0032080c070250003800c4a42806413541c28410861070241100b02e50b80300e990b4040c02c02d561000c00501200400c032401c424200d10b0702c0b0003e440b403030709608420040c8181c0c0c440d40081141c036508100d000468520003042855090860038202080d803040a0400400e07002e12184000d415040b11100110680d041c00042d070356852409001e646070082c02c0060440f541c1e040105240a41224044c0a4020500742c50003a03203a4505165501403400b030009040d100501fa22600800d01c001c5034007a00960181c29180b824400003400d0301401030000040c010086404181d042100c1a80d0707000d050f0140013040a4101018003038810400e21910010107801e080000d11051200c00a0324186030700c102c422814042c0100800015000c020021001001c81c1c031408074495030b0107584107018a00500c207480c218140316140c0410795501551040526003820254904e01411404503680b090708030358103440d68000c40488445911039580120f9482c0303c0c4121040b0705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397954226 1250 397952976 397953001
    0x1a10050d0c1403180c0d12080403030222090e03120103060e120d0212010b090a0306090611070b010e07031b0f12020f0c070e0f01060c0c0506040e0406180b07030c050c0303 75
    0x41104c160219080c413996081003245490240f200144540e00708000345003028000c50340c40750801c0c0309042c090305010940d0300030300310307400c8a20a42c0500351405008000d250801d2181030b07910380c3c03000301861030081c0c1c004030507541315030610004041d6070740d5042140c0481002d11450003001a60080c0a554925417441400a034000040704288007526800029947c40c3c60303012602d1584018200c0d1500c640b954840c24002c0105003c1650b0843e103d841c0d00c111181441c0080c540e01d449a0f01c00c94055043c1a1426000d01004004600340362a04c250782100101c10030403a07030007030100d1921200c5050f80c22001c80b02c80600d10700c0040d4032400880d0098036885004c000c0c010303030501d03541150743c030b66074614006150007400c0d60740c0c0c1241803442c0d00501c81c183c4070b054046480b600603071071007811540d10380200d078456020350f2000300ca56404800b1b0004000d1140120f6225031040781d136959100242e5120b48480384805000c5070140b59440c1009414140a8800d039032210520b41c0c02d490701d074544081079010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397955476 1250 397954226 397954261
    0x612040201020f0a200409120203070510060e01051003020c0f0f0d0309080f0306030715090e0a0e0c06160b040f060e070e0402041802030d031a10050d0c1403 69
    0x250150f890403142051002924409040e0402c03c1d015440401c0420280101c11480b03c1c4c58006494003401340100c0c0891a001e0300e4203106600541d52a1390b1810402d0818115495484045040c00b030704100e1040580d40c11030540b42c0c201c900d0030424103007220a038001e11400317501401900504041c404140d501203004080900d2403415510321016800c812070464a80c5440144201c1c02400f00342d0310000c8150155500c06030240450f030000d0740705c22a0200c610044030329000015030b5030006110b00f0102c07120941d00580e885005201d100c0c03286d48803646401c042e00a4500600010600c401221001d00e507940c2c10350b8006c081098181000c4c10b1812074007130403100941c0c4050802210115120300043c82c44110341c10642c0d0740d681740d00c80fa8200000b81401016401a024124044e0b001594003031000d844024a962000246107070b02c200f0500e90b540c2103d034044d00c25402c00301007007105908481110002010f6041c002941c1d000d1400c207030f40c81401418003511084000c0100040780c1e480094101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397956726 1250 397955476 397955479
    0x31a0f01081005220f120e01171f150311040b090103050703060f0303020c090601020d36080c030705040b01090311060c07030f110a060509010302070c170a02010305060d0812130206120402 82
    0x402602040000e590309000047c060b40024a107a2201035080040c4000f20b0300f0229140e00c103e0100300c040703000200c03007049801c00c03000402c04210240317809801d80311b071f02c28200c4800750142c1010702d00004000c407800384c29216414162914001440391348240d202c00c028044100351241c0068030703804d0095854103104001402071042a0120300303d0360000806120111080d6902011000308003806080301c080c0b407601e07901c2d407401c40e403050072000090751821020307100c140f004020201360700c410145090881e520840c020380c9030640f1251540d80c45098602034940160818104034940300108d81c9511070803892603958081c050020041102d034032049010f00380108013004009203418100a84055a80706a0006c02c9041202107020350080d005032956a0060380d800a0040e940c0c6030b00a00c445100413200b4030703600b20440e884115030701486925000300c429980f100034010b150391155054481d441c400c1d448559400000340c103410007070407140c2446030301401c0d980d10349500300c4505018200554049 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397957976 1250 397956726 397956743
    0x21e0c03090f09011a0c01090602190e0909190203070302150301061106090616020c1002030406020708060f132612060102030c06040605150a031a0f01081005220f 71
    0x160510303d042500c00d130603101c42418a0900803143c0c6403240c82c0d9401451446000c3d52510545404140c03140f0103807051a8414200f09000000300354018030884040414038460402c0f20280701c0e0700000014602e0303e2107c403810000d000f0f251400000d24000e0580c2c8001e42c000b8203204e88941007060f420246048503082d4594401c1f9009100760f90707031030f088121007103401a80200c0c00905d0140e410308090344000e030a401521902c006040104400c00140311030280541d000180800149604102480080c162240501981d0038240c4880703036483c1c07019146000741080d00d901c04060080c0d01600406124056110700a0400e0741111400c0f903400540c0150361103007104000a4580d40080100d03a01c5401c000b029020560b01d66035900c005120141581c1c66008508078034100d182c46031a4844041d41c065028003105c152290b0381c1302c24000c00141003004c44002040100501440001d4440c5812214030b00031400d5501c6480d030360020902d100020118445101002e802c1c003100404d00701115000e808003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397959226 1250 397957976 397957999
    0x1104030605010f05030f0d020a03080a060b1209060c041d06031c021b0a05100309140f15100605070f08120412020f06010f03081b0a0b070201150303050706021e0c0309 73
    0x12647c845a1803400000580c1044e018040064803420500b039001e150782e980001c4151300d480d041129038000c0d4403100810072224090100000c410845030794451000c5080760300d46424806101103004803504180c00c046588804507090f99801c0c420400640e0203841c003481da40c160300074025501c502449940f91603041c4511604445e041141e50141070310000b034000600d0548910b4101d0062021180548900340c260441074541c000c140240000480c00c44010941c440134030711000c102510140140c0d2030303041686010861240c02800340c036005900012600801d82d41ea06103040a4416400446070704100c0f40100420000c80003095a100fa0140e42110110f41824074855510242030003600303100c0c9400c072000c01c001516100180a190b8011515061044841428902d450089607044621046000801000700d90902c140401c1c0020501100304c030f80d240d610003070003603c604180078100580004035005042c4056009039103484c0c00400031a5510f040c0318115850303402100140b031103164114003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397960476 1250 397959226 397959253
    0x41a060405070801060f140307090f0806040b0105090408091519030c1b02030f01020703030b090c03010e2202030f010614060f04050f01020a0c09020a030c0804050d031104030605010f0503 82
    0xa07aa00c030ba08180c44a0703540d6402e0002c151442c2030400c00740c07420402402442e80d1032400300380280d8054581902d03819401401c012100c0000d5000e5040009250300280810020401450700d007070440c0c10036540c0c4000e94072141806805481004a1070b9000182e04402411050581e4000d10310b40f0310410515a10813149c00702102075403458440d1400041c6112008a40fa40070074000c40140ca10050880d42413402e40c1c41001d00b0781c0c01800c010384c08a076a5492000960819010079940035070402e83c00307840c640c10070380b0300d42454001030000d0300c9100025400101e80e03003c20103c0151250024100c1d1704180c09039500c0d9010740f0a074040c040080d070007842c030b2600c42d0a00c0c0041d81c09281e000041c084c101030402c401c0c40403601c500b2140b40e0462044680d2080403410000204010b0400e042e809607540720f403c180074055404030b12108003045031103c10880030071740c00316400a00880501d8041822600101c154450b80101d800203410580381500000340144039205040460310240c0548005041851 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397961726 1250 397960476 397960481
    0x6050901030f0902011e09030b0f011505030f011e050303030f070306050414160912110f2d060c030a030501032117060d0807081309020408190501020909041a0604 71
    0x4500a0106103200da0103c458041100040d01c14046483c0c0791000c556a5112203926000540b40ca25184052b503005002c0071140000050002142c0c0c2041c91035030a025024a8406005100740c916040821460386100581003100d100180740090403a601c0382031005a4a109000603503481c40030a15001c800a610306160241d8044d261064002d050180d4800300c0b69080071212000910400400f114045402c00c42061800c00c10750184010400402c1c5240902c201501081921880740b0942650010300c90100c4503918044141e0140381044203000d40040b600c180500c0d0684421400003040c00d0103565815401181200d02401d6903459040d00c0400340001c0040410440001603510345842498541450043d500402c1c0a803082460000c5602c600409401480b030854001400040e004e21164994a60001806680d40c0c11441c01e0314048805996418144100c000c40c0c0082c021041071280a50642d40034010141c04c020092401d443c1c0000507403205080080341001000c00315803d0308003031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397962976 1250 397961726 397961741
    0xb0604060e01080d26070c0b0703110409020c0a060609090507050a0b0702010503071809020c0f010b0604093803061b16080c0a03020715020f1518030406050901030f 72
    0x5002a20004c015100110380d0040280c244c010544400894150390018900800381300312020390740c6002c103261929000e03a81140182040341003508021002071a070030450219800c0710b40941d00180c3c0c2d10407460381e40703013400c0950304082c1009117458030004000142da0030021a15201e2020340300216114020403001c11424005c81800c2c010520031540194002c41c021600480c0d40e0809114064884094815120460304081b05070cd070045400d482e09802044604c2c3c504510000034000441a8004604640124801c1018407500c8811012010140402c60041c0d0b01e8030461881d10b081d2043c0c40541d1040102070b400340248284400107c0c2c15001c060720180d1040c040308640c3c6018500d5a1a50300701080800a03203e8440030405040411000c101d0944074610075000b4040441c940508400c10240f119071000554010200382011000041104c240ca415a000410841e0700c50707203c81c542014044103600f09a1000140c04605250042c0c090702101500340d8040c8048c4640442d0001603900d403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397964226 1250 397962976 397962989
    0x51302030f0a0b0d120c11010206190c14030405010603020a05090f0118020f071a010803070512131508101d0f0606091309021c1e03020102040506070b0604060e01 71
    0x5200c0410140b4801e5003014843e030500800015102c003250b102c42c0d00d0005409001000310f82c05015500801c092241034201d400024009868a480c10041d811004038a00c02036440503541c4414a08050f0b0140e4a4600491944401c43d9207d02e000e1401b18000d1003540026880f40409020011b03651a240c071004d4840d10007449003c0c21a40f800c7d9076040741d40092946621071940078080300d003004040901400743d44c0c1c001c0e403282e20914480011108020030682100711690000c1140401003800000e00c4403101042a03181a0754001d02c100c0400082e416412119921070001541603060f64080c82e814001c2d40c1040c40d800700c582d654490a036050b5042014950340e181c2c80c400085030389920703640d01031f840782c0081c160034030b070007100c20008101d41820300fa90328403583d07251449410350419400c001c141c10220070307502e4110070b01511805e0400000f040d02a0b1071141082184041520070340607a80100005030180d0707251219890400c0c0c0ba101e0031610503000e60f1405000140390300154241314100d490 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397965476 1250 397964226 397964251
    0x90507123f050c39061e2217070b030402100c0312020c07090e190f03050c0a0c140406050603060409020f090a09050f0303060109122a05130203 63
    0x10715000d0380c05800c26800c8503100d000d002804000d0304821842c00041400d104404144405070006100c508030151a07800d00801043c4045107400440b12407080d0035403c10f04101d516040303401c3c10894000c0c415060386c140411169400110920070320310304024691041e0645d8912516070146a802e03000440707020f1b601c45c05180d8400c035010700401595081320700034a0300348403800f402600c800c1641c1c0114224881640245003c0040011a2180c078014401031b0f805031401d1070340b00aa10b140ca030741201d0003920b0a0611040d00e001c26000d4411160300c1c0c250107040e5125803d141c1465500d00c14a441180c5c0000e080400f0f820036450244038903030655400502030b074110b0329480305000007054020310407a0001c0f8580e440007180d641d00c501d8540b003107421003804030b0009007500d8483c6c1402010400b17003425038014401d01c84503a030071403038000c15100000344000fa645800d0416207400c03410050b019200000c6600042200000600344030159003040e21211032144540c4081c50417840122001c014118 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397966726 1250 397965476 397965593
    0x828090f05010507120b0d020409031806050a09120807110d0b070f0f02030307080f0a09080708191b02040b01140a080708100b180102030403050709150f030b070309050712 75
    0x14155001c5406640a4335040c520300200940902c58201c0c2034120b074010480c0410758080c0503038840696405088681604000d0001c40e0755010fa03203000b010307001042c012021404102c5a2503550426442d00e4000c045801581000350010b4800c0000e00e04550028040380f002c0144e140c00001100d0103007200e603981043c907a81d644103d1109140242c088842243c0b120301d04804200c00350050700c803040c02079914581d20a4120340e01a4041d0441ca004c1d01881181d54410b0f80d42d2084104c01c2e211241c05a9010851658550040302d07861030802884442d28804220b943e6a103a10140040c03007813043d9115403010751509165010800b01c82e00c07900707103204401c10042d4904070902403229241e078010300440781003e4403952a01e00b860340d00e422890680d070f030700c0100d405a115426101c000411030090031700307205403c0d500c405070a401d00a043d0f00601d602c0340442020803501300b12410041c01c854802d0003000d9414504139a820311039008a0280e00d261014140415601345070b0224803107e891240001e05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397967976 1250 397966726 397966729
    0x2070611040815091207082106150a1701120b01061814120f0607032702010c020d080315040b0405091c1103030c04150828090f05010507120b0d02 64
    0x3900010312400c0d09008450b045441140c110000c2c1c41d282d481006408d80b1b0704504511100404694001c20f040c101d060400d00202d07450320041c1c2c0329401c12403108103580c3d010641040d181402e060360703990105034098000044040700501032a141621a0141c0f0517036236a01e100482344102c20500c1c030088002c0c00601000580c04014400324101c1000d0410b40300c0d0a901c9800303a08009001121031001e403c05410890815414854500d620b80503404101c2c503d00310a00c018081c180c003070002814468840001003e40d5103100203000c142d9848608035540f0720340b40358600601c1c1054008240102d04041d10310695181038000c0c1d62107943c010004081038406040700301c0508014111120038040591008039a8001c1403004511900c04500415076039031528a85030f0189014012010030400d45d00c01b8440c541010f1100d9200b120800684101c20300c0003802140001d0000680c0200b840c401e1602c15010842e0640000d4801c030310540300d0501004050701d040c800d035880c040e0003079401002c6100341c1703006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397969226 1250 397967976 397968013
    0x1501080a0c030f0c020607080106050a09030308222108130206071407120213021903050a0f05090c0405060307270b0d050703020a060e0906040e0109080409020706110408 74
    0x9100491401041006610403414101c134518030b05500141c002c0020840040e0300408401c0c01800d05141c8503203001c01d44c12008240000744d02008041000c5803001c40c04c0407403c0c0380c6402200841c40c100d990900646d1400520305079420b0b400c0c40680c9000c690840b0418010002c0174800c20b8000c41000800c546a420020b590b80071100c11251a0705041c820214003030200020740240403148105070800c4520300400c104204000e600810316401003182c100c0c0c0345949012412030803802d042c082080d40b00d21000c4d034017a1410b940c0d40c442d1103180104001c020040060402c46440301910b0801c1140c41d840b00f456240c070454028041d08140c11400c0d000c80380079400100b428140810000180380078400006410f01c91022070035100355010035010300641c54a80461001070995003440c6220200c1e1002040398290001c068038400c80ea200840311400000707400410030b0980c0030009680c0d503501c4441900082d08170403400d0307840b6494403141c50700c00c401240440e41903031298401003008044280d9100314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397970476 1250 397969226 397969241
    0xd0801150c06050a090b090d091401050a1d030a03080105150f040b031e04050a02030115061d0a030c08060108010f0209180a0e0304060e03101103070f050903030301090b04051501080a 80
    0x892503030f40c40c80c3e60102c6c0c80070a40600410450001e81799128240300020006000764204080055902c0e0714007002d0382c3c108040700d021100c1c906100d01c8001440310034440c0b8404040f1420f4040c050b50140b003040580c8801114142c031000c4800c10759409003030104115500a8001001c60b06000704000e0101200b0392010b903920002d103027941e080488643c1500281c480095800b160310361301006410302103280a010b400e4498200c8503002c48003601e0401c0c003e0200060b51115240c0d4940031103020420b0301d920303c1000c003558210380040c04283c0d80c0c03c400d5a803100d0920910086511301107510645014070b000715905a4001003150004046041d0f00c1d46c46d86401a081d10000c2c1c0c0d641c1180040c040007840648000c00d4107480c1d1210800075007050506150007414241c107130914241410000c5800c080603070f6044021844c258419601c4004240c49506c603124050f54548070100000406102c2d5401001e40c1400c103903400c0c842078554200881c0b82080c10303100c00d404200030000107039522469500088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397971726 1250 397970476 397970491
    0x20703080c07180509060714030105101e022503080306130209100306061101050c070b041a10030c080d1e0c0f060603060e030c0d0518120d0801150c0605 67
    0x1002c4507500d506811140141c0010000304a494804102c0000e0b0f05004c216070042c42030400400b82c0a0915606000b4881409014428400c440061081c0341c400c4102e1000d5508034142c2002c5a843c0c880069070f204070080d480c0c102440c074100c803000c40c003c64000c3d03017048a600141450454999000f00b000c4108102c0c128070343d1a40c28060280b49a4820703500310a0310070f140d20002000e605010006009500c840e05a40590b0304250521000d9841070f412211300d03c2e0003106c1c030320305600c45161140559821806541c1d01d2034000c2c003406440440ba44241d000c4074840c401a8010681e201c0340300351500c0d0145030684c046401a10300e558030014000711514510001c0c5040358083c10f0300d0ba1610051000170a0658080d039951505004101e003e100700e115494261000b1800c0c800351036081a80d82050500040c10010081043d20362540c882442800d80302005200204031840078101c2c66032052812500d10000d034020000007181e07034088580717000790012590381c0000e120494071a000503010181c000b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397972976 1250 397971726 397971733
    0x321020c090705090402070b06130207110405040606030503130819021810080709020310060503040b010332060910060b0a0c0804241107060e0f0f0301020c032107020703080c 76
    0x30300b815034030381c4021f01c1c12500c04c6601010381c0c1008824044003a103c0140b080c000d42c410007888002c905c0b10500100c80c5c1400301c401107500d03030361850000058209688002c00d10700c0041805100b6a9400190300d00307a803d00030803103a0400040c102c81001110800c0302a400c5039082c168005503100c4650780d03c0e4042c9003000f01e1100541c0c1d41c0b1b880c92420405910151100350302005100d10a40b9181200300284180e00c2d015065081c41d0711501d040c101c040c0300050200c80840f14076040000203a1a80c1804183d220410203210011201f00e0384034002101c0e000c806004466661200b8652031145800f540e410500c8142080710690094a401c1d0140e041540e12000c00d0000160300184440c0e9400c160501042c001c1e407081c1074080180012100001b00c03509a001030b4801d02400d58084c9401400e15001c035010354544c4e4050000c640035010706100325030075500001d484400e08100100030700390503070040c1401040d812000c01c6060340c81010754004006070024802040400e81c03e0002d00542c600d104140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397974226 1250 397972976 397972987
    0xb01032009182410090608040501180809040b0907090911090406031a070201140703020a0c020a030c050f0a030b04030e031207051501090902010c021210050c040321020c090705 77
    0x8403010b0340d01220851503009030f202040000055181020160b0041a59190300145035400c01030102c2410b401010104111000001c0078003009403c203000100b10401c5010b000c0209041c441d80f01e034400c03080d40340914101003038060b480c00c01500d668482c05450703a401004c42d040071030150140041d454104940881440308a086980310b1240740011446000315490f4100142030569220000914800c00d5924059003030311071496031428141d002e100b03490010f036654081c600079207020a5160340170b50171a0b5000c2c004801c05c89580410401c1c1d41040b0f965844464000080007000d00250100078404500240450002401500c96144c80d880040594002001050303224034590004042035896a0140159032907500104040034013502800342e050000a9560300083d080b809400c000034003802103443d00c070320040000c0c80203c128540113030060005040200385481c003038000d400207440d0020889040c44185820b818203812110301d9801038007042040104100411100800040601404120703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397975476 1250 397974226 397974259
    0x1103071106030709030503030c300417070602130303020f070f031704031703100f0302180a020c010603140f210307021c11010c05031905060402041505030106030b01032009 75
    0x1642c0304000d180609c3c5c0d100c0b81441d80540300c00500b00b045c420000600d00008040070901070050764400d40141000c50156501c0000c80131501c00c482025108501c082075070128460005000011203009600319858140102c900c01d84508440c41a805a101c40c00750402c0010201c01b40c00c040f183c4003248590034079070b030303500c0f0505107200c1c1c81030710388106600101f00400c400b8030018440c00b5154481c001200c0c642541d0100e111400703800302516510381a0300008500080940403107806581d000000d112240c3c0d41d00e4480380034908001c542c9541e0040b0100da91318403000244600341d43c44a140b0034020b08000c01100e0a80d43d00103800d80046020700000003034903e105051035040e0b1011a900d4041c40280c0f10321140c01c440c066589281004002c0050040b8840c55542901c0d22846450b00043c3c141c6502c800540203108a5100d011080d500350b00c04045190040c0240d412203443e92405d0103500c03416001101103500c011025601819a244405007111030f00018008400c40035024400c0001d1808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397976726 1250 397975476 397975483
    0xa2a111c020d180308160c0915090b190b090a0e130201050d06080a0c0503150601020d1101060e041a01060212041527050f12030a0c030c0804060e0111030711060307090305 75
    0xf100c021b8802c1c11525403000704090307814a40014115135500300700c9161380d4011031454035203500c25964115103c0d400c601481e541e0540d06c84072055004810307000103644001500041e004101d01604c034036022440040e200c00300201c0c86111b140700d1142208075440d140c6c01540d0941052140c1c0c038109035204008544d14000700940b2200600842c244a1820b02d00000c00d850f1031105002105805003400c00c1c482903076000110f00c080490142401841c503100750440307078014400c0d580150101d80508060000b8450240c1d07806110a4200c15011004e030780b12001a03030b40f080e00c1407110541c13140812081103c0a5041c00b08040d011013450084000c42e8401113000c00c1c0d4820408004819801c40b808000c00e182c003107400703c0f1400c0281c0d824401010705401c10b940301d0150341010006d200400c4441b2007018030925000e0480c941c011032044d02c40d0340341d03c00100210400340c4e01c10302180e2415508101c0e04030000a03079000c00c0d448103c0c81d00e414015814050384e034201030111340502110705008070000c3c00a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397977976 1250 397976726 397976737
    0x706030b19060804082b18240e030d15051f03020a360518041202070b0a02030433030e0313060302091003050603060a2a111c020d180308 60
    0x2045001e1130344407810100100c511800754030707c454100850f0100090314030400e481c08a0703501040280141a122400703c0901070b8179042c181540800188000c450b0303d19400220800700c0c4039407010b14191110240400700c140740174240080011040c0903030129202c0c2e0014241c580361460040070040d20620307446400c606083e660712541418406800010f5030104101009000071203e03c1441074400c15900c400b04000340010f0070803015205001e5445008208203401441d0a680b42c9a445c0748912000391a50001c0c022084a412020b400310400704601c02d00400c80040d0f00f200400c58a61514160020005241e107030406000900045d0000b40d0390324000e0f8000d00c030941780540e0782c201610820030750001c44000b0720185884e00341401020344000a125600501400c4000380c4002c1030b454001c01c4591a42c0c19105117545440029102603112803010031031500402103800b5001068442000101800005070040c1c1c40b00714a540403038840c40082945c2104409041160340d144e480f0811543d100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397979226 1250 397977976 397978027
    0x2100c0c03030f05150f03030903030301120b0106020d0e10021509070303030e07270605060f07050f0c0f190902040902190906050415031d0706030b1906080408 70
    0x40d0092905040e058010021103100b00c1d00c04014030b01e0400301c141c46110856007090701071040710044503c1c90b182041100c0300c808000702203945a6960300181d4180b1103180c0411540000d482000040741d50001400031589603042e11480a800000c03001d100301484080040d90444c41141c15020001e160410010300400c0b0142c090480207095080190036500f6220030121580d000b5107003004030351600b0000150841612a0000445a0a10b001d501400103a001507131f1001e800105001341c00794a80041c100c0a10440665070340180302403100b901c681181500c2da4001841c502180c4a91404c21941a03441c2d070a4101c9109803a100c2032513078100d0b001508445000303640021000c00d2a1740c40d07200508070341c0245c50440c410038104400100700340101d2050810a000c1d04c201e07510264040c3c2c000c01c1c2d04c51a40d80001d2807005404d1322071355490001c0c0c42040040b0345042c188030b615043c5040103051201818140c420105d04e041012a11404002d00540d03640105001c811000c903d040040700080d5407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397980476 1250 397979226 397979237
    0x5090105160c15031514060c030f03160905041419090605040c091803050d1a030a050d0323160215011401140c0615150c0a060b0406050105030a0c02100c 67
    0x394600207003c946040c101d04a68030711260041144d41102c400f5011b20a0045e03428680f81c4116108c070707900e076016521800020000c0130082140c0c05403c10480703103420400e9900c03940926514814041158146441e00f98080032020000da144036102000c4820302e003000070b001400a81303e0321383e14200c074000e43e402c441703032481c60104000c008158000c0880c0c0c4460740d10490301184c050303580900b45105280d00d52660301e8907514480f025003e2144045c98041018054910f201494585151101c095940e2a0080703860503681008030072804030803800c007503201902c0c0c00700d40e201c0b0f0040c40480003440d00500110b00c5005280f10040c82410000341c028030b501014401401d86660000d41628140804011150000c0c40542c10b140c500185280d0071070b904000c41440b4100b004041000c082c2000320407502300100140d0b20586000014460410342e000d004104142c003240002c11003500d15500c80c0300d000960900c0491076004080d130001c80700405900403620f2100c031205902e8162003060519201058 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397981726 1250 397980476 397980509
    0xc0e030312010f050303090102100911090f071d0a0b070512070b040b06061317120f0d06090c140d020d0f0606110607020d140d050a0b030d0306030305090105160c 71
    0xd140400e03c041c1038110095402c09804000003540d07041c880090812503621059500240140024241d401000107070003d00c451600c52080d030849102920a9400108000c01141000c5165031441d0402000148401c0c01c0382d25020303148130300e41c2180c1c0c41910b00e4042d2000d13860034070030f01000901005100b00307200d034001d191904202d140c031000200402c0c0602c2c0c0401940e40d844918406410580f1180e0040404c07014100d4005441c14200e070305104a191400241d074001048140042d1480c030342c64500900201c0d0f10b511704941070b40d02d0900324402141000c90040c0c41c0c042c1a0010300990141c2c180c00509160308000c41e082540c1c2d0009104403400c1d600d500c10b10120382d10404901800d48000f00914050030403810013965240074215400400c1101d0311000002e4100c0f404880c4051000c0d0024416400e0184100c03005080e408000c510034402c821080800354085d000e61403c517501034a849081100c944010340b81039000000c450010000f4030004000100d0201c8954046d01e0300080051020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397982976 1250 397981726 397981739
    0xf120a0e0a2601110d0f09061d011a03060c0f0c100501210b0c0c0109050105101d0702030910030f0207030e090a020412080903010212040312050703060b0d0c0e03031201 74
    0x40610780080e00302e590421a403480c0100d40c00c1c040764140e50100100060041204854000904441c04018072150500a11030b03100c0700c90418005128074440c008018004100404016040e1300f4008160160803410004509050b0940540030403040115010314081450100c03505107001084c50280050307488006024010851204581ca0000c40703845000b000c5490302c5194114030000d0a1091880b4005a010140b6000390094002c055102c0e00a01660038a88a200661011801011800c010110503110900c441c45001405041203402075403420340c8002c1400080000350043d45c0a140d10740d5268030901d26140300905249009039242d51502c1c00410400159190162814010314010f000038042c0405140c411600c00c0d6210398107540d03440380b8401007806030003171507001541440c08604110606401019000440c198150200415610150300b5011076001e4041c81d103030f43c0024015190640a1a8840300050071182880780030b1b04000ba0000346103a100c180318104118207900100a0b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397984226 1250 397982976 397983029
    0x21b06071d040c0203090d020402160503070b0a02090105040918172a0c0105070f0804030c0312051206090a060906090606110a1101120b1c0506090f120a0e0a 69
    0x40344011a002e0129041c0000025a46e0282109540c82820001c511004540e56541119801d900907901162400182c1c10100c1d101d42203040d0640710407814000007261840c41d0300c2120b00c20a416103480b82841e0821004a0082c0b120751030714070042a024000030702044250500a2140c0d00c000b80550f5610341d24152244140b0700215800681c0704922182406500301107200420801e0a1800d1500c503a998100080741e14220344015290610014010041c070412a100e80186e03800b0b10130002c0c07002c0700c0000844051040740810b00c100c0c00080f0200c1c1d16480c000030460781160000c0c01c08141e840d00e640b04d0000b102c6065100d10341d41c65654070100561a0441c85074a40005204041c01112070307607450710f41c414808042c865040003661042e4441e40b0000382e200c1c1012400180801c45002d45489044d00d44504200f0141d46a204000015200e10400500d080b0041f103140040c081444903a038039a501c58020762015010701840740040000c42d20340750002c41c010105140004107000c80389000028 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397985476 1250 397984226 397984277
    0x40627060b01141806160308040308130203030406050a0315060806010e0303030c09010c0311030c0109020406080c01020d0311090d12260705071104090b0a0609060e040204021b0607 79
    0x10300a80e03c01074030072003c90030107807404541079898010920307181d031001510a02c242d80480c402c9a40e134071a21010715500032080e80c030852094171044010b890303011540c0c1100e158030300000c5d8154000c00003030150604c9a07020f0003400b11142004110f03001611b407210204001500084001101d4208010342c81d030b401200311000c3c10b010b9020f1032450034150000c80840c8a0070150307c4c180443c541d51002014400e503442007031140075070207998030340b034104290301d002c1c010b6800103901c0380b414140c010500100c04140f035440c414050b0020007090a50440a50203014004043c40d207c982c02d0145481d1601c540c42c0072562584200107901005802c003002a08442c0b520340080c0a00668007603086d0b804840030691074000f1800d0506d561100d40e81d10b00b81105070704118615401c141015018001c005505610134068044408107110150301d682e2820221036031703440f0700f600b000459408940035091580c020b00d0b10f1700e501100c7c52880c400c020001d92034500191442000125001d03244000003121005116 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397986726 1250 397985476 397985479
    0x319050606090102030d05040809130c1e0e04050a06050607080306040c020f0a030806030a06021c0c031104050103020d11031603060909210e28050f0d0803040627060b 73
    0x142010b4602d070000396203005004070580751030350f240080b4042c0034402c825180b10803030050082c0d40c190741101c01500036000b1800000c1c00f2130502012120b00511701a980040701c2e000c1d0707644200c8103030904100406841c1c0548041c0e001541c910010400ea156980100040d0307008400302640d07410700900303000440d80c1c850786a01c11900407190b0300c00208030210f400c1e0020303a050b244c6403e00da00c80d07800007402d1003e800c60091400b41300203500402003034021919080c080c2170720010400482c1006043d0252a01e0440742c800100040105100644c0240e01030802c0080e50032000a4000c969185402d4940c02902d0070380c014455003160307400e03180e454042c0c00050121140c050000c0d084695030341000d41c00003d8103682d8950403000d15031910384030340503030744200300010100d60580c0f44500c3c0b00c0c6850400d400c10042c2c0c8000218022807241003520985000b841b02406841081556803078500007a04054021125140c441d0310280c2200340c2c00504d110102c8010484204000083c5030902c00c4451480034507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397987976 1250 397986726 397986739
    0x501090b040b0a0c050c10030903080a0c080703020c0703120c26030c032a0406120608030f07020a031b0513050708040206030901060305030c010f11131806030803190506 74
    0x511621220b0300c1540c841c48100e00301251030320311078030b0110300704040c0c406400e41081034149002c0d6201e0340b40d00300d190242d019403502034003a01d43c1445032054aa9480790500402c5170341000c64079842c4280e000b0045e00788251300380e51460361039a94800c00c075042c184404d8006406844684c080c84511340c28400d41c0340020a1f118409010b441c14400140002064000140001700c00549114044080000f4640d611560326421f016408280c40c1140c115000d020005809580c3c10b49100c81207120752026180d4500095041200f0803030214000ea210503000ca03041940a640000050080d4041c420340880d081140a500c0c2e082006000c12400b09030511480d0a082c04140502582c00414070b90300702e40c0550710203903650348044002d40508016800145a0300c000214800c8042040d4004410780d8041c00c0705028141c91405d03a402d0500031080081500e82d1105010411380919001c1540c403000104c00214110b03980c0c0e152171021b80c00858100800052070b4400c1303c1e08010300e208191f0f1241044484c3c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397989226 1250 397987976 397987979
    0x804050306062e0e09090109112707110d020c04140c0d090c05060f0d150303090b0307031805031b16030602090d080a1805032a0d0c0f0501090b04 64
    0xc000b0b05840d0070340c12000190030107201d0306030f24469050148500c1000c0c05510107401d100380040e00070b100d00701050351820454441400c5616019880d110410340107614015061022095074141d414040c20401c1030200d5005030381003407207050010003a001c1c1d80b500070302040c5444a06210075070300101c44103d4180801410810014003810944045e60006000060719070410f192500e0b01c030a05801041c1d101c800403840f400100300c644010300002944031010300002914070500410708201c1d0000401140d107000f020b00c462494140503581c060000e01d03000c1812301e48121241c400c942080002d0f40d807500000780c3c901240e40b00084c0480c514110200412420041e0421101c03002c00398000288115000a0043c440e56035a0351502100742e0042031a0b42c0c0da07506c880300500348107a0b05100200010b24140e00003058500801c084030201c11800304440801000049c0c4440711a080404c140c1c02010082c0c2000450300c102502c4001d098260400d0340c040307003400009400180315a0106000d40000c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397990476 1250 397989226 397989259
    0x11502060c0a051911060c09040605040c08010e070c020d0822060504180e0105010f0509070f0c060f0e121308010912030902012304090e0604050a170c0604080405030606 74
    0x103c51307102012214800da100560754080340c0c01001c0c0c01d40740131648103800030301000c006590001c09003500c1c200c40130014150b5407020302040d17804c800507403400306102e0001001000340000000b9030040e400d291030500c400003640040c000300c900c40007e85000d030b40415503004480841074101100c03010100071401e07032847e100c1c00402500c08c50140c0d02003030b031608855201c24917082c5c004140d0020b60780c1c0244102d603121810084900203e1081c50303c2580540041003042e8040c00000614507030b29aa4094140000c0d100e11002e080754000b1881c90680d00c100c9910000018041c900e4a0b001080702d0594403026540f107040c1c4043c864200103e182d240280c14400200b13181401d46110034103060100b120143c90006031480d111070100d801c081400300c4203241c2c0405c0a04010026690300e0201008415040c00c8501d07519141214004c2007a403002d4910004105c1400b61304c8490812012940e152000b902c1c41c0a00303101081c0d034212806900460f0510141c0b605026075a40a681613500030424144a83c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397991726 1250 397990476 397990487
    0x4020906151b0a050706090305030702010e060909180f0c2d0904060219050a1710170109140a0f12030b1c110f0f2106011502060c0a 58
    0x1400c240c410030300c044400741d100200c08142c81400005a042219002403900010703200d1000d00b4080f20540941040401c080380190740080603250000011030078488c1d143e005591482ca018401c135448201480410f05035070b00c81601c030748507080400340c00c4042003030140c4c003a144c4002a148040b03583c01c0003280e8460380d200c07440100c2d44008000724805030a450004020444503a115140d60052016800c00052000640080c40c0100c05011074070b6070300e20000401c0300c2d5401490615400a1540c9100d13803da0070041d2038050f0008800150f1804191f520125052407840059510350640d4450301c10b5414004030345501c951424041c0040d00c421400c658540c41c40c200e40a10003018181d0100000640e030740f02e54080e030050078001c3c1201000b02d001801000d031240700058121059903410619004a0800240e020b20840014020b44203600188040044580c075102c4503c0c0702c03005964070081c124030f080000a0080c0b90303007a41c002005a03c0d80c0c00a041000c000c0c000250036408120190030f66a100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397992976 1250 397991726 397991731
    0xa11010516080624030f0c090a06030c020c0307090e0106080c01140706090c060804060b030c060904110d060905090d0c0519140105040606090e1911130c020304090b0603040209 77
    0x207190200041c3e591800103009080010f000301410507480080c07203102e045440081d03018480007089110b1030741ea0350761829403610862651a4024522072002c2100a009070448942c440d4a4015510050891400b00c0d141811941c403d20b1056280c1d20200080c4000703225001c068030b258009071141c03c00000c0043d000c0365868409a08807000080c1c020140240d543c8944070443c1e0200034580e0720795070340b4001070038a04195003c1ea8100e260098020359490300094130040000041c0c40345003400400800c0100a20328151b00e204035010030801d0801c040514801d0101a00369100002442d00b440340034240384c820034810141c14820035001070350110700006940e01000340130b8022045031008034508400441d80b240206801c0c2d6081070705000800c5456004a001e03075241001c108090780c54500156615200c2401d1081c1d08000611a1404030310a02485d00c1e041d503002d05110b4070302132031041c181d0032500c00c10740030001a000460244580391203401035001090046a40342d04506160300040c1105001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397994226 1250 397992976 397993021
    0x3020d24060e15090a03060504060510090506032d01060305031201081f0209010e031005061203040e0c0a0504120b010905060603010b0d0902010216030c0e011215020a0909110a110105 80
    0x319070b052203036850641145c069036200005106d2030620386003c4010f08011340344d01c0100d8415090100f40203a0505c510703031080c00d0050090144440b44050f000c00e103071180d50b850350707190001c0950030314400c424016103004502c50001140c0d540c1e41c1103640d1840780d13010703001030741590811980202400820b0b00105900c407100c4d200165219210700042e00d086407880c582d00d41600035492181d080c0754495100503c5500c0945040000020300c0802d80c0d00c0c0c1c820360250810b4841e4040100d80041c0c079a0700684040e01d41800d2452500d81c54058407480f007052400116002c031040401480303207a440780585a08501d041e94120f04550400403a46600c1c0a6902542401d660b1030300d080003035a100704039581d5052100c09207140055100e08200c401c242031805892040e01c11140002582c0c0c2c600940400081c1d040fa03c0b001c520a80b10000d800a9030040209a08008184402061751503142c1300d4114203120180c07407250703100403100000d04003041112020285034075000810060034044030384035152409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397995476 1250 397994226 397994269
    0x7020f0601090f0f0c11100b1003020903011820010201060f1e17100e0d090614040306060e160c080307030f0204030f05060106180501021c03020d24060e 67
    0x81030840004010342401d401c60704d4184000304c1d60860300f004d4504804e0045e05c00340c134130060080081c03100f80c0d000c0364005900401d0303003000100014483d034054204d41070300031300201d00c4844034203141e54070340700180055480801c0344071344402044010305089081c0c0c10030300007404568a081e0740c03080003803018440c03103c9130402c03038601e030446403031119402d4054003a070b00d00b803800c00504002440e91040b90040500a480c507188005808060003d0309008003070311940d0b42c8000d2800c02c0f40c1160303080f00040f070184020f0018040440082c5643c044c00015001802d5a1039941c0340130b05c240d001300c1c500f03001d442081c030070742c9281034011840310021030b907012081e03080102d01d4954020580c0004e1186500140c0b04036007400c0800200100425600d0403030342c0c2e42e80d5449004000d550a4840e410303147c4142d5026034041000c0741c4500b90351030500148811942401814082c0f600c03024410303100b22840d800d1202084c074072101040584141c103440078003000e140c20070281071510049410103409511030041850f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397996726 1250 397995476 397995491
    0x6120613020618190f06030207080d1d0a080d06050d020a03061e021b07060503090d0c1103060405010605120f03040e040609120e0a1a120c09100c050607020f060109 72
    0x9216089100b0070014080224400d8000058401d1130420b00481001d1a200000001c0c224801c2c003e44018a0b084080c40b8a4108089181c03401480030301300030f401000085150b2042e0316028800f204401e80034102040d990341185000300300f110300503001940b0901c2080e20000240c2c030798040d080c0941e544600000764481002004029401b86e0b40e0002c0c0341d2500003c3c080c5107880074444c10100384015034048809050f15200180d425010880b524203c3d507005844d0b001e191803149504240303203030107140d04400e01c0500c40e0101e41030400031102596140c0d100d43d0100100d090180c4040c204044c0340000e488402e034800c03245902c13841756104130195544290701080074017038150300a03242e40b2303400150807521404642c800340c040614100c1452190502400000e02260405100342c020800071060f18600031001440b07440b00c2c000a810003808850600204009171074100029402c942a80c036440501c02c2140740092074141d00819850442d000084503103023828002a00c81d0642d2010800490300780c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397997976 1250 397996726 397996747
    0x5130909031e11190b060904031205060406032310020a0e090613020a111908030a020a0e0301020307091a0711060a020f03120103060c0305070e010c02060903030403050105061206130206 81
    0x83c0c1a16803048903034042c0d07648841250507148290360f6018071a00402415039034800030409072040844014002c141100302440b0840c460743c0c031140e40008010800154140c5a44442d24040100f4240140280461100102d401c10801604079040b030303c144107501d04840780b03400505510741900614010242c182c0401d01d10350302c03000303515001c003014482191203043c0214000d101c41501a80c0e00c4150044181c2c0003d007000d040c011440c0709805c40c10051031511120581c000940c40307064180100f0100415900c03240d0303800c0c0002e60003408144c0e40c24856500306405038801114103080742c042e050041140310300056540c0c00d8150703910300071208661142ca5083c016400c241e6940301c2c00ca403600000034100b10446001040605882c000c0004101d11420040290220741081d0364440103d0403500324040380d5842030086003041803000d0442401c202040e8046491500b142d0422503803079450750200704003405e025078480180000b9900901207400c0c0a04101e01d440e0350009d01078022200090f881d801c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397999226 1250 397997976 397997987
    0x509062a0d050f010302010809070608070509010e0a090608012409200c07030b0f040b060402030907051804140312010e040f02091003051b1e0a1505130909031e 70
    0x700c03800050a22092401050b2180450b90900049020464842c0820141d180000340201030301c1c0191100f101c41d455040c0f00b5140c83d08403282c0309040147d4801da00080b512009402001041050030205401c0d01b05484c0c0c03400d40301a98461102940c03000c29216071040c101b40810200d54401d1000680180e010000440c81c610781001900c0c508400a0103202e4140c00180f950f089030300034209802252600000c41c40300b6442620023074101d81c1200c0101d000e03450140d0045404c40c0e864002c41d4501c41d5581d0100c2c00059480301078084200c100c0081209005031505490203018080d03000d98a4110f45a410107407940c0107000751074000520000050070011306810350950140c00030030a550354980002061100d51301400116090b006014084042d2a0808100040008007d054007124a00300301c0120800c0745030b440c7d841e80801040000520a00005252180c501e410b40e2943e0b901c410504c651041b070b0b00c443e880780301c0041c5810a840040303507102c0404003024000382080e10222003141011200c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398000476 1250 397999226 397999237
    0x70302030d0b0d140a060f090f030e0a050a0608010e060409050706080a020403240b0301021809040f0b071d030304060c030503130803090a050106091803080403022505040509062a 78
    0xa04c007000c0c01800d070882d00040c8500010340f00c0d0b5814010030f411000c3e1607050300c91424006110001074001080028002d501503407000f0b4000d00016000d0341d03660001020610305a100d200447d14a030014805020084456a400304044d00d080c45100318641d5403a40d03d020900c42e241c1000310850100b0100c011940440e401190407035803000050003080000000c42c282c0d081c0d03449071103180c80881d214a04040c000c0c0e9401d07460002003040e00900300e00c1404111100100704136a02d04200c06208001070071290f005000b0343e00e0f0b941701c81410403020700501c46000f202000500c00da10500042040c41d80c0922050718180e41860305540781d03180d08003080041c560101004020f007902000b000401000041c90a548502490013840901d580d83c01160895003010a14007120800c0303d51038022030300603511960881e20070304c11591a8074940d2042195030076000c4054038003038030344441045075150a0103826000016a000b134051030030142a00440940700e11880020b024103140c80b0f60161541ca0151075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398001726 1250 398000476 398000483
    0x1507050703150905120408160e0105120307060c030608160b0a0c1a0405034512010504080702040f020307020a2901141021180812010812070302030d0b0d 67
    0x10741c564105024005240c02a008151003423264040c0381004104050880049800f55032030451a43d08003804d00c00098650004542c262004101c1040002d9407031045125950059a0001e4200d0918108a05203030501c912000150a644018400100c0120850b22001501c1c00d080d41c09101500e8141c0f202900107004c4961134128070104014007501000502002c0c100005140c044240320386c0d20002c10003142d801741c00308294144a038980b0310041d40c41d160790780e600034204c09205160040013030071744804a90440b884140030401e0021800d141c003400d0b0860407886000d41c02c41c40c0c412002540c440102501801c000110394040b003c3d54020b0101c110705540c160214602e542e118040419613940d0302c417200c1d00801407064101c040f24032420f0985001140d015075003c1000000541c1d001038180503d5004202009402c10000114403100030800c201800a40030102c2d07260411032400c100c1c501c4100d80089504200d2000001d03030110842c1c401090f02e400002c1c0c0c0303e0f01c685c04910b91903040c15008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398002976 1250 398001726 398001733
    0x309121106070605090d02010c091505040b0c01060303021c02062e0e04110901030b042414040309061b0b101203112103010902070f170403021507050703150905 70
    0x54284890b0b42c00040c130a0b615002190b446d841c042074220b0880d00703000310340f43c002071081c1d00c03e00c075600b84140550507901e41d62409a040649603901d00b0328079442202d410540360741d80d8904008050301031202249078a090580a0122241d40d800692280001032202070320316072040881c41c0d0002100d01c0d211003409251205010a070310358014a4000c0d00a44082c1c48000c10082503030214a81020814140c17540700d0000030060301c8591300c0d80403207984190300c6440c40d8140d0300d691828151078031850450001104030003110307007030a0502501c0d04c1d525410850400000800c072016040040b40d07208a1507501880003030207952201c4100307888181d243c00000d902440880300c1c03014503600000038007041e000001030710b45110701c40e074600544001e0050500c003004000e100400084040343c1c090300100b8050103c55001c0c1440d90344120030b0032115200b56031003900208041c001d504102240c1d0140c098101c9425240c076001d5141d0301c0d615410351100a041840a044110703040b80c06401c40e807107082d441000c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398004226 1250 398002976 398002987
    0xf0204081b0306161805040f090209060a050f0f04150806161b021c02090c0408070b0c100e070b370f03020904091b03030e0d0309121106 60
    0x403140c4544600a980a4a0300841200c080e01d140c00304034140244030165a04410700356000d01920311203180b0204410641c14420700291540b114001c6d041580140000007070b8441c00c034410026118400703041603001c0c0700c518200384501d40f10480b0071003c10b00126a40c00c1010901000600900410600c000888280d90400290a800095000d000b602c40e4000038080010078401142d200c4648a000115685405031000240c244078000341d61034140c070441582c01d81ca0540100321500d0040e9082c0c0505000007800b00302401d000c0c0400d2000c1c10b080d00446e481c1404800c46103590b01508095680c41641d2070000307081600e020403440000380f0b088048980c403003000c10121012000310130000402c04031342281d100755025201a801115110540301e4840018182c10128025007103050155002980c614040022990740e0f010024100114004c11040ca41940f60052011000e5121580642c02c45588440002d4126a0440c05d031181c450301001c1e1914242064803098079660000f0350040000180d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398005476 1250 398004226 398004239
    0x30207030c030305100b19030e151f080d110c030111090402090301060503070b0304060506013006090f0f150506040b07050a0f0501020706200d183003020721030f0204 73
    0x442c042024000c8e142008440c0d82070901a131203946c1e2007490140841c3c01c0d80020406022005502c0d04404143c1000507000d89038000d040c503000d40d094039940882c01425054111840030014070a030000706070300a0000c5d0100102004044c06141900e921541c3c0204d441ba83c1500c1c2541300000801006080300c003025520a12080d440c1d00503102610401d00b800001007195010f8140c074861241000100f000b51030404090310202d800740b0300c9040101d610f5003000912000a03000e02001d06404141c00101010403040e050116600c040d400421404080b07010842540c0d20005d4404450401110581c1d4109510b88203091140844000705080c0102041d9404d100d815030140a400b486507104000541ca0300c80c000c00070402140811111020401004016003102d401c00c0c000c400600e0340342a060301c0590703220b02d1101034008141040500000c41d449101100900a00f43d070707885410218500b40203921407151501e0b0000c10010951601200c80349101e10940c0844402c52910310115111501ca51 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398006726 1250 398005476 398005507
    0x1323060a21020909060d03120c1710050f01050c121c1428271b0605040e130c03080c071d040f02031e010b10030207030c030305100b 58
    0x561079881c0118410294940902e20894812000083c010700403544d407001000100c03801054200e081044105042e009040c0ca0700600140c800c46407902800e01c03048504070801401c0084c50480c0303005500304104003030744402c0c2c500b01d042142840c10540d030b80c074941c0015261100d03044065041034400075200c10500c0c041c42c14001c00950181d1300380300183c2c0d01c1d501c804e96070f02c0c00d407111001141e1880c5800408513601000b03892101580c035000c1055589114412025540400c4616107000d003010360104000d0b00b1501078044040d02c2000820060900030020a00c0c0940d00a0300002e01c155404145181c804c3c43c5010324159100102010031a00c0e4500024541c102240700e00c1d46108030580442e480400c45400343c2d080c0c0c00405044040d5440d9240c0034030000609034203a80500900d40c4d0402540300404058400462910011804082000521a004100900400c20103105000c002d0000c0da105910306050740e00740c640400e01d6215962162190300046d40700c80031000f0006403400000c136600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398007976 1250 398006726 398006747
    0x80304050f030303090d121413020f150304020904030509280803040b160204021b06011401090803030a1104090c020a0b01090e06180c0405011d010503031323060a 71
    0x161107251440700c0384814140d882c001030326022419007141d5040d48040e0710426440c952140c0d248804a02c014900107105508103090380c400392890815a5102c003075041005c450100d0b140d040d103200a4489181b40c01004034000a08020310900f44003020806151003901541c4140e40000e00800031030800d02044e000c520706079414a00d10207604000000d00b10f202100355000c40d030b100401c181c035103810300003c008100998101243e0050b400d000750b00280040d40740c48030b1071071000402000b055041c1100c44080f564605110341c108041140305000400300030013582d03008a034140c0049515204220400040d001799004000b10702d02d051841c003081035000591040300d034050540010141d0301e801400040d05c030303210f022003800d5004d0004100400c41903149441600800ea05071a81e40c8005d90025090703441c01c0c0e001d0401c940740644080702c00446581c4450040c88210003d62400210030504012010284103080812050320760320358000d140b02c0034120381e1020080020340e503500814000343c80d94020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398009226 1250 398007976 398007979
    0xb070809011a0109121a070810090c0f12091506030c12020a03080319110403050d030c0912110301060801150b16022701080c1503101406040f08030405 66
    0x200b0b8900000300e20141e00009000c030741030b0b49100c42c0c1400d00c43c00c45205040710a084543c1c0702428240f50700c1840c1a8082401040c03e6030303030f512050521030001040b842c81d0360015001249001c00c101030458003e0040740d1003076900e0402e412036003903800380d034402005004070252907200c00713005041c140c0f03055a011000f03a0340b0422040c2d00541e02c1d840520400a44200c0c029007060319507005201041654014503071100210309560020418905442d054400f80c00741441c1102020900344200001881242c0c07031800c0034a010499400b1040e001008500d8a00c2400035145840340400144680000504001c5e14041c0080c010555a10400ca008000d120038400700240e1441c4081240c248640032110102224180c4c099100215020806d24030b01d40104882800141c042d0b1060b00c0c5907a042d000e00921200010307092120500c2c040c00140141006c1003080c1520401c1004100c03000350045038140c40c0b00c600011403800060022070a94465504058036084c0c1d00d150002e40884008010000c1c0c1c3d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398010476 1250 398009226 398009231
    0x7050106180e2425020109210804230a080a08010f08100f0e010e0a031d0319020621010602102309010609140103020910180c0c0b07080901 61
    0x20028110340ca501c110011888065030243c000120f4110003c10350b600625031360030802c000198202d104081809640159016135113480042d018069201c405882a440162815407040d0384040d009100300801440104038070851100001c003001c0101001c6909181001113584107401c0b41000c2030141c020841c0000016040d00011581e201141c401e28103d40d407860082a60b0320803184107002419086c080000841da0302e0240343c01d010030074055940d4080d108009014001e90bd814011301c503004003501011a04926031401c442611700103234000c0a80c0051f040400c1ea0800740c80020550312441c0b01c601c1c5e00810042c40301c7c104100c02c1184a0403030b600c64084401c181080c00c80c00c020b5800e504811104060303d82100e401c482029403403140d00580c00c600000750140c607100300e14201c0d4046500f018084070795200620441c100b800040d90484020403074003660350301d410813030140240880e661104490f19440c5500c0b1080c0a494940002ea034071822070107440c5441c91004101b510204da070000b8039030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398011726 1250 398010476 398010491
    0x32a03030703032403171612050a020f030301050a050d0606090501080d0801051e010c0f0c0b0901030e0a0c05010c03030609061205010b0d0203071401140c0a0312020301051806060705010618 83
    0x115204c0102c41142e0f4810362400b060301280100800076007101c03c50402100002c51100001802844001032540b07164407920340f513401e1031900901d8083c02042c880140e40c000c00051181d0390364212030714100e41c0c040390b03000000c107000d240c100007524165100800050500001103031450020440d0b44449106a4850301680c6e2f840c020018a01500046251803a04a1040440c03a5114100000c08280135007804400044580d90702484280140c0c8500f4401b140811410590343e40b60050340581e00c440801012040155103901e44101300510070b090601140703440c2e103c10540a5080b00c801440c502d803082001d82d5032070041c02c01c000e00035142106c0651074011018064900b03160302d42981c0f900500289491420034401c000800f140c80021410700ca1402c00c803010b90788040005140401035130000d0000d40140d0f20b00a40407110544104020500500040c00b49881c3ca100070348240511441c09500d0351501c23008141c2500c43d01201801e00d5080031800700360754175100c0404e200300c10041030411200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398012976 1250 398011726 398011781
    0x30c061303080109092301020408010c0504030203070905220605010501090504140f061804050a0203070f031a040c1e0e1509130809030a0516060905032a0303070303 72
    0x3240103000050208250100502c4048a84d520040c0850310aa68803141c04a140703e400d425885002d2031208240c1d00040c0c03d01c8400d60030700514150548a003040d82c02c2504540c0000d465a00c3e600800940a54400024808001058a0110000c00b502614015904c14206803000d8a0240a2940414080c8900091a0130513100d840c11028444842140039103135450100300521000c1d01d902e900c810428440380250050071100c50045109000a004002952041c982445050350000c5252107105c40c08101180702564100c2c01001c222405100c00d40e41c0e0700d0f282c40900e9035504400c0403d00c02c030007904100f00c0313001640c80a0b0341010307904001580d524003110300840b0482c40340e40e41004a1101060300c00c440140e41c140c484d03105051103070a150b41d400201e4035103500483d06644640c081070542c03013500104000c0f000a000185040e8884a0030203021942d10390b22141c295091801c15101c01c200c403109070341c090f0030421000707003500d5a800c014280100900200340e44804403607018149180407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398014226 1250 398012976 398013001
    0x90703061e14091e04020a09020c010603060b0111190f1202150c0a050d110903120d0f1a0d020a0f0609051e01080f0c0c0706110f0c06030a0e070b0705030c06 69
    0x88160095506181034403500303164480001401c01c0303800c0008180081a40230246c00600a418811000020303424618184102076801c0110528103010700740c22090524580032803500400400310403000d241012500d4040c94121492030013420401c1c0c40c814a080d00b80d80843c039541c580001e104818500e44400a0310441c901c942c80003500401c0c02001080000d003d0740e003004a50300030750568141080c0010700400e003880101d000e404600340001422191600c214440d800d9003d920030745c01c209032204003460441c6140140c00300341c82502c00710faa0900315545c0b1208007025089035802014815a2070750041d00404036400750a1240031060904201e010ba4014090f0110005035550111503e42e00d02c812080c1c01c014002d040c50003010803212422410410091004000765666401105000c014090420401242554540e04800c00c4000c00307903034120559821195a020002d106802d41400c1480c2c074669038414508220082018420303c9008009007420450300d40564541c0d0352442c030319511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398015476 1250 398014226 398014231
    0x5040308031e04080910020f28021e1311070b0c07120e0a060c0804170307061e050a0b030a020613051f080705030f010308071403270d0809090703061e1409 68
    0x10700d60301a41c9e07440080240d14038805118040a4400441e50301940c001c03c80400400300c40504100c004e100441c2a41003020280c00c52094012040200f10001c0c00040f440e44500c0501800134218000460120500c131000c50f200154003107c110580005d40901801040358100043d11811000e000058032a008408082440764030003841e500d03003401c201c1d42641c0d0507a56006d00055100900040300014498443c0021030442807000d03a40c0d80800340d10303507400d8860051200c40c1e41803d1002e41001c0703840009820428690450700c1944414061210030614030140d8421030780b01c00000085401c52200b0603030f07581102c1c41a40c461001c2e5a9044040d00e0034031050b00c0601108082c01c00420110f0f00a401030600ca6101340101a20304820004440c519000f440c02da0803004140c00c4c506d0205d40d1984107400d60340d54140d648400001c17068649048a014620b45035001c1c000410001d64424443e50124018001241015542000c1c1010345c055598150085a038191342d1266000098645042c4862 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398016726 1250 398015476 398015503
    0xf08010207110d05031b03030604050105041e0506010e04090b0f09010209211c030213080d02100e0703051207050706090b0a0309051005070203071703060105040308031e0408091002 79
    0x2c810300e03291000c0c01401c4107000301c00d8549000074080d68040ca45503d100400d5401072000139034a03424050100011104103a020387d00c203c2c503050807014240350880b0038110703070720589800240c42d0355200e005031a001da03001c500c01e41c420b20700300e005010004c0030400d6038000c40c1082d1440145903905a0140d00f02d1052401e6150302044550011404071008140c0c0209601504250754510500f031054010000b0411040c0d000300c0e40200b03854018039144491700004001000017031500c101d00c0703c03029448440c100c00c0060219162000400010820032942c001950b1100c1252b800581420549000340c001d540c0403101401400e0780018528132509920b410b950340c103140d0300e24084a12406800030007040302c003180c0d54024442e0320391920360320b442141c1c49107080e9009581c1c0d4425620b0211220841c0e07141400f2482402c1c030510134507036484416034090340c0d80052055602d45940e0200d50b2004910715041d04e0700e20301c900400c01005074020203070900314000d4884090310306807528103903144c2c0f40c08600c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398017976 1250 398016726 398016743
    0xc02011e02131205190305071208060906010c170a0c080d0b12010b01080a0b01023c031201140607050610030b220206130f0e010323070317160c0f08010207 68
    0x5e40b500e08200c0141c403401d200b414011f141c01c0c05980c13032407140400c0034030a41c04558082c0410155050041c1d0031a8842c4003441e01c04074495280c1c4d15000303c20300c0301e14080d4008d6404102c000d0058010380601010312340101800b5100e103004a901000343c5184802c5a00810048241075003242c814040d5804454050711105141c0e6a0303075001c40002c056000042d41184a081400506800030f00002040754a400018183c00100304001c15150981d83c1c1e102c07022544200941c01207417018401d6681502d0f4607020b50004414046d000800301c0c040c040000d4124001c40d400c0c020f00c8881c106401040b00e10402442e9078568038402c12034415003d422420580c010030711038079401031400200500002d240101245001500c411a800c148009500211418100b4400600a010600740d2a07070a0004030f0b0b10344941c0351000a050358549203c1d10001340100d00300307410b0015041c110001d40c1c0b072281d00104220444080f0707007000381e54090300703108801c0c6440c51000041052030701070084404040e001000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398019226 1250 398017976 398017993
    0xa03030507170405090f010e090d08060607020a2303280204050a11040315241203030605090903071b0b0f031005040203131101050313060c02011e02131205 68
    0x15400390790b000001c03030103004808100206903556400103690140605034140f28480d070602c2c00032580180301424210b6254424107410382d210b607111221030752003070060710100d40307070410703440440c0914820760000c4206004102c205002c01c00d16042ea1001c0c014120111254102c00d600c4a86000442c0404000321413040320107180582880d8000d1a040204081700103060b1916070481701c00c41e041340e08100d424036403001c012300300c030075142c0a0548501507012107214000000301d8030783d06e000315610410070200410010300c0c0070f05000364414001404040d00000143c13518007007454481e88162421241c0d081440440c22200444400e81b0f810385202c0b2448070b04d0851001d01c2d180c1c460704000c2001031503118800e4049006e031501d00103180610409040d1901c3d261803442c055071001860310400d41080801e10802c1000078420303022100042c0c11000005902102000490150104000d41a16015800c400086a2920f9401032008084802002103840c0c0c4603958414074600c005400703806940101d24 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398020476 1250 398019226 398019233
    0xb130e0403020c03010507050706060e0106081602010603050d0816170c09030309040f0b10050c0a02010309110a0305070f12051203090304170a020f04090b0403210f020306040b0a03030507 82
    0x8010350414000e00440b000002d0074400603094410403540300001a90120703d20341046014001c6002520a002d082d50603581000c42c02040800001c1404c1c032820008080169014002c0d4407a070085c64102013520520340c007404001d800c58a041e2091607000c030480c40e9800b005481100c640d549110141340b00000303600e4a10310004070750099104140e06010400c10785000d0743c1c841c0729407140340300200c1011034110b0040c0b0400c100808400005000e0100030003624500c0c08011801c0040203509080009900b0000d05115585401080742d498000d65000c80110602c8400202d0904491500c1e044540396511103004180d810040c4200504580c007000701c1c8107007002c130790003e1a4464042022642401e03a41c002180c44004105410582c0750007440b915019400c0081045548e220151400d00202d0707500c2c4e84031000488010409003c000580321000340181c0400d954100000e444e0707100707001c40100124030b03000a44c01a0707500780c425403409040700602e041c850384140440f601521500c0c1810910b45 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398021582 1106 398020476 398020499
    0xd11190905030d0f14070b07030902030c030a0209131a010603020a0905090c0d090309080a0c08061812030604020d2d051003030c05030904020c0a0c0b13 67
    0x200f0042590380040400071070501500e801c80440b082484140400c0c00f40c00402410300302e1640500c12540d9050f0025400c0038002c0b410381d01259040002c03d1380d00d13450300714000d4105020710001101c60880c0c014542009008400c1c005141a011180c0209020242c20100100381d0100c0c41c1103802d9886030900001d03020a460b81f40080c100280b4880b158080e101010b00801d4407855200201440750760324500402c92001240e0303403403102c0d07d841d083c1c1c0d140c14014000039101d0307400011840c070310307814952a00342c7c0c0c06800303490500c540d85050001035000030701264026800700107201000400748070301080c0c00c440141101c00001864440302c00d00310261810b1290b903082409009100da68070040c4021203a050500707105c0f408007490118214002d105095600600c0400e1402c900d09000c100305003803070b100300c1c0310050294550004155900540490941d800903494050000b20b0108 = true := by decide +kernel

theorem cover : BRFrame.Cov 397841726 398021582 := by
  have h0 := BRFrame.cov_init 397841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 397841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 397841726 ≤ n) (h2 : n < 398021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
