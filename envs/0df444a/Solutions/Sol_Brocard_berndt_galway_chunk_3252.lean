-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:06:55.263577+00:00
-- url     : https://prove2.me/submissions/d1e0a15e-d7f0-4d94-bcde-288ca7801506

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 584712230 ≤ n < 584892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 584713480 1250 584712230 584712241
    0x20109022116030c0e041e0b0a0b030109030806041a10050903060c09091b04090f05010801050c0a0f050f12011203090510021b0a15170714090d0c1a12 66
    0x102e450003c032984800c0c0102e10a18003c5804150302020b44100c603642c800403903142c0100300602c0042c81c254020240300c1820f0a02c0c0c0c0300302c82112400403009010344d04180402c00841d40064000790321440c192404141c0c8485109018148019940500d0340030700e040b1154072010354007030090104508244c00b2111142c0716071b03158043d039025000152782e1010001c000643d19040b5916100200413202e031160b42020740f601c00c0c08080d121100704001140c1d940390010000b6410034010990040328000b9a5440c01ca00881c00610103400049200c050003000103180c1030b02040007040303a0401008000c40a02941c54102c0d0301e0340d4100050040d000038600840c00f042d140741c841c06810440c20190003c1250310240c50004d004c1d08440542154008903140000514811030088150a0160342d0f584524031460303040b0f10728140c0406005c0d00202f04004a1618423401804122402c4ca40100c40c10b56003040246098482c20b149a04035030200607440542006c583d015001074a26040320080f5180e0340ea561 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 584714730 1250 584713480 584713513
    0x1d0f0d0c020d11010c14030720030a170c010603060614100f0f03090b043c030302090607050a0b07030f201b0139020c09070201090221 59
    0x80c110041e42c005807410300d58000a01c58403240600980604094050380450780784c010842c40d0441c2e082c00540c1001402e0340c208802180404804e0b046e11700030388030424a010109548100525000b881d9100d40600e84420b4121403050b0b41115520303400903c001610b80c502040949194407941012802001038028145481002030034a20030b265111b003c1d0000b40038080b00c621010b00804130625076501030341c03004104200c020360711560169201d0384202c92110b820020000082c0c0254004506025207249141403400303030000100d07018a0056224a06580001d0140c0b0550381d0051180c82048060810800c0080f070f5184664442c0d281044006c03580d580b1601955042c280f810500d410754600c4036034032a540c030080c00d901c60211159101d1582c50f4a030007802c490f1141155812854400382c40c3d200324203014170700840300392840d2001107111305400020b9503c030047c1b5000b52196184200050000f07100350300c8448400c0c0c00416480035801c40b0302101c1d401070040c0c00450000d0188010a2400d400d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 584715980 1250 584714730 584714747
    0x30f060906110937141203180105030a0b060c0109061a030c09070306080d020105040606060c0b0609150d1b05011b0f061e021b070f0b0903011d0f0d 65
    0x405010038003080084003d1100c413245242e094184070b90384001d00c1c2048442c08030007001400e104051040804070035810441c905149441d60405a802040702100c040c1c0d1700c40c10914220420b081503601d0303407141071081c8060300403101d096401a001040500101c1415002003405034042d0348200708a8001807054901296111310303594159115100c3c002c500e00380407200d55449122803900040b03145c3c42e06805401d09010101442c0140e440710203200038000240721f184c00804480c2843c101008003540c03141c0342c05100504881c0b1510102c000100c1d804511031401a14160003003440c0d4a9840310700e4000d1641d2440312504100e03580400004c10194050091800c030103040c1c0120306400d0f00e26688a001844201e001102c0c15034660710b90183c01e0120b003a417070710540b01201001d6150500380600c032000b071100303200781c03030055205180401149010021010a1350861032490781e6031100c03040405c1c09400f901e0404054045180e00c2c000d100000400c01044078803000007503541681c160002100e0b10705 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 584717230 1250 584715980 584715997
    0xe010f0501050705030c06010e0709091b1b0c180608030a02120f070215070201021006150c02041401060806090c2106030a0f03050301141c060207050304030f06090611 73
    0x8540006001942c010000350903070900c82c0f000c80b45000f0300800118102802030340040d180e03016003014004281d81200e00540600b04502003006a400ca007244000d5000440980b0f500f8400c843c1070074800c5e819a1401d05821503080042c615005640d1003c0e1144c1070000041b10b1900345c5021004100d0341404012952b15461a5000b40003828600c4643c00655009000500010008202000050304d89070310342c504500749040115143c1025000181c10031614105200d042d0b86010800c2c45041100ca804d0107045540d440e00400c01c6009102090080c244452a000140224000090324507440000284111400d5501c0351090311005c581042d0383c02054034001d04164040d0020005401904070103510110080840c1c1040d8070303984841c0200f1a99a4080d00011800801030200720720407071003000f0a07541954000420340c03e0407034a044031035640c24002c12581e000500c09041c00000c00a9074003654000e00356103421021890403074010300302e980007195102e0511196000050074002034482d0301d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 584718480 1250 584717230 584717249
    0x4320906090c070c0e18030f030403141306081509091c030f0510050316080c01081b0304031d011103120406020f0c100501091e090201030f02070804140609060f0903030409021603090e01 81
    0x40d100c50781c054942c020300807488034cc0d11801b48525407200000030304100041189444d032031820b0070502c20031101d000040a1160203242104140040142c000480707000d46660350704440610f8240140480c09080a0031040c0d072514107101c148000c800c004c0e80003804641c2e00301c0c1140d842c46100c03614649468031070304c6940c075250400d400581caa54020308a050348000300240364440c042c2c5c09a144034580c7c00c1540c050b400110030b200c0c121004800c06030382440042d03007400d0060405110311107807652481051b400e444811035100c08603081080680595100440300d810b2185c50740d05918400d0f0f5254030110448150078242000001e0340040c5200f10301441d04c01c0100702050200010181003d010326250417030426603602d80301c19050240d8406400020701c504aa10f030b0782c030314020400c0c10940120b02c80c035200e01001c1140d0491030b40c804c000c035041504044000d40e00d4014541c0002e045000e6a440b40c804240002116400a000004491074151081d210a6201615007c0c1c41042c14024003400c0c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584719730 1250 584718480 584718487
    0x1809060e0a0c0801062a1a0a0b150705030409140a060608070813030c0c060c05010b0a062f0303010905012112110a020604320906090c070c0e18030f 65
    0x242e46c8a001a65000d451101000c0022071080f441c440d81803a04007070540c0d04c0d04032118040c50050700c007280c0300e8010503410300c02d12000600b040058800034803030b1403061880c90300203403520401500f0700c20f41e0002c00c80c0c03a0b4100140307800780e0340444002204a4145504030b21b0f062012a05901940c1c00901480c5a50740f103500640d0f540803001c3c00f130054548250107100e0f45034486800260003007807007405010300e6550942c0b030704600d00e403071407d441503404628464100a03009000c0203600440984950303080300e40c09002040d00c80308030703000140301c04241d2656000006c000702c1c400d51190413090494441ca04442180a440c1038141d041250806000700f070080c1d6a41800c810610965081d08045410b400351000000c03694001004c9030320641c003441500101c1c815040e6002070b2401c140e03400b01c0b5000c4c491300c13903c05184006011540001d0480b840351940c0c1c0081095060500151940c0070303031042d01090400c0d20390032030201441040b640b5011400210859044900011041e0f58031424846603403800c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584720980 1250 584719730 584719739
    0xe040201121506080a0f0507050904181127010308030411032b03020d0e0a050f060705040905270105061e010c14010902100306060201110c0d030c1809060e0a0c0801 72
    0x1000130000e4081900103031142e08406201d88503202e601d01400d00b0344c0b2001d68440700c007001c2c0b1094500031075180380e0481458510b0408034011040740d400c488021281c205295500401c03c0d1101c1000e000b80161540c1300300000b004121a1340000d5008501035103100f0b800707040920416035104038003004040c0741c403084802d440c100cc5840f90050302c0b1040c01e044c0035052440e50f40c200301c02ca800c1c400708414030b584644104000d0006c103002130800582840d0181c44a0f1030f0408000d80544150b2141c11282d0350f031000040c50300385002e01101030643d4500c800201c4010080c0c00f050181206560b45449400030490f299480032112031410f81050060312241e2960005480e901e0826613012054207a65494000350f10040e60340c220074080c0200030340c500068003808d211000742154280c034129800180d0800c504881080009604001c5a050b460040348030f03603203004100c90005044103c00d0010315001d00202d03112440d5081081518601c04455040d9650b0072003003006d45110100410210307036500010310 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584722230 1250 584720980 584720987
    0x21010b0d05061215011805060105031303140313060e0c0121060312020f06070c0c0b0315060d0b0103050603030307090e09151509060d12030b04060f0e040201121506 72
    0x10380c001c800500f0351402a0148203000e0804c0b0b0480e010b0011142c42c100140484102c150602501e124076140402080c980180041d0140c0310241225520300840801c510405200d110401e90740380c3e0340303207400d5180d007402402001d00b82403e140481d00141403411210550b440054400c0710b4201c16911003080c450764500700c081001d030950102d1a6580c40f4000800402c194070380c2281181c00e01c0e8020449800301a05040c1001c4016081404100d540c0301114045552004290300b9942d0f0010030a60380c0e01c80c9108010040780d482100d07900500040307a24100c410241e400401e40b09400c3e00c051010b60745000805850b4441101e007140440c40d0883c051140710001500703594030681000480307407e141c80d5040e1120500040314036070258910000d4880e118102406119000181a11903511313903103665540c00341c90200c450b040e108156603002c0c0154507a03107a0b08600014441d0242c0b6294094403043c0030200c1c440111810790106d641c16529480482c1a8404c1d100025240038400320945d0401004a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584723480 1250 584722230 584722241
    0x30a0b0303040b0c03071401050105090a05070519020c0f04060e0c03040807060e011b02030310030b06040609020c100c3e0d021b03120418060f0b21010b0d 68
    0x16030184801c0c40007141e4490f095006040341d015410080d42c40d8040fa1502c802105c0c02c2d64800c1b501641007070010401500c2c0c1c103403a01d030051844000031403669034208089805020f2242000c402660005020501c95000f1807540101c0c101529500316845c420014001030702d546101701c8444280002c002030002d040c850240d90402c1c842c0711054a0084241c9503607003690000c110000f41650340b010309408a400494540603168014000b40d8190b2401180c0240216120b11010f4129000c6100042c110783d6560300c514042c26416004544440c03000100513500c002304141111018500031000100d6401418a4410080c900e4503a0907200c0081c0380d014550600211240340c14003c040440661050510800c402c1641940c0100210500b400c48641c1c00400310b80031a0094115009260008849004550031f0711140c403040e940480044507007000401c0c00b640150941e102c40c44010070350b0050b101c010007444010940442c0c40d000d58082c403070b0a814080c17040000004003000240d1101c680c07034026 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584724730 1250 584723480 584723501
    0x80c07030309050a0b060f01090b0d05430206011503020705241e0c1e0c071509050406060e010c0f06060f170705030d111204121214030a 60
    0x301e030010882ea196481c04c085401d0807500e80500c203040064a061601581c10410002d18000464514000c443c078000e00c541904800c072207860f81c0c0002d10f1161494840310b201c480b40d4584401002c1182030146c86064460000c0d030303041d003560b0002c0c00141c0c800500ba5050743e1503400c04407198021003405078000d6110503400c4800e0b002d10142c001d03140354049019048803544805414a5190440e002280c0c10f042503203011015a060040c003d90804960548404441094010441c101400300142d61070240c0b44240290744a004000300b01e01045d0780c08280044802d4944100507500c0303904020070740da05030064500043c0701405003688e0750710940052007650f010744841c401003009a00e8aa06485844c2c006ca90540c00c0d212040000c04500c20908100e2050000034086e52070410340002d49a48007041140d04006203450107407008507050001c00ca001c801e00c11542d945660303d40c10340c0009a5203046c03c0e940e046400110b906613038041c0842881072481d14a0182c07541c0d5904140d0802003098403003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584725980 1250 584724730 584724737
    0x1d0106050309070906120204050f011412010209330301080a080d1e02030702070f05090f0702030d020a03050613200c010f0e100b03030f0a0c08190e0406080c01080c0703 74
    0x4d0b28032250b1003030f800548401525801c8046081c01400280c90011f030006441e07816640c01008a41c032001050b54441c05c2c01c03180e02802003809065240640203200d1040c1e40590300304000700c0c40c1e0403880c0c0c500b007260303207040b01c549004000d43c1080c2c1480d02091041a50076006140b921001501c110018800c1907000b407800118a450b01808000405444a000b680b1356400428403a07007503010080400102140e024880980c0d05200201d0784030400541a84003450407000401c414034024010749130342d034984020440d2039a220304d1300100a03010554400e4010b840d1018040c002d580f40b405002442c0100c0100d0043c1c000000440b0340d6654808400110135550710400001a80c403940107100e80f04040000030541104136109035001c40d2001003d49129900c1080f0080c000a611820750f49850302e18200b03141c29502504111120b40301e8034401d0071800285800e006900360300f050041882c6007055a082000e20f8954140944d2140700074001c03404582d03180300040c6004204001403000070300c0b0b4174 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584727230 1250 584725980 584725993
    0x702092202270a0609060b04030f02090901240e0f27100e1506010903051504170406020d0324031b081c020c040c050702092a0c071d0106050309 63
    0x165202c0c00c510094940401c81c5031202c3c0c00304011115406110060038020403001c0c6841c2c81d680d06c400b691444464028043c148000010342c6582080d030080c82008551039610443ca0303159218240440214020407007200d6104001c40c9000c000700120070b00c41d910740e60303900d2028100141090a1040e0546858580d0320820030360007102c41700d40c0107150000810b80300900c00c03150702496a0004030340040565040000d5044100003003080007912203000c1c0d100e00c0440302c0507103a50034090042214800d210725514800280005c000b0f50004108059180940d010061411000e40807281c001640003000404c01184e02c050020541d800c01192042a06030001c0044c10344d0741124604088101c401d0510720354030060b813040d402ea0140814101800b00301d904004400340c0e0940a41940100940a40211650070000301100c4140c14141c08040646d0b245d41c8a180c800d0348002513562082c0f1401d6528081c0703030f0001a101c001102c405200c43c00007002d6012580c01c12508480a401c0180088058030491 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584728480 1250 584727230 584727289
    0x1205061e010e061246030f050c0a140d030e0c0609190303020f0d051914130801061403120a050a091208070201030e0609060601030c0207030b0a020702092202 69
    0x30403040803005000b1078035145d82e5400e00c200030044501c4010140b0700601002c2c80001c12091a8413941c00d180e454201980005114881105c15010702241d0240314844c1c00e603180180088601c421305540e044a04483c200900e59004030103407012500d80d001310b80d215840407200343c80c20902030900d80c10f028003002a4860b010f00f1228400a0790761040e0090b0300b2086a41d103900300140188100c80076a800e0041c541400c41d0840d441c00e49903007041604019043c00010180c80c4600e0480c5c4c101541d20510502840d00c40b00c0030350007002d80340708610b2030014804808a003801d003c9500d80404c0c9484032402c4c2001140301040d1010341c8451740080400686010102e411580310009415050041e10280c0c0c0312541c9100240c01c036060b000204a49902841c204005e042001072007550064013840c011523481c403024000e910f090310603000200299800c50800190f10015806844014002c42c1c600034103440b05040b0001c251410001c4030704451003d4200005410814059040720480c012111424041c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584729730 1250 584728480 584728483
    0x5010b090a230a17010e030703020c010c03171501021b010c060506011403010e0601030b0901080a030c020406081203100b03070504030308061804030206040b0702070b1606020f041205061e010e0612 86
    0x81c0c04c00c0032400c0304081040140380c03003442617130444140c40c0d00840c07505205880280da100c0d0010480c60400c2450503003242014800c0342680f0444d0b00c0745003180540d0802c011410070700c8011000042c01882403100d0240c0549081e01d5004504c101038644640c0f400c03040d01c0720005008000c00c81414041d0108151011001c0400150300030186201c0d06c1580e41800000182542c1c003429009206100c10030050002e014045403002c02c6550504252043d0103803440440c026240641c031134034140c0140490340300010402c500542c4500103422004002a0b00d512580c2c0d40760100341c40c0b00c03000560920060001901a10700f894101318010025100f0f440c501440507049001280d00b200182c010000348005c118500c419550000d4950004d000b01c1ca01b8500e0700d8403c0c0c051070b0500101e000003039a410040c80144d41c11100024407400e0398a0307660f0303116000b40d03e442c8881d000032a100e11508002400007240b0600d6006c4000d10109911000d034a458169510304101030400c1d540070300003c074108030f200da0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584730980 1250 584729730 584729749
    0x20907080c0a05091c08070b0604020f0904020c120309011a03011119020109050304030c061106041e1a091606032a02010b10030506100504030b0601050c07030804120605010b090a23 79
    0xc1814150f55034036088c40c2c070000c40b07480500101c0c00b5034014401d210f0314108141c1660041e510075100144c8030910350902a14003110811802819080001800810581034101a0182141c1c0c031403003220409000500d401c071001c460580744880d40c14000071002401030800554404d041c2d10001c910400d068032468210b5006038411203083d59200c00411200d40c00c903412022003c148805006a440c094031010161a40320508107123005404903002c04118003079554210082c8840100d11480c0381c1000001c0da00d20700c49800e030092100e850000181d06209004403d243d20841702c0300078a15440102d48518800ca182d4008299501c0740890407040c0c56802c065030000c0f0707040c3e42c0859241040c006000c03140c0d5220000500700441044180042040103246940152081c038002d030b030300d03968495451304040c00b030742004105900014002a00e00841400421064086c041c20400c60341d071204000381d9485a18031298100710803d0042004080c028280002d10b003568141018480b4101c000401d04003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584732230 1250 584730980 584730983
    0x31817010204061d0102060c0d02070b0a0c030b1207030b0403031b20070528050a0306050f10050d0b1b0a0309141212220609020907080c0a05091c 64
    0x81d40860204030740c5501608641020300c00d50500001101c0e1000001c0d284c62000b08417200c9558009003400f2102034650480f400c09402c4201003c1504260362a1000f8115078080c3c000000e003001c05926140c6420014400d42c104c1003001018158035581c1c440199420041043e428540c2d03407050702061607848082c405489980f581c0d511054444003501408843c1000005116588680010302282d103c0101120100e4a8090314105102428100d003048032604d4102507040b000307002c8000200641500404e01401c02007803c210300d5915aa10784038002030394899141d000e030f451200000071038550f803001070708020781481c060040c85002070064080d5105d000044002a5034001c1d010a0040400d80742c100c007005a000350245000a6480d41510302415018843e121421800704601c0b0004200b050385840e1880d0409800b02e07447d0030305200500c941c25059000d264403d000816603440360990500c41ca04800d211400c10000c1d18049545410004480f600301002585551010301c08408450040707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584733480 1250 584732230 584732233
    0x3c0306050405210d15080f03031503030304020a12060b190e010e0f0c0d020409150e07020d05030705070311070b22050a1502011409010c020d1704031817 67
    0x41c141403411a15002c0041c0480300c0e030140035100342000d0034541c802c994407040b4102d07000c14211101c07009800c4503584d540c8014001d220300c01c1414401c447c048061413041c14820b511003020728484040c03503180c0c0700c120b8000758019056a000e00c0140700f03040b4419201030040c400060b81b040d54102080c1c060104e00105041c0440d200b50070402000d400701c580d80509000c844d1a0340d18246103411144080c8042c0c00441d0560340030498451031070341581a1402040c4800b42400f0001985003021007904960007040c8041800000007618640001424145403100d40c0c4e42ca461543c2d032450490759608540000c40420100000f2095501d60400c400ea02502220001c15591850083d0f040203403000c5034284c075801f101c650010843c954500b000c0f107084030b20f43c201080741c1c0000540220b004001100c5d403508075400c039205106c82e600055001e411005120f40841b1b0410303024940582e00c902c80340c001c0d101050500000540003a105020403080f2610540b801c0c030b4007980301c0e01204100264000b031503850707 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584734730 1250 584733480 584733491
    0x1005100f0c1b051003090c0510020a0606060306030311030901080129070602190f090e0711010504050a020f0d0206040512010e030f03040605060d08180310020f090a0b043c0306 77
    0x10b481e204c00b13446281c10040c141000041c3c07180d03031014608941d920072036200d4200705e008004030740e00070700402030311a070712400801403e529150090000c10b1140016800115420320540505c000081140e0340c5000c141c4803842d4581c80c10700132200031800005003401c8085180c600540d080783c000054145644900c90250700c50035152480d9041c455440380550410880f1204545190b0300816200142c0e80010350300d002c3e940c1e170081c0c00d440c0c5503881c00d1543d800e50b01e000200018031101140c411041442151b0551195820104000510071408000380d8851410401042145045110100b14a19800c000705513040c110312207a003550450100b00740d80c40c0001040000b004102e109090307018400b01d03524030300f001090320b4500d01402000b2190b10b1603450f03920810950359040003c3c05481852400941d0754503641460040c00d500f010407594040d042004000c501d00401c10141c506444950b006180d0f40140800d0158010809a000c02e092441c0884031400080e4000c6000026500601e000300381c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584735980 1250 584734730 584734739
    0xd150c030b1c08030f0901140705070204050c03060102030a050c070e130c080a11060d1103070903060516020316110a090c0f080412110f0307050105010e1005100f0c1b 73
    0x151020361a6050341042d03030800c46440010b203054107603034100c00801404c003039541d1a2a0042d004218230b80c07500d100d0340081c20802c102550b001005184540c03090701d00388580c0d01c034484103035010b003c180d510902582042c0a00d0b2081031140000c1d2500c22041c0c0210307030b081d0341d071810001507482c016620503001d006000c0d8603106010107054108010215a001005242d80c0c644550325030500d001c00081c0f2840303000404000310000e40d0802a1034000c002d5555540cae0801040140c5016507520007210200d05200008a4140c503590410080100f144c000d145001d004080c20017042440310012100c040c84c03008240c029849039090600600481003000480e5100400d0242c00d000050010038100302407170702000001030380c100c001c180701c90f03880c10300031208510f0305a041d0910342420800030441c030000c00e02c0c2d81803150542105040740c15070900005223849541d0444211015801240d0704a40315035101795106105009810140c42c0302c2c03a2969645410f50f580300800242021100080c0142007070500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584737230 1250 584735980 584735989
    0x409020307091e1202030f070e1503060606040302210d0504061707210b030a08090f0a031a0604020903010f050f0a060509150301090c0914060904050c0d150c030b 71
    0xc000d0f103a42d580c8040a00303a107000290f101d550b0f50048540d4000041e10190454404010b80d0038070240c00c4041d00d01032511030840406010301151201e80704005900d007640c480c100494101d000300d5000d0500e500e46800c1d41c0030b020106003100300901441714040500b6018400600800108485507550103070f590745400790080401d0405025588118821414041c6084d0004082606440328511603501520000307d00ca006204011640e90540290582c0780700704540040100003041048880c0405000000180480c201003404000c05051031040f40c080d4444660003161344c4000300900161519040d40086421364030b08030056210641c44406201da5000700244881c1c0c010110b5008021071032900b0006801194060583c003035070805840e6000140d00d00b90001030705950031403070140415641d5072040d002402501620030b9200e95031800b2550780d02c0d060702d20600680d008002020000411001c00c0200345003444112100c400e17908001d52181103a00a00c94102029180001c03d01054070500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584738480 1250 584737230 584737247
    0xb0c0c071a07200d080d0e150705030907500108061c0b0f1b09041d010f0c020609070f03121205040809030c101b0c03080409020307 58
    0x2041840c54030040a5265000362003900c00d40c9801c1519020b000040d080b031010443c2d8886001038000c00c0d02c0300c0b54418404114010841016180e00402510b0b02c0c18003c136854042c0701031080ca81055900110340d015201e1405107402c080d502080d42c0c0351907504d160740e00284a00248240034000404081040114910031400010010350840724204000c030154200c26003501040f14140f000b031710003040c5030b07841d003080a646060341074601c1c0080088504141c02aa6000c694075408180380b5000500c010640c102c00000101480000604021030302d0200000340001c401500c0b80700d481c0c0d0081001440d001d020b50540340c4510f40000400322002000241800c20040503400c050f4080c041c00c010100c6140007900071a070300714856440c03954074114102e9608405a0564003000e082c002131009202e854801461810f10440488501580010a200d84d04c00030300000c4001c00c140e0401e41903485010400310140c01c0c41000b09040d199281d0350380c3d019a4000d904154140350303012040199041e00800b41 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584739730 1250 584738480 584738489
    0x13060b0901060203190302041509082a09040321020406030e0c030d030216081309141003030521040b01050f190635040201080c070201080c0c0a0b0c0c07 67
    0x540340300d60402c40040c3d070b00c1c42140524030861001d04a260303550b034400e41c103841c09001c0000c1c900360341d0824104001c2a00710a4003802c441d0307004005c941c00f00ea10b4200b20300040018201c0400e44020f001c1d104202d10418000c0c000d0701804040010624004042c80b02e020300c090000300010b848900342030006003100c040118100055200b211004007a90b00094411071114941c940981da0b02c0103a41401d040d030300b44c618010030341000482e48803440030202120000b40c50b0082e20030822410407005180d007549003610300c4020317200030b01d04c144082403242c0020502c003d0b500b42484500e032501030001a845030216001e03105440110014041031600c01c2ca04103000303008903030b0711180800030407560400e21200d108003c14040e03042a10110004100c1e501040415001e884504d091100e8455260141045030101d00141c0c00d81c00142d500c400480550b03003100d40607510303401d00d9511489104080c0d4050000d0b8001c030b01c24191498005511400e2480c403070040b2002c4030380ca03a0414485640b5020300c43c1c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584740980 1250 584739730 584739739
    0x605010f1401050f03040201090b0c01050f0a112706070b06030d050a12090f02090a0c0f0504060f2607170601030b0f010806040e0115170a02010804260313060b 70
    0x140403000781c3e0b0120a4030415044081c1043d070320f840b18070041e40c156403150701001202c5004195a12601070641c001403080c9801c103254030155a800c0c40c44005c60b00c0c80071b00c2c4280d150341845420508050540d401a42c0000c81000050400b01c00c000203c03030350403144007182c92010070010480b4a003022300c90821080d1103400c1036070600080044c06000584c00c43c102005d1280e880000c1403d10211142c4a0107458014240d0364035800d107000400c0140ca0b0920100000c9800560350701c0c000381c440d50868044480665540c40f800748840e20484102108a02c9480091206244024100c0d46810f030b0901070041502c901103c402d0011600410883c000c1c005818140380c406c09402a46429800a800035024a015403441c0d65610011707004108941d6125002e40c03810308000401005010780c2825200407241e40803081039080700c242e0362200e03401402400114201c01140c000b0f010402072030090f04605941e100940c01034000d01e04180c00440d0b50300c400c40341c8502d1310005e001c258815940510f03c15138 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584742230 1250 584740980 584741009
    0x102090f0f0a03150b0d06090506060d020907030c020708120c12070c050402220e071b11010806030a06051003170c0d050306012a03171504020901050405030a0605010f 73
    0x100041007402c0501c40035000220195070070818042c6a445039110a400070038101c545911800d00c1030050070500300031034040c400d04000c20f1207840d05402e0015402d81c002e00c03c8190b42d0b01c0d007804401404c03454800806510520801044100040c031640c4c004ca500d07210f50680311051024a0341c41d00c004c403400f900750a5420880398021502080b20302058039800d581c05030303503601c0c0184a80d020035407420980c88589080c140101d0503c40c20389500e40201d0490303644115066402541035610000698000d00002c801c0c0284a295405103c11681c4240700905403030440d41c09460791401d440381110151000601d00c1003e10801201e003e10313038020034884054500f81003103452540d03640c550800c902c60038040041b00191081c4e104040c10700006010040c54240541e5525054110f038500942c01c6007c249180c165500c481c5e401100341d8030a10040c5401300c0c041c50240c1c1800025401000390700c1c1081070400c004980c5450410103076030000c1c440c0500040710b600d805407014110600d900410045200711 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584743480 1250 584742230 584742259
    0x60804050a230a06091e0c0501180e130b1803122206050601090605070807020d0212010204030309051e1011011d1b03060603030901050c1005070c05211902070e090102090f 75
    0x186c44081651401e0a100c9060040c80c002b02c2c1d0b1001c0107620112030090404100403032201021380d140c3d40f02e8441d488055680d03c81048c0b900406182d15101c010307a80c403d0003000c802c180d451400a42004e250305100041110180054980301c146010030340342d00c1d88880070301c80c280d41c0c0082403c00624140c501b01d403c00056139601c032107510503d1800307485203042010100965a940506010142d07001f07008550300c0b40d80f854040e0401007948074091045503443c911081c800302010040d10807900003841008004001c6400341c1d020b21290381c6492540d940d07000140d04880c0720003101d080d120a01030051841202d0350b0240360204041041141c0290000e90911500380c60000c00e40c1c80340d076400d013081d070703141c102c17590040e454100421080307001281060180405150803940d04d0121600507000c2c0d48200d0040818100e4404056500200c001d200b080710394003000101d0041281c02d071207407050381c0c94155a011105e400e001c00391080300341079500041d180c0042c60511003c6040c0704056408103d0140d49 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584744730 1250 584743480 584743493
    0x60906010f0f0e09070f2904031707030201090f140d0f05030601120e07120213020306010518040f050403020f010c030608030306100c0b070503060406060804050a230a06091e 76
    0x703c2c880c548070684001c0105200078010300861001c0c00e1061034600d0303030681c0c46c0251981c000f04500580400c4110082048008444800b290181d903004462901c4401d0403c200f0b181c0d139400b030003050301107540c2c80030014002240d980510014030700601150201c400b10418040c01c0c1451510b1a4080c0100e00c03081d44810381d04017080d01d60004090906c50003103110f4068500141440c8854040140161800455108000740c0a0051240203580d108088c0d90300401c0c0d03004a01c401c3d214540421401e018410f10001c0060740e45640050107480401d45801103800748055901c00e40b4210090381046100c000d40140074030903800401424502840344a20342000c1907124070000d01210f00585511564942d05805030700d0409a142d8000700019080c0750030b04005126400540f495403040341080340000b40385200b1812540600c3e08503014140400c3d4585d03804c00400420407000703c102222680030b42e05c2c0c4000303004001c0d401d4060f03640454403a180e440d19070f140440c1401d07070103125254140c108010910 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584745980 1250 584744730 584744759
    0x2120d0b0109270e07090914010b030d02100507050705010c030f0e0102040e01120311030409020703090f0308030a0b03161403010e01060609033c061a060d0b040204090e060906010f 79
    0x3d83c0b10000344100051000b03509014070340e00054400d13824503242808205281c410440001049002045007072040020141c50380c4000000b1030040e4400c0b01c083d25548030341e030b02c80d54100c0c0690800c2494002c1c03a80d40e543c20f42d0f140e41e04002c0882d544040c12401e0481074028104401c030392034000c525142c20021954130941c4103003d0040501c00c0000740e0420980604181207440e52040101ca0303c41e9600c6400c24065804a81c04400240f142900050003007050032660007130b0780c0c5c002034682c15a6180505c00000f056a1358105515204000740c00d1250f01491405801400c010005400983e07960018513080d038014000911190307141c05000c01500350300100800c02c0d00d42c8060240c1641d0040480c48800f081d40c09100c110380360045482c620264a181c0f000704143c1d00c075a00c03d111000142d0070034002c004091a072583c01103420400c220656005600c58404144001c00050900b0b80351b0031440122150102030a0342540840280710751a1030030801c0c0380c01031544881c0c141da140e0500105404010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584747230 1250 584745980 584746049
    0x60501090e0d080606090603090601060f030219120b060a121104060203120a020c1507120515010509060d0f06030b151305060f220b0103020c0a0b0702120d0b0109 71
    0xc501e004c41d24075030320311088031450f10b4020701440c0c49041c5000001d85030003007071041d9008a49800c62411005000340240c6a000d582c0c07280c140310041c50b82e4010313030301d980030301110301a01991303181030303141546e5580080c16120303a0607503941d0b400d007800c02030410444549003001c5140800034002000002da00000b19480d95a01c0320788030005807241007200d006800764004101e100d00a540044100c1c0d003034003406c148252144e41d540184e101551582e141154402e0310703d04941c0340c21300e0740300d82154080c400030a00404090481c0389020000b900c10310458038402c4040a41c0c68848104009200c01035442d150858040000d50000c040b40c5000144a00408119a00c03565240c0700010419550300d1030742c80c2030100c050708000c0306046080242220a1078174009003d0030b40b2f082940c2056511a100341c0300259190001041c0c50101c0b91294600114001c00c03200840c441c1d501c501010400100282030882030144000c03036415507820000d02000039641001d158128000c00b12941c0030040c21a041845 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584748480 1250 584747230 584747237
    0x3010603020f0c060103120806011b02060c160b0403050706080c04050d061d010c08011202011b14030703030b0126041506150504031b080304171006080a060501090e0d 73
    0x40b0340300410703201c181c0180c440100d030303900540000200780140c600880515010a69507007209944190065a401c0f80102c4881015580d16540740c0060408800405a01e010581124080c8556842e500c60500302c1e5001101d0b010b07008503040041240820201010b4512824018214036205a4480303250040e80300d00d521078104041d80c030b4240015a0b0208206082c200c2d250380d50424400c83e00d902806894050700c00284102000041d024400d1500c80500f0ba8141d450b14001403480581d10740a00315000d00390b0b09900d034801e00c0005050100010440b85200e40c5011554102c00c800240903840c04c140b2414164a00b022400b40c04101c00a1076907005d5880b00683c4101d0034610141c400a00c0170350800201c0340b1164100c0e40b1643d405c40060000c40b07104140e100d85030b1840e000a0200d4541e00c0c030600c003840c1d200344002d02000e800c100e961848980210221110100b1050300b40c1c0c16075072250b0241106410048010041c080d8034001d060251841081c1407103019a20349466a40f081c1c403104070b0081 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584749730 1250 584748480 584748487
    0x4051921140d051003020d0605060a0503010b01021b040f050f07090f1208160b0106050421031407170a03060303020c0108090c040b01090f030809090f0601090302010e0f04050a021308120301060302 86
    0x82488044c04101071500a480343c0500c5c001440c020000b03103026039501e8401c40b84140001032514050141411610041e40541200d40c5004130079003a5507980c2041c00d6000751107071005659050b0034810345208505068490490b81085003020306500003d41000c030801c00080c0051062071000300340313420303141d0740050403656408101022082c004001107006003041c0c1132400004e00300340d102000e4000d0f2602103120b501350800180c1d4007030812904e146c5c01070108002d00c2140302d4106040c0302402055010b00410007070f105141110810702e501148560b00481d65482046c41850b504021500c5d054000782414000f070f08000c0e411954951090032094417403900e50043c42d200da445010040c005142003c088a0815243e29103507880c0e411400c070b640e000d000b081002a000c0c880c00480c1d207007d804181c60320300d407441c1075400445556000c007040b150030415410707103502c0c076403200e00c602d600c150403a500068482a0044001810420b9a0700c60400c2d03601c603030811002210709074100ea04551076420010780e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584750980 1250 584749730 584749741
    0x9030f090f0b0f130b04091d0d030e030c0a05280c1505040504020f1b0a0305300f0426030c03060120070306061d070804051921140d05 59
    0x11107105180309550f103d4001c5500117200903480c07026000f0341c1e201c00010310001d0300314000047e00268900300e550603a0300c81318645002c107000b60b10001880031490142c03407509903100c13040c9141281c0e24204032a1a404500b00c0328a43d00740901e0074068a4440401d01c08200c2a9100d10003013410b640103030b03c5141c00d48094191514040c0c42110010702c00900305540380e0100300c0324911950000000c4000c0b1010700403049610f40e0004c0b902c00c00c1c41d50b05807a2076003082e511001244014124004060300c601d09145103030110000248540d00c5107044d003481150b6403405103080d601c4414500c01c010108103400c800301c0c1150440c04150b0341e0280711000c40075102e9035490700481e51005420141c0380b42070506071107072101503408503403c01564003445017800160303501da02002c0911101403155031f417460742030042608a4859013440d0381060190040b00d030700881d915250142944000c000302e40c05111007845103100c00000608500e18145420033488a1224054083c030768032030010380c2440159680700265 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584752230 1250 584750980 584751007
    0x1080a0b15040503100605010f051c0501090b1e01050901030b0312031f0e070905040203040302150c0c010e12090907020f010609020c0c030c060904020904020405100309030f090f0b 79
    0x841080d005040300740c40301c007100920440390310a0084500030302500000d403007a500307107014803012101e041e914110340304105801210700d500b0610b80d1a03101e15521004038003686550041502038500a040000d14050320420000e07060010203520030070b40703070103462010301e41c0c2c01800313460300d0120070300380071401a8400d8000703800c0c004d00114844420300c020081c400c10300070380300c14144107105080a90a8051320b888048103200c00032940c2c01d00003210110144005d05080d00610780191103401140c42614403100000a0720030300311080040c0120200d090081e040c000d01544034184c0341e11001c0d29807a98240b040810718801d400c0180d000780c140c02c0c08542c88500c2009400c0744100e4020007000b45a485902600280d488103880300d602d88107010040c5251315001c40c1d844000c00000700540e03d04090001400044e401142c080c60303000e0f509010000f2643c49001c0b64458035642076900107103184c170500d4082d00ca070131031007801400c00068040c2440401d80102038042626901c03040b140d1180744512045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584753480 1250 584752230 584752241
    0x30718060807062c1f11070b1c0614240307030204032a090b130207060b0a0b12191d010603050f0a08030f0907080d0203030f0a06060e01080a 62
    0x8041920a01a001661a43c004c202c1120700d400032448941c0404000d10091003040989a060b83c021040e24403e8480f550340265115202c0807402c0c660b002038529410142010b103180d000429400000600700c02904841c404c0000c040301c50f00c0200b25940c100b074050101c0d80c5038021541d000e101032440d56005640e0b8440e201d00c4920b8940c882035940d00d0110b0004003e5081032104450317120b44468081e02190840100210aa1013184605601ca00c1d000250011300302c0000d040b60000c1042c0c100050503001400200411409000003044006600051106003a250352094000070400d210101c2d0f9404908210381c1c1244035207404401003051100035500500b080c051002d4100c04136090080c1d00c1c807041d00b0040c112400381003540c1071110110151a214622208010101c540030400a280d00c2e842003085a00301003410107d602254690003060324010b400184600542c1c03000c0304000d40c40b10b5003500160300c50811003050101c40c0c43e245000e482e0100600ca41c905014007140001e544070000d6105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584754730 1250 584753480 584753489
    0xa030210202508040609230127050d0b160905030a0b06030c0d061a01081603091106120a061401050706200f070501050a020301030b0609130c181a03071806 68
    0x181c3d40e0b207560350306014214200500c68040c21483c14603102aa42141d61b40b0030340411410385800a00343c0c015104010140901c1d402202c081007000404606074550100301e0910070310030340c0198001d003000310440c220f0341d080260401c10414203000038030103910089151051941d20940110b03441c4c580c10006820540c20200c1207801c202403507804c41c02d110280d00f1410030302251140c408000c8101400442d8a07100c112340000010700d2126401d06c1c8580f0076800301c10070340d0050058a41040f80540003900076408000301300d650030903510621556041c40e1003440014000c40345190300d41c40c101000682240150031026201591342c07102c0b2a40500700c1d4500c0405519034105035a61000d25030b000c541c483c0c00030f1000380d0385586071000180803240c05200b01c034180c80c1c00003840881c1d03a80341c1c410050b452100400c0e0030000785000f2242000619581c01c410041c00c000141c0c10900c1003280c03146001c840c101e13031001071120281044440c0340d0301d002ca00e1501350340d518580c6140514800381c3c60300181c500f5500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584755980 1250 584754730 584754743
    0x7080d05070816080a030506040524030a02040f0203072010020c03070f12020709050105060409180b01141c23190501050106081b03010e04060e0a0302102025 69
    0x43e0204210410008002c44207064030100b2454070340d0001d001c22036004940071142d5102c903400c1240784038001001454030040040442ea01d4250643c08902130300c445109403120113030040140000c80750800c542840d143c40088219659807030a1070071950b201c01841c0c20800305a40090070650b41d6200b882129015500458040c008006920f40820742d0181a40300500500940c030000c03c1c0452a07000782c13412a2401040da60809082a2031304005094a0f80d4a00722518402c0b0000005003d01291070300030b10444d500704e043c81d0422000d10404110620141d1304036041e203014140080c00642031401490701100154503889444030300c840c0707412440c28810302240a10010743c0204401500210b050314540e96540040c3d454848954140c0610446c02400d2102c040c0700501c440f9581018690380140030f1203000c21035801083e4450708140d011101600140c02014284030b1b1400b407406240c005020f543d00c2c1103070740d905030a00032029005400b0a02948120404280710b20009288020702007900240c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584757230 1250 584755980 584756017
    0x32706100303080612070902090118090504020a15121505041a120f0d120b060c0a060e2404050307060e060a060503010b0607030c02040f06080109110307080d050708 72
    0x140d11419840503844100c000800f0000001c007542001303546080d002224070b0003005e0311804d00d01c5400c00394000c03143d040c2c1080100c60040d121b01402c8103c0100030b041006000403141020f005002e010881e5810489821a58900e651100c03503000940e005400c80d2420002030b0b0803a41c110142080700c0991009901a0a2200c40005a8001000042d1050040755100310b00541c1145068603540e448032280c250b0b8000158142d8107500031106001d145143c0715000480146c0e80c0000b8003550451102142141c1c0124a0842003165500c070303240d071503540d440040c00c40c2074190001007a20034203100100390550b0002c0216080000810507229919806281800928040c0c001c503551640c003151814040c40c01c0200001c1c403801d06104007040041e010f0902ea1a00303680d034038151081c00702c0c100200e0f005542c411801c010a0721510585000c1c000e850008602818541018021140b504811a109402c0f400c0c0070480c503100040c40c40c079440c18500301191103050381d05180b089030040c00c84540f508100003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584758480 1250 584757230 584757241
    0x909070905130f0605030f1c0e0d060e0c0a0515071401020315090c19210504050c0a08031201050d0c090e060a050132120a15060b0c03032706 62
    0x5401840144080140c00c0140c0c0341c3c0c0e1700806039944801107072200710b90041c0c02207420000c03102d0f03840160849039082c8008104c2e468004a1582d448800c029190142d4500010030300f0031041c840d41410710822900c01800030300746400070310804164200096590f100141190070405850030005522002400840d00c4c0d14024031900203d076414202e051060490900240c2400c0150741680c800c411004800c081d04080c000003556140d01070310340c85001c0707040d801e00c140c0e1142c442c0c051684a07512803400340490840c0c11052240840c42c81d0091041500248003940c1c4c24009240c10350704480701215500c010032310324241203075440785a030023103114142080190808017100003102405034055000400c441d0b07030384816880d14520304208484032060790346100400030303019514603000c60100070325403c42008003080c034500c1e200319044103c5a801c245002c80701001910b00c070b100002c0c445a803035a817400d007034541034030f4407403000a2402c004404000c09030b0114400f003107c83c1c54459180c0c005c4510300d0505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584759730 1250 584758480 584758519
    0x30b0d020619080c0a05030103120e030f1e0102090603040602090a03080310051c053c07140909060121060c030203040209071b0201081f15020f0606060909070905 71
    0x69200d00b004900d41c400890f03031455a040482c0d202c4009569080e0440c3d095035500003d040070782029004100e403095440340d03182e60034040d1130800404e440040210f00521030300140c0b1260391380a0b103605d0340d20611049400c1d44035042100d070300030b500060060380c5e0251940011101e401580001c0c004071008410411407007080080042610b07402c50b2030400316018181d071003410302e10501d00102a9000102d1164107500b905039484015000042c81104544503444c12102c401c0c4480302218099004090410045003100c6010491201c143c980e03a000b49041d001496a0304018418940c11030302244000d114108901100711310103a009000b40b10f007061510b00203002c0c1d042554140d21600301d1030082041d09001d038041d2140060303190307541d11420003a60019a000308000b48156500c0b00348140c030640302c20b03c0340f240c00064070340d10060f016462a43c1da4000e00d8403a043c900c0c54030303d85c45201070010fa07a480606442072031000716415081a0380e000c404072581910b81d40459041003440b1144401050b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584760980 1250 584759730 584759767
    0x70b0c0709050c031b0d0b04021303021809030a05030405010e1902011b0203100e0a0501050403050c0f0601060e10031b2003071e05190c0e150f01030b0d0206 69
    0x14280c01404951907100c50300301184030903904003091030781c0102c05d00011244e04014000340c0708152000618440d12801003410f0340e002c4c00c0c2504001042403414011843e0901c0c80d401c000180c0372110480b0b00d080c1c00010b039603100d480c0600c420722801100143c1048025040700540400007800d4501910060210313104500c44800120301041b81000840e1002d01c481200f050100d800400903c4218031401c0c2450040c4014401c1d1050740c0212400800443c409000e0207000718802e0395070076aa00303040081e89041510301c2d0880d1800c1e4004000421895a02440c03041032000f0444004802c0898000700f940240005111400000215041c0388841c54101031080200c218682e52103842d0340240d101c00d034a910540000621184880c214403440c000d810845981383c0784101d08403820340980d55860120700203500001c44800c100380b101444003000b00e08213590081003021b9248a990801c8002418402070321540740e040560700c00c1d00307001c03940e119500d0311100d5030040d0503075907542030707107180102c3c0d100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584762230 1250 584760980 584760989
    0x270a180507120b03060c0d06050402030f070e1c02060a0903051504060b040b0105040b07050106051f020d03140403080907051306030b010503060f010b0c030f0307121d07060e03070b0c07 81
    0x1000d202c18011004640d0098243c2d60038002d002d00016955201d003049103400511008150790768034030001c00c2135240d0b40f004500483c0b41098254045c98001e070000c0840301c0c0555503500030811601d0a40d100145000007004141c0d040703a065444610782c9108803144030865102030464450b031030007508101546040d45015034080c0780c050015068070703070500068521713040e04140041d104000410020240d0300c0a0000303140320b0400032840e541c0d075100040742c04040d160211101600c05407000c04203a010010340b0340780d06060406020380f416035965004c00490062002d4148550a80000e54484d024011034020f010000e16010049d8060110b0740001c02c0340d40402c0710881341501c004201b030f00d800140e05201d4040f101001041c3d070300303042041899401161407841c8078807040c401c103c50015841d02640c85a0190360390300000a021804079000d8904c000300301d043c0c00c1c0d894400700001140120700701e4165440d50814050000501c80840c1c6810090303840b480c0780c2e000101c4c241100c4040410428100c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584763480 1250 584762230 584762237
    0x1110d0c080109021c09020409020a060512061014090f0916030e15040f05030d1d2a120f0a290603030a0c02060d06090f060b270a180507 60
    0xaa07228603200040384928001d50f458451400b03440042c2c00d4194006c040791620191000c42c42034201d501060000440f9000f002c00b040000c24025846903054007003e501c650201d501c00d007c8000600090801ca168132030980c0f01c480c000594490b65100da2030030420010000e4500c40261402c04400c0c0c818003250101500003d003405c580c4a01c0c10030024041c4c4130140070081c0b0b0016a00c8994924101c40350004080352907000502440039040714510550946114100120030305101850800d0309100301c0144d0a07200c50880c0c205403040b14040022581e071031ba8180d9001543e502016081403808007102c80429007441120141020804480703140c5e592028801d0600ca21070744140014020303160100c40310f90301a4414002c07454041e1284680003130450018084925000c4221110002e41d56580c0200041d41d80b1840500315000191003500003c1c01101d0a1b5400c05560080c4841c0c800c841c49500581c01580c00c07510020340d076030845204010004600c1c00300c400700e1103080c1c41000e44803c8660302c020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584764730 1250 584763480 584763497
    0x11011b0b0c0a12090c060809100e030301050f0d0b011a1314010908060106170403090503060702011401060215242101050105090103080a08090f0d020c101704030c0501110d0c 76
    0x540301da001c1c500606500c1040305d140942094001c95401c80000c1c00325071544035105580c4a008164402c1c100100c2d0188040c41e038a606001c03c0c4030a40410b00ea0880c091035405100c900841d17030b410201c0d415540640341c00030032500400851001030040312422589000d00c5180000c800c009140001d110340000c0e02d4205840382d852803d161102c10922601000c0f50480043d01a551594000035074064803d06004072616220004203241c614101d420703101603035441d44420347d00900313840c8813401000e4610088c0f5491858042d165010380300a450510601d28180e040841d49880305a600150000608055810300d00c4030b6107044010900718020050794070f803e0020655081100b07826050740e810040003072500c40080000c882c0d030385004000b18054000d95100d5040d20209000621a0724440d40c002c0c00700c024144204001c101110000901b4441d040307100c550308001a4000d907034425018280510b40b1b40071406c04c00c1c054121a0030780380000400140850590700a42e000912100403075171079441c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584765980 1250 584764730 584764757
    0xd0b0a1509030b0c04080601090f061505090a35070b2b0b09040b1b0415020c090919080403060203010b0a02010b03010b13110d09080318010911011b0b0c0a 68
    0x4e0078030441c010151a90040b40050045a4041d0050284080740c0040002d8595a0b14607207000482c4011502c0c00081000565107094900700390078801422131110f0030103410081203a180c00781448a600c0c800a00c0f810310201041d00c50512000d4002e00311401943d0785c81c2c880c039035040f041d1b0613050805160304100d414810000303c110301c11850089070103400c030034064585494900c0780500040034441ca481520700d4a1500b42c0c52400a00003c01c819030350740c100c03204d05410290503d440f04070154003031079109082004030100000c580c001c6480d41b40c07009544403214100083e5334805e071303080504074038000070000a0071184130000b420304107440e500170400038111a040500b40c492907186c0c00c0c0d10807200b00000e84145040e520204245100858031884c0079008002c1c0d8080d06c40140703040e101a4000310810000400c2d03500c04080e00a5480000c0014030100c3e0f403080700703a01d4141d6006040000300012401007002c80307044290513542240100c00249081e03140300344203610081d410310002d0780400c4002d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584767230 1250 584765980 584766001
    0x50f1305072d08040201080406150303020c030114100e040507080145120507020306040f110102070303020709050c0405040f0f0c0c02060904021e0301030302010902010e12030d0b0a1509030b 83
    0x30190b00290b0b2a1240c3da1500c0d0011201c0031805403056130500d0391400710300084025100040d000f14800e030090702490f500d03181010f084074000c0c1201240f9248000810400c0018841c1510075140300f07081a01c003c0d10b80e424506c0c80d242c204e410010300c031741c40d10504071801d11000e11800c0c100480c1000c081c045102c01d580c1e030841a803401c05505040c81542a00c08000b450a20941c070b50f41c1080e00c0d0035801e180860300001d142560940e025111800c4002c54407083c031542000350880c80030280000d01030b19143d40d40003540c0d510103120f989030300d42c1c0e10808200d000401310111002404000d02c00c0c0030469911148100500ca4030b10030954603481e12150000382400b40d032210070b84a07001004281820340507002c0c031019600180b0403c00d01035241002100c8040c1000195000e1070081d030000911358214400980880482c0300401d1142040c600040c0784210008102ca00303040e070b026004100d0844860200b039903041030340c0180f07004c1d1201c042141a016806039002c4101d80c05514468401d484111818 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584768480 1250 584767230 584767307
    0x20d0c0302150c3a05030a0c050702060a0f0207120b1006030b06120c0904060b0703030608120409200a020d12020712050f0f0a0e28050f130507 63
    0x220400e030000084925000b0200202c0166002d0343c4144541ca103c42a40115071302e80c254440d440070800c00300500005076090b100d81200110181407147c98010190001030311030207281c00010802282079041c004ca64800d008070f20040019003c0c60400e030080d481c0540c4010022685941c000700c1504c00022244e1180c081c0c610724a4004c3c0045141403400107a02041100041c2900c00d401020023011045d07850398420701d0000e04202286039110702c0546001403d5070a01e5210207203e40c0541044800ea540700303011241242c00158000421120f030100310340785005040c4854480ca0008607150741c45640100300365145180c00c2d50b800104c9107407400c055089008155000d001c1c0f0b54448500031915008130010054810ba038121a410a0907011001e2210b0707101101041c00a40c0c1000d5101a504119000507180d1030418200700e00c2030080004042500749501c1410711420380e5000b62059511440e515650041015000f40100c2c5092500513100c4412000203040020ba20741c04c081c0101c0442484 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584769730 1250 584768480 584768497
    0x9090601030201050d0c0203090303220b030402010e1e15031e090607081801021c0f050f1501030e0714010905060a09050103200a0e0103060801020a050d0c0c020d0c030215 75
    0x44c41e0400781c00042d50001042e1407542001540f10802c600080c1d5902040071f440310651800e0340407614608101200300070341140d03010441c10319040c028800140e800040415440c9400e0340d941005540c0220741c0008100f002e0650343d04001341800c030300c64600d10f030801140300d0341e01da141599489030b8100313500d00c5441040321000029007025011850b036506c50b0031f1305600040300044944403841c0e0254030f1801c88c0e1080c0c604039151225401d6a900e540300d90700801000911000041290b890400b00c075071032001d0014190702101e44500401c41d22a8005d82c0040c50000c144400c480e03003951241000000849683c40b424040f40251030000341d00d2400740222034246850360b50380e4805038908801580900b0008c220101d140102c150010310b031203400d0016181400c5c0c180d480300a0555542c00140c00c03600541c105035041c0e4010015071034420780110485407441b440981c00910784071403040480d400720325903000130343c00b00f0149084814010308003890b0060724000c0311241c03401465240c41103001e00c00c1101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584770980 1250 584769730 584769737
    0xf06040f0204090c03090210020d140c01060515040e100303120c12140417031e06010e04020a1206170a0803060a030b0709090c020304060f05160b0a09150603030c080c01060803120609090601030201 86
    0xc498002e5106030014103424334012001141c9503880b07074005622000811081c4404107800b0030100501c251500c02c0ca83c01145004020782c1d05030540e24010401c02d07003070400144140d103075841941c580f4454985a24003c5030f40b1400c1090443c101882c9448030340584041c3c84540c003c03003001d00809000c00460303003c0d00f00e00d1045980ea0903c00710641340010001e142034103008151104a0f075907110390000f060059030f0341c4e40755000c00000d02c601404940d4190024401c885000d5424440104006a044541078100c0007058030703552054001040300501c1d80000f04100c03502c000b4002d29035000701c5000c040d5000d07003800340405a07002208076036034041c038840e62001800389a9111a0030b8000c80081441840540c0201e980745403a03102d83c0e2441c90140c3c1d451840c203595171140030502c8054620142e000d00c5151080c010a450354070001c0002b90704100241a50320001400c1110880950242008040d100260b03915824420200c1301e41407002c8500398091f000d010300142d92040d000c503d15050380d90584 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584772230 1250 584770980 584770997
    0x3070201031b0c0212011e0c0f08010e07141905041a030c0403060908070b0906192a0c0f0c060e03010e060a0b01020a0507140a06080f06040f0204090c03090210020d 72
    0x1000c02c0503492803a401c140c0ea9560300c0d4001d0f1b06928491040c1c0b00e91f45051031000c00c6825400720000d2062024070303060020002000018051300d560307080c0c005e41204036464101100d0041d40c050703186500c41c00b11001403c9164141c011901a0084060b0080781c40540252104062040c845c6500d44012a07114002d00340c104801e00014030603a00c034080a0f0b0241025604040850355541200c20707043d10626107039803109003003004c0c414440500c901c0100b0071100c00c0c0075980e09011030326075108400c011140700b080101056003d1074410b070f45c40e82c0055008443e40c9541c0d4070074102000c0103030300c50040398001520125002e106060501416036524a440018151561000c1c0c440004082114442d8114000c0d20701350b6000c1502001a000546440c4140101007980f81040040114031a80304400748000300c42000028a020810039a100d1016036010481d60080401e4200034482c81d0404804a85840c400b54010781d8154803141d0346501c203071900008a0002134090707944620b4400100b00254100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584773480 1250 584772230 584772233
    0x10e06030a030233130c1401081b070c0303050408060a0603151e090501050121020d0312110f09010f0207080c041109090421030903080604021c060803070201031b0c 72
    0xb0402000303003480030220024000e5282c07416030500c98045d03a04a00c2d4100c0e0111150900c0003483d1a9001130801c80042030315000b10000283c10004020100c2600c0041d01110a19105010040384c01e0b4681c0f20b4142c001c040c0c4c491401810540141c007841403184a03500000e5151489442000d05a80e000945100022410301064000c2e2408090f45400540c1d4001a503200c01c1040c000c2c006110300c0340700080f40c0d9605003100c1030400ca9959184100c1110350300d0743d08001d0703120a4500c4c15641e8052814180180c0400008405000b044030745c000340c04030015083da6500e4800000e8903525800b40e0f6070800e14014040301b240e44841a000e051070340d410880c0106990300c0c081d4000190081705034811070518145000040c07506d00201d4013610000c0c07201d000c00d000400404d000810342151402c00300034500c1d0580303009008180080c00c05000f142d00007011002000780b1640910107580e11102804025201d81c60740d40ca9400095003240800c2c149038107200040e01d075501140c40b180042c1e4511803011105d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584774730 1250 584773480 584773513
    0xf0f03090f0b031b09040b13090615030f02010f0e0d060e0609161205010b0a0905040c0e0c070209070c050a080c10061a070f060903052106030a110a0b04030b010e06030a0302 76
    0x20400d20740c0a541c5000f9030113651203000d40502c081d84401400109c4040900b40101610000600186400428007013800041c6d401b16038100e5254081c03070503421a405885045d01e242080ba01042d51000c8002c1e5500304014141d0014091b042e4a541602c005403160078509a0b1202c0d0581a039144490301e200c14000d85081c200114a160300400020501e48030803070100e0804003090704094111501c400402090100c1203221000414070385c0c5540c02c02c0d161003030a01c101402402e0009204440031380101703001c03620900c903e080c03441e007080640d1510301c1c16140010306070348107403001c500c40d0280f00100c20240f28184118000c6807a441d0401d408007414075050161039000700350031141c003100d005899021500d1032007102c090034441d403100303503480c0804a442c110344011580d46c00d814a842c0d800308455514041072442c00c0076130041b0040c207250350940008002d00095000100c1714030000c10000305002001800c24100c1c0c6844000e8102600c500c0d0915459461040c2c01030056030142103140d500140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584775980 1250 584774730 584774737
    0x30417130618050603011403010e0d051204060e100f0c020a050c06070c0e0f04030e040b031015051002010203060a05040b2d040f0e070b0310030803040f0f03090f0b031b 74
    0x1000e1401e107030b00640f210001200d0f030300280c01003800f114022490405904003403080c5554002d0a03402000c811080410041c410300c20340f2280d00b4544007803c0030904200494000e420360783d55001c01e82b100c19015950341801804c000104010250414103c0d600e454008a41e45810351f401c8409410a10742c2c00c0184030313007544520011910001402c0d0000b070201391341040140290103102413500c050519007801040e210f0f2842e05144528680460213200e95400602900c0001d440c00c0041060000d880c4910180c00c4181d00c5650848010249010655410b600461040c901201c400040b0307510790003400304540c801c1800c0e036049118502030090b602c078818460701412880071303244c650340100880880c080e105105003d0b03000c0e07621500071001c86941803019030080c000b090401403d62602c0b52009403040d0841c07002902c2d040c0d0000c040303400d000d5058180447d01e500030401d107090700744501d40101131161034801c2c1c03500316903103041c049040b86594085174020140490a1040041c0c100d450b200c0350742c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584777230 1250 584775980 584776007
    0xd03022a0a0f03090e010807240207090203010b04031e02090103080f0c010c0c120e01050a140904060e100803211e09010f0b06041802070c090e01020304171306 70
    0x840c1035a000c0002e20301c1d240e80100e8030f01c80d95699000c0e51501000c1c100e1300d074043e04114480e810480c42842805000580c0b4115030741c0303415172400828604d6000340c0c2072062541100218500000003c101c520004000b001207910400d81810609001c844034844d10b00803ca000b90300601d0140100080740013840681101180700d51541d02d0803118180032400c51b100302c0e2000021404440106050120b2188440d40c805c99508051802a220b440001c01520404100000307200501d00130781c101c2422401501c4a26202070302c10002c03951038040300d003032110342181e031482c8003554914080b0721820007106450000c4008218507849030f0421496220405000b00110001c84420b044580c004011030340c614044ca410800018480c0d00080c400c0c415140b800500c540200001c00c0100500c0e140c0c640080d141100140c00180ca50180385448010641580d00000720b041c1880081c05c01007c06600940c007070303032240c5840021010142e07840340d80d034002e202e41c8038080c1100300c104015543c015410a1000c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584778480 1250 584777230 584777233
    0x6010605030c1603030903170402010e010f02151014060a0905040917070b041110120504080c03030115030605040501180e0f0307050c0909030c120a020a020409060e0d03022a 76
    0x24040903c00030b9000150802a000a92610300003c00e1507000302c0400d00c5050440c0b150b00c89032515800103880c0d101d64200050400441112468075944241701c647d400181490384c0000c039041030842644810541d00a824918501c42052421440e00c101152a40026911041c641c149000108801031a10840586030041d105078203000300320440006016403407158580c2c3c40d2504050038010910380c40e8280940c01180190107001150360405101c250a0fa022400443c069032580f03001c41440c000d4114190301e23444080700109080403620070f01c801d403103510340d0100f000c1d43e0340c1c030100000e403802841000441401c0d01c3c01c20401c0b003030399001b5401242e044011202020301a04031645941c0c4610000c3c1c6041d0480d119404c100e2924a0101e9040100c1c1c00003182401d0844c0704440d2110113051045042080009111071254004d01c4050300040e0020800c0104900c0343c01c0c040003420341204203288034000d85901e1f1840718000d100356040800a08010304903000310990027426404002c5984146 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584779730 1250 584778480 584778487
    0x2909060105042102270411040c02071e0314030316020c150c0c030613110901080c100306030c150206102304060b030a02070b070c02030d030b220c120e06010605030c 72
    0x10660a1404000120420072140301903c0d003818008801f21210704102d00c03030390038061040f6550341e00103803001c192450f1008007030422103043d02d080b4559113550300003000c91200035903050340110040003841c8151a0200100c0d00500c1d100c00890f284c580307003442260300695500340302c1c3c00410548041c1683c031042c0021110140c0107000042c0c40c12104403280d10300c00d10202c02142c2006410290080c050006a0360f12500c2c4d410640d0035502c41b80c603211164042c4040d150858001e41c840d400440085411030406111140c4a50f092240000358903924800341c4202c00c04100c1003840a05140100c45850308400c1450240b04d10741d20041580f440d4859009850302000b00e02000060700a501620f200200141d40306450b14200903500300c01000f007428001108000d00140c3c4011408812482e194a40042d04100d0030001a10304081e05032444000c81c500034114103000110303805024024429141c0c0d0100c03500d242641000c2d982c26050103034140d0000d400401a99029002540d04032104c488501e04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584780980 1250 584779730 584779759
    0x30e01021011030115110703021c080301090506041b090315060f0f080c01090e16050706090303090506010b070c03080306030304050303070b0f0709030506070804062909060105042102 80
    0x35180c003542902c11803500000104800446110448062003050400328605507011811030380b180d074180300c007a0103180f00215030500c464039410005a41d661216000e505c950f1180c040400400c01110018040c624024990f804801031014007175201c00b85540d100e05450540e0743d032110501c00414000e040301e45800b40898808000c541c210003401e140c920000e0a03e1601350410301d844070170030006041c0a0701480920090002e01071349030348001449220070358003190f66022106485013000c09001185400b10b014101a4160000c1401500403412034003a6600c03a400c00b4030a21900c1c1004004040c0c0d56000c00000b01d900c0c001e107620500041c1a2424256203030f010a0541e4010981103400202d82005c101965030030102040c4c00c42031519002c030005046a55199807240302a0516043c41962030010b0104000368106c0542c3d40342d1031206480107612a10107010116010b0f40c0180704403020360020b40f442d4441d1090324215464146030444803251410260f1304100c005030f0607a00851030460841c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584782230 1250 584780980 584781013
    0x30b01020c0a0b09040c050c0a06200a03050f060103050717090109120f08010906120609020f120102040e01080f0c090726010e0a0606080106030b0f030d0504081006030f030e0102 78
    0x345040c103103e035038031000842000100c0343c1510152040c400b040c043c441404000280c1c110752542c0c0031000040c1d840075001c409070078040c1d040010041010000e20b040040340c1c586c0009001d00c104580480d8551a8140190281d44045481d01c1c00990b006445096100c00044481d800c4150000002413800007500d40300345c201038420845000c102e040da070440700e1651210003c2c5c0102030012042200c07500700b1007078040c0850851800b40c2165220724250040d50349418550758201c1c40100003050007105080d0141c0031303400511901d14031465038000020500c1c2d001c200008240c204002130b00414203528200310007407102038505810071565544460140c810307284401041c6218096800e0f8540c91316400d41c101180c0103140822250602c1c0d010040c041e004030325103054034000e0602044842840b004569040360fa21704441c2d00d803041c601d401c440079400400800075103002c0c100350fa4480b00c5c070f15080401e45480d40b000411802d5200d9403007010034490020090310b82030502c1500c03111040f40355004d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584783480 1250 584782230 584782249
    0xb0a030e060402030607230f0909070228060209030615010e0102070302150f07140c0405010b0a08070f0e04140f070801080304090b01030908122e0509100314160509040210030b01020c 80
    0x2092401c20000300320b007072031030301460040d2f114980780700802400c00403910041350090300311480c41c0400045031200e07040100c0c41d0155540c0b40c1c4058100c030341d10300d0143c10280500071628003040c0801c480c915003401c41d502c0415454180c0342c000d4902c0390144070780c550754511035020380082c40d030f55041030003003a00084102071001d09201ca420024980c60f000d11040004a65040e0702c5004604000c11070703000d245403c9103106900c03040504112860048510069500440c0c0003046944240381509500107941101c4055026030340000200f0aa6902d40700c05803503502e828000c8400c1031340144010070a00c00c698001200505040c54081424965680c485a580c1c01c103140c0c40119504450800900000e0300d0401c2141e8944401284140c001d804130307110041d03110b0302840380200e230b46200003054480840215402181d111000788a403e48401840741ca032070840c024580000a4503100145925016001c14041c9070003c0041d41d41c0402044285c000b0203c03004898150b00a403040a0015901c0c05500c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584784730 1250 584783480 584783497
    0x5060a03020309100501031101031a030708011a030a0512070503040513050601031b0c03080903070b0103050d0e190b0304061b090e0a090b070f05070c0b0a030e06040203060723 77
    0x5620b0341030078071501d4280f594000b481c10700381d45000010008030320910a0f180302c1210a00f4000b8000003500b480c1c0403c60350448801d0740500c00c200d80091015415070041c511000340340010b50400850404041e1146503100740506554010640904014078400050040c248a001200c2c6081d84e507102080f03110049480c0304c54615540c81c00c2250a58050040180c0381d04186801c85031090f0f0500040c5c02c9007901c00c40a805c0001000020340350303034010002c65090b80d4100130103503110340e5646006652200d0408046c4001205c41710302140c0c4e030628219190f5103e40c901091492203041010900483d04005c10a94016440f07042811204440c4c0b0014a40400c40c0e95800a9482c14010f610001d180003400b880005c9140040113804036403000021a00031009141041e540c51001c48110f40034011407601030402c02c403020000a2406d0180001c05682015441c01c0c040b0550004d9640d0300e450b0212000380d011380100c0005038880d446810f8040408e03c40420403045c80043e034101040e2a00306040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584785980 1250 584784730 584784737
    0xe070b09121903050703080a050402061902030f070c151404031401093e0d12140409050f06010807140c160909230a12050c0f2a0a03080d0605060a 64
    0x2141010302d030b881f03021f4982c0960444001d00c4907080550100f40c441c4200c414900c800005d5901c0600050310a10031503418080e10300303809449020380c0c241802e8050843c840c8911840451501c019218011100b904c2280400300001d41010720355180c1084001034501d090010f950b8a071400c0000035203000d4102044d08000c699081c010041c41c44d00c40640d09010300c60300300a800b100103507040385c0d5000100d4580581c00365080d110403491480c251400004201c10320080d140104010032035100c5a84036900c02c0154000c40341540d251840192035940058580c4000110042e03451000100c100c0020581650868100c85c0038890403082140f01c280c2c680c10100da09911041040c00740004402d02c00c07040b9013504480600300d0000040143e40d074868400c0180454a5400c240c2221406001501c460b000c00310166400c2051200c2c0c0551602d20000d054206940c181c01d4482604c002c2880f05c80508034040e11f01c1c1d1180d41940c944111603004a503001c9541600c800e8045499240c0d0009840c466202d900d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584787230 1250 584785980 584785987
    0x5160503120a0c03060b25080c03030a06090903020a11010908032b0b010918060b0304050a03120e0c0603090a080f07060e1606051303120c03030e070b0912190305 71
    0x189800266005a80e42404241c01c00b8401c1c401c4402403812603061f400c210201c0c450903100a401080620010301003e040c807940413a070b00c01c4050001c00110701c00e510946c0101300140d203030340181e8105d072441c01c4007400690104581c600020018522841c03d9030050500f02c03c2540d45000c80d918680c070408070f010888080c003240181268000d060705d8500401d0399414486001c042000078902c403928440c990408030380e0f44c4840e15032131256000030082d02d03a0940556403803070701d810419617030000302e0011000543c00c44030500d201c180901c22840c400860742c010f401c01c00b030b0b05010000b0740e40018014011501404520780d00081c103801c0101405014000c1050b1180282e00f085011642d024040c154643c01c8201c0070544544501c0441080d02c040b8107100d40c88040c103910b40750910910f40c200a0020b40c8445104100c00d030070099450300c1c2c520955052125450318800c40e5164002c2d0b1040864100c000d0002c1900303490a1504110119038080480d4000b4500180e601c0a040154006901044001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584788480 1250 584787230 584787241
    0x4020f040602070f15050d0b03010f05060f0d0b0c09030c040507090303080a020a08131e03090918080403030e03031e0316030b010806012010061d0c0a0516050312 71
    0x1480800e00038582180d03c409018a071044988a6a4008401c0305c10802c2c00698000c05200b15071004036151809070081142204581000c80201402e43d40c0511602e40b49004061500d1704622240116034002d19074191500c1c1c0b10001c40d5a50040d0420903818020010703180455101c03445001d1145001c1d940306c11a031451400c000d05040005040070008c28010032154403c543c010f030040382c000d074008851100440e5035043c04510492810b180c2e5200100c240c171003d0074107170300541e010156030001c2130801c001e910354000c3c0e035016004c010008101842c1030008002080c019036081d6800400903060300e10f440c0340b000441820958101c2d410644103004030500c00d441d44928401c51001c80107007420050301c101040080e1151078014a16410009500c030780c1d43e2750f882014825420385400100b1070311043c01c588009409130502d030042881c1c1c81c5030312102800014581d517460f030007100e0074020103140248500b030407181c41d80001d0408400c101141c06181c0010b00c00c200038101180d245014440d5030428 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584789730 1250 584788480 584788483
    0x301030309120f022407030f1103040302030a0f0201090305161d011d04080f040e0103140604021509060906030c0d05060f060a1808010606050403050706050a08190b04020f040602 78
    0x468000b19111029101c44a000421800c00f4090580d0120383c0120090500ca0316041d0443d010700e8104884400810000101600614551404003050b1208122006500b080603580d02480c0302c0603500d903100c5040500401d02c80984103203210700616000017100c0d101e0300c5092605103240f0f4071012125008408001000700b03080d02c050303252551207422086526106640d03104500d00c166001454014101250410040c00e0445401490161941f5227640c2e0f50f818090074400d09100545140d60b01081c2c000180c0d2012401611550380140381c91001c1d105c100503502150040700c5040d4018070104403481041c1d4814005d144100c1c10907a040ba552403504480700f060760741c09400c0381e0003006152844a05551094180c440001c458944001060072501203000f4100030b9910403142c9510b041c03008145c05038010014070980c1e000300704a400c0307550f039801c1c00c84d41c81c4a81000940043d4481d008614100520407080307001580c40c0da004a1250f510b4000107080303038000c011007800000005810008240c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584790980 1250 584789730 584789747
    0x6010905010f1409060d0c090b030f061e0a0e0114220510020f0403120c03140a081308090a06180f120f050a0503030f040b010b1606110d050c03010303 66
    0x3074034403030b5880c1e1458501001c5014008540b268803950001001548a80703800604031035283d08003076902c0355580e0300d0b44031500501101000b68028014a0f103c0311154800081d41030003a20002448811a80c264000e00f18480010340401103407910740c202502d00d89000d006030300307070801c4460061604e030425650250b00e01c0003000741c4400b008140803503140031600c04583d243e4054140d0070b001d80c0ea42d0650b20550b54520440e08002c00c1e100300160303028103032540411114260b074441c3d00c4e096801602e0071030740c00b114000e84040b80001aa400300103010200184010196203100e42c0c1c410f41401910780c0010410411750f00300400013161082c2540399070303560783d100c1c2004110000c02ca0b5503403820300100c940101c001d450058248014000d11108010302003040c40701c40c40e088010f0340d48070b0404120000700070001b5281130310b40032000000442c203401503a0440c0e9042d6000c45000ca00c00443d0b0360350310301a01b00d611441d94000320600241d0381c600850b01901d4400c403018580c1566a40c19441c0280c4802d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584792230 1250 584790980 584790989
    0x712051302151804020d02040501141806070f05010f0c030605060f04030605091501080109121b0611090a0306020c0d050724110c03090109083007140601090501 70
    0xd480c86528005a180c89207640c60700c800790401c069840505250710f011016418003d1038125100040d80d40720400c6541c0508103a40b001d0780c0d1646070b52840b030100b403098080c07140a5000e02c503840c041131095240950084c007a261040760203294481050311441c2c00c584030800310405440d100c07901820318990520a03000a04412543e8030300b0061803004520150040c0d0100030a456658000329030140c6041122414442240d81c00d03040c590786500101d80038203e0518216180302800412403480c034050020403e50300c0841da443c12062116484481c0503080982e680080c018040040c4a01c45d1901c100c2d00002e54041c0c04050380d104001c4c800c562030451000302020402c2418480e040020310014a00100244606040306560384590b60f118000e1511541803080540005400005003102001030801103409803922498940c1e5464081c2e1248044107100d150126182480e620040c0c81c0d8180004400038203103402c2c1095401c0e074804085400100d00a9a2230303116500400c11714049000d52405030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584793480 1250 584792230 584792251
    0x1e231501050306330a0b04090b18160e0405130309090b0d020d08040b0403030e10021227090405060f090f0307060504050c151308010e070923071205 65
    0x1032034510240181d25091300228500885141061140300141042074104500020540d503540340d074480c00f428450f0700c140300304089a800c1031061911490300300800303c0f0f186001c2901181c56035440800c0c0e102c10000c08098000d2020281e40e00d549501c41c2d114661060056240d0542c0c0f403405814040d10400341e40d84100b540c2d0303081c814056480e80b038442c0b040c6002641a228140c0355409864121a5030180c0d400111003210003140020905611806101107580c00740c0307d134a440c8240841c226101c4081210000012204200080c0340d00311081c541ca40419100152112040b2803130300081c840d0f2070554003520190300c9a014440040e00d1107040c40d0308081c6140040c80d00e00740e00c5500c81d0702d0307001d921030103020259203d000406200b4107202d0000c0455000b0442c541c82076243c1c012101e00e401c020348003107500d010410003040c0c05505105a000090380d80c4020203906240c102c0810103040c0510241d0581e100b50002d0100304003000c8100e40c080c03e030315100c01c1e84400c01003d101d812110010101901d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584794730 1250 584793480 584793493
    0xf0c0c080738090a03083615031506040b031f150f0909020307020f011a090406050601110f0c043c020408150105100c1e2315010503 58
    0x2118018940b0380c03100400030b060070b45070405035001404a240710350014107001000141e0128038a8803260358481101c140150301c41030140c840201841e8a981f0b1020398002c0c4c03135050b0122520200301d02039039000200c02e03450381c0c03040300d00e40114600d90020340c00542d2080c00402880380300c0b00c4071840000c2c000a194807025249142500800079080b5084030f03101441907108174003094911601c2941c010f0641b0700815940e0b800c00d1107000755516425610030f50103501c0c0c01e100320702c16401503282c0c14103203000070400390282d143d41c1c83d0800240400b4080d581409401c00006a48150502078020080c5d14903019045c50244481480180d40300582c580d034920900c000340b1340589180714194183e007058200c040310f0340f085003a00c620091081d60844001c0c0e214141c41e014101c03c400260700d060b01d805803240c0c0d24814030810150350302c01e20814000c2120540016294204d071070881030750034880c082d0f901818104011102c80c82d0034a03440c1c100324045c0d0403d807007455145d001b4001081c01080c060340140303503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584795980 1250 584794730 584794799
    0x4030602070b06061c0e151e01060207050d030e03010f090c030605060a0510031d03040b0414150906030c0403061409010e06060f010c05030f030a0203090d110309010f0c0c0807 77
    0x140010805c030040d041d20303621240c3d141c0046007003000303819650200d103a044150901110440c0040b580b024024070300e07803180300041181840454141308076280501030740e101c0324440c0d500b601e004000d800480c0d0199a502e00240700031040e401031212150040108035009407c1d0f04114003a941c0080c0400c0c081d108902042109441e420f800340b0a0540b01d18001071b8040b5048a080c0072950705001654880c400494080f0307907076081e00c008000b1038a00c82c0842c51042c60040500c100c00707088804401ca03c800500881c2420300b4414025507003d80c2c00c82846181c1a02c0795540b404a502e0b0300499190b1440ca01c041004200702407042e0090280100000c01081c50503600007012940e116600c0780c100202d081c69041046010800d641e0a049001020b5403240b410f901c088000b900111007c040d07501c07540500320100b6001d448004608099040039514000a42c00103440d442c03039030180d01e010014003100398001f0505800550020300200b00103800c5152a10541c01c500c02d4070300d00c961054203107400c591030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584797230 1250 584795980 584796007
    0xb0c07081c0804050c370e0403050c070b0316080106020a0b061e06030414071d0103030f0908011a010206010b1c0504050109020d0b04051c0503060f030708010204030602070b0606 78
    0x1500300c451800303400956071132420600704001c40c60402d0300440c2c0d8a00010200083d481c00c81032100080b02c803402490b40c0688114440e00c3c891081d130050b1966040400c1c007081c440c000801c0c465070940111000c40391382d0b05911400b9170089070700c52050300344c802059101035030241b0001c0c01000c1c68401054440e1440e150b041c001c1c0009440310303204e60f24a030041961482c074490042c1c00701c03900030305035034591809061800e96030404821802090059060100783c9564200c948882500301030406100340c1c2c25990262141c0d001030002c42d090044840001400d640240500b100c9410f6200d608030007a41560006460a80180c1210808074230604c030b15124521030343c8082d8521142444045002d80360350900d1801400c95402c00b0707421070705c0c6a00c6041407251200b82d15010300e01c684201c2d5420700003084040c08600c02c06540c50000b0b503041001c10410300d0031002841480c00c0060503625070565551186089078082da10466405802223540c0050110301600309074002029101585001071890f00070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584798480 1250 584797230 584797273
    0x2040c0306080c21010f050f01060c0b0403050903011d010e0d050309030d0513020d080309060a0c0801120c09061d060a0803070221010603150e0c010e101106010b0c0708 74
    0x21401800b00415a490011300410040d0840c0ba00078001c010880d02d000c140006403d045074041c52481c04100005601882189450306490b0801c041007015295541d08a4842d030048181d1523240d900c408101c4444114602c0b80384030000c080000080f03160a00d0310403402c284110b4414018003405004002004501004035081c10380c02c448002200e586044000c01c040340040030103134115001e40703a04001c0000342402140168a1003003112001c0da142e414000a44103420b001d03900107608100104504e045a50107014501e1055102e00c10f181d48689021040310b0340b941c0620300a00d00810788182008a64481030f40101c415907075517a10344d0038503040c01e940c0d1191580c000d000b4070f000040e024400c0c20862442034600e51110091080590f6428100c40185a0303440c00c516044c5410364550000800045140340c181040e100c144144a03d6810425140c008406000c1805007260240c080b15009204080c0a4220343c03014944900c2c0b09c003032491030301c19107801030340c05036000d462100c005003a83d0940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584799730 1250 584798480 584798503
    0x30503010501031e050c0a0908010203100e09030c061009060501020f070b16061a0f04050412030b010509040204081605030a050714060d1503060509070b040b0d0b0a1202040c030608 79
    0x1c246a1312100c400c8440594010381d06541038604014058808071010081ca94440b55a4511001c47c0c0c036036044c1401c074402a58200280807d01d40c0c100300c440101381c1e68a071b2107922242500d040ca880c403801d0500300f02045a07689003105000400380484c1c0454860b0301c01034802840102101c070403003a0520760f140000d0040e150b256002042044105000310112100035500c14004d10181402c02ca812a00104c414026031003200d12108c0040c00c1d0400d0b00c109403040c0e4001c10590903c2d5039100065000340240b0701210b0402008010020440d121400180010b08216008295002581e01e001440300015001700f4807d81140e0740c103401081001031010190b6445500089103465528001800382c440c1004100b1449d0800e00700c1c02108109004c40401c490040b03c00b808030b559040740c040d40750343c0c1da40103018808205000038000310b040ca0b00601280d0580c03080001300f4209a90008480d4a02d03136110290340d2003e8191903045041034040e0612801c0c06040c00d021031400c100030540c452161402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584800980 1250 584799730 584799737
    0xb072a030314073306060309052a040e0c211c021e060a050a020a02071a1e0a12090c0303050a0c08030702030c1b01050703050c0703020a060e090f04030503010501 71
    0x708003080c0688109004c109007440241a03034502006202a04205543e0700e000440c07910b005000103110740a4003e40c0f18065220002d0901c01c1c0d84541e44502000400c5800a45403c070f05c034890b805922148640c7c5a00e000d5180104a5640a40208100c512810f0040415443c0200d4444070b040e4001400407402c820071207001c83c091100c0981240703440c2c821000340350581010840c44c0c56003440030410b03a0142400600502042c0e8503141c3c1d110581c807400e0143d50050707010707442c01c2000300040d810034260686000309042c5010700d100c4003800444100221700040e990001042810030b60081000700c046140c0c1c0b241880315031415220b00403e40254480541031202c00a0f18001c4188500c03420482a03a100f02541d440303041285009507203800c01030401e0880e2003540c115100048248424410400c016507841340703066515603040350143c1104c00e01c80d001d8440ca030408401a0f0b500b4029030041d02c16aa03d8540406c8103008002074050041d1030a034183c0d000c00d06210119601504581c151032003800d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584802230 1250 584800980 584800987
    0x509072a0b010e191503051606050307050c1c03060e0a05010e040308040618030206061903150c050c01060305010506011710170f07120201030501320a0b072a030314 72
    0xa20303541103864907030744130810781d02d80300101100c480b0b0040e0074410349003da4102c0e0040030034003034541644860f900900d00455030601c0080c4829102c2c000a020700083d000135a1a90000c07090b0101d12070260005490100e41c43e04410f010380002c90800701e80c8a000301405110551521802c102411800340010707040041d05030000c0c040c880b044d001014160b4a1010442c070030f807134504009450b00303829a00b0794031501c0b14007a40e41c500b0710800684800c1d00e03080790101c881c07104580007010081100c0b551340000d1100c2884240c1d2144401e00c41d40c00218014000400c1501d04600011300f091410041035045210041c14001019000b01584055a4286480000061f8200c500e14584000360f202102c55200f40c0b0f0003c50720300c0c0740001012045201307032018011a40c8035040d0b40041c0c0242c141c0c002004001604200c01811113440f011440280a0240182503443e02c10900160b81701d403038207480d0a8880d084e005050b880d03168412018590019041c2c59190840d03400809071010300318561a4090b022 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584803480 1250 584802230 584802241
    0x303030e0304210303112b090b0f0702070f09020d05241e041802030f030712140d1a03100c0509060f04050d03080414010507080402010c05070509072a0b010e 69
    0x2544841d640da1010700085481fa140389003091241146a00f590346030b114801420081c003407044c0030f50312103198400e500f00e500c1e41e2070b2200721701d80c414014054002c41c810401d00040e03030b06104031010302410a000016980c1c03040c003549107056501c0640305550b940d8080b0303103180048590390002201030504441d900c664121380019080002103041c02140d020b440d049a9000b0075201b6807414408510039000d852480d010040310075100c1c0a100700140c0141c941a45403c2c5031489100064240d4802922031810108503400c074104540500701074400d0780d00410100381c1c8611302040a0810f90140000902402e6003043d0010110700070108124012071021403424208800304094070050310703000e01b08100c49485410010600001034409844400c0401050440e40d0010b0081c10702c036610300d484602840e141c6900441d07400c0c901d014151028017039103c01007059038a100c0c0c40c0780540d0007a036410b00348601c03031460301c01103d8464080100c00701c88560903500003610b8512903811903100504414442ea00c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584804730 1250 584803480 584803487
    0x30c03041e0804090605010212090307050603040f0f0b071233090e06100e070504050d1a1f14031b0d0b040c140618040b01030e070b040303030e03042103 67
    0x10008000c0c00200d0114000c80c44d82c20380d500c201d00b200c0c4240d0807641c03010700414840c861440b0700f40d0f1054140d0001c9905002906043d001150040e00c20800c0000c000706540b1220820100c401045a6003a00d45061000e0b0036881491001101961a4100405400d200c102148a00300c112206865002c000d03a06080100c8060780c2401011480f0052145052080340c0c6034585070110344112281240300004075208480e0800103124200a46807203190505100030000020031000d003c0322801e036080081f031020400c0c2c001c8240510503203109054544180990b1102c60003058100894645202924000d155000a282d0f1000d1191694074810130400201140100414070800340c00d214040e004e0008100c0c1081090f01200d2401d01c004080e031000d08100600781c494040c440b00003a11285540c0301500d0141e0206040300c40c141000140b01402c01040c0d4100681c40e07202d40952140402c00304149505409202101c10b10f40b40a185013a052038000035a01d05003c610b007440c61001c2c0301c2030080600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584805980 1250 584804730 584804783
    0x1404061805010f050a180507030b0a0f0c020a05060c0a1d030a14030c1c120f271a0f07031505130e16050616110904081905030c0304 58
    0x1c000c8000e10070601010385200c09003d06480410f03284e0b1a1840e10322120381c1203101c802a5680c010083c014442c03540e1911520510064166a103241e80d4400341c603481c00b81885060081c1c00103402921030007a4500b0041c0c00c1180c0240b4101710400104000d0030042d0b4404102d40c21158007100c210150331896021918010700080010104a2401c4d50781040e4280000a80700c1c410300364003210b038101c1023000b80d401c0d44848003c04c2da0100d80b1082020458007201e0304030490819107600c00003072020014107542d100502d91440c1040d4040303d407104a06100190302f00751341d0034a04064000b1a81400c1c0d00d0350750f807410002c0441c010556203880c2856810b034002c081000030b00c00200038414800c1c00a5030100106040311500c50a440394810021207030801000b180c0481e00d00400715402e10508041180b00303c18214030858124601601c00361039a0f881c14203a038080c40c0038442e415210005070751414505140b005082c3c007800001d00400582e0324086045941c056400400d208105d401c0c1d0b02e20460010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584807230 1250 584805980 584805983
    0xf0b0403140c060a0207080f39060d0917031303180905012408010501020c120c040501261b010c1b060201020a03061406090609031006090902040b0414040618 69
    0x40c40003503042012517000800748140e4500b10f05613a00310350103410182c0c0d117004001c1d40105160f140241d05100e1003a040c21000c0d6a40641e025511050100c400110703158458041440b00c1c580e00c6070f0b11400d2100301c11620108520380c00034145117007803070f0070005090400804024100310103a08000101c000d201808002421480c0c420b00241d44c44039100c00380c2e00c400b42900b064a8031441d86900005118034101c9049440607000342c0a5100151f0a000c007450030f0011482403407080150207000c94586115450081c4041107182c4800e203500105490b9041c1030900154065000d40000d1451665545200c0c500c51000d00b01402414071720300c0c0c40240c469608011020030340ca01e620010f40950190010909100f00303503402c0100380d441c0c0285540800b03000c000d03a074221500303100741807140c20104020150b03958001c04403803d1110b1040b6182c01d444413900031007051a201c2c0440821400e06d400b4600041100301c40500c242c0ea03100441107401349004001504941c0c40b8106000035500c18241340e03c1c0b1a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584808480 1250 584807230 584807239
    0x1917150a12111f090506090409050601081c050708030a0f060305011404020328082104050307020109050402030408090f1f09030c05180708270a0b010f0b0403140c 71
    0x41414003a00200d01c100101c1d0140c0280c00300201440d001d01d00400324500340c1d483e504c22542c10003060010326042510143e030030640da45810008210100640c5000300170000c000c00c2110b195000c030740c1c054000035003d0818044140004c42c0040d000c1c40a8aa01c050340f0369002450b81c4801803000040e11550b80047c20342e500c0c0082c1d8000000ca2020903031f100e10f00035130485844007144042c80e00722184c05c1c0c44016840a40f090303000000342d001c60040c900703098203054240c1c90080d80000c0500001007a14226510390001482004550b0818841d81c0108000c490460543c602900d4002407445441c10503807090780c0040703052620b555403010740c1c01c00c40c08040e100d4100c4000c0f804081c02080b264007044d540e480c1441070001e818600442280d440481d81c020404003510380c820107444040340580341c0d0080c074046581c22045066034070050381c0031148d000e0007010081c0c0c09042c5150401d0042c0c2000c1c041d00400b09017408a400544100c6045a82c881e110703407920140e06075100c0c100905c250a16911 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584809730 1250 584808480 584808509
    0x1203070c0302310f150b0703080c0408070b0304050a02030d170f070f0e0a0f09200c1e0712120e0a0f14010302040512030c06010e09060411010c0506040302031917150a 73
    0x10006c4d09000340c200d0900c25240d00301551201410303001c690080d40300e8a0041c4e8411081840200c0070003024540151194017150040280c1c2d0740000d0601210915000025100407848107141c88044241900200902c1c0a8110303403d00160080800206800c00d10500004403032900c1152a00030f1118010b003107100100200300e45880c00c1c1c002900c04a50662244000c20010360b0000803280704886080520b4001403a03080c185200e00f0203e12840702403070304640201c060018a0082d000c50501000f0310030210003000300e0707102001038012031600c0c2c4800d00400c0c1002003031061017110304442040d901c00383c0b0300b0290002c030302e40102c0182c491a00283e40001024201c501d12560001c042e03c4c3c660242400d03114103a1301d0702c0040c8a0302008075180c0000741d04c22030119000c9001d49580d101098070601d01540131901c5900d5580c50403100b55402c50043e40001008418030707410f00890316154441d460000b460242c5640d810342e00c8440540451000942004020700b6951480d22001c001d00800440442 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584810980 1250 584809730 584809739
    0x1a3a031b0221060610090e061c08030406020909070816050c0313081011070b0a020a0509030d08070f02030901020a1419030503070e01110604060b1203070c0302310f15 73
    0x84580054a80501030f040345e1054142c054040d80030842551324410741b54043d50341c0c4500700111000c0101c0612100381c2c00c40b2052011507145002148280d00917003000d42d07512040f10030702009010003000030301041201414419420079030400c14130454814170744151140c50340fa14803411440b0b00500c00448503400d440000c4c110784081080d6801390340c0e0580030040d41422400480303962040400041140c1d04e8032000603e035941ca070340034080020882c2703059400d02c03c0420100789002c136614450404102c00c0400c10854a901240540c041d411600c00f550401100d040042c0da103104a250040101429950800082d41c0410190794142061401d45d400d41e1a20b041c06052070780191821030020302d200f40c4008480d405001da00080c03075800401040e4541d1240c23a11801424030118150b0b1100501c21005494501000501080e41c014401c0e01400c07480c61040050300c4403418410360070402d1583c00000341d00310100140e412217000703450202d964051501c510004000c5540e54580c004019070001c039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584812230 1250 584810980 584810983
    0x20108131b1412010510120507030c03082205010212030a141f0f030321200d051803031b09031c030b0109181a3a031b0221 54
    0x20a01c1805440340120390b415403a0f540d00740c4104079030701c07085141d000700100000c10b202c1e034a84400c103000b00b054450a030345aa84031801301085d43d20a50341070b14045201c1c04000410300680018041418084407118034200010b510703504038003449030303501c4008070028055414542003190300c0b04400e09010b050f803910802203201032a4031070101101044150000c244410700785a81c1043d250507403120800d0052400303040043d5501600c2c0c8110300c40d2540051910001404464010b0344400b120f080d0300e80e07585003201030482d04020f02e0701c50450030f07641c6019800000071040780d0308050308040750040201c0c0c4a03038003a02445010090340e01403060304010780d041160070554005425555405000501680c001122145400d0003401010540461a1841c840440d401003003800c040341004c2081001120009480458844120115031810480000c0390890b4100d620f86600010503a164491215200203144032910340000c4462484500c400d4295621400420307044900c400d001c00100f020f284455 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584813480 1250 584812230 584812259
    0x302030c010c15091511212215060f090b01090b0f0f160c05120303040203071707170a050106051c030f030906020a021606321c1e0603020108131b 64
    0x5100d0f120a40040000c80e448010400380100e240a65401e041c2c00c0c04e07410082d40002d014230494025148411181c443c120364011000144120050070030075a207003400c0c0405071841c1c0703901e490400c240314005000c51030b90309043d100f815a18501843e11b81c1c2012912030030ba4030580380003422800758004000b0400a40942e00c2c02903801c113803010445182c1d12580950340740800e843c000d40c580c00c144003d01102c8200c52080da07605480d07004480d45103a0313a080c04443c1040641108280c1d80110800005128003402940010302050380e40050703048030360b4910254100e01800c024204450b410941240500c139030007461400350400030440d503c00c2500806540c07280c0c01c441074072075260310510000d40300d07001d140d101c221040b04031100c040c000c130300047e1a42041410f0003203020811052140c005002d8030108105848901c0110000b241c1480a4411500310103a0f4808005103040000501c0141d80c800226a0081c6100200d0b60181d10a860240c2c94030b103120600f44131101da60040090f5000c0f004070711 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584814730 1250 584813480 584813497
    0x803012301030506010c0b07020c181f08070315090803090d140c0d0323041b090b1804060e0303190b060301032102101103010302030c010c15091511 65
    0x404441105010064050f10011034031a4042011320080c000400c40e00c2c1211540800c035803054038102d407003840c0042d05d80200d0700e0404124100082c00c00101c107903041859821f0f503080110041d0315a103801c0c00c00d50f881507507010080501000191100c2d42c04496042040500d070310400c035907280c3c41c000c20000c2c0d44000a0180c00000f40c0068000b0200b40e1890302241d0300080040050408900411400d07005420349207444801c032003544803d00084646480f882c0d024520441030080450841741280d1030913905500840161441d241b00c51241e641e480e50b40c840c0d003060441c18603045d5640d0381000c070000c1c03070040e107030307080034003000081041e0100201d2240c1e2100d40c2d4442c0800c100084030051125600003408020902103920010700c000448a25485403a42128811184c20300a41d01c1290305803107014140843c001408001442180380070700c0341400e003440a2800b2400c5507d261500d4070040050001c09007140d03600d035410000c3c0200c800036070412a09a000900600c0c00c1c0940700d20055100821 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584815980 1250 584814730 584814779
    0x3070303022d04050402210c09100915081302030d0f0f0e06040902030c2101180213061407061401050916050a05090f1818010c021902010903080301 65
    0x80502d4101da510310700c180d512502040107814075040505101c000d5100c0d140c111150103a0503041100300344040e580da4442c06062030300c20b46500b564418003041e8003011707410700c05100301ea5a052180c01c1076458040054202890b04801580310f01c410700c0625119404003075014064844c2c2c00081d103030403101410070000f644d07881c0652000304080856007810b010304855400703802040304011244481c0c018541000c0c08580041c58034000340d1081e1442005111107200030385030103004020f01c08034200342803c0d217001800e007945031040e820311040d084000740c001d50041c026000e442c05014003c0d20251880c0703e52141d010004e2440340c181c0c01603c144e0900c2207502c600d101c5030020310b240c0f4800303500c2e4400d8181e0740c541c503003046000700c81610746410905030316800c10483c00e1a4281030780e50400002c21690340945000890410402c49089150345000305116030781040000c0100740d40c00910003480d000580d03491111030b1502e10048403140f8042d80060411000400042000100c502514030546c03040c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584817230 1250 584815980 584816017
    0x20105090f27060604030c23060c06061314070f05130801052502070306111e27100809150108060106030b1f031d0d030c0905040b0d080d06080307030302 67
    0x500b042042d02c21400002d04100c800801008a0444018040a2307018105903600f0f041e01d580b408038056801071011a83c881e800b05003400407508055110007200100c001c000d1010300107000b000c03040030401034012344c10042e590b5107462409201d042551084c0042d40018000c041d941c126090182c841601ca0418048003420075803280a44a50701c142250940e4005d010311520b0f507220b400040c0005c000f6070386103e20400040178900c1460805039000000c17155030b25114900c200b291241c160303400c44080720551441061820380d42d1420380c00b8016803224900940340b5600c81d10074a041175401c4034003003000b601000001c501080c010035014141c80c04c43d0b41c1040703014000030170080390a401c0541502c495142200d10003403a4800d410500c11000410018422040454243d51400f80140f0080c0002551a00ca07504040d40c00040000140b0041300d09120480c40507001030000000110002e00000d00010200c0b800780b81504494010b14026064944815540c14003034080d50080c01c03848a02c94501 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584818480 1250 584817230 584817241
    0xe010216030806061603050d020f040b0a081f090c020309100e01120645020921150907080601030b01050907030e25030f0c050f01020d0c020105090f27 66
    0x281665641d240035045d50700300d2000f81c2c40a5410760700410b140c0b402c5a40030800510200f8a1a008200805010b445240d4401d07615000038208074000d800340744440f84104120300036021802c6050150f032215107000640e28001a4207a1562190301c14494000a060026034081500301070030410342c4a083c2c81e0154607240381d07803800b000c840290080101c642100e00d90102c0100201c4540d055015004200130905081411640c00302d05d081452510265000203212149003003150b00004500345410f10a42da4240440c001912952064521509403681c3c3c400030712044d01c100074101c01441400e00b0f482c81941c403807c1c200010132090040358042e40051011400c0700d40300b40b0982403401808070160070790001d6294904c0205481c1405a800b4854060700400800c24a00515201d1352080c5a0148801c0c41c043c10321408082545426041d5045001443c12054100300e010308502d40c2440c2c8190f03204907e0001070550400311318110741141c5800e4000c0c5800120b20f400d820781024602240490340d0b1079 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584819730 1250 584818480 584818489
    0x80909070c081602010e040f0501090606141c060e0a0f05070512160909020d090c0e090a06051909060902210c1306051207090609020a05090f040e010216030806 70
    0x40e003000303009074020400071801410126400760104e10502d0850884c2182d000040d0a03540c51001d041d01c1142e07254010010350354a41724250040c5202c0c20044c6800410070360110450190f00e00203803004480e21100c034071260003580458050a4000c0b1180c20b282028170b00d86004103951320000b07003843e00d4080411012070060b400d880354080c040b0381c00041d50399407101d00700c04800030074608410301044001c0803d014655002808032840a4100010241c480381421301c8800c00a501400545c804c64050051a1001040d01c90145400c22000b01c1c4a441d6841c060032613903156400004140e14041e00d000400070160018040c0c0c0c3d000319200d03240d040d40301c01740900d01c0c0d02d2000b0302c18a80c1e010105c02549420920702001c2c44618440000440c40c2d40c0d400450b600e00e070400701c1070b0703500d421a00041c041d8682d18410f407809400e402d02d0860518900010142c6280b240c030b0032075481051050700d41502035a0b1074000d1041440244000e41d20382420040e110096130b00700004070041154100020403d041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 584820980 1250 584819730 584819747
    0x903050c310b040f09170703090b030705120103080909150906040f0e0109080403050f030c030406030b031009241e151d070909020a27090908090907 65
    0x1500c82049800c40c071041c1c0d6045500710406650050a07140c0c440501c00c1e83d254400e0826640e0a40e0000c01d200c1142d24001001480b444501800c03040248810404a40e20910900a581c1c0d040e50883d540d8548403800c0cbc409026525060b46800ba1500000c8200034a80340541501e42d01968811240c0d21000341414000c050004080c3d0007006080000d80c15242c0750b000035001c0010904005002210f4600782c6080d03614290054806841c001005c1081140800c8240c24a01840c00079609001207640c60310703202c0c0f04030f204040c2050b4880140c1006035800b8480c400042c404000100000d000e00e18112125540d0101c440038640558900700c070550384907004800e0041c0c510340c1200c82c42880040060000c3c101074942c0452004070190100760f2060350700715411080e510b5038070416a454000c1006143d1035480d0400710380c40b801030210008541e002103e001054030802c0d0040d80a40300c1032140300c090001d940c4140141401c0c04981400e0001440040000d04000d640040103a0350352442900c000d503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 584822230 1250 584820980 584821009
    0x806010f09050c090d060b04090602030c0712090602060601120f0518101e09061d0313050a05090412140f12060103060e0c030c09130c0306050f012309030d0903050c 72
    0x803190b000c490001102ea41c4040540d400c01040017800c01c03a034ac1c590000701d8208407503006403410001140c000380907200d4040524000540350817810103040c100c00035102e800207070030719060110103408018840955000b521004c615003008004a1500d46207004c2107500c41013200c009070140d0301101289800501441c2c203002c1c9a01d101c00b0710300e03c09881110082040b80c03c16a5441d50302c0203e0030784c0b680111038000d400e2903203100858a0390034030302d503107511118a94069881464242010440358865400403075000b41c006001c01690380c018174040c0c83c4414036020307607401000b000840a410b404140c000c4d0212100d217078920211aa1844019812500240101c5c104100410001503000032000002c55010b914920f05c0d0b42051042c4000c6000c20b010380400080d055201c10085864980c180320b048002c3c00122036002150b54114000380c401c14040307011140c1950780320555104011020f049440079640078003260308544064900030301c0800c003800201e5a502480181e042c1d10715000c44500b00c2c02 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 584823480 1250 584822230 584822239
    0x100905011b1103120c04030f030c0c0503010912050304320105100506070f061404030306081908160302011d011b020a0c0e06040f0f06080c090c0406180806010f09050c09 74
    0x44240d081c4d05503d8400240300d610005070401c008000150f807690100d90140c801e44900d214807a880c42c05105030441500018080d07858036601c28080b5081168500c204801424140e960751074902b00348010740c880ca00e540e80641c841811200c5c4041c07500d45503401d075100b000020011a1030b95209000079485030710500303600190502107070020500468441e00340310b100e004001007140300c0b009200f61700c500455055000c00c0d6903003400c00400c1d00500c00030446005078124070440035030315034854200380100c03050214810401c5030348108260003540251010300040c8011035141545445240c003174485000c103101c0008000340c0c80351041d800000ca031070105500071800e218103428842c410b000307030324001c180a07030091705c0b101c080311004a24412004101d82714540490703aa03080c0034120345419007807040c2c01d010b0305043d0208800010804192429541c00d4501082c40e0440c00c0505400c2c041c45802980d035901070a8000100c0da0207045003503003145c0011b0407e010f580e80f403801120960290b144c1c9141c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 584824730 1250 584823480 584823487
    0x11b2409050d140403120c020a270b03120708090a081609110d0906090b0105030a020114090a0b0a03021e07031224080c03160f090e100905011b1103 65
    0x1e0a0050343c006203610341211046080135925151100400181282e001c0810702c03a040000541c14058040c0000c2c04035101c070203004424400151f082111030581202d002691841e80e0300da10703901880381c0f00307013881d40034105601c4042604083c0000c0d4462030f441845424508000a0081400301e964442401e8000c0039441c403914200790b21020f80066140f1040b4108104a01030490300f1510076920451b008690000d4007014914008200b4501038100c00c0c8a940207104040044c8c0c0d1107001c2c2c2a081780841c03481511500342c2d0010850081e140d402c01d07200d4407030208416410651550203000190068000c1604441038044400580e10038ad244c0680083d50712044109034510300c0c1c00140542d290401604913a0054000e5244009980d401014041d006011080210300e4100105800302ca0120f07401c0741c48601d4140b10440280386c0d8800c4020507074030b401d0b40e00420f0f2028403060104411182c000c0c002c000252900c14000c0901180300002110f90000703036480d26100311070061104c003140004615 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 584825980 1250 584824730 584824753
    0x40f0f171e010615020a030f03021804090f0609081e03040809040b01090f1d0c090f0108040c1a0304120201050606250f110114090618011b240905 64
    0x2a9100c0180100e8030b40d242d60000461514111200100b440c15070701400228502c0d01e001001d42c0b803404e20000403d8014043e00da81c200d260761034100d4000d1b0444000501d64040d1829100d0444d10203006040b50389801c58510034404c9000092040482c50300d070396400c000c51900c211b60319000683e40680460024800c1c200541015401740307203d0041418011500c940e170319030350319031040103402c1084043d902d2079204120b0102e550303800390490341441880342010101004284090203403040b00f4100540400802e0a0184250b02d02007d4406400c84094914a14030101340710b50060b60206c4400c1d48480d208a5828418400c05000c2c980041c641e9140c02c0c1c261510000c2c02000103d80580d482000c10807074009442d190500b113155102d0100d6812500320328001402114241d649040c1c8018208a02d45203030380e5102c100d0f0802c03010503002100d107140c9000100d80d8100604016204401540024401d1012400010590940003c0e0345a034400484c07006e0415200341480041981e8440150101e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 584827230 1250 584825980 584826013
    0x601020f010608030d020319050a0b030d03200a18031a010503160b09040b030f060604060b0307050708030c0412060629030606030a090506040f050607050c2104050303040f0f17 77
    0x1a000210100320740b8016842907261b400b180c000342c8a0140301f40cbe98403403c07042820248103050440000d410100465504608081d000120700000c0448140001174005841c5000319008903038001c404118a100340e4a9140c0300501c4090704800c1c0c0548541c000000480345000a8001a414041a441c980062030010608056000994082d900a848042d03500540e28100b000780c13400301c200b100030001410710905100072a02c15030003651600004000b0007a2003a0404100e500ea5035124503140ea8954071440759442900031a008110722100040e00740003401480d0f040350701910b00781041686d41444e0a522505446a100d500301e12007402440003d0b03051038074401135940b01c101000c0200d025103080d03a41e1820000c0860b03040744c092500740300c031400740501049100d40c8600709080c1fa51410305100a0307250384410b06480c040104400001c03a40000300040f040d01d0003807030301808a076144c0d5100c01c140703042e40c00d04d40940420761300884d00008090200e0012191102080006030602c080320001a1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 584828480 1250 584827230 584827237
    0x305190201121b031d16090e01090206030c0d060f0306020c010b0603100611031e07030206070228020316060203180d03051204060b0a030b01050405180706052802060601020f010608030d02 82
    0x2900d1701065184848074660b060045120141031410f003040d40b10f0406503803408554101101010030ba1402d0038080041e240c0b1001c5a0300022945451074450b074094004101402c502d4100202c2c40790090000001c0010303035005030003030484480003805a29055420704c900740c002200e024540f200e5041d400c2001c0c900a000001c030046000007501d150001c048102580900ac00440c0c0302100d90001d125810300da4140552900011140301511000f41440381904009910400401600302001c0a40c000c5680410a04080c07041541e20350b0505642c034200130b0345940005400460304464913254944514000c5540d51100341c2c55158581440c0c400320182c162084010805c4458039941c00740301445589040603d00110310540d4454000d60400c4140829181c01403c044240c40c00e0100c04480180e020030309100382e84561900076281e0700155041000c0c0c020488080d00c00a0380a440142c0f069404075005228050a8084501e0030800b0500300d4207c1e40035100740801c5810510404030031100b550002c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 584829730 1250 584828480 584828501
    0x90903050d0203041b090204030804051002190b0108011505030d0807140706050a11070203071502031c0e060105030a0b060409030e040509010f0506030f03180a0305190201121b03 78
    0x186092640e03650760041240c3c000d4034160b9140506800b0800740d06545551180a403007a41d5056051601d113680750402030040380a15889035210840312800c2520810030029500c1c031860880e0308207152801c04200c1d102e000e006a0b900e0303508216104541d4001c010310002154809002000d440b00700d5102262142c00207489801040603514000095003412006458454003920000400c3d0800391400d20460749003484804120205101002c0544c2d8040340800c100c50000102940d20701544030120308610500f000f601c4081420204d298440403540e002c2c0044411510860b802640c80703000301a60783c1c07600070000300302c5403e01d00065014240ba40003000881c0c030074100582e4440140b000503041e035008441c6a0000da43d255601265502d0f14080d00341c0011080c2c01908140d43ca503100701c0d4803840385241e112034280321041c14040c01c1e02c1e040507000055030007806a80c1c0f454a035402c040226203401c10203074001100d440280c825100031f03102e0b0356030903540703121041076000698000342d0107415a00d10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 584830980 1250 584829730 584829737
    0x1e0a151e090f0803030115080103110d02060f1c0608010e0a3e0f01030605010903030305040807020301050403080f0f06010903030c14060c0a110c031504050c060a050307020606010c0309090903 84
    0x29010b07000800c03840c0600349220281d6125810580d1840d07881142900400c100b1118100400106003c5030300c1d04203140003070341c5102051042d400402e40910035503550205a000020303020840a140403036101040320b19000901605564064135401eaa442c0080758925400c0f403406040051b2100c441800072411352540303007020080c800c080382003e04c140c6058a00e200d10340b140e2414545462a003c00d05ca00d4242800c00c4024180f5000070407076140b40c000141410361b1800810240034844050350304855005000b03000e07a10b81890010310902040d11007091003400744000c2124003d2808120b44120010f03520130203260702e0360b1803c6030304a00b80e0000781d6405030318110300b5048110a0160a01c40d203500698159034500740c6000a00801c412105405c2c04d800c51800809550307008201c0f4650391b40d6800802490751180c1c01c0c00303810905044a116071091000425110b1107801c10003462186d01c03d50240e07442c59527007078015502c0d41c0004400a0000d04510f000b072040c628903174040b03c0d14038000e00c1d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 584832230 1250 584830980 584830997
    0x210111b0c030a0807020108070906082a040303021c0305151c05010603141509100b1305010806071b030f030c020c030f1024030201030f09021e0a151e 66
    0x700424245030040c9015112240002090401d42d40c201c0301658011650785043c604003446d10900400501c2e000d00451040c42c00c0130050f440c1d1608002082120360402e80400703543ea5a41d19001e0760307034144990140b034004421420031000501030320a461084000d50710824040e140c2e0010466514000c42149200c020045000340203e0000d10461780a0f40c80389025010008007146030510f00021200d441c04160180b40811098100214041005c1040c849010801200120001d0183d9421104070164945007a0001074400000176511380151402d403506140040282c504011200c500341014010400d41e1110282092007036014840005a07407041d40c000088050010307044c4051300098001c0ca50014020382419051032041d001640208182014a224948204040203540d0f11004e414103540f5080407001890703d41002c418140e00804240e034901d00e10000c0b01c0000264001075000e410f10803008540ea404920990358010343c20384641c1d10100642c800c60071022103d42c404004c10600300b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 584833480 1250 584832230 584832253
    0x3150f150906051314220c12090213090c032a090b013c0203120f070c1502041a0315060a09030f020402090307170d020a030917011e0c0210111b 63
    0x185110841c010030000401e10301f0317814070010040c0349203400c5034100c60325040d881c00059440c0e1007100c400081c103043c0410030b0a4182080015055681e00160003141207414055120408108108081c0d503409601c002040e220b42c06001200e011700105408034144144891110038488211519001e1018565502d8040440e2448000716403000c4540980c1c0041401d681401d00e02d07074200d40c00029001c86074454580604c006000d000452005440007215031291b074941e804580403140a001d10310580d4003c4200100c245000740e00407540507500d42c0c03100c4110182c2d441d100c0101e4440e800c1e20754034408440c1c15610ac1c00f26119400104a0780140d0801c030050180d1801c5c072142c40103048031821a80b4046032080214185800d82600c041190843c4410b14002a085078540040d100220003207034001c0e000c0f02d440e60060110300c03150104114145024103002100350004481e2164580c20769020100c042078040550b500c24555000f01c2c4000c1c860241000202102c003000c0c02c43c2d00084803d5200724 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 584834730 1250 584833480 584833519
    0x61314100b07030818160f0504060e13140c1e030d080108030d0b03031204050703140f0615030a0b0f1e06030703031b0f0b061c021003150f150906051314 67
    0x100d900174007042c900d0a07c104141d03d040e1260400800c18000850750302d00d040c0c4482d100ba000c08210050070051481e8840e2030700e80040080c013222190191181b04840840d0341c0f011107a1542c11b25062181c802d0030a0303900079a101e080f8060482d0310010043d8140030800040e50046d100a0412542602c000e0022622101c480c0340c105002e58080c901800e01c243c1541000801c8140e460f0440440d944500081c1d131030014001030155002048880d81d400211032180002e04007514610042d043c80d10320801d0000b010840d103040d6015a040c5010350881c05072030762000380203003c00c403546035040d00841e0003000031070300801203c8081c80c0707040c2c000c0191310465619441904001a015071b0080b1241c030402166003024503101c01e00b00410180201094090b5001407070544012546000700346d00d0b07210445108c01d203120004060b00c410780813060000d4880b4202510502040500c030005061091f00007012030080c42219014018003e01c4903056007040e00260100c610707011819082140c210750700601650 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 584835980 1250 584834730 584834773
    0x605091f05090705030a0b0c030c0706021314041526070e071d031e03160b091905030a081f150206060a051305061314100b07030818 58
    0x1110600001daa0501c2c403005454803801d6080326009a105407100404500485c0406922200d55201c482d0b8a5a0b5010101114002d034180280340500110302c010416618404210a842c0c40807100e4440e040700c04100700598080076081810901040b03404d200c0803078440ca246004100e01418522a5810b8a200511b06803d540c0300304101176182c1e092060207548440081c0100c10a001251070740c6413070380300203a1a040340d50fa040800080c0003a042c28110003e1082d240d1101c0010140c040207900c0c0d0900091250084544100d1801364540740c100425224010700c5140343c001c0011802c1081a850655410318058120100a00000c1000c000c0088000c0500c0c0603028a00150072401c0441c00701130f20f0880b001c2c28082c8500600c07942840b090b11600d000c3c440104e0603000104070b030307150400466001100c10a071525a0b9082052000c54039214040c400d00440d04541544c0800c0da841c0e40c03040890041c41c0c070040c0050192800b04402d9164815420700c590640c80c207584000c84440402c00f0b0415 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 584837230 1250 584835980 584836033
    0x30a021801081c05030c03041511070b0a02070c0302060f0909070509030f0c03030f070602070602040311330c01150306051602010b0f0103021c0501180522060509 71
    0x5250100600c5a00d205000150f2580c1021995500c1162062000341c0306010041045100c19000301c0020180402c0c1c404030a030704401c0440400a982d24022031a00b00d0b8008030058030112020004600d62007040d1003110141c641100410307000c54215420052981e00503503242010000501024009685004010340210300d40d40b241590b07004104c0500d4145614540181c40b030350403103010002c442e1004030440c2e4282401030b1021741e440442d85411002400740100181c0000e00c0402c0100400c800782e904280b6151007216078040180c0c1c00c0c2c6142d51129038000007007000502442c81e000c012405e410180c084200c070000042083c1c02220a00c9400c03050b00da00607100c0700d85078814840300c0500d403d000c001006e8944000d0104803904401f04503030111031401c0038105a4001041340001340c102d15400404a2000000d1140d569500815140100785259030007e00f4605804504084400d07680b01b0b10015140216040100c080d4450701e00030440100600002d01801600c0d5004004980081503950b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 584838480 1250 584837230 584837269
    0x7050f061803030714090105071703150603040c120c090c0369060504060f060c0209220c031406060109030b06040902040606020c04050a0b0d0f02030a02 67
    0x28500030301c0d424200036030100c801a60340c10401c244003100d540400041e8040b441100502d64950031400121541e11400401901c041710050000b000c2071006c02c000d40c0a00c40c080e02207141822108200102c82c813054400a1482c4000002082150000c0391151080e44c02601900c25680e622040704082c0c4e00004000000a0b131754040642303c1c030703460407111170540000d02d80a4804840c0742048450100030814180468038a403203203080b16031480e107030860118070106111140d1456071046000a0082400307100d209609280c4082a510703601c41d50082115201e5075054001292078080c40107007800076017040c820358260700800a0002080b82c0d43d0074544c0c80b80d01000c030814a1030a10303054620382031051943d250000420310086071ba03c480680c00380c0340c0140f15040d441d25800002401450713070420080d005400c0c91000261a9000710340302100759420707241841281d03103686184040b541c0075505654030241d503a211101003105c84021401c0548098101d922154081e0000780c0007045031001181758 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 584839730 1250 584838480 584838493
    0x120f11030c1c050105010e1e044101120c080303100906090b0303030718050a060906030c1e0e1801030f03091e03110619030e010c09141507050f 63
    0x544a0b01d4140701451811035a0400055040c003000810307041c910503a140c4100080302c4c1e100350200c010070060525100c000e004204042003404e004200354441064450300100c03201240c00c450050242c1d407055060030480140c0c543e8200f40c03800d8074030750b4003600650700311005110200f2440c1c010001107004282203844078100e00e280a1000054070190b401c44644503080c0248120551000000c0c0c940283c42e0341800009416072072505994401541c2c0001d5004000d04030000f603490300400d541003a81c8040d030b02401604e801c1c0c0f034140c51200b034241b04500c40450042d00d0b1802180329424120611800815885481c40382c85546280c0c0f1800381c20941d4512074200000003059001641140104100701104141101c402c10254005040e44009005402c04950310022641c0358821103962400300c0341202d10220a00340e0090050494001d40c81d829880d0150721201036000d1c410020407a1a01c003400d550900d2140c003070000002c03921101412500d4203000d0500001d0040c0182c00e01c00031003500400a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 584840980 1250 584839730 584839747
    0x1e0507060e06150a0e070c150501090506010f1d060307090909120206160e06070807050312040302070807180e0102091002150a05011503050601120603051b010906120f11030c 76
    0x74284048202180b1138454010100285a050116a80d2006490624034494640380c02c081d0354448140c0d6a5900d9076150030f00100d908403c0c0e034040c0c0d01940c0c0a90b038070404c0d502001e030180c803203858928a2401c2c0d0041161070359894a01a0003c5920050078600048a01d50790519041601c00c6c0180480345942c0801140301d07102d0781085200e901c812100c036209110140300102904030404014203d014075000100c080500c0049411990b070f81e94000222075460180d440c00081782501542c04800500a450300092943e100080d54000c0e0790312180c0b080754100b00200d2403070042441140101c4595002c5c0024541655104100c2c03a040c01e0700d1700605501429603040a92241008201c081214640340043c0b1014514900f00c4102c840c103820b00095a84842005854000c050185000c1c0a03081c84004030400c000401c07a2500c1004109001d28625080d40c0155403181c00c0c1c2c041c1400003240c210001c2035074001908200c0da04425884000b0700c506500b4210861540221740040c100e03200001c601304e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 584842230 1250 584840980 584841001
    0x30506010e1005150703050f0f130b091005070203010603171c020a050412051e0c1e03032205040609060602060703060f0603020d0612111c02011e0507060e06 69
    0xb940028102003100c02207050030002036481800b84000781210030041050010140141c049400003545060015200c0c03c0104416440d0392001846210a10280c0340018440017040240d0303841000040400c015010710300c0044582d9001082c1c180d900d0341d01c030040003010035040d0b1002105050100f4046507220ba0840b13400100d00907218444400e0703441006040d10f000d030b00c1826207050342c541c945000009906170400f54074149180d01e800084140034407480550301000101e6000305079080d25150560342005071020a582e81241c889501030f0020000ca07040031a841e6400300d0042c000f0080022451340741c2d400300702156802d412a64150fa52158140101501003014640c00b100c40c1c03906018040c00c006240d10000d445108140c14980c0100d01401c000c20b2a8109601402d0b8040d190201005c5904001c0c406000a01109000701400002d51851800286061001035010385130302007004094408601040c00c11001d00c0300b0080140000b100281c00f03070003101c05081c2d500c0001c0c54103040224640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 584843480 1250 584842230 584842259
    0xe03130b0a08070e01080c2208010e01060605030105090135071d040f03030c021e03040618080d0516050f0c030d11100507030b090109091a090c09060f040603050601 72
    0x9030900640d6144001340307a034003401c61640a45000d50712622001550104441000031403003005c8101e80c4c0d8517000c00e01c814154070088181001400901900755070705810b55541c03000380038540d04803c3d0600140b10160b01e101000c9500d5110740c002201d00036486003130f01e0540c440f0041d81e0301250001c10b01001100c0364100d402c44c140884c600c2c00da4880c105560344008000c040748008003415100d40c001c40580b0300038440c42154048079100d6841a500d10880702e0340300d5100307005450111341c40724051020600301d03181c0b4005030340c0040c00500213281401c0d000e03100350f0406135010010850f9044c081c00001c50621412240c010020003d12030a41c204d070401d42014008440c0104025000c901c1403140fa20000b001da483c40203100c03000800d61a8200210040d02008030100c5e00608088000a01d0440e1036001218031400b80c0f204a00440512280c040c80074001c1d0b0310100240d1100003040c255180072500240c01141c01081512003c0020000c1800e80303407075034811307105500b2a0004108035110001312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 584844730 1250 584843480 584843491
    0xa06141e1c0317072105100f0605130e01050105120405030d02070605060307170d110a052b0c0804090f091b0315020405240408031603020c0906090a0e03130b0a08 71
    0x250900701c0c40790b04015098035005c50301001c00c90321400801e58000c42040040003401d00b0094407482c680d102d042c094159400110b90086189001400043c611508503283c0d040e070b003050b99054503000c0c1d004079400814030003400c141e074980010820300b04244014802041c855200f41400300d0203140013403c05040038015480401e0310421a1031080f0264070200c1c403050120801c0c208006145042d01c40c00e49020000000144240302c0d04650081100a40740707000b04202d09091007841c07940a11b401191513561010b13008005c0c041c144028007003a031303286d002602c000340c821000007900005516080c0b4019207000e20700b5003409034018244184581c6580329002c40115040642c03410385000d000c100854085000746041081250903a0031007072a03042281d0050400c00300716500c031903100d2640c03011410f015008401504c9440c100c1c0e0024180400b03c3c5104500c01400c4084640d94004030b0000303010070800e901220302040040325551468022820040e00300c81031072540305d090b40349015044000107001d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 584845980 1250 584844730 584844737
    0x20312040c031a10170114070302190f020a030e0303130605030907050904020f04020702030307120915020f0705190503010504081803071206090c031a0a06141e1c031707 74
    0x4102041c00c041c94800c0440301c0706a0306030360507816050300764010241094900b01c41f0441b08117000b21554180c01401030240e6000b0341242800b01c0d150700f51046101d405028001d60031205022004c24003c0607411100c81d40a0709a915000090000114003101600140301086c008400d02c148950100905006020269011549401c09400041c0c140503642d42162281780c00290301c004545043c0b0a03683c220341d114451000e644081d1a026015103140e01601a8a0080807800b13540f90f03100241c0107088005680281c40302a0800040c810384040c841c007132400b0341c0b940400018241d10b0034829948201d00803000d10362034a0700303010020400400c20717810901c40c2d840007000340080b410141001013145c0d0702c00320015032601c41d0b10382460307600c03000d0380064200d610585032421011210081a482041c0d0320208000d6983c49040090f43d0700700d003405842e00041c5031074030a004020140340d510382411005200745914000403052140309042810100c0c005013000e44c4600021401c0403442e03802c402c1c3c505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 584847230 1250 584845980 584846033
    0x60d14070809011a060f090d020a14041b0e0d0c050a08031305180f07090e0f1603020423030f060112060e030406082706271603030f020312040c03 64
    0x90018825020b20840b1340106d0310300240f2610301780d49441100c2403555006d424112401c0d81c401400389001c0c9050100b500480c10000b804c0c80c5030501c044549148840c40c3c5138810301034800814403022121a120031a0682a21800800da81d602e81101c140100707004001140d60b40e00b403014456082c040da038401801a1061001900c40700e60011006a100d050310100d601c0954801c40110b41038a40b03a8810280001c4000a0040e0000882035a6100384584403104a504411a504800301e03c0350384160030890602021302c44e0740a8035500e031411240070003001c58a03090700c021110350400d442a0300580240d0300d004080d004101040c0111075444c402813014504051402c1c00c0070740680390040c071f07139050700040f42001406140c01c0c2c4402c0c0680e031078500403240e29261030140500124001030280d900500041500d01581d800001c130100c0365110b608245035002c0c40d50350161201852000088154002440007910450040226a1040e40600841480780d450760400503045907441d0040822809101e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 584848480 1250 584847230 584847281
    0x1311071b05150f070f0b152407020607060501170723010c14010c210e03040308030618070c02040501060f230f0d09060c021b060d1407080901 62
    0xa001400c1582c0c0070808180c2e95400385030f510046403003004030041420b201c21501505000c00e6200d264401d41c0111006041718500904205066002460074204c2410030100700240701c0300c4e04003a0000f0703480541312500302011365464506480b0243c104628107000c2500f0f00d015800d04108010090000d082d000e010110b441c1c0c0c100d03a03070110004500d4184501c0090200c00c21180780321309851616020001c100240442c0343c001c0c0405442c40c10b5030391030a01400c2c10408182c0d0f9102d03101030b04441b140214949841e542d600c104030b410003451503a01680280388500303480c0e000c2510a20035807040ea242090301c2610710411048650681140040198440f149000c0c0c2d900310a08140030301c0074008942048442003e0843d940c401d141051030302e030708040f80300240c110864003d408658400c180c2400b0380001100203d03641e02d81884101c2c14401c43ea10580003d0620300b0007070403000030705400130440d658404440c0c10741c400c0640c1c0300c2002481e0101000105c40d0701303104a892880c200d100010901c04003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 584849730 1250 584848480 584848489
    0x10080103060507050d14060102010507020c010207121719030513050a02120f07120c1d1f0b300c040501140c010e0a03140310030807021311071b05 64
    0x1404024031140c2d880e07011506180c001c0c002e072080010b0119003803140d40c45041500700d00d2441900c006001d503003400042a206400451880040c51040e0b0090003040c0c43d1004000c0705143c11582610342c007501084504900ea04c030b81c002c104602d0b40e01411844101180001000c07a54001c041c0842d958108000384009030b400b2411890f215011640c000b144c00003198883c0c240704000e040740d4081e1003801c0c000a010b00380b401d40100810302a87d0740742ea0040c1d595051041520030301381c0000481a030040080c8441114003c1949203034542440c15402c15101e070480320960f4010307500781e41445000e21202820b043c441c1d4507103201071440e60b50001c10381084010080d050280e40109414444601404826120710340181c4030441c40c10740081c0303d204aa00500c130b0f1900007168040d00000c2a4403191600b20607403008580c02040ca0329009009540b8507211020f5541003800120390000c040c0424403a43c0030341d0b00402d0601e80e54240321550720903640c40c1c548281c01c0a064400808030003a0b0b8104125620f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 584850980 1250 584849730 584849747
    0x20303070f2307051e0f06100602060601050d0b0a0f05120705012319080412020f0c040b0102030928060924091226033c0f090c10 57
    0x80d8400503500c0d5600d51420905100e0252492880b01c0300b0403902c03202c401700000c0c1801c121007210058070b0f41c9403200d00141e40c000710743d40500c102507400103001c42d0702540b04030000c0005d18482c8600150780908413000444500196002224a01b400700c1c044c0410b1400c0c4551090205030440108076040c81c010010340780401d0721154a140e1805140c00e034008400300340440d0041c1a010f03080102c0128420300103070038032105650540d61751100030802010a8000251103485400000c02404c0d001618020071000e803101c1d00015045000c00e0101d61010385a119849125004030502c450b4400300901024608114903400682004101c4008010752062487c0c10480e145c20410307044038406d00f80e403040d00c045010340e209000c06460441c158050160355102d0279402c00c60829690f0301c04010b00c0504000d070106030740406601500044400700c07000384194001c90450100c48008194200c00c43c810b00324081290b403804103c5c142c004100b2804402c1c4a000d14100048521130819800007070002d22088 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 584852230 1250 584850980 584851037
    0x50a0b0f06090a1206050a05160c02061b1b1e0d140705030304090e1506030c0d14030703051c0203070519090b030429240406080706020303070f 63
    0x70000b4680380c1070b11400250307009403c1e03030100d0405414403840d0010013058120340702a5028540303804603200344070718003c00f070742d000075a0f40d040741614403a001c0100d00c2c1c0c448100c031807002d020150314a980c0d010038030144100d0001c200c0d1200b458410f40f401d0000d0f21035190031101680904003c07150582d0345000e100c00882c4e810909125500c03600c1030a0910b8640145c00003903040c8130102d80051185295004017038a40b40c42c00c145c2d00c0d003010001d100c524032217050319507a62607006001400821700781088803000c554002c81103440c2c100c1e011044182075600103982900007400000c1c2d4000805c0081c0c003458105154800118554500414024503900074499000e8001d128000c82e045194811110344011300b090036001540c9040502e031800b06840f650034106c660000c800020110451040c808a201d50507000b8007000726607604000e40008bc0071000013a80c4940e4556010545001c10001840a007205800440e5241002c0704007810350000b07490b1a00c10030082014003850b207020380306000c0303610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 584853480 1250 584852230 584852239
    0x120f030e030423031c0914010813020f09070e010908161e080105010914130308151c0804081011120406021e0405040c140301030b06060d0509060703050a0b0f 69
    0x2c021a859001c054038455941607041c403803081040c00340c240a51181e80004506d844412016a4032405c00e484600400d000d1404a141e90001910800815144c07182e405d100502c007603403004004000418000301a0b860100017822240e03540c820796040007030103000d002502d00800d01c00d9400000d402c4542c5940c0580202040c07245100c134030302a00820210003604c10b041c002c0c44190f0b10b07851150021728600b043c0d2801d0000140118600e00851200480c0d02034041d9500001c582d200050580d14107078112500d50405101224844984994401512158480d00f81103503900d2600b441ca901d84155071821810007071034000c1940c420f00c90f920807034001446442105c070241d41c803420140024000e02920700a0842d01d000a858109a428014425100106da040156141051045905803549802c180760380504000620102d00c25101c07440e44080b0080c0b0300da00d0444003290030015a842600c1d44142c60b403000301030044c825018090b182d8010301040040220703501820019040c45128422940907 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 584854730 1250 584853480 584853509
    0x607020111010c0509040c0c030f1d1e010305090d12090305120a0f0e0a08030a020c03070203031209210d05150612040615121101051204120f030e0304 66
    0x8590090491007480a64030008000000c030703140d00070304240e00c21054039201e645010700018805000340075606001d44c0680d03500c0700181902505850740c101c00c0c2a040300b45188203810b484250b4034604081307884440004241c4d0702a0800e00090140c80340075100c28500e8202200110307000d640710312411104485440f000c9100400c608040da85407150602e9805907002040411490200d9500041852030100c84104012a0880c1232951100314041000b407d440040011850089498000e02400b02c01201500d1500c400b035070010b4a0f5522405c04036030244060020840e8084003401400080042d0300d022154821078110f00c42d1503441244118040710b03035107c01041018003000d0101ca29000e01801c0b280ea105d0411800c051588403c0300c04445075410b00d6600b0946151207130001040340c0d140f08950300f2100d81c5954024600a2900b1110304100c03041c80b130004d600103402c9000b0302850003881050100c1407002e00003030100a0100111050504107210344030462000002c6908445981c0c40c813999 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 584855980 1250 584854730 584854733
    0x3040b070314040e07050304050d0e03070504150f0f080c03010b10032a030603230d1b0803010b040315110a14070c0b03010f0f050d08031909030f020f060f060607 71
    0x41d6000f540c00c141d407807207113041c00c01c10803d8000c0e009501580c0544101c0d521301c16030900442d40d01c00116071282d05500a900d04100e141000d030441c907000301d1100180a402d039144d40d89104842110b0b17000141d00b800f1800b00b001000300901c18459100020f8000780440d5039018042400c004100c400c2e80100f43d038410711301d41480070681444c02c00c031806840c0650030001c00c0c13500501610b032900041c0d0326000040840d19161058103100e000d841d4448018203410141303030005403612441c07150041c3d00c81124410020004d00404011800303031460300c03261a20b642c21030804403066007450040062003890100501084142003054a042c00032a10740364612054400d40417815000314403006041d16025200820740ca20380c08040e5050b01d0411041e09004d0342e03520b443c1c200c40c0c2128131500f500b00241200110205415000450340b201008941442041030704181200302d07a600601540001c800000151b22968180301c5009100994002000c050801c00e05c9500352040123002944100c000155110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 584857230 1250 584855980 584856017
    0xc0525020a2d031101020d08011a03040305161b05090415021804050f0604050f13110a2103020607051201150c140d0806040c080a0f0b0d150e03040b0703 67
    0x8400301420b010141c0140d4a10f44030700f90125a80c00d460140c0a0101c05441c45841190210304031070310002c4445001008a4202e4000d500182042e001c00a0801249004200c000340ca00ca5076842030221200c0220b03480d04196a40e681030304007a00c00d8106070709120104511a0b24608203400485005030303108d8000000a040c1c0c54809181504503003480100403103040030308103030b41c81400140d03401d01a6584204200720300c3c030300441f081c41c2001c460030307001c1d00850054581100c45440151610300782c0e0b61034500318880180b401e01c2950413087d1b01c01e1444101541405595040807a5062490a1028a0803003101601e414040c0d40c0c404800043c3c00c038400c503c100848444a9008600001091880102c032502c641442031140d003c2003034072020a581d0704103403181c0e0b6000102607840280e00d484043c03012024102d41c0d03a0f0100800d88a811440c0f4a81e24840d603480c02c5842184403503060380c40d41c1c5c928400d9984e03105030001d481d00107000403c1500e202d0003c0312515907043c50000a00052a20181c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 584858480 1250 584857230 584857289
    0xf0b060a0e032a090603010e0a0627060527030a2316060c050306010c021908011a01030b040608060714041e080606041a0d03030e010c0525020a 63
    0x1ca0800a40c400e10181c0d40c20f1088004070401020340d05480359503500030515003030f82d1802c501d100050340030003000d001058080e070147d1800e00114408280c0b04c00e80440d6129021110101900c4140d03581c0e0510240e04140c02107010902103242c0c03c0300788002600542038a90080407070075814418968a2205800c10702c80c8400060030001d00b1080d12812030101e11207a401d64014111202890b103040301c0249801602641e1040e801650303a4900c0b04c8050f420b000400d90742e81994090301540000201e442038003030007900c55010003406501c40c040c41c1540010140c070081c8840c94015444c0c03000c18454a030010461a90195540c1441021501013268020151003241e006440d0f4400d82d040c0045072252054491040b505681d04030390454507044100421546903882c482181000b006690101d8140118024030507402820700044403005000080d007515440b560300d00018400281d081009000307501740c0b0359149100c1c400030884040036070200d0716141c01c9000d002c03c040b4017409014045001780802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 584859730 1250 584858480 584858503
    0x151a0a0f05010c2f0901270903020a0f080a140304082203082206030e0a0201030e030c01020c06010806070f080a0203040f02060d06030204050117060114040213080c03010f0b060a0e03 80
    0x40290f03546400c401c3c00c0095103035a820317209402038000014100400d82802006030f1101e50800d000010b2030140c00000d207a010702c200d082d8000c0c440c01802181c00c4071000040c15000d0711032155a0307080400020201c15005040720018075003401440042008401078548561003080720110028041d41c440150f01c0d1243d00c0140a6a800034800f129902499401c2d0303800b40c10540032004017900d890302a820b40e8180e00349046160300100440001d0341c440c1e002203d04400010540b072038400781018140c02d9a100c02c2c42452681c3c025030040004a1080145035031110241c6800318004844450003048018098408800980c003c8042820700c40c050100509035580184080e07580d601950040c40a090941701c20791050380303010b00001ea5070300d1040301210300a0a56000d480030381e00b001c00c0c0c80c4000d0072002116400030f600340135503503280e01c2c0c1b02028406018414010803c603550f020815007941d1003100340084c014244a07011903140c0b5900d060303801613110340c00c210910b403005002103850521078224 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 584860980 1250 584859730 584859773
    0x501090e150f0907050c060f131205040f0306020903060601080601080a2004170106170d0302030c040801050127021908071e0e0406080d1403040609151a0a0f05010c 72
    0x50041c40c507004030003044a00c4611044d5222940d510311a01d00f230300401c64000c00d400402d00741c4500060b85540200c1ca0481245c1007190a1036200d00785502c6c40322481d0003c54100341d002034100e0840c60304005140e404402403a00c40c01900d080030009090413806007445c141140c450300340c0c4030003c1183c55810003000c1e200c400162610394408001c0030409800880701c07800d510f0000042000d0b44403030307030810724115440c009100c04210608214000d500080080c48a01424400071801034401c0c044e00b8000c01000d05481002c2c800000e0800300033400f0500080214410091644030110040050804070610300701100d080d902c5500c20766850344010451080496040040c0c031450340c100c1100c0d0410001070b202000101c3e20b44000e00e81d568503a000000225001d910400342c20202c0c10011540075108030000309001c0400e541e91b0300b050340400c1060310035a480e02030304405200320251104c1110402c82e00d80d224185000a200c086110390300809040107110481038090081620000c6090011b807003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 584862230 1250 584860980 584860999
    0x30409020f0a03150b180a0b040e090d0504051804151506021614040c0908030f0a0e09060108150a050a080c09010807061d150d05040c0501090e150f 65
    0x601e0841075020781112008a8a07003001512400700c0740d5a550190340f003101e5400c0c50001e90f848010b100c0171080c07030744540c4908200e802050700d0071210042e02c002e1401034a905014202158845c1c20300e99168025010020284010403040d5900c2d00c0c45180002041c90a0195071514203005904280200401c0d1046041c0300704803100509010b40c4008680d104e9080e80e0707422003440c81240861200c2d00c90a9801403101d44c1c031540610380742e80100e4001209003010410166511401820341c0c1016910b080034a00114481c8001c1d40c11401c10014010221142c21440c9000c6001804541000c0c1101410400101d0b0748200c0340c80b0300b042d0002a1400418195074940d8071965241d94005403180d10f80190308000c0005288480041c43c0419114561a01911441c954058018010040410340d80c000707010b010000030700c815440107000e032044107200496146098180704010f43e095034040ca040001469041241511703400096802480896507900385070100d9000030100c10403411099804510074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 584863480 1250 584862230 584862247
    0x90803040c0302040f02160b0903070c081005010609080607080402010509150403060b0d030c140a0b01060503161103071401090b09030705071e030201120e0f0a0203100507090e0903040902 82
    0x71000001101c1c421034050000d00340c015494000d0f80034410749910807456143d2040b00080301c0c0d855583d44400040c080340c0c01d00c0c84036210708400c0c1c074981d8414210f64212403168600480b003400b40030301521003410961031080c81c000b100381d030f1000c0c000c2c0300d0010441c03004085421a07201d80115049450014500d4090214804054526500501c001c4a8180c0380440000d1079007000b45004956907015100e4240c000031640712048407007501c0700101c2075806a4054900014220607156008c0c04840e6242c0381c41c3c1c44d210601852085112200f00217003c40c010304825040000800c44001c2a030046072000c0515440300f80c079000d0301c1d020300002c0c60b8050300c004100203184000b002e856443d00a2086540320b80d80d84050f030f50390601c20700d03041d008451050401e00241d40a603240842c1c1c0c1c141c1070300c00070768003941241c4a03040c40104403201506400c052030078025441c00704071035020b10080f82410445800c00c45400380103520b89204030001402c85900240303108200b84242d9000b008a040c0965a40c400ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 584864730 1250 584863480 584863493
    0x6060415120c0201021c0b2b080a0e031e0705040b0a080703080a18080706080403020c090114040e0115050f0d150207020a0824061504080102040303090e0405190609080304 75
    0x4401d0622000e203d910041b0348a0290300801418100240010101072070034018400e0020024036032032000041700003007000140c0d502000380000745ea6076540d078035810252010103080503610742c20105c03203c11070b40303501c5c03001d840c040381c6601250011500001c0400c0ba0b05c000c50305039952584074101794000c203c000001d11040000500169086a980c1407100010b0454144416128001c20030a584624010f015050240600d16000340c042d004594404025030b0000c2c4c3d11402c02d8116120740d00d007054103240c00e030500340550075000842000030703c5280c260600210b444445481041d124119042c0302c1403003030715111071062100ba04558608248501141100069480207200b02d01038aa400c0300001c05090104a8030041c1e07861a40001103584c40b070b500f20f913903450042c218644c0b24905907480440700a849000744002c0503100d0015840f1499070602030a05a002e51102d6081656038081000060380480d0070314060894000100030451742c0c0c00d00e11300078541003d0041c0300c2c030000418041403040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 584865980 1250 584864730 584864737
    0x30c090405071401050a020316030909020304140d03060e04151407020d090603050403120b0a0f03051b0d0b0f04110913060b01050f0f181903110906060415120c020102 73
    0x403400c03040007000850f900111841d10031003c8000c0140c100784aaa160a000d40f0780c00c040843c02403501c50100c5480c1d5040c24100d03401900c0444140c100200040030038402401300140c44895810704024680c9802078811840000410003866044014201c03881c0d4915a032045850820013020400a4070344040069911356152803600b001c14031440d0b00142480c480d01950b480340340c0c10303541c29600c40301c003504010141607030307440c540d9104011241c043341c4600012900001140554024a4001c84128299400b00040d00c041402840b4014045000c5035030295101d03000000c104007181141c0d65400c019901c1c40c44194001d43c0104200f05000c440a982d910f0900d440303004200c100111441ca5006555512501000030452b503000c0c00300c001072200c800090b128800748503004c07140b06003804001030b01c9031501000c0000f1585014406105010035900445c001c18010f5984c2010341c14608001210381c000e40c81a102c420f08640245140988616034042c1c030321541d142e0a01c02d407444840003170302031f42 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 584867230 1250 584865980 584865989
    0x30405030c0609070e09030403211106241c020d03090302040c1e1e0f210617060c0f0d1401030309061b021003020a140c06070e010e0306070e030c09040507 68
    0x5d011004103181e800c001c8111000c582e8040c81d81c0c003100c24030301015022112881d032040180a007110a1001c4810144081c074400d41c000d40010381503d005541c1000c3c44c168600540d40600c40c0ca001080002080d80020000c0b10340460340d241c0085400e190448010205420094019040c1031000c08400d0b002402045181e4100c64502d803240390030303403040b112100b2203a5036160402c00d0b010000c0300507019444000304000540307040c1407114070116180e003480b00744025203c18181d81d50300800c140040b040004180b10f24007005070600d81072503d0b10780081d018504049802c031000058440c500d071166032004c4c60b5443c81074010480d645c2d4909010b031150030148100008582d60046850000720869040d10415900070840000744104010440080d0084219107051081007001102b0796900c01000d000c040c540000100402d24264400030240000007251030b050040804000101d550081079582d8031040901e091080c01c0481c9000900d40410900080d80107100300c02444180400490480306a8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 584868480 1250 584867230 584867249
    0x14060412030207020915030102070501240602030c0727180615031e0303020c07140f0405010506070b04060605100c211d01050f0a0c060f0e030d02030405030c060907 72
    0x85440c00030503401d03403045842c002e5203d00ca4100146440c0c0103d03000c1c4008040141c00141021817a50760b09007101d00682c0c0b5642c203090000c2620601c0070340e014150300a00124405075044c090348601c100e65903502c502880300ea208030254454031100400c0e0310f1017409a050481030080c0740712168080c1400000b031100342c44030b0381007100d00303440f171240800c0d08011254007a0411014a02ea2007a500700241750590840c201034081101d414201002c101d00c5014000d81416100303c10290802c10600e42d0088003240e003c0d905000040044d44c6e549015600d84d9a0048000b901d04d940e1440c1c10402010650000755004001d10802c034002548101e02003800c5103d80f01034651012000c1d5145409026000040001400004000d1100308030740c0c40c4141551040c14003034104400c6000b0740340c00c3d0f0803620201340000c500a84c41401e0001ca03001d6007452001855042240d00d0303010b0801c60b26442081745008055030000f020a0800130100211924107036104151899030501820b0701d52201c0130341c498003084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 584869730 1250 584868480 584868503
    0x70c0b0412120c0504060e0d0c08061e01230a090606170c070210180308030c0a0e0d02011d21010905070e091c1b050f070b0c03120c07140604 62
    0x20410b103445000e141c540d554840b107080910f001b10450b405030428151a4101c151110b40701300040103031108501820080000d0079040c0742824034a03403581040c109003502044980010880c3c10031441c00002d004100c451802c186d03011303030030103d0210b0201c1c0d400700c0d2005141980c000380302d6038012900c03403801e0400507413441580c590040300804e80c000c601c0040d50000f01c00381d20f11000d601070fa140401c0103d040e122030302415901c0d1115901034004440c400c01c01c210000e103800102d41d00c810005500c0700f0480d50250103194a0300002c01c10080c0c40300d010004c4081d000e051040e60388401d486040c1d500e034201951003580161880c10301074088041d0448036803048020100301d880c2041401485403503010001d002e411507007045030881d0400c50154030f0902c235610382200b860b40364041708525054080c0b40188404075138841ca05242c402c2c0c9507c6400b10079001c0c8006c00f4581004402c0324140045443c2c01032264681c80301188140c4640c03a00200266007140fa0705800400124170030b4400c50082500c2d00b903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 584870980 1250 584869730 584869757
    0x908010c020718091a0103050307060b010807080609090102120103060e122b0f020c0a0302161a13170d03180809090a0b120a0210090f0e070c0b0412 65
    0x9542c400740c01481d6400942c8006a804030009902110741c1c14000c550186903c200070b80d40340c2094100b80c0017a40c460b00005021000d0144078010808203030302c207203002c8449181c02403008203a85006003c3c0f0744141c00300e0b4046500318109405a0340442d01c243c1081116503943d1404034001c08600801210034050084070001152059040d14480c504418018503084000400c1302c0c445034041d010303800501d0341c49504034040815032000d0b045a1007010024070518008d4100649083d002440d101d420340b070380b0f40c1c007403144254a200a155035088205016210300c045040100303030030680d0f00300500f86600303004c1d0745200200000c2d0405540029817410412582d4102d502c024150400703401070210038040221803031394100ba08505a00141c0104000340c0d000841000811505d40b5001048184e03004425420540c0b40114010713400d0003041c01d01440c0700f07207030900c2203200400d1840f400d0940016040060b0b0114003500030107030380b1907002810801518082c6010502003c0650140002945d15001d240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 584872230 1250 584870980 584870983
    0x30c020124080d03110d0b03010609060e15040612020f04091b2108123303010e010905060103021c05060705190e09160306120c0e0717060d08070b070908010c02 70
    0x117881c066001d0400d2404001c0740351903011300310040985030075641e184d1000030700000600c292000783c45c510007100d40c0c1e814005d0028810f0560350308040d124500e4100c0c10040000d28590500f8610750590781a00c0381849030b40014018212180c0c050840d1840e081c9001210902c040c1d0401540d0404071209980032400224404984590200801400042004c2d001d202100301440f41d010498101074121882c0b2030b00507842c42c0c140f0340071220511481a5820702e442c03400b07010301c0250314403d02c0204002201500c400365280010f120181c0140300303910100580c0380303030b07501c12200d180e4102d004c0300c000342060b0000400b56807000c905c4084003a18840583c06c503c2c03040e910314441c0b450003400c60045403111142c080c641e8031260030900505a48020000340d41040d241d086007924020705689000d42c0c40d00668000b8242e0041c800c00410004844e5011508180003056400c50010b07034401071090003600e8a051070f80b045a401801d07286484003009112540558104162001d0300000c3c003d510584100303a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 584873480 1250 584872230 584872241
    0x12020315070e09130c09020d020d0e0c010f02151503120f041412071502070909060209010201150819110d11031002070308010b16020a0305031e0307050a030c020124080d03 75
    0x80517089000d0041041c48842c0d00540080c0880c49001854080d1080c80d2a08845080d10700d00380d282c000b400d84005035038124260b071021040c0340c0003805140c00c451081270501e00b0f009010245040c051545283c40c0e0300c041150f00503403a60394030076a40d144d4945114900d070783c200d40301d00c0491641d011400100c41c28010801051001506d0050002c40c6c02c01c08000d81c1d581050f483d03e03045120701074002030a64814000d100745140581c2d00140c4d1584020002070030344403011003420740d00c29041003c20054000003000880000120f503c0f020001c0303145420701c109080050010b03800150b1459400134000700540c03440c907010003281160768144203203e08000743e010300740300178011400030801004540e2110004264500e0b02008100c1c00a0741c2d40e002a15a44050b08180e90036400800c02078030003c00c03913001c00101010850118218035099000411300d1196078a01d030100743d00c807196864024001d41110508400103c860f008210b00240e10800101b030b5442040014417a03c12009010b44c06407280307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 584874730 1250 584873480 584873483
    0xc0c0a091e1802120f0a080304051627060906080d0201050928051014100b070f110103090602160201180f06051b060a02030601020c01090b030112020315070e0913 71
    0xc5024012032038007000851410030a613200d00d03025068001200340f00a01c80c101d0240d1003120f1050701c074101401c1042c0b404540360b0b080420b61440d00303000c0c49031540c05951601501103403460407600d03490022464024140560048010034241100410946d0700400d1807004400d41d90300800440e43c1e0307000c445a807100d00c1c00071030410401424420741c0e00010040c0030400c2501079000c44916001044400c000c4031410000c0f82c1d101d59513141840742e0401a410700100901544a45608050340340e1070702c00216111000c010005107804c440f0704540d90088d0002c002c045c4c1c01603800c54940181c00786041904000742000c03400141c032505103003601c031508244075098070110f00a045c00641001750a0f90b250b03204c000c0402088180c070707440311038089041001034440c4082500c0903841b400c1140004e0715001c1c000082a0500c90901e5060005100c0c1100341d13411a402a22034010001e01d82c0086810001c069408001181c4640108100c0d207401020350059002c00341c5407100d156492403615240d01d00c6401c0c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 584875980 1250 584874730 584874761
    0x30938190528120216140717063706081f050f04120513120c0506210a0204030203030f04031e050303010b030a0b100905010908011e020c0c0a091e 64
    0x10780e0f603074618079580a080d445525400111846829443c1c200ea04c890000800c0c49680c000d00051240080307036107846000380a0100144641d040944072211102204d44080c0ac1c2456461081202c0102030385182581c584403000c10050951203815580c0c54004c041080220488603201d40c2450340c40c81e03c5182d20072000c0c40c0c40325803107454039a40d074501450485202c0040202c24030503a2004d6141d0210b210082c511504000381c441c0703161920b51450030a590140e0b03c00c440501030b8900707144011544502900420440000c03d5640300c9420000f0700440e00041d40500c400310705801f618150307000070001e49000710388080b0302c0042144401d08201d25080010110380003840100300d40032f80c0340e028603003225007000c0100307080c00000c02042c4648480040400040c1051340700300000d503000074041000c1d00c00d002c000c1c0501c3e543c1008081c92030115660b01020907500069222490f4030a0128020f003440013450449513a07581e040c080d0286c44c0d0100d0b0b51551110342440344441c101c552040501880c1d170b400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 584877230 1250 584875980 584875997
    0x71406040f14030a020a1202010e0f010c060b01021f020903100c0504091a100e15130e040c030501020408071509060813060b120a030938190528 63
    0x1c02c041294580b603a00e503050300c990328240e001a40d400069901034415507030ba00440387c516000042019040d1650107000307401159002250382d0388041c4030b42c03000350480f801103029945000100e1900300302654140411880d10301c0d1fa90301e8031681d00248078210302142113500381d0000c0c070110000c03100700e4902e000100f07404100400103004903412541164480c82800000400100045000390004400020008004210103103061400d0f403240d49801091071860380c00c142e0800c0c884c03030004c0e8042c005d07001a1240b03080041e04220b03640442201440c0e10100039919591341b01180c0c0d0b034840d024050708d0100f40c1c2c11607407111694031032401d07403080310400da55600d0662180c51541c0c031018007028003641c0080e220b60811045450326014a402a48040000d01c140c3c201d90500810103030480d003001c07200383c85a20380304030081824001c03040c00125036203600c4218030046042e81c11903c03c0840d1104854264000c4c10410707030f04200507040141c594451740d80c104881003a84100901141810000324981c80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 584878480 1250 584877230 584877239
    0x180a060c0b0903090d03030c0f031512060e10090b070f0e060307051303080a0905030606100f1e05040e010e0f0109020c03310f0b030a0c0c14071406040f 67
    0x3039007940040040c003d6074a000311800200f100070100030003c1c1c0120745c848404800319503201c4521101d0340c503503260400c013080e1101080c10303181640b8894407401c035100384a0141448140d03444240045040c104031034a82041704007076405881c65040030340b189001240091491380c022001c01c8000c2c1229a9801e1961100743d040203881d40028041c801040018003d0f015040f1142000c0400740d805200115199000322070b000300940f00d0b1f604028040d812420501034241c640d0307100620651281e0070045244901d5000031609032120543c3c1502c1134014102001340035405c04024010b41c0c90142c64140c3c10b2382c82e0000d001c2e0291043d0391100b08200c2100042100345002e5010313000b40c2d600c003000d032032900059094046550003051500344440010028520014a002540c000107003448050042058988807600520740401403d01c03420b1903c0e4907421410510030515484501d42c42240307680600c400d0300419a481e1094020449007070804694101e8034501801918100d880e8290444d0307609050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 584879730 1250 584878480 584878493
    0xb0412021f121109041d2104090f0908180108060a0e0f04060222050f010207050306040f020415060c030f02010b03031c02160f0302010f020f0f030702120a020102180a060c 75
    0x390f4040544518051203000c50390341c2c81d402a000070152051407194241c01c981029810501d030300c0300081c00e020034400104030622520080e1404c850410400140c0000b07000f0b00c9802a0040306402444464005a403119500c401d0180e44600c880c00e136035641d400d0707480d002844103400040c05000000d031904030010342d17000610304a20f81c5c4548079440c054101440d68940c50501c0308512039401c03054480740410301c40c0c0c1c2400284500d0b558000d10007840720914140200341c4804c80604080d1109000c6281304095403600c3d04a06111100000701e0f410076581c98400801220300300c2412000500050003644449105000320410024001c02a520341000c0090005100c80b0046040308629020300021007480c456590344521980502d0300d6148610315441c00900712042c0300441d000840c4144502045080d5003c25a800014090704081c0d03261aaa03000b82e1030203c4402502c3d06400001605030881a419009420360050582604040c0c87d0301d00304200c80800f540c081c4c030340028902201c2c040403440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 584880980 1250 584879730 584879741
    0x6020606180412020f0601080703030e040606200102160305090915130b01230702010f0201060602070612020d051008071406031f03050d030203190c0e12070b0412021f12 74
    0x210f00445c2c001c0d2903c54107142c1040002d900010950700300350810001e05401801400e2543d20480707042105a092502c0648003541d4000c41d000350220991008440c0d00b803d40c11991204107203c1480307000c0a0358513006001d0743c00324403680e00819210300403500705a581400d21201d02001000e0000d0040382c44c241e02c0081403400041c0341040184100c1c210704002800700c04c1404900e130b1044907076843d03072030001400c10a018900c64045a250000800503140e0124481c401c0d100760f40f41044c240840310b09814080e0142c880900c0c00d281c42d1400740540d503204840d913402103601078802d99181c07a96580c0e07800300c0c03084540091500001c0c2080000d18178420030780c40304881d003202079105090395201d845440c940b10507000e1500109500000b4001c01002159000203880700d4240140314510307602d01c00508644c0b181d82d8580c0240b400a541707404202d808e100a0b000303070070740810194445d5030b51400040310010317154059024010b0441a5440e0020794036081348440c401c1c0d2a10841c1c4d140d0381151800424 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 584882230 1250 584880980 584881013
    0x1141e03100504050a090501050c130b09040207080d090201030b0609130b030f0a030507030306050a0302030c010309061d10060f0f0b030429070806030321060613060504060206061804 80
    0x107124030404541a070355846414011082c000000a03400c40e18549a403c54102601440b20080140100c10703242510019003810b90f02200855500c86402c1000b080280c051038a00521440002c6005084070b90780d0760020020078000d036400e00049855106000c801e105088003260404413140054180e883c00b508000303e070f500050120b500da152240500d41c02d082034000224001600040d86009169150007103138054002115141c0703a4501e5131b030020395129450310b00281819121100202441520387c00010070b401c0241010100c040440240398550b2846480c0d4032145150030390102e0ba01d20f011141c142924046444031020341d0402c41b0340c86040c2c01c0140111203511407540450030400d141910205940d03016150a550380c00c0414000c0c144420003010b15021790310500c0f000e001ea24020b0aa40f4444144420380410358550b0400701d40b0710710a500d501144100b0306c040001c2c805070302074000c104403100c60342942d03915140c2ca4108074500d01c0c120740c0f00300f10386504170200d004111035011144159 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 584883480 1250 584882230 584882251
    0x12190c020d0209040f0b06191509030b012c01052803050d080a051806130f0816030818120c0c13020315010e0307030311120c0c01141e03 60
    0xc00c002c0e800035807407603012242219500c000d0640001004600300c03c1d030360000d20490343c3c07951a1002124100d44030002e0310039400044c26910a01100c0d42c003418845000c0d541240d495200740d030315018801d41c1c24002220380501c1210040b441030360101240d0301e141c141c0b0f0004200c0005007994890141300d01030103146140031a0721041c0000700003101084100c2046860743c1b10f1928a281034200c80e401c540c8000d00c480303020912621100b00b21040480c0c21944415070300ca214820007031604003d2040424800020700d4650000341d0005661080c0400c40750181c881c1ea1500c6041c0e4a000000c004444140c48403007007588005d45040e10031034000080c0c008a5503e03070450303140c42c219000044c220307010000e2214030380b54000240a0042040c13803045640c0c250a0030b0140c10754120a011075518252071101400f084400c1004484071a000c1c84041c88105d1041402da84a030504001a038450301c9210915012a02d400d0094142d44909000c0e01c0030300e480d100e8141d0304003492605103c190b900041ca4103104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 584884730 1250 584883480 584883499
    0x150a030f080a050f0d060914090705040518010f0902030f0d080604050a240e07051215061b0c03070f150807090503072c0c0304110414070f0212190c02 66
    0xf020b1103040501384400142c8001b0403d2450546048215103158011264519081c02004410040040c1840454500382e0740021140c0d601c00d182c1d0510365544207520282c0d405c0000c41c80041180d504084070340d074001c80549202004036250590746400b1040d9a5001c01c0c0303c1000108146060f0380310990080424070702081f4180542e00101d0b900502070050065061620000d000c8030604511455010b0803234101945000054683c5240958000749094000c0c1c43c441d081c480d4070707140c9170251410410f00d80742d81010000c440b00ca0756114405903a00c0c1d4028820420005610700e40b8403807410484030907072244040b0000642c4101c0e401400180040284401c514001640351401c10601b0300621540035200c40c0b40819040c5403401100d551800c1201a0a090a00c00c16040b13040450790016404680d281ca0540441c01142c05401c003240c480c01481c03103503801c109410342c1241e910328501d850b0b6802d46010b066031000462460207200144141c501e03424030316071001800b43e8540030003607000411178410b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 584885980 1250 584884730 584884747
    0x81302040605120a0c0b040b0706020c0a02040c0c05060604050106080a05060102070f060c140a0302071719060c02062811130303090501020d110a0f0f02030106060305150a030f080a05 80
    0x1aa1500402c03e00d42036111201e014288510b50504901030300326404950311301071520003044c407180100c40c4050445030703000440c100080c20030004808419805007040c000c401003400c020780514a4804c003681d8038010400040c030f803450300d0302c5032506036107480d11486050744400403000000c2000429280c107602c41c01501290382100c08070707804010a81507603400425641481c0031030381c1080e221741104c03490340107405440000e42c000c1101c0003591204440003481c0105800b040b03241c40081c2030b0759a9011551b00b5810203005158100c0c18083c0629001c4078980e4035904150640005100148461942040c80080c680241c0390001404006100b0f00203081000c0500620100b141c90b038003c4010030441d4904022550301401268007800141c00c1c44d805210341d0040781b940f50000e02034001c0a481c40704040c10308100300b4007042281d0a402800070004940c44a102038001c18007690182c1d00c52202c1c003c0c8081e28509009020281d0354000c00307001c48034046556958880d00282410424050180000070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 584887230 1250 584885980 584885989
    0x1514190e0f010c200312071403090c100f1713021207080f1c080c0c1e06010906080309060a14030a0c0f0906050a1d1201050a0608030307081302040605 66
    0x14401440000401c0310f900400030748068041d140c540340006964020040c000404800e40740c14a0b0022090441c594500c601100c170070341c8c00c0390302102100c008001e2007400000020f1400c1d9410050741c145221804551003621150481120100002c62520083c10610110300c0c0d800d07003001c400d0300c00c44801101070f400038142e4000d02e0f000e02d405900c0824200540030b401c0080e10b405800002c040e00b46259217008480e8900482c0100600340200f0101161418071007101b02e078490307122001038800343d83c1c0714665150400002c1e80744810038800d100011403c0d0381d8510404044942440c001c6107088240c10900080d60800442807043c446407081da03008001c50302d4004c611852507503100042e01128402c010f05038111000d6150200032400c0001d0003c180c00a0480d224810941450031b2900600c11000083c581c0c00c241e5143c20008a604803040c02c101504954040d0000020601450b619103e0281d5a400100d07500400180050b0100e9001c0c040c681140c2080d90002c1c001081640d01c902c00704 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 584888480 1250 584887230 584887243
    0x20d170a0c0b0f0106080403051321121d0d0f02150c1212061210020408010606090902091005030c1e07020f01080412110a1704031514190e 61
    0x400114144030104801c205915603001d43c0030b450309030b050f600d95061800041c214500108000c09106002581048180d841c0c04524007c003160104c203000741700e034030b501d48402c440721500840d501003818540b82061409040100028041041c140b07201882d90800c114180000758825542310101c070b140d03038016031030b003000d40800c954200210503070707451050090a280c03c08208a040b410340080c8812001450142e01d03294001a04544144600346000034280c1043d100c8540840d070b00e4800540082e0050041d0443e02c111041900c0e420390300303a40d608160099200d242580c56000303524801c0c10101b02c5c003510186400610300c8041d1814038800c800c0e03c0c4c80b007583c0f20180c05920074011400380114035000350f52910020080c030300828103042981e82c145034642c8008121007441155804080c02507002c014009095030000b075680880300d0300d6054260a54403500083c1c889807a40f10002c104010f041c05650324010f84000194001e95032400354101007071070108000a500c0e20707500d03050000e050801c240c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 584889730 1250 584888480 584888497
    0x60d0e03030a140109090206031302041d07091d03040e130c03031706180c0904020c03070b070f181406090907030b0405060a03030504050d03050903060916140d020d17 73
    0x16910303d10f00c2d001c0500303e8050b400760b910a41000c01203001a1174500590b504440d600d006182c4240700d910000307014000359001829201815200c07240d1f4880700144281c00c0310000d140420068203802000704085201003d13042c12980108400c02404c407107a4041d42d8008054110074070111903565801252481d56402500043c1c00340c0348000005604180303e64010200722141c0701400c901c4942c14940c15401091f5441a81011600b12080c1c2c84076012907000b080d4120036640e840c1c00c1882c0690b02070000307413403c0c4000b508444903088994003070982600354904194400a00354640030a5104001c240744020f5009281440194180e4403a42d10035805541c003601c0109500c0c10070010301040768001004a0301c5039083c0102000800d4004045500307490301690b80c220300200c141810b40d0305101d009681c1d5058840c940400400600c0030a40000ca03201c1c0e070034022110740e9908000f0210160074480c00d6800307004564905c00502d04080f01ca2105403107150200c80086141032020003c0e08503021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 584890980 1250 584889730 584889751
    0x230402121603050616020a030f0210091b060201050907120c0b03070e1302210c0919090c030504120c03020a06060602210304050d0c080705070b0a110606010e060d0e0303 74
    0x8140b04100b4144001c0303030300c07407040e0000303038040c40100750020760f1a03001d07840280600904031a002d80f102e00c2801107981c0e446171504180b04119840c074200c012400307050030310b842c1000751010124016206010340c3c0d0007045004000c0c1001828054400841810180e0071103004202d4800094150260300c051840b0740595150300c16441881e4061081e408003401c10150041d03c10001510201c03020b0008060034100b03000340200030364800e26502c01c2482681c1d0446c0c0c1c440c2c20042440c002c00354000b042403d8480911051004c41a1005d0503010741d203013640c0050050300704c140e400c18044e00c1400d803988514060f00c122402d00d140c036182c582c1100e0480c1c20000041e04555030b40c2c1444841881c2168034581564059865880d05132030f490b03191707281d0309058020020041c0a04050014540944c1c1d44290030000791400c04da80d50f015048aa880b07060b044010641c000e544101c0780b4030100b0300ba40b0400068407070100303141d500001c102c11031b800444500d502950701d050045211104001075031080c488400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 584892086 1106 584890980 584891023
    0x3160302090a1a04090503030916030215070819020c030d110d0c0c08121803150f270a03090f0f050621070305100501020123040212 58
    0x40f41030354040d0500c0e450318280100840190300039403a03142280ca40300440309100d250b02c515440043e60103030043d6070700a0b0a00c04d0b0b500901545109900c4c00d882c0c0140040700501100d04030b686500107034004600c18102c0d08040028504440c86814158003031441c401d202e9a07100080b00102e02040001e4080d03030100301c0d01c00c01c0500900030035404d882c2c40d46514081007503140c00140480b503100721800c20340f03055418045898080c1208011503e40c070740c0d50b0036411003000d000c00b4142e425141241e20f001d6615600c80b050360409504500d014100c40041400c0c02011030303160b40c0001c6d1305480003100c2046003030500c102c502e04955094804549401610301c2810506d203c03002d11060b101c110f202002522036165010f58440d9405406170b03601030b910740b0b00480c01c031890305043d40442850341182084240c0604101940035100404600d455a1201c1e4190308101d04800c1c880400071989 = true := by decide +kernel

theorem cover : BRFrame.Cov 584712230 584892086 := by
  have h0 := BRFrame.cov_init 584712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 584712230 ≤ n) (h2 : n < 584892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
