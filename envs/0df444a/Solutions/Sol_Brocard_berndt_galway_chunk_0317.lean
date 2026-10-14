-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:10:56.741471+00:00
-- url     : https://prove2.me/submissions/c3f895d4-1d58-4582-8ab6-cb0accdcde9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 56834535 ≤ n < 57014391 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 56835785 1250 56834535 56834539
    0x504080a08040507080105100807141005160c09020714070b161b080703050d020105040507051e12030c0c0301090b0106031808040e06012006040b070315080c09070c0b0105 75
    0x201c400300302800010010130b406051200000c00c5a82030078802921381e192036204c2d00e4020b01562900080340c41c011401c0c3c0760000e402400c040d10800d5040c0c8100d4460340402e80c1d00080c0921702401c140400d09030320009003c0c110702d0380010313629092350070300e46250b410701d002e10f20f0340c1d5001c040c00b44445400003040e28640070b110b040542080c02d00c0d107003910502442e00105041c03128141c1000032214000641c5030112402141a0390300324001200480c26603204850140082e80101e808100c24204024110510b0909003030000407640e06d080003c4502d9900310140d44541d00110b174a40444600388180e050081080700204400d100340d0b51410b0341d501c014800c41042c0f5640e5103101d0b0034825a20b23400b0100650010324244d803680c0740c0c032401b0009601920340c18000368402c0d81c41c141d03054071300281d01c8252600d04024042030340c66a5840c103120400a0115080503201e504c2e0000244c0c804801d50301420925001e84a808500300070322842040081c15642040802180200812030507000103041d00d600b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 56837035 1250 56835785 56835797
    0x61a01020a0311010e0f03030402010f020706020327060c010c08070c0b010314030c1905071706150102030c030403060e100513030f140c060708061e040f0e0105070507150504080a 78
    0x2403d0010350040100284440b020f010b5940d1401240e4004401144100d1003602d032009810741182003207990b50fa540c020740015034001c020355002003041800440404c01c0c4403d00b41c103601110400700d01d603600100e4000d45280e4440000c400d8203038125040d158003020034540f007508103103e03442d8680c0e550818403025040341c4150360136000502c01481101c00c3d6520810031550802e084c1c2c1d080c007407210704843d020380707444c05090000700e000d00d292442c45010f003901310700802980c0c9490701000c00ba01800881c103415480204420000e40300d00b80003420055024640c001200480c0c8000241812a80640004420710b0941042042a203002c40750300069010719144042140c10541950510035180001e0542035003c00d85204050700011010700c501c0c41a900e0b80c406848000a00140000e100841580c0000a80e40c0340e80c281082d82c400321401020100103d001d0851045560031100c0966107a030000b000020391109101040036220307080d9010324801c0086140540300c80890740200c1064030100700c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 56838285 1250 56837035 56837057
    0x604021318151b0804050c01030c0e010f09180227030a030807030209090411040e010c0f1b020a1e08030f040902031806010602030301090b030303011508100b031003061a01020a03 78
    0xc1c0507401000f20030495400d400c600340d030411000d444d150040f07504440038480c80140046035403180c014007210421300e072190100c0c80700785001500e9244150481000f04980c10340001418a459800d1903544465044010303560142441c540314000c84080711034034000405803039a400d80d180014080d000303d03003615001c00ca43d100c0c40c03000c8020b80311303082001e50710102903810301003800311034080359400007001c50f030403c000d040907607140e420703540e08130708600108880c0200707414000e01510403c1c7c07107c514911400280401036000524603035242c0c019580b101d030000100451501d0401e00fa2000d020300d00011401d0104210320701d0868800d0b4003c07170740c22580120100350a408401c07200b035940401d070310030380d921036841c1d0000079940d400920450550310f08000800c08a400d000c81224162145080d10000b04105130900b07a40710755001d424a400044c1c0c018002032420310a4019500550280c040d5802031480c60405000b80d0749000344801b01a070460150f541240e8000500908144d0701d410030300e210203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 56839535 1250 56838285 56838323
    0x18010b0d230712120306050306070905090c0409050405070317072d02030102071406130b01030b0403140705010b0a06050315040e0705121515090403050904090c080604021318 76
    0x4040c1d64843d0004941c143c04120421003c850b210412008036038003044401da03108101580c612042c0e595a020a440917010301c2a03080000ca1a075001202480d100d24041c1d65101840031148102d0781070f14642c011040520820000c031080c3c00c1694001a941030a00200c0c1c0c940110f0518180e25014500300180084100300701014414400d4680007070003103440340780d14100030040700004108920f880c0601000640c1c22548099010380c000c0c0c020a150341035a095640b00a122180500154140050f2501c01420750301502c0041031f00b23174411000490000724441c1840541d40e0300d500000d0621409004000d03151a8007a10322240d11800c4802080c00410281c24605280c034540001c1c2d0440283c240c400340a40700002c08610000c88115400c901d0343e01e034005000300c03c070228051076103d402080030402007481003000e0304500000402c00214840c041d03640412030036076988070b05030b13903009103003000706500d4104d200f0510590985000d00000b40c958018841c90741034003030300400b40f040441c6400128 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 56840785 1250 56839535 56839543
    0x2060a050916030b09070603051302060702060d06030804030c0b030609070c020a171605120d0c0c050402030f0402030c0108040b061311030a020417011b0302070203010209030618010b0d23 82
    0x703100c40c1c6561408860b12800c081d080c0781d000311990700c02403040410001d840c508c00e10510b4801e10408100401c501140da082144c00d40c0080401c6c6e80c040b0080c448288500c0c014480c403402584100201983c8515601d4601040f400c290b00001c5011000e004024554844101250340800246850683d1b1061071000400c6021103800c100350101c035043c0910514880002c429020703100d50a802c40310555142c04100340809041ca050f646500310380303503044006006a0b01d4503051841000c80250441e11800480d00302c3c1c000711501c0c580c0f800b54405001c00d42c182407041e204003000030302e40b912151400761500001e4410203003915001d46000ca410110544059202101c941d12000409549080000700c00021390031a0141c0300f40c101c82e2940905081805110b841c00803405401c12003d00d40c1c0e203040039002504001800e0b601550201702202803540d0a000c418411500102e64500512078808084e00315080c0d0350045001d141d01e641c18102007a40c2c4951100401c40a8618170103c2020310b5402e410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 56842035 1250 56840785 56840803
    0x1060306062c0904021c080c280303020306030f0d02070608070c110f031002030a0e0c100f080a020f1903060b041d06030c030d0f1205010b030a0b0a080312090706020703020102060a0509 81
    0x50138003100b8640030054400c004214149007482150351003015040c44c1b404990709c0b6074508001c0a0259060300002c1e0098010b154454070040c02e549814000040150424045900340781c0182c0254509002c00364001034582e03040002440c000c800c40c082584c1d40c075940d10300d5015041c81202104003292050f50104110700403640001010b40d281d007086400000a4080e680c1d02c0307610b13801040301544840c100072805400b0b03d0f80c0e556a01a081c041c0c108181c0e011400504400d85080d000c114425051400100a00901001c12404210b0100c80f10005040710403079040410100410002004102e0702c80c0c4204022155101405210341c07500030009245c80e0244e00459003500690f0a10314105411441c1d030000c401240e1110070f64182e010800d90200c41d001d005002c0d29400a01c0814151007140d4841d4481c80005492100c010f0b0b1141e80040ca142c0140702040c806158041c100000c04c1070600c58100181114002080c0e90342c11940081d403103800c02800781d00e0341c03503640000404950003000f080700707 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 56843285 1250 56842035 56842069
    0x210f1413030b090d0206040804060c0507030b0c0903010501080d1224030b0103170702010f052b09060f02090616050a0210170601020a0302030a140d0501060306062c090402 75
    0x1a11a075240307801540303003030221062001da00581c40031050041c00071800343d10071540700c0f058929040c10100700362502c0440d402c05450510038100f001c00015480031a0030301880c81e1040d05511092041c08050a4400580200c10280c1104032104002030300007070010f0300080d4220011600407600141c0005200c50000c042402c01c4495400100740a90385031514181c90160a00b40004003a5a09402151065a40080c0051243c4e950241414495030180400800148940f25030317820404000f1200c2c24210354100742140e89000f0701c010080d0a00c60388890b0650700c1000c4d4200078884d40054954000c0c5503521140e6103803140c0c21010481c0c1071118031001540180920750480796228014020b00032800d18a0005a0000200b03d596000081065000d54076500861420317608130030407035190250801146500c0c0040c021200c040c01c0c240103141c0605800d42d0005034041c5002c40040040c940d6035400703006510100d094241c02481c003855211080740984954500d070301c1c1c601c0428042506006105 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 56844535 1250 56843285 56843317
    0x61605070204060e1f0503100203070c0506010e0106020c04060b1806120114010801080c0d020402090f0301060e040308100b041401051c2f09090405010603050a03020307210f14 77
    0x116200c0080704500c0d005d20317860b0711005d0054541c42180311803c481c030b011b800d915600444c0b43c2d11040d501600116440b04036448c0c1140140b1465a54501d4400d00ba0400c02c2800c0c0241d00520506604001c1b4000c201000c40e0b040c016a0f00e0300085070600d1141a640060081c00b043c201314050300c1c1c7d0784c00c41d1408210751148150660303660309058a07040103148220f00240b00d030000050389100c00a68544246401030800704c03203012a46c200002948007598298120002c010480410303502849400028850002072200a2401c0d140081190000906c854001c1341c0c051814444254610265015248d0441c0c9106009450400503a80c5000e40e9061119441c0c244001c00000c0d03c554200f40c4012507543d200015070105007501211410f01c505031100400c0c4207102281c40c41ca4042403041d00503026800026071075440380c54003400c040c2d2101c01923015a0000803000d040001b12310360724055002c0c410046004110780c0d18014191072500c003500042001d441c1205449408580840c0c01280f1b0648400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 56845785 1250 56844535 56844539
    0xf1b0f030a020a09060509130302030909040c09090c08010506060a02060c090103060e070c03020f1f0f0605040207031d0a0605030106030f0e0102130518253c0c030206160507020406 79
    0x110000d448a8003491780200c7c4640046103030890380345070616101d58036402a40c01c00042d04288a00000700a009a401c0000101d0000e2031004a109410f8414082c0d02450089810442c40500751a070240074240034202c20809180c60560101d44240c00c405407070403c96560003d540102c01074501a00000d40950001c802e1080380d50700524031081851107502a83c1c00742c000940703c82d4950281490801a030200b4459041184005510880114031020700000d40d00c0e407603074081012604031200032000305440354900030700303c1e6058203100e402c840c084078110305040c14650000c0c2035020610070102895203650010300c009003c3d40140f113071124a10021500c0c1e002c3c1a00254022105201e110f0048024283c241c6c41602e01d120040d106a00b15940110b4813901010840c100c41070f02c504810800c61100b2090185258002140c01e480642001d43c0e5541210320406980d11040001e01100b072146030011100040c1d0082801d5502031184600c909c04012041015a11881040c0340250b10600e05140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 56847035 1250 56845785 56845799
    0xb07050d1e0b090906190f180b0621070306050a091a06100203030c0712140a03020301090e0a0f150b060d020705120a0504030f03052203050f1b0f030a020a 68
    0x842403801400300c45400c103135200c5225050310741005554511302c4043c00901e0f0700089541c1e4111050794454600005141041016010110030a80600710382301244a400c0c0010703031038418802031203c5000c07a452119100c4490085070b80b2400ba110041072541c41e40d00003070003c202e9510800d000c42c0c00c040342d40c0c9424004402d05080c92030860f480340c401c80d01c00072101d107220300c0001030300c0c4a03424401485182110f1178449521500c2004041d0b0200101c1101001d030f54201540901000b45c001c0c0c801684a505100241c07041d0742e03c455403042140e010601d000c2c08100c1d0351a5111080742c228040707080800080c0349510203010503454168100c0c4c80000e100d116505190700900e400381c06123040c0e4041c03a40b410f055524504c52340c501c020018806200500100f20071030040c110b068804d041c40d902d00559804041d40c01c148410f82d803100701601c40c0c820020310006006c00000224030300058642c00c0d030742c0007082e88040341c0c4d0a807241c0030305d4148008204984040040c10031f060303001000070907420b42c0c3d03035a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 56848285 1250 56847035 56847041
    0x2d04030c1509150f06030201081504020f0406050d0f14060405040c05040c05030a051b07080a0302041802070210030b012f01110c010c0f050d0509120a02010b0118030b07050d1e 77
    0x70010050704c3d140030a40d000c10103218040a0302d40c140d4681506444403180c241d010f8a81d140d01a500c07903802c100e0f0039240e040000040005040f0340e2106500c03030481d04400005c552140c420f0085003030400d562400700c40c01150340c3c150f0040088900080a45450504c2c01005806400464100d40352401ea2503095070058090342c0700e00c0541206014554651400f810000b5403c2800c403002c030028030800d80098984806030400011500d00107003000d5170342c4512081c180003902858040e0740e0015804055044c203100ca40c012440a041c148001128038000800c0c96107900c0459161460706000703208040210741c1180c644040882c000e10520400c0d80c088641d527405906111015881c0040c04c007055800b4491200c200102900c815040c00182c040d41005440c001300305030950302954102003104954107003e00b8000343c541d8000960004102c001518030222514804c0c100d20441d4420000907500c0e071041070303000d0803501c2c2440d140c4002c40e8210f80501a04412640901c00780c24140000c94120383c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 56849535 1250 56848285 56848313
    0x30e0402071412121006020d0c0f021807030c0f021f1e0605030d0903080702011b0b01030308070e01030e1905120705060f01050904020a060e03070302040f02032d04030c1509 76
    0x2070b00d1345240380c81d520120ba15608617031085902680241c48420110390241c03520150705800368802c2036038810f0640c0007070115400000340480c2a08081c0078171080b65030500c80c1100d401400d00b01020080c00e0500c02941d503032030f181000394412609066000405007660884041590083c04d040c1c841c035402d04528018005a0151354007a2149900f41612544500d402100b104d0304500311624002305034004640e5541c440300681c410b1046464942e0020b0850181503000314042e5a0300340103400c0800006003000e50b01c05880d4100b500342001c080710181c0c0490071000740384200007054a90000b07442c0540c02c050b601340f421804400e021640320300f0b010001c02c0c100e2083d01c4210341120365a8880040000301c003c1a0b90103074004102c0c12051140b140142100944410300804030b603449542c85d4001000e56000c1e80d040c0c26815008010b0010384204001200d046c02c0000c01200c03e60012640c0d10050542c004001a00300440305a00809106002500000e00541d40c603050040d01040e04203040c040c1864 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 56850785 1250 56849535 56849557
    0x9030708120a0b0d080a26090a060c0207050303041511030301080a030801120f060f181104050903160312020d09080702150c0a060e0c030601030c140409030e0402071412 74
    0x1c3d4940f050380c0f0308402c3c2040078950000390035042c00c0c01400116001c50190400b03a80300d48460038a000c00d4541c40a24a10070800180204004981c0c1e152410944083c0b1480d6400d640c4808001d200c29176011081e241a07031180d01c0d5203500303090701300802c880c0c400c100c101000c00350000100214003060042130000c9200c0c00381d01d90395456642c1d00ca241e40040b030781c0a0042c241c1040ba003216000107103c2d030400b0901d00c5036003001242d6100e842d030405040c4a603410080b5004070521580070111300341401101d6000c0d4031000a1810545103550426003403200d080e000f410041c0001c000c4030ba449680e4140c0b140418488410800d40780ca520381441982e03c0841c00384d201c1c52110448942403001c0c0700c1114a4200108050041d0b00c10303550310075002e0449104c4214450181c107800c0d52036500c04100d0103008502901c0c0c40140e00e8904458404100c80f1420360b10f000340e090540b8680401e402c600a042c40c000281c50040c2e4900d010b06162804c2c4192205030120740c0280c1c11200404d00511002d00340280c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 56852035 1250 56850785 56850791
    0x705090106050a110d0806100c021507060e030c120a0c05060103060204060e0a03020a050d081b06060909010b01050a08041a010308040609240c14030a120b060306010c0b09030708120a 80
    0x41d40304c01940ca0305078046040028500b04006101384c10600008000d030540b41c1891034412103541e0004045240609042a6049010803410144405401540c0740c40b800d14000e90b1400e03040e014070b6525128064102446408001070305901c0c01c5c880c505548540360407c1c1926201d585900d0800e010b94414800c00b000a86402d45a011501e409500704040740d45c010001c00949141c2401e00244040441090301c80d4017048c841203440b20013140c0c0e20004031130404041e00d940e16010b0100480c3c20740113042c2c01c0c100da140440341075142e60468212442500780e420108844c4c0c5e100d14105242c108040210301000d400c88000000700440d40380580207513643c64648079015621803244148484541e840301c0301d2401c8148200241e18000c0d00000b400340e006605007190102ea424001e80303543d2042300d10b800040c0040420740d000c4000c1d0f00c40e108400800b140e0081c0b440c01e014000911101a40d103001c2c4c048440792021900947c410001c43d480030703921040351078030703448102422151528121540340080781 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 56853285 1250 56852035 56852057
    0x706060803070c1d0105090a0b120109020a0617010915090c0906110a0203100f110a02030a09090209130b040f06030b01030212060405150c04170a020a0f06050901110705090106050a 79
    0x144044c40c84103da08400203041c2580c0f0b4142041800c1d50085c05013040c20340c0e41e46000e003072901d81d03041801b00c580c8108000b081070500b501c1801071204180e4821001c0003040303d040030444594844003030445d02501710204141800c0008650032703c007645d001c05082ca24040f1094042c6c2c0d0050b0881041300c0482d29084840200c40758555104c0a120b18029459000750007030300c0451405074010340150340200701c001400c0b0303044281001e86500c22183c10700940d00105092180d154081982000b602c64100c0960800e08070f10080b4059070705d0004400c80072500d81e5200305c07881c2c540b584180181c40400e0b20071f01296640c1e04028010b48000c0c0010783c047c003c080c0b81c0100b003050006099008030340c45001000c040d550308020100a60340581800961760041100082008446501c0004000080090a40a1241c0c0b040110041065200841c0d42d40222800c00c9001d4010040d1640101d080c20105206180700e40310b0380c10151a90840355028902d1b5002040565000020305040e80d040d8861a800135 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 56854535 1250 56853285 56853299
    0x6030a0e010f1a0d0c05090c07060506010e100f020109061e053603040b030403030608190503090f040221041b080a11030f0706030e16050a090504080706060803070c 72
    0x18080e907451100300802c0350720300c0c4103401c0c981088070104d0b0140d4000200f00e610360000400f2030b0805e40d10240c0c4250085440c00602945205d4503030044000d01b441c83c46007081c0400720f0300c0101d152203100d003480310b60f403085009a030003900b014190950000c0c0400151640c02c022890390b010680360341b0102882c1200007440c0e43c405504c3e948815919014190000400209680c45070140ea100d00c80140024400003901c8544013020b90300543c40b03620042a50f03820111310501d086c00d15580c0d0f804404040326954003045010003115060041a100b0140104401d40420003a114050308030541c5018120921005144440d03454081ca200e0310b070244400e5604404000c20707401c40e00884001d50002954400020140b0170301c0c0e07640c0790011781602e0000c40392000d0181071100329400302c0d001c261286031000c0103070010300c2100442d10100b02031060700e034146808140e01e1000c40c041d0140803030b9500d0114061001803070690356a550300074000e108017506d51031b407203480ba00305d03a6080761010201c1101050007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 56855785 1250 56854535 56854541
    0xc100e100207020d020d0804080604050303251e03150803120606030103150b01110a030305040302190506010b0717180103050f01030210120f2a050408030a050703050906030a0e010f 79
    0x4a03800800d5400035240980820401c041b44840407140c030b01c810440094540000d01c0703c688168003e00c091a01d0b8a0911800000c071103119511181400088001701e00560b00720507c020445810305c00040f4211000105030010321940343e184001071400f04001958140c008020140904130126089050711104103203e40341c0001c6c04020008103030382901c2004000340350302520080c0c2c0145003c111404105000c141402c03000101600001c0e103400810007410303010042500149a00d1500400a064a40351070740c89180c18000c2041510340041d0000501800c03c4a1814041d0916180b6540e00145215150740351011000540402e0034400080c80c24002260803604903900074084041d01c03410301e442221000c92030f000341d0310201c0c5d6821741d500f0420b1283c03003803501c0060180000b0783c1000c8010900349500c442c0030105410420104400e2040384400b1003130f540358a910b41001500e404e510315003503655004001e101500524040204800c6103419000b05c03480d41c0c00c1c038000304803081024481e9425 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 56857035 1250 56855785 56855797
    0xc05090307090207051603051b06090604050d021302040806090705180a05100305010606050703030e010b0109060809100c0f1b020a06120204090204030809030709050403020a12050c100e1002 83
    0x10507041020104800000e40c0c00820b40302e88600c0a4613050706d0314044060400701c85810079650351340718071b20344580c844c1c038110131006841c022141c40d42031482c4000011018030443c0100c80c05a006200c20f0700440d01e8401141c002c020081c1c0044d915503454031840c0703544510864141240d8420414002440d0400c0316060040d804032824643c03899880028600140030045c000c005228420040007002c65030070301c03d40c1c024080d1030303560941d50403407410300600342d5413105008002039140c03031800404c681c0c0201001089070f1f460708008580d90346006505080003401851010320b60b06245200c550140c1c4a00919420100c030b48460382e14800d07000b210300201c01c08000094010040320f00c107005042c01220b84011620b06600050320b05516400350000703a07002079004403040640030a4000840c98103000300000340030a1202000710789040d441c0290390701e10140c4081c0485c00c410a8200110784541d0844081d41400d1003200c8a814102c001880140b5800c85600c1d80c50003041c000c9400b1001d05d00890320 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 56858285 1250 56857035 56857039
    0x40812071a0c0f1c0e010c030b040204140111030f0703031d010203040507060305180a050d1e050406080402060918040605090d12020d020702090712060e160e12030d020309010c0509 79
    0x1041c0b41500e00d482d402c9502c090400e0b030590544686113845022a4082c03124a004c2c00b00010903c2d030b10110b07014003902c0c600e8010300c0c40f444c014001400112030044071480614070034a0411444103034180c0742419032040703c074003080401c030020b462030500d50076801c2030806500302c0e000b5041104a424445d400c0b8001920004c0844d0000c44007008030a1007600f2054003c01c2da154003110240032a08041d1130512030712421502e6407c45200002c119800500000719203403c0c461b14290701e048203030028000c0c40340303010310707000d01800764042415502c81c0026101d407558054500522000c800d60700480740002240d00301d50040c00e100c00159513540100c0e0300180360b103003a11038902e191500a602c4010390810000d103464a6803d1182c000582e4407402c13014003030b00e1140c0742c200b0001075051584098030040d40004011340710280a00182801c007081e0910340740050728003a10300c0e01040300050300b0200c02d03100d07a82c105d01c40480c04603c0050742d40c4c01180103403c0c2000801400c1001181500c080c040d062a9a0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 56859535 1250 56858285 56858287
    0x4090f0c0f061403071d1002010e070b070314072402031609050a18110a18060903030503040605040f050727060b0a08041a1303080f0105090a0b01020102040812071a0c 73
    0x2603801c1c0c0c050802c050021b0344a032040346071070300b441000c1540b65880e01420070061307448030040307000d2042c01c2c00346a02505802108510b412000d40340982441810168000700300d0340010b0020901840700c0d00a01c1c030400c0c01610451050502c0c014001940040e6220303090411122840d1518600408619044580283c40e0804c00b0b480e00b040b1100d220295205c242040d501c1d404041010542c102c01008400700640f51500c5620050142800d4020f03035801580900400300301c1803002c2900201501d5005600120224003582e85203889140700581a10007495413203081c00c0490b280e0001d50309020114400e0b01c44011245603011014103031400d80c4500036120b1820412100c007035101d91115503003d4010541a1003d80181e50034a030340035001c40b00b80c404e0701e050422403003c1540c0001d400d500100c1000100e41c540d410310300060b40070710020b4034044081d40d07030704c8591000b03074000e40507600100313088402e036a0034071b140c080744402c00e03030210b0800c43d01480d000b05009458460011340602950105050b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 56860785 1250 56859535 56859541
    0x10b0a0807090209060f040602010c0f0518040c0c05070b0a1b0f03080612070303090321020c120f060c0d0e0d0c02090a060b0a032c0c06030604090f0c0f061403 70
    0x42c00003903000340201038200104100014a841d0050020001804564000190b114075040020400c0302c58402240c1003200400034034409102d00040b80d40c151004540005104005450a440c0080d4084000717106000703108000030204259805030400d1500d6407181160500c82103200c01c102006000e008010003030121090010902c12451035501c00406800c1030404101071690902c0c000e9540e104500180580000340b040110713034025000f1000741c2d801c2c0048482c0f04184082d46452041d46514003910448241111b029000c00074403506240450a880c020304049485800c240e102c3d04851490a0a01d650074900034000600990071010f16680d0321021145942000301c0400058111400c01c1d48654011449038201e000525035200a030307c0010f0a10a050030340303801d046001006002000c000d041d180c007013410100f90041c000340c04449a560760b80d90340000400030107a015000d40002326062071a81080102c030790745000d54125141c030440069840c94101e0b52008035000702001150f0078004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 56862035 1250 56860785 56860799
    0xc0504080a0b100b030c091804050c120313080105180c06030a090204060302090a0504050c09060a030303050a021902030c01060503070b070f030201090213140f0606030c030910020a090305010b0a0807 87
    0xc2c080e040300b1412000d000c040d903511030034030503031300290745daa581e44c0d000040d8400503180038094030714400354540d060b03c00b6141070346904c1d48076071030342c0301082c020043d040b5200850002030044400c5d0041c8910140341080e12841d405d4020a002c6400b030035010680d0700043e405a000041300c111615008119600c1c5070750fa40d18038030249c0402c40040360040e403240e0020005039207101c007040c42800e90744000140b03031908c1e0030003521703020620381c407940116559024800d40742c480f9071103841500e802d0f080200301c5841e410b6281000748203425249091500128050307800980c00300c002c000c00c022250084c41455181d004240d1500140e10561110074410060800007603101c0a840a00b01d0103400006084141a0040b607036825a030303091303202801d940fa40c1d070749010350305a84460341218601d00c046071075141c0708020403810301c405001198044c201100095000700100007040d00ca22800d8011741d1078030744148014042c140d450004079aa5403d01c0e010321202c3c01c18245240072201190001c0c1802490014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 56863285 1250 56862035 56862053
    0x9010f0b04050112020403151a041b0c05030c010c090312050307020a0f1a0c03060a06020c030a03050c07030f05010504030905061303110613080606030705030d080a0c0e0405100602010c0504080a 85
    0x8a04e84080d4080c80000b0124140d00e040c00f02c120241040400c003180000c13000c6c68072001c5120b509204030b00d0804061203828098030700b141400b01604000e00e8070702c56410302c14514082c04e07021410540c213222410b4100390707000c0b101c5402c07a885034440e0003002c05e480348203540e5400201e40140050380b0034450300010a4121401c40b0000340520720800104c091900e0802d5406811100009020303400400d2250030304021081c0d90041c5400d2000d09480140b620001b40c80e0380c103142001e001c018001c1000380d1000818001c400007941e010307051a007002600c0c50301070702030803003207405901151a01000280504086041b0388503046603405000042e0300f19030750024207860b285815034000e10b007486411040880007031074601502c081402800c1d6407400304105850441c4c0c60b080345019070800120101e17200c0c1c004600f141c00587e0000d0200e100341c417101049446040342c8912581c01403c1c90280440750311600050000d88041303900900405a0712a401d40320780c031a5101390030031356101012a0b008600c1c2d9030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 56864535 1250 56863285 56863307
    0x50a11121902091e070306080f0d0c0602070c080303070c03020c180610110d0e040b040c0504030b07030209040f0902030115060903060b130905060106080a110d020d0f1a09010f0b040501 81
    0x34134249810a01000315108004940840210fa5a6003050000380b4080140e00e941e003180c0030051210202c140300082040b0300c0c01c0d5000703100680101d400020010112000005800a881100c0d243d10340a60003c040141c14030b81600580030782d5035508001d0420702210b0341481e01c2540724419540324101440007c45982c0440c00030402e81c551500340201040c000044041c9a40c0d4840b00140104001c000c12a150817500b42d00c61494546038100c4150041d0176a000c803501302800506542c0c0751407041e4007a215944415901520340082d41902c0310850b4841015540240d000f04984558202d4010004505c0e01030140403402040040000580c0703070308498041000a4510030032030500018a1003940c200700c2003141c441c1c0040b0700500c080c41e4885402c90340f010f202c19050003401004a014400ba12606040c1c1264079000502d0100100302500580900c0034281d200300541d1400228004400c40f400003418401c0d000342c070001907083c0211600344160346111503094a00b5140c4801560311980e5a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 56865785 1250 56864535 56864551
    0x31e0724090501150e0c090904170409020f071a0f192301030302100b06120405011808091c0c14030a120905040507230a0903050a1112190209 62
    0x41c4001c000041d020b00403030040038190307032079015410b0811036110040380000700390b200c0c020001d111612a960b1544042600160018915010000c0862a0311002d20880d04184a89400000c101e028940346078020030141d40600700703840d00080c94901820030702e40b086d5040e40e10110540c02081c00140500a02d4401e011061400078010b4441e01c1a04508a11400000e800b408160300410034107030107001c02c000d0181d0f11807040004010400004a850064200360290300700c1c0400010100039095009a9458072180c3c1c501d019030184c7d10b02800136502c4244c060b0302541c0d40700701610406503500041020540c0c4110181e0301d035820801d04515404812000c2c81d890b10850b840380022480c002d0a90301001030a588484c0b04a082c0003d01040d194054904000c018600081144448200001034201e20703c0120060b0344110825088908654641001e4228028000c8030002c21502a00036a040d04065940003080c402d02607159441d19054100c24126180e55442d0b000107180156407140c0c01000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 56867035 1250 56865785 56865791
    0xc02040203130c080d020106060f0203040e07033305010e010516050a0b1008070501050c1e0f03040602070e1008030a0c02130603031709071a09130509031e0724 70
    0x21584400140c495154401180c40e0840304110345c019a080c01484003038029801c0c40e50004a104000075074a10a51040341c031040401d40c0850311841c0f198200c0440c031b0401141030301c10402e9000503420040d0340407180c00214000e200c0002819405803542e5214090161981405c04210300a40b8045008804045070b01c3e010342103030f880024034080c0c0c0c4280280c0c80c088400b003080d4202080762b890030740c09810039814840c007880008080ca400240ba80500390501c80d400c00705080405000c0d1070500000040b41107400f01050200e00190b00186d148100c407a25aa1801c050300c5403026400402d00b01d0043d032201c0d030404c0200301c0b0614001d4288100446c8090305512001c0e0801c001003084802c1a00120b000542c2c00c0001c100d20310780b4100d07040c1c00000c120040d190251902083c540b40e44440c1c40c25064043c070101d180c0e40e603071342c48888000310308195220174002882c1509a5036201e42c00048044913507888400383d00000006a015140300540c08042c40d0210079094030102145034010b02d1804015403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 56868285 1250 56867035 56867071
    0x30b0604060507080c0a0f06051302060702010509030c090c0705070509040309120309120605061e090a09020f0303030903091306050a060302090f0a08010c03241509081b0f01020606010c02040203 85
    0x341080070110150007a071f01004110300c10700d0130b43c0c1550400780c4074814103040c1110b030b00301607543c21040f15101542400c00e20b50355030310400840d003400000b90506032304c141e021003000844014000185805840b071010b0390402c603150000c2000014045e1005030004624007000d02414400c0e400c5044018064100950a42d030f4030354501d039403c07500c1c90080700e0322500d80c0305221060400109941c400840913641348040c00c800300104507103503c000c004040d865203030b90707a2200b136454050b042003c04001505a0740d5910300150384c9503890b441610b0140c0106800c480325490105648648016590000c0140003003500d804011006500706010066010f071402c40f00001c682d40b0031a0400081c00032400209401155110140840381d502c4080041c103d04541441804a61003540740f041c2c1702d08014010801d484410100c858070b03030640004010303220350440000505415869200b03007807011141350030141c88407801240c481109032503150202c2d201000e1480146050b401456010028032100b403d0a1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 56869535 1250 56868285 56868307
    0x31d0a0803040b030c16051b0303070201080f0a09020d080301080f0708030d0f06050d120921140a0c080f0c04020408060a05070e040f060e0603010209220f091103010c030b060406050708 81
    0x9441c086c1120254003900070003001d542442c1c040d0701da2000841c007440c01c0045940001c0d2800e14014000154a110301c00014060000c1d98071182c4c1c0c10350068001c880a401510300040305910030300a8181911681080601d80b0f60001010026a401030700034500300f410005900d40500350b070400c041c180e240c440e074000c541e41d240c0c0c84002405a02540a0031001070f2086000b500040da04d40059100b0844402c107405406c1030b182c4548652a4462944400700114014140c02c001d800a80100740b5200408006019100001c1074440910306c002560001200d944c108404c91195200701c2000d60447d030005204d003011684020761108250410649143c802030000302200c080c03d00080210355070319414403940c21050700c80c0394002020780c021443d014541c00090030700c03010001c28010050703036030113070f0039040d9507d40101e00f50220a00307080c090b2103400d1501c40c2002c108010080e0103907103400240e2807900c0c0f01e401046020440a000345140c241400741c1150103502c400c1042c1c4a801040100700c401d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 56870785 1250 56869535 56869567
    0x3150b1804230304080705011103040b0403050f0c010315030210021e07060206100806043e0913030e06070c0315051b0f0a0e1903031d0a0803040b030c 66
    0x403440b0300ca1400300b000a6000c0d0740608580304400d014650310600003400f0450300000c940003a203509007018084800d030074801e507145101d035030401c440303084020800004010000400d4a40303259020141e40038115640c00440840700080101c2046030421541000981003d51008140f6030180c816140200811204d407094070b02400d0590b00141d01c68a81000b800f40e050110070f400c50555401d184016141c45851603032180040c00140418602079941401c1841d4030704541c0d03074801d02c4d03981c89110400b0124110804039840d025030740602034440004243c800030320361810280303501d07499521207045c02c807081c4021900700007821102980d070f50001101089082c3d188080c0c1008000021443e490110040c1c60481d10341100d5480740300c2e0510200301c0001c2c162056560f020128900011121708440002c1c034540c201d500307804400694010040103059201544081091f010462080c200144101348017484003188100449078106001c1841071048401c003d5810240009486d810440291085450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 56872035 1250 56870785 56870791
    0x2090301020c0609030a02120c03030a02030c0c0f0a02040c03140106110a050105010905060f0d03090b0711120c0a150c08070203150c09010206010b03010b03040f1b030f02090a020403150b18 83
    0x425403002c46c1d100780f0103038100704501e0709400b1900b07440d04000f4042d003500c0d0390b4003003e48140c03522900800000c4d020540351068456200710902111044003001d0301090301d84460f401c09902650900310107401c0070b0f000e802220b0b1000084400c02068ae80b070100d0442d007038104084618818000d8400301d0000c11400d00643d80648101d010008443c10100b00f0004008013400880b800344400080c55030203c0c0c0c1046102040302c05902c2441e070768034074501d841c0380c0038825070413480c0c0d005500003c0c01c00c0d8810002801040180280e8800c9840b035155580b46024a101804404c00a942d0142d003000294284005c1d04030544054110740c48005071070500020010111410151040080340681c107541e4104030050040c02405185071540d4107003541c80b11288001040500200d24400c10300040204e907030106d4040345a604c1c00e15400e15224501a02c04984646090341f0581e10070303010075410a400c1c030032102280e612030005000b00e19161155005842c440400640c000c24402100ca10326850100d4284 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 56873285 1250 56872035 56872051
    0x60114070605060a06020d0c0605040c090c080720030f0d06080102030f09011823070b13050f0402030709050112110f0a080a050402061e160501020717070c03020402090301020c06 78
    0x220b0b85080020300a00032041d501a00466000203a030102064008a1903030196410201c0490070365518200b07800d001d1801e90203007001914101c00d24280c6a40721507028003641159035110354818581e80248907000740c90148185903001007005d01140c004103002400882c4106501062041c1c1d620140d908a810441d2043e0340302e000c0b84100402d5400a2094488410001503041e01c035101e5900d030754091105004150341c9450302c3d411202d17000f001c20000e4500409040d100c0c0e039a40c0b0000340c5009819244c501c80c590180021070100c1d40d1074070b45402074a11881081c3ea0b1440203d1402d001151000910505404002c0d81d0340014a0b0f40c0068200400d518042c1c00c85159440300070304401017100710020f2111a0340380c5000141700050392510225403c072085a00b16050800b4440710400642c801c1d40072a00d400d1b8400001d01040100640140030b8040c003500001400c500f12900074011486140b90040410315000d00600c01031800340e019154812f0003400060904000401c6686005001c1d51680 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 56874535 1250 56873285 56873291
    0x507030605070f0507051b030c0901240309052e020301090506090901020a0c02100504080105010f150f0c060f0f0f1a0f1509010c020d030306080601120f03080601140706 74
    0xb1071000c0d04510022040c465501e4040d180c0307049a12555243c0740e8400c0e40d05414500040d45040c583e03000c00c0914401740c0000c1c20a0140e507510740c241981c20301c907098120041c3c91000d18984842c2c1c040e110712015160001c01800c000e08140840c1d0007044c0d04c032a45c4c07072000380d12801c09206a0415201541c0030304034009000a85082003000c1080040c0000c19401c503da004119006400d40d112501000c8282e050714400f004a6010030141c80c50302990300b000c03c06610f00360000130310700c022802007030407030b40c2c8601030081c00320300030104a44800b5070000d10700100d400101c842001609582c401c0d4048000c8490011f00840c40c95402c400765846010184480c54642ca188140308403450070360031814900302c0700010400c8400000c5143c0c02d14018481c50015004150a038807a4000e21070003204650051200e41c08107240d00c1c02030020003040c01000080e00c25040003181080c0d80401c22076015401032205a10b40c10760f6981100c14500080c2100d04001e490401c610b1081c1900b03008d80280f5114100c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 56875785 1250 56874535 56874541
    0x90c0c1c02070b04081f0f0906060e0c0a02150702071d0403090608061513080106060804030806040b010c0f11090903040806060603060a051e06030c030406050603060417160507030605 80
    0x2d00e03042007030b0041d00301030b041000108810b40d070010310689001d40742000c0502907a1041e0781d440040c180603010400403420b0003100000c200c0a0f0303010109417030b00e40c50000d540f43c40d401c4500c41a0b004010364034000d1b911020005440e0508202d040e0303031080c1c480c811550546e4841415003000300a130404580a002014244010907404c035107078802404043c40c10040350320b01240060b410840d0540c117030401d4000080c03803080803d0810840c2000d048030800074440241e56110090022074105d40c1500010344950200d1214503003805015241c0e00141d499201580003078889040c1400c41070011203000c41c4654031035400ba100e0703c054502c2074802101968032645401640d5003803010040c061441141c00300200081e81e500e030005081507400a4035034031a00c4003900103007200ca2250052642d80582c0100420883e01c203144020b42c030603449924148441c1d1140d0301410350714070040c3e0b0001c0120a0105888188071b80a001070b14903184021540054007050391581c0d818811980c000b6038009803500b0070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 56877035 1250 56875785 56875787
    0xa180b010602061602030a0c0501180f02090907050a030204020d0e010606020304170102131e030c0e1006020102030f041101020a020613030c05090c07020402070c21140d02060402090c0c1c 82
    0x30350f03100313903428a40d03800c101c0103480c025142d1007005007200034407115000010600c602580403070a104080064100440100d081142d1000c1410104a220b9071040c00080d4001c1c0b004101e103411030f5009415940c60b0b074295802c02019400642414043c25600c180c1c8075050748090107500004d004580141d580c9a0411700d6404005900f28000314490b80100502e040c02080900c2c204100d640c02001c100c5412140c8410440701e41d41c07540081c0181107191008a405460074541354007680105042081c808d030780d000d040e400d0b0b0100300d0b1074500c041c0240d000034001c54080c450b1070075001014030644280661942c0003d0345500250f40503002102114420300030008507000d400701500b030440380704105140100c800e807003520400a00900a54000ca10f09040010441010029200040007050740d01415420306a040d8100301c02590702a1042c5185010300602245607040ba0311982d02070700141d41d9503002d0001001c005404603d4a881c100b050701a41c210a001c040b607220030403404004a1080e401d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 56878285 1250 56877035 56877043
    0xf121206090a09021f021902010804120507080a0216050108090d14040f03050102070209060d05030a030f0b06070f110103022a150c030f10050109062001060f03150b0a06080a180b010602 81
    0x7e803984960808110710015030780095000b81c1c000d40c40510b52061342008002100d80340282203008040e120046022401180c0205190a0300199202c2c6802c2040d65100111451380341032302c401c9015004908035040301807292401204c8001c40c04640c0b4034080d03462030b06a0252b0803d80c01610282d6020501000310701e030490425803c00c0040707410418903101915199103234440c400300c82d424181d4a150681c0901407503089103002c80130003010151120400e00f082e030882400600c007200c005603244217854156000c5d1080d0f40020540008007a0095a00070001d10000c3c25660385003d14070800300700c10004405003285503c500c022111040d1a420204540c0158084c05400e0b61070231013a1907401d121a0748c0c0000130f00304070380385450404106000400d514030442d00c0362243c10082e5082c050086520760172a007030001124407420900095810b600c0d40b800417554004d48890303100d4100703601082102d00c94280d140d04a03c240f10700183d445503a141e24000e400c5801e070b00b1508003216200400ca41b5070188 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 56879535 1250 56878285 56878303
    0x120305153015010807060905010c0507080604030e01180b1c090c0906290d0504020d020a090e070501050c030a0c020105120a0b040e01150905100b0403050f121206090a09021f02 77
    0x1800405e062030400c00d0242641c5030034050345041004208101d400e20400700301d1031000340030701c1c0151101414281402440019441d9049022a07401a1035024400c0e0049010b02214940e8041c40c2c00c00100e201c000c0304102da030130261514280c59000030008280c284104500800c114000061000c0c80c0194860990249400036104030800341081100300b00c0780001c54607066000940003901d33a41d503100241e001c0b4500c60000c1c2d0031020040c1d02261610f0141d1142d21000c80722012150420366490044800c0c0c4110b041054854105000124642e03002e419a080e00d1481414610f050400300203400741000b40441d201c145042d190030f502c000e0380c100307481810a038400140080c00440d000802c100300c10200c6100382c11001d40c0d50000114454100341c0441d0280000074102e0f5546c95603402c003d60b560001605104072402100c485400700b000043c2192411800c242014086903105810426510342c01400e2002140d2034840d40d40040c1d0310054090003880d948040d40140c1820301c440280f51039190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 56880785 1250 56879535 56879549
    0x2010f11031509040b040b100305010f051f0302012c03030a0c020a0603090305071205040504020a030914031c0e070b042301110c040504020607060608070312030515301501 75
    0x14400e00001c613901c40765051b441a085101d40010341c03610503040f448602e0a41c006015946003040c090f00c0780d015500424010f1f0030700101002e41d820580701d24100f192107840028089040d480000409050320340444400000455441941503070b44004a03003554080c00b580780010f03420000380b000314504080312002030121490f04001c0c034059980c0140c81c0d44039512000d00814004860044890f2040c4201c40c0a001d01800640d1143c4000c203000d40a0030740900101c0d0a0381000d1000400084000182d80074112904e15142c0e1038855112600000c00c0c48294409050003494004910030005c03500030002000288940320714880000d024807021504000911304008004400c690850400160389102ea00300b1500001c680e1190301c0042c0c421b20030100000c2c00c1500b13091000031088070124062045078061248482c040814000403000c55070b08460480404820381001d551a00304036613401c402c1203078418200c50701c1d0551480c003284080d400f08500b45c00d5004060700c488504245078034034010510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 56882035 1250 56880785 56880799
    0x10e071b020d080406050c0f0303160503070201111201080f010903050f0f070609140d021212060d1406180106080c010e01090b120115170403050a02010f110315 70
    0x1024006062640c0814140900e410304005034081d941d0b8440e41440c601c0e8410b4515a4440d5104005070998125840080e050b028892020001b0003011040300d100e1034000c09030078013290748628150340c1500050240c01c03c41d9641c940e40b0600c1006840204a0030401940400056140a0640740740c40580442465240d04005a1800203500001a41c0904502d41e0031241c50318141c1c030b0001c50500410b80050000307801c0082220500c0301070800225907001d40400e0791b8038078088507802eaa4a523902411090008420443d000e141405000a07e0f013152009140e00035030412a1104510620780e2401e0640580203101440113110a1018224440300c540b0000e01c64545040c1055403680c8500b00030034140039201041015517807042c81404080c0c0040341d240d41d1168240384070a0403042007405500b00803001c5010014059000b4440c00207020710030f412840c00f644d00c540d0111400e40012119006564a40d4503200c03d11405020b83d50103d020a00a03540704d02d800045401c10188000b0058003440c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 56883285 1250 56882035 56882041
    0x20405070e0108010302120c06040f030c0806280e1b040506030c0d0b0601020c0607050c0405010e0c0a0f05091206090607080c120405100f0c0e040e0d03110909040503030f010e 77
    0x40c10003032a030f04494048503140c400007500c0e03440741c0c21b2801c00c9032301e254440400100440d0b00d10b008090007096a000c0d440301d101c000d40780c02c005541c0e000305407000807142060300b2100b10504844098401c03402510079010400a140821031490400c00c6003100500030218584042c10f030405104032940018100c0082161048100211ba000342010101034a9141c000f40024480d034002c00012010440c06840b2030366032741060402d60b8544004200681c4141d01f04000000c880041c150200c0c0680d500403070036498a00c050500ba118201c4006228050003000c3c002ca448a0342c0746440446401d102c0340150840e8607003a8081814010010200c40c20f11040c01c05104580881c00c1c159086c41000b41032480841e1110b050007881c055120b50322690550403c080103588030156084108030280030b446a915000320807040000381d81307000c81d0740d20310340e480030700a0000e42c0e00c01c0c0c12042080754922000c07441c181164010401400c001c660a407815400002841911443e601c1c0043c0107000039502001542 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 56884535 1250 56883285 56883287
    0x1d0609060f010e0d06060302030d180504231302061b07080d05030402120f01050c0d0506040902090a0c0c0609050a14070e060d0317100501030f021c050414010501030f020405070e01 79
    0x209a03007582d0f400f0b0402d4a40b800d0405c58a80d001d2009550000e00f115507007042c861008107003807101050211181e84907100007a1034100b902401400d00802a0805c00b41001001c0810140b600141184402807a54003403c4c05030b101c8030000c0c024102c0c0d28100f201440042e00807185402d0a0342c1c0f011b4038a9002002419887d40c2c05420749402c19030494040a10698025503185071180038640c030750040d460b0005222248607040000c110354101c10a06200c60790701e08080204517600c44101075002034503d40094030002c040d030711080019205043c4000710b80c203941c480004445090300101d550354004c2868005102c40c3d11000e035981400c100c010030700c0d14142000503441c0c4002410a0380503d8520800c07a041601030405408002d00b840d940c1e02040ca0450145d404500300340c070034240071900c2c1101402800503940202e444510060300d103146880203114408004000c0144142c034510a243e45c6210030810a02956000f14015844661808014010002244e0700075004c1020700110003d150610703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 56885785 1250 56884535 56884547
    0x150304080403110312031509060f030616030905030c01090309050603040f03030216020d030315050a0b1b0f0a0501090b280e010204170609100b150c071d0609060f01 72
    0x80d81d808050f40301d0030340703281010901d07242807401885204c01d400300030440804c004002c2c0781218041250012416182c203024403e013049168203030303a0903820400000344070300081c1c104021402c215280c0040e003c0e0740e03a21003c1c1150041418001c2d01d9446050030301c01d1507480400e90014102c212185440c604140e80c80c0303002c49040700c0c401810b043d0089400795680c9a4002e400060540141c28880d5060180c5002801020044002c41c4011003100010900381051a50340c03060f02e94290800d403800d03c4410b9810b001001c6e2891140312840346a0220b10312072818001150703d80c3c41030703002144480a40c54540d8406200500a1170342d205003c990324815214911041034841c4103e40004d0146100040d09000e4071594024408902079404c1d204441c0c0d00001b0014801c8607544155086410300d6221002030b6442c00000c5540f1189419059106e0702c1c201d401404d498a00d4812164100d595050300d0100145025010545082d400c041040c641028002035a002c0d000f102c101460340003c0f400a010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 56887035 1250 56885785 56885789
    0xd0306120b0c040e0a0b010906140409110d060b0a090803191805060f04031104050603060402090c0d110403030e030d050d090203030708120711060c030103030c060b0d0606051503040804 81
    0x708940030004144002070107070496019100c0c00c8005081c616017181c111340a04096502580041c031a80800140306102d0740440da9040c2a81005614141ca4504420702510b001e13003035080301103020464010040031621a15004040a281081d282c040a40010708401c0407688051006e030000c000440014103514814101c07018541042482604010505c80350a0003e03080650401c0b0002081500e204d10300010300b084a1061050440c01200720042c44261002604c044ea05680302c80d02040c010710741b402c062a4042e2240c50901d0520151130700d144240c1d400b55080c2a14110300107014001e0680c090304084482000368001c02007810311150081180c820b5003004502c183d45d55404108554007403040f103800326000315000f52115200f10003240320751000d84501c0040350b61704c1c494984400c804100b080c4141d546190b000d00716840e40d10190b8034500e08080c1155406d40d07801410f5030942c2d41074544180320780551800145141000c09100c14040144800800c0c5103044c020000098401012501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 56888285 1250 56887035 56887043
    0x60206010b0a02030c100b1c080403020105091207030318050d050706030b0103060e0108010203010f08060f0103020603130204090f0201091d0a1a1305090c0103020403030503070807090f0e090d030612 87
    0x182c2da9194040890460203201c1c9100054002c1412580b04c03445160000000001d0440701c0d0311288000404411140f510050001d0a507501440700b00090742c0150040c2601400c0500340104140c00c507000c0c1030520080340c20443c0880c4080504c0c465280c03403480150301404003a64031003004081c54407825502e240e1889240c0c00c16803500000c9003244d1103604800002d00c075100b810344a650319002554041c0d0800d025051664081110000d010b420025100b80030b904d0407082d0301c25507401d5800b40b21080c0d000038401e150003801814081d005031118807400c01642d005031800082c0c50b0382403000400713007a800e6100c06c224840240106040c1a00c0800050300200e541c0300028088164641c444e0168185409081c3d11600c07105030003801e40807a0700b03e5071240b902c000550721801098001035080380617038080540050010b000140c41540030b00c1625401c0301c104d0922241403565400880f070a44219000b00103542217100c1485201c070f0302040910981029801e0500c05130b0304060b140e904980d0792802c0a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 56889535 1250 56888285 56888287
    0x6130203100b060d0606091a09060a03020306040b060c060601030b0f01020c090603010906140103050c09010f0b03040501060f060e0910060203070b07050c100b01020c0306040c0504020c12070c06080907060206010b 93
    0x10303a01c0703004803030701030781406130900190f507450101a00f004550300c684698800480790f0000300d00c000608030751200400516150030504070340030480094200800e419081a84e84114031101d0340c4074800b51030401c500000825030340c030f02030000400b600e500303075080342c0100c8401c4050701c600c1e130300400c1c6d003ca162421f646040559a40030000307805010341e0440a000355190444004210240062181c10b0360301a0040300c800010480c14000719450910602c2100c44d002582440801d054400540e04140950004501641c60b5285040c54560310b50100d00031442d050400c29640c103003000c145501c207074403205a10a262a080005e03459200d1100000c1c003451002c00060621402a8140c500414102c41251111644690304000610b822991170b80580320302541c20505180000b080c503c52070380000f4004d0708620b04810300003c1d40148141c00c00a01070381f95404076507001180981402c81c015400c14580c1e901d081c401810081014000c0754054010240c1441920340000d82ca03030460386102242 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 56890785 1250 56889535 56889551
    0x604032018010501120212130b0f01030b0a090311070906141e0411071b06110f0a030e030a020405040804090506060f0a080402011103071406102306070813080613020310 74
    0xc0020b00c81c04660b00d047c0e02c80c407824032400900c40c144211803c0d1259503510907a4541c1c840a480d015001d20004007001411f0001400070b582d5900040b0106102e400c0c902009801d40500a04010b0a0b410540382a90740e0007080151040045040d803d0480c280d9045186402c105400d0f00441004413600c3e0046032034110b010340240c030a00071550041e030800080b200180d9803082c0451219460700c183c034001180380c0d8140d0380c10344001c90380d13203a140807003002411101c203965021764040c4c2d00c0d08141c640c10b0184030301c402c001d6200d07401883e1113140716100322982d4900302040c120031076002619840c00750505118094401044c601120301039082400c00f411580e132188012200810f0480c9180c0365804003082017403c03c100d42101c0452040040c3c00d499403aa105010150300380d041e8462405012407869015004010882d1410120030014250f036184c0306041d10b90507001d80c00152025428100d0394020081101d091002d150414410f06004002c00020340000341d442c00140151440c3e25030350075070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 56892035 1250 56890785 56890817
    0x60301030602090a05090103060902100318020f011202131d0402030304030303090204110c0102030402131b08090118141b010503010e0a1b0f0212030603061b090604032018010501 78
    0x103130009100052000c1074075a101d15001018080080040340a168403506600040e07019000300314800f408402c851014030f0091b020020020700c903841b80c605001c100440c03000e100d400da000030070382d030a030303449070394144603d41102007804446d515524800d16101c8824400103a40100403101260740620b0085400c00f140d000260061200c19034854441d4400107440104441c10f401640c401c0d4000c8980a01c4141c029500ca41522030008045060b00d10070405c02c5080c1313005a1229401c2041000000340b2100c0385070320341c0748941c2214000e95910354080f0526615000420071003100581610415640f09001c000190450006018206000e2040c0c00000c0e10148580d00c030059511003001603462403025010060041041c0d849101c00501504486102c0d1140003001c03a4024200076009001e0340c1e03502e0744104440034a0345041e82e084802042030300515600e4030041c1c006503000790200c0e0091101040c61100c1c40da90203103214024541071441c200410012078049046030020300307206031400c40b8a20 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 56893285 1250 56892035 56892049
    0x50603010609061107120c230a12050a12050309060a0c02030a030c021005041110020304030209040f050a080a02061503010c09060806010e19140d0f0609030c0b0403020c01080a0b06030103060209 85
    0x1b00c510310150b030105503c1071058801e0044d044981d882c04250580640c0d960200305500100045034104000001c20004a000a071000000c180105c0a0302d00448036980e40d4505000215206000164007000703200410f90180030301780d0056444002003162218404000e926401070394851024160380d0b00702c403900c4900074042c0f0621280c00060403c803030b103042e140280401c48203188a42c014820811880b1640e400003084078140c13a0014000c0c06c0c25a155601c130036500b2410201260b550055060100000e6030100141015145c01d0700a00b519244c044012420f103aa00c034032040c4640c0c18218164055034120040341c4c240d4016251141642e0b0b91180185c404030920b2030500e4000501590420580c4520010b640989442c40315044c9000c461004103e61280307088000341c00a84d0142c055000a8095070084c03401d0341c82170034061000c00312070b19110b4111604440a50140e0404100c400c1d0740d40e485525584c0c80380c41800108102d6802801149690105000003409568005000400e47e0342e540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 56894535 1250 56893285 56893289
    0x41b08010b07061d07090605030102070b0604020c0a0b07050c010b010914010c0c0515090901080d0503010b07020d021314060303042303030424020d0504030807150e01020d0606020601050603010609061107 89
    0x8512044d03688a48880c6542d244614070580048910301080800c1c51314044c003c842000360840c00002158a1b07003400c0000a41c4460304000c0c1d544039209480c400a50307102c1c2c0d102c0c821003158840b1901c40f10202e010070700307403140325511364100840300e081804032030a00e04004401c5102842d00152030203007454001c0307081c1101d400c05c95100300221014505014141d008040740030060f607007001148d0780c5441140e07481052051810118005200510022610000dc4c006090005041880101458001c1401030a24070b00b8840d030161200385c400e141510041640760002c1041c0e00443c41d16117003004d071165420031102c6829420507010000034940d642001a240906100c02d807039412254040744680581c900703800c1c00386c00b50103100d02102180b8010020340742201d4020049916101d03050741c0390401120600d044540ea640c0d514800158100248003078521115085000a2007505144020b4540708050b44078030720400301000144421940610418201d40140c104002c8045200903640c0c1080e00603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 56895785 1250 56894535 56894561
    0x2070201110105090705030f060c0913061a030103120f050a0e031e030a08010602011b030e01090b0405010e0c0603090c0f0d290a151401030e060903030402041b08010b0706 75
    0xb02e41441134198000c10644200d420031822942002d1f0b06025080d00e80d201203582d020800814044c3c00901d08060030070744aa10000200010019154096514000100102054403c0010005000300701c906c180782c01e079500b91400c0c40c00100c03100e18802051031181007840020007860445142154800304200c045154040105050580740754400c0c980e03d4005644440000b6410000058001d006104070210b441c18000144075420107494250054840b6512181103503503109050b40c0442c0355600c0e1580140d202d480080b0700400000350007481c0c04101079031117104002c2001404198000050100710402c000e4035040d1181200500040c041081c0503800307040b910305020f0140b0202e095030000041c420140408044503250108030074201d41c42a1b046101001c4452412710002031541e02d0441209414503011600c070100305c410905004003610b50780c20300e60001c0103000c210314041c003458650a8403103800e8200c00b10700080c001c000e0203040c07090b0002000f00140e55014000290403601c03140840b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 56897035 1250 56895785 56895791
    0x16030509130f2c070306091e030e0405011406070609030201022a07060804020d03141c02040302090601050306030d03050702100e06040308010b040b04090b03070f03121101091203020702011101 84
    0x320001d9400f0f003140f0060340c101524034480564000e1002802a804031000b040107125a0381582d950000030300c001c40d015030f12020503014002d100200c40e084007501d0351103a03a0300320300c009800040c170003a154181c000101210300543c012040e074440506440c4402e0f00400302066030075144c00d040e8024429004c00003050003011a05000b42035400310f200100c05100000c50b00581d580318411140307401d00b030790000d40c80710b03130000405d010038070601d2024a404460500c0c507103020302d015031481c1c0702d031583c201c500280713034000c00c0c00c10952609480d1654044400c0c20f01902c1c5250046c0040e07110407055145a09260f5148041402c15202300000103440307404103010070000b000324981940d00c0b401124102c0000705810004940ea100d64800e84040b02ca019090b24101420309000c0710180089940e419003500c1a04000122a20001c203100700940c05503145140050f160040140320180490021100340e040801200c0050030300f26082906280d80c5c41c00503112240c42c40121148a001049800342e507003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 56898285 1250 56897035 56897051
    0x801020a05030906011a0702040b190909060b040905030a050c030f1803010f0e0d0f020313030c150c1e080910020304091404020307050907020703080c0303070e0102031603050913 78
    0x1401c0310056004844400c110340c110707031b42c50b100040c4903200c40e090b0340e91800091020000506003030704041548040101700e160409007902d40000142815032100310f031a61100304c90000d2081510801c0401c24041d00d080c4101d407010b41398107560740f0500c2d840c6000c10000041d224403a036814400d90381d5a500c8891011381d5036644401100c0310740050040341d48079520384500a40c83e403101c1d11900407100c4040e8003800e10362144c6a403d907142c40d5011014030a60000b0490740c0c1080120655610256201e0050b403c0031904202e242c003400c2190410086c00d204800f041708020603900c0041000c5a0800c014444441c1060302e0031140500441d0030240d040a6100c80041065801001410684d0341c00c040c100109602d4503200c8401140c20345000e501034000e6001441207041c000100c9a10501c580122840d05549544200c40c50740050f0005040e03402c084140021198880e0200d40210003d2004500380319145c1000c00200043d8840103080c0400051412916102c003080240b035034560480800c5480c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 56899535 1250 56898285 56898287
    0x402150f04030c030308090115170304030605040506071b0807061104090c0f121a06030c070c0602010c0801090c050901030504020112020a03020301030b010512030406050a230a0909060b090d020a0801020a 89
    0x200044c0812400b040080000446e0b0b0401446105034003806155420145c91030304441070351466228080c203240d40000c00021002c48c41501036103006900c00e500424607440c0029008001044007071100698078104502c090100d540441034500c0c054000600090803103108034060007074441c0d640807071502d41c200b4500c4a0041c0d0400f00300d0000f55100d4541002c0000307620034200403075001d0041c1407941900007140d01d102d0b042c1480555441000c0d0b40e121841e01031140c4030103051821075441080180e4658620480250380700c10090f004294403401817118101c07190340030702a0702443c4a00d41c101a500d4000605580c490f680201c01c8e51540d0700215541c00c100c0074001d0107588240030603984040c03110300024071b6041444a40d5a0018400080c5041505240045a40b5030055017500d081003040c2c5a1030b4800901c000080ca5104091f10342160740c2d00d03100c0780141803030016500c0b96800a01d002810001101c1440484a04a03002c40d041e0f07076810718600c0000c0d070083c5245c015103d00e61011900038195 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 56900785 1250 56899535 56899553
    0xa0f09030b0c030906010b04051c02040207020a170c2d010216062c060406051602040c03020307020f0703051b03010e010606020708151b070602121f0801060e0402150f0403 75
    0x5a808801645c1c00c9a894000300d0f00c1902c118890603401c80141c0400203243c002380303110945214802000581b03020130b15000210003690603000100e000700c450030704140071502000001c150140a40700000c40e000081c81101c0380c2c081c0390b1241820b00100096012040e80b090011405150300d142c404801151200001001000c074264103642c5e29800d160f0104030640140032003000c0b858020306040c40d040c146042243c3c4d640190348806070030745171024a400182d86600501c54000d00c2654016240e2814410003442e11480169a11160300031980c180041480403031400d84103003503e100e1110800907200441e0050600e581c0fa55555440c002012601ca40d02041030310880b105071046034241d4022048021074120140d034446100000c00c00c4491040021402800042c1c1c043e600060400ca00e00000d0710555108aa4819501042d1500c03600a01d804000e84800351402030000c01c00981820104004a03801800c00307845079001c0480f02c0b82c4243c01d001260741c1151288401c50701c0d2075491401c1801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 56902035 1250 56900785 56900791
    0x2040903020c01110703120f180806160e0f1509090108011a0307060801090504080712080f0108030a08040f020406051f030c140304030315050301110d05010f0602030a0f09030b0c03 79
    0x7100d100d600c0081c0c84d00080c417401500e410126450a81c1c9035040182c400019140c405400d011000c0580352800c107481204000901c00000a84480d140c000c0035002c0401c45841013005002c0c04e181c00c5c0d605511519041b02c16502d0607960700180300702d1400d002c4514003d00c01d035107500c00203240002c07480a406400c1054540c0c20300fa52005c00c00d005004241c0c59440e41d00071400003035601c4004100c12141038104941160185581d41d00d8540c580c2c540c000e071134561a01d0140801d00d0f802c01e110740c0c8030000e2601401031803080003450408050120040c260180a040913002c80e081d04a00c1041d0350f5203a000d1001000010b100e540304807040202e8000b01001400c170400804c2c40c00140740d581030702550001c8240c0f48612601440c0d40d0351a58107900a1140c62500c4100704201e80020615440c2449800c10b4075840c0820300d611281c102c032107841540d10582010112080030310041082c01e4000040d90806062404c141183c0106048102c40c211202e510140000b0400000e02603003088400040d40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 56903285 1250 56902035 56902037
    0x1302131214010203130f0f15020306030c04150e150a080a0b0c0406080105120a0615090617060402060c030705030412030f03060509060103090602040503030a110d1418010201020702040903020c01 85
    0xa20440070420305080380030490382502c85500713070001400040d040c00b00407003590f80b0585910300d000d8102c0e16000f002800c0e490301d5a0040b5030000c240b02c01b0781f0302000b207001850030031a0300b8002100005001c0340607240500c40e9003422094040414018100040320401d5280050031130790ba0b00e9030303d039881c603600c0d080b0f4a400da036828127100101e480034003410115000d555160302d8451440c1d20305003d01441c0c40b00c44143c03918500071010001d000401ea0300840c600c20a581c44001d036807a08110400003210604c1e88240200039282041c015802c0c1c0201e402c6900c6901202e4160701c505a0006850461284540090080c0030010300070404010910304806081c0c0a561450038120300360b141a42282c0e0a4007641d03502800e0080090001e610940040211910403c0f01604090b40c2d98042850754000d05810400700b142185c12003420801040111a41803181c50b010845a00c0710465070300034404c903007400308040451404038243d64000d4040f1401d04c0d42c064000c1110005c54100251641107821a0794 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 56904535 1250 56903285 56903303
    0x504110310120b060d0f0506040b010f050916050702060d050702010606030e0309010225120f14120708070204090510090b090f0c090402150f1801050c0c13021312 71
    0x7080440c1c0700700551401c2c5a01c08100d030000c0e1501c404106040c02101411200205c419994100041c8284003683c05244a000205142c2d410302504000d41c1075a904003902441c10181042114100d003600074000310518140789e5030f11502c9001284c203500c101005d0005a508160502c04d030301c2e43c1540000700700e0780107607000c21002c44085031054407407042c3c0740694016406240c0f81c51860381e14412919454001004410f000ca5403103030900c062101180c0203441002c66240b0a0060250346101048401000809491140d145031043c00035030040c0d44002e8900000441c0000c11911103501403900e05400c00211131100d400c0130542c0d0098601c0c50401c6900b216050041409280c0003e5800d84001d00e4002800d41500f00e5818890600c5e0024000c1e640180324406982d40000482c005107088516500b10b940e441070364586001e41c10f00007120090400904024140d002c0342c0100301000c98803011218416242c1e81d248441000c5e0050100600000d8586200028404002a054031110f40f04401003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 56905785 1250 56904535 56904539
    0x303010510030b03030d0c050910030e0114060a0b0703030f020408011a0f0303070605150402040b0a09050306010509060108042607050111040e130c0305060c0702091503250504110310 80
    0x480540d0035400300907030103034014001040040504e401020f102c0301d562a0032342c02c0c100c0c1e07000000c65100c084540d076030100b5503804540740080000e0041888203224054040900d003004808904819403601c50341c041c802001c6400800c16200c2d17007103c0c01c041d42500086d5180d0340ca4081e640d00038140030700c60105c1d1031f109204060351410030515400d5407800c0200034505058641d2150409040003c0003a131400240c03000b0700342c155032148042d101800d240284281c45507008031b4060b1a840c10f5801c00e0381319a025900412481d518400ca8070783c828001e28000a080d2280d29010224004000d04602c1e980c0e0b80703010355135032400a940038020190107000240484400721440c0c0c0201e108500601c1859229080003c00050507144041030b00c0e0f204610300c0480c945d5945400381000e81c240c1e8440d40000c00010b0420030741c6004420320303070410003020780640d00340480b0000940d6480030100000305800ba0352a1540a002c00d5031404c80148006081400624003002d540d00c110752007119041c032608504840 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 56907035 1250 56905785 56905787
    0x2010e03040914130510020c03070204060609030c0b070f060b0102010209041109210c010302211314010b0d03080a06030209010b030f25030b0d060e0c01020d02240c0c030c0303010510 80
    0x2581320581d070001d020300f510140e206265006944400c0c02c0355890b2008005820050702d0794420613005268580d5401801811480c084013081580d903c8400c8a444c107004450204040114070f10b0340c035500c0a00011900724220040c0c0c01b82c05040b2a2503805842c082c41011001c030904018444214101c402c01406211803000c0c1c0428580218401d015138440750020740f5650080e8010604051952003450b44c400c150554604103242c11201d44202c845074000c0e0303008100d6880502054221208000c2c00702d10010b4021500c1d960003d24080c0c100320350780c008525540f14545c0240013843d00604113108640e1103041041c400d50081d207107170042800c5807000814440316000d9040c030411071003601c1d0029100b502d80840142c10380c0c03009a5400110480301600181551281480c48950400a8504203a1707600c00641800403094050081d90032809420158951140010f2065200349440d4a000c2e1038403c010b120300d0080345a1440d25100006041c50346181c0003000e54107ca0045031546449455240 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 56908285 1250 56907035 56907061
    0x908031501120c270e0115180315090606051305090f1c0309030e0901080f07080106050d060509010204050612040b091c1b0203011b02070e0c040e040302010e03040914 73
    0x12030f241c00951400868115814500c8203034800d03d1001d4031001c070181d00d8040b500e01c42c02d000e034003c0150411040f6520140c94010044c1240c40840d00031030644585503840d509540d044001101c0a0166039250301c42c204011a030054000c4e00018040000000c0c10200d010700034801980c011100b482846d120304850311000030701d40502d08602601580194003541c00383e0141407030b0402241031008191800380c19484014405008201c100c004202240001c03034074504050082d003007404240d0421000748031030344604a20ba000035a20810015803540d81c0f454003402030107940c0000354001e00c000f07007000e482d91030f54034002e0140c2e01852070b50100b40c86089100e540c820b804850001102811209250410300842c0c4902d005442da0840c445070300d0b490340c00203086584070100d002c901c040a40100402590412260011303101c0c00000840c581031a002c0034809014510440b0708490000c800075080620039040030003800021070450b0345598589510101030002c400c030b444a0b01200c071000844040c0d81074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 56909535 1250 56908285 56908301
    0x703020f060304060b0907120c0e060f130302030d0305060a080102030105010c02060903010b091f05010801080a0204110f0c0616020a35041403010c02030a02060708040204090803150112 81
    0x40c04200015140c800303000d01a04010f006a900c2a03946404040c144c4800e4107003881131096039100f0382d41d0340900302c01c60115480800b02c4810000442040d2166440b80b00480c2c0040c0310081c00581c030303804101007843d40390100e500003d4050207229031100c0c600b601a00700703d001d107900300d035003031801d588a8904900301d01003441f515002035001501c20000d42007070402049034800103000440c6500d11700d400300307800f14410b0384e45c901c40d40c00f20410b8207050010307840d030b5202424003481c000340994540b072002030b618142100301034812640c44104c01c03421f100020841e05030f40c42c402c070080d485da01e0404032182c6801080700c40c848240c0d424208002020f01c003180e08111940c0c007556008085060080e05013500c905001c50802c41551848134a8009807010084e200804480c11014540c5000500349801e40310f14081e004150b60044c0502290140c001c1100c2e42c1c4100585000407081c2c0d43d900003d000381c115220083c0403d41d001091111003c0341d0100360022207000c1c0c8800444440040681084410103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 56910785 1250 56909535 56909539
    0x12110f07030f0f09052103070b04030e030a032003160f020405061518031f020c010e071505090a120303090203150903070206090402070c0f030b010501030c0e0405100b030126070302 79
    0x2109007402035107400d500750f07920f800d1b0b841113a443c91040450351078655445008141c494401100400c820558000d40381103800310103401800d2008030654000d0401c3d000b1013a0586003504d8902e104200110800503925000c00c240712417100f40d081410419000c601044080c0c0c01241414001617081c03c4c18984081000104904a89001d03030359005c3c00460030a0480c3c0e0741d4180290712010710b81008135008110b0080703103001d0042e60381c502c5042260071030700c0c40300e40030f05640c000b0700080188070b041c842c449280301d4040c1441595607855100240030220141c204100b0129032120302c40c2419415417020032038500c2a0122806842e0030910303456415011544092998000c00c0600014284000a0514860090720160415100c0d550f18107121459030400c0c80b0100c28428200140010040003d00410080c20204020a1280802010340030000d0440d40266161000b0582511040b00800028284202400d85950b103d0040000c41a400c42d58455400034402408007010000300b0500c0c03c490340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 56912035 1250 56910785 56910797
    0x80102040b1603022e0f050403080402060d060f0609030b1305030414031f090302061810090f0203010f02090109050303041d040215030403020d08071701030312110f07030f0f 76
    0x59a000007500b06040000c90460140b550482c070305000c04000a481c0d04581a05030344404c9000c40c09808a0329212140e0f502c1c2c604100610012039013052001350059016280581e0340c1c0d10f03902480024160983c0001201050018001003065100d03016500f580d200c4c1034410381c07075110315020804900d0008400380548d0420032042000b0000b090a10b1003210000e400c0e1844500960100c01030900307540325012125481b005504201641405010360004030540007150b2415052482540d83e900b45c03c400d1811541c603120001408a60100810389a9004000b40426070080108002a4010f90221808100846e5010665150110594081e43c1c20314201e29421a500d5015001e6074001500981e0403807414401e030700010360400001d510403406900203090810300d40b0001425802c1c018000c400b00002480c2c1118421105260181125010719086a08044540340b81006050a6240001c1a24002010032034100a00060314001e4000d465607100c00c480c82e84151030744260343c00c2c54400617178 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 56913285 1250 56912035 56912047
    0x80a1e090e070207090504080c0c09150d020a0306020c0703050c12030d020901051902030c060a060e0f1f06031a0103060305070b0a1202030106120e010209150705030c0105070f020601080102040b 85
    0x50036907210354041400e10440d51003681d00c00d5038108880c015541035840c9000010310071000030f0200506040400e05595110f61803a00d0103c035a0405004000380d032042c908059410305641d608041d40000e143c01c004115550242050140d40d1552144001c5400707000e81c10b118031030381c5458a548a004003015000d18038160084075000029130007950325034180481031100d4050100c1c02da1994850200359001540d45540940700ca130f281c81001440300c4203c03401c0c418140f01203505c0000182d009100c03071150000035141c10a4081600b01d00c8600070f000c4132a07a200001c3c807598580c00c403d44501b0304482d03100c0e420002100441c20341c0c4c03ea00001d0410748c0000c00c1009014104030007440080c0d1a4940b2050f040ca030f480038401664002c0c1c1c0f200000900750708207100744085034420192010308100003140707030440f00c0300450907811107042c034603940d620046195014411300340200d5201c1d0088000030846072910b414090510b030f80070414140148503440000c207118105108440c00d60303082d8a13103a81400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 56914535 1250 56913285 56913299
    0x20406050f15031e0103080301030b090304050f010c020f040203090309012d080919060b010201050901330f030302031b06040c0e090f071418040804030609020a0f03080a1e09 76
    0x3610103000210146245041d154582d00d03413800c014041d43c0302e9400301e84d417540765041c10001448003034042c03880b942042004010300d0b41d034410401396800c02820400c641c0e07130146c00010000030603101c2c1d1981140c000410440100c0c0048010204800c0036201d00740b401801e07014802d0450b4400110108483d500201c412429000e0b0603015403003511a411240c031414400e00107445143d580340304036006c40c1c8072415468590b8082c00740396400440c11000b042000d104c503580141c0042c0100d0b405005505042501d90748514401e2000041c010031a00006001c0e6241342c000d41d280c1c00312030700105180001a6445d0b00c0d040106103c0d005540000d01d00c064035080003c0d06407125809409030206110300038086109200a0014100a1400c0d00c0b25110581c000b1050120322083c54640c0e20204400c08104800903486a0558040c1c030307042034002038100740b24404a00e0b040810b800001940c900b0450000c00c0110b40e030014490302041d91381c1e880b600e01c014012291907030308000c090340100c2d42950090041c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 56915785 1250 56914535 56914537
    0x2010204171501051c050102071208130312050a20040f120803071409030d020105070e04060f0905070302041e0302130e031602060904060b0d050114010503181216020406050f15 77
    0x210080711000561000070346d88003030880e400740c0e00c00c0310382000340c1400c0190301e5048081143d00004107003024069451503500209100c2007481210719a943d110f0102c0c1c10002103910101801c1100c820707401944070040036001c41504030f441750009804c80c1407000300d55880003071201c507405980215407a0460701d80c420f003500c1055005031071244043d01440740700e6807640c1c200300c0c069070a580f130b400015080c10450740040503005032001d00d5000b075090030b80c10080c40120390040021a00701c03241c006025124007008030080d109a50100d259070000c0040072480c21486e44083c02204e108454440c08041052451000d440b88001d10101e241c001b4000c01c0307864a90f2030742c007819181c4000e040f10302d40003d0000090132204690090078009501040700f414840a034814503003d801040c2d2a20301b606a90340c0001c1c030390310000304110f111400b41c42000d00c580404100300070020020405481d01c80c207484440d64040d00d04104164070071410010005261306094000011210000c0c291402c0b500f810398500200d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 56917035 1250 56915785 56915809
    0x4080a03050d110712020607031104090e031e03160207051507060e0d0207050f04151206090501021206100e011d0d05070303030b0901080106080a121e0201020417150105 74
    0x4180c07500c4040c1c103410801401030542c18031654100e17201924105000345040d800034801000d16150511141e18010725805072000c49640420102c1c1c04904116254150700418007003c241c1c01850b080c0c02c54003c1d4100107580300c0e4081d44076078487c2403a5444101d984803958800c0d00d420104d01314051000000c82001800e01da40600c03008500e001400340100e01d4501810320003001608505000d0290f032503d50004580458210303028020780706140749541c41c0c2080c41c415401c003940340002c03001c10005035810107801c081d0418001c54844800780d50703000c1125000ca681c98414030131a190008900d009030701c1501031180c107039105000355140703c1c61843c03104828114198401c00595455001810401494000e1403281e540414240340c0c14040c005003120607040414564102002803080c0b080c0041c0c8949541e8205800100c52079075140c081d60600d0309440c2030080d8039002c500e000407076901500104110742506444182c642ca00b2004541c807a4458400e140b60b031605c030001000307a0710b414420a44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 56918285 1250 56917035 56917057
    0x6060a0509030a0c09050108101a012114010312030207110609040b270105100c02150d050403020607020f03122e060305040605010509010e060108040c050307030302010912030204080a0305 82
    0x42c2c00310b9483e940002c0c1c074139920a940313054a40c0018840d6100a2000e0745c00c13009030b0700341440f120f81864a0003810100c1603062030b04200c50300800301c0503110f81d04813180c05812080c50802010b5015405095100d900b40820358004010f0104504118403900c00c0b514080d07044074080841c0d03024041000815071010489135801070b2584141034041e51001340386821300c3c0c10585124805031442100b8603a00b0016400140704441e01c80781d5155079900704d03600074042941107440000d076424800201c7d8141c01740c0350501030381c54580b0080004050300069040c2c0200340c1e6400310744042c2d039102002d660f41c1c0b080d1464000c2406200380403d6180c5403001d410301d40b40e814455070341241d00c42c040030b07060f24085030341c440c0c1c00190b254000d100c144441441003e0152000380c0350303060300f581000e44004001c0005030095040144500009003403051380601603000d00300040c261010503984e41002030191441d04800d84000f0041c4121402c40c44c001e100300e404035203008014204041d0561401d44158002c400e01d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 56919535 1250 56918285 56918293
    0x213090201090b13050301060f030b01060c030903060507050319020a0c0201050c0304080118031d0f0f0312030108030703030e010e06071d030a0804090e010b0a1503020708070f021806060a050903 85
    0x4a2001280c1004d4404242500c840d488424035040406083d1516a408108038150118003440480da2592086041da80a403c101c00140054601210004920707440601203901c0e0805001c1d0740790b4000001c60241d08115113801010b070100040c0001ca12404040b04081180ca0000b100154000d5014245804070b00094a040c150317142c80960039039400c280f02545c5020401d07090810182c0116848030806800302c500101c0804070f002040125800d080c00c144502e14094850446560403c8000f501c4814101c90340e440b541d59a1055590307804c117000c11030100382004d81840381c00c80305120b0281c0e000a00d000402854880d0b90003a180c1c5000c2041003150034403a81c0691550392020843c0b0140c0500c1081d1503030781c0e0f501e0b1050301002c0f00e019844084003a41071005140082d99520210010344200810fa00c4450102000c164024070400000404440700491a4001c4c020030500e41800c15000380c074000c4440d10782a03060301000b04122600c590100c41407003d00f0406210b28080c249039035005d4212 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 56920785 1250 56919535 56919539
    0x10915031d07080703030807051c0506030a0204060e150f090105040b0109120807150b0a0b090315040803060301061203020d0f030612050105070201060602010207020f0603060418060f18021309020109 87
    0x201c2c1045403079040503001d42d00c488000c01c10154483c14a541c0f00040f450950b0501040c0e03001c00c2016440710303101c0ea040c961248041202560140300380c00e4201e900410401186a641400d012001000c40f0882c00480d421140e441040c1881000d00a01c08001001d050b10350b800d10003044020412661418100f00b181203000c18500301c0d810222540d1030140d0b000300c0e00c85101e8a080342e100608006078100c0c060914041070000d0f2140000502a1280302491507201e000400c08a450312001c200d45d0f08440d112082488140004580114091a016002803200c2c035110400043d143e0150080200181d02c1403212003205480b44203142020a2030340790105a2035503c2c6e04e4035088d04c2000d04240d465940da90300b40203403250240f040780c0c01030403607000039410a841030700010000044410f030f16024a500000081c0e050341c941d44825003a0540e154031025512180c20a90020002690703000d84681c9020000c0700d40c800403c9400b0b2a03a80c1c0148040d0080341c1c03400d2650050003000340124140f0200f8500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 56922035 1250 56920785 56920841
    0x6050406110f0414040608060708060301020c030a0905030c03010c0203040621020d050702150601050f1c0c20070311270c07031e0801030311120a0f02060601091503 72
    0x42034040c1c0b0b007802164031242400e054482e5000b9503026244291b203424000c009500d03000c200a0751000e05400c180483d0754540020a01901c12808001040d001c00941d42e00c00c02d400c55201010f07241d00b030b030480384140c0484003450b00b00c1d0008c040e04400342e4018441013100d030f841030340006d6503c6c5901c4200000501c1c4001001d06a81029441c98011901c4108020a00364100305074070601600e045140041d0900c0c0b80040d00c940302e030315808040402d000503951000c4145a603107080d542d105030000c00008588200080800d008a0425a15026010340014290b0700001c2c0780c1d0300766900104880741040c904400c20034110740d102b0104548260b441c1840f440100d008040e24400e59500b51260741c0c503406407800600b40d4440c900407040c8413001070440c40e0015031042009064941c141401c000e40c42800c2e030341c6860000c0c1c0300c4022a0071000003940101c1c03207501c100c1c903000c84101c907021644551039813030041d2020041809044491140c00358240d09061003900003082540403845100041010006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 56923285 1250 56922035 56922037
    0x6050106080f10030803010510050408060114030f1209040218040c09050a05030106031e030c080301081029010522091a01020613170405060c010615030b06070605040611 74
    0x442200441d8841c82046a01100714101540c003442c80094120490700750340d44d00d182c1d80018002c0600a03130304801d84041e454002c00440d0003800800045450541c0d50300748040b4068000503045000c3d0058000b000169000010705559141016111600705855041400002d4200360342550209035008402000781c1c5030b612900095401d1035545051032800e00d018010110390640c841c038000e038074000381003021807082c1c04000d030060383d10382c0c0c121300240c8142400c61f0075200b4110302428010002000040340240001c0a040d205685141801ba00f1048031510100102e25812169a000a00c24252240d80300d807004022080c0c03102074103510141600b00c81c0304a41101e8010049040d40c5e0302036800d803010f07544500c000141c2c00b440100110b2410001802504640d0000180580404201004817100241c00e80e0040c12010b8440344e180d524004140d4042c040c11f10444034022414001b103055030744640181c9055210241c103051070a880f03076440038010b020041c0140c0b601940ca191542e01d40b80300d20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 56924535 1250 56923285 56923289
    0x130206131e08011b270e0c0901020105070305060108310c090615050409021c020d0b1f09140d080417060a060509040204020d090204022a030f0301120c03060501 70
    0x2001803081c2030400181c00c40300021100400c41304810810f88606510524808130714500d001401092141c60074041d524190a42052420f044107a0420900c4c8240c0301c054298140240d00130710040c4c5a64034107070110384054494074001141080024420320440e0709a00f0ba58a90244540309051100c910410031000e074034049038007008002c07003000918514004e440261100004410310f01640e094003511a101d135101c0d2200103500818001041c060041c803000c9540c8100009644e0b604211042c0c5c801001300c40b141034450801400108c0305003160110741c02c4030601544a4140355400e0480f8408070140b000601e56000042002d403100150080010340000c01c0781c542c0361198051900d20320383c00d10100a00c01001d06180900800045d50791014590b0003070740550340107940f41c0c40f840d904405810300b840701a4005000152075012a0798401c3c04a41006911080c41c1c11003501d02c10260b202d2058121400380c0c0c11b8180018003000c01440311030125148a81042c07070000b0740e65038030201901c00907 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 56925785 1250 56924535 56924579
    0x150e03040302190f031b0801020a1707090605030a0f0605060c01150b070f060203060102010b190609090e0703032006070518060703020d0305070302071703060f03030313020613 77
    0x4501001181484900801c02c0810160000141030800c0384c6842061101d1102074040c1d101c0000ea1541601d030400340002070302c0081d000355921403280074090302010005690442911a0400061226211b80100003d607602665003900e5901c5280240c000342c409400c0c0d4070115030741c1d194001400d9441030002c04c41d44480100210b505c00c00801352440c590390590010445c8241000f600d40000c25a0400d82c0a4070313800040142c894540400407401080c2c56051107402005201780b84001c0c000c0c0c00242d40482d160b50755000c0c01c1da603c4510910035130715201642c0e08164000e14060001a028a40360080c1c04c0d00004000004030020104d20700d400d60990720351000c11030010703c901c2181312240041007038800c203a60b260310701b0b20b081c0e03802545c3d20b456240c00420140c0d103501062407030b8404d8040360340a54010042000000b1854040902988207072005440b8000080344c19843d0706021058a1040b0400510b01c00e4010480e024040d1a40c0070042c82c01d0780020b843c501007402c4810302c8103018500c2c12 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 56927035 1250 56925785 56925787
    0x10f090b16020f030405091801021b010e0102090603150402090d06150501050403150510120803091902090a0507020a150902090703270510020a02030706050604180f150e03 75
    0x700701190340140c00c100c19240210340104074a12900000001150201d90055464084640d95401e11a1030702c2a2016a601c00e0750001459941e03411842041140c10007151000300300000480117070a00b00c1c803480500c1030300400113000091024a0500c120041034202a0025141c044c40c0782c00190b2145402108440c1c440d912a40455803800d911000c0b00074003401c0c00c2c201e280c2400c44d120f00c205041c10783c1c04841a25102c43c001030084a4450074100203100c0703050b9200b1406411f1a08030402c0e00111100c8000d403152440c89a10842d12a000340501074001e0710000964488500304005808010201000d41c8100c6c400540010003d400000c01c0c036846c0240000d10035064410400d52081c0900040e04144c01c1000c02e03482c0501140e4008612028403900c06c0c0310b1100c03407130240c1c1400031805146d10308070310101c2c0c15003205030040020007107035114a40800c5a51380b07900c104030841d1315541c449232400b00d202000c40700080542d00b240213207c1c000d905542c89051004420300a90b460341b2100312245d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 56928285 1250 56927035 56927041
    0x9170a0507030c08060f0f0c09010903050f0a03080c07030504061d090103060b030c01030510091e06080c09070c050c10050705070b0a020c03013c0c0c0c050607020f060309010f090b 79
    0x4c040c4a15500140110b004600505280464102e0306801170720400c21306400250503800ea030b0054014000640d8045d046d504200c5010720001c2d01c4032411003040d00880c41a80c005854400d200b42180c26990381902c40f0341c10941044000c0b80d1020002c500c000045101c0c46040001d0307a2507252450086100f51404030b44c40360207200b03250410034480d5145050500389414803140c4000e012604040d5103102e040003e182c590b4084030300e01026005540301c50640f4102010502c030502003440804042c0565054240352101c000413540b640000b4030151481d005a802c2c10104d1a018010030200303121880d0280c148a1036440e080d040c03400d203078801c284c640300001c0c9842010740c051000d550510b4089000700110148012090a6504002d503100928196a0001061101d45540140114103081c40400c80b003922944042c069900b0440195410413003003200203001e29124040b210081d60141441c00300002d142c05116142d00040d280c03022554981d03288011480e214881c940407075004014400c0681 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 56929535 1250 56928285 56928299
    0xa02070801020d0911040911300a03030608190b0c0d020a02010c03060501050f16051f0506130c0230130e10060203180105091807030507050a09170a0507030c 69
    0x71943d074403170030f020f5030800c090030000c60703a4150100420441682c0301599040c4016514845d95805621080040880155252034540008803600f02c107110b52800c201e8030307858010300d990784c1e03200c03410340c1e89004050402540040c0e1803d032243d4000c400c42c0c1c4a2420710a00b40c003010300fa40c0003240030000503992028510b5a01c0e6260040340b00400b001e0902a00d440d01606d0322403501c1c400d11300303c03210014900c126503040003000c100809a8400141000c5441d40340c504c12040a81800c1c0c031002c0c862484080075210318089032140300380000d8681c00802289009070417007800c10a03107100394900e1480d0500743c0c1101e815060000d1480c031403030b0541c009840d4280f9101084652014156054005045505101464000084401108401c0c44001c0032981d084012a240e2250701c807032940050f80d859160300303203c03102005c20740240829202807220f513841071001c458030301848010a00003111100200841000f00800400484000b0300340d445040007074890324617184e1180e0089443d1918454200448 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 56930785 1250 56929535 56929553
    0xa18090b07090501020307030e0f0405040506010611030310030b040f050730020603061903020301020d0603020f0108070e13020d2c060403020604020111010209040906020d0c0206010305030a03020a02070801020d09 93
    0x460400d0a198900c20b04000001359a401000d80007014032030b2001039401a85c0d19512b115490203c0217209115038501403908039165242071142c0d00100300c5000744041d000c8c00c0070080d2440b03005c03481c0d86403901e1460b54448a546540141c0207980260020110102140041c0108009440322110401402416642145800d07141501e800c0e03e0307011061030000180d4aa4003181e4010741c0840d05594024541400b03441079444640c0b0096156200240a01c1360b02d10070381202c02168000c503562000310600c04010b4420b03c100310391081c00200380d0320b031081ca00d241821b01407420f41c0d503400707005003044d0298800004507113003010640480001c08036402e4001b0140300485441c58001801303041c050805c2d59002e0360314440588020304ac49111594810111406d5040c0d48a4000082003440421590b0504600a503c000c034401d1005040009050095000040a6040380e6102000394031300400c80c0301c214025009140e080701103000303848000a00c04400d0020703020302510f81600183c2d1101c580345c42d50304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 56932035 1250 56930785 56930791
    0x90c05031b031b012c040b1f0f030905011401050306010f0b0307030506131418031c0b0406051e03070914270709020403020a0806010e0a09020a18090b 66
    0x1c1c10142548002850b24046030311141003196052140380c0c2e504901c01038400e0f08924a0080841103104142e4660644152401c9220308054408101410083c0140003030314441d0301c036081644000604503003d492040203800500d000034540001c001c00140d40d0349095510350f845104965550070018002c07807806204441c0144000845450400e00c0e01d628840c41c0c1c00700801d09801d05640b800003e4940d10754080e41101c100c42c030001080300d0006a154404e50311020345003100c111007002004441c10000008130340202035800c0380d1062044507405540003416464040d03540084d164040010107440d80e00016521051880c0001c400e00041b00502d80b50103204d901c44c0001c2820160502c1542d0b1007419141c0e00500618016049031150220505044101078040300c01441031000000e0015060342c060400c3d42d20854100c90210703036401c11030303540700e000b03000e807031101d000c1c40e002b10b0310302d030204e0380310b405401e2001d130010701125655207a50400142c0c11101007121500c0714200c10030402111091a4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 56933285 1250 56932035 56932063
    0xb070b0a11030f01032015030907060e0f040b12010504080304060b0901030f0b090a0c06050d0b0301020c06011221030b010f2f01020c03040b091003020a140304080d090c0503 76
    0x41145000041d4585140f010303c40070345040100d01c101a1140300444410202d03004c06441860183c1121880090030303802110751104501a400002c207240c0d00c00c2403000e5038000010005090306400754104402811603a8a00344d0060740c02550b401108130030f0196600c107d01079080140c682c238042c1000070650340a22519403042c7d0481005100140b07403603a200b06100e4000d044d80b081c2d565a1100581b46c40c034400070151681d954950700051140c0d00c18020014100003002c244811820740c000d0500740c0c000c0c48070142c00307078005500500010b64281e40c031030901c6000c3c2da820b08070400c40d4002050107100304100c101c006501c81c00041070b03a503004a45424844800e1030309405c1d403003030507441d051401640c407104107811580c00e000000d680b0007501038540c0f00d00380c4006e90b9621592104a45040d42c410900180942580528070450a010b4400c5e10024601c0791a44045070680302c1d40985654070081c401c988a1409110030868005144641c01400b4846c88198081c00d06140415240105068140d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 56934535 1250 56933285 56933287
    0xa0501060f0e0f060a15020a020d14150108060705030403090b030c03010906080c03060711070e01140a0e0108060c07060905030a030e01061401020c060c01090503130603050601091401080406060b070b0a11 89
    0x13002c16145c00b2041c0341120071141c0e0707032281c48580200403810300102010281d8030482000454091040344400103005c01510700807511020320384519069015024030404005030002c10005075218000d0005550061103441c123811101c3d11900782c2003440e0816209840003040100061194203400c0c8180030141101c54010400c440b4010002035444000525000c02c0100c1000c07680d510001c20400c007400f604001e4410044c540e190807030500c0c900703008484644900418807000074480b0444d1a030307074103940100b80540160f60740e9007803504207603000e40b900301c2d00d8585d01c0c400400070030414405010300500035034004c916103a0700360b43c0c14207440560704400c510103615100c0c1403190f03800048079400482d00350bc001c0d0b00e400382c1e0711803070717006164840e00500305000c001003480100d56200c60300b01c290780a0703840412083c0c503060011540c0b8142e07401800b1400400500400040d030107000041c0d8064800c10003c0740080c1c466400c818035030003044040310b42c18140710502c0f8180d0341c540510210503c81d58a01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 56935785 1250 56934535 56934541
    0x11040510090e011d01050d08270d0311120307090311010203070606090509010e010b01050901030b040e01060303050304060c080c07021e040606031d0a020d02090c07080304120e0f09070e01020a0501060f0e0f 90
    0x1310000e0320403002c1000d0302751044100c1601090a0000c030204e80013000b40800100981414040c0c50009500b4004503180100382004000c201c5903001c0c0c90103400560f4500c1403d134190303a1409410954040a54103510051045200084150183d1406882031080128a50410404003401d4a804007109822641800a8024245d9103d02a5140c4000c246800b02d04600c1d10f402080090054000814107542820070100500d0340000083d80542d00c43d12082013000e504d00301c101d5106009440e80301002c442040700e0710261070601041081c030034210b03080390080103010000400304c8056601c640c0210391912900c0709802001e0b0320601c030b0304951401500c04000250300040205400303900c003e204605142c0840c406032800d509640100b540103004507540d061905103140c240b041110745000051a80c81d00078003d09250b81030002040d00a004c4600c82d8841400c10748046c0b00200189045220703010070342011880034012000100500b40c0598000d5052084486541000030310748600042c044080c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 56937035 1250 56935785 56935793
    0xc0109060f0309060e01180c0f030201050a0509011e090f090509030403060e0a060c09090b040221090a02090a06030302010e0303010b04031101170405060109060911040510090e011d01050d 82
    0x41400000140d10b00018900d0b0a0325200d4014006048031460b150b1801c040e10700540081e013812070085014803801d42146503540001c202000d458000240050802d000b0400c0d0103000f1401303004100740504100401194107501c019100800e071030035000180708048204004001c017080c0320041c1145204c281314bd481c041120b15546e1190744801012103a40e0801855010380600c030700e8030007a070f0000c02841206404030300200544104c0c09130b40b0b000c46c86c0c00c1c1d030414580703031a100319070300f416145040300c03140100341005e2008102e00901702442401425422401a034650040c3c0d440381c055000009070380703403c50034024212140f82401941550003000107225014851341900c044980c013070043c000b134150300f00048031821601c2103042d003005410703010700c42000f0000c40c040d8140c032154081003155954501c04842038039440c81d0704103858070b020001400181089003415010403d40e0801c440038a0f945c0c0380004000c5800d030f0144c00c0d09e200c40380c0150200c110202e5528010101101d201c0c000b00c036607841e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 56938285 1250 56937035 56937047
    0x10051c1821020a1a0711120301060e0405011508060301020d11031504150314100203070201021b07060507080c12030403020f010b030d0503010902090103090510060812030411011416140c010906 84
    0x410009031345100002d41c00301e21440b040b2018444440540d00080700107106000960028020740c0041203030586040c01e607080620607141251a4400030510160040c1005ea61250024006a4255400300100382c90349060340a440380d1490135100850f501e141c0301c05030318040441d0061241c0b003a400c2c01043c00c001d010b803490b01000e036a085003c0c0300303500081c0e4900f1071806544000310b00b0240d00120030019680d4041d40902007a0748070015407040790711010390103130b01e030017590080e00080b602c1400031320702284814010705810b011610031216010f211000d41c0c042c9400071901240141d000c05110600d604081c0a0701c45101001d81c01032450386050038019080b40014050712079019400b0038074041c2680b081d00840c0819802a0944020743d0700200c01d035016100303900403294184205c42c00400c0310150501140c0c4a2608060074607a107000743d00c01180c03d12600354182441180c03c1c4002544500078107000540e29100c1e404000b1001c0d03c8a03c5c450400d000821064103010980300c00b0004203400c20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 56939535 1250 56938285 56938313
    0x908060702060c030702030702030106030b010303080a06051309020303040e012402070302010804030305090c0a0602011d0307022803060615080f040f020f1201050a05070e10051c1821020a 82
    0x2480f40d0740c072581d40c01c000b00d01e58003814034083c0d8550700703041000040c00309404145040e00e01995074001c540e903c407403209080c3d880911841e40c0096010525180c05102ea9100d044c0e064401400e40b850a41c1c3c3d02203900442c142a0050702c0001092000c400d44101e11010514410700d0900141280b940b0315000600301800081004d8103140d01c800005000440a10500411080081c43d842e01983c41d44c4009008200f0112940206618198901c034552000410386e04082e6004244203806c02099800351b0001c0d03503c4960035041c5103000c0011001811601900300540f00c505441442c8c4002000001c0605a01520a070b202d111800c1c10700c8046015409170307080d21501503d14448806585000c202001000c844056440d4a0501030252075140c1d41c001d5070260a0641e01e20102c00100c0d800c001d01d400c242c4440c08040f070000c0104000490300707840501d80310410104002642403036200c00441070b100d8007a0498020340c10102c81302d82c1c41d28015040300303940903031310003040604d03500e943e0b00d00114559 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 56940785 1250 56939535 56939551
    0xb01020c01090e0c030c0408010203181608031c060b07050c090f060d02120319031a0a05010203030a0b0d0204021204020306010e060a090f02090406060207060e1801090207060b06040f0501090806070206 88
    0x103403d451b03c1d4001c0703038010300c0c0e020002c5650b441c02001c01401c80380308401d4a0118010561407106e05202d4140000648160001039071504007084a2806020300000c01c520300951111030007d4989400c2014156550086014242581d081000c211815000500e2503080544e8038040c042c25450700c1160310103295050354801c106c0c148140c1c00700d195001d56021092581800004040001e0f407642044948540d4001140c00380c404c0b5500f009210070f2107000301d0340180d106200058201d481da1700016010b00014010340d0302c0e40501d40208043ea0304c032552031284000720100340f008604040010310b004000d40f549a00307880c20300d0000501aa00d46105682c41191655040440e940003a4101c5140e244014420000d5541e100d80180d240d112900c10000800c00f1260101c105090002e80510755034078030040d0300510780c28004500b0003500b28040036030b000d80e5542c11080507512440020310280021142c81201c80346460001003410316250031030781c915080344040c0656241c0000e900d541000c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 56942035 1250 56940785 56940787
    0x20071a0702030c04020a0314010506070b0c03071704060207050607020c0a0b0a03020f03090c1c050a0605071704140706050403020a060c02150a0c03030b030610050907110609010b01020c01090e0c 85
    0x103500001c0d00d06807400811a900910000e2501059601030b403110320b440031400450400f60f03136581c0c100070541c0900e400141c00c10400740001524036142c10010f60784a981030604040f9400107044c00841c05800301c90456020303600040303090502c40c0820203294010700502c001c00c101e01401c0c000c9010f2a0302881b5218130801c01261403006503000360140c50814096414290303c0c3d127041c518507a590092088102d026156030f09100141030040480c99551a40200041600c405595030b0440240002000b0134200103841c8098107100700c42c1d1110a000d00d0040c080c0d100c2c80240f942010f814030240d64404818014101700400058489010002c100e400e40d0401d40324503200b0380082500300252a1020306101c1000481540e40780e0004c0a4060050181d642000440440f20903d584c0d03040684038060b503c224a81c003040310f444c00e91185c91384005c051801409100744409a03030326285084d50324a10a03519090030344200c0d60304101c545c103c1b1109183c0500321a16013020030908040c00b800368048000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 56943285 1250 56942035 56942047
    0x50612120c1f0b040b03160308090103020c060a0605030c01020d1706040204050a03081201051c060902041b030b0906031c03050a021e0d0b04060807060c2120071a 71
    0x15052100307840c40510140c1c103507801c0140c156032400600f408002a0722651402124607000c0c2800541d00500603d444a00035885003580c9030859190080107010307040680802854032886030520699004d5840340d0070114001e41880308050406500d01a154110742c050440309141590001e90f2142041e01a180c1d001e0984410000c50081d02c11500301540004505038001b041044035402441c2d0300e01d00500c001e0725641c0724003c000c4481c90250100c51070011500c000400308007540c2c0844100e41c40204001000044643c2c0010412000c1e140c0601095680c4181da2550410300401540010b04501130100d4a400d06080b00341c241c4210850010036945200094043c3c82950495814603400c82030800d20b98107940101c000c07640184048100d05041000d06001403d00d405010240c44000d000340c5807850910008a4a503400200c013600d138110039a8220580002103590614903109603501c000c004003034141031000c043c90525000300c0c2c3c0e074081141000340b100701e0308203036041c030841e028641e42d241 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 56944535 1250 56943285 56943307
    0x6020d050f07060b180a0f0605011202030703060e010b070203100b030a031d030106180e01060302030304050402070c0e07020601150c03020715030219020102090406060c0b010306020306120f1005061212 88
    0x481104d0040e086800000b0511500148100484c17080758203038001c0c00541480d080c5842a14210b03c2414003140d01203031044c4c0d880317110340c010b50390104041c500002c0007607640800888455081e4415440100c00290705000e60509110400c0510300e0880240034a00a030400b190f40c58516100c00740030800764a42c8020072800d4041241080c1400400074011140c03a02c2d0009916000318a40300616813a102061801301818018070003140e800401a40c28103140c007040c03002951140d00202e0b0101d452580100d0b8180f903030b0410501409042d4000c14080d17060980c0c02550500160000d01070180c0f42c604800000c0d1b0000c1c4003815140e103e9a0f503035885001d41415006030140b41041c1c0f00110101c116020800d905601500124408460034002c496030f41c5800d98080111000180500104100500210b6003540085030080f0014110842c0c50701c41c03c0240741010004110149103820507118580040041e0144640041d82160010091800011030035980c00140d50202450138011803c640f01d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 56945785 1250 56944535 56944541
    0x11106042d050d0201050a0e0f070b0306060417060610050708030c090d12080708011505090f0102070806070909060f0608040303050921190503070804032102070f050706020d050f0706 80
    0x2080c1c0c000116141c10105040c081d006c0d10701107802403400c900d00b0b0503400802030001440340c0100d800e000a8500d8a04000f140e41c80780e40010300040d001102000002400c41d0217440c42410801d040002e0030090900c0c0d000c000c1c440606812043c1081800e0240d4030100719250b007104d401014401c1504c8e17850005070041980c0c0c103100940504002030330104100da45401010041c0714070243e9550504682e00d0315204d881050711000841c00090081c410100a41081c2000341012101401100e001c195510b1145142c20700440350380000a1102004204c014054051600500360403500c0e5481c59080c501d000340411001000641007648032400b113403520341f080c070010803424420190b00d0120408010801226403007580300c28001d400c1c03418000b081510035406c0d00c1c02154180d03039000d0141c0355074a044401121010b404c11021000f05110310380740c40d861009029031413140040407144881801c2040c1010442e40c001d00a40d0815a00c0c400d03007941c40022a6502d00c101c108060710b0341410704001c002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 56947035 1250 56945785 56945873
    0x4090c031107050a020306221709060703090603110a0507030e0118060e01080f010317030406020c03040e040614011401050c0a05071d090a02061204030219030e01110604 74
    0x2034400142d0704081c00301c0401d0324140780f4029400c03114913890b40b01580d2040307a0744140c6401d940280081000018a4512420902400030b2a071541800c0020000175126032000600700e021603003410040088035003500400850100125580c3d0074118400c0300905288682900101084606802402103030700030310f40c44004a43c0d10495500036500c5080140952080c81505804070302e488000620020704001003e05807640100043d6002003122071001d044c1d003001d88200c511503000c1c800c1c010310480c20000b48c0001d02c00b01a00d52a80d08090074824125480743e0400e102d48070701880180007969a60311046038025003841d09507680d81d0140034060800203a0640104640a020300c0095142c0454048000f500c8600d040110f154865215260b5100b246400013500a139081c403c1c0382c5042c00714140594003034043d0055a280074860b200406c00d420600c8402c41c00300d40d007100c1e200d5241d40d011030700b0481003541500030001400d1a40300c0c0d2040f84454054500b5410f920310440145401e00810080e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 56948285 1250 56947035 56947061
    0x8070e0103230603010f09170304031202070501090c05040e0616050c01150e0c0309100c0908190303050901140c090a0503030d020309010b060405100f11190b0108070b04090c03 77
    0x14203104004294041a4140d0f480c44c440c0d800c01d4140041030265102d2540c00c1da41c402140ba0241d035455681e9415900010025414003031941281501c04402c1e00040060a209100005080040b4030b0b11003200c1c0030300d400c00780c0254034000c1341c0003040c0400120542c110b00032008040b01100385020444241c859000241d0306942081c19203914442d160160005403400b54910090599401c0102c80c0036004c01c0342d60039441e52201c02840b401e2400f5500c100a01d9001e80741002c0c80781d48940c580c62820481c440c200c0042c0c600404a9024503600d80309007a00500404003c3c4540c00398600480030307642029003103004030440018287d81580d1440e01000044c40c7c01ba058076241c0300024110f4001303406c201c400050550070100000e44a01c0e20f13800300c0f001d0b030740020642d45088164900131070320381241d040d000c4180200008080e104042c02c0041d85451040341602c501d4040d51803801841b00d180c180d00410042d0301045040c001311503070324251410785a450f03000185020302850110090300c8940e200c10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 56949535 1250 56948285 56948321
    0x1a06030309030d02100b04020a0c0b070c02040507120c080106090509060d12050c0708031306030513050615010909050f0f0903120408041d011406070501021903150806010608070e0103 80
    0x8403c5401040900b01c40d00c0040d02001060141ba00b800140d01c110070720000000e400c014010005406111b60640240c42c038500007600100980c042011503805440c076801099110020464036a2a800342d042c40140d40d29040b41c543d450500040c2c00c2c50580e00480744600100c100064440c0c440d8440041a139400c40d11a0110364180c5a0207040342e03001c81007050290040090100700c00c04004100c5024070b42900e09000c01c0c601c0c1172011401490060400c41c0078079803281a00c40464402c001c80d90241d000e507421a14a8803042001505101403070740300d01c0d007150500341000f881209249006500c50b9000c09000200d55914040f581944550304d1070a030040d5102d000d002c03d00800130082d006550303104111501c40890030142d8100c0d00030074403450643d050520b030010320500303005002d000306030b200d40001740c2064200a10003e61400d40e0001c00006a5581c414801c80004e00c4016401068032101403c01c9504148c0700408a0600508000c10700034861420001648030303901003001c02115050360 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 56950785 1250 56949535 56949553
    0x307140303070b071709070b04051e040f0f0e070e070c030215040b0402120105091c12020d090b073b0d0c08060105010525060902090a090c09091a0603030903 69
    0x34200c0841310640c10174011903000060fa420714002040c0098840c00c0f08070a050a181c04200700403002070300f02c2424045c0d0143c0e0b2141c00d944036070195030b4864002c00360115440e201e030003866040b0f0b01c1031400e002d040d51000c94200125800d950800350072804038a043c42003000c5608041c0d00c2d0402c49202241d4603904c05c42044140180f50044030b000714822100003144020007040c0909a400560382d40e02150400d0f40d08400a8050181c20028071b00c0074100b10619a440c11140412a0800061140101d0719400e03114100240d017424583d115501d400c0c0103255804080c0c071241c110441d00d844000c820b0420045500098402284100f5040d0092501180b5903031442c02d0240d412640c80303003508034030a2500115166000e181542c0d84cd90781d406614851f81030b107034182145c015403241c007501c445654489200140c2c807040f05861090300b1102d07000c204202107141ca01c00c0200a41d010411041c58840d048002944030203210032103100360f81e607150b810380328100001d0071440b8844580703602d8481c00c440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 56952035 1250 56950785 56950787
    0x90b0a02070501140705061609080d080406060605030f0f0c09060c0a030f03050601020316080405090103050d020c0406051807090503100906050606030112080a1e091e03020307140303070b07 83
    0x107401d050391001c2c3d13110100512010600ca84d40e001c0c10100070807a400c11000101c0001100c000000030454a00c0e0070304001d60f0b41c170642c60078420740698020000b8900400c00040c40064010240103200318a025813030b40c84d05028400c41d0b0040a40016004a400d0010407540410381c802d892546000502280d82c480301e03000c080744d171002c0e4640100e01081e0800011400750b4081d125051003104107130003661504191240304580c0801c85a030031100b1900502c070114a688036041e400d03018610590003841d0340b0145150203894810143c4502d40328504050040c8500d45038400c2046000d01542260b5006458243d0141c0f0695040e07007000f80c15104000c05010820340d1900a110200d001c0d00c403c1089454030001e00596100901070341c1c43c40380070703112501d00081001c2f0007004001e400f1315010766001e0010700c100c540720351490105c10020389a00d105000303058124054851528114003401111407840c1e010030340361300b440d205100d640000d4840120046d10140100d4041d0b0754040080910b42c0b42c6900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 56953285 1250 56952035 56952043
    0x2062202060406050d1a1509030a0c060503010302030f010501060e040c02190c091104030f0b04020a030812071b21031d03030121030e040b0a030827010513090c090b0a02 74
    0xd01c000b172810911440780401104420300b5401070040d1a0782041c2d0403130511402954051040c0640500c16095580c001c541c600100501a1441e56070341c035030365407441c0105407a000d000a070141059152400401115400c6a21081ca00c1401d40303012070321044541090f403c2c00381c03142c003241a240840c501c42c402c10018503003000c1a40c9041508100d000d0118650305c00034012800700070000c03510903848001041d4030050560b1b0080c4010080d1310840d44954503241282c22040b615180d0030000d40502951a40003400b0400b0706110034200000656280c5400400220304001030010f0030040c4900d410b0340d442a041020ba00051810b50000790490843c21544e07940709100b00e8401e0b0840360500300c01140d82036041003072190155500d0f5030750700049080200904604600b03961020048100000240404c000f6280c064024180141031a81301c92003804107090360210300d41084810056150f00042a00254054942c0d015002070b000801040595580c000c50300202c1c070002010620300e520582c001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 56954535 1250 56953285 56953297
    0x50312010f08010902060306040e0309061803010501050418020112020f13050301050a050c0d0c050909190501081603031206030204060e100515191806030b030c0904030206220206040605 81
    0x1010118640c2c1c5003021030880d0301ca03880007980610100b002c21900e01c1d103a0805140d01406109903031130b1011103800540e003540700d01481c0c0c40070000f82c01076041c0c0d40b40c28480e003801420b041c0d07028000390a0082d00890f0341c0740142c10082c180028044003202c2d1048941c1a00c54589000b40d03074035503403440810b40c00c03420101881041d21075824a00060300081c02030250030f0044482c001010304110844110f078010300188200326082000070702280380d0559a0a46a60145800710b00340e9803000003020036001075490582196585910211108101c0300c041000b6004030b0380c061410780f0824109121090141509500295005080103008280e24a400c20340324000c900003180300e4032240d40e440502c8a0300b4100e15900d21000d00500040d10212441c4c003190910740c885280019565000d03c160034080c101170b8001c003001aa40392040807081c2401c0181048040f4121400302c007515155800940d20200100f103000b21660400300d06110622003d1920200e6900400607625252110ba008085070026 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 56955785 1250 56954535 56954549
    0xe1e07030f0b120709110a020303042301021803010c02010c0807050a0e150a12060506040e060f04060308091206041104111306050a08010b07152003040602041a1314040905031201 78
    0x195007101c1044109003241c86000048d00a182140e44039200c6094403c001211550200c508040c2c0c00c280031000c0c801001c1040c19000e007281c50410316014503003103c038080d03a560250f83c9080076143d1400e4000d8850b5a201c5040d2170010364800c5803c000b100e4041101140355000003240310001d00b2011b91601811814555580e900000c1143c104400240c07802c9104180e0081d10411060260300c00002c0c1d12503003d003010386140025202c041c0494201c0b0003592090701c01560100e1205603c1c600180b000c848041020000d0519040a850f1802c07041804808140700d203940c1d04c0042c0326500079805540004500444010015960f42c4001c0d0441d4046400c40d00011a002c002180a000701403d692485820220420607103111205000c000c000c05401100b800e41201008511040718000443c0710f1071090101507140c07494003030845d50003200c4000d03c03612480144140d418001140c0d04040c11540d840d4001c030b0f428a0b031040850000c11803510050518080000c03d0740c252106544498100c442c1c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 56957035 1250 56955785 56955791
    0x10b06070b1501180303030c0e100f0e0a03202404060f0f051b030c01060b042117031b1908090d02070923040c0e1e07030f0b120709 58
    0xc0000440e1901d035983c00c004130381000540c050021a2080c4c0c0040610540c030308040203a80c0002d40080d002d820480810000100d4001720155104c2d0308c8010403030b2078003050b104000c02c54151f90320082c480e12000d14010540c00f0480c0e2303d419990716640030000c41c01569401400200951112540030b610500409010500c4000034000040c030500d020302e0014030558130030741841980c01001510303801d804100135943c07000b40300c000c604610a1103000c00821043c010380360380b03a00d0001030200d186c1c0500c00c0001da2a882c0325001c00440d449081300420304942c08071465403651041d8a51496038084400e0180c10361003c00c0083c88010001c0101c121418507480d040c010b0343c1c6143d40c0303e6480e00141026801030f04042070801140d41d850b0020700c118030031605944000107280c900a40c820b80116015100000000d208022000d00b86503082d400000e034200342000d0b41000d034246e64802902926071800c0581e100144c5440790030940c40194001c000404400002d1300041840703503109014081da82203107103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 56958285 1250 56957035 56957071
    0x6020c0a081210060212090103020703020f03160c14030a0f050312100302030c0405160f0203040801020304032d050f180307030c14030604170c10020a0507110105030403020c060309010b06070b 84
    0xc00059262802d01c01440a04e180050707da0044019402c990300490951080100400008409001800075520701540c3d680c4601b03980d0034000d20440d00c9a000038500c0100d00e41d440e0090310003013a00030b62503800c1600164206a84d1170720310f03d903200e480150420a56007030280503d600e011402d03801164000c9003111901d0500004002c1200c0003a601410b915080e0017034003441d90301a880d040303071040c007a0040e01d0a0642d0f07820f105007a41c0c4100c030218005050b0562400c5c4109400300c44241d182d10000221510414510700640315210ba07903481c6148140c0401ca0916000c120411b4101101000c1d080e41c031182ea4070b04e0506080040c9008a0102c44420400b019440c1000a03c00b84907941085801c0c66019105007484d600340e0081c0c0824520b03020300c070090707800105140010a17030f107003095494907511403140c20001919250003100c1410010100140004681c0c000342110f004d071070031140b4550f0703900c1f04d030000c6006000c00800c1c1ca0300148045001014040890101c52003100700c1415042e8880c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 56959535 1250 56958285 56958287
    0x13207020907030b010e0f03070812040801050709080304090f0603050d080a050c090d022707020f0c010f0e0f0a1a07061d06220b01180e01060602030706020c0a08121006 74
    0x6440504c000740080c141c0f040c0c0fa4560319003541c3c40c00b840403010f003d8400a03a00c03008a641800942254100c01c10b4000404114940c0e00b40720f041c2c2d02c80b6103454091b00300c6050240080c0c80303204600c20300b410541c45000f040700c541c1d11948000005e41c0d0080c100c4e4905080c44070060f110310003c95159142925050004521500201c1142c0c0e0007140240040f2140c1515030030004911130007034200840103c00c4141c07001c80140c0040b9203028001030707001020600c4d08038201c5440d01c0300152201d41082520f03408076081d0785c0c01580341d51650900307d40010b10025298003088103c1000e52041c1c0b020b40700c104100945903404401004902c3c0244410b01440b40d021503011030080101c0c00c0000e042d8031082c00600a640755003980070140c00c60031044040c000c0c1607103802541c000c0c280c200e2045240548c0040c0b160300306d10f1150034540d8072000000d0100c5c40c500080603440e4050060b020300020f0b0005902c04d0340175014044c3c02c20f030540c00f00c031040e01d61000d03080c0a040d151045480c0ca160100b8210085051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 56960785 1250 56959535 56959541
    0x1202010b090112080c012007060c050a08042a06030f11071113110d060603050601020127030c0c0e0402011701080601030f05030d090503030a0b0f0f01320702090703 72
    0xf0b12406078041e601d2242079034a00340c01e948034040c5980d40303543e03c84c6004590440e83c00071080c450540740d03c454a90007241019011070b403030b0401010a202040001c40c5e10190442c10441e80a41c000100390317000c010b01910a200046c1100c1f24032660404150302080c03494242d4050501140380c48800c02100c100d00e000642d003489141d0015151000c411269107851804a0801882d89080300001c100c0e501000d05a901ca504001170340f031412a12280300380491641440fa0399403259091000f44100c0c0c1c19203082801e10f501100360382c004110340d90185020326000700980504e80303600140d048205542c418000d8842841500c00f03c7c001039080071094030980380c01c44014140d420140242c52141d18541d1034880c0d5400004c8100c4043c081400442d0711a422881816910303409440a181e80c0d1808143c0c074411105161240361250000e88401400d0303441d50318000718181003e003040d55078801480940300388012021030940d002c0030004511110b1810f604007a140e80340c420341e804885c0d621602e40542c16 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 56962035 1250 56960785 56960789
    0x8010302030a060519021305090f0f070f050c24070504081005190504030903020111010e0312071107030f0302120301050306040609060204120c03020a090c020a080304050c0d1202010b0901 82
    0x1041e800842c100d8081075196125a41002100e8901508030f010750011034140c1c0c0015480e00944000c5a500b0046820000c0c2d08a500c01c0842d0101c400c903241c081c0c440c0300c44c240080e10180070810520b1606403854011011120302c82e042c1c0301190208541c14228010a40008194903601c10101c130100d40d0304c0f030180040c0c81c00d4900510150842d407244c030000702c0040c1001002c940710001c1140c0c072400c0030a102d1046500860185e40c44069030340c25030001502c50444000800201ea150081c10a0f0840340401a144008186c08031901c280d2a5840c0842e15145204c05100f614007540d04000200505034001450f035520a400799404104405c0c40d480c882d010900c14190150401c070300080c001001c40d0b20070307501584a50070040c205511010000400300c03080004981c44d81d0506414000d524108260070020300841105120f10303204000025210040004004c010410100124040007024030845181840c007030441c4101108c0c42c1802081c00b004170300e131900994a800603143ca03e050200c11281 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 56963285 1250 56962035 56962039
    0x405040614011e020715050310060207180911030708030301180506010c031809020301080c030714010903020909010b060307050a030f09020102031c0b030a0609170405090a0c030f0509030301140108010302 89
    0x41c0f400e14078110712600858410a181c1180a03410700030880312040700c0c003604109000d50750300d0b4680c9080082e000310000136400c00c230190341c0546400c000c040402c2e0115001c88208140c08070f5100303039915040d11112048004aa414040d04402149107200000910f04913116070031107070100c00300c0e10202800c58509032100342c0052205601100424080d1088038420840340001d8104180c2d205004001c0382c0080c0c0000040d50040700d600c400600d0300b00520b002500c070b86070344144101607000028109104074400280185200c900103200b0708029030049061040203403907582e4914017804001d215a00006112010a2402040b951503c00c40d10800000301d0341a0021480d01c0c07408a14604160044260542d241e030b25984d0803045510240003014503948141c1c004078104005103000c841c0703550382030641094041c0510080200741d44881565800000c8400002900512208110054403402d8000c1030070342d09207018028810000001141201c921003242d50300c481e000f100445140e1030078800a5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 56964535 1250 56963285 56963297
    0x1103040f02030307021305010501020706020723010203041a04031a1b1b15060102060c03070f030906021908040c0504090b06040209010c0506070203070302120a3e03040504061401 78
    0x2000105100c58400c80da0340000e04072030074041140c0c00540803422066100002e207854000402980d60100850300181007903001400b0b4aa0500b19a4040d13401d060181e02200c136602400303079001e64001c2c03044601038050300455406c2149000f003a45500d0b409803008841c800401c000100c1081c4076550400d01410584040c4800e02100314403200160b0800190004201510480701c140580d041103018000c1c515541a080585843c00019003403840040c0707803c2801504204200c24258400172600604255003000103050070744e41040030007170003000b84685103040866080c40c5050340120301d031445030340319041e0300e140c181c0c5031000e01040c0c40109800414400300c00b03010a42c64517294014044442041c9000b01092220703480c0d4600d01101924aa4056040090044185903040c000305e6402c0360603005048c9003d002000c0140b1202d40d1031515451340440d04107056135500d00b4048160310401140107449400301c0c0c0400e0984a610a01c00c851103203280000c0050190701100c11800e010308161281 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 56965785 1250 56964535 56964541
    0x10061d010c0303020d060314010e03091005030702072112050c030d0e12030f07020610050108010512010b040e071805010f030f1103010f020c0d090b0d02090d0c060c151103 75
    0x540703400018070001c40c280f50f02071182c111010302601c40c0d20f00540c090400e10f951404040c000908660021444da0031030341003006031405940f120410480700034103929055541782d81f900300490420714103800440440303070040440610190700119154905000c3c45074016204115842514144a80749000d8070070340003803205100c0300b826640000050300940d400c0e140941080c4001d0405948101e480b01c1030042000180506950b04100c0c1e56031141c1031113283d100301400e00c4000380030b02c47e0502c2100d1080c00c04000b908046042904956003000e0080c0040c0b00c01e404081c865074441c0800c0c0a41c03400c91010402074444100e280c001d46040302da06104409840381107031120119400800001d45992658038115280d5460912429070040304101006031500b691840399800e00002d07807031510412001401c240000144c001c1250f121510500005035659503031400701e80c062040b000c0c080c21304101c4c400c0001e030786600f1130140c0121038400c00303140c00318907a1144440b04440c044202002294414400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 56967035 1250 56965785 56965787
    0x7080109090204020f040e18071206020f12090309130605060904091703070c0c060309020f010503070905150a09080708070b03040c0320030616080f06010c0b0c0310061d01 75
    0x25041c0d4a0010740050300d8202c811894003c01d51080d4040001d0700c545008015003038a410001050849100c00a4081985480c0106100d48140140070f4011a070000d00d542d1300d0071010088070385c0b001c940860001503140c580e005545a40081228a0103804e00c041704810401c042e110704815150001c124030b040c042c0c0c41040c80001c0110702800c403041555002014014110400514800c900ca5034407000441d120b494405011041680881e0a0600b8814040e0059469020300140c0c06000e103460b82c2c50f6a40d641048521804c4c0e5800b031500002881100740d0303002c841c600101074402c200c2d01c80b100019554403429a4511562050645581019a00f0f00c541e5640000841c0c010340200302c08507020703880c1d4644c070068005004960002c00070400c10194141010b204c0741b540078000c80c0e0010694110b13204050040d40e001083c042c541c0c0c401d00c0000b03c40e40e000741c008000041e0001103440c401d10b8410304d81c10043d481510164080c17503030380e200018640c0c8a421526110081404030030114034070340d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 56968285 1250 56967035 56967041
    0x901031b0e1306061203120902190603020d140c0a03020a02030f0d0c090b03060d060b060712090f080303040201090608070c150b150f030105210106030308060f0907080109 75
    0x280e410400d180c00381000076101c5903030700a5030141001c25242040c00d91646070120450305560305c40d9000c1048441ca00300801c1c1c011502e80917540608078003055400c8240b00160302c140a2200c4503005000c02c1c0c0010070020f80c194047c01e55084103901c00c0050108901c03c660540808940c40d1307158500801604100030b20a07000343c0401c80c2d031801124103081c400c28901d001a00428000f00180342e8a28240c00318541c80303c40c48002b0402007280c02e02d1802c04401240440c83d409d0009007032180c030b8401c1d001c0035480d0101110112a008083d01c1a590790300103000380701c50080d22031985840c40840002c01c0d0b058021007221300840e4140c6520000510706001070b6000300008025005010802c40031002065032010148195107880000181459140c01044000030380014030b214010f4080c0a000c60a0f680c400850b415903400315511102e84d203507042c07036542500c80f1100400302542460000020140c00c2500c040c0200c0c1e04460002c400034080e800d200240c04111402c03c00540f2810041282c03031110341c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 56969535 1250 56968285 56968313
    0xd09060f151818150c0e03060c0c070815010314070510120e160609080c060706020c071d010e15030705090c160b0603071208030609060105040909050c1e090103 70
    0x58045401800f8944000e040000c114040d1000044103c00c0e680001e41e9201c0c21802e1003075030a02820180e00c5c0d10100b03965440042000e20440000121082d00c6c030003c011600040c000302e01140c1071035041c041c849a24030b1003844111008212100f80382020840440c11206580740500301079140c00b035100040381c41c017000c280c41820590b99002001a544414001100d8940c0d094800601e01d52030450b005200081a500c0500942c00c540303400481303030b51800200d43c0403d170469409a260000b20207101d00300104c0d584170040c40660070307407051301255a405046040303412a100e5018a980c0d82245981c000180391005941500100c1c07044c441450510001d50f00310321014400b0382884103841140580318a001429900c4803140410040366180030040007001d81103a4210786005181c0d640c0302c00c070600000d0401403188403c200010400e92041c02540d000300b103c128140a5145541016600c4070312604109001d80a1036040034038196880e01c900880030b001410344c25217a8655250107962400d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 56970785 1250 56969535 56969579
    0x60c030512060d050615120c0102060a0e01140703140a06060806100201021606021902160311032404050610080a140c04020c160e01060e060c120d09060f15 68
    0x4410f004011a03800c0001c148600c2e40c02601d15460b4030141c0800c03503248049094041c130765021604401590364046a001c0c2c004009000105585070404407590241090880c14408407a1140811003126890740100003445103000216580d41c8036000c413201940d103103000c0c1d0004201e44074041240750510850000c041446c038400141081140310540c50301c041000b509480c0545c010a05032030003056600641e50200081c0002c052981d42c01c03061500c102d2040c072010b00100040102c8080710388090102079030303241d4100158260010f050420052440c3c0a07102540d062040400241e5000441a409000e50714004020145500031350707180a00c00f1803444c1403100601560040d44081c1c0c4690005c1e03d83c211641010b4414480503c0c01c0d148111000d600100d0103c1a24004015907034104a816600c204103a84040e0b56456080c2581e14080a010103403104420019116000c03049691090541520406060010310000c04000c025524101c903078400c1102c4050341005011f0042c6000b00101c514 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 56972035 1250 56970785 56970799
    0x11203090801060603090203010608012007140d0809010e010504030212070309030c12030206131a0402031e06060102070b0909070c140f060f0f04030c03050f0f0c0313060c03051206 79
    0x20740301002e0a5665540c056000300e5119140c03541180707070a025100251000384004c1001c80c0c0c0c0c1c01810981864152401d603c4000300141c0b81050140b1030100d241b01c00070500c100e515214012800610b5a401250700004a518140600030642c406000b0f05003d150994010144005c0d00003a8500d2a4440c0004a0038007812607000000201c18840000080c80c01e4546c1041d84003440c00c001c0e05001e0001c0840d01100d10340d6107543e0000b0341d402400d48880c4030f24410094196102c0c1f01191516002140030301c4103803c130901405034454001003061280c00b0a03030994003160b654004000b5540215011a0b600c020251f001854042c4128450b002e49802032000b189459144403c4500703000c94429119035a400c00020800c81c03011008004d600002d1a43c8000d2461510352001002d5200c210401020032400180c8583d069284406688524044050f4030399980c00100c06903950350b020b40d0310120807902a081c00604107018100388000b954041e1600c40c58484070442e0100076079030040c0020351000c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 56973285 1250 56972035 56972039
    0x120105041a0f100608150406030807060e030406140a05120405010b0103060f0503070e13020d030c170906161403040807031106070b28020415030617150406090b04080d0c05040b0301120309 82
    0x2030b0324000d00000354058090240d41c3c100d40c0c1041ccd000d4070392100031382d8800d80c41004100501a0321180d28961031918031002501c54100b91000c0305c032442540d5003010350b075111906000030b2200c19486a0b09801d400d0300c0c2040040d41d99041d1071044503040c0310b280d0381074000030400c01103000781c151401d6010785c0c0e0705444071401c44590300140f414941e0b80825400609540000010442441120b290f5848525000c50421141e00000307007803440788403185104411410742d10410404070b0704007044c5140360b62050b2900e40d40c0314545c080e640c5a0501c004c2d81c0ea04075208070991917090000c01c071060b15800a101200035911081d21030754129171503010301c60360141210314540041d4944003410107082c032102c0c050340d080800f41c801000e03a48141c0100c41c031703c0b07100c641000c124040000c08650070340c60880c4070f030210340d141d041a00c02010350001c040c0c0000d240c40f04000401408900070508005108010020722055030402c551071b0040340900404040100014014014146452030801e8400d183c0700d10269 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 56974535 1250 56973285 56973289
    0x1c0c02150a0801140102070311100c0c080f19050c19091401050f030706050306040c0302041707030b070c1205030402060705010606030b0f1c0809120105041a0f10060815 74
    0x6403080d4450700019842c1401807002200194015013400d4003440104105421500c1c0c54154890410030144101048140380740014022030550801c1ca81064541080759610700b446500d5454401c680c7c0c006025446562500f1021030042010003a000030040210b2032041081c02020490300841d4014051080d50010b144055070203440d0310921440910425075250409001c0c85d02e00841c01c4903c0398004403014840c480d44001500c3d0310076004c5a0100b400001c410b0b06030000d02c12a0012540c04014040c9d107600c0301000035050049a01c00d801541450380e65030000c0701c907103141e43c10041c9501c94002d40309034424419406580c010380009c0c002441d08003281e56050841302664007050209446486420340e07403800e00681248840d040d05c500c022100d00003d041001c3c48003050003032102c0008284504283c407804038401020f1003d8008005034289400e01031900c8144481c83c003820070320b4800242d44100144080c50264408200715907242d400c10900b9600c00000400780d02014420384089003041d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 56975785 1250 56974535 56974537
    0x60f0111060408040603060506071208070309050a0c050109210b0601051c06030510020705060109050403090812031009060506070201030504110316150801080a170d02041d01081c0c0215 81
    0x2580f044880541d5103141150141c04e0760707d10b51150b40b0950060100320b01190441e00024000d95041c64080003030342d078020f011b07001000400b4002d405072165104d420100f10307407000503005445007600e6041115689205001004000c1e0203021b40b801e00c22402c04000030b03c440001c603000300050510f581002c02403040543c44c088480301500c401c0d07813900010030504c1024418412281c003c0482035151665645070039507284818421640030760340e928001001e1500c42d4151078054000c101c1910302010f1110442c000315003080d40c000761450020280007030100c1d01031140e4811188003811440c28400d4640065004084c01003050b1740b807071291600440380759020f00503004c7c0780f24035174242290a400c0469400c0002d01c505000c40502c2000001400800b000092040301c041d07000c50b641d1030a5640032007441d907900030b42c298108198008980468200f160480c1c2020184078111030881c80e81c0d8078074205640e0b209410b0380c2101c0d06589141d00c55060b00c1004404140c03400a018812200c1921400c00c1c52 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 56977035 1250 56975785 56975791
    0x27030c0c05120d120c2a08030c0315010c1502070c033f021903020106030512041742040602030709170601060c150507050408070e0f060f011106 63
    0x340f600710585401c0d03041d40204421091062016080089044550b00074100010145100c03400701603040c00b05900403060030404620036072140d00c660302d0782884842d142d46a041074501c9000301e500f0703500009003548500128100b8a8001035030a895120f0480c13013000950100005441902140901101080f140c071031600140310a40142582c05010000e003542026090303034020303880a40072054080c49980041c1c4842c080100341c404203001541e9240a0380103104592006045000d83c0840d03501050490020f4407c0781c10315601031000340c244020440e200c60207506071b034418161511381103100300c03080200e161a000b142c502000550072410a413035081c02003150100d50040e00001013000715688100e1020040ca0003080f044000301d54100003640300c0405002d400e0400018020400502540500384440ca4040703c00c10016420000710080c8281c4c0203010324500c80c030609030f00040e0881c4c80c4074100d226604041180c40c90b0b407245010007280781d0140403040d040000c0c03803806507140c540c00e0001c140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 56978285 1250 56977035 56977069
    0x70602030c0c06070f14031c05040209060d05120a020a0609050102071e081602060d0914060907080304090b0406030506010f080d0e060702010804031b0303020403050127030c0c05 78
    0x145a074606100300b40350440110145000c2c201c10f009420000b118100841c1c07606500c00300d1031110901c01b2000b40c0c61030041c0c110740c0c070803d200da400c82880e100803079024a011302d009840b4003096603607a105100d502640008010074551207106a0b0395041000f801400180313203e84140c620490a07600c422040c0c0c0c80c2c21101f0358a81e580000c0d0f0000b0401c80b00044240a02d02c0c40b031040c4044440c0d10380d620a40121031013280e680100a449038115038804003114030003d8461020494a13403d410642c002e110401c255031320f184074030400b0810518001840c02e00b00e403a000011407515041c61003170030141280002c155005a190b0702d000c070001f00c090003218003030040c1c4900e441101340ba11000910300811200032000703000f0314140f0007000b9180c8208076481d6540a08041c079040d00e891604071a01c004c102240741c07029040e4404201010790540040c070840c1d0060000340001c08111401c40b11024481c2d05000c16140d00059400009000780030a001042c01100310b03113180c43da00c2001c66450306400603126 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 56979535 1250 56978285 56978287
    0x2010c0215042705010f05010c03030c0e09040f030e030721020a0306051f05040c05030114030705121e06060d020d0602090603012c01051c111201020a0801060e03060106031d07060203 80
    0x420443c00f40d11405004020816141205d0b43c80c00300040d210343c4007444040c0805494596061081c1d000310325030400d582d0041e004800500e07140c1408059442d50300c804400090207500c0d0b5900703e140c0000c1603410760b01000342280c6140c425946000014401c250100c1c1c01c0300551030300002060281c070034103104422030110b041600240e1103e0000e1000301d83c100341d1055140c04c042c11400c583c07007001e880c1034425680034041c0c20604440028517200580d03006507804084850044070681c800f081d054a0041202d200d000d581242004013510317040115401d0750494003d0810601600d44460114002d60040000600d070000c6180840c080d0b03030090300181c4441c140200c084070b80d806c600503551500500d5400740c41055040c000041c2c00294071184040200d4050134041c0c0520100300e0a41080d600018000004500018180ca010790460f036039900110300d0410000502034091310750300500c0c1070010f000c0e0800ba8200401900103268020140c245032030400fa003000c0f48441000518003034607560b0019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 56980785 1250 56979535 56979599
    0x501050307090606050904090203210a030f050606030423010c0f1e0e040b12100506040e070308121e070207140d030210090303110f0a090e0402010c021504 68
    0x11601d024890741c0228409072030040c08000710303039111083d1803000100300c0700461030b100741c0c2c00000d00d0070404010f8008210011001120781040420080020206648040c041c0c2074108001d081211030480700550004020000100090310100188c0100c025101488100d00503901c415400c581d10f0301d404001084040c014004640e81090080200d43c10743c16401c841c0c0d00034001d00030012300c600d568050040d52140c101445c155100000080d0350680c03c412240c40955007034001d00503000030740b6098000c1d45024903030300207000c01081e1342042e650422101c070310313040300310351441d500441c0100541011161031942c2e100003540c00310390074081c4000398014489642450300d04030305d000301d4072009445800040611800240c01040c0b94030f14281e181030010303184410342001d030301815105180c03403007840000640c507000e110383ca4043d120050090b81d4501d520b54940c40c11801440c7d00f40c4010740455640c502e1f120040c03404459084500180e221a0b509160b90350210315180f0401140c0c0c007403121180d01d44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 56982035 1250 56980785 56980789
    0x8031f150219120807051905041d27010207060f0203040b010501020607020a0206181906080f0402090f040203010f0e01020403030e031606200304030f1a090303010510120e01050105 79
    0xa4940e02c546a150120500e0321a50b50704000a01040104414081000009140c80340290706480076a621080002426004040010032300e61150040c0450050010300001c00a0300f1070030300302c3c40380c51704400170340d0540c5d4a140c04011184800c0d0b82030303d556400700941000246e030b5004151100341c0d0a84003517200c1c03c180c6400707422580140c1100e811540003404200000e94001600510590145c800560b561095060b25100104901c100b5400200000c141000a011002d409080700e000340c0e52206141c075104e4480e02000c1c01950040c0d409803401001c2510f14580058084d00544000c00000703600c46907032048015102038090082c0035940c0801c00300b040c035811080c01214080203c0c0035180c00803601255815403100c90142c0740401000c20780350004450810b090704443c02851040340d40701e0b5624600302e400c4d94248401180d80813103000c803c441703da07010000719000d00d51f81300c06142960700300301c140580303070512001a60030482c0c2c140440a070802d5901ca017895040c00d1000104940d0b0400007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 56983285 1250 56982035 56982043
    0x20f040f050f03120a0507050109020405010b03040b010f060909180203060f15030a020607030e12030c0706140a122706050703110c06010302150c1e0c0a08070308031f1502 75
    0x1400b03030b00a070000740e103c0b620021107508a421030407581c03c0041c1c81d100942883c41c014a15510003c0d00145044008180b5102000245116500c5056404c505a0300d4116420882210307105a401041903840c0038008140c054000140645a89410300b04c04189030300040e15201d4240c449503800c8051205000d03141391a01c2d00301c410000e050340141140381c0d5a0b40400c0032845242e00c0502005146151000300d41d99840803807401d4001801140e840309180d5000b40e481d40381521503040400e80250329400004a0741c8243c0d090420300d40c650011940140f41c11002802481403200fa0040f80c0c0c102441c0b090300001003002419025520025207468080405400c41d07450802540a00d4030500100d00882000100181501e40c140c4000609030001f0016444a0066003c0b1003024000d440103000d450400c41c03403001101628008844d201a0060706021400f28280900e00303080c1c02031001880855410002960402481301707016a07041404200c050075190a90410500c010f280b2203075007692a4100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 56984535 1250 56983285 56983309
    0x81c02030f0601091a070b090a0503040b130617040303050408160303020c01060636030605090c0a050f0d08130504060e01090f050c0301092309070e0c0a020c0d06020f040f05 76
    0x5ca524400005409000a02e078052080000c1410032020000707003407068280b1128100d50740c8142180d4a179070712500f0301c2c0c0b00c90b0000300e204841e101c1a05800602c5920429100c04001c00b10300c48250282c40340c0d1030440103010010010707580c010040040031520524a003030749208038005d541c01a150281144500d00399103e60313000c1801c0010700000358800b80f032411074845131203107a01568854000a10a1680202501e44c00035000c0c038980400c002d024070300400c489000340c5045807821080780d1110104841c403a00c0494031900030b0420302000c0001a21314004103844607824042d61981560398001800317645d01034001c40c016100c8407004002038889030045400d80f8400450501040c0703040c4d07803190500c2c0014410903c405807190920f4441c02d0380c04240d0140c0350360440140d6010b1821801301503842c100e42c40303480d80c2400c0c0d001c0000c000700c0324032090b580c0081003a80505000740400d401c120000441c00c1c020340d40290301304201852102e03903000400041a00700c9544c2d5240380780200300004c10f8140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 56985785 1250 56984535 56984549
    0x50705060a060b0a050705010b0301060905010e06030601081b0f06030901060e0a0603080a1d040f1a0111030403030c021804061a03010c020a0201030213031401050412110a081c02030f060109 83
    0x240521510f2140c070300781e9015a605203007064440c606428403d0151140c0ea01054143d441d011022130285110742186059505280803070b40503880f5a03041c90354505007441550429002250503005c04080014400c4005d2401000c1040c142807010006c2e00d55441540e03400410781d901c40d0b08110b400184142e06601c80503009082104628540311212a0f1080039041420010240314a0320103030003940c0400f40c040d0010700304008408510302e000d80100502540c130110320358800c4500c2c8544d803150080012011112000c0d6040c640f95a40644040680d404203d80c00400311590226901402c450180300300c0c068440410218000f5107050f441c54100840c06e13001e80d060105e58a0f0041c1c002a401684990a10340161380700c280052003040b03d907182d040249005007030701350030340d03030300015000b00d8083c41c021900c21114a1114006850598840700e800101c0d8110300c4244e00410320080c050008001c3c641100f05411452410702d108983c070490316500a10800c83c00c6c481c1d07950380302100001030080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 56987035 1250 56985785 56985791
    0x3040317070308010f0b070204092301090309050402040f0b07050a05030f0703030506090f0f091c0206010906050108042103090b041b060305010b040b030901090b0709060e0301050403080c03041b06050705060a 91
    0x50002c4503800d07101f9100003a02540e22203500404110400504040f0030710044c1d9880380004c48421114007808101d4003d400040034440c022505241500c01c0368112010b540c0d205042d2464154625000c6d041844160b95a000e0300d410000403800c00d000510b2400b0010301c030141d555135070346405000c80741d02402090090724003808000503441c158084c4c2c3d070440c201c802c1d00300d01541d0701c01c4c81031302e050000703030720780007000900040760b00301c242c00280d01c0d0706070b540c24107003800025150300044a81c41d078100d4016040007042e05900369291200d410501c118040c03403401082d001c242e5207076603120700d409990480d500e00d1170402440d0034645010519024144518040c040340d40f402c0b00380d0845000d5402000259040040030402c2a2000d51101c1449a4442400105417a000740003800006091017060b021805d0b00300210010300d41131081d07500c1642d02d41c640141c9501c89014491040d04000c100720307040e141d91014000ca280204695100400341940c50780d41d580032500e022030910201402d0a0441d42c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 56988285 1250 56987035 56987039
    0x902090c03060d080a18290f040914040605060f010206070e030309090106030e060108010c0c030503130c0b0910051822021305100e2103040317070308010f 68
    0x91418405500020602201a22521001c00141940b800c1520090140030001040381041d03400c15803083c2d817205c0c4449a845226a500e03010481d241120514030003040044032031044890610025140c624074002d15035042131b48510726807044400401851840c8002201040100f1199001e15a444002a103105080486440020b0740d54200a003404c030502c1801030000600f514200151061010000c01128082d696410013a000348800b1404501300d014010000c40d8034141401811414107095680a241f500799440451750385d0409018565180f400300e00301804905c80c07403510400b07050b40d02c25190b0303280c18600400c54003107440e5180c0400d02500b070010340100d04d0b4006480c042d0440959100c0f19603180740c20b170032180390003801c07602c2400c41c030100d041245010f104505409880054501440c01004c400094464140a00d24030f03502050500e84119000360080d07210b40996105411030b800c00382c595887c240044460b81c010107000002203041c4d070515034805051801031454801280f0468 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 56989535 1250 56988285 56988289
    0xb03072c040b040c090311060c1b0301050709060507060203060f0d12030b0d1703060f03060108071a0f0318070504020d02030411090106050406030203040203070f03030c0302060f2202040612030519030902 89
    0x2205d43c0710150190740180f003a0003607a140c45040f0389101e4050001d0318009101d010400224542d004a550700031740c42c000000e41c1450103a0030360411b890340c60300c850b800d1103010307a80c12010390b100900058002c100541c0b1000c45840d0019000c81d002c1c13040140460300810108002c0403a200911180e1040038a41305c150003182804200c89580d00580e03882c1c80d0740c1e070340e00130205034292a013455440c0c140c400c400c00002d400c07070042120410346008480030000d40d940c0c2e946c03000c0a40580ba814840d5004c00304003142480180354440b003801d02004017982d0290f40d0320000281207800c207440b01ea2185030004208000c202c1c2007844092000c108484600265040460040c0789010324042d88003410381c0080890706641d01002002c00406645914807211394a0340b800815440040d00c2c110054403c200206004100c1d005800788035410064544c0740482013000000b0141c0c401c1101660015610000071035816000403038101c51754043d44511b44d50340c00010f900220441c03a40814400c0600d80a005001070f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 56990785 1250 56989535 56989547
    0x6140126060105180c040302060c030706050f041518020301020310050a08010608030a0c060605030712030305250f030e030a03061e030203061513330f0b03072c040b040c 74
    0x83c0007801c0313000d5240e030307440650b18110300c01c940010350300510216038000c0000001004260862192105014584948045110200041d24002c0c56070654413905c4041d002183d101180e1100665641d160300c007225000719003264020740c1c014481808641c41400381e4201000c00303030020321051000b0408985004a901d4890050322100c004001025103054107001d495040300014003030050640301890368501900d80045e11400d0120042814040090840c22601c080740c0103900307040745105007070220117204680c104039140a081c24195103047e07040740c0d2002000a0b010321661514001581c900303100c0d500003900c5610404aa220007581c00504c01a01c01143c090703004940004c080308084480800900071070005120044500d2074001c04410707140b01c6041c80b0054042a000c03000c0c5001c25000802d102c0c100e2405520008007403e03000b0000c010781800116800300d9140790040e00011707600312143c000f2000c07039480090920b90740745080301450644244680781e04100d03070401c40310301c00440c09422 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 56992035 1250 56990785 56990809
    0x9060a03020c030706020d02040e150306010501030b03010f06030c03020102060105090717070e0301050703090605100308030c09030c09010810060605091012060504110712080c07060906140126060105 87
    0x41603000304011560b100c0c104141da0515620010a41d00d0316a5082144e0083d0810301c00c84009110030408070b0401032044066558010024001d8250790b030070300303006402400c004024a03825641e2135a07130314145107081c4070300c0010350b11808803400d11625500009250601c1a000540700361481411710103030a07007100042d14030000000051100380e881c140180c2c0e039100c10702c1070150103508103810072100560503400008514820706003000303240c407a08079250700d80303005010042c00c0313680c2000890a0381c0000c1c00074007604040141160f200d1401c04010950110382a400032266a22110701e0030307130042c0540601406031855240890800e02420005008501c5540c0801c09100844c0e14030301885000750050800751101130814040025400380c40c03407290b0f01080c0c007920010381030480910000c2c0304010b414041d184008140381841c0607038451800400441008560507541c400e401da1802540d00740090007440301d620031165012103454482d00707421b00c0c05030744492908400018046130707442c5420b03604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 56993285 1250 56992035 56992037
    0x304030c0201050403080705010c0809030f090f0a09060e01090c230a021e03040602011503110108130c0e040201030e150a090303060504150f120b0a020306010c02040f02030702010c0509060a 83
    0x4400180d41c00183d40134851600068030900f0001803000c1408815000501440c80940d41c080d8a9a00c04030210303200d0150110800019404000c01c01c058641545105541e95009013454000f0381d50301d0a80c400c6403856441002d83c1d0b10000c004001e01c24292082c0e00040c025428020030303091229000102030141030181284280d40840c3c504201403080142980c0b10400c2c49038820049612205590745c0c3c1c2041c0b24030b40c0190300313280c03900319020340e034103010303422a035000b91b00455548400c4010760b003c0500800700c80ca049940040311000c85e032400d0941008000e28120680d45040a000040c2600c3c0c0701d801e066050340c003400703400559a41c0b52109a9002800c5003001034042014642100940705a91002e0341c0203042554503101c13403c590481c81c044424102180c00d085a0f106c40c0103030103c21804001d80b10501c1c040001d10285500c0e0001c543c000c50525111402c0c02c80f580c0004c1c229400b14001071a40d5601008010a40750248a25550083c05003050f80c202400600015945c0c401e10b00004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 56994535 1250 56993285 56993297
    0xf0613020303190302091207051005040e070f1404030b061804020315070201090203120d050708090a020f220608070b0c0a02120c0607031d0405130b0c090604030f0215030c030403 78
    0x3c50318a1103541a50707903401009016412515414800076551111401628401c0584250260000c0d004600310b40c1203034501c56010301141d45102060700ca02e00000f03940c000703000c042c4507200b11000b907207801000554030580b0792458a0500509001c3c03804104080496007110305018400546c0e000141d103503045800c2560800503503160f0301c08a0241005440007905886411030b00240c040f54503016200d07800850004210595540e00103e888840646500407160020f8002202500702a40381c09407181002e8400ca4003060400101d50504111025046503d81d541d40d080c46124002d1001d900100348401c3c08a0a290101030030390748404e00714200030720480d80303109001c141c410309000d841c0030070200404064403010541400380240c000b11f00101c03880c240704401c8081501c4e05218903070041000d50380d56210896903503280d01d82c007080901901521b64040c006110707203507141c03c0208083c6120704850b43c200d41440c8140f05007a5603e610080907900b00303108029506480609980d030240d014600300d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 56995785 1250 56994535 56994577
    0x10080406091b0f08010516080f06061306020606010f05040803090108090109140303090706030c080604021809090a060b04110304020d0809060a03061d01030c0b0904060801020c0f0613020303 83
    0x4528007035100da207001e14514079002c0012040140800342c0d00f01c0741054020301180e80c035070740858981070507040c7d040c000c202d4800c04942d076440000c3d201340d4000341c05401207182c15440c0b040c035020b2200c07a0340040e00607031224007000f015507400004000110300c0750514600346400c280d00310341c6074041c00808604101207800010b00a84094004a03440346e0045a141109080041c006440764000c9640da450b40c40380d40800940c2511034460080c2403032241d920400140c40301410840039605c07041c0d0041140303040105000841d0303201d00880703004904c0e400091605410303030b00d080790a0b0f030007c0c0300f51403140e8074107019900318003284000c0f03d50150781140d00782c10741d07035051030300302564000c821f1a950030100124a840c1d8860301580a80280c4504822034400000036040a68408509000080c440392844a041044000b00d501071310050304014008100c0d01d407941a42c2c0c2c01ca81001244445030751188100041d040001e110f0641c2150001d40665281003198020950700e20451490390100b400721001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 56997035 1250 56995785 56995793
    0x60f0703020703210c09080c01080c0304020d0b070f0f0503131e0501020f04170c130c0207121a06060c0c090424050403030b040b010c14030405030a0b01080c1008040609 74
    0x100a00320007012103042003480f1844d04080050103002c00003000b064800c42d0110341c1c403800042058140205035035110050303858200c140303400e40000d04100d0304078940e132858000044900c0446407260079160f8600b460018500301c010858a2108801e83c1800410014042d02c099a00b4002501c7c40d000102210070800a01003920041903c2c900035000e035101040c1070b030380b2003800402003089500001c07100c89a10340411405403182c1a8125059015282800b203284041e004d401c203545204140c0140c1d00c65541d603030480003107030328944812500f120041200c04210725640c2810b54110310143c68442c10102140a5640e449003025010743c411050b000c00542008000000891840d80d030702c1c1e00038043ca0600250401401c4180e600318040380c1491a01411400c2c80d01c46c060030314070142d4440840c7c840341d132030703e0402550070702140080b4002004081500e8608016202d030b042c0c070601e03185c1410340c03400a25900744070703800091600c10203031aa040301200364003038604d03908507400800000301401c6a180c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 56998285 1250 56997035 56997047
    0x20c06041b0305120d06170a020d110406080102130f080607030504050c0a080a0b0601020118080306040603240b030606222406021002040e040b0c070602030a05041202060f0703020703 80
    0x8402032442c0315180400a882510401601c0e2400300d004084c401d0f1b54a8070010f2010100034040d80280b0340c014040880589003840c03e28081e20300071505524503c407500045400d07141181c0010025a40000d4007103030300705d4842191801828003105a0880c40e0420760f40d44e8031880040d15038401c058458000c2802d200c4142720758080408014802c241d0343e680ea52400d034031515001c0c8280c41074582200010095401801406400c5140402d03459080c0d05c3e60795100102c6e003000c1d004980180c0c0c0c8100100004503d80452008214043d48081c4800000300103802541c6250301e66074044c2d0400300c01d00401e5150040403540c00001c40c5910a400b0340103650305001450b4200d04459003001e030100c800d05214a1500c044140c91050b401d03601490b1164014038141c0c400e91280c98411008000003801090410343e1707603908032002441462804a9580f40c0d8130581c1c10984002c0f0503030390755005120402090151195801c503013030000d020307a4508103d0210000500030708440c18990005500800c2500c00c407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 56999535 1250 56998285 56998289
    0x3020120012a0207060503070c03020a05060103060203180d05030c0304060b0a03031206091a0402090604030c080d080a0e0a0b090c0603090f060c0c0705010e211f020c06041b 76
    0xc0002d550400d2698103903000880c10000b01c1c501c0d00c981e00c0360007071010403508241c82a940307030140b86441d1a90704a58600110700c050701103000da00ca001002071800d01640b8001c5002d03080c096241e081102a298070b00341c045035400c01c1a44007a40655110343c1200a403544413185250b0300e6226610780c00c021010340f0703840c5040707a88510403050200415412200c1d4a07000e085600040280a840d04503020440d003d210a10744c3c40d000c2c091210300c861034260010440c061001d090642015680d81d81d000c00014607030004100b540002560711035542d80302c1f040540c495028441032020041c4014001c0d1568403411028010b06a403000181b448070f4100100000f92202520710355036450b00210880e2240304540d0a40c0e03030390040384041400c11020b20182d41c01d00204001400c1038500d403800640d20b209019181c940c110f03107484240e0f04251791003030780700c049003061002405011010003603100c10348100c280354500083c07050283340c00d0700d01d000524991013036004e000c212049849043c008074840040d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57000785 1250 56999535 56999597
    0x81503060405010507020c0f13020a110a030504050102060a02030105010c1209050d0c051f1202030702010615030507090902040b0d0b150c0f15070807050a030b03070902070209060f0109030201 84
    0x8041c403080050541c06184142c0f0281d00703941d05132034030000b08500702203003c0303000380c1c8080d20040104088104c3e500500000580d401c249510341a40703c0400c0c107086a509055011450200d0204070a503014442c00d43d0042500c41c003180b5641c18040060142d2000c0318003d416003241c54440180e007405200c0503005898010000300311401d0501d840a00d0b07450300e000d03503401003401d150400146181d4000f02c44d0482c0b11030315050f01c0001c41d02903410080d00020415011903489941c001041c070b51100c43e0148030480c559001c0f4092070031080207000c1c10125804007010510400042000a01784015a02e5030450040b0100382401c03400002111503000341c02084540f207000510700b9004d40c0005007440d0800c00e0b1400ea80d4003580220016100c14030440c0c1c0c0c9000b2a15080000c3c040c41d103d08000d000000762410009101c5c2c02c104046803406001e03800041005500141c0b907029458240c9900b540900c0450f0f4140c443e04440c0002401c3c400700d840005d05126903140c010f10080201800c8526549038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57002035 1250 57000785 57000793
    0x1303050105012d05030307020d05070b1209011d1b010905040612050d02010c020705100c0f030906021902030c01140c100f110c1209060408060c03010311030304080607081503 76
    0x40c1e507622048403642e4881d43c1540c042c0b000380e601c1003001e030815010866400030051030904215400f4002c0c1e06200d0340307040300c55010312000072851b42c0d81100070702002d405000e015145440d210301da0b83c2c2107900c213004191a0400d648070320351901c0d40c00684051080607130100d404842a9070300058a040c01d042d046980d03c00e00308180400c81441c800c2000580300d00400807078410034001d9000364200c440b80c40c1c000c0010b030019401400182000c0840c459440d030303603240c0300e204000703d0b0319404d102c10301d003120403800102c4e2003800b085070b150704108403040b42040340c03c4100c5007131345980061b0b81c8400c02e22586d4144450090741044401204003591100b005510507140300684607030001000300040851092054584914010649056803d9420007070386803004020400e59160070603a560000b940351079101d9002c2102040b8103105100050203031103041c03400b640b25410f44c64181a21420150200c0c02507000344401c101100c400035125800503440d013802c1c1815299050192614260409a00c1e05841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57003285 1250 57002035 57002039
    0x230a05030903071d010b090109030501090303090501060815010e0606091003061a04080607030e0c060c0a11010c080a121d0d110f03040306020d0e060f09100212010b130305010501 78
    0x2004401441d844030214180c03220142c03200d10840441c400130000e442c29141e00d400500403100814002c03c143d89050404511300b6649945503030a64464080440001c1d80303c01c0d668080000902078040505031450180c5020605150607030520001442400f040454031404220251940c00c00c55164100244c8070101c407140881019020f0f1036207100c1c0b0401d1350301c503089041c0201400301c1a902174840107009080745842d0041c0490103000221410441070240909420841c0d0f02c41005241c0c4608103009001900d00f0390600350562080c05210a05005040100c400018003010483e00304420034200382907401c0300c02010f08018022031242800d0b82c540c001c000d441501c00000e01c0002d460b220303503403000240300c010601a10355143c3d10040740c99a01c1407006100090070350700a4100300541c0b4500181c1080000c940e00d02c0e00c9000c0c1c8a1402c03035001ea80c02d22124540502042e109080051410340c50301010242c3d14156400520a08030410008544041002d60188609005540020003400b61356 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57004535 1250 57003285 57003293
    0x110f09040f0e0f0304081006120204090320100608060f04020907020f070914100b0d11070203060411031002070b0601051c050109020301050f09040807030302070c0803030403020c2704230a 82
    0x207070041c0540b99042c42947d50070b000c500d00a018050a07103a40041c1c000c0043c86640c2804050001c40104409200150420034a00084490303001038001d0301200a002c02c500c42c620400860b007082d00b1035032171500858100001c12040440154025034152400031b0309641d803030401c90400c004540b59182c580a00d032800580e0301d2081d0880c984140c01038081d19800d894980300c00822150600c10700005510501055040603e10303488980900c021101143c81d202807a030020f41490411030782125625905129000c00c0d003001c20042040340c0d4900c101b145000380f9504c40350150000240007a040000000e0003540360380054110380c658280401091009503151148400030303400c01d0207040d000b007401c800d1809a500d44070190500607072300a2055807802c0c201d80c4007140654400034040d1405400c15000050121081009620a0f40030340c4c05010107144d0407080155841401c400c00d10110311081d41410f498080c0700c4441c0c0c00c554026080007202c4010288804107480c1d13224564080c1c025141c8000902c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57005785 1250 57004535 57004537
    0xf0b09030316050310170307020d1a0c030124030906090501050612030a08010b0702040b030a030203031e0601020303161206060206090106080601120609030e0607080d110f09040f0e0f03 81
    0x740d00b000040c0c40d200c1030724281c1100d480c00111401c040118021204229007990800d0400b80c829002003501d10340000394002c078484090300e04044401d0104600c00d441509400010142c2000c400682c05207594900030a104102100e0f696409500e0040401c02001d28000c0e8407240400340d01c010b003403040c00054140766000303040480f41c0c10300403425080d1440d0242310200480b554030038a92900c2c070190b4204014408a500520350403608107545110320079403542e00700324018406100340e00469480c40c003280880b2811140001007003280d43d040c0140310241c1c1e0040152581704000d40b480035030850386d600e0100c840702054030524103014900100452020741c0490680e200c1c112910080c00001d95130103a0694500d0240314901801c18501a00d90015600f50410b950217802403500030880610000059410780c0810401c440034070300050000c0c0c80400070f014603410b140072040007506081100050f030340e4038070808841d54070031a96403801d6105280194400c546440398041101c180941c0900e03c1652 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57007035 1250 57005785 57005791
    0x92103070b06010806010f0e03030702041104061b030c08160210170609090a0b0c0c011503020414090d030f1515120605030706050c030c0d0504060e010c02090c03040f0b090303 77
    0x31501ea80c2000881da0b502032840b15002d0030040e034891924440c0618112980c041451445502d40020801000075079241d00590740a04110800143d4451a109018103540119400d0702140d001d50b619213000710f40c0011a48520b0740d00105181e40e03031140c19488140540ba0b03940d0080d800f051603000190010303441160f901d04504d5440042407c0e0300c0c3c2c0c80c01c0003001003040f556080c1d294400c6908030300081d403803100540c0010903801c4542c20071002c04841829601e2088070518003d8500b5020019407409015443c0a0b2001d50440c0729507082003094a0b442d11303000408003003032503290382400a650081d0b9104034200c0402c10300280070310382c03102c10b03985004002d0740c00000040e114000c811408c039140c0c070a04c0d0480c3d0780100280503051910800395130ba40c0010040c0c4170640400e010b043d000c20030034170100008410a664280c0d0f11805c10401500c408410314042d0f04000704c882c03045005803610141241c2103011312810b01e441340e60f02e25185042c1d000e96000205954901000d21007200400000b644c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57008285 1250 57007035 57007043
    0x30a03060603020313080c1609090b16081b0408030c030301090b0604080c191203020c0405160203070615050d0c0801050a0908090907020c030307080d0501080f03040b09210307 77
    0x211855650004030b0a81c0020f44d0360030602455289080005980d4100400028004000b035458101e4800d00d8440061030990000301030b213407200340c000704011700041c00b01c0c3d01c008004640f88030040140c100410200000380100711160203102c7c125044100c1c081034400a00e06001105d54035009040307907648075082032040d2301c039841c202407035625189821400c2e01d0580745554000d08103c0c86030b00c20008003003480c0c070180b0780c41500c4010219400c07010f004050502401380d0014002e44481105000031140000c0081035001032030200c5081030343d40441118130554002030003103075203c212410001140215400164068a800d03490030030040e0108a02c001c80c1d0040e0700802140da00c004009050310784001d4010704010f410000c2d81c40c01e01c1c2c180032164100301c40f84120f503040c0e040d06001c070b403466204c0e20040d00e41c1c0f4404a85030200000500905001d0000e90001e80b00460040f00825076a009601815040701d00c00700304a0910344840c5da484044000d4014951521206441d01c1600c035403045034103071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57009535 1250 57008285 57008291
    0x20a02010e0622030f0509040507080412080121051002030f010815040c05060d0b040f0902040b0a0506070803071101020a090302030c040c050301090e1002190207450e030a03 76
    0x1400030254003c002100c010905550180b089039940c0c1103515000785800d000074001c0c28082c04c8000d858030300c5118818950b03511a4240c50815003052045002d03608903080030002607134014072202280c020a070018400e5241c410310f403603040d4a8142d06181e030038828000800e00c04020807500c1011481c64034100c54128056440000d02c88042460030f00f0100c070050090034406000304058100304005060005840c4000a5061040d000003000d03100240c2c1c404c101365440382194425071400303102d207520f1070034100c800c484290320b40004904a8040ca40c5c0103485510f0110000c1c040b140541041090746100030000c65407100b040d8009445042d89000582c0a07102d4030700c1c001e01500b414031503010030f030b05a5200d03a811a0310f040c4414000e03160340142107e1500030b409034504e1942041c0003070b1110007082d8020081c52000d200c40281b0301031440c2d020108104002c41c80d4011082098860642058070030580d40301c1c10560100b0000b034002d0700b03800c4050b1500c1c0005890b480303c8080060180f03100159014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57010785 1250 57009535 57009541
    0x30f050a0c17090c010c061415040e0a050d030908120f01030b0a020901080103080c030c0a0f02180f04030302070f15050405010f090302190f02090108010c020106170d1110020a02010e06 81
    0x10464042d402c40d030010030740c0d210103e0800158081e02c40580e00e18402d09004ca000b0f8005448000d2428060b00d0341210f00241500c08009440c041c061360030081606c0005103030140e0b5603102c2c0359807640f520815109040e030b40d111040c2407100c40000c843c0a035100e003018040b0707420a00800003081409102c160380001c910000304451882c1c030300844407000d070141e446803c964219100c0b10010381c0700460140d0244070400030324264078402e200d03030b00080c0d005011103606031199006000352800c2801958a448214100300305444048003443c0b90469018600140c6031041c916004503882030855001d00740c0d070061001f00440700380c0c68210601c00e612900c000e020400d00c0400c001c050f150040c07001805a00031700001e400845400101c01da50234011100070351a9441500070800b0301100b030700960400e9440b007100c805104d80900800f4000c008010441c003115501007034045c2c891440624420400440328080d03000040b007006400309007600c02c54110f6032103501500290007007401c14183d0910740556000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57012035 1250 57010785 57010817
    0x150717071b0e04110604090f0b04150605030114030c090a050412180522020c0a0605010b031302040c02150c070302011a0102060f0a180312050f0412050901030f050a0c 73
    0x20342412a071860001500d99259903849065248000582c2c030b4201700184030002d171103c1e0710700400841c403c2c0141c0008500781e03090140001c0d1030300710404c0211070300818002c00c00540d11104481c1190000000558020070300c0e40020b0418080c90101035010308240c003030020300b4405d90700c0180200d200b23000303205220f010080192405418141906a2041d280f0010045400c146910321000081042010300304994600700070101d0300a08880162070740561340344010880030340305103809031046500b81c50131031504001e130311501d440740d1000038011507c600036900e43c3d40c000c01c0042000201c21841c1440c03440d0003034074446d1075004440180d00542c00c00000f100c510465848000385003506a000e024181e031040c00c02220801d02402c0c40341010303a100c18001000f420f100503440349610130f940d042901030507040e0903029207070003800481d0310301007400501000481c540240c088501e05410507a0300c82509100503030082c42c924a40c4040b460800e4100004240160f000d6603400700c0360740328218000c4039000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57013285 1250 57012035 57012083
    0xe0415030206030105040213030b01080d0f08010509010605070f050d031505120309010c14030a030203010635060109030803040809010206130c0504090c17010c020d020f060615071707 80
    0xc0080d40020042006105c2420725400078903010230784101d0011140c1c1c1d44d43e1b0b25100d190003688241010340003011401d000a6015400105080051a0003000d95051200064404a0620466050290004100c000c0241214100c45219004010f4402009800401a015128803038421220240b51240071407245000e00c0fa4a000c1c5101c5001503052a413424019030741040050015240301010516030903190404200900500c480c503a005a100d514099000d8415007000501d604448401c4542e08001da20790800701505e9042c03040e40140e5511101c0042c1c5030b12105406c0070f03005503800000c04c024012010001d0541000c01c0e4200c941550b2498600382648054041c0108070442d0307102d042100f8030706908055602c6004050802000b03941e075803c0d40700d402265032004841d9456440305c2044036014000d40711848518009041c0c1d55000b050899221300c0001d00a0b0700c600f5a101090300030791000360544809584c0040c0ca1080220300d06400302c0c1701c1e08410800ca900c640440c041c2c140885c1c0040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57014391 1106 57013285 57013289
    0x110d03030b090a0501030201050a032016021005030103150506040f0e1b0906012a1703090d030603111e03191406010b09090a060b0301060e0415 63
    0x10080c4001201c2c02068400a00d16100040001d070342c0080c115400c1c0d010300d28001036600901480d00703400f40444c1d03400040112011454210401c070641007010810f000701d460341046c81034010308075001e1200740030040008240b017421241c03099464101a030882c600a0001c00c01c100c00700815011150442c2c503507005680044248085405411650007840d1405da0700c0294601c0c003600064202c005d400d40508800003500600c0362203441a10030066408e0340840403c00c80c800382d41120303600740c00689900c00759004000e03c8030809406841020126940030b101500a52000410003440040b0491084c1001d440012420042e46d0b00344440ea1001c6002054401c40a0341c1c1c0c10030380d4082009060103542684560b005200c1c4004250a0310840c42044800c41c3c0c680d951118004040c116541c00b5101075540800041070090700880a24807d00c015102009030b03080004001d8030101041c = true := by decide +kernel

theorem cover : BRFrame.Cov 56834535 57014391 := by
  have h0 := BRFrame.cov_init 56834535
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 56834535 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 56834535 ≤ n) (h2 : n < 57014391) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
