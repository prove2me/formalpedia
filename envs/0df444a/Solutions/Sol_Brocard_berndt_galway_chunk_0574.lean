-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0574
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:31:13.132497+00:00
-- url     : https://prove2.me/submissions/9e911285-92a1-4000-9bcd-79b204dbd757

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103057553 ≤ n < 103237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103058803 1250 103057553 103057567
    0x70216080f010605041b0819060902090102060702011a06130f030f120305040f0f030309060903030b10090f0b0f13030b071b02030d0311090d05060708010e09070915030602 75
    0x30004040140000220090040a5441040104441202100100c0340c01c102d603200203028403601c00b41d94080196110102202408081601194100d4102a41d101e60028807980c0b02d40e010003242e6405070b000e1000340600003407400140740304002d000c1401d0142030042020f03100c2040200d4500302410b120030b408040326035642400701e03400c450345005980c0040174900443c001407090003a071740318a0300101c40c0a001e83c4140d0741c0411007103180c1e00942c1015610b9400f000014943d01407103440c24001c3e6004034600c0e100348100004400018445014025403002c200610301041c080c11084405c0c02813055258142070b0048201445807036111050b0405100780032040020004285014500590f1801c2c0e4030680c5000c40368058600c5900030f98154080f0b4908580720b8030036008081c1144009420314100801c680224441012817103040f601a0855402c0000342584807500a004100480d4150500c1c01d107080519150703105802002a02c9840d20045001c0440071003050000350381c0b2030411035803208 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103060053 1250 103058803 103058819
    0x5040908031608010819030c0203060a090b0105030c0f0d02030c0d0308100b030c1e0409140411010e0a12110607050f0f0309100305060d0503040b0301030b070c1703070216 75
    0x100440300081038094024151075868800c101d41410f031782a01000b8040103036401286a00d00c5003410b000c078108880001d0b0280140c40c144403003400395500f00000309610b000751524850814058202c0f41c000c0d13020340c45644c40f65071103404000002406651810140100e030000ca8107002d007409440e41c101d210004040c0070154015540c5201d13055142c109485151101080303020b03840140c0e0301100181051001c0e00c112601441007012003020380c4821444c01e907035100008152410044018a444500c00401c828801089100c4004020928280312541041e8000540c80295809a100182c01c43e03000c01042003820343c2400300c0c42030010501f60f1200214584503580b03258607005c0713803082d0041010305203a80308000103442211600410104001000d071908070020700c001051940d1105c0082c5d0f0130000314805000070009080042002035496045003030041400b1700c054801010000764280311400325161440b500e201c0030030310b0f208903a25212084128581001c2400c40900d0405242001800c2c5d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103061303 1250 103060053 103060057
    0xb0d050d08010911071b0f080a0b090a210201090203010207060506100e28030204020a030204081e07350606030f0102031b0912010507090e0a090c060503070905040908 73
    0xc0e26569007005070f80351215001540c800190540c2c2050040c4100307000295903101d040302c3d8280504240044650300c030030394900c100c120b40c0007000c42e4001b03214450500c00d8206495070310082d80401040c14107580d56038403031703000da412103541c0714603207602c00100443d8401e4000075007464005000b59180d00403400d21400501c010745007184034983c1e41d43d07007000c0d050081c0340c0c01140304001002810b2001c0c0c0d484803141c50755600030b04001302003079020001c030041e40c03544040e000b03890352943c0061311a400d040640385015045810f07070154103408171000c0c0402d4400600902543c041d0900c81c40c1002880500c0c184001c05401d41050b084281824403944100010f4100e03c03801e412002c551031510204515405c1348420340b140840000340c40074075010000d1714002400444c0018110903090603041c0f900e14211352050380c6000019040403410481e04180f42d5240740c000640031400c000d81c1c000f556440c513601059129941c1800004800290414041d041100c01400d000d1b000780301c82d1440385450480f039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103062553 1250 103061303 103061323
    0x130c050c1212070c020904020907030915060f1703040b1e07060e060a090c150c1406190c020a060906020903030705070306180302060c0706020403060219030b040209030c0607060b0d05 80
    0x501d080c2d030300258849114040790f904c0c10307401811032071050303d45400748840410010301000c01d2644901e00b03800000c003a007a45078003595a544000a41500b040d0f0030780c60354103455110744d48032a504042c0c2c903c2032502200321012075079101655071b500d05050031105504c158100d02ca00e0040c0021902d441442016002124001d5480c07060718416510040369204450000b54040c00d0382203400c0040c03012440980c1450340c50f4000e402d007825110072595030380c00000f048000803030054201e034041c85004211a13902061480c0036400500c0012540e9500035607800c0c40400142003181c99100f8074092201d20341c129120ba91025060366502e46050400603660155440120f4500b441d02a2510301040d407003050880c000d1703150b405440980c55002d1808013a420942e4181c41843e030802002000644500c024500035041d090320115440207144003804481e00e05a08502a03401007020307051907075021581d04032038001218896260348803420042e00503c001032069070091001c00e03003001800400101c1d1011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103063803 1250 103062553 103062577
    0x5210a0207140304180e0c04181407030f24020a020307020307050a14090901020906040f080609061009091401050a0204170a020108070c0609231605130c050c12 70
    0x21000140c00443d664400d9205604641c0d142c080b00044104c4030390812002e040780d55003103400c2003420038005000c80702001c807414601b1001040f20130400c0f1050b200d181c2c04150282c060030486141d03403030794101e803402c1001c02032601905004444180845110780d4003600e040503411915184c030901c002c0c0d985e91181c40e043e4820f203d003880000340d914149030b5003401c0da00a6940340c24801c03206424440210030107420702c1c1c203654081c0075011340781e180d01001e003005094804480c0740382071600b266682042e40140801506411950410000c0d055101104040380c2018000144204041c10080303040e0f0100b4000e94929424402800002e01c4c0b19005403040d40e5002c006402604c8800382102e5641c1c100110080c04a25a000064070580c081e51540c07489500403140410f5000c1d480d5500e0b2a441965a21010503100801c07401b5034040040205800001a41c40312150f1309080200007481098150f605206d1180c0780c200c4010290b202e01c09a17800b01c00924111645c404c42e41c0c1d180702c060f400c1041c404078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103065053 1250 103063803 103063823
    0x3090a050607050a02011d03090411070f05010204150806030601051908070e0702010b0105190c08040b070b01080f031201050f030106181b140703080c09120a0204200a05210a0207 78
    0x92420000c500400f0b1f04110000154034119014052002400c00714441101d40d0405000300710215008401c60300c03855100e0000141e45900b012121101a0038200c030440070041807404025003514001101e03415980111080c04603803a1040c0c0007000008180c0000d5280e0040300000140310082282e00d50286001d5002402005804001110a8005c50b40380e00c1c0c004005040c1d020b61a0b000b0880481600d009042c01c0386840d07105c8041911030303489400100d40d90b41d0315600400c28680d0503c041d034402803408016514080580c8840d00c03065a060046a120302c2c2200c0c0b00c05042d076002d501080007050a204040c10504242d40002d0040050301904030707490440703040341210341e40301d000d540b4a40c21800d000c89003000d90685040322445001000c1030400d01c01041408801e650305901c0280d940c0b00c80e0024030591107144188029200d580b0030b408038460000d00d0040705c60810000355080300046182007925031601c1b80c20429184903c506003d2100507a100f8455880d240ea0000c0c81c02c1d074090442c3c81 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103066303 1250 103065053 103065071
    0x1520090906030d050a0509030102040306020c030702090f061008060301090c0f140d0305180a05090c04171209011d0927060601020309040c031407050c0d030c020607030203090a050607050a0201 84
    0xd0b0f00d4103410380c400e00000e542000654505800760000d0300c40118040d000500f403035166683e8204980c00168214641e43c008503070312003189042c051a0781d00c00d03030402c80b4440c581040340200e0701e001c4c046100d01060107110320005110f600c00354401019903421001425600380d03200c01c80309001c07070503019040c002c04207001800f0203410000540900301d070381513440b80d141007880018441a0316165840300d5020380298030000b2560b0b104081b450007215080402ea07a600c1c0341021402089a46030001000c0760040c0c191506480c09070400d58091107800e0803d051590300c071001500340305203007502c502d44c080070780b000f44514442c00c824a850085440105e01001016540000b03640384400c43c0d8107401680100300c2449141030039000007031407100c5800d01188110700b0048414942c081140d031000003a42c040303940a200c1c0000c0000c3d04803001d0030b090802030307411070b158001d45458004001c0e90915400001248415030204010204d103a0041d003034800901701142c1c000d00650006143c20019820002c9203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103067553 1250 103066303 103066309
    0xc1e0307120b060d030c0203010f0507020c010912030309020625060e0c0d171314010905090103110405150310050703051f030b041a070c02010305100608041520090906 73
    0x100003401c0e0800394200560380c0d400f08000b100070310b00501320104030307000b244400162002d0080400d2400d50a0000c6001c0ca484180286002031150905040200ea070204100701002e41c00e9034000e040d00742c60701142008250000c25041e104480040042060441e40c3c9d00340b180c19545c4c0c8841c101e1044000780004205414595681c8400c203041d00e17403000445161400040941590820b25024105000c0c14080c282c403071403a051015a00040341102092144a510b41c0d0160788079004e00801c6a840340c0c40d5056845a450010410200c0d5000e1079441d4081040d2495015450030524001000c8441811502e200100541001c1c1d85040205e401d000c045446d842400d0b04038480c0d60000c06102c00d4151858031500c04010000c0e200b40e4240b640ca8800404000b844600c59108803031503210340c038007215107100041c110b810083c0b100c20340005010080c0021580803400b581c010342c000015019080103047e181001302503440c017041f504140c4078203600c0c3c001c2a4001401490070122440b100581d907002c18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103068803 1250 103067553 103067579
    0x9020a0e0105040e0f09160608010e0f010b030a0b1309060b010908010501080307080f0c0115150302030f04020d02010e06160515010503060403050313020a1206200412050c1e0307 78
    0x30301c901c40110800003140c5148017030b581544020090201c03019400161413076552201543c120100003121400140104d0010f060b5454000201c4200c04400d0343c50903802003600e00001d000c00701807944a02640d041c030380e141000000301c1e80a01400700951049894018010219030001c2400f003002d2032000102c1501c1803054034105c404c0c0c8405549090801e41d01c444050f40900011034403440140210310300607909114403c01203480b90b00c4003001500380041200e446403101c1c2450109070041041214090507000341d00e82150341902d20342c481422602c0162080007071703020200e40250001c02c03072810070039400c04100e003614002e10554900039140c11020103292024020550144c0c070100110740020b00c28001990710a030704100309101032029500090140d1003961101c80d02e030501d9041c0c1c0080c030406100700307180300c00e01940381c040f0140c404980d24014011031288503000c01c04401c441c0c4c01e0100501a25514580040542d9900c084003850080045958990203010307210708840410900200b0349 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103070053 1250 103068803 103068809
    0xe010b0105040b130f080c1507030f080720010218030a020307050613030c030615050907020a02130b030f0708011404031407170c060a0c090e0f180709020a0e010504 72
    0x995540b5003414408519030035806003050b150403004914000941c540520700d07800291544a01074034070354440342d0401c0059407289250940c03244081148900086d0050200c1c811b0024600705030340390307603540e6506a80710382c3da11466404440e0f240c0a04000e0000640c0102080c0d010380940c03045048403070b400e165035002e074001300a4041e48400000c2c090352034030708050f000c0c50f800180d030050301c1a2646d0340c0d140002c078158405c481d2107880d00902d0100b80090300200000d0315064801c01954642040300a507521480351000e401030704d8010000020714a1030b00290086000030f400c035881c0c9c0d0010458103688da4458030805496501c4d24201030741d04a202c3c8880f40c003ca42507510890a000407502d840b82903480824121210102400a0403451500c01d0161000700ca070b00c00030300a40d1418981500541e00950f80e60b804102c0c040b0400d20101d10b464102c43d800c03600c15511030031140e5403448007286080501000803400e01c180e550005242d1400c0d0010114685266982c2000044110055a603030050340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103071303 1250 103070053 103070057
    0x60201020a0207180b0d20040212240a0f090c0302030108070303030c05040509070e09010e09100216020312071406070e100c0c080705010215070e0108070e0405010b0306040e010b01 79
    0x80000c20512400c65091842d20131001e9000504100c13420010306000d50426040f02d440446010a012482441000c0440303a030080e1001d5240c105813240c1c0102c0301c480141039650114000e03460a058100216051490f80e80180c8034104203600c818082d810303003140c0c0c451741c40d0450070200b546000a1180c02543d04032402c01006040c42821581c1c1a80035100c0030320b00c2c504001b814130000409681c0e0503140e9000d2440c546a082d201d00800c0140004110305070001034205480b02e0504c43e1407003000071a040c030308220900041e120480126058020805035801070340c17501c940d4884503104050400285100f44c8075100c612850800006490b8903030004445480100310140100812400d100380e40441414151038051990206641c8080c040e1009810030b108a40c442c0c2e10a02c21540c04015100c0341d510340c09024109441c080300004c0242c3c004849040c100568040401c0c0c41c540101c0e140d208032407008005002560310340b80360400540045403403078400d600780820154051818400e01440440c10307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103072553 1250 103071303 103071313
    0x309060606110c0a1a0a050f0d0b040b0901050a05011809020408060609070201050702060402100e0909030406031406061e1209010c0e010c0506010e09030714030901080718150e0303030907030b01060201020a02 91
    0x80b0344200d503030b040011106d05202080203000400b0710054010282201d19010000b061681c8400303000807202150340042c062080d903130051103503544c0c01c444007046032024a071602c841800c00a000b0741344003050340041d8507940003040205020b080803c616120388416514600c090b503030514103d090301c0066a00c2800b5800800c08100513007020100d120b0103103218142186000b2448021518940040f2050103481d00086010f1040036450f0003034200300c03004480044601c3c103020740011503e10602250130216180d040d4182031285118040e210740c50812071111a1602e4401e003124040d014100500c4009038900b0f01c03c032107660280c880785007141e811000500a907800d10080e011560313005442000c0710700c018000400040c3c5100e5107110603c0c01d00f0301460f144c03540040098400300000d060034041c0045035581d40c6982180707003103603401c50b080e1207106105844242c03c25220150106203158250200108000d80740380300180074011244030f40f070141026aa5464100e00701d011300c4030500c0040e000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103073803 1250 103072553 103072589
    0x7080102070b060f060f04060c03091e0303030e0c06040512160315060506180909010615020f0c2d010302070606031a0606030705070b061507030f020106060c02090f070309060606110c0a 81
    0x480c1c0d09d05004180710f8103100c07152a89501003485401058082d004a030444004240101680341c014603a11a072020000d0092184070000281540103038014540500b6041d1500c403001d08040181b003042441d065803030a01d0b10344901f0030400c181c4071100c14440c42070030600d00140340d041003000c0b18519061f52001581c481c480404002400602901c01c404542d207070a0041500c0c1300c0800c03940c0d943c0c0503940003400981e6040c0b10050404840c030105612030011101d0180064440441004202c29400250760b02c81c01d41c000103038001e01407100050481850000040104181c05100d9a404d142c03c0c500300065640790001c200701407100301c2c1c00c10005074090012400088410f46e451f6013019000340703488000700000340804407607008035034143c0025200d11102c602254080c40703100040c1883d40303402c03500d014a540200b8040311001e00311400381380141001400080c40b990180e03034075035030000e4244070095403480300900031100f10f01680301501804c0c500c0c004919101c050501100c2400c1d8401246400e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103075053 1250 103073803 103073807
    0x515060a050d170309031c06060c030503040606080d0306060e0f1c080903030a0302030f0108120708220e060a050913020108040305073302030717060307080102070b060f060f0406 78
    0x400c0348000c4403400302c0f008110300c003160030303001961251001d980156180c13405d0402d4410324031007071042044d6803031901806110703c0d035025000300a40794240c01c06564036101c0c0d150020080486030701069044c01100c0d4400308195041e000002100d43e03550350310105002c14008c00907000c29141000ea8060604030554040c2441003c4440d00070340212200360401ca00600445c1c29580150f41950000358008100a081600015400d02500060000b0201c0b54110b040701d00071440740a40180481ea004903000c1124056015079640300140b50082945460340c510091b60b0280c02501c0d81741c446c44461201194a0030940c00e074034400c0b614072880410501c003d0b0019140000080c1c4264200201003001c00d010074150701c22142000c0c070502d030500040c00d2a4142c100154481c1c0001c00312380d4010414445e4040e4415002510070058031250109070700c415000a10f45031081d80010340650001c20708009000301c0713400701c511a110a0310104030010b603281c10400f551044c5420038614040910040c1b1100f8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103076303 1250 103075053 103075069
    0xb010f0f020106090f0f1409100504060b06070303050702070816230d05060103110d030807030b0f040e030306042d0207080f0f03150303040609140301020d05070c0515060a05 76
    0x24035103000008007a5283c00510094030345411040035010707210004503900545502c516102c240c4038091042d10360030304c4641a900c41d8a618102c081158030f0f0030200d81030000d1581f02c1900400b005201c20381e150680d02c0e0140c00f0340001c0f9040710140c040e0740d60000c0d0f0a0f0000c01e031940c1c5501010110302006061540205108070210340c040351044211015103000e868540050321a076000e200180b07083d6145242524006030111106806003454400510019230000700c2960054114200490b100c104440071880d1426403e00190b0f0060601c8480d1b5055803001c8001d43c0900b905035420301030303280c01b00031a00f00c0a41508849440102100d24480391944507405403142c0d62096828500c0e2031000070000325190040c1c19543d0b2013080000030322849400c004d2400385102c05c00d41c080c0d82494a03215001e807000c042407244000141080f0070000a541c0c1c02c0d07040b110300e0000315400b00514148500000c0000150502c225410310032540d01c000d800c1020030680384a0400104060122820b00c0b040c001d403a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103077553 1250 103076303 103076327
    0x31107080610091e0c1211041d0601121109031207020102030307080c13030b090d0e13020c0a0507060801081509120c010f06030602130b0405060403060902030319051201090b010f 78
    0x80314804040c010504e00340c4c0500f070b916a0407a035404032408500c118800860f4600c08401c0c180080403c010030100000e009040f00c00d800c00032440c0c03c944e40d03030030050f289809440390902a2501e840400040e00c1d88241c00b80c098800c0030780440d0030050301c1d07078142502d030b102e0050082d0141e4010700020700118419200d19900800482d9041d0401300b00b400030a900380100c0d001226020640303004c004c0d0350325003040400b0380c0a2142c03a01e121451011408200003000d00413034401e07900d0b000200d00d034061004100d4000800d600108842100b40c0d104801040c04e00203014031703066030091000303528200c0c0c09440c201e0b000f2244480500031405180c4c001e07113899844132806808554a42c4251907010f4210b00c945001180540380141e41c41c0003001c104100d1340b80d140c20000c54400300b4031050065481c0c0005680980740d02030000684c190003400000d14602030340c01d032111480500030400ca02164008064a800b0b500b400ba080e90f1030b40c0350400b0718103948803014141d0004140c24038019045c2d03c10303080c000391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103078803 1250 103077553 103077581
    0xf05010b070f23030a120b0a050103050702030715090203010e0d020d0e012705040501080f03030c031005060d1b0903020102150612010c020615060c1005040602130303110708061009 79
    0x1500c0a0030200c0314045448183c24000c5030004504603d10b0754000b51400031220000ca02080021110030016040c90890b014281c10142e40b80c0010352000d0080084074441504072000d803500c1106070003e4400780814580480c020350030442e00384c0211900180181c5035504503000742c043c1c08010304080301c084402c01035090400683e200ba009450410150b1815011708100001a90a080c42e0a101c182c98069005da4101e030311160450006960200549030044040c0b400e0f15640d03122103421100d05400c03500241d601241c0094203d00f64845035112280c51010301e42100c1a11807401d00039600c444841c880030340540c00004544040c89160320090758441e20050190001c010b660540c42c2c00c4905e4003044c10090383c4480d0074007845594043c43c0714600081128500c1c90030720345001c0103407101d2162000008050301d42d0003007000c221a86e0150741c10301c0c6041c00e2002c00300f40e880c100100110b40c2109581d0203400b0340c0402184005020507114407483c4003810410040e8a005024001040000341d6003407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103080053 1250 103078803 103078823
    0x11a060f040b2b2c07062304080d02010c0311120406090605131b03080906030a0605090c0a08090109050c010509030102040e010305030703090e01050a05010c1b180f05010b070f 77
    0x400c0d5001d5070f1041e04072001004000410102c44100e6281001400d0501403010400607002c040b00380c00060340714291001440d00d84c186000c0e1b41ca45403003440c056000e140c1a01000304e40070a46480000b0b40007c03220b0700340c0c024080940003c0007075040b10214800c444045c081000200000e013410f88205070094130540c80015141a0358039400200c0e10107503086900205100403e40034810310305449113459943c10509103c044ca103580749044c0388200d004003405200040700240802c0d04a500c514010040a86403144034613115003501d8455200808410200e02154080b42c0c54040c14403413500203a43c0311008040c1c090b4a080152903d030010001a58559001c000118001215040c018001c1d44200000c54560041e41340103040c0c8981d0740c1003400e02d450b00200410580d641c208000c0c08403002030a105c1107400ca40d04210f0500380e02c5a0b190303003d416040300001103204010706c400041c0d2960240c2007000d82000280300b4151307007081c426110011030520499000c1480440802080c5101e480c0c804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103081303 1250 103080053 103080097
    0x70605030717090c040f1103040210180303020c10051201050415050409060b04050f09060103020105070c23010219020303040e100e0901050702150108030a030f021b011a060f040b 78
    0x42c99800701112440001c0e00888404c0c10141001d000741070030900715074800d02505000c4000e040190200400180c032038a070307400030350b51914024000c1000180d40704a02100050312030401035912000039803164024903115101c015442d10030810f4426000c0200301c2040c4907460b140400024210b5a521001d40c81c031201c2d400181c41c1d076988650085644280800f040c184c1d030400410044450003420845c50b94001400c11508040c0442d0341410b403942420120b880c1c240758285030341d20164603003002d600b1101ca441030b2034940ca42c1010b07070a500ca600742d0803580e488001021040000002c810000d40551050005100109900c401182d01c10b20b21707010120310030f54034002022036200a5a01d10b01c565511405d02039100c0d070610401503c80c0e0312011503075040d4548a1034965a00c01d49522100b016075031100d003000450340b0340491303443c221802207880c00100351646850080400302001e880f40301240d03070145068107080c025100111031220040d81054580140b031140d940c0150407002e048000103182e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103082553 1250 103081303 103081337
    0x1290d0b1207060c0c050904020d060504030c022e05180f1306060c0b0f010b0f09010c02220e0c01020d05133201090b090402090102070803030705030421020706050307 73
    0x4a0000c00341551000d0000055080c07801d410250f031b401290040510508210160302c41700c8543c041542d209000042a0340e860030708403008200c50000030340c0007102d0700d04404180c03100f000c0f1845514060103800403106007200280e900780715004c8040080800044103180d94a40039078050b10340d1901428902c5043c0c14811154110380030354000d0b502082d1905004020301140542c0c203a4444e0f102c3e403184445504050814005024034503c1110310034000590b041c583e4841c5081c4007000c2d6010303251042680c2814001040e0883c0d8207411003400e440c0a1075120140e034001109140004103130054480f450b20f9010442e04c0c2e50142d09120b80c112011600000d03815040009180540c041d440400344406c41c4800300d102c551160880d4904004441d81c0501440d005401201e24a4408540043e5142c0781c050041c0d04080e1154054802400088100100190000021807140b0b115449a0603140078040b4483c944447d0f040b408401079011070810b0005d0380c010001140c100c9100d040910b6240c80e94011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103083803 1250 103082553 103082563
    0x50f060d150e1e16110609011d010b1e01090803030c07030f0c0201020705061806030108030a0e03120d0c0e04020c1e03040303050d0906180b01290d0b12 67
    0x24aa03001a091904008107561000d0880d000f4950b0f242444100b40c001c0502d100d501c2c0040e003c5110008104180d40c0c0d40342c09904100c0b284002c41c41500c00c2441c02c04140380c02010200032242c08108264203050008106100e180c031118801800c102043c04a00c04800105c1e40c858016818403108101c042000d07102040518400d52070508415514101803400502d40602480c01005102880f00034500503a004551001a00d5042d47c10b2034a407007071000e80c80f412241c8400103a400040000020031410301c08001130551141503110742003135040f0704c1c050540e200d211603050749810b00f06201c030341106000c40d008061130011600d80712140e2910100040c049038050f04004c6101c0d80101d560182c1c15440b0011850401129000355040c9403075a200500380b403066280e0071000b1640c403034000d030420040d83d00c1482000c40022852240036103515000c2318002080c0a24001c001c041c0c182180b43c0e030210222195a0000f681060b428864510301060103440680d001560001c43d16030a003a5044041103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103085053 1250 103083803 103083821
    0x60902060c07030c0602070509090c040b03100e03090a051c03030c0c060c0804050f030309100e03040306050103030914040627060e0702010903090b0702062203080706020c0d030e0601050f060d 84
    0x1e44da040c45031500d4400792500c84d0742e81c4014024181071080005854000c00c108546400541d030202e0224070794000070b42441c00c11800c0a640742d14000d00454030320000806404d201000307071004d4664548850401c41c4000504031400c030195410840f5100181c4a030b0458906e22400307040c8582c1d20491a59214140c40e103107410000010f0400b8100800c2c000c041200107000d01c41c0c007014610310b0500132001916040c00d0b0303810400300c035261070a042003a5000c00c200c5000b0f54000000300010751316458018030310503051062505203041894450a1458144185401c136952105c5032044109031403850001e200b800450301403610381d152800550b881403180040c2c8200071580c00003440300840d01d005044401680c200b0001000e09000701e40051b120002142c0e80b83e81758518039601031680e400d2900c000304094200512681c400f081d4031081002c50f030003404101c020071043e1580d852042008130210360b410f10b04e15a5584c84000100071600f031400c40c54008400117445d0f14940030040700031605503404a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103086303 1250 103085053 103085063
    0x2060708030610030501140d0f060f05010f0e06012a14010b011b020a030201030914030a050d050603160b0a110307142104032018070810050607060902060c0703 70
    0x1c01c000d0b1910b08903540601140507070070208129410aa28201d2440240400500070f28800c0c192805104000c0d62641034260302041c00c0c019086002c1e0840050f000038454403d40c000d45400215401c81d054100310300c1440180d48848400d4444001034042c081440c0041c80b003120304001c4030010861041c1c0c403089101d1800008030350700000390001010f03001540c10010703206024110010040c3c2e07600c0c1244044913024600495601e002c1d08001805060723111071800c140c4000900305000c681c120000e00086100c5000802055640506054480450009401410850b10000c1c003034003074110f010301031300e02280c0b8054100703035103c1c1e40e154910b900582c02550f189071150603110140000b00300c0e00051650268080c84641c0b44191107030314038003032408010501803011107251102542284c4101d40050002c10f0341200302d440416410019034241c40e803000041c40400019124407686440c902259400360000f03241010a445481c028104010100d0313000b48200001c02c940c180070020710024600031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103087553 1250 103086303 103086307
    0x8060604082505100c020405040302010605090907081e0307140309040207081201060512070f021c1205070305190f0617030406020c030616080405070e010b090a050d08030601140702060708 82
    0x5080560900300140e105901c2041c0280504060540c0503204104176641980c0104168444c4d00c0e0680c05046c0603040241c10400040030480c500c0300000b481800c1b940254141c8004001c1400307030004021054804400c2580104070000c000b6801200526241030380109480c10102c0302c1c40024283d03031010724151000310011a00081900b0138849107401404a42001c0385003906803541070100ca0300c0140b00e00240015040740c400d0141c001e1003800401c00f1a0b240c8248080074000010300658802011001580e19110000305014020b110340340c05591506404c0c001440c000107840c015002d204e01c00c0c900e10f900c136000003a000305d504000a140c1091400516210f42c14450000d241c0ba00b00140244240d028005101400c004944a81d103070909600e8900a25038540c185240303003005079400411401400d200005401900c0009030041c15000c6440012860313468040080318450910040c0008504101180007580a440c1c90040144035400044c10700203070383c00290144c1c20808051b142c038200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103088803 1250 103087553 103087603
    0x50d030605120303060a1e08010501030317060d0201090b180a080a0203060a18060b0102010216050102040603060501050304080a030c09080a03021513050c04020c0109080c010903140406020303070806060408 90
    0x482c1201c0031110741244001d42c214500b07507002a17500348491140700c031341101641c50103164043d24440d09001d00b80c101c000f401380e940e4a10303008290300703c030029980c02d041c00000423480c2c0f0f141c04107505038015016940d40c100d250a28031300383d045600120a03148045062001d40324942c0700d09403c4c90041c003540d0060a4041c1c254018541800b100501240301d4904d081030b41003101500031f10460555070070450029071103c2c0140103034024032071003082c00069002041d08100300641500140240c0d452558107000c00c40e910340055401e07000503a8000e12201040c05240c2e1407130302c603900c950894165443e040c018665506c41480c2000d100c5402900140c2000300304074011460f0f030140c190480c4481102a820042e2616100d48910800c0c40340c81c8208d4000803426a14202500411800c5030092809641c4010303200340385000b03040c81c5c10110007042000141004400c124010f850031243c458006d9803665840300b4089070b0a07400284070940c0000c0030300c804501c11800700700d03102c42807030058451800000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103090053 1250 103088803 103088809
    0x5010509070512120a140c1f0b01031404020d0303060e0c03040501060b070312050603010209060c100b06091305060a0b0c01020a0201060906050303040e2d0412080f180109050d030605 80
    0x202c10600d00c0705a40c45465103104074150501215202516498959101140c07990082000d1207583d0103d5040d100f01009400ca5000c104540180200040c0003008880c078527200550956800504089295121100280160030a400020a103a1203403400140c910f0315800180c6c4440c40680da661030184d4044100f0041010911402015040c908082410480c540e58020240c154411951a49a440344c0101d10300307450035016291603400052140d40c0316090700c0386a81d59204487c01c8032001d2414143c105845062150442d10011b801609410f240c80c3c3c1c6804910103080c02800003130f080a0700000009060b1040b1016062010034000090b9a42100d114000d0a48000e80c203c00b82042ca410b00800181d03800000700c40856150208507a039582c1d500d50ba505c0050314404801035070f500c101908108501104282030300c10b0b40316048404006802d00320031192810112502101c2ca801c40c404111880320040200c2c10100c911000481c450b81d85644103421700120303108007404a40c440c241408686 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103091303 1250 103090053 103090069
    0x9060601020703020904080c070e070c2105121e0a061d070801091814062202030a02010c02030a0507090507020d020a0503160c0e0405060105040f0510061407050105090705 75
    0x91024401000d1803810354000503551000500300070801c100c00944800003500078088103005162240f01c10390685440350016201881c981d50446022190940d050701c0d010f502002c2d0380800c0060394416050032000d40d00c0030408038020700b1125074000c420420040484094115910588079843c0226001c0e143c505260080050010300c81c00030545041000500ca80c401e40343e5045400c2c401d00891401104480140e0521103c01c01a2001a0540301d07040031040c001607081c020451000c0400c000120f0001c0100c0e011601d2000940c503030040a40e135000341d0b20a0704c09a03101c900040c19542c2640840c2e440c0c51500600341c1c40b040d4001d8940041040c5160148201610404240058096640103680e0142c40c0e124000120042e8060080144184034074403c110b00505031040c007558030ba04203410a955078000901c00d40740305509110340c0e02c0b00e4940c83d0150798081d003030000a041c5241d007455010380d00200c103c0d105100e4101c06101c8800440e50034054280100c03141d1028118550820003809008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103092553 1250 103091303 103091311
    0xf0d0306050a05030a0b040816020310060305070e07020705010c060209040504050601030b0606090d0b0408120a0501051e13050a020d0603080c010b01030204261608031c1b0318080a080906 82
    0xd4100c0015171020541d0490002e038815440b065031a40c40400b11440c2c6100c01c002100650184260411002c456149508c20310a0303034090021a00340c59650b4200b000e146100701c801d08010b07044a84104842c0d40280d501030071041c4130304005810000800c01040880390126070540702680058010010301a082102e140c2294040d00c400b46007690000200d0f04415101000415000c50000003406104503007041e00e40c00d04000544074440c2c2032a00f48880586428041c45114050000940724604010343d08001e08440140526031100a104070910080c640148040c00168007007142d08900c1c05603101b02c001451186030407948800040c1841d901710b0b445a03000741c0c141841048144005420800256106102100c45007410b5480c407480070304098500c03640c145039025000003c15040004030107002c96000c800b2040c003900f10a064000143e416042001e458000312002e2200118802d0300070504c1c0540c4c406414075200c03060794846980364406115503000851400500a107200e062000ba500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103093803 1250 103092553 103092559
    0x3030b0303030c04051203090402070302061015211508250e061c02030d0309050d0804030806040e011407050301030b0a0501080c0607060f06060906021203090d110f0d0306050a05 78
    0x3140341003410200f59105a010b41803113002c2c4000c2d100302800c1e0400c1203420313800f0003078010340d103e16061401965a0f08103440d1072508488645003c5200c001101c03040c1107100316a17840d000c1190080d10040c9c4918140682c0548654480c0900d00034003025400300801130050703000510300b08a1070044980304051a030200e4240e108004010007030300c6580341c0300c2c80c1c100074212080d440611155580a04501140c02c0c020b40500484601c041c0030b0750554810381c441030040c420346480c00034000c01165070f95012200100800c0c3c8020101e01982020703803000002c040903a00021301d42082d001d0028002c030045880000182d00040140108008a01480d070484030300002440740c0e506002c1d50f2911380300310700c00403805220702051030330501c8000d41040f288036030030b150b003081019255980103001e0643c901800c0b015108268a901d2802c128004581c814111103001e40702d003061070401101c2e8100d81c1e61404081e0300c120040100811018002401c0e0601e8984000816a2800f002d005405149a2140344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103095053 1250 103093803 103093807
    0xa0506091c09121128090609020a020d1b05030705010b030723090601200109020301151d0c0f0301060302041d0906040f02040e150f0a050702100f11070f03030b0303 72
    0x70450003403600083c030b81c0d03c5a10302414003042d601242002c2c407142d917000040e000c1c00c101120f40c0403101112000b0b40d54804000e100594555040600fa44140514100181e00c05808621304600c0b603c0d140340c0c840642d001d00f441c21000c50315490b295030000042940c00341d64500c4208410b150070480d02c0024050030440e41041d1225044070b501884030400102d00400d06c00c0002000e0303a20480c49044a03038420400f00440c40c1c2d001c0f240b58003d20030480128020340c80d010b1900055001403207814204c5580300a03c14100009003148185208040d141c900b1141041c010494240c00d11400f542c040c02891740c006864500e05001942d01250320300e9103412175501103003031159419001c210b05600c9500001100b500107800e101280c014003801da2100c00034021408070200c10a10801e4860042d0744250200c2d10b55154160380d0021a6020b44490300941e2100060300d084000e19008a01003035a0382c01c0008101143d04c12000440c1c4c4200000c845800c02242d0342400c244e05032140c11240b1383c0030340081d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103096303 1250 103095053 103095059
    0x4050105180a02090f1c03020d0513090f090c0611100203070f050901021002041e0b13150309020315040203011a06030105060714070905040510050f180a0506091c09 72
    0x7400e2040203454922140d4001505040a8a908803080c00540003e802c42c154144800e511001c140310704803046005000b0f01403c03182d05446002134500c00002d4504002003e0320301007540000300383d40c031255010551111001c4000c9507102d05440c0040441e030301c5180e2a1003080b007403d0b08000f0740503822072a95105000344007034a0391080700c640c2065800d040a41d5100c00f40b40c01030b4a041d6a12401d180340600008002c00d1480710801400c403028940200c6903207594a805442d800b600514041c40e0384041141001c0151003002102c07802c80c03105900b00040c1005c031640110b82001404216580b120800500b84004c5040900c11145600c0c5d0303401d040541c2585503000912584410b00c80e40d40304140210300641802401c4080b1a01c1440000c00c441145560341004406080121070581d010300440300103403904c0306107000e0940300314410320321111700b076403291104105001505040b01d000d1149103d40d100181003001000c0c01040720740000e1850010101110394107000042902080010240f010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103097553 1250 103096303 103096339
    0x22170d0206072604030c020a03120f020708060f07140a091503020304030e060a030608010e0703020f0102030a0c0219090e0f010f060302210c030307110108011202130504080906070303060504050105 86
    0x70000b0003d182c10107020a403940c0c1011100ca915074180a5441000707890000100300841c03e085403080001d0f128800c400303140c400700707a0711440c00c1d00c035540003500900000b540448154000c50340c0200036040c401040744a6402841c02c6801190240d0007007140184240309124004582d90302002c3c5501e01549140703000c1d6801040e032902125860300a000219a10003014000e03080f01c80a404440c0080101400c103c10150350f0f00030510003680034000000c034810145d4400b00071940303803094603194640711041540c20b000e08100d0380c54601c10001c038400d4000c03d50300f0060241e030001001c800002c10502004400413821503440014100d03081d0328220b02000140c8030702c0704030410307826091501500041148a403e0801c00e400720134270303490b010001301141042581c4500301c0140d082a078410b02d40fa81c849030317642e2800880c1c1001950141c003c031404211080750b500820760043c860f910050404441070045902030f0410142100403a40750f400920079424144540c500500c800c85206546058401827 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103098803 1250 103097553 103097597
    0x305070f050603160f020c0310050f0702030f0a120f0507030b0a080d0c020910030b0906040302060a06241e030b03010f090f0209070e06030f01090c020d0522170d020607 74
    0x40d84d4280030b10017440d42c01c000c0c000d21840e4103020003e002d0b15441d0b203040358400c0007000d0441303081440510000109070220310020568000e546204e0155140059501d820b07160900700c0400720900070b84450340790b0341425150280340d00400b41c649010031440c04150400107900e44c1904000c1055120000c4100265409826240700d0341c1c042d240c2004603154645801d1100c1e81c960809040340c031090060100102c400120b15118074003d60030b4446580780d510240e01600c186100e569000450102d1071242c050380c945124840404030b00308030b0400c02594140d043c0d008511080c00d404603035036400340001030400b03000c0c06101540da510f04104507212a5100b10602d405184040d00400d0000c00152445018601e00d5040c8035004044603128500011144010340b824018120b4450031300d14680303401ca0000408285164154449508100f0025460300e1940240b40440c3c14500c1d4101c0b0009141c0300680b10751110648420103014a80014078001c0e1070928042e007000c04001164a07240001644841 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103100053 1250 103098803 103098841
    0xf090c06030c09130204030309080f0706020d051605060f160c050d03090521030709080a2f0a0306060503070605071a040f1b050102010e070302010507060c03150305070f050603 77
    0x800c1920f45030014042a6445080501e5240407440090040203040c1c00c2165001280c55440c111950f240012542c16203458a91090b0b102580c4107450040146000c4c0c006012100300d8488107420030021a00c0b003a281c40030555014414040d20818494524104035085c072050000c1d04212400821550751a940e98503001140020103039201748030700400c102880110041c4203c2a104083c10701e9042c101d101a0b88181c0d2003101180242400041140010800304c00180e008004000c403000c880d43e40c00304139042101c121404003001c0501c40b50596464189070055401030a00142460610040c9894454981c100209200e01400060001880512071200310892001c6540140e104c9181c03001c94013044000040c000e040410f43e1020801000c3d2014089440076170090096080b03071f000540e11200039000180c00141d040002002144680d0010b1580041031f190018019001c22800c03805141a90422507407a00010020170142c510840c524000d070604603116843c44c00c21005661501e0f00ca00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 103101303 1250 103100053 103100071
    0x60812090102010612050309040506041406102601030c09050c032202100e15041202010309020a1a030712060f03030c030207090e10050a0908091519080f090c0603 71
    0xd240142a4402c0d000b8a0040280300d1680e0300d000b1003442d0580c3c0702d402c40c0c5113060141c0e280200040341e40c0307068003030310301c50311032141c00820140c5401c8240302c50000104a07440500010921031500700f9404103c4802402d14031030704503150350540c6840031410301c1c2ca902100032743d42440f050001380040071044903000388200741032113890b42445407d1241c400341d040001e544440b00341c11990245410440b01e40c2c80d5801242c080d5000140301c40801014029409901405114443c100d80194041c4e806100d809000411250020355030385041001080000c408040400001c01480410b5410030500c01c01c0034100c1cac00c14000942807605400e90034005101c0074080007103c161340c0003814000c0c0640d030060034141a05002c0140c01450441d44c80a01510f2019038900d0440010114041c0c3d00c82c0c68001c0780d00403400b07480d1a4a003002c03c00407196520100c0d40030441000555002500f82400501904042d210090039140011402c10200d100030b01c981d03180d8000f41648542c41d586e200841e0ba020b03010b9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 103102553 1250 103101303 103101307
    0x603230c0d2301031e03020c0d0503040906090e150108062d182e020c0709050f060f010f09090e03040902120901110f0703121b0305090f01060812 64
    0x44124200580070005a008070380050300b00e0601c40009184000d0705030f80c081c030171402043e4202191803914924070701003c0c0058204072154101450850088401c581c0100201c0f810a500e44607040704507105580b00420703003a518641e502c0110014001342010040b121044a00356141c07119154440c0c1c0002c2030742c0340301611421180d1580404000317420346400210110482c1e442c14620008a0280300d4031031400310310800d048098224500c4000414450613010003494015440384920040e410920344c1481c40c2c01400008107446202c0e10a09104502c0041a10707040c0c14064248403c1244014045041166130f600c00c4515039000300400c01250500340b40014042190882c09086014540000d030300ca03800082e1400002c0c174096441c0d0f000e1010341e0020801e080c60b50303141d108144503500b9501a030b9141400410007182c0620720f502e5144440b050081030b032420009500c400320301542d10a0010a0f81c0c9c00501c50001400c0000c2c0b480d62825a00800801e4100801c4a07035403c01c03040489140080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 103103803 1250 103102553 103102567
    0x30303110c0114100f050a14040204050d0323030105061204031b03081504150308030415110d050a0507090e0408090a06021c0f0c0201081b030903040603230c 69
    0x48100c1e250000890300070000e0301c20302402d00080321001d03a10031680e84916100480c8050b0703004d2214085500051500301c486192086541d031408039685c00d03a0f8020381c24000050f26840b58011480380701c0c400c1c2d882c8886105c03030001c2c0d00000e004036180b40010507020720051086440782c0d0104da03003201e43c403443c6800f01d51300c0b894100e4240c0c0300d9515041d00880c0b20340c065010542c0041e44980210301d1001850340070000d40080c4402c8400184682418038404002040480c101030300858015001c0c48013202240c06c1c0310141070a45000c0404a101c000d40040d4140342c49901e40f04035508002104c2c0d081c460b9003040c04004140b01003a010300a12415a100401c0070440000112400180c0207060340c28410b0b941c9030040c1d00c03242120031030081c91340b41501c003064840c0b0a4a580c58400019200e03a00d0750051074004407441c0c0c0000740003200300e1545803500011014aa40514480c510542c0111b070f5450400c030000f03090320811071001c00e055050040c50a4400d80b152900d5030700000103240c40380c55804c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 103105053 1250 103103803 103103831
    0x1030f060603141e0a0302300f0a0f021f0c03020904050a091e0507170309030a0507060314040206090121020d091202160b0a0e1201060e01081501030303 67
    0x29140c0e000902c4102807030f8007507928074004502007002e2400180080804580040c049803500d10b031500c01401604915180030071009800040228600c008641000c0c0a48015160389240d00601c8180c98041011903900c04403030b07202054030310300340c2c1c0791002d442840303542c98211190020300005c0c5003000ba2564203504210348298103480002c80b0041c010b102d41d0528448020003490782803810386610710000c030f004002c00041c00f014000ca0380e2103001030000610348041c0141c0034800361030002e1140070130446150640c1e000c21600051030700860290054078640341c00502100d201e00c2c001c0341001088010440965180c1095514500003070078000c4460b181014264010301c00051031007021440410030600b40e55256100140d094410004070480892804088ea6521032a28503ca515001c3c40341c14441443e404000d003c40340018141601c000b1640800a091004040c1901040760b548120800900010503103050050505201800094030083c03d9428030820500000e81416160251241581 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 103106303 1250 103105053 103105061
    0x23131d071202090415090501050907050f0706112107020a080d02090307050d050c0913080a141306030509010501050a080303040308060d14032109151e0c19050702060301030f06 77
    0xa10080040099440345c0346032280b20300300c034040d511030186468008161030400d040c25502031810ba85038141004a01e040000440d441044101c5071952960225900700388030034060840862030900b11517482184c1c2950020f0751070018688402c55105c200e020022420010440e002408940c80141e51000464003207860031380345d980140c4e00181c0c02a15003040c860042001c18842d40111a404100e8176054080780a4200021016001c1001003218181c0180140040700883c00d84103192400c04044440e00c000d000115802807011948904c1040007a543c28422280035290888080e85c03540d0400c0c501c0780d940c4c04024001014462070002141305076071040c000003450b5610010300c03481002c0301c4550700e071640c001c1c40043c810854200100030030100070714000740c411201000100326010a101d110812108044d081c1c54a10246054140c8906241c0f6090b600c21643c50403090703030306d01c0c0821210310446500360f44142042401c0c03007070714010703640c440440381100c0e00078112402d4880c081c20044014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 103107553 1250 103106303 103106317
    0x2042d061422060203071101080717060a0305010f060503070803030f0408030c04050a030804050301050a05010e0712090803010e071704080909070e090103060c11030903150723131d071202 82
    0x1414004400043c040d80c000010301080e0301c903403010120b24031228015142c04d0310980e0420046005103070100d003400080041594013a00003044070100340d03569204d842c01c44040c0d107403000c0000d840704402d102904081000c2c4c0000e1124600031482d5140c180b103400400c82014000030100d6030000041000000e45070b060b280540002000f850907640e0300e00d80701905a11500c95030f8040e5090000081139030030103104490488904903980300ca241e940c09400c850082a403258114446e80c0d0318600004614001c02031400780130031040c10912402d091001418444c030443d10100c0151b07421081100040c11101a01d0764100282d0301444107031500c02c020340360401851402a00154094000428854181c02c414054640c41c2c6070b0820381040b00007415142e100d2042da003178056000401c2e07086020301107580660b20841500d01481020380403421501510301c003410745c5805031000305103860001403c020040040c00c031202c4002105010003440030600100400c020107100400d0005030260601d03804440b58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 103108803 1250 103107553 103107607
    0xb1207020a08041e1e0306110f040306020405090f0709060c020a090e2b02060606090105040e04030c02040c170712020c07080610060f12020706060902042d0614 70
    0xf141d88660036a0040e01602d582044460301c420380018071100960400c0c080114029907510403141107031545005010b080d550962030386e0003040311610508020b00075002131881164050b0b0790b0791401c0100310303e445000d040e84100f4030440d8180030382c2c2c0350000030000440d006401e000c44600345500018080a460307510400c130305401c044403002c00d180045402030420204070740d0341c0c0e60a00b00c90302c01504503036048440009a400040030400c81d15004000d00340030081458040e150540300e400d88510001c040d50210003081c7c81814480c1107107403600498070304200d41d10381850440300c200d00c03101d04000003074103e41c24007052925028080d003142e011158008206d00c00c9410180e56062a9580c44104403060300b0621444000890840d100c1c1180c40401c01c016554424440d107041c1c4200003d605c1400100c0344d4a035104000603034180c290000d040281300b2400d0810b040a64001a10b021441016101749588400030050012540024846426880507948039880300340c444e00243c0030903040c20032450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 103110053 1250 103108803 103108807
    0x5070e012123030d1109100302030a0e0a03020f0c27040f0204020c071403120f210a02030403030b0f130207060f1104080d0e0a05120a170417070b1207020a08 69
    0x40b00c050000000c0c140420040c000300a540c205a84800c540d0282c01003640d8001c5029030145ca21600c82d80155410100c51580041e1001098000790314040d00c0c10390460240e00244e440c51460f03a428091019583c03825506208131003030294206a40480b0900f4500c1901220004241800041d000201c0c2086d8041c101f1540d0b5511004503030b0352444948100d40c8410041e210b489264100420859001d2070310f001c0c0c140c189809110224010b4001e65080030035107401c404191150580c1c0304001d0b000b0100a480180c3c0c9041500340203042d184c034055154054056100091495141c5d86240389105507600c0d40142c07969003e1510201030101d81c0102d0200c54100403a001e03100004400800446107a0f0782121b0881300110405c0d1a4810070084080e844001a0307010003807814500100741c2b0322034160050350704900481d698602403c41005880513000000b0600b40140510b410303002200784000001030094510b003501c580c0c4140b0400080643c02c15104011691280c0204182c80320035074040b04040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 103111303 1250 103110053 103110113
    0x50d0b07050d05040503180111030409180b010b0a03110702011d130e0706030c1106040213020f030703090204060b120a022206020c101d0d03140703090305070e0121 72
    0x1560747e400441030030300d840c100382d113146c4110760040348105041da00c02d50140d0b007090f02c1c00707a02078020130011170404409100c100021000a115102c01030180025440042d290748566100800b200c2804a100a21207010071031040582e0b00168030941134070036008820790307a4014402084044800400000000d801d203045011400d101180301300955485590030002203e042d0004c031000c0c0014003a010310b60b0011004180581020344040401d28056280540380c10880042c180290780708480e6403000030340d900301c41c10840c03415000c0d550050804102c0c03a803c01250a881451403200130b0700d03141032581c3c009a5115418602d0104215415880c01801d000d0340d5035a1019454075203c8403207034402c0b420710041510050060300c10300ca940701e100c0408006141110b06000401148617001d03001d20600621055001c072000005041d15031195440a10882c42d42c40c00354075005e219045181403540a00c01030102d03211048580450240b450340340d541103445810521442e12201c800ca512442d000f09040e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 103112553 1250 103111303 103111313
    0x210501050913080d05130210030b0a051e0f030c0a03080d05010b0a0801030312090203070b09090c0a0804020d030905150702190506160303151d07020601050d0b07050d0504 75
    0x2412039600361400744055507450508a0b0300c5000c028000c01800c800e0140741c03400c20700c80e44610381c8207000d8030006c00c50151503000114403941181c402c4000a40700c0350302a0803420020707035200041005580004481040780300b6003040c0520915454040d100500c19105159000c2100d8134500700e010300780080454507800c00d807010740d1207000311400d09410034000003140340d070500840c0c1007014030740e603002c4a507400c60740c044540607c009402201c070398540e2100030150741c080c0415401007505010300380c1e40d0410f0f0418007010010041c0114480c02c400d000110b000f58004000a0b0b200b68112408444480369180907140c0e507071180c00540d0401071512446d5007200c9030400400c4024000c0348c1d404000003110300d085810100300c0c0516604080240000b4001d0102c105078064a640f2a04003c10020000d480581502003560300462103141d8010741c0d219401d1040180c141c0001715440a04001d60501010458050700e03540000e19142d208400a514540f02c1c10940d852800c1c4100140074506041c102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 103113803 1250 103112553 103112561
    0x3080307090510050405060a080a0e060708010602010b0a05030706080903130e010617070e010e0409060911010e010f020705012d0c02090601020c01080105060c0109141006060c05100b0121 82
    0x2d0345003d01024416540018010810345049400013840507143c614000000c4a1303900e006440d103a40c0c203446a18000244100784892442084e05a0b10410503600d030050090949484081ca10700078211840f05000c1903c011811030150b030343c181800b2202e42c5030783d600e00f031031440b50010000d4000d62030040401d00c0d406c8450000d0407160145d1f00c080100d01d0f0350348040d00c00c800580b034040115403982c80d040c00d2540a401c42d01d0712818010030024000d031041c0c07100f10940302e0307000e42200e01c540341a5102e00c06607001001d5001d001801c0c603124803c2c1c55400c00295031441c440c05001d043c071440202480168481d4200c900b8400349203440c2c0e5800045000300600300d2403885104a01c280b03440c40000d0025403000802481400050350f95440700e920704014490185d000e0a880f403429500e490182c00490501402002c0400070007005000302000e142110080340c00f1074004204020103060488040b40001401110480030701c40d0025429141e5801a6185042aa0b0303080c200038400c404284150351542c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 103115053 1250 103113803 103113809
    0x2714030a0f0f05030114040506060d0f0501092301090f0207020a0b120106030506030318040b03010c05040f06030b0603070f1707050408010e1c0507050a0b01171b0a1406040308030709 80
    0x1c80e00b2003000c00000541d40790000340510040c21001c0c0392548104c1c44c0039040b0a81100001c3c01e0f0798607009402041d8025120b01a4005001e41e490350b00411994050307100e071078005607a03104001142da50b1111103c69208061283c0d00c0d40b26240c41b14480380440703545c100c1d10307800e60091042001a94400444c0d103d504454101c41c500050500001881c034000d0040511a49005001c2e40c03034042e458400300e044c003484041c615041980e807840c0c450b00e605c09104010441c1699250152a545451101ca03601c00c0750b034000108041c102102c17440c090302d441e4281d90304403080d0704140d03400380c0a92008682c00d00050500c84807003054002070285140e040300013081074a881000a104184510002c1c69540303941c152142c4084400402400c40350f407140d0040c0c902c0c14882d00540e0500c000d1905c43c2e2155440030780001c03020103103503034000c40681d40420038007041d0824140950501e03409a0f00140d900c848502c1143c40180100d050200113070740b404120307005103901103812600c0381404280101082101c1c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 103116303 1250 103115053 103115057
    0x90501060305012102100f26101406120c0c060a0f06060e0a03060e10020c01060e16090b0c0709050c130602160b0a03110a0201090c05042714030a0f 65
    0x1246404c45a04d05601d25031400d8000d084110703210564041110041080c2c0d0780c2c0c1d420000901500d8500514000c0000e41404034601032038414104025800072000303065003d00c4001004040b843c80540381c840603100107280d502102c032031030f5460031404c0b4002d1040400841032400340c44200000d801c050350011b9480400742d070b41002001d40307401c815039402072078082156000540e580b040000848507003004d028150150243e450101d00981a4020b076003103d00000e07102c2e5114142445030010036a09903510401c290f05405c01186001c0e00640802c420740a407210041380010141b8044100300045001000d80c040c0411451406219011813900001c800c0e008500001d600000c089100245d140311000340c80003503c031054605100b0f99401d510140350403003072540304c0303101d410b0341c441d000c000d09a0895150004106c0d0155454004a00310b1180c1140344202c0c60403282201c680059050080a2018180004200c1d112410b081c0b02046c201409058036100010340045080d900034134042e8000710725 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 103117553 1250 103116303 103116329
    0x150d030306170f03070605090a0209040b04020118060c020f040e0a0f0501050c0408120307021e0d0801150518040b3001050717070e041506080a02090105120c0409050106030501 77
    0x602060391a500f150900561030381c0b0500102d008a0350b01d90007030381c000740c0390302c06c8501c454050350204119400446042c0d5900c0c462004100070f41d42c01980b20005c01c0901c8040315007075401c1290250054080131406405a07040043d1103030709446640c840100e591040c4122403425a1501d0001001c2075001030445240d424900800d40344540700f82078900761280d807000f800342082845909800b41d000140000214412004103000028024100d0500d54030402c0141070a42c2c4540001381c002030045c0d000c0b4241008070600804a80d40c40710903201c111300f01501c00845070349840005030142400a00041c0d1050710032500703c10380c5004c044110040e80d40c13904804407041844c07103003501300c50040303c42c0070200758900080c28400d101c0c04001984880507007400071000e211600400d0448102c01c0d9600d51600187e80c05022a80d004050315a20400701c10096141945840c0000d001d809030f03210160020003c0f40101c1c0c00f00e00e010381900d01800f0590801c200d0341d0b070f54000042c0901800e100d0031040c0aa4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 103118803 1250 103117553 103117589
    0x1120609210311071e08130b0901020c0d0203031903020c03040b090a0909020d0f02041b08010f0503030304050304150c1424040c0605090f04020c07031103150f150d030306 75
    0x200340266020704e03400c00044c0198038819104400905a81001128024000c001e02c0e5440b80310071441402404901000b0342e212541c0b44006031030300b00710303c8841d4030a0b4561050301e001607070000300700c50003424030350041194214888400c2d0040c1c01001c0300210700e4040454089145047e1001901040101700d41d40c3c2e40c13840d541c0c001d0f14101c0e44207036030194020303400c0700e0080c020900740e0540c15646840944001030784078010881d200843d00504604001800c200e00400c245c40a0b034115602400044014503d03508065544a580703120386e1143c104088500d590081c00c0c203008030803804000e60420f2a159150b2000c80c0f8054540961002203c41c030f82d207a1561101100c5048042071203582c3c4044503618807030419070152840d41000845a81c070280800a0850301c1e02c0700d0002c4c02422202a0040c010ba904515207151032404800d19607000b035000041e4000b00c104019409900610461540d41ea951100010307a181c08440002d070720381041d41900100c0415626511142c101c460545443d020784035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 103120053 1250 103118803 103118831
    0xa05060402010f0519031a0409030909061a03060f22020403030207120305220504111e030f0a0c020307061103101a091e0301181104050f011206092103 66
    0x60340c440384d111a4a0741e11540117143c026803010b0b6210007554414101030000388009804d50b006040e086001070501001000000c1081c080c400180143c60680c030000e11583d004402070f8000105650720841001c82c0303013002030303d0319080800d9003801d60b05814064040030080034069403051000b100148600343c2d0000e42c0039410a482c1103459455070300c00c0e01e1b1418100b200080c007425072602c0104403500a0002959a95621441c0d803108040c402442d00d41c41d010800b42440380d002c00c6d246a00c000b00704204003908200408280e4001140c4e04001909000d0700e00803859800351100c000e161340d1800002c00000014a00030b588504000d00c954401961110200c001c0065850800312500800340038001040c0b5003549071f28020000708400c08140c40c100170000382581e0324851a29088403260280300c0c14424440c00302d1003500f10039203013400541480700004186500500c40d8203a0814418060402c00a458010481d0941c11800030007a00c0150310900d2010244105440702082c036045107022418 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 103121303 1250 103120053 103120057
    0xe040318050f0105190e06160b150d02060705150c030604180302100c1b08030717040f0303050606130608010807050a031a04080c0304080a03030e0102030405060402010e030309030a05060402010f05 86
    0x100c01a529039013881c450341c3c10021030340070440c170303481c240200100d00e10403645841001e00050f800c4800f86d8408503420b0704007d44560009030007144110705514042c80700744c80b06a00c0703400702c41d41035074099a00c03c1c1c54280903061540000c1107100343c1050030705010a0140600140d40584c0d03088030204040d040016000c07443c154078060041c00760700450b1501c00c002805038006058180390707046c8076036142c0303047c0000c8610002d005412103003c4c002000740311300141e100e00004041ca8192488072000d00345510784903e19448084014105501d60700040c529032501e005a400140c0390745218829280c03640405003c003d4240944030782840355440c00100d5140042d0f5400480303420025103800c103029148201c0c0c00e4140288107440031041000203514042041000740300900c202c034041c04403a43c0c00c1c0380c01003d840f2085120012a801401071001050f000704651f82c10690908010480c2021100441c2c150301031502c2d165071600407460508240040422510310440c03003641d07191000148220f00780c07140c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 103122553 1250 103121303 103121329
    0xf10061b020906181602070e1902030a090602070f0201020d03090b061002030403020915090105100e10030e01020c011b020a0c03031404090f0c020f030c1002130e04031805 75
    0x205040c403040260901c0709216411600103000022400000748002c1c031904c02c140d07070541c950400840030380600342e410321400e0302800e04013580411a08061000b05213050a1205440078681c1c0040400d40c01c2210354096004250302003015900e4207440e0812000700690201d06034058050006502c100905c64440c0180a55000c8107503400c81c0c49280500c4104120303c203408082d0300c000c11010016945641055104031904107400e81d103d1503400900501300010380c4800d0040c40c00028103100c5903000710841880040c141e50030710003240320071401c4002d1301200112400551000402100811040d0031204007400707965604544010754a41c01ca0392944488805450302d6000141400040d02c11019860560740c0ca0304d04504283d01c1c0c3c001d000440d05000d03a00c50381d490392250a55003903901800068044507010000e9418200061501a02c0d49002e2921806080c0d0008110159420740ca480c18060420007000e15907a18080ca0054a140004d0400300d0014203d60b10002e00361510380700720611 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 103123803 1250 103122553 103122587
    0x507050f03061315090e03070812064b0a030210140a0804051005070212090d0804090b150307050a0309030507020405040c0906170c0d03090e0f1006 65
    0x5090500030a9200503080035044a0b4010088083c50030148268043c114000380220304554040d0300d4420328404540c0c00c0305180010350028814130000c40d48010075508010b03600700820070300340c6e20500001c8180d4426040400d0541103a80c191419040145155040d83c0781101d1160706a002046c0303400201042d8000c0079800380714084144010b0070700b240c1c40d4800328002e0030b10000454091728201160340103040d00e00300080201c42040180601042191682010f001041115040500009445841101e013803041300ca0001030300320868984010740d82071590001c00ba1368a0303984540e601d41c09071007510f540a1044105510b921a41c0e84c0100c01c80b0f009401c01d4944034a03203541e01c0010707409440764480030b50a1090070b110320009078482e801070034400c912600e400303440c840c1400e02038000c4480a401c1851a0a6212402d00103201c00042c00d464440e0308a84010408040e46070807120000300d03130040c20301c1c0e05400d414007811802002905009a0320726070038800701511504210742c010085000020307 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 103125053 1250 103123803 103123807
    0x807050901050d060902060409021c0c03020a020a0b07050f07060b040b1e0904020121050115091a031b1204020a15020a06091b030b0405010b040c050d1a1c0312050705 73
    0x4001a0994071141951b0b102901d444d003003c0c1e039460f40208a80180c07000c5113400000800c0b5004010309485003400c5039900742411070031b08030400d40080d9140885c000c001d000d10040004200380d01c0c06602134803901701c0361941041c3c0d91543c40ca0088040e054140c0001e002d142810001c83c040d15241e588501e00c4128424040c3c4040d4202080000030b4002034000ea05100041e01905501c0205200c00c50000d940c0c41e070701043c5945060b040f12041481801901c0030010401018400724803a509032140404110701065202e88403024907034040d450400007a0b82818002420798106000c60754003a1069000b00e6011b4401507aa04040b11300c0d49102915a005803c0218080001003503030f0700442540e8010f04000a401200380707200c80201010307401c00d40b441143c150401003006000d00818942e030009170303014440144021000303403250050500c002201ca03101c0241000002000c90f0100305d20340010310034096131460004412014809030f07070503000290304260720070068a00d40a00340c0940100d0350341e00c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 103126303 1250 103125053 103125079
    0x405040213210b1f030204020a03020306280b030a0f0924020a0f050c0c0303030907090509031204080d0f09080d05090601080c0103180203101506030b090f060f090907080705090105 79
    0x10020015803098800b25040c180400310251f00ca51019100400190b14010390381c0c1848020002c8039141d2910300b041e610f841d825200402002031013840304450307040e14842d48075152440a01c000e88000c45600341e200e45040908400d02a07240c5082d011103c0f04220740780c200000034920026031003002055004a55070a0401c080c0340c0c0709400a00141c01c3e07100035035800701c40c2800007909640c0107840301c07030382031b8811300d014800d406441c85055006400400158500f1054640d00c0004d600010400341c2403040110f0805014011078015035503042ca088400c002480940c98440e55a80086000c9141c1d0f500c0c10300060400680091074505a4844100401c007400d44800114054058503c041c6800701003480c0790310050b1020029803c90310b1041c500460603003c4100c01b04205201903000c04101030500d200d20707200b6220019015041400c811a41c9074a5491001049900b1000500360760894002001c0200d69034020030840107441411342034841082c2d5070002c204240e4000c2c000e5652000c41c5607560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 103127553 1250 103126303 103126321
    0x2010801120302030d0f020315180a0c050409060f03110105070c140303040306060b04080f0703030504180e0f010506100c0809060c0c060406050909060603010b030f0a020405040213210b 81
    0x880d102c1c400c1c41140c1c90007209142c1076043d10a140100c0103d11340200c1800b840c000419a5945c6004007507400440401880d0300034038076600080c011940140e6652100d031905441042102d0251000340e1091003510f40d22203440c40008180c0c403041e5801c4d0008030201c00d1562080080b5030949411055816419080090720500c2040c04143c1300d0745480200000000a51179024440061104400301911140317001e0041d8100420380c0c2110b400307500404001c0c0002a00309017a5801d98003400621210120f00503003600007490741c40c4202180b48030380c1201707032803101054000911620f029500340180d40c00501e000c0e60b412482c5480100503680c1441136203c0ca04000000c2c0122015420071078000c059010080783e029440780d0004000603100280540030703803c0061130590410403c0c0d582516641c9090b107480d21030300001e00003656150312540460001c2800c0d0701035401812004100b15580c403140410701e2022030841c424049213038581c45c50f94040e0415050040c01080d006194107a6603075400c0c0034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 103128803 1250 103127553 103127579
    0x8011a0301030213050702010209040903080105090108010e0706050304020a0f140f09061810030b010303090e1506030403111c0c0c14060a08040303061e0603050f01051c050a020612060901080a02010801 88
    0x1c81b0440d982801111a155224050118110b0284e140c540c10b44d4100024495000c04c141c1050b00540c0c14403046000c0210001004401c50f80309141042d1a5203a620004208840551010b581c0d01c00c1d00c50045450580c0720b904800c80c280403a4203170401c8207208107001d1003402c21180c02da0b000e11142140d50a9580d1100041e5002c03500248460881d9100d40c1c038146240001c0c1c03c290005100c0c15424480f00080518060704000082d00202d00844a640001d00c14070005000070208666400d688800d10300800c0448280903042c000c03030721940740c2c0c604000c1c20205030110540742484014030000309180e04100c0103140410180001e40b81a000603408c1e900c0c00c4010700200c04241c0d803001d0000b91003801142e0400c8020603e081016080e2034207200034159a4050202660408490010000d0b03130340700126080700c1d030194030300d201070300420f8105603007841041c2a0103500400c000400a540c64150b141c114400c02c0201e500346404d98803510401d80d50840c1070700003400706860741c0051000340d031a258 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 103130053 1250 103128803 103128811
    0x1213030518040b040e03041e0302310e0d14041202040207020d060c050703030b01021b01031a06040f09111c0f0608030c06070318020121020c0d08011a030103021305 72
    0xc0482e104943c0030108080f94070b01c580407152500b0101e410f000282a1015940c0c0c020700e000050301d002400c0d0b80025062402e40b00a2030101d525004140080c4400c0d03001c0d40c1541d89000004109401c00e5944c10745e150107140001900203030420b00140203d8000100781e9094848091840c10125595428000254444202030f40c1c4207441599020000384c640c00f4080781410603940f05070f01c2d03141e42e140180c144c4419580707280c15904101c601e500b03400004800e121544400f442c01080d20303086d1a18003901407403101680c681248000030042001c400440034802120307000c0300108041c1e80d0a01400d28070380688401034000c820042c10448110302e01c1e4100d00700241c040980050b4260b50392070600d242da4404007908602d40c005400300029203803d0311502c003171103980080140300c04460350b00080c20b955903c4005806900b40d107030291790201941c1e065400003000e1608489803072110143c0589110001d1007000c21611a00f40b0740741c0980c0f42d08059034122a03002d4054034140c1c0582ca00c0304042c1070020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 103131303 1250 103130053 103130059
    0xb151213080c0d02010b09010e06010f12020c0f1e030a080a110904060e0f0c0a12151502100b01020a0c050f151809010e04020102060615070f03051213030518 69
    0x1200d100b0405200703200f980f141c801180c0000070744109003c00c0c4000303588140d01c00440786112904204e140c0e60003040b8107005211514004802007850902c11000380149075181d50700340314041d0640940400014440e02c8903810310b441e07290305c04040003030395560f01c45c505981000900500220f80362001d6a0452540c50741b000301110f040c2508400402c0494455502083d0701c9041c0c80e041c094100c0c0601121078101080085aa261030600710000e0700641407030500b00740465440d0b010b115103400030b001140107829450000403204d1140c440003507490b00209600c0154614042e501a4550300000320b40078065440030f051b01070f003071810b420400040c103010000b9400c00c8000d07007088852504500104107508451545903040140101485080780b0141c2041c105c01444c0d00034440580c6e0009405a406402151000400c6420b407100c01e88070701407a071004020504504200301010b8009004e014003403040900308a2580c1c0f140c2905d12400340e5600c001c2c021510800180c2c01c0690340303100c81510101d0113 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 103132553 1250 103131303 103131307
    0x110d06060305030d0614040c05220b07050607091e0303030914060115020d05030c07080708070b09010501030314130b090604030503070c03020f0d1e02010e040f0b15121308 75
    0x90b202d10742168401d840001c0c3e000d41e40c03401402080035030404414840f00c01d990400001140c000081c200780318451500704031480b0b180d80b490112010f107031050013600c0051003080d2548060328115548205c01d5903d0000318481d80e80200e1114541400610301405281401c0c40042c078589080c2c0040c0814201690030010800c14000c40480030000c1c180203203141c2c0085c2c280d000b000000203041400b0701c030751881007003c01c2044c0141044a10b040e2400250841d0021b43d540505107001007440c0b090400041c0f03000842000c010752800e040d480241268025190320230301d071401c80f007100b1981c483e50000351000c10703802c1c6050040b0410000602005030016110034505901e13610383c103240d600300c50b030125480c901584041c42141001c1035426805201610003a00811407542c071503044903c209021814103c4c80c0030000f00350b80c0719006071040104041c008001d001c0107181da007405082d40110080c0241404110100303c0d003003100450704c0b110030f00d25000320346844070840440904405941135800141c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 103133803 1250 103132553 103132559
    0x9090d0c03031e090b010510090f03020609010203120708090105070f1d12030d0207150b130b0103090f0f020109050f0604050114041a0307080105221e0e07180504110d0606 75
    0x164440d0040c56401174100068a602d4a01003080c038032508844901044110441000300206900741c8405680d8110390079501c6011003c0101d01d5401940080308070100390000b80898a9000134200d0b0046662000a20541d43c6100d03065031964920518500000c2c80340c05107210348600c887c10003405c0c44004250300b800700c0707402000500d140c11000c1c2c04d141d0503600061007001c11401584007111000d0701d01080c04580346941c00183e140d0610f100014640d5100c0e0310115142e84030340e10613201d043e8042c4c81c1049001c8142000d0184100701c081c100e001c03035100700e004070b003e2620781c2200a465100406462910f41400c0c01100e1410b03940ba4007400c22842400b002c00c5c40e100c0a24401800044402041e07102e10307000400415174201a482640501a0101e064014800c0c000c444a402030222101151004800320b240150b00c000d0ba41d43c0441500d4446003000000020614804032030082154616100c3d0080c021350440d101074030024079441420780b2454072030800035099481c140c01003d00240b0340341c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 103135053 1250 103133803 103133861
    0xc0506030414100c03060806090c12030c030d0606080f0103020604170c060d0902031e03040e0702032b0b040605030a02240304050c100c030807120e070b070209090d0c0303 75
    0x4040b8143c85850b075255498154a664584034000090082030004c000c02c0c1804110a5140c0b802081701c03071b00a0171841c6030140d020800300200d6204030314000442e0307591240c4c054600000c2200307005500c0003514100114241c4a030745242581629001440140b504d0f1400c0c1c0701d40c1002d15255100031050107010804107041da2403102422403600d48140c00303e0012894410142403001c0c010031f1120060802d180b07021507600010940d000d172080000c188907282c8400005034035600600c405140ca0814051101e640798000355807041444801200600c00b04140300204429240d80703001e02e60b0140c2c0110001c0c00035180c0300d446202d2040c115251040c41c80b41c10840025107a1046505603080d0b4840c80408040c1c1c14110b03404108800d403881c00840b0050a594000d10703002010302202c0811206d0b0460200310f1182e1380c802e001c0620703802d003228400c0c0e5a402c4c0a2a080e00908010307445602c1210010707240c4440800d020040741d0031f51b99110810880d55600780e00610070520000245400009241c41c014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 103136303 1250 103135053 103135063
    0x51207050a3006092007030c020f040e030a020106081b061606020f0c010605091302060706050919060f0b040e060705210108010e011119080a150b0414030a0c0506030414 74
    0x66283d004550002c4501041c0075090283c5480000c0017810009000400d6002c01e11405460703040700c0b095400c82e80d80c2c1c001006030150b004004140c1c0000070703211007a00d4056001004031007110055511030340c642c2102c2e5511491074101540c0020b020040814000c0030b8100720242944100700040c06c000b6011012400c0c0d4110040c09403803699101c100788854942580c000f0f601c40340450101c40f54501c19404241c00d402004d200820703180d210f40210b4030b54001480402e0004510840c500450400c03810500041c2c00400c2501e000ae51503e02c41c0b00e4503080038003600b02074961002c0202485d8440040450b4103034012410040030346502c4500c40601d110021015000300300071000130071706400610030503084429890100328108400c000c3c684180488010f4014641418217040c009961012000c40140104c000302500f0107015a0010841e40e00307075070103841a15040303651034405803102001d265407017a801d04060081c6260200c1048540741c0760000b07680c882c1c4908196441c4d0349400e29014501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 103137553 1250 103136303 103136309
    0x106051825050711030d0905090402120102030c040311100c1b03052e052401120204080a050607020105070801151101060603052d010905101203051207050a3006 70
    0x141c0005000c1042c0204044c1c5404085400c6016140100c000c20015020344441d02c1102e004015001c001410b41d03a0f0b24002c403092410581c000d5540e858a0520401680d0080c0401c0703c1115000720801d0303031070034181c100030f00503012074031649254405034503490300403220f2180b01c100c0801820350100024400f44210040e400d10640da40a80400004106c00c10010104401ea440c0e441c04040041840c4d651215100c060410703110718075040b001200403502c80c0407103065883d03520b000050018800b03070001115150140104180d0ba855100d0201c2203081e520195400c400258409006010071081c115180003c10101d0800c1090302d000801c2c46800e441403540628003090340d5604108002c00a40203c259502d40c4115040340c01e00a40c0c514440b44106015024405075524002010303860004402d40113001044908a8550708603d00200039501145d480c5031070380d050300c021510b507902031800c1c1c0d21801c00035101c00b001c0f01d0301074160701c10344403800c0e1194803c0e80c0b0840c03540c00348280520401c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 103138803 1250 103137553 103137557
    0x304030c17160303050c070c29040b0301060306081b0f0607050d030b010306050406051c0c050a03050303091203090604030c020613080307140c031b030c041803020f0106051825 77
    0x14480c10f4100a011140010411072000908120300000510b4a00e800340c20340720301c1182148901c00c801c1c000554400d00c16110307101d86d180003a010600b080c2c0140950f049860301d59061011540f207203600d64a4448110410030002d00c4c100706060285454052501c030140040d1140781400c50603110107103800519007034000800d03654aa052100d5034140151000340c681680c003403003440e00c0d0001042d84801d0303001a41c12220b80361203c0d9010401c2003890080248001401c0d400142e031203090581d200c0d40300ba5900340c3c1c01c2c8903441000905e410341c0307000d4920904455010f800c580d5100d8030700b40c403440c0c1c0303056089034803490030010140b40c1402005850007074160380b0015900c0e8500c038601304840514403408907286038480380314098903070707000540821540030380001010090b522001192500c0c001901103a400703802c10043d2410b0f00514414141894001d608440000413a4031000742254603901565070000d807a5060289003440804d00c01707402480c001c0d440c42c1103450b07011480000c0f0020b2800240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 103140053 1250 103138803 103138837
    0x114340e090105010e01020d14070204060b130905013006020408011e06080712060612060c080a0504110402090102031303050a0c090e0a231f0e060c0304030c17 70
    0x460401d0458203014020a081142c890b09101d00040e603110f0140610b1001c01002c5507901c0880c0c1d200e2420b540301198054000d001d0700c0d480703412500880d000110240300804070b649001600d01c0090003000d0403211958545a031740b4044107604e120f035030040404030504264520040000a1032803000304010000c00c000003600814240e18401c0d0f0a5a0b42030100c40203013488400d200468000ca4820116075061f698030101c19403624040b40903003920351208201310f520401103002d105179500030030200e0105980324005a13a903944158122001520050070005141c0710401460516071b001303181c038800c1401100d052104c40485504c0704040c0b50404c403a66004081301804102050000c0006041c201d20140540c1001c0004c0d81c1d5907400903c80900100034105000c0c0c1c60700482c0c3c0c800d00e0411015016510380846601c003940124581000c44041c1d00d180c28541004e030240030584070300a0710340b903160030b00c0c503112178804a89500c0c0e00304080d0394000e02584419802c0c0d240800801d42101c82d1800300b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 103141303 1250 103140053 103140077
    0x302070515040803090c01020102134209061b02040b01030212180d0504080604020d060906021909080705150705070b03130308010504050415090309120303020702040b03011434 77
    0x31b081004602c44c140c15603005011881084810004000a88005500d1282d209202c8076010b007560b882403205c0c4001090541c1d1003100f00c40030310000c20241000c0d4803860509940c507002194038818aa060650f50f082c9481082c00610f0650400484000c0501d005800c05041000b2400c45250650781852507101151a54241080510600d048403c850500b1070030a031408020340c5c0c680c00700400081c42801154000b42c100705555105403900c07600030303000315103032203003124584100c01da04444200480c425802c0080c1105001a0100503140e02510054028000907031006c1030340c000d43e1081340d0a0017034480105091401d03001840c49954004140c10004032903003000382001c0c00603040300c1e019034101800c110100c0c03c0c8401072248804800000106d003015820102c818a4054101c00344042003407490b6002c0c50f40c1500a800214000c8804008103003002080500325808440841e41c0100f04d013002940c0408101100701455480e09170003c0e071001d10322a408490345070103207882d002c0740d00c1002503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 103142553 1250 103141303 103141321
    0xc0607112812051201060309031e030e06093009120304060305130b0601080717100915270603051005010801050709080606040914060108070314060403050a0302070515040803 76
    0x609902501401c00300d2414220684c0107100c40c005006e0841419181d8403000f00b01441014a145c3d2025002c9000f03071364015000008014101105040303141c0c2c441c1e200070850150001c19044219603420203903000b1040b0a11603003c426000042c50395203204180440065521031015a12100c21014051640c65040c00c8002d0200c80307016040840840c9c00a001c0d000046008102d542c000c43c090905480690724014100c0e5440300c1c0164a449060540c000d01200d00c01c610100000d880c10f41e06c044c01060030380038204103000301d98899001e5003624040b00d0850100c0c010f903514100c0994220115045031070f0b171620b62070b00c0030445140080030390f00c4004110702e51080c85201d03003000701850034610481c41c0c0201ca5070f4551000d054a441a075455201604100903445492074503002d02e070030340d0031641e502d40e04c564542c60284820b40301c408013071609408000021030b03401d101d240d05031940760410a001e50120002d400a400c2200c1500c2441c2d40304203031884250380144968454915542e592510700c401c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 103143803 1250 103142553 103142573
    0x90b18010b030117030702090a0f02070f0503190c0515090a0506160f02010203070c0201030f0b121509070b07330b0f04140103020904020616030c06060b0c06071128 72
    0xe001c0058006101890060340c3d4402509d4002d901001d020a181c50f6941894000740302c2c0850050551298000c0e404c200140880038001d424400030440c440708103001003d0f248818882d100524075040b101031548a0200000c050313400c0300d144000c5500d15900f95a405180c144191910140e6001a000e20748078a681301c403103401c0b03111542c070095046040400000c4d140e9178803040c000b41070644480780d2800d215180e6005841002e4001e1000621860085265480340c030003000e014941181303000000c1c03040c078000513100c04480008180f18a800420703214031302da8420f00010614441c081d42580d81480303040916000c117011581d00f0028800001074100651014481100c50080303040152007040d0080303084c46281102c1c0c0503100c0102c0c903585c52002603424400c2100050380b02000c011044245540b00d4000d1080c58400c44e010040683c0318810301005004080f80b4000b80e40c00000028600c82c42405a050801c1041e0b041b0780224030185028030f01048405200920324100303d00d902c2c00e011060354 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 103145053 1250 103143803 103143839
    0xc0d0302071401030903170405030f040e041e03080c09060d1b02060a0b210106030605130501050a02070b040602090a0302060a0f02010f0b0a0302101809050a0b0f0a090b18010b0301 79
    0x20f0402075900176907000750426082ca0f00d103c55811078400090144541070084590001d00c80032100da66903180c104d5598016004d4078103403500700828aa000c160010300000350305403a0940c0315240569141190724016038072200c1c42c541c10103006c2c0181010101d140c080c0455041c2d6520031132600600c0a10028903000004000340e5a10742050b01c09a01500e91301c8401030502a44100161048a00070907107014004a500c014801e5107000100051030307098404a12045206000a11698559074070100590140c0000074011301000000300e40062a5a40141690324000d40700181c45a500d80001b5150b41050403440c01294040c128014610350a02c40c0c480550080d990410804040f03501040c507021042c080280107091a03254200c006000b544854003076072902c1c6c43c0d030781c016449101d107002030207050310080151810100b03d49158540b2842c8202903210180c040c4016525040b24500588600320205420110021240d6445030031804407502a00284440d240e49503d001c500d02000d0000034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 103146303 1250 103145053 103145057
    0x60b03070507020f041b120207080c06090f06270a060606180905251206081c080708040b0604090503030a0203040302060c07030909020f09030114010303030606090e0c0307020c0d0302071401 83
    0x510100c509000030001c0c2040441e10b2a020075014045511f42e00244151240035019100200d0311650b54440090954403404a41080c0d4403c21064a80681e40e50000d9500700c1088404040721050031252000c05084c4140010498080c0c80e20381d16140b08071801500110002801d00c00f41c07000345500102d41030010300d07100d481007003145030003074031120140103c0380d88460380c804002e25000c490b80319403040d01d10314510003001c20046581e2050640c2d52503507a141409500c4105080c15600e41c090511389216203080c1d210302c0c24036076032992a041c400100400490380142c0d15905400451000c00103940301d014005c03030060340c03803c0605000c0e1030200003c00c0b00207440c00070050000080d03440321081d000c07a050500e01585812a2240d020807901070b4840e0740ba003641c6412000340300c1c4044110414100c900a8408001845c4c4403001141d41c0800350084030820501b075004101005c6030400110b502c8042c62058800030381c0d5200c00100c4541244000b0b5005900105051001c0c41c803005101d800040c0034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 103147553 1250 103146303 103146311
    0x50604030302060a02030406021219110f0a0c1e030e130c02030a08151c0303050a060b04170a020415030b01090b0d020904030e060f0a08010909020904020d0303060b03070507020f04 79
    0x2641c1e000790340e07480051841c05401c1d0084046410000780350150380c41c10310309a191000515240580502d16031142150240060400e440320400428440845480da0045085d040ca0101c08283c240c600d21143c0804890b4803950002d03060401142180d401d141a20941c1c802d60140800d00410541405c41c2407111582441c022002606580000840b0003807a8142070840c2c40382d81d4441d65542c0301c040c142807a5000810b2101841108101e00c0d0320b2040c0c54071a80302084642c484a21440440303c880c040c480045030208070a2280300200c1004607140b18182c422640b41d07000e40c2c3d000c107013611843c0c0c801c1c400040704040c0501c10072542e02c0c6100e003d420543c40400c60a104207000030700030203003072101900501e0b9090109003414400c48408808210141540303a035184203403103003200f0b40d02c1030107100b001490b44400440d41d0741160042c00d450b20b80003032001145445503020403402c0c40c1685000c805043d036802e8001001d10306000a54450720aa0b104c1a49504050060010070200c40308d03c24417a501d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 103148803 1250 103147553 103147559
    0xc0406050a0b03060904140a06050604180b0606070602190302070b07020a0c14010512090706020f0708070306020c0f070602030405040b06091e0d050f0706020d05041422050f060109050604 82
    0x442d00680f580400c0440326142c65842d1401c222088176400e01d1200481e015a90039903040c081a9080240a840c040d1000c0020380d1500048e68a801a8024002e0104141c5000300e00c107890480c002c0c00405025020052405140d401005100d1843d2130a0a000c01d0300440e00e4424400c1c0e11103126440000740c006020607008903916080e03c029503000340850380081088643c6141d1250007a1981c0cac2c1d401d400c003d0b185051080116036142c1d176500c01c160041c031400c1c0280c80304410208420044425450041010034290740d10344001e0340148042c52014400c0381420079100404101c404002c08998001c0e60ba182d007400c043c070040e07641c0a94514028403007000314112603101c00316010903512448410084061409002031084441c4607006000e034441d8240d0111088808034007201211030075000c5400102d40c141d0113455500651140c08000c2030384001040036414500c0e481e0a1040340c00b081c0018480c0c0c040f80300030441c0d9090b14080d848a081c13204101095820940c40c00c050034044031100d0030b140c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 103150053 1250 103148803 103148819
    0xf070807050f04181103040c0504060510050f160203070315050c07081204030918021801140403030c05030d0905010509010c02070f0603021b0d050304110d030c2a080c0406050a 77
    0x4114030500d4510071044c1d400203503400865200d0341c03861a6420451351b50713003440d0404452615643c06010f1103146000c1000550b460200003034041210151030740c500b0003081c00401c0031070b900302d0780015144c001c0c008050001a5010305c00c0c580918031440786a001420802402811110020f00101030444104002d40210300d007407056070501a80940004015515481c040310500f4890b48034100701105518145a841465009041003d0440740302c41e02040d80b0300c00460b0089a1503034001c2c1011001c10090002ca84202040742055000704100c9240c01840c0383d4034012078080c904103a4560355a903090000c824420301804201e05260700c02010420304100c0207004900700ea210b0303103091540c000b03802d28100c647c00b449007015400c0d000596040702c40c1610702034a1980304580072035204201c44600003440ca480e4142004080d01640c40c0d01110816555040110b60039900d450302c207410200001070b00801001c2650301511500003c0c007428400902400185c41460700301a201d907c0c1e48109000b003c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 103151303 1250 103150053 103150057
    0x3130f0509010506130f060e0906040225110d060f1404030203032403010c08010620060604090303020c0601031110080115050901050403120206042d24050f070807050f 73
    0x50f0304507001e540d20141d95000c01c1d880416070b40b00344081040d8a00014125070000d0401c541c00d14142e88140050361070303004002c00c038800d079400d1040115a0140081e24401c10282c82e60f20700c1d00c07520040032028604070015040101c18182102e9464850030342c03203c1d1125900400085214801100a91781410b947c06500c82c00010b160310785004889500c500002201c01200001d104050000c018080c0f1490008003000c909004400120f80c40c81c6401e601100c0c9000544264055003003d4882520f850040102502c030401c0261f08064081c003800002c007a05002c0300f070085126000d00b0055290546c18850084525984107042c00f80c0840108042d1a40001a44060301c0e50314203142d4903c4203400503295401990400740ca0000d14521203a400b54000845a004074020a1802c10603006400b0440c1e0310000d10501c04085609000ea401c000b4000002201c2c03075004a0b05c4407400b4a003002d241000b11030040701c010b81c28003005018410000e401422035a00400b5614201d442c1a1260f500741d2214 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 103152553 1250 103151303 103151309
    0xa0b0609011d010309020627060c0304090b180a0e06160903111f0908190807060c09090911090a0c0206070e01052109010c03020c0c010305090708060903130f050901 72
    0x100050b098070000ea11a5004118159006141e1500c0c0c0002c000c030311700070311300b000b070460502e9455402d0b104482c41c00005443c2401d006100662401d41000c080d030018003c200401e075040319210a103a08554102c40005204a850b4840080e240c60054145841d0000280c4a020401910b0300b020f41000d6111801d50103403500600f514103030301560f5000c10001500c5250741c000c1d805203c0701c40f4504c039501041680c203c400130302c00c4940c003034010031000700003104000d00100200d404000c454000348050f0422020078505007084c0d40b43d00c1c2c2d44d17800700d4240d4203011801c4400542d159004a064900743c1100c5030070440414082190020301c48000e13544050103403060003030001007540d41c0303c10703032080040340c08442d0100745031862002c866a8090414038107a0380a640c55081014950045210303100361090440000024414542d080e40190018070020705040b6550180310fa000c100341100300303c060300a800401c01103980c0d20305407407000b9849090390040c08a02144c10410003c42d0f803071003091419 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 103153803 1250 103152553 103152587
    0x120912020f0a0305010207030c05010510050603010303030c030609020c030a02160e07050c0321070e0103050f07051b01051509010e01050d020105030a0f0516023a1103070b0a0b060901 80
    0x10290200000030100b81d1942c1c0300401540c00026804101075000f421012600d101d0340007840507450301a100d0003a042c2c5402003d8002074244010804244280c001c0444000d00e030500252031615200a08142c2c0d0207484001ca00f41c0c00003981383c5945a040007450102542801c080711002e040082d210500c1201070310b40020044003040c3c09013400c1082c0308503941000010180c2080c103403450a2440704000444440c00816503010062140794020701445114001d80e801c011860355407020280c03544d4108449403440300c441000e880c0c0c980c200c248a014010a5000704112000c2500c000708648440140c00921001801500422071034a034a8006003020380e090a020340c480e81c4143c2800001d207021020200c003c0d003800d091081c1c0e04500c1d0304070105e8425580c241c50440710044110011010300c010443d02c0c0074880713150071010318a100b15000200001d89070003a0f41d1a02e20125502d15004904251184041e680500151040c2403280380b00309001500c80344c0c2003615460000e0003004043d204640 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 103155053 1250 103153803 103153819
    0x4050c04020304170c01060512010b0108040209071403010e062b02040c051204030c050f150c0c010204030506010e07030c080f0604090203120403061406030708032209050108030712091202 82
    0x402c00c501d101d01c0d61918035076030131984440c0700c11a038601803c6e039845642d00031010500c007051500810300a100100006031108141034480740c0c01d0100e0504001c0a544c01c200c411094100500c607000011030091182009030205070401030100101072601072071444214103981c0e80384600b1010300340304820480d01200c0002d080300c510b140641e054811040c01e100580d00b0fa00c00c00c802c0640181d20210620302500c216110600c08003280c170307034680f14a1084160740000c00c001400e0484050000c2034107014160000d410f0983d0380e40c55a01d091001e80201c000b00c0002e00402c01116490b205056088800d454051058207004112011060004e0541030045885158500c10754808002000701020790164407030f81c0e00d55170300b03100000b094400e112014880d00354021440528000902c007040d40c2001e4040c41c0b44c0800420000001c2c01c00041ca0707140c1320840040060800303020700c14075000b03115401c0a143d6450f000c0c6404124052062011002c1c4505001c0c240000c12403882e004200c1507042d039040d0303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 103156303 1250 103155053 103155061
    0xc060a0209030a140a05100203010b0702040b0609120601060e011e0507030c02100306050114040b0306010c060f11040503060a0c05030a0209030106030f110a0602010b1f17040b160804050c040203 85
    0xa0803c41c1d011400f50807002d03071801e00e801140c000224182d100d03000b0400d9030300b107081c0400c503081640300c00c1c464aa9100818071400700035107800d51160041440081610b8a088002d8011565400b01030b151800b5a401410040041a80124401050070380034a440c115582e92402d120140c52280440c00c010846d02064500405000718041d04085400070500030030842d8041c0000c01400706809002d00040c0d0540302d0080c03000e0700c9400c0c0c03001d54540745516425035998500454926425034801e440c410b481d00300449840500348240451040c51180301341c0e4031400d003400c1c145442000750102c9050740c9448520503123170364002c090701c0e000700003150701583d100f01c8071000a015100980000d0441d503003c02045041003103481c04480803d0080d51646011030b0307a00c405900320b45440140c2c40d0000400400d0709070b101c04400c442102071035142490040c54280e50a40202442e044804542040e084810702500000c4059030600e403410602d4144605d25080d515076880340106c020742401550044041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 103157553 1250 103156303 103156309
    0x305010522120e031006090c2003070f0f0f060f0c050c0604081605010e0102070512030903030f0a06030803090a05010b030a050705151e1e0301050d0b07021213030b0c0c060a0209 78
    0xc0d008040200380250b80c0c0b00c11f8408010101c00e1030480200319010001c04003082c2e4102410355001452001d181804800e460301480368011940c00c450318100c1c0c1c8888400a8402101001010f0181e1000640c001d8019014411518803c00c080103020041c03069030204d140002d1025800f07540b03d4000c580350030b1300382080035802c0582d050003401d550820036111080c902c15405403208078010011156440c180304d00464240c4410f48504680d43c00400001d2002042c3d0014160000311180340040c52a50380d8548000a4005a4425900d60412400c3c40c0600c071017405140274150084001d8042d04c1041d907a51513561010303119181c010503602410816094a000c00d85d80c0c0e4072110840303d03003580c0d4650003080c541e50100e12020340d02c0c0d47c1641260f04154a00090b0384c1a1800030300301c0c0307040c0040c6031203000c0a82c1c001010388045200302c00e66141c0f04101c0c980540861841a000f511441d41503113028100b06034000c0c00003070a200701f400300802002d8001980c54025a01000060f0340d64444004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 103158803 1250 103157553 103157563
    0x1503060604090503130e0f010605130611070f0902090a0b130311030a0605071e020118020d170d06080f060c22080703150f0c050a050a12060305010522120e03 69
    0x5d645248100500092401052000d140c0b09007503e898660780c9070f1300e400065855000d04907000822201910041c42890701401c6d982140a542204591140d40c6d240311110720200c03640c0200504540204282c01c1a0900f0a20f0714041c160307141c0e01d00d0030b042da9541d10b8007640c4c2261201070300322210740420b0341c0b940d1001d00040d92030b44d4105c10305000516000c00b002c2d1020b42d0f110748ad66010500384842014071b5106106845c9030f1042090040b0720511729400300201c4100440003a0b03540003040940d02d905c02011402042d04080a003000300311a8a84901d0b14204801c0d0003015245800c80010024045c802804550309105641901d031400f8040c1c0700800f10004903504101c0359481091008070a01c12943c3c980c03088500881418801c4004203070201050f10003103003a21010400030300c180000c2c50f0282000d07100d504640d1a100e000040680b9003241503e0b0310381c0c820780b00340e59100d060200b0348200042e003640004502200c010044000d5031103060ba61400f010000410185582d1140e1170381d07003801 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 103160053 1250 103158803 103158817
    0x10308120912160c0f090b0117090604080702060d060608101d071b08221502070b0f09041107050d210b040f0c080f010f081506030304120302010b091503060604090503 73
    0x811217802d6240c0c170f40d4070000e190b241d82c3d250100d1b12180d140c0c200c004007000c80c184071307061007806407046844a660f01e05540e0040c2a049911407418000761401c42c504e841035000a00603036031013500d28100411003810013002c0d9040f04070203442e6a0828004140d098a409410880c10701c0c0003000400443d003111008030410b44002c1034490f0009101c102c1c0d20040c1180c0181c40c1c00904540070059464a19450302c0c07032110012000f50708800d03001c2040015420142c03034051a05107a00e85481c50740720001c0c0450341c091084a00015020400300248101000709540c05520ba04080204010844403c41003440311707614841d0140c0c860b4a021110b803955000070300c810700100b070180120403401c14080c2c00d1402c112007100211444600001c1c0100994684008071070407040070b0301c0c555001d41c6100260800c010102501884200800500102d001d050913890500960001070720b00441002c0040f024005040030365883c82005080340641e5010a02581110088030b000501e4041440e080d41540a609 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103161303 1250 103160053 103160069
    0x5090405070f05040605100e030705031207060f020a1b03090b0703110c030601051e030115030c09050105031c0305040c050a12030201050901090302070626010308120912160c 76
    0x4180000c110380010300006580301c01c6038500005440c1c030244400c84074944100c5030b0229107408542c106a0046244a030b21071300c0902911401034131400868504200a18070000c1e20748001111424401144240d4010001015096151098a00c0020319900d6903201d02034500300e10203644801c02d03000c1d0810400524460150b141c07218440c2c20083d00705000038088481500406041c002c1600d000324003681a83c0c0c2c0184480640840c1c40000c1c1c5101c0703a0f01c80f5090301907584844c0c0f0f950301c2034800071260046114559880d8401c3c00c046a00003074034410791105010b640241c4000407004030b0841014000600c9150001d842e43e614240702c048044154030464106524001c08102e107451212031403003c5000750024040c076110382c0030160890300d0441700540180c002c41001d00c940313407140e001c442e010340ca0619100054100c00807103108040b401c1e40101e0b18840d00080d8154021801d20f46e0b03e5101100802400c404005507801d4021441000d038020304268000113010200101102c440000d080c0312 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 103162553 1250 103161303 103161319
    0xb0a03021903050613030e090c030a02070609050727060602030708030705090a06020c1c3201050703020909010605070201021c0306030f11030c090421030902090f04030f0512060d02010905 82
    0x6034803998400c45c0c80b060160b0001f1400c080780030507800c00d000481e0080e600300d04610b1440c2d59983c0880c1c0250800171040f6002c603160805c0d600810810414000502400c01141700040840d60a0052408a01100c41c00441c1000d00800c81180c020003034440d0290400c0322940e42e947e07400300885041c442c01a0840e40111882c1000c5003a5500190310711558800742e40082170700528030107446107022144401402c0c010b01d502d00303800e4080d428144a408141c3e08015804c0d075403072641c1150940d07108541c07890019902240140d11441d092a50300d0050840d41072040c5044210740001b516000401038510a810a4a5103000014482da2000d8025500074004405121040c5091181c0350400102c05201e4403481d03442146e20701e411800c040c0a01e9120080644800380c0c0112002020b2665820105065442c0780740c4000d80c0303445136160300c40e13066000e50381043d02c0d0610300508015403010288080080910045034440a201b10054200d41e0032140085005090301c0100c400d0070075038006a80103980 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 103163803 1250 103162553 103162561
    0x504050306130312021303080f0c2b0c020906041a0a031a1005180603030405060c0105070207080f03090103090f06110c0f0c0109050f042a030509010b0a030219030506 73
    0x4440c000441c070318031941d5040c40219a0981190580c090b06c000d2412504034044104001042c005c000e00c0d103030035900f00c0c190408082d030351001d0521580ca010840b0162411040c50600d1007462030102d00100f09050010b902002c40d0003040c04504001c010b1401207555203030100c500884d0348005405c01d000100418090307500c07450075200303060401142141113040240400d02010380000c12000f5180c02500340301c3c200440d00300782485040050a6160180400c000119444d00d841e00181310703203038036003001040038108000300902d08800c035441403109402080d60a08003403800b00c11601d0710360702480d01180004003814a03041901c042c010080500780b81c41e00090219000a0241650b01da03803000b0b664121410000c8142c568108180c154006050a0003e011620b8408039880019002034400614004411703080d00340300064038060184110300250300b062103907050003882e510002c40d030002d12215114001244448241d03000c000d00c5140c071035440802404a2031144001150004112039450038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 103165053 1250 103163803 103163821
    0xc150c0a020106051f12020d15030212060114040b010201060b0a08180d08010320041109101103030708061504030c051f02101d1006050a05030d0c06020a0504050306 72
    0x10000e14900003650821000141529210a9180c00030000004884540010f16821110102c001d0f0340000859803d03c01101c403c0200d121303d0041d03074504185002024114010084801c4c000d0306408140da2242e4011b104092640895807a104410f540c0070419000c0c132001070b405080070360800107502c1004034070342d10702076441071300a4011240c5103d908510b52920441d142c48880380640d040c04104c12600400c0000d0000d150400340380f10700d203214185004000c00243c00d8400c52510000b00c2200032541c0e261506d002031092a550420b401c0080080d8882c240982d103d0000811190a000100001a02c86d0710f40b0075031086890481c1401c50703500d03a00ca282510340e03c0c1c16400b07442d0180d03d4660340e002845200c5203043c8074800481e00144030014042c603015001c1d1214604612601d9030a540e0644107241c200820101120501c50100f245030824080c000f02072035940c4454800d174441050041d04d103402150b034105c1160040c4025a85100c490026035040c03256030300240d0144980300c10801400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 103166303 1250 103165053 103165057
    0xd0b04020d06031e0f3309120c210c0c0305060103060b0906030a060506061903050115020106060f0503061804030309061a0a0b0d091202060405070504020414060c150c 73
    0x81c0b24035070908000c40744035102103451a50715801010612501140c0000c14002000c01ea1802110f4035140a82c440d036240c80583e86031170454000c0c21030b450b40d40702800c02815401c103813018219841c0c015844420b0b625074800c100000290712102b40c28009207856400e202d44000e40c6825005000c00c1e032516a41c2c5800e690320882480300340e4284c4c1ca00006075000d032400e00d00c0e060048000400806881500e5200c8100402014103070340e61108007084080b010030801c0b05409804005514005903c1d0700d4920703492036151584c0c0b410401c691510205102d001d40140804a502c489450042d4896552101088460451001125403101c0300c0040004150341745e000515031038801c200500554079a00d03092200d40f070f00c20720290750282d2142000c0c814002e1820282000c126042c20100e00c08105484124a50200c9010080140c008004000902500300149801048156000c61603d807416005030004440c01039070510422001076611000e0300c080180c66695001c05150f07440c2401c111401d400c1c10307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 103167553 1250 103166303 103166309
    0x3070f03030f02030f0301090f06080105071d190308032206050402104407021501080303010609060309030221180a030c050d03051e07020922080d0b04020d06 69
    0x29800080303409200f031021003501c841d4403e01c5030480c15030342004035a001800030845060800380d41c0e0040090024000d016842c0078071299116184141c0c0c0e5411403d4641c0d0aa240d103034001c10351080c155205400d003d801c04120703500010302640300c3c0c446000d01ca0802c288003e00302100120382c00681c0030300081d80d00c520f014901c216182a0f1801001205541081d01d10882c030804641c120003000b01c55405105000300c01c0d016042072030399200100c0c6440f03580c1c41d066403d100103078883c00401e2a0081074039000d5001d0458640154250362502d9001410300240d8007441040540310125501010b00802580c2e50904411002c8004891244200740d09500311408015011301a40d505500608100d030442e0f040e2038001d8010f040301824401480008200c50400b1810007004000b4401c483c90404942c088002034a10701c1d680c0c5d60b07154010405580c00c0039061031925821655100890600040c225042c0c9030b108400c1d0740c48210340b00c40395006011800c030054201d0300009503410701506c01da0180040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 103168803 1250 103167553 103167557
    0x625080304030914090928140607020c09150103090f050102070b0f010b09030703080f1c050406050a0204050120030c030d0605040606020a0209040f060b0a3c06080c040503070f0303 79
    0x904d81c003400300495200151a0180b150f001200541908054200a0203420b0158460752070b050b1010741da00c00c0594020b400080b1a60050400d00c07007055818426000204821602554181050f100002403103004080c030506140d95007040b9030130410b544060a0b00d07150003800840d1107285504055500303030300c00c030380b00b00b0442c21120010070703400c030f0417802c0c7d401c3c101c0b01600812400341142d84074080c943c4a103010501e00351050004258000c00c05c200408807000c0807d01041c1d9041500d0240305689016080000c99030060000b440030742d030f02104210000c0c00420000c49916400da001c941548110400e501960100180040c004021a0006011074105032020030029545040c12a21103d4903d002541311501c000441c1c00f0642c2e4264041a00340161800901c558848001032641d0360b040e401208511440105602c07801c680d003511104a85003074810b620000f040340401c0c0300c8035000d80108818031000318081400c0c4a086801e8034060407019086812a58907410344000ba07080611081700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 103170053 1250 103168803 103168829
    0x20012006150102060903040b0f0702040608102a1209080a020d0e03010c0512090c100903060b090403120f0207020a03030503100602010b060414130504060510090b06250803040309 78
    0x2210303501c000307103051044402c517000c0e505103824a8017280181e032141081482d4000144403405c090381d11b81c400c80c0c2c0100107100041440f4010300c00700e5015103200c102c0724041302d030740540015000d10f40140000005095843c1c00340c100c22403095404020102100054034035040890014102900050307000e07012040c585030711040038481d0080500b60741c0040b82c3c02c6d00180d018030840b0203540200b540c4940084004003651032005650700410380c00c603080301811000400c100c00400500c030280c4200d04161005903600d200c03610707107900c001d044088604c4013020503035550041100040c3d025819244c0480d801040085240e980e400e0050064005035152090040300c10300000e8101d005102d040d81101c0701401d140e083c24503002e50000c40034803a900d00f5811000e00750300190140080c0c442c5500c01d070300c41d200003da81d060410074076814103429080445100d2402210050f0740e0f80c5c4100f6184800c4450026103820685c1013103021002a8150004101d460080207110800d5003021043c015252100d000b68 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 103171303 1250 103170053 103170091
    0x140f0c0303190f02070b071209050301090c0618030606090207030f08010f0e0714121501050703020c1c02060408030c060f06060d24060e030d08010320012006 69
    0xd40c076403084080d4140340300b81000907400700c140508000d4411003000d0054440341540c910442665a1000b60116100c40c010b0070740c5940a90860429005031100390000c01070030465035108403162405000300c0041c082c800078030300c001d80300004070f0402666019205200070ba0340c90021070065000180110f01080c0d0400c01c0e01c148510443e145412507544000d05403480f8074100b03d4000001001c1c0464040104043d4a00c468041280c001c0008298040c1d008480385056102e542409490300c40c010b04004013002a0404294002041c0c4840b200c1110300809040076603eaa080144072840d009400c04000303e4005030180010000d064110610416100b00d03980e00e1418039480034044440c2c0350322000a01004101380000da100c001e24140030f0b0b0106946c581d0300301c00324031624070907841000000c05840c16081d060605018504111000303040c039441c00d50460f6580081d109120300354113821444074142c0c4810b0b84c81080462101221078205415070543c2c0e001031034a0b080101c44500743d102c2c85200c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 103172553 1250 103171303 103171309
    0xc030304141c15050403031404030e0312040602210c01050c1b03040605030a02090f030601080309041d0703030c03092c09060f070c03020a0203100507021207020a05060f07140f0c 78
    0x40007500d0f074000030540d91030440d00d4298005243c0a003003901095640c00c0819400e02210b0000d0b8005c0d8025161710700180c480303908262403d454420201540070007030008201280c0c00182c451101d500c081e60011810320701d80c4e1141c1c0240507071b426041c065070800c82441090b007100c41c01481e40e4000403100426424104071301c280d81c0e12031032207484002141040054100702c5281d01400907000700400e1a03022009510000c2c0c5050000e80042100390000610074501c0e00e000d109403540340146980c0c4042e152400c0d601903807180b90341e05c4040d0038840c0501c1544105441610307000c02074440c0201448101ca600f004100204030b20b52080440c0c0c800c882c002c54100d16001134110720560000041c0c00080da620001144d43c0303a000c2da400c80030f6101f100280801a03400707002d0349503030240e0114001030520b02900028a040b10003001d58901f80c82c10814030300561142c00c003900980d80199511643c0b00c20b12000c40c04144074149001e0402200d00c41079804071a804203c0c20300043e2200c08482c109200c040030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 103173803 1250 103172553 103172599
    0x9190f06030204120803180a0b07020d020708060606030402031006080105010311061e0c010207050106031101090501140307050315130902030601050609060d0c030603050d0203040918030c11030c03030414 89
    0x1400007141003101c10130000030011801550310050781c40d0010b96060a00219501e0000c4061085032581c03481d0b010403035441da040201840181c601c0c4001c0051901c0c0c01d8102c1d4640c1409010140900c5c0001300007004d40d20304100d141d1489a0300130381005010b99590045c0e008000c2800212620044410203000c5481d050ac240d812021080d1081d21f1506a8071917450410780c0040c40c028180d54023800702d440440c60030b00c00c1c00c0c015801940c2500e030b25104280010428040754014505100d030302c00c0720032b01c402e0340203068a41c82400750030001c1d5691074000301000c004400008440d8041100d072000302491803d030300a001980c0c825401c0301c049907217903810441e1600841c448107400000501c80c1d101e8180d210b0b00304148020382ea0a00280550710394550904003c90901220096440010300b008502e00300d02c240c00c50420500c115000c20030140d50000c0c81c0110b09000070b044c02d0000d151403081550180030f4524110760040840c0d035039580d1030400c10303250224542e41a1040f1110b0f00300c42c1a14890b071103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 103175053 1250 103173803 103173809
    0x150906020931141305100204031b0503010e10050403181806091e090c050306010b0c060f040f02040b010e03190b160c0305180406090b042306120309190f06030204 71
    0x603a910003a80c0f20440421311003801101900c1910540c20600c1b07021100748000d00145003e505e035145600340b40a08500d00108079032115019a26040c0f0340c4040d00c0002c42c43d03000320481d200d8041940d40315410115009501d4080030540b07070f1003c10f0005204070308400f8070803000c80d015109005084d0b4071060a412219540340a03050140b040c49a0f030a00f50480e0702058141c1d114010158450740c448000c80e140c810240c11000c1400800155001c0f90401084681d5000b011a18034043c0c0d0b2516580380c020300e14404600a006a845a1140b445070380036207a135210030080030382103566800300c402c60200d02e4150340000f511030b80b103800c011403d59a013440541c00300c4c4086468018040f001558111495484102810386440a40012564580e194014407008028001011504043c0c0034100400c07559801d8100b1900f07018803400b0300c0c41c04114032030507030702240464460071701030660030710503085206d82000283e0040c40c25085141039124230341d10744160303640e04116810860f280c42c030540c12403140340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 103176303 1250 103175053 103175081
    0x10e0a0308011202121c09140a0b07080c01142e06180909030905043b0703020306090604030305060102070b0f0904020405041415060403150906020931 66
    0x81c00600442807810966845035102a05000088000071103103030070200302584d01d825079028002c54031882c85d405a103401c0500140900716242c3c1c06d00c540000c103d4081403081030390007600424503200f4030007807100f502d00d000301c03510091000030308010507032043c03410450b0461a00408d05a10464100584d1240380100f007001c03505015207400c01340c00352002500d800c10300030300c448880004a04d240e10b502900f5040c3d4465290321921904010400060b04c2d00402d50b203070224840b100101c2c5692100d000d82039102c49400d0682c0c070500020403010b092841c07030741003c1c0d094820700050048a0711300207101481140a03903800c110345d0302c4010049031a02031500c40c2d40f40d444020320503403c00d422032000801110400900062410b669803003c00c094903070740c480782810b07586000c042044810f5003070b010041c1e00000302d8201e4540303411540c40d07291505144040d80700182e500c010000400800da41120794244000708a09460b400035402e0281280c81c60101d0685d2280312501c09103000b5040c002e4902001c0c000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 103177553 1250 103176303 103176317
    0x40b1812030a0203090f0a0507061e020303150105040f0608041101020606060706020c011b0c060515030304090203061503010b03090c01030b0d0605070c060c0201060504110a0207270c05040503010e0a03 88
    0x102c02a0003942000c0c092070355034002c00d10b000c900280100030300f4500b540f00d0409084058582000940880504003450314040118490010300c158084226588080b020301c1d50396280f0360349401200c06004075080002030415200c03001c140b481c1c00c902054400d0740315407000c1c0000c0303030103400490301c0b0752013584ca00e038215009012210004000f900601504400c1400018500030742c0ca01950005000e5910130011400070106582031290a024969000c00000710047e60740d0f040c0c0c004240d6138802c46c030803243c5a607400f0012404540d944481096107400340c2050369100d58440b00b4072030b00f550094a43c0782c9175104408180101354004e01802102d00001403c4038901c0394942c65a8010b000020104030801503541c1e0104006409442604641c40842e0b000065041c2400c007400308031742c2e808500455420081c0009034030954002a110155001d0b80501e0200310398007480e07500c00c5521048501ca2003801c00003140145039000c80030b401100d000301e00900441c040c4203252600c0d9040784401030009502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 103178803 1250 103177553 103177561
    0xf030f020904080c0607050304110a080303070507081e09090f010e04060e0c1e120f0a080a09120602030a05130c14120604051b061c0b06090603040b181203 68
    0x220301d00c80d9116028042407881c04916111181c2081c00803142030010801c044180014008580b1502c2c8401405480041d03e043c10300c014039a507408020004400c00c070780010301070104100b850035655103403076910b40f203d591707250b56400d44015040340c80d1541c02008003e0000b07007145484901503049403560108140c0c1034445440b800c002d030000c071861400c02e2080038070009a070740b40d45410b814001012076111403904459010845038008031002483d0a03401121503c0e0941800b0607425030703955108000360360f241750044040d54004029440500040e00c1c4202400a010003a00190312860340350b00200141c0d5584585210102d091100140c01d03542d04c201c01380311340070205e0250782c50f00c6030041072000e040d004200440c3c0341680880741140c0581050707041c016110724600104070b5080301211080c0c1880858485016a5002212041d420390b4540b0b040d0b0b203080d110101114103040014000b5640d03890681002880d1020680300c01c5d0862640d112a6040c6010102c0c1e000c0c03e0481c2c2089562543d21 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103180053 1250 103178803 103178809
    0x31401240302150405090406060509070203070218060d140102070b0a02030103050a06050c0417010f0c0f0f1b1403090a0f060c0f0c090e0d081609050105160605010f0801060f030f02 79
    0x1038000f0f00300354540c008200206680d584e1101c810300c6180f0880c00494024200b40901c040c480380034020320f00b954400d1000200507070320424801c044103407440c0c07090303500d07942c40001410000000c080a402d940c2c500c01419440312064006248450240c005038180d0b8444401b100201c0c40244000740080d040903074030400061031600601d800c0003000c9400c504180c0c40d11200c0c04414504030500d0540ea54031107001c001404240542c100800c0142090380c6d4485d59113502a11503244034400c0d1341001400080300c0045250207500c030031015040030050401005420321036a59a21480a9520580ca02403000032051f000186c5002619180e5413580d88950740345e92088406844460700302d034685860b6a01080d842070700d100e0341076121181c3d4014056812840d1020341b841c44040c0051004603400140d4421681c6c102c0c0c41841150030a18000350342e486800500c9080100c0040c000700f00c6401c00c400060300c20b04d20300a0301d080c5d45441008005848d6120440591108640310007440503600b4030f8840c001d46 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103181303 1250 103180053 103180069
    0x302010813060b03030301090606112113080a0b0a05130c140a03051501060f0302070206030606030903070c0306062606012c0112030e040e0604080901050d06031401240302 75
    0x203202d401c000c640c1e100c1c0c0d400060f01316002604070740412a55084200030850780200b5003440340d03020f58040c3c8004030203003203940c0c1401d41d40c402010f001c8a001400a01581c00c030300030400209080420340e10410b01d203140c00c0340000700c00e80d03a040059040001240c40c0d101a50120710a82d580030b020310401038a01001c110801110b4040180c2c0058100d8000010403000d20035900705c81c07006074032640d0319030510b01b000d08440c0748282850304051041c440c42c00181c03515803c0325080303d021207940c0e40360360703881c00a917146104501e401484c00d0b10300380001003006402e42100003034600162060404040b40d40039030400501494001e50580d0100c80104018031004100254507299540480d448070150003540c01c032050282c0c011019060a08044402e140d8003603041c0f22109401c8506003e01c0450502c403943e80d05000d04081c003041000104061142c0c0220b08a40c4001a03868090000340d5890401080d84141400c08001d19400c1900700384044004490401101485182442d110360654007030013006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103182553 1250 103181303 103181341
    0x31510020a08030a050a0509030f09150d1a101b060b21030406030c050a0c0b0a0e070e01031406100e070c080d0902040b0105040506040509060a0f031203060f03020108 73
    0x5406080d0801c400708603004019882020f01e4540491141046505501242c0c1c0050a88800340c0061001c500e072502c00c0d03411248001d40481d481d9408080124a10395548079040710340211a04d045d541c1d50070940f50300d180301d0300d01d681101e070b10f407051204040c152a80d514085640c400300c44d0b51f518003c0020aa580104404100a44404070124010041da003036003103115400099540003040400030036601d4015043c46244a140150821010b114007071b10b42c9102c0d09001f0201c000041c0001c01c005501c0e4004924178110b00f044a22107a07a030741c59180b0744102800150307000c4540f0b81d42000c0c011000a0401d0144d500d038248940c54520300550001c42c450054042020809412207010100740310001402c5004450440000c00a14030710400c4112640d40420606010061000304480c5da039000035201107410a0f10804200c0d500c003c001204400315802c0054000030f941d4011051001d2041000410186504d0400c48585c85541510303c0d201c444c0701c000c0c00208250300089040007146544155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103183803 1250 103182553 103182557
    0x140405090a02040308031816120809010c060f0c080c12010e04050a02040c08090c01090311060d0204030c03030801170604051911030105180d09050603070f020a0501020d140c031510 79
    0x1440d4585c0d13114802d0f41d005440940c04107484d014113442d0350006000d84682d0b040c1c1500300400b42e52400b890200380e0015210058100b0b000230032120303800d034000c5606501c0194013140400190b04a03888480041145d0f005c2c090000301540c000503980c038041c07400c44288804611040b04240c1c60102c5514402c0d0005104980380c1c018500f5040040c2c03128092910300c0706568850404901c0d003e14107501d405400c0750031504100c04000100045942013440c00c0700000c06840181e42c1d9020040081d01070b04c1194001403c444082c800001030652010300c4605031034050036504410081e10403c19620b44040e20041e120750048101e1024018040f4034003020380e44912200b260782c040c440000b90031180704a842e0102900045c0148070002c4092210300064a4103042011145007000049009800024040c2c000d1002021060318100e0003000303410b000320391000c0259606c0701d50010078406010b10440205040e00d0b03050204281c1006003065070b200f50f03420401d80019540003010009014090300302c00742 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103185053 1250 103183803 103183807
    0xb0406032007382d150102120c070e0c1c05070e060a030c030b0319020609031f0603060b09010303080a050c0d09110306060409081c020d0504140d140405090a02 70
    0x4024520004000200b0030341001c076032494603285520800c82c43d0705040400513601d4a00540d04254212611280c1111200c618140c100b024000141d00c0d00000d80e2207141182000700d100391608000085181c1900c14905281c903040e100d00203048035502030381129031400108040303840081c1140da0b00156106003d0318082100e42c4c010b20206541d94001810040040d80302c0d4803007502d464040c0218101c584060300104004000340b038584071992001c00c8000e1003004009019040c99904000440c00c0c0605103d0204100030300a180358001c00e85c6100490f905c50500b5085801442c0139941e03035048a8140e01d0320611940c4a600311001000300806000c01014140a400781340a120706c101981c40c0d105601c1d220400100f10201850b081c00208090311950a010f401800106030000b6600020758020365107000001e4404888060b000d00f10350034554520349010041400003220140c1c4503c0812070503142603540043c42240c0c0b00081100e00c0d01d80420821040010b0708010240c20740c440a5600014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103186303 1250 103185053 103185113
    0x10503280602120402041a030a02120313170601080601030b070e0103060905100e0f06100f02030c0105040f02120c030d11120a0801030c0608060f01030b01020f06010b0406032007 78
    0x3008a0f00150a80c5002c8a000300070041141058811042c02001c80380440a4aa84100000381d542a001038024000c02c0980c0410034003200400a03240d11a82080c00f50310500d44540d4242d800018110555041d0b206540001616090202c2c43c24140c0340c001c29080a540c0d10f848007550541681e8507014101642c903000019482200e1003864018010003d4000a203070cd480000f006100000d4038018050021030148100340e5125980e00e40c0c0c1d140d180c1000465003a509405034114060700c4800c1f00720303500309420001005403030842c5418072442220190a03031900c180c20240d41d13050820450b60581e03c0442650081d80c001c00825000005000c00ca90700c05200001c4440241c10004000b400b043c150700042c400c1010f802d13100c030084d224518004036189000e2000603130700c1900007105814155142c4188000381d100f44040d50159007040103c50345035039150551a42540700c0c0c452240080d10b000d200341c02e0026000b0200081d0b00c0303683c41d01803c0100307030b8a80d41c072180c802c080c80d40e041c1019240c01e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103187553 1250 103186303 103186313
    0x30315180a0c020c030f060a0903090e040501020d18021005131d0105030f0d0e09041e0f0b01050d02130515030d051801080705031602031b0f0c0102030301050328 71
    0x207489846035803000700d0b81080ca40400b80ca06060b8254031803180d00f02c1c00122180d07001c00100140e1080021201042a4030207040545402c0075a8101e100a90b91810803c024008150002c1180030b0b4a40c60400000c0001022400c4d4003401000c000d40c041106da03003d100302881100600003603400b050300d40000c550b0751600d17030900d80d40d211000c010103224040104400e00e020f03c403001c0d10720039400c0507008400c144003000340381c987c101e5403a500c10b00d10340e8003103411320600c03072503020218039002d5048617682c1d21818a00502c0b500d1110458001055038008105814043e1074850450703806010b68140b80380d01542d40024200c024144090320881140d44842079a080065100580e016194556130f02070f680140d00000030740d40d00d040c3c10b00c5420014000d65075400000c40740c1c000e680542d9140070b044a00c80032802e42c49249010701c0c1c1040000070140480d040824032803e440c185c4070864041c04c1d0803000582e10390100348030b240d51507002085910582c0d07c130b200352070499406001103840c1d210703490303075a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103188803 1250 103187553 103187599
    0x308071134030b0108060106020a0302070e040c0515030f060f0d0b0402060d0504030804061b050409090507031203021c090f080a090e0106110c01030e070b0d060f120201091502030315 80
    0x10b43c1e2164441004010059051110341d0150a80e07101800340d541864074041d58a031030034458440b001e603e960006061140368100c00d006401d000703000809035400b004119041d43c005480e80d88a02d51a40041401d6240c556469450b41c00d02500000d41c60b24582c03900083c600004000b84d0300040d003004800d030350140c43c0c440c441c86a44aa220b810140c101030604004441030303443c03081d40341d49000e544002800e410105440c02c0310360f410030204d01d0f0f442900d03140e0304081103030b0300013000c041d1101040c0303400903090340140c411721004000c9070640003024030080c4142c85212201400e1400d070010102d0100b00014000d00c030300701150070a00310350365640340074103503e4100742d0121b00003d08841110800e4001802030a00c01d40b424a420312282100d4181c064694002e841512414000012151811741c0d00745c00074401800c08800780134560342d82d40c840c1c2100c0c012180b0f04900054440f000403517072104078040103c40040030b60003035055030340741045000c007107180d03031315050384103034842c0310603180b8070006003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103190053 1250 103188803 103188809
    0x1a0114070807061524021f0f0e01050a0c0206060604060e060f030a050a0f05040201020607120f0e0a06050f0f06040f0204050301020307110c0a06120b1f08040308071134 74
    0xc08420310f42c40d015095104208100160803c500c0c841450110603034000380e14140759000c0346101f0390002c02004080010408205202401801e00305180c8484a0641c0024030444520005129120300103801b00d0f1103d9040f91002d81c00001844188140c61082d11804240300c0c0c00b81401d4070740007129041000c0c0380c100701c4120940648038000c00241108034001c0b82441134900205115604182e80081e40700d4070024810801c0105246850701308040d180c2007001200c0d00343c2e401b0007909000300c21036500d0342440d0606840741030814000c2180c1c0704100e00c1d0644650356001c1c5160160311100108400707417507050900700800741c09003c085120b503400e20003107001c3c0c917030390300d41d0500b0102a58500c1d041180340301400d80325548001040040503000104802c10484440001884502030000100c0030f0550000882da50341007108002500c58002100c0c41c007460281e2a40b034000c1e83ca0355403c030340c40e4620341007402451b04424546026000003e02480d0004c4000c8401c00d01c0101c048014000880168 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103191303 1250 103190053 103190081
    0x912250b15010905060a050d0b0a170705090906070f050706060e0c120124030902040e030a17010801050106171512011413020a05100903050303010603020d1a011407080706 75
    0x241d580d240540e00207141d680140700c02d80f0000d06040044c070020300580a01051081000e4440813190555580d0f001414050003640b00708414a12203428100c0c0d403071005000d114062648900466101c82002400c54400c2c00781c1da8500d0715460542804640302d8105400443e042900d4031000b042c11100491030a2083c400c18014603242c01c5048400c5c0720440c0c045c0c1c000230010490200c0c043c840d81c0f55018000300004107041c0826504094030200d4014140a070b26001240800700d440800391394800c030044520842540c0315207090762900c650718202c813028403842011a10907080030f643e14142a1400364080d10301240c2800e02255603006ca1745000700f1170708414150f5512071420072420b050aa441da0046810002e610180840303501050003001103003c5c0d2885500c000c848807590a11610340301000e907601500750717600d0796034a4074060041e40114892102543c206102c0889282c10000701c82218001651401e202848505420300140c0c8031352004c2c0d405001c01c001c1040030616900681010182c1c81b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103192553 1250 103191303 103191331
    0x40f0312030e101e05040308070509030304030203070e0702060f06010504090518071e0f050a030809120307050703020109080a030816031d06011a1c05070507051507080912250b 77
    0x100d25981d43d020441c0d6088801c4c24a8142440003099100c07441917403140150a04a41e00d0505400180c9940529407000354107100fa040e001c12401d5890618901401c0c45400b11403033a182c2c5400c0c196403c0049556500003030f801d110800c40c40f588d64110310341220782e50f542c0144043c2c904107034a0401c1119001091031180303120348032050400c614032803002001c14242e602c1407141048001110305141e844040e140c03013804a05102c043d07071140308020380041480103c80c2d80f42c5840c50010703104e850703d100a071301155140c0c00000312200302085007480698180c1d9070b00d610741c0d0380c980002c0382d40d41da4685031420950384168500422202c00d60962403080544014181c6600d0515003040196080916a06100c1d05000c288503000540d55030b0800c0c00700785507000c10f480d59200003c131660f00076180d02420a10071880103c01d2810f000c081c0310300600031603444458070f60320700f1300c41e655811404802c0f8010290800c290055488044100c00f0190213009250105092170b8840b44c00c03604054420310504019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103193803 1250 103192553 103192571
    0x1303052509060f0b0c0c06030403090e06010e1f030b0303070606030c06051309020c030d020415030b0f030712051903080708130215030403030e07060c03030b06040f0312030e10 77
    0x1040c04840081101003001e001e9641000040c80c503404140c0304442c2d00c2000810104210001440940200000a0036681e203070f107030034100240248030314410030844034810320104203194403c1d40011a540342c0030b4050501c60410039000d10b20b160f0620f00002c00c1550b00c01c00501955401d00c002c05540b8020600030070006d0450034801c0009032140c2c40141801420882103104110482c80c000c1201c040003801a166160811049d0a500c42d40602e00a86440000c0104a40c1e021a9121085c00c405079020070084001c10244036111041ca404150300d03620929040145246d941d144d03420052203041a2002c01000d003100c3c0b003440714401000c80c04076888504004030b4641c0500c1d080c0d4080701e44105c42304108059000f0441e00900c0066009820200100190074180680c01446c86141c080381150903031a83c49000030011030321141b0840000e42050403850062500f40c040c0d0b010385c4d6134102c5a11032240346940ea2410100d90607110420b26465049194440c03806000558002202c00408204400707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103195053 1250 103193803 103193863
    0xd0e09060409052104210506090703020901271406120604020612220b01050a060302090a0501050a110714010f0f02150702010902060309100513030c0206130305 70
    0x2400030041806507107400441404540002501c51072803000010700300d1101d00b51001c1d841240302e25040034881e00c0144645130740480180d07420740e16060007035090700c8840d20350148840e25410715101c06580105c0a100500c050108241c0103002c002c0f8040075030f4040407100e4807142c1070f0b402c2080c881c3c48224100003040000e0078003103909400210800058078051170b10381d000449038080c020010200045400008549507054038034611811815a18030703081c00001e150844003d8824002e50340580e06c407a0340080c8090281c000c1d9411f45000600b81c50750030b400d01004490a070041000d00b020094036052180300100d082c0800c0303003d0585c4001d2000c01c464602c0024080c0540c503d001003c0003013403420812043d6002c241d205003d00c540245000c1c2c0d03124610308038050110800065405407002040c81480e460000380d400741940d84001c144550f640c2e1021096100c03004500113004900001d954800501d0444000e02e45a034140551141c596281c0e1185881e200f2640000c1d040c0302d0300302c4a200c4a004d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103196303 1250 103195053 103195069
    0x3090501050a0207020406290a09030f050601080106050d0804140a05090c030115050a05220504020a0225060903030e1801090b0906032e020c0f0d09150804080310080d0e 74
    0x14a946200c1c0d504e0043c07491800c81c1c4448c1c400c16500100d0104040c43e0302c03486141001e0085412150303400a115690070085c0c0c80780740030700c03500042e9071904000042e20b0030400c80280ca002c0d049140c45080514144541c510590b0441d002640b1400140001c91180da0f000c05450144500905050300c1e0f604201300c41a0700d178032050b005000c2c40300a1042c0300c0000e81c4101114072450740d60441d48620216902c0550300c0700456000745d80d000d4008241c0300c0200394006050030443d40501c1d80320718440c3e1500c14030021241d10340604400280c034040c061011901400000c00d0071080030744202d078405090850811105070a800a000c00d9486107900629850f085003d0360300908128007800d00034614401010700766403108208181154120103000110354144c4c1030b1183c0c440c2150076a2110500080515100d15190b042d25001c00c15a91003c241011104e1444420007038035280c989054985450740c2c94540c000414515800740104000b06040300e0611801007e200c240d100d040140c07440c003040000328 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103197553 1250 103196303 103196309
    0x160302010b011b150902030d05131d161404030c03060b2d030a0212150a020a05090d02060c011b03111809060307090908091002010515060a03090501050a0207020406 72
    0xd9503481890a83c0c14650359120994004603485580a1401401014041d000d0000e50326001c0c660605007201c2d0403500030f00b00b1110388030041100307503210040c070038000c2555009030403800c90640c002440c41d0381d188903060740840705080601d0708940c00c8400d8182540182c00c2101e610081240c1002004511302640c10302d810101c030307184884142d0000c0207100f40f83c14501e50454010075103120302142c0b01031050048035900580349039508003c0341c1c903441ea0f4100c000288041c5030580713800075481d0f180301e100f41c1c0c007031441c9940e4580c0b4045012040280300029540240e81c846401c01c49000311020034466040584800c0e81d20112000c3c41c020050111014200d0102c112401007100f00c6030822a01210b50350104101c0b101c007440e854800100f813030195a9003008400030f282803140c50512120b08003138006003404030b816084c0000c41d80c0040342a41c005442c0a80e50349a02e690056441ca088000360040305001d1800061528240c2c03206400d6803010360303c140398076600180001c1941858024680030f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103198803 1250 103197553 103197557
    0xf05160605070b0a05160311130b0304140a0302061b1921020705060415020c0f010b19051c020103020d1104031a040f03050d020409090b061002010c0507020111010b030102160302010b01 81
    0x42d500d4090804041b180e40e4814070300030503540f405140f4404201e0401e64180000b028910508070380c0300c05a210710b036130090f10150750340c0768030380701201d507500b000103180000e03031b44c180d0203401d1070789070103c2c0240081004c486109106000384000e0004402401003032041d900e403955042002c600403441880c0b0f00010841c1e58810b640108034000102c0c0c000680f003500980e1048000500039045040e62001340180d40350101326000f40d000701c1030450300540140d40b0218041729042ca4011550742654000710861050582001c14158003080001c0c003224149070247c01810054500501c40010310222440c03250003040021021806005002c42c03410789034008240e2000a150505040c0c0358452180040c003801010020001407020740ca215940689009010000040c0840360651804480031401144c0241c010688400c4101141d031050080c4d0700c1aa40130741380c0340d181410039001128010344c0c0000300e0146d1f648a008200194500344001c0c4540b01d540000700c986c4410ba49002030a48bc045010181 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103200053 1250 103198803 103198811
    0xc080406050609060a0612020c07060f030b01051c021b0601120c080303040b160210060e01050f190504020c010b0d050a0c0602030405090106050a020a02100908280f05160605070b0a 79
    0x70507a10768910100580c2c0c018140500f4100307030b000081020788a03900d275884040c0070f8035400142c86500151018001c0c4a42d031014414100f40d60300444481c00b8070000c20200c41c00174040340c0c00341030160303008041030b16606030000c4218140410f080d14196080c0c2c0111205034410400c102408500041c01c0041c00c1a00041c40c5107040580b02c551880c200074001100542a11000c4580180200449488040e40e41010312010b503541780b0410409800f445501c0c0580040d18100d00f1510308040343c000101401014003042a007007a0512000390001e516520a80d0742e12a8100c071565940401522064842d01c001c200e000300a00d01100c40801c02e074004000e5500900040c8010780d94607a9040c190341d4035290064036402e089400f00d2610311440000303904101020740035011070798441044416a0040004c54a64150402903801e03000c2140b56060300880c202000000007038101900c1c0d450140c001c0c170485448840346051810041c080da032010380450740001c2d112080015010341ca0b40c1c001e000890804c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103201303 1250 103200053 103200061
    0xf0906061404030221010c080a0b06090d060f0b030102030405060604110a0801050603040c21020109050105070305030c0309030408030c0124080a06091401021b0f0304060507060e030d0c080406050609 87
    0x40d040c0200d0100034814208411110001c81c1044003500c05c0c20a10740007880550050800130b80610029103110300c0703031404e12803800e005081c11700803940d4020300980580d01c24045601e5480c02001c1c0030903008240c507103a442845155a00b400690b000354003034809054281403803800c2008071281c1c0c1c01d00200b882c405021260303c1c40d4019030358904641e4281d4101d40e6958035450b040c5104192034001210409003001c0712290504142101414180b00381c030380007a01c98641006503141e0103042c1000300001c41c100000303181151020040d60b0030401000c2180e003002d84030062a0700f160000d50003038600f603544080086040100c05040440d0540404049859504140301103450303130010500070340070b543c68113526800c004800050f04483c2c21110001c5441d0801003410b903135003401d0005d20162900c03940540054248000c41118220b0781e00d512840e140c203040e0f6031002e01410341004c2c0c1100b035000501000b4022120b9001e000344650301599004803d152904d00541105c20107007444d4042e1040380200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103202553 1250 103201303 103201337
    0x10609180c0b03040f02060c0c030606030102040b0414212407050706090f02040e0304081c050418140109090203100c050f0d0605060c01091a0910020a0c020a0f090606 73
    0xc1d405461407011890703070702c0d561030501071044081010000d4201100103400d5030880e0b000300d00d5034004101201034883c10f4403003400705400d07400b0300d00410075080c1d001c010801c40d803641c070002c40b4841e180181210110038011042d054464400e4408442e4a8100a00030600144c2615a5190700c1d00c001e1051269030501075001071103030007903050041006680c3c520350030034019184100030451354010f00600c01410f0740c94803261241c116208440f0381c0d225105516000d0151112a507946a0460740d80300c1c2003074541115040482d484046085215a44801442a5400195216010304403816011803034074034500c10309d483d2142a070007a000d0700d0b1501c00c0089200c2d45c81404c46541c603910310f0041d51140003030f10701b10380100340341c1d800035500c0640066080451032064001004444c0542000c454203103661145040600003100c1451003500000c040d0410000d00768007800c203c00707071868030307500c1c214059000c1241244103400201e1503480051080040080074003501015214614080744103400d03810b40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103203803 1250 103202553 103202573
    0x1903110901030f0222080d05070f080318100207111002060c0309010617010f0e0a08030601050f1c1b0302090f04050a0b130204080c10021f0e07030501060918 69
    0x4550401d074a03141800d03c03a103c1901595801040400802c0085124a040c5210345402d489465443d02440000a207000e00072401d50f485242c01c50441116040c25a49031a402d034030041288032160600814a40b08160800c01d2022135584004010b99404171420640851000450038600c20881d601c0b032011030369030114100b600483c244d22165202d031240149940904601e81010342d0051500ca045d00440c0d80c15000070407600001413003000f0101d003280403030f0f40364100d882d00580250700810100c0d5841d44940001c180812100b0364071030a1001040410302d405d00b40c03203191354046440c1e00f03004031102100540800e6000103420214a019182c40125410703a8a40062612903541c0b030f0002030b020040742e0096604041e0041022840368104030040009400502809881d03101e6981c94520340e00306200014402c100d00c0e002021580703180901e5410306520380803514451502d03039888420803030040100310f020318881d02c000301d50a030900039000101c410b02410b6441d50300720140c0110101f41c0d2400c0e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103205053 1250 103203803 103203817
    0xa051f030506041b021609050402030d1b060c021005010806130f0206070813180203010302280e01060903030e03030a0c38071e0207090b030705060f190311 68
    0x2404500356030740340b0019005240248850103800c1c2c04c181e40d0b4100076404a01c4000c0302d640710080e42ca203141c07100101030850310100c80c025010fa02800502118070b0040010311805044400c1c5050700b4441940c032081550908000400035a2040340e0012200c0c826000d400e0240c01444001c2c43c003443c0c41c681901d030b803000b100381c040c0401070040c2d002415500c551044880c0c00f6086200503542d081035901e4502940c1c1c4502c00d2502204219070080941c00d050700859040301c1d00106074800c0d102280050a09902180a4103103c1c1500000d00217441c81c800d810b007a008107900d44a03180c15625508012305000011502d02d8429001000160129500500caa00c4400d4200c0c0640002d001e40701c1d2101d601035030360884e03c510001d1500c81d00c0b0000c481e0101ca18410b120543e034030202403000c004850704201c039902c20b143c05078000040521400300158004a1040002802c445182e0391704c00c00309041380d10080f86540e4080f000101004020390700000104110131078a010060381c0d04410032400b2034040d0031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103206303 1250 103205053 103205057
    0x812090a050714010c05030f2106010c02010e04020712030b04230f04080409050a1e090c050f0a0e090607021e030403230f06010602061003020f0411070803010e060a051f 74
    0xf009580107030748200e0b4110420b5034000c007120b9480c206100104a99040000780140d0b58048d1812000b0f06003035400168040d0307006031a103040c149001d034010350b010305a01000b5074000da03003030010501003802c01c1a403050644507078900041d880100300c244415609540c1e0203465515510140b03041e90100c484110781c3c042c868a2108a83c1e171154500340c0042d00c9261f026812250902052040450596200d8070800072049a00391040c46400c5440d0243e60840e4000b4100040c500780800c075a0402408a44542030000d055512223a1107c00c4507000074020786809159500120130440038607010000c441d4209410407070340c40224180008981e0380e22a50000401c20440701115070b0100d14807075005070ba0351009000f66601e19040f4020655108424410b18006109040110b80b100c1103800301c2805984d009041009107081034414400540003c561041c1840400c02c440008200303040e011750301a00081400f0006070510745d040100c507000384c0c0c00c030324030940214490121014080e103004034461824 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103207553 1250 103206303 103206329
    0x90a08030a0e0a05060c0a0f03060b030711010b041d010501080102070f080c0109020d030c17090a06030b0303070c030f0b0106031e090201020a06050c0a080a02090a0e0a0204080a0812090a0507 84
    0x4045201e00f405040d5800030958400c000510200812050140440e20650b0342c404940718850704040341550f015109800c091401000400c03070700ca1040501848007002100003050a8044101003011200a03540b030340d200b820600002042d00100b805a1030050605d280258100b0555858445202c1200708005001103000203441801c00402c0d00841c0480d0f40003041c104080303040d410050101981d014048945440312000d10001d5840341c0b0030b55100e9040600000306560400781c0503802030020002041d450b200c14851100014107005a01011318410582140000d400e0314001440b42c5043e040300062604003460b440c0300c91f031404046500c0400b03000012810020a00050303003442c03881c0340e021b004507040c40b040100304146e00005040442880c1d0f40d50b00c59958680700342089002d0704100c030f64010340d031440030000c80140c1d01c1404e4214044003030051400760f44041891500b1800c1c0012600c1002c08903400d01056184020030764001d00c240d000d450b0004540e0b4640781c9440c00d80c080c02241c0505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103208803 1250 103207553 103207571
    0x50a110106030f1a061005040504110c0709061a040e160c020301090b090d050408121c0207050c04061205060705340b07020a080a050a1b0f0b090a08030a 67
    0xd400603002035800801c0c00d080a601c608028a007903026500e00003210013400c01142c07060805890f83d5022405968a042c1018145420000a00311148007140c0c00d10042c80172281c901c1003031003c403005220540c4005100b5290045482030300b0103038a1000c07080c440510007000350310850b204099000568200314400180d00a5041c0c6014107040c0300690035610380b92000c020844000002401440000d08a40002c0406401112070f4400d50240d00e03940c0e04400303900340c2020000d4000c0c043c44000e03081092900119140c43c00202c1c0c0044009071210b90113412180824246440b401010b0700140d160380c0e220000689415a4641c0b0251429040000004040c5001003601034035044094001020b6950300c2281c0047c50321807103800b03c0035280c5c10b14400100e1015400000d0340c5100307540c4884100c4c1811031000040d40c0c540c0203031000b07000b0710444850070841e41900e0700070341080d00d01c01c040b410300403842410101c0107102c0c01003078042c2c10b43c000000707000800e241c0020b895011034030301c50100c0c1c6802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103210053 1250 103208803 103208837
    0x17070605090f18040c090615140a02191b0906270b04020408010e1519050c040f0305250617060a090507021c030c09030201050a0c05032205090106050a 66
    0x1102d0501190543d4211083c03104200303100581100b16408803100340440360300d034201001000c01d210341031070104805814152218482c1d002904030920140183c9035030549030100d82a030301580501c101c54803035800070546004454101410003615804004214460820b4202c40086c40800e4200c845141201039030300d480125600402082d11024200b5511181d4540740355000c0c2c0340a501e040742030f014070003c0071445045180e0051207503925450b9503c040020031620302c000c00c1c010301410704a13001008085454000354001c00d004510801c010104103a401e200d9046103208030580072030312101010704008403a4840c0000060040010108500740c4070300001a143c04d943d0381c40455058200800c2204254000c10050313481c08004640148082c07036004102c0c22100c80035904070100300744080510165100c0c401811042000c1d00b0030744c00007080d50329030910f580c014003c41448580b46445806070f152421152000900f01545c07140e116504024000d44680210300c030080400c24a4071800c038002c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103211303 1250 103210053 103210069
    0x907060903030e09181b04111612020c06030f0103030e0a03022107150c0c14130506030c0d051e060c0a030e25030228060302030903040504060e0117070605090f 70
    0x2d003c11742200c042100328010100810b203440e0b5103c0c41145030070510030440c6852021142040203a500300c40a115181d552180c0c2c98240c00c041e4401c5100e003c0c05642a40c80b000c0046005450784045500c09d50f00d1444c00500b50015500010b0190440400800040e180c840044104d0f50107809800a088145072246181c540d06501c030154050408aa900910b40c1003d1045c03641401950516132560300c6012000a0181078074455421211039078a01540400035031001d81c0010700201034070a0b000c0280c000641c5211710403401c0d980c0340c11000c1c1e0f0141071002119070982050b4003d0140005181015400d00d04d40201402d50050645500100c914103005009450081d81c51400400603400c400d04124110051400300303d0166044510a4518804445c00e0a4200340c9420407481c0a40c10080114081c1d0009404042a40300c140808182ca0381c1c2c900807007010300780100018025600d054100642036445a03803020700394100140901445900070200c9a0409054a00391030358400140826154 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103212553 1250 103211303 103211341
    0x627110409230d0206040507030303020322060515040b03030d0e1e10060b07021c110307090f0c0305040314070201090e0703020a120b03031e070204060b030907060903030e09 76
    0xc1c0e04200e40680d00b040c10702c0c010180307164000d049a124410b8480240d9540f0301c10386014116902a031410400079100e80c0085030b01c200d400f04200107807901402d4041c02484408021176003182c80b14200440204291040000a50110303400e003d02c212041c00703e034403441800000a41d071a145d0442641a0008210050404d5490f16241c004114080501c589a202503c840b01c030044c1840b90000d030071044034050350320043e001000301441c10260810b01d9184a020407080798205250790501c191540c062048400070082518081004040c0b25520800c64602c0c101d1360040c0b41c0b070081848080713580000e14140d00f64480403000e954020500042e07666800c075601081c0c110300d941c010000301a501d50043c0c80c0000c140c0d141c40d500148402c140506551407006260380540c010b0182500410f084410844e00d296415605441e2840640205050707540540000c4850072001050164844e42006030b08020001c0b03103040c802d014190b950040c4042c941003001c80c85260002c000c01c000740083c000501c88 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103213803 1250 103212553 103212563
    0x3020d171308340b1005130e1e07030303050c041a0a021501060f02060907030b060d020f060f0406090b040b0301050f0f0d0b160302030906010306020f040f060504030627110409 77
    0x32140111500c0241c16580401c201c0f45011a0004107000080b1707041c00d00c060340c0c001408031040d4515014030100400c01c4803040c0040d4403c1e5034284a04204044116209000000c0070307081032421070801605944c4050181406000104010400c00b8024040c2502007800c0c880c14a98a0807a00400c900e0400840100c00c44038102c0c00000503126000040c1101c0c681c0741e50250b80c00c07651400c0040f0307114003052102401210032000003d6851900094003082148003c200440b1a070711180481c0032a000015000d04d103400014080c1f200310340000014004002d402091850b02e030500b41300302480d020620549000d14400d0700380d44079643d02c500c6110000c2c1c0c4013400c107100f50380003070501c420110700c2900d805105a101c95800c900b8903100c0d0088902c40d00440d8000c0006074078599403500258000f038840c06800205000200d240d02145c00001d0040034180d55480c0c5450039410a801100c00c20a030301d100e010b80340e02e020401c401003503039107a21003500260800141074041002c01c014102e48140140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103215053 1250 103213803 103213867
    0x3040f080f0901120203150121060f1a0a0c06110c060a091104090507030f050a0b07020f0c010302030118050402240c0c0301050613020304030302040509010303020d171308 75
    0x844007100303a0150040400c240d80e21461590350903021030417032000b500e01d66080341008050300c10b994042d5a80b070010b5289a400b82814041e01000002203c03e00d400c0900d08d07840c4040c04110306280c0381d0f140b100700801340c845c251a0032203140010740000140b020040c41c51f500c814051000d210181c05843c9aa001c40050360404d2404002d00b500034030021604881071024465440c4d01030a21380300e880c103015408001400120308503128003582c003ca0b07100803102c0703100300d4900c030f40001c0c0075403491070003030300a50010010404485419410400c205c1c0c0510704261040c0010040010290b0108407206180400004c481d21203002082c01070cd4410700c135180c894809100c890003005014010900d207a12241503850107032240c1c08142c01d075041510f00f1035100e801c4030b1000784c564419500450b0000d120b801c005142030350b00d1010402e07141e0240e2003500076801804040810329000340a1011404030580055250310300100224051041c000010304890401305502118607960a40040743e00c2d4140c041d80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103216303 1250 103215053 103215067
    0x10512070e0d0218040209012903090f0304171504030519020f030a0203040302040513030e19120305040905070f140d0e0a081330020f090a020a0905010804120503040f08 74
    0x1c652000c0c151340c200d000380110000019030f80d820903805200c9c2500104401880e18001041c0d00a0390405040780307045000302e1000d805042c0041000300001d1070f039448019100b11850301d005e030a0407010300d0111a0008124100000a0b0303102085402040c044040740f4000020745904900d480b03203000c1883d0180c4000500480b4007078000000d8401c0b0381c800c40c0c4c24040c0d03550f44400c501c000304000c4401000720f80c030031103180014503080d140201e0901e035007000c0305105a81d40b000200d500c10382440035008200300003400e0040d01c07002d000d101d60040e580c1c145000321120024009050800c50440202c1c04840400e0002d611031090304058500c08068040b100c1803101c50400c500710f0341c8844c82200001c00b01103c0001d460004103002c618074900b885901c4500c00030b070606000c1c045c441281c01c9921210314030002419030340720340c522801604280ba0040e1601d51104c405881000640c00141c140130440007000300081640b039a45c01c1041a5160032502e985651400401700030308101c0c010880c10780801d440c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103217553 1250 103216303 103216339
    0x32d06060512030c06060d0807060903050403030e010503040309060e01120e010c11070e0705180607030305040219031e140a140705040507121a04090501020301050f010512070e0d02 79
    0x2240c00d803101121582040c0d0801d81200f6a6481100006207181d0071003030025900c1d1600c0304003200b0305070040b809240381c482a03a0340d50080781c0b640d01040300850804541032091503404205602c0a090a0038003a1460509440c00b8003162030750310a020800282891000050744a0410707818840104a41888191404912140a800f242c600c8034000350030031f82c3c806650200010740d94115100d449204a1a0b140c81304101d54a9010410089429200b1280448141c440d00018a4514001da80c0000d0a040510404c291400005007440000840d24410720218004260320607800644451030340c0d0940c201e141151a00c0000c4046405900580e010740080c400d25880c00070785044040281c5070360307544a10412040301c500340d40303641c001600f01c107001c190312501c1d03400503100307426114402c2100300d984c00c0007400760b4400201c00c0325103940200040100d0b01307045011049068003401c010341000541d0052404544008140c0f0041000e6201c2401032620307404240100141c000e00fa0380800700548900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103218803 1250 103217553 103217561
    0x11150406020a020f03010c171b03010e0601030b09010b0a03020d0e1606030608011a0111070b030c12010e040206030718050607030305160903050d0c06060e010305010b0a1707032d06 79
    0xb00342d0142076004405142c80c0f506200748801c000d1251116100e51010341d50b210030000c0010221408101110f0050715214202e00c0514020710f2500d441c19100d241a400040981d28076083c860302a4001800602c2441240d801fa00c01840c4140780050701c521401d91038030080d284c400381c0c00c6a18080c4c5440070145d2807800d4a04802c0e900152000d00810365990020b500301c4a01200f0341c051503010700e41c084455881036000803007100c4601c2c108d8030115116104600c0d0b43d030045d1221034084100082c608104101c19800c0383c0180a1035848565070314003a00820340901c03006119034200b203d00131074222400031074440107001d8400a80340580302d164500d8058014141a101c1d0190055154101034046224580034401d0700d6110003d072140302e06006042c2d030905100e40e001c903001501c650b40400c441c24203810042c02180603100100302c3c030b0202024014a440a80c0002c42071045060440407503181c0041c06a0441c2d038480f0310744229030104e214000c26100100e2000004003c400300d0728080c0101e50304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103220053 1250 103218803 103218823
    0x3020a030b01030506130c0b09060d0c09140103090c0317040308040b0a20100203150402030a0f0501050607080306060702060405040f0b0405010605040e0103140c030a060213051c1115040602 83
    0x1220302c01d4a400b115180151b84411000b8082d1400d480c080c00b11003410805084c502d0009405141000280b003940d000303550700ca42c0e84200140394081d0420030702d002c04c0303d440d04058081c01c04101e014440d860300480010540009007040c03020800800c48000c46e0b408541c01103421802030741c1c071a0340305c10004c021540b00c03c4140c400506c980e0300303800303445000c03014000803012030350020a1129a00da080310b0180d0402055004810781900c680fa160f6212070005500c40c0707110307900002e0150844110b03a0101c0c0e406812107405030500340055000124113408680d0803610848807243c6a680600c001035032031286801287d081802c07d0754166180c0c1c0c0c42e03040040c8400003118203000c142e0300e810080b01e080c0114843d881344c6a042c0401080480c40e0190501040f0001c1003d640384401500d0201c1c0c5040401301046520541c002500c0c5a078410251410001e054100c444000c0c1e1601c3c031040c410b80c080100700c05403085568590300784060b602c2421003c3d824450032011a21240d03126006911418111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103221303 1250 103220053 103220063
    0x204030605010e010806040f050c1e120616030f09060c0e030601150c03050702040e030a0801030605060d02130209040b0a090c020f03030610080903160605090d090e071803020a030b0103 81
    0x1c40040f070344492482c400b030306079001100204066030744c60301c0b20b2540310380c117070810380c0d407800b90468840b120b80380c0c02c0a40365000110b000300c00c09a03070501c052001c071200d0006041c556070807100c00d1249505011125518140d49464042140c601c8901c0c254014058080e0090545207040003014109801000c0107040d400110142c4d91583c3c0c1e00c04107100421140306201e8000b80007404940c00007400b03040540540c2d4009003000800900803107403030380703513502a801c2c40001c070703801e000108200401402007a50003c4141c032500440403c582c04903801c030741c94000380c00c0d0b5280c0104203c829500d031239000546a10b001060440c865549001c3d4200410020700c0c7c0d000140034007080940c0d10f0130001f007201e00400c0c01411444000802c000110741e0700070050030f50385030781c00f08015030403229a441608240480c000d8000041d1410029200752400b54000b41500034891103d00800c40c4051010000b0f91049a50921244c02107001c40e80b180302c03000702d0304001d501c80c485000103c00d014100e402d09040e28425 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103222553 1250 103221303 103221311
    0x203160e0108060105040b161a16020a0b06090403020f16050f01020a02060904111e0d060806091b0d0606080303100611070302100c201011070504020307021f02040306 73
    0x24011a1020b9044403200c0c041107080008001c030115000052544210303281c0042401d00c2d1569940440720b11412015054880700e1040c0617a100d803c00c02144001c0060000748624800369698400400c00142101e1061075204005030600d402400051104101d00c019110707207241800d951035500004c0c1c042c4034010b103084d80c40030380070f9400090442500c5400030002424151803408000107082d42803460400f00701d0501030215090b40d0b681200c0308a014285240e034803800043d501e030303085804070b50010015030b01950034401200b4000c21004030003a66482050722088620021980903446032200900c2c541c641000069110404400355000f180240c01a4201d269921401c4420481c00e5510300d095420141d403c000620300b800512640501ca403e007805a0502038031904082c1800f543d51090f2946408904059450b003070351784086086131418540d8002040d481003031754844550066500940e400004560154001c100d581002c11050100c040c185c203230b071b0141c0c801030f400510086801c5424 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103223803 1250 103222553 103222577
    0x402040518181203150f0904030804150203130212011d0609010b0a050a090209030115030602070506010e13020f0a0801060b0c0705010f05030c1e04090204170105040302071512020316 80
    0x4081070b80c3c2101d07008190303d90b08540380c00340780080c04244106055402241440c03a800d04e626803d1446220f280640c884040502d810f09000700c008180c011340c201254810002c014107045050120300ca02c54060b075421145400c0c24024a0041440303400340004000b10105100b00b02c40e0000d8a14400e00801300288075042c1e200c0c007800322450f0a402215400080258140400c480560103404060802000419125543c052404003004079400c00d82d10a03400095540034060200032043c01408219100605450040280060522481c0000340302c0d124241401e1030783d81d030703000c0001c000d007030071000802245550700ca4081860303004044161711409803c10015080d80aa078454241030344030345590345903580c4c100d00454154410100300c20100910f88020411064140203000505140f0000590701d0741040200c00025101c182d0072011607040c8802c20000075808200c030022100c1520f103141d018214440d00b0360b8402390303640c482c0700200d10110401c51400310194002e42608043d40b21003180c400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103225053 1250 103223803 103223851
    0x16020f01050f040b22080702310902010c050607020c0108130213020d020d0c030b0a050a140111150f10050102060708221b21110d020402040518 63
    0x582200c1000b01c412540e8005004074141c100c041da0f00c100015104206060341040e0f0314502c80c03010740e040e5001080403415a0440c107042c071517140000400f080d070010514482074106a0405200d20422115481f030941a0459004292240080ba40b02c41a11401e160807a03009541c2c0e01c1408195000503119408110f803001c00034488011a80c01a0507900c595600c101d41c0c0d0042e40c4414080302c005a0b0801455040c89018454a5142d032003561b004551401c0280400c050504203400540c450104a0002c014000b400b000c001e04404081c241800ca1011060b0046c1c1446907641e80c031141207144d6801c000000200054080c0b003603100742d01918078140c42e00012aa1524111880d00105a4030b60100d5101100001540a084818412554075171070542d80c020118000749611440a001d580041c04078244c80e1b11104110041d4900f0380c00300042c10744445090100e0b140410b802154020841070642d21190100d5010304005001d8500d019000d440c140003400d4220b070320151000e800032039a22010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103226303 1250 103225053 103225061
    0x7081216050403050615010e030d0309120905030309151b01060f1208121f030804050411090102031c0605121509030406020a030e03011407110f0d080103030305040f0b16020f01 77
    0x784c2010040141d07030740b984455041c021000f03003440d05000540a120076659070030040b0039400c1202d81d50200b0050f81074034104908079441c641e00400d0040c00c5400384030b13949000058070244038046680d600c0c01071810b800070740107200760007040b0310180500900d1418184150061011113060044042034581d50381100c8481e2080040010701d182000c021104003c62200d007216040089201520716800c1001c0001d0451912075108031007101c4c000c02c081055140078030984948006200d94117261208810000b5124461801014a45641d08007070400000706684414082c00003c0c12900c07911000f00754559075400400081c810765a00b42000402812021065034201c80e503a4004140909140d507040d9a0306014203100c41c0c0540d41e4103001100141ca20050a00541390750302c5004025020542c030500303000d10328000050550081050b440425404070456044a4062a00250382e48817480c100c44100c484d2074001d1b00041d11003082c410000e80e0303820300002020081c0c007100e0300202302c807088500b03803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103227553 1250 103226303 103226309
    0xa0b04061d010b030c030f0a06091506090f0b0f0f07020d0303240308030114130f060510020102041a0f070c08010c1b05150c12010806061809060406020c0102070812160504 75
    0x105d502800810103d54409100c10340140e0030788408a04952502c0d0f80f04100d5142c00b02c20012200e20320b504120007500300c28001d004c1c021542e00141480d040211000e09482032041c051440317400020f640c0d84011080e400c0e01c00c0d90380c2c0141502654500360030028058140030500001000300400c0c9180c076402c10713848001c1100e50105a6034110780c40c02d0018004206d0078564140c0185045c0020741086245202d803070748160380340744002090740c10038003801207160486c0d1728242503a204100920022405001079041081229a140e6803500501c00c0304481d0b004400c0c0c0241740d541070840200300b01c0819006204139068070781d00d101c294840302c036581286504008024225401c520001c54036140d0000d82c01d940852107170354681c40c024804031440e05900c0c00340d11035802600404103000b4145095103c48004009201711429a42010f440c0f154960030003500040c400c03a400100c5031009942034058815103a0402003c5458140d109440d070040b03072040b00d046a60300e81580e420500103014800792030507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103228803 1250 103227553 103227571
    0x50c0c0a0303050910020304081902121207050721030c03020909040f081207030c080c070218040212010f0204080c03030304050a150f051611060615030a0b04061d010b03 74
    0xc1100d503480503001000064503007501400b95410310704510046000a5006501c521100e9507259900364480c904441804081d80464108165200300844050280c1e01d10140c1e5052030703151920b507510266468440d5030390040040400c5084c05482200b040710b4030900c103a19071000d0040101c503a100710201d10401600d00da00c46210408500030500060200c000e080c803544419103031800040310100008021940074000030303115192039081aa0040100f80c101e10b00001407410100c0039800601d2412169034000ca05504c85c80001d02503580d0800e0320398a0341d81030002041821079240e07008000c0e44c46406a2105841510501c101c4c5040010440344078541102c0a401c4144459070346c000c00f0400d900ca035030181d54480c80341e10900d80c3c40d841790b5400307444070b20122601002c1003d030203082c20541943c00411364000c042045019211307141c0000842c008400c02a40c1c80d0340b0300803c40c0c002c01c050105280c02524000000c90501c264400c0d101c0c0c032500d0302c6d901d207a841c1c0e81c98a00212a20080b603000071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103230053 1250 103228803 103228813
    0x12010f0b01090503030a110c04021903060b16080901020c100c0b090d090b1602041a0414041101050a020f010c0503010f15121122181103070c051c03050703050c0c 71
    0x3406c944180c05049050001e1070030380e5079549841c0c00203004d9070410b001301c01c8200b01440d20008095014818000141000350a060900b6000c0003400030810110f03070064603001001448400760307803007401541e18048009010482022206d0070041001102c40022180f090360000401d820b0040066490440c1c0006d0f0713a010002030400c0042e85881d000424540384c1522402c1d00d07800140d489000714100c1ca072016401c0c9040200181c05c200c2540c684800b0b80c5031406013401400045680c4847c4c13080070600a086c40c0c2d0740d40da1559401ca02c0c003107031120408000d511b04404005040d502000550480344078009810a56840e030495500300046124104041410b540d202600381103607401c41900f0030745214005d81410050f90903010a40005070a480241143c850b060020125842010074601c003444000c004c14009000c10031032510010f00780c0414010400c10803003c22030100590414001003803002e0700600700303079580900580810b50380080800d06002c00118160001c0c02941c4440001e200144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103231303 1250 103230053 103230067
    0x7050d0e2a0a060c0807170a030f1e02090a0b041203180e0402090613150602010f0b0d020f0d020a030302010c030b1c0201030c03110414090f06180a06030212010f0b0109050303 77
    0x5680c1c1134401804483e803540500403e0080750024140030b442c080150000790303998042840003001c035880303490001442032806aa800040c1000b5081c904142a41840141e640315620b000076078000071b9a120301e0b170f1414002400310701e0b14010030b90040180d110707458140c8460400c0f0165282004103010b003814401000c0001405484d000078019046513014205941200600c583c2005403a040d4840320349800d0908410003200381d0903c590100410341407400c01c01d00f030300e10f40014200014882c004e44690802110744180742e9482e9a1941032540c0203140c05c03003144d620301e0003078040c1c64040106004a40b41891540301030130b0054510500e41100e88030850001810760056009292030f038002c1c0708069441541042d0b4007240c84c0140041c1441071042c2610960b000c0c104998404010920301803002440240195a184d101022459032b00300c00407207240360341d841d10541c01070030181c0c000b0354403180c0102400d030b410704198841c4844281c045818880741c9201801035a051800e0300c18150140d00400c182 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103232553 1250 103231303 103231307
    0x10f030503031303120e0d0210051006140d0c08010e0c130e10050405070e04051012030c050c03060a14060306090303060609010905030d080711070305120307050d0e2a0a06 75
    0x301e50380f01e03c242484405124815282411201c00c860004819800f0301e201d20301329a01040340c05e0b0b84c1a00c005050090346002c01c00c04844040c0c6101d08001d01c040c0005160310f4000e03040c240c0340c841d440c84408000110000744002c01c00b407020302c02d01c501c41922001003a0780b81210421103040285213800307800d006181201c092001031005204005401c01c981c00800d20b0360355401244d005001039581c1c41c00d614484000c2000322800900405070030442d60508020301c8509590031003099415041560001e4a5810850b0070b008403120490f0341401142c08000603001079078481c0c50052034401910078160703204010f041d520a02611120426402400012039903d0b2140c01000000c106142c01d41490350340344046032400412007850170101d00014200520385602041d250035881c0480000e1115501d1916a81d44458200c00518081c40001000920340d0303014008892501003004402c111800c1e2008a0359161070301e0b8101221032501021490b040c1d580741c450b09544644008001141240c070701002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103233803 1250 103232553 103232581
    0x1c03050405011d030f01020408010f05010807061b050d1e08040507050603090a0203060901020a02010506010221030a0e0d1e02210d090b0708060415030f06050603030f041d010f03050303 81
    0xe8039000f504050000500d40341400141101030954001603210781c101740900d03095481c080c6220394000e01d00401040610b40000b049000c4941c203050040d203004803005c0720100e600701e058000e0140d2060000c5180341d80d0b0310582c00f00642d40c10a40c44002d5040b04001150390311002d4401409640c803801c070274007032172500c0c0c030045800880c44801c84048001503400319007030480449041d54165408500003401640a0094070391098092002d4202c904038404159100e5080700256030600c000840004c640c0e401c9c0380d0002890580860440d044c8948844009101c040103003256145589003500d440d038000d0001401030807034990340c88d180201006482d40e404541c1c21115003010b059480d038802d4008282c1e00303900c40d40500d0055458009524000c401e010a95050602500d0110710020041004c0340900c00300250043d400440800c030b035101d180010740f85005800100b010b81d0400900002c00c03524071441450045900448e40f546a80e942081c0742c01e480307480c880640b05070410400215090034440c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103235053 1250 103233803 103233827
    0x601030204080708061008070303020d08132001110d050915092e091503051015110f060c0403170403080409020a030516050d2007030e1c0305040501 65
    0x58014102a92202c6091414807140e2224616030840b02c1031144648021900001600c0c001009011091460750003e50301d0b900302003504108850341011408841081c0d403d80c1e003c0d50840c10408004080c041e210030102c01c079100c89030104030380440700d0501040c0401c070304000501f00e40b0b4450030140e440d010300003150000c000ea00c00c0b100702001032840e03d40d141d00c0030000700102104001031091720f50f451510f030400281c0300442032001c000030810042942c03541c0b480c11240c09103004501c1c1d13126010702039081041c6400c040300c05130320640401091940414545205401d40c4100c0d070f40d40500140326500e880f01a600e0300042c040c200400d10100e000c284810780000e12241c41c1e01d29055503074070b4649858106030415503105400041140c906540b42c001c0c03c0d005003500e180640c0b803c032516070240081c41084202484d29456211180c0701554600c8010a405d1442e109140e56440c80d18000b070030102d02480c0b00e881a000c50003203250340003035418900c8080b0783c580c5800b0301d4541800c0055405041c004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103236303 1250 103235053 103235057
    0xf0d06020c070f181401090207021f0201020d0b0f0f010f11010e0a03030c020105131209051504030201030c08101e0506070b01090606030209031c1106011403070605040b0d050601 78
    0x40800c004040c200401001000f80c02d44030000542002507940d503040c100740e442c0249608003074044400760b405502d80c81c1111614440169115458804511070004c401251034203610842c0141c03c000c0c5d0190014402c0c041c8012041141000c410104801114044151031300000898040c10030343d4020030b800441d5400d9824403d40884420000a007940d201c0800340c02140c000620340e0041640602070702d0028151400244014030300050ac002c200070350368002070001428503140101041c010340c0c14102502002c3d01c040718075a03040b0341c0c0b07a8081c0d105100c12800a454000c4071a001882100b489004140f1040c0e21030210789000c94144c01507000d904090010b04500034002160341d00c660062103441d03c2200c4943e0a0343c9450031200454003644d2298043c14010000c84c2510340c0e001c1040700304005005255420b8006001084460711f0309564115000d01c82d96002062071130704000075092050086084601b45a01c88508850f80d02035880762903c5a507060181014031030a68005c207034048418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103237410 1107 103236303 103236307
    0xa0f031706030c0d080d0204030308150105120c0c120a0305180102040501090b07050a290c07020604030b040f060501061206090b09010b0f0403050d0807030b030a020f0d0602 76
    0x3c000628850440ea000010030811010103480d90a07500041c215121034580c42e015029540035926a41080c0440600d407042c0d44c4910129080302c11003d10110303150b1600b0004000c944c024070407601c0c80e4020340d010948002d50310b1002d80400c5a0310340d0301050506202e0b0311001020f41c0c1c0752405030140d00402061040d41d802c04120411a0031a180080d0f84a5060510310700705200d0300300050034039082a000189005a114683c404800c0611041e481500c0e00443c1241c280305644009400920600c0704101040031426401d91041c00340d42d444902da4175640d9000101c4000340c200c400410310214031841c411303803035100d0000030f0300222401b0020701045c0c2c0c0010740350100500c50140350300c0001444999228450703041da802517500c8030440d0f54000550f400075019007400c8aa05000031b00d8a076a5000b1840d001808103c1c0980280c48100c2046c0600c041c014012240d0750f0031b4a2464003 = true := by decide +kernel

theorem cover : BRFrame.Cov 103057553 103237410 := by
  have h0 := BRFrame.cov_init 103057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103057553 ≤ n) (h2 : n < 103237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
