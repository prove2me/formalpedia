-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:47:49.922969+00:00
-- url     : https://prove2.me/submissions/0250831c-a8d4-4017-a27b-a0f4b55ed3cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 565647482 ≤ n < 565827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 565648732 1250 565647482 565647493
    0x90604031b020d0609081c0212010e1306050405190501050609010b0f0a050903070504090605070306090204050a09051e01080601080d0306062106050a060507110402091020070f05040e070f0b0c 84
    0x1b103034a0107140b50055081090005030303403002c00d254600203030305040e0040311000312f046041c004244d81a90340d07020300551001740400d40b9900c0b810141c1c02c00501250920741c00326040b032420101700d01940003922600003210700140a9032111060311103401410a071003600c800411842620f14020310103401480742c0107044941464440011500341d440c03000c0212030b059124410300910700c0d0076001e658040d00141900b1418641341c60005480c0c00729511424110176550004510b400c0311110b040301645601c440d1503109942d6541100c2e507034074001d10078113900e8081e16180c900120b10a004a004859003560f034035041d944c409140910f046013900b9003000c0c090381d070400007510341c45030b030780340c000070469501c43c0c0361501f186051501000d504803420705d100714810003042c182956090341181d0310020f640341c4103c2400050000d40c130600f010388544803491148013000102c50b21050007400075508151402c1c040401900c0e4110f0340c0c0c050300e003c0e0340c080b00c0f40180148045a07190007c0c00d03040442000b20742 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 565649982 1250 565648732 565648747
    0xf0a05031513140f10060c0303090f11030609030906030105040c0203090411030703180b01150908120316170408031b0c0105041419110a0e090604031b020d060908 71
    0x341e00c0050600080202c944401c40b80c00110210100c140d0f1200064401240c14500200079590300c5c04039000d01c6052001440004050510950009000f158840800c0c48580c0e00d81c00d040510124450810b44280710389400202043e0f8040f040e9140c0c44400381c42541581d0800c03040002510300b01a010003144014800c140d171950b00d1303008189600c2e0304499815980c1c10031050003000c0e68051082c600405074451a000c001841e00100340e811600e000b20000b010030a64407086941c4041d83d4440c1c81d01d803007020849a0054000e40065009283e00800c1902c2ca454890040c0c9603404001d4012150001d1000010003180c400b000550b4418281e00400204280501d4601c0c0503070010840d0f003c49139554000c020030000000240344c000b0354010000c080c51070810a02e15858820303841c000b003209850319052030403611021101005400c1076080c1c1c02d01880c0c4800c2c2c203543c80d44100c5040c1c00282c1d80c901c02e82c40c240c00c400b05800c0a190050503d048401c1280c88040290000782c0341160843ea0410011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 565651232 1250 565649982 565649989
    0x1e090106172a12040606120503190903020a0e090c0a030803060904081c14070810090e07030204021c1b0909021803071d010602281403030127020f0a050315 68
    0x5181952400083c801d0078245403c20008442d0185c101499241943d010100480c00c0041a02c0040d140a04045460750020408840e84080f5600003500002c6500001c1610101d60300784a100b44c50150481340c0c0c040e1404200080c450251002030300340002000030405504095454582c03040c000c0d25a02e1506194a00c900d0540078000d181310081c40d511240002010440840c0b00c1e0800e00d00e19084030700c0d00300100501c0e0200e07180d103e0700b880250b80d010b041289500c28403096004640081046488149189d1241d1503908002c080c05244e6140078176030721403040302d100402200402e9a91303114519080c07214030002507100c1c001d0046070308200c01c5081d11681d0308000003405407520310440c020380c03000400c591040c220103801c440255048800480032002400617070895002043c407102c6580241424910107041c0300e41c0e228690350200100114a6070881800c10b02d26401a407001d8050241c2c1001e41e00480c0a00c0010002030f003020018010003c1c8240c001d190480c4207145420208001003000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 565652482 1250 565651232 565651237
    0x2a080301090212180303010618120303050603010f0c090506090f060c010e0d08010e070c06150b19020106080703170c060a0b1206150103020307020106051e090106172a 73
    0x11500480d000205070303802201030103c1c29006903140007000189010a803102d42c4038001402840b0410001c0501d03d000b044004405a00400d1414049940e000403402e000340a498200d417650b02940c20720070b0b03e08020b101c83c80b0f840c0310500b0960b650306103c4d09007410000503500952100341c0c0708003c02c403182a05d03621b0b100100f0b409040d282c00003541c03002041d0b01a0501c1100000801800b101000402c40c08108113401940305250380f414400d64030031340c80d100e8000c2040000d80401c0216006021075104803400c002d00080b5004101c130072220018100c103c1c00e85000380100028bd4211000800018803002c107404c0b60074440180c401d00f4402d030080e40380e141c40c500319070000d0a00c1c1c41d59010b20290901043c032400c000f10b2600540302c80d1504c00b9421001c880f680591504240e40080041d070100d10030340c400b90182900404404a401c1c00c80304662a581040755841c0c440e01c4c1d106c0000a039680968070500c03010404560404044c2e50b00561400e9140c0e00f081080354043d0109898400329200380300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 565653732 1250 565652482 565652489
    0x501020415021e03040909060e0109030206060306100614030a020712050702130504121103091018080d0f0c0201050d0501030f11030303070e060904141306110a2a080301 74
    0xa106260a01d0380d800249803002240750340014060030b2000150194000c8101e8007610620f22012840000c0d915000008041d0014003415035440c01211908051340440e1440c0038110881c00c40b85680c0b0303500004402d0620345d201d0356011415240d125520a5000c10146030700540c507200050501c10551501d0b40e00c0340d2401c0707a100000d04005126011460800e004203031021042e0020822441c051f594800300c13540d0b5030010360a10588125040c8607200400c2101c00741800600b11a6a81566800c05440603d40765041034034104440070100d1004c07000101038a209119980f0740010070b6500350705540e40c0380d401e041641000400c1007140d10040f00d60103070740c2c001c52150600003440344541c289040350100307508025119400070801d00c61801d83c04681c1c4429503e045540c6581c40d41200000703001003a903a0107040750b17405042c0401c100102c40203002c5034264002d50050007550844460545140b154404040120307400e00d20720401d07680310801c44060024604c1c13080c64010b14507207031038445d900242e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 565654982 1250 565653732 565653749
    0x60204030317091b130f02181e031e0f0d09060f020a080318010e01050a140f010302030d0c0614010807051512010b032e03020a0e0f010905060d05010204 67
    0x1105890400c0009442d19441650b240141100c2028402c0080e0a100504007082c401c100001241c03002c015141d0041c550102d100c0300840d03407280c1c0b846245107181c1103c4c61441c81144e0751400061651420348140804150041c09000b0300103403450074407107400180354881c407603115a10f030820300b400c07040114501c0d504c025100c040d86e55103021802020328029454680464004034002c0b80090b9401e01620b4000c1000c80c550303030b080c04c408502d90b401041050b900100543c201014001c10750b070658007a070340000850640d00000e82c1c0d81c1080400f030900a110007509070b8030400078060000d104a4080750301520403c004107031201c11600041c4015802e030403035107058100b044100868034201119904841c0f00c000900d0600000700825010900c051040026049000000420b4001c50318044611a801d802d48120308400700071110f45009a6030001b24082c10b50580b000c2440404201054440d1402e034003180c13510fa00b0940010050030f00641030f41d4014501414070000a0802e0019001522051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 565656232 1250 565654982 565654997
    0xd020a0608281505100f0509030f060f060117010605030f060f0d150c0e030c04090302030705030304031e030506091317070503131a04090c120e06040312051603180602040303 76
    0x4800b0f41c6a502254000e9200e00c101c0c8411152058000343c6032540c4c00850309000b601c40742c0c2000400d04296000c1c6031801c25001d100200081c0350401c50f0141e0052400b81d0380e298200e21a44240c0c03034142c00070300503003022a000348006089244c1800d00d60b07502c444050140c40c000060800419074000d9242d60445401d100940d500c4a010760300d124010242e48246400c01e0407a810601090b280d81e0880d4070f150003036447e09040c0041c18020011075007040c2c1c0c00300403250ba80c541400d00400300307802c40150307423048544c1c4100d811010344240156800b49800504030328003521a12420040c45d28a0701003168031070005c0552090b0100c91030041c00005001d00c0140d83d07107407074100d51000c40e10380b145c008034505426440108603c1e80480180c5064039200000001c15000341b41d42520040000c04480d00d0380ba041807165000c8601c007042c0540076611940380d2841e660500f101940980d0411641015014603080d03210010911a03088a040c1d0a06002e040d11810580d40b9404140e034000d420603070104070786 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 565657482 1250 565656232 565656251
    0x604080a181d07183c06030c02010510060c0219061815020705060c0102120a0e060609061f05160809180705040303050c030c0106090e010b0d020a060828 67
    0x41c82e241550040740d624102d00405090b40605198400b1800340c0b0804031030b121050381103044525890a00401540b80e007800d440307240e0040c9030701d140d0203001c2c910001c0d003042250741000340140203aa008844140d10168403034109039003200c820352150010707a84991000c8481c1d0043c032059a03240050442c5903107644079200c40c95010003d021680d80300044c0a1004c60b80c1d030040950224182054602c00c0b603803660349484408007540640243c0151410003001ba07402d01034140c03540e07445403103032624603000d803080d540e0b510b001c00c19140d000b110090b801c1043d1441510140107152007103400100389080080c05e211442e00300c5250b1400d040f00c100c40440c0c3c00505a03016142034280010441203200c0b003220a45003084000b0074600941c40010103100300821000135186082c8290344c41d81c030f1900003c100e56a45d5800c1440905003040003c043d5528041000a450a10900e038010603034001e42107801f40303454040304031501800180007a41c980e8251052050b58903140d0704500080c102e80001094800700e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 565658732 1250 565657482 565657529
    0xd05090c040b06040f060302030c13080d0816020606010f0908030319060e1605070c050316090e01060803040e040309031a01030203100506030a230d11060702030a020604080a18 77
    0x1d0790f100c0c903c140000c000240b80d07001004103590480ca00540c580e19080703005a03040c080c800700080440085000410701803400901c80c1d00c0c15100b40d80d54100c9032a1100c08030704194108290100581002c800130b86154050354001540e040c0d41e01d402c2d140030b41d4640d000c60644d0010f56101d10904451140f0302c044036024010075014011807411096542408a140304a0f18a9004060140b0601007101c1040c01300b4841620f0080001070240d8540c4e51050864a280320b25034040c07042030307500e4240c9492005205204844c203a442000055103014140301014902e040e00038011000c003c005580800012844829106240284400e07150a541584101420081407400d1804440d01d811304000c0b491760005051042c0581200c225078900d002c0d01c6072050583d100502d800400d1040000c070700e6041d0f521103d10000c1c1402c40064450646408804980301d104801794100180c0c886404134000c241c00034024941d904141c10102c0d00003a0340c003580c82c0240044c0d0b000003011800d000174000c5125 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 565659982 1250 565658732 565658741
    0x100501051503070206010e060d0c030807020a06020712020103110c01110711150f030a0e1b04050c0304080f0c0109020310020a080f09120d0f062d060e060904020d05090c04 75
    0x100801034a9040d440e2010f402560f484d414803c0f07120400c00180458416144c11000484441c0c00c0319940580b251213007042ca510340d100385422801645540c2c000581d03144040341c58002d9402c6092070300503402c1079400450140c04c516078a018800c504210a200c3c0c803609214072240d20702c0014030750fa01e030107a41c200060700207141c000044c090248c0d51840503844040101702d6003404000031005490307480340781440c0000c0941c03001d00c41c442d00c178030350343e01c0784180c05200d4171200c4490881c1c0500050343c0d80380c000c0007540820703107000b070101038248440e004464007040544100442d5000020742c50b405600001d140404901c4040350050380054202c8059501a40c1241d004c042c02031869a64201401d446984000b8201c0300501d1f060b010815035a110081d400184039401048424803485443d44030480c0d41f00c400d001c0e43c2030568092403580c101014514018000c5440b07544441a100009000303028a0394444c881c1e50345d11035400c02c1203402c40c20191207503074000c618000c02001c18210040c103000854 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 565661232 1250 565659982 565660009
    0xf050d0504080d05220e1008010207150b19060314070305150108190504060606021911040506120f0f060108031c0209012a03031401060e010804020a0810050105 70
    0xc10030060011a100048064003c031080ca092940c1c0c5c3c60000c00401c2d05c0150905850161801d0400011a01c200309403003409595280012506c9a90b2038a00c0f508074494140000c0541464007002820030a10b540701d00c92158003c0c22180721200c04203003015658889400c100046951703030300f40301410824031030559844142828104000e040014a4400c0741d4406490340d4104074503c800540d07081d00c0e031802821074620018041c44141800d29010740a0a03803402420010300c10380341402e031507203024510070302c5d0280c02000341030500c03c041c010300c130141600a0a8540005d441c510000030300710200305901068141c403002e007a941e0080054030f810243d042c5d000001c154410702040c1c0022807a0402c02c070b140720b1801c00042c1c1d10355100c401a1502c0154043d0407041d03411a17041e58080751a442d1107841014440e6074100841c0c461040300310407105085c0035900016400118814055009081e6a030f0014001405005100d54841c0308924000d01060b0350420307261503000410641c14550b4400100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 565662482 1250 565661232 565661237
    0x101d090105060103060b070204240b0d0e0a080d11091005070203011a01050f03060f12030307090506190507050a0c060c03120501210c080d210e0615030c04090f050d 72
    0x30b11b1030a10003041e50b020b900d00180c4134070b42c1c9415001d0401501011202404503150003140e2903030707072200c0c5e854254103d07078030916146040904001c401100402d0428046520031441400d105d00107003000000c041840318008080b50412040c0740544d00e14011500070700c01c1c2da4075544d40303080c1407052500f502c0300f10340210301c4c0b12001c20802d50720348c0e0002c0540e9415030041e401c0381d8607030752190001340488100b00c02950b0408003130341d5480c1d16040040b0040d4840c0c4000e840f10724070140d944050020134800c01c0c50040c2090741803501103584901c9a80280449405a4101c81d042d81441d11001280e4281341e11070400300e080c07005014201500070380d003819104581a81004a5031611003110b100b20604603003a00e40000d620400810000000720800151100004442c2c0e040007155015240440b40c00e1195503c10030000714000801050080c00c3d49407004101a100c140c0740d569070401d05d40c650042041d17042c01000501d0881d5107480c072070500560b000f18002400304a80b030034154184001d07403072030108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 565663732 1250 565662482 565662491
    0x60e0c09090c0d1e0308040b090a02010e0103020f1e09100c08030f07020709050f1005030c0d02040507140f090415210c090e07051201060f030803101d090105060103 72
    0x6007201c1c04100d41219880684088070815440d28100200c8000b445a0f180c02c80c21450300e01d0145540500458492441802007070403075194510030641d2101490f40080c0000e0800c00261041d52003034014104400c3c40144442c184002980710940c088120328100c040820040b409440501d804074041302e55800d1404c1c2403264408645492081c0e1000400400079012550007003404140b082201d080103003082d200c1005907041052000641020594011b41680702c2d05030040b410703190208031522284c80003000c0d10030100c55a428030010b400010034003000d2040e40441c420203450b2050090106000004026a807114103208200880ba200310340c40c04000001e800900540b0740340169900b01c4050f0700c100c8445c04502d80f900300c047c142250040117415080140a211a510024101c803c0d200c04850b0002c03000c85a05506080f65141c3c49070600141c1c42c0082040851400002950048000d401801040d910b55140712440002103088980000341c0e0810018804000c0c03107915049902480c0500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 565664982 1250 565663732 565663741
    0x1e0908030103060b012705030105010b0325030b0a080c13051003031112280f021b04020d0e06040c0f0e162003040e010b030c16061503060e0c09 63
    0x24594003050000808040d40c1e4000750440b80c0c00741d41c003280b10981800c8050722003407450850444108041c0b00d814000e60030100045007124070202924411107505917240440c1c070214488590241d1400c90640516550f121025000c0d100c901e05440074088510040420501031414030510700641c0007100788403031509043c4038040701410b01d03200490707030545002c00940d241c15140c7d40c241009075091030410800011b440c02c50030040d075100d00c100703003903280d5640700100882c0013940d03405111340130304005800401900582866a01415104802c0035000600344034015120341c1c11190301c211010500da100030100420002d40c40218006068000721780c0a07494602203401606107406410350001c08490744c40c810300300d48210100124001000d40305410700030310761030041c2c0b039502c240124495900e000c030000c031306015000112801103034525540c80c6400004a005c9001d401d2051003220815142d03102400c040040a10402c0514024079000420078081811a407420800c0307001107002e40301100400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 565666232 1250 565664982 565664993
    0xa05101116080c10020106090f1e05060307260f01320106050d2c0d17040f03230d0e0a050d1413120b1b190915031e09 52
    0x11080100113076038001c4628658602640581600d400412410345001d1016480e6101c076007001a1040d00c3e10100c14524030710202840559100301e400e183c07d03502c000020000b01c1e9070780c46413850a48222030028203d1880880d85403c0118204c5106c0f070310380d1a00404c00410700f6070415418003080c0104005d1a0b41e101e41100c000740a0148900424800042039a400c1c1d04815041800da0030182000b076190f070001041e880c0d06040d201d04c00100c440c8114030f00161590300031500320025446c0121500419650703903031041f103007105041c821420040c030384812403422800c1c2d443d0100e11307022100000b5100c2500351505400c5458560b00700d4034a6201c01d40c4a004204040b0365011420760398134040c211100700c07002030901440b81400390403114510701c00c0050740d4420001c0c0003c929205810540c40e6449200c0740d0700c40032403040c0c003806144800304a46c041da80103105010020b0600d50030503458507a6038040001e071141030403000c040802d032500814601101d181004020450084400700990f90392516103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 565667482 1250 565666232 565666243
    0xc0310030803310506011a0f0903160f05010f0c0b2e12150207031d0109030b070c0b07080c0702150f1c05070f08070e0a0510111608 58
    0x282014078000081580d000c045078510000401d28541e500000201505842451060003400d4800e03000d20000811645501c42c020544040c6003582e844c105141038145902c503a2104040551600c1030501d051118240d0802402c02010940e0001030642d2500c0000340480c80f02072100c2e010040220154000035040310309540d0883c60b14030481100394001d25845185100100d00c1c851070b00c42c0207400081803804440b010b00c12903c12881108a40c0005ea010390682c0244503005004c111152203509520741c080c1050714014205142c85003082c0d0fa20340318522008801e50f2000001541144540140840b10380803a80018942c50401c440c0c0c0382840c0a807075940a03000000b8840c400c804002e4403981881800e0362441941c4250303081d540d60300400010001d03c05100c10800031800c203000911458003480d04440020455114085590740303000301203901070b48510105600010b04c9101141e9a240c07d80d40c0900b1454a803120008203400702c01007407030f0841247c0868003502c641030061008804c0460b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 565668732 1250 565667482 565667489
    0x6070605060f041a03100b0a05090408070b10030308060316170102120114120d0503010501050903150a02090a14030307020d0c090207120f0804022101021e0d050c0310 73
    0x1116141e21000039034072070800520b00d6210741000006541001007400d02814564118116032040d4191000355095a41910039981e1108180e0001c11070f5081c40468158080d10884c4490315150360f9036180c0d00e103d031094400c4001c030307000c6903000e108068000071142d402231012001044000104401c00031014904c0c0a01c0b60402c911180700214040250140c45400500600c0e1400301d41c1c5400b204441e2000c0411383c079101d050115070015195801040358440403802d50391381841c40c2e003407900543d80e5910551030183c0603c940340302e51000f50054900e00380501c440c882c0240e510903084041040c45504c580100c44412911424203e05903000012650f959a0540358031550703a84504141d0800c0f070343d51303120303070a81400010008100a90484400303400002a120300c00c21580c1c10908540c106800c99000b0742001da490410814440400581c107030403903034940058940260810302003180b4980030300d11008003201040d40c0b140540940a02d90748604040382c06801e5140049054180711814070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 565669982 1250 565668732 565668743
    0x40204020a03090203010905060708131703180a0308040c0f060206130606050315010501021002091003111312050c09041e0c0e0c0a030506030106080c0f0f121c0507020607 75
    0xe426001079000e03401203103400c3e800a000f040407100340d082c19500d87d941103e0b5080020701d00f6001400e021900c6000d020a141c101e96180408400705c0420101c950004d01602c40020800304a138515403402c000000800d031184d80c0365407641c00d20745082c5808540940150340602c038100800d20400da400101154404691035184907000d00504240c030080c28160043c0b0f8050064104815049650348640ea040b00c000f0fa0849003000c0312601c1c800100d000710075500c3c1d84408418074808081d8403d4001044000d05080c1d9145440c2c0c090001c0340c6d003032681b13a00000a0111200d001814084c050082c8908510f05841405040c40c080e900c150300414408070101d206105841c100062080742942500070308048010303074505013801400309903240c028500d1000044d040c1070000f107a0b400c040c05804200c41c0000300400002c120700d001c2021440031b03a0001034000f803004481d018543c0e40c14054035000c020000190248902018410030981d0004c10080300340a001c0160400603100c001c100c8550780d4118 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 565671232 1250 565669982 565669987
    0x90d02060d0e0609150a09030c02091018060303090f06090e0c07020405042301060305070b0d0b060313021003090201050d050604380111030a11030f12041106030f04020402 75
    0x100020051001e0800b56002d48158000c00001c0f2030006400d040b882e12042050304a50b82c2c400c0202c05030345494500400203001030342d442006042c03040145402c82c95005a405500c0e480303941aa0325041e000a401005544640080040c550000491800f902c4030110b2880751340d0030301e480904503100d64030510004040300000690280c486100f0744c1e054030b50081041c015800c103410680b1000b800c0842503d64002e119000000c013610500c1004101d80d071040280111910b400b16410b1240c0103540080c109584801c12600240e40d003078021841620307644a8041000898014414212140e940300340074103107441c0c1084050303a00a0103407010034141c0c0c3c4001c1515941c80d8046006071070b21001c0001160345c6001144401091141c5c0c1e064514400d512800203c1981170044483c40c1862241b28071940040120340d0720b592040341506030000100084a00d4407484481008007940199100c1c1c4250034041c0a0008100004030250b00e4100115020341c103504001c032855418420207803000707115a500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 565672482 1250 565671232 565671247
    0xc1903020f060a060608090a050606120c1c0506100e0a0902041e060e0c0406080c07060b13060f050103051608070e1323104101020606010203090d0206 66
    0x801400d100c8811040030342c1c0351800c0044007070f03001d8003290060502080d00e00c0c00080328040300065010307080703030401e000f0051a06c07040d00380403144100202d100380b0390007000c014103e2034036000c400d850111034030341000744155a6400c0c55410494050300c0c0041a0700d41c10341c02c03c8075003221000540c200725080000101c0455520015006003130382c5c05000a0911501900c584e44000c0d64415030032940c7d0591315040c80d80e036510206500c1d00c128040c40020456689c003007014030042401400a1910422000402c4881000015069804a150300d9101921781b0428060008a80000c5000f002c0030b00b800d12040c00c0030101a0602181d1805820821030104002051944030300300151400e03001410f0750f422021041807130740c0544406000448a00600c0c08544114220f40d6100c908c01c5110a150245190611500400818100034040b89640010044000a038a030b00702d400e2030001d120000010b1000d0100000e401d180000f84070505542061280006a0319806052015158101c0305140d1b282007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565673732 1250 565672482 565672487
    0x51e01021b04021b0307022b0605060402041a0a26043309030e030304300503030a0f150f090c03110703020c010927181406071101020c1903 61
    0x10b5440e2803c800ca00c00e010b613603a12a400710003040100d00a40e40c00d41603a803e034081440d850080c3d2039010021072a03400031000700301d0580c482904520000c2002d443d01359680b03103603e04c0c0c0344070500402e11628006050f0074043d8000d01c103594016408612508606044030011176280c1d0010409850852520860442021001d101000c540b07442c80101080440c62418a0000c00c0010021000b02d41c03003080708461031900105860884080000012a4a680c480b103110404014050352040e2441942c3c054001101800514410541c1c0305000030701e80c3c8940320300700542d06500b4a061103030045c82c1d0240134900100300000d0a41d2010200404c0c800c46d8054120010b18180d0446a0300c28070221708441050740c040303090300465109989d41c4070000d4a680380f1591a1085100c65012645030b0320715000c9070300f11a0004d00c41a0341c0d54002e11307260b80c82526107000450020441e0126038108070b04200e1110b400880d02103400140e80300031401d0004140105aa645034505006649215007103a00d04061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 565674982 1250 565673732 565673737
    0x90106180209180f010503013806161b140d080c0c190e100b0405042c010504031e0203031305070b04080309040c110604021311070507051e01021b0402 66
    0x212204084040313454882da2a0254a8007805180d100e5408d054400b003018003501d000c5c2c040030890030401210070710b01200f0303003016031003507440d43d600000c080c0034804a584c241c504007034609008928480d415030103902004800300c80c51700b040800040e005042c11007030311031000b1103003080e030f000030040d548104144030b4a280040100184d40c0c00030842810040046400000e503040364440c0c3c0702000d5540350081c0462400d0514040c4001060080c00100401e2800d80c10030480e9082c6d1054402000e115080400300341354500b04011880c2e91950144010198045c0084c0b2105868100740c51387c186c840540251244009000b546005111080d1001440005e002c0c1100a040c3c001c0d075960303129034818042c2d0712500541c200c540300d60b1a2820450419002d11107801041c7d080e140540855540c43c1c0c20400003c04030b03d10a90031a9942040b011713070100c0c090051281a0265008203000383c030b840704001103a02103101d020003e40c2110354a0003566000220f01519000d080301c10a050079000001c5402070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 565676232 1250 565674982 565675009
    0x9040c12050a060c020a080708221d01080105060a090e070503030313030801060504030b0a0c021c0e041a1f180f1d0c03180a060609060e090106180209 66
    0xc5000e40040020010001440840b0074411001400125020481030782c4901c16413801401002e420420840002ca2900003441c0c60105441c1080740d4501a070390200800a05400040316101c4403220108800c4a44040d030340106500002403050303280c548042006180d02c0d01c902e5864603100c507600740040c18107020f070401518005d01202d4591400c4510001c04c4200c200e810380104200c40008192588030701c04440aaa810502094040d19601d54040040072194040700840c020b000ca13010743c1c40350041c07081101c5021b540e039040f0484024400c000449041081154000c8080c40d40010386840b000c0850314411000d990710100c9a010120645d0480162503444602c29500704c0049901090340b540c84003610b419a480142811007038940c001c030700c90306550f2050300040038000070700e90b40d408502030184584484151150350045a550070151403103604040b01007a1682c5c8140264049500c40c0ca612035013010007404000c1c0307010030010b403980c03480d8143c0b104e030b030b40002e0150344030349420364043c048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 565677482 1250 565676232 565676249
    0x280c02030c330f04080a030e0610080c011803030c0317011d0c4305030316020307080706020702060f0d0f1107020312031f1e15050909040c 61
    0x4803081c11806103155400c46244015052482d0312072903580b9900000500c101d58484200c02d82d0344403078641070030301e41000d0550001c05460b149454003199050003050301450241e41c6101c1050305044031503090038600a01c1c1c0b0304100c090700520035903040605a005c05c81b03815080c542803003103c50504440350180d00d00c00d414003000c4180001041c0d8850550800000c00c2a5298a00e0391501c80c040c1c40c0501c03038860030032000202564443c601707000a420007044c282e80c402907044030311064202d82060400300d24003621907410100400907040c1c45424809070030b100030300c0039505d01a1540d4031b2141d0780c056110b0140901c1e6001c41c1d1401151115002c5030001c081c112101500d41d21804811000740501c03500d00c005d0241013030b01d89882001200c041c3e40b51554010040e000610868507a8103031508000d100303074208110144904030000031041c0c114050403c2220302c0801c0e05000080b1321440c07440d0ba11030201071150b828008515a8000e05840c03a500040b648030005032541d0418410b039a1207a00000300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 565678732 1250 565677482 565677493
    0x702070509010315110a0e0405090f010915050906010503060a1116050d0215060604060e04090c062312060105130509090106140405010b07030c0812010b0a0305280c02030c 75
    0x24000d0382d41e10071030704c041003110070f1004020340d02c0109070a006003501400421000c4000009500d820b400169111019204842407a81c071503034070034203450480f202036070b024a0740c46241010312080c1c0180c641c8044107500038412035141001080d5900d000805080b0724903500c000c0c040070242c60718221040307003144203a654403154090400c179403a06000b51500b0090711a484005400c42d004154680c0f26038002461399041c80e20341042900d07014640041a0303032103030b40c884542c0c00246483c3d50003800b80a1640d503040440d800c481800f850102446200c402c042814007419603031905d50801d03540c1c003d80a11304161a614240106048540e107900000c3c0c1c403800170b404010102c1c4055209508603410507010a01c1c4024035803d000c100d500c00e0180c88516442000603502003406584100d40e00b500c251080da241c03500204041103400c00a801c00c0c0c030080300024016504c0d83c0d02d40150741c1c01c400c4505c4c00b5140e200cbc2004440c88140e80c060081c1243c503880e14400d0914030300034815101030907000401e480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 565679982 1250 565678732 565678739
    0x120307080c0a0e210f0a020f01050c07030807050307171206040b0303071202010213050a030203030901200307260918070c06060801020d2a0c17070b0411030a0305030609070207050901 80
    0x41e1145008010703400b21344145ca0701400c00820000b006000581c004d840811071400c03a100448150b8400f8541c10b406e40b05149000001407200c00050a10f01e01510103140c07100220300e0202c00301034094040d003513030b00c1c4180070744000400c0c00340c0243c0c0c10190880c1c3c005407200c20000403a046010325003020301700412210341c1520558040d001051800c10591241d41982e48485c01c00c00403080600020f03400d50f105200040e515401401c1c5080704114000c0c0c083c81117081000c00914550090310110359448101400f801c400c82c1000c01c10071941c2d03078184054100040400418482101c0da0b42062446846501003000300780103540100895400c89800d000c0e081e152120903010350300405402c401585805c100b40b960a000d0b1200004080703031840c542a1082050000b150548601141560f0300d40050a80001c100c082e40d009000943c410403481100d813405041800b103816030b02c604e540c02600050148800654080100c9a00120841e49440d0503180c01c10b040f031901049070440c5410484920011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 565681232 1250 565679982 565680019
    0x60308030709050109051203040b09010912080405011d0f0103090201110a051615080109090611030106030b040509070b040b221815062a020a06030b03120307080c0a0e 73
    0x31020740d0000c1c5c0303c0800040c0e80342d091101e44a036010740503250340c00c24041481001040401480315100502d82405101c1c1c59640701c0b00705000442c412101200006401c01c141d50b04004803032007906141c400b0b884081d02e20000b00b202062440c401d1070400d40e990342200216806044041c486001e40320407114140210300c2d102e83d0b21070959400d100a5074a650000810022006264800d03480076590308020340d28141000001d82300c220700c01c5403080c2e10740d00341e80c4840f1800800ba50090000303a40101d42c00700e10900748411201c4c05411060140c0050500744840100e900880d0300721141c20030400c2d0340310500000c0924201c41c0c3c45c060500c41c1142c1000190030410344d0512091140d1003501001540c001d01456200743c4503a2007230b0b00108040c0070801000580e031041d01c84401045811040c07540d02c407640001c0250340d194101101182d950380c0c08070028103040201980f441d20601a8500d941400030000e00600340080641c10540400101c80b40c046118440328610b0310300c041c05050741c80a00300f104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 565682482 1250 565681232 565681247
    0x109090b0d080c0c01021203090d0c0c0b0d050a05060d1e08040504060906060f090501020c0108090a05010e03030912040b03040f080c0703080910031802060c0712110306090714060702040603080307 86
    0x10311740188948844400310342440c404680c060484000200346031840564152504042481e058900c0c982401300020102c9042c801400e04103800b038400240f501e4001c20700b030100c41c0c010b00020b0049143e882080e00194611402014506213060030891a07034240c0783c003072102d20907a00038540042c140000041c40c40e00c1904030001b41c0d20315031038032601c26860710011520042e052080b140103a00c61400e242e15540160881c50304104014103540303030785401d601c405081d1902d01d070038516603520000c10801080003d012200031442040070a03031505103010006690307400054005804844281501c1080ac9100c8048500c080040c03010381d481c0903030701c2c1005c2e810354004008a600030072a080015031003600c6417003114141ca170503541101c1d1003c450703000d11916800440e00300d0280d10501c1c1c00842e24203446000c00c002c06106a4080511014103801d00d410000040c04808041e40045028800c6d01d035945480f10f007101e42070302c0c4c0c2525405103000241c090240e5510103450034070700205008500768005d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 565683732 1250 565682482 565682503
    0x140d080411060720010e060f030105091306020c070e060d0b0f07050403020a0b040e0c0c030304030c030e04060b2106060d09020109050d03081b030c0f070218190e07050109090b0d080c 80
    0x2e51b0b0840c0300444043c08400d02ca400e81603000d90004100500551501c3c0c845550020b1110008884c074003547d40d04e4030126400341b040f424103a4461041044003050030113000d030740441c0584010803164400d80c0c0c0c036012100c001d0111424009400300284109126000341c90046400401185485940d4080b502017540240651400841c0b107400040010b0510001c036240a49644020740c65940c8070349049841c926203080c12000c0100e08202005541d0720b90003468050109040c0181c0d440c007640202007a050a2a001000307a406400d0400c00c441e0755800c1607446100300e00341d0114a01080b8030040303502407c25045a03900030b1040e120042415400520380d480354959985125a41c80342004945850008581000a00ca000c002d20364030400301501805182d440501880641c8200340d640c903106141c12554501c10000e61015100b01740303a0340c060398181003030041c05000c2190410000070b040c01c240d4050311095640303440201485845a89403580c4d0740e40c0002e826600c4038602a20103858661054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 565684982 1250 565683732 565683737
    0xf0b07090e06030d051602041104080706022a21372406050d0602031611030306090702150a1d06060d0f021507050a140d08041106072001 60
    0x60000c2c92a00300003880c6410554aa1140c03420a00c50741030044072107040d40c41c101d80040c0c841c0707264030b14486148081c1015000c0d41c0090207802c0d0802d04024540451124004a4040c02c1880491480032803241c44100038026115086184046003001c0814102c90000355694407900188030300030241e28510900b0209203d02d554101000524100400d0752541005419008650345144a4400d500b07003c8140c4503080d2808207200da50344000070014828810203454a85e0000100146400240440c04860b03095080000b80da0000d40d007403030f0340c034040101094004c0581e50085203e09008100c510380700c0390700354800390302403074908500d1000d001800403030010784403000c11040344210b010071503a201c0e00001c1c0502c5000c8a50b9151038080400c0040c0603038010802029080400490074001c00d0840d00480007410303802c055203007043c209040041001c1c07654200d50240c003445940034001580094200b05000141440700000600510641c000201410160074110030036088021a00b42286000d8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 565686232 1250 565684982 565685009
    0x6151216090608090706051e160c1706040210090e041b0609050102031905040f03031805091e07030b0d20030604031403070201290301050924040f0b0709 67
    0x2150203540a2106a4851202d170700440b0007403000f180304102610048414407424411032201491802d410384c00030540040350741c1d002070744005000c107140d0b456008220340e42e860203503d01050120341d110300000d00020b100751045218042054842d4a4900241241d03c4442c265800c003450a48082c0d86151220180c603161464006401c501030300010b811144180c01452501ca58040900c00c0c0c00d01445c01001401410301c004208081d080130010059403003031301d030f0440100c59001c07042d1000f0003030360042e0310036135040042160070385540000490624010b032101e60705450340038060300607200008081e43c0140c400465402445a107986035661222005403407880e40c00c7c18024191202c00880b03029011071703403ca115003504810f0380007d641c484800d2000180350b5500500c0303152400030241001c031010480107080051403500327100c0d442e00141904020f00300d00000301e41d00444550810b51203c8003481610005050000c240300000c001c5a1000d080100c80c03400c2c1501a001000500400c690748104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 565687482 1250 565686232 565686239
    0x15060e04020103050a201e0310060212030118020304410607050f130f030c0302090f01240e060a021c023007020d110102100902090615121609 62
    0x30b40c8140411b00940042e2140c100c16003410341c200341d074000d03000d25040241c81c1ca1a62100850074015502032807242d600b604255140c10402440e0000d001c0103541c48075030400040001c880d81032113042030030f15203aa000d40ca0390390b242422200c1e000180c01c00000c4140c21040c01c08403d070346042040c000503018940141034000c1c411980d076181800c483e032a0106908118505500015802500000c4842040c06944580321998400c040f000344d442180c000000b03010510071890711034442a403100540c4101a0b056161070322024113a00c149051402d401c20b0841102d600c9441800000829180505552380c0d480304c001e4005c0d603d0280c0b40109040c3c40304044082c00052000c034091340c400700403002e05188403581018032980d4511119010034942c108004920041c0c403050301c41e00c4454066000c000c19140250000790400c10007065100b1500d00c1c0c4230340140103982d4980600e410401c1a01c0c0c0c0000112a680080a14405d040520740c01c40d10580c2005020743c03030000358004024072981c40700c14203680d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 565688732 1250 565687482 565687501
    0x60e030f0f03031e040c090b0604030501060f03060e1b011b0c030f0c0b1216090305060a0e0c011b0b040c030b01080a022713020f0402070302150c040308031315060e0402010305 77
    0x81c5c8001b03140c401d05120400818815401c00d514801c80100b50034945580c0340d903100d0031264160711041c40340740000800c2042c007800740309030600d103a911009400d20400f061060b0b0f80c16121030310700f40c0c14080003442c03001152005014076088568860702c002090380d103e040c440d9110150b071100300c1d00d60300d8819002c82c0c1c0c06400e800f980c91050190070140855181c0c4680d02101406140c058010800c0e00400040400d408128040c021400d00c4000280c00051401d40c0f402c01c1a03007a903407414400154280303020300591005402200350800180c9405450b145061030f4002401e51029020003030920000c50a0040803400c600e045108842c2c3c200d05441400006004568845c0c4a480c1c0100d03c0e070000782501502c60394580d2181c802015560b0110b00540014102c0c1c021110580041e4030480c04144071101c0024405e0700000d03000c01d1b540c1064515550700d01b0740d1000402c0448070500394500c1e40c01300000c140242e003000b1400c17030052111a4841540c040c80700b00c11203059001a08040100e00c4091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 565689982 1250 565688732 565688791
    0x3020a050411030f13020405160201270803090f0703140105011d15040b0424050303041203050f0c1c0e090103020a0b16020306100608100b04060e030f0f0303 69
    0xda61628103507030b5018000803104c0c000400c01c00070320905c0c200120040c1c2c0c580c400d1910441202c074806050300c0c51118000c5c211000c811003251288103000006103803c005800d584034196200903003035031300c1c2c0d41c41c140c079810064800f240d103900e44200140481000714803031600035445071120080195070390310602c842d0f801c10b202000e88107004840b400303c0e5821520042e0a102000007500100e4034140c040c0118088416103e200f41c800f10f1141c203043c0c0103001c41e4000b20001d00d012002141060306000180f4034000002c8001018040c0004521440d1100d10b011f803039070000e04900b612440c003400301c0702d03a8100c0701c4000b0010018011070a100641d18000101505a0b40c000d8220822507003450f00756521540802a880d406c2d54a00c0500d00040c2c0e420019030740702e12291516040500d203001c4003c2c0180501800d2450a59403480042c002c0049842c25501140c80510308030140c04007980100e8240b00301102e108105000350043d030110350400100842c090b108503d90010f804040e00c0700c003401e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 565691232 1250 565689982 565690001
    0x2150709051c03021f1b02010902060d0b150c011e020309150901060f0b1b1b09070504080307050601170307030914040b0303030709150908190c081603020a0504 70
    0x518080c8884603a210800d0504841510a0045403d242030620a100440b1403120140000340e80315030019005a003003d10100d1541c036071f800240701c550041c1d8002011809982c0d140302c01c04e40c0d0780140250030b5888801c403416030704009400964030002c0d49840f80c00b03000300145469010040c901c00003298450352003200e10500b112009850203540c2e400e01424400b20151000c0c5156403109000702d40340d0615a201e1009001c405070041d135500c1e0842900e40d0400041c540315019801c201010484103c1030b00c0d10a0002008a07440b020581c0c80440503203080c01942c0201240d44004500d820070890000b5040c3d041c0c400354565550b030310116162441e620701c103a10b0010001070014508001e03544202c61404c140034001440490034801620100c0c0c5188c1044030b108000801d610744c01c01041d80040b810801e140c8552074809101410000c00caa9103200059aa41c0f07408140e000c04c03410311041e03c4ca2040030301a120700b65a58500b54015580d40d099550005a100b0105020300081515207446032200702d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 565692482 1250 565691232 565691239
    0x11d15010806040c050409020f040305010e03121b07120c020906030303071202090303071704031209051008090a060c03151d0118090204090b0411040509191e030215070905 75
    0x1aaa00c0b8024800644a851000d02c1031020034000840c0390740351070018190340c075103103145d258407145103060040c00d42c1d42e205200c1000c0d030801c110841c488411220f51a070b100519810100381c00014000d1060203104210b0050301006040054603400c0b54048084d00003240201c0b80c04006807580e8080548903c400d4551704080350308180983c40885031a0003400001d00020241e900703201064498500d80c0603662040c0300710401c0041e09104016449805403410100391810111a6040c00e01061211209000700402d100603003002078840c1c1020811044d00796413010050002110201c5c025001e0020b82c2d18000441c128003201140c25003030102d15040d82c0404d034014045992034107103e10710352220b4581c8440083c2c0c44182000150300c581c059071000a01c140c24180341c52078141009403001080c041064452418001407000703456000500308041314002425103600040b610b001750340d00f19a52915550349110408080034144c011400c00b84e28401000c4132011555403440441d800700043c0039240c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 565693732 1250 565692482 565692497
    0x30405010c080f06460b0403050316020d1b0906060e2427010e120d03021b07171903140a140d06050f0613030209040812011d1501 57
    0x2040c6050780d00007200345d5048002282113401450040001800b0b0b006001075107540390303090007040a07071080d501c0041440d21441400e040c110381d580c0b074032031040310f881c10030181c0d10041c41c8055581d180c0550020541c424540348181504101160254400388604271000d4a080790000d4040d0050f100c3c090f9800004000c0e2503401d080180a40071401600d610074520344003071081099001c40d4440d1b030311031540400051400404840001091461a1a000c6008841c400444003c2c0d54000401040442007800c002d41c0f10014440c02c46041031044171090708610400000188441101d5112007901070030300140c4000003241e851084d00b54014404c01800a91011900703480441d003840500f905442d60702d4949213003031013103050643e0b40e0401c000c0502c03582d9452404014a1401e5440941a245c003580c956050041c550441000d224840c480030f8001c0b010f200004041000c5101262900104d6400c0703c042540c40e681d4076410300c1884000c0d0340030080b20741d010601214080c0401300920005035613020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 565694982 1250 565693732 565693741
    0x5150609060d06050d0b01081e0607080603100903030b0a050616260a320915090a2c011a0a0207030204050c1e04050a1502150a02030405010c080f 64
    0x40780e0b100c5401520300b260341d5103000c074066481c3c18034400700a000d103540401da035040170146401c1070860990b080708182c0406100d54202008508103034420b21504000a4690701c19000ca4203200d0100b43c0c511040d881c04414204040d090361084484e200c083c2c50201009032600c0074080103214480e41200300001020381000001d80141c020f50160043c1c0d2000700303000420200d000d031680c1050f00400e01140321210003601c078800e06200c1140707010b40c900f0340c1020680c00b04a201d445118240c00540520140712035001c1e54038500084595aa10241c40700c0801070345d405031800803280d0041342d8981039120602d513071891a90718031380364140c811603030780d4120380402d041e1024803170790042590740b042d4000c1040010241c0c5e20341c811688a42d0000801035500c0040c00c14081002440d100001c04100052009201d1516803440480a6503c2d980350750803040c903540c1007685440090b294001d50031450f0030400601e009150003440c0510b200d00b0003031141e80312001c401c0e0388001048950000e04240c290005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 565696232 1250 565694982 565694989
    0x1021308070521190b06090f040804120c1a1306050403080901031d06010305030a02150f040b0402030a0605090c011101180305030a0603171b0703170a170907050405150609 75
    0x8900d012010b5040703a00c50b41032010241c0040c4185102654540008410040301d0701f0718000403075100359000da21240e035103041e0b95410002c0c011401032201003000c80070765030304110320002d4240107481e98203849154105100005545035201c8500820078450342c4400041c103d001d0400d450540390312198060030848001c0045004000c00480d40700f81760b22004d600c090401c0240b000902950041000c0e40e80c580c0c8001c0701a02e088800c00c0c94110010b151020480c1c0100050740158125504c11054103e589407800060300e01806810098981490a020b01c03008070300000344200001006c0c0c1b60340c5c043d440148903243c00c03281c0d68980c68100e810b0300d907031000010b072260300110b520580340e00c0e0020300c00341ca0b80c07600d000f16402210f00610042000820300b50011a4111040c1a405214020030002c1c1c25a034aa0040030140700024141c201c0210380340f04603c2c01410340c400c0c0c00e51071101940d100e04d08210003a560b460b6030700c01d20703004907c4c3c1004601941e00c040e05280d0100c2c8007525980c0703410804000d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 565697482 1250 565696232 565696279
    0x60a081909080d050702010b01090f12140319020c0604150305040c0f030c0e180706050f0415080604050912070201200109150c020d0e040b030c0a08010213080705 71
    0x90304000c0366524280800a00380700040d0540c11401d1070f00042c5403412590190840320500d400a052005600b010021204101c0e00c101c25540030b0800b031076000c0c10340d10f012a240c2c4036010b60000c6500001c942ca034150003003509000b060f0202542100c4e40d03405403502b80481f42c1304500401102da01070f0111720342c00078002d410140d0814030034500001c42c95904c80d100c1480c9030300e5810032035042c2402441000b1810110110075041654507190b620415003c0043c5992214184070303203010b2000100c0c103c0842c0004c00143c4d0000c1260000c010a030a80d008001030000004541961007146031102080048000181100300704194401c4280741021580040d241101000302c01802d0314041c0e24051003542080c0034035003605200d004010020210080410180e40b456014a03045611814810165540c0801429840c0030107940014000c00520003090030000180c4610303403c50f240e00c400080c0034005600a01c21b00000044070030b5000d48071b2441072b80741d400d20711400752301a10a00d000101003584051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 565698732 1250 565697482 565697521
    0x21070e1503010e04020f031b0901090b1f0509040507030501170a020f210d020a0c0b03090c04022101060206070306051e01050c1504050a030306060302030f0c0306062203020f060a08 79
    0x3206c000040c403040041c2c5428032a01100502c555414402021802d005c0d141a01500320140140a0803d0341004a490b00000782d8000d51b080494a00912507540540f04031340c41404050414030040c0f40071b81f8082c1c007800d02841403454800b040d0f4440a09000042190000590300614891104441900b0810346080c4441d4140c800c1c544c6146a841c007403000c20101940908c0c40c2c002d400018400d041c40b6600c04005ea021174805c10302082002110080402c0a40140004480058442c01c0b820740014006801d41c10400840348400b001003646a000200284620010340d01800241d46510610440300100301c1c00f101074032101c4021502c03960040300607180f0100b50300304a6010b601d010141c003119144c140c5042e41c0310b40084440700103041e8580900000380c0802e04055107141460043c80c0384561000306009190b05010001c40c03429507d000c2118080c00c00501c421011403003801101306014607620040340305421900f21081c1c00c1c02d1480c1a00c0c4005000d40701c1d2081581c0310540004041c02421 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 565699982 1250 565698732 565698739
    0x15050c090306011205060601050c0d21050a060e010506070206030103060b03011b120501060327050705030703060b13091e022b2d0201050f21070e1503010e0402 70
    0x144061601d0400071a03009203050710203a04109900d040031800d00308080e004034100501044030004584d80020030a511410501e48010711007000d200c851480303140540c0156074141040c00780414078140d90480c1302a00c41142000c4040d0b681d49007040f10030b11400c40f000b50842402d000410200e00683d00000c1a00c40260000c18601070b50140202440b0f1901012008900240c01c020602d00e15881061702400c02030404000c80503100640641400907601ea0103c0c400250341c01808100050041c80020035000c0e0441c0c0300b1984071300d071201c09030010002c00b0b401405840420f0070401103d001d603010340e9401100113040008085081403840c0301010040c0e80007140140d03070004285003c1400580d080d62103e0340c01c04400c05103800404600d40c0d5152411a668058440700d5803040849203100d240d03070908000b40c0e11040c85007040c246000710b8100c8803a11a800a50200107408a01c04ca445004039543e103ea1214001040024440b02151280c400038424401030007404410710764660002e0008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 565701232 1250 565699982 565699987
    0x327031412041505060102010227030a05060a06140418141c0c02030d0e061c0f05040f15050f0a0c050c060a0f0c0e06030c0307090807060c0b010b0715050c 68
    0x10301c50381c50070300c29901241d00900710155a14200807901c1000c0c0c00c81400d100035807520f46c410406c4564140c441600740785008008030200403030754080019041c1c083d84641034034a00c4c501001c002008200c240b10748402d0b00c60407170b070307681c03092420784260138180070003d58540000082ea25025450308010103090501e104240c001020b05801954501461025075520402a55140b0500d0308007128200103005004180349821002c0c0c3c0da11098074503413245190348520481280d4482e00150102440303c00030030f41703881c06200a02000e8500c103d0310030f0003064080740114195902e002140c2007241c03009410b0071840e02040344c003000d81d040b440c1034003400d19003035060032200d4411a0800d42c041d1008880c00341e03142070741900c2c00f142e805030004d0342c01d030f504043c2d203031182c200c000c5046480700a10041c03081c0780c00800101c400c3e01a2802402600807038048442c00c0b03850720006410b0200210085d0362131982d08000141c0c0c01d0208003200c140310303032081a804c0004d076241244405450040e1849a100205 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 565702482 1250 565701232 565701247
    0xf060503091f05060f090912090103181a0c04080c0607020a031203150807050117130b07050c01050c0301030807020d082205040c3b0409030e0103270314 67
    0x3441c00103080b00c80b103900098904240040219907600c0b82c4045004100d1402001050040800c6a04080b04004440c690358605440100c004084458008c41e112901c01640414000740c4280002c2c0032810340d0110f9070540381d44407c021540290710800c5c840d41e20190080c07041d420460050418030b407019008002d09a2030741d450b42c0d4560505c03910300000940e2920303009440381689940c40f008200b110042e0034868100310000b00b00343c140804041300c000e82c14000ca40d026821444c066182e94002c4070307032103c41c100308100801c00d500038a140303ca1076080002180741074402104a074122a8400c000c7c918040159007444140c810707590040e58044024080b41405141c11088200c4086074101d20008407070a0404100840d401020301c00101310750102c2102180e24002c20341000042940d496212001c6040c4171005e04000307100c212a001820401c58804047e04025049090402620300340888401c194603031012603010480f0400107490742e252900400e000b082640148460040d8541c544080c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 565703732 1250 565702482 565702513
    0x80c06070c0618180c1e1b0515010308130f0e0a050714040b070b100509010506030408090616031e02030a0e28060f03060305030319091a090d02070f06050309 69
    0x104660038070000d5845103000d030552580500c1c01b0f4a040c2d00840c40d80d002c0405441d0007040012284001c9021100021039581400010040c400d251540303030140c01c00960311f914100c511a000380000c3c02c0c0f5000c2c5c0c83c001241c11041c1c2103005c01659802c150300c0c07000e5690301180c0d2000d420b018092a0911401c809285091040c01e0010405072070003890f040d969120324035128000c500c000308440c0041030401e109010030766843d6402811110304441c0c1d141c4a40307450030304144e24442d0385c41d02580404001f808200c61003101c40c028040324080d40f680100090100850030081c19000700000c010307042001090449801000a140700c0b003400341103801d40c0c240407408100004e10116800d2400c3e8001403080003040c0e03208400a03c610a02d01e4280b02c013918503910036942c2d000103000d81da00d0744860340203100d880250794040400302e40c0040880700b1800a18001040d03000b815a1700303007203038090601c031500402d00000b9004112010035548220745440c240702114903801c041c054460314090600300303048882 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 565704982 1250 565703732 565703759
    0x120403180806060a0b0319110d0906090b0c1810030e060a0207140a03020c0d020103020904020d0902040606031415060c0a051c09060f030c1107080106080c06070c0618 73
    0x107054070081199003820020456000340c40e60003242a00b50401c204211816248814000c075190150089075803a8510381001c103900403c5421040c0c0341c9084600c0c018132050750043d1031040d016104e15840c640383c1c1259040103124a080304011040d0a40c000107081c10b1107031003000a26290b24000904150349848507080c400140d4196a1040c0c0204000b0140029804100000c01428000708040c0100303560203902d41906c4034580e4481da04101401c4250390181d011030329101c030021720865640e41d100340310030000d10040c2020f83c0900e241450204d202c07130203031050955104814a200b031301503079071103070a43e40f0204401c0c07807a402010520040030b000008001c03588a05104401030071009038007100703441d1003403002d8450808101203c21308200c0300d83c00140703805000c5032600c0d001c6002249501d0580f80c03c50849a000c04611640a00041499065220b4000d6505080507a8007090b241b80400a49014400018000300c0440304100300344c90040c0359900d03e008100f0031b5219801d07908d019050659 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 565706232 1250 565704982 565704989
    0xc080d0908070b1005030d12140112030e04051e04050a12080412182d081f060806010b0a0309050106030b070e010f09050d080c060406060314070b12040318 68
    0x100d03011890000300f18400600984c000224001c2c15480c40c50440000c0c0e441607910200070a001c00042e00382c0114070039030050a08000c1400b80200c19594494646506009512080d0001104988813101c0b070729050054030301480950340d16040d404518100c10328101d030040c5c8211118462420008002201140280341001e8079480d050428a41818104400541d0ba13900000304140c1142c154844185400c2c01000e03504c2104554424060300c20700440d54480c852907a001081c051000001d090200060030f4514009004084031101c0b202c01c005000e441d000d01803001182c01200050003440c01160250030204010b00d07000c101c00c18242c84036801c6a07201c1d001558201c00102c2000400e5811002500180070302786090188400003a0004200e10080e000d5988036410070400c0c5020300500c8410744a80c40c00d207009170340982c10b05260800061032607120455100d9074940c004400060003058036400c4440e2002c0051425841072a11940400018401c40900200303511000a0b02c880c0b8083c0b0025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 565707482 1250 565706232 565706243
    0x315040e07091e091a0406201306030e120a0207090e03090a05010f0c1712100602010e0a030905010507020a09182d3309031202030105100c080d09 64
    0x3c402036074514460305804800201c1c201c0c140a180400140307031181340036004a41041071915903c9a2809101911444040c000310752444815000042a02c40082040040c2d649400449a94230314007a000e4580d080390114843d00100495140300c100e4000510b2010281e105450101e80c51341c44660403a1002400462075074004500c000003400e00d03000c100090207090a0030011f102600d08010411f03501980700030806114a29000d107443d0b000303419910203070348400841c441da180540a101040000388a100300660030204a00b81e42c03100801c80d07141c05a0156140301d02181020015201d5602400080340c21030f501d581c00085941140c4104d9460100c070002031190712643d42012401d00c00c9150024066600a442d51803452080c03082c003a603008d80c00740d80310503440608004d0200600720319030401b01c145540038114002419503403000941c58400d848007020002c0242405080340424060b00390060900c00d0340c0441940511140c4540310f108410251404003444420401e44051004c2102c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 565708732 1250 565707482 565707491
    0x6020c0a060b010306090519090314120604060609180e1623010513090e1501060809060f0f06011209140c0a0909020d0b041e030e03010c020c01050315040e0709 70
    0x2070560313050140f0001050024401c1c05903003072030f610881403107401481072040c0547e103a406e001054041e41140c55000c541500c52074441d00649800882c0510849085120300d1030284081161070140341c44406807120070074408521082092540000c02184804421030b1050f811081190042100c0703500c040e20981440b031041c00a4908800078a40403065010305020007802607241c002960b804100032140c09200124030007415400302420451003042c6480030000c820700200364035400240841c0a0807844040300c0740380d43c07403841046140e20140c071540b801e80c10010200c0c0c401d611440f010a15140c0d000d0380000e031025599140002402e0740c10000c845500000031012003490500c1c1450300501c0340ea602840403103d143c0c00146c0ca00e848a01c01068198040c010070709205800c051440d424a609503c1001d003403103400e001d400017078190b41942c483d41c00e080202d00d0040c804500f0311080801038543d40d0454a0b012105e80d4909020040d00d40c200e995114240c0300140100311034001005405000103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 565709982 1250 565708732 565708751
    0x30c03031728090204110c1c0203030411120d200c0303040509040c080703030801141801140301090506010b090102070609080712020f091905150604090906020c0a06 72
    0x8051280c02064041020300075420009108610b900304001c8200086100740070752190742c0c0d054010081120b010303410601d003e043c2d1041404030340c01469082a0300c1c0449401c0122403000070044c11100e00c2c81d0005800c1403021600250010020409030003009110460400c0c800e600c2d2850500b807100414001040003941044000709803083d550b00020002c040c003403a0380b002003c0b175901e00c50b900c030310790080c01c51100140030301200c4140b10014007180300550700225075a050007414040203003e440882610b501807138000e85040405807030045808e0701c0c1c00d0b68980c0380c91440c40000d00e110502c240c06548504242000401c00d205480c082e0030040d8080740c80e0601031000a1030306440c3e030498010300c01140b0040c095244001542c40c11990f0300c500c10445d41d2814404640202c80e001c00c02500201040c051200000c02d910042c82c145004c1803040102d0703030310309400c3c02200403041002500704604010070300816603540c00c02d545280c001c1030050720703100d1684d44c151703d4800d601c0015261a681c030000780 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 565711232 1250 565709982 565709987
    0x180803092d0a12030207120c02010e010804020d03081b04060305010f090203101503020f0c06060925050c0a0f0309080f071a07060902152503020613110901030c0303 72
    0x8841d070403001a511020780070301d00d4550741c8080500e0301922061603c0112802203110740c0442d10000d40c4540e00301c001c0e04e6a4400900780a044010407030101c0d000c0b4510007080d510404030188601d0b0004d150039007a00454070282c1d643e000107003110300c1006a140300c0c0d25414550300001d000802030740e58006415894000704020165268000506940c0108180805089600a09400c0d80d003881c2e003419030320010700401d400038403c4450f4800b80800219115900071008641d0070301c07070402501c50381c4203561444420440c44403c003040b111220032a0341c010200b10701c2a00584100c40c3d02c501240c1204c02c8988800c0c20556681702e044000520b011020f00071000305101441880100c41c0c010800700c0d040c1418058840d11481d043c0c250200c0c08124401400603542184003580d40140c243d4100c400c445145c003a00c2e0313004003900307680410342130401c200e09a0456000c4007602d41650181030f1540315444e51500b0a00140340c00e80302040020f48803869565100c2249008512500b03069038030501d1407402 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 565712482 1250 565711232 565711273
    0xc09061404050f0601050909100e0a0b01020f01091e15090f120806090403140717090a0501020a02030c041503050303161d010903150f230919020418080309 68
    0x520f440c50f91024140581c0d82d0300030f02600e600b8101118982d14580c6e900d84108400521644056050440c220501407450401e9200400000c820b0b03080d00c4940001604c21400c1e9020302c0b100601c891503401418034001d4061a45503522032241e807943d18400d408100c0b000c141c1e040341c0000e0700c0c3d0b5102010440208030000640348040ba081d410601c0840c82c040c4009644040700a03c044d0034003031144444a29a40100211161a5440300244c0c0307030010010b0300f0b1441030b0080e6001d940100c18182021130190b00000d005c0c52516801401410115580010b10001d05881e804074214094881000300000e24144041c40c420b10007424001c1861440d0f407801031400b0250a0148005251441d400342d15980c841c1048065a4200c00300c0b24a03043c500031528000c200945000322001e25010305003540c4101144004003202c420b407101804c6480da00801c5444150f04410030000c0f0344481c1e03003400141495040322035401d00c1c44040c41400701640d1101c40d0954421183c1d2030694200c0030f1100c1144c10ba2003003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 565713732 1250 565712482 565712491
    0x110108060909030a080601200a050f0f0613170d0c0e061809090f0d05090a0603060602100908070606090f050f0c2212050f07080307020a120c0906140405 67
    0x4140100b4101050083d499100384400700b030400200c240040c0071a4001d444a41429548070602901c00840c0768400ba01c41d54058800c070340a00800c00c1c544245200017800d010540401e00260455172506800c0200b00c0007440070407a8400f9186d801c0500004000c005400c0c040104940812a5501e0344c90040103100d00c941943e00c43e0405204401c2007203403503100c0c9150f0640c1600c030180d071a2180562580380c41061040e034200c07446111503a0000a5100010f0a02c00c541958402802b03900ca5400b582030711620301800d0300692040416440140d020340201740c9040c002c0c103840b490002c0503190142682c0b0399812045c0959120110000380300c9051158903800b8514113080a807500306150000f009208050440103407c0c3c0081920074883d0100e817108000304003618000382c020742a407910039100c002031480c420050043e510006800940070017140c44142d8010a0700103980e09180302c000311180b042c4030030b807040c03101d00c2000329100030f151040e8806803090791101540840c4040410094560080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 565714982 1250 565713732 565713739
    0x1e06070f021912030f060f050111030a141b0304090b031c050a050f1215030d11031606020d2f13291303200a230d11010806 54
    0x82d0100a01e181d0440c80070501d43d070200061100c92070021084000d401c8000c030420180f850310000107510b0035039410500403030701c0a8a410b004c1c14034818501e0340300e001d409030100201c0d40700d200320304404207810010240041038032281c0c1d18146111052510f15082504202c00d03203603a442071000340d8502040507000403903005900b4550003441902c010880e010b01d441040174810040751460010b043c0c0002e84500855501c6c0044161078030340025410000b01760001c5000340120210710040c01d00c00c8084222402251008502d041a42c444000d0980b0040a040d554554240100d0820038158040c4d406100c03804240c402c090703a403044920ba07800351062000c0240910404c00303410b40c0020b03820044102c513115605901c05c0155205001c0e20103040781d0005440c18030005020fa0820704d1a01e2403026240210b0003401124a0004002000315040b202c155010010070410400126910401045245409071062141a4940c080703240198a140200c3d034903d0409016110717542d101550652151044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 565716232 1250 565714982 565714993
    0xf11090c0a170a0e0f012003011d0705040905071107140f120703020603010b04080d091d07182303010203040c2d0e0910110a111e06070f02 61
    0xc030301c06000078001840c940349030400700e00000c5001e0025484250b0305003c0b03406941c0c28044130061980200000b0b03080b52440c0078401c0e400640d90f00c48a06490584803200045441c40c512005c4100e030b0301070300801800130401c1c2000080780e1001c85015484c000d031b0068403901a4082112000c0741499202c0c1c010044001808041c0e0103150703115402100c220000f526080c1481c00602840d82c06c2c00c1c21508081e4001c5000400014003e0040000304200c031020800d68860110310300c030456880031680b08403441c003040c0074416581814406d40c103d403c0074450409240c4101e8111255490000c030342d01007408003a05060f004c0040c00ca40c060511480c10440c0210301d5460180d4514011520038010349640b8015442d03401846850302d03134018070341d81e4120700c040d03d820b030340e18140c1b50305401c100e80c450040e0080803500d100042e140d001d02848504204240341c100260003408680e00881c0c480d01400c28403817606000a10f80d01c5850380f0b079094032020080d00b030901d00000094003101071001e12104541c0300e03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 565717482 1250 565716232 565716247
    0x1b1c03261e040c0803040602160603052e180222060c080f1314031618020a1403090102070b07020a0803070e010e03070602010501051005160308130f11090c 68
    0x95084504880c40c02034446a8030750f8101401c6600080e088030342184400200821416000102450a0340798401d001622036200c150032001e5034001e855040407030112140032075003242e040000070000400949010190317076491f98a1040c1d5071070350340c002c0001075000400420140648148900440c03410800072030091038014020040070760000041d0001402259404c001c0c0c504c40c040362040401d15481c0d054054a40c0c0351242d08070405004a4070a00c0b40c003c42e0b8400c0144850b000301101c0022001100c100500300100019500a062200400c40788030140000601c00d14040c5000b03a100c4000103888984910305101c240f40d000c1c1c80309041d9400040b9490000381d00c0c10440c0d07800042841c1400b10305040307100580b020800380f204580e060040711004215594154001c074101c50301150501480c6101940c141c900d4458006c8a011043c5401c2000011038010000e154020380c1e400b0600184112640340e008500c84102012902480c2842e0031544500c1e0909040b50000340d9159a10b1a00c4070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 565718732 1250 565717482 565717501
    0x16030f05010f03030c03050415120f051302040b04020d0204170105060312030a0b0103090203030307020109030206060f031207030c0804030b07020706050c0c0910090c05030a051501021b1c0326 84
    0x60b030340701c01000c02c40c44103120010503124801303490040c012841484501c1c0545180907044103034850f5804099460b100081d01000441d001d00f500900c4400081c00c0d444d02c0c81d4080c40064406c80101c1500940c0800400c0390016540c4000c000408007440051b0744c0340c44e00708880e8207480010700f009100f42d000d000b020050401c0c48044035040344141c035001030b4002170500103070003078000410003130b5060002004012800d41c042d040100789510039402e40d0184c3e981e01d0108800c92580040c5e03550554442100f03060000701d00310007000614000c4c103101c4403541980d0355180a66002d5041240c0b03900300740060140701e58042000101a020a0502034108a010310722103554040000078a0b11a890010205040010324070b0341d5800351030580390038000c0045095015103160b0080d10300e1a103e6103010001011000d86040201c016801640075040e852005031003e07542d801d1103914035521101c803210001d210b00002c0e404800503482500c0382c0042e2441c1d004038046240e41c03031499000480034031007044460032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565719982 1250 565718732 565718759
    0x6030c0909020c01140405010209090a06060905060711090c0a08010506490c270b0c071d0106030c2102070f060203010801090b070f050a111516030f0501 67
    0x311040c200603111114500c0e100c4c0588040802c0080014200301808103022042d0010308480d101940c45c64003603100d00c00c07d5821a882c61190600040400390b061040d07240903401000030900441c3c555039100707164000554000303401e940c801901000003501c03424403078000500034014802150500e04001344552901c0502c0c04040d00100e0112182104000c03062404041c0700b4400340f081c3c503509000246544080c0213004945150000c0f80c402940a40244805410091681d103c03414401c00303d03240500004443d0884076103040e5601440f030012a104804240c005407160340c00080f20b08079454804040c04850340100100304004000d19000f040f0300ca8030250310b80c00440d4400040e55402d25007010643c60340010030040006000100000313a03264150085040344d8000e46825030240c41d03040b016180c0c44200524000852401e00c08080524024101d401050315650180e440300c4169041e1000c815031700310340c2e07a80300e101110450200b040d8940708050b00380c070001000300001d5062141421051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565721232 1250 565719982 565719989
    0x216060c0201120f0515090103020d030f11030c03181014090f09010e0103030305060603151e0402070606090e0106030b06040f11030a02090118060806090403110d1806030c09 76
    0x2060345400941103910403090340300e01038401c1e4810800404450303d01c038050f09050b01c1481d91250b0715040c02c01189080c0c403065040326070007480c009154250b5681903620301c0000d01030005000104944007140320041c401088039006601c040d50740c074030b454261a07a20383c000d040304a0089680143c104940b54000c6110340d07030003050212607a00d400260000440ca03043c4541c005801c41045030000510141500080f4141d9200fa1800d100a03a640c50901a1500080321410004000388150066a0519558500c0e46c962550221a01c0d0a000300c04141664071002c07044400710750b00c000170001000d02e071141c10400d011180c002d1003090701d1600c541780c10703100c007030301452243daa14446450a00300960210182c00a0080090703101d150100509000f50041c012580c0440c40d1340c40c4111007890441003807401d0364600d80320f07400c890700d45106020008000030412003c1c8020000060310b00d82c030030010745030300b84441da80744450549620210003c0c540164481400d041c10b110a0140c030903009151281076 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565722482 1250 565721232 565721237
    0x2090d152901120e012a05070c030f02041116050f060903071403040906060c110103051303050904141807051e0d05030f16110a030206180a050a0b0415021606 69
    0x21a14a8190100100b84c00c8910000b0380d03281143d00322490b00d160380d000958031400144604011608103085d00e03d0702c24200018940c50401e01c00307200065980d2001044603001801c0060b541180e104481d02da54018003c0800d5460044022800c00078208248560010b40714068001d81c109461a40d03070728046e0380303c020110219650141005501041581e008064989040c01813aa45000180088402c20700039661000c80d1040120a540a4050140100401400f004680e400e42d101107407150043d40705140d0003515582e12046000804034414050f40384040010300c1c808803440f24078a40341260340014010465070000032801b00d280c81c00315036480419280e050f0742d11064500340703095105c1e0030b200d41c0300346401082900505d000c156006000900c40d00528155611000c00c01804003094030000798000001c00846505581649068000b108058080143e16172030740d001649100f0580c000d9222240080380030854400d03150501030f0405281d00181c50910640d030702052812080780168000e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565723732 1250 565722482 565722497
    0x240313020409080f04080d080402030304060e030a021801090c03090807021023341b0314030c0c0d17130902030907140102030a2102090d152901 63
    0xd64075035801007401d4581c00060540e0382d424900e0180d0a0390130a0042d04124884d00855544c5140580c1609001d690024015410a4507141c02141c8008500b100290940210f030904401a21000014030b8a40450250b1954540c10003250404603134403003103100c00305810b007185400820340c02c00840b190550141e03000c2144142d41082174072160782d80c0c20b614204d400000d064000740b50000c800351090400c034221001c9885204030f40d0344084000c4800d144600402c40b05c003d0b002a0074100007030210355418000500403a03a036241c030201c0d044a61032000c0540c1001884407503c08003800703008280d80c011200440300d0036090301d8840d003003c0240b41141c24071100040c030958032000c00c02d802d030083c26407031019035407450454005501d4520a10640c14041e0068452500560020042d690b4a045a594920445050794991111028060080c0d10b41076420803000c00e95403a603107251900d05025592100e000d0200110941c1104c41e103905230741808407043c1c07010b903208000c6507030b2200288013482d1503039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565724982 1250 565723732 565723771
    0x20307080f070201090510080901060f0e180c030a050615061e03040f021e131a0918060c031b040303050d1e180204050a18081b0105010303030501052403 67
    0x8400c5845900100e40c801020007d0020040e8000341040c862010b5200a022490ba1420008049038a90081d0b1304151450400941030034812411410014042011a810340e40504040b9041c881c20103010388050b00f000080207903801602c171040341a032070305852280c941104015001031400f202c0e03012544040e000408142408240e038030403507215400400404514030003400c071680d07500c55007810b94001c0340307200c0e0403000e02c0e881d13072040000d543d0510005520350740600041080002c0e00815010b07190072001440030b400c01c030812007207105810072101070340c2c2ca0802c0540c400760b55400000e242c8510a08020502c0000e5104082e00e600d400002408a488100320000340b64581c1951520000d440ca04900e0389940c0e1043d6442c02c1030503000303503010400b60b20360114500036609140d0705030f00f00c8080300b07243c0d00000e0081d4008181411580c00310602e4803031000901800e41c0c2c000e2f4815000030381c03500018040c0d85088002e14044c0c040c1c4203001c200b004019a07180722070b03003c0108240f8800006180c2c2c134 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565726232 1250 565724982 565724987
    0x5070305070510020f0a0807021204090e1509060108070906080a0308060d150b1c0b070c0c08011119080603100b0a050d0b1005030a0c09050a020423040507020307080f070201 76
    0x2510307070070820072080d901c900170540001c034079401c030100c0c00c00010000001b00300e21500104482031407265840c142c83c9030a06100100340a440c060640d01e409100345103078215006007200046014500c0b03072002e000c3c5949050030795494031449410890041e40f803c6420002440002212600d80d94035080103002079540000040b44001d94000181020000d500e104d00c40c403001ea40722800e0b81d20700700c40000020104040744987c540030b410340100a20b0992021603401402640c010b0f0a41c0c0c0310345904908181c8440c01542900c8220f24181402e100100d103d9004800701a07902d5410150b0b46400b02c290b02c0c0050000c6d079103101c080d401f00341155450380345000c0c0ba140c00000d0005020b02400c0040655503601c3e0503408030304100e410198194680c0000305852402095800309030790824008500f840c03d11000c1e0005100280c41d80021f41d50811001504249003489a5500c015a02240c00c0308402c0e841484103a800092408045420400c0814001000b00c0c095803070311a810003030b0907240c03100c51005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565727482 1250 565726232 565726243
    0x30d080411010c1b03120918020315030304090b0a090212060d020f030d05030a051303050a0806030a0c060e0108010e01081b0406030f08030a2d150b1b12070201050703050705 76
    0x40c204030768000e8094a000c01c0c0300711300000c0324440c85102c800840c10300e1003110302d45454001d43d054407801c900100084039030354010f50341100041c003100e4101d21b9200c0009146a1050b4070800c8004c2d120010f0054a14081000c43d00030320110764150b140902590907104c501e81300400c41845542c0501c10003040d5281c2d007031083c40e51903025080380c007080315144014096030000c4818030300d00d0b403c260010b4202c4106504500555a0640b115802c0000e07201c415500f10310001c00350360b09031180080600100f41e5100e041030060003d602c4103104c11400500050004a05030050490810001e004020845000400c034034800700e800b804071280005040002e001c0c00946e40098400100000f00406201c80700006500030a40e6001c2080760804c0305035600c2240d030400d00da02035030a80c484409588490a03800c8480310300341c11800d110131262125078010311504040b241d01504c0800582060b03090004000f8540741c0110300004034146400c640c0020543c4c410010001d080003408200c0000b00300d000c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565728732 1250 565727482 565727507
    0x103091a1005030712120804060b1c0201022a150705060f180c09010b0d0b030706050309070501020601440c010f1d040b0d141b030d08041101 62
    0x100300000d007841012100e07454410300030b0a101e4001c03484000340704102d80d04c00c519132940c404051b0110355200d900607100c0c504020b0013034a249031a0300041c1c1040d44c40c00b440c24603a4240c211800e94000c2c4d02e0000a14100745816500202c00810010200a84c4a402217242c40c001c11603601ca03400214800c544214000d0040040840c440c0d030040c0060050418403240c418000003854841c03407100d01d00b10590304d40954070041e40218a4a0051000d075050310010038102c506450045540003c2c500403e03d0f2102a07486900000c2c004001d00c10032400901c0428018030091000b89110350400c00c502c100c000100300304800e29507040132060350144019540307840d040740c00d5605603030f14030400c144c0c51b4407850005500c9000981c40c100f0320f02c215000340c2d40e21b4074680e600304e054014180c1e07040c1400001e200030a845940301d41040d80c1440000d844c1020350b9203000b80c07080a814860032070f1030009000e2241d810710a129030000281600c941c0d51200c50340e0f40c4240c010605003860000e9034011780d8420790074031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565729982 1250 565728732 565728773
    0x100e0a020c070e0105032b030c0c02030307060603030305060402130513060f0e010303090e150409060204080d09170727140109020c060603012309070518090c0409020906010309 77
    0x403001070002c4010402030f040340d20a03400d1303800001151140d01400d007601350134070304490300c5604410b180c1886070b404804c0201090074154480072b01500040e2640d04031640840320f05403602c40134070170180d041c00350940003c0191000d60400c1650b01015100c0861405860301a0142c41e001001c03440407500030100078240300000d140303015104c0c3d04401c03503000c090000f6404100310070000164036008182440c4540444c560041d40c0c846007204000c00b401d104582a00c00036003d00011410880030300c42d003038010400b912520755440c54040110090460080c0408036030f04180c01c100800500795071542030f05280c081c0c0150705001b210303070090010088031610702c20680401c000400c1940320740d4010031005460034112901e0b82e0b90901018281d4070703c0703c1641d048145d075540c0c03070080764910310312950012403a0060702c1180b91034801240100640200c0d00c0e07046c5441d00300b48400c0c0c01051040886400045d54148600040c0c2d80100e01b142c2c0000d4404c504265a50720628240025041d0201310324080a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565731232 1250 565729982 565729993
    0x3060f010504060e13061e0905070203070c060f120f0e160b1e0d0203040305030f10030c12060e03030411101407020625030305061903020a030803060d080708041d100e0a020c 76
    0xa4403500c0803500d00a40d25014603010115412b1340c000007e54a00b5603100c4000c00400c3c2c24040c040712108507400094091041c1d5120107002050b490066082009912030002001070310314110624040c2561008a04000d00340001d004508221702210741c1c034682e143d02c01c0000c40328070070310681070b104000401d4200342c030100501041552020003140240e80d10f000551060321050300c1d1800c0700b0407500c8003c0c20310345400310800070000e80b00c940d03e203200d0055100007100b001540b802c60443d030048030102c402c0404504050041e00e80600d20f8900304502d41f8041e4088064a100f800040c8a0b1000c068802d941c0803410401807800c4070042c020707400051503078203501d90862a010740600415180c06102e0303002c110040502c60046400c080c12290010000e415091954840305110750006c0c1600da0451038032000d90000c10006001403112920803441c0540d0350f4a02418000310031603500c500600044017a0501c190504180709040642c1d40e003140c0c5003503540b106032048000744100c51444102d806074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565732482 1250 565731232 565731269
    0x40c032f030a1d06010e010306061e14121c02010509030a0509010302090f0319060522060203070e0901120b1b07030e041508010219031112191103060f010504060e1306 73
    0x22240810b049a100391018020b168955002f0320304a10082c54038003407003c010b01c0412034004170301c901076501c3e43c026082d48011420007001904207107003041c040c10130040344504030031203039030900c02d866120b106040510308000480704010000e11070000c000d030405401007041e81481d40c0c5d40da044ac0013010010122031000c8101d81111000300702c0fa06095481d1482c5c9000254401585120210540c00c004c41c018412030700c036504d040007900081c0c050001c000c1c008078928482d882c0d0708027243c041c0032481030f040b030003100d103250a403002d21005101502c0016810003640881c101c180a940c056941030801040010303c4001007002000300c1940d5050922003c0400030303000806500400c190f2110013803404241d1800c00c03080d81618100106901070388010440c58010a104216483d040844152444081848440e100058500c17180020109941c000144601490065588a9504420b080c00750805180c450080e00901208913a107004032640008211941401d5001e030340a4200400301c00c619200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565733732 1250 565732482 565732499
    0x11010503281407020c1e0a0501180e010b120108010b06070f0312060b0a1209030804120201061503021b0a0209150102070302030a0311160302030316060b040c032f030a1d0601 76
    0x584060490182d8400454040c0314041081b26600c0c201010301503481c0c581c64800116401ca0184008581e0300020780d401003051014101e00783c0c000c2c00200c0081c8d032662410600f0500441d010780c031091041e0f15180c49540180c5940081e0340c0451303048414400c1803e11410b007920b0146030402c1c1c5060942c5030041c0409c83d404110090108061103544000d20001c00c00298001c58901c5a40074020850000018001030300c1c40014130b2050030b6500c000b045842d62500184401010f100500b000710b9000300d400c541d04680781108100543c64a0b0041101000325008140c0c400b05c0904400710000c1552140da180e640204102c4000f1039000c3c00300c4868408a0500030030740c000c000e54076411409160008080e0440705031000090b00d40050103145080c003105a44104000c4081003160402c1d00c40d0302e80c110711350340d80c8141940300d403c588011035245111200319401c0e80400411040510225044528401c550015207610003848940010813880304203c0440c0024070004007085807089000200c3d0006 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565734982 1250 565733732 565733743
    0xa110d020d12050613020715050403120e01090f0b0603150108031801080405281e061b090504050702030903160e130209040f060e0304121101050328140702 68
    0x44140c0d07500b141640c045400c0307100380e541c140c500e03c0c0d00020074070608000100541c010401e65104c2e2005040411101035158140c69089030305801080d92102001011412401880b1140003000c0080205d840d09540f0400300100b00724011304080340c1040080d500d40c404000222525181c03880c4a06103680d103421107540c80e44210000c0d000210809001d010720b5001e14640341c084da074040f018002c80c0c41188c403032100882e0003052000c400d42070f0040ca100418519030300c005200001e000050303c9400941130080588044098050084031540c84058000c1d6002500d1400c0c1c85003100c1c0130881d9100c101080b840e5000d07880354940d2600076440000580e40318a1410011225400d260804940e100340111000c1e90007904043c1d008091600040c00194209040c800c8441c4500c3d00058409544040c451442d00107420a00120102501050a11034004081e80d0700722000d10740341d07155142805100b020070b0801c4004281103030311401010200307450754200500b50384c101003015226140000d8000d41c0c81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565736232 1250 565734982 565735003
    0x40204090b0a090c05040b03090106120f02150319020306060d020a0801060206060d1a09070b0c0d020c09061c0f020640170a020d111203041a0a110d02 66
    0x2a00410340005451090340104107504d9280d84945041c40d01e48090031240340e000030b06c1c10b5001d550703030040429038046451141c400c0720701032046011010814070511452000400106500d14424010016041d101107a60314103180d4183c1e015840c1c1c1c030b511010800303501499600c0722046001248620103254005103141c101c0c1c1c0160308481d0940c46482c01d00990007003003040600784501d502e4071440214144450b480c2c001505800700c600040d559000b071490b54000c0000e45c0841c0e0054900024103540c10011003490840440c1c0811183c2003c1001510100d15600402c00900c281e005075030a1245103064107000f0741d0040c040c0d541c0d40003101c20341468414030307060113034102e5105400081a200b590001c0e01542d641c800d584c840007400d10000407042e501d12082030116105104c0036500580f10388141050807403054804007040f0401c0400c110361000c110600d004198428441040f0000c1140b40500d41070015001480c2d65001c500b10464580c85000c082c0e542c0da108844500c142c4c960300003640c0040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565737482 1250 565736232 565736239
    0xf0b300318030d050c0636210c0c09100902070f17030412030e0c1905090108030a020c131b0807120c02071509180c02010c090302060307031a040204090b 67
    0x3140000c070402d6413a8024001107000640c0138000141c3e0169001c400e4074180c590700790500d00402d09a8006c0c4005824038005000503400003019000026603244c0044c61250310f0789950303400d0030115451143d441016402c0341d44078200c0b2101060030502c42500c220054252000c065550304018107005940010242c01254130042036076080a035a01e140054901a5510640001a5038021034085024058002c5c40140c5409800c014075010f94a84104c1d0401503035804424102034607100800007140c20503804021540c00400c11203070502e5022494650140301110301c50701d2001c018801070020450b003440c643c41c519011071201c07401a00150024401e80190f6264142090400c00c000e00792011000c0240259200003818811003005122403a544e090720320b018072842d56030b140c0c000c00c04094005041c03c50350703484000c444203a50a0081d01219041030924064461465003c41c03114480180404201592280d03001d410611030507040c5c844020042055440e5074135181500b00400f000e90342940b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565738732 1250 565737482 565737493
    0x90d050a0215071e050c03100608060f06060706020d18050a0506062d120a0b0412020a12030203060127141009030b090a060504030f030f0b30031803 65
    0x1442804102203601c0580d1000300c43c07101c04c40b240c0541024402214084805d4002d03411003144a803000c00c25800320302d4070760300045407040c0f41c541ca0318140320001d49811452045a0200300258564100b01c900305907000030300581c1c40d0b80c0d080c0018001c0c01039900f40991803d69403440003d00100103400510503004006840c4030380c0340e0b80100814490f0003021300064501c030f0080c20069041c40d65241c544c0c406c011b0810301600d60310001550070890761480496400e1080001d10051080726418800341200c0c81c0000d200c030b24000d8440224800340e00440e40c04142d000000a1640d0b48103980c0102026445800703c81d101c000c1c0c0030011000515402204031101c03480e0640001854604105554540940c68860081e400d42d110408018802820300c05980b00d8050741c0c000241c10351180501c600d0080c1d451101074004014000c094503a8061541062418454802d0107651251820b487e81144103038402458215500d4141f09086c0301c00a42c0c0300c074000070944c520381d12148080c02d000107130110b06459 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565739982 1250 565738732 565738759
    0x313030219060515090105100f03140a020a0809030a05070605130c080d020d1704030c03260103060e160611070f08010905070b030108060103061a041a0102010b0a12021302090d050a02 80
    0x14210b05c00344107240d40024400240c00d01e03a40a4983c213202c510080c6004905000c0e4283e102501640581f55030082c91b5000407a03201059000d100c4c10342140011024601e00b0b92500b000414500a41c0c1c1c0c09844260b645000c00c0700c1102c12011000c000741d0025100f000a5919840540c6030b507038461103c00580180d201d0755444602c984100341d10682021a029219201d545044074407140d03811b01102440302000b05c2c864500003071000340ca490160080304409c15811450720b441075921706918071803541e1007000d000c0c50355001804180d099422034902108001101003a0514100560740211800d980b0040c0205005906400c40c550a5000d542190783c6135a40707800030030343c91209114071102500010010700024030290002c511420003540782c450041d40420025048070002045d10300b101c104031040200302d50f02070048010440048511810b090714181441400e00b00700e40700244280458182120f9059840d030555428001c0504800c1c0c544004d898a5582c1c3c84011105a1080f00100040c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565741232 1250 565739982 565739989
    0x105090a02011409010908030d020702040c0c0b0a0b060f07030c0203070510080a02070305040e01120201080a0b0105090f0d0b01030b190c0e040b031213030c09110313030219060515 79
    0x38031981d41a940d03000d0f5003d01c40241c00e515003200e03141604000501030005a4408100050508403120020041c0e840220740f04010071546541580014881b9030a4030001055142d11480d50110311030801044082c2c818002403036502c9040400d43d04244042074500c18550b0000704030350628400c0d41190000c1d900c0310304011140c6007400c00d0000140c0200f00180d90b003040c130b4000d04181803003400c00906250300d030044001c01d0308098000c0503960f0b5041c00c00c0001d669000401c00d400500303c103420070406c140d00300004c04a102e410902800b0b4000c00355010201c0d00d80600e08900940c002d03c100d1401d584904e400740c14440141ca000501c000c40124200300795805206201a0500e652180601d032031036881480054224a01d150313500d4024003070513040032800c00d001009920500401160317024210300c1c08d81580341050300441c401c24a088001c0c50041c00344400c4907007044000741044083c845501e07040b441c00d40d00400c08401019200703001020496590412030043c000c5c007003103124461030758050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565742482 1250 565741232 565741243
    0x20409053409050402041403061803040b070f0b01080102030f160215092b0320070605060d120e090f040210050307020f2506140711040b03011409010509 67
    0x403140204008006510314107000300c0712810104a800e100c00d0550f83c07500014202e801030786c0404140c3c6200860050713603140034800c07e603001200903081c181d1005030440c4182e81c1e000b140184024546c00181050038840081840710b000c50380003106891940e110080c0138080c0d04181c409080040d071030001301c0d1404950303041440c0b441000341c2c000c01040700c407000040c2c181c0e600546255010702440510703901c900ca0b10000038000e04000895800640200d2000808844030042c010f283d13456000d0680070a031180030101d034010f40e004500814903449903400078001c141c0c0d900e001820b41000303c643e00131150f006031918a20407003c071070030040c40d41d503d840800b680404480096001011600f01070020740510040c50b0052114412154402283d00e002403401f0100c00c404c00340c400c9900309458401c1c10301d083c010040d00c100d00c1c3c64082400d02c0f8010760720038001c0742d400a190f0a89111810b100391219446480300417070081c000e108605201200810040c4280c071800309a50070400014508040004c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565743732 1250 565742482 565742521
    0x90c020d0503012114030304030306031202010e19030e090109091a0108061321080603010507110a03050a050d060e0a060f1d1f0308032e03020105070f08040902040905 73
    0x5407070039007840c2001c0030070203d4213500c0c00c80b608003100241d0a00094204095445144640c0300020f03140c1c198100380c00d4035200360130048110380c1061800e01020f80041230441001d140d160400c0c82c1d00e580d900d0142c8071240c00e15a150f420401e00000050802c4860300070003002ca0140080d001e1075200e00d54425070040303007400b5050f41a4050004180b415585e00b1220032a140603011003101110062000510003488100da200003a0f80001404814a0207115440d08070300d450800a20300c1c0b41c000582c680b11810810040e09019000c9404000c02d40500116145922010700402480e0f0312100807074030b150010784202d00810725041d070100d414181500f80c08140c07003241042c80311508844503050307402c80000f054540d0082c405006003601400c00c0140c84080c1d4801d01c00e0340d0302c0b86022030b105d26055961643c0450386c680c5101d284403142001c1001c0c0001e4940a00e41140d542031182407070320880c1c0c01d450000b00604000140001c4100b160790140058a040c80018040c1c0d4450980383c5a02402a44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565744982 1250 565743732 565743749
    0x51c0f20100507030c110405010605042d05010f0306150302190e0a0506090d02090c071a04021807022d0c0102070b0d052d18030a0801170a0c090c020d050301 69
    0x10480c04031740140390aa007441d22074100e00f80907110038804141903e00a80c0100045540800c040c02050142081500180500040d050358005040d4840b10a01e895120762418001c211103c0c0c00246e210f900b042000e090150881d0501c0595450000c2c000d60141d0380000c803241c807060b04410307203038400d100c00166820000c09807060310b0708000401c400b6a00c0031400356403006c543c5c405400140c030703481d10740c5100303841c4c082c030041c0c9841c15030811160681c02d021665a0190000080000607034030b0010740c03039007e685480525101c1d582c0c418203900e0a4000d0807040e01c084c00140031913980c0311001e2203292100c41d1900c1611505000d43c0016641c40360780d40a4803a44160a2100961840300c07580001e80c89410005402803072000c41d0000303581c801100c0003010408001400b08000d0b1030040380b030030502c0b007100c0001310b14001d000480200807440602a004a44860b00510403a0360420000c07001039541000407160202c0d56030144030020100c100c6084050700829248002d41c50058060324101c0d031240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565746232 1250 565744982 565744987
    0x7060e1527030f1b0d06050c03010611070b03070c03111b0109080304140d03020727181113110f03010f090c02150a090f240b0a051c0f201005 62
    0x585444c0c18a4101000ca83c2c0c1103226014084086000340c000c00d0701a40f601c150080c0e4a504050000b005070602078401212030340b25030000c201e0070120104880c0e00107541e2410052002143c9002c80c0c0307025844421910500c101e80c201007030308010100d08800c40b2000d0300c800b981d0a503102c034031984030b025602c100c02140403820b801006600b0250314105d07249120344181c0c3c1d0b4040c2c45a14801c1070040b0559007400310026801c030f0150103d150b118541800c1406051041e41250aa540000008200c104603016103100c1d804207207034400790f030840324261a0381000107460701c078003170242c0400390824895101c074400b81001c00142003501d07204980701c069299010b0201c50f400408a444d803840083e14108070550b9880c0044c01040c2085c410036101441200451480003c014500158140d10b03c0343c0ea00007460003201c0c1e48540c1d070344151182161010307241307079040800266080c14180c04006024154440c0d100300f06040040004180d605d03030fa251102d109429007080140051996000046404140708 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565747482 1250 565746232 565746253
    0x17122707081908071a04170f04061d120c0a0905090a2003030406090303030b030606091603091b0609060807050a0e060d0914011a0307060e1527030f 65
    0x40740b615410390f0190500300d1516155030340b52000e002c18508010258000b00d42844200f00751512456001d0301c80f5210755003419180e1007a5039861207a4410b00e824485c90002c914500280440c60f0400004020030101c440d080e260501612401d10b0540d50780328802540c40448c0c106460301c2241c0c00b03400650000d003d2010786641d11414030301c03035144540400341e640c1c8015241e41e400f003000380003070b08283d502d55100f20701d54a4042c041c1c03079604d0301c441d1080d001003040029944818519503401202c152040d20790051019040d0010500b10201800c0c1120840e000211400c1c01c1304d146084401942d282000b0300d40d80c030401c481d20b150984920700041c4040103612a5288640f0040b802e81c40003c060500e081030440c4080e084030b1075080102c500b04200489801064002e101e0403001c100041562a5130070000070004e500c0f02840e02070802488006540d40c81c0640b07442c540800317241120742c096a40c1e07884401413515406103588001d02c0144001d03500c0c140c20706000c2541464050304c0e10003007403094035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565748732 1250 565747482 565747513
    0x201021309060b07061e050103030e0406090b2808060c211b130803031e011403120f04031a19020708090907050c070617070207060503041712270708 65
    0x2070390359016406d090003900200c00f8580f03920603180258840d0311510300c440300c1c82d000d02060724001d03440742034038502d0420107410f6500d8420035620010124480303000c7d055034a0a17003480c04103594010002910400082001c0414240e004020b100b1038821100f00001c404110184001c2c000c95551711640000e042c41c4042e0250100a403031141d031070700100d17111350b03440b1191103145401c02c403403d0f01a01b0074003850401e808201c080c00c5025201c0701000d1000d150210700400d41d6540b820220702c0c032990b0b0003d41c0940c006a10320a41e070103154400751492201c03003040701d000300b030361019070701010082c2819070800050202d42c8201c4802560218195090420020400004401c018132a1045c8802003010052445081c041000503103035513164603014140c54040c2d4040e162004004a00b0b5520000c01408403e402c40240e03944280d00103040d528907200059184150700400440388964950303d010b004c80d0b40b01c200d0824400c0902d801481c0000c0c200500c41541c0d070585445514015008140155111328 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565749982 1250 565748732 565748741
    0x905040203030d0f0c110f1207210507110405010302090c0306040906021902010e0303010e0c1318060504050a060f09021602061207110d02060109180c060201021309060b0706 76
    0x80c0010103a0b0300701a0582021810789550843d501e4440f82e450b00f021141c29002200d0f42940107141000300b81b401901d08002d43e40b0040071040000420012aa440030015000c807101007c8100d0f400403083c0251400001d482a080000200c03181101c10302e08010f030b400d06114050480750010103440c803d490b6518000707400d80c000340201d40c10944504040c000b283d142d000620a1808101c401800e600c8410002802c4844110b401c00c950742080004100044543e5003030303500007251924041d0340d00e00c0070300c0c21a010b1034141d001840400451034104e4040e44c1c01d50040d01114415181405075640e0840762004813036690188201c2e0401240042c00941c40d654090840c0d0318410003544001d828640020b0002c2d044415040c000342e90711020010001d07407007442007071910700c1c22005204090401c03001039110300c414050100e0750340e0348840000560f00c07003607130f400c4500e038000000d08141910340b04004c0c085e60210200c0c9024040074400011b044403944030304000c40b21540c10300e50420220303548810140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565751232 1250 565749982 565749991
    0x1080c0c01090f2001090503280b24030109030c12020106051201050103020109060203280e0409030306050f0f0315100312081603050702150406020c10240308040905 72
    0x66503035082c244002483c07500031041c141d02a68520005100500d04601d4107031400c45100d041100c0c13080104038035180042c110442c086d000b0003180784004c8000c45001411000d00014044042407414016050003020340042c448034920103058112100300185820b0f100d11440c000d001548605041021802860002d2300382c41e000c5c400481c02c10703980d0000969102c030764010072203036942da44010030031076030011040002440345002650500c02442c00d0078241e0110b0500121080b0304002580c0c000c2c030b100340e01e9440c01180090007040112794500f00280100514001c3c2c5009500114061982d4600008091010007005004060502a0420501c00c00b80054010903c0000c10708000c00080da00807200c0341860813550b03481d10103181081b0640c40222003009440189440e2105128030950b001c0342c480c11040c043c2000c43c03c44c0c0c40c0c41c9000c1009100d078002034900d0f03000e0400030440e030650b5034014030f004003142034108840607045015480d03601c165210040a4807030800080110301c00c0783c0c010940c0b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565752482 1250 565751232 565751257
    0x1140a030c110a03020102120a06050913020a170307061d1e0708071e0b070206251509020102061807050904060b0603010306020a031a01080a090501200307140901080c 73
    0xb604800100146040c810480440c0580d4000c500d2440e20b201c1500d5460b0300c2400d2103402d02049203448085108104094003218800000c0c405076425525044440c400510000c20580d200d0a050100a9100d801021040300c146042c00740000081c0101251401c080b81a08080c120010010111284d101150601c0c0107190007a500c0000d01160248101c1008103038080103602404000030f03114042c1c0040b40c21503c08003000b40700c2c840158480d80191030403849412640000380100884070300d040302080ca0001d00c107030007002c0648007a210036042680014404e80880c2c2103078036510541c58907422114910304480d442004100060b00d0140100d540003405508001841c090200210324141d10980058a1294001034a821881d03030510400400b4141000b0012110100f100000d044d07160190581925035180c48406051003400e60204a1442c4050165180c8406d03100e4440b81c81d400c00c0350f50f40003003003c84031600c0c041f00e10b81c1c04481c26050b0507590038a031a0307039001d8051007503080001c9540a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565753732 1250 565752482 565752497
    0x50c03010b0906040b030a02100c0c12030c060902030114090c1503060f09040201050705030d0204050901090b0919020d0204090b040b0303040e04080a050706151406070b042006030703050f0601140a030c 88
    0x9a210050042e8580301c503641c0d50b1400c01c50030309100032f10907603981c4550401040090b0400100380e10284808034198000380c042050039107800060b001d890300d0a80c0f080751b4a20f01c402d008050800082c000c034411010b8440039540101c20345480000d0100301d030300c00d8100030500e01100680c0303031074080700c3e07841881410b08030304008039034680916642200700031030003040c1d0019060040c1c1c40c2501001e40100381001c02441310f180007501192201c00003802c031003134014181298101d00c070100c1c0c040c1c4106c8028102e0854566a88511150140c0700c032501c050f02071854400011200d040100898090315006c6580c80800e444560700c2c500f0075031102a000c000c0042c140301032000a41c51380561918851859000b50035603081031808130203000a0004144560001c1155800091680704550b0740075411040300401e8110f00d00b071815008952803120340d800103000041214050701507018030b002e442c440d070b280e4203155540801034a1500a11f0300302100c3e03185c14003074102485e219400c4400070002500d4000c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565754982 1250 565753732 565753753
    0xc030b04150e0a020c030f0a2a060e10110d11030108120c03120f0f06100e090606190c03081f030b060d0b01080709051b070f0c080604030c050c03010b0906040b03 71
    0x141941c010303070b8445400d20f200250b03000c102c9074007900800050604003009c072610218030704000c01c02c000d408402003c260f2100c00360399080b0300a01401400e81c2c002070060210098031031441515500401442d40458a000044d41082080d01d00782c034141c1b04510010404584584400e56140e0081714040d60b092008204012a071804082d2260007804100c3d0344000b00c1c10300d034503503021280000342800e01a0640d4601910310940c002c1218180d03020907500140240c48080200740c03d40300d20103d44042441e1090304501040c0c0c401010b05000c1c1c06552303030200c0c1d601c030021601c08182da03580540070320202c0c015003070001c20001c2e82c071150000380081011180303032250390b1a02003000e001d0388210613582140030200120000d038001c2d10340c00383d05488080c0c070b002e6031082e0100c018003030032801900c0c4500e1441e13080c04000c802022480502428001c8840a1400c0e240082102e030840e4011940d40c0030b4000400a40d0405002c0c14441d028000e049103066900d080501000b4449580f42d998181301e003030700c8603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565756232 1250 565754982 565755007
    0x19180c0f08010f0b030a080f130b0c010e16140109030b04050303190b0a18020d09080c0c01030608060c0705030c10150905040b0105240301080102030403030c0c0503091302090909010c030b04150e0a02 87
    0x80000d01c6480e4003039445500c4100140d0843780d01701d4440f00d0541010a0a00c1100320265000007540c2140030f0901d0600d001c040101c80340041078000a007004e03004c10500080c04800006140b003010b10301c0704c543d6109490115441503035814240b154109151400c14030070000b9854420b00b2101d508100103040c04140c8044005540c1a442e09980000000400c4030010700c0034440c0c500c900c003084c02c082c00002d1525a840d661590001e020380d00460012484208000051003190320b402c419a00711000d42840b40041402004660340c1c000c0380d0351050100043d55242d50249070300c22900100c20040c241e180000f4030840b039284003003204000401d040110124040311011318060130b400800143c5a1520389005000c03923000c3c10380e5105114902c285a00007070800001c4401c403401c145d502000c0b403005510144083e00607545110b5000200074200803402805610412a0340780540d014000c030701180c41400120f551007400240d241c0c0350030109002c0d1201c0d00c2c0d019904100d4144d001480c0040c200c185 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565757482 1250 565756232 565756267
    0x207050d0c051015030f02011b060b03060112051504020301020c1005101706042406080a031806090b090310021309050603030319180c0f08010f0b030a080f 68
    0xc034041181d07030000e0810b00208100b0002101000ba000704529550504c0410018405200007040f081c0084603100869220781a514040d940448507071200c44007605c0d090020301512a81c150003803240c0000000c0d02c45d05c0ca02c0c446203076900b010191503131090391250011000d0b030040c4180d030103640812005880300c41c10006400e541d44071803000295420908038951810545500001589004d82c40031410920045042c17504541c0c0f12034459480d9100e048184128071000401815051410500240f010300118080803203522951303e088a00f83d660002a845503124020701000030b125440502c50241440001c0441040040807101d001c85800105416a8081c00c44c0c1d100d441c1c03001a08100c0c18032640500358112408501940c1149060b0900050102d030f00ca802803011611004078170360381411744844200c0c3c070b90001c1011144a84540f103600c64501e00b8810315410350b2a021080035064454810098000401030203803035040d90030f48541d06d26030003c40c2c445000850070442c0c3c00c034034000e6822 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565758732 1250 565757482 565757503
    0x40b1503090d02071502030f0d0b030106030c0914071e050d06080109021836070b0c0706020a08042c42040c03110d020711010918020904020705 63
    0x91103551540b50000742080c0041c0c0c040480c07200402c403078480c455004010f030340c182504018801e4560102a540401034036042d15501d03055440c4c2113002c02401a00c3e00c8441c2920841c54051140c84640c008100100c80101e400c5d40010b0200d4014003644141460040e00c840c000d854018104042d0f00084421030310307103134000021a9940c4074003c0441c06c10740a00e800805d2012011019484d01402115100040c061625126081000c50303000e0000711000e500d4002c071044086034503098407860130392000e40c01012102d80d14400c0010008003644002500407440b43d220300510f040c075240c0400c0000c00c030310382d41000001603000030b100003942c5a4003d030240301d062242c410742d0402a80c0001e08040803015945015107801205840202b000342c1340c85542d01040035200060720004840080b0b00820050401a80810703001401d0901c1003015006070000501810541c000a0321a03001910082d00034880c0f00b102da4962402000c084600764081c0c0215040030b0030140c900f1495036182030521490b050f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565759982 1250 565758732 565758751
    0x507061a0f3a02090a0c020d08040305030703020d0204030b04060507140f04090b060c0f0a020108010905150f03010b0d030306051302090306040807170307052a190218091c0815040b1503 81
    0x151b071145483d030410442e0702d4040d05040c50300050509490042c614400104100b0500d50002842403010500d41c0c115001140c1161505085042518010003d00402d4031000c00040ba603800b101420180c0c0345c121001000c40306a00b502c0c140c5028601c1d00a00340050310079612900034003400700344210030300580d0510080607010780003d90f410301c005041603006070010b250083c6040100840e600803a0800400403a0407111a40d030301203980006805410740034412600110702c07403110400c064058001e02c0903243d0440d001448102d110145404030f005880e17420b80c1c150320034800724011401c041d00503c1ca05002d00c1a02800300100c00c03041034554000d844d40d5002680001d10615510f070a5509081315018030304c3e032034014002d4000f440341e503220301c814031040da01c65407043da00440d9212080d40c4c031030402d155500d02c6c5034585165100e0321400c8205980d14907520302e0070f4085a882c0700380a403510075000c420025900441e444141300003400178012054104d40c0d8503496165002c04403025500c074800c0748 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565761232 1250 565759982 565759991
    0x10090602010e0312011214100c020f01090305030c18060f07060e0a0c0605180306070f0f1701090c030e0609010203010f0e060a0e070507061a0f3a02090a 67
    0x940080c21a46542c5140000e0b4000340a20744020400c00801d42c11039901e044101c203480341d5400c19a0f44007100c2c0d0b550303840a208401e120b8a2035030203600003040781a401e40a44000b281030b62038041c02c0e07800c0a140100000c100300001514410804040c000c0c940b2203940518406140340085030055110f0500c408004001103030020810150323000308400140e107100a4030400c086a03880d42c19220b190b0144c1d40c10f00002054a44a1480341070840e6046040241196840e0a00c02d01c041e010002214500000896019003060580e008080168100d0400c1e01032410326860440924002d0a8045440d401c261b220600340d0748109040001034000c0e40d40200050b520b51414100e504501007503031110b2046410030040150a940c1c103060841142c0c041300203944541d5491508075000c1c0b00f2010020826498090342e50000407070314104502c0000156000c1a982c2491420001c18000044104005813200b80c2c01758a1007134034080842d030501e5040c107a036502720000e500144019a0803141d040c1b10300c0c0d4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565762482 1250 565761232 565761239
    0x60e0606090a020a0210110706060e070221040b0f040b28090e0f0402030a020d0803041b0b0904411e1302030a060912020606040e03271009 61
    0x70114050300520049000c501d02990040c001c0e44682c0300da034590040559804940607a174440e4821a110150300000c1080361035117030080c140c1d03980703010307100c1390014401d200c03074511030b80c40501e602c0215010402203281404d20b004001d9125a0246c605c2c510103100900000038000c1c0618041c1c685c0e8003010404050343c1040c4000208001901480b144c20007491031420001c070401c0c00111074101d04072a80408840d5500d0010074580840490b0003034011114010f41d00601122002541c050791043d070758040b0007120140300c10b80135a407030f0161150307081c4100701e86d035110302d0982d110740c04c1c00700100d070002c800c032a2075400c003840401c201c1180c4007000001c0300c038002c021814920b0241e201e248204034054400c04220303036a19100001f0702d8001401740d9440c01100b17540d41084246001070f4800000d2000244900d480460080c11000210243c8281000b142207841d060181e01415500040118100159402090400401c030702d0a4400803c4800640781d142c0c640e000060103001035901c903050803902c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565763732 1250 565762482 565762489
    0x4110a1d04020315130b090a0f1406090610170c040e030d05100e041e050a0f120903081c0e030a02070807061b03030902011209030e01020d05070507050d050a060e0606 73
    0x7413164103074042c0c00300c082040310b440888852056101c0d00612540e40740d03921840154940b00b00d01d5409041c00c440722880b10308016401c00e2000042c1f0145051752a10b8071080b2905a40d500141c03908107040303000c5481402144260362085600303c00d80342c00c489800b412134020071308a41c07017007007044403d0b04000381240014100c0c0c05400d030020440a000c000081c0303880b08042d1440d0700500000d0421440030150b00b400601051044c518035081401d45480500c1480c0540c5002c05aa40403160007030703044101d0012901070f800190849400440e03451411120701e2100c456804200760300345503203a0b10804004080010000f9126600c4071b40c000340200307418800e00a12705400d5600078002c101c0c01500150101c4448280d01210640c1800c0201b014803051005846131110071514a054515080c40c20041c59481014400940c1d002e030241d4610440003c001c64052258100203011580240810452403e00000c8100b2541c040e4040c0c9501007466500c0c0d109503114040012015400b917401c2c001d4030b10317 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565764982 1250 565763732 565763743
    0x50307060e030604030f0212130914070206040602090a2403050c0c0c0906040605131e0c0519050c060901020415050406120504060b1c05060c0301050904110a1d040203 73
    0x40c203420702000c030444560009a803624001d03c01410050701c4545034421a000700f10110264174802c100b82c5d00c0310030001040701150740394400c0b0441903091650310044414508404c0e805100542d02030700d41e036030701c94490710003941c8600c0310981c009101400005501070401070143c0c001c03110061011b402d0005031001401c0d03850140011340d01580400080c900701500041e070440c07190055a088030166568000a80107084691060f50480c0c95204035162580e001d9000407108011040350118824500c90804111001c1703200c07a2004c10010003214602a040c01628003649065242840c64483c40003141424407000b030310f000345107a402142c00d00c0351170015140010300b140c461400c42e0909213403280050011000c0701c0d105000e141e0715004641405420b402004540c1c00c090a245141088504104a0000f400c1000d031190302039600821403c45002007140d040760001170034101d080e2034a4460b100d89040c90400d5075440181c0307400001e02c9121041040100200c0380c0f10010b00c03850240180350614 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565766232 1250 565764982 565764989
    0x113607080106091205010f05070215010f0f140f060a020303010f0b0a0906120920150909072a2001170a0b03030904060b030106090902030103030206061302070b0709050307 75
    0xc80014401260303c002d484048903a0080311804840160504034014180c200407840b040382030404102d0f07041e030002824549200a5075007186527a03a43c800b0140000310368041e005403400c103038404000c0404089565207082c0e10013070812500d594042c00190700da48c444609500503801c088010046c0010b1005040001d01025a92919081b0100744c01002d100c079074020307803040c0300d51100051020340741d680c08036140030b501100550a11741440303d41e002c25a0480b16186c0725028215030a0424000e03881911607181d00a4a40c00c2c084d1900081a01c00d00c16079400c0f1100710102c07559150b07403c400d03103000d1984240603002c444648010f01c8071035a55900300c10840390521810030811403240d4002907120b60f10006040c0e000884603050b80000e810361040d4010140d1140c01c1072004200070361000010740c1250b0007034a5000d04541c0d5000c035001a0b0209200190243e000140081c0c1d0343e05080a040e48501c06158006242032506e03170f9004454003043c0c9843d800070303500c070009102d58101000b540014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565767482 1250 565766232 565766237
    0x30d0c03091e08030a09060b03070b0310090216060c020a3201020903101109090a06050118030b060123031e09012c010905030d0e1b010507113607 64
    0x40300c81d83c81c0d030b07045440040c00d100d01d4195034540071800e2000c240c0c4600303828003005040d1444581d0740d2620441c5500150398040301d00110140000e00415980700b00c0c5c01101d40c440f44600303030006035280c0d80014034000c0b0800080d0300403648102c0c0000d5600c80ba8032800018504801c00d280520005103294031008070f5004017982c03040201c00425900080c0d038030b048044c0310074086140d0360a00c0e4055514004e40c03045e1604851401d080c00400015900144141d49003aa110311000340007640c0da2010f0031461001424003031250001c01c184d94480c0c02204840540742c0c1ca5281c14032a05100300c13690790310032504000c81e036928500403c04501100b51258110381103100034000407001010341d407200400c6035004105501101485c40d101c000a412040c00f1a80100a80c0e4652020106403005458600040b81140c0241c00c550510300e02c44030030700c3d2600b541c10b944007810b01075180c0d00d00207081a5801d0490b8804208046582c003000c02400d10f00d40070000c0c007615281d004143c00010510720011708802c09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565768732 1250 565767482 565767533
    0x7050f1c14070201081501021c0903060e03032a04050a0308070c0b09031207060b0621010602151f05030d0309110303090f06030406020927150a0b0c030d0c0309 70
    0x5030303902103032140d04000c00d2100c0406e20641d9500503482c0410b51002078941c5031030203082112075500410900101c034015035050207000940c41c8103d880b8802200c25016499040c1d200309142041c1302d49050203085c802c1070003031920f52107000044110505d50300481d2035403070004002d02040001170071400103010205401c0c0c142031201f03001a440c1d050f00b2031220b40d44040400c01405200517904886203601c00a003084d0b41c0c1c0c1209840024500b500202960000c1380d0b20000001c0d814400200071b4181011000c41604030345442640e05004186603501c0c0d80c0e141c80840c0003040c250f0f01400083d15440641e02c0c0090314120302d1405415100c0b05a0500d44250400e101105042d29001c4a00d5006441124015a02e54551034688003e0050103995500521400501002001f00c1041144a80c0e0402030320002603413102c4a03041703510340c0f0840703150b00218210750070420425248090303c40542801c0032b0300d0a0805c4c500010003210060506000001e803202c03210707030038401401b00003141c1040d001d60552 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565769982 1250 565768732 565768747
    0x6150e04060c080c040501030c0e04140610020c09010e0711100b0406050612040615170a021e150a050d0e030d0c05030103050a02090604140a0b010801150c060207050f1c14 75
    0xc0c0e080c040d61180c0347c141030715405150920b5204e040c420441c0d010052040001a0810400b40100c0e2130842d10180103c100781c95802c805400000c030035110490041000700503030b0070200d0b158032a4502808003414001c01500daa0b5000205103c0000c0c20741d10f4150000d074881c013480800060764001e500c50341c003c6c1c0c0b0400203041040304000070542d100350811004030310701c048400c00f004e180440341e0095101c10481e00403101c01075000700d0701c8032046008541785525024602d584410300100445110307030080c4441c4070050440350303500181c90b070a06541017540c10004248a6a42554220a1403601c0344c0c10001e642c103400315080c807802e19040d1091800a041d981943c0da4a5620001c00700c0191060b189400040c5c11941c40380c0002d02c9520b40031600001c0d508000b102c50002d41a0419140d0108030140f00200e04680074400b1149811040d6441c4040c040d0b803504c6102c0203500a08065079107001c0d480c4040c803902810800d0075120500c02c21081c49444120704010100410f01c100a054000300f000b005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565771232 1250 565769982 565770001
    0x80412050a080a0c0e060726250201110706090e01150f11160b1c020c120d1b11010c05181306030c060903021906051606150e04060c08 59
    0x3650310010152000640700004d503019101c0003c140142ca501500010300d10081002c0c00c980115181078010748103242032042025405507014400c8490b580c2003440b0388c3c0d8860301c058500702c3c40d00c00d401030400c1d5452503100c9000d01c2c20500c41d5000640803a00c0645c041042c030704c4503682031340107102e80d880da40411150000020711a80340301101d00100041a0741314201c02d1018801c084100f801c2c3d5142079003065640c0e046002a4001c44944162100b501d880440c04035041d00842e4404500800038100c0da030108048074000c0c0d04034918541348075545441645d440303c900102d00f04103001ca42c440400542d50405000e0a403900c0d0101c1408000c803c1c850940c0b5842940c950305c0742500122a00003080b00d00028480050845500c00760049122000002e50035800403083c1099a00070f5451074108001c0502c1a4035403501403190b417001617000c02445417115090780050440c2031240382c01080e0080c52a1031540c03100a9a0044d41000b140d110620040003001d10402d040d40f41d0f1424050400e25100350074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565772482 1250 565771232 565771247
    0x211f080d0203031b040e01090e1e0705011b0501020d0b1309050c010e1f050a0e06030f0f3408070f0e04020309190602040806011a07170903010507080412050a 69
    0x442404940010113548508041070a035005803c01105e501707829a07440b503210024106c4509458514010b03066031113449190007480116603500900101003035842c00004540901d41007a9071803c0007201300a040000d40c00b8001046402256440411140442010044440d500f109048c00300c0b0b2528015000203400410a0007075141c0034242800d0420701d5101041d1031840c1c0071111907006130680c0c480d01741190450054070341da2300746a50718080040c0513821702c0450320041d50007600c4141070800181c0c1c60f43c8a40c004983c0003d0348200c805090781e108458040002e8680e008400c0c9400b401c0b0240031040d400302d0119440782040c54401c0703141c0117440019040c5500d07044014001d540000000e26004001c0000103070344040140c80c0281d00c40c00c0d042c000000c2d0070030f0051010340d0242c48000101c180c50b2058820502032110b2030145401440d696020810501c014244074511060100000950b02031051520800342034542d004507180500e00041802048a240c0c0d06000042c050180c1c0e46130300000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565773732 1250 565772482 565772491
    0x9080c01050306040f0c02061009020c071217130513060501050909061c05030903061501140706090f03030e0c0604062f0a0c0f0509060d08211f080d020303 68
    0x200941d4944800c0301260140a0034105e0016107030030280480c003265800504c40d80f1402025180c03120381d13510396080c1001d071305c035021182c48581d00070b0350240100c0c1825521100c2e43c61203003596a000d00e003003490b044000d810642000320b0a003c242000c200e1400c004648008038490000100059404c05001038600d0185070551402060004001511510f9840c81c85400c3c0c1c0c58514104a44109840c08a030780e940800c840360300070300500e00800d49000d01c07400d801e01e01e164140c594240444010310458403e80001c8000d80746c1c20380ba81c0a08001c18222030410031024001d65011520541110305903207040c019490180c05424100010491264444140804940200d000d85400b0700c40c900c40003440c00c506000c1c04000e00498888004100c0d0041d005004c540030840807440d01c41c0d644017085990030048503c103811011021928001400000007861041040c000c1c88484c82d078030803000c0d00d201004545440011100074044100505103516a100404100c030041050003010500203480e03000150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565774982 1250 565773732 565773737
    0x105041e0506041103010f05030c0307030b0f0901240503190c060c260309060f0103050307141009030306050418020a120f0b0a0606030606020d0906110102070c090e070609080c01 78
    0x40811480d0743c82e50880c045200342c0d5501c3e16280c0d6110302246840910b00e1213142d101b407080e060003002c90704001c900101103940019007145599203010213040701e002d00603c005202d55032400c00d1854004459048420745000d060091610ba04000a25180111851040c42c030012415140e0001030b90704144801510020f152000000b102807030440041040811002040039070b8134080c0c400543c10340b001d1403040d160b200c212106034a039452000f4800b40c00303020240494200700451000300c1ca103500082507416580c1d049805460040221a0440d81c2c4038030110300081e1103410401c1545442e0160001031040c0904a0881e0105540041c4400e85280301d200320808014040b83c0c00c1c0710802044010164000745041c081d450485403c1000f800c042c003c01000ca481c01c2000301d0000d10014500d0700030710070f036240c2c0713449076040a000380d603051040c451081c200c0d03400f00280780009442022410040c4000c20000c501e11111188503030402c1c6158100700108400e2807070401188070002074480321141d00f0b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565776232 1250 565774982 565774991
    0xc0a0b031b0d090602070b04030324050103090309090e0d180501120b1f030905061003110f03011806020d0b0f0a0e1b07050a171306080903070c0b0c060105041e 70
    0x14000010300285240130308024070201c2c0107070074410044084c51040d8400d0b6000c000b1941c40316029151940c911205054490700c4100c18800c2d0750080d400b01440724060705251905035030b1103074074a0942c0d49400f46103030340f900088c1950782c0843d005040c00616100b07034610303130b2122420100000c140c891901c074840b5040d41c56041d810f142d03454800c5854801411602102c42040827440b000d0040c001c0410101e44034890070300002c8800c071880541c501560307480705c401000111100200704201804000d5240d01d9540c40c0c8901064101c01400d00312000c0c8500e1015880360702003812401101c20b03881200740075200090900c00c1a80c0c803405010180d03a480c1503406903d44074600c100d08541c64142403a01000c1000276243d061000000300c01020501c00d540042e004c0b0703d0b0301d02412580c041c0ca00702082800c1c1c007400c14010789014002d4154003445000441e400c0208549901c800f41401d684003a034a0800004d00d5042c826082c403500707000d0502541c05000d40e60310000c0340c0c003c850070145812151541c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565777482 1250 565776232 565776247
    0x60c031207110a020f060c01020a05180306010501080406201c050a0e0a03050f0903060c0c010c032a020a0501050403050a020f0708030f1b0a03090609120b0601080712020a020c0a0b031b 81
    0x45205503041b8130501c0e03008642b100c81800380600030b03a00502c1d00c80180143c1180b603d8180c9400a129416214181e542e00c100d5207566980d0b8000d8403444040004081c0c0b41800d000d01c00c458440905217040032583c85648c4902c04140c1c03c0121200944888400c41c107045070b4010080000038100c000e15803500e01b04d41e03140302cac1b000302181c1400f0300381506038140511000d011b0751118403c050a00460359400030007415101c1c139070907011542030342050b100301140356109101030034800001f203d1f00e4550380180d8403a080c55680e154219401102c04402146001c50240c25160f8100f086801c2c0d919a000100511401c01032130702e81d01d00503082100f5810100250450308440104400e00c8000701c004211004e0629500c0c02038198422402600001001d448000901a2004e0708000650790000101030103512a80c00464504c400104410140009540800d4484202e44020300303080400340d0140c140001300d0f03402c0001010300c80e0f000390850301c001d10602c80c80f600c3c80000d00c0301c10003401509503540e010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565778732 1250 565777482 565777489
    0x4080306130501061716090302010f110102030406060e06120a15140a09140a08040909020d0c0905070e010807050306120c0307030803011701020a080f06040902060c031207110a020f 79
    0xe0701204424514180400081c5090300a4026611060006001c4005948444080c400540f42c142400c000501c0c098081000d035000e186060010303070030307480e1940f1202c018007842402ea83c000e540c06c40e01e41c3e594900070401c2a004450107608540c044620140309601161450f6480c840700001405000c1804145210315816501809001505a1421403140380a40c0e0b4240145154281038800a04c801c008800c0c190f004240140d40d03503444100d150510f800e0844210003000c0401c0300300e81040c0c00c50a0f038000309900300621001014440e0300411140b800304401484c2d61800915039040c07060101c1800380203900102a02c0d4070143c00d803000c00205101c11300a6213000440c000380713501400b42e01008014000710a0045050761900ca65a035048130940a44500300d2140802d44800240070070302144242d07500c0800242c0083c001403010982a2061300010021781c42141994555400092828120100c013003407150710031001e0410801203d50301311419100d81003080028400c2250310315080a564 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565779982 1250 565778732 565778749
    0x101e05160f03080402040b090c070318050d0f03090608040b010b0c010609020c03070c0803030f0f0a09050114070305060a0503030a11011e0c080108070b121e0f15030109080304080306 80
    0x1d4100d04440070941d26802e0103000070384156003d070b000ba4106001e0700740e1400e00103210380c000c0541300f10081c644042514100c80d5000d88035452249440da241000a60b44d650003410b4076600c0c0500ca071200020b150b458064030a4109521400c140085a0200404a04044070150442c2c15030817000340c0d58441031200c540101441c0d000b44000c2440461a444c9000001021f401c03114443c01d420801640c50342c0c18503a1b41c4c002150103044103940440000c002000039078000e50066103083c1d020500d2203159590f1030030345100600071110b48103201c040220940d4127001d0b69420582c19552101c07828200301c0400c0d00d07441100440410701c5111011804842402d501060b0038481030b0000181e03071001048028040c04500342e0390000500d03064008225000c3c080340d4503080720350034207250345801c0c1480d0420b000e9000082690280000c007040c000000380302810500d22940000d5003002081c07402140e5241d9000040c125140660b1500030144009142c0c4402c0300d400030780100e560382d244e030380715000548180d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565781232 1250 565779982 565780027
    0x207060c150b0a0e1f0509060609030a0f030c0b07030e070b0f0403200a0e090705010c020f03010c030507110109050a080d0e07170105180c092a0405101e05 68
    0x150410364001381400c50102998014a0b00030311a903c0145120005e10841c1d090380921907122007188040f81301032034401c0c001c1074400b9010b01a01d610028584843c108000c0e42c0006a0101c5e1101a40310100820764140c03075407009190034200700001c07140040340d43c0d0304074074010207000c2c880c0092000196448407065034025980200c4940d211041402c81c500700b006600b2145c0e0052034044404540000c01c4450070380316004040041009070301c1c00004441182d08100b0598200d405100b4035441e980b001c0c0140b04903180709880100c1e5906001800a01420401d02c0303a030156403404203504002a00815074140c016002041030f0307100c0c250410040c0080c0328584080c4094401c95900203440500542c0180400a401000304115600c0194142c180101401c2c42e25807508446220f40c0c035480e2207442c1a0308000828048000524049900c0c02840421005000c0c84200402e0403c014a007041c0c6110a10b44545081c0c00d102d000c2e4640c5401c86901241000e003400f8001c25400d5844900d01c5058002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565782482 1250 565781232 565781239
    0xe0f0415021903140106030519050a02070f060b15040803040306021e0705070914060a03020409030c0c120203070506040b040501050a0201091208070813121b0c0b04150207060c150b 79
    0x591400107030082c803080c0707142144e4611180000035941e0191080511030304181034081401100c0f507022100500f001041210341c65420321800000c5005003d01000c2c071440348200003424a2403408001d42e640300000760f01b030000e0003004280150034010042e20b084943c032250150b110340320140c6207601381001f050003010310100461007a05001c800603500e801ca4800102c10080d4441c1e00500080f0380f0011601c56400941d01c4201300010700b020360041d00da4602902c0c1144030005541d845280501641c1d121f0001682e04400040030344c0f40900820713004290882d00d10340b40620b44030400780680141e02c01c0d0341c1130003008200341823118003e410a88805e680000360541420758004040c00f9480c0690742800080c008030009100e6000c06040c180601c0d41040280070a03070070b80b003000c44a0302e106400900307041d600b581500001818403405036024212107000c0303944684c1401000c03d1a541c041141c98115400701c40d0801c01181c01c40e4448403031607048091740110020840c5000b0203000030141c25a00f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565783732 1250 565782482 565782517
    0x11011802060f0a0c12030204032a1208090d05070501020d020f06041103120f04260c04020a0e13020c01050907120b181005090d0903050309120106150c020103060e0f041502 75
    0x545ea816801441035a206500280c5034041220400e600b070300d00c6400c040d54030280c00c07c080c091000d100d00411340082c4a00c1240d0302c1e051203480410485890308104468542c081441801151b1301842140c01d0040b0034402080e003000d5801d0b546640c1c250250024040d4a00317500400c0d469141806440350382c0b0b4036044603031703690440d1200c015480d902900c9075102014013504c0c03502844501c0300c5681d148203250401000c1c0d0340b80b507d007040020741c4031604240502c4244034a0300e00d03d48a007039904921401e01d10340180c41d41d0b400002182900e100074109449500b04007001e001c02e142c1042c16240554008000f602150b4400100d0402036001984c0c20700603100b158050030080c9150b170496407041c03032404141c0710912400601964461642d0000810542042c071290003142000c441c21000c445000001107507650751401c03100c0040314014003140015a0140e000c4c070642d40c06010f101c006142c0101c07814018039020f5110501d011000c1c0c401030180301d00e40134800c140d60f0340d0340568460003103407109c10a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565784982 1250 565783732 565783763
    0x70201090e040b220305030a1119020703051e060a0237020c0123030c0405060715060e0f0a15030203070f050909010e060105010c05010e01090311011802060f0a0c 71
    0x2003c0c1d40c0456491005a220b403038664003a5124202000710591315460315415500d032000f213100680070800b64010080820300582e02840c5980400045e0940503801400203d802c41c106a410f0018008698810445045441010660008185920a010300c40050b11011081c001c820401a034540c84008040803480715458602014103901c0c0c820000d408a8881080c1a4015070b04c80c45520500c41c290114540000030002a080085a0090181c0c610074501500d9400182c201c2d000b260f41500d85841524080d060f001072842040302614108403c4e003041e203070265a10713592040091080c41402d850301100c049600103076110401855008055030711682d11034600400d14865072060380e120f01494404a03013100c0e01032182c0350f4007010b04005445241e08200054807207a080407821503a541d80c4000e0007005071401e1048180b040d201c1d503070f141819140441ca141c2034a6181f4000c0c0c4007440c0070800000141c0d9024211400365080800f481e844050901003524146031050010303004804101d45107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565786232 1250 565784982 565784993
    0x306160f0c150b0f01030509071202030309030a0303051b0c281203050603011d0a1b090e1b09130201081e010305060708130f02061309020a171f0308070201090e04 71
    0x50120902913407036641c84070000c0011400d5580c1aa200711858020020500040c155110030301c001a0018080b41c2ca07087c07070309001c01d1400d0491038044e00043d546200340200308000802c1c421480d60820286410422080300d490303107551a1180c00400e8600c150425000c0d0413584811040581d008000314044001840d80540904002c0704d0b03e61195103001c0c1c0140d44850032061010310645518014110300340f5540c4e91001141800c1d00010085611003070000f0324240358007412290340010000b602180708200181c0ca40c1c0c018066019200310007074010020305041e002240700781c8940900e04452a511010f40000f00b170400b4960003804666840008024441c0010394180260000d59030307503020395941f400080c000300f0559402000314a082400340c02610700b9030042d04088054600104203036541d51650f608a9004041010100c2e050020840e215444c3d40440350f403001d900d00c000180c5402812082d0401405800000c00c000d00102c4e80e40150392050185a01900b01c00074041341e90304040c20135 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565787482 1250 565786232 565786241
    0xc1614010e010f02070b01090506190920030106020312070e0d030e09010504060e0a020a1709100c08070507020402180402130e0c040b070f11090a020d0b0306160f0c15 73
    0x41d281c0c150700f800c0d440480610b8904c01c03180d03403503002075401169900701b013480000f6010141c11640d006c0d200d41410070b030751000410500014544a4800541c2c461002407100b02064000b0400380401001c2c0f00400000b03070007104075001c0f41080380c026503581d0f6510000390303140701c804107003503801c000383d5080c0104044c5c0208594800840441d002001d50f07070b8030000c08c001d40d07500b0300441c83c840017540d010a0b100c5000b81c000c0c28000c28182070401c0c103600c3d6003039600c48941b0704883c01a0a5402416250503500591280d101c3d880d142e0315104010b0b10b408580500309210ba018001e020320350000740d0b56040d08903060854400c42d8010000d56990405a5150248681500808441c0d89041d0049814040c03c13101300c8084031010359083d0b0070b20303910fa115181e040d030118000356510000782d040d80070f8550321510040d1043c100c0705030068403400b0003905c280c100d40c03030700c91214080c0d4010001d1201480200700e0300d048100140c0391000d92260000401c030341050044000500c841080e840100d54820035410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565788732 1250 565787482 565787501
    0x12090f06030b030606031603020d15111b0c0108010b13170303011e080d080a0213090510091a21071d0601051e1e0f03010501080f040b0c161401 63
    0x1110351342d0302c52604043d20340308400712440425041c51001c100504081c655405841c2c06403c821200c200c4410703040041c0c4901f0040a000130400150695209078021036040074010700b24002c0001d0507010340040d14052060045404030031011405405400742210300c44040c22240c0d800c146801da20651482e85ca070400e000e110201640c1c1e541031003505002d001005c1c21141d622009140e082c5075204140c589401c080c00000d001d0b50200042c0d0051030080e81003070010f100c0520002160301c2c028503d600b00c400650400c0481900700f003407550360b00c58160484807610000702c03815201d01c515080c01ea0003500c1c11032200d80443c001c80d0f000250a540c849866000710401c60075450301c903907400c401181c03544a012400b0300201b00c507032403104191030b5150240040e400890541c0c0891031140d601072145401040340b42a10f900e00000602035941e2040c074068000407501b640500f14103103903490b040b628070010820400c0101c0031075140c480c0100100c40307100e0300d174010600c80488185185281e006c0c04c600030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565789982 1250 565788732 565788739
    0x70f0c05010c05030412020d080c100f0c0c060f0e0609060108060a0b0102060a0e0102041a07022b06050619150906020309030d080a0f1503030e0301050408030412090f06030b 76
    0x90018055000b40000300e40e943e40000554034181c1040030b501c401b980452021383c0c00000d56611900001d042c20010f180d1004844000c0c88180103c030484015203400c464113500322424120220011500030000085443e8011004961b00720380001d41c0c001404440c003020450310841c014000040e0020070254103079a5401d007030360b481d60b403103002a034203403480c6039445401a07006200003030599442e039110b0f0007810101c3c4005890a030f540d0a4201110000716240140f90700000340c0c10085141c00480900600d00070b004000c1d0324003003005900d0b1402c60320f01c0301a02154070340300003074a2a99150f11480d080d1403600c0c095603107640c50780641003030220386a1100340070403800d5501082c598000002c0d290700c030300c00400401d102d8980c000c1c00c03943c0820182510a4481e243c121001c82045039000b500ca41102044c1c482c01054a50b0a000305102032a0141d140aa490310081c0404a4880030441b540550400102031224901003002c40743c0745d80c958005a0809055080800c00035415004200316081c00c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565791232 1250 565789982 565790003
    0xe03031009140f06010c0516060e010314041a1003050601060c020324060d1a011401020d0309170c0a020d050318010e0a060e12030a03270f150e03070f 66
    0xa0009142000d003503c201d0300b00c0ca800707070014505601c41c2d01303c018143e01c600e0648040c640c1d0343c0b0380305218499030307040400070462804600426503498030918082c501034521980e09414280c4581c2096040100d062010400c0e000000303d52501e513026a4004540c0642140d40541e0744180c010321080e82c04030200d100380941d0044810b820400302030000d1400030344080c0e900980b00c003030821650220070301040f103071240c11014104182c4040d144050007412041e985898000803800020704011044c0c080300207041c034110300348020800f19100d500c8201d0a01401ca030f0f543c042e240005103400c050320310084d8001e00120070b4504005010029009140c03030105d1384400a0520001501e14100201019400504007a82049842d00c105000c02480001a140344454140201c00300e0950340900030071070100c1d840c0c9101c030552403040304007000039007041070b206046400c40d0350742c100e00c0070030b403910240200c4841803441030103800c5503000b81800c02d140d0040720f503166000d2400c140704500340342058501c5100c8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565792482 1250 565791232 565791251
    0x9060504091713080a0b062701090209062506230f1302090901272301110408060919020a090908090904080d0b100912060e03031009 58
    0x280928424154444850b030303034a5003800807121607030300b010444500c0401e19050002d00000c007401140080b074010f110142c500c2c0f410005001c1c86078080c80079845040d1340310302c0c4191002c9140303045c141034428055000d41d0714201c1c100000d0490140120115407203c5e296400b03590301040d40c2c64403450b24402e40e41030010400341d0f040b024003184c559902d401d42400410005210f80c0724001195440912404800d6040c2950780120701c5943c02150518800d03035403a4502c00701c035003002101c0031200501800c4030020f4081555142a201164441c090b21051484071040c1d107903200307400100c00c00c0560700b00a40c6030303540d07400090b41d01c0d82d05441008260080c03607603001850004805c4001869005002901c42c10b14200d04d0800a240d00b400503a4a54814010030351965a41101c0a02590040c4150703034503407151f260018201e0741d6009034280f084802c0a00451070350b41000054048520041311550600741a003084400740c4000d00400f002070000004114880b5460020402a07442000d01003115001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565793732 1250 565792482 565792489
    0x10606080603030a0804020406030605131a010311010f120c0521010b070b0406020f210f040c060f09050d0b040c0e19330618030b0a0b2206090605 64
    0x80981d509605a00204442e46032035026510044c0c000c2c0c4090400a02540c0d6911800101c0d50141c84010440403c05406000d0001c190b107448091440200c00b2542c651455a0720444d00d0082e4a81d00c0c1440706100401c0c1080d405100c0c0800308a500400910401e80c460400034810342c080103c2822000e89020701131020415140e40c68107031148210704610300040798a804000301c0005008480c0c2c42e408000018081d06000301904480b441504002d112140383c483d1000002402841e03504002620010000030401c540b84c86c8040f9a81d90801000c0c1d01d0520340d0480709e400142c1c2040d80c1061204122008208a65829601c034502a40e510b80e5550b8446071900c460040903a25003107080c14109000c4802241c550026410b082040b00c2c0c49168491048030b41600c0e082e00603903059418119004001c06074010f400501a2034104925180143c11941d48005414020745100d031215a00e0b075651801e500c0d02585465143c0c01c5092081140d000000220090000c03030040d0b105403400d0071000511420f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565794982 1250 565793732 565793747
    0x9010803041505030603190f150203011d040b1f0b04030b04110109030f08030c090409110a060509360f0106030f0615080705090d080714030304050615010309081209010606 75
    0x5d1009015046044055170840d03414407100d9801d0b42c2d0f40c1f03440c00c0c00d40002344070710102c02080600c0e04800358880d89021520310010203506040001c0c90381700400c00c000290108041d0b07502c04a680c2d081d2507074210207000d014240d9030a0300440002680054040103201e10030401c03500c598450000030440b0135000004448014541c8002854a5210b60203c40010540c0001d940c1c8040d801c0343c45400c01e03883c0f500140c01d8501d05442903899944d40300c0303103148034241014010050581420310310320f07013200c000200745c4142c092060f00c0b00d050b030b5060080c402406080701900c10758807072156900b00d6040000114a655a007031146502003490028a1480c010513401101d0480d40100030109201111940550301841e004110f042001000c221400165a944803903a0505010b4802030792180b020380384c0b10210120000b0079030740a90041c4100b100041d000075105a000d80d03459008209810b0380c40060b0050074918100a00c001404900d54a20f006402c54161003103080000034003880b503566005442d4070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565796232 1250 565794982 565794991
    0x307052512030503190516080105061305060c070510080a050f0c190903060e030901080a020301050a0512030f0a0c0b060a0b031b0f07061d0106050303071707020901080304150503 78
    0x7000366410312000c28058005994410320800d0414010564181007000b128022140b8075104890011944030090340a540c0602401090344c4c8180350900f18524141c800072141f18103407140400144488000c07a003404081e008003400361031808000034000026000c01400c840c0c1c0c00107140b40000099040030200c11680c015628443c42924041c81d0002e030325111000c0b00c1c0504140810400000001015840b410420b01c5000b0055a204d09000d80014580c1c03034084d114191003401480140f00c1903032035034403140c221130045032501010714580321050705501035590004080100480d0080c419070b04030994900244c072030505c105856442000700710b0700023024046e10411079400c0c00082c0100751030405000051200c1402c00b030900290200c0d4907807a40c40b2020450703100f0b480da594040810300e03030100c0d9880b50301594001d000d942d0519011960340c0c01291070241000e0004007a8040c0910840200d50f00d6070b4014018031120340e19610392603607903405489100083d141c0d24200112082c0300301c050305d015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565797482 1250 565796232 565796249
    0x30f0a020a08060f0d050601080f07060c080d0c0212071a06011d091909140601080304060f18080a05010b030f011a06130f0e0402010e04050402011b06060803070525 72
    0x280c44050902052020840340d2540001c4005c0f110000314108004050080030410010440d0540303052902d81000104d521140074840c240040400040200c02642c10342c0c0c0b0b80e5180000d1990056108a241c8020b120700001c14040004201c010301c41c14041d400c2102c5d0ac01015503d164644100440d800e800d51070421940100d1a4021501c0c6d24020140640244980ca21902e8049410400c80e00700e0321145002c642004542d041c0b441e0050b0184802801000000069400c140c070303000001e40710301241e18221701042041e40303a48a0040441d40000054041642152020307056450003d00800440c400103100340f04010340d00c2a510303414040c402c126084084a0600b641505050000c00d030000f40001032200020800031481c407500076086c10080c014a08c20380001d0400d40000341070a8400c41c9480d00980c1404100170160b600306045010348020325140310802407150611000500f0700e370300034501c203010010306941840400580000d0b0302d041c03400850018480311502e03625203583c51159444 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565798732 1250 565797482 565797497
    0x30f0a060e070309050c090c071b1d01081c0f0e04021605210412080306030f060420010c0b06060a1205070207030c0f03020a050108040501020c06010f03062306191a030f0a020a 77
    0xc040380110040d0466040041c2b0105480380c5402152180c0c103526021001180f074010000e050080094109501844981076042c600c0c881f401800303241e040c2d0055042c4011607824070427070b0b111a8121900300d0305001ca2100c10003107a151682d100c11042d000e072010400c012801f0352040213448100c50444082c0b148080e00800d02d5500c0f986036401c0140611360602906000f59142601402201c2c4a14450300945000400e01c041e8109a008204582c2d410018070004c11400180300340b0703d040c2c06c050125280354a640b20b415003112403034143c1081c0381d0003c0c2403105200305650009561800c0d02c0c81503501500140e00d0300b40c42d0302044c1c003e10000e50f112800d0f820401c205d501905140341c003c2c0c00343c0c001510381006901810316184081e402071459001c901e2081003440b4244c850905c1c0c100c0c202d010794445ca4030345100100300c060050110751040303401000c1204031100c2e140f507180080031440025019060940001d01e241d420403203541c0e801d42103440c001004404103100315603119038543c65061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565799982 1250 565798732 565798747
    0x1f0203090616020c45091b0906030307060f200708030a051312020a110d0f0201080c0c1c0e15040b070c030f060b040b04060b030f0a060e070309050c090c 67
    0x807100070001a01000c5484d454003440406400750135050b00500e0041c00040040c5517202240f000020080c081842034000c4840c244001c00b2035681080185012602c0028030b0300d071200001d00750302c03c41c00b00610003890f00a08203071002040e00002c03111000e941925410045a5500108a21442130300400c031040400c0090b54181c250381c0b0164102c40c05403031141e0700d03803036603903806501c86020380c0300d03c026038811080d5000300409604d55440a00d029550040c0c4402c1599600d40f42c11910403000303041c847c110000400c4111448240c0b558201014220380905205040018a042181c428203000505201010980c4c0c2042241184182c8080200c28502413030500e01a20940082c0000c80d0f8982c500394000000c194429a4484441e0081070009000903920381080111184244054000e90074040c041041003a48815640e01c41841c200ea100e0a60f501c0081600070031594020100b840c182ca418040d03120f41c5a03001c0d5607064400c03002c0700c0d941c1c01e4200c2041402d6504841d01e00c4261410030100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565801232 1250 565799982 565799989
    0x6160210020d02161506050f0d02010c060f02210741070b0f0108010b130908040806010b0a08150604090f140a0b150901020a0201050307021f0203090616020c 69
    0x415009142c058010700700109400d500b015103130007101c1a0764002e2602d8281c8001c0c00c0910881d0002e21084801103010100c040c04160b100600c010043d051040001c100d0041c0101c9170804c40389500103040c21990307046240d50300412529182e5100005060010004014030b019003480c5445801e80aa00400500074a07200f44042e46240c2000b1071600c0f89816400902c00300e0805050307041c0c420280ca030160b2921510403400321805030b0141e0103a038184101840d071505c90034000742c0006080000401c2c0d104071410041c0c100d01c02d035481040d180c4242c100005810300740c1c0d001f80800c03100079070b50043c25840342d071001d180c00c0304040c4001c0d03440074042100b0041410300d41c0c019104045c04050105003241010181340341590101d03a84007445489000c1c0001528003100c2500302d500c4245619401c0c041c151000030354a061102000341404800004103c0180c020000361020071030720341c0b6035a5402c0707203204008040d400c1035403243c09600c21880812a034a225040208072840c075036005092905c00003042 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565802482 1250 565801232 565801237
    0x203090907021501030305120a0606050d020f040b0429040609060806012f0706140702010507050a060207110f120a23010207050304060905090c120c0c0303090706020616021002 77
    0x414055100f0000300f400c01c9210442040c2c000c501030b4590700d44485440c401400111070040005074950320b001010301c01140c0210544140500030100186c035200031803220351701c0e4461504112075034540400c00103450164460110b080c6d0742c50060011210f040b841d8104214029802000d004c1400c00300305011152060b85403541c022130515040c8909012140000308400040e100e89011b007690581004801d1810450240206804d180c1184021484a00c01886015241000b810800001490020b108080016003c00b5400910441d9140c109203014240a20b40c1920b0340d02505851a5100e00780c6010600011003110070b002811440039141c2c0c40c030301081e01610222003c0d0b0380182442540d80300074405813042d02e12400c010340e84c450034004064016407859000c50b1240c005035080001051034041614024501c201e9840701c651902414404070340124a0200c041d844048108100c00900050b20b03401c60f0083e0702562440e40310080c001e6142c015510031700c400f581c402c2c207008484543c42d500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565803732 1250 565802482 565802491
    0x6120f0402010c0204020318120f090f0325030b0c0304020102060a090813060e041505011407030306030812040204140c070f0c0509010803070b070c121b020603090d0e0d0302030909 79
    0x1003030f10b6140d6507540090700b00c2e041511480c0000309000301d010608442000302ca0380e007036410902142005c0c2c5008804c115444ad50784080c1c00b071403031003000d152076445c10004c18154440c440e2512005420f12141004890034901c803e0b581800300e4030218504d05011f078100c0340201e0301a0b0160883c0d541b050080405003242000c00c5880f10800c01c194480c03040d100502002808242c3e8440105411705000c02040d20a8106a100110b0301c110342040117030f070002c1c58bd000100320340707204a4660340541003e500401241d800507084140010311550f5001c0311910b030501c164422035003089002c100c000141000141103510000b829002c2264001041401c1d04440e1303007a200340b8400d2403980e125008160100000c1c1d01500c450b0340041416820400710b145025404103c0349000f90308410035403201892800400790500600c030b25001c0c100c4981d46100d400c0d06010b5000703019142e603030404060023039030794040c040510002000d10780310300103500d810030903c0005500340e401903082ca101c03101003001c4c5c000d0140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565804982 1250 565803732 565803737
    0x40e06010813080406050a02100506030d181a0406270b07050102040503100c1b020d0f030509090423071233140c1e30040201090506120f040201 63
    0x82c401d400265040d002080030b81103996a06498400748103020f0b1070220b0008402d01d5040c1820100405030300c0001d00e0405540c01464984000d5041028191500115402a0309104400c0e0307070310200b4054140040080318042ea40c4c85c0c40084480d517062a18001142e0005030b003071340c221001c2001c2c0f642c40000d000c030503000710001032070a03a8450000c0e01c1e003030200ca07030f00302c20315100c80014146641024007001c082ea40350340b0540044245a00144410394540310007486e0310301c2e80c6254002c1c5445003007a2216a400644110b14034201400c2c50b030101240007070440302004641d200c20b01c144501280410469266070b13100c2c000c401d22640d88108000b600d842c0c400040b020080f0001d9000280c04a00d410041d529800003424a0b0001d001c4c005110010206644054100090120b041c24040300303000c803034614104580c40d680011000b9048181894484c0c1410354078411161201d484900c20500580c402d0300c43c6118240d0b140c1c1406858001e54074142000c801490005d1881d03649141c4040c0e0161051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565806232 1250 565804982 565805011
    0x18040b040f15030308060303040315021b0105070c2d020607030509100e040c17070305040201090b1209010c0305010308160312020c0c01030f0203060604030f020d050703051f02040e060108 82
    0x700c00700c049910400a03051442490403080042c10b401032804c81c0c006005a024510b8a42107031206d2009200300750506e8030b003030b600140255012840b00c041c0f00e0a2051507000303000a0030b202600514100c0e600100340c5909002159243c40c902202044680c0c10b0380c41060741021200f00e03005c00c503254003d05801d07014424108541921a599110b02040845241e2076080000c5e158030148001ca41340070b4075a40a00c80c40c641d0540402075500c4615500850914001c1801c0c0e44501c0100d0310810305521549120502007050f941c070210300002c0314420252100200319003400d0703000c12000d40700f080c44090013441d81048001c4000d5034078070341d820324140a81048482c442d004d400201c00c03a40310302e010184903001342e0808459980d00d402841c140c46255542541103040c035000003802da105d90b1100030f00c603204004070307407003192034008243c3da00c282c0110030703624065501d04209440f81840741c14034040e10016190500c1c0c40c1e015100b51415076510304442542076980400540c0c0b07184015000780301641d840c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565807482 1250 565806232 565806251
    0xb010c08090d0c06181a0301090b0f040609020703030e0d0f121e060938180c040303090806040314090103090c03080d06060507050c210714100518040b04 67
    0x248002e070008026a5444280b000d600d400448080b000e180c0004c44608078110046c0d01c100669015241500c644c6540058078486480000e201d00c8284041d4540141c142940007401c2101c55003d010100c0c020b03241030008405004000d034442840001c4e8002141d440b400c2885494825002680c007401000d2000692092245c0c0f4403450141c080a034101440d180c1c8801d024150081c01a240ca40b441e050381c502001700340d076003040c1140c0801240f560105100c0018040581d50316004c20b04d90b40d1084039000d03400c0c186103203001c030f07143d1007400182c01103441b50f000015103000000d8414801c81e01581c45d02c6604080f108500e51641c014846241010b8480500030040380311041064029031068894560311800c00c1110410380708541d0004040c0310303080c00720310b011400c08110300888520446851103418013614608c0c032458100500d0341c1c000d00c24110003103003044592411500c3c1c20003c6400002240000c0000c032a0303442040b032a0000c0b420050070f41d50311818103401c05254880c0081c400328070f1055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565808732 1250 565807482 565807493
    0x60d0b040807060e0616050a02032b0c080f0a020904060b0d09030f0c0809060723060106030501050f01020d210e16050d0b151c0f02010e040b010c08090d 67
    0x106031400c0e01d5140c00000c1c0103042050a125901014610501a110f185088000d60b010700f031541030204280000010303000c0c0e44501c2402100d035000100801c0708842c08031010009030882da410403089a0320b103010061a43d01e806403050303500c2403424031908038256803100c503110040c0d0070000b02107410580b200c1c0003103500300703142025020a400d24000001c0b0121a0b003801000990303030086000a01c4000c0d58030303001142030801151902c1409655280e9525660301d00303155000c40014030050303040c4850500c0e081440000c1002030403941699018016070740c890007048a40300c8030a07201c40c0560301501c034054600e030007150001c40c801c0b032180315030108850050285d0107882143c0080c0700e40360803c1c4040403d10300d096003254054601610b00a0020000f03540714000c049003d4402c004140161480005079968030703544d0140000e52511207040203206e4542031994290144049000c203122001c07150b4141464440c1c600e00302016981c4d10343d0300304130340c07a0503009034400310b0440c1d004a24035119102154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565809982 1250 565808732 565808753
    0x3010e060a090f0b040b16090506040b07080d0e0a1403092206080115050a150206180a080711040507031a13020c030a02061902040608150d02030a111323060d 69
    0x81c02003098015514040300032400d003100d01f40b804806d01c4003030303841804692070749825034096910129585944543c0c900b07001009000340b42484801904040e01c003554540c5c0440e8242c1014030034007512050003101d80c049504e031301945400c01d420604e04851b40020034141d034903003204407480314000668107441d40030302d5094490031450328007120040030041000341008003580c802061084000d4403940d40340000203407240f070003402c2c540170003d203c1c60381c00c214803050020311984c80d031000c0c110f0760f80e011501e460102c05d1305000c64103110307a20b4000080c101c1d50081c050b61070940c6888101c80e8230b680c10081004480d400da410403600c1c02d507003401501c0317482d0400c00082052842d15002441303103180000215041c0010f200110a0160060004010b10303508503420f1f036005007540c00d505012005c2c01c00494220400080c01a40c0340c4254070750203051042c43c20000241c2401541c546401d0305510b96060192616010402da2a04518108409086c0e400210340d4225a000b8128448080355848503560301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565811232 1250 565809982 565809991
    0x10c0b0a0b0f0103060b07230d0f0e0f22020f13051219170f070606060f17010e04140d0905041406010c030f18081b03010e060a090f0b 59
    0x40c0c0d10000d0800c0d501d031007541c4940100013464140040350400d0b0b55144503006502000301180c0b17200201299440c03010080c0100004c2038070441d40313000300d810f0005000034001c880a01c04103034411054041801d180ea0381c2e0b0074040024040c042400e944426544840d110244550a0258248080551020950006d009602c20312000750105400d09003003042420103910300d4090b985c0002c3c15041294120f05035000ca43c0d400c48000c90856800110000c240e1051200d440c4d00c020001944504100d1140c5c0540b0075911281d50f480c0c04840f6180d0309456401c1c0000003c000782003101c00410070035100f4401c1d80d62013031042c41c2030b140c8a06600f030700e5407401c01c040303031039a01142d00083e05210b1400c180c860300700704501e82c0c60085420b09104001a0071034115040c080c04200394040801e050302d00400c40e05802900c0c1c95450780f0107650300c1e16015140c00800c645032240c03010816900c4141d00d01400b50004885c0b924020b840603485010750360000304031449040340d40320101142078001c0f904601180784074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565812482 1250 565811232 565811251
    0x60408011b020105070c121e03090c08070828020d0503072f040b210a0209060a0e0c070c050406060914040e07170307060c09030218190b010c0b 63
    0x200000a03407a028400d503241c680c07008582c50b01c000c00460030b03442100744c00810382001e103070040d4115aa100721820003402e00030450b9031402101c0c507406103515900096a850007000324100d0f0a4442502d15180d41d024843d03c516940b1400781150240070034061143c9115070707080c9400f0000c1555010076a2030120800036101754001141e0001400444602141014a4200b10341c0384202414580741c1010950044d003400380d030746c407041500e203916902a5017a0f81004601907010460310440307441e503a00088541240107440103000b0a00a040402c040070a607850005120300030703510849a40d2070740c0c10129050b20242c12440e000141903d030b03441148040c00c0036030f03502c500e098107103e800c0c81030172204800340d40514500000440b00642c00305019064031940451240d00c49582018940b45020b500b00142c50b0038075015034086c038190402644000c40380300b900c41708002084458090146c00341191850000c40b0448420203160f01942e0229103c40d105050a1000009646517410350381c3c42220400e12 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565813732 1250 565812482 565812491
    0x3020d1b0c15020307090e060f0904080409110c0307170708030103200f221d0102210403020706140705100504110604050117090c06030a0b0a0906060816090506040801 73
    0x1d100c0c2c031001c0d24402014100c001e5140d0f0903c0d8030300800d10030491003180c0d4200c0d2900e0219896640300c20a54840034070040a400312801c083c10a0781c4940c1c030911030020810301c0c005102c8002e070840713025500c1c910745090207507003052842d0721080c00c0a001c144600101c02c10420036180000d8500303001d90b000e5402620443d0908645c62a01140c1020401c4000e03c00c3d00303810890420750351402c81d0b0f0003511840281100403808118104400342188500c00e60091000174920401d40c50154040d1411070403e45001c001d01c4a1041003c4091200742c4018006822580050000e240280031801c046121280000d1030040181c07110b5007004240401000c403113803120700f1b000034402101e0811765098022503145290514140003e850200c181941482d1028204005281c411083c40b90061001000e00410307074910308003117444020460300005502c26141f070807001c00c4201c43e81c032079070050700d245131110086e0342c4030130324464201150300c1c0a2004010f0022008125501e8910140004200b50700001c42e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565814982 1250 565813732 565813757
    0x90901060510020d08060a0b071407051c050607090b0a030b03030714061b0f0405010804110301060e1e0408040512011b020705150a1b050a0501022110031203020d1b 72
    0x402c81780c80070300780f00c0c40b410001c0b00c103105201855044411040d44000c154004143c4480741c641010f03510b40c88658404841070340742c03c8007034401c2040c5108a2150040da0382c40d40d5900c1e02940c0d00c510a01400d803800005001305001c95009500c24400210b0050890b414040c060741c1d000384d4a040c1c040c03140c500d42c206206014084000240f4240044140c040c014205452641d814020340107a228040c10402c00ca000f00b4140030b40001c0040031504041c000713128150321203814524800c03080c0d6a82540482c1e200c42545401d0885030003600031640081c01d03621340391800e403c0140603c15440e0080c1255640e414003507240d06c5004409013000d0b8641c015000c05c503d80000c00082041241c1845038505042008941181d800300d4101c1c50500c0c40107500e000524a400c0840c40c03d084210001c0c41d96200050400840119095400c4128207030b07448030107680c0d150074846a0a4000d40320041c03946e2100d8031007540c4a8043d401810f6400440100040c5040d85102c0303495282d90110700784004118500c0c0c050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565816232 1250 565814982 565814987
    0x70b1f030c080d08040b072003120708070c151119030b030d0201060f050904030c0804080c10050901020d0e030a06060b1b0d0e040c110f0d03050106021b090901060510020d 75
    0x30030003c6038100b00c489440c00d500c1b20030180e10020300b980c2c1046800b040c03451540084c074080811007407400044a84500784210a101c80901c1030707540101103820303d0001010341d0f01c00c40281c1c503607540c014510049510407020200c0902040e030303c0000782410500c240c000080c0788981c1181041400d0b13030040f620034110f9061505103080da01000007164189042030104400d444d058030100e5009030b0304820705a445007800c84020008660080041e640010005032541d0b00140215000d01c044542103150145203400361064032030180b8003405604451081400e050140c00300b03410b400c10103810745400492543d02e01003102c840d130b00160000e07180402e07010043c041018003a40e14601510080409102890015000d007200020341c0744901d44805900401ea84120000c540041c3c199013110540705404c10303515101d41030140498000f914100c00007403281d10002d0304810a200744006060360f502c1c60700500c5020300000f4064001076403510700006081e240e02c042034002100c980e001e00402e01200500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565817482 1250 565816232 565816243
    0xd021e0a09060506070b0919030207030c0501260414070303080109050c0c150c040515121506041e0b0a2001050708070c030e03030d09060b1005070b1f030c08 69
    0x1000101c2e280c0301051110307888440840e40040e4203e050303403025503585a5403a1604840d55000f0070119411032100040540000c0c050341581e104d03142c0c50704115213030001156822180e41c050340c0000b4001c000c8248800940003800d4200c0d0040c40713202d00c9490507144a074a8480607a000300c0003c3c0070310300100420002c5c2e02c83d4640040b030b46444246008030500b85176a490840841000c06409a00302242044800d40119001482c0181c00c031a112004481070606503000140341000007846080010700a511610f803441ea038902c010812410607003003a03024044034031351f44038101c3c0c0b00c00441000300c0d103103040c5e2029001e203404990b2400a00c081c045031007101d038085070006c0c1407503a04010031b1150894004c0c07140c0380d0203001c0345803070b000d02440c5040442e03041c00d55941e40c54150000040c1600400c445401c05a16580104024065074403508203200c594400b06071080009075080c8030010000f4501c0300c0403500050104881b40c50f103510702803c91034014440d40103c0b500c0c10500010402041c0a208 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565818732 1250 565817482 565817489
    0x18170a030e01090308040b0a1b030207020f0d0b0c0904060305070b07020a08010606050406030b180103030f02010e0f0c01031e0203011e06051303020927010b01030e1f02090d021e0a 79
    0xf401400c45958001c1c15400e0701405c01451003071081e000441c1e408195020020320f12080c525054000a5410f02400a61025034141e01070300f90204e411843c2d0801d102503c0c0c0d42e41d84569105410341e01d5030040c0c90f00c0d8100c215650303486605c400000021410810000c0d015289011041c2e945103001e01c10800d0480c2a07a00c03d0b6400c0c3d05215042003504d4100b01a501180c6480c1000b00701c2400c0e40e00002d4202003811824003d201020b400841032541c040311418038244190000c01050300e0321065a544d070710840488145035031201400c01c0041d4030a4004204020b00c60003002050300150031118240d800036080b004846810034510001100d161024900604a0381086071070700c0003003034100d40701e0380050201a00071030b103040c00300c0c50301800c00e211000b0314400209001e41000e41c6012450180030740c41030040c00039050840e940051100450784011b80459004031311404040d289210f00a50080300525030302840841510000d030f2200100103c01c0b07410b1010742c1005801050401002070007680 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565819982 1250 565818732 565818761
    0x12071a010518060d080423041a06030c070302010905070b03190e2a0604060c020a0e01050108070c11090f070f0206070f03052a0a0801080a02060a0318170a03 69
    0x31800900150750811500000251002d08400c861404e002c140c5d4413480e80072002407520300c80349070440d90034804c030280d41040843d410301030b0f442080405003444694000c50b5522800401c041485894414014039040d441b9000100720200f0940f1382600300740f00e980c008403071014001704004424040e9698580940e44040040004085d510401d681d550000700030301042c110144084104440c3c14080e5140f54000100b020341d0f551344441c001002044070880c100c0c020302d0005000328034581c0c46100703079058440603910743c2c815544440040340c250100780400c3e150079030440007018054a65900e058410380452595800d5810400d0004000d5680b014424086400c21000d210388a0f50100c0e88510b074000c2840c01155a403103074072888070440341c1410141d6a4540e0588414a00c80f8a400a8006141107403110a040daa90310390b20364580d85a803500a52050040100d854940d00a5006420303e0314403003400c805030a5940e83d04040b8011403101015812408101d1503025a454043d030701c190404507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 565821232 1250 565819982 565819999
    0x1050a08060f011808010c0e06092409030a0f03170103030f0c03021501080106050126040206210a0b0418021e0112020d020306011b0b070f0212071a0105 67
    0x12080100000d0018210500c100e0a240203118268495a42e510b40415150b050741c0304141d0742e00ca0b0034001c002d4007517100c0104188003001081880c220089e00c0c0c14043c085c10061a403528050502c51002440060303140485042c84000340700e48040016000c1e962040c000302d8041e00280c06c0c0641480405503401c2403c0190100500000394031142110f03121510341800755040c0381030314099042c4009041c004034910701180000271025815084501190360a07214462440380c00c00c003034801910103280161400b54203002060040c24060020900c41681c7e10503142e9078240741340d2f550004001501c600d010700e030702e0b001130603091b10f000d21580303070502c207884052404030a0590104a6118a40809141903003244072450243d901a903e40110f006610908650b80e00190403400003d400a1324170074001103400c0c80c4010700d10300c010044001d042d0032035810220b554805000300c4045132098004003c50046886816110344618084c20035180f240d00c0b60809090040780030071602c01c050703100382c1c8650041c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 565822482 1250 565821232 565821247
    0x1e0409140f010902130513020909101a0301080309012303040b010302040507051e0a020c060703030c02010606090b070b090c060c0105060f15030a0911060703030f06050f030705221805010b0105 84
    0x45c80e5080044450079a16072082c82500d132159002070090306000c0b500b040625041103d80100b010108050b14010315400c40b10480501c000c03144c5000901030001c042e44200090b41956005640429543e42d40f00701010004101c0e1554400a41096804541c040910801801140307003a000701c40d40180d00d46041801d115404c0c022080703003000f540010026030b1000416070311051081c08032070194900030b030040780c0c1c070f141515000f070007400039910f035600651030680003088152003200c00c1000c23150781112160810310981c6a00c000790750007800f040c01030711458100152a8607560080e106400990000003524600b1000303021615044c80007483c828584143d41c21401003040064a4102d028210000356084140c5070001c1611406100c0590011021858001b016459000340004a800040a100065070b403014408440c10a2014a6041d003141209120750700380520303102c014030000040311442080c2102d5000866443c564030501c880440070003007042c02801d0080c002561003e00c3c0c6107240490 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 565823732 1250 565822482 565822507
    0x20423010908011e05090a02030717060604060f06050c0c03010608070603051605070b0a0b042c0c090a020d110705030c07060c0503040603020c010905250f08031e0409140f010902 78
    0x2130344141410a03560b0021807182e00041240010590b070103811900265119600100c1018402c07090b5800d520a9034005601400c3c54095141240e0074103844180c05800d2980036101508800502c2c8114481d0407100305080d5000d000300c100a01200010384001801d140d0000d098420080c100c42e9001158054a150550301c075044900060304442c06011030f40321018160301810140c550a035005042c0094102c0360302892800c0e6424038902001010315501c84602e0648078141002c03440d501032402000158004410f4000340919042c4c00300000344010b182d40700011175080b862054801d540007245d541c4040000b000003101500361400c003011014503030b40c7c400e80d8074446e134084c440406801160420302d070b030382c00d402c03c1c082c82d5482800d540c2da044e4003002101420621000712260810041070001e020392140b044d10090b140400091807a023066500f0029504011411070030403880d00b000000381d110310a00c44d2506a0400c244c1c2c92000b410440f1103100840750603005490f03480c0c41001021403070703c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 565824982 1250 565823732 565823771
    0x20706030506210f01050c0310270b01142d03010b040b0a030204091d1212220c0305032a190c05120f060717070e030102042301090801 59
    0xe10810043c2c0603d08000d203a40c00c2100b04810380724650f0a083c1070118500e60315011318820b03503044501303421465562509182c42803404100590f00d40140580841074103482d040342c00d18000c1818002c10780002e1300644640350b4000c1e120000708007225003100310b003a80c9403603034101004401545542554140304020b04107215501c2104028040020112821802501514000c04040b00e0410a810810080048440c5030001e05a0117000c4c82d82100c514210801c19a0030414070b102503868181d0f540580241480100070003600a070340d044403901e00161444c61000003562040300a15217a80400038034503141041030880c500b451001104110790b0306800030b514503214a1890f81e07244900603c0c20a4103514940c2e4001a4000e1200d2102040120f400030300e00f450301008a04507407080d9920001220454000503d0b40b1201d40d01e10301290581c0d200c4c2d101102c84034030040005190030303983c0c07060401e1840000e01c12600100d0a880c01d00040d0b80250049008100e81e00c024042801040500385044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 565826232 1250 565824982 565825009
    0xb0f0102033411040c0302270402040825050a030b0721020f0403050c040b1008071715090610140705031201030c051c020f040c050c0a1101020706030506 67
    0x2c40d000400040b4400c0d2603021155040d0580320140903911443c01d241c41c00080d10b8400034026401c01e000700c1d020742d100344219400c1d007519080366007043c0c00c554460b0301c041e6662007845030300540a100114000c20140109811103050260499000d02081000c0a9940c1c245d40702c144a803245e44801c001040121109a900c00214a810380780c20031049001480b0804069511800394404213540c1c2174440c0c60b900400540c0c3c050000c031000960309030304000135640341708800c81d0407030500120b0030045409401c2513604400f135410490485904d00008100c1206c00f103500401600181c0b580c004582062203505402520649422080090346440940402c11140460001550000c0c569085c40400e0003503400b410422068100c555a490030181084013180c010144125010064011159004038144590650107003480e980c500e06030040000a000003014601840003c0241c0c540007042400b01c408100e00c070341c10914941841c000020300d8558140c01c607001b414900030500c8036695610380b031580c15 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 565827338 1106 565826232 565826257
    0x9050708030c0c031603020f01021906050115030902030705270f0f0915040809010908101406010c050c090606120c04090b042f09031f0b0f010203 64
    0x1364040000217800c070554007030f03003000141043c20009001003014015220603980490242c822400302c540e003140c20b940c0e168010300010b040302c81d16040180c8503140802107425181d01081d030314400d0f4000c85126240c030280001405a00d81c01c01500462003a00512050500f03410054418401b41d400000d480381a200040e014180003600030441301d0382c61000707001074585840e04146644002482e50400c0f08401020507050410400c092040c150003200003024140d521004400d804042c28060401544144000c042980010580c1c1c102c0012600c103980d507155036001407018480e03144455404064141002645824036010304202c4000302005d00c40c03800840b00308002c55403c4200301a03504503c1c3c18140e6071061010b4140300341c000d03100380b103840c0c10f5160000904d000c0038032002c43c521903d14150409803006d10701408480d4282962420381040302980040d407a0702030980d00108 = true := by decide +kernel

theorem cover : BRFrame.Cov 565647482 565827338 := by
  have h0 := BRFrame.cov_init 565647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 565647482 ≤ n) (h2 : n < 565827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
