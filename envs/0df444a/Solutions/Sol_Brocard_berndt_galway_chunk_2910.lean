-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2910
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:41.811325+00:00
-- url     : https://prove2.me/submissions/d078bc13-3cf1-4528-83e3-39a7860f0125

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523201438 ≤ n < 523381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523202688 1250 523201438 523201489
    0x70905010f050a03110412050a200a0b0903030c0f0c010e0d02010c031101110c0109060506010c0f060c0e0d0b0411040501060509040905120c031c020f1c0608070f03020a1d06 76
    0x180c501810189007c0e110300041c0410f0310007424a1141070000b10b0700503201440503429030300a40d842c01854000c4407100e006aa48400c1c42c080001d0a5004619840243d4056010002034070003010030001503082013600d80c00070300c0710030005001000c01c244200a000c03c3d41c2c00d251202090054840e4041c00404000101d0003688007802500c072900305813054801030f91101519070402035a4003945501c03081c20318101030345c94600d86486d1074564803510f015181c6551a401c6208948c883c040107440d9a40142c003010101d1050718107a08110f01c211810780c4d14110443e40607007103240c1030003102d0480c0c80603540c40d41400381400410005001c1c0d680300322500e20034075440b04900000c180244c50401c141201540e21010342802c079088a0701c01c1ca50540031144104158540c14413404240c1c0c0240807078094609003108107200e0280104841d030801843c0d031040030000100123096007604003d40b44291001c1d0281542c1e081e04c440701d01000100c1041d0801b00900180c114244040c4034410042103d03c1400031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523203938 1250 523202688 523202699
    0x4020f1513080f0a03050c0c04050f011d04030518031c090f080c06030403030b0f040501030809010201140907060516080c06060a140a0303030e150a05070905010f050a031104 76
    0xc580c0003603046440440454100d04403401411954001c08812000c2d000c0d00c0c0c2000121600e448011300000c0601c0400308140ba10303507204108000d0081d0740588100440e0500003030f0410009400d1254090080446802d1100c210312590707458001c03507064440382d0510fa0003016402280b014407a11541501c120442c203e810710340028080d03880c46450300d071403000788d0400401c00b58880036604507400603030108651080d41c3d00c031941201ea1058143c54001840c62404000424510000070b18943c4181000000310500c11003400905031f0081c2600204030703090710b074609814000003c5541200540000404000b0180101c00070641043c00130b4407450791702020f0f607a40074039030030400b01d15602d40c1c061001c210aa04040c0d140c000640040564000204500030018400a001c0c0c0001420075413107a146503a180000c004002051182485c60000c1d480e0800c6514004e001c11075560001030760203500021720354081d01d034810101e88159500e519103501071809078050072100814203030701282000300050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523205188 1250 523203938 523203949
    0x8150408090d060906060e070c030c080d06050d110f0f0f0609060702030304170d080c1b01061203050702040f02090d0618020d080d1a03030a181508041b05090c0304020f 74
    0x1c64810304000038800d003004c04005030311400234814014061803082c208003198000788c0c0209280c1d400030b04076581b800d1300d03003200c0b000d854560f01440c1c000c1c0068401004001c2808a80170401009540e205022680c010820090008003000c0319008400c0d81103002403030810400030710f908100a4007462804100b60b01080c43c6500030380c000c854203070100e031080c0701070803051048048101d010300d001c4900c0c0c02c0c15a6031104910906907441600c0c0450b603124100e00314203400000040c96600003100d40c840160501405070ba1005a00324840c23072400403011030f984064402d40305010406080001d045404d03660381c4000304900d11210303104020500495005039103003840d07000150f1041c0382007078aa10b91040180d0603903241c0042064841d0700081c407240d003501c00205444000c0c89501d01011030031980c1d00c03c402c2c40704094014a09203804e0180c0b8407000303904020300b0760141e0301c40d0302040b80074441c0314104131304081075004860340812071801082654140b440650380040c001440490300c0d80c0d403a800280d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523206438 1250 523205188 523205201
    0xf0a0b071a0420010509061611150d0501120309120807021005091314060d0314160c080303010f0b07050f010c08180105010302280b03010b040f08150408090d06 70
    0x651082c0d1041e07507070300d200d80c075000303803d03038690003070901608040b44000001d101d8000c1d07828007080140c04185501c140862914030960283c00070308400540e214400810b0056400101c140e10058102400028241032640791260180d805944180c440c0723080480d00c62090180c0002511081810b02042001da070b209400c5412450f101c0d01c2d083d5450401c03205010103590740c0c03840d04440030719114501c81c5007810455a01c1d440307030044914101c01c038001d1505880c01c5205e12400b401110021410096042120080815541c011940c0d1846d0782c5d41c881980b6500e00c02405148070340e000d00f020800c0110400c4000c3c015042c840d20680e20004401d00489084a20791450400041c0340c103802d0084214174100302c200c45041041c000d0040d5811600410303810150000b0304030220560180241d00e484e0384d05601c60280c90038000307030356803560354140b2200c0c5500180a0003d5840c00030b1000200c40600007001621145500b402d8400c69459850b408003d0b004001080e400914121108001130310314403070078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523207688 1250 523206438 523206443
    0x21c0c0507030306170a1e0602030a05061c052e0507080f010504110711010e09040c06030c030b0f040902030102091c0b09030406021906060f061d0f0a0b071a04 70
    0x11925640c01d420000c06070b07440c55200c0d40d004a80e492041408050214101410395080f00d0000c050480b0b40403d040b80803040100a0405d500c08400e20000c0851078001e18011042100c421030740d9030303403c10080e2100c80d0b482001480d99100342078203581010800c3c0c10064074504614100c0110380101c40c00c0c02541c9007128800c0006200c031040003c11700c002081d09001d000190780401c001180031140301d00c86c3c810f8010140c540b0407444032440c40c42c1e11402c0c1451000030098010111402c3c1840c10249004543c091407000c2030802d6102690188a8446c2d03500740180100009903583c40703c400d00004000d0100d0698040d502082407205a03120142c252500c820080020000041e0b54113040c0c0c00f6400c090080c91960700b04000c2003024650000d01845184400700c0107100c0c400203490300e038008140c20b0340304026400050700001b0741e0541000c1c2c1701e2007081044440851500c0403c0802200c085040200369001c2c00c2c940040c011440713034802400b6010310600b21302d6981380b003001e003240569001312002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523208938 1250 523207688 523207697
    0x11060417061b0a050f0d110408070806060108060a12020a0e070c020a0b030f07110f010507050d0510030210120f05010803280c020913120504060216050a09021c0c 71
    0x40c0110b110044142d4000e229103a0320590030310454000c0200180704c0e542e42040c0c00320f0041218841201180e000b04c502005078402507980f5981e0399030450300c88180384039103101c5024000000c3d00f2540030b807074100e205100c01800207100c103003020901c04200c20300800c182d070006d400001c00314510518030b121500500264981c02c0d4131029500c1048800411500302000ca91001c0c018400b59002042c25981c02852074201043d5441d90154203600c2c018441503003100750344c00e01060188841d0014000d083c51040080c041c407032603a0350b442c1c0c050008600d210007500640c0ea0898108264455814800c080200c030001080c0e00c04900340510503281d003030b04450f0840d00000783e28180c1c01500c1c0400e52031404004d46004c1c440f0707140f00000c2c0210352510000382c0940840e83c00680c40b605035410b0219070725400240034191000f4000700408170f030014041c11000d031103034041c0c080c1c449201100302c40884000810710100c090900085c000070350041621700702602180003034500c405150b03001d21185a03845689 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523210188 1250 523208938 523208941
    0x60801082a1011101a010f0c1b06080901021309020a1814190f051c0602030f061219080706110a08070e09150f0a1a0403050d0315031106041706 63
    0x806500b803d41c00d004136400c0c0740c075055920650320026040c502d03c10000f420712400d0101014004e440c05004828002c7c05c00300c4031448203800210307144c04841590407654905c0b06650310b480700b0038200c1c8140c280701c4071554890841000400314607001003080c0da40f5482c0085044046c03000c2c009044410360006150848617141c01c139158100140c1c516842c60000701c0001c5043d01d041c8111641510a00903a405180c002d00d01140800c0d051886258480e4008011552031900b510341c002e41000644080d840f6092100c51110390341d0380052020b00320f24029041c1c0100291aa80701700d02588030380320480d0220740f14804070207000104d5004d8a400403468981c0c1e0214500100000c2005005420046c410103d0340240314500c9403001c016640030300140c4182c5242840b40000544c0c2e044240d000e00508400c5070944c0320100750800203401180e109400b10788040c15441410303010b840390301211024001048a040010070705080e170130f03000c210b0701500035450251610303045440781350260081c1040e03500000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523211438 1250 523210188 523210217
    0x2150d09060b0d170a090b030115030606031b0c020a21151103010302040c090b0c070305010f09110d03120f0902010e090c0d1512060b010801060801082a10 68
    0x141002c240c0049400d1401d07484940e85000e5824680100704858403004030781c0c41d80f01e50168184002901d030640d900f40c0c070396a444288075948010120380000290a0041c00031f0514001d0282c01d40c2d04200d41ea580c14a01841d607002c803041d0b100e609041c0d80c801c80844001541c3c54548924091000289400d04500c072070380d0611041e0303d0703070407070407072850b00d00d0030b90143d00d000c502d82c007a641565411107011584404c680740807200c80b4140d0f00251a031040000300382180d240d0018160040f64800d400030b00401c0d100c4083c2d681112000d60000c0c100c001c980603007000d02d1a002c802000b000380b280c100b034540c1d288420500b00c2141c061207281000c5580e11919030007075681010045641030350407144013031103192404500d401c500418503400c2c08151a50104a41d03240c0c59819140503002070803001320041e26504002e0f000d171180c0c0b413070700d0302241e5100d00120b030180c8100d6290341680c0500c8010590345400c03c0203611500700c3d10704c40003050f261801041941f543c2c4c6966401c0240700a661f6030b001d08070000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523212688 1250 523211438 523211441
    0x120507061103040807140321030108070623090a030605100513051501231233060304110409060c020d050a0219020109050307030803070905060c1902150d0906 69
    0x1d1401e500c0d0365109120801135078030001900010f94012814a40480c14245e001c00d00d041d0401950307092015040c80c078110b01e0041c8402460407140030350200c40c41c0741e558a0f005c0d900441180caa8035200719000c1c25050040003e08000c00152501901c0038900598a4032400b044a9095a1804042c541080c2c100300c0c9241a5080c1c060000c5016800c12090801100c1c0702480101d440b80c01d8103000a030704007406051030407000360500c5040c03800314580e145010f0170303980405c02040318256081c8481c65030030201c07042c00c2c00300c10304208090180d00800b49030903810400d0741c1e08002d104036074050061407112040d817601e000310525903105072000f0840d00c00c1c1c8400030303040c030021551000406c5001c1c07243c114440d82c00150340015081c2281e607102e02084900040303544141c80e8000320f030107101d485070000400c031540700158072600c2c0c295150203149403282d0410a035482610382ca00c4080c3e0006034007822070a0301e412288000c91000f8580c92400154440c280350030341201c40c00507c0b540e41d548101d0207000d000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523213938 1250 523212688 523212707
    0x150204060f051606050a0e07030b060a060e03030703030f0209060406032f07020d08160c031101080417090102100f021c02071a071b06060302030c01080106090512030412050706 77
    0x5040c0507007002c500d11900c0c4100406030a010300b40a0b12440482c0551b43d82d507003c1010980084141c841c1c1d03907101c0c00c5c07101d05044280c1e10b09025240180c80000c03003501c100c0e110741c0744890050247d8981307001602c08038060143c40000061441d401c00c00f603500d6607600e000500040070350fa14041440d400c6034a400101c401d80f81e140401c031000d82c000510f0307100911801c903124942d0440392880410b0450810160302d0154440751251151f40c05581c009021300043c0e004104c0b44281c8092a064990100448a1070f100381c6006003540100300b140990320740e050004e4590404d040c4126403847d065402070740c068a201c0ba5001914907400210006101300700e541c1e01d0506209214150329180380340c1e540340c20021200d000c805140300020007062a452140b40c03958424612a007002e240c203c03544c10030400134030242c48224401e10414042c01090b50150b50382d81e040701c0c841d0300c0d804011440d0030300348503036041c3d120600d043c90b001c05c00010030b002400300c5000e065240240001c02c5114100301029200519 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523215188 1250 523213938 523213967
    0x6030312140613150e010b040302100905010e041d060c030907050105040302100c021809030a12150504150803040e01080c190612022b110909041103030715020406 71
    0x10070040382c1d84920184212911945100181550300e041521003820041d802c481e02c0c6205440001880030440005001a40d000310b450001e00c0c100c030301095911002e030b44a00c0380071481035603041c001450558458042d4900000c0103621001d00a640507081c1001124000251720b004000c1c840550020048500646801c4c02c00510b032a055400007001d480070b4034000d800f0841b01c0040c030411915800c41c2c180400e24080740c44402800e01085031600d170f401c800c2d50310300002d102840407011030501c0d0103004c81e01482001040040c40c00d21062001400307240e01c03038003880e5408240000d450801040104010254203036000490350401002c03506154544488d24818580800c01913114450b1080c0101190110f060042c50044400c8060010707014403100a400900e150b10000d0407a1700c41402e40056032181c107401c00000d95070221144160141d0a4180d03040f101000c00200091507034855000704540041c1142c3c02c04c1500e503140703072840011040d6102e1603034010030708001d180d420821802c240c59 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523216438 1250 523215188 523215221
    0xb0702070801060f030f050c090a092d060e01061d060306010605070b150a0f06032301081506030114071e05122a0408011d030c0304050618030106030312 67
    0xb45070150044000c0345070700002c0d0000486c4196041003000c2003000101e42c2002400e00b02d5503241c0946684020f00580d0801c3c1d03001070324600513510034420031000c21002250302d1050682c0c41c42980303500e4018207420400f40f415660b0795401081e14210550b50300703039910084200c0c1002d8941001171506010040e80320304140300040c042c1100043d40480c100d07602c40b00801012940c3d04140d400245440c102ea44a00c035000c0c1d001c000452265819089803007000862140700d038400800c0c09042c1e011202c00d200300c580760b070480c0310407002020031810400d8200c400140003051607105205400c40e0b640042c0d40c184003045c01154244074070203585a4285040c800780c2007141c14040381e08030602d0101c90080c90400d6001e5882c00e0b0302580c0d51036502e01d50401c6001440c451b10341c0d0b101e00069008048618072950520f41d000c005040002e0000f04441c8886910006542024a840d05000940c0c104200214802c03003090001d16913a02c0c24403c0341c00840c042d5a4000064080b10003030811200c0012400940c90b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523217688 1250 523216438 523216451
    0x21010e030301050907050703090e01170c10050a050703091e05090a09200d120306050a05031b0f0a120309031202060907030305032806060201111809220b0702070801 72
    0x40e07446031404d690142c81d90501c03d03920344462500f110322003000d8104070003407461400081002001c0501e080e0401c030440c400c4070781c1125420104074444030419031040010b002081041003a0780f107900a08134261007070501070081615984004912a2407480c00d0b0047c1d002078034200068a440120305420030703c001d0082002160390340f52549500d0000c400c2e03200810b0507000304d028984540b0840301000e9005442c100e140f10070250014064a007900c10181304a460080c0400c80d40390128821010710004100c1001d035100c08000c0c4101402c2036195141e00c0210f01c10300107204040005510350b114440d0743c44080b014154a0015040c40d1000909c0c01150b0004003044141d0724009020750607a038050400c5500d036942d441070821910040a1a0200740b51401143e5400038443e400146c240c5030070307400a001c00d180b681144112f5000d82c251400c03c0465120014099080c211201504040006415454000203080c0c909102040769000c84030030714210100015140e06204000c06409524020f0010703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523218938 1250 523217688 523217699
    0x206010b120f060a0503010e0606030601050a30020d050f07060503060f01110c0a0f08060f07050307050708040320090a05070e0423280b0a0303030905010b21010e030301 74
    0xc00c80140030000202c1c46001140756655200c508100030315009000303204d8a00c0c13200f0b03180c1d250f12054803410b0203071045070000706d01031a0034a00c40050300c88002ea441204050410720b4520446440e03001481c00705000e0305040961912071502e48200c3c00b0b00c000b004204651941c4625046441d8408010020180306104542e039484405001049091819641525081140c54180a14a411968803403d442c0000a200d082d82200c40c08a40310602566505d50319100724441c20401203401c0400518100002401c0d1070240c1c01903e0294045e480c242d042507203e41e074030b13882d00b460042101c0034a113100c520345d0300500d00070080c140e001100701c00a01c03180c1040701d80a095024a018094071454440800070b55551000415070341c018083c071000e41660522008001c01f4800d4261420071048809006116040702c5015040000a004d03180d9803000e8559202100101440c81c0125030954031500410419601e4003964001110700348115102072030301160040c2154a0150505034030703041800100702d0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523220188 1250 523218938 523218967
    0x8010b03040201140c12130e090604050a120c0203160e09011a041109040204060e011b020a17030d0e0f1018112101020304020901171002180901090209010206010b 71
    0x1001c19a400190b807204084a42641481c4900e40021103c6d403010504442d5049445030a0b41151000350340c0d503015485510f0100c1d1501d00c00c0f140949070f54081c2d8100c1e40018110003004050411501d04509032441d0b80c0d0001c1d0511403040b00f02c3c512000c0010701840408050030000b40c114000c00d0082000c602e01d0700511540344a0341c0d00d41407040303640c0d010f007d1000c0154800c445908030014000c5548940740c000240c020342c840918140002c032140e2034001c0800104100e014003d030020a0700d031495182c81004443e16003a4138001001c0d020030b100107841c2103c81d0140d1095583c840024010340c4c08003102881c0380501101c101111141894000300c0750041054114a00c03035040002204090700f013402041020002542d420030130201e44002c02107912045d400303140a82c0c8210b41070590759a0b907040d856081c00800d550b5080a800041c00d800c0c108106900a00c0101c4035003100f0101c80800303000041045200f40c2c8143c20142e00010700d400c5542e41441218003401050b2078507800c00450504164 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523221438 1250 523220188 523220207
    0x203070923220906020f0c010c1b0b1510021e01062904030f0302010c0339020c041805070602030310060f0e06031f06300b190608010b03040201 63
    0x10000010309001055a00b01078000d507080c1600720405641c0c40b0003058144030b095001c449100990b500e018402c05516214110420864907401d80c031100c5400c882e1a400e0071260050304469a940c0e2540701c0c2e122680783d407405085081402d801a1900703800d00d0448042c005805445a50681d2406105200d40d04882c0d0826038480800d10011284409294442515200780d400182019440306080000c1541c15008a00d00b924259003d010b100003900c0340d01445605416604540d40d031000c1c00001c0e040603100d40d43c901034910f20407501c501e141c29022404460900c20791000710300070a0104000d00c001006503078001c003076500c0114910b15250b000711100c1e10840c01210100284115820000d41c441c1610300b910020050149540b400c00700064812044055400c1c55801403a0800103191802002641440320080054a14001441a601c900150701c50782c0d03150b41c1e9503502c0d145440f54546c2d0742e0f0950324401194040000d030f030804a0151046005078406134030510104100700042c3d910540c0355 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523222688 1250 523221438 523221469
    0xc0f0f10030e0705031f0c020304060f0e0f1c0b090f12031305010c090302010e04050606041a161b08010501050105120c0c060903041502030f040b0903100203070923 72
    0x7440340800340b07a190400d00c050340600d03414410a107002c48480b80342640001d440744946000c2103501d440b072800766164041c0c1c0c4244004240e200d4038800595001d80c405002050000745541540f010820024507030300680c140812802a003e4460700400109051103038103c8000e40041122804903094070341d851041d051808040c10f0f02001240084442d40c04105946038044020300c1359230102c96006242c84060f1105a0004001c2412111181042e10a560040d44080e060340e186c682004090050a81403c10710210000d08000c1d001c808003008400d8000d00d8842c01c040600e1380031402006510424030341000340c60303134500300040240741e0f04107003180c4201d00b2030040703900d0940e1559050500d82c000c40301040f045000c0d2000308040080080009d0041d81d060241d103010030b0240c207000701c0e0307a0300030711505031003101c800c00c424005103c2404c0a4414140018112030a0480801c40351040ea00280e801d0404219170010500840f080700c0791010604c005d558078004480e2002d00004c050340010381d0036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523223938 1250 523222688 523222691
    0xb0616060b0d050129041b05030601110304090501050103060b031303080705040e04030225060c0f051f0603021c03050304060506011e1707030509070b03190e0c0f0f1003 74
    0x400502d4071800020707803001d0742000c020040c03030200c1c90440c50340d00751480501d40740328003048000c4c00700d14152207401c0c148039600708942a003480d204c5003543c2e21f034800340407941030100003648425144401c00040010700458400480c080d40742000150030303280340c0d40200148138001c1c0100b140c1e401c074a4440301045034041c54140303455103441c8010349103881550040b4800c551490100414503400181c2c1300100e80c0c0b0101c168030209201703054041c000e00d05005100005580b04903c0c4041040d2428a0120030300030300544880d15144d0001c200400504559014803540f07611040043d817818a0440700101548140910301c1c42d17659400803d18800200000c0009030303941d0109682e80d100741c0d00454902c1a41d00d0860440d161070710041e04480c14403050184038030340c5000140034940301e8000c09006004a41c020140181004649841a0001060300756001b00315083c0c600903040602602003040c54403805040895461018840c1c041d00b018813050103040b07601c400341d07c15101d414003201d114605160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523225188 1250 523223938 523223951
    0x7110a0b04270b041d0c041803140c03121803090a06050c0106150c05010b0f060406080703110a110c03010c0813060b100504150c030507060506060c1606030b061606 72
    0x4020010f041c5100c005803c44d00d85800707220309000441d400c2ca18111380b80100e42012910204010546181401211000480b2149007001a00542046410101c148491420700c2007542085140d60000740050802c100c0160034040300a4514176220043c00b1043c002d1342c42c152104012800c1100d41c5c0c46928100480003415840d18030b000c0d80414060721001d43d4107850403080043c020700e0150b441d0340546180d442d200d600d158528020071240d0f076a81d4090300d1141001d1402000740c0d44000010801c03401c0c1529a11000e4240a15000600100d400c42c0c464013449110301002a14100200360414041e030f14003900c0c4000c2d81c0d0000f40e400c1e401401c0c0424030400c40c9492405030041c00b00c41440f55084a58001c038080c00da078110b8003a00070340d00c020301511410703022080100e4080d00741c0000500071031000c210207404940503030080c5511030006848149400741c61404d180c41e280742c1d0940d0f110540302c45c0d00c05200744c80d41402030840f0020f084030b045080c90700c090103c0000889426000380000d81e1010b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523226438 1250 523225188 523225259
    0x20102030712050301180615030b060d060b04090f0c020604021e130b10050a081303090305030a0807180311040e0106210209060d0305070201080c04090207110a0b04 72
    0x1255070031640881c900c00806850b40000d0b00581003805a0803a10415486002401d0414400e001c2140d91745804074100c000000b00c00da00800d2032622041d00100c0811090f507010300e99001d250b00400600c0801e83d03680c1d06d04030010048410b44440700382d0306400c00e014015110790004819400c580c044415a02000b59260310150300742282341241d800c28540405030f650001d4581c01110800301c25603024001038008a0115100c1c42040070350b0700481c0d003020100d140108000064a866482801d1510105859881c0d80f0302d160010380304a8006400142004141c41c1d01c40020035098400751320000d41a4110307518106510815203000307002d0741c3e41e601c2401c0110000d400c10401081c00b41186001c400c01d02842d40d031700741d0100c8816405400d5030b030007190050905042c4801800c0d05907440c5403c15165038011a80c1400250020614190602002c10320b00040d00c018054075200e1040d076900211040207010a039155a440804404418407040001c2d902c172440710046201c20184c40b42c0516a0720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523227688 1250 523226438 523226443
    0x30c010e060409060b19020d120b0607080c060a0f0c050906070809060f0a0801120308040b1503060c21010b030c0d061d06132009060d0504050d18140d020102 69
    0x750f2140030712604190001401081c1c50300284070b41d503500344601480031002041642c0d03a01c800d07596400019240c0010070113190301035018598000300142441d02d0000b580d15003560303a030010f021800c8070350000d00038812001c5080c8102410008014001e1040c1951400080c20074012301c0f9402c6d0003400e0020f00041000840300c121083e00c9002021241c9800031300c040c14506810994061000c1006480086184800588154603455166172415226581c0341d803103010710780014004020040c007141c4824100da030140003642c459a01594880d840381c3c034400110402c0e050070f0180681240380c0d4001400035a1107841181d038800c0721004030966031028460800002c1080d64007000303450350400350352005030981c449028060b40007210016140340303000030b00301c086580c00c0315043c015948152024854404200180640c804020000340c10310705c4460034101611402c40381120641c000e041c0855501d03030086502115040300c2c0b20b50508032030a041500000f84070411960344100030014820341160302c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523228938 1250 523227688 523227697
    0x1b030709090f14030309060106050d090501050f1006050c1903170a020a120b1806030106030609050102190f230c1507020606010203120f0c0f040f09050c0405030c010e06 74
    0xc50810031881d0311074100401d4405106000300c0d902120095600040f500010907039000d409400e02401099192000503241540706c80ea5145030162601d4060b80810741c2803003814440c0e442007000d24030a1825612100d0b66007240c2d00b1110511005201c000c07002c1d13000107100180319040c094004121f03912400c09949849070300415162842c01542080b5514a0907006000f500d9035036100d1450000c000d8080e101a035150f01032a0380c100349015038000356003811160a03a005400900005941501c0b51952000c0d14003d4509032003aa40000740050300d4a01c0244078030850841c0e00c0c00d1300b0030701c641e8203008020300e04003207070f900c403500245d00100554101081180d580d121084202c403116141c601c480c1144660841e00c1e440580900000680594008012500007030710f500a920000c0d91072402c1143c00145c00390980c0f20661003840815081d100d51801807025190204040c081d280c80c110810342900c50003000514061001d20041041d40c4002031382c1c01034428242041e280304030078480442d405016 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523230188 1250 523228938 523228949
    0x80315060f0706090201090f03030e0103110d060602013e0a03021207171f06180f300b0f0406090b15010207080d091509080109151d1b0307 61
    0x50002c0d21004108881d803020342000e10030b0b294a0501d5954035103042034403031903202c09130105040c940a003034998400d5200d01d030303036819440b45c0a08082005001c0c86c1194031541040c80980c0d03584c100141d910a54540c40280c0b0710381e61480c221036000c0c0000d40b080458400c611007061420115103510f043d4040d4042d1411110700302c41c400c61601d008180204010000103d80d03007040c4209010030041e203140d0303040410105403d20b01000f40380c0703082c404403010300000200101c1c02901102c00b180c81c4150302040c000420b2901941c1a49150340c0c60f08040380c1400b00420520045112404c0d4002403404160a0303000599142641c0240c0d140c1c104400a01f24070103005010441100401031028085074500f490040281e08644c030080d1100b2040b070b50740101002042c0468600b002c01c000c1c00b0002c600100c0701a407589808031070315075600c1c051405e40d100c1c4081107030440318400c59440c10404c240304d1030001d21041404c000c0c018130780c403c866031640006031418804980300c202c08601038804000c000c1c002c16 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523231438 1250 523230188 523230217
    0x16030c03050c0a2a140f010e1c1713140d0f060203090f030f0d0504290105010e1f0f0c050f060a0509150c130315050103050708070308031506 62
    0x1070f094a400e200d001c000707140d800e090900d241340740604e070b1180d802050705407245181210511505642000300344801d01d5402030400c02a403000c0700d2192103560300c101c9940b0407120b00c1d8001840e10f180c0542140c0c500e06031465486401d0264802c104803588080c82202c0c07800620940a294410210309402c0f0300c407801030b0120281c4004402004034a074011807041d000441910345240c0380704c41d82c640307034410032049404105081c031040c038222213164010750b00244501c00444888085080211240700010100e24454015000400c417030b5030800c0d0145007590003120040c082650070000075001c4c06c0e1480b060360401c4001204d085115001e55403112078945c1000c201c0300840040109141d55040c11113000401900300310120b02020000070789446c20400a00c0c007503c940d0f654031003141031500001804410f1071028800040410600401802455114040452190b042d420410f20340354040d40001070984c40030504001003810003059a8001c0a102c1481240b40c4100e000104d6900800c6044d04040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523232688 1250 523231438 523231453
    0xc0b0706141006080105010f12050c04051915050901020d11010e0f03070516030c06080703020d0c0f0f230903010b0613060905040c170a090c06170c16030c03050c 71
    0x140301e1102d00900300c403078076681c0c0b80e00e580e200d00044a4070340304606200046074418808003002c0500b604155030109034191481e08146d91600059110552700c04400b500c80c1104c00e0070711407038040d50b100301c4514081c2c1c1800d600c0c0c040c0c1180000d58a06c10f041910013040540800158028401c2d0442e44034000300c402102c0f80d040074036100645035442008100e07028441c1d0100583d907035203d9120141201d4103c060f05902a15000056900e80401042c550415600300705030701000009101314400101141d984a190072120a80600302006064840d020b205040d014030301100581c502040c038a43c9501b912948402000010a001d0a41030301d819074000d00201d448040315206820b19801c07280c1c030f9902d55982c240d0302c00511045640c00315040001405030f0030601100c85281c078000d5000700c1c0700b410000d0130404a44600b000f1001035003160307001505135030300504e15442440344141c0115a84039400d1038101900b10240b0404110000141802014442807080c503004809442e440900e02080d02d000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523233938 1250 523232688 523232701
    0xc030b010806271006030e0708071a0f0f030601020c03010e330c090306100302031009081b010221090c0118090c080a0e0105072118150b0306040c0b070614 68
    0x3108030710b0154200003840e02c0e801f0810501e0000f8264102c50040b005801842e0803d480e18214000c81c0c110301d0710f140c508001401781d108260b0700524680d4000340c90f0300d23200d04102d0300080c140506841f40c40d2203681888841010904040b840c1001c214071a10301902034240c500700c001202d11a4540e205006045204010807000504014040d800c812000d07500307581d40341e03170304036500c0b41e018000650581c0c00320103200c190f003400350b000b0b1400f5070180680f50708144c0c0240e10410350504d0034110b4041c40e500402d050f1450145404507000080358030646429504c0c141200c079a40702d00b16a40c1904003d00303442d0221040c041c01a140000d429040f1060180075802d2002902e9004280c3d0070701c400b01d1400d03c004150080600c2014054000c03640c0729039459524035092103044208070452024541e0381c181c0703021b80b098400034009459109418045414410007a42d408a6042c00006402900705008000002c0c40505114058540c06415107486100a0a044008162543c65400c004409a061000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523235188 1250 523233938 523233961
    0x11a1020010e0615010e0d0804211506050102071703070f030522030519030f0e0301020927090102040308070303090609120e100203190e061204080c010c030b01080627 73
    0x161513500f1380301c00352001c0c4407809119552203491005020b000042c402400302c43c0e009150440c80b81a04503000c1d401e851662202c841520481c0c05840031150380d0181049903503014045003008005a29074112a0103002e5061900c0f80304809000b04030140a00e80311701014001d1050b00c0307403c850500c0754940000f9140c112400703101140000e648a2103001400c908002d4900082c240e0349501d952603101c1280f03419415a003002e000011a5030554080c00060669292101429040c000414000c00700a40194881c65105005040303551781c0e0340104414008a1410300807500416410310b000604600c0700c1c1419001098491001407030b421402601c400207950107801c00045400844401805100341c040c00da81e688501c501c6035800200c0891004685801200001c01030b500281c24607243c4840c060070312101c1c0c0c2d001c0780d00b201d1105004c00c0340709015000f40314104505a036410100030303001c014800600f65680041c191481b8219135040c0784581d00d807082c2801d84207040040c0f62901818030602c00318 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523236438 1250 523235188 523235221
    0xc03070306080c0a0527090d120c050f07031b110915010219240e07090203041509051504060b0117040b010603020c03120702011a1020010e06 62
    0x7400c0c120086003085010070a82e0055500820048a4030310705030900090b004042510b000d515480e403051130340820400d44c5548110301e0300000d049104070031a4080e0403116591848418640f07440000b040982c2c11000306c481112442c00120384070210780c84c0880380054210440e003449001c048405003040f448066103003805c3c0c81156540303003c2d665031141d8641c0040c82c0302510300580c00100598640c0d0507c00601c40c5040c02155812603040d81c113600700101e50781c6021100d014507520019483c40d1007040c03200d20050014000d0039490740c20301e40c4400c201c1b014030115034949555500465800c00ca007c0010403080410941c00074424506814110006d00c04a200e0901280c180400a480f04103d21915440342c2ea1000c18016540d00b0080d044000307412206071480144030805c10744280c0010300a150b1b200b00c0c0c0030b03400882d58501d03406030f400344030340300464050241e07141520244109400c080d000454503443d00394240c1004805e4152405050600c0b515840f80c007a10381407011413a002840c62 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523237688 1250 523236438 523236451
    0x50703030e010816030506063709140f06270901050409170702010c021804020a1505070201030b13021c0c0906080c03150603010b0d0e0d020312060402070b0c03 70
    0x1c0d400c4000d4010344000c0000c4820100840380030600258140c02944903d4204501410702810f0000746856807004c00307200441115103101035004904040400740300da014880740d40c58802005c0340b80003c800402d00ea0347d00daa81c8109101c00d0000703480e4071108240c5040b07518101d0b03040e0f054a8400c41912040c1d00c1150300311b004050260010500e401c0c180a43d0f54100d0740300c00d0683c018102c8021060b45a006144128100101d0752003210140c1e942c0c8201000003107038182e16612030b0400348104142c1c401070746c0c8408a5803000101c50b90140380c008064900e07864082c01d01140001c0400c0000d080303025190250444940b01055500d0f5584140d0b0000d020074200000811529020301000c0d00e041550340728000016a8000008000a0204000d15048401c00702c01441d01040070002400360341090b0403000115a001c14480c40c1c6620324051101041001d0f0081c01c0e001000400080d143d100700404ea200a50652000c100382c8e88885e030440e0032094001c0181d84042c207000c210703030b507081c0e00581d80f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523238938 1250 523237688 523237697
    0x2090307060216091508030301081507020d080c03090f061302040b190501120213030f0b0f01260c03010207050708070803180d02010e04141b130618080a05070303 71
    0x70072200d000248880701d080078814002220341c42c01d01c0c00c030701030150480e03841710095500d41c001620300c80030030185020707010400180c140d039003000e800c0c0384811a000f8100790856011207800720000d80c210703400c55081507880130800d40d40d0b0360b0440014609040f01e018100175104410800913001c88000211051500c00c41c0c00740b00c0c50000000300214420f92906001e0190300d081010440c941c090039820000310384005015080031000701c4000001103495106440d842c0d0010050010864128419035002c0000440708910b5410700032070208000e1070f58903400755481d0303c10403216400c90070841280c0c1d501004000390f648241c81d00d0100d855030164450714029209441000c601c0700c2000c0240d4203514126184881c00200d0401004829030b2481c0099040c41920007a0a65036219405410b048559078121410741d410400d828541004a00d200c81c596105e007400281c040c58a04440c000c11542145000e41041d00e80448580703110f00d00394803510f0140300c2d0000100c20444003082d44000c40e4000e1300c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523240188 1250 523238938 523238953
    0x30b0f010c0b010b03190e060403030f0c0905040507030204030c0b04051206011a0f0705010f050f0114010c120e0a0f03060f02070206070f170c0c102105040305120109020903 76
    0x199684161640c0040502c201d490050028082003000346070302070200080c01070b10b034010011500807180144011409078006408000501d501030007001710261181c6802c115803121400010030404450060314462520f503008101114801d4040d5070195030440040d012140d918004942964400d22446006801101031905000380200d800d40c12179a07240d050951404a0104031421741d4084803503028001e00500055000c0740d07003445081d0006040312030028042c1448004401424816449070214403a00541100b20ba40d014155072812984050602d5045035900425200601040c0c4001d410078041800003e0f09442c0107408011607000e8503040213040c41900403d0103074410480042c0d00b06008008100000d00001d500700441802151000c14035241140400c40580c88810304070b26a0380601c11103041da16240c035452612240320304040c606c6c207802c048070081d802d844a003e4003165548500103000d0600800c100c454510b0240300c1302503a9030710f840520000b900b020b01554024401c400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523241438 1250 523240188 523240219
    0xf120105180130140a02030c03010c02030f07080d020f0d0501050d020a0608091005090a051b090408031003081b0c0d020102211908071202090a121e03030b 68
    0x5210a0586010394408440d90766408043c0000f02c091050b00070122901500c00d9000c114440345044114040e840a01520900390040503d0b1000c0d020312140301e030340b500d68038008041d0008100c84842c92440e0001d03880704081e00389690103004901d01d0050759400090352412415800000b00080103849400300450798131602448801500110020b4000301c0e2070009109070fa0065009681c400c0384007048a52030203170340095109079102621280410780c07004c6035035000c024003070201601820749000d6080052000100040c150f00d030181001c1c0000d10b00202040200f001c0300503410145030440a459030b1254040c44107014202e4240c2c002e40140500482d07140c262422841000c1c01c160141e00400000003d940d000209040d4104210a070780000c104000c1c01921800c5035001c0071005456024180c6007203100030780000d0002d20041c45a5104101e40603841e40c40044c00000e450006200c100705030703012700d888040240c4203200c0340d81c40c4000001d10000c042d410341100240c01802d40350011151480c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523242688 1250 523241438 523241479
    0x50a0c031415060108090c04380604031101020f030724020702031b0406050d0c0312050421061409011a19170313031103210a0f050f120105 61
    0xa15a0740e000b4185400810b24562041d01c1c0d89400480034420341d0300c0301104a002404a03040c1d44040061381c1d8816012609140b0419501c40103001071312034035480095250300007282881140002803074007101c1c0800c074000f139208000320181d00060300222940e610300b900700403605907800e0705200d09014144801008842d800e0003921401640071b00240740060414202c1c500d510200e0030255000380d5149400038581c1d44001c1600e8070a4003850300000b0b0507040d4104143c1001d400e8144000f8800c08000801c0034103038550005c1110b08550030703c200c41c81e94901d40fa90240201010000403031821000b8040c1584041d40140d094000010000000d1034491007401807050025071650341c0025030203020080090700c140000340261014007580e2506040115001d080681a002503e01d001d070300782d890036076081c10000b11900c507911003070600240403240740c0780407e03103e5558034000304a00b020300580c2c10781c01001541c25206014150545880c400421404614030034483c140c8109860307a1780500700c0300304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523243938 1250 523242688 523242703
    0x117070609260c030d0e0306092b05040b040902090301060603051e04141608070e06060712030b0a150905060304020603070f0c0203071d1006120c02030403050a0c0314 73
    0x311581000b000034180c144209070b211082405800f0301811124007084c1c0c0c1c0c01c0c0007480d00d010039602c8840003091044103162800d48010100e071020703444032103a1081402401c07074451a41c408219111081100044220f43d6402164401a01c480c004500803072254030740d170094146100250020042143d0740e400c220180c4006541d89030340440300e41c55030303c507001d8400300300303031784140030355010380e47d0b00c202ca8519854150004507c015142a220307061003c9201801484000c020590305141941410000507100307204c0c500f0020505000543c8201490340203401c62511140c009014541b02070f501d10106480301140c451007000a0000040403c0314030b45607003a04e00468024140b80e04558407020300b510200d020080d50000d21800c106208010b07a010418040500b83c0c502070400f0106885407030b400202c0c0d01070041c0101050700141441496405109009525007415001c509901200020380c110f100700d42018100c0d0055407010350600c03290b0040202160b01c100a201c1e0450070525480d40c03100034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523245188 1250 523243938 523243949
    0x3022701050f063a0c020c01030b01020f16150206041a040206160f06060b070203060a05100f091d0d0c03080601111501080c0a050108041211060117070609 68
    0x14180018801c034100600140340401c4003514091420f0030740034124001d9082003003022030070581c6521046907120720414001d1307100007000051000300705088004c0c0d140c00790207201c00e041541d1890020144d138800c000100383c00201d0400e0743c1840741d095058070614050303030040d84101c01152044031012880025001c2c07003640c0140100d20500350004058003c400701170000d82e804041440020200f43e0001c100800d000d10400e145050002c181c50320100303641d12940542c188010074080600035880210700981e005c0c07000d030000507440d0794101a003030305000c40b508116002c0491030302c0801c05541552000300c02c0000072054200c00910300700c565590703400c1150b1074000140d0801d4480c00182c0200300064100714141081a46131407210042444c1170100382007103080303101000041081c07041c18459403059040555110420509000010b41001d402a0000b45106c081c0d590008003144504880030b01c541003d000c0ea41c495035036113030f030b00200d0b2a44200300e0380501072000d0015103e40146140d00840b0b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523246438 1250 523245188 523245259
    0x90609130e010c180339030308010f23030f0307060e07210b1b0703020a11010519050304050111040303210522060e0303010b071a011a07080918010302 66
    0xe040d80c1e86c426a81d1850b60f521415a03c0014410621003240c0641d0b2141c83c0a5001d044c009901e141070040200d5030690045c100070762820f01c107001401400b9880d03840c6580f0307004504981b100e07410109181425103c90044640004181e4400300402c64000d410302510705012075245076202c078024187c00500084c005943c0c03101d44d01d00000104d0035040e140c0c4c80b03449141e034002c95501400d044906039212442c1113006030429010348003081462040789070858420318196081582c00300382141c2c549410700c503038403d0100100c000b03402c200094000c0840e107100b003c00651101c1d0b607890050500c03a40400e02090070700c110103124849039240d1145522800b21406050b690110200c60001c0e2440000c1c42038a5954403031003404182c41080000b18000c20146c207000356680120f00701242800359140042d084d111003640104a4014480510600000440c0701d142c1e4034076861130140c4141c401c41031041c1e0011841e200039000c1c420f40d580c4040c12a402554101c01c020b0a40300741d01580244ac2283c08e00c01e8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523247688 1250 523246438 523246487
    0x20408060612060f10080a0303020301170a0305040611100e0a0c090b010804020d290601110a0503040501030507110607050307080c070f03080901020f03010e0a0c09030b0606090609130e010c 83
    0x880c0c01e503500c560050a00385e1101c990319101c401c030390b0a0944004064012940000c0100072a42d81c0d241402074000540000d403001404035900103120340300f548180c3e010042038412031541004e09201181c0380d910349040403c0f541d0072615030345856010500c0c0031345410024203c0001da40c1d201c1d0107441c40106050707440d5070f05580d81d9420404400312602c41540c1100884c80c03268519200e601c0d5402d01c68460082960f454a0088001040c140b0201c00304851500b108640760000364002083ea030a8072400d09012455955404c412501001c4d032003101c0c0314912501c014080aa600040194001c00d119942e0070910394950428850600c42c0740001004503907868843c10200e031080c04066008445240058075010691100250503002a0085648402d000c01481945403a030b00c2503a140483c50b0502441c028910340324170240034002031205000c1c40300000c080034980d6a03a001c076213038854010030f00048521101c0108004007a40d20740040150318007090644c007580515845100c10b29032080c03402c1003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523248938 1250 523247688 523247701
    0x30414060a11010e01050105040e0d12020c1f0507091220011209201f03090606092306150a050d02040911072108010b16020406060302040806061206 65
    0x440e0300c803a0101c03003044019400050040402e0158030038401d100300000c10594103120401c41142c1c031003002000c0caa03101480801d403081c2c110040d483c0f110f10380e6400686800803020480c0c1460b0082d000c02c5141480001a0681100f00b42e01060140c0300982c0c0303541c00c15440d07690001d120038610714040e0006420001c000350100c00344442499603081032401255071910001d00c0c000780e507a003004c1103400070f4a60784202c0e203c5440721121640d0300412121070038038491680c1e00c81c03001039080c00300104150311244c20800303200b01c98001c200103142c42c0314100001f0384480b03140905140c01100c43c450f07080126021030a249050740301d070960590303005041031901008007001d461b240c1c0708505010269400f8000062001010321034064481078080c007030380c0c1e182482d1601c005421040c920f5061440038000c0c9071007450303a00503a4181900c01c100380c1c65507101d08411002804c00d807001c100940c080d040c0180440d00c20752540207017003101c66510880c0d02940703c038800c01124007a8080c030500030b60f0060303001509 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523250188 1250 523248938 523248949
    0x60806040c1d0409020604080d030b04020f0901110c090c0a0e041a011b02090a0902120f1c051b0d030c081504090f0c0b07031e02120a02010609020d0b0f03030414 71
    0xa200d40c006000042c041d04c10307400f01c0c07801d070400c2e4032503000c940090602c00b12054060040c1c10740c0308000c450071072518030080d65285160049a140344d04100c0c13640041446500d00300050a60a4001000d880c5145405d615070311499111880d5440040d00003001c415043c1042d0040502e9498144000244141008011034820b07142c2040040c00d000c07202070350070141c1c444c581c465003c3c00034000d01040241e8140140b00e207807514007480031165400410079030500c42c404180a170640d1702c040700b068031a42040303804031098005c00d07240a030020140b00310030000802c001950003000d20981c030144512400c550b02621114411280029100013030321080b038440ca0981e01903090907105a603482c4080d5019190ac44901605030482c4090300b600003000010716030440805100c1c1d21031101d01c2c240150780d11070001d403104001d023602c0036041c4002c00c900028600030340100700039007404141113490b00c11100801000d880d0b455490307401070a1a1a10410f181404404c5030255040000100d0b82855154144407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523251438 1250 523250188 523250237
    0x607080c0f0f0c0624041a03010203100611210703030e0a06020d110403030e10111603061a06041205012d060609060c080c150f01060806040c 62
    0x25003490100112240002000090698400d550340300985070714003e03001da464102d01a180c80640410010003421410203d0221190b0796010b460103d0340d0300c981c000d06841c44245039174841c2d02d035001108022000f040d1a80400440348141d89508d2240013400f0801c0d1260241c4101c1d000d00c03180c40004940c00980b460040080314464035001030030304140c001031070800c0310058046540c175030005014403200c52180102a02e0066400d5401c1c9400d00d5641c014220801362100c1078010810040c0c00f0f100180149c0d0f59680f01b0740f07400140e44007001d903012440d459504034001160340300e10b0684004101c082040d070030090090040c080525050410441c8107561040c010100c9640d9200d030310b20006e0240514800041c2c2a90f446107450389904a0030302000d0301c000d600180200040f07080200102ca600c00181d10b040ba4009030101c2d502e0802e0712515082c48a0a0740c0c1da06111001c4051008400352910080e04a03009965006015100c0d0780070001991194000ca1000410316400c01d11002d55041144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523252688 1250 523251438 523251451
    0x9010f0e120706020d02060105101b03111c170105211c08060f090903040519030501180203100c0e060328060503160321090803030c18010e0102060708 66
    0x40034500c1d889a0722500c0c2c00c0c100e8001600607081801c200d2062038040100d580981400c54441c44500700340b0b0001040e0b80c101840d144a40c00314042c0d80c1080c1130003203000030000f045007001e4981e041c03241205070300d680d40c2200c681c03000140181040d0300072a00e014041810380b50010301802600c25103007459010000101c03803008090144982c49002e00044040390456904203884800c2c3ea4500481004418460659102c0c0900101810070203030000100c1201c040d5642180e00000800200c01050709101c0c881d0402803180d072030600d04119000107507000000092084080780d40303542e0301029810603241240c0008012900100c032401192030584050341e81708c100d949070380000303400c02504141c8842c001040c050f0b034156100c81c14080ca040a100d400b00c1480b00140203001f062540c0c1e00e0110f040e10386042501144c1c2144000d05000380315000c1000140009404c6903201c1c140704000760542c2d448000c0448143c12000b4603c501940104106040724405070081c00c0d40d0b9444c5803040e11603a00007442e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523253938 1250 523252688 523252699
    0x3030c0105010306050f280c090e0f100b040b040302011d03011406010306060905030a0f020315070e030d0306150f02120a090e01060813060b0f04050a2009010f0e 71
    0x554120800d1007142c0c021802410041041e0808802031849040301816880f522890011092060054545c0f50182c460409000003404500f10b0301c1140c211040c2d801070f10180402d2003c2c45011030014480c82e0040180038070320740c42247d503021110040d2040d0311400d120454107100c00c002540c0101030300360140c0b40c142ea80441407807000c1d0000e42110170003c0c43c03840522480301170040d40c2d60305115a20242081d400c0440c001814140080e988880300800100201c2c868140b00045440c00c1c402c0d001c1200300803450fa00380f401c0c14500640100e108907400e900922030103140300310080c8240500380480f550301e41030414510350031004450125401c01100103502c21842079040112116004100c242c24940d42c42003007500b001801c0e0840c000c1a407010b000c000400d028401400c034102440c5c40003550000c2c000038440110070100f42843c41e540481588940b03400100601c444803a0007034000031460300402c1d51400444024182107010700e102c038500003508041a01b8605e80110314400c0c144034000c3c171 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523255188 1250 523253938 523253947
    0x20408061f0b0d18140607020d020c060702040615120c090f050d051218010915020607051b0109060209042f07020a05130603170705060a1e0e070609050a05130b0303 72
    0x2041518005004c0865001c403a003c4c03542400c0809020282d003103107543c0f003e01682105114025514191000a107102d44d030009600070071980c07160300080c000c100c0d129181d0040d03120340001a01c098682400781250b03d0401c1c3c4115885849403080c0f00c1512450341010303901c0b90402c818400b044543c481c0449880c8030741e504821494401e14050201c403040c60031200341e06244040018418101540901030744800a0407040700a900840e800394006050300e090f58503410901c03c00ba00d40114080541d40350352030840008203001154006240d0b210041c3d40c240286110303411001201d02c0e1907101074145101105051450070320100040c2081c5d4001455942c0042d1600c00040f9040ca1200ea4100c2c0c05555500400c10011024100410f4903408644c0c1c40c104800703074540a494540050040e08429a500c040f1144540400460107141090900800402a401e41c1f02560740440b405a600821007080c0006000e151204908040e1031000d04500030ae0380794040c0d400c0141c10034044840d490b020030720 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523256438 1250 523255188 523255211
    0x80f070507021302030703141306022a030901140c0a060b0117100e06030d0c08070309030f060507140c0a020409020102190b07080c0a050a08060f04090501020408061f0b0d 75
    0x2001000c803403c00240165681041382c00501102c0300b0500341e07070750b040c2d0440c00c03c00e500c0386015541060b03c2d00840007682c0c5019051010340c0381d010103403080011103445002c0d8404400000091720440c0020388941c80f01141e5194450854094100c0d416000d078800000c1c000000c4185c0c2045141e1141030501c0c44041604804180d21098200c075040c00310b1494040c2082403d2143c081e55801c41c10903809840c0e294440c0a006068101545007c2c106180008000080500ca1940c0c100115003103040248001c00b5403a007403000d0841654108002030040310b0344c0744800e444074210341c00031102e0001003084001960921019200c0c00e042030307066005488034800c694000c02d02c0303451054032942c0080d00c6440c0c450006011988060401d0794504014094000441c1c4c2101c00c480c4903844600304640e250f03940c4000240745180c0c2e01d0321590014141050b0108110054016000b0740b8400c0f011703608240d03070350650800c0c4003038010350031001007030154000c205903861100105400e0146804c0403544c5000703076 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523257688 1250 523256438 523256449
    0xc06060b0f0d0605010813030e0a0902210105090601021e0102091c0c0801180f020307080f03070c0e090d1103041e0303020606010305010e0106030e010e070e25080f07050702 76
    0x206281c1c940c8541c0003445000b042001e10840e00034200908001c855401c0076049003000001820005050020302140c041c0b45a03201c912400003880d00301000d5545440a4020842e100f00707207540c1515400000700040707101c1c5460501d10740f040c501a401045544080b82410480920398030036110300755420420111a510750124102c0144100440c031b81c22241645403442032021942c1c005e66050b4034000b03c0300d0035202e503441c1c42c2c490310303800004103000220346000007403c009103648003119506c5883c08003100c1640100140a0040c000d251000c1e040d82e032100088405001151050050f4001c0317506040041c0c040c40c00c011483d200401182e0138180c480f446888891100e4004111004405c02e003041019070400807158007103000e01e424401545040202140c13442d041c000c40c0d0034035803162202d082c140740952040c21901d01d124116401ca582e208010510100709039500c4060f14001c50301d0390303080b01c1c0b040c14501c2001042e43d9201616950045203041141c8007400b00010030008109000140e941e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523258938 1250 523257688 523257697
    0x20a090c05070213020408060c090402160c080f1203060607032318010528021207060b210c011d04050405010b010f0e0a03121b05030406030c030605030c010c06060b 72
    0x154072201e07035501050040080c05200410101d80c030b00c0c0100014070070f803d8040750440d041521954525210b0046800080280c0121000303041d001e260306841d1418000642c003d075084803c000d040d64030307420040d80442d40718205025100c458002c100301061309404c0400080c00d4041c06858441003850080d94107a101c01e08a100411a007500802d40d081c0c81c09840c031070950414000d00700549080400002c01090205410107042e03031040310010455030b0b500a1042c0b183d404101110144d5803503ca140500040159032031442c018200440e02181ea2040380e803c0041000d212070007090074811000c01164120045070035101c11b540380e02c1c044600c81c5c445005031070186204100118140384860001841d00c03140040300300c10000360f4420081030382c82d40c4585034140ca42110900100759600c660030703a80c0320065210040f550003035600d10780074024044003500035660590390600c80401441000c40607200c990151961607003280030f031465158060365400c0042c0d4415000400d00f65907404154086030030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523260188 1250 523258938 523258961
    0x4060b061206011706011b03030f0207031d040605060d020705031c050a0c091206180f030801090f09020a15120c0207030b09031201050613080a03210903020c010507020a09 75
    0xd0040c0040b41da0440709001c4072010503822203c2901d4a24002014500e0202240780c02d5a0120205000d0610a4001d84d2145448800c03d6598851920340141191555004a0b200402e81c51802001e440d082c0550320880340014142c9082c4002c40c400d48009500c60314085a503844200050480c4c44000c265120715a20001000201031510900034829191803003542c200300a81d00c00d05000d40300000d9055a01e5540210707000034139501e800c49003504001c0100029100102c81c5e960300302090340c05100135058604480d41401041e17030741510081030f9040303214000d6024048000911040c0759a12090355400d04030300e082e0400710003000c20728044506100d02080107030800311040c000c0c401d9180c03284e600051884015494400903c640e44540390301802040e109540001d0303202015210029410054007154040e100e01101c00c0c50050010b0400c15680c444022481d200080410400e02c9161380098054010300161800c03400112402c2d800741078100d0380300c00c02240100c0c20322814072420b07440344c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523261438 1250 523260188 523260217
    0x220b030606181305160306031203020d09020901030506160504230303070209010311120a051b06040305030a120b03010212010e0a140a02120c070c050607060207121806030e0a0b04060b06 81
    0x805c0202101076140c6000030005240c01d059080001841c14401540c0040c1c0f603240c016210f000002c0d205001d00321284002c1e41c0403255100100c28002c010441902030100c4801180320180c03555020f60703650143c1c1c421780c09443d05078660078030080040c040d08030344a1001416680740c8455607001a0039100281c0080d01d5001641d55118031030300f08200202440c5150310018014a0ba0b01d0780c80ea6603840c01c6684400e1264640c1c1a40130141d11220281e070040c56000090340e4884003d200028006030200c500c21810a050404c891454107041c800c680d80415413a000e000c8581c01c022842c40100b402a15040a143d902c00d1600c00405004844c5070089060b0040035035034610380c3c1c1050400e40c1c0060110f826180b8200201c0f030006550010f10811510240c0e001c42c0c440082c1d00f8114000e0007014400703010781c000c0503803100301194424070402c003560185803601c0000351194400c80440d80840302c09203265200d41c25440100d0b500105060b4060312400b008a00c008160303001c5080d81d00003003050030219 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523262688 1250 523261438 523261441
    0x904051e040606170102040b0322020d050102030a0c1b03080702030c0f07030c090e03030a0902030a080d2f0421050708070e09010b01200c100203220b030606181305 72
    0x24600c0c030b4007149055180001c1d0705003401c041c00c223407041c8030207041c1d00e51140c1e0744c400381e9016504070030381b0107002a0000e1010710700180c00e0030700c0d0307000c0c3d40203c2300c020240749003100140c0c0542c015140418241030150040b05075140e1503900392101d001c00752000c03003584018072034080b0602041064003480c2c400f5101402c08203103540f4060b114504d8941012000300e08010b2042007034007000003a01d5126090610200d503480c56030010034142010204c0c00b91038500c00007103803201d0f400f035504010b5509025080d07854110712030607000c241c071010720714042030824000c01c4200410310310082c4100c4040d040700d1000748000e5056642c0c500d001555400580d00740c2044000b0030a90a01c02c481c260701080500090005000340c034002020180c0940e40d1804600a003c03650038001002c10000e94036680151600f040c2d400c0c8042d010b9501d0300088000644245190341d11001c00070758410007811280d400040c0e900310f071120805c0010030f4103c10f00c00c030b002e40c0c00d0018240075980ca80343c5c2226620128030b00010607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523263938 1250 523262688 523262699
    0x715020313080307180e060d15061d0f0610080a1a06030117060c09030706050a0e0a060e040b030a23120409020901030e06060108040201051e3009030904051e040606 72
    0x40b90719030384910301914404041150b148c40d01000e840c0400c1c1d010b15404408594040614003c00c4a500228190354401c000c4c0c100030503403003080d01d001d010041b0780078682e99034550400008001640c154800115070748003050742010a078000244440c8070080c1080b00701126000b144c240c1e04240c0c046403c4a056099038880500c080c896160440c901c525401d292120207000b1a660315507920500303003081400545858105d00c503070b1145055280081c00195070a544490042c03040001aa0703161103180b0345045d604d181e10300003483d00011a40029100c4000d09112400d601c00c02d03420b464004d09024812450b10030010120040000e0044450016114013001000604481580e08445010b511400074440700b0f1780c21101c4141c0c840e034240380c01581c0324502d01e0300305e80350010914190b07980400440c40c1c00180c9040b481200040782d07480c03a01d03070320701078611106035002c0400d032070f60ba106800400020b42c0908154000c0c0f54071400324070b07141c440161842844204850100c0342500c07015543d400904c039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523265188 1250 523263938 523263977
    0x100b0309010c03060b2d0f0c1c11100f0209031e0c010f020606040b011101380d060209010c0c0b0a020d0513050409051c170c0715020313080307 63
    0x5020040c428504114002000b00c611190494100d4200c0300310242c000c8020341c0600448043c547d14100391a100c11403000d41c941d40301c00724000400110740c910100203400d442407a5200309040c0c10030003404004510484a402480203e400c242442d808001501198030204042480380e0030401280060b91941e081030750501e948620607034100305200000c1600580c2c005400307034111404031000a1007031440801030710040c0308150003111075424100000e880031104143d40c6402040c440c1480f1b2803a5008020b03108100540c03542c1584403804084250200300c0c0c9034060180a4410305000e40c2c0141c0030f460340080506164002d860040c400900d200c0c00c282c1c184601504040c1c1410070500382004580954030100c0345000d1240140c0e507c1c190740007801070410a60721240c0d40c40500d40710320501c58000500042c44140e80d020011110000705801c200b01c142101c0ca0030307400850303800300620807040c80702c06580702078403071441ca510010710480816840c0c0021405442640c540700140c100d207179400403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523266438 1250 523265188 523265201
    0x120d030506010203070f030f0e09090c0306060f01020d12020405090a1b020706020c0f040f050a02030106090f030302060a05090a15051f03020901030201141e0909090a0f0b100b0309010c03 82
    0x141150024000200007805e81c0911b07000655142c14010500010f0003401c80709019111042c0760304c50a01d030305100e261280454620443e15040d01961056038401003400f01340b1025492250040c0e212505903004140b00d4982001e900243c0140580362654a80008400550903101044072039900c0020301e204c0c40c0c55070f820313829a0aa90001d070080901e8403102075191090501c0042c025440800c80c180e4a40d07495200030748801d4816010401c504008402c54001d410900a407408601d6048000c28074040303070096201101c1c0e0650040040d56240c1c21844064000540912402d10441d50803100003000c481e4a10703072000340041c001506207001e0f003442c503d2140d88c00904066060100781480581c644541e654192a028248250103280400da10f20903071041e000e03d22200f0b0600ba45000b00e9190500c0204000d81c0c044030401700c503403030f8090200c0d15440c0011004106040170703041e01e03001402c1d85a0307050b440b00207020703040700565882c5d60003c510750048800c601180d644224040c3c0b4650907102d8030f07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523267688 1250 523266438 523266451
    0x1c060504052a0306040e0115080c03071802090f030d0c0b0c0a02031602270610050c0a0213110a03020d141b03041112031b032b0605120d0305 62
    0x507482c0011015103600d0400350307981030310904030000000030001d880d0380e00b0800440070024020040c0c2803c02030049004005030140003141d0240341c0c4800554030340000c1134020f030f44030312a15414525608100000030b46c410200a500800540c8001d006560f091182113014100b649400c01100d82c02c2c5440340c0059401405100c2803035007071101d080a15800030942d9400c0800f4210205408800d00000716410805103403007010850101070402c0710040d00100340c0c0111815074103412003407001402660702d0b0003480c00010240e408206040058540300d6121000040440d4001681401c0082d880c200b43d40301a90402c0840c2c1c00145c44901030300e00d8828000080300340004551181440c080740d0100c00301c1042c8001d071901010011500344010307000b20400329140107120b00d041070418015262243c00c608035064030f5100000600c0024000442128030081e0a5001c240350058611415540003200f0400c115160b50345440224680d1514858030240704c1d100c0000b82490700c03554000800742ca0004100c13 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523268938 1250 523267688 523267711
    0x30e03060a0e03250507080d0e0a030317060a0b03130c1203020309090a0f0c200d05090121020f070b0a090206030103020d06140f07020111031311061c06050405 70
    0x500d448440c0030040e2103004040444000b4181c05000913410001c2802d04040e04030b020750140020254400524200a00140d480d200c000301d58800812441c0c1c0007620014000c9803c3c100d10341e445102084460398441d00050908007819140c14403854560000c40ba00c14000764088a180103100d1943c4028005000c48202440c0428081c1c0d4000d40b0f0f0701503c01c15a00810100020880103039107a08080d01124801c48100100840340c24010042d8410400b4400c40d1820503009900404010840d0b1844180c103072592860508800c0044521031145945180c401c032000c080781003480c950380000e1075907060700601c860300c496107414000e01001014000c050076520703010803000141c592605032811a501240c8a8001446c1c03428804080d14040000010b1141c0300c2080004103900408000c0c040c1d01e082d4000c00c80f40c003440c1ca0010152005a40b5030001c0c24482c060003000601d004c1e0300780324502d80940301a04150708035903070328a590b80c19850344d409161609018045070400f0303c03407140d011400710103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523270188 1250 523268938 523268951
    0x70c06020718020f0a03090c0305010905010906180b01051521041b081207170d0e01050604060e160c080d060819020d02010f0e12010504020a0b210919030e03060a 71
    0x40222003849502d0314034086c15180d458410a00400c0190180110f800a009002d101c48920b011270090984c0c01048400da49001115044030444020710100164000c0507455541d00704002c120101e0400713103880e8560001040b1036410305c0718176004d64108003850481890a4101498081c413041d410310000b0054084a82c004c000007100092a961200120343c0260b507107010606008210321580e800c296456500003da00940351450b034031180280500758000c02071512504204001d581d036504c52031440c0412400031401c0501e481c45400141d0105040c480503201d030554800c44c290f04101d0900400c582e6960042040041c203010300f400001030700702c215030403040e03da0000d00e0000110b00c0190411081e824403020300c5000d41c0f0b462000f908000c01440403c4002c480e041d0103802c0499080380201c7c8c500f0340008502c05448140c070507038030302e44843c1c01240804410120b50910003e203800c0540c4a200340201c3c060300c00307100b00c41406007c1c0d0341c0e00250b0f081c20810f0515010000d8000700c01301e8035000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523271438 1250 523270188 523270207
    0x705190210080c0f031303030b040612060b0f030706050a080a0b10030911031c1202120c03040c03060203040f0605092a0102100c0c020910050a0302060f070c0602071802 74
    0x3112800307900181004000c80c1c030b403540041d0701c500445054401d088400800d1050100c1d004440545040c070079641840241d49541c03e200a81e0341134480d4400a041501140b030000d40b03950031540d60600003030b2803000c1103c840d00c0000c0ca003041d10f03442140450400650001215400826254030808488090003643d10038004140b80948039070440c0e0030590350307400110030091074014a0040284c002c5c100c9001c0f01314000031811503880071480302c010550800d42000600c03624001d0741c006040c02d000d03090f419503510945843c15440104112949180c0540200000e200351000c2d50090f80282c1d5104d13010f10b21813402c00e00b103d00c064010aca183c0e2240d092aa40c0c04140018881080404500715120700380140c010b0340380508aa10030701000d0b080c604d50b415040d13804440c800a050084541c2d80f00340c0c65409100c94007400764010f094002402680910250900f42c000381240d42c804082d003490070546807a0301c09180a1a0418001600004e03010401500000b007512841400d0725402c40c900003002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523272688 1250 523271438 523271449
    0xf0b0a09030807030509011d06090706020c0904110d050109060207020f031504060c0905060304060c0f0c120302250b01150e0d02120a020d0606090f0b01020d1d1507051902 75
    0x8000e01d00701521080052103411b4290032115002110f00c11410221802c041c416840300d0702200e52550911036008009a070030720008a1421408000c0c1102c0080d44443e12141c407152802a401c076086000c40400c2d00000300241300f0b29061a014000c016111341c014030402c03004103010084141f1981c00300c1001000703003041401640c1c07c26031120f00003c91041c014030030b480800030b552101c0c0e48980003004210a2041d50707085001c0b1000c2e16503400520b1100d4040582c1d22087d80400a032401c1007100034901085d010754002c10200180c040301d62805145080c5c41030b0601001d003000c60b42c05100000420a11101144441a808042c104840c0000030b003c0440d4081e001d107200a80300e40b0484542c0b00c0300707110503c6100d80c11500500103d4030f10041e400c220780680fa50388103001c06146051f005900000740d9129503040404160301500400401e044200c5940c5800381c2605140d1041c0d40f03041c2003d0365840d11800030f01c0e031038150041c1c6a00550a0150407c00080c1c20402d101c5444030401c00180e848 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523273938 1250 523272688 523272691
    0xe0a140108281e050c03010608011a031c080705040b040611070e130b060d0b1003110a050d110a1502100f09080304023703051009030e2205040f0b0a090308 68
    0x150301e0b52003e88050b508200d45898107859506030103500c0c0c6031002c25400419086024041c0c020f9184a80490120040c15904c1c03401c4440a90428000c2e401415068402c034445034000038207103041c5050940310a1140c1050748650310600200d042d06100304007103502070128400038819600050003500d002241c8149401c0c4d41f00c00180710b8810b030f070005802640c41c0ca01000c00d85420108140580c1780141d07545a00c826a4002980c4022100105100380c0c50034a001030280d400103030074401d40c11100e0780c0d6481e280124101940d4440c0104a011514048089c0403181040c495401020800c449503125021076010702600c10180d030030000140701080d01003088036005641580c83c0c018010304090741495441451a5400c0c00303c00f01c0c0004d454810b950f05280003920b0040c010343d040b41d103c590b410b0040b1001c0c2d1900901049440740201c1080ca03060642155090010b862100088080018101115000c41c1c0403100400103104d0301c01404450701d5810b03807100001d4030812184550382c4016229040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523275188 1250 523273938 523273973
    0x6090c0706060f120506010e13030f0309021203030703060b0301050a051203071509020a170d0f1b060e0c18010e04080d090b0403120b01090e0a14010828 67
    0xa00c55080200035880700c0010300c00c5071040d16060351240410041c03181e1542c02915103114036400800c1807000340309058042c1c003128180384c08a03e5956000c0c1c1c0d0642148500c030341419614110300000d07032036068a01401102a201441d0f40e40f40054014048401c00d4200d820380410a2005002c0c980f51540340e4000d6800440300340e0840c0300300428080c514407441038010a0000c0c0700e50302c9043c00300160000c10f4140e200303c6484012944820401700c1004200c401c030030290f07001904040c11140901141e00c1c0e480303454940801030b120000c04010384d1108400d07088800941d203040088540100b40202e08070310000300d0b4510510a0390520306010800c040c05070010812210f00840d00b0400204100d40c49001009418032200c5a44d04101e80d00d41400c40d015004070f5512800c81036100401e1084090b00031058503545d5000d420400c0c891329402c402007042c010309603070390000e80f9031080c08180c45009202110040c13101c2092401c030024400e05035109219a4045a4203000010f50b081c0c0c502c03c40000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523276438 1250 523275188 523275211
    0x20f0c130509010e12040311221a03010c12150501050708090316030818040501050d0b06060d020c060702161401081302150403020406050303030f0c0a121a01030509060609 75
    0x200d80d24040303401407045040394600362013950001c017007013080500070b4000c90b80074025104824100009100202000c0722222200d00705542108407511040d5005204e043c25844002c904c850070035010a0846102610050208180303005045442d5202e024510490034245040c4044519101c00688180110000104000070226003a50305880c1040121004495030b0785a0200d40e540e800c0c0301c000b43e48882140c44000726107402010080c00c0c0307802581d048400103850303820050419142c032091503002600041e4000c1003084925078100803400900445d0440fa805840796003081c040c06480c05200d80003240f0901840c010030007a00701a001c1510740c0103c01e00340540e03582d50b0a5842400402d074640000c1d8440c0c4d840c07080380042d100342e8003e00180c1b8401e480070400c141d140c10803d59207010032506540c080e04003500246085003080040d1815050509001209030f480c0075401c0181c0d05120841001500002a81c402d03544e890300a140c0c002402c3c0d80076254901744180801c02101c4002c06040e51b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523277688 1250 523276438 523276441
    0xf0d1a0405150f010333020a020a0c0803041809080a0e0d12020d0f0207140f01090801060e06100513032405011203021c020307060506150a080403020f0c1305 69
    0x400107010003004100b010701d24a800b40b83c621810702801c402800152034002c0c144441d408409141c0d02510894400d00c0980020080e0348030850780650b11030f0140030304500a4400240014803d400d0410103840180042e5880b5070900300d6000d03191100c07a0b04440514281b03807441e00412000d40441c1c9a114203483d10710344040740000031500c1b69001e054001d011103018140c0c8404d0550203d08002480c640303a0b2090844042914100ea80d140140a0100d2840c80302e0740949031450040480c4c8030300c19060419444c195500c00d80c2c5401c40e0310540c0840107000e100000c0020b1840c0c6482181c45408460403c541011300741d08100720319116500005045090055044000300b10046000350078000c50f0f8014031081d0303110448031201c06c21080048000d4450440411541040750f5a02511440d480d4002d60070100340d034403900c002d040080c1c10fa80e0040410381c0700540e4202c0c07410007020400d8403901c84070302c1070425280091511502c0c00c0c810449800c0540c100302c01c0d603501866110000c07006030012955 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523278938 1250 523277688 523277693
    0x90403050f0c01090605010803070201140d0b131401050105040b0d0b060d0c0c02190e070318020904110901050303030106020a0807080c1609060902030f0601030c02011116020f0d1a04 80
    0xa9109039009440001070114222641c0b5105420054503207114060a00c400e03641d940d810341d9207029614009003c55803500e4003034401c4100e00c0c040d01c0d80e00c034a0700b4040340f03401d100404101c1060040f000301510710307203882c680c0c3d14504510003c1c50040100307207443c40c5414a0582622031900a075151011500d03180c4e03058030503613500ca100b503940e0800800390410061846041c058030101201307104a0081e003150500071100740d80d1060a008480c42084001410341d0b4100044000f0412000f030300c0040d80030a0240c40142c3c80c0c018150388141d04c04c100d41007402c140072040100c03e290580c8030b03e100782c0c0100014051103501280620300c103a0310005144d02c41072070307151005850141120410f0341d031142c101000200c440480c0c1c19000c80390350440070046036442c2c040d0401a84011550404051490000324803103501c40d500c20203803a105403000190808250441101c554030109288028a0780241c00360f0071340c80c01061003030441ea000c40318410144070980d251040140035a0078840840f032940b00040c00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523280188 1250 523278938 523278947
    0x901050306180c04050306010e040f0f030207320a0b0930060f0c04050901170a050607030c020c0111120708070b070819050403090504020d0f0e03040509090d0806090403 74
    0x80a4588080e40802481c200c1903e800c99000340c81100d20a1051400003d031603503003c0e0320203009982080100c210b050b400c0d00c54000f20781038500110210f100c0e02c0800a9840d6107140051900e80404040d0500d4043c8141071044064011040340d00c980c078045401c1240d000b420b02255030705031055405401070003201d40e51815091074500403603aa414100174600d200340e0080b034042d210b0f0602998000c15611860290242d6000d203009242d0421050b41c018480c03816241c0c0b081a500c8010b00407281c86036120798406042102c140ca898000c03c2d07d0714003401c1c105070140700c0b041840e40c007803810302e0b4424252810f5a90b1503600507081c24007058001407403c1400b0b144422107500d0380d0030501c10180c5090400c0002c1c00e40c001140c6500300040c0d0001c94500c89019801424019a003527511007040038140b004110003580018580b80c0c1e003982e191149200301c016802a468200c0e40e00001e1070b1500d1418091000d8070034004e002001640184001c115503980000c5a1500b00b18241c84d9011b47e40c0e44e518090301e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 523281438 1250 523280188 523280209
    0x601110d0e150f0a0305071b030309210804020109120b060f03031209071a18040b1906020f061e1503070918140601060c060509010612030203040609060f050901050306 73
    0x45801d03200040704542d85101c10000e000203100791750100251396421008403074008202ca1142c01c20b100a81c00350001c00d11903000b4030300c0107001e40040400c4102c010b4003451040c1c0c82c61540004100c500c2c040009543c3c0150700000200390900014040c1e20140c1d45520040714001c0916114800b45480d080c11528100140c641000907220080b026003080d9044030342d03c41107440740860b04031003541085030f01c40303240f420341d034081400d111076000c2d0007035400800c800303000700804564004100d40444a03d0f480454000d02c0203210680182070a19109844c0314240580107200780ea1110b440d2100b01050750f00030420720f0303104404400e104030444900d0002303810301130f0341e600034064541008155058480d2030360164108034440e80c0c3c250041040d070384080e5100c007003d1003010041060500c03100003003001600b0007503020004900008803503403207900103080c03003801c0081136006130300200d000d0040c95042145200544401c3c2040519402c404800030000d2040030009410800080041681600d030f000ea8034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 523282688 1250 523281438 523281469
    0x105161703011e06020c09150d0213020a0e030c010c12050d02040b041502060105060d11040806041a0a05010503030306040f180302010f11031b070302070308070303060501080601110d0e 81
    0x907a034a595460500720b920034101c0329001421848000040c025000240360740ca100406844244560b0340d5030041d03110061810021030f0071440122501d00144d803550102e1080710030400c00141c40b41d840c41c6004065107502d4142a002c0d80c080c0d5968452aa0050b07a0060704580c00903916409505042d0216107501600d000c1c001d941d4004140440d220421102520075590440d0340c2d06552280c2c1001265602d5003803080b190400020072045001c035402d40c02c0300800d581484000c51400d552400d14078907040040b6001d881c1d1200303882d10f0024508825203919040501448140159414003000945034400036200901c91175484e1500c444504080d00103070311070004c5141c09a503d040504010380606001d481c0403e100b45042400c503e8215400180c83c0500c1da519601030368103aa440040c003c41e482400306030305612590b640040014018001000c01f1072107507601185a5141c17000140c03640c24050507441c140604820044045800000c041ea100b0b034251908030010010000401d402000306842c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 523283938 1250 523282688 523282733
    0xc2103161d09042a06080c070c0b031314030a0e0a031a041a070c020406060908062e090b090109020901050304030e04060803040308181005040b1804060e07030608010506010516 77
    0x40c04c060128280c4074400301c8105450381d40d09503880c3d94480c4520b22450074002c5c00c401589005024018414001e15402804400250001c03162074443c000020045003081d0b1066000281003004140e00c42d0f60355100d00302c150350b42100c143c03c40e5501500c24440242d600e01001d003000001341401301001e108001c001d000f00046403142810074008004005029050b4000c9013400000507420740300e64200c504403103600300a82840c0c1c035000d2040ca0009441596100c0300e1070f2180b0707071007910955503005900030420f82600042114110040c0003034424143d015810311841448030b403005907044000c895016074546001541c003405000024010000758105031100d00c400306020041045500c000c0c4950900d010340c048035481140c0400c050344000100480000f003090100b0020349090030301620038030304002382d008501c41090300890201e07035440d88103001ca002c0020038454040c2e01031003104040c2403614005c0c0030501d0031400103030540c8658899811302065402c1800184840c0e49001c0000c510305800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 523285188 1250 523283938 523283993
    0x403050f160204141302010e040906060b04080c010504050a030212101d06060d020d08070816060207030e0d030504140406032015041a0c2103161d0904 66
    0x100e00c100c4481904a00591400060001da08a10840c492040315000c1d1200c003205c019600449030300981d0070385035402a450b05110310024004d40184805454079030707440b80c2c640d49050707040ea15046002d00102e041c01002c110501881d2148110181034940540e0141c2d0451100e036100c80c40c107030139003440d040803074074141100d244c8000d1048250f850485100c111001ca460b4101040300106c0d4200c002036014020400300ba0008000c0009051183e01440341e040c1421003401040709882e50a400440760a940022040b0425401041c0760708104001d88400300d0b84030690f60041e00720b114074000c3d003100b210300c030305009000d5860750402009142d0001803100c02e00d07401c0d00c84041d40396440c0b20003481414100d0781c610401c91001c050301c0403106008402d444800d02c42841441c15406488820000d02604151a08400040d03a40c2100500038a0015581c0e240498904040380b03204c0c013501040080140f52010780390032201c0700c1c40e6032480403902d803000e984030383c41c045c0c0360400c0f04031805102c1c256104c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 523286438 1250 523285188 523285207
    0x21206220626030906031b1201120c0608240a0807090207060501122d080c07030b070f02030930010b0a0b0f1206010e040e0115090c05070b0403050f 65
    0x1240c030b03000035204800003070060b28564891a00c80c001c5000c425080182800007481800c01c41c080c07101004090340f0003904e40030b0800e610340b03840e42090f044000c01e01c642000f440100b010150804004088034070340b541341402c5c405424940541840c20b5580c002001c41c0b00892643e85100c90b40c401440710a00302c90f00d507035a403031000340607402c400d1041c1c907260f26104c000919044450702c00070076590302590401e210822002417009030380e4205111551040e54500b0000001d004200a004000c0300500400c1c50301c1c55450312200c2884000c211004009030803101445954000050380c1e10b43e441101d02519021003060404916a001650862020200b1180d032a5500044d803120fa045182030717034640c000303e86803c0100d60501c0798100303000d0010401c10002a804501c1c0c510140c00510516084001400140000d01921203489058000c0d03595501c0c0300740d900301001388074001030210b840c050212280b074a1010303005005e540f2002d40b10034084400142014880c00460724040e550148090312144102e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 523287688 1250 523286438 523286459
    0x10e010518010207020a030303021c06031b090606020a081b0715080f040b040210031b1d09040b0c030705090a0611100b0f0d03020a08120702060a0212062206 69
    0x507180220031030940351402182100c1802201e000d01e80184c5103840e2245141d40840080d80582681940040b00529032003400b40701d805000c1c0150300525403c0220748441d01c1c000074a01c1d042d030010700b120389801c000300700051300810800c08054000c003813203031a160171a90308104200d001c0480b4549014158021840700c1000380b814101c030903265a44d0000d980c440e02000144a0182d8015002024810005005181104041411030724603d004908081100903000f0810080c598000100700000e04540040c107d007980c0801040040701c40c030b00242000c3d03d5088181e20040c0501c00014000800200010f0090303084900011001d0108070180782d85030745c000c0c8400c148102d245440d001c1d400800601c10014040c03001c3c5071500a1250030b03443c58010800040580300001201903000d0101400c1c0815059005001400d5015400300d10524020710001d080c05c1005240c0550544180440400035120a401c81da01c40e200392501d40386803e6032080c0d5158661402c01794041c00d41020300105500f00003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 523288938 1250 523287688 523287691
    0xb07110324100503030403080f0c0a1113110f0a020f0328020303271e03040305010b030615010f140307020c0f040c0c0602091f020303091501140d0c08010e0105 70
    0xd114014640d0b894112101010010620800d60703d64002e00051010803454130040021241c2222054a04154041c0c0c0c0d034284180ca2800341c4480c1a85560004070f0f090030100b48100900210040108003620104180140202c0b00ea130000f0f4100440c0504081d8000c00c0140e603c0251101100e4030b03402036018084541969030442c6242013003903902090406e0002064a0240c58900b140c0342094a8245a4009284030800035070054480e02d00314100c41e6445403031501000036001301950751103056007052420346900c000301c140694800e80410001c030070044290030390807009203480b00c0180c2e045181118812080c501c418500e903070010138045401e4002800700e5003404180c070b0442d10080c4240410045881300982000443d540c0300000c40040e8455000348100035000b0100c04c0c130140d6108e0038864241c3d40220080141c1e0000007440b40c038000800140f03030703504004051200d056042c0300341250315000e50b98080f8017800c405c6a0140030400c1e07844c4150007030081030b0000c010b07401214040c240a001e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 523290188 1250 523288938 523288993
    0xb18130c09050f030c04090c050a030c08010e0303220302010209041418030405150c0313030b0406050a0207020f0f150a180f031a0c0702150319150b071103 68
    0x658600040314140b0354490403d66200801520f040003808050101030030b0440011110803251100118041d65082c044002a6000746c1011101508203c408e0f07003195a4400002140c0d4014800c005048540f0710005001070386041c185604500c4074503040c0d029003c3d4031401d541c424107203140c5884000c004490035202d103140c24040ca0b211020f4030252508c5e40310314065160000b41c12107080043c4030003034000704040341006003201d10b84080d4400d5010b4285084e0002c4501050027010710092114a000c0c283e0401001401186040450390001e00202240e003103103401400326401d003408507501c08a0b5041b0703640201d4a42540e03203526020091060314280c3d480c1c03e44035900d8501040f841226032a40c003c0d6948400820f001c0b044158501c9041302000300300090700c41040141d100142c940d000d0903106142030f40e0b560342e1a4280004424001480e84000d01c10651030403600c0401901a800d0000441c1c0b85810b9443e079500300d9061200c6209400b4000325014130501849803296522400c0030681041c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 523291438 1250 523290188 523290197
    0xa0302131418010b19090e0702010e060a06050604180b090109020c0d02120301060311070c030308061c0b0a050604020417060a05061009150504081f061508010b18130c 73
    0x4080030b20401c10301003800740b0f00d06064103120400d4000010109030340000c20074101040c4860344c981c2e0b101e52880080783c40c00b0041c2d440f03280101404808214254019012040030701038503080c100031860318007480c864420b0340600d00c101c0c0e459800060b48008003c1c4800b508004035981c40300c038400c0103580544109141031090007101c846841c40031034000303268500d925401d4a9640b0b030240403409041c0d07400342c5a9018900300915000584102c888600030340c031903110f0a84500d400303c100b04402d58000883d43d031201e10a464240010644165298890070300c02000030302d52500781c0418000d01883d0480342240c4003141200107500d80000f074443c1304800a280511155545038148100706208110980106032002400c0c048607242c20b4026040c65410b240641c03d0a44e180100c52070000ea8048440c2d08800c094041c541d0000d16005100243ca03c440e2480742000c0309444c010600e810520030a60502e002051b4024a8824060300807032884c801031400c0b00b0142c07942807250040c115180c00f41c0216 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 523292688 1250 523291438 523291459
    0xf030b030d0e10020114271615090b19020f2e0e0a060b0f040f0902090a050c0d0504060f0e15100f090921090f0b041a0a03021314 57
    0x25105002d980341d081c1b036000d8141c1140c0c4440701078a072822500401844410a20303040c3c1e80c0c0c4140b0420003680c0345220f064501c0805071802100580c0007812504410401c420320340140808040380c0121224200d448004203050700f48850100c0c20329001c07604222550050013040307a212041d0404160101140c00c0308808000c2404c1d500d01c0c01c456014004080541151200354042842a44592500607014111036500308000001604807080c5c032103040d45140e1703a01c0700003040d428805251644202e510070308002500b01018400554010040d080f840c09440b03200280800c0b20301c1e0420310360034000000510003441100d04070798645a8030744400d0850900c0c2c80009130807900c080c0074801110524080754002d00e040150002c05000446010b03200080100550f00d10281c900079040c3c202011550742150741418000b484450310400d0384203500d2120180401e00407100004a407071541e003280000c942d66404200341c15000703030040704002d140c11503220308005482cac400290301c440340708400c6032010f441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 523293938 1250 523292688 523292719
    0x6090914070207050d1b0b0d0b04140112031803050309120c0f10170c0913200307020a06060807090c02030309060402060d060807090218010f0f0f030b030d0e 69
    0x1a190101d55507801a44070100400890405c00d203000b050724040d0100582e05156048040a0000241c0c442030041200258100301103000b4400c0c50511a0b0880381405900d4102d08120710002d01802604620b251142c0d0032400c050003015134041400e007040107440101d0780c03070800310b071a034210f960501d0040318441c0d280c0c140711030046800708000380000d02007000c040580742840b008804400720f050600c00035002c0341046009006106110b1420300900b00d5460f0650401d11090190180c0040d103402c0c10640c2412540510b6283d0882200b0210b00d1642c0b65964481c0032403820a26203005055a840c1c00b00101c4c4001010690b03105172002208140400038007610100d03520b00c01100c0c4100c294201c1c00110740103152250041c0484803520501185440d1950010360404911380c0c030140355646e0010b6000d000190805440700c2c5041d003421300405580701c905018040007086170601c0c04010080c0c1d103805040340603902441d034030341e006422140c4801501d18060400842a4002440392043c032210000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 523295188 1250 523293938 523293971
    0x7050a030b0a0b0109090f0b04060b0c0a0f02061204030e01180b091e1e1e0a0e060409120c14010c050409020d020c0321010b0301050105070311120301060909 69
    0x1260340c4060485125941c100c502c8000b0041100a01d041001020000130803520798005c0b0041000a11000030b00004020200021038810303502c8006000c800380040900c441c008140414100c2e00485400070300c0e00c031803000514030b04c104d0ad00c528480040805000c01e0540c000ca1a0419a4013030302c2e403500d008401084607211840a1142140d280c008005401e0b0390b090039000c08201c1d880e04504c040b13886802c40e00007100c40035101c00c00c4c4180500200d1080552400c1541c2c0b03402503c807621940503206581000c240c4002c840d000e40c1c0d0f1041510380116800da2100c2d0700c503442c1c464001c2072040c030300f4003901001000100c4600043d5400081c030842d1900081d018810345000c011152501c61615103041280dd029410805181031510303420701c24017004140c1800140003040054281419481564400900610060700302c0c2103c41400d100600541e604001155080d5401d4101840320341c1101f807040d4a809464080c400d121103000c03000103a00d640103020b560239a4101d0a05100c0044580311031038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 523296438 1250 523295188 523295209
    0x10e0606070f020f0f030d0509040b0a0e0408030411040203041220062a0301080a030f030504020a03140309030a030807030b0108100302010302072d0605090c0901170a0519050705 78
    0x30700712042c100c2c1210040c9401d00840001c100040c0029540d1944140060b0a14495164140208000041d40012848d2610805150000031100c00c0c007881d0400b074041e429840002d0000701005000400f14085c00200e081088491500400230742d603030b10b882d1400032a803050941045012402c16203c0308544280200c40c00054403c2d54000e003129a105441255a04c0da440c101020b9980b10444420205100d08000d40c060a52400140740c01c038800c0c0f90041030059400024000c062803d01400010703178940c00b401c421207070021540310f268400e0b0f00c01c0c00d0449c490700050311341c94428200010b0030560043e030303254030966054038200010031a04005442d000c50031a00703051914003c09090005602a5020b065038500544030305200158654981c1d281801c00114540400e0071090010304000003402040c1d80f00840c080a0710780c0070700601c0170803188801801400005040005112001c1604101e0795803010340202c203c50b041001103543d4815145441c00580719401040808100d6040200101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 523297688 1250 523296438 523296443
    0xc0702090613140414071d0105010c212c03100c032c070b04060e1002210c10020c03121b040e0711070f0603020f21010e060607 56
    0x80041d40c6503000c20904240c070002c0350050035514000500c1c00400000c0a9114900c90080548041c2022991a10705042c540c000b180e02c4280c9040309414000b03800d061811100d0a0901c803490712124500b94445070350391009403a81c1c0c007485c0070702c11a40303602400710024050084040c3c500300891854184022880c9004641c05030702c11540c0e02164241503100f154400c0e141c2c500094107240c1195051000007815084a403581c08542c0165200c50b000c0c80f42c5130091407443c040c20f1500e458010050044184044418800c80003a1030300d40c401c900910420b51034012100d110322500400b0403c1c800703247c1148000307401c14803451207000c08003040d138821100c905103000000c40c00c04c5441c4950141c0c00c04020003040700900c40003130b091509062140900041e0801d601c4e0a145850030103001007104031001c041034015807082e00100b2a4070f007060072480a9410500c0c2c00341e581c01d59160501d8143c416030310b040340c916920383d43e00640d4182a414481c1aa44402a8210741b501d604082000701d00071904003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 523298938 1250 523297688 523297699
    0x21010c0809030c120304080702040903021e010204060f0806040e07151b0305120c0d05010b1b0714060c030405060304210512011403011b0504171606110a060c050409050c0702 76
    0x1400f01d044044001c5c50f40315118a03e4113180100a60205080d02ea80030011805a4003144022201341e40e00d150b80389400800c8802103060a260100091500c10040c0c0840c05028241000c90b400d42c44582101314090300c2c4074115007220750b4a020740b1044a0300ca000c1103000696191555100c50040708a241c0e10701e030540d64641c245048250160605da030007800c0c40d0030403401001a1483c018280c041d943c020310948200d907403144e9868990114001c0c59544444054004e42018811200d01828580820405a03086900c0e03201a031800380c514403440d0406c951114ec080100401c00401d1681600ca500014084004103036460f1030070755140c011207001e1142c6609500040c443c400e012001da441c4071030010004210800845003c42e0088143d0b61100001071000030b06001c002e00e40c0001c4690265001c005000704c00c120b040f5001c101c50540100820401c0418803603104000030483c906a4540152041080c0c006200000d4401e5100b40328550300c0500b80f0340000d9040c2d07844410f5904c0160058103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 523300188 1250 523298938 523298953
    0x903120429010e0126010e0106031104021c0507050d05040c0303260408070809040f06080105070f0219060905030307170f4807060605030c010207090b21010c0809030c 73
    0x551004030300c0d00017140c1080c1d0103818448440540c0900452040901d040c00001d1010704505000b42c42c0c2c58162040341c041c5004104a0900d441c0c1c441000c4086081c44000103620b4030386c040100d80c64031540822800c12801e00d400d00050214400d412800c0301c1c42074940200507541240e60f403001205c4012000b004060303010004000c500c1d040000d01c90702d0300c0344164a1030155540006801c460661540b4051107075159814420b8190910900350000003500303011080b03107200309000355101a40d401c101141c0c0c01c0000b1280c1000001e4001948042d88039059079224a4901e000901848003aa843d020404010380070400002110354541d0040300702c801d0b000c2e49050f994265519030561118040b03800c40c044000e01ca100351621140e0003a0381030305616241d440c0c100707042100c107580e10391304151b1094001d5610010241c0c0c0000312241210380c2c5d020045a03640115001442e103014121440c1d02940c1c86501c8102100c0b010740c884443c2e00800e440745521500c0e43c1040683d2805800d8012007507034450301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 523301438 1250 523300188 523300199
    0x8010b030c180c0c1e0c040f06050f010c02030304050604030803070215010b03060d170c010e0105100f0312030b1801030203010e070305120d020c01140f01061b0b0903120429010e01 79
    0x1003840c0131307100742107a0b0000704540825140c042c1042031180140c0050b04c0c40212441d0034005c800c88402c20384810301016003020001220201020201818400b202e042c1c0402c6480070b2050707400801c001004161038590340d060260065100321100801809904083d06406c100d80040d43d05a0300040740550556564905000003d0f200e40307410b0f80c078a1210844101c1c1c003d007903030080ca40c05031140000700c0c0c010540035007182910405003194001000314102444555134804006003203071f41196078842040c2c02c1c29400da004202a1100c2c68001c4000d4200900d901209050070303040300c3c400d500811006100204483c2c13901150f0100829580101700b1041d00c80031804050800c07040404401498003c0c080c00e480e0840d00c21039080c1c409041c0c1a800c125000341c0401c005401064030b424941d119a150010544489000c20801060080118081295804100240c8040c00894100300d05281810b08005000c58107100c110b1400c45c11445185240a80000c01d02c1d040380d480d00d106038241e90034403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 523302688 1250 523301438 523301461
    0xf0503060102010f110a2c042307031e05240103180605040b0610050a0503220f11010e18090312010f050109050609130507110708010b030c18 62
    0xd000141103640b104190807580056100d06410490600c3d940351355002d001c0409480f1403039500391801c0050082c41501c1551480007040400510103d9000501c4050304040742c1a0b0701d041c5041c00340d00103446042000e2150035070320480080803007240803601c106a00f000700003554802c640c00c2550b03042c0301181165200c4003d20059083c07505041c041013120940c95200034030741007203c050b00d40586450611050002c09580760b500410305a035440c0d039020a800f0040c04920443c0120001c0150010029041c0740002c804130000d0040d0901141c62001c0e07600740a80384040d0000180c42c00c0065164240031036000703101401e8100c84c0644090b402c03800b410108000618001e115030301902007048246d04500324040d140d800303003c1010705200c0140c1080c00043c103003a19a0031060040d1420840c40701190354076003a108a203004031101207480d99523078000322480181e01c107900c03680d8414540082403010044d00010070f0480d09400302c0780e841c0003000c20401c49951241e407445c191100310005c10002e0509 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 523303938 1250 523302688 523302691
    0xe1506010e0f030a03200307050a060501050306093a1e020706171806180f0c2d0a270b09070c030203160b0103020f12070b07020d050106030b0f0112030f0503 69
    0x301503851b94071100000710030381960b00c640e904803003e81142c04400100406e40c13081174003420058000b003000e45000b901550f076400139a601e04008980e040d0243e4140c10b100360070307049075421403c0403400c0d043d100da80c0070f00444500c40815241600000300780060910000f400d900b1507189658103c41092045e0340c0e5119200c021f01010458141422100c5004504000340c50140701505a0b40144800301c00c2d55506064102c0311602d0721741c1043d60300c401c5d669507803801d503c034030b003034980880c03500e408032682d8100309075040249d45402c085038040028817030051500300f01400104455110340c400800c4202d0003112411904603a11107046408034400320311403c40030719000d100307004603071501071310001c84004d422060f001101c0401080c4018411410001c4030003080100543d8058800302d801d905090319420503005032070440c0c801084140031b40d954a20b80411454202008214042d200d080020314540100d512803103580c860000090030005941c0414515a0540d40d4494100d441c0a4200c495600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 523305188 1250 523303938 523303967
    0x150b090610050708040b04030c09060b1206030a240b010503010b181306030c1a07120e01090b0d0e1207170f09060a030b0f06040f0b0c010e1506010e0f030a03 69
    0x106110a40000e04013400030170152482c1010162a10300d1480c0c13030104008141c014200403400c0402c10030a501c0d03090b050701c1000d29100c510748003943e00d25000c41d182900b0814041d0150b03180584989483d01240e404607215a603595041c803102440d01d00540d01480207210b905034112003003202c0220000403d543e0012294010090b00c60350700c00c40b2900c411743d041381c0c00075101c03050110010001950b950941035144564103180c1030808500303842ea0015800700950000600c03402420000b007036071140f88060060309801d1b465544400400c0c0b0f00100411140ca9044600d10400b11420915202c1d1402d40c0d403200d40c0711010003141800c00703a081d03170304c0d41003129a090002000d002501050740c0d91000740c9886201c50f500010001d8081007000581d0189048990198000304024401d4070317811100d12050310060b04026550b8284011868010030819509590324041c64080d80160b4031548000d07800760304241e03140442c0c140c040003001080c80e0400352240e81a03100c80703c01800a0702035001c5070855003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 523306438 1250 523305188 523305197
    0x31b010b010c0c15091a09040f110706050603010b131b020705090118090c030515011406090d0f0203070609060906020321070c021203090103050a020414010c210903150b090610 77
    0x703a0f03461002446c88480e5200244d1a0340c00304880f0001d08003031180c0c00030b803424001c00780005140402c10412034421580041e00d119114000203100d0345003500030140c400c1d000ba002018040c980c6000c0d800038400c3d4001842000c030b40d03104050301c0520000f40001907890040020392240d282c102c1e51300c102d0b0420304041c1d4401c7d46500e02e64011952a80c440c100441c0110060006080c5507444040c4000050300b001c5260340e5412500203458991000741e5050744c5c010740b2288807181c814201104000d0340000000d40c10701ca00d40d40406d04a9201c5103843c2190510707211402c6c0581c0700c0005036200d004000c11103200e0b00f40c450004090703082c41c0d50500d400030716909091055140b10b4000c142650900e40c16074040c5d23840050a81803c3d41d0501c03503a42d2109400b00114181030a1805a59581403091a801e04000846200c4001d0109940428900e201d44000100a0312586e030700c050b00340e03221413105607100c0c600035840c10303140e9040740102150342d580101810810307658003040085103d500c1401c1030410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 523307688 1250 523306438 523306457
    0x9090a06151106070c120f17130209010806040305070f210f0e0301140103060908040b0a020601051003141906080102030118110a020a0f020f03031b010b010c0c15 71
    0x2041c6412401140070002c0e90740c84041505101c84900d8954054079520400c100841e0a81c0881c400f02070081c141c10083c60003958110301c0c1d541c03c980d0605204804800000e42101b880300c1324240b02044616944251104c0f600c680c6e0f03401c0e0032500d6000481d40500450402c00c0a0070014900c095480061403007000c1000b1a010703035001c4282c11101844001010450088070b1185085c0c02001802041c2c5045009001020b02aa00c5076030000e0f062000030200381d11241c8150400c403030942602c02911a55120544481e0491802540c904080c400c1030b004070359846880b48502e10a00034044d100c90400d0720034034261601620720000704101011880100d98805011415400a0008500802180b0b0308907203900280380c9158104c440400c8400c051104c20083c0c406019004914201a150001c2200e956a1902c0c0081520358000000f00c5505000c0080c82009042500d40008035181101000f041142040e00041d43c00e40702c6540083e0081c10141003c00068611006106405001c1c1c544181507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 523308938 1250 523307688 523307699
    0x51003030c0f081909030c12080d02030a09080c1c03060308120612030a020714090709060e0609220e012018040e03070501050705040b07060f140114150304050309090a06 74
    0x340382c41103041341c00040c1e01c803408000b809038054061014022a0360302c03480304080b668039031016226800c0c084042940110005403100095401140f0581d08410350f00d580340314085000c0d03200c1c2c8100c00c0030311142c00c05200101000c0e200e4451070041d00c7c3c0c000300440c03801e0451034001c1045100240f80300d5018030303201c80750701841106101800021909400501e040350800c1c10451190b03100c0a2405d005405100c1000754082e4032074152804c484a41c00c244100d409420003007940c0c1d100303080300323250410080520741c00d101d217542c94030441c4440c3e440020440c2c58150481d441c01e8a5181c0d4a9941c40361080c081c0191030340b4143c00503c0728051200d820701030700941c1c80219007907a00300704055200343c1001c42d2003000e02c4401e010303090380412107140c56071405050000b2800c0900400e0800780c652951601c0201900d080d40c2d015820310556800100000d603540c000c045800c03d03655102c14010012519941040740703d003005c5d607011703540c040e014504242d4004140004000020199980984c8070070740081c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 523310188 1250 523308938 523308967
    0x315090b2209020112020901050a1803060c1d0f030c1003020d0e03040e090303090d05030717010e060f0312071106310509090a0303020315091504051003030c0f08 71
    0x400749010500814419000e00000d0f100422000314440c0c064010040c240150f80d1003402ca030780310701c40c41c184506100343d84a0501d0400406070001040180b5280f809003150350040d035a218154800c280108414010105000d850081002d410b605a07014051500403850216541061064603142c01814482c0560102e03007510091300c10450309400004d01440f20034008004a503118021900440c03850a007122003554070590704031400304001e00403000c1505c1c94030980000705150362840d404001540c50b008031459440341034410610a008440444609080125100d090182c003002828104801600c844410300501c50703406a00a4041050441e07461100003004488110b06554a4400c001188031a60000b203d03006584900105005c07c0703c1c00c60300188400425a0618000d600d0392a5004008100030646c0c12055002980d00c04120725255114581c2c0c000400485090009850780e002c01c20400c1c0f81800041c0016140703280060200b181040c2c81e800e800d115521481c0b400d585e64034400d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 523311438 1250 523310188 523310239
    0x2c0a0b060403121701080706030c0c120206090c030d02031602060c0f1011030606090d0602041d100603060509070f0c06110d050705040506090904051e15070315090b 72
    0x101c0d60720802c3c0c42e03107441950000c0b118150802814a1030322950401004943d51798942c8545010551211020b0540d18410801d504200381d01450106000152080194641d5401c4983d51114458084401400d2800007101c881e801450340207585000c0c411403050940c40c110700e1060760012402c110480600c8001c126004900c0303d900701034640310038030b8a031413400e0302c032485000c1c0c001d046c1c03d006200040d07803080201c0b0031001c130071031305820008803520708407000e80903e43c400e100200804071100c060b1003140803c10b2040c5078503003c0061081c0c85940c160115081e41c0901500b0141c00d800051919000302030342100c950003401c019030a104c035075491600b502c255404440d169040403070008410b4106028658011a0908007a0704060030900417035800d008201c0318030312a440078000705042c48800d1200e0400000c0fa100d0500340221811134040e6602d00900c000c0040c620380e42c00049105200303204480c2c1d5182c1151802c80e282c0e10380740d03150015003d40c1d1300303a0340e10032085043c600304d0b00021304400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 523312688 1250 523311438 523311443
    0x302030f060f0a0b0a060c06140106091a16031412010b0a0f030e030313020414040303020309070e07050a0f050c0601150314040b0c1c09080d05012c0a0b060403 70
    0xd01c440d240c10980052035100107010001c8003800c0c0a548999035031210505400d5401c0c0d484c001603051420300b400d0340900400c107000c180b1049040004666180d101d80014182c411403c004254000d018030b07550307201e109a0080d0101c0c49602020040060f108030f1000c0040b4000b80000b03801d281d40742460070000170081c0d00c060300001c00000c500b41d840e5080140b001c0d1844960400700310001401044039141d10004007507500d07040746180c906c000c55490380d002d1085178406030440c00c100d1406245c040e00946c010345a55160748940f8000103000074003c0e440d03901c1820039503102c60a110803403805075802021a1007480611100703020007030b040c6204118050003080c04c021000e8205c404814082c040f9003901d92504081441c5908102c0070418003100ca640200044050b140d032070355105940d84101e000c0d01088081c0500340b44c07182052041b46000342c40100603a100c2005a82d9807600c86542400c0108103089004089170f4030718500445602e16558031051124010441f0300100b00017510b0f542c01600304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 523313938 1250 523312688 523312693
    0x604030f0b091f0c081f1703071406040201080c0f0702100302040e04030801030303060602010e03090f1503101401090e04020d061d01050f0a021e1e0408010b0f041e11040302030f 78
    0x203c13481c26403081066801006103800024503000103100016480c40300d010316201c074410f0400800796040100200c401e80d03904210704a200008160002d17840e05404c2c0c400741d00183d0401d011411901e0720b8400c8407107104601c6540751404049609000041d4500103a00050603800d100c00100002c4041c045032055209035075004c40ca42c103614003d02110344541048085a1500c06441c5d100000041115004042120003200000c1c6c49170005c1e201000c1d010908210b0707071010041c0200081c0c00404001519011107003c54208004001111111000e03c1400c120344c1c61600801c01504000381280040340c0103100c08140c18042d8402c6c8030342c2d0b40000004000e6a0764035008c1200103c0010072450304020410350a525141c05d000c481c0090750403941307411884080004404080c052160414860034442c3c0008940f034581c0c032880180206040010302d03020300724150351041146420b101c0c2c070120841b26400c1e04810102d101540f030041c0012459030b6600b003000c02010025075810040c103400c03038000f07800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 523315188 1250 523313938 523313951
    0x30c060804020301110901092d06050a02070509060901061803020a060f03180503070206130503120703030f11030c0c100f15080303010f182c0c0604030f0b091f 70
    0x41c142142c0e41e85004000c0c1007400c0c046061240e81c410b15030030071250f0003400d02240c0c54989d84141032810301c0c01c040c2e0314000c440510006006400901925030002143c09076a021992070301804150b50044a803170358080300f80001800740c98080d9842d201190325840c250341c98a0380701d0307000c62150f81c80d075082400403550300071011203010b606006540d074002580c01c080c1c400c08103a6950320781e00c0c018468000d01c994070100d14520140284d003e944c004040040032120001100300c2d0380031682d403246100750002802d00b0a40c0010600e68090b2006122075194041c0c03a40da900b0f06160b5182d00941c42404440c080c010743c000c3d08400700d016401c0304a070030800019a1071103c01c06100d000c501d03075101e002c0c1038105000401c143c104902c143d5085410241000c5040344140204200a10294003082d103001051002c0c15041d4030110301c02d480d00c0110000b00c80900030388034104541c6004071b100c001c00c0900d240d40c851001905100e0b100707030007c038108212440711041c42c20400143d02e565025941c1135a0728007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 523316438 1250 523315188 523315193
    0x2010f0e1006081c051c0c0507060e0118060e0109022101150e060402160b090a0b0619051521091002070210080601020f0709020405040507050f030718030c060804 71
    0x86200b0041120400a100005028901184107070307a0041c2c0c801030080105590307959801b80b407120b014114014500b0040098415401352554010b1841641c91510b4041c00e95013104c0d0503c10091440100c0c901029800d80d1740e5200800b80448040d104c40c80d549480e140e10041c0c0341c050081551204c00c01500c01e140c54808082c1d82141d0142665251a40b03984034200410907030701000c1600f03d80b0507a03001d0380d45d40c000304441e2000d040c04040103201c0000e4908101c3c01d1503000c41d207545081c2c401c0070603007100e803504400c000e01d802c149050b88482c2068443d080010345083e88000f100c22a080402c50700f0800035031030019a9800c480c545003400c810301e00c00c02849141c03e1121501c54800ea820031424419507401103400c21904064240c1440341d82004248280e0017002034a400c030044104840801782ca40901c0c0c0080e411074400e80d801681004085440d0500541c103031040c40c07401e00d400342d0441c3e43c0d0400442e01c24441460510101051440c0440800c0300007806001400141e10340780803500305071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 523317688 1250 523316438 523316441
    0x10f0c020c1509150705070b190e0a0b120a150f15021516030603020402160c0e04030203070b150d030c1b0524090d0507030314070809060a02010f0e10 66
    0x840080049901001803c05540e2450b04e00c1c5850102c0c000801d8480342d007480c082c3d01c0c054280d003114803144404500d400483c0c00b0032801503401c2c440b03a684e400c07411114806020026905029244568105000c2c80c40d00041c0607840b170b03600c1990101d000c10b0300c082c044200100d80860790017035130307010110103401d010b001458011031090721454401080c128942c6811000c81e8100503103014240a4440c541a245070310a80001000c3d5800600441d5612400c40101507400e589600c21210460740b0000050080c48405500c0c0c89160507030050340c40c109a0350355034102003000500301415506c0c00c01103d03c0f0750311040f0420f280240720fa281e002d038000840c24444805920300c91041c42488401409000c00c0e02c68036498070115035041d0140180c00e0b11461040c030300c0d0040e420350705d800c03080240520301400400200c0e4400c0364040d40300d44001c00030002c40000380d440354070009070ac1c22030100511030309400c00c0030050911202c64030000900c0d0110b42c550340c0c00e507142d101030352041d54006215501d151075507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 523318938 1250 523317688 523317709
    0x318030206092116060f0515040e010e1c140d02070c290d0b280b0703084c06050c06040807060605090109020703080601050306030a1103010f0c020c 65
    0x941003d0100303404000f034030f40c0302e00c04c0004041c001d803402010310007004180e41100c0d020210514050101e4607044020441c588170400c40c0034804c80c02d01e40c44104503030040c89103c41d06607124020301083d000c03044207024018000c010150400c012070020348404800c0402a00c40720710401000344e9982e11904003ea10200355030080108600b180f20812941c5180c00034000d0800082202c25803510301c02101c5e0310080075600312007900296070b00039101e2048110700d00224a150503904100000d41c488095000d00d00a4120041c04a815107020078000015404052210208218094150b40206038080d080c0328400310624190200c569109204182904003040501501d140540c1000c0e41001010390703801000d00081d0418900280e444140034441e000795002d4180500480c80c1940d4900007500250b201010540c005007514002c0391003507210314200c2c2c3c0120b4008008201c80752507901d900c091440c800d54420390640d81c81480c5c96101aa500034000b045038650017809072130030440140306506a8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 523320188 1250 523318938 523318963
    0x15050a0b0c03160f060b0a0506030a09060e01020706140c040320030a140c0102012403080d02090a08030a080604140a02031801051303080105030114010b0a020703080d060519050303030105010c0201031803020609 92
    0x21141f0140000c0d29044152980109295008203d1407424101900101008040083c0c654000107454050140313540003641c40f1054440707002207a40d121a9084464060f03400000c0000041e00d10401d20303c6140042c00c0070400e0b004007035a4000078103030b4072480010700000601000c0d03044506c030301900d0341e02882000c142c40c840302d100c40a484403540c11400c0400301c1780001010b4800200d00f460a800b840c0e8151149000e0181c0702180c1c3c9600c54410355035030f8010084210004818000289003403d00340528a000790382a031000d0410b84552020b01c0180d04020031030a0311107030000650004038004d01819020360841900c0944083e064140181001c005810440c0280e04001a400c0c2c460069200541181e014550702503c9140070b802c02c030704088195001600c0040d0200742c82402c4401d03540b001080768811101c81d107681600f04074100041070144a03240c0d041d0800d000411640d4001e481420203184140340c00140391000a10505100c40c08500c280c1c0117a100d40d081081030340c3e04100c1f00110a9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 523321438 1250 523320188 523320199
    0xf0216171603050606130902130213081b01030f0b0a0f0501020c040e030315030a0b0f01140d020a0605031e0a09050d020f0d0f09180c0315050a0b0c03160f060b 70
    0x10b0564a6030740c0d9038880902800e000b140c1172080000f640000780d11940649038002c0031240c0b105c2e004005400607410101c080140703d441c00000190031400024011402c000c03514824a190600d4070041d00100b580c0c4040070b04458490051002903030700ca40f014005803a140803045075050134000020314212480310040e00941c50300030b020141000000c29030750712600240412034240c26820109003081c4020340000c09103032500c03044c00500c0c86d00b1400790f81038500070010a45981c0403001007007030710311446c4ca001e900681510030902496200700e000796401880508200030b980840b0500c1101c601c02150b4106a040c1d4803858101000414000c4e040340280700d00c02000d42e060b00000403500c0d01207103103044007400b001c0d081c9511039a0068200100070300c03112242c51010355080c0004406440140c0e45100041e00c0c3c660410080e41c295443c0005459028002510250902402c000d680c1c1c04070384014043c1c032042c000d40d00740a654820103071005104d41c01c00c980003106890003605031524498500c2c03080e07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 523322688 1250 523321438 523321483
    0x1050915100e1303091d072319110703080706050f0103020a0b07030c02060c0105160504061b081201060504140a0b0a030c030906320106050702010f021617 68
    0x10b01d285186039000f20a10615620128941c9000d039480f10107039000e8541e40000105401c44c03400801407052041803e81c660348007450300c21440301d812804092020340c000406010170812840300304040b111000799030030b00d070807d800c0742400e0303c0c80e0a00c3c5600403509180006091010401280103081e0410014000200e555055a00040c00700e41ca0b8044e00700b0000d408a0a42c0c20300d0f214485080d100743c0c000c2c0213507582d40c4003010000e0281c1804ca0301260149105610308040c03910803c00c840446000385d8500c43d40104203400d90f0b1071103031300b1007080d5000442400a4142c01c101c4001ca14000d0840703480d030310b0b552464030080c410000c0c100a121841845205e01c01c0190254400895050418620700095200c00010094006110181c1c1c05414586446c200702c4c40e42c00f407110806255650300da282000030b40fa0b10080c965142c000d0103040c000940a0005a0055000d41c02180b00c050b01401a500c51110b0180d480702400e4241d03012600703400d101c0607207182e400f9003031102c0d00f1700c65400c00a45881c3c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 523323938 1250 523322688 523322699
    0xa0e0f0a060819050f0106081b2514030406020d031503080f0c1f111e092103030402040e03090a031103010e01090b060f010f0e0910080105091510 64
    0xa1900d124030010301a01c000000e03440012001011200c0720f2040c02000141000c0e1410b10300c0550901501004c10708020101c1c450100002401d00080408004c003898040c7d15501d4000c241081c0c2c0401d48140221102c90000544410400c2d103002240c5c801140c0316072415100030f1403d415403d8940c2810f02d0040301d072441e030403580383c40030030741c0e81104010fa07680c64003411814541c4106400f07018180241000c03121b58441080b48502480000c020074407903020101c3d902c1d0b0f224410088015200e0704401e0130304210509600c0038010303000b0020201c070025680c5400e8400c001c69044002d04068000000300811440d16100300b01d0480d48440055081c40401004035004060724040504003c00904075099196025000451140d1080d4001c6c440d01483c2d20300a0010703003050303d04074031580910f003c4060b654810034505102001981d10102024480720502820403405460080041c00d40040410070b9a0240207550166190100406d41c40184030a981407030880070346100e01d00c0307014002c03c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 523325188 1250 523323938 523323949
    0x10f050304030e0a180501030611130e0612030d06050901060935030a0c02090f09061308130e16050c07090209040f050403080103120f0c060f200a0e0f 66
    0x103110340d0600303100600096480018001e107030f01d44d1005d0044001080441022001e41c0c002c50304a03441100e06000c1403140d0940580e02c0c0c01111104900d400d41342008100c601c07260486980c20a0014142c50a206500c1540a04641c0105001d0000703944900c5d0411450400d01900c600400e5507240c060000d43c2450003151015600082070312a502031030b01107907850b45140c11030750500704150f42101d40e1a0385480001d07080b0742001100764070466031180014601d41e10100c0b0f80f44141400800b83c8459655107000039152049a10709907090001801250174101106c1c2141b0301814001080401c0c91411110329029210340a80001c1040341c2808402850307a800110300c0182c80c0110300150b151900c09000c02c0040c820940801e920504000c24407081c182c001c3d0301c25058078010545490000301d0840c055541d00410381e00c6d000000c41c81b2024401050040d4084003040c0e4094a0110780c1403001940c020340a204022500303032194002511440380740e040b404400d0001f2042d10442100c81d002c200244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 523326438 1250 523325188 523325191
    0x108010903081807051215010902070b0105190f090203010510020a02030615150d020702010908030901020304050913020405040303240b030703020a02071517090c0f0f010c05011802010e010f0503 85
    0x41c0c11509003402c03d540400244510000b40202030501e666540351014000c1c2d5034402e09510303002880a01001280c40403ea008a45070903030804103440c0b950b480c01d000e020058030035450f01911402001d002103083e01181382240d0050518240250b00c81d4108010452814114907110307055600c0741000340016180807801c20750180b00b01c2d10b01c5d00484052404507001e0441c0811078800c80b00d000450319402403442d4007070304002d8000c0c3d032442812900c0d003804036901c0c0310384003800707001d41c0c01400b04218a180001071598001d00c80c88010340403e86c248e020409440e8142d904901107900d40000c4181000314901d001c4880d50b0040c4406140391034080c0c0403140303100191070f408c00c041d00000c4039440c0341c0c000c002e20b500410148210b5a40d0444103100100350784a5070740305000525850011500016000604103100b0030002d08043d602000c003000c21030701c6004010180c1c1404405480c880c08150207214051803000884001c0351131407264800104141c1c00240443e051080300c002d50b610480d84103040c2d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 523327688 1250 523326438 523326451
    0x150f3003312c0613020c0f070608010f0509070e03060a140a02070c0b030c22030213140a0c180303030f0b0303030c0f160f060915060b090f0a0906030c0608010801090308 74
    0x74141c2d80f20340340860110403042044190450000959620707413140095915000700400c02600c01a5840d01800c540b401020700c00d8002c0c03050091000e000034034060400c1e5070400300c103040c461005400240440e060000455860300250390fa080c0310520041035860084e800f0380c2c1c6190851130001d07540e90b190102e4050f8080c0020120021000400c112400c000312505220168020204002c0c0c61005408a140a0004070b0143d40c000361280075520507401000e04450500e6003031909541c80c0507800e0000c0c00507a0000b02041900d40c04470a034142c100701010003071400380c0e80c04100703911161071101c2542c6801808034003072307031041080000101d80c60f019500380790030310703607180d0f6075940b4490700041c0081444e80c025110810b5602c51000308070459108034003243c03040c0020483e003480d01032420100c40d07403840343c040c03a1002040a030321145000c603c0343c2d08041c4001c1014106075140c450260032600250003c680700e116644080c0040343d0000141030040079464024820000c0c2550010f000751406001d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 523328938 1250 523327688 523327769
    0x80702032506020405090405030d15050d080c01150623040303090501180810092003060a091b0305010207030215070c0f050a0b150f300331 61
    0x1241e0802c00b45030121002004010044981420141031490b200c0d48600100f51000f883c100e5494040c0908440b10400c603040100241d004149a4490703078040c0e4045440b100c0e05559032145c14801c1610040000c0c00b800056603448140c0c00c00403444d54107032000000c1302c103417035405000402c00644d100120b00143c410038607203001104000d59100e110000c168208070036900601c0c21400203101c0592080702d4060255821008001500c0c2484609410380801c05416411190001d12802ca05800c80f20400f88038219911590303007440e049084d00c0711a908100c0d001e940001c1e130360b01070660400044002c015203440100c82d03420b149802400380540b8840050044c42100c5540d02408414401c406141c1d800044008281c07525401d01c49a00e4500102e90388941011912129a03090800420204042c20182c503803002d41c1d46168400000c400b003c1e0704469100400c808038a0001a014035441d000c1c175035100d0b009010071800080c2c2498002c2d0071000004000664413464944035204c13410b01800301046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 523330188 1250 523328938 523329007
    0x4092103112a0102040803270906090603030408070f030611040e04020f060f03101a0405030c060d0603020a061805090618070e120601030c0509041a0705090a060f08070203 75
    0x81c20000100610b61080507520125002079104404001801c4445049554506217003030030514100f1407202c0c040302070300407c1000004038142403c010082d00300d80000c0c110381c01d00d5030303400c4801e141004a420a803a01d405c00b401c1082080898000c91200354510821582840d0034142455840440144041c2c4a08406024004613031561002c0b5215403420761016136880c80c21200c81d0040c8070003480b44130003c05803000071002e940c03804810b441c16180001e000c0d2054610200c104800390300b0030710008402c40d5987c80c0c0040143d45082c95980140b00e141ca8200c0220b01d81c0090f1155020b49902007401141c511b001c004003982c0d19032506507081044950316040d61141941100c040d0301031840c50f80c206100100101e4282400070b41c3c6412284a0b404000070282c844060101c02581034800034000e41034170075055412802d00c1c2ea0540d00c621145015400c24028100082c81070806a01c0340c00810191040c8601540d0f114003480d40c000c040380003c41c0f5028035250003c603411b904010f4070001c00100352 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 523331438 1250 523330188 523330237
    0x4170702010519050c10050705040627030311150613020711040509010b0a12020627130b09090d02030d0b0a050307090c0f0c0b130609020409210311 65
    0xc00e952860407607501460704400e101c3d402800d503a00001680c85c50b80304488002c061000c0ca40a00c80c0f01c1c03038280e902d031b5041c1454200165030072803241001008101d0304106080034082007042101c0110701030317a41e5461500d2040105418643c1c1c000ea0ba070032089288041000070385644807901d0b4015409540182c0c1c0304190300300080402c11602080da80581003005100c1072040540000207030150850700401e0a598409082030b4500d0f801703c0007500f0000c240211050011420b426510031592003250018801c1800c0000e40988009c40c40003000a9480901c00041d062420003182d0008103e00201004800c07864080d542e401100d000e42021030312040c1c1c22000351100300b13409004000107030403640c0031a141c507a090003825a154000002403e42010550384522514026030380f1604400001142d4483c03450400041115800a5070316944494400700180c45038030880e910103015842c0c034055089100e1000001142c11504c4804042c1480807014908030020200d65000c01648402185101c200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 523332688 1250 523331438 523331447
    0x415210e03042105010e0606010f08060d0210090306092904051c210c0f080c04090b041d0127110d0f0c0f060315290f04030309050f010203030417070201 67
    0x283d0005003154288000540f05240008003e80a00000d0321021400c0c1c2010004880800c02100c2e2581e001c00c0c03080f0100b0141c00c0105401e407901c3d9851a10074030b060f48a4907800c00781c070104503046072000c0792041400d040a6940e000900018680ea00360000c038181501c51950f220f40c80300c0003405041852261600d03090040460040042e82060400d1419414001c1070740180020703082c00d0040f49100d01250800c42c443c0000ca4071900c0c10214141c03c060420030304800a04030a00016000340e6246410032413040034000d01009a495071001149241e080300c19642100881c1e641c1100c2c4999010241c1c00245818000c1090702105540030342c5a00c00c1404d0001c041400003c0207001e890500360301180c2d1040f19508030b800c1d1141d5407000c0c8a50395242109488180143c4651149031103090741c9402c20294614a014040250605a50070400400c500d000e1a6020ba03004601042c0c88000805c040d080042d030003210905c0c03d00181d4103506c2d00d910b0f88000780c80803041112101000081200071607018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 523333938 1250 523332688 523332749
    0xa061a0406080f07080d0c060c02031201091a0102070b0d020d090f03020a060507050906030103060213090f0f06090b0d03080a290112050108070b0d020415210e0304 72
    0x51041c000c8aa840182e0358580c03c840e8078006260260f2203020480d0000001c18168102c02070380c480345400c040b51142001000080d80300c0301140010403a004101000281c030a01800e0103020014801c01d03000781301200142070400c0e03107040d504810307010049903070071109480d0b10381018400075075038055544030b08008211000000342556591800c1e00e0501d0b0380002c8018116100c3c4500300100c1d21800c0003611540071f10300e607881d84604101b00520001c0c0383d43d0091300d00c4814034800a085651210980816140141f8002c080d0559801c003031300c0003a4142c020040281303a2101d080041ca2400340214020300e411000c06000e001c00b0f0400b103800d841042e449440d90280a0300020811080d954144c42c84015603104140000c54401c00d100ca06401441043d040307807190701c0104540d038a096859402604507800500c103941e42800002040720500809041e5a130340e41d580d03000c0f1041c040e2100003102940c2440007082c00c0c130b0034031410643c43c1c1c0002290262000c4e02002c2007241007980040100808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 523335188 1250 523333938 523333991
    0xc0a0e031204030303092d110117011e0902070c09020a050f04090501050103061d07230c0c0a1a031f08010e1c172d010e01140103020c0a06 61
    0x1c0040d00006165140d840369045601c0340c0d2000314413061981ca80b5140301140000032481010030300f015000200403641c0300b9040740060601c40c2009140d098001101d050076404083c00c0b01001d00c0c510340f40c0145c02d0070100a001600320450820041d1b41b070340f0080140c40d025442c0110760000308141c00c140104240ca00480c00204030590b200e03120500c20340545070a105640c01301f41411400701d1401500d5419001c15401c403010f42001c0d0380c46841c200e541c401c042100e8070028003907104120008100b40020f00200c14900001c003802421a030604c07c1d80348695115560101c0044003d02c0510041411170b034108240080d10750310034488040110b4807088c01d034010f041561070403a14032004400403030601d0442c0900810280c00c40258503040d02c04905031102058100d2403200007540032907410302d07041051607400080808503103000c0301044d6200c5003a0059034000309140c0c0108448800c1f0070040800c0f107400c0c40c06508010400c02b00d036666481c0c111005291030345034629200c001d02019000302e2400c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 523336438 1250 523335188 523335223
    0xc0f0307141e1009232d100c11010215070f3b0609030c22050f090c0d111e100306090e0304030f02060705070801060b0c01050702060c0a0e03 62
    0x2550f00c00c02902d00c400c0c9200e43e68010741c0010b0b001e0f80032490040c0c00340c001040070b001c40340307116140024850069096102075000b00d920102519161f00c900d0950181d05605455218a1107111700b1b202c400b01814100791070440d4021607140c1c1d000c0c00c01c458856000b0b00207003068200300d40340040c180c0e184600030311501e04130300d200d8280d00f400301c0107401d6000528330000d8004548802e00700c1440010310500700c0c0d1a4145d03000c82503020a07810420610480d00e486080040001004204801c060307400079604504264000801c0c000f40749024000b00c402e100003241c00c0038076841079544508003401c00c01c0714035204114034200174036240d40d007200100030703900000c0c4940500c4600d01c0d00a4001d00d20350103010b035120f1a25030320004d561000400c50b420f481d0050301d644550345c001ea0801000e54000c032411103c500400c0030004644902f4000c41019049403105503443e800503908890840e00001e200c0c10855000900384810755a01108940c081c01451602036074141c2c02c80046031074010410703030003030000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 523337688 1250 523336438 523336459
    0xd030c031b020d21020706090506070609140d0914090105010318050105010602011d0a02030307060b0a0306020c01060509220b06010c0803010902031803130608190e0c0f0307141e 78
    0x30903140303480000e444e0900042c85001c0d070780120407039075607195014280200d0040401440580f415502400303100344038910100c0c94070100e80d0340c04500108104441e0a6a1000d01c0121180390000000409044c140808600e0345400b003000840c8034206101c1c0c18103141d2b03210031407a1084145224404983c0d003040082c441940c0d1290000e000341161540c4055010b110880c08004000c00701d03030700400680040045040c0422612148018003601595907030040e100072000000400c1c500251000103504000020341924000074082d00b22f40050041803e03d00349440c4040385031450500d201c80607004182e0410036942d80700144c403840d00904000e0503840010000090203851034000718442c0c96000810300d4240390102d000c84d501c2c0544080c04d210300b5400003060180a100d01000355000c842c0300444151100840c02d914100c3c4c210380b4409a040d006910411420705012101c3d0b0b00c02d4409800805c03510345009003504000d880b801000b4840c55420344a0000d0b8908820b04001d503160041c10300014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 523338938 1250 523337688 523337693
    0x70f11040b030a12030b010e0105070b071119060501120209070f0210020d09021203040807090f0f05070e010e0303042303010f0615021002040f06120f06060302090405060d030c031b020d 81
    0x1c407030940301340c50020b03013031074442e41a5510400180c0381a61045c2c60311070030300c001360340d8150a4800013007100041041d2815840d5141e1010060000e149403491603040c6441001e08120007500c034160040c1d088001600d0004d00181c03210b2070300366840030b400d103001c00114400104c124101490401106c242c2800401c0d918040340701036001d00c012510880d285403080c1e4443c40266140e00030f0740b04504058010450810010b982c40d04500310010740707170400042c11040148000c04840040d1a032070001400d21385c1c0e07820156000511090740e09403c8005500701850403070071400c410100440e4042d1001020b03071420f030301c4d20250450040c400e101d810a02a05441d0411031540e8001d0440700c600602c60100307070014100662003110709481c80e00c00740224841c1440b07815100c80043c0d9040c102c24540e2048420740b601c03028419640a4001a640541e85224081c00c00c03081d40c0001e0003480c8100c034803132504000260001c054100441e81030421015061406105c09103414446401039000702c081c0c540d034401c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 523340188 1250 523338938 523338953
    0x30709020f1c0c0c0b1003020301050c0415030902030c1309052b09081209121006180e060114060705010f02030f1f03230a1b0803070f11040b030a 64
    0x4a01c40d860790b01c20000d010b07080140549504048250100302e038045402c020644400c1c590b5400324020b8850a641ea561750b0119003101c3c030440d020440907801080030311080c920304100c29940549850b00380300d000c1f116000207440b80303a410001c9209030908888005841c1e4503400c04600b058011059481c07564040d000300c11008642d20b0524104000c1340010b0300303c0d50003180294280c5451400400d6061440f0b0426810759100740000740d40540902044490404100b160b03190b48070369114049a8640303000c1106080500c040c0306601020b06290514100400002d141030440f450381ca00e035400d03000482d000c07804500c24880017800c15400c2c2140d40e070803564140c00450160102180152242d035880d4804c0d1490681e0b00320a1601c080301c40410004100310360980c55207060000000daa0b404030b012112464000c0b142d41c101d6940041039090030f5034090045e10b000080003100050740c0b4002541e07031050300a03510124000c10b81a4803e102c0211500c440e80080e031181400750848090f4403c0742807450 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 523341438 1250 523340188 523340197
    0x109170703081e010306051302041d060601030c0e06071e06020301030b01090903050a0f0302040906081f200c0106090c030e060714160f0c0b0a0206010f05011d030709020f 75
    0x140800e22031008901c103c070400b1510b54200c028610f8102e060303400c41d83c581000d02000347c003580101c014162500d0143c2c3c0c461040090200d400415004810300444200b800c20320000d10584c1450f103041e407100000e0b604250000d82c14501115410758804841c036201e401420f42c207280e16405016408040200a01e0b64000c5040e280500d2035003095a07612100380080d90440c03407000b00000c00a100c900145d40c0a078036030350302d03c25041c00c0241c00d180c2c44a4200e8103d0300a0f81c0f08514503032000603029480410140040041a00008203002c103038528100c0440008072081021290300c000036040303049e803000b9404031003d0800a0402d12801d88041c100401134409079182380340b1401100045007040c0d000301c4464003020b146e101d0303071410820400e1f0403000601c82e6100a0758088001c58158001401e40800c0388007621449004584507002070718024503064050b0460392007069841d40034440b076038009201140c84001000b080c0091410b0700042428a00c09920423b607207030011500b4036a241405d005070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 523342688 1250 523341438 523341443
    0x80303040c0f0f0f12030309080f0d0e0f060714072319020a0501050d02090916090f030507090203190e01021801051303111507080901090b0a1e0201091707 68
    0xb5106076440b200e01e102d80425520600c0034800f89280d0400c401421004013071240b90003400c0024802c81c2d43d48481c80c0b942c0c000c40341030340c981c0c00001d11300e40e00c0307001b07442004011580b02d40241640c0ca00c1850482d503450000d4403800911007112221081d042205007101c603d180e010404021400e1900c0460384800400340a8529078003c000c00d000d40480342840c11504590014840504140340500668641c1d00040000048540801403042e05498503003001c0d01880c0d09c414190944400c1180041042d0002c1d0405504082071450400102d80700062040603034050342e800503a40e880e11084c3c440c1124151071810030090508808114102065001d4691000b01c0d440315621740512710b00444445c400c5001d0701c0c01c8284410414004200e2240a80b580ba4501410707481000c0e0f5540c61304101908808400c9448860000c0c21012550384044000010401c030300d480b42c10841c070303e100039140c20320450021311000360000c880d00240b03200350000564607400075180f402219003890301602c1c0b40c2c44200300b07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 523343938 1250 523342688 523342709
    0x30c060c0a0839063c180303090604150207050a0b06010f0f02070909050c0d081c09020105070b040c051201051e01030302030a0507020414010b120609061309020604080303040c 77
    0x10ba80300d004002d8643c1203403003522005032405a4402014603140400000212000d030308510340c0030560300080021550000ea05441c030201481c181d070214006003510442d92085400504c1802180c03c0c0010340e658000d03a1003240c0501309080f600b03001d8001e00030340f20302074030600c02c100102c414081091440c0e4051042030ba40d08980d082140415102e2200c10420035005034414401003004070312590002845500c200c1c243c0e9480e581c0400014280e01190350300341c0b244c0000040c0d041c40c0d8800981141841b201058007400180744ca5000600103005900d4040c01c0852100009020801207581c00e90203080c005003400c41c124080041d0701d000700021a1a41c3d42c11012003003003e40d10f00c0380c0380f560b81280e074141e004525000c5259812601c81d0881242242c0168440807032028a228080d02e550107440d00756100341c1c0b40e0350f201e0744c3d004040c03c02900e8140200b002d8030a0010390b4903034942c490031504038084003003550445407001c91070720710a40c0e02600050202206002c104601e0700b030140b0484050440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 523345188 1250 523343938 523344007
    0x30f0c0e12010506151c2405090708010501051c0e0c031608072306041205010c03111905120405011415090414010b0a0e1014030c060c0a08 61
    0x107280b401c9401c16035540e54070080c2803910005041c2e112008041140182d005505e00c6104007030f0035030030b96208880b900c40b1400c1d15031080c2240191048031070010001103e10080c1c03820841d4004d045501c0600505041040007e403241540030001c1903010642410310b002c1280204580b0b28a45039690050154400e0142c1000d401040e10004128805e407000c80002c1c0100c14038107130301030403858410240c4641c49c58400b4140c50450b0f0f900000b40c4001c040d1205214104a510b24155084804030000702c0245840d013000d5107208010301c0190f80300d611003416080002c0020440a50b081d00509102d02c0507000c5c4a8100400c201c3c1c1074000980030521a414400c460300c40c459001301c20210070244d02d40060030788000a001c03a100d0102d400c1c44500440c00050b155144030701154001c200303a0800d440f1544a2001e00c41404804061840144040c0990f00711807004100003949071211041030511410000c659650320b10300c10321007071503255400038403035566181101d551001801c43d858219042c042e800b5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 523346438 1250 523345188 523345219
    0x224040f0503070302030318010207031403030a0e1507030c020106050415140108070f0e040b12070e01090209031b06090901030b0601030b0904030215100506070602040e0117060f0601030f0c0e 84
    0xc1d01c0f03425241d00030f001d98100010540e16600c582032032600f6078114400c072000007002c2034185442e055038a013040b000c2c6569151a007222820f0b0b40340318620607620f83c03140000e4802e01d62141c004d280c11007020b2801050f080c8406a040b0301401107500410303481841c08940c924507941103094241221200c103010700200010400644100d07208940e0b400c01300390001081c4417594414001680041c000900c0000ea03e034071400462222461000d003030b42980e2000d1818441701002d11580c0307004040003e410b51515161402003615402000c662035180900444145190ba07603080556000680c05030902e0219079480c02c0901c04510700f601c0315030219242000b00d0306103080040b022441285c054009110700181106a1a10f0b804000c0c19651991200c0d03502041a560743c0000303060582c02800b000d43c4030b43c117003002c103080084180c0c01840c0d081c405140c0401480800300e80d46602403407481381e110641d82d4250050f0054554100c00e01d5400b8a0102e06a40040d000604002a50019a0300c6400300141c071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 523347688 1250 523346438 523346443
    0x18050709020f120421020102030601081501020a030c060e121b070e04081c02030a020c010e0706080c18150406121a040b011b060c0f0206070e0d0224040f0503 69
    0xc1c030000d441c0800400403c3c2c0c1041015001035001485813910110b0203682c202c0200c00102c0903149600107035000405d0044030b60340000aa03410038030f00c0e00103003684140302c00081c0d990210301c4001010301515440f400e0912116034400d20411580ba4255a1200c040e800140850f605c1107021114002c120100016440b0740050030001341c2d10510f45c00c005945503500c440745107400201000103008540340d100390a01c07801c0e00142d400b9030b0302c1840240e11040100c500600307561445248011550064004010455000620640040300700c80403650312100f08407500341c0507a12118403900880001894048206000010300c100c40240c0d0b5904025220700c481242680c03042d4001e00d0442a01c41640c002d503141c01c1c0d12140e02c1d54014106050409030000e446016008860300a8a4081d51f49110b00029a00300c900c0c00407003540340c07018200300d00d09440b018040b0a91611140c0c002c025100c1440219185c07001c101c046006a4280e0301d0006160390039907049c0782e000f0b010304410200d802e1000181400e00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 523348938 1250 523347688 523347697
    0x30e150c060105010e0f131523040b121911030f0a0201110c04060806010305010b10090608060a03140c01030f0e1c090b0c010903080f010302240d1805070902 69
    0x6800544801d0f480c10f001140c210f05000c1c1c8907980290811803000d8181e5410034054512111903802240f58546044460408017444c1d00610402004100180e1803044202c00001034210844002525841701d101054821084a1018000b40f05510006034069511090021500c1c82070801c008046840c2080c5529204040e01d024030580c400a00c0b04010760241c05480c1e07a10980c0c1c01226501441d041c001020703181c0c10b40c08000141c00c0100188140142030140d5005040d055504881c4d022000c40020542c518622405080045c804045106035035420030b030400454000b03600a040d40940001c45489080b04055540070070f10700000c00c0d000302105d01072040301e03030000c070090000110042100a00169609120f20070043d80304004912201c810000c0c20160720300d0307000040d0121240c54051300701080034254140070322412004100580e6524203407506074000803882c1c02c1603041000c100c00940501c81500b41c0e1181080311a000c0000d07803003044c0800901910881e1400ca5803400c3c0c4c0030487c40b5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 523350188 1250 523348938 523348957
    0x120c040501090c081611010c030603110609060342010201050f06030703140109210f0509090126100c0e1e0108040807020603010b0a12060501020d180e04030e15 70
    0x69200024030040290700c5003440ea45d00c0c0c0c0c101400896014580c03c0d0840740e5113140c0b6400300c0da80b1841801840001d00c01440070500a648241c07408641d480020fa840c00000d20f999100c0c0e40018140c1400e81001089490040ea81d1500e901480420441e00880d51031141d4187e005610348000605004d820880060140901801511301c650464540640c8520310402160707a40d0f403a032000b4000105e0360580028503990102e004042d0701c140c144018030000c50304072075608101050211003925034440300e0040c11558001c070510080c13138003040320703101c0140e0034401507245000c7c06014009011050304640d40c02c22259540b400c680c1c42240c104a08806235a031460b046035410b4043d00da0950180006c1604540218412402c042c0f40b6030018107141d1098104840407000468081105900004407a2022007500000d1003030f5800c0c280000d5036040703660b010004011019402c1c0007203203641074168000d40065540c2c00804d141504001d01066825910740e070058600c0101e11020501c0c6a003038512440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 523351438 1250 523350188 523350197
    0x60e120d08070c17030f090610060207060f2c04111921060602011b032a030902041503030f08091507050d14011401050403020f0904060902120c040501090c 68
    0x88401008844a800c0d91a040f980d400c20700320344e80b0b020264000914803400301501505154500071001c2820030001929140e00141020303414000320b9000b14264050310070524001c0c1006101690440c0c6966181c500140e0003010311006944680d1b010075482038190003a0741c24025000d501e0042ca80c90701c40c0c3c822140c405030b001c030315003801e0b42e00c11071042007400382d2a0b0600300c0a148031818842200c00b1540588051303035581922607586441144580e5040b116400c003001202c00c4448044000ca400c0103200b01030000340303500304060601a620801d44150007074010024000c44410902000d0030318001500070480d440d40c0d444541d807140c1009449114031201928460500e260a030568000c054080002c0c802c0038001500350081c54400c40f00c40c812150341106d00b81d403610311207441700020305c40d130b03241004004c0200f480075031034440b5112100351080c3d9003150307180c0e15418060001c00450b20004e622100700c45040d000c1d4840041c0010809104031002c0006903650400d038011607044400003004207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 523352688 1250 523351438 523351441
    0x5151809070e030f0c0306073f0c080a11070c14010507060e011d0f070608060325091113090504062c070803090f10030603060204060e120d08 62
    0x18145503403040e07008195414400280740070307140000e0a2103907180c2d0012817135106805c3c0c029903103410030401e6000300880c01e183c40500480e407084007104e01c500d400d0420482c000800d01122400040e9010081410303d4400c10406003040d400500300201a2001d82c82f0b9401c0440f1007441c010000200c40d8140d80c80400780c0207052038000c520b0318601200120303031705100c01846a41e011641901908040400c000e000161130031141c020100200440d89810f2000c1d0311050524092040001340101601c103c0c3c2080d02c80350341c62000017460407012803880b500c41d00080d0040e80d9504002c099003820389200290501c80144050340d1a4400c0c0954144903c002200340300c02c102540c1960300058119001d50001b0030114140000460856100440c1c1c20320308036954101e80c020f09d814041a4050015400654030f0405540c0c0010750711100b07080054030614540c108010898083d41c0800c0c001e50344080b0035902c0315070300ca9000c0c4c491004075002c103024080140d582c044122020410319108070854541c080507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 523353938 1250 523352688 523352737
    0x603030a080a110313031106040506131110051b0d0c030f2606010e03030304020907050a1701080a1202010b130e19060b041805060705070312150515 65
    0x4160041c1800c4840c540c3e418800b00d5600900004610601c81885082170190051600800640314000c402070150868814000016404100150010188541914101000e007001000a020100c059900031140c1e00120001e030f0300f000280004605500492108040f4514080e803960807126044001408100584002a01441c04001402e54906d08054200c00c8805071032107005104c55444650f90154080000a6a010050303458034030041c0c6c003640c02c0d07040c1680811241e240240c107250501c072011580c00ca9492103442030390814107012a0210240d69507541d510348a01c074004040e80c01c5120080d00c280d03624014000c0700c10300f072009400354002003062a1020003d004a8020001500800d0100e1540d00c1d1182c41407480c05018210029012542c0c01c100406c80320800395075420a070001407004040745d40484c078554024124240070707035a180140b07801c42d083e841e600c40d410141481c11a480d4600403003140700d0410f4400a071444500344c80010381c03069060040c9040711944c8002c0815040340c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 523355188 1250 523353938 523353947
    0x1015020a0503030c03100b071a101202040e011b1701060f0e150c030d02090a1e0b07030c0204060b0307110f1207060e0a0b0405011103010312030905070515130e0603030a 74
    0x2d008098941c1046d84a0b02d96545c202641e00030402961814418034544040605c000543c0d5000740a9080300c0e9141d500c4d0000b92008142d011601134402d554840f000c03060038900707420203070020441e000e0f02210010b8089020300302d0f0000d043c040c4000c1e80034000115190303015003e600307640825a29601d00a001441c00c200b62041d1427408408540001d02011806c4a4104080d016803041000e001d41c50701a64400d10a1745842640100400303120854030701c02c801c074108c42150a640c1c444d07030b50507610700d52800d00341c40500301e0b0403001790441d00d05000000e84440f5840550301503039840c1c0e9103082119083d1400d0b96a07408032030001c54a0340040100701c0072a45000010081c4503c244004200d02140410090411a681006441e11540740080004020082c4102540c0c09258400d450641d4199141d400080d0086820701c020b00d82d4540841041c0101004041c0044c81d00a20601c040001c964103070007030f500034807503200b06030380c0c40710003c203010300031a08a41c400c030030180056042c49400c000444 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 523356438 1250 523355188 523355191
    0x50405040201020f0717160302100f1701090e1606020d0f171302031002120a090212070b1b15040807031101290603042301060e1015020a0503030c03 65
    0xb41544a40e219018180b00144850340007010150f03440034440c1c0d100241c2c94201104d00200c0f10040d12a540d042c80140d8030711040c10036056492522146401e003611081c0c1e03e151504d200070903210102000080c562540d45c21015041e03400070140c1d1b0300780d054529120b500304601e004a0000da00718402291905102c0c8040c0c502051682c03500840720b1030240c1000510050503102801140e04061584055080400c805449031904510451800043c00004a0000c0024100f09103058495080030305540d24540343e0400c000000c000c0d40c034000c0e0781e27907034204183e4031404100c1141215034080e00f08114010645103285148101801c51a588664480240d6071062404400b48640f1401e1550032100901c2060032841ea00100c1c1019840500309403031180c40b00f07243c101c1c400c490400c01c000002d24440c0c0030500f40d031900c02e805040e510b10500c10034050285d68202000070201c0c0d5007040340706110410044101e600e040003103100c005103010100e031034032020900074041d0ba000301701043c4a804000b0003103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 523357688 1250 523356438 523356443
    0x606061110330501080115050a050f120921040e010311030109171c180f05010605060703090302090603031e0304020312031311091306050a2304030305060f090105040504 74
    0x4000031200d44a00d040c00454610b100c1c0398040c1940d0503c51542c0008160380500700d051040196001b60000c0142640301c2c03090301104008000c5041c01c0888541415116561030a0243d42d03828a4100d03a826912561002030007245130100507421894800300c4210750980c0e000c2400120103a00359241c81411480340b036561600b56580d2513201c1c010482d541480d8150aa51109050b964500c2c0300c4418560700b81c0c0007010507000d141800080c0d400810351440c9401c294088c1c1e400f14441c540d414098010040da6000070303080031001541c5400c16902184a2040d0b81c070850f2840140d8840302e041c90b0b030301d009101050760483c0e0010302404070001e002c00519402440101110180405030ba5250401e40081c1d90b019108030709880c03140104004c3c3d8416220300c100640b1900400d01e0300131560351403252084406082d4540d10303404680580000d40009280300360b01c0701c1c1190f4100c48640c44085001301254140d0000340340c40046a81458080b19880010344000d0200c1d030540d013840e00b000300906001c2d204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 523358938 1250 523357688 523357721
    0x1c021c1509020a05030702010b0103150e180601121a0702030301030b1003051902031c09060f030f0e0f070b0403030503063c03070509040c090203060622030606061110 73
    0x14101c400340000d2000c1440c9954817516410000000303401d483d51034858034141400c050913001140159001c450446144184081d00b41e11815021014003100000d505064080c20002068441c0b140b2564200d0b04d00c0790704500c4e00d0311521100d01c03450b440d054481c2001130700100010800b04480701d0a00d078102082007000002d82c0d540b95515071074083c07043c0c14401850714003400c1009601e424801514070810806428200706080f100041c0070303031885c0c014030052000381c004c0c481003944668880215042528000c01000d00d24818050b0b0398a1110040c0c0c44a00c00c0c0c17000860035a078140c050b58200c96154498905584441081140001d02000901031301c40340798040040b2440071443d5180d5803490b444101900c074041c40181414030300d4540005004035049001e0000088011103600704030b4005050042c6c494950400161041c401c1004e010003004500307140d11140d80103120300070100ea206401c1000443c0d907801c3c007501e05000d14103d00c0c0d11358000501c0f540c5141d030b0360340103400301141201c00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523360188 1250 523358938 523358981
    0xa034a1c14040303030c09080d020a031d1905092202010302090621010f0b0703020c04090303090510020a080a06180b03121303020301180b011203020309040e031c021c 73
    0x207520725904a81c0c02540081d132942c41040c116a00301100502501c514400f1340301540c0035020103035441c080c126005042101403d000e03203007462889a02c0e401d0796001800d8403491340403403c500020980b98003450303114201120110f80c098014001180310031440b10155076681642e500113400942043e172440d50003040c00c205050303036800c1d414500540b540e01d95403016615410201c801407110810b400451140c002008010301282d00001d0000f01c00030704a50102c0d880c40035103822400380c0394412005040e4803030440c090347c0800041d005400e515141d070342c0360030041e0780d680b21100a5603041d10610342c1c418143c1118050034041a04074080700500542182e03204c000c8034038506410f80c00750800964034a03040c081070007149420300070842e10a440e1100406401c080b516031921000c4184984082212108010010907000303101382e52070a60000e008200c0e00e030441070311030745030303401004003600b01112a03581d1a1003038010320907100303003260020301c001c120380e1600002c10003000c840083c440c0e95200c035803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523361438 1250 523360188 523360217
    0x2104052515020303070215010810050c0c06010b0703030f09020105030f0a140a020715110f0d091203050f09161a0c0a0302010b1801050306060103020a034a1c 69
    0x180d010031036095900940c0c1c4c2e40b030900b200908008807641030b034441e89400c1e001004031501c009040d000008100c480010340341c442d908042e0543c0701d1050120018080c00300002500150303180902001400380e18140300701141d01b0b208108032017200700024042101440400d4903440d640c41802d901907404540001d0f0654903200182004d03004440c0000417070380001e009800c104c40461050b001d01d4024509005001c0c900481d20090300550350000c04040700454100765144454000242c00c541106000c520030340c80b500300030050718086506071824603003000810500700d40000c1503c814454000b00503c1c09090906610b69210303603a541084010040c0010012641c0500111050f144250000941c16201d0410700841101e204140100100b00000402c503070380303020501ea03038849024a40141d448000c02010380090030f03206c21160414940c8401c0a400c00340ca120369420f4003082001100310301459951003158004c511b0140f007080c1d04405604100801c3c00303122820b481c2200e041900c194180135 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523362688 1250 523361438 523361459
    0x10030b0c0c06010b0a0f02060108030403080702150409090b010605090f0f010201090b01090213050d0804050d021512010302030606060901090905040c1502011509060b030f07121121040525 82
    0xa8112131341501c0001001072460760816001a03800742c2c24005030080390715103c0c0700b03900da005522028020070000580d04007103544400c58488864054503820703845607122080f0000411801600700d80b1081807000104080b40030f8020f4411624000305550012084801400300c0504031f034000d00d05541d2100c1031080001c51003e03070715010f8103103400010703200c114100c20306111004c0caa02450107003901401078030120700041e0841d4142c44095800c413900c8003051020414070000c6401504036403201145001034035807201240fa0490380202c04a0390130781c40b1842042101e21035414110f022410f80402002190129004144c0c0240144441c07001c0541d611b0510317295000c2c03a611400182d5485141c070f000e451200c03008001800702000d0411102c1d043c4603008041b880301521142c4120281000503610a1180081d900e5645689005001c00a0202201c0d956074109414803140300e40c5008000100440418200e441282c1040041c80800201e44000c0c030703245000f82c015812a04508804208260017 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523363938 1250 523362688 523362691
    0x10b03100e0601090e03220e070216090c05073f0332060406080d09080c0f030703080a05070602040f0e0a090809012a0501020a080f10030b0c0c06 64
    0x41010a00d8484846201c0c00d2140c160040d01399185071500c20000084004142c0c1d00f416850025000c000000d02e00d00c00108040e0741c03009030072011000801916603804968001c400c11038401c1f4019084e290742c0708078140e0381419054030019038148480300100301c6c21025004110b00c8601c0d171059510540b011498280d4080d00d803c9540c0d445050a1031450381c6c18030400c5c3d10584030304451301d55102a54080d803109110009210610701c1000049022a6115405140281303640b000301e81011002010103401c045503441455020f010b282d541c1011420f094811000c0300382d004016022076410340c0e0301c040350358210809600c1004801c1c029000007070603910052020b045008000142140b41501e001c011060040480c10841d042c2082d200000b801d40c01620f86040302401c0600c8050340b240ca4615604c242514102c0800403000060014424194020001160240e803604190b64503000040c0d03056001b920480d8903e90349190400101e00d03400140c503017140b20f880c003e80c0340421084115280200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523365188 1250 523363938 523363963
    0x20d0203040b070c1e110d060606030e010e12071a011221020a2409110f031506010c031101020a02060f06030a0b0411060f0d0b0102070501030b1c05010b03 68
    0x280003081c402400348046500d0b6000c0d00e14505510f02d07000507940c040119110002e1502c1001394110032a00700300410303a5040b4692805001136800984a042c044043c0c0090f12030100420303d070000052080b039040c05002040804100107080c038a2058444441c560302048058a03c00601100f80110b084400701050003404014007255400f00d02c1c0c00c1194100034808083e0303da14104044440040d0b402041c0c4903d0702d03400c5001030100c05c0342c0000115000c49415138125100e4900300c1c40500308542d849032003038080020313211f010310640401e040c1542c610240d00410348801315034000900d150300c2400b0b030001c554440e140032005110a0444242603030882030b40500560030603010401c005990b101c025601c4141200203004201054491607142c04000d400680f124003541d20302e1400c8c1e1031f01411503842c1841c504080b07960b41100c590f61002001680101d030700500031800000380030340c4179004803000c1e081d0082a0001108400c1c1c2140e04684c1c0f008401c0302c0340e54881c00404415a410b0101d00304019 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523366438 1250 523365188 523365191
    0x30a0608070f0501020601270c02031603020a051501030b04080c070902120f07030b1005090418050a0302060a1b0e01020c030d030b2803150204030f0c05010810080c1909020d 76
    0x1410080017908009050f000740d04000701210300901e203031031072070740d803013a00c1c800b244001804440261080f0705501c81e1103005884c0c2e8401e08401020107600240502c1042e000b082a2020803003190072940c101d850030f00c03001d424500c003d401300d00415044402800b4941110302110043c0d5904e11200050ba0030074648000c02c4110501044810203600d08142e51004086c9010403e002c40d40000072122240f90907a80c0030000041841140c80e1a180e1148458012801e010017030b090755850840d50f10038a01c0b104400501032180451102545070042c2c84442d03c2c0741c1115212004c04400c122035036121210485e0442c070411b02c071a0805d480a02a008064409035000b146507903140040c041090a81144c40d803200c00301310400200c1c602c02c6c03276000003074030741c0b21a20036581e0780380090300ca000e4021500090301c50011600003808004d407013010482280c03000e03201c0c00e034075540740c0c03e810b0414041c030301c035415441c2c0024114088a20b441c403100b280c4031070041d0844014645591190080340c002100841c00c46 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523367688 1250 523366438 523366469
    0x30507030e0405010f12030207090e1c0810170a0b01030c050109051f0503130506010b040302040e16050130020405040627090f02060c0607080a0b0108010b030a060807 73
    0x5500c0440e0103105882a9800c3c05035500d071044c060250350310f03482640b180e11140400c0300c0806100f44915801400100818007058403140c8050352180f104000d01d0094964000030700c3d04150052003468450307072201111141941c6410030203410301440b514003007000d0080703441510015201410841c0614041c2d044c4800302800c180c00507001881c2600300c50320440c1441c000e90480b007545107840246141c10302e40591a40c680350003103005100c801030010010b024140011855403030a101400850740221428022041c3c10100c4685988081c0071642d449102e0880920440d4019600722400e40c00010002e20310908020005031044460400d041c0620b40016040002d4502400b400300601407489031429491070307600f18010fa01e014500c403006e040e5100c01100080c09080e0500083e219000303041da9035070700b40194685e62110390849448011507609004940c0c1d5040d140300c4d03400108410784915489900f0f000b80d451454000500100d107554075248007241640003032260700010b218604200502 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523368938 1250 523367688 523367693
    0xd110304110109170a081b0307080c070605040b12180106080105040231090317070221030c07080927010303031a010e040b040e06070507050c100e2b030507 68
    0x2081141c3c040c286a40494214002c1e6280114040a00325031040700280d4403080107804800050f001c81c87c402c0140004a0701c10180844a002008000305c0401070710304039a260a8292100d0289000f10920710390180581c41801000206450f00544001100c1d2a044400b04400d0700f5124990030510059442d40c080c08210b0a00382d4508080c070204c14a00308500b0b00d505155940c0d030051900c4c1203e07040e1140c884205150084003015144903541140080a181038480a035a5000318903101c4041480881c0c4ac1c108003020348160b9006e02c9030032046038078001094440015035006540c07801e611610790301c030a0740400303a01e11414000b1503089034045c1c482c2d0702d035040250403100d0500410070062030310030030310b1035903070307019803c121b000300304407000103c00b4024004280104040714612141d032254205100140e41c1000103050321501c89c0080f03a80507003188080c0160004000d9000b00403c01d8084041141e107000200304202880d480c07800822140d000c48440302c1400c481d541276020802c0001e16505 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523370188 1250 523368938 523368947
    0x1602090901090629210a200a0602070522050a091703100e040f15020d0e03040b030126060f060a0e04050c04020c010608060916120f02060d1103041101 66
    0x50003500e8045880b602c485880c0d16602e203002c0c03610a01c103040071600c00c5401e20301003071480071014020f400c9524114003447c04498842850820001d0481e80b620040b805245c50a0014207881c0070b80d01800501d86040140228113070810300041650300c1ca000d411034040b1081c81460b01c115400300c00070450240300d013803030f00c0c0c01d5400f0360310840328010802c200302000b20301c5002142101c885643e0103d01b50740d42d0400071500146d000000307003010b000d65005407078490303a50003408454458840c10040c8404034428143d80e441184107041700b18030144010085141215031389415003440d26480f50f424074440a40742d040000031030300d41032850044c3c0b0610910381010019040500905000101d8a08150b11651354804070030010a00c540e800043c6110484070030f4006500900303440046903d141401c01c032035520b808051104002c1e40003940e5000610003000803650b0401500f02021040e0122103409009040d80f02d1144401d5072038540200004480524005500c2180220200a1501c801600040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523371438 1250 523370188 523370201
    0xc070b0c01230f060112020d0203040c03020f010302120c0708070c080304090b0a0b07060b010306050d0c050301110a0c03030b04110a11060a110a110c0a0806090601080d0f0516020909010906 83
    0x200b1a03920000300152015000c0c0c0180c0c0003030f0242401a9002c2a24090501074030801603010b501d05c0c000f109210410500103045015640308031240360303180722038000440480c0212607070001540a81d40200d1903400c002c41c01400c3d10f9000700c01e40b52070b000068030782c800e88030101d03802690345510020307040240301442d101d00301000c4000c55200120b41e1908403a140c6a0180c2d0001500d03440d80e403800c58076980e011713510540050a010300707404e80582c05414400080b401900c00c0314029400d0500c40000e0000d0b450440f1000006a280c102da51341440d20114010844a6000c0d03030810b036520700038510444140050701040520ba0303254950200295519402c0c000c0140c041d150007400d0007a1420000030300702c182c650580062503c01c0b00044072010076482c20004003081900702940c2940401d0081e000302d0203034032030b0803a8022610142d0340c0d50700c29035075024509c2168000a405d4881241d8061003a4000c050300c0d0403900717000c0f2601011303030005080c0e8401540d0340305440e0764400e1808100b02c600c0c007420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523372688 1250 523371438 523371491
    0x702031e071101050d0e010e0d0219030804260d05041a060112110d020a020a0c08061b030415151404060e0f0606040e161e12020c070b0c01 61
    0x340c2400d51950b10069101c1c0303161022818403801042c0032107403840e507900206501009800902601c128880c071144c0710f51503c0403860041c050307102401441521515858074682d85540da070840c0356519142c1d240d043c90440320340d9042d02d400d20700c3e1000c20b1180b840a4040306c1e081d05400181d0b81050302e8081c0316055044598543c1d00480010081540e8218085010440701c40c1800701e003004406200e03010360702c14001c81c0e007141480031480b504440ea00040e40c0e04074030b210342201c203410754a03807406682d160b00407140400c5209000351400c3d0001c06203000f540d0428803a139003403442c55603070300020001d407541c001c40e80e0489101d5007010041c000e825a0030615040d8185d03000c121160903d407240d5405a00203000e90a007503501e00c0490a0f64462000b1030b8014266000c4543c980c0c06e0a044001c04d02040f0000000051180300045c7c0c5003004900d5801004a090713200d148610040350300a001a4100e80c600a5850040c1c3c400051002d035500000c1c80c0c3c26505000020764030700c00500300c444049208160 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523373938 1250 523372688 523372747
    0x114090f13140f072c041e0f0b0307030c03112115011a090409050f060403080103021014090f03010b060409140709080d08270c010915020a031b0b070203 67
    0x43c0484c100a141300c11714200e40f02d002c21107003c2c030210780a8031140100303c401c160560140340400d00e060748000c1e00322848000c00e000d002c10300001c0581d150034a000160098002c2c42d01080000ca00b100c56010440018021203462485c3c51015203002c0300d0020540e01d00d81020a40756242c038504407046000d0b01340c201c034150240015201a06c10b500401d50101d004643d5a006035003800000c1045900d0320107541c046415031300d040e10b00200039031400c0c0700482c014160141002e4100d4010a002079004661140041c10700c01580300b04240c03401c1c1c60741c0d40e03030f05956140051042d0f40c98000080000d407000c180040380302c0f580c80440d0800c640000f0301040c20041d00150900ca0041d000c22441c400320741c85d2400f10710984425544080070341c829140890300360301141f1400c07040300c0085031308a034020003600d48801ca207a17120400040c50114200f0040141c01c20800d40c40068001c1c00507441142d00907103030147c0d62041d96641c0322019801e80300351001d40d101003181042c500600d01d10344a40d0008458 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523375188 1250 523373938 523373957
    0x90f0e0d091a12090d090812030a1a060a0302070c080c0a180204050301060909061a06031303030216050601031205130e0c09041d0c0114090f13140f07 66
    0x24000c104401c640118401030408042e840516007000c4103482c001c070b00380c000e22001820480c00e0700d9503400c0c22001a0700490856000061440b601062000000010b00c0040c0d1443d0341d070031080002400328030000104001d5074803040010751126006000103202580300103a80c0c89650a284400c0500343d4040d001d990f100c140c59102d43d890746142c160480303145c00d4005e80040035400a01000e4002c941205030558078205002454000c5900843c0156008480403c8081c0c01c1208a06240c1000e41e07085408c4842000440c42c92802480240005402441c0c0107050a14240700702c0380e100086041521180c0c08074005200b404442411014a942541411450185105800042c104c0c062080c00440004280081c1500650804580c4c500c0d1008004001d214000ba0902c04201d440c0b40c42900c203442100510b070320300d50290440361668110000c1090505801000300722b01030800100030f6802c020710a0843c0700401150260000c1021807d039480c40c80d1500c2c0407181540300b001009141005021070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523376438 1250 523375188 523375213
    0x140106230d060b03150403021c0503090a1403070501060e06030d0207140613030203060f15220213120b070e040506090a0510051009050301060501031b0e01030f06090f0e 74
    0x3400c940055400b101c045148019000024145902c0c0c0200300445400001004101680450200c40c00003600c5c0050742d6011118404480600084811a10a500001260010502003081c5e9201d29424030100c1e46440083d65900382900c089920030342d030b1640d00906111003071409002c40710298a05200801c225450001d8400c1c404c048d5001041c0181c100046038440e185119803014050b503005003c45407a404d01045110171000d0896040001c5039092078440c41600c0d0034050400c100031101108200000c802018034025405889000b012900b50f080c00144402c1d51114402c669000d0f14540c0c405107070002011348040c410412152146240600b00306040c0d4548180350f07000303d4180b500042540e5004420000b01030710b50040f03a0f020340b03c604684d003041e91014502040c0c1c0c100350020301100d640c440054055403181044412100005079002c4d42a91280359600d030713480341c1450302140825503504208200c030820703040300840544982c10360411881c940070390035000c00303c08010803000c280e25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523377688 1250 523376438 523376449
    0x2030304020d03141e0904060e0907032009010b0403031202030420040902060c010f06080712120c120914010801031221060603090c080f0c06030603030714010623 71
    0x65004090241121400654200444c00d460303090182d1010341380300e10445442c003215604419640e500c00ea04080000c05d50341c03802c000d01401001814001c0150509507910b00e800c0c416400318599100140044541e032940d2030840c414001c02090f405d10740c0c2c0b2070031424000c0042c501002c020209900400070701c000a808240c81800d118014038954107001600c2c00050060654820069401900820045448407040d070140d8240c4903000740801c02265200d031000d8071080f00c4d00c036400300848140326910100760361030326000c40c1404929044501c00303800d03031b81d19a244039050703540c0000800c242ea090110040003034000104150034205610107600d150748182030f42c1101d60030f040400180102801d800c0003003202c0203506443c080028490b0307e40b10ba03001001800a0001038450b07142440d00003e03101808180e500b907282b444000f4014001403801404000d034409407060350184000c000344d070b0214928420030041e0444071300020500d10b10780a034488481c4100e241c10104910001c1c80000300c5d641d44e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523378938 1250 523377688 523377709
    0xe07121802012a0b1005040b031903110f061618051203070618050606010c0c15050405100e0405070306120609030c0c080f24040201121e09050d0203030402 68
    0x91034450041e890103c41d00122003040202c00c10001c03260402034080100d440d02e04c0388203109203038420303442680e124200004d4502c512130040c0c16800240c09480c0a040c4a042d080c001c600904212884000f101c05061500b20342c3c2c00d002c02c40d90050000c1c07041030300e6000200090990700e8039049400755001a507108204126114051040c294001c942c42e100c841401643d012680000081005540f5110b4040c42c2d09628031084406001d82c0000600540c010402000711130380000d66501ca180c101301400c07410a2071102000e0a101c002e200014007030396410050981c00c18690703604084440142c0a020035200060801014075052801c01c0c05400344408038400401d8121801045082107802e0545110601a6018205000700080450181000210390000c03d06610446051308030860000319414841428251090210004100503611840500741310201c0e58000240800340840da80e9075a43c0c2c032074415a03a00b80c44595540901c10180010200d42c0303440d001452031844c0980c002440f0044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523380188 1250 523378938 523378943
    0x30302181e040c1202070303020405030c150415210209030c091b0306460b040e1b0a0f170f1909060f02090f030a0302100e0f070e071218 60
    0x50f280c120410461042d084002c015001c602e04568034401800c0040180d48036001d441c1c028402c00340707804d0403420640380c031218034540c02880e682040d00b0240d421030303981c003c00340140c10010343c03101e0080e000060300400350707500e800030000582d0740d0140818103040ca0029191248114104030030050014100001896000700401359555203994206c000b8552041025403402000d42c5101031030401b0404118680d000900340c504550b02004944a0200403806800790701c81c0300170203110404c04000c002d4101a040b110070694119401d00a4440700300541010344a10005082c0f00b4000e80059044050b14801e2a0503221100300c0c0e14040446132034861018209003411944241c2c0056000146d500941c112617001c2030034400380d1f03540c40d100d0010b5044450f031288a00d4214a12030204d182c0016814802135150b0090905281201442c6004144142039100c00e406041698584030001784a40c03009004084206510f0f41009603000f0814002c5c083e210b800c0621341802d40c0c0070b1141c0b80310303c010080d9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523381294 1106 523380188 523380191
    0x801020c0c0112141f050d050604021203070f05010f06091815060906080604170c0a0b0711010c08060f010215010308090303040b07030302181e04 64
    0x4039008000c0c0e03050744540107464095000d90030911031511100400210900060180340c1c03000c2085030f100d0310740880b8400c210721501d140c0321684041c0100703450920008004e139481c00d0343d40e8000380000c0d2140b00d8000c2c0d03025466200304110748074550700c114545900c03031891070114040c1941098808006040c000040f48a06243c42011003807111101903100803d055140e18240c9a01a0320390856140c9910300810502c0b05409008020700c0ca090003080c40786401d04200f0351400b0004882118002c2c108020103a031400041c403040c0e42900f0044003807040d1100442034036401c04070b441503149942400340c520022078110704914410081640c0c800100380c80d250049132114004504a496548083c0043c008240c0910241ca0301c0c410140480c0e26042c1c56403001d03c420b402510041340003980018005084506418a081008000b5140c40c5d0a10344101292440d0380f110000980c01503 = true := by decide +kernel

theorem cover : BRFrame.Cov 523201438 523381294 := by
  have h0 := BRFrame.cov_init 523201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523201438 ≤ n) (h2 : n < 523381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
