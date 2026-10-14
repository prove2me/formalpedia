-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:57:52.778059+00:00
-- url     : https://prove2.me/submissions/9613ddce-cfc6-48c0-a7a3-bb33cd417c09

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50899284 ≤ n < 51079140 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50900534 1250 50899284 50899307
    0x601050922150203040c0b0307020606040c0201060b04030b04030f0f0c0b060a030807120801170303060f0a03080f0c010b01050a0c02091909080405150313081e0d020a02100605010c03 80
    0x11a041ca08050320b80380c1c2020300540e08001c40540c00800c10091100300b8049030007820116814a20350305003818002d50360440542482d109959078491038a03190f0017580072000400e0b1400109895654a061540300103004803025001305860508006125229901c2c0400010072601c403400c00321a83d8544154080c00140b41c3d0ba0400d040320408000f107500da0010303140d0304c0d108aa5400601d140300c04000c1026406038451f480100885010500174030003c411369520035010341f101080d0380d00c10f40020700d90365000d51025021403000109002c424040354000c00b03140c0c07201c0300280118070b00c0c0710045811303200d2080c80e4000200e04454180061520400558000c5100b50302080001a4000c201c1c1c212403200038110303000700700014104214100b080440b480c44c0c0626000301e04506d4403112001114001c800005d1814400195507004400c005035207441010b211075030b244c0c466001c08802c400940c44203045201520969181000900707003402a00706070350040c0d43d24000c125050340e0998070200c048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50901784 1250 50900534 50900581
    0x60910050702040c0305070210051504060305100b0402130b0f070206130e0c0403020a0603020c010905030a09050a050411030c0a2705031501061d01090803030403080f09060106050f030601020c0d032006010509 91
    0x986004bc1107540b18003a12010307500540107000c851403429a210300703d44401c2011402035005108150300100b00900740030842d40b5424106e60360307541e0081540c0d86440341c140c0007580050041603030b041c01100022010301340c0300101400c00c0c06480740d1920300e2540c06203100003588490500b1041c0320b1207100c1d40160210f215480000314125540ea40da26040d600003008070400075242c0315040000307184c6140780c0301c010441078030104158080c00e11a4091480020600c4142e01000222000d0a40c4030305200b07548040e807414a4600508441440341408100d4441c26200e0302c20554458070045034003901d203040320465140c0c006c0d030b0301c02c0e400c0c040c10000c0c00360b61311418828131140001e012941031008501c101e109a6a00da02c6141082400081c9100541500c1040d80084014055241c02c28100c5092102030070020f80c903540c911004030b103460002d040140e0488150b180c0c3d5010140c120400c0c6144400c603845507841c20030f018108030303500e0000744107003903012150380302044102c25910302164814045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50903034 1250 50901784 50901811
    0xa0617060108060412210c02100e250f03050a0201080702030306030d0315031703070311040308040b0702130c12111305090a090503041707050a0b0711060910050702040c030507021005 80
    0xc6040c06c040b60a4110710f120361103441d0908501015414040c058065109500c100b0080c0d92209200da5240442c0803096446400c0c0c03c01a40304c91800300c41c0900030240011a40d80654691900070b07115044420224041414900030420040c000b0050360711071140034005024048111008901403c00e014141c40134508a140100104501121021484540000d680ea9a040a005c020119110711181c1843c404040c4424000200d0301c104507411989281000d81c0c448946000203103007a022a10882d20071407918861803038a540050070741e425400344500400100020780c1c0790b040984075003441d40d400804d0900c0c0078421890810000c0350030501e41c3c000060314400b20350b00c01d440c0da480368028001d4003d02d42c9501008000070889500507010aa540e116181d2500744a40000e0040004c020802403800e8050364150300c500054501c1011f00410081031402c480d10060a0307980049401d1b40598144411103840b00d00a00480c0d01400096008218046416580c00700500c0060841c3d464000d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50904284 1250 50903034 50903057
    0xd02040609020a020604051623130c03050406060f14010302031806090601080d0c20220228020d0f02100606110f01060e0a0b0604030206030a0617060108060412 70
    0x40c40900f100310450703001088203007080d0501c03615003403900d90560040c00038601c0170310400408440c01c0c000711890a68809000240000007440b210400c81208010351800148605660781038110501850158404008440d10703009a140c403103030140108518402e1404410000d035200364002c660200301c00480c50107600e00c0020036820004195848603517984168012722080e50280280d0610004038109000c5401407a96444118401000800c0d00303162921208146a10780110340c1c00390362062500010944e221010030710003074220581401d5050502010000701c001140f50420b0100b02940082030790040c0000c0c06c13070714100c80c08401d90850145144090100c1c00c98003d0340050982612106405010030f4111403400f20b1141001c80300341c0c1411020040941c003054584c1e041604103c010900c0d180c00e801280c000c0c411507100a4000c8000010000d500403035501500c03c3d1040e142c82a54003030200c1554565500080c01501c000340c0090b0040350004a0302d0800000e904828200400c1402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50905534 1250 50904284 50904299
    0x912030e0a0807151814030a02030106260a02030606040213030f05010204031106070c0e060607080d02040f050d050c061804050f04120309030206010b22091401060e0f0d020406 77
    0x240340d0301950043d8424038091003964001060f00119030004d24001306400402064418817000740d101c1c0c02c0300c00c0940e52203070016460511291300c0da0f60b0003070300038408140d41e03580301c83d510715003500c1400070a18881441c10f52804041510120740e9001402000c01e91601402c100082d03001c07540201e8540246400040010083c1135000f060034050000140c8651550409500080c0595800b81c802c141c02c121900010700703c2501d160980344540c202485503075072080807904c0d41c842e9a00142000c480800c17820860101a0010300a445a511307240078040e50707900521840b00e074404401095a0024512103d1a040c682c026101001120025000f1211080c003c2000c0703c00c261101e0510101210401c001c1c401001c003010f28058003490700b001100318030f480094442c0b006000308000108002000114400d0212590b02c0b80c0c51000c0181071a90b65480c0311070002c150001070408444044400081c0c401d00940007030f24401da0140500c0095a40002003084008854204a905c2a500d640214180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50906784 1250 50905534 50905549
    0x8070b0703020702130903030c0806130c0e040204081b010302042103051902010b011103130302010302030a0e01111209010b0607060e12040b07020a05060301060215130b0403030504060506030d0912030e 88
    0x5502c02d000540c46c0041c0c18000c0a90b81c50103031203c240b240000900c8119211a0104841c182403000c0004001025000464200c110fa0030500e5100b030000c81d01244d090008212000c410898290072070aa001c00c100643c03e0740228400c20b100c1c0580a081c1002000c98240c01c604900d03c6840c095142c404800303d100c080b00f000040340f00040c1e545502030601c650f0010214207030450070000840c1020f2859110744216021400000e04241e004000b10f040c0100540210310403115410083c0070b5417101024248140c4c02c0313417610403054944c540114500e40c00c184540d80d580240030300b403a464000c80380ca072400034200c41030fa10486482014500c0c10790a041e1400790010b4000c40d1003a582d44c80a90040040c400c0440c3c0056101d29000c0004215044d000505011303120b030300f03400c94000ad60712ba1840400c0c0d2a0746c000050128046982088105603040d03201a1103503100f00d030f0030082c649651050603600d159007424400815011503043c4814141100307441007403842803411602507001d003c04103030038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50908034 1250 50906784 50906809
    0x2092d1e04050f03030a02091309020a06050901030906060311030d0305151c05070b030601030e01020909011205030c030f03060a09090201200c03030c0a0201030605030307030518060d020a020a030906020a08070b0703020702 97
    0x10035404101022546411300c50f272046001148024400496690009600c4002034824a010b0200c0015104040c0c0d000340c0154900b103800c120108242c640e2814041000300b02c54800c9840390141c80c0c400c0030356900034424036001d038820303040300c001e800c3d098000c3c007014014141d403018600185c00250740001702c08020300d84c00340a01d00700107526820302c2c40c00901079449204d101181640180081c203c940c031a008440c0c1102c06025000511540600b041802c610030843d60500f43d002c006019881c0e40001c60046000d00e406030b0700c9409240e5188000c008407010700c0304c004e00248103411002c0c070411007107200c5101801e4070015a11500100030000340b541c0d1120500b044260064003400041d50381620881c402003c0c1074025600c0c0c1038291303900401a02c900da134001441841341c0c0042c019a141c410540e8100c28201200b15170328000c40102960300ca4006904a002818105012428500c003090b41c1c04419400001641403458941d59810408801444401059401c0c80401d01507034845c86603440303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50909284 1250 50908034 50908051
    0x3031801021c120b01140a090f0e0106020c09090c19090c110703060f0b0604120b0c04060c02091308070b0103050c0d030e0d0204060302092d1e04050f0303 68
    0x1402000540068140284001ca0005a604400a103030300290400d40a1142c6101c25070b0001c1c04042280042c2c5a418040c844410a0413002ca4841445034010003900b00ba5020480749041040d42c508000030702c01400d019000c010b0f0420007402c0c01354146503601507004003455099801c000b101c0d10100b5601900342c81c0c4c202c0b4107007003070504001503291481204044020b0389400c9001340419015195280326520004020540c2c40d044943c00c0030340c03540651180300d40280040c0d510340d56001801c10321140c00d04155680041c84020468280c1c9842c11107080301c3e65511041d080d44840c0c3c081140025004004d011010500030170100052150030023040c0641c030400104009504606102e4034148440204038000c0044010380d00c086030b0001c5c44c18201c5001201c070000143e8140c07020038081c1c0929400250000485000e00c007019401d84403a4023855943d5204042d00c809000d1400300380b98040d6401c89000090660b1120200500034090798018050412601200a20403840d0f10b16402240d5602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50910534 1250 50909284 50909317
    0x803030a090b0a02071208070c060518010b010305010f0603020c070503101b02060903030a0e15010f0501140f070b060d08030708071407150507140f03040203070b040f030f020f0303 79
    0x40402014103a0342d9041158280c0440c10506941d40318000c1060404c500c40c01d1003102000107000a116442041c001a403028080c440c4c1c3c02c0c19070f0030f21117214400040001950800d4121072044d40b19218070b604a406034140003d88518100c4160001d40c8481610705071800b03600008075494800b000990070f80b0509403000180f80ca90300000803181c800c00007850046421003030034802440390000c25650000c403032050001c0d0301d40c1d41d54922890a00650102c00c1507900640c00058110004181ca078201c640c283c03540303035550740301301e814042a00c00d104155100320400c1c09441d001c554407000070b50380864064041002d804040c2c0790034869800c21201080000d029804104490b0707804000d194002c1d560b041e80078105000c0da40d42c0c2d40d02282c0d00055602c010750f0742c3c00003038005204400c1d81c4501c01807403031503590b9044003140310748181d4002c440c2a4040c0c810f1550000780842100304803000c0b600e801c03461074506800c51390b03044081e10704014240d0340301c0004c0d1245132042d601800100015110141d010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50911784 1250 50910534 50910551
    0x3040506040219060210020f091906020d02031e0904060e0103110f01080105010206040b0402010e0d032c060a0302070515010b030402040b03060705160c030602030c040e090109020a030303020904060803030a 90
    0x8407201d581d02e00026902030729004100f00b90740d0000b41c01d010801d5100c41c0548c0364480e2401041a502880c868540d11001714001c040ca5082c220301d40c0d4043d0345040c0e00740c0e40c0b0f1651440040c0d94920400032040e910740c210000850a01c00050041c020380003008002043e00d036640c909070300701c05030280c1041d9880c1002c15001041e901d0846503008211000b801d03e2a5103614140c0040d4a03004020005403c203050340340050210ba100e1008100003c40062014060140904004104450001c0079107140110900420b961a803095441d1485034401003280f03180c031318456022006500401c1c822036562086108418411844d40302c420301a00d8032500340b03516440e003401004195000c140b0054025040107041c8013809a00904503640a0021411030300c600c0b1991400b2401d081c2243e201810b1548084180704201c6d04090050007102d800001500d4503859400300c2c01d003250300200c0000c0d03110620308400c1000a000f03030003a003041c0d08001c0c0f0005046a40f0700e03000f815075100312020106c442d540c0c20003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50913034 1250 50911784 50911789
    0xd0203030f0417070608040b06010c0615090902030f010902060715060b0415020c0a06080c0a0e0d080a140a080a0b040207020a030303020405100509030a0803090f0114011412060a02030714030405060402 88
    0x1113900402c12890414810708060b19108400100034000034100040345001606020064110f031944860000c19502c0f42c9030f488100300d0041040c114128443d0090180c221300941d01400f80d01c1102c1c0d001016285401456600c980c82000d030500b50403052611100700060540c5020080d00052050480c44000c00201c154001d0408070203100c1c1c9841403245440c00d00031b4a40c420080c0f40d10134613520440e0b507a038001180c2580d90140460f50349900c441110304e66810061800081c1c100e0901d40e40700c1d00344490310002c1c590014040c404200d0002171400c00020501510703908202080308019000514014558000c1246e0900e80d810a170042500014100200e00701940c2d0600b0f5030f210743c5042070a0040c0040002d031a0144100c2c0035000207408008215180407d00c08040c3c00d8000348001c01c58250240054200d1402c00d01c504a80589041e5950100c2e060070303c40c0900600600000c1e210607540c1003042c00003500050321000801040080c44440d000c001002140203034014402400d40746402d204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50914284 1250 50913034 50913043
    0xc090a080102030f060f0103020903031b1603120c060923070503010b030304030b041b0306060f15080a2403060501080d020a02131e020f0a0f0806010e0d0203030f0417 73
    0xc0034034240e00c100208004205100669900282c044681e510700c48006070048000c5d000c5e280010b44d060000040051403039483c0d42e81d01c03080d4134450003903420a29a205041000c40807510020b041000602c071801c455910400700f6180340c611940c0d001490802c3c2e5115036400c0400c0b98070b01c810040308003100035902c0c001000044020802200244a05001400481c0e228001c40c80b00405141c900c0003c50100011071311240114506581000390b00c42d81c83c00c107200948114490084000010030011819015250700303100192100d4640951a07125110460014002d42803982503441044400d00850076030b4084180095006007000b0800754106a00d040c14441419514425036010b64050750040e00c1e5480b5202c43d40070200800a030710f28038001d0403034481000c86100c01d6907a1000912002c0440c040b4081c02c9052940d980b208140c411850301a40c0c00541030f40c4c650301161b0b5402c80c1107180d20b40603110000c468800340649003400742d000c170103010399040354000c0c520301c10b00f020411908030400c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50915534 1250 50914284 50914289
    0x30f01080601050f0103023f010f0f03390801060b030601020715030f06030605070806090c03010b09120307050a120c0c060c0515100524090402090a030b0c090a 70
    0x14081e000551401001460b03155000880700d06068000c1000c0350000c1500b007880c080c3c1d12010245007450092000c07030340d48500b428210340c1c01c00210500089450300c0c110380501300b43c440003035051150504644138602881007510080752405d050084402900340740c1440c0d01d001c440740000c0100c14074103100c407490a480c1d094002c001c5100091082180d10780e40000d81c0c404960481240181d5220a00d0040f03003d04205407100380e0310b03820508000204008c5a001310722405255481e01c0003a143d040400c4004041999603d0086800348014012104503d008040c2c901005102c010316190784001c107810350304072607404c1d5807540007405603100740803802c01c41000d1080d042c03400c41105c81d401e584a5080851500505080140c01e0010b1000c1090030480800020501500400240b46c541c0404948101034011980910202c0019106a401c90601018150652a107441c1000c03000b42c1400002d410160f00e00d03610180000d40040481c0c508501680550700382d01d0541d90390440320003031103a0301095a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50916784 1250 50915534 50915549
    0x20409151a030a02040b0102070b0403050624130b0103021e030f330a0b190201061706060609010905151e0403020d031107090606050309010c09050303030103150f0c05030f01 76
    0x7410041954040380980c00c00ba03044400040745007804004030b1401071250007010003044001004828040b00040041c030809051050f0f00310200740c26442400c6441000d0f034140c02c4115030000001011700c07900000d011081c185001420198180d01000c0b40501c1031300503150b100c0d800020701410b02c0000c03d949a0054102d008400c5152a0440c5c0c10100754003c0d20951001c850303498002100e503286040275000301a05a1003940f01c003070303107086c080040070540840c20240d1f18000e4000b4568061074040146101c0c00006080266100801c0c440038be03000307080d200e041041e40d880100307241d41e601d40422524281e042e184d40c0c0702c0c4022120302a440010040c44074400406100400040c4e840c0c4c036910600395854606006100b1003140c95a10f0603005030800c00c0110708110000c84c0d4a0b902c4006144101d41c032400900c021171490005503120312403802000d805400402c01800403c98114a00c2000444a0400a40c03d0a506421000c0301c1c850664030000610020070301c0540320482d0001c6002d030200c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50918034 1250 50916784 50916821
    0x1b1b05040504080d020705210a0305060a05010507060b030102070c0807031104020f070f050c09070e090a0608060612030403150218090105030613020a030b010e070807050a0f0507080702040915 84
    0x1c0d403141146806a03030f894810498000031500c00f0807c00744141c480544c040b0904001500d100350281c4000c0d00319102440000b0b1030070000a1081c60003034028402c5550685a051900c50300341c46003c0600012031000741c056400304010b00c0010004101a401002d40b000904003903402c6107080c2402c60810100c0c0c2e4805c90050200c0c004a041c0507003120002584441c2400c0030311200e280507810703c2c107041031041d1300651040802c074400360030050301c0001e400202c45c070085907991203071008103c41e40750003041610340c0301c880010000e003000318010301c005083c441180c1c00c20b540ea60314030700002240c0c3d50b2846101e0b00070501e290751000e10030701800081c000311001640ca6042c070010942c1c0341402804580540708501d001001d6485440000000d0342d0000703024801036131100d5080a0000c01540c000c00000e0140780041c03106071003482520034890941da12410190000507046959400c0000241c40c0540c0c108a6100141d80d10721407006818410402301030300c0060140000c00b00d801c208013072001c1d05c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50919284 1250 50918034 50918041
    0x106020f0d0f0e1c060b030c030f07060f0219060b04050105040902130218060708040611060112080912010218030c01020109032a0c08062a03070309031b1b050405 71
    0x300181d85600000c4103140c11034003983c202000032a801c003589031030000c08150560b100c060105a810000c00c1c10402c0d4201c0d400385032140c0525940d180e03036950740e401e250445c100a104041c4614804050003c1500c120307400e021441055814900400b07108480090340c400d2007054504007805210b0051400710783c20010003a854000c9500c403104000043e1f40e050b40003520102c0a0104d4030782c4015401d01030805a250003032032503c1d40690348140604800b20f4070200d0680e83c01c140005e04541620000e13400c51004180e20364a21040d0342014810540c094041001013448203801d1000d0030350108025181c14950a011003032500303260342021000e0440e4103160107440401d4102442c1c02404130740b01000d0907a003881c0030241903c83d0035a07070020480c918104c00043e00020000e02b02d40202818400311054079070f5074107540c0b0680b1541c0c0c00e07959441028000100c1c80b5000e9446600b2040c001e0809110801c1038105525003980d61103412030328943c442d01400340110b80014510b0180c40190303400c03c984d05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50920534 1250 50919284 50919287
    0x2090601050f0a0f1103210c040308070f050c040507180602070f050108090c0d0f03031503030804020607210215180616050903070e09010c0c1e05240106020f0d 70
    0x319050f2484284404416519409407050004a0001c42c0300c2c4191794a40d60340c4016090382d01d170f80042c404001294940401c040b001c2c89801c403002c50f58040b00c0b461500303942d036840a41a203410a41a07c0b9030144645101050311603009103071048681c0d684919508540d954402c00d849030940101c8115808a2024400ea030004030211050f48c400b420404100e99a100ca2140340600c801507060300700703221400040030040500034402c075941c442d0720140542c50380100442d1002c2c007540300160000d0041c4001c42c02605100000344450b6025840e841d019039071140c211580c0e18402e41c05c110050b4842682c90b1010051001000e070440c9041748001188901600b0540d5282c0000d0a401703441c0307500014040c0500d000b0822502c6514014040c0e80116030358031121489202d040b40c55880e95424003001c0d140340341c0b107661400388203a0303c074106030000817013105030300f0340c4410620084945100c0c102d4008000502508110b04a90f180003624010b9030412500a003410540c400c00b0301198040105c42d107815 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50921784 1250 50920534 50920537
    0x2011101140112050c060c0601051c03080402090a0212040b01062c0f01020f06010f06030f050402101202070f08030403032403020108071e110601080c0607060b04020c0d090302090601050f 82
    0x1540f4200c9070303488884090400d03505010a0018440d0301c08400190843c0180001c11402e0480e102240c0b00401114096903002488034207030002400a10104001401440c080b6001a040700540000608100e19481c0e9641142d50a4909a850036014001004010790001c4900540809100c16051191480c10b0f20082010500402c40c8030301024100c18103203901c00c00c0040c1c00c54595800703e840d10f5070340710302c4d00f29031035840d0007804006401e180c001801c40c0b00601a00340035540c09807280071020083c5130101c44031030b1034010152400b40c00300910070104410300104420f16018200f001d55078100303890058110380d10303081d0002c0c040380d0103088031840300d1010080764101ea40a087c03541c0360751340d0010103c0340360a00b50b104803101700e2141e507407110385540b0070340034a410031802044a0981e6210288517a070f80219403091507220f80c04124400000f0303105d820031803512201070400350804407407000c81070901080c580744500040da184020001d615240d03c03510741021003800d05c546007145400045e0031a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50923034 1250 50921784 50921789
    0x6030c1e06090301020f031302010806120d030f15081e0a020904080a02010609050c070203060a0b0a1809350a0c020f0a03170c120a020c090406020d0f09020111011401 73
    0x700320108194000303440a404403101103202018082ea240b1300081e42da60209950502640012100800109103040c4059800d18850014008180c10304a80c0c42c11000741028028680e141610b0300b483c000400e90100700c44001c3d0401c903002e0080700c00c550049940251464000c1900c0e940803245100142e00c9017055142c000d41c1203400c5943ea074502d114103034054040c03503202c000c0c0c0b103180c0002c0051030700f8841c014180c1d140c0701714252400c686901d10700e403003541c1446c0d12a95008500000400c4040061091b00e0303902e10b406840400c00200545601d0700c5040c60308416031090800d154003044241c2c055072584002d0f540c084140e0304143c4606001840741c500d0700d44c0240074441c417440c003d9a60f0b603455681401540d220102d290303458900c40c800312464014207000700c164424000142032041852007514900180741e2b0090069160b40300c201700400c01c1c090803c0e940d80b0b5081010003140c00640c01400201d000c0c418000c80d1090040c80014102106000b241c070190745450f01106880c400c3c100e07113904 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50924284 1250 50923034 50923039
    0x6090304060503011e030c03061e050601020c130603080d09210c0602030603011b0509010f020604020d06020304080c0322050415030b090c03030d1b09121707050f010506030c1e 77
    0x613101c05e81d02c031038806090250000b400d101c0031444000200718860f0042c4c0300a401144c1107448081a480c3d80c4410740790240c0d0000e01682180105a146003407a4540400d1003075191404980c0c540d49850303002c41035200031b50140e22070744c07a6a0844144050001c20415000500a00480c0c8124850005000b078a142800901c0d241e0000003184860342c0075003104100c1d00c20f0310900d0408204103c0060003540c0f01c0c1030114080303000c3c21a0041e04a0021800920be40c0c2c002d8030000741c3c05403580e00e450003940000d10031504244248020524003000b04040c14010080807500f44480c2c0340b001c500d070b4048040f9482107226608003030041483c0715500d4110000c90f54850000307400c50301c8049042d800e241008038543d170103100c0824040d00b042d0154206101110074583d2200c0c41c00016642203e868440d0700501e01d018a03002e0f01800001c031314204540204081d0005507081c00b44994a460510007440c00b140314907915642403050394542401030317140045040b00e100101354512240e80001070400710b078a51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50925534 1250 50924284 50924309
    0x30203030f0a02041707050a1208030c0708130602060901050a0c0c030c0c050d0602030411060412030f090f0602030c0106050108160305060d0602070f03030e0102130e10050402030a0606020609030406050301 90
    0x42c86440d00d601614003070f03c00c1044102c0382d07850385510580e469041c1d1144034410701e00560300042402c01b521252034420740000391f503032a6660f0070600181f1603000d4401111343d480c3c200000601c880030700c6404009007c00381c1c06080d841c101074080d9400e45501600c24404517213000021803016811010701c803000c0e941424108003540c0241002c640d8000d00b58045500b200e0070030000c00802c000341d40194401da2052030101c119100590502105000700d0080c00054411007120002003802050a174114402030324bc01580740e910b910384101d13000f003264440d001503480459801010a828021800902000e180c10155480e10204800c290900b0fa1010b1090503914800b080d001e03100d08203004801e5410000540d41c440d07451030505078131004100203400281c5040803904820300180219a080303014918000c4a0710b04000104d10f00d507a01504c00d003c40d10341c0d50b1000810340c65074000785105c1c84032450002109490b168000e401d140000f0b00c0e00303240b50400c2006101d919003100c166410741d1300b01c0c500c21 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50926784 1250 50925534 50925541
    0xa0314130329010810110a0503180102071502190201150911190203070c1406070204020a02010b03010905300f030c07050304030809130e07030308070c0c03060c090f03030203030f 78
    0x38181a00302d40b007070041c18030180049001c1e1000a044005c401020b0420086114109540c140da07000d411100d00c0010402c00c0814807100000031808101100080014904480e41d0b54191050380385503845100941c010a100c131401c40c604161842d008210700003800107521100c01e4120b4007a890050484159a0b64400c5207490040d40958100d0099059500c182c1071060700043e50ba40c00c2f18000700d603505a00c00001c191402c02800110085c032000d0182400d0038042c2e0b0801002c0e4000989030380842d980c030914401c00340e5007406600205806103018007655600f110a0510030416072481030030b01e0700168000304500b060714007194600d01e0205074468403070b11820f0008206104000c0d01070458130010602000380001c0c0300040c005554210303810034114140c01026815990841a948400d400015040010034081c014455101883c1c1c60017150580307442d96149200300c4590019600d10399141041900e90b80c10401e900050040154049500e92940d5002503480c0300051409070086e41e000d004c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50928034 1250 50926784 50926823
    0x30c05041e1803140325020703050105090c09070f1b1a150f01030b01170a09020d0b07031a01021b01031503080403060b010509030613081611190f0501030911120a03141303 75
    0xa4400782d580032b002030209061030700181da52049401c2005101d660a48045032035280161076840241040ea158440030710401000040c0706800b078032099443c14260344024800140742d2001520074280300c42007030340e108050030500c402d8243c01e14002e0306141c60040301b443d181c0e030080806450f8044104c03031002d29a840f0107444000c0c014a0304025040000424041c04008003101038520900142d501000b2324032625001a41035400b405042e0b000d0f130420000048051007040c080c50203004181404500c2c00c3c00400f5070032981e14940c0c025102c4002c0131a0520070400f540c0180020f040c1c091910b28188881c500c00680c880e900600b520402c5400c03852003500700490360080d2020f02c00c0d40480c0301c010100d0b5061060480038030300059440f80500d203080c04419501481c519080d00d0768500c1d204201418030f00103600401a940381078503ca0074100e4294050b0740c4034100c414900345e0700d2018240c03a40807413130b01501c2003450005010107001c05010507182c0c00c1e61000300d0b504580d00640a00340c1842401007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50929284 1250 50928034 50928043
    0x40e0603070b210604110f0d06051906020c151903060305150103020306090f100e0124030308071b0201030c030e0607110d050301030c05041e180314032502 68
    0x8600c0d0290030100b2160300040100300140c00c10061000e007890f4540d6000d080004890440d00e10301070801003400014409096640076040b024290000003a4080c0c075a030008004407200494000740c400002010b20209505000440031914203441402048091090503686ca00442401e03140e01a80b0320144400180309810800085800605a076141c007200c4c0703811183c4a4090005074060302c01c860119107500780003d680d00701c403403118018001c981e258081702005008149107414580d92130307400324103910340c3d103900c015207114500c4200c2c41480e1452a000d811210300030500c40900c03404120204040c8410050350035141d0f130901e0001011500442c0550062821001c090350364402d41080045481d001805d64420301c80b04005c6442c94401c00700d007111148406d010040a005441a00b0025418150040c03218000c44221014459044100385402c0f5810b00c58244400b038202d1004900349078201c424540c0d01401c83f034402e0b203103240440c21104420201c0b41000c50350700403c40c0b0700c1c1a90b4030a10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50930534 1250 50929284 50929289
    0x11401141e130918060605030a03020d0f021615030b010503070516020d06020c01060303020606030d0e0922030527030a030807030b180a0b01030506090f040303060b0309061609050303040e060307 85
    0x40c404c0003c4d03400c03aa01041c89000240d01150fa03140341c59400301c0c0c54a8005200012140d156004040c085800c113801c07102407135000c0d103074400d42c45042c42c202e2030300e10154118000b42000d840000c0a10380440f4000302622003498809040c483c0401c20f020446030b10004079202084281034008a0510500c082000301059a10107008184040b800c003041e000190444c82c1124020303800c80e02c0b19120a07080549a000914082c0d010400c0850031034401d06095015036400143c008400a0328031590302070851451448004400280d00004c0804546203540d154880d14101502844010340c00000400d55a10807444050705011202c0001900584a038109000001015201d89454008483d4030501a501a15a0080c1307600780111100154403d209291003020001c21009480d2a00000c40c001650080c0040d0300f01600d4007004903c1c0c801d035000540c09444460010800c910b856039100401160500b42d5104100000d001000141d80000540e0140d40b10b500c9010700f65121080064034100096 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50931784 1250 50930534 50930549
    0x5040516080408160818010513050405040f050307080d06060f0f030509120a030b0f04090c0b0a050d18050c030109050705041d0114010515070308040602070201050c06011401141e13 79
    0x4031520200b01c5c3c0c81c4041c03d4625401c00002424229100c01900c017402003118400003210614000c21030303490b1039004550007034014002540804095180c03a415036110030825207019000080c0c8080b1020603114a000400301440c0000c05201c180758020505a007e043c104100f50300d59010818200050141c00f101e03019280c21181c1c0e8031540140035010784034005900380700e4841d842201c01941068001c60b407400340d001c60044881410542000e500e50455039190040020074480740c0032280c540d200340814409003502c00d070b601800d6071410a1405c00304100590203a414142c0d6440080c10018030b1794181e410032640816000b10043c0a042003201c50b8110b14500d6007002903203011100580030060517144c0540c1c2d101400558951194124440c180d00100010341c044002000306615901410f02584140b402c14600044c0640d00c6203411801c1c0c11032880c3c1071841122403c19030b0006158450407000500445c2000424010740000120f02d0945c6000c130710001445001e0051003c0441c0c0140148 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50933034 1250 50931784 50931817
    0x10b09090105070201140103050c0910030807051b060c101a130506040c020f120307110a030207080607020d020a1721100b0f160c0b120f0105040516080408 68
    0x20400203002c1d020030703103c810165290017000b0070880301e9985018180da400a0040204100103001e001e042c40d00246070303401d4260407250210004071007000824a00b402800103240baa40401c0c44008081030318027000c1e00c0307018108400b0414001c0400c1a0100110207003000541020704090821070803640307103125500405020341c2c00c0c410b04041e40010f015440030340d0100425029036006a0f1350f00d429003d41001a0303c0104441600401040150b500500700d01e4102080f0f0310414201c1e260043c4154224050f8000b2034060000c80700421029500415620043c070608601c03550181d1919002d0101521006083c1418094102c03003004858581125542c00102d4551400c034081d580801036600242c0504031650000700001004150b0705040116041329282003951307a140804104d40d0641142d42c014010310000b48252800058101ca0212552040749450008000307044860144c02c035034402c070f00e02424800312802e007400e4521449801d040070229a22181010110342c000c04030501d003004007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50934284 1250 50933034 50933041
    0x40b0609030a0825030c080903030405040e030903060f010f0614070f14060f0f1909080309030409050c07050c011808070b09030d1d0402070303090203030406050c150402010804110102010b09 83
    0x243d0002080d610341241e5004010300c5a240c504c03c4040b403c441c1c041d0028586c03845000104d0301480090222840050850f480d081da56004502a142007201c01311003500040b0f900209400c0610285034411209901e40c0c2480d81041490f002002030b43c080c1d10104640c5001101da13001c00c0344122070b07403590840c050304032842131480d0619a0391a0207800700400c2c02243c0102e120906ca21103504c0c0075a0480c40040ca41e669401c1103020122a01c8002d4081c940d1591041c0c404140d083d0020b5000d400b5017405195070702d00f0300f41130340c1c10303100b001c2c2000840c5034040150601050001c00c0c1d07109400b5091802c840340d02c2215000099580e0141c100d5003250041520000d0100f04442c02051020b5055081d0343c8405041c0c1030a84614060004000044198440e04d101c54074155005281e4584a4100004d140350a80c021a2444d0010382040c408907074001603580c103c1c0310800c190010310b54540384040551410703600090296001420041420340c1c02031200546078000e4019001d0303020058241d226901c2c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50935534 1250 50934284 50934293
    0x7030206130f0909020307030f02030c13050105030d050403020604060c0f060203070509090603030c071701060e010e01080f0303100509041103010207030c2109030b0403020c19060207050a03030806040b0609030a 92
    0x1142482003540c5042e0140001608034810b028001d090340e0000c0152004070f1540e01c0700740261400130030480c1e05014450054407141d4030180203025100c51003e000035198101010325240c05914804c40081c071405110800042c0d40348030072141601c000d40742c4001001c01900e040c1911015006006010314000320402502c0744e440000b03820700210440300e60030107231110010701d52684114160700410f500155420f00c180165180c1c0519904054400040c3d456514191821030890030382084507030780c04130b00042015520801032008401c20840145156040c071101189454150340310301c9005191520005082c0703c0d018007413003070030f100c090025595001c0030326000780b8014040740f04a40007002c0004400c42400303011702090181d111504d500c1041801c0d600c41041c0120000d00440462180b40224000e81d21081c0f0180480700c903139401000240d0501201a0410180d900b040c0d010751600c40082000c260703c4014160800c1c0281e50008900820902141d0144141d4140541600c9140401400c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50936784 1250 50935534 50935567
    0x706050706050a0905031b1207060516050f030f060a0e01030b07081f03020904061b0c05070b0306061b100c0c05010b040608030f030a150e010608150a0902090307030206 74
    0x1074441c46007088941d80701d1aa000454081d001c01030010390040c0b2844010503094000d002d040030806007141e100604801c0f00c0201380e40200c00c101d070155164010b00c500d103901a031080c9c0d010500c07810114208102ca4409855501000302600311014141020540c90340b94009a10064602c02e0465451903859040c109115202503070841c0000360349600150107440f00342d20703130a0302415101c5050001440c580800054000191066400c160380d6408030040e84100514144e4083e44c035112214002c07070340c1c2021030502d155548410b4481108000f002800d0b030300ca504980324020041d03c03040054560000103890300b11b41c100c43d0301c2c2c214580669554a82c0d004445e112015200324002d2140f00311000601050710f080b845501c080340c1c41800000440450240550307030001c6481000101d5541340b41801204003020307808100e440b03000a006110695001601552000060011560755585000402ca4030039042c0700300c406065000c11502c090380d030709006180040d900102034540f511461545480e51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50938034 1250 50936784 50936797
    0xa0506030606030a030909090219082406010e0112020c15011403010614010c140a12030507020f0a170d060f050301060501090e0402040c09120f0209010501021219050705070605 77
    0x24451400010480c0c58000f6620001170b901d03540b00362600b80b80c002c08101800b2403090490780440d4070040001401001c030502c2c002094650001c041c0c10810914034070403143c1004400c5041001001044800c4c3d0f000b510080c0858028a046004810500000d000074007034101064143d0084401c9612002050081541a41d5500860100e80d001c420201400c030b40640c8506407002807400410ba00302d40c01000c0c41e501450064140701219140c0c0c0c000706052141c000070413200b0001112140d40072a1f414442d1035030001040c00241000c002c205840c55541340741000040042c88070041084071440b42c0740c2511201c0382c00c0401130101a480f000d02d090000341c01e0168600941c0f81c4540024107600c90309590084035041a80100d2944450b002e00c0050200c0f5140b260034000c44040025145804868030300340b6601800200714031000310300c1000b01e0704d60182d01250455000b0101815403469040444200725640d4844000102d03800300e050754603000300d241c0984140601400011507a4012009001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50939284 1250 50938034 50938039
    0x120706020919030b0702030a140a0e0604080105011d01050d02040b0f100503090d080f010909080f18030d02060105010f110f0624010309030f0f0207270b0306130f08120a0506 76
    0x4141d90745c1104a80d81c0c080c0203204000103021250240f903203880d110060038440c80e18a03102d0181c11035080464400e41c0240c1c002d42003030395200010456000c030030a802032407105450708541c0c10352501d00058501200c0c5a8041e205071780e036003048a4103680b034460030444004064000c5540d4801040080d1498108480c00012809003104260895111b407040c14464400c0f140c001003180d08001d0140020b0403005411070b6800e104100105504840d04d02811b101d0b8000381d01062244c000c41c0906040c210f111258105551042c2d0051145a800c00c002c40b140c1109403038001a41c60454001c41e02d0000040c0158009014010038400c00d15450040b40b200070030b4000c0003681241000b401101150003988018002941c4039a0050046220700c59410007419144111600b19489840c00501d04100089844100c403c452a1100d1501c280c06042c100100440160030a403a2442207100d10140110b001000e40c002010510100011034081d00d140f0442c2442d150303e02e140c40003144009140c162092071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50940534 1250 50939284 50939303
    0x40905100f17100b0102152d0103060c0e0622090515030d0212070b07111e0d05250213051005040e0a020112050901110705030d140912070602091903 65
    0x41c2c40b200b6134065607440e1041a801080104114000da0361420005051140c40005140340701144e459501c3c1c0948a6403c08106007074a945949800360440701c41f181c0c0700e030500814003103050380c0d5513486c0d040d00d243d0044800303412010100220701d0f0b112890190006030303000b4540300c01e001000b402051200c0080310705800b00c0d00d40b08400c09041e43d0303840880440303c403034080c00c02080001075074030700607590804c0c85402c1400900d42d094880c1420032000c0b41c00b00143d00c1e42486c0d4031680c441c0800c4003400b0012507081442c6404883d81c0080c6900480300d8032034443c120300001c52030440d1100c0526030044080c8200402290a00041e00740d842079152051134800d60500d5025a100340c404155107826543c142c4900d544850310b001440c000e00380c0100003110555a50310041c01100c0183c0090012620884c0516038419140c2c00345011240040c00032a0070509a02c03c00c60309150026503007010001090034603444814901e081406441000c0a0301c1d00030701c88103e652880720341c0d42165001c5c1c904c901c0200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50941784 1250 50940534 50940553
    0x18010911120f010216021c080403030c02012a0308010b040602060112050c0603040b0103020a0b0415230a0203030a06060c03020a110a03061a01020f061005091312020709051308040905100f17 83
    0x9111f50312000070040e20070007080100308002070142c40749a201500c10b04010b14000c03004011481a1222150b01c412050400d403040e1007050707480201140500543d540150401c0d044c040c0003076807428140035112113103c40030281401e0010406c10310444510003003600381d4230301d02440c00d168964400e1108a000b8035880b1004510202d81c0070036503040d00c460301a02859580506006c86140c0030f850009005d54600c2600c044040702c1003001000b081c2c4564008503a24100071080c00c085400396030005080110014504000980c081142d29180360440d803c1c00c3c40403080800100718840603403004040310328190180b410503801ca010445d240b5000d0702a5400300d504d11700da00761501c1048820484603507a440041c0494074260401503085000701e805582e000c82d030741c0d60395140350340c01851502c0564024a0704009c02c00d82401095405680500610320302d84495030f6000c100e001c0c2d4022135800d1900c400c0000d092001c015100c100405110f10380b1a5201e54442400184034080d40c0d043e1281e000b540c006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50943034 1250 50941784 50941819
    0x70518040204030803060f1908012702030c01180b0d06210b16090302060d0b091503070b030910110a020111030105060403060b01170108010518010911120f01021602 72
    0x296000c40e50130504051441d580c290410070189075102d0055880700d54403440004545282d423984003d46054400003a182c01135400001c1c20b64440f0040ca034040e902d911071140144c07004100da00405d8403c1c20001002091414a9640c0750b410781c000910714100070030300d28901180c6411007011601d0503400512800702c400e400c9800c01001010150041402c200820354280d40181d004203401e42c1483c010503201e03102c0d40055101d078800c810f10391450b526030b808601189450384655802032070542203400000161000b20b82ca442c01c52280c483e0f03100c00400080c50030801480201c2c400d00f101101000502c1780d140030706041c0c4c0c1040403c0070041d07180210a8810140d220110b9041c2c2e100101494149403442d680c040140402004080c1004200b50204a8560310303607003654003a024480000c205031801c00e02400d40044101c2100500b070381000c4100380030508480c1c40d650564015103200200c80342d41c5000300e01e00b50b00c40150724250361000882109074107800380c003812a2442103522610080210700c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50944284 1250 50943034 50943037
    0xd0c050903070506090117010b03014211062e050607060504020102010204122603060108060d02120a050c030f010212010b0a0905040c080403020c040204081207051002030705180402 79
    0x14801d40503884500d05114030b00c1c100024011089052410307000e2021880e01030031400f030080c4d0002190202c04401400000100c0208411511087c080905110b54980740404547c801d1584846445420b07882c1c14885480713007440f10340b1005c03154112171036410000c600c0781c50016007481c10a4400c9640c01c0c01420680243c17a02d000b1990002e280c0c500788507494496800528010304120306540d42080002030b11400301c21040030160050b241c141a10340c505c0c04241c0c040250341c0c820303400e44604204200d03d5a03000070300c07540c002c50301fa203058191521a10104500c03004680310003040384a1001c0e5141000800501010303040c07000c0c0c058488036480d07241c02c0760a0340145d04a03501d001401f20014000150014003402c842920761404046c0c0342c3e80c0b0004075084070042083c22000400c0c80701000145501000343c0c10862000395421850146003106454446410000319031651400007529000d006040001d40076901d20084215a00d040886000e0080d600c00840e02c110303065511403000d60b070700e03180c030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50945534 1250 50944284 50944297
    0x230607030b011809052203050409050604020301121221020a020106050901050d1202011113050906090c04060e0121050105090f070e01030b12010f0b01110102040f03060207051009080d0c05 82
    0x3c4040c8070441c10300200c41c010f864010005441a03858601c02d0400c0d0620003840c04c4514042e848041d5681e0500310404152a0010b000601039030040004100045000407102a03032500708901401c2c2c00002030085513510045404045000c004840e8445c5040d00750740200020304458000304065a660001c0c000030b03d10922405a009803284240c00100b48a1048070701619040e100000d00e84d68a6004a003c50f0030102a1f6010400504803c0c003050525450440d0003010440c3d00d42124038120800080d588610b000c0d800411060031035014882c0d0040500d60f61904400801c104220801e550000042c01c0034441c41d8811028a4003042d80703e0035541100f401081e459030340f49101c15500006401826846000980201040504c07441400d0280b064862404040b4004507001c2008000140125981e654101107030b4030400c410001c0154500c410030850364403407805a100d044905106081c50151a180100b09050002d5001049100e40081a1000112388100508910303164125018042c03070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50946784 1250 50945534 50945567
    0x1403010c0e030606060a110609060412030207020d061107080d27030e041a120d030506061c0b040204150c0b0c03131103010f0608011e050601020604030c230607030b01 73
    0x183d02041250604c24010700300c045d00d13401c120300d02a140c00c1400f4030340141164818203075001081800704124500e180c0da808407010713140070750402c1c0b03071900041c800c60710240c0002c01c2c595503040b024085038854030a841d081c80d080001d0940312800e402c6140040c0414403034282000810000c1456440107510828060581650f507141c980007442c0c0602c8003c04041c035842074083c0c005140d07000103a4420354541e01c0c554503500500708800d5210805000c1d2075014003820700c100070520402c101c0b000c50003074060044022040c0840d0359030550b800b05000f0320a6800c1042040b40301342040306220703048480003103c42d104101c0306a05945400c000d00c101d01050f25503d10b13800b28280c19202291100c100504404402000001c1c480c0500703684408a0f1907941c0004100e035102d800348061407110002c07a4420803d409001c1c481803400300d0000307440d1b00c3c1c0180b005080c006606599406d201a550400d07084221298290f107080e030030b03002c00315a2501c0407180c1c0320010741814132038001035214140401e01705280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50948034 1250 50946784 50946793
    0x8010b03061e04170309010b04050105100203120c0705030a0203130905040f0206030402031e0c0f09250e0303040311130902060f07050c040501140307140307030f020612011403010c0e03 81
    0x40c0e060560b500c54018000341d685076140c403849141d911100000310b02514810000080f003844c82024881903590590109119102d0512001240d0382c001c030444406030011081c0320030582d03407000c400f0228003c03100d01400b2448080790b1819186d4000004000019001418102d055910100356060344d40031140204102e480b110745000604054015641003440141aa09101c041d82004080c4c10726201c0c2d84529a07210070f40940440c140b1850164441009640c0040e007440c0000ca00e415440891050000f1041034609162019200c1d0f22200c0f031921004044da0341d01d82c4d503400c210900e0004144074070700c19803500c200400c50544a03c510a9240c0c2e014000d581030800c4e503c8400402e42041c2c03400c0e61035019074004000c0c255503602c1164043c000d00011007401005000074035107060b049420044586441885d09440d642e80021b91a040742ea20201c1201d43c02c000e480801c4141c0261000d840041c08808004a0080ea085410782080c080c29002008480207002040700c500800d450820b416401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50949284 1250 50948034 50948071
    0xb01080f070605070302031b060106030b0102120702010e0102120304081b0d0903080904021608030414030406090302060901171003020f03010c09050603090115080f01060f06020309220903020708010b0306 89
    0x10fa000d4880c0034000d0055a0400e403060100d0311a5099806a00780580c101c080180880354142c0f0a00c290000203100408054900d00002d02c220311403100040c0c140a105181820140e10800a034860940c021030070ba9200e0801e0b1130403500540110529403100b040030100080070070130014411121a4507613030f8400100e40740d0340764404542c0c0004a8150090b408000c0b52007061b055480506005202e248120350340d1409040983e0104003017111217446030001c200403c80150b011807503c00340c070340482d00180d859035441c0040c0c940b030340c001c15040c11503110740741081842555142004100d03802a03412030042194503041508882107040c0c041e01003110124144540d0804001a5500000c50000050640c45007040129901a07039888804550700190105e1425902030190740000c10345000ca103941241485c1c8041e440c1c2c0540070800303000f40312596a640c042d00400d4154410b046196070108819285818029203500c0503009030103144d1300b010b450b40000d00380000d0061080d01032041516100340f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50950534 1250 50949284 50949287
    0x315150a030c08181b13060b030604240605030a0f0504031107290f0904061511010c051606200d0e070b0717070501020a03060e070c080906071a010f030b01080f0706 72
    0xa885c004aa0400c2040406540098581c42000044c0030f00001a5440b860810200700580e9100c07002d4141c8900c0c055001100f4003050110792098801c2418010346a40e0307180840001003c1c4821102d44007400e01050000b450b070000303082005007003008191503400e80c68041c2400007007080c0d6442a900c2d00752040c0742c0d40525076800604070058a583d07109107401501c400007001e950365500030b000c011510401c00104240c01860f050719040c4804024400c24040c844040d0250290014842a0f20040b003205410440e441e440042a00c041410041b00c0101c50301c0d2900c29600030b01c001015240c601032a4400c54080001c0745800c45041c07440c0546400c4c0c2d05d079607005100000310b45011100105000d03c4c0005402800600072115503070344c001942c0e070300e04481c2c11043c4001030009014001c40340380d4040483e00750011560402402d542e000da503004c0ea031038000c0c2c2d80b0300c460350b001c64100300300ca0003c110100441c0d41e64044034080c0002d001c460343c071420740688071002c068031170f0859881a001004180e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50951784 1250 50950534 50950573
    0x50d03050408070b0a02061b090d1b030501050a0c020c0f0f0a03050706030504031e02060106030e030d0608010203060931080c0607030c03200315150a030c0818 70
    0x4612900d02582000d0351180030701c1c0b40a41680004034100700c0807039140b820542c10020340350b01400800c1608400316038004010f085100314001c55015080d800a02820f00c00c100880401061100398400040c60ba6414002e00070a003d54080180070300f030656004041344009840110103400800c00310040315641c00700040d40f03a4170841e1507048aa85207001002c10384c1403010740003d00480d10042820700e454a402007a54120b810002291402409094202c6500040b2281920440e040c005490240042c02c140341d8000c0500f89459182440760204c1c56100640145000d110141c0f0042c8075903c4500510b01441d0700310140500c0324400b180544000f031900c48804000c01d0007003090b2450400792800340b6040c80400c991150110b51207040c0000380326032500c203103050889000024070a07181c46c10b0a4910300d20020304010303820400e0b034007001e8583c0e590b00501e0301079411880c44a90f8030b07942601d002c0c0182054003514008144901d0010b25074401903544906503424003c041d00e6600c041d42c0400662 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50953034 1250 50951784 50951809
    0xf0b031905100603020306060d02150703180603020c0d0c0204020c0a0f0c0905041703070c1a04050f060606070f060216030903060c020705131d06070309110a06050a0809010f11030603060f0c0405 85
    0x10205c41d028008588010340c0033084100d00a9880c26103a200541c03030001c001702103900041c1014810400340240d450042060780b0a260145060b540d0251f090001070301170b005040c0003c6c00340c06802003020410075400c01002d0030314800c04c92418000da03100080011280d007120050b02e613000d0411018141c15841c4011903004203d41401c0007000e51075242c0c0794501c0005142800341c5241a800d000c2031080411034100c1e00d8004c40010242c5203401343c00704000f402689002000d68810341d0210b020442d50303405a80e48600b4080303030050084000d0070001d00000d51807000391041464641840c50052007c5504016650003401c6001d0360450001e410004040c2403420440c00c0c0031040402c0e40c0d8075020300070140100c50965001c01c000c15682802007610a100d0000381c801c0e84022810058141c02c5410355940503c6424540340e5661610074542c00741060350040710390b0303600c0c00a078505e40f20041000355000d40419401c50341da6a4801c40c10785104202950300342a010014042080680f0300101071500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50954284 1250 50953034 50953039
    0x60a0218091911070303140114060901050c030a0203191805270702030a090e0402100c050f030d060e010603090b160207080609011b05030f07030f0b031905100603020306060d02 77
    0x49908000202011500f20440d90500c03014006002c40905905000306101144060019400c651501708480380328000e603070005000b0329002ca842030f80c0740c2c02141a50783e01000d10065070783c1c42a80b01c40007500eaa1003c2a5280380815a500c0300d0000c500c2071607a07840104800c4049030046003000c080041901070032005520204118013280b522811584c0b1090243c201900250313165040e01c907000d018441240c0280030005c0c01002000007503519280c01214510300d13410541c03400c10050814034244002c4619108507803000013078038880c550361035020354126820105440d00b030380d8854a040b4103680c40340b0800350410f203852021502582c030b4100c42140713100f810b0044841c0d2955440c0c005050107c100d5420071240d54840345000c1c1003040f1a40c0c00020403880c0351191951030150407400e0b0104002d010041055500c0d112a0b90452281d03201000800000f000c685c400b240b80f8040000d192101035040712540140c1460b013141030301c14000d00c1e003a41d5005015050701d60380c010506c42c0c403640c07140c02a80e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50955534 1250 50954284 50954311
    0x4060204090906140a02121f03020d0b0103170909150604050d0303050621061501140301080a051018030c020607020405040f050105011e03060e0f030309030408060a021809 75
    0x2220111441902c80c024070420b03011510300c8003600c9545072400010a04400240100000490140c1002d02254010382c520b024060a821207094108007015903003000303420946c0300d83c0340700c01d00080043d010704892141003559800132100101341c04c0c034000d0b8000c00790402d5590b00443c41e081e100d000d1608604d18082c1c119420160740c3c40000d52001c05803202074000c07a07518000e2100504254950b02441c8015160744020140600c411507604d81e0010100c403140c034030130740c00d0000c103a200c2c0007540b94441144803500c0d102c1d61a0010a900e914804da801c90b058403901c0d01c0d00990204074002c044070400380c3c0540324000d021989094440460303521341280d0020307040040300010307a01c0b4810580901d00442601c0d1078144980f07049400c50300b040e0450340c401814901c070141c40201c0020b24030181d90340b0cd2004606c054a00150078540215004044880d010110170001c1643c00040948207c610a200303c44072a160909900120301c50885240c0d1141c0999025030310300d0824000c1035810105912482 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50956784 1250 50955534 50955539
    0xb09010912030f0608030301030203030a050f07050a060c0e182d0115080f0c03040f0203030706090308060102070e01051302030907170601031a0f010303030b1503010806100b040608060904060204 85
    0x18500c1c60050058040865950110344020752600e114903006000780702d00451440d4107640010366240031f40203001081110001d41500411411000e80300103070381c4542220400e40321841e007040074000c40a800d0b0000b40011414035004e10f45128284100300440b5820582e686661501d941501103480d103002540c00250401001344412800841c0244904100c503285180301200c018a05030010f041c10303451030700c4103080c400307a40084811a604298001e454200c1d04205102090960184400142c11917190001000c1459000101e031442500c09a095400507600c640021880300c00a0041c1d036040780c043c00d10406604515401940c000b600c1004407640d55551f01c01109003001180985441500b0810041003004052502015009070121100b0050700e4141031842403003005120107400c1680320100301e2482d845648801c2d0705070020500f132554960311100107594174402a5144c44c480b0030345903030000c1c1ea28841ca0584040c1c80c926504c01440782c8542042001c03201c400752082d00c45070344c02c0000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50958034 1250 50956784 50956793
    0x3140c01060e01080d090f0609060c210c02030105010501030c0215040f080d06180e0c04051b070803010e31020f090f0f010614070f1104050106090e060109120b090109 73
    0xb564000c00302100100a00c50710180002c0c0442019404181040b003140c1c41030040c190408108000c2c5d0320a440c09010500a034204007240d0b2044140460f00a04004a115042035105119040310350090b4020301040c1da131400118100d039126058500140c0260300400001e01050400f40e4102d4020540c181805140c1c1c1c80c0e03002240d02c800c1c1d60801c0195640e40810066241003d0701c0041d0000788803c1140380e4521b03009640380c034075110b001e0f071180343d550700020b00d0b8131144840c401d52507d51810300340d00c6403100c0c54410b00c42e51080c0a501e040d4200c0b540068003070500104205000c0e181d07210303108000354103114041c440c01c0e01400100d038443c042038004440c9850310070425102e440d42d800d6400700c9081a00c440c1c01804030680144007000146191140c10301212000ca920a83d0700180c0d074901181c550420071102e21482040d00c0c0e0090515000180c5142c0c0803255070295850b002000701140c5030400151008441d511a0840012303040010b1408190454103c9600c0741c0098000305009446030799 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50959284 1250 50958034 50958059
    0x16030e1002040618050405060d1202070b0f0405040501120305040b13050312040311010f09060e060409090b010509070c1502030703021b06010821040e06060c010906140c030403140c0106 81
    0xc2000600711480c4154800300340a130160080c24250780400c0740d4201031012885444e0620342c09080032010500702c1d51254802c0040c0d000030102500e14036241d0000b03442c11a510307401407140610881c2041300100311100c0d09a00441c020754544c035214941440d244007070b0a180c000018106070f21024060015080d10240400740e1010702214080c0e50751811860032194206000652a04000000d4098100c81d074200446000740e8042e17080200d840401800020124440d5030400820941401902c1d010400c008a400741611f00c101e4003400c00b6a0f07820021601c0b1004030b1000b800410500d12884000c2080354003c40d0018803924000d85030940c05022030044070942c001c42801d940c09000100003050090000b96402c00d9141d02d04c0c050807691903141d071402d00542c080c0103119012440810801e50b10f81048a4500e000d04000344001129810036000800f1445a00d06200c02c00d01c00040c40c2c1c0b0f80e268216407081c0c1d41a2200c11851034581e0030034030079400c450035000c5150746e240d40c0820b42000b001d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50960534 1250 50959284 50959289
    0x1103041a0d021606050703021206130905030708071406100306230405070906090b030a060e0a12030614010f05030703050a0204380a02070e070306090c020f010e0616030e100204 77
    0xb07000e0000e203244c0c603141c82100d0b0001d0900f01014810b010400d10112111105600400300300d6640200c1951880d242004080c1c980008220340b10008001040000300c43c040c050050052000000e00c206060140b600c0390000c60b4a100540d00113407040c00098200c0d4003600e9117074041e075000410004000d84140600c0026603050743e56610250b0b041041d881e05008280103032160071800d03c45003840b98046942c56a410030010001030703c41c01001e0b01080200800305000e0f40000400c51840302c2da10000d0b0040105010780e00080d4200b541d48200c9501400c29a000c0c3c0d040790795090710b150341c0d0400440c01001c0142400020303130340030480040c05100084141216080c2000d02c3d003d104c1a04207000303801d545903aa180f00c503a03018061780e140d45030013040503400c0350325521808142c0d0b0f450000860084c2019000304c102700b840d00949a140542c0010180b001e41d4048008002d8580c40540c0030f95507080072951300740180300c3c100c002098a03219801c0301c8603074004a001c80f400401c600c5c00031810b913040354 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50961784 1250 50960534 50960557
    0xb0d03021006050a060504030209061311120903030105060a08070e0307060302091c0804050d0f02030d081501090b090409030306090504030203030402011403040803040b040813031506061103041a0d02 87
    0x26840038540841c64402c00380200700844030a00c082c1e14041003e000c50041e403001a2080341c0000000d0030a490f840f11031b0000d40340c3c1080c10400c55070810b103d074038a038000c0183e18000c079108000251041c20008107d0341a0b503001002c0305e00b000d41200c0100c2c0c111000030140c0701009aa01c4081010751000c1114a0290083d030724050303202c2c0e4011080c0100d140c00710b00d42008040d030ba5101c61000c0750301030b012a410f480d01a01c4564400103e03040c0182d455010b040000e402d442001507130a52641c0c840c00d40d6004400302c7e44a921039048410044568055602984030013000800c041d04082c546071380401480d0b40f003420041102690350240e202207420459099001d13070000410482150ba21100304e100210141d00224154101612620024000100002d1202211801050234000c103281920810300a004c290710b40c1d9900c91904009102d19010681c51041c104500850b0303060192801c9040807034000000c50030309140c190040342c000f800040203240003600300300f5101c86c00c2242c001405070001d0b5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50963034 1250 50961784 50961793
    0x70602030a14090f01032310050112020702011d0f18060301050702030a0806010f0504031401060306050a09020312030a060e091b0d080306040506031e300d09060b0d0302 74
    0x20076409050030741d5107180c0704040032003006641c0c1996034110110003d078500780f8000920310144022141d14070358206000400c1c0c0001010000021407026150050310740a83e980160071805641207803c0e8040c0345070090100302c500101c01700180f182070032a407403030388000e056010b0040c0740c7c004030322078068043d41c011055142000704540b0b810240902600241d26200a61a00607181c000604030b9074081d04180c1044659603600100300d11a80955026680005900500c528140d0306280288101d10048520a04141c0010a4848588031b8038000300c1d00600070b0600240b500f01c2c0742c40c19070300003040c0c122800e0741c6110110307403100c4c1482140e00c031f02c070007034018001c24084044102c0100c0b4800b01a41c891114281c01c180041d0041068039003000c01501c0100f100d481d0480001d041c082c55000104601603100c4641c802518009100380b480201540c08045402010168010f804840f12982480c184108899034010107181e01401000d07024581c00036204440d01c1c00a00c80706008a000c4d03005921 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50964284 1250 50963034 50963047
    0x7020708030301081f09030e09091f05010f06020c0a150c140a12050f120402030f01090f03090902030103080406030b0409080c031201090e0703150e1609051806060d03030e0a06020408060a060305030d05061207060203 94
    0x900b611100c02501050c0000d100400f40d07400021105c0802d4000c45001c000c00804608866018100a414455000420000140c12043c00300e5594104a100341c601c0005e98482c100654011400c945c114441c2ca00d110385092a06150383c0f1030458050320498061003000a80c010081081c85581115885085c2c0c8003506181030400910b0540c40d0f80001c10410702c10001080014000d00441d400c6a8a60801050364585e0301c0000d0b0007803035030000c06010300d18001403a40b210000480144004d508c00d04050806903201c4110008a440e0751207085204da00ca1407042c00407a0742800c1c00348601030000c0c00460380d000d9107940e45051052042d10000075203160725050000c0c80139409900e911021707181c2400b40303100a441070140d8034031005d05128050400000131800f414800d400030410b0019542c204c904107241813514030020340c8280300d1082240a01d0f1301241201c001070148500b1203801000850a0a100070460002000c0140103290700c00030822030b84035811300a1004800402554001c1c60b00c1340c2e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50965534 1250 50964284 50964299
    0x2303010b040512010e0604230601090209041104030b0103030309020607060e06071d0f06131a0a02010b010c0c03151803020f0d030603020112020307020708030301081f09030e09091f0501 81
    0x3e0107080708550390790404070f113060940c0d40001c4c6140d200b034206404008078030419031980c01e0341407140c0c51603c0c540500c40002c82c021620790020090410140d03020015410111320444090045020080c0032440302c00040003c80d100e6040685210300041c482c0349020b0880d43c2c4c1e00d04850390243d58000c1608004200100c80303030418040f13130240c600001440d1608070014005001c030301207504264400c4101189650803030003103034407d0019001c225407006d28146103a400c141035030084074201c0300560910341c8104840d48591b20f6410720581c006880320005086a444a003116004d0b90210900c5175100e28030b10040c61001c1504a00300d0185d000303031041c103041036410790030800041440d106141c10302c5810001070741c0c8203501c00c61100c5901d8005031240c981e1030049040a400e580b01c0e00c1c0c40c2c0300c044004503004501054804079200b4800e0604154901c2c1684001514541100034000c28241600b0850078201365001e0b40d88a403000301030307030b01c0001c5002c000c080c41c0b18918007101e09503560700014406030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50966784 1250 50965534 50965549
    0x301060506090f0d1b030b010509011706150114070f020405060a060e0609061603050a020709140103060905070f0f05090928062007030305060109060207062303010b0405 74
    0x20042501c21600e4000c102011900b070b8100928254042d502129200050199a00c1d900d00001c103a0603c1d00032196486c00e2954a420003070241a1144614900001d81d801409042312643c0f14440c0144c4016551200ca1107150a40480366034180141441d4001800d0705210080103154455120605001007a0041c4421200000c10682c064284140c040c00721395048014411007103800c41d0304550318440c26011801c240500d81c6044d0100402e81c103104101038000010785106d8040d40e084410b0640d99401d110203450f00f200400c1c1c400e0038010300510215510350041801c0b02c0c01603080318112540c0311000240e0500a62200c600e100040340203100d5480e00c1c1c0d181d10781001a0000034001c0c0440c64845c000d030259440c1c120404034440820314810080a0382001c01640740b4805464640d103400c1e00c8069503580150400c50002e460030002815640c001d005000560710700380c1c004d00700c0c582001e8003610010040b15050403c0038403801c9203550280080011400b13082040b000d913031150300d40000d21081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50968034 1250 50966784 50966789
    0x51005281e080606090a0e0f01031703040b0103020d030c0b07050406030b0910121401020708090f1e12010b04020304060f0510120b07050c060406050103030915020307080903030c0318030106 83
    0x401504007503440510790302010054100808071100c40c0d540c1c15003c000350340d101c0c0607404184030143c000100b00000741031890316070480e07008040403d24404200c031000c8072031008450040c21000487d006001505084018142c03061080c00d000111403c03d8036100c0120000300d945a000440019041c00009da143c0224401e144060701c0b40c0c8243c1c1826141034083d061640520301d00c0c400d00202107018020420700c00030136000003500071581c1d4070f030609140705180d2100c00011300504418640541e581812507031842c2041d66081e414442020280c20031005607108494943caa42d01c0355040d0065503118030007103010b548240800119003040780b00e183d065810041aa0712034140c1403004001c0303c1500b9000d01c1c80c80e9406921b41940313070341c1c5690a454600940881388158800c0400b080208442544070b00d040e280070b521401c03600c1c3c0e82c0da5580c0c810740d46002500c4005030414007050300004d031020041c0c20303d85402030a482c204000038100c0c601d036820000d038110348010703010b04c40c0c2401c3c00c081c80b61901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50969284 1250 50968034 50968067
    0xf0d02070f1701060b0301120201080609040209040609020f191e15051c2c0105010b07080d0605030a051f0c0903111302030c130503060402030705100528 67
    0x6151900d203110141e6015849441d8a0740412121019010300030340c03110014000c1901d041c2c2d02ca50316040000300d0002e80c100200c0c00b28100801085151a101c9030b55071185500030003048265480355181006031481d500205e0304481c2031191a0059a01c103250031030385280c0e0740da6111070645003100039041032520750102e020700c04d00f501051008900c1d044111094140c0780c10300541d1140b00f0080c00c4004c02040303292448440c50600460200742c2040d8000741c80000d02c400320181c1a016941c2c041c201c0e14288500400c80c20104000300002d0032550240441d1401038000146165440020900300290200300711110b400c0768265080c804d656100380388840c2c0c8103a604215680300c0140c06000f01807103000242c1180110f040c1001d0076034582d581003641da01c2d150010b540303d040003004400c0ea90400405860111481240800c0c181400640144070b250002e00a0550b0303071520080c0444608050300e10b8081000800101c1800c0c43d0050141000c202c085980008901035000e00800c6440340405034203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50970534 1250 50969284 50969293
    0xd030e10090201080f090307060218030f07320d0503030403080114090417090a03060606140f03150307080a0c1a031006030c11100c03050709030804030f11060c0f0d02 73
    0x1002d03036441003103241c0c422414045000784e03885040c00705203140141d40d00100f5541c000076203090304049956205200d50400d03402c07a54410600c0030300342c0e107515482c02514083d00c12002d4400c1d001030100c030401c03264125500880140c21740707100410394034030704400250791550001050000b0198401081801050a1045007030104890b0000948142c0d000d040500364989004804401c01c2440d021030300200300007070900c0d04141e0382c0d00e00030340900440d120f150301142c42800b107054190052400c40f560f04c00c0e08400c4901d0b5507100340031086811070070002d5035010300c01e00c000450050710400403c4080c03805105d40d801c038585810070f5035404650903140481c081d4418020b001d00f003002019000300b5102541400f2684090b5070b201211034803c03405030a40140720303450303610f00b088440c0d030720140d170100d00ea0b42e00344081e6841120a4401f0501403200404140302004204080340e000c54128601c00c0c8514040d01240c00c000b130004034150003224071001a6004090907080206017000100c0102c4290b00152 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50971784 1250 50970534 50970551
    0x11060304030e01031e0c020a02040614131a060d0506040f141812121006030606020703031103040306090501020a0806090603030d11130f14010203091f0e030d030e10 72
    0x80400d200b40d20128145600c40440a410f20b00700c450042d00c0c40020081001956207801c0002d5075088844000e030701a600e049000714814a5403540c51440100150440d00d480030b921741164000c01d1018107800415020100051032542c684006002c130700238000001c1140d080c040108012180b000049440d12850b040e03106081c0b0500200039540400381e40a181820040f1400990811250b5280841e40c84c50001320100403079140030806001d20700201d08550090b031550800d0b8100c5603a80605000340e40311481c10400203200c1c03001007001c035182d9020740341019500e90300d80e001ea0b0015241200c44e0707500410885403080e0310205895000700e04440700d00007400d010740403944a215020080c3c032070a032031340c0c09080740c0c0042004862070f11100451406180b60348454401c0154020702840d84000032070388102c541c541c0700000b51484007000510104002c0a0b250820207000c8618514001b40103440030400c48130395007442183c00c1941c0c562404034111000a50103424540e050a210f15600d1030704000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50973034 1250 50971784 50971787
    0x720011802040504170a03151203050702061e13080c010207051f0201060e070206090d050901050406030b0d0f030801060f0c0b01210b0406150e190203060f04050408071106030403 78
    0x50000c09501690002495210b0381855100c03008030390000d071104040000d032a8403080c1e040d803020f880c2c0040a49000314540e100d2559080c4000403420103000075074240481d002501c0c01c54018507242030710383d002c90301d190300149035846190804040984046068282049401ea0500140d1441d42c02440a041a203081c000040c201314100f00000e1184000441c029481070700035030003000503149070380d10414a850714950007551040300300c5e043d480b58002c045158007103c1c029000c0c2c5040d11416100c1c141024104403086000301225042c0551000804440c00c01103201002c1c501d601ca0b001c1da83e60003140d0b05204000c0d2448154940c580704100300c6031981d01c046000c80803481d0550307a44060141c0b020003098621800700d50020005800d0443c18801e010401510303611840000d15215200c02c80e141c0e13560000b0b08100e1045403010082c10400303d48200e00790050b402107920141c001c0c88110005030000c0454100c44003120126110000000d4040901c4030401007110101000c0f54998a18945990b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50974284 1250 50973034 50973071
    0xf06010b090901080f12090109210c12030503161407061d030a0212030a140a06050901060804050a03081807060302040e060303070309030605040c050607050d121808160506072001 78
    0x814a400000305107d402c9a00c1401020b00600c008032a2002804001c00001070410408000b02c60300e508000f8001840c03d08400300f490003076010f0700c5403801c41e070f074000308031180f01c188058800810001520041480e000342c4060710000b4000c800010381c400d206680f80c503200743c2444461040c6d5100b4043e820240c2d40c0050310f104151801c1d45002e48949070031030395402420140b62120142020281000f22000d0a03a121204a4038200c4016241e41d80e105402d40788910181c5024050b074020102050100f4010003005400010141960090344044070700d481c180f1220307400c40c3c4002500040d04201e40c9000e4140641c02085c01c5019600e01000355902601c504c42c10b01c001000c6507140c10009060200c035034822001000040d001c0c030b0340d900552408070307100c1249013072101c041800206048194800c5105840b421846030a0302a1041ca0b507440711400c40e040302c1001c03841c2540c112200b0001035410710040e4080e94554440c1030141110400c0340b0003070903403151111208e81c075102e81611622540d08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50975534 1250 50974284 50974303
    0x7030509210a201302070c08010606110115060e100c080307090501021c0503070f0c060f0b0915060301180e010e01060602060a0203040302030a0309021305070f17011a0901020f06010b090901080f 85
    0x114016500c2c002403a0189048031f8952221440d940b030b000001a01039003000b01a400c41040000802070303503601303503210342d520520303402200c0c0080c1c260910340500e03003000c035007015031103040e41042d5052664646e17800c1c1081e4412520480020501c0c9400c2050f13580410558040c84006841545c8520340c3c1c1200070140e0200614003030400074074210384031055010301a000441d41e04504240100c16402116034050f01a4280303031801078800e20300050b2100390016070200c40240040c1494a1a403078085955049040201c400c0415507541030002a00c40b002d11071202c18011010001c20b44034a40385029040400040240b00054010020440042d0380031080341c0140e000d9080020b080443c500204101c002032070800403141d1300e428140314540ea0000c0050704040740c03a1b65603001070207550301d0a41146400b0300c64900d038200b1185040500402c16405040e089606204070b0700b01120001d001d9140400a0740710801a0344006462581070503c0504180036041c0b120061a078222611421030f910301c0202c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50976784 1250 50975534 50975569
    0x60c030318021e040f020c1504020d0c060903120201050907051201060b07142505090c04120605090d0f0504050d03050c030f0c16050d030f0908010c05030105040c09030807030509210a20 81
    0x10b230006002c55803140b1038130740d50b01d41000100c0c261648a02015102450500081d99081c100c4d11000b20f503103105001e95441800980007030244a4940b00502c1404030346412039603005c2d5203500c03000c5204000c41c8064401c00d07016000e4014141526002a800c0213103503018050780c0300320717415054004528401080201d9106a40e031090030303900c000e1940010700880c1c0180340d40003150304482c801d0103030075000f4500645042069811154000d001694401480c14a00c4041841440200130300e1030b20218100985019051203854100b10240c3c050960f400328401c50003028011902507d41e040c200a131711001c84028a540382d499040c82c00042d03103c40c0c2400010100801d900d000b6180d541704684241c010140c0c48000c0c03021800348007018145030003d000e082e006914111140c4000c2e03114610b042e0440340c102013103c3c03520f821601c0840b100c6e4003182c0d00d03035040907114007008246017030b510001c0c0c084203040e405800000e280345851022481c181e0726001d8131f030050100f81401d40d81c50345000482513192 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50978034 1250 50976784 50976823
    0x1308070b0a060302040e0a030e010e030d1107080715022401030f0f060501260a031403090c030d090320030d030207051c0203030f010f060c030318021e040f020c 70
    0x854007180090549500000d40103818041d01c00c0801c040003450a001a210751180c0a4101000004495030017001d81c40c60382c1940001c42c540c2c0170b81c0c041c01c00400d80c08912001c3d6907145480e08490303031400b103150b80a00340141100d004101d20940c140a200715500329111250b8a49003150000d0051401c103000c058007145800386020704108064030400c40159010000784815a03544d26540040710b242800300200030021001d640103c18081046403100354980c0340d10200000800320346842e0b80008064084901c00e4094400721550102700040403c03d69035a440d214a00b9403905d101c11007092001c003031101c001801c440003e59030104202c60a40d6036882c00585a045500f011454901040c9090184548602c2d6180e08145d02000030340c07181d8180115184541d81c1d42c0c882ca20055176611460300003880c6901c0c00b2001034825040015581171300507051780400c00c01d400041c0034040184030007507140203d070f85840381070400380540c400d407161100c0110f0400c80038041d40c94448040103443c40d4580d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50979284 1250 50978034 50978041
    0x1b0307050a120e041113050910090504020a030609230c010e060f13030c0311030f060f0c0f030901050105010318030c0816080d1a041a04050403050408100b04051308070b 74
    0x3140d4403d84402e81d0041051103484100c1242c840140e01c5074904480d030301c44484021483c0d080c800040ca000b14600c5540d52016840c03c9240b44c0100006441260300500c411400004196a0b0040c8c5040f1801800f03016000c12190841e1740c4260103154010b6a036070011302c0a00d905d681c220b814155968000c1d120035036101c000c02c1d8032500358459035030841a0b884c20300d0004010301c11815010401c2d01d115a4004003e0312070102059a11b00c46020040c1031940000005112409101c1038540c1044001c0c40180c10241d2201600100e50411950040d15a40d601700400c100e680c54015120942920a0030745503103401601d008105d8194140041c0c540c480000d01821441c100e1660a40240e420600d500c1d04d4140040c240ca01034503044052074000e103406140c0d0040c82c41c05103b886181040000d20b0003400421500740b00c0600300041040c0c0038004140000148008140b110070795003030444100203008c7e03020004010032143e01402e006414400d06154000080c41c1c04203e601c21500b1200c400742c0c90b80e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50980534 1250 50979284 50979287
    0x50a0506071209050d1a06040905060a18060903020d020c010f090b03061503070801090b030c01050a08060a0306050c04030c0e0c09190902040b0c150c090d030c080406051b0307050a12 80
    0x20b43d2940540e802038041e81a4505004006e00c9140d13000e1b16418050080340c0341c0c18104421b8035600701c0040d100741c02c001e0103d0040c000c20790240c040b18200c04041417040c001c54a0301d8007203a41035602038001da00308641d075a0b107081e07050103100a1000d0900300401e10000801c00189401c801e402601c03070708000000420000c2d91929441d80d441c525040b146903030fa2600b46001840070400703104010445062004042007407801180c20ac070800010b0751014100608641c0407111081c3c054403664004402401c0400481c410b4003404d03214098130360780c07166540e242d403070801c00d07135003840d03010300c090781070324004d02442c01c0a040403105260411188404812019000003480323482c194031000c500c42c400100080d8240801016007090b030341c0d000940c1d140e070342c0001d0082c03012001198001130b56001082800e840749094040450024020b2070100d4000ca07241e82c903000725900542044002c02e002049101c1e814008000c050311490414000d1805c00750180e0700d496480c5c04014008003030003006481c1d0f2441c175 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50981784 1250 50980534 50980547
    0x1170a02030d090501111203060f0f041515020f060103330504060605030114010504050c0d020301090207020f010c08120a140411041503030804021e030a030801080601050a05060712 79
    0x10350000d0565425504041c40070b070460704a0b11070640403618076034460184140100f102141195500d4806186540d000c0400144000c000b02560740641038024450040e1904e12412440340d0207611240f0156080590001c1d0b03a4400b202030f00e085600140300a4100000880c405046175072240c0d5600c0d42c038144045034040c0c0c3e00e060904000321a201c455600b40d40059402060165008071010001e16459034103060907a400c4214007207210403014010800c03814a60f10071a030101c00780050900307140e8122031000030790f4070030f80c40150f1298000c9003500561414000c3c01d00c0b10750090030a0b20315125956259100c40c060f007102d02e0100820500000c1c1c20120300d0300000d20803000c0c40170b180164589071034020041549002c0050140b80383c4040c10111407401882282a00d81540f2403500c2c40e5100e5003001000d1803074461902c9202c52084c80140c881d02c041261802e4284a40c441e1041917050458482c03401d1016482980324817001d0000f00207030340b5010100c0e110143c004207804e800c40803411003514403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50983034 1250 50981784 50981803
    0xd020901020f0a0b010e130308130203010b03070605070b0c07020319080403020a0303110d02030f041a0c011404060c050405060f03040302070e01080a0b090a0804050d030c081215010305040305030117 87
    0x110b000b60b0440f0000c10007032030002d80c10f0f5801602100f04a80301d2810130300c070300e14088200801044540700841c2108007008050300d1310a100400120b55903101c800481d0802035154403407804110042022000c0001030307450207070300441d00750b0b640e0b04001d00360300042d903205101c0081c1c802c1300761440702c04018003d15070101c901945e0050000c940302603a80c0360091942d10307218484004c03802000e45100c10a8804812103c041603540c03640360a003030604010f06403140d060040c0400c3c2803403c04c0007d211100a0040c00d0b1000000500f0400510b00303070608605075808031a81034204142040103000703e9540c1c0c0c080d10910600c0140c0c490703c0b641e8618080c2d25020060300560303607401c001400003908070f10021f01c0c1d0b8005403203109070821548075590308903074440303c2400007000312000388800d101e24200380b458448060302030b00d0b081d002c40c04162174810142d44181d90703410450b030b51a82000078142e40700c0e405600c4c9400c06e01e400c101c98501924014141c1c00107024002e45402210240080c00000f08101c818 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50984284 1250 50983034 50983063
    0x11506260c071106270a03020a06051309060b0310060908030a050702030a1403090319050a0f05030f07032003070201080109151a0307080601080f010e0a020408030706060e010b0705030d02090102 85
    0x43e2000c8003000c07041c5c120842400c02c010290201020403603030400a0008003140d5000e40300040241c2000b400f50740e60380151104002c0000c480c0e01c00a200d001d2401801c0040c20110b002039a20700700f042440c08410402d0700043c0500c10300c10740c2044000000411070b1003903d214078145803110801d10000c0e06221452001500035100c29442b030352114400300060284990031001c4401d0456035881d440030140005001920b941c0100f141a40810068519040a00e105800b13482ca0b104485030380c40303030075007210038203030300285208500d68500540d180b03c0b42076052120000718208a1136900080840c01c05008588078561a4016550200f1800081d58060712070001d0505445041d684043c80702d070001c5908800180305500840d41a5014640305801941080d04003203540c1c2c03c5c042840e01154019151711003907030f402c03c000a4502401c1c4040c1c10068410140450150b141c640404101c20042e04000800d030310410a0380300080d0000102d400e41c45803aa8050388502d941e40c010303410308202c1c202484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50985534 1250 50984284 50984287
    0x41109040c030c080a0605010912080721121a010e12100b030114060303160302070e0405010903030e010e0316080412141005100608090f011506260c071106 68
    0x8070041d030507400c0802150a2030352405115551281e4050a5841c0ca100f80e902048039500c040c80350281c6030413038522050151003890f1802d02a80d80d405644030740204941b0303110210b01600418954014015108030341051004e001d001104440d03d0820710550409506125014070240c5840d02e820340820302903003800781500d50201490a003c4090000c001000d403095113000c2c0001000e000d4420640d001d07a101400850400b05a56a070100e0107442d01d0b000d60540c4034003200082e8040c2014009445030b03202e40d0001c80e03c8501803401500382c9642ca0003503074081c1d041400e000460034000054890310314a89940420050702810b1a1040344240d40041c04140030305005a024080e904000141c0480200c04803024005410446000c0ba681038488042803200746034100807961140c90350b41c1d00010300809031114071007050340712821603041004401120303204da003003001901e80240c20314500100f00090054001d031883c50000074004000c10300c0c03586400100b40a4184607001460583c000405003516 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50986784 1250 50985534 50985551
    0x7020120030c16080702040606030b2106271002071e0201050d0c0e130c02010c0203030103020a1a070807050a120509180a0207020301021909050d05030904110904 71
    0x9029094051450000d1200c4903202000140210100ca119015602e5000d0074035042e08450303654010409425a80e401041c8106409650f0318401c000040216427000241c4100710000d0003401521031022848061818020703500c207030000700d00c069009609154038040c8202031880010740d041c9111001929114071a04858042c0950340145000d500441080d45644071455900e202548540300081c002401800092803103022a00500e011416034200541604410300c00701d0900404040b2204c4201e413030714850040e041c1c080c420200100a0b030b2015514640c11500819151602403180001c0c0c0e400010050082011000540d5080380c0d000306d54903501c140a0802c5a510b156030360040d5036515001240031580c038003e0307040300c00d0820041d105040c15154560324420900000300f04011107a001c10983e00160f4080c03004002003132404140003052144058001c180540c3d5401290144409a82440100c0c4001082d030310004000c0310301103080d20200e5030f550050301400e403901c0c0e040350906400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50988034 1250 50986784 50986787
    0x20316050303071e0c02040209010c050a060621230106120c1806260c040608010e0c0904030207030609050a020d08090301050a020405010906030b1c03020304030b06040c21060e07 78
    0x1c0d4054803a41e40e071140383c000b4801030f9000d80c448560a4402088400300317044014100341d00901078404050420401603c601d403569414002840401c46080f5076504040c001c3e04035007110360405442e0f0034840d1116140d03650300e41c40340c050310750050128506621f80c140c0e50301a094110802408120180303002e030600500e8045c0000c640d90280e901500500c1c465400003035036030b106040449444400d4804842841c240d100a001c0c1d8081850800d8040d10115450342d40b0789009070b0b0020700d20751000094004403d902c4506203184104080e120b61b80440a100c08260300040701c800380c13a041140000c140200349085481c00030065002504091010040010b02c1480c10203010032b03200940090001e40c2d00c0e40980c5049202d10f000711030102c0d0b4513403402c0c08024440c3d4402100703580083c0c0000b200382900c0c04401500c1c414a40c0480041c0d00019051080000310b80105030040f406580500035250b000402400701d00340d41e807050904044005031240401055001003005012041c100750741e40c244100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50989284 1250 50988034 50988037
    0x3180c0b03070f0314060103020d0e0106060c0302010e070608040210210605040b01020f0d1206030f05011b08060604032915121b0d0305040b0301090c090b0a021203070203160503 78
    0x310000420b04510203283c1d40d0303000c0d01858202e41c0700b01d500030207180c3e01d0b04010342c000e4005018110000e079031240104891345c001d12460307001c0c06054541004200c85440e0090075601d10540e0503489812240e030401032103400c15112a00309904444808a0020018040385ca1040c4d5803c1000c00204a035554040039045902ca04241c407002c1e0f0b818455806040010b90b91400783c1400898181d00000020240c10312850b600e90742d01e11654004940550342e81c0780c51030002d4a0107c00d0710241d40d50340841240059070301c0c2c8060482e45600b0242e5081c074280380000c9650280744005403002d05088503080c8484010703d0504110060340d04d200400d400c0c01181000c1090030b942126004112410f200c0751011800541c000d03a2202c50301680c0803000341c440071321003000c50000d4210107000c07040c403011901c0c0324000041c5003e4040365000040610140c0d100030503000780f5034880600308608115425003a9808240c1d28600c000e00e400e6123580c3d4503101d004a246100d00a000c07607040b54140070303800c00c0010100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50990534 1250 50989284 50989291
    0x3090423010f0f120f0308090a0c0801050a05070903050d050f04050405090d0201060b07230a0507090203060102070902070206090f0a080106080a12110d0c03050706020307050d0606050a0f03180c0b03 87
    0x75082d602652950340313000404004000140c0a03240008a40300000d12031640d203607010010f04103691980d02e60b951100c084244035008102a03944413000c0041050492180c1c540c032501910b80200c4581c0303562511070312909030701030500c200040003900d9140e6400c00000c4900618004e001003020380341110807c0c1d00c81040b031910100550906c040040c41c44c1e480401d0311074040c0c03c105e4214284818400101c00041d10003005403082c0903850034400420b6007807007a0030080005000240ea0307850818002424260306400ca98003051060001d400980c0ba040d00391020003405403440440a4451030009250100540c01000e20350f00702080419082030218840326414406c0c040b00d210080340000688414500c0d060502507135005105114400b0b1040d810142801d029042c150315000090b143c90703046c6d0b802201c551022420000340c94103a060180705180c001c1205181c6241420400d0030018004010307000c0c0c900405482c0d0b00280300d54101b0040080c50160b02c480c61046455560744140070541040707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50991784 1250 50990534 50990549
    0x180907030b03060703050c040504020c10020f030a0c0207030b0a0e10020a0302120606070b060913120c02090a05010b0f090a080f0105060909030a050405010c08130b0d0e030c03090423010f 82
    0x101c0426201342c001d003d00d0740a807000c1a80541001d05040c10300000b5000034406624a101e04c0d03290000560300c6200074800340304d45202c255038a01e840c00e9982e0503100030700131306803c6610125080021a84041910350050070944011886488012480d454a624603541c40d03401440040c1400d08113802d68014181c500702c2c030700883c01c40c0e952482040010300844002600d9040c401c400962640340581d10300b944080c445034441c4c0e0103a0103031104001000c01e940c40b800842d040f040b0500952800c03841c0503a00500e0781500380440e6042c280050164000c0e13001c601c039038440c0030942c1174555070754200e6480602405011169071890745114540a00815240280a0611035001c80d1041c88080304031581d0148945850b8641032401004441c036004080f0142c400801c01d004024040500704401d20090001c00000e40d1503c04404a1100700c4005150010040d40b080048038100c01020090f90318081003201c00082c2c1d0000a422071b88000209001c1444148041001141004145002d102952501c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50993034 1250 50991784 50991793
    0x301060906090b07030819020c010902010806030d09140a030503030a0203010e0c040305070612180b060310090b010513020c06130302010b060408031b16030b090f06100902180907030b03 81
    0xc600d019102d0101c1c1c1d015210b94890304000d198040b034090582540c02c010a0751661500000782d02d000340807030708000843c0250340d448122040c250340c0c3c88030220b0f412540407009410800100d01c0d025020500e68403e100384002540000c2c1416526101100011a040020b9030365a1900c2140394000350304c240a1840c00110740c0d008623490a03142c0003560b040e6603101004000755802c0450981d00c2d82c500300268450140c46800c940b50001d094146c0c031125a02c03c2d09802018140300d0704042c02d04020300c01d402040c91801c00d80d4004120a114900e0441e0400e860501010b00d0141e10384010748210b00b103074500b034800c000031312400e80744068014a07014060341c003c002da0101441000201e105620860031281d000b40019210346041da5600301d02041d90008481c14048100101c00354007005d503005454010300542046804e6105025100441710440042d0a003844e08001c4030700c00e00098000e4034a210307030210b0110f48001c2c640040c001c80010040410341d6500d07080000070050944041f285029014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50994284 1250 50993034 50993039
    0x30301030501061a0a0305060a120303021201140d03030b030109020a030308090c010f0503060f040f0c020c0a1e031202010b0301050c0702100306080c1e060a0c050d080103080a200601060503010609 86
    0x4240e03654401e107941c484c01d920b190481c00b5000b18090030380580f10b01c8d0f000f48488000a822101c01c5920700f510b034460b03100583c5904003c0c080999910050344000e94070310158000e50141d540d01107800715116030500f40025a6010b5002082c0100710303902e0001e42218810700b020007415040054184100b08401c100c40450000000444840800314201d2000c15801d00100301145010381107140b40800c041d00001d5900e2201d40b0240599030382055072000b581102150340307000d050501150b8040e0101000012100700d6601789241425000d1002529401d00000e124120034400c0d00305075090b031002402070044d07003000a115030b25548a045c1c1280306400c101969202c09002e40107547c200c94190001d4010207107100240030b0f400000000c01c0444c2d41d540c00003607490307a076280b0190251384030981d100540c0c2030706407a00d64034108483c0605401d201138000100b00052405080702c2c04031820b4a0000041801c0c64501101913095030b030204468003c9900200b440c50744200a90304940041d80c2c0c1d82501035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50995534 1250 50994284 50994299
    0x19172101060c080301030605060105090a0b0406020c01030603050706030506011b0b0a0b030d08040314130b0309010608060f1b0c030a030515041a0402030403200f06070504050607020d02030c04020c03030103050106 93
    0x8a040750000e05680084c0300400c0414150b034409544182c060410620b410300540c00581401401d8101008000003c0b806111300e99041100006024082c20708000c014210740352907603161031511480b0209601ca80020701241d01c269030b8840308080c00103d41203240224134100181035000c03203140354aa0b1038800074201c40e29001403c00351050803506e60402903166074504481140ba410b442c540c0c0b4001c10001d14210030080103e0100900100044540724185801001c0c04e50f02190b22000d110742c40354084c080d40740d5100c8003450f000100015940d102c1c5480380c0318050039000f1607140050070f000204180c3c010581607040244504a503803480320310451514100803c4405059422402c18001c54690071241855030003150468000d040079208006160355a520040d1308020000d40e60b0850918645d038540c0030868181c009440341400c50030030707090101280c1d1a01a0b500b0183c400d11a140c0170f04290b44080c0019000c401029005543d102c9000d03c245603281c2c02072004a400b036107824800281d91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50996784 1250 50995534 50995547
    0x3060207120c11010f02010b0d03081005030d050a0f020109080309060601030e06010f0501030b0607140708060c09100e0a030203030310050f150702060a090509040f03020d111917210106 81
    0x6075403000c0d01806000d000001181c5c10812248108159965074505002d959290800b0054040c40381c0d440d88041d00e0315100c504040d10440c0d04c190b0282c0e000211607158241c00c90f0955000d01018034001c0310f03801401074200d01414041002400c2c1d84000418041c10443c04184d0303500c250420f03203080c0460001c5400c8540c1d02c8209100385000d0650081c400d110071b40c82034001ba60f0840c801031206d4108450b9803518000c46c0c214031b4540100c3c2d844200d08120502043c002c1c140d000e9002c10b40941860340e00d0740410380f80c80000c04503404003c00c030491405240da5040451000c0c50700941100e480c0d24201c00000c3d00b0f0800ca0007401d115088140112001d4540921669100700e14421407504040c4a5401e000d055000910500140686040007040d0b03606c9450720b061049015000d0311541c081c80742400b900740107030721008900304036040160000b084000950500c0512820203200400d00960904030f503a00032a1940b1200054002244112804c1c100c103d85d6001103c01d03003a1040c2d036138404041e60b08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50998034 1250 50996784 50996807
    0x90c180b032409090616020f060714070606060f090503010b0f0f0d05010c0203071208040b060603070203041a0c0d1d06030a0f0e06040b010f061706060708040306020712 74
    0x2062007000090710444400d0b00b0004440342100c0b060802248803030000f0001c01c812036800c080c0c0c0d402032040040c1c030303051141070460100550020b801801400060103840700c0005040c40140080b07410065502010101120078245e002003040005a13191040101080150011800058080e1030081403c0c90181704080340c10340018010306401143d2410301880035410290290711858817002c140200c4c1d8207016020b10143d5030f5014550300d03121450403110510300002c2d19001c01c0448000c2000040d00c00c01d445802c220122880f070b07180c2c2e845580c1246544210f0300107102c17400c0d07940e11000400440d040604000464503060704c4011000b040211040003100403d03008100c4a41ca071a01030b81088402503422805101000c246a41c1610002042c0d80b501c454600300b650000042000340200f05c43c469014000691109030035524269004180c0e29544515059102c1540c0c040750060b65000308584d01c840e40710500c15141e40d40c9042080081d003040c2015114509004450b4814901c0b600d1000031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50999284 1250 50998034 50998049
    0x6010501020f0715051909031e050604060915061202040501170a080918041401060e091005150d120306080303060a0905040201031e0e0c030312070f021501090c18 71
    0x10800c0c90500e62841c00f0700342c0486403017030250800002840e071107403008200c981c03280c94480d41a80362461070329904500e24050700301617a090030740e240c00c005140855a40d40203034020002140301e09243c2020050000c1e03911443c800c0c58601240000c0d0100c880300c9004029001700c0c0c00300456030f61071108494444000c8030524094006e07442210005140802400a44201404400c5a40421480d071781008000b82da041c0e41d103010800390300600b604240140c101a025401400406080403250540e071a40b00214070412951940d0008204d0100391f0f48015000350020f001d10b00091240c241212019503104021000074101100800c03801c2000048038003c0c0d0b00070384880c124504e080034403c000c1601500803030402d615212103200071500c04400c1000c1c58050b03a4005a00800064000e2401d290102218080e42003030101400c01c081c6003545690041c010b0a101c0403086404100320b0911000c5000c28540e2403030b500012682a15680c0401740000c1d96442e508461240071000b140d556085100c0eaa4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51000534 1250 50999284 50999293
    0x10b180601090e0a0608010c030504110406030203370b0403110c010203070f060b0415050f22021c05070206012c04030f030e030f070203010b011103030a02030403110307060b0306010501020f 83
    0x200801d00400d80300d50090100d640082d005e07807502071031400d440708020300340c0001c2c0c0c458050009007c0f44104140c046001150100400c1d80b544c1d01294480100b000d42c01c40c82e50034071210441c1500d104560520f0040010064210348410349040300c0700c3c51044d1020303000500321016130039840c0c400040b15030b1440d1050700114102007a584d14050901518941100c03125203138442074107162280d02640c64211642440a208142000b041c440e604140c44001031141704000c020b207101c119512010052581144400f41e42d442d0300c841402c054240300004411305519000800c20720582c0806c1d2581a603142a20000518407030701e60344204242d182d1030a00040b180c070b002260000e40500c8181c90303600000e081c0441c503000d01c41c8649056400c601c403500c0036264001041402c6150a20138484040b07000d080034001c001a4456203170303807800000d00d01d04c1141e034004045402c1c107016000300b214a00c0c006003120f03a9030705580741240142464060307160280c0301c0e40c000441e6660022540e81c0301d0640030001030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51001784 1250 51000534 51000539
    0xa0b040e01050321070809370b090409050c0d030503010e0a140720030403051e190605090721060b041a0108041703040305032d07050703140408010b18060109 69
    0x14100340c5d2100d2001c6400e00303070030000740d0325645400f08002010300c14449151044000b80600e0000390b248070070b5404a55001d840700b8446440c0703da09640c1525002c6e0703070008040d042d41c9000382c1703040c6410072800e91051102c0806000c0582c00801141a90719004d01c00075030351140f9054030107848400245020f85620400080c41403486100c101586c140050f030009010750412611500310792040d0000d440d80e400c042049507084c40a4415a080c8040080060034050003a1554080700c640450000b03004548030404100054403c11500e009004a940c4642d00200b0241c403880c0f610702c03085011034629007802c48200342c034a0f1621801d141803401c07a178001c80d00650b103401190030000040080b510109244a03e440c5240c0c800003451140d4466110a0b66a0600313075400c00c45840d005442c02000c10f10904d52000c4150162242e42d0000418140382d40c44001c0c518054481200800340a49a124081000034183c0415000105201000e0b91032400c0488400c0c0310030400b12003160600c0c04a1030181d800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51003034 1250 51001784 51001843
    0x160504051e0f060d0207020108060f0616240f0506091005040207020111030d0b01140304020d140118051b0109050901060c030203070606030501050403120203070807110c0a0b040e010503 81
    0x1c244107010010450004000700000244054200100d81030b0b0300395020170200d0031541c200c00f445401460840340101c00c2e541c2c903000a41684204250701c1102d00c0a002880304000106181503500c5540044002480006102c014020410307503000f80402424603010825900306560b1a074000d10342191840c0c0d0650400b000c0c8406580304800c100e0400a50440d43c0b43c1d5408144058806206800d4022071007020010006101d60800703540114518000c00a100060380c1300291441050b40c05690b40b4410000340e0344050050800310409442c0441e901c0070103007040804510401c0d5800c00e0301020740362044203001151003181c68029550408a05001804080d0081200c0c1c80c00c1413180c07044a2810480340d40d070b0010344406501c210b903140e44030350600c010103410103041040034003031400441c198a0020401404080003402070001e02110428001000c0010700044403c20700160040708080d40e141d400407119801880342104074496480085154a0041040e07005c00b035150440c07018810b009203e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51004284 1250 51003034 51003079
    0x8090703020f010c08040306050a06081902130605060705010617030c1009060603021e0102010b010e010e09040c09060f0504050108010204050303041e15031e020301060c0b0405030d02030f16050405 86
    0x14543e0510446001620015010100500255101e1100403500d42405490103050f03c20340d80042e402c1e500407484400c041c0780301c480160752454040fa80b440d01c040c950414a402040d0765002550084800964034060100541280342103c10041501c008408086401a10303070007803403210b15280d0000352000c0c000e02d216400408181d0701886000034810340c1e13a40007132060f800d10360203a90301803500b81c2c00c04125078080c80781c042485002c1c05d002800241c244002400b8050440c0014132400c3c600002c00c051050506016010b0480f080302005181c2c0c5810120004031000d00c80c4a21032804c2400109180701e040c0240d508980f070180041d400c01717050403080d4818110000210302500b0b140c000004000e041c00404c0c0d0b403054980d840c00519481d0b042100340300c140701e00d00308448050042004000360f942c0400443c2d03183b904420719111300d0f191490101d00310701c80e000700600c50300c0c004420b0100b52817038a90090700505200784240c184220211090300e8a000b103102ea0b50780b148801c207905c031000000a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51005534 1250 51004284 51004309
    0x40c09060305090f07030516120b1f050909071415370905041515050c010f0903090608070305040506010b030603030903010905010204051c020f0402131715070809070302 74
    0x41501c419140413a1054503221169105480c558006040600b001c3c0402840e20050b200c0000c5080580700551243c2e118000041e03c801c1c0c0b0303141144404030010010f0120b01015040040c003008880c00d04044160343e03260301d806006c030800c482c10b4408045181030300c8098028140303801c0403424116007501e8824100c01c0540c0c0302c49804843c0c100b400c941c64910b25103a80315180c646844e010a8204410b00048803458000b1041d242c02c030000600c114040856405100503e524003d952000e8502c0402d0240000c034106075052400e0240c03c00400d82c01000ba00d06807201550f592905035607250080b0103488044da00904180c000000500804194070002c543c081d0b0041c045074508a803002c042400c441e840d031402e1f00e82e40d502040074031480c6400a290900000c82c40b40c600e51881e0903400003140382511031b626512460740000d03502d000a07031a40070840101101042e41c424080138075607058039191300406090201d0051000030304040e0240c43d0407070050710b40e0401002d0792429035081c040c1c4220001d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51006784 1250 51005534 51005551
    0x5090c0a12060914060c040303080106030203040f060b040605040203010902040801050c030c070303052206050624030f132009070c0f03140c030c0304080712030807030902060d05090f0c040c09060305 87
    0x1355166180150100401405024804030095513a451420300a0004606030010002c0500400501000c15400000e403000f854004d0b000046456080d000940103007040c0e4016038200e400400005a400505e0307025100311010600240003658035903d010100c1d22041707960000c180303401e00c00c00c008680700e03610031507000305050030024031031200c11400415010a10000c44003951113104124a604250307010354440c41c08200d0140c21550000104d1800380070007084403074189144000074086084a11108440e1608001d00504082d040b8020a900d451040e0446011341000340100700e40300d11804c0030710440ca401c15203110b10a9031541d4101c80d007402c0c003c880a2001c41c1840141e400395000d20007826489125030055035520300e0700d01040c0c14403c070791b448143e82c0f2030385804003c00300380c2260045070301500c9854002010401d920000b00207005520040d10014035040811144107400145c0f0b0501c0d40c040d6040702d813441d103404100300135583d40320f40040016060036070400c20580290411504880755 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51008034 1250 51006784 51006803
    0x1110a051e090904050102030a060e07020a150605040212070e0603010506030402060d091209080f060702033106050a17011401140403020910030b010b0c28120305090c0a120609 77
    0x950006030640c0c3c003d58042c1c5550350f0000502001d002c00d441000010700d00381481c1409480c101c00041c0d1580284000a4600d09000d840c5110b1180c7c16845540903040c010821034444141701210080018112012008910b481041468030b203041c01c16a03049800041529141d83c3d01c5600b80030107604052103440402c0e403108412400106c164000041180003562481101b0749000313002d034941200e942038013103107800c00014130004d1680132085030140c040c1120488800f03a4850107100b443c81e05420700040c1001800404141954050000c0803444166500d2041c90b01407070b43e0100c00c0220a200f800058035540700081c08950146046070510170035214641c1c1019078940214207084012240c032846842c041e482802000300e105c0060340074286680350076007040455115160741c2c2100301980041ea10072400660138502d140c2d15a40c043d240d00407840c1c410140e00d00c4000d00640350681d41001240101190103c0c0b509106100c4822503c80080880c403d0040d91500402407600c94404c1d50503455 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51009284 1250 51008034 51008047
    0x1d1c030203120103060f0609020f03010504050c0706020d02030f0601020f0d0e0105070b0109020301030302010507080103030c0f0c17060a0605010f14030606070503041d060906180903040f0f0801110a051e 89
    0x81000450f000714000c0001081c4603e01981c103500311101600310001051040c42031070800300005081c0d80c1540c4c0c040e100054591204400042a8012180003c00e554000595403241a20540203940102107000114544d40c4030b060040e40c4403035900034204410350000e8044554180300c4c0307148010780e0380103042c2103203401c0710b80c1c840182d8204242c200c07510305a00040100100f55091181c90b0b444001442c0c60f600d154190380c0d000300700b026503401c00740940f0026501c800070b01441000400082c4000242c4140300d1510510f115118001282d0b030000441c40e1000004036540207160f5804030100f182d485640000c00782ca0847e0b11500068813041c3c20000601c8050000389080004002a01000005902860300099a1608043e008007d503014043c200c09211541d1910368501c42c1121040282c0640c80c1d4610781014514000c99100440514040000180c011003102080f015198044001d104030703030303000c01c50b41c14610a00c865400021001c110b049021350024250755000000100114544107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51010534 1250 51009284 51009307
    0x60712050408010f06031511031311040504050607090b1e03150d150509071a030403031b0e010212090a0302130612060609050603010606021b28061d1c030203 69
    0x4e0104102d450629554070003401480b0b0000c3d42d84c007143c054200c050002140c3c1451001c02400045d143c2e078880d410450309a0200b000780900428a250094020851464607041c0b60740d88000944081003c28030498005c544120001c00301c801600c4010f0307140c40c00c0c01c55203850040d20b60000f810341c45c254900410006d5140d1316002d0210340349003e81c42c91030b0b034804074018a00c22150045c00a800d542c2c0101c2003003201c0f2030b00ca443ca0048103101c035045501e9550b1810180c01524150106c2e2074030075200044411500c0d04040c01d8003481c1030030f80c21076072050a00c403610a151b00c1201040365203e03e103030000f000186041551540c4414030a13501182c5c1e103a43c1c2000d021051900801110040e44484c0309101c2d80c1c0c1c0522520760720240440c0280070315460624040d45400b045014a10440417201c0d0344084c40e181c0c43e0800c07007000d00c2d0410450100618038103052940a96000740710010780d418408400d0702420221070040180010001a400d003400c008028000700307041021825400140806a040c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51011784 1250 51010534 51010541
    0xf060f010e090708010f0f050102060402010e06070f0804081b0d080703020f0d03021b0d0c020f0d02060d0507021507050316120203160e04140a0207020616050705010f05070206071205040801 83
    0x214102d41350030049504100b005c801d10306982c0c114818210b0054001c010030b0b030b4001407844d00941c0a0806804108050020a001d841011005000d02c2e81c04d10720f00c000c100804004004840340319050704c6c80e458034035010101c4179410f1280350340e00074a26040000801e00040080c03074203908c04e0040300d044c50621610f4505007005485080302080d404610080348210400c140300303a00a04401801442d11203401c040d00c1820118406070141c09400a1034200d0b440303903c0c00c2d00030160001d10f0252603000d25030458001e4403007260380b000140540307400b01806c00078481906018804039243c00e4110b542e01424080c3c0140d6043c01c0034100018140b808400c4e0f0780e64402140141884e4103410079849114201615142d8203130085805039140078054000e20301d011480316040a000d00000d61350b01110b000080b03181c05260380107000d5807804072140c8101f100000e560070442c0d074282c9946401024908054885025010001e5004002007102c1800607507001d0140c4160511380c104241044c2c0c9070007005086 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51013034 1250 51011784 51011791
    0x3020f0f01050909092401060f080402031002040909021320030a02090a03030206040620040302120307020a06092c0604020c15010602010911030304060e060a05040b030a02031602060f060f010e09 85
    0x40e81c000070b100449030f0001440326081e492101b040740c01c1d41d500d8034400812a900c00c1c5100010022084003060856a00b4003603802d00442c585015501c460710388003c0e2006120582080303108208243e20318084140c4e500900e14001261601d520410000042e902c1d040c0d40000c01c0300406649c01c12036901255100114000954000d41c000e0465250915007a012a205580c1a8020300640314182810b03050340c4040f00c050309da060304c41300c8a0b04043c2010503d14018038070001c5d4010f0048a000c600264014022000c50b081c1485501e030581d046180f006030180074a8645e07511200c0b49000481c1c900b084d80050210b0f0f0b08031030881c0c0034006c80c0070414060034000c0c0c0050b80143d440d00c0c90300090000642600445100c11800b441c40d2603d00b281c003400000051041d130740900340c049804600709025400b543c0023041040100ba6880c03500b0340c00c080c02544102d80100c94840d58014050526100142140c80b41c0c100c40003105a648034902085008d840d20078035181000448003100340682c0710940d41501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51014284 1250 51013034 51013051
    0x10f050c0a080d0c020f0c0d060207050706030207030f1d0405060d050105071107090b09040212120705010617010227030a1b0f08121c061d0609070903020f0f01050909 73
    0x225140302d410342c0e0007918413034201c141c215800b64121402c14400442c410003800c90894a903211140f551420f00041c2c05440c501a007207010740f00001500c984c06800038508076229070f44040ca00406a02c05482400840c071450a02c18504144010706050552044e500100010b0220000c1122541c415003510022103240d0700090100004136000401040440082d0440c541c060040791058170120303071030401c002c0000e403184005080e10714034a00c080c030010100440d03421010ba40d40700c4609119000c0c1125200300320003a07481c90041c1d0340c21103041c401e0302c1d014084c22a40d049040391001c0c440d0100d1000d1014294540680c04400e000203a0043c00c000c21f5101d050120b030312003460983c01854109060703010341c106e60000128850145610300443d2034541411071040700488043c0c2c0810f0080640d50000400030382039856a00d569001c1c00500e602c00c28048460360100e07580e20034210b620300454400203420003007513802625149050706041ca2a22018507200d03007400d40090008000c800191824071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51015534 1250 51014284 51014287
    0x504210209011a0d020306040603230d030b030606040f18060e0d08070c0803150907030e0106080c130f111306030c0203070b070305040c032012010c0e010f050c0a08 72
    0x4114109a08400d0043c010a803420350480000d410a030300038801c280401680690000020300b0954881d40041d003c1d54001c44101c14410600c0b0b6142070060b103011b8440c60903c0760780484072005101c0e0203101c84031803018010703006540303c130402d0001500c9107900e8044a207480c0c0d80c50710000b45580d180160075a00522010912040c50351070241040c9030114280d0402c03c840c400c01c00c2440c1c00586c0815070f03542c0701814a503261f440180c2c6280c809030305204d4561040002d4203102c0e545a041c1c10a034405189100200045552400340c15580d40034940c03c190080204980303400402881e50240c0c10481100502060a400c08030201541b5402405244080c180110341400466414829045008021300040d0300c0c101240c0c40f040400b400042c840d108154485d00090108141c640314800159800742e1040d502d450300702200d11420102c5000a03000e513007101c400040cad0b00814080c1307580c00d81c440d489980d40c40700d908004651042c40c0b88089020702104201042c00050104807215500b4028140075 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51016784 1250 51015534 51015599
    0x61416030b0d2a05030102070f02040e0c030d0f0212040303170a0501180509010b0d0c08012004142b0215120106050309120c070e130804060f0504 64
    0x14084070144001e9034054140e2460b0800059244242500310050890f95041e02d145940b40c3c8686a607455048150954000700b650b804224100403070641140c800c4406110386003a150b400c0d5aa0340920203080d40c5a030200914816080c0640c1641c030b880031061040cbd81d02031060b406541281d0340641d00440002c1c4005200f1444440b034030004036084503c400b0140400e51500400c0b464105407414a02d5105a03640d01049140350b0940c8160305442001d00b40ca1741311902130071700d14030400c1540320b081815400c14560300d042c0d0044e62034822114180211460425042c50f41d00340034603030304221a54000d00790700803441c00c4c018600f900d2600856100340003e51000c40d88103003e1b030550741d000350b00d440c504188440c414003000403800317505603600e5141940d1a9a07a1030001441c1006400c0f00c4420088000350000d08034401040c288161014000812060385a80b03113403a038040e60b038a90180120106000a0002910500f0007403102e050900d806070038140c45440140c2e9568140750841196116500d01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51018034 1250 51016784 51016787
    0x11202041407050d0209180a0515040b03100f111306020d081302090604020d23010501020307082508030106021609060503070b03040c0b0a02071d0402010e01050304061416 75
    0x100e80308203010380401e020714140000090194000c081d2120002600469643e04a071074006000514000d01c1c070840f5046e003450594200104002e6030030311080821007001803201d0400340640640c207500a00140f0028602c0c0030624000d0581d000c012000d03986400d4402c5290084038054840d590031080040d02892620070f010f854034101040f0801844100780c1041709002140c0b4283c1b1004d038041e25449401d40d18035001400a1141540f80000782c5d01d00500c0e01c0c40b103e400b08481c0e54200303800d1190b54030f607600c0741b006990304d00800d00002c10a520810071013800c0885221140d841e5503214495660600c55559030202c00c1e08241c1000c2c0050303001c4244521100d0824000900402446c602002094105001710340c680742c8034095840411070000100302000f6808030500700400d00c110400e92250040e080080d00d8103071a01c034030f00b0355180854800e481000391406031401356030705854014000355200c00544068000500c16140300b5620101003a0010080300c0d580e10460b400c1c50441d080d030040880 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51019284 1250 51018034 51018041
    0xa030503030f011e030b090f012301093605120904050f0403080703110405060a020d02060123090604090f05010e120418021c0204030f0c050d05100e0109050601120204 73
    0x41000000707400c0c1c100c08480004c0400015650001c0c1000d03403c0e520100c8003460100c003041406c55640c40c1c2455a41b0b4021340962248021450040c1e050140c0d170381300c1171a0140c0e83c101e40b0840100c90a56071041c09002c194000c6840c000070440420000013087c1c803070310b00b000c0f204503940144c002c00240b0404030380380c00e104032641701c59680c582001ca4203054800500d0318100411050500d503440342e10401e142a00c400360ba006060050401c0c3d034420b0b01d15002925085400354a4026100303000020a0700c21145200c0342940c1100c04060022030001020404c603404003070280340c2c100e40d0312440400412900f041129040d07001c2c0c000890180d40b802807442c41c095240407007d1006105000c140000248820445d0b140004940096203e1000d500c2e000324020340100e0503000584001b0f0300008020280012400b00f50148000722041940c45042c0150341816101c000d185411036001c014202c00d00b40d00c401800702c10b002c0001800c0c54a035031290f241c840207801c400e5124480564050440c9850300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51020534 1250 51019284 51019289
    0x60301020a120e0c03070f030b090a030c021012020c0604050c01050c07030b060f06040e090115050f0409030e1507060b0402040303020d0e131d0115080a020f0a03020a030503030f01 79
    0x14000c618000109000030107a808180081c81180d480c3c10785524414000c00c400e12a100380282a03810b100d95400c00301082c13107140e100440b848581000000d2548002290040085803d41c540e45003003000c650803c078900400417518001e01c003103600c04000b14100e03403014054803010840102007e040c1814000e2510740c035040e840d81004410803107460204d00c0442c0f200101d0b035011090b80d40715141c150000b02000320700d1480780e41119000c10006600460300390f8060207828000d000304003a21514a07000d0741d000b135074020f164100c1c0c0010600c42080c10543d22002c0101d01a20302004612200c400085401e50f001007080f40100c0080350b0038042c42428032030300c1c5040004507011840d0601e980e1b4044d48400424002400380051700300d11100a07110080c145034620070f500801c02030320307508082c04140d410b8020b9408250350700e40584014501c0100700000241c64a074070081103a60f03101c0c0d003007040081e80f84001c550400c0c5a403e0000042e00e404040300f0285d44904081c6459140441c40c2584824059 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51021784 1250 51020534 51020539
    0x70311060618040807080f120108030412120201091502040306051e01030821160f0201060311040902010c06020d0203010320150702010201150b0901171b0c120a0309060506 75
    0x1101441040e035a800e03079050b0041014490b00d2800d64580c100241140503010004d03090150010380c0d04c1c50780c4040b9004046000041e00c40d50003d90721510101e650340218080c94183e41104944180494443d07410b00c10700c114184000b144d066102d03503c01480b60045160b1401d010b070040b0f0b092080086500405030300900b4421050050380c05004810400070040c44058500140041d50042800078498010003010101442030124100302c044030f41d441042d03480070b0001a20101d0582020752040c0288030489400900700f0f609003800008102c02011901c0e022814045c40300318074400a44180003401c070800c490600141c6a624500303000070365910911513100040c02c1d01e50b8140b01039031400c40c002241c40300c183c0c8464482801d03200507030040038401104000b51150402c00500702e45a08000c3c295100b00382e0f07880c02032600d4407400000149003524480464483c42640840c0b180214001d00340045101e4101c03100f8488400064170541e000d20007000c0040d4854400c0c20a01009001d02074008406 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51023034 1250 51021784 51021793
    0xb030108010e1c0311040b03040506040c05040903120b01050418050f070f0203070b060402070b09010b03010c0302090f06070c0f0e010602010c1d0d021f030209030f070b16061e02070311 81
    0x2c51403088000d00150702990030f041d0f961940e44221062001610087c00301441000e03600d08280c213100b80c0d680012a800c5030446809400854142402d010b10008241d064894990841000c0c3c04000580014040d10f41001400d01c40080c0c03c008000b4505007000c1800c00005003400c1008411409500082c841c81c01c3c0000348600b16907caa00104441d00340c0d410a511802c15122040010301031b200309500540481d000174248005120194410071210004400800415a131150254281c0c000c440c0280e50003a1848074100040c1001030092000900c144a9544104d850300d004486180444c2c0061100e4001d003030040c00100d0302407040000e000c07060b06041da24520041c4540800d8104249094002c14403002081d0454a07921101030321070110050b5803500a5081c0700003030094009440381442403155038148036841c02c000c502503066503840042646031444c001c80802d8000410f8004660b101d659461150140c9103901d907801020130ad0f141c000da580c0d5900d00300240800980240302031117412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51024284 1250 51023034 51023053
    0x905150c0403030f20012f040e0402032503030906030615051b030309100515011e0c060908030105040515010921020402040b0408070b0a0206070305041b0b030108010e 73
    0x80354141d41c2103951620b0101880c210310f0000700c0c1d610400c0d14218010045410404042c1d08040d045a040c0b036010002a1a002415601020501c0c071281c5a07042880340c2084140041c03104d0a01490b40140064210350242e082d45440004080780e02c42aa20000340258081c01016400406c0d0002460503140070301402c5d0626101c103000001403180c040c00c1c0000001c25143d02204a041204803401a0703040e40d46034500300304c402c0d031074010383c00d552052580f40c100040d00c050010307016240c80f500180d40b0807551560b401c403648141041c422816081c00f518100141c0000e442d0b00809945d98803640035031762a9407424080c04141c80c00a000c08104c40440e0031001d1060b41e100c0c000500b200c85d10007039200161450286e40004000d4094040d400500005011482c4000c0d02c005204441c2c5420444071440d985a00c4440746000c2c6440047c0147c0012000c66080362194002c01e0300103005080076100740d00310000c1d1003240002039104001c42680130004002680f070038030a070014101060080d196040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51025534 1250 51024284 51024301
    0xd03020f030a09140105010303020c100c05070e100b07080a120b15030c040e09061807230f04021b0708120403230307050c0a06031814010f020706090515 67
    0x1c0184080005a07903115000d0030b01c481e401101ca0b90303d040f50020800e41d612410000d440c2c0d41c042340b4190040305091a0001d8061081d14100d02d05030f04400600345003414805804400d9102800300c00b0b1180440070007140005a020050005520030201613594014502c80a403202504480700f40c078492601c911047c030380d101d540c101907030700c02c400c10080e58a94405450b401d0034051900180014500d450030042a400001502030060b00f0700320303400644540c15a442507030707a140350282c15008041c20300280000302040c1070248038104020210341d84a1460800f04089801602407198400d01e020740c1906190b07410f00c90940540040c001031304504040c1c0104800c28852484020002c0e40d00780e804400920003201048540342c0c0c04c0b0252542c44a40e82000380e039420b4866810391084800b0500051081c0c02403107107030b9078a01e514500c81c05aa0351901d0341d000c4003124031510b0441d03540311051482522064401040920b12a02e40060030105600702186048440110b0b0311040401c10203002e0f004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51026784 1250 51025534 51025537
    0x30d020109030e0d05030334080f0901020304050d050d06090c180902090102070b0c012004061206150302070203010b031911060301120f05010608030a050c10090314090d0b0a0e0d03020f 81
    0x2028055101c5a2034403404442d0341169214540c0c8e040000c03e060790581555801151107005d20043c0039807007256122022118207d00c016075008002da884000048110750081018281048031424009400c46e6564441403d8550b103070010340020340c1c0d280301c0303404000300142c0742d80140c892043c046090411020001c0d643ea0401c0c06001040b4001003600c18241c4402d4004003058403c190010040424030034595110f80c10601540000c120f400ca102075004d00c280c0b10704011201c0030001c17001c201d107420318258029400074005903099525001e0003070307403600c0411600405407a984061444080349080c4038810401d400c070315510a1348200010850028040c08000d0160340000c40e10745c0403c0740c0d2404c10b004021640c002e800c00d000104000c480340e900480503040c48250842030f202648030342900001100c65591f00140800d04607600c1c004000c8101d40a0014007101a02c1c803c800821600c41c0c404103403088400d0300b8120340307641c1c903221601018024088500c2040c1415400d0500c02103110301076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51028034 1250 51026784 51026791
    0x11040209150d061a09010903030f021c080106020c04020906030604110705120a080105040e120a0302040801110414010207060e0609010c0209040c360507020c030d020109030e0d050303 80
    0x464020800c80040d5481c46011204403101c100e070181c0d240500c00c14100506118031521034448000c03d2100ca0240c4020221021818160340780d4441a05580c0c05580f000104a034080451003a040300801454562100030b00c2c00283e9143c5411540c50020000c2c03078643c0341c040040c01036005006031022902c810b826640c2194044401048030000386005070520b0007030710b070042c000384901d1160701203c5000f0070003041800d000341d82d850601da807101c0610040d640a940c0c0e901003580100c518040c4001d156001d0030030b800c01c0b45000742c60142c0d1841101d09584d81c0c81152103c10500190800418484400007041030b1401c0c000350450303529218001d000019100d28060040c10300042d4800240c1c400c4140d40c52203036004005180d14105070a1070b6004140d14052201c003038801e0100440c12512111803c4803104000f29504e84c0003050f6540000585800b03084802588201401303803081c0e540501050201030b00c41c8d4000140c0100301c0c20005c2c00100d0340400c0c2402000121010000303d600401181c0c4d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51029284 1250 51028034 51028039
    0x200f060c030417030103030f03050c160b040206041502030d0e0f10090503040902041206060902030123030c06030103080d050601050316051303151a040b03060106110f060f07180311 79
    0x201c07550769080040c1c01c041d080202a1900900000100030550840e078410b210412540d0204200c0c0d54405c13820301d01e44915000d607103010651a11443c00102103004c9075500501c0034155904003960341d002d98860011622043c000b42e00042642c0e072161640784544040408104001c15421054640141c0c5a107030401c04c94042c01e8483d0340b103409200040046600404040500715510381c1e4518190841860401c0211986801e00300001a152500d00039641684d400c010141d0518003003d401e10b0700c40d158a410150180140c600480060761082c01450085010368030040e6a440c1c611170a8080f644001c00c8070341403000900600190100c2c0c545265005c3e0240c0c2856a640c54030380400821a490a910040490fa0203a04d88440744102d50008001c076442c902e18035070321008a4042106490074001c5607a0140e0010004225281c482c91101454001c0c07841625076003800c2803001c9080020850b4524107002d601d001b402107a50384084004c5c1c4c0c0c1383c100031504000320b040d03944400203803000004842c0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51030534 1250 51029284 51029287
    0x206130c120c1e17070305030409020702030f0601030f050609010615120b0a0603020a020d031404020906061207020c0108090d09031401020c1009051e03030601080a0209030d200f060c 80
    0x1400c000d1103000d404098541a0140c0a1800580040c0b41c550300709801150990698411300001c10100001d008003965401005581401e061500c1c4000a4010780000d036814800c0d0b54408811140510a29000c1c40c0640c220714080481c40c00c046180a0001d001d1661341e0389002c10400030045602c4881e400059145406640c0702595891364025004092030300c0d902c800303901000168a030b0190b00400b60b070880c0707800b0741c1d03607039144040c0541c00c0320a09845a1029034401c00007038010b03d019a0661350140d03000305094107040400810446050b4202c0e00f100150703104684481596070011180360341302400c1e000414426101d550700030700c0f0449a10004102c002c080c1000e98840c4802c0d01516100320130349027240c0c03009442d108a0000342110b030380c1c1070382c0600a0003218910348424000c4491b1401d4184025851900d40b080111100c0400034409a500d40c4e00380403460440e542030007100508115a0b8842802e0352941060b401d20b041d09202d52404c0d980304a841804803e004600c06a02212884109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51031784 1250 51030534 51030569
    0x603030e1009090b010c0b090a02010807091a0a09030804030c030203010f020408100504021203070b0f0a05070903030c0305070602040e04150c120b180403050d06080c01080115210b010206130c 84
    0x11b80742d14a01c8040200080c01131803c0050407200000c1e68880c40d03000740e848034103588850030240e0b101c2c034190150300207041c1140074104425488400902aa14492a2100060b41d50781c44c0c10b2803a4000f6082268155a0048100b0a5103800d0098840409141a0441c13515160030350003992641140c4000701c01e03c1d2100e000030203540c1c940700b07194a240b28000659a503280c503460000c84100c002c640c1c10001e80e0076200840d552603001e11880388110241d84911301964110b40f003e554a9030503403011010800104000c0000500d07500141c03009101c0c2c081b40c242941814600148403c6003004003201d241e2411445c0c001a6034011907061003043da5140000d06030001801103409201900204904108440240810150f1040060840d0500007804100c10340d25503014903140c0290345015400102000c0050156004e20307000c1003110030307160034200300122000035400000c03031a02841c0340780e180d40c2e607120702c103503580500001c0c2d40141c0c00085070441c468142da543d42184500c2c059036030480c2c10030710768 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51033034 1250 51031784 51031787
    0x90e0f090c09090d08010f030503271e030c04111806040801110403050706020d0f031802041514010309050607080712050103051c05070c0902090a0f090603030e1009090b01 75
    0x15058441015120402c40e1030050a6107035582800281c840c0042c110800015110002519090980390701901552401203090300c8040c0b050a41c620005842e0401140c01c0407540d01c0703c00e48402c500a424814403441b0340c00007010700f07201200341a01d0051303041a0400040301154021190585126510f04510034445408900c2d40c3c0a02c1d0000c100c03030340c600b14600707022028040250003228403030801c80304c80c107403144802c980f0384c41c8545280c008206946082841a8000d4222a40d85041b60720442c03104030ba1900001c007507aa81039a140015040114203118800e050121541c10b15402e00342405418000c2d5206952500002c22541c00c10002c1404103040d0f510480140020343c051308000c0c006940c49043c81c948076024800c1034000c180c6072280600c1c0150144c81500c100640002c0103104031841c0446240182d0f0010540d154400704150001c81d6002c01034482c10301818030f1a40008075541141b80250114000050305031050341960426101c03d548159080f083d2201a0804035045000000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51034284 1250 51033034 51033043
    0x9060219170c010f0e07080d0e09061f0804060b01020d09120302160906051804020603040204090213090302030405040b04020c03030103170f070b0403080a05070221040f060519090e0f09 81
    0x400b0701542001020f0b8070310012500160704524540c81138a240c146d0716400199141d07102604e12000c18003043d48030f440e518205502c03a900040103820040b04461402080141c1004054903402140d000000d00c401c0c000284a280902c0000780010140401c1e80301c80905083c03e40c0c0300c1e158007159030103800710425200b800086401d0400075805e5011903162907100c0c0203091240030b01401900500c80c061524002c400c1880d01464010f44600e01c0c50b00c4a80900014080250b41070303821083d15580e01414607907620610b4100e6020b030340a55102c82c00d010400046d103060000346031040d4010b001c80203410070080101da044a521006000300104861108100c1e409101103000414a0210300d010034070850b144400d1060740300b070b92160891f070f8503603a10504840060710310700016840341841d00914125841481441c1842c203588500307207075640004400484c41c1d50451000100d0114040b050907000c0c1c84805580d400c681405140745040c4010b0303041541009240c403a44007090804141001030610 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51035534 1250 51034284 51034297
    0x12060f0603060e3f210702030c01050f0c0d0c0309050f01020c060906040209010b0a021c0c03031409030a03180c17060c0309190303021207030203150303070c060309030908060907060906021917 84
    0x1c80170b08185400c010280d1250403200703000515500740b40016007403030b180c01200b40c4030f081c91445150400303d03543c600d42e005014003002d6400f0b05070b880000d1004500c04018100e4030410a600142c0e48252540c0314605000c2d01030440704c1c15500040a000040c0d40b040403880c191022401102c2d10b40a01c000c0891402e60803201d80e11900045c0e042d130703580b0907500110500002d0701a0300c0504c081c540c440fa941e0380420088450b0900c0780c009211246c0343ca0301c2900258103600c1c2e0046080158280340d11420002000b80c0c0c0400421072840400114048050201e1075002140c1e08000e07041d490b0401140d610740c1c1c07905000308a042411038210040601a5055800649030403500c508186030411018009500035110404958a004080f080381e15001040700c2800c2e6021800380081445e20303109034094031000000700e091000451012640302000c004883c46090360a00511050f440c2c540054441030541c3c02800c21500b11007000c2c240c148000b101007006550080d0100b64520039416014054090031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51036784 1250 51035534 51035587
    0x60703090f080403051c05031e06040b04020f091002030307020d0e0d06050405060a0b04020406020a0609080405060d09030315080d0804061d0313050301050112060f0603060e3f 77
    0x1c030f804000d102000462100085400d28102c0d002e070014482030301c0380d01048410b0111803880702d4480703444004100050350001405000441c00300004000903069800c2611003030b501c15000700c0c1121407031410300260a01c04440303001071031031402c15442c001d454207083c840040900039105c10700003064603a07400095101c2c1c3c21150030411410a49001500c41c002a282c1c00d05071802c00082962030318092003183c0450752650010041c5041d1aa11303403020341103010b030955100d60305010009842c1c6500c002401c001000e82000540c4d4041441e003e411101f001d040c60b070380a000c00c0c000380022140028054034ac5003460401038040e6541d46401c00180c100d00548485803800c0544010901500001810302440c0503a04d68040503201c4083c1402c0b03900910510349061034508a40d000702d070b03550707000002c08680301c08007086141e225194141034500c40d07940c403001a070110424000b0300491100303e004403c449044401681c002105458a08a4400c984250743c0d00010381da0542040103000b00020040c41c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51038034 1250 51036784 51036787
    0x10902130b0309071d0406050610300e03130905011202040b13020406030c0801080604050d08070c02150909060907080a11070c0b0703020d020102090d15020c070f1503090203060703090f08 82
    0xa105000714001402d803012a0f0540c20700000c100c9c0c0d45840040d81e0f0340c50b5856074940c52000450021644401503048512241d00545500e08400d407030540100c5140704440002150f650545402c000481e60440e4890940b0030304d4000180100c2c2e0548141070a441d80484003c22514141c0c40000c070b141d00f000e0f42d003c06080c4001070010301903400d40c204d100c4180903a22103281980e0303207018940d01c440040710001d007540c1121200050440c020500740c1d42282591504801500050303001c13690301f4050710a04075901e80080703441526880e01e0b0b00c030b180e880042a00d004400d41011000070b02805405020f0f0005951649155840000c89409581c1c0051b000002440e40c5c95845501700c0899001400c19001806030001e62050305d40140200d80444001030324885c802040c54444816008440704c01c01316042e020420700024a1081010001424a518010b403000d03181031545081003004625080a041c14100348201590b40412841e03817110180c05c01050401151410385040940000d000b41040c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51039284 1250 51038034 51038069
    0xd0302011d070501030b03150103230d05130503030c060109180b100302010305180727021b010e0d050304080702040204051309050d0e09040201030903020f070b070506010902130b030907 81
    0x4001085811120282c17000c01101d51500189600e4080c14650381ba0415000c90040001070382d810340e0f008020745a00d0202e0350900c0c58510503410b202840851000180b004150241c0340c0260318101e10040100314001d600d042d1005002075150001446001d007000c1e1f07600c4240440c00d074440e00300d1506a6000e91200310b246840c3c010642c0c003804030b01060740020b01d0f01c00014600100076034207100c102c0b07000c1e004000e054030307001060401000c06044038841348280340c0f17034800c000024005800030442ca48482c4c035031207a0150056085480003c0c4440741940041804030700c254000003142d40040d00002d4903540d801d11b60012070040d21640d8441c0c0d0b08042072a0340e0103580800b6900c1590100d11070026640a49858002101e605203150825130340124940b021400560280d40480c1a0754800c0c0140c4a0080801801c58140803055011b45440c030000030b2171004200043c0907450240400f503200314201042a00d4000600d0240d000e218140140000031030500c1e24104148030044c94003046848080c1f1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51040534 1250 51039284 51039341
    0x207080d031e0513060e0a150519061503090606080607170f07080117150112170c0303040206072d05101109011b08120106020d020304080c0d030201 65
    0x1442e508074000102902d810200075654010a40a07050704100b000c5000b20544070840140202400c0a104d4810000860700003411400c4030f00b03010320b8580b03000031a40350100d45100e0b0038032007030f90038204035141100a2140c2050700300380e04484078552600040012551401c00d00400c6140c00404140c410b01c000c2040c3c169020100d415030b00e5075903514020640340d5100345c54014106030380707034030100384c030413005011401215031600c400c00c1e42c1c2001c440d00e0256081c40310314000402e80203150003410106550f400c0c00510403114810002c0c81c20a01d20301014601983d480740800b41c8000e1240070300069002c180084203d9080c03030312602126032100900c08814044440030341541c11a124021400c3e1440200300e40c3c8182281c0c0b8a040d60620f1038083c41c0b00045500d1030510100030b078140c19400350407004c6100d103001740000c00c04500c040e014a506000000e4640300d04410301074119030007008203100b00c140200329000b0880342590401c404041c00d2509a01400c40c1c2c01402c080f1070801416441d100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51041784 1250 51040534 51040541
    0x908041701020702060f0d0f060906051801051e010203070512040f150807050d02040b160302010e1902040203070e0405090709150509040b0907030f060b013c0207080d03 74
    0x803041645a001a038448850280c20b0303008151010358403000500803440801d401d6002007800140e250000104048055140c42c101c40302a00301807074655407043d040c010b904005040310f0840c8440101026103614100015107080c400c041c07400092440d080c07814486074020010365031256440b2040e90084a43d048010314260428400c80082c01d810340400140d120f0f5040d400c1500140e5940c500d00706075100501902c01754001542142d086034200030000f0039490100140c81e6510307021f101c1d4503a490032820020700303544d42d04400f82c400d50400c842610b8486045641c10080c142e05a030701603103964030441c0c16203900c0c1542c52080d40040c103103000c11031410008107045082c1c1e08030700001c1202041c05680b00305138500d60f016042e004907040000c50701054000080035484070300303407048800c4103440741c3d0b484c5202202a4000c503a207980702c1000010ba0340c1c0000300028030865034407030b202100c14030b0f501c0c08030300d0b03821500102540340c1c8005025203031510178000d20340540041e1040303030500c00c2e08000c018000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51043034 1250 51041784 51041789
    0x31602030c01030c020d0e0310020d0b041506050403060903030605120303070206010e0c0703030f020903032a03160204090204090b090304090b0a3030030c0504060f020c04090804 78
    0x190041e40014051503000b88510307841951998010030604008050aa918107035031065140d05108408203080d410019000404410070010004a014030b10a030600c01a10b2801c041010362211902c1e003408807583c04801c3d64100c0f82c12440115100e01d060a05400030001504080d40040b4112851100d0900000085001d09a55801c8882603aa241c041e8100600c080e14220480c140411880300800d01c2134001401d50200f2450051401d106a0700080c40d50384a01501e0011a101300b0101804000e0349038070811043c0c081010b54600000b410103200c0c000d6410800074491070f500d03101a420b40d02c40f54000200725034400460b55403802c200502c140d59801c80d01c1081d9105060024509550410800880481e40d44d800004549180c120711108540009030030083d152510102607004104201e40c80c0700461000c409080064202d181040d0490b001518032400b410f051141c500c40c15a48003040301c0c211880361407c1c81075210280c400301d0803ea00580340c0780e8001d04000c01c0354140503d410041c0b08 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51044284 1250 51043034 51043039
    0x20901060906020c040e1b030102040803030a0905070f080a02060c010213060e03070515032701050408121e0402091801092001080f010e07051b01050106090b0408060105060a020c03031602 82
    0x22000d43c4c90810055034804a05032105403c184074203590201001c418120f5100000d00140c14a80c49007091451904100da221000c291204140800c0c06020b10005024108041c1400b841030708118000755500c0f00c00318000c0c0110b4001441c0d0310745e5042035040c2e60304844548400e10300345556007001003108210081c0790380300340100c0d400042e0a00e08000075201504100c586141141c1e02c0c501d52807000401c018010140142a002428020f0820711503075100e98443c200b121748810089525950012004208170780200c40411000c2ca4041d507888001d5000394100c54441003543c0300319080f100a0400b9108180640c00c051006c810010030b07000e42e524001c01c2c0045001170001e00001110302c014103132154100742e484900144000d202c00042c2d60340c05815802e0180c60040600640c4003808050300741400301c0e955900c010b00c080c2d640080303014001d001b11005982410300b48034855440741e0041c450315108234000600728403890300074000c8040d280f10040c141c2e40c60340c41c0a17150414ac3c0e001c0d00c204a2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51045534 1250 51044284 51044293
    0x204171005090307033908071a2e050604090207060c020c15070204110a030c0e1e010c05010902040608030d050a0903050405011b050609010605130902030d14040302090106090602 78
    0x4110502c00401c0c2c85000f80c01d40ea940c2c14520000351444030303020000110350440d40c014012003035040b02400703009074a1340c0f1030000c2d942e0380d01150a03c0d200811001460541c0601d911060003a0000110768003200642c001c0c41040c0104d10140c0c1c80500590541c0c059034100318040b0300050484056030180c003a59014010612146610802c02c0f40c4400c2500c20781c03a8880402c0700720030038411120014240e4544007030070000704070000d0f846001054101c00c0c2c1100010743c54140200080e588035120110164095a8901c200710654001303985d01c884040e4407a04000034840c1000030300c082500007901c241d802800400c40192a281c40c152282e104d405100a858100008a01c501c0c0170b9200300c481d4a074250b03603050b00f05810030004403440d00c141c08180381c80340800c4e83e8100100c1c0003440301c01c0c0607000c010000a61540340c20240000b40442e003c43c0c480c210714004007040561400b080d0380407050881e24125600e20b00312413440406004d690000794010102a0020030b400c0d030400320240580340d084e000c48 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51046784 1250 51045534 51045541
    0x90905070e010e0f100c05030c070b0306031b0916180305030924030406020702060d14150109030507150c0f0602070b0f04020f150d020705010b010e03070e07080402040204171005 78
    0xc2d04c1c055848890b904292954219621644103008102c40d90740f0603016640f400150410403131424038150031000011000005002141ca01000405185850340c0d06100e1103c04240005181c0c0c50010f1403d041d01c1034050741c52a049218051940490615000f0718413a50f0b202c2c01c04175502d8000040c000c0c054115094605824190704901c4040c654606403683d16581e111b5442c403000e0341100800700d030051002c2c000260400b00300d010781e84070313060103010700e00c001d1808006402c8c1402450b0001d42c1446034050701400414400f051034401e48ac60310407200c1c400301c482c0c403085444000c3e000d005000d401e0740d03401003801c21440b60000c2600a0182101040a0321800e03140b81c0e15900030b4400039401880001c030700030541071080c1040340300f00b000e17640e060820491901800680c0d00200d403c41302659508890b0360550381081c81844d18120580040c142a8181808101b61810190656080c840c2c1f030340028045645e280c0449010b461106c0c0c5c02d504a00c254005107070348800c042a03c1c1025410300000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51048034 1250 51046784 51046789
    0xa061d0f070803090607020f1309020a150e36041b0b0d050705040b04080304080d0c080301030b15100f11030a0f1d091801050601020601030b01030b07090905070e010e 73
    0x70079058500040c081c51410b0705180801c0a0b42d402010101e0b00008420b442031440e0350b401003140d00c541d010110103d20740c0c84520400504150540106900402c0c0042494040f07602c000407908503036054a0308244c09002c512111007805814843c1c4141d010300c4980000014500c50781039020b1803054081010070819a0310040c0d40369214014040c40034800d1080e080782510540249800400c2c6061882c0340944800108001e03610507040710b04242e00015082201582c1003010702c0070642503207841050001c0c40d5035000810312040c032000e410213008001150502580d41d040c1c0c0402c45000780162035405910340c0181046444082071008a04000b05038003050708044100c0b07140410329038070201006071054013500d40d40720030b07800703e0034100d05942c8180c4541c89151300d6501600168480e500b000c101d8460150030740350020039403411074004000420000f1504024281500d070b02c501c0d404c02640d64104101d83d10080740c6d000320042401c01080c4125103800c81c450400c0b2010030f81c1d0f400b080c25000d106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51049284 1250 51048034 51048043
    0xd05010e0118020d060810061403060c03010308390c03060702100c032c0d09031101080702010b0316050a2310050408010e062205100e0a061d0f 63
    0x186084901c0c42c0c401e150904aa03560007819803070a8004002101501d83e141c0b01e04e44006026210f10f440e41e2441c06215008061010015044007180202524070303094018002c50302040c0310041440401140e655510050000003000e6812004a2050075094420507105081d04500d541c07010f0340a0150000301c1420081001842101180c00902d4200919203040c4024149042001c003090b03660b010160795001e4885601800c00ca0b400f04140703008034060300450920354200032364000d1256034a000c000007900384e003101e8541c44090811243c0750b80d50392000d03400340c1a045011130707243c0604040405074001e420742c1d26094174030130755220880d281c603010040c0082c445541000705100703a1462404151509207000c0010544514020b800c050303403014201d0a40e0820140030b12160040002c10040c0001901895070180c2c4559200300c140c00d4a8030344588039400e00c080b10001907286c8541e0b198281040096203800349e4810710822000f41c0521009200d8608240314501c580516105510341c52000074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51050534 1250 51049284 51049289
    0x907020307030e0f04110304080307030c08040507050118050d050706030e150604050601020c0a0e060108070306050907120e1603120206070f0813120309050d080c07020d0203030c120d05010e01 84
    0x2c41e08a0301143c00350800242d03035403040f05180d20545812000c40c00a050070040d43c0900c0c404c0c51003680304c1c1066034001e0b095443c1002c4580400c03001c0300c02c00c00854000038466003158002c0c20445a64200d04080d0f0307902c0d0020750002500240c100808034100300002410104440f0555402c000c200340c03910905071200014080c01691103007403070118180d803034160702c0365805c800305004481c0003000040c00b18081c01c019510000045010303000300909542c00c00b50503a07000550b8076081011508100001700e080101900b20404c20101c000c926509000c158403801700d008404046640c0c4440b9610388004c20001130200311503056200c44151a580c0c0000713003040c050300032038880c0508001c0c0359204840030b0100070880d00800344513004481c00705420700c41450419070b0310340d000f103280c0d2001d0514a261285007a0382d0340070000c1d2081003010a903050815917180c0c1740e04950001c0a8102030000a2442c0602e082e41101406150614400001010020310f00200c03285018001aa039035001020302c102c00340b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51051784 1250 51050534 51050537
    0x30702010306050103060614090d02030105070c03081b0403080c070b220504090503031603231f14060705030c030f040e0a0b010801060806010c0c080d1116050f01021002031302090702030703 83
    0x80c10030350321524452300a000c0c01080580640c4280344c040d00000e0030344201355151004242c0141c51401030651050b14985d1083c1d54200b9110302c2c0c608459645400e1007184405800309030f011505000b8a001071200704010005501c1454440042940780f401c01d01d8101915280d070720791000c0001e00ca080c01d002e1841e00b9a04440078505654440101420744018001c61400f0150b03a83c0030303402c01c01d000d04003130004182c140138a86258a4507200143c0c604900601c0015440800801081940c0c441c074004d150b0030a0958402c1c0d200d0304285001c82c41c501521682c4406404041601d80307207c00d80101500440f00300030080160b6403141500d11007264120b0301d02c0750000d56282e005006050203092420340106061600802d804560b40f00c4002035038064101081c10f0b04a0b4456405041c2d01001242d080000840a40b402e940c0602000d500c1c030307105201702402601d03030b54030301800b03a8024881455400001c00d0150b50f41d01d800d17050a0400841603a00324172640002010480c6288004103550415615 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51053034 1250 51051784 51051797
    0x501110a03080603030403150f050603010b0d03031116060b09131a0402010905030303070305041202010b01021e030c03030f0417090f010c0809030a0308090114040305070f06110a020307020103060501030606 90
    0xc646040b5000c0400400302505840f081100000045250f02c0050012200d032070001554940d80c0300e0b04090311405044c0382e219a040c1a440c50190341c030700e03018480701c0754142000201c4111080f0210624020b449801d0750f02c82110054005221700e6410038846504121049045651061030b1103030207800a46000c1d045c0f515407240104240b174110032040d085401418682d203210340c0d820000c0d00c3c6510841c3d4400000c1c1e1504248400c0150450030b66442102c10b00003440f0b500080c8000035035030815031586406555042000e50340d4040280200c500052204040e25a6403402810861a20500fa01c04807540200d07000e0494007844000140c51203424000c003166000d1000900441d0030300170546050329091002c011154159904000d110082031294540e86002e182101110742103440181001203903599100400c40004e0b0300108456040b03a100400265040b00c505140e0002c1c070785044059103c60001454404140d000801f030400d191003641c003481060f0f15040110286d50307040c03294001003084c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51054284 1250 51053034 51053053
    0x5151905040812030a09061a040b0103270f0203060f04120206040c09050709050a060c0c0f0b07080c0307060911090a0b0a17010f1517010506010e010804050114090610050111 76
    0x740b43d80116040a0850b9012940d40001c1e11140d00321014a110701501104120480009040a000d6610124801d007010000c003103580310407040c00c1144c5101d000c41c5070030340d448080800041100f082e00b00340d0041d0854a2610b04101c3c0c810080340b003903800391016005040c1d41d642162001400d54071803a4001400c5000310318007000e0342d001e400e01601090030b105804101154613100c01e03000400070181e9560701010b0b41103509255130301c4c0d023640c1c10910554650803020304c40c1001300c0f030407104d003580c0c0140303080d40e5000010412801d40c09000380003442d43e030030490410140a8940c281d448901b2044a1054550f01c41810300c00440c0e0700d031450240c209000c420304010030304250040c0300c0c030016190008559001c000c5240801c80724410b01c11100415110010701018900c0c0000b1054540c184008000394141000041c3c202c02001010504004030880001c08000081d0058098101400e0068600303050255041e03894400c2140d064a11075860000010b0f1036104038944460b00040705c0c0540403490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51055534 1250 51054284 51054313
    0x72d110105071a0105011412040807021903030207060806030c0904020f060f0d02070c080d090e181518070e130309050a0303030204030204060e0c030f10051519050408 73
    0x4200a141403141c280710280100d0704044044480500e400b00b8060f096050400161020750989070150b00307a4014040c0701c21078800e48640170381154000701c069444600d0b900c0002c000d40ac82d805158030802c00c450000040540002d80c0106880d10b944401c001540c0f018180340e914400104d40d00d6120f840800894050705241410046154001d86110300d041c54007503503062254084c2c001660042c0d4001880c2084c003c156034140301400d000c201034280c400030b00078014180b40b0709000d90800c0344240c501141d00780100320b21041c0e881580d43c00ba0f07600d4103d6112120b090040c02c481c008031008408080328007840c000f040c0e410540707044043c03240381d94031980029683c02071843c104031f0610900c40000301c5c01d913894040040065100c0d0764007581c1c1b94114030500040e5007896002800350442c1100303001010706000d003926407045012079140c1c10341e6558005040e86c8410303a8030140d00071030b500340c00c1c40c3c0006210300200300001d141d020a4155800994044407248503034880c0e80e4441e00085e01410049 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51056784 1250 51055534 51055553
    0x1214060609010e011b0b010302030706030203091b0310091505061f0e030f060f07030e010b060f0c0115060306090e030304080708130e01090c020f0c0109090e150c072d 73
    0x2440c0c10300d000740503c40c580c5855417107001d03c003400303880e0200003800400c1186810054070018160350315055055050002106650300c588500c1e4070301c488164003a86446031820402c0d40c0b80c1c118030110030301c901a01402c1142120940805400704103041200040c11414841100c2c00c440c07100701d00d001c04030320101e04111a511148040503a05000b080144002c880040001a00844604062420b03d050111014048a0312078412407401d9040c580e00706550f035103c2003501c0c0f4400029101d641d070780c000e04181d036004045c0e900083e08400c68038900840c0340b944c1648400162a24824100041003903411200d0b0749000445000708004002c002d18000580c2c440301070400080c0c0380144a2409444070741d07072404038500b604070348402c541c1c4040841041d03a04106a044403402803000d8851501c000b80000c1800903d030240791504c03500c4101005411408225242221800528008240c141850380890726400700300c080e10039158212001500b600714102034401207203002c0c3c5043e00280259544c1002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51058034 1250 51056784 51056807
    0x101b2f1c0f060e030903060901051e06011e02010209010f0201020301080c060f07200a0e0403081b1608040311010906050306040f090503070605040b1003020604090f0b060a121406060901 81
    0xd1000066040e00082c406029038100c08541102660710380a0309070a2520386500141048070076130402c02440b55400109040c040000712030744140416648400050b15400100c840030000390402021b0301110503810340c041e0032000c109076500110402d40030703002c0342070740420301801585d074004a41d400c28900c0e2141c0100555180c03007610504103c699241c52180140ca000c480c050f209101c1d503510390f00e10b03100d040c0030058500482034001c1c600f01514003c0c0300c010014420304202c0707440100d03891000c80c070800b41c0f40d00140c9103078010103655180c90250596009032104444034442c10059145030b6000d03078950000e230b0b0780c41e50b240d41c01e50f07603090f00704005481c0070010403c084e1341da01c1c140c0d0049074040c0020100710b4082e900209090800c1e10382080d9080300100a00c030301c0000d40c202400141e9800044030120749040c0400316250300034418110080c00e60070324080e80040001940881c058222070480c001228207803007013088441800c00401d00c01c60490b81d066105000300f02d046460741c0550b401c0c801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51059284 1250 51058034 51058043
    0x3020c0418140106050f0603070c0308042d05010e06011203050a090504050c070203060f010b07110a050a0303020a050607050703050a030216150204050a09090c05101b2f1c 75
    0x1c515400c1e241d0310782d040044a003412507651a01424411810034100c500001501929018610701c0c10340c50051181ca82908000c0410046001207014012400e0307082002020440030100204900a000700898208540071140c2e54240000b611460001052341e50403104513070b0106004150558045540390f12040d03041c814400d180001040c10b4881d40304052085540005480d07803241c181c0101403820100a040284080c40c06005018005000c0191030712581c1c0112120703090035000000420703210480e04142d800c410030140c00424554000380d1480300c140035005850580c1c9a28038202d41d544920b080c050086241044488100e034881d5000308803101030386000d1040780c440b41c1d580341850388004503401c50075a004030b414041450019914401464580c40410440c40c01d540c5030081e0071568822548100e011040d0b4280c29801110180e1f50350300080350f0b1100150403450440c01c8541010701000700d0000c172941e07a420340c045180002c0c202c0440107110040d14036034460a5491006c08002c1207a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51060534 1250 51059284 51059321
    0x1050c01140a0e0c0901030507091d0625090311011409090106020106140a0e1b04030510290d1506030204020f040501081f030305030402060f12040201180303020c04 72
    0xc84141003080c1082c000c00c0c00500c00720303103402203501140c54158006401c0e03228041d040010000510700280c41e4049800048000c20311140703840d00c103007090041120f000c0c0b1501560f001c0242c4d0901c2c03190340c1000c0c0718120001d181f8681d20008211211f00d81400000c1c00707140c69201042c16036001c1c3c185c0e104240300300c20065140402d203102280c47c0040aa00074030260f0346560080c0020300c0480e1010150060689141700800e2400c440c02c001e58001070205034541005401118100c1103e8045501a5800c0380440751180c184100d0364008041c40305000060704120134001c580c41d66800c1c00300070307009002440d00c01400c81079254a0b0030b0180c510403c0786281e42e034080000058440740007070300c107000c800080d40c0d80303591404001502400c80240741030018108102d40500e030403510140101a2501854542e442c1d554520100e4a20b00c52030500340a41c24001c903c00c10003105002645128034402e03a21040482c420401140c0302c010140001005a00b080f02d03029114181580561580000460713000f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51061784 1250 51060534 51060551
    0x8040305010c0809060a0c050304020d0609020d1109010603020a0e13180305030f01050406051c1b0e06030f03030c090d1a160206010f030b04030e04060308040b0d0f0c080601050c01 79
    0x100d0854012031401800f1400880c10804660024810b0550111003107809000c240d400c65002030141c400104002e04c140e11650b080018000d046d48861241390b80544030307690907100c0d42800001a8854580c4a1051061100121f8620710038000d641000c845034071a8218504180c0410182e0b600c4001c541c100c2c20381e00c00070505400d0702025070401c40d601980396143c2d41d09021701000307000c20050300900c1c003d43c01c000b0100150b45078500c0050105945215000381585149450900b0038100ca0281d10498201440451207010607400c1d42d000d50801c50445c0d0507a071020343e22944078007044070914903c480034000e004030f5040140c02241e0107881458500500e00d22148aa44241c4007501c0c0707074000c01400c0c510b400f21203404200d02d9014001c041d48142c0902c3c50341c0e0303864600040050008003000001c2404146a03100d03504000099036012801c1a210794527200c0c400c005401c28521110028104000c0200c0600340e44036003503142c2d489507201c800360f54900c001581d1980c80b0300d0724000d603503581e030400c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51063034 1250 51061784 51061793
    0x50612010204230d0c26070303110c0a0302010912020103060b19230301092403051f0608060117030d02040f03020a0512150603010207170307090e040c060804080403 72
    0x601c050526002c1c80b09440c4500081d6030000140281034a0081404500320404500d0740e032103a500700c0e42d00e200da210248180c01d60340c2d1206c0d418203c80710124440e4040210400d42c00144200115110318102c8420107080c80c200180c8403c1c610000c0c0c041000e005080c800645030942c0b40100740d0041c180480e40320350716a03280c0d981d41d00030b060ba11110000700c00c100e0fa41e5135101d048102c0020900501da803000e00b0000408041e44018407030600c07525034401820b04280107040855150407000d110074010380c1d5403030030419140c148203204145030492020810003030700218443c08017913590002c020915a07080c2001044004c410700141c20181c88103001164901420340000d0024080c204e17500401c103841c61041c0468a455500b1403442030b0500007039910611000110f21312a100ca0354080105900c408012070b00901c05e11101928054038002030301000080c80000718003c1340e041c0ea0b0108817641e219040c05030b03013005480041040c28450300402c80903101d0b0a101c0d0300309018040c52407406d030f41c036581e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51064284 1250 51063034 51063037
    0xf04030206180f010206010806060f0103060e070206010905010807061e030b090405210c0a0f21020304051e0607080f13060833060313050304061211040f090506120102 73
    0x40c0160204886106810a42420300043c10b40c3d0308203000a0209504000400d80c644500030002401043d00c0c00b80a01c45a04c40d40040005003031903801c12a080c100501c0007505c9181c2402402503043c20400005000c03540000c03460300b181d81a9a0b241d0058102648641c0423518201c00001055218030782d01820b6501e071800280100d1050004100c50301c400c13143c10075000710080094a51078002e000040080344042800100d0701d42c4021100c01c0c580440c6041c1045100c40500e800e0682c082908603011a0340010080041d501c0841d00e0340c0700080c0b07101650301d45030400241c04e5003082003881213000140c40000506a506005190603061501d0149004c19083c0303c0d038029400683c504d0217002245142c4102c58100700c44445031507127000d0151010003d0762010880c1c040c068440080060102042100c1040b040da5014007070b2a07a0b0340d03407800b0003400843c01c050888180f0b031a002110303032005100d00445045503255000380340e480d490f006103000200402071404d60001d54000c11040c00d52000c2c030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51065534 1250 51064284 51064297
    0xc090907170313140607060902011101020a03060e0105060c1c02120d0c0807030515120f01020c150a05151003140103080d0609090506010e0408040306060602070302041103070f050f04030206 83
    0x1c025912142001960405001e0681c0030b65000340c0d00c2140d952040e103860301180e03030316a0800408500344519100480b0341d502d1101b0844d00a51011441c441d61a9068000b00110f030101e040301b8640c1d9803107131304100703181c07140f10a00c00f0a40e0144a11141c503083d030400100f18a60580103540001074112540e4045521099003d130880d0381e222a000c02140d001180750380c0210b817500e400c01c490310308483c0c3e0896030451200c01034400c10b240d108040d02c81004102a48c40d8200c0f540c02035407112000c503d0355a40781c0b20103503840c550501400000310080c441b4800c1510640c0c0710310820074a00401421300041c8074920000108143c2c0310340e0f00032626028140e501c1e00070340c0f140c00b000c3d81e55811035550000702d44a80e008a1811810311441002003140052024107507040c503074141209849510300440755111301d600007000e030b82c100207000a000340c000c54004200c0c1d000382c40610010380000f0030503029102c100c44142c003080b02c204403180d60344c0c403c101500d007829001c0c0a0604d05034980d00050f00b50742050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51066784 1250 51065534 51065579
    0x6120303010909060501080d140f090406080f0607180608150303070c091803050904020a03020c100501060305060402190c080d1811030102040e04060905010b060403051b0307080c090907 81
    0x83c0802400c004031442441d00400b040340c0903182d00b103007810005155140c400000005078802107101e81c5941e110700101d8070300722001001045515629440300f912260100d0801c0d806025640004880781d0003202e0007591f0700d41104440c202c0c5030602c0300c26036802c0d10182200790001100c207a10708460f20208024401300d80102c020242070780c50103144400341c03408810b0503405400b801d401040002d420005440c010042218050388507080c14000300c000f4051148902141d210342c4002d0009070030700340d200906880c4070380d400384180c5c0c1e01c2c4810f0109920075584882c10014001f402d01040303c1c800c0c940c06448a200d41c0d07810f40341981c202c2c1c0319803c0e0b5114110070741c1140340082d011030422078002040e21040c2010b400070350519103401d09041c1c0398440103002400090303c030382c01101048401e500002c400c8000400594440e0303101c1c101280d540b8000709040040d03151030200351110346000100c1c00700301c50000c0001c0030041e5800040c001101000380074850b1364400c0381c0b80820500c40100201680c103921 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51068034 1250 51066784 51066791
    0xc07021c050105010f060f030506030c0303070b040309060305010509010501050d0e03030a0e16080312070203040e101809020901120f05010e030909010603020406020601030809121006050a0605120f061203030109 92
    0xc0e04040b400c444060340b08500040d011807041012603080107008035408a181000a0590359100100303060602d0380c0000c90307060100080e64020842c07d450074034000d80c025650054055121030007581280c9003806491307070018201e001004558800c030010329003015a504045160581250311710318503082610b02021084c1c40c4c0c0d01b404000c507030802030341d0426140214480c0410b403038541c10315200e02c00d13140d00a4140143e000054801030003002142d008050184060185241805910b0780148213401340f044000820441e024080500c0d0050804454008000c036900d80d1070300000c415250b40084044a60203815080100490340038401c244908803880003540e95040040704101c20040142c0100c0241881800288802a40007032603a0640303610403240c5680d5901400000c01112000c031800040e8401d045c80d0359507000d056040041141d1041e14600b8940c1d8554000307071502d008165103070040c001d2a0000600918050007402e800c02005842d003032081d03010615050640d4001d80006806a44 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51069284 1250 51068034 51068089
    0x10b0a141203070b0609180f07140f1e010905040e25030b040209070302041e1e0e040206071103060429070c02150903010204060201060920120c0702 65
    0x108108041c10500400d0051840c11019070360340190386101900c040d02902d030041c00500c001e000700307440b41d4165801d101100da9114255003c0b03aa240810302403809039140303240342c0300c6413400c2002900300c540a00500f8207800c15410312a0f00107d850041500c1c0c100f000d020b40000307540d01c6500c1940002c02c00c003409083c1c944440c0c10f0002c00303100070112240300e01c41c0c419001c0010074500d000c0542c00650448a01110752503009085000c0d00a83d004040c080d9220240703401603c1c0042d00d02011940b100e5030130021141c210308034960b81c000a01c50180520b000170300103001440e00000400d9001c1c454403615008804010100c3d10340300044400320349040b07103006400c03141d65083d459010700740e1400001440e03a24125400030400003170100024050003019040305510000170066410380c840c050021911a5921080207010382014403441143d075203482c20010300340145024820702c8030403600d4150300d415203040241f4860500104202c588003001d01c94540181e84030820240100510a09030300c0341d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51070534 1250 51069284 51069289
    0x150806040b07050702130203041104051302010207080105070203040e0a060803040f24090504050601110d050d0f0c050a0f11011103090607032714060403020a12020601050109050909010b0a14 83
    0x1800586180103008003404881c0051b511a81c0d003500c1d8004882c4007503144e460b00e20b07110820304499200ca40e0b0040c100b0040140f111184469084c80314002d07401c80340342a98400f0158202d542c1139480d0300040c0c001704070034488001014034481c1c10040d41c42e00000ea02d6501c0c00c0d03184c103540051b001f078010105c0c070305000c0000c810f803c0c1d403980c3ca00303072403a0b004002c90000d600080e018a1451088902882e100d00004589038007401e51400107460801c01d4070f420700c0e8a0030300203240d54424480c1c80202460903420212640c007034407a00038040030a403283c2e8601200044c09454000c0500c460a0030820580f10000b000e05082c0214540074505d5170320b0580720f0401e8403a041c20031100600c0c580426150580c2007401c0310600e44803041040080950b005020744a042007100036002041440b21031240c00280000c060f400a16009070174000c079000140c40040c1c0f44200d8503000203225490000303e1003a414442d920340030790683d4015840400020b94110324002251f20300200c0e5000103098040902c0781180d90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51071784 1250 51070534 51070553
    0x3030f0316030c0509010c15050403050340020d08041206060e04020d080c070504020f0315010801030b07140418090309060203090604030b0c0f0f0a0207050a050108070e0415080604 79
    0x20030741c0c10140803100186000030031500644c034100381000000045041440348507001400000c07030801081c040792409050140c02030b8420faa0522422110046407810b8440704a01d41400510a0300101940420a100318190030705201042e64441600380c0004d0024038001300400c01458031083c5481403c00900b0400c4c1200c8099104103c04045802040700617540d41c0258080280e100b60313904d071201d4540681501c1c100050700003030f81192000910100000d003940146101c4d1394406224070303405119100441d0401400c1c4001081d000d84480440c20079405003284241c13080d8409001d500709684e6040d07070040d10b0211002a103000b40c0d0b40000c20141940b140418026150307500007107140442c4e100203e0003e12592001810000c080340104a526150307404030707070440103500700c0ea0b92110404203030b0100ca94031042001015104041e400209402c002c01c9007c22180c058541c040140d40c1c020f0b00b500d54038090300d081540700b9620081c0000c2408440c81080140030054002c02c824a0203241040381c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51073034 1250 51071784 51071821
    0x305040b13081b01060b040b04090b03070303020d080702160e06120601061407080c0d091d1504050601020703020a0801140906060f010c1a16260a0b0f03030f03 70
    0x704400800d01c0e80124a040044940c02c1c0446034000f41d000c401034001078010703c1540c0001c1c1d502a000503001916503040c1c800303082500d020160030005130528604041e0760384e8051000401581201000b0640301d400f9580322503004583d030050300d860031b1180d20643c09100b8141c10030040640c804c0c0070303c4800d003048205460103d1007400200241d505200c805045000300c030314a0414601c0009110b801c00104034160340825940108580c0c00c03408c4660060210000350107210302c801c3e100b02e005071303943c03160300c14050140701d030422148101c0d001e501c02d00000c0d150081002e41544203000c8004010380340d03124800300520030354000096081003007000d0b00c450725005d00b01050a501410501100c0d640300c40034002c44030b00909164a0000c041d10704000200d010408400000306c802c01000b00c40613008150030500c1c942c550700c0060140c00c0741c040503014400c26a140600c0c4200c000096241000c59014490600700100812024074080d40007910f164840c6829100c680c0340401800400000300580401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51074284 1250 51073034 51073051
    0x70906020d03050609160302070515090f0c0913060b03060411010e0102120a18090204090c0f08040c09110d15030204050603070605070605060f03030a090608010605120a0504050c0d030305040b 84
    0x909021001900300c1780094074848110900304510105180690f044944150f4400c00741c504d601c4020b1600d003c0e103182100c103c02c103070180c0740700149054004900b002d00b580000300840002d440300320032911702b6150141c1c1110101d40d510f1210240d0303031302040301d144980d1052541c0e000045908000608485031011090305650007440806214008481074076148509841e12104562100000c80f12005040c0d1104075402c2c400100410801d40c240c000340c580d80c0e89919001c40c074010b400030448150101710360280005149032000d20003111550411161035140d00c02036402c1c00100424041202e2145c88952031440c000d600c204110b00306400b40c540c4c0003100310042c003211864100d010b4042d120701c0f00000d040329500d80c00100c0583c0e481e000c0c00000071029040f640c80e96803022000d401c003045400b03840c011602c24400003031070318858001c68401102100c0c40d00000c0d128039000317401500f0050812210b41c003591173380d002a81c4030f80b40c006000d10300a44d0041071600741402c0c41c26044401400009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51075534 1250 51074284 51074291
    0x40b040c02070509060a1203080709060e0916300b010302030613020903070f09020d0609020901090603021617070303050105040c0507020d0317070906080603010e070b21070906020d03 80
    0xa0103250042200d00455400b65045036066440c030002800950300e94106040e8002c5a0030038000f070590020a852080300d094a81880c16515180c094611092a1503030940c024220000201d0401009881002c20843e90030402c2149404d100720b41a6088440581c10078094921483d6607a0f0105000c4c0014060007820110701e5410200c001c58804038030001708410040d0009113560990f00c00700454002072003021501c400742900d40d4840c038080d500058090309010b0601c032000c5400580c0d4802c80e0650201611040b80c017030b19000050740690444c03406010f1982100350503002082030b443c21059421043c08501343d49075081d01c0c02408584043e00001d004514000c03e0380640b903007003011280c0342601183c0b02d0103c0c0440345002c0320030b240509151445038903040288000550051440c20980e20b44c1d8462506564807101418200d1f949000d0308075465101c0c2401f0000080190000d04031030368842c0c500001010022034a03100100e0944450000459034001004410380c18004600070310203915060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51076784 1250 51075534 51075551
    0x90c0c05011503080702010809030904050403030207050f0615120c04060f031b0f09050a24051008060604030b0709080f0318010804110103020d090606080105010609080706021c030b030f010506040b04 87
    0x142c0351030040076170080c1405504000b00f400003100b04107036020342400403c240b00d6460a03240040180d04121821600b07441406400d0051101c00304d5882d03c41e20404498511503960001049004001e500c0d00801500801c2c12601d00c80e145d5004120291983c03440182142d461403421495054240e0701840e030942d40240148841c82d1202d8410341160400c40000c102600c0304103403600200294074a001c1d4400c80825590394286a01344031b00211207003290065601c80d05901c09417030749141152460361000080000b48000390702d444940780c02c80fa2500d130106110b903e4001c40d5282003202c1c103142201e5440824072940010840d00347e070701440c0b0280f8009102d400c256880c1c00d075018045504a040c9500401c000305100c1250b030000e4044c641041050040c2651445094020002030150b07134001b0300c0300000807401020006d003103012100030307500030020030164001c201ca1225043da03a110406480e401c11540342c3c0d4082180c400101d20900000900b41040c80800040b5840d5200d035074012428001d98 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51078034 1250 51076784 51076793
    0x80303070507080c0a1104060501050f070f050a120306030c120206091212130302030c0105090a030f150519050601020c0f04090813030b1f031707030306090c0c05011503 74
    0x1500c0e0880e40c00d0401948a00891a0808490041008100541c0701c1c1c94010400d214149625032000c417019030702082170a49030401180d642c4541c5031080c244000801810340042ca81e0b80d5203800c00c03030058081d24140c0005d540d500415158a50348400001d46841051040c01030583c1c55000410840039004601b040381e81c0071880c01c0c010480850710405a09a00c0c0c04006000d00c007848c0000219009656610f10060250722216032502090740a8804c004281c01154003503030441e95014002088244001c2c03030b40d40e4808052049200844240400c940034035140c010a000e168001c0c064201d0782c0c00212000e4005008440c801080903045500141c46901207481e08074210300c1c1c4020998010401c5015420180c40354801d02c0044211200101400005c1c06110341a8600484080c641d50f00414a02d00e01e420038507000d030002511070651811010507024000300241740e260720030b0a02081d41643c0d6240d41d0100c58018420b50003040708503d48400b000b0003072060341612603100c0d2209040f40d080d41c64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51079140 1106 51078034 51078037
    0x20c12010f060b090109120303021908061212040b13050a060e01021005041101031e06080c0a0905040803070c020112051905010b03060d0201080601090e090a030212040803 75
    0x2004658205030f081203a0707050300144d485084084c00c04942d81c0c4c607448056021011306500700b1000f44a0540f11400c03d6807507007503444220003843c4c00420700031407030149120752400341c018450f44203820b94080c09503015960501400794071203160010f9411000916000240d0240e0184400140142c1c4000032000c4c0303a00070390a03034000d900001880c40980d1130666004041d0304080d042c0c000380d54441d921600704203480400e0301d08070180201c483d1b021109039801c20001c1d85c001c0f82c100074903814070203a450010f04d0740e00703000c0243c1c4c076142d02d5000880c0005032515003003060140e104001d5a1003030011241c101c14240041005082400e030080e08005900e007050186800d0100003e4a007020ba0b0549104e19006041c4072001704c2c15034011180c1d15001090035060110390400451002101480c0c1442401100e000705164000c40c1400f074030f81000300d5586800c0d0003040200b0f03ca103100c00b20 = true := by decide +kernel

theorem cover : BRFrame.Cov 50899284 51079140 := by
  have h0 := BRFrame.cov_init 50899284
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50899284 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50899284 ≤ n) (h2 : n < 51079140) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
