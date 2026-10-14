-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:02:34.246208+00:00
-- url     : https://prove2.me/submissions/26e8c26c-15d0-47e6-8728-9aada67e5090

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53237413 ≤ n < 53417269 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53238663 1250 53237413 53237419
    0x1a0112020a050f0313120903080306060903030c1515010905030a0602090a031406041106120115030e0114090607020601030c0905060d1407050a1715130f0c0303120e030d0902 76
    0x3c48215040c1400000940c8507000e039030714502a02000d0b180c8440c0035605c60580c40300b04192844107200188030a4101c0390006403c8440d2038441c1ca1300700c0004d182d8840e01403020014000d001012929500c100c120600540c80071210074040c0d600c160044174254003510038590f00d54800741c0880045001c6030300601103080040d045242c200c1d183e8541640500310100509903607848030080009108000340802103028013240c580e45440e90344119000180018080c0b10110188900c1d40c40e1640d019a202468000180c4003d00001c090900b0321801d01008951081e0680101000035842e14030105070345040ea0340c04224600101d0800b22032100510340245016000040007903d0301c041195511100321020800c001000c0c20381c148030501c4102e07103c951240d01112003904001e501d810000c00c9201e03007c214003560315260360fa40e900c4c3c1906840034a10181c0424000701100c818482c1c02041801600d0082d101c9200d0407160407114400c851101c1700ca903e164200703008201042034103400003d8518001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53239913 1250 53238663 53238667
    0x10b211c05040f0501030b1f02210403020f1c060e07170105310b1e0403050301060305070c0f1202011104060c060f0504050c06030c070b0103151a0112020a05 69
    0x840401040c1400d000e403880c042100842e0810058542c20410f5000e4202031070140401821040030880c8990710b546800b21140c070300618182400e1003000345036511102034131382054407480442400143d034081d0005034011003c2c840d500009050140540701c4200311014501000240c07615100005c0500340c021041724090801c0000d044600305181081100040d000000c0906101340c8034281b10028401407501c60303210031411003560804a440d1040b194005200751001da40b0904481d00a4540d2107010400b0b00718030301031000740343d8051701850682e501618100a10f44650070f0541e88041030b010000c00e4041c100007405d0004036140c123481c8500443d80008581c6012042c0e600c0f10907000354000f00006080101d2110a11215002e18115140c14910421403030401f46c58041c0c03502e81c040364281c058103000021410300da0b02c05084680058001403000c41c02d50f102c0c03500040303024800340708406580c10b002002c0a454081c3d0b0741880c0c00304050f110a04011510110310019411407500c0000744041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53241163 1250 53239913 53239933
    0x6030c0d120e0d030305010509060907122a03050103020306010e0103081b010212090d020d0504030512161401090c090506010903031404030c0e010518010602060105040216060c20010b21 81
    0x700d800410b0303e184603440100d80396040c1020300210550080c0100c0c406c42208042c40f910a811907050400c1c0100c0c00004240510102c207450b400c5603244155a070040c1403003412001c400c0e4564022410b03030344201d041c0d80b00d5991f21240030318403140038000945000c00402c002282d188000114170000021a0005402c0136101c03400d00e85072440803030301390111f07420241401c0c800301d90500041d80703002c0c0c40b03007005030a0034207540b1003540e07070900703d80703000101d40002800501c0020750b0480101010b5101da288440e030f181429405010380200f080440b0340c1c440d081008148211700c0e0140b14071030601a03480400442c40d58804440325098685d00700e1900c1070420000c00403e082c51255000381442c0750307005041e540f42009008200d40445645400b00c100c00c0010b10100782e000c21310b24111a4126005625550030641c00d5903912003070000200800d152022500c509904144400c90074407101540c2c0303c13004008a0158261000144455400b00c2140780d40907540240c555502103800e500c10484501d00300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53242413 1250 53241163 53241169
    0x20309101713060608030c061303020c0603040302030d0501091812050c1207021503062428090608090a02040908040806181b09010b0a020c040f0c0806030c0d120e 71
    0x68414028106071000240c043c80308a014680c0204422401580352001456509807282e10190026043c103079120424018903208111a060700d2100070304050f82c1c1d04080ca0040d5481d070098001c102c0d80d60521000040c615010b100b8012200a00059071358a6865684c0c0d4010340202c40c2410418024140055241c043e0200406d02e554a110902240c4d12015801000a92407034240c11806920081080149903120f01207030071420b807203903403003180c0d01700100407544000d0049210403681c10311031880038141d107441000c0000305072010fa21000c0d4500d0700c0382021148104100c0c1e00ca003071944194071000c0142455804510720314080c203092810640c6400301c072810520309503803803200449140349940300d10300240200681c1100041d05140d91010030350205100c03c105200b07800042602241d40c980c0705000b400b140c0e0781a04020802c004020200d450000205040760082c00042d1000300090040d003400951030031148401040768035110359903624501d004036401000303c1004042d904070040c0e61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53243663 1250 53242413 53242457
    0x309160906031a041212020702042306040903050901180e010305070f0e0405060402011115010308030a1401080c060a05040e0709051f080720030403060905010c020304030302030910 79
    0x218100402040c050b2a500704014480c0d0460010760b0092900b900380000205540c2d1040c4000803c3c0c10109070200246170716000038041c0d20304c0a500181045070000e00e04814495080c1114140328080304c01d5107a80c000d100c03c4940d8601c0003000314808100303c94280d8000e04141044051a40b4071004260b100c1880c00442102a8400c451940c40000184070b641901d00030503000d030403000708940305450685c031803c1d900c81c4013030710280c14043d92112a0ba910501801030712407006501807600300c1541c0d2490800c0440c0d00464100c449240750100c01000c0038606c458a604a85e00c0200600124000d00104012070348010000c0041c00820080003610700f40603490248114041d03103c4080062400c001d1144404000200c402106009045460510381000b20690001c48500e0020449100240e00c121260032045c1ea0811601c07001c24000f08100c80b981050080b180700d50000c0c8462500d5541c2070740c2c2c80c015800000e006d60818000303854542013042040147c2c644524050000340c03080c03083d54105d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53244913 1250 53243663 53243669
    0xd050709020c06070f080c0a0302250302010506040b01080f0606041d090d0503010302061605030d18020a080f0d050319020a050a0201050c090a0e06060904020f04060305010602160902030916 83
    0x140e80c02182008101405003c0f00d9802440750812080200c40840d0040c1000b00084c5030100c80c680c0410030421380d920950544807500307d9508009011035240364090121510f14004600647c24035001071241d04142c02405054241a1540d03452030302c4017404544440801007030103030000c90a0000041f580214644080d0302100d005030a003403410300e9080c00341001c01c1140c419062240404c010001030f01e81c64200c072065500043c0300114102545131203420341c8a0491103989460902104c1d060800c05d1241040501d8800c65030b42081e83e41d603079003030344d140c140315181ca07885a0454581003400c01e028a00031a40324003480d1044001509207050201244c1260841400145001c100240c0407038091152a4002485030880e07070410068900094880c80f090140e110a030b036000c008244241c541e5030a440d000040144159254100407203101c446802c680b00c0d80300080c1c1047c00000d0410700200c1c440700f001d4050b04007003449505001d22440650300c05000342400c2c1c400c290303284131031201180c190005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53246163 1250 53244913 53244929
    0xf050609120102160b0a0c12020702040f0c02030a12050f0f040c091b030c033303050105012c0906070c260406020c0301111608040e090102071217070e0d0507 69
    0x2054901707240d81c003814000c280c60f00491820b0300c0740507050f40180850705c0007100c07418007598809152003c0f8024010889010710400d080c4200214000c3e00031014010b100c0c61562001c10b280900d242c004240c030b00640d910707144140c03140d01055482c18016003080e84540281b41c40c83c0300c0c2d40d43d081104106d52501c44a01402c0b07841540501003d0351500030740c005002145424450550710703204200b0703100307030503481d40d082079001c032240003e00d1014078011760007150024002c000c9584e4402e502840610010321b02800d6151200e0940c05100c1e860718014003031240741004121680e201d610985403032480200640c0e90001c04051025081c20030f801401c04046090b020039290382c68110040c2c506070180d000c6920070390500980e1408510344105480c1b00d007200d0a1981c1d000385040c04c11080d0380c8180c2d0840604000000e0400c071410005400600307005110303040784d0b001040c4825040380c9045004c0f41d00511b8001c1e440200e80c0c020701ca128a07401c4404c006000f10413120702c0c2e40e5503501d0310784640e1044070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53247413 1250 53246163 53246197
    0x30204030201170417090a090509060103020103110703020309060306040207060203070e10020f030d05070306182405090a0c1b0f05060106050405010f0302130314010203060312040f050609120102 85
    0x401c40d64000079558200c0b60005000100f81802e0351040108203108401c815036000110311028070f81c0c3c85200074030040035880e41c204000e08005600540f5401c00340070690100b03040100c1c122440c4e10f080c00321249aa0998007450510540b0800c1014a07480500304030b9009409204017408111580300460085400e43c0b5400c0da11410f602c140305200303094201910964200e418008003400340401201d0190940c0f0000085540e60440150010121600702c403080d060041410858444c1903400040c503117403481840071403043e00d10710104484200b405543d400400107000320320043e00380e8020803000785080c24104036504910f5401084070307081d00f4055038035443c11410032040c050240050b40c09054640340840c07a16003441c0002c0d00350740340d041c5003c00b00341d40091500e00b82120b141440c0040c503405205004003140c0304000034040c1d0001e0700d006103c0e0250084804c1041c10980c01c03a012501990541e4090034500000c120145c1c202d81e5005e5003010380c411090004000a10040001032400a0218 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53248663 1250 53247413 53247419
    0x30a0504030e031204050906030a0f080a020f03040b070f02010201090213090213091a090a0c060c03020606040501050f010e041401080601030b010602032503050903120903010f020f040e25030204 85
    0x401c41000780b4140350190704100d49070351002e00c9a80855080e510255281000b98640c44046840d00c100c0d06c5024281d1a030300b075a0603040000340c100828002c045542201c9503c4c8125030030b20340740d124a200701c1402440c00c101c0c5000143c9ca039071000c0d00e0345005000014a010b929008141221840303480803031541e660720710f1001103152084c080d808001c100c0c542040314420b01d64584101c580b201805980450314000024000f400c1001424032040c1d1000a0450340c1e503880c207000d0080d507000d4004402600030704000890a08291050764101c840082250b228030720118015078070089445000340d00140c4506a8007140d94660000900034034a00e4020410341d071450500e8025402e068200a003107400800079442100740c003030840c0144030b40440500c180060503250a5502d8403910040c41d0701405010740502d04040c08101624202d4130a50091102890403805501240b190004400d402c3d841400188200c120400d415a071240f0122821000b008000303001400c0100524000030009070009024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53249913 1250 53248663 53248667
    0x4141f0c0206090604020609030f070305010b10030504020904150f021305010e03031315050403021809060c0a080c0d0b0303040806070906030b1c020f040606091d070504060c051002030a050403 84
    0x40500d00c240c6102030720103800c080200ca030310b401c0302030b001911941020030346041c00d58050154515102044044030003c503942e00e00f00b80600444081c84c2c0c41750046054204960340030f400352500c29035005200e0252656507a03907072130a840c0c04034868586a951503134001c007980c003503100034000f20082a1030000010300e0500014050240003450500075001400031a140380c04062484c0280d0700c003065170300a62000c4c41c40c101c40b580a1540041d40c4000c0c49a0700c00c84081c000e01d03400d805a42c0070400d507003480c0c0d24070360900018030482c00303407500154003180041c3c8468a4400035210b603014210003c201e03a2a144c0002c2e1558229420091083e00b00400f030044558114180100900d072a0034280072a6202c18001060078445011002048143d85825011950b60410604103504020803c00c2a15100c0340010301203030060150101c4008565281c84500c50301d9a0510300c5010705030307941880c207420008120340d0b420b42c020341126184201c048120136080e50340041c500c280e020400c001800e160900300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53251163 1250 53249913 53249921
    0xe0705040e01020a050a0c02130911100f05071e0b0103050714010f1d0a0308030a0c020609030c031e0403080f0a0f03061401051305090f06130506010e010804141f 71
    0xa00d41240e00c100513040780b13240c211003581c1241d0703641d007802400e5803000d001242e44524450200301e003c1d80340a9103141000000021502d0707801003030700c510000300c011000c00d8a07141e40740404403000c12401e000040c0019060480c00c1052454035010b030038504120b65032958a600c0c207070001c503441c2e04a81030034411a054054a2848000300b417a10b8191910090406002c066504542505001d001d080100081e104c00060500440e4454080795692070000d011034001e0850880c020300602407100400c081407400400c0da40c4c624140d1020b180380030301d9418101c0c416114800c0c0b620b00d5410038000000070618400141c09103c404446c0240c1d221403412005084160321303a20300c03051600e084418449100d00380716408031410282032056845814440ba80c140300000c1d841281e1050b040300800000308a003c004034040c00d020303140c10703115032511202d210942d1021180030b4005104403244003115842091002d800c00d000b070600d207949081c104401c0d4103100088043e810701000b80800903414844c20300c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53252413 1250 53251163 53251181
    0x50609060f0126100204050114090604140a030f03030609060618031e1e02010e01050c03070b0a0b030303040c080d020318060a050f03070305040b1509040303050403120e070504 77
    0x1028104a142006460000a00c180100705580680030300010300032003200360302c0003e00380d5503044640000200113101d0103076016000741400038103003500140d180452041034460200000b089207080c00d05241e007582448000c50301213a80002442400008503c9030312029080310300a5030f000c180b013410b1003411407d40e071b03065018000300501c503540c540e00e160f64010070105580d488080d0082003529084002c0481d20110006440201807040d0400d01c0b1515042c0c2c500c00078800e80b2100a110040303001540c81d8001e09000c910303150810890500050341c01121103a20007800e11001501c403900d01c01103403558008450845500075141002e1013180740c100042604080c10340300940c680003400e214000d409040311403c034003e00300440d9a03006140114103480e80d0322145800c05859141c208002400b5000656017500d014402d00040348071490074201c000c1d6046c030050041c100e50346550b07800b1030083c00001c3c404e4003041110310400c0316000043c01001c0d40100c1c030b10b00618040d8180f10030002101c0c0800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53253663 1250 53252413 53252431
    0xf04090b1e010f08040204060f09020301080d05030105010207030b070207030b0108010b09090c130b061b161508010b030a0e0111120f150114120a06031b030302070504090218010e040506 81
    0xc444081030703070307002a01d0f405242003403822400c141c03039510100d00908240d0b00521a1100c0c502008583c9034180e1b805181202c0c0100c1c12110900481072090398503100a000340ca0050308440000d1000c201101e500e00d0704000c444c812502015601e885064000c00c080e001002941d44542d6061183d25000c04401e42140d501c1024142130300030741e40011044407038242c0784104a600d4100c448043d6642400384c4168502109040d00b04084c0c290289845521000d1071000d0400101f01c0814a040500309071441101d00b03483d00d00850b42030030701c007003000c0e00000c124844040e1121451030401030203001e11503032400390f2101c542e21002125280943c021000300082600f03000b0001b009040413100c10180d81d080310a081060000c5075589020503e0b00c113548013130402000100521807403810681c041e0301160b0041450315401540c020249030340d80b00510019005900405040c48245010317400b00407580c0c0f000384541001c000c0316408402c1003000341c0c400526400d01c3c108001c140007040c40b02c84e60001d660 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53254913 1250 53253663 53253709
    0xb010905010e0f010c020d06200306060304060e030903010f020307030b011d04021b0105010f0311271905040501020301060e0d08030a020f0d09140708070501020718020f04090b 77
    0xb8515080e140039184608043e0812083c240d0044139900322064000c0c1620240141908202d005000e4070020710b010360b2802100550082180c0301a41d01580004201c00e1940c1c84903201c01d00503251036900010180400c11401410396024440c01e41c080118070f4001d80c89240010000c0e088480501c0c110707040c88000126400b2018084d0080c400d100070850f4010b0303c2e00040c221000d51a444810306403040d620380000070502e1840b8524100481f84280b90091140034203130b05012060310010340342003981449150181021001e43c1c0c515500040500c501d01203000350b0300401003903032000e03034080c0c0300c0380d40c00001408882d91005c46c0d1000010250b4913219035100d03a565801241c4801841b08420765404a80712035503040007000c442034500501d105000c501c120703080400118440c5001018a4483c40300000380760701e4041592000c6540580140c4402498000c1c000c900201c2c24106083d419800c00c1014890b055241c0940007620022200003012503440e414040024000880000c000c040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53256163 1250 53254913 53254919
    0x304061a0102030406020a0f06020f0d1401090b03030307030504020f030d0e0906040603020d060f0212010303030e0d020f070b030405070305030a09080f060f0c07050106050604090c03050604090f1704050405070e03010b0109 97
    0x4547c56501c0d8004100d21144400781030040003801a1540e12103d007400054503020341003280c0040080912440c00380246d40d86e03590078803080703134402d03007000750103401c01e10000b10607600941c4410342c01030008d00103100342c101c0000020b040c01c40020841d03001c00c8000702800000e0070003013405a0f005000362001c0100c1c6085800042c081166110000c1c101038840c0394504c001c1d140b5030140d5030401811781f2118000e503120715016001d46a802d1218180c1d21841c0c400c41811440000c1d400300c00e40c0280c01905459040446100d51540000d1040e195481100302c000001141000180951034040d0b03180c250b01810090701c2803d0641c84c3d9060b8000d0fa004009000012001d003c940f60840c4807030450350ba8481080c40c1c8a070140166502103548500d02080000d030200c00c2e904526048802940e0030082a0b807081c0c00c01c011030f050000007803c510701c009640400a000c0d0307400482000c60707a0300600e05141e41c400000d01510021500c600008101034980d03021400c09004034100740c0002d080100d080d40c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53257413 1250 53256163 53256167
    0xf091308131d090307080a050f0a03060801050604060b0307030b120708062e0b0307030f050127020c0705040504020a0807030c06091712160c030803093711060304061a0102030406 78
    0x176104025264240014940315842c0c004e00c00c42d4160039007581c8154480000d4500500140700c288644031041d400c050009441d4603017889072030300359100455030030704648491000320010418550b60703e130032508900a48440850410441005000c260018030702440e11140030100745620b900c80301c00d04d81111041b045001c60000c20074060701d000c43c0001d42ca070303561035008501030240ca007c00f244c46443c0900124240c0301c008040f80c80b0300130f24070201c03560201e0006280e0881c450800c040403640c02c60300c0c3c184100d14164000c50303007140c00240203c01880d21124898242059580100c0303442c2c039440350406c5410342241241000708149a801403625a081d40a1515440d01d004003d803074240014038044000442c580c99100c0070740107075010002540320325080c0c455910035240514244100c0303021859203500c1291303c0158050702c03075021000101038240201240b4441d0070403100c00b000c0500c0c5c00707015107800c405148543c2c040c26020800c849025680c40d14a02d0703440381c180c11500b0410081c0b214503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53258663 1250 53257413 53257417
    0x30702040f0b100807050a1412091b0a0302010801030803070c020303030703020901032703120608030a1d0603010f0306020f04151d03010b0109030b04060605040e070e01050d020f091308131d0903 85
    0x4032a4182030800c1014503506e400c0f00e2082010200700ca400b00428040ac80400003983c030244030172800e98010b4031003400200020400248030090016484c2e100510000340c0b040c0c05560442400e007482145140240e00080c2180c00032541140080c3d40410741541541e8140291640c0410f0039401c0c0b1903101e180c01c40e48041301c41c500406001d1003080c0210f20909803035a44100d00418004094a0321400200c178014015400940e110401d42100c0d48404035074980101104c1c101c41c4010152882c6500d95030340c08010790005070050b0365452003800300080d420007030060113800d610580d0b119005900700d00310341b56000c5000d60002c3e0091303140042c440040d0341c00280e58029030b60080c0040710195202d01c1c03d04040d02503504850f411508144c00381f01c4050000030104180c54000c04496100c0e0303200c10511010066440004e5030002c44a00c0c55803941c01d1013071527543c100c0040d070350704200c1040c1501c4090381580030580d5080e10300b80c10002001400c4d850407488855117410300c5040d43c00e042c050403999a078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53259913 1250 53258663 53258677
    0x705041b080c0f0a0e150c0106060e100917120409060303110c060a111e03040303170c090d020402120403050c0f0304080a030e0a15080a0509011509020309030702040f0b10080705 78
    0x1104001700300c2c00e8156152521030003680d4590340003503520f52180440b28082c007402e01c1aa80403541c9004182070500d0084c910300c040703510a84e00c00e07215600c4c0c1101d00200036440d03202d00416001c0c00c288542d124861400520182414200c08141c0c2480d500c0d0080548100b08100300c1c46400c025420145a5a20170445050161619101007040c2901c0021814003405004c1d03940c1c5103201c415240c0f0a040080017400450b0b01a864160110801c41c180c040c08030000c0b15020304a410402400005191803c00001e00c00c1c00a40014108040310007621135500e010b13281500441e00120311400e58070402c20040c181481c00d1000345060a251042d034580e10700040100505008610403249296184c00302054000c04041d68903441c03602c080440a40b1944060322a00303051400c10001501d00b02d01405600149038151045400052804400c44000c1d0000340401465020800488004d66200e00800368424942200045c0901241c41005a1070317829988400c244031030b1804120101d60400150fa600b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53261163 1250 53259913 53259917
    0x106030b060d0501080c0306060d120c2d0611040308120c0903070312030501060c082b09051506010306050105031302010314040303050612120a110705041b080c0f0a 72
    0x2249801030002489409901c44001c0c085183c0000003c428030700080100681006805699898a8001c180202d21034901c2e0040c06015502c22407846d020b02c6901c90b00803070740c0121aa0f200380d400851000b84441002042c0440007035104281c482404585d02c01e8004454400c0145854180345544080042c00f609110b5216000444001a5081404000c5a24404005054400b800d48a00d040208040e60401c41e00010b45404000b290050040f01c4100e412500506130070705244800715004503c0ca0310400c0b650310013510040c900315814140c0103481c030040c4200c0103481151418a428484d018000704090704040c20302004005030390f001000c4030703040700440798112840b800a00041c3d02030074103440103010764003d0320104010705d80d05602250282e0021191040c150208a414503502c1484607181b81c540c080400c518500c060081103592003001121080c1c51180c0e558000280071101c9002080d0040d020313640d0005c8980d035000003001c0e8482803140302142400d0825034104c145005190300d02d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53262413 1250 53261163 53261171
    0x414030a020c040f020f0301060804060b040b0f040b0111010c050703020115052b0506040309030212010911210f061b0c0d0305070e090117010e030705030d1104030609080a1101090209010603 83
    0x41300ca420b41e01100ca0b40d00700c0541c0c2e01d649580d10032004001c520b00311029038607a0301c1c0c1507901e141403405006003600c0c100300400103650031240c84108001001c65004190501c00340d80322880042c1307001e00481d80c0e07002264956940740c4c1c03d00c1c10003a00b920300c00041c1e00c9000152003824040390780d810550031416140042c00100803ca0b0701880703180034500c010064002c3c4140750030070081650045080040e81e100b55440080b60100c54800c50a0360f0303011034004d00041c401110344005040180d01c2556041442c005541003200c1c0c5442c0074100391480800a901e500084204080190304d411f10380e0750000c02d240d0303840c90000c03075030700a0f030301d40400e04800010146c64074042a1064420810f0801c42c400050001c0e80d0340d42d4400180c201001c48024281c0c107035007081320604102c5008420340390820b821401461170441c581240000502404178020201c4109000110120f0442e20561100c0c91080d818140d40e482013441c090001c2241d50102d00c1030303a04000000d40103850303404600c0d044640302d003408a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53263663 1250 53262413 53262431
    0x706050a090f080a030f020606030a140a08040905070f090602032b0e0d0f0309030816020307050f03030618090307110a050415051305100b030c070f06050414030a020c04 74
    0x1d68038012a80208160104800045403840e000f24080c2101846a01e0344901c4940080c801da0f1202e41c115120707a8550031404880022917981c00441c04002959015107401410720369640300346410a4006000b060f50f288100701846411141130021300510b81404009a890448001e40d20300c101e83d660502c180382c0c80d921000c0304c4c0380400510303241d0805c901c0503c400000b51031555941c0c0e4006081d840062441025904454083d00c13901120356050354505074107682e03100300c03080050001c4044400314401080b00101143e404e0100803040389000340030355580d0074820108005058038485040074504210280b11040343c00004a807280b943c40903040081c00c03507641c00034040d410203030700c00f6802c039092200e031a03075a00140c51018103440085542c0d104030030006c40c945080f1441100d038464040c203015814005064018040c40c0d0010b40c060005250045550b90006402007070a0300b10350140d19141804100a54000b807094940740301303070045041c001d011100035502c1e071200c00da83e805555500f07460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53264913 1250 53263663 53263667
    0x3030b0f04090f030207090c0507031b0501050c0403050606040c1d040e0d050d0f060302060406052511030f0d0f0e130e0d11070303120c050d0603050d140702030706050a 74
    0x5140c125000500800424610f030801030801c403104001240180030300480400c6102d003901c65846041c590f0f9a8550030aa01983c083d2280266001e400440480c1141200e000510034010540f007070b040f02d140e00b41c0300c6103103261051520b980504180e01c03c606064500ca251540288405804007200e446d454049200c00046402015007020410f0a40110305151031400c0e0420018003514210810400c100c03076060105500702c07011404029405a8108410000c403407081c0050010704000e500843d0a800401c151503590100c60003080b44d608450010b040d121b072400f4005078041c804100c0140803100e04429005001c03d01300340b821401d10414181403101901c8042007040018103016040064041c0c90b00601d03901c800b0030360070b900081c5000107600302d00c0a000c503503813048a6054030380e1040b000f00d100c110000b4050a421190170030005018149041515014400080d0700440140010628240000b0401c03005030101d420404420801c0c000181c60010300d43c41158510f24006454178010141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53266163 1250 53264913 53264929
    0x20708030901023f220506070f0e0a05040e100207031206061805040c0203090607060209030606030a120503060f0d0c0603150e0c1e0a0206011805040b160908010f060905060402090306010303030b 85
    0x50a440440176000e500c2045000106103008001c02d4880d15511781d80308901f02d46c190302c03110359541c005e092000b04100d6410300b6080241c07040040d070291101000305c0742000703040f40c000040680004802e0b242c0603001c1c154603c01c00b800f60040f860003c0402c10704105501c0e40300503510665009075960b05503a443d40344280151650000d008280c00e550302000d00b0150081e401100c0309510038050000811450310700080d15460740c9600240305840c05541450588290308000c100d213810100462420500e0340c0c8400c00c0000c2c440c400d01800c0005800c04030010111000d4200c004540b0700070b442c0a000108409401c00d0f800b1704011103456856400c0d0074090b0010b040c10081d101c000c000402d8032100c994001c540e050690b081d0400d90fa03400c0f0412480c031402d950040c0c4026029001090108020303440442a81603000c00500340611041d5030307503030301900b120301c0c1d105a0303405079030385801c20b00c554403103405455080701c0c0072242981820080d00c0040c0d203414040c4001030034035550b25680c1ea1143c0711005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53267413 1250 53266163 53266201
    0x40503070609150305040506070c050c101101051012080c0709060305060a0509010b060702040b03070503060106030c140702030c0904150c0804062306010c02010201020708030901023f 80
    0x106840d1000d81e500380240011820303004245081690040001e00b9a00c00d12a542c070490b00070380188030702d4544103010f48054080c1a4280d03a00d00035003030080c0054031001d00120641000c0d50f1100500000791800300e003140e0340902404c8500d00108003c2100041036480310690702c6d0008d01255542d05404000c07407030301900b548040c101a040c25000028040c0129802d031051000c968103000b01d40c1c0c2c400e08a82221300319844d5603440034041c0901005400d244e4007202c0702001c09402c5840d02512040001e00e000c60991001000a40b9548009030701c40c1e212891007101d5090741e00160404072283d001907120010004070500035403525001500b40011a00007480108200008000c01101140f005001e8542103c040d10014107103486102c00c00740240e103003800c3d007c8004001940c1d0f10f800d00115900202c07210240c2c11590280094008190090015030107103c8440006965100b184440580144625481580045500b44983c411644164a0044094a401c120303040e40e4030f041d000c81c0c4140c0498 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53268663 1250 53267413 53267419
    0x30409060b091003020a080a02180918010b0604030206040e0705130b03240f0402091207091505010801030507090b0616060510080f0309060705071a12011403210405 72
    0x903600254850700c010080030991402d5545144011030300809800380c1c814130b1490b4000a00e11400104010802d0703019000d14000150010605203d2000084506c802520305845055596600c9030650340b091181d105003941c103a4001341010f00d1a0000b41c01e5000c0c0d44100580c01d900d0340001800305210714200c91400c0c80030552120115129500303003c01750400c480e41c0510303044d02c6071011003101c20300b807090001c0400202200200c0c00c5450601000e5000044800e80000100c841c1806840080c0300321000344c03885080c00118001c18282c02c100d061116413000781440810710040c00031881c08102d4000343d918680005c40d1000074403000c50094803612410a0465000c150040100b00f600e0704510300984108607941030554035400110b44482c0300b14a4103030b06620130829070359942050f0000c1c00c201e50140083d0b031015a5039003400c02c2101d0024940154103a400940360080e40f40c40c002e1507002d403030140b02000804600d840403e503250700c11142e822741030410f00311034249101c0040854010300300203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53269913 1250 53268663 53268671
    0x90e0403090603110301080316020a050d150b0d020901030f03020a060f020a080601020319031e0c02030a020f03070b13060f110c010605030a02060322050d050a030c020105070e040c02030409 83
    0x20305008200700c0540c003510000909001300c08540700c1000c07054a0684032400c000d103240c00c2040d40300c400c03000c11300d51040703030031a0814800240030365800688404c202d004040d0780c106240054440e200315403650b04194070a000d285000c0340903032204094141982e500c401400300058450805904d02000c0080080545040c44000c60304c4c40d03415000342c5601e1600c1d803110005a15a0001680c99000702e0b107403030040824803005040c081b0b02c01c2e00118aa503200c00c565803500001d621581c815502c107040e190300540e0000130320014266040150a03810b08a05020394100a83c0b99242c001800000d02410b0305894408400c0e410f000d03260780090300c1c00e2640c040420280d4811006540c241d0060010038040c0c0d440e00100117141d0801241c003090456005007464074503a21384116061140442c0d840040c04a48030a5400014800f008111000d08454546075195141140000e040d1602070f019001164181070600a019070030159408403400c0071140480c6514100408901e98000e030384c0019161410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53271163 1250 53269913 53269921
    0x120307030e01050709060203030c0a050705010c020c1302090609090c09030a030801051302071a070512130c1401090b1c1401060906080c040303030c110607080108010f06120210090e 79
    0x564070403405055460000e01c455660320b10150b0300d0305603911038280075030000c0001448002c0c6010090003000110309001d420400c40752200390844a1541041d03000d80e0241401052914206111040069a044042d460b011051000c00c80c0c80c0181d0000360f0242d510380d00840e64013840d080603103003400d0300942101e045da1710703606000303103206d20038400c060041c195540c410983c1009402222800c0390442c03030801000c43e84807c105c0170004001c00325801c2160038460003124485900010303008881a641c10b1802103030300d041008030720041d60f00c001e9134448580e40a01c1580d800491910480f207410041c9138940e10130700307040009507000c41e401d10303035591400484600803007140b1100c0b4141c502c15503944022988490050f00d0340f03102901c1950103e54144010400284640c01c91001d450f5189001e140d400502544d0b2860200b05403210301c0402c000000500841800b445003026103503080500340800c030700e0404030400f0000c011070007a000700d0003403881241d254019401e850040682c1c02404280f40f030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53272413 1250 53271163 53271167
    0x4030909092d200d020909070501081e06010c020402130602150705070c031104021b010504120f0507140f03040b0304051501030b010b03090708010204170609060714070302120307 78
    0x22031031140300070203511044803a4502c030110052285684184400e03101da1207801c0b807091500c24190001da02c0040c100240005031100d10f0445d0041103020010148207080c070001600c0d0040040c6032210480b1305088400d41c42e02d1110082c2e0b04900b00b0b0800c65115401800850301900c070b6103c190507a1b44020744c000814550000701804001540084050107448100302140e0314492904041c00f0f10000340c109201040302400e1441543d0402400145071210500c2864113854000070125056551141004103118144070500841405881d003c44800c0304400060024003a401014286624604003190200020418083d60a16900840c0d40b155641c0c4241c0c001c036070080344c1c121828000c0480503465181c40b40505410390b613110072524400d0313081242d04556078000600d005981e10901c1d07000a0107007404e10041c40600b124600e04200d042c07000c1d81507854144050700501407684400304004400780d01c082218088141d64074980d175100164103080785001000070510b03201c40b00000071b003c1d0041e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53273663 1250 53272413 53272433
    0x109051209040b18040210050c0a1119060206010b09031203100501120209010c0204090302011b0f022e020a09080d180b071104180b040503030426040504050403090909 73
    0x1080482d428020b10450b00c042c001d04101d040301003040918804081001031500032244e202d4a40300346805400c202548011614001ca003403000e0301d15041d040444141030408128a1a013050f529440b16419868448003c0d520f040510458a04260101e2008829901401284516840c0c80680c40d20390805034144081381d0306902c943c0340418006015140e4203450381c0283e400c3e200058407940c40994440d02070102921088104500b15580ca640c2040c421040d0711060840015540c0d030b1203804410041d001c0c1c50310000f91441401c544024445c101d00d4042031420b1030b030540800b20056191400c1040968641c000c41e00100c1e014000c01510145055000305010410b43c0c2843c401d0420a54540f0000313158441c0c00c5014040190701c5d80d00300c82e0f60909802c40702021484250a40c101e041c0c684072055203903026981101c0b5a04000144010701065404014120300020071080403c20406801c031424800c2e07108081c040d030388480000b000d01d8080c0e20004002c1c031000100b2311284403145802c007814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53274913 1250 53273663 53273677
    0x6020405031608150601120e0a0308060303041202060906120f070e0f03030d09050319050c010b03010509030a0c06060e090102070204050a020418020c0109081b07050118140301090512 80
    0x6445200c2c0d428440c41e40c0d8015030b60840786150060540081e440100500d013841c0101214188000f4140079020820b9500c00c2d000e00440000180002d0b00c118a4000c01c0c2c43e101a1542c1e200394821320040c0200c121480103403042d0750703040b501c01c1d5070b80b0503450204086000d114a0208581414820480d20602002a6a104401c581c1d100b8240182100c02c0240300d10401c03140641540c010301c5030303000c0c44110398410544140910210f078207001c2984c08845204444c02004000280301203440340541c0001d008a089280007100284034901d040d0032a141e990040d03400035003c1110080b1940306000c0d16034054005000c0c14890795055140c001d0120303000c0c1d88410012409144ad000005100c07071024401e03201550084012090802540200c90707020350008141d081080d56900480350000d06103070001c0140004c0755903a4080a00c200d0080313428246a035200c1ea05204a1019a00c406406440444242c0d80c0041d5005408041200840d00604454034018a0380c45007407841811209038030302070406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53276163 1250 53274913 53274919
    0x50412110303010605030708130804090902190602060403080403120603120807080108072d030609020901060212030703020a031e05090f0f15042604050a09020a08010302100207090906020405 83
    0x2061146002690341c1e2100340b044e030000401c1072010800075031003511840d401c00d03c4a55642002d44068846441c0c55005a0050340782d01c2c0c0c2c07500b010b030460500d505010f80c0100c80c0e2103140c410740d15110021f501e46000030402410031000c0c900140825014418000891441c00003c10a482c0c80349042180b03083c007000300001090b46400001c011300c2c81a143d6034182d999190241c5225490b000c0d0b15000d00903550018050354040340242c0785c800c40d8003a005002540103041c0800c14002500522815a5041c1c00200841d0001c0c01c502075075800c4001125000807052400580d1000340120840c020f05111184c0c0790615441d07040c1c0d6000a10300d0b0040c501a44018085d01c0003140b0701201c4996614603481c854010350080114217403002005450305d54841c1c000c0b0f500c1c03009011241c0081d1690b46184000c20380b00007010505100364140f00311150080c012070042180760001204000d0421001448002d10403001d0f00e00503170845200b404940001c01804109011841551070054082d4226014440c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53277413 1250 53276163 53276177
    0x90f05190b0a02070c2603160201091e030f0204020c06041103060603011e1d0d02011506030c0e10110111030609090705180a150803030f010506130621050412 69
    0xc0b10019108403401141d000c10703c0031049181c05141001e080014151070302903003546021111450060008200e40094441c1441c904111440090147d43d2540c02c048004003d20319214200300031030501d0802d8036084030320043c04101ba880010b000e41b00d0001900e006018207402d000410220707130280104610228107a851030350f02c00d4241400c071419203020308044600314046c0c2c882400076034000100c01c140d00305008001041808801c1c80d010440302c40703500503907603072540030a404070151100d0042c0541c2e140030b020315550f001c00101403c02e1a90040d03c2160070106040c4054081d00c2800313081c0796048000d01009034607440d66816600101c500d01c0c000d00c00e1781d000030149a40426a1802c0c0d0724003e00c8501800181028208161001042805050fa0321020080c40c403500e140107400500041d00207503070f646056050351114000607070045014103c1440510303030b031134001c000c2c0509548282ca0041440031200e4140700001842c0d590b280c85580c034001c18041071100b1124038030103106007074440303036 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53278663 1250 53277413 53277421
    0x11a1c0e0a150203090c12010b0a0305070618060e0111010605040501181b17040309051804060c0801050114070302010906110901020601231c02130c110a020d0303090f05190b 76
    0x2400f680b00c1100c1451441d000555400407610304400c905c7c80c107034255800007444202280200715601d402f50000d413181e0380410004c100c001d61200b14403500c5c90a140c01c1009540c680f45000d0524010405a5070501c014400c990740301d801d00354880d500400e4010700502c06075035038440d9285105103442030701000c107090000d42040350b40d05032010071044180d6a140c0102c100151841160f41038050b000b2404c0001c98400044c0700c1c0d4a014003140e023100c400c0114403007400c0c07516200c000c40303203400040f0040c004404010411aa0032011b140d0f044160180110764416031031a0403401040300c030400419451614148241c1121208003411161b10282c00311582a41c9a1810342c110007601c0c0c04400f415154824034850905008041c54075541411202c5403888030030f94002030407148a030101c560071716070b04c10070404000e501003080c842c10800d21300500705503032454010030b200612019016041c5501c41c01d02da8204071041042c05107084e008001d4680c03d40020381d4072001c0301d01e203500948100c0703902800b02d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53279913 1250 53278663 53278703
    0x406020f0601030c090e120a030213050306060f10051614060606040e060d080702100c0b06100c06050606040f0602070f05010306140f031609050603060f011a1c0e0a 72
    0x2e05880d04501402c2131036140014117809000c040b200c4001a010352407042c01080c10407000f500700380703520f510b01503100c5841001c0d107030031481c02d5440b0754465030002013441141c1c1c0380d07241e0ba002c05010949100c000540764103015a09841001c5804c2e00c0e000401120310141b20041c44140c1c5294401d00580324603803a844100211405140030b40542c2c0e6001c05e010401c02d203404846040c009108100c0e150404031582c00085540307141c0b41062012072078540b818800c01c0203502d81c0c2d80c6d201c031003190344901440d14500028420058207900500050790f42000c00c0e0140d0b80d030030984008028004c2e009841d5511124025215045e500c01c10440c1c1086040c00704442d0b02a0042c070065400080c0007a45c0c04c07024408020094214540654150048001c0d1003038040c4540d21000c003804024101055505204062600d01040242202c2000d85405d00600071a441c441c2c12501c2d001d0b0084000382c441c50800c540c200c0040c1c4c00311a071040740f4548050041c05a90200d10000396502581440070010454604 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 53281163 1250 53279913 53279923
    0x8060a051c170c06010b0c0c130f060b0c0a020f0414090d02060108120a03090204090818010e040c270e010905060f0103090206160609050a0609020907020c0a0302060c0f01050a020406020f 82
    0x868603d54004100500464811801600c0207004900c00c403140d40080001240032500001002445c0549550304007540d4055409441c0041a640c0b0803245402d10b00c41d4040e8603030f0403140c002845890f2604041400e83d0b81c541042c5a40300c1030041248407401d02d4544903540704a03060700880940607030380000a51950204641500d49900c202161801032070100440c020200110f080364060b0f03035500c0310f001003112900a0030035990701c1c8200200102c515000509540e203117650380f83c852801d0500c840d06a982c01981c851401d41c840020484000f50440000710ba0a0141c200e1000d07a030000000040d075020a80266000304026500d40904410140046094030f108040194206070108416040b509884403806100c3d4080e40d00007403820380039030340d803030078110210019218642c58007075460951909068450f003201c51750001345000303031541e00840d0704a4041d1101278465070000c940c03c90f0306c2c281404581c4119070048000c010702c1c9085039030b500003908203025110040c03107031000d4600096030001d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 53282413 1250 53281163 53281177
    0x1803030203120403050c0d02071404270c09020706051015020601140d0f110901050a030b01030f0303020c1e0d0c051203040602130605120c04060f08060a051c17 70
    0x301551405600c03050071100164058402c604200c410000081009814001207121100c1680907000f543c1c1b81501d4240303404200d01409108900d4000800784001c21a6802d250600b40917000394843c020ba803d010130300404030b81c4900310090000606070f04104140e80304030b10031070900c41064411900e445065900d0b01040410744c000d0b0340590b0040c00021079541560402c1d40004111013a401025500c45811010064044503444d40c00c03505902240b901c0c0380386501502c0103840d0035000910b951241c862100040c0f2010708425004202c4c04145407103501101c403140800d104070782d051240c0050000c0b4a01c000542c2c595070380a00c01001c01d0b03003485060915401da17000380041424045010003011968005001103480650070400010031801c4607500000400031511100d072200e0012022174088040207010b00c203a01010003040c0705182d0000c0342801028001d10308410140e0f10b4001044d05680343d9000154407070800040060044006900e4214182c4680300a0901e000340d10302d488880d0042e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 53283663 1250 53282413 53282417
    0x60c08010503190501060b0706270507060e03010b04060b030a1406130b03101104061803031b020109080627060402010c03080a0213120201030b03120d0b03120a030c180303 75
    0x200301c2c00c50f010121856151100c1c0210b0000070169500c000c4441903a00c404c40850b10240c407488941e103d1408035540e10381450361000180c2c2000100c0d034072141c4996683c014117040c0024084070b41d6140d102544410a201c034060300820046440d80010501900304941202d9424200f01503215820003030b0300c0250051401825003424464061600c2c400b500b20010b4240d00351007140d83d0141706070f120b0300902c0b010710b001450540e030b21410500028094018075001d1000e4822080c001c000080c1c3c002416100d141d800c0340c903650800113503c01240d507020383e44d00c0ac40240c800d960900c8456480088940f400170744a440c3d1403440441c000340c040e101d200880300640403074011815071021a000340111a801070348040018900340c0402220500044990130041c02e50900d0808141103581510404400040c114014611128580c00484c040e1045c40d03101020f064032400d441110751000c0024000407074440810703a17100c80c1881801401004031103010700000716036410000f80146084034075400c1d00d401d0303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 53284913 1250 53283663 53283673
    0x2040b09030d0f05090402070206071a010617010f031101030e15092104060807020a0605090a03170412030b04020f04120209061207090207140a050a0c06020f0c0f0d0519060c08010503 80
    0x103170400000750091001681c11210420404000542c81d01c4081002d545030311000d142541000c1c4014800041d0500c001420340d90301006100211014103214101d07548401046480d02d200c8004a001d8044040c1341c0300503101d880480e00e00f00d4107240d10f851280390283c0458a08190708190992814140c0c00e40800c111010001805184d216190255001580c1e00499050490300e54a5000302e4404032010201c0fa0030501010040581c01000002c0304030100460301c080342015240c040300b1034400c100742c900341565030341d16954588443d0151824481d0b41071000d40c940c0d940340c000c0000304c020072208034401c8880701c001409514203001d0704402c0400d01c0004000322810542c89000075808440c09a4091f461420000b4924008101600140340b245020b001514424035024585000c40d0b0801410340d0040440500580000200c0046900003145c00b8514070780b1031070101e440d048141c0e0015044d40610108042610304898070300010b10f121780d50030841c00501610448440f030082c09625415001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 53286163 1250 53284913 53284927
    0x405010c080c0718050603071703090d020310020703020609060109020703080114010504120302010b030d0201051608060409050601060807090515040902280f020c09010b0301051302090402040b09030d0f05 89
    0x350024040c00301000b0308803000142c80703443d80100502840814030007161a0410030010b400d05118010080084103601d17000040388818480e2039004825440d170041c680c190f215002c0d50350400a9448500c1c2c000011076680700035080007910f40000312082c03415441a50000114081c040c03080750000c03a015a51035032182d082c84904c256290000120504005c010b200106036444251290113009120b5000000c1d03c5884409040c01c055401c40e0303240a592400c0c00304080c4c002e102d54001c0b2010b220740b420113600e540381c0740010001e20006501820500c50600045080c6400102c0343c2e0140955442c0c07814129501c8080003070306021170600c00b00503801440b040180c2c0360b0517005080b0004854620240d040c040e5660a144040460b00d50400241190100c405e55501444124405001903509408541c1410a80d01d454407040c85410b00a5200340940b54203400181c0c19661007010050003907554aa07113804200c89074008906c10b922038015000b04217086ca02402040d40140095100c003410103034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 53287413 1250 53286163 53286173
    0x30c030601061805040c050a0e0904150b010212040e04051c1409031c051305040b0604030311161202040c08100605090a090f0203040b060109030807020418020603090714010201020405010c 82
    0x303d0080d55503c021040c000c40d95a030b882c0101d011412281e40c0707464070f8504400d0028040c0d07140c0c42000703000b18121001d00c80421954282848132a40b06d80e070215003035502800403460024155550107a40c070004c14046a400c02c092503450080c2d0082d0122000aa801303900d0300e9030000204071080124a00c3c2c452081c2094107000503001000e00101590034141000d020310442407580d02000340000e400295171214070b600d54195402410b0103032004c00200b00301d040070070458401e074040a000d100d13080480201740ca60800a640e4181c5405680301c0120b0f40d12850340fa01c6094040717040780b00b1170500380040c3c4c01038400c81900c7e100f20b221482c003c81c200c0c540382080d6071a42c0020300076600002a43d101240c40c003a1401140340040c044c0704011b076039140c507042000740340d400501100d041261110741000400c1e81d15003902d90303080d0100d50000721010021842004101c00c403078000c3d0842404420024034042c0801c000040300e041c0c00c0c140c1d0404212800480c200c1c8614080c00340461110300d08000810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 53288663 1250 53287413 53287427
    0x7060c030c020904052506020303270a0605040201030c17040f03030213080a0507060311071b05100201021306080c04170c120d030b03010b0901031202010603150c020c030c03060106 79
    0x98040d050518110380710360041000c0410442d4181d80d1076000d103840010b01024050011003419020806100f03084c280340300207449100113050500303584001c580d0481c00005601d500741c1e6407292642100c107051807514005000c3c0c04201c13000da02080c581900e03a2140c0b0b001d01e24601140b00707943e28044550f656550b400c5401420701400340d04240d82031050700130002240c04030b0009001c01000604002c141840c15503d8040e642c0c1100d400c050400328034a00c0c115041060b200415401842e4204071040c4a1420781c17802c046034082030344150950380e0000455010750007030860000c2824100001900c0301419240b405c402d0364a204000002c100030403d0384100d01c010000c003d00e19050710030760b01d0000d0006003c04448550404075400059400c01a5034242c421a204101c0903002800480060000074406000520000e00050f40100386400418800c1d48003c0c0519031200c0c9082950b081401c4c1c4a001b400d2880246015214030188202223290016107030030035101c02401011140c4c20040201d60103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 53289913 1250 53288663 53288687
    0x2060a030203090a0605090c12030a050915130608220b0a09030504091a100f12020903100507090807080307050309010e01090f08010f0b04020304030207050405060604090203090d02011d0706 83
    0x13030103a50b80ca580020003a0040c00c0c017035100030f4024000d0401e1402005038400040c180c0d503405600030086071180e01c0cbc00c0030a070392a140c4100d610792070740941908000d04c1803040550b66001480c18440200e41540c1180e00c5034001c0020b01201b01c00e048041180d1809200d1841d03010b001c13180000005000d001c01a00b100310010f100745080b0703042c81d0303840c00b15909403030390855860182c00f102280401e140c02d1040345143c0d000418a032101d07a40b81c0c071003c050b0400c0303d08016241e07600e400190304c21440d14200141003118010314401c001c14501841c0040070100240101d00ca13902039210000350507207000040e00c0700c07242c01038080c40c0740440300001590a407000c40e0003281800754030840003e400c00c2400320b000040600d01e00200341140e04c000100c003150111000284100e206000348400309600003104000c0ea5020348000a003516810001100b5000d15400301c04481d0000040040080001c82c25a50300d0020b81c000780b0a030a0000b001140c0c4e2a02c025000c001540070580030081030307200c0c0724041c0007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53291163 1250 53289913 53289931
    0x30204050d060b010e06030403080c070602121503010b120705040e0f0601030303050906060d1211030c16090e03031b1804111b030c0304030b100512070306050c0702060a030203 77
    0x645991800400e0410010100036038410341d07a00750a0f811543c10035158500381c8003c8a0480c034600d001c5d6005800da15010300050b20407280840c84408100e5280d04a03000b401d8281039040c040e141050311a80c5001140030100d000f942020002592401c1c251000c620005045010303150303860030402440010508420292a00c0c824040f41c2003280c0c10621001e406580681c0d03012405d0b181c01c0c03a445181c801c02622003400380e105c40c40040d01080b52000d0f152084c0c07600f450138040700072014001c645580940c00e8400c580340155002c050101c002c0c042c1001c00c44060700d50a224030806000d08540740c0c001210a40407012010f4007804543d01020010200007c1c0d9a0740481171070005004036084420300c4000071030351000061280b659448101c12a05040051002140750014224820b42c0341d00540c80018551414400880c1482d810489140007401010b82402001a84a1051640c40c00c0030300c0140c50041c50040441c80c5200300311708a482c0c40d40c01505062811049450880c0250300c020f0130303540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 53292413 1250 53291163 53291167
    0xc09090c3a020619260103020603070c0f0209070507030207140303090105070c120807020913020f04090303090203060903030414070609030b07020312040b0115030912030b0607080406020304090b040c1d010302 91
    0x580c030b40044074102c1c02000b03682d05d90844041c409010b80886043e40c003800c49444107001040141d50f95411641d03c01c00500e0070030082482803406003ea044007a030000c3d4400d150804101d101ca6028018015050003030307085540959448003038003000c0c08503010081d01a001042044d1141d40590014000c4074418203010040f6940e070b040c5440c00d80c104100880380203100040d00015450241407841c0c02103030181014a104425500041d8020190340b006070143d0b48805401090500907484101d4582c2c000c0d05644c00c600d030460201e604d9034421501140d04031860854021440800503585040d5001034461001460464407042e1038002d008000104500c001c110716540004c14021003800b4520880c0c030031b00c0340d50600d41f042c42000d03810083c020825280c52901d502160b00104a201c9111103808c1c000f4001040102103103451003041000380c5940800140040e14560000c0103000311070203084108840000780d0f00304010740b00c802401c0c200280308404008011401000360304000041418018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 53293663 1250 53292413 53292427
    0x103080c070f08030d1b020c0906030a170a090807060c0314040902070f02130b0f0402090102071a030907050f0928110d0c03200703020c09090c3a0206 66
    0x8501006a5041111a6000428645c0c01d001560056604007505c0141d69824407540680080d80c8500002035244180c5d01c1501083c0152802d1021210040d041591122184242120300440394010301161002400c0c911001860303001c0803900e01d00790344050f612060b03000590346040305c0e080040c1c2801d00001c8410080001c00e8a030900c01496010700c40c4103840306843c001e0040020b06105450a5400b45080c9501c8484940d9a16050785111100b00c41c0180c8820200c2c2c0100d1605081e5080010130303440c642800300e10a40c00201651145811408503407050f074a450038000040148000c4541043c2104081089154034800c00030881c005002c82d501e20940e0310014200380e48507c27804010b0001d0000e6051000c00c40307400340e0791240c059802c0501410012011541d10030030103c01d407603039044004c01d07400101403082c413121800c0754000b04a6055403e2841c40203031141c8500203428400d441b00303016815005684801b500d685001c980c2a440410241203160f040340b420044c0072030303112400300310321 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 53294913 1250 53293663 53293679
    0x8040e06040213060c02130b030a03140708030103030917030712030203090a080307090f0e010605040e07030b0d06050106200705010c0f0204140106090b0f0a0c0602070c03030819020705060103080c07 87
    0x500000c0c421513584070b0380e05d80c3c18010f00c82c510707841481c192061418165010407035140007401d584556418645054500b09204004409000355003004240000001c000170030b05510005c80825503117110310440403450505107407030ba64410904000e102c0302c0034180795150b0354041c0d030145030300c0f14480c029140c58812560740c044156004480c1200420301078801844a03583c00c0241501820030011499182c0d410002c014040740a64460340380030401c034400003840588030750011085d002d4041c01424513410035140004c083c0c8824042d01c000541010420350b0407015018940810280c6030000d042c0c0d003400c0100448254580b500c044c0c3e13403020303089146001622148520794040b141c03407505183d0355040101c000d00d0440c2980c0602c603406e100380403001c00441010120b0380c5070025402e003e1610704c00c501d01000030303007e0b400303001e0064110030000106041d0003040c2c41d44200c090800707014448841c03503034940c12801000b07000b80c5298014030050000558010061001c503403110125100ca6984d0b42136 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 53296163 1250 53294913 53294947
    0xd0902040c0503090d0201140c070c0b030405071d0f06150c0303090a170f0a030218130b010e0402130306021605030c0f060a060311090703060513020405090603010908040e060402 78
    0x1603070000c0c42c00020062480421703c0201009042e510003030140550305518041240400f9101c4010500002423880401c43c120b941c0317400820f82001060b80b20318040c1003240e1204071030311585076591902c024a000e042d104407001485246c102182950546809003441800c00784480f1903000c0c0c020400c89066810010006503110b411000c008104c001c146240c81015010240302400650909010400700d900000f0b040d1031b40c1c10072914005032036650f0b0080f00b6800b8030185909a0300146800703843d040d200c80d29000130300c0360003080e02c1e6403480440300f009010483c852203481d40480012041c0500008100760020058940150a0a00c050000c2d07290b132419980110404400d551002c541c500c010003003408543da01c0310603002e0810606e403464640034101e84042c48120311801804001400e000d0003648214041c203409001c0c15070080d50007044400a51250180b24410421100090300510b01405507022017984060243d00b0185080c0c107265800b24080c2c14268004d4080c00600e510040c0690 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 53297413 1250 53296163 53296181
    0x90b0706150509090d0509030a1403030702060606190c02030312010f09050601170601030c0908010c11060901061203180801090b010510030b03070b28030209030f030a0c03050d090204 80
    0xc40014440a500d50031100001c0c10381c07002d4050b0074540108520a00040780514010845003441e40c0c0e1803200c000007030304203140290b0081180e8040c9604c812842000806548620865001c65055860340c0013089036034001d008039005418003510007542440c1c810100410075910140843c0d0902428a003210f6050400360401c080381c20120b07400b0403140340c590103226003010702030030040850410030f6030048400d075006003184d06040c0c8422003c00e10074480c06104004010440080103101d00740f001c0100b44250071904002236215200c0451307402541031060b0000c0721184800d410320035985a500381c85607146078002c511030020740203000507070710350a026940007284500b2600c541c1d0b40c140b1080080c202d04503c105400c0501d40381c0c5c803401c19200001e2100a4582d1081c0843e00c07400c4a15440101c9101054030206541c0581982d01d19560140c0180001400071000ea40003d84003c0e2030079540e0042075800c1c00058a00500540424040ca0003011103548079540802c070088143c0104064503a040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 53298663 1250 53297413 53297423
    0x90904060e060f010509010302121504030306060905060909041707050a0302010c030c0e03060a02250c14011404050118090903020601030c1202150d020c07080303240d030f090b07 78
    0x50001c00300d10000c0c055203610003080b111107030495040030042040d44005000003030141850150b0b6001c4500104805465002c604084058a141070310300280074110501c141d6010481a00d000720300c1e03151000550303030909009400134a15649644549030042d414020740f0f074151904000c0000130410034091041c5d114001d400224240032400d10040c11503000e40042010032003218145aa2035602080040c1c01c280030200240e1105c003c911014001522264901c00c0241c2e010290810002d80f45405d4044a07110307800c0c803c01d08102030040d01e11003040511103008a10421082c0301540c001d4030001c0001101c84840040f00e9110341c81e0104130b03284d45200b50090ba0180c001001005000b20000c00506001c60b2140c1403c00181c0c0400d00000c50014140b002c6500400c1e050a105440d5051b101038540103002c50301b54a5441c5003064a0754420f84014140070000481c0340e00c4c1c034510720042c00240201404124005e85c45403011141c4031448581d2104201c050f080001d400900840a04401c45c018 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 53299913 1250 53298663 53298671
    0xf010e060a0207080a0c0203010b040e0a02040507020a03080a11040e0a020d06090e070506031302030303280606080411011808010209010e150406050f12010b071115091509090406 78
    0x412a45140c04001886519100d00402c046400502e9036401d454025240d0b06140c11007241c103200007405408071215042d0024131b002149d50400d040003500c245041d0080d03904115a4a4000007261104410603018002c1010440444c284500f142e011505500302090342c103007010f0f19a80032690105007500c1401c5901c0e0080380c1d4803001c09107407084100410104104001c3d05044120807500c0d00018410710344190000300024036014001c0703011984c424cc0c0101947d9592030050a8000001d0041c184811007210401000c10340d0070a0b0b00c030b6002074600030345038800c80c0c1d9075a42e82c0080c62f0000c0404507040013101d130056605904440ba0900c0500b900704000360300d40c01c4a200040031100700d186614410401113401c3e070403041c1b103002160152002d03031408541c0e84a111280309168400d81400a4244542c40b000080c12007031240601010340c841c0c6812840700c1d40d807104104d2140701070290440501d208110f004001c2c41c3c2103012000714060190024100308401000520103102203070195042a00d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 53301163 1250 53299913 53299931
    0x3050301030308060a18020a030b0d060c08010b07051506060c070906080f03030c030705250c050103110702030c01030e0109050f0a050607090e1303030906020315130b061204060902030f01 82
    0x8816059070045055400314002450005000443d0000b54032280001e1f5000904c058120300c02c1c1c01000302202d001d0141614114145484001044103103002d03000104071f007001051000303c0c0c008032443d40d5005402440d14090b00210a2800d5001070070296000108000050022205000000045c0503203400040c00502c1c1c03049943c14906510034003107040d0802c1007041840d04e6040140c035001310051030800d4403103a121004840c1901d01588594001c0b801c280e520003001604440704003503403c00c2c1d030240302c0b0b070190704a011010b020b40c1c04020360642046440800e254801d62001c0300d1441000d00104130031009440d03090404020812401154100b4401c90043c00020016180c00180d60b203051440d582c60038855915000c00501595083c071003c13040e40c03003414807a800c4030250740c2c0c0104046680c3d042002e805008000303402d14030f0b13001d0048843e407800407032200d01c00c482c1c051078042d1084e0700e0700c840b020340c07a050310030300070400c0321101c1ea11044000981c0f410021680f040403480000106110 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 53302413 1250 53301163 53301167
    0x90418030905030c030a0b040201091d061e1008040c090f14070503010e010b070203030403080c0c0f060307120f0908120702070504060303090905090f030f070303060f12140c0904030503010303 84
    0x14550442e602951015070f102c04152000290408140d070056005c4c40903445900c012180c0020350b40c4000c000c004003117181000c103500c50001c41d00038101103c01070b1000d4001481540c50f80400c51600307521490607089504824081d0021980c02442400420045911040d4120442d11000c801041031b50795190555000c85c081014540c00040c5402c06074115803410341d00c400e801e1014050742021000201d449011900c0810035103001e0b5a00c9000d17162111540e0b08440d1b039814001850612840380050884050304212080301e001388042c1c1c0e40c060304200e5035526100070b403010f4446502025582e0f100d1178081080d020140042d0003603c2e0028610341008000246030801540007548118601302c01000001e03000700c43c01d41102d60102d000300700e076a9098012800d00c01308510700b4903140000109a1b00d1032041c0401066004e03c280c80c00c105150301c400903032409800360f0080301d4030741103414001404a02807404814200c904141250041c086a80c085080c1d09010340d01103001c10700120041c4205a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 53303663 1250 53302413 53302427
    0x6040b071b060e07030204140105030a171c0e06100e0105060a1103040803030601080114010516030315030302030901090806010f0501141303030512070f0c020405060f060408061b160602090609041803 87
    0x440d40c000305048c0d075050200080c0c03548a0440e004191206003c0c414030000c0c2c45d641a501c401460401090144070451000303c040c040040c5003080e01d014100009185600e41d45c1003000350340c1841d2034420540c0c20030080c810340340c1c0190310100c184402c4064284c072031202000100007a12a040c0a581c0381d0034018005000410180c01101c0b401d01403222a046591303000f420350340002c401300c0800e0110700ba141805c1d001080303c1013a8034040c40b1006d002200b07058001008000b07105003030b83d0361f066240e658808240c88100c28010800164a101401c002c590b100700d00e08802509400d080b5464500241c03185010b034240c0b03600c2100411004580103400090107001c0380e91001482c1030000b102514402c0052030b5400c9207400910a541e2000401c58948500d030503030080303410283c80710382e40f1a220041b0582c0e40030111041403080c800d0350101220b0151002c10740e105550702c0c2d070102c0c04107000c0c1e07551800030790040c1e1450343d04900700b0b000341d03401c550316030180600b584440c4080013201c13196070400510038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 53304913 1250 53303663 53303681
    0x204030c0801050702210702210606030f160b0307050c07180b010302210405030c0a03030912090501090b030405150c0a0f030b060414040f110a02060906040b071b060e07030204 77
    0x164104100403c4505400c010078000d801b518503105503140c00314400070300d10307408003d01c51031b404c500c96180450b1280700252040c000c60003201213469010000c00c0b13940e65841802c5050210000c00d00d0b080104a20140c007a54010b011070500f01d0a0818a100e103629007045980441c0000008001e00d01002c602d41c4544c8070328050030700e41507207000c15400318054803c40d41002243c1740340894001809100081c01903d03542050700060340c1c3d01d4806400d004018000d469004c2d10720348000e48402130010f00070203201040310410b03110000c613149010210300c070a800040058078240606110b43c4201242010f61920551654145549074a030189000386000894102402070620b40400c0325420380d140300c20384003140c960000d94001a000100401e014000e901d02c21134025003000002c02d04004200701030300c188007881d0300701d0700c8582c0c4003000c0d1aa101019a40540f00c070b8074840214080c144112801048104900d180702004402655020215045c9109001d565000b420007801180b60a005550217 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 53306163 1250 53304913 53304917
    0x10b190e03010b09040f030e03120a05070c0306020c030a17010f0302012a080307110f031e13030c0503060702010b01080a09020d0b010e0a060e041e03020a150207020109170c040b0a05040204030c08010507 89
    0x482d00340703c0808050bc00c2c0e640c0038007440b0000ca80d2000304a0f8103580c0d9406540c8c800c40c00c0d074440c14008041030340c94100704030743c00c0820390400400c840305526200310f5049513140000050340502c1c50300150746100212120412075645181c800031030124040144090500c240c001c1780d981d1400000c0280301d5400b0000b0404650040030032000e04000002c182ea00310303240c11519003042420b4070341a40325031040300c44911b481082d96000000b400600075890b0110b40b0240d003506c0702075944480480c2200e41035086a408203040b4000302d48401038980c8a00f01c81d51001d03051008030f01c46600c6101001209034844240c0040c1042000529401d50060000414041181d0b40560030241d483c00c200c1d0041102d86080110030903c075009041c403c10015142d42d03088040020340d21600000c40b0060b500c0504140d000c0394070354200140c1c0c5100c0307000000d0726074801030103003140500780ca0411016001d4402d0700342e07214429440100c1c6680e0b543c80280015031107040c00e402d0541c44d240400f03094510041034841 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 53307413 1250 53306163 53306173
    0xc0913020307060e12011404050706080115030506040204030f2d03090e040303150902090f0d02060711060415020f0114040b0703020c10020c0d0305010b190e03010b09040f030e03 78
    0x41c0c0380080d008095414a040c11800711580c000801c48003140b440100c0029800c004445102002d60020f20740641c0c020b509903003540c0c0c0c542c1e01c1950411030a00c2380034025119441f241c516644030768404e680000c0d000b400036181503580c0d118024241d03050f05082c4c40c0c002c041211211441156085415078120141540c910925103807005061024240f1844806041c0100087c040510a910114501491481c01c16119841c1c800003c001d42001c81d8582c0601d03400c0c0074040300c52600c28100d061041d801400145441e40640c4c0303441e81000741410079a004013040c000820042201c83c0c402d01a2103240d40188452000f4800361030075107880d00d1100c050034920400344000701e101c1110036980400c0030b08001d641d440164500d14136080703a031030100d2002403002c640d00c000b0003401300750010940320a550512050b608d8000c510014459061840c02c01c0d00c4850601075010300601482044020050000a040b1840c00100700816412182107038006c0c5404840d604158001c2401d0f020b007181980101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 53308663 1250 53307413 53307451
    0x1f031b0903020105070507050a030b010306230a0207060b1e0f0607020f0108070c080d020301060e010908030d0b06070b04060204030b160c030305060303070606080607110c0603010608070c140c09 85
    0x34140319158000030341089000070b440c8060000401502d0700500000c0c05070842c00da5203041222000c070081c001110340a00b099010020198070070315942c1d0f203101001c07500540c0d403504241a1700a51200d9001c603102501c80c1c040b403c1c15518a540301441d49505061501c01049040c20070400074540f5400c40d00c100024403080c0096241c2000034190920b00307081c010b256841d100020344100f0301070003000b41400400a41066900e805402940c101c86035910fa014100320004015108074200e401002d0b002d61052090000044543e04002e00b41d0700d02070006c0d40f501416403680740440703204660684100781c000904004015a02400c0ba62100031011000b186194080300103250000f10b400240806449002040326540d00348201c40302103500c80c1c010402c09039a101c105459500c12205c1c003000c18100f1381c1c080c03440d000100b48845051001001d02d86181e090400c01e80d0031001c060822402c21150250131030011725224182902c0d083e035940103050700d070044801c220080b0b04c02082001031050b00e01c900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 53309913 1250 53308663 53308667
    0x30e011410091a0609060c0f0c0a06210c030e030c16050105031509071101021606060b120a020a05090607030315090b0607060c020118030c140109120318021f031b 71
    0x442d50480044a60710380d5100c42000150560040c02c0e1883c1f030502a400c00340d42c1080000810500c04070f4152102400e50f5a40ca105a8004542c20001220600480d03169148202c40c0d40c89003084041504001600514a8078003d00d5900029001d915503807000043c0f1980035558802c5000a013803d1070181e21b10310b01030041c42903000707070040b020f4011038581020400042c051410080612861002107440c0c44030030400aa16150704002542d0b0740d4640b1002003100b40305171080310200c5640d0081c1216a80b500b0500713034001c0d03200c021040d040040034002d84145a41c1c0714018804107010395000306445480304640700b004455a403090f2040c914110068007161120b00548411907002035000031900c452403401ea024025030244103400c0e000c42050001016040155802e036507024403180c41106a10b03001345400c0b40d503640700c0030b01014134500000780010312907044250084174000684010100c2503000c01c0615034130703154252207803025411003400143d0520446844150f151000c0c1501d030425900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 53311163 1250 53309913 53309951
    0x10c02120901030609051e0601030507050702060c0f060103050703050c090103020a0b09030a02130609050c0901020303011e08122d03011208090607050a03020f010b090115030e01141009 81
    0x508240e100c0801c000000d80e000340d100ca8024070758440b003400070389400000b040003903450060380201e0101d00b40104826501c2445042d01c40c2d44107807100c0b403403c9100e408004180c0c1003a07511000600c40d9001c01030041d14180a44c034001c510800c018a002400d510b0001d0804e1841900135001c0c04803040108096981c20035001c0071200101c1030300340e035180c00401203400e1845175107010390030481d0008120400029a40003808941c0710020802c0305403151a034125a501c40d0b03800c40d0f40164002d0005222101212002e020f001c0504086c02e0461aa195011428950895201281884042071804a0021030364071a5051100e05403f072501c03c0c020005e024130340c007040c00345085454500c54103000b04400d550454030304280003044280c440441d403170029610664810102c0040c094042419080007050140e403440100040ca00001d41c2c0c00c00d28074541002e489403102003010340301c03200d50200313036000e200303021003403400b1403601a1a02e0720300841e800b180c2e010f5110490043ca05844649200c0c11000c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 53312413 1250 53311163 53311183
    0x9010507061515020f0a020d020405091e0a0b0c03070c0605060301021308030a0315180b010c080d09020f06071e03020a0203060c040306050a11030439090509010c02 72
    0x2042500c600eaa420514010882d074030000c860052002404203101c0300e9402d45588400c425403c8032010700c103040000f0b44035541d0300300007500004084021801441c00ba001598001c60482c1100d480c07a407040c0f04590700c18561002031840ba00400000020700001d4040b166004078940071a42c594140780c00014840321260002612481c6e0700c402142540e40c0a404035070300340020000e90803849844110807030b11790707110820710340119141c0700700c40fa007440d51120301030100c40001c14040c0b4000c1404040c43d014000b2807401904014118402c0d034001902c0700003801031002c0034034002620038924410301002401c0150590721841c4144141c00000e50f4210010384001da000b04cc050361800e0b03500d030030b81c41c042e800d040080d850f010382c00030010400403d2016208403806400c0074801c0b6120710804004a41d50802802d07103c010401c0014089000c1030007107440b0b4002e1070f5140a103082c5100ba920113201503e601d017600d07414629020420344e07800d80122500007404800803c070340715890b01e000c0d569980c03281c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 53313663 1250 53312413 53312417
    0x1a030a0e010b0303040609080f0703030f03230a02030a050f220c0801110307020610120f020a090e030901080c0c0a0308070309051c020d020c0108180c0d12110a0302030901 75
    0x281000c204880039000a506800040c080326200e58445501800c03c4102c0d0040d9499442230004c864107013000080c0250442e60980c1300d5203400d40b00c15000702d024142410304500c0c849400c0c0d241140729400c004800b40b00700642180147c42e42000d0341c044c0d090340c0024001c4e01600000c00203001e1030301d8444c0c0250010751002c0880ba0312114403803500031107482c3d85511060fa07075460a000781a214100b5801144181d20300e81c01d46860f643c0303249080b0381d030500c81d0003809180f95010440800280b03031140c0810309a40014103c00d03940360307111074082c103890702101600400c0c0c0001c03908011550304102d2140c1c00589035045130b8102580002d040c0d136074050980303001e001c1001440200395154001e07445040071710b07002000e8a01054181c00d8015107012519a1107005210340310500390598400304a0101c64981603456014030b8441c4262000030301030054040079240150303203004001c1d075111102002d03d07074800c64401c0b4007000d03e208050410131014254520b41e400a690180021b039011044541c002c10034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 53314913 1250 53313663 53313671
    0x9020306061801051207090504080408070621020d1d0705030c010903080a050a0c0f0c3b06030106080609010501091d0a02091003050d181a090d02060c070b0705071a030a 74
    0x808178146880315540c0300e035004628041c00e00017403101c0307e00113100342c3d22410101c03010381b50354802c102c0f558001800318403841101c0d1581c0490006a03a0010582ca203203080001c01c4540e80340c2907620002104460569450340050000c01540c207007030020340c1003c0700908080e96039a00e99107a04c1340a1280d00765072001c10070002031080c4001d010300d9508800a0304013011824142c424034000d084107009000f0b5201c0c048045d561181074007002c903e00107241204080301c01a007444080041c0000f40090248d6915540360003000c903c41388200504d521848050001049652600905404943c880d00810110340c074907600c0c083d504003001840c020740a6050702d103518190b1700c01141c5030350308107190001003460080081041e405030380101c01030f1031245280002d40c4001c3d5a10000c2c0120107408103404d09406003070211000e41e15004c006085024000f8151918140c08032100d14101a85034118013040365010410a084c040c08000c80700280c040c010441d001403040c284c0440f0a40001000800d003182c1f2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 53316163 1250 53314913 53314939
    0x90b030102220609090b180c0904020f120106090501020a0b0606120109020d050f0702072117040f0503010504020d020402130b0a0c02010806040614010c0318090902030606180105 78
    0x2007503040b02d840c21042c4442c030041000c065074030205019544103510005044841c007003a1315440b0702c100401d885c0020000d07048900c0b204403130b04111400600c2d21450344414000c40880c0d4403180028105101074221059460000383c2c61200d0307500c41a080041004526002405266000039450265039001b0750030384c40c26543c3e00000b034064490000080c42c00d000d800b00009000c061031300500055881401c06000907a1801c040c0d1a040034121004c40059000080030404507900c0b07100e00800b5441d8000741b07403100045d6210024a080030344c010000c01140000e0420003104003245680180004500900c907a06040d00002e04d80718441002a01c5a5070000e62124410b524002610003450099170b01c41d2200012000600418002241039003c18622000540b0740e02e450320808050791401011051501c4400004603051038440360100c1c140034503040400d8503440f01c03540005c010300d903041e00810103241501c18141808405030541d8003411140c184480d044900c444294152071003600c480107080c031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 53317413 1250 53316163 53316169
    0x8010b030a060b07030e0f0f031c05090303070c0303020f0109030203090402180306100906080c030703031404030506010b03011706090606011202070f0b010e061f0518030d0c031e09090b 81
    0x303038550051943c0c1c1030009503101096009010b100e09503804445a0789402c0d03065040c888204c02641c052a49900108031180d496182005400e881c001c40785000b90900541d40c000c01c2c55540014420b542c00302e000281001050340c104501d03076040209100034800c001c0c00707580c0a55240121210030748900c3d0042481d00103041081006401c0076401002c43d0001d04003030b104a16852118041c42c05032904240001c5a0060002441008218042c0c020302c3e03000d203151000c4035031540c0c0f0a205202e90320308200c00030210b023003080075034040c00c0700d1800c0c01e640e5454440321208009507003130406031540148040000049000c110280d002d0021708005000081100c0144024454014020102c81040c51a80180170420344058141c070142e0405960984884003005407000091080049000500720002c4c03100384540f000c1c051003081100c11001c1001102d00007400d00440803081000110140aa0010700d948681544950a071190741000c1c12a1890402054108580113004800e901da1a440010f61 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 53318663 1250 53317413 53317421
    0x13061b0308070509040f06060e0613050d020a0f080303090115030b0711070b040e0411030c060f070204060902120405011505010903021504240305091501050f0109180e060906010608010b030a 83
    0x80d000a10401c4680c06c041c00050081c0803c0c004d00c80001c1d5000b0400280c0d0500c0000c5584240921b55035601c00391509003000341b03601d03c1010490300000800c030300003403168a10000101800d0b200e8080c54613031410a0345da41c02c5640014004a01c60001303802000803e00001d4030a0b0000d9052600d43c000f000c2c1040d2407490a0040d03400447c90550002e80040c2c02d22802c00380707900641c03003141d8007030a90205004040da208c41410041e03510007001c10650074442d180780c00a0101a1004d032011440d5641d80c062442280c103c1814159401004420041041402c0c820f040d98440f06000141146092038002040d000050100034000e10040f440c80901a8224080d140107140304040c8100032903e04429a03a401420074454020030700380341c0855509a8042098120f135010f91001c009160720b090108483c400b20072901906014900002080ed4261201100c84260080e000414080781d0040450b00e8800007d0036682c05070031440047c0140707a0b01c101603504541005840a40303a40f10052100c1c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 53319913 1250 53318663 53318677
    0xe06040e01140106030e0c04020f1603020109020307090b040506100503011a0702030607050702030d020c10030902131104080f0c090f22030315120309030209070309140313061b03080705 81
    0x161100341d00000c1c565905070420101c6d1511141a0780740c004600d4288421b074069080d00c0e00100805200d41c3c950100c0702100381c46058000e20001c641084590003280c1082c806403c0101000d45445c001411420540516500503006a5004205001c40075004000d400f040c0903400821000e0704060312a001114251040c041e0024203071002030405003405001079200320812130180c041c540c0d20307032080c500120300c80000040c0501980c1d0029900c0c44118010881000300b264071600070070403c203040700709104494601c0d404a000e59561030602c500140b0304440d01040e20201e40c00721801c412140c4500c0b5400d42c02c0380071011000c082e5100d1000705440344466140c400340c40d560940300c070010b160f4180c010445129010344455001764440744142d40d00b0394035140241c0800c3c2c400404000508104080d10350081c0c451030001980755180e035902000310441c01910701780d64400b0038884c0c1c5030300f1101c004500074095404c118000d0102048003030016994603c018040c0300501d030009107014011003c42d0700d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 53321163 1250 53319913 53319941
    0x20c0d0b0721090203060603070e010506090a17010b01030e010207030e06030411060a050a0306150206040f110a0b07060509070501080a0b030a06140912040b070b06040204090212010e100e06040e01 86
    0x101901038220240101600f142c103130301c80e1140002160381814081114401e68041280e1076101d81c2c240300c2403110680c0005605a0000104000042c070745210300c0c0014031000205002050b01c1c8800c400050642d24642c480c4e19040e40704111080029410018070605064143c400c01e803030350750350304150300150741e40000300340c1041c0c00040441c04964404028949900252810050300340c5480d041d801c00e0000c4000302000d039010030046004607040da450011114410b03e6000f4928100c81d001c2003030030600713510800001d1400300d6004d04214240c0940e90f4009910b400602e011860034000070086038003d08004c0203265200004061914203200c0144026001035040c0106a2550101c0210345030407904094940078000c1808211403e0100326000ca5244d0090036092000301d4541c24080d5401505141e071059080100140b0f0032843e00141000400c42c0d04014036035854108a425105401801d0081009100c00300344007031180036440e16000310341603d0010740402100103290040c034214004002d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 53322413 1250 53321163 53321207
    0x60c0109030206010317190e0a150905030f031201030f0c0302060708040905070c0b0a020a020f07061709014a010608010b0d0210080c0f0403030816020c0d0b07 70
    0x80c560002181c3e4101c0e445003074003041c0340c401498001d0381c1c2c0c020b4540f11414102c80008040c0c3d00c0344203840741e841c4404000c04c0300c03107480d548958030400000c0b404601c001207200320350100002d14050005420154911010f1850a20018000c03145810140002884a0f0011200c00305000070702d80020003942c1e024004660780c0b0341504120303006811901c5010540d6041800242c8014481c1c04041c403410ba20110704451030300e5030780065000c1d4010510260451080050309028480c080021100910b0140c40b04c100c140b4003603081513050380000b0321801850781070450f07103030f2201140b414208034801c0308581341055503211061040003d00081d1426469008800444c100ca1010352212080300c1c0d0342ea000300240e0410906012603590342c004046e40c1320103076001c00c01c40d090091400a6003c65014895454020380d1130034240703107821540084d400104040704002415116035803480c95607010707000800c02d100001000aa074842d6004006100d9000b41c80460180e80c0929040e414407101c2441600d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 53323663 1250 53322413 53322431
    0xa060f050103060b0d050709230109020c010b03061e0a0204050306091c0e060708030601020a08070308040c050109082505030d050304170306030703031407140a0209060603160e060c01 80
    0x840985400c0c0400d4a1040c600160091145460172102c6400d41d4050301504000e0b103040540c2c8000c015480c2c151200e0080d054040d60120b00390200c00d8040c14007e6401130300d410703ca941c040d08548000c06854040c0e4001010700040c13500d01c9510b00424000302400000a42d908c8a103030000e030040d640144c0d00740c45400c0030f20404c41d41c041a000c4080f0340d19960106203000042c41201c1c049a440f0885402002c10060303080466030000043d030340160180100e03030342c10710250358021031544080c40507400600f070030040c8810000300c2d61880c40100f800f46003e0011508013941c0c581c50f2451607800d4102c100340c0d1100ca14280c52041d000740c0041c0030050585640844d140c0d00901654005c440c1151040c140c00031a012854144d0240c070300603d400740003801802e007180d03800c1d24610349150020903014814454440001c0c260b007803090003201080d000d02a16a01441071180c03052000d050300e0320812050081212216280c440303000c84d00e503585890540400f41030b02044440c456040308052550070a4041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 53324913 1250 53323663 53323691
    0x216050303071101020906090f0d2a06030b09150d1401090501060503010911010f050904051e0f06010f18050301020d020307080a02040308030105062a0f0c0402030402031e0a06 77
    0x503621030652070f02e6960302c24a04080003802c078411414055031260091080501c14140100c0c41504a200a0419030f00d060702ca88a0210200c019088032541401030300412007412940a0410020203850905000003400c607030000b00f2080e0020300c102c441e291410b5401c113040e5a0034424100940d04680115401c001d00c0406074080e240c40e41d0183d40c10360804c0d00c00215401c05100e02488140c1080c5040b18112075040111030f00c1d100e4800c42810000f05004640d056507403489031038003070b008038070b201c0c481c0f00160b2019a01408006020042c1c0c542c1520404c0484e9801070500d0a503400b00e4a00200c1c0390400b0030020420602d1500480d4040d0320110701302449030300e254000e40c02825503403680202695120300e404140c0c40740b03000c000d000100a000401440c201000540441d44c00740300c0a094003180d041603881c5001500c10591415070048562845514045c44482c0c255941510f00750b10b549032a4011071b550740b41034110003a000301c0408120590850501c920350629601c48810b2001d40c00304c03404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 53326163 1250 53324913 53324917
    0x705010c020d0609390603050405070b1804050f041a070203071b050103050f10090b0a0914010608180601030b060d0507140102100c0807230403060f1103010b1b0102160503 75
    0x500205e08045a11030000008465030724400b00540450500181010004c4002d00f50141040300c2038890000d0218a801c0c03500c01070801807166002042d520740d9a0810002030340c40140071b002010154005200100e03550f010052030130640322920100540315110100c3c9144a48500902414920058502a141c0440c40310b801c4803001d81e400c1c0100e403518840c4e805d911000b561b1910216404440c1008032040540152500c008002c0c620001c8580c0c90401e403050340c40a14400301850f00e03150060215640007000306812070b0b92500c410140039112100140e80f00010b000181054900f60b00041070769842d02812046180e00c282030740c005564600121804491000c6141d001d0700402c02d10020b0302041c0e2203508da2040640d61aa901c68803814000c3d61251220901315042e041030300044c3d45c4100d4581c0c02000103510504000030b40e01488034a9804407a0301a250b803696100420041003c2181c4106507040807040780d0702a10881c00c000911402403103117040180c0001e12200d9454140640480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 53327413 1250 53326163 53326193
    0x50c03031b06100e0a0c09031403070510060b07060f060506070f060c02011112070e09100807050d050a0209190f140708042001020115080105011a04030201020705010c020d0609 77
    0x2086442c07075290020300d90741203240350140c0d1210841c040005a140c0e40290404507054010f030901058542c0c40c0c0e00c40c45041080492002d00d00d600000c0c0500c10400704201c280c60888a00108000060400340300741810b200d4400060b09550302e8130900ca5a080c0b15a00c004014540103009030b5032020b041c9008449004214006e64041c0e16100c50902c0150040c090406600c000d90444c0e40390000f14492200d0860001e4486001c00c04900200c284580b16901c10398020001c110040307140924003a8490314012141e04030b42c1c002e00c11021508001b0b0000030380341c140c0b2039040342d40110b90703610540400b610400d0311901074055410148460500545075006114040e45454086541e40d035400c015100002c05035401401c00ca0751404c0d40000700d80608000042100520000c18040c0070b12030780e440c034001d01c0d410126043e555140104140465a025034200f01c4e1800c0d4140c0c10a495900080e40311036080c45014148984040710004540d01c2c905500e00e4a80c0c450340030844c00d50300d41081640c21800b90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 53328663 1250 53327413 53327467
    0x105030105130f0213180504020a272a1e2118061a0d020402090f0a030507081c02060a0207140d021b0301021204140309030a050303070f1b030c050c0303 67
    0x2804035110091b913024031481150050903520b59580380c60240c4041c2c4000c00445401d010344030b410301ca070340007490042110308601e4aa0300c040131140d40344a00340703800c00a6604802d200c401d40c40d04812924550810740d010440303080801c80b94194448801b180b44e01c108251060310714000800c0d1840021660011180b07000780d5003000482c00c0340d101041c0c21070100a000e075108500c401c400c0c0051070036030020035a5074800b602294214105002081c08123071241c204407241e070007d0105008c10001006171000340110441500b186481100c80079494200250011104a07000155003050042c950356040c401c64000084558601510300d0094480c8400343c410150401450410f101d545814001c0e5546148915100f100c907032969912803c1c00c14043c2101a400d010621064016175000d00004400e140154081c0d076032441d00d01070040c6680481c9061b1402d10003248030307210f000c1c82940f8440201d03a0f45030400c582450308608200d13180202c0c05255503494800003503041c6918003d2042d29040381504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 53329913 1250 53328663 53328689
    0x6090c080a05010603031407050c090403180b0d0b03060c030f0c070f0b09010b03031305010309021804081c02040f29030705070c170309150c0d0c030f0e0105030105130f0213 76
    0x9024103018500c900074014255610422100080b1702cbd0800b02150018480c0c100040c03044104a00c0d41030240950740403d040c00b202041541c001001401140d8140000710060002c51601e00400003481c0000b801d510404203a0307a0015110440a03000c8412258101c1114050b240c7d50b03103040d070100c0d481291081a55400c00000403074a00b400000d55203520b5200c82480c403000e0410f00110000d051401c5d068be8001c52342c00c5400042e0b03554481d002d024500810200d41d40e18580413000580700382c001080350501c3d01c10001005118140c80c2c003002552030204e4a240840c0b500341030301c00c01054072051601911000000d01c2040380e00900202052481040075071201c50362040d04441d000110030100d90709400404c012800740c0340c016036540720702c40110315160a0a03010040c1e28034207000c1e04144408a94a40340e480d0030f154000003002c441643d28034142d80800c5c51080000c005000610440303000e01d40b113080b42d08560a9907041051002500c0a04548409040840d1960783e07a0b03510461503e40f001e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 53331163 1250 53329913 53329937
    0x40915050f09010321020106031704030309060801080304170c0910170f1b01140304030f2a06020f0405330a09031b03050307060506030706020304060c06090c080a0501060303 76
    0x2040b608107048a1304840c0c88609206003421424004030002400000c6550303072140030000411810f00c9014104040c0a419107036070031361501500d220074a80040301440000401003020400000440e003ea40c2d020b450701d4044c04040c511309281088511217154000d51120420048017403100340301c004c0302c41c0091020082c000b0b0020803611101c5403c00c0001b16001350800f04910000084c80b24503204040c03420352180c000410304c0040d02e8100703440c00c500050410f205000b5061344a01240001c03c2c90b0200e203407081503002c42500090003000d00003490543c02190405903c840f075000d032402440042c00c0c0005443c01904c541c901d24a40001030181c00103003c2408540c0e0390b07000281c1e5a400d0036900d82084072801d43e00c98190300c81040003d484034809607000840060790500c05005058847c00c004a040d04180d8205400c1902c16040803003198411b00003003007407682c0003407a44141500030200141c81c0b01d803070901c00040503039031b000003e6a00c114001442000310561111040760700039239440004c203003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 53332413 1250 53331163 53331169
    0x40506011a030f07020a02031509010c1d010e010905040212091005040507060c150e010c0306090b130f02090306070810060206010b0a030221010b040f0801110f070602040915050f 78
    0x100d0078144200c503001072000401400c0750700c00c800e401425030300441e0f0420005600103450400059130b140d00301c00b1000140030910801f40954100354180741040c1c2c9070300c1c414285410010044101c214100061816105c00f240d001e11021350141801400966413003417000c19000c071500c01520705154610079150b8040c0240c16a20549004032f074008050030403146441c000305d13000d02c071040c410303a9185d4000042d1803442b20786200d07468515800c8000400d080c25002c6001d800c44441d40d0082420b81d0400e1a40c1a00303a880019150540100340340000f1039102580c40710f030090142c43e0f4881d40600c03c00d003e1001143d04411024802d100d00e0840204540d20340c01d040303880343c1082c410000c14070400c1c406282c40c0d900903005000707819450503610f50f03008001101001164000e0f03100c6145000300280501c01048191115005032203104c00a2200d40c8000039118400d05c6440d524440026010440d40d0030080607404980091416003824044412808015031801420788600342c07044c0b00040d04000b41741 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 53333663 1250 53332413 53332439
    0x2031204140607031101020a0305160809060105100309080d050f0a020405150702010203091908010e07080a080a02100903030605120a050c061e0403060c320a03091a04050601 76
    0x941c9090050080d4022038051101c2c0d41c0140e8021002c1c00540c0842551100d0240301402d800d100a980110382410030078107000714050b0505c000810003190900300100c0420010f685411500251081c40c1c080e144400100d000f400c11002c01071245400140c080411049a04000d0085405800724400754640703403112403c901c524400d044d04140c41001501c10f50303503844090140e00f401070041c0d81c03422011400140002840d1061000400031042040c00808030910402c6034600451006100550501000a0341c40040007c010000e840018002c052a442400310312444500382900f0321041203e46400b41c060100e0340101400f415442440700084080011012030725a0808040d009111006003403000c03980c861003210301c540d03082100607100e05482078000d00c021402820001440307540604020010019102c060085079038140315010103541c440203440030544022a02903032840e000105601400744901d003c3c20600c4a088005104945410b513a03205920032001d07640d0300c2c0c0e280c003001c541013 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 53334913 1250 53333663 53333669
    0x506030f060a150c020d060603020402030a05040b090705150a03020f0d050108010c0302090f01030e0c12010f1409071503060b03040809010905150d0f24091b171003060606090302031204 81
    0x2c0e40840c44c030015013050040001e0b11070186002080c40f0f41c40e0340202c1c3c20303039005680301c07036030f0720f644400b044240082c4040d0503800801d4100602595481c001c00640c04100a84c0840214900054000c041c83e000703070304581c9540c0c40d40c19100d86500a40c2811001060248514005c55081c0410341a1062082c170803103503c00f100414105541070720200440040040701c181d01c58501c10924000d00303566030410003002c10101e05001054851487c030121064400d8190303040040034039803040c04410907010682c80e094030300403041c100c810800b0610031400f0f000a42c1c40350002950000600040c0802940100700003070017a2220004585d0700c40c280400305100640e800800e40b01400041031525036500b0442a000112002041c401d80401204002c0100c45d9003a1a0b140880d6404001980250003110340462224052101075410640045c0c001d00c0e03201d0044010707481d2400043c2103450800180005590810010484941c031007002034040403080c0010b074132034802e03069a021b410f03502d1012503044d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 53336163 1250 53334913 53334917
    0x90b010303080403091a0409050612010203090109110409050d050708090a030812160504090f0e03030a0203010f060201050610080702010e060108011a0409020d0210050f030a020304060606022d03040506030f060a15 93
    0x7d0b0038a0500000000d140240c038031684040300910998a0b0402400031b036000b05841e60000424001d98500111381d4010400803c1c080c1e420b203600b8402190000c45c0312142e290032410001d0380d80381c01d07141c094800c0c40b44d2551160303c125510001704c240000d150291050303841078003001c8665200d140241c41d900861003605000a94200001d11094039140c0040411b40c0414401148544a00c408c00b800e5070405c03a1841816940270004219406090320010028041d40c0000c000c01d007000070100310420015040b0070148440500840c11780e03071007588035000c0514a0025951156160744585020380700d00c00c001025645001900c2c0c1403071626100745040154000c3c4101c0e00000c043d424000d0907414000f075041400004e00c8190071000f13644005612802919500603a81d01d801d2905070300321340041e00300380219401003c5032007620442003200b002202000030042907041200700c20300d156210383d0304116000f000c00b1041c41040c82c0c08251076130007401c00320b4007000f000d5161100d0340080c81000c8540c3c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 53337413 1250 53336163 53336167
    0x40306052e0317040306020d05090d0507050304060e0a09090302160f08060103060f0e0703050d02070902210c090d0506010504111306050c031b0307030206070311120a090b010303080403091a 83
    0x1d1062000e600120701030f40c0c1d05030415030380740c0350103089811110fa400c0c0071a07114000c00c02c40b080180014041203003581441818002181c4406a890146001d07102c113001000c2d641c000329682d00c45441004110b00381050107020820721f07000307403038141d40b5030104c1c041e8054800110728001c00c504888161034a02004042c00c0c2e1940d00c6010140100800440f082d80e13494184018814051008201450180d001049140e460141c001c5c54080d182d80450442c0344140910300c0040c00400c3e0101414681a01071030060f15240d44a40d01c0740f154812503980110101c84a07000c0140100f9100d0480b84111002c0040c446e040018014521070344e0f0070440b024152203028070039140a00003800d50010381308120381c109024140c01c6c8a402d03c1c860011a00d41d8008144c4204241d1304005495204100b0302c1e06218819030801200584c1c052100c1c06c0c108125200002450b0030340c658440c1144d140c01580c04803495940381409444450144c6065000560355800415041b400301c040b50460703103044440714 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 53338663 1250 53337413 53337419
    0x20a050907050f160605010f06021b0603040f0201030e07120c080d0503060105070c2114070f05040b0d0f0c03020102060f040503070b09031306050c0d090506220308040306052e 77
    0x1d245502000c55140f400c138000710b282000c12000d214145c041c0c403202c00440480d60401601074500b10014910908200c0240b10f840c4003900c9100c10b480e00035070310003000900b20f4024801600580400440e05910748915400000c91243d40380c682c421607801103aa00b00d046d9140c0000513164016074090401096040010407540d506c10384c002e200080c094007000d01c22a80310141180700700708021040da21078000482c0b601c24840d140b04603914080543d0010310440345031006004c160441440b910348500d0b0b0301c0318164081d851b0800b0096816038412801076800c0c01d545452103100903903000690040c420741d00007856256101c0c04150045030003c000f075042c28299900c0e003070403000003044807515000030320000c035642c140d0109550240600b521011340f40c402c9001068940002e00200c64100401c400d0700b0841c80d2a05401c80f080c00503503810ba01d18402010120a00740c180943c0010a415400140001400300c194001401181844200c0e00e440e400d90320701a480c01c0303904441001e110080b240c20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 53339913 1250 53338663 53338687
    0x1b0111030601140f0703030207060c11060402040c17010b04170604030503010509150d0309150509150313021503070318080a0c050c040c210501030302030412020f040e010207020a05090705 82
    0x505003008440846203022100d6a031201315400c000b01c210007098000c91283c003089114000d4455009031407510004c050b0320341d003410340d0b912400341c80030b0702650382c40d2040300c2058823540c00228018244000d64400e542d46680d81142c581c4644100c00c404200742c503448084401c003140c01809103405035220b6041d6420001002500301d0064080a0405516000100300c1d4642243c2010424021b459a0481918099030085142002100c0ca400c1000420512546640b00c2420140b81304220310405e032241d4070007410030800b241503e001f03580108158180d0f0424034101c0b004502c80e140030798003030200c02e079000e9440c0c45440c05004000e0543c0018003040708214440c40030420900c6c00307a021034061064a1021a040703410316040e88002860210302c10b840441d0b0000508007511810030108031540c95920000d44074003881c005d074003208040c80e01481c00c1d036031a444428401c00b001030040103045544408203000350b00900049001c0d40854000060b00c0c50300b9651030344103111b0354481c50320741a91a248 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 53341163 1250 53339913 53339927
    0x102100b030c0a06030504020906030c01050d02070c08070f080c0301090201050f0706060504050a090303360317010e060102010b030115090c09150e011b0c031e05060901021b0111030601 81
    0x9075094401c003402c0880e0743d95202c015100030050342e00d0000d41c070b04190044c000a54002400c1500a0f07001c1404a079081c2d0f44802161400c4241e85001625200b092130012440ea0076a409034489118114001c07130207166a1403114115507000041f03d0f401c82b61002410b00380c858201300a0b0214506100d4520a001c1c10b40044c02001c0c450f80e4005150b40d00d9a00240031600180d503000000780d980c40b0b008040540610505891000c00130f41440c0c40b201d811506281034460240001401d440c2c000e041c01014050608001000c0004184c00c0066840310460306009900b103420900643c00c280070162281411b1040d07c2400e144041c0c01d0780300074106070303881c03018140c10900d610400105d803000042c0e0702c0854080c185600304603980c546c03220007014001040d80958616800f001490210010000380032400d03628111390b80004199824007800c402c4a036800542d0300c0107050350042808004040b5019030040c01800c9220003041c072403036003251b01c142c2218010070800215113001c0010424560003985 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 53342413 1250 53341163 53341181
    0x3180d0c0f081b01060b1305012a050f06070503060a0509090a080a020c13021305180105040b1807080f1b0301090504021c05070504050609090c040e030c1603060606030605010210 78
    0x100380c1001d5000300c3c0c00c6003180c00300d9010900d003100c00304000d4003040b1170342001c0e401800c0134a003101c002d06035030b40002c0c2221030101607504101080342005c030420001b88540000c2421000607aa0645440c07000589280d104840c60b070300c50500c10340d000c200e614201000703d00500401004100754031003079a4004103540905694010341c45a0020300c49240da5015920240fa20501c601586401191071440407156540d00401d00c541e0a070b0042c2030001d0800000c043c11100102d0340071808401c040701207107440aa503250324481e08034040c00c004925800c42c1405028541e90f4038024001d80d03c61410b100340d40b0034a041c40314161020401000710380119000140c01c54001403209190039a40c518100018200110451b15508015420800741c81d0034440c0c1a0720040642e0241441c2c03405450f0240c840307641c102101d108644c0da4100f0707080380301c1c00c00c29204191600401c0b611494184140b648002090740b09c05c0303900c14240440800c45d548a80103a404131401030b001403406043d41c00050002d896044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 53343663 1250 53342413 53342437
    0x60402040308030a0b1f120b040603030f0302030a09020904050d0207170c090c040905090f07090b010e060310030209010617061008010501080403030f0c05040503010c110304052403180d0c0f08 84
    0x101000e1008541b0014034100704030b0715114006800d4842140c00c0682d200303401c1171446603140035010004a500049082c42c843c4c201c1c5001652651030706403500042190681c06500310070100c00300410084006050b0000803003d03000c0340c1c60266145448104c1170185411080315800c0f064501456003000b9002a402c203850402d4903040c076481c2c4107000b0481324126904203070390b030050010307240400080c0612000340680c00c0c01400704191410003c1c2460500c0c8083c507028401c004005050300c04142c83e014040c540c014000012540e464000a18524000034910105920403001c0346147c9089001c0d510900f201c0c0d2075203400c0d42c1c41e01e0019500041e0081054003810703141c1e442ca43d880030319880b1b06022401140c8545440f1801c00c5e06041c2110f80311044041030018000301c4603154000002a034040760801c4030601c0301071030103d24824000e00400a04c2898800200c28000751481d81c00c000184441d001c802c4500b101c0c040202210304894903030020b40703411440010040800e4010f07000300b50f401c0c0c0b06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 53344913 1250 53343663 53343679
    0x115090b03100903020a0215090306040305090409050d0f0f110c01030903050d0204120b01050d050c100504090608010203060f0603040b040f03030e0a14060a0209090c0c0f0a110306060402040308030a0b 88
    0x1180b02c580548054140450041c0c01c5002403400b18508048902d032032105100c212400c1c41919804265640f4024201405108004c220b00500c2d036a140c20507569168010140e070718928422501808a06580c81040d002c44d41d40346a401ca218410040350220304140001050805425001980106288901601003010400803611040c00a0000380020010140c003402c0001a81c1402c420440c0c068115501c02d8206601100200b040090704801d99242164500044a50108182d41c0f92041d035104d240100c0c184035000031444d4066000c0c5208200c01d90307070b00c0d03030040514040060512086400420f003000c0c1078007103008a4610410031024504c00d040014280310307030600c3c881c44c0c4460280202c508085a071002c1c040000103000c00364011038560800c1d400c01d6034080014004040085c01c030013003103101161482d90190104800080202d5690541e0020040b504110907124240e000d000d02070310924012500750308042c400c03101181e401422080c1103860b5008e03c00b001d410075281850b400280 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 53346163 1250 53344913 53344933
    0x8130515040c051c12080f0f060f030a0302030301150905090a0f0f02070803041a0105010c1403040911130501052715040909030810120b0c0c0303040f03030506030115090b03 76
    0x41c4400210400103a1084038580c485501c4c0441410b0b034410301170400c112445050091109418181c182c2081d2000c4200140b0741d61000401c040320040080c0f139a05220702555a0241900840198103846004200540d03540807503005071a490711921805802c683e5150005404c64586d41c030090120304000c0012580802184008059800c000802e803114103000003400b0400c0000c04240d41100480c5030440c11540c0750000103007403c54188800391418100c412a06400c0318140110340c00742c070105c40100038010703100e01d55015503080075814204070341c102200840c4642c000c0341170395128181c40c4040e282c1541801980035405182c554460b030003404070030042c007800c03840c24054400703020f0b44d41001034400704a080040c00310b11b010706001e024200918050040485c240042d50055410000301c200d180c8880d030b00a803030f40c0b08640211945001c0401844100040d034030051162034042e54040c401070303d070320040600700ca08030314402a050381810020803100e5a1a00601ca4841d8014282c030401d0366 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 53347413 1250 53346163 53346169
    0x207080313080c0901140402211612050c0901030b1c030201020a2601060e010207090c08040c06030c0c14010e01020414150c1005040c08030c06010608130515040c05 72
    0x4541d140d09101001d0020a0003030301000c0101042c9403104440042040d490310130105410002c269111340030f581c0019078a41c9036444030302001c8100e46071070080440352a2100e5842c2a10361110b0120002400e80d2107010302909140c0200d50042d4140c40215292000c1040190010316a007400a6003003c00343e0445400521003000381510316002c0c0c0c00160751a02d55400007000e441f0540301851280051199420040f9107109045056510504011442104420040c0e29020461f444807040600f00100400441d92001c8054011807084c1d03440309065441b010300390185c1c0c20091800000440440844001c204000044100e84140400006080c420305c51030b81c0c00c4e41d00641055120401300d00c02518a82464000d05200c058481c0c178003030804d141c4d10516900c602a004a108504d40c458000c40d00740103031074081c1001000210122a40c3d090607040d1151141c5091190501003a1150000b5030110601f8030442e46040d031100c040c11082040600c800074030200a0000c2d200d02d91400400720b8951 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 53348663 1250 53347413 53347417
    0x9030e06030403080f010801060305030904050a0b060d020a030b01050901081501050417010b0a0603050408120618011202010f0e030304090e010f06060207030b090c01120519150e0c03010b120702070803 88
    0x82c003d513100302c0c03141781c01d451003600180183d000411a80c0351500800200303501009407900000c0444002c2070b19100c2070724044c06041d0103d01107a0004002071048514102a4010904610903407418006010004010f50326401a05400b030b000c42c024200040c103403000710041141c40103050601604113920b030100c4040c9405044003029084c0e54408180e0a5864104d5071540180540d143c1440203207459a0750301c01601800101c0c402d81d800c1c400c0400c503580e40f00b2071071074075046059480c01c0056940e1040d015603080a20b105a020500c03182011084500ca50410051480f01030000c514147c40c1c242c801300105a41847c651003035690704020300c00c01d00d00d4001c00d802452654028405d841c118204168940009003902440e941300400c20000c698220008222209090b1000101d41d900d00e03900d81034203091a4030f0007426600c0d02085904503551007a200b42510740c8089641000d90343c0b1807900310280300a0203114691003045c46040300c4880300d140455070051032481a1060039544200d498555 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 53349913 1250 53348663 53348671
    0x7060b01090b03010e1321020717070e0406060e0f070e030a0305030c0a12060f050111010203060102060601050c03160c17070503150601020703080304050703060506040209010f0e370b0c1009030e0603 87
    0x8102040901843d504128640180103441c40103200e12b1034240300ea035524000361162042e00c580341c400180910206500400040c50080300c900e809292560182d510300004803807800200380344010504407410000343d0031441c683d042e10380c2480d50b01c1c1e402ca500417540213150b07804104030f61003d002c0320050b01401014000d045583c448000b07079003440005002400340344261110341c0e2050040010710380c0d0008500ba0000002c0c02c000c0d030348280c1a100b10382148244087c0a40740c40c0c06004003404c00c004039500c1c0048804188010580e0950303049e00c0c0b6101d500030701c91740e503040d80096409044a1038002c04650000d5050044620361566a84c4008007a00100c80079680f86c2c2254000f0010311620f0b005060307220754120703011880c043d0701d10000381c07030028000c58242c00c11032240543c0e10703692562084090051200310080001440e04010041402c500b1308001c078481e5030746c1d40c3c001120342c203840c1502c0248003110041c00e01550485440c1000346803003801581042485240c00c21a511400c0c011401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 53351163 1250 53349913 53349953
    0x913020c0609011b0e0112060b1804060902040e04020f0f0a0b070506060108042a090e070801150609140102011d011a03060c0706020f0d0c0507060b01090b03010e13 72
    0x10b0302e428070105003190401e840000b044040d1400300041d995000c08101886202428911000c0d48035004100007000c6a42245040b100b00107556080c181e1825090040803c080308d040c0511072f1140c0f101e200368001d52240304503243e080c8001c1001480c0500b0924401032000c0c10a6100d00707101400a51002d115600c40702458200048000500100740041c5a010700c086c2401ca00c0c0f030a26642c1e4911940108424a01000084054210148200c1071800081c001600c080c0604403c00521300c3e16a00e00d4403800c0d14a601e031544101458118a00c034900311056503d6070040546402206000d05010791035050441d50703981c42d410001611503220004450050000058844175603100d52464411000994441c1d40024104030000482808803104e450b4010009612540d001185c0d409034020548051440d43c1003040c010784d0664008040c03c1044c0c000d680512101e90794100544207000301e4060550461002c00c01441134104009c44243c01043e23901c40707811980802d85031010b00b090741001c0000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 53352413 1250 53351163 53351173
    0x31203070305010b0a09140f09090312010f0b1c0902090709030b06040b090c0702150304051c0c02011b020f0a030803071215030201080c0417070609061b03050913020c 73
    0x14040341d1601c961405031046460f8103181040303000015107200d0961140d00101c1080c0601e0000726143d00310120030700d4202800904e02400c0404840351281c0204c010607202002c60000000c40d02800c200c540d0480d1118280d02d0300c4c2214035414080e02c805400c442421403a2500d0609005841348140c4510a005e140e0f25032140c9030851802030900c16000c0c181500c21030038000d08000035a1243c0e1368a8008151110305545ca5140344040b40145e6034807003070b05085050100420052004c040b80740f040701c08002c1c000c0360100014038001e480d0b690070710341d010b40060240215003000d01d6201c1050700038580000e21159191018031f00180324803e90380c00413240f60a01000b823060310b0380c00800c0800500d03a0b40c0341c140003c50a84000310b8140c0c2244c80060b0401c203060010411050718081180c0192070307040d0441e142c00d840400900d607035080c1c502c152400682d04140000c0c2444c41019032004075040c2d68000240b0303103220f0710200d400790801c02619034000303804e188107107880c0c0381072004208480d151070240c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 53353663 1250 53352413 53352421
    0x30c0b1801050702031e011e02030f07090303020606060a2a0b010b0403031b020604030203030d02071a0106120f020405030a0b041203050f04151e1506110c0f0609031203 74
    0x1001003480103003401c1c1404414030078600180c1e80407980c4100e500d045d01c2e40b143c44545208109024164486100e1400c00b030981081b40c0410140e0015031207810b12490001c0203807116501192064214440940143c2042010551510306040100303600b030b54625041d00f6141c000c0c3c400c20824940c000c1c4140c001550619010100407a1503801070042400d583c0182c1803610b551006050440480c9520103550926004102156a0401034402540c0c026040340e480d21144a0407000940c84054207a540d00855a112508080001c8084d0305849907581d4280074640030744030080241200a492210181d000c0c0400700d043d8808000400005025252388009400c00341403111064090700d91003420141070808100480032005291a0004e80c0041c103000a240d0005a641c01420301c00004104070040f0000c151481d82190041c020b0b0300c0c103810b41d14909a03510f200607941c801d004c528100781c2c1d4000d01c0750030f8143c3c600b44d50024103000c000b42c0000c0c60440c032080081e061040b841c002558440002c010308c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 53354913 1250 53353663 53353687
    0x901060c050f0303090d11030c1f0f0204050d0b0a0b060c01330608040309030b01120b060306090706030b0d020409081b0106060503010302040518010e010b18010f0303050703020304030c0b 82
    0x82c00e1444802d101451039814a680c02545541030103242009014202a04021002040046640c88124a0190340c544510484035443c128403120810003c542803181c5180d014016101301c0d01180d00003840d5544502842d030b0b076600e50380002400020101c0c0d580700d0520b41510f4110081440c240c03110300019001c0c0010401c4c070088407010820034601407851046a10440702c8901c00c0e0180c0e040c60504440580e22441c04641c4103800ea0001800e1510176000001d03c5910010581c10892103241b410341140c0d6410f09165960f0402c032030b40082a0303c02c020400245010b644984403540c0c014010000090664003c039090b0303807200c40219100440000c04e580c02e0b00a40b200e0042d40c143c002c3c0288002c40c940700004003540018000a40f0840c3c0d20b00c0446c1e00b01d031003400c80c40f0052045600a110070341d02804814003d11124200d80d004801c514040341207002e080f2001410b942ca1000c81d40045415500d04035525001440304401754841000084003040c1010b003107100401410701180e0307498800384e0384 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 53356163 1250 53354913 53354923
    0x50106031527020103020c03130605070c05010c0b19021b070f0b0c06010918140709060f0503030f030a0207050f0a020a05090f0a0e1204060c1a1e040201020c0901060c05 74
    0x164800204502c070103950008500e4148044050b024680580c5828007600c05c58114841d00c2d420b46013000300010005a03241d0440042e0505034001c2c0b654507100c033340d503030010b4940c1c9010500040510105400090140907010500d00000404110043c1408148668001d03a4038610004043d5580070103c20003001405e12a642c018000c030911085c1892007010185994038418080c1440f01d9450700d04580061507a06080d10103140c0110ba00000c0c041e84003582615882117009224007507081c001d01250b0440c8620500701252000380056240158041c5a003001d5000501a5450180c080007c03501080b0100404003143e00a00050482150144100001110700303a00c4a4011400001081000405c19503001d03844803180c100411240d40c08a60142441c0082d42d100300c8210b000f15000ca40c02d5403054031090128450701d1584100c02120540d0034452000303c0d03408404802c1c08000300b446c0700f0802049070b049481070048914889100d0006803141d0002d030002c10004481000c10f83c140581044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 53357413 1250 53356163 53356181
    0x20403060b0a080c0d0b0403031104090207151b051e040f09051501200709050702010b010201050606070503031603020c010f0e16080717150c030709060905010f0e06070501060315 78
    0x14601c24003824081402c400c0110005406c6000a40c0003a040c18001d0304110b2a0b540c1d03610b042542c0b603172180710880094119090507031704d07030f0f0b621042850042c601340f1a482c803840300b5241c4601c1010402c0303412103040e2302420104620b418100804081314410001400c0502210501aa9110f0400001c0d9007183c00003000d0218001d41b80c41565400d9070070420221491032030b6030242c06640702500380c6a2400405901c01400c882c44c10701045a0f85a040d40400311240d0240d0080c085030711002d04200c003e0041220103060b50b0000c001081414550706100d04410701d01d81405402c0c07a0108c08038908554420b041e4500c1d83d511800c0303c0c1c2482005100a0040008401c4140013160415054035070301d850340d00030000c19034500d400c40380406104001500040402c0d111890382c92821003182d1006401c10f0310741c0c20200740c07030704400301307203d07001e15090707419a203040e0f5605d415025404002c030b80114050340b1072a00003104001a4000c1f400071300801000d140201050781800000910910403221980 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 53358663 1250 53357413 53357429
    0x120a09180e06090c0a09020a050c060f0105031501080d050a12090602040608011d04060209030a020a0f05010f080f06010f110105090c011e0c0209091e0c010909020a052209020403060b0a 81
    0x2814035131703072400d070060191100100016202c000410040d209032040110200303031071080d0070801c417000c03001d19141416500c06505884e0303d0b00c604200b40311105000c1c00b54584030740012860030700c070f50300c200058000c0549074500f88060704044034105c4222201043c0584645030001400d00030241c10481071030051001480b000484010a1000c6c4003802010340020091500020b9000c1e0b41d90301084a40e9120b60000e10b401c5405540d00070301da01404062040f11301150100c0c8402d0819401f038140c23544514105c0720444a244d49110044480400360202d540c140192114201c5046c103092003107603c64000d140080c0007028220002400505014014000030311b18800510805507224811401807541a1041c8000c1d440d0081070a0400070505044408001e8511030341c8400390300010990984a000c1e242c2050380c40d1030740186016841003410103400701d10200404000d5903000341c502201d00700d298108040564444041c4400c1c3d13070007036209440342d41e114204002e0500d0900d2003000200101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53359913 1250 53358663 53358673
    0x1203020601230d0c17010902100c030207060e0102030f0307030c0801090b01050406080a0b090408030a11070209060f0a081f0b1212070804030b0a050a0b0301050702120a09180e0609 79
    0x1100910040d0300802c1e000c203000f24215450724007044580d5500034060007122034904140c071818021035009003000c0c3c0c3c09902c81c040340b00f01c541d81a409401840c4945406038060540d1a050800070795940e0349803810181144010403001c1481c00d60300707001c1c60040c8030555001c81d442180040040c00800107820a503002460072422900301d0303070020100d42c03c443c201d0401d00e51070b40d42c0384110340060401c29400c0345c01040d400204001c01200b40000c40c840c075146c1c0001c08c001c10032502d000d119401424402504110410301091181c81c040008490743c0f00010003101c0c0c420384501085040c00140c0a0790b20f0b19440140c2107003003907412401090b038151400e80e403090722400409020b503618006114565980040010030030240940c4a0896004e581c01c4003010203d0f0810b80140c1d00104411646d0f4008903207405c281c80c00d10716040c05001d00601c050f5000340241800060034850a5019162603828031140000000744084442e00306441030104032400900c0b00036070000c4a0800800030100c4140d6006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53361163 1250 53359913 53359949
    0x1a16060507020d0e1e060d0c030903090905060303030a0f0209030d090f0509040b010b0703051603080609090d09030206030601020f06090c01030c020708030412080c01090f0c050a0e06090702161203020601 89
    0x1342c44a145503060100d02c2c1d0800c2500070030100f1301c070f4801ca103400c1001a0820320b22100158068026600311032084d03031000303030895642c104400ec0703c0302590302e80e41c103420400c0411407050f42604488964498088010b25001a52000034505031109400304003080000d90704004920444242d0030081405a0704020745117000e1761408644101400b4041c0c804d0808540201418820700c10395a807400c0c1c40c801410107180300d04019140240031142c0303600c2981c12200003000e244021800401d1001c00c1c2d2a5004400e04560030030203180c000070902411885000f1304001c920604105040c000d07a0306d00041c004004802e4001402d59015103844019584840810099410004100c40c03c80d0200c09640241c140c1c42d141c0010b4920503000c0e042d0b0150b00f44052482807140303d0345002c4505120b0641c4401d869911070034071200b0342040c440d40c2003201400c000240c0b90300700700c0710059208803103205455180001c0349031148044a15005200000514070501c42010380400070345002d49881203404215102c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53362413 1250 53361163 53361169
    0x21050f0d0c0b09030c03030a060e0c040506071104020c01150317030907031203110a02060618130f0804090e060702070603060311040c020c03100b180609011a16060507020d0e 76
    0x21140c1d60041216959800088a125083c0103844c1110705000c1501c1c0c0e2414604040d8001c3c00c4980180c48402c3c00075404201c52080110440f011a44d024002c23500f01749480e00d80003082c44c03404a103190415002c1050040c1070b00288a4401c02d4070504100c03031411401c5081008824001d401c11a00003030041041c0410700000003016000c0742d602143c03406050448400850150602c50001c0c0754041010480c58070040c1c010890508c108401d840090f0410007a41c0c140251842c00c1c4c407444190702081c5400c20101c0c0d00d48103010703c4240200500ca10f001d0341c4290311011238900107148462908050b080c040e04640c144171a100501f464070b424442076085032160b00340a9040044644a00d6a41010003070f400c1c0280180c9401400040a440c031506060408801802c10080d51038426500c0c0c80040100b1a4428100c9000780c0c0c002e010400c0c81d80c28041c5c10440b44502e030148100c001002e03c01501303412284ca0381440d03024895600070400d8101135034007a280602041862040c841080041d80c3e10391 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53363663 1250 53362413 53362427
    0x150807090203040c291603080a0516050a0e03150103030908070b0a0f0e030f03030a14010e0612070e10050a1d04030807140309010207050610060519050421050f0d 71
    0x1d0031a01680380c504c60800e00b1700e82040c15101d02c203511801e02140302200349200d4504104028020740303034126960b0742c41e20000103e541c05c481c018010b001c2c41101c4a1620f00c02c1d0064010380060b82080500c120038100000e10b0445d5040f4101020f000000c01441003541c03203603004005100c45c10040c240f80c0e041c030313071130110b035000348001c04082049544190f1039a902c83c07000f6981c550784c00b0301680e1616407550507940c0ca84c0c0c42210b0305603489042c442401c02c1c1c21110503480c0c1c1201e47d81d41116060340c1710901008541c04c2001c0110a0511440f48080b541d16030010380b1500996440c00140550740ca0a002d2015410103507200115001000f400101d100c81c1040f103213513115a240c070f041c00242e81d0741c8c90700340c1d250000061900b08101d008403c01000d05015070080c080b05004008941e80d95840d00c0032245510614015403002500910081d01c0c40548424800051000fa0414a0415441d04a1a0815155030004604480d500c01e00380c402d20009000d04c2c480d10700c40342e01a040511203200050005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53364913 1250 53363663 53363669
    0x80403080708040b070507080c0d0b040219030b07020f100c050d09020a0b0714010f0e10020c1e010b0a090c170405010902030f0d090b0a0c060506040b04150807090203040c 75
    0x32000068900104419a41210060100f101220b5110811801c10fa5a41c034038900603d40b061090103126025460121301c0c0c803090550041640059941e6a82884081c19080c410501d0315000303044048001855500c669100700b003194000c1264209010405180c9001d052850b0b0000d80b03810302c880300f515400400c80d18800901ca0b404247c50b85a4030100d1410302565001928241c0081a240c0410194a049680c02d08540c0001c0c0a8400c44d151504102c9181240044941d4400a01c00f04549403640207405500d0050341030b68025038001466001403c495260802680d56500c0c0d10440ca242c0214003d001d000f01c1d5408122040c58800b010340550700091001c40028078010000c4d040210941020184547c043c060f0380024510010165942c150403094034042030000034046000042e01080e540d0610042d552140150095119336006201c0500056006501c40c0b41710110381c0c9507401078548902740140514011031410468604020040d00000c811600400512010420a80b0341c0300503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53366163 1250 53364913 53364923
    0x6161406010f0e0f070c08030a06030201140307050316020709090b0a0c090807062003040e0103120c0201021509010b120706120203040f030810030c03080910080702070905270c01021207080403 84
    0x60360705c1c2c56030107603030702441d03410000c10781c40307002080103440580783e00100b007164402e0700d0303010949040c005850980d000c21640346000030414000074900c0180c560881c0a05c2010307005440e5459190307950341e003e650f1400415240306d242ca50920403061610310800300840c0381440d08044c40d1382007006094450381035201da072007007000741d00078010700401c2506085044103000003103d80e181d40e10782d01d0f9070a0102c240720680d103107100c103442c01302c001d4040c801c44454160305a0260602a125a50400c14000e025003125a150f40e5188510f51540341e9604121b040100c0e00000c1440528203c0010558201e07080b40110490040c414030001400f11280841c44a92500b0303c180566500c0c0300ca40302030a8180d1002d800030301122400000d00204100825030752109803403454000c0003000c020b5075110b105940040040e441100d0800444400d07030b00c034582212a0107000b01e821110f22000b2600b400a09441280c00c4d00b00255031221507030104903820390000d160081c2420140503440f207500354040d07407201a00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53367413 1250 53366163 53366191
    0x2150306090f0703020f031306110301140d081b060402040c09030b0a0207080906030114010306091a10030b12100c0e0a0303030c02030906070b070210020c1b06161406010f0e 76
    0xc09004c0c0d01580c03050781c407203600c280e180d00d450105601d625552540917120346242c00c8154031568500781c100e0703060310100c08901d031080c00c528040c00750b0509a00425034002c00c05010050720826401106141174a40c0c0e0000e100609003401000110340c00f40340380c46e05000c05200100000f416201c42c1030341c03001ca0000010f032181001d0900d003002e03100343d00009600410010021403a00c0d41a03181d94000402a41c04006103501d810040f81101d181c920a0410010302c15900d402e10b00d170803601a82c00301100d19010036010424004920340420030b0010018135042501442502c4100b44205094a00c4518003a44001c0303007034000c1503442059000140405854883c403240c0d181c000c104942840d04054100e650701d04c802e09080d100550244c3e003040050241078a01458442d2600945500c0c203401c034094001c1d00c40100001e0a5001300c3d00203c1e0304408188030013681040b13800b40c0b42601d24007a540013481d541240c0e000300d00b041016045000c005004140600c03460210421555001080c1c1a0100c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53368663 1250 53367413 53367421
    0x804020d060c02060f0c03070507080d0f050c0414060909180114070302070519020a09090f02040608010e210d0b030f010f0204080706020f0c101b0f02150306090f 71
    0x20300031560161001d4401070420030200e80c029400100c00d0311804000c40605203a48a508141c28184802d07114240096028410340000c502100010201c0e081c484d000010740084e110711400595200b19040a404200400d003000340168030780700d03140da2802c00c035042450042d020000a4207100040d02c000291094801e0703405180b9804d602000000000450f207002d5441c2800c1c3c014041c0d48040c204803101d00450710a18001d010744802809100d600814800056040c0031181c00100351f041c005460301c1041d01d48000141c0c035103200e4840981100310001c20360100c031244184c40d080e135041d400591a540300105544441020041c1d8800e240d84540100e400305030704c400a403500320203141e00310584d46001050701940403558000d0040724125819541307095a6000c0c2a07071106140940441e050b0010307020841d152401c0004041c0602560400080748521110120200000000c040340c4000101000400790302d4003680311030703802c00d80380c1555285140560220f881800c0161076a0150340c0000041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53369913 1250 53368663 53368669
    0x301030f0c0e15180f0408031e0405070609060216030803040c180b0a050d0f0b09010608150906062b2103150b0f1b01060504090302030d0501080f0c01080402 69
    0x10a0041c101c1169aa80d1400d2030581e200002000300c8106128145070180c0e01d410030110320f8601d1040200c0400305000396a0f41d00c54441642c80100340300c1500300d412740141c910301c5980b0040c0f0301840c0600010302c07072981802c9010304515a960040c5040d507102006441c40c80000082901c1941c0d23001c040749480352101e24054091214a800003031151810340300d0725980d803103668082200440d08488440d0002e41c0c807810300030f4a4040810190003000d21408030401304121248079034000c0041000014141e0355509a1802d0030418109903002e0300e1074074188041010100092900180100c401421555520154181200540d01a0340b91652046d640034140700003100250040324152100903100b04400c00004c004152400303e40748540585507011510801c280705580c48800c1c983d42c01407078501111304482c0c01900b103610074041c942d2200c0c40413800352100e00030154501c1c800e400039a11079603449499800d1300e00c16004001035078003442c0c070300120600000300b00750a00c10a007003000b6a91580c3c008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53371163 1250 53369913 53369933
    0x30203100b071a01090e011a01020a06150b030f0a11042105070504051003060f0506010e011b08070629030c040b0103020403080a02031b0606030d0e01020a060509010c1808030301030f 80
    0x14001c3d041c003560000051054403a0022000c408618008100d400e5024a07088c49400b004900503006901009400000900300d0703208544407040d0f130380d0080c1002c1d82d8000a001035403044500254010080e0140306800c00300c1d0040d00d0f030301840c45040600b8941401c20181d0060710a021300f040301c1040108001c1402014070402c4050f2002620a000a290420310003641858502c0126115450821103444698503841614060340e8141c2d2608004002d070001114000302ea850323103151140d08c042000e000600001c000300b01151003a4000700d051244024520746c000d1050707d075404540c69203030301400319a07008100b806145400700c60000d528207800c401203009005981006044103c00505601041c1c2c002002e0305002c0c4802011411941c001d02030907841702c1c016140f181e096400180394400c070500410034189113072010b20458041c503140c1e48410090b40c4040e0703201003103a5907420f068240503600426a0014a03100750210100b103103841c1d6a2070392480144409401855180590820000300d006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53372413 1250 53371163 53371193
    0x10f0309110a03060606020d051201050d052b0f050a2307061107020f0d08040315090b070f0e030f0312070212030c09270f0c160503090907030203100b07 67
    0x402c00809035102d203441001041c403405244050b1241101c0800c0c8a441041140c3c014002640380c0c41c9141d290034244200b032070b01040100c42c10300400303500b0b2440980c1c1815803e20320441c0041e20b951702d4542600541100e508003038080402034204032264840ba004420130032188210801311030480340c040f010080314081c50000900b1a410702c080140b59a2030304000c1c02c1c0031703402141e184481040360010080907012a050040242006001c1000864070340d031000c00c0380382d00354080421340c0d010310b030750340c0c00e82c003504448003c00300e160304425110705039000d01e0001da954810f500400b880441481c1d020303a41e000d13880404c80c0070b40c0d2280008100502c00d00402800548400c2140e48900340f40b817661800b81c0241051034000d5080042c00c80c00c1c000824020b0444142c2620580041d0302c6504034040d41c14002481c7d240e00e01420000c800540e0035202e070190782240144059078644080347c0c1000b0300d0800240480c8200b50050052029044d07200114000302c3d14031007452562010b0074070b40300136071985000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53373663 1250 53372413 53372419
    0x303031521061b0418150b071a0619030b090a0c23010201020702090703051f0906080c060306010207050d0302240405010c0c050607030b040207141501090902010f030911 74
    0x140501d5040e600090140c0c000c8a61030000c0d070902c0b0f0f01410101e502d00a6118070403554038001000d1000c40e10541c0510000c480d406c3c07040c6051519407100c04019440314000711500c0b04951895800c0c042c07aa20050380000b001c40e0341d07503141200031042030741d0421030f400b01510130408240411400700d0f04019002d599a0310080c00510155903032070300300454081c1001150182c48201d50441305600c103108030703003416500402c0b28110f9101d41c4000c400518000b003403a4205480e4542811458102c04007150007085c03080000700701241000c0c07041d4107004452199a0041406005003c0d0503138001c284a02038910548803403264503107904040f0702e007000c007002503c03141061140084081c0e62202900d407040780100c000388540d00c90702d40200c8240c0b03500c060103401c3e42c0244001c140350500c03d4110b04c20b4208001d10150a00c00b40e82c039290360104a07891280695401121040220000740412500428410600b003088021035000030f890100c0a1064400b05640c030f01102c020045054281940c0b6103010f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53374913 1250 53373663 53373709
    0x8070f1e0b0f09010c0b0c090307060203040b042601060806060f010503090a060b1507050c100c050709050c040f08030403140708060f060a120c180209032a03100f0c03090203030315 79
    0x607c00022079a8000805640280240c11020a2250000080b50110b814070158589407501e481da02095010742d18020254220f003804800c0342c100024014140509000d10103010700303003414801c02034580540c13000e450600806004101172410081901400f281e0014000304140b048070380020f02011071002c00f902242408030740d000c144900010590901d81c402d45d04800440c5a1180540d400f501400d0700800960015500784421250ba0700065005410b8410140c1407039140c01c4202848030494000e9249507001280800034010b44010200840754403e000c1c10445d410076076055100c410007441e0303800c1044107074041401a12540c243e8130007000001074004565201d4078041c00b807032107a4464842c5950003545c446400d159035200303c3e0b0820300020018582c0312a1880034014050404e2400603580c3c107120210305640c0c80c24040c3c1c08a00e0023088000070082d170007044000442e4074520401040500e820b003540010b0301c0c0041141d40262a0044144060b0300c00400590381c40300a00c89083c440301350b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53376163 1250 53374913 53374921
    0x705090904080309011107110d15020c1501061704030503100f27020a020d11010f0c0207061b0b06011101090c120c090902030a03050a0908070f1e0b0f09010c0b 70
    0x682d4000d1809019180b0081c0145404284400128000d402d00a011a01c0c1040c0021251800c02d89400c0c481d07100d52140c07005207001c0380410049802049400f4070582000d00c40d500740900c6100382034054a0030f414180c240c500725500c181c82d40000100010144800000031a17056030451804000901092003070390446600c82c9049a1881050401036510ba00d0105038580003038018000d0351035100d00343d4000d221200407214100d550b54144c0c0d030403a6a40d50f07500e141201c4250b0601610b0324003081d07500207000041c50644000c003080b41e442c00b461480f0070440e92000000b0740410071306401c00f0091030800d5035500e0074401c160061590340c200420341000c1000009512200101994045001e02840350000d070755408680169000700000940c180c10070344040000074003810240501045c1c915003040c65036180c02d015841c010301e90f0002a2140c10490081007101c01040145c520b94248807034825000b46040c0d04003c4600030500111221040401e9820141e40301c0c4200b04c10503500f1442150361414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53377413 1250 53376163 53376173
    0xb0708160203070b0c0c0904020f0d080705031602030d03110f07140609010b150301050a0339030b010b120601050d14010e01030b0c0715020a140d050f07020708150705090904 76
    0x4080c0c05c02d401d1a001d8418440d18614010580c1d81c840c1d074001d040641e80c2c004a8041144000119100302c500341421700c14a00440d0041005c0d04480c064144c1000e6410180c0c0101480e000140304020101820500d940300051040c80503a00111910103410b41c8405591511030a00440b82034200079038425942044000c520540096800c8901505e68030341b003521015048410b031109000d0035811141024040000a540088410400200c0c2034600c40d0580450b00b02c01800102c81d1b408414851100f0042c42400b01258078640101082200d55180c44111015003504200042116040c04808200541554040c4d0002640b00c10960880441c81d030311060000c1d200d140a0200340c5d18240380c1d40000343c1241c201401c03a40003a0304034030458025110107100c58041c0d0301401c0e40000b08514520f070002c050a103100079240c02640d0700004a07882c1b410401165030108024801001c55101010401c12140081680341c030b007007900d0a000400b691518002ea80a200d000b911903000f820350313001c0000b801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53378663 1250 53377413 53377417
    0xe0f030a060b0a120f080a051c050912030609060d0212010606020a0606170709020906090901090c230f1305030d0207090501050405010303050d05040c2304060503070b0708160203070b 80
    0xd4101c3c0c0c0710180300d864201c0ca80c13840655031002002c0342141005540401c80200261420f60428a0003d180c23501c0d9100e2441324845140034260040d489805100e4180c0040c00078615074640c002c92107095252400000e007400c40064125402401440c40ca02c0c1907440c1d0040700840d40e0780034802400490780e5004c0007581e490702030308241c0780586040130200b510b0344a8901864640003020003020102e060500460003940108a000c1c0e1000d420080c1400d107480d40500075000302080c00c0700040040c0d40d010b0207400c207009100340f5901c100c03003040e00c01c031151604400e4034161022843e01030b071112411175006622070141c4c1c104592510801135008401740e8000360301c10584000e54002d100e0350766510107000503200280001004036005200b4103c0380d80a9a000aa01c00d010301c10700085250381e21545022014481558800030200c02040364160802c2c0c01000000c000079001000f01c140703092a060403078002e10030020b16814000400d0380003208004003200324a038000382a21400350351403181035816 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53379913 1250 53378663 53378681
    0xe0603091b0306070806090a020d1e0e06040209070c0305071a010f0602010c0f110a17030105030d0c05030706051e09060406051302031b0402070602070b040b130804060e0f030a06 78
    0x11141c0300400030386034180807580320700541c0c00351140b180301c2c0c5035402000502c42005041d164025401d0141c1031500b07245024440c1c491442020207041e484448000c08295003800c00d000045520010a100c0140c6850b929294487e6041c0f1b04011800950310f801c45951091140140100d0b00702420070000c2c0910720107a60484180c0e21800b100c01b0340d01c138000d0f400d9a807050300310004034a0a4514103881c501409054004085a00a0790003602e0380b552020340f50411000c02000c02c100c044014099828200700c2c400754211981040e014447c126034900340d403440380010043c04240c45030f010401e015282d94402145034010902942280303032002c100c07035940c082210180c0b051800c2c01c0103d98103081da81018501c164005c6d028203070400741114108229240704907401c2d0426401c010781c40108035684041c0c4110b9210350b2040600c0d060605101c00f4414000d494151079009480c03401d0002003582c070441d003c840c004d013001d900190848001421903503c0040840c1c26020b00070740c480c10844154031103104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53381163 1250 53379913 53379943
    0x5070e06041401350d0206010807050604080615040b030312040302100e060a110904060308040306050c0f04090e0c120d020f0c13050a02040302180a0506060f070b04030e060309 77
    0xc20b6684541c1c110707a0402c01c1c031a540a280802c10341138804450300c580ba030220740c011082c00011001c044403543c6007100742203000005801c90001480240d0082c00440028001100c68a0500341410340700c41c1c0341d80c009080b9080c039000c03c80d8a0842d07a103c642110307a0005005058a481d554607011002c00e0f1002100c0031001402100c011103404511846400006048100141000d64450b070b54038004041030303414013072041414007035154196194000c1c0350185100d1680103880748d01d14034248041e58009031201c0303803c860501162090340d24100a07501210100403000c1071480b40551f500c0c0c106241031141640000090038181c0c82c00000084424030800541d08030b0b61010030f4429a0b40e141d00100c001c0b680d000d42020055014800079422003900322542b40d40042c58696030b035001644012101c0d400402d101281000c00152259500c155030f80810143d542034a0000504410201032054903001840140004081014107101d554600200c401c0074010a580742040c074002e40d5a80d6880c0c400c441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53382413 1250 53381163 53381171
    0x7080303041a0f01030b0609090106080d0203070b010f0501020619060801020a111c05090d11031e0d0c0201020304030605041a0c0301090605010302071110141812010b10080a0905070e0604 82
    0x86203443c02e80c0b545040342e40141c0c02c01c0b41526910100040307148003600c21811592140f5000c10f081c0420300c070110005245400441e61001f1900c3c100c0013104050f48810007406034203c0030000c590b004910150300c0415040c0300000080506000c80042043c5d030468074030b035071001c51a100d906802510101044410104441c40c900c1788521000b2103802c541e40d0000011170500800f485410100b00c4601c800e4801c540b20000682c80c1030200c1c0c684454542d440029211100014110060038480440b0790209445d165504d160b02e500040c1d0b4a00c41c074407000300f01030350345e00004007400211000583c10003900d602901803410980d820f254107800a00902c1e11540c60a01c002850b50b00a03c211001c29511120515084010b001002007181043c0004420301c1003090045141c0d083c88401003c0350840035801a14410101d81446207200c681010a078030780c2e240000c0440c2c1541c40d0445000250501d2401580030341e12445c8078000707010381d401c0042c09446500800302e225103000c0f41c014891038080d50100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53383663 1250 53382413 53382421
    0xc090c13060c2a050906060c1507090f060f23070c06120b09010b0d0e0f01020703030b010c20060d140a0f0204030f03050304060b0d060515030106060e090907080303041a 74
    0x21001d41c20103c6942080340180030070000b6003414030301c0980c0700c0300080c031250420b00ca100e030480c1040300041c001240e01c4560400c2142030364100100302e02404402450002180c10990041c12103402a0350303141c24070201060b40503040c1e2a0f50007200083d2440c94440d0b4940320103113451130034084c0501481000c14901000540042c15621440700211002801d40c01181d1810202c43c84661265146400301c50700c500307114040031800c100544503101000c000581d10750080c14010100d4242d40c9a550401000000d16400b1820400d0300b0340b01103000000c5c840044103030074000758070f0344100101817075080d0420080700034111408062a1207517001000c18049440d851000c60b04a2043e400010b10703001d084030101c00828418809035501911030080014690601e0300055801607581100321000d079107800410480c140b0742403841c40485d600f0340080c03100c40d04181c400b82c0300c052060405409101c42c0c80c0000c400800c00c014500060200340b043d290ba03824181456003c81160102c0c0000a0990502003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53384913 1250 53383663 53383703
    0x3020f2506110a0c02040207021c080d0f0203040210050a110601060908070b0304051510090f1a041b03091a07020d081f090f0209100305090d0206090c090c13060c 71
    0x112103284003a51504131010079642000029003205505070382241d1090f01d031003542e49490040c1d0306224014000c540c0c075154050020b0003901d2303081d0074030183e060040c0103210041c3c40c5c0d0042c0c5407807841a414280e071111103a007011626402030076200303005442520000a0750a0f00104210151904c060075a03030344a850303420049441c8002e030307002046c980c400b4404582a5200d07802c0c00360420503038090000983d5480801805032004040180c0e50f490351408000c00040384e0318000b01d40c44100350b500340304899049414200b038500c0c5d10302c00818036450300040402c0152049614100300c404c41d00c5035035581000c0f40029a04c07217402c010700011460b4071000c14078601d01102c5d051006a40c00140411150034034003614003601c141c40c100071009400703001c3c0148941e1074002c071400d04445964001910700d008410030b4a13203100001031009640091084c084560310202d916034822406440c13620042d15412241d41740f07445842c105202300d4170710740001315880740d0000300b031001d00e402504150707500c03000c880c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53386163 1250 53384913 53384917
    0xa05071107050d030302030702160f0f051017070201090203060a0504020a06050c03030403030c120207050d08010b09030c09090a020a09140703021c0911060a180b0307050a03020f250611 81
    0x4031584030300031107103c10019120b5001164040ca8600c151044200b1100d2450300400943c1c0000001d40c18078001488101c2d045180c24008140407600e030003068001d402c003e054400c100541c43d03522a5804006860b2a00175002486e555a0181c200c40951601c0340000700200403d8804074070179a1200e000003150b601c20401d486c44204002c0186182d503c0301c1d40c0c1507008042d01d05503402030240c001c0d06c0354100e200398409800c080d8082c4010f40003109449500030500b51050b000305089110a01412441e924001160f0b80144019101c0641030340740d1440d154940415010002e51180451002141d040c40b607401c04e0302ca03050b07a40182e170032948036407509409a020745c260064039050408001200c6440ba074103c00c00e40740c0500030551042c0d41c100d01050351503000001090104640c0710707a2100b0360301386600300c42c0180500a903032800d6050140c40100303103224850310702007003540116400c0c196038100d400301c0320002d040201108160005850170702140700b2514041c0d03200782c68820320035110604d03001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53387413 1250 53386163 53386169
    0x90c010206070f090e04030f08090613060509070f081006150e0d021503010f0e010b070804050607060216030905041b091e08010e0601150e010c061a090a05071107 71
    0xd000e41d80e85030742c030403118160000f441e402004804000024541700f1600400d01a600a0340c2d00b040c030308080c2a000d0002ca0f000341400c2403d900a104000404031041104002d072540114081119101e016007240b40001f650016005c072520924002907ca00008205401c0c1840b0b50701131041a40e55145440071074107810340751000c605046943d01d1035103820160031402601c000d0500030000e0102a01d02d045070002d0f04014210000784000780038110509150f140184030200c00d01380b520845a8411100d03015034451a0f0041c6c1010401104100554050711035090310700804451000490500800044e03070b5101c0c50340641d1804003480c806529010015420541e240c03107241002e460013503440c5501c1040c000d800b285642604010030a07180a01400081800c4500281481d5040c508905402c2e418203240c4010b100f0317041035904c40b690704040c00090fa15000710300012580c9000c0c20b5091207507581d424160380106003e00700000d481d203940c4054000d41c95941e51079a5030310000e0f0a20342e9190f00d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53388663 1250 53387413 53387417
    0x806010503010e0a020c060403020f1207080706020309070b0c0a0b06040902030d0f2a05071d0105010807030204050d1a1305030306090402030102040e1501080a1b0c06020c0a1109090c01 81
    0x600c004120200d103c1d030060420300006103030445a542c03447c00d0070820340f0210016005101c60b649000010092101c0070403105101a03d840300b21794035110b0a100c1c2181c010252070700480003884245007842803800600d90603c110703503220105840e048d21592100c90407645080d0072400b00301c15050030301c541c903062503015000b49025807441c0403ea5000d07031190914001c0194004d40080200c1210180c60300d40303040f05143c6e0407100c28a181041c2030528036086000d40008480301600d0310b0360500703800c80c11900c003070914a200d51120301d001c502a00c201e4101c29004900790001400300056035000f9460007032012100325050b104e040042070082c10100024050798424008036400d45003600400d03070030901c01400140741550f554880c0d48481c008861260342040302d4a4042d5140d41c112024692004903030704104504c0d50305140459448140c01620b90410105000030020440c0c203904680f2008142401c41d0a114076501c1c00c035144d40320381030700a4041c0c03200402248601c4030000310203840300416 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53389913 1250 53388663 53388667
    0x60106022b11010b060c03031005010e0102031b070f030308090c0109140f04020702030f060115030207020d08070303060905010b130b040303090b07050a060504030c05060f010501210e030d1b08060105 87
    0xe640031038101c0145036045416560b10785046085645e800c0052200342c2c10300005e16100c0c034112000061042c0c0d658080c9040c000100752025580c2c0e8048112038407146c8040d8800c030f01b41c054804103450900b458010000185a001e0007000385600401c02d14071600700c1504603501e9079200743c0111100003051040440310a4200342c22000343ca40104451540c040243c40181040c800380c001900d0b000d884000349005401810040c030a1600e480304420302500b00d03003410b42c0781a480c0d0b408201d15075195040078182d10300200712941014801e4001c000104203840302805996110001c9030b9043d88214640000d03070b02041d10000d4881e8050003a20202c07034050b260506028501110029160722541e0100c625000d00040100003172460700c5514083c41c025614500c04803614a4198070740344010302415002000d4030010040c1c0c0e0ba1012925000c00203a8103100e0b5480100700c0260701504447c0c0c480002030001090f0300c0d074148030301d0b4482e60203055103400f00301c1034590717904055688100c02d40740c1e03c2c009082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53391163 1250 53389913 53389993
    0x50f070f0b0c010213090b10110d03090f0605011e0504110a0509010207080607050702042409020a0201090501060806040611120703110702060d1b0f0203300906010602 73
    0x400018003600c000000015181403402a94041052802e40080f04555510b00c7d41c000e01d8205401c0810302811030342081201e001080c0c036001e6a80d0608444941016115041c00c0e040000c140c0004030102d510000c14000795031208031701c000c070b203512640e4440b07020701c8284001aa46864040c4242080c20744240c0b6180210740642122203074000b61000d810b501c541d800001e11654200182d41c842c440070f550b0251030705aa41f04100c2a1030740803a4030a0002c40301c2c0c0031032082d03890001d107103003c844000f1801030751000c40c0c140c01d0b1701512031400f010300994070740307a000580c0c3e040c003250380c500c2140b08038810805002940d5580c1c0d0680640e00c0101d40210300300f00050145406984540d4544004001245c1040d0095000030200d03403083d0f012514041d111075003641d182c82d000080f241100110b0824581009440c48001c5d03407805101610704100c201e20048180f022400b51b0317a02d05100300c0403140c41c910b1500c072016655404c4284551401441a141003048075130240c0161020301500001100040035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53392413 1250 53391163 53391179
    0x90d0605060a08030309060702010605040e03030a050403111f0c030204030b13020102071802131a070f0206070507120308060108040b010501080a1e060608010b03040b04120201090519050f070f 84
    0x50300a0000350402d107003500c085200301c0100099482030100e00d00814561500b000000d0968106030b0100f4015420005540c150100c08015268040b0400c0c0e4001351039511410b0842da00c0f0311105507100c0d14024550440d94030941c150b4004003000500c41c080c0f08590000300101c1c200d104503c030240c02c101c588408203100402d05120403029500501c100d0f0a816110740c11141410210359546022560001e0000c1c80362418402e031000a011144915440b0101c07429104400d02c02c1c6c100080108004194680440da00d00301a680c0064100081b5080c651301c84404050b4149a86000da010591f65400140658031800400b0311540e84406441da85d6440c0c04010b48402c10094130780704c00d17192110019100442c0c03031080380b41140d081000c08280300b450004007400840040c0c1001c00030000400030003002c100c07450742003038129900c401481c48842d00c2c9a012401880c19100091590182406003c10f85011003d0504074901030000c0c2d41c803128510081540c0c0700e40b03510842042d18614401046501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53393663 1250 53392413 53392421
    0xa0201270b0a12060f05010f030c1b050a0c030501060e1501020a03140c01112d040b07031e08010f050405040312020d0b0d080d060b16110109050d0b041205090d06 71
    0x1509090340c0d84610025038a0544e1403e4024020305d202e088000c101669120003501c444440900381040b1038003941000518044400d0801031828425031b415408100040150381c82c01034000e059014669240e10b00756001c1d14091058003099505400468503d19040b01380321000e04058005003628022a60151280b042021414845c400107000b074180c145000c2c069840245000030704c50b81e13076410b403201c003d40c680700c80044407052440c20320900c01c102c0c812404840c01d4032050300340d65071a0311440c50100e03280307810855048074040c4442401d00400d03410241107410b940300004400b031501e481ea814002120300841d400f50029a551000303480c104030a9005005028000c1000700700002c0e03c1c4003080300c40d0310103401100d0700c9600207050b85203a5040e114010290016102440c03400d80002c800e0f41c030450b0381d04806480d8010b82006a1210303030040c19541d0042a001d0301c4080702030344e00d0402040c1c40900301c1b003d0b03420040385240c40201500c2103044502441c00149198881450350310356038024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53394913 1250 53393663 53393677
    0x11150c0405040e010c11030c12030606040b0d06050328061e0603031d0406050d0b19060801090308010509070c0602030411040504080406031505090109020307020c120a0201270b 77
    0x41202080041515100d40c000c2010580c80c410000c102014421030081001680c1611800181c00500084501c1c1c00041203103c0c50f507401c1240c840d101c0e140c6070700146007485590720411509800141101c40e0703441c0f5802c035400301c500031000d0381c640c400441010254030510450240d8454140715030a80000d00d41c3e40a1002580e90038401e07108451224110421a6295002980801c0c10504d24000c0302320344d219442403150054909100580c41c01e40420510142c101d801850300301e01800107440d0a0304036404241a0100c448140001c0d507031103085600030322030a80c00b1740000c0d0310b800000c103c500b002c0d84100d02450003965503000880444d02c0341c00003504081c000f06c80501500403182210b03a941d000d124010381c0a9020340c0d0340e8529140014040b20705480c0c03400c40011428070308008035a904100e00d41190300e0f183c0c0159890303981e50401c030b0404022043e0190300034824410a0b0a084001a40302c4002d4400c0c1c03240d606000c06620403800d0f81c88984401c00340200104010700010901001800740 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53396163 1250 53394913 53394931
    0x250f050621010603020d0b0301060e270a0803041406060a0915050901060e1f02031206040902032506110a080c3901030b03060105040509030403050303090309010305071115 75
    0x544140072441181248080c0d001600198002c10480e042010500c20100c0c1324400710004c205a502d484003801503100020003030301154201440d0701c40c01032540c80400f041c050040017038501c01c2056181c84601900252400d44a241c10714000300328030080083c1e254020f00700100040d10700752419003110041c215140150854940f103030400181521006900f502030442600c8030408074510b98140039040001240340240070f403094554200941d00403044442030420024800380b42ea9510002c54060700d00c60704000d4041c42901002240c1c022300c20308008481c0720003c00040c0590b5924400c84100041c005119a65000403964000250f41c52004024404c140b9060f21a540c1c050300303041102040c0380e008420450151141401d00884640004108010034202085401e030f40700082541c0b80414040c8a0080395100b0105a07002001c1064800540e8444110f0f91f491800c0c0701d0f03880d16a084895042c0c080380c2080045018a80144001d0031b030f0480080092504502d02d91200c451090058800c20f5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53397413 1250 53396163 53396197
    0x30f010e130804080318011803020d0c0312030506090603010603020603010b130b070c03060f0606050910140f0c070e0c030a0513060204030311060a0b06090d0203010b090108250f0506 80
    0x140700c0b4000b5100034800c000117580c60308070803180c20307410805620540e81000182101440000a26407610341540d4054a4000c01d0340124a0300c160003c1c891740002c0d08560501c254075410b60384c1500103e00c5207c080d14a0740d4551913075002c1c1400d0307600c5804000c1d40b001c1c040c0011f00c00ba402001c06801001c4a03004181442940c0300190b00065109800540d50403501c21030030f20a00c0b00c14002e00d0004021400304201991500400610a002c0c103200c1a114401d00b400e602c1d0014803c8242e40800104024000e0f0b0380d506440c460311059101c1503044425000e9007a0000e01c24088541d010b21500c0700a403c0d500e566244580c2d04020074000740b16069140814940c60b001c500c451000d4400b541c17107500c440182030011340fa9a8501341c0001c200d500320074288a80081d5070b13190348041d40d4003e6000c0e641c0300310b8610130b03100203409491340540454000e80c81d08000606080c0000c0e00381e11100d10505001698600c0c2244171840318094050084010304540040125041210062001e00c04c00c440c595 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53398663 1250 53397413 53397451
    0x7060f020a2003300906010f06090b040519030203010c091802040506030c0d11030f010e06120304050607020604030b040606031205190c0201020c0d03020f010c0903170f0d020408060a050a02030f010e 87
    0x41903804c180c4083d00c131544600d0060003520301c0150000003070032a9042101c0100c3c900103807030489201e07a00070790340150308242204600706000c10440d030141d40d00030000d1014020503240140701901c41e00c10305941662401d04591f40300014403c031400d031103000d0601495559424003103000b90b40001513080b24681c1d110001040303101020050742c080d80400c1041281b80d45025405281460080d10240c41605804014580c0300d00c00811102115802d48400340c071000c840c00040c1040c000c503030015110403240d200b040100070301e81e0b04c840b003aa4841c0c8a15407210580320401c0710b43d4080c907a404405070705d00d140710b104483d0142044640c00c1d88144100d07005505000041500401007402c100e025030f12028180c1c4a0140a024582520301d032885c1c60b189184c0f840c0c55000f602071400c4000304c0428800500304044101685c00c17175101520442c800d6540b03a680c0c80e4404e070b0301c4500301c454603001440d220204445904034000c072801014004500c075034a0b405c180040c0d860140250541c680d98602180e10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53399913 1250 53398663 53398747
    0x1d0a110d060305010c0f03050610200109050309040e030f03010905190f0f0c020c010210020a020a02030f0c03190b0402010305060102010209031005150307260307060f020a2003 77
    0x7400155100740e00100b280e4050505c00f401400c1c0710b40c10f04085c581004100070454841c28003110140c0640d24100c0f8142619017007040003c180e80d8844192542000941001c0c403400000510700c00390252410022130080c04c020396101d000f914021411031030308000400a00382c5a4101c180c0042c407502c8913110a2040c2030359201154000c0c400340d0840798407420006404013681c49000c1c8002c419001810750b49000b800005d4454071a9540f081005e680400ca0705001031081008003600f40d030107400c90313001000502c24155101c24003001c3e28403d00c1607003c1c00c81c1c00102c0c0c0c0380c141141a40702d0101400740d21103a0040d406010000c1c00c07541199070902c40c0640540e810404803141e2280203100107014100025105820141c0000c480d020b68070140c01048681d6581e0f40b07810020700804e0051001c3d50801c7c03182c500f5485a0040545580c5c02d112610160103410390042403814003540300c0c075410000154900c2070144680701140b02070f400500003440e042e410919201c49061009800a444907401104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53401163 1250 53399913 53399921
    0x1210311030d090f020901090501060c0f170a0804060b1509010e03150c040303020c0301020306062508180306070c02031c030f060311031603020a150c0b09010b0a1d0a110d 75
    0x109440400030b18002c00e0540c24050500d87c00350400d40400d0043c0d40c180703d8040c15013a556040204040403800300603052001c05c0440041044c0500125039a0b5040c459005100340400d40d401c0d58513600d000c0001096141c51a0340083c00c51048a4041c200103820f40155254154421015054091084000000d0401402d40c5100c2c4c0e01d03200a881c1c0704d0307096040003031502101171f520314000d80c4100284a1203980300b400f910040300d40302d20154104244c030461548002070a41005082140104200c4240030301c40040c00a00c0030282e0480300655a0700e8811281c0d401e00450103501501700705040e0450241c0842c042c882d03207085042c041401240b8141c908202e40880c0d0094400000300c5076010380c103240500400a45a02c5070010b0840035040d600014100b48880c820034441c11408501c43c50701c0c5010340f02d059040354116203503000914200207038901800c100c000c0584100c1001c8008142c1c50300c103038184100410f412962442a9036607200310340c0205800038800507264010301201207803200c2402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53402413 1250 53401163 53401181
    0x7090f0e100f180807110a08010509030307110a0c03150b0a0308070c0501090e0f04170a0201050105030601120b01051014070804030317060607020d0606120b0105030601210311030d 79
    0xc410b070b28400b4410072201c0082400001c4031200c3c0b04a0b01140c5801c040e1051a60481c07418031100c482603000451080386a4400d8507154241020030030074280c080040d621aa046848084840c040c02c8811511182a00d170000c2c81e0001c1c1100a0010540420240c030001c840150f0024480900c403001403508199544116181c0d800001d0a904010b400151400100420300342291314a0400e91140d80014000308280e0610340d034440040d041c8508124902d01f81c07a84051115600c4c00c100100034041c103024000d2500074030506000284812040104098040c2c101c0179900c1c690f401c090400071392804017002c0b0410400d2209000c41201c18540080503c0340c403401e0140c0c0d8032490341c5070281404510030583d000c0100b01d10200b00407a10340904030381045d82d044803802c0f14504d46151400003005180c1001310b081d2132941c626006c03c0308500d22a4180e603400c80448005030303070707802c0b0380d0032550042d074101902c2c8000a042000042c0c0100a031054000404054a04041c000b0a18030115082c5c45 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53403663 1250 53402413 53402443
    0x70602040305070f05030a0303090501020706050f1006081e040c08070608070e060405060f090a08010c03020901020f010501150503070903120804021002060f13050a170910030b0307090f0e 82
    0x1030400410004100c490000c180c10600820402c1c64800041e850750f1364004060249501d440c07070481041002e604644d403ca501400801c403a080441c0e0385c2080d00001c5840c014007103030742d0001090450140d108580b14a10034080c011406421100318001004040c200f260b28100c4408041002d42c004d125400103840746070f56180f40ba1420f0107004040b01c0381c01c1d49081c058801084107206a0300d95400307c664103840c10903819503035164800441c81c0004268440ca0080d481c02041e2440c60707a058000f00243c000903421148983c001c4001c1038201c54003881003402d00c1039007600d0007880034050005154041d1050030a1901d841d078a44540c10485400b01d68074001681c007900300011458111151403115045100408091030010240342450030090918590000340d00860820040d080042c001140e0340201a104103c14011005489410103074040d4420707030120b6801480c8600c070303114070300302c03003100400600c0340a01e0070a610006052520610401c0d90301d5040090b04030008104d00f6182c82010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53404913 1250 53403663 53403667
    0x20705010905061810020a210b040605060f0301030f03110703050a020a0b07050d05090f12030307081b03070c08090405150a06140d020904020403120c02090a05040b040b041106070602 80
    0xd0310744541020001007003001382441d444182101340d8000114045c1c43d80c00442c0050303a03011600703000d50b540380b07004004121318500514030680c0503440e50821000001c060354140710103501d503002c1000078060500c031010850024401000800d05000e0600c862074000c1c107003848648100107046003021800d03001501c2562240f41c4a504506100b210b01005024103000f882c01c2c4121035490305d44519a5400751700c200040464644002d9881000700381141d94000e0409600d80d200b01c4056450741c1084400301c0200d0042d000059140640b00ca4080c2c585800e40b07a801d01e0b698070240d081c0c481000034440ce840c82441480350300d1064807a40704083c0070342c4219100d001090650000c00010b6207582e0802410000080f04180070714003e0b40a40e10244c10501d4003686031900d46001c40e00a01a03540040c202c11300c4013000c0d00c505131700304038010354a80c001c0d074030107200d559000c00c008140d40c03043d40d0007482c0c94075180c0080d020035500045160011301c0f4041d0501c800030f030b82d80010071a4100b00002e40f0201c3c0cac0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53406163 1250 53404913 53404931
    0x90105070c080102030115080f07031d01020c1006050a05030304120f060e06040501050a181104110a050406020c010503060a1e1502011406120a02131e06030b0a05010f12030e0402070501 81
    0x1a03480b80001f01c0b85181c00100e600d00064580d16140c4060000024161210015120011418445c10440b00044000c645a441c411041581c9400080003080c000c0e15010012483c1d04281c0301c00d10941d04064001d41c6070902d1720108180d01c0d01c50403400d4401640b651070501c0001c0440c025440725054142c01000c0c281024100182150b0b00503000c450124a0071024541c45151306210f000c0490300300c0079030302001c20120041400b4000c1103481a54080d0001000c4400716004400390040e11181e508452480d85803800544441c8001d5483c29480014404100102010080d42a03407180310700c0344100406584074400c1110b130003215032280142c0d4544064201c2d141c0260516540601c0071901c01c941c80540e5000c4175150080070314068094890080e600c00615002e80160350804880603030b14070010703030000d110401401180030480320b88014101013402c04d50940a1706050b501404028594035150682626101010038812000c1c4000c0d1681000180c0c0c0c0d81c8094041107014400115081c0c00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53407413 1250 53406163 53406179
    0x20727060b1809151014070f0b0f040c050906040f0c020d170103020f0105030603070e0702160801020c0616030b130912020303011d070e10170603030a050f090105070c0801020301 78
    0x403064030540c05000920108400011304014504c0030a1080e0341000310140083d104482c1c503801040e088205580001e882e104018a024680c1d2030700703000c1d40700e000702505c0e02c40008005071001d070f801a20741c0720a0301c414491813424403980c03038206800420008190555241c40c809442d100200c560160f000072010041440e0072000740c9584010f6a10303034003a42d40c10340e8005000c0b045046215810400d000c000a20b0300e0710704000e48409041092401c00c05c0b441e0200c0020740ea0100302d1422564218050740c0094950414000c0c1c03440100c00724054421503a440c40c1e03948014103410070150400da100c0c1429490394a41640764150b4134085600400c10f4465824135820040004000350215031080004114030b1580d016621110401c03040b28010395128204100d40719600c060700c2c590700c070b01401c030385042141d0442c0d920742c9480c1000e4400ca0040c0d451604041e2a07004a00344200414010042254503075a000e00500450105041460805696440340290002160060700c0a60350020051001034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53408663 1250 53407413 53407447
    0x80601080115050f0d02090933180604020f0f070507050f090106030209040b151b0607090302010302031008070312110706122319061401020727060b 65
    0x11142c0b0500e80c215070b0402000a1891003440384004201c0b9000c0341080900314290112210107500424500b0300d03061400c400c405c02c00d030143c100007510500c0c0c1c509045100b450040d18915000042c182d141d4001809402040103e004080e1540542d003001085a5100003034050300c03444024110303185d140e0065280451501041d900700e58400c1b08900b0400c911591004010f50640d6032601d405078982c0a598042009005c4401c1c1155008841c0700c0f840f0312144400016100c92900203100c031200507140e5104c1c0352111015642c000010343c04003000d101550007600215000303003a00341601662a958070050f800c0c10025002100c40c403103000103244200b03034013540001181c213800c0302900c507da2908901402031100c1541c404c4c0219140c81c40e40d94540c000c101c0070740700348002d01e805940a142c02c0b681c0b0a89160350083c16442d403032400d4408600b040b03010415001c10b00d030680042130f4050a1840c480c40355944101003041c40080148015403030506801403e0040c4003013518261107055500983c0309038 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53409913 1250 53408663 53408669
    0x60809010b1f021e0607050c0a0614060118140411040801050903030103031202030c04030609030201090f2618010503091606050403120e0a03060c14070b0106030b060705061609090c0806010801 84
    0x340080e0080184c0140012a62071b81105603030a00e20f568184810301203041000162000e410f10380f0b407881e8010100c284040281c41040c091b078511070403500c50b0a059184d080b2900a200c9145030006042110b0b0800e54001d104a40480403800e060907610a00242561801c6621f642e903034202100400805402c030111003900310081c5015425441c0c986c19403501400b4501c00036000f80d4071240400b0134035000303500c215026900300d400c2440c80582424500050b106505000501100140405064444140c1a1307200e800c0043c0f880a6900100300c01101c803604046c05c3c840030790042c1011415699802020040141616100d1988031803460a02c4c100a070200c1520f0000e210b0003220108460b51882c00f082c050329800304000038180a0800c044907015001c0c5420800b40310006001814041c0b91030303403075049421640d8144407900c40780080c03007240e010f08280209140d0010000c0345003c4000b0160181c9203032a4030b426003415030340761410016a994540c420020821090602c01c803568800705003409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53411163 1250 53409913 53409943
    0x204050601170f06011106090106140a060c0b061f0806040513030503040b0c040504060605041e050d0809030109060c0f0e011404090510080109030207060207060804020a060809010b1f02 81
    0x99988041c0d0001a110010043c0d852000302c1800500c03a80e005010f44050300d59600c003243e801340b5141c4c0342030340201503500404107440701a52903404c075480e0410140041c1c6003159a07400b8142030075030350340d0b51000010340781a0b48074110340c00c10030515182c416108081025503036181171600b804c000f40011514017900b00c89030f909048040e040444e401c801229000303a0320841c8d4207599900c0c030190f00c10720300540c2c00c5954010b04005001444076440f101070000d88000e505443e40002c0c07080d1f08104152a00d1240c00e40003010550990045030b400d070040c00716023202400105e13031403203540e13031b100116070304034803d81c0120781511544c04020b60301a160b082032031420300340311914142d081403011039030103280301e00720105031140d0015001800400703074800104000002800220910302d4080d484003000d004450040c410850001440f0f440307842c2076802141c02402400160b41406802c503490701c001441e2050540d201c01e1540c0d003648811300c0040301ea003594680d10541d1b100c03500c03009080801d1003418030300d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53412413 1250 53411163 53411177
    0x6090f1b09140414101109030105092e0b0a03140d02071a09030a050304060507260405060d0b0a0f05010201110309070603090201020a050a0c180e06010603051e010f030204050601 78
    0x10a16000c032501d50803a820030301c103100d00c0304e1052039103140010302c0284c10100d6050481011401401d0b101070a5030b0f480c00c800a0005503100103841eaa115a0890844d550a4000c00c00d02d6882c00407000c0e0700c0740044104008505204600041403101100750308c00c4a10b0b895911440c0c60070001400b108840c610315102800000c0d1030b20207412407165104481040351840000c2c0c000150354100320007044180d022064a4540303a44000141690704400425511340102c60000d00710050200340c8503298140c25590a070800382088180201600669000c400c0c0c03640e605501d58480e91103000c5040141220310109030300504182c002401c0d04c5e440044803c01d84002d100b8801c40c1480840c20105a40103407800140c1c540d22400100e00d403941c80c4401402c10300850b01d46034188070410280c807041d80c1025942c4008000b015490f0b1003110481d00e4400b107503402c00c00c0140706c00c511941010b0303003000c0d9654400f5070b0171000040321404500281d00c280b1040c011004104214103041c020f0300e911143c242440c0d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53413663 1250 53412413 53412431
    0x30609020c070506161403030708070207030317071202070507090c09140d020609090a02040911040302030a0605060f13090510020421080d0c030903110607020d0c06090f1b09 76
    0x56901c0c031540c041e0f00d2040c4004a035014141001e46200c2030829000794800f0010759991410a840b54010b1b03034100001707154400001d4099000203000030840c0c0e49655809000290004040d2a680e8050440c2080012501120383e10f00c80a0001d404000d005001404200345480c00207401c485260a010040c0300c04688100446420f901c0c000300802d00a4540705a01071951002944074400c44c0c00e550b0340115980280001744450380c3c040c1040e940441001c11038040e0402408000b400380b848001d6040d80b02110b4140064456041190440400b51411900d002010000346003c44200300390820380344e4800c000c1c42401020000900400403a80c41145040e04000e4480c8000540c0d115050802c15406003000402003800d0440e03c040c10769080800a0b00c2410400501a11514905800040ea10340c1d02c01c04070309000c920300703000c3c500e1500204040340203508240e80c20061740300180d4809903034403400c0003c100c1301820070921074840d6040070f16034180f8006042c41c00c0703a280c2080381042c0c40c040c0341d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53414913 1250 53413663 53413687
    0x90a050601050f130e0103030917030f07110103060f08031c0b06041a04030c09090203061f12030203040b12010e101220030f031903050906010e10031202030a03060902 73
    0x980441003000354280d598000540700d10038500b40e82c5c2c40903114500b4000000189a40001c00034280c2e80e01c00b50500105e0406011640d49000300e940103e0030b0142000240001442c072113410000c280306040110708265603220090424405d680095099000000c0400c0c0ca2801c4c010912070310524410100140c24403030000c250180a02e00134010042c0503203400b910001007400580b001140d00612881136180c561501e10f015080420f41240644103a802062010751040d0700620301038290304c01011900d1400749002c00c3c5c1e9560700703025420360204000105444040200030094024414094191949400c90000302410300601c003915075000b0300c8040c0303c8984100f004004150b000307000007009503a02070b05104002c4660120b6a4140726031415940b2030072307000c000340000b40d0840c800c002d45a9894032042d42520021264140a50030400c01841900a0020115009800d14210784a416101e640b42c8200c03d040a5111000d640049440490554140208005800101c0c000d40c204200c01080c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53416163 1250 53414913 53414917
    0xc0a1e0603021b0601060e130b090c0901090b030f01030b0603060417030a06150c0201081f0302210d020c09060409120c03050f07060603061d06040303181709090a05060105 75
    0x40508040e0001620340f0280c03111005480d102e0b129078280c0740b003035941c0c440103000c104500140368000c0e10140d01d80c10586120744202d440c0500d020b02606159542c1c100f000055a000025450600c04500000300e00500190041c501c160103940781c0c400294118208140400d0000748281d00c660320142c1000005050800c070007048102c14003055840c2e880304006000a4605900481c15650b001e9140d001c51661003030300d812200e4002c0e241c060b52615074510400340701015074100c1060b003805910400041c14002d0f402e642524000400c2c1d6050081400d0352810b01004c441c0800c0164400078064089241c030580d25a00002e0445041103030915960710040003911244402042c450000190340c00d040c040c0048803c3c0081c5501160380e41c0e000c9241041c01064180001e0718140e10b052803a40c03004440d0b00c210b260141a240007418160740b1036504402800210700040c0c040117200302201e000440f0400c4020a00d2144030416840349080406e0140c00c02008004829440c2000c060004690300102 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53417269 1106 53416163 53416169
    0x30709150807090905010620010207020a0b0c070509040f03030b0d02040608100b030102040308040b0711100804060f0b09012603030c030717010b0904020c010b030105090c0a1e 77
    0x2110300031185d0034002c50f004500c1c41003035032031550003107041503030301540300d03000546440411703401f242100c3c0040e030051002d1000400c13820210300c030500c224006000705071410095450b00d0303200c0301440c0c4484e027409030034542d49110b01c0009480d000181d0521a0b0068401e100480d500c444c41070369241f641e0106400c861601e00030840502d4180201e40460f07420200079820300d070a16485017035503880080120b808092a4085905640f40d8400c200e1b8000c810303485868140c0361900300307807050700c241c5001000440e00d400071750442640c481c003000703054803101e42259403a00c0111101030a403900e07803030400f1424400030040044040214004522400141c3e80d84036900703490911115050000f805419010740c4240000d07070041c10143c2c042c0c07500c40c0b0480c00214800c0d0f000404a800c407801078944402640008200400e54100618080010300d04401d21015104c100002c07032031120f040b80 = true := by decide +kernel

theorem cover : BRFrame.Cov 53237413 53417269 := by
  have h0 := BRFrame.cov_init 53237413
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53237413 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53237413 ≤ n) (h2 : n < 53417269) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
