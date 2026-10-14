-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3281
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:10.562986+00:00
-- url     : https://prove2.me/submissions/0f48ae9c-914b-4242-a66e-55a54b552c3e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589928057 ≤ n < 590107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589929307 1250 589928057 589928077
    0x8060f0a0527072c0a0f06031a0106201c091a03041509020d080904020d0903030506010f110c040b031216030801150c06050601020a060e1f05070509120c0303 69
    0x2118a0401c5081410303043e0000640d1016410f0f800c2808900c259030713400c82c004000c0402070b9103030740d00641004540c2d03000c40002c0d41c100501d072004418828455070621007c1c8034003000251502d2075050b90b0380700c2005000c0c0a14441004000307699100000b0007506510a07050002c2c00a11440003c0c10010034040304001c052a940c019502e161030f143c55044052041090729036a4505040400140c44242040b010a41c000703403070301e8645681c0c4000130080c3c40390721300c000c25060628131140b08040d0160441c0e4001d0b0320980361b088c0303040045a0102c1d8100007014000f182c652180884003010306103a0b2015480c0500602a90205403a400c5102070582c041100c02d01c0e01c0a0048801c1c09060b440001140540030072010811002e003442c1c0c00508120108601900060759103001c2680d0b68000c00450107075542c005018000e0b00f1408902c0764880000312801014960b69100141d030b80b8420b407050030710658041d21040d0170403494500b800a4945404203001c064070500c0b0081c041035604101420039100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589930557 1250 589929307 589929313
    0x90510050a080c0906070f060f151401170624030c0903100c020a08030a150e0108010e01150308090604030804180b0108060f040b03010b1305090708060f0a0527 70
    0x520241c000c2841d00010440098408103108400d9107542d6101100d0003c0d8114010106010307180c200b180c000c203884107220128901d4a10200c8604400303002020032174400301c05034030358041d50794010344624400c01c520705c108104034400a003e40c03030302010101313001d6192110302c0d003031035483c542249070f541c01924215848400414030030514902000b01040300115008144a40c0c000624007079610302e103032540144084000b00001d15103542e903500c2000110f1001c04032004850392040c801c05800420300600225500f8080e0702d00c44048140910010100301c1e1058480003441c503142c10140c0c0e0841c4d454141d100904010010206108002400240c14020804181d48880c41400811204c0c14801c85050281078410804643e4800d205454480d40a80700816103804450001c0e00614000d001c0942c058201e00c1558031a4803030345e11a51141d101c1e102201c01700c503120680c10ba07135884200d136402381c0c5031300f03040008080044617045660040a040c6501c43c49004548503a1882161300241004c80c0d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589931807 1250 589930557 589930567
    0x21507050a0c030b0709030309410a06030b060313140604050c010e041a0f010e0409060203100812030712090c03050a030909020903030d091703101404051504090309051005 75
    0x2001d440705176004a4179003020701036685144e401074481700d0284102252000e4001c3c03080041166406110084401ea5803070024084503d507940d4800c0c050302c04600c1c010b0203846408030b00c0500034810f0740904000180540c0c115500e5580b01440318081c610122107100c604030191905503002c0209a029520603809002c59450b0400018225100741c400940300d9403c0c196040340081c280c0707850021508080e107008400cac107020401078640d4000c00c3c41080c0c02a290858407024440181d0285018880e0811804401d950ba00410795854081c05c40c00720b000b90040010429940c0181381e021000d003005c4401103440201c5440e10f00d0840d00075031050b1151f400400f80350081680c000d0142001c1c00c00f9a208508102c03600c00032a541c0d000320240070602c0e81d9034030080700c240000c01800344d8281001e1001c40c1c0d903d2078800017209243c9054401d102052002141c011400d19050064070310443c00c2d81298520b401000c070030000a051040310a505011000740c0c08541a21a048400401c0c481c1d40c0365180c0c0c81e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589933057 1250 589931807 589931813
    0x406090e07060f0e0f040c021615080c0f34060b0906091b13030b131e05060c0304020f1003020903190f0303020c0312090a030f0c030804021507050a0c03 67
    0x3e004869501c3c0308024110080c5030703951342c403040c900b441142c2c2503500155180107501f090b854140e0420700c0701c40381c0402080000c1d1207080342402c00d441c402141d444618a441c0c1d101469a40d0044103d01c24421906000c52361850103106820195201c60b104101c403002d0b040d0042c1c0b442d01c0320014081d0742c030a07110035002403903044c04148503400103010f071a04542c81ca0125007140c460f00c0071401e1480f014070001a04070081800ca000b40005c0c5800211550301401c0085038041d9100700030f4070403200d0072825076a15606031074202c02011f180c3d40000c042c1030a40e84010403500c142e070000b0412079001e10040389586154850803055035600c0c4003a2001a5103015000c20103203048000c0c1003120091201c0010b601c0054030b101c0980a5030b82c3c1c182009600c4502c804112170950045c1403401094240c08800c010900d4000607008a0f005d010b503d403040c03c03031080841124400c5aa00010740803d40103070100c0c0041c140744411301240401601d085083c901c5a0342d03179504042504400782c2d03005010710418424 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589934307 1250 589933057 589933067
    0xf0f0506011d01030f0f0203180705010f02030301060f0c060e0c0405100b0d1d1903080f160f050910032007020904260403120908060603070504020304020406090e0706 73
    0x40035007400c040800722403070641ea0040d424074031203250405490b00c481194a4489401c00c0c3d820084c000405d64403880c0c0010851243d0400a10305007a41c071691000050a501803d00900350307040705d9001d1461070f800c3c05c0c0169541102c1209100400501e801c04001003405071064509108000010b052070f4100344003000191100030340140b41e05408203d08000d0810f07814110342c3d491000000104103c020809845c0640c0616000034540b4000c034450107403d240800c0307540d031500f0310075100c0041e00d4540d0b4841200c8540121208054014030880703034244a4094145c3c2049404240340403031070a0008400b10b0b250403100f20380000400e40702c66041c401c01c400c10811000144080145030300b405015000038104400241002d480c1640d046043ca2480981620000e08a200080c50b0b030f5580b07549142c10b85220003203040b1003000411800f404030b06070001264140c003411000f4018040380c0d0900d405c200c001d500180c42240c3c0a9030b01c080020f0420800d00600003460b0320880600405c034609003001e01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589935557 1250 589934307 589934311
    0x803042406080303090c0a05030304180204080f0622120813051c0909050c0703180e15010315060203030a0f1b05070201090803040b12130b0f1006050405090a0209060d0f0f05 76
    0x48162010001031000c0d0714000151000c339103000440e423242d1000619000300900c500d422900340c1c0c1c0905084407500e0400003610303074081c0c540403040c0700000c0ca4a10402c401c41c101ca050003170481c00103011400080d8801e10b03445400c01481c0c80f802c0003181c15980d80c00d00c0d00d04003c4241c0d990942a8a019280359003012105000b002c040906005920b0022501030451080740001000e02011441c80300070401c0450202c0b0140c1804114803200f400c00b0b10200111070904070810380001d00305206112806c40e0725100c03200f1281142c0055003551106940c0c10050000d070a00014039030b0f5100e00078846860401c13620604003500e6200d05a541d030090000501e00d00c0039400041190b44108010044440800200c41c1b44114016000400740c075145100d8080000340c100241040000c2401e024411680602c01c80c0114070214607044450798400d13055410380124400c0b103074002040f00004400055540040c07403c3c8000900382c51070600007044503c04c035038509035000c0800e60343c0d25440000f21007500c48d4503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589936807 1250 589935557 589935559
    0x30806120a110415091505041107050c1302070203060f010f0b0301120305090f19050906040c020c1e100302030a1802030c240f0304020306130803042406080303090c 72
    0x40031800394031035905140441d02e115004650b50690b001d500c045400c4550042c0495400603c50745403005a1014a802c0764065035104501e008505084c1850b00400c6802c0030390300c1400f0f014a10480700c100038040c02019992080c5540800803c40141e800f444054070034012071205491b59414030050b114880d0300398115800c8a4020030051101e01a4241002c0b10390782d05140007556504c00001090b6007034100c40c1c4c41a004000340c00d64400841456a4440940c0d009070341290080d039902c410081621558803000015801082c0c0c412540d05140d080c2c0341c0400408000c1490307001030100811700b52100007001c1d800190f404428410500c059000d440800e885c0d0140314031240d05542c00013500c5040441142e4420760500354080d10900c160801080645a00c90302640c480036016440d90131a8000c440481c820f0140030700043c4001e00c2c400ea45070f40c86400418a6055a035580d030780340c2d88191642c0c07028201130305203c106030701c480581c040c2e08007919a101c042c680f00d00303218030414a0712500c09401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589938057 1250 589936807 589936813
    0x4140303160b0405030f040b03040204140105060f09060c0d0c06140f0a0c120c09140603010b0405090a180f021e060a031a03030a0c030f0e0a0506030a0f050403080612 73
    0xc88440d076000014000c1d82c0020125100d501c903480c12a2a61041001da09644900803500040c980d9200c409544958000c4d68140640611405d411035910002d014259000101703100389402840400c01130400060094001840c0034042040310b4940351034111590001484003101070100400c60103103014500112051050a040c0303482c420144080007407042d01c09503070f00c55410000038071a50309040502c514000c10403601414110003019550103001700da4101b81c441109655904103d402c5a040b20804078400b8241030402c1c04011485402804000500d0344805212a42d4030001241040c61842462030700b50104c218411b002180442c20304400706220000502c50702c035141e0340c048030078003072481c035000401220140d5000e031100d400c51000ea03094800410010012600542e00158490094451118012103064226401e540c05c21011f81c00800d1300b41e04200a00306003010710f4106c10b4682c00880e10310f01c4101000d0440c0c41c21942903000601d06003e000c40c9081c014010584225000c001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589939307 1250 589938057 589938067
    0x60118030305030601030209011b030f091e060e0a150e1008060904150914100509060c040315091e0c0503010b090f040212070b0d0b1e0d03090504020c0304140303 71
    0x7015001e4007000307100b24141a000507085805a20600200184040081a0613030944036420014042000385001c0408944102400b18521001d414888805407a1401d080381d440d04001f030407107a40b8920b00102e03030822003225000ca507401142480c3d564010f100c2e40ca0b03a03050044c0c0c00402c808010b00190390402c6c4014141440415142d01d0690780d80180c005401280b8030b071035601124014041142c004d0170010919441c05181c0c04081800008160101c009214a44402c60802e849880035620103a07180000c100400c0003403084c42c84241d6200e80c09100080f40ea590761200007146c00a03030203410f00c5501144200e000c10032400c0509002e41000d80081241a103e9408140c919001401c0e0022100b05c00000070115502c0d03146c6902c0c264505011b8072a0300d5075603000c4581541044d222200d40c81d003021070346207450030701c011100042e020124000102011300030034031041030307000881502000000f0b80c010903c6e0f160303030001b0308050b030082000b965034a1030301c3c4071084120700800c120f0b44a41c00c1044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589940557 1250 589939307 589939313
    0x2d0102011d0d21020f0903060106020f191106030711011103070c020d060f0c0504080c060f0307120608011d160b09012006010312081312030e010f0f020306011803 71
    0x1d44495842d4241468029040c50305000340141e07070b0500c0e102035000e00018828090106410142c11101002d40464083da602c600050781c4520888e11192090303403066a00070740000c0071281e250041805400c620045007407140c045480c0f50310031240e44e804200c00640c1900c1c540424402c01e4035004010480d503046040100c0c00400b01c4000d00000f904c502c12002171101844196032069071000c546403810401200080c1c8050441e40182c4101503443c06a500c08248a041041c00c4070030308481b480d1190319544c0c42c1c5c14140c4400c0080c0b48060b048036641d0fa030200c0c039120240704914061442c40380683e441282c2401c240c5c0307810502e20f800c041005c9403900c20400141258280c416902d02420f103c0d01c010300030040c03072100c4920050180b403d4031900d00008107010109a16401021080d0341d030b80d20b1990b5050b03594a00c0c0700d8107000200a1a9007040241046200394880c04000e0110342c0045440d12f0902c1401003580c10b8054940d0030154000103124107036030800e10b59007000460899038064613103991 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589941807 1250 589940557 589940563
    0x3110f0105060f2106040f021201060302010203090922050115080c0d0f031202030a09150506130506010905130c03051806070e0a090c0f140408060c092d0102011d 71
    0x40f04182c0070307500c5903500703c0d00b0041d00f44500c80005550000c036401454507040411690540c064241c2c065451000b4800341448180201d005480c2c041e0000c500c1c004d6030606200d04114001c144145601c8400aa50751031a03600b424001440d014100120b0a140450400c28420b0096404651103500c441864591621828050081242c01000a00485969040644039120100604404503100000300304079024035a20280c1c4a0b0301540c4002084000c1e8001a01190b5058a4483d800004002001c1100c81c682c3c001036803100041c944003611039610004150402c00451801404a450b001d4032808698140b14041d40040d036209922080c20858100c6520340802501110410a400b4000c805075110301c21844010842d103142000720302a0701c103009007916100e606610004500d031000d0801c1c0d40ca020143c0f000d0711004030203003410f600c516981404a9000301001e40e002009845d44a01c8030400c0039000303080340b070b50314145d01e00c2a910700002402c4a804c40340702c0c1042c1c0d004101c3c0c600c041e9800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589943057 1250 589941807 589941829
    0x30e010e01171506030702070602120a050316030e0f0a210c12030b060f09040b010801080709050a090b0916060906080c070614190f020c03031f1203110f010506 70
    0x1c5410502940f110401010110000749003680c00c620000184801d1a500203080360480e5003503425a170a994550500c541c442c41034140c5d80c00015414404240030074800b90001c81501620b04000547c81c98807240d5030b08007946c1041c902d0316070300030034a100280f06c400b04454282103008540070000f45440c01010f0104295804060001c0b6841444030040b24000e0784000d0781c011004001546600147c401044a944107603c02d9020b02e003040300626865000e81855810b03071707030b054015180c402d04001c920001800000c14001480d078480c80d10303402140030f40b013400b80035405401c0a00003114001e41c41e0150703000039034010010020181070410049520404040d04903080860b025621115030910002030145c0d42d84412032100c1c0c00c000d00c5049509100b203d00c643d0840780e03007805441c0b04c8460740c0d8200d004400e040b460b1500304200107203068104c52503d095042c0108076402c92241c4826621210024841b0700320041000202d00c081c031000300b04070341c1c0c1c404824079009100701d2400c040815800041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589944307 1250 589943057 589943087
    0x10b030a0b040507050a03120314070e10140310050102060f07021b01110d021606050c060a09230c011103071a09030c19120c1a06121009030e010e01 65
    0x6001c1401c10200b4020350009140046c03044400e5916428400d03412205800f03006c011030f1419481000c0c0c0c02c00022070a01c40c024684581041524890512186844004100c0100203070380c0f61054180740e01c040907500a21495030142416401c260000e468000094151810f44404004014030641e0009804144000600d404d541c2c64102000507100481526189402400b51400c0d0308001540050340100e6a4000d080d151600c580d02c8406642030b10481201c0b0701140c0002000800c4000a41c01c550136440c41411268984000010369181c01303007946642c0013030b940041810907903e6074880300d80f40c0030000c0721000d076203424a256140c042140c1c0340341d003564481c813102c4005502c3e14410b02c1a07030712820840302079480b0b000900c510481c039a044600f08485140000300304401d041d1280400e0880b080d0b10100095001c50341c02d105070000c00000700401d60104800110720103000088c4101040d030185040040754a04240c600a8a4044004000c50401c02c15919020b0940e034020f1040c007406003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589945557 1250 589944307 589944323
    0x10f090902060d0c0201050901060f030203060a021803030a180f08060406271109010b040b04120c0906060c0c09051909080405030a2a05130c120c05070212010b030a 72
    0x944041921070142110030703c549072410540350b00d040d4064000912801c2890006c1141c0d0303445600300300204115000180d01544034000041d106d9085600424070041041c903092082181e01000074034550100c1803000000b8980d000d1014420140d05a280290001115000d0064104888130ba56902c0040c000303400c25840b00c42110062200a2017030a90b84044040880ca01d821030815180100d1515106030007490701ba8000200d1205100a84007601d08035034005103401d1038950560408400300c00c0503500d91307400c110b000030a51880d01c0f440e0018041600c50000c10b03142801c14111582c49540000c0302e00341408104482021130380342c01c4d0b0142101000001d4a040c943c10414083d02880e0401e03509403080001e8201400b1260202e400b0120003284030040003c40141d03e030b80c44180b01d120322074002a114030342130118070858000c54000d000c14685802904078214602c0c003034880d007402c0603022480010f0007101350300b000c8405000c0f03480003100a11400007102c001c650303a440d0070880038106007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589946807 1250 589945557 589945571
    0x60c0711091e09030a0806030c0a05120322080123010504020a0c08031e090d080708190507050d0c03090816080d090615060e0109180b1c140303010f09 66
    0x42d14682e156a030245a542c80b400151815071820f0f5920345c4007240313010104200e100020118500012400c2030604007134000000c681c9000140031901d900020b000c2c00c03e0006024000301644190440c058229210184502c040c2ca000200e5003100d540c44085101d01c400d13004000000c0c00c00e0304881d0f04403281500c0041c1c0d16080d001d000c83d4000703003480c8018042003000080c030030300502c41c00010240e050213111f1220705403074401001c0d54801d01009080c01107044200040ca085001d044000d034030180301601c0c520300c2c0710b0700c0941200f104c4080b22203070041b038000b0502d103104d51058410300d804c884a5003420040c09400e07403200400c0d4087c440380d42141a0043d84040200038903081603504c19040c00c8803c1c0300285403454800c028010401c4810841c110310440040c5541c03041d550241e03600700684603000c0041c100100c014103d2211840000c070a070301c41c04500700d60388a0460000e40323202c6034150102a602d007403900c01c404004041c0100d010364402c2c8014041424510018021220389030b034000740312 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589948057 1250 589946807 589946821
    0xe0c030a030e0a050d0f060c050c100507270315020f04051203040b03040c0e1303170903042105011416050705010b0a06110c060f07020105030901060803041205060c071109 75
    0x311450713030030036600100c00216050402444810740d01c0807900c2010140208a42c2c44400c40b404e0251075003802c101e40c081000c0000f1080703568445a0840b00f2407416924000189403441910b14140c50134008005001c1420018021505206120300aa415096140500c081004038450080d400b035184201100441c620b1200350402c03c40c0c004180a101c000c6d103c0c6841d003031100c1116450301c0381d14110900f40b000180c1c0c0103220783c1d04448007941620b80302c001065162055440e00c000420303010140c801044041102e411550310031101450600da5028011801e150050079a41c000d03181481485000060244140005003000040c4046103015522030304d850410b60701608400081d284c1100070120041015507009403020300c0c03840e0300c50480f06a401042c060000c00d22070220070382190341d414807074000150310550003540c104a500d000418142d0b12902c500303065500c1548480c0c0050f448450785410020300f80011681329100d03120450402c821a1102d40d100d2085000251042942500003084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589949307 1250 589948057 589948069
    0xa080f150906193209010e06041e060603110a0e10020127021011060c2a030a0801061106041203021905180d020a1214030c060a0e0c030a030e 62
    0x4030038064003003a901564501c0313004d08800002c18010b501101d02c80844142020010042e8000d44e4040c21000c0e4903841c04680b402c680002a00c0d45034855250341001100980f201290300702ca440900001441034a020409411a01c62403003150343d180d003e104d4144c1c1c2d990800d00780700144100b9611f0031860a0140d800300e006081e01c4003c8407404a42d82444540d60650200c0749440307900c2641c0c0502c0044030b1410548461000740c509814170b5005100141800d074070349025020401486510300b807628001d1910140c12106500e0070641a1300c080b9041c42c0725903015048034014220741c1420820341c040b4074002c50310384038007c00c081c214084501d1070243d180c0c0309604a584441300203052000d03451441900428a41c040c0e001c03220070704002c801c08422494070358070790100030354003c2284000506d0505072103d00e0f40c0c5030600f80c0e031401544200601040060006094040c4018068401403400c210321030103c540b494003080042d1b0210b00c0802c0a520b0008030850032507014149500041007203000201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589950557 1250 589949307 589949329
    0x103020a12082116020102070b0c0a0210061211120604021c0b0f0403030617070314120a090302090f09031c0e03040306060305010c0c260706060b0a080f150906 70
    0xc408420f802007091488002d95554010401316800005840720980200e00742d0285941c003408855900740405c114410f4030f0001c103290700d85401039850362269648004219101c581c0952058803220415408015401b84900c1c51004104d819484000c03582003040d6480034000e00007070089205040c1040100071101c40050b500d584400d02e41483c2c5413280300007003091410707182180440d003408000320b022801d1011100690300000c004007409403031611043c40781442c02048030100c4c043d2784513200c0c40500c0c1d01c0040084290700c0e01c402c2180c92652040c00308050b0014814100c01c01910140010b278840802250450010981c05505540841030301200a11038040c141d680341c400014000b0802c16140c0126049034002e5000f0030071110801030964018008050061105034406080b10711515440b04002505016040700d5003001059a21039040314055041050300c840301240050545070b100d0f0780b0607032240702017000c980203050940101e6000c010800c00140704804d010002503403a1501c0d0181c01d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589951807 1250 589950557 589950577
    0x606110607141c0b031e0a1707080301170f0705010912020a180b0301060e0c0301031202150a091b06050924130303110c0d030305090a0219090605090103020a1208 71
    0x100d00d6440c046071200034131210508500a004200c04a0701b05142107902c0c0710020512401750000c11829941c6021324410780d200d03903200980034007030720020400410203540648540e50007559040c2c8001c04c150f2400034102503400c1031b41d01c459000e1040d641d005050104644505049900c00e0350244001217030504aa0030040901d400c2c04c00410034003e054002c0e14204001364020848a0303115161030107202001c90b0134010154041004200040304d2111207091040709106450710381c4030418464080d10401c4d200850056103c1c00c5a6040c07180030240c0c03070488881d03504200e180c83d00e02000907041d405113054040c401c42110307420110640203014400810a82c00c048603644089150140c0b40c01c8100b800150005000c04080c1050300e84002142d00c02444000e109100000c0999011009008010100c0925010f000d542e0801620344101d2582c0e03402c0c00d450f041d02c401c0d0802e014803003240d4490380803504c584c800c2c4004001680b41c02c0b0361141a10100141803101c0d6445091803074240c4a444440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589953057 1250 589951807 589951837
    0x90b030a021002010f0f09020603060d030207030c03050606011409010212090406080a0803100f18090609021009030b0610170915040507030201090b27130c12060611060714 75
    0x1182c0c07650f41035000c800d0b001c445074001c102c1b01564940081c1101d4218100a401840c00c0011071018a013000500410301d102c2e00c1200d0f0b41d141c0325580c109040308561300450f081e60008091108540c0c00050441c10302d00215291400e00003400d0000303549403030406820080000004107020941c403030f074010300c01600c4800b08840720142e4500d00081e80c0c1c0c0c021190031644560f10380c404141440300701c011200f00c0c3e05172914940d0701c0404144a030001c0c0802d0304103c8669689100c00344c01a182c0100100c60300ea00758a545208034038600f86010f0031080204424455401c540d5820201380d00f06022003c401914a5001050741c0e82044885c40d013a4036a01c90050b800340782082200b0010300160103802c0c0c038806c2c1c3e20450b086982e001001c1e01ca0190150725000d01040c461540c460b10722556440c065980002c00002c8000c081c4404e40c1d0032950003020840c001003081c0b1030145080b03401c0c001c19005003014904007840129a504440d00d40b480504404108504044103091442400007983c441501e14090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589954307 1250 589953057 589953079
    0x120423070803131203080406053705010e1303050c07050d0503041a03060604092c0705030f030906070321181b050603070507020103180506010315020310090b030a02 72
    0x40c0d42c0c0c0d00d4110107200d0301804400c090105074441c030711104c441e020782c0c50303194410640c80d0707999032070080c1100510007035103440055000d8001c010b8201183d030300c4490f42409840c140080d0000c2c44160b4405030071040c41c1c4031010060041c00480402480c003c0d230341501d072080c3c039601301004543c140b41840e840550b0000082e030002d014044044024012070f110940807405c0120002c1c0304c14445e010844132558800b1080c0400c028144180d04201d405003420041403024041049040e071015129204410309680100c4040c0210f050800c44404042d0b068002181004d001000284291048000040401c04a2510907104030709035200c0a0221821100500c0b4004000314503009002c02004140c0f692000d0341c0d2203a00d480c403503e808109440029207a01d195658101d41035806a01c80c2c00100e0405988607200030a8801c1c030001001e046100b9805800b05500d181002c84401d0201d18544150600c108240302ca030004c2856200d088a446540215021000400007400c202c1003150294000002c207031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589955557 1250 589954307 589954319
    0x40c02011410060f02010c020c0103110c1005061005030f0619150c0c0501210b03030f0403060603050105010b03091902060c06040c0618050a092a050702031212042307 73
    0xb04031058440655485004080c2c80034201e0aa0321001c44400141e004406801364035442078024040c80401e1603a10342c500344071060154603040b000e0300300361312441d650814090b143c078081c400b030010040b051600741e0841c10500c0804981c0c0c040a00b100348260030741d80c540300511070002008402440303052200f140c9d40708000400b900e240740300001100c10810000f07010071598040c0000810304d008000391a0f04580404051400501600b402940e0521040c01109202030040b0700030b0025500c15100401c00c6842c526016095550607044401681403d00800844150010308c00b14000429141400008001e0010980c10322030807042c1e05850198200f00400c3c4204450b4003000c0304c0550303858141c0c01e20600c0c1e5040c407403406e074040c2c11381c080d40c0c40108001d42d00107034100b059002102c8000218900404142103030015050390340001080001c950142035140c14045555407040034030741c0e40d291000c4942c521018440040000b0031800b4002008184c1c8034004800b00c100140c02c804131595543c60300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589956807 1250 589955557 589955581
    0xc08030a050319090b0a090303110a030b10020a17030403030b151308060c041a0d02130f0f051c060e07170f011a2205100303031b0509040c020114 64
    0x80e5a200c3e0a50041c03452800c0048070322070301e441da41c0c0103100e40c0c015807201901400644845581981015102c0034401240001d610007003007458281d84002a0000c0c2503401e0000d018078802c003480654100740d00350341c0405d00c0e90352178815003050000159541d907a5403070305400800f00039940d6a0401505c08010071014803c3c401050704464440c0c032041c0c95950f0f044000d80d148800c40700d010300120144070810404014401000c01000308101407401c0c544038009441c00c90f0002c00031090f80802441081080ac0b444001d050042e001300690740c80700ea400d04003c40d42d001d80c18104803484d10f03200c9029200b40140390740310300381c1e074046041641c0a42d9501d10b980c0611401003110340c1c016001d0101d60ae100148148103603640d0009a191410034803212104000480003c00e010f076070144000c1c003007a4061125442035034429295507079200c0040d800c504004040700c15640c6403000d8028124030740e41030036800006590780608125004140f0000e01c1100302e02400c80d0754030b40c2103803000190034030520b00004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589958057 1250 589956807 589956811
    0x50714071511180d110f0117040b1012080f0903101505030d030203090d0c030207031505011505090a09020906040f0311010201231603090b15100c020306060d0c08030a0503 75
    0x191000e003003220500001c00c000d8142c44803000301700c1150229400780504003031200c4a9101070505212407c0c100c20300a10543e00c80c112021100c85840c1c2c410004410410f240d45005882d000004550080f115581c0e000c080c4100c00c000c07200320f04041402c001c643d8041000c0c1c210154000d0041c040c039040581340381c030040142d003e4140319010701c42090301c42503c20300c01e8070b01c15031820000305401018294103558080058000b98114094468007001084144c10012460303007445000245562601d0260600e20380c10713050f241c0c2041820400c011181d0341d6042401d05403000b04400686d1014400002401e40c403ca500000600706c254200200f403006400601c1507001c800e030024044031002104181d101d041c54030208500e040802d020686c402c00b4654a20415482e5003070010315401540c0303c81481400807201140381c41d10406d030901c15400c0c80f440e4900c0741c01403400c0c4603042898a41c0000d40342c0b04000c10b5980141d0144a030141404208007400700144040410360b640d80d1141ea400030019401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589959307 1250 589958057 589958077
    0x718050d11010e010c02060316020f030c1c0e061209010b0d031e090b0d3614030a09060c08040b03070f110303060a06120b091e0a050714071511 63
    0x10b003e080a2295002d40c0070480000d90041c0881d265980344a405240a00600481011032040510303244600808200030946800303101c0061000000c54000700d004143c0040158003040000d01e16103180703480740019100c0c00e1001d100202c03c241e481c1041603004150910445612441303a200940c103054108100385551001d48010740244414080207a443d150703a4403d060441c5000c1120206494059022241d018922903041c144a091a006007000326007100c1a003003441e070707103185120401001800e9815070745004e402540c04e14900c060042c0c03070310a9500c81c0034280000007111f103040004003401c44018165140b5241d841e0b0070403030300003000c64681e00c141502090102e082034048000004c2502d00c6480000c242680e00c80c10701d001102c154070021101b503070440d19000d40303003015580c0141070303071080303843e104c0746040303071442012401c0303180006400030300003624000512441d1944080445124111394030001e544980307a1815031a904a40448180c1283c40e00d42c82c0404004031400920074845 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589960557 1250 589959307 589959317
    0x3010b0f09520e060309011517011d0304090b0315070203130f080a02210708010e0c040509150601140c030403031e09051c060504080304060509150718050d1101 70
    0x1da0012500340c010100300d0b403000800c403050000380305440c1070b1000b10350000c03520300081040b01d50100c5549408800f608403965094107900e0484100c00c0901c40c0c800040c2000f0004d405845407115141d44a100c3e5004003694035403034105204464a08000b03070004001c21800c01c0130300e8902010001e48a400c8045e100120300714418000415442c00300e000c0040d20500c8001c0c041e04803e9500304018458030000010102e03603205080d580059007401410b004243ca035002044030031f007401861342400c076052803040c4036900d00400d0044085000912030380c01c0c1405001070302d880d150200140d8140c411034682d5201c0640014081f03801e07400200140080345c0c860740702c0d40705ca40041420b141d9650007c0303090000094502408008a1070080c140b91030f00c0501140116072820b00d03843c0c01055032012a01541c0f405000400c0c001000903a1088652040050021300484141c040312584005c03c0507200004220094110780d03000040f40140f00d00820300189a413284054615045115460050906011a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589961807 1250 589960557 589960681
    0x210020a03050d3306080717010302090a090c0609060e0604030816080f0d240806150a12050a031e0c260f031503010b0f09 54
    0x9000160840080da4180c40d01402d01c411694002c0080414040d180c201684200c004201c0100c00c058540340001805104108103040c002c0141803170901400b02d00410500f000c002c0d40a03120000305038152681107800d504036441c0e108480300501070010b07000c1c2c01c00300f058500003222500b00c0c1443d41101c03226181da40b6001c0205040224502a0b440040d18886c81040b0049001d000c50502d04040c034400c02d40340b03050030601c5200d0f004540014501502c50f0b82e5070304072203082141030000124100480248000700c84d040c1010035444600180041e00d64602c10b412980c03c6a448600e1840a0888107001500d1107003241800c42e03940e0a0040181c0c04111410303c1200005000034071064001c0e10342d00c5140050100742c3e11141c1c1c10680700400300c2c0c1d0b203020110f20000240102c0003000681040c1c04e41d50303100e06180c0781100000440e061020f1181c0e02d00030710300c99180c5410454481c05e40e0100c40040c1c4654941410030000d0b060044022440508050840c480c000a4015424802c0780e061600105c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589963057 1250 589961807 589961839
    0x140c0403030801092c070e090124031121030a080411040605031e010207170309070603061a03040f0510020c010b0f371203080601020d080606160f060902 67
    0x46040103035001710108900b03c200800882111405e500c4c5003032000701c40350596103058070b000b41e070029a5074211b01d03511032649400d101d00c191072040019030404441c10f240e03480c56803410413030700d444d10031140500510391128004000045140140c102030700b007030302d41d01c1c0c05603103000300540400c0310120707a146ca00c0c400001c0e9504091090800380e90010b0000c103c424030348003640b034030043d9082a82100d59001c00c56400003e10752048050f110050001460b01c904044280d9410181107030042c000301072402500f00508541a410418158446142e2035039a4480b402d242100d0b050041c005080380c0324800b40307038641d500103500403d2054008030081002c104680c003004a040b00310b00f503103648092001d461540b580765101c44090105e03800500f19200c55500c0000401d10003040e407166241490f0080c103082413540041c0d80c00d03030048003403000d0402241c080c00050941072001d0003050195002080800302c007aa59400402ea461700214000079100b40c82c0740140190000b030004031b00804294401102e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589964307 1250 589963057 589963061
    0x100c05070c09140403030b0d0c03140c03120307030908040b03040f020424090f0920090a020408060424021206100c171303020d03021e0304050a0612140c040303080109 73
    0x45044103040542c3c0315120ba444c01c502625680049960001121065100107010401c0e944020340c82013181c0a082c0e0507403101d00e4200381d00c0740450703400b0344c003e48541c0d05d0070018002213960001d800e040000b070480c52410041141d010b940c100d192040d1000080c40140410780401700e0555100720b6017031003845443c140c0c690181a1200d00641c1c02903110405120a044640002c0c0e2030f0844d112001804035141d4854078801800079042c600010480740201d46c081c100080050345c006078188003546010302d00602cae02c1c2e460344002d01c09840481d81814580201600c0c114088031061104019921590150245155a0803c0d134505200d500380c1ea00b4000d00da40074503540548181c200803e00c0081d1a68800c1e00740c1540b0590f10a080030324010800320040e0345502c0150482806a0b006003140c00c8400b82181d44015140c0040400303600c21f01c010025591440a2007050760396a1a0039041c1c0e110240e095000741c41c00940a03904a0004070401c81181c0d1000090400c49000350f6032041d10b6680d41c7c4860702 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589965557 1250 589964307 589964321
    0x2e1b060e1b0a050105031b0a0503040b060102060403091203090906060210150e07050318011e1401030809060706020f0408030909010b0310030b0c1903230f0703050603100c05070c09 79
    0x140140310700d0020041036005401961f0b1100c0322440050103000c4030031303000c00b007540300b01c075542c021440200511040c04424a56690300500a00040000c0e05017914041c005e001c0314850421040c0f1020310324020548941809001840e1661060207026103810000e0745802c03051201d0101c0310314056011480351142903061080341c0c40920300040b075440711201101c2e00e07030009040c1c3d110b810848030030789005c3c40240b09003400b400f01900c05895054149051000b52a02d491103403222800820050011a8040e001c0314110082101c0d0140e90380a6441c0400180c0141c1500d100c0d1014046030018410340040003d00f50400126418030907603803555030845480c00107550440b040810b41d142480000d40d02c00c049600260134400180c1000b00620341101c1260360a00711000003900c1d0307c65404042500400c4603011301c500d6001040c03e18008806490b01c10740203041108058443d00482c486440501110f1182c6000140500078044540c1c2c000d0320300ea01c40700701100d20001200002401900a2240c82d13 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589966807 1250 589965557 589965559
    0x1101020f07031a040305070b01030b010501080f0415021614060412170115050906030a06032009040204150531020c1e01020405060403050a020307052e1b060e1b 70
    0x103e44403c0c1c00300310300200c1000410840900c0010001e56010038980c3c01160700851160b199945c8071360400c0c0004001c0c004c050080181181c5000512001031145c1e0040c1042d60000e036001600d541840d03007039810520404001904c080c902007490b0002c0c03880411268851806020003481d074008904040303404c1624011414403070b600303074801440075000301c1e4204003030284180b414a0a00b10120000b507169481962104000d554620b030030010020f0140382030555040c910301c07c1207010740d960041114400018070081c811a910300c00300c0c08180358182120094180a407001c0000004445040110419401a00419140e103400c0d10400c6005000304c481141086000e41006001c0f200702c040c050060340349001c030554081c003020813a511540f0180c00118020802480d181c00b040c01418100390403500128000d410013000002e100d00503900b14450040950b86a80c0031b0340d201c0104950b00d8030b803803034880d0030078484902900030301c00942c20500480c004070060b5520804051807441c24248007807611 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589968057 1250 589966807 589966823
    0x6010e070e0301061d070e030f0a0201080c12090a030207080105010609290f040f1d0118090b0a0b01080f04120e0d02031e0d0507020607061e091101020f0703 69
    0x614110700c03901c1c00c0d030015036020b40045a0326803510420300320403003107100900e0180c0242041004003030b0700140d107140248041d4094a807170780b40e506806031240c15192010b814001d130b42e404079000d004114102c8ac175040959640c044203040641e82907480fa82c00013416401886480b001280e0380c0c8040c46264120b81181d1202d4003017030724055594600003101c0900c424813903000080f040400302000010000d120042e81569900c5040081617040c4140c160010b0903040c103440341c41000c07502c0c04015281500d1a200c421120b0300d014060b002c010301070800300141420f40e044140018150550410091170009880c1c00d02030b6500c1c003403d2612104202e40140241d10131150a4030b00d07600078000040d4000c00030344a54001c01c4190042440d0408580c1d111340300001030186000710800521080e424038140789403a41c0741c08034a4000903038034002d034880036100e50ba481c0020035516070341e0100d003114910003840900ca2002241001c2c000c640454007028090b01450501100b280c41c007144040075070b0b5100000f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589969307 1250 589968057 589968061
    0x90b0a0e120a06230c0a082d01050a06030e030f160618060c0302070f031101060f0b0a08061c08030a0f0e060109050a02090a03060c14041e05062d0409060e09060906010e 74
    0x81300e150001403d0300705c41680500441c01c071444048c0800300300c003201c000c9125503540342c0405c2c440810559800001013500d402c880c02032910002c4201c1d50941a000e18941e195080e50700c0078203207065480030050506142a00009000303001da0021101103015603c1085078050741ca405401fa84901c2d14010080d55031580328000003806000c2c0e4075180d520075000042c0c107585030201e17011001090b400c8555070300e0f408185044455072044605502100981d401a81c1403140580b9600c00c1c2040840200028000300014800722810703400f0b01d418a45900043c0040410b03c51140e8541c03400b8041c0c040200d041c007001488820481c000c841e12001d0141c01d444580f4030350389030311004000001c181010081e0400010300e5003015240504081c044079030b440700e0a0000d14458011681440c0d0100307000300310900240c0c0d0204801004200c4807241c0020350942403440081040c80d601c102d03085000501c3c1b030a00085a007501d2910300340e1040007004100c079442e1320303555030890b80d460007403288140d41341c18100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589970557 1250 589969307 589969327
    0x403020d020d1110021f1e0c03021911071512050c070206070c0e1b07110409050f01021206040501050a05120a02030109120f090b0a0e120a06230c 64
    0x182201c0c440f07014004042c1c01041a800040d010400220360710016401045000707911204001c1c415024120316600b081911600806810402800e8542d0441907544003010055180240c04541c00c0f890440e4481801d42d82e180c6018001d0b00440f03075520006e1080c4000412016512b2106d049a00040c2d140c8400b151000e1403010080d2600030544103894038240080c000603180e210141014a01c02c11406800c5824442810040a40181004032400300e0700185c3c446601160200c40c07050360400443e1500c040727108085400350140c00001403a41c4119401c200c013074081903015040d0300303a0141000c1c3d01901c0d20000c12003983c0d400c1c02000c0c1c1c00300d40c49004104034544942952000210f010070355029001540000b421200009001ea4810402c040c2d4a800d4540c01a01140041401d0030b1242c4660304010b051062401142c0c80001441146c29220301c43d583c03007e594542c034010b034108580c4880202d10700400901781c800c0c40c1e500f080c41801240140d4400640c5581d10503440c01031000d0516803000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589971807 1250 589970557 589970569
    0xa0b12070212043b0f0705040b1c1524231303140d080106081003120e130e0601061b030806060d090311160e0114011e03050411060403020d02 62
    0x20070313424205510300c16424002c000030135940d40a2000e80f549000b030303191014012a00f6040101030004010082006104500500040c2c9071080da80700d00d19a41c000d820711420b00100b81c1e0355035072450b10130b00034400191410103034424072050f032a080703006185040c0344909946494160041c0c0f038201c0902d0281d001a810020081c2000004e442d154040082e03aa44520309180030300724405499030000c036580d247d180d03085000640100007504d003101c4a494042c50030b42002140b80001081c440300c0d5907200004521a0155001c6400001c01ca0904203000d40c0181000b0001c00b03072168458003444000080e240e001c0d007040c181300c800f240c1d98480604410340d01111203d800420460340700806014102d41d01c01940701e99403c7c988a51202c3d502410b8030006540b4000e00c0712400b98460008010501c040100310b030302c1c00d04650002d01904000c3e0703990401a11418461700c0c0321115841c0d054684980c065140c0c00050146e40246081e004660340301045c001140700b180400b03900062a0014600141000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589973057 1250 589971807 589971839
    0x706120b1806040c0e061b1e0a020405010617040b0a06081603061b020601030b060301060902040e070e060c1f0b030a0b070f08041a130602030c070303050a02160318050a0b1207021204 80
    0x20b035023070b40e0003140070301c00d003017000c03191051741400a074845280541103081600c18540503146c9410007407003090703900424402d03020000b04018002507100c070104291040c0c0b900030401400c54402075440d4007106101c4200b8140452100b03540603401c20f526655007030941d065400b4444a9035001c1e00d4560308603140c15850000260019030199698000010003180c0c078406030025202200000c00e580c100302c00000c051104031503180344102020403050744010303400104112103400301d0160000c1c84000750b002d14000d03e10000840d415010b0060102c00700411018094411781986c0c441e940c0b20305915504664a00d001c0381c0c02401c076207040307441e275125a0b510500c4551141e90405048a81c11065850900b030380c10907075001505050200300c1c00f081580500a081d401200450300314148095102030b00044401588090140141014100301030190303142c103180034202c0a0604090340387d40b5969900c095200030f0942c00c59680340000b0a10140c0301103402d00f046455880b403681020306080340071100e0515 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589974307 1250 589973057 589973107
    0xe15010b130906080325080301090c0206100501120b01050d110301150206070203270a06021f110f1e070b0415020306010801060e040213080f0f0a03020706120b1806040c0e06 76
    0xc9808100c0005007c98010741c040c2c903a000011030700d40d14082000c0d19003d40981440740c2c060b0003580501099074803c001301c0680f60310300000306c6e00d03800e0540142c9041c844c580d1516891410140e10303d04061550000314121001c0e1210540f02c8401e540f801c913210041a100800160420020b14120b0400c000808c015030602901c038012401e01d22002881140b030a070302240140c3c028000c003080303d00320070400c203000783c046180510102c1540300c1401c3d582d200b0b1a009800c8450f010030504c010404520710492000f81f145c1f9640c2d9602c015061800ca05072045a0071504002c6141c010103c0080c98003c2e81c0c05070406846a00082c1d003003040a40d03800701491080ca8006600f0700c84448482d01d0200294010075803400070300306000b00030440c0c9043c040c3e201899843d0343e002080080000b40d001401100320303812842c100003080f44030320042014141c00c401d009d500c61b80354170f092084c01600040d41801100102c0b0104501741204bc000e035028105034040e41d602c900c041c064070940c441d61488038210700303503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589975557 1250 589974307 589974367
    0x150e0c070f0c0503010e0604060b060a08010b160c030302030c0d0302070f0201120b10030603021201140a02090402040b0705010213050a050303090f060d09051c03051006030e15010b1309060803 84
    0x41c80d0f4001c203013154461152031865501002c180014400c240c40b65000302e060549000c1e1400d070307410b000589000c40c11301c41d4401c203840004041403515410810754078526400b03a0004400c5a1702d0500a503213030007268410f42c1724081e030011102902d00a100700c500344bc1c1c3c0488400c165661035001520700f08014a00903076255200d060f0500366548101e00d08884884c20b80300005c580c2c0c21030051083c2d10392840c1000c88140e14000505070001c1c8842c40880c0d020881900c0940d503983c0c2540810081e004030750107007034040b4002c10f0503001c0100640207800c1d03141140c0c10b00414150340b0400c1224203001c5120360780e050340081100059034100850000d11034540500300c01d1801d408080ea02c3c0c00c07100460303000d46258100c11004d05100304517004500141c00f0300d00e0188500c0c10050101c803400f0031144145420b00d030b036918085489100c1800f4046849a115009240540e555a010401c0e54030102c422581d4440d0b0120103c0c00820a2103002c007690508c0e8000c5080042b20300079018400350a0f0914400e02c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589976807 1250 589975557 589975559
    0x40c02011409030a0e030f06011703090a0308120a1e0b04060e01030303140f0708151201050a0608010b060c0a0615081f0e06070206040303110c0a0501150e0c070f0c 72
    0x191081e48060040e030564000b1980c807100c2000c001d00035080c0b1426244640c110b8050070444070030001c2d103107044d504140c103100c01440031550454954400d0101a503007103440d0660001c207116484d07000d03018401180d400c2e0411a91110110b034102c1d003140c441c2020b001c210103024190190f09a000c5810b884002d0000102c107a15418651065a001d030b01c00c030000b0341c44040c8881c00412082d032447d04200e180707070100242d041ca58009448400020300402603c0d41c0e20001e04100d82c0e0b510309403801030340c20800130005801c0022199011b040701e802011525800c1c280281c881d0f080010440340350ba1035800c0030388152000c50743c620000d022007031802074680a610501043c4054180203448201c41e0b0a02d8440113403082007104029644414891035040d00b00c1ea0810503c690007080741544168980340000310080c04910120450140010b00c1045124203481035040140542c04805031412a07034082c05415580c245000d01c02504982049007803805100c0500011078080506c0d4031030f032042c40001461 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589978057 1250 589976807 589976831
    0x209130b19060f1403150c0a1b0803130b0115090b0d020906041202180705090409030224010905090d12200f09040b0102060c0a180b03100807060f090302040c0201 71
    0xf20704680c025a44910710340d4000181450200000d44050000600c0350809280c5208054500c0c051134200c1d906001203014441040e80d602c0c103047d00c80c0c80e840b001144c0c0768244180b004d00c801802840460b807000c003003030002c68604014410400686516a00c029103582080d05000c150303000303124a20251a02071000c41615aa0140600090100e01c0c5201200441600400900e541c40c0711103a880224a0070910403c039501104a0700131410503a4003160403001860124504000c0944154081c0c0c4030200115002d100c8900f440d0403914603a50510103600c0d00401c160303d600b80d201926000c941c42e800206a0049960002500c04240072210b000c15694102d02109543c412007007800000400201c0c059246458407a00d4401034003807004000c2d078034062207900003510400321070206001c107100e425442c013010f440d41034010b024040c10341ea4132405d15a00910000d07059000c1c11200e13008103140491010b11468981c45600d00694840300074602d0740d002d101c0200144100c1000715500c401c1c00060b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589979307 1250 589978057 589978079
    0xc06022a031504050d090b0702010c1101120e0703031404080c0913050111040510030902030606010e03030f04090203070f021603021002160f06020f06130204050c0c0d0503040209130b1906 82
    0x46103008001801c00c5005a40001b4800e085c190014040c811003480f50a015036448001944181e0703012070b2008070a05440010780b18480450f54080e5100d017894810080d0b89804180141140d203e138440d20701c0e403c200703c401352850281c0c0c006c2e24006e03840121744100354580018600e80040d407041c01a41c1c00b003066110756082d2141d29100000c0c3c1318002900308030a040218005060b2000d901c0c0810501e02e040e400251030b0a40580113504121280c00500f9255605104803200726008a0300c0f50b942c0c0f0781c1d075002c0e600a50001c40720800800d040c3c0041029080c004038400000070b58011000c640c440c1950300b0000c420941c008440308510450b490400700e03a02c0d00d0002e1020700060f003258540a4034151000345080500340d0508550b41244050089034043c2c846080f2506174101c40c081402d41c0c42d90140c01c0310f070194072500b441510900a0340d140d0b07203400c10003c500a0b80290b03034090a5075169485002c0350641300c02c00401140c0b1100004440c100d5562031008100440b41c07010070056601e82d40010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589980557 1250 589979307 589979311
    0x50d0606031b0f02100519020d0f0501290304032a060f18080a030b06040909060c0e030316020a050316090c0c0c0303050d0204050406030605040c06022a0315 69
    0x70907540c1c100e10101c01d101826aa05204807890429100e02400c80b0007521003400340340300d80c595910f81010851a01000c64005200d0301d41c0380d0110744a88404906001074290380e85200c10040c4bc10001041741e480c0280b0340503d2440c0c900c01524030640042c150318003070313000030016001c000381e2012040001d00c1203084041e140c00308034001050116107050070741c00c417010303a8003400c02d1f5440d00011007840004403011440f2250414944c6440c1c6500010503001361000c00352081e800700c00082d000c144244140d008042e030a00511041100c0c03408204255000440703000d400d81d0540c41446046004100f40c01c0f02d5182c2c91010704400341c1c1ca47d580c40420710f0160403100412110803d204280f09500317082c421051500f40034580802440c1590301c86141c1d40d805800068204640000c3c400792048168048400a12000c1d000b006140d60340d00304103000305800c1d82d0444072038071342c0a4009003041c4002191a41882254202035115894030302004005100d01015034140c091811405040314042d01118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589981807 1250 589980557 589980569
    0xf091f140702010318030e10030e070e09071502060121110d050a14100e0c0d0b0403091211040e16050d0606080a082505031206010c050f16050402090619050d06 70
    0xd14600c0e41d607c00c00c006400343c800d880c4101881c080514000301c20002e5a02e0072074181c9158403203180c4600e4070207401e0070a503811a0080c03180071000f185800c0d0340080c2442c100c48038500241c001054030f4405d50001c1d402003402904440c0b544182400e1413420180c002c1c2c45500c98012694040c60725990a80c580701a4076441c5d00c0344d000b4009400c414019401106c0560681c500a4007903603480600166001d291800080c3c8001e982c10b0001d01094081c980010103422036059014086240385804200700381c142c09a14002d500f00452802c5000d4001740300c0c11680d0751410f42441c40c038104424842e89002c8c0b400e00341d54040e00c400c0e002998502c2448101d464074050011150f560b00380c210303101401c401c105040c811580c0307018074000202e040803040d540702d4500310714030402c291141d02c0100c88140320f4000c05171950048402c815a80303103001500744541409090701703441640e40c41d02044101d00030040e0050700404100962441c07201402c2d004900e11125080c06800d1031185003001d421908660002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589983057 1250 589981807 589981817
    0x140711070f0b0c0c191d01030c0603020c1515011205101401030207080f0d0605010212030403030515090a050f13081c110c060601091431020f091f14070201031803 71
    0x10b05c940c06c980c1910807007100791007542c28a15495036039900d000703800e10b00c2140c08050340410300c0f61303803050b06209002c1c01803803d6840e40907034203101c40e03800701403500000e4440c0843c0740e121035640910568002c0f01c1c4101c00f5000c0851075a8507081c4054406514940450f042590130080600054016809010140c0028260340c1d15050011108811a501600650705541c002401098a10130311401c90703500641c58030303010079075071a02c0403070041c1000e00c040703a15070000c19003042004c59030f03141d0301c06071142c4c0324096800e100751643d029102c8008140c000142014000b0001c05550311ba14040386409403c8055000903200e00c0c280085a4a4000c5040002543c0019092042e20341c0c1c002c0744c000c044c000c030b610001d200c0340c20000000c03581e0074807500051480700c10200d1427024102c201c0042c0600400d1600555030341c0c04c9507064011540c00040c1c018401d9200c2020f1710350904079466003003758041c03500c484d158041f1070b140303c1e010368124234012030405898404510b0b041c0158050305400501c26164 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589984307 1250 589983057 589983059
    0x70e060f0f040f0f080304090b030a020a09020a0206060a050a031b05040905070905090111030a0510090e0a021f08040b0a0e0a0606030201230a0302070f0501140711070f0b0c0c19 78
    0x80c075440c0d16515489010f001300310325000e00101502008550482d41c28480014000c402c040c040f07810325030300540296004000780f00004044180b0340003040112455402d455031507644508002c040c136031600481703030400c2400c101480040d8102c4132000810508509800001c7d0791040098141c40c0070620444150300083c400300aa41c425020f00c41c2c0040707240c0c000303101e4020101c182d2003444c0801041250703002d03100c0011407981c91141c187d100107030880d810180003844101c01c040d0740c0c400284008a008102d40703000341c031203803005001143c400e406556a210507910359444170b41c450540a40b2828082d6506c820a140d424010090201658840d00000c5402071442c0005425900c0c103403001009000041240302c40740241004a031201b0380c06007001616003200c0e081c4284030003034002c00106291b10307010020012244840e5124414920307551401d5040c664441e0540e10b9011510848494a041c0c07102444203110b58400f0b084103029000480e21031441c13900c0004c00028010254225001c0640c01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589985557 1250 589984307 589984319
    0xc02010f110c040c030b090a02040819110622060f030606021b060309010609091103010501051c0f081204030914010203040803120705090604080d0f0c0209070e060f0f04 74
    0x2191038103051030700704400122040140140c0720700c2c20b03444081c0302d1560340482a2009020364010070426002410f880300900d45011a40c00940c0180201041d40c882c01440c01888007044201c0281c081d0b10030001c080b0683c900b406d100301e6400c4406404610b0310300c4011010a050450070b510010305896903405402400a94081c3c00c4818035003290045400ca00c13080310950b1381c51101401d8450050350100d942e80e40d8070081c0350050081e50012580f40b81401e20b00003e10103081194546544210700820080e6030b203100304034000302204141b0352041000604040810110107002d4a01800380c0031142c44e209482030f1280d1444011601180481d01101c41441410800384030b001c61100d0a000030740c1fa00381800b2006960f40652091414500803520000c0c641741d110f1400e507880040d002c1c010741c0d103690b200c1c40500d451303070400340400c40080d081c4807401d15942e02c10306032074000c150041d207010305645074807004403100c41d200b6131001d400100030406424482500f0b0000c1840c00400076499440e070342080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589986807 1250 589985557 589985567
    0xf0a0f030501170a0201080417070f060608030702090a020706180303050411030303101403011b0207080d080112120e09090714030a0b0c030406060b0403031d1f0e040e0d0c0201 77
    0x28000322407251580183c015840380c0012003001079030702406c2c110290f5680380313840c0b03000701d80054a4210900021031480100900402c02c6540c1910401081c8503203038441160990f60b01401c2006503010042102041035042554010700606001386408141c40765013010310501c0100c8058110b0002e562601040144031601c50f2250841600300c0242d4030310f0520f4080d41075540030341d0054100e800005003000d6590383e400d43c00f040d150101c400c00381c506c00c00058000307522444203104100c1c07940500b8000c61f42c1c16100d215480d044e900a402007802d0200c03d51642213a0001c0c1d031101900340009103600382d041e41d84014006200307001c150014910903007801c1e00001820f030381c0c4100c6030003030740500740303410000d03e0400000758170448441070291250b4403820b0801c003404541c2e20140e414800050084140340e0f000c184001101c4505013168005000801401171400c0c5220062032090b02182001803064825001081c00780802480410154600c592f800e0034041c00440d0392010071210a103c40841d44c000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589988057 1250 589986807 589986809
    0x21030906060d2144310c1818050a020d020d06050901140603160b0a1701080312070503280207050f010e070b070507030f02060f0a0f030501 61
    0x10340d04100180c500c0d603111000084120b2051002c452901561000c45124402c070360303103104c010100c80c40c055500881088948008040d54941509000020072580c000741100030301a10004003050a180086220414503009a068000562a0034104007002c150412500b5000c3e2120b0132034542482d0084c050380048441030300d444030381100d00c42d9102d40482d002081002609405441302000815a8800145a080e182c2c00007040c00345131030284000a501580109588601402190920388413403040603034600101c40c0d02c80e03840a02200601c002e044501c050489000f40d4203010900248200710210110760036000034031980e1000c1036041c89000b105034203c0d001091410410710b9410a00030b10030240c00083d500154450700d5003504c03d40351029a0440341d410340c00c841907030200360580102c07038041c0c05107040b0390301c2c00e200d80840411511249000c40e001d656100c801859403a00c0c5681c0c00c1d900a44c9004180d910120070720031540c0c3c400d1b004000f02040c8013685e80b44140380c0e0160501900300d50301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589989307 1250 589988057 589988059
    0x10501060c0201080426032d0c071b09020a110d03090506040605040f121e0527040e07030b070908010507080c0d0f18051b030d0f022103090606 63
    0x8032820301400350f40c0000071950040d800016001400e074038400202020079510171507200410300001080f55000c1041003680c54094441501c03607808c030307000103d0b0400f600169640c10580d20108030003000683c008000384280b070701040c0b214411680d80c038641802c9070002e10408000c03c1c8161412b030b10306102032140c0c44a404c00c038141000181e0282c0c4400c0c0c1d45100080c40203007015070380c80205040c840341c1c2c0b0344c400110347d10500641c500203164400030101d481411071080b5000010002603000c5010380160341520380c0c0d0006400007a982003200c1034840012030b80d03868102d039695522500c484401d000c481c018501a01101d075550070903400080002c0c201e0341c001c003036a9141c10140078045500401c480e4002c0100c0e0406a1a0017884152000900c0c2c02031860b4003503460004041424801c030307d2403542c0749020b2426140621604441410000c0c0354120866058012105080615008030326417420004180b0484501c0c85076409288901040c0340040c0341101c0c804800c21001f15020080b107584a14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589990557 1250 589989307 589989317
    0xc0e04050c0a180f09020a030f05040206190909020a020115060f170a140f07120216030c0804080d0c0c150c030302090f1e030c01090b09040911040e0f01050106 70
    0xd40002141d07000c0c055880a14104810202d0030a407004542c21404040c000380c0c0c101c40b400950712980e1500960203412030501007420140c1070b5544142c58480d491089401a00341460440260801c0b6401d0a40d0070750b05041c044191130200c1d0403011032015000f03c99454000152503501c640681c0c400380c0f08d5610070404c10003000002c1c44d61700e600001060354520110340c05480f507110904e01801400013410002410381c1103070104004c801002640e14082c0382281c0301d00c40d5408000080354103038400d1001c2d240c40e0b4019850f9000c002842182d04103800e034004c49204d42007948440e01c0a0803c900701858200040b604120301d818029299000c100030170001050405072249104007906030840114043c09043c0e0200340404582c4074901a415152001802501007213040802d802140c9900c00d005d50080c03103141841c51281d4041c02d04442500c00722600395003000303004020003000d0710003400100da039034154143c0241282c6950241410752103101d00545515400001081d084400581c01441001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589991807 1250 589990557 589990561
    0x111030a051c2706050c042601020c100b09010b07110409080405030706050d0e06060916030f0e06090d051c0e120a05040321050a0e03120301090c0e0405 67
    0x80e401104403010205090300522640307411030381c0c050040c8020a06408100e911401c5a04003c040c4001c0300350040c8290000c00c4151540d4620441074003660090f00c0d1031a05048021840340016040104880c0d20311002525240c40b5101040c100450f80d0048004280c0b00c44544181e40f0b404000580504100c65150342083c0198131000d11682000303401a0085540b0310300d04090120040c201c401404010701120201560303100020916801240340840952a040c84e50100e000e0100704540141401007028109440700c2800c581e501403000400d50601d41d0b02d4141d000b01e20200d0003134051030030921001c1c100b070f450203840702420503994191400070000c08011080c0550340c02c03c0084800c0d4801c80e030001788850059589454010515100d03c812035002c2500910103a111000b00302b0391b80701d00d5205645421068000312031400d20442030000c00c000340040300c0000c0c03084640c0340c0b035100020200c40b6030364071420040c02240d00a804c1091019151000815100d0304907809102c0da100c2914100322038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589993057 1250 589991807 589991827
    0x3031104120b2a0702191a0405090c0a09060503100306110301050f030a03090b070c03080c030903071d0703020f0702180601110703020a0620070909021215010302040209121b011103 79
    0x40c401c600307001b44100070040041803100c140b0400702c0301600b204034000002e02e0419455141f560403520441e0712540c40200082e8080d2220010b5550280c40d41c0c4840315001d0a042041d9a1030300000c14884440448420010100c0c045001b4070020224006074150380c0d504140510000311680c52038503000c0e42c000710300306000950041803401144e200d450341e1a1541100d1a000d00010400c0c3c0c0050308030480450420510751020005080705401101110f02c80c0e5542c6254104648100d0b11009800502c10300250501c3e029400038103000e10803580a618142c2103900250012130070140c9103401c01445404c001c2e00356080100034050014110007420410703c2c50780042c5003d2403a02846080008003100000580d45d07a242c095602e0b00503006540840340ca40c00300034002c100e403400c142e104d09029461040d10103400f19094426056411504400f80e003141c082c44040d41c80081d000303800c8401e40c3c2449240120600031054840d09520340701004440c6400010a00546102c502d10150000c0201c0c81c0c0e5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589994307 1250 589993057 589993141
    0x12060b0c0a0605150915030f0a0b07080a020708070b060f0a03050714010e180901110405010f0e010e13050f0a02120f1b0a030c03060608070c03031104120b 68
    0x34850740014003003500d0380d072410b84e050200d4180c84001d41202507441401181803004600c0e0355580d0003501101e00155650b81c041d9600ca00c039001c0a0101c7c002070707022411281c8584c04042e03002ea4008000344c6030103402c0e60703400074640c003c0c08199000e10a000c1408810b280000c41000c40e04011203d40c0c00c150f065403182e5446943c1e0744a031001c6404c89841000d142d9001d01c9488142c5040140520000d0300043c100110702d07641140e00c50703029403800001341e2a442250302983c09840e010b9640c031203514060039081e580188600d61007414403400b83c60a00c0e01d42d4542840054440f90070b140855141010f45003c905800041d1581800314014049412490300700d650659100303800d08424059510340ca400345000130f00c00b01e0b4003e05a000091241d035802e405402038815000e240d40c00b0002c0e82c0c1d4031013080311244c07003d03101c41002910b4034003c01c000c00c0c4030790440f5455450850081c5c1c5400e070b540102c16240201003800b1503258010804100074181c04403c0741d50768800b1071452824200d910864007903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589995557 1250 589994307 589994323
    0xf0306090c0903030d0506040b030712060b0126040507080d110c0d11090c0903030f07120201050c0a03020c0c061308060714041a072a0609080607052812060b0c 70
    0x20951b80d440051090b40d5030343c01543c40f000010f41514501526801041d00740102007106540003410710311a560554822410220001447d04804100d8031002034000304030a030207041910f5520a40d08045004402031024120f405041e85a94011200c103021031402d0000320f001c10b520490300e42400c4000b090181c6607020050f041164007d007655213003440480d5034004d58454580503c00411040c10f0405104001c101c0a4050708201c03819154515080303080c0d550845004101d05401e21024035900c3c0a50040c0400c425100d083d1200c0c03584850102e5980d8112400380e070000070440c1c000300020030080c04541d412442900e085026421151000c036040d215134490508032a80c04444000c60100090030303504140d501044c0000400c54000000c00c9094580c00312420441d02c1040c0010b070307240251180c4003150b000340d024204641d58190305650070f410040c00b6400e106180789107400740401d1200c12080000061305c52030060703820402e1003000c07210300d07400c03028940310104a29190001e000070269 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589996807 1250 589995557 589995577
    0x10110a0302031906180e030702030a150906092613140117040c170109170a0903020d0501060810050106020a02040e0c0d062f07030e01090b0f0306090c090303 69
    0x90390380d4a801064004100319422540d001a2424202117500000f0f01c050215030b001c0a0800d00070484c1c20b12019441e07216900001f503040d8003511180340001c0400e103412190700005400000c014a113904c444080da50104400c54140205030040090318510078031801c0c06010b8a0191b034108001d0710202000032049003d0542500c0031003110401e103a1003160385244060489040703030303900d081c00d180203245845c042c0180703052450904682020888144111380000340c000c3c0c0441d40703601c12008000c0301503101c40110401c1106071000880076840e190504500244a04000a1417070f1902c10403a0a1146501c4414076885c10b103001001500c5c0d00082205103942c044500040d20818880760900d03018010001d1500300c100c075440304050210301d0b4001d1410380c20600d2094540f15881d00d458202201c2e030544001000000c0c051200802c0c89140c420070312100c1030412044c442e44480044800780c2000e414086500d030000200071003410004032560300240207540312810301d08801c00103030b180c0c003800c0d03820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589998057 1250 589996807 589996811
    0x90f060414121602040b01080c0703050f070b091501080606220f06090f0f0504170a030f110307110703030207090c0509040c05040515030f010308070201020a14060910110a03 76
    0x400070a01c24000c42079501c280140e5641d440886500100324140803240580c4500d1515401141d103500442913188031b0f805002030300703180c00351b1039509954940107503d0700341841405000c440d0000320b4030b80d1928001e100b9000103019200d5603120380007031114140c00075095500329006202c125201d000307901c81000c0e100d140740903070a00ba05480d03100400032641000301903824042700150301c0395036601c00c5c000003200c11410b01c014140d0b526500160307070301a500200301003690020010304100d00b40141c0f1200901d85008145102c000400d14255030580720001d0705800300005101d082900070304030313101c10700c13035100600407441c91601c029403a18482d10411100607201c545802096114130200c0350f50f000700600800401c81c40c5d000040054001e4001c4602845046030300100e000071000943e0b2280c4d03214810001268255502d03c08035270401d140480c10f51165801e0140000c1040400304030006900d4004e0180f844d00d800c143d460500010390031034030a4075044900040407000011540d0103407103403c2c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589999307 1250 589998057 589998083
    0x2030a0503060301091205090109080106050a0b160803010f0f09090b0c1305061b07050102061302150f031302040c050f1905070b010b0301080c0f180c040b130806090f0604 75
    0x1c04e000d0314100b04020042402480750085c013a404c440601aa42000c5e6102d03200142c03550101801c94445004165201441901c10004a80e1600048c004922450042c4c0c280d542c0300d41d0ba25060340c01c00c1e000380038409595072060181805900d0020300078050b1403030500c4070136030305d1311b031042c018401415101040c18002004559002070740848001802e0140501c0e0355a201c1444200011080300e810221a001d01c45000610b58800a681d900550030661851008182c59003000707114004501000010301c010320035949402c00640240d48903095920280307040800b40d1040104403a08248108288041070190516074400001518440d00c039410b0201081c2e030703681304183e50743c1c050000010420304140c000480c104583c100654101c1c2c1000040712401c0310f0141c1045884880705400d01e4002c00800101c0d41d6a1000d0005035810440c91680940303044c2d111003c8116aa00c10000e01070b04082c0c202042051420800200c1d03408898040036101202e00c100a01d900d0b0304015001402c8204843d02c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 590000557 1250 589999307 589999309
    0x11a010e040f0b0d03050c0c040501031a190603120206060405010609030803061305042607030c1211010e161d010e150d032616180503010e0c09090d02030a050306 71
    0xf01040f1110b90007042d0403480041460000c21a500c20020b0081d1402002882091400c0600699050707c1c0e005a1141c1c16000c080d0042003600380050584101e03c03200703c4407454000c13403482000c0103540200a40d0000c60134540340640352001c068aa14000d51a0000400100764424008415658054a00f940c0c83d00c5200010f001a10384071405803005103414180410401c40b4107111a13510710380141109101c0b02442c02e8406802580c2019011900031121800081d00c400d00401c03290504d42820030341c00c9441c480315401c69000c0100c680c4258040c5450341070040d40f101e90080140100d0b00000c1c0c0c90140641e05e500e0a101c1886507000800c00d0201050401c031404000c10340442004c0c21036040c034007250400500014665203160131404c0004020b50303041c001100c2c03480c4510a03607140e00c40c2840d148181150840404036003103c02d049010760201d10350781c0c28014052a01c060f0307001800c00400500811108c100302402c1007010b80e0154040d41c0c003658000c400d440c00d100300c41c105103490b0b59940c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 590001807 1250 590000557 590000561
    0x1812020d05091203220305070b0306030a02060901170103051e0c030a060213030b09011a0303030928051002090f010203180f040e0f070e06060702030c060307030e0f03070302011a010e040f 82
    0x120080d40170381070b00c2c00710325841a01aa1881e085a00510483d0029960381c2040e400d184000d0740c0300d03078158002415083c0903040c00d400031f042e80c0b1010724002ca0304929415500d20740c101c0a0300221400e421100c2c0b007013a0710482e0882c0604c42140c0c800507101c11001c80002a98400c01000020202d0f41c0120f44600403074000045080119040f8800440615040302818000e02c5180c240794050b214201e00c0c000c0604001041d02d1183c805000180540f6005900483c1032021410895441262404401000400600c0050b482d000207400141e01d9170f50400070002201c1280e40c0032030441d8424401654074841d01ca4200c0985103080d551825070b11014800315000d48001816400c9034801da03e1441580c6000084c41001c07038410000410b0191184020069140308030348029505601c1110314020301d103044002107400c4099400c00040446220844a042c400304070307000c41094001003407a8050540a0090160300b00c4003d44203501a80007000207461100303400c18841c00341d40e540a072801048055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 590003057 1250 590001807 590001817
    0x4050c041214070f0e15130e0a0209060609031c050918041a090c090915010608040c05090f1305070503010f0603020427241812020d05091203 62
    0x100e0340300c0e801c80c5079040400011a200000300b415114540d80040c80c60000c420b01000d80d00c3c05071030086140ca440409400d1007034503941881d808040780800420480c01841044007150301c00015000101c414010001d003200d005105074050b003c00c00140c1540d682c042150600880c2003d852180c1078407410b4100c8142c0241d000c60798002c2e011980d208030705a8108000c911030782c81000040d05199103112403007003a2000795586a17095212a5128000c2d1800c80186c943c017407124011180d215500f00c248521040c803c0e8000000b02d034100041c0003e000c13031b0703503000d002501c0c0959100b8131600300300f41c51018284005140d640380d1541600e4110401905010780401040020024803c03001c03a15001d41c003d00881c8400c074480d6140201420044c200f150400068403600c1c4c4590081c04041e807240c001154107a4004c13400220404504100040c0504c00c003041c440a00403240c561042d1840e10340070150040004e0015584001011166958020200c99482c0425148460104200104180756000e5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 590004307 1250 590003057 590003069
    0x2401050703031503080301080615100c05280201110102030405100b06120705030610021606030902060403120503010317090d080a0c20210d03090c080d0c060c0905060904050c04 77
    0x9400f400418001000080d505035103003003055a0300351326003030b40c2407848510b03c245898000e130300300188046e801d018488044c0c10a01400c181c400b41d091614a44040200180014040d028050740c01c0b401d55a02202c00102c40c40a171000f1451801c01d40c40d8940c0d00c0c1c6000d00c82c207082c43e4540ca1114170380c0d100c0301d081d41e08c1c080840d201d0082d01c0c2801540900b494008450b024002c4201032102400c0f1880041d25a0b40700d04038603c07540c0d00a00703040e001c034082e0002410580e04a84200b00000015001d1402c2c0309500e191961140d4a0f0350442c1342c654040a480c1c14140a811400d100a100d02da680071008866280d1017106e1039950344042c0b43c01d5440518296024104010541203002050071500c00c5503150a0101e8105112031281c40400c90f50145652051083c0e50101a00c14650b6000c4c0e440100785030b010310180b05129680f46856490320310211030320000150015681d5040010900600070003007140d081900480d400e080100d40c7e940603000200d0f21894480c2e0104084031030100c01c80b00034200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 590005557 1250 590004307 590004341
    0xc03021e0405090607110304031a060102030c0307050102190e090f0613060611120c100e12030703090c0509070e090421110d030b0a0504020a140d14240105070303 71
    0x142203c119901c409046454001090188810310702c00540481114140e0b42d0011306e10001d40f003084030340015100000c01d03142c10751008004460f0391510401c040c011301071040e8009a51080241c0718081d2400e603141c000313000c0c00940e00440005940d0010440c1e4010500780f4800d11a58510001030f02d040032400c0303174a5480b072400300302042c800c1e4040340984243c042c2c1000c94403000d940042604080c825180b402c44e55401102c0c040b40031580c3c542000442e015030800300e03022440c0d0002e92540941c010740740741021a0703075881710f402080250000f02004082c125420110303444d151501070f009107045040070b0301c1350741060002000c2001050120400480308040903450b205480340c050525080c00901c0c40d500c1c89981c0071401190300c03900a0301c1c08504094220160545040d0910019400070b035032100922401403c0850300b04400409403103c4034500401041d42442c010614104030005080601044005000c02892054024902c00d100360203180141e03441c1c0e0030b418214000c100d0300040b690208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 590006807 1250 590005557 590005561
    0x40b070204090c0b0702040b090402060702100509040f021b010605033003070201050f090304030c05060f0c060a050106030605010306030528080403050d0e1c02150f03010f1706040c03021e0405 84
    0x2c407080016001080c807d4408100d500d415008111400a0484000350721540400a08005017010034065040b00d00c1800c005007030140c01c000060546140034808820554042080400350f4180c04038040060804030082108505000109840314803c0b050b401c101000064518062064211108501c84a10380807503141e01702944000e02a01040d206983c0d180c03008400b0801c060400b200720780480b039008a0701c3d003d003440c00050190780d8000c8040c076030052806001c2954401e000b44a400e205250a010000c1d496050031000b0381129400d811aa041620307045007800080e03800a0a2640307030011440010b030100d408042c03020300076000c841c010403691012900004011002070110a2041c981e211044442021002d200c00000f1100c0c0d405c0280444109480142c01c203141d07040c03103000404a4403441c007041d0000c1b00d6602d600c281c1c800582141040d408000c102c1441054000e600604d9002d08503604050311811000d095074007020b403280410100d480080b6010a2403003103a241c0c0a04180224 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 590008057 1250 590006807 590006819
    0xa02121803030f03060102060606040e062e020a051c050301140409021005030601090b070506040b060604120c18020a050f130918021302041511120f07030e010f05040b070204090c 78
    0x4d80050ba00a80544903813000318403140740020580b400d0302c20720805940d203507170b41800300f1074091603440386204010381064000b12007941c0030050f0000004079070010441e400c0c09241440c90300403480701d00d0f050341014201011020ba403001c00c42c0c0c1101c0c0480d030030078405558940001c0003000d190a009500c502c200440e20702c00340d0410301540c0b2030b00c2d0076200c1070143d541c0e4820061091040380070080554108100150000b80902c0083e234105402400c0341d828261698074090034000140c4041d00c03c47e405100401880c034141c44249900049544150309100000c04c0c060308501950003080546040030600d1056080c070404444002e100e01441442003181046501c46203031090074050b8018010104504003c42d0b041c02103400700e5120005030340294110741c40468020b00030401c021320307d02440d400c1c1c940c42c0e400c0700042e014103002c42454680d540928a400f40c444000407043d00d050040040710300107502d070408180d070103c0707048000c0103a41c1c1000d840028010481c1180040801d843e4500200305 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 590009307 1250 590008057 590008087
    0x1a0603040c0e0c040b03070c06060f0f084e031008101407030f0207140327060412060b030d09050307060219060b0d0503071b0b0a0212180303 62
    0x80b20306903a44a01683c481904a10f00c0740f060703014015580408002280314a8418a620840c1c01c3c000e020000e6a2074942083d1203180e19698071030000d030b012a030014420360354180190b20740700d1500f1140c0d0000391030601398009040c04100e11949060f89110b140000c54406e0982d04420700d0071004056503910b0300c00f02d000118000350044020741d2141b58000e040b2007195202d0000c80c0c108000000c00c0566a984045001e454844144100a50240652000140e403140001c4004050320301840c3c98510301e00b083c450303031400400e01c1c89040c0d460302121207540e00c6107801c0760291380585040004030a107508103c00900b00c5d1020f09505071007403002141c10075034050305150a0b90b03803c82c180c48000356201403c0303030755061041069074003940b0300d1016400582664080340e0000e60190400700708202607150142503410400d0192209504410b6094500b10f0058102000c3c0155040c114100310486800a55801c20203c01d001c01e080300060802010031407580c214030005004084a544140000d40040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 590010557 1250 590009307 590009309
    0x3140423100c0e0405041a070203070b0a020409050f0f0c0d0603050d0e130b1c020f1c0b07092706050a0801020d110c0d12090605250f0c061a0603040c 66
    0x20000c2e0820f0341c078100f185414010700740216003249404017800980380415080b80030140641d030035031104104071800190400e40b500e100d031648200c01070719207141581d04020740d50000e04040289151a08102007404e852175490f4002001303240c21a2107001c1403512030010701c0c16400241c254443c21540c20001a40102e00300540ca000f500c5940710100c680700c407902600c0d10710030b0a40d400075000c5120400880b00300100d0700307202d00007401c0104411008011689160a413800c051140305a940315901307100c5100e0b4141e0300801c4034580382050910740f98400841e00d45041c9500c440b0044008048400e07200c03604840c01504c401828524202d6692005600079840b0044050585007003515503148840c3d80c1c0c0548500281c008054003080c200b000c0120b40894103244184440b42d0740306030704c1022905910400f803140034440c0600b8a0941c001000340081500c080c070700340400000140c0c02c00e0321a40108010816a44250f0108145410400822085808460390b5070000004800c00c000c1c045003100b458 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 590011807 1250 590010557 590010581
    0x10b030706181d0402150c07031b0f0b0421030e0609040f060b070b060d02090c070606090c110f160b07030203040e07030209010810051e1c0507060306060314042310 72
    0x46c0b0100204012100d880c0100340348640141c101c0e003410004164142c04040d4030381c8400d0100c07074040341c4415480805e101581c100c20540c60000c43d091090140f180c3c01c0514003082442150381030100c0b664020700e080413190340f00340544800b00e1681303c0b036225070708940d642c015190740c180303d010307100c0c4a80c0d14543c2002d00c013a40c81c1029900440d0080c10030101c4543c4280d00907200d900d8650307461317141001d541d03c0b241c002c89030325545080009840791540b10f941d5a021896903031900c901c80d2083c803540b030522003003070070300044d00040c180c00c40c140c1c625424a000c644503806100e454080c2030130240d003503000ea40c0c012010708104104000300a58907a00901050609072280e520780d0b1a2b0308421021000e00b40940c0d90071a550311034a03205502c0142c00c23000a41c800506c01c40b608400154408403104490004503025404900b09010b21034060203210042c1929240030002040f01e49039042e20a01c010308003a0840a0703c0c031029000207517400103110440307820012118051641006a401041c60892035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 590013057 1250 590011807 590011819
    0xc0a0203010c020d12060b070f050723090f06010905040c0909060f0e0c0a020613021f020d0206090109050a060207020a0b2217030a03052805010503010509010b030706181d0402 77
    0x30f1003485c030b0b0600c646010380d1000400c1900740310107689c43c40905007080c40c06a841c1e116100001900158101c1e180480201130300da48004245080103105074507201400c2d074502c820a0700108806039034010300d0801111011903020030400c0c1d1034402901c4a100319042012143d003050808181c80c86d207813000ba01100e080340036a11556130380b0b048180e00ea000f400c13180301c010f0f04220041086d4180c220a201c05076800200020b0719100d20125100c4280000e020030f20240e00411070741c0c4c0c0c40310313018411980d020308942c009208000207a500c01e51200300125000b0b11050780411010195162030b100100a020010700060b66201900c8a100c4281c40d024043c003c8110725036008101110010051aaa01b880704021401d110b210742040d8080c150003005110861043c40b0744d03804405031200418245d81c3d68400004040d4103103c281030940350001d16200701681880d45440403601c0004403942140e40c3d42c5408020030704650304c0000000c20640c824810200b50340011040c0c100e10100340c07400f9610031600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 590014307 1250 590013057 590013077
    0x403050d0c080403060e070f080105160801080d11030d1806180f0b06011403070e030f0d051b07030507060e091b160303090519050d02060c040b0c0a0203010c020d 71
    0xc035804140c03481d0052901106000400000f01d658005014081c2200305a81c6642d88074211030307894440560100c41d49d81e443e1014002c6040c0a8000e50340d006c0d4051030088800e40c100800b09998644905102d4100100b8040c1c42d102120280169480c1c0c141a01061100c40c1000303003019007881070741b0800d90b0349624101460b043c0b03103411040c0400c00b0354000151691410356440e0182c040d280140101d05001c2d14107032a004c81940072004621500c0c1c0c90311544d4094100409051402d500341007050100e0b40020081c0c0181508002918a041c0c41031803198884221b140950b03041c04401e510013801445080000718145401411441e031a0100303981c3ea81d4166914210380700260189030801350315a00030050030000c49201d202c19901d107802420b001c0b44c00006544c55170314000c80940c0c1b01c1c030b4180c4407107a0102001818001041070091b517100801c0b45003403901044402e4030692088007203121000034000c049540a10a840034290001c0c02000a4106000c002e52141d24640764000060b10b5210 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 590015557 1250 590014307 590014333
    0x3031b160506180c10050d090c1e0b0c121b1c080c03040c03080c0313080a0b1e2205030705010f0506010513150c0c06031a01030605010f141b0102040305 67
    0xa00040701403005055840f541c011200030303031b1250310200c11940219103078003801000c50400c182140050a81012039054175101182d1520412200d42000941d80c804000d925a00c1e50700084299401609480c0c4903038031b0544176a4900304803107000f1030b41f0700d030f02a041136602280c4521841c0540340743d0a40711010b140c1d80d01803554000c0e200c102e5000707148000011f01070001c100349801034a484244030342100d02d0325a00d0356200e03800304403523484a0358580c401d02e002c2c8100032003411681d400100b040c4a1200c4000215000e8002071002440f07400605c02c1c0341504c4041c40b0100710528403c1d5044401d0740d980d02810304115028103890800645841d0919000c81d90300c0d40701d101105c0c41c040c007465643d03451600700f00441555106c1c0304c0c2e1000030040f6000c90840890310599085004208030b8900065a5481218200350803034007111540c141868003004204c1c82c0d0308041c015450818a03c1c08000c0c08162881a91041c06001d0000641c0404039400c0d4240000c15801001504e00420841e500005812 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 590016807 1250 590015557 590015563
    0x100e09010207151b0c1e14010f0506061b0703080c03030a0507021f0f0b03030a0c120c020d1113020a170f010f05060a1e030605011d0303031b16050618 66
    0x1091036032040d40904e6130b00145216a00075050540303d80c2c88906c00300d07205065041c0702010706009540825a24010000041c0c0901c03a500340018a0b078018800c42c5440800a8030304d004592150003501d003241041001114248603040185034424005030320762000c2c12045039039800444103809400d06d401e0104215500000ba885961800f00030410400195000010058034155151802d640e4580d800b0740040da4090000c1d241c0c0b6007641d9200d015420550a21704078034490300c000c0500344100b00c40c0203005a254034914022068000000d4a80c0348110004201d00b4140704001c4200c00f4804160302c000a58401e04401326031050808452080d1144068000c05400c00e104480403210b0300e040c100480d04001001d00841592030414081c09404051044c1007820000e540000203541c030f90003400742c0c1da0400030031030101301d9642007100d082d2030040119580e484080d108412050001500e4091540441c04645912510710200750300b140d454a49030f40c0e00c26042d03031280341d03800111503030101480c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 590018057 1250 590016807 590016821
    0x615031b0509060f0415120302061014100516050714040b0d0605090a050303010612050c120402090c091203030a1103070207060c0212060718090c020304030b100e0901020715 76
    0x34840c8003261245020013507810f004118043d00940c4a80148411817020b5800500902e403200c4018224445840c00a0074400c0003082d44110703c0304424284444810120f11400300d05059482c01c071080c503c03000c251058000c01c5055080400c084e540c241c1000b10106803407084904424201d034502c00800300700700680303032044c0e40c5030f03046140566140003049068001e243c01c129294155810440c0382e072209800d5620981000001c0b8203414200e8070565400d109807540711000160320b600b40b005003030079040c80c500050406480341d42d41b0000301b04c0c51440d51049602411008214000180007941203940b41c6d002142c054900f40d25000c081c8800c1e2a0b406c1c2280d11074025940070f082058284103096030b501032001d4050743c01501c140c2d03805480d51003c01600c4c2c0141c400340c4600c0440c4041204007400c3d05601d400920055082c5411484001d170000140d1301601d60100c2803442a6880c64509002251164807003100031030035070144040c51406600400c012070054030386180500181c00503c05840721 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 590019307 1250 590018057 590018059
    0xd0e0d1d01051206011b06090c050d02012010090f020f09040804091a0d1a062b050a020901030818030705010804031206081f1d1e0a0615031b05 63
    0x1000004071030000c080d080c3d40e0240050611b0700c07000162a000c5c034440f44260004541c5241d43d2071004090040d41c0f60000c0040104481d0341703e10305403940c002488400d1000f500700c007180038000420200d480600c441486000c844008102030801410010100040c80e03c0681c00341c024581490610f06080c05550b10940d00844100d10306450114000010000c01605009100511307850912681c0c4007100500c440e401079104030022400102069107140000d8107d1348a41040b4404894194501c00780300201c411101140007501d0b0681821410800181c41c0298007a22141c0040100410716000d00f070745619250303a200684012100f41561a00319010722408650b8940003d0700217889450304504041c0b0900005c208542da5038050362510b41c84140c1c0001220079401d2070b24440c6170740e01c5440007071103824010040e00102c0303510403038a410303040d4020017140754035400f0004041000c01c1185656684540d00300943d075840c035100d520310580c42c0012510030340c82805851500030014109816244 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 590020557 1250 590019307 590019317
    0x10c0b13290919150204270c020a0201091509050301020a0809070b040e150607060603060507170105100f11030c070906050303030412121409030706060806151003020d0e0d1d01 77
    0x100c00c1e1205200e40b0600180c04c400203408000114480700d046d007840441854002d4204141e604882c0c41d94281c5511006403021984000d0b002070140c4c2e4408040e01c103d50140c00c0c00034108040c01c1007250500b00c0382d041541c242d17000045051a03154007800c81817080c5500003e46003016192000c020144c4158801d01c00d0344500312011032021030201e030b008054144000d000a10b031061580e15003041c0c41d020751040c1d4104c1d0361602002807664000f085c400c00c0b8881c142000c080c80d81042c00207036040481c0315005082008a485982050307000d03000410000805200b241e4446c00d002e08015541c8180740a0784100a0800e100052142000420380f4052580311040d180b454607020f0341110724242056202c07a141d601c540e4401440e0080a40250190354040003a5942c1c6d200c40c01d200081e1001584132016950000e002c02c10301c102100c1c00190100012035241101d680c40c424120042d004100b814000c6e5440c0800c1305a900c1c2c0c0c0000c0700000d20460340c0b0344035003842070381d03039140001ca03108800140410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 590021807 1250 590020557 590020603
    0x5010c0f0c120905101d010e1e030102091905150c060a0b1903030201060321050315030109060c022a15131a2106010c0b132909 56
    0x2c0e500900541c407406251070008101e0b0b5445002500c00b00200030440c0c00b00d01c10551a8152500c402c1840108403c00c1c20002c0350b091005012546030141d0a900401ca0782550703560225136507080d0101c400284c4024440d52240120b1079200c6074101141c41594414072915004814114007442550650b1100754090000c81e034030a11180040d2089640302c9a00c0140c04d115060b0102c6da031500d070000356000b9070001860310305500d01210100c03500d81e040b0403086082c4940791943c035030000c2200c0c0e000003080c4078068842042000309014004030600200503c0c1040c2d030701442281d0010b00c4110a03c180c01c00c00384031300c0402d41e6600d11030200848940c0c0140451403001704411405008182e030640011108601c0e5603a40d1490b400c0a01169810440290000d00c00440c40c541c150804c1c0302300b1402c2001102d60600304000303410a644030b0300c000e040100c0040003c0180c3ca0304448c16101c0c0c2c4e081030300b034005501c08524030b19200c00c1c400640d4604c0022200403c51992000541f00b0615005043c114240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 590023057 1250 590021807 590021813
    0x32301061e030b0925292505060106030905100b0f010c0f06020d0605100e0105043516120506040308091606020106030309050d111306120f05010c0f0c 66
    0x203d60300402900341da202d02c4100320401091482441e888101c40307190002c5490500031914500302280c25110551040c4000f034220300c45c043c1013180d5000c5801c1c20401426402c1d100c110171084900d80015105021394000080d50300e405800c88a001c0d4481d1b01a10044140c0c0d031840720440301d004208641268241310b404502d94001e0108204c5d15000302c002d010344511710b95030700382a61f01520040904a8840808000508043c1d2100d01c89008a0030a130000310011000200345025500c1411a0883c1d0071001d241000d0b0760624200700c50000107026144c13111500000c0707030348000030795409240003002038002034074800888214041c1688903015100d16261900c003241d00d0741c2c000c0c0845035280290464042c1c01c03192001d922000b06040e800220b0300c14514180038140b0310305a8000b40c000c14121003042c0001f0314212545804480407660140000c4840715110010704007a000314140400350803001c4148010b0030070403034a1070722840c02407010740003500c1c046416070b1100c40c0384e60110b51a14050800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 590024307 1250 590023057 590023073
    0xb031f1b2c03010f0207060c080903030c121302040218010e06040b0f071b080708120a02060601030c111009120915030b0103090b0c03071431032301061e03 68
    0x101c0d91004002040b500e007400c400c0380499004480440d859a56001000c42d8550001e0002d40d00c0340b00b10300658114900848048a6803080f603091009100d00c4000080b86240100180258160054003c544070407819007000643c0304054102346c0800d280c195246040d02d002000c44003a5004c0c03262050420080005000c1c40c1d800110f011039403c0c07a0308489108014400480400501e840f40080c4030081c6450724040c10305410450842c5020820440b419020340c002072a1904842e003072030000b400d200c00003c111a2085010a104400c0c002c413041c0d1a00300500307412206c0d02500030043d0000b058400c003c00d507070001c011712583e044440100300c1e02003e10301a03403001c8070104060501060140340f650302e5180301c0c8400c481d501d0784d40130702005011300d495001c644460030844102096240503100001c00200060101401c44201070300c60042c2d9610025000c0800155404040c4800c1400e01c0641f0001c0042d1306a00f101c165071a0860001c0c04100e05035580d00025162002440418115210042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 590025557 1250 590024307 590024387
    0xa0b1603030b2707110102071a041b06050d0e03030708040b1f03210f0806101b0c030b0f0f010b030a021204030504080c0609060d0b031f1b 61
    0x29014000145410160001c14003c18a00043d0a1941e82c0c41c41c0c0f105002d8185105140e0140480e841031090500188181d25100030100ba01d00100103155510310780801d02880e020076840802180080011328103030414040c080341c0c1c1c0902c0003071110010f081d0145076a40004c84501c0000780c00403011a02007903000080c260010b0603500b01610f417a0701030a1245820000354811142a00d02800780111082040e0746101034203118078110b400d0a44900b4000c01400c1e0103800c040c0f00301181e01c460504e40340030711002903070a010190041355011040c20803010210241c841039501c55483d10004409a048000d40c5102e0540c0e018601480d90038903540000581004001558040e820014480145000b10001c0d02c60b6119076106950341c3c2c10b22030b0450a1284a400035801480107201c200c440e170341d0b800150390a1003451900003c0740c0d241500042e10b000011040c1000603079076011010707101c030200d4000346800c580d03044401d11101d600040840c2c1c0c40404507554041c200521031406015000148514 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 590026807 1250 590025557 590025559
    0x615020a1e21260f01060822080702011701120303090311100608070515090f0411161209030302150615040f0302040e030c07030308060d061a0a0b1603030b 68
    0x108842e20807180003070300304550709a41000c40c241c0d44a100403160701e410810594801c411181030a810301c200c0c40c44030380c4c0040c0502e40c144a14040050900000c60000342e00240359000031100707022490030230380f81962007140c0c1a800180140d40c01d040304401400380904861000c5020700d114003903074802310010000300c0d2f000c8040040440780302c0900c1104104480b00e0323a07001000092080c3c64210180e140140b1075001e14000e117645502c24848210301c405071804000196000039040c42180001001442c40c00800d0009000101c1c5000c041c03017031078650841032480398100b408100245001a01c1d4016103100080c016800128202d104032500002c0a4001c600980347d510b00420300403101405404c20b807c080702d80c50420740104107520300b60050a20305124200030b9071410f201800600c0e118805c0380130280a200c0110b0210b000344c0c5070f084420f029207800500410a14901080000d59901100380e101d10600403944c002c03410502d424100c4084031112101d41d01d0794281640e080c0d01914101c1a21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 590028057 1250 590026807 590026823
    0x708091c02070b0406020d1e0203040b07060f1d010b040917070303140108240708010509040317250e01080711010204030c0801020a0f08040209070309140706030615020a1e 75
    0xf082603811014002420075a0054030620010101c010b1154010143e06c007415820070080e81001034000c01268152900010708030754480007820f00300041e240a010161100c2c1ca058190040364030011540102d000c802c0000744002c2c11a4070402c0152401d50303002420343c001c228407882d031789071030b40d0000c0c0100c500c20b040c0814002d00303034900c0d6004503109038030001158000d6200141d03070396070380488082c49a2007940c10801a00309508020721078941401400d00912131000850300345402000011000ea000c4c000d21109854802c06130310f04420039948001c114101c48120403007150080c1d50100c82190180d6540400b03a03a18241294400c103d40c850084555081101002240c0481074080c007404d02c442c00948d0754020888000e02d07541c00c507054002004801424000103aa600d90f00760341018140c0b07004070322280141440c00c9111564013000040e40302c0c1440000f09036400d600444115039422000f0011240044020713612000a0380c0018402100c01d111203110074030700c46009107514059614 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 590029307 1250 590028057 590028059
    0x1e0f0e0f030105040b01080f0714060a300b03150601261e060d03020a020613120c0302010806030a230a15020306090a1a040915140108060708091c0207 66
    0x110b801c440040c0e6090b43d41d400c2c20300046c030529800308849070b961116000141005840c054520031600a10105144500c4002508400b494030540502d10701c07030003e504515005210100032024010041c0b801300d0704030300700344c0201c5040c6008112924410190038012046540d80c03401118158081d9820500e407010303030901003445089560307406100c1c0080303a00c0c0301811404881100000a0000c003201d12424500c109000026400b00e091041030342d0648a0b1622030050317850880c003c40c0c140d0015510b004d4040c4040052000c00001c80d01124000c0c2c0361400c1d00c2e2640824591a00c4107504090040703100b0942c0b02d5030145210032901c0b480840c0a081e030701c80c407440380d50303000204021861a0200700d401100744862441d1036a955600842501020001e64110104040c61303020b8601c1002d1080703a031451010184907241d04600e05440ca4404204180100c424110000e150280100c940301c1c0305a80014611900034480706000300440c1e40100100d003010003000540c684480c6810085021b14a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 590030557 1250 590029307 590029309
    0x50705030702132318060105130903021905010b010908010506060702190306050702030a0e0f09070522091a090c040308070f050d27061215180902011e0f0e0f 69
    0x5000400d9500b04da01c60502401d120400741d180120005007090150002c5004203c5640c0f5400700c1400700424410106070140300e420306a041c011030907171000603818021070400400c9411351104801c01002d03228407043c00e4481a1482c0cc0750811074065401000400808000d031801000d60070480c24081110030a150722a5155019100f098407484090381c030202e00460a036802601019003c01c0c1950b464050300b80050009a003804094500c5083c0038000903580c10003030300390540e0718100707800100b013840305503940a044006020050410301ea4005546400300b4600d0000c050034052015000d5017401e081c02e68851119513484445d088a01d2450b81c1d4010b0300103041807000d100201c0d03040c3c984401548107a1804204a00183c20b50708080550311020301055412040081820014034000112240f05416034284603141d500a00701401464889541214858006a01c114800e0340e986440000002e2400501d00ca10580304022400d14110b03103584030320403100c0009228000740307c8850410880 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 590031807 1250 590030557 590030591
    0xc0405130e0709050f0c0a02060c1b06010b031006020309030c0f0315010b070b0a090203150c1308010e190809011425050c03030408061b07080301090c0306050105070503070213 77
    0xd885a040c03c1d031107004201d00e400740c020041340d2100120340400d140c640b0701d000007921514002c7c0441004000807030f058204204490304503000280c05030031107003156140c00b248100c0360011106080040606280814454400700644c1c0381c0140c003400521030355107442c04000f2a00c1c6000d00706030b0980f050102900c418807020000030300a008a0711000c1d55142c00341041d40b8201d00c0204600c20231410842a140140c8000a40b00f00511842c03240940070307282c0d901510800d12881c903030040c40380310304440401d160806600c10104203105404440d40c18000c0444a90849220140640300800a00803004254040d505c040e10300d50710020f4880c0b07000480d0000024400715900f14000d01c08801c04400100003003004600144c1004900460501c1d26140c030040e55100c0090404001d00a0465403003680752458003a601020343c0003d00c0380d1a036071a030101000402d1681855000a03040000005995000380c0c11140a290003001035440c02c0c05ca50203202040c00d0140303030141915690110215085594 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 590033057 1250 590031807 590031809
    0xb0603160e101e020c1e030c0a060906030509011d0c09071b02040902031603050d08070513091e0f0906060b09030d0f093b0c0405130e07 60
    0x5040d8084242540d8100428401041d003103035000301d400d40e480e803221035002400c0c8580240c0e180d4904070302c60259401241400c0701c0100203900301c1240e146190a100622140b007212140903801c8448414440c8c04000c092941c2c6d00c940d10200724501d0040c0a00703482500101c1e40704a1180000c0303003d082c001000c1c905400c1803800072030103030007021808040d403400c0c0035800c7e007040841c034224051901c07019000401c040c1e943c100901c61992180c20808544042c418203052364280c0500d03440c0720340c1e40d081154032890340300c5807100040d80d1107001910540c054025918031968540c600340100d428241c1000042c112000c4000c0b0150510391402c0d104103080c000c20302d07910010728012980800e00d140c40000e4a0103074210007564101030100032074603100000c9008580c0354500d09035480d00701054043ea4070394210781010200c00550034040c1100c5855a0001c1d40d43d69400c42032204609580c84407000d00c05060b9180100c0c3c0c40108003c01152800f907039145840d0860050002c3c261201c080002c2ca00b02c02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 590034307 1250 590033057 590033071
    0x4050f0304120b0a050402060a050903150109140a0507050901030c05070609080a02010605030a110904080c060717160906080601030608030408062d0a050c0c0a0b161d040f0b0603 78
    0x482c105401000b080c80c08040c0c2101d807401c802c0c0040e040039400558140503800005007040004503800c0c603a59410007032045c1080340c6858440b0607585901c044009441604040d07100c1010890120f0010001882401c1c80360300207954843c2040181d81c01180501580c000c60801c11005001000204000d480741d4484039200d850626a104400400039080d01d426030310803072080e008800300b140400e561030840d0307400210440750a034040e50b59240100c0f00e8004c20880001030b00c100006c11401c103030085004540d40058403000740c5255150314000c40da121808080d01d000410503c4100106801604a0b54003c4014100410038640301e41c4890301c0c6822070341c0074a00c40d5200106208001480c0e40000c00101c610914203c0d03c40c01c1010701143c7c0d908040c050000240e5500001142803d51038159469010880207031580802d00307090141d11110b003501e104900744000c000400d0000d000304480e101136036854401d511540c01c2d4800300001000b40d071150010181c0c03603820800c3d6030303901c40d001117100d019 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 590035557 1250 590034307 590034329
    0xf0d0f050f09070602060f06032505030106052d0301180303140f0c03011206060f08060601080609060307030f080910020307030f08151002010b0901140f1005030f04050f0304 76
    0x36003224007101803200648445040c0d04081c1050103150383c00704902d9480b028050580d00700d603c401c00484c0c03a006031141c0d4041c0064580302c400d01e1810030307020300300e003282c0c000c42c0244000c0d5111810860401409030451340341d54103041c2d507041c0c91500300c1050f0b9241c0c01d00600000310b1240c9501c602106074144070701240002e503241509201841c000702e270117410503a01311540d8128544001c88018030721041c02403c0030203400149000030046590004000f9029400100d6001956640e0440e65100180c0e201400b20f444440016080c1c00c0c50007050b071107800010020f0900b180307580c035070f44c0c0351a0420300143c850040821144031151550b065581c1020180d5004541c2c607d240e0400801c00d0038583e00d41410841d801083c80523a050021103072210301403c450541004000c420281d00400e0b541c2482600400d03d0b500000d0070843c5002ca401030000305031818602d2410300410400320b015200c1c154404180140040342000b906298a00d034054400d03021500c000901300c20140c0345030015845000307561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 590036807 1250 590035557 590035561
    0x1008061e280b01031a0f010c080c1b0102251404020d0204142b12021f020301060e0402070f0308090a0606080d1e020706030f0605060301080d090501051804020f0d0f05 73
    0x540e25200d0182c501702d91600f4203d04140307504c001410340c0400300300170b410400c084500c5800c0c00328440071250705138103403422500b094107000001c0e111120076003461ba025004100c00401d80210718a03041c803561510074040d05880b0308100e00b40f8030a04440074101c0d0059400d000d00c2c440030045100500281c01c054a031070031001c03018010400859400a42950a4080c2071241e0440c05401422030030b10551103103072220700c800005022482c04d13140c6000b1905200004960170311240090f40114181d400300e5480c2c0ea84107a00d141400243e03c40c0160081c02c400420f01d0301000701e4491030b203207500541c0302825510002c0301621184155520740d0451410b54009200c507041d62030b04801007039111185801c02c04508041e4010207900c6282c24801c44050544a5004c0c24206e20290301010240c21300a003115100e584880c00d45030341b5480b0076001070104400300d80102d62507001d00c2c245c40c43e0025984240d29034100100900019401c021485406840144459058504e05000b21481100d5600e0002814 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 590038057 1250 590036807 590036809
    0x6050402040e04330203070311210105030a051b030703021503240f0907200705090705090901170316031707090b2208151008061e280b 59
    0x1040402d4100c200d59814200d0b111200700804403013503140e07030700c41001130f02c80d518031000350060400e802c803124501c400000c17003d004420780d000325000c1e0154003403100200c0e0303215409d06a45400580018041d03034071101780c6182c3c440042c0c41c1001c1030070001d01580d020300c0d07407503000c110b603040031142000b1400d00100070420038180180f40d80c56022903c140c450359500560000c82e5034403178601c003a923010303100c808000b915480c081d80c0328035501d6002d8805810400c01c01144243c071190f042c000d1030b104040e254040380070705105905480d84044018450101a46011140a04500244c40e0140c607400180000c5188010b96000348000a00a0b03d9581500450348160b00e03040d10010002024800921402e2188840c0c03901900d0800c0c0c4100c407a0207591060300808000320300241e0003000c40f407148034410500d8075105866a405080035902040c2e0b040e48840700540ca03107c04440700302c0c80060460707500580e5083c281606400c00c0444200101d1000002001c14521120488518400e070b2075400c0b90f401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 590039307 1250 590038057 590038073
    0x15030a0c031103060108060a0806130b090c090610120c03021c1527020c0c01090e0601080f2205010b1005070803160915030f320a06050402040e04 64
    0x110104a15003040040e003400e4146550f400081c2901303040125050000d00c240c0c48806540024242000407141c080c6041c0b507450340510310700c1c04100d803001000d030013181640e140040c3e0400400340040c00c07041360799141701c00d0140e440010310f440000c2100380094002079215034425031040050555015940390240e0072401c260f60300c42c280305402d0301e03d02001080700b40241c8550f1006d94940c40501c115409102440c2c18001d102c0710703180340d003442c070020f844001c4850001d80d000c4000c1c0c00307032619911107980316060122400304448a074003080da91800566050f42c4100100d038080541602141194881c118961000790581000ca510742c1d99060700b2100c3d450f0000c0e081900c012545012854550b195035520a03501020740405045c2903004545441e86019000400140003042340034007104d0034a10004010745250342003595031526000316140413803103a0741801c801c0650525480b61410152041100d143c00007044080744503601c120100e550399a5000910040010b140130410302e040c01c0c204001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 590040557 1250 590039307 590039321
    0x903121003120f0206060603091f0c091e05010e120604030804050105180a0609031112040e010b1204030c020f0307080a0606060813030c0c0e01090c02010e011a0f030a0215030a 77
    0xc1401640569400070340c4e8000382c0580d01031416101a9100d403078108280b450540340046c6c0d000c100b0504074503030752400740710746c448a080c241e26032b2111030f507540c0c0d002c0c144211811a003480c0780d0354000c41d10610055004190443c405030026018120410760740e0000313828080155001c4000440c0081844103002007400b40755003020280103101600c1c500c0c94980c03a42d40c100402e00914403900c0351109400c5c136000755620341174060386606076084d400362400c001c04264440d005080010001c100007043c3c400d00324003a0b58003103400c00300d20821500c031520180c4403048844002c90b07206011445180741c1c1d0700c081c404200140003000040160304803618100c07050b685135411610810641000304901602c210002c0704070b00f03815040041c08030800f810500d241d0700298110800d41c40d5030900003c7c102015500c0f8001c0c0601d941e00030065004081c4071242a80c2d0314501c0c411210b011074440320001e243c6944520201c0400800316400d0140e55808184461005440720f04011400702c2004019415401403c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 590041807 1250 590040557 590040593
    0x60d02030712060f050904080f0a0c14071805100305010f090212010b090414030f27010f05090f030c1003060611120703081315020d0f050903120903121003 68
    0x40f01080c10300f42c40b4402c11003a8400c2c10311035014100806e007405441c408903141c00c0340f0215038664800007071401401d11400000200c0d040e810015002604020100c0e002003501c0c11440300200a41c0b14082c0c5501910b40909000c443c001c1003840000056024800d90014050341d02000c9500b41550040120051520840b1030b05641002e60000017039a60002c1580d0003035105400d02c4403141480c507050300d14012041c0c0e02c25101000103d07001c10b61091807000c00302003121081a000322082c04011100c440c078002111300807510034080e0020500e810150510f0402c4080d007122a141130354400150f0138019225001c0110b5a070303403018007800f603101c01c001b404041103500501c20602800319900d038078818040b0203020402050042654061f0071a810291240c02401240e0468400807062000354425501aa5102e280008030640c00c0300714010755100c2d40c1c1c200091418080018100c0c04000001020162a4042041880d400a8031500041e0240c184045900705050541c80c20500b0481c10318010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 590043057 1250 590041807 590041811
    0x40b06030c0f03040812072c0108180f100e1603032a080c06010e01050f0d080f040302180a060e160f0e03070b0c062208090a0302060d02030712 63
    0xc60225041c408844001414100580c1d80780c0e00c07401c2501e6a40903090740071807201916400c3c815020392040c2003c80816180b20582c0e00040380e42a42541a000c0e14080c44c041850080007840590058030300072a2142c107201942d210700b91480d581800c10103248036107000141c0c0c0d4071440f84550300c10801d00c00c2124140c41182156825038034068031030481040c4c1d0014a2110a9043c81d42c484800001ccd801254800e240c55250317128107207604d03285c003401d0080d074400c420704c1070001500c1d1402180c080e801d8080940301d041d6000082d01c0d8007210358001d01d4034515a14003040b00200503181d024092455010070303003100c4100d0070a040b5010984241d60310001c600903607801400159010b1340d0f010079242e01181407281d003040810600790396076681ca95030f40e941401940400200c0910300c41c0244000080941502d500355503c01c00303121403059590303208a00d556030043c0c15000035887d1000707040f10000140303e540039940e00d81c005019070348200c035626640358000c018499070075044510400c03525800d6100b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 590044307 1250 590043057 590043061
    0x30d020c07081f0b0a0302060703110f0c010530040f060e03030c1902070b0f0a0201110309151b04030804031b050618040e01060305060402100302070b070c031e020c040b0603 76
    0xb90400b818105030803a0403266940078240002d544000c0d200001b15406041e0a49402d92400e0150000518680307590440c05000704018a100001c00c41001c8450141c58030740c14046000c1040c01e01002d40c02c000f003160b4002c45140001170b6019002d641c4214401c11808040d107483c4d00c3c5c600d007a51030301204002658030500034000d210000c2c90a440d0801038041c1c01448100309081d04038505015030b440b100460f103002441c030412900c80b41c02002d0030303081600240f0114071013240b1034503e482300310741c1041560001511104448010070038036402c000350003080e1142d400c06401d2003106034040e900440300c07441c0000b010420490b0780000060380c150324004044150386002e0125426110b01c01400c815455281d800034503540c0d851380001840205280200301440e00c901e081d5a45580940702a4400c03015900002031742c13442402221122544424980c10341d44640400350f80c08103c1c800128284401a80b40da0705c181d40c0c030f5000c0c45031110f0550080c401c000d80c0c0d0080c002160342507100c041c09002c0400c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 590045557 1250 590044307 590044333
    0x503070c17030927040b06040b010c02090a0c090f0e0103060c0c050d230c010b010e03122205190e100302060301030f29061503060d1104020c030d020c0708 68
    0x1c280c5083e860240d80c0c51030ba0b41d10b1040340800419404c0006081d40ca0180107000034042096416445040c0039142080400340303000064072003d1907020025802200100058001078454110070b84c840b0750790801d114000c0e1542c8a041403039906130071003082210080010020302045010305d461041c9075042c08074020a0a403941030301ca50450f0038803800d00100e108d1002c0e108545c441d107404280da010001d15195012021114081d20070f421440f03001070b458194008462401240e20f00500e0b01400700c9500d40910800c10841d0b69518000d480d1400e06441800911030726103030318424180440c04490742c0441d04040c1c01c1054030401603d26810010805010300c0141c80351000c8a040d203400104c00c610405441c40c3c040120b15903039440b0f0050b15131004124454094548120b40280e8044400c1d01c004005a0f440003c2c500045412650014503000b60a012610501000100c070101920152820700111800f41c5503901644841c2516540001d1034032400d03900f40000030280041901809140303080d41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 590046807 1250 590045557 590045563
    0x2070c1215150f09020711010e013e010f0515060a050318070816090b060403060903021c210507020c0603070e041112100303020601061b02040501030503070c17 70
    0x40d210880c41d035480c0940c000c2d4540d1100c2001c002c0c01c1000441d885262590080e40c080c0d08002d00843d00c410680c0e03c00d001640c091070070070b044618181e544080c025152010741c05241d003c000001e800441d011480d82c034506501d01480300034403a0a00120388040707501c0503002140c600501a120b002030f02e84800c011580c0f0700040758a08140f62814a469880302c420344c3d600c41a20341804001413054410001e0350f0000070804400c03810b1107161600d89281d580e1030800c2603400e04580146d2180c4100002d1000805503444102c07814020301c1182e01200c43c0d008008901e15a018801c804900d00300701d02440106014480f107514400b07514244a40e0429080103941c540422038854807407080403002521551148103503d80b0030304000c1c02880100c2c0014150082d076801003200056080407440014060706c40d540c0f4030b000b10b0341c1c99401049540e103008011600300d01116602440c29291034060740259580e800b42034085c6006101550b40d9880919042407000c296602c2010588140428105045004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 590048057 1250 590046807 590046833
    0x216020306070201091e030212041d100b07321f090b0103120528090b0a0903020411040905100501020c1806090a09051b03250504150807030602070c12 66
    0xd1181c50340b41d081070710342a420b1030340b2144800c9d058040407a001802140030500104c1e6100062495805604c40210f8401521420b000718039004404100341d4001a5000c017000c5414081e20032804075141c42440701001c40420f8410302443c6034007060502d01564116603411807085160306081144240782c0c5e4030a110050148006808840c1c07000e071b01904540640d0881e010244000301c5010300050038001c56101962180e95140000c0c0700c064041040c41080e0100c2e50900d1564491410b039501e9035003000302130401480c10341e040341014031000803c403140c1e00400340100c071000810708446091000080c6406039200882c0c0c425544400e0400503031059801a503000070040d11032503d1641c509040e80040c01e07030307064001c10a105072a65058802090a0305685a00c07044050794020540008030f0075994602e50300c684007103050080c1c03c00c0a81b42c10751185c02c0d0303500c5208010100301e55404499040c50360662058503e81e4000400d002041004200c44028081040c031001c00252141c0360350705032043c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 590049307 1250 590048057 590048093
    0x10b07030905060d090501050f071707050d0f02030604141605070f0206070f02010e100e1c0c03050a0c0503010213050f0d021906030515091b0d021602030607020109 72
    0x180081850300c9010014054000981807a036108107002800e4000d0001440540c0c165103000701090b84403030700c1c214a9000b0012559850f4150048010b04c1240081c082c0c655414000200708406189680303010b02c031801200100010f8480c50074400f0302003074070009ca118929042c008020000e032080c00d00783d046e01241803403230b02c0c0e9101d02080c81d04041e012071102c0c01951181c1c0c04950003040010500d038440c00180300b03a031070180468000c0140901c40c8c01c54130240010401d0940c40070711609000c0c80407903051040a00820700407034540c50b02c030b42801c91504251501c0c2c1086a500341804030000c0000024030056008614142954006c0014030081d8051030f44621520b58044015a0b20b00d40700580c025002022170b00c60f80d80ca0508400c2c681a035128810100707040c5400160800100d00600600d00c04c00380c9202001d075203107910480b1100d1250b00745050f00d0800d004140e4200080d01c0906400102441c041d80116803d004161500100800b0f107411681001d214400052100c1200700640203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 590050557 1250 590049307 590049329
    0x8010f030c06080403020c04090602031602010c0f1115071e020a080901080604090b071223060906060d0e010603110306040f170c01050915011e0b03100801052a040302010801 76
    0xc980c1703402c80c142802d80300010b500905041c0c1910610200340d00a5005141d1000344114800030504140d007698014409003000c5003420b02410840c50080c07500c0881004600306407000440f194680c41c0d4440c409454000000e09455040420114640480003800070540000d1500301b080b5518151988900c0648504000100340469100d03107035900242540340e44505074858900d00042c00510007401045051103103401d000e502ca8070440790b412916005540e0f013030a1000c0d503580c2014041ca588010340155004507041090b06503a6401c0c0c0324800031003c0d490000300d00c4614504004c0c2e904502516031a105e50410b03014400068280b0b882c07028225407054040035203d540b112150308a000e90320350610a54203080c1002002d41010440d03003840c80b40500c000300c140c0d072516012030000b038601c014500703400c441c031406000152008004c4c603801503140c512185c20039181e000072401c1d03440558034101b90020000c10364610074409004550040c141440c000e082600d5030300000c14080e07040c40748a00d006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 590051807 1250 590050557 590050561
    0x90706030c03110d090302070504091a060d0c09200c0d121503241e0f020d1103040b070518040e0f070e04051207020108040809031c090608010f030c0608 67
    0x16009411070700d581040f1050703068035540f40b0b03684003014080080c401c40c01030003913078404152807a06104034101c0da6000070f000e800c0c13a1400c0900306115031028250035071100c010b0031460009184107000b07a0103841c9040300030440501e42c889048a0003102008028815400c0c4030035071469000194028210b000c518202c0c3c1d80800c0c00309280010000700c4031005c1010305404012091282c02c0442d920b1000c040b0038502c1c03280410740b202500321201030003000c200c408415120110a00d5682080da80c0c905292401440e200052070000c1c00c5640c81100415244008401c21040c0604043c0056019125080203490a4410b1081050090310241018411507139815400d04440c0c0420002541002180490710241c0e1510018407000740116803c44451107442184100d04004005551989a0686604040351140d60b00c005d403942003048100e07098407a04000400d043d0413801025140d503103649034a81a0341c1014002400d1413416000214003c1e02c10104200150304904c0c0031045400c02e24000201d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 590053057 1250 590051807 590051831
    0x70c061805010c0908071403120706060e1303030b040b2b05060106050304050d0906090504020c0a020a060e010323061011030301090b0a0e060a0b1b12030a1409070603 73
    0x251982000181a540c60002d0545507141c2142e103503015151030030b04480800b43e8034901c1e8015400c0c3c00041c20b4243e0802c0c07881000300d48902000d070ac811440340c0004102583c80e002c07001840c05003100c200c09021804e4050f00181509440b4130102c6410641d014000380340040301103100760501ea56000100d100380d2000300e00010a22400200300c5d5440b0301940c00b19651290020240e42003a40c0541c0e0302e0140c44a00401c05001c1c0360300004a0710241c507088052850041004000e4004000d05440d5000b07100c811001660707080c01404c0680102c0d168150340007003001c0010103c40c41c4080c0810074420207040c00d40070b1840304804951100040f6404a2199884807040b210302805c1d0301204410b01c0040000700300d04035032740c0041041c0d40d4195804a0403d035100b01c1d10200b00300c21b440b05900101024003d20081c2e00c654000c042c80d00303560070650b0904982d000042d2800540350b446010941004c030512101c6a180d0113450004c00c04d0040807640b82c18a05841503c4841e54031a5105241d51801d2000c09 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 590054307 1250 590053057 590053091
    0x6010302011103210106090e0114010c0303020f0a02150108070b0717090a030308060907051801180f0e06100c031205071403040f0311010c050d09020a0911041d070c06 73
    0xb43c403020f084200000440b1620715400d04c0300c00e02540c80401c9101001103038a940b4030741c40c00d0486070034040c44699264080c00554012941400aa00f015004c0000c0b00780d040303203400100703000600d40c0d00401d112210407011020540040c0c011a040340c100c140c04208180016081c1d0b0303009508520010b0141116403140c2c40b00c0d100d595900e40c0c0146c0c04100000c2030542010792544259000c0e03804034469503d020b400c95003442034150110501060001c005403e5214074040c244406001c1400c8040307a0b120103582d40b000865520284820f8843c40401800342410003e50301014003500384400c82036080d54011305401c0445240b001951369810004075050f1040414508480c4441c91072552030902d401c024820003281030003900402c0c3e40c41150440c501d4148510000700303071659604da017420700c4e814524018141c4441c060ba40030490080c0860030343c40c548240070002c0300c192881c1e550b59181c18190000b00140051690200b00040b0400c203103030307410984400c0305e25480580021080003a08090310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 590055557 1250 590054307 590054317
    0x10305070f2a0b0702031207020105010f21061806060801141909171b0c130e0124050a1203120f1e1505030304050a0e061f0f0305070c0506010302011103 67
    0x41204074034240800c1302c2c0c000c001071800e903001104010303d5950f03c0d14207a00741c42081c42070301b404c08042503003008040419291403850629190a401c001400398036081c0a80f01d64036000d102842100c0182c8041000510442c80141003040c020300c6000c007075581c0000d43c010002d0403011390159a001001e0b6a046a5002d9801194016464200f500e014414403909030400c07401403540ba82c030044002104000002c0359800f240c00140044a00c800100302113015040c0300007480b01c1ca6413251105144111440d648803e003644d641001c000440c60001004500c58490b880580d02d007d010f0704103800300340e0180c5d05c0342c40000740982c0440d42141c6403801c00020141b10305140070640e0014420081a12950008080341180d440600c03440341c0c0f81c000301a241c1c40350344110750340030010320401c0203085014500300703501c040e000b130115a0407032030000c04254001c80c1c00070000005e41d005808007034040d010300c500d58010504d0301d0241d402400e03507034dda255944818040039061080d481552050b400040040b20303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 590056807 1250 590055557 590055563
    0xf1a090a0e0702060f06060705060103020609030a0609120305160e0d020f030a2a120b04031103030408210919051002040e0105040b101d180103050c010305070f2a 71
    0x154610b411032000b0744844064032078107032401010740416500c2ca403603020340b9040d50b0800050f01c096443c4d5400c000b21644019040da1300350151080c15000300d14a0b10510107030a01401071014495206a4002c0840300d000b48031b4003d010706c4030301c0d46034041d80c0000d040395001015103600070322003100d00001d405041d54070501c07136141c0b050903640b00c100b1213815094030a008003140c0c4424140b1001c40440421189400303156a04214106000c01240500700c800d0f402502900f03165048000d8050942d086510840c1c0c00d9442c2e910000e0398044502080480450807000c44820402d030b4245030080f561110400448030490781400040841401001d02c06c4d411520f2803000f01b190f5441e41c602400407000030910916100e82d00d051400c0c40503090030307200c02000d00401c1c1d0703940d407003020081800742c0b41d035040142c83c0380c003c02890410340ca00b0b1442d024003800f95010300024400c00044500044c1600c0c0010070311400c002a00c811705401ca03030081264038103407a00c1c00c0082480b074041008040800c8542c840a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 590058057 1250 590056807 590056829
    0x23060d110a02010b0906220b04110c060109090c05091017100501090513080a020c03060f0f06030a02031b03010b0409030c0308011202090114060705100608070f1a090a 73
    0x28441032103040c00600703007a60346400038800030604204100c1c4201044a50940002c0d500141c0c0d1600502442e01000130b000070080003a2862080e0040740407201403921105400500148070103d9013420001140180750945091149840e641d82d0088403400d2841014007604600d80820301c1058091409000341c0440c0e400c102c02101c0b07400050b580c030124000555804c80c40c0200100b10480580995031083c449400400c428580c1c0e0303590382c1c0381c40c1d00003400d4a085002c0e410407001c0075a02481000e008806440080c4024105010740c808440c00161420380b081d84411159001a01c000c10782c4c0c0071120b51b02c2d903004005035081010034003400b044420b00ba07100d03207800110801c01d07802440320035840780a5520b030051682c0b0383d580e16400710100c4001944c05034135500100b008100d484400384000202404150030304e801d658856240c41501d124415100e600c4400611550004000d80802400b60180d801e0003a031401099440c000482169001c401c40001074080041d00c4a140c000000c14281c1d4803 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 590059307 1250 590058057 590058071
    0x903030a030b120f1c14041203020304030c0e1006210b011103031e0c0301030809090a060302040f06050405070212032e03030306050109061403062814041523060d 71
    0xa00c45d101c502211404801c0714400c15858107440c42030005240344c0d000004840e1070107043c480a07041c00190f2590890461104100100c00200c0c03000400c03008101129410700c85041c0f4491256000e441504590100584029600c0c580c0d2000e87c1e0340b014803081e20f000002e0f4040310100480d0800304c0d054994903580700000501846004d2484004010f4001c0b01800c0080e446404046500d0300c0300f840041d280b4101844810642d1902001d80c641000881e40001099560795000c102641c008480350041c0690760070042200f800c5c9400b61f03039400754003403010749004415020141c0341404083c2c22344a0000702c1d0b0303034030000c3c41c0e0701084541c60408458118442e6555a0f280040c0507040754000c031030005220100000d0b0650040d20015445c510b104241820340e5600c0c002d12403600c2e10000b1101c2e030301e1012422580913050a1201d8405012070711494480c86121000340000c2c2c4201840c4403034160503188041110f46198400140040300d5840f000603002c00c200d00041d203a00030031484000e400e2504203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 590060557 1250 590059307 590059333
    0xb09280906030302162c0a0605130209040c030606090e06031014180a030503010b0306030a06020a020f010b0909121b0d030501080c04050c1c0e0109050a0213020903030a030b12 77
    0x1180d10782052071103a260714441d00c8000f454948952540d5500c000d1b040c0d00700122000c42418807096122035a8400041d0f090380d10b100040c00e106d071414840c12056400214080181072901404602c0c1250307003000c0c4000b900c2e150008211145911035071b400c400f50745012801d2550144960518205519000d1100d641544540c0511070820307242544900d41d80514400e443e00c001c01c1d0101c0b02e070b0700358072500e04680c80d042100d4002d900040c166649030003045812000240c0c284060405045590b000701406403404200e00c0c01c407903a124000d80301d035440301c0070807400480001c3c0a01070700c02c090903d507031a000d5240381c441c844254103002480c640105c80c20301c221603a0551000e4100c85c100001c03103d00300401030601c800c842098410f2000200104000003103980000e2641c40e0040c040c88001548074103061032103007101d424000848181d042058500250f107003114003d081482e041100f10314029080f40000c0c0d4030f1203101d00d40800e0686901e00701c40140d51713002064000300d040c1402e0750b24803901c0076 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 590061807 1250 590060557 590060563
    0x10210090602041805040f030c1109090f0d09052b1415250807090504060b030f0903040b091e0d03090503011506080411041b020105040501060b09280906030302 70
    0x8002c0c0740d040e4011410112801c50781c0e0241794002e541040c6000c07094001034030116944021410709a43c000401c1704680c0340c60300c8440c030a500c2036600070094aa54100080010f0410a800c4410300400294003401d01c456a0382d40c0224600d004400d0941c055175070018222103002c0c03c052405841441180f584020024011400c998a0500103004001c0360365a0126078901c44045c0c03454001200006800350006402134441c07903000901400e00c5100c1c180da030000102592900d4026440742c2902000f4040000c0d13200070001c2d008040007005d14103050415000c01014051504d40b644035605e01130940d048401d40a1207010f886001030001e604140c4a801e001c1c03d00c80480c8101400380d0320b805000c85101d00658800b400b82d402560302c0121030b03126500c44410b81e00b00900030701e03401551b42c1901c134a000f0600c0400d4007a51490f07000450a4901420140d00b110101c1d844a03001e090204110b1506595440c015841904030343d0340d81108004406842c2400300c7c0355086036031960f19090011090503000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 590063057 1250 590061807 590061809
    0xe0c0c15040f0b01060f050d0e0c15040f060905010c0602091f051c0b030a06050a0e06070807080f0408030703091b08013e07030c021c03021c020309010c0201021009060204 75
    0x40f20340c1e01c41c0c1d0340e8840080f960444094061030005500b4007070009007041c184c100200700d040100444a404040e900014500a4030040403900804005401c1107030304803a01802000700101d05200c49100e140200180c02c05d0b180440007000b05030b0001c0d4503285555490680c5d11050016051071803a420903200240003540422080d00c000300181030b1a84030101c00c0d004a0741e040301c001d00604400c88072a901d1102401000d40000c00194072844124804d42040002c248070305070359900d04580703080017500a07102d004060000e03400b0818600405c00030a180d201100e8100d00145400a420744860410192010350140491442c2e4042e180009000340c0540203080c0c21a034100d40e83e503800c20000c3c0003440c106d02c44440058652001d40c408003a101201c2c01606031140031f41022000703034000b94006549400402043c0d44000074000c0c10009043d410401d801000c20b8550149400d40100c02d0080e689000c0c122105040002c08108002164400d0040007000091100300340105511481c20030f0180d009 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 590064307 1250 590063057 590063063
    0x5071206020d0e0a030909110d050c03040308160207030b090c0306070305012102030c0121020c010606080c0903060f18030f0c010c020d05030f22060504050d0201060e0c0c15040f 78
    0x52040074424200b01040c44c041503641521445040d51034a561f031000b5003c0000784207841c5805200c8035410160501880d0703c5600b0441845550389070910b009041b405000c3d01c1714080360040140d41030502d070005011401c0d281c001c0e007c11082d0340c0b8202003038913013010030107210b80501400052004880d003580101c1c0c161905920122903052581c0c416110958013100040c0d4540c1c4801c268800550065203089441ca44105274504031907000601c19007a07030720840e01c100c41d907992040c0400280e036028104039088103201481c3d0385001c03003180c0044d42d80c0b080600440c50f4000b840340071520310038407044201240b440d0501503984410452086265581191082e54101d50030b0180b82c82a09102041f074030820007651312140d0854441d034114101c80840100a064003803181c0c402803031303003002c1200341d180858850b41c4089000d141c149065420900960f4818066a0420600f8403c10703113150325160f031111280c000541c888142041407403170080c1031001d440c01c481d074400511080c0319181e41324041d0302d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 590065557 1250 590064307 590064311
    0x402041d06040617280203030a0e0102010c45060206041209081203040201020c06030c13050405010510110106032a06091a16060c0914181305071206020d 67
    0x2544000a10040342c10120390602c5410160b00c269005e1928036056001c0b5248140c0003080350580d03404a807566200382045e0010407928a000702c510341e424051007110b698075140401001020035020640309444007070b8660070101400395041c111041c100081c502d04420708001245a95520001e0345881060314141c49403020312201c40c1c0310f28083c10000c0d044504a40c0141b410b10300d441403102946d0000340c4100e0460003442114200d550368140918080c0c0303c0c50480035542d40328049000744101c0d25503c81c0e400340d4102001001103580e00020f042c403000725400d04100040c0300d550081d00400c0180c1000305180e0b211941311141c9040084c1c0b00130380d80b0001551069068450380b0545030b80d01c0ea445004200e21059001000362000b03440074001c600544070344c080070f01c60155683d40580f14800c1c9040300288101c4010042101030040006840e00242d0300d02c400c640d406040022840c40085c0540e480c42d0b9141c10a0701000030030000f0344001c08001c00350780030100803403508801039030041c60300300c00d168 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 590066807 1250 590065557 590065559
    0xd02040b0402131a0306100810051f030b0a0b0d090303090501020d0b13090f0201050d151502010b040b0a06140403120513060206090a2006040b0a0212031e060402041d060406 76
    0x1307944008903070080b2001012007540000c1800100c8446c1030003818681903d0201d04005865212281d1b04400da490403419032021810702007000381283c1c03072100c1042c4205d02075142000035070b050108544c0018140074000c510603016040c00d80140c000808001c00942c800140c14104ca02035920108415108840f080304010b03081b802c0c1c00c2034401c0300c4005040f00004802d0140158040c000030081008444400700e10000d10400d51414850143d010212842605101000c915421b1081c8050910103c604100201e05400032440b040190300401d0240325958400c0034000c01c0d03010651f00103603400744101840ea148440001d100f904081001c100361101c41801143c01800815031a1103030300060014140c05400343c031108810403035180f1401c2841030b4201c0080d02ca03104c4000400103843c11006182d95101d00e070000034901130031811a44089402442448109001e200480c0b460315039030703a01c21150b070f00ca400000b070082c4180da21a102803030700c079510100d11070207450000d4841c4d0b10465041181c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 590068057 1250 590066807 590066849
    0xc12070201081e010e15091008070801060e0105060c01021611132901090503070e1902090604140103020d02120a0c11152a03191a0d02040b040213 64
    0x8020b0100f004103600502c10300510620f165055155440458044628480d1001001003042d0041c160b070405e480c41c0c04088180b160382c0c8204800e00007015910b0007040450301e4000481c10020b418002c403441900d00244469a80b002501a075010104ea10100e1045e1285c40c9032001c6c0c7d41d611004101d0191300d03131800c0109036461910600b1b106401d400e4080c40c001d07840f02d810880c032100001c0598180100030502180e6034400b0081c44000e4510031190b8545410000d407004110b8240241c1c6c80c06036401044005001c0d292403094604441c40c0720700e40c1c3c80c450751400c01038010703015104410903414404241a48410b511413200c5001e4001041c0401102da50b2410455000030106c06c00302c00d03035200c2c48103a1407140074010f50b00d03881a03041606600c03104203852951442054841150740702c04010040c802101c0c8411369035095030084034810091004640790000761740c03e001c020540b08554100c3c0e07400549d1650780021050030001402155074080804440440d02c0d03c900401440c4213295142500d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 590069307 1250 590068057 590068081
    0x60301060e07050a090b2a0303100302010503040302101e0b010915050c010b030f06061c020a0b0705100504121719270b01150206190e030c1207020108 66
    0x160303510034038100003550740c2c18002d40300c039071004004004020a24400282200d0040007401c06030052000c0b0040b041040110854081060043c80030a6082003040c40324081e070b080c038011700700e940c2820125100d83d070300d0400f81e06140010400c10030303030307414419074034038002e03091824000044c0c041c8810480b100e821801110540250300a949a00c6091560000401d0249000e41885001000081894002d050104c0d04000c40f16800c0302d0194402c40c180f0081d490004500c101400080c0141d1130300b205140c0001d412a0070502c6400030a41000030030800780802409080f05000d9020814010303420b19107440310200350240b08100019140e0b0728020001403400907400d005407000c16404a84814104c20b0344000c0060301c81030006c6000b901c8024100d0307910441a0300496005504403840c6601d00480e0306121500709400e00c046401040411404410b0701003030690031141c20340b0009403920343c10b00345071440c450624a01d0192150395100c41c0d0950740c00006040340741c402e0369800f100b51200402880c0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 590070557 1250 590069307 590069309
    0x3060807292b1a1309020a03110f030610182c0d03060806150103140f040b060a0602030d0b010e210f0f031215041d0f1204032003010501150806030106 66
    0x280d0001a200074a001c507407404d00c102c50203038000313185080c0e64005a100b162681c4111603483c0307040c40403066480c007400d0241551100303401415480c5840c80c60880c0004450042c1150f40485aa007494940d04c40c0d8401302800e090310020b503100c0528011203414111003100404028410101410701207071003400b4070b004031400701d0014400c58541c12198601401d10b403202c1d904165480344401203002d54641094020005d0100000041c1840d0402d0a110100105918000d000c030203010000035a0000441d102a641408001840c081c80700c0100c0720b100701503004039400042c81c014208045032400f03155060a0000089519420000c110300762515003980c40c80300345070004c0c022551644004100b280d400341100c1c0810b5424555107000908451120602101040c2d0740c40e249a41c1402c00c100490155000000401c0c0743c013100382c8408228403ca00004140d19039005a2250780c000103555a600030310b00800070b001668580e801510408900c1149600055451001c02c04904041c07250760 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 590071807 1250 590070557 590070581
    0xf0b0c0c070522140106020d050a0905091b030c0a03050a0c020a0822030c0503210904090c080f0c15030c030c0c100906061503060807292b 61
    0x101c0d041d46002c040140361031181d51580d00d015240090007030744140520035000d008860741c6803000e8a5040c0701000780740c810003024150501000b000300b0607005130003411180031500125034152699a8884860062b000e4011740824061008028050608403000240144034040c0d503040200b80e41c0d08440340103488d01540d031070000d6081010850082a070070780c010004540c0e00d4112000d1000c0020790402c0b02c4c10194029511440b0881007408503140030b200320070340d0441580360b105c1d500350a420903516520901c8412813146986447c00010000207a407140c1c0141401070980320110003001c0070036201c6407017280315803060180780410100c2c5e581100940c2c1c01203800704034250075072f51661340760110b40c0d00c80710f41d407000361040c18141816542540162050035100321000318803e480c280138034916280210182062508006052003c00d600154060850b6060448918000c00350303111a0a540072100711141c5841c40040c0080103c000142441d40022450032100d8118030001980c10888500c05108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 590073057 1250 590071807 590071813
    0x61409060f0304031701150f03020324010c1b150c0b071b080a0903060f020a020a12050f0f0309071403060604050601050d020406030e010b031908071502070f0b0c0c 72
    0x7440c880d24501014580c03051003420705d0320390212080364104200701c0987c03003040d00700d0841c40200d040961040070003445c4441420158154103013403030000f400c60f83c0c1340445240b0380107059039980319a20400c40384851070340042101c202801c000c95030a0f545500342c040c41d1190310090150b4014a4402c181030340d030f00e5030810400342039a1079648040380da00f118035640790a0003a40900381d002044c82200204100003068a45441ca43e1441c41e018060301c8102503590b00c203034814042c4859068001c00d00700d8041e03071f10200c2c21100400f0a00c0a4800e4000c0000c0c101103071001060f20385001250a00860040084900301c0da901c1d079681001c0d003103801000759040e80640114000c01c0c41c0381030070b07040150403640c14142542000004081c100407604658448000240c4070f1507200f00c2e41c1790038400d20860f0f41040c0c011b000d01c440b5000c9500d24080c01ca01c0010880c013070001e02003090201e4008100a022445c40e0155501c080300d00f05451340129028007035a900c00700a001c0707400d115000045600c0752040c031000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 590074307 1250 590073057 590073067
    0x18060e010f12060605090106020c0a060201060b09131d0a05101e0e011b09030c050303032a0427051807090b0d02040606080702060c0a020304050904051c03020406140906 74
    0x210602d9405034084401e01c2e150900445c180e07a5042080380a003c43e075000300412800303641082403d07100c41e44a0b00543e45400002d008108030402181e150b99026a0040c0c400d0307002800020080c540c442a0140c0c0d10080300c0911030700364021400b448058062400c44500c0948428020100c801d10b940b40c0500b064464140b02600140d03400071901e04400310000210750000458280b03119000c2d500c03e0b8009450050144104100040e000c800303454140d00440c21072400304940b4000074074503c140d4244500a20500e43c015046e0b0302201c000c0c200f001079951608500342148070b0f01102c00b0003030750b40d06420440003c1d90f00555440101807410140f000300200d81c900401035000740032030351030242c100f8800341c04040036842c3d078003605005101c5595154035138030700007030700a04008010784510101d44d420020481c076550300100b42e400f42e42084a4020064a480c54102d20b882b40c148044265501c10985c01c1e2811a050ba0181080740e103030341c0711500200e0700c403004c0c60514032544407400c9e840502800f03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 590075557 1250 590074307 590074319
    0xa0c05031303050c01110912030403120e0a1701020712210510050405011e120305030411010519020c0f040605010c0618020316080d0906020a170d0618060e010f 70
    0x703803901505009003480b9182a00c0110210b0a4400d258005600300c400020068594185403101c8013480d11440003550a02d421503441e410541542006a402c000c40c03641028160344c2c0700020308005108085010300b034401003940e228041d4004142c15120400401c0d05800c01c1806010780049410b600e140300c00daa8590344161354001c05015041c4c4841c14659040401c0c142c44620a250203405140036000c05604076000200560029070010856a007005910380006604001a81c2d00a580001d448444012500040f00c4a00911003850200c20f050303515002241e0300401d210622000545003142200010002d100c20344206100f0140080c29170502c25010850326448000700109515910000c0245600000c1c40c1040c5d141030301159030003016040000702010800b855001040d410a10022441d10001945070312440401800e0205510f0301e02c00c0c681c610b442150a045500c80040121503118006240c41c0390006402c00f1a8500e485401710342d02001c40030940c12101030100101a00d82001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 590076807 1250 590075557 590075581
    0x1a01031b031505030f03130b0922021213020411090a17010209030f0f012a0305040312020a17060a0f1a04090c030203060414070206060103111b0a0b0a0c0503 69
    0x30b4680c10940c0c940c0d803011519540620502e03030782d074204d640190f4035010500b05910085805500001c0900b03000c018210041d200e041501c0b0110320b001880031404030403144220301074451120207008007141e450030000b40e03c0c506010740300c6440c02520100712491500800340a6440f4648006912800e01402000225081c1503103851501d580c5001505044071000428a00003115a0703a000076001282071030400d103400d1040501030710b85120281c8080d042001d9403c0445040743c11300c01015101d10006041c18001c002440d01d8032581001150307104121200100569041c800d09140b40400300082545032400e55030080c161511720201072041480e08444440d00702c1c107400e0104980e0003e010000b80780d071051003038a4500c10b05440150742d91030701714100421180c2c4910381960b440180402e0082244e400605039501001c20700340050b03003e1070f49000f40c00502602240c180080580ea02c100a06800421180c101038070401c0c500c6034989807411803c094070908229040012014400100103500203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 590078057 1250 590076807 590076821
    0x6030512090d05070b190c0218062106090d0302030907051c050304090501090f0207030f0f09090914011d0a031206080f06040c0b040501020705060d021b011a01031b03 73
    0xd00001c0c6034030050b903506081411a500c0701c511103174003007140254052810307800d00e03005081d03182480d6035280c03550010701c0d00c40403070180500140d44903000070300648800c16100341215001058409030040034404513900c2c6070071030b07050340319003d04420078000a00a0090300d0003098a1001b80000b5030a01052250440b44602e0002101c00c029080801040e070600007000504035031940807440d581030480600680b280c201402e60a144104450070100b0b90181140540d865a07250660022100b403d08032a58110303500f1045844d480c05215804201c40d2280805a09181d40001d00c00b860410480020980302108501d180743c010001c80e500107440340c00110300c40301c226113000682d02d8465940c140b900c51b0405407041c0d1507001d501840b00348200b20011000a14058000c2c83c80c22b410140003d40382c206a10501d40200c2d400700b0407a41e0aa299010340701c545410200c80b0038945d014611681c040c0c0101441280807200c030940081d059482303805001120000107071000340031174988408030020505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 590079307 1250 590078057 590078059
    0x6050406110c0a11220b0303131212260403120e060712020f0d110904150311030c01050a0f020a0501050c1b01060e0402060c0a02030724030603051209 66
    0x6181036441c940041640584507510721a0000e0014510360329200e01680030740c030700d00c40c841c84003041e142400c0e984640004004030080c0701c001c162480d080c0701091030350054040381c0c046054180350210358050202d0300b01280c0c07405800640c0c0c1c000d000b0326081d6490860848000314010018128656410b16400e030355030464400d00d008000d90405800403000c4807209005401107400280521112980c841503183d20390307140c20400c5107804200001c100c1c00c2d200e941c10414a0075100c0c4104080704c420b81041c0e803480c40c0090804e00221009040d15025240940021a0f400c89030521030f0030b1505001031340038500780d01038450078039002d549882030b42d801c0d000e11814030851040401c078000095003030181c180602e00d1940403549980b4424000c00c03641c00803183d07108541c2e00d0003034100000100b540d0143d800c190180c42083c2c0e9000315400c1035041000f03a20b4040d4252080e02e20010300b0607120a190744606022003105002500300c0b03001201902d1a5100c041c18a900220501c038500c01350000401c01500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 590080557 1250 590079307 590079311
    0x130309120309152303040b1608060d0c090e071509030f08030415060b0a0e01030513030c0203071e050f0402090d02150c060412091203090b030411041506030e0a020a0306050406 77
    0x6544d07032441483e80e16104011003441c030040f09000411481d001025007150408018507100d08513400c0040c00b0410060400d44661b8000880e40207001e1320780c4a8002411032030030188448c00c900055a5a140a0361040c00c0c020703100740300303000030740c40c821003a40d425260711559581081c40151184100d0b0307000507100b91100004080001c9030100d2501c1340380010000c0034900394582040c02c00150842d1103030b0078a281410b0400040100c08000710354242a80c81d41420f003810291950300200c5d141010a401c0038915122030a20111140e050300c280f90101c850480d14184006046c40500c000e030f00610101e250820403182c0601e0044ca8400748150540c0c22240302c1600700006040410710b00f00e0256011355848074012400341d9295402030320800030b0322140318a88200d0b649035500030200c41c41c61203084400000440481c04000a003d4803084000c4000d1041c803c81145070b00c0150580c89903c10540420316048444455070401b090781075403150001c0c0728140311480c45e110400070f000e000b44100c65580e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 590081807 1250 590080557 590080577
    0x21207080420270406060506040b031618081501120305091002190f140d1403070e0904030f110f03040909080c0106030311010f050c03061c0b13030912030915 69
    0x180d80c8801d880310140c0f0408484400e400d06080210407107805810060003014200006d105038158501243d420000710842c5103031302030390804101d81003107031100d0240100001d1500041c2d90080040d40712400445c0d5070540d591640c2e80c81841c070341440707510b50080100f035061207981c50600d08011100d50380030060040d01d04c848150f2035810a507814008040310314880041c4204144081d9112000caa40c404c1e00003082490507106001e030110090720b03105441030100100282010303120b25019440c0d0307100a004080141401d103000380ca00f11a8048c9032001400c22041ca81c0e00c5600002c101403110100c101a500d081c1c2402a00406043c04803810740701100100a50012144244240d200643c000d5a444a0510000110700d0035102d0038060744840a0403d001e2003950b11a45044903048181155a01070b8070001440c0300c1640c401d010400b60010f00410b0400c009140e080d401c11150078840d507140a4000d1319405148000e00e520540a000582c030400140000c003820384480c455130b1480c0c24002081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 590083057 1250 590081807 590081839
    0x9100c02030c03070b0a0305010b070b010e0403051306050c060f040b06120102071209080f030a1d19060509011b05060406020f040b07060f061d0406050604020c030d021207080420 78
    0x1044456202c0b48003070800082c0b1b2041c0d264144602d5000d08040400a0318010003922800001d0b03d060207100e41504440c0040380805004070211000a485650785121650355180050603a40220800307004601408001440036840ca01a241c461a4440204003040e203440003448203160030840c1700c02056600b0080000400c545400002c0d01144541d1031480c42e50401105030f0900720420342185641d0320910145c100e40d9002807420b0500401082c500d600d01c08042c00050002202030018542c1c071036580c10221301280d002000f0a8154020b0305c501c855120120028030250b000200f02a00caa000000170500144050b0000c0040103440707a02e1508050f202c2c00c0451a507445040e04803210742d50795000300310090f40c1d402a04c0c020500c480c030500c40142c041c0a026000000140000c080c0340e41ca4000864540d52681074072690364070081100d0302d4140300c0700007400951040c2020303444141480b000405451203012140d1059034003401400c0c82c4e070b8290104594012030180c03080d6001544542da4801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 590084307 1250 590083057 590083063
    0x70507030c0f05030a03080606160213090b0912120601110d090602060a06050d02120708030d060504050c090102030703051305090f10290705190c03060c02010209100c02030c03 77
    0x958018040c203110030b4a044401e880a0b051035001901030f4001d000c07202d0200c1c2d00000c83c60351011043c0c5250356541510442011140203e0000a6005500e005191009200b96100c848103d104041c0f109240d100c000c90345070354035840407100b0300314203040103c92020030151f043c05801501c103041020300150b00706135403401c04810313a8000f000261130b010208603140d810404a1b40202c0008010030045003000c021a401e034200b900301902036203601c41c0e82d0b45299810080e0400400b900c109698461511158181c01ba0500c2c1c030507079100341e003000040723105520f000040341d034149016001103180070b25980d01500c20740c1003c01c140c80440360340c8a00141c50b403601c0c0b203098031481c104a981441483c005050085c3d030311964002c0c0d0369024910655495000003040307440c21107c00c00c400c441c1c555510b46001894009802d07000c86200d81d028400500300003010b80c0031000d40c2e1280c5800d020f981ca540307404034202e00401c440740342c0c01050010750402103030191340742a1000d40050240c4804000000210346 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 590085557 1250 590084307 590084309
    0x3130b22030302031908010f03031b1e02030c060a02031606060e01091b0249230315041e0c081f03080d050c040f1e0b2106010203070507 60
    0xf5030000035030720900c41c107841c082d10402562420114061f5050600c2c94000070682d0000030184043c0c4d5000c80788144070b40d2404400c480c0c0c0802601ca1001d4006105452541c44c03134000c80c001d00c6250690161b074600541a5200c3d00d90541c01142000c443c035100251a11050340241d4050380d44134004100b041803000d00501a0440020100d080300c000d404030601041401021011504083d0f003a20962009000340c204104291244100c6100f00144d8030103c5162a058101c505001c049072601960f00b1800444180003581152840c1401c5028054500d00c421200408030b143c00045a01c0245001c1d44903914180d004412004004a01c501c94400c035240b2100740c07800300d907040080140c0f0070b4920301c02183c948241455203400518540c2e503040140a2003080d00c050540303407000910318680703400541d0f00828440341032100c11a912801c45040072000c1d840f1102c240e00c5440d0220701d407030f01001210b44081011150b58100740c08548001051032001d4500750450004012500124074200040c1c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 590086807 1250 590085557 590085563
    0xb060f0109080327031c080a0b120703020307060819110c01050f060922080706090819030609090816020a051203090f0405060607030c021c030806011103130b2203 71
    0x9413410149010141c600820f4280140700742d004c1c4150380f40010b1410076202843c031072400c00640d01d486040841c0060100304124541040300001e40180d640d03400034050003180d00075015156040c3d03e802080b180480219415004502218002015002e00e6480340c8003800508540e941000350060703006095131701c240d5009517242d900c2003c0c058203140003600141c0003800110701030080c44c3e0440050041d200c031650042c0c2030040201c0c1c1038092001c2038100301e10286d800441d03540e542c00c0450098503520410091040000d1901c180443d102c0c01c1c0f03100e03544907150417041403424000486601803c15100e06d00880c0c1140c94524001000d4032030303200503500010b000d00503507201d00d103200500011240320390039244074500f008103126442d140c1034109c855494142c5010b20100c081030000c40c24441903682e02c3d0580c1b070f0013101074605244e407016507903008000c2680c8441c240481088026a01d00464172034007244581d02408119600c4a40000c000360001e0310500e01119a8000d20140213401e294401d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 590088057 1250 590086807 590086837
    0x1b03021c023421060c02191b030b01080a1506030209180f010501090606020606100912061e0203040b09060405060a0c0e0a09020406080a021c05150a15020f03070b060f01090803 77
    0x24010440c29000d50514010b041c07000342128005151060070194403103801408024000301e000d8000c0c00380b000ca102c043e4ae04158000199650b84000070fa552003100c6042c0c45540b50725000d045040100c3c0503031403c59400501d03004041d02d840c202400e0007410030503e080148516100650320803000e004690080004000006a00b443c04070040e050590091015214000064803488881d03041454182503c030701c800a80342e06102c81c41c01c3c00007007540303009100800c6070289950880072416001584654401c6c00c030341019854202030540d0b511019600180b00740c1003400000c130782c2e8020754001c1c5286649440d1507a0103400100c08030381d0900240d04044c01b4a40c00180501099410418107500020104402c41c50000c01c000041c0e45252040c0c04848403d88941c04581d0000e010560f2010707443c0c0007884414169500c04c0801554030180d00400c02600503400402c0616001000b514102508605202030715603034041040101142c0d0b800081c180701003188046640c1000300080c0c984542c0c41244 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 590089307 1250 590088057 590088119
    0x9100303170603152e0b030106051b010204030b01151e030b0307030f0f050c100905040207031403180127021c0803011805010b07020d11011b03021c0234 67
    0x2c40600308024003c117105a81c4000204600b650700d20489046031554580b8030349845d1052000d5100303e0010010006644c00814007000f4001140d01180c1200d071503519150680c072036020142c0e1480803103908042c0ba80c412101c0e0600740ea009420a01e00600d00809441410752a542c40f4450b00e0004101030391400389d03c42501e020080c0800818491900444801c100c041c1c4010008007004814014070f030250350080303075000401d1701034094030480d2010090b08503124a04150030507000c3c2c0003440d42903400e600b04640010003203e4501e02444000202d8018200c3c02500c0d000d111120408841040c0c07404600c41d6504003003507024003d90f000c0c14800409052510140080074140d40c410b030401030690700304004080050b80c91619805842c1d03840782c20100310060240041e82e01d442e10701048a9456030840c0d0340d01c00c2503404203400658024546820000c03ca011078103c1e981c0d00165080c14048890410705100800c03580d0343e040d86030582d2400203400310303142d98000e1b00740c0102084041c2c00b1100c091f5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 590090557 1250 590089307 590089351
    0xb100e0306070309080a03091a280b0109030212072105010b19260f010902270402120307080d0e0607020109110d0206070f0305090910030317060315 65
    0x703602c1d0000010319007442107424980398401c1034410951444140b40d5101281020401d41d6001c3c08600e40e08181230020307902d401410019074a405c280d4130100329640060550900f0300c140f007070440910044e910000c1e4942943d080c40344010114032241810322440000040140001c01c0c0c0790103a0900c1107403200c280c003a61070010b00703540c4500c040a104510328003181d07020a040c8030481c0c080750400703452902c511010400c4c0c031410040600d880011b6008460b40010324640540202d018070303100382c40300803510165410b081c220090342030400c445540802c001c40e016240c030940742c54034100c0352170a0b01c0c0b6244241d03a4030401940041000300502f82c81d21400280040c040c08451340c40541340c0003e00c980d401030b030760304859601010003441c030486031103014000755200ca600b95a0b00e103900c01c014003104002410041c0031504031000e07984c482c0980d8400110b400800d80d0354070040320303459224040300032120701b0181201500140b001d5054492100300340d0088003845510348c041c0503c0420004000c01c151 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 590091807 1250 590090557 590090563
    0x901120c0b030103020105031623040609060c150519020c010501090c030506090414072706080a0804050d030302090d11040c0921081210060f0801080604060905010b100e03 75
    0x5480400d10705020310041000d030740c22070101c035407008100c540d080000000f020240c0c0c0414a842c03603104a40c180c22121401c030f60b5840010015038100b52038240126948040c01c581d65071202030010321000314082e401c3d1a07034055411180d000703a1030320081d00d00384d031800840038120380128031021444da44940040209189501c80c07021620100e1030240040d1810794080786410102400040261040740608084080f084c44100060300350308802d81200412107101005440ca48055a030700c0615180d0000350711140060380c0c11410394401c100c513040c03929281c100040e0004420b4203405042e000c122440d05691062000720246204a9a01b01d90400c0841884102e90304c8501d80c1e824404601e00a101c0c6640395075000981e40b840300e480a501c52014680300b80d0500900104004903c4070301300344558080d40ca4580300c10b13101c8569400c00241420b01045800540a104042840d0810008540410842e411109240f4025000407440c0c1a20a0205501e0031076203010400060000603482507c0c5001c2c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 590093057 1250 590091807 590091809
    0x15030906110a051803012405102c0406090c020105100608090a0b04020d0b070914010503040809060304170a12050c030f160c060c05071a071d0105090901120c 69
    0x45041682841c00c0142d0103041441000304900540340c2400042400780d03003d4001454200f80e8403030140c0440640c00601140c1c1069019407403085110015501080b4454040560a074000e44900c184561000b146203107058080c280c070302c2c1c009880780004500d400f803501a00003425595400059186000d1800c0b00c41041990450350811542406004428000240f030b0b41c040c2d03400a848040b5500d840c40024002c1c0c0c4001e0340109007003580410494000d401513580300440d82200c80c403411806500300115601e20080b68001c110f0b110600404209080c4000a0740e44148a840344140c086801c15110040d60400d0250b1000500440b003003541c1d003c954021142c100203103490807825401d00302d030b503a00c2c0b5910082145070b00c5800c035483c0c4102a4400c031266081c10b900f04104001007501c0d050001c1055101c05010b80702120761060101089507107200d440d20502003991100c01d8006580c82c0700001100280c00c050400800b406000000c2e601c50811701c0c02051201075015140c0898600140e4035101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 590094307 1250 590093057 590093081
    0x70305190f142209050106021506030d110f100b0f031b240307020c09090303040308010b090301150801020318060103080d0f1107050a03030e0a08070f050715030906 72
    0x100740304031066600400501e5058004006498a89a04450740728420388044003410b5201c000e484000740d4045294004c60603a80c2907400e840c4200a0350011034004002a100c06e41c1540c80294045a01e0703200e003246625445d42c400c195180801c0c00031407036244c41013403044070b502c0742ea0310b40c2108003524051780d401c04000c206034098914841645841124200c185070002e00a900c0d4540400d59a0461100f0071013035054081100d071a41007142c00255500b00150000d40a800e82c5008249590000402c0d01d200300da041d40d4120003603003001070468440d003000690f10f0b0550348404001c030000311000c00b200c01034143c4000040e08c072f103482c041422017442441401c080c40d0300171200500208000e041190b03841d45030702c5004140c2140f61503100006000400119a00c1c600201d82802009408520b4a401030b009580601c407294440402d07507120200344034020b1200004101c150002401c410131100e069008200b42c03485207a440682c04842c810740e00d400e10001c1d17516a410400c1242506c80c0e28481c01e0303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 590095557 1250 590094307 590094317
    0xe010201180c0b160c03080405040c0905060d09080903070e041209060f030c0c1e060e1c11010204150903030906020102031005120a0203161d0c09100201090807030519 73
    0x410303602c80001100c400d01400d20000e20005002c1c0c10303031440d40e000407012a8048800301030765075681400d0280b90040c4c056280718a04050456559501c15035808050f1030700104610314206030384c5132800003004e07440d000701c03020300060044501c669000e0000f04000c020101120b80c09141c589010030740b40350018884401c1c0f00c03089000340b2605511400406510400d070400198110603208150b0700c6841d80400109400720101c00c04448581c45203511320814410312082c050400600d18880e1180328890000c05034800d82a0300c44100744c40f588a603107402e00401d00061400b500c64110300031845801d0080000303d440903200300304159015000c00014900d0388005c50940c01c007614a005841c40f10712480b845800d4580071201c00728814840e41e40c4a036402412036540c9d8042588015400d40107110345400301d00c00d265070040707503a0312414043c850794211a104c0e00e081c00c101c0405c103403007010010010071996515103c4002900a100418009020751030741c070784a40007a030240700d180c03010241c4201009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 590096807 1250 590095557 590095601
    0x1306030617060610230a02010b04110306010c081b0304060807180e0c1323040605090406020f1c0209040b190605030c0909010906080f0303240a08010504030e010201 72
    0x4408035246401000840d90420790300800300c0c080710b0031031700c0e50340160036044000b0301d545910114000401c503690164000344014621101008119507560450400318542000050001c0d845261103000d40c2e80705505482c20818825030100300c1c4545600000d0040d07200290601105401a0300140e01990302d28240814030103100600c1040d800d94400c07107404c03401a40105100e156280c040d10180401c4c10303032a05090f41c0d20412000064011840301420b07598280000c0703003a040c0742c0507810958602a14040310f584903503880303a00a41c40ba009590020380140001105004009045907052081e50400760700c40025404101c116000728006d0b0f03102c1d82450010796203601d0424441c0c02200d01c036003030041d100d0382c07410214a02c03407058042850f8800304540020400c2041507000c42d0540301c508007104c6241d14854110790b0fa0b8071040d2400704006e251a0843c84100f00214000b8580100140c40303810900d540360bc050f420b4580648040340440c042181c5080e00e035909200e508104031500010000c82 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 590098057 1250 590096807 590096849
    0x120309030414040e030c07421403010e06090f071d0105040503250e06010915090b03070e090f13021315030305071e11010c051213060306 60
    0x2407080d44100101c90440c1070031110305036102e6100781440051202a2592a0079208186850745450f000c0c00e05e0282c2e0307100f02e04826843d41209045d0b041311040340e4165211178001c250b1500d00d020b207003c1040108650100c0d1288136014040c2d8002c0044d07040f1460142091400c226040c1301c024040790b05d11030040104001c69030301c15000380d901c10361210f281d8400b0880f100100c440340700c0c5400082d098030401c49405080200c62055540c25890320106d0f200e81170302c601102c1120f2384192039250000d802240c0610605694246600240703030107040610090341c0c0e581c3d90710055013040302d5200200d03d6041c00441c1c182042c3e5442a030058051103072007480d151024070010760703200d186400303030184881511540c039007005544416160414611214001d666916000701642c0c40000200d0340c1061406484001801c4811038003003040e0b100c80c0d07400c00c1c20412401140c0011440e5800d5405128000c0710205111000008100c9619041c4240785400e007004005803c1d01c1c102d0b802242181c4c405e031110038803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 590099307 1250 590098057 590098063
    0x702190308010b0d060807080f060c0703091509180b040b090c0406121514030d110a080705150a0605040b0306011212111606110a05100c2003030702120309 68
    0x41d07a0f1110441619000954441c000410213500403c92603c542c41c00841d1080307000800e980080c00d180119821942c80b00d6065030b00d80515800140440d01d5030740d09000c004484102e001e0001880d145c0605296512804070040003250304e5000901d55451440c2d010fa0304040c060300001034001c0d10102003509114880003110320852240c2070411000a25400c000507881c0c0000200925510b50407051544034084c00500224488900d03200b0b01c1103d03c60141140104a0032140c0c42600014003011181034031152180c4e84541c0046809009141030340d41d81c10142d0901e54001d500703075000040e0403800c140034030044171020301080e84264812801000012440c00445d8207203944822044a4031201407000c1d65810894012003049020b01c3c400d404205c000354225000b1142980c1c3d0721a6004500402d0640312040100060100d1304208801011611039412120218140d85403440c0d0b0500d9510003903514039100080903a2a030000003e100500c0d60420840e0907030f1500b0b4031260704d1400c0c00384040d99 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 590100557 1250 590099307 590099309
    0xa091406040e0304091506030b15030406020a0519170a020909060609030c13090c05060405093601061415160314071505010603020f0d05180a050303070219030801 71
    0xc030660320303103650b00b122100620641c0e0060410340030612011a1800300040c404640b8000c0800003807520400d01e40742d2401d080e444030b2241e10101d0103032031522180c5420340694008028102801303000c00107240255107000706600a2481f46e600d0030482e15208204080000002c0c00b5038428a0041c89021090b56691002542004c0201c458550340c0702e0b00000700741000b010603002680001100c44054440c3e0302c0d47c0255209078031075107040c50810348503010043e0500450052680140030340002905589100c640200e28012102c0d04c8200030340c0d00b06410341c803041c2c2402c092310241d4503140204460300c0d00c0240e000b00c60904907140c3c000c14404c0c091030040c41c040c2943d00905460088880410316004004c40754046000704400d6a44d0f045904082002ca081e4100019540c1e18040000941c0380c824070a075144000c4010b8a10324000481d03d03c01c002c0c11010300401e102078400303900712400c035400f003010086091207030001d191a45401c61011341047c0c01050f00040400045d090440041d81c801101c034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 590101807 1250 590100557 590100559
    0xf1807182d0902031f32030c0a061d0f15030c040506040603060302090f040206030604020a1b0c03050607081303050a0e0d0638010c03110d08060a091406 67
    0x1c80e66820414140d580ca080d804081454800420b0180d10741069030100c803002e9404075022002a07580d16800180c2d480c0c60410345c00740f00c15048078410903a8080324000c14100c0142110003040000300040c075110070310f60000f8081404a0003080600c0c0d804414640c8222040755000c00740190003010070702c1d000040c4014403282400100003042d030f40c1042c0a98019020113000c0c99151600c0d1100540141300c180401d030310a28800f0001810312220b903a026200341ea020780343d141951101010b210280d00f1a4a0385400d100d941004148241c003c82180c03807225021310718200740107256080003400c0c13103c046d00312000c00480008100c10f0050720190b40010ba58949420350ba80c40503036a08599400110322a2a0701032944180072051041581149022194841c00c4107060403441c0300d107903527101407030902180c00d1801703400e41c4680758091555600c0c103902030700b003c041c295580c5e0340c89400e0032002401f0a000c10307185003d21440c1c0c00d095079107401130120120708100c0444680041640418010411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 590103057 1250 590101807 590101859
    0x50402090f012007060807121b05131a031b120c070c051201060f050a050f1005220906140306040204050405030f21060616110f180718 59
    0x105415a03050703052400c400e80f0100c10f031613219840d034000178a150f85c01ea0b14000001c10303103807207003120710803500c81c07000380001c2d401c403081d40c40b03102d04400c0d01c445d00131410310304100c2c02c004400900c44035041d020760071880400d0141030b548c5c941107201601c00c05c00c40504002038001800b021850012502603950400624002507440d041d00345400b4603242256004143c00680366912104000c1d415040b40003541e04009030900815110400e02c810680340707100301c2d688410645980f103010f0915940c4075841c4c40c11840e040e46816108001100c0004000c0c81c04201c950070560104900b600902c04d10015000204140908100c2140029600d09018001a205640d07582c08a010450200b04480d142031110000540b04d40d42505440019119032150100701c0c0070309c10029122345001400c468034181280c4140042c80c80d2602c51400c11042c0e400500d802440c03482100245030384800500c00100d51182650700d1925091500404c8100710030210a41e0010805043c031000c03486a448541d484207032100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 590104307 1250 590103057 590103077
    0x20a060513140313080c0a030803191107060501120c14011106071119080f1e0f030103060c1d060d1509060f0f2610050c090a050402090f01 61
    0xa042007001070030300040200c1c2d04a010504001d102002a02290414000000f04d855072126803545031950303a51102d9001240040030310000d12501e024541001030700c03001d080300449860740c901c00c0f250300444103034410340b001c15410200030050050b82d000d0039844004d4a40e005042d5100c074801da10768000d1122212142d01e80c1ca100740d2140040810a03100340d011500e16041503c005008e00d084201803401e0741c000d268652105805400c040071020b603100c05414945990b002c01601c040c1c1100062484082c0328a607400d1408580c04003a052000070180d8140d0b59502d103282c0701e0115408090203800b40134070320688066199070250f40181c84c100c150341c07855071810007106000090880b00704035280c04d040c080b030100d440307211740d0300400c1507502c0400c907240202c0c0c880d040100f0283e8580b0501050341a9442124800d40040d643c0140002d280400c440d5a804256410400d8071000c440310240c1c1038010030040b40038a0094002d000400c007d80d002c51070500500c0c04200402000c0f0401c0e81400b0403018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 590105557 1250 590104307 590104321
    0x240e0d140c07180c030b060702091b13090c0c0c0e06010201090c03060f391b03021f021606050403090e0c04081605030a02090c0f2a0c01020a0605 64
    0x1140c007040790500c15550141d0303d801d40042d07010a4410100c1116141c0780142440c04e000e0310a1109228008040d60308084041e820003900820007052041c0d0116240d040e8040b0402c940003404001c0c0d104216003c41e10300f46040c4000301c0d0076803040001001547c0060b080400da0918860080d29440c1d00410810342d2504010303800740003c1c202c0103003500c408850010503c00558803141101a100350140010710000d589181b030310410800100342d0101d481c124521940600d10881154119424101110b00210031404201d00340d0103000d0703025800060000d10a944035030a4070506020004086003084444000c00c00082009480100516501d202240034036024211a130014440e076104404185026034507180f294000380328400892089102e1003888d0100920140207441c4c000c1c0040103600d030380d0303020000301100107420061150700400069400c04c0d1030600810035942c11541c414019145c03a0540c3c00c00920f0320708000d0440d0041850241507130f074081200700c0441d8200d0800300300760b11214 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 590106807 1250 590105557 590105597
    0xe16050f040f03021513120f02060a050d0e16061b0f05100f060b27120c0a050303040e13050304050301020a08011d060114130909240e0d 60
    0x31510445008240003400e29207003038140e0180e901c25908002c0340f02060080044500401c43c0510101d009240f0a000c000540c210032038442d0f0164000340062a00d980112301e05510040011000400009a510560030325004500542d9a02c0f001040c0362550703141c00c0a00490103000302e004200c90b10709101c04940602c10380b403142d541c2201c2d04003001744841c41c041c0d6a6a14000e4119805420206c1d882c03140070313040c4108001c80f80a90402881c064408800c00c055a01110516240e0003241104e15042d4680b010a400c4000d01c170002841150341920800c01d03129006c1d80b000d403080e40100401c1c031080f00c0c21805117400c1480144a12607480a82c40d010781107000d207030081501907101050782c4001c1a44101d000d41251010340315100e840c44004545032540303604948560104400c1901046552404c030000c00754a512030749120241601e914071902500c40200c0180c42e036640003080748260f80d034840002507004440c0c000402140b660f2103440d9407100307100007541c401d000d811441d50444000380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 590107913 1106 590106807 590106817
    0x5180106080f090d030506130e010b0a080a210212070b0109060801140423070f0501110d0f05090d06050f15010f021f180303090312060e1605 62
    0x1c01d005e07000307444007400850b0401d08942e60540000700034800d0000840401c0008209070700d0728070030000b040803903400081081d00002c01c9c1c4400503002d0b04c1d1640300810341640c407401c1c824071804180e081140710070b201c0081c514000307007920402003041c0c00b05040e540c1c0040c0c200301494030b030000c0b01d08907106910414010310b00100800d0120761002418003400381c08440075403c52400007a1a41000d00710b9202100c3d500d101d480511196030000540b02c2c404c4d082000915201c0ca09840c02441800d0741131180050110001e0341c00d41c82e483d44e000c1000d40135007044084c4890b00303100504d402e20140844084c00302c0100750310342c02015846801c2c10207804000c0d50052200b44036107102000850044005074071001d40e1400000c0581981010007403410f4080c0c2c03400a449800e40c24040c10040d03a0481c00d039a49840e1210134800c0540d05481d480c0c102000c00c50743d42c01544004001e4900c1d210b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 589928057 590107913 := by
  have h0 := BRFrame.cov_init 589928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589928057 ≤ n) (h2 : n < 590107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
