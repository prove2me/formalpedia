-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2974
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:17:56.240589+00:00
-- url     : https://prove2.me/submissions/c137163f-e25d-4068-b9ee-988cb83aff5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 534712230 ≤ n < 534892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 534713480 1250 534712230 534712309
    0x106050a02030418091407080613030210111608090f04060315090c120320070f0b09060f030f070e04110a210c08040606050d11062107020a02 62
    0x444810305501038081301880303207070b210503035041e0044115135080044551181e03e4000601544120f4014940000d002c1034540e045c007030209034143d00810300300100c00c40501c001d09407035140c120781d50410032104000c9a00304802c10a41401000300503510180b02e801c200034940300b8044940114104074003000416100040d14108541080b004601404c50f8a002c0d8644105604660604604e03004407405141d44294406426120040e01503024208610311541d5920184903584040702e440c8000d000443e4000043d284545000c1c1a107414074611f10f90b55a0f6a4204a808060829403001040603c90f441408080010401d076410000d540040300000c0e010704c40c00e00140c0c03c1c8400c0e208460042c2440c800091806200b000040003c1e01c0700802c001c1c0f09540a44054500c10b040000104080c544826992140341e44141182148030003030003400840e40006007090540801607401e100030000d801c0005200e0741c0580e0181c090000d0a1041194551003c1d0145100307050b6542d111440c91401c9240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 534714730 1250 534713480 534713489
    0x90d0e0907180504020c010e0105010e010e07052808390702010e0a140a4401060f090609060b030c13030f20030102031e0717010e010e0106050a020304 66
    0x140b00c454409a2600001000350750000c1c0e0420300c0000d54900c01001944414a5040450003d000d80d90740d032454200032140c01c0c058085000c5108000c2414103004500078007000c1c076001030307405803c01e49035240041c0c48400c11060f00441e00755410414400ca03050b40140041c4848080382c00c3c103806d0f22000703204600302c80c028000a880c000070403105580c0140f81c1003200300d03c01840b00c41c010792074102c0300114401031401540150300480020420b0492003a0070345503444e0049640848a040c3d40c956103408003802035480a2469041840b4851070080c010200a4000e03030300d00055542c9172142c00e004454440c2d128040c010301e0a04148072000540c03007282e41012a03101119190000481109200d54455100038003121102458008110b0300030b030540d0344000c1d144961601f0340d0a48c1c0038142070388002ca444d4428200c0061594503108800038009400200300c3c50001041c900700341a019400400307070030070a1309070108001081407004020420380500498601507080500702940a96207010728082d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 534715980 1250 534714730 534714737
    0xf14090a0309090b1c120801150e090406090b040b07110d0e300d0905090925080114090d030e0703171603030c110316020415030f0308090d0e0907 64
    0x113402259a03955009942d0b440d0121022046030311140c50440c08450b0050706c00e801041e134100000440130b001d4401c144a5410b40d0b280c00001e204188108949030400400859a841d51003080f8000f15070074044a92081d4030807000c960070350402490191840881d40c1c00001c007540054081c480c560350010905441c10029190060040e48a06501006040c2d07039002c030811b92181048100c0c034020001e10410f0204861700d469110580b510b0910551071801c454855055002c0f058040c40040e400d0004000c480307000a07151000f41d1101001c0e03080d240d00406a10403580143d0900240b01c000740076000b80c2e81410300341040401c0c1e42c801030383c0d1184c10920000e0402d01000e8610350045c480781046034074451410400429625140c0340140041244040d0304000035070302d1030007051281e0004204e80054804030040c04500c2c6a0303600b04000b40402c2400c06041d180d134844000000344134884807401c9184a80c448240d0b0b80341c141220b912300760344100103504004a403041c0c21611f0300c5014030b05402001624 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 534717230 1250 534715980 534715991
    0x1140301050d24090c030309060201111b010605030303091b031605010c0302032a0d030b060d0b0109090903201216060b030d020f010b04051504021c0f14090a030909 72
    0x1241015030443c420300703044103080110708020045d0724210700d0290307403003034403105c489070340b50b0710100d00301c4070828003994624400304500f98038903145c85500300d1324001c1440007140c0e89889201082c00c541042d644411250b01000c640030690b0344001c400c40380d0342002e50052840c1307417102c524200304045a101d0369042c41401c82002040c10304c288207d99159031080030b0041d6424030442d0082d1442036514141e03103980108400c90001d14401c5c000c2e00c0d42080001c010754105150701102800402014584030705100114800143d00c20450044201c03981c0282c80d00c4021b603507a02c01ca0724141c03e6820034450541c00c03150b070b000181c4042e10705803840c00c150304240d0700e14904c55140c16002004824101036040c81102491050f81c2e5000528080d41c074401002801b15441610500c0244c4005560440b140c40a804e6403200c20b040a40c00303003280300c00001c0c103103a611000348610001c56800d012540300a40e02c440c402c5e15003c40e09048203400c50908001131011003066140101001c2260007200001c40d02c64 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 534718480 1250 534717230 534717263
    0x181906030b060f0301060f110d02150a0212090304050307271e1d0d0f021f06050d030509030106050a0605071b15030b12030405030717011107050c01140301050d 70
    0x1007511121008542d0140d41ca584580c40a05100344d11103440d0005000110109408e035004282c01c200007500d60000d000c1504800640f640c0d00800410712108543d00b4400c41c003600c0c01c80325140c0e014900c83d002456a41f0b00300030505080c611603406c0250420350541488450384001d5504422140400300c0011b41d41d09450810007806064030004012582441d0f400039004040400701155000490b007100d40c8a2400c54049d10000003501e0240d000d07030007441120354041d1903940b009c01d02502001000032040c0c0c48100242884003503944c140d0004802280c01021410248100d03406484100c0f80c1c08449490600014014403c1d07a10090450740c2602c11648041d0040b9284405011454041030044070603000060040600031810751050104095250061001008171029208090003901d80781303050010004070002d007800064125944c03400c20502c030004010141c003010b072140002d002010788100c00140703811900182c4100c0ca030404c0004104a98a0540c041c2c11141d105009400d5410702c3d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534719730 1250 534718480 534718489
    0xa03050d09150c1805030f0304030f0507050409080301091103101214010534051b12280206010f060c02061c0b0907031118030309040c05181906030b 65
    0x816020000050404051900f0a600080b007003c6008000c0d94821100d5920030815030380d00240300f1055000d400401c0148007240f508800c5042041c0900704594001d60b5a40200b03084420104040d203001c20040700500c0819600e00945a8030001c3c8420503007141042600300d8048009440f07500140c4440b4841c1000300b110540c2c0340314810568000800c2540342481585601c81607403200c210781011144040000c3c0078a03511220f0091030ba0b640c407242400101d61030304107205030442c14180c180c480d1040e144e036086c00003401400c1e04996044442c9880041c0d100d180c1c0801020100c517002d541010f4014010702e100c080000381240c0483c50104409031440c0041030992081a14401c1c6103000d400300003141c41180c0d004a054030100b038900203803da0320a80120101c030029a19044401c400704202c44110000f444036240c001401802e907407816081d28005412621a4550040443d1011401d50b80c1150081c980280356041961888030505000c085108080241d00494040c1a6a02c1c03807122203486 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534720980 1250 534719730 534719753
    0xf18060212070f1a070201060503010504080a0c0c0b0c0a0b0a051b0a171003030e010206040b040b060f09090c03010c050903100c0504171c0516110f0d030903140a03050d09 75
    0x100228010144400b021340000c040b44e040712240095820700c0c00001c0d003410140b285500c51038008680c1c50a001584100f101e003000d9004080d100b030b007040d4401251807085800100413803e1142e00402e51000f9030314002a9a60004140e8200289801c0c01c10102c1e030000c05007401006003001c4e2607542c41c40c0d0ba4006031040000c200b003c8055800300300030852010101c5944200f40c1e4007a80307500c122141020012070703903010101ca0003080180d8410100d400120406000394000d540281040c003030358020780119429603002c441003483d0364020300c04c40d0b120342030a02c501d460a403110710b0410b10340817003100441e070b0b40e00800101c2121513503244400102580301da8141c13005013050501440d625440705160643c3c4ea49160600104520071982c000381d05402102240d410549684c190343c44a1540d817201d6015120056400f0707004000c08140580325540c05064607103691083c0c90b03451941f421418074070351642c01c0051509581e400f04c200d010100b80c1281c2502c120100c0d4400200e440c94030b82c9404070341c450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534722230 1250 534720980 534720983
    0x2070b0a09150c0801030605011a07060f0207080f070c06020106210c0e07081509060d0308060a0302040204090213142b0506010b0909060a050f240a0f18060212070f 72
    0x34a401803082c60f8070f6004512504036401440180075590702c1c0c4080340348010340401010100502001f9410003c0c2884e040020080b40e5000c006042c0000c80d01c500102c0c0e03004c20024603d2a00c0040da030401c1000c101051400f40c8164402045480d04100e107142106c04c503404010241c012000c4094204185410014064000c8100321340d8141401e0070003521402c402d41d10718641c280d007040991403c0c01c1280505201d4100180300e145170024a4a0654402001622942c1c000e501d0b09804005a107841c0000c0001300409000180d1781d011140c090481c0312a682c0142030302c000a01c030031a000d076813091501d4040d2000e046290342204005542d03100c00d82c491a030014110300030000002880c100e4200901031703085041d1118000741c0d55803c1088203400190150f2075016140200103506400c141c0010361080d00740d100004500b59078518000a1a044400d000b00007500c00382108050980c0f10003905030f011980440d4159450401e1303006921407045204c9080c01050229210081c0316254400c0e4a286 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534723480 1250 534722230 534722273
    0x201201c060b0c0a02011b11010c15090c050114070807020609060d0905061e0405120912030706020405030114040b13030c080c0105010806090d08061203251502070b0a09 74
    0x48451060306500c13045203100503404111107034600c0c4840700c3c40700844e56200340d01001054081540300015203601070080010368020030001c1d183c1c84020558452081100d001c2da114255180c60240010055488192268100d15081c048840083d0340b54003900c01a50341192404d884810560105c2d05600541070702e015014141a00c072428098003141c0c103406034922040c00b44002050b902c44481c4940e042c1c40052455002d82d0fa45104144d640c0064080c440c4010b0003103180c004032180403465500843c005445ca02d90001c3e040041340780074410511502c450441901481c90141c441c04020080105582c0c070f111803006242040600c144038000015a118141941f00d0042c0c4009030300806090084190701d2181c1c00118542c90302c0000c090380321100320368983c1b41d95580d0000340300e182000b004800c0f0041c40244400708100340d84105a100350950f00d00e446900d24000d003070082132218040300140810303204200c50b102242e0500900c1d58001c0030110046240c500624102c4682c0300c61000c4c04600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534724730 1250 534723480 534723487
    0x160611060a1a0a0e190b030c0123040305031b06090a170f03010308070221030a110c06121902040f03020108071707030603050f03040e040b0c0408010f0c0201201c060b 73
    0x40180700702c034003800307411050900d0361712840d01d160140840b080000032542c154031000d1700071f00d5584109000c416285040700c2c9401c1070042070807a180c054010340c1003101d243d00042070b50101c035a140b860950040742c13000d000304194140721499a0b210706000030080c0070303903009030015054042280c0031540e031018213407a2155a50303580d080444140d0400d0364124404c0415100101d1a4206240512018880480a0341c54034840f002e0903108503802018280e028041d55a00070410307952000900842c0c08040b000c04014586071406840006116100764550351060000740002020000c250090f2035080c24081031517101d0b000240c1d58000e841c008200480600f070108000d40740d05402040449100f81e0855000c41380709070300980c480c00345000c0c060212052000103400320f030001210700c1c0c10040302a645450580c0324003410742590522940c052003552034080a1401c241e091244440c1d1a00e5600b651031200b2004452031400d10a1460320206114603030100d45480c440c50b40040020702c40b210001340da = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534725980 1250 534724730 534724739
    0x8060d03091e090b0f0f06070c09090602090a061403010b0c1e031c05010b09090c070602030703150504051611030903060109150e09030403020108130b09160611060a1a0a 74
    0x60b01c01c16802400c90043c1040042c81c800c2c03c0c0300c4030f1070048040080100454800501c140140c1e60807008068030715240c0000700055403003452148540d40c2c0e01a0780003603030ba000041e0902c1040d01c21580110b0400541c00c5003030040300c180e0021b60341540e6040c0307031181e51a00203101031450302d0780002e640981d110140c011442819400001018040716110424075064221044001140c4007480350035003100c2c003004018190f06c1c0c924111035006800111443c203100301034440c002203070403c0703500601099441440411203d00d440e01d5100414044906100d01d01d0100c454842c0d01540305400e2080c4904890030220b0a031090003a280482c0c0c1c05000c503400e075a940d50054005e054808944860f20700c0705000403441aa800e041a842191540020740c0340c9880d40e4011a14140d00402c4552209050101c41001880354045076011b007103c3c100078106980c4452441181c04481d60090302400340700412000700f208041442c0350b00031964240091aa4a0030341400d00e1000804290f03a4000505400400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534727230 1250 534725980 534726029
    0x81803030711010b04150e040201020a1b06080114010f11031903061a041d0c041a031e070f111c0f020c03010207080301030204180206041512050708060d0309 69
    0x2000b004219000780300780720704034003440304440c281c01400f000d0b2a10010f0a00c00c140700c0c40010350b040383c07040c8100c0d010908a0744078a10070441d00d0740740c151240002c590402006030321285d06409081e00030680c0502480d1580042c1a4114615070001403007010100c4000313443d400c0c815644554100038203100c42181c4c0c0007009005249070300071400d400d065200407404c41018070055805643d841444841e01618aa4081a00820041c42c88025500c100804540c0b0a5440c040c04110f0500c030b4411a103900345809810746c5031000e0700064081e5501c100820100b150b022000d044580c845060426102000c52030083c02e08005601e060b002c058501c10b410042035011010004008040e42600d030300c54412802c040c00d070302c40e414024050010500062001d40740560008200149000c101c11888044d5404038400e1741003503010b840c035a1100405003a030250059800c00460b02d42080420980c50851400342415601030906401121025018410180281403100140c000700028032151440e0389040c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534728480 1250 534727230 534727247
    0x20c0307050601080706170a0915051905090705040c020307060501030f021906080711030c070e01140901030f060c05040306050c0d06171b220b090c0c0303070818030307 74
    0x315070621814000041c2920017140200980300c00c1d9441004100700303501d03040c2082c44007030214010036035039030715140000b0307110f8511040141d9a0000031611f03190440c115182082045550304080e4185400c100f00f880303010a00074142c4808590006002c451410b0413480d40c050248010b0027a8503000010083c0b00300e00c0000c0b80b120740708540c2d08032451007035190056072121174801c08020030382080114503145d00811000710048034030021281480c00940c2202e1034026079030301050b0501c080300c00500c148800e900d2030401e0010150f8208209524581d500d1010040c0000b0150180343e482040a07078042c0300b182114011900000c0030b200c1800d000e45c0d41401307a801100501079452909100140d0713030b00e00012085102604002411500c21081e40c032486154400b40e420342e0003025101212102c11a201031381c012620301c4140051803003420018003c050402418030040942c050080000e040c80c000700322030b03015907149040c0703140361200f000d45405540500d5000000e80404801c2044035a80401e85 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534729730 1250 534728480 534728483
    0x150905060a050d031707120f0506010e010c08250807050c03012a11011d010515090108070303050d090c0810050f160815031c0f020c0105030f04020102070504020c0307 73
    0x8405502e0340c501c03c00c901140c07865002404180d0004136403c10506103203c1c00d501c601141800701902a2255a0328115510100e0102c40d0641d607405100c103d503400704121030700c04001c1c28003071f1014840352a104942c3c0104001c20003150541140c90110702000c0044206460344204a00d0f11280c441c40c1c01780d16402d00c8142c090096280c100c4003c590f042080042541e034048070905507900c04d00c010101c41000784801580402c1d92104003004043c04010741840b15410a070000050305d00704041082a80c40c0911541482503013040300510413107a01003401006c0701d0b07040c00d02070b0307465981c06003000c040c01000034080e144d540c0b070050001c2c03d04c3c008110500071785c0c0101d03010803581e0b50300c81200002c0c1074161814a490740c1c0c0700c203803078054500070b00d8400d030484402c502101802d5100e10000e885c26038024958030310031a44151400d6504c1e004400b00c40c806145d80040c110890345000024031034040181040da40c40000c90100c3c007964000d100020141801610640d500c2c01c04c8201556a607011810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534730980 1250 534729730 534729739
    0x31425090b090103120309030e190f09053108071a09010504030e0d08160f05071401050904020a0e04050103030503090d05090315090f0303010e07081612020c0115090506 74
    0x74209103450210211416a503108000d9428140345160850050003510300440c00e1003481c21305c1040d5075440f58555104913006000b41030790181040602c10182004d070b4800400e8034185003c0c868044c44509600784070460780006007002c50341c10390f403001010014400181c441b80340041c2140a100c40c1c031074a82001108002c9000d8107880c1e00758042c1c200e40040754043c00092010904144602d0031030502889103000301c803c2400c0c17180403d140f210316018401d08580c9405c0e5031100d102000410700640e8024001003041030ba84002510000c2c2580c0f0034800b6040c8915400501030188074041c2440311175124000d4801c01c01507843e450090b240b64404d5030144180e10644000400b1039100d102161001d031809009404108281d012030b4400301c1c80039000a01c1406403003e5030901010400185000b0100000d210304181017200c40544900000740c030031031311920a0554001e103107803c00d07100c0d00103000032000181c0d0341d905e25207098014078070343c0344030b2840c00c46103c070000d1412401e80090f4000c400c1242d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534732230 1250 534730980 534730991
    0xe0102030f210114010c0b0601210504021804050c0603100315092127030206030f0411040605060702090405010e030706151e03060f0219021605010f0903142509 70
    0x400e13100c3d052104940c240080d03070610035000056452503000d40c00c00018100720442146a142c2003030115442c00b00c41e07011540d5801048194a4804460740602c061003202130954201602c0311a00c40c3c4480f04020f00900c1c0c000040350050004105410040d41c01004140030a98020381d034001406201034255210140c8150081d03451154003001016619240c40d1159100c074421643c8440021500241c0003d401c00000080036803a05802144110105480d44200346010f20300f1002c01340c00c40a1303081c0218030b040c4081c8095140e5200302c4501035012180c008190781c0b240b030a0340c003501800d021400c05010102e003c00c00c10105400045000380b800c0c0500d442c10342c0761910011114034203140501d85900e980c0081010603519031001510791390240025241071620510f201d034120403503c440c801a405009441181e14440d1080320141c402482d003035904010f114402845000c1c03500020b000c28044811064200804001c80e1003503102d1004002c110800400100302c000c0498860f2203807450412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534733480 1250 534732230 534732239
    0x6060906040606120906060816061b08090108090f010e15160f050c0c06040e0603010e010915020a0c0b0106020304080d0c1505090109060509162102010e0102030f2101 73
    0xb40282ca0aa401c00d940d5003540700d2040b04404040c00c81032501b0b8960681d18030001c24148000e1180c480aa0f4100da06010241d140c144018181c641c9001031140c581f1014100c0c000156820003180c80c110803d107481c820a40382c4103c0c80342003865403600d01089610303011117008024008900040c406480c4504482213998013108648582110035861000807410844844814082d0000e40443d928410889402c0440c0b003001c00e406520a410102c5040e4240c410405c50780750034003d10070007007011070003131140c94010794502001c9006c0c00004007005401082c80803109201c1e0300003000340ea80081c0c0e06011540d4540029440e82c5c02405108581d00a01d80c0c01c1d0b90b198044d0b160003040a511a4000c2c40e0220038139296002440090031111165480300041c501081c100c2c010b050280d096403019101c1c8181419484452304043c0d806000144120042030241d0b41a04622100554080c00c1441500007078a00403070451107005c0c8041140c0d140418010400056841c80800503a8802c01d2030381f599884 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534734730 1250 534733480 534733489
    0x30e030306100f1e0801030c050616030521190c0f08070507060b0d0615060c020a0e04020303071703010e060d15110904060303030b04061d010e0402011e0206060906 72
    0x200d854940004040492078142c41c8074142e4000c152020b03103040c111000c40440003440030aa640348080000d140300c8018018401421040c0c0300a103011211503190900306440800034441515000e400c1c480085220001d08803e0300800042e10081509001c1918003807507405031420318070640c20740c0b16280901c10118140955035455135800951142008c503036510358212050740c002c40c0211141900c0b061070402c1c41d00d5030704101c2d41f020b220b40d002082415071001901611442a40300f64100940b1002000141c0c07600c1d040d250030b60303032085981e0b05169a103002092961080040040c5040010b0744800c4003680c0c0b140140d41a00e0342c08000505076200c8408000f45c0720364a10010300794112100701683c40002d50b07400540180f00010009081c8072424002400b100c0083e0300070390209442d001c503a022440c01e88281800b400c1040a458501c01d80006000078496050040c2440581143c0100e0150b80c000e2041d840c200303d8249004500d0001d400c0020340720b44040c0c4020b03000b8403030180841c51a140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534735980 1250 534734730 534734737
    0x60901030515040f0c030302210901050405130b060f03041101020c06090f0d0206030a02041809030906080c130f050306150303160305040504020708040f060207050a05041e0501090606030e03 83
    0x100a40145941c8411802d84801a5400381c022125080d200d41140c0c006010700708107100031806a005054400210709580f4140c8001059991354554100070200302c076a0040242e03026580c0650707040f0030107050103102c0d00092040e1401e06502280200b5106091361102e0000d62050703100d035000030707c6202d03a01c0059030784000355031030340b6804001441000b0319070070b02075108184010001c00c1d00207a0b40e680c4c1c011441903401900e090400700d0300050240040c940e62281403000c240960002c04c0a00f0568400409502050040c48100984a00401c010031401425900c9842c5100c20352405103a64402c828802d000a1143d00e01034046c10001822005c402c118140c07036404080e02440c64107c50444070036901135048011800d0041c00c2c00701080c0c40d2201d2003c0c1c2000c1c0d01ca01c84d041e41e19030a02d5100004021164406e204540c0a1a01404640c50f1101900100c44c029903001c100c40a019400e8200f488102207100401e520f000e00003d0070440b950401d0341220003540307040080342e40460100d91030f4403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534737230 1250 534735980 534735983
    0x9080a0b01180b040e10060807051309081c06181503060b0d060e03120906041a13080703020a0314070c030b0601050c0f07080c01030911040b03010e0d1706090103 71
    0x80d150030040108031808016900391801000740010104850b0001600b12180c4440b106104d51103207540320944076007840780c803000e1f02c05c0400800380d2525000010307465418408640e0041501d521506042006220948505150700800c00344401704031201800184150304c900781000b030b04000e21409000f00b6200d103207115000c0c1c810820095045484070409000e84000c0a07403c28841e66084022440e00e2040b083d02c2040e400c0a036070340b0386043c0401a0700140143c0074504940004d02400300140e01ca00c95032112642c2e451400d0802e80d80c00442c04003030140c2420203480400300103500c1040660100b21401032501c26102c80118408081036074416018001000f020355550040a00120b0703480d5440940c4604140760091a240e0518071844c180b402441c280c402990040c0070034480004240b206210301c84085c0303400c0001c0c4045844103200131030034600d51030245a566003289643c1d102074100048010030b000840d201507440c2440207140d00c9a6840340011420004085a854580062868101c0c2d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534738480 1250 534737230 534737243
    0x1e0a120e0a020d080d020a170a0c0f0804170d150806060d02060906040f080f070b0f03132f03010f090f0321060605071b051c020a0807120309080a 64
    0x240d909002c0910f2440f40207560060040c084000c500002d40001c0010f00031039640c01c1c106000ca502c46100c0b0543c090618000f2908148140d40c030382d94071402c0000c8040941c948400d0341e03281c90038034290503140349182d100401000641c40351011160781008441c03421281002c1d4103a60b40d808180e031500801d8641d20307841070b520b5403400c01618000380134280d441002401030345802c2d928002c0c07000e6409036521019854000b817520000c103131414400328004010754a0082d180c52885c100008062100070440d00e9542442e041080500a07056520041c44c142c0d07000b400501c846151036a038103070b0460001c6078401d60800110040042a81c0079202015a1000880b0140032960ba42502c400c80c0f1201e283c4000c078580c0790104e4162081e03014017002000240c480c9551044642003500303e8020400c5884200b01540b4810019601c404c81d03420122030800a0703114003810107200061a484565004071001c0c85201c90100c0c40c00048140068068401e4961000441d90b40803c2921030aa0200113800c0c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534739730 1250 534738480 534738493
    0xa020d181406061f14310e180a0209040602090307240f0c0f03080402090601030e06010308030a0b041416080f0c07030e0301182006031602031e0a120e 66
    0x410704125940500c600c2a030521a402c0c0f180346028140d943c11010030b400124080168824041e00e486c100303200ba54150f280550001c42c101207000201c450007034038000d10304140d60b83c240111401440141c24507580100443c64a0500d800d141e406904131194180c406e01030403c001600307010b22031401d0310b0040584c100380c071104500401034801096540802081c08130285221000600700720303481c0140b0340300303443c1c203140c500b02030044c41184080108000d06051a240b0a04c03106803000070010b0440394003e03011590b0340c0d516a1120043c0140d00c4007981c000742004005c0310124102c1c0e17095803150520000d400c450341c1000c24110303008c2074140e520301c841050302070106154480c1c82c1e00034140a80a81440e6210b02c3c0c032200440d08540c6100501030100002c810b41c070080085c3c1d140c1c00022280740700018080e090307150b03001800074400030f00781d000084040000956060700a0007609c0c2c01815506145c10f07903410300c02c04001146d00070105140051160108a078205615201b010303200e80c19071009081 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534740980 1250 534739730 534739759
    0x71a1302011e030617010504030306050d050c040e010b060c031206030109120810050604080c0405010603060f0605211008060609040c0308210a0605032b05030a020d18140606 76
    0x201402c040300b102c0c04058a5080205910f03640c000340d800b4046011000207080e18190400030300b11002034022030300c60011803803144080b400005141c04492822540000c000380c0300070b0010f0041c034140d0036180e0813403004211a01c0000c0040060201c0004440500f0390303d95440040508a03075042c44002c040100c41504e41d00d40a12500c3d850703a2051040c1e000040050300c4000040083d00164020003680c1e10204158160b030415018840c01000c060500384211420248a10400030507801014204040490090b082c0441d0740d00c41004418041114242410801801070800d1850300034010303188143c2c80403c4143c2806403446120f1500074030401c070300d181551b695a035158424803a040c40d01c02c1460407403032030000e00b4041c00d000c0c032071509000800610b0601410305110201200c44560144001164144180c0f0020003207514010324002c1d99070b554a40c2100c0090241c02c01c2804000e1510484842000c10114451801801904001c0f488c0c0904607200e036a4001c111420364104102108589 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534742230 1250 534740980 534741017
    0xf171905060928021608041d070203030a020d060f080a05071d0604050a0209040c1107090204030b070e0a0b130611011e020c010b0d0c031406160c06020708071a130201 73
    0x161003641c0800145c40c10b003820b03a0f003c5ca58214403e0650b25080b00203010810705071150503110310070218102c0d8450038039040f8400b94407400001c04031051a500000c0d125200c182e140e0000000c0c00040e81101300c01500c0c0c52049a86181d01072003102c90b440b6014001c1120090522000e4083c1d050003078043c0e190341c44000f4400500405890042503640038042c060159a540c040c80c00800f80e15038860b4090325030700040900e0240c40c0e60206420074810002440466109481540d0003100ea06140e980810140f0104404051720361101c4205840422080703117020004422804803070b91540d401c2c0420031001e03017040c00c981c10420a640c1c2c20010500c919082442034026181c021041d07000055007000960100b41c411140b564202c5000d901c200003402042010000110b1240c40000180098a8140048007148203201000000d20000c40c82000800c4400c1e011284815030000a154440c0c00301d00c0c081e04440c0910b2401d07900805900e00040e00140c90b09443c2041540507512500203501c490102c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534743480 1250 534742230 534742291
    0x905031209060d140f160c0206032d0717011406030f040305040f03082a0d050d09081b0c040c1b14010c02030c1006060f0f1719050609 59
    0x605443e41c4980d0002c1000903c014010711aa404007a442c3e00343c41d080c502c015a4a03610a951010701902c040e0324009601e07400252030303008050722500003000078800802000006800601c005103030301031003000300141e4031012101d0640342640700640b8503601c1c0c07010070441c0c8031562601500301c5000e10001d1240c4202e81300180e0080d00034108580b4040d102c40c2d8485441d21a80c2054a0b00c00d000110742405018008455076010040c0c0d00e054004003011020584a01c0e42200303001c200500400c3e100c0030f1000d540e01c8000c5840d80f14440c995121502c00c0b10b8002e0001400581b012405506106115070a207030080040d07021040d6200310002a10450660312401c00031010307510104481041d0b20203080901c03458030b2105440c1c00643e01d440c00540061b10b44184c08014031400c5050a00410102e070304240302c02d401518500b04511444200304e4122044610b01e60402c00141800701802010307102c5400751038030006201401d0080340e039140d00f030104201080c2e0f2140d41906a06920300c0d40101c010014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534744730 1250 534743480 534743497
    0x160e01030905010c0c020102190f0807031701060905010f021c230a030b120106050109050f03010e16090c020f030403020103090804090c120b0d0f0b100f1203090503120906 75
    0x6010401601c0302d40c2128104690383d0301040349507415000350340e01000780f05020b1880407007030f2107a20f003940c1c0c80c1c240c89000f074500100000008036a003410140038070200298024098444c101c01e60307440c58010103d03030091180a012a0340071595546061020070250f0365005650b810312088090001c0c21940401c0c0b040c00c141c4540d560131044050700c104507008200b0541c0990340400e4030040e600c20010880010500500c05a160540412403030760465a600304540d4200c840c0e103c8003844170301007405440400350700e90b00ca001c1c10240580f07800000040b8000e40e01604800c01c101c0025540a9a6880507580017000d50f5205000070001503100760804111207100b41038144c1016550305000003070b00c1103210f00e5808118100200b1f0312100380c41c410b901e02d10400325039440031840c090b20345d00c103040e01200c00581484540000140350721510b0690320002d00480c951000c0e4180d031500704d00b207080c043e0f040841c0001c2c4607180003e014940014201d10740410102c2543c508100d120030040030354040c041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534745980 1250 534744730 534744737
    0x1201051005070503040e010e0108070e190204050405160e010e010c02330a0210050103020607030c05010e0a0f020a09090c17010f020a050901080a2309011d0703060b010503160e01 78
    0x1d00b60002d4030600c003500080c602c140314400d040d4100900c4500301c50051700400080c0d031241000300f0200b081d104600e500020300c41003042050845000c00c1000e4412900070680080c240014029120500b02404040c00190340d1407424070500000111021100880041e0001e030106209401510b42480008189401c2c1a103c11801e03168048000861340c580d1980001e9440c0866004102a0148604a1806014042085258190390008a1501508601404010b81d60b003405007004000d60118001c04150700c02c0314001700340ea1400700180f505064089020768501040050f114400b4001c1106069014000c1d2b2481800c2a40680c40380c01004001c00b065034803003110310640941ca1000341030b0800c841d41c0325a0303200a140300240c9411405085001054039014605800c42800320b248000300e88040e00080d001e449510041d070140ca1007550348050340c1100704201081880000e600004c0300e104d10028008114180010354280c01708484c0c0f9504c07610301868041072248903903480d8461810506 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534747230 1250 534745980 534745987
    0x40b0c01090f030c0b06012c010c050304091a0a0e0103080c07050901030809030d08010608070311040b040e060a0e09060c071a190b0301050405031e04030b0a06030303060801021201051005 82
    0x4541a51200020b0390075404160000648400e010035283c1a40d8001c3c001e081170714040715607600c03004100c1d50000d6201021101031408100c13581c4a14042000d0303541000c11603840d0f64440407003000610003a0100101d110100100e01c1c0c85060030340d0030904541888260042aa02c1d54035038030119400b12001100c41e0103032200218036aa82c4044c11400381d8020507499840e090b07014107251420048580c40d13004c0c40604401008215400110940e00c1402407030080341c482002d0090000341d000b070390007000c400d80e00031501148420058212070b01c1048116038440300786581e50040e1840b904166119509a0040400502d6460810300200351591080c018044c001507030741030608500006450700b48814a07852425041407500313002c0c810180600302c0c02000305003003966444d5a24403442540700c0025403d03031076041c4051240c40c10b403401035400040d01117492900c1103011006002601003100400c0c600f100100340d40340148240c0d03509801c0c035699514103034245030800101d803005420840800c102007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534748480 1250 534747230 534747233
    0x403030207170c0d03051f0312050708030a0b1c0f0615080f0c0306181c020309060301060201021e030c030a0504020a05040f060302180907090c0e040c020a0b1b040b0c0109 75
    0x104001e00040903c034014110031000740000070103a80c0c001d0089000100500d01020070b2003120a41c00c4101d035403100600b8203043c0e00b81030a6420b030054080141240401004000241000d41c00170005003c3c126002068088004040701c020802d0705000b600300050300360707607900207203041c1c0c401c1d064038243c50b40b2000c4003541c802c0d1083ca4106041c030250001d801001020403035080400200f904015080201c180c2c0c006100b0460399680b890001020014005001c244643e600a1089411070b000282c040b81d0350b582c490002034042d600829080128506920081c0750401610701620b02031260201000d19503200c0c205004050130b00544180c1e1b1201c01144002680d80e038034801d41001000324100401c4452441c0104400e0070003480315203240094540401107004000310b1018181ca10074480002ca00344c1007a0211085001c080c6400e800c2444e01e41c0c032300c00582d000656104558868a010a0555200300c1c04000300c0204011101c20300300c0c103000611442c0410b1002d02040c4a43c0400011400d240d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534749730 1250 534748480 534748523
    0x16060903050a110714150403120c0c1a0706020913230c0a02060613110a030504110f03030924031501090b0702090f15032b03060e0403030207 62
    0x10804110049040000d804195641044490b240c0d030707694001618916151080000051442407407003486402e86004440800000105a0f401b07550004902880700d0108100580080000760f001e440090050000103091700d9500c02c131886064031804000d00705442c590f10500a900000a103a906c41d00030b694a034032440381407181c4158500c5040c10608503800c40404c5010520000d044201e0062003007000c00605074000400503013040d42070380c0a20400505d040b5002c000d001d80d001c1c400c0c5521000444900d6681e15400c540c0c05540a083e9210790070020808010480c1c0c58410541e401d80c00a20401d08035103059121441c20041340d1000b1031214006401c2542c441c6c0c8115008103201080b500129440e50348056900083e100305000306240508640011340000c00090158503081d01502c0060542c07034480d00803041004001d8110317109803000864030020300d80c80340740c0c41d252040b1a194035100540300f03000c1c1608680d12403e9501c090344032038130f0440c06940200c90544c1c01056554580400c0d044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534750980 1250 534749730 534749741
    0x90e370b0702031923030f06062203030509120a15020a020709110c060105030604030504090b01050903010203070c050d051c0f110705030309010f0605030d0807020f01090f15201606 79
    0x4c80da03640d400005e04500e0101e800c84100c0484601084040c020844010b01008a0075000325040305e000e0303201d80d01445581500e00701038001c8122452034400000400d9004805000e0901c012210305000c1102e20409944e01d044880b0080d0040e859400034108800f415802071155054600c1941d10045e240c15502065076102c003000061080c0001e2400d17070540051140601400044019001505054030300418a00550086a03107140e034400018035a40c2c014821143c0040c0050000e540340d28202101030000d58030380200740c4031401740380c0c1c2220140f03108208840b41000d8001c0c910f283c0e08801284140100959100740c07003200e40c2c400d00301c88240c40c0500a0000e05120301c00440e036914184101d98203440101d1201785903039040c5601805265800706407405030740e0103031501080e95551904120300d0a0840d0043c0c21481d442e00c080710051016551b03038121494050f005402001c0c2c901e5005600321170862034201041004030300e00e00f81180c6020b00400d000701c0781c0d09004d00c0020346138039010110350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534752230 1250 534750980 534751027
    0xd0c091104030c0b040b0a0e0d0c09200c1207020f18010f06090302010905010309150f022107080609090a021801081b01050a0f09090e370b070203 64
    0x40301080030000c0102c201008800392a0040482d400c09190440107051405001031040130b0000c0d81e0317420905602c428000c03044868025407501c0e4401c0d034440b0380600824007904d907544d424107040e005101611032001100e440e0420107000389110780b19040c0b554029041804200e0b4052007000c04c00a05644481c0c00d2040c54003012268809545400c4180c3c260b401d483d40910180911a40e0800260780c004121000b01c400030b080128150806103800300c1500c65040c419007a041c81e10490200381211a8081e01e800007404400080404001d144c85104820450398400014900d1000608030b00300001c405401c0310081c03048501c92455a40006d00700d1103000401c070400004400100084107040110985e20541103442d10145110400000c1c00d41c03064a07a29010f0010006006e5101845001c02c0c100a0005000410891032850025074546003080c40d001240c0b076803034917044490012000504030303e890902d0302000d900010b554654410317500074844001c0d030005100c4d1103021407100c40208c00d42c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534753480 1250 534752230 534752261
    0x10e060d1b110d0c0b040822030804050307060201050f0a180f080703031a15131a0403020a0f0e0a0b040207050609010615090b030a09081e0909180c0d0c09 68
    0x900044100b034a0011003420400400100350000030105400e81507040e0440e42052041d41d80f0080600360a0485c104048000601e0440358000800c1c491075102400a8642c110103503001c2e5a40c0d044101d09903401a42c81c0d600c2e941e20b0401203140440c85030b100340f41c00001c80100415218094a41d40d004003a080c80a41d10302c1000030f0030030100755140c8242c840f44c045a100710b8244002c1040440c6071186101c502d080001c10005a6022480c0355042280040521800e0b103400000d03e140e0f0000c03550414401240a1820b80304080340c0e0100c40306505050318641071003100301341e407100d8011014111808031281c01690070070050000c070f402448454810f0760b00d100003207441498181001502c4000509100420084000a00207110f00b00100d030381040030401c02140618450400740d00d607200b6011800d106806541c50021030b04000d50280040395021925003200303036030f442c5070100e440790510000001d07500703c0301e00c40c51070b441c0051310b0f44e001c14085d40c1c1d0180c0c2e4503115480801160018400d0b032108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534754730 1250 534753480 534753497
    0x1003090503270103020f03070f11071206110406050f090f0402070615050f100315330e0604030b04060e1209090c07020a0506031e190c020606010e060d1b 67
    0xd114109440c29030701c00013882c0840c074100d4000c5404d045400b024090300c0800c440110641c43d028482c1d045106a0043e20041d20031075076a030000c1100244c80d00d042100c0d004e0030410724503003c020300230948048035029220b1307516200300c0c3e0392071242ca50701505860b80d03c030400c4070101c0c00c240c4403840079180242c03240380c00281803c2d00304402074198a0341d03885031b441030002c01074841d60b549a441102d00900203608002c00c0d070342e44440160f00d0160b944e4000c4000e690040400220095501c29409407100e59503102e0240e6000742c800445034500e050701800d410450400c002c100150705030390310650241c0600400a000d54a400303010f0308005104e5405d02040e40c1c00b007880c4a2a10341500f02d10b0f088001e0420341440e0029640c0860040c082c9440f88500c9410080300055040380e080c0b50100070300c5c0d00307840e1072031840c41c00c5080c02a241d4201011070103810f290042a030000341c00020001d0040d41d0584805458024040c20004250700035a22003402a884284c0342004c0440c416102401144640360440c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534755980 1250 534754730 534754777
    0x9032603041a09060105130e010b06030709060816020a080f1b0615013f0504060501150305040c0b1c02070812090a0c090903030b10081014010e1003090503 68
    0xe0400281c07000320a1340000c0c00412031070342c8032001c500740c69454000104078822104190303401002e0704400250400c030300104100c5a1a405403400b01900d10300d13190450a91114107c2500e081c508604032400359000048450104002c40c01520004002d0a07060b49409902c0c152120140303006080d03219540d001009220344141811203010344031000f860080b019110401c07402e807503a200031510055849180741d100c1d0361418504105504003480007018413241c200303850104005c142c01d204050304481c42d0650348a1031403103402501d0086401c5481c00a006051129070003441c2d120001d51003803184140800f100119490015281d128000c40e88c068031170040445640c0c412a00074100d02c8240c101b01561400280701c06440001d56a01c407500280000071460300790001c0c0224411540e02020000000180c1079100010500c500040c006110030190307111006800c501410030010702092027601c5c803006e14181480110500702c3e1914000c6070b01c540c03580320f8600b1903104441b40079000e22840079564 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534757230 1250 534755980 534756023
    0x12030c02120c030729091005280525050c010c110601090906060e010b030601110c0f010804330c02070e010b0c0a060509030c0105090105070903260304 66
    0x111078a00e0240064a02080c1c094010703203078424840c000f0405424150b451020b802801c09204200c1520b22941c41c0900b4194501642c808284100840150419002942c0364594032108542030154000201c486050b842081c3c3c003401c00204031071809030403d81c0300441100b031207210b40710614254689580d203004205071ba070b0a40300910508020700540903144001e0300c000041c0581180c1110070001440c1e0490f00c2d00c41d010307010690080d80b02800f1000003281c88a101070044d806990242c03103030350042d002c3c014501d890705061403a441e8003589130a2100440c2d40030b030060310380c0140700d18800c16000080740c4561f6007000400155426280840b60808003140a6119121303043c440d034002441c000c0d103481a00d4000c0307841401a180050b1010995040d0480200404016035038410303018013442c9090070a03030381d403a0080c0c00b41c003c1a6007440c0200d800f084040c4a418011012680d4491003a070454942400e80303c4010b98805550b01d540c98520741c003020400146000310320440c03111900240100028 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534758480 1250 534757230 534757243
    0x617150d11122a0d0c1a0c0a06050a0c0c050309010507020105120106030608150c2506050c0307200607081003053a0c0201121103010f0510110a030c0f12030c02 70
    0x124000c03441e90804c0c0001c50840c0458a0845860140c64000310040790300d408864083c1c0510a0101d11440d8440c00c03c10080d41c100074854100150104a4030000d5481210400c600f80c1003e0320b96082001504100d52080c0014480760f401810402e2800036000000c101c402e009910802c0041d03035038001808400b005004d0340001d0303103101c00000e1040c20840400c140320712a2600b400c480b4030040c004207c001c3c100b201040e28035038001c2c90030040c924012032072007a203034000c4513103c00062a40030800a414808400342d5009483c0100411150795405c0060301e81c014040c00300e5154400c280300000c0002d0b410440b082d008218101303954007200704072181c80e00b81031210f00401250341020010144c0309502080c04500742d902440d1050300d0410048110001300302d003002c000e049a200000103d100c1c0300045403482143c8045c0c0b1443c4115210100485090076190403211081d0815004030740071a00c00c10b9641007050168101a000c20714550340c0710a445089102c0e0b502182c4c444665600258052001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534759730 1250 534758480 534758563
    0x1107080d091707080a0e010e060a031b11030711040912090302030c0a120f060e0f0c030706020f07090b03010b062a0f07030318050a0617150d1112 64
    0xe0400103e60380b008564080c51003948104981007081c1d0361540e114615503a100c4501500499a60030001e03001405446510810a5084003400200c203007140324115100440325143d01850512580e1341c0c0c5d45403600b100011035644151150354070300c08500c6032a070001420100d601e452000d14a548103044c00e081c68001c03041d12a0080a004114042c4981429800580d119401c4984040700e8a018001000000d50300340341417282e0340014401c02d80000e641400700008800712085e84d65038010417031f542c80c40001504003d07000000e0400000b038054111200d010401400030034104ca810f004106507420040000001501c02c080051050b000303001d4244031013800030080c0642c1c099511106648003d03d01c0001c0070030407060b69401820310702105483c05814001c1840c4000e5581d8500200181902c0ea01d844107505c1c02400710303034505100049411582e4000d01054440340c1641c444040c000050030b19203070003c80039400608401d10600c603241942082c0c0c009030003e0f101c9100c0002c0e1140b1101c24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534760980 1250 534759730 534759773
    0x70501020c160b120f182401120804050111010902060313030e240919080a0c171c02010b0a0b0d0c030204080a11211e0d121107080d09 59
    0x181003885a148010170b0340700c05421482c0c0c1e1642c861841901e07081c8650600c03c51076000780e110040d001c10020201012000c0b01c1c091810403640c1380e03d280403014002000c02000003800b04403c0220394058118110390411600002501301f0031500499403070303070044a140c0c1119003140403a20030140c0120131200005010b4800f141407001c5500c50392105544c3c43e41c2890850380100d520000c035500d1490700308a01803401880d44900c0c1d0340d900c500c0d903580003050f8100d9511140e51404940104604c210b20000100b4900400c0090b01c0407814200c078190f189804002c5540390383c40517049440b05e071011b0380146040a02d0303cbd42c6c3d03941ca0210070120f43c032079280742d401c041c01003000700424440024049200c0703802803081410b0240544c00039420700101d43e5a840b818034a4021074116070360209801080c071200b0280e4011418403c0c107401e0702c0e019600420004217210310048085904190300c070f4802e40c00380014940c82e141264507515615003107800f000c84a240c80da078240d81003203010302c41442143c07011f14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534762230 1250 534760980 534760987
    0x6090507050901210e03040308040518131104020c031314010c08030c0f0c070311040c030b0105031306021c090c0609030201170a1d0109020a06020c010f14070501020c160b 75
    0x10000303041c0c001e11314602c030282d40d904590703045214003603014016400b964130459666179604e10701003600d4ac1040c4a070310321802c880100ca000840760300b0a147d205040c408548e2000380c160303070b6440c00715039113000308107400542c00d10120451003001c2000302840d032900d4640c03554403490100a1040c060090201604004a000803480065046400d4030703041120b5200c02920340c3c0d00b900000103030380104c100c2d600c80c603c65a03d00000b0720803d20410380b0038880903138041c881964405800d0b0280c0e102c01d421030780082e06c00c0001881e94040010320442952140c10054a800c000c08136050502d1611010503607890755407440142040170203c030010041030f1a05018040a1454001030319420709544070344504420300001035240040755000c84c0040300301a004503100c0800c6e40101c1c1c0245a4400200d00601c2c404001203540ca0000641d5400100c0c1603450300718054507203d04954100d2041c000d11981c40080c41135170300090080c005400d03018500e00040002480c0882c1c2d4021181150340280840e29040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534763480 1250 534762230 534762247
    0x60311090f0f190612050103020a120515070905090f060d140f0a031106090718020d2a020709090305040311220b01090b0c0709090c08030309010609050705 68
    0x5006458065008940840980c0710000220342c04240e0300c1c2450354001401010b400d002000c0c04003403810780340b00c0c1e6a2007190700d41d1100e00504039007083c0006940001c61034004c02c07810380100c0104a21b14030400654124503c6d1225040002c442610050007140201c001800039040204020b64050712880280905091400c0455601503000101410b4a8948150100d83c00d108028005020343c01e0000c480401005d810018002200200124101c0c000c0c50701207010064000713050002c1d41c8071200740349118182000c0000081d80442d450030007849d101d07010702e402a8580e402e4a488441207101519001480080003400c0440940290315914548003124001c20750110603a0160b903405410022040d00000010300d5464200143c520740c000c00c00580c0031008402d030000d2381742040a0b203955000360b4a40e5100c0100b8026003042d0f8940382d122180400c1030140304e40000c000e446c000c160315124640c90703424260855100302d86241031030f9102d1108200119261103400d611045c285412414407030340c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534764730 1250 534763480 534763511
    0x117010f0501141c2319020d140103080a03150303090b070c051e0418150209010507211b030203030a0e10020715060e060d080309101a0a0603 62
    0xd402500d04000a501050205454150448103081d044028901a0641c055840b0b00508040d000d00f6110044800800d4109204065890b00940302942414510b040d819071206c0250007059002d10150307201c5a034a072081c00c0501c00e0f140030358000c0003855590201070202030195034040301d980e03128a010400c10000f00342d101070060142c1d001c40f64515985c104605040c1a0107203240c114503401168840f030030403141404034450780c0d40982038038140402c2c42c8030030382c5040d178203540800a0544555681044551084c507401080d4100c0305040850400c001619261040080d060101c2d1450240d0500b12807102d801100c5254800160b4512400030341e41d03550025124000a0090040503440e40300d500500042480710b14520007424070210749070761079400d004131111100008180c0003032400f071001c0f030000d1415001601ca480003408050100a4956541606500040201800b0701403200001b0403100c82d030088241078141c64284228943d41c103000c0024030146036010702c05151501c280b100b4450034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534765980 1250 534764730 534764759
    0x8190602030a200705011505010e060c010e1905010609061d0604060503100c080a090804170a0b13120e0307050103180b040606180903051c0207050609060105011701 72
    0x1404180540c60361909015240901804900425070441001d80d5200000c0c0743d9020301820b0380181c00034070643e0301140100745850b02600071240000d0100c0c50600481c10424001c111241c0e150000281c403581054074103081056403100700e59102540110602409024001c00010f412884c40401400d4034210035181c448006201010407644410001002a0b070b0b5644440c00a020103030581c1c0071000d08070690b200a125031114035021a682802149445c1c0c42403051940096028010610781410906030b840070082201e5004210700c1480c3d6213200082100c810107002e18166090f8010040c00781c6800d50b0a100013504200401c0342d05042d29101d0b9400040d101d040315400c2c00c00040401e502c0d50710001c01c04010b900034010030416001c0c40100212944010101d500d8243c8195501200d424090207a51206074007400262090000c2c03100c800101c00c5182c108111464014079100c0250350722820040120b6280c410764100d03e00404c415604928440c5065688007641160303981048000000103d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534767230 1250 534765980 534765983
    0x7050309071719050109050604080a110601031e2102030406080f1e060a031e030206060d0f060510210201030b1815010509060c0106031e1e021f09030c0819 68
    0x403c90100c40078460207601c11122540c00c20180d92407446d080c00c10a0307082d4402d01c5102c001030f0304480003014001000ca5154140c913440f10310403280c20001405204ca001101d1000d4499031465980d61034008034a80c01058445007035005140c44078645000500351a1009000401070b05000c006c020324074801c02c03e58055121207202c001c029446150107c0e0210016410050440300c0324200003019021904110034000d01c2036084461580e03c00080c0903400f01c507100020244c0070210b860300c1c0056200e800203507105d9125260f104013550f071400e01c00800c80403a405440003500c4004440255641401420130148041d41c81c2e06d400c0c0b4400851041c0d0b803030b0003440903c98102c462481503003a8410001c035184010018241d584807401264a14000c0145100460380414110502e003c20030130101c42048150700403002002c13036201e020284910b512000c0040380c0c0015001c00c000c0302d408243c2e4901080300c80300e42e01c40d80701d10300b1880c0c074042180c202d4100380d0b6035522085012859a850200114070603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534768480 1250 534767230 534767263
    0x30d0e0f1302043201020f0316030c0206030a0203160801050a050112020906041503050f072a0b0702030d050603030c0c1908030403060b030d170610110303070503090717 74
    0x500074a560180240565002061503001d0844885100250b070040301103e40e0080f0000d00b02805501c005994580540c0000001c5401c2800010004200f002903800e019000f400c1c0390025010781d0f03000449a910845020704016404401c0c401901e20314100341031103400905106100b941070000042200e40705208640c100070328820790720301c241020380540b94160383c0070b445552076544807018842e5859040c0c55010000f483d01c8000341032246180001740c040c24960f10703180c84400080c3c95050510030700d0442506c10303c42040004000820011882d80700300c2c11a03020b56243c403c08240074081d1400600f50b5846035000780300009601c0da0110b40025030f07500c02c442e400c012950340d10350351005501c10b07400a022800041000800d01c0095040340c0304099040f01510320a8101031025030b604010245820b20110300580020002e0409910311500c1280d1030400c558a030703003003000143c40c1d076200701c5803440081c001200b806030840c0200b106901510800740c0400d8031003d0381d0000c940e24001501703c05083c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534769730 1250 534768480 534768499
    0x5060604090c08010f0c0f091d07020c0d050f07060206100e13060207060b0414040b010905090307150903090b0408060f0c040510020717031c02030c090a14030d0e0f 72
    0x2c00001240100c010321100340240035001c840d01c800d00080402c20403490102da240d100c005a414454003030481581da402c0742d0a01c105011420703540c20310100030501c0c1c0c2035104100301a1119034410240d24131042c03040c4010805801d885414508020b815444a010741d8405014400b1500d895011700c815106440c3c101082c5a851540313454041011990250000e480064204180036a035044800c55a80030344041c411094501d00c0b494944800301d801400d008030040040c080d8950365048940c1021802040704e0402c0c0241d1248100301d0103d0382c1a8075001e584910384070406400280c018000c10006001d14200f61401c0201903c0310310040c940ca40f6501e03054005855801e452040d0f601801020b07100e1542d6a0900320040c1d40c2d0405805170a40700740203485001e418500000c11a894121044491a40b030003030045100e010f50000f900c9070800e541c05004011590311440035840040c03e2001400030101803000c18541083c00c101c0c1520308000000d41c00c00390646803e08840c14940054030100316 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534770980 1250 534769730 534769733
    0x31f09110d090609020a0e07140a0f08091002042c06010801061b06111b0c03070302041d0607020a0314030610050702010c0804290903070e0c122404090506060409 71
    0x5180344c50000390302c81450000400c07036440f5181c00303500c240d00907141c0c503118000e1041020310034000d80c03030100d0015002c8060071044500ca58541038110441e1401c9505108100400e201a030300650004245410075990080e020b0080d40e40d2950103c01c02c1003844028109800002c144800500841060005083c01c44e88034104504842d1001c40c1c011008000000301006480703203e40c02200b003da04801182100a02841d0105624a4203440180103055244c07456090002406501c031002c03020b2090340e0350700742c07006100384011441404960b001d0450305507946006002c602c107a000040d818401130003044a15150199180d00c0482d20303060440d142c50306440100e410640b0010f004101c1140440c0018210001e6001c2c4100514020741403081d20030300b43d03525007490180d10001c5515a104030010170032989000000ca03000705031001042e04c0e01303450814609501200b0354040e860501d0600385c40d641c10700c901c00c00550003101224284082812a16007070762b1420f010b070078944169a42c200c0c210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534772230 1250 534770980 534770993
    0xf22030b0a090b06010905011d03010905030c0c090a05010302030a0f0213090605160c0804050603090f030c03040f140d080d0e120909100b16080c03031f09110d09 71
    0x469100e0380a095514100340808007508a007401120280f9a00020813803540c055850403003521410307500c04040017841070001a0300a90070700380c00d815560741c1c0c000070007043c018001080e40204100003020303071b6182d40b003e108402030024104000c1340e240074014401070740c1c041041b4208542104041c01e941e01070f0b00003d54440e00401403410710b50f01c0d00400908110790307608603611894064144400803514075009403202e00948a0043c011003040100340083d25007040519007202004d81103030f034146514035010340755030321009507400c45e07130310200b010408048400c180202900d610503000404010ba5004a81215416040200200700c0440d008030240c0166101604500d94542222600c081030880295141d1044500300c0c0900c60003000141c000320010303801002c440d00100c1c241e02c0c1c0140702110a001105205d030483d40e42608008401301c900d82000907600030408200703820300c000100031b20109040700f5580400e40c0c150070808100c2e20085160295040e094288001140e5040e5500c1c008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534773480 1250 534772230 534772297
    0xd0605090901061401020307020303090d0804030c0618050109050112050703020904140105090c0c0a03140f0c060910051611100c1707210e0c120a0201140f 68
    0x5038110111204001c000441500a14100d941490f41070103001c1c241d03401281c60b0f05c00e0703800180d09503004100c40c40340c0707040210b00611703d01c0c02400c00a06258a071b0303803064000c0c1110b03070090703000460f0410182c030380d070301c849200100829007420600441c500d0540003a011010b0004850841541c07200012200340c080d804071035590708014001c200c0d40060038010850641c003805214007400d101ca00040c0d00345c03c0c2d0001c5402c030302801c10060854240070b40e01180c07805110210405400350a110141411024601825076048103030040c2090f4940002818606600d00200342d40c404d09003070a2048a60344001041584001031a01c0703401c0d403140781d003220301d0240c4000042021910340b21100c81d4560f40940c1e40482c009001029082e56229028211543c100c05900505550001c01d1141903440b15a449454200002e006582e030300d00004001980c001c00304280342030141c0224800a04540e401040d0b50702d041c190b180d005003843c040b481458954040c42e0380c44600540201c06006001454080c0d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534774730 1250 534773480 534773489
    0x1e03100b0313061805010b04090503040b0c03071a18150c0706060b031005130b010e040902010c0203070b2d030703090f05061f14031b04090c15020c03031c020d06 71
    0x14085520284c503000018807002900f91255440c0c00340c101400e01c0c060185402c000e80101c01076081c6070411500f01041d610100e1910070b0340c84100a5540041c41c0c022101608000d4958100181c0c41d210201903454a09405500401c0c0c011010005079504440c941d560003041988020307844a10790314041d070003800e240d040840242e030040200140740329240e5802007610010303900102146040c400c400140c91811041c2400301e42c4440a6504c14105680030700c0301c8500514101c1d01414054010a0421810303810081c404400007801010100309c0c003010540304010f00000f61140006501e820a8501020700141c040603182d240a0f802c0c00640c124180c82681c00c802a6045814030f07400f000f103010700d01581c000b0001e002c00000070b501080b0107001950314001402504505000713402c0c000021003c0c1d6016903102d56642c0c50720000c14103034620800a461000c00c0381d4030b55020140c0181c0b500100c4540c4920940c0208014111510007030319001d0f01e003001e88405600d600c420440140074190303e811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534775980 1250 534774730 534774743
    0xb040b061c0b062208011d071a091008010317040e0c0a02011407080402010e01031b181206050a051b04060809010617100507020102130521010e031e03100b0313 70
    0x501145002c4c1c188548044412500007080301d100040e003c1000e0341400103188140340c002c454200507503c0b81c40c2d00c2d144800700c90140989808828400a0320f031002c101221000035510300010310400581e080d0100001000c050502e0503d40303080034520788680024102d408950b0041042100b1703078000d400160340e03420030040c401e1081c6130200004110f000122010790008000301c00000c80b55000c2d1041c60210840c507100445018041441510346220107414030008030340c0040c0c00140c0d44038501006240a209010100d80da007404240c283c00e0320380107402c81c50380450070b2009500555185044070100c50141c20513801680e60000690700403c4140d100596045007030281c1450010041840c02d02d4500c50700c01006103881c0c42004900301e00172412061549030714550103005034980880c224594030071842c4201c0164070300101250948044248100c40c40c3d1010a01d8030060320391207940c1c0700c906148000c1a0661030012454103420a19100310b000454001010403c280362209a800346a0381151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534777230 1250 534775980 534776017
    0xf031b0d080c0f060c03070f0807020f0f0a031106061f020a1b03020301050a0e0705010e2202040e01060215040b0618010b0d060504050c04031101020a150b040b061c0b06 74
    0x41c02c40d1a103034041c03800300c80360140500282241e900b02e8180c078001c0d034555031581c903039061008080d80c05400252050381588a0000c424031354090400428101d510404040c001d050828a8007524850f01c141609160390448020000d443c2c0360b01c200040c000c08841c180000000384078105901384510a4005444440925460a2074040000d1600c04403032090700200142c2c1c0d5909828011181900c000d16100e0300002c0040103e984500c50103500610010400903d04200004040c05140c24415610015401040c00c104244c100380c6040d005020034006040381d81070305580c00941587c01132008140a0303107140070032480d40b150244045250704490721500d407543c60741c0c880e860075040300038080021400d2a901040c2424070f4001d00d0b0003440c0b00c0c4480f905080c00e40e918000f01042900c2a01c0c1188a004c05920115950201e5003c82840c0f010300041ca01031110144810303140c142403111f000d00b00821024200140303030032041d00c04e0780000c48000f4a0301c81050004d041d920078080004d20354071812 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534778480 1250 534777230 534777247
    0x5070c0909060902090f090a2a0e0103020f06120601081503010513020a06030c08180c060f0a03060b0f09040b0103020408010c030f0605032e0605060d09050c0f031b0d08 74
    0xe50101e00f84500840d0fa003126a07072014100020101c00703d4040d41c494004480141c0050410410152601260181400312a82201407484121401d9002e103840c1c0d40100010415404c1880800085800641d091407414040c1c003116110f031103001d014541046803040001d0b0340b0103458818030740d000c18010001d201c682442c0342c0c110707500b001c200d0f0243d03c075440c4040c001840034080d1203032400020756503c1da060256246a02503a601525018032405402803100038086aa2404018004c491042282a4643c0000f174001400c0360426042003005403420400c044280d03840e03409a42c6024000c613004103102020000480207801694400103056080c00040100c0a0305500321545401c40020f00b04200c03a605c100300351342d80e01c00940b101d840e920701c4408681ca010900c600c18101949844001c10301c1a51000824041e5114000600806a542c103413441008418071550401d5030303080751b007140514681c00c0060703203420808001ea0007040740202604003039203d002e40090302c646c01c585465203c401a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534779730 1250 534778480 534778493
    0x7030f0b0f060907020c01030908070204140a0c0302090108011710050a06050301270b0912070819030c021902030a080705071503020721050d0c1e0e06070305070c0909 73
    0x40c0c41c40034031454880000741e05820110302c0580300f00003a600508010851900540090803030200544403000100000c00158070765004010150011001c0009146401d807108821902c1c503501880030076004200021150b07a1250748103041d101e500902c02c0300012485485031501d440000e400310f01c54100810032a940700d10b54840402c882e410b9000340702507500d00f4032010441602108800785010b43c075220402183c51150b0b19170b40030300d00300308484110203041c817010060342200100f100d5010b40010b4043d500381c01402e12000c41c159908007800074201011000e0749848103a40041c0600c0392507a10181555001c0000365096500406030507911900e40c1000d0b81c5408542c09107917448040c80140e031103c2c501c2071003200c00303240e008820600c0c800b9440a0404007100c40c0c00c1c4d5001040018031240c4080e28441c4940444040b031a291402c45d006081520f092400b420700407501802042d8407042c1c0b46071130b400c084071242c0f5030610340940d036502c1c0da18211032803450b0394001d03050051500317481c001006031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534780980 1250 534779730 534779753
    0x315020c16050a050109081009240c030c3015141815090403050f0313030e0109290f070c03021903110108060301020c0a032d051b07030f 60
    0x102a10700302c0c240c513100c40064036242d4091040c14030503400181045103400080d07120391140c07403140503260722803a0301040e0646035030310b421482d42e201070f961010351004a03014482d0f52071401d1107052841c00000080c04c03841000c503500c40c0c002c00ba01404030341c00511b41c009500c419011900000392034071264480304500d00d030500c00700005d805080590000d0088140800805103e14400440105180c0340e440901001140290044007848000d00c00f01c40c120380758078003451280c5481c2d04451501c000740d081c014010030315070b1101c60610040d0442840326920350103044e5403c0d0600c1c0e1400c080030382540b44007829807003030f8200c8801802d000316043c000c001c1c001150038100c80c000c03180004d20800c14002d20482001e2444002c021080100c42cac101c3c1c55010b2010203500003401000181444c00d80c00c4903505092504100710000b4011401064680c1c5201c201200441001d24000810103141803004e4010312511211080c0c840c241c118843c035041d0100a0b03440907617444506003d00b5003652a25040008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534782230 1250 534780980 534780989
    0x6090a0b03101109030d02060c031501030b040504210f0518181609140f0d03091a2d07141009081c1505061b010e0a030f03060503070315020c16 63
    0x34a400681b04544002001405503030690811407468583c000010100cac0c80c100c0382d06060548500c0524042e588921450384503501070303000d04001c0b4491012010500349040321000c00c0c4100f10712401b03030403503001041d60400400d5010600b4403031034990000388000c41d884001e038508016681000b0b85041d03162180c43c4100025158406466100c0d400e154100310070b0041e00fa003095991444600381c0c601441c03000301c124080d040c4002100c1d103450308040d904203218024110300800044c500ca1880c00e009110002d81c91301d0941c0d00c0c0c1c5e20200705490041e48244540542006c10440700d030084c0c1042030100350b0341180c203101c08000114040c9000754042d009451700354004400c0140c83c0401000900814a00c14448040c06500600303003c1041184c0c0c22607004440102c50f951341041c0762900900c14201c039451548010000c00885c1d00e4000e0000d200b800001d0101420103004000c162030001e6010181e95011984001c00b142c2038103004000d00030510314070030718440c0c0c2e030b0b41003412910760304001c0076076 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534783480 1250 534782230 534782233
    0x10b03030f0a090812070b0a18031805040501030c030f0c0819060c05161709040614090c071208070519110c01090305031e07050a030810090506090a0b0310110903 71
    0x480c0c2c1c0d4404c55494006188400a0415080004000042c00c00f011307180c0c401c04807040000c401c1c4c0d01502c440c2e400e602d0010200c0205000e0044108900c0680c0f00000042c034040703c2c2440198155954107040103400d1000501d81c080c00580740040040111a080207400110122441c04041d602c4007144180d454806444983c582601507581c60310610841c1d21341300f650342083e04c400210740e840c9030381006d0b540303074500f00b40906000b20003065407a40103d000500c4200d0319156807224540070440d0303041c0c004e0f00d4510000010000303400092818844000c80b4035990403d58810303650718405644a07c904c05c0300c03c000d0b00350301c20902002c07a000900c14180118600460f0911300b00c08005452016007400060107036441271100100749103101100a07080c00210f0b045604003070390356803801e01e0142985401c401040c0d8070001c0080201c080545503000b810009010701007401c25402045400c00080c3c00ca40c0040e88402038016207450030810800008100b2004100301120703148140a51b42021a65500c02d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534784730 1250 534783480 534783497
    0x30c04231e010201061e0e0906042307030204050412020c0303160f05031b0f061311010518090a09150203060307060c050f010c030509010c0c05071205010b03030f0a 72
    0x4115030410440ca4890016044060807840404070740010803034005072904643d00d59101180303074a5400c2d040100d0041c0c10184406407410301003064041d050040546e60164004000c110114814191489034912103401c441014441c3c2ca10f081d08007080ca0f04040e40040c100380c02d101c2040080703210030716070314400c3e4207803003d03d075241c2d08140d2a0320800003000701c0c1d008180c5505010410b00900440c105200c0e20480e45080225461000c1412070990b4603072981d005444003100264041c04100c3c1d00c0900170fa9000d42009190740c030b4410000c2d03522042410044085405070041101d40300071400260007d01064032450705040150280029100881c0e03a10b2a4116a424065083c000c0e28003810000b40605180d41c01e0280489074554610002e450b2845079000d814078002c0203200e01036848145560110319460309591040c25100c410480c0c50401404288200104402080341000d46001e1204e01da05132600f8100b890151454030b0780c840d4903000006000d06403400c464000c02002c506034540491 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534785980 1250 534784730 534784769
    0xc0c030a0903021314150607060e060709080d0f0e120a060e150408040b070318060822051015050913030905060c15061836030d150b030c04 61
    0x680d05010f080b810000c0c105c40c00705203064007904c4a60407041c1e02038501400c0601c1034441038140c40000c070348400c1c03e030020814004040da1056421015042c2c01d001418a00101da40092034400010f5115041102001c6007d41a40d100c3c160101030005183c02c880302c1100c00c1c14103a00815408103010040d1080c114481c5500d00100c4186100b0758000002d0f6003818582010201280d10140040782003122004d482941080071204200c060455542c1d03890452500d83c2d10129030000c41545c1d42c10501c04211071f44001103000078562160310328900042007000e2030905443e650841c81c0c018079403201e2050104007480c030021302c800030424000c0d0b4400d84119034030400e00002d03224003a0f00309000e0300983d4440e140b1010104c41c2c207800460140a007207441c1c0d822100400d480005407a0140200e00c00040210642c0741d0010341d0754404c14003d64000c50740d181d400304503902e110b00a05000d00707030344074540c410038400c1020740e40004041000c003051740ca140100d40c034800c90340140103024082030107401010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534787230 1250 534785980 534786019
    0x40b090a0c0e010f020a0b040317010f03020906150d0b01020c030a030503090634120908090306092406030a12050a1409060403062412140c0a0b030c0c030a090302 71
    0xc0344180d0340241c8084010344c1c8a58400300c80080089d001d204c0700ba00084c0440c88680c1d4910700800004100e01c03605403c44c810000440009404140310300e680b200541150740590717041303c041d80d1040d000060901b407094010303800c042e124448142d02d0300429660700140b5401000a42c0302e2a940002c0d1101640c8028000045203442e10184c2004517010488812410110b0700c100040001030400036411032100c0e100c030090381e42d0540101c0701400c0200b500459410204a0950052201c40184c20368034510704440d130300501c826807001710a02c1c00c040031a0b00c41d14248000d821094000c800002c04490142d80605642d000d001440001041d40c0e001180a40c20700003038412401c00201802d240924641302d90b40a0500c440704415907226101080400b030345140041c0e0014411f050031003005e05c1450800e040b4102e0082c100b207416800425040542e0303518003012005036044092040d0302c07601e0710300d55440035024203901d400c2c003444009107a69240381c009900404503842200c400203120010507115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534788480 1250 534787230 534787247
    0x3010e030912191403070c090c0201150e06151902010603140105010807050108070302190e2115070522170f0604081e07060603050f07140f040b090a0c0e01 68
    0x495840c3c1035209440008040303d1007030581e604044200e0781800da00d51111404001c0c9980014200356481108070403054085c05000307480b0400081e084a02ca02d84401c00d481c1100003030131140f00d2014030401140c1c643d0b01200f03840c03014200c600c40c58407013900a00060700800361804181c540c003001e05a0440c100d041409040e059410000141640301d240c50015140f0300009017864050507001c0c041c01505100c1141c4e00d4042050030340d0713a80004010b42d0180200421916909800b000400c4081306003484006144104c028404007010841e655280d021070362802a100c04026821400301515098401c00c02901d040d2010b500e98031000e51183c0c18425035811100c18a03128941090703002902107070440b4080e12070214203030012403500d403004540c4c81450340220012210300c0c2d698075081c014090300300030608030b02c02c5030700061120030705042820321401d00c2c400b4164824a40f4001c80013964482e5005443c180b03001074102c426508041c02d02da005001004c43d05c03800620503070382281c80d035071191b46413 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534789730 1250 534788480 534788503
    0x306241b0d020c01032c280c0506030601090503070303260112150e0f1b01030c120504020f090406020702010e010905010e060309011803020715030b0619030b03010e030912 75
    0x107060500c0640f00540250081c1c01030103294000400000204800d40c20251040100d144c01405005002204492410b69500a00701c1e20341031507450040010b600c0b603a00025980212070441e240c1d030700d01c40100c031207070342e0344d0440c1342c15010f0789070000300b055040100280300d15480c03114010034000405032101010b90074481da80c9429001c00c09230000c40c2e03602c1004030340c2980050020a4010800404a01d400500203040d451a80030a11007440e6841e10142c0d48d074907441c240780c10700007100c8038a00100204050780f40f02c007072250340e074010408540e500f01842c00c1c01c0c18082c2c000415403400c1c2c14030000035008a581030340440e15070100314009601c204100425104140c50300e000385144003041c00015000240080d02035076803004208098803101d84280d003064400d034000c20049040c034001320440d26400b50248141820320664031020b664010944601040c041c52181c05114040c0d8210040d042100389550554a0b0442c0d0054808001c002401c26110546000d9031080b1008900c0b555074002d0102c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534790980 1250 534789730 534789733
    0xb030c0405131b0e090c03091c17010609051906090620070f0305160608150112110c15040503070305091f03020a0f020a0c06050306241b0d02 62
    0x3080c052450401d03281c58881400b80c0c000144074809010030b07204400070151020116451912002c3c01d490720b60003059111500040d80c0f400d6090034491140d03980312800480481c04600881d92000500c00c4403200341400c440d03807085c03200b03503544d810181c14103c10b8011207006015040001c520303410080581c0d8115401a65000745052906004039401d1807a0503400c902d502110880b00b060000030041e01c006003101c0d0380e050015034594a00302c0e01d02000c00c0740001070540c1880003000515040140d00390302c084124201902072042800484404d030445d0450007042d8540900c116a5086103800382c44018490012039110022501141d444614102c40060a551041049100088c807078400340116031030203080c07180c0071a1519420b142e040d884648610019502044101480758010850925003015001500e604034054944010344200c40c040c11041c1705001001c0394007600c0d00c26104662000d8001c4000d00e01181e000002540da201c5142c280c00394840031020406043d020810b954644400d80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534792230 1250 534790980 534790987
    0x906060309030e010f110709050f100f1a22080f010b220e030d0509010c0e030604060903020709090c0302120105010e0a0f0b060307020c210a110d06090b040c0b030c 72
    0x10011a07174044002c0350301e01040248220020707000410004000035095645020816107805515820001320080a21500002001080000052403c42d41c3c05503418a500d0340c1d440f103d2030303d0030a403910400d0000c1d076501d04001e5803413002400e0f2640005c1683c0c3e115040d01c081c2c0346c001c09583d082c1c4581c101410b9201c0159402c690805030011a002a0070206560106084051107005400c40c0c0008480c0348004d510350040280030350b02840707000c10750040350078100420b000b0007000c0f07035444c880200000d01540d5511014814940200031940013081e42d14800d0041544a18103488142c40511040703001c0c59801c01400c01c100390600905040e03c4001608002c140c0e24011124083c003501e9456000c02541d4a0840c0c60030b80340e900c011031040c5c00a40080105224110601c055500000c000008070017000303140000851008c9500403001d43c001e40c6500118860800007542820320702d0004ac2100d25045030407040003103e0712298405c1d4010038610224a40d2000001080d00c403c44031710342c5441042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534793480 1250 534792230 534792257
    0xd0806100509010513030602040312270905040f06060b070605010b18010f0c020301050f190903020613030219061409060105130f14010807090e0c03030a08070c0b010b04090606030903 80
    0x90700909400d05001d01d00c5203031170f5603d03210f40b02264056003061b80d00907114042c08401541100a000740310103d449024103e000303524410340314020601413809004d85900205041c00315428580c0821a0000c40804c4401d68600030f0010319480746200700d03038450400c0e00004d440500c46050350017404a000c503002d50181e0071401180c030503d080449506010761541e0107000f60300d0920441d0700c21807610071544144c1c02d150101c40340c862112818403040c03a080c9081e8200280d40420300903080040120320080d031064614050b03080042d400d6840860905600c210000d0141a070845820b89071141e0701e0841700d86612400e1922298240543e0360494644400328804010780c0c1c0c0703d0749a40e8066000011103059000e50107901d0030082e070101245a120140900a480711440b40e15002c01924008095180502c40800d071a40100300c1c4000600c004140000c101900502c04111200c1c2e214405610365a1513604401d40350b0020700071515868500385011030701038040e00c540b040c95a05500d1f1040070a006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534794730 1250 534793480 534793487
    0x6061309020f0904022e0e04090c030305090604051e0f0a081207060f050907082e02090a030f050607090b120f061c0506160509090f04061407020d080610050901 70
    0x14100702e03000680400919544250010180c2c3c0c2c5440c0b406c604900c011141c0e00085c140244114000e208602e00311072440014000b25a13a011a90701d401c085803141005000128140101d80c001500001005240c2005210303003020340c0c0340c0c124111591592125060280300c030506546c0500340340350b480940c20126080c1c071400035143c00c0b841207401040c010700780615401610400c2d00d051907154450bc03000e0008038400e12078541d040200034580c001440d428401010415582904007890303a90001300d1014a46400e2256005190008140004039602c0e103030590b6140c204841050000c0d000420120302c142c003000032680c03001c908080d00e000d5078958011b007205801e00506a1940007400704840d0554074001c803541c080903070140c00600260319100140c0948000614000001c11408003d0428645c1c0e402041c150480b41c002d401c55807560b100d2402c600102400c0d84901e42c018144010401c0c0700340c1c0001e040400e10707459036840c4e441d83c0703a150900c0301c8045114032400202e1030601c181c000a510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534795980 1250 534794730 534794749
    0x606090b16140c010305090c011d030f010603080706060509070c0204020a02150a0213080303161803080f0c011404020306060d260909010614030f07050c0f06061309020f 74
    0x7a50a03840340c1c11000341c0e5000c40d42103820744191071039001803111a009680600c102d40d841140c1002400c4480c0e005c0e00000d02c00d90600c0d00b003402c0e551184418050f980c400b0040c180004017110000c20080c2d442f802c10203119007046504403021414240d0105450901e003010500500054807000114000c80e42008080d40001c0c4201c1300b14490b0007070382d02d0255130f2014801c2c003c40c201000140d079902e41c071019109001c8560412801d6520407c2800308220505103080c40c0324010b03140c4118000712843c10405544865403024019000100301c0800b500b488034018900344005400030040803c41c650700c90800032040305c0195140d002480050140e00f442d1114400d818411021a161a0388910702c0c0b0000103002c1100f540c0454010800f11030908258800c0ca000d400181805903c0700e15404001900d440003d0407440a00c8400d80400d044500640a40343d80618600c00e56454594072000943d03a000308a8880d8410b480315840050010400e100d071148142d000341214001220710801c3c8041d950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534797230 1250 534795980 534795997
    0xc090312170f06130504080d0c0201091109090f0105070201020405270609100503031b060c030405030315010909020c0c010912020f09040219170d170f06060c0a060f0608010606090b 79
    0x602c40c1c00d0b404c0381200b40c07080501c61442040a10745500d000c040c07130f034116200c4007032003810344e0701d4110150007140800c181122200b000b280d41030180e40d10a542d031030800410300d5404210b582800103010421f038041d0050400e40c2d000755044040b40c00840341081c03000e040022082c0100c4191008241141080039815034000e4450a482c0425542d81c40030074034540c0642500d24413107001601580c1c0101091002603007221035000241d085081c90b455068a030300c409084c111a0013180403c06240f640038071451001400d2926046444035142d210306a1541c0c0034032506400109410008698002e21010051031160080c1181c903180e1020350902c0300c0010058400d0744e0203440400c0307160703c1c2c0002c8004500581440c00706424a01203824400785002c2e508103485c400d0118080b80307001d410041c1a079140d0301c4a0001d0401704551904404100795200b0310704140b006024410503002030110582249032030b09001c2d0f0381009125599694103088808900949000a9402d8410040f41c41a00003905054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534798480 1250 534797230 534797239
    0x21b100c05030c0d030b0307051807050a021207030815061603050918090a030206010e040b2202042c03121906050a0e07030b09041205070c090c090312170f06 69
    0x90116083d00b443c04051180540000e03403540314031720b16400c0c14030110005040a8525120541450080c92b045c2400101038608111002c10f0907200e00c0e00c01c1102c0440000180740702ca513600441e040003081440211851013881c003110002c1d64403401e002d021a1071603030004034074240c4600c1c039690841c1c83da0301120071076a11642c42041d4480c107031024100c0303030f0203013803d00001c1400110901c0d020f070611905a01200021482008200204040006255000e050b601800340c84c072100701c0000101d645622030283d08646880d21068840400c110300c01c2c1050b41d50a564402041c1041e11199244140350010003074204040200c0c07503c3c81c108554541c540e0545a010551584a201040d401c240c564004181943d04d6070903c059a034141c419541c11000580e0302d001c2501c5e00e511603400090108980d4004c0140014105041c4280610340c440076203030030320091201c2d0780096001003240580340010364003411140721301c681450003191911a810f10300244a20155a50400000707042c50003045103400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534799730 1250 534798480 534798487
    0x8041e060e010f02070c060806010e210f100b0f031216060906140703181e0503031014010c1a0703020403060c080f010b1305040510050a060e01021b100c0503 69
    0x8000307082c0540c0304005031502c0c0068807a240e40c2080491244280e01c9002441401070501000d039900c0010f0710407140c2c098510480e09448040154000d16050030300c080d00c0c2c0580c1000301214040450811415050146c06001c04048103041000d50781d824581903905500265542c1d0b200c01400300500f04d0081c136a4994a02c084842d1100c10941d80b807030300100c601e15500c85807175945148031144980c0148191400300484071040e004007007024800c58000e0030004155030448500f00c1c0b070006554034550f10405403601e07030820f40961a6120400e014048107603843d500101020f500c070340c101c0121316411039085800b80c0130321018030f002c54101400003810507800300f0021001c1107440c0540c96140fa219034541070070340741068400d4a1400c040e0042c60700b8080410000850341540b03640c0300c040e940c0c2140c0008040d191001d21541c0042503a00c0750b070b00110203010002e01a80c0055012018a030203800740d640b0000c0c00c0903a0a9440140c04450341d1082500500358981881a00034035402d52090b02120325 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534800980 1250 534799730 534799751
    0xd09030e030f060712110d09061805010203010302040b060705060a0b0303121f0f080c06030a2408101b1209050708010e0106080601060f1d0406060c03080708041e06 72
    0x28808030b07100e90b45055004005101c100e940c04036131518051030984d010001c112440000b1001403007417041a5640c291124600c0c0144207a650000c41c81072000741c41a4a400142e2034a075001c0d41091106074402c529286198a03241800b130200d803042648440585900d50b00c6a060710010f150f03c610040d014402406a42e08408003458428050052a1064482c0d40400e46c00740d0308030071064010300d80003406918100828403002800c1048241c007200c0c3c40d9181e03501e40082c00000c001b01e5038000c0c94100010590092181c01501079001e0340c0240042c0d03081c048000c50140d068403101000c400c4065800700103c3d010034461100c2d486ca608121101086206140c0c649524115003074211100e10f0355180c0c1a0400c00409108007401000c200d4054003681d03242c020058440e4040c2601d020912080e030242c2100300c5400346c078404d51000003c100f00034540e101e0800900b04000b401c0110045606600400c81050280c1111842151321503640c403e00036a60039580704d141c00d0b0b0341080b81c429448080449 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534802230 1250 534800980 534800983
    0x9070e0c0403380a0e0c1009060311091c1e02100522030b01170a1119090507020a02040b060336070e0714040e06010302090f1903050d02010e030d09030e03 68
    0x5000c1c281510300420314405c4088620300b04600c0c00a610300c5103401c01c50255245820070407501c11901541800039200903480c0000794036100e6415a9075205034030720040c010580042410404490040500009c81c5418108443c80c1105440019601540c5a00070b006444d00c1400180801c800b0100003100e000b1078035002d03050040c00d0380c0049a102d04648018080e0403000450350b0b440e00b03d801e00420303610304582c03110342d15a4401194640500000c144090000720a50415001000030b40820090380c0b0748440001c1d1a0540050200c2c410f03400c28000d90198030f04001640c0c0610b03828441002013102c04c100190140000d90741e40f00c0340d080341f5900700d1145042400400014020706d280d0800a180806000700241c07000c01d000380c00200c0500062109a004840c95540544282401039803100885d00166150400d40d090b03d0348020100c2100b000d001306020000102e070722403000c84541c0c900454041e8240e0300c0902d41100e42d40c3c028005d04840d2070306d0703030003201c3d03140d02030b04000c1142c524910209 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534803480 1250 534802230 534802343
    0x1207020a0b2b1802101b0303050106020d050c0c0907350c0a08041b230111060112060908040f0e090c010801050a0608190509070e0c0403 60
    0x50781d603440c8420b0000550191810740882c0c2d040008104807110070741c203842d14003030b82210000c1e0091140603061071085005038824a40c21042c00c0903078104411514004014000c24010017005006060140ea042405041581c50345128440a403030b118801200b80210b17260014400000c109503009040081c0300c803241185900340144011b205444502030590700c1070040502481444401045400b90590303001a9a540255000b0800200d88071460940307040f08109800a4800600a407884a0142c00c11440380401d16804c2e2035000714061030100d80303501d507a424801c8418004070781c3c4822001032090b601c201d50042c07143d9041c5080544465850038804d40d550051040014480c0030f01401c00010090305150400901e0121002d41c1040049030614509c0e1292500b84526000400d0580455048034002d1009031a03080203140741c0381c81b40c2a52880c040c4201c1100304000340200b0703504c2a002e000c440585c0c1e000031030036100c107134010118048001034000c0030050f41000f000c0d4503050074020840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534804730 1250 534803480 534803497
    0xe07050715200d051b0a1103070605071d0307030506130f0803071817070302090618040c151107171002030406091101030203090a140c130212070c051207020a0b 70
    0x1819120f940c0d880b044001c8a4010f4070812014448000210440006100300c075004c006519260300d200034150724207869070140d1500181064101000c20000c20b610061917a005000d041030b540065041c40e05058541c05140400780c1a6000080020801d0407030043c590341d101d00c121850044440c003501e41112680083d22114001209072950007a172010012150313016044484070500e8100010451503a18481c5100003800f401c00b8800003440c03583d07040700300038115a00450072031092400f4a40101c8441050050301e0701c0ea400061100f400500ca0340142e103403000110000c0260504280005551865401d07159000b40308030349820441100c0381c0095405680704000c0401e00030f12914188142a180e1480241090310600410034248400200c4240ca10380005c40028141ea50141047c1400d4154200039000214540c0d0f40704195610340c02820311a9490607100440e0b01c80d05011900409481800f5003e98400b03002d0f1f00740e0302c0900000303144440c402044090040d550342203010481d002030340e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534805980 1250 534804730 534804791
    0x80c0d050f0702010c17060d03050405030f010c0810050315090307232419060506040b12090607051b1603110f01021612050a050303040c06090e07050715 67
    0x91160003070f024092940c80c043c03941820100d190071940407964a9070300070007551041044001640034940210126005008064150364018884900250103082503248000c005402c400005500380c03105244803050703841c014080d00e90341882c0e1101400030800a0710305080e81c0010043d5400107078619076070059408400000134a6941d4182c20389040c00c00e944009003c3e07940b0020440041601e401145038400240ea4680d080d440400d049440240f441c7d070000764001000142c00314030b1105d02c8019280840c0c184030800c040341d480e01d584039110007043e1107100100303030144030b003082c00c07c90800701c490178401e40c7d4125083c0d50b06d615406040c40306076a1095422007203d100e041d403603040540180c5144c00080c00244010045109a100071a606200302c0410b0040c001618080250030310500344055007180c00c071ba40f203040505100c451000c00388070ba10085140f02400241e240c6010f4800d038800c40c219101c4130300b089100d85804e20b41c18101c44000c501ca80d69002102c5002c003688426051390a200a0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534807230 1250 534805980 534806011
    0x411041b170708010e0a151211040605010c0f030507170d150e0a020705010e0604030816020601051c1103060c03071107180902060f220b130501080c0d05 67
    0x4902800c2508400540e40742040c00d4020090099040b40c4402d044401034925103d05030f5504000c9801804202d00100301c1d810329400018002070100d030315041c0a809690b071307101c400e1003031001c0100f16030041c45100e0100300301016900100d4074404544001320301a08085241284035a10700005009400e8403c000784404200c184660034140708102d40905a4850180440e09081c1c03000025640100300012580d00002c00104004003074015514000d600310456600f4245481c0c00f4006800440780408000840c3c136031400c41c1c9200141c00307412210040c040400820b290300102c0c0c3c0d0005224016900e5034503140c00801039440c20004580b1505103150780035164181580c00511010494000e80d9403a03200e5001480a440710102080315034102c5031f400030b07034440c0a101082107405440708242600101240e4001c4101c003501d118207043e1440881215916100d9020b102140520340501c903202507247c0d0141300650103403070700603000482c641c0e0007030070f105d00301c6031078000e0350022240c41e0560066031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534808480 1250 534807230 534807281
    0x2040807172407050d1119090605030438150a051503091e010c080c0a08060f0a0929010c15020a0302090a0e0907170706030203041104 59
    0x40540c4400740d005001401d1103080c4100250315484000351808107160b00c80000c6110709000b482125503c80d6803800511034404081ea014403160000401641c041020030300302c503c240c2c4103101c0f01c800d982a5482d03030303429515a911230b01c0025050040402915074450383c02c08c002040303400115401d030a06444188146825400da83e0f07880d071803900751402092151014000c0d542c8003035800c1607010022604035180c0c1e40e0f1000841c85c02d10210a08e0f07282480441030140303c01c4064011480d421041d80b140005901c8200c410000e9105581610000400000202e04a4a0070070038944500000a00318005951106408000c889203404001481c20406600107560400746020120300702003404d101410414136100e0b0100d8807003131140703810305c1d03503002944005141c000e40c10790700d110201400320300d00151201410100541c0641d44c40c609485150b40004900c4202c00030191074900a8002d040301e07511b0200c0c107034080e41024100f1a4030b43c000392840403843d11548200703009204c607031807404040c1c1040b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534809730 1250 534808480 534808499
    0x60f0b0a11030a1d041d101406060d02070c030203121809010b0a080a0e060a0905010e0c0105091512040c0e01080d1e11060403050301050f030316060b1302040807 71
    0x103070030380d6107107074000f40502c0a04035002003643c183c551410f481e1a400400d035200043c000c004075400c0031a600043c174214070b034651001441c14001608510100482c011040810194110407110700c1c4d803000080191101c035040c10380182510720711400103222401d44950000c0d0500d03034282400e42a0f02400310300030090441104210342d038000151006030280d414010100395034810940481c060100000200e4010342165200212100e03a42c4155006410003400c1c14000d05640c00e002c0d11550f007002c4a89001c103201090094020505848a5140c811071701c06010020480e840b6800100c5801e00c042d404090000c007000d84158481c0841905d001d0418011380c40900d81a00030070344030386c4640048602184c01413001c552824996080341408452450225040000d85c0f40c441914001e40c1c06100c1050740140165041c0ca4088a40c0001407400a013459a00d01034001c8101c00e210b04038a4580115060340e10140340c0650203021f01d204415201a640103981c801c2d4087c01c15a44608000c0092194 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534810980 1250 534809730 534809747
    0x12070b030a1d0309040e2406010815030a0311010b060304060c090e040b0a15030f050606011b05060c130f0b0c0624012f060f1602060c0c01060f0b0a 65
    0x50310180201d41d661002203541e038003409955034002d541e170751b5000500d802c04204000950f03203004504064134100c41c0311660b02040580e4601d010402d0034010a05c42c0c250311461040da2140580100981130740e070f1703d0072142010300070803808265580300155a4551100e20003944502e02908000c82c098214441c011300e40c1c00c1903800322141040b100300344070025018241c1305400600c004400316007003244600c140105a091f41c4020148811848036004111740070401d035200b108240c076458041d0092120706500101c04010003032250308140006020029007030050310350000007580500807603488024100d0322900381d4012a41c075490201d48100210410040309030b200d0f214500017001180030782e0101039460507a50f5000e06110b00341c907610006100c860130416104a40c54810340b09001c40e00c204030340b00c06068072212030407003140f000185107412a00740c0138451141603004200301c0c0e071403407c0140c56401000038410203548942c8001071140440e51050003174010018002d907030701c00450003c2c00352007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534812230 1250 534810980 534811001
    0x1406030f0706081501170114030105010e16032c0a060b06041a090d020a17012403020d050a0204020307080601020c011e03020913020d050f100e040f0212070b030a 71
    0x10700410003441929409609541c0088100c500b8103c0400703620f005031a440450541d08117455005000002c190030405202014940190b008209590700d48501300d02290086401c1030450703030b44020b542010317480b03644060355851000b9120010480318023940202042d125610704c1d07060380520356807018000f551007200d49a100444000385040d20704909039020a444030420781800302c0106907049980c6682d001c401e0003a41c010301310003180345c68801c0700342c04a5100600111035031820150003044c0d2030703041d49002c04100c6210081401843d40c0d0070000c01c84101001100c8038045c4840c0c440060b1240d0000d1030040c1b03c41d1310782038203616107040024a42172890703081d9410460640b402d44180041c001626003080468500035075580c8000e130110302c502140001480880e80700140c00c590360b00f00780d4000c50283e260320410b41060388901d200109042110b00950310b0b90705002010a00140e00e40c0c00b5403015920161003034407004c00705400341d810302410307a00c0b100182c80000100844110a44503034084030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534813480 1250 534812230 534812233
    0xb1c0603030801180b030601170d0507020d0605061201050703020a03051e01090b010e060c010f05010f0e2202100f091712070602041e050a12051903030b041406030f 72
    0x3403464800a04204061007400d5540ba40c008036402218501e8102d900c003e500079080b036901d560745d03010035810050340001e005034901812603601c1c6400d00ca6400c8480c03494008002d13000395541a01c90b01c4c02000090102a408034130b003419044003210a000740c41c820328041d00c2c0140c0710b0314888406400c0c1d031f0000301800f1b03250807002e4084840e00c110301886819512200800541205010016121100224012540010041095120b403401500541c40c101c2902c4070038400c1c2d90381c035003e00743d021500f40950340110341804005a1070704514104401041c507540c52003151601d240e00400ca10101e40000c00b400603500107000710350307a50001255001040f40490b5550a480504c2c2e00a0301c03108110280c80c07041d04e000508609020700e5030142c4001c0c0c94040b41c62400c5020082402c1c10b5400fa40c41a24000c003428003002916910301101e40310300b03e4100c0050010403006071407000341d4042481d012414181d0707034242c14000d5200e900c54211407840e100303100074182c02d10604044c44e1051320078401405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534814730 1250 534813480 534813491
    0xe0307050709060f092304030e060f03041e0507121712061e030304230612090c1504030b060a08030307050d1a030d110304091404260915130b1c 63
    0x4c01011803034400d800340840c46c1083ca04d0302e4903c0d04072405134860001c80d50115010919400a490140c011405144103020303018110041081c0c0e0701d0320303800141c006002d5400a10040008190444803402c60700d2040302c104e92800c051f141e01090711b421500001c081d10701240b0030088a42003051034551032200c041440904407001c480000d54901c07030b600500d0100c14442c1d13200490541182c040e1410b4000050055031a8020b580920380b00e480200c903042a140b284030b2140b03c09040240c04017107501c101c070300c0c080e00e0700d030454a5000e144580070b0000380d080204120001800b49040c000745001d100550380d03407a0303111407810042c01500c042500e1040d07008a900a5106160f40000e41c80c02066002c0c20800c508076a800241801c502440e1312005003d4108031914072008034007200c4520552042940c11881e5183e07100032540100d0103c070070481d281040015100e0392801c80e05184402e03000488980c50612034076040d80542d04a68494080b41e80023258000b010b625248510400194003d400c115 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534815980 1250 534814730 534814751
    0x61d040c050f042702090f10090b01120e0f010b0a2102190806040c062105181504030e0607050c060f0706050708040605010906060804060e0307050709060f09 69
    0x30030810311070240b0601c5142d001c41e91a8607140c01500c415640010703007403039196040200a2140303581c0030302240b04100d600000b6801d5131541007a98026425041042d60740c1e03052001946c0200031096010303042c482440080001c0405901401e0083c030400b4026003130031090402007034296000840190300c101500f010070300c0004202240b2914003c40c001c0812900841030002c01e0001e088441c0b586149014480e011580c0400001d204e40a54403c0c072140c0c0d04195107190845042d290440e1071207140000b2980f40415926a0b0443c0e500210218460000740d4a40f42d2818074028018110f40040c1036590108814150041c0e0700502c030310415070300146401134981d1426221190101542d10072000491270700f004030309c02c0c416106000c2c0d002004006904110b40087c00d03004044a04a40950a240010550303070080e002c0c1d00c084404944404401d45c966940e9000540108059040c0c039100601c40e05e40400c00400c9410010140c04c04c00289070350070110b018142071115040800185e051031800c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534817230 1250 534815980 534815993
    0x801090903120b0a0b03010909020907030c0e120c04020c07140109060c0b040c0e0a0e06070207080a0b04050319050706060f060f05130f170114071403040302010e10061d04 75
    0x42c1e214075400c400040203580c000002d1441921500105d1100602100100d00941b0075808100079034002c8035400d04c15942e0031012015038138a03000b0800002c81900d000205818105010242c0751154400d41e01184440f0f80810201e0b08205560001d5500c085400c010300340b20b82c404480541402e2800c50300045c01c1c00d4000d80002c000301c0004010f4405100044d042c0320f140e8490300d0240c00d114400310514180341c200a009000c1c2c03000401030358020700f070219460b1400026028110b901e4540a04034410b080e4443c003400381c00051058486000c00c1100540c0c0e406100300780c00e800d600c42e480d8140c50380018100101110900d4202e86010500c0250910000d900300414050400c8249010360b83c50310384814240740f018842d400051004c1101c40c0109080302024107070990715a040008001d881851032155040c04010355008010440301206c411740c0000100007941e00078040d000120b41201d900d1103452803e00c2c0d2004500329281e03100b01c00c2c801c40407001041109400c5011503400282071071b03150070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534818480 1250 534817230 534817247
    0x30605041b0203220305101a1e0d170304050f19080405090a090f0b18070b070f0c1d06010807020f1002090a03021e030f0703120804031b0f030801090903 67
    0x31a40410240341380036150b02e650100d0003441c2c0c0306040e54201c204100b0340320302070020680914030080c5502d281c811103050801d101001900d480440b0300c500c0c0c01d290140322510b2000716007611341d0040b03400d5045074100311350011401281f0801c01410395005640d0064144040701550b001010039508002020a94420039502514411035105c480c40d01d90001c428000c142c1014010581102ca4000b034040c030214501a034410b40c228500e031148000c800001030b4171800d181c0204840c4a10a004640104584100341da58262041224044043e101c10381701d03d00c0b9001e4030b42c2e400b2501c850703005c0180c0755a202002c0e50704180f85000501c41112029001c0d85c41d0340c1131074010413540780d0100702c404a5903a9650721344001e64000c2c10b80306080b8103502d0101d540d80016802d0328080e2007030142c40120420006105030031640c00c41c1c4200c5040c800d010007141d03000000342c4113030200000c00c0c080300113854a50702c520b44264482c907140048a44a8a8081c0401d10140e205403015071810190501184e00038510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534819730 1250 534818480 534818497
    0xf010509070c21050910120b030f1005041a0901020c0d081e0601270305160e010603090c1a0306010e090106021e0f2409010501120209100510030605041b0203 69
    0xb0107543d01d00081c801c5445000f07501c0143e038428a00540803458942009100e480c0300c0500c5400c0c852500c620080c199a1a080390f800d04d20382c1c1c0010100c3d641010303203034003a6070068868403040859a00003003190042040544444e0f070a43d5001421104014081100311100c00d0307507051501082c60301c0355003400303204000d2091401005042002512a030300c03401480d412860003021010300b10908514110280d4030502045449100b518103000d6107007014449181202c0d4260401400d036030074028200c0181c0540b03502154041030300c0d103000c01c0b00707500700c0f582d400300301000b420042e02c038500718000400ca034007001b0138103004603c03840c014454150f0202d0340f8203c400e41c1c0f44080c1d800440c4070040034984042e91107030812a00401c1306070400c140441020804018424503940c4d0f140c4c844220b00e0342210020b2062801c0f4840c805502c5005041c1814030742d03800485800152030300c687d00e00105540641690711000081d5413200c042c40715240610a140040107403071001501c1445800700a5600e10a1100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 534820980 1250 534819730 534819773
    0x30d06140f01030e0129090108061614093601030503041a040e0106020f0708071217270a0602070806060603060a0803040f0e010b0a0c080a0e06030f010509070c 70
    0x1840351840425046070b240d003200c0c2c8081e144840c1b43c206620b03d00f14880120107100e4000c540000903116400142180204901d1016a040480100c8165030381c0a9040049802040034801074103203541e8142c111041c010342a10011001c80710111050b800d00c1202c1d00d1940c00030000c030050003c02c0300082030340d041c1d42081280d5500c2d15003a0303641140c0760056501c1344400c59401d83c0007150040d07001c980000350118040494100985415840752076050b14040c3d090006105094040890078100c107100c040101403908900d0600c0c0c0f4145604810034410480c20400c02e00f9500958905100c24100002c1201d0f1001d85541424140c003c4e403202c0c40a80310510070f280100c0402d6142d51144034080c01803258104680d0368541d0741c0700c400880d400303c0c41000c1140090b0f038000504042000110b5100b09201d6032118441d034065950383c1d0183e001520550208003100720121711503151a00203501030703c1d0012062540791f1406e02008100200100708404101d8159a05030024448040d43f01c0c40a00440d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 534822230 1250 534820980 534820991
    0x90a0c18022203060b030d0c022e0c02120c090105210714040501060c051c121d010c020c1f02190602030403020d0219080f09060a02030d06140f0103 65
    0x8104030080d018905041041040003000c800c01d840d6041000030031240310b641c003401400c4039442011748442403115584046a1502000e400500c0d12094460b00203c3c000d40f4621040505212003d1504c500b2070490007180c1030a00400640c640411215800d0042030001c20103140c11101041c4040300c11300c1030600070f50b8400010b01040850303040d1b610040f1030241c100d6545984d01c64502e100301c0030500c52980102e10708030010413040c2c4a9800c00c00c40a401000620195880104a1040700090003401040200e04001480c85680900a44101014034810480c040e021110100d0071503800023074420656200a007148840e2f06d4155415440f54035010160b09403c0103c81c00b44c0c101203496407200c0c046030301c00072000d04024050307000d540168040c0c2d0031140d02d44c000020590752001880b64103554070520701020130000344002b00501642201904007402c00200b20702142c03454000740a001c0140e0400715900d040e84a891144000422200a5040d2032015800205001c0340e0403504da03504064450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 534823480 1250 534822230 534822269
    0x9010b040b1308031201090e01020a0804020603091005070e0310150b0717030708010815062b02060a02010c080906011208030c1c1a27040c0806090303010e090a0c 71
    0x280508000c1090b4810b4075a2405e80300103250750030a09005a902e454030b0460414424103051080d00d28103165074a850705280c4868081103c0c41d00000c120781282d200343c510102074507540d40074003406481c954031070711303004030048041504013a10024008881032602d04c2c0d888220000400329400c407280855156500c12080c2000c6004106002141c12a044000207015007a58480040c5d4100c40d01c200036a2658203420744e000281703100c1680c6903070340a80515940c070320306c68440b40680103807204450094100020340d4013003040c5421a5001101607503540002100b25600480f00d23580c8a6070340806031903a58104181c20000c86a80080900502c1000c000502c800c90701500702d0750380c0c06005015020101ca1440c0c448092304403d80c1c0c00415100d1502d001070356040425100500c80d1004c6041802c1d1020342c1451103000b00001d000b580d400f0105100002d901c4000d00c00203002c0c81c02c0001940c0c1c1c940c18401c000701c000102404c0000654000042c003400314058100d07080c10340d03203404100d191080c0c89 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 534824730 1250 534823480 534823507
    0xa03050d0e0621071e020a0201030b19050405090106090608060703060501110d14040e0a0f20031311100216050d020607061a1305190e03070305160f05010c080609010b040b 75
    0x140c3d26003c000c1175601429011240c0028a03030450030f03c01d9038240200303c03683c014030984403003c018000ca100b0308418103016034a455042242c0c400c408500001c0c8455070703949103c00b9105180c0c0b201915401070800e2110807503050213494090402802c0440c5140b2210300c402e9540c01008074540e040018001c3c9541c0100064412200141035040180101d0b041840120004216a05241c0030710b500e400f48008240090960202500000341c084c182990384e01170445002125039181111440c2d07080728030007500d03658903598603c00201540201004074103401c8031003c4800c90340000e44107640701a46800140c4c1c41d20201c921003503100c007001c038030340c80d85842201d60030020030000c940c1302c440407446809010b0f49070303c0144034960980c0300805101b00702c40020100d4078451452090398200b04400c40120340908001c2231005240c610300280d0401075268420100103202c011070f0316944071301d00da00d125030784503844542100e070842e1001d031507500d8588044498800c1e44a030400111012074080d818029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 534825980 1250 534824730 534824747
    0x3050a141204031e0201051009180206030f011e0e07030b011e110c04051509130614041104110421021002010606020601140a12110a03050d0e062107 65
    0x80c8100c01c295500309031030b01500c10a4011580b190744c802d591600c2c000b1510500a00f4040c076010507141507101c2c100050305019000c01d0102160049130402e880c2c0c01612080001d62244c410700000007500d5042c400d0780f0045070007080c050840c1c12900c920510004040c008090b8201046d402c00181901c0d6040c010f0320240142d5621160391b2a04586114440b50401c00146030b881c690380c01d5030307a0200140c041000325641038400001c0003041c3d0104000d141450064550010010350070920005280d07681d85060300e42118109600301244803d110402c00d1820024201d014116000e0000340d029000c100b40031b0095100395042c03403500f800151400741500300403215164001d03026121100c58084081d002c1c2c41d062081c600140305030000019a03c401d02089102d07034400400d4000000d24220500480c940305803000c1e1110700da07481c5001c105544c2c000350280254440c4000c0c00103648400308c0640781c0d68482110b5805004200081016242150758070405095111480385080c2c5900c081241d400d403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 534827230 1250 534825980 534825997
    0x120e0109050c0112060e070c0813060e0108010b090112050711030d021b030a0f08070905060a030f060605040807030b2205070305060c0703080601030f0b060708030406050f0403050a14 80
    0x51034400c0000c1030100200c2c4180c1c41c0038007078850310070043c0c1019030070f41101c00920400c01c6441c0b01c000455181d503c901103100c040c9000d2007200341028180c0442800c2404194001030200d803a446241d905075030001c0c0010b00424940105504000b18000040c0c0490180304038188455a598005024140644040384101c000141141d44407012101c0850003513020340156040481410800c42c040b00c4000121040310304256603824092581d00400d0705c074990054110b07018841c00c610040b80540b00d203406010180f44d151303030205143d21062040c10407614130b40c015108102c4204414080a90000780103011280d001926003002e903904480c005000ca801d01c1914107106020042c03070b040c40400983e00c42504d026000341c0c0e01c030b0b4442c0c0d040b40c4210301c5003440c02030210b000b46000a05541c000d506c03108601091000c045a041a8903001854983c4000c3e82216103503004010303c030034001a40b1031a5800244420140d03602d04150301c000d4050700441181204109001450405000c0707850251080300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 534828480 1250 534827230 534827233
    0xc0307110a091125210c0807061b0f020d05180405010b1804050618090a051c0810050d020607080c060a0f0b0a050a140406150f0207091b120e 62
    0x141025071030708550784001600f040149138600581e031540c150040c6901841e901030104103001e844040140500303240780300010300b40500301800c800841c035010020b00107148500800030b4003694090319035082801c200300c5d01041145050500040a0300040c803420b003a881030a041d615990840a4122000b0b40d043c2c50540050400340006545c0781307210007a001440c0308810702100c8500040512080702c1d02114883d9114065055003d005604d90080580212100381640d5280f4102e4641360b02c0c0c0301c200d07440314000c030114402500744039034080790381a0082c1450030b6003140223151000045640850300c0001e4410007000030348404200c0c1510480d040c4024040c1030301e00307910b85014050020296216560123260400d0603503c181d2800b800d0b0002669001040220000e05020729400e00a00a1030201c2c1c005a0f103e4010464042c141b4800030000c0c41c0e55a2540c0007000a00003e0800540da40055601414108409080080301456041c5079189182000401c154119020301500d00c9041c03100b982d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 534829730 1250 534828480 534828491
    0x12020d0b0a17071d18030706140603011a060f0c0703060e0105060f06090a0b0f0c060103300e010309020103020d09062c03030a09030302042d06050c0307110a09 70
    0x3111952000002200b00920644960b29601d182d40990301080900c03258036400d611000403000071901d02040c0640341d0700002c84c0d00700a500c1e681d890031601c4554000384540306100070021607150034019400c10040701d04c400c100b00c01c13109011800d00d0050000d19100242e001c43c2903000c5004c05c0120000070343c0c01540510400f2801e1656500034101a12110b020748840c1103400316908001c2c045507c0824050a030f096990315005d0301c03070543d41007949180140070307080010400d080d03010083c0901a5028614404540c107101040d107590341c8420850140b1804051400001c050300008120341902013070802180107402031004900a1182107400c1600034500403181040c08196803150700c10800c0502ca8178207210ba01810014000d40074041040c10f5401003001030609409a0009900c3d98400d08025081c036484e01074920420341714800604032164070000e150511b181c0a6041d200804403400e015251150545083c2d49178400e290020740340740900c805241450320340c50903040007003141c440c0c00c204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 534830980 1250 534829730 534829739
    0x20d14130b150d05150a201921060504060806160c02150a0e0a21031803080a050c1204051f1404080703020f1c02010c1401020307050c061612020d0b0a 66
    0xc00d00e105403080c80300c6d9031600b0041c081c102c4400d01c2d04a402045c000480382800d000c41c42c1003107518241114a4204940020f881c84501010003034441c2c2600403200c0030a140f4101028041260995845020154009018080d4a403103401c0101040400d500d06105428002c0c00420460440751040350382045002801e0050780e640300140c4007280c2c404880c0700d58580c3d9a04c0c46540c11030451080c00028040860b035010001e80034032914408904900004c091442d035039183c10500e50003008050000c248005500d403000a0140311003841400d44440c064205814000407900104d25001c41101c800101d50300102e08900441199003800402c281c0d841d5202d450780002516900c442c80b080380104003009103104540340c07100c1d5545503580d482c0c8007581030011503001120b280c20901805c1c2c0d1618944101c00e501444280000d5100300d102d5240d050b42ea607220071065182c81c000504050348034800a403002c070315680c4001102d60034000e01c1070240c0c4540c040ce0840c402010800c5400b40c0c030001101d030005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 534832230 1250 534830980 534831013
    0x304020d05010908120105030114070504170c0d0503091009030f0b060f09090d0f14090409080c0633030a060203071101090b011e06050301060f090801020d14130b150d05 74
    0x1b0705981d401c0d40244081c034031090b01071610705015910600810b1040c042807100026400a40c0c580d044038408803404040040007282301140600010783d002e8000007500c0c101c1d0f04041d001140055903614003800814515101c0ca5614a005100100031a0403480440e005503915550001c3c078510003405000d650510144056035001130481190205990b1441d200c001802004a0910300401406007460400d1050801000782685031048506130300a0120b1411140d041000610402d11041d5200c1d000030020110618903296190202c50b009414400450070784000c108031034a140d00200150b240e450f04001543d60100d120f840c029103602e00f01000c03003403200310800340d0b040f0750900c100000c2504800d8107891088615000380750110304104010019588a1040001600003038640001c0003515411803e003603071b000300300c02150252660380704c460f02c481c440030207500004808000c072190001c1e44c0d01c640840800030460711080480d0104542c0540321182255483c59000040c1e9120740c20385040f04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 534833480 1250 534832230 534832267
    0x6031e0a1d0307110d03020712060e1207110f0f102001090c1202040f020408010203040204150f0303030f060f1205070905040b010b0a0201060906090e0c0f060304020d05010908 77
    0xc007056481c481056024503002c41152001504041144040d109000c1032002685241100301d08502c581c201c00100c8280c2c1d5080100e203540714100c082403140c04010340902c0d1074406445d40c1c0d20000100140b01c0002d980710707102c40c4010001d9405801180c41040050302c07401c0a400c046030400a5103907038220096004c0454501c0b0661180e4110041030602001d900b203c0380071000400039451395070140105440e0420340101c191000384080380f0b090580e0814020ba0700154000d2030305a4000c03051100714a0140589815038074400b0300000350070301e48800100c1141107840b000c1c00741550358070840805442c2c2c0d040306025251030809524240c0e40d45106040180c00d0420030780703290041203c0810199a039003d0a03002c0d940000c2c60118590034035a004d200383c0c0c403034520917040d90350754840009c1c6010340d0b0081a00900b0301c03103400507918070002240303410300d0709080c1803d100c1c210500e0215055a6020190b03a0415010ba50300c99500c0e0940c0b81c0540100310411028086050218214031445401d0780074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 534834730 1250 534833480 534833501
    0x12100e0c030a15080715080c0403020307170f01020a090503060603060f16090302030d0905012615030c100909060b03221407030b04060c050a1403070e0d060911060408070506031e0a 79
    0x1044025682c000023601c007806a800001e45c150004c4404201c0415005011980003030041d05070f40c40805400c40281c2240c0c01541c2940102d00b5814040029240c05d003c0b00e9400801a070150469180140300c181d181070008041641000504100454252090000c580070f16400750803560740410f10200504068601e116160000b2042151503039500d21030701e00e181c00744400b801c0c0740b4929107814141c19012280070004c160503116280c0c48204c1c554940085d01c40d0000e441c0c94410040c0c3c2040003a00545801c0d411020317924404006001d411a091030000c40c2150f5000801d141032441c1c0d140000c680300c1020502c1885e449401e00100501070010052402035118100400145904020940b42405501d9000300460040082a40494030440055a12900c50301c1d0022002c2541d50018078800d40c880c00c15524a0750b90341500301086401070a1580b2102d01719009400c0c2031515054564449081c000d480c000c02c0d010010810100e003150401204004988aa500d28944941c0d90720040024a18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 534835980 1250 534834730 534834737
    0x8030d0c0c030c02010f0302070b04060f051303020c0d020d0c0b0a030b100c0b100f0801020c010c03050c0301121707030c0210031a0f060c010212100e0c030a15080715 73
    0x65621400740791076441c85a4161509050190603800542d02c00409506e041c080c5a0200244800900d0740c4820601c1284109800074800c04119503010459400501c06480d0203004110100441d400041021544000b250455220003283c0301017000070f50308010082048400076000b00b80b00700242c001e007100312681e99003003001d055843c00308000715031281c0303080e00800d0142c44560046802c50b03803013540c4940e5402c10881103c1d40d42c4043e0580004070b0340102100c0e5804120f00f03020704428080c55003904040c4c83e0900c400e0911034468111880188540031140d99802c20500800c014550039008249080b040f5a89900d554203001e07042203040c4200300d101d510490107000304140603102e8280151b01303c0300c2a40710b81803400700344403401080840c13503503000c0e2080c4040c03404900700340002d02e04100746217082209410000c000741c050070000c0d00502c011200c40000c1101c4800b6071000d0700e41c000010000403412007a0032094241818281d00155942d01940902246128036203107408040669a81c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 534837230 1250 534835980 534835991
    0x50a020c0a0b040b0630010908030106031505031612060b180103021305070509010c0c030c09061a0306150d1b030204170a0812070210051005090f042d0b0108030d 71
    0xc041000306c114800a49414040e48543e043c08030490b08042d03c0070200036000080e001c24180ca56041c240c100360700c0f50b00080d803104401026078040c0c80c03000c40104000e4000780300b00500c010041d10410b11502440c5040c4888a190780c06004090b006051001006060011403105010b19954004800d000683c0100b11072905003400804610605204401507a6140d00342403c110044400884907402990b00c0243c00101002003140c2c14110002481d8050b00010307010f180030340842c485110383d80c0c2c0c8019170005004124880c1c80304140084001c602c2e1103010750b5500d48904000007040b103842e01c401c0041310318400000b041e4055000f0010380c0c0d0f0a03224036440b40390780c0060350340d600d046001c020403045051261500710481040780c50740014030b13070041d100c202135000c1d50300c02120002c80b0005111a0360034002c000605115000c0c54229180000b40051486c05880d204500004161040a030382180a00071441500031109060182d602c80c21284840d6555110380d552500301e03080e4400e0407480c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 534838480 1250 534837230 534837241
    0x10203070201091517010e0702150403081302180906060906030a08070605041103031309060603020918090c031605030f150f060109050d0f1502031504050a020c0a0b040b 74
    0x903140255816503da110039401c0ca00c00c184d0441a02d0200f9090101401915469551054100b4040c01c00b4510044a07803a12110007840d2940400303a2400100b185018880426841078400e82e005114196045841109201050955404000c104c05403001503060110008020031102e0190504070744440ca1a211703081010340707608601d0340c002d0501a0400480c030014205400c120b40c410702404c00b81121320b021f20040fa0440d4880b00b030044070845c0c240403c2c0f060320018407030700000c1e0480d03140850506c1103000200d800401d41c038154540d00d0a00300002404242e04000b9040c0d21039028051700c024524210b2080c0a044082c0601442405402014041910002200d0310b42801d81c18560b041e5840e8550b00100250000d040da60401140e2100811141c65102000080621904492505000c64241140401c0c0740b4554800c4082c01001032000d0f00c400d1b0682440c40c080115400922501e581008030024071841e1520801c900498401d0400c2c05502c4850303030311440c01040f0605259460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 534839730 1250 534838480 534838483
    0x403051b040e150a0608060103030206040606230d05010608100f0f0b03030a080a1103070f120b370e0103031d130c0210110903190f06020306010c06090609020f0102 72
    0x4240402510381c000c0c1c58001001025506007504413003202000030303145494030540380c10460260020b5000d40c2c440e5051008100040c8200700081078071107044411910178501d900c200801d244a458071a128070641c1d902401000c1d440781d0003c08a07802143d0758050220050000740150502d400c0c816480c20180c070350b6440f21030040103500d81004015514203074140005a80012000e8030083d0700c580d4582c003810520320300c000154002c0d550707078442c00803e00303030403600400e030b50b902c82c00c4000010f051915510880e200d0540d0f10020070081c0395420f9143c441d100e0b007e89d284500080041003851030740f00000d18039405000041c140ea01958494004030301d03249109a48011000b90103400c2040103110306040005548444141146481680c588903445011201660b9407510201440000055841c00030300d01042000c1c15030108a04502c1003c000380c0700c009503d8800303040540071580000c00907855a114a66000505510500c2085079106038242040141070040c0708034040c040e20800c3c40201d600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 534840980 1250 534839730 534839741
    0xd0306080a0212030f0a0512070c03020703060e03090307180e0303011a090d060213050a150c060b0105090a0305010b10050313110f210601090603030215100b0403051b04 74
    0x842038020012020305034244546503003c20300f412642c2c0014007103400c02c062841c00401c0130320407030b82c2c072162109a03101c0b04103171a16002d400c83c801c2c0309010201c640000d80214100c0b003100d412075000a01e40c100901c03420304510400b1100da515004010340407034801010603610394417043d0344004100300f4a25515a50b503a1200b809100c403011080c0a000e00000c004900810345424040c1030314400391011760303c2100380d80008900481f03004200209110303500f03145610703400901e03244101c00504801d03c0c50140158161004c040c103d01d8503021103844030b074044d100b03d54034480041c100402060b40c03030600c1c078000d1154911291140700c082e26200c910354812001e5902600b0701441d040d200082d181c0c0e0b000c40c111080d07a0502c0d048485c90f94180002d98031610546c103810101c3d01191603903500303507200c9410010140c04c130001c054070307125092010a41c0000c80b012182c21000000f0f4090719400c0034016042a280c0c1702c000740c0c5000040101c20810003152410b03660721390000c43c04a40155070b007008160784 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 534842230 1250 534840980 534840989
    0x18320d0c1805011a070321020d050604180303021608130e01060309020a0504150306050c091203131208120403050d0c020c01050d23070905120303061503090102220501020d0306 77
    0x144d401841220811081009120840c840e0820b00c140060002400c1050b8040d02084c0301e2150340852040300541d41401b030158040b0f4100c60801130068071345c6a045a0b044852130213410182e0100f114500d041c2c2d030024000300c1c2900011010b45460703440c2c1544000b01201e001d45100140c420340001446030190164030701c0c803039000b0601807107503080c10f0030300c0020003158003c0f690f4845018000404a511881100d015031680c0101664131403d40d13080c410080c08003003004420740e004100212009a180010005846028940c1401da01c0d0368104000a400b99040d80c3c6802d07542c1318140801c0580000092003a074030343c0e540510016140340c07000e90700d038a13042e100c00e07000c208200f1030145030406e154050042c2045034640e024100301040304250381244100e03100400b00b609520240038910300300080c00440f0200744001c600d1850010007064078000204101e0070505004008649501c2c429010344403940180d09510403014016112520401c03990f101d51070150151200b4600d24522034010502920f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 534843480 1250 534842230 534842249
    0x204090b0403091a1c1404050f0708060c04171e03031509070f0e06040323120f180f12060f010602030c07140a03020d0305090118320d0c180501 63
    0x980d03005e4084400da4990300442007450742c4226a0400040800741140501d00400040002c090350034640c61801c0102d820148181d8010000c106048181404031020b0383c01204141ca094450311041901c0c2191000180c0303080c090010b41c031010703c80000302440c4920102080c51100350004024001d8881080d1110000182d103030403201080340c05a2100b440007000a040f0620b099a40d46491400906450303440310398210b10154030420791403c001e021f80e92080e00103400e24025500076610f206214070441640010201c400c0c260081c0d544180c03902011002803c411120001c404034261183c4d0100d0310400c0c1e00011900105026200005840821112800134070205040c00051100039000203107040c1d1110301c0590100060f2960784a5140e1180b107501c540ba2101002c100161681860b46100350080c00386840c200192004240080d0a04501c1925205040300100c104001c499a82c0180741d0014404800c071030800050034801c0e000c83d440d02c1c424200d140045007544055078030038810202c11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 534844730 1250 534843480 534843487
    0x50304020d05070f0b212502160806040302010c081302011d040204031505010503010c0e0108060d02040e030405040f020325270303020f01050c0a1103070204090b0403091a 75
    0x1030034041c0103011054050021140440c2c2c1d41c802024518055030807444016802060280005403084141401922a551941c41c20300d01000107040c03100d42c940700d0000c805000d080f040540d070300030f01c02500c03080d40c0d2007080740710940c980302120740e41c4a00780c0b800c60041d8a03002c00310f1100fa2040c003a180c0078403065588030503200c02c503800441d81842d40e07054101d0301882d800480070740c0742ea41c0d1005100031751080086181910810b0f06503811114140d014900076410400940100c950000d0b11800742c200900340300340130380c03a1400400c11a04100400030f41151401284003034552001010300110351046030b0a0120002c40d001410603404207660f0790101c42440c020741c074804006903580110090061078500310b8080024007038005a200e00404c814000c25200043c8103169062001782e60400400000b4001814140003504551003078401c141c08010441e11210589032060040740c5640d60010000c1c0040e000a00b03000c0b1040340f09560440100c4c4040c00001505e01d05000b4031400c06811a260a04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 534845980 1250 534844730 534844733
    0x80c01170a020703030608030a080708010b0a0c061e0608030904060518161107120b090a0b1b091e010801080613030305061309050703020a06020705031f111219020703050304 76
    0x42d4103c44421000d2680b40c500118030940d04102900464200340d84545040c00c10a00241c400c4030f068210b2941d01a00300074100c6d4080e0810690702c0143c0e484100080c41c0c4090281c0301040c100301140c20207560b4100350b03000420703040010180c440c0040445080006a40d030324100681d04080501d410340c07001000c40062030aa50102d00b010654000e401c0c00100211884c008078200311147d080004000300c4e0b110020123115080864a5010110034001c100c1e111072521f90141e020310041c0110707180c4480a00e10310078032600009841c1c01c0c40340907180031000420006140c00c00d48410342594006500140005825900020020700400c41c8003012a04010070382c500f10003030f1038000c001036009206204044566030035881181056401440034140c1d15081d881001103105855021404562152205102c0c1e69008200e5544845a500810440f081c1e148d8180003c1e00a034150112041004a08a0320b4012408a62031013001604100102e06008a005200300d00a500002d00015420710000d070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 534847230 1250 534845980 534846001
    0x30a02070b091c050102040f21060e070f0f0519180b06160809030c010305010501090e04020307090204061e02160b220803180d11060708090306040804080c0117 70
    0x848580301400f000140404100202040941c03100304842aa50000b0100809a4210800782c050000560144105503031154080c040720603841018140603030b02c4008000403e0b040008800505400124086032607030b800070010001658811301707000320340142400750300500ca000c001e810768485420310180500c1525020005040d16080d05400c010208541124070301482c4002903640c0c842ca040e650b8403040340c2c040c181450010510641498200001441941c2e04607880100345d58406c0000b441c031307580311300000c0e01d0480264400c2040b10302c0043c000c501c1c01d900001002d071006051074502400d0140340001c036955900d1203050354250680031003d0015601c000024003005119840c011122060001003003143c1d003007540035034810b510016030050204902c017880050001c04641080d000c00d25600c801403c45c0c1e007841d2091007400d001895000300854001a103000002c050101c41d014078251614940b10b5101d802107400f14840c0ca061045158810f105200c0221003001144a0ba0b48585403102d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 534848480 1250 534847230 534847237
    0x3031b070518150915060702010203120103030e091305030f03180114100f050f090c0d060e040213200a0c051f0c02030f03040803131209080d02030a02070b 68
    0x209560069460004003541d030004482180d255641c01d001c440d00f044881c0990412103e40520701072031080007040200d61541d845050140001c0e580542c2c0e43c4c040d440100d0030b501c52f19001070107070f1000c000044103040c2d002d180d16103407010943d0400da680d100c0e50b01c02420b4074410240207005034070030003109014020b854091a00300c05010020032000c000401c42500352050060308094500c0000e042000d0441e03600302504c010030450045078846400e00c408107441d07600c884a224046c080780c5001c40d4014007800f00311070352420280c408011254841a4044441c40280c4040e032044404500f820ba13151860310650360707000f088407a200c1c0e52044610b691030a0360841c09000080c00503444c2e214020440034404441001c00411621407845e02c100c080100703d400700d0040c10115803041c04040c0840700642e04480e002a002102e083d22503440045d0702134802c04044c002040f883e0300440c0000160307001040082501d889030192140d0107005601243c0c1c900030702c0301c00e2005a120704410084e001d95031006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 534849730 1250 534848480 534848527
    0xc141501080a0c030615081b0f0604060203040b07030c0f0510050f06010813060e0708010203061201020307021921030c0905041112041103030a1701080a080f0c071a0c0c0303090303 79
    0x81c4161169540015410301031102320f0100c9504411082114a140c083c01000ea00703202100d0803401c280c141180203640340210b008511200c0c6c0d0010702a800e25020342d00c00200381da8004015050043c892800c1900c910707410444e041214249004a049400c0c140f0305203100303080c10395034420a0342c0c0c0c42000d42e1290030100401c1d10944da86000450b00c1c1e0750240800400341440800150340c9003484018000300d034021310300030388081e44103100384010780c0d60120704002c1080c1242c0c600318960000d82004104080c114041c0780a00501c007a00d040300c40c0c0c060304000c46042a0381c0f20f40d290980e5030b106000546a06040a000e1a0401c01070349240c81100c15a00350441c4c02001c3c5504414400c42c04680b81d81d110030401804120490208603000400381307245409030100e24003030000c4042039a94407200c0c0c021503420410801001c1014240410100306001c01002680708000c954510700359807041c19449104410010f005129101c0d2003810000b00f25030308400040c00551034010130500c00d09a81c0c402c10b50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 534850980 1250 534849730 534849761
    0xc010f111e0412111206070c0506100f05360f060301060303082806030c052b03030902010c0c1707050402030112032007060f1106060d02060a0c141501080a0c0306 71
    0x1050b06440170304002c068419511f540720221041840d0620925007032004000f0100824003081c10300019400d99101000c80d801950410300c81010200da03480807000f04150b0340c80c0301c0c0301c1030311013210f10303841780451405584800b5052086071900810f05080e9400c0c0d02018006c40e4800307011450203103080100c01c40310422102000000d80d405404c2106440b62030744240c1c4d15080700078041c0000d00d8030b001058081c045542c02c485503140c00407860301c4078110f0070700040c0625640c0c030f44207015640100350f00045207500141800308030b516146c0c002048807800181c00e007107100d013100100e85030030b0604c02c8070b068136910943c180f030402690b42c04440008841040d004001c03003061414505003020402d1f42c3c040d1105031220b010024100d5801005001ca144242c0c0c030551068040c01016107610b40901e1980f5010b40b001c075911261014269691082648000d01000403242c14003488030300071a4514641d4040009917405981e904960740d90741c10300d41d01c06805003003580790800000d00180e0181c03840922501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 534852230 1250 534850980 534850999
    0xc151806111b150309030d1103010617070504080d1e0320090d05030a0c0209070c21030617070e09060105130903020a140105100506030118020c010f111e041211 70
    0x907440f84590402d45032500c090f4404600726a0800c900e004000400b41c0c1501c6a81c159803420000401d6241035100e10708003000c0100c041000d440c1b040041314050003c81d003c5a1402980c060010542541018601c5108200e01c90250140c4d11a00030140c10f50110410050580410899100b460740b129001590104450010344002346060016180b00c00d03090701d8100d03160b8800d006008400f2002000b40302044001c0440b01d00042d540446045150302e1300c80300d1040e082049005800801107a0405107034590f00f00c1e40702c4c0c20f4040028090050b82c5c00c10340340f102c0c65181e5a255a035284000e020303040d030141c00d0804001c0081d820703511160300b95000384125283c1d940241c54070b5800301131014004134141d455030100302411105c00d44d4400140001d94403a03107107614003540500104103500300c118115400041960190209401102c003142c488075040080610820001c07205903c00204400e14010004035440d07800b1404082d42d0842d000450b00303248000c400e5684204a01450808aa0056448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 534853480 1250 534852230 534852259
    0x160812250209070f1701232b03020f060114010c0f0f2d0302100f110f070c0602010203060a06032c010204080f0303160c0c151806111b 59
    0x8101c28003e8070262030303560350100c55100052244d0303105c080303207026984118010003405005c8000200c020209030300303064010031102e00048080541d2000d94001ba2810340d42c1403400c0d100d8500f075060b418481d400302c4454440004409803648024891160354003450f003031942880d4068600b405c1c17090301c030310240ea4140840741d42d0300020403507140c000c1d600440050801c89102000d046c2d900500b40465201ca2070090043e03a0080d07482c039140c18400740300340e101c0c40075550010007900000080300e404c0381102d880300185041040306d03070403000094a41c61014800000c1d4540180708581c002c00019040c01c2100e418158141d0113803044680c2c0813103035071811882d880030701110715243c020084200000350351149080d000c58a080b40b60a042c110700c1d00100288540b800c014003402003840840c3c2080c0f0b041c40c1d40c608005049c60f4455000d9420581080802121280d00142200310000000150b0304a80d407111001c440c012001450f040940e031103910340a1600c20740c220b245040e11790042402d00d170314030318 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 534854730 1250 534853480 534853489
    0x4080a090f0e0a0e0f0604200a0e0423060403031a040903030e011b05071112030c0312070e10031d010c0305011a090d141006081608122502 61
    0x40d4000140b0a1000e4207000c0143c69a000b003000c100750980080c1142c0800c00e100c13a40318500900000c04001c0c1715050340c1c001c0600403032803c1000d50024161000c06581e0310206c1c2c1c0c01c1100311000c031005900320048020882180c800d1883d220f508000400860b070b92680d06800400440c100e40c0c42c05503042ea041d14595a85005507800c151096401081c54003981805500b5944010741d49103801c01940c4040003810303408415200042c0d040345e05e0f08000c8429002088419600e001c409189010000f80107600c030340008021301002a90302e2006495543d059800c0301c8105400201c0e5510204160440d0800e5100c1d13040855003540c44603800b404030325909103460850385800c84c1e04000c252a94010031124a1469080c2d51030064244004e10b080d003810002481580c1d4844000d2240700091824100003a0800118180c000300c00020841c2039110510940e60708540f050b8002c05107004000840c4103c0d01180d06410003c0700c9081c20300b070540d02509000c08290036810f001e00648003e0304c200260f40e0f03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 534855980 1250 534854730 534854759
    0x31d03030904090807060606050408030a0e040b03070303091d0c07030302030a0605120106030303060e0907060f0918020306240d0e0f0604060b010f0f080a0b041b0207090f0b0904080a09 81
    0x800d02c03155917240710524003241621540d62044051090130320080022001c04821119420f03e10701c0e0490074408448001030003003c400c441580c162003504008410035400c0b00e00001a510701098501f00c046a40941112103c000c07aa044110001480000d0000b80a50040d40d04034440c0080482c1407a240ca000c90f2405c00003083d9528180c0d1a8801003041c10303010f100d900301602d007004130300700c01d4a40048160742e140510f102d503c0812080c5007280100070b2051b6a0340000c0c0403182e8030742c809080c24003090000380d003050b100c46105802d4071401e00a9103001210040031049040130140c10400c0940d170300e00050101607990401750142d07814000001c60140410741c8510300c0b640c4001030956184000510861070008440c050010340c0780d49800c4250805440b65101401580c027103003000182012602411544484d40f188140513100c0404242e00400c03404103584038030328104010555035402205981105900c00d402c8500c0c940800c0106540b64000c3c004085a41064901a81d4802117003a1104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 534857230 1250 534855980 534855983
    0x5131a271807090905040b040201050c19030201020901090b032404090602070516050306100b0307110a0c03030219080d0903030b0a090915090506340206041e031d0303090409 76
    0x7a110410014580180e1050081c3c214024100000c0c074180c3e865005500d00a03002034148600414040c1c01d0307120400044020043d10030202800a0700e511340070b80030303400095106001c00c40b1100d000c55601540f0040c0d922921501d032100d41d4031035031a00609200c030424500a5003090b1680d0300f03440819500d000805050b403007a40100007084400303600341c6034960941c10a0788682c020800380054403294200410a075072401510941d41c4d103078903400b901c1c00c404001c0d00301307040c3c0544d043c000c082c0101d40040c50105c038080e4090320100169002e0640780504c2c05d1200a014210901200c0010301c0c0d25440341031094803e0900041104099000030a4100340f41e0282c2081602c40c0800d904003c140c040d0364040007100c0a0502101400755141501c0c0c140040086140e5070140321040303003000b02607050307402040b00d4054039100082c2249e03009449050855058031107014107031907900440e51620343e45800c03d8155440c80f80da01c0b04e5018481441d40f070840c0e03545d41840140b102c12f07025500d80c4518030007203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 534858480 1250 534857230 534857269
    0xc040b060c0706090801050c04030f141c12111312080d06030803070e0d020901030201081005040c050a110706050702090a140c0705060a0b010206070c060207060c05131a27 75
    0x107a1a10705d0700360940c2c4004101c4242c25000380130410000352000c202075480d5a01c00c90a180380000403810900d080001072401c404da10124a80c1c00e00c1070740100c000b041400c0314140070701000011030b4100c40d06104510306140c40e1914120104000184400c8815026112700902071030b1610a65a40b000d9071b000e034000750380300758000040c4410703190450000e001d00c640075180101410450703000074900c403070140b002a06100000c40060303041606048204050300300104104030442100301d008005401c48280380010600503800800074001c0042d92400300d41c0c507503844614000460b800c0c03020f9114054400101141c0350300b4040020351841c03c2051040b80041000742e02d03030a050401d5490218060300d4081003514090241840766400700e4010f51022a60810074185090303480c2c031100904c00c290f0054a414501405600800e42c00350041c010680c40c03000a080c503984030250900105680c0b0901040a502041020554020700b4400600680c1201c0b118000d50701030740c081980710b8260043e14086 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 534859730 1250 534858480 534858497
    0x3120a09360b0d060902060903100e190807031b0f0609060f1407110c0d050c0a1d06040b15030717010801020414090c0919091406030c040b060c0706 65
    0x410181c159007004003003800703014008075050101003242c10080c00c034068451600d8411401c29500c0f4801103649485014040b03e09a51301c605040c0300411800501c0c034014040c004a42d407541c5050a0131101c100e030020071942c500302d86542c0594888594080c0e0760100c03003038480d2410200e0070003201c07601d1043c007d22000c40c0060341441c0c080e04542e801c412040c411854507600d01c4100c440041e216074407490b682002c0301741c103180f450300c145482400c152150388824810000d8041003c0444c00342c514020580f00c1c0c0e0346058403a07007084c3c0c0004001c00801c1c460300c148400076505107045c0e003160b81000c00180a0fa46120424509005e83d90b1044800e4000b1a50400149109044600d00e40d80145034030402103007032030704069050072180f84250030248201d1071400441d000c114420115000c15000401a012103d07d6001520a0440318800c421700782d40f80903043c43c400a190308649106003c014081c0c1140e484032020800100b0442c40101e8000700c3c18040c003000c103801003205101820712034031101310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 534860980 1250 534859730 534859799
    0x30307140105070306060518040f0608010b0a06020a120804030c0210020105270307111306240215130510060807051c030203070209040f0206030103060b0f03070503120a09 75
    0x2d440c0c010b400c100030185408820020380e94841c083d11410081e0426600301341300448005005080c403010741d9041d1500d0404005021041584000c48264064401050140d0b80d40c100b80c0c0c4440640740050400c0040c2202d200d080c40c03141504540c054800d0070308040b04203c940124803500001103441d00580e40d1744050008988400304d8140e4900700141c001e00304c45001d030002e6500c0780600040248074240280c126116039803080c403e11891846940c1c1002016510f0031030340c203281e2410640480052681c540d0008417480401c102100d007031199010310043c1c40703400481104e0709011600740e40500031700b84210504401070244c20000c1c0207000081c482c4500f00707401c00c201d40c0e0702900c40c400344000902440c00081d4010085e44c40841e01102c5a070180d0b81c4906000103c1700c02c03000001e41c070000000001c03040001c2d662010b04614001d940c030701c002c0c010401c141030b591310982c003030346070b0540c00390380065030112204000f401001e4a5140030400181d0314080c8211130f045080c28411822201003900380c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 534862230 1250 534860980 534860983
    0xa030605030c1020030c030a05041a030f240a060e1009030c090513060f09210206180a0f080a020d0f051c141003050712080d050406060503030714 64
    0x54181400c075059500c00c07410b40c0c009406070403940d80482c0389086010344d500c503150040c41501c1c28200058244ca6590124500060140d445030040d0360503400c609407468403102010054a00c101441d4500d40700d10b40b034002c428000c4c030800b00a010999031489081c0d144584070104014000c01c01d070348401d1045c815950400c5002c0401105200c1000031480080003c2a4400741c500120b6080e007a000031640c8840c09940c014500c1244040c2201c0d042240c4500200b081d58000907030b107401801c4290b54100c1c0d0425801c844a18800030700700503403041003c0380703110001883d00360010390144102e07580d44d1000d680701c044c0055002c0d02030700e0308203021031a0001c8076018005686042d07042d15140b81c590050406c0900180112000c0c220300707926840d0504030b200643e03401001210264590f00c5941c0ca08242699840d800701c0c0001c172983d0150300c100154111000307048107007031940100480c3c01d088160a10700f0091000030800d030b0304a5100d800004040d2003e00081c40040d010b03180c86080404d0f6409100d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 534863480 1250 534862230 534862243
    0xb060f0d052a0f240c0706021606020a12030615050418050f070e0102030d020c0d090503060c0708071722080c0d0303020a091a130e04082b020a03060503 67
    0xa203803200100c9150026503c900302590742510464400860030801108100f094000180801c034079400080c2442c210100010001c08031006542220490140b440c400d8444140601c030784005a8408030a100000d00795140252003032419140028800da90b13610b201064009050385140410760000717003400301c2d40c0900a0016420316550090000c4d045c40724802c049404000c0c405000c12031240e0000c1c41c503078402e0084800e203244107082903449000c0c0c0c1c0800c54903004050a60700114101e50000506402d000c40c090b4419080403a5050a05401d41ca4844142c0c0c44000701b11810345182c0f040c4440d104480c009841e2420041100460000a500000c0700032001600451026440048000d1a980d40c585503500b00503407603d00503803940348540c010b17508198a40c00c0141c1e0600c100912046403109540503040000c0807514980360705542b1401c1900c80c400645000d003074540200710782c140385a00010004481c0380d07441d1414a242141c0d626540498010701c5801c030009407681402c10031860104040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 534864730 1250 534863480 534863533
    0xc111605010818070b1b0706030501180509190f0803010602060601090e2503090c080d020111030c0304110a1203030207111e041808070525060c0b060f0d05 68
    0x8201802c00c100c08000c1e031301c0c00a481051180100040c510014411701000c1040c901c681d10300b103500d043d84804010b0003916090090a0110a10406c04903d001c1140203140c001c40c8032201a14200c07140b81d26a02000d11416011307038500c191380b04c2c40d80020300360714000d6009124a5018022600740b290004080c0c840c198041d180a60b035180900211150190502c900d000243c0d8100000701d8548106401504008401034000240e10100251840021070080b1804220354020010144903402441c2070340816035511000740d5003440001c00003102d0300c1303072000c859800074143c29070340369100700a40d242ca419081c01c0b0002034012034400e0030800a42c1132200e80600c101c48840c55070041c010303070145010084213103921540d21032a100d0502d15424200480042d00003034800e5071489282010b41c0d5030408480c80d24040f04943c05600b48042e07500080f4810b9604550380c024504009440f412644800588459440007018074078181c556120120040c100384601d0107840925400c840b80202d88103030456 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 534865980 1250 534864730 534864751
    0xf0303121014150d0507260a1d060408030601021f020702010e040b10030f0213090203090d030c050307051318140702031305040f02090603100311010207180c1116050108 74
    0x32401c10516643c19a502480b488400180541c0c8000d02115604480640800c1c600840400d140c00780c0000f45c4041e01c20450b502c01030000b5034005c201100100f80010311901150800da011400041d1100c0c02590460014811100b40f030822104128000c00100303a5001c043d9400150304c421541c0054287e00f071a04200e80800c80100010041003240d200e2181d42400c2503581c008003841442c00d6070603076000c070141000882c0d9030b54031168890000d510a86400760582b01d4018480b50481c0319005400f04030f0303200d40e10f807400c54480c1075080d5465040140300f4400d4000000021442c48115040760b0741d0145401400300f071620901c507021012a401030300f900300315002000310fa0785941502181004903001500c0020702c0e118000d807a04001e010303c8003913583c800000824000304585004000781a00d00403002c4c001c85882a500681ea514490310070445031600c80036410801c0112507101410200c0076061604054841c0760449060034901c25075022000c0c2c00400612440d41d0080f0040e43c0400b0515 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 534867230 1250 534865980 534865999
    0x703050c010503150105090d050f070303030b090105061b0102071208040605070809030313150c0305011a090d020d020f03100f0c030b0d0611070f230a0f020f0303121014 74
    0x881000441070341c1c039030a81031146c009001c10a0740c850000d030102154100d030964405020b0203817456100c040d42e201c01d03800a4241074aa065610b05000114101c038070042c10f80c1d107403203024204680c51034266801c9500b01d5509000c1c500200b0171908802030842015a00d450035403929184c1001103881c0545584100101c1000b00164100008100c98200711180e0064514a041d4074018010440070018810761604100c940155660160040b9060303505190000e00d58500b40148001c1500400f019540e1142d8000c070454003606040c03c0a20a0310b0000d41071f4401000e6440100e448c001a0403004402c495403001d01030851b103d240f05172540008145024440a008038000800001d41e10f40c0103000d150b0b5076215001c50320402d90480744110b90003203508018402504000c0c2d4240c000030764902c0f4008103100620210000422035010303281c0c0c0010301e045182c01d142c09010003615421701064062108002144401581008191252800300d04034070065003000c080080c4030403101000c81c01800b102 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 534868480 1250 534867230 534867241
    0x114070f03170a0e0a080f040305100603121103030406020304020d080304240c0503010b130e0c28051813140a18030210050601140406080901061e060c060b030105090703050c010503 79
    0x415130703400e0b451b04070140795210f01c96900c441e03410384116030006050344620560b5254210160b080702c0101c03805a41c1820074140081c0c820323140700304003002c0102950000c0002400046244c1e000d581c100e0700241c150300c42200507039104842070f4002c0e941a9400e2003d21500a508440810950601564550148114495a0f50207032403800107000c0d01058100103d002c81440c083c0042c1c080050465409001481c1000c0c3d0175459143d00004902003240c40c910b00401daa46014807140d1010059662041c1c81c00101c003a211040f10035044660364040400911418141c85900a007840076080800128590510250f541c080354246850300040c02404544100842d40105203c4180c9103102d42c04911030390355a0040f02d111010807240c10700200301040c08a04594052a00c1e403041ca044e0000b0000951981c5805803003415101c0300d1040f039145c3c04d100740082d03803089481d02e040b07030310811021841080c001c0001e801c1d10001c5440100c3c1d503100750801c0050046c100032040f000d0b9001e082251850410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 534869730 1250 534868480 534868483
    0x6061401120513020316081b01090603150f0b0c060114090f0411030601060507050f010b0a060c06020d0e160e04150504110a0311040e07080604020114070f03170a0e 72
    0x10014202040d40c610004011101c0c110783d09018580c0101601c40c10000c1c140d82006a40030790003400490301c50040c1400c21000414490030154805842c0d10058030700d490300c214060031144c0c440201760300c5120f100081074101000e181d00513004410300a0345402c1c4148002d031920205a01c4070080c003141d2030590000c0c2c1c58080301960402c8400706c10028036940c82c02c100311031600003056542c00d4420fa400014060f58810090a010ba01c0750003038950704428010031030b00303030342c2c00401c003540c071004000b402c00900b8050000140550710600025040c0f40043d0320302000c40300c2c8003010f154503801c900120030350150030581c00400303451482080c640c107061544541c0c01c6a00441041d4403000d03034400203d81441004414210490001080000384c42c0e00c0c0d24140034070b9002d51000d82d01590510611070030200012500c4410b540810000309020f940319001190130300343d0400c920301c11140c100450070202d524910b1403a64103000c0c0c0c07106d00b4420200c10780c3c03030740c0c0030b0004040c1c040861520070001e40e5400c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 534870980 1250 534869730 534869747
    0x30c0801031109100b07031d300709060801061d01061d0f060a1806050403030c121b0303020a230d0b12030d0e1e280c09050406061401 59
    0x40543c0c079000c0c150307584082250740c0340c00c42d0069a4030103404a1594205640035200c1c412000c3c65500c69580c0308502030a0060001d04882504050034040c01988003c112242030607084083c14000c46511503a01c0e642681180d5540c0c208841594403a002449861403640c102da800e122040e40c41200303589020700c0285100041450705130601240705503000c0c941d13251400781690344402030085544003c035100103008640400e8110710458091040000c51501880a50302201e0305902c4407007850409946200d6a011410441c6080c080d070102852121100c0d0906106214869100180d48000540d800740c0350380e007000c0070513020b1f0400b0b003105010300c5000803c1c0c0309440840b08010440300030680c00611070080500e010030700e904c808221304404845a4211070b00220180c0d09640e044940420114003004000c1c00078002c99100ca945500641e100c250100c500e0032000065003210070166446203612031b490380c00507804a440d83c044c00180324661148a004242158040c80103010000010b044181e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 534872230 1250 534870980 534871013
    0x303040f020f09010605090f01051602060d1413050c0307060c030503090705042d05070504260102070803072006190e060106030507140a0e0d140111030106030c080103 73
    0x1103810030031421900c1d90a10412a560000d180d000c2d03a60312461700400035000075600702d00c584000d064420341c0754050700860b40c0100941340c84207010b540903028441140d01400403543c080d55507100342842c080c18449403d020302c140c003407060410700700c03410302c1c80c0380c807201d9841a4403907004800c003081069000244091550341c1030901c01c6d00d0b95240301c80281002c91540c005604070b400c1900160f06641402220300c01680c5022a100d00c10110026001c01c442c8100c89940128200b0041480f0300001c1c2d1039018041c1c2a041180c0a4041d01881085c3c00e98120300011203500c08040309120b021500080e0510509859503000062200705607440d0b07079102406041050350308a000030000c2c0381c201d250001741c01407007048100e5110313580d2040010010202119600009031444c03200042d080064801c44a01d5482980c50501001f0090300704400161864400c651034a141c1d000c1340c92011080c001c501049481200b03c54483d85840703c00b90541d5050f004590400c0701d800e0060002a24600c0b2074031350340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 534873480 1250 534872230 534872243
    0x708030108150108070e0f07020c031b031011040302060f0f120f060306060a0b0306040204090e07030b0c070b0a1802030a0b070e0301020708120a02090d062004080d081f0e0a0c0809030304 82
    0x10780f08e03000260700741030341c0e41d00c8030f0b402d80510991401d4518085296462140c0300360216900d04002007080b0040351030385181100307208070400003040549404400741804c48a1408103d24044064840f2480c990005011190201c0900200300d410007034807500365481b01094001d084149016070008590414038064541c0c3c0c66400710211b54503450340d0781620043c03c003d41040100004420711345a442c04103210840301e20172080001900c80d55040e054039005548000d05800325110510740c030000c1c00c440c2400b00010b0003204030840142c1e81c00c22400c80311500483c030600e0107003044480105550230704021580668010020b0f60006480f800444600b0400e14622140b25210820840041d214030040294001d5010301d01009100c1143c0c002ca080c00100c4001411403a40080e8040d03542c0114490240700c1e03002201840d036100e006004007940078952100c46943c64589054546030040c07607400c0700400e54600d40c1046400c22040c440c42180c1001810010000d00e0500d0305940c0d21b100081005002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 534874730 1250 534873480 534873511
    0x9080a0219050d031107120507060305070302250302101b0806060d020c03040905061e040b010921140309030a021507050105153f030708030108150108070e 68
    0x1094a400c00001c06880c00600002d41080b05040090144000445901d0765000e02c0707000040c02d620a100c0308040c1a40040541025031610b41d09800a050080c40101415000c001890f1070048901004003202c44148505d0440c40060500a151062404884100c42d20b0090070058036065030b07501d44003160003868200c489a0350407002c20524062a0240404c0a0000c00d010340f8000c4080041d000340d5092680c10009981e90788100140710036000c0d40030b49240c444516201d0641043e4000020208060422000c83c643d606d40199403004101c07001c9580c142c0d0140c90508010303011002810403950040210700f0302c040100001d8945001c440024400e9000d6001442902c10080698601e20b822000821680c50804200d510458242d0801440b8100d40c000c0b064001d8030602e840c440800c014a1484812003503107070b0074a000b10191650384004d100500014000804410095029242600103028000500700840b00d1114040e080140544c101d0001032080309402c0d070400e0340c05014554120132 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 534875980 1250 534874730 534874759
    0xa1a0d050307060e07031a04150b041b080601140f0301060e01020a0f0f03090e042105160f060b1c110a0302031b0a0f121101020f1f060609080a02 64
    0xa50b2041c041e000b0003840c141100c180070081c0204025045030b006000110b006005c0c07680926000d0740840e0b00810303940c4111a0514020744a5015501245000d0000100c1346502524100490000050703940003c51540800034156440803245100c040803213401801c1501a40320140e841c0014090f40f01044955000b400c0319030310030450106560380244451500300340905000052001514040c1c000c20783c0000009010072110b12010710485c0c0003898920719180c980c5004010800c1c1c1c481d00c0040000c140061040c04600c0c503080781025200e84082000600c182c64410700381c400345051940708951001e80c030300b00c40707400c01514180e269111050302e11200200000809455094101940611810210120350780d28071030220012401119031300132041c2d0f0340c0b0003900060101d01484030f500c000342004000144240384822405c0704140141c481c038134084483c15140c80501100c02078480d00786078000514031100d110f020043c000d42e140010b119420512215581c01240600074044c1c0e0400d5150035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 534877230 1250 534875980 534875983
    0xa26090604120611041d010b0c061f080706030f061431110703120b01090501050f040e090303330f180c0c0c09060f06030a061503020d050a1a0d05 64
    0xc00d01c0c03045a00c0d03221740d250b1148550b590031421909a845032000300110305005030b50700344c46c00e04070341d200140800c6d0340c0d0020085031f400c00c1d42c10840e45001c0c02e08010694000a00104002d4041641e00040103980410341400341d80c83e6500240b21388030140b81c440100d03168643c1aa000074081c800882484144440c034141e20061900d00c0030b051460180d40c002c140f40007500400155010f41d80c2c42c190349150003414012031740f03a6000140821036078a820004e950240d00540300f841140d140540c01c140d9940c44c4000003240c1201c44581c6070b00b001040007100705940c99850085d0801d0514020101c0060400c0c402c2c03001c0440d0014415a0010211000d07541c541e501c081c02e011345001400c20a081000c003030105038002054a040d540601c189800107802d00e0b50300c0500c50b4070010729100c00708413004144070741540041d24546005444030008076000705e05500c802625039290f540180d88907041c0700140100c402c0a0300a01e004c1c1e0a0520340300c140400c0c403001a0116404407148591500300e850945d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 534878480 1250 534877230 534877241
    0x807020712080d0c14160201140d0b19061b140a030210201818040b0406050c0a0906050c1618050702070308121302030a260906041206 59
    0x4400c60305071500300400c00c18900090401da060010b424066003150304429112282a4510200c01c480244409150307140e01038104803c150060504e280e903e820f41e00018440d44c08504d00c0d07000141c507155100c81e2410b00c1902c15480c540b052015858040c00d040e00100381741c0d10f80754042c090014441018080c0013002c184851880d03600310855044681c245400307511284014007001900f45800c0b5008849030110407c0c04001071b8a1b0708080c0343c00441c40380e40d0050202d903201d1540250220840c1814490703600d507464001e502590500d001d5103403910b000070075a0301c01003800c1100c140902020400a03007003141c00c01610064207080751202010504a131400d100c0345c090a100010500d00002e40c11102641c019080315840400c0c00320750f84411003a44c5e80c4905200003400c5040030454000c2d6120b00080035070b0070094025690201c1d14064000a14150208105644000300e0604285034405c0f00b01c2451058111590607908096200000403090f002e0740c402c42d0841c030a80990720f82001110b601a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 534879730 1250 534878480 534878489
    0x609060c1821010b0f2e09080a050f0c0d0506040f02060d0c0903111503041e0602030711060601030501120204020c010f06030503070b0c0304020a0519051509011b03020d08070207 78
    0xa8a01d01500c114480c080c10780c03040e40313078000c4030807601c0c18040e4180780c100c0769000b1072029000902001040c848054030780a20b9664802c101d415600861450300038845002e21300d00034802040c2500010044604015040c01c07030902c01c40000141a0004002088841e40103402400340303000242076001240e1b86218160784811071500e0262003520303150f00140070f402940d0280c29a02007440d803030000e1020040c5010781c000010041400001c00240313680000c4a061348080d000d03040d41e804103a454406903001aa140004030300e0101031050720080802600f0741c410b101340303030601040d40351a810b400300c02d400540c0030340600d0300000d000c145080250403507400c02d0001401004000d5590074540c0e00c1b0f40242100319411000400421880d100c0b0109807401030b5001825000407500c0c0004000040c002c115807020500d448000000d62aa9001660040011080303c0182d5407403407540014942c0500309403182e0b074081d6005d513010200798009801100f2544e1406e00d80440d4880240903807420720650310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 534880980 1250 534879730 534879769
    0x5060312031006140301080601050907030e03070f1115030c07080408190201080711030a0c0f060c090f06140703030e15190c110a02100c080c0309030609060c18 70
    0x3804148080b0740300202c116101c0e036844640c0b15041c50208200c42c8000e21680d0502d43c050401030185180403400c250b0420103031b00300012801c00e4a056682140c000380c0041d64240103500c4240c007408036a00c407000b85920121000700c082410b0481303505d070340c0c0000b0300f02111068020030a0703810401950119005000001d04680c40da00321560380e0800c0b00c040c55001ca0000e8003460100e0201d43c020110301c0441982d020207141880d610080840300c0144840e001c2d1500740c004604200070411038880da150002c0a80c0ea06d1040900f00f580302c3d694a16142d00100410541d030708030018034090142540d00180d0304d40390100384c0f01e1a03c60600d1800c0211802d01e1598017010060000758184000a0704004451090510001090071016501e8100c110f40303007007041d08000c0c3c0d00f00c0189031144103100c9411040c02c00070080e00580d00c8100c0103400c180103000c4141d00c00070f0a9001d510302000f409502809080090074249031180d4208598000c110322111b03800c0c9040903000040c0c5e280d00511244145280 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 534882230 1250 534880980 534880987
    0x90c14030f0106200d0c03090918050d0c0203030d051b0301080a26030a0f020c0102040f09150b0f0c010b12010903030e03131e1e0807060512060405060312 68
    0x41800d01c41d0420300c18040400c1c01c180e00b051214200661264070383e24103001800100444001c141e4443c0d1190104900f001000d00c1c0c0803802d1030b250711620728544201c2000542d132198a24001d85801210815031051018030307a11040147e44c000f0440b40c1d071500000700400d0700c0c2c07900002070258511900c903900c8001c0000c00080740c0080005015103410740903199484c40701a407a076413a00c0312620200280d688070810400200b203d01d80f0341101d4a001100c0d03000501e0840510b0403a400c98011741c11000c401581c64104200036400b90041031691400c2d8080110070741d04d0040f03008994890702c0c40c521441840032810600d03901080d80450444080608040e041110301618140284910102240403d1500408160302d0070000300795007143d2070424441d40e07120b080048410301410140380101045001c00404684a110180c40c3c2c0039824080c4100c03c60b141c02c0030101c50a101c0300c5e4010b281001002c0c0502d5080c6581f41040070b4001c0000e450014141c0c4445000c46d080a540c03240c5504140c8001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 534883480 1250 534882230 534882241
    0x20d110601212d061b0503010506160c06020f010e071518030b07053006040b0411040b0406020717070e131b180e0703020f0105041203050319090c090c1403 68
    0x41d04941040c84c0b04600403c2000b061440940300d4450058140001903002d00041c0201e0400000510010903401000036003c10203969104a02c07a40e90020001a084107002454909090180b000d40c404050041e021180c10484d481d0903d8101018900c2000040c08502e42c0402c0340386030160265810402107182403408102c0030b030141e400726981d034540071300f01c03602c0854185580640558003034039a043d01905841d070350104806800040c41d89580180c0d144e4003250340b0079208000300001e10500e00781d1b85c1c0300d0789000806402e000c1c442e4408448403001207110801e040010074448251a02040d03030280a0b265100f20300040724101d5030040007602c130003400820f02030b025a51030302180e0384004078513446070800c100c00c1d041d40c480c5400c01d01c6643c44040c0500043ca40b0300d2101100c907506240880c1410b07554200d0a101070108981900800c03070000038015414988090401261403000c8140010f00e910341c0d440d118842940305240c203441c0d450b14446545807007086108803400c400d4102540b2400d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 534884730 1250 534883480 534883553
    0x2303040801090309090c0807110f0303130b0601080c04030204110421050601050f060f090402070f140601061e120e010603030806210d0e1302030106020d11060121 71
    0x4000e01903004c540442000079240d1101c0c011280c07803460039968803410b42c4521105440701c0342805010303802401441d4030340292220400c0a14841c0603c0002704020b4a05130818000c80301d0043c01d22410016450308001058803008200e41c1100e6054400140c02040d218400340381c2c0c01540c200b415844a842d4160f1903042d0500e0f8055510741c0288161200c40c3da81d041040f19070b100800c6140d800502c1400389400f18030a80000c1d0100c410060409850000c440c2d807542d0b00580c040c0403c5494514440d10078501c04001c000c2075014000906041043d10350716000281c403292003803640740400031100c0c2c1c24055803020b90405a0000040c0e0000d001d810f80307d1401404803c005c84115001781408440380b007000f82804251280916054090403c6100d0502d0458a405018580c59040200949600d1450303901e84000d40c0203201a03406002c199281a2004025124000304903171641c0c002c20062103280705460420b43c1451007a042520341300c001c1d2400400301040900c444982100554a20214101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 534885980 1250 534884730 534884741
    0x1b0b0418060e011d0c09030d0e040f062402070b0304020f010903080c01510e040b06030c090c091c0b07020607090b07050c0607080d050103050304140109030f2303040801 74
    0x10541213035203551650380745440703809501a031942c10b40c0290448040c0501404d2080000400508041452103145001038107541441d402540808a030700f6070000c48a8422ba42020064254400341580f41c0c60040c9411040c0009080070707104081c182a2001c207a0b01030700c0000d005540c481c40d59500c420112250034020b0000b000b0b00d088a908088020004d101014101500e162941c00f244440e0300652506103030071400e803e044a00071242c2440416964013071441113210318452606002c031480c000f03044c14140b10000d50381a015949035402c1c418101d07132800c107071420542c0c2541d4082c00d1401003401e10b03800b948180000b5040003003d0040c0042c0710340c0070428501c104103d0300c49400f61541c401d0040c3c8a40315024000c0c201350002121001d1078a0310704018070341e140c054402d07181402070030f1049070110750f401e9104a6083c0d00000f4204106018880e00981003082401d003040054550349990044003120714004212021410000501314254588007144a200400b1240c44c0e0781c40c0c1041070300824 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534887230 1250 534885980 534886019
    0xf03130501140c1015170d210510060e090f150105041205070f080d05180d051005090d09182403110a0b0406021c210203041b0b0418060e01 61
    0x101c90001040c800d40c8486c07040f80800c0403000800410000d00380c100c2e110040621072003130000c601c0100e0396503c201170064034082e66a2102c0c80c1030607850034001410350ac3c0310007149070040700248104207002001100f010741c00401040800119114031004035071a1203150440c00032402c140c1c1020090010014030581a2100b18241002e0344d0b86a807800c951700c510041c504030018004002e408c000c600d03581d541e000844405000c42d08000600c0c1d6a190a04204594820b0515500c004100791402c042081160240803800c2c880d050505000d00c15041c1d03040304458490b020740301c001c0c2e03c0030240e01c229101211b404007000d42e06880d4492030710781ca03001c3d800004184244e580243c04a000c02c1c0304011a41210615001424900d118090000c0f8601000d01c45805200034800000c181039055130501c040d03124020350050380c030311381842c3c9454500f1240c1c0500c1d541e000c0c4401c4c01e20502252000300c80a0f1031030000b05803041d84584d00d03520045d00d540d8102010b41c0301207200020300c07540700c0b1340f829508a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 534888480 1250 534887230 534887261
    0x30c111f0621060e0102040b07030e010306180c030b0405010b070b090a0206031305010506060f0702010c0317091621081303020d0f0506130c0b0c0313060f020f03130501140c10 77
    0x1380e402194034242c2c011805210b228190401c00280024003070b004c070031185507042c10b0100d80b0a580d801441e500440c50300d054001d0179214103a03105019814072500c13654201c100c0b0208665410600710040b5030047e02c40003020f000078640841d191140400c032504100e42c0c0200712641e03a00e40714008485109440704220342c1c0c0d42c01c000203c1d002c1e00e40901070311905041c0d0201076041c00d00c0d94004641c5071600d68025010300051901d00b50380491107140542c400c5000b0f90007819158a08000203440140c00d0f03010b2035590b0896480c0150031182040c1025219801c84411607c40c4241100441810119800254440450810b540401000f1404064034501070010742d80d480e40c800e219800b6071905403e004014100280c0240b01d88800032026140c2100050100d07400c01c0d16480e55001d803c5c689800210202d4100426480c04950400144094000c0b80c001b850424201c0341d110016901e95002c0c2030f040c05549c0301c1d50b248001e609003c0c4c4811288140071104842e03206420a07004000320110101071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 534889730 1250 534888480 534888491
    0x93409150e0306010909081206060c060906010f0501050c100203340906031b110a0204090501050906181f0b04020a091703040501082706070807030c111f062106 70
    0x31700300c4520074845099004910320b0700d4407078015403400f04a40018407a5900160511000d01120020801584240700113401800e055040080343c0008421a0340020704003d400c102440c0084c5010422070008010418096165200c076a1010306130520420084116080c12840e80200b080c0001d580202c44107644681202a480b20360032030a54810b0360705040e6481041c1c42c03802e107042c815540442074991240641e07000643c01d60014080d1411b00c14180d403103a44070390074004109828440941c00002841c901104686500c80058980c4009401c4056000c8104520340e254a29904036091b2050010402c44d271b10701502c80c000d0303c00d0000740215242a5400c1d81d403200d41c9107000044030142e40c4161108026651303168045170140750b070386041006420071048125060401003104a000e48480d4403911014a440030303004045801d1140072604229521111034102000030a40c0c2c0010824200380b200750140380400f11015107100e85c05800e41c2c603041203100c1e200c10504064800224442d4505000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 534890980 1250 534889730 534889739
    0xc05130c170402030a0f03050d140610110601030b0702030d0c12050a180609080c011815050f042a08030a0e03030a0906180f03060506093409150e030601 67
    0x52501242d00a4065021a213918049143d40c40c01c8040903119240c094a000b200210b2001602d40040280384030700d1100f03080c4802c1345011a883d014203032191070094041400e045295650381d034184409031580c0c2c0741c140411b2006200307004546155034034000174810b4160910b80240900b07100c2440c07584052506020420700c2805010340f0f171204900c0810300ca44811142c48402c01410070840440d2240300400400fa0301c00000c8c05820f0880c240040d00904c2d800c054148084404055020f00881924201c100500071030680c01203a00309800400800850044c001c45503495414040d88841018100b403001800490000050040300b005907030f13944408050605042d034a000c1e00c40c064001c5030388440203200386132281965100304030750698650700b03e55030f5840e2440c504841e600309480035502c802c200031050402c40c1074140c000c80c403a0030069582030203804217510041c0114000d141c9004031804a0205407084d07007524040c1100580ca480140030050016090482848407540030b4004c5000001d07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 534892086 1106 534890980 534891017
    0x10602060a11042c0109060b0403170d0e011a0103051915030f06050a0e060603060a0e012c010608030c07060c0c032012010e0c09040c05130c 62
    0x26420306040e0304c8441881d00c140c108101d030303904100d0100f00c10403200080340c04580e046022039081d84101d640c402c0e824410341d4180712615040042c103000b9100198002c84115000e05e046403040c0705d1180055068031800c481041c441800300c02e01e241e007504a6084058001c9241d00c00c1d0115540341e80e5011111251644103030341d11a5110200110880e030f038824407a0945229000f0000f0746004000030f070341c42c4001009004130075150741c101e010901c025000451012910045007254041c24156030040c00500c5007a83c1c2190700304000062803003000300c03c94401c0038054000d488000c2c2408401e8906c0d41181b1000c69980c404444000007060f92007246da03034103054a0070384d51350100c1200d00b003004444103a008a19170340d1400400d04010440006c2400c5200310503501d80c0055940c0d414107048003943e9501a60304215103000703681c0700d00d04940c441403c01c00b040d02c0d1849001c02d0051100c = true := by decide +kernel

theorem cover : BRFrame.Cov 534712230 534892086 := by
  have h0 := BRFrame.cov_init 534712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 534712230 ≤ n) (h2 : n < 534892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
