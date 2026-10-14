-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2424
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:34.705966+00:00
-- url     : https://prove2.me/submissions/0780ff1b-9b46-451b-b697-7576c89ed77e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435791366 ≤ n < 435971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435792616 1250 435791366 435791423
    0x203042705010512060402040c05040e040804030c0b0a021903050f1c06060f2109121e110a03030b0114072009090604030c030c08120a06050312180d0609 67
    0x12210603004c0108010251380700e400080000384555078540011030803501600a5401400d8403e8855046180a2503c0343d003d9120f4042aa810504100001404841081221450402c80d40506051610b4103844500460744038811018803c0a0003160042007a440207014484141e01640d00a8800485404221800b6030041801c00c41400301e640d80d8542c00c000c1c0c03640017625403912404003024092288000b0042401d0003080600003881c0005140d47c0070200220b040d800e4049031075003960408058840090f09040301100360820785600010900a0740602000303001810980304100051826071481c1e48815030031074000a0b524640c00d001c0b0901c004200d4190300541da111910700701520525a07803030340107000400b000464071400003054441d5021410040d80141c4051b12505004040052528100c03050a4000d1610500040b2445c0000d0000d840c180704035206031400d00007440ca4045105250700c0b181e0000e04030528400018014800c92209074081c41907416036201e034280070507214800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435793866 1250 435792616 435792619
    0x13030822090c2a1202060702150f0a020304140d170a050c07200603190c0905060a1d0a0801091b0b040509040f0c2c01030803010506030702030427050105 67
    0x8041d00c00402075000340c801c0c1102c03c0c452601c11800d40b105904a4603400c8108002071041c02207012042d2401d0f0001307615406007016400340d402c40043c0040300690702c0c3c0201ca82c401200b941201103480e9104c50b078011900180200521080c40c08542e40040ca03000300f420107003000881d0002c01c10301104041039a00c1d0400361603001070086e82440c030901c600c1400b0300c0030041c0404d1140007a24145844e44100316115540180030b0301d4403441c0019a1204e5121144110701c8c0060400380203004442c030901c11642a00d000921507414000c05443c200c4038440700010f01c003680010280030300000d0390f42c905030700d0003020b844e40042480516843c2100d40c6c1c00610149a41003a42c4070741c00e008200b2043c043c2d0301030760016a445203190b035442c103180c2615181800c02400c4c000502d1000300e00d110006080040c092072104590442980003030341d040300c841c000d2002520402301440140b0142c5000401980c104040c0e10440342040d0300c440c40032500a030100b0384a01095021801c0e21a03a049a01845004000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435795116 1250 435793866 435793871
    0x21120606051602040b0a0305072c071e03240f0608041e030c080309010911190909030e060a03020307030b040e100b12240c030105030706051303082209 66
    0x41c000c2c000b07918006002002807140d5110800107540e0745504003000029600030303013150a007665406811080103141c203070303090b100082d80e000d40700301d407100070800742c040c0d05c4c10380d40c00d42034109998a1b40b403c84e880001c3c050405440d0401e4201c0716889035410780b6000300c0b40b0382d01d0407861701e4408420300720102a4000424082c84030100400f140210030049000304d04a11a49103002c954074080728044009500103003000000b02c20301840b9a015806008010b2145807410608038995041001c000050300d85030101d42d4505074103000b01d80581c1c01408455100b800d013408550b442c600003401c917400c010140f100081e03002c010007140c264035004d0f0521540b010b4a0401000510002858a03607882c020500310190b00c030b5a24004a85400d000c5900c99461601901c104041070720354480800322141d0300c80070005964010030b081d43d484078105e81c101e0354000c0041090070b190141c140c42503001410002880303501580000702141d0b92034000c00071060f8800d0341d01158544804600c52103006604948181407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435796366 1250 435795116 435795127
    0xf01050912070302011b05070203010608030f07060f0216151506050a1805150c010b060301121205090d0309061106091b0a030204091214030f0c072112060605 69
    0x714650007594180c1c10341d90750b07506490074242d014007107a03401d94856004801d038004e1000d510001624165108800a00600b0b654100c02035580c0140a030540c0c0d40d240811001000480c0d42d848141018150030000d410300e040b2000641c079040c0030100031386521490a41180164855110b0345540c1c2800d110001003550501c00010318501070030215038144211826001c0450004003d01c800a1200030f15000126001c40050003280d00b00c3c510098641d0300749101c1d5122440c0c038400f603074161001c0c0300d0035400d07480c00c80d1541c60541001e0b1194500748802003180480c191159003010242a0007034460030705c43e515103d40100301100a05084a1a41014051040341e00c404200441802500d101c205240c0c980300740040e030001e40c0f40e030000f0f5000d80380c012070104001c000ba03600c141140d41501ca181c0286000468801039100031140c2c1d80034289401c001031a80c0700da54010300b40c1c03140504035220b080c0a12003121450340501507208400b00e8038024920305000400c1c0603180c0609032902c0c046d800c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435797616 1250 435796366 435796381
    0x903080f07024201031b090b062b06120c0e090604030e030c0d05100c090b0306040c050c2d03040509040f030216090e0d141e09060a110f0105 62
    0xd100700031000051070341e64101c80007a0f02200d0412003082d1001c12078030907036581d07030700c1d0500d0710758a00e8410340c01801c21ba105c001b4408496215046070140d0140900d480d1108440429039481c031003410310303120418100421002c1c4c21542c422940603284000104c6220040e40c1000743c09040d03da0f000d0b200c0c0c220720604014440c18045a0150050752506001c0300003402c2d800040d08110130740801e9500183c2160040e410f1143c0002c0442c0c080200d034004000038288200200ca05400078068140820000c00c04625107003003560000049041c00d02d0104c3c01d241e0050402402c00c24104112001c080385210115000590318a105450407000c800462070300d413525000c1383e04020300505c0940200718000400382070500034000014900c2995510200d07054076400120000c110750250600103101d40066805402e00540b000c1450388072450006080004803220050100c4454119003401e15084c4255030180e220326001d444004040c0c1c4949d92425070071307401d051525020300d1851041b68180000d00c444c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435798866 1250 435797616 435797653
    0xf0f01060608012c04081c05150d0506010b1e04090b04060918061e050106080906010509040c05130b0907050726040b0a02010213030803010321050d15030203010903080f0702 76
    0x1100c2000d00704d002503900d50030318803054040d501209031310150b81401082c1741a41039001521421b010800800715007000340901c246520640c0005202d5031000c4014810961003001400d01c145101c2d40010a2419007994014950059800464181c0e110003a8040516040c02817002820804208215000803145060210070b00110043e041d940e40c0e44134080d02102c4003444112b250100301d03040c0a60b50752404000e0500d07904880040b000d0142e03900125440c030386868080d0080d908060304281da58200010042076418a8451300c184aa55010880b910b4072905030051088030140c440d152501682d05003441040c2440c004107100000b44104040003910745400d8900b5076040703403001601c40504800982c0203105842e150201340c008007000008011107000158140c80c0714000000544d11f40300e0040001c0d076251000d450204030305021850301619180d20901c0486c0b240142001d600d03aa039000f080c02c4501c199410780029601c6000c0003055044910780c40e821030128030081180d546440c611070074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435800116 1250 435798866 435798929
    0xe01021b01090f0e0412030902300d12060b0c0d08060a09021303150c020703030e13020309030301080c150901180e130201030617120304050f0f0106060801 68
    0x300c50310300c00d00240e6446421494050250314681d846015140d440200f209035044408031080f05600b45c1201102e07202e0b004d48500c86502407c0c0d0319811a1112100c08440440d01421441801c040c0003050118001c0003003010720103454803020404c004000102c42901c095030800c0c0390402042064100780c071400502144e0b81102850300000c59180d43c000a040c00045a000100d00f6001080150700ba020700c0f0800003c9074410380400810759500501241916200c0080c1000358101001c00c2010034003d8420500d0500c0c008c002d5a844111107140030100d810660b007e25503548080014030110740c081004507118601150300c1c46c84085046100041442981c030300504004139903c4d05001458054a040080c003d103c1e040e690900d00100c004544c205603041c2a80001e08245002034400c3e00c40d190783e14424101d038041c4c007801d92150700c10f104030761010b0000c882d00d10038104895032009040c02701d004955800e00001c1303400c5181580c01446904182c1266488102481d504180c03200032644408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435801366 1250 435800116 435800143
    0xb01020c0a0303021b0a0510021f1103131506082805060c1e0a03090c051c080f0c060f0405060708010509070e0a03021011010e030f030705030907051008040b06010e0102 74
    0xc1c240c800e03d00441c02803031095000346e0b0008e00301c034078410740c00d60081640e4118407506981d4006c0c0c0084d0b541444140d444000e02500e140c6403c0000c90700301c079000b1440c1890980a400d492800843d20010701c2c044802c6644001c10320340080b0303800450204014040b0f041d00c081191003a41c503075025190300762162002b924003020307408001003074820000060551500c003403401d038005440301440b41c0301902070b02e00038104071141c0700f4145021440e46403a0203241032840c0d40008800943d26965100022030b40110303204072050100344a080c0d00048108055481403680741e5042080d170516183ca24a4882e001d002c0500f400000c40052103603441e40030040340c1c4184903241640107041c01a0100303244d003a0355080031390840380c403842540f10f880c1c11030751000c0c44150010003044800c00e07081185450380070303814800c50403420030004030364242d205101841d0000c0d000000e840800d5035038400505202c210003014000b0030030260400050150304095594044000e003030507610f0a240c40f0000707484101d1441d216 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435802616 1250 435801366 435801403
    0x42105031b0a0c0306020c011b0503070c11030d0f020d020307020913030309050706030b12120a0c080d090605040b060f10030c200c030c100801030b06060c100b01020c0a030302 77
    0x4404400100301840c6015002900425001c4c0c403810004042e500000040c9419070030076121003441d1074561503805c0502000d0745c601d42991503800f0211040150404241d03154012002c0e8038480c0e80c0d003401958584400303031b140c2c0c00601d107500d1800390a12180600c1d44007590014030100003d6162440c485510041e02100f0b8205400035190540080a4454014110b40f00700a17011810701c3e0140e07c0048184c40496490440b002c54412055843c490303400410480e110622224254030f010b55a4240c90b113108681060030314104040100c00c03203007e44000d803036003034645051100380081c214145400c54010380d10f039584500361790003140c00080320b074941604256981d400c01014a11444143c071103c8210031005080040c3c0140d25a0344000c1e29124a00c80d000c0e1404000c0c8500d8082d074111500c50003911003e81c0c60786191500074900100030f0503d03402150800c005408c141c000e0103001400360403d48006142000c0c82e00082c90b2041400d00f150107051013a00500120ba00010001100304105070300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435803866 1250 435802616 435802657
    0x1c031518150b032d07020a0b060a0b0405040c03020403140109020f060307080601081005032407030506010813060f14180105090c1903050f0304080f031303060f09080d0204210503 78
    0x41520515054031074400204e42038140030201da400b0a4003d103aa0160800c071070300ba16a03004021404190b4840c8040c0030390100401c00550400e500702c0003000215040040c203056076038a420703a172540c541d802c80c0c1a5075500d400f83e0f4218070740490080f0014106540160851804050250404070040e101c079050198800005c2d039150019402c4102030301e8040c041d240c2040301d21202007c48203580c1c140000c2d10038a034001440c464801d1003640d2003254144c0d61407503607032610301e80f0b82d0307481c81010004c0da4075980b24255907410203550b018410843c59002c0700c200140c070740f5106001142c2080b45981c0e00356410300d820f1001c040f1001848915141084401e8000c180c045440b5007407112180d4001032a502504007003401000021000d00304541ca903400b6184510b441061180d00c81c441c44019a05201101c03030140003048903a800304100c540c0c8080e00080522403a15030b40c1840d0841c2c80c60f2045030380c00181c14005a01e18414904010310086080e09001100e80e4030f460301e80c042c441c1204290380351246c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435805116 1250 435803866 435803911
    0x90a0c0303121d030405090c03040506072015190e030a0e040912030504030801080123090102120c0c10060e0103080c0307061523031c031518150b03 65
    0x440ca580501d80c0c240f00c1403400310010680700e81140c80340a110b031000000103102d003020381c400c803441180d201005d002e05903070340d802c240c030b051440d004c0680f83c00b0030300d54916921140400c00844501d0080d50801a40c0c500702501c00b061066402d40400c1c0a42824a440181400041511702104107801d1050014000350003043c010300080d40d01820b80705502408402c010b8042e40598015800b941d40c0d00c01583c1c803201c0040c207032220860f18440c40d9001c0d1920307024003091002140e41000303e0400143c600103418400c0c412101040c9c03001e0b61a0b010004a02c0f401550400a11101c51700c1040700f07000c1075240410282090005200c0a825881e00181141d0440400d00032a00007940c040010800c9000400d4194503402d064090450380400740c03034a003102c20151480344180304500500501d100d8401e0b65080001d6a101072265051684074a905ca050007001c0d02e4007009002008650003026103408ec0e06401c0d11864814044400c0c107184081c00303c0302070801100d40c041e24007885010340701000344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435806366 1250 435805116 435805121
    0x52409013806030a020901030501120b070302070828110d0c0807170d1a010509060a110c0a030f050105060109050d0f0c0e042f1c020319120305090a0c030312 69
    0x40c40d40d911400010410001c61391540c00341c02e0700d0070203070303420066603032540700c0191022015100a414250200c2c00555801e12940080c4084e81c0301d24043c1d402e12640c103202012482e603c140003103812841c070300c0c203001c0290b0104270b030b1003035180e204001c081070500c1030030241458801c003030050200500001c015051101950f40913161139045241c05985100d2010f4240003865200d5031014800d0b0380403590440c0b58412015a413510200400b420300e001c41ca0074007522403640c3d81c0c07034013000b6001d1010705005907076420007024011809030206021203241e500e0074608591300100714070f0500175000c0d410700c0715031910102484400e911190306500d5800070300306510007065961010340d404902e0740400040041c401480c9002140b00f18902d0600c000f40200c00c58008981e5001681291040050144160030041c1c4801c0c101e0003c0c00703803a841c0e04132402a90340500360344c03415299030010b4801d10b94069450310842d64010850001790009441e15079640e0341980241c40050208504054050728484080c0e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435807616 1250 435806366 435806471
    0x152f030414070b191e120e010509100b04090506060613091b030e070b1c1d061b04030b0403110c041a130e0a0f0f05240901 54
    0x40441e9040782e036840b80f04000d6800f0001c8103403080980c0a4403510103008100c03079802c03481e060b0349004003500001c10031140401c03110702c130a20840d01da90f600c0c0c03201c50080c85024010000440608544202001c21b20107561600090a0150b450440c100e8089540800d440d50000c000301c2d05156524207861086804890036000807a40034030340303036088100f900c801c40031407202e8000d030701e00348411818001255100d091506c070b01c4802c520304012000030844001c1c14114130f20311003080001e600b001c608030390241d030216542c48440e44c4e02c14414018684000260309000d407038541c02c0e003443c060860744c8580800c240a00001c0603c800c0100c50010300d84144580c14400501403c1000894142c1c0c0050040070382c148001405642c0c40d504851442c0d6950050b1000b0340c00c80c070014034000c0c6907035948000d0070780d00c10b0003510664010105800021414421720f1a048204440d6401c000020100920038407400391004100d47c0c54109111a01d000c0c44100d82c042c1d00008200c3e814816000c2c031940d4a04018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435808866 1250 435807616 435807653
    0x51516050f0303100b16080a020102070501020d02040905012301030b0a150309111c02090405010b0d0501021c0b1f180906170c030a0b06011803152f0304 67
    0x1112108240020000082c610952414091040c419514100c5c800280708200004180c0e05c00014a0400b10780500300a2010300010300c0010315005c0e980d11618220b13000074400c50300c0309030002000c102c201d0305805264007500d05c0700301089540c543d40c800d013841009260411410715403036151161455136401c114800038184409817114087d0002c030001c0091081d0b06046071a040c2585010442c1d05189204d04a1388130001e15060b261760050f000c01c28400c100a100702c44643d20f80401d00f41c41d40340d07400000703140c0d84203400143e10b590120155500748130015210b03686091030a4a403040d641d4070f00c800300b2120007071514032880c12565050112200c8440a55600503811010740c00240c2143c9075215000f02c5180306042c1042d07040a48896441d80c480000c22549075000c85030b4200481e10004031550000414140400c4070301c520f203401060707040568825070710181c400064411000180c014041c0c01d03100365041041201585d81828403281d0001d00503c0f800c03030040005401c001020040513906e119 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435810116 1250 435808866 435808873
    0x111060a320403120c0e0405041511040e0603280309030605090d0e0f09070503090102090d0f02100c0c14120304090e0706020109050304050f01050d0e030901170105151605 75
    0x603040078021144806460840008588a2215902d11620320801100c505203944124407444c07090108006400064401e940410701e5810102c880d555074840e07071400801c0401c1c10341e15185040c3c0d8909125070020110740c040d03005070018011517580480c0c0b4000350b000f0001450401040d80c00c0480d400200c6400081c0f030b040c81c2400384242e00800281c01030034504143c0d00d00d902c410810b02031080c0000c010f00810f400c10341039030111341a00d0080f8060340d03010946000040c1001340f0100011002c150180046d01c281000c588801c00358140401d0036a070240036401c0c514050141955210b180e5140351180c500c45030010090301000340c0d00c82c861001c0d0884c0035030460b070716507443d82c403071f0001014008046542807040540005505006001c0d07a04010740040165090516010030b10154642c4401034904014080040080409161007400007242d8020700071230702c40c82e05600240241c0c000c49506400c1049880041010740e0b9084d0b400c1d03079500d60704c7c03010544078a0760000c0040b0380030302003600800501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435811366 1250 435810116 435810191
    0x303180b0c09040b0604050306060120072909180a0f020403140d0c03121e05160210060807120c0e0903070b0612061512030c06010f050111060a 63
    0x16280d8064072240d034084400f0490380d20300344c041041d0b5100f544509601500070700c0000d40703a58068071400c07041444501d4104400e00101c0116414520140c00c2488070341040a07044448004461039980001c180c14803a52401060b0400070345150090020034284115241c00603404414680090341744401040c2706544454403481d001c941d6510700390060a0b40c2c825405d01d102814880d40c140300860f6003507181c049400030205082c902800501c44511180705403c0400e51612009210309c0d4401c01c20a109841c1d2100241d034005c0c00c20040b0012190201e08010040c80103003c04100b81e8200d806068412401e214240380c840b6040c00c446d0700290b000c5522504214507901d011000341081e81c07094000781d202d5a0f9070f03400c000c41054001c404080907408000091041550214a00c0301a100240284003012040c0d11103880c42d03101041910b201c0e0004401000f900c0c41091000b00981701c2401c21041a401031401c40d555400c1c01484968a00c0d01c0d41565190340c500100008420910301c0011100c03607 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435812616 1250 435811366 435811381
    0x1407090204090218030a150203040618080a02070b0a090608220807062405061605010e0a020f06030f0606070c03080a03050f0907061d120115030c060e0d0303180b 71
    0x1e4100d602084c840d80101c0c2e82c050101c0c034001c40c0491039240d100b119141001e03008841c520003508001e004451850340d5521103c60010700107034131880540700f4801180d4650006034000d0406055a12a1000c803005001c99003131070342c01c21794000980d080c515000c0a580e4a410450390048a018070460310346007224103501c20321155100415400c2d008078001d20110420000d00891550f00c25030320341720134040030020f0049140c1000100084441902111107484c0142c480c075007102c40c1c0c00c1c0f211080c1d82c0940c01400450a103d1301c0c0d1000013200700c41250461500c04200e2102d0311004281611503440017802d0000c02c628550700c0d02c081d5811113003560700c0b0344440d0b038058000c020540c0c0d03a500d5030903070f0700c000f414444000600405444840d47d9505145a100465588030621240728a0340300a401181d52034000c800d10440d010014100300c41c0c09518035504000c0f10980d6950401c9080203505414100030f51100d1000300300c22903052030005850010000741c105002780ba031030014810b403450b2040c000d5030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435813866 1250 435812616 435812621
    0x30c0c0803071b2301020c04060801021309151403030f0304080a09170c131e1a0a06083c07270317070b04030f02010b041107140709020409 61
    0xb6842114881011040d01000c103211001521550801c013000c441901d04040c00484e036812043c00600403600341564180c00182505e4064000f05c07026940420340c81038030b00450406000400a4140400000404a400d8030604c0158026015000c040c5601d21915403000c0048880c0704208400c095100d05003450300314032a502c502006e00010f40000c1001c600ca48440680e09616100c82004041c003505440a000540c1306034281908801c3c1c0d03650340b02800d12007001c0c01105c0c0b45400d42000503100b031300c02d220f684400408200903000301d203001d83c24081c6503003015895400a00e113810301003a96060700300d080609002640d052402d40075440c0752544e020948075401d400340c12591101c6000070384020780c0040c1d20700d40c000811403422040e4010800303d80344811404044014410322494a0490740f1551904941902e080300000d420958401800381d080c0f148600070401144c0c188120704001c1c019182c81d005940c8080c0014420361300419080e0400c104140c02410700d0030040d500d4582c1e032180301c1b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435815116 1250 435813866 435813877
    0x40e01090b1c08040f0e0c070605100906090b150903060a2a11060a15060e0a03080406020d080a0c0804080a030b19050111161e09050c030603100603050c040207030c0c0803 75
    0x1000c1148400100e51b550302140d00d40d10803a10355481c6410000252141400341c240506007140d180e205a6011414000c41c0c0141c1005e03002581300071076803030300110038410900b445200204001005026101c11540c0c0490706542200c0c94201c003091748031195405000550300c441e418200c10a481014642964000540030050180726080e54800c1c0c0d910b0300d00105907221509082c0102c5807080050040c640541041240f60001500700380c2090307201c3c1d56800c040d500a8209502583c0311035503108416601c00103843d80301c0c04403c828864080d00c2c1002506004000d4001015440041084040b141c401e07071281c07034040c0c0001d00c5102e00d07034600c000030b0000204c01d01409000910341580550304900010303203500c80e100501e01c1038010303915100560f80d0460751110744810542e04514006030b0300045e4064140503802c101205035490a02000305807505403481c042c0b020007070070000e080000c1078021907071580021040d90b025990713000500d022a10303150700100c0200010f000310b00128011788000007070314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435816366 1250 435815116 435815129
    0x60705010b061b0c191e0e0c1e0405030c15190305060102010e0123040203250f050d0c030605090307020301060e0402100809060a0213050405070c050601060302040e01090b1c0804 78
    0xea200c4005402e000402c900403030124800c85c8100c2c4200720b41903804c800310380708100552000f1076050b181c280765111070806803041030400002003032825070321600590030f214001881c80383c2d52600c0d1806001c2900c1d200d061039860720030800d00340c0565240340200c00f1600c0d0041c460054404244010303002400030502924854015880d040300c541820405100783e458000d110042c141480c00781c6140c503101840c4c020004c0ba09801440e9400c02071401004155840044100b001d101c002d00b0311015040701000d41d403219121300b03007400003100441da1100045050741c2c2c002a01150541d10824854594450041c0082d050361034414001403502e00f0a044d2070245100300c52258441c400e8035000c03500c044094410341d4060b0445008111034081d00d81c0102058801c842111a1540c1d031000050201e03581150b8500c0401c62010b10780b810007405001075405000182021400d09041c442041c03002e0300140181041d040d641c80701c0207000e55851444600f65000600450348001c0c01c2c1c685524181c00c45c0c414030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435817616 1250 435816366 435816373
    0x110d0e10060614090607030c080313021017150a170312090c031e011d0d11060c07031407020d2001020106150810151d0f0f060705010b061b 61
    0x1050192081c1d070110400b5111210309420f2140d02d40c10817545a010000c200c040c004281081d5000640b003002643c482c90911020b03054890b000d005001d4200741e8002c8403000c0003180520240751142d00b010307081c0c1102208030074015a080b000c0108074000320a070172444a0110144a090450704000010880301d0f010040c220020340740d507000642d9502e00c510713003146d01d074020303500340d03001600840245910b4031480320001c2140c2d00e80e1540040f44a44040080780f00c0c1d00001080d03a84c541c1c01144240c0c4841482c2d0041040d07141c07015084400740201c8a0040400000300245014400d000c0240c54031141c0042403c18451510314106200311031a04510b01219510090b0b042d0380d41c01031003004100c1c2d080b41089174805c5140603089995000091000b41000d40d441004110745004071800146030300360ba00d0340d07950b14001e40c1c00318070032881407010b541c422034419268840c6500c50032800c51030f211003520f109490f01c00f170b0b282442c054040c0c519001c1c0c115101040c0a080034010341c1c3d0311518611403c099 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435818866 1250 435817616 435817619
    0xf03010e041112071404091110090f12020325120507090e0a1707020306011202030316060b130b03070b130801020d0f06090203100311060403080c0703060c020d12110d0e1006 76
    0x42c00151201c0190141c84423a01d00c044000c1818000c00f11400c1e4002c03890488030341511441020030422036600050740314001c5442c45000c41c181007049100140200c04510b034080301071b030391001d6000820b000e0140c050b0110030421082080401401e4098001410184000c07a4030701906170f03503550141e40545440c864810300c0c102c0010a18201c400d21600035002d400c1680c01c011491282c2180300c2c404a0b0148020005c043d00c544150090b148880e1140754082820b009074420070003c0584601c5100c00145819a8111243d40c00203041c022560320a10703440e2075044000c60064405090780c0900e00075400002c4004c041c40c41c81d40003080301000d078103040080d0340d103070550081240021541c1d0300c0c40300280d81090001c2900030b4400d01140f5001080e007441e00fa00c0e640c820000350040094101103034400c103418000c020890168003403404003803008003914481942c000b09410041c0352540c41c02580c1d120300d071418102920444018040503903080c04044030f441d5a0603910001c035020311400d140752010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435820116 1250 435818866 435818869
    0x230c09010201330b0a0e04020f040e0a0603061104060c1b050d050321150409020f040c0309020a051f0e03012a02010c090620031608040602010509030f03010e0411120714 74
    0x9941c01c005d91a55594448840f000500000350702100c03680d00112030900c400202c150b02d110a07944280d1043c4004a00c1501e58500541540c00381e19640d00305039000c0c8024019586d02200860038903400007031038408070807012035846913001031350071143c2c2107050607041c4e00074000004020922000321488401c60840d02e58140b0012090540c0c028285010078604e002c014549074002c0c0c1801400148100c84140c100070005080301c2840c802900070940300c45002d400d40c41c0c59100000203000c01d844c80a0070320041a007036001c031902d107000c800500c0301ca074010b0451070300d00754030101c0c0c0c3c050082c45503401014880c544480074048101c04800540c01d2608260110740b00300c040c1c20490b00143c88001e102c407629283c000100d40340b201c0d1881240310502155101d901261700d1180d03070790302460205070313143d040540003400d441004100350410b0b44104282001c040c00c500480781110084025820301e40c07520301d40308141c412140b030207070f5114900f0035030915403035070200e510f40c22101c00803c16001d0344c00040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 435821366 1250 435820116 435820139
    0x915090f030a03020a030e10170414032b0903020a0b040f02030316060506010c080d09141014010e130605040809040f02030a1d0d030506031e010609230c0901020133 72
    0x11082800281c101d61076402c80d09c000d00d441a001481480400006485140c081d40b4540002880c0004582c40c0c1c00d40d540c10001c2855408004500441c040c00350b81c2441e140a0360707510120070020940d0003c840014207000300c44058032a0184d0003802d6035901e1040c80b0844c60f4048103050280c605510344008141258042c41102c0c00c501c3c0c1c0b0005031818200084030300d0000341011901500e4140d47c140301d5400f84a01802994032078250510000b416013075541c5440b8074a541600840c040310501c0c81408415210001c2152910794001c8010807956100d00e01600702d40200d9456503002802d24010180c012440c1d005107100c1c407a0100204220031a00d440f603c009100603001c0700640d04401521040e9034480d0300420f500102c09030071540e4440011140d403801400320200400345035590b0401307010800b010b01540c212040c1c58201070324000e0000304108051380002d4541c400d0018002900d42d19a4001c0d08006002941d0301d039490703058255040c0d417408100040707014214807024880040b42051200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 435822616 1250 435821366 435821389
    0x1090f090c0e1302090c070b1f0b09010314070815010e060304060504030c08031801150501020c040504061508030c060130030215160201110915090f030a03020a030e 72
    0x1070601c184071850860211900400600540030041075405100050f80f100c2503564092030b10f8803000380d680c207441d041c40d61207050094044a981c0300705026a200407082a49903d040e00c902d0707980780351703a108580c0068005005004d0740000c0d0814010400c4030300c03504600c41e144910107517100e0607603c9541000450b00c003410950302030f40c42501800440c01040e280da100c01d510a100e030a203440c40350382c251190b110503041110305012031002e224440380c0060303081c0655410701c0080d856096a850411001079220481d80d413000b4013a955601c005410301141390001c00004608507000303900240c4403c480c58a079405035003040f400e8130440000241c0355071845036603c5d5149085040c015203a0010844950071040c19a0a504522588050250f503860128404d0b0058400090304d2100340080c50001e0f007581d40350526285440e50500011461b901c5180a01d0b201011201071180d880804400252810b850202041e8040c4600d900c8130007056000910702c0109802a152401e6005c14130b0f040090740c9560 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 435823866 1250 435822616 435822623
    0x71e090506040317040509090f010606020c010c02060703020c09010b070615051c050708030a0c03020c010c0c06050c0a0c03241e020f0d140114030a0c0509040c0f0e01090f09 76
    0x2c0004101080e6501101c040403002d0024441c81c203681d41c03001541e80728059629071240e40012000414401017407242d140206428000b03004d10485650010f4840b29044c00003900a92001030103004040c400d01c250079000c00003c1c400405561521803503407003500000e00485025107840980e21020f101341ca080b800f1074000a141081c10041420380c1840e0f00e0161038100c13010302c10054003050100040c400707414141402c2e900d4841180032420000d242c050341e0301e90a418000803a14541c0413032080030880d01600d82600700582d0700da0030240424904540d9201c050428003079441c005c4200f0070316140054255034200c1410314401a40a0048101c54007003008a00014004c1b400c2103d1042c55000b405403a2052250745003001c051000410a50f104402c08208105c603540040c80304000d41e200340240c400c400d0300280006102541c0c2c4040f51805400746512411544c000182044061020b0b0300140c03140307000d01c2512564400e0342c10059107080c05501e05090514901c10302d150601e102c4c41c890641c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 435825116 1250 435823866 435823879
    0x901030e0c0a09242702072a0509180127020d0206300112080313020604053a030806090c0f0a0507021002010608120a0215071e0905 58
    0x64407808500501c01013041e40100200204100d4080400c010f609004158401c1801900040349804080d00c22540166440d01c43c81070103e880842d4159030406080d5070442d94844041a60052000010202d64042d40d0f0048500c01000321182c50100719010002c5640000c0c041d9a1a11072070032520368800410700982411000000007501c1c014005e200c2a81c00501038900c0d202c039804018406c00395081d44801a005000d540d08085e0416010040c01052204040700d581201d6644100e01c40c030000c1c01d0f001070710800c00303001800c1d9500d42003158000c0c48000c11002000e28410f0050a0011841d1880504800c81410148038405440d200351803261740b640c4c034481713140d94410070004514006094a000c40509000b13498040b803a0500609080325680c58458552542d481000300e070117481d9111100710790400b00c1c1003007140c1c07000031421104500307030603229254184048200c2c540845400c4803507280c1449014082c0458000610014088807a0030301c0707903601205c82d8186c8108403148100d6400c0701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 435826366 1250 435825116 435825119
    0x9020a0509040302030d090c050901150f080c07110433081203010323010e03300610020309181905010605040504090f020306040524060604060813170901030e0c0a 71
    0x300c1f64010000d8130b20855000d88000d48401c04a000d0a0b0260841180f0391800e01c5203000660308595a01c4032245549810642494000b90011981c0100c0d1801000d01e01d042c00d80f80020303906c6e1341042c654900c0315070741c1030f41d205140e152460a0400740e02750b02682030fa00642c00300c3d4115000c590400d1030a40850f4803841d40e4615603824280728a0503100c02c00100d60724000030301c2ca000a00a5201c0480020019511071f0010f06800e008291041c604180c2c4001c2004c0c544900146400b51aa101c48100c84070803031540402c2047c5d04510030b506d0b240703600440707071000440e1110a05203114010031000341c03c5101c185001c0310007400c4032005c2c00f0b03440208005020400c001e02e0700750046041c1a06c80e0307117002c0c400c000541c0417a1504100344c80880f9250402a860030700d610060141ca000c41c24800d120042e2400c00fa0b01082140c8603a0003600c0c108011200000c021517244400030440540c0100310389094040c00100d02c0e415000320301564000780c100605103c10b590006412101c00200800c0703844040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 435827616 1250 435826366 435826387
    0x3050901180b0406020f0f15092404060b010e0d02090601110303160206091f0f06051207090b0625030216060c031202120423030a020109020a050904030203 68
    0x680080040904100881c0d01030422210144a036000500503100156201e0b81800c0001e82401414101c01c01150701400310300401030400600551068001040000982c640600b060b09040000070f01c1e20000348682c40d040500021001140d205502480c410801104c44500458402280c00c07801584502d004800304007615103806405e030854814100301c200d51140301c400b40d003960411100d00d11000107080c42444c0017901403001b41e41c400075070009030100b02004c0441c1c3e2a03803001003002c51405076460707420304411013a503032021303010f00401081d01c000560103115040ea516041e001e60812035051020f09080ea050400039146041c589480c41d08030090000448074040d4610f0200390210311541012850100a42c1d00c01d001030545590307188416402400e02416200180d50580c201500c1000103444a881483c070030381e006540004c00e2540ca25541020b90504048501920914080044c001d03140c0c0d90154070107c5a180f0030b0b1403020f031582c0d40d0001c00503010001c40d009005a0410052402c88 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 435828866 1250 435827616 435827627
    0x3180c062c130b030f03130501050405150f0417030309010b0108163603050613080a23030c12010f060e01120207051501170601050609010e0402071e0b0c041203 70
    0x615000030b500280354080b40000a1811910207111040da8000040103200120410401006480b0a00b00140342c2071600c00410f91603080d100784041c1114001c280020041303050421a801010086903412001e140501e581e40c03264001d8561407599860701c20405a5940030744640351281001b40c0004050b4001b010060301c01c1400500c410000a03c2000c89a003c40300025210100c03007e00c02c100c0c803070a400e62030010301e08940030b0051100c01000d0099403001460100845138031491610b80b2400004422000326410400100074850f40600071080240c600e1583e406000300652200c03810040340d90b2085602d0310070300c03a4002c01307001030010021041070f940254028006030780003050061902e03085031103081c108442c0d00d051803407000102d00104500352910103864404000e20001e402107501d0980014001e02c960041a0b042c0b10070360348048800d80d1180d068a04450304203840030402000000001070401d0312540458032160700c80c0204100c0013100040d241a1201e80320921075820300d40e201643e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 435830116 1250 435828866 435828889
    0x60f0221090f01200307020907110d0e010216150e0a0b0405060304020a1a09012604150207080d020405010f091415040512010e0d0c020109090c03180c062c 68
    0x1413019900919921000f10b0032100501d0000e00f010319280c451a00c10882c80100107010602040030310b200f081c44480020440583c0450f03c4d080ca540410840401031b030500ba803000540c06191801c1c1e41c0001c684140f01810030441d0344554900e00c03102602010403e040c0301a001d240d4a01d94240006c1c0300c81d08000c401035403c507000501c00700945980d0040c00b002818141c1c003044034400301184055071560403c1c04c2101c4041d0b4800355490824420946848420004001802c102000c00740d05d004080550b048400717481d00010074a945440441e0a003000c0d5000303106007800a00441c030000700d40f510501c07006081da0407201c0040c59445110040102089050800307200e0685d003040700180f1179641d0700000c00e0a40c0b0400000c42c1180c1d070305500314101190b64100c6c0c13040c01341c2140c8820050380d2180e903030019208007200010b0a00381080d400c90003450711701001005031560540b000188400500094105d400d00d503504e0301d5030b500c200140d40000781488207840484400350300b001c14900e0104c81016 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 435831366 1250 435830116 435830119
    0x30b01050f03040b09190305130b030f0604241706090d02060a050705040b0c0c0a09020c100905072105010609060f030602090111070b0904060b040303080c0c16060f0221090f 76
    0x700450f43c1e641d02e0409094084030214042040001c1d03002c51022580e02701c000510f030f83c466060a41c0707064a1090f1030340c0d40c003c260074400e90340d48000c010f51110715120060181c04507146020f016403a02c0c02c0c4003a07132007000e40c2070840d8854000040e0f20700c1c100185c20341c0600480d50203001191200d40794000505006030480052000a01010401403051000303414419412401080c4001c401c50910280c4140c44d0019503403503004000380e000f22200058404c1004880b0407000a94910300e003425030421a55030082d80811080003051854400035885c42000c1d9405503008100c050351340c000c51011258075109109208010620802c0465425400341c280a00e060400f50143d83c1c0c0708441a0600e01c1c3ca401641d580b440103e0782407c1820035105080182440c0c8100c0c6243c1821078402030a0028018500b80b48108005580c18003010103010b8041800d42c09203904849139218400a0900c0c1e00307d8400304010301c94903940b050f194824010303400701144180e80c81c40c0b8004018081c1300d0700b1000e40c1e840a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 435832616 1250 435831366 435831373
    0xf010f020c03030f0409050a27020d0b130b0711060c0319110d0e160b16060204060806040b0414061002031b0d0e0102070b0f07030905090a060303030b01050f03040b09 73
    0x4407071900c00b4001088502c0c0480101c5980d9400c141c0084119a0060312200201d0701c0c1c0441d188000c05121142c0c225540f901c91081c51011319480014518115035400802d12440501881407442d15a9900c45120303128003420130b200da0380d0765002c41e1030000300c110380d55003079111901060242400e400111b400003400310011012104800700c210540b001c080c031103a41500001006905221680304880e17420000d140038019804181c080040b900350b16000740b484e601e8002400200c081901020b100c641caa0003403040d9219035540c40c01500ca080d0407101d10380100c0c203004c1030b0f1109203090710401d201403984a03c1003409803120f80a00aa44624200f0701083d407004100251800d840807540d0f0052401400c0203011001c2003c1004042e020a25019030555214220601c1407041200c255071642d2146010182c85000070b060440d0282d00c282c2c441e54000c5598000d02400c000c142c3c1041d41940c0c000d44060040c00c10601c011a09403050242c0301840305e005001180c001981d40c2038054101c003040c0c080707 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 435833866 1250 435832616 435832633
    0xb0c1b03070c05010225090b03031903020304110405040b073605030d020616031e05130b1006120e0a05060c031f0f0306020717030915060603060f010f02 67
    0x1203891079100c007809030b072440e110312010022981e0400205904404107503414a02104078005502c420386140500210252601788040d07013a10200144c4041d41c0e442c03140c2007844525454094001d6000751000c5e81c000003050380214882c1003138020603001d079074130140140f01541c1c0c900084401c81100314201c1142c011a02141401c1c2080704c1c4841d00001000b00040182c614260801d45032440c0d0300c0c5104195040340c0100038841010101a460b5070403582000703e165038404181d0081c84803108140c085840ca000103109103c0c40208440a01c0d92203146240050385403600b4212070f882052087c1c1000030528501c0701d806485540100030030711043c00031288440d20301c0c2d0361182060000c0b580000100400300070000c2e55070110460070303546000d000ea03007208035061003549401ba8110b80005880550009140c20412400c030790300202d9002c03c0b810b0f1940b00d01388880d03440e03240c40700d00c01e40c00401d10400e00410320a00c0c05a0483e800380d140205000050880e004c015a6000c0340c4030390754010350160442 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 435835116 1250 435833866 435833917
    0x20409020120100509070303021e07260d03050906061201020405030703210906020a031416050c01091a1605070e130309080a0312200c0304030515040b0c 67
    0x400c02d1614054030183c00c0040315040c000044031300003046903c00f035014810400200c0d4012520b00c05882d00c04032a101e402205103011813501d403c076844049400889800080088044040704100801c5c003029141140b101d000118203659096807205219002075001c50520310b40294003100c0d11031154000b6003015501c41c0001e06240c410b50059a45119170301d4800901d00180109407458002c0d4240301d81d1035420120000c3d51250240720081c14003484400b64001c1990034030a480b8407005410803207020601c2490540e072074141848480d40400c0ba1044080792050b820512a04800144c441c501d0904001480003881c50341c04d8081680c040c0220f0303a01080310403001e040188644580104101e0740351a524008018584550001c1016004400010300083e03001086140c015880c80703000c203d5030610040103410007498440030b20035101c0025140a05800070010384101e9000b0700c199042402c2d40070f034420b400403040b28000d10766510200043c40401141000e40300c51010141c85201010400d030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 435836366 1250 435835116 435835157
    0x9031e0c080d0f1103010f03080706060302040e15070f050f0a03060b042c150d03200703140307150504060b0904050303160e0f010e030a02271609030204090201 70
    0x1908407035840e44807002044070030781c10301079134100440c000009482c5614181801141c0038550000900300c2a000030f0701c82c2404116001803000d0b41d0000c1003041807a180000040c0d0303c8500154500c2200708a0b03001440300c901820b4000c11150741c03901c86601c6c21440b003000341040c0d4010190716080c10f50f00d00010946100820140c00034018604d0180d03242ca510036041c0b4000701c00d030452580c00300a05410401c2440841000c11012039090391a402851a9498207032412040c4d80354044007615002041741074404001445000c03240075904078464006c0d0449215120302c5203a1000d05070800140d6a040303240c6055210541c0580079420000f201c0f0400000145c5404060300c09655a60010040c0002500180062080841541407144d44041102c01180c4041540c0500a06022a080e016105030301c0c00e0001940c030f0759004004410f42108400c40060900000803010000104e040005000c154216082c02200c2c03c16280d1600d59899542044058408603100704d0409c0a0710340140144030800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 435837616 1250 435836366 435836377
    0x20a02151009060e090106300f12051305041a011404080304061d2e110a0302030a0f0207080a0b2205060912090d08091810150309031e0c08 61
    0x60b04c44491414010042402e46140383c104030101248200480015100d040da9845a50015161040c0d050007509182c10045054100038145002100c00828032690042c010031940d51005050000c41e40ca440612045030508148120789601c550704200407907018058410614052072003180c80c0c55200c1942c5c0d805c0d03401c541d1008001c00c02c046207241018006446810b02140c0c00d647c000e24401c0510140314089000405003241d400214810980301c5129104207054222101c0032101e0b60000d0380f600941d264013035420075000482d80001c0c1c1c9100c0d0303c08117800303088070759510090404400540b2207030620640030f8a80100300c41f64000c0059005010340c0c00035800380c0100007070265858025501800c14114000e8003a0016080050700600e50711005044245904480603e1711a00c102380401c20350040e4141408039800c11030104003481c3d005213000016119a4980d04070f040e80c0c03424090341604c2003107a0050128020040070b80d00800140188030040f00e0501c0c2442d00c141c4140c80b51142940030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 435838866 1250 435837616 435837629
    0x130914100e070c0213150b040305010b09090d1b05160603200711010e0604080a06200a030515060406120507050703020307080306060405040f0b1003020a0215100906 72
    0x1841005a11041000c061008040e524907103031040c60003100c010b00614400c000248150b03c0e0240c0241215400e0784040000684503540603992915480c0300d1103280c01510046030558200034100c8084e09058030300c02e0260390020000c001c20b018803842559002002d00d94001c1d07007900030f400c8201250b001c205c5107254880c41807a190b4a18100031000f41510000b00c1a00c95041182c881c40b0b504c100c255045030000c98200380c0807100f105d008001200d1030808415042d510641c00304002c60254408261071108a202c0c038820008410041003012801c50780740010071000f4400e02698102c14000e4104540c0562013003808190550b034000050b0850700550050300005d0000c1104c0c0042d425184581d0382c01000c2410014100f19650340d0081d924858035000400d4014007001065140c0c40300c1c402d48001c1c01e8010424042c81518190300c03130040429941c010b110301d0f4a1510100070900900c02c031303103401d41290f002d0620340d011050746d070314201c40c01b9080c4240008140c40001d003820051064a01404d00d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 435840116 1250 435838866 435838901
    0x1e0803040b040b2401031508010921030902060910030b0909211306110118110102160e01090207021305090c032b0c0f050a0b01090e060405121309 64
    0xa0504014510081c000d1018403014924240d80e28245941500e13050030b41030928020640300075645610101081c035500c09101b80d803c001540d0300700941d80140c1c03c4105000516041407160703000040703066541080c8041e400041c01c00c00304400d0f040024603020003008500313012590590400104d01088400c440c01507182e00300c8149411103190302c1015901500642d889641424903240001c0c2e40c49100384110003d009000c3e400b00c60702c282c20341005000072030322405000100710f5400e00d2a65a04440485401801002c005101d0b0413010203003581030750402d50403e00705a00300002c0c2030095101c132509a03400841030144129607100c42c014a486070050b03001800030050030405240c40c080b1001c80320b1000c4040102c800d5110318104016480340042860f008446c010396081c43c00d81c40301201c10181240c010000005c003840ec02d40e440da4100c8140c0c140400010f281681c60944900303050301d008003503420000e01841c05c091010040e00e900312580d4001800340d60350300d1074401240c010b986503040c20764 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 435841366 1250 435840116 435840121
    0x1030c0f060201020f1614120d0501050d0f120e0d0f0c1211040903050c0a06140c070f0b10051009090b0409051f020d020d05010302030f01181e0803040b 67
    0x4900c0c420401010280001d60a08446440030300c0e9601483c43c414185000b04400d80b070a01c00450b03038240416002e00f080d81c08a00e803a0300d02c08400e5020701c1151144605000001401e410301d80b0951600310307004090f450180170595140c50050b03516000210421001d2000c0c09810b980c0d4240c4403112500c181c00011018910740391484a66001c0c0c0d00a803011142c544404d00440c02c0f08468030381c001d104440c0087d440040b40b4080d1303450f0045403024480c91050790004030400c80580d01c40811800b0f184003240c02540d50350382c2c0780d056200d04400101b05280b2215801d0015419034145078000481410319038000f52902c1c0440c00103100b51940c400001c40d502c2003040b040102e889507594148050750709001ca8541c0742c894a9803483d460b050310604074a94035030000000b4040d4155910a04918400e55440c40342406c1d100c0504001c1c00700741e12030300910700b14101403031341442000880120b0b00400c100e25442a01c0e80c008040c83c01901c904a078000c8202040014100310045205034414846113080d070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 435842616 1250 435841366 435841379
    0x5031b03060601020105060112020c0a06050a050601030501080705030a06020c01061d0f060f0d03120e19020a080120070302072103030f060806180703020d0f02031b010e01050a0507020901030c 84
    0x1c40546680d056900d00f00c00c0c001c0b5a688289962002606e11002503902d400e040c003600d1901052030310240c0410714201c1401045100d0f0340009024150998041c445139807034208560b15480180f0a40e03a042d88070901e880c0000302940c0240ca1414a03d00000407030300e5907a00c1c9113106506c00740b44108a44150010001c021050203e02070300a01d05544ca80400c00c1c110000c0754a00a15078070140502154602140840d481a00500348440d07181c001d41e910083c80d5040c0502c001d01c2004100c1c4139103502200440d2021052040292003820703003070304c046208455190003445900540c4180d046006154020a40700c01d141d0802c0d240300e8038100c9440302c0c041c4905004049a91004d10800d026042900422401a00023a1980c02507201d20441c2d540100008400c1d103820442d40c0000d410945203110801400080504081c003e8000c3e815103002da0b40445080c0c0100c1496010f850100d607421908103401d52142c000380a80b04a10309119107000000d1300042c041e854241d0085402074030900003030054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 435843866 1250 435842616 435842623
    0x60403020f07060917010f09211407111309050616051303021c060504050105010504110705190c170c01030f0204050d0807080f120a0b010c051009080405031b03 70
    0x1d1104500600511402e090780209090250700c540401c69540c120203000d40c040c20340c0520441141036904010a40312890003480310900c1280fa0a01035084403451a0010b0150728075030800300d1198171040c6400c0d0035a60350140c548100640036080041082944442c020070710400c03484602500050202d494400c24010315034175411440010400f0030310003149031601307091010041e20f50403101980282c1044540341d4404100203c0540079038100002c2c84180075065111606072031042e00c0038860302c29049901c03110752180407001049a848000141403403082008084070302441950388014503651545800c501d41210b41c4582000d80102002614035a014420f510030705020301021750420f46020005080c0c509000b00142005e00c0000308001001508022200c5284024100e26140c0c954141c50a400030001c861100150303140007405c10f06503008442c41400180d00100402c1c1e9001a44002c5015107901c041c200c82000007071102141c140e8050041c00f0707802400503e2030a429040c1c4040514 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 435845116 1250 435843866 435843883
    0x105030c0c010b120c031905060a111c0204030b060609030d2d020d020c011805150928270b1f1809020a0c030f0504030b040803341b1406040302 63
    0x1082c0401041f410000e6000702c6c031264480140c40002612881c5224403450070700c0b40134034000441d000f441769840304007440d6010b030007a030740241d041003080c0d5904014004244210f000040d415401409440d092512400e0700d900c1444110410381a056801d15408042641481400000d40c1094800c00d0140b0f60400500e081c1c0007003440c00e8851802144403032032600000303008407030048a0310b0600403e8600c54008682c1c1e0136102500103035002c28084001c015400e040c0990701c9900c940c01c0d070002080014100d030001e504500c001c91200b00d03840120303044010003540d2111500240090082c0f40c508240d4003402605006c1c07034035151800800c81c1d20031110881190802c00d080351045c444d004c2c009900c0380104410700c4c1e250070420188100c01c03200780d6050255510007402c1a80b40c00030070041102c0c00b070285014041d00c05007601201154288511110621041085903034030b00e031840329006120303800c6500d0f82ea03184c60540c1d0390154681c41c0c3d00c1426040c42222540c9905c41414802019810000b024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 435846366 1250 435845116 435845143
    0x2090a09110904020616050c060705030c07090b01050307030506042406030e07030b1302060f040b0417030c0c1905030f030c150c0f2b09020a060207050105030c0c010b120c03 76
    0xb00c2c80c58540c0c00100e0b42c0c090240030100e050081407404042120401045c20400002071035243c0b1403586180c429a0380d4005000b920a5000da4100040e030308002e4000c412004105131102030440d900c02c2804c0b0002c00c402014240e2081c0ca58880d04072031122051140c56640c54200700d40713045c80c1086400303000d0711a4804041c03010340c41044c0c200049044940394980001d44e1801d41e240c0b032005400000c11900032490b1498040d200080c0000340079452400510446690001800011a41d40f41c1581ca078010410001016042504000c0035441c1c034011000040080010700084951100080391414014200000c581d500000d080c00610034100024034101d80000c0702020149040f0300081d206001d4080000344085000c500085c0300425030a18042c024216081d4601100c49110203a004d010803035000c0e401948403881c0810124800318903101680c0040c0c50742c51460b00c030303180c4461080e031014850410780d55807020b118009a0750024007840d008a0400105444603d040405003012072406240 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 435847616 1250 435846366 435846379
    0xf0c04051e061b06010311060c0303070e03071206090b0a0621050a1205030610030510120f02030d11010513030e01051b060a150e1b130302090a0911 65
    0x200419a1509501c940c06514000d000c1c00c1c06495002041c410300400510400201120520b040e000c90700169090407030b400b131210311900f1700303e01c401d0061a11540c0c4204000382c00410003d81814008d507004030b0400340280840d00b403260740c1c0141a802c80e07600752080701c2641e1200040018812503101d0b4940003551148100012490700d059655850402d805d01e82d050b40248402406001007440b00f007a00c1500084441e07113002003460000d20503070007106c4040c8240e4000c003040c030b20785100b0302c10a840341c9044001040882d05211990070800804801103a0390003200c0c8403880180c40034840949403045503100c0111019802e000c0e0303400d6500040003903000c11400844540480d03800142c8070400d010a08000c1d40e207001914011074007884264040c040c6205040034000c1101c6590b002c0c10300c21a451703150350320180d16010750030b0618500399041c030701c980e0000d5014034007501480c00a003ca607074240c4151551039904d9010030280e07502121251001e590b180008000c0c002400c0040c03503110400c4811 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 435848866 1250 435847616 435847619
    0x201021206040c08070f0c020a1502060901091e0c0f060504050a150f080c090429030a110907020312090a11030123090705121b06070807030311040504140f0c04 70
    0x20034180e002402e5000b000591000c0c3c46c1c0d05409440c00000704d40d0040c000d201402d4641184013010070300c1441040040c81444000303403c000c01031090240b02e5a104001da03102c0c41c1d180c20000c40c1c0d0b001da00c40079541d584542e10300043c0300c02e20304491801400c050b2191920740d89440104200c0100c40d9104c540941074a0b0100c90100381c0c01003020810461500340842c1d142c0f02c00304110000d0040e01802a0040d00d046110035a1444080c04401011204403542541d00400c0b400d2503151100c2d058000c1546603100b20b40c0866281445000c0d9020005e0320441c3d091003018244454880025110203204d0380110f1500801d21810504107109200709400a010744050307101140640408c00c541420480c6105010844184090020307038010100107000c6c0041402d002030094640c0b400c40203003100c60741c21045500302820a042a1580a03800400a5040415544098010f00812100c16051040820000c2425a268800d03024220f2501c104c2409600c0e05210350311400d200a032805040b810203000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 435850116 1250 435848866 435848891
    0x9051e040512070303020f07060609110703020c09090a05150403090f0e060d03230d050702010902061603031122050102070b091311070f0b1509070807020a080406020102120604 77
    0x1021200100900c0060750750b9905420210001d0047d060303613040424000074240c003800b0041d0002c1c0244c1e8060101000442c00c0d01d400d000040c45403110041c056040321800c0401440c141c1000c5600c494128113031007075869150780c1c050503c0064145000165111003d1200b07147d401070300b8a015001101c1003480140c104040301d410340500610142c81050140c00031820103104010442242c2000d2441005020040914038042e800544000a40510708000103c009205004000009401925440c0392000802daa01c051500401d81a024175031140e6a40031113020100003080304031a0345110111410b0150861203110890383d005030b0455103c44814801801d1800480783e400d04100c800390346908150300c018003c1c4c5003c20140100520202e06d603001e0118001c0d012f10700ca403084604089a5a4070030710702c00111180481d0b150482030340c1d000105d25500030036003203402030901c0c01220801c004a40d103400b8a80d106400101c0141d4010840c000240c014048a075007100089800b0703c540c4a81c3d96 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 435851366 1250 435850116 435850123
    0x7090b1e0603090a050d0c380c12150102010f110405040f0f020c0c03060109140c07061e02040807050a08060703021b160e0c030907151809051e0405 65
    0x40d0040c810078001000c0343c1800420022001c21581c0807013580c014065040e0050501e090742401590f02201080c00105c2c20b00c81742240860200c0032290180768011100f00c0d81e000075200412164541c00200444076412101480151040640300c2142003001c04020009003907400e090100c034202c0d4244079030104805801400d0b0780039a107055400043c11044090b4900140004d0421000203601c00604800707408030109086c10840c006408440459a8941280d0100c6000954500c4132a050b00302080c4a60307040c50040456070702481c00405e0010480366450400c45060601d048901c0e8001070400104005028a2008180896517980f040e441c180201e515600d00401d03800070954002035000800003030f609441142907202d002c4400740340c00e00350300046810031801703114200c8011000180d07101ea82d60341103911038400007020707220351072401584500f0300b00c49000c51410300c154100c08210300c040140400d00103280d01003004c00e450038613035030400d280c00c0d1403200300f91a17601e0720b000c200c003003407002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 435852616 1250 435851366 435851419
    0x90e0f0601050a05040e0c090108180d0e01030605180f0a020a0e130905030f04091107051b060906070b0a0b030c0a061103090a0b0c060624030a110a0207090b 69
    0x3800c2c6541d8070703000c00c1d208031903d204035080340c0d801c03283c50424001c0c0e00c5151405072a03a03260a072a4060552a200d507100c078440300c041010405540304405100003544100e411284c010410706010030300a444900080c81b0388000d00c2e198600c07030042c0c010400c2e110300d0710380030541140700d548003145000442c0c00700800040c0740d960b9150040c50102803084880f0a99881090b596030001c0c156501c44400c3c403104403056019104854140341410040e6144042410440f084558003400508109180c200049000d0741c09014155001505114070304003900c1c1c200040450034410089c0073302e03d18200c0301e20012280d05205c602d010798040292056181c5400c0c140c1415210107013041c40a01030075440d107030b24612504d100140c000c200240b000907113031410f802030160300c0d0341c00042d156a0780d51501403140201c45c4556094401100c4000f00025100c03010055400040b4900c002c510070604500e01c0f0021ba001d44880030050740081001c00a082c443d1290385a000d2080710b40b200714042c0201d840720101c004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 435853866 1250 435852616 435852619
    0x50c0906070510020708030a1a010909051008070603020702040f0b06040b07050307060903084807020d08040f12020f270702010507170f0703050702070806040501020307090e0f06 78
    0x288a001c1c05810050301c4280d001c1d0f09829540d0f404107261101c803e800c19922001d038076003441c1c074440781c0368000800403410f01c006030340f084280d40c40d2941101c040d00c0b002d455040381c03001c00c007400b241540c030601c02c080181c001620050f95480c014810301c0112030355080800400b41c509154010320750b40c3c0754119400c45d146400019100d101908082d030071071092030300042038140341030503880030076030072290692180b48038149130b4400b070001d1403207000c01c44800c4480c8100014074908001000c16406000ba4403495540302440c2040c43d59070101e80444900326040e1403007040800d0070001030105c000540050240c41072442a04480ea50100d00c0c940042401c40c2e1113810900c200d9034507111b99188030454014080c07410411410020800f0b802440141c3d00400000c1c0303441c03426030b1600310454186004020400c2300707040c50790b03558508038010f100150020045004042000a505400f002039501072802480010317601d0a105c03002425008195000700b030701001a20400c001c0e03800074282e0350340c003c60 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 435855116 1250 435853866 435853879
    0x19050603040813120f0204061205060f130203100204090b0a06021002030a1e05010501030c0f081b040f4e02060405030a0305040518061e01090e010b1903050c09 70
    0x2a58450300c2840f420f50b005100c08200200d4400e0510404000c2540748034020b65003000416120940d21000c4124081c000d400c540c0400c003c03d40509031a041590b100c005030002c0c0801d14220782c0041c0c200504544030031000c98000c5414400c0d954980318050301e03048210f903481d85c0145001d1029417215111541082c45507404000550081311640221030200440c0d0031587d48044245400c01c000e05080c02040e0000740752040381714105000d0001290000c00c0c0703448059440e80c640f100010700001d00074059400d0300c4140000a9081c030810301d208098a0702c94240e003405d010311f03140505246c24035080810102c1d50031800c015004d44001d115041b0f0308500740080c1200c201400842d215105550140b50548141c1302079000341075210004c1d00940380102d441c00009480208a2a0001016507406500002e0040a840d050003429280b8814220605048501e03650b59902044840030990029440490003c0d0b48102040d00c000340e4003005070982010840c0c0d003803400c98034500d0f00034400c0300b43c041d81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 435856366 1250 435855116 435855127
    0xf0d060f0f0903031d010528020d09030203071b0b0a0e01211e020f04180b04143301030c0915020d090f060f050304060902030604050c190506030408 65
    0x55a40201d940044072850510802078940360080c01044a1151442d00030b86080040402c2d01c010b0040c64000c240003134844903030b01406025038181c000a10000182c0315420485601d91580d14026884890300a8001c0c6898080300d041c200c40c0c1010901401081000001091008120798810740380410902e140032002483e2a000580b0805815074961005035803a001c0d1801084403034011020040c000a54900402c410f0281481079000f80074110262020521081c84480e007915102c002c1d10300b13200c00124243d602e080200302194150508283d94a12100803c41c1c800c81c144c21006620140d038040a804003000d0300c080c00e5812030700300c80ca410151100305d510750152041042c000030b851107250700160414124406035484050306015004502c010f0780000d1100d0407021078400710b81139500c82c541c000305102000c4a107540028011142540e076802e010016840030040648558031130001840624400001c2204d00d1031000d01e016460410708505121945a9505594000d0fa00900c5503031075a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 435857616 1250 435856366 435856391
    0x50f070203011805030c07060c080702090907030b090c0a0e0708040215040b030c04170a0809041806051003140109020117100e090d090b0f0a0c020f030316110f0d06 72
    0x1810044030740c0ba00040c14440e294203102c07011006014100381a0222480c05640c0d8200727441c8420789210107021240240045405403c01c02d1020b07500a080b981900c0310180c613580c621144000944042d001030384040c1e1184400e05211401b98040c000c03150314a54240740c5403070300905914005000a0241540584401401c1e00310419100644640c14096032207160410781c01c0d1654000c0e00c680110040781d0310a00110307110214845046a07001408103180c840d44a05020240501240b200366050121200c040481c01c54416103000d45861321031140302500d5070508044428100074900c956901d0309040705c4c0140e03002030181e0070030b02c045001141e41e540c40714982c2d1443c0711144d020b01c00c9001404208000b5001c02700e2164454102c5071504903145407180390441031b60044141249288508000103079001340a000e90083c00e5100800b6605680e0070a8040307819500540040f80e405120b0b41c040104103c1041c050200c40c040c10b58035203001145000000700496654403000d000706940303900041c0324 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 435858866 1250 435857616 435857621
    0x2060f010e04141c17060901030f240207030503070201060e1006030905030c0d0206010806130b07030b2803060e011a21070b0309060709060203030106050f070f081e04030201050f07020301 82
    0xc400203502036803000d050003013010b0102c00403081e060740c400e00e9102c0002d0a503c3d00e403411038142c98206045a9846826546d01a5100048030200312148404907404003020b000c1d000404001d1721907a242501c0f8100604040d00b951034507003254050007044010000080030816402c402c40701d9518001c9210003d5041030380c02c500c41e440091100e0300410718001e8442c2d400049603030489041604403402039507003c100d10500c9880d039000400c0c0d20345c00340115200030704c2504020a1090018801445146200b50500340107280000c07503200b07480c6104040007800007a00c40c43c0e2603004068001d0080d0041450210541e100c4100e0003481640d121200c800400c4509218480e144240001c9501141e141c1070f03003d910f60000c0303600c81864840c810000384d81340e20a0034ac5604440b59074000b181941d090a00c103071003981042201c0f001c0c00c04103100b0b04001c1411510501110360140c0903091380d0f00d1520780c07500c0341000c10824602c003000701000308000603640513044403600030500c014580c0b54103552001a01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 435860116 1250 435858866 435858883
    0x80a14130b030f01080303040c2309250c0c0b130801020301030c0905070216030311033115022a04051504050105040c0507120513080d02060f010e0414 66
    0x11000c001150124030741e010907008602a111080000c9140c0ea82c0d02c0e04581d80344000c4030020140b88825008105104000c40307440c444407485542d0301a0b0a2145002c260765000480f035030036800c0c44a03516403a815210f0011000402424036104c1d901151540f154400008144550001118002801a1600c000f5480b01001d012120700035540c9503901e0401d41c0750355100c0e010b2098182d00e0714000c1501c45000040c45844500420b128002091458800f59070701018424407046070f0204000007103030703200d54101f00021000503883c0360b030b00f460340d103406a2412900c540242104801d8181c247d0401a00040c0b000c8184100045507801003598034000034070030310204000b13a0880c0c00e12041c044081c0d0701c80354507038110300e00303480c104510784e40d031000c0006548180400307401184040001c2d80102e007085120140c0c2c41c0309401c00c00e02d040c44041007906d1040041d800342656800100016101950510100360001c80c40c090030302d041e5040c504103c00c05000034000801030b02640540070340344041489100c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 435861366 1250 435860116 435860137
    0x31a030d080f13080705010905070f03020f090c09040e0f0706030603210c0803070804060b03011503080f040f03080301060908061012030e100c0b1003110d030207120609061503080a14 80
    0x303448041c0d0f450f1581c048c00720f0310400c4681e402812030100e8491245591841120340040080b64805018810b00840c00006081215086401c000c07400c0d041d2141d000304050030890340b0007001c849054108041c00d1149941064003010b003804010800304500d015241e6041e0245c0003a050f034000c44500c280e408002461340100071840c04010007004580050b91a8840d5006e18410b100210000c81014200e5001002241c60f484141c0014404101458042c007042905140c095252544802c0c4500c00d010895008403805140040184041071303000c141b100c02010f654000708074508000900e00c0703504400b4081c2a00c0c0d140b400c00500113141c0b1984a1701c84010380039181c81d991203c41e14000b004c0401c0d28006035140e088401c0840d400414400741441140c2e000140504107005407030401c40e540c0089030307044d811446285400709014a400303200110703851081d0b20004403c40355107030540544000d07201d01841c16030b0312030042000c00c0c2c1480031124450040d161180003c02d1140740d0352200d00503510300c0d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 435862616 1250 435861366 435861383
    0x1050c091f091508010e131707110402030109051b0702010801060e0102010f110406020f030c0a17270907080f0103080d111c06081209040c050c0d031a030d080f13 71
    0x32814190007502d40ca042e00c0c20146e49400c0703aa503100401a84503404036008110a0010402c600943c5201e0040c119840c42508103120701c819180015003a40c02c2a04402d035031658480500040c50341484c41070b6504416041098100480f540000e00150814460710f003e002c99081d41c00d42d0382c1e01c00e50290011071304601c0204240c4e40980f401110340e0f00240100000340c414111780385101c8034000300307440c03400f54200001e1001e02c1d05c80da144403040e4854500380714440b00a0002c80300c1e03892040c1600112101112b05842d022608904125118a01a20400038000c0c40300a10540e0382000c8086410b480d08581950703654000c82184400420003442d1820f0110004508458000a810405658854000740c180517240c0c031102d46540301c00503d072800c2c0d075002040000000c40e0405030041c0300c002c80d150800900305641c0302440f0f42010714001e60440001d42d18031250462481002c054044103200360010280e40740302e8000070b8000e00014141d084803410000015140300c1740c03510500400c40c0e00079101d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 435863866 1250 435862616 435862649
    0x50a0b0618010f020304180906060f080a0b06100c12120c080a11030c0418200c120f071e0c0f0e0c180906010c20010201050c091f09 58
    0x160032410035624075450014201c40c4403048102d2000007924141c0f4403401308003601c020100600303001070402c0c96040b10781d00e0310745074001841300b0240388003001401018040c0c00e0f106420f207000c5440343c80007054148500481440860041c0c3d10041d120300e030640c080e2100da51648020815101603240c400620303910340c24502e0741c81c0201d5010090794043c03907401c041400304100d440554426408120758200000409200070008142041603501130641800000600c030803006154001c1420402c4a05513001030004420340c001d00c003003100107444a1500c0346076041c4040751490805900c0303000c502500480801c419852080381620001250713990100c021914155290f1400380e0704480f038400c0f16410321401c00065124070348402210f0602081c01c031468081c00c061410000102070107003105041010500d071460000b80c000741c4c04440f1500b41070300d01c0207a20700003000a013510703001880e640c3e90040920001c1e406407112044050450001007604070500e100d8841100e0851082d44000f00c2902640031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 435865116 1250 435863866 435863887
    0x40e0105010b1b06040f170c0d05071101080601050901051b06010e0906011d062206060201151a1204021309060204030201140705151b07050c090105010809030d050a0b06 74
    0xd20380410a5240920b00c1c06030f01209070b484440840b00a02440c07007000e131540001d0300d08007401e80740d032420784030030b44c00c1c059005082c500d07012040d10090003040c00001d2448c1800b0500c60480c0a41000346040c0d030b19031811800003010760060704c042a040c0034000c10560542400020050b2042e01a0004c907409503a403201000c0019a064940b10b5180c0503040c00071510000c10062802c52503695101d82c4900d0b03c8403c2070010005221544401c1d00072554050107107c1c0942c0078031802004294004581d55107080d0f403e1421816076404a0b400c1406003550020050009040e01d044e44e800d580300504c10340e904d0001c991042d8043e918000d800b803401061104221243d0702400c00e4034001e07030380d0320080460301905001c0d034850300102038003581c4407991243d0014000c880f515440b865020306517103100c685940e060125003101c80121b51a80150840e103056040589040380105002d01e040c000d04e0414112a5440341300d20161111040d45850003d48140c0c103540000c1c0710808040d05160f9108001c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 435866366 1250 435865116 435865139
    0x3020c2a010305010e01030c140109050d050c1f0206060d020d02060d0e10021213050c030304031401200409090c031401050601030e030a121806090308150604030c090b040e010501 78
    0x10007030100380340800100300544000e1049040e1b82d408915080e005081c8000350b0401c0303e140c420300781080012400864a03860b01d64500303034460300c2140100040080003003001030040c0ea0100045141010a4807005020340c00600c3c02d030081003c2d00c0e5074645200300e00210b0380c0b4046549000e0b40200700000c403004a2907052b13121404e0541c0940071b0301c551440320044142684a21001440700c9440f52001c100203000441144c404503200f0001c803021002010301290558205510039a04d0b591100f030b806060b40340030f01542a62078040c001c0300803108504210040307107000d40e0040540070341c0ea0340341d548104030500340c070f8802131600200304001d040445134800d03018020407203e01c0d00283c100942a0b03407000000041c4da00400f404d031965150881e050143c5001000440b21440d000300c081101e1034049400351042856850003545c2c1c95006103400605015220116002c1d240200750400c0104082824810840c0030385460010202e440d100c0c6500040c058400c02290142d154641400002c20f0080c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435867616 1250 435866366 435866443
    0x1512130309050303030408030a0b0d060f021c1107030c03141306030b090105060318100c0e010807020a050a141e031305120709020702030a08210c031603020c 69
    0x20341e6420080740d1160305041d100d020907500281480410701c041a02d0b160560030064501501510000039940e407600c5500039100318001c8648250ba0020740c021440011000200845034040f0043c00b01c01045801a1120712425070701400b04410085403208142c0b2039072070b02142203002d41032582c59040c1d03d0001200048103114403000f003031601d0202251810081012412504028451401c507911070317880e60a000034110401070280501c202d080b070003001a21544a8946807569064119a110b0002414110f07002d010801950b0140305040300150000490030341542d4002d03150001d0f9000030303050515019050508482a511000ca00340042c41c1c004064000c0c00d02060441400a6460042c445100307512400301c8401e4200090510158090380c0042801d1071015084541c48401c98503409642e130040c609849402505042c6400c1000d0701c840368981050401c0074562845c01e01c56050403d01c0702a40c621014181c01150b00382d4425070610203607203102c101d0102e02c0d20020210311901c4861404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 435868866 1250 435867616 435867623
    0xa0c030302060124080402040c030207080403080301051215150a0b120a06060c210c0b0405060709090c0e0108060f0d0318120c0e0c04150816051305151213 68
    0x1e0101c1106400410507401c2d5808545d884800444e1034030b400b030201520740c0f000c0310782c14550204042000100308200520055015800b006d44a50520701040300c0c800302184083d40329404803200b007045110030b075000c5800840d10000001c0c860207250100781c035002c4990100e600751602080d141820201801c04903c14007901100300111512501e0039034030b004d02048044c280c3c261001c036201086040d50788654000f41c80d41401110f014080e47c076818459801c503400c4556400c0f41080c000041e0700044940080d00b9010000e00c900c0605150007485003156591041c1040606070100300c958541101180401c10007900c80710800c400c909020b0501411b04030141518103405000245041c04071018003401c43e441540201e0382c43c40c1201118003207401400115401104000c0054012003009982c0d4201040c4e0300d840310340345041810a00c50540c15400305003070050410242c9141e4a64007088001d84004443e43c40c1603a40d260340e014058041c2400842852089100744083c441d810b44076803417030510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 435870116 1250 435868866 435868889
    0x10b0a18260105090d050901050d0609020f130927031205130302060603030c120c010b0301060603091b0e01050103020a03020c010c0810060201060305030f070f05011b0e09130201110a0c0303020601 86
    0x10340704e860540d69207010400c00002401800000a550300c40c00040078200540c0202103030a540350421041260300070100f61b17080744c40020305000c0d802082c00380c5000a084d441d008001c010551104903203100825820000c40c50b02c0c041d0003c0030580145001004070b0381101c0108550f181c12108040800c0c04900181c01500c074400001e002c0d840c0020032140300e8002d05001d171074110f13000d00a200d81500f1120101d486552030303078002c0c1c410f40c40074031646000b8207965a01050308440b9040a15083d80120f0b030240080802040900008201014403411a407003882c00507a40c848481c401c07402400307000800811942403040208465600840c103074020301e0f808407403014481c0e59403c02c2e401c030740f110300c4010590b0b00103210344001d0034118801380c82c0301c0f030040109848071700701990340070b0840321860300760107107040003283c1c0990440c0e01400e0000710082c1542d01a600d8100b0107030ba1810000854402810003103525850502c441c000c3c48139509243e4000f40e004001922464080d480300c90034014000040c0c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 435871366 1250 435870116 435870121
    0xa0c050712230c030a030207050f0d021b040203040314091305010e15012a020a0503010c11070506310305030a03140604050f1f1a041d010b0a18260105 66
    0x4110500b01d512020a50f001035150000404040d17019400601007503850707008100100c0e004110074881c1841a080079405401d80719207412520f034003031401817030381400b441c0f040c42000700098000204c81e4001d192140504c0d11000407400040c0e2144089202a40c41c600301000014400407918480f4000d00042c4119000890500011100c0811494440c2c040c0c4426451100c1c5191086e01000c4040d400900030384502520742c4080707420348400b04003102c005925100200e410f030b1014070650026100454003140740010700807200c0c1d03c054103401c0d40204040d4841101c00c01c04c200000301d0004503440300c1901d403100703110701e009001400f1401c44a41e07003c440c0700000d042da240c0751103500d10a0710342000e400788a446a50f260301c0f083c2701c40603110003055540d410120b09000ca014461040c141d4801d81c80d5600d90401903480083c56030180244010702d10600144506810a000ea40c00f80d07000d03241090110300c045450301d0084806903c60030120a800e0030303418030084207000c1c0072446400c4030021f02258 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 435872616 1250 435871366 435871427
    0x1e0a08030c010e061b090d081b010b0a080307030302030603030714060403170c0318010f02040f18020403030504270204060e092505070c0e09061602070501080a0c050712 74
    0x84e0821551010401c0d026110b003030715107110344041c00c01110082d044a0450b43c0e01d90b241a030540c0408400c01521804480b0300c0307001c42c000d0261005485041d501b019050f85132180700c640e64080c0701c00c020f00381500840024400e071130400039100300a4000b8290384460a907080b803252174070010342c4c0c10340c0055a60a60307024000481e00405010700328248a0724074540c0d80c40c0c0700410904050742d1141d0700b5500c650f030403000484c560029102401c000a40310314028a01560910882d90005080d03003100e00500c81000030a4100042d101198241456043c800106030015040b4010301920000403500c04607000c82c0046d404074012030343c80e42c180e82c0c0c504152154292804070800c1000c007004000f10300e640d900070711841032001c0c15074544600d1300e01c0016034aa210000c4861411038020426030302c40000c202202c403c141038030003035048500182040500300000201002c0c0020110300f4003030384820041009603c070f0011100047e4100c0c014000781c10086030024000c80f41401c050541103850452980744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 435873866 1250 435872616 435872623
    0x5070515060d030f171008070501170a0504020a0801050c031501020c0f0105090103021b010218120a0209061f030b0406080114040f0215040305010f150608061e0a08030c010e 76
    0x7040010028402c02603140d90451380380540002600821201d203005400580c502c600c0c15025180b442d040200c02400d02c5005171800c1303030aa015904000c5051000c203141c0314503101c1d254000c01460004503552b6500c0c0041403c4807060360080740303250700c1c00c4d0420206075540c001031405900380791034907016031824034012607031072859840c0716a01000b2200c00300d08641c010402050b00d40e80c18180541854074401d004080221100c0761050315940000b01d4071084040d21501003135181d0211a0645012980001c0c280d82c1e60710410001d000f00700c0c400205400c0c0c1e54000b171070b020000c410303204005440c8000038020301800d00e145a083c0143e003802404100c010040c0107404c21091020100e03c2e29903202d4552143c00300c100c0c40e00740c0e0000b000c000500c04181c0c0c0d0390000c00203075005c0c1002199440c404100e01d4100d6000035000348034048152814442c080d0b110070400d800c10422030fa41600c500364a00b0102510703465002c5664032001e0900009031100f0080068a4403036100302c02041100321019107182c9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 435875116 1250 435873866 435873871
    0x100203091507051f0e06070c05060f0a0e0d020319031e09030c02040204031b05041b050304080c070f1403010501030c060f020c040c09030512131502071806170c09060607110a0605070515 81
    0x107240c2282c000680bc0f005550390150780034403010310110784222144005030030301488418070801a00b001400c4040c410654800c41d11024407403404100c402c803141300520111210b450580402510341d42e070682454402e580510000d50010402c40d40c031a541e151800110068621040440d40d4403032001800340340c103224000c26044060400006481540c20031200d03540000c0c01118061024440c0304000c1d001002000301030310245a42034100360070009400110f840c010301c904c0c0f00741c2c1040014000151a081000708460071410100b26008580c04180e041441c5502d000d500545002e0402c15800e910003612421079014105aa40004400340800500d1140104010004072000001c00c0306215074405040b06421500c1652031aa88442541700a6405031312012081501d81c0c4042c0000741c0c002c8207400d041e0326070f0801130580c1c0c0d10400101e1942c3d00d0040244c1d11032000410b60a045c810341185a965440c030081404500b146c9404001e016504030303480a075080d1051301c000001d00baa03502d038410f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 435876366 1250 435875116 435875123
    0xa1205100908030601180e0108070602370816060203060f030a0c05101119120804050606060915030c0d050601091a070804050301020d0b100203091507051f0e06070c 72
    0x1499039a8444c01529405880c1c1c01081c401d4040801c00a60749030701616840c060402e410107030980d5440c058000b032078a0104032100c4a0098040c003070100d081c019030389544100000e07242c00d1070340c080c050410f00c5d454003900380120390302040d4248400070410706030700070b600c25181110840745101000041c5a66428a040d00400c080004e14052043d03241001174506841c900b4609004440f03030700c04a10781052071300c0300585a0024032030780329030030402034009443e020f61442c40c00c09c0b03c51415444050b92010007400f0940580e90028081025860360500700c803101c2903814065680f400d19403005070b581d9000d07414004882c0c4c81c180201c2ca03258415000c0d50b0441351a500e46a19010703501c524189a035003c820100c4d07114004110006190310280044d004031703a0045030001d01a005e0409102401c5200350700c1c20119082009030380303082e560382241d0400218152001a442f4240c500d041480c00c403135a0782006080380210321601e1000e115030444021035003880203403030301c1b910303a1601981c400c038043c0b8008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 435877616 1250 435876366 435876383
    0x190201031d1902030309030d0c0201092c10050a081e031614070504091a07020d120915060f09060b16120c0c080a0506130206040302090705090a12051009 67
    0x10b1141509004405101600080a403803a0540540002e450400c4194600c004660741c004803a09560f085101800103099500c1c84414074825029944664240840f8400d240010030001c03800000c0c04c002e400f00038000181143e014070362510b681c01c0d0b0f580000404001d00c810700d61a0403000000c080700352500c01d000361140d0221a03043e60354265040c2a00d81c100d00c11031154110000c0c3c00e44d124062401c809014102030042d8810014141490b084000e14030780a561003031640d100e81c140c0c042c1b585018203080c154006852100c603d403c80a1090b413015014089003811004144400900b80d504116400c12104100c00c84c0ea940c1642e0707181c004c0e40340c0315991000c10f11052010420030103580028211078900780d86910000d654192904100f908603010542c8445000c000704101040300a07000851208141c40110312070b40001c0d82e500c218040240282032280109021a0054042c0e0301c00745801011661084d85441c52a0320083c0d01c00000d989074031460b01100307842c4200c1e209080c0e40d1600245d44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 435878866 1250 435877616 435877633
    0xb10080f010c05030c1b030a050a1101050709120303200301081e060705030c0714160905040506040201261905010e191107061506030c1704110f03190201031d 69
    0xa817403da00002802d20f9006034148281407041c1d010300082c9029025034480310b8aa254642d8000e016035100c10032020340380e14003401d11000750f070030164170030803582c4555410070b240c00d203454102c010308985040385080e00c2540b80455803041d110780145060303030400c1003140c4121980300b05d03950140c0302d81c82048047c2d40181d0046020b00744a880207603801925440001d181040030768400641c00906203010000b034110707001104402011410303080040ca250301c07051005040686503031b030302da0030054002810b000072408104030541c0040c034001e000345241400800b5034a046418103801c01811003900c54074515100c00810007402c44041a40a10244003820707600d900026031482c02041c2920340d403007103403400740482800031341d00303019a0381d02e0a103540710600c6142c941417024080c0c42e070720360a11050014804a241d200c000240c0282d40c02508000c0c00d4070201c6800c004500c0c0403e2021907160140200b404000c2aa0031421036158400e200307076010400b10400c01e46107003500016154284443c0c005094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 435880116 1250 435878866 435878881
    0xb131b0f060c0c050d060605040608010618020a17130b0a060b0a030e01060902040611010b030c09070f030603121d0406050a030204090203071d01030b06010e0612130b10080f010c0503 80
    0x2c0d0182d498032511030444490785610000740980714102d0125000c2e91509000d204508160113600010400d540007880110b09051130303044206100841501d08942c003003940c01505100c0c2d009403402d2024440d43c02c02c6810a628481c070100d19145040d030307400c1119008038000b1640c521840040303589000c4040d04040b5142c40c101c001d0315060105800381c0d901d1300d4020828860510040c0014051601d5583d00090710520113800d58145030b5140b44250001d000c03444040c6c40f410120b0b40d02c102c1c1403501c804140035240e4150003c1c00b0f942c001810f40160484842e0682d50850780a000c0d2a50844030410340f2000b8008000c2620700602466070002d8007002d0030001420507412404a07284001d0680e165113489061402c44205209124410944d035503004206020300d400105401801c01e18004d80206107010205600e40714003030050100c03003d6180000d440c0c449444020154943c0300d08030766010300342034201d1503000b00c81c7d0007160360b24010b101c0c9011047c81c05125504000311a0346031541556140e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 435881366 1250 435880116 435880127
    0x30909071101090506090304061701120201050c03161a0a0507022d030c1e01140112060905060403081008030418020306060f0a032304050a020402090d0b131b0f06 71
    0xd4240d592203c460800081d0140f20030b511401040c40190340301ca00e411801090803010701ca403500d080100200600101d0038180c5400c02040d021300742075a49000751841e103032441c881d4203027910f02d420008240004114619048081481a040b010240d45c0c444801c030310200c600c152401d42c0541c0c0114000b22005211041c00098582c0c01031000314080018001203003103920406180209401801203140011071110f21a8041050000200501c181e0a03154141000060003034a104150400d59001045401d07000481a075034044180c4551b414240380c054505030301501d82c9542102860400300d0f644d500042a0f42c04c50380401d0710688401841d0308800020350000c0e2142d03811190410801d01c0c40103140006000111031543e00040b048800c0c400d20001c03038280140321341c100c4d09100074040441c1c1e0002c0c10141c216012203005a8a02400b000150348903c801c00080802007002d040204101c441e034003071003a40b80281070315110318141000c0c180c01c1c544640584441540d03a17400500115100340c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 435882616 1250 435881366 435881387
    0xe01030c020a06090b01080601060906021b0f030d030e0f0f030d0b0a0506070803011d190507090f123806010203090a230a0810020d0f06080615010203090907 69
    0x41c01512800e40390383e151101602d182d0001941c11020b51030040006840c10800e1500511540c6031008210381400002510340b10402c0034407003400000d000b0b8145699407214148017440e0020f0854266180b83c0700082c018103085034568041d4095003141c081c0e00140171038180c3c03905060300061846d22001040c540000c200e00c0402540102660034003007100c0d15030384000c00c9101e00a9503181d442e98501407801c6501003102d4070707003500c8401050900010801c185101205800040300c082100d0b600d4507070440f510205607001c2424088044000200c00d0b61590195080b03500070150329035500c1c004503043c040101e003c2e2080c003034080c1c0d42c1103281080105803440780d04000144160ba261010300b80004d175001e415038005443c00d9507460002801540c60304e4071680f814005030b0f0085500c0d407030090841e03180c03018403032092012500050000b0940201e58049803000c2c8640104000c030070340741d070305142e614041207a000c54580400005844151b000006550800c54000c2c400465651190b03021110407008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 435883866 1250 435882616 435882641
    0xa2102120c010b040207030206040506090c0112090302210a020118030c02120c0904030917060609070516080a0801030b01090207020f0103020a030f0501150f0309150c0912050c0f100e0103 82
    0x80703c41da01400c0d07071180024103c29000f540289103500b070030b0501c64105000038140b12000c0d88062501c1e10f60b641c0200da009038440c800003000691301c00c075080982c00c020450b50342e170f5000d4182c408400200301401c0050b00284049600130480c1910003d00d500d002702002d000680440e0f9801d0110b001860078a501e40394200d00ca00039142e0031b04140380861429901503508401085030907800f0320041e81c00c000705186105800b0001e0005080030004151a070740087c01e404200240094807059440410740c101c006268040c41080d5500c1c0444001400514203000480f84206414000180c40199000345d4038180e800510811141e00007074010340007907122201c8001419199240e01c121010148a0345009010803c07561200b03000540d0010070304d81601d6003c1c070915290201d1000442c45901d044281501615000100c600d2511000e40d9004000da0042d5000c8590052030000c02c54049450800034405552028000f0b18400800521103480b4003a200081c034201c01740300c4035600ca038020380d40c11600c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 435885116 1250 435883866 435883871
    0x2030304030507090603140102030712050604140c1b070b0a03020a090308070c0503010501094110091b0c020405250305010e070203130b0c070e01080a2102120c01 71
    0xea0b56695402c2c1035181e07103e440c202d0b40d1524104103010442d00002a000c1d51040210b2542c900014050201c06401041c480d44943d00c000003071075a20b865200c0a403404021400c0040303440c010500465550004040b05003082c03182850309506c2000150709000e40350f03d51202410300b084224210000e400009800042045000d000004156130500070002c0c0f60150680e480400d0030031040c03609462040e4441d100c9907280c00170144004011050b1000d00381b140e040e4480d5a40e01d065a04146440c00f00b07280e1039039072481c1d028448804482205602103409c0b452042c0250100c00840c4548c44000c4940c54000c2119090810018605940301e0b950006482d03600442d051400b81000103101c5a0b0841d080c0442d540744014000d2181c51199a41d00141c0e40c4021450454009240d840c050764920461020740c80104200707181d104180903140140403a486110541d45e503441200e03968019020098513081007941c00420300090300496000800d00741c1d0002c2420780034044480089038400500200b0555 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 435886366 1250 435885116 435885119
    0x52205070e04060b03060619030f050106150f030c0c020d0813180b04150b09060a050d1406010f0903030e010f02030d0504030806120307030c03030504110306010f060909050c0d020702030304 83
    0x140c01204841c0503d00a0800080407141c000c05c0c540f4103034010304650b1103900c10180b090314025480da2a04141c95119000c240307c00a1031034200c0c050080c0360010343c00e0704625106540c40b580d0110488101006640d000e021030303d5440c10035942c14aa003000650820038075400c0b078012540ca04001c001c44015901c40380c054968841c61001001901041d0b4213200e511889411114031f481d0107040d04600c0c60b0703050202aa440d01810601511032281c503140549030108075208214020402ea6144d214054020300117510500d8814402040031582680802c0e03085590b1442248074010140569074540c07520f191000d40440150758800341034040348114803080140e42ca125403d0700590b4002c40c420344034003890741002000c001018984078005d1420340d00034401034001c42d5000001c445000d41505000038992240d0500026074104060680e0309441090000122400c94200784030840e8603640c0c401c81242d484502c8003090300c0382550008480f003000e101c40d01c00d100243c0d0040003140e20060481c0d11f0725 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 435887616 1250 435886366 435886379
    0x81909050c0a0605030108010e03090a05040b060f04030501020406110c09150d02210105060d1a072a0302010f020c060c0c07150503010906120b041b230a060305220507 73
    0x11450700083d00141000c0010044a43d007401041c5c41080c2c414095403d220b40f20002c180c0303c003482d115039441030b80c8648034442c550712060100e40f004000d0b45c07000d96a8644905246000c0d41c0944a0100000e020090b21521000b001c1940d40e40f02c0b90042004405856680700040a0701408035410340c40401c000c02c1c030005a44424481c038001444850f6500d40d140c150071002d0031544000d100314003400030300c2d07403810001e81e800100d4240104881c80b039040070389a0000440700c0052140070600b180d01500062a5141e0b181103081195078825402423044407120180e5205034059803201080c0f82d0300c100c0104040c94071580242641450000845480da50750720300011051203041400808601d0010042c41140901c4c0120406070109801e25141e0300c98640d10f05d83c8080b0000c201602c45c503c104c070020524910502070800618a246041100103075a0060544009403001954820f564030a0000780480c06409801d00c100c0130b25903070203490204101a100c0702c1c1c40d0000b003241c503070240f0700000c41d04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 435888866 1250 435887616 435887629
    0x308061e0316050907020304030807080c0c0a0801150b090a18020f1308070f0b0a030f090204021317061312031b0908151519030f140d081909050c 64
    0xe0b900c14100c103200d85481c060921102080151080c0700315081040301f070002c01ca50380100c440ca954800c0f025903076009a140700c1d90030006141d48555000480d400005001103054202404952840c030341403c1980da501035821980c031505840b103400160302c046c1001040981800e440f4201441c04002d8030b4108884010106503110901d030130340d00902c0c010240304d101d038100304105c0541410400c2c1c540b005e04000481c02a401407009042c1055141c0059407503080082e0400310b5035a81c003400c00d5441e01c0141c02441000700c207a003d007158110081104801c0390b200018101e018070030401101d00360880f0342d1503400316041c60302030120515403508070003125001e40c3ca0b000811400c146d55204a62410205510300301209200800b210400300e000f8420701030440945003000ca80c0c1111124404005c1300030511086407a1380c0013030880345041d81d842d806d10001c101c400c015004920700381d854007440164160790321074058580004580143c50140c08482e01a80030440243c050300c200c81004200b100090305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 435890116 1250 435888866 435888883
    0xb040620070f1e180204030c060806010507020f0d060908091c120503040326190e0d081806011707060206101e05030102030406090311010606170c1b0a15090308061e03 73
    0x680c0006c0400c14440182e5180c00682410700d8000802e041c01d8000030040c1c000c4810180c441c01d26040c010200d5034680d0b07100640641c1c8001e052202901e141401207150f00074002d5240181c0300703103900070700c04094840804500c5500106010360820740803c21601c07900f00510132020300000d20000c801c0c941400342e480c403d01002e122102060f00d8001e500420b4608014540440f860030071007954001d500100c3c4030b019040e19898440ba150740d501c260a401342c4901c24010503039001d408008142d4911100b079020b030407900601141c0e08a951124100d9854400301c0e103a0800d100d040f10240000301d03102882c0000084200840406191a07074001307402c90340295400c95441d0760f210350303140c200750b002184040c619880200801c01149040e50140000400100d10701d19103900341d000480806110303041e18000c0c0e2030941d03100c10a4a401d464250380f64103c0300d069800801140f14941a884540192101c0b0b6605035184441344c0c40d501c00703101d003000d1810440001d070829813181103402d8030204001301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 435891366 1250 435890116 435890159
    0x120706020301080d0e0607112101060e0f0106210f020f1803160308091201090c06121a061810030b130504080a180b040620070f1e 57
    0x107076254540a0a40d1400d04a01d00e06000d001000c02e000c5800da9038041900c2d440c1d60401c1d420809102c4000c0010482401155000410758070620604c800290560010b01524800c801008407612851a00c0c2d441110910415000401641c402442400580c01042082001020200b8841040900e06090380c0020441114000c40411a55114910129003400404090300940081c034291548002000c0e007900018107200303000030705801c0c0d64441d5043c20b40410002002048040307128070b07007029680414425034000803038024208003006414490242c00b1080c08196030b41500c0108203010b501d41101600024142601c40c001400e80c1701c45040c207140d1441a50005654160001044030751a1104c1c8100c8280303150204001c0001d85003000c649440040741803443d081042c110281c048111907821600a80c44040b80005d0241c0d0002e0b0118946030542a0307030705c9840e04d00c4c0d805555405083c400c9140c056041c803802c02481d241c690b204001202480c614000990712100e03911030b0000c0100041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 435892616 1250 435891366 435891371
    0x120a0503061905060a0507030504050603130210080105011b0503070b010b0c010612080a0804080403080c0102030a0c110a0318210605160c0b0703020c1006030c0b0a09090b03120706 79
    0x2010728600340e5040160900c0c0703064071a0045082c02d01080042c01080104424402d00213440401c0c1409281560020079004000320742d64904105120b200030540c4004a008801402400d0b0300107008600c804d05954040e510020f1101c001c2c0c2060084003040c0300300b510746010401021012071030806e13000740a001c6007030751183d0b201c60700b140440c21070340c07180e1001c00a001c1001591000560711808c0352081d400f03914000040d600d5a04040c804d6208a6000074240701300066861554a0190042d5201d411005400c010516600c8815600300c190880c0009070ba400009516000030302030030b030410300e05403405030008146464108503c076103602a51355042c40c100c44015a410045503018440c2d2240f40201040c9076245510000f030500165440014080341051000441d6584603505964004c0c100d40c007110481380e0280c684500400450000752002d0b2940310780031654035102804c4a4041041da9501d20459141001d10390003031084c0002c0c01d034140a8105000e80041464010380301c0b913070003074100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 435893866 1250 435892616 435892621
    0x90a0609021c060b130c090b030705040f09060509060d0206120406020d091416050d080a030209040504031e020607020a08030402041b02030c0c0a050d0b0402041509021305120309010f02120a0503 85
    0x40201008800700a51005c504180700030290b558000d00410441c1c1e4000e40f40c0f91251150002600c40703001d40c0c3c0082d25a09001040025042030a400c0390301100d100303035210840d070346424007408446801c811019400c100304010603100c2c103076074410302d03a0b00501809005003402250121182601c50b50035083e070340700151240c0303101200010320400100c010100c0c159080c0c2c41c50b29000c00d070002c20000e070252616030301040e031002003030185e0101d40320040010302c200200d280c80e00d0051b1640110121034081183e0001c50001d465000080b11801805035400030300140c031031951009500c0d4801017040344c1140e100d40120305000748400d40300c6074a680c103030040c0d82c948100090191810054944151149a6994003040341d512415a07110155412040505007660b450000c2000b401245014102d4038000c601c0004840344941d01403c80b8035000e011520190ba6603074200048034243c0ea03884451500100b00d1100d5640c041c1142000207a014010343e4903420821000d1542d41d04020150380208500108 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 435895116 1250 435893866 435893869
    0x30a0201060306110909010e0702070e0f07180b16051608060f090c010906080a1401030312060b090612042d020406050d0c03031116080c090c03090a0609021c060b 71
    0x42d0b058818041c203804ca040c104a1400541b0181c810305c07900c0003864a03840800c203203610901404020b44110030406040e03040010a1000a400403a90000003c034000c00c030350b0b001c850407100d5404a41c10b0140c9107041c4071086440450032001110226014800c1e050301400c880d0324400380100904410002e465540f500d42c02d65401c090008107940003582082c07552086076a000b40c0185c0c00da41403407400f105640d840c2003006d40203100d02045820420318520000040503480215500c011040c584c0611a460b42c4a00a281c1400791244c4664800000d0281101301c0c0300c2000340345d42c440e003e070800b030510900c82803241800500c4214624100c1080d2561a820350826001e1a40100002c0d40e441c0d07221381c0342e074640702108046400020b04016141e00d0708030114004200565034091891030381c1d501c09a5812105070749484502c040d901800fa403800141c454004002940d01c19001d0802800d80901903a032103000401c1228000c90b0b001c8042d00007424001344000072500c3d50761007a040040d81088050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 435896366 1250 435895116 435895121
    0x2040f020307110a08030c0304151d0709020c03090d0206070209040c030b0112150b0102071d041e03090608130803090a03030e0c0d06050c0705120d0606020106120f0f05030a0201060306 81
    0x680f101e03103074494110344001a900800f182d03403100806030f40c19201d4a483c90182541c00c14594521060740c100104041e0036045580c2d40541e441c203d00072942100e98900a03013050780a17030207050030642c00a102d62105818205003021507148014141340c035020b116400995030b1201038606503506260000c0a004128002007058003512038000005400100380d911000b040740482c1d00015441d03103801051000b64020000c040142100c0800d00f462024105400f49142c001128103072103041c00071407081c00c21a01014000d0030260503a546000340c0d820060152031403070303000e40f640d0480401140b41c1c0c404912400083e41c0151880c401601d43c8824506000f016252014505800d0784c00201d50809140d450001c0d490f07000350b004d440402c01303030750740005550709018624018085003e000360400040091000070500d070406284100b00d00c0c0e8503072904900302d0b40303640142441e902c10044182c004c00d407199440c0b20301521034824a03503103c255035109800c41d00a010820b0240c0e450341c0e010301c1000240e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 435897616 1250 435896366 435896387
    0x6060e01060e18150a05150a0207050d081b0f0d090509070305010b0319020706050403090e0708370606030507030f0b06040608070c080a020a0c0603230c0702040f020307 74
    0x44840d1015001950b162080311480030701004c0c551041009401c4150321685070b80002000000c0c24824043c940d15140722440c1d00808a40006002e202c2000c2050702e4003003c002015500901038508020382c01c041205442075202046009102e40c2c100010340d01c404000f403840c030401650722410b4507440c1200b40039004802804000034581000d00610410b98642c081e01c4d8044d85002880185144041c10b10001b4451800090724a80c1440100301c10305400031507090440e40e844120541c99035405c3c1003151560b8050f600d2030034800c850300c4290002d1002c1d0808440e000f603504403e9100300d01442d540c0f000c0310105d5000c640420745407010480d0050305485a40c03850340724084140901000c0d000021203e10403400340106001c01840031070071084c0300d694800300040d44a10701e26552001014003079921210131034115150480050042040ca00c02e009111a070f16005840b80c0f07c209000040c000c1511006000d400c2c4103c0521981025076154011622649030384c000059680c10000401804603821 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 435898866 1250 435897616 435897619
    0x304050103270809010c02033304030e04021308060f040c08010e19030203131d011409071124010906210605040318080d02100c020c011b06060e01060e 66
    0x414030001210b0b04261460a0b600c00c0109a94110460042c0d42042c014140650580b140350f000485159a40003441c06901c01d49262000c64840c0360b0403170308200022140200028810500c149260030513030080c5c0280030303803482d846407416182e0718020b00d00f00c0d04940c0c54a528207501c044c030091081c1640d90002604003440240b00c1d0682144c0303c03070f0751800b2001100b1844000c0c18000381c1130510038020740314180700481440d08041c0c0d035240000da8800f1417031784041450003aa00002100c40b5107100d9000501c0003d0120a02c5a036403141c181c80c0781c201ea02c0f0095640c0500d982c0600c0d01040381040204203030781e000c0000e10315410022110704896041c5c01a82e104440c05448105148034a4164080c1c00c1e03002c1004501903403a0701e4102c5007000c0d0264103600002c0701040106211002080c02c0d5030f901c0c8a507003244e550503c0c0c5e105e0350041c1c56240394541c0c003580101803019581c0d44a0400b03501c00071507144024207007010a40e0b400c400c03115164060401124208014418503a00c119400e044600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435900116 1250 435898866 435898901
    0x503060c0f031f030f060605011d0907030603080310060809070302030303040b0a0b03010f09060b091909020103020c07060c0c080303070e0f130c020106060e040203010b0a0e031c020304050103 84
    0x1000c015040c05403248680c101c031100808800203404100c42911280d46a000c00d441c1100283e0382c3ca0102c00c000c0c51405c04030798003410f003e4003080f5940704504130340d440c1042032000c024400b403c00c01d2000780b5501908060800d0740f5442c2c003001058181c40114020f01d01a49201758081c50130400034070f40d650160050070590080c003030800c0035a0740003040d00e0300950060050012038480d40c851000804e600101150036500349241004139007400c5c0d04c04034804d0700a82e401c0c0014052502007220001080b1418425038010742d030140e50010140e40500d10041c81070400604c1d04849a21007440e00165601c40c0c000542d2803a001d030204004501030600070f0003513038000e41c25810300c1c0901915034031102e00414040d0070003040100166490003062600c03d412040200708a0515100083c080c001e64000d010100780d003101814181d007024800c490480f20304540c070604115214904980040302d0a44180d0b040c0b049420b64609030a52000104504030560001c40d540c078940b80000d41554803041c2c0881e070011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435901366 1250 435900116 435900121
    0x52d03040308070210200105240d0605100b0304110a08031201150507150b120f0601030803151002010609150503060f040302031b1f09030f050c0106050607030203030709050306 77
    0xb080c403015508160340c103d038880c0e82c04481c854204e486191740c0c00c41100d0b508011820440000c8107501990240300a0340c1d00044203100400314011070340c0b040c040140c00c0200c00f02040c000c900a40d2265400c078101135002a61a941c1e440808101c1c0c00984080d911400300512401252409401d10402070080c10095030900c2e203051030b0b5261070001403140440440342c00c00c40300e0329144524125000b0903071241158a02400301e24124000b41480080180200c105402600080200050701c00e900031051004084983c00c65039840c840781c10191441082313440c0d0b00c2805c44142d0303441070070410000e01d940c000221a480c00d80c00714107990305200c56550740c0d0b610490500c10380d20040b404680c040e4400b400d1070a1516285012441e40c404c0fa0011403203407040f0010201150000f00d000300c0303500e195623074801c0c1214490106408a5030440d000401042c540f012040c0c0031402840605018403407100001007007607880003c604607912000c800c80040c1c20001c2004003040e000200701c000742000750001c00361032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435902616 1250 435901366 435901373
    0x9080d030b090a1e09020f0603070f02160b0a03150305030a0824060708280e1206090705010807030213060801091d060109110c01090c1a0901120b040207052d030403 72
    0x420403489540e90380e440c5c103002819510380a030405000803001e418656a4501404020180e42d0040113400040c050201c010481640b091090700a44000191041c540003140e1011b9005002500c0c40440f98918038500201145080c40603280305911600d5000c0a40303840039940f000715170925610758401080c1e00c41c2c540551182401d40c0c0344039a0000702e20741d803078403007030f5113108044140003d200099184102c01c9070001c0d84020000d00d540710540345a4611403d050201d52502002c075854071031507006030070400056200b04606d5411078003e0074010310f0590b1001807001846c0007a00013a0220b00f01d00c00400030385050380719500d0902d01441c54a801c1440d000d4802e51076201c1841400740c2a170b20348104040405000d0101c17402940d80d0300080002d02a10f10b006414000d0318170941c0d0b03415481c102c01d4060b00303024004076068440141e44080b8800c1e009600360700100111714003160403d41c03d1086100150003042000d020f1900c1a44a1030425003a004d4041001c44134174005407250014802003000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435903866 1250 435902616 435902651
    0x14061801020a050724050412030e0105150906060d15061d03210408010509100c021c080a2d0c03090201090b0f071e060b090108060406050709080d030b090a 68
    0x1c9607004407607030903442c6100b000041c1444c5c0c1659000fa018981401d010400040c1c011602c020000d5440078000800c2c0070722843d00700e92046803200c02e510a5614903c3c2c0c1441c00c2e6111961064000302941d0030a421b0710b275008210b5000e00280a01240d0590701407000c1c50f0001d0002103001c00a41c0e19064000004c40841d442d06070070f2414000d0300c1d49104500e0b0040e82000280c5000d095107500030052407428540c900c2da28540c510202090720f103005810b005031403000c611540489080400320310020148001207582c0030b801400c48d0b454603a500c850105150b441481a101038000d800440103440040c44142c0850301069058001c1c075150603000e0005076000104001180c61400003a41c49010389201e84202e48a9044014035000d4025030003c580710011500d6440030340560ba08100398001c60051080300402030042c0340255001100280000301d0580000750f02201a02e46408581c2e0f5450780b05203010649400800400d80b02c00030300d40d0030705101507200e83c0000c084100b401074420a1341d68460 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435905116 1250 435903866 435903877
    0x503150c070b06030304090c02070f0e1e090312070c030f03060f0b0f070812041709090103120c1b051801120210090b040902071e110d02030a14061801020a05 69
    0x440c0b1a440090301d255401d10070740d002000d0945d410310140d440200c0094a41e4184e00400000c43d1a80401050201000c6803080c41029101012201d56031044422100180c00a01e110000d00c01040312013848902c9006490003030640b92516490b800381480d0290225105910710710030185080001c20218079a80005000c50300c9007003920b95180d0580794500320a1003800303000fa1080345e000901c1000800b00c41704803882240035032004460800d1060003010b0341c0c41071060b410b600c440c0a00040c400710307030480c080c40001002802e0002001e0384554410b150005900c2080c1403503200700104200c01d0401002c0f203c0a192080420f00c241e60600402041d460a0f820019024105640030742c1c0c0894010118480680b1403245541d8503155030315110b1002c0d5001180440b0205000303200c0f410071500c801011494075074003550100c0c1d40301c10002403100e003900a6209a030b16204125150000c540f80c00703201ca41c100c9504001e030200c0e00e84146442d1407803058031a1004503078810030500b107006500006444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435906366 1250 435905116 435905123
    0x614090402092404090b0105010212040b0913140c0903010e0114150d050319030e03160602031302060301091d1f0c030f05070e030d090509150607050312010503150c07 73
    0x10760203e420301c5980b08541d10400c00f2a00316140a0035402400300b1074240b01d0498009a00b104d10040a040000955000f14458400048014030064040e07250103100701c401d5180d405d42c0050803004120514600603c2610b004420340c00004406c100307410280150b0020301c00c0718000b440414602220000b041c040285400361452100000c29501d03a541e042105030107400600300d0f5280d0424400c1d01041c018000c0503034010a2802400041c0b5070300101c240c840080070706442c814911200d4441d403000e507200a20820703000241c0300880c0010f03950b40d800303980030b070020a0300020a14466a82c0c2102d40e9015035907645281d00051804503c0003242d00032411460000c0300104005000100a9001d0032140000104160422040080e095401410411811011801c030344601500c0c0c0d90035143c400d000c7c012281c024501000143c07104034022102e41e040c1c1c0b00a00102d00c0c045e05903c0d038609540100c1080480c0c00c1e100d84c01082145002c20048264140750001200c090401c6507080c0940e1140c1d05005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435907616 1250 435906366 435906391
    0x1030603170c0307121119050c130e0718060914190612120f05180103020c0f03040e010312030204050d0609050c03030f0a0801080610120f06020d061409040209 70
    0x3084014014810345840f41d034054032201a40502c600c020b0042c588504100030141f103004401120481015542800c140e00300c5c1c00380410f4101c1d01d0610000d40145440f84c0c2030f86807030f0991202c80700c0c02000780710020048041c40c4c2c02ca11401e28100e800380e0b40ea6500101c0c98506060030b11255808401089400c075000080b07600c0140904542031000d800c10340d020030358401c002300d10344041c003402c4000086018559914a2900c40118a00b503480d80030784070b00004c00904100201041d54080d0303004040548001e8101c07580a0f031100342c914030710b0703016800085401000100420800c0200094040807080c507060941c04d0904100220388881030025000d415541c031383c0103440c10b00800f8004010807000c094245e981d500c501c511040380a50207401130f0b00019a406000080641e40400c80034081d240c0340c2d098055003803520030f00c9d001940d180502540d1b140100301800e0002030b10792000342804040b012001c20803d2826808400c400e100c405194043d0b00c4013020840103070784042015901140d034840781d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435908866 1250 435907616 435907627
    0x10b10021518030301030f03030e010504170705011116030f0206152e08071b05100e07090603060b010806100e0603191409070f0605071509020d0b04060b0103060317 72
    0xc80b4241d0981c0340e400c411804000300100c02c1c030484402040849029440c00d100480c519a0100c0c22208115406003076460368480700300054000000400405000718000f0030180c020030100301e42d581c030446a00c02003541c5583c030202019007000c0d03070b00030038161030000e01040d141c10101da0680748440f038100f078441c1001d41031844145041c51003150615004560640c0c3c082c14103980a8000c12007914035101050400c01500e020758088440524583c0c0d002d809000700c0740d0020f0741400a0081542e0305030180c02441d4000c44c50600714410040298001c000c0440e0682c0b1171000500408406000c1c0c6000700e420032201d010301ea420045008a4071002d840c01a46c170342ea40c04159906480c05004110200c0c01c103e03005a01c07000c507100f20b40c0240800b03801c0d1000036681e03081040c2041c00908c02c440200d2000d000b0030b0089401038480f000103200903603000c20011865070001d50790340c0005104892045020060100f84459845a426100401e085c1004982d05540b541c049014031605008088000042ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435910116 1250 435908866 435908881
    0x30901030f0e150a060506070c030b0403030b0d05060402040501060e030c010c0201020c031f0507301e0e0606031b060705070306060e01240c0605060a0803041502010b100215 76
    0x120b80e81c1c61010040c2c070388060204080b100800002d681040c2d450303040c102c000c1510f20f4000f045540099114488141451450786d99420503d001082034091513501c1d44032003020f45070002141080c900c91009824949401c0c410802280d406030800340401c400c0c9000111240c800194241540900342000d120907559440100d190850840b0803d405000300c89a404491005620307014010b0f515200c188a00ea841c0d0348100c030724422210301d03641200341c60715017001080d9020810b044515000100802c070a001220710407101a4480404607442e42d0303490842110380700c144400c9422940031800351407581c115030364562012800c0840c01d48600d400043c058100075042140c600290350113031051103520394448000f040650709110754540014941d0301403500103000801c0c80414203181d124074105100c0ca49031007005000003000300760403105644020070495400c00141c401406c030703c505006855208907000b42500c01c120f00035800b84090042078170345250046040e009801035919030003000e955019 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435911366 1250 435910116 435910121
    0x31406070f0c0b0435040f09150b160f2a030b06060c1507020a021302040f1809051005010807050307080607052808010e060f090a200d060317030108030901030f 70
    0xf884211502c01d01585c01000007042c0002d0421105a6100d05030200d540f0b403014000d441e1501ca540c5900401c0c54400d03c44044e046014081130340201e6414403544e46c00f1745e21107445404000003640c554013003c40814500c81c24041d5808400440382642410515581e00c1002c04e10000d09000d201d0403012502d10803204c02044000d00803105440b4911389414490700181d100d85080206a00400101400404410440c003c940848800c408145250351820248001030750410031141038507a12101e01c5008030780b040103807402c05020410b0000d400c0d450000020300d00348440c0d10050207030704101c0007001440740106400307502c4080d40c10500d0b41d80340340f0b655010005000c0c1c0000248203520344000c4601641c1f00c80d01d94180d510850410310303d0703200c12040100066034140543e60110a070700c002007210300300341c102c5071003da2040100100c081d08801c0d030107403540000c1c914081082c1c1c0d030101081802401c130414004c00b910a5212891541000d59041d00ca2055590b000d06141d200d400c04401783c0610f0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435912616 1250 435911366 435911423
    0xd05180106031a060607151d0a0c05010306170c010f0e0301050f0f06030c0f060d090c060804060f05090a030e01020304050a180c0e060d050c120405010f050a0b0d0615031406070f0c0b04 81
    0x390949504201c0c51402b8480b0201c0d82c007030180000d01c3c1450101e09616114110245161401c0c0100007200e00d030b5004484100c2480b80207410441403586990007071f102405400d009101c2018010700717514040d4401a040a802400d140c031a9006543c038902d20340b1006000b941e45171095610039541c1ca00654100c003d4010588001c000c80c0c01c1c0c0d600020f520b0f9001d507000b80641e11900d014000c002c4000040c00c191070058544810319000400c001002a0084126003000a010700540b42095a21000104903200c82e92024102050084850320510401e1240742e032041e2650034401d00d07000c8494003144450140011660866a64002103606410100c05881c20311280d582c3c00c0366035162514040e03000c0d1038020040030a960034500401c0920f80180a0705140d20000341040081d8030003522104040c02c04e0050f4414444038084005c00030406040082c0c1e50050241d000344001d0034042c000030300d4400b000c11a40108904a85205c00080240e4440c0340c202d90080a801040389020703e0710402039844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435913866 1250 435912616 435912671
    0x31e09010e1c050f16150905040218090108010204060306080304030b06190801290a0510030b010509040612050d3222060909050c0d05180106031a06060715 68
    0x4090388602036134070000321042d00000780f0003061030030395070f0b0700400000c40c40c410441d0012074030143c800e002074140b07a0301818515460300505469622014086a82c1d88000c0c5c1000c0060794001605114064150045200800071400107603d0140f96444002400c4030140c4424441d0301d041007910014000808241d024150348402004200c1e4001410002c0059101d80c1c9a2102643c92540303440c1c1c41d203520020220307900940b030348802c000340440071802014000d0b213103814428188404403450b22180b295101400c03104841049210850400500d840d020f048810104003000100d035800c1e9803004281410703100301c49442070030170085454150050052401070861030345501100188100e10507045406c48010381c9903641050340712070034141030312000c40c0c0300c6400c0300d0708014281c420700407940b02c26400000301e0340c515580c0342c84030f00391829500ea0364015200d1030200802c07410103500d400c00981e0452011188140b5040081d561707610941c000b611f110045a50b10400a2586040001840002c072003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435915116 1250 435913866 435913873
    0x2012703030e15310302060705091504030b0f0c03040f1113140601030501060302120112020d020a031101020105070e090426070309180203011a0a05040e09031e09010e1c05 75
    0x514202c4c0c04c1507a0411040881100e0074100d1941510f180c16070040c01040d0594090001c9a690102c10303107155105803005600b00c2c4002028206c8a101c5101030300103148a03800703000c41428950b1401810b09030282a51024040400c18000050711039004c0a007044c0e44944591100c043c0d4500181e29a441540106500c40c14103880040001e0001d00d010b01c243c8003600c01700000c1e40c0b699411030072030050400d0789c9085440c4200500103a05a10030030f1810314801420308568001c1940403803440aa2035004843c409000c6d8200d002c103603020300515030f000c0c003e031030aa030700b030036034100041e80e80b100c0a04050304d81d914800902180000c0ca003084890b0b0030007250302656071821850010001d1056120700c41d01c15864811042c2c0202c01402100e04840c0500f110200c4a00781d20f0000d1843d84c40400b010051000c10400000c04d14164040c5a10a0903c40d025503110741c40001c490600c02c40b50b41e102650a5400c128032143c0388e80100c681c010f8401d09680e4180404110031130000038180c03070711001e8030700e21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435916366 1250 435915116 435915121
    0xa05060303030711011401270623030c060c0a030305060118180e0718110f0405010f1115010312181203091e0614030601080a0902030c0a03030f02012703030e15 70
    0x4245400c6190300d00c2c8014003406041c04800d800740c0071207495022b0019044001030310107099510501140451201c003c0940392442400310014849601c44c0000440702d810050001c024950103201711507010f1800e01b06034400d410490700143c900f10040c040c4100b1007900203218449516164414450641e850044891040c1c650301c00741c050803241100413428a091050101251000d0001c0c0c2e06001c101d0301101e0700b00790500c001507a44003d8080907408100d03001e241840b100d0020480350fa030090441104145650643c103002952049040c1d40d070040c0b004c12201d100d2101020403200c01244d401d0040c80900082c07a14080700c14a2041d44868803142210390b0400740c0ea109100b64100715211030300c911682e01c0c401221804240000c075070305400b0910000000355a003000ea085068014401002d035852245031000203010300c1c990350400c0e0700140104100d40c80542c9c0910807804000c5160f0388417266062001460440d950003c000101015201c0401d400c01000130030200582c06124200c558203407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435917616 1250 435916366 435916379
    0x30e06090f010f020405030d0879030b090715090305030403060902060403020405040507032a14040e0d0c060b01050301060215040c120b0f0a05060303030711011401 72
    0x5580c807030340401040d46482080042c84140b0300c02c4804a50011b00600311603001301e40b00380e840c002d008141e40d00c40e11142d024401e8254174030395003038000b462a40c8001d240d40480b101640c141d00300c2d480748200003090001ca0700e80e0307071112000030340c0b50881c944400020b8084000030100c0110407a0b1004103001c84410034011808004285402500c0403803c000810340c0070018100d481407420f10014005810802051022507001d41010f100b80d80050300792898203940382d020908564040700c0555482c1c105007400c4c802c07c240c1c152076400910001c069a40300c00090088281800b845204004100490152050701c90f1540c0d0865020820010f00341d40030f0009440001e40386101e07e0404a07140c0c0d1900b2100e400540c0280d0940f4161016640184113400403406589d004a00140c825036080400001c001071100181103081c0c0121700c254081d00e501e09102d2991004c0c82d601908109a140c10603040108036203001060340c0e40054689003281010001d42e044d2030041c40703400c1d0301400c10580d134030012840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435918866 1250 435917616 435917623
    0xd0b1309051b0102070605030c03090a0c090c020c01030e070b180307030c08060c0406080a0506030708030a020312160507230111071514150f09010314120913020307030e0609 76
    0x26500042c00c241d01c1d9800c00001207071600300601039034000c60300500214510a5a42c00a180c0c001480030881d0306210f502d4440042c3d03030200368007142215232a2450340c1c2d48180d051007080c00051084c242400451000302e4441c0e110b1410b07005d0403c400101180c50100041900004c00f00c0c0c04020b408d681d4004e03101e0400c1c0d00c5101190103507580611801000c50010042c07441258209c580c5582c60545540300c80c854100546005080c4a038076104903040400d415000744000c041c0390300c07141c0043d90749200400ca4014000b4000300101055080156242e40c980e400108a54141750b219561300d070001300001c3c0003038404500000c103005c40e41c40d04000d20781d000440c0004050325405103e440030319410120020040e60031280a6990240301c04e4040303091000050540d810a110003003601001c00428400720b101a48240d100365180003c0c4807501120400038816002c604948400b01c1307103801030100c0400c80081848410804031079000002a041c01d11a03070003003055030307480130958825003010038100c0d58 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435920116 1250 435918866 435918883
    0x27060b031302030616091502160b0430030807050d02040603051503062404020c0f011508060f1306060306020d05100503070608040210170c0d050c0901050d0b130905 72
    0x103032183d180405d00220f8200d000d89071011459a07242c125904040760349041422145500055114071003641480c0b10b4028035000160a5000025032504d151207030920039101c46000700780824125006070345141c4112a0320149480c0c15081001890301e40c8003084070b191180c0440031100910102d80400c01c5540340e00f24902480e0720301c00c1d580c9580c1c8520300300f40d20f80c01c0070303915001e01c03c04941c900c914284000c01d2141841c400100018242403001c0350b050f00304840310b031150710143d6480c00d11501d0035096024500203801c40000505461a0032103089451210182103003c0d2800c03010350880800c18282c00142c041d69102905540f80c0704441c02c110081c02d000c0c4d48015440f4035161011405041c001100390440390780c3d640b0300d04551103580920960f02c81c201210002c0041d504091512035070031786007160040d1001c6a1003a6103d000c80954001c0301c1d009440380d04c8089c02081101860f80c0d010041e6500301015401c0003c000c40e480740012046200c20f0448003e190504c00c4000c20700401040402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435921366 1250 435920116 435920119
    0x230a03030509040f2c030c07060816020601030312091b0305010903030b0301021801030b030c030d082a22030213060e0901050606250b10060e01020727060b031302 71
    0x81240c84120100d419104a800c0c611700e00c02e18a00c1031101c9a9103017807003c107003860510503249403482e06a40781e0b01f0b02d04542c03ca0404105c040060000c18081e064581d41164070074406003003294150340d03006110301d074890001960607451b080500705020389166000070300031051007400d002580c2c0f440c015001c2c1100b07540950200f8a8a000c14940c3c1c2810700842e05100c1c035885040c03950060f02c0c00158010119580744680510031244c0140703158404100c04549024140c9590a007407802101403446000540d6403065000280c180e030042a00e01c22054420050320030511500d0400d00411b0a85c5000c25648084c2d072080e800c1030304103040c140030385c441d1040d030b07514002100c0a665080da00d00d0a070703401503031000d40050040000f85110700c00e0480d445000a00e4040c0b14218001640302d410f40410b06480305e0301c095821140400c13104c1d0300074865110518080c005445501d1500809000088030421070310200414403009030340c0e00816520002c00780c12580d0810b5102e0410404400d100031034000c04a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435922616 1250 435921366 435921371
    0x303030c0e010c02091308040f0b0405030d0f0c030509010224190b09010504020714030f27030705150909010308040806010e15130e0a050a06150b0301230a0303050904 73
    0x10303140c1d54420240c4092003500584001001d8441c86a1002156150078060b6921030080c080420b090303886442800041c4205032410740c4030741c1050704043c02c140402c1031460603c104904902c03219601300700f10380e08640c2c043c100242c40b00b100d0801030741440c0c03c514424001000d01c0d034110400031041c0003c0ca01a00e003118801000081ca0034108085407059901c20341e10102c2d4500402031460315400420243d440f5865003040da4203030003206440c40d086000400017081011440311070b00543e810144000844410030307000032003010004262144031500540d401081d5030300100e004407480104a545911000d8110b96041d03070749080003209500640078011160080e4400064131510400c40540034400080949041406140402c20508041004032400d2510740705103501d00d440034050708400600030701c050002d244c014604001120400100382280c203526030020b1010120700425a03065880700c0840340050120341d1540c4802c1007000c580e456000c50f1158001c8100340e8050060a4410400da905 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435923866 1250 435922616 435922637
    0x904020c15070f02030f13080d030605130225030504051c0501060803030105010516061e020306150c0c0f0d0203030307090305100603020d0f0c031407060206010503010207031b0305130303030c 84
    0x407100c3c400040c0c1480010381c028084200c400300c2c29001401c1d01e0346046038201c2c490381d0380c07030b04c1c1803d224071064800d000c03c4e82c61030200700d141004140e11a41c0082142d085142c407000260342107140c0301d030f40290000c0c0200c5448140825000e2002c03a00035040c01000414109915029001041d04c24003040f02c0c25420828009002c03403002003500c0c181e070300586900d410600e54030640c1d2032003240d800c42034810315120807250750024200c15808013407a4503110003581c2e80c03a011003480340302c1c054820b465034115810041881202030109030074940c44401c0341d40181040d802c10000b0407c0a07a80b80c06075050100000b404031042e0401c54040072244200240ca4800341e0101c14202220342c14880039400840c4141505d00240c500800c0c541c10a100d034408500311506e94880c00c42c00701c90084600c0440c2c1c00301c00c06101c81a01080410300420084000f0b46c0742081503030300103250340c920001000d01a0000300804042502500c15600420302d20000c4088150307813410000c0241c4901e500721004581c40c03680 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435925116 1250 435923866 435923881
    0x90509030c1612080304080d0c1d01021c140904060b070b01080f10050403180821030112020d02011112031806070215060102030403080d090b061f080c0904020c15 71
    0x11103508407030b0402183e40c582c4005407101025070b400100b003218898004c00c6071105445043c481e0a0b201c8002d5a190200058042c020f002c1002000c0301460555100c440505c0d00460361002103a250754141c9480c40c001a9060190011802403905040d40b0a08010002c10100c080701c01030540c16008054403441c51741c1c1c03030340020389074490301f0a1100c0680001c01d2843da04002e580042d40c206110349848400040c1690210900e191a44c002074025004030b80303030500d1402481d03c1002141040d4500c9880c40d450a4850600160482c81c000d0050f03480c09a41c070156070040840003040b403c0c6c4c0066404210710084c0c90080e0350300844c3c0240c000c0038105003140b10040c0005289200303998079001080e07400400c010394050010001c00c440e04510040002100088d02100908200c4000d100042200748007480e0003010720700028000ca0264a040b0040464006008bc41004403182804d01c8074142c0c80f03c0e015a0881d100f000803040d007141c000100144640070004071802d40307101c000001c00e07143d141c0c3c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435926366 1250 435925116 435925153
    0x50d1e050c040f0b1c090b04051204060504090e030f0a09180b0609091008070e090d020607051c0209310b030304060311041a13090204030209040b04030306090509030c 73
    0x1c03680102841a414003040648800500000c2c1005d0f030010701c04810311426030305a031043d041c101c55025845091100b008002c101d03581e9500354071030805041c1410000c00500c1c078015449141d50150302ca0ed082c800c040001d00c101d4004000040d14180c1d240c4401101800c0503c1a204589010001e400300b00c403503007014800c94184201c020700d11840c1c0100581000130846010384420024129000002a881401c20000005140ea01450b6005203460081d2506055500000b10150b400440801540035404012200441008042850449895000c0c04000d02628124680258a00200c002c1c0c66801503c60880045104c80031400c1c0140c0060303074016500304c0550140c02d640b0030701c024041c260094000302080704d42c0c0e00889003400d540c2d0030042c0e0411455001400c88040c0050202c030105941c039081c9020f00780060081d460980b86901290020f9401080a02000809004142010322a8011000520108000740700c83d0403c80000f0303403258400c1c4242010343c8145000c40b4030f000d1101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435927616 1250 435926366 435926369
    0x812070f021506010305040204140115031b140f0919080d0e01120b01020c03060f0609010618180e0f0c0103140108120c0a08070b060a0522020a050d1e050c04 69
    0x382c20314511520ba0310015006040c02400407039008e900ca0703081c035102c980ca10382c1040c000c0c4008000740e84030b080c1d59a4040d04a403070622000004100a1324848a455003168107001c1c5c042d4212040e640d82e0444002d10806400303642c40c0184d200c842101070307102140351100a802501c000701d0641d41c2e4110040300a40d07649002c3c5413000c0c0401d820140c0d0040784000b940c044500c070001801914000380b81e110009003880801c5420300c40020310302c014011035040c044101809007607203052040581d18403544241c00108940b2400320f1051101809013544001600032511000c01e02d0100e848a000300c10120b07403590a00c3c503c0c0d030300080c5040c407400c6a100b40b0380001d5040300d01c64006080086444007403450581d2102c01140c000344070700c0c45120001100b95006200c81070207045640303820b0428408000c031140c1c866101511852035405100c070803112a06c03000d036514001c540d006030381c2c602d221800d0702d19009003c01c1000c0720f0f18140c00202c9100c84078941035a11408c0c100100311a0b81e807880122003a0203036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435928866 1250 435927616 435927643
    0xa0e0609061c06110d140937030908010b030a080405040c0c02150d180210032007060b090601055217042702070812070f02 54
    0x2400412258280b003031a4030500700c07201d0903001c0010303429211001500e4030118a0303034200c48001294400da91052058811900c40005a0b0f00a81000c41c080c542d42c2d0f000700300180d0008040910740323030710105a5440c1911100401007900421025090280035110320340700700c3c0465401c01d811819180f81c041902d8a00690022450303003403508000a00c00101a2003816105000e82056000c002d42d80d00180c001303140000001c8070390342d1304e45145188280d030050100c0c80d03010512480c203000103985240c0b4000c1486014640020b11a0f903a10007118504020082084110000075052060003d10382051801c0501642c9403846074403200c0044440c0d10401c400428407000485031041031812448141155001300d84071940302c0300d04034200d00200c004407221141d00000c0b1030b6082040001140e407600150345184e040d0b0f030400c2d1400003088a081e60020251848910405c902040d4030301035410788106d2500301140d183c407016801c000924124041d10f1120210707100040314055180300142440f01f0303040c2e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435930116 1250 435928866 435928879
    0xb10051003020f09030f030d0c050a0801050d0309090c031413052505040609060603051008060c1c050a0e0f010603031403040201020a1401022a0c1203040909050c0a0e06 74
    0x52008044000390080800c3c4140500c0800c030150311550104000380c4031103500400341d65180b0b924002da07000c980c2e50504417000d01005000f041c0c11950414880c504580d0103503150743c80c7e101e81d4a421600340782e5581111000c117160002601e0416855400070352141c0080074541c049840d8030040041d410400300300205145d000e02c0254848504e04080b90300b43d998441010b072001a15400040c065500c1074011000341940c5103801c00c81103a1502400e6080b032480b8260840c0c49007807014940e2980001401c010000000103840c0450604800b0062290001b805041055080c94003801c0c0241c001800c080700e0610030030074000000201841640201c07541500d80501520800c4424499608020416410750060b01090008201308142c2c10040d01c003200001030395800091190a480c41b2004031180c0d1910105020390b244200004068810b5003044408440c88411009560b10394130640d0030001c00141002c80d048204800010b0704c0440050468002c401c0e603031521502e29280c0f004540d42c07503000c038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435931366 1250 435930116 435930139
    0x23601051c090f08070506070329090717040f11090910050c040320040c0311030105130e15010806060607051c050f041e0803030f04111306080105040b1005 68
    0x3100c550011103200e100306a03081c1e125105448a130010b800c08001552150052000c008013a50b0600c0789880ca10100c48013190000004010f41c015401030b800c405004884440c0032410030380c0134107007031038601e10b03070041c11b150a11313091a140350042e6142d5400c65140d62054121440da1600300103035440b03084400010901c4200307101c1044040d082c003801c02d2141120411000c000f02d6200c58000c410890014050541c0984030701c28002200c0f4003403170640c00c0514240da8006540c031b40100312411207004440b40075103958401c4000303004210b4080102c0c158441d48401d8454410046034142c125460001581c159580c0c40c07017070080034454200020300c02d411458030600003017031840d42200145010302e00345040526112503070010390300c15003040d0410300c044c5101c49041900c000301d040281503801c002d142107081000b1000c0640c1c80c0604010003c0c0510340d0415500e440702c0c4068085180454418448070b40c1c0e80725028000d0605950503140d2210110014030035408034103914088030130281c404107404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435932616 1250 435931366 435931417
    0x3210902040b04091e0809090a0e0d050c0a2a061701060905060313030e28090c020c011119030c150504050c010f0309020316060f020f0607110102360105 67
    0x20742041400f02d81c02c6001f404582d00341e0301c491400034031418540c580090008181b80300649401c58203015001000003c1290001311031000c900e003400c90f540714540400d1050254815885010052100080661020b030b0000300181c0c00710f4195900e400d550001041641c8500c412140c102d02405025001441040891907074000507617024007a0f40a80b40068001c07401d000020030030b44890f4a1344103800d100080740003644a90f104a6401001c200c3d1003041f00c0140311602075181c440400b40903040c0844e401c1d0100c43c4080a00030b04e1030708500b1075041280c081c150301e006030500400e124181d58074080500704240345450f5209040c01f85070400d008000b24100100112000e00792213608104154440880750010b8400b0482218050030b2480c200001070b0401400a01c81034002c94000304551007144400610b160100e0510340181c40d515201c0107184942c9003c5000e8480c0f0040041689210032040400202c8100c403601441c4400501c002003005c910011a05401021800e8030070301d0521a410f2001d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435933866 1250 435932616 435932663
    0x31a040c150c06090503030603010e03091008040302100e031806070309090c110a0807050d0207060c0201050706060b0d090309060201060303021b030a0c06020c0906040608030a030903210902040b0409 87
    0x181d90091401c1c0c11500c9450303603508242e64480c0e9003101c490380080140300e00c5280030300403015042c6080c0010b42c2406031907400110341d1000e0348c0c1044203004040c07011070103240c401d114060b5035400000c0148000c1045030306040c4d0f80d84c4946032410a00601e250130501c2403611004031204a9090795421141900780391400d002030912820b2201445112002400c80d0f100910074480828000e488854541d2a02c1c1011800c1c40000b0b070502046402420b001d01032079030004100c0d401c807034081c030b0200c0e02c62249260000042815410030882c080c00401c800c2610304554101040003803199851190155440d901a800d079a040e000080c094ac1160000b0b1100300c03c8000c886454020003001c4980341b02e000d0315030401006190300540f0047e001803d20030424200f135a0f00c0e035080310080e00d08002140c9811a0780b41c49004250b4a0001c0545170035030307002494401c1c0c03544000c0003d401440e4040c000c10700078001c0205120030301203001c0d071b04000305103c0505c0e00344602c1a00b250404100b6845e40c141c40301c03c128 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435935116 1250 435933866 435933899
    0x150d0c091706010801060b04030b0103030f030f020c1c02123907060306050316030605060f0a29090d0f080d0f0506090906010b1614060f01031a040c 65
    0x200032004a000a054902075401455034040d030000d048a54144080035082d984035070008641c201c0100820800202d40e400d800c0c0c1182d4141c9812000581c50b00811405070079105a0440c4290001c02c0c1c1e080d1910010640700344656030845601c1241c024030505a0301c0d00e500403404032a400c0c0c03e22288841408260801514103903842d6481c5a2071900d88180050100c01819030711184d200322018025160148941c0020f00002c4000f4040600513503541500c0581902004000d5601d030700200364181c4400c84203540d003400061204c03280320745402080490b0504400300e00801c0301e010000d4140880c502080b114682d4018048240d9400c00c0c2d00d403562016802d101c111107000c4204a442119042449030034005200224089404d0600302c081245142d030180c0301610542004004000040208084524480c840705400c50301680504020b414030302d1b0341581104502540d010410380748c00e242c02d110b050300d105603c1d207038141d000f812110785100401c5400810500c0c43e203a09015202e4000300444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435936366 1250 435935116 435935141
    0x4090c06030903020c041d060109140601050f0706050103081c05040507050d03090e01080a2a03060f020408070909140604031b0606152a111005040b07110f150d 70
    0xf4003d130042e0010608407410100701d00000074801d0044850107c043c84010300603c06502d040c0010301e00c10199815800001c1c101c01e0500000283c0a210301c4503510680e009240c01020402c815039590500300300d207a20003004030320f115950071100c2c104801c6c0ca20031540030341d40120007003802c10700300f20500902c207404078800d030103114505100103240b5055044250282c02401301400403040f2501d4014035040c1d1100041d099031780080140c91420310302c4107020341125046030300032404d1081c503101c0c14000e110740d400c80034403402000c00c007240340ca1168002a03509071280390501d2445101c804000d44448080c0d41c024001030170b4040045c031105503503109a09582c040e140c000f5001d596211488e098810303d644400c007007140200e4183c0c0e0060005d9505107079204d0180c004200e000036564030b281800002c5201403140c20311440c0450114400e5051340c003e8140b01c00b8166980e81c090800800c580b0080408500c18203072081d102c800c40c10401541c98032101c1c1032034680c7c10301c7e0701c86020307801404079005c041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435937616 1250 435936366 435936373
    0x3f040e071704120e010f1209080c12070b010e0118090302010605040617120f0a110c04061d10050913170d020a110a02031c05070b041103060604090c0603090302 70
    0xa0414010000751502942c800d16150b16044071107807014019000e8507070540d060003000310700e90001d560003514110304000034030030004121146180040c0c96010b042104d02c0144903194092000c1e944080c000c0c030145024021240d0180e0742d400201402d04030034010210080548001c140c05084c450b0450b00f6118440d000100700700340c03110041021290198825902c0d1040b40855050005003404211030809007240c0c002d10b001c900f1070305101248100101541008140d54040100c01d005100d80e24110070300920a00120b503a809030703039030040b40c0003480c0e01c0400c0c400d00c0070821152a422964044400c081d1002040e0b41d115a100c030001540c0714015112007100e1060010411040707002044141c0401500580300c40e40d9a50040080c0d2070001890896172088080801580d0000381075004000310420b030510810340c1c0c40d41158203000b11032006041c0d440b148148800c0043d50a0340950b080801d500b20f9400b650b5030700810007680c1d00d2440c05001c004070a0f206001c134074441d0b0011114030b402801103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435938866 1250 435937616 435937637
    0x20c031213050a0f060506010e01080c070f0507171e1005041406070f022401151106090106061116090209030106080f061501141206010e033f040e07 65
    0x2010f00340b03030750f58804035130b80c1c43e0042d807041c1040b4952259982044003840d01c24014a41040040c054100141008080510102c3c010041000320601003004680c040d040d250b4860762594107030b91954000c40c403045140a018034406007150445484c0c0051031514001349494500d20382004000c2002400559102d107a4440100ca210810080a03001340e0f240d5950b06410741411900a040035159225803000a80440c0f042e040054691000ba05564041c183c1c1040c01c0b684000603100160312480301400e030f0062508001c81e280e41035210000b02e900985a042442c2e84011150f03031101c0c4100301501132a11510801e00a28869078080c04030448003400019220780c94668541c40c14408917040c00c6c00b60700140c104501c0400c0742c060480c40341e000b801d0180d2030038400240c01502c1d009a070b01070520603030140000b8905a2080d40340c190704400140507030715482100c41d100c01da0703a11480079407100785118a402214035002c080c00d80500c030040072601802e00f0304160000440445c082c02d503504004c01c80a8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435940116 1250 435938866 435938873
    0x1e0c0803100e010824181203041a07121116260c0a0b06041103070c0b0106020f070317040b0c07030c080102031905090f01050c0406020c04020c031213 66
    0xc50181d41d04262626886141c60080341818038142c200301010b811151484208150014840c4050185516079401c075603900400300c004629551b0114034544214503544100c009a8002140118000c1180000d0140f51104035510504151031110004110741e141c034001d802d00354055518602c02c1c15003103280613205000c50103903102824094500d000c629440c081303640b4202104440d42c0c2440d40c2c00c0e5060015081500382c4460303103500040c0810390311600081c0319503a513a002c0f00c05416803075542da489091001005040342080e0300101c8000c100f00300003040403030000450601122070070300100301032411030303a428035032245031111031101c0c032000e110200b01d114940d0007620011724461f004001103443c40c20034408000255102650907407042007800792403400708480081102c3c18000108494507013601e102d2520029210f081c10365440c02041c8060403042da401401102d9044e4200ca5000c1e400c241004120f01c50200106410b80c01001a90441e841003000c0543c0802417401007010480c642c2c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435941366 1250 435940116 435940133
    0x10030923010e12070f05010b04020412020918060c18040c030902150306130e0307051506100203161419033507120209190303110d1e0c 59
    0x210040440c0c000341124201440911848100103030400080c40f0040040d40319039003511400030003628144841c1e150605001007500041e90400f80607000b1591250703076108034040c0c409090400c910a41e0044041451502800100c013008012074020b4122a04c03a5071383c501940d44001320081070703105038151086540d6074520409448420b203440110b0403201510401a01d942140c01052581c1014070500034541c60700b0804d900c080d441c0c10400200010703000c0b5128075501400500405500c0780d044024102d009021445006180584500502e40600d8006030381301e0140201d51280d4002201482001c00d0310292003c52494007c8282e5030140910440c6080c0480c0094054003c1415030403207210114520205003030340c000320341d0016030500c1d505c5c10001000e080079042c4010000e180e109490060700c560304903902204000c103840510444071001c07014a0035148005e5000ca90407030112501048041008a2403811543d102c1c05200e003070b070b405a440d2420388a03081003005050482c002c001400c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435942616 1250 435941366 435941393
    0xb2113170306211b06040b130302150405010203180d05100c02060a0911010e1309060905010c030e07060c0305040f080c120c0105070314090d1208071706100309 70
    0x1124a00d54902e4103005102242c415128280c02d460a0901e2200d0b50380d901141000c040d4003900030312071410400c500090000c1c06183c120707103982000095040940603580b5a228112442507555000700c0b659404070740d6050103144036460240e0010031403881400d1119541e01e10081004110100c21002612407502c3d00140c8810382c0b030744c6581d4280e45004140c04101142c1d11040c001c1c820b0103034000942c2c2e90b040a511603048039052001c0010955003d40d6100c00d0f08050029402c0108000c260608192001c0e0181c9042035941c0e510300359254400521034000ca205410b8024014a02d0902c0c00e80111101d018030301c000d40801600b804040741d004c103000d060b2002441c89100604801c100c04040207244251090b14070200d9210322a448501c1c2d8005080c1c440e102c0d010304028034243c07a402003000381442503c004c641d114121600900410000b40d00a03804156139589104035540e4036a0309889074401e2454400c440840500060460300e81080640741c115400e2a0200e018221562102404100c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435943866 1250 435942616 435942653
    0x60612050106050301060f0630092d02190504021201080d090303020714030106050a060503100e0c091011010e0606010f0903210908030403050d090b2113 67
    0x100a220400d1000c01d01031500603180860080045d03074a030526070740211516104031401e01c080380307204403414400c1340c10142c0203584814200d840503100b8070480f0300a201d681000c450036060b01c800d0313407280020324030745990403c94a49521343c0f0031403507002c0041000815104800e0181e4915001c0b80d01d0b03d0341c0c00600140d000e00b0503000055410281c2e41030502c40d0f0f2841e4a4100002c5910400200341c2c00a0000308440d0002c0b100d505100398034010070b01414868003c2500403610358000141180c1c07001c000d42c4911440900f0316a1191910001003a0300d40c1602d50001318607050003500306510b003016289402c6000f60800d9520034049040d040d0940710740c19044074954015104200065800000241c00d04a4600d4950009411540c8880c0c5801142c122000152a94241d00303202d82d020f8041c681c080d25160040300d03100c90b541c0c030301301d99030780144540312000804600000445101c0310003a541d2600725802d6040030051180d101c84a0001c00402200c501c10754125414046881604038440d800c15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435945116 1250 435943866 435943889
    0x70e040c140f220326090f010305100f03080705011b0504061d19050406080d3203090309010909020906090127090504050f06040302120a1e0509030f030f070b0a090606 73
    0x2901c924540c040100b48040701d000c540c0801206000f1f5558140011600000f400c3c005055110101c0c4d4200820b5103800203206240c00e03113004001d04c98184003070682284507600070f102d082840854070361100c16064131000440c00512003030241502451a403007071198015091400000c89800040c2c507801c80381645091848454400c0c4180d0925008100141a4660042000030740c0118024140411310050010070982c00f032040406541d2044100c3d4407007a00201c164a13401d217200701c961258444400c0c2d40c0030840548000070490054020307618441070007000305003000c03281d034010746640100c01820801c2c1c1c038070308120740da1000d00d148952010300a08440002c0928103071900f645404140848401c6aa21a408010010340e000a0710700c00110310007031140d107916079000146c0714081c403580140c90700120383d4180d25200354804068090f14100724125011402c0f05016107450748a10881c0380321a0200b0003008011500004c4080c0d0044811040007540c00312a4075100304a4520f40c02001d145003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435946366 1250 435945116 435945143
    0x30a110403060e070603020a090e090c060a0f180e0a0b040f0f020702091510050f0c03030711160803041712030a1d0111160f0506070e040c140f2203 65
    0xd4100705130030151449040031071600a0304030015110b400c170b0f44030b40e10511009000203005902c0030303c50140001400342c0031a4480505600103080356007a1000100054020b0350b889400c25141900003003200c1150110500944840c04920041d0158500c010380040d15903900c0f1915010702e104040d4041003420300142c0721080d0788100216041c000d06a0410100c08044605181e501c0003440404003250b82080e99842c1e0244802c0d117254007034070700c140d07201d0301020041144458200d900740c14800c8402096502414000c60f031601003404c0c500840c6c0c102c4d801480f00744038170b80e140c509210361240813200b2a000c1c0c2c4561a030118a9038001ca80010090b900e80181c042d0510403040c11840466050f030081c0710a115102c110310f00d5002c0d1803800d49465400403003c13018440380f01e2000d01041d4000c0b0941d407a600d844000a07125403140503100f40240d02d05640c05640904c61140e100700c41e440d0b005aa0b150030080c0cbd40954281c1c000ca000c00681002c0140b40ca00d030f401020744401c0040d0b03c02d01c4201c4049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435947616 1250 435946366 435946391
    0xc071103160e150409120503130602030a06030c1d150d050327103c0206060f0f0306010b0705010e03281103031906090c170105040903090b030a11040306 67
    0x4910281d24a008600b4118107000041c1b000c2200c0c0c44101c90f500d00547c4030b80d03034180210380c1188405c0e03014103000d10000074001c000000d0740112059900030b01c12020240d41d01c2c0714050001c045160140465100d00c030105960f6a29408407112090008191007420445511814110340c8894854107002410540464071060464480741041c2412070300c41480300305108001d4840d034411140410241c0d03004030803118003030b0810120078100d142c0b880385164900c1401006540c0305402e6515512807081408605000e02e07003080940300010028014110907440d0001e000144d07041403c0450307265480340020b03681d0b1071040000e08000400340b07000300586075015220907100b03040d0007906402c00001c3c6000a440d4840081105d82011500074041c591400080b0030b08020080d68106154860501c0400c2005541c404500c240b46440050080000d0b682d55007084121910900c0003000308240c54400c10140d030003400a15070220807a20b0206040f140b0b2808410306900070740007291502d944d28040c40c2079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435948866 1250 435947616 435947641
    0x120309040509031303060c1407030c060b310b100c0b061905121510030b01051008040206160b040c09050906010b041202010306030602040603050615030c071103160e 72
    0x40900c5001944c580010249a1091405540405001c26031103040c4c0202c1c2600c44c0c5240f5092084411a03d0b40390606498010805a002c0740c0c00d50306582019074040440c5011301c900c920810084c00c501c00c0100000110603400760b038031403000a02d03030b036900e9445425841c1c60703082e40640b1300641c0d10301c480076003035103441a12294060700d114000c2c1d0103182c5901d42d0708001d214400030303240d08503811140a1103a144041c9480c40441d254000000094213002c0c074405d00041c44020780b8031900d460101a88c80d00e00740300b2805c903500da503031000520b00070115002d41003180007000c00a05005e056480030409450381c03c0c03100c3c02528100c4101c00400c0c41000580000c2c80f03400d8104070041c0c05004d682d4900b01c1101024016400b500708071600e0304400b2021a03003c0d5015800641c1d00032015511a981d0b4007026000f804119809406120fa40c4d0301009460346480032240300700070b102103442c1000c00d01d4132050300c82c98002141076050f121390102d4036040c0702e50312411402020340803038036075582c17900500728441c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435950116 1250 435948866 435948871
    0x31501120e0a1709100810230907110a05030714012a110f0c120a0c060c020a080f0616090308071b0b0c01090b010b0909241203090405 59
    0x22440c007040c4210307240001c128554101d4000c4003080910289038694006882441401580410b1056807500241e81003803203c1c1c89400305a0144c01503c2d9100c812003242e40c0c011102c8a5030400780d002d182c60a00d00186204e412061602d4001c82020303504414518018040d00d05650550001c40c242e003c011034190b0102e41a1258030090045400b0281d002c014a00c54080d80610094001c041c40c202034810b050040c0400e411130229103045076001c1d01d039a11040768080704c034004c04058220403a04c0c000041c1b105a000d520442a5000601c0c0180849004900003406c0307034461003442001079070f040208903105845030580003900d028141192088021400700240400f44488441c0820209254005480c040f58005c5039403d0b4807a6036645012140e4074a411011034000041004105a84158402d00c0f04174030942840600b0790b200c88242040c0e01891101c190701c0701e030290016080d0324500c9120305d480d01c10781542c13565100e54040003820101c000384d600c52060b40302040800c0c040c5003d008141c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435951366 1250 435950116 435950147
    0x1030b10030f05151e070804110307230a060504120f020405090328140906120106081e0126010f1d1002070f0201050a09080303010306020c0609010b03250b031501 71
    0x224000340e41700701c2c1c40c441c9000804440c14411620000f60510003184003180f00410010107031070115858a03551083c1c907a6003400fa50042050500c1100c5600380701a103041603e101d0b40312079007230501c1e01ca840c0c181140007010803290aa81d514800006072a01c0c09054011106a03015688130491010f1028a4500c0c4070100c5c0b014181544810000c0c80d008000303c0c214200071000b05a5442d0040081002031107020755551005048500001e180da611647c80382c0245a20361090282c1c2c80021046103c8020038014010303041146009000782266140d03641301040c00e020f0000c250324026502180482d5107402e07880d20401d4070340003003584640040c442c000703c08209207011810211640c0b10040c42801c0005c000b810b11400040d0000705234010b8020200400d4110112039482d82c4074078002c0080e404c004000b41c401d00c1900081400604107016070000e05002600401071500c6003010038032017812080e01620300513069100890b441136804015480740c4580d0040c0510700c00003400040c50300750110700300c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435952616 1250 435951366 435951391
    0xe01030506010e131d06010f1a09031509151602100504170c030d050a0c080703051b0a051606020912070f0b090103020d0516020c0a060801030b10030f0515 68
    0x5003e0f80e80e039108281c00840509000154001141200400c0c541a0030340d800c480340b107614000942034180d00340748415a6036401c1540308941c48103100d01c101e801240061a8540c1101342900303040091100c6840e070091080c0115a0005040604d500300d08506031a00c44840c1200c02103906030303903010000d0103040000d030b003000c00051400b42c556022104a0307000903c520280020142da81500c1001600d0380100b41100412450400d50240001808051f0031100420395010024105038003a1191710310480c5070122280780c3c910b4840c06000305501c0300766543c0911800b441442a403010314218012414810040143d56201e01020080030300110700300d410f42a440200140300100706a44a070781102d450b4001252504813490050f40a40141042d00212514080030802d07100840300b001c01d01e05c0c0154023030300d601610714024008200ca07240110400304c1c100d034004100041c00c030b45d191503016601c00003031240d8503101d5441c41001c440110741500e00e40d001144034400814040d008a8004201c82c812 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435953866 1250 435952616 435952637
    0x31005010221040b070303110c01051b0301030f0f0309120f260d0e010209220e010203162f070608010609030c03031b020a0b1308030a0503040b0c0c0307030e0103050601 74
    0x414241c0c0703e14040c6895509000ca240402c1500a07080b40001c24a10075015032110051021079008060803503038020103031503040d00e0803903040a14084074141e907081040c1c202d0085207130f02c1304140743c0c102003012010030010220014070005100c800026003446441040321107000d9003401c2c140305d05500c400b034020040c0c080303002040c0d44445048174810075454402203491140428024028090502013940050b000d500002514440345003910010a0b1a00300b000680c20003c6030500300d0004450110f82c810308810100c80b2603000d01d96800d078a00620403015100c44826041d100003021400f00c282d4103070300100303050100c03d030854241c50140c00b841c58403922381d92842e225600d140d140f03840082d017409910982001028907010300c6240858000d4822818165141e0101030154040d04410003002c107410400708032101d000c170407036001c00680e543d4281183c9454541d0f00c0c0b284030107080c0c882c03070342030800c000d6000c03000c03d00c043c000032402603c446142400600c005410342d20020410740c1000b456011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435955116 1250 435953866 435953923
    0x3030b03031207080702011b0906020d09060206010501050c030706060303020307150e0709050411040c02030a090602070f0e06010203120c090f0d0302150702030d090b04060b1507020f150310050102 86
    0x10300640c440310754900641309407510300c07003640140f483c11002002e2140b4500000e01c1160006684002c5400c2613080f14041d400300d800848240c019400703101d005030000001003100d9803040c2c020300340c40b030741620680e4034003c01d9550b03071800c9800640c0110056080070902c01e040c0880302d41c1c0030f10401280c0a041c00b240300c04200080d11441c2e5405400002e81d030311000300d000d014144070104c1065002420800075004c0c20341c3c020b0741e03036044200c8260004503007000c0450344500c0842c4900c2141c002d0304981c4c94442c1080b07084a0400401001d443c1103120601c062602414202c903114000c04034000c540c1d90310501c050074808d0040204240d03d001d14404134403180000d03400030b0703000541c15210190354100c0d200c0b07050481c02c5205c0d000e0301040440c01c006140090041c0000f01074022841480e0411050361850300340140708500e0041e14555510500c01c2c94058203021007212a0503000410340d02c000d5954411201e01d90f00306a03081c0c809015007000c01e00182d6010440b00000e20b50311640300300d029a591a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435956366 1250 435955116 435955147
    0xb10080a0201030c110d0207030b0a06050609040209030a0f0f0203060109060608041202160e090d0c0c0608060a0e0118140c04030f11030105010312020607050909010b180604090903030b0303 83
    0xb810142c0d18502803101521032010103190281000543e03101c002d00901c003d50310700c8070f40000c0d00d0b03111813500460502e081501c038020032504098411800c2c040c000c0204402500b00200340c039014011416658000f5074051800c000861050081035829203490041c10302c0c000c4160054502c091a164003440980d40290f40e403580254010010111414800412030411400c40f064455521010382c0224031030f01c0c40584c03c0d21502c0810100d81e42031006483c203e8003c52001070203007520451000601007140706800855100720007514200c0c0307c035982c1108400401c405d030f2014030010b80e880100d145445442c02108201d131505500d29071542400d40728400d80748254031004255031400d10304082040b20522240704107180050007004550b83d030781448101d04189a00000041c0505030000b15211300403c150354003003e0181c5440c91f036a0810101e54459030101108400c03a016401c0c488905036901030040025160b0010045042c480b6441e014054892425a80f8825001809103d0b4180f1401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435957616 1250 435956366 435956383
    0x501030206121305030c0d110706140c15010303030207051902060f0a03060519150804050d031a0307080c0a140f27040b012610111b0a0b1008 62
    0x414446030b458803a41c188001807444004024418000440d810a0000001c60038000c1c0700907603161000c0310344820b6017158503010f09003c2e280c00704441c04a03101c000740f0004060010b0121581c00c803181c00c50246541180ba01d026401200002d4000031014104241842040b41503a40d000d0035002d0381c07003c1c0d40010540d001710361096400903808140c0891561107078001c040102005020022560128400e111180c2c0842c000c08034500c0300c8081e400e220307a12a403255441603811002a18070b001c06101c0440160861503000d030b840000082c0e001d002c80ea0244a208000c12032140108062400c15003031100011061784082c05441c9504000b02c000e49a84100e0724072440104e9071003422605036841d1048e484401d03504a0707485000769007000200500504101d040c3d43e480280d03418000358540403007100310b141c2c85480100d5009001410003a004c2a000350384541c030b45603070356810301410f01142d00740c0c00e4202c0c140e25840d0b485000c2107001e011504242507001592021a0600c090802040c0343d680d0300c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435958866 1250 435957616 435957637
    0x109060e09070318080f03060405010b040b0306190305030c0d030606090807030204050402030a0c030b0a0518100b1c03030b040506030c0108011a0f0d0203060f0915010c14010e030309100501030206 86
    0x40750010024121500c041d40d481c2d50780302040e40c6d2249882109200d484d00211600c0e030250f07287ca0000b084602e052800d88085801d070b04816031540da1040c0612480600400401c40c0403100b10a000c03001036400d00180034140e4540e0003c20107450107450003401d94030241d02040620118000c1805185004100c41c4280d84e01a030f000302c4c95403036500c00300303140a1041351f0140c00e00d501c0c0b800110400c022018524010300c1240e2003400036442e95000b94900c2e62103403d00c2c0c80c0f250f00c41481d405240400350809000301400510f25229050603905612800c031110900700c1c0003d554008194052404e4419181c00000c154024007407400e4240010b4030352001802400c0d2030b02c0c082900190441051004c49240d0200311a80c2ea40340c1d10340c4d4402d14080e40095600030b126442824018115083c01c00c035607031081c12007012080c90f110f003c0005403010403815609541c0f0b9161034404100021090240b00804809040259031701d00d00048040d040c181210b0005140b1800c4c40d00400150b50791806954038400c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435960116 1250 435958866 435958871
    0x908100207080904020301060903210503041101030f020d06080f030304050d050310080109151d0d0f03020c1606110f0309010807030209100f0306081c0c1511090109060e090703 77
    0x1041c01d00b003189010700c651940d4007500020000c5103485d480f0941400322885615107000140c2042444d0b040d000550300484001802440002d010541441e0140807101043c14005483c0308450181008d0f60300061010395074944a035010000b50700c0800c01101c6482c3c60b640958203500701a03581c11f44520070580b020081150200100c3d252101400d03c88000b405114002c000d00c14451808002c440940d40a80319428606529428685000740c2c5620b4031031581c2028010440036040d0680b10910010040800c05a080c03145206012003000303100800803c07006c200c2c0321680351803001401c44040e140035000c41e030000b000781150703e103002050355441c6009007040480da981311f54084000b402107202180d801138a00c400002c071207403c107841c002e010140c0d03541841031030380ba98041584c81c9440c20b148421100c142466454041c8074078041c06d0010b1040302c100c460480c0001d00002540c0b00d00a540c41d540800044005456810122450003842a814100507810300c0900003441140018400018583c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435961366 1250 435960116 435960127
    0x91208060111100f050f15010f03060b041d090d0e011b060c0e10020714040f020708040f2102010f0f0302190207030c0b2b06031401020d0501050109081002 68
    0x2070207284181074042d074800841d88100642c01040014200c82d9115140551512000c107506006902d102485524100603129030070b200d080044030b5600d4119408030406598810100783c81510030002c0008101503103c000d9103140040d170201a6580c0a0854841c41c0d00021035035103100c1e0840912803030320401f402c00780002c0d071078604c21031480c03122504010105d42c6054000d00c80c01c1d4100341c400c40f00b644252081c1003242c03c444004c0c4c1e513541940c060501001e01c03824081000745000d401c10b80950022000143c10405a0382d148e030400c0c6c01a402c0002d444c01800814040d691589510b42028503030554006030042d0300d07400181030280e05d030b180f202c104208030140302c25580c0203404a4280105240448000a66010f4001d49400721030000304c40d502012580010381e22220307400d85076159000e840108100c2e40c08940d20b2580b000803051520000e0701c0345000008a2200b440508010000308000342c1d40b15421440c050459405030800c2d810303c80041c20a005000d000105007481403950107006075180b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435962616 1250 435961366 435961369
    0x603032102040911030703050f09120306130c050309011512030e030c03030d09021807092d0e060906100e0609060d06080a0213110a0f111203010f060309120806 70
    0x2842560070011909013483c07611006020301400a5104030b42070350b020403940e11550b10350300c0009010755101000b80c2c05804000c2800324400000c40d00701200030644805203a0501d040700c10b56181014800104a0200801100700d00a008852650341c91408014146080010307602210b50503c2018040003000c0b4491042510108080e290142c401021240ca403103142d030140014016003070041b40242211250100a641d4500055005040940f100c01007030f4182903000299040e4441c1e42c20702c41d60780380b400c11803405108801700040d01c00021201210b181c41707030a2003180b01d00a000c40d4025401414078100d059401510340c4048241151942c1d52141000005121070064100d110300e441d01c1c0020004104200041d05ca400510903100340c000c683d13181080c03404945100b40b100c0704086003004100b0f0387e40d10a0090050598007410071161207103c01c020306181403480303413500c0d40c00c560000050020050700140701000308018a01886041c074190354001d46024258040300c01d0210000215895 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435963866 1250 435962616 435962621
    0x1031a0403021f1d0606031b061903050123010e0f040f0e0703061514130915060302030f010b0a090228030c120b0f010f120c090e0a06030321 62
    0x6041903400e0fa41c103a2070303025070088010490840004c0881e58081100180a600494410b1103580014041c00c520011150040d062580300b064480d8000410455880640c1d05500f0b8821086442d540004103507050509043d0b81c80300809600d40a00040c40203101313541e1303000f038a0074900c440a846d484000c0b045480400c018184641440b0342036402d1100703400342030320001110001c40340580000d00c112642c04a80d0014a40c560144408526140c640c52020f8140325a03c070440740c520200c0082e5040310b0303032900e00340c00351070709001c19100792a28410004c1d0314042209802c0165000b0003080b40b1400500014040301c5c0e1407154100b60303074001c070b05091034403001d0307034842c0e0303e81d451100000840d480d442c0001c00408604108401040c0c0c50215401d82d5941c5d03229010b84803d024200c08a1103005d1f0005503003054141800ca01005203000040d9440b291901482c80000e5994445646040c2840540c0c4030740000100940c00c020f00e03000042011960002d800b8450703403402d6011500380c2c0014147d6501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435965116 1250 435963866 435963883
    0x108370612050610061115061c031805060a0906080603150708011a040303080403110a0c0b090a290a1202030f060f040509030307032310030b07050301031a040302 71
    0x1546440301c041d1818080e000c103403244102e000f440108901603c860b42642c05180c07207000981c041e0300138808007448082104125400410040025000b49030300c5420144505222604800240340740803201102e15034070461202078001113407210b04005101400030000022407099200b04171b403001c0441d211340c500b400310f200c14161399142c091461800d02c0740030380125002c1c8500c8801c1e81c018520301a0f942d40f81c3e42603406581d4103950b0b180d600c2c0c07142c0e242121550349556400c3c001d8088c1440c0e030b60001701104c3c05100107184c9120215110304441d020410045040d50169901d031206031100a0100100c110f2020503400035400701c2d88a921010040303c075440e550781d410440c01d1000003880031100c00461940d00c582c5017100c50791004110f1100b40300980f130303050b02c5007942c5620a0012503d9140680c0088841110750b0600c4c1d030b40100a090f0800444106460b40d031160a0908024001e012000f4502a4000f6050402c1c03480c652543e6680aa030000c1e4050740c04030030100e803020a0030148240b05590 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435966366 1250 435965116 435965129
    0x507120b060732030906160809130b0111071223060c030114040b010c0303050a0216060219080405150c04080a05010b01030e070f140414040b040201083706 68
    0x3003241199803441441541c0000c50301050410f030448841d142e180001c101c490052010b007159041403031506d00520003030001001225824410f006c0004152200704103c0c00d03920003144003085201d800342c00585078070383c00c50030080b003500301c91018400d00ca18481e0081c01c050f80f06050400301d0129408440c520f0160009200c00c5021307103401d001030250440b01a5050b030f081074030101c4160202004000854078021041404120b081d20300b80c010a000b58800d95102c4800c15025250418000070381000b1210080204c0342180e02041d1071504a0390100000800203144c10900755078100b9407105651118420100005195080c0014050705508400d0b80d00505443e400c03581011000e00e4031038060102400542e000038a02500c103c40400009030881c04c990904000851071402c05100b581c13001006e80315141c010380c4a404201004034101d1050380b01c0c0e805a810b80880c1e0500d413000500f000c60141104501050400316901014000841c2401c001310814148100700d00130a040c1010740500d0f030011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435967616 1250 435966366 435966383
    0x30206092b050708060f01080d030c030f0e0318030f030714150115031109010903110406050907090801060902031b09150301081501080d02031c020f04030c05010807030507120b0607 79
    0x2000c0010016100d42039039042d01c145e0320a9aa4901d01601d04c01c0c09110315112544061305080d1200c1c0240d0040c08407c045240c041103140742d506101c0196055070b031820041c2d5000080f441001c10070303603c1d0158048800c9014000c800d00b400c54070350341c030b0080035805841601c0301750f50107442c0781c001c1110218518085d840c56110750ba40350800c1c1980b0850440420110b801c00d104c020101c0e8201084442c0d440c0141c44800321242940c94850520411294068206a46030320104a56607540595031054503a60f0b80c8034155400c241a01d0309440150b40701d501000c4c0140140403040c48900342c009244050724640a03201e030110b000094104a1344140701c01c1a00c1e0000c0080f07500744020407a500300b07040c000240621640d031800c0301581c0d0a2100d0000c0011303081031180c403800c2c03030b5200f08a540d80400000054105410b4484092a6501642c411100c510003208100b0071960020b6400d544803030303141010000c620785100d0140c4082c05030134440544540d28484180c040c1e55441c1505c4200f90800041c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435968866 1250 435967616 435967699
    0x50310050a140f010c050618100f24080a140c0d060509071a0307082503020910020a0321061a030906010807030c030809060c030d200403020609 63
    0x225a502188114043c105090b0400403d5016004860380306601c0001070581d070781c401a0603040382000076804e01440c0105442e412040c1100d02451040c2804200d0008865600142d0f00c201507500780440c1c071040b414030310b08120b038101c04901c021119800000840c1c01410450f9074609082180b40015804224504084d05010b91a407082c0d105090240841e10055201e280ca00c625a001c0c0c5100403000200304002140076200d041e0094000301b9903203800500780300160700d0300307402c2c141700f48400c00180d130110700d06815203007101d0b6400c003028450018049200050314020801d19074072030b550510425114044901080740d5216100404940007002c103400c00b001101000d0354002e07507030100303280704400001c5610030002c602c0a00b201d0703000c0c01850301c0714030319980c041c195006a1102c542c0107078203112007400e2010910082408100000300001c1203110b0711202a20840d2010201e00d1502e02404140010707100e00d41250000e9104545d403120026010700384c03044261944000382c40c001c124145 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435970116 1250 435968866 435968879
    0x30405010f290d05030909010b0a0314070c020d110607151a03060403030e010b0909010e10020f1b010b04061e05100f0309030e03010e07140402070f03050310050a 71
    0x940340305441c00410b01c03840c268408030300500314002c200000c40d18445000d0000b203103031450030706014500c180d06407410704800d640000c104003000d90000c189120300241d65800c09500d8400c2c1d03401078001c070088544c1d9080c0904020005184c09000a004490504400c02845120154890070080040c00169903480d603241141c0c0403001d00e0412800c0034184020501030b0300601d010085d9040000e0003d0031595115202200a070040d140d001c40d0319580d902070710702e032611102509071180183c84004070303100b00b417410000c0c90901004001c0c01d41c00d06c1840120071101d00c80d01241c605a40d000da0541c1c0c01f8030b420345100d0050624040990b4018a0b088000030184a9888840d00c00703c0e5940c00700300413960740d0301408143c9011090420002d80e103246140d0049000382d006000081c040d280c411040103509004c41d0071148441ca00385459800100d0400c9001410f05442040c2c000a5400b0760510390345036641403602c0f514400040c148a00800042e1050991645000040200800c440440b07541d815 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435971223 1107 435970116 435970121
    0x307051008311a01050306130c08030711091612090f06111b0c030601030b09030d0c0f09120b0411010c0503030a060501080105010f1710080303040501 66
    0x24840c85441c10403000710a0036000d8505502c0d0510524141000711032181400c1e01c8000c3c2018006000580340071444d907410910003d0162800c4016280003039825465030802442c900c00425120306000889081c016442800d44104010b80c88421012070110514624100856942140e00c000b21400b2382c0600e402074051030383c085070582e55569210681e01e94594a00050401241c01401c02d00043d450030351421603100100190009540400c0d1200414032014001e01c142d01e0000740d04002c03d0007110031646c420b620070440d040780c280001d82045843c000c0403002a48051010980d0b59a200001620a42021103980c0300c6da22503550100780300c03c10f2441810041e0f0b9819010001d4010005036010f011303c2e502c04199642403000050282d02c0581c802410800d100e1400110f0700c0e0846440700c8000080000115283d03200c20400300959155030103259a4400041040140001075 = true := by decide +kernel

theorem cover : BRFrame.Cov 435791366 435971223 := by
  have h0 := BRFrame.cov_init 435791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435791366 ≤ n) (h2 : n < 435971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
