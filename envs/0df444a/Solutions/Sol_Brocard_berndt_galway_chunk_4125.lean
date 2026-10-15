-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4125
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:38:33.925411+00:00
-- url     : https://prove2.me/submissions/51f27b36-8761-4f72-a1a4-6e793a9bd6c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741726618 ≤ n < 741906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741727868 1250 741726618 741726637
    0x3080912041719020a0308220f03050c03160506030408040503030a2a050c100c0204050103080405100f0f0e040207021503090c0402190e0a0e09070e060904050a08 71
    0x6006030205000515401440500900d2010314101c62035140d4040c0381140ca1900b507183d044402e1140801a52400c03040c2003100c0d0031002c1d468403010580102d0f040100102c002c4400f021107017000040f030352a02d05420007120f008205441c1820061014941c030355581030345490a600020005108a19120b00603540040c00303058040d040c5500c0c0d80210f46164007000032200420614444801c0f000c0f550100e641d8041c042c0302821740e9039201aa500d0f942d03101501c003050311819015030f030070078054802c040140d00c251f0020424801ca595a0524185a40c070501030702d4006c80ca07009110f0300444c0a4403444002c40c613955240c042c984034103201140e0717001461000d560302980030449400507986514002c5040c9062003855540c0e03080c650843c03880e02d8105010140200d00610001c12030780c800404003082554141803806032203210500040c42c05145401070b03074650740c22070300b40008950001542000d440e0900c0c500fa10588800c010001c03d02c10440c0c0050255000071400c500080c600710150a0303001c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741729118 1250 741727868 741727873
    0x80c280221072a06121811090606070f0605041406090d0e04140711070f051e040603080f0322080712120603030e09060105070c0e0709050409120327030809 68
    0x343d6103004140403216503031006000405c0c2842403218080a845000c070198466807003503004d0355040d075600c583c4011140119108441d0b01000035402d80ba01011600070030741c0002e01340e44056041c5481001000c0c203680c01d4035032202010104288900000b4014001c4642c01c0c01040c1840c51840100c0b401c03d0900c0c440350308582c559507252900c00e0b012084c0c0c0c0c02002d03542c031100380d408000d208841c030701006030f0320030380200c81c0ca0b0000b008a61910030604c2500b2201c0301d050311b440000755001ca030240c41e1640c402031020200040d054404900303440038600505c030500300384003810100103c5000000c100da030054462030300bc0080400090203010444080901d906001c103d031480c40160004460303007580298080740307100700c080b9003514040d414a41d11000908110b07041c0603190b280d24208041074000e0301d000d1444c04020410711802900b1260081030024814007403001d551412051200c40c010014001c40d04110007051411000b1038807010181c0f07020300103514100c00c0e4800b2a00142c015103009140e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741730368 1250 741729118 741729173
    0x40204090807060b1014040b1305060f0a0e090606031501090509100e0f0c1b0c06040b04051207060e06130b03010e1b0901090303080c28022107 63
    0x750084014100441c06003400203800d600c0002884440f8003042003000410000c1900b00c00a01c0d60748090b00c2c1031b55940b1451944809a4038200300380050309401c40c60740511301182080c0d000004900403c1b42d0344a541d2400c4454030b2410500070740c400d040c2d07030b15584407100b0310000e0900e510906035011210b505142c5071280c207a0f58008211480d078284c3da010b00c054043c1c08103101041c01030f0784240d00846241e01003501c038501034510104a00488a941581140e1242849000744082000b82010741c40145003a03074607980d6880b4100c0c298440d1040c1802401e080200b8030b0000700c0030541e04c08840050726030100d003482840c20801654007c000002c030702c0074111004503400c0c8004c001703103000c0e1016898845213814540d80351100004d4000d15a2021a01000303100e40c80c1c0d910080e071004582d4181800c601986031004089541d009500d0b0210520a000786000c000036241e0803020315a83c1c0716000c0c1c23030a040340903500c40100340c01c01000104040d03080002c030000034100041d1680b041d08010344c00d580d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741731618 1250 741730368 741730373
    0x5030c090613090c0f050903060708130614040303110a08010902090d0b0a02091f1202070c0905130620251e020f0109081b03340e01180504020409 64
    0x7060425000710914907504d070041d0000319041030018801d01198240103081106c1600040d076200d0380184000704200035040815a40d200792201e000b0038690000c0180226000343c0700040f00c0c48800c0700c041c0c001a003006900f03880c0d20040da0072a09015126501d01500d40c0c249185880039500803102150003807000354500380410509203859004400118000d03070307105081c10401508605052005c4103c0400104c5140d8464001451021102d8203440150704e5135810708100000f0056a0300c01407585041008100c05108056440c8461a01c00c034401c002c619050b83c620b41131503410000c00303549240204202000c07008401c001080720701e402d00840007000242e541d440304140d0102c40001401541203112000c600d030050841c0f5a07000d00b0301c0e01401d4280750800042c0d03203c02d1000c90300421800d641403807100361000c1c400300c20078805d0081c4004d041440c2100000e10380451b00141141c0360450b200c049110103101425034106e9201d0880b0100a2011b0000c01d0010200600201d0b80141c0c0d0341d840000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741732868 1250 741731618 741731647
    0x6010e0a0303051b0303060d120318080a12020c07170f150118140c0c0a021002071403030918070921031706060316090803070503042405030c0906 64
    0x70318407a07501c0b603071544074001044001c0304d16401406a90b410a00400010b6124180001c604603085190203800c0e1091030800d50051200c3c031000416002d0440c0960140403010001302009807440e0351302111664400d10841c100d00410072551000e0304009410840300700c2c1441e803120a85060b070305580c900003c205405142140680c0d08070880e040c0312004024441d0280794218041155420503c8007040040c0280c0d01600010603040e01100c0100d2101c403150020400500c034141c1c090300d1901c4101454070003a5440207584620f00780c8042c42c1c1980c508604011040d10700d51400070740391400342d2030001d81e0302c6130380000209100204503941c0000207544c13080301e040c82c1600d10b2004c0c0d0050122201e09000b4204c01440b090720359480024400e200c2207490300c8088130345c0000480303010034411030303101800c49004c10203503c0503c2c2440080b5410051042c084020b02c21a41022027a08261220305102c100d2151144801008680144001044200c82d00024030568000501162401125440703446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741734118 1250 741732868 741732889
    0xf03020408030c06090d080405060f13170c0706020f1c0212030a1b0329030102040803120603010537020c0a030f031505060702040b01020115061106012c06010e 70
    0xf1040d80444d041c41460304041c000c1c0c00c2c1c000c1c854030342401070703140585030655074010240c4150501400b04d03000400c24042c0d08081440d179907000140c0c0c40502d040340e1051240d41c02501e100c0c81540111107000903003d0002440519805404026001001300343d40b1441900148428810550091003034409500b991b0000440c440c0d200750a0010f000c5410081c20003003205808450b40c241807800c0080c4810301540c1070004860024000300115140042c40800d019004551000030740d4803000c250b03a188061100c041034884d10381500204075941e1040c140903000d0f105c5040720003210580318041c0100d2998a0329141200c1c114804c003501c0c116001c03800c946002c1070700e1002d40002e8406290038034200d9142c090100f0351080ea1001c50328880c10000051035510450310020322070369984610703003250390017900f14254083c509100c5c44005596500064660300041c02441c0c21400f5803000440d100c2d0300e003050070111740c071149040003030b1074542f4030122000200940f010b41401302e905e402503040c0d42c420b82d052 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741735368 1250 741734118 741734137
    0x9090c0c0b010305060f0c0309250504060e010503060c041d0601090e090a0b0604050705040915030206040305303108030a02010e01020c03070f0602090a031a0703050103050d0f0302040803 82
    0x6010619201b401800b0b40ca40c064000e145215080041c8901c965000514091926109840100c10322030881844c4007480251301554219040070350004c0c4011181344003c1c101c42003981a6072842d030711401e0282c06031040e4003882c001c001c1c07001c581000900a400c03441b5884101070608400366526502416961102115081070980c844642c08082100d00c560194100b101660240120300700084003610a01070780c010300d44c04a66a4501481441d94803141c0741c011740d00a40070683d20764036410f01d540c4404000c0c0c10b402007a2440707121103482c00e010810400301080c800d035409091600d0515072100c110258010b41c01c2500da030712080ca549002c0428180d00a01582c0001c545d240300c001c40203401d4516148103807074964410300c510070100c45e003c4210b800c007030f51040100d03564081c00c0c074019000307000e0100b045800218680d80481045800109106910601020443c45546080c2d046066070400d0000a19503040b00301080d444900840d0300140c180001d003000b40c1043e4840000a02d16040030b00c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741736618 1250 741735368 741735373
    0x1002031b1f050a0c080603061305160308040e010b0306060417100c02060105120304080d05030601110a060902040f05040c0911160c0509060612060f0406080a03080f0a0c09090c0c0b010305 82
    0xb031003002c464620503050300080342c4c1445e003c035291000c006916500300900f10304100e08800c8200c0100f0000380154070039505119580e00c2c41ca901da080c000d80d00e81050180071003801c0c41c10f0022800928120984c1d2150500402030362409003869130011242c1c1c41c3c000c0754043c2c0d119031500000200c0160003242080c00995006154562400b0200410f080b1b1561400403641c1042005003c01a004500d21102d00d105050980d940e845280c012107000030300c1000700043c2c0c05a00200020000e1302d40128503d40e008440500541e100b01c06540c1c1120302c20b0300c0040101c6841d80c802c0001c025250400200846111002c0c1c4c113280c0a001c0804080c41080c1003102c0c016403005080c0500e00c1d200116030307004581a1240b1f0300301501d595440804c620041c04070f41c03003076089440340d0711f85540d00d8004c00040d010703200c10707904003694a1a028000b00001d40341381182c00001030010301c09144078401c405180c5095951410b120340341c1031451000346140c42555081101c1803014a0209a0035038000e4020351042c0300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741737868 1250 741736618 741736621
    0x9080f0a1205071527030804080a14030112030f030204080d0c052505030105070c02030a060b03100228030b0d0b0606040b040323031e03130b0a0e0c1002031b1f05 71
    0x149a10700c4004081550140019001e0017011030342c8081504d9000394026400d995172000c42c0c1c81a03401a640c0c58044d01803400000001ca80a07611450250303120b8840d48440100d001c0240d400d4099010b0340c040c2044540c4880200300541e07214811006640e4000e40584202550320003049000018980010b5030300a0411410015800e003480b456510281e50311300154400401d5001030b8888030762240141805d0b842e076a400840e6503050201002e0400403000855950000d540c01c2d603060b07990b4581d0098007000040740850392502900407000004001041000440025a1064075000c005030015400403024000030509240150080010f180541000704500b402c10940f0640420841041032040c2c00500c1455140c600c11009841080c0100450b0b944a81d249100420003d10350342d00500740592500501ca8040496400316000c81c03011015680280c02c90010b000d50303220315811100c01030380101b1498403c801055109800c2031a82c6042d55080500940398002d11080320300070b190420703600e50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741739118 1250 741737868 741737891
    0x50a0207030e030a020f0603040606090f140f060105031602010f0e0105090d180e180607270b0904050c0c0f010606030e0c01080606160c0b090109080f0a12050715 71
    0x18030090010307004800901c130b0f985084d80802c070591003e02103e402503101201180421070342d41c0040001d00303a50343e8200454480400c01070054404074110049070758041e004600c0505040c1042d030300c1040181c445c1c42c65074440303025800c800c54048090b0f408555849080342034650060060810003004000089800d0414042042c20000301203603000c2400109000001504c11044c44001201c10103400207040380d0b50695110341a608644040686014000801c18181d40010160411510219501c10210010035040122018901500d0710f144002d00c0418210324040e00b14079400501e078421182010510042c01e80303003000700b05605043d139441d43c07414000281e2501c0703845a240c80207801031000c82030480004c2c01003840a0061801044000307200e00c10794101c0504003200580c004910718407640e5a1004403660f400507104140094007e110004030303134100040c800e172202100000381c0303c154455a50181161010a5440c00f4400140100b402081601107040c0060380640f40c00b00e040401c09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741740368 1250 741739118 741739127
    0x72a03020d210903050d020705070e060d020108151801060e03010506270c09061b0124060e0a09060e04111c020112020d1125020f06030712050a020703 66
    0x703800c1c050811410224106000034414920314000c085100000b40004990504a9a0b03108030a203844685000045420030000e0010312442101c940310303110b00142e20707070740c081040c0007840700e50207030015980d40c02140001800c010b800d0f0714284014030082d0704480c001169450300000740e10140103c0d0410b41e0600b0107007400c3c042e1640c03100d01101e800100e144800307055106032140e00070245400e580613001030480b41c000e00880b0004400100300795101e4a60000308e0780c01c0c0140c6170381c0d6a0380d5400c3c0618a22124a4000110b00c0f9078080011011114200b040458100408005099100c1107104000070030301d0480c89000060a098440d041c1130385018203200ca017407041a140c141c0a481742c0362001c0c101d0000340c5007410304a0b50901c0c0548030382410408034406401100c1ca0032000c030f4680800e51200c03442060080050498a1501d881c059901c8a100b003021114524043e40000d2070745a85401807902c0740c0155404001130900300107a8881e040814200d60013140c10820300d5900080000c10305800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741741618 1250 741740368 741740383
    0x4090c050307050304080a0306050301020d0204140411040303050a02010f1401080c03070321020a02061218030c0303130219030c0812031009090515040b16030903020c09072a0302 78
    0x460030a6031460501000092442c400108058201c01c004944020018401d421081c001c080c010000d540b43e807c040d45040003076005200b04482d40486068843c400d040a01554844070301240040e0706081c038545065655920407509501195620600150480450302c950041106015002241c6605141c082d91803c3c113420901c0d413207640f064004100103200c071030f0140301c20fa54099603801d44d0060707040c059142070007820300258000004a05a0382614090004074410002e05489032800051100501d49038880c3d8403882105030401c10004901000510040758010310241034011f1903101070344031500b0103100d500f0481d4100d03282c68003042031a804022a50541d000c0030b01813032441c101540303280882c907124800c6210a54540f0107170f5007480f5041c0300700c040c803041d410124207603882c113841e12900d070510894240d2044203010420404440c0310344666400e651703058000300300c5044140200300d030100008100800700284030740061540c030f60710b007440b042e401d80111140c0d94a501c21f240117410400e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741742868 1250 741741618 741741641
    0x111041703040f120b07032a090807080f0c0111070918050318040c18140d05060f010510050408030931020904050f09070306020706020f030705090102010b0f2407020d05030409 77
    0x4100c10b0f5111204051250a812023034a060700348030211260003940d135480103510010190044101c0010120030208000c903840e00c0c0e24081c0c03110841102d00540d03000035490b038810043d034481c450034856880164851901c40380042e21b04000100326648040c40d40e4041c411402e014140d040444070241002d0050004508603400d045e0345d40c40540b0f03040d602d003074414800d100d60040701d001c00054a440320781105102c0c0d9040130588071980b90810558100d0b01702031041e0390064a081030b00e244070902c91010b550964074150040c602c0c02c41101c0070022040b10b140009c100e081c0c025400c002c07815600b03009400304144018000750315031a50804000c108da40080000e001c4001c0d0004010808002082c0f40c400e032584040c005840b18020b04000000340200075502018850000901c850a5004000b506900500f68000e0202c680094240f051a000c121201034012240b20b0134500e02da48000a50380c065059003101fa0308040c1e06800052130340286090a5807036400001d424407100c441c60103007100e20350 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741744118 1250 741742868 741742871
    0x3010603121e11150a0e010204120506010608240109080303072c010e010507110a0605120a110d1116141c0e10110715030b030111041703040f120b0703 66
    0x2e010360aa40d445881d1413550392001c0c95420300117a240349603540310502d801942002107486549554040c1c4041004010582d8144032b1032000040309441202028885e08040d40301880002d0f0703044801c0001d001c1c0001d01c2d0706100841c04042024102000614460b0802d5681c0c40406408411006d043c0c012440e44903c0b000d440700000c1485982246048034115421302e09160385802c1c1d4101880030104084440342e015421200018125600030b014025141030000200a40d03181c003000d030301c101d88003043c5103040081d0078854058900850b6005d00000c1c4100741c002171401000c0710101668481c1080121580c911130094003202903002c102210340f9010b070f245000c500b4403202d01e000d072902d0106504c0f03511034400c000110006900c603c001908812085c41100c076829103842060f6400c1181e44607100009240041460f154030b4140a488041100d20300520728050401c1d501e58002855000d4150750781c8410480014207c01e224480c0000349140c0781c111100201c940f40058a070704001e0710217000c15 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741745368 1250 741744118 741744137
    0xa0f14060a061e0506040e0c04090507020c1206061e1302030c04030615031707020f060307020f010e010c0e04091a10050a09050c0d05040201030f180507050913080903010603121e 78
    0x107171211030450341034407030407034603440c0c90346c1c40716213046852046410511440707003030800b807110301600050f0b00d4075003074021140e150700c100814201d80e90b155801c0300c0c82544a014504819078418040c8218644000050610406100e40c584120140d074003d5904a40c460f10020f003c10034001c441c45110580c1100301c4600031001c1c81c688803102c0d51021050001761070b0703034000f039901c0465840340c0030744000800207000b094591801c0c41e80a9160002282018020750810b01d8a5100c084103110f00d03d000d000940710701c3c4610514000313000040840c032904440c0d0b03820300701d840c0d0001600410070902c242d44070f901c0d28156904003000e005402c0042d13404100701d507040c00140000b000b04502520300f042c0e0716240004550b03580d0300048016162103da0290681e251402402c8a02180d84028448501903001ca8004560b00c00a102c5a880d04aa811501c000d0b00d26905000949501c01040903000c004d00106800b9203c0d182c502c803000c44484500e02040e80c00b940d40c0210101001002d190603014100310704c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741746618 1250 741745368 741745379
    0x270204080d0305100e040f020406090b31060f17010b061b0a02190509010f1401050703020f070605040915031205131701050402030709020703020a0f14060a061e 70
    0x1079000600e1040207150300e46000403001e49940c0d5040004142c01101e00d00c0318200f6040c490301d50031043c030041c0d00943c02c0260206501900740110b4190300000703002140c13624001800310b100c01c8085081c0140104800f034516034036030085c0c09054050708415150030003481c40d108440502c1c00240d2803000a17a4102611a00300380c0e12001aa200d901801e01c00e510b8441d102c00d2807605003807a1810080d0701801c0f840b441761449000600c80d00940e03009644540c0141d8a80b442d03c8101c1364644078100c0040f940342a000020b51040f0b010708007241c840e00403034804200d403410141c184400c0350800b000066021908018144850081d070546c020006940b80e541d80c21520b504041ca0b0742070017940c00340400080c540c1214207100410b2001440c803120040001d01106460343e0290405903001c0c1e1007840b4180c0041000a194803c84014a40c0741d001003400c0d000c11365030300c61081790001c0243c6200d030080c00a00480c000611a0501c1038440280c0024000d05040c1e105500201d00b00c40c2c650018407a0106100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741747868 1250 741746618 741746623
    0xa0507021203132a120f0204110c0d440709090f0b0a06170a05070309020607050c01030e03040620030403020307060e150720060d0627020408 62
    0xc400c2503003040d040d036940c1ca0990b01160107428100013490a00340000c4000742c1c040d0000c500f0040401c040341c2c0d400044d6600c0aa07403070720b8007641010705041e984150040051525900003a402c2417040c04043c1070003030846089042c405451642000305520710801301c03426204d102000400c000c42c001601500703801c0092400301c00d046d018011440201000803401013802281c1800080122300400d03c06031611424500c00342c80c03801d00040c0034401044003c2065402440941400c0d042686d00c2c230419030300c014903071018001c0504400705255aa00c0400050b8550710028084039001d0f1000304038900d510000141255400503d10249400900c02030010550200025402480c007084024206a0340e065290440c03183c1c2d88001d47c148500000051080d070070110a0710a107a0490764031603c01e03100c80c080307050b074401c2c030743c000304007200c000303508040a10405014451003030094000ca0404112300101d074100d956a400405605103000440d0501c4a200b849407060790810700801d50a061070f00e09840e9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741749118 1250 741747868 741747883
    0xc030b1c020d02120f030d0e2e09020a0b07120806030c0108271005060d0c12231509030f0306101407030801080d111c0903080d02120a050702 62
    0x2441a0350160110080d5070344c00a400d06559054001e40d1545c202d07032840e5582c0c070790045204e00c0050741842d121110a000202d45090b12585010031a00c01a030480c0c00071950549a01c515104903981d600c1c13402c056110502e001c805002903400710b5582d05c1e0507080c02c02082c2a02403215041000c40d008101c926140801d010854410a0804a0098a464003c01801609185105082c0828840f03007010300200180700d10985400200402003a00d802061011098580340050131102c50b80d002000704506200c2d900c048a801030000c43ca0004005013152100b000c400307081c410302c4c0d128549a59066140681c120b0b080250000150300d03010030050700820b01c1c0070044c00c00748605180784080c1000c40c050017409401c50840045141e4070a418913000d82242c40a024103941445181c6080040c580580e20100324848880001d144d1a40e85d03ea00a6042441000c1581000040440007002a8840340903069028040b078006d43ca9240f00002c4a45454004100c5218241040203014041c0e40100307008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741750368 1250 741749118 741749123
    0xd03050405010c02030316050c100e0f060c0c0a0b09010905011809110409020a0c11010e033c010f151202150f1b0601060201021e0306030118060c030b1c 67
    0x41d11200191300009013540039140908059403505ca61500810201081c4880020304c11544c030301140340441411a000d00c5203c07141d0740c01180d03802040ca0700e880c0c03030301c00380c02e69040c3c201c00c5912515106000c00c01185c1315a00c103415060010038000a2981c02c0a1000042e0a0a103810b04151045804440510403a4032548480070380c0c07451244511600d41040381e001c0d200380c09045d5a41c0d05201d00041000d0060130050702e1200c001400000c040d031040000b00c06a00c001801050070b054424142c03071481900e0800b81042080d00c00c0ca454581d818544880c01c0c50501348000141690885503140650341c000b8000c04c10b01c05440001d111310a04c816600081d20340646407252000503468940c2003d110700c804d0843c801d2008200c41d800e201c40c0b83d00015001665030182c9101c0e903a900c10581c00d07401030500000d10ac500400d14040d600024001035175000900500201e03a04c042000b0460240942841c16540b698a4a09507101e183c0c041c0120f003100c1ca402c0d0754815194414082c100d56800408400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741751618 1250 741750368 741750377
    0x90402090f09040804050f12030a030f06051903140a02030d0c080405060f0304050c04021306030b03152410142b0902010e060304110112090602040f06030b0d0305040501 74
    0x4554903511500241e402441001d410601542481d0801300201d412903c00c1a02c03810246039000f080e82010305d00011000318000c029030502c0c5501509401a14654080d02141661040c00044a40c1e0746845124104681c00c040e4a01c1421400e01403001c03c40c502520b00d86a004001004c01078074001120a00d80e071452501915130180c03484d143e005403150761b000070b900000202d0310501200800000354080d034800c500b19001305243c2e00602080c0d0281000d504446101644104030050003900310207072802c002800d0714400d01c4c0a00b0040321102c015103103504c603286e49804d480004c4162441c078000782032080300c0c0c0c01c0c40322081403402040340a11b0341c90303141000030115841042c12a8580550200c7c40d9884140386821740c200d80c075000078442a8010b034000b0301c400828040030300701101100c0c05140c00c02d204030385c007090030801569601c02c000c0031200c01070307514074545001c40c590348003500240c103000700e06916103880c040005040e1003070050b80c01d1068110b40d1401001a80150840701100c20a080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741752868 1250 741751618 741751627
    0xb1207171b06031f0b030103080a18050603010b13120b04051b150a300b01080f0402062a010c2705221e05220b06060702040c0c02030f12090402 63
    0x4900d0040c8100d90045d00c1c031210120010080000c1c0c58050000b6603000d941e4400070b0110110110000030151040d140c11210400051008032101d400500c100c03154510035a5145a90303c104a1080100840542c0c114680e08180020401c0900108040010106041c404100b003000040d090765500310114050301c0c1c00081c01400703940a14001c456548580328410b020501c080400700c0f04400300d914034041c42c1c1c0b40100690b880e6000781640f5000d4210f5007040348060396a5800c0c09515880030f910710621001035544004183d0403c10304c5604014600004281d000d60003002602542c0c00600504201c00c0f02050020b41d22081300320320048420440c4c0081550501d0240a02a00381c0880c20b030340158180108400d54158104030301c03001c0b015064041107640e56940801142c25000c1c1080014140c040f45c004011613403000031182c0094006281d90f180c6499640060b0494160b94442c1000c6007240620000b5454244601d000d2021450041d091b10450003554035118031660600c0c0f07110b580d0218 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741754118 1250 741752868 741752911
    0x3061533030902060c0106030b06032103041a0c0c010f09024501080d0f090b210906041a09120309010608060112050d050f030103060b1207171b0603 65
    0x100102e0006801404195545080c105d10501a1601b400152650355001000c0382242c10300107a18040004519401d1312003400954641c0c4e583c3d4400742007a1207104403540d001030340c401780900036401080125001d80e031340d125504c0302900351142e12400b1103245103080391a1016850b6808202d1020014150340c0344855110000e4280701012207a8407202039003219500c0e0b0003c543d0f2219107040c0d0300c0803001c0f6003411100d9201180c00e03410300c205010005403201810041340c00440064010180c800e2204545170800c444001e20402007114034030600c1c1c0c00030301032000344203a220141140e440540c106507082d180403002c9039a038601019503480324280000024003203c1d02944200042e01d40001501c055581d1202c140304c13940d0001c00182c0e02d60288207d9442064054821a50b8142d480d030b4606041d0b0b880c58030342400070171560111640020078a8071300b1804441c1403151102030701106a8100d04c001503031150500c0c04020031421a591000c21300e942d44103503550f2060701e03030000322255401449031a49 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741755368 1250 741754118 741754121
    0x70f0311030a020d021e07180621201e011106070c030f020604120e01030b0904030305180c06120405070911270f01030c030b06040306153303 62
    0x318188a06000201d07010003541d50100d269800020320760708650012001004140c030350400040000e807a036000020401c0b510700d030481c903200010407440f40000c0303440d643c150000408a142ca80310315103001102d400000c0100e0300380c4031304001e0038915034440800c400c0301c04a1018001440c002c01d9000c082e03130010441d070703104600309a1801c0000090314042e090901e00038051582d40d079821004603400e9018034088030310010311540300e01d82041c04224100b41060301502d400c85c601d060305d41090344540c07882c545612080c0d4868001ca100360327000142071501001c1500d030b5600e802079950716904207048505040e84d4404c2660303403505441c0e445640316216842c1030780c6130403169072200c0d0045050010880d20701d8180c00151076140641d02c0c9506400c241c100c0c054603c0c020748200c25030b0011030811418110351282e48501020b04039403c0021b80c1624142c0050720f0364004d90300c02c41d85c0301d031100000c0d2040710380140700c10014104042030301e058000c00b0940207041103210440b104a0303c0d030941a4000188603 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741756618 1250 741755368 741755387
    0x313060519021b190f0f210807030c0e0603010b220920030f070f02071a0c0c01020d050d09020a09020f270102030a03092607060e01020708070f03 64
    0x14039404541e0f5500440103d0030a9120700b0b1003141d18001e0714244102540c1c0501070980c9a076000000117001d10076965840e001e01c020302815906840540e0901540080d844400002d218040d00c6890301d614140a004064a100c1d44008003004503c055064581c0c03100303010782b41514105075680751225644264600c116205c00c0d03c4c02c0c45444000390005020640d940003040000410803056406000b100c15151140f2069400014405840780015034441c0300e941d8410300060f0030f20545103016036851014000b25080b0f07050070340658000506034800340e01005410b500341000e00183c0b50502105002502900800501300800c5d80c440400b0421581c41503000d03c0a021918011501c810341200c0c81645601f2900000700c2e2190360300f50007544040e4a08450b50711a00c142d00540c64904450803c4014201140088510102c0c0c0940c030300b04030b0311b1000443c4900c011b2904094855605040c1002070714820340c0d145809910410110000c01ca03280221180143c020300380c0f0301000198501110320194 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741757868 1250 741756618 741756661
    0x170a060e1c0c03020721110f120d080109061511150708011806050f04022503020a0201140a0207060516120504140109050603130302120708030a1103130605 68
    0x100c2603400840c10750440d1007561468080c4e402c031a01c0304e8580c0b81e42c040250620248000c072500d2400c40e54002048503d07044d4010304040c00794902070358a10040ba8605d14130010758040c0b50071004600d420558000031301c030300600c0384001c00d00c03400d071400c8982c3c4071060702c001c2004100015030381100010b01d810018205001c1c050210074071145810344d00205902420300520300385503980881c1d40311000050051005550707000300781c000c82000002c20440203522a4007060f4907440c141c044d040300e0780c00c46580f0f0010725000350003805013000700d44001030001c441c04c5480040c460040c031400c0d003819400600c40c8140e0b0820704250780e94030380340d02120703281e400113100007000344070589800a9074a45c00806401103c0b070702001d4141c0c1c0341c2c0c240c0c01519111100d00443d508407905000003004c4000040d07480514600a00541e40041682c200032641a440307400241d89008002060007010221449148208222841d90a0640c200800c10210500c180300000c0d0000b512500840d4408032200c0200c2c04c1d0f2a07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741759118 1250 741757868 741757903
    0x40b15190e0a1a0708131703131401110618010c0206160e04020d0509160f0506030f04060b0a060e10080c1204151a15090607080c120c0307050106170a060e 68
    0x1103031a0400319580c042c1c001d2030104900c4d11200b80c0a8440001032707032942d03111840103030305a03414a0b0069411506940046040001c2c04010404002c1c040c8100c0d4051500425200c4805540250040c00d68600d4000d15046500540c00c008070f0b4201c0b00000c101c0c495481c0741200e4105409400500680a01701d6000143c40c5411700f030003800c1c0e50000741c1d0311004285241040c04d207035942c540505004103510519170840300800c0040c2c01180f402418079403044c0b168100086500c0c0345004502d03100b0035500844082b80100301142e6903403030810150f08030758841d89412003262a1101d910090703800f840070303a4120352200300003040804c8502112444002002d44c1d0810402c1e0004e140001d040d6900040c8034001c2c1c0603401582c80380310b40e44045a034400c802070072540c40d010a07950303450002c0c1c0c42030345085168018003405108480c050002000307010b070f41800940e198006c0f800c0407401c44185602916080720f0107a074003850f8004c089000038010381c00c00400079036845100300c01030418423040c0c05c202100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741760368 1250 741759118 741759127
    0x80d0305041b2918040906020f120f090106120807050109051207170309060417130b0309010e0a030f11010b09040804081207080d020702040b15190e0a1a0708 69
    0x1501d810010143d0b030345034012100d1950300c00030460708551240e0501c000192060140808881c1003541142c0d07003807441050010300e018840d20040a030380d00001e5104802c4d001c0c500522a40040c403100194001008030000c01c40c445c0b600902100d205518100280f1300c0720042500011b103c020f6100c005683e8020054030484495048540d9803684031040c01c0394000f2046003c1102801580b0940303101e82d1481c03000f0030440d12581c9482c41500300c120b14401d0319030402c1110b010300c03088601001004082c000d56103526402c0bd14501c5094516a103030241d100e6000403441c1000c00d600024154403980642000000075002d0740e0007501400c200c1410740d4006203181c091200300b14614005004598980081d41d6800c0d021629140461103040409400d202060041581d030003010b82c0207012242c80103000044503901040803d0100c0f0043c01d031070000310380218469026250076110b5040c6c903165460074110310340c44d000003e04211698041d00d00040000c800100c1804820011101d03490303004903015403503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741761618 1250 741760368 741760379
    0x3121f0308030702010e0a0c03020603040f060f1e0c120b040908040305150f091203070e0907021506010212030415140a0501061e0804060e010f150305060709080d0305041b 75
    0x10b54000d94150b001586003a65000c3c1c058004a030040100c2c3d80700d200703605098a503400308500b6030805041652091300d00d025403800207601d84645c01148010350008100e40c11015008094024804452910181030121002c101540001003502c01a020b02c03000508004ca400803030010540c142004002c0b610004010043c041c000030b09200c3c08407007000703000d100d0340c48200c40141088242d400400692001d04020382070310019001c4c42e40b0a00074a4080c503955014030008404490580d4400d001d600b0400100e05800c10300704020307900c018207000a280f00c2c00001e58600203484020070141008100c03503151000c45895820070480307108071204d00b42c01070500224440041c0707828494000030590760b2804611901111841c0d450712a030300c1d15420803c3c1d4071030f1100d0024091460000e102c5560310401d02244400b40e03c2038250500005244d02c641c9400d51a10900d01203014010809200b1103010400884600050a0095500621300401e1586039450a548004006000803040306d9150501044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741762868 1250 741761618 741761633
    0xc0904180204180c120503072109170c011409060304030513050312090d05120408030a03050901021303080a0203210a0c14041a0409020a050a020d0e0303121f03 70
    0x9016000b15070030000c94404401c00f05240c24600320042070803103d4001042003c80f10460001c0c810300031401e0300e1600142d0307507a500c40106400202d1100c1c7c0e4403100103038201341d40804408090640021400c01d00c1030301169041d69800d1249455040140c1d01040d05901c24114041e20302e0018040c090a07100d05080c540501150031040c422640c40100c108001410b14000555080c0004a11901440c00c7c1500090040c59211110305440314800c46103d0780e00740f509000104003c0c00568051078541c444020000d007615005440480103038014029400045003c07010a02105c2d030280d903642d5581e0400c0401d0b0300b5405420108812254a040b04400043c0756802c010301c100280e9104100c40317402103a0550725903030340d800b02030040c9a0600052000d403840300e00c4203440007010f210580c00d05684100280c00c0c5d0b4803100034200022000714560b001241c041004810441c001d040c2048108036a8000ca0765038004c80f11103c00058a0101094035500004110138042c044514001e031b40c50307100d04010b04e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741764118 1250 741762868 741762911
    0xa05150a0c0c0b04170d0c0204020c03070b0f150d1203020a270e160e0609030c030a121704030507060b010309050a0302210705100c0e0303040e0105010206060411030a050c0904 77
    0x285d60204c1c00081002010215040c80303000050388038510042419000d1100039045081c11151502c0104803034004210340c4400f0a2003110012199005031405149a82440901040c3c6178001d1000c601080d00286880c4e80030070020701c0c0b501d001a103c901a400844110f00400701c10032500b600e80e141d202130108002411002d581d221110400152216140c90078200c06070502d1500103542c80c0d1010001e80b410000510440740c1c010110303900560503100207400d0003c081c0d4110f890a1040c05141511a0400b17840e640180c03124080c0380040c9482d840c00b818620030044002c0a05d0359801c8410480d03806a481401c0041c1c200c41129140c0410307150181d9a200840d0400c803910442c0306008881c040804100c0740507981c04070140020621400c0c404000e88280c01c0f40c3d03800e000381600800110303101080500000d164116801006525040c00a42400809031030f0a0146042203880d034045950302040740c1d0400c65524000840780c4d9032800044141c010351000b5a80141040c25005050245030b0741903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741765368 1250 741764118 741764129
    0x1e080306040c0e030a02151908040516030b160201150b1b1606080901020d09050d030b030d1b0f1401020c0c0d020a05010c0f0803010303120b0a05150a0c0c0b04 70
    0x20403801c0b21030001902d961100e080c000d50315920542007000142806425510021041c013412405c00000003d90700302d81100c01c00c072400290b4441c0410081c000300704600f40390010b142c14040c07981130954032202640c0d503000b0080d4540e05030358500000355501c00d40c400e04100c100f0301c45140b402622080c100c00c0b560710104101c1d01070460b03047c03011545440807400c40c05814026504013410f924044007a140540002c042660b2550700b0b00503000c00344854020a0b0803903105002800c1d24001c2100054100e6485000d51800b070741c061603120220307681080f156a00194482d003103010a02a51402e0540503c07072400003080034200596080d04e00301e05401070203a41c0d81740415101150850740c14440008480100070b9132089040f40100000c1d402225007d5046004400f54000381c030030703900d6035a41035000707900460000f0440d104d281e03a07100980c45000b1849604480c1501d041385004c0000c0e0900c2d910620f17005041c04001a40b000149c002c40d0381c188101c2e448680800c480c0d69134010300909403c10301c00d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741766618 1250 741765368 741765371
    0x222606090c010225080307050a03110303040308180f0111041511370503030105040c05090a050906030c030f01150503150a050a020702060d0902010e03030a05161e08030604 75
    0x300306000e0012484030300054069006100b601c402240114801c050110a039002c0c10700840e020400041c180000c05d04140144000c10000b255858010184881481d40d0030440d00180107002c0001ea000c260300d0b0304600c1c425501007010101d032001c50708000c440d1079035600720341c41e00345584610900c0b10003070004c448051884144600700440e05982070000e4606c4d00095801c1032004250942000c3c654407220348140c8405482c003004103403120410181140700340c49d50f9001000401c154035041c02006000074007490900e007401d243c18040707101000507001d9184240890000200d0320740741049404c030703012802021240c495080111241c02400104051000148550f20200d003a040c00200da0300c0498000d80c4104240e03640300e410b0001480701901400c1c01c0c903002c0100001503604c003005842118145200020f84003454400580780380c84290350035000350824002401040c1d0413006542e00941c05600d2610b20110070b250224041c4540780761484c0300840c4003000c000340000307030010758420b030800d850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741767868 1250 741766618 741766621
    0x80406050108030a140c12070606030507090b030a02041116110405070302120708130c031101020d020c3109080705240610110f100b060906222606 64
    0x551648103d0004c10041424480103a201c060081c1c010050101c8903000c1da94400c1448049000d00e030701c452800d070b402da81c440600b8401c1c003d09114002c0101084041080302d0322a9502003178a50300e8021010f8412642e5242c26507518484c0d01c2122002900c4002800d46020302d80781800501100789405800355182030b0024000b54060310031207001805d8400d18014550b210f020442d1542002010064905000000b01002409000500d0040d42c803910814800782071910009140c00801c0c4600e0341198007141444c0900d4a0302041c0c003180c1114548800320b0507102c0d9500207411084203483c403040c40c6c9401c40c09810321405001602c1502d1003507042c1c850010f20701008810302a1552100d25102b033180e00403038010314040844108103074181c100000c01c001c0c400035160410381031401c407801680029142d900d0f40003480c424280d50380402c484d503d0500302d0550224200d401991482003031044100200d82642003261201001481c00310f400241035151048101401188503212444501c107000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741769118 1250 741767868 741767879
    0x4080709050f1b03180a0c031a04021020030c0f0d18060c0515070306050a09150608040305040f03030207050108090109050c04050711010603120807090f330804060501 73
    0x100d6140c05038840550812514034201c00d5810b081d40082e0103400402c804221780c0030007680c01c0c0600b50303400740101c40720b00f4807601d0340c107048205480c8204242c0d5151044020000140d4580501444141051921200f910034480d80844030610400901c2110311011905810711100003c1076001c0110400030703200e240500910586a0907180c000c44018022860018452103110b0241c840550b030241084500002228121101d066016909100041e448038020301280c18040b506000400081d002004042e2140981c1c50304192940110303800c02600201103008c0c9072055041e01c020744040c624110100c1e9591030040d41d6030a0600c00c10380450308000000d5502c0380d045c403070351803d280c000700980000c0361000d0812005000091401c02800020440030320340c0e940c240300b440f0280d4403a40071442c00390045000589810002071400c41085220403040c44000340003128030080364505450040180301c0954041400c600200101c59480b001d00c0401c140c0660001d661800345000d6442004984d80f1003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741770368 1250 741769118 741769141
    0x904060806131406160320030f060a061407061a06030c090109270b041e0905010f060501020a03080621160506190518150d06140d031d060408070905 65
    0x111602070643c0c508a45d4511864025041005024a008040903015041d0540c140c49a0810b80381221091000410814141005180d4802404685c00c040072010380d41103210307003a80308034040240015100c05645204060b41d112880c039085000306919164036180c2d41e207c2c4203801101034a8000b41c0c910314005150f004501a4502e1140c02d40380000710b200b84002240080e0580015041e001550340c003152044c00d0760b0301000308030400300b03c90200d940441420101e0039600030808080388030b45804810000c50380c0000303801550035071504000549983e0b20001603230048004d030140c0f0111642c100007814664005c900448011003580708400e0b06e9486d58103100150007044030321911101510000d180d07040c041c0003c2c0950f00d10442d4002d0a80c84141c6c08600f81c281c4c0913440e000d4044010032504050340e03440c01464007800404000002201004000030507280110002809100020f844640e00c07040100b00245c0c001c201801c0180d583d6603849285507941507600c5076415881c5000041015038a45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741771618 1250 741770368 741770371
    0xa03080c09060a2106060314060f0603040b0a020d0218030f07061413230a17060705070312061404060801180210020a060f090b0105240904060806131406 67
    0x2520b03590410302c10318029144006020942c1103211071312280c1c1d52400c0031501440000d030a25a030081040704c031002c1d210f8144000a04450f110350b000d542d25544607229007013640c3c0e110b82c100c0c052940f00c2e20381001100007440b40100d441c00c130300e0001414000c4814000080d150082080c1c0031074403022008012207440303160314004c14001800c01c0d900030001c01c1018001d0000001e03000416803000340e80b00d41111003112400d0101c40e003107200110080a91810f00c3d6a00020003003103200020320441d49001300c1d1510802006401130103004a04282810710422550b0700c40c0b401004100700c05600c4644490a0307698207020988654180350300852144018010340c000c2d04103c0c03850001d5010980c0c01c0016940302040c2e40d82c00c42c415400000e01188060041410042c0c540c4400200352041d420005070915050700103038014210041003030751480d21403049403030380c1c000510700c4c40c1c03140402000075001d80344030b5000484600c030b1007013480302d4200c00c0c00b68000308900c60070412406210380c91405859032070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741772868 1250 741771618 741771637
    0x307020717030f030f0601140f042309040f2001200114010b07031b050a0638030c090601090b1810180602070b040b18030f0a03080c 58
    0x30110003003000220700d03101086104900c00c250790400c0d015801070009500105d41650500150302c040c4619540c0000d001c56070018031021062410500d10009049417059102d9088055090b140030849410700d009044801c40c4001c0200c50f850400307092244000120010070f4803080c0001e004150541500d00410912910603115000414420344100c0c0c90610102c00303007a155500d65000618048860707401e18040e114198600d03841311a05e04008280c0341100d2002280c0d14980720080012901c0013408502550f4011404a44060400d454040718040001c000040b009a8144507000c3e14120701040c0740ca00d0140c040360038894040e8104040e07100305503a4107010901314102442002e01c0d00c401040500d4460300c0c0021039600715008507103c0703414034603c4030005012799008000d99401e5941304c4014070180c8001d00181c0c1c00c0284081e00ba11562290108855002400c2d9a00704031040c5014400030004080e075581240c81c0c02003684030180000b080b40050031190006100704407a005a441016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741774118 1250 741772868 741772873
    0x20a03080c2511120703110603010e010b0a0e100f030b180f0406091b0501032003012c0106030519060303050d05090f060a0f0f0501050d03030209010504121a0c030702 73
    0x810050b040310420510b5076098031110021660900c0075140c20541114086404e0b00904205c0c2c07960074001141c0b0903c2503202d125040400040043d0345003920603605440c000c5000c030365607100d040b40903034020364078401040d007040b0900803003118290003d03415445030030b85450500c4007031000c000b0064490804c42c800c0c49007841d1040420088087d5607110340e405442400d00003403003540c03500c440b42c2025409030300d204c000f8014402844035503414020b52408100c00003070807600546401e20030240740014010324904900c1244038961600d020b03002810071074002442082256100c60005021301b0b021118510010710982d1814500c64182c882c101c12650555079030f9050048a42100000c1c1c4005085425503119003e40100e40210a02455015030307880c1a0000c0d400b100c1d0103160041e101170602190300b051802c80104000c0c0c48800c8a02006981481d0040c0c0c1c2e03440c4900141e8081c02130390030004a400760200b82d6420820001000d4403c1080e40c1c25184807070340c40c091101c001e403004840c9000184c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741775368 1250 741774118 741774157
    0xc041e02070201180b0405130203070804021504091107060627150914040c151b1b030507050f090c07060504110d05010219050a0c0b1504020703020a03080c 68
    0x2100254007500c0745510514040459210381e11100d00d048000742c00c409404180001c0811152424600404450b130b0303407030410350a40c608120050000000244083d014408900d82c010350b01381100110340191515080400c81d04074602d46442c0f00c0d80011400b22100e510303100001ca0b036030546183c0ea9010105a8004e8440780c40b0200294001c4c00c0700d4100c0c10a038002554001c500401e0600070390802e01e8004940081c04c0c50035085c04410301f9855072000300d02c525030505115082e03a0040000a0344100080c945160884038a80b4000c10388800310301b580c800102400c040108900402c01408403074080701c0c1c0920081e40c4008000007024282e0351015501c1c02040f403140000c40c240c11041e4024019801c4195058041011074544440c0c9a0202d03404d950004180051040804d0078162298040c5086070610a007524041c241031781403480034104160301d1000540c00181c0030006460b090024206648801052401035980c20300448120080fa44090004080f05050070a40e881d00010f1460620344 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741776618 1250 741775368 741775421
    0x121605070e100909020103090f051501152715090812030c0d0c03060f140301050f01150818030403060f18030f050c03090910082119110d02010605030c04 67
    0x4000c0040200c6c14992900814030205901c003c031201d0aa0166020b0320700c0001d0b10081c980c10400507040203000913218520208103d50001c0c9049094007840040701c07086400d2023507000000c81030f9000d1204100760302d00408060741d0040800c003c03503200c0c8046840e41c041c1040f50400c81d010031116604101c2d01480b0031420018150090fa01d000850700780090043e03141c0e41e22400290858201c0548110b25100601ca581400d01c1644d07032250680200b0602941404022003043e040c59141780b0401031021702084100034000c054641c50341911049a90f110303601e1030014041c01d040e0f51000542441c1201c0300104801c40e41c2e03404562030f03150340c03070301d0262046d002c060b034803038006d1101d100b064842802201d0150b29200286805040304001000e401c40c503200c08145040ea9a10021508104500324103080e144020b0a0ba00155100140800100c02c0e001d003c898180e40ba02c1c0101c0c241c45040384641500b501035202100380c038400e8040e925011041010f000075604c0081c203012008210b142c12044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741777868 1250 741776618 741776621
    0x1104090614010f081b3607030b100c080904020f13030303051503010c020607083303191511070206031303030c0e061b01020910030203010e010e0402030309010804020102121605070e1009 81
    0xf541d40d03644131b043d401c040c2d85415440c0d54041220342d107000c00d5851510341c05620300508001d1005800f8276000c0700001c5a5916180b0600454180310301454001c11201c41b8a0850025601d44905201140324141d80c0c1c0d00f0020080c02c01a20f5040229044074030307010003810103000e041070503100c0e43c0080c4410785480d8030486807810010951400001d42c9010b1742c05182c421010701e40d80900041000c241c1d240000c00b09402c1208003641c40350962655070710080007500c46001d8000d020084c01000400c0405180801c00c4e520800b0402981300400008008000c2d00155207401414001e44c0e0810003455000c206a404075484418241d10610501c400c0601201101110103000d9070b400015041c4010000440c2c41e1011710840440443e401100502006008003201801414458030303800c55800c064000c26100d08c241114581040034100010301564003c21121030000e035003000382d035610442c2402d042e40240c2ca070b10b02281c5034040c1000004040840c44c0859004505100c2001500d500d441c480c1070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741779118 1250 741777868 741777919
    0x7030c020604050a030b0105120f061b041a0c101116021504260c1342050d050c09070c0b0c091c1104090614010f081b 52
    0x20707404401048085820b031625515800214810010320000d03504110421034100d82007406400e2075400607a039051180c0f000640d058005007000e030104e4044100c0c8404903c1445140c01c20f19200344413000e03400407003e00000908141840d0300545070415080c8603600b06490050341d52140c214010f00c96803403601e0440400c00000b074402043c80c04030440e100030050f6076070042d17442000038507a200e1418105e0307542640c0303043c085130310040a0803411260200048111120210509241756a14600e03011168252500c81a440200c660f05020500400a03c0d8460100c69050005924038a000141504194080d10303c803560041c05040311040c01e80511003103080082c00c40d010445255100400304040a1001d40149000401551f0302d43c0410280403081c003c0d4a130304a030f106142d69400001c91324056500d4a03040c01258049000c403194148007000d00424100166203071554400040c260b8002c1c90701e2402c480b000340035034010070304200340c080404028a414541280500210300704400c0d540c46043c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741780368 1250 741779118 741779123
    0x3020f19080105150a1205120d150f050415050a0b0703020a0f1104060501050a0c240f0606030506090903090402070305160f140a11090c1903090b100b07030c 69
    0x9080322640d51a660303003520400d556850202c0a20204100a0708007075599502a02c4003408196425802c1c2e62141d545010400d00e441d0400c0c004181200003800d150070080b801c09401060001030f0b41c8620f40721506c0d10741486028420f07850314900710900e5820801407c100c41006240d0340065250901c100303502c3d807210340100d003180510040300001a06101811400c0da004803005011508071500b4001110850f820440c14410240910035440b6401102100c1184d80800c03100e07101d54000d46241e443c0310b21800300c3e0381c40c2420300c1040c81c9000040d0744110b0440c1d400f40c1d82401075032a604203000010b0700a070fd003070003203810801000d9500e00b402c0d002411181c0c860f260661500c101501100300042c092801140d0401006403104280700040d10041d4440c0c0d2040042e0103401e1107503851103044480c102502c0d00480c400c0c400501d1803d41541a1011a070043d42041088000b6100003002441c8000c011508800d80101041c0640a051403d105442c0804007291401b03440e41c805842151114208 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741781618 1250 741780368 741780409
    0x41d010510050108061512040305040e100b0a0f03060b040605030a061208120c0424020f03250f050307051005100e0708151f030f051003020d060e060f0403030b0a03020f 74
    0x684107c218200200d030311481c000c0d500c180c1ca4600b802e4100410703030400b402685509004040c01d2081c0c61100080300e51383d1005090108003122b45541c00d0380686116403101044420200300020f5060f00907008520400840c0000c00805494900501140000401c050131080c024001c902e4140080e021441e0010308100c207060034941e440150480c0e664480a0044600f14070201105c401030f01000044401c065060156003000308065032043c00d02001c030340c00244031a42803180014007510b1410003003000e4101013038940d120100d00340b20341e94504100c18450346500c0c1c400041c83d510327902100e100a450380100740d03c155860f1103100305e804440103001003000321030b19004541c0d5903441400b030100c00c08100c3c4044a24140440d80603081b91150640000464180000c01030b0f80840c01608400703403541203a02c8143c41c503d07420f01100a080010000e80da6220b00d0051217944418a035100c3e04c1648207503001d10101e48486c0510103841c006220082d000840e800c003091b41451300f480302c4150b54000814 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741782868 1250 741781618 741781627
    0x5062e05160317060a060816030b180601020601060c0f0605060f031b040b01030e060105120a0b0f161805040e0118080702010e030f0304060e060702041d0105100501080615 75
    0x644001c071148a100b180454000f42046001c0003603841c0300c80d40302e5811034070700030700c40c1c508000501201d00050807034080740000346a4102c1c0c0340c0683d201910b240b6001d4400e1010a0300a150018500410344095025116040001506a100d4603240402030343c441410004d01e40295101d0010305805040c1c00d60240548040c1d08090310108101070240080d909610b0302545130394140b0046501d1405004d041608103545a5145140000e40b0f604590094a500856401c4811454184001d0700b40060068481d0301c1030100070000b0074019802000881e45024403000812000e84145030b0010507d501503190510170480c510b0654400201840c0100000c07a1003101300e80210910020031004075003202d004a442419075030300c001051040c0350154010801d05042c0503106580740110711460781000000d01182c0f0701c0752a01000e582865602038014041107110301000c0e03810703035083d14464690358030700400074400d004803080001c1200c07410303101c0b99496145e040901024010342096a80b51410810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741784118 1250 741782868 741782887
    0x20913082713061e26030708030408040302030c040207021f0912061505040b0a140105041205010e061f0308070204020f1615050115050c0708070b0703020105062e05 72
    0xc01d02528100c210074000f5540b400e2000c4040e20f0a01300c1c0c007102450703070501400d101c51301440041441c10000003602e00010209010a0707440c512800e28010100f00300070050004100ea0311000d401924404c800380c9500070003c00a0201b03e0003200000307540b02c0c034021100c0c610740311402c3d42c40d1040400c5142000d600d90b280c038039140d0729a043e46411240716941c0c0c0030b4000305500981248002e41400c84051128035140b1000030801c0602c1e0041803501c185015018409178012001c030390042412210418813801241016402002d140d0036007422801070500103040860000100c504010f904034007107104504580300c03d03d44d9000708004a80040c0e0070070021207040c5d03452014021a4809002c00580c100c080d180414011511003410f0445a091030014042c80f401c84030354040e491020310f0701a4070f9070768400d4070525145055000001c54001c929001c64a002ca000003015010301a400074011515444144440c000c0819145108410707232036149014140501ca4890401d000c61920609081410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741785368 1250 741784118 741784129
    0x3020a050607020a050c0910061101090c03060b0907110624030a06150b040e06040b04020715022d04061b050105340f12110f04030209130827 62
    0x42d18040d0141e400290548104003003005074810341031040c0c81d03020075402c05001d8562199018021141840b40d61041c00c05095025072050943c0c58010040c508031654130309040006000102d006401100343c00300041e407080c040c06a114101040c02c00400c060742d5014208064000050300c3c01c20841c52840001040303075400c000601e072283c022440010381350350301d501004140e030350b075803029043e054240001c000d10042c1c2110b00d42d11140546000c1400c02205000030300a11034034100038083c140045e103844035008550301804011541d8038031040800e8810603003400800c0407030100169140200f1003440f00e20311440c1410710214440d10241c2115540c0d540b0070f0300b559821101d130030a0f500a0320030700f54407001d04c0303260355600132485030803108450500e2001400c0054070500282400181c0391209444000c540c0014680e0a847c90203e40b1003540d2480301425500512041c4d100c0c1010034003003003000c0d001181265105074000800341c5400303180c840e194212900880c103a1840c3c40003032029001501d89 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741786618 1250 741785368 741785371
    0x60c030f05041119051302210f0601030506060910020d030e030f0d1107080c1c0f020a0215130e0103020f01050c06040605040f06060e060a1401050706050a020f04080a050d2a03020a0506 81
    0x301c6c1c2015841d40000e081c511085c80d480001891910150b10038041c03c3c3d100356404a821900a20700402e655559002290f42c62141c4007985400440c80041000f40340c1e4042100021580030741e800303110f00e4001205955581c050044a0715411300e040002d076540e00c0c8260300c903400300c4000440352800c0c10055154044250805158031840350005a500281107920310902000e802d0903061002d1207400401009607920714803203009005103440440d000e03a2031810310944070011000188809103d8a0743e940c3c0710404420700c0304900034504143e85d0741140d800b52056554400782035004090b50369507900e8002c00b900015105940082c0c070300b07000c0300c0854068028070020300000aa50442400e000082c00b801e2112030f4045e9203400480c3e003c18000341c2e448001c880c01641c0085002c00d60342ca40040d210024030944c080c19000610004002414000102d24040c07414003072800da851640f03194605030b503012a039628138490082e411452010703200040b0014450744c1c0c000d00c1280d41d00e0f00d03a80d0701e551a103c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741787868 1250 741786618 741786649
    0x30423040608011b081e04230106260307030f1d0d0c05130e100c030f09051f02030601020307060e0307020a2702120705070f0f060c030f0504111905 65
    0x2840d00f208100b40783c11054082d04a244202c0c1681c2c6c9400c1010881c1c058100a00001c0c41c1f298060900a08402d0311200c141c01204000c0007081216900c80071140310364072600301c056400d11040100c11302c7c0c00e030101c265000b00e50103440300d22070b218040c2401c0b90021213a051102da403c4220081c52070b151a00c10700288080e118516011b4254140700030806a2100b9030f807070302d4606003003a440901c000004980c6034209560214081400186040c0a81c06004482c14000316245041d0488040c4500014030201e080441c0c29901c0114040311102d070300b80e01c800c0794034070b0250b0b0080200d03d00042e80340c2e110a00c00728100e030660b0700b000096400624020f6090344102e148646c600010640c541412255000001c0508011850440d01d10308010205000520350020b12201066020500c02d081d554001d00c030b9841094802c01885910307205000384009010040028601000c4004c4482c451054a00403500708008051145440c403c0060700250007441d0f0b80390200c1e07a01d00041684400011fa4200c40 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741789118 1250 741787868 741787901
    0x30227040b0f060301090f1506030515042102060402060307030f020d05091c080c0304021f020f06010e092d1b0f01210c020a1410050903042304060801 66
    0x3032600b103400c28082c0281c01c00d44203901d000c4c2d058000a0225a0f00c22003141d0082a00b41d9040c06061100c004001075070014000f070040a01e0703a19919903405035103104a201710155441d580c003200e84003040c1c201d035020070f10140c1e001c407000c540545800b002a43e07103d1740901d00441d0101d02c0f01143c1d070980c2c01050030541404d41724028020001c605200251102c103001d13400c52400e200c0e55800418908010301854281038000000c202951960340d5005003004031120302c40200d00380028001e582d114240c0201c600e0740035100010a030040c00701d40c3d03a4040c46494008160742054402c0c203150500d0000290301d0542003a442364008003505001c070b070000404a500702c1d0b103405610010301c8000f0710041c59241c100708104034484522958000345034a90402c07a18001100b070383d1410240d28140400001900b03a00c900c0d8200a45200c00041405402120f460700b8045a114030ba03240e584c1c1e00850060b912619a5118901c0f12218646148200e51800810206107150744220035070840e03030b0751a4800c0d9000c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741790368 1250 741789118 741789121
    0x5060f0d031e140a0309020312030c211b03180f0a060501090621051204090b030f0d080a2304050307050f030403030c02010c0822150c0804030227040b 66
    0x810505000c4000d106060a203c9a442c0d00308104404a04c03030342d40104140f40c0d480707054800b5034408200d00c40c2284d031070300c0480c0d55078103104000b6500d40c3c20641c61003142c40d00c1640c919241c0f10740b1201960240f546000fa030040100000c01d03050860300000c041c01103600904910a1403280200070002407000d480c00030304040001405c1020540c0c1c016008625071500b8003004101d50101c04812070b01654200b01000000d194904e03140742042590846c442840c1302c04a004a00208603038003040c59002d088088821044e069044203450b189001044808200200b00054200302160401d000007640322a114003903040c0050f00b1035010f80c050714161815480802c2100411070100040541c0b61403041c02941850701d541d8004084080c1180024100099200c1c0d007010002028255000070089642d405040a075002580b0b0807500c1a100e60381800e51420764104589009040b02c1040e0340e0845c076014501415a000d01131240c4800d00d449030300030181c17100c4041544104140d94080ca208050180c2035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741791618 1250 741790368 741790397
    0x50d091515083c0c0406080a0201080403050f0c070e040c0f080307170409051501020610051e060705060405010902040506010f050d0c140a260f040605060f0d03 70
    0x1c9850400c1d4040c4048a500030034070000703400040c02c1008680e203040d1020810724071051240070002c1e000001980740c800d0400307803418030408620b8101e80e00096404010751a80d070b8081c82c0d035a0f050140040e0214800f24041004a449500204401284111074500e000e00441c3d00c5481c0c8043c581c004402d0f0340c042002d000c10004000310120041a902112048813420304480c00c4e180c1c89030000040c480146190000001c050140940d002084c851004004518151041441011803002e81e540140030764000243e00c084e178601301d075003a554007030300b4003c00f05c0c0c42520360306d54054803801c1c166100da000c0c85800b001400070400103100d14411390002c180c0070001d105206c1030700c0025040c1810310480f008a00580d81d402030076541d10507000d06010a04502d005415144683c01d40c403040c1504000142e250354268104d0410190180420503691420070b61151070388810405039903041941004201041c0800e4454101ea40c00c00001030100801c1829100010f80441401000304e01244101002115 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741792868 1250 741791618 741791621
    0x9060a03050a0b060f03220c14031501140f03010902030a14010b01090302150306151b0f0109050a081804060e0906060108040b0109111c05160e0604060c03050d0915 72
    0x1075128090354040e05110107036119810b00e000051480c1c5035034481c914a196040f1044910001c07c90300b12080503c680d03194106407030815840c1d146180280704030b9050214a520300124113048035032145da004038403d40e80081144524102c140c0b81d60640d2503c49810241c0d1b02400880841c621940784108020603174201c09003914000100e40d418010002c01c1080540c03203495035506800c200850040e603d40d5a60000340d6141c031000000004d508012070054140e9502d03c0300301144020240403121802090401e15081c0c0c0d80b501c900034151341150340390100003648000a003a000c410f002800c100c00c2800e50105040360143ea00a03000d448090042c85480401405001d40214081c82c1c441018036040d210f0050011041c4100007041d0350720720108110311840707000e031078004404074103082413920700d0300704040545070544000340110a6008580d041a01404001d11105000b9004034140340c0303401c2c019500228507600035014800c1c10492019006994850010b9561080345220441c4070711440010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741794118 1250 741792868 741792881
    0xa0c06180608070203070b0406140c030a0b0405060f0405101701020406080108210d02070204050f0105040e07030b010b09010311070b19060803090603090a050d0804120305070e120309060a03050a 85
    0x3402240b505200e000c69000c01102c9100b030304001c41c2440d075200d5141410041c0415030050b07850b00c01c00c00c103101c00e0404500040d0f0107140b03d10000d11001c41c2034810001292000e60749035500c4039400b103100496050076040715034003040c1032400b000b10341c2d03441e4445045030000010b0550140d5001409011701900f050885024110038030040c840101b2a045190b01d13034001c04043c21130f200000c20400c12400c2c0f1901101d140940c060810721490404880a00c2d18410078001d03184140d00303080c404821480c1c005a0b0004680d00705104d20f00c2a403030444040304580c45080440d0405131180c403011800704d502c10007040c40ea4440d1480e1000d0746070004c82c84406025160109400b641040010040d9100010550781511412102140d49840d5000000e1410416201c000c0c500e001d5519016100d80c2c01c00903aa01c900d020328414032102d0f038401000c40c01c62302e04455080c003007031503119000c5460405c1400948030310008011289080004030004080d60060f0030b9900000751074604000004c0068007510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741795368 1250 741794118 741794129
    0x4080106090507050a12061d01050a09050403120b013b0103020a02070b0903330702031603081b0c0705150f0a230a09030303050f090d0c03020a0c0618 66
    0xc0000b401c0c0078200420300c5c80303220385a8017080600c01098190080c0d0790300c000000d10b20004420302d02c1d42c1480c030004e000390091003528031a11954900084c004100c0c002c0030300c62035155591038400c40d801c541020041040300c0d202810004290b442d11300d0026141003051484031080c0d000440c042d00e402c0001c850815001300396040600500c8120015034000031103c00b503600500202d80c444483c100480c2c40e02c4428200c6500141072079414030030418a00000503444c04421180c0a01d0b903480980c260b03603d00c102c45035142c3c42a9810000e20100780704002c8030f500065000100d1085c80003070f10001d4000d4001e0100103080b81c200203402c0106103801542800b544d81402c8201c4d003802e040075503482541c01402009400d01100e00814031880200340b488205240d00c0f443d0700741d111140302400403d108101c0c00b045021902e0100403c1304000a00c82881c4188600c0c0010525210070b044101c0e41944000070440552103802c0301d4900190000b001d02000c2d2500341e84e0800c5804001c15134444281065205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741796618 1250 741795368 741795371
    0x4021207060206180c0613061b0b0c1c140106020c0a030206030f06030a08070503040f14030c01030b06070b040b1b030403050412150912090b0f04091104050a0b0408010609 75
    0x1c0184640201d81e040e4048000014401c5400c0190050340c00e00c1440c8025550001000072180c0006c56041c9030882500e520342d884000f0240003442c015007102c0440806040d80601000181c09001141c0c0107040c1082008411100c800b0801050800d507250442001c0210307407d00018017441c3d6041250303441924084418044161030750300843d40511001d80203500c1d6421403000240243c0b0704006803050a613203c0303441c2c3e940c0c2c1c0311401e05030340341d40140c024008005241400010b4103100e18801c08400352004002e02011503606e0010360080501c1d070001c07600036900740302002c0403802c00091903100d1401801c40c400c40c0e00d0503c60005650500d103141d11070305a01030041c4008603034080c050302d0540c5c807050f90411509076a82802d4154a10258120b0701207818410f140c1300308050400c0e000110080c644440c21107035283d4280140c60300920500c100c0b00a4180003c0065079440d8010030030b0005060000c0d03140c0384c4ca40e80460854159074110002009000804000c1280240300d18030007012207000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741797868 1250 741796618 741796633
    0x30212030f070605040f0209090d02010b220f1121010503010c02030a0f1707030b1207050f09180616081e010b0c010f06080d0e061e070804090603030305040212 70
    0x403000440c0a0520041c00300b581d101c4c00601000318124118000039001854000304d4580010020340d211410b81e03074103005500704441e000c500d04200c210000320080400050003203058140c4000001e0004005c4401155140c10f07604602004000c001c0080b0382090700c40340c160341011101400ca201d4180e10860290f0316000d55480103980c040142c8040440918107941c540c0c84c100300031a81944009042c031403104009052081d416010390048400d10000d84140e45101c644489003500c40c0864412141c0001500851822600c1c01900c1c4c198000f100150b03190710b119003440031503d84981200d5580101c0fa03210303003440303001c7c0d0821901503012950b40b1485064621110154940c441d0610401e10440400714240819010a40140e01845076600341004000da0300d0042c550b03a0030340040340030081051503801a605041560450705405402d031000c05011825040480d40d07a8002581a5180d110600020452000d503000d480b00440c001d81d004561030405004020116841c80110342c0d59621005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741799118 1250 741797868 741797887
    0xa020405010b04030b010e0c071505150d02150c03070501061e0b0915030603100f05060f0d170c030f0a0302040f080a05070302150c01110703090614030402060d0204030f060603021203 80
    0x945540c191f60302a480303038000391039040d00750354140038007600102503a405410f108030a6195500251141c0c00c8030007403040e500b62150070b0200354030700a8400794000f1801c0c00c8010804200740001d0140301b1a40701142d02e045003544995007140c034103070000c2400c04103101e10035809880048910f40940030800d0140d250480401c001000d0034504192110241720100014110b517800380110b000900d81d080040c0701c00c440c6092440014130049a0705441510b401c010102982080c0c0d054080190340f10060300700c16461402805070640000e066580c0a100c204480c807080300e8000c0181c04214032b5520050f807074a017401e0769004c5e0004d0340c1d003018400380c0c0500900804198001007440403a5016541c00080203289540c0760058481c04288186540c00d11410002c42c07072030280204201806036030792406580c0c60302403c499920071122480c400b50424404500940340084c02071541c2400e1020051410b40c0d203039a41003010762150400e81e00155121000c1055081c0300708103003880710103140614039081d4041e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741800368 1250 741799118 741799133
    0x3090605160b0c12041101020616020c041a12060105090a0b030a03030b04060801020a0c20090411012001050a1103070c0311010b0405090d020d0c0c03020108041703090a020405010b0403 81
    0x181c018108241a03008101540c03002412280303c1001c51003464903030b1a00d402c207420000b000200c428014030466001580c002c5001201e22003d2840c3c0c0d016100c00b00290301000007038580031043d600b5080c501d40310075040c2e544001c40c101d0030074160005070500d58500000c000e03082200030403012980b402c0000204035944c011444c06074507a07150070002106024580803c00912003034010100c01c3d03200240605181d6000880c8854491184080c81035803444100b6810040c03407152002504a800500411f000822503901a900c000c1d06142c40e2846151080010541115851692480c1e075076031014001e20400300d010b0b000100e01094081851802c104074010294009044c0180802480200241450741c0a400030b012003a40180b00b031085040100d0103e480c1e4841b4001c1e032000d8424800100d00c200d026106050007140c01101c03100c40d407851600151a8070000410440d0351030000070144100100603400395000da14640018103000b01d4a1051108842c41a004844400014001040000c004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741801618 1250 741800368 741800407
    0x183f0f0a08190917010b1528112a100504150203041e320609040b12030d0c020714041d03030a093008060d020303120403090605 56
    0x601c0c0b42c10890080000c4111481c01071900500b030a4481d19054001061054005031204141150000101d44294094000078412840240c04507a203c1240ca001c220b07100d01220300403102c41c20f0868410b0383d2451403a0030f104410601006030604d401d010903a425544901120900c4241ca00b442d044c0c4500701c002d00140114440c0304680c07201c291180c85018800e00a03076000704040d0040500494041528043c0c04403e40103103039480c0781820078020fa040c2e4600040b0151800480c401c0880c6800c4001c0c4100b581c000ca46e41500162070300c06810072525040386a103520406100a980c690b030041d2692000d560101030604119401100306003c04d1a448802c0302c40709100300d030001440030510074165201ca00c6a00701006d00d0001204002054090303812a00c900e42c072401c11044148030392940d41e4020f044201c0700c014032440e400220703080360780242d1907250071040c000d206685140072a4000381c656800303030b0010482c0400e20800c0c40201600111848050201401c060b42025446080540303807202 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741802868 1250 741801618 741801637
    0xa08181b030c1f08061c02060307090e040302060106020c04060503061f03081303170f030a0509030c010608161a030703020d0605090a1e02183f0f0a08 66
    0x91140d0118050390100610444014050040040d29090351030600f01c41001105803c042401503001139860b2a04900e0000d1050f081d05d008120400c00b5000d0003916040140400f052040240c03010072040d00b8014000d02c11480380d8028406507050150003802e0540e101c1d40c0f280564106501482180d4021400560002803820340104074928900300f0200125941d0000e4041640003901d4104298456060001d0360301422940c908101400031000760362041018500e000344081c13003c1030300850700b40c011075040000c120840381800c0c20340c006103003110056441880c45600000c46100160347c00940c0e2002000d80c01002850344110055000721480300601d4481010390004032110f810b00c40ba4865005000050980c0b8003524000c00b40400a00e8440320791001d1031712000080030380c4065070080f509241b1955820940d81180c3c2c0d0306101485004100324424049102e03000c0002801d49800d58042c3c0740d140300d110580c908030a90b69424441100801e80c4d16400001c0d8801c04101e9030000c0703400321035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741804118 1250 741802868 741802903
    0x50f040e06040f05150904080f0a0807090501020607120c0e090a020901080c090a030b220c06030509010c0e1201060b0f070c080d0806131b0210060b04080d08060a0f0305030a0818 78
    0x156070f40b40021540c400d03050342800642700495020701a5a00c141203901c1a10702c1d40b5410701103512000103a80d284001c40395100051149a44061248680d41280c00d03805441c2c00c20b02e80340104000050314424049441c1000380ba07010414440540e0b114070303519080b0621f20f01503403400c14a107011400781c107007a0002410345580311000c141c03d08e501904080500059188081c2007010a00c3c1800c1203c00903c224000241004040380c114101031051000003010b940302d0018040044050140c2c803826840d01450956950340f0005100d55040000c1c0300029880b203085030b40740c84515003100344400e940c0156500b039210b161200c07404e941029032150007110844009540480c2000c16001414180d060710004030025890610700d030b500058032841c0b080601c2030a100503911003c1c2c1c19141d00944c4141c1983d41d000e800101600b42c0502001340d08410094901d07409140c07204210242c14289510841e101da00005603082001d80c0294960303001016602c1601030408503220040d80c840c045c9800c3e81c0103c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741805368 1250 741804118 741804121
    0x1409041e2f01113d0f0506010513050f0102030403150c020f03040815040c24030606111e0708070308130b0f2b180209010f03051c050f040e06040f051509 67
    0x14880741841c010707500c03071061101010a200f01350403009411200f440c01d108030b00b000301081c803540c0a401541c0d150390f148040740500900d0041040301920081c0e5005040d40010400440070076561040020041c1355908045507449a20000900d0704e1450605801035070030a110a000b9104045000081030083e03507c6407500307445500381003481403080c3e440102d5940c14456021b40780c40e40b0005400298003203440401c01c0a5560b003041c0caa40041a41d4030b11107801411040f189400c0304c007100b0403072000d294112084640c4a86001d450f14a0581080c2d0304d030240881c25001281c1c0303000342c00d07010b0022000794500340003400319000854002c4002110032000d8000004035040c080d80c0c1c2442403010055010b201d100040000010007403104c0b881640503081480021030490141d40e080c500300e950160080c40d202503409047c0c2d1800c1e0301d40c446081081401c0015440d400036500242015010b41a2145440e0038540200000c8681803034455000909140802c00d003a46440c0540840d00c0c025900195203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741806618 1250 741805368 741805423
    0x12030f010e040213061d090705010e0108090109020a06021e070501050706090f05100b150903030a05130e010b0408010e2b020a02040f0212011409041e2f0111 69
    0xc81500841c4d2a50716450180001141d4603148080c203480981165219040d843d15408a5114a50303802942d0100d5101d05d080c19155214500c410781c44542c2d4000011845400c0d030014980d601c2d25408040180d000d0050160790000b0020f80d9081ea9510350300810401b8039050010300680240c102c082c0100343d803904800d00340002d9100c0d50807850341c814207039071540310748001040051112182242c0a66541a141c1c2c800d20708003c100c40e100f00c8002c000b50700b000301c0d5440c102c88035800007881e4440004254800101004401072181c080c020710511306440d54144030416084440d0030784000c00310b0f40178100c40000e4a0b1070982140f110a0200c1c0c00c0140072a945409910703160701018003e401900d407207125401000e075503000d4078020540c2040c00419036610200a034814609265890b404030030080813070f0024003c41d6901c0c0d2041c111324011500c520454440740c2684000040518241c410241c9000e07100f01c2c2c08410203c55042401d001c65000301082d0802c0d5901045440c50048440e10b001040c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741807868 1250 741806618 741806629
    0x2b0c020d140a1a190b1302030c0c100b0909061005011823240423040c0c020306010f0b0403080d09051207021e030d0f1b110312030f010e0402 62
    0x6550380c1151803140c000c0110028440300d4001103e038041c40311280c1042d1001380300580581121513600070300c0d44e5804d08501901d03800070750003d89a046003c0040010030300a82d003e218442908104070301c006050300301d14081c0103000c24014841c40c035a82211040180040c0c020700c004003901e4003860034030b02d01052283c003200c0300401070b04003805503000e4440c028051b0640e074140d070a0512041d42c0e035021201002411400604131a40c4031103440100744401e102c803c400e10649400c03100301c07803107001c100c01c81400450110b40c6d1480d80600000c264844620030f41c217080064500400b000040400050b1030b08200f40d80340d003d940001030041c840000c0301c5c4050f64150300702000213504103050722000b12503804440c41c03551043c0400c0780181002008120010810400901c0030100179001e03091840b000a000c99075101d09440b100e080c0710042c80700990050303144484100d102c1c071030200d1a41c1c3c0303441002010700e070030040c00d00207080c500308104100c00902010007a40c11500250b4032141162101c0c8000380 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741809118 1250 741807868 741807883
    0x150605060a031509060e0405010f02090307090e030f07140f07080c0d020a080313081006182309010c17130210260106030f0b011b142b0c020d14 63
    0x18496810008007103020008a0071b014002c1e8461402004010041241c80050b4000c5420040d41500504000c10141c0030f140c2050a46601c03a50589180c159031007054821900010002d032400030030901d808509403000c102000200ca20074000b460b00030303d00244181d445c424807249501500701d2425030011902c4643e90000030b0035640c4184e9071110606036848904480d181b240130218030071480000c050031401e05c20790701524400021243c01c8540c901040018009682c030301c20004030344041c00407404501c0d1014901855000e40007050b000b5805c28010302d01ca0446220001c1d10b142c200600c14482ca98140044c09281e05035048000008940c0c030507a148001c202003901c40d0400c071108281e015188003c85416034032261401c002d000c9000301107108a80e42007034104d002c204061000d50a03400c0c01191680042d02c18604c05030f4180d6040d000c00c0c180000c80c0b4a41214807103800f60340e5008181c0d103251088548003480c0616001c40181c00068140024410140081d0328411602003042c00520484 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741810368 1250 741809118 741809129
    0x20a0909020303071502071203060b070b0c0d0603050d230301050d0c030b090d17060310020f04180504060c170a020a0314090c0109080318121501080109150605060a0315 74
    0x20820505c3c03856210020354054030341241d61264044801034198003904c54002a1501d071003e0f40d00301081995655900100a407480c00307084170910102c0300f8100980a140051485080905800c503a030400140801450180c01c1170544810304514440b40c03400c02c00d80341183c07000c075024070a00c14181040394800c101d582000d0040b18180c0304000d050b40002980000e001041d50340c07200c0885038a0002800e0341020b0f119164190001d001c000fa2030910b680281150014020b01a45030a5407a500c10b05c03030740314550a006800b078440d000c02c424020395100e0008000201d00b44142068016000390240b00001462101002d0f4040b441b0102d051080d4414100400f00b41002095810072514066a40e178110410a00040840b50701045c894004000d4542014541680d000781602090400507110411071200c0307094032030f8100711201c0c00041320005009154103000016040500d00b0300b050481c00000ba1070030168240741d410007032a10340c0002c460200210f4680001c000b46c1003c28800c0c402c5555004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741811618 1250 741810368 741810383
    0x708040513060503120304111e0d061d0105040c06320c0105010b0c19050a020a03080301140d030e010302071109340905010f0302070b0703060501021009020a090902030307 75
    0x1c400c520072581d404102620412000c655104068020103001c9100843e00146224110440d041c01402c0440740c030008a104060705090200c0e0520220340c1c814850482900e01a88500443d00025811050300c500300150300c00034415441c0035240e0701e11110700c9120794000c0150503d04d0320724000c1e03161001c0e01104005003000380c1c820004450815141c0020340c07035004035403900f8000200da004000460301c403480840040d2601880b920b01654820600c043c0035900f50080343c1e00b01d0010381c0c0d00c041e0940514454628261294184004421404141030030300707001d03c80102d0b01e900130a80248140504181c01d29000d6904d030300900e0a45842d04014a0b05608070403043c05200b496403440140001d4004140400340d020b200b95074010b20183c0c10040c001e404515035110600455200e160107140d403001070305025190122580d500b991981c2c044600340b001a039030348070501c0690390500c1440304c00c151000c414000f09480c1e0300002c1c80d480c10b901c500c00d801e940c0c0b190ba04046440034401d4070612078100c03c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741812868 1250 741811618 741811639
    0x50a11061003120801061d040f0c02030a140f19020a0f06020d180206040306020309032514060f0c130f08010f1d0604030309020609040510060f051e07080405 69
    0xc9120541e2460004070703048003410700b00b468183c2c840e070146130485000f5a0748000351041507040f4103543c8004284c494100f500c50100503a01285800f546000241a0340150b54903400d0440c028940d00394030200d001c21030f00c00c01c00341010311744502c1510307042405018420200b016624080e0314100719110000c215262005c0f0360300a0092907409007007501c214400c144405500d40000d0030151940441c0290b0100080c4030500c041a200d6010f180d200c186103040300c0c40c09008051240981280307008080311425485170b00c4080100d0700121025207140c2100034400c500b4205840403441030002c203071440589c3c0205001c420b030050523605074004c007146101409900c2d12050368602030007044030782c2c0f0030880c242502000890708034075a01c18004156800703819180c943d035404402030500c50000381da020000f8041c01035035989030702c9814000c4880b2214502040e250840213814000d00240c50402d2150034040c0c100c0381002440c0f0380c031003542000221079072214185406082e50146400103501b104407100b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741814118 1250 741812868 741812881
    0xf0307111309050a0501050f0a0624090b040e060a0b03060d02090c0f0d05060901240c060b1e03010b0306010f03021c1a190207030e120a020618090f0402060307050a1106 74
    0x601090094803030b00d036101849e540e40349965041e520039206015107212503255008400c0e4240d0101e907000015880c0111078107594441070380d1719800c181c1040c400120700000b445104d14040441000401d12040b545080d1700e0031300000b5107005070028020f8008d9141c07000280440b00c500f002c60b400d030f0801c8500d1a0701d4801c101a480300410044034168082c001c400004541030a200c04059541d1811040e2902c0700a207101d411101c048440358200d584a44070980800c0320396501d14204408035041d01c9105162814008060a40c2e029104250080d0442001131240ca85801d1400c0d0603250103541c0c81444101c02c03c001d40c41c1642c0c03802c0181041010b580001c5d05d46660000c507074002c03a10754852040c80550850f01d042284601580240444e1044030002c0b054141b04805007004588513040e9180b100e4103030041502079114103943c54407070440620b443c8203450318904d02e503084003071284551003a14090740802c4841c8405801d030001d005011403801d000c540300790581010840d421b003c0d1001802c191 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741815368 1250 741814118 741814121
    0x7060f0c110606030c0a15141602030d08041e08121005010206012310030b0a06020d030f1104030201030b13060b0712020f06070302091912050f0307111309050a0501 72
    0x700c00d4803481c0104000704100f480d00180c00414894000d12203080c1c4e0b45400c8a02404429140a10040c000c1d074003442d0341e408945201078540341001d00501c80001c1503d104241c1402009000e620622090b241488081101140d808205030359100c9000c0906001e0f0412240b64029624810454a00b0404200580d12540105000c5441c20303000c5031080c4e40c81e041800c1100000c4100c01d8003140782e841c9441641d140c040c4a00303407404054240025000358100101e0040009034100b800541e110005040c00c3d5076040c070540c0c0b5680f210ba07030b0030812085a0000104144540d120203030405032240582507036640d6203c4140340300f034440141082182d40d40c21180c0d140b44c00c00310301640c15005100310a11510300116203c00c10b140154042c10041c0d4940409400075009269107a030090000c090311003528103500030342c002404202c4203628007000c02e85002880d10168074850503460b0001e104103800501c000c03c6c2c94000700c5c8102c0c5d020101402169081e0b00a108030800980b261040810340710600106 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741816618 1250 741815368 741815387
    0xc030f06061d06010f0e0d0b15010903050a060b06190206010311010905010816050c1506042a03090501020f04060c050c030d020d08040c0e161b080d0207060f0c 70
    0x920000c0c440c165540c050b071035108504191030140044034500140242d8468840028400f0745030030301041d00f08611000c281900d8100908640c4c80429000780803036988560b030101100c400904e09a0b003002d003181e803200d4841800e007800900a1b600d48d158200160b4400054440a1100410002e54510b900a000790364103402c2c84161080c00049030000c6641d449100c1c17500a5a0040e103891a0a448400c0310340340300b1042c1d0301c007102005010720603051100e805104541d10580820700718401400c05004100c1140c20760100507050300801095003004a06400110058078440d043c002041805404c1142c00791041c2d54410724000d0303000401240300c94210204541c1603000303000721a03070346800c7c0701071590b51070300603a22902690006a071104410703c582e0601d80d0061007040c2c5a510640c0d1039032010308403401542e01c01c000030012030700c1c1c1001961040c14901110074140d00310040c01c10580750322885108080d100042c50390001505000e01400d03030040700540300310402c20000b810400c0401003103c044c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741817868 1250 741816618 741816623
    0x40b071209050a03020a050105030702101a011814190923100f050f040212040506181908210720010b0310020a1707050a090b072307030c030f 62
    0x141050202e101d0910741800700036030342e001d0100320b080b9040000640341c80c1c000900c0c560461003002901c06c00c41c511806009203802000d816840b01103080c8001405a100201048030428221a020070484035a9021a0032580c82550350305110f50140302101c90b1260340d50405000542070501d4110403c0310700452004081e01442d0151480e21028806201c0200781c0c801d0000c9164134120900103850115101101140c0041c401442e01c1e20080c5a501e407031100b19020b0300d20384c10601c1041002050a03840c2c0645c1040440985203401c43d1076044d480c00480110007800030382d004901320450684100d040c03101d0f1801030300314407410300d01110b0081c6410290142401d4407074650007069001501401030011100340103004d098040101d071900340003900a2100a03081151030400001144545070741e0f140100159900c6503a01d2420f8600580442d09941c40080e813104c08000d02804241d0606001404185018130085441d40200c07046181c14116080900802c01030b010010400c8400f4030b82c03250052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741819118 1250 741817868 741817877
    0xa0b010603050c0705060604020a120f0f18120807030204091409121812010b0a0303050c0c0f090708150a0b1c09031706060d0c0503060114040b0d050903040b0712 71
    0x1d03260340d40b0f85014003034a900103099601c01c1300800c1e10341c500394001d800078100d140f900350780132089140c41409581046000c001c860342c0e14003c0007034110706400307100d07052000620518045c0700640d5a0740740c94043c40404504018150021901ca68800c0e0100c400030b110f455010300000e9811502c00d0640441500c810741c4500c240c0c50756180c2448903009a824551500d80901011076500041c0a64100402e108500c1c4c0d56a031402c040e031a644080d12440518029a9034940746c05003546528506516400480d1081910f140214001d6880004050f444000d41c5807210041e00c0d40164860301100e03850200e40c3c0410405800300781040700c00e001d0310030917014010710300ea9602c84c00541e81c201c800445000e030001d1185944c035002c004950078126001780c1c01514141c9491250b4a00d00115015203040c40002440003090140a41e8030960f2280c1003607100c00c02c03500d0a4903141c29607006210b4880c401300d8160301c40300001d984c0c0340c0c1803051740c0c003c0c07a1060125a0301c13203a602d007089890758040503486c00704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 741820368 1250 741819118 741819121
    0x90619090f051b04050c0d0509010e0d08070e040218120a060608031e130b13030503030f0405010507031e0903110a03020102040e09160603090828020d020102190c0c080a0b01060305 79
    0x10300d130a010340c6000b04903245c030301c914008441503c074014240060600303020399295401000030040400105000c1c0f103140e541c0190b1810482c2c0b0003070406008081d01d52159005215100701c0c54140008260781b0441145c403220002d5400c10f00c1400e02d250b2840141000e454060300060850010000708800d6100e0021100f26125104166400e40100030a0903511180000d040c00007400c3c02c401403000c48400d8602c007d6140c0e0b01d64a1524580c02121050080b8074014140400c001c000d000382ca800c0703000c9050a03c00907003111860960306503018440074680742c481c6040b00c20706016000001c07141003564282d0350f0000c0d450a019010303511601c40c00c40c4070304550340003e5101c0c001240d004a000703601c80c40c0c60105850010700300c010340034040059850f00c2c0c00f0000704502d03021010341200d00300e44142c0315843c0c0b000c86c5c40d070203030403d0410f6800b0700a6900400801010318000310032169130070000d00300f481d000e01c4079080c8000b4400a94000d14024419102e061081c00603202716a81215195501031100703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 741821618 1250 741820368 741820423
    0x907021b030a1205070507030b0a0c0f05180120190b07021912050c010e070905060f15030901021608040801061401021b01210e15090619090f05 63
    0x31080b8116010f44400c05a082010505120304024101c950040084a01c49602ea4031110302400c419039100840030b944841e00b854207a008401250030403110305046040402a4642050402402c82018100300302d04088444411941c40d1b0014070891480854080f9104102c8803914640d102c541075a2403074807800001d850b18400101d0034400803034000d00300b031043d46a9440c0b40b11411281e000344140320045c0200c4100d4202440307090f0256200000511616141c410600211140980072502030300d004040c10107035407280031059142c5199102c0c1517607a41e030380308915802130140c8051880c0b100d420020368024020080081c0082c2c0d0b83d0000200700c0726075508410342c15030204010581c0543c00044291142c0100910504c07040340f0306044c5640b5000a403840c081c0220103102040ba5400d61314210342280b2078040055140c1401c11036441c030264101405d9155440b540280f100c8504c04810b00c002403144019080819010303840944926a5032051610030f44480600c0c102c4110040d66403906820b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 741822868 1250 741821618 741821623
    0xb15240904060f0602150a14070215150f0f0f21060603030a0e0409231b060405031504031412010303030e0109080405151e031906320907021b03 63
    0x211801340c0c00a209540c100c070300130120641c1c0145102e950b259140392065003804009402c902c10741035540036040200403506a1411030201a100e401c22007866203d80310140c942c1413001032400b6040700c1003020000e518001902001d6200c6003641c0141000b07130740444000704072005d040b40813204c03019900e01d603607400c050541e20b004200410002803000e00403000d45081c41d900c60f0340142e002d211545900740d21181160044950340740c1032075040c0c0c410f1001c00300d00390741090170442c6180101c03003541c1762030729140000e030b942e448000c80c0701c40c91072414010504150048102c021841d051849050b1a0f0030b0b84240900d07083c41c24442170700804d003440c04640041d181031040307070002984020700504207400e00040c802c81c0c01c0440d46000440b403007041107a65900c54290400c0e482c05402e20159640d1802c0a00b154060714614000c035010390426206004180c01d001003450010309104002c240d58108035604417480341310001c400d82000c030000500041c250f0200780b4203042e65050700c0407a1040d050401703042d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 741824118 1250 741822868 741822899
    0x71a060a09050c0705011407030f060815090f061501030606080415020306150d0606090b0c030f1309020c0f0601050105070206030103260d1401060c0b1524090406 71
    0x980c0002825000d010440305035106940041c14480c9090602245580d06421160100c0700c411040b800300c2e00b0480001e03490b0180c845654441a01441003501d00240d05a59000c403c481142b001c801c4000110781e0321040050004007103501d0304480f240d0030002a641808011214050f00007401c1c000302003001802210014061648000c003c44215000c030804802900301801803580000c90b080588180245030340035001d9180d82e0301d00000c52a150800c00340802c0e5255104c2c100c1d4510920590320610004001d0f11a4002c000e00d14603901d505001480d0007181007074100c4642a8804104941d1208000400100f640a00e0044030b0305a40ca0344e0056503140100d00009600803020401400010300920b0041c40c4000c032011941c5517402c4444000300303950030410102804580c2c40c5240740c242886407510600400740340c189559500750715150902c000c03c0040c580380001201c583c13064203544072804121425450700c40d080001180c00051280380b070380310a5516202d50b0810201081d41102c0310303403c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 741825368 1250 741824118 741824131
    0x50405010b040e1810140a27030e040b0a0e040b0901150303050d090b0906250f0e030a08040609140406060219060615050a03050a060302330a05071a 65
    0x48080e502c018001080200307013860214540540c00100410301400e00429403807030101c90f2182128589000c0e1034080b41d54042001030010b0680460b2507810020001e86502d80d50949003180c2103025400c00720700901001c0c2480350304107110903000071b0802540001c59000e14415214600d1540b1401041401d0350745196103401c0c034025844017040043d0040000380840004041c01044512050301da40c11b0f06801101c1007601504020104a022181c00328090862801c40c0c141c00070000c580240100f04d0403c0000440c14007000c2c201500d6a9502003080b5261664807036500c55445454150040813049280f141506903450741c91801424075290266000755402c5600900035201c00c1000441c03094003003601070350381030354400011413411007503003d15a01456079114181d07201c035103942c0207003200c0c03004201401092400c0d5043c00140d4441400c08400c035031610250000001c001d03003c044180c400418210070040c00100821034a4002c0060407803180115030303140507004200740c01d000320102120310 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 741826618 1250 741825368 741825389
    0x807090b0a030c140705070609080316060509150a06081908031612020703030213120c0506030c0f040e01050907020303160c03051c0902040b030106031e02190b04050405010b04 77
    0x301d0740c82c0c40395024610007465031030905090010a510200d0782c0d80a800141c13429000f403074043c0412900255004010a00d181c011450300804062030b6007059a5440010705503030f11500460b216010030402d10000e440350820700151810a041c81074010b10f842e11849525004103010314800003110006400d10541000c3c03800d00c2c695a10301e00003008005042c01034203010005c0101031291101c1d1010301a401e12a44006030345181c00346140c05210125484600a8284007c403000040c551030300d0700084990507202d040c0c4a0301e501901e490039000d12280404145404100001c6c240c800851603030407142c00741d5000d0a2601c42004c00c81e03ca1004403881d1101659500c244103543e807040c030704447c8060013490402e040905c52008400c901300302d44e204541040d00e070f00c1070304c1c01d501d082d206070101a14100c0082214030300d146c0d500303840c5051032031610450317941da0940c0b6020b40d10b480b04015045e0350148a000d103419114004080c81e40c010b4040c45004525180c004120002c544003242d0a58120444 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 741827868 1250 741826618 741826627
    0xc05060a090e07170c090d080a050304031e050d0b1c110f030a021c0804050d0803090606010e010e0f0607050a150507020c0114160516060212070b19020702030a080a0807090b 76
    0x401782c00c10b07401301c50000d812401c3d20400ca070102e0303040c0c0c001d07211551003650f800f40c1e0b908090800a100c210039900e00710021081c10040303025203811408644020640c140302085e41c6c84c1c5440007814a000c202d0000300c184a00d020720004000c41003014200c901e1044616450b000442001c8c13540d2045a84c4009400c040480c024040c01382c1c00b0500e02c0748162003510040c1ca082d40b24404906984a011000c40f585c00e1f0100c1072004001041c0025580801c0030304c0c0c054200f020030300c00244105401d101c29401401e0092080d006070315003078200d03580660003808840d0808490b10340030485d021203050195044d40b40c40085103407180302040300c0410702030503034604001c0c0c0d03038034104005198444c8418225031000c0342d03144400680300388541311100000c10b81c448055481c00c5e6020341406580c60301e05440384c50800400f00064010b50103079801c12a0f20102803000c0009100d480002d11800c0e0010b5818483c91140700100a02c6200406000d4515900c12a541e181c5c000180c0b0503100c50300407a442d01c0410302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 741829118 1250 741827868 741827881
    0xb03070c0b10030204180203240c0a0e190602060714040b030613050f0106230d0b0d05010212060a0e0702060f07030612050a020928090c05060a090e0717 67
    0x90742150880803070644100d03965070341c2d40043c0484260120f102003c04203a029042586418000c0c41541c00c91203101c0d50030028141105c01c00504001c03c10311198002044105080348a10351644400c680908080c051f5000103030007502c40a0a88140b500520a05001074007d5110340007810080106000c40f40c1024140051003046800003005260401860580c0000c1e401990240301e01400e501460380201d5414043e0040200f41240c031048500c0326000411800d200c0180d0440d2484174000c0e500007003040c03840740020b812520030b0001404c1036002255041c405820510304038059401140d4a03a099aa0750582e0786c080d0f10100c910b0700c0583c001e100001c1d890034205240fa540003115180000344c154450907d083c01c681900c03416969a4009001a002c50800800541e00085503100000783d1114451580c030038440d640d01903a0f0790fa074454109108011946109101a0000070107960711200c100c1001040c50110f8401c80741411071a00c04242c0e1103000307041031144a14000400c070026a60403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 741830368 1250 741829118 741829133
    0x30a0903030309021503130314120103060c0e030d021f0c0804061d0d120b06030f071b1208040c06080603032b0204080a050c0117060904062007020306010b03070c 71
    0x445050f0382001c01c4070349420300c89140b680158855228a002031100018500f0009c2071410059504600c0301410054034203450109161b440c1140d5004001140c520425141201d0807000e601a042d05031181024021400360082111070120748909141108420105294811354200e82c1150020070240008070b0045000d54101c01c242e03d0240d100354040d402c181404910300030300c408240c400113020202c0482c0440c0f00d80144001c545049804074110300b032080e1006a89200501854140300700d282550500007070403a0169815a0440301120000e8074540c0003400b00d0008640c00c0700d04500342940030611500902200e801803002030021030410180722490f05060104991860016246075100888001580000d2001d451058050411a0000d10704181303440d48601c0d186042c054107074021000c04801d40b00302a030210044550700d0f10b54803903090904c000c0c6004403c4d500514140c008090a4511010081c03800c14800e80413100c1d140c0e80d542d0500018001503030b50b0310020f240700741d0003008903060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 741831618 1250 741830368 741830381
    0x5030a1802100509031902210c0315040201111204150903060504030207031707031209080702091006140408100e10050114150319020a0c0b0108030c070503030a09030303 74
    0x24603100300101a91500000c0b90001c00341c6240c40040c8000500081d203050910001c803902c011904194206403582c2c0c00503022031400741541207800741c003906040e1702080c00c05c00080401009010350326140b0341e580001035600412917007079000c2600e000314408540d8000504040d800d0f0352030050740c281410000c040344503078041081c010400c40640303408030102c0c0c1d5a1243d280100e20a8000b003404502e903250245172044844d404d0101080103016543c04250400c500b502031440030100001d411281c2e242189282c00307083c40207508001c00c001000124109010b01100b511b000c2d4850b12200c100440040c070b0341c0d10840c000d10302903410880c40740c0038901854014100f5030001109483d0140002c09088003241c10903400003080580c22044a506401c1540310308e24520307200c6449600d03500e840c4158504079440710310141d529a90010341400b1452158074104074840e801084040309503500c000550307a0380c0103010410a940070300c03040000d8902d4000f00321005400c4a88902c0030007071551711705030002c081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 741832868 1250 741831618 741831641
    0x80c0f2e1202040e0f090d0504090c03020c03070b0103061d0c190e15011202040e04020904080f0a020f16030309030b0a2c06010906141203040509042a03020105030a 72
    0x1581912001c1006060000d00080c0010071003102481c0342003602c0319010350b00503201407059000b0110007142d0740c0d03111046030281d40c20200040340c40c005004040b1300034130034051a5a100c0c04007103805000c000407444d43c2c0b0704a80c000c01c414010748000e0354040010f401150780d101700a0f070003400e6074684c60030442050003412180c210390145060703a03828850256502128000000140848120442c0d0f0704810400880d90b2100d004505060030705200480c0c0c07100150000c1d205102580c0041c3c1080b207458121040c100000c0c00381394544a41e840c010355990401d03482e01285018844806980c1c8407480c0c803007412250180c0d00c00c4030f114a107458440c414440601608031440c2c850a20010038030035a0300303886d0f01070406550a0340a503000741c41c45042c0001030f0032601000c0c1c2840010000c03252030140c00c0032080380c00c4a444040380d01611401e86544907580c0081d0300402d0710707000c0205111250b1001200c03003030140d0030080300b4510520907440c4511580002400f2030070602c04a07013a51916032140c010982d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 741834118 1250 741832868 741832877
    0x10c02040902120d0906080f0f0a09140c0a0509040b040308040606030b0106050405130c080a0c05071a01052716020c0901030605090708210f1201080c0f2e 68
    0x941a0040799100e504a880580e0f039600c10705000448a0348080010010300c503d2808183c0c504194008c0b140e121030203800c010b80d07842c0f5440815004e1421f07a004002d0642d215040200b040c00403503c4945404101e601103104d1317050800000341c5801c1c042c00c2140f140d81d1040c4218500e940743c3e03500740d441407009002501c00750303038402c40800050203c11380c0502030580d988801d40c903a481d00040001d40381a08040700c0b085418003200c8420290080c0c012030f00f0845945c408220500c0b4400110b5060003a40405401c4506044070202d030f01d0740c00040340e070584000b40d64040311228845101c4010000700c1c90340083c90200f42e00062480068031070465150309051050311820103005000501402c402e03041500d83c1070b80d80301802000700c1c04020340300052000c0c101400160107031040300c03250803031005070021046500240303016000e44844119a1403481c003c015040030750316901007560715031010307004a000b9086401824000e02c0c3c1038051240c05000c51039410f851440090700d008a40c80410040c0040c070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 741835368 1250 741834118 741834131
    0x25140d0c050d1a010b18061206101101050a05091e0a02060d181a15092710090302070501090e1f0803071109060105040602030703050c030d2f030c0405010c0204 70
    0x164126143c0a00030a5000517103a1261040742101840c075038090482c0784200e800308003102140c0c1007814110792080f42207e140b011003020400589214251141210841d460b00d400c02c40c14004d154402d60049030048100c42130311601d04101d005202c0c10040b94845640000500001841e0960007440d07110104800818280210380500d80413409090044a44501d05c0a00041c450342104071103600603100d504052407403e4140111343c4020014041110301210f0030f035081104003895a030f00b21030300c50110407203c100f0141607201008000c208000ca0050180e48400a03884d0b1003508160b083e5401880c000c070150b01c0700001c10510100481c05d0f0186e42d0603c020028103136030188041c10b886406407280c0303c0c10444205c10042d00384401440075050210500082c07040740e6002055801150f0b040c1091a5112100582e039441c501a00140342d6a060401180304201d08d20445103030202c01c080c100c2d05074018038240c03c031281c0780030480301a0700258040c4020040341d803064120100544c000b41001035003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 741836618 1250 741835368 741835403
    0x509060a1d0d0c140406090c020307110901062a02120601060206010b13060e0a0b0f0c0f19020d050a0210030614040b031b040207020d0606080f011503110325140d0c050d 74
    0x92301c08245180000d80c0001c41c07000184410b00e60800890107017140d00f04900e40c101103010340003914400741100d2110016810005040342401e09060741074004140071003500c902c20000d43e40c1da400340607200041c040d520000074260806410740e80a942c0e194140c1001c0350805a086034130b00303419107590340e015441a01c0003d003002e03080014481c81c0d00e00c0c003d00c0c1da9400040719040c41c20400c44036140c000d0b80030710012031002082e100c0d401b41c1540c1c101e40401c1c610f007660038007600d402c00031000a580310b020b814641c0802ca030140d1204d02100c007610600c241803c0c04200300811580c0340d9005075059005000c0c007825001802400e004c02c0c80d002040103003800030035004218040c0c0c2119085505035900c40c030078030510382d08100e8072000e65103840003481841d081960400d04030040348401070110f95203c0721226503541c01c0c4840b06a484260600c21441055010400a9415540704644242101c0b00c0e020341c80b401d01107605641240c0001034092400e1902e82072020121020406465001140082402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 741837868 1250 741836618 741836621
    0xb06010c03031d1c020309060f0c1006080a0c152001061208120603030f181c031e1b1104060f09050f07110606100509060a1d0d0c14040609 61
    0x420030900008180d104503105100302e1340e6030801d040030b003958001c3c00b5010b250303515042111922860703081c600d900e500620400601d02880004c0d0042990b040030703004201722000080c03104500303024130010402150780b400c20341030905000103404005050031420344142c00c0c9184c0c1d0301040c0b0400c81d000080709640d45034003400034a4a04401c551500002800c0b441d02c0d00c0b5040b01c075030810403c130003640c030307214007520b00303503050f101d03003120015106071740c0041459a5942d007502400c40e405500d82483d94907001d01c0c2c020840c449100c4200d0100c111307415a00d000c940f10700040124452041d00501e020000703610780b5200415914035956100f81c40d0b07207010401d2a9128440e0700249510200032545080040c406411128020036140800c2500e050b48404030342d001030f5081d04000203846084803924003136001c550700c4c4903444c031240d04248005080403685520201d10003007501044060310041c0e071403104112280c80010805021030b40d1104040c0400d60f010000e5002c124001000051982d030386802900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 741839118 1250 741837868 741837911
    0x2210424021228060308030103020901060e062706071a07030b03121312140f06040f020907030f110a17060102150c090406230f1f0c0209040809010f030203040b06010c0303 75
    0x4898006c0840100114140814218050001800c0c0342841c0c18060000c16100e002c0d40c400c00f04220f450045807010000d8804e03e9440b018030143c826941c8240314103010103000c2c0b8800c041c058241c0408001001ca6129119001803c5402400f5090554041403001c560340c0042030b066500200f100c000142d050b00d911841c500c1c0d10710980c4072141c141000200c203403c0400d03900300d050082c1c0101c003c00c000a02e5a9040c1081540d0440700001c02d5203a9001c210014605007207400161032400100b581b200a103140613001c480700540d506e00d050246540904a1804240d5409015030b00c41200c00880701400d41009900070802c02d021801c102c18040020300b503e00b182c0c050300310744030880d14640c003040307900703010246020040d100d1a1040d0781c01004a02c105c40100341440c070401074007202c202c40764400d03070040c0c3d10b039a00140954001e040c03a040c05130709036201011071800301c0c0b40b030f545200c0041d00a000f520311940d002101c580e075996480005640c07450100d90708604040d83d44003100c000101e00d04881 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 741840368 1250 741839118 741839123
    0xc0d0b0915180702030702060c0f0105100807051801090903110d050a0327110f04090b01060207060c2d120201051503010e030409022104240212280603 66
    0xc140300511402401441e402e0b0003060382100d0241820030a88540010403505920750554185a0300c3da8001e04003420021100105480d55081a06200b0300d1303004122142d05850b14841911545a903400030084a40e9090300c1154a00c0b08000040252260300d0f40550110f07802801c0404d0300ca425243c40908141904295001040d00429100042541449103491005607601502c400003c1c4204402035043c0c843c070001c20756880225484080c0d1250303100300c400f054000c0c00503c0b0b02211494001440a000d006070780062040710310008402d0b04c5140419003064014a12902c60114208002c1ca01c1d8030704c9444010104441403030034009101c1a902c080c4032581e6a00009850070701500500c0621584c0c4034007071080e03042c0341070710040c40d0340030089504441c85000c0047c1e640782d05004c116000401d0260b0030101412580400040c0042c85141c00911400454004d0300c101c41480620101e0017984011240ea04403000061113400820902d500d02132a0b40803403014444450600106452041c0c008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 741841618 1250 741840368 741840391
    0x90a150e06131806080303041407051801090c0309080f0a0203040f090e101b18050306042a0b070803040f05011e15061704060905070609030221060c0d0b09 68
    0x8000050700a00c15003058004100f0a000072032400c0e503001d981e4080900054000300030010604a00b80d02006100002e00002d82400c0748540c40300c0d4042c1808100340f25030b17210a420f12042e0041d5034407a04c9040d40c4654030008143c01d0030ba000798650b074240c000b20102020344c801040b002c6004107054160704000c3c251940040b4045160008141c10051010751080025003048a00c40603041c00c40035140c0410003520700500c52035400100e04156141340e52245805000f10020b201c00d01820070f0000e5600b200c5101100c503110440e001d219014115442000d14840c002d222420000b00c10303030000d6030881e029100c141805100c0c0d445079421500740302821034804a860300f014215111502075000f07030100000c055080c00d46030400c0035102c0f103007a00d041c4604428120004007004080da10144e0020303045800c45840c50384420010f060503500340410382c850721144d0300d952984a13440d00c04044102e0500701826080d240c0e00344a2030907802c00112103e44607143d9400c0c0c00c4584644079101e106407a0013a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 741842868 1250 741841618 741841657
    0x1a090a0308091e06030121140c0111060606031504090210020105090712150b0622060809030c1f0e030f1803060114060304030c02210f0102090a150e06 66
    0xc011414060004000031500d0f03507201c0340c07425034865058034111002007030007500e0300c0f40980c403080042040c400c0007800d4080d034209071202e918000449050441c0c080c0c03103103440c280390f1480d401c2e915503041301c81c541c0c801000c2000074a00d000ca222684429a001b6001049000c420f50000710040404200030005039500c501b005150101001020010b04164203008255035654803840b02e04003a4040700c40c80b0545807c00150207841c0c001c2201e41c0c0c41c485001c01002c04c07140050042d0308190074841c00c1c000816010214002718004000c940740d1046540c0203051504080c60f00d1a1109402c15500040300d5443c1041c01d00303944140000c000c00510b48503503d5032910030443c5854051110316205010ba0310100061141c514103034000100ca040c2104c402d5107903603551408403910080c1401c0250404100c20116000304a000c6c0300341e098003040c3c0296a0007083c8140e040c0d08074000c484240e9402010340504010403403080031704104018240c6030010000044001040b8198000c410042e000d0b00500c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 741844118 1250 741842868 741842887
    0x3040809180f16050f0f1305190608070e030a030e0105090301091506060509030a0b06130c080402030c1903020d0204020c0f031306080403080703021b071503180203071a090a0308 78
    0xd40c903280301203c1d007001410600a980b08121a0007000c4400345810b600242c0700070303005004c2c0c0d191030060000421160204901c00d14004a441c424480c4c003000c81c00400105414034014204409034442c042e00403c0003482d0b40d10100c402e03924188142e414040100851000d1762030a0107802e101c98000c80c5003a2412001034411743c2201d00e1a40480100310b414015100d482d54040380180415400c645210410b4617404d0014403881e10b0b20900807442843c1c150140d01140d001141c0034402c0307000f1001c3c0c0b41d80034138034030610903920003a03800f50b44c2e010711729a4140014035228099280c4c2c1c80c0003800060503c1c8038210b150f440c00c89002241903451b840400c05aa220440600322006040545054200d80c206a54060849400504200300341900420b045140000b042030207041207110340100e9088540e00c042d11a54210000f031020300007800c04401c060b00c80040541020034a13806001440d42526001045402110b040310801d0500802c03c0801456600e100d141c9016601030381c03103076a42d0405ca5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 741845368 1250 741844118 741844141
    0x9020a03060e0f0f060f0705030901020415080103020907030911060d022229030601030f0f0f0f291207150e041d280503071b06050f03040809180f 64
    0x11a4044d550350020f42041910441c00020603013109081c04e00b161a600c0b03004482d406409150000714141107032404e200c820380d903c00802c1e0304807402a1061925500e0b251012400d6071078803803010342860780d181c540140070b0138007400810808010b800300605044810304c12000c410200800d441c10301814241c140510300b01504d0104900851444c1d910301d1401c2e01d034000c803150100800d880d06059464040301c0c107250003904141c0103a1461384c8100080c00d050b00c4140020008403489070300c44c82c6444241c0d28401d0518081030307125154541c20000b11400042000020310b08607400e0b05990041980000c2c913006400010218039009841e45012030324040c0501c81295074400349440104488501e1002d013032008a4003410100f42085103141c002d40303150503071034040d466820041851000003421014003c0c1c000e00c140b0140e124071809229244d5a41084951380607644a0b016003000c06c001080c00202c1e0039000b0103402c032014158060f40c00103440012a0411b0844100d0542c0400004010f000400d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 741846618 1250 741845368 741845383
    0x9010216030807121b030309021503180c0d020307050418120f020c09130f03180b07120c05030a080a0617010b03010c030e031605010e010e100b040504031209020a03060e0f 75
    0xc43c5001741d42c1c00101c48250800c50217002d005418141d459203100159121098121003800713042d0785403540c90500640e00d004070450300682c4295801464100e40c40c501e090310900350030701d400600410b40141818100300091403143c0d40c081c41c102d03c0c28001c00000c0d903a078007408040d440c1d03034460314241400c104020307040644201d001c9118203600020850b09034480d1204005240e042544078070841c0b0945415207500154040030390441d18960310024039018100c00030081240b2400d40f5299100111100b56a42d64001c08020310a80040c0700c403689161081418603805191224080b40e2203680b0150301c00035043c2c07503030103181c141d4460746003402da802c09000c2c0041d0090f051a0801c6206403524501d922405003040c18900384d040e200614044c0842504105100400b20000300005900b4000702c996801c590b42c0c070340b007030a42401c5224a240c54503100f114422505134444000303081c5407525240c01002404400c03030f44041521404008100c0600c03e0042003480300e401030a410310448589807a0010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 741847868 1250 741846618 741846653
    0x50412171b0f0c0103051b070203150a060303091a030f1302060d0902180103021011010b09011217090102100902280f0803030c0a05070321090c092009010216030807 72
    0x401080c0900e801041511a00e5042803900381fa80768a0030748006820f021413100001005c0500b08184280210150710070302c200c901c43d0325070300c0a043ea03d24121070481c44a018003409010203000080d040308014480c503601c40185c0340540094100f6078006201031f0850101001e2140d030310501e00085040081190704080c8615003501c440758559400119400c0c0b071082107508012905c051003e03000c2d070940004c5408040180a84030940e1240b00b07464446041901c10760301e00c408010030005c00c02484084800b40e0106a02a1585c1180a01100060558244100d0b041660044c080148580720359103001410340c000e040080c02440c1504802103040944c100c0d054503003042080c00500f5022a0131590302101c00c1c1401e50700c8030010300b0240d0780011040240c07444000080d0720800d6211855018150b4544100401403520740c81e5541c150494244558405040000c203090b569903402410140c048030340c0510443d40c507013850081d8001601c0e4070354802c0311484000304845d800c0201d030000180200c0c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 741849118 1250 741847868 741847871
    0xd0509011505040b040e0109050a02180f071815080103051b010c06180b0f040c14090711120d02190305060a09090303112701050412171b0f0c0103 64
    0x201c40c05984141c56040d1080c2c03403003070f0741d9039040c085030392115000440d0380c8403840020441c0075001d051903070b00c454180703604a04c116010407204800c0b0000d516210300401030181e03480410366039240280c900f1780d60f0350481c0e0f40462101000084c805507020104605515507503072105103501d140b601900e0b02c1d03108144030342030303ca4a0741c460303e080e64130a51082d8070903044240850f0b120040e88a03012250103215014280084185c10054a040c1030001c03240114400c44116121903a10880f0f252a1251298880d620021540109003200d02c6154010240c441e110142c8070610000b56205580e42c2c42642c3c007c1000d60042146203659003011000400780d0240c0c1010720880c03610000042198800c0e0140d44071341542e4a0106081c544240c1c040c0450200078070311b00f59640c102e10419140d40ba01d001409413414510072a440300765100742c042c0ea0854003410356100c040c20650fa2442202092a08100d040354414484174050b088920fa05a880c689002c001c0c040c002c040351905400d0a0244400c1c60505 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 741850368 1250 741849118 741849131
    0xf1514010f0b090d1a0c04030311060f0403030e011410050a090c02030a050a0201021c020c10090b0604020904110a031b1b06090303150806060a09140f09070b040602030d050901 77
    0x1e88107041198126082107500000d58400c0d45131102c55517003102103008040c00540104010400020700600036240030351244100307420104a0156a91404c4504008032002c080129001034000c0d00001c074043d0f0000c00110b141e040740000030024000031a054145200f40500c10896800e007045040302a16200d0018000102014030203543c074030401041c0c2c0c041003800605012060710030340c10381d10b1002248051300034045d56074201c840070b90400400a03406010340081d103034280540c1d2041c260090351101c18068240d0740d4908003c000c1d00031050441c1c00645489054104603941402410b4006180e01c2c0058210600c6602103086090000c4c0003091010134620311030500b00100c4000c0303d840e405100414030b6401031404901500c040119030240b80b04070f17100840c803504c0c0441c0b558801c43c02035403241006640d4596500c15925241c034203406280d0250040f070440109501401c1d840280782040b554460f503562803181940c1c0c0150700c07000058101007259100e0288074042d440e0000000c8000b404607 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 741851618 1250 741850368 741850379
    0x70203190f06290913030509030304030602040b042d061103040e090d0f0c03210e06070309060522021002031b010504060b0105040305150601030e0d03020306030c27040f1514010f 78
    0xc0c1040300170103014000d001c11806880d0340d0400c21038014560208065440301da8a082200554125000311255a50560f98840c0780740102012034441200303030700701c42445500c1c0c114191001d0f5085180520f60b400704010100f003108004c800789014510f041c0041017180441040188072000d848034501c1081800401c103c04682c0c8000341c03450f42010917168510030007401034503000400301a006900030b406181c0030441100e401d940808070343d43c01044240034907a206412101d00c80483e800c2994403940840a01000d403c00b000d03143d140030310b07034011a8a0103500101e1440000c1d4080420105691100c040104210050140f582020801c0c28414205800c50350f602d6141c45003c0f10301c020703c0000c01d0004450760710941084219032161001c0d80d1120300200c000502a50003101c000d4028841c11040086031f09290b50524621000502c0c00480708000d600025508440548241c9045010f1215103010071035581c1503040e02d50801400060017680c1170517500c40b00d0016030040388905640710f001c200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 741852868 1250 741851618 741851641
    0x609190e0f0f041101020a24060806063a0803090d020303070e0105130519031b03110d03022e1b020601090b0d1514010803070203190f062909 62
    0x8010742c1c13203a600392110401800407450200c84000103441c55a00305549801c043d202c03030041c1d0301c501c1070460900006440d44103076550f841040c1d6a050300076480031101012404007955807207100349035442a034011b11241019040100440c2c10039a42c54200006001c1c080b80304111703090022423540095411071030f0095000c0d01d0800b80782c42990601c02c0000d094a400e2513840310390005848028102a170380039003280481e01c1011640002c4501c510202c0e41c40400010a2083c074044a600040d10740d040d02c40c800c144152151800c0003103003584107584285605c004500c042480e244c18440c007440718034001a1040044c0c1d0301168003040c1e4507008914240c5201d42c00708003141550900c85001c0780501c103580115074260441c500140005580507295680301c007164006442101e40c98050041e26601c3d015926103911905800a50591180b6102c0030044111032030b10702c07000e0141c2890f02e5181c1c100d4a542064604000c0d81310301c4008103601d100f40c000d9444d512000310a4068410020343d00c0c18091181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 741854118 1250 741852868 741852871
    0xc0102101a041d01060e07030c0305150d0813120b1e0105041a090c1b24060103020d0c211401211a010302090a0515010305060609190e0f0f 61
    0x2d010315100c06401ca8001410800d007401d641c14240204996a5160480d078a10f90b000c6c0c801314000780c100015984540e100303014181c080d10003100f804403403414a404000212440d00c100310f5851350144800b901089031080140020000110f10f4041c6144d11314040700f00c0c40c1300501c40e10003400b000c4400c890220502001030305581040e0390000e041e22104080c05a8115900e0200f540104e9802c00c201d031087c243c40c050502180d8005620350403c002c0710103203807540d802c80400818640e81c0310f21510039004940c10a50010018100140744c0b4039080d20320b00585d44440c0da144046105c180000380780b142c44005136100c0252200e82080354008032003c2e5880c0754818803d12a40c0d03032842c035040d0002c0070400d88810300954008461039050030601c4c602941c400d0309210a434440c19903080014403181c4c490003040d10035100b01c21901600c101580044d0000c110141c42a81c0015091200700c0e466110344400c620748061034149070000c1443c0404941d204031000b84881c1800a00c0c40038000c00050060b4200e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 741855368 1250 741854118 741854171
    0x1809060a0f05070503370b03010e060903071e0b010b1c0509070e061804120e01031103060409030c12030e0c0406030c0b0d020d020732300a020c010210 66
    0x1500c10580300480d80c0d0511520304204660094046d44600309010b0315403205217400410b80092203210346007600c079503d1328000c544000503504204408000140c500340309c480c590f00c0c40116809121095104d040401500340c00c240c40c2e4690014040001121501c1c104035070040a10040c4014a40324a215807501c59512480c1d50074001c00c8082480d035924000040c2104600da1001451032605042802c280d211034075550021800e000c2011180d541701e130086442007802c013000145035482e05000c0c00006c040c800415020000c0201c2800006200001e007044a01c4e010b40e800300b18031191000c40f50904040c030403205d2040d4500501040081c400000510455000403a070903120318140315080044e100f01404250610301c005800000c105250302e46d00681051b21404100d4100ca14440800802001e00000c40c660700c842c0d0b0303403401d0640c94404c0300c02d0207a41c55143c035039690f510181030071a500300e42d0320360015810401c03260310196070402030031803a82001801030004004210b00c02c00e0341c083d003000c80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 741856618 1250 741855368 741855391
    0x93606060d02031009150e011b03020301050607020906121005070f08010e040b0c19051305190b0307030b060c0d080c040303171e040f020118060516021809060a0f05070503 75
    0x117000f032206440c03443c020b810040c003050110316100c0c2d01c030301c0c000d14000400d01d0249155100e8107290380c2c4030744242c038141c0f00d02401aa1a00c2d846408026140f03c004006a0303020980303050b60800c01074140700c41001a801c011010680307050100025100540140c2414104640360004100300d078102c43c491a08250450141d0b40c00e80c8403046251014415411103012281450b920182c00643c400000e2504519107144901441c6d120020045040012040c108080540750000d0000d00c3c81c074001540c200d0202d017000504080fa03a004503505421101611445400c00f800c085107081d0030800c01c0d80d110002c1c031111450141941d0300500f01c0c40b035031900f10700050345034400070f0301e80340b04803a401a840f810580303010298a843e152003005101d00c01001ca000540d80e400c046c986510020914060710096114035007031130b8940540c2d00810544c2a030590340f203480c4050602d0f0140888880700c0c00707440681c0240803907241000040058404500261240300d10f003008024129510500ba40e4201411102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 741857868 1250 741856618 741856631
    0x61002010e0715020c04020702060702010f020102041701050414011e0b1801080c210307030503040602070602040605041509030c0b0d0609050901060810060b0702093606060d020310 79
    0x1040340105007032500c554091088842c042046005568140240207642d4220f03444844000d00b44002d178010524000d42006083c40050010340c0106d98411805040e88001814259541e0310b50350146803a41141d1510b95442083c041071241c0e4460844041000c2002030001060448181e22144500501d001361542c6c9c41c282d080b5aaa2001d42001c0b481e903500aa0a046503100c4106689904298006600c507880660a043c01c21101d48441d0b091300d411507000d141840341a0b1020f03a05079100400c00c482c0240c1c01c1080a0000341984042c002800c529621076071264100010703100340c0d040e210f5604c8240486280100b000031041e103a4401642c40c034038019515814074050340c1c0090019034020003003c50030401004000c078415800102201c40140407108030001c244a0001261341c00d00840c0e1040601300f03c040c0150901141e81030b000a1016100100310940449110300b6460003100114a6418114800035500c070401c00740d82c00000450b48040005016400030390360346043c800458010ba29800c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 741859118 1250 741857868 741857899
    0x30c090f1e060f090303030a0e0115030c090f0e1506090c120105130207060c02250f060503040c0f09060302010e030c0a03060b062203060c020d0c0f020f04140a11070b06 74
    0x2050b1350380100081c080341d489051a190707400181c107a00840e4545907103024101c002c03030000d010307441d012079812400700780c4854203107003034003006d080094109800315403510b030104405d603010400d003c4540381030103460a0504040301000200c110180080c03007101011721200c00070100c4150503504444045402082e04402e004d0810007a00454101410031840d001c50401c0446c1c0100c2c000c0366010440110000da180820700321458207000740030b610418004440c060160f180120025a0043d004000c51000682d4440007040d0711546900f04441c440d840302000c100b10f581204001b094034401b10064207180074800302142040c10144805084152038080d071801c80c2e240c1c0d000301c0307483c1c9540c0c5407040c0c0d8108d0285429403c0da899417200b03c50343c0345400301d0856000d201181e45a030400b80c41d55101c40000307484d01c910204080a9400f07a900900d40d040303c3c03440d59070b2071103400011b80f01c19105408900d04140b0350011524140815903904000300084000034201500c080d034000303411a1071410110f080c2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 741860368 1250 741859118 741859147
    0x509010c0b0f10090e03030114010507081b010c1d0904020a0510051b01052203030f022701021f09080d0504050313050a030201050a2102030c090f1e06 66
    0x52401070a48400141445442102180314030300c50b882000c1c2001241c1e59440c00001150101c0e00b85005581043c00140414540310004410190051500030305101e881e841c4c1100d690b00c80b02c0c64204800c00303982c25808001d000c1c09014030080301424442440c00f901c1c0d1030410150b0344881c2003032040450000060031540e031080c410015241c0580070f001e8010b038070b02d400381c043c0d4070600600c591610410b10a4007051014010a8815013008490300c0820903c40d041c41c4c0080c110520450074181ca52400421500851010b8007012031103060705400001c80a2104010280a003403080c11034200d00ca89034560403412004903c102d2140d8400585810507040c81991401030800d40070740c4038107090a201c28050000060080c00640c480e1140c2c207a80d50304100107410700e0621000303011400500001e203c03940548490b500c6400b60380c501c080324140041c055012603008403272440703200c080450036903c0f80c01c04241e00c4e05408000d4410f00803a0f81c201c2e070420b15441088241900c9403a00055200504916 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 741861618 1250 741860368 741860387
    0x8042a031115040f0f170a1203020904050a0b1c030504151e020309090c160326040b0108120301210218241c110d050604060516080106020d050901 64
    0x140045078030755440d02907030244c1c0105445075043c001d00d8500046465198100d4094020410000404041d04607540300401d00079000516000d041d400e2045000d01d84a900451740702d9410340030006642c90043c020442990710300d081c91202070322201c8020001907002000c4900740d0f00900300c0d54410708103080085864524800494036055404400b500701607400102038180401c00300d03543e06082d0740701d160051040c054280c250f8040e580300352000c0b0100f4000c0b05010142140000e440c459420700103902c80c04940291000c480b03141ca8840100003141c5d00307029001c0036503230301c40300302c1d00d154500034402c2a40114844405407900c240e83d41c80045548034092890750280c104100289403070b25849910b40203403a52441000781c200c00c101c1f00442e2a001d4100c00c41c00f4680c1403100c0303e203481d0b40c40782c030002c1100041c1181c100c60002c5040340880d60400a10388038910640e004503052401c1d906044561045541c0c0303505103d8401d00500141d6004100405400c20314500300c2d032130f4400c00700100e501882 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 741862868 1250 741861618 741861649
    0x30c150c050606121e0c01090b0708040501030b0109031a0702060705130e0603010207170301051302070f230f0c04060602010507050a030c18060c02010e012609070305030a08042a0311 80
    0x107101c0c010203400d20006c944140301381001d8035142d5611b41d0700d519490640c8104c0c400240054410001408030303600030351041c19410018944aa2401c1d242d5469007034240e100e16040401c801c005081107241c544c100701d2140c1c0944285803a60404c50b4803001c684030450180a0030a540300c0620004096071003d5041c1c0300d0003a0420356074a1800d98811020540381d00a000e414051060654035001d00f03641e40c02203907280c0c0c0d071100001c2a403042c16103d1030f40703a903d0085c40c040b400000c81244084070383c0800c003281c101c110800180c40b8035061542000121013213544005e080d0390400081201080d003190a0302c0303504070302c0e00300070400044030101103a40008966140043d003c20010100d001075021300c52038200c5100780c88040c422100b400041d1040c42210f029400e1000300c0304c02007002031100181342c94004120340d040324900ca4417030b0b07519410340e045103041030700040c000c9041000303100e0900920100420070100700d1a04121181c3c049240c600c460001800070f681980105482d52580c04c1c03402a00038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 741864118 1250 741862868 741862903
    0x40b01061b1e12080405060f07170a0608070603060e130b070c050c030d051b07230a0306061e0f0b070206300106030e1c030c0513030c150c05060612 65
    0x324560006007094009403400e1b200c502c11440050148441210941e000d0b02e5030341c5a00144032a5000303000c2c0404401001e01000c162034010010b8401010003c00019202c540c8001c0350490a080d075034030609100820b1640b5140810710710ba000708075445600e0f60005140d2400c8441c507407440c10700318504004c074441c160b0903100320140d607007440d07610170040c05940b00c00c00d204400441c5602c0c80c02d662082140556a40c5000407105600c04040c40d51003045802800b405d00341100d80e5a4481500325842944a03c4285041e142a41c01014011000501401d05481080b1015040a01c00100c6020760314009019035400030b01c900e02c0002600300200c1d5200c48a10420490411044011480b0028401c000110317040c910700a200000c08540d0420340d4900d6400110b4040c19180110003074801c4c0c90015042c031600700080381a1044240c0035001860040510780ba8903890008480360103039a0110420030444036078000400240081401c1d40c0051084448440c8480c0c3c0241e03a0303080490850341100c600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 741865368 1250 741864118 741864143
    0xa020a050f190f021614010909050109060504060b070c0306180605180c0a0b032e080109110d03200304051002010b0f03070b03013506040b01061b1e 65
    0x71248003100c1c82074119a40c44038805400c0103c203903a601390a02d286190307030500c02030502c0800c22444103809420310514100035110360701c03182201116000e8200c803d00c03544502040c4072a060500641004003000d0b08494545411a00d41c2d01d0700303800a000c0240071507100c40440703181005074040413070303281d4102c44200820300f8030352070402c00d4810002061100d030103403204000c40c070324010f500d000c100c50560380d00750300d15511062030101404881302c0343c904070010420b058503203580d605202806895441c0000408d2403843c203101c01041601074105124501c801300400000361306c03d441c43c0c80d0b440054200e40300c05502d042d9690850050350010758100000c0040032915503415084410741e2a03041d03030300060010004080c152035080a0142c0040110208010401462451030141c0072140800c03241441900b500818424440300524039849a404403060105014600040703600400076801d14070785d0130000410040c0042c0c3c4010340513140d88400c10103c05040307200403c801480e80d2015805150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 741866618 1250 741865368 741865387
    0x31f08030d06050603070e0103020702060408060c1c18080903070b210c070506060d110d08030f090a05071503180501060807060503060d4e02010b090a020a050f 70
    0x894001192641140341005800111400c204c4100c034040d10041d6200141141c201c0015806940100412030700040f04000010313a00c80180102c2d07004410341703d600c41d55400000440e0309610031025129100300e29022490341460b9083c02034054913580027288541b10f02c41e0707400180c1801015405903100600000301d541d844010001c45821307c441d030310140401e640f103111141840340113100d001003040d403007c4082006840e01e01e940c9404035104542c12a41007035000c003c542a031101c208212020f19010040c0305e8240c811200d582d5208045000425210b40c05490321982c0320f15920906281c0040c000016807110311907044107142046072090682c0104d4180382250007044148190b032224042d450300490040c1c410030450303001e020010290300034039505881b001c019040c20b080782c5078007221820320b42546035200c2e802456007444442200d141c007001070201303800d1414941031080840e407405841c040117980704c0e0b60044e0400e1070844010780311700800310180c4143c0704506000c40108004a4800b40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 741867868 1250 741866618 741866623
    0x32c0d0f1b05120c090109020c1c05120a0e0d031112090307020f0a0303050301140f030f0c0108010b07050304260f010b040c0914090402010e0d0b01080f07060212031f08 74
    0x403035a0a880182e42e180c800899241c0b0b91104000169000c202d05d0b00400c415103c41e000f41500b000a1001d43c0d0b203001c8441d45200480303001240410100d5808150002c41100c030a9aa40d80656403180501411344151401c2e603e54038984040e50a0540e600c012010b0704006c00c0c01d849050903086101c003080e0900c038204541d04d4110810803842145988281100ea0528084010440b58140c40c1c4504690030035a00004240c0700c072030b00310340040c03e15450030590740d02000001d4911101c540038045011110000501c040016000800c11350800c00c0300d500052400400c0720201c0310381503815410200640d0030080300010007003075600944509003c42200e00010360103901641c8088804120b404803004081d0340c8428148226201030b4002d0714501078504100f519258024070500d007491080e070014002500440c00e80e24140e410601880c018801180c00b00008000a24130200401c80c1c6460b004c2c0082da282e00030150003204600102c0400c0c410b4000c111a403008030000751080c60482d4503400040e5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 741869118 1250 741867868 741867923
    0x803190e100c0c08010b0312090f042c011b1808030f0301080c09010317090d02041b0909050c190207081c020c100906050a11150103032c0d0f 62
    0x140d03c00450000020320030014481c0842480700940a80b4001a000d114507645130442c40040341c100011603003c2d0b0ba507aa03584901d44015819030401d071240a503045c40d040c4104185490040306a2504500808030550300c0c0d5842244405490300d56554000451101540032041d4041d004900c404102036454a001801440c184d46550f0110341895250008101c1c03885003e12002c0c0402a1342412094200e41c200d004081c651005040302030032001c1980841c0482c2c40318036074501e0445992403846040b65000c0305482c000c00c00040c09100c1e60034540800b0185200301810b801601c0440c010a0f881c40c1e0003402558014a1a6000e581c0580c0c1020b10814031440c1d100b01c1480140a120035285c080c1c0b514000360b44d5491a41d40d222655070303052010540d02a80816081170a015260380318a0404d24200905c41030400034031241e4885515502d0302824100a802c414200c100103019104d203d2018920750700038511045a15080340012418006140411224050f006250042641e010041b01c200241c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 741870368 1250 741869118 741869123
    0x150703030222050a090e010209030d20032107170c18060309120c160b04080105010b070b0a05040212010e1b0a0803160305040e090a030e0a0803190e100c 67
    0x2c000345511250b950109210501500760b001d00400d400b80324001c0d25900450b855000e40c2c00061030b2030380890011303203045c1c02e41302d1002c0010700400c0e2403001081e21b501114103010007e001141451045184c502e00700c10000c094140c200e000d80b000072041842400f0800403003806500c4c40d5041d0a100007040303a964040354001036812040c0001d00202d0038101c0c116442501841c020703200c004884a04441c042d40041c07503118691007000031500381448141d01c20402040581c0313103690380794900600e250075120144d00c0a042c00c00706001c0c410129004004160307201e5506880011656213501c0020014071034000704224641c40d0030b080c2108800002201c403003003940d120b054003000190b441000382d0903409000e00c6d84d0580051040f0720603644840003103038030f80f072003414243c1c142900c5000499821004a4007211694042204001030580140c58000aa0070035500e044000d804d20300c43d07540da803044048014082d5404404403c2e114030804024200c0840140714044192181d14020f000d4800c03140c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 741871618 1250 741870368 741870397
    0x91505030a05151804110a120b0105040603081905040f09050402030f0f1b060d09030203120a0b0d030c0c0302030f0d031a010f18240e010c0b01050402091507030302 72
    0x8100f8030926080c0c5214850b00081100751101e0b504000511103a0b400b60044541100150115006030307207100d982ea000e0810901110301000c010700388500041c80690000e40201d18014040c000f06940408403092450140403c0c0900f000050044610384034552191041510400000c2070b207010b035801050044d4001c0f021a25402000c00041c2d403500300c50b10a00b01c89500402001c41b0602594001c0840c6001c0204268140790103c4c91a13001c2d80c605080860050300001215441e100045e00313201c0d00a02d10641c1006a10f404070f001c1812001c2c0d8500190502c510601c00750200104044264061940070782a2006036086403a80c0d0b549044030b16844020a003002c000c504500e140750f81c400745142c4169968000b0041100e800e40d070014481c01035002c00e140e8001d0110304044000783c0c0c000c40c2c403800384400c0c2c290b04030f08500401008040d00d1003070400195135031000106100c0c0b10a141900c070212001039950040354006581035940150355a42420f002c00c854040c150035a010f070401e508600c15 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 741872868 1250 741871618 741871621
    0x3090513060b16140a0501050906090d0c110d170a0e011e0327030c0209161e17090601051c0c0306050a06080109300909020a091505030a05 61
    0x102064038058040d0780450741c03090085803080b681d241d104003071440c0100100034010744007031329441c01e042c88441d054400c2c1c7c0d1901c1c00d200e4407080400003203500002190145c074142c542184024210324203088050000d4540b101c035002c499407600403070040194800f12441220865020050458202144000100c0d12990381e0841c80e5000d5001418080b00c03242c180e054a9444d2a41500200848114107105071600c506c5041300c07a20002c90202d0050090300e8881c00310740907204104041400511441008400d4080c20301d0480e04000d400248a144803030555410002c400c01702c64081d400307610f8200034821142401184040824031078141c0700e00741e91074903800e030540e01d010628000078100281405024001080412125804660000112940402d0380d41c0d44500032800d4410940003520a0b100b080031501e405419100405a440d1401c1d8001e400b0409000020741000d000e4454404069000201c1284462007800440040c001c96140c40a103000c0d01480103001d908100ca103070151624180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 741874118 1250 741872868 741872899
    0x903030c020c030a060c1b200d0b07200d050408010e07030f0f0807060f05070e011b1103030d0608071509030b040f1a0a020c0105060910062604030905 66
    0x2650b11103060002d03004040c2040d01d0380d04c0da001071100080704404c0094a0b11001d915101401244180c203004107602404070710213420351601c1e4441c40359000c1c410348026142c04009402000803960060590800d00c104603420341d01210715040902c0b07038030020302070303840101c280301c6d00030f4080c00540711030b44007c111241c502000241d070b400c89400090010407204000c400040c090034030035404e440c4150100c600b440010740d901070130344241041003000c06071101c0800820a50210307024188400920740040ca00c002c44113050503c086c0e55501070900f680e48848210305031410011039002c1ca00260080002554070004241c43d101c0034040ca14a00111401d802c681c0c03441201010103503a0030003401417a5860b5540c90710700c2c000300004102d80c2540700180c5000c1c001d01070b402c0144141008007001d0380e24100c82c0100c508580700205140e01c81c118180a0110b89641c008003042510b1003030800c000c9941c2200350009032982400b0b201001010700804100405a002412030219201030340e00c03210501101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 741875368 1250 741874118 741874123
    0x60b0304030503011502160b030114010c02090a090215040906170a03021e1e0303150a14120a050111120c1903021e0f03100b030708040209060f130903030c02 69
    0x9a40281c0014400e2005000c81103652200140f0600c8500407a04140c001c00b201842c1001c031035000d0202910b0105c010002e804c201100f64503943c03000d20305030680700d0040e4001415800003514038181103988071204001c54513000307103075200c80f1400090281c40d40da44100643c09841c43c0d001e44040304001c80172411158100103060341800e50f041c0c01902c248a071240041c3c0780c140c004040c120892241442d041c05581c0321000b4820030a13045806107030b0b80e241c0009110014041e045019029461481c0c040000301c6405142c07080464044403e0020480f80b07c04092601c8000d01026003070f94680a500d412043c8038500400807007a48c00403070305543da60355920114502840c105c5002148160030100410f80c82540104801612503145406480c07010312101341c5134002421510501c0000824001c141c00ca20b90060010710540c64020301d540382092000300501e401410003401001c0100c08184035564000a440c00150041c0152412000c1c0101300800f6081203441500070a203080c03540747c60076102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 741876618 1250 741875368 741875371
    0x11010c0212062a04090b0105040312031b0e0306040b040c031b05030105060105090f01111c0e041b09030f170703050d0605030f0703020607150612030e0406030209040f0c051003020706060b03 83
    0x44800f40b03800c01d441d20007400d001d000100c00043c100f150810002c0009205050001c6900021381d80010b100b03c0000701447c0252001c8503040140060000122580d41e000194140e1055020703000400d242c440d03103451130604800d030304010a590a144180050000e11008110813520105c0090000391144001911f692190400726a0030141902c2d450185500404580c0440740f40c81003180e070b40714070000c8609010b03600d014030300d400110300210343c032000c1c40c0030700402419041c0c2d944442c612103071100e8080d08003001c91000600320502440d0410501c40c084141012102c0e03400700c202d0351b40580b440c005066910405001044619024002c511414002054451041090001d18129096401304400e60300f10740030848081d0402c0e0f4840201013072a000c1e5500402c00081c1342a00306c0000d24001e416138a01440c501e01540c0340c010200f000d41e4414403000d40081e00b02c00d0003c802001030500503407060080d04142d410955a201401c0c0541d8154010902107000f003c042000b1620783c02000c01a100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 741877868 1250 741876618 741876691
    0x2b090603051303051e2b020c070e070c020301060b1b060408031305101a090f220f050604150c02010515011b05060703050712020705070311010c021206 66
    0x51210b400001038002c030001d251107030a0f00340b4a15030503000100341e065544002c500100514140314007075101052410000300008600070294204401884c080c0d582c0d140751b110300c0d13003d81e03524808101c89a01501482d0b5085401400078881f09450701d0845855912142540c04a0040d80202c074528010204060380a03541c4004124959110301c04d45040510796000155564047c98803040e20700103062054010800c440507030a008520424104a0302001c02000c0c2414114000100018203c1040d2888009a29038014911040003410311850300190110b0080ca03902c40e40040c001881490340f40040c2c0510141002d003d10900e000c070890a03154140d4200031504c03030404111900d0b60042a038a8030381c02c55860038104044907503d400746410001d0351101c0c04a035407642400442684004070104090780b0540135440c010880d0b039a40ea942082e8400a00190400004807155a10036010140e486030000c0ca0000180381c490301c0c0f56240c0c5800d59180407a03062110705c4046036003010b01d03020389820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 741879118 1250 741877868 741877891
    0xf061e010804060203191b03180506160504030510050a0c05041805220f050c0a0302010c0b0705040807030507051206060607081e0309010f0501050604262b09060305 72
    0x1c580d0703542c01003e17400142c40000d0411503a0340c030b01d102103c90702c900c0303019500c0d001d60182d415030250009000c54041c1d00542140c00a110f801341c02140740050802d030020041803507825404000070301116640125000144103005460a80344401100d1700080e00607900e1300c004002142c41188155036521803480303200c020351a2015016042085603001a40c0441041d40c07000c040400710b8604504280302402c1224102c40c4010386a0501c00c00b003011400d410350034bc80a45030300d820754002902003400030302d0003402942000d00180b09544a9820385000f0069030046419494503443e0240c0c03541c2c1903009050091400044c04a403030500000c000780152400b41c411450000c4984840101d83c0c0706504402e0822034890141c8403410000000714071070820300d400002e8414a245a500640e0301c1a4001c5124007401d0000b48400c0510b60101b041502481c0c068811442000d4403036800e0080301d046003007103100b182802d0113002c1c50705405542c14200070390b5001e802030740320340c41902141d130103407030450100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 741880368 1250 741879118 741879121
    0x13180311030309150406180b0a24030602030901091209030201021507080c181e04180b071209021c14030c07060c1b080102040f0803070f030311120f061e0108 69
    0xa5501084e0365000b0703014903004a40c0c1500404070060400d001e084c11103080c0000010424001c0300c0f40304240a0722107881c8641d45108244101310081703682800701900c0140d000020401210382517203c0c101040d805403007295100004a00a8181d02075440709a0160042c884603241c0e0b411140d5020b84540010707101d100c2076883d540703101445a00706004840841030035130341c0041307950fa412580c01520351034090340e003491421600500066400c90705903e40d1034400034400740000f9440705085640003001d454145500a612407001d0007408500101a4200080c10b04600031031b070b111400c2e5203c00d4058401c0042d20240402000e80d02e01c54204988500d4115590034000103104010105e8018000e00355030b441c4030203130065800003501951000e000350390b00140800200072000c0c400340c005e018841c05181007003444e41b201e040c0400100300003420195105030b01c410f80002282030315008162880d46810030318000400e1015540e060b04c0861242c146070301041250b04461018100460043e951040c10307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 741881618 1250 741880368 741880393
    0x3061801050d170c120316030c1d030106090f0902040b0901080c100905060c070302120c01121812080105090f060d060c020f0f06010e0c0c070b070213180311030309 72
    0x3e900081c0008046003c1c10000c0d031990f20410451425012501185655281420b11300f01e40c2c01094030241d64181410945581d5400ba005400c0110f0000011610040b0340b02c2800080e00420454020030107a5190090030035040354a9404032202d14402e480c10002008920300300960a1807d107e441b03040da0041036510340d10309045001150101143c145450501d40b1980080c22a8000424a0b070140c1d01c82c4100b0019031811080c9143c00e602414003924441a111000910900c5515101941c80d600c1c2d80220031031580402400e035060380c124006010002c01d145008018810070301c01c25110358a00700124081403502100e050250800070320258130100c1d6a03071040d0103005404080e0080d4001c0170b0500080c10310500041c1410080500601707020b6051045541000c80044c010308581da009200640c0c01076400075802040d1401402e05a8980985100203045002c5100740400441c1c180503066280d4107000741000c401c00e10a031a1100391050603400c09542e80411030b2044110760081502086 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 741882868 1250 741881618 741881633
    0xb0c0316030b010210060b090910150c020d052506080c181f0c03110a080909040f061806050a2f070807030503070f020a0f0303020a0513060503061801050d 68
    0x102c030107005462112101128000071641660701c840700329040000c40d6442860440c03165079000b9019001c80300c105043c82810051607004085a60600c13542021000540d5102c1c20382003074056201040794545100603224120805081c0000306a040d41013401044490040050b14801c0c14035080c503500344410310300e03940c02c00e10700f0780d8210303810401600e144210141356031650380c500d285685032245580b0192500400705000c2d01c2108400c2d41098240000003481001291b410103022100607019031214205a00000840c80005246034900f1100c031601c4016082c2450754940110b104018a54402000700151180b2507400c1c946145041d040c45003443c00c0070307251011481000c2946040070119070790081c196006003070503400700b900442006440da902605042034400988050040070f40159600c0190a00300c0c1c10040a00d030b000700b0004d4403035100d030040c1d400c0200d0301040920060307560000608160300554100f0f009032090f0400142c48540c8000040c1225400f8100c4054420107440f00c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 741884118 1250 741882868 741882881
    0x90309060f070606061d03070e0103020909120705010b01090506070c030b1b0f1b030c060a050c0708130e06062814030106030507020d110c010f031509090b0c031603 72
    0x40110107002c0040410050b00c90a4050a01c94403140c0144125510054620300c4001d0300310300c60340c40203006021034160b90b071080c3d04503541622a022941c0b21401c1c15418502011513400c8000b202080240a0000540000d40d03603190a072669014035445100707010b482d119100020740f401d00c60110400009951162250740800c0c940034030442080840c1c0711140d42c0e4414014042da404000c81c50800e6641010300c5d10562180b030070000d600c5e1031703108121142c80303610003040b00c1406a503c00000300c150021800b2203c0481e80207074001d68a01d080c8030118121010780c0035103d4000d01c60f50004880d403c0070b034101c1c0d11a0006a001c00d040642d40744100d50003116646035a01013148105401d40d071207101201440c080c14940d2004203141c502800700a16203007407900210f003001141b4a80f01c1400c034010a0b422a190320030b2800301943d103101c40d42a00031b85106e242c480344a00c1803030400150356050740e2144032400d02c106162500b54072460b031885203501007a10f51180c1441105a48000103000307a0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 741885368 1250 741884118 741884137
    0x12100e13021909200a0219170d050a140105010203250804170d051c050612060a020a09120b070c06150609050f0307061409030109080c0a0210050309030906 68
    0x24269400084800b0708010341e40d000d190718030b0711002580340b54281d076000e03154981d0303840380322034142091220002d64641c809a880c030a040200c8244034240803001032024141c90740311403923035074514050038448000d242c112002030096240202c20240da0b08008800340c1207035016801103041c02e054450a002c0460018850400b464440520900148030a40500007e01c00700c10b400c41d40092003039460b0f007404516500001085400c00580c43d8003c43c2c82990105500c043e640080c241d52144003088141541030018142485036404005c1c00000390713002406400d050760b490b4002c1603070342c2d0411080f000700b40400030290308000c000501040c1c420000720340014050f0102281c03000140f03010f032074940c0c603640201c0f00060344143c081c4018203208450b10107001068008003a02c030720b49400100803400a0600110000f00003400f00103654003508041c00650b004074610780d465442804495030748242a0040f809281c2d02580e110301ea40c01001683e01c01d900c100051481e0103200340400005034030100c41d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 741886618 1250 741885368 741885379
    0x10e0c1509030a030507020a0f0f1205030d0e0303180a0c03030806150c010204031a09060601110a0b011d0609010b0a231c05100b1207031d0312100e1302 67
    0x203075080d035034100603690b00e0310300a840c0c3c81c0d0317610340a00511040d500241c205650548540e00c080198200c50a0310030202c0384450712591036103026140c901c1c150301c64070700903510060500d855140c40c520040001c500507500d5090b01141c603204000c005480740004c18003d080042ca5800400100c3d0050394515400480107141c450181500300030915585c1244c407803550365a6011400703100f00030161805641c1c1603003141600150303190221ba400c0d91746c5001045103041102100000808100801100f01901e41c0000c400c021580c440c01c9502c26485070302d120020001d140004220746081010b23060303068801130781c02240740185003001502c0c08000c1c5800400c00081920190f100d148020700944425a000d500c45c41012030a00c0c3c0d00b00c25900c01400404085000710400c00c0314040d03900848004044d01c00c4440410360b22440c0a40007000c1404200782c4510450061f9542c041c0084018486c01c00f410803603186503114840d01d004210300718010f0003041c848100100d0f00c2c1184407202e041d004c81c1700504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 741887868 1250 741886618 741886627
    0x91e18150302061201090501050a180b030705041d19050706140409020714070b0f0d0f060806010609060f0305060d151b030c1d0108060108090f0a0b0a0e010e0c15 71
    0xf05189510080d0010360b400e542c0c4c0c0062200200340c0c000d1500500c0216140c02c8404d040c01000c602d040103402d07415980c0e580e07849e40a040e54900307000c8070005020040080040750248480b03c502d407101071a030f000ea140500041940300b0340380342c444da0441c96009402083d80c2420017a0644951132042c0d00c60f00381003014400003954841e035000500080d071084010080651561805a103800c00c02d4002150030213060281c1032800700c0c41415030354000c1450402094210001c0401801049036402a0185008800001c910540c004650400300d0310340d59a01d40e48e059217008110110740c8140c03001e95014250b00706540c0130a811400025400c150038800054040310149050748030b0f0320300003a40c0e0100e92956200140c807a002203001516581d0340445201061806d8002803c121009056a0502c0400f00120b09401e104101c6c2a00e901c228a00b1110318100d1070a100000000440e482400035081c28088206d00d541070244900340b0b644800140141400e080400c900c000c1a48800600c00c5414003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 741889118 1250 741887868 741887873
    0x8010e22030512070809030d021305040f23090c060a11060723030405030301060c140307081803030a090504180f120f08090303010501120615091e181503 67
    0x451210001c0c071903201c1c1c5a07600c885904450030010000c20013024022103404106100502000311282c81c500080016503a150340c010b9005d02d100310b6040300b40c00501d072150048030540190b010044c0001d0852001209008641c19003c200c1e9040359040f2058001080d10899820410090448109282000f0740300c8400e52040e1131800404850410005551034459503c074150000402c000303642c04200c0318034510f01622242e98910041c031900c81009002d04021081c0302128120744100020441520703680c5102c2d0400c104d0a800c83c0340480c0000b8250403100c00e052500004a0305001803c0d00c804e4161490078081000070941801e84c60120024031050f40d000500d00546202c286120340b0300d9081c05c45610340c0051901505561003010b0040150501046180000c240d031b0445e00c0901e08164aa028203030f5081c00340c102640b003c1150f50000c00b0018940c6e8114400303c0035107488503003000303c4003031010b456003603407401c0d21070150082e45040460010b4001c0d80c0040d4240700b100800c5030041030f5640d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 741890368 1250 741889118 741889171
    0x1d091207031d13050106080a09020f1e030609010b04051003030206040b15220e150412031d0f33100e07050a110c280e010f05030c1008010e 61
    0x10450012103513914010302c14a504903106540125074800d081100205507404604e4110318003802c00d00c01e14480103002050008414944200080a401d42d80e150401c2240e0038081c0601c1410580708070b08000c00140058402103020301100d4041d03006102a894540301c1100307119028203030b02580e03501800610740300d0300d5032144401490211510a0380c8504600711200813105003500800715900300010400d410a00b2003d00c0c1d41203600220803041d050070100d4242e0040c4089403804d80c85410b80c0004644091002c21288084416582661181150b85c44601c1c40c92520725481c0b078100d908902c3c0c025400545400040c0d0050040302c0504c1641c2e140c203118012240200c03a480000b43c00000c21403990b80e440b09001404d0030584005050540b0214000b03040301008e016090758408141c0c20076601c5642c207940f008000c04c80d1a00c13040341c40d42c48540030b8070740c17440b180900340c000c6c8164900c4c20502d082800004c1c0114a86584d4041640d00b411900b410384200500718000f000ca40c81188528000c1c00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 741891618 1250 741890368 741890389
    0x1e13020402180319050a080a0e040f0c080f0403021002070201030209190f092304110d0c1e0b041205030f13090b01030c080c030901060e011d091207031d 67
    0x2a12100c110b40c151104041c40e10096019038219548405480400a5800030b000081030340d20031000b0351180c030700201c11908078810410b401c1d4444c0c141107031001d800d0100d0340050921469907650310003540c2e0f40c03074600034a0341040e60001d0059111002d80032a00d50a0342c09032001b02c0c8140b4025142c2800400020300c0e002040c0140e8000140498081002244001001c80100900c0c034061100c040180b1a041d00c50b514078004917140c1c6688000202005141190303013440c1c5400070070b14210b0360f1840c180b01c41d00302424050409200d5140e500b8120f0f0321208003c54080324051b0240e0340c0350a00345052040c04420340901140d85200038450310030382c5200c0f2405415203110104243d01d0080c50113580006071144404042d06062400030b025600740d6000380e03120b40c0801402503103943c94803030842c401d00400c4554072955036071070088004075030220b8032030190308c042c0841c0c5d0000019440e01c4400c00d4449501c1d41c02d00000039010004000068080e001c3c041055035280d01100c00c108005011411a840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 741892868 1250 741891618 741891637
    0x1e0f041a24180f0106021e0303011827050d1d060a05070507060203070501060b0408060402010c0c26071401210f020a170c03010f120204060302150a03060501081e13020402 75
    0x143c481c018080503504015200104540d10700e041da58510903c0b1141e101d21060040701c02512060001030048500e98101880c2c585010380091b220340c2e104204441500c400020849850080b40021700e840ca204d44c0ca03030102c40c02c45205c0e201da282218800c00105601801c0030200744030050000c00d01081c004e2180f40000c204c00c2d000b9580c3d0b05114608182159015040340310500008c0c0810702c500000040c140d580b1075420708154006030030f213040809407032180340e11a10040c101c03000b0380388669043c0d81024040c1c404002c00c030f40f106170303d40d41820120010100034900140d8441c005075011a0340305d800d084e00c0260a02c002440808006016007a64001d030a0940800c140120300441d4084141c0d0f41648a440c03070040c0d604550418402400030341040c07080b04008a19080d0500565980340d0050000f15030044c4000412801c408110806400142c00c0e100403170701c0d041c000107255001d072100ea0322841184034120441e45564404043c0c001000c4c0178418800143c03c40c02c00180c071203200520b65406c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 741894118 1250 741892868 741892891
    0xe0304260303070c14061015020c1c02130c0512071b0f03020d090e1504020c01230a1b0503042109080c060f04030b1e0f041a2418 57
    0x14091304011041c5038001c000010540c1c1b01d04108034102443c0345640701950b1319181c0b1100d422011540803441c20705002c030341e5a40950240c80d00010002402d0209454501c20790300c03641c0360706414141204070b4045480c0400032036000c100710000c6800b1500005d5000f020350800e800b000526045919440d20704c400201c6074030001d1444c503410b050b010130618425a80a24150401ea410320b0018110140050016580c1c2045d105550216507582c0d01130b0341d0440b4040c002007010414402c010100130800a41d0013003222001c0d00480c03540c8e031640c00303040e504007250b02c1c1e00c1d405103161301e200315040e51008005a90b0302c1e0411340c0342c00c4803448140c151107002d5038070f9a034951800c0c148061305081159100390b00d4400c907402c005c1c0082c040d51b081e05aa0031280c000440d4a000e0b40c548440c452070604c034601480703201441a04000041d05a42191401280544200d0207103001c292103584a50001760b90b548070301240e1140614071007d0a00d520b4551200240c80200c20440c101a007002c4108191074040040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 741895368 1250 741894118 741894137
    0x507060501060815030303270f030c07151b0f0606090911011107030f120504052701140609190909030e040b090402060d0209150403050a0b0a0e030426030307 69
    0x109a490144c2c0200a000c4001c1c40c50f40c10102e101075010002a641d00380d0b8948000c1c0c1c0e10701c01c410140700750141074100d0020740355643c1c41800c4480d11007603680a400c07050f4100c0e10030b41072368501c940191b07004441d00c01001c1080858640310310342c1003a0004000c440254403000d0200d5644101d0090802d02c074031070360460900c8201c8c00f001500c44030428459203400da004070400c00100d0700da0701004013181e410260050300340e004007104032a144540d412180c0c0007003c0070139044148010030b4014414444020000ca003590f02c0300c3e90401019181425158091020f00600c08a4500945c94250b151512100384051650750b202c6201030381c9085100380c0102e94000c81002c0c0c6070400f4000c40c2c0c1c0c00c80040703400d4082c1d40307441e90000b1010300805000440042e4085926070081c0c0b01d552442040100c504106521540da0b031514a655030881c80e412245920207e0116540c414140100c8160301c0040b006903007001c2c01c0500841c0d40304070780b0240598851100120711142c617414801540183c00710348d9031031540c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 741896618 1250 741895368 741895381
    0x9020307171e1b060f04030c0303090303030c03060510030c11060a0204050f040507080f040512031326091309020d1103151311240a120917090105070605010608 70
    0x8412602c010100300e800c1181030150034000e54040108815040740e2550312140b01822400c8180904d800c0100ba021040001100f8143c0000702e40007124031079601846407009440080b02501c40074424503420a0502c0301000c0e980340a50001181d044240c42c00040302d2240b064214580102518154401540080d052043e81405100c40b50558000e803000d00c51814007103402408545d0003040307810b0301010380020a0800409026940c01c8581c5010758076160b08202840ca804213114000c1251513104950407800000320f82110b0110243e4a459090b050601c150280980b0200e101081803110f580c43c0c080a00690b0303152003081c0b282e80101d01040e804000c84061516000c0c0303003050b00c189400044100f04030942405030403001c56904c280740f031400c41001c8010440001180e995110b1680031888210300300302199000e00440740c03d6603900410244040c428000711220b034400a444c0301008690559034000610042401640602d8910300c1c000003a00d40804072007081c0c001400003a41d00e424000e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 741897868 1250 741896618 741896653
    0xc0d0e121917070803071d010201090b0103060507050408070f0807051c080d110a02010e010513030206220c03050606130515130b03030c0105010312050c030307030902030717 76
    0x1580d14040c0241100292041c0128a080d2003280041c40381c02e074020400340111241c001d5540403940414415141d00744060045d00e1100724244110980c10040c0340c8012641c030501810001d56009050040c2690031030310b8460280200515020501070b017003000184040b01044864000c00c0010301000500f070528140c42d090025985c8424440c95540d0070740c81d0000723820204080169408a0840d640c1c0c808036280b080a016101822402c420020075503581c080c0e0107402c41040b01241c480200001d0341c2e10f80e401c00595641384000380c0140e2291000801002610400300f10983c0141400f0a41d01c1ca0b80e03807644107221030307500101c8440c0c000006200485c204622f1070f40c0c2c2c21070b0280c01841b5a18040300164500001003070003900c94200005030000800142d8460649020042c0c207032990380ea01d01100c82c1c040c10080c44200c0c0c0c240034402800030601d00c948103482d402c1d070103500a94519194041c0440c0a072003403450513030b450702540800040d100c2e55000d107030440409a002420410681e120705d0708 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 741899118 1250 741897868 741897889
    0x71403061b030a0209150d0209180c0d020d18050a06050106030908090d022b02120c0901060f090923060118051509040f09050d03020c0a03080702030c0d0e 68
    0x141000020001041400201c41503a903c1030b0b50340b10050701c0f00d000c2c0d00054079840400c0c4861b00b4030880000c69550baa416038000700130084090f2441c0c0c1c4410702c0c055144480c42011614441c64840c00d1080c120f907c038407500104104009a81c02150b03102c05c034030400200350711400341100c02d076100030356010401000c2c3c0070b0207004003240d00b42040042090303160380006100b1080074903c00d0805008600c1159294500c09400e51060000c181c040086400b2482c01e10765101416481050602c03031135400c0140c0050f240ba50900064104903c607403a04205982c4c06d541d50140c4014420100c0c40441c03461014130400e4604600008106103180400d4801c0c0e03100c1c1d4010709000e04220180001010441d0412121720442c3c07400c7e2450021422010219105d0b400740452460f8014180703400909040340c113822030364803d2300079019141080d0043d2402d9003248200f03001e0034000e0700034442d2140805e002c0c07801b4640c415514010b41c1d00e0401c481440b941004001030040020542201102d07155040408081 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741900368 1250 741899118 741899131
    0x315130c052e020f0d53190b0d0f080301030b0105010c05070b03060114041d0f040507090b061620040e030315010903020604090c080c07020105071103010e07140306 72
    0x5081ca030408560140d1100c0f020040032040c00070080e10358641c035001010000420380d0020707640060f125507040d010070765064208543c111201a8111660102083d1103603401200c600c1c440e490104c0002c201d40e406000d6440c40140e000f500c0c0406503020500c000002200a48a00200b6533a51705610b000ca00500060b0021410050490310040c0050000164081134608008800b83c40782e40d0840100c61030042660f5410000002080028409040303018191402c01005c109100c1540c460f160184012012200600682d1224800704601650790344491440300c800390159180ca90650307843c1d00b0450800508882076100d82c241043c1c10300441c645800e510808031000d0007215009110b41d40c3da404050160580e2003090300001160381e001e42e5039440211741c05480c194450b555518014001c100035181000032032202400183c5800c880c90445000d954140c444070300701481508c60150410f0705607600c94156503600c018400071b820030070985004014508400400ea2644020f141c01c04d440035080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741901618 1250 741900368 741900373
    0x18070e10030528061515020a060c020d140705030f03180f01050c18030c0a0b1b011107030305150303130303030b0604050a06080c07080f180315130c052e02 68
    0x2180c4a41c10380b8410b40810354000b5800704002407201000480c1e0070983c0d0084000c0c1b070003254407000c2c2d10b070041030300c0400034001c0008110405008009a0f02e424008030b0b1700c0c0000d40d402003c500042e80d04800b0b04034403070080c0100c9007004059500412294019100040608a40207149504500812140c850812150000c0c8000c3c1031105102140380a078480842148006e03e5894074681c90030050100a8180248580e454a50301e650154541d403180b04140049940403190742c0c0511414014210340c01421030005d880c5c5111510201d00038100a0010810104007200c459103d070f03801c20140411000c1c10402000ca141307075241c0601111908071210b40074540c10302c020801540ca082032f400844040d03041050455032041e50128640c03080c80402000d003200841c094a52004131000790140c40034a802102e07038190740c041019690300c403d510080a20100b0400946440b03520301a00890314418441066a80c0d15040010300641c0302e441080c031400d205810100062014003c02c40302e90215001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741902868 1250 741901618 741901663
    0x1e05040c0f050906090d0602070615140321070f1b050103050114010c0f08070f0201170906060f040603020a08010f110414010e06070212160f05010818070e100305 71
    0x501602c0d601071211000c1c85003201140e522801d0b101c0040e48141c0c160f01880456032243c56250074002030015030b00c020f8501c00c44000200705010200201541c64070028014100060012804241084500c280801580003072007204006151000c64080752840741c6441d101e6481c120340768004444031640321504150902d80108120010012080b11240c02864114446006402d0000040181e0b0b00000d00d0014000340c00024021501000b09a41d07100f6a9800e01c400c4884428070340c5030505980103802a0425000700e1003070300e0a03030003841c52080064408200f181d507a800203683d844ea1a4811055070351500e040d460001500d10802054803051908203040071b0030983c4d8a02d02c0e008040c03600303051041c11410054203031349003400e82d07031119030080520283c40708810002c1e0729090f9900a958902c1e0080001203000200070150340c0a50308180c2d03507400c0e165150340d06411281015074410080d8003814101049c000314811055104d002d5021840c2c41e02c0b0303d180381c818035058046800c502d0085030100d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741904118 1250 741902868 741902897
    0x70c0f0303140a1e09030903121808070806060d150902011107080c0f0d0302060f13170a0f050a02150c0c0708071805040b070507140609150604050603070501080408041e05040c 77
    0x108070000b2390b5000f0880c04489420319038151292610346d1102e00f040c50300b40900081d16100014264290307004441076840760746a0310305002c4500c0c0411b1004000545d9414070150408090f13015000300c0340149051030400c11140501420315005810598440c1c0110145080b01c2c1440ca6010390781c9107060f56506142e100d2502d00a403144006450002d03640d0314400411006410266081c4016401601e1240710a11a280c6681c4643c070050500b40400d0264900c10240b902441c00d8410f00a40c98001e032200039002d041601942c1c80003400804480340601c17500c0b00100d020444400136000010060461030b080180c0d0300408244602c0d4a03107a80e00b440c00f00000540070000f0280c0080c3e10341403050321041c480ca405035a45040740c941103501d10030041044111900055520055045100d034a00317591202c0052000b50b560484945826920050307041101d075100d656195030040c02080010309040d00d40c402ca9082003800b0510010201c25001d083c400c501d402c0c07040c0f0304c1c80301d60360421081205100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741905368 1250 741904118 741904127
    0x7022e09170a0b070f0306031205030103120314060d1401060f1802030c040e06040e060a0501060e190e09100903050a08090f0a02130b030106030b1806070c0f0303140a1e0903 76
    0x40c42001000105c90481d500c0a000e0340051001e035610a5580070301c40d0340c1c66002440781c4c00901c016a07201070a00300307000001d4040e2249107507100000c50344000c0c0c0d940d080d0921405120f44030b03040712104101400080c0300700c801e1240c1030250015650302c0e0000d515100c44080302c0c200c42c04000000314410010310820380071a42c21a0101c50106c4540398840da075080008000f4510492082000c2c0a00710801c244484c16901c01d905032041602d0321000c14000300c0600c078401028005240c58003004001c03d04c07600754888c0f41142c0c403121850498817410812400076045e04c0949404402140c004502c80000a40200a495204000d00020310714525116061552500005000780c064241030a11607809030301c680002c100c3c100c0c040d00901c00d059591a0000d1128400c03290545440142080100090404506140a0300702c903a00c801a8841a40351040c40900100084003403568800c41400d007203219000640c07007a186170f100051345d080b0140d254000080c400713002040641c505005040041d820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741906474 1106 741905368 741905371
    0x1833170106020a11060d290102120309151f12061a09010e15180403030b040506030d0311090a0b07060b01021207022e09170a0b 56
    0xc6907030480e01e82c41000e5000303055180303200303030081a45130441c050308081e61210740c0065050480341051003644c510664003080f000c84120302c120030f50380501040842441c4c1c0001c186ca185860000c80351600304000f54000010003800c04696050380c2c04181c2460200544d14010b075203611007060301c4594000d100116036450400e80e203010400101ca00310680400042c0141aa42e402d041c0c4039800100024900c040e400d6030980c040b049a40c0d8141a40010720600910012600302424001c060b0790161500c1400303141000180030035074800103007960031089207103030008420000002d454120b01c2503040302d81e4400041100032415401400050141d41d100d14400c00019981d82c005a0700c50603640590004008203018000c05410499031060a0555260121026031003c0884130311090500035024001040c000003807003144080e003100c00c400c0c1c0d002da0050413419050340e140c2540080 = true := by decide +kernel

theorem cover : BRFrame.Cov 741726618 741906474 := by
  have h0 := BRFrame.cov_init 741726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741726618 ≤ n) (h2 : n < 741906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
